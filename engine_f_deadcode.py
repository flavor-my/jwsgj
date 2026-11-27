from __future__ import annotations

import argparse
import ast
import collections
import importlib
import logging
import os
import re
import sys
import time
from collections.abc import Iterator
from functools import lru_cache, partial
from typing import Any, NamedTuple

from jwsgj.build_module_topology import (
    collect_lazy_registered_names,
    zero_consumer_summary,
)
from jwsgj.cleanup_residue import cleanup_plan_path, enqueue_cleanup_plan
from jwsgj.diag_regression_guard import (
    run_equivalence_gate as _run_equivalence_gate_entry,
)
from jwsgj.diag_shared_ast_surface import collect_module_exports_state
from jwsgj.diag_shared_source_core import (
    parse_or_cache,
    read_source_auto,
)
from jwsgj.diag_types_normalize import as_count, safe_text
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC
from jwsgj.html_render_pipeline import emit_step_html
from jwsgj.log_config import Stopwatch, log_swallowed, perf_trace, timed_log
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    SCAN_COLLECT_PRUNE_DIRS,
    is_backup_snapshot_dir,
    is_temp_artifact_dir,
    is_test_file_path,
)
from jwsgj.shared_cache import (
    SharedCache,
    cached_getter,
    ensure_entry_warmed,
    get_warmed_cache,
    require_warmed,
)
from jwsgj.xv_intermediate_store import (
    build_ai_fix_list,
    collect_round_p0_findings,
    collect_scale_baseline,
    load_called_symbols,
)

logger = logging.getLogger("jwsgj.engine_f_deadcode")
__all__ = [
    "build_clean_plan",
    "build_fixed_sources",
    "build_plan_with_evidence",
    "build_scan_context",
    "build_tests_evidence",
    "call_graph_from_ctx",
    "clean_dead_functions",
    "clean_unused_imports",
    "cross_validate_deadcode",
    "ctx_file_path",
    "enqueue_cleanup_review",
    "iter_py_files",
    "module_file_map",
    "module_path",
    "read_or_cache",
    "reexport_map_from_ctx",
    "run_deadcode_cleanup",
    "run_deadcode_gate",
    "run_delivery_gate",
    "run_engine_f",
    "run_refactor_gate",
    "run_safeops_gate",
    "tests_consumes_symbol",
    "verify_clean",
]
logger.info("engine_f_deadcode 已加载: %d 项导出", len(__all__))
IGNORE_DIRS = SCAN_COLLECT_PRUNE_DIRS | {"references"}
_DEADCODE_SEVERITY = "P3"
_IGNORE_DIRS_LOWER = frozenset(name.lower() for name in IGNORE_DIRS)
_DYN_REGISTER_PREFIXES = ("_register",)
_DEFAULT_PKG_CHAIN = ()
_DEFAULT_INCLUDE_TESTS = False
_DEFAULT_SKILL_DIR = ""
def _pruned_dirs(dirs):
    return [d for d in dirs
            if d.lower() not in _IGNORE_DIRS_LOWER
            and not d.startswith(".")
            and not is_backup_snapshot_dir(d)
            and not is_temp_artifact_dir(d)]
def _is_scan_py_file(f):
    return f.lower().endswith(".py") and not f.startswith(".")
def iter_py_files(
    skill_dir: str, include_tests=_DEFAULT_INCLUDE_TESTS,
) -> Iterator[str]:
    for root, dirs, files in os.walk(skill_dir):
        dirs[:] = _pruned_dirs(dirs)
        rel = os.path.relpath(root, skill_dir).replace("\\", "/")
        for f in files:
            if not _is_scan_py_file(f):
                continue
            rel_file = f if rel == "." else f"{rel}/{f}"
            if include_tests or not is_test_file_path(rel_file):
                yield os.path.join(root, f)
def read_or_cache(src_path: str, cache=None) -> Any:
    cached = cached_getter(cache, "get_source", src_path)
    return read_source_auto(src_path) if cached is None else cached
def _read_scan_source(src_path: str, cache=None, stage='') -> Any:
    try:
        return read_or_cache(src_path, cache)
    except OSError as e:
        logger.warning("[F6] 源码读取失败（文件不可读）: %s: %s (stage=%s)",
                       src_path, e, stage or "scan")
        return None
def _read_parse_source(src_path: str, cache, stage: str
                        ) -> tuple[str, ast.AST] | None:
    src = _read_scan_source(src_path, cache, stage=stage)
    if src is None:
        return None
    tree = parse_or_cache(src_path, src, cache)
    if tree is None:
        return None
    return src, tree
TOKEN_RE = re.compile(r"[a-zA-Z_]\w*")
def _export_surface(ctx: dict, fkey: str, tree: ast.Module) -> tuple[set, bool]:
    cached = (ctx.get("exported") or {}).get(fkey)
    if cached is None:
        return collect_module_exports_state(tree)
    return cached, (ctx.get("exported_exact") or {}).get(fkey, True)
_NOQA_F401_RE = re.compile(
    r"#\s*noqa\s*(?:[#()].*)?$"
    r"|#\s*noqa\s*:\s*[^\n#(]*\bF401\b",
    re.IGNORECASE,
)
def _is_tc_ref(n):
    return (isinstance(n, ast.Name) and n.id == "TYPE_CHECKING") or (
        isinstance(n, ast.Attribute) and n.attr == "TYPE_CHECKING")
def _push_child_nodes(todo, n):
    for f in n._fields:
        v = getattr(n, f, None)
        if isinstance(v, ast.AST):
            todo.append(v)
        elif isinstance(v, list):
            todo.extend(c for c in v if isinstance(c, ast.AST))
def _test_is_type_checking(test: ast.expr) -> bool:
    if type(test) in (ast.Name, ast.Attribute):
        return _is_tc_ref(test)
    if type(test) is ast.BoolOp:
        return any(_test_is_type_checking(value) for value in test.values)
    return False
def _collect_tc_imports(tc_if: ast.If, tc: set) -> None:
    sub_todo = collections.deque(tc_if.body)
    while sub_todo:
        sub = sub_todo.popleft()
        if isinstance(sub, (ast.Import, ast.ImportFrom)):
            for alias in sub.names:
                tc.add(alias.asname or alias.name.split(".")[0])
        _push_child_nodes(sub_todo, sub)
def _record_alias_targets(aliases, alias, source_mod):
    if not alias.asname:
        return
    _mods = aliases.setdefault(alias.asname, set())
    _mods.add(source_mod)
    _mods.add(alias.name.split(".")[-1])
def _record_from_imports(n, source_mod: str, fin, aliases,
                          star_mods) -> None:
    for alias in n.names:
        if alias.name == "*":
            star_mods.add(source_mod)
            continue
        fin.setdefault(alias.name, set()).add(source_mod)
        _record_alias_targets(aliases, alias, source_mod)
def _importfrom_target(node: ast.AST, pkg_chain: tuple | list) -> str | None:
    if type(node) is not ast.ImportFrom:
        return None
    if node.module:
        return node.module.split(".")[-1]
    if not pkg_chain:
        return None
    _lvl = getattr(node, "level", 0)
    if 1 <= _lvl <= len(pkg_chain):
        return pkg_chain[_lvl - 1]
    return None
def _collect_import_evidence(n: ast.AST, imps: list, fin: dict,
                             aliases: dict, star_mods: set,
                             pkg_chain: tuple | list = _DEFAULT_PKG_CHAIN) -> None:
    imps.append(n)
    tn = type(n)
    if tn is ast.ImportFrom:
        _target = _importfrom_target(n, pkg_chain)
        if _target is not None:
            _record_from_imports(n, _target, fin, aliases, star_mods)
    elif tn is ast.Import:
        _collect_plain_import_evidence(n, aliases)
def _collect_plain_import_evidence(n: ast.Import, aliases: dict) -> None:
    for alias in n.names:
        if alias.asname:
            aliases.setdefault(alias.asname, set()).add(
                alias.name.split(".")[-1])
def _pkg_chain_of(skill_dir, p: str) -> tuple:
    _rel = os.path.relpath(p, skill_dir).replace("\\", "/")
    _rel_dir = _rel.rsplit("/", 1)[0] if "/" in _rel else ""
    chain = list(reversed(_rel_dir.split("/"))) if _rel_dir else []
    _root = os.path.basename(os.path.abspath(skill_dir))
    if not _root:
        return ()
    chain.append(_root)
    return tuple(chain)
def module_file_map(
    skill_dir: str, include_tests: bool = _DEFAULT_INCLUDE_TESTS,
) -> dict[str, str]:
    _all_paths = sorted(iter_py_files(skill_dir, include_tests=include_tests))
    _base_counts: collections.Counter = collections.Counter(
        os.path.splitext(os.path.basename(p))[0] for p in _all_paths)
    core_files = {}
    for p in _all_paths:
        base = os.path.splitext(os.path.basename(p))[0]
        if _base_counts[base] > 1 or base.lower() == "__init__":
            core_files[os.path.relpath(p, skill_dir).replace("\\", "/")[:-3]] = p
        else:
            core_files[base] = p
    return core_files
def _resolve_path_map(skill_dir: str,
                      path_map: dict[str, str] | None) -> dict[str, str]:
    return module_file_map(skill_dir) if path_map is None else path_map
def module_path(skill_dir: str, module: str,
                path_map: dict[str, str] | None = None) -> str:
    paths = _resolve_path_map(skill_dir, path_map)
    found = paths.get(module)
    if found is not None:
        return found
    return os.path.join(skill_dir, module.replace("/", os.sep) + ".py")
def ctx_file_path(ctx: dict, fkey: str) -> str | None:
    return ((ctx.get("files") or {}).get(fkey) or {}).get("path")
def _note_attr_uses(n, an, aa, unowned):
    if type(n.value) is ast.Name:
        an.setdefault(n.attr, set()).add(n.value.id)
    elif type(n.value) is ast.Attribute:
        aa.setdefault(n.attr, set()).add(n.value.attr)
    else:
        unowned.add(n.attr)
def _note_str_tokens(n, str_all, str_ev, doc_ids):
    toks = TOKEN_RE.findall(n.value)
    if not toks:
        return
    str_all.update(toks)
    if id(n) not in doc_ids:
        str_ev.update(toks)
def _call_symbol(node: ast.Call) -> str | None:
    func = node.func
    if type(func) is ast.Name:
        return func.id
    if type(func) is ast.Attribute:
        return func.attr
    return None
def _note_call_count(n, calls):
    sym = _call_symbol(n)
    if sym is not None:
        calls[sym] = calls.get(sym, 0) + 1
def _docstring_id(body):
    if (body and type(body[0]) is ast.Expr
            and type(body[0].value) is ast.Constant
            and type(body[0].value.value) is str):
        return id(body[0].value)
    return None
_FILE_EVIDENCE_KEYS: tuple[str, ...] = (
    "name_uses", "attr_name_uses", "attr_attr_uses", "attr_unowned",
    "imports", "from_import_names", "import_aliases", "tc_imports",
    "str_all", "call_counts",
)
class _FileEvidence:
    __slots__ = (*_FILE_EVIDENCE_KEYS, "doc_ids")
    def __init__(self) -> None:
        self.name_uses: collections.Counter = collections.Counter()
        self.attr_name_uses: dict[str, set] = {}
        self.attr_attr_uses: dict[str, set] = {}
        self.attr_unowned: set = set()
        self.imports: list = []
        self.from_import_names: dict[str, set[str]] = {}
        self.import_aliases: dict[str, set] = {}
        self.tc_imports: set = set()
        self.str_all: collections.Counter = collections.Counter()
        self.doc_ids: set[int] = set()
        self.call_counts: dict[str, int] = {}
    def note(self, node, str_ev, star_mods, pkg_chain) -> None:
        tn = type(node)
        if tn is ast.Name:
            self.name_uses[node.id] += 1
            return
        if tn is ast.Attribute:
            _note_attr_uses(node, self.attr_name_uses, self.attr_attr_uses,
                            self.attr_unowned)
            return
        if tn is ast.Constant and type(node.value) is str:
            _note_str_tokens(node, self.str_all, str_ev, self.doc_ids)
            return
        self._note_structure(node, star_mods, pkg_chain)
    def _note_structure(self, node, star_mods, pkg_chain) -> None:
        tn = type(node)
        if tn is ast.Call:
            _note_call_count(node, self.call_counts)
        elif tn is ast.If:
            _note_type_checking(node, self.tc_imports)
        elif tn is ast.Import or tn is ast.ImportFrom:
            _collect_import_evidence(node, self.imports,
                                     self.from_import_names,
                                     self.import_aliases, star_mods,
                                     pkg_chain=pkg_chain)
        else:
            _note_definition(node, self.doc_ids)
def _note_type_checking(node, tc_imports: set) -> None:
    if _test_is_type_checking(node.test):
        _collect_tc_imports(node, tc_imports)
def _note_definition(node, doc_ids: set) -> None:
    if type(node) not in (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.ClassDef):
        return
    did = _docstring_id(node.body)
    if did is not None:
        doc_ids.add(did)
def _scan_one_file(fkey, p, skill_dir, ctx, cache):
    parsed = _read_parse_source(p, cache, "build_context")
    if parsed is None:
        return False
    src, tree = parsed
    pkg_chain = _pkg_chain_of(skill_dir, p)
    ctx["files"][fkey] = {"path": p, "src": src, "tree": tree,
                          "base": fkey.rsplit("/", 1)[-1]}
    ev = _FileEvidence()
    todo = collections.deque([tree])
    while todo:
        n = todo.popleft()
        ev.note(n, ctx["str_evidence"], ctx["star_imports"], pkg_chain)
        _push_child_nodes(todo, n)
    aliases, _, _, dynamic_funcs = _collect_test_imports(
        tree, skill_dir, pkg_chain)
    for owner, targets in aliases.items():
        ev.import_aliases.setdefault(owner, set()).update(targets)
    _store_file_evidence(ctx, fkey, ev, tree)
    dynamic_ev = {"unresolved_dynamic": set()}
    for node in walk_nodes(tree):
        if type(node) is ast.Call:
            _record_unresolved_dynamic_consumption(
                node, fkey, dynamic_ev, aliases, skill_dir, None,
                dynamic_funcs=dynamic_funcs)
    if dynamic_ev["unresolved_dynamic"]:
        logger.warning(
            "[F6] 源码动态消费无法静态解析，删除判定 fail-closed: %s", fkey)
        return False
    return True
def _store_file_evidence(ctx, fkey: str, ev: _FileEvidence, tree) -> None:
    for key in _FILE_EVIDENCE_KEYS:
        ctx[key][fkey] = getattr(ev, key)
    exports, exact = collect_module_exports_state(tree)
    ctx["exported"][fkey] = exports
    ctx["exported_exact"][fkey] = exact
def build_scan_context(skill_dir: str, cache: Any = None,
                       include_tests: bool = _DEFAULT_INCLUDE_TESTS) -> dict:
    core_files = module_file_map(skill_dir, include_tests=include_tests)
    ctx: dict[str, Any] = {
        "files": {},
        **{key: {} for key in _FILE_EVIDENCE_KEYS},
        "exported": {},
        "exported_exact": {},
        "str_evidence": collections.Counter(),
        "star_imports": set(),
        "scan_complete": True,
        "scan_errors": [],
    }
    for fkey, p in core_files.items():
        if not _scan_one_file(fkey, p, skill_dir, ctx, cache):
            ctx["scan_complete"] = False
            ctx["scan_errors"].append(fkey)
    return ctx
def _self_name_uses(node: ast.AST, name: str) -> int:
    cnt = 0
    for sub in walk_nodes(node):
        if type(sub) is ast.Name and sub.id == name:
            cnt += 1
    return cnt
def _init_key_variants(module: str, skill_dir: str = _DEFAULT_SKILL_DIR) -> set:
    mod_key = module.rsplit("/", 1)[-1]
    keys = {mod_key}
    if mod_key.lower() == "__init__":
        if "/" in module:
            keys.add(module.rsplit("/", 1)[0].rsplit("/", 1)[-1])
        elif skill_dir:
            _pkg = os.path.basename(os.path.normpath(skill_dir))
            if _pkg:
                keys.add(_pkg)
    return keys
class _UseEvidence(NamedTuple):
    importers: dict
    attr_name_all: dict
    attr_attr_all: dict
    alias_mods: dict
    str_evidence: Any
    star_mods: set
    attr_unowned: set
def _merge_symbol_sets(ctx, key: str) -> dict[str, set]:
    merged: dict[str, set] = {}
    for per_file in ctx.get(key, {}).values():
        for symbol, values in per_file.items():
            merged.setdefault(symbol, set()).update(values)
    return merged
def _aggregate_use_evidence(ctx) -> _UseEvidence:
    return _UseEvidence(
        importers=_merge_symbol_sets(ctx, "from_import_names"),
        attr_name_all=_merge_symbol_sets(ctx, "attr_name_uses"),
        attr_attr_all=_merge_symbol_sets(ctx, "attr_attr_uses"),
        alias_mods=_merge_symbol_sets(ctx, "import_aliases"),
        str_evidence=ctx.get("str_evidence", {}),
        star_mods=ctx.get("star_imports", set()),
        attr_unowned=set().union(*ctx.get("attr_unowned", {}).values()),
    )
def _candidate_query_names(fkey, meta, skill_dir):
    mod_name = meta.get("base", fkey.rsplit("/", 1)[-1])
    qnames = {mod_name}
    if mod_name.lower() == "__init__":
        qnames |= _init_key_variants(fkey, skill_dir)
        _p = meta.get("path")
        if _p:
            _pkg = os.path.basename(os.path.dirname(os.path.abspath(_p)))
            if _pkg:
                qnames.add(_pkg)
    return qnames
def _e3_attr_hit(name, qnames, ev) -> bool:
    if name in ev.attr_unowned:
        return True
    name_owners = ev.attr_name_all.get(name, set())
    if name_owners & qnames:
        return True
    if ev.attr_attr_all.get(name, set()) & qnames:
        return True
    return any(ev.alias_mods.get(owner, set()) & qnames
               for owner in name_owners)
def _scan_dead_functions(skill_dir: str, cache: Any = None,
                         _ctx: dict | None = None) -> list:
    ctx = _ctx or build_scan_context(skill_dir, cache=cache, include_tests=False)
    if not ctx.get("scan_complete", True):
        logger.warning(
            "[F6] 源码扫描不完整，死函数判定 fail-closed 跳过: %s",
            ctx.get("scan_errors") or [])
        return []
    ev = _aggregate_use_evidence(ctx)
    dead = []
    for fkey, meta in ctx["files"].items():
        dead.extend(_dead_candidates_in_file(fkey, meta, skill_dir, ctx, ev))
    return dead
def _is_protocol_hook(name: str) -> bool:
    return len(name) > 4 and name.startswith("__") and name.endswith("__")
def _dead_candidates_in_file(fkey, meta, skill_dir, ctx,
                             ev: _UseEvidence) -> list:
    tree = meta["tree"]
    qnames = _candidate_query_names(fkey, meta, skill_dir)
    exported, export_exact = _export_surface(ctx, fkey, tree)
    dead: list = []
    if not export_exact:
        logger.debug(
            "[F6] %s 的 __all__ 无法静态解析（动态导出面），顶层定义判定"
            " fail-closed 豁免", fkey)
        return dead
    own_uses = ctx.get("name_uses", {}).get(fkey, collections.Counter())
    self_uses = _top_level_self_uses(tree)
    for node in tree.body:
        kind, name = _top_level_definition(node)
        if kind is None:
            continue
        if (node.decorator_list
                or _is_protocol_hook(name)
                or name.startswith(_DYN_REGISTER_PREFIXES)
                or name in exported):
            continue
        if _used_in_own_file(name, own_uses, self_uses.get(name, 0)):
            continue
        if _used_cross_file(name, qnames, ev):
            continue
        dead.append((fkey, kind, name, node.lineno))
    return dead
def _top_level_definition(node) -> tuple[str | None, str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return "func", node.name
    if isinstance(node, ast.ClassDef):
        return "class", node.name
    return None, ""
def _top_level_self_uses(tree: ast.Module) -> collections.Counter:
    self_uses = collections.Counter()
    for node in tree.body:
        kind, name = _top_level_definition(node)
        if kind is not None:
            self_uses[name] += _self_name_uses(node, name)
    return self_uses
def _used_in_own_file(name: str, own_uses, self_use_count: int) -> bool:
    return own_uses.get(name, 0) > self_use_count
def _used_cross_file(name: str, qnames: set, ev: _UseEvidence) -> bool:
    if ev.importers.get(name, set()) & qnames:
        return True
    if _e3_attr_hit(name, qnames, ev):
        return True
    if ev.str_evidence.get(name, 0) > 0:
        return True
    return not name.startswith("_") and bool(ev.star_mods & qnames)
def _noqa_line_flags(node, lines):
    end = getattr(node, "end_lineno", None) or node.lineno
    seg_lines = lines[node.lineno - 1:end]
    line_noqa = [_NOQA_F401_RE.search(_ln) is not None for _ln in seg_lines]
    return end, line_noqa
def _alias_noqa_exempt(alias, node, end, line_noqa, has_noqa):
    _aln = getattr(alias, "lineno", None)
    if _aln is not None and node.lineno <= _aln <= end:
        _aidx = _aln - node.lineno
        if _aidx >= len(line_noqa):
            return True
        return line_noqa[_aidx]
    return has_noqa
def _file_unused_imports(fkey, meta, ctx, lazy_registered):
    src = meta["src"]
    tree = meta["tree"]
    exported, export_exact = _export_surface(ctx, fkey, tree)
    if not export_exact:
        logger.debug(
            "[F6] %s 的 __all__ 无法静态解析（动态导出面），未使用导入判定"
            " fail-closed 豁免", fkey)
        return []
    ictx = _UnusedImportContext(
        lines=src.split("\n"),
        name_uses=ctx.get("name_uses", {}).get(fkey, collections.Counter()),
        attr_name_uses=ctx.get("attr_name_uses", {}).get(fkey, {}),
        str_all=ctx.get("str_all", {}).get(fkey, collections.Counter()),
        tc_imports=ctx.get("tc_imports", {}).get(fkey, set()),
        exported=exported,
        lazy_registered=lazy_registered,
    )
    is_package_init = fkey.rsplit("/", 1)[-1].lower() == "__init__"
    facade_stmt_ids = _module_scope_import_ids(tree) if is_package_init else set()
    if facade_stmt_ids:
        logger.debug(
            "[F6] %s 是包初始化模块，模块级 import 视为再导出面豁免"
            "（%d 条）", fkey, len(facade_stmt_ids))
    unused = []
    for node in ctx.get("imports", {}).get(fkey, []):
        if isinstance(node, ast.ImportFrom) and node.module == "__future__":
            continue
        if id(node) in facade_stmt_ids:
            continue
        unused.extend(_unused_aliases_of_stmt(node, ictx))
    return unused
def _alias_symbol(alias) -> str:
    return alias.asname or alias.name.split(".")[0]
def _alias_exempt_static(alias, tc: set, lazy_registered: set,
                         exported: set) -> bool:
    if alias.name == "*":
        return True
    sym = _alias_symbol(alias)
    return sym in tc or sym in lazy_registered or sym in exported
def _alias_has_use_evidence(alias, nu, au: dict, str_all) -> bool:
    sym = _alias_symbol(alias)
    return nu.get(sym, 0) > 0 or sym in au or str_all.get(sym, 0) > 0
class _UnusedImportContext(NamedTuple):
    lines: list
    name_uses: Any
    attr_name_uses: dict
    str_all: Any
    tc_imports: set
    exported: set
    lazy_registered: set
class _NoqaWindow(NamedTuple):
    end: int
    line_noqa: list
    stmt_noqa: bool
    has_noqa: bool
def _noqa_window(node, lines) -> _NoqaWindow:
    end, line_noqa = _noqa_line_flags(node, lines)
    return _NoqaWindow(end, line_noqa, bool(line_noqa) and line_noqa[0],
                       any(line_noqa))
def _alias_is_used(alias, node, window: _NoqaWindow, ictx) -> bool:
    if _alias_exempt_static(alias, ictx.tc_imports, ictx.lazy_registered,
                            ictx.exported):
        return True
    if window.stmt_noqa:
        return True
    if _alias_noqa_exempt(alias, node, window.end, window.line_noqa,
                          window.has_noqa):
        return True
    return _alias_has_use_evidence(alias, ictx.name_uses, ictx.attr_name_uses,
                                   ictx.str_all)
def _unused_aliases_of_stmt(node, ictx: _UnusedImportContext) -> list:
    window = _noqa_window(node, ictx.lines)
    unused = []
    for alias in node.names:
        if _alias_is_used(alias, node, window, ictx):
            continue
        rep_ln = getattr(alias, "lineno", None) or node.lineno
        unused.append((rep_ln, alias.asname or alias.name))
    return unused
def _scan_unused_imports(skill_dir: str, cache: Any = None, _ctx: dict | None = None) -> dict:
    ctx = _ctx or build_scan_context(skill_dir, cache=cache, include_tests=False)
    if not ctx.get("scan_complete", True):
        logger.warning(
            "[F6] 源码扫描不完整，未使用导入判定 fail-closed 跳过: %s",
            ctx.get("scan_errors") or [])
        return {}
    lazy_registered = collect_lazy_registered_names(skill_dir)
    result = {}
    for fkey, meta in ctx["files"].items():
        unused = _file_unused_imports(fkey, meta, ctx, lazy_registered)
        if unused:
            result[fkey] = unused
    return result
def _record_reexport_names(reexported: dict, target: str, names) -> None:
    for alias in names:
        if alias.name != "*":
            reexported[target].add(alias.name)
_TRY_STMT_TYPES: tuple[type, ...] = tuple(
    node_type for node_type in (ast.Try, getattr(ast, "TryStar", None))
    if node_type is not None)
_MATCH_STMT_TYPES: tuple[type, ...] = tuple(
    node_type for node_type in (getattr(ast, "Match", None),)
    if node_type is not None)
def _iter_module_scope_stmts(stmts) -> Iterator[ast.stmt]:
    for node in stmts:
        yield node
        if isinstance(node, (ast.If, ast.For, ast.AsyncFor, ast.While,
                             ast.With, ast.AsyncWith)):
            yield from _iter_module_scope_stmts(node.body)
            yield from _iter_module_scope_stmts(getattr(node, "orelse", ()))
        elif isinstance(node, _TRY_STMT_TYPES):
            yield from _iter_module_scope_stmts(node.body)
            for handler in getattr(node, "handlers", ()):
                yield from _iter_module_scope_stmts(handler.body)
            yield from _iter_module_scope_stmts(node.orelse)
            yield from _iter_module_scope_stmts(node.finalbody)
        elif isinstance(node, _MATCH_STMT_TYPES):
            for case in node.cases:
                yield from _iter_module_scope_stmts(case.body)
def _module_scope_import_ids(tree: ast.AST) -> set[int]:
    return {id(node) for node in _iter_module_scope_stmts(
        getattr(tree, "body", ()))
        if isinstance(node, (ast.Import, ast.ImportFrom))}
def _collect_reexport_from_tree(tree: ast.AST, reexported: dict,
                                pkg_chain: tuple | list = _DEFAULT_PKG_CHAIN) -> None:
    for node in _iter_module_scope_stmts(getattr(tree, "body", ())):
        _target = _importfrom_target(node, pkg_chain)
        if _target is not None:
            _record_reexport_names(reexported, _target, node.names)
def _iter_parsed_files(skill_dir, cache, *, stage: str,
                       skip_paths=(), evidence_errors=None):
    for p in iter_py_files(skill_dir, include_tests=True):
        if p in skip_paths:
            continue
        parsed = _read_parse_source(p, cache, stage)
        if parsed is None:
            if evidence_errors is not None:
                evidence_errors.add(
                    os.path.relpath(p, skill_dir).replace("\\", "/"))
            continue
        yield p, parsed[1]
def _scan_reexport_usage(skill_dir, cache=None, evidence_errors=None):
    reexported = collections.defaultdict(set)
    for p, tree in _iter_parsed_files(
            skill_dir, cache, stage="reexport_usage",
            evidence_errors=evidence_errors):
        _collect_reexport_from_tree(
            tree, reexported, pkg_chain=_pkg_chain_of(skill_dir, p))
    return reexported
def _check_reexport(module, symbol, reexport_map, skill_dir=_DEFAULT_SKILL_DIR):
    head = symbol.split(".")[0]
    return any(
        head in reexport_map.get(k, set())
        for k in _init_key_variants(module, skill_dir))
def _core_paths_with_collision(skill_dir: str) -> tuple[list, bool]:
    core_paths: list[str] = []
    seen_bases: set[str] = set()
    collision = False
    for p in iter_py_files(skill_dir, include_tests=False):
        core_paths.append(p)
        _b = os.path.splitext(os.path.basename(p))[0]
        if _b.lower() == "__init__":
            continue
        if _b in seen_bases:
            collision = True
        seen_bases.add(_b)
    return core_paths, collision
def _has_deep_relative_import(core_paths: list, cache: Any) -> bool:
    for p in core_paths:
        _src = _read_scan_source(p, cache, stage="reexport_ctx_equiv_check")
        if _src and re.search(r"\bfrom\s+\.{2,}[\w.]*\s+import\b", _src):
            return True
    return False
def _reexport_from_ctx_trees(ctx: dict, skill_dir: str) -> dict:
    reexported: dict = collections.defaultdict(set)
    for meta in (ctx.get("files") or {}).values():
        tree = meta.get("tree")
        path = meta.get("path")
        if tree is None or not path:
            continue
        _collect_reexport_from_tree(
            tree, reexported, _pkg_chain_of(skill_dir, path))
    return reexported
def _merge_tests_reexport(reexported: dict, skill_dir: str,
                          core_paths: list, tests_evidence: dict | None,
                          cache: Any) -> None:
    if tests_evidence is not None:
        for src_mod, names in (tests_evidence.get("reexported") or {}).items():
            reexported[src_mod].update(names or ())
        return
    core_set = set(core_paths)
    for p, tree in _iter_parsed_files(skill_dir, cache,
                                       stage="reexport_light_scan",
                                       skip_paths=core_set):
        _collect_reexport_from_tree(
            tree, reexported, pkg_chain=_pkg_chain_of(skill_dir, p))
def reexport_map_from_ctx(ctx: dict, skill_dir: str, cache: Any = None,
                           tests_evidence: dict | None = None) -> dict:
    core_paths, collision = _core_paths_with_collision(skill_dir)
    if collision:
        return _scan_reexport_usage(skill_dir, cache=cache)
    if _has_deep_relative_import(core_paths, cache):
        return _scan_reexport_usage(skill_dir, cache=cache)
    reexported = _reexport_from_ctx_trees(ctx, skill_dir)
    _merge_tests_reexport(reexported, skill_dir, core_paths,
                          tests_evidence, cache)
    return reexported
def _check_local_ref(module, symbol, skill_dir, ctx: dict | None = None,
                     cache: Any = None):
    p = ctx_file_path(ctx, module) if ctx is not None else None
    if not p:
        p = module_path(skill_dir, module)
    if not os.path.exists(p):
        return True
    src = _read_scan_source(p, cache, stage="local_ref")
    if src is None:
        return True
    return collections.Counter(
        TOKEN_RE.findall(src)).get(symbol.split(".")[0], 0) > 1
def _safe_function_candidates(ctx: dict, tests_evidence: dict,
                              reexport_map: dict, skill_dir: str,
                              cache: Any) -> list:
    funcs = []
    for module, kind, name, lineno in _scan_dead_functions(
            skill_dir, cache=cache, _ctx=ctx):
        if _check_reexport(module, name, reexport_map, skill_dir=skill_dir):
            continue
        if tests_consumes_symbol(tests_evidence, module, name,
                                  skill_dir=skill_dir):
            continue
        funcs.append((module, kind, name, lineno))
    return funcs
def _safe_import_candidates(ctx: dict, tests_evidence: dict,
                            reexport_map: dict, skill_dir: str,
                            cache: Any) -> dict:
    imports = {}
    use_ev = _aggregate_use_evidence(ctx)
    for module, syms in _scan_unused_imports(
            skill_dir, cache=cache, _ctx=ctx).items():
        qnames = _candidate_query_names(module, ctx["files"][module], skill_dir)
        safe = []
        for lineno, full in syms:
            if _check_reexport(module, full, reexport_map, skill_dir=skill_dir):
                continue
            if _used_cross_file(full.split(".", maxsplit=1)[0], qnames, use_ev):
                continue
            if _check_local_ref(module, full, skill_dir, ctx=ctx, cache=cache):
                continue
            if tests_consumes_symbol(tests_evidence, module, full,
                                      skill_dir=skill_dir):
                continue
            safe.append((lineno, full))
        if safe:
            imports[module] = safe
    return imports
def build_clean_plan(skill_dir: str, cache: Any = None, _ctx: dict | None = None,
                     reexport_map: dict | None = None,
                     tests_evidence: dict | None = None) -> dict:
    ctx = _ctx or build_scan_context(skill_dir, cache=cache, include_tests=False)
    if tests_evidence is None:
        tests_evidence = build_tests_evidence(skill_dir, cache=cache)
    if reexport_map is None:
        reexport_map = reexport_map_from_ctx(
            ctx, skill_dir, cache=cache, tests_evidence=tests_evidence)
    funcs = _safe_function_candidates(ctx, tests_evidence, reexport_map,
                                      skill_dir, cache)
    imports = _safe_import_candidates(ctx, tests_evidence, reexport_map,
                                      skill_dir, cache)
    logger.info("[F6] 安全清理计划构建: 函数%d项, 未用导入%d模块%d项",
                len(funcs), len(imports),
                sum(len(s) for s in imports.values()))
    evidence_errors = (
        [f"source:{key}" for key in (ctx.get("scan_errors") or [])]
        + [f"test:{key}" for key in (tests_evidence.get("scan_errors") or [])])
    evidence_complete = bool(
        ctx.get("scan_complete", True)
        and tests_evidence.get("scan_complete", True)
        and not evidence_errors)
    return {"functions": funcs, "imports": imports,
            "evidence_complete": evidence_complete,
            "evidence_errors": evidence_errors}
_DYN_REF_PATTERNS = [
    r"import_module\s*\(\s*['\"][^'\"]*\b" + "{NAME}" + r"\b",
    r"getattr\s*\(\s*[\w\.]+\s*,\s*['\"]\b" + "{NAME}" + r"\b",
    r"globals\(\)\s*\[\s*['\"]\b" + "{NAME}" + r"\b",
    r"locals\(\)\s*\[\s*['\"]\b" + "{NAME}" + r"\b",
    r"vars\([^)]*\)\s*\[\s*['\"]\b" + "{NAME}" + r"\b",
]
def _new_call_ref_graph() -> dict:
    return collections.defaultdict(lambda: [0, set()])
def _build_call_ref_graph(skill_dir, cache=None, evidence_errors=None):
    refs = _new_call_ref_graph()
    for p, tree in _iter_parsed_files(
            skill_dir, cache, stage="call_ref_graph",
            evidence_errors=evidence_errors):
        rel = os.path.relpath(p, skill_dir).replace("\\", "/")
        _record_call_refs(tree, rel, refs)
    return refs
def _record_call_refs(tree, rel: str, refs: dict) -> None:
    for node in walk_nodes(tree):
        if type(node) is ast.Call:
            _absorb_tests_call(node, rel, refs)
_DYN_REF_CACHE_MAX = 1024
@lru_cache(maxsize=_DYN_REF_CACHE_MAX)
def _dyn_ref_regexes(symbol: str) -> tuple:
    return tuple(re.compile(p.replace("{NAME}", re.escape(symbol)))
                 for p in _DYN_REF_PATTERNS)
def _has_dynamic_ref(symbol, all_src):
    return any(p.search(all_src) for p in _dyn_ref_regexes(symbol))
def _concat_all_sources(skill_dir: str, cache: Any,
                        evidence_errors=None) -> str:
    _src_parts: list[str] = []
    for p in iter_py_files(skill_dir, include_tests=True):
        _src = _read_scan_source(p, cache, stage="cross_validate")
        if _src is None:
            if evidence_errors is not None:
                evidence_errors.add(
                    os.path.relpath(p, skill_dir).replace("\\", "/"))
            continue
        _src_parts.append(_src)
    return "\n".join(_src_parts)
class _CvEvidence(NamedTuple):
    all_src: str
    call_graph: dict
    reexport_map: dict
    lazy_registered: set
    called_symbols: set
    evidence_errors: set
def _prepare_cv_evidence(skill_dir: str, shared: dict,
                         output_dir: str | None, cache: Any) -> _CvEvidence:
    evidence_errors: set[str] = set()
    builders = {
        "all_src": lambda: _concat_all_sources(
            skill_dir, cache, evidence_errors=evidence_errors),
        "call_graph": lambda: _build_call_ref_graph(
            skill_dir, cache=cache, evidence_errors=evidence_errors),
        "reexport_map": lambda: _scan_reexport_usage(
            skill_dir, cache=cache, evidence_errors=evidence_errors),
        "lazy_registered": lambda: collect_lazy_registered_names(skill_dir),
    }
    resolved = {
        key: (injected if (injected := shared.get(key)) is not None
              else builder())
        for key, builder in builders.items()
    }
    return _CvEvidence(
        all_src=resolved["all_src"], call_graph=resolved["call_graph"],
        reexport_map=resolved["reexport_map"],
        lazy_registered=resolved["lazy_registered"],
        called_symbols=load_called_symbols(output_dir),
        evidence_errors=evidence_errors,
    )
def _cv_exempt_reason(module: str, name: str, ev: _CvEvidence,
                      skill_dir: str) -> str | None:
    if _has_dynamic_ref(name, ev.all_src):
        return "动态调用/反射引用(引擎A误判)"
    if _check_reexport(module, name, ev.reexport_map, skill_dir=skill_dir):
        return "re-export 跨模块依赖(引擎A误判)"
    if name in ev.lazy_registered:
        return "公开面登记表登记(消费锚点)"
    return None
def _cv_confidence_evidence(name: str, eng_a_cnt: int, eng_b_cnt: int,
                            ref_files: set, called_symbols: set
                            ) -> tuple[str, str]:
    if eng_a_cnt <= 1:
        if eng_b_cnt == 0:
            if name in called_symbols:
                return ("MEDIUM",
                        (f"引擎A引用={eng_a_cnt}, 引擎B真实调用=0, "
                         "C1调用图显示该符号被调用(需复核)"))
            return "HIGH", f"引擎A引用={eng_a_cnt}, 引擎B真实调用=0"
        return ("MEDIUM",
                (f"引擎A引用={eng_a_cnt}, 引擎B真实调用={eng_b_cnt}"
                 f" @{sorted(ref_files)[:2]}"))
    return "MEDIUM", f"引擎A引用={eng_a_cnt}(需复核)"
def cross_validate_deadcode(skill_dir: str, candidates: list | None = None,
                            output_dir: str | None = None, cache: Any = None,
                            _shared: dict | None = None) -> list:
    cache = ensure_entry_warmed(skill_dir, cache, "死代码交叉验证 cross_validate_deadcode")
    skill_dir = os.path.abspath(skill_dir)
    shared = _shared or {}
    if candidates is None:
        candidates = _scan_dead_functions(skill_dir, cache=cache)
    ev = _prepare_cv_evidence(skill_dir, shared, output_dir, cache)
    results = _cv_judge_candidates(candidates, ev, skill_dir)
    _conf = collections.Counter(r[3] for r in results)
    logger.info("[F6] 死代码交叉验证完成: 候选%d项 → "
                "HIGH=%d/MEDIUM=%d/EXEMPT=%d/ERROR=%d，证据错误%d项",
                len(results), _conf.get("HIGH", 0),
                _conf.get("MEDIUM", 0), _conf.get("EXEMPT", 0),
                _conf.get("ERROR", 0), len(ev.evidence_errors))
    _emit_cv_html_report(
        skill_dir, results, _conf, evidence_errors=ev.evidence_errors)
    return results
def _cv_judge_candidates(candidates: list, ev: _CvEvidence,
                         skill_dir: str) -> list:
    results = []
    evidence_errors = sorted(getattr(ev, "evidence_errors", ()))
    for module, _kind, name, lineno in candidates:
        if evidence_errors:
            results.append((
                module, name, lineno, "ERROR",
                "扫描证据不完整，交叉验证 fail-closed: "
                + ", ".join(evidence_errors[:5]),
            ))
            continue
        _exempt = _cv_exempt_reason(module, name, ev, skill_dir)
        if _exempt is not None:
            results.append((module, name, lineno, "EXEMPT", _exempt))
            continue
        eng_a_cnt = len(re.findall(r"\b" + re.escape(name) + r"\b",
                                  ev.all_src))
        eng_b_cnt, ref_files = ev.call_graph.get(name, [0, set()])
        conf, evidence = _cv_confidence_evidence(
            name, eng_a_cnt, eng_b_cnt, ref_files, ev.called_symbols)
        results.append((module, name, lineno, conf, evidence))
    return results
def _build_cleanup_items(skill_dir: str, plan: dict, fixed_sources: dict,
                         path_map: dict[str, str] | None = None) -> list:
    by_module: dict[str, list] = {}
    for module, kind, name, lineno in plan.get("functions", []):
        by_module.setdefault(module, []).append((
            "dead_code", "delete_function", f"删除死代码 {kind}: {name}", lineno))
    for module, syms in plan.get("imports", {}).items():
        for lineno, full in syms:
            by_module.setdefault(module, []).append((
                "unused_import", "remove_import", f"移除未使用导入: {full}", lineno))
    cleanup_items = []
    paths = _resolve_path_map(skill_dir, path_map)
    for module, changes in by_module.items():
        category, operation, description = _fold_module_changes(changes)
        cleanup_items.append({
            "file_path": module_path(skill_dir, module, paths),
            "line": min(change[3] for change in changes),
            "category": category,
            "operation": operation,
            "description": description,
            "confidence": 0.8,
            "severity": _DEADCODE_SEVERITY,
            "fixed_source": fixed_sources.get(module, ""),
        })
    return cleanup_items
def _fold_module_changes(changes: list) -> tuple[str, str, str]:
    if len(changes) == 1:
        category, operation, description, _lineno = changes[0]
        return category, operation, description
    category = ("dead_code" if any(c[0] == "dead_code" for c in changes)
                else "unused_import")
    operation = ("delete_deadcode_batch" if category == "dead_code"
                 else "remove_import_batch")
    return (category, operation,
            "应用模块级清理计划（原子审核）: "
            + "; ".join(change[2] for change in changes))
def _zero_consumer_report(skill_dir: str) -> dict:
    try:
        return zero_consumer_summary(skill_dir)
    except Exception as _e:
        logger.warning("[F6] 零消费者检测失败(降级空集): %s", _e, exc_info=True)
        return {"total": 0, "dead_stubs": [], "orphan_utils": [],
                "unreadable": [], "can_delete": 0, "error": str(_e)[:200]}
def _degraded_summary_fallback(skill_dir: str, error=None) -> dict:
    try:
        plan_file = cleanup_plan_path(skill_dir)
    except Exception as _e:  # noqa: BLE001 — 降级通道自守：任何落点解析失败都不得再抛
        logger.debug("[F6] 降级回执无法解析 plan 落点: %s", _e)
        plan_file = ""
    result = {
        "enqueued": 0,
        "total_pending": 0,
        "next_action": "retry_enqueue",
        "plan_file": plan_file,
        "blocked_items": 0,
        "require_confirm_items": 0,
        "degraded": True,
    }
    if error is not None:
        result["error"] = safe_text(error)[:200]
    return result
def _degraded_enqueue_summary(skill_dir: str, error=None) -> dict:
    try:
        result = enqueue_cleanup_plan(
            skill_dir, [], source="run_deadcode_cleanup")
    except Exception as _e:  # noqa: BLE001 — 降级通道自守：读队失败不得击穿主流程
        logger.warning("[F6] 降级回执无法读取待审队列: %s", _e)
        return _degraded_summary_fallback(skill_dir, error=error or _e)
    if error is not None:
        result["degraded"] = True
        result["error"] = safe_text(error)[:200]
        result["next_action"] = "retry_enqueue"
    return result
def _enqueue_cleanup_items(skill_dir: str, plan: dict, fixed_sources: dict,
                           path_map: dict[str, str] | None = None) -> dict:
    try:
        _cleanup_items = _build_cleanup_items(skill_dir, plan, fixed_sources,
                                             path_map)
    except Exception as _e:
        logger.warning("[F6] 清理项装配失败(降级不入队): %s", _e, exc_info=True)
        return _degraded_enqueue_summary(skill_dir, error=_e)
    if not _cleanup_items:
        return _degraded_enqueue_summary(skill_dir)
    try:
        return enqueue_cleanup_plan(skill_dir, _cleanup_items,
                                    source="run_deadcode_cleanup")
    except Exception as _e:
        logger.warning("[F6] 清理方案入AI审核队列失败: %s", _e, exc_info=True)
        return _degraded_enqueue_summary(skill_dir, error=_e)
def enqueue_cleanup_review(skill_dir: str, plan: dict, fixed_sources: dict,
                           path_map: dict[str, str] | None = None) -> dict:
    return {
        "zero_consumers": _zero_consumer_report(skill_dir),
        "ai_review": _enqueue_cleanup_items(skill_dir, plan, fixed_sources,
                                            path_map),
    }
def _emit_cv_html_report(skill_dir: str, results: list,
                         conf: collections.Counter,
                         evidence_errors=None) -> None:
    high = conf.get("HIGH", 0)
    medium = conf.get("MEDIUM", 0)
    exempt = conf.get("EXEMPT", 0)
    error = conf.get("ERROR", 0)
    errors = sorted(evidence_errors or ())
    summary = (f"候选 {len(results)} 项 → HIGH={high}"
               f" / MEDIUM={medium} / EXEMPT={exempt} / ERROR={error}")
    if errors:
        summary += f"；证据不完整 {len(errors)} 项，已 fail-closed"
    emit_step_html("deadcode_cv", skill_dir, {
        "_stage_hint": "diag:F",
        "status": "error" if errors else "completed",
        "summary": summary,
        "skill_dir": skill_dir,
        "candidates": len(results),
        "evidence_complete": not errors,
        "evidence_errors": errors,
        "distribution": {"HIGH": high, "MEDIUM": medium,
                         "EXEMPT": exempt, "ERROR": error},
        "results": [
            {"module": r[0], "name": r[1], "lineno": r[2],
             "confidence": r[3], "evidence": r[4]}
            for r in results
        ],
    })
def _tests_import_targets(node: ast.AST, chain, skill_dir: str,
                          key_map) -> set[str]:
    legacy = _importfrom_target(node, chain)
    dotted = _importfrom_dotted(node, chain)
    resolved = _skill_module_key(skill_dir, dotted, key_map)
    if resolved is None:
        return {legacy} if legacy is not None else set()
    targets = {resolved}
    if legacy is not None and legacy != resolved:
        module_keys = set(key_map.values()) if key_map else set()
        matches = [key for key in module_keys
                   if legacy in _module_keys_of(key, skill_dir)]
        if len(matches) <= 1:
            targets.add(legacy)
    return targets
def _absorb_tests_importfrom(node: ast.AST, chain, stars: set,
                             reexported: dict, skill_dir: str,
                             key_map) -> None:
    targets = _tests_import_targets(node, chain, skill_dir, key_map)
    for target in targets:
        for alias in node.names:
            if alias.name == "*":
                stars.add(target)
            else:
                reexported[target].add(alias.name)
_DOTTED_SEGMENT_RE = re.compile(r"[^A-Za-z0-9_.]+")
_GETATTR_FUNCS = frozenset({"getattr", "setattr", "hasattr"})
_DYNAMIC_IMPORT_FUNCS = frozenset({"import_module", "__import__"})
def _dynamic_import_aliases(tree: ast.AST) -> dict[str, str]:
    aliases: dict[str, str] = {}
    def record_assignment(target, value) -> None:
        canonical = None
        if type(value) is ast.Name:
            canonical = aliases.get(value.id) or (
                value.id if value.id in _DYNAMIC_IMPORT_FUNCS else None)
        elif type(value) is ast.Attribute and value.attr in _DYNAMIC_IMPORT_FUNCS:
            canonical = value.attr
        if type(target) is ast.Name:
            if canonical is not None:
                aliases[target.id] = canonical
            return
        if (type(target) in (ast.Tuple, ast.List)
                and type(value) in (ast.Tuple, ast.List)):
            for sub_target, sub_value in zip(target.elts, value.elts):
                record_assignment(sub_target, sub_value)
    for node in walk_nodes(tree):
        if type(node) is ast.ImportFrom and node.level == 0:
            for alias in node.names:
                canonical = None
                if node.module == "importlib" and alias.name == "import_module":
                    canonical = "import_module"
                elif node.module == "builtins" and alias.name == "__import__":
                    canonical = "__import__"
                if canonical is not None:
                    aliases[alias.asname or alias.name] = canonical
            continue
        if type(node) not in (ast.Assign, ast.AnnAssign, ast.NamedExpr):
            continue
        targets = getattr(node, "targets", None) or [node.target]
        for target in targets:
            record_assignment(target, node.value)
    return aliases
def _dynamic_call_name(node: ast.AST, dynamic_funcs=None) -> str | None:
    name = _call_symbol(node)
    if name is None:
        return None
    return (dynamic_funcs or {}).get(name, name)
def _dynamic_module_name(node: ast.AST, dynamic_funcs=None) -> str | None:
    if type(node) is not ast.Call or not node.args:
        return None
    if _dynamic_call_name(node, dynamic_funcs) not in _DYNAMIC_IMPORT_FUNCS:
        return None
    module_arg = node.args[0]
    if type(module_arg) is not ast.Constant or type(module_arg.value) is not str:
        return None
    return module_arg.value
def _dotted_expr(node: Any, dynamic_funcs=None) -> str | None:
    parts: list[str] = []
    cur = node
    while type(cur) is ast.Attribute:
        parts.append(cur.attr)
        cur = cur.value
    while type(cur) is ast.Subscript:
        cur = cur.value
    if type(cur) is ast.Call:
        module_name = _dynamic_module_name(cur, dynamic_funcs)
        if module_name is None:
            return None
        if (_dynamic_call_name(cur, dynamic_funcs) == "__import__"
                and "." in module_name
                and _dunder_fromlist_state(cur) is not True):
            module_name = module_name.split(".", 1)[0]
        parts.append(module_name)
        return ".".join(reversed(parts))
    if type(cur) is not ast.Name:
        return None
    parts.append(cur.id)
    return ".".join(reversed(parts))
def _importfrom_dotted(node: ast.ImportFrom, chain) -> str:
    mod = node.module or ""
    level = getattr(node, "level", 0) or 0
    if level and chain and level - 1 < len(chain):
        base = ".".join(reversed(chain[level - 1:]))
        return f"{base}.{mod}" if mod else base
    return mod
def _module_key_lookup(skill_dir: str) -> dict[str, str]:
    return {os.path.normcase(os.path.abspath(path)): key
            for key, path in module_file_map(skill_dir).items()}
def _key_map_suffix_match(name: str, key_map: dict[str, str]) -> str | None:
    rel = name.replace(".", "/").strip("/")
    if not rel:
        return None
    suffixes = (f"/{rel}.py", f"/{rel}/__init__.py")
    matches = {
        key
        for path, key in key_map.items()
        for normalized in (os.path.normcase(path).replace("\\", "/"),)
        if any(normalized.endswith(suffix) for suffix in suffixes)
    }
    return next(iter(matches)) if len(matches) == 1 else None
def _skill_module_key(skill_dir: str, dotted: str,
                      key_map: dict[str, str] | None = None) -> str | None:
    if not dotted or not skill_dir:
        return None
    name = dotted.replace("\\", "/").strip(".")
    pkg = os.path.basename(os.path.normpath(skill_dir))
    if pkg and (name == pkg or name.startswith(pkg + ".")):
        name = name[len(pkg):].lstrip(".")
    rel = name.replace(".", "/")
    file_cand = os.path.join(skill_dir, f"{rel}.py") if rel else None
    init_cand = (os.path.join(skill_dir, rel, "__init__.py") if rel
                 else os.path.join(skill_dir, "__init__.py"))
    for cand in (file_cand, init_cand):
        if not cand or not os.path.isfile(cand):
            continue
        if key_map is not None:
            key = key_map.get(os.path.normcase(os.path.abspath(cand)))
            if key is not None:
                return key
        return ("__init__" if cand is init_cand
                else os.path.splitext(os.path.basename(cand))[0])
    return _key_map_suffix_match(name, key_map) if key_map is not None else None
def _record_test_alias(aliases: dict, name: str, key: str) -> None:
    aliases.setdefault(name, set()).add(key)
def _alias_keys(value) -> set:
    if not value:
        return set()
    return {value} if isinstance(value, str) else set(value)
def _module_import_name(skill_dir: str, key: str, key_map) -> str | None:
    path = dict(map(reversed, (key_map or {}).items())).get(key)
    if path is None:
        return None
    rel = os.path.relpath(path, skill_dir).replace("\\", "/")
    if rel == "__init__.py":
        return os.path.basename(os.path.normpath(skill_dir))
    rel = rel.removesuffix("/__init__.py").removesuffix(".py")
    return rel.replace("/", ".")
def _merge_aliased_module_path(base: str, remainder: str) -> str:
    base_parts = base.split(".")
    remainder_parts = remainder.split(".")
    for size in range(min(len(base_parts), len(remainder_parts)), 0, -1):
        if base_parts[-size:] == remainder_parts[:size]:
            remainder_parts = remainder_parts[size:]
            break
    suffix = ".".join(remainder_parts)
    return f"{base}.{suffix}" if suffix else base
def _nested_aliased_binding_keys(owner: str, aliases: dict, skill_dir: str,
                                 key_map=None) -> set:
    root, _, remainder = owner.partition(".")
    resolved = set()
    import_name = partial(_module_import_name, skill_dir, key_map=key_map)
    roots = _alias_keys(aliases.get(root))
    for base in filter(None, map(import_name, roots)):
        candidates = (f"{base}.{remainder}",
                      _merge_aliased_module_path(base, remainder))
        for dotted in dict.fromkeys(candidates):
            key = _skill_module_key(skill_dir, dotted, key_map)
            resolved.update(_alias_keys(key))
    return resolved
def _test_binding_keys(owner: str, aliases: dict, skill_dir: str,
                       key_map=None) -> set:
    bound = _alias_keys(aliases.get(owner))
    if bound:
        return bound
    root = owner.partition(".")[0]
    if "." in owner and _alias_keys(aliases.get(root)):
        return _nested_aliased_binding_keys(owner, aliases, skill_dir, key_map)
    key = _skill_module_key(skill_dir, owner, key_map)
    return _alias_keys(key)
def _bind_plain_import(node: ast.Import, skill_dir: str,
                       aliases: dict, keys: set, key_map=None) -> None:
    for alias in node.names:
        imported_key = _skill_module_key(skill_dir, alias.name, key_map)
        if imported_key is None:
            continue
        keys.add(imported_key)
        if alias.asname:
            _record_test_alias(aliases, alias.asname, imported_key)
            continue
        bound_name = alias.name.split(".")[0]
        _record_test_alias(
            aliases, bound_name,
            _skill_module_key(skill_dir, bound_name, key_map) or imported_key)
def _bind_from_import(node: ast.ImportFrom, skill_dir: str, chain,
                      aliases: dict, keys: set, call_aliases: dict,
                      key_map=None) -> None:
    mod = _importfrom_dotted(node, chain)
    mod_key = _skill_module_key(skill_dir, mod, key_map)
    for alias in node.names:
        if alias.name == "*":
            continue
        sub_key = (_skill_module_key(skill_dir, f"{mod}.{alias.name}", key_map)
                   if mod else None)
        key = sub_key or mod_key
        if key is None:
            continue
        keys.add(key)
        binding = alias.asname or alias.name
        _record_test_alias(call_aliases, binding, key)
        if alias.asname or sub_key is not None:
            _record_test_alias(aliases, binding, key)
def _dunder_fromlist_state(node: ast.Call) -> bool | None:
    has_starred_args = any(type(arg) is ast.Starred for arg in node.args[1:])
    value = (node.args[3]
             if len(node.args) >= 4 and not has_starred_args else None)
    if value is None:
        value = next((kw.value for kw in node.keywords
                      if kw.arg == "fromlist"), None)
    if value is None:
        if has_starred_args or any(kw.arg is None for kw in node.keywords):
            return None
        return False
    if type(value) in (ast.List, ast.Tuple, ast.Set):
        if any(type(elt) is ast.Starred for elt in value.elts):
            return None
        return bool(value.elts)
    if type(value) is ast.Dict:
        if any(key is None for key in value.keys):
            return None
        return bool(value.keys)
    if type(value) is ast.Constant:
        return bool(value.value)
    return None
def _dynamic_import_keys(node, skill_dir: str, key_map=None,
                         dynamic_funcs=None) -> set:
    module_name = _dynamic_module_name(node, dynamic_funcs)
    if module_name is None:
        return set()
    call_name = _dynamic_call_name(node, dynamic_funcs)
    module_keys = _alias_keys(
        _skill_module_key(skill_dir, module_name, key_map))
    if call_name != "__import__" or "." not in module_name:
        return module_keys
    fromlist_state = _dunder_fromlist_state(node)
    if fromlist_state is True:
        return module_keys
    top_keys = _alias_keys(_skill_module_key(
        skill_dir, module_name.split(".", 1)[0], key_map))
    if fromlist_state is False:
        return top_keys or module_keys
    return module_keys | top_keys
def _dynamic_import_keys_in(value, skill_dir: str, key_map=None,
                            dynamic_funcs=None) -> set:
    nodes = value.elts if type(value) in (ast.Tuple, ast.List) else (value,)
    keys = set()
    for node in nodes:
        keys.update(_dynamic_import_keys(
            node, skill_dir=skill_dir, key_map=key_map,
            dynamic_funcs=dynamic_funcs))
    return keys
def _bind_dynamic_target(target, value, skill_dir: str, aliases: dict,
                         keys: set, key_map=None, dynamic_funcs=None) -> None:
    value_keys = _dynamic_import_keys_in(
        value, skill_dir, key_map, dynamic_funcs=dynamic_funcs)
    nodes = value.elts if type(value) in (ast.Tuple, ast.List) else (value,)
    for node in nodes:
        dotted = _dotted_expr(node, dynamic_funcs)
        if dotted:
            value_keys.update(_test_binding_keys(
                dotted, aliases, skill_dir, key_map))
    keys.update(value_keys)
    if type(target) is ast.Name:
        aliases.setdefault(target.id, set()).update(value_keys)
        return
    if (type(target) in (ast.Tuple, ast.List)
            and type(value) in (ast.Tuple, ast.List)):
        for sub_target, sub_value in zip(target.elts, value.elts):
            _bind_dynamic_target(
                sub_target, sub_value, skill_dir, aliases, keys, key_map,
                dynamic_funcs=dynamic_funcs)
def _bind_dynamic_import_assignment(node, skill_dir: str, aliases: dict,
                                    keys: set, key_map=None,
                                    dynamic_funcs=None) -> None:
    targets = getattr(node, "targets", None) or [node.target]
    for target in targets:
        _bind_dynamic_target(
            target, node.value, skill_dir, aliases, keys, key_map,
            dynamic_funcs=dynamic_funcs)
def _collect_test_imports(tree: ast.AST, skill_dir: str, chain,
                          key_map=None) -> tuple[dict, set, dict, dict]:
    aliases: dict[str, set[str]] = {}
    call_aliases: dict[str, set[str]] = {}
    dynamic_funcs = _dynamic_import_aliases(tree)
    keys: set = set()
    for node in walk_nodes(tree):
        if type(node) is ast.Import:
            _bind_plain_import(node, skill_dir, aliases, keys, key_map)
        elif type(node) is ast.ImportFrom:
            _bind_from_import(
                node, skill_dir, chain, aliases, keys, call_aliases, key_map)
        elif type(node) in (ast.Assign, ast.AnnAssign, ast.NamedExpr):
            _bind_dynamic_import_assignment(
                node, skill_dir, aliases, keys, key_map,
                dynamic_funcs=dynamic_funcs)
    return aliases, keys, call_aliases, dynamic_funcs
def _absorb_tests_dotted(node: ast.AST, aliases: dict, skill_dir: str,
                         module_attrs: dict, key_map=None,
                         dynamic_funcs=None) -> None:
    dynamic_keys = _dynamic_import_keys(
        node.value, skill_dir, key_map, dynamic_funcs=dynamic_funcs)
    if dynamic_keys:
        for dynamic_key in dynamic_keys:
            module_attrs[dynamic_key].add(node.attr)
        return
    dotted = _dotted_expr(node, dynamic_funcs)
    if not dotted or "." not in dotted:
        return
    owner, _, attr = dotted.rpartition(".")
    for key in _test_binding_keys(owner, aliases, skill_dir, key_map):
        module_attrs[key].add(attr)
def _absorb_tests_getattr(node: ast.Call, aliases: dict, skill_dir: str,
                          module_attrs: dict, key_map=None,
                          dynamic_funcs=None) -> bool:
    if _call_symbol(node) not in _GETATTR_FUNCS:
        return False
    if len(node.args) < 2:
        return False
    name_arg = node.args[1]
    if type(name_arg) is not ast.Constant or type(name_arg.value) is not str:
        return False
    dynamic_keys = _dynamic_import_keys(
        node.args[0], skill_dir, key_map, dynamic_funcs=dynamic_funcs)
    if dynamic_keys:
        for dynamic_key in dynamic_keys:
            module_attrs[dynamic_key].add(name_arg.value)
        return True
    owner = _dotted_expr(node.args[0], dynamic_funcs)
    if owner is None:
        return False
    for key in _test_binding_keys(owner, aliases, skill_dir, key_map):
        module_attrs[key].add(name_arg.value)
    return True
def _dynamic_attr_targets_module(node: ast.Call, aliases: dict,
                                 skill_dir: str, key_map=None,
                                 dynamic_funcs=None) -> bool:
    if _call_symbol(node) not in _GETATTR_FUNCS:
        return False
    if len(node.args) < 2:
        return False
    name_arg = node.args[1]
    if type(name_arg) is ast.Constant and type(name_arg.value) is str:
        return False
    owner_value = node.args[0]
    if _dynamic_import_keys(
            owner_value, skill_dir, key_map, dynamic_funcs=dynamic_funcs):
        return True
    owner = _dotted_expr(owner_value, dynamic_funcs)
    return bool(owner and _test_binding_keys(
        owner, aliases, skill_dir, key_map))
def _record_unresolved_dynamic_consumption(node: ast.Call, rel: str,
                                           ev: dict, aliases: dict,
                                           skill_dir: str, key_map,
                                           dynamic_funcs=None) -> None:
    if (_dynamic_call_name(node, dynamic_funcs) in _DYNAMIC_IMPORT_FUNCS
            and _dynamic_module_name(node, dynamic_funcs) is None):
        ev["unresolved_dynamic"].add(rel)
        return
    if _dynamic_attr_targets_module(
            node, aliases, skill_dir, key_map, dynamic_funcs=dynamic_funcs):
        ev["unresolved_dynamic"].add(rel)
def _absorb_tests_node(node: ast.AST, rel: str, chain, ev: dict,
                       aliases: dict | None = None, keys=frozenset(),
                       skill_dir: str = _DEFAULT_SKILL_DIR, key_map=None,
                       call_aliases: dict | None = None,
                       dynamic_funcs: dict | None = None) -> None:
    tn = type(node)
    aliases = aliases or {}
    call_aliases = call_aliases or {}
    module_attrs = ev["module_attrs"]
    module_calls = ev["module_calls"]
    if tn is ast.Call:
        _record_unresolved_dynamic_consumption(
            node, rel, ev, aliases, skill_dir, key_map,
            dynamic_funcs=dynamic_funcs)
        _absorb_tests_call(node, rel, ev["call_refs"])
        if _absorb_tests_getattr(
                node, aliases, skill_dir, module_attrs, key_map,
                dynamic_funcs=dynamic_funcs):
            return
        if type(node.func) is ast.Name:
            bound = call_aliases.get(node.func.id)
            if bound:
                for bound_key in _alias_keys(bound):
                    module_calls[bound_key].add(node.func.id)
            else:
                for key in keys:
                    module_calls[key].add(node.func.id)
    elif tn is ast.Attribute:
        _absorb_tests_dotted(
            node, aliases, skill_dir, module_attrs, key_map,
            dynamic_funcs=dynamic_funcs)
    elif tn is ast.Constant and type(node.value) is str:
        _absorb_tests_constant(node.value, ev, aliases, keys, skill_dir,
                               key_map)
    elif tn is ast.ImportFrom:
        _absorb_tests_importfrom(
            node, chain, ev["stars"], ev["reexported"], skill_dir, key_map)
def _absorb_tests_constant(value: str, ev: dict, aliases: dict, keys,
                           skill_dir: str, key_map=None) -> None:
    toks = TOKEN_RE.findall(value)
    if toks:
        for key in keys:
            ev["module_strs"][key].update(toks)
    for seg in _DOTTED_SEGMENT_RE.split(value):
        if "." not in seg:
            continue
        owner, _, attr = seg.rpartition(".")
        for key in _test_binding_keys(owner, aliases, skill_dir, key_map):
            ev["module_attrs"][key].add(attr)
def _absorb_tests_call(node, rel: str, call_refs: dict) -> None:
    sym = _call_symbol(node)
    if sym is None:
        return
    call_refs[sym][0] += 1
    call_refs[sym][1].add(rel)
def _absorb_tests_file(path: str, rel: str, ev: dict, skill_dir: str,
                      cache: Any, key_map=None) -> bool:
    parsed = _read_parse_source(path, cache, "tests_evidence")
    if parsed is None:
        return False
    _chain = _pkg_chain_of(skill_dir, path)
    tree = parsed[1]
    _aliases, _keys, _call_aliases, _dynamic_funcs = _collect_test_imports(
        tree, skill_dir, _chain, key_map)
    for node in walk_nodes(tree):
        _absorb_tests_node(
            node, rel, _chain, ev, aliases=_aliases, keys=_keys,
            skill_dir=skill_dir, key_map=key_map, call_aliases=_call_aliases,
            dynamic_funcs=_dynamic_funcs)
    return True
def build_tests_evidence(skill_dir: str, cache=None) -> dict:
    call_refs = _new_call_ref_graph()
    stars: set = set()
    reexported = collections.defaultdict(set)
    module_attrs: dict[str, set] = collections.defaultdict(set)
    module_strs: dict[str, set] = collections.defaultdict(set)
    module_calls: dict[str, set] = collections.defaultdict(set)
    ev = {"call_refs": call_refs, "stars": stars, "reexported": reexported,
          "module_attrs": module_attrs, "module_strs": module_strs,
          "module_calls": module_calls, "unresolved_dynamic": set()}
    key_map = _module_key_lookup(skill_dir)
    scan_errors = []
    for p in iter_py_files(skill_dir, include_tests=True):
        rel = os.path.relpath(p, skill_dir).replace("\\", "/")
        if (is_test_file_path(rel)
                and not _absorb_tests_file(
                    p, rel, ev, skill_dir, cache, key_map)):
            scan_errors.append(rel)
    unresolved = sorted(ev["unresolved_dynamic"])
    if unresolved:
        logger.warning(
            "[F6] 测试动态消费无法静态解析，删除判定 fail-closed: %s",
            unresolved)
        scan_errors.extend(
            f"{rel}:unresolved_dynamic_consumption" for rel in unresolved)
    return {"call_refs": call_refs, "star_mods": stars,
            "reexported": reexported,
            "module_attrs": module_attrs, "module_strs": module_strs,
            "module_calls": module_calls,
            "scan_complete": not scan_errors, "scan_errors": scan_errors}
def _module_keys_of(module: str, skill_dir: str) -> set:
    keys = {module, module.rsplit("/", 1)[-1]}
    if skill_dir:
        keys |= _init_key_variants(module, skill_dir)
    return {key for key in keys if key}
def _module_scoped_consumed(tests_ev: dict, module: str, binding: str,
                            skill_dir: str) -> bool:
    for chan in ("reexported", "module_attrs", "module_strs", "module_calls"):
        bucket = tests_ev.get(chan) or {}
        for key in _module_keys_of(module, skill_dir):
            if binding in (bucket.get(key) or ()):
                return True
    return False
def tests_consumes_symbol(tests_ev: dict, module: str, symbol: str,
                           skill_dir: str = _DEFAULT_SKILL_DIR) -> bool:
    binding = symbol.split(".", maxsplit=1)[0]
    if not binding:
        return False
    if not tests_ev.get("scan_complete", True):
        return True
    if _module_scoped_consumed(tests_ev, module, binding, skill_dir):
        return True
    return _star_consumed(tests_ev, module, binding, skill_dir)
def _star_consumed(tests_ev: dict, module: str, binding: str,
                   skill_dir: str) -> bool:
    if binding.startswith("_"):
        return False
    return bool((tests_ev.get("star_mods") or set())
                & _module_keys_of(module, skill_dir))
def call_graph_from_ctx(ctx: dict, skill_dir: str,
                         tests_evidence: dict | None = None,
                         cache: Any = None) -> dict:
    refs = _new_call_ref_graph()
    _merge_ctx_calls(refs, ctx, skill_dir)
    te = tests_evidence if tests_evidence is not None else build_tests_evidence(
        skill_dir, cache=cache)
    for sym, (cnt, files) in (te.get("call_refs") or {}).items():
        refs[sym][0] += cnt
        refs[sym][1].update(files)
    return refs
def _merge_ctx_calls(refs: dict, ctx: dict, skill_dir: str) -> None:
    for fkey, calls in (ctx.get("call_counts") or {}).items():
        path = ctx_file_path(ctx, fkey)
        if path is None:
            continue
        rel = os.path.relpath(path, skill_dir).replace("\\", "/")
        for sym, cnt in calls.items():
            refs[sym][0] += cnt
            refs[sym][1].add(rel)
def build_plan_with_evidence(skill_dir: str, cache: Any,
                                    include_call_graph: bool = False):
    ctx = build_scan_context(skill_dir, cache=cache, include_tests=False)
    tests_evidence = build_tests_evidence(skill_dir, cache=cache)
    reexport_map = reexport_map_from_ctx(ctx, skill_dir, cache=cache,
                                          tests_evidence=tests_evidence)
    plan = build_clean_plan(skill_dir, cache=cache, _ctx=ctx,
                            reexport_map=reexport_map,
                            tests_evidence=tests_evidence)
    call_graph = (call_graph_from_ctx(ctx, skill_dir,
                                       tests_evidence=tests_evidence)
                  if include_call_graph else None)
    return plan, tests_evidence, reexport_map, call_graph
_PARSE_ERRORS: tuple[type[BaseException], ...] = PARSE_DEGRADE_EXC
_SOURCE_READ_ERRORS = _PARSE_ERRORS + (OSError,)
def _collect_topdef_ranges(tree: ast.Module, names: set) -> dict:
    targets = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) \
                and node.name in names:
            start = node.lineno
            if getattr(node, "decorator_list", None):
                start = node.decorator_list[0].lineno
            targets[(node.name, node.lineno)] = (start, node.end_lineno)
    return targets
def _delete_topdef_ranges(lines: list, items: list, targets: dict) -> list:
    resolved = [targets.get((name, lineno)) for name, lineno in items]
    first_idx: dict = {}
    for i, rng in enumerate(resolved):
        if rng is not None and rng not in first_idx:
            first_idx[rng] = i
    for rng in sorted(first_idx, key=lambda r: -r[0]):
        del lines[rng[0] - 1:rng[1]]
    return [rng is not None and first_idx.get(rng) == i
            for i, rng in enumerate(resolved)]
def _group_cleaning_items(plan: dict) -> dict:
    by_module: dict[str, list] = {}
    for module, _kind, name, lineno in plan.get("functions", []):
        by_module.setdefault(module, []).append(("func", name, lineno))
    for module, syms in plan.get("imports", {}).items():
        for lineno, full in syms:
            by_module.setdefault(module, []).append(("import", full, lineno))
    return by_module
def _read_parse_or_failed(p: str, module: str, label: str):
    if not os.path.exists(p):
        logger.warning("[deadcode] %s.py 不存在，%s", module, label)
        return None
    parsed = _read_parse_source(p, None, stage=f"deadcode:{label}")
    if parsed is None:
        logger.warning(
            "[deadcode] %s.py 读取/解析失败（源码不可读或语法异常），%s",
            module, label)
        return None
    return parsed
def _delete_function_ranges(tree: ast.AST, lines: list,
                            func_items: list) -> list:
    targets = _collect_topdef_ranges(tree, {it[1] for it in func_items})
    return _delete_topdef_ranges(
        lines, [(it[1], it[2]) for it in func_items], targets)
def _import_alias_key(node: ast.AST, alias: ast.alias) -> tuple[int, str]:
    return (getattr(alias, "lineno", None) or node.lineno,
            alias.asname or alias.name)
def _import_alias_is_target(node: ast.AST, alias: ast.alias,
                            target_refs: set) -> bool:
    return _import_alias_key(node, alias) in target_refs
def _prune_imports_in_lines(lines: list, tree: ast.AST,
                            target_refs: set) -> list:
    nodes = _collect_target_import_nodes(tree, target_refs)
    pass_required = _pass_required_import_ids(tree, target_refs)
    nodes.sort(
        key=lambda n: (n.lineno, getattr(n, "col_offset", 0)), reverse=True)
    return [_prune_import_aliases(lines, n, target_refs, id(n) in pass_required)
            for n in nodes]
def _import_fully_removed(node: ast.AST, target_refs: set) -> bool:
    return (isinstance(node, (ast.Import, ast.ImportFrom))
            and all(_import_alias_is_target(node, a, target_refs)
                    for a in node.names))
def _pass_required_import_ids(tree: ast.AST, target_refs: set) -> set[int]:
    required: set[int] = set()
    for parent in walk_nodes(tree):
        if isinstance(parent, ast.Module):
            continue
        for field in ("body", "orelse", "finalbody"):
            body = getattr(parent, field, None)
            if (isinstance(body, list) and body
                    and all(_import_fully_removed(node, target_refs)
                            for node in body)):
                required.add(id(body[0]))
    return required
def _retarget_imports_after_function_deletions(target_refs: set,
                                                 tree: ast.AST,
                                                 func_items: list) -> set:
    if not func_items:
        return set(target_refs)
    targets = _collect_topdef_ranges(tree, {it[1] for it in func_items})
    deleted_spans = set()
    for _kind, name, lineno in func_items:
        span = targets.get((name, lineno))
        if span is not None:
            deleted_spans.add(span)
    adjusted = set()
    for lineno, full in target_refs:
        if any(start <= lineno <= end for start, end in deleted_spans):
            continue
        shift = sum(end - start + 1 for start, end in deleted_spans
                    if end < lineno)
        adjusted.add((lineno - shift, full))
    return adjusted
def _apply_cleaning_to_lines(src: str, func_items: list,
                              import_syms: set, module: str,
                              tree: ast.AST) -> str | None:
    target_refs = {(lineno, full) for full, lineno in import_syms}
    unresolved_imports = target_refs - _handled_import_bindings(
        tree, target_refs)
    if unresolved_imports:
        logger.warning(
            "[deadcode] %s.py import 候选未全部定位(%s)，跳过 fixed_source 生成",
            module, ", ".join(f"{full}@{lineno}"
                              for lineno, full in sorted(unresolved_imports)))
        return None
    lines = src.split("\n")
    deleted = _delete_function_ranges(tree, lines, func_items)
    if not all(deleted):
        logger.warning(
            "[deadcode] %s.py 死代码候选未全部定位，跳过 fixed_source 生成",
            module)
        return None
    try:
        tree2 = ast.parse("\n".join(lines))
    except _PARSE_ERRORS:
        logger.warning("[deadcode] %s.py 函数删除后语法异常，跳过 fixed_source 生成", module)
        return None
    adjusted_refs = _retarget_imports_after_function_deletions(
        target_refs, tree, func_items)
    _prune_imports_in_lines(lines, tree2, adjusted_refs)
    new_src = "\n".join(lines)
    try:
        compile(new_src, "<string>", "exec")
    except _PARSE_ERRORS as e:
        logger.warning("[deadcode] %s.py fixed_source 语法错误，跳过: %s", module, e)
        return None
    return new_src
def _run_module_edit(skill_dir: str, module: str, fallback: list,
                     label: str, mutate,
                     path_map: dict[str, str] | None = None) -> list:
    parsed = _read_parse_or_failed(
        module_path(skill_dir, module, path_map), module,
        f"{label}跳过（候选保留为未生效）")
    if parsed is None:
        return fallback
    src, tree = parsed
    lines = src.split("\n")
    module_results = mutate(lines, tree)
    try:
        compile("\n".join(lines), '<string>', 'exec')
    except _PARSE_ERRORS as e:
        logger.warning("[deadcode] %s.py %s后语法错误: %s，已跳过",
                       module, label, e)
        return fallback
    return module_results
def _clean_module_functions(skill_dir: str, module: str,
                            items: list,
                            path_map: dict[str, str] | None = None) -> list:
    fallback = [(module, it[1], False) for it in items]
    def _mutate(lines: list, tree: ast.AST) -> list:
        deleted_flags = _delete_function_ranges(tree, lines, items)
        return [(module, name, ok)
                for (_kind, name, _lineno), ok in zip(
                    items, deleted_flags, strict=True)]
    return _run_module_edit(
        skill_dir, module, fallback, "清理", _mutate, path_map)
def clean_dead_functions(skill_dir: str, plan: dict,
                         path_map: dict[str, str] | None = None) -> list:
    results = []
    by_module = collections.defaultdict(list)
    for module, kind, name, lineno in plan.get("functions", []):
        by_module[module].append((kind, name, lineno))
    path_map = _resolve_path_map(skill_dir, path_map)
    for module, items in by_module.items():
        results.extend(_clean_module_functions(
            skill_dir, module, items, path_map))
    return results
def _utf8_slice(text: str, start: int, stop: int | None = None) -> str | None:
    try:
        data = text.encode("utf-8")
        if stop is None:
            stop = len(data)
        if not 0 <= start <= stop <= len(data):
            return None
        return data[start:stop].decode("utf-8")
    except (UnicodeEncodeError, UnicodeDecodeError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_utf8_slice:UnicodeEncodeError')
        return None
def _alias_repr(a: ast.alias) -> str:
    return a.name + (f" as {a.asname}" if a.asname else "")
def _prune_import_aliases(lines: list, n: ast.AST, target_refs: set,
                          require_pass: bool):
    if not isinstance(n, (ast.Import, ast.ImportFrom)):
        return None
    start, end = n.lineno, getattr(n, "end_lineno", n.lineno)
    _bounds = _line_bounds(lines, n, start, end)
    used = [a for a in n.names
            if not _import_alias_is_target(n, a, target_refs)]
    if not used:
        _desc = _desc_or_removed(n, None)
        _del_all_aliases(lines, start, end, _bounds, require_pass)
        return ("del", _desc)
    stmt = _rewrite_remaining_stmt(n, used)
    removed = _desc_or_removed(n, {id(a) for a in used})
    _apply_rewrite(lines, start, end, _bounds, stmt)
    return ("rewrite", removed)
def _line_bounds(lines: list, n: ast.AST, start: int,
                 end: int) -> tuple[str, str] | None:
    col_s = getattr(n, "col_offset", None)
    col_e = getattr(n, "end_col_offset", None)
    if col_s is None or col_e is None:
        return None
    _line = lines[start - 1] if 0 < start <= len(lines) else ""
    _end_line = lines[end - 1] if 0 < end <= len(lines) else ""
    prefix = _utf8_slice(_line, 0, col_s)
    suffix = _utf8_slice(_end_line, col_e)
    if prefix is None or suffix is None:
        return None
    return prefix, suffix
def _apply_rewrite(lines: list, start: int, end: int,
                   bounds: tuple[str, str] | None, stmt: str) -> None:
    if bounds is not None:
        lines[start - 1:end] = [bounds[0] + stmt + bounds[1]]
        return
    _line = lines[start - 1] if 0 < start <= len(lines) else ""
    indent = _line[:len(_line) - len(_line.lstrip())]
    lines[start - 1:end] = [indent + stmt]
def _desc_or_removed(n: ast.AST, used_ids: set | None) -> str:
    if used_ids is None:
        return ", ".join(_alias_repr(a) for a in n.names)
    return ", ".join(_alias_repr(a) for a in n.names
                      if id(a) not in used_ids)
def _del_all_aliases(lines: list, start: int, end: int,
                     bounds: tuple[str, str] | None,
                     require_pass: bool) -> None:
    if bounds is not None and _splice_delete_segment(
            lines, start, end, *bounds, require_pass):
        return
    del lines[start - 1:end]
def _strip_semicolon_sides(prefix: str, suffix: str) -> tuple[str, str]:
    _s = suffix.lstrip()
    _s_had_semi = _s.startswith(";")
    if _s_had_semi:
        suffix = _s[1:].lstrip()
    _p = prefix.rstrip()
    if _p.endswith(";"):
        prefix = prefix if _s_had_semi else _p[:-1]
    return prefix, suffix
def _splice_delete_segment(lines: list, start: int, end: int,
                           prefix: str, suffix: str,
                           require_pass: bool) -> bool:
    original_prefix = prefix
    prefix, suffix = _strip_semicolon_sides(prefix, suffix)
    _new_line = prefix + suffix
    _stripped = _new_line.strip()
    _suffix = suffix.lstrip()
    if (require_pass and prefix.rstrip().endswith(":")
            and (not _suffix or _suffix.startswith("#"))):
        lines[start - 1:end] = [f"{prefix.rstrip()} pass{suffix}"]
        return True
    if _stripped and not _stripped.startswith("#"):
        lines[start - 1:end] = [_new_line]
        return True
    if not require_pass:
        return False
    replacement = (f"{prefix} pass{suffix}" if prefix.strip()
                   else f"{original_prefix}pass{suffix}")
    lines[start - 1:end] = [replacement]
    return True
def _rewrite_remaining_stmt(n: ast.AST, used: list) -> str:
    if isinstance(n, ast.ImportFrom):
        lvl = "." * n.level
        fp = (f"from {lvl}{n.module} import " if n.module
              else f"from {lvl} import ")
        return fp + ", ".join(_alias_repr(a) for a in used)
    return "import " + ", ".join(_alias_repr(a) for a in used)
def _collect_target_import_nodes(tree: ast.AST, target_refs: set) -> list:
    nodes = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        for alias in node.names:
            if _import_alias_is_target(node, alias, target_refs):
                nodes.append(node)
                break
    return nodes
def _handled_import_bindings(tree: ast.AST, target_refs: set) -> set:
    return {_import_alias_key(node, alias) for node in walk_nodes(tree)
            if isinstance(node, (ast.Import, ast.ImportFrom))
            for alias in node.names
            if _import_alias_is_target(node, alias, target_refs)}
def _clean_module_imports(skill_dir: str, module: str, syms: list,
                          path_map: dict[str, str] | None = None) -> list:
    fallback = [(module, "skipped", full) for _ln, full in syms]
    def _mutate(lines: list, tree: ast.AST) -> list:
        target_refs = {(lineno, full) for lineno, full in syms}
        handled = _handled_import_bindings(tree, target_refs)
        actions = _prune_imports_in_lines(lines, tree, target_refs)
        results = [(module, act[0], act[1]) for act in actions]
        results.extend((module, "skipped", full)
                       for lineno, full in syms if (lineno, full) not in handled)
        return results
    return _run_module_edit(
        skill_dir, module, fallback, "import 清理", _mutate, path_map)
def clean_unused_imports(skill_dir: str, plan: dict,
                         path_map: dict[str, str] | None = None) -> list:
    results = []
    path_map = _resolve_path_map(skill_dir, path_map)
    for module, syms in plan.get("imports", {}).items():
        results.extend(_clean_module_imports(skill_dir, module, syms, path_map))
    return results
def build_fixed_sources(skill_dir: str, plan: dict,
                        path_map: dict[str, str] | None = None) -> dict:
    fixed: dict[str, str] = {}
    by_module = _group_cleaning_items(plan)
    path_map = _resolve_path_map(skill_dir, path_map)
    for module, items in by_module.items():
        p = module_path(skill_dir, module, path_map)
        parsed = _read_parse_or_failed(
            p, module, "跳过 fixed_source 生成")
        if parsed is None:
            continue
        src, tree = parsed
        func_items = []
        import_syms = set()
        for kind, name, lineno in items:
            if kind == "func":
                func_items.append((kind, name, lineno))
            elif kind == "import":
                import_syms.add((name, lineno))
        new_src = _apply_cleaning_to_lines(
            src, func_items, import_syms, module, tree)
        if new_src is None:
            continue
        if new_src != src:
            fixed[module] = new_src if new_src else "\n"
    return fixed
class _VerifyGroup(NamedTuple):
    module_root: str
    import_root: str
    package: str
    paths: list[str]
def _relative_path_under(path: str, root: str) -> str | None:
    try:
        relative = os.path.relpath(path, root)
    except ValueError:
        return None
    if relative == ".." or relative.startswith(".." + os.sep):
        return None
    return relative
def _verify_layout_for_path(skill_dir: str, path: str) -> tuple[str, str, str]:
    source_root = os.path.join(skill_dir, "src")
    if (os.path.isdir(source_root)
            and _relative_path_under(path, source_root) is not None):
        return source_root, source_root, ""
    root_name = os.path.basename(skill_dir)
    if (os.path.isfile(os.path.join(skill_dir, "__init__.py"))
            and root_name.isidentifier()):
        return skill_dir, os.path.dirname(skill_dir), root_name
    return skill_dir, skill_dir, ""
def _verify_import_groups(skill_dir: str, core: list[str]) -> list[_VerifyGroup]:
    grouped: dict[tuple[str, str, str], list[str]] = {}
    for path in core:
        layout = _verify_layout_for_path(skill_dir, path)
        grouped.setdefault(layout, []).append(path)
    return [_VerifyGroup(*layout, paths) for layout, paths in grouped.items()]
def _import_verify_group(group: _VerifyGroup,
                         failed: list) -> tuple[int, int, list, str]:
    path_added = group.import_root not in sys.path
    if path_added:
        sys.path.insert(0, group.import_root)
    try:
        return _import_all_modules(
            group.paths, group.module_root, group.package, failed)
    finally:
        if path_added:
            sys.path.remove(group.import_root)
def _sys_modules_snapshot() -> dict:
    return dict(sys.modules)
def _restore_sys_modules(snapshot: dict) -> None:
    for name in [n for n in sys.modules if n not in snapshot]:
        sys.modules.pop(name, None)
    for name, module in snapshot.items():
        if sys.modules.get(name) is not module:
            sys.modules[name] = module
def verify_clean(skill_dir: str, cache: Any = None) -> dict:
    skill_dir = os.path.abspath(os.path.normpath(skill_dir))
    core = list(iter_py_files(skill_dir, include_tests=False))
    ok, total, failed = _compile_all_modules(core, cache)
    imp_ok = imp_total = 0
    imported: list[str] = []
    skipped_channels: set[str] = set()
    modules_before = _sys_modules_snapshot()
    try:
        for group in _verify_import_groups(skill_dir, core):
            group_ok, group_total, group_imported, group_skipped = (
                _import_verify_group(group, failed))
            imp_ok += group_ok
            imp_total += group_total
            imported.extend(group_imported)
            if group_skipped:
                skipped_channels.add(group_skipped)
    finally:
        _restore_sys_modules(modules_before)
    return {"compile": (ok, total), "import": (imp_ok, imp_total),
            "failed": failed, "modules": imported,
            "import_skipped": ",".join(sorted(skipped_channels))}
def _compile_all_modules(core: list, cache: Any) -> tuple[int, int, list]:
    ok = total = 0
    failed: list = []
    for p in core:
        total += 1
        try:
            source = _read_scan_source(p, cache, stage="verify_clean")
            if source is None:
                failed.append((os.path.basename(p), "compile: source unreadable"))
                continue
            compile(source, p, "exec")
            ok += 1
        except _SOURCE_READ_ERRORS as e:
            log_swallowed(__name__, e, context='verify_clean:SyntaxError')
            failed.append((os.path.basename(p), f"compile: {e}"))
    return ok, total, failed
def _purge_stale_package_modules(pkg: str) -> None:
    if not pkg or pkg == __package__:
        return
    prefix = pkg + "."
    for name in [n for n in list(sys.modules)
                 if n == pkg or n.startswith(prefix)]:
        sys.modules.pop(name, None)
def _purge_unprefixed_group_cache(core: list, module_root: str,
                                  current_top_package: str) -> None:
    top_names: set[str] = set()
    for path in core:
        relative = _relative_path_under(path, module_root)
        if not relative:
            continue
        top = relative.replace("\\", "/").split("/", 1)[0]
        top = top.removesuffix(".py")
        if top and top != current_top_package:
            top_names.add(top)
    for top in sorted(top_names):
        _purge_stale_package_modules(top)
def _import_all_modules(core: list, module_root: str, pkg: str,
                        failed: list) -> tuple[int, int, list, str]:
    imp_ok = imp_total = 0
    imported: list[str] = []
    import_skipped = ""
    current_top_package = (__package__ or "").split(".")[0]
    if pkg and pkg == __package__:
        logger.warning(
            "[deadcode] 目标包 %s 与当前运行包同名：同进程 import 验证只会"
            "命中旧模块对象，该通道跳过（compile 通道不受影响，如需"
            "import 证据请在新进程执行）", pkg)
        return 0, 0, [], "self_package"
    _purge_stale_package_modules(pkg)
    if not pkg:
        _purge_unprefixed_group_cache(core, module_root, current_top_package)
    for p in core:
        try:
            rel = os.path.relpath(p, module_root).replace("\\", "/")
            if rel == ".." or rel.startswith("../"):
                continue
        except ValueError:
            continue
        if rel == "__init__.py":
            if not pkg:
                continue
            modname = qualified = pkg
        else:
            suffix_len = (len("/__init__.py")
                          if rel.endswith("/__init__.py") else len(".py"))
            modname = rel[:-suffix_len].replace("/", ".")
            qualified = f"{pkg}.{modname}" if pkg else modname
        if (current_top_package
                and qualified.split(".")[0] == current_top_package):
            import_skipped = "self_package"
            continue
        imp_total += 1
        try:
            if not pkg:
                sys.modules.pop(qualified, None)
            importlib.import_module(qualified)  # lazy-by-design — 插件/注册表按名装载，静态导入会破坏插件边界
            imp_ok += 1
            imported.append(modname)
        except Exception as e:  # noqa: BLE001
            log_swallowed(__name__, e, context='verify_clean:Exc')
            failed.append((modname, f"import: {str(e)[:60]}"))
    return imp_ok, imp_total, imported, import_skipped
def _collect_unapplied_failures(func_results: list | None,
                                import_results: list | None) -> list:
    failed: list = []
    for module, name, deleted in func_results or ():
        if not deleted:
            failed.append((module, f"deadcode: {name} 清理未生效（未定位到定义或删除后语法校验失败）"))
    for module, action, symbol in import_results or ():
        if action == "skipped":
            failed.append((module, f"import 清理未生效: {symbol}（模块缺失或语法校验失败）"))
    return failed
def _verify_fixed_sources(fixed_sources: dict, func_results: list | None = None,
                          import_results: list | None = None) -> dict:
    ok = total = 0
    failed = []
    for module, src in fixed_sources.items():
        total += 1
        try:
            compile(src, f"<{module}:fixed>", "exec")
            ok += 1
        except _PARSE_ERRORS as e:
            log_swallowed(__name__, e, context='_verify_fixed_sources:SyntaxError')
            failed.append((module, f"compile: {e}"))
    failed.extend(_collect_unapplied_failures(func_results, import_results))
    return {"compile": (ok, total), "failed": failed}
def run_deadcode_cleanup(skill_dir: str, dry_run: bool = True,
                         verify: bool = True, use_cross_validate: bool = True,
                         diagnostics_dir: str | None = None, cache: Any = None) -> dict:
    skill_dir = os.path.abspath(skill_dir)
    if not os.path.isdir(skill_dir):
        raise FileNotFoundError(f"技能目录不存在: {skill_dir}")
    cache = _resolve_warmed_cache(skill_dir, cache)
    plan, _tests_ev, _reexport_map, _call_graph = (
        build_plan_with_evidence(skill_dir, cache,
                                        include_call_graph=True))
    logger.info("[deadcode] 计划: %d 个死函数, %d 个模块的未使用 import",
                len(plan["functions"]),
                sum(len(v) for v in plan["imports"].values()))
    cv_summary = (_run_cv_gate(skill_dir, plan, diagnostics_dir, cache,
                               _reexport_map, _call_graph)
                  if use_cross_validate and plan["functions"] else None)
    path_map = module_file_map(skill_dir)
    fr, ir, _fixed_sources, v = _run_cleanup_channels(
        skill_dir, plan, verify, path_map)
    _handoff = enqueue_cleanup_review(skill_dir, plan, _fixed_sources,
                                      path_map)
    _dc_result = {"plan": plan, "cross_validate": cv_summary,
                  "zero_consumers": _handoff["zero_consumers"],
                  "func_results": fr, "import_results": ir, "verify": v,
                  "fixed_sources": _fixed_sources,
                  "dry_run": dry_run, "ai_review": _handoff["ai_review"]}
    emit_step_html("deadcode_cleanup", skill_dir,
                   {**_dc_result, "_stage_hint": "diag:F"})
    return _dc_result
def _resolve_warmed_cache(skill_dir: str, cache: Any) -> Any:
    if cache is None:
        return get_warmed_cache(skill_dir)
    require_warmed(cache, "死代码清理 run_deadcode_cleanup")
    return cache
def _run_cleanup_channels(skill_dir: str, plan: dict, verify: bool,
                          path_map: dict[str, str]) -> tuple[list, list, dict, dict | None]:
    fr = clean_dead_functions(skill_dir, plan, path_map)
    ir = clean_unused_imports(skill_dir, plan, path_map)
    fixed_sources = _generate_fixed_sources(skill_dir, plan, path_map)
    v = (_verify_fixed_sources(fixed_sources, func_results=fr,
                               import_results=ir)
         if verify else None)
    return fr, ir, fixed_sources, v
def _generate_fixed_sources(skill_dir: str, plan: dict,
                            path_map: dict[str, str] | None = None) -> dict:
    try:
        return build_fixed_sources(skill_dir, plan, path_map)
    except Exception as _e:
        logger.warning("[deadcode] fixed_source 生成失败(降级空集): %s", _e,
                       exc_info=True)
        return {}
def _split_cv_verdicts(cv: list, orig: dict) -> tuple[list, list, list]:
    high, review, torn = [], [], []
    returned = set()
    for (module, name, lineno, conf, evidence) in cv:
        key = (module, name, lineno)
        if key not in orig:
            torn.append(key)
            continue
        returned.add(key)
        if conf == "HIGH":
            high.append(orig[key])
        else:
            review.append((module, name, lineno, conf, evidence))
    for module, name, lineno in orig:
        if (module, name, lineno) not in returned:
            review.append((
                module, name, lineno, "ERROR",
                "交叉验证未返回该候选，按 fail-closed 保留并转入复核",
            ))
    return high, review, torn
def _run_cv_gate(skill_dir: str, plan: dict, diagnostics_dir,
                  cache, reexport_map: dict, call_graph: dict) -> dict | None:
    try:
        cv = cross_validate_deadcode(
            skill_dir, candidates=plan["functions"],
            output_dir=diagnostics_dir, cache=cache,
            _shared={"reexport_map": reexport_map,
                     "call_graph": call_graph})
        orig = {(m, n, ln): (m, k, n, ln)
                for (m, k, n, ln) in plan["functions"]}
        high, review, _torn = _split_cv_verdicts(cv, orig)
        if _torn:
            logger.warning(
                "[deadcode] 交叉验证产出 %d 个计划外候选（撕裂形态）"
                "已隔离: %s", len(_torn), _torn[:5])
        plan["functions"] = high
        logger.info(
            "[deadcode] 交叉验证: %d 候选 → %d HIGH(清理) / %d 豁免/复核",
            len(orig), len(high), len(review))
        return {
            "total": len(orig), "cleaned": len(high),
            "exempt_or_review": len(review), "review": review,
        }
    except Exception as _cve:
        original = list(plan["functions"])
        evidence = f"交叉验证不可用: {_cve}"
        review = [
            (module, name, lineno, "ERROR", evidence)
            for module, _kind, name, lineno in original
        ]
        plan["functions"] = []
        logger.warning(
            "[deadcode] 交叉验证异常(死函数清理已阻断，import 通道保留): %s",
            _cve, exc_info=True)
        return {
            "status": "error", "error": str(_cve),
            "total": len(original), "cleaned": 0,
            "exempt_or_review": len(review), "review": review,
        }
def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="死代码检测与安全清理（适用于任意 Python 项目与技能）")
    ap.add_argument("skill_dir", help="技能目录路径")
    ap.add_argument("--apply", action="store_true", help="兼容参数（恒为分析模式不落盘，任何修复由 AI 审核并执行验证）")
    ap.add_argument("--no-verify", action="store_true", help="跳过 compile/import 验证")
    ap.add_argument("--no-cross-validate", action="store_true",
                    help="关闭与诊断引擎的交叉验证（默认开启，仅清理HIGH置信度）")
    ap.add_argument("--diagnostics-dir", default=None,
                    help="诊断报告目录或其 _intermediate 子目录，用于交叉验证增强")
    args = ap.parse_args(argv)
    try:
        result = run_deadcode_cleanup(
            args.skill_dir,
            dry_run=not args.apply,
            verify=not args.no_verify,
            use_cross_validate=not args.no_cross_validate,
            diagnostics_dir=args.diagnostics_dir,
        )
    except (RuntimeError, OSError) as e:
        log_swallowed(__name__, e, context='main:FileNotFoundError')
        print(f"错误: {e}", file=sys.stderr)
        return 2
    print("=== 死代码清理报告（检测即交叉验证）===")
    _print_cv_block(result.get("cross_validate"))
    _print_plan_items(result["plan"])
    _print_verify_block(result["verify"])
    print(f"dry_run: {result['dry_run']}（恒为分析模式不落盘, 任何修复由 AI 审核并执行验证）")
    _log_cli_report_trace(result)
    return 0
def _print_cv_block(cv) -> None:
    if not cv:
        return
    print(f"交叉验证: {cv['total']} 候选 → {cv['cleaned']} HIGH(清理) / "
          f"{cv['exempt_or_review']} 豁免/复核")
    for m, n, _l, c, e in cv["review"]:
        print(f"  [豁免/复核] {m}.{n} ({c}): {e}")
def _print_plan_items(plan: dict) -> None:
    print(f"死函数候选(清理): {len(plan['functions'])}")  # jwsgj:suppress WM-01
    for m, k, n, ln in plan["functions"]:  # jwsgj:suppress WM-01
        print(f"  [{k}] {m}.{n} (行{ln})")
    print(f"未使用import候选: {sum(len(v) for v in plan['imports'].values())}")  # jwsgj:suppress WM-01
    for m, syms in plan["imports"].items():  # jwsgj:suppress WM-01
        for ln, full in syms:
            print(f"  [{m}] 行{ln}: {full}")
def _print_verify_block(v) -> None:
    if not v:
        return
    print(f"\n验证(清理方案编译): {v['compile'][0]}/{v['compile'][1]} 模块通过")
    if v.get("import_skipped"):
        print(f"  import 通道跳过: {v['import_skipped']}"
              f"（同进程自验证不可信，需在新进程复核）")
    for name, err in v["failed"]:
        print(f"  失败: {name}: {err}")
def _log_cli_report_trace(result: dict) -> None:
    _cv = result.get("cross_validate") or {}
    _v = result.get("verify") or {}
    logger.info(
        "[deadcode] CLI 清理报告留痕: 死函数候选=%d, import候选=%d, "
        "交叉验证=%s, 编译验证=%s, dry_run=%s",
        len(result["plan"]["functions"]),  # jwsgj:suppress WM-01
        sum(len(v) for v in result["plan"]["imports"].values()),  # jwsgj:suppress WM-01
        (f"{_cv.get('cleaned', 0)}HIGH/{_cv.get('exempt_or_review', 0)}豁免复核"
         f"/{_cv.get('total', 0)}总") if _cv else "off",
        (f"{_v['compile'][0]}/{_v['compile'][1]}通过" if _v else "off"),
        result["dry_run"],
    )
def _g6_function_findings(plan: dict, tests_ev: Any,
                          skill_dir: str) -> list[dict]:
    findings: list[dict] = []
    for module, kind, name, lineno in plan["functions"]:
        if tests_consumes_symbol(tests_ev, module, name, skill_dir=skill_dir):
            continue
        findings.append({
            "rule_id": "DEAD-FUNC",
            "severity": _DEADCODE_SEVERITY,
            "file": module,
            "line": lineno,
            "message": f"死{kind}: {name}",
            "source": "G6",
        })
    return findings
def _g6_import_findings(plan: dict) -> list[dict]:
    findings: list[dict] = []
    for module, syms in plan["imports"].items():
        for lineno, full_symbol in syms:
            findings.append({
                "rule_id": "UNUSED-IMPORT",
                "severity": _DEADCODE_SEVERITY,
                "file": module,
                "line": lineno,
                "message": f"未使用导入: {full_symbol}",
                "source": "G6",
            })
    return findings
def run_safeops_gate(skill_dir: str, cache=None) -> dict:
    from jwsgj.build_safe_orchestration import (
        safe_delivery_check,  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    )
    require_warmed(cache, "G2 SafeOps 守卫")
    watch = Stopwatch()
    try:
        result = safe_delivery_check(target_path=skill_dir, cache=cache)
        blocked = result.get('blocked', False)
        failed = result.get('failed', 0)
        passed = result.get('passed', 0)
        total = result.get('total', 0)
        status = 'fail' if blocked else ('warn' if failed else 'pass')
        result_dict = {
            'status': status, 'blocked': blocked,
            'passed': passed, 'failed': failed,
            'total': total, 'issues': result.get('issues', []),
            'report': result.get('report', ''),
            'summary': f"SafeOps守卫: {passed}/{total} 守卫通过",
        }
        perf_trace('g2_safeops', round(watch.elapsed_ms(), 1))
        return result_dict
    except Exception as e:
        logger.warning('[G2] SafeOps 守卫执行异常，本次交付未经 SafeOps 检查: %s', e, exc_info=True)
        return {'status': 'skip', 'summary': 'SafeOps守卫跳过',
                'error': str(e), 'component_failed': True}
def run_refactor_gate(skill_dir: str, cache: SharedCache | None = None) -> dict:
    from jwsgj.refactor_split_actions import (
        run_refactor_workflow,  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    )
    require_warmed(cache, "G5 重构执行引擎")
    watch = Stopwatch()
    try:
        result = run_refactor_workflow(
            skill_dir, dry_run=True, mode="full", cache=cache)
        violations = result.get("violations", [])
        actions = result.get("actions", [])
        file_analyses = result.get("file_analyses", {})
        n_violations = len(violations)
        n_actions = len(actions)
        n_files = len(file_analyses)
        summary_parts = [f"重构分析: {n_files}个文件"]
        if n_violations > 0:
            summary_parts.append(f"{n_violations}个违规")
        if n_actions > 0:
            summary_parts.append(f"{n_actions}个建议动作")
        perf_trace("g5_refactor", round(watch.elapsed_ms(), 1),
                         files=n_files, violations=n_violations,
                         actions=n_actions)
        status = "warn" if (n_violations > 0 or n_actions > 0) else "pass"
        return {
            "status": status, "findings_count": n_violations + n_actions,
            "ai_action": "AI 审核上述重构建议后，调用 "
                         "run_refactor_workflow(skill_dir, dry_run=False, "
                         "mode='execute') 执行落盘（备份→写盘→语法校验→失败回滚），"
                         "再复跑本方法验证违规归零",
            "summary": ", ".join(summary_parts), "violations": violations,
            "actions": actions, "file_analyses": file_analyses,
            "n_files": n_files, "n_violations": n_violations, "n_actions": n_actions,
        }
    except Exception as e:
        logger.warning("[G5] 重构分析执行异常: %s", e, exc_info=True)
        return {"status": "warn", "summary": f"重构分析异常: {e}",
                "findings_count": 0, "component_failed": True}
@timed_log("g6_code_cleaner")
def run_deadcode_gate(skill_dir: str, cache=None) -> dict:
    require_warmed(cache, "G6 代码清理执行")
    try:
        plan, _tests_ev, _rmap, _ = build_plan_with_evidence(
            skill_dir, cache)
        findings = (_g6_function_findings(plan, _tests_ev, skill_dir)
                    + _g6_import_findings(plan))
        n = len(findings)
        evidence_complete = bool(plan.get("evidence_complete", True))
        evidence_errors = list(plan.get("evidence_errors") or [])
        summary = f"代码清理扫描: {n}个发现"
        if not evidence_complete:
            summary += ", 扫描证据不完整（删除候选已阻断）"
        return {
            "status": "warn" if n or not evidence_complete else "pass",
            "findings_count": n,
            "summary": summary,
            "findings": findings,
            "clean_plan": list(findings),
            "evidence_complete": evidence_complete,
            "evidence_errors": evidence_errors,
            "component_failed": not evidence_complete,
        }
    except Exception as e:
        logger.warning("[G6] 代码清理异常: %s", e, exc_info=True)
        return {"status": "warn", "summary": f"代码清理异常: {e}",
                "findings": [], "findings_count": 0, "clean_plan": [],
                "component_failed": True}
SUB_ENGINE_ORDER_F = ("F1", "F2", "F3", "F4", "F5", "F6")
_ACTION_LIST_KEYS = ("actions", "fix_list", "clean_plan", "ai_fix_list")
_TREATMENT_STATUS = {
    'fail': 'fail', 'error': 'error', 'blocked': 'fail',
    'warn': 'warn', 'warning': 'warn', 'skip': 'warn', 'pass': 'pass',
}
_G3_VERDICT_STATUS = {
    'REJECTED': 'fail', 'APPROVED': 'pass',
    'CONDITIONAL': 'warn', 'PENDING': 'skip',
}
def _count_items(value) -> int:
    return len(value) if isinstance(value, (list, tuple, set, dict)) else 0
def _gate_skip_note(skipped: int) -> str:
    return f", {skipped}项跳过" if skipped else ""
def _g3_apply_verdict_summary(verdict: str, result_dict: dict) -> None:
    _passed = as_count(result_dict.get('passed_gates', 0))
    _failed = as_count(result_dict.get('failed_gates', 0))
    _warned = as_count(result_dict.get('warn_gates', 0))
    _skipped = as_count(result_dict.get('skipped_gates', 0))
    _g_total = _passed + _failed + _warned + _skipped
    _score = result_dict.get('overall_score', 0)
    _skip_note = _gate_skip_note(_skipped)
    if verdict == 'REJECTED':
        _blocking_n = _count_items(result_dict.get('blocking_issues', []))
        result_dict['blocking_count'] = _blocking_n
        result_dict['summary'] = (f"交付门禁拒绝: {_failed}/{_g_total}门禁失败, "
                                  f"评分{_score}, {_blocking_n}项阻断{_skip_note}")
    elif verdict == 'CONDITIONAL':
        result_dict['summary'] = (f"交付门禁条件通过: {_passed}/{_g_total}门禁通过, "
                                  f"{_warned}项WARN{_skip_note}, 评分{_score}")
    elif verdict == 'APPROVED':
        result_dict['summary'] = (f"交付门禁通过: {_passed}/{_g_total}门禁通过"
                                  f"{_skip_note}, 评分{_score}")
    else:
        result_dict['summary'] = "交付门禁待定: 无有效门禁结果"
def run_delivery_gate(skill_dir: str, cache: SharedCache | None = None) -> dict:
    require_warmed(cache, "G3 交付门禁")
    _g3_start = time.time()
    try:
        from jwsgj.diag_delivery_gate import (
            PreDeliveryGate,  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
        )
        _baseline = collect_scale_baseline(skill_dir)
        gate = PreDeliveryGate(skill_dir, baseline_data=_baseline, shared_cache=cache)
        result = gate.execute()
        result_dict = result.to_dict()
        _verdict_raw = result_dict.get('verdict')
        verdict = _verdict_raw if isinstance(_verdict_raw, str) else 'PENDING'
        result_dict['status'] = _G3_VERDICT_STATUS.get(verdict, 'warn')
        _g3_apply_verdict_summary(verdict, result_dict)
        p0_count, p0_fp_exempted, p0_error = collect_round_p0_findings(skill_dir)
        if p0_error:
            result_dict['p0_check_error'] = p0_error
            result_dict['p0_check_degraded'] = True
            result_dict['status'] = 'blocked'
            result_dict['summary'] = (
                f"{result_dict.get('summary', '')} "
                f"[BLOCKED: P0 取证通道降级（{p0_error}），"
                f"按 fail-closed 阻断交付]")
            result_dict['blocking_count'] = (
                as_count(result_dict.get('blocking_count', 0)) + 1)
        if p0_fp_exempted:
            result_dict['p0_fp_exempted'] = p0_fp_exempted
        if p0_count > 0:
            result_dict['status'] = 'blocked'
            result_dict['p0_findings_count'] = p0_count
            _blocking_total = (
                as_count(result_dict.get('blocking_count', 0)) + p0_count)
            result_dict['blocking_count'] = _blocking_total
            existing_summary = result_dict.get('summary', '')
            result_dict['summary'] = (
                f'{existing_summary} [BLOCKED: {p0_count} P0 findings; '
                f'阻断合计 {_blocking_total} 项]')
        perf_trace('g3_gate', round((time.time() - _g3_start) * 1000, 1))
        return result_dict
    except Exception as e:
        logger.warning('[G3] 交付门禁执行异常，本次交付未经门禁校验: %s', e, exc_info=True)
        return {'status': 'skip', 'summary': '交付门禁跳过',
                'error': str(e), 'component_failed': True}
_SUB_ENGINE_CALLABLES_F = {
    "F1": build_ai_fix_list,
    "F2": run_safeops_gate,
    "F3": run_delivery_gate,
    "F4": _run_equivalence_gate_entry,
    "F5": run_refactor_gate,
    "F6": run_deadcode_gate,
}
def _treatment_sub_status(result: dict) -> str:
    if not isinstance(result, dict):
        return "error"
    st = str(result.get("status", "")).lower()
    return _TREATMENT_STATUS.get(st, "warn")
def _iter_action_lists(result: dict):
    for key in _ACTION_LIST_KEYS:
        value = result.get(key)
        if isinstance(value, list):
            yield key, value
def _is_placeholder_action_list(sub_id: str, result: dict, key: str) -> bool:
    return (sub_id == "F1" and key == "ai_fix_list"
            and result.get("list_mode") == "blind")
def _iter_real_action_lists(sub_id: str, result: dict):
    for key, items in _iter_action_lists(result):
        if _is_placeholder_action_list(sub_id, result, key):
            continue
        yield key, items
def _tally_actions_count(result: dict, sub_id: str = "") -> int:
    return sum(len(items) for _key, items in _iter_real_action_lists(
        sub_id, result))
def _run_treatment_sub_engine(sub_id: str, skill_dir: str, cache) -> dict:
    watch = Stopwatch()
    entry = {"sub_engine": sub_id, "detector": sub_id, "source_method": "F",
             "summary": "", "actions_count": 0}
    try:
        fn = _SUB_ENGINE_CALLABLES_F[sub_id]
        result = fn(skill_dir, cache)
        entry["result"] = result
        entry["sub_status"] = _treatment_sub_status(result)
        entry["error"] = None
        if isinstance(result, dict):
            entry["summary"] = safe_text(result.get("summary", ""))
            entry["actions_count"] = _tally_actions_count(result, sub_id)
    except Exception as e:
        _text = safe_text(e)
        entry["sub_status"] = "error"
        entry["error"] = f"{type(e).__name__}: {_text}"
        entry["summary"] = f"{sub_id} 异常: {_text}"
        entry["result"] = {"status": "error",
                           "summary": f"{sub_id} 异常: {_text}"}
        logger.warning("[F] 子引擎 %s 异常: %s", sub_id, e, exc_info=True)
    entry["elapsed_ms"] = round(watch.elapsed_ms(), 1)
    return entry
def _norm_action_item(a, sub_id: str) -> dict:
    if isinstance(a, dict):
        item = dict(a)
        item["sub_engine"] = sub_id
        return item
    return {"sub_engine": sub_id, "action": safe_text(a)}
def _collect_actions(sub_results: dict) -> list:
    actions: list = []
    for sub_id in sub_results:
        res = _sub_result_of(sub_results, sub_id)
        for _key, items in _iter_real_action_lists(sub_id, res):
            actions.extend(_norm_action_item(a, sub_id) for a in items)
    return actions
def _sub_result_of(sub_results: dict, sub_id: str) -> dict:
    _node = sub_results.get(sub_id)
    _raw = _node.get("result") if isinstance(_node, dict) else None
    return _raw if isinstance(_raw, dict) else {}
def _detect_conflicts(sub_results: dict) -> list:
    conflicts: list = []
    f3 = _sub_result_of(sub_results, "F3")
    f4 = _sub_result_of(sub_results, "F4")
    f3_not_pass = str(f3.get("status", "")).lower() in ("fail", "blocked")
    _f4_fc = f4.get("findings_count", 0)
    _f4_has_verdict = (isinstance(_f4_fc, int)
                       and not isinstance(_f4_fc, bool) and _f4_fc > 0)
    f4_pass = (str(f4.get("status", "")).lower() in ("pass", "ok")
               and _f4_has_verdict)
    if f3_not_pass and f4_pass:
        conflicts.append({
            "type": "gate_vs_equivalence",
            "reason": "F3 交付门禁未通过但 F4 等价性验证通过，结论相悖，交人工/AI 审核",
            "gate_status": f3.get("status"),
            "equivalence_status": f4.get("status"),
        })
    return conflicts
_SUB_STATUS_ORDER_F = {"pass": 0, "warn": 1, "fail": 2, "error": 3}
def _worst_treatment_sub_status(sub_results: dict) -> str:
    worst = "pass"
    for entry in sub_results.values():
        st = (str(entry.get("sub_status", "warn"))
              if isinstance(entry, dict) else "error")
        if st not in _SUB_STATUS_ORDER_F:
            st = "warn"
        if _SUB_STATUS_ORDER_F[st] > _SUB_STATUS_ORDER_F[worst]:
            worst = st
    return worst
def _sub_results_view(sub_results: dict) -> dict:
    return {
        sub_id: {
            "sub_status": e["sub_status"],
            "actions_count": e.get("actions_count", 0),
            "elapsed_ms": e.get("elapsed_ms", 0),
            "error": e.get("error"),
            "summary": e.get("summary", ""),
            "result": e.get("result"),
        }
        for sub_id, e in sub_results.items()
    }
def _f_verdict(worst: str) -> tuple[str, str]:
    """治疗链结论：门禁未通过是 verdict=fail，不是执行失败。"""
    _status = str(worst).strip().lower()
    if _status in ("error", "timeout", "blocked", "skip"):
        return "unknown", ""
    if _status == "fail":
        return "fail", "治疗链门禁未通过"
    if _status == "warn":
        return "warn", ""
    return "pass", ""
def run_engine_f(skill_dir: str, cache=None) -> dict:
    cache = ensure_entry_warmed(skill_dir, cache, "主引擎 F 组（治疗域）")
    watch = Stopwatch()
    sub_results: dict = {}
    for sub_id in SUB_ENGINE_ORDER_F:
        sub_results[sub_id] = _run_treatment_sub_engine(sub_id, skill_dir, cache)
    actions = _collect_actions(sub_results)
    conflicts = _detect_conflicts(sub_results)
    worst = _worst_treatment_sub_status(sub_results)
    sub_results_view = _sub_results_view(sub_results)
    payload = {
        "engine": "F", "sub_engines": SUB_ENGINE_ORDER_F,
        "detectors": list(SUB_ENGINE_ORDER_F),
        "sub_results": sub_results_view, "detector_results": sub_results_view,
        "actions_count": len(actions), "conflicts": conflicts,
    }
    _verdict, _verdict_reason = _f_verdict(worst)
    return {
        "status": worst, "engine": "F",
        "verdict": _verdict, "verdict_reason": _verdict_reason,
        "summary": ("主引擎F: 治疗链 G1修复清单+G2安全操作+G3交付门禁+G4等价性验证"
                    f"+G5重构+G6清理, 子引擎{len(sub_results)}个, 动作{len(actions)}个, "
                    f"冲突{len(conflicts)}个"),
        "findings": [], "actions": actions, "payload": payload,
        "sub_results": sub_results, "detector_results": sub_results,
        "conflicts": conflicts,
        "elapsed_ms": round(watch.elapsed_ms(), 1),
    }

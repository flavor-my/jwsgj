from __future__ import annotations

import ast
import logging
import os
from collections import Counter
from dataclasses import dataclass, field
from typing import Any, NamedTuple

from jwsgj.diag_detector_findings import normalize_id_set
from jwsgj.diag_guard_sql_connection import (
    check_RD29,
    check_RD31,
)
from jwsgj.diag_guard_sql_statement import (
    check_RD28,
    check_RD30,
    check_RD32,
)
from jwsgj.diag_module_surface import (
    iter_module_level_nodes_tc,
    run_api_integrity_checks,
)
from jwsgj.diag_rules_text_damage import run_text_checks
from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_NAMES,
    COMP_SCOPE_NODES,
    PY_STDLIB_HINTS,
    TRY_NODE_TYPES,
    TYPE_ALIAS_NODES,
    collect_param_names,
    dotted_name,
    is_constant_expr_stmt,
    is_star_import,
    is_type_checking_guard,
    iter_module_scope_funcdefs,
    iter_module_scope_nodes,
    iter_pattern_capture_names,
    iter_scope_nodes,
    iter_unpack_target_names,
    module_postpones_annotations,
    node_position,
    typing_guard_aliases,
    typing_type_checking_names,
)
from jwsgj.diag_shared_ast_surface import import_time_branch_visibility
from jwsgj.diag_shared_source_core import (
    aligned_source_lines,
    guard_tree,
    is_consolidated_code,
    parse_cached,
)
from jwsgj.diag_smell_detector import check_RD27
from jwsgj.diag_types_defs import (
    FindingRecord,
    finding_scan_exempt,
)
from jwsgj.diag_types_vocab import PROJECT_ROOT_MARKERS
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    "detect_all",
]
_log = logging.getLogger(__name__)
_log.info("diag_symbol_integrity 符号完整性守卫（GF-08/11/13/14/15；RD-26~32 族编排同宿）已加载: %d 项导出", len(__all__))
def _normalize_detect_inputs(code: Any, filepath: Any, tree: Any,
                             exclude_rules: Any) -> tuple:
    if tree is not None and not isinstance(tree, ast.Module):
        raise TypeError("detect_all() 的 tree 必须是 ast.Module")
    if not isinstance(code, str):
        if tree is not None:
            code = ""
        else:
            raise TypeError(
                "detect_all() 需要源码字符串（code: str）；"
                "已解析 AST 请经 tree 参数传入")
    if not isinstance(filepath, str):
        filepath = str(filepath) if filepath else ""
    return code, filepath, tree, frozenset(normalize_id_set(exclude_rules))
def _parse_tree_with_split(code: str, tree: ast.AST | None) -> tuple:
    if tree is not None:
        return tree, True, False
    try:
        return parse_cached(code), True, False
    except (SyntaxError, ValueError):
        _log.warning("detect_all: suppressed SyntaxError/ValueError", exc_info=True)
        return tree, False, False
    except (RecursionError, MemoryError) as _overflow:
        _log.warning(
            "detect_all: suppressed %s（病态嵌套源码）",
            type(_overflow).__name__)
        return tree, False, True
def _run_ast_checks(ctx: _DetectCtx) -> list[dict[str, Any]]:
    if not ctx.syntax_ok:
        return []
    issues = []
    if not ctx.skip("GF-08"):
        issues.extend(check_import_chain_integrity(ctx.code, tree=ctx.tree))
    if not ctx.skip("GF-11"):
        issues.extend(check_variable_lifecycle(ctx.code, tree=ctx.tree))
    issues.extend(run_api_integrity_checks(
        ctx.code, tree=ctx.tree, filepath=ctx.filepath,
        is_excluded=ctx.skip))
    return issues
def _rd26_from_self_import(node: Any, filename: str,
                           pkg_prefix: str, top_level_self: bool) -> bool:
    if not filename or not node.module:
        return False
    if node.level > 0 and pkg_prefix:
        resolved = _rd26_relative_absolute_module(
            node, pkg_prefix, filename)
        if resolved is not None:
            return resolved == pkg_prefix
    if node.module == filename:
        return node.level == 1 or (node.level == 0 and top_level_self)
    return bool(pkg_prefix) and node.level == 0 and node.module == pkg_prefix
def _rd26_parent_import_parts(pkg_prefix: str,
                              filename: str) -> tuple[str, str]:
    parent, _, base = pkg_prefix.rpartition(".")
    if filename == "__init__":
        return parent, base
    return (parent if base == filename else ""), filename
def _rd26_collect_relative_bare(node: Any, filename: str, pkg_prefix: str,
                                self_import_hits: list) -> None:
    parent_pkg, parent_symbol = _rd26_parent_import_parts(
        pkg_prefix, filename)
    if filename == "__init__":
        expected_level = 2 if parent_pkg else 0
        expected_name = parent_symbol
    else:
        expected_level = 1
        expected_name = filename
    if node.level != expected_level or not expected_name:
        return
    for alias in node.names:
        if alias.name == expected_name:
            self_import_hits.append(
                (alias.asname or alias.name, "." * node.level, node.lineno))
class _RD26ImportRegistry:
    def __init__(self) -> None:
        self.imported_symbols: dict[str, list[tuple[str, int]]] = {}
        self.module_imported: set[str] = set()
        self.module_import_src: dict[str, str] = {}
        self.self_import_hits: list[tuple[str, str, int]] = []
    def feed(self, node: Any, filename: str, is_module_level: bool,
             pkg_prefix: str, top_level_self: bool) -> None:
        if isinstance(node, ast.ImportFrom):
            self._feed_importfrom(node, filename, is_module_level, pkg_prefix,
                                  top_level_self)
        elif isinstance(node, ast.Import):
            self._feed_import(node, filename, is_module_level, pkg_prefix,
                              top_level_self)
    def _register(self, sym: str, source: str, lineno: int) -> None:
        self.imported_symbols.setdefault(sym, []).append((source, lineno))
        self.module_imported.add(sym)
        self.module_import_src.setdefault(sym, source)
    def _register_from_aliases(self, node: Any, filename: str,
                               is_module_level: bool, pkg_prefix: str,
                               top_level_self: bool) -> None:
        src_key = "." * node.level + node.module
        from_self = _rd26_from_self_import(
            node, filename, pkg_prefix, top_level_self)
        parent_pkg, parent_symbol = _rd26_parent_import_parts(
            pkg_prefix, filename)
        alias_self = bool(node.level == 0 and parent_pkg
                          and node.module == parent_pkg)
        lineno = node.lineno
        for alias in node.names:
            sym = alias.asname or alias.name
            if sym == "*":
                continue
            if is_module_level:
                self._register(sym, src_key, lineno)
            if from_self or (alias_self and alias.name == parent_symbol):
                self.self_import_hits.append((sym, src_key, lineno))
    def _register_relative_bare(self, node: Any,
                                is_module_level: bool) -> None:
        src_key = "." * node.level
        for alias in node.names:
            sym = alias.asname or alias.name
            if sym == "*":
                continue
            if is_module_level:
                self._register(sym, src_key, node.lineno)
    def _feed_importfrom(self, node: Any, filename: str,
                         is_module_level: bool, pkg_prefix: str,
                         top_level_self: bool) -> None:
        if not node.module:
            self._register_relative_bare(node, is_module_level)
            _rd26_collect_relative_bare(
                node, filename, pkg_prefix, self.self_import_hits)
            return
        self._register_from_aliases(node, filename, is_module_level, pkg_prefix,
                                    top_level_self)
    def _feed_import(self, node: Any, filename: str,
                     is_module_level: bool, pkg_prefix: str,
                     top_level_self: bool) -> None:
        for alias in node.names:
            bound = alias.asname or alias.name.split(".")[0]
            source = alias.name if alias.asname else bound
            if is_module_level:
                self._register(bound, source, node.lineno)
            if ((alias.name == filename and top_level_self)
                    or (pkg_prefix and alias.name == pkg_prefix)):
                self.self_import_hits.append(
                    (bound, alias.name, node.lineno))
def _rd26_is_import_chain(sources: set[str]) -> bool:
    ordered = sorted(sources, key=lambda s: (s.count("."), s))
    for i in range(len(ordered) - 1):
        shorter, longer = ordered[i], ordered[i + 1]
        if not shorter.lstrip(".") or not longer.startswith(shorter + "."):
            return False
    return True
def _rd26_collect_top_imports(tree: Any) -> set:
    return {
        node for node in iter_module_scope_nodes(tree, descend_classes=False)
        if isinstance(node, (ast.Import, ast.ImportFrom))
    }
def _rd26_collect_defined_symbols(tree: Any) -> dict[str, int]:
    defined_symbols: dict[str, int] = {}
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        if isinstance(node, ast.ClassDef):
            defined_symbols.setdefault(node.name, node.lineno)
    for node in iter_module_scope_funcdefs(tree):
        defined_symbols.setdefault(node.name, node.lineno)
    return defined_symbols
def _rd26_merge_residue_findings(registry: _RD26ImportRegistry,
                                 defined_symbols: dict[str, int],
                                 filepath: Any,
                                 fallback_definitions: set[tuple[str, int]]) -> list:
    issues: list[FindingRecord] = []
    for sym in sorted(registry.module_imported & set(defined_symbols))[:5]:
        src_mod = registry.module_import_src[sym]
        def_line = defined_symbols[sym]
        if (sym, def_line) in fallback_definitions:
            continue
        issues.append(FindingRecord(
            id="RD-26", severity="P1", dimension="maintainability",
            file=filepath, line=def_line,
            title=f"合并残留: '{sym}' 既从 {src_mod} 导入又在第{def_line}行内联定义",
            description=f"符号 '{sym}' 同时存在导入与本地定义，合并/迁移操作的典型残留，"
                        f"存在符号双重定义与来源歧义风险。",
            suggestion="删除冗余的导入语句，保留唯一定义（或保留导入删除本地副本），"
                       "确保符号来源唯一。"))
    return issues
def _rd26_self_import_findings(registry: _RD26ImportRegistry, filename: str,
                               filepath: Any) -> list:
    issues: list[FindingRecord] = []
    if not filename:
        return issues
    for sym, src_mod, line_no in registry.self_import_hits:
        issues.append(FindingRecord(
            id="RD-26", severity="P1", dimension="maintainability",
            file=filepath, line=line_no,
            title=f"自导入: '{sym}' 从 {src_mod} 导入,但源模块即当前文件",
            description="从自身模块导入形成循环依赖，合并/拆分操作的残留。",
            suggestion=f"删除该导入语句；'{sym}' 已在本文件中定义，直接使用即可。"))
    return issues
def _rd26_relative_absolute_module(node: ast.ImportFrom,
                                   pkg_prefix: str, filename: str) -> str | None:
    package = (pkg_prefix if filename == "__init__"
               else pkg_prefix.rpartition(".")[0])
    for _ in range(max(0, node.level - 1)):
        package = package.rpartition(".")[0]
    if not package:
        return None
    return ".".join(part for part in (package, node.module) if part)
def _rd26_fallback_branch_entries(body: list, relative: bool,
                                  pkg_prefix: str, filename: str) -> list[tuple]:
    entries = []
    for node in body:
        if isinstance(node, ast.ImportFrom):
            if relative != (node.level > 0):
                continue
            for alias in node.names:
                base = (_rd26_relative_absolute_module(
                    node, pkg_prefix, filename) if relative else node.module)
                entries.append((
                    alias.asname or alias.name,
                    _rd26_resolved_module(base, node, alias),
                    "." * node.level + (node.module or ""), node.lineno))
        elif not relative and isinstance(node, ast.Import):
            for alias in node.names:
                entries.append((alias.asname or alias.name.split(".")[0],
                                alias.name, alias.name, node.lineno))
    return entries
def _rd26_resolved_module(base, node: ast.ImportFrom,
                           alias: ast.alias) -> str:
    """导入分支解析到的**模块**全路径。

    ``from . import sub`` 的 ``node.module`` 是 ``None``：被导入的名字是子模块，
    解析结果必须补上它。漏补时相对分支停在包名（``pkg``）、绝对分支是
    ``sub``，两者永远比不上——双模式回退的等价豁免整体失效，RD-26 会把每条
    回退导入都报成“双重导入”。
    """
    if base and node.module is None and node.level > 0:
        return "%s.%s" % (base, alias.name)
    return base or node.module or alias.name

def _rd26_modules_equivalent(rel_module: str, abs_module: str) -> bool:
    """相对导入解析结果与绝对导入是否指向同一模块。

    双模式导入（``try: from ._shared import X / except ImportError: from
    _shared import X``）里，相对分支解析成 ``<pkg>._shared``、绝对分支是裸
    模块名 ``_shared``——按全路径比较永远不等。绝对分支为**单段名**时按尾段
    比较即可判定同源（多段名不做尾段比较，避免 ``pkg.a.b`` 误配 ``b``）。
    """
    if rel_module == abs_module:
        return True
    if not abs_module or "." in abs_module:
        return False
    return rel_module.endswith("." + abs_module)

def _rd26_record_equivalent_entries(equivalent: dict[str, set[tuple]],
                                    relative: list[tuple],
                                    absolute: list[tuple]) -> None:
    for rel_sym, rel_module, rel_src, rel_line in relative:
        for abs_sym, abs_module, abs_src, abs_line in absolute:
            if rel_sym == abs_sym and _rd26_modules_equivalent(
                    rel_module, abs_module):
                equivalent.setdefault(rel_sym, set()).update({
                    (rel_src, rel_line), (abs_src, abs_line)})
_IMPORT_ERROR_NAME_PARTS = frozenset({"ImportError", "ModuleNotFoundError"})
def _handler_import_error_candidates(handler: ast.ExceptHandler) -> tuple:
    if handler.type is None:
        return ()
    return (handler.type.elts if isinstance(handler.type, ast.Tuple)
            else (handler.type,))
def _import_error_last_parts(candidates: tuple) -> set[str]:
    return {dotted_name(candidate).rpartition(".")[2]
            for candidate in candidates
            if isinstance(candidate, (ast.Name, ast.Attribute))}
def _handler_catches_import_error(handler: ast.ExceptHandler) -> bool:
    return bool(_import_error_last_parts(
        _handler_import_error_candidates(handler)) & _IMPORT_ERROR_NAME_PARTS)
def _rd26_equivalent_fallback_entries(
    tree: Any, pkg_prefix: str, filename: str,
) -> dict[str, set[tuple]]:
    equivalent: dict[str, set[tuple]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, TRY_NODE_TYPES):
            continue
        handlers = [handler for handler in node.handlers
                    if _handler_catches_import_error(handler)]
        for handler in handlers:
            for first_body, second_body in (
                    (node.body, handler.body), (handler.body, node.body)):
                # 回退两分支各自可能用相对或绝对形态书写（如
                # ``from pkg._shared import X`` ↔ ``from _shared import X``）。
                # 旧实现固定把 try 体当相对分支、handler 体当绝对分支，
                # 导致双绝对形态的等价回退永远配不上对，RD-26 把合法回退
                # 误报成“双重导入”。两分支均收集两种形态，等价性交给
                # _rd26_modules_equivalent 按解析后模块判定。
                first = [
                    entry
                    for relative in (True, False)
                    for entry in _rd26_fallback_branch_entries(
                        first_body, relative, pkg_prefix, filename)
                ]
                second = [
                    entry
                    for relative in (True, False)
                    for entry in _rd26_fallback_branch_entries(
                        second_body, relative, pkg_prefix, filename)
                ]
                _rd26_record_equivalent_entries(equivalent, first, second)
    return equivalent
def _rd26_fallback_definition_lines(
        tree: Any, pkg_prefix: str, filename: str) -> set[tuple[str, int]]:
    fallback: set[tuple[str, int]] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, TRY_NODE_TYPES):
            continue
        for handler in node.handlers:
            if not _handler_catches_import_error(handler):
                continue
            for import_body, definition_body in (
                    (node.body, handler.body), (handler.body, node.body)):
                imported_names = {
                    entry[0]
                    for relative in (False, True)
                    for entry in _rd26_fallback_branch_entries(
                        import_body, relative, pkg_prefix, filename)
                }
                for stmt in definition_body:
                    if (isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                          ast.ClassDef))
                            and stmt.name in imported_names):
                        fallback.add((stmt.name, stmt.lineno))
    return fallback
def _rd26_double_import_findings(registry: _RD26ImportRegistry,
                                 filepath: Any,
                                 equivalent_fallback: dict[str, set[tuple]] | None) -> list:
    issues: list[FindingRecord] = []
    for sym, entries in registry.imported_symbols.items():
        sources = {src for src, _ in entries}
        if len(sources) > 1 and not _rd26_is_import_chain(sources):
            exempt_entries = (equivalent_fallback or {}).get(sym, set())
            if entries and all(entry in exempt_entries for entry in entries):
                continue
            line_no = entries[-1][1]
            issues.append(FindingRecord(
                id="RD-26", severity="P2", dimension="maintainability",
                file=filepath, line=line_no,
                title=f"双重导入: '{sym}' 从 {len(sources)} 条路径导入 ({', '.join(sorted(sources)[:3])})",
                description="同一符号多路径导入，来源歧义且其中一条路径失效时将引发 ImportError。",
                suggestion="保留唯一权威导入路径，删除其余导入语句。"))
    return issues
def _rd26_project_root(path: str) -> str | None:
    cur = os.path.dirname(os.path.abspath(path))
    while True:
        if any(os.path.exists(os.path.join(cur, marker))
               for marker in PROJECT_ROOT_MARKERS):
            return cur
        parent = os.path.dirname(cur)
        if parent == cur:
            return None
        cur = parent
def _rd26_package_root(path: str) -> str | None:
    abs_path = os.path.abspath(path)
    directory = os.path.dirname(abs_path)
    cur = directory
    while os.path.isfile(os.path.join(cur, "__init__.py")):
        parent = os.path.dirname(cur)
        if parent == cur:
            break
        cur = parent
    if cur != directory:
        return cur
    return _rd26_project_root(abs_path)
def _rd26_is_absolute_path(text: str) -> bool:
    return os.path.isabs(text) or (len(text) > 1 and text[1] == ":")
def _rd26_module_path_from_parts(parts: list[str], filename: str) -> str:
    parts = [part for part in parts if part not in ("", ".", "..")]
    if not parts:
        return ""
    base = parts[-1].removesuffix(".py")
    if base != filename:
        base = filename
    parts[-1] = base
    if base == "__init__":
        parts.pop()
    return ".".join(parts)
def _rd26_module_path(filepath: Any, filename: str) -> str:
    if not filepath or not filename:
        return ""
    text = str(filepath)
    normalized = os.path.normpath(text).replace("\\", "/")
    relative = not _rd26_is_absolute_path(text)
    if relative and (normalized == ".." or normalized.startswith("../")):  # jwsgj:suppress SS-02 — 路径守卫判定，非路径访问
        return ""
    root = _rd26_package_root(text)
    if root is None:
        if relative:
            return _rd26_module_path_from_parts(
                normalized.split("/"), filename)
        parent = os.path.basename(os.path.dirname(os.path.abspath(text)))
        return f"{parent}.{filename}" if parent else ""
    try:
        path = os.path.relpath(os.path.abspath(text), root)
    except ValueError as _swallowed_exc:
        _log.debug("_rd26_module_path: 跨盘符相对路径不可求: %s",
                   _swallowed_exc, exc_info=True)
        return ""
    parts = path.replace("\\", "/").split("/")
    if (len(parts) > 1 and parts[0] == "src"
            and not os.path.isfile(os.path.join(root, "src", "__init__.py"))):
        parts = parts[1:]
    return _rd26_module_path_from_parts(parts, filename)
def _rd26_alternate_module_paths(filepath: Any, filename: str,
                                 primary: str) -> list[str]:
    if not primary:
        return []
    text = str(filepath)
    normalized = os.path.normpath(text).replace("\\", "/")
    if not _rd26_is_absolute_path(text):
        if normalized == ".." or normalized.startswith("../"):  # jwsgj:suppress SS-02 — 路径守卫判定，非路径访问
            return []
        legacy = _rd26_module_path_from_parts(
            normalized.split("/"), filename)
        return [legacy] if legacy and legacy != primary else []
    root = _rd26_package_root(text)
    if root is None:
        return []
    try:
        path = os.path.relpath(os.path.abspath(text), root)
    except ValueError as _swallowed_exc:
        _log.debug("_rd26_alternate_module_paths: 跨盘符相对路径不可求: %s",
                   _swallowed_exc, exc_info=True)
        return []
    legacy = _rd26_module_path_from_parts(
        path.replace("\\", "/").split("/"), filename)
    return [legacy] if legacy and legacy != primary else []
def _rd26_top_level_self_possible(filepath: Any, filename: str,
                                  pkg_prefix: str) -> bool:
    if not filename:
        return False
    if not pkg_prefix:
        return True
    text = str(filepath or "")
    if not _rd26_is_absolute_path(text):
        return pkg_prefix == filename
    root = _rd26_package_root(text)
    if root is None:
        return True
    candidate = os.path.join(root, filename + ".py")
    return os.path.normcase(os.path.abspath(text)) == os.path.normcase(
        os.path.abspath(candidate))
def check_RD26(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues: list[FindingRecord] = []
    if tree is None:
        return issues
    filename = os.path.splitext(os.path.basename(filepath))[0] if filepath else ""
    pkg_prefix = _rd26_module_path(filepath, filename)
    top_level_self = _rd26_top_level_self_possible(
        filepath, filename, pkg_prefix)
    alternate_prefixes = _rd26_alternate_module_paths(
        filepath, filename, pkg_prefix)
    registry = _RD26ImportRegistry()
    top_imports = _rd26_collect_top_imports(tree)
    for node in walk_nodes(tree):
        registry.feed(node, filename, node in top_imports, pkg_prefix,
                      top_level_self)
    equivalent_fallback = _rd26_equivalent_fallback_entries(
        tree, pkg_prefix, filename)
    for alternate in alternate_prefixes:
        alternate_registry = _RD26ImportRegistry()
        for node in walk_nodes(tree):
            if (isinstance(node, ast.Import)
                    or (isinstance(node, ast.ImportFrom) and node.level == 0)):
                alternate_registry.feed(
                    node, filename, False, alternate, top_level_self)
        for hit in alternate_registry.self_import_hits:
            if hit not in registry.self_import_hits:
                registry.self_import_hits.append(hit)
        for sym, entries in _rd26_equivalent_fallback_entries(
                tree, alternate, filename).items():
            equivalent_fallback.setdefault(sym, set()).update(entries)
    issues.extend(_rd26_merge_residue_findings(
        registry, _rd26_collect_defined_symbols(tree), filepath,
        _rd26_fallback_definition_lines(tree, pkg_prefix, filename)))
    issues.extend(_rd26_self_import_findings(registry, filename, filepath))
    issues.extend(_rd26_double_import_findings(
        registry, filepath, equivalent_fallback))
    return issues
_RD_CHECKERS: tuple[tuple[str, Any], ...] = (
    ("RD-26", check_RD26), ("RD-27", check_RD27),
    ("RD-28", check_RD28), ("RD-29", check_RD29),
    ("RD-30", check_RD30), ("RD-31", check_RD31),
    ("RD-32", check_RD32),
)
def run_rd_checks(tree: Any, source_lines: Any, filepath: Any, *,
                  syntax_ok: bool = True, is_excluded: Any = None
                  ) -> list[FindingRecord]:
    if not syntax_ok:
        _log.warning(
            "detect_all: RD-26~RD-32 重构残留与数据库安全检测因语法错误跳过")
        return []
    issues: list[FindingRecord] = []
    for rule_id, checker in _RD_CHECKERS:
        if is_excluded is not None and is_excluded(rule_id):
            continue
        issues.extend(checker(tree, source_lines, filepath))
    return issues
def _finding_identity(finding: Any) -> tuple[str, str]:
    if isinstance(finding, dict):
        return (str(finding.get("severity", "?")),
                str(finding.get("rule_id", finding.get("id", "?"))))
    return (str(getattr(finding, "severity", "?")),
            str(getattr(finding, "id", getattr(finding, "rule_id", "?"))))
def _log_findings(issues: list, filepath: str) -> None:
    if not issues:
        return
    sev_dist: Counter[str] = Counter()
    rule_dist: Counter[str] = Counter()
    for finding in issues:
        severity, rule_id = _finding_identity(finding)
        sev_dist[severity] += 1
        rule_dist[rule_id] += 1
    _log.warning(
        "[GuardSymbol] detect_all 检出 %d 项: sev=%s rules=%s file=%s",
        len(issues), dict(sev_dist), dict(rule_dist), filepath or "<code>",
    )
class _DetectCtx(NamedTuple):
    code: str
    tree: ast.Module | None
    source_lines: Any
    filepath: str
    syntax_ok: bool
    parse_overflow: bool
    excluded_rules: frozenset[str]
    text_policy: Any = None
    def skip(self, rule_id: str) -> bool:
        return bool(normalize_id_set((rule_id,)) & self.excluded_rules)
def detect_all(code: Any, tree: ast.Module | None = None,
               source_lines: Any = None, filepath: str = "",
               exclude_rules: Any = None, *,
               text_policy: Any = None,
               ) -> list[dict[str, Any] | FindingRecord]:
    code, filepath, tree, exclude_rules = _normalize_detect_inputs(
        code, filepath, tree, exclude_rules)
    if finding_scan_exempt(filepath):
        return []
    tree, syntax_ok, parse_overflow = _parse_tree_with_split(code, tree)
    ctx = _DetectCtx(
        code=code,
        tree=tree,
        source_lines=(aligned_source_lines(code) if source_lines is None
                      else source_lines),
        filepath=filepath,
        syntax_ok=syntax_ok,
        parse_overflow=parse_overflow,
        excluded_rules=exclude_rules,
        text_policy=text_policy,
    )
    issues: list[dict[str, Any] | FindingRecord] = list(run_text_checks(
        ctx.code,
        syntax_ok=ctx.syntax_ok,
        parse_overflow=ctx.parse_overflow,
        is_excluded=ctx.skip,
        filepath=ctx.filepath,
        policy=ctx.text_policy,
    ))
    issues.extend(_run_ast_checks(ctx))
    issues.extend(run_rd_checks(
        ctx.tree, ctx.source_lines, ctx.filepath,
        syntax_ok=ctx.syntax_ok, is_excluded=ctx.skip))
    _log_findings(issues, ctx.filepath)
    return issues
def _is_narrow_import_error_handler(handler: ast.ExceptHandler) -> bool:
    candidates = _handler_import_error_candidates(handler)
    if not candidates or not all(
            isinstance(candidate, (ast.Name, ast.Attribute))
            for candidate in candidates):
        return False
    return (_import_error_last_parts(candidates)
            <= _IMPORT_ERROR_NAME_PARTS)
def _gf08_is_import_probe(node, try_types) -> bool:
    if not isinstance(node, try_types):
        return False
    pending = list(node.body)
    while pending:
        stmt = pending.pop()
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            return True
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, *try_types)):
            continue
        if isinstance(stmt, ast.ClassDef):
            pending.extend(stmt.body)
            continue
        pending.extend(_rebind_child_stmts(stmt))
    return False
def _gf08_is_silent_handler(handler) -> bool:
    return bool(handler.body) and all(
        isinstance(stmt, ast.Pass) or is_constant_expr_stmt(stmt)
        for stmt in handler.body)
def _gf08_report_silent_handler(node, issues: list) -> None:
    for handler in node.handlers:
        if _gf08_is_silent_handler(handler):
            if _is_narrow_import_error_handler(handler):
                continue
            issues.append({
                "rule_id": "GF-08",
                "severity": "P0",
                "line": node.lineno,
                "message": "脆弱导入链: try/except导入+静默吞错,"
                           "重构时易导致级联失败",
                "fix": "改为直接导入或移除try/except,"
                       "若模块不可用则让ImportError自然传播",
                "category": "import_chain",
            })
            break
def check_import_chain_integrity(code: Any, tree: ast.AST | None = None) -> Any:
    issues = []
    if is_consolidated_code(code):
        return issues
    tree = guard_tree(code, tree)
    if tree is None:
        return issues
    _prepare_symbol_branch_visibility(tree)
    for node in walk_nodes(tree):
        if _gf08_is_import_probe(node, TRY_NODE_TYPES):
            _gf08_report_silent_handler(node, issues)
    return issues
_TYPE_PARAM_TYPES: tuple = tuple(
    _t for _t in (getattr(ast, _n, None)
                  for _n in ("TypeVar", "ParamSpec", "TypeVarTuple"))
    if _t is not None)
def signature_children(node) -> list:
    if isinstance(node, ast.Lambda):
        return [node.args]
    if isinstance(node, ast.ClassDef):
        return [*node.decorator_list, *node.bases, *node.keywords,
                *(getattr(node, "type_params", None) or ())]
    kids = [node.args, *node.decorator_list,
            *(getattr(node, "type_params", None) or ())]
    if node.returns is not None:
        kids.append(node.returns)
    return kids
class _RebindEvent(NamedTuple):
    position: tuple[int, int]
    line: int
    origin: int | None = None
    path: tuple = ()
class _DeleteEvent(NamedTuple):
    position: tuple[int, int]
    origin: int | None = None
    path: tuple = ()
class _ModuleEventTiming(NamedTuple):
    position: tuple[int, ...]
    read_position: tuple[int, ...]
    source_position: tuple[int, int]
    path: tuple = ()
class _Activation(NamedTuple):
    position: tuple[int, int]
    caller: int | None
    callee: int
    direct: bool = True
def _end_position(node: Any) -> tuple[int, int]:
    start = node_position(node)
    end_line = getattr(node, "end_lineno", None)
    end_col = getattr(node, "end_col_offset", None)
    return (start[0] if end_line is None else end_line,
            start[1] if end_col is None else end_col)
def _rebind_event(node: Any, line_node: Any = None) -> _RebindEvent:
    source = line_node if line_node is not None else node
    return _RebindEvent(_end_position(node), getattr(source, "lineno", 0))
def _walrus_binding(node: Any) -> tuple[str, _RebindEvent] | None:
    if isinstance(node, ast.NamedExpr) and isinstance(node.target, ast.Name):
        return (node.target.id, _rebind_event(node))
    return None
def _walrus_scope_children(node: Any) -> list:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)):
        return signature_children(node)
    return [child for child in ast.iter_child_nodes(node)
            if not isinstance(child, ast.stmt)]
def _iter_module_walrus_binds(stmt: Any) -> list:
    out: list[tuple[str, _RebindEvent]] = []
    stack = [stmt]
    while stack:
        node = stack.pop()
        binding = _walrus_binding(node)
        if binding is not None:
            out.append(binding)
        stack.extend(_walrus_scope_children(node))
    return out
def _bind_target_names(targets, event: _RebindEvent, add) -> None:
    for name in iter_unpack_target_names(targets):
        add(name, event)
def _iter_import_bindings(st) -> Any:
    if isinstance(st, ast.Import):
        return (a.asname or a.name.split(".")[0] for a in st.names)
    return (a.asname or a.name for a in st.names if a.name != "*")
def _iter_with_bindings(items) -> Any:
    for item in items:
        if item.optional_vars is not None:
            yield from iter_unpack_target_names(item.optional_vars)
def _bind_module_import_names(st, event: _RebindEvent, add) -> None:
    for name in _iter_import_bindings(st):
        add(name, event)
def _bind_match_captures(st: ast.Match, add) -> None:
    for case in st.cases:
        event = _rebind_event(case.pattern, st)
        for name in iter_pattern_capture_names(case.pattern):
            add(name, event)
def _bind_with_events(st: ast.With | ast.AsyncWith, add) -> None:
    for item in st.items:
        if item.optional_vars is None:
            continue
        event = _rebind_event(item.context_expr, st)
        for name in iter_unpack_target_names(item.optional_vars):
            add(name, event)
def _rebind_primary_binds(st, add) -> bool:
    if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        add(st.name, _rebind_event(st))
        return True
    if TYPE_ALIAS_NODES and isinstance(st, TYPE_ALIAS_NODES):
        _bind_target_names((st.name,), _rebind_event(st), add)
        return True
    if isinstance(st, ast.Assign):
        _bind_target_names(st.targets, _rebind_event(st), add)
        return True
    if isinstance(st, (ast.Import, ast.ImportFrom)):
        _bind_module_import_names(st, _rebind_event(st), add)
        return True
    return False
def _rebind_compound_binds(st, add) -> None:
    if isinstance(st, ast.AnnAssign):
        if st.value is not None:
            _bind_target_names((st.target,), _rebind_event(st), add)
        return
    if isinstance(st, (ast.For, ast.AsyncFor)):
        _bind_target_names((st.target,), _rebind_event(st.iter, st), add)
        return
    if isinstance(st, (ast.With, ast.AsyncWith)):
        _bind_with_events(st, add)
        return
    if isinstance(st, ast.Match):
        _bind_match_captures(st, add)
def _rebind_stmt_binds(st, add) -> None:
    if not _rebind_primary_binds(st, add):
        _rebind_compound_binds(st, add)
def _try_scope_children(st: Any) -> list:
    children = [*st.body, *st.orelse, *st.finalbody]
    for handler in st.handlers:
        children.extend(handler.body)
    return children
def _match_scope_children(st: Any) -> list:
    children: list = []
    for case in st.cases:
        children.extend(case.body)
    return children
_SYMBOL_BRANCH_VISIBILITY_ATTR = "_jwsgj_symbol_branch_visibility"
def _prepare_symbol_branch_visibility(tree: Any) -> None:
    typing_aliases = typing_guard_aliases(tree)
    type_checking_names = typing_type_checking_names(tree) or None
    for node in walk_nodes(tree):
        if isinstance(node, ast.If):
            setattr(
                node, _SYMBOL_BRANCH_VISIBILITY_ATTR,
                import_time_branch_visibility(
                    node.test, typing_aliases, type_checking_names))
def _rebind_child_stmts(st: Any) -> list:
    if isinstance(st, ast.If):
        visible = getattr(st, _SYMBOL_BRANCH_VISIBILITY_ATTR, None)
        if visible is not None:
            return list(st.body if visible else st.orelse)
        if isinstance(st.test, ast.Constant):
            return list(st.body if st.test.value else st.orelse)
    if isinstance(st, (ast.For, ast.AsyncFor, ast.While, ast.If)):
        return [*st.body, *st.orelse]
    if isinstance(st, TRY_NODE_TYPES):
        return _try_scope_children(st)
    if isinstance(st, (ast.With, ast.AsyncWith)):
        return list(st.body)
    if isinstance(st, ast.Match):
        return _match_scope_children(st)
    return []
def _rebind_branch_blocks(st: Any) -> list[tuple[list, tuple | None]]:
    if isinstance(st, ast.If):
        visible = getattr(st, _SYMBOL_BRANCH_VISIBILITY_ATTR, None)
        if visible is None and isinstance(st.test, ast.Constant):
            visible = bool(st.test.value)
        if visible is not None:
            return [(st.body if visible else st.orelse, None)]
        return [
            (st.body, (id(st), "if", 0)),
            (st.orelse, (id(st), "if", 1)),
        ]
    if isinstance(st, (ast.For, ast.AsyncFor, ast.While)):
        return [
            (st.body, (id(st), "loop", 0)),
            (st.orelse, (id(st), "loop", 1)),
        ]
    if isinstance(st, TRY_NODE_TYPES):
        branch_count = len(st.handlers) + 1
        branches = [
            ([*st.body, *st.orelse], (id(st), "try", 0, branch_count)),
            *((handler.body, (id(st), "try", index, branch_count))
              for index, handler in enumerate(st.handlers, 1)),
        ]
        branches.append((st.finalbody, None))
        return branches
    return [(_rebind_child_stmts(st), None)]


def _child_branch_markers(node: Any) -> dict[int, tuple]:
    """直接子节点 → 读取路径上追加的分支标记（与 _rebind_branch_blocks 同口径）。"""
    if isinstance(node, ast.If):
        visible = getattr(node, _SYMBOL_BRANCH_VISIBILITY_ATTR, None)
        if visible is None and isinstance(node.test, ast.Constant):
            visible = bool(node.test.value)
        if visible is not None:
            return {}
        return {
            **{id(child): (id(node), "if", 0) for child in node.body},
            **{id(child): (id(node), "if", 1) for child in node.orelse},
        }
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        return {
            **{id(child): (id(node), "loop", 0) for child in node.body},
            **{id(child): (id(node), "loop", 1) for child in node.orelse},
        }
    if isinstance(node, TRY_NODE_TYPES):
        branch_count = len(node.handlers) + 1
        markers = {
            id(child): (id(node), "try", 0, branch_count)
            for child in (*node.body, *node.orelse)}
        markers.update({
            id(handler): (id(node), "try", index, branch_count)
            for index, handler in enumerate(node.handlers, 1)})
        return markers
    return {}


def _read_path_sees_event(read_path: tuple, event_path: tuple) -> bool:
    """删除事件的分支路径与读取点路径能否落在同一次执行。

    同一分支节点的两个标记：if 两个分支互斥；loop 体与 else、try 体与
    handler 顺序执行（前一阶段的删除对后一阶段可见）。
    """
    decisions = {marker[0]: marker for marker in read_path}
    for marker in event_path:
        current = decisions.get(marker[0])
        if current is None or current == marker or current[1] == "loop":
            continue
        if current[1] == "try" and (current[2] == 0 or marker[2] == 0):
            continue
        return False
    return True


def _module_rebind_walk(stmts, add, path: tuple = ()) -> None:
    for st in stmts:
        if getattr(st, "lineno", None) is None:
            continue
        def add_at_path(name: str, event: _RebindEvent) -> None:
            add(name, event._replace(path=path))
        for name, event in _iter_module_walrus_binds(st):
            add_at_path(name, event)
        _rebind_stmt_binds(st, add_at_path)
        if isinstance(st, TRY_NODE_TYPES):
            for handler in st.handlers:
                if handler.name:
                    add_at_path(
                        handler.name, _rebind_event(handler.type, handler))
        for children, marker in _rebind_branch_blocks(st):
            _module_rebind_walk(
                children, add, path if marker is None else (*path, marker))
def _statement_rebind_events(stmts: Any) -> dict:
    rebinds: dict[str, list[_RebindEvent]] = {}
    def _add(name: str, event: _RebindEvent) -> None:
        rebinds.setdefault(name, []).append(event)
    _module_rebind_walk(stmts, _add)
    return rebinds
def module_rebind_events(tree: Any) -> dict:
    rebinds = _statement_rebind_events(tree.body)
    for name, events in _gf11_global_rebind_events(tree).items():
        rebinds.setdefault(name, []).extend(events)
    return rebinds
def collect_module_del_targets(
        stmts: Any, del_targets: dict, path: tuple = ()) -> None:
    for st in stmts:
        if isinstance(st, TRY_NODE_TYPES):
            for handler in st.handlers:
                if handler.name:
                    del_targets.setdefault(handler.name, []).append(
                        _DeleteEvent(_end_position(handler), path=path))
        if isinstance(st, ast.Delete):
            for target in st.targets:
                for name in iter_unpack_target_names(target):
                    del_targets.setdefault(name, []).append(
                        _DeleteEvent(node_position(st), path=path))
        for children, marker in _rebind_branch_blocks(st):
            collect_module_del_targets(
                children, del_targets,
                path if marker is None else (*path, marker))
def _expr_bind_name(node: Any) -> str | None:
    if isinstance(node, ast.NamedExpr):
        return node.target.id if isinstance(node.target, ast.Name) else None
    if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
        return node.id
    return None
def _for_bind_name(node: Any) -> str | None:
    if not isinstance(node, (ast.For, ast.AsyncFor)):
        return None
    return node.target.id if isinstance(node.target, ast.Name) else None
def _func_single_bind_name(node: Any) -> str | None:
    for extract in (_expr_bind_name, _for_bind_name):
        name = extract(node)
        if name is not None:
            return name
    if isinstance(node, ast.ExceptHandler):
        return node.name or None
    return None
def _bind_func_match_captures(node: ast.Match, owner: set) -> None:
    owner.update(name for case in node.cases
                 for name in iter_pattern_capture_names(case.pattern))
def _func_local_collect(node, owner: set, in_comp: bool) -> None:
    name = _func_single_bind_name(node)
    if name is not None:
        if not in_comp or isinstance(node, ast.NamedExpr):
            owner.add(name)
        return
    if isinstance(node, ast.Delete):
        for target in node.targets:
            owner.update(iter_unpack_target_names(target))
        return
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        owner.update(_iter_import_bindings(node))
        return
    if isinstance(node, (ast.With, ast.AsyncWith)):
        owner.update(_iter_with_bindings(node.items))
        return
    if isinstance(node, ast.Match):
        _bind_func_match_captures(node, owner)
def _push_func_scope_frame(stack: list, binds: dict, node, owner) -> None:
    new_owner: set = set()
    binds[id(node)] = new_owner
    new_owner.update(collect_param_names(node))
    new_owner.update(
        child.target.id for child in iter_scope_nodes(node)
        if isinstance(child, ast.AnnAssign) and child.value is None
        and isinstance(child.target, ast.Name))
    if owner is not None and hasattr(node, "name"):
        owner.add(node.name)
    for child in signature_children(node):
        stack.append((child, owner, False))
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        for _st in node.body:
            stack.append((_st, new_owner, False))
    else:
        stack.append((node.body, new_owner, False))
def _push_class_scope_frame(stack: list, binds: dict, node: ast.ClassDef,
                            owner, in_comp: bool) -> None:
    cls_owner: set = set()
    binds[id(node)] = cls_owner
    if owner is not None:
        owner.add(node.name)
    for child in signature_children(node):
        stack.append((child, owner, in_comp))
    for _st in node.body:
        stack.append((_st, cls_owner, False))
def _func_local_visit_node(node: Any, owner: Any, in_comp: bool,
                           stack: list, binds: dict) -> bool:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        _push_func_scope_frame(stack, binds, node, owner)
        return True
    if isinstance(node, ast.ClassDef):
        _push_class_scope_frame(stack, binds, node, owner, in_comp)
        return True
    if isinstance(node, ast.AnnAssign) and node.value is None:
        if node.annotation is not None:
            stack.append((node.annotation, owner, in_comp))
        return True
    if owner is not None:
        _func_local_collect(node, owner, in_comp)
    return False
def func_local_bind_map(tree: Any) -> dict:
    binds: dict = {}
    stack = [(tree, None, False)]
    while stack:
        node, owner, in_comp = stack.pop()
        if _func_local_visit_node(node, owner, in_comp, stack, binds):
            continue
        _child_in_comp = in_comp or isinstance(node, COMP_SCOPE_NODES)
        for child in ast.iter_child_nodes(node):
            stack.append((child, owner, _child_in_comp))
    for declaration_type in (ast.Global, ast.Nonlocal):
        for scope, names in _gf11_scopes_with_declarations(
                tree, declaration_type):
            binds[id(scope)].difference_update(names)
    return binds
@dataclass
class _DelUseContext:
    del_targets: dict
    rebinds: dict
    global_scopes: dict
    activations: dict
    scope_owners: dict
    issues: list
class _FrameA(NamedTuple):
    node: Any
    chain: tuple
    comp_chain: tuple
    path: tuple = ()
class _FrameB(NamedTuple):
    node: Any
    lb_chain: tuple
    comp_chain: tuple
    path: tuple = ()
def _comp_children_frames(comp_node: Any, template: Any) -> tuple:
    frames = []
    bound_scopes = []
    active_chain = template.comp_chain
    for index, generator in enumerate(comp_node.generators):
        if index:
            frames.append(template._replace(
                node=generator.iter,
                comp_chain=(*bound_scopes, *template.comp_chain)))
        bound_scopes.append(frozenset(
            iter_unpack_target_names(generator.target)))
        active_chain = (*bound_scopes, *template.comp_chain)
        frames.append(template._replace(
            node=generator.target, comp_chain=active_chain))
        frames.extend(template._replace(node=condition,
                                        comp_chain=active_chain)
                      for condition in generator.ifs)
    result_exprs = ((comp_node.key, comp_node.value)
                    if isinstance(comp_node, ast.DictComp) else (comp_node.elt,))
    frames.extend(template._replace(node=expr, comp_chain=active_chain)
                  for expr in result_exprs)
    return tuple(frames)
def _is_read_name(node, augassign_read: bool) -> bool:
    return (isinstance(node, ast.Name)
            and (augassign_read or isinstance(node.ctx, ast.Load)))
def _frame_execution_scopes(frame: _FrameA, scope_owners: dict) -> set:
    owners = set()
    in_function = False
    for scope, kind in frame.chain:
        if kind == 2:
            continue
        owner = scope_owners.get(id(scope))
        if owner is not None:
            owners.add(owner)
        in_function = in_function or kind == 0
    if not in_function:
        owners.add(None)
    return owners
def _event_effective_position(frame: _FrameA, event: Any,
                              ctx: _DelUseContext) -> tuple[int, ...] | None:
    read_position = node_position(frame.node)
    scopes = _frame_execution_scopes(frame, ctx.scope_owners)
    if event.origin is None or event.origin in scopes:
        return event.position if event.position < read_position else None
    return max((
        (*site.position, *event.position)
        for site in ctx.activations.get(event.origin, ())
        if site.caller in scopes
        and (site.direct or event.position < site.position)
        and site.position < read_position
    ), default=None)
def _del_use_del_position(frame: _FrameA, augassign_read: bool,
                          scope_key: Any, ctx: _DelUseContext) -> tuple | None:
    node = frame.node
    del_targets = ctx.del_targets.get(scope_key, {})
    if not (_is_read_name(node, augassign_read) and node.id in del_targets
            and hasattr(node, "lineno")):
        return None
    candidates = []
    read_scope = _frame_function_scope(frame, ctx)
    event_scope = ctx.scope_owners.get(scope_key)
    in_event_class_body = any(
        kind == 1 and ctx.scope_owners.get(id(scope)) == event_scope
        for scope, kind in frame.chain
    )
    for event in del_targets[node.id]:
        if (event.origin is None and read_scope != event_scope
                and not in_event_class_body):
            continue
        if not _read_path_sees_event(frame.path, event.path):
            continue
        effective = _event_effective_position(frame, event, ctx)
        if effective is not None:
            candidates.append((effective, event.position, event.path))
    return max(candidates, key=lambda item: item[0], default=None)
def _frame_function_scope(frame: _FrameA, ctx: _DelUseContext) -> int | None:
    for scope, kind in frame.chain:
        if kind == 0:
            return ctx.scope_owners.get(id(scope))
    return None
def _direct_module_event_orders(event: Any, ctx: _DelUseContext) -> list[tuple]:
    if event.origin is None:
        return [(*event.position, *event.position)]
    return [(*site.position, *event.position)
            for site in ctx.activations.get(event.origin, ())
            if site.caller is None]
def _direct_module_del_timing(frame: _FrameA, augassign_read: bool,
                              scope_key: Any, ctx: _DelUseContext
                              ) -> _ModuleEventTiming | None:
    if scope_key is not None or not _is_read_name(frame.node, augassign_read):
        return None
    read_scope = _frame_function_scope(frame, ctx)
    if read_scope is None:
        return None
    node = frame.node
    candidates: list[_ModuleEventTiming] = []
    for read_site in ctx.activations.get(read_scope, ()):
        if read_site.caller is not None:
            continue
        read_order = (*read_site.position, *node_position(node))
        for event in ctx.del_targets.get(None, {}).get(node.id, ()):
            if not _read_path_sees_event(frame.path, event.path):
                continue
            for event_order in _direct_module_event_orders(event, ctx):
                if event_order < read_order:
                    candidates.append(_ModuleEventTiming(
                        event_order, read_order, event.position, event.path))
    return max(candidates, key=lambda item: item.position, default=None)
def _direct_module_rebind_exempt(frame: _FrameA, deletion: _ModuleEventTiming,
                                 rebinds: dict, ctx: _DelUseContext) -> bool:
    paths = []
    for event in rebinds.get(frame.node.id, ()):
        for event_order in _direct_module_event_orders(event, ctx):
            if deletion.position < event_order < deletion.read_position:
                paths.append(event.path)
    return _rebind_paths_cover_delete(paths, deletion.path)
def _direct_closure_event_orders(event: Any, event_scope: int,
                                 ctx: _DelUseContext) -> list[tuple]:
    if event.origin is None:
        return [(*event.position, 0, 0)]
    return [(*site.position, *event.position)
            for site in ctx.activations.get(event.origin, ())
            if site.caller == event_scope]
def _direct_closure_del_timing(
        frame: _FrameA, augassign_read: bool, scope_key: Any,
        ctx: _DelUseContext) -> _ModuleEventTiming | None:
    if scope_key is None or not _is_read_name(frame.node, augassign_read):
        return None
    read_scope = _frame_function_scope(frame, ctx)
    event_scope = ctx.scope_owners.get(scope_key)
    if (read_scope is None or event_scope is None
            or read_scope == event_scope):
        return None
    node = frame.node
    candidates: list[_ModuleEventTiming] = []
    for read_site in ctx.activations.get(read_scope, ()):
        if read_site.caller != event_scope:
            continue
        read_order = (*read_site.position, *node_position(node))
        for event in ctx.del_targets.get(scope_key, {}).get(node.id, ()):
            for event_order in _direct_closure_event_orders(
                    event, event_scope, ctx):
                if event_order < read_order:
                    candidates.append(_ModuleEventTiming(
                        event_order, read_order, event.position, event.path))
    return max(candidates, key=lambda item: item.position, default=None)
def _direct_closure_rebind_exempt(
        frame: _FrameA, deletion: _ModuleEventTiming, rebinds: dict,
        ctx: _DelUseContext) -> bool:
    scope_key = _del_scope_key(frame, ctx.global_scopes)
    event_scope = ctx.scope_owners.get(scope_key)
    paths = []
    for event in rebinds.get(frame.node.id, ()):
        for event_order in _direct_closure_event_orders(
                event, event_scope, ctx):
            if deletion.position < event_order < deletion.read_position:
                paths.append(event.path)
    return _rebind_paths_cover_delete(paths, deletion.path)
def _del_scope_key(frame: _FrameA, global_scopes: dict):
    name = frame.node.id
    for scope, kind in frame.chain:
        if kind == 2:  
            continue
        if name in global_scopes.get(id(scope), ()):
            return None
        if name in scope:
            return id(scope)
    return None
def _path_is_prefix(prefix: tuple, path: tuple) -> bool:
    return len(prefix) <= len(path) and path[:len(prefix)] == prefix


def _rebind_paths_cover_delete(paths, delete_path: tuple) -> bool:
    paths = tuple(set(paths))
    if any(_path_is_prefix(path, delete_path) for path in paths):
        return True

    def covers(prefix: tuple) -> bool:
        if prefix in paths:
            return True
        markers = {
            path[len(prefix)] for path in paths
            if len(path) > len(prefix) and _path_is_prefix(prefix, path)
        }
        by_node: dict[int, set] = {}
        for marker in markers:
            by_node.setdefault(marker[0], set()).add(marker)
        for node_id, node_markers in by_node.items():
            sample = next(iter(node_markers))
            if sample[1] == "try":
                branch_count = sample[3]
                required = {
                    (node_id, "try", index, branch_count)
                    for index in range(branch_count)
                }
            elif sample[1] == "if":
                required = {(node_id, "if", 0), (node_id, "if", 1)}
            else:
                continue
            if all(marker in node_markers for marker in required) and all(
                    covers((*prefix, marker)) for marker in required):
                return True
        return False

    return covers(delete_path)


def _del_use_exempt(frame: _FrameA, del_position: tuple[int, int],
                    rebinds: dict, ctx: _DelUseContext,
                    delete_path: tuple = ()) -> bool:
    node = frame.node
    read_position = node_position(node)
    paths = []
    for event in rebinds.get(node.id, ()):
        effective = _event_effective_position(frame, event, ctx)
        if (effective is not None
                and del_position < effective < read_position):
            paths.append(event.path)
    return (_rebind_paths_cover_delete(paths, delete_path)
            or _shadowed_in_comp(frame))
def _shadowed_in_comp(frame: _FrameA) -> bool:
    return any(frame.node.id in scope for scope in frame.comp_chain)
def _issue(severity: str, line: int, message: str, fix: str) -> dict:
    return {"rule_id": "GF-11", "severity": severity, "line": line,
            "message": message, "fix": fix,
            "category": "variable_lifecycle"}
def _report_del_then_use(frame: _FrameA, ctx: _DelUseContext,
                         augassign_read: bool = False) -> None:
    node = frame.node
    if not isinstance(node, ast.Name):
        return
    scope_key = _del_scope_key(frame, ctx.global_scopes)
    rebinds = ctx.rebinds.get(scope_key, {})
    closure_deletion = _direct_closure_del_timing(
        frame, augassign_read, scope_key, ctx)
    if closure_deletion is not None:
        source_position = closure_deletion.source_position
        if (_direct_closure_rebind_exempt(
                frame, closure_deletion, rebinds, ctx)
                or _shadowed_in_comp(frame)):
            return
    else:
        deletion = _del_use_del_position(
            frame, augassign_read, scope_key, ctx)
        if deletion is None:
            module_deletion = _direct_module_del_timing(
                frame, augassign_read, scope_key, ctx)
            if module_deletion is None:
                return
            del_position = module_deletion.position
            source_position = module_deletion.source_position
            if (_direct_module_rebind_exempt(
                    frame, module_deletion, rebinds, ctx)
                    or _shadowed_in_comp(frame)):
                return
        else:
            del_position, source_position, delete_path = deletion
            if _del_use_exempt(
                    frame, del_position, rebinds, ctx, delete_path):
                return
    ctx.issues.append(_issue(
        "P0", node.lineno,
        f'Variable "{node.id}" deleted at L{source_position[0]} '
        f'but referenced at L{node.lineno}',
        "Remove del or move reference before del"))
@dataclass
class _ModuleRefContext:
    issues: list
    defined_at_module: set
    whitelist: frozenset
    deferred_refs: frozenset[int]
def _report_undefined_name(node: Any, ctx: _ModuleRefContext) -> None:
    if id(node) in ctx.deferred_refs:
        return
    name = node.id
    if name in ctx.defined_at_module or name in ctx.whitelist:
        return
    ctx.issues.append(_issue(
        "P1", getattr(node, "lineno", 0),
        f'Undefined variable: "{name}" referenced but not imported/defined '
        'at module level',
        "Check for typo, or add import/definition"))
def _filter_class_scopes(chain) -> tuple:
    return tuple(_p for _p in chain if _p[1] != 1)
def _body_chain(frame: _FrameA, binds: dict, kind: int) -> tuple:
    return ((binds.get(id(frame.node), frozenset()), kind),
            ) + _filter_class_scopes(frame.chain)
def _scope_frames_a(frame: _FrameA, binds: dict, kind: int) -> tuple:
    node = frame.node
    body_chain = _body_chain(frame, binds, kind)
    return (
        *(_FrameA(kid, frame.chain, frame.comp_chain, frame.path)
          for kid in signature_children(node)),
        *(_FrameA(stmt, body_chain, frame.comp_chain)
          for stmt in node.body),
    )
def _except_frames_a(frame: _FrameA) -> tuple:
    node = frame.node
    alias_chain = ((frozenset({node.name}), 2),) + frame.chain
    head = () if node.type is None else (
        _FrameA(node.type, frame.chain, frame.comp_chain, frame.path),)
    return (
        *head,
        *(_FrameA(stmt, alias_chain, frame.comp_chain, frame.path)
          for stmt in node.body),
    )
def _lambda_frames_a(frame: _FrameA, binds: dict) -> tuple:
    node = frame.node
    body_chain = _body_chain(frame, binds, 0)
    return (
        _FrameA(node.args, frame.chain, frame.comp_chain, frame.path),
        _FrameA(node.body, body_chain, frame.comp_chain),
    )
def _comp_frames_a(frame: _FrameA) -> tuple:
    node = frame.node
    template = _FrameA(node, _filter_class_scopes(frame.chain),
                       frame.comp_chain, frame.path)
    head = _FrameA(node.generators[0].iter, frame.chain, frame.comp_chain,
                   frame.path)
    return (head, *_comp_children_frames(node, template))
def _expand_frames_a(frame: _FrameA, binds: dict) -> tuple | None:
    node = frame.node
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return _scope_frames_a(frame, binds, 0)
    if isinstance(node, ast.Lambda):
        return _lambda_frames_a(frame, binds)
    if isinstance(node, ast.ClassDef):
        return _scope_frames_a(frame, binds, 1)
    if isinstance(node, COMP_SCOPE_NODES):
        return _comp_frames_a(frame)
    if isinstance(node, ast.ExceptHandler) and node.name:
        return _except_frames_a(frame)
    return None
def _walk_scope_frames(root: Any, make_frame, expand_frames, visit_leaf) -> None:
    stack = [make_frame(root)]
    while stack:
        frame = stack.pop()
        frames = expand_frames(frame)
        if frames is not None:
            stack.extend(frames)
            continue
        visit_leaf(frame)
        markers = _child_branch_markers(frame.node)
        stack.extend(
            frame._replace(
                node=child,
                path=(frame.path if markers.get(id(child)) is None
                      else (*frame.path, markers[id(child)])))
            for child in ast.iter_child_nodes(frame.node))
def _handle_del_use_leaf(frame: _FrameA, ctx: _DelUseContext) -> None:
    node = frame.node
    if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
        _report_del_then_use(frame._replace(node=node.target), ctx,
                             augassign_read=True)
    _report_del_then_use(frame, ctx)
def _scan_del_then_use(tree: Any, binds: dict,
                       ctx: _DelUseContext) -> None:
    _walk_scope_frames(
        tree,
        lambda node: _FrameA(node, (), ()),
        lambda frame: _expand_frames_a(frame, binds),
        lambda frame: _handle_del_use_leaf(frame, ctx),
    )
def _without_class_scopes(chain, class_bind_ids: set[int]) -> tuple:
    return tuple(scope for scope in chain if id(scope) not in class_bind_ids)
def _def_class_frames_b(frame: _FrameB, binds: dict,
                        class_bind_ids: set[int]) -> tuple:
    node = frame.node
    signature = tuple(_FrameB(kid, frame.lb_chain, frame.comp_chain)
                      for kid in signature_children(node))
    body_chain = ((binds.get(id(node), frozenset()),)
                  + _without_class_scopes(frame.lb_chain, class_bind_ids))
    return (*signature,
            *(_FrameB(stmt, body_chain, frame.comp_chain)
              for stmt in node.body))
def _except_frames_b(frame: _FrameB) -> tuple:
    node = frame.node
    head = () if node.type is None else (
        _FrameB(node.type, frame.lb_chain, frame.comp_chain),)
    body_chain = ((frozenset({node.name}),) + frame.lb_chain
                  if node.name else frame.lb_chain)
    return (
        *head,
        *(_FrameB(stmt, body_chain, frame.comp_chain)
          for stmt in node.body),
    )
def _lambda_frames_b(frame: _FrameB, binds: dict,
                     class_bind_ids: set[int]) -> tuple:
    node = frame.node
    body_chain = ((binds.get(id(node), frozenset()),)
                  + _without_class_scopes(frame.lb_chain, class_bind_ids))
    return (
        _FrameB(node.args, frame.lb_chain, frame.comp_chain),
        _FrameB(node.body, body_chain, frame.comp_chain),
    )
def _comp_frames_b(frame: _FrameB,
                   class_bind_ids: set[int]) -> tuple:
    node = frame.node
    template = _FrameB(
        node, _without_class_scopes(frame.lb_chain, class_bind_ids),
        frame.comp_chain)
    head = _FrameB(node.generators[0].iter, frame.lb_chain, frame.comp_chain)
    return (head, *_comp_children_frames(node, template))
def _expand_frames_b(frame: _FrameB, binds: dict,
                     class_bind_ids: set[int]) -> tuple | None:
    node = frame.node
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return _def_class_frames_b(frame, binds, class_bind_ids)
    if isinstance(node, ast.Lambda):
        return _lambda_frames_b(frame, binds, class_bind_ids)
    if isinstance(node, ast.ExceptHandler):
        return _except_frames_b(frame)
    if isinstance(node, COMP_SCOPE_NODES):
        return _comp_frames_b(frame, class_bind_ids)
    return None
def _read_reference_name(node: Any) -> Any:
    if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
        return node.target
    if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
        return node
    return None
def _module_ref_name(frame: _FrameB) -> Any:
    candidate = _read_reference_name(frame.node)
    if candidate is None:
        return None
    scopes = (*frame.lb_chain, *frame.comp_chain)
    if any(candidate.id in scope for scope in scopes):
        return None
    return candidate
def _handle_undefined_leaf(frame: _FrameB, ctx: _ModuleRefContext) -> None:
    candidate = _module_ref_name(frame)
    if candidate is not None:
        _report_undefined_name(candidate, ctx)
def _scan_undefined_references(tree: Any, binds: dict,
                               ctx: _ModuleRefContext) -> None:
    class_bind_ids = {
        id(binds[id(node)]) for node in walk_nodes(tree)
        if isinstance(node, ast.ClassDef)
    }
    for node in tree.body:
        _walk_scope_frames(
            node,
            lambda item: _FrameB(item, (), ()),
            lambda frame: _expand_frames_b(
                frame, binds, class_bind_ids),
            lambda frame: _handle_undefined_leaf(frame, ctx),
        )
def _has_runtime_star_import(tree) -> bool:
    return any(is_star_import(node)
               for node, under_tc in iter_module_level_nodes_tc(
                   tree, include_class_body=False)
               if not under_tc)
def _gf11_name_whitelist() -> frozenset:
    return BUILTIN_NAMES | PY_STDLIB_HINTS | {
        "__name__", "__file__", "__doc__", "__annotations__", "__all__",
        "__version__",
        "__author__", "__builtins__", "__spec__", "__loader__", "__package__",
        "__cached__", "__path__", "__class__",
    }
@dataclass
class _LifecycleContext:
    defined: set
    type_param_refs: frozenset[int] = frozenset()
    type_checking_defined: set = field(default_factory=set)
    non_runtime_refs: set[int] = field(default_factory=set)
def _gf11_defined_assign_targets(node: ast.Assign, defined: set) -> None:
    for target in node.targets:
        if isinstance(target, ast.Name):
            defined.add(target.id)
def _gf11_defined_import_targets(node: ast.Import | ast.ImportFrom,
                                 defined: set) -> None:
    defined.update(_iter_import_bindings(node))
def _gf11_defined_ann_target(node: ast.AnnAssign, defined: set) -> None:
    if node.value is not None and isinstance(node.target, ast.Name):
        defined.add(node.target.id)
def _gf11_defined_def_name(node: Any, defined: set) -> None:
    defined.add(node.name)
_GF11_DEFINED_HANDLERS = (
    (ast.Assign, _gf11_defined_assign_targets),
    (ast.AnnAssign, _gf11_defined_ann_target),
    ((ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef),
     _gf11_defined_def_name),
    ((ast.Import, ast.ImportFrom), _gf11_defined_import_targets),
)
def _gf11_defined_targets(node: Any, defined: set, func_depth: int) -> None:
    if func_depth > 0:
        return
    if isinstance(node, ast.NamedExpr) and isinstance(node.target, ast.Name):
        defined.add(node.target.id)
        return
    for node_types, collect in _GF11_DEFINED_HANDLERS:
        if isinstance(node, node_types):
            collect(node, defined)
            return
def _gf11_module_binds(node: Any, func_depth: int, in_comp: bool,
                       defined: set) -> None:
    if func_depth > 0:
        return
    if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
        if not in_comp:
            defined.add(node.id)
        return
    if isinstance(node, ast.ExceptHandler):
        if node.name:
            defined.add(node.name)
        return
    if isinstance(node, ast.Match):
        for case in node.cases:
            defined.update(iter_pattern_capture_names(case.pattern))
def _push_ann_annotation_only(stack: list, node: ast.AnnAssign,
                              func_depth: int, in_comp: bool,
                              mode: str) -> None:
    if node.annotation is not None:
        stack.append((node.annotation, func_depth, in_comp, mode))
def _push_augassign_parts(stack: list, node: ast.AugAssign,
                          func_depth: int, in_comp: bool,
                          mode: str) -> None:
    if func_depth > 0:
        stack.append((node.target, func_depth, in_comp, mode))
    stack.append((node.value, func_depth, in_comp, mode))
def _push_sig_body_split(stack: list, node, func_depth: int,
                         in_comp: bool, mode: str) -> None:
    stack.extend((child, func_depth, in_comp, mode)
                 for child in signature_children(node))
    body = node.body if isinstance(node.body, list) else [node.body]
    stack.extend((stmt, func_depth + 1, in_comp, mode) for stmt in body)
def _handle_special_subtrees(
    stack: list, node: ast.AST, func_depth: int, in_comp: bool,
    mode: str,
) -> bool:
    if isinstance(node, ast.AnnAssign) and node.value is None:
        _push_ann_annotation_only(stack, node, func_depth, in_comp, mode)
        return True
    if isinstance(node, ast.AugAssign):
        _push_augassign_parts(stack, node, func_depth, in_comp, mode)
        return True
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)):
        _push_sig_body_split(stack, node, func_depth, in_comp, mode)
        return True
    return False
def _gf11_type_param_names(node: Any) -> frozenset[str]:
    return frozenset(
        param.name for param in getattr(node, "type_params", None) or ()
        if isinstance(param, _TYPE_PARAM_TYPES)
        and isinstance(getattr(param, "name", None), str) and param.name)
def _gf11_arg_annotations(node: Any) -> list:
    args = node.args
    return [arg.annotation for arg in (
        *args.posonlyargs, *args.args, *args.kwonlyargs,
        args.vararg, args.kwarg)
        if arg is not None and arg.annotation is not None]
def _gf11_type_param_roots(node: Any) -> list:
    roots = list(getattr(node, "type_params", None) or ())
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        roots.extend(_gf11_arg_annotations(node))
        if node.returns is not None:
            roots.append(node.returns)
        roots.extend(node.body)
    elif isinstance(node, ast.ClassDef):
        roots.extend(node.bases)
        roots.extend(keyword.value for keyword in node.keywords)
        roots.extend(node.body)
    return roots
def _gf11_reference_ids(roots: list, names: frozenset[str] | None = None) -> set[int]:
    return {id(child) for root in roots if root is not None
            for child in walk_nodes(root)
            if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Load)
            and (names is None or child.id in names)}
def _gf11_type_param_reference_ids(tree: Any) -> frozenset[int]:
    refs: set[int] = set()
    for node in walk_nodes(tree):
        names = _gf11_type_param_names(node)
        if names:
            refs.update(_gf11_reference_ids(_gf11_type_param_roots(node), names))
    return frozenset(refs)
def _gf11_annotation_reference_ids(
    tree: Any, names: frozenset[str] | None = None,
) -> frozenset[int]:
    postponed = module_postpones_annotations(tree)
    parents = {id(child): node for node in walk_nodes(tree)
               for child in ast.iter_child_nodes(node)}
    roots: list = []
    for node in walk_nodes(tree):
        if TYPE_ALIAS_NODES and isinstance(node, TYPE_ALIAS_NODES):
            roots.append(node.value)
        if isinstance(node, _TYPE_PARAM_TYPES):
            roots.append(node)
        if isinstance(node, ast.AnnAssign):
            parent = parents.get(id(node))
            while parent is not None and not isinstance(parent, _GF11_SCOPE_TYPES):
                parent = parents.get(id(parent))
            if postponed or isinstance(parent, (ast.FunctionDef,
                                                ast.AsyncFunctionDef)):
                roots.append(node.annotation)
            continue
        if not postponed:
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            roots.extend(_gf11_arg_annotations(node))
            returns = getattr(node, "returns", None)
            if returns is not None:
                roots.append(returns)
    return frozenset(_gf11_reference_ids(roots, names))
def _gf11_absorb_node(node: Any, func_depth: int, in_comp: bool,
                      ctx: _LifecycleContext, stack: list, mode: str) -> bool:
    if mode != "invisible":
        defined = (ctx.type_checking_defined
                   if mode == "type_only" else ctx.defined)
        _gf11_defined_targets(node, defined, func_depth)
        _gf11_module_binds(node, func_depth, in_comp, defined)
    return _handle_special_subtrees(
        stack, node, func_depth, in_comp, mode)
_GF11_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef,
                     ast.ClassDef, ast.Lambda)
def _gf11_scope_body(scope: Any) -> list:
    body = getattr(scope, "body", None)
    if body is None:
        return []
    return list(body) if isinstance(body, list) else [body]
def _gf11_scope_binding_stores(
        scope: Any, declaration_type: type[ast.AST]) -> tuple[set, set, list]:
    declared: set = set()
    nested: list = []
    body = _gf11_scope_body(scope)
    stack = list(body)
    while stack:
        node = stack.pop()
        if isinstance(node, _GF11_SCOPE_TYPES):
            nested.append(node)
            stack.extend(signature_children(node))
            continue
        if isinstance(node, declaration_type):
            declared.update(node.names)
            continue
        stack.extend(ast.iter_child_nodes(node))
    stores = set(_statement_rebind_events(body))
    return declared, stores, nested
def _gf11_scopes_with_declarations(tree: Any, declaration_type: type[ast.AST]):
    pending = [tree]
    while pending:
        scope = pending.pop()
        declared, _stores, nested = _gf11_scope_binding_stores(
            scope, declaration_type)
        if scope is not tree and declared:
            yield scope, declared
        pending.extend(nested)
def _gf11_scope_parents(tree: Any) -> dict[int, Any]:
    parents: dict[int, Any] = {}
    stack = [(tree, None)]
    while stack:
        node, parent = stack.pop()
        if isinstance(node, _GF11_SCOPE_TYPES):
            parents[id(node)] = parent if parent is not None else tree
            parent = node
        stack.extend((child, parent) for child in ast.iter_child_nodes(node))
    return parents
def _gf11_nonlocal_owner(scope: Any, name: str, parents: dict,
                         binds: dict) -> Any:
    candidate = parents.get(id(scope))
    while candidate is not None:
        if (not isinstance(candidate, (ast.ClassDef, ast.Module))
                and name in binds.get(id(candidate), ())):
            return candidate
        candidate = parents.get(id(candidate))
    return None
def _gf11_nonlocal_scoped_events(tree: Any, binds: dict, collector) -> dict:
    parents = _gf11_scope_parents(tree)
    merged: dict[int, dict[str, list]] = {}
    for scope, declared in _gf11_scopes_with_declarations(tree, ast.Nonlocal):
        scoped = collector(_gf11_scope_body(scope))
        for name, values in scoped.items():
            if name not in declared:
                continue
            owner = _gf11_nonlocal_owner(scope, name, parents, binds)
            if owner is None:
                continue
            scope_key = id(binds[id(owner)])
            origin = _gf11_execution_scope_key(scope, parents)
            scoped_values = [value._replace(origin=origin) for value in values]
            merged.setdefault(scope_key, {}).setdefault(
                name, []).extend(scoped_values)
    return merged
def _merge_scoped_events(target: dict, incoming: dict) -> None:
    for scope_key, named_events in incoming.items():
        for name, values in named_events.items():
            target.setdefault(scope_key, {}).setdefault(
                name, []).extend(values)
def _gf11_global_rebind_events(tree: Any) -> dict:
    rebinds: dict[str, list[_RebindEvent]] = {}
    parents = _gf11_scope_parents(tree)
    for scope, declared in _gf11_scopes_with_declarations(tree, ast.Global):
        scoped = _statement_rebind_events(_gf11_scope_body(scope))
        for name, events in scoped.items():
            if name in declared:
                origin = _gf11_execution_scope_key(scope, parents)
                rebinds.setdefault(name, []).extend(
                    event._replace(origin=origin) for event in events)
    return rebinds
def _gf11_global_del_targets(tree: Any) -> dict:
    targets: dict[str, list[_DeleteEvent]] = {}
    parents = _gf11_scope_parents(tree)
    for scope, declared in _gf11_scopes_with_declarations(tree, ast.Global):
        scoped: dict[str, list[_DeleteEvent]] = {}
        collect_module_del_targets(_gf11_scope_body(scope), scoped)
        for name, positions in scoped.items():
            if name in declared:
                origin = _gf11_execution_scope_key(scope, parents)
                targets.setdefault(name, []).extend(
                    event._replace(origin=origin) for event in positions)
    return targets
def _gf11_global_bindings(tree: Any) -> set:
    bindings: set = set()
    pending = [tree]
    while pending:
        declared, stores, nested = _gf11_scope_binding_stores(
            pending.pop(), ast.Global)
        bindings.update(declared & stores)
        pending.extend(nested)
    return bindings
def _gf11_scope_key(scope: Any) -> int | None:
    return None if isinstance(scope, ast.Module) else id(scope)
def _gf11_execution_scope_key(scope: Any, parents: dict) -> int | None:
    while isinstance(scope, ast.ClassDef):
        scope = parents.get(id(scope))
    return _gf11_scope_key(scope) if scope is not None else None
def _gf11_direct_function_definitions(scope: Any) -> dict:
    _declared, _stores, nested = _gf11_scope_binding_stores(scope, ast.Global)
    definitions: dict[str, list[Any]] = {}
    for node in nested:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            definitions.setdefault(node.name, []).append(node)
    stack = list(_gf11_scope_body(scope))
    while stack:
        node = stack.pop()
        if isinstance(node, _GF11_SCOPE_TYPES):
            stack.extend(signature_children(node))
            continue
        if (isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr))
                and isinstance(node.value, ast.Lambda)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            for target in targets:
                if isinstance(target, ast.Name):
                    definitions.setdefault(target.id, []).append(node.value)
        stack.extend(ast.iter_child_nodes(node))
    return definitions
def _gf11_visible_functions(scope: Any, name: str, parents: dict,
                            definitions: dict) -> tuple:
    current = scope
    while current is not None:
        if not (isinstance(current, ast.ClassDef) and current is not scope):
            found = definitions.get(_gf11_scope_key(current), {}).get(name)
            if found:
                return tuple(found)
        current = parents.get(id(current))
    return ()
def _gf11_activation_sites(tree: Any) -> dict:
    scopes = [tree, *(node for node in walk_nodes(tree)
                      if isinstance(node, _GF11_SCOPE_TYPES))]
    parents = _gf11_scope_parents(tree)
    definitions = {_gf11_scope_key(scope):
                   _gf11_direct_function_definitions(scope) for scope in scopes}
    direct: list[_Activation] = []
    for scope in scopes:
        calls: list[tuple[ast.Call, int | None]] = []
        alias_pairs: list[tuple[str, str]] = []
        alias_writes: list[tuple[
            str, str | None, tuple[int, int], bool]] = []
        awaited_calls: set[int] = set()
        stack = [(stmt, 0) for stmt in _gf11_scope_body(scope)]
        while stack:
            node, direct_block = stack.pop()
            if isinstance(node, _GF11_SCOPE_TYPES):
                stack.extend((child, direct_block)
                             for child in signature_children(node))
                continue
            if isinstance(node, ast.Await) and isinstance(node.value, ast.Call):
                awaited_calls.add(id(node.value))
            if isinstance(node, ast.Call):
                calls.append((node, direct_block))
            if (direct_block is not None
                    and isinstance(node, (ast.Assign, ast.AnnAssign))
                    and node.value is not None):
                targets = (node.targets if isinstance(node, ast.Assign)
                           else [node.target])
                source_name = (node.value.id
                               if isinstance(node.value, ast.Name) else None)
                alias_writes.extend(
                    (target.id, source_name, _end_position(node),
                     isinstance(node.value, ast.Lambda))
                    for target in targets if isinstance(target, ast.Name))
            if (isinstance(node, ast.Assign)
                    and isinstance(node.value, ast.Name)):
                alias_pairs.extend((target.id, node.value.id)
                                   for target in node.targets
                                   if isinstance(target, ast.Name))
            elif (isinstance(node, (ast.AnnAssign, ast.NamedExpr))
                  and node.value is not None
                  and isinstance(node.value, ast.Name)
                  and isinstance(node.target, ast.Name)):
                alias_pairs.append((node.target.id, node.value.id))
            stack.extend(
                (child, None if isinstance(
                    child, (ast.stmt, ast.ExceptHandler)) else direct_block)
                for child in ast.iter_child_nodes(node))
        aliases: dict[str, list[Any]] = {}
        changed = True
        while changed:
            changed = False
            for alias, name in alias_pairs:
                targets = [*_gf11_visible_functions(
                    scope, name, parents, definitions), *aliases.get(name, ())]
                known = aliases.setdefault(alias, [])
                known_ids = {id(target) for target in known}
                for target in targets:
                    if id(target) not in known_ids:
                        known.append(target)
                        known_ids.add(id(target))
                        changed = True
        def call_targets(
            name: str, call_position: tuple[int, int],
            direct_block: int | None,
            _seen: frozenset[str] = frozenset(), *,
            _scope=scope, _alias_writes=alias_writes, _aliases=aliases,
        ) -> list[Any]:
            if name in _seen:
                return []
            if direct_block is not None:
                writes = [write for write in _alias_writes
                          if write[0] == name and write[2] < call_position]
                if writes:
                    _alias, source, _position, allow_defined = max(
                        writes, key=lambda write: write[2])
                    if source is None:
                        return (list(_gf11_visible_functions(
                            _scope, name, parents, definitions))
                            if allow_defined else [])
                    return call_targets(
                        source, call_position, direct_block, _seen | {name})
            return [*_gf11_visible_functions(
                _scope, name, parents, definitions), *_aliases.get(name, ())]
        for call, direct_block in calls:
            func = call.func
            if isinstance(func, ast.Lambda):
                targets = [func]
            else:
                if isinstance(func, ast.NamedExpr):
                    func = func.target
                if not isinstance(func, ast.Name):
                    continue
                name = func.id
                targets = call_targets(
                    name, _end_position(call), direct_block)
            emitted: set[int] = set()
            for target in targets:
                if (isinstance(target, ast.AsyncFunctionDef)
                        and id(call) not in awaited_calls):
                    continue
                if id(target) in emitted:
                    continue
                emitted.add(id(target))
                direct.append(_Activation(
                    _end_position(call),
                    _gf11_execution_scope_key(scope, parents), id(target)))
    activations: dict[int, list[_Activation]] = {}
    incoming: dict[int, list[_Activation]] = {}
    seen = {(site.callee, site.caller, site.position) for site in direct}
    for site in direct:
        activations.setdefault(site.callee, []).append(site)
        incoming.setdefault(site.callee, []).append(site)
    queue = list(direct)
    index = 0
    while index < len(queue):
        site = queue[index]
        index += 1
        for parent in incoming.get(site.caller, ()):
            key = (site.callee, parent.caller, parent.position)
            if key in seen:
                continue
            seen.add(key)
            propagated = _Activation(
                parent.position, parent.caller, site.callee, direct=False)
            activations.setdefault(site.callee, []).append(propagated)
            queue.append(propagated)
    return activations
def _gf11_type_checking_branch_visibility(
    test: ast.expr, typing_aliases: set[str], type_checking_names: set[str] | None,
) -> bool | None:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        inner = _gf11_type_checking_branch_visibility(
            test.operand, typing_aliases, type_checking_names)
        return None if inner is None else not inner
    return (False if is_type_checking_guard(
        test, typing_aliases, type_checking_names) else None)
def _gf11_if_branch_modes(
    node: ast.If, parent_mode: str, typing_aliases: set[str],
    type_checking_names: set[str] | None,
) -> tuple[str, str]:
    if parent_mode != "runtime":
        return parent_mode, parent_mode
    visible = (bool(node.test.value) if isinstance(node.test, ast.Constant)
               else import_time_branch_visibility(
                   node.test, typing_aliases, type_checking_names))
    type_visible = _gf11_type_checking_branch_visibility(
        node.test, typing_aliases, type_checking_names)
    def branch_mode(branch_visible, branch_type_visible) -> str:
        if branch_type_visible is False:
            return "type_only"
        if branch_type_visible is True:
            return "runtime"
        return "invisible" if branch_visible is False else "runtime"
    else_visible = None if visible is None else not visible
    else_type_visible = (
        None if type_visible is None else not type_visible)
    return (branch_mode(visible, type_visible),
            branch_mode(else_visible, else_type_visible))
def collect_variable_lifecycle_context(tree: Any) -> _LifecycleContext:
    ctx = _LifecycleContext(defined=set())
    typing_aliases = typing_guard_aliases(tree)
    type_checking_names = typing_type_checking_names(tree) or None
    stack = [(tree, 0, False, "runtime")]
    while stack:
        node, func_depth, in_comp, mode = stack.pop()
        if (mode != "runtime" and isinstance(node, ast.Name)
                and isinstance(node.ctx, ast.Load)):
            ctx.non_runtime_refs.add(id(node))
        if _gf11_absorb_node(
                node, func_depth, in_comp, ctx, stack, mode):
            continue
        if isinstance(node, ast.If) and func_depth == 0:
            body_mode, else_mode = _gf11_if_branch_modes(
                node, mode, typing_aliases, type_checking_names)
            stack.append((node.test, func_depth, in_comp, mode))
            stack.extend((stmt, func_depth, in_comp, body_mode)
                         for stmt in node.body)
            stack.extend((stmt, func_depth, in_comp, else_mode)
                         for stmt in node.orelse)
            continue
        _child_in_comp = in_comp or isinstance(node, COMP_SCOPE_NODES)
        for child in ast.iter_child_nodes(node):
            stack.append((child, func_depth, _child_in_comp, mode))
    ctx.defined.update(_gf11_global_bindings(tree))
    ctx.type_param_refs = _gf11_type_param_reference_ids(tree)
    return ctx
def _del_binding_events(body: list) -> dict:
    events: dict[str, list[tuple[int, int]]] = {}
    collect_module_del_targets(body, events)
    return events
def _scoped_del_targets(tree: Any, binds: dict) -> dict:
    module: dict[str, list[tuple[int, int]]] = {}
    collect_module_del_targets(tree.body, module)
    for name, positions in _gf11_global_del_targets(tree).items():
        module.setdefault(name, []).extend(positions)
    targets = {None: module}
    for scope in walk_nodes(tree):
        if not isinstance(scope, _GF11_SCOPE_TYPES):
            continue
        scoped: dict[str, list[tuple[int, int]]] = {}
        collect_module_del_targets(_gf11_scope_body(scope), scoped)
        targets[id(binds[id(scope)])] = scoped
    _merge_scoped_events(targets, _gf11_nonlocal_scoped_events(
        tree, binds, _del_binding_events))
    return targets
def _scoped_rebind_events(tree: Any, binds: dict) -> dict:
    events = {None: module_rebind_events(tree)}
    for scope in walk_nodes(tree):
        if isinstance(scope, _GF11_SCOPE_TYPES):
            events[id(binds[id(scope)])] = _statement_rebind_events(
                _gf11_scope_body(scope))
    _merge_scoped_events(events, _gf11_nonlocal_scoped_events(
        tree, binds, _statement_rebind_events))
    return events
def check_variable_lifecycle(code: Any, tree=None) -> Any:
    issues = []
    tree = guard_tree(code, tree)
    if tree is None:
        return issues
    _prepare_symbol_branch_visibility(tree)
    binds = func_local_bind_map(tree)
    del_targets = _scoped_del_targets(tree, binds)
    if any(del_targets.values()):
        ctx = _DelUseContext(
            del_targets=del_targets,
            rebinds=_scoped_rebind_events(tree, binds),
            global_scopes={
                id(binds[id(scope)]): names
                for scope, names in _gf11_scopes_with_declarations(
                    tree, ast.Global)
            },
            activations=_gf11_activation_sites(tree),
            scope_owners={
                id(binds[id(scope)]): id(scope)
                for scope in walk_nodes(tree)
                if isinstance(scope, _GF11_SCOPE_TYPES)
            },
            issues=issues,
        )
        _scan_del_then_use(tree, binds, ctx)
    if _has_runtime_star_import(tree):
        return issues
    lifecycle = collect_variable_lifecycle_context(tree)
    annotation_refs = _gf11_annotation_reference_ids(tree)
    ctx_b = _ModuleRefContext(
        issues=issues,
        defined_at_module=lifecycle.defined,
        whitelist=_gf11_name_whitelist(),
        deferred_refs=(lifecycle.type_param_refs | annotation_refs |
                       frozenset(lifecycle.non_runtime_refs)),
    )
    _scan_undefined_references(tree, binds, ctx_b)
    return issues
def wiring_declarations() -> dict:
    return {"catalogs": {
        "early_channels": {"GF": (10, detect_all, False)},
        "diag4_direct": {"RD-26": check_RD26},
    }}

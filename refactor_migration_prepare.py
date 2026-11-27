from __future__ import annotations

import ast
import copy
import logging
import os
import re
import symtable
from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Any, ClassVar

from jwsgj.build_module_topology import ZeroConsumerChecker, normalize_module_name
from jwsgj.diag_shared_ast_bindings import (
    enclosing_scope_load_names,
    exec_scope_declarations,
    import_bound_names,
    import_stmt_binds,
    module_scope_binds,
    symtable_global_refs,
)
from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_NAMES,
    PY_STDLIB_HINTS,
    build_parent_map,
    is_type_checking_guard,
    iter_module_level_stmts,
    parse_source_tree,
    symbol_start_line,
)
from jwsgj.diag_shared_source_core import (
    ast_split_lines,
    read_source,
    read_source_with_fingerprint,
)
from jwsgj.diag_types_defs import (
    ContractViolationError,
)
from jwsgj.diag_types_vocab import (
    INPLACE_MUTATING_METHODS,
    PARSE_DEGRADE_EXC,
    SENSITIVE_NAME_KEYWORDS,
    SHARED_BASE_CONSUMER_THRESHOLD,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    collect_migration_py_files,
    strip_stale_coding_declaration,
)

_log = logging.getLogger(__name__)
def immutable(spec: str) -> Callable:
    def decorator(func: Callable) -> Callable:
        specs = getattr(func, "_immutability_specs", None)
        if specs is None:
            specs = []
            func._immutability_specs = specs  # type: ignore[attr-defined]
        specs.append(spec)
        return func
    return decorator
@dataclass
class MergeCleanupPlan:
    merged_files: list[str] = field(default_factory=list)
    target_file: str = ""
    deletable_stubs: list[str] = field(default_factory=list)
    stale_references: list[str] = field(default_factory=list)
    orphans_kept: list[str] = field(default_factory=list)
    stats: dict[str, Any] = field(default_factory=dict)
    def to_dict(self) -> dict[str, Any]:
        return {
            "merged_files": self.merged_files,
            "target_file": self.target_file,
            "deletable_stubs": self.deletable_stubs,
            "orphans_kept": self.orphans_kept,
            "stale_references": self.stale_references,
            "stats": self.stats,
        }
def _source_eol(source: str) -> str:
    if "\r\n" in source:
        return "\r\n"
    if "\r" in source and "\n" not in source:
        return "\r"
    return "\n"
def _path_text(value: object) -> str:
    try:
        text = os.fspath(value)
    except TypeError:  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return ""
    return os.fsdecode(text) if isinstance(text, bytes) else text
def _path_identity(path: object) -> str:
    return os.path.normcase(os.path.realpath(os.path.abspath(_path_text(path))))
def _as_merged_file_list(merged_files: object) -> list[str]:
    if not isinstance(merged_files, (list, tuple)):
        _log.warning("[PMC] merged_files 非序列形态 %s，按空清单处理",
                      type(merged_files).__name__)
        return []
    out: list[str] = []
    for mf in merged_files:
        try:
            text = os.fsdecode(mf)
        except TypeError:
            _log.warning("[PMC] merged_files 含非路径元素 %r，已跳过", mf)
            continue
        if not text.strip():
            _log.warning("[PMC] merged_files 含空路径元素，已跳过")
            continue
        out.append(text)
    return out
def _cleanup_stats(total_merged: int, deletable: list[str],
                   orphans_kept: int = 0, error: str = "") -> dict[str, Any]:
    stats = {
        'total_merged': total_merged,
        'deletable': len(deletable),
        'orphans_kept': orphans_kept,
        'safe_to_delete_ratio': round(
            len(deletable) / max(total_merged, 1), 2),
    }
    if error:
        stats['error'] = error
    return stats
def _report_section(title: str, items: list[str],
                    limit: int | None = None) -> list[str]:
    if not items:
        return []
    shown = items[:limit] if limit is not None else items
    lines = ["", title]
    lines.extend(f"  - {s}" for s in shown)
    if limit is not None and len(items) > limit:
        lines.append(f"  ...（共 {len(items)} 个，仅列前 {limit}）")
    return lines
_BUCKET_FIELDS: dict[str, str] = {
    "deletable": "deletable_stubs",
    "orphan": "orphans_kept",
    "stale": "stale_references",
}
class PostMergeCleaner:
    def __init__(self, skill_dir: str) -> None:
        raw = _path_text(skill_dir)
        self.skill_dir = os.path.abspath(raw) if raw else ""
    def plan_cleanup(self, merged_files: list, target_file: str) -> MergeCleanupPlan:
        merged_files = _as_merged_file_list(merged_files)
        target_file = _path_text(target_file)
        if not self.skill_dir:
            _log.warning("[PMC] skill_dir 为空，拒绝扫描（返回空计划）")
            plan = MergeCleanupPlan(merged_files=merged_files,
                                    target_file=target_file)
            plan.stats = _cleanup_stats(
                0, [], error="skill_dir 为空，拒绝扫描")
            return plan
        if not target_file:
            _log.warning("[PMC] target_file 为空，不做目标自身排除（分类照常）")
        target_path = (target_file if os.path.isabs(target_file)
                       else os.path.join(self.skill_dir, target_file))
        target_identity = _path_identity(target_path)
        abs_merged: list[str] = []
        seen: set[str] = set()
        for mf in merged_files:
            abs_mf = (mf if os.path.isabs(mf)
                      else os.path.join(self.skill_dir, mf))
            identity = _path_identity(abs_mf)
            if identity == target_identity or identity in seen:
                continue
            seen.add(identity)
            abs_merged.append(abs_mf)
        plan = MergeCleanupPlan(merged_files=abs_merged, target_file=target_file)
        try:
            checker = get_zero_consumer_checker(self.skill_dir)
        except Exception as e:  # noqa: BLE001 - 刻意降级：扫描失败返回空计划
            _log.warning("[PMC] 零消费者扫描跳过 %s: %s", self.skill_dir, e)
            plan.stats = _cleanup_stats(
                len(abs_merged), [], error=str(e)[:200])
            return plan
        if not checker.scan_complete:
            error = "零消费者消费图不完整，拒绝生成可删除计划"
            _log.warning("[PMC] %s: %s", self.skill_dir, error)
            plan.stats = _cleanup_stats(
                len(abs_merged), [], error=error)
            return plan
        self._classify_into_buckets(plan, checker)
        plan.stats = _cleanup_stats(
            len(abs_merged), plan.deletable_stubs,
            orphans_kept=len(plan.orphans_kept))
        return plan
    def _classify_into_buckets(self, plan: MergeCleanupPlan,
                               checker: ZeroConsumerChecker) -> None:
        for mf in plan.merged_files:
            bucket, rel = self._classify_merged_file(mf, checker)
            attr = _BUCKET_FIELDS.get(bucket)
            if rel is None or attr is None:
                continue
            getattr(plan, attr).append(rel)
    def _classify_merged_file(
        self, mf: str, checker: ZeroConsumerChecker,
    ) -> tuple[str, str | None]:
        if not os.path.exists(mf):
            return ("skip", None)
        rel, outside = self._in_scope_rel(mf)
        if outside is not None:
            return (outside, rel)
        consumers = checker.get_module_consumers(normalize_module_name(rel))
        if consumers:
            _log.info("[PMC] 跳过 %s: 仍有 %d 消费者", rel, len(consumers))
            return ("stale", rel)
        source = self._read_merged_source(mf)
        if source is None:
            return ("orphan", rel)
        return self._stub_bucket(rel, source)
    def _in_scope_rel(self, mf: str) -> tuple[str, str | None]:
        try:
            rel = os.path.relpath(
                os.path.realpath(os.path.abspath(mf)),
                os.path.realpath(os.path.abspath(self.skill_dir)))
        except ValueError as _e:
            log_swallowed(
                __name__, _e,
                context=f'_in_scope_rel:{type(_e).__name__}')
            return str(mf), "orphan"
        if not rel or rel == ".." or rel.startswith(".." + os.sep):
            _log.warning("[PMC] 项目目录外文件，保守保留: %s", mf)
            return (rel.replace("\\", "/") if rel else str(mf)), "orphan"
        return rel.replace("\\", "/"), None
    def _read_merged_source(self, mf: str) -> str | None:
        source, _fingerprint = read_source_with_fingerprint(mf)
        if source is None:
            _log.warning("[PMC] 读取失败 %s", mf)
        return source
    def _stub_bucket(self, rel: str, source: str) -> tuple[str, str]:
        is_stub, stub_target = ZeroConsumerChecker.is_pure_import_stub(source)
        if is_stub:
            _log.info("[PMC] 可删除死桩: %s -> %s", rel, stub_target)
            return ("deletable", rel)
        _log.info("[PMC] 保留孤儿工具: %s (含业务逻辑)", rel)
        return ("orphan", rel)
    def generate_report(self, plan: MergeCleanupPlan) -> str:
        lines = [
            "=" * 60,
            "合并后清理报告（仅规划，不自动执行）",
            "=" * 60,
            f"合并源文件: {len(plan.merged_files)}",
            f"可安全删除: {len(plan.deletable_stubs)}",
            f"保留(有业务逻辑): {len(plan.orphans_kept)}",
        ]
        lines += _report_section("可删除的死桩文件:", plan.deletable_stubs)
        lines += _report_section(
            "保留的孤儿工具(含业务逻辑):", plan.orphans_kept)
        lines += _report_section(
            "仍有消费者的旧模块(勿删，需更新导入):",
            plan.stale_references, limit=10)
        lines += ["", "=" * 60]
        return "\n".join(lines)
def plan_post_merge_cleanup(skill_dir: str, merged_files: list,
                            target_file: str) -> dict:
    cleaner = PostMergeCleaner(skill_dir)
    plan = cleaner.plan_cleanup(merged_files, target_file)
    return {
        "plan": plan.to_dict(),
        "report": cleaner.generate_report(plan),
    }
def _as_text_list(value: Any) -> list:
    if isinstance(value, str):
        return [value]
    if isinstance(value, (list, tuple)):
        return list(value)
    if value is None:
        return []
    _log.warning("合并装配: 序列载荷非 list/tuple(%s)，按空处理",
                 type(value).__name__)
    return []
def _import_section_text(items: list) -> str:
    lines: list[str] = []
    for item in items:
        if not isinstance(item, str):
            _log.warning("合并装配: 导入片段非 str(%s)，已跳过",
                         type(item).__name__)
            continue
        text = item.rstrip("\r\n")
        if text.strip():
            lines.append(text)
    return "\n".join(lines) + "\n" if lines else ""
def assemble_merged_source(parts: Any) -> str:
    uniq_imports = (list(dict.fromkeys(_as_text_list(parts.future_imports)))
                    + list(dict.fromkeys(_as_text_list(parts.imports))))
    sections: list[str] = []
    import_text = _import_section_text(uniq_imports)
    if import_text:
        sections.append(import_text)
    sections.extend(
        b for b in _as_text_list(parts.bodies)
        if isinstance(b, str) and b.strip())
    # 单源合并把原 __all__ 声明原位保留在正文（exports_in_body），
    # 再生成一份折叠声明只会得到等值的重复赋值。
    if not getattr(parts, "exports_in_body", False):
        sections.extend(_export_sections(
            parts.all_exports,
            declared=bool(getattr(parts, "exports_by_file", None))))
    merged = "\n\n".join(sections)
    merged = strip_stale_coding_declaration(merged)
    if not merged.endswith("\n"):
        merged += "\n"
    return merged
def _export_sections(all_exports: list, declared: bool = False) -> list[str]:
    exports = _as_text_list(all_exports)
    if not exports and not declared:
        return []
    ordered = list(dict.fromkeys(exports))
    return [f"__all__ = [{', '.join(repr(x) for x in ordered)}]"]
def prepare_migrate_in(source_path, target_path,
                       safe_syms: list[str]) -> tuple[list, list]:
    source_text = _path_text(source_path)
    target_text = _path_text(target_path)
    if not source_text:
        raise OSError(f"源文件路径形态非法: {source_path!r}")
    if not target_text:
        raise OSError(f"目标文件路径形态非法: {target_path!r}")
    src_code, _src_fp_meta = read_source_with_fingerprint(source_text)
    if src_code is None:
        raise OSError(f"读取源文件失败: {source_text}")
    tgt_code, _tgt_fp_meta = read_source_with_fingerprint(target_text)
    if tgt_code is None:
        raise OSError(f"读取目标文件失败: {target_text}")
    candidates = [
        MigrationCandidate(
            symbol=sym, source_file=source_text,
            target_file=target_text)
        for sym in safe_syms]
    previews = batch_migrate_in(
        candidates, {source_text: src_code}, tgt_code)
    return candidates, previews
@dataclass
class ConsumptionEntry:
    source_file: str
    target_module: str
    symbol: str
    lineno: int = 0
    imported_name: str = ""
@dataclass
class MigrationCandidate:
    symbol: str
    source_file: str
    target_file: str
    priority: str = ""
    consumer_count: int = 0
    lineno: int = 0
    reason: str = ""
@dataclass
class MigrationVerdict:
    action: str
    priority: str = ""
    reason: str = ""
    consumer_count: int = 0
@dataclass
class MigrateInResult:
    success: bool
    symbol: str = ""
    target_code: str = ""
    source_code: str = ""
    reason: str = ""
    source_file: str = ""
    target_file: str = ""
    base_target_code: str = ""
_HUB_SYMBOL_PATTERNS = (
    "register", "dispatch", "router", "factory", "manager",
    "registry", "scheduler", "coordinator", "orchestrator",
)
def _toplevel_defs(tree) -> list:
    return [node for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef))]
def _parse_module_file(fp: str, cache: Any):
    filepath = _path_text(fp)
    if not filepath:
        _log.warning("模块文件路径形态非法，已跳过: %r", fp)
        return None
    if cache is not None:
        try:
            tree = cache.get_ast(filepath)
        except Exception as _e:  # noqa: BLE001 — 缓存失败回退直读
            log_swallowed(__name__, _e,
                          context=f"_parse_module_file:{type(_e).__name__}")
            tree = None
        if isinstance(tree, ast.Module):
            return tree
    source = read_source(filepath)
    if source is None:
        _log.debug("文件读取失败（跳过该文件）: %s", filepath)
        return None
    return parse_source_tree(source, filepath)
def _definition_index(module_symbols: dict[str, list[str]],
                      *, normalized: bool) -> dict[str, list[str]]:
    index: dict[str, list[str]] = {}
    for sfp, syms in module_symbols.items():
        key = norm_cache_key(sfp) if normalized else sfp
        for sym in syms:
            source_files = index.setdefault(sym, [])
            if key not in source_files:
                source_files.append(key)
    return index
def _module_definition_match(source_fp: str, target_module: str) -> bool:
    module_parts = tuple(part for part in target_module.split(".") if part)
    if not module_parts:
        return False
    module_path = os.path.join(*module_parts)
    source_path = os.path.normcase(os.path.abspath(source_fp))
    suffixes = (f"{module_path}.py", os.path.join(module_path, "__init__.py"))
    return any(source_path.endswith(os.path.normcase(f"{os.sep}{suffix}"))
               for suffix in suffixes)
def _target_module_definition_match(
    source_fp: str, target_module: str, target_file: str,
) -> bool:
    target_text = _path_text(target_file)
    module_parts = tuple(part for part in target_module.split(".") if part)
    if not target_text or not module_parts:
        return False
    target_dir = os.path.dirname(os.path.abspath(target_text))
    import_root = target_dir
    for _part in _package_chain(target_dir):
        import_root = os.path.dirname(import_root)
    module_path = os.path.join(*module_parts)
    candidates = (
        os.path.join(import_root, f"{module_path}.py"),
        os.path.join(import_root, module_path, "__init__.py"),
    )
    existing = [path for path in candidates if os.path.isfile(path)]
    if existing:
        return (len(existing) == 1
                and _path_identity(existing[0]) == _path_identity(source_fp))
    return _module_definition_match(source_fp, target_module)
def _source_for_entry(entry: ConsumptionEntry,
                      definition_index: dict[str, list[str]]) -> str:
    sym = entry.imported_name or entry.symbol
    source_files = definition_index.get(sym, [])
    if not source_files:
        return ""
    if not entry.target_module:
        return ""
    matches = [
        source_fp for source_fp in source_files
        if _module_definition_match(source_fp, entry.target_module)
    ]
    if len(matches) != 1:
        if matches:
            _log.warning(
                "消费分析: 符号 %s 的模块 %s 对应多个定义文件 %s，"
                "拒绝任意归因", sym, entry.target_module, matches)
        return ""
    return matches[0]
def _scan_module_symbols(py_files: list[str],
                         cache: Any = None) -> dict[str, list[str]]:
    module_symbols: dict[str, list[str]] = {}
    for fp in py_files:
        filepath = _path_text(fp)
        if not filepath:
            _log.warning("模块符号扫描: 路径形态非法，已跳过: %r", fp)
            continue
        tree = _parse_module_file(filepath, cache)
        if tree is None:
            continue
        module_symbols[filepath] = [
            node.name for node in _toplevel_defs(tree)]
    return module_symbols
def analyze_file_consumption(source: str, filepath: str = "",
                             tree: ast.Module | None = None) -> list[ConsumptionEntry]:
    if tree is None:
        tree = parse_source_tree(
            source, 'analyze_file_consumption:parse_source_tree')
        if tree is None:
            return []
    entries: list[ConsumptionEntry] = []
    for node in walk_nodes(tree):
        node_type = type(node)
        if node_type is ast.ImportFrom:
            _consumption_from_import_from(node, filepath, entries)
        elif node_type is ast.Import:
            _consumption_from_import(node, filepath, entries)
    return entries
@lru_cache(maxsize=4096)
def _package_chain(directory: str) -> tuple[str, ...]:
    parts: list[str] = []
    current = os.path.abspath(directory)
    while os.path.isfile(os.path.join(current, "__init__.py")):
        parts.append(os.path.basename(current))
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    return tuple(reversed(parts))
def _resolve_relative_target(filepath: str, node: ast.ImportFrom) -> str:
    module = node.module or ""
    if node.level <= 0:
        return module
    file_dir = os.path.dirname(filepath) if filepath else ""
    if not file_dir:
        return ""
    parts = list(_package_chain(os.path.abspath(file_dir)))
    ascend = node.level - 1
    if not parts or ascend >= len(parts):
        return ""
    if ascend:
        parts = parts[:len(parts) - ascend]
    parts.extend(part for part in module.split(".") if part)
    return ".".join(parts)
def _import_from_excluded(node: ast.ImportFrom) -> bool:
    if node.module == "__future__":
        return True
    top_mod = (node.module or "").split(".")[0]
    return (node.level == 0
            and (top_mod in ("__main__", "builtins")
                 or top_mod in PY_STDLIB_HINTS))
def _consumption_from_import_from(node: ast.ImportFrom, filepath: str,
                                  entries: list[ConsumptionEntry]) -> None:
    if _import_from_excluded(node):
        return
    mod = _resolve_relative_target(filepath, node)
    if node.level > 0 and not mod:
        _log.debug("消费分析: 相对导入无法解析到具体模块，跳过该条边"
                   "（%s 第 %s 行）", filepath or "<unknown>", node.lineno)
        return
    for alias in node.names:
        if alias.name == "*":
            continue
        entries.append(ConsumptionEntry(
            source_file=filepath,
            target_module=mod,
            symbol=alias.asname or alias.name,
            lineno=node.lineno,
            imported_name=alias.name,
        ))
def _consumption_from_import(node: ast.Import, filepath: str,
                             entries: list[ConsumptionEntry]) -> None:
    for alias in node.names:
        top_mod = alias.name.split(".")[0]
        if top_mod in PY_STDLIB_HINTS or top_mod == "builtins":
            continue
        sym = alias.asname or alias.name.split(".")[0]
        entries.append(ConsumptionEntry(
            source_file=filepath,
            target_module=alias.name,
            symbol=sym,
            lineno=node.lineno,
            imported_name=alias.name.split(".")[0],
        ))
def _load_file_source_and_tree(fp: str, cache: Any) -> tuple | None:
    src = None
    tree = None
    if cache is not None:
        try:
            src = cache.get_source(fp)
            tree = cache.get_ast(fp)
        except Exception as _e:  # noqa: BLE001 — 缓存失败回退直读
            log_swallowed(
                __name__, _e,
                context=f"_load_file_source_and_tree:{type(_e).__name__}")
            src = None
    if src is None:
        src = read_source(fp)
        if src is None:
            _log.debug("文件读取失败（跳过）: %s", fp)
            return None
    return src, tree
def _record_consumption(consumption_map: dict, symbol: str,
                        source_fp: str, consumer_fp: str) -> None:
    consumers = consumption_map.setdefault(symbol, {}).setdefault(
        source_fp, [])
    if consumer_fp not in consumers:
        consumers.append(consumer_fp)
def build_global_consumption_map(
    skill_dir: str,
    py_files: list[str] | None = None,
    cache: Any = None,
) -> dict[str, dict[str, list[str]]]:
    if py_files is None:
        if not _path_text(skill_dir):
            _log.warning("消费图构建: skill_dir 为空，按空图处理")
            return {}
        py_files = collect_migration_py_files(
            skill_dir, include_tests=True)
    sym_index = _definition_index(
        _scan_module_symbols(py_files, cache=cache), normalized=True)
    consumption_map: dict[str, dict[str, list[str]]] = {}
    for fp in py_files:
        filepath = _path_text(fp)
        if not filepath:
            _log.warning("消费图构建: 文件路径形态非法，已跳过: %r", fp)
            continue
        loaded = _load_file_source_and_tree(filepath, cache)
        if loaded is None:
            continue
        src, tree = loaded
        consumer_fp = norm_cache_key(filepath)
        for entry in analyze_file_consumption(src, filepath, tree=tree):
            sym = entry.imported_name or entry.symbol
            source_fp = _source_for_entry(entry, sym_index)
            if source_fp:
                _record_consumption(
                    consumption_map, sym, source_fp, consumer_fp)
    return consumption_map
def get_consumers_for_symbol(
    symbol: str,
    consumption_map: dict[str, dict[str, list[str]]],
) -> list[tuple[str, list[str]]]:
    if not isinstance(consumption_map, dict):
        _log.warning("消费图载荷非映射(%s)，按无消费者处理",
                     type(consumption_map).__name__)
        return []
    symbol_data = consumption_map.get(symbol, {})
    if not isinstance(symbol_data, dict):
        _log.warning("消费图符号载荷非映射(%s)，按无消费者处理",
                     type(symbol_data).__name__)
        return []
    return list(symbol_data.items())
_CONSUMPTION_CACHE: dict[str, dict] = {}
def get_consumption_map(skill_dir: str,
                        cache: Any = None) -> dict[str, dict[str, list[str]]]:
    if not _path_text(skill_dir):
        _log.warning("消费图查询: skill_dir 为空，返回空图（拒绝回落到 cwd）")
        return {}
    key = norm_cache_key(skill_dir)
    if key not in _CONSUMPTION_CACHE:
        try:
            _CONSUMPTION_CACHE[key] = build_global_consumption_map(
                skill_dir, cache=cache)
        except (OSError, SyntaxError, ValueError) as exc:
            _log.warning("消费图构建失败(%s)，本次降级空图（不缓存，下次调用重试）: %s",
                         skill_dir, exc)
            return {}
    return _CONSUMPTION_CACHE[key]
def invalidate_consumption_cache(skill_dir: str = "") -> None:
    if skill_dir:
        cache_key = _path_text(skill_dir)
        if cache_key:
            _CONSUMPTION_CACHE.pop(norm_cache_key(cache_key), None)
    else:
        _CONSUMPTION_CACHE.clear()
    _package_chain.cache_clear()
_ZCC_CACHE: dict[str, ZeroConsumerChecker] = {}
def get_zero_consumer_checker(skill_dir: str) -> ZeroConsumerChecker:
    if not _path_text(skill_dir):
        raise ValueError(
            "skill_dir 不能为空：拒绝把空路径解析成进程 cwd 后扫描")
    key = norm_cache_key(skill_dir)
    if key not in _ZCC_CACHE:
        checker = ZeroConsumerChecker()
        checker.scan_directory(key)
        _ZCC_CACHE[key] = checker
    return _ZCC_CACHE[key]
def invalidate_zcc_cache(skill_dir: str = "") -> None:
    if skill_dir:
        cache_key = _path_text(skill_dir)
        if cache_key:
            _ZCC_CACHE.pop(norm_cache_key(cache_key), None)
    else:
        _ZCC_CACHE.clear()
def _hub_pattern(symbol: str) -> str | None:
    sym_lower = symbol.lower() if isinstance(symbol, str) else ""
    for pattern in _HUB_SYMBOL_PATTERNS:
        if pattern in sym_lower:
            return pattern
    return None
def _symbol_consumers(symbol_data: dict, source_file: str,
                      target_file: str) -> tuple[list[str], bool]:
    src_text = _path_text(source_file)
    tgt_text = _path_text(target_file)
    if not src_text or not tgt_text or not isinstance(symbol_data, dict):
        _log.warning("消费图条目形态非法，无法裁决消费关系")
        return [], False
    src_norm = norm_cache_key(src_text)
    tgt_norm = norm_cache_key(tgt_text)
    src_is_target = src_norm == tgt_norm
    consumers: list[str] = []
    for source_fp, consumer_list in symbol_data.items():
        source_text = _path_text(source_fp)
        if not source_text or norm_cache_key(source_text) != src_norm:
            continue
        if src_is_target:
            continue
        if not isinstance(consumer_list, (list, tuple, set, frozenset)):
            _log.warning("消费图消费者载荷非序列(%s)，已跳过",
                         type(consumer_list).__name__)
            continue
        for consumer in consumer_list:
            consumer_text = _path_text(consumer)
            if consumer_text:
                consumers.append(norm_cache_key(consumer_text))
    unique = list(dict.fromkeys(consumers))
    only_by_target = (all(c == tgt_norm for c in unique)
                      if unique else False)
    return unique, only_by_target
def judge_migration(
    symbol: str,
    source_file: str,
    target_file: str,
    consumption_map: dict[str, dict[str, list[str]]],
) -> MigrationVerdict:
    if not isinstance(symbol, str) or not symbol:
        _log.warning("[Migration] 符号名非法(%s)，跳过裁决",
                     type(symbol).__name__)
        return MigrationVerdict(
            action="skip", priority="SKIP",
            reason=f"符号名非法（{type(symbol).__name__}），无法裁决",
            consumer_count=0,
        )
    if not isinstance(consumption_map, dict):
        _log.warning("[Migration] 消费图载荷非映射(%s)，无法裁决",
                     type(consumption_map).__name__)
        return MigrationVerdict(
            action="skip", priority="SKIP",
            reason="消费图载荷形态非法，无法裁决",
            consumer_count=0,
        )
    pattern = _hub_pattern(symbol)
    if pattern is not None:
        return MigrationVerdict(
            action="skip", priority="SKIP",
            reason=f"枢纽函数模式（含'{pattern}'），天然多处消费，保留原处",
            consumer_count=0,
        )
    consumers, only_by_target = _symbol_consumers(
        consumption_map.get(symbol, {}), source_file, target_file)
    consumer_count = len(consumers)
    if not consumers:
        return MigrationVerdict(
            action="skip", priority="SKIP",
            reason="无法确定消费关系，跳过",
            consumer_count=0,
        )
    if consumer_count >= SHARED_BASE_CONSUMER_THRESHOLD:
        return MigrationVerdict(
            action="skip", priority="SKIP",
            reason=f"被 {consumer_count} 个文件消费（≥{SHARED_BASE_CONSUMER_THRESHOLD}），共享底座，保留原处",
            consumer_count=consumer_count,
        )
    if consumer_count == 1:
        reason = (f"仅被目标文件独占消费（{consumer_count} 个消费者），强迁入候选"
                  if only_by_target
                  else f"仅被 1 个文件（{consumers[0]}）消费，强迁入候选")
        return MigrationVerdict(
            action="migrate_in", priority="STRONG",
            reason=reason,
            consumer_count=consumer_count,
        )
    return MigrationVerdict(
        action="migrate_in", priority="MEDIUM",
        reason=f"被 {consumer_count} 个文件消费，中迁入候选，需评估上下文贴合度",
        consumer_count=consumer_count,
    )
def _read_top_def_linenos(source_fp: str) -> dict[str, int]:
    tree = _parse_module_file(source_fp, None)
    if tree is None:
        _log.debug("解析 %s 顶层定义失败，行号保持 0", source_fp)
        return {}
    defs: dict[str, int] = {}
    for node in _toplevel_defs(tree):
        defs.setdefault(node.name, node.lineno)
    return defs
def _candidate_from_entry(entry: ConsumptionEntry, target_file: str,
                          consumption_map: dict,
                          sym_index: dict[str, list[str]],
                          def_cache: dict) -> MigrationCandidate | None:
    sym = entry.imported_name or entry.symbol
    source_fp = _source_for_entry(entry, sym_index)
    if not source_fp:
        return None
    defs = def_cache.get(source_fp)
    if defs is None:
        defs = _read_top_def_linenos(source_fp)
        def_cache[source_fp] = defs
    verdict = judge_migration(
        sym, source_fp, target_file, consumption_map)
    if verdict.action != "migrate_in":
        return None
    return MigrationCandidate(
        symbol=sym,
        source_file=source_fp,
        target_file=target_file,
        priority=verdict.priority,
        consumer_count=verdict.consumer_count,
        lineno=defs.get(sym, 0),
        reason=verdict.reason,
    )
def find_migration_candidates(
    target_file: str,
    source: str,
    consumption_map: dict[str, dict[str, list[str]]],
) -> list[MigrationCandidate]:
    if not isinstance(consumption_map, dict):
        _log.warning("候选查找: 消费图载荷非映射(%s)，按无候选处理",
                     type(consumption_map).__name__)
        return []
    entries = analyze_file_consumption(source, target_file)
    candidates: list[MigrationCandidate] = []
    sym_index: dict[str, list[str]] = {
        sym: list(sources)
        for sym, sources in consumption_map.items()
        if isinstance(sym, str) and sym and isinstance(sources, dict)
    }
    seen: set[tuple[str, str]] = set()
    def_cache: dict[str, dict[str, int]] = {}
    for entry in entries:
        sym = entry.imported_name or entry.symbol
        identity = (entry.target_module, sym)
        if identity in seen:
            continue
        seen.add(identity)
        candidate = _candidate_from_entry(
            entry, target_file, consumption_map, sym_index, def_cache)
        if candidate is not None:
            candidates.append(candidate)
    priority_order = {"STRONG": 0, "MEDIUM": 1}
    candidates.sort(key=lambda c: (priority_order.get(c.priority, 99), c.symbol))
    return candidates
class _SingleLineMultiStmtError(Exception):
    pass
class _DuplicateSymbolDefinitionError(Exception):
    pass
def _collect_def_used_names(def_node: ast.AST) -> set[str]:
    names = {node.id for node in walk_nodes(def_node)
             if isinstance(node, ast.Name)}
    for node in walk_nodes(def_node):
        if isinstance(node, ast.Global):
            names.update(node.names)
    return names
def _symtable_module_refs(source: str, symbol: str) -> set[str] | None:
    try:
        table = symtable.symtable(source, "<migration-source>", "exec")
    except (SyntaxError, RecursionError, MemoryError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_symtable_module_refs:{type(_e).__name__}')
        return None
    return symtable_global_refs(table, symbol)
def _collect_symbol_module_refs(def_node: ast.AST, source: str,
                                symbol: str) -> set[str]:
    refs = _symtable_module_refs(source, symbol)
    if refs is None:
        return _collect_def_used_names(def_node)
    return refs | enclosing_scope_load_names(def_node)
def _string_interior_lines(tree: ast.AST) -> set[int]:
    interior: set[int] = set()
    for node in walk_nodes(tree):
        is_text = (isinstance(node, ast.Constant)
                   and isinstance(node.value, str)) or isinstance(
                       node, ast.JoinedStr)
        if not is_text:
            continue
        end = getattr(node, "end_lineno", None)
        if end is None or end <= node.lineno:
            continue
        interior.update(range(node.lineno, end))
    return interior
def _append_stmt_lines(import_blocks: list, lines: list[str],
                       stmt: ast.stmt,
                       interior: frozenset[int]) -> None:
    _end = stmt.end_lineno
    block: list[str] = []
    for _i in range(stmt.lineno - 1, min(_end, len(lines))):
        _line = lines[_i]
        if _i in interior:
            block.append(_line)
            continue
        if _line.strip() and not _line.strip().startswith("#"):
            block.append(_line)
    if block:
        import_blocks.append(block)
_TRY_BODY_SAFE_STMTS = (ast.Import, ast.ImportFrom, ast.Pass)
def _try_handler_assignment_names(stmt: ast.stmt) -> set[str]:
    if isinstance(stmt, ast.Assign):
        targets = stmt.targets
    elif isinstance(stmt, ast.AnnAssign):
        targets = [stmt.target]
    else:
        return set()
    return {
        node.id for target in targets for node in walk_nodes(target)
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store)
    }
def _immutable_fallback_value(node: ast.AST | None) -> bool:
    if isinstance(node, ast.Constant):
        return True
    if isinstance(node, ast.Tuple):
        return all(_immutable_fallback_value(elt) for elt in node.elts)
    return (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.UAdd, ast.USub, ast.Invert))
            and isinstance(node.operand, ast.Constant)
            and isinstance(node.operand.value, (bool, int, float, complex)))
def _try_handler_stmt_is_safe(stmt: ast.stmt,
                              import_names: set[str]) -> bool:
    if isinstance(stmt, (ast.Import, ast.ImportFrom, ast.Pass)):
        return True
    bindings = _try_handler_assignment_names(stmt)
    if not bindings or not bindings <= import_names:
        return False
    value = (stmt.value
             if isinstance(stmt, (ast.Assign, ast.AnnAssign)) else None)
    return _immutable_fallback_value(value)
def _try_import_block_is_safe(node: ast.stmt,
                              import_names: set[str]) -> bool:
    executed = (list(node.body) + list(node.orelse)
                + list(node.finalbody))
    handled = [_s for _h in node.handlers for _s in _h.body]
    return (all(isinstance(_s, _TRY_BODY_SAFE_STMTS) for _s in executed)
            and all(_try_handler_stmt_is_safe(_s, import_names)
                    for _s in handled))
def _find_target_def(tree, symbol: str):
    matches = [node for node in _toplevel_defs(tree)
               if node.name == symbol]
    if len(matches) > 1:
        lines = ", ".join(str(node.lineno) for node in matches)
        raise _DuplicateSymbolDefinitionError(
            f"源文件存在 {len(matches)} 个同名顶层定义 {symbol!r}"
            f"（第 {lines} 行）；只有最后一个定义决定运行时绑定，"
            "逐个提取并删除全部同名定义会迁入错误实现，拒绝迁移")
    return matches[0] if matches else None
def _collect_plain_import_block(node, tree, import_blocks, lines,
                                used_names,
                                interior: frozenset[int]) -> None:
    if isinstance(node, ast.ImportFrom) and node.module == "__future__":
        return
    if not (import_stmt_binds(node) & used_names):
        return
    _reject_inline_co_statement(node, tree)
    _append_stmt_lines(import_blocks, lines, node, interior)
def _reject_inline_co_statement(node, tree) -> None:
    for _other in tree.body:
        if _other is node or isinstance(
                _other, (ast.Import, ast.ImportFrom)):
            continue
        if (_other.lineno <= node.end_lineno
                and _other.end_lineno >= node.lineno):
            raise _SingleLineMultiStmtError(
                "源文件含单行多语句（import 与其他顶层语句"
                "同行），整行收集将静默带进同行语句，拒绝"
                "提取（请先归一为多行形态）: "
                f"第 {node.lineno} 行")
def _collect_try_import_block(node, import_blocks, lines,
                              used_names,
                              interior: frozenset[int]) -> None:
    _try_imports: set[str] = set()
    for _sub in walk_nodes(node):
        if isinstance(_sub, (ast.Import, ast.ImportFrom)):
            _try_imports |= import_stmt_binds(_sub)
    if not (_try_imports & used_names):
        return
    if not _try_import_block_is_safe(node, _try_imports):
        _log.debug("迁移提取：Try 降级导入块(line %s) 含白名单外语句，保守放弃整块提取",
                   node.lineno)
        return
    _append_stmt_lines(import_blocks, lines, node, interior)
def _dedupe_import_blocks(import_blocks: list) -> list[str]:
    extracted_lines: list[str] = []
    seen_imports: set[str] = set()
    for block in import_blocks:
        stmt_key = "\n".join(ln.strip() for ln in block)
        if stmt_key in seen_imports:
            continue
        seen_imports.add(stmt_key)
        extracted_lines.extend(block)
    return extracted_lines
def _collect_symbol_imports(tree, lines: list[str],
                            used_names: set[str]) -> list[str]:
    import_blocks: list[list[str]] = []
    interior = frozenset(_string_interior_lines(tree))
    try_types = (ast.Try,) + (
        (ast.TryStar,) if hasattr(ast, "TryStar") else ())
    for node in tree.body:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            _collect_plain_import_block(
                node, tree, import_blocks, lines, used_names, interior)
        elif isinstance(node, try_types):
            _collect_try_import_block(
                node, import_blocks, lines, used_names, interior)
    extracted_lines = _dedupe_import_blocks(import_blocks)
    if extracted_lines:
        extracted_lines.append("")
    return extracted_lines
def _definition_lines(lines: list[str], start_line: int,
                      end_line: int) -> list[str]:
    return [lines[i] for i in range(start_line - 1,
                                    min(end_line, len(lines)))]
def _extract_symbol_definition(source: str, symbol: str) -> tuple[str, int]:
    tree = parse_source_tree(
        source, '_extract_symbol_definition:parse_source_tree')
    if tree is None:
        return "", 0
    lines = ast_split_lines(source)
    def_node = _find_target_def(tree, symbol)
    if def_node is None:
        return "", 0
    start_line = symbol_start_line(lines, def_node)
    used_names = _collect_symbol_module_refs(def_node, source, symbol)
    extracted_lines = _collect_symbol_imports(tree, lines, used_names)
    extracted_lines.extend(
        _definition_lines(lines, start_line, def_node.end_lineno))
    return "\n".join(extracted_lines), len(extracted_lines)
def _target_binds_name(target, symbol: str) -> bool:
    return any(isinstance(el, ast.Name)
               and isinstance(el.ctx, ast.Store)
               and el.id == symbol
               for el in walk_nodes(target))
def _node_binds_toplevel_name(node, symbol: str) -> bool:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        return node.name == symbol
    type_alias = getattr(ast, "TypeAlias", None)
    if type_alias is not None and isinstance(node, type_alias):
        return getattr(node.name, "id", "") == symbol
    if isinstance(node, ast.Assign):
        return any(_target_binds_name(t, symbol) for t in node.targets)
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return False
    if isinstance(node, (ast.AugAssign, ast.AnnAssign)):
        return (isinstance(node.target, ast.Name)
                and node.target.id == symbol)
    return False
class _ImportBindingStripper(ast.NodeTransformer):
    def visit_Import(self, node: ast.Import) -> None:
        return None
    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        return None
def _unsafe_import_rebinding_names(tree: ast.Module) -> set[str]:
    runtime_imports = import_bound_names(tree.body)
    if not runtime_imports:
        return set()
    original_nodes = [
        node for node in tree.body
        if not isinstance(node, (ast.Import, ast.ImportFrom))
    ]
    non_import_tree = _ImportBindingStripper().visit(copy.deepcopy(tree))
    unsafe: set[str] = set()
    try_types = (ast.Try,) + (
        (ast.TryStar,) if hasattr(ast, "TryStar") else ())
    for original, stripped in zip(
            original_nodes, non_import_tree.body, strict=True):
        rebound = module_scope_binds([stripped]) & runtime_imports
        if not rebound:
            continue
        if isinstance(original, try_types):
            try_imports: set[str] = set()
            for sub in walk_nodes(original):
                if isinstance(sub, (ast.Import, ast.ImportFrom)):
                    try_imports |= import_stmt_binds(sub)
            if _try_import_block_is_safe(original, try_imports):
                continue
        unsafe |= rebound
    return unsafe
def _has_toplevel_definition(code: str, symbol: str) -> bool:
    tree = parse_source_tree(
        code, '_has_toplevel_definition:parse_source_tree')
    if tree is None:
        return False
    non_import_tree = _ImportBindingStripper().visit(copy.deepcopy(tree))
    return symbol in module_scope_binds(non_import_tree.body)
def _import_rebinding_conflict(
    target_code: str, symbol: str, source_file: str, target_file: str,
) -> str | None:
    source_text = _path_text(source_file)
    if not source_text:
        return None
    tree = parse_source_tree(
        target_code, '_import_rebinding_conflict:parse_source_tree')
    if tree is None:
        return None
    target_text = _path_text(target_file)
    for node in iter_module_level_stmts(tree):
        if isinstance(node, ast.Import) and symbol in import_stmt_binds(node):
            return (f"目标文件第 {node.lineno} 行已通过 import 绑定 "
                    f"'{symbol}'；迁入同名定义会覆盖模块对象而非待迁函数，"
                    "请先重命名或移除该绑定")
        if not isinstance(node, ast.ImportFrom):
            continue
        for alias in node.names:
            if alias.name == "*" or (alias.asname or alias.name) != symbol:
                continue
            module = _resolve_relative_target(target_text, node)
            if module and _target_module_definition_match(
                    source_text, module, target_text):
                continue
            reference = "." * node.level + (node.module or "")
            return (f"目标文件第 {node.lineno} 行已从 '{reference}' 导入并绑定 "
                    f"'{symbol}'，该绑定无法证明来自待迁源 {source_text}；"
                    "迁入同名定义会覆盖无关实现并改变目标既有调用结果，"
                    "请先重命名或移除冲突导入")
    return None
def _import_binding_origins(
    tree: ast.Module,
) -> dict[str, frozenset[tuple[str, ...]]]:
    origins: dict[str, set[tuple[str, ...]]] = {}
    runtime_imports = import_bound_names(tree.body)
    unsafe_rebound = _unsafe_import_rebinding_names(tree)
    for node in iter_module_level_stmts(tree):
        aliases: list[tuple[str, tuple[str, ...]]] = []
        if isinstance(node, ast.Import):
            for alias in node.names:
                bound = alias.asname or alias.name.split(".")[0]
                imported = alias.name if alias.asname else bound
                aliases.append((bound, ("import", imported)))
        elif isinstance(node, ast.ImportFrom):
            module = "." * node.level + (node.module or "")
            aliases.extend(
                (alias.asname or alias.name,
                 ("from", module, alias.name))
                for alias in node.names if alias.name != "*"
            )
        for bound, origin in aliases:
            if bound in runtime_imports and bound not in unsafe_rebound:
                origins.setdefault(bound, set()).add(origin)
    return {name: frozenset(sources) for name, sources in origins.items()}
def _module_binding_kinds(
    code: str,
) -> tuple[
    set[str], dict[str, frozenset[tuple[str, ...]]]
] | None:
    tree = parse_source_tree(
        code, '_module_binding_kinds:parse_source_tree')
    if tree is None:
        return None
    return (module_scope_binds(tree.body), _import_binding_origins(tree))
def _migrate_binding_conflict(
    target_code: str, extracted_code: str, symbol: str,
) -> str | None:
    target = _module_binding_kinds(target_code)
    fragment = _module_binding_kinds(extracted_code)
    if target is None or fragment is None:
        return None
    target_binds, target_imports = target
    fragment_binds, fragment_imports = fragment
    overlaps = (fragment_binds & target_binds) - {symbol}
    benign = {
        name for name in overlaps
        if name in fragment_imports and name in target_imports
        and fragment_imports[name] == target_imports[name]
    }
    conflicts = sorted(overlaps - benign)
    if not conflicts:
        return None
    return (f"迁入片段会在目标文件重新绑定已有名字 {conflicts}；"
            "直接迁入会静默覆盖目标模块级绑定，"
            "请先重命名依赖或调整迁移边界")
def _copied_import_names(extracted_code: str) -> set[str]:
    tree = parse_source_tree(
        extracted_code, '_copied_import_names:parse_source_tree')
    if tree is None:
        return set()
    names: set[str] = set()
    for node in iter_module_level_stmts(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            names |= import_stmt_binds(node)
    return names
def _collect_scope_global_usage(
    scope, refs: set[str], writes: set[str] | None,
) -> None:
    for symbol in scope.get_symbols():
        if not symbol.is_global():
            continue
        if symbol.is_referenced():
            refs.add(symbol.get_name())
        if writes is not None and (
                symbol.is_assigned() or symbol.is_imported()):
            writes.add(symbol.get_name())
    for child in scope.get_children():
        _collect_scope_global_usage(child, refs, writes)
def _fragment_module_free_reads(extracted_code: str) -> set[str] | None:
    try:
        table = symtable.symtable(
            extracted_code, "<migration-fragment>", "exec")
    except PARSE_DEGRADE_EXC as _e:
        _log.debug("迁移依赖校验: 迁入片段作用域解析失败，跳过校验: %s", _e)
        return None
    bound = {
        symbol.get_name() for symbol in table.get_symbols()
        if symbol.is_assigned() or symbol.is_imported()
        or symbol.is_namespace()
    }
    reads = {
        symbol.get_name() for symbol in table.get_symbols()
        if symbol.is_referenced()
    }
    for child in table.get_children():
        _collect_scope_global_usage(child, reads, None)
    return reads - bound
def _symbol_global_usage(
    source: str, symbol: str,
) -> tuple[set[str], set[str]] | None:
    try:
        table = symtable.symtable(source, "<migration-source>", "exec")
        sym = table.lookup(symbol)
        if not sym.is_namespace():
            return None
        namespaces = sym.get_namespaces()
    except (SyntaxError, KeyError, ValueError, RecursionError,
            MemoryError) as _e:
        _log.debug("迁移依赖校验: 源符号作用域解析失败，跳过校验: %s", _e)
        return None
    refs: set[str] = set()
    writes: set[str] = set()
    for scope in namespaces:
        _collect_scope_global_usage(scope, refs, writes)
    return refs, writes
def _mutation_root(node: ast.AST) -> str | None:
    while isinstance(node, (ast.Attribute, ast.Subscript)):
        node = node.value
    return node.id if isinstance(node, ast.Name) else None
_STATE_MUTATING_BUILTIN_CALLS = frozenset({"delattr", "setattr"})
_STATE_MUTATING_METHODS = INPLACE_MUTATING_METHODS | frozenset({
    "__delattr__", "__setattr__",
})
_UNBOUND_STATE_MUTATOR_RECEIVERS = frozenset({
    "bytearray", "dict", "list", "object", "set", "type",
})
_DEFAULT_VISIBLE_BUILTINS = frozenset(BUILTIN_NAMES)
def _node_mutation_roots(node: ast.AST) -> set[str]:
    roots: set[str] = set()
    if (isinstance(node, (ast.Attribute, ast.Subscript))
            and isinstance(node.ctx, (ast.Store, ast.Del))):
        root = _mutation_root(node.value)
        if root:
            roots.add(root)
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr in _STATE_MUTATING_METHODS):
        root = _mutation_root(node.func.value)
        if root:
            roots.add(root)
    return roots
def _is_scope_body_child(parent: ast.AST, child: ast.AST) -> bool:
    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                           ast.ClassDef)):
        return child in parent.body
    if isinstance(parent, ast.Lambda):
        return child is parent.body
    return False
def _local_name_scope(
    node: ast.AST, name: str, parents: dict[int, ast.AST],
) -> ast.AST | None:
    current = node
    crossed_function = False
    crossed_class = False
    parent = parents.get(id(current))
    while parent is not None:
        if (isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda))
                and _is_scope_body_child(parent, current)):
            local, declared_global = exec_scope_declarations(parent)
            if name in declared_global:
                return None
            if name in local:
                return parent
            crossed_function = True
        elif (isinstance(parent, ast.ClassDef)
                and _is_scope_body_child(parent, current)):
            if not crossed_function and not crossed_class:
                local, declared_global = exec_scope_declarations(parent)
                if name in declared_global:
                    return None
                if name in local:
                    return parent
            crossed_class = True
        current, parent = parent, parents.get(id(parent))
    return None
def _enclosing_callable_scope(
    node: ast.AST, parents: dict[int, ast.AST],
) -> ast.AST | None:
    current = node
    parent = parents.get(id(current))
    while parent is not None:
        if (isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda))
                and _is_scope_body_child(parent, current)):
            return parent
        current, parent = parent, parents.get(id(parent))
    return None
def _mutation_name_is_module_global(
    node: ast.AST, name: str, parents: dict[int, ast.AST],
) -> bool:
    return _local_name_scope(node, name, parents) is None
@dataclass(frozen=True)
class _StateAliasBinding:
    value: ast.AST
    position: tuple[int, int]
    conditional: bool
def _alias_position(node: ast.AST) -> tuple[int, int]:
    return (getattr(node, "lineno", 0) or 0,
            getattr(node, "col_offset", 0) or 0)
def _alias_binding_is_conditional(
    node: ast.AST, scope: ast.AST, parents: dict[int, ast.AST],
) -> bool:
    conditional_types = (
        ast.If, ast.For, ast.AsyncFor, ast.While, ast.Try, ast.Match,
        ast.BoolOp, ast.IfExp, ast.ListComp, ast.SetComp, ast.DictComp,
        ast.GeneratorExp,
    ) + ((ast.TryStar,) if hasattr(ast, "TryStar") else ())
    current = node
    while current is not scope:
        parent = parents.get(id(current))
        if parent is None:
            break
        if isinstance(parent, conditional_types):
            return True
        current = parent
    return False
def _alias_default_pairs(
    scope: ast.AST,
) -> Iterator[tuple[ast.arg, ast.AST]]:
    if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
        return
    arguments = scope.args
    positional = [*arguments.posonlyargs, *arguments.args]
    if arguments.defaults:
        start = len(positional) - len(arguments.defaults)
        yield from zip(positional[start:], arguments.defaults, strict=False)
    for arg, default in zip(
            arguments.kwonlyargs, arguments.kw_defaults, strict=False):
        if default is not None:
            yield arg, default
def _alias_target_value_pairs(
    target: ast.AST, value: ast.AST,
) -> Iterator[tuple[ast.Name, ast.AST]]:
    if isinstance(target, ast.Name):
        yield target, value
        return
    if not isinstance(target, (ast.Tuple, ast.List)):
        return
    if not isinstance(value, (ast.Tuple, ast.List)):
        return
    targets, values = target.elts, value.elts
    if any(isinstance(item, ast.Starred) for item in values):
        return
    starred = [index for index, item in enumerate(targets)
               if isinstance(item, ast.Starred)]
    if len(starred) > 1:
        return
    if not starred:
        if len(targets) != len(values):
            return
        pairs = zip(targets, values, strict=True)
    else:
        star_index = starred[0]
        trailing = len(targets) - star_index - 1
        if len(values) < len(targets) - 1:
            return
        aligned = (
            list(zip(targets[:star_index], values[:star_index],
                     strict=True))
            + list(zip(targets[star_index + 1:],
                       values[len(values) - trailing:] if trailing else [],
                       strict=True))
        )
        pairs = iter(aligned)
    for target_elt, value_elt in pairs:
        yield from _alias_target_value_pairs(target_elt, value_elt)
def _collect_state_alias_bindings(
    def_node: ast.AST, parents: dict[int, ast.AST],
) -> dict[tuple[int, str], list[_StateAliasBinding]]:
    bindings: dict[tuple[int, str], list[_StateAliasBinding]] = {}
    scopes = [
        node for node in walk_nodes(def_node)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda))]
    for scope in scopes:
        for arg, default in _alias_default_pairs(scope):
            bindings.setdefault((id(scope), arg.arg), []).append(
                _StateAliasBinding(default, (0, 0), True))
    for node in walk_nodes(def_node):
        if isinstance(node, ast.Assign):
            targets, value = node.targets, node.value
        elif ((isinstance(node, ast.AnnAssign) and node.value is not None)
              or isinstance(node, ast.NamedExpr)):
            targets, value = [node.target], node.value
        else:
            continue
        for target in targets:
            for bound, bound_value in _alias_target_value_pairs(target, value):
                scope = _local_name_scope(bound, bound.id, parents)
                if scope is None:
                    continue
                bindings.setdefault((id(scope), bound.id), []).append(
                    _StateAliasBinding(
                        bound_value, _alias_position(node),
                        _alias_binding_is_conditional(node, scope, parents)))
    for records in bindings.values():
        records.sort(key=lambda record: record.position)
    return bindings
def _resolve_state_alias_name(
    name: str, node: ast.AST, module_bindings: frozenset[str],
    parents: dict[int, ast.AST],
    bindings: dict[tuple[int, str], list[_StateAliasBinding]],
    seen: set[tuple[int, str, tuple[int, int]]],
) -> tuple[frozenset[str], frozenset[tuple[str, str]]]:
    scope = _local_name_scope(node, name, parents)
    if scope is None:
        if (name in module_bindings
                and _mutation_name_is_module_global(node, name, parents)):
            return frozenset({name}), frozenset()
        return frozenset(), frozenset()
    position = _alias_position(node)
    late_bound = (
        isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
        and _enclosing_callable_scope(node, parents) is not scope
    )
    identity = (id(scope), name, position)
    if identity in seen:
        return frozenset(), frozenset()
    seen.add(identity)
    objects: set[str] = set()
    methods: set[tuple[str, str]] = set()
    try:
        for record in bindings.get((id(scope), name), ()):
            if not late_bound and record.position >= position:
                break
            next_objects, next_methods = _resolve_state_alias_expr(
                record.value, module_bindings, parents, bindings, seen)
            if record.conditional or late_bound:
                objects.update(next_objects)
                methods.update(next_methods)
            else:
                objects = set(next_objects)
                methods = set(next_methods)
    finally:
        seen.remove(identity)
    return frozenset(objects), frozenset(methods)
def _resolve_state_alias_expr(
    node: ast.AST, module_bindings: frozenset[str],
    parents: dict[int, ast.AST],
    bindings: dict[tuple[int, str], list[_StateAliasBinding]],
    seen: set[tuple[int, str, tuple[int, int]]],
) -> tuple[frozenset[str], frozenset[tuple[str, str]]]:
    if isinstance(node, ast.Name):
        return _resolve_state_alias_name(
            node.id, node, module_bindings, parents, bindings, seen)
    if (isinstance(node, ast.Attribute)
            and node.attr in _STATE_MUTATING_METHODS):
        objects, _methods = _resolve_state_alias_expr(
            node.value, module_bindings, parents, bindings, seen)
        return (frozenset(),
                frozenset((name, node.attr) for name in objects))
    if isinstance(node, (ast.Attribute, ast.Subscript)):
        return _resolve_state_alias_expr(
            node.value, module_bindings, parents, bindings, seen)
    values: tuple[ast.AST, ...] = ()
    if isinstance(node, ast.IfExp):
        values = (node.body, node.orelse)
    elif isinstance(node, ast.BoolOp):
        values = tuple(node.values)
    elif isinstance(node, ast.NamedExpr):
        values = (node.value,)
    objects: set[str] = set()
    methods: set[tuple[str, str]] = set()
    for value in values:
        next_objects, next_methods = _resolve_state_alias_expr(
            value, module_bindings, parents, bindings, seen)
        objects.update(next_objects)
        methods.update(next_methods)
    return frozenset(objects), frozenset(methods)
def _mutated_module_state(
    def_node: ast.AST, module_bindings: frozenset[str],
    visible_builtins: frozenset[str] | set[str] = _DEFAULT_VISIBLE_BUILTINS,
) -> frozenset[str]:
    mutated: set[str] = set()
    if not module_bindings:
        return frozenset()
    module = ast.Module(body=[def_node], type_ignores=[])
    parents = build_parent_map(module)
    alias_bindings = _collect_state_alias_bindings(def_node, parents)
    for node in walk_nodes(def_node):
        for name in _node_mutation_roots(node):
            objects, _methods = _resolve_state_alias_name(
                name, node, module_bindings, parents, alias_bindings, set())
            mutated.update(objects)
        if not isinstance(node, ast.Call):
            continue
        if isinstance(node.func, ast.Name):
            if (node.func.id in _STATE_MUTATING_BUILTIN_CALLS
                    and node.args and node.func.id in visible_builtins
                    and _mutation_name_is_module_global(
                        node.func, node.func.id, parents)):
                objects, _methods = _resolve_state_alias_expr(
                    node.args[0], module_bindings, parents, alias_bindings,
                    set())
                mutated.update(objects)
            _objects, methods = _resolve_state_alias_name(
                node.func.id, node.func, module_bindings, parents,
                alias_bindings, set())
            mutated.update(
                name for name, method in methods
                if method in _STATE_MUTATING_METHODS)
        elif (isinstance(node.func, ast.Attribute)
              and node.func.attr in _STATE_MUTATING_METHODS and node.args
              and isinstance(node.func.value, ast.Name)
              and node.func.value.id in _UNBOUND_STATE_MUTATOR_RECEIVERS
              and node.func.value.id in visible_builtins
              and _mutation_name_is_module_global(
                  node.func.value, node.func.value.id, parents)):
            objects, _methods = _resolve_state_alias_expr(
                node.args[0], module_bindings, parents, alias_bindings, set())
            mutated.update(objects)
    return frozenset(mutated)
@dataclass(frozen=True)
class _SymbolDependencyAudit:
    missing: frozenset[str] = frozenset()
    ambiguous: frozenset[str] = frozenset()
    context: frozenset[str] = frozenset()
    writes: frozenset[str] = frozenset()
    mutations: frozenset[str] = frozenset()
_MODULE_CONTEXT_GLOBALS = frozenset({
    "__file__", "__name__", "__package__", "__spec__",
    "__loader__", "__cached__",
})
_MODULE_CONTEXT_BUILTINS = frozenset({"globals", "eval", "exec"})
def _dynamic_context_import_aliases(
    tree: ast.Module,
) -> tuple[dict[str, str], set[str]]:
    aliases: dict[str, str] = {}
    module_aliases: set[str] = set()
    for name, origins in _import_binding_origins(tree).items():
        if len(origins) != 1:
            continue
        origin = next(iter(origins))
        if (len(origin) == 3 and origin[0] == "from"
                and origin[1] == "builtins"
                and origin[2] in _MODULE_CONTEXT_BUILTINS):
            aliases[name] = origin[2]
        elif origin == ("import", "builtins"):
            module_aliases.add(name)
    return aliases, module_aliases
def _indirect_dynamic_context_refs(
    node: ast.AST, parents: dict[int, ast.AST],
    aliases: dict[str, str], module_aliases: set[str],
    visible_builtins: frozenset[str] | set[str] = _DEFAULT_VISIBLE_BUILTINS,
) -> set[str]:
    refs: set[str] = set()
    for current in walk_nodes(node):
        if isinstance(current, ast.Name) and isinstance(current.ctx, ast.Load):
            if _local_name_scope(current, current.id, parents) is not None:
                continue
            if current.id in aliases or current.id == "__builtins__":
                refs.add(current.id)
        elif (isinstance(current, ast.Attribute)
              and current.attr in _MODULE_CONTEXT_BUILTINS
              and isinstance(current.value, ast.Name)
              and current.value.id in module_aliases
              and _local_name_scope(
                  current.value, current.value.id, parents) is None):
            refs.add(current.value.id)
        elif (isinstance(current, ast.Call)
              and len(current.args) in (2, 3) and not current.keywords):
            func = current.func
            bare_getattr = (
                isinstance(func, ast.Name) and func.id == "getattr"
                and func.id in visible_builtins
                and _mutation_name_is_module_global(
                    func, func.id, parents))
            module_getattr = (
                isinstance(func, ast.Attribute) and func.attr == "getattr"
                and isinstance(func.value, ast.Name)
                and func.value.id in module_aliases
                and _mutation_name_is_module_global(
                    func.value, func.value.id, parents))
            if not (bare_getattr or module_getattr):
                continue
            receiver, attribute = current.args[:2]
            if (isinstance(receiver, ast.Name)
                    and receiver.id in module_aliases
                    and _mutation_name_is_module_global(
                        receiver, receiver.id, parents)
                    and isinstance(attribute, ast.Constant)
                    and isinstance(attribute.value, str)
                    and attribute.value in _MODULE_CONTEXT_BUILTINS):
                refs.add(receiver.id)
    return refs
def _binding_definition_fingerprints(
    tree: ast.Module, names: frozenset[str],
) -> dict[str, frozenset[str]]:
    definitions: dict[str, set[str]] = {name: set() for name in names}
    if not names:
        return {}
    for node in iter_module_level_stmts(tree):
        for name in names:
            if _node_binds_toplevel_name(node, name):
                definitions[name].add(ast.dump(node))
    return {name: frozenset(items) for name, items in definitions.items()}
def _proven_binding_identities(
    source_tree: ast.Module, target_tree: ast.Module, names: frozenset[str],
    migrated_symbols: frozenset[str],
) -> set[str]:
    definition_names = names & migrated_symbols
    source_defs = _binding_definition_fingerprints(
        source_tree, definition_names)
    target_defs = _binding_definition_fingerprints(
        target_tree, definition_names)
    source_imports = _import_binding_origins(source_tree)
    target_imports = _import_binding_origins(target_tree)
    proven: set[str] = set()
    for name in names:
        same_definition = name in migrated_symbols and bool(
            source_defs.get(name)) and (
                source_defs[name] == target_defs.get(name))
        same_import = bool(source_imports.get(name)) and (
            source_imports[name] == target_imports.get(name))
        if same_definition or same_import:
            proven.add(name)
    return proven
def _audit_symbol_dependencies(
    source_code: str, target_code: str, extracted_code: str, symbol: str,
    migrated_symbols: frozenset[str],
) -> _SymbolDependencyAudit:
    source_tree = parse_source_tree(
        source_code, '_audit_symbol_dependencies:parse_source_tree')
    target_tree = parse_source_tree(
        target_code, '_audit_symbol_dependencies:parse_target_tree')
    if source_tree is None or target_tree is None:
        return _SymbolDependencyAudit()
    target_bindings = module_scope_binds(target_tree.body)
    def_node = _find_target_def(source_tree, symbol)
    if def_node is None:
        return _SymbolDependencyAudit()
    usage = _symbol_global_usage(source_code, symbol)
    fragment_reads = _fragment_module_free_reads(extracted_code)
    if usage is None or fragment_reads is None:
        return _SymbolDependencyAudit()
    refs, writes = usage
    source_bindings = module_scope_binds(source_tree.body)
    source_imports = import_bound_names(source_tree.body)
    unsafe_rebound = _unsafe_import_rebinding_names(source_tree)
    module_state = frozenset(
        (source_bindings - source_imports - {symbol})
        | (unsafe_rebound - {symbol}))
    visible_builtins = BUILTIN_NAMES - source_bindings
    mutations = _mutated_module_state(
        def_node, module_state, visible_builtins)
    refs |= fragment_reads
    refs |= (enclosing_scope_load_names(def_node)
             - _type_param_names(def_node))
    copied = _copied_import_names(extracted_code) - unsafe_rebound
    external_refs = refs - {symbol} - copied
    dynamic_aliases, dynamic_modules = _dynamic_context_import_aliases(
        source_tree)
    indirect_context = _indirect_dynamic_context_refs(
        def_node, build_parent_map(source_tree),
        dynamic_aliases, dynamic_modules, visible_builtins)
    context = ((external_refs & _MODULE_CONTEXT_GLOBALS)
               | (external_refs & _MODULE_CONTEXT_BUILTINS
                  & visible_builtins)
               | indirect_context)
    ambiguous_candidates = frozenset({
        name for name in external_refs - context
        if name in target_bindings
        and (name in source_bindings or name in visible_builtins)
    })
    ambiguous = ambiguous_candidates - _proven_binding_identities(
        source_tree, target_tree, ambiguous_candidates, migrated_symbols)
    missing = {
        name for name in external_refs - context - ambiguous
        if _is_missing_dependency(
            name, target_bindings, visible_builtins)
    }
    return _SymbolDependencyAudit(
        missing=frozenset(missing),
        ambiguous=frozenset(ambiguous),
        context=frozenset(context),
        writes=frozenset(writes),
        mutations=mutations,
    )
def _type_param_names(def_node: ast.AST) -> set[str]:
    return {type_param.name
            for type_param in getattr(def_node, "type_params", None) or ()}
def _is_missing_dependency(
    name: str,
    target_bindings: set[str],
    visible_builtins: set[str],
) -> bool:
    return not (name in target_bindings or name in visible_builtins
                or name == "__builtins__")
def _target_read_names(target: ast.AST) -> set[str]:
    return {node.id for node in walk_nodes(target)
            if isinstance(node, ast.Name)}
def _retained_source_refs(node: ast.AST) -> set[str]:
    refs: set[str] = set()
    stack: list[ast.AST] = [node]
    while stack:
        current = stack.pop()
        if isinstance(current, ast.If) and is_type_checking_guard(current.test):
            stack.append(current.test)
            stack.extend(current.orelse)
            continue
        if isinstance(current, ast.Name):
            if isinstance(current.ctx, ast.Load):
                refs.add(current.id)
        elif isinstance(current, ast.AugAssign):
            refs |= _target_read_names(current.target)
        elif isinstance(current, ast.Delete):
            for target in current.targets:
                refs |= _target_read_names(target)
        stack.extend(ast.iter_child_nodes(current))
    return refs
def _evaluates_in_module_scope(
    node: ast.AST, parents: dict[int, ast.AST],
) -> bool:
    current = node
    generator: ast.comprehension | None = None
    in_generator_iter = False
    comp_types = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
    parent = parents.get(id(current))
    while parent is not None:
        if (isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda))
                and _is_scope_body_child(parent, current)):
            return False
        if isinstance(parent, ast.comprehension):
            generator = parent
            in_generator_iter = current is parent.iter
        elif isinstance(parent, comp_types):
            if generator is None:
                return False
            try:
                index = parent.generators.index(generator)
            except ValueError:
                return False
            if index or not in_generator_iter:
                return False
            generator = None
            in_generator_iter = False
        current, parent = parent, parents.get(id(parent))
    return True
def _module_local_dynamic_names(
    node: ast.AST, parents: dict[int, ast.AST],
) -> set[str]:
    names: set[str] = set()
    for current in walk_nodes(node):
        if not (isinstance(current, ast.Call)
                and isinstance(current.func, ast.Name)
                and current.func.id in {"locals", "vars"}
                and not current.args and not current.keywords):
            continue
        if _evaluates_in_module_scope(current, parents):
            names.add(current.func.id)
    return names
def retained_source_reference_blocks(tree: ast.AST,
                                     moved_names: set[str]) -> list[str]:
    if not moved_names:
        return []
    blocked: list[str] = []
    module_bindings = module_scope_binds(tree.body)
    parents = build_parent_map(tree)
    dynamic_aliases, dynamic_modules = _dynamic_context_import_aliases(tree)
    visible_builtins = BUILTIN_NAMES - module_bindings
    for node in tree.body:
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef))
                and node.name in moved_names):
            continue
        refs = _retained_source_refs(node)
        bad = refs & moved_names
        if bad:
            blocked.append(
                "源文件保留代码引用将被迁走的符号 "
                + ", ".join(repr(n) for n in sorted(bad))
                + f"（第 {node.lineno} 行），符号迁走后源模块将在导入期或"
                "回调运行期 NameError，请先调整迁移/拆分边界或移除该引用")
            continue
        dynamic = (((refs & _MODULE_CONTEXT_BUILTINS)
                    | _module_local_dynamic_names(node, parents))
                   - module_bindings) | _indirect_dynamic_context_refs(
                       node, parents, dynamic_aliases, dynamic_modules,
                       visible_builtins)
        if dynamic:
            blocked.append(
                "源文件保留代码使用动态模块命名空间 "
                + ", ".join(sorted(dynamic))
                + "，无法排除其通过字符串键或动态代码访问待迁符号 "
                + ", ".join(repr(n) for n in sorted(moved_names))
                + f"（第 {node.lineno} 行）；删除定义可能使保留代码运行期"
                "断裂，请先改为显式依赖或调整迁移边界")
    return blocked
def _relative_import_context_error(
    extracted_code: str, source_file: str, target_file: str,
) -> str | None:
    tree = parse_source_tree(
        extracted_code, '_relative_import_context_error:parse_source_tree')
    if tree is None:
        return "迁入片段无法解析，不能校验相对导入的目标身份"
    relatives = [node for node in walk_nodes(tree)
                 if isinstance(node, ast.ImportFrom) and node.level > 0]
    if not relatives:
        return None
    source_text = _path_text(source_file)
    target_text = _path_text(target_file)
    if not source_text or not target_text:
        return ("迁入片段含相对导入，但缺少源/目标路径上下文，"
                "无法证明依赖在目标包中保持同一身份；请通过 "
                "prepare_migrate_in/batch_migrate_in 提供候选路径")
    source_package = norm_cache_key(os.path.dirname(os.path.abspath(source_text)))
    target_package = norm_cache_key(os.path.dirname(os.path.abspath(target_text)))
    if source_package != target_package:
        return ("迁入片段含相对导入，跨包迁入会改变依赖解析目标；"
                "为避免生成导入期断裂或静默绑定到同名依赖的代码，"
                "请先把相对导入改为指向源依赖的显式绝对导入")
    return None
def _splice_symbol(target_code: str, extracted_code: str) -> str:
    eol = _source_eol(target_code)
    migrated = (extracted_code.replace("\n", eol)
                if eol != "\n" else extracted_code)
    if not target_code.strip():
        new_target = migrated
    else:
        new_target = target_code.rstrip("\r\n") + eol + eol + migrated
    if not new_target.endswith(("\r", "\n")):
        new_target += eol
    return new_target
def _postponed_annotations(code: str) -> bool | None:
    tree = parse_source_tree(
        code, '_postponed_annotations:parse_source_tree')
    if tree is None:
        return None
    return any(
        isinstance(node, ast.ImportFrom) and node.module == "__future__"
        and any(alias.name == "annotations" for alias in node.names)
        for node in tree.body
    )
@immutable("valid_syntax")
def execute_migrate_in(
    source_code: str,
    target_code: str,
    symbol: str,
    *,
    source_file: str = "",
    target_file: str = "",
    _migrated_symbols: frozenset[str] = frozenset(),
) -> MigrateInResult:
    if not isinstance(source_code, str) or not isinstance(target_code, str):
        return MigrateInResult(
            success=False,
            symbol=symbol if isinstance(symbol, str) else "",
            reason="源/目标源码载荷须为 str 文本",
        )
    try:
        extracted_code, line_count = _extract_symbol_definition(
            source_code, symbol)
    except (_SingleLineMultiStmtError,
            _DuplicateSymbolDefinitionError) as _extract_error:
        log_swallowed(
            __name__, _extract_error,
            context=f'execute_migrate_in:{type(_extract_error).__name__}')
        return MigrateInResult(
            success=False, symbol=symbol,
            reason=str(_extract_error),
        )
    if not extracted_code:
        return MigrateInResult(
            success=False, symbol=symbol,
            reason=f"在源文件中未找到符号 '{symbol}' 的定义",
        )
    source_postponed = _postponed_annotations(source_code)
    target_postponed = _postponed_annotations(target_code)
    if source_postponed is None or target_postponed is None:
        return MigrateInResult(
            success=False, symbol=symbol,
            reason="源/目标文件无法解析，不能校验注解求值语义",
        )
    if source_postponed != target_postponed:
        return MigrateInResult(
            success=False, symbol=symbol,
            reason=("源/目标文件的 __future__.annotations 特性不一致，"
                    "迁入会改变函数注解的求值时机与 __annotations__ 内容；"
                    "请先统一目标文件的 future 特性后重试"),
        )
    relative_error = _relative_import_context_error(
        extracted_code, source_file, target_file)
    if relative_error is not None:
        return MigrateInResult(
            success=False, symbol=symbol, reason=relative_error)
    if _has_toplevel_definition(target_code, symbol):
        return MigrateInResult(
            success=False, symbol=symbol,
            reason=f"目标文件已存在同名符号 '{symbol}' 的顶层定义，"
                   "直接迁入会产生重复定义（后者静默遮蔽前者）；"
                   "请先重命名或移除冲突定义后重试",
        )
    import_conflict = _import_rebinding_conflict(
        target_code, symbol, source_file, target_file)
    if import_conflict is not None:
        return MigrateInResult(
            success=False, symbol=symbol, reason=import_conflict)
    binding_conflict = _migrate_binding_conflict(
        target_code, extracted_code, symbol)
    if binding_conflict is not None:
        return MigrateInResult(
            success=False, symbol=symbol, reason=binding_conflict)
    dependency_audit = _audit_symbol_dependencies(
        source_code, target_code, extracted_code, symbol, _migrated_symbols)
    block_reason = _dependency_audit_reason(dependency_audit, symbol)
    if block_reason is not None:
        return MigrateInResult(
            success=False, symbol=symbol, reason=block_reason)
    new_target = _splice_symbol(target_code, extracted_code)
    try:
        ChangeImmunity.verify_decorated(
            execute_migrate_in, {"code": new_target})
    except ContractViolationError as _cve:
        log_swallowed(__name__, _cve,
                      context=f'execute_migrate_in:{type(_cve).__name__}')
        return MigrateInResult(
            success=False, symbol=symbol,
            reason=f"迁入产物未通过不变性校验: {_cve}",
        )
    return MigrateInResult(
        success=True,
        symbol=symbol,
        target_code=new_target,
        source_code=source_code,
        source_file=source_file,
        target_file=target_file,
        base_target_code=target_code,
        reason=f"已生成 '{symbol}' 迁入目标文件的代码预览（{line_count} 行），"
               "未添加兼容桩（S01），AI 审核后落盘并更新消费者 import",
    )
def _dependency_audit_reason(
    audit: _SymbolDependencyAudit, symbol: str,
) -> str | None:
    if audit.context:
        names = ", ".join(sorted(audit.context))
        return (f"'{symbol}' 依赖源模块上下文 [{names}]；迁入后这些值将"
                "属于目标模块，模块身份、动态导入或资源定位语义会改变。"
                "请先改为显式参数或不依赖模块上下文的实现")
    if audit.writes:
        names = ", ".join(sorted(audit.writes))
        return (f"'{symbol}' 含模块全局写 [{names}]；迁入后写入会落到"
                "目标模块，源模块及其保留代码则继续读取原模块状态，"
                "无法保持共享状态语义。请先改为显式状态参数/返回值，"
                "或连同状态所有者一起调整迁移边界")
    if audit.mutations:
        names = ", ".join(sorted(audit.mutations))
        return (f"'{symbol}' 原地改写源模块级状态 [{names}]；迁入后改写会"
                "落到目标模块的同名对象，源模块保留代码仍读写原对象，"
                "共享状态会静默分叉。请先改为显式状态参数/返回值，"
                "或连同状态所有者一起调整迁移边界")
    if audit.ambiguous:
        names = ", ".join(sorted(audit.ambiguous))
        return (f"'{symbol}' 的依赖 [{names}] 在源/目标中均有同名绑定，"
                "但无法证明绑定身份一致；直接迁入会改变全局或内建名的"
                "解析结果。请先迁移依赖、统一实现或重命名冲突绑定")
    return _missing_dependency_reason(audit.missing, symbol)
def _missing_dependency_reason(missing_deps: frozenset[str],
                                symbol: str) -> str | None:
    if missing_deps:
        names = ", ".join(sorted(missing_deps))
        return (f"'{symbol}' 依赖源文件模块级定义 [{names}]，迁入片段不会"
                "携带这些定义，目标文件也缺少同名绑定；直接迁入会在运行期 "
                "NameError。请先迁移这些依赖后重试")
    return None
def _candidate_identity(candidate: Any) -> tuple[str, str] | None:
    symbol = getattr(candidate, "symbol", None)
    source_text = _path_text(getattr(candidate, "source_file", None))
    if isinstance(symbol, str) and symbol and source_text:
        return symbol, source_text
    return None
def _candidate_symbol(candidate: Any) -> str:
    symbol = getattr(candidate, "symbol", "")
    return symbol if isinstance(symbol, str) else ""
def _normalize_source_files_index(
    source_files: dict[str, str],
) -> dict[str, str]:
    index: dict[str, str] = {}
    if not isinstance(source_files, dict):
        _log.warning("source_files 载荷非映射,按空索引处理: %s",
                     type(source_files).__name__)
        return index
    for fp, code in source_files.items():
        filepath = _path_text(fp)
        if not filepath:
            _log.warning("source_files 含非路径键，已跳过: %r", fp)
            continue
        if not isinstance(code, str):
            _log.warning(
                "source_files 载荷非 str 源码,按缺失处理: %s: %r",
                filepath, type(code).__name__)
            continue
        index[norm_cache_key(filepath)] = code
    return index
def batch_migrate_in(
    candidates: list[MigrationCandidate],
    source_files: dict[str, str],
    target_code: str,
) -> list[MigrateInResult]:
    results: list[MigrateInResult] = []
    current_target = target_code
    migrated_symbols: dict[str, set[str]] = {}
    source_index = _normalize_source_files_index(source_files)
    if (isinstance(candidates, (list, tuple))
            or (isinstance(candidates, Iterable)
                and not isinstance(candidates,
                                   (str, bytes, bytearray, dict)))):
        candidate_list = list(candidates)
    else:
        if candidates is not None:
            _log.warning("批量迁入: candidates 非候选序列(%s)，按空清单处理",
                         type(candidates).__name__)
        candidate_list = []
    for candidate in candidate_list:
        identity = _candidate_identity(candidate)
        if identity is None:
            _log.warning("[Migration] 候选条目形态非法(须含 str 型 symbol/"
                         "source_file),跳过迁入: %s",
                         type(candidate).__name__)
            results.append(MigrateInResult(
                success=False, symbol=_candidate_symbol(candidate),
                reason=("候选条目形态非法（须含 str 型 symbol/source_file）"
                        f"，跳过迁入: {type(candidate).__name__}"),
            ))
            continue
        symbol, source_fp = identity
        source_key = norm_cache_key(source_fp)
        source_code = source_index.get(source_key)
        if source_code is None:
            results.append(MigrateInResult(
                success=False, symbol=symbol,
                reason=f"源文件 {source_fp} 不在 source_files 中",
            ))
            continue
        try:
            result = execute_migrate_in(
                source_code,
                current_target,
                symbol,
                source_file=source_fp,
                target_file=_path_text(getattr(candidate, "target_file", "")),
                _migrated_symbols=frozenset(
                    migrated_symbols.get(source_key, ())),
            )
        except ContractViolationError as _cve:
            log_swallowed(__name__, _cve,
                          context=f'batch_migrate_in:{type(_cve).__name__}')
            results.append(MigrateInResult(
                success=False, symbol=candidate.symbol,
                reason=f"迁入产物破坏 valid_syntax 不变量，已跳过该符号: {_cve}",
            ))
            continue
        if result.success:
            result.base_target_code = target_code
            current_target = result.target_code
            migrated_symbols.setdefault(source_key, set()).add(symbol)
        results.append(result)
    return results
def norm_cache_key(skill_dir: str) -> str:
    return os.path.normcase(os.path.normpath(
        os.path.realpath(os.path.abspath(skill_dir))))
_CODE_MISSING = object()
def _spec_code_value(after_state: dict):
    if "code" in after_state:
        return after_state["code"]
    if "source" in after_state:
        return after_state["source"]
    return _CODE_MISSING
def _verify_valid_syntax(after_state: dict, func_id: str) -> None:
    code_val = _spec_code_value(after_state)
    if code_val is _CODE_MISSING:
        raise ContractViolationError(
            f"不变性违反(valid_syntax): {func_id} 缺少 code/source 载荷，"
            "无法证明变更后代码可编译")
    if code_val == "":
        return
    if not isinstance(code_val, str):
        raise ContractViolationError(
            f"不变性违反(valid_syntax): {func_id} 变更后代码"
            f"须为 str 源码文本，得到 {type(code_val).__name__}"
        )
    try:
        compile(code_val, f"<immunity:{func_id}>", "exec")
    except PARSE_DEGRADE_EXC as exc:
        log_swallowed(__name__, exc,
                      context=f"_verify_valid_syntax:{type(exc).__name__}")
        raise ContractViolationError(
            f"不变性违反(valid_syntax): {func_id} 变更后代码存在语法错误: "
            f"{type(exc).__name__}: {exc}") from exc
def _verify_dir_exists(after_state: dict, func_id: str, key: str) -> None:
    if key not in after_state:
        raise ContractViolationError(
            f"不变性违反({key}_exists): {func_id} 缺少 {key} 载荷，"
            "无法证明目录存在")
    dir_val = after_state.get(key)
    if dir_val is None:
        raise ContractViolationError(
            f"不变性违反({key}_exists): {func_id} 变更后 {key} 为 null"
        )
    try:
        path_text = os.fsdecode(os.fspath(dir_val))
    except (TypeError, UnicodeDecodeError) as exc:
        raise ContractViolationError(
            f"不变性违反({key}_exists): {func_id} 变更后 {key} 非路径形态"
            f"（{type(dir_val).__name__}）"
        ) from exc
    if not os.path.isdir(path_text):
        raise ContractViolationError(
            f"不变性违反({key}_exists): {func_id} 变更后 {key} 不存在: {dir_val}"
        )
def _secret_name_alt(key: str) -> str:
    return r"[_-]?".join(
        re.escape(part) for part in key.split("_") if part)
_SECRET_NAME_ALTS = tuple(
    _secret_name_alt(k) for k in SENSITIVE_NAME_KEYWORDS if k)
_SECRET_NAME_RE = (
    re.compile("(?:" + "|".join(_SECRET_NAME_ALTS) + r")\Z",
               re.IGNORECASE)
    if _SECRET_NAME_ALTS else None
)
def _secret_target_names(target: ast.AST) -> Iterator[str]:
    if isinstance(target, ast.Name):
        yield target.id
    elif isinstance(target, ast.Attribute):
        yield target.attr
    elif isinstance(target, ast.Subscript):
        key = _static_text_literal(target.slice)
        if isinstance(key, str):
            yield key
    elif isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            yield from _secret_target_names(element)
    elif isinstance(target, ast.Starred):
        yield from _secret_target_names(target.value)
def _sensitive_name(name: str) -> bool:
    return (_SECRET_NAME_RE is not None
            and _SECRET_NAME_RE.search(name) is not None)
def _targets_contain_secret(targets: Iterable[ast.AST]) -> bool:
    return any(
        _sensitive_name(name)
        for target in targets
        for name in _secret_target_names(target)
    )
def _static_text_literal(node: ast.AST | None) -> str | bytes | None:
    if isinstance(node, ast.Constant):
        return node.value if isinstance(node.value, (str, bytes)) else None
    if isinstance(node, ast.FormattedValue):
        value = _static_text_literal(node.value)
        if value is None:
            return None
        if node.conversion == -1 or node.conversion == ord("s"):
            converted = str(value)
        elif node.conversion == ord("r"):
            converted = repr(value)
        elif node.conversion == ord("a"):
            converted = ascii(value)
        else:
            return None
        if node.format_spec is None:
            return converted
        spec = _static_text_literal(node.format_spec)
        if not isinstance(spec, str):
            return None
        try:
            return format(converted, spec)
        except (TypeError, ValueError) as exc:
            raise ContractViolationError(
                f"静态 f-string 格式说明非法: {spec!r}") from exc
    if isinstance(node, ast.JoinedStr):
        parts: list[str] = []
        for value in node.values:
            part = _static_text_literal(value)
            if not isinstance(part, str):
                return None
            parts.append(part)
        return "".join(parts)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left = _static_text_literal(node.left)
        right = _static_text_literal(node.right)
        if left is not None and right is not None and type(left) is type(right):
            return left + right
    return None
def _literal_secret_value(node: ast.AST | None) -> bool:
    text = _static_text_literal(node)
    if text is not None:
        return bool(text.strip())
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return any(_literal_secret_value(elt) for elt in node.elts)
    return False
def _arguments_contain_secret_default(arguments: ast.arguments) -> bool:
    positional = [*arguments.posonlyargs, *arguments.args]
    default_count = len(arguments.defaults)
    default_pairs = (
        zip(positional[len(positional) - default_count:],
            arguments.defaults, strict=False)
        if default_count else ()
    )
    if any(_sensitive_name(arg.arg) and _literal_secret_value(default)
           for arg, default in default_pairs):
        return True
    return any(
        default is not None
        and _sensitive_name(arg.arg)
        and _literal_secret_value(default)
        for arg, default in zip(
            arguments.kwonlyargs, arguments.kw_defaults, strict=False)
    )
def _dict_contains_secret(node: ast.Dict) -> bool:
    for key, value in zip(node.keys, node.values, strict=False):
        key_text = _static_text_literal(key)
        if (isinstance(key_text, str) and _sensitive_name(key_text)
                and _literal_secret_value(value)):
            return True
    return False
def _secret_node_hit(node: ast.AST) -> bool | None:
    if isinstance(node, ast.keyword):
        return bool(node.arg and _sensitive_name(node.arg)
                    and _literal_secret_value(node.value))
    if isinstance(node, ast.Dict):
        return _dict_contains_secret(node)
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        return _arguments_contain_secret_default(node.args)
    return None
def _assignment_parts(node: ast.AST) -> tuple[list[ast.AST], ast.AST | None] | None:
    if isinstance(node, ast.Assign):
        return list(node.targets), node.value
    if isinstance(node, ast.AnnAssign):
        return ([node.target] if node.value is not None else []), node.value
    if isinstance(node, (ast.NamedExpr, ast.AugAssign)):
        return [node.target], node.value
    return None
def _code_contains_secret_assignment(tree: ast.AST) -> bool:
    for node in walk_nodes(tree):
        hit = _secret_node_hit(node)
        if hit is not None:
            if hit:
                return True
            continue
        parts = _assignment_parts(node)
        if parts is None:
            continue
        targets, value = parts
        if _targets_contain_secret(targets) and _literal_secret_value(value):
            return True
    return False
def _verify_no_secrets(after_state: dict, func_id: str) -> None:
    code_val = _spec_code_value(after_state)
    if code_val is _CODE_MISSING:
        raise ContractViolationError(
            f"不变性违反(no_secrets): {func_id} 缺少 code/source 载荷，"
            "无法证明未包含硬编码密钥")
    if code_val == "":
        return
    if not isinstance(code_val, str):
        raise ContractViolationError(
            f"不变性违反(no_secrets): {func_id} 变更后代码须为 str 源码文本，"
            f"得到 {type(code_val).__name__}"
        )
    try:
        tree = ast.parse(code_val)
    except PARSE_DEGRADE_EXC as exc:
        raise ContractViolationError(
            f"不变性违反(no_secrets): {func_id} 源码无法解析，"
            "无法证明未包含硬编码密钥"
        ) from exc
    if _code_contains_secret_assignment(tree):
        raise ContractViolationError(
            f"不变性违反(no_secrets): {func_id} 变更后代码包含硬编码密钥"
        )
def _verify_key_equals(after_state: dict, func_id: str,
                       spec_stripped: str) -> None:
    key, expected_val = spec_stripped.split("=", 1)
    key = key.strip()
    expected_val = expected_val.strip()
    actual_val = str(after_state.get(key, ""))
    if actual_val != expected_val:
        raise ContractViolationError(
            f"不变性违反({spec_stripped}): {func_id} 变更后 {key}={actual_val!r}, 期望 {expected_val!r}"
        )
def _verify_nonempty(after_state: dict, func_id: str,
                     spec_stripped: str) -> None:
    val = after_state.get(spec_stripped)
    empty_container = (
        isinstance(val, (list, tuple, dict, set, frozenset, bytes, bytearray))
        and not val
    )
    if (val is None or (isinstance(val, str) and not val.strip())
            or empty_container):
        raise ContractViolationError(
            f"不变性违反({spec_stripped}): {func_id} 变更后 {spec_stripped} 为空或不存在"
        )
_IMMUNITY_SPEC_HANDLERS: dict[str, Callable[[dict, str], None]] = {
    "valid_syntax": _verify_valid_syntax,
    "output_dir_exists": lambda after_state, func_id: _verify_dir_exists(
        after_state, func_id, "output_dir"),
    "skill_dir_exists": lambda after_state, func_id: _verify_dir_exists(
        after_state, func_id, "skill_dir"),
    "no_secrets": _verify_no_secrets,
}
def _check_immunity_spec(spec_stripped: str, after_state: dict,
                         func_id: str) -> None:
    handler = _IMMUNITY_SPEC_HANDLERS.get(spec_stripped)
    if handler is not None:
        handler(after_state, func_id)
        return
    if "=" in spec_stripped:
        _verify_key_equals(after_state, func_id, spec_stripped)
        return
    _verify_nonempty(after_state, func_id, spec_stripped)
def _normalize_invariant_specs(raw: Any, func_id: str) -> list[str]:
    if isinstance(raw, str):
        return [raw] if raw.strip() else []
    if isinstance(raw, (bytes, bytearray)) or not isinstance(raw, Iterable):
        raise ContractViolationError(
            f"不变性声明须为 str 或 str 序列: {func_id} 得到 {type(raw).__name__}"
        )
    return list(raw)
class ChangeImmunity:
    _invariants: ClassVar[dict[str, list[str]]] = {}
    @classmethod
    def declare(cls, func_id: str, invariants) -> None:
        cls._invariants[func_id] = _normalize_invariant_specs(invariants, func_id)
    @classmethod
    def verify(cls, func_id: str, after_state: dict) -> None:
        specs = cls._invariants.get(func_id, [])
        if not specs:
            _log.debug("ChangeImmunity.verify: 操作 %r 未声明不变性, 跳过检查", func_id)
            return
        if not isinstance(after_state, dict):
            raise ContractViolationError(
                f"不变性检查载荷须为 dict: {func_id} 得到 "
                f"{type(after_state).__name__}"
            )
        for spec in specs:
            if not isinstance(spec, str):
                raise ContractViolationError(
                    f"不变性声明项须为 str: {func_id} 得到 {type(spec).__name__}"
                )
            _check_immunity_spec(spec.strip(), after_state, func_id)
    @classmethod
    def verify_decorated(cls, func: Callable, after_state: dict) -> None:
        specs = list(getattr(func, "_immutability_specs", []) or [])
        func_id = (f"{getattr(func, '__module__', '<unknown>')}"
                   f".{getattr(func, '__qualname__', getattr(func, '__name__', '<func>'))}")
        if specs:
            cls._invariants.setdefault(func_id, specs)
        cls.verify(func_id, after_state)
__all__ = [
    'ChangeImmunity',
    'ConsumptionEntry',
    'MergeCleanupPlan',
    'MigrateInResult',
    'MigrationCandidate',
    'MigrationVerdict',
    'PostMergeCleaner',
    'analyze_file_consumption',
    'assemble_merged_source',
    'batch_migrate_in',
    'build_global_consumption_map',
    'execute_migrate_in',
    'find_migration_candidates',
    'get_consumers_for_symbol',
    'get_consumption_map',
    'get_zero_consumer_checker',
    'immutable',
    'invalidate_consumption_cache',
    'invalidate_zcc_cache',
    'judge_migration',
    'norm_cache_key',
    'plan_post_merge_cleanup',
    'prepare_migrate_in',
    'retained_source_reference_blocks',
]
_log.info(
    "refactor_migration_prepare 迁移预览域已加载: %d 项导出",
    len(__all__))

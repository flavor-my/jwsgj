from __future__ import annotations

import ast
import builtins as _builtins
import copy
import errno
import logging
import os
from dataclasses import dataclass, field
from importlib import import_module
from typing import Any

from jwsgj.diag_shared_ast_bindings import build_module_symbol_table
from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    TYPE_ALIAS_NODES,
    annassign_target_names,
    collect_param_names,
    definition_binding_name,
    first_segment,
    import_alias_bound_names,
    is_star_import,
    is_type_checking_guard,
    iter_arg_nodes,
    iter_def_site_nodes,
    iter_module_level_stmts,
    iter_unpack_target_names,
    main_guard_branch,
    module_postpones_annotations,
    parse_source_tree,
    pattern_capture_name,
    type_checking_body_node_ids,
)
from jwsgj.diag_shared_ast_surface import collect_module_exports_state
from jwsgj.diag_shared_source_core import (
    files_fingerprint,
    load_source_tree,
    parse_py_file,
    read_source_with_fingerprint,
    resolve_module_name,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    PatternFinding,
    finding_scan_exempt,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    SPLIT_SAFETY_DIMENSION,
)
from jwsgj.diag_wiring_import_scan import (
    _HUB_THRESHOLD_DEFAULT,
    BareImport,
    DepthError,
    HubModule,
    _find_spec,
    _from_import_names,
    _is_marked_project_root,
    _is_package_dir,
    _is_temp_root,
    _package_dirs,
    _package_import_roots,
    check_GF16,
    check_GF18,
    collect_all_imports,
    collect_internal_modules,
    detect_bare_imports,
    detect_depth_errors,
    detect_hub_modules,
    iter_project_py_files,
    resolve_project_package,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import source_import_roots
from jwsgj.runtime_scope import (
    import_key,
    is_scan_py_name,
    is_under_root,
)

_log = logging.getLogger(__name__)
__all__ = [
    'CrossSkillDependencyDetector',
    'ImportSafetyReport',
    'ImportSafetyScanner',
    'TransitiveMissing',
    'check_SL06',
    'detect_cross_module_refs',
    'detect_transitive_missing',
    'import_check_payload',
    'print_import_chain_result',
    'print_report',
    'quick_check',
    'wiring_declarations',
]
_log.info("diag_wiring_symbol_scan 符号核验与扫描报告域已加载: %d 项导出",
          len(__all__))
@dataclass
class ImportSafetyReport:
    project_root: str
    total_files: int = 0
    bare_imports: list[BareImport] = field(default_factory=list)
    hub_modules: list[HubModule] = field(default_factory=list)
    depth_errors: list[DepthError] = field(default_factory=list)
    transitive_missing: list[TransitiveMissing] = field(default_factory=list)
    @property
    def total_issues(self) -> int:
        return (
            len(self.bare_imports)
            + len(self.hub_modules)
            + len(self.depth_errors)
            + len(self.transitive_missing)
        )
    def blocking(self) -> bool:
        return (_has_high_risk(self.bare_imports)
                or _has_high_risk(self.hub_modules)
                or bool(self.depth_errors))
_SCAN_CACHE: dict[str, tuple[tuple, ImportSafetyReport]] = {}
_SCAN_CACHE_MAX = 8
def _cache_lookup(cache_key: str,
                  signature: tuple) -> ImportSafetyReport | None:
    cached = _SCAN_CACHE.get(cache_key)
    if cached is not None and cached[0] == signature:
        return copy.deepcopy(cached[1])
    return None
def _cache_store(cache_key: str, signature: tuple,
                 report: ImportSafetyReport) -> None:
    if (cache_key not in _SCAN_CACHE
            and len(_SCAN_CACHE) >= _SCAN_CACHE_MAX):
        _SCAN_CACHE.pop(next(iter(_SCAN_CACHE)))
    _SCAN_CACHE[cache_key] = (signature, copy.deepcopy(report))
def _require_project_root(project_root, caller: str) -> None:
    try:
        raw = os.fspath(project_root)
    except TypeError:
        raise ValueError(
            f"{caller}: project_root 须为 str/PathLike，实际为 {project_root!r}"
        ) from None
    if not isinstance(raw, str) or not raw:
        raise ValueError(
            f"{caller}: project_root 须为非空 str/PathLike，实际为 {project_root!r}")
    if not os.path.isdir(raw):
        raise ValueError(f"{caller}: project_root 目录不存在: {project_root!r}")
def _has_high_risk(items) -> bool:
    return any(getattr(item, "risk", "") == "HIGH" for item in items)
def _dotted_module_path_exists(base_dir: str, target: str) -> bool:
    parts = [part for part in target.split('.') if part]
    if not parts:
        return False
    cur = base_dir
    last = len(parts) - 1
    for index, part in enumerate(parts):
        package_dir = os.path.join(cur, part)
        if os.path.isfile(os.path.join(package_dir, '__init__.py')):
            if index == last:
                return True
            cur = package_dir
            continue
        if os.path.isfile(os.path.join(cur, part + '.py')):
            return index == last
        if not os.path.isdir(package_dir):
            return False
        cur = package_dir
    return True
def _module_search_bases(project_root: str,
                         importer_dir: str | None) -> list[str]:
    bases = [project_root, *_package_import_roots(project_root)]
    if importer_dir and os.path.abspath(importer_dir) not in {
            os.path.abspath(base) for base in bases}:
        bases.append(importer_dir)
    return bases
def _module_target_unresolvable(target: str, internal_modules: set[str],
                                project_root: str,
                                importer_dir: str | None, *,
                                internal_required: bool) -> bool:
    if not internal_required and first_segment(target) not in internal_modules:
        return False
    bases = _module_search_bases(project_root, importer_dir)
    if any(_dotted_module_path_exists(base, target) for base in bases):
        return False
    if internal_required:
        return True
    if _module_source_path(
            first_segment(target), project_root, importer_dir) is not None:
        return True
    return _find_spec(target, quiet=True) is None
def _module_source_path(target: str, project_root: str,
                        importer_dir: str | None) -> str | None:
    parts = [part for part in target.split('.') if part]
    if not parts:
        return None
    for base in _module_search_bases(project_root, importer_dir):
        init_file = os.path.join(base, *parts, '__init__.py')
        if os.path.isfile(init_file):
            return init_file
        module_file = os.path.join(base, *parts) + '.py'
        if os.path.isfile(module_file):
            return module_file
    return None
def _imported_name_unresolvable(
    module: str, name: str, project_root: str, importer_dir: str | None,
    cache: dict[str, tuple[set[str], bool] | None] | None = None,
    *, internal_required: bool = False,
    type_checking_only: bool = False,
    static_cache: dict[str, tuple[set[str], bool] | None] | None = None,
) -> bool:
    submodule = f'{module}.{name}' if module else name
    if any(_dotted_module_path_exists(base, submodule)
           for base in _module_search_bases(project_root, importer_dir)):
        return False
    source_path = _module_source_path(module, project_root, importer_dir)
    if source_path is None:
        parts = [part for part in module.split('.') if part]
        if parts and any(
                os.path.isdir(os.path.join(base, *parts))
                for base in _module_search_bases(project_root, importer_dir)):
            if internal_required:
                return True
            return _find_spec(submodule, quiet=True) is None
        return False
    surface = (
        _ast_static_export_surface(source_path, static_cache)
        if type_checking_only else _ast_export_surface(source_path, cache))
    if surface is None:
        return False
    exports, open_surface = surface
    return not open_surface and name not in exports
def _verification_import_base(filepath: str, project_root: str) -> str:
    root = os.path.abspath(project_root)
    if _is_package_dir(root):
        return os.path.dirname(root)
    for source_root in source_import_roots(root):
        if is_under_root(filepath, source_root):
            return source_root
    return root
class ImportSafetyScanner:
    def __init__(self) -> None:
        self._hub_threshold = _HUB_THRESHOLD_DEFAULT
    def scan(self, project_root: str) -> ImportSafetyReport:
        _require_project_root(project_root, "ImportSafetyScanner.scan")
        cache_key = os.path.abspath(project_root)
        py_files = iter_project_py_files(project_root)
        signature = (files_fingerprint(py_files), self._hub_threshold)
        cached = _cache_lookup(cache_key, signature)
        if cached is not None:
            return cached
        report = ImportSafetyReport(project_root=cache_key)
        report.total_files = len(py_files)
        all_imports = collect_all_imports(py_files)
        internal_modules = collect_internal_modules(py_files, project_root)
        report.bare_imports = detect_bare_imports(
            py_files, internal_modules, project_root)
        report.hub_modules = detect_hub_modules(
            all_imports, project_root, hub_threshold=self._hub_threshold)
        report.depth_errors = detect_depth_errors(
            all_imports, internal_modules, project_root)
        report.transitive_missing = detect_transitive_missing(
            py_files, project_root)
        _cache_store(cache_key, signature, report)
        return report
    def verify_import_chain(self, project_root: str) -> tuple[bool, list[str]]:
        _require_project_root(
            project_root, "ImportSafetyScanner.verify_import_chain")
        py_files = iter_project_py_files(project_root)
        internal_modules = collect_internal_modules(py_files, project_root)
        root_package = resolve_project_package(project_root)[0]
        if root_package:
            internal_modules = {*internal_modules, root_package}
        surfaces: dict[str, tuple[set[str], bool] | None] = {}
        static_surfaces: dict[str, tuple[set[str], bool] | None] = {}
        type_checking_ranges: dict[str, list[tuple[int, int]]] = {}
        failures = []
        for filepath, imports in collect_all_imports(py_files).items():
            importer_dir = os.path.dirname(filepath)
            for line_no, stmt, target in imports:
                resolved_target = target
                is_relative = target.startswith('.')
                if is_relative:
                    resolved_target = _resolve_relative_import(
                        target, filepath,
                        _verification_import_base(filepath, project_root))
                if (resolved_target.startswith('.')
                        or _module_target_unresolvable(
                            resolved_target, internal_modules, project_root,
                            importer_dir, internal_required=is_relative)):
                    failures.append(
                        f"{os.path.relpath(filepath, project_root)}:"
                        f"{line_no}  target '{target}' not found")
                    continue
                if (not is_relative
                        and first_segment(resolved_target) not in internal_modules):
                    continue
                for name in _from_import_names(stmt):
                    if not _imported_name_unresolvable(
                            resolved_target, name, project_root, importer_dir,
                            surfaces, internal_required=is_relative):
                        continue
                    # TYPE_CHECKING-only 分支里的导入只在类型检查期解析，
                    # 运行期导出面会折叠该分支；改用静态面复核，避免误报。
                    if (_type_checking_only_import(
                            filepath, line_no, type_checking_ranges)
                            and not _imported_name_unresolvable(
                                resolved_target, name, project_root,
                                importer_dir, surfaces,
                                internal_required=is_relative,
                                type_checking_only=True,
                                static_cache=static_surfaces)):
                        continue
                    failures.append(
                        f"{os.path.relpath(filepath, project_root)}:"
                        f"{line_no}  target '{resolved_target}.{name}' not found")
        return not bool(failures), failures
def quick_check(project_root: str) -> dict:
    report = ImportSafetyScanner().scan(project_root)
    high_risk_bare = [b for b in report.bare_imports if b.risk == "HIGH"]
    high_risk_hub = [h for h in report.hub_modules if h.risk == "HIGH"]
    return {
        "project_root": report.project_root,
        "total_files": report.total_files,
        "high_risk_bare_imports": len(high_risk_bare),
        "high_risk_hub_modules": len(high_risk_hub),
        "depth_errors": len(report.depth_errors),
        "transitive_missing": len(report.transitive_missing),
        "blocking": report.blocking(),
        "bare_imports": [{"file": b.file, "line": b.line, "fix": b.suggested_fix} for b in high_risk_bare],
        "hub_modules": [{"module": h.module_path, "count": h.import_count} for h in high_risk_hub],
    }
_RISK_ORDER = {"HIGH": 0, "MEDIUM": 1}
def print_report(report: ImportSafetyReport) -> None:
    print("=" * 60)
    print(f"导入安全扫描报告: {report.project_root}")
    print("=" * 60)
    print(f"总文件: {report.total_files} | 总问题: {report.total_issues} | "
          f"阻断: {'是' if report.blocking() else '否'}")
    if report.bare_imports:
        _print_bare_imports(report.bare_imports)
    if report.hub_modules:
        _print_hub_modules(report.hub_modules)
    if report.depth_errors:
        _print_depth_errors(report.depth_errors)
    if report.transitive_missing:
        _print_transitive_missing(report.transitive_missing)
    print("\n" + "=" * 60)
def import_check_payload(report, chain_ok: bool, failures: list) -> dict:
    return {
        "project_root": report.project_root,
        "total_files": report.total_files,
        "total_issues": report.total_issues,
        "blocking": report.blocking(),
        "bare_imports": [
            {"file": b.file, "line": b.line, "risk": b.risk,
             "fix": b.suggested_fix} for b in report.bare_imports],
        "hub_modules": [
            {"module": h.module_path, "import_count": h.import_count,
             "risk": h.risk} for h in report.hub_modules],
        "depth_errors": [
            {"file": d.file, "line": d.line, "fix": d.fix}
            for d in report.depth_errors],
        "transitive_missing": [
            {"file": t.file, "line": t.line, "symbol": t.missing_symbol}
            for t in report.transitive_missing],
        "import_chain": {"ok": chain_ok,
                          "failures": failures[:50]},
    }
def print_import_chain_result(failures: list) -> None:
    if not failures:
        print("\n-- 导入链完整性: PASS --")
        return
    print(f"\n-- 导入链完整性: FAIL ({len(failures)} 处断裂) --")
    for item in failures[:10]:
        print(f"  {item}")
def _print_bare_imports(items: list[BareImport]) -> None:
    print(f"\n-- GF-16 裸导入 ({len(items)}个) --")
    for bi in sorted(items, key=lambda x: _RISK_ORDER.get(x.risk, 9)):
        print(f"  [{bi.risk}] {bi.file}:{bi.line}  {bi.import_stmt}")
        print(f"         -> {bi.suggested_fix}")
def _print_hub_modules(items: list[HubModule]) -> None:
    print(f"\n-- GF-17 枢纽模块 ({len(items)}个) --")
    for hm in items:
        print(f"  [{hm.risk}] {hm.module_path} "
              f"(被{hm.import_count}个模块引用)")
        for ri in hm.relative_imports[:3]:
            print(f"         {ri}")
def _print_depth_errors(items: list[DepthError]) -> None:
    print(f"\n-- GF-18 深度错误 ({len(items)}个) --")
    for de in items:
        print(f"  {de.file}:{de.line}  {de.import_stmt}")
        print(f"        当前深度{de.current_depth}, "
              f"用了{de.dots_used}点, 应为{de.expected_dots}点")
        print(f"        修复: {de.fix}")
def _print_transitive_missing(items: list[TransitiveMissing]) -> None:
    print(f"\n-- GF-19 传递缺失 ({len(items)}个) --")
    for tm in items:
        print(f"  {tm.file}:{tm.line}  缺失: {tm.missing_symbol}")
if hasattr(ast, "Match"):
    _MATCH_BIND_NODES = (ast.MatchAs, ast.MatchStar)
    _MATCH_MAPPING_TYPES = (ast.MatchMapping,)
else:
    _MATCH_BIND_NODES = ()
    _MATCH_MAPPING_TYPES = ()
_STAR_IMPORT_DEFAULT = False
def _get_module_exports(
    module_path: str, *, star_import: bool = _STAR_IMPORT_DEFAULT,
) -> set[str] | None:
    try:
        module = import_module(module_path)  # lazy-by-design — 插件/注册表按名装载，静态导入会破坏插件边界
        if not star_import:
            return set(dir(module))
        try:
            declared_all = module.__all__
        except AttributeError:
            return {name for name in dir(module) if not name.startswith('_')}
        return set(declared_all)
    except (KeyboardInterrupt, SystemExit):
        raise
    except Exception as e:  # noqa: BLE001 — 插件失败留痕后回退静态导出面
        _log.debug("无法导入模块 %s: %s", module_path, e)
        log_swallowed(
            __name__, e, context=f'_get_module_exports:{type(e).__name__}')
        return _fallback_exports_from_spec(
            module_path, star_import=star_import)
#: ``_exports_from_tree`` 的记忆化表。
#:
#: 导出面只是**树的纯函数**（与文件路径、扫描轮次无关）。实测单个文件会
#: 为同一个被导入模块重复推导 7~88 次（跨文件更多），每次都是一次整树
#: 符号表构建。键用弱引用，值只存 ``frozenset[str]``——**值里不引用树**，
#: 因此不会像父子映射那样形成「弱键 → 强值 → 键」的引用环，可安全常驻。
_EXPORTS_FROM_TREE_CACHE: Any = None

def _exports_from_tree(
    tree: ast.AST, *, star_import: bool = _STAR_IMPORT_DEFAULT,
) -> set[str] | None:
    global _EXPORTS_FROM_TREE_CACHE
    cache = _EXPORTS_FROM_TREE_CACHE
    if cache is None:
        from weakref import WeakKeyDictionary
        cache = _EXPORTS_FROM_TREE_CACHE = WeakKeyDictionary()
    try:
        per_flag = cache.get(tree)
    except TypeError:  # 不可弱引用对象（如自定义 AST 包装），退化为直算
        per_flag = None
        cache = None
    if per_flag is not None and star_import in per_flag:
        memo = per_flag[star_import]
        return None if memo is None else set(memo)
    exports, open_surface = _module_export_surface(tree)
    if star_import:
        if '__all__' in exports:
            declared_all, exact = collect_module_exports_state(tree)
            result = declared_all if exact else None
        elif open_surface:
            result = None
        else:
            result = {name for name in exports if not name.startswith('_')}
    else:
        result = None if open_surface else exports
    if cache is not None:
        try:
            per_flag = cache.get(tree)
            if per_flag is None:
                per_flag = {}
                cache[tree] = per_flag
            per_flag[star_import] = None if result is None else frozenset(result)
        except TypeError:
            pass
    return result
def _fallback_exports_from_spec(
    module_path: str, *, star_import: bool = _STAR_IMPORT_DEFAULT,
) -> set[str] | None:
    spec = _find_spec(module_path, quiet=True)
    if not (spec and spec.origin and os.path.isfile(spec.origin)):
        return None
    _source, tree = parse_py_file(spec.origin, quiet=True)
    if tree is None:
        return None
    return _exports_from_tree(tree, star_import=star_import)
def _local_module_exports(
    module: str, filepath: str, base_path: str | None, *,
    star_import: bool = _STAR_IMPORT_DEFAULT,
) -> set[str] | None:
    if not (filepath and base_path):
        return None
    source_path = _module_source_path(
        module, base_path, os.path.dirname(filepath))
    if source_path is None:
        return None
    _source, tree = parse_py_file(source_path, quiet=True)
    if tree is None:
        return None
    return _exports_from_tree(tree, star_import=star_import)
def _with_binding_names(node: ast.AST) -> set[str]:
    return {name for item in node.items if item.optional_vars is not None
            for name in iter_unpack_target_names(item.optional_vars)}
def _import_binding_names(node: ast.AST) -> set[str]:
    return set(import_alias_bound_names(node))
def _type_alias_binding(node: ast.AST) -> set[str]:
    target = getattr(node, "name", None)
    return {target.id} if isinstance(target, ast.Name) else set()
def _iteration_target_binding_names(node: ast.AST) -> set[str]:
    return set(iter_unpack_target_names(node.target))
def _dispatch_by_type(handlers: dict[type, Any], node: ast.AST) -> set[str]:
    handler = handlers.get(type(node))
    return handler(node) if handler is not None else set()
def _runtime_type_checking_branch(node: ast.If) -> list[ast.stmt] | None:
    if is_type_checking_guard(node.test):
        return node.orelse
    if (isinstance(node.test, ast.UnaryOp)
            and isinstance(node.test.op, ast.Not)
            and is_type_checking_guard(node.test.operand)):
        return node.body
    return None
def _type_checking_only_branch(node: ast.If) -> list[ast.stmt] | None:
    """返回 ``node`` 中「仅类型检查期执行」的分支（运行期永不执行）。

    ``TYPE_CHECKING`` 在运行期恒为 ``False``，因此正极性守卫的 ``body``、
    取反守卫的 ``orelse`` 都只对类型检查器可见；运行期导出面会把这些分支
    整体折叠掉，从而把其中合法的 type-only 导入误判成「符号不存在」。
    """
    runtime_branch = _runtime_type_checking_branch(node)
    if runtime_branch is None:
        return None
    return node.orelse if runtime_branch is node.body else node.body


def _type_checking_only_line_ranges(tree: ast.AST) -> list[tuple[int, int]]:
    """收集 TYPE_CHECKING-only 分支的行号区间，供按行号判定导入语境。"""
    ranges: list[tuple[int, int]] = []
    for node in walk_nodes(tree):
        if not isinstance(node, ast.If):
            continue
        branch = _type_checking_only_branch(node)
        if not branch:
            continue
        starts = [int(getattr(stmt, "lineno", 0) or 0) for stmt in branch]
        ends = [int(getattr(stmt, "end_lineno", 0) or 0) for stmt in branch]
        start, end = min(starts), max(ends)
        if start and end:
            ranges.append((start, end))
    return ranges


def _type_checking_only_import(filepath: str, lineno: int,
                               cache: dict[str, list[tuple[int, int]]]) -> bool:
    """判断 ``filepath:lineno`` 的导入是否位于 TYPE_CHECKING-only 分支。"""
    ranges = cache.get(filepath)
    if ranges is None:
        _source, tree = parse_py_file(filepath, quiet=True)
        ranges = (_type_checking_only_line_ranges(tree)
                  if tree is not None else [])
        cache[filepath] = ranges
    return any(start <= lineno <= end for start, end in ranges)


def _runtime_if_branch(node: ast.If) -> list[ast.stmt] | None:
    type_checking_branch = _runtime_type_checking_branch(node)
    if type_checking_branch is not None:
        return type_checking_branch
    test = node.test
    negated = (isinstance(test, ast.UnaryOp)
               and isinstance(test.op, ast.Not))
    if negated:
        test = test.operand
    if isinstance(test, ast.Constant):
        condition = bool(test.value)
    else:
        main_branch = main_guard_branch(test)
        if main_branch is None:
            return None
        condition = not main_branch
    if negated:
        condition = not condition
    return node.body if condition else node.orelse
def _runtime_child_nodes(node: ast.AST):
    if isinstance(node, ast.If):
        branch = _runtime_if_branch(node)
        if branch is not None:
            return branch
    return ast.iter_child_nodes(node)
def _iter_runtime_nodes(tree: ast.AST):
    stack = [tree]
    while stack:
        node = stack.pop()
        yield node
        stack.extend(_runtime_child_nodes(node))
def _scope_namedexpr_binds(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    body = getattr(tree, "body", ())
    if isinstance(body, ast.AST):
        body = (body,)
    stack: list[ast.AST] = list(body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            stack.extend(iter_def_site_nodes(node))
            continue
        if isinstance(node, ast.NamedExpr) and isinstance(node.target, ast.Name):
            names.add(node.target.id)
        stack.extend(_runtime_child_nodes(node))
    return names
def _module_export_surface(tree: ast.AST) -> tuple[set[str], bool]:
    runtime_tree = _runtime_module_surface_tree(tree)
    bindings = (set(build_module_symbol_table(runtime_tree))
                | _scope_namedexpr_binds(runtime_tree))
    module_stmts = list(iter_module_level_stmts(runtime_tree))
    open_surface = (
        "__getattr__" in _scope_local_defined_names(runtime_tree)
        or any(is_star_import(node) for node in module_stmts))
    return bindings, open_surface


def _subtree_bound_names(node: ast.AST) -> set[str]:
    """收集子树内所有绑定名（用于 type-only 分支的静态可见面）。"""
    names: set[str] = set()
    for sub in walk_nodes(node):
        if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef)):
            names.add(sub.name)
        elif isinstance(sub, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            targets = (sub.targets if isinstance(sub, ast.Assign)
                       else [sub.target])
            for target in targets:
                names.update(iter_unpack_target_names(target))
        elif isinstance(sub, (ast.Import, ast.ImportFrom)):
            names.update(import_alias_bound_names(sub))
        elif isinstance(sub, ast.ExceptHandler) and sub.name:
            names.add(sub.name)
    return names


def _type_checking_only_bound_names(tree: ast.AST) -> set[str]:
    """收集 TYPE_CHECKING-only 分支内绑定的名字。"""
    names: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.If):
            continue
        branch = _type_checking_only_branch(node)
        if not branch:
            continue
        for stmt in branch:
            names |= _subtree_bound_names(stmt)
    return names


def _static_export_surface(tree: ast.AST) -> tuple[set[str], bool]:
    """含 TYPE_CHECKING 分支的静态导出面。

    与 `_module_export_surface`（运行期面）互补：type-only 导入只在类型检查期
    解析，必须用未折叠 TYPE_CHECKING 分支的面来校验，否则合法导入会被误报。
    """
    bindings = (set(build_module_symbol_table(tree))
                | _scope_namedexpr_binds(tree)
                | _type_checking_only_bound_names(tree))
    module_stmts = list(iter_module_level_stmts(tree))
    open_surface = (
        "__getattr__" in _scope_local_defined_names(tree)
        or any(is_star_import(node) for node in module_stmts))
    return bindings, open_surface


def _ast_export_surface(
    filepath: str,
    cache: dict[str, tuple[set[str], bool] | None] | None = None,
) -> tuple[set[str], bool] | None:
    if cache is not None and filepath in cache:
        return cache[filepath]
    _source, tree = parse_py_file(filepath, quiet=True)
    surface = None if tree is None else _module_export_surface(tree)
    if cache is not None:
        cache[filepath] = surface
    return surface
def _ast_static_export_surface(
    filepath: str,
    cache: dict[str, tuple[set[str], bool] | None] | None = None,
) -> tuple[set[str], bool] | None:
    """含 TYPE_CHECKING 分支的静态导出面（type-only 导入校验专用）。"""
    if cache is not None and filepath in cache:
        return cache[filepath]
    _source, tree = parse_py_file(filepath, quiet=True)
    surface = None if tree is None else _static_export_surface(tree)
    if cache is not None:
        cache[filepath] = surface
    return surface


def _is_submodule_of(package: str, name: str) -> bool:
    return _find_spec(f"{package}.{name}", quiet=True) is not None
def _resolve_relative_import(
    module_name: str,
    filepath: str,
    base_path: str = ""
) -> str:
    if not module_name.startswith('.'):
        return module_name
    level = len(module_name) - len(module_name.lstrip('.'))
    rest = module_name[level:]
    if filepath and base_path:
        return _resolve_anchored_module(filepath, base_path, level, rest, module_name)
    return module_name
def _resolve_anchored_module(filepath: str, base_path: str, level: int,
                             rest: str, module_name: str) -> str:
    try:
        rel = os.path.relpath(filepath, base_path)
    except ValueError as _e:
        log_swallowed(
            __name__, _e,
            context=f'_resolve_anchored_module:{type(_e).__name__}')
        return module_name
    _rel_norm = rel.replace(os.sep, '/')
    parts = (_rel_norm.rsplit('/', 1)[0] if '/' in _rel_norm else '').split('/')
    if level > len(parts):
        return module_name
    parts = parts[:len(parts) - level + 1]
    if '..' in parts:
        return module_name
    pkg = '.'.join(p for p in parts if p)
    if not pkg:
        return module_name
    return f"{pkg}.{rest}" if rest else pkg
_BUILTIN_NAMES = frozenset(dir(_builtins))
def _pattern_binding_names(child: ast.AST) -> set[str]:
    name = pattern_capture_name(child)
    return {name} if name else set()
def _defined_assignment_names(child: ast.AST) -> set[str]:
    if isinstance(child, ast.Assign):
        return set(iter_unpack_target_names(child.targets))
    return annassign_target_names(child)
def _namedexpr_binding_name(child: ast.NamedExpr) -> set[str]:
    return {child.target.id} if isinstance(child.target, ast.Name) else set()
_DEFINED_NAME_HANDLERS = {
    ast.FunctionDef: definition_binding_name,
    ast.AsyncFunctionDef: definition_binding_name,
    ast.ClassDef: definition_binding_name,
    ast.Import: _import_binding_names,
    ast.ImportFrom: _import_binding_names,
    ast.Assign: _defined_assignment_names,
    ast.AnnAssign: _defined_assignment_names,
    ast.For: _iteration_target_binding_names,
    ast.AsyncFor: _iteration_target_binding_names,
    ast.With: _with_binding_names,
    ast.AsyncWith: _with_binding_names,
    ast.NamedExpr: _namedexpr_binding_name,
    ast.ExceptHandler: _pattern_binding_names,
    **dict.fromkeys(_MATCH_BIND_NODES, _pattern_binding_names),
    **dict.fromkeys(_MATCH_MAPPING_TYPES, _pattern_binding_names),
    **dict.fromkeys(TYPE_ALIAS_NODES, _type_alias_binding),
}
def _scope_local_defined_names(scope: ast.AST) -> set[str]:
    names = (collect_param_names(scope)
             if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.Lambda)) else set())
    body = getattr(scope, "body", ())
    if isinstance(body, ast.AST):
        body = (body,)
    stack = list(body)
    while stack:
        child = stack.pop()
        if (isinstance(child, ast.AnnAssign)
                and isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))):
            names |= annassign_target_names(child, include_unassigned=True)
        elif not isinstance(child, (ast.Lambda, ast.comprehension)):
            names |= _dispatch_by_type(_DEFINED_NAME_HANDLERS, child)
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef, ast.Lambda)):
            stack.extend(iter_def_site_nodes(child))
            continue
        stack.extend(_runtime_child_nodes(child))
    return names
def _infer_base_path(filepath: str) -> str | None:
    d = os.path.dirname(os.path.abspath(filepath))
    base = None
    while os.path.isfile(os.path.join(d, '__init__.py')):
        base = os.path.dirname(d)
        if base == d:
            break
        d = base
    if base is not None:
        return base
    project_root = _project_root_of(filepath)
    if not project_root:
        return None
    return _verification_import_base(filepath, project_root)
def _resolve_import_target(node: ast.ImportFrom, filepath: str,
                           base_path: str | None) -> str | None:
    if node.level == 0:
        return node.module
    if not (filepath and base_path):
        return None
    return _resolve_relative_import(
        '.' * node.level + (node.module or ''), filepath, base_path)
_ModuleExportCache = dict[tuple[str, bool, bool], set[str] | None]
def _module_exports_or_unknown(
    module: str, *, star_import: bool = _STAR_IMPORT_DEFAULT,
) -> set[str] | None:
    exports = _get_module_exports(module, star_import=star_import)
    if exports:
        return exports
    spec = _find_spec(module, quiet=True)
    return exports if spec is not None else None
def _cached_module_exports(
    module: str, checked_modules: _ModuleExportCache, *,
    star_import: bool = _STAR_IMPORT_DEFAULT, filepath: str = "",
    base_path: str | None = None, local_first: bool = False,
) -> set[str] | None:
    cache_key = (module, star_import, local_first)
    if cache_key not in checked_modules:
        local_path = (
            _module_source_path(
                module, base_path, os.path.dirname(filepath))
            if local_first and filepath and base_path else None)
        if local_path is not None:
            _source, tree = parse_py_file(local_path, quiet=True)
            exports = (None if tree is None else
                       _exports_from_tree(tree, star_import=star_import))
        else:
            exports = _module_exports_or_unknown(
                module, star_import=star_import)
            if exports is None:
                exports = _local_module_exports(
                    module, filepath, base_path, star_import=star_import)
        checked_modules[cache_key] = exports
    return checked_modules[cache_key]


def _cached_static_module_exports(
    module: str, cache: dict[tuple[str, bool], set[str] | None], *,
    filepath: str = "", base_path: str | None = None,
    local_first: bool = False,
) -> set[str] | None:
    """缓存「含 TYPE_CHECKING 分支」的本地模块导出面。

    只对能定位到源码的本地模块返回集合；外部模块返回 ``None`` 表示无法静态
    验证（调用方不得据此报错）。
    """
    cache_key = (module, local_first)
    if cache_key not in cache:
        local_path = (
            _module_source_path(
                module, base_path, os.path.dirname(filepath))
            if local_first and filepath and base_path else None)
        if local_path is None:
            cache[cache_key] = None
        else:
            _source, tree = parse_py_file(local_path, quiet=True)
            cache[cache_key] = (
                None if tree is None else _static_export_surface(tree)[0])
    return cache[cache_key]


def _star_universe_merge(tree: ast.AST, filepath: str,
                          base_path: str | None,
                          checked_modules: _ModuleExportCache,
                          defined_names: set[str]) -> bool:
    star_import_unknown = False
    for node in _iter_runtime_nodes(tree):
        if not is_star_import(node):
            continue
        module = _resolve_import_target(node, filepath, base_path)
        if module is None:
            star_import_unknown = True
            continue
        exports = _cached_module_exports(
            module, checked_modules, star_import=True,
            filepath=filepath, base_path=base_path,
            local_first=node.level > 0)
        if exports is not None:
            defined_names |= exports
        else:
            star_import_unknown = True
    return star_import_unknown
def _imported_symbol_finding(node: ast.ImportFrom, module: str, name: str,
                             exports: set[str], filepath: str,
                             base_path: str | None = None, *,
                             local_first: bool = False) -> dict[str, Any] | None:
    if name == '*' or name in exports:
        return None
    if not local_first and _is_submodule_of(module, name):
        return None
    if base_path and _module_source_path(
            f'{module}.{name}', base_path, os.path.dirname(filepath)) is not None:
        return None
    return {
        "check_id": "XR01",
        "pattern": "导入符号不存在",
        "lineno": node.lineno,
        "col": node.col_offset,
        "message": (
            f"from {module} import {name} — "
            f"'{name}' 不在 {module} 的导出列表中"
        ),
        "severity": "ERROR",
        "filepath": filepath,
        "suggestion": (
            f"检查 {module} 是否定义了 '{name}'，"
            f"或确认 __all__ 列表是否包含此符号"
        ),
    }
def _importfrom_findings(
        node: ast.ImportFrom, filepath: str, base_path: str | None,
        checked_modules: _ModuleExportCache, *,
        type_checking_only: bool = False,
        static_cache: dict[tuple[str, bool], set[str] | None] | None = None,
) -> list[dict[str, Any]]:
    module = _resolve_import_target(node, filepath, base_path)
    if module is None:
        return []
    local_first = node.level > 0 or bool(
        base_path and _module_source_path(
            module, base_path, os.path.dirname(filepath)) is not None)
    if type_checking_only:
        # type-only 导入只在类型检查期解析：运行期导出面会折叠 TYPE_CHECKING
        # 分支，必须改用未折叠的静态面，否则合法导入会被误报。
        exports = _cached_static_module_exports(
            module, {} if static_cache is None else static_cache,
            filepath=filepath, base_path=base_path, local_first=local_first)
        if exports is None:
            # 外部模块无法静态验证 type-only 导出，不做运行期符号断言。
            return []
    else:
        exports = _cached_module_exports(
            module, checked_modules, filepath=filepath, base_path=base_path,
            local_first=local_first)
    if exports is None or "__getattr__" in exports:
        return []
    findings = []
    for alias in node.names:
        finding = _imported_symbol_finding(
            node, module, alias.name, exports, filepath, base_path,
            local_first=local_first)
        if finding is not None:
            findings.append(finding)
    return findings
def _undefined_call_findings(node: ast.Call, defined_names: set[str],
                              star_import_unknown: bool,
                              filepath: str) -> list[dict[str, Any]]:
    if star_import_unknown:
        return []
    if not isinstance(node.func, ast.Name):
        return []
    func_name = node.func.id
    if func_name in _BUILTIN_NAMES:
        return []
    if func_name not in defined_names:
        return [{
            "check_id": "XR01",
            "pattern": "未定义函数调用",
            "lineno": node.lineno,
            "col": node.col_offset,
            "message": (
                f"调用 '{func_name}()' — "
                f"该函数未在当前模块中定义或导入"
            ),
            "severity": "WARNING",
            "filepath": filepath,
            "suggestion": f"添加 'from X import {func_name}' 或定义此函数",
        }]
    return []
def _node_findings(node: ast.AST, filepath: str, base_path: str | None,
                    checked_modules: _ModuleExportCache,
                    defined_names: set[str],
                    star_import_unknown: bool, *,
                    type_checking_only: bool = False,
                    static_cache: dict[tuple[str, bool], set[str] | None] | None = None,
) -> list[dict[str, Any]]:
    if isinstance(node, ast.ImportFrom):
        return _importfrom_findings(
            node, filepath, base_path, checked_modules,
            type_checking_only=type_checking_only,
            static_cache=static_cache)
    if isinstance(node, ast.Call):
        return _undefined_call_findings(
            node, defined_names, star_import_unknown, filepath)
    return []
_CALL_SCOPE_DEFINITION_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda,
)
def _visible_scope_names(
    chain: list[ast.AST], scope_names: dict[ast.AST, set[str]],
) -> set[str]:
    return {name for scope in chain for name in scope_names[scope]}
def _definition_annotation_ids(node: ast.AST) -> set[int]:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return set()
    annotations = [
        param.annotation for param in iter_arg_nodes(node.args)
        if param.annotation is not None
    ]
    if node.returns is not None:
        annotations.append(node.returns)
    return {id(annotation) for annotation in annotations}
def _push_call_definition_scope(
    node: ast.AST, chain: list[ast.AST],
    scope_names: dict[ast.AST, set[str]],
    stack: list[tuple[ast.AST, list[ast.AST]]],
    postpone_annotations: bool,
) -> None:
    scope_names[node] = _scope_local_defined_names(node)
    outer_chain = [scope for scope in chain
                   if not isinstance(scope, ast.ClassDef)]
    body_chain = [node, *outer_chain]
    body = [node.body] if isinstance(node, ast.Lambda) else node.body
    stack.extend((stmt, body_chain) for stmt in reversed(body))
    sites = iter_def_site_nodes(node)
    if postpone_annotations:
        deferred = _definition_annotation_ids(node)
        sites = (site for site in sites if id(site) not in deferred)
    stack.extend((site, chain) for site in reversed(list(sites)))
def _push_call_comprehension_scope(
    node: ast.AST, chain: list[ast.AST],
    scope_names: dict[ast.AST, set[str]],
    stack: list[tuple[ast.AST, list[ast.AST]]],
) -> None:
    inner_chain = [scope for scope in chain
                   if not isinstance(scope, ast.ClassDef)]
    generator_chain = inner_chain
    for index, generator in enumerate(node.generators):
        iter_chain = chain if index == 0 else generator_chain
        stack.append((generator.iter, iter_chain))
        scope_names[generator] = _iteration_target_binding_names(generator)
        generator_chain = [generator, *generator_chain]
        stack.append((generator.target, generator_chain))
        stack.extend((condition, generator_chain) for condition in generator.ifs)
    values = ((node.key, node.value)
              if isinstance(node, ast.DictComp) else (node.elt,))
    stack.extend((value, generator_chain) for value in values)
def _call_scope_universes(
    tree: ast.AST, scope_names: dict[ast.AST, set[str]],
) -> dict[int, set[str]]:
    universes: dict[int, set[str]] = {}
    postpone_annotations = module_postpones_annotations(tree)
    stack = [(stmt, [tree]) for stmt in reversed(getattr(tree, "body", ()))]
    while stack:
        node, chain = stack.pop()
        if isinstance(node, ast.Call):
            universes[id(node)] = _visible_scope_names(chain, scope_names)
        if isinstance(node, _CALL_SCOPE_DEFINITION_NODES):
            _push_call_definition_scope(
                node, chain, scope_names, stack, postpone_annotations)
            continue
        if isinstance(node, COMP_SCOPE_NODES):
            _push_call_comprehension_scope(node, chain, scope_names, stack)
            continue
        children = list(_runtime_child_nodes(node))
        if isinstance(node, ast.AnnAssign) and (
                postpone_annotations
                or isinstance(chain[0], (ast.FunctionDef,
                                         ast.AsyncFunctionDef, ast.Lambda))):
            children = [child for child in children
                        if child is not node.annotation]
        stack.extend((child, chain) for child in reversed(children))
    return universes
def detect_cross_module_refs(tree: ast.AST | None=None,
                             source_lines: list | None=None,
                             filepath: str='',
                             base_path: str | None=None,
                             **kwargs) -> list[dict[str, Any]]:
    if tree is None:
        return []
    if base_path is None and filepath:
        base_path = _infer_base_path(filepath)
    checked_modules: _ModuleExportCache = {}
    static_cache: dict[tuple[str, bool], set[str] | None] = {}
    type_checking_ids = type_checking_body_node_ids(tree)
    scope_names = {tree: _scope_local_defined_names(tree)}
    star_import_unknown = _star_universe_merge(
        tree, filepath, base_path, checked_modules, scope_names[tree])
    call_universes = _call_scope_universes(tree, scope_names)
    findings = []
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call) and id(node) not in call_universes:
            continue
        defined_names = call_universes.get(id(node), scope_names[tree])
        findings.extend(_node_findings(
            node, filepath, base_path, checked_modules,
            defined_names, star_import_unknown,
            type_checking_only=id(node) in type_checking_ids,
            static_cache=static_cache))
    return findings
@dataclass
class TransitiveMissing:
    file: str = ""
    line: int = 0
    missing_symbol: str = ""
    caller_context: str = ""
    def to_dict(self) -> dict:
        return dict(self.__dict__)
def detect_transitive_missing(py_files: list[str], root: str) -> list[TransitiveMissing]:
    results = []
    for fp in py_files:
        _src, tree = parse_py_file(fp)
        if tree is None:
            continue
        results.extend(_check_file_calls(fp, tree, root))
    return results
def _check_file_calls(fp: str, tree: ast.AST, root: str) -> list[TransitiveMissing]:
    results: list[TransitiveMissing] = []
    if any(is_star_import(node) for node in _iter_runtime_nodes(tree)):
        _log.debug("[gf19] 文件含 star import，跳过传递缺失检查: %s", fp)
        return results
    scope_names = {tree: _scope_local_defined_names(tree)}
    call_universes = _call_scope_universes(tree, scope_names)
    for node in _iter_runtime_nodes(tree):
        if isinstance(node, ast.Call) and id(node) not in call_universes:
            continue
        name = _bare_call_name(node)
        defined = call_universes.get(id(node), scope_names[tree])
        if name is None or name in _BUILTIN_NAMES or name in defined:
            continue
        line = getattr(node, 'lineno', 0)
        results.append(TransitiveMissing(
            file=os.path.relpath(fp, root),
            line=line,
            missing_symbol=name,
            caller_context=f"call to '{name}' at line {line}",
        ))
    return results
def _bare_call_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        return node.func.id
    return None
_LAZY_REGISTRY_HINTS = (
    "lazy", "table", "registry", "export", "surface", "anchor")
def _lazy_registry_files(module_dir: str) -> tuple[str, ...]:
    try:
        entries = sorted(os.listdir(module_dir))
    except OSError as e:
        _log.warning("listdir 失败 %s: %s", module_dir, e)
        return ()
    names = []
    for name in entries:
        if not is_scan_py_name(name):
            continue
        stem = name[:-3].lower()
        if stem == "__init__" or any(
                hint in stem for hint in _LAZY_REGISTRY_HINTS):
            names.append(name)
    return tuple(names)
def _sl06_finding(init_file: Any, description: str,
                  suggestion: str, title: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="SL-06", severity="P1", dimension=SPLIT_SAFETY_DIMENSION,
        file=init_file, line=1, title=title,
        description=description, suggestion=suggestion)
def _scan_lazy_registry_modules(
    module_dir: str, init_tree: ast.Module | None = None,
) -> set:
    lazy_source_modules = set()
    for lazy_name in _lazy_registry_files(module_dir):
        lazy_path = os.path.join(module_dir, lazy_name)
        if lazy_name == '__init__.py' and init_tree is not None:
            lazy_source_modules |= _extract_lazy_import_modules_from_tree(
                init_tree, module_dir)
            continue
        try:
            stat = os.stat(lazy_path)
        except FileNotFoundError:
            _log.debug("SL-06 可选 lazy 登记表不存在: %s", lazy_path)
            continue
        except OSError as e:
            _log.warning("lazy 登记表 stat 失败 %s: %s", lazy_path, e)
            continue
        lazy_source_modules |= set(_sl06_lazy_module_names(
            lazy_path, (lazy_path, stat.st_mtime_ns, stat.st_size)))
    return lazy_source_modules
def _sl06_public_submodules(module_dir: str) -> list | None:
    try:
        dir_entries = sorted(os.listdir(module_dir))
    except OSError as e:
        _log.warning("listdir 失败 %s: %s", module_dir, e)
        return None
    sub_modules = []
    for f in dir_entries:
        if f == "__init__.py" or ".tmp_" in f or f.startswith("."):
            continue
        if is_scan_py_name(f):
            sub_modules.append(f[:-3])
        elif os.path.isdir(os.path.join(module_dir, f)):
            sub_modules.append(f)
    return sub_modules
class _RuntimeModuleSurfaceTransformer(ast.NodeTransformer):
    def _visit_block(self, statements: list[ast.stmt]) -> list[ast.stmt]:
        visited: list[ast.stmt] = []
        for statement in statements:
            result = self.visit(statement)
            if isinstance(result, list):
                visited.extend(result)
            elif result is not None:
                visited.append(result)
        return visited
    def visit_If(self, node: ast.If):
        branch = _runtime_if_branch(node)
        if branch is not None:
            return self._visit_block(branch)
        node.body = self._visit_block(node.body)
        node.orelse = self._visit_block(node.orelse)
        return node
    def visit_FunctionDef(self, node: ast.FunctionDef):
        return node
    visit_AsyncFunctionDef = visit_FunctionDef
    visit_ClassDef = visit_FunctionDef
    visit_Lambda = visit_FunctionDef
def _has_foldable_if(tree: ast.AST) -> bool:
    """树中是否存在会被 ``_runtime_if_branch`` 折叠的 ``If`` 节点。

    典型形态：``if TYPE_CHECKING:``、``if True:``、``if not __debug__:`` 等
    条件恒定的守卫——它们的某个分支需要被提升到模块层面。
    """
    stack = [tree]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.If) and _runtime_if_branch(node) is not None:
            return True
        stack.extend(ast.iter_child_nodes(node))
    return False


def _runtime_module_surface_tree(tree: ast.Module) -> ast.Module:
    """把模块树变换成「运行期可见表面」。

    性能约定（实测）：旧实现无条件 ``copy.deepcopy(tree)``，单个 127 KB 模块
    会递归 **905,335 次**，占 XR01 耗时的 **78.6%**。

    当树里**没有可折叠的 ``If``** 时，``_RuntimeModuleSurfaceTransformer``
    只会把每个 ``If`` 的 ``body``/``orelse`` 换成一个内容相同的新 list
    （``_visit_block`` 恒返回新 list），**结构与原树逐层等价**。
    因此此时直接返回原树即可，零拷贝。

    安全性：本函数的全部调用方（``build_module_symbol_table`` /
    ``_scope_namedexpr_binds`` / ``iter_module_level_stmts`` /
    ``_scope_local_defined_names`` / ``collect_module_exports_state`` /
    ``_extract_lazy_import_modules_from_tree``）均**只读**，不做原地修改。
    """
    if not _has_foldable_if(tree):
        return tree
    return _RuntimeModuleSurfaceTransformer().visit(copy.deepcopy(tree))
def _parse_init_surface(init_file: Any,
                        tree: ast.Module | None = None) -> tuple[Any, set]:
    if tree is None:
        init_src, _fingerprint = read_source_with_fingerprint(
            init_file, strict=True)
        if init_src is None:
            _log.warning("__init__ 读取失败 %s", init_file)
            return None, set()
        try:
            init_tree = parse_source_tree(init_src, init_file)
            if init_tree is None:
                raise SyntaxError(f"无法解析 {init_file}")
        except PARSE_DEGRADE_EXC:
            _log.warning(
                "SL-06 __init__ 解析降级(语法错误) %s", init_file)
            return None, set()
    else:
        init_tree = tree
    surface_tree = _runtime_module_surface_tree(init_tree)
    symbol_names, open_surface = _module_export_surface(surface_tree)
    exported = set(symbol_names)
    exported.difference_update({"__all__", "__getattr__"})
    declared_all, declared_all_exact = collect_module_exports_state(
        surface_tree)
    if not declared_all_exact:
        declared_all = set()
    package_name = os.path.basename(os.path.dirname(os.path.abspath(init_file)))
    for node in iter_module_level_stmts(surface_tree):
        if isinstance(node, ast.Import):
            _parse_init_import_names(node, exported, package_name)
        elif isinstance(node, ast.ImportFrom):
            _parse_init_importfrom_names(node, exported, package_name)
    if open_surface:
        exported |= declared_all
    return exported, declared_all
def _parse_init_import_names(node: ast.Import, exported: set,
                             package_name: str) -> None:
    for alias in node.names:
        segments = alias.name.split(".")
        exported.add(alias.asname or segments[0])
        if len(segments) > 1 and segments[0] == package_name:
            exported.add(segments[1])
def _parse_init_importfrom_names(node: ast.ImportFrom, exported: set,
                                 package_name: str) -> None:
    if node.level == 1 and node.module:
        exported.add(node.module.split(".")[0])
    elif node.level == 0 and node.module and package_name:
        _segs = node.module.split(".")
        if len(_segs) > 1 and _segs[0] == package_name:
            exported.add(_segs[1])
    for alias in node.names:
        if alias.name == "*":
            continue
        exported.add(alias.asname or alias.name)
        if node.level == 1 and not node.module and alias.asname:
            exported.add(alias.name)
def _dict_module_keys(value: ast.expr) -> set:
    mods: set = set()
    if isinstance(value, ast.Dict):
        for key in value.keys:
            if isinstance(key, ast.Constant) and isinstance(key.value, str):
                mods.add(key.value)
    return mods
def _is_module_key(key: str) -> bool:
    return bool(key) and all(seg.isidentifier() for seg in key.split("."))
def _is_name_sequence(value: ast.expr | None) -> bool:
    return (isinstance(value, (ast.List, ast.Tuple))
            and all(isinstance(elt, ast.Constant) and isinstance(elt.value, str)
                    for elt in value.elts))
def _is_lazy_registry_name(name: str) -> bool:
    lowered = name.lower()
    return any(hint in lowered for hint in _LAZY_REGISTRY_HINTS)
def _has_lazy_registry_shape(value: ast.expr, keys: set, *,
                             allow_partial_keys: bool = False) -> bool:
    if not isinstance(value, ast.Dict) or not keys:
        return False
    if not allow_partial_keys and len(keys) != len(value.keys):
        return False
    if not all(_is_module_key(key) for key in keys):
        return False
    return all(_is_name_sequence(item) for item in value.values)
def _looks_like_lazy_registry(value: ast.expr, keys: set,
                              module_dir: str) -> bool:
    if not _has_lazy_registry_shape(value, keys):
        return False
    return any(_lazy_source_module_exists(module_dir, key) for key in keys)
def _lazy_target_modules(tgt: ast.expr, value: ast.expr,
                         module_dir: str | None = None) -> set:
    if not isinstance(tgt, ast.Name):
        return set()
    mods = _dict_module_keys(value)
    if not mods:
        return set()
    if (_is_lazy_registry_name(tgt.id)
            and _has_lazy_registry_shape(
                value, mods, allow_partial_keys=True)):
        return mods
    if module_dir and _looks_like_lazy_registry(value, mods, module_dir):
        return mods
    return set()
def _extract_lazy_import_modules_from_tree(
    lazy_tree: ast.Module, module_dir: str | None = None,
) -> set:
    lazy_tree = _runtime_module_surface_tree(lazy_tree)
    modules: set = set()
    for node in iter_module_level_stmts(lazy_tree):
        if isinstance(node, ast.Assign):
            targets = node.targets
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            targets = [node.target]
        else:
            continue
        for tgt in targets:
            modules |= _lazy_target_modules(tgt, node.value, module_dir)
    return modules
def _extract_lazy_import_modules(lazy_src: str,
                                 module_dir: str | None = None) -> set:
    lazy_tree = parse_source_tree(lazy_src, "<lazy_registry>")
    if lazy_tree is None:
        return set()
    return _extract_lazy_import_modules_from_tree(lazy_tree, module_dir)
def _lazy_module_path_exists(module_dir: str, parts: list[str]) -> bool:
    target = os.path.join(module_dir, *parts) if parts else module_dir
    return os.path.isfile(target + ".py") or os.path.isdir(target)
def _lazy_module_path_candidates(
        module_dir: str, module_name: str) -> tuple[list[str], ...]:
    parts = module_name.split(".")
    candidates = [parts]
    directory_parts = os.path.abspath(module_dir).replace("\\", "/").split("/")
    for split in range(1, len(parts) + 1):
        if directory_parts[-split:] == parts[:split]:
            candidates.append(parts[split:])
    return tuple(candidates)
def _lazy_source_module_exists(module_dir: str, module_name: str) -> bool:
    return any(
        _lazy_module_path_exists(module_dir, parts)
        for parts in _lazy_module_path_candidates(module_dir, module_name))
def _sl06_check_missing_exports(
    module_dir: Any, exported: Any, declared_all: Any,
    init_tree: ast.Module | None = None,
) -> Any:
    init_file = os.path.join(module_dir, "__init__.py")
    lazy_source_modules = _scan_lazy_registry_modules(module_dir, init_tree)
    findings = _sl06_missing_lazy_source_findings(
        module_dir, init_file, lazy_source_modules)
    sub_modules = _sl06_public_submodules(module_dir)
    if sub_modules is None:
        return findings
    findings.extend(_sl06_unresolvable_all_findings(
        init_file, declared_all or set(), set(sub_modules), set(exported)))
    return findings
def _sl06_unresolvable_all_findings(init_file: str, declared_all: Any,
                                    sub_modules: set,
                                    exported: Any) -> list:
    missing = sorted(
        name for name in set(declared_all)
        if name not in exported and name not in sub_modules)
    if not missing:
        return []
    return [_sl06_finding(
        init_file,
        (f"__all__ 声明的 {len(missing)} 个名字既未在 __init__.py 绑定，"
         f"也不是现存子模块: {missing}。调用方 from pkg import * 将抛 ImportError。"),
        ("根因: __all__ 白名单与实际导出面不一致。\n"
         "修复策略: 补 from .<模块> import <名字>，或从 __all__ 移除失效项\n"
         "参考标准: PEP 8 / import structure / pylint C0411"),
        "__all__ 声明了不可解析的导出名")]
def _sl06_missing_lazy_source_findings(module_dir: str, init_file: str,
                                       lazy_source_modules: set) -> list:
    expected = sorted(lazy_source_modules)
    missing_files = [
        m
        for m in expected
        if not _lazy_source_module_exists(module_dir, m)
        and _find_spec(m, quiet=True) is None
    ]
    if not missing_files:
        return []
    return [_sl06_finding(
        init_file,
        (f"lazy 导出登记表引用了 {len(missing_files)} 个不存在的源模块: {missing_files}。"
         "调用方通过 __getattr__ 访问时将触发 ImportError。"),
        ("根因: lazy 导出登记表的模块键指向不存在的模块"
         "（键须按本项目的模块路径书写）。\n"
         "修复策略: 修正登记表中不存在的源模块键\n"
         "参考标准: PEP 8 / import structure / pylint C0411"),
        "lazy 导出登记表引用不存在的源模块")]
_SL06_DIR_CACHE: dict = {}
_SL06_DIR_CACHE_MAX = 256
_SL06_LAZY_NAMES_CACHE: dict = {}
def _sl06_lazy_module_names(lazy_path: str, stat_key: tuple) -> tuple:
    hit = _SL06_LAZY_NAMES_CACHE.get(stat_key)
    if hit is not None:
        return hit
    lazy_src, _fingerprint = read_source_with_fingerprint(lazy_path, strict=True)
    if lazy_src is None:
        _log.debug("SL-06 lazy 登记表指纹提取失败（不可解码） %s", lazy_path)
        return ()
    try:
        names = tuple(sorted(_extract_lazy_import_modules(
            lazy_src, os.path.dirname(lazy_path))))
    except (OSError, *PARSE_DEGRADE_EXC) as e:
        _log.debug("SL-06 lazy 登记表指纹提取失败 %s: %s", lazy_path, e)
        return ()
    if len(_SL06_LAZY_NAMES_CACHE) >= _SL06_DIR_CACHE_MAX:
        _SL06_LAZY_NAMES_CACHE.clear()
    _SL06_LAZY_NAMES_CACHE[stat_key] = names
    return names
_SL06_LAZY_DEPS_CACHE: dict = {}
def _sl06_lazy_dep_dirs(module_dir: str, names: tuple) -> tuple:
    dirs = {module_dir}
    for name in names:
        for parts in _lazy_module_path_candidates(module_dir, name):
            cur = module_dir
            for seg in parts[:-1]:
                cur = os.path.join(cur, seg)
                dirs.add(cur)
            target = os.path.join(module_dir, *parts)
            if os.path.isdir(target):
                dirs.add(target)
    return tuple(sorted(dirs))
def _sl06_dir_signature(dirs: tuple) -> tuple:
    sig = []
    for _dir in dirs:
        try:
            _st = os.stat(_dir)
        except OSError as _e:
            if _e.errno != errno.ENOENT:
                log_swallowed(
                    __name__, _e,
                    context=f'_sl06_dir_signature:{type(_e).__name__}')
            sig.append((_dir, None, None))
            continue
        sig.append((_dir, _st.st_mtime_ns, _st.st_size))
    return tuple(sig)
def _sl06_lazy_dep_fingerprint(module_dir: str, lazy_path: str,
                               stat_key: tuple) -> tuple:
    names = _sl06_lazy_module_names(lazy_path, stat_key)
    if not names:
        return ()
    memo_key = (module_dir, names,
                _sl06_dir_signature(_sl06_lazy_dep_dirs(module_dir, names)))
    hit = _SL06_LAZY_DEPS_CACHE.get(memo_key)
    if hit is not None:
        return hit
    deps = tuple(
        (name, _lazy_source_module_exists(module_dir, name))
        for name in names)
    if len(_SL06_LAZY_DEPS_CACHE) >= _SL06_DIR_CACHE_MAX:
        _SL06_LAZY_DEPS_CACHE.clear()
    _SL06_LAZY_DEPS_CACHE[memo_key] = deps
    return deps
def _sl06_dir_cache_key(module_dir: str, init_file: str) -> tuple | None:
    try:
        _ist = os.stat(init_file)
        _dst = os.stat(module_dir)
        _lazy_fps = []
        for _lazy_name in _lazy_registry_files(module_dir):
            _lazy_path = os.path.join(module_dir, _lazy_name)
            try:
                _lst = os.stat(_lazy_path)
                _lazy_fps.append((
                    _lazy_name, _lst.st_mtime_ns, _lst.st_size,
                    _sl06_lazy_dep_fingerprint(
                        module_dir, _lazy_path,
                        (_lazy_path, _lst.st_mtime_ns, _lst.st_size))))
            except FileNotFoundError:
                _log.debug("SL-06 可选 lazy 登记表不存在: %s", _lazy_path)
                continue
            except OSError as _e:
                log_swallowed(
                    __name__, _e,
                    context=f'_sl06_dir_cache_key:{type(_e).__name__}')
                continue
        return (module_dir, _ist.st_mtime_ns, _ist.st_size,
                _dst.st_mtime_ns, _dst.st_size, tuple(_lazy_fps))
    except FileNotFoundError:
        _log.debug("SL-06 记忆化跳过(无 __init__.py): %s", module_dir)
        return None
    except OSError as _e:
        log_swallowed(
            __name__, _e,
            context=f'_sl06_dir_cache_key:{type(_e).__name__}')
        return None
def check_SL06(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    if not filepath:
        return issues
    if os.path.basename(os.path.abspath(filepath)) != "__init__.py":
        return issues
    module_dir = os.path.dirname(os.path.abspath(filepath))
    init_file = os.path.join(module_dir, "__init__.py")
    provided_tree = tree if isinstance(tree, ast.Module) else None
    if provided_tree is not None:
        return _sl06_compute_uncached(
            module_dir, init_file, provided_tree)
    if not os.path.isfile(init_file):
        return issues
    _cache_key = _sl06_dir_cache_key(module_dir, init_file)
    if _cache_key is not None:
        _hit = _SL06_DIR_CACHE.get(_cache_key)
        if _hit is not None:
            return [DiagnoseFinding(**_d) for _d in _hit]
    result = _sl06_compute_uncached(module_dir, init_file)
    if _cache_key is not None:
        _sl06_cache_put(_cache_key, result)
    return result
def _sl06_compute_uncached(module_dir: str, init_file: str,
                           tree: ast.Module | None = None) -> list:
    if tree is None and not os.path.isfile(init_file):
        return []
    exported, declared_all = _parse_init_surface(init_file, tree)
    if exported is None:
        return []
    return _sl06_check_missing_exports(
        module_dir, exported, declared_all, init_tree=tree)
def _sl06_cache_put(cache_key: tuple, findings: list) -> None:
    if len(_SL06_DIR_CACHE) >= _SL06_DIR_CACHE_MAX:
        _SL06_DIR_CACHE.clear()
    _SL06_DIR_CACHE[cache_key] = [_f.to_dict() for _f in findings]
def _project_root_of(filepath: str) -> str:
    if not isinstance(filepath, str) or not filepath.strip():
        return ""
    current = os.path.dirname(os.path.abspath(filepath))
    package_parent = ""
    while True:
        if not _is_temp_root(current) and _is_marked_project_root(current):
            return current
        if _is_package_dir(current):
            package_parent = os.path.dirname(current)
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    if not package_parent or _is_temp_root(package_parent):
        return ""
    return package_parent
def _sibling_project_names(filepath: str,
                           root: str | None = None) -> frozenset[str]:
    root = _project_root_of(filepath) if root is None else root
    if not root:
        return frozenset()
    names: set[str] = set()
    if _is_marked_project_root(root):
        parent = os.path.dirname(root)
        if not parent or parent == root:
            return frozenset()
        try:
            for entry in os.listdir(parent):
                path = os.path.join(parent, entry)
                if not os.path.isdir(path) or entry.startswith("."):
                    continue
                if _is_marked_project_root(path) or _is_package_dir(path):
                    names.add(entry)
        except OSError as exc:
            _log.debug("同级项目发现失败（按无同级处理）: %s: %s", parent, exc)
        return frozenset(names)
    names.update(_package_dirs(root))
    for layout_root in source_import_roots(root):
        names.update(_package_dirs(layout_root))
    return frozenset(names)
def _own_project_names(filepath: str, root: str) -> frozenset[str]:
    names: set[str] = set()
    if root:
        names.add(os.path.basename(os.path.normpath(root)))
    current = os.path.dirname(os.path.abspath(filepath)) if filepath else ""
    while current and _is_package_dir(current):
        names.add(os.path.basename(current))
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    return frozenset(names)
class CrossSkillDependencyDetector:
    DETECTOR_ID = "D37"
    PATTERN_NAME = "跨技能依赖"
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        findings = []
        parsed = load_source_tree(filepath)
        if parsed is None:
            return findings
        _source, tree = parsed
        root = _project_root_of(filepath)
        own_names = _own_project_names(filepath, root)
        if not own_names:
            own_names = frozenset(
                {resolve_module_name(filepath).split('.', 1)[0]})
        sibling_names = _sibling_project_names(filepath, root)
        for node in walk_nodes(tree):
            findings.extend(self._import_findings(
                node, filepath, sibling_names, own_names))
        return findings
    def _import_findings(
            self, node: ast.AST, filepath: str,
            sibling_names: frozenset[str] | None = None,
            own_names: frozenset[str] | None = None,
    ) -> list[PatternFinding]:
        if isinstance(node, ast.Import):
            return [self._finding(
                filepath, node.lineno, f"import {alias.name}",
                f"跨技能依赖: import {alias.name}（技能: {skill}）")
                for alias in node.names
                if (skill := self._extract_skill(
                    alias.name, filepath, sibling_names, own_names))]
        if (isinstance(node, ast.ImportFrom) and node.module
                and not node.level):
            skill = self._extract_skill(
                node.module, filepath, sibling_names, own_names)
            if skill:
                names = ", ".join(a.name for a in node.names[:3])
                return [self._finding(
                    filepath, node.lineno,
                    f"from {node.module} import {names}",
                    f"跨技能依赖: from {node.module}（技能: {skill}）")]
        return []
    def _finding(self, filepath: str, line: int, snippet: str,
                 message: str) -> PatternFinding:
        return PatternFinding(
            detector_id=self.DETECTOR_ID,
            pattern_name=self.PATTERN_NAME,
            severity="WARN",
            filepath=filepath,
            line=line,
            snippet=snippet,
            message=message,
            suggestion="改为通过标准接口调用,或内敛所需功能到本技能",
        )
    def _extract_skill(
            self, module_name: str, filepath: str = "",
            sibling_names: frozenset[str] | None = None,
            own_names: frozenset[str] | None = None,
    ) -> str | None:
        if own_names is None:
            own_root = _project_root_of(filepath) if filepath else ""
            own_names = (_own_project_names(filepath, own_root)
                         if filepath else frozenset())
            if not own_names and filepath:
                own_names = frozenset(
                    {resolve_module_name(filepath).split('.', 1)[0]})
        if sibling_names is None:
            sibling_names = (_sibling_project_names(filepath) if filepath
                             else frozenset())
        own_keys = {import_key(name) for name in own_names}
        for name in sorted(sibling_names, key=len, reverse=True):
            key = import_key(name)
            if not key.isidentifier() or key in own_keys:
                continue
            if module_name == key or module_name.startswith(key + '.'):
                return name
        return None
def wiring_declarations() -> dict:
    return {"catalogs": {
        "rule_bindings": {
            "GF16": check_GF16,
            "GF18": check_GF18,
            "XR01": detect_cross_module_refs,
            "SL06": check_SL06,
        },
        "sl_checks": {"SL06": check_SL06},
        "new_pattern_classes": {"D37": CrossSkillDependencyDetector},
    }}

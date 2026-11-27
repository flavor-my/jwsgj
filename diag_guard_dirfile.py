from __future__ import annotations

import ast as _ast
import logging
import os
import re
from collections import Counter
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field, replace
from enum import Enum
from functools import partial
from typing import Any, ClassVar

from jwsgj.diag_shared_ast_nodes import (
    TRY_STAR,
    collect_import_usage,
    cyclomatic_complexity,
    decorator_name,
    definition_start_line,
    direct_class_methods,
    extract_all_declarations,
    is_abstract_class_def,
    is_main_check,
    is_none_literal,
    is_package_init_path,
    is_static_method,
    is_type_checking_guard,
    iter_module_level_stmts,
    iter_own_scope,
    iter_unpack_target_names,
    main_guard_branch,
    parse_ast_safely,
    typing_guard_aliases,
    typing_type_checking_names,
)
from jwsgj.diag_shared_ast_surface import replay_export_surface
from jwsgj.diag_shared_source_core import (
    count_lines,
    parse_cached,
    parse_guard_cached,
    parse_py_file,
    read_cached,
    read_source,
    read_source_strict,
)
from jwsgj.diag_shared_source_scan import (
    is_suppressed,
    parse_suppressions,
)
from jwsgj.diag_types_defs import (
    DirFileResult,
    DirFileStats,
    Finding,
    MergePlan,
    PreinterventionResult,
    finish_check,
    make_detail,
    prepare_tree,
)
from jwsgj.diag_types_normalize import normalize_input
from jwsgj.diag_types_vocab import (
    ALLOWED_RESOURCES,
    MAX_FUNC_LINES,
    PARSE_DEGRADE_EXC,
    SEVERITY_BLOCKING,
    SEVERITY_WARNING,
    Severity,
    normalize_filepath,
    register_check_provider,
)
from jwsgj.diag_types_vocab import (
    MAX_CLASS_METHODS as PRE_MAX_CLASS_METHODS,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    CACHE_TEMP_DIR_NAMES,
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    detect_cycles,
    is_pruned_scan_dir,
    is_py_source_file,
    is_test_file_path,
)

logger = logging.getLogger(__name__)
__all__ = [
    'ARCH_DIR_MAX_FILES_DEFAULT',
    'ARCH_FACADE_MAX_SYMBOLS',
    'ARCH_FILE_MAX_LINES',
    'ARCH_FUNC_MAX_COMPLEXITY',
    'ARCH_FUNC_MAX_LINES',
    'ARCH_SRP_MAX_CLASSES',
    'ARCH_SRP_MAX_FUNCS',
    'BUILTIN_ARCHITECTURE_RULES',
    'LAYER_KEYWORDS',
    'UTIL_TOKENS',
    'ArchRuleChecker',
    'ArchitecturePrinciple',
    'ArchitectureRule',
    'DirFileGuard',
    'check_all_declaration',
    'check_architecture',
    'check_dependency_management',
    'check_import_structure',
    'collect_module_all_declaration',
    'detect_layer',
    'dirfile_warning_lines',
    'get_architecture_rules',
    'path_tokens',
    'review_architecture',
]
ARCH_SRP_MAX_FUNCS = 30
ARCH_SRP_MAX_CLASSES = 10
ARCH_FACADE_MAX_SYMBOLS = 9
ARCH_FUNC_MAX_LINES = MAX_FUNC_LINES
ARCH_FUNC_MAX_COMPLEXITY = 15
ARCH_FILE_MAX_LINES = 3000
ARCH_DIR_MAX_FILES_DEFAULT = 50
_ARCH_ALLOW_LOCAL_IMPORTS_DEFAULT = False
_MERGE_EXEMPT_FILENAMES = frozenset({
    '__init__.py', '_version.py', '_version_meta.py',
    'version.py', 'facade.py', '__main__.py', 'setup.py',
})
_IN_PLACE_GOVERNANCE_PHASES = (
    ("SIMPLIFY", "简化逻辑并消除重复"),
    ("CONVERGE", "收敛依赖，必要时迁移到既有职责模块"),
    ("EXTRACT_PRIVATE", "提取同模块私有实现"),
    ("VERIFY", "执行定向回归与六项治理验收"),
)
def _require_non_negative_int(owner: str, name: str, value: Any) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ValueError(f"{owner} 阈值参数 {name} 须为非负整数,实际: {value!r}")
    return value
def _require_bool(owner: str, name: str, value: Any) -> bool:
    if not isinstance(value, bool):
        raise ValueError(  # noqa: TRY004
            f"{owner} 阈值参数 {name} 须为 bool,实际: {value!r}")
    return value
def _existing_target_lines(file_sizes: dict[str, int], target: str) -> int:
    norm_target = os.path.normcase(target)
    return next((size for path, size in file_sizes.items()
                 if os.path.normcase(path) == norm_target), 0)
def _iter_file_trees(py_files: list[str]):
    for fpath in py_files:
        tree = parse_guard_cached(fpath)
        if tree is not None:
            yield fpath, tree
def _rule_scope_files(py_files: list[str]) -> list[str]:
    return [fpath for fpath in py_files if not is_test_file_path(fpath)]
def _entry_message(entry: Any) -> Any:
    return entry.get("message", entry) if isinstance(entry, dict) else entry
def _entry_rule(entry: Any) -> str:
    return entry.get("rule_id", "") if isinstance(entry, dict) else ""
_SIZE_ISSUE_CODES: dict[str, str] = {
    "ARCH-FILE-001": "FILE_TOO_LONG",
    "ARCH-DIR-001": "DIR_TOO_MANY_FILES",
}
def _size_issue_view(arch_violations: list[dict]) -> list[dict]:
    issues: list[dict] = []
    for violation in arch_violations:
        if not isinstance(violation, dict):
            continue
        code = _SIZE_ISSUE_CODES.get(str(violation.get("rule_id", "")))
        if code is None:
            continue
        issues.append({
            "code": code,
            "file": violation.get("file", ""),
            "message": violation.get("message", ""),
            "severity": violation.get("severity", ""),
            "suggestion": violation.get("suggestion", ""),
        })
    return issues
def _dir_file_counts(py_files: list[str]) -> dict[str, int]:
    return dict(Counter(os.path.dirname(fpath) for fpath in py_files))
def dirfile_warning_lines(result: Any) -> list[str]:
    lines = [f"目录检查: {_entry_message(issue)}" for issue in result.issues]
    lines.extend(
        f"目录 .py 文件数超限，建议整合: {plan.target_module} "
        f"(待合并 {len(plan.source_files or [])} 个文件)"
        for plan in result.merge_plans)
    lines.extend(
        f"架构违规: {_entry_rule(violation)} {_entry_message(violation)}"
        for violation in result.arch_violations
        if _entry_rule(violation) not in _SIZE_ISSUE_CODES)
    return lines
_COUNTED_SKIP_DIRS_LOWER = GENERIC_SCAN_IGNORE_DIRS_LOWER | CACHE_TEMP_DIR_NAMES
class DirFileGuard:
    def __init__(self, max_dir_files: int = ARCH_DIR_MAX_FILES_DEFAULT,
                 max_file_lines: int = ARCH_FILE_MAX_LINES,
                 massive_threshold: int = 8000,
                 small_file_threshold: int = 80,
                 allow_local_imports: bool = _ARCH_ALLOW_LOCAL_IMPORTS_DEFAULT):
        _owner = "DirFileGuard"
        self.max_dir_files = _require_non_negative_int(
            _owner, "max_dir_files", max_dir_files)
        self.max_file_lines = _require_non_negative_int(
            _owner, "max_file_lines", max_file_lines)
        self.massive_threshold = _require_non_negative_int(
            _owner, "massive_threshold", massive_threshold)
        self.small_file_threshold = _require_non_negative_int(
            _owner, "small_file_threshold", small_file_threshold)
        self.allow_local_imports = _require_bool(
            _owner, "allow_local_imports", allow_local_imports)
    def check_directory(self, dir_path: str) -> DirFileResult:
        if not os.path.isdir(dir_path):
            return DirFileResult(
                ok=False,
                dir_path=dir_path,
                stats=DirFileStats(
                    dir_path=dir_path,
                    total_py_files=0,
                    total_lines=0,
                ),
                message="目录不存在",
            )
        py_files, stats = self._collect_file_stats(dir_path)
        rule_files = _rule_scope_files(py_files)
        arch_violations = ArchRuleChecker(
            max_dir_files=self.max_dir_files,
            allow_local_imports=self.allow_local_imports,
            max_file_lines=self.max_file_lines,
        ).check_architecture_rules(dir_path, rule_files, stats.file_sizes)
        issues = _size_issue_view(arch_violations)
        merge_plans, strangler_plans = self._collect_governance_plans(
            rule_files, stats)
        block_n = sum(
            1 for item in arch_violations
            if isinstance(item, dict) and item.get("severity") == "BLOCK")
        if issues or arch_violations:
            logger.warning(
                "[DirFileGuard] check_directory 检出 issues=%d arch=%d block=%d: %s",
                len(issues), len(arch_violations), block_n, dir_path,
            )
        return DirFileResult(
            ok=block_n == 0,
            dir_path=dir_path,
            stats=stats,
            merge_plans=merge_plans,
            strangler_plans=strangler_plans,
            arch_violations=arch_violations,
            issues=issues,
        )
    @staticmethod
    def _is_counted_dir(name: str) -> bool:
        return not is_pruned_scan_dir(name, _COUNTED_SKIP_DIRS_LOWER)
    @staticmethod
    def _iter_source_files(dir_path: str):
        for root, dirs, files in os.walk(
                dir_path,
                onerror=lambda err: logger.warning(
                    "[Guard] 目录不可读，跳过并继续: %s", err)):
            dirs[:] = sorted(d for d in dirs if DirFileGuard._is_counted_dir(d))
            for fname in sorted(files):
                if not is_py_source_file(fname):
                    continue
                fpath = os.path.join(root, fname)
                content = read_cached(fpath)
                if content is None:
                    logger.warning("[Guard] 读取文件失败,跳过: %s", fpath)
                    continue
                yield fpath, content
    def _size_bucket(self, n_lines: int) -> str:
        if n_lines >= self.massive_threshold:
            return "massive"
        if n_lines > self.max_file_lines:
            return "large"
        if n_lines <= self.small_file_threshold:
            return "small"
        return "normal"
    def _collect_file_stats(self, dir_path: str) -> tuple[list[str], DirFileStats]:
        py_files: list[str] = []
        total_lines = 0
        file_sizes: dict[str, int] = {}
        buckets: dict[str, list[str]] = {"small": [], "large": [], "massive": []}
        for fpath, content in self._iter_source_files(dir_path):
            n_lines = count_lines(content)
            py_files.append(fpath)
            total_lines += n_lines
            file_sizes[fpath] = n_lines
            bucket = buckets.get(self._size_bucket(n_lines))
            if bucket is not None:
                bucket.append(fpath)
        stats = DirFileStats(
            dir_path=dir_path,
            total_py_files=len(py_files),
            total_lines=total_lines,
            small_files=buckets["small"],
            large_files=buckets["large"],
            massive_files=buckets["massive"],
            file_sizes=file_sizes,
        )
        return py_files, stats
    def _collect_governance_plans(
            self, py_files: list[str],
            stats: DirFileStats
    ) -> tuple[list[MergePlan], list[dict]]:
        dir_counts = _dir_file_counts(py_files)
        over_limit = {directory for directory, count in dir_counts.items()
                      if count > self.max_dir_files}
        merge_plans: list[MergePlan] = []
        if over_limit:
            merge_plans = self._generate_merge_plans(
                [fpath for fpath in py_files
                 if os.path.dirname(fpath) in over_limit],
                stats.file_sizes)
        return merge_plans, self._massive_file_plans(stats, py_files)
    def _massive_file_plans(self, stats: DirFileStats,
                            py_files: list[str]) -> list[dict]:
        governed_files = set(py_files)
        return [
            {
                "file": mf,
                "lines": stats.file_sizes[mf],
                "strategy": "IN_PLACE_GOVERNANCE",
                "phases": self._generate_governance_phases(
                    mf, stats.file_sizes[mf]),
            }
            for mf in stats.massive_files
            if mf in governed_files
        ]
    def _generate_merge_plans(self, py_files: list[str],
                               file_sizes: dict[str, int]) -> list[MergePlan]:
        plans = []
        small_files = [
            f for f in py_files
            if file_sizes.get(f, 0) <= self.small_file_threshold
            and os.path.basename(f).lower() not in _MERGE_EXEMPT_FILENAMES
        ]
        if len(small_files) < 2:
            return plans
        dir_groups: dict[str, list[str]] = {}
        for f in small_files:
            d = os.path.dirname(f)
            dir_groups.setdefault(d, []).append(f)
        for directory in sorted(dir_groups):
            plans.extend(self._merge_plans_for_dir(
                directory, dir_groups[directory], file_sizes))
        return plans
    def _merge_plans_for_dir(self, directory: str, files: list[str],
                            file_sizes: dict[str, int]) -> list[MergePlan]:
        if len(files) < 2:
            return []
        plans: list[MergePlan] = []
        groups = self._group_by_semantic_prefix(files)
        for prefix in sorted(groups):
            plan = self._build_merge_plan(
                directory, prefix, groups[prefix], file_sizes)
            if plan is not None:
                plans.append(plan)
        return plans
    def _build_merge_plan(self, directory: str, prefix: str, group: list[str],
                          file_sizes: dict[str, int]) -> MergePlan | None:
        target = os.path.join(directory, f"{prefix}_merged.py")
        target_name = os.path.normcase(os.path.basename(target))
        sources = [
            f for f in group
            if os.path.normcase(os.path.basename(f)) != target_name
        ]
        if len(sources) < 2:
            return None
        total = sum(file_sizes.get(f, 0) for f in sources)
        total += _existing_target_lines(file_sizes, target)
        if total > self.max_file_lines:
            return None
        return MergePlan(
            target_module=target,
            source_files=sources,
            rationale=(f"前缀 '{prefix}' 的 {len(sources)} 个文件为内聚候选，"
                       f"合并后估算 {total} 行；执行前必须补 pros/cons/"
                       "net_benefit=positive 论证并写入治理决策"),
            total_lines=total,
            strategy="semantic_group",
        )
    def _group_by_semantic_prefix(self, files: list[str]) -> dict[str, list[str]]:
        groups: dict[str, list[str]] = {}
        for f in files:
            basename = os.path.splitext(os.path.basename(f))[0]
            prefix = re.split(r"[_-]", basename, maxsplit=1)[0]
            groups.setdefault(prefix, []).append(f)
        return groups
    @staticmethod
    def _generate_governance_phases(filepath: str,
                                    total_lines: int) -> list[dict]:
        phase_count = len(_IN_PLACE_GOVERNANCE_PHASES)
        return [
            {
                "phase": index,
                "action": action,
                "target": filepath,
                "estimated_lines": total_lines,
                "description": f"阶段 {index}/{phase_count}: {description}",
            }
            for index, (action, description) in enumerate(
                _IN_PLACE_GOVERNANCE_PHASES, 1)
        ]
def _generic_py_files(dir_path: str) -> list[str]:
    return [fpath for fpath, _content in DirFileGuard._iter_source_files(
        os.fspath(dir_path))]
_IMPORT_ERROR_NAMES = frozenset({"ImportError", "ModuleNotFoundError"})
def _none_bound_names(stmt: _ast.AST) -> list[str]:
    if not (isinstance(stmt, (_ast.Assign, _ast.AnnAssign))
            and is_none_literal(stmt.value)):
        return []
    targets = (stmt.targets
               if isinstance(stmt, _ast.Assign)
               else (stmt.target,))
    return [t.id for t in targets if isinstance(t, _ast.Name)]
def _iter_handler_none_bindings(
        handler: _ast.ExceptHandler) -> Iterator[tuple[str, int]]:
    stack: list[_ast.AST] = list(reversed(handler.body))
    while stack:
        node = stack.pop()
        if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef,
                             _ast.ClassDef)):
            continue
        if isinstance(node, (_ast.Try, TRY_STAR)):
            stack.extend(reversed([
                *node.body, *node.orelse, *node.finalbody,
                *(nested for nested in node.handlers
                  if _matched_import_error_name(nested.type) is None),
            ]))
            continue
        for name in _none_bound_names(node):
            yield name, node.lineno
        stack.extend(reversed(list(_ast.iter_child_nodes(node))))
def _matched_import_error_name(htype) -> str | None:
    if isinstance(htype, _ast.Name):
        return htype.id if htype.id in _IMPORT_ERROR_NAMES else None
    if isinstance(htype, _ast.Tuple):
        for elt in htype.elts:
            if isinstance(elt, _ast.Name) and elt.id in _IMPORT_ERROR_NAMES:
                return elt.id
    return None
_LAYER_EXEMPT_DIRS = frozenset(
    {''} | CACHE_TEMP_DIR_NAMES | {'tests', 'test'}
    | {d.lower() for d in ALLOWED_RESOURCES})
_VALID_ARCH_LAYERS = frozenset({
    'core', 'domain', 'application', 'infrastructure',
    'presentation', 'shared', 'utils', 'tools', 'adapters',
})
_NEUTRAL_PROJECT_DIRS = frozenset({
    'src', 'lib', 'source', 'sources', 'python', 'pkg', 'packages',
})
def _count_module_symbols(tree: _ast.AST) -> tuple[int, int]:
    func_count = 0
    class_count = 0
    for node in _ast.iter_child_nodes(tree):
        if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            func_count += 1
        elif isinstance(node, _ast.ClassDef):
            class_count += 1
            func_count += sum(
                1 for child in iter_own_scope(
                    node, skip_lambda=True, include_self=True)
                if isinstance(child, (_ast.FunctionDef, _ast.AsyncFunctionDef))
            )
    return func_count, class_count
def _split_leading_docstring(body: list) -> tuple[str | None, list]:
    if (body and isinstance(body[0], _ast.Expr)
            and isinstance(body[0].value, _ast.Constant)
            and isinstance(body[0].value.value, str)):
        return body[0].value.value, body[1:]
    return None, body
def _is_stub_body(body: list) -> bool:
    docstring, stmts = _split_leading_docstring(body)
    if not stmts:
        return docstring is not None
    if len(stmts) != 1:
        return False
    stmt = stmts[0]
    if isinstance(stmt, _ast.Pass):
        return True
    if not (isinstance(stmt, _ast.Expr)
            and isinstance(stmt.value, _ast.Constant)):
        return False
    value = stmt.value.value
    return value is Ellipsis or (isinstance(value, str) and not value.strip())
def _cycle_finding(dir_path: str, cycle: list) -> dict:
    closed = [*cycle, cycle[0]]
    return {
        "rule_id": "ARCH-CIRC-001",
        "file": dir_path,
        "message": f"检测到模块级循环依赖: {' -> '.join(closed)}",
        "severity": "BLOCK",
        "suggestion": ("收敛依赖：环内共享部分下沉到既有下层模块，或经包入口"
                       "注入（GOV-01 禁止新建模块消环）"),
    }
def _build_import_graph(dir_path: str,
                        py_files: list[str]) -> dict[str, set[str]]:
    modules, packages = _index_module_layout(dir_path, py_files)
    root_parts = _scan_root_package_parts(dir_path)
    graph: dict[str, set[str]] = {}
    for fpath in py_files:
        identity = _module_identity(fpath, dir_path)
        if identity is None:
            continue
        key, pkg_parts, _is_init = identity
        graph.setdefault(key, set())
        owned_initializers = _owned_package_initializers(
            pkg_parts, root_parts, modules)
        tree = parse_guard_cached(fpath)
        if tree is None:
            continue
        inactive_imports = _inactive_branch_import_ids(tree)
        for node in iter_module_level_stmts(tree):
            if id(node) in inactive_imports:
                continue
            if isinstance(node, _ast.Import):
                targets = _resolve_import(
                    node, root_parts, modules, packages, owned_initializers)
            elif isinstance(node, _ast.ImportFrom):
                targets = _resolve_importfrom(
                    node, pkg_parts, root_parts, modules, packages,
                    owned_initializers)
            else:
                continue
            graph[key].update(t for t in targets if t != key)
    return graph
def _module_identity(fpath: str, dir_path: str
                     ) -> tuple[str, list[str], bool] | None:
    try:
        rel = os.path.relpath(fpath, dir_path)
    except ValueError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_module_identity:ValueError')
        return None
    parts = rel.replace(os.sep, '/').split('/')
    if not parts or parts[0] == '..':
        return None
    if (len(parts) > 1 and parts[0] == 'src'
            and not _has_package_init(os.path.join(dir_path, 'src'))):
        parts = parts[1:]
    pkg_parts = parts[:-1]
    stem = os.path.splitext(parts[-1])[0]
    if stem.lower() == '__init__':
        return '.'.join([*pkg_parts, '__init__']), pkg_parts, True
    return '.'.join([*pkg_parts, stem]), pkg_parts, False
def _index_module_layout(
        dir_path: str, py_files: list[str]
) -> tuple[dict[str, str], set[str]]:
    modules: dict[str, str] = {}
    packages = {''}
    for fpath in py_files:
        identity = _module_identity(fpath, dir_path)
        if identity is None:
            continue
        key, pkg_parts, _is_init = identity
        modules[key] = fpath
        for depth in range(1, len(pkg_parts) + 1):
            packages.add('.'.join(pkg_parts[:depth]))
    return modules, packages
def _scan_root_package_parts(dir_path: str) -> list[str]:
    cur = os.path.abspath(dir_path)
    names: list[str] = []
    while _has_package_init(cur):
        names.append(os.path.basename(cur))
        parent = os.path.dirname(cur)
        if parent == cur:
            break
        cur = parent
    return names[::-1]
def _has_package_init(directory: str) -> bool:
    return any(
        os.path.isfile(os.path.join(directory, name))
        for name in ('__init__.py', '__INIT__.PY'))
def _resolved_module_kind(key: str, modules: dict[str, str],
                          packages: set[str]) -> str | None:
    if _package_init_key(key) in modules:
        return 'package'
    if key in modules:
        return 'module'
    if key in packages:
        return 'package'
    return None
def _resolve_absolute_module(parts: list[str], root_parts: list[str],
                             modules: dict[str, str],
                             packages: set[str]) -> tuple[str, str] | None:
    if root_parts:
        if parts[:len(root_parts)] != root_parts:
            return None
        parts = parts[len(root_parts):]
        if not parts:
            return 'package', ''
    key = '.'.join(parts)
    kind = _resolved_module_kind(key, modules, packages)
    return (kind, key) if kind is not None else None
def _resolve_relative_module(
        node: _ast.ImportFrom, pkg_parts: list[str],
        root_parts: list[str], modules: dict[str, str],
        packages: set[str]) -> tuple[str, str] | None:
    up = node.level - 1
    if up < 0 or up > len(pkg_parts):
        return None
    if up > 0 and up == len(pkg_parts) and not root_parts:
        return None
    base = pkg_parts[:len(pkg_parts) - up]
    if node.module:
        base = [*base, *node.module.split('.')]
    key = '.'.join(base)
    kind = _resolved_module_kind(key, modules, packages)
    return (kind, key) if kind is not None else None
def _package_init_key(package_key: str) -> str:
    return f"{package_key}.__init__" if package_key else "__init__"
def _package_key_chain(package_key: str) -> list[str]:
    if not package_key:
        return [""]
    parts = package_key.split(".")
    return [".".join(parts[:depth]) for depth in range(1, len(parts) + 1)]
def _owned_package_initializers(
        pkg_parts: list[str], root_parts: list[str],
        modules: dict[str, str]) -> set[str]:
    package_keys = [""] if root_parts else []
    package_keys.extend(
        ".".join(pkg_parts[:depth]) for depth in range(1, len(pkg_parts) + 1))
    return {
        init_key
        for package_key in package_keys
        if (init_key := _package_init_key(package_key)) in modules
    }
def _import_runtime_targets(
        kind: str, key: str, modules: dict[str, str],
        owned_initializers: set[str] | None = None) -> list[str]:
    owned = owned_initializers or set()
    package_key = key if kind == 'package' else key.rpartition('.')[0]
    package_keys = _package_key_chain(package_key) if package_key or kind == 'package' else []
    targets = [
        init_key
        for package_key in package_keys
        if (init_key := _package_init_key(package_key)) in modules
        and init_key not in owned
    ]
    if kind == 'module':
        targets.append(key)
    return list(dict.fromkeys(targets))
def _resolve_import(node: _ast.Import, root_parts: list[str],
                    modules: dict[str, str], packages: set[str],
                    owned_initializers: set[str] | None = None) -> list[str]:
    targets = []
    for alias in node.names:
        resolved = _resolve_absolute_module(
            alias.name.split('.'), root_parts, modules, packages)
        if resolved is None:
            continue
        kind, key = resolved
        targets.extend(_import_runtime_targets(
            kind, key, modules, owned_initializers))
    return targets
def _resolve_importfrom(
        node: _ast.ImportFrom, pkg_parts: list[str], root_parts: list[str],
        modules: dict[str, str], packages: set[str],
        owned_initializers: set[str] | None = None) -> list[str]:
    if node.level:
        resolved = _resolve_relative_module(
            node, pkg_parts, root_parts, modules, packages)
    else:
        resolved = _resolve_absolute_module(
            (node.module or '').split('.'), root_parts, modules, packages)
    if resolved is None:
        return []
    kind, base_key = resolved
    targets = _import_runtime_targets(
        kind, base_key, modules, owned_initializers)
    if kind == 'module':
        return targets
    for alias in node.names:
        if alias.name == '*':
            continue
        candidate = f"{base_key}.{alias.name}" if base_key else alias.name
        candidate_kind = _resolved_module_kind(candidate, modules, packages)
        if candidate_kind is not None:
            targets.extend(_import_runtime_targets(
                candidate_kind, candidate, modules, owned_initializers))
    return list(dict.fromkeys(targets))
_DECLARATION_ONLY_DECORATORS = frozenset({
    "abstractmethod", "abstractclassmethod", "abstractstaticmethod",
    "abstractproperty", "overload",
})
_PROTOCOL_BASE_NAMES = frozenset({"Protocol"})
def _has_declaration_decorator(node: _ast.AST) -> bool:
    return any(
        decorator_name(dec) in _DECLARATION_ONLY_DECORATORS
        for dec in getattr(node, "decorator_list", ())
    )
def _protocol_base_name(base: _ast.AST) -> str:
    while isinstance(base, _ast.Subscript):
        base = base.value
    if isinstance(base, _ast.Name):
        return base.id
    if isinstance(base, _ast.Attribute):
        return base.attr
    return ""
def _is_protocol_class(node: _ast.ClassDef) -> bool:
    return any(_protocol_base_name(base) in _PROTOCOL_BASE_NAMES
               for base in node.bases)
def _declaration_only_method_ids(tree: _ast.AST) -> set[int]:
    declared: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, _ast.ClassDef):
            continue
        if not (is_abstract_class_def(node) or _is_protocol_class(node)):
            continue
        declared.update(
            id(child)
            for child in _ast.iter_child_nodes(node)
            if isinstance(child, (_ast.FunctionDef, _ast.AsyncFunctionDef))
        )
    return declared
_DEAD_CODE_SUPPRESS_CATEGORIES = (
    "ARCH-DEAD-001", "empty_function", "stub_function", "dead_stub")
def _suppressed_dead_code(suppressions: dict, *linenos: int) -> bool:
    return any(
        is_suppressed(suppressions, lineno, category)
        for lineno in linenos
        for category in _DEAD_CODE_SUPPRESS_CATEGORIES
    )
def _dead_code_node_linenos(node: _ast.AST) -> tuple[int, ...]:
    linenos = [getattr(node, "lineno", None)]
    body = getattr(node, "body", ())
    if isinstance(body, (list, tuple)):
        linenos.extend(getattr(stmt, "lineno", None) for stmt in body)
    return tuple(lineno for lineno in linenos if isinstance(lineno, int))
def _dead_code_suppressed(suppressions: dict | None, node: _ast.AST) -> bool:
    if suppressions is None:
        return False
    return _suppressed_dead_code(suppressions, *_dead_code_node_linenos(node))
def _dead_code_findings(py_files: list[str]) -> list[dict]:
    violations = []
    for fpath in py_files:
        tree = parse_guard_cached(fpath)
        if tree is None:
            continue
        declared = _declaration_only_method_ids(tree)
        suppressions = parse_suppressions(read_cached(fpath) or "")
        for node in walk_nodes(tree):
            finding = _detect_dead_code_node(
                fpath, node, declared, suppressions)
            if finding is not None:
                violations.append(finding)
    return violations
def _detect_dead_code_node(fpath: str, node: _ast.AST,
                           declared_methods: set[int] | frozenset[int],
                           suppressions: dict | None = None
                           ) -> dict | None:
    if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
        if id(node) in declared_methods or _has_declaration_decorator(node):
            return None
        if _dead_code_suppressed(suppressions, node):
            return None
        return (_stub_function_finding(fpath, node)
                or _unreachable_tail_finding(fpath, node))
    if isinstance(node, (_ast.If, _ast.While)):
        if _dead_code_suppressed(suppressions, node):
            return None
        return _unreachable_block_finding(fpath, node)
    return None
_UNCONDITIONAL_FLOW_END = (_ast.Return, _ast.Raise)
def _unreachable_tail_finding(fpath: str, node: _ast.AST) -> dict | None:
    for index, stmt in enumerate(node.body[:-1]):
        if not isinstance(stmt, _UNCONDITIONAL_FLOW_END):
            continue
        kind = "return" if isinstance(stmt, _ast.Return) else "raise"
        dead = node.body[index + 1]
        return {
            "rule_id": "ARCH-DEAD-001",
            "file": fpath,
            "message": (
                f"函数 '{node.name}' 在 {kind} 后有不可达代码 "
                f"(行 {dead.lineno})"
            ),
            "severity": "WARN",
            "suggestion": "移除死代码",
        }
    return None
def _stub_function_finding(fpath: str, node: _ast.AST) -> dict | None:
    if not _is_stub_body(node.body):
        return None
    return {
        "rule_id": "ARCH-DEAD-001",
        "file": fpath,
        "message": (
            f"函数 '{node.name}' 仅含 pass/.../docstring,"
            f"疑似桩函数"
        ),
        "severity": "WARN",
        "suggestion": "移除死代码或实现函数体",
    }
def _unreachable_block_finding(fpath: str, node: _ast.AST) -> dict | None:
    if not (isinstance(node.test, _ast.Constant) and not node.test.value):
        return None
    kw = "if" if isinstance(node, _ast.If) else "while"
    return {
        "rule_id": "ARCH-DEAD-001",
        "file": fpath,
        "message": (
            f"{kw} {node.test.value!r}: 恒假不可达块 "
            f"(行 {node.lineno})"
        ),
        "severity": "WARN",
        "suggestion": "移除死代码",
    }
class ArchRuleChecker:
    _dead_code_findings = staticmethod(_dead_code_findings)
    def __init__(self, max_dir_files: int = ARCH_DIR_MAX_FILES_DEFAULT,
                 allow_local_imports: bool = _ARCH_ALLOW_LOCAL_IMPORTS_DEFAULT,
                 max_file_lines: int = ARCH_FILE_MAX_LINES):
        _owner = "ArchRuleChecker"
        self.max_dir_files = _require_non_negative_int(
            _owner, "max_dir_files", max_dir_files)
        self.max_file_lines = _require_non_negative_int(
            _owner, "max_file_lines", max_file_lines)
        self.allow_local_imports = _require_bool(
            _owner, "allow_local_imports", allow_local_imports)
    def check_architecture_rules(self, dir_path: str,
                                 py_files: list[str],
                                 file_sizes: dict[str, int]) -> list[dict]:
        py_files = _rule_scope_files(py_files)
        violations = []
        for fpath, tree in _iter_file_trees(py_files):
            violations.extend(self._check_facade_symbols(fpath, tree))
            if not self.allow_local_imports:
                violations.extend(self._check_lazy_imports(fpath, tree))
            violations.extend(self._check_degrade_strategy(fpath, tree))
            violations.extend(self._check_bare_except(fpath, tree))
        violations.extend(self._check_single_responsibility(py_files))
        violations.extend(self._check_func_size(py_files))
        violations.extend(self._check_file_size(py_files, file_sizes))
        violations.extend(self._check_dir_file_count(py_files))
        violations.extend(
            self._circular_dependency_findings(dir_path, py_files))
        violations.extend(self._dead_code_findings(py_files))
        violations.extend(self._check_layered_arch(dir_path, py_files))
        return violations
    def _check_facade_symbols(self, fpath: str, tree: _ast.AST) -> list[dict]:
        if os.path.basename(fpath).lower() != '__init__.py':
            return []
        facade_count = sum(
            1 for node in iter_module_level_stmts(tree)
            if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef,
                                 _ast.ClassDef))
        )
        if facade_count <= ARCH_FACADE_MAX_SYMBOLS:
            return []
        return [{
            "rule_id": "ARCH-FACADE-001",
            "file": fpath,
            "message": (
                f"__init__.py 门面 {facade_count} 个超过阈值 "
                f"{ARCH_FACADE_MAX_SYMBOLS}"
            ),
            "severity": "BLOCK",
            "suggestion": "使用薄门面模式或子模块重导出",
        }]
    def _check_lazy_imports(self, fpath: str, tree: _ast.AST) -> list[dict]:
        violations = []
        reported_imports: set[_ast.AST] = set()
        for node in walk_nodes(tree):
            if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef,
                                 _ast.ClassDef)):
                violations.extend(
                    self._scope_import_findings(fpath, node, reported_imports))
        return violations
    @staticmethod
    def _scope_import_findings(fpath: str, node: _ast.AST,
                               reported_imports: set[_ast.AST]) -> list[dict]:
        violations = []
        container_kind = "类" if isinstance(node, _ast.ClassDef) else "函数"
        for child in iter_own_scope(
                node, skip_lambda=True, include_self=True):
            if not isinstance(child, (_ast.Import, _ast.ImportFrom)):
                continue
            if child in reported_imports:
                continue
            reported_imports.add(child)
            violations.append({
                "rule_id": "ARCH-IMPORT-001",
                "file": fpath,
                "message": (
                    f"{container_kind} '{node.name}' 内有 import 语句 "
                    f"(行 {child.lineno})"
                ),
                "severity": "BLOCK",
                "suggestion": "将 import 移至模块顶部",
            })
        return violations
    def _check_degrade_strategy(self, fpath: str, tree: _ast.AST) -> list[dict]:
        violations = []
        for node in walk_nodes(tree):
            if isinstance(node, (_ast.Try, TRY_STAR)):
                for handler in node.handlers:
                    matched_exc = _matched_import_error_name(handler.type)
                    if matched_exc is not None:
                        violations.extend(self._degrade_handler_findings(
                            fpath, matched_exc, handler))
        return violations
    @staticmethod
    def _degrade_handler_findings(fpath: str, matched_exc: str,
                                  handler: _ast.ExceptHandler) -> list[dict]:
        return [
            {
                "rule_id": "ARCH-DEGRADE-001",
                "file": fpath,
                "message": (
                    f"降级策略: except {matched_exc}: "
                    f"{name} = None (行 {lineno})"
                ),
                "severity": "BLOCK",
                "suggestion": "依赖缺失直接报错",
            }
            for name, lineno in _iter_handler_none_bindings(handler)
        ]
    def _check_bare_except(self, fpath: str, tree: _ast.AST) -> list[dict]:
        violations = []
        for node in walk_nodes(tree):
            if isinstance(node, _ast.ExceptHandler) and node.type is None:
                violations.append({
                    "rule_id": "ARCH-ERR-001",
                    "file": fpath,
                    "message": f"裸 except: (行 {node.lineno})",
                    "severity": "BLOCK",
                    "suggestion": "指定具体异常类型",
                })
        return violations
    def _check_single_responsibility(self, py_files: list[str]) -> list[dict]:
        violations = []
        for fpath, tree in _iter_file_trees(py_files):
            func_count, class_count = _count_module_symbols(tree)
            for kind, count, threshold in (
                    ("函数", func_count, ARCH_SRP_MAX_FUNCS),
                    ("类", class_count, ARCH_SRP_MAX_CLASSES)):
                if count <= threshold:
                    continue
                violations.append({
                    "rule_id": "ARCH-SRP-001",
                    "file": fpath,
                    "message": (
                        f"模块有 {count} 个{kind},超过阈值 {threshold},"
                        f"须按 GOV-01 治理（迁移无关职责/收敛依赖）"
                    ),
                    "severity": "WARN",
                    "suggestion": ("简化逻辑/消除重复/迁移无关职责到既有"
                                   "模块（GOV-01 禁止直接拆分）"),
                })
        return violations
    def _check_func_size(self, py_files: list[str]) -> list[dict]:
        violations = []
        for fpath, tree in _iter_file_trees(py_files):
            for node in walk_nodes(tree):
                if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
                    violations.extend(self._func_size_findings(fpath, node))
        return violations
    @staticmethod
    def _func_size_findings(fpath: str, node: _ast.AST) -> list[dict]:
        findings = []
        func_lines = node.end_lineno - definition_start_line(node) + 1
        if func_lines > ARCH_FUNC_MAX_LINES:
            findings.append({
                "rule_id": "ARCH-FUNC-001",
                "file": fpath,
                "message": (
                    f"函数 '{node.name}' {func_lines} 行,"
                    f"超过阈值 {ARCH_FUNC_MAX_LINES} 行"
                ),
                "severity": "BLOCK",
                "suggestion": "提取子函数或使用策略模式",
            })
        complexity = cyclomatic_complexity(
            node, partial(iter_own_scope, skip_lambda=True, include_self=True))
        if complexity > ARCH_FUNC_MAX_COMPLEXITY:
            findings.append({
                "rule_id": "ARCH-FUNC-001",
                "file": fpath,
                "message": (
                    f"函数 '{node.name}' 圈复杂度 {complexity},"
                    f"超过阈值 {ARCH_FUNC_MAX_COMPLEXITY}"
                ),
                "severity": "BLOCK",
                "suggestion": "提取子函数或使用策略模式降低复杂度",
            })
        return findings
    def _check_file_size(self, py_files: list[str],
                          file_sizes: dict[str, int]) -> list[dict]:
        violations = []
        threshold = self.max_file_lines
        for fpath in py_files:
            n_lines = file_sizes.get(fpath)
            if n_lines is None:
                continue
            if n_lines > threshold:
                violations.append({
                    "rule_id": "ARCH-FILE-001",
                    "file": fpath,
                    "message": (
                        f"文件 {os.path.basename(fpath)} {n_lines} 行,"
                        f"超过阈值 {threshold} 行"
                    ),
                    "severity": "BLOCK",
                    "suggestion": ("简化逻辑/消除重复/迁移无关职责到既有"
                                   "模块（GOV-01 禁止拆分）"),
                })
        return violations
    def _check_dir_file_count(self, py_files: list[str]) -> list[dict]:
        violations = []
        threshold = self.max_dir_files
        for directory, file_count in sorted(_dir_file_counts(py_files).items()):
            if file_count <= threshold:
                continue
            violations.append({
                "rule_id": "ARCH-DIR-001",
                "file": directory,
                "message": (
                    f"目录有 {file_count} 个 .py 文件,"
                    f"超过阈值 {threshold}"
                ),
                "severity": "WARN",
                "suggestion": "整合相关模块/收敛依赖（GOV-01 禁止拆分）",
            })
        return violations
    @staticmethod
    def _circular_dependency_findings(dir_path: str,
                                      py_files: list[str]) -> list[dict]:
        imports = _build_import_graph(dir_path, py_files)
        return [
            _cycle_finding(dir_path, cycle)
            for cycle in detect_cycles(imports)
        ]
    def _check_layered_arch(self, dir_path: str,
                             py_files: list[str]) -> list[dict]:
        violations = []
        resolved_files = []
        for fpath in py_files:
            resolved = _relative_path_parts(fpath, dir_path)
            if resolved is None:
                continue
            rel, parts = resolved
            scoped = _layer_scope_parts(dir_path, parts)
            if len(scoped) > 1:
                resolved_files.append((fpath, rel, parts, scoped))
        if not any(_is_layer_marker(scoped[0])
                   for _fpath, _rel, _parts, scoped in resolved_files):
            return []
        for fpath, rel, scoped_parts, scoped in resolved_files:
            layer_name = scoped[0]
            if _is_known_layer_dir(layer_name.lower()):
                continue
            layer_path = os.path.join(
                dir_path,
                *scoped_parts[:len(scoped_parts) - len(scoped) + 1])
            if _has_package_init(layer_path):
                continue
            violations.append({
                "rule_id": "ARCH-LAYER-001",
                "file": fpath,
                "message": (
                    f"文件 '{rel}' 位于未识别的架构层 '{layer_name}',"
                    f"建议移至标准层目录"
                ),
                "severity": "WARN",
                "suggestion": "将代码归入正确的架构层",
            })
        return violations
def _layer_scope_parts(dir_path: str, parts: list[str]) -> list[str]:
    cut = 0
    while cut < len(parts) - 1 and parts[cut].lower() in _NEUTRAL_PROJECT_DIRS:
        cut += 1
    scoped = parts[cut:]
    while (len(scoped) > 2
           and not _is_known_layer_dir(scoped[0].lower())
           and _has_package_init(
               os.path.join(dir_path, *parts[:len(parts) - len(scoped) + 1]))):
        scoped = scoped[1:]
    return scoped
def _relative_path_parts(fpath: str, dir_path: str) -> tuple[str, list[str]] | None:
    try:
        rel = os.path.relpath(fpath, dir_path)
    except ValueError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_relative_path_parts:ValueError')
        return None
    return rel, rel.replace(os.sep, '/').split('/')
class ArchitecturePrinciple(Enum):
    SINGLE_RESPONSIBILITY = "single_responsibility"
    LAYERED_ARCH = "layered_architecture"
    THIN_FACADE = "thin_facade"
    STATIC_IMPORT = "static_import"
    ZERO_DEGRADATION = "zero_degradation"
    FUNC_SIZE_LIMIT = "func_size_limit"
    FILE_SIZE_LIMIT = "file_size_limit"
    DIR_FILE_LIMIT = "dir_file_limit"
    CIRCULAR_FREE = "circular_free"
    NO_DEAD_CODE = "no_dead_code"
    EXPLICIT_ERROR = "explicit_error"
@dataclass
class ArchitectureRule:
    principle: ArchitecturePrinciple
    rule_id: str
    description: str
    severity: str
    check_fn_name: str
    auto_fixable: bool = False
    threshold: int | None = None
    suggestion: str = ""
    def to_dict(self) -> dict:
        return {
            "principle": self.principle.value,
            "rule_id": self.rule_id,
            "description": self.description,
            "severity": self.severity,
            "check_fn_name": self.check_fn_name,
            "auto_fixable": self.auto_fixable,
            "threshold": self.threshold,
            "suggestion": self.suggestion,
        }
BUILTIN_ARCHITECTURE_RULES: list[ArchitectureRule] = [
    ArchitectureRule(
        ArchitecturePrinciple.SINGLE_RESPONSIBILITY,
        "ARCH-SRP-001",
        "每个模块应只有一个职责域,函数数 >30 或类数 >10 的模块应治理（GOV-01 禁止拆分）",
        "WARN",
        "_check_single_responsibility",
        auto_fixable=False,
        threshold=ARCH_SRP_MAX_FUNCS,
        suggestion="迁移无关职责到既有模块/收敛依赖/提取同模块私有实现",
    ),
    ArchitectureRule(
        ArchitecturePrinciple.THIN_FACADE,
        "ARCH-FACADE-001",
        "__init__.py 门面函数 ≤9 个,超出需薄门面化",
        "BLOCK",
        "_check_facade_symbols",
        auto_fixable=False,
        threshold=ARCH_FACADE_MAX_SYMBOLS,
        suggestion="使用薄门面模式或子模块重导出",
    ),
    ArchitectureRule(
        ArchitecturePrinciple.STATIC_IMPORT,
        "ARCH-IMPORT-001",
        "所有 import 必须在模块顶部,禁止函数/类体内 import",
        "BLOCK",
        "_check_lazy_imports",
        auto_fixable=False,
        suggestion="将 import 移至模块顶部",
    ),
    ArchitectureRule(
        ArchitecturePrinciple.ZERO_DEGRADATION,
        "ARCH-DEGRADE-001",
        "禁止 except ImportError/ModuleNotFoundError: xxx = None 静默降级模式",
        "BLOCK",
        "_check_degrade_strategy",
        auto_fixable=False,
        suggestion="依赖缺失直接报错,不静默降级",
    ),
    ArchitectureRule(
        ArchitecturePrinciple.FUNC_SIZE_LIMIT,
        "ARCH-FUNC-001",
        "函数 ≤300 行,圈复杂度 ≤15",
        "BLOCK",
        "_check_func_size",
        auto_fixable=False,
        threshold=ARCH_FUNC_MAX_LINES,
        suggestion="提取子函数或使用策略模式",
    ),
    ArchitectureRule(
        ArchitecturePrinciple.FILE_SIZE_LIMIT,
        "ARCH-FILE-001",
        "文件 ≤3000 行,超限必须按 GOV-01 治理（禁止拆分）",
        "BLOCK",
        "_check_file_size",
        auto_fixable=False,
        threshold=ARCH_FILE_MAX_LINES,
        suggestion="简化逻辑/消除重复/迁移无关职责到既有模块",
    ),
    ArchitectureRule(
        ArchitecturePrinciple.DIR_FILE_LIMIT,
        "ARCH-DIR-001",
        "单目录 .py 文件 ≤50 个,超限需模块整合",
        "WARN",
        "_check_dir_file_count",
        auto_fixable=False,
        threshold=ARCH_DIR_MAX_FILES_DEFAULT,
        suggestion="整合相关模块/收敛依赖（GOV-01 禁止拆分）",
    ),
    ArchitectureRule(
        ArchitecturePrinciple.CIRCULAR_FREE,
        "ARCH-CIRC-001",
        "禁止模块级循环依赖",
        "BLOCK",
        "_circular_dependency_findings",
        auto_fixable=False,
        suggestion="收敛到既有下层模块或经包入口注入，禁止新建模块消环",
    ),
    ArchitectureRule(
        ArchitecturePrinciple.NO_DEAD_CODE,
        "ARCH-DEAD-001",
        "禁止死代码:空函数体、if False: 块、不可达代码",
        "WARN",
        "_dead_code_findings",
        auto_fixable=False,
        suggestion="移除死代码",
    ),
    ArchitectureRule(
        ArchitecturePrinciple.EXPLICIT_ERROR,
        "ARCH-ERR-001",
        "禁止裸 except: 和过于宽泛的异常捕获",
        "BLOCK",
        "_check_bare_except",
        auto_fixable=False,
        suggestion="指定具体异常类型",
    ),
    ArchitectureRule(
        ArchitecturePrinciple.LAYERED_ARCH,
        "ARCH-LAYER-001",
        "代码应遵循分层架构:core→domain→application→infrastructure→presentation→shared",
        "WARN",
        "_check_layered_arch",
        auto_fixable=False,
        suggestion="将代码归入正确的架构层",
    ),
]
def get_architecture_rules() -> list[ArchitectureRule]:
    return [replace(rule) for rule in BUILTIN_ARCHITECTURE_RULES]
_WORD_SEP_RE = re.compile(r'[^0-9a-zA-Z]+')
_CAMEL_RE = re.compile(r'[A-Z]+(?![a-z])|[A-Z][a-z]+|[a-z0-9]+')
def _segment_tokens(seg: str) -> list[str]:
    tokens: list[str] = []
    for tok in _WORD_SEP_RE.split(seg):
        if not tok:
            continue
        tokens.append(tok.lower())
        parts = _CAMEL_RE.findall(tok)
        if len(parts) > 1:
            tokens.extend(p.lower() for p in parts)
    return tokens
def path_tokens(filepath: str) -> list[str]:
    if not isinstance(filepath, str):
        return []
    return [
        token
        for seg in re.split(r'[\\/]+', filepath)
        for token in _segment_tokens(seg)
    ]
LAYER_KEYWORDS: tuple[tuple[str, tuple[tuple[str, ...], ...]], ...] = (
    ("domain", (("domain",), ("domains",), ("model",), ("models",),
                 ("entity",), ("entities",))),
    ("application", (("service",), ("services",), ("use", "case"),
                      ("use", "cases"), ("usecase",), ("usecases",),
                      ("application",), ("applications",))),
    ("infrastructure", (("infrastructure",), ("infrastructures",),
                         ("infra",), ("repository",), ("repositories",),
                         ("db",), ("database",), ("databases",),
                         ("adapter",), ("adapters",),
                         ("container",), ("containers",))),
    ("presentation", (("api",), ("apis",), ("controller",), ("controllers",),
                       ("view",), ("views",), ("presentation",),
                       ("presentations",), ("handler",), ("handlers",))),
    ("shared", (("core",), ("shared",), ("common",), ("commons",),
                 ("util",), ("utils",), ("utility",), ("utilities",),
                 ("helper",), ("helpers",))),
)
UTIL_TOKENS = frozenset(
    {"util", "utils", "utility", "utilities", "helper", "helpers"})
def _is_layer_marker(name: str) -> bool:
    lowered = str(name or "").lower()
    return lowered in _VALID_ARCH_LAYERS or detect_layer(lowered) != "unknown"
def _is_known_layer_dir(name: str) -> bool:
    return name in _LAYER_EXEMPT_DIRS or _is_layer_marker(name)
def _detect_layer_tokens(tokens: list[str]) -> str:
    token_set = set(tokens)
    for layer, keyword_groups in LAYER_KEYWORDS:
        if any(_layer_group_hit(group, tokens, token_set)
               for group in keyword_groups):
            return layer
    return "unknown"
def detect_layer(filepath: str) -> str:
    if not isinstance(filepath, str):
        return "unknown"
    segments = re.split(r'[\\/]+', filepath)
    for segment in segments[:-1]:
        layer = _detect_layer_tokens(_segment_tokens(segment))
        if layer != "unknown":
            return layer
    return _detect_layer_tokens(path_tokens(filepath))
def _layer_group_hit(group: tuple, tokens: list[str],
                     token_set: set[str]) -> bool:
    if len(group) == 1:
        return group[0] in token_set
    n = len(group)
    return any(tuple(tokens[i:i + n]) == group
               for i in range(len(tokens) - n + 1))
def _arch_check_content_length(content: str, details: list[dict],
                               suggestions: list[str]) -> bool:
    if not content:
        return False
    lines = count_lines(content)
    if lines <= ARCH_FILE_MAX_LINES:
        return False
    details.append(make_detail(
        "file_too_long", "ARCH-01", "<content>", confidence=0.95,
        lines=lines,
        threshold=ARCH_FILE_MAX_LINES,
        message=f"文件行数 {lines} 超过阈值 {ARCH_FILE_MAX_LINES}",
    ))
    suggestions.append(
        "按 GOV-01 治理（简化/去重/迁移无关块），"
        f"把规模收敛到 {ARCH_FILE_MAX_LINES} 行以内")
    return True
def _existing_file_lines(fpath: str) -> int | None:
    source = read_source(fpath)
    if source is None:
        logger.warning(
            "architecture_check: 既有文件不可读，跳过行数检查: %s", fpath)
        return None
    return count_lines(source)
def _arch_check_existing_files(skill_dir: str, details: list[dict],
                               suggestions: list[str]) -> bool:
    if not (skill_dir and os.path.isdir(skill_dir)):
        return False
    try:
        py_files = _generic_py_files(skill_dir)
    except OSError as exc:
        logger.warning(
            "architecture_check: 列举目录失败，跳过既有文件扫描: %s (%s)",
            skill_dir, exc)
        return False
    violated = False
    root = os.path.abspath(skill_dir)
    for fpath in py_files:
        if is_test_file_path(str(fpath)):
            continue
        flines = _existing_file_lines(str(fpath))
        if flines is None or flines <= ARCH_FILE_MAX_LINES:
            continue
        fname = os.path.relpath(fpath, root).replace(os.sep, "/")
        violated = True
        details.append(make_detail(
            "existing_file_too_long", "ARCH-02", "<file>", confidence=0.95,
            file=fname,
            lines=flines,
            threshold=ARCH_FILE_MAX_LINES,
            message=f"{fname} 已有 {flines} 行，超过阈值 {ARCH_FILE_MAX_LINES}",
        ))
        suggestions.append(
            f"{fname} 已有 {flines} 行，按 GOV-01 治理"
            "（简化/去重/迁移无关块到既有职责模块），不新增文件")
    return violated
def _arch_check_class_methods(content: str, details: list[dict],
                              suggestions: list[str]) -> bool:
    if not content:
        return False
    try:
        tree = parse_cached(content)
    except PARSE_DEGRADE_EXC as e:
        logger.debug("suppressed parse error: %s", e)
        details.append(make_detail(
            "syntax_error", "ARCH-04", "<content>", confidence=1.0,
            message="无法解析 content 的 AST",
        ))
        return True
    violated = False
    for cls in (n for n in walk_nodes(tree) if isinstance(n, _ast.ClassDef)):
        methods = direct_class_methods(cls)
        if len(methods) <= PRE_MAX_CLASS_METHODS:
            continue
        violated = True
        details.append(make_detail(
            "class_too_many_methods", "ARCH-03", "<class>", confidence=0.9,
            **{"class": cls.name},
            methods=len(methods),
            threshold=PRE_MAX_CLASS_METHODS,
        ))
        suggestions.append(
            f"类 {cls.name} 方法数 {len(methods)} 过多，按 GOV-01 "
            "简化分派/消除重复/提取同模块私有实现，禁止拆分文件或模块")
    return violated
_ARCH_RULE_IDS: dict[str, str] = {
    "file_too_long": "ARCH-FILE-001",
    "existing_file_too_long": "ARCH-FILE-001",
    "class_too_many_methods": "ARCH-SRP-001",
}
def _inject_arch_rules(details: list[dict], suggestions: list[str]) -> None:
    arch_rules = {r.rule_id: r for r in get_architecture_rules()}
    for detail in details:
        rule = arch_rules.get(_ARCH_RULE_IDS.get(str(detail.get("issue", "")), ""))
        if rule is not None:
            detail["arch_rule"] = rule.to_dict()
            if rule.suggestion and rule.suggestion not in suggestions:
                suggestions.append(rule.suggestion)
def check_architecture(skill_dir: str | os.PathLike = "",
                       content: str = "") -> PreinterventionResult:
    skill_dir = normalize_input(skill_dir, "check_architecture 参数 skill_dir",
                                 allow_path=True)
    content = normalize_input(content, "check_architecture 参数 content")
    details: list[dict] = []
    suggestions: list[str] = []
    violated_a = _arch_check_content_length(content, details, suggestions)
    violated_b = _arch_check_existing_files(skill_dir, details, suggestions)
    violated_c = _arch_check_class_methods(content, details, suggestions)
    _inject_arch_rules(details, suggestions)
    passed = not (violated_a or violated_b or violated_c)
    return finish_check("architecture_check", "架构分层检查", passed,
                        SEVERITY_BLOCKING, details, suggestions)
def _inactive_branch_import_ids(ftree: _ast.AST) -> set[int]:
    inactive: set[int] = set()
    typing_aliases = typing_guard_aliases(ftree)
    type_checking_names = typing_type_checking_names(ftree) or None
    for node in iter_module_level_stmts(ftree):
        if not isinstance(node, _ast.If):
            continue
        test = node.test
        negated = isinstance(test, _ast.UnaryOp) and isinstance(test.op, _ast.Not)
        if negated:
            test = test.operand
        if isinstance(test, _ast.Constant):
            condition_value = bool(test.value)
            if negated:
                condition_value = not condition_value
            inactive_stmts = node.orelse if condition_value else node.body
        else:
            main_branch = main_guard_branch(test)
            if main_branch is not None:
                if negated:
                    main_branch = not main_branch
                inactive_stmts = node.body if main_branch else node.orelse
            else:
                if not (is_main_check(test) or is_type_checking_guard(
                        test, typing_aliases, type_checking_names)):
                    continue
                inactive_stmts = node.orelse if negated else node.body
        for stmt in inactive_stmts:
            for sub in walk_nodes(stmt):
                if isinstance(sub, (_ast.Import, _ast.ImportFrom)):
                    inactive.add(id(sub))
    return inactive
def _collect_import_deps(ftree: _ast.AST, module_stems: set,
                         package_stems: set) -> set:
    deps = set()
    inactive = _inactive_branch_import_ids(ftree)
    for node in iter_module_level_stmts(ftree):
        if id(node) in inactive:
            continue
        if isinstance(node, _ast.ImportFrom):
            deps |= _importfrom_node_deps(
                node, module_stems, package_stems)
        elif isinstance(node, _ast.Import):
            deps |= _import_node_deps(node, module_stems, package_stems)
    return deps
def _importfrom_node_deps(node: _ast.ImportFrom, module_stems: set,
                          package_stems: set) -> set:
    deps = set()
    module_parts = node.module.split(".") if node.module else []
    if module_parts:
        if (module_parts[0] in package_stems and len(module_parts) > 1
                and module_parts[1] in module_stems):
            deps.add(module_parts[1])
        elif module_parts[0] in module_stems:
            deps.add(module_parts[0])
    may_import_submodule = (not node.module or bool(
        module_parts and module_parts[-1] in package_stems))
    if may_import_submodule:
        deps.update(
            alias.name for alias in node.names
            if alias.name != "*" and alias.name in module_stems)
    return deps
def _import_node_deps(node: _ast.Import, module_stems: set,
                      package_stems: set) -> set:
    deps = set()
    for alias in node.names:
        parts = alias.name.split(".")
        top = parts[0]
        if (top in package_stems and len(parts) > 1
                and parts[1] in module_stems):
            deps.add(parts[1])
        elif top in module_stems:
            deps.add(top)
    return deps
def _scan_unused_imports(tree: _ast.Module) -> set[str]:
    entries, used_names, exported_names = collect_import_usage(tree)
    return {name for name, _line, _desc in entries
            if name not in used_names and name not in exported_names}
def _module_stem(module_name: str) -> str:
    return module_name.removesuffix('.__init__').rsplit('.', 1)[-1]
def _collect_py_files(skill_dir: str, recursive: bool) -> tuple[list, set]:
    if recursive:
        py_files = _collect_py_files_recursive(skill_dir)
    else:
        py_files = _collect_py_files_flat(skill_dir)
    module_stems = {_module_stem(m) for m, _p in py_files}
    return py_files, module_stems
def _collect_py_files_recursive(skill_dir: str) -> list[tuple[str, str]]:
    py_files = []
    for path in _generic_py_files(skill_dir):
        identity = _module_identity(str(path), skill_dir)
        if identity is not None:
            py_files.append((identity[0], str(path)))
    py_files.sort()
    return py_files
def _collect_py_files_flat(skill_dir: str) -> list[tuple[str, str]]:
    try:
        entries = os.listdir(skill_dir)
    except OSError as exc:
        logger.warning(
            "import_structure_check: 列举目录失败，跳过循环导入扫描: %s (%s)",
            skill_dir, exc)
        return []
    return sorted(
        (os.path.splitext(f)[0], os.path.join(skill_dir, f))
        for f in entries
        if (is_py_source_file(f) and not f.startswith('.')
            and os.path.isfile(os.path.join(skill_dir, f))))
def _preintervention_build_import_graph(py_files: list, module_stems: set) -> dict:
    import_graph: dict[str, set] = {}
    package_stems = {
        _module_stem(module_name)
        for module_name, _fpath in py_files
        if module_name == "__init__" or module_name.endswith(".__init__")
    }
    package_stems.update(
        os.path.basename(os.path.dirname(fpath))
        for module_name, fpath in py_files
        if module_name == "__init__")
    for module_name, fpath in py_files:
        _, ftree = parse_py_file(fpath, quiet=True)
        if ftree is None:
            continue
        import_graph[module_name] = _collect_import_deps(
            ftree, module_stems, package_stems)
    return import_graph
def _resolve_import_graph(import_graph: dict) -> dict:
    keys = list(import_graph)
    suffix_map: dict[str, list] = {}
    for k in keys:
        suffix_map.setdefault(k.rsplit('.', 1)[-1], []).append(k)
    for mod in keys:
        import_graph[mod] = {_resolve_import_dep(d, import_graph, suffix_map)
                             for d in import_graph[mod]}
        import_graph[mod].discard(mod)
    return import_graph
def _resolve_import_dep(dep: str, import_graph: dict,
                        suffix_map: dict[str, list]) -> str:
    if dep in import_graph:
        return dep
    pkg_init = f"{dep}.__init__"
    if pkg_init in import_graph:
        return pkg_init
    cands = [k for k in suffix_map.get(dep.rsplit('.', 1)[-1], [])
             if k.endswith("." + dep)]
    return cands[0] if len(cands) == 1 else dep
def check_import_structure(content: str = "", skill_dir: str | os.PathLike = "",
                           filename: str = "",
                           recursive: bool = False) -> PreinterventionResult:
    content = normalize_input(content, "check_import_structure 参数 content")
    skill_dir = normalize_input(skill_dir, "check_import_structure 参数 skill_dir",
                                 allow_path=True)
    filename = normalize_input(filename, "check_import_structure 参数 filename",
                               allow_path=True)
    details: list[dict] = []
    suggestions: list[str] = []
    passed = True
    if content:
        tree, early = prepare_tree(content, "import_structure_check")
        if early is not None:
            return early
        if _check_unused_imports_phase(tree, details, suggestions, filename):
            passed = False
    if _check_circular_imports_phase(skill_dir, recursive, details, suggestions):
        passed = False
    return finish_check("import_structure_check", "导入结构检查", passed,
                        SEVERITY_WARNING, details, suggestions)
def _check_unused_imports_phase(tree: _ast.Module, details: list[dict],
                                suggestions: list[str],
                                filename: str) -> bool:
    if is_package_init_path(filename):
        return False
    unused = _scan_unused_imports(tree)
    if not unused:
        return False
    details.append(make_detail(
        "unused_imports", "IMP-01", "<unknown>", confidence=0.8,
        imports=sorted(unused),
        count=len(unused),
    ))
    suggestions.append(f"发现 {len(unused)} 个未使用的导入: {sorted(unused)}")
    return True
def _check_circular_imports_phase(skill_dir: str, recursive: bool,
                                  details: list[dict],
                                  suggestions: list[str]) -> bool:
    if not (skill_dir and os.path.isdir(skill_dir)):
        return False
    py_files, module_stems = _collect_py_files(skill_dir, recursive)
    if recursive:
        import_graph = _build_import_graph(
            skill_dir, [fpath for _module_name, fpath in py_files])
    else:
        import_graph = _resolve_import_graph(
            _preintervention_build_import_graph(py_files, module_stems))
    found = False
    for mod, deps in import_graph.items():
        for dep in sorted(deps):
            if mod < dep and mod in import_graph.get(dep, ()):
                found = True
                details.append(make_detail(
                    "circular_import", "IMP-02", "<unknown>", confidence=0.9,
                    module_a=mod,
                    module_b=dep,
                ))
                suggestions.append(f"检测到循环导入: {mod} <-> {dep}")
    for cycle in _sorted_long_cycles(import_graph):
        found = True
        path = " -> ".join(cycle)
        details.append(make_detail(
            "circular_import", "IMP-02", "<unknown>", confidence=0.9,
            cycle=path,
            modules=list(cycle[:-1]),
        ))
        suggestions.append(f"检测到循环导入: {path}")
    return found
def _sorted_long_cycles(import_graph: dict[str, set]) -> list[list[str]]:
    graph = {node: sorted(deps) for node, deps in import_graph.items()}
    long_cycles: list[list[str]] = []
    seen: set[frozenset[str]] = set()
    for cycle in detect_cycles(graph):
        if len(cycle) < 3:
            continue
        key = frozenset(cycle)
        if key in seen:
            continue
        seen.add(key)
        long_cycles.append(cycle + [cycle[0]])
    long_cycles.sort(key=lambda c: (len(c), c))
    return long_cycles
def collect_module_all_declaration(tree: _ast.AST) -> tuple[set[str], bool]:
    replay = replay_export_surface(tree)
    return set(replay.names), replay.declared
def _public_assignment_export_names(node: _ast.stmt) -> set[str]:
    if isinstance(node, _ast.Assign):
        targets = node.targets
    elif isinstance(node, _ast.AnnAssign) and node.value is not None:
        targets = [node.target]
    else:
        return set()
    return {
        name for target in targets for name in iter_unpack_target_names(target)
        if not name.startswith("_")
    }
def _collect_new_public_exports(content: str) -> set[str] | None:
    if not content:
        return None
    try:
        tree = parse_cached(content)
    except PARSE_DEGRADE_EXC as e:
        logger.warning(
            "dependency_management_check: skip file with syntax error: %s", e)
        return None
    exports: set[str] = extract_all_declarations(tree)
    for node in iter_module_level_stmts(tree):
        if (isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef, _ast.ClassDef))
                and not node.name.startswith("_")):
            exports.add(node.name)
            continue
        exports.update(
            name for name in _public_assignment_export_names(node)
            if name.isupper())
    return exports
def _parse_init_tree(init_path: str) -> _ast.Module | None:
    _init_content, init_tree = parse_py_file(init_path, quiet=True)
    if init_tree is None:
        logger.warning(
            "dependency_management_check: __init__.py 读取或解析失败，"
            "跳过导出检查: %s", init_path)
    return init_tree
def _importfrom_base_parts(node: _ast.ImportFrom,
                           package_parts: list[str]) -> list[str] | None:
    module_parts = node.module.split(".") if node.module else []
    if not node.level:
        return module_parts
    up = node.level - 1
    if up > len(package_parts):
        return None
    return [*package_parts[:len(package_parts) - up], *module_parts]
def _module_registered_in_init(module_parts: list[str], public_names: set[str],
                               init_tree: _ast.Module,
                               package_parts: list[str]) -> bool:
    expected_module = (*package_parts, *module_parts)
    inactive_imports = _inactive_branch_import_ids(init_tree)
    for node in iter_module_level_stmts(init_tree):
        if id(node) in inactive_imports:
            continue
        if isinstance(node, _ast.Import):
            if any(tuple(alias.name.split(".")) == expected_module
                   for alias in node.names):
                return True
            continue
        if not isinstance(node, _ast.ImportFrom):
            continue
        base = _importfrom_base_parts(node, package_parts)
        if base is None:
            continue
        for alias in node.names:
            if alias.name == "*":
                if tuple(base) == expected_module:
                    return True
                continue
            if (*base, alias.name) == expected_module:
                return True
            if tuple(base) == expected_module and alias.name in public_names:
                return True
    return False
def _package_init_for(filename: str, skill_dir: str) -> str | None:
    root = os.path.abspath(skill_dir)
    file_path = filename if os.path.isabs(filename) else os.path.join(
        root, filename)
    current = os.path.dirname(os.path.abspath(file_path))
    try:
        rel = os.path.relpath(current, root)
    except ValueError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_package_init_for:ValueError')
        return None
    if rel == os.pardir or rel.startswith(os.pardir + os.sep):
        return None
    while True:
        for name in ('__init__.py', '__INIT__.py'):
            candidate = os.path.join(current, name)
            if os.path.isfile(candidate):
                return candidate
        if os.path.normcase(current) == os.path.normcase(root):
            return None
        parent = os.path.dirname(current)
        if parent == current:
            return None
        current = parent
def _module_parts_from_package(filename: str,
                               package_dir: str) -> list[str] | None:
    try:
        rel = os.path.relpath(os.path.splitext(os.path.abspath(filename))[0],
                              package_dir)
    except ValueError as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context='_module_parts_from_package:ValueError')
        return None
    parts = rel.replace(os.sep, '/').split('/')
    if not parts or any(part in ('', '.', '..') for part in parts):
        return None
    return parts
def _export_completeness_phase(content: str, skill_dir: str, filename: str,
                               details: list[dict],
                               suggestions: list[str]) -> bool:
    if not content or not filename:
        logger.debug(
            "dependency_management_check: 缺少模块路径，跳过导出完整性检查")
        return False
    module_name = os.path.splitext(os.path.basename(filename))[0]
    if not module_name or module_name.lower() == "__init__":
        return False
    init_path = _package_init_for(filename, skill_dir)
    if init_path is None:
        return False
    init_tree = _parse_init_tree(init_path)
    if init_tree is None:
        return False
    public_names = _collect_new_public_exports(content)
    if public_names is None:
        logger.debug(
            "dependency_management_check: content 不可解析，"
            "跳过导出完整性检查（不可判定≠空导出面）")
        return False
    package_dir = os.path.dirname(init_path)
    resolved_filename = filename if os.path.isabs(filename) else os.path.join(
        os.path.abspath(skill_dir), filename)
    module_parts = _module_parts_from_package(resolved_filename, package_dir)
    if module_parts is None:
        return False
    scan_root = os.path.abspath(skill_dir)
    # 所属包必须从 __init__.py 自身推导：module_parts 以 init 所在目录为基底，
    # 若改用模块所在目录（identity[1]），命名空间子目录（无 __init__.py）会被
    # 重复拼入 expected_module，绝对形注册全部漏判，相对形仅因两侧同向出错才侥幸命中。
    init_identity = _module_identity(init_path, scan_root)
    if init_identity is None:
        return False
    package_parts = [
        *_scan_root_package_parts(scan_root), *init_identity[1]]
    if _module_registered_in_init(
            module_parts, public_names, init_tree, package_parts):
        return False
    dotted = ".".join(module_parts)
    relative_base = "." + ".".join(module_parts[:-1])
    details.append(make_detail(
        "unregistered_module", "DEP-02",
        "__init__.py", confidence=0.80,
        module=dotted,
        module_leaf=module_parts[-1],
    ))
    suggestions.append(
        f"模块 {dotted} 未在 __init__.py 注册"
        f"（from {relative_base} import {module_parts[-1]}）")
    return True
def check_dependency_management(skill_dir: str | os.PathLike = "", content: str = "",
                                filename: str = "") -> PreinterventionResult:
    skill_dir = normalize_input(skill_dir, "check_dependency_management 参数 skill_dir",
                                 allow_path=True)
    content = normalize_input(content, "check_dependency_management 参数 content")
    filename = normalize_input(filename, "check_dependency_management 参数 filename",
                               allow_path=True)
    details: list[dict] = []
    suggestions: list[str] = []
    passed = True
    if skill_dir and os.path.isdir(skill_dir):
        passed = not _export_completeness_phase(
            content, skill_dir, filename, details, suggestions)
    return finish_check("dependency_management_check", "依赖管理检查", passed,
                        SEVERITY_WARNING, details, suggestions)
def _collect_public_api_names(tree: _ast.Module) -> set[str]:
    return {
        node.name for node in iter_module_level_stmts(tree)
        if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef, _ast.ClassDef))
        and not node.name.startswith("_")
    }
def _declaration_gaps(public_names: set[str], all_names: set[str],
                      has_all: bool, all_exact: bool = True
                      ) -> list[tuple[dict, str]]:
    if not public_names:
        return []
    if not has_all:
        return [(
            {"issue": "missing_all_declaration", "rule_id": "API-01",
             "locator": "module", "confidence": 0.90,
             "public_count": len(public_names)},
            f"模块有 {len(public_names)} 个公开 API 但未声明 __all__，建议添加",
        )]
    if not all_exact:
        return []
    return [
        ({"issue": "missing_from_all", "rule_id": "API-02",
          "locator": f"symbol:{name}", "confidence": 0.85, "symbol": name},
         f"公开 API '{name}' 未在 __all__ 中声明")
        for name in sorted(public_names - all_names)
    ]
def _scan_all_declaration(tree: _ast.AST,
                          details: list, suggestions: list) -> bool:
    replay = replay_export_surface(tree)
    gaps = _declaration_gaps(
        _collect_public_api_names(tree), set(replay.names),
        replay.declared, replay.exact)
    details.extend(make_detail(**detail_kw) for detail_kw, _msg in gaps)
    suggestions.extend(message for _detail_kw, message in gaps)
    return not gaps
def check_all_declaration(content: str = "") -> PreinterventionResult:
    content = normalize_input(content, "check_all_declaration 参数 content")
    tree, early = prepare_tree(content, "all_declaration_check")
    if early is not None:
        return early
    details: list[dict] = []
    suggestions: list[str] = []
    passed = _scan_all_declaration(tree, details, suggestions)
    result = finish_check("all_declaration_check", "__all__ 声明检查", passed,
                          SEVERITY_BLOCKING, details, suggestions)
    if passed:
        logger.debug("[preintervention] %s 通过（%d 项明细）",
                     result.check_name, len(result.details))
    else:
        logger.info("[preintervention] %s 未通过 severity=%s 明细 %d 项",
                    result.check_name, result.severity, len(result.details))
    return result
def _preintervention_structure_provider() -> dict:
    return {
        "architecture_check": check_architecture,
        "import_structure_check": check_import_structure,
        "dependency_management_check": check_dependency_management,
        "all_declaration_check": check_all_declaration,
    }
register_check_provider(_preintervention_structure_provider)
_UTIL_BLOAT_FUNC_THRESHOLD = 20
def _util_bloat_issue(filepath: str, metrics: Any) -> dict | None:
    if not set(path_tokens(filepath)) & UTIL_TOKENS:
        return None
    util_funcs = sum(1 for f in metrics.functions if not f.is_method)
    if util_funcs <= _UTIL_BLOAT_FUNC_THRESHOLD:
        return None
    return {
        "code": "UTIL_BLOAT",
        "message": f"工具模块过大: {util_funcs} 个函数",
        "suggestion": ("按功能域把无关函数迁至既有职责模块（GOV-01 优先"
                       "收敛/迁移，禁止直接拆分）"),
    }
def _base_class_tail(base: Any) -> str:
    return str(base).split("[", 1)[0].rsplit(".", 1)[-1]
def _no_impl_issue(metrics: Any) -> dict | None:
    abstract = [c for c in metrics.classes if c.is_abstract]
    if not abstract:
        return None
    classes_by_name = {cls.name: cls for cls in metrics.classes}
    implemented_bases: set[str] = set()
    for cls in (c for c in metrics.classes if not c.is_abstract):
        pending = list(getattr(cls, "base_classes", ()))
        seen: set[str] = set()
        while pending:
            base_name = _base_class_tail(pending.pop())
            if not base_name or base_name in seen:
                continue
            seen.add(base_name)
            implemented_bases.add(base_name)
            parent = classes_by_name.get(base_name)
            if parent is not None:
                pending.extend(getattr(parent, "base_classes", ()))
    missing = [c.name for c in abstract if c.name not in implemented_bases]
    if not missing:
        return None
    return {
        "code": "NO_IMPL",
        "message": f"抽象类缺少实现: {', '.join(missing)}",
        "suggestion": "添加具体实现，或将抽象类迁至既有职责模块",
    }
class _ArchitectureLevel(Enum):
    SCRIPT = "script"
    MODULE = "module"
    APPLICATION = "application"
    SYSTEM = "system"
@dataclass
class _ArchitectureReport:
    score: int = 0
    level: _ArchitectureLevel = _ArchitectureLevel.SCRIPT
    dimensions: dict[str, int] = field(default_factory=dict)
    solid_violations: list[Finding] = field(default_factory=list)
    layer_violations: list[Finding] = field(default_factory=list)
    dependency_graph: dict = field(default_factory=dict)
    summary: str = ""
    analysis_error: str = ""
    def to_dict(self) -> dict:
        return {
            "score": self.score,
            "level": self.level.value if isinstance(self.level, _ArchitectureLevel) else self.level,
            "dimensions": self.dimensions,
            "solid_violations": [v.to_dict() if hasattr(v, "to_dict") else str(v) for v in self.solid_violations],
            "layer_violations": [v.to_dict() if hasattr(v, "to_dict") else str(v) for v in self.layer_violations],
            "dependency_graph": self.dependency_graph,
            "summary": self.summary,
            "analysis_error": self.analysis_error,
        }
@dataclass(frozen=True)
class _MethodCallShape:
    positional_capacity: float
    keyword_names: frozenset[str] | None
    required_count: int
    required_named: frozenset[tuple[str, int | None]]
    required_posonly: int
    positional_named: frozenset[str]
    keyword_only: frozenset[str]
    positional_name_positions: frozenset[tuple[str, int]]
    positional_only_names: frozenset[str]
def _method_call_shape(method) -> _MethodCallShape:
    sig = method.args
    has_receiver = bool(sig.posonlyargs or sig.args) and not is_static_method(method)
    positional_args = [*sig.posonlyargs, *sig.args]
    if has_receiver:
        positional_args = positional_args[1:]
    positional_count = len(positional_args)
    positional_capacity = (
        float("inf") if sig.vararg is not None else positional_count)
    required_positional = max(0, positional_count - len(sig.defaults))
    receiver_in_posonly = has_receiver and bool(sig.posonlyargs)
    posonly_count = len(sig.posonlyargs) - int(receiver_in_posonly)
    required_posonly = min(required_positional, posonly_count)
    required_named = frozenset(
        [(arg.arg, index)
         for index, arg in enumerate(positional_args[:required_positional])
         if index >= required_posonly]
        + [(arg.arg, None)
           for arg, default in zip(sig.kwonlyargs, sig.kw_defaults,
                                   strict=True)
           if default is None]
    )
    required_count = required_positional + sum(
        default is None for default in sig.kw_defaults)
    if sig.kwarg is not None:
        keyword_names = None
    else:
        keyword_args = [*sig.args, *sig.kwonlyargs]
        if has_receiver and not sig.posonlyargs:
            keyword_args = keyword_args[1:]
        keyword_names = frozenset(arg.arg for arg in keyword_args)
    positional_name_positions = frozenset(
        (arg.arg, index) for index, arg in enumerate(positional_args)
        if index >= posonly_count)
    positional_named = frozenset(
        name for name, _position in positional_name_positions)
    keyword_only = frozenset(arg.arg for arg in sig.kwonlyargs)
    return _MethodCallShape(
        positional_capacity, keyword_names, required_count,
        required_named, required_posonly, positional_named, keyword_only,
        positional_name_positions,
        frozenset(arg.arg for arg in positional_args[:posonly_count]))
def _capacity_label(value: float) -> str:
    return "任意" if value == float("inf") else str(int(value))
def _keyword_incompatibility(parent: frozenset[str] | None,
                             child: frozenset[str] | None) -> str:
    if parent is None:
        if child is None:
            return ""
        return f"关键字参数容量减少({len(child)} < 任意)"
    if child is None:
        return ""
    missing = parent - child
    if not missing:
        return ""
    detail = ", ".join(sorted(missing))
    if len(child) < len(parent):
        return (f"关键字参数容量减少({len(child)} < {len(parent)}; "
                f"缺少: {detail})")
    return f"关键字参数接受面收窄(缺少: {detail})"
def _required_argument_incompatibility(
        parent: _MethodCallShape, child: _MethodCallShape) -> str:
    parent_names = {name for name, _position in parent.required_named}
    unguaranteed = sorted(
        name for name, position in child.required_named
        if name not in parent_names
        and (position is None or position >= parent.required_posonly)
    )
    if not unguaranteed:
        return ""
    return "必需参数约束收紧(父类调用可省略: " + ", ".join(unguaranteed) + ")"
def _keyword_position_incompatibility(
        parent: _MethodCallShape, child: _MethodCallShape) -> str:
    parent_positions = dict(parent.positional_name_positions)
    parent_keywords = set(parent_positions) | parent.keyword_only
    accepts_arbitrary_keywords = parent.keyword_names is None
    if accepts_arbitrary_keywords:
        parent_keywords |= parent.positional_only_names
    collisions = []
    for name, child_position in child.positional_name_positions:
        if not accepts_arbitrary_keywords and name not in parent_keywords:
            continue
        parent_position = parent_positions.get(name)
        positional_count = max(child_position + 1, parent.required_posonly)
        if positional_count > parent.positional_capacity:
            continue
        if parent_position is not None and parent_position < positional_count:
            continue
        collisions.append(name)
    if not collisions:
        return ""
    return "位置/关键字参数重排导致重复绑定: " + ", ".join(sorted(collisions))
def _call_form_incompatibilities(
        parent: _MethodCallShape, child: _MethodCallShape) -> list[str]:
    issues: list[str] = []
    if child.required_posonly > parent.required_posonly:
        issues.append(
            "必需位置专用参数增加("
            f"{child.required_posonly} > {parent.required_posonly})")
    keyword_position_issue = _keyword_position_incompatibility(parent, child)
    if keyword_position_issue:
        issues.append(keyword_position_issue)
    forced_kwonly = sorted(child.keyword_only & parent.positional_named)
    required_kwonly = {
        name for name, position in child.required_named if position is None}
    required_forced = [name for name in forced_kwonly if name in required_kwonly]
    if required_forced:
        issues.append(
            "必需位置参数转为仅关键字参数("
            + ", ".join(required_forced) + ")")
    return issues
_SRP_IO_FUNCS = frozenset({"print", "open", "input", "read", "write"})
_SRP_COMPUTE_FUNCS = frozenset({"sum", "max", "min", "len", "range"})
_SRP_FORMAT_FUNCS = frozenset({"format", "join", "replace", "split"})
_SRP_FUNC_ROLE = {
    func_name: role
    for role, func_names in (
        ("io", _SRP_IO_FUNCS),
        ("compute", _SRP_COMPUTE_FUNCS),
        ("format", _SRP_FORMAT_FUNCS),
    )
    for func_name in func_names
}
def _srp_mixed_role_count(func_node: _ast.FunctionDef | _ast.AsyncFunctionDef) -> int:
    roles = {
        _SRP_FUNC_ROLE[child.func.id]
        for child in iter_own_scope(
            func_node, skip_lambda=True, include_self=True)
        if isinstance(child, _ast.Call)
        and isinstance(child.func, _ast.Name)
        and child.func.id in _SRP_FUNC_ROLE
    }
    return len(roles)
def _is_isinstance_guard(node: _ast.AST) -> bool:
    return (isinstance(node, _ast.If)
            and isinstance(node.test, _ast.Call)
            and isinstance(node.test.func, _ast.Name)
            and node.test.func.id == "isinstance")
def _effective_class_methods(
        node: _ast.ClassDef,
        classes_map: dict[str, _ast.ClassDef],
) -> dict[str, _ast.FunctionDef | _ast.AsyncFunctionDef]:
    methods = {m.name: m for m in direct_class_methods(node)}
    pending = [
        base.id for base in node.bases
        if isinstance(base, _ast.Name) and base.id in classes_map
    ]
    seen: set[str] = set()
    while pending:
        ancestor_name = pending.pop(0)
        if ancestor_name in seen:
            continue
        seen.add(ancestor_name)
        ancestor = classes_map[ancestor_name]
        for method in direct_class_methods(ancestor):
            methods.setdefault(method.name, method)
        pending.extend(
            base.id for base in ancestor.bases
            if isinstance(base, _ast.Name) and base.id in classes_map
        )
    return methods
def _lsp_violation_findings(
        classes_map: dict[str, _ast.ClassDef]) -> list[Finding]:
    findings: list[Finding] = []
    checked_method_pairs: set[tuple[int, int]] = set()
    for node in classes_map.values():
        if not node.bases:
            continue
        for base in node.bases:
            if not (isinstance(base, _ast.Name) and base.id in classes_map):
                continue
            findings.extend(
                _lsp_param_findings_for_pair(
                    classes_map[base.id], node, classes_map,
                    checked_method_pairs))
    return findings
def _lsp_param_findings_for_pair(
        parent: _ast.ClassDef,
        child: _ast.ClassDef,
        classes_map: dict[str, _ast.ClassDef] | None = None,
        checked_method_pairs: set[tuple[int, int]] | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    parent_methods = (
        {m.name: m for m in direct_class_methods(parent)}
        if classes_map is None
        else _effective_class_methods(parent, classes_map)
    )
    child_methods = {m.name: m for m in direct_class_methods(child)}
    for name, child_method in child_methods.items():
        if name not in parent_methods:
            continue
        parent_method = parent_methods[name]
        if checked_method_pairs is not None:
            method_pair = (id(child_method), id(parent_method))
            if method_pair in checked_method_pairs:
                continue
            checked_method_pairs.add(method_pair)
        parent_shape = _method_call_shape(parent_method)
        child_shape = _method_call_shape(child_method)
        incompatibilities: list[str] = []
        if child_shape.positional_capacity < parent_shape.positional_capacity:
            incompatibilities.append(
                "位置参数容量减少("
                f"{_capacity_label(child_shape.positional_capacity)} < "
                f"{_capacity_label(parent_shape.positional_capacity)})")
        keyword_issue = _keyword_incompatibility(
            parent_shape.keyword_names, child_shape.keyword_names)
        if keyword_issue:
            incompatibilities.append(keyword_issue)
        if child_shape.required_count > parent_shape.required_count:
            incompatibilities.append(
                f"必需参数增加({child_shape.required_count} > "
                f"{parent_shape.required_count})")
        required_issue = _required_argument_incompatibility(
            parent_shape, child_shape)
        if required_issue:
            incompatibilities.append(required_issue)
        incompatibilities.extend(
            _call_form_incompatibilities(parent_shape, child_shape))
        if incompatibilities:
            findings.append(Finding(
                rule_id="SOLID-LSP", severity=Severity.HIGH,
                location=f"{child.name}.{name}",
                message=("子类方法" + "，".join(incompatibilities)
                         + ",可能违反里氏替换"),
                suggestion="保持子类方法签名与父类一致",
            ))
    return findings
@dataclass
class _DependencyGraph:
    nodes: list[str] = field(default_factory=list)
    edges: list[dict[str, str]] = field(default_factory=list)
    _seen: set[str] = field(default_factory=set)
    def add_node(self, name: str) -> None:
        if name and name not in self._seen:
            self._seen.add(name)
            self.nodes.append(name)
    def add_edge(self, target: str, symbol: str) -> None:
        self.edges.append({"from": "<self>", "to": target, "symbol": symbol})
    def add_import_node(self, node: _ast.Import | _ast.ImportFrom) -> None:
        if isinstance(node, _ast.Import):
            for alias in node.names:
                self.add_node(alias.name.split(".")[0])
        else:
            self._add_from_import(node)
    def _add_from_import(self, node: _ast.ImportFrom) -> None:
        if node.level and not node.module:
            for alias in node.names:
                self._register_import(
                    "." * node.level + alias.name, alias.name)
            return
        target = ("." * node.level + node.module if node.level
                  else (node.module or "").split(".")[0])
        self.add_node(target)
        for alias in node.names:
            self._register_import(target, alias.name)
    def _register_import(self, target: str, symbol: str) -> None:
        if symbol == "*":
            return
        self.add_node(target)
        self.add_edge(target, symbol)
    def to_dict(self) -> dict[str, Any]:
        return {"nodes": list(self.nodes), "edges": list(self.edges)}
def _iter_framework_imports(tree: _ast.Module,
                            framework_modules: frozenset[str]
                            ) -> Iterator[tuple[_ast.AST, str, str]]:
    for node in walk_nodes(tree):
        if isinstance(node, _ast.ImportFrom):
            hit = _from_import_framework_hit(node, framework_modules)
            if hit is not None:
                yield hit
        elif isinstance(node, _ast.Import):
            yield from _plain_import_framework_hits(node, framework_modules)
def _from_import_framework_hit(node: _ast.ImportFrom,
                               framework_modules: frozenset[str]
                               ) -> tuple[_ast.AST, str, str] | None:
    if node.level:
        return None
    mod = node.module or ""
    top = mod.split(".")[0]
    return (node, mod, top) if top in framework_modules else None
def _plain_import_framework_hits(node: _ast.Import,
                                 framework_modules: frozenset[str]
                                 ) -> Iterator[tuple[_ast.AST, str, str]]:
    for alias in node.names:
        top = alias.name.split(".")[0]
        if top in framework_modules:
            yield node, alias.name, top
@dataclass(frozen=True)
class _FrameworkRule:
    rule_id: str
    severity: Any
    describe: Callable[[str, str], str]
    suggestion: str
    def findings(self, tree: _ast.Module,
                 framework_modules: frozenset[str]) -> list[Finding]:
        return [
            Finding(rule_id=self.rule_id, severity=self.severity,
                    line=node.lineno,
                    message=self.describe(full_name, top_name),
                    suggestion=self.suggestion)
            for node, full_name, top_name
            in _iter_framework_imports(tree, framework_modules)
        ]
_DIP_RULE = _FrameworkRule(
    "SOLID-DIP", Severity.MEDIUM,
    lambda full_name, _top: f"直接依赖具体框架: {full_name}",
    "通过抽象接口/适配器解耦")
_LAYER_RULE = _FrameworkRule(
    "LAYER-VIOLATION", Severity.HIGH,
    lambda _full_name, top: f"业务层直接依赖框架: {top}",
    "将框架依赖移至基础设施层,通过端口-适配器模式解耦")
_LAYER_RULE_APPLICABLE_LAYERS = frozenset({"unknown", "domain", "application"})
def _scan_entities(tree: _ast.Module) -> tuple[list[_ast.ClassDef], list, bool]:
    classes: list[_ast.ClassDef] = []
    functions: list = []
    has_imports = False
    for node in walk_nodes(tree):
        if isinstance(node, _ast.ClassDef):
            classes.append(node)
        elif isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            functions.append(node)
        elif isinstance(node, (_ast.Import, _ast.ImportFrom)):
            has_imports = True
    return classes, functions, has_imports
_SYSTEM_CLASS_THRESHOLD = 20
_APPLICATION_CLASS_THRESHOLD = 3
_SRP_MIXED_ROLE_THRESHOLD = 2
_ISP_METHOD_THRESHOLD = 20
def _arch_level_for(class_count: int, has_imports: bool) -> _ArchitectureLevel:
    if has_imports and class_count > _SYSTEM_CLASS_THRESHOLD:
        return _ArchitectureLevel.SYSTEM
    if class_count > _APPLICATION_CLASS_THRESHOLD:
        return _ArchitectureLevel.APPLICATION
    if class_count > 0:
        return _ArchitectureLevel.MODULE
    return _ArchitectureLevel.SCRIPT
class _ArchitectureExcellenceV3:
    SOLID_WEIGHTS: ClassVar[dict[str, float]] = {
        "S": 0.3, "O": 0.2, "L": 0.2, "I": 0.15, "D": 0.15}
    _FRAMEWORK_MODULES: ClassVar[frozenset[str]] = frozenset({
        "flask", "django", "fastapi", "requests", "sqlite3", "pymongo"})
    def analyze(self, filepath: str, code: str | None = None) -> _ArchitectureReport:
        tree = self._load_tree(filepath, code)
        if tree is None:
            return _ArchitectureReport(
                score=0,
                level=_ArchitectureLevel.SCRIPT,
                analysis_error="源码读取或解析失败，架构分析不可用",
            )
        classes, functions, has_imports = _scan_entities(tree)
        solid_results = self._check_solid(tree, classes, functions)
        layer_results = self._check_layers(tree, filepath)
        final_score = self._final_score(solid_results, layer_results)
        arch_level = _arch_level_for(len(classes), has_imports)
        return _ArchitectureReport(
            score=final_score,
            level=arch_level,
            dimensions={k: r["score"] for k, r in solid_results.items()},
            solid_violations=[
                v for r in solid_results.values() for v in r.get("findings", [])
            ],
            layer_violations=layer_results,
            dependency_graph=self._build_dependency_graph(tree),
            summary=(f"SOLID score: {final_score}/100, level: {arch_level.value}, "
                     f"classes: {len(classes)}, functions: {len(functions)}"),
        )
    def _load_tree(self, filepath: str, code: str | None) -> _ast.Module | None:
        filepath = normalize_filepath(filepath)
        if code is None:
            try:
                code = read_source_strict(filepath)
            except (OSError, UnicodeDecodeError, SyntaxError,
                    LookupError) as e:
                logger.warning("[ArchExcellence] 无法读取文件 %s: %s", filepath, e)
                return None
        tree, err = parse_ast_safely(code)
        if tree is None:
            logger.warning("[ArchExcellence] 无法解析源码 %s: %s", filepath, err)
        return tree
    def _final_score(self, solid_results: dict[str, dict],
                     layer_violations: list) -> int:
        weighted = sum(r["score"] * self.SOLID_WEIGHTS.get(k, 0)
                       for k, r in solid_results.items())
        return max(0, min(100, int(weighted - len(layer_violations) * 10)))
    @staticmethod
    def _solid_result(findings: list[Finding], penalty: int) -> dict:
        return {"score": max(0, 100 - penalty * len(findings)),
                "findings": findings}
    def _detect_srp(self, functions: list) -> dict:
        findings = [
            Finding(
                rule_id="SOLID-SRP", severity=Severity.MEDIUM,
                location=node.name, line=node.lineno,
                message=f"函数 '{node.name}' 混合了多种职责(IO/计算/格式化)",
                suggestion="提取同模块私有函数并收敛单一职责，禁止拆分文件或模块",
            )
            for node in functions
            if _srp_mixed_role_count(node) >= _SRP_MIXED_ROLE_THRESHOLD
        ]
        return self._solid_result(findings, 15)
    def _detect_ocp(self, tree: _ast.Module) -> dict:
        findings = [
            Finding(
                rule_id="SOLID-OCP", severity=Severity.MEDIUM,
                line=node.lineno,
                message="检测到 isinstance 类型判断,违反开闭原则",
                suggestion="使用多态或策略模式替代类型判断",
            )
            for node in walk_nodes(tree)
            if _is_isinstance_guard(node)
        ]
        return self._solid_result(findings, 10)
    def _detect_lsp(self, classes: list[_ast.ClassDef]) -> dict:
        classes_map = {node.name: node for node in classes}
        findings = _lsp_violation_findings(classes_map)
        return self._solid_result(findings, 20)
    def _detect_isp(self, classes: list[_ast.ClassDef]) -> dict:
        findings: list[Finding] = []
        for node in classes:
            method_count = len(direct_class_methods(node))
            if method_count <= _ISP_METHOD_THRESHOLD:
                continue
            findings.append(Finding(
                rule_id="SOLID-ISP", severity=Severity.LOW,
                location=node.name,
                message=(f"类 '{node.name}' 方法数({method_count})"
                         f"超过警戒值({_ISP_METHOD_THRESHOLD})"),
                suggestion="按调用方收敛接口并提取同模块私有实现，禁止拆分文件或模块",
            ))
        return self._solid_result(findings, 10)
    def _detect_dip(self, tree: _ast.Module) -> dict:
        findings = _DIP_RULE.findings(tree, self._FRAMEWORK_MODULES)
        return self._solid_result(findings, 10)
    def _check_solid(self, tree: _ast.Module,
                     classes: list[_ast.ClassDef] | None = None,
                     functions: list | None = None) -> dict[str, dict]:
        if classes is None:
            classes = [n for n in walk_nodes(tree) if isinstance(n, _ast.ClassDef)]
        if functions is None:
            functions = [n for n in walk_nodes(tree)
                         if isinstance(n, (_ast.FunctionDef, _ast.AsyncFunctionDef))]
        return {
            "S": self._detect_srp(functions),
            "O": self._detect_ocp(tree),
            "L": self._detect_lsp(classes),
            "I": self._detect_isp(classes),
            "D": self._detect_dip(tree),
        }
    def _check_layers(self, tree: _ast.Module,
                      filepath: str = "") -> list[Finding]:
        layer = detect_layer(filepath) if filepath else "unknown"
        if layer not in _LAYER_RULE_APPLICABLE_LAYERS:
            return []
        return _LAYER_RULE.findings(tree, self._FRAMEWORK_MODULES)
    def _build_dependency_graph(self, tree: _ast.Module) -> dict[str, Any]:
        graph = _DependencyGraph()
        for node in walk_nodes(tree):
            if isinstance(node, (_ast.Import, _ast.ImportFrom)):
                graph.add_import_node(node)
        return graph.to_dict()
def _solid_layer_violations(code: str, filepath: str) -> dict:
    fields: dict = {}
    try:
        arch = _ArchitectureExcellenceV3().analyze(filepath or "<string>", code=code)
        fields["architecture_score"] = arch.score
        if arch.analysis_error:
            fields["architecture_error"] = arch.analysis_error
            return fields
        if arch.solid_violations:
            fields["solid_violations"] = [
                getattr(v, "message", str(v)) for v in arch.solid_violations
            ]
        if arch.layer_violations:
            fields["layer_violations"] = [
                getattr(v, "message", str(v)) for v in arch.layer_violations
            ]
    except (AttributeError, KeyError, TypeError, ValueError, RuntimeError) as _e:
        log_swallowed(__name__, _e, context="review_architecture:analyze")
        fields["architecture_score"] = 0
        fields["architecture_error"] = "架构分析异常，详见日志"
    return fields
def review_architecture(code: str, metrics: Any,
                         filepath: str) -> dict:
    review = {
        "issues": [],
        "layer": detect_layer(filepath),
    }
    try:
        review["issues"] = [i for i in (
            _util_bloat_issue(filepath, metrics),
            _no_impl_issue(metrics)) if i]
    except (AttributeError, TypeError, KeyError) as _e:
        log_swallowed(__name__, _e, context="review_architecture:metrics")
        review["metrics_error"] = "架构指标分析异常，详见日志"
    review.update(_solid_layer_violations(code, filepath))
    review["ok"] = (not review["issues"]
                    and not review.get("solid_violations")
                    and not review.get("layer_violations")
                    and not review.get("architecture_error")
                    and not review.get("metrics_error"))
    return review

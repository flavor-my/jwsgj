from __future__ import annotations

import ast
import glob
import json
import os
import re
import subprocess
import sys
import threading
import time
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, ClassVar

from jwsgj.diag_guard_io import (
    atomic_write_text,
    read_source_text_strict,
    safe_delete,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
)
from jwsgj.diag_shared_ast_views import shared_walk
from jwsgj.diag_testing_source import (
    entry_nodes,
    iter_own_scope_nodes,
    iter_test_dirs,
    nodes_where,
    resolve_file_cache,
)
from jwsgj.diag_testing_test_index import (
    _internal_package_roots,
    imp_internal_target,
    iter_collectable_test_functions,
    load_test_ast,
)
from jwsgj.diag_types_defs import (
    TestMethodResult,
)
from jwsgj.diag_types_normalize import (
    as_number,
    is_finite_num,
    normalize_path_list,
)
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import get_temp_base, subprocess_noartifact_env
from jwsgj.runtime_scope import (
    SCAN_IGNORE_DIRS,
    TEST_ARTIFACT_DIRS,
    TEST_DIR_CANDIDATES,
    TEST_DIR_CANDIDATES_LOWER,
    is_backup_like_dir,
    is_py_source_file,
    is_test_source_basename,
    safe_relpath,
)

logger = get_module_logger(__name__)
__all__ = [
    'DEFAULT_COVERAGE_THRESHOLD',
    'DEFAULT_COVERAGE_TIMEOUT',
    'DEFAULT_PROJECT_CONFIG_NAME',
    'EFFECTIVE_LEVEL_DOMAIN',
    'SKIP_DIRS_LOWER',
    'TEST_DIR_CANDIDATES',
    'CoverageMap',
    'DjangoAdapter',
    'GenericAdapter',
    'PackageAdapter',
    'ProjectAdapter',
    'SkillAdapter',
    'apply_coverage_extras',
    'create_adapter',
    'detect_project_type',
    'diff_scan_reports',
    'export_gap_context',
    'file_to_module_path',
    'history_variance_warning',
    'is_outside_root',
    'iter_py_files_under',
    'iter_scoped_py',
    'iter_test_source_files',
    'load_config',
    'locate_pytest_summary_line',
    'norm_nonneg_int',
    'parse_pytest_summary_counts',
    'prune_scan_dirs',
    'resolve_project_path',
    'run_coverage_analysis',
    'step_err',
    'step_ok',
    'step_skip',
    'summarize_coverage_report',
    'write_coverage_payload',
]
logger.info("diag_testing_coverage 已加载：%d 项导出", len(__all__))
_PYTEST_DURATION_TAIL = r"(?:\s*\(\d+:\d{2}:\d{2}\))?"
_SUMMARY_OUTCOME_TOKENS = (
    # 与 pytest 终端汇总 KNOWN_TYPES 对齐："subtests passed/failed/skipped"
    # 为 pytest 9 原生 subTest 计数令牌；"rerun/reruns" 为
    # pytest-rerunfailures 计数令牌。缺失任一令牌会使整行汇总不匹配，
    # passed/failed 计数静默归零。
    "passed", "failed", "error", "errors", "skipped", "deselected",
    "xfailed", "xpassed", "warning", "warnings",
    "rerun", "reruns",
    "subtests passed", "subtests failed", "subtests skipped",
)
_SUMMARY_ITEM = r"[\d,]+ (?:" + "|".join(_SUMMARY_OUTCOME_TOKENS) + r")"
_PYTEST_QSUMMARY_RE = re.compile(
    r"(?:no tests ran|" + _SUMMARY_ITEM + r")"
    r"(?:, " + _SUMMARY_ITEM + r")*"
    r" in \d+(?:\.\d+)?s" + _PYTEST_DURATION_TAIL
)
_THOUSANDS_SEP_RE = re.compile(r"(?<=\d),(?=\d)")
_ANSI_CSI_RE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
_WRAPPED_SUMMARY_MIN_LEN = 10
def _is_wrapped_summary_line(stripped: str) -> bool:
    if not (stripped.startswith("=") and stripped.endswith("=")
            and len(stripped) > _WRAPPED_SUMMARY_MIN_LEN):
        return False
    summary = stripped.strip("=").strip()
    return bool(_PYTEST_QSUMMARY_RE.fullmatch(summary))
def locate_pytest_summary_line(output: str) -> str:
    normalized = _normalize_count_text(output)
    located = ""
    for line in normalized.splitlines():
        stripped = line.strip()
        if (_is_wrapped_summary_line(stripped)
                or _PYTEST_QSUMMARY_RE.fullmatch(stripped)):
            located = stripped
    return located
_SUMMARY_COUNT_PATTERNS: dict[str, str] = {
    "passed": r"(\d+) passed",
    "failed": r"(\d+) failed",
    "errors": r"(\d+) errors?",
    "skipped": r"(\d+) skipped",
    "xfailed": r"(\d+) xfailed",
    "xpassed": r"(\d+) xpassed",
    "deselected": r"(\d+) deselected",
}
_TEST_DIR_NAMES = TEST_ARTIFACT_DIRS
_TEST_INFRA_BASENAMES = frozenset({'conftest.py'})
_PROTECTED_INFRA_BASENAMES = _TEST_INFRA_BASENAMES | {'__init__.py'}
def _normalize_count_text(summary_line) -> str:
    if not isinstance(summary_line, str):
        return ""
    without_ansi = _ANSI_CSI_RE.sub("", summary_line)
    return _THOUSANDS_SEP_RE.sub("", without_ansi)
def parse_pytest_summary_counts(summary_line: str) -> dict[str, int]:
    normalized = _normalize_count_text(summary_line)
    return {
        key: int(m.group(1))
        if (m := re.search(pattern, normalized)) else 0
        for key, pattern in _SUMMARY_COUNT_PATTERNS.items()
    }
_ASSERT_CALL_ATTRS = frozenset(('raises', 'assertRaises', 'assertRaisesRegex'))
_NO_RAISES_NAMES = frozenset()
def _pytest_raises_bind_names(tree) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if (isinstance(node, ast.ImportFrom) and node.level == 0
                and node.module == 'pytest'):
            for alias in node.names:
                if alias.name == 'raises':
                    names.add(alias.asname or alias.name)
    return names
def _extract_except_type_names(type_expr) -> list:
    _names = []
    for _t in (type_expr.elts if isinstance(type_expr, ast.Tuple) else [type_expr]):
        if isinstance(_t, ast.Name):
            _names.append(_t.id)
        elif isinstance(_t, ast.Attribute):
            _names.append(_t.attr)
    return _names
def _handler_exc_names(node) -> list:
    if not isinstance(node, ast.ExceptHandler) or node.type is None:
        return []
    return _extract_except_type_names(node.type)
def _raises_call_exc_names(node, raises_names=_NO_RAISES_NAMES) -> list:
    if not isinstance(node, ast.Call):
        return []
    func = node.func
    if isinstance(func, ast.Attribute):
        if func.attr not in _ASSERT_CALL_ATTRS:
            return []
    elif not (isinstance(func, ast.Name) and func.id in raises_names):
        return []
    if node.args:
        type_expr = node.args[0]
    else:
        type_expr = next(
            (kw.value for kw in node.keywords
             if kw.arg == 'expected_exception'), None)
    if type_expr is None:
        return []
    return _extract_except_type_names(type_expr)
def _collect_tested_exception_types(test_trees) -> set:
    names: set[str] = set()
    for _tree in _unique_trees(test_trees):
        _raises_names = _pytest_raises_bind_names(_tree)
        for node in shared_walk(_tree):
            names.update(_handler_exc_names(node))
            names.update(_raises_call_exc_names(node, _raises_names))
    return names
def _coverage_callee_name(node) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    return None
_FUNCTION_APPROX_BRANCH_RATIO = 0.6
_FUNCTION_APPROX_STATEMENT_RATIO = 0.7
def _test_fn_signals(fn, other_test_names: set,
                     raises_names=_NO_RAISES_NAMES) -> tuple[bool, bool]:
    has_assertion = False
    calls_other = False
    for n in iter_own_scope_nodes(fn):
        if _is_assertion_node(n, raises_names):
            has_assertion = True
        if _coverage_callee_name(n) in other_test_names:
            calls_other = True
        if has_assertion and calls_other:
            break
    return has_assertion, calls_other
def _is_assertion_node(node, raises_names=_NO_RAISES_NAMES) -> bool:
    return (isinstance(node, ast.Assert)
            or _is_assertion_call(node, raises_names))
def _is_assertion_call(node, raises_names=_NO_RAISES_NAMES) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    if isinstance(func, ast.Attribute):
        return (func.attr in _ASSERT_CALL_ATTRS
                or func.attr.startswith('assert'))
    return isinstance(func, ast.Name) and func.id in raises_names
def _unique_trees(test_trees) -> list:
    _seen_ids: set[int] = set()
    _unique = []
    for _t in test_trees or ():
        if _t is None or id(_t) in _seen_ids:
            continue
        _seen_ids.add(id(_t))
        _unique.append(_t)
    return _unique
def _test_suite_quality_components(test_trees) -> tuple:
    _asserting = 0
    _independent = 0
    _n = 0
    for _tree in _unique_trees(test_trees):
        _test_fns = list(iter_collectable_test_functions(_tree))
        if not _test_fns:
            continue
        _raises_names = _pytest_raises_bind_names(_tree)
        _all_names = {fn.name for fn in _test_fns}
        for fn in _test_fns:
            has_assertion, calls_other = _test_fn_signals(
                fn, _all_names - {fn.name}, _raises_names)
            if has_assertion:
                _asserting += 1
            if not calls_other:
                _independent += 1
            _n += 1
    if _n == 0:
        return 0.0, 0.0
    return _asserting / _n, _independent / _n
def _has_named_test_module(mod_stem: str, test_files: set) -> bool:
    return f"test_{mod_stem}" in test_files or f"{mod_stem}_test" in test_files
def _is_test_side_rel(rel_path) -> bool:
    if not isinstance(rel_path, str) or not rel_path:
        return False
    parts = rel_path.replace('\\', '/').split('/')
    basename = parts[-1]
    if (basename.lower() in _TEST_INFRA_BASENAMES
            or is_test_source_basename(basename)):
        return True
    return any(part.lower() in _TEST_DIR_NAMES for part in parts[:-1])
_NO_DJANGO_TEST_BASENAMES: tuple[str, ...] = ()
def _django_test_basenames_for_root(root) -> tuple[str, ...]:
    if not root or detect_project_type(os.fspath(root)) != 'django':
        return _NO_DJANGO_TEST_BASENAMES
    return DjangoAdapter.DJANGO_TEST_BASENAMES
def _is_test_side_entry(entry, django_tests=_NO_DJANGO_TEST_BASENAMES) -> bool:
    if getattr(entry, 'is_test', False):
        return True
    if _is_test_side_rel(getattr(entry, 'rel_path', '')):
        return True
    return os.path.basename(getattr(entry, 'path', '')).lower() in django_tests
def _is_collectable_test_entry(entry, django_tests=_NO_DJANGO_TEST_BASENAMES) -> bool:
    if getattr(entry, 'is_test', False):
        return True
    return os.path.basename(getattr(entry, 'path', '')).lower() in django_tests
def _iter_production_entries(cache):
    django_tests = _django_test_basenames_for_root(
        getattr(cache, 'skill_dir', ''))
    for entry in cache.valid_entries:
        if _is_test_side_entry(entry, django_tests):
            continue
        yield entry
def _count_class_public_methods(cls, tested_function_names) -> tuple[int, int]:
    _total = 0
    _tested = 0
    for method in cls['methods']:
        if method.startswith('_'):
            continue
        _total += 1
        if method in tested_function_names:
            _tested += 1
    return _total, _tested
def _method_coverage_metrics(cache, tested_function_names) -> dict:
    total_methods = 0
    tested_methods = 0
    for entry in _iter_production_entries(cache):
        for cls in entry.classes:
            _total, _tested = _count_class_public_methods(
                cls, tested_function_names)
            total_methods += _total
            tested_methods += _tested
    method_coverage = _pct(tested_methods, total_methods)
    return {
        "method_coverage_pct": round(method_coverage, 1),
        "total_methods": total_methods,
        "tested_methods": tested_methods,
    }
def _import_coverage_metrics(cache, test_files) -> dict:
    total_internal_imports = 0
    tested_imports = 0
    internal_roots = _internal_package_roots(cache)
    for entry in _iter_production_entries(cache):
        for imp in entry.imports:
            _target = imp_internal_target(
                imp, cache.internal_mods, internal_roots)
            if _target:
                total_internal_imports += 1
                if _has_named_test_module(_target, test_files):
                    tested_imports += 1
    import_coverage = _pct(tested_imports, total_internal_imports)
    return {"import_coverage_pct": round(import_coverage, 1)}
def _collect_test_trees(cache, test_files) -> list:
    django_tests = _django_test_basenames_for_root(
        getattr(cache, 'skill_dir', ''))
    _test_trees = [te.tree for te in cache.entries
                   if te.tree is not None
                   and te.mod_stem in test_files
                   and _is_collectable_test_entry(te, django_tests)]
    _test_trees.extend(_entry.tree for _entry in cache.test_dir_entries
                       if _entry.tree is not None
                       and _is_collectable_test_entry(_entry, django_tests))
    return _test_trees
def _django_test_parent_dirs(cache) -> frozenset[str]:
    django_tests = _django_test_basenames_for_root(
        getattr(cache, 'skill_dir', ''))
    if not django_tests:
        return frozenset()
    parents: set[str] = set()
    for entries in (cache.entries, cache.test_dir_entries):
        for entry in entries:
            if os.path.basename(entry.path).lower() in django_tests:
                parents.add(os.path.normcase(os.path.dirname(entry.rel_path)))
    return frozenset(parents)
def _exception_coverage_metrics(cache, test_trees) -> dict:
    total_except_handlers = 0
    tested_except_handlers = 0
    tested_except_types = _collect_tested_exception_types(test_trees)
    for entry in _iter_production_entries(cache):
        for node in nodes_where(entry, (ast.ExceptHandler,)):
            total_except_handlers += 1
            if node.type and tested_except_types.intersection(
                    _extract_except_type_names(node.type)):
                tested_except_handlers += 1
    exception_coverage = _pct(tested_except_handlers, total_except_handlers)
    return {
        "total_except_handlers": total_except_handlers,
        "tested_except_handlers": tested_except_handlers,
        "tested_exception_types": len(tested_except_types),
        "exception_coverage_pct": round(exception_coverage, 1),
    }
def _decorator_coverage_metrics(cache, tested_function_names) -> dict:
    total_decorated = 0
    tested_decorated = 0
    for entry in _iter_production_entries(cache):
        for func in entry.functions:
            if func.get('decorators'):
                total_decorated += 1
                if func['name'] in tested_function_names:
                    tested_decorated += 1
    decorator_coverage = _pct(tested_decorated, total_decorated)
    return {
        "decorated_functions": total_decorated,
        "tested_decorated": tested_decorated,
        "decorator_coverage_pct": round(decorator_coverage, 1),
    }
def _test_quality_score(scan: _CoverageScan, test_trees: list) -> float:
    if scan.total_functions <= 0:
        return 0.0
    overall = _coverage_rates(scan).overall
    assertion, independence = _test_suite_quality_components(test_trees)
    score = (min(overall / 100, 1.0) * 0.5
             + assertion * 0.3 + independence * 0.2) * 100
    return round(score, 1)
_MAX_PRIORITY_RECOMMENDATIONS = 5
def _compute_extended_coverage(cache, test_files, tested_function_names,
                               scan: _CoverageScan) -> dict:
    metrics = {}
    metrics.update(_method_coverage_metrics(cache, tested_function_names))
    metrics.update(_import_coverage_metrics(cache, test_files))
    metrics['priority_recommendations'] = [
        {"file": f["file"], "function": f["function"],
         "line": f["line"], "severity": f["severity"]}
        for f in scan.untested_critical[:_MAX_PRIORITY_RECOMMENDATIONS]
    ]
    test_trees = _collect_test_trees(cache, test_files)
    metrics.update(_exception_coverage_metrics(cache, test_trees))
    metrics.update(_decorator_coverage_metrics(cache, tested_function_names))
    metrics['test_quality_score'] = _test_quality_score(scan, test_trees)
    _ranked = sorted(
        (m for m in scan.module_coverage if m.get('functions', 0) > 0),
        key=lambda m: (m.get('tested_functions', 0) / m['functions'],
                       -m.get('functions', 0)))
    metrics['worst_covered_module'] = _ranked[0]['file'] if _ranked else None
    metrics['best_covered_module'] = _ranked[-1]['file'] if _ranked else None
    return metrics
def _collect_called_names(nodes, names_out: set) -> None:
    for node in nodes:
        if not isinstance(node, ast.Call):
            continue
        _called = _coverage_callee_name(node)
        if _called is not None:
            names_out.add(_called)
def _collect_tested_functions(cache) -> tuple:
    test_files: set[str] = set()
    tested_function_names: set[str] = set()
    django_tests = _django_test_basenames_for_root(
        getattr(cache, 'skill_dir', ''))
    for entry in cache.entries:
        if not _is_collectable_test_entry(entry, django_tests):
            continue
        test_files.add(entry.mod_stem)
        if entry.tree is not None:
            _collect_called_names(entry_nodes(entry), tested_function_names)
    for entry in cache.test_dir_entries:
        if not _is_collectable_test_entry(entry, django_tests):
            continue
        test_files.add(entry.mod_stem)
        if entry.tree is not None:
            _collect_called_names(entry_nodes(entry), tested_function_names)
    return test_files, tested_function_names
def _build_internal_call_graph(cache) -> dict:
    _internal_call_graph = {}
    for entry in _iter_production_entries(cache):
        for node in nodes_where(entry, (ast.FunctionDef, ast.AsyncFunctionDef)):
            called = {_c for _c in (_coverage_callee_name(child)
                                    for child in iter_own_scope_nodes(node))
                      if _c is not None}
            _internal_call_graph.setdefault(node.name, set()).update(called)
    return _internal_call_graph
def _expand_tested_transitive_closure(cache, tested_function_names: set) -> set:
    _internal_call_graph = _build_internal_call_graph(cache)
    _expanded = set(tested_function_names)
    _queue = list(_expanded)
    _cursor = 0
    while _cursor < len(_queue):
        _fn = _queue[_cursor]
        _cursor += 1
        for _callee in _internal_call_graph.get(_fn, set()):
            if _callee not in _expanded and _callee in _internal_call_graph:
                _expanded.add(_callee)
                _queue.append(_callee)
    return _expanded
_BRANCH_WEIGHT_T = {
    ast.If: 2, ast.IfExp: 2, ast.For: 2, ast.AsyncFor: 2, ast.While: 2,
    ast.ExceptHandler: 1,
}
_STMT_T = frozenset((ast.Assign, ast.AugAssign, ast.AnnAssign, ast.Expr,
                     ast.Return, ast.Raise, ast.Delete))
def _branch_increment(child) -> int:
    _t = child.__class__
    _weight = _BRANCH_WEIGHT_T.get(_t)
    if _weight is not None:
        return _weight
    if _t is ast.Match:
        return len(child.cases)
    if _t is ast.BoolOp:
        return len(child.values) - 1
    if _t is ast.comprehension:
        return 2 * (1 + len(child.ifs))
    return 0
def _count_branches_and_statements(node) -> tuple:
    branches = 0
    statements = 0
    for child in iter_own_scope_nodes(node):
        branches += _branch_increment(child)
        if child.__class__ in _STMT_T:
            statements += 1
    return branches, statements
def _qualname_join(prefix: str, name: str) -> str:
    return f"{prefix}.{name}" if prefix else name
def _collect_qualnames(tree) -> dict:
    qualnames: dict[int, str] = {}
    def _rec(parent, prefix):
        for child in ast.iter_child_nodes(parent):
            if isinstance(child, ast.expr):
                continue
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                qn = _qualname_join(prefix, child.name)
                qualnames[id(child)] = qn
                _rec(child, qn)
            elif isinstance(child, ast.ClassDef):
                _rec(child, _qualname_join(prefix, child.name))
            else:
                _rec(child, prefix)
    _rec(tree, "")
    return qualnames
@dataclass
class _CoverageRates:
    function_pct: float
    branch_pct: float
    statement_pct: float
    overall: float
@dataclass
class _CoverageScan:
    total_functions: int
    tested_functions: int
    total_branches: int
    covered_branches: int
    total_statements: int
    covered_statements: int
    untested_critical: list
    module_coverage: list
    func_coverage_map: dict
@dataclass
class _FunctionScan:
    is_tested: bool
    branches: int
    statements: int
    coverage_entry: dict
    critical: dict | None
@dataclass
class _ModuleScan:
    rel_path: str
    mod_stem: str
    functions: int
    tested_functions: int
    branches: int
    statements: int
    covered_branches: int
    covered_statements: int
    has_tests: bool
    untested_critical: list[dict]
    coverage_entries: dict[str, dict]
def _coverage_entry(node, rel_path: str, is_tested: bool) -> dict:
    return {
        "name": node.name, "file": rel_path, "line": node.lineno,
        "executed_count": 1 if is_tested else 0,
    }
def _critical_function_finding(node, rel_path: str) -> dict | None:
    if node.name.startswith('_'):
        return None
    _end = getattr(node, 'end_lineno', None) or node.lineno
    func_len = _end - node.lineno + 1
    if func_len < _CRITICAL_MIN_LINES:
        return None
    return {
        "file": rel_path, "function": node.name,
        "rule_id": "TC-01",
        "line": node.lineno, "lines": func_len,
        "severity": ("high" if func_len > _CRITICAL_HIGH_LINES
                     else "medium"),
        "message": f"关键函数 {node.name} ({func_len} 行) 无测试覆盖",
    }
def _scan_single_function(node, rel_path: str,
                          tested_function_names: set) -> _FunctionScan:
    is_tested = node.name in tested_function_names
    critical = None if is_tested else _critical_function_finding(node, rel_path)
    branches, statements = _count_branches_and_statements(node)
    return _FunctionScan(
        is_tested=is_tested, branches=branches, statements=statements,
        coverage_entry=_coverage_entry(node, rel_path, is_tested),
        critical=critical,
    )
def _scan_module_entry(entry, test_files: set,
                      tested_function_names: set,
                      django_test_dirs: frozenset[str]) -> _ModuleScan:
    rel_path = entry.rel_path
    mod_stem = entry.mod_stem
    qualnames = _collect_qualnames(entry.tree)
    functions = 0
    tested = 0
    branches = 0
    statements = 0
    covered_branches = 0
    covered_statements = 0
    criticals: list[dict] = []
    coverage_entries: dict[str, dict] = {}
    for node in nodes_where(entry, (ast.FunctionDef, ast.AsyncFunctionDef)):
        scan = _scan_single_function(
            node, rel_path, tested_function_names)
        qualname = qualnames.get(id(node), node.name)
        coverage_entries[f"{rel_path}:{qualname}"] = scan.coverage_entry
        functions += 1
        if scan.is_tested:
            tested += 1
            covered_branches += scan.branches
            covered_statements += scan.statements
        elif scan.critical:
            criticals.append(scan.critical)
        branches += scan.branches
        statements += scan.statements
    covered_branches = round(
        covered_branches * _FUNCTION_APPROX_BRANCH_RATIO)
    covered_statements = round(
        covered_statements * _FUNCTION_APPROX_STATEMENT_RATIO)
    return _ModuleScan(
        rel_path=rel_path, mod_stem=mod_stem, functions=functions,
        tested_functions=tested, branches=branches, statements=statements,
        covered_branches=covered_branches,
        covered_statements=covered_statements,
        has_tests=(
            _has_named_test_module(mod_stem, test_files)
            or os.path.normcase(os.path.dirname(rel_path)) in django_test_dirs
        ),
        untested_critical=criticals, coverage_entries=coverage_entries,
    )
def _scan_module_coverage(cache, test_files: set,
                          tested_function_names: set) -> _CoverageScan:
    total_functions = 0
    tested_functions = 0
    total_branches = 0
    covered_branches = 0
    total_statements = 0
    covered_statements = 0
    untested_critical: list[dict] = []
    module_coverage: list[dict] = []
    func_coverage_map: dict = {}
    django_test_dirs = _django_test_parent_dirs(cache)
    for entry in _iter_production_entries(cache):
        module = _scan_module_entry(
            entry, test_files, tested_function_names, django_test_dirs)
        total_functions += module.functions
        tested_functions += module.tested_functions
        total_branches += module.branches
        total_statements += module.statements
        covered_branches += module.covered_branches
        covered_statements += module.covered_statements
        untested_critical.extend(module.untested_critical)
        func_coverage_map.update(module.coverage_entries)
        module_coverage.append({
            "file": module.rel_path,
            "has_tests": module.has_tests,
            "functions": module.functions,
            "tested_functions": module.tested_functions,
            "branches": module.branches,
            "statements": module.statements,
        })
    return _CoverageScan(
        total_functions=total_functions, tested_functions=tested_functions,
        total_branches=total_branches, covered_branches=covered_branches,
        total_statements=total_statements, covered_statements=covered_statements,
        untested_critical=untested_critical, module_coverage=module_coverage,
        func_coverage_map=func_coverage_map,
    )
_COVERAGE_PASS_MIN_PCT = 80.0
_COVERAGE_METHOD_NAME = "覆盖率度量(AST静态估算)"
_COVERAGE_METHOD_ID = "coverage"
_CRITICAL_PENALTY_PER_FINDING = 3
_MAX_CRITICAL_PENALTY = 60
_MIN_WARN_SCORE = 30
_CRITICAL_MIN_LINES = 20
_CRITICAL_HIGH_LINES = 50
def run_coverage_analysis(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        logger.warning(
            "[Coverage] 覆盖率度量中止: 度量目录无效 %r", skill_dir)
        return TestMethodResult.invalid_input(
            skill_dir, _COVERAGE_METHOD_NAME, _COVERAGE_METHOD_ID,
            "度量", start)
    result = TestMethodResult(
        method_name=_COVERAGE_METHOD_NAME,
        method_id=_COVERAGE_METHOD_ID,
    )
    test_files, tested_function_names = _collect_tested_functions(cache)
    tested_function_names = _expand_tested_transitive_closure(
        cache, tested_function_names)
    scan = _scan_module_coverage(cache, test_files, tested_function_names)
    rates = _coverage_rates(scan)
    result.metrics = _build_coverage_metrics(scan, rates)
    result.metrics.update(_compute_extended_coverage(
        cache, test_files, tested_function_names, scan))
    result.findings.extend(scan.untested_critical[:20])
    _apply_coverage_verdict(result, rates, scan.untested_critical, scan)
    return result.finish(start, precision=1)
def _coverage_rates(scan: _CoverageScan) -> _CoverageRates:
    function_pct = _pct(scan.tested_functions, scan.total_functions)
    branch_pct = _pct(scan.covered_branches, scan.total_branches)
    statement_pct = _pct(scan.covered_statements, scan.total_statements)
    _dims = ((function_pct, 0.4, scan.total_functions),
             (branch_pct, 0.35, scan.total_branches),
             (statement_pct, 0.25, scan.total_statements))
    _weight = sum(w for _, w, denom in _dims if denom > 0)
    overall = (sum(pct * w for pct, w, denom in _dims if denom > 0)
               / _weight) if _weight > 0 else 0.0
    return _CoverageRates(
        function_pct=function_pct, branch_pct=branch_pct,
        statement_pct=statement_pct, overall=overall)
def _pct(numerator: int, denominator: int) -> float:
    return numerator / denominator * 100 if denominator > 0 else 100.0
def _build_coverage_metrics(scan: _CoverageScan, rates: _CoverageRates) -> dict:
    if scan.total_functions <= 0:
        function_pct = branch_pct = statement_pct = 0.0
    else:
        function_pct = round(rates.function_pct, 1)
        branch_pct = round(rates.branch_pct, 1)
        statement_pct = round(rates.statement_pct, 1)
    return {
        "total_functions": scan.total_functions,
        "tested_functions": scan.tested_functions,
        "function_coverage_pct": function_pct,
        "total_branches": scan.total_branches,
        "covered_branches": scan.covered_branches,
        "branch_coverage_pct": branch_pct,
        "total_statements": scan.total_statements,
        "covered_statements": scan.covered_statements,
        "statement_coverage_pct": statement_pct,
        "overall_coverage_pct": round(rates.overall, 1),
        "modules_with_tests": sum(1 for m in scan.module_coverage if m["has_tests"]),
        "modules_without_tests": sum(1 for m in scan.module_coverage if not m["has_tests"]),
        "untested_critical_functions": len(scan.untested_critical),
        "func_coverage": scan.func_coverage_map,
    }
def _apply_coverage_verdict(result: TestMethodResult, rates: _CoverageRates,
                            untested_critical: list[dict],
                            scan: _CoverageScan) -> None:
    _summary = (f"覆盖率 {round(rates.overall, 1)}% "
                f"(函数 {round(rates.function_pct, 1)}% / "
                f"分支 {round(rates.branch_pct, 1)}% / "
                f"语句 {round(rates.statement_pct, 1)}%)")
    if scan.total_functions <= 0:
        result.status = "skip"
        result.score = 0
        result.summary = "未发现可度量的生产函数（无覆盖率证据）"
        return
    if scan.tested_functions == 0:
        result.status = "warn"
        result.score = _MIN_WARN_SCORE
        result.summary = (f"{_summary}，无任何测试覆盖证据（静态口径），"
                          f"须补充测试")
        if untested_critical:
            result.summary += f"；发现 {len(untested_critical)} 个未测试关键函数"
        return
    if not untested_critical:
        if rates.overall >= _COVERAGE_PASS_MIN_PCT:
            result.status = "pass"
            result.score = 100
            result.summary = _summary
            return
        result.status = "warn"
        result.score = max(_MIN_WARN_SCORE, int(rates.overall))
        result.summary = (f"{_summary}, 低于及格线 "
                          f"{_COVERAGE_PASS_MIN_PCT:.0f}%，须补充测试")
        return
    result.status = "warn"
    _penalty = min(_MAX_CRITICAL_PENALTY,
                   len(untested_critical) * _CRITICAL_PENALTY_PER_FINDING)
    result.score = max(_MIN_WARN_SCORE, int(rates.overall) - _penalty)
    result.summary = (f"{_summary}, "
                      f"发现 {len(untested_critical)} 个未测试关键函数"
                      f"（扣 {_penalty} 分）")
DEFAULT_COVERAGE_THRESHOLD = 95.0
_PERCENT_MAX = 100.0
_DEFAULT_GAP_CONTEXT_LINES = 3
def step_ok(data: dict, message: str) -> dict:
    return {"ok": True, "status": "ok", "data": data, "message": message}
def step_err(message: str, data: dict | None = None) -> dict:
    return {"ok": False, "status": "error", "data": data or {}, "message": message}
def step_skip(message: str, data: dict | None = None) -> dict:
    return {"ok": True, "status": "skipped", "data": data or {},
            "message": message}
def _norm_files(report: dict) -> dict:
    files = report.get("files", {}) if isinstance(report, dict) else {}
    return files if isinstance(files, dict) else {}
def _norm_summary(info: dict) -> dict:
    s = info.get("summary", {})
    return s if isinstance(s, dict) else {}
def _has_absolute_file_keys(files: dict) -> bool:
    return any(isinstance(key, str) and os.path.isabs(key)
               for key in files)
def _root_shape_ok(project_root: str | Path | None) -> bool:
    if project_root is None:
        return True
    if isinstance(project_root, (str, os.PathLike)):
        return True
    logger.warning("[coverage] project_root 形态非法（%r），按无根处理",
                 project_root)
    return False
def _abs_key_to_rel(path: str, project_root: str | Path) -> str | None:
    try:
        return os.path.relpath(path, project_root)
    except ValueError:
        logger.debug("[coverage] 报告路径键归一失败（跳过）: %s", path)
        return None
def _rel_key(path: str, project_root: str | Path | None) -> str | None:
    if not isinstance(path, str):
        logger.warning("[coverage] 报告路径键形态非法（%r），跳过该条目", path)
        return None
    if not _root_shape_ok(project_root):
        project_root = None
    rel = path
    if project_root:
        if os.path.isabs(path):
            rel = _abs_key_to_rel(path, project_root)
            if rel is None:
                return None
        else:
            rel = _rel_key_2src_restore(path, project_root) or path
    return os.path.normpath(rel).replace("\\", "/")
def _path_hits(base: str, rel: str) -> bool:
    try:
        return os.path.isfile(os.path.join(base, rel))
    except (OSError, ValueError) as _e:
        logger.debug("[coverage] 相对键探测失败（按不存在处理）: %s: %s",
                   rel, _e)
        return False
def _rel_key_2src_restore(path: str, project_root: str | Path) -> str | None:
    try:
        _abs_cand = os.path.abspath(path)
        _abs_root = os.path.abspath(project_root)
    except (OSError, ValueError) as _e:
        logger.debug("[coverage] 相对键②源还原路径归一失败（维持键原样）: %s", _e)
        return None
    if os.path.normcase(_abs_cand) == os.path.normcase(_abs_root):
        return None
    if (is_outside_root(path)
            or (not _path_hits(_abs_root, path)
                and _path_hits(os.getcwd(), path))):
        return _abs_key_to_rel(_abs_cand, _abs_root)
    return os.path.normpath(path)
def _normalize_project_root(project_root: str | Path | None) -> str | None:
    if not _root_shape_ok(project_root):
        return None
    if not project_root:
        return None
    try:
        return str(Path(project_root).resolve())
    except (OSError, ValueError, RuntimeError) as exc:
        logger.warning("[coverage] project_root 归一失败（%r），按无根处理: %s",
                       project_root, exc)
        return None
def _is_root_module(rel: str, django_tests=_NO_DJANGO_TEST_BASENAMES) -> bool:
    return "/" not in rel and _is_source_module(rel, django_tests)
def _is_test_module(rel: str, django_tests=_NO_DJANGO_TEST_BASENAMES) -> bool:
    if not rel.lower().endswith(".py"):
        return False
    parts = rel.split("/")
    if parts[-1].lower() in django_tests:
        return True
    if any(part.lower() in _TEST_DIR_NAMES for part in parts[:-1]):
        return True
    return is_test_source_basename(parts[-1])
_EXTRA_SKIP_DOT_DIRS = frozenset({
    ".hg", ".svn", ".tox", ".eggs", ".mypy_cache", ".ruff_cache",
    ".idea", ".vscode",
})
_SKIP_DIRS = frozenset(SCAN_IGNORE_DIRS) | _EXTRA_SKIP_DOT_DIRS
SKIP_DIRS_LOWER = frozenset(s.lower() for s in _SKIP_DIRS)
def _is_source_module(rel: str, django_tests=_NO_DJANGO_TEST_BASENAMES) -> bool:
    if not rel.lower().endswith(".py") or is_outside_root(rel):
        return False
    parts = rel.split("/")
    if any(part.lower() in SKIP_DIRS_LOWER
           or part.lower() in _TEST_DIR_NAMES for part in parts[:-1]):
        return False
    name = parts[-1]
    return (name.lower() not in django_tests
            and name.lower() != "conftest.py"
            and not is_test_source_basename(name))
_SCOPES = ("root", "source", "all")
def _normalize_scope(scope: str, channel: str = "") -> str:
    if scope in _SCOPES:
        return scope
    logger.warning("[coverage] %sscope 形态非法（%r），回退默认 root",
                 f"{channel} " if channel else "", scope)
    return "root"
_DEFAULT_SCOPE = "root"
def _in_scope(rel: str, scope: str = _DEFAULT_SCOPE,
              django_tests=_NO_DJANGO_TEST_BASENAMES) -> bool:
    if is_outside_root(rel):
        return False
    if scope == "all":
        return True
    if scope == "source":
        return _is_source_module(rel, django_tests)
    return _is_root_module(rel, django_tests)
_HISTORY_VARIANCE_SPREAD_PCT = 3.0
def _history_percent(entry) -> float | None:
    if not isinstance(entry, dict):
        return None
    raw_report = entry.get("raw_report")
    if not isinstance(raw_report, dict):
        return None
    totals = raw_report.get("totals")
    if not isinstance(totals, dict):
        return None
    p = totals.get("percent_covered")
    if not is_finite_num(p) or not 0 <= p <= _PERCENT_MAX:
        return None
    if as_number(totals.get("num_statements"), 0) <= 0:
        return None
    return round(float(p), 2)
def _collect_history_percents(coord_dir) -> list[float]:
    percents: list[float] = []
    for fp in sorted(Path(coord_dir).glob("*.json")):
        entry, kind, error = read_json_artifact(str(fp))
        if kind != "ok":
            logger.debug(
                "[coverage] 历史报告读取降级（%s）: %s", kind, error)
            continue
        pct = _history_percent(entry)
        if pct is not None:
            percents.append(pct)
    return percents
def _variance_alert(lo: float, hi: float, cur: float, spread: float) -> str:
    return (
        f"同项目历史扫描轮次总体覆盖率方差过大（历史 {lo:.2f}%~"
        f"{hi:.2f}%，本次 {cur:.2f}%，跨度 {spread:.2f} 个百分点，"
        f"阈值 {_HISTORY_VARIANCE_SPREAD_PCT:g}）——多会话并行扫描或 "
        "worker 内采集竞态（CTracer/sys.monitoring）会造成系统性"
        "低估，本报告数字采信前建议对关键模块以 -n0 串行单文件"
        "口径交叉验证")
def history_variance_warning(coord_ctx: dict | None,
                              current_percent: float) -> str | None:
    if not coord_ctx:
        return None
    coord_dir = coord_ctx.get("coord_dir")
    if not coord_dir:
        return None
    try:
        percents = _collect_history_percents(coord_dir)
        if not percents:
            return None
        if not is_finite_num(current_percent):
            return None
        cur = round(float(current_percent), 2)
        lo, hi = min(percents), max(percents)
        spread = max(hi, cur) - min(lo, cur)
        if spread > _HISTORY_VARIANCE_SPREAD_PCT:
            return _variance_alert(lo, hi, cur, spread)
    except Exception:
        logger.debug("[coverage] 历史方差检测降级", exc_info=True)
    return None
def _owner_spans_from_text(text: str) -> list | None:
    try:
        tree = ast.parse(text)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as _oe:
        logger.debug("[coverage] 归属解析降级（语法坏/超深/超大）: %s", _oe)
        return None
    spans = [
        (node.lineno, node.end_lineno, node.name)
        for node in walk_nodes(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef))]
    spans.sort(key=lambda t: (t[1] - t[0]))
    return spans
def _read_gap_source_text(src_path) -> str | None:
    try:
        return read_source_text_strict(os.fspath(src_path))
    except (OSError, ValueError, SyntaxError) as _oe:
        logger.debug("[coverage] gap 源码读取降级（不可读/编码声明坏）: %s", _oe)
        return None
def _normalize_export_options(context_lines, modules) -> tuple:
    ctx = norm_nonneg_int(context_lines, _DEFAULT_GAP_CONTEXT_LINES,
                           "context_lines")
    if modules is not None and not isinstance(modules, (list, tuple, set)):
        logger.warning("[coverage] modules 形态非法（%r），回退不过滤",
                     modules)
        mods = None
    else:
        mods = modules
    return ctx, mods
def _load_gap_report(report_path) -> tuple[Path | None, dict | None, dict | None]:
    if not isinstance(report_path, (str, os.PathLike)):
        logger.warning("[coverage] report_path 形态非法（%r），拒绝导出",
                     report_path)
        return None, None, step_err(
            f"报告路径形态非法: {type(report_path).__name__}")
    rp = Path(report_path)
    if not rp.is_file():
        return rp, None, step_err(f"报告不存在: {rp}")
    report, kind, error = read_json_artifact(str(rp))
    if kind != "ok":
        detail = error or kind
        logger.warning("[coverage] gap 报告解析失败: %s", detail)
        return rp, None, step_err(f"报告解析失败: {detail}")
    if not isinstance(report, dict):
        logger.warning("[coverage] gap 报告顶层非映射（%s），拒绝导出",
                       type(report).__name__)
        return rp, None, step_err(
            f"报告顶层非映射: {type(report).__name__}")
    return rp, report, None
def _write_gap_markdown(out: Path, lines_out: list[str]) -> str:
    try:
        out.parent.mkdir(parents=True, exist_ok=True)
        atomic_write_text(
            str(out), "\n".join(lines_out) + "\n", tag="coverage-gap")
        return ""
    except (OSError, ValueError) as exc:
        logger.warning("[coverage] gap 上下文导出写盘失败: %s", exc, exc_info=True)
        return str(exc)
def export_gap_context(report_path: str | Path, out_path: str | Path,
                       project_root: str | Path | None = None,
                       context_lines: int = _DEFAULT_GAP_CONTEXT_LINES,
                       modules: list[str] | None = None,
                       scope: str = _DEFAULT_SCOPE) -> dict:
    context_lines, modules = _normalize_export_options(context_lines,
                                                        modules)
    scope = _normalize_scope(scope, "export")
    if not isinstance(out_path, (str, os.PathLike)):
        logger.warning("[coverage] out_path 形态非法（%r），拒绝导出",
                     out_path)
        return step_err(f"输出路径形态非法: {type(out_path).__name__}")
    rp, report, failure = _load_gap_report(report_path)
    if failure is not None:
        return failure
    out = Path(out_path)
    if (os.path.normcase(os.path.realpath(rp))
            == os.path.normcase(os.path.realpath(out))):
        return step_err(f"输出路径不能与输入报告相同: {out}")
    root_str = _normalize_project_root(project_root)
    root = Path(root_str) if root_str else None
    files = _norm_files(report)
    if root is None and _has_absolute_file_keys(files):
        return step_err(
            "报告文件键为绝对路径，需提供 project_root 才能归一到项目根"
            "口径（否则缺口会被全部过滤，导出空文档）")
    items = _collect_gap_items(files, root, modules, scope)
    lines_out = _render_gap_markdown(items, root, rp.name, context_lines)
    write_error = _write_gap_markdown(out, lines_out)
    if write_error:
        return step_err(f"缺口上下文写盘失败: {write_error}")
    return step_ok({"modules": len(items),
                    "gap_lines": sum(len(m) for _, _, _, m in items),
                    "out_path": str(out)},
                   f"缺口上下文已导出: {out}")
def _collect_gap_items(files: dict, root: Path | None, modules,
                       scope: str = _DEFAULT_SCOPE) -> list[tuple]:
    items = []
    django_tests = _django_test_basenames_for_root(root)
    for path, info in files.items():
        item = _gap_candidate(path, info, root, modules, scope, django_tests)
        if item is not None:
            items.append(item)
    items.sort(key=lambda t: (t[1], -len(t[3])))
    return items
def _in_gap_scope(rel: str, modules, scope: str = _DEFAULT_SCOPE,
                  django_tests=_NO_DJANGO_TEST_BASENAMES) -> bool:
    if not _in_scope(rel, scope, django_tests):
        return False
    if not modules:
        return True
    return any(
        isinstance(module, str)
        and os.path.normpath(module).replace("\\", "/") == rel
        for module in modules
    )
def _gap_candidate(path: str, info: object, root: Path | None,
                   modules, scope: str = _DEFAULT_SCOPE,
                   django_tests=_NO_DJANGO_TEST_BASENAMES) -> tuple | None:
    if not isinstance(info, dict):
        return None
    rel = _rel_key(path, str(root) if root is not None else None)
    if rel is None or not _in_gap_scope(
            rel, modules, scope, django_tests):
        return None
    missing = _norm_missing_lines(info.get("missing_lines"))
    if not missing:
        return None
    s = _norm_summary(info)
    return (rel, as_number(s.get("percent_covered")),
            as_number(s.get("num_statements"), 0), missing)
def _norm_missing_lines(missing) -> list[int]:
    if not isinstance(missing, list) or not missing:
        return []
    return sorted({ln for ln in missing
                   if isinstance(ln, int) and not isinstance(ln, bool)
                   and ln > 0})
def _render_gap_markdown(items: list[tuple], root: Path | None,
                         rp_name: str, context_lines: int) -> list[str]:
    lines_out: list[str] = [
        "# 覆盖率缺口上下文", "",
        f"- 报告: `{rp_name}`", f"- 缺口模块: {len(items)}",
        f"- 缺口行总数: {sum(len(m) for _, _, _, m in items)}", "",
    ]
    for item in items:
        lines_out.extend(_render_module_gap_section(
            item, root, context_lines))
    return lines_out
def _merge_gap_blocks(missing: list[int]) -> list[list[int]]:
    blocks: list[list[int]] = []
    for ln in missing:
        if blocks and ln == blocks[-1][-1] + 1:
            blocks[-1].append(ln)
        else:
            blocks.append([ln])
    return blocks
def _load_gap_source(src: Path | None) -> tuple[list | None, list[str]]:
    if src is None:
        return None, []
    try:
        if not src.is_file():
            return None, []
        text = _read_gap_source_text(src)
        if text is None:
            return None, []
        return _owner_spans_from_text(text), text.splitlines()
    except (OSError, ValueError, RecursionError, MemoryError) as _e:
        logger.debug("[coverage] gap 源码解析降级（不渲染上下文）: %s", _e)
        return None, []
def _render_gap_block(block: list[int], spans: list | None,
                      src_lines: list[str], miss_set: set[int],
                      context_lines: int) -> list[str]:
    lo, hi = block[0], block[-1]
    owner = "<module>"
    if spans:
        owner = next((name for (a, b, name) in spans
                      if a <= lo <= b), "<module>")
    ctx_lo = max(1, lo - context_lines)
    ctx_hi = min(len(src_lines), hi + context_lines) if src_lines else hi
    return [
        f"--- lines {lo}-{hi}  [{owner}]",
        *(f"{'X' if ln in miss_set else ' '}{ln:5d} | "
          f"{src_lines[ln - 1] if ln <= len(src_lines) else ''}"
          for ln in range(ctx_lo, ctx_hi + 1)),
    ]
def _render_module_gap_section(item: tuple, root: Path | None,
                               context_lines: int) -> list[str]:
    rel, pct, stmts, missing = item
    out: list[str] = [f"===== {rel}  percent={pct:.2f}%  miss={len(missing)}/{stmts}"]
    src = root / rel if root else None
    spans, src_lines = _load_gap_source(src)
    miss_set = set(missing)
    for block in _merge_gap_blocks(missing):
        out.extend(_render_gap_block(block, spans, src_lines, miss_set,
                                     context_lines))
    out.append("")
    return out
def _normalize_threshold(threshold: float) -> float:
    if (not is_finite_num(threshold)
            or not 0 <= threshold <= _PERCENT_MAX):
        logger.warning("[coverage] threshold 形态非法（%r），回退默认 %s",
                     threshold, DEFAULT_COVERAGE_THRESHOLD)
        return DEFAULT_COVERAGE_THRESHOLD
    return threshold
def _iter_report_rows(report: dict, project_root: str | None):
    for path, info in _norm_files(report).items():
        if not isinstance(info, dict):
            continue
        rel = _rel_key(path, project_root)
        if rel is None:
            continue
        yield rel, _norm_summary(info)
def _missing_line_count(summary: dict) -> int:
    raw = summary.get("missing_lines")
    if isinstance(raw, (list, tuple, set, frozenset)):
        return len(raw)
    if is_finite_num(raw):
        return max(0, int(raw))
    statements = as_number(summary.get("num_statements"), 0.0)
    covered = as_number(summary.get("covered_lines"), 0.0)
    return max(0, int(statements - covered))
def _collect_summary_rows(report: dict, scope: str,
                          project_root: str | None) -> list[dict]:
    rows = []
    django_tests = _django_test_basenames_for_root(project_root)
    for rel, s in _iter_report_rows(report, project_root):
        if not _in_scope(rel, scope, django_tests):
            continue
        rows.append({
            "module": rel,
            "percent": as_number(s.get("percent_covered")),
            "percent_statements": as_number(
                s.get("percent_statements_covered")),
            "statements": as_number(s.get("num_statements"), 0),
            "missing": _missing_line_count(s),
            "_covered_lines": as_number(s.get("covered_lines"), 0),
            "_branches": as_number(s.get("num_branches"), 0),
            "_covered_branches": as_number(s.get("covered_branches"), 0),
        })
    rows.sort(key=lambda r: (r["percent"], -r["missing"]))
    return rows
def _scoped_summary_totals(rows: list[dict]) -> dict:
    statements = sum(row["statements"] for row in rows)
    covered_lines = sum(row["_covered_lines"] for row in rows)
    branches = sum(row["_branches"] for row in rows)
    covered_branches = sum(row["_covered_branches"] for row in rows)
    denominator = statements + branches
    percent = ((covered_lines + covered_branches) / denominator * 100
               if denominator > 0 else 0.0)
    return {
        "percent": round(percent, 2),
        "statements": statements,
        "covered_lines": covered_lines,
        "branches": branches,
    }
_DEFAULT_DROP_PP = 1.0
def _normalize_drop_pp(drop_pp: float) -> float:
    if is_finite_num(drop_pp):
        return max(0.0, drop_pp)
    logger.warning("[coverage] drop_pp 形态非法（%r），回退默认 %s",
                 drop_pp, _DEFAULT_DROP_PP)
    return _DEFAULT_DROP_PP
def _compose_gap_export(data: dict, gaps_out: str, project_dir: str) -> None:
    try:
        data["gaps_export"] = export_gap_context(
            data["json_path"], gaps_out,
            project_root=project_dir, scope="source")
    except Exception as exc:
        logger.warning("[coverage-scan] 缺口上下文导出失败（不阻断主结果）: %s",
                     exc, exc_info=True)
        data["gaps_export"] = step_err(f"缺口上下文导出失败: {exc}")
def _compose_baseline_diff(data: dict, diff_against: str,
                          project_dir: str) -> None:
    try:
        prev, prev_kind, prev_err = read_json_artifact(diff_against)
        cur, cur_kind, cur_err = read_json_artifact(str(data["json_path"]))
        if prev_kind != "ok" or cur_kind != "ok":
            details = []
            if prev_kind != "ok":
                details.append(f"基线读取失败: {prev_err or prev_kind}")
            if cur_kind != "ok":
                details.append(f"当前报告读取失败: {cur_err or cur_kind}")
            raise ValueError("；".join(details))
        diff = diff_scan_reports(
            cur, prev, project_root=project_dir, scope="source")
        data["diff"] = {"ok": True, **diff}
        for alert in diff["alerts"]:
            print(f"[coverage-scan] 告警: {alert}", flush=True)
        print(f"[coverage-scan] diff: 回归 {len(diff['regressed'])} / "
              f"改善 {len(diff['improved'])} / 新增 {len(diff.get('added', []))}"
              f" / 移除 {len(diff.get('removed', []))}"
              f" / 告警 {len(diff['alerts'])}", flush=True)
    except Exception as exc:  # noqa: BLE001
        logger.warning("[coverage-scan] 基线对比失败（不阻断主结果）: %s", exc)
        data["diff"] = {"ok": False, "message": f"对比失败: {exc}"}
def apply_coverage_extras(data: dict, *, gaps_out: str | None = None,
                          diff_against: str | None = None,
                          project_dir: str = "") -> None:
    if gaps_out:
        _compose_gap_export(data, gaps_out, project_dir)
    if diff_against:
        _compose_baseline_diff(data, diff_against, project_dir)
def write_coverage_payload(json_out: str, payload: str) -> None:
    try:
        out_json = Path(json_out)
        out_json.parent.mkdir(parents=True, exist_ok=True)
        atomic_write_text(str(out_json), payload, tag="coverage")
        print(f"结果已写入 {json_out}")
    except (OSError, ValueError) as exc:
        logger.warning("[coverage-scan] --json-out 落盘失败（结果仍打印到 "
                     "stdout）: %s", exc, exc_info=True)
        print(f"[coverage-scan] 警告: 结果落盘失败（{exc}），已改由 stdout 输出",
              flush=True)
def diff_scan_reports(current: dict, previous: dict,
                      drop_pp: float = _DEFAULT_DROP_PP,
                      project_root: str | Path | None = None,
                      scope: str = _DEFAULT_SCOPE) -> dict:
    drop_pp = _normalize_drop_pp(drop_pp)
    project_root = _normalize_project_root(project_root)
    scope = _normalize_scope(scope, "diff")
    cur_mods, cur_tests = _coverage_stats(current, project_root, scope)
    prev_mods, prev_tests = _coverage_stats(previous, project_root, scope)
    regressed, improved, added, alerts = [], [], [], []
    if project_root is None and (
            _has_absolute_file_keys(_norm_files(current))
            or _has_absolute_file_keys(_norm_files(previous))):
        alerts.append(
            "报告文件键为绝对路径且未提供 project_root：无法归一到项目根，"
            "回归/改善可能整侧漏失（请传 project_root 后重算）")
    for mod, (pct, covered, covered_known) in cur_mods.items():
        prev_entry = prev_mods.get(mod)
        prev_pct, prev_covered, prev_covered_known = (
            prev_entry if prev_entry is not None else (None, 0, False))
        cur_t = _test_statements_for(mod, cur_tests)
        prev_t = _test_statements_for(mod, prev_tests)
        if (cur_t > prev_t and covered_known and prev_covered_known
                and covered == prev_covered):
            alerts.append(
                f"{mod}: 测试文件语句数 +{cur_t - prev_t} 但模块覆盖行数零增长"
                "——新测试可能未被收集/执行（检查类名 Test* 前缀等收集规则）")
        if prev_pct is None:
            added.append((mod, pct))
            continue
        if pct < prev_pct - drop_pp:
            regressed.append((mod, prev_pct, pct))
        elif pct > prev_pct + drop_pp:
            improved.append((mod, prev_pct, pct))
    removed = sorted((mod, pct) for mod, (pct, _cov, _known)
                     in prev_mods.items() if mod not in cur_mods)
    for mod, pct in removed:
        alerts.append(
            f"{mod}: 基线存在（{pct}%）但本次报告缺失——模块被删除或未"
            "被收集，回归/改善均无法评估")
    return {"regressed": regressed, "improved": improved, "added": added,
            "removed": removed, "alerts": alerts}
def _test_file_basenames(module: str) -> tuple[str, str]:
    stem = os.path.splitext(module)[0]
    basename = stem.rsplit("/", 1)[-1]
    return (f"test_{basename}.py", f"{basename}_test.py")
def _dir_parts(path: str) -> list[str]:
    normalized = path.replace("\\", "/")
    if "/" not in normalized:
        return []
    return normalized.rsplit("/", 1)[0].split("/")
def _common_dir_prefix_depth(module_dirs: list[str],
                             test_dirs: list[str]) -> int:
    depth = 0
    while (depth < len(module_dirs) and depth < len(test_dirs)
           and module_dirs[depth] == test_dirs[depth]):
        depth += 1
    return depth
def _test_statements_for(module: str, tests: dict) -> float:
    basenames = _test_file_basenames(module)
    matched = [name for name in tests
               if name.rsplit("/", 1)[-1] in basenames]
    if not matched:
        return 0
    module_dirs = _dir_parts(module)
    scored = []
    for name in matched:
        test_dirs = _dir_parts(name)
        depth = _common_dir_prefix_depth(module_dirs, test_dirs)
        if depth == 0:
            if (test_dirs
                    and test_dirs[0].lower() not in _TEST_DIR_NAMES):
                continue
        elif depth != len(module_dirs) and depth != len(test_dirs):
            continue
        scored.append(((depth, -len(test_dirs)), name))
    if not scored:
        return 0
    best_score = max(score for score, _name in scored)
    best = [name for score, name in scored if score == best_score]
    return sum(tests[name] for name in best)
def _coverage_stats(report: dict,
                    project_root: str | None,
                    scope: str = _DEFAULT_SCOPE) -> tuple[dict, dict]:
    mods: dict = {}
    tests: dict = {}
    django_tests = _django_test_basenames_for_root(project_root)
    for rel, s in _iter_report_rows(report, project_root):
        if _is_test_module(rel, django_tests):
            tests[rel] = as_number(s.get("num_statements"), 0)
        if _in_scope(rel, scope, django_tests):
            mods[rel] = (round(as_number(s.get("percent_covered")), 2),
                         as_number(s.get("covered_lines"), 0),
                         is_finite_num(s.get("covered_lines")))
    return mods, tests
def summarize_coverage_report(report: dict,
                              threshold: float = DEFAULT_COVERAGE_THRESHOLD,
                              scope: str = _DEFAULT_SCOPE,
                              project_root: str | Path | None = None) -> dict:
    threshold = _normalize_threshold(threshold)
    scope = _normalize_scope(scope)
    project_root = _normalize_project_root(project_root)
    if project_root is None and _has_absolute_file_keys(_norm_files(report)):
        logger.warning(
            "[coverage] 报告文件键为绝对路径且未提供 project_root："
            "scope=%s 下的模块归属不可信（建议传 project_root 重算）", scope)
    rows = _collect_summary_rows(report, scope, project_root)
    for row in rows:
        row["percent"] = round(row["percent"], 2)
        row["percent_statements"] = round(row["percent_statements"], 2)
    totals = _scoped_summary_totals(rows)
    for row in rows:
        for key in ("_covered_lines", "_branches", "_covered_branches"):
            row.pop(key)
    below = [r for r in rows if r["percent"] < threshold]
    return {
        "totals": totals,
        "scope": scope,
        "module_count": len(rows),
        "below_count": len(below),
        "below_threshold": below,
        "pass": bool(rows) and not below,
        "threshold": threshold,
    }
def norm_nonneg_int(value, default: int, label: str) -> int:
    if is_finite_num(value):
        return max(0, int(value))
    logger.warning("[coverage] %s 形态非法（%r），回退默认 %d",
                 label, value, default)
    return default
EFFECTIVE_LEVEL_DOMAIN = ("L0", "L1", "L2")
DEFAULT_COVERAGE_TIMEOUT = 60
try:
    import coverage as _coverage_mod
    _HAS_COVERAGE = True
except ImportError as e:
    logger.debug("coverage 未安装，L2 覆盖降级到 L1: %s", e)
    _coverage_mod = None
    _HAS_COVERAGE = False
_MAX_IMPORT_SCAN_SIZE = 2 * 1024 * 1024
def _fromlist_submodule_candidates(node: ast.ImportFrom) -> list[str]:
    return [f"{node.module}.{a.name}" for a in node.names if a.name != "*"]
def resolve_project_path(path: str, project_root: str) -> str:
    if os.path.isabs(path):
        return path
    return os.path.abspath(os.path.join(project_root, path))
def _path_identity(path: str, project_root: str) -> str:
    return os.path.normcase(os.path.realpath(
        resolve_project_path(path, project_root)))
def _dedup_project_path_identities(paths: list[str],
                                   project_root: str) -> list[str]:
    result: list[str] = []
    seen: set[str] = set()
    for path in paths:
        identity = _path_identity(path, project_root)
        if identity in seen:
            continue
        seen.add(identity)
        result.append(path)
    return result
def _parent_or_empty(path: str) -> str:
    parent = os.path.dirname(path)
    return "" if parent == path else parent
def _detect_package_prefix(project_root: str) -> str:
    current = os.path.abspath(project_root)
    segments: list[str] = []
    while current:
        if not os.path.isfile(os.path.join(current, "__init__.py")):
            break
        name = os.path.basename(current)
        if not name or not name.isidentifier():
            break
        segments.append(name)
        current = _parent_or_empty(current)
    return ".".join(reversed(segments))
def _rel_module_parts(filepath: str, project_root: str) -> list[str] | None:
    filepath = resolve_project_path(filepath, project_root)
    rel = safe_relpath(filepath, project_root)
    if os.path.isabs(rel) or rel.split("/", 1)[0] in (".", ".."):
        return None
    return rel.split("/")
def _normalize_module_parts(parts: list[str]) -> tuple[list[str], bool]:
    src_stripped = False
    if parts and parts[0] == "src":
        parts = parts[1:]
        src_stripped = True
    if not parts:
        return [], src_stripped
    parts[-1] = os.path.splitext(parts[-1])[0]
    if parts[-1] == "__init__":
        parts = parts[:-1]
    return parts, src_stripped
def _qualify_module_path(parts: list[str], src_stripped: bool,
                         project_root: str) -> str:
    if src_stripped:
        return ".".join(parts)
    prefix = _detect_package_prefix(project_root)
    if prefix:
        if not parts:
            return prefix
        return prefix + "." + ".".join(parts)
    if not parts:
        return ""
    return ".".join(parts)
def file_to_module_path(filepath: str, project_root: str) -> str:
    rel_parts = _rel_module_parts(filepath, project_root)
    if rel_parts is None:
        return ""
    parts, src_stripped = _normalize_module_parts(rel_parts)
    if not parts and src_stripped:
        return ""
    return _qualify_module_path(parts, src_stripped, project_root)
def _relative_import_candidates(node: ast.ImportFrom, filepath: str,
                                project_root: str) -> list[str]:
    module_path = file_to_module_path(filepath, project_root)
    if node.level <= 0 or not module_path:
        return []
    resolved = resolve_project_path(filepath, project_root)
    package_path = (module_path if os.path.basename(resolved) == "__init__.py"
                    else module_path.rpartition(".")[0])
    package_parts = package_path.split(".") if package_path else []
    parent_levels = node.level - 1
    if not package_parts or parent_levels >= len(package_parts):
        return []
    if parent_levels:
        package_parts = package_parts[:-parent_levels]
    base = ".".join(package_parts)
    if node.module:
        base = f"{base}.{node.module}"
    modules = [base]
    modules.extend(f"{base}.{alias.name}" for alias in node.names
                   if alias.name != "*")
    return modules
def _build_stem_index(source_files: list[str]) -> tuple[dict[str, str], dict[str, str]]:
    stem_files: dict[str, set[str]] = defaultdict(set)
    stem_lower_files: dict[str, set[str]] = defaultdict(set)
    for sf in source_files:
        stem = os.path.splitext(os.path.basename(sf))[0]
        sf_norm = os.path.normpath(sf)
        stem_files[stem].add(sf_norm)
        stem_lower_files[stem.lower()].add(sf_norm)
    source_stems = {s: next(iter(p)) for s, p in stem_files.items() if len(p) == 1}
    source_stems_lower = {s: next(iter(p)) for s, p in stem_lower_files.items() if len(p) == 1}
    return source_stems, source_stems_lower
def _is_ambiguous_candidate(candidate: str, mod_alias: dict,
                            stem_alias: dict) -> bool:
    if len(mod_alias.get(candidate, ())) > 1:
        return True
    return "." not in candidate and len(stem_alias.get(candidate, ())) > 1
def _append_unique(mapping: dict[str, list[str]], key: str, value: str) -> None:
    bucket = mapping.setdefault(key, [])
    if value not in bucket:
        bucket.append(value)
def _collect_source_dirs(source_files: list[str],
                         test_files: list[str],
                         project_root: str) -> set[str]:
    source_dirs: set[str] = set()
    test_files_set = {os.path.normpath(tf) for tf in test_files}
    test_files_abs = {os.path.normpath(resolve_project_path(tf, project_root))
                      for tf in test_files}
    for sf in source_files:
        sf_norm = os.path.normpath(sf)
        sf_abs = os.path.normpath(resolve_project_path(sf, project_root))
        if sf_norm in test_files_set or sf_abs in test_files_abs:
            continue
        sf_dir = os.path.dirname(sf_abs)
        if sf_dir:
            source_dirs.add(sf_dir)
    return source_dirs
def _detect_collect_args(test_files: list[str],
                         project_root: str) -> list[str]:
    return sorted({
        os.path.normpath(resolve_project_path(tf, project_root))
        for tf in test_files
    })
_COVERAGE_PYTEST_RUNNER = (
    "import json, sys\n"
    "import coverage\n"
    "config = json.loads(sys.argv[1])\n"
    "cov = coverage.Coverage("
    "data_file=config['data_file'], source=config['source_dirs'])\n"
    "cov.start()\n"
    "try:\n"
    "    import pytest\n"
    "    rc = pytest.main(sys.argv[2:])\n"
    "finally:\n"
    "    cov.stop()\n"
    "    cov.save()\n"
    "sys.exit(rc)\n"
)
def _coverage_run_command(source_dirs: set[str], test_files: list[str],
                          project_root: str, cov_data_file: str) -> list[str]:
    collect_args = _detect_collect_args(test_files, project_root)
    config = json.dumps({
        "data_file": cov_data_file,
        "source_dirs": sorted(source_dirs),
    })
    return [
        sys.executable, "-c", _COVERAGE_PYTEST_RUNNER, config,
        "-q", "--tb=short", "--maxfail=5",
        "-p", "no:cacheprovider",
        "-o", "addopts=",
        *collect_args,
    ]
def _close_coverage_data(cov) -> None:
    try:
        cov.get_data().close()
    except Exception:
        logger.debug("[CoverageMap] coverage 数据句柄关闭失败（清理仍会尝试）",
                     exc_info=True)
def _cleanup_coverage_artifacts(cov_data_file: str, cov_data_dir: str) -> None:
    if not safe_delete(cov_data_file):
        logger.warning("[CoverageMap] 清理 coverage 数据文件失败: %s", cov_data_file)
    try:
        if not os.listdir(cov_data_dir):
            safe_delete(cov_data_dir)
    except OSError as e:
        logger.debug("临时目录清理失败（残留待后续回收）: %s: %s", cov_data_dir, e)
def _path_lookup_key(path: str) -> str:
    return os.path.normcase(os.path.normpath(path))
def _path_mapping_get(mapping: dict[str, list[str]],
                      source_file: str) -> list[str]:
    if source_file in mapping:
        return mapping[source_file]
    source_key = _path_lookup_key(source_file)
    for path, tests in mapping.items():
        if _path_lookup_key(path) == source_key:
            return tests
    return []
@dataclass
class CoverageMap:
    by_filename: dict[str, list[str]] = field(default_factory=dict)
    by_import: dict[str, list[str]] = field(default_factory=dict)
    by_coverage: dict[str, list[str]] = field(default_factory=dict)
    reverse_index: dict[str, list[str]] = field(default_factory=dict)
    effective_level: str = "L0"
    total_source_files: int = 0
    total_test_files: int = 0
    covered_files: int = 0
    def get_tests_for(self, source_file: str) -> list[str]:
        source_file = os.path.normpath(source_file)
        result: list[str] = []
        seen: set[str] = set()
        for mapping in (self.by_coverage, self.by_import, self.by_filename):
            tests = _path_mapping_get(mapping, source_file)
            for t in tests:
                t_key = _path_lookup_key(t)
                if t_key not in seen:
                    result.append(t)
                    seen.add(t_key)
        return result
    def get_covered_files(self) -> list[str]:
        all_covered: set[str] = set()
        for mapping in (self.by_filename, self.by_import, self.by_coverage):
            all_covered.update(mapping.keys())
        return sorted(all_covered)
    def get_uncovered_files(self, all_source_files: list[str]) -> list[str]:
        covered = {_path_lookup_key(f) for f in self.get_covered_files()}
        return [f for f in all_source_files if _path_lookup_key(f) not in covered]
    def coverage_ratio(self) -> float:
        if self.total_source_files == 0:
            return 0.0
        return self.covered_files / self.total_source_files
    def to_dict(self) -> dict[str, Any]:
        return {
            "by_filename_count": len(self.by_filename),
            "by_import_count": len(self.by_import),
            "by_coverage_count": len(self.by_coverage),
            "reverse_index_count": len(self.reverse_index),
            "effective_level": self.effective_level,
            "total_source_files": self.total_source_files,
            "total_test_files": self.total_test_files,
            "covered_files": self.covered_files,
            "coverage_ratio": round(self.coverage_ratio(), 4),
        }
    @classmethod
    def build(
        cls,
        source_files: list[str],
        test_files: list[str],
        project_root: str,
        run_coverage: bool = False,
        coverage_timeout: int | None = None,
    ) -> CoverageMap:
        if coverage_timeout is None:
            coverage_timeout = DEFAULT_COVERAGE_TIMEOUT
        cm = cls()
        source_files = _dedup_project_path_identities(
            [resolve_project_path(p, project_root)
             for p in normalize_path_list(source_files, "source_files")],
            project_root)
        test_files = _dedup_project_path_identities(
            [resolve_project_path(p, project_root)
             for p in normalize_path_list(test_files, "test_files")],
            project_root)
        test_ids = {_path_identity(tf, project_root) for tf in test_files}
        kept: list[str] = []
        excluded: list[str] = []
        for sf in source_files:
            if _path_identity(sf, project_root) in test_ids:
                excluded.append(sf)
            else:
                kept.append(sf)
        if excluded:
            logger.info(
                "[CoverageMap] 源清单剔除 %d 个测试文件（源/测试重叠）: %s",
                len(excluded), excluded[:3])
        source_files = kept
        cm.total_source_files = len(source_files)
        cm.total_test_files = len(test_files)
        if not test_files:
            logger.debug("[CoverageMap] 无测试文件，返回空映射")
            return cm
        cm._build_filename_mapping(source_files, test_files)
        cm.effective_level = "L0"
        cm._build_import_mapping(source_files, test_files, project_root)
        if cm.by_import:
            cm.effective_level = "L1"
        if run_coverage:
            cm._apply_coverage_stage(source_files, test_files,
                                     project_root, coverage_timeout)
        cm.build_reverse_index()
        cm.covered_files = len(cm.get_covered_files())
        logger.info(
            "[CoverageMap] 构建完成: level=%s, covered=%d/%d (%.1f%%)",
            cm.effective_level, cm.covered_files, cm.total_source_files,
            cm.coverage_ratio() * 100,
        )
        return cm
    def _build_filename_mapping(self, source_files: list[str],
                                test_files: list[str]) -> None:
        source_stems, source_stems_lower = _build_stem_index(source_files)
        for tf in test_files:
            tf_norm = os.path.normpath(tf)
            test_stem = os.path.splitext(os.path.basename(tf))[0]
            test_stem_lower = test_stem.lower()
            matched_stem = ""
            if test_stem_lower.startswith("test_"):
                matched_stem = test_stem[5:]
            elif (test_stem.startswith("Test") and len(test_stem) > 4
                  and test_stem[4].isupper()):
                matched_stem = test_stem[4:]
            elif test_stem_lower.endswith("_test"):
                matched_stem = test_stem[:-5]
            if not matched_stem:
                continue
            sf = (source_stems.get(matched_stem)
                  or source_stems_lower.get(matched_stem.lower()))
            if sf is not None:
                _append_unique(self.by_filename, sf, tf_norm)
    def _build_import_mapping(
        self, source_files: list[str], test_files: list[str], project_root: str
    ) -> None:
        source_modules, mod_alias, stem_alias = self._build_module_index(
            source_files, project_root)
        for tf in test_files:
            tf_norm = os.path.normpath(tf)
            imported_modules = self._extract_imports(tf, project_root)
            for mod in imported_modules:
                self._link_import(tf_norm, mod, source_modules,
                                  mod_alias, stem_alias)
    def _build_module_index(
            self, source_files: list[str], project_root: str
    ) -> tuple[dict[str, str], dict[str, set[str]], dict[str, set[str]]]:
        source_modules: dict[str, str] = {}
        mod_alias: dict[str, set[str]] = defaultdict(set)
        stem_alias: dict[str, set[str]] = defaultdict(set)
        for sf in source_files:
            sf_norm = os.path.normpath(sf)
            mod_path = file_to_module_path(sf, project_root)
            if mod_path:
                source_modules[mod_path] = sf_norm
                mod_alias[mod_path].add(sf_norm)
            stem = os.path.splitext(os.path.basename(sf))[0]
            if stem != "__init__":
                source_modules.setdefault(stem, sf_norm)
                stem_alias[stem].add(sf_norm)
        return source_modules, mod_alias, stem_alias
    def _link_import(self, tf_norm: str, mod: str,
                     source_modules: dict[str, str],
                     mod_alias: dict, stem_alias: dict) -> None:
        candidates = [mod]
        if mod not in source_modules:
            parts = mod.split(".")
            candidates = [".".join(parts[:i])
                          for i in range(len(parts) - 1, 0, -1)]
        for candidate in candidates:
            if candidate not in source_modules:
                continue
            if _is_ambiguous_candidate(candidate, mod_alias, stem_alias):
                count = max(len(mod_alias.get(candidate, ())),
                            len(stem_alias.get(candidate, ())))
                logger.debug("[CoverageMap] 候选 '%s' 有 %d 个候选源文件, 跳过歧义匹配",
                             candidate, count)
                return
            _append_unique(self.by_import, source_modules[candidate], tf_norm)
            return
    def _apply_coverage_stage(self, source_files: list[str],
                              test_files: list[str], project_root: str,
                              timeout: int) -> None:
        if not _HAS_COVERAGE:
            logger.warning(
                "[CoverageMap] 请求 L2 coverage 但 coverage.py 未安装，保持 L1 降级"
            )
            return
        try:
            self._build_coverage_mapping(source_files, test_files,
                                         project_root, timeout)
            if self.by_coverage:
                self.effective_level = "L2"
        except Exception as e:  # noqa: BLE001
            logger.warning("[CoverageMap] L2 coverage 构建失败，降级至已建层级（L0/L1）: %s", e)
    def _build_coverage_mapping(
        self, source_files: list[str], test_files: list[str],
        project_root: str, timeout: int
    ) -> None:
        if not test_files:
            logger.debug("[CoverageMap] 无测试文件，跳过 L2 coverage 构建")
            return
        source_dirs = _collect_source_dirs(
            source_files, test_files, project_root)
        if not source_dirs:
            logger.debug("[CoverageMap] source_dirs 为空，跳过 L2 coverage 构建")
            return
        cov_data_dir = os.path.join(
            get_temp_base(project_root),
            f"coverage_bridge_{os.getpid()}_{threading.get_ident()}")
        os.makedirs(cov_data_dir, exist_ok=True)
        cov_data_file = os.path.join(cov_data_dir, ".coverage_bridge")
        try:
            cmd = _coverage_run_command(
                source_dirs, test_files, project_root, cov_data_file)
            result = subprocess.run(  # jwsgj:suppress SYM-TAINT — 审计认可：cmd 由 _coverage_run_command 内部构造（sys.executable -m coverage）
                cmd, cwd=project_root, capture_output=True, text=True,
                timeout=timeout, encoding="utf-8", errors="replace", check=False,
                env=subprocess_noartifact_env(),
            )
            if result.returncode not in (0, 1):
                logger.warning(
                    "[CoverageMap] coverage run 异常退出 rc=%d（5=未收集到"
                    "用例），L2 保持 L0/L1 降级", result.returncode)
                return
            cov = _coverage_mod.Coverage(data_file=cov_data_file)
            try:
                cov.load()
                self._collect_coverage_results(cov, source_files, project_root)
            finally:
                _close_coverage_data(cov)
        except subprocess.TimeoutExpired:
            logger.warning("[CoverageMap] coverage run 超时 (%ds)", timeout, exc_info=True)
        except (OSError, ValueError) as e:
            logger.warning("[CoverageMap] coverage run 异常: %s", e, exc_info=True)
        finally:
            _cleanup_coverage_artifacts(cov_data_file, cov_data_dir)
    def _collect_coverage_results(self, cov, source_files: list[str],
                                   project_root: str) -> None:
        for sf_raw in source_files:
            sf = os.path.normpath(sf_raw)
            sf_analyze = resolve_project_path(sf_raw, project_root)
            try:
                _, executable, _, missing, _ = cov.analysis2(sf_analyze)
                executed = len(executable) - len(missing)
                if executed > 0:
                    covering_tests = self._tests_exercising_module(sf)
                    if covering_tests:
                        self.by_coverage[sf] = covering_tests
            except Exception:
                logger.warning("[CoverageMap] coverage analysis2 失败: %s", sf, exc_info=True)
    def _tests_exercising_module(self, source_file: str) -> list[str]:
        import_mapping = self.by_import.get(source_file, [])
        filename_mapping = self.by_filename.get(source_file, [])
        combined = list(dict.fromkeys(import_mapping + filename_mapping))
        if combined:
            logger.debug(
                "[CoverageMap] L2 coverage 按 L1 精度归并: %s → %d tests",
                source_file, len(combined),
            )
        return combined
    def build_reverse_index(self) -> None:
        self.reverse_index.clear()
        for mapping in (self.by_filename, self.by_import, self.by_coverage):
            for sf, tests in mapping.items():
                for tf in tests:
                    _append_unique(self.reverse_index, tf, sf)
    @staticmethod
    def _extract_imports(filepath: str, project_root: str) -> list[str]:
        fp = resolve_project_path(filepath, project_root)
        _, tree = load_test_ast(
            fp, None, None, "CoverageMap._extract_imports",
            max_size=_MAX_IMPORT_SCAN_SIZE)
        if tree is None:
            return []
        modules: list[str] = []
        for node in walk_nodes(tree):
            if isinstance(node, ast.Import):
                modules.extend(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom):
                if node.level > 0:
                    modules.extend(_relative_import_candidates(
                        node, fp, project_root))
                elif node.module:
                    modules.append(node.module)
                    modules.extend(_fromlist_submodule_candidates(node))
        return modules
def prune_scan_dirs(dirs: list, extra_excludes: tuple = ()) -> None:
    excludes_lower = _DEFAULT_EXCLUDE_DIRS_LOWER
    if extra_excludes:
        excludes_lower = excludes_lower | frozenset(
            d.lower() for d in extra_excludes)
    _prune_walk_dirs(dirs, excludes_lower)
def iter_py_files_under(base_dir: str, extra_excludes: tuple = ()):
    for root, dirs, filenames in os.walk(base_dir):
        dirs.sort()
        prune_scan_dirs(dirs, extra_excludes)
        for f in sorted(filenames):
            if f.startswith(".") or not f.lower().endswith(".py"):
                continue
            yield os.path.join(root, f)
def _root_test_files(skill_dir: str) -> list[str]:
    try:
        names = sorted(os.listdir(skill_dir))
    except OSError as exc:
        logger.warning("[coverage] 根目录测试文件枚举失败: %s (%s)",
                       skill_dir, exc)
        return []
    return [os.path.join(skill_dir, name) for name in names
            if (os.path.isfile(os.path.join(skill_dir, name))
                and is_py_source_file(name)
                and is_test_source_basename(name))]
def iter_test_source_files(skill_dir: str):
    root = str(skill_dir)
    if not root or not os.path.isdir(root):
        return
    seen: set[str] = set()
    candidates = [*_iter_container_test_files(root), *_root_test_files(root)]
    django_tests = _django_test_basenames_for_root(root)
    candidates.extend(
        path for path in iter_py_files_under(root)
        if is_test_source_basename(os.path.basename(path))
        or os.path.basename(path).lower() in django_tests)
    for path in candidates:
        key = os.path.normcase(os.path.abspath(path))
        if key in seen:
            continue
        seen.add(key)
        yield path
def _iter_container_test_files(skill_dir: str):
    for test_dir in iter_test_dirs(skill_dir):
        yield from iter_py_files_under(test_dir)
    extra_dirs = TEST_ARTIFACT_DIRS - TEST_DIR_CANDIDATES_LOWER
    if not extra_dirs:
        return
    for root, dirs, _files in os.walk(skill_dir):
        dirs.sort()
        prune_scan_dirs(dirs)
        selected = [d for d in dirs if d.lower() in extra_dirs]
        for dirname in selected:
            for path in iter_py_files_under(os.path.join(root, dirname)):
                if is_test_source_basename(os.path.basename(path)):
                    yield path
        dirs[:] = [d for d in dirs if d.lower() not in TEST_ARTIFACT_DIRS]
def iter_scoped_py(skill_dir: str):
    django_tests = _django_test_basenames_for_root(skill_dir)
    for path in iter_py_files_under(skill_dir, tuple(TEST_ARTIFACT_DIRS)):
        name = os.path.basename(path)
        if is_test_source_basename(name):
            continue
        if (name.lower() in _TEST_INFRA_BASENAMES
                or name.lower() in django_tests):
            continue
        yield path
DEFAULT_PROJECT_CONFIG_NAME = ".test-coverage.yml"
try:
    import yaml as _yaml_mod
except ImportError as _imp_err:
    logger.debug("[Adapter] yaml 导入失败，降级占位 None: %s", _imp_err)
    _yaml_mod = None
_DEFAULT_EXCLUDE_DIRS = _SKIP_DIRS
_DEFAULT_EXCLUDE_DIRS_LOWER = SKIP_DIRS_LOWER
def is_outside_root(rel: str) -> bool:
    norm = os.path.normpath(rel)
    return norm == os.pardir or norm.startswith(os.pardir + os.sep)
def _prune_walk_dirs(dirs: list[str],
                     excludes_lower: frozenset[str]) -> None:
    dirs[:] = [d for d in dirs
               if d.lower() not in excludes_lower
               and not d.startswith(".")
               and not is_backup_like_dir(d)]
class ProjectAdapter:
    PROTECTED_BASENAMES: ClassVar[tuple[str, ...]] = ()
    TEST_DIRNAMES: ClassVar[tuple[str, ...]] = TEST_DIR_CANDIDATES
    def __init__(self, root: str):
        self.root = os.path.abspath(root)
    def _is_test_side_path(self, path: str) -> bool:
        rel = safe_relpath(path, self.root)
        if not is_outside_root(rel):
            parts = rel.replace("\\", "/").split("/")
            test_dirnames = {name.lower() for name in self.TEST_DIRNAMES}
            test_dirnames |= TEST_ARTIFACT_DIRS
            if any(part.lower() in test_dirnames for part in parts[:-1]):
                return True
        if os.path.basename(path).lower() in _TEST_INFRA_BASENAMES:
            return True
        return self.is_test_file(path)
    def get_source_files(self) -> list[str]:
        return [path for path in self._walk_py_files()
                if not self._is_test_side_path(path)]
    def get_test_files(self) -> list[str]:
        return [path for path in self._walk_py_files()
                if self.is_test_file(path)]
    def _protected_basenames(self) -> frozenset[str]:
        return frozenset(self.PROTECTED_BASENAMES)
    def is_test_file(self, path: str) -> bool:
        return is_test_source_basename(os.path.basename(path))
    def is_protected_file(self, path: str) -> bool:
        basename = os.path.basename(path).lower()
        dirname = os.path.dirname(path)
        try:
            rel_path = os.path.relpath(path, self.root)
        except ValueError:
            rel_path = None
        if rel_path and not is_outside_root(rel_path):
            test_dirnames = {name.lower() for name in self.TEST_DIRNAMES}
            test_dirnames |= TEST_ARTIFACT_DIRS
            parts = rel_path.replace("\\", "/").split("/")
            if any(part.lower() in test_dirnames for part in parts[:-1]):
                return True
        if basename in _PROTECTED_INFRA_BASENAMES:
            return True
        if is_test_source_basename(basename):
            return True
        if self._within_root_temp(dirname):
            return True
        if basename.endswith((".bak", ".backup", ".pyc", ".pyo")):
            return True
        return basename in self._protected_basenames()
    def _within_root_temp(self, dirname: str) -> bool:
        try:
            _rel_dir = os.path.relpath(dirname or ".", self.root)
        except ValueError as _e:
            log_swallowed(__name__, _e,
                          context='ProjectAdapter._within_root_temp:ValueError')
            return False
        return bool(
            _rel_dir
            and not is_outside_root(_rel_dir)
            and "temp" in (p.lower() for p in _rel_dir.split(os.sep))
        )
    def get_exclude_dirs(self) -> set[str]:
        return set(_DEFAULT_EXCLUDE_DIRS)
    def get_temp_dir(self) -> str:
        return get_temp_base(self.root)
    def _collect_py_under(self, base_dir: str,
                          excludes: set[str] | frozenset[str]) -> list[str]:
        out: list[str] = []
        excludes_lower = frozenset(e.lower() for e in excludes)
        for root, dirs, filenames in os.walk(base_dir):
            dirs.sort()
            _prune_walk_dirs(dirs, excludes_lower)
            for f in sorted(filenames):
                if f.lower().endswith(".py") and not f.startswith("."):
                    out.append(os.path.join(root, f))
        return out
    def _resolve_include_dir(self, inc_dir: str) -> str | None:
        full_dir = os.path.normpath(os.path.join(self.root, inc_dir))
        try:
            rel_inc = os.path.relpath(full_dir, self.root)
        except ValueError as _e:
            log_swallowed(__name__, _e,
                          context='ProjectAdapter._resolve_include_dir:ValueError')
            return None
        if is_outside_root(rel_inc):
            logger.warning("[Adapter] include_dirs 越出项目根，跳过: %s", inc_dir)
            return None
        if not os.path.isdir(full_dir):
            return None
        return full_dir
    def _walk_py_files(
        self,
        include_dirs: list[str] | None = None,
        exclude_dirs: set[str] | frozenset[str] | None = None,
    ) -> list[str]:
        excludes = exclude_dirs if exclude_dirs is not None else self.get_exclude_dirs()
        files = []
        if include_dirs is not None:
            for inc_dir in include_dirs:
                full_dir = self._resolve_include_dir(inc_dir)
                if full_dir is None:
                    continue
                files.extend(self._collect_py_under(full_dir, excludes))
        else:
            files.extend(self._collect_py_under(self.root, excludes))
        return sorted(set(files))
class SkillAdapter(ProjectAdapter):
    PROTECTED_BASENAMES = ("skill.md", "pytest.ini")
class PackageAdapter(ProjectAdapter):
    PROTECTED_BASENAMES = (
        "setup.py", "pyproject.toml", "setup.cfg", "manage.py", "wsgi.py",
    )
    def get_source_files(self) -> list[str]:
        src_dir = os.path.join(self.root, "src")
        if os.path.isdir(src_dir):
            return [path for path in self._walk_py_files(
                include_dirs=["src"])
                if not self._is_test_side_path(path)]
        return super().get_source_files()
class DjangoAdapter(ProjectAdapter):
    DJANGO_EXCLUDE_DIRS = _DEFAULT_EXCLUDE_DIRS | {
        "migrations", "static", "media", "templates",
        "locale", "fixtures",
    }
    DJANGO_TEST_BASENAMES = ("tests.py", "test_models.py", "test_views.py")
    PROTECTED_BASENAMES = (
        "manage.py", "wsgi.py", "asgi.py", "settings.py", "urls.py",
    ) + DJANGO_TEST_BASENAMES
    def get_exclude_dirs(self) -> set[str]:
        return set(self.DJANGO_EXCLUDE_DIRS)
    def _walk_source_area(self) -> list[str]:
        apps_dir = os.path.join(self.root, "apps")
        if os.path.isdir(apps_dir):
            return self._walk_py_files(include_dirs=["apps"])
        return self._walk_py_files()
    def is_test_file(self, path: str) -> bool:
        basename = os.path.basename(path).lower()
        return (basename in self.DJANGO_TEST_BASENAMES
                or is_test_source_basename(basename))
    def get_source_files(self) -> list[str]:
        return [f for f in self._walk_source_area()
                if not self._is_test_side_path(f)]
def _as_pattern_list(config: dict, key: str, default: list[str]) -> list[str]:
    value = config.get(key)
    if (isinstance(value, list)
            and all(isinstance(item, str) for item in value)):
        return list(value)
    if value is not None:
        logger.warning(
            "[Adapter] 配置字段 %s 非字符串列表形态(%s)，回退默认值",
            key, type(value).__name__,
        )
    return default
def _as_protected_set(config: dict, key: str) -> set[str]:
    value = config.get(key)
    if isinstance(value, (list, tuple, set)):
        return {str(item) for item in value}
    if value is not None:
        logger.warning(
            "[Adapter] 配置字段 %s 非列表形态(%s)，回退空集",
            key, type(value).__name__,
        )
    return set()
def _resolve_exclude_hits(
    exclude_patterns: list[str] | None, root: str
) -> tuple[set[str], list[str]]:
    discarded: set[str] = set()
    prefixes: list[str] = []
    for pattern in exclude_patterns or ():
        for excluded in glob.glob(os.path.join(root, pattern), recursive=True):
            norm = os.path.normpath(excluded)
            key = _path_lookup_key(norm)
            discarded.add(key)
            if os.path.isdir(norm):
                prefixes.append(key + os.sep)
    return discarded, prefixes
_DEFAULT_TEST_FILE_PATTERNS = ("**/test_*.py", "**/*_test.py")
class GenericAdapter(ProjectAdapter):
    def __init__(self, root: str, config: dict):
        super().__init__(root)
        if not isinstance(config, dict):
            raise TypeError(
                f"config 必须为 dict 形态，实际为 {type(config).__name__}")
        self._source_patterns = _as_pattern_list(config, "source_patterns", ["**/*.py"])
        django_extra_tests = tuple(
            name for name in _django_test_basenames_for_root(self.root)
            if not is_test_source_basename(name))
        self._test_patterns = _as_pattern_list(
            config, "test_patterns", list(_DEFAULT_TEST_FILE_PATTERNS)
            + [f"**/{name}" for name in django_extra_tests])
        default_excludes = (
            [f"**/{name}/**" for name in sorted(TEST_ARTIFACT_DIRS)]
            + list(_DEFAULT_TEST_FILE_PATTERNS)
            + [f"**/{name}" for name in _TEST_INFRA_BASENAMES]
            + [f"**/{name}" for name in django_extra_tests])
        default_excludes.extend(
            pattern for pattern in self._test_patterns
            if pattern not in default_excludes)
        self._exclude_patterns = _as_pattern_list(
            config, "exclude_patterns", default_excludes)
        self._protected_files = {
            pf.lower()
            for pf in _as_protected_set(config, "protected_files")
        }
    def _filter_glob_results(self, files) -> list[str]:
        result = []
        for f in sorted(files):
            if not os.path.isfile(f):
                continue
            try:
                rel = os.path.relpath(f, self.root)
            except ValueError:
                logger.warning("[Adapter] glob 结果跨盘符不可相对化，跳过: %s", f)
                continue
            if is_outside_root(rel):
                logger.warning("[Adapter] glob 结果越出项目根，跳过: %s", f)
                continue
            parts = rel.split(os.sep)
            if any(p.lower() in _DEFAULT_EXCLUDE_DIRS_LOWER
                   or is_backup_like_dir(p) for p in parts[:-1]):
                continue
            result.append(f)
        return result
    def _glob_filtered(
        self,
        patterns: list[str],
        exclude_patterns: list[str] | None = None,
    ) -> list[str]:
        files = set()
        for pattern in patterns:
            files.update(
                os.path.normpath(p)
                for p in glob.glob(os.path.join(self.root, pattern), recursive=True)
            )
        discarded, prefixes = _resolve_exclude_hits(
            exclude_patterns, self.root)
        files = {f for f in files if _path_lookup_key(f) not in discarded}
        if prefixes:
            files = {f for f in files
                     if not any(_path_lookup_key(f).startswith(p)
                                for p in prefixes)}
        return self._filter_glob_results(files)
    def get_source_files(self) -> list[str]:
        files = self._glob_filtered(self._source_patterns, self._exclude_patterns)
        test_files = {_path_lookup_key(f) for f in self.get_test_files()}
        return [
            f for f in files
            if not self._is_test_side_path(f)
            and _path_lookup_key(f) not in test_files
        ]
    def get_test_files(self) -> list[str]:
        return self._glob_filtered(self._test_patterns)
    def _protected_basenames(self) -> frozenset[str]:
        return super()._protected_basenames() | frozenset(self._protected_files)
def detect_project_type(root: str) -> str:
    root = os.path.abspath(root)
    if os.path.isfile(os.path.join(root, "manage.py")):
        return "django"
    if os.path.isfile(os.path.join(root, "SKILL.md")):
        return "skill"
    if (os.path.isdir(os.path.join(root, "src")) or
            os.path.isfile(os.path.join(root, "setup.py")) or
            os.path.isfile(os.path.join(root, "pyproject.toml"))):
        return "package"
    return "generic"
def load_config(root: str, config_path: str | None = None) -> dict | None:
    if config_path is None:
        config_path = os.path.join(root, DEFAULT_PROJECT_CONFIG_NAME)
    elif not os.path.isabs(config_path):
        config_path = os.path.join(root, config_path)
    if not os.path.isfile(config_path):
        return None
    if _yaml_mod is None:
        logger.warning(
            "[Adapter] PyYAML 未安装，跳过配置文件解析（pip install pyyaml 后重试）: %s",
            config_path,
        )
        return None
    try:
        with open(config_path, encoding="utf-8") as f:
            result = _yaml_mod.safe_load(f)
        if not isinstance(result, dict):
            logger.warning(
                "[Adapter] 配置文件顶层非映射(%s)，忽略: %s",
                type(result).__name__, config_path,
            )
            return None
        return result
    except Exception as e:  # noqa: BLE001
        logger.warning("[Adapter] 配置文件加载失败: %s", e)
        return None
_ADAPTER_BY_TYPE: dict[str, type[ProjectAdapter]] = {
    "skill": SkillAdapter,
    "package": PackageAdapter,
    "django": DjangoAdapter,
    "generic": ProjectAdapter,
}
def create_adapter(
    root: str,
    project_type: str | None = None,
    config: dict | None = None,
    config_path: str | None = None,
) -> ProjectAdapter:
    root = os.path.abspath(root)
    if config is None and (project_type is None or config_path is not None):
        config = load_config(root, config_path)
    if config is not None:
        logger.info("[Adapter] 使用配置驱动的 GenericAdapter")
        return GenericAdapter(root, config)
    if project_type is None:
        project_type = detect_project_type(root)
    _adapter_cls = _ADAPTER_BY_TYPE.get(project_type)
    if _adapter_cls is not None:
        return _adapter_cls(root)
    logger.info("[Adapter] 未识别项目类型(%r)，使用通用适配器", project_type)
    return ProjectAdapter(root)

from __future__ import annotations

import ast
import io
import logging
import math
import os
import tokenize
from collections import Counter, defaultdict
from collections.abc import Callable
from dataclasses import dataclass, field
from itertools import pairwise
from typing import Any

from jwsgj.diag_guard_state import (
    read_json_artifact,
    write_json_artifact,
)
from jwsgj.diag_shared_ast_nodes import (
    is_self_caller_name,
    normalize_torn_name,
    parse_source_tree,
)
from jwsgj.diag_shared_source_core import (
    iter_file_trees,
    read_source,
)
from jwsgj.diag_testing_coverage import (
    iter_py_files_under,
    iter_test_source_files,
    resolve_project_path,
)
from jwsgj.diag_testing_test_index import iter_collectable_test_functions
from jwsgj.diag_types_normalize import (
    append_judgment,
    append_recommendation_once,
    int_metric,
    normalize_list_field,
    ratio01,
    section_dict,
    signal_bool,
    timestamp_human,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    FIELD_RECOMMENDATIONS,
    FIELD_TOTAL_BLINDSPOTS,
    FIELD_TOTAL_FUNCTIONS,
    PERCENT_FACTOR,
)
from jwsgj.log_config import (
    locked_artifact,
    log_swallowed,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    baseline_data_dir,
)
from jwsgj.runtime_scope import (
    TEST_DIR_CANDIDATES,
    is_test_source_basename,
)

__all__ = [
    'COMMENT_RATIO_LINE_BUDGET',
    'SUB_METRICS',
    'BaselineManager',
    'BaselineReport',
    'MetricDelta',
    'TestCoverageMapper',
    'TrendPoint',
    'analyze_call_depth',
    'apply_baseline_comparison',
    'blindspot_total',
    'compute_comment_ratio',
    'record_degradation',
    'score_test_coverage_ratio',
    'supplement_graph_report_dimensions',
]
logger = logging.getLogger(__name__)
logger.info("diag_health_profile 健康画像与基线域已加载: %d 项导出", len(__all__))
def _text_path(value: Any) -> str:
    if isinstance(value, str):
        return value
    try:
        return os.fsdecode(os.fspath(value))
    except TypeError:
        return ""
def _collect_test_files_for_coverage(skill_dir: str) -> list[str]:
    return [path for path in iter_test_source_files(_text_path(skill_dir))
            if is_test_source_basename(os.path.basename(path))]
def _resolve_coverage_ratio(report: dict, test_func_count: int,
                            src_func_count: int
                            ) -> tuple[float | None, str, bool, bool]:
    tc_mapped = report.get("test_coverage")
    _tc_pct = (tc_mapped.get("coverage_pct")
               if isinstance(tc_mapped, dict) else None)
    _tc_pct_num = _coerce_num(_tc_pct, None, '_resolve_coverage_ratio')
    has_mapped = _tc_pct_num is not None
    if has_mapped:
        _tc_num = int_metric(tc_mapped.get("tested_count", 0))
        _tc_den = _tc_num + int_metric(tc_mapped.get("untested_count", 0))
        tc_frac = f"{_tc_num}/{_tc_den}"
        if _tc_den > 0 or _tc_pct_num != 0:
            return ratio01(_tc_pct_num / 100.0), tc_frac, True, True
        return None, tc_frac, True, False
    if src_func_count <= 0:
        return None, "0/0", False, False
    return (ratio01(test_func_count / max(src_func_count, 1)),
            f"{test_func_count}/{src_func_count}", False, True)
def _count_test_defs_in_files(test_files: list[str], ctx: Any = None) -> int:
    return sum(1
               for _fp, tree in iter_file_trees(test_files, ctx)
               for _node in iter_collectable_test_functions(tree))
def _has_test_config(skill_dir: str) -> bool:
    candidates = [
        os.path.join(skill_dir, cfg)
        for cfg in ("conftest.py", "pytest.ini", "setup.cfg",
                    "tox.ini", "pyproject.toml")
    ]
    candidates.extend(
        os.path.join(skill_dir, dirname, "conftest.py")
        for dirname in TEST_DIR_CANDIDATES
    )
    return any(os.path.isfile(path) for path in candidates)
def _coverage_penalty(coverage_ratio: float | None, tc_frac: str, *,
                      has_mapped: bool, src_func_count: int,
                      test_file_count: int, test_func_count: int,
                      measured: bool = True,
                      ) -> tuple[int, str, str]:
    if not measured or coverage_ratio is None:
        return 0, "info", (
            f"Test coverage: not measured ({tc_frac}; "
            "no measured source functions to compare)")
    detail = f"{tc_frac} ({coverage_ratio * 100:.1f}%)"
    if (not has_mapped and src_func_count > 0
            and test_file_count == 0 and test_func_count == 0):
        return 5, "warn", (
            f"Test coverage: 0 test files, 0 test functions "
            f"for {src_func_count} source functions")
    if coverage_ratio < 0.1:
        return 3, "warn", (
            f"Test coverage: {detail} below 10% threshold")
    if coverage_ratio < 0.3:
        return 1, "info", f"Test coverage: {detail}"
    return 0, "pass", f"Test coverage: {detail}"
def score_test_coverage_ratio(report: dict, skill_dir: str,
                              ctx: Any = None) -> int:
    if not isinstance(report, dict):
        logger.warning(
            "[test_coverage] report 非映射（%s），按空报告评估且不落证据",
            type(report).__name__)
        report = {}
    skill_dir_text = _text_path(skill_dir)
    test_files = _collect_test_files_for_coverage(skill_dir_text)
    test_func_count = _count_test_defs_in_files(test_files, ctx)
    _cc_src = report.get("call_chain")
    src_func_count = (
        int_metric(_cc_src.get(FIELD_TOTAL_FUNCTIONS, 0))
        if isinstance(_cc_src, dict) and _cc_src
        else 0
    )
    coverage_ratio, tc_frac, has_mapped, measured = _resolve_coverage_ratio(
        report, test_func_count, src_func_count)
    test_file_count = len(test_files)
    penalty, level, message = _coverage_penalty(
        coverage_ratio, tc_frac,
        has_mapped=has_mapped,
        src_func_count=src_func_count,
        test_file_count=test_file_count,
        test_func_count=test_func_count,
        measured=measured,
    )
    append_judgment(report, "test_coverage", level, message)
    report["test_coverage_assessment"] = {
        "test_files": test_file_count,
        "test_functions": test_func_count,
        "source_functions": src_func_count,
        "coverage_ratio": (round(coverage_ratio, 4)
                           if coverage_ratio is not None else None),
        "coverage_measured": measured,
        "has_test_config": _has_test_config(skill_dir_text),
        "penalty": penalty,
    }
    return penalty
_DEEP_CHAIN_MIN_DEPTH = 5
def _depth_statistics(all_depths: dict) -> tuple[int, float, float, dict[int, int]]:
    depth_values = list(all_depths.values()) or [0]
    max_depth = max(depth_values)
    avg_depth = sum(depth_values) / len(depth_values)
    sorted_depths = sorted(depth_values)
    midpoint = len(sorted_depths) // 2
    if len(sorted_depths) % 2:
        median_depth = float(sorted_depths[midpoint])
    else:
        median_depth = (sorted_depths[midpoint - 1] + sorted_depths[midpoint]) / 2
    return max_depth, avg_depth, median_depth, Counter(depth_values)
def _call_graph_functions(call_graph: Any) -> dict:
    for attr in ("functions", "_nodes"):
        table = getattr(call_graph, attr, None)
        if isinstance(table, dict) and table:
            return table
    return {}
def _call_graph_edges(call_graph: Any) -> list:
    edges = getattr(call_graph, "calls", None)
    if edges is None or isinstance(edges, (str, bytes, dict)):
        return []
    try:
        return list(edges)
    except TypeError as _e:
        log_swallowed(__name__, _e, context='_call_graph_edges:TypeError')
        return []
def _depth_report(payload: dict | None = None, *, measured: bool = True,
                  reason: str | None = None) -> dict:
    report = {
        "max_depth": 0, "avg_depth": 0, "median_depth": 0,
        "depth_distribution": {}, "deep_chains": [], "shallow_chains": [],
        "entry_points": 0, "leaf_functions": 0, "depth_score": 0.0,
    }
    if payload:
        report.update(payload)
    report["measured"] = measured
    if reason is not None:
        report["reason"] = reason
    return report
def analyze_call_depth(call_graph: Any) -> dict:
    if call_graph is None:
        return _depth_report(measured=False, reason="call_graph unavailable")
    functions = _call_graph_functions(call_graph)
    if not functions:
        return _depth_report(
            measured=False,
            reason=(f"call_graph has no function table "
                    f"(got {type(call_graph).__name__})"))
    edges = _call_graph_edges(call_graph)
    adj, rev_adj, all_funcs, external_roots = _build_depth_graph(
        functions, edges)
    entry_points = _find_depth_entry_points(
        functions, rev_adj, all_funcs, external_roots)
    leaf_count = _count_leaf_functions(adj, all_funcs)
    all_depths, entry_depths = _calculate_depths(
        entry_points, adj, all_funcs)
    entry_max_depth, entry_reached = _aggregate_entry_depths(entry_depths)
    deep_chains = _collect_deep_chains(entry_points, entry_max_depth,
                                       entry_reached)
    max_depth, avg_depth, median_depth, dist = _depth_statistics(all_depths)
    shallow_chains = _collect_shallow_chains(entry_points, entry_max_depth)
    return _depth_report({
        "max_depth": max_depth,
        "avg_depth": round(avg_depth, 2),
        "median_depth": median_depth,
        "depth_distribution": dict(sorted(dist.items())),
        "deep_chains": deep_chains,
        "shallow_chains": shallow_chains[:20],
        "entry_points": len(entry_points),
        "leaf_functions": leaf_count,
        "depth_score": round(_depth_health_score(dist), 3),
    })
def _build_depth_graph(functions: dict, edges: list
                       ) -> tuple[dict, dict, set, set]:
    adj = defaultdict(list)
    rev_adj = defaultdict(list)
    all_funcs = set(functions)
    external_roots: set = set()
    for edge in edges:
        caller = getattr(edge, 'caller_func', '')
        callee = getattr(edge, 'callee_func', '')
        if not caller or not callee or getattr(edge, 'is_external', False):
            continue
        if callee not in all_funcs:
            continue
        if is_self_caller_name(caller, callee):
            continue
        if caller not in all_funcs:
            external_roots.add(callee)
            continue
        adj[caller].append(callee)
        rev_adj[callee].append(caller)
    return adj, rev_adj, all_funcs, external_roots
def _find_depth_entry_points(functions: dict, rev_adj: dict, all_funcs: set,
                             external_roots: set) -> list:
    in_degree = {f: len(rev_adj.get(f, [])) for f in all_funcs}
    roots = {f for f, deg in in_degree.items() if deg == 0}
    entry_points = ({f for f in roots
                     if getattr(functions.get(f), 'is_public', False)}
                    | external_roots)
    if not entry_points:
        entry_points = roots
    return sorted(entry_points, key=_entry_sort_key)
def _entry_sort_key(entry) -> tuple[str, str]:
    return (normalize_torn_name(entry), type(entry).__name__)
def _count_leaf_functions(adj: dict, all_funcs: set) -> int:
    out_degree = {f: len(adj.get(f, [])) for f in all_funcs}
    return sum(1 for deg in out_degree.values() if deg == 0)
def _sorted_neighbors(node, adj: dict) -> list:
    return sorted(adj.get(node, ()), key=_entry_sort_key)
def _depth_traversal(seed, adj: dict) -> tuple[list, set]:
    state = {seed: 1}
    postorder = []
    back_edges = set()
    stack = [(seed, iter(_sorted_neighbors(seed, adj)))]
    while stack:
        node, neighbors = stack[-1]
        try:
            neighbor = next(neighbors)
        except StopIteration:
            stack.pop()
            state[node] = 2
            postorder.append(node)
            continue
        if neighbor not in state:
            state[neighbor] = 1
            stack.append((neighbor, iter(_sorted_neighbors(neighbor, adj))))
        elif state[neighbor] == 1:
            back_edges.add((node, neighbor))
    return postorder, back_edges
def _walk_component_depths(seed, adj: dict) -> dict:
    postorder, back_edges = _depth_traversal(seed, adj)
    depths = {seed: 0}
    for node in reversed(postorder):
        depth = depths[node]
        for neighbor in _sorted_neighbors(node, adj):
            if (node, neighbor) in back_edges:
                continue
            depths[neighbor] = max(depths.get(neighbor, 0), depth + 1)
    return depths
def _merge_max_depths(all_depths: dict, depths: dict) -> None:
    for node, depth in depths.items():
        all_depths[node] = max(all_depths.get(node, 0), depth)
def _calculate_depths(
        entry_points: list, adj: dict, all_funcs: set,
) -> tuple[dict, dict]:
    all_depths: dict = {}
    entry_depths: dict = {}
    for entry in entry_points:
        depths = _walk_component_depths(entry, adj)
        entry_depths[entry] = depths
        _merge_max_depths(all_depths, depths)
    unreached = sorted(all_funcs - all_depths.keys(), key=_entry_sort_key)
    for seed in unreached:
        if seed in all_depths:
            continue
        _merge_max_depths(
            all_depths, _walk_component_depths(seed, adj))
    return all_depths, entry_depths
def _aggregate_entry_depths(entry_depths: dict) -> tuple[dict, dict]:
    entry_max_depth: dict = {}
    entry_reached: dict = {}
    for entry, depths in entry_depths.items():
        entry_max_depth[entry] = max(depths.values(), default=0)
        entry_reached[entry] = len(depths)
    return entry_max_depth, entry_reached
def _entry_label(entry) -> str:
    return str(entry).rsplit('.', 1)[-1]
def _collect_deep_chains(entry_points: list, entry_max_depth: dict,
                         entry_reached: dict) -> list:
    deep_chains = []
    for entry in entry_points:
        max_d = entry_max_depth.get(entry, 0)
        if max_d > _DEEP_CHAIN_MIN_DEPTH:
            deep_chains.append({
                "entry": _entry_label(entry),
                "depth": max_d,
                "reached": entry_reached.get(entry, 1),
            })
    return deep_chains
def _collect_shallow_chains(entry_points: list, entry_max_depth: dict) -> list:
    return [{
        "entry": _entry_label(ep),
        "depth": entry_max_depth.get(ep, 0),
    } for ep in entry_points if entry_max_depth.get(ep, 0) <= 1]
def _depth_health_score(dist) -> float:
    deep_count = sum(v for k, v in dist.items()
                     if k > _DEEP_CHAIN_MIN_DEPTH)
    total = sum(dist.values())
    return deep_count / max(total, 1)
_BLINDSPOT_ENTRY_KEYS: tuple[str, ...] = ("entries", "entry_details")
def _blindspot_entries(report: dict) -> list:
    section = section_dict(report, "blindspots", {})
    for key in _BLINDSPOT_ENTRY_KEYS:
        entries = section.get(key)
        if isinstance(entries, (list, tuple)):
            return list(entries)
    return []
def record_degradation(report: dict, step: str, label: str,
                       err: BaseException) -> None:
    logger.warning("%s: %s", label, err)
    report["errors"] = normalize_list_field(report.get("errors"))
    report["errors"].append({"step": step, "error": str(err)})
def _apply_graph_section(report: dict, step: str, label: str, key: str,
                         producer: Callable[[], Any]) -> None:
    try:
        result = producer()
    except Exception as err:  # noqa: BLE001
        log_swallowed(__name__, err, context=f'{step}:{type(err).__name__}')
        record_degradation(report, step, label, err)
        return
    report[key] = result
def _called_names_in_tree(tree: ast.Module) -> set:
    return {
        called for called in (_call_target_name(node) for node in walk_nodes(tree))
        if called
    }
def _call_target_name(node: ast.AST) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        return func.attr
    return None
def _leaf_name(func_name) -> str:
    if not isinstance(func_name, str):
        return ""
    return func_name.rsplit(".", 1)[-1]
def _load_test_file_tree(fpath: str, ctx: Any) -> ast.Module | None:
    src = read_source(fpath, ctx)
    if src is None:
        return None
    if ctx is not None and hasattr(ctx, "get_ast"):
        try:
            tree = ctx.get_ast(fpath)
        except (OSError, SyntaxError, ValueError, RecursionError,
                MemoryError):
            logger.debug(
                "[CoverageMapper] ctx AST 读取失败，回退直解析: %s", fpath)
        else:
            if tree is not None:
                return tree
    return parse_source_tree(src, fpath)
class _TestCoverageReport:
    def __init__(self, skill_dir: str):
        self.skill_dir = skill_dir
        self._coverage_pct = 0.0
        self._public_count = 0
        self._tested_funcs: set = set()
        self._untested_funcs: list = []
        self._blindspot_coverage: dict = {}
    def summary(self) -> dict:
        return {
            "coverage_pct": self._coverage_pct,
            "public_count": self._public_count,
            "tested_count": len(self._tested_funcs),
            "untested_count": len(self._untested_funcs),
            "untested_functions": self._untested_funcs[:50],
            "blindspot_coverage": self._blindspot_coverage,
        }
class TestCoverageMapper:
    def __init__(self, skill_dir: str, ctx: Any = None):
        self.skill_dir = _text_path(skill_dir)
        self._tested_names: set = self._collect_tested_names(ctx)
        logger.info(
            "[CoverageMapper] 被测函数名收集完成: %d 个（skill=%s）",
            len(self._tested_names),
            os.path.basename(os.path.normpath(self.skill_dir or os.curdir)))
    def _collect_tested_names(self, ctx: Any = None) -> set:
        tested = set()
        for fpath in _collect_test_files_for_coverage(self.skill_dir):
            try:
                tree = _load_test_file_tree(fpath, ctx)
            except (OSError, SyntaxError, ValueError, RecursionError,
                    MemoryError) as e:
                logger.warning("[CoverageMapper] 测试文件跳过: %s", e)
                continue
            if tree is None:
                continue
            tested |= _called_names_in_tree(tree)
        return tested
    def _all_public_funcs(self, graph) -> set:
        return {name for name, node in _call_graph_functions(graph).items()
                if isinstance(name, str)
                and getattr(node, "is_public", False)}
    def map_blindspots(self, graph, blindspot_entries):
        rpt = _TestCoverageReport(self.skill_dir)
        if blindspot_entries is None:
            blindspot_entries = []
        all_public_funcs = self._all_public_funcs(graph)
        rpt._public_count = len(all_public_funcs)
        leaf_totals: dict[str, int] = defaultdict(int)
        for func_name in all_public_funcs:
            leaf_totals[_leaf_name(func_name)] += 1
        unambiguous_tested = {
            leaf for leaf, total in leaf_totals.items()
            if total == 1 and leaf in self._tested_names
        }
        rpt._tested_funcs = {
            func_name for func_name in all_public_funcs
            if _leaf_name(func_name) in unambiguous_tested
        }
        rpt._untested_funcs = sorted(all_public_funcs - rpt._tested_funcs)
        if all_public_funcs:
            rpt._coverage_pct = round(len(rpt._tested_funcs) / len(all_public_funcs) * 100, 1)
        for entry in blindspot_entries:
            if isinstance(entry, dict):
                func_name = entry.get("name", entry.get("function", ""))
            else:
                func_name = getattr(entry, "name", getattr(entry, "function", ""))
            if func_name:
                leaf = _leaf_name(func_name)
                rpt._blindspot_coverage[func_name] = (
                    leaf_totals.get(leaf, 0) <= 1
                    and leaf in self._tested_names)
        logger.info(
            "[CoverageMapper] map_blindspots 完成: public=%d tested=%d "
            "untested=%d coverage=%.1f%%",
            len(all_public_funcs), len(rpt._tested_funcs),
            len(rpt._untested_funcs), rpt._coverage_pct)
        return rpt
def _supplement_test_coverage(report: dict, skill_dir: str, ctx: Any,
                              call_graph: Any) -> None:
    try:
        entries = _blindspot_entries(report)
        mapper = TestCoverageMapper(skill_dir, ctx)
        coverage_report = mapper.map_blindspots(call_graph, entries)
        summary = coverage_report.summary()
        if not summary["public_count"]:
            logger.debug(
                "[Step6.4] 调用图无公开函数，测试覆盖率不落证据（避免 0/0 冒充满分）")
            return
        report["test_coverage"] = summary
    except Exception as err:  # pragma: no cover  # noqa: BLE001
        log_swallowed(__name__, err,
                      context=f'_supplement_test_coverage:{type(err).__name__}')
        record_degradation(
            report, "test_coverage", "[Step6.4] 测试覆盖率映射失败", err)
def supplement_graph_report_dimensions(report: dict, skill_dir: str,
                                       ctx: Any, call_graph: Any) -> None:
    if not isinstance(report, dict):
        logger.warning("[Step6] report 非映射（%s），调用图维度补充跳过",
                       type(report).__name__)
        return
    if call_graph is None:
        return
    if "call_depth" not in report:
        _apply_graph_section(
            report, "call_depth", "[Step6.2] 调用链深度分析失败", "call_depth",
            lambda: analyze_call_depth(call_graph))
    if "test_coverage" not in report:
        _supplement_test_coverage(report, skill_dir, ctx, call_graph)
def _docstring_line_rows(tree: ast.AST) -> set[int]:
    rows: set[int] = set()
    doc_owners = (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)
    for node in walk_nodes(tree):
        if not isinstance(node, doc_owners):
            continue
        body = getattr(node, "body", None)
        if not body:
            continue
        first = body[0]
        if not isinstance(first, ast.Expr):
            continue
        value = first.value
        if not (isinstance(value, ast.Constant) and isinstance(value.value, str)):
            continue
        start = getattr(value, "lineno", None)
        if start is None:
            continue
        end = getattr(value, "end_lineno", None) or start
        rows.update(range(start, max(start, end) + 1))
    return rows
def _comment_line_rows(src: str) -> set[int]:
    rows: set[int] = set()
    try:
        tree = ast.parse(src)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_comment_line_rows:{type(_swallowed_exc).__name__}')
        tree = None
    if tree is not None:
        rows |= _docstring_line_rows(tree)
    try:
        for token in tokenize.generate_tokens(io.StringIO(src).readline):
            if token.type == tokenize.COMMENT:
                rows.add(token.start[0])
    except (tokenize.TokenError, IndentationError, SyntaxError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_comment_line_rows:{type(_swallowed_exc).__name__}')
    if tree is None:
        for lineno, line in enumerate(src.splitlines(), start=1):
            if line.strip().startswith(("#", '"""', "'''")):
                rows.add(lineno)
    return rows
COMMENT_RATIO_LINE_BUDGET = 20000
_COMMENT_RATIO_FILE_LIMIT = 200
def _comment_ratio_files(skill_dir: str, ctx: Any = None) -> list[str]:
    if ctx is not None and hasattr(ctx, 'py_files'):
        paths: list[str] = []
        skipped = 0
        for raw in normalize_list_field(ctx.py_files):
            try:
                paths.append(resolve_project_path(os.fspath(raw), skill_dir))
            except (TypeError, ValueError, OSError):
                skipped += 1
        if skipped:
            logger.debug("[comment_ratio] 跳过 %d 个非路径条目", skipped)
    else:
        paths = list(iter_py_files_under(skill_dir))
    return sorted(paths)[:_COMMENT_RATIO_FILE_LIMIT]
def compute_comment_ratio(skill_dir: str, ctx: Any = None) -> float:
    comment_lines = 0
    total_lines = 0
    try:
        py_files = _comment_ratio_files(_text_path(skill_dir), ctx)
    except (OSError, ValueError) as exc:
        logger.debug("comment_ratio 枚举失败，按零样本计: %s", exc)
        py_files = []
    for fpath in py_files:
        if total_lines >= COMMENT_RATIO_LINE_BUDGET:
            break
        try:
            src = read_source(fpath, ctx)
        except (OSError, ValueError) as exc:
            logger.debug("comment_ratio 跳过不可读文件 %s: %s", fpath, exc)
            continue
        if not src:
            continue
        source_line_count = len(src.splitlines())
        sampled_line_count = min(
            source_line_count, COMMENT_RATIO_LINE_BUDGET - total_lines)
        total_lines += sampled_line_count
        comment_lines += sum(
            1 for row in _comment_line_rows(src)
            if row <= sampled_line_count)
    return comment_lines / max(total_lines, 1)
def _read_json_file(path: str, default, label: str, *,
                    on_io_error: Callable[[OSError], None] | None = None,
                    on_content_error: Callable[[ValueError], None] | None = None):
    if not os.path.isfile(path):
        return default
    try:
        data, status, error = read_json_artifact(path, propagate_io=True)
    except OSError as exc:
        log_swallowed(__name__, exc,
                      context=f'_read_json_file:{label}:OSError')
        if on_io_error is not None:
            on_io_error(exc)
        return default
    if status == "missing":
        return default
    if status != "ok":
        logger.warning("[%s] 内容损坏（%s），按默认值降级且禁止覆盖: %s",
                       label, error, path)
        if on_content_error is not None:
            on_content_error(ValueError(error or status))
        return default
    return data
def _write_json_file(path: str, payload) -> Exception | None:
    try:
        parent = os.path.dirname(path)
        if parent:
            os.makedirs(parent, exist_ok=True)
        write_json_artifact(path, payload, indent=2)
    except (OSError, TypeError, ValueError, RecursionError) as e:
        log_swallowed(__name__, e,
                      context=f'_write_json_file:{type(e).__name__}')
        return e
    return None
def _coerce_num(val, default, context: str) -> float | None:
    if val is None or isinstance(val, bool):
        return default
    try:
        num = float(val)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context=f'{context}:{type(_e).__name__}')
        return default
    if not math.isfinite(num):
        log_swallowed(__name__, ValueError(f'非有限数值: {val!r}'),
                      context=f'{context}:NonFinite')
        return default
    return num
_DEFAULT_METRIC_VALUE = 0.0
def _ex_num(section, key, default=_DEFAULT_METRIC_VALUE) -> float:
    if not isinstance(section, dict):
        return default
    return _coerce_num(section.get(key), default, '_ex_num')
def _ex_safe_count(val, default=_DEFAULT_METRIC_VALUE) -> float:
    if isinstance(val, (list, tuple, set)):
        return float(len(val))
    if isinstance(val, dict):
        return default
    return _coerce_num(val, default, '_ex_safe_count')
def blindspot_total(blindspots: Any, default: int | None = 0) -> int | None:
    if not isinstance(blindspots, dict):
        return default
    for key in ("total", FIELD_TOTAL_BLINDSPOTS):
        value = blindspots.get(key)
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            normalized = int_metric(value, -1)
            if normalized >= 0:
                return normalized
    return default
DELTA_PCT_MODERATE: float = 30.0
DELTA_PCT_WARN: float = 20.0
DELTA_PCT_CRITICAL: float = 50.0
SUB_METRICS: dict[str, dict] = {
    'health_score': {'direction': 'higher_better'},
    FIELD_TOTAL_FUNCTIONS: {'direction': 'neutral'},
    'break_points': {'direction': 'lower_better'},
    'orphans': {'direction': 'lower_better'},
    'blindspots': {'direction': 'lower_better'},
    'syntax_errors': {'direction': 'lower_better'},
    'circular_deps': {'direction': 'lower_better'},
    'isolated_modules': {'direction': 'lower_better'},
    'small_files': {'direction': 'lower_better'},
    'test_coverage_pct': {'direction': 'higher_better'},
    'liveness_rate': {'direction': 'higher_better'},
    'max_call_depth': {'direction': 'lower_better'},
    'cross_skill_consumers': {'direction': 'neutral'},
    'static_precision': {'direction': 'higher_better'},
}
@dataclass
class TrendPoint:
    timestamp: str
    health_score: float
    break_points: float | None = None
    orphans: float | None = None
    blindspots: float | None = None
    status: str = "N/A"
    health_score_known: bool = True
@dataclass
class MetricDelta:
    metric: str
    current: float
    previous: float
    delta: float
    delta_pct: float
    direction: str
    severity: str
    message: str
    quantifiable: bool = True
@dataclass
class BaselineReport:
    skill_name: str
    current_score: float | None
    previous_score: float | None
    score_delta: float
    deltas: list[MetricDelta] = field(default_factory=list)
    trends: list[TrendPoint] = field(default_factory=list)
    regressions: list[MetricDelta] = field(default_factory=list)
    improvements: list[MetricDelta] = field(default_factory=list)
    trend_direction: str = "stable"
    recommendations: list[str] = field(default_factory=list)
    previous_status: str = "N/A"
    def summary(self) -> dict:
        try:
            return {
                "current_score": self.current_score,
                "previous_score": self.previous_score,
                "score_delta": self.score_delta,
                "trend_direction": self.trend_direction,
                "regression_count": len(self.regressions),
                "improvement_count": len(self.improvements),
                "regressions": [
                    {"metric": r.metric, "delta": r.delta, "severity": r.severity}
                    for r in self.regressions
                ],
                "improvements": [
                    {"metric": i.metric, "delta": i.delta, "severity": i.severity}
                    for i in self.improvements
                ],
                FIELD_RECOMMENDATIONS: self.recommendations,
            }
        except Exception as e:
            logger.warning("[baseline] summary 构建失败（部分降级）: %s", e, exc_info=True)
            return {"_error": True, "_partial": True}
def _report_metrics(report: dict) -> dict[str, float | None]:
    metrics = _top_metric_values(
        report, section_dict(report, "call_chain", {}))
    metrics.update(_section_metric_values(report))
    return metrics
def _health_score_or_none(data: object) -> float | None:
    return _ex_num(data, "health_score", None)
def _history_timestamp(baseline_data: dict) -> str:
    ts = baseline_data.get("timestamp") if isinstance(baseline_data, dict) else None
    return ts if isinstance(ts, str) and ts else timestamp_human()
def _first_metric(data: dict, cc: dict, key: str):
    value = data.get(key)
    if value is not None:
        return value
    return cc.get(key)
def _top_metric_values(data: dict, cc: dict) -> dict:
    if not isinstance(data, dict):
        data = {}
    if not isinstance(cc, dict):
        cc = {}
    metrics = {}
    metrics["health_score"] = _ex_num(data, "health_score", None)
    metrics[FIELD_TOTAL_FUNCTIONS] = _ex_num(
        data, FIELD_TOTAL_FUNCTIONS,
        _ex_num(cc, FIELD_TOTAL_FUNCTIONS, None))
    metrics["break_points"] = _ex_safe_count(
        _first_metric(data, cc, "break_points"), None)
    metrics["orphans"] = _ex_safe_count(
        _first_metric(data, cc, "orphans"), None)
    bs = data.get("blindspots")
    if isinstance(bs, dict):
        metrics["blindspots"] = blindspot_total(bs, None)
    else:
        metrics["blindspots"] = _ex_safe_count(bs, None)
    metrics["syntax_errors"] = _ex_safe_count(
        _first_metric(data, cc, "syntax_errors"), None)
    return metrics
def _liveness_metric(bf: object) -> float | None:
    lr = bf.get("liveness_rate") if isinstance(bf, dict) else None
    rate = _coerce_num(lr, None, '_liveness_metric')
    if rate is None:
        return None
    return rate * PERCENT_FACTOR if 0 <= rate <= 1 else rate
def _section_num(data: dict, section_name: str, key: str) -> float | None:
    section = data.get(section_name)
    if not isinstance(section, dict):
        return None
    return _coerce_num(
        section.get(key), None, f'_section_num:{section_name}.{key}')
def _section_count(data: dict, section_name: str, key: str) -> float | None:
    section = data.get(section_name)
    if not isinstance(section, dict) or key not in section:
        return None
    return _ex_safe_count(section[key], None)
def _cv_precision_num(data: dict, key: str) -> float | None:
    cv = data.get(CAT_CROSS_VALIDATION)
    precision = cv.get("precision_metrics") if isinstance(cv, dict) else None
    if not isinstance(precision, dict):
        return None
    return _coerce_num(
        precision.get(key), None, f'_cv_precision_num:{key}')
_CALL_DEPTH_MEASURED_DEFAULT = True
def _call_depth_measured(call_depth: dict) -> bool:
    return signal_bool(call_depth.get(
        "measured", _CALL_DEPTH_MEASURED_DEFAULT))
def _section_metric_values(data: dict) -> dict:
    call_depth = section_dict(data, "call_depth", {})
    max_call_depth = (
        _coerce_num(
            call_depth.get("max_depth"), None,
            '_section_metric_values:max_call_depth')
        if _call_depth_measured(call_depth) else None)
    return {
        "circular_deps": _section_count(data, "module_coupling", "cycles"),
        "isolated_modules": _section_count(data, "module_coupling", "isolated_modules"),
        "small_files": _section_count(data, "fragmentation", "small_files"),
        "test_coverage_pct": _section_num(data, "test_coverage", "coverage_pct"),
        "liveness_rate": _liveness_metric(data.get("business_flows")),
        "max_call_depth": max_call_depth,
        "cross_skill_consumers": _section_num(
            data, "cross_skill_imports", "consumer_count"),
        "static_precision": _cv_precision_num(data, "static_precision"),
    }
TREND_WINDOW = 5
class BaselineManager:
    MAX_HISTORY = 20
    def __init__(self, skill_dir: str, data_dir: str | None = None) -> None:
        skill_dir_text = _text_path(skill_dir)
        if not skill_dir_text.strip():
            raise ValueError("skill_dir 不能为空或纯空白")
        self.skill_dir = os.path.abspath(skill_dir_text)
        self.skill_name = os.path.basename(self.skill_dir)
        data_dir_text = _text_path(data_dir)
        self.data_dir = data_dir_text or baseline_data_dir(self.skill_dir)
        self.baseline_path = os.path.join(self.data_dir, ".jws_baseline.json")
        self.history_path = os.path.join(self.data_dir,
                                         "_baseline_history.json")
        self._io_failures: dict[str, OSError] = {}
        self._content_failures: dict[str, ValueError] = {}
    def _read_ledger(self, path: str, default, label: str):
        key = os.path.normcase(os.path.abspath(path))
        failures: list[OSError] = []
        content_failures: list[ValueError] = []
        data = _read_json_file(path, default, label,
                               on_io_error=failures.append,
                               on_content_error=content_failures.append)
        expected = type(default) if isinstance(default, (dict, list)) else None
        if (not content_failures and expected is not None
                and not isinstance(data, expected)):
            content_failures.append(ValueError(
                f"顶层类型为 {type(data).__name__}，期望 {expected.__name__}"))
        if content_failures:
            self._content_failures[key] = content_failures[0]
        else:
            self._content_failures.pop(key, None)
        if failures:
            self._io_failures[key] = failures[0]
        else:
            self._io_failures.pop(key, None)
        return data
    def _write_allowed(self, path: str, label: str) -> bool:
        key = os.path.normcase(os.path.abspath(path))
        if key in self._content_failures:
            if not os.path.exists(path):
                self._content_failures.pop(key, None)
            else:
                logger.warning(
                    "[%s] 台账内容损坏或顶层类型非法，拒绝覆盖原始证据: %s: %s",
                    label, path, self._content_failures[key])
                return False
        if key not in self._io_failures:
            return True
        try:
            with open(path, "r", encoding="utf-8-sig"):
                pass
        except FileNotFoundError:
            self._io_failures.pop(key, None)
            return True
        except OSError as exc:
            logger.warning(
                "[%s] 台账当前不可读，拒绝覆盖写盘（避免整份丢失）: %s: %s",
                label, path, exc)
            return False
        self._io_failures.pop(key, None)
        return True
    def load(self) -> dict:
        data = self._read_ledger(self.baseline_path, {}, "BaselineManager")
        if not isinstance(data, dict):
            logger.warning(
                "[BaselineManager] 基线顶层非映射（%s），按空基线处理: %s",
                type(data).__name__, self.baseline_path)
            return {}
        return data
    def save(self, baseline_data: dict) -> bool:
        if not isinstance(baseline_data, dict):
            logger.warning("[BaselineManager] baseline_data 非 dict（%s），拒绝保存",
                           type(baseline_data).__name__)
            return False
        # save() may be the first operation; refresh ledger health before overwriting.
        self._read_ledger(self.baseline_path, {}, "BaselineManager")
        if not self._write_allowed(self.baseline_path, "BaselineManager"):
            return False
        error = _write_json_file(self.baseline_path, baseline_data)
        if error is not None:
            logger.debug("[BaselineManager] 基线保存失败（返回 False 由调用方降级）: %s", error)
            return False
        try:
            self._append_history(baseline_data)
        except (OSError, TypeError, ValueError, RecursionError) as exc:
            logger.warning("历史快照追加失败，不影响基线保存: %s", exc)
        return True
    def _read_history_raw(self) -> list:
        raw = self._read_ledger(self.history_path, [], "BaselineManager")
        if isinstance(raw, list):
            return raw
        logger.warning(
            "[BaselineManager] 历史台账顶层非列表（%s），按空历史处理: %s",
            type(raw).__name__, self.history_path)
        return []
    def _append_history(self, baseline_data: dict) -> None:
        health_score = _health_score_or_none(baseline_data)
        if health_score is None:
            logger.debug("[BaselineManager] 本轮无健康分，趋势快照跳过")
            return
        with locked_artifact(self.history_path) as locked:
            if not locked:
                raise OSError(f"历史台账写锁不可用: {self.history_path}")
            history = self._read_history_raw()
            history_key = os.path.normcase(os.path.abspath(self.history_path))
            reload_history = history_key in self._io_failures
            if not self._write_allowed(self.history_path, "BaselineManager"):
                logger.warning(
                    "[BaselineManager] 历史台账当前不可读，跳过本轮快照追加: %s",
                    self.history_path)
                return
            if reload_history:
                history = self._read_history_raw()
                if history_key in self._io_failures:
                    logger.warning(
                        "[BaselineManager] 历史台账恢复后重读仍失败，跳过本轮快照追加: %s",
                        self.history_path)
                    return
            os.makedirs(self.data_dir, exist_ok=True)
            cc = baseline_data.get("call_chain")
            if not isinstance(cc, dict):
                cc = {}
            metrics = _top_metric_values(baseline_data, cc)
            snapshot = {
                "timestamp": _history_timestamp(baseline_data),
                "health_score": health_score,
                "break_points": metrics["break_points"],
                "orphans": metrics["orphans"],
                "blindspots": metrics["blindspots"],
                "status": baseline_data.get("status") or "N/A",
            }
            history.append(snapshot)
            if len(history) > self.MAX_HISTORY:
                history = history[-self.MAX_HISTORY:]
            error = _write_json_file(self.history_path, history)
            if error is not None:
                raise error
    @staticmethod
    def _trend_num(payload: dict, key: str, default=None):
        return _coerce_num(payload.get(key), default, '_trend_num')
    def load_history(self) -> list[TrendPoint]:
        return [
            TrendPoint(
                timestamp=p.get("timestamp", ""),
                health_score=self._trend_num(
                    p, "health_score", _DEFAULT_METRIC_VALUE),
                break_points=self._trend_num(p, "break_points"),
                orphans=self._trend_num(p, "orphans"),
                blindspots=self._trend_num(p, "blindspots"),
                status=p.get("status") or "N/A",
                health_score_known=_health_score_or_none(p) is not None,
            )
            for p in self._read_history_raw()
            if isinstance(p, dict)
        ]
    def diff(self, current_report: dict) -> BaselineReport:
        previous = self.load()
        current_score, previous_score = _score_pair(current_report, previous)
        score_delta = (
            current_score - previous_score
            if current_score is not None and previous_score is not None
            else 0.0)
        report = BaselineReport(
            skill_name=self.skill_name,
            current_score=current_score,
            previous_score=previous_score,
            score_delta=score_delta,
            previous_status=_baseline_status(previous),
        )
        if previous:
            self._diff_metrics(current_report, previous, report)
        trends = self.load_history()
        current_point = _current_trend_point(current_report, current_score)
        if current_point is not None and (trends or previous_score is not None):
            trends = [*trends, current_point]
        report.trends = trends
        report.trend_direction = self._trend_direction(trends, score_delta)
        self._generate_recommendations(report)
        return report
    def _diff_metrics(self, current_report: dict, previous: dict,
                      report: BaselineReport) -> None:
        current_metrics = _report_metrics(current_report)
        previous_metrics = _report_metrics(previous)
        for metric, config in SUB_METRICS.items():
            md = self._build_metric_delta(
                metric, config,
                current_metrics.get(metric), previous_metrics.get(metric),
            )
            if md is None:
                continue
            report.deltas.append(md)
            if md.direction == "worsened" and md.severity in ("warn", "critical"):
                report.regressions.append(md)
            elif md.direction == "improved":
                report.improvements.append(md)
    def _build_metric_delta(self, metric: str, config: dict,
                            curr: float | None,
                            prev: float | None) -> MetricDelta | None:
        if curr is None or prev is None or curr == prev:
            return None
        delta = curr - prev
        base = abs(prev)
        quantifiable = base > 0
        delta_pct = (delta / base if quantifiable else delta) * PERCENT_FACTOR
        direction, severity, message = self._classify_delta(
            metric, config, curr, prev, delta, delta_pct,
            quantifiable=quantifiable,
        )
        return MetricDelta(
            metric=metric,
            current=curr,
            previous=prev,
            delta=delta,
            delta_pct=round(delta_pct, 1),
            direction=direction,
            severity=severity,
            message=message,
            quantifiable=quantifiable,
        )
    def _classify_delta(
        self, metric: str, config: dict,
        curr: float, prev: float, delta: float, delta_pct: float,
        *, quantifiable: bool = True,
    ) -> tuple[str, str, str]:
        direction = config.get("direction", "neutral")
        unchanged = ("unchanged", "info", f"{metric}: {prev} -> {curr}")
        if direction == "neutral" or delta == 0:
            return unchanged
        if direction not in ("lower_better", "higher_better"):
            return unchanged
        abs_delta_pct = abs(delta_pct)
        improved = delta < 0 if direction == "lower_better" else delta > 0
        scale = f"{delta_pct:+.1f}%" if quantifiable else f"{delta:+g}"
        if improved:
            severity = ("warn" if quantifiable
                        and abs_delta_pct > DELTA_PCT_MODERATE else "info")
            return ("improved", severity,
                    f"{metric}: {prev} -> {curr} ({scale})")
        severity = ("warn" if not quantifiable
                    else self._regression_severity(abs_delta_pct))
        note = "" if quantifiable else " (previous=0, 增幅不可量化)"
        return ("worsened", severity,
                f"{metric}: {prev} -> {curr} ({scale}){note} - regression")
    @staticmethod
    def _regression_severity(abs_delta_pct: float) -> str:
        if abs_delta_pct > DELTA_PCT_CRITICAL:
            return "critical"
        return "warn" if abs_delta_pct > DELTA_PCT_WARN else "info"
    def _analyze_trend(self, trends: list[TrendPoint]) -> str:
        scores = [t.health_score
                  for t in _usable_trend_points(trends)[-TREND_WINDOW:]]
        if len(scores) < 3:
            return "stable"
        return self._score_trend(scores)
    @staticmethod
    def _score_trend(scores: list[float]) -> str:
        deltas = [b - a for a, b in pairwise(scores)]
        if min(deltas) >= 0 and scores[-1] > scores[0] + 2:
            return "improving"
        if max(deltas) <= 0 and scores[-1] < scores[0] - 2:
            return "worsening"
        return "stable"
    def _trend_direction(self, trends: list, score_delta: float) -> str:
        usable = _usable_trend_points(trends)
        if len(usable) >= 3:
            return self._analyze_trend(trends)
        if usable:
            if score_delta > 2:
                return "improving"
            if score_delta < -2:
                return "worsening"
            return "stable"
        return "initial" if not trends else "stable"
    def _generate_recommendations(self, report: BaselineReport):
        report.recommendations.extend(_regression_recommendations(report))
        trend_note = _trend_recommendation(report)
        if trend_note:
            report.recommendations.append(trend_note)
        has_worsened = any(d.direction == "worsened" for d in report.deltas)
        if report.improvements and not has_worsened:
            report.recommendations.append("所有指标均无回归，质量稳定")
def _regression_recommendations(report: BaselineReport) -> list[str]:
    if not report.regressions:
        return []
    messages = [
        (f"检测到 {len(report.regressions)} 项回归: "
         f"{', '.join(r.metric for r in report.regressions)}")
    ]
    critical = [r for r in report.regressions if r.severity == "critical"]
    if critical:
        messages.append(
            f"严重回归: {', '.join(r.metric for r in critical)}，需立即处理")
    return messages
def _current_trend_point(current_report: dict,
                         current_score: float) -> TrendPoint | None:
    if _health_score_or_none(current_report) is None:
        return None
    metrics = _top_metric_values(
        current_report, section_dict(current_report, "call_chain", {}))
    return TrendPoint(
        timestamp=timestamp_human(),
        health_score=current_score,
        break_points=metrics["break_points"],
        orphans=metrics["orphans"],
        blindspots=metrics["blindspots"],
        status=current_report.get("status") or "N/A",
    )
def _baseline_status(previous: dict) -> str:
    status = previous.get("status") if isinstance(previous, dict) else None
    return status if isinstance(status, str) and status else "N/A"
def _score_pair(current_report: dict, previous: dict
                ) -> tuple[float | None, float | None]:
    return (_health_score_or_none(current_report),
            _health_score_or_none(previous))
def _usable_trend_points(trends) -> list:
    if not isinstance(trends, list):
        return []
    return [t for t in trends if getattr(t, "health_score_known", True)]
def _trend_recommendation(report: BaselineReport) -> str | None:
    score_text = "N/A" if report.current_score is None else f"{report.current_score}"
    if report.trend_direction == "worsening":
        return (f"健康评分持续下降趋势（{score_text}），"
                "建议审查近期变更")
    if report.trend_direction == "improving":
        return f"健康评分持续改善（{score_text}），趋势良好"
    return None
def _baseline_section(baseline_report: Any, ts: str) -> dict:
    return {
        "previous_score": baseline_report.previous_score,
        "current_score": baseline_report.current_score,
        "delta": baseline_report.score_delta,
        "previous_status": baseline_report.previous_status,
        "timestamp": ts,
        "sub_metric_deltas": [
            {
                "metric": d.metric,
                "current": d.current,
                "previous": d.previous,
                "delta": d.delta,
                "delta_pct": d.delta_pct,
                "direction": d.direction,
                "severity": d.severity,
                "message": d.message,
                "quantifiable": d.quantifiable,
            }
            for d in baseline_report.deltas
        ],
        "trend_direction": baseline_report.trend_direction,
        "trend_points": len(baseline_report.trends),
        "regression_count": len(baseline_report.regressions),
        "regressions": [
            {"metric": r.metric, "delta": r.delta, "severity": r.severity}
            for r in baseline_report.regressions
        ],
    }
_BASELINE_SECTION_PROJECTIONS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("module_coupling", ("cycles", "isolated_modules")),
    ("fragmentation", ("small_files",)),
    ("test_coverage", ("coverage_pct",)),
    ("call_depth", ("max_depth", "measured")),
    ("cross_skill_imports", ("consumer_count",)),
    ("business_flows", ("liveness_rate",)),
)
def _project_baseline_sections(report: dict) -> dict:
    projected: dict = {}
    for _section, _keys in _BASELINE_SECTION_PROJECTIONS:
        _data = report.get(_section)
        if isinstance(_data, dict):
            values = {k: _data.get(k) for k in _keys}
            if _section == "call_depth":
                values["measured"] = _call_depth_measured(_data)
            projected[_section] = values
    _cv = report.get(CAT_CROSS_VALIDATION)
    if isinstance(_cv, dict):
        _pm = _cv.get("precision_metrics")
        if isinstance(_pm, dict):
            projected[CAT_CROSS_VALIDATION] = {
                "precision_metrics": {
                    "static_precision": _pm.get("static_precision")}}
    return projected
def _append_baseline_judgments(report: dict, baseline_report: Any) -> None:
    if baseline_report.regressions:
        reg_summary = ", ".join(
            (f"{r.metric}({r.delta_pct:+.1f}%)" if r.quantifiable
             else f"{r.metric}({r.delta:+g})")
            for r in baseline_report.regressions
        )
        append_judgment(
            report, "baseline_regression",
            "fail" if any(r.severity == "critical" for r in baseline_report.regressions) else "warn",
            f"Baseline regression: {len(baseline_report.regressions)} metrics worsened ({reg_summary})",
        )
    elif baseline_report.improvements:
        append_judgment(
            report, "baseline_improvement", "pass",
            f"Baseline improved: {len(baseline_report.improvements)} metrics better than previous",
        )
    trend_status = {
        "worsening": "warn",
        "improving": "pass",
    }.get(baseline_report.trend_direction)
    if trend_status:
        append_judgment(
            report, "baseline_trend", trend_status,
            f"Health trend: {baseline_report.trend_direction} over last "
            f"{min(len(_usable_trend_points(baseline_report.trends)), TREND_WINDOW)} snapshots",
        )
    for rec in baseline_report.recommendations:
        append_recommendation_once(report, rec)
def _baseline_snapshot_payload(report: dict, ts: str) -> dict:
    metrics = _report_metrics(report)
    return {
        "health_score": _health_score_or_none(report),
        "status": report.get("status") or "N/A",
        "timestamp": ts,
        FIELD_TOTAL_FUNCTIONS: metrics[FIELD_TOTAL_FUNCTIONS],
        "break_points": metrics["break_points"],
        "orphans": metrics["orphans"],
        "blindspots": metrics["blindspots"],
        "syntax_errors": metrics["syntax_errors"],
        **_project_baseline_sections(report),
    }
def _carry_forward_unmeasured(previous: Any, current: Any) -> Any:
    if current is None:
        return previous
    if not isinstance(current, dict):
        return current
    old = previous if isinstance(previous, dict) else {}
    merged = dict(current)
    for key, old_value in old.items():
        if key not in merged:
            merged[key] = old_value
        else:
            merged[key] = _carry_forward_unmeasured(old_value, merged[key])
    return merged
def _baseline_snapshot_with_carry_forward(previous: dict, current: dict) -> dict:
    merged = _carry_forward_unmeasured(previous, current)
    current_depth = current.get("call_depth")
    previous_depth = previous.get("call_depth")
    if (isinstance(current_depth, dict)
            and not _call_depth_measured(current_depth)
            and isinstance(previous_depth, dict)
            and _call_depth_measured(previous_depth)
            and _coerce_num(previous_depth.get("max_depth"), None,
                            '_baseline_snapshot_with_carry_forward') is not None):
        merged["call_depth"] = dict(previous_depth)
    return merged
def _save_baseline_snapshot(bm: Any, report: dict, ts: str) -> None:
    if _health_score_or_none(report) is None:
        logger.debug("[baseline] 本轮无健康分，保留上一实测基线且不落趋势点")
        return
    try:
        payload = _baseline_snapshot_with_carry_forward(
            bm.load(), _baseline_snapshot_payload(report, ts))
        saved = bm.save(payload)
    except Exception as e:  # noqa: BLE001
        record_degradation(report, "baseline", "[baseline] 基线快照保存失败", e)
        return
    if saved is False:
        record_degradation(
            report, "baseline", "[baseline] 基线快照保存被拒",
            RuntimeError("基线快照保存返回 False，趋势追踪将缺失本轮基线"))
def apply_baseline_comparison(skill_dir: str, report: dict, data_dir: str | None = None) -> None:
    if not isinstance(report, dict):
        logger.warning("[baseline] report 非映射（%s），基线比较跳过",
                       type(report).__name__)
        return
    try:
        bm = BaselineManager(skill_dir, data_dir=data_dir)
        baseline_report = bm.diff(report)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e,
                      context=f'apply_baseline_comparison:{type(e).__name__}')
        record_degradation(report, "baseline", "[baseline] 基线处理失败", e)
        return
    ts_text = timestamp_human()
    report["baseline"] = _baseline_section(baseline_report, ts_text)
    _append_baseline_judgments(report, baseline_report)
    _save_baseline_snapshot(bm, report, ts_text)

from __future__ import annotations

import ast
import difflib
import io
import json
import logging
import os
import posixpath
import re
import time
import tokenize
from dataclasses import dataclass, field
from datetime import datetime
from functools import cached_property
from typing import Any

from jwsgj.diag_shared_ast_surface import replay_export_surface
from jwsgj.diag_shared_source_core import (
    ast_split_lines,
    count_lines,
    read_source_strict,
    read_source_with_fingerprint,
)
from jwsgj.diag_testing_source import (
    FileCache,
    collect_function_behavior_metrics,
    is_transient_io_error,
    iter_module_level_stmts,
    qualified_name,
)
from jwsgj.diag_types_defs import (
    TestMethodResult,
)
from jwsgj.diag_types_normalize import (
    dict_or_empty,
    finite_float_or_none,
    is_number,
    normalize_passed,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    collect_migration_py_files,
    detect_cycles,
    is_backup_like_dir,
    is_temp_artifact_dir,
    iter_py_source_files,
)
from jwsgj.shared_cache_store import (
    _T5BaselinePersistenceError,
    load_t5_baseline,
    save_t5_baseline,
    t5_baseline_path,
)

_log = logging.getLogger(__name__)
def _path_arg(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, os.PathLike):
        path = os.fspath(value)
        return path if isinstance(path, str) else ""
    return ""
def _declared_all_names(tree: ast.Module) -> frozenset[str] | None:
    replay = replay_export_surface(tree)
    if not replay.declared or replay.computed:
        return None
    return frozenset(replay.names)
def _assignment_binding_names(node: ast.Assign | ast.AnnAssign) -> list[str]:
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return []
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    names: list[str] = []
    pending = list(targets)
    while pending:
        target = pending.pop(0)
        if isinstance(target, ast.Name):
            names.append(target.id)
        elif isinstance(target, ast.Starred):
            pending[0:0] = [target.value]
        elif isinstance(target, (ast.Tuple, ast.List)):
            pending[0:0] = target.elts
    return names
def _public_binding_names(node: ast.AST,
                          declared: frozenset[str] | None) -> list[str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        candidates = [node.name]
    elif isinstance(node, ast.ImportFrom):
        if node.level == 0 and node.module == "__future__":
            return []
        candidates = [alias.asname or alias.name for alias in node.names
                      if alias.name != "*"]
    elif isinstance(node, ast.Import):
        candidates = [alias.asname or alias.name.split(".", 1)[0]
                      for alias in node.names]
    elif isinstance(node, (ast.Assign, ast.AnnAssign)):
        candidates = _assignment_binding_names(node)
    else:
        return []
    if declared is not None:
        return [name for name in candidates if name in declared]
    return [name for name in candidates if not name.startswith("_")]
def extract_public_names(code: str, fpath: str = "") -> list[str]:
    try:
        tree = ast.parse(code)
    except PARSE_DEGRADE_EXC:
        _log.debug("公开符号提取跳过不可解析文件: %s", fpath, exc_info=True)
        return []
    declared = _declared_all_names(tree)
    names = (
        name for node in iter_module_level_stmts(tree.body)
        for name in _public_binding_names(node, declared)
    )
    return list(dict.fromkeys(names))
__all__ = [
    'API_RETENTION_FLOOR',
    'COPY_SUSPECT_MIN_LINES',
    'COPY_SUSPECT_SIMILARITY',
    'DEFAULT_GUARD_STAGE',
    'SKELETON_STUB_RATIO',
    'BaselineSnapshot',
    'GrowthDelta',
    'GrowthReport',
    'HonestProgressReport',
    'IntegrityResult',
    'analyze_growth',
    'assess_honest_progress',
    'check_lazy_loading',
    'check_version_uniformity',
    'collect_py_source_files',
    'compare_file_integrity',
    'count_import_cycles',
    'count_meaningful_stmts',
    'extract_public_names',
    'format_guard_report',
    'run_guard',
    'run_regression_tests',
]
_log.info("refactor_post_validation 已加载: %d 项导出", len(__all__))
def _dict_section(container, key: str) -> dict:
    return dict_or_empty(dict_or_empty(container).get(key))
def _field(container, key: str, default=None):
    return dict_or_empty(container).get(key, default)
_BASELINE_SCHEMA = 5
_SEVERITY_WEIGHTS = {'critical': 25, 'high': 15, 'medium': 8, 'low': 3}
_DEFAULT_SEVERITY_WEIGHT = _SEVERITY_WEIGHTS['low']
_RISK_SCORE_CAP = 100
def _compute_health_delta(prev_score, current_score) -> int | float | None:
    if is_number(prev_score) and is_number(current_score):
        return current_score - prev_score
    return None
_STRING_CONTAINER_TYPES = (list, set, frozenset, tuple)
def _normalize_string_set(value) -> frozenset | None:
    if not isinstance(value, _STRING_CONTAINER_TYPES):
        return None
    normalized = frozenset(item for item in value if isinstance(item, str))
    return normalized if normalized or not value else None
def _api_key_path(rel_path) -> str:
    return str(rel_path).replace("\\", "/")
def _normalize_api_key_set(value) -> frozenset | None:
    keys = _normalize_string_set(value)
    if keys is None:
        return None
    return frozenset(_api_key_path(key) for key in keys)
def _check_metric_regressions(baseline: dict, report: dict) -> list:
    prev_score = baseline.get("previous_score")
    current_score = _field(report, "health_score")
    delta = _compute_health_delta(prev_score, current_score)
    regressions = _score_regressions(prev_score, current_score, delta)
    cc = _dict_section(report, "call_chain")
    bl = _dict_section(report, "blindspots")
    regressions.extend(_count_metric_regressions(baseline, cc, bl))
    regressions.extend(_syntax_error_regression(cc))
    return regressions
def _score_regressions(prev_score, current_score, delta) -> list:
    if delta is None:
        return []
    if delta < -5:
        return [{
            "type": "score_regression", "severity": "high",
            "message": f"健康评分回归: {prev_score} → {current_score} (Δ{delta})",
        }]
    if delta < 0:
        return [{
            "type": "score_regression", "severity": "low",
            "message": f"健康评分小幅下降: {prev_score} → {current_score} (Δ{delta})",
        }]
    return []
def _count_metric_regressions(baseline: dict, cc: dict, bl: dict) -> list:
    return _count_delta_regressions([
        (baseline.get("break_points"), cc.get("break_points", 0),
         "breakpoint_increase", "medium",
         lambda p, c: f"断裂点增加: {p} → {c}", False),
        (baseline.get("orphans"), cc.get("orphans", 0),
         "orphan_increase", "medium",
         lambda p, c: f"孤立函数增加: {p} → {c}", False),
        (baseline.get("blindspots"), bl.get("total", 0),
         "blindspot_increase", "medium",
         lambda p, c: f"盲区增加: {p} → {c}", False),
    ])
def _syntax_error_regression(cc: dict) -> list:
    syntax_errors = cc.get("syntax_errors", 0)
    if is_number(syntax_errors) and syntax_errors > 0:
        return [{
            "type": "syntax_error", "severity": "critical",
            "message": f"存在 {syntax_errors} 个语法错误",
        }]
    return []
def _report_dead_code(report: dict | None) -> int | float | None:
    if not isinstance(report, dict):
        return None
    cv_root = report.get(CAT_CROSS_VALIDATION)
    if isinstance(cv_root, dict):
        metrics = cv_root.get("precision_metrics")
        if isinstance(metrics, dict) and is_number(
                metrics.get("confirmed_dead")):
            return metrics["confirmed_dead"]
        if is_number(cv_root.get("confirmed_dead")):
            return cv_root["confirmed_dead"]
    blindspots = report.get("blindspots")
    nested = blindspots.get("metrics") if isinstance(blindspots, dict) else None
    nested_cv = (nested.get(CAT_CROSS_VALIDATION)
                 if isinstance(nested, dict) else None)
    if isinstance(nested_cv, dict) and is_number(nested_cv.get("confirmed_dead")):
        return nested_cv["confirmed_dead"]
    legacy = report.get("confirmed_dead_code")
    return legacy if is_number(legacy) else None
def _resolve_baseline(skill_dir: str, report: dict | None) -> dict:
    baseline = _dict_section(report, "baseline")
    if baseline and baseline.get("_schema_version") == _BASELINE_SCHEMA:
        return baseline
    disk = load_t5_baseline(skill_dir, _strict=True)
    if disk and disk.get("_schema_version") == _BASELINE_SCHEMA:
        return disk
    return {}
def _argument_default_texts(node) -> tuple | None:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None
    positional = (*node.args.posonlyargs, *node.args.args)
    positional_defaults = (
        [None] * (len(positional) - len(node.args.defaults))
        + list(node.args.defaults))
    defaults_by_arg = {
        id(arg): default
        for arg, default in zip(positional, positional_defaults)
    }
    defaults_by_arg.update({
        id(arg): default
        for arg, default in zip(node.args.kwonlyargs, node.args.kw_defaults)
    })
    ordered = positional
    if node.args.vararg is not None:
        ordered = (*ordered, node.args.vararg)
    ordered = (*ordered, *node.args.kwonlyargs)
    if node.args.kwarg is not None:
        ordered = (*ordered, node.args.kwarg)
    return tuple(
        ast.unparse(defaults_by_arg[id(arg)])
        if defaults_by_arg.get(id(arg)) is not None else None
        for arg in ordered)
def _function_defaults_by_line(cache, rel_path: str) -> dict[int, tuple]:
    get_entry = getattr(cache, 'get', None)
    if not callable(get_entry):
        return {}
    entry = get_entry(rel_path)
    tree = getattr(entry, 'tree', None)
    if tree is None:
        return {}
    return {
        node.lineno: defaults
        for node in walk_nodes(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        if (defaults := _argument_default_texts(node)) is not None
    }
def _api_surface_keys(cache) -> tuple:
    func_keys: set = set()
    class_keys: set = set()
    sig_by_key: dict = {}
    for rel_path, func_list in cache.all_functions.items():
        rel_key = _api_key_path(rel_path)
        defaults_by_line = _function_defaults_by_line(cache, rel_path)
        for func in func_list:
            key = f"{rel_key}::{qualified_name(func.get('scope') or (), func['name'])}"
            func_keys.add(key)
            sig_by_key[key] = {
                'arg_count': func.get('arg_count', 0),
                'arg_names': tuple(func.get('arg_names', []) or ()),
                'arg_types': tuple(func.get('arg_types', []) or ()),
                'arg_defaults': defaults_by_line.get(func.get('line')),
                'return_annotation': func.get('return_annotation', None),
            }
    for rel_path, class_list in cache.all_classes.items():
        rel_key = _api_key_path(rel_path)
        for cls in class_list:
            class_keys.add(
                f"{rel_key}::{qualified_name(cls.get('scope') or (), cls['name'])}")
    return func_keys, class_keys, sig_by_key
def _sig_changes(prev_sig: dict, curr_sig: dict) -> list:
    changes = []
    prev_count = prev_sig.get('arg_count')
    if not is_number(prev_count):
        prev_count = 0
    if curr_sig['arg_count'] != prev_count:
        changes.append(f"参数数 {prev_count} -> {curr_sig['arg_count']}")
    for key, label in (('arg_names', '参数名'), ('arg_types', '参数类型注解')):
        prev_raw = prev_sig.get(key)
        prev_value = tuple(prev_raw) if isinstance(prev_raw, (list, tuple)) else ()
        # 基线快照存 list、当前签名也存 list；必须两侧同型比较，否则
        # list != tuple 恒为真，会把未变化的签名误报成 signature_change。
        curr_raw = curr_sig.get(key)
        curr_value = tuple(curr_raw) if isinstance(curr_raw, (list, tuple)) else ()
        if curr_value != prev_value:
            changes.append(f"{label} {list(prev_value)} -> {list(curr_value)}")
    prev_defaults = prev_sig.get('arg_defaults')
    curr_defaults = curr_sig.get('arg_defaults')
    if (isinstance(prev_defaults, (list, tuple))
            and isinstance(curr_defaults, (list, tuple))
            and tuple(prev_defaults) != tuple(curr_defaults)):
        changes.append(
            f"参数默认值 {list(prev_defaults)} -> {list(curr_defaults)}")
    prev_ret = prev_sig.get('return_annotation')
    if curr_sig['return_annotation'] != prev_ret:
        changes.append(f"返回注解 {prev_ret} -> {curr_sig['return_annotation']}")
    return changes
def _check_api_surface_regressions(baseline: dict, cache,
                                   behavior_metrics: dict | None = None) -> tuple:
    if baseline.get("_schema_version") != _BASELINE_SCHEMA:
        baseline = {}
    _func_keys, _class_keys, _sig_by_key = _api_surface_keys(cache)
    curr_funcs, curr_classes = set(_func_keys), set(_class_keys)
    regressions = _surface_delta_regressions(baseline, _func_keys, _class_keys)
    regressions.extend(_signature_change_regressions(baseline, _sig_by_key))
    regressions.extend(_check_behavior_regressions(
        baseline, cache, behavior_metrics=behavior_metrics))
    return regressions, curr_funcs, curr_classes
def _append_surface_delta(regressions: list, prev_keys: frozenset | set | None,
                          curr_keys: set, noun: str,
                          removed_type: str, added_type: str) -> None:
    if prev_keys is None:
        return
    removed = prev_keys - curr_keys
    if removed:
        regressions.append({
            "type": removed_type, "severity": "high",
            "message": (f"API 删除了 {len(removed)} 个{noun}: "
                        f"{', '.join(sorted(removed)[:10])}"
                        f"{' 等' if len(removed) > 10 else ''}"),
        })
    added = curr_keys - prev_keys
    if added:
        regressions.append({
            "type": added_type, "severity": "low",
            "message": (f"API 新增了 {len(added)} 个{noun}: "
                        f"{', '.join(sorted(added)[:10])}"
                        f"{' 等' if len(added) > 10 else ''}"),
        })
def _surface_delta_regressions(baseline: dict, func_keys: set,
                               class_keys: set) -> list:
    regressions: list = []
    _append_surface_delta(
        regressions, _normalize_api_key_set(baseline.get("api_function_keys")),
        func_keys, "函数", "api_removed_functions", "api_added_functions")
    _append_surface_delta(
        regressions, _normalize_api_key_set(baseline.get("api_class_keys")),
        class_keys, "类", "api_removed_classes", "api_added_classes")
    return regressions
def _signature_change_regressions(baseline: dict, curr_signatures: dict) -> list:
    regressions: list = []
    prev_signatures = baseline.get("function_signatures", {})
    if not isinstance(prev_signatures, dict):
        prev_signatures = {}
    prev_signatures = {
        _api_key_path(fname): prev_sig
        for fname, prev_sig in prev_signatures.items()
    }
    if not prev_signatures:
        return regressions
    for fname, prev_sig in prev_signatures.items():
        curr_sig = curr_signatures.get(fname)
        if curr_sig is None:
            continue
        if not isinstance(prev_sig, dict):
            continue
        changes = _sig_changes(prev_sig, curr_sig)
        if changes:
            regressions.append({
                "type": "signature_change", "severity": "medium",
                "function": fname,
                "message": f"函数 {fname} 签名变更: {'; '.join(changes)}",
            })
    return regressions
def _compare_behavior_metrics(prev_metrics: dict, curr_metrics: dict) -> tuple:
    changes = []
    cc_change, cc_delta = _compare_cc_metric(
        prev_metrics.get('cyclomatic_complexity'),
        curr_metrics.get('cyclomatic_complexity'))
    if cc_change:
        changes.append(cc_change)
    line_change, line_delta_pct = _compare_body_lines_metric(
        prev_metrics.get('body_lines'),
        curr_metrics.get('body_lines'))
    if line_change:
        changes.append(line_change)
    for key, label in (('try_count', 'try块数'), ('return_count', 'return路径数')):
        cnt_change = _compare_count_metric(
            prev_metrics.get(key), curr_metrics.get(key), label)
        if cnt_change:
            changes.append(cnt_change)
    calls_change = _compare_call_targets_change(
        prev_metrics.get('call_targets'), curr_metrics.get('call_targets'))
    if calls_change:
        changes.append(calls_change)
    return changes, cc_delta, line_delta_pct
def _compare_cc_metric(prev_cc, curr_cc) -> tuple:
    comparable = is_number(prev_cc) and is_number(curr_cc)
    delta = (curr_cc - prev_cc) if comparable else 0
    if comparable and curr_cc > prev_cc and delta >= 3:
        return f"圈复杂度 {prev_cc} -> {curr_cc}", delta
    return None, delta
def _compare_body_lines_metric(prev_lines, curr_lines) -> tuple:
    if not (is_number(prev_lines) and is_number(curr_lines)
            and prev_lines > 0):
        return None, 0.0
    pct = abs(curr_lines - prev_lines) / prev_lines
    if pct >= 0.5:
        return f"函数体行数 {prev_lines} -> {curr_lines}", pct
    return None, pct
def _compare_count_metric(prev_val, curr_val, label: str) -> str | None:
    if (is_number(prev_val) and is_number(curr_val)
            and curr_val != prev_val):
        return f"{label} {prev_val} -> {curr_val}"
    return None
def _compare_call_targets_change(prev_targets, curr_targets) -> str | None:
    prev_calls = _normalize_string_set(prev_targets)
    curr_calls = _normalize_string_set(curr_targets)
    if prev_calls is None or curr_calls is None:
        return None
    added_calls = curr_calls - prev_calls
    removed_calls = prev_calls - curr_calls
    if not (added_calls or removed_calls):
        return None
    parts = []
    if added_calls:
        parts.append(f"新增调用: {sorted(added_calls)[:5]}")
    if removed_calls:
        parts.append(f"移除调用: {sorted(removed_calls)[:5]}")
    return "; ".join(parts)
def _check_behavior_regressions(baseline: dict, cache,
                                behavior_metrics: dict | None = None) -> list:
    regressions: list = []
    prev_behavior = baseline.get("function_behavior", {})
    if not isinstance(prev_behavior, dict):
        prev_behavior = {}
    prev_behavior = {
        _api_key_path(fname): metrics for fname, metrics in prev_behavior.items()}
    if not prev_behavior:
        return regressions
    curr_behavior = (behavior_metrics if isinstance(behavior_metrics, dict)
                     else collect_function_behavior_metrics(cache))
    curr_behavior = {
        _api_key_path(fname): metrics for fname, metrics in curr_behavior.items()}
    for fname, prev_metrics in prev_behavior.items():
        entry = _behavior_change_entry(
            fname, prev_metrics, curr_behavior.get(fname))
        if entry is not None:
            regressions.append(entry)
    return regressions
def _behavior_change_entry(fname: str, prev_metrics,
                           curr_metrics) -> dict | None:
    if not isinstance(prev_metrics, dict) or not isinstance(curr_metrics, dict):
        return None
    changes, cc_delta, line_delta_pct = _compare_behavior_metrics(
        prev_metrics, curr_metrics)
    if not changes:
        return None
    severity = "medium" if cc_delta >= 5 or line_delta_pct >= 1.0 else "low"
    return {
        "type": "behavior_change", "severity": severity,
        "function": fname,
        "message": f"函数 {fname} 行为变化: {'; '.join(changes)}",
    }
_CARRY_FORWARD_FIELDS = (
    "orphans", "break_points", "syntax_errors", "blindspots",
    "confirmed_dead_code", "previous_score",
)
def _carry_forward_baseline(snapshot: dict, previous: dict | None) -> dict:
    if not isinstance(previous, dict) or not previous:
        return snapshot
    merged = dict(snapshot)
    for name in _CARRY_FORWARD_FIELDS:
        if merged.get(name) is None and previous.get(name) is not None:
            merged[name] = previous[name]
    return merged
def _cycle_graph(cache) -> dict:
    graph = getattr(cache, "import_graph", None)
    if graph:
        return graph
    entries = getattr(cache, "entries", None)
    if entries is not None:
        return getattr(cache, "import_graph", None) or {}
    skill_dir = _path_arg(getattr(cache, "skill_dir", ""))
    if not skill_dir or not os.path.isdir(skill_dir):
        _log.warning(
            "count_import_cycles: 缓存 %s 无导入图且无可用技能目录，按 0 环处理",
            type(cache).__name__)
        return {}
    file_cache = FileCache(skill_dir)
    file_cache.load()
    return file_cache.import_graph
def count_import_cycles(cache) -> int:
    graph = _cycle_graph(cache)
    return len(detect_cycles(graph)) if graph else 0
def _collect_t5_snapshot(cache, behavior_metrics: dict | None = None,
                         runtime_current: dict | None = None,
                         current_score: float | None = None,
                         circular_imports: int | None = None) -> dict:
    api_functions, api_classes, signatures = _api_surface_keys(cache)
    signatures = {
        key: {
            'arg_count': sig['arg_count'],
            'arg_names': list(sig['arg_names']),
            'arg_types': list(sig['arg_types']),
            'arg_defaults': (list(sig['arg_defaults'])
                             if sig['arg_defaults'] is not None else None),
            'return_annotation': sig['return_annotation'],
        }
        for key, sig in signatures.items()
    }
    raw_behavior = (behavior_metrics if isinstance(behavior_metrics, dict)
                    else collect_function_behavior_metrics(cache))
    behavior = {}
    for fname, m in raw_behavior.items():
        if not isinstance(m, dict):
            continue
        behavior[_api_key_path(fname)] = {
            **m,
            'call_targets': sorted(_normalize_string_set(m.get('call_targets')) or ()),
        }
    cycles = (circular_imports if circular_imports is not None
              else count_import_cycles(cache))
    rt = dict_or_empty(runtime_current)
    cc = _dict_section(rt, "call_chain")
    bl = _dict_section(rt, "blindspots")
    return {
        "_schema_version": _BASELINE_SCHEMA,
        "api_function_keys": sorted(api_functions),
        "api_class_keys": sorted(api_classes),
        "function_signatures": signatures,
        "function_behavior": behavior,
        "file_count": len(cache.entries),
        "circular_imports": cycles,
        "orphans": cc.get("orphans"),
        "break_points": cc.get("break_points"),
        "syntax_errors": cc.get("syntax_errors"),
        "blindspots": bl.get("total"),
        "previous_score": current_score,
        "confirmed_dead_code": _report_dead_code(runtime_current),
    }
def _compute_regression_risk_score(regressions: list,
                                   delta: float) -> int | float:
    score = 0
    for r in regressions:
        score += _SEVERITY_WEIGHTS.get(
            r.get('severity', 'low'), _DEFAULT_SEVERITY_WEIGHT)
    if delta < 0:
        score += abs(delta)
    return min(score, _RISK_SCORE_CAP)
@dataclass(frozen=True)
class _RegressionContext:
    cache: FileCache
    report: dict | None
    baseline: dict
    behavior: dict
    @property
    def current_files(self) -> int:
        return len(self.cache.entries)
    @cached_property
    def current_cycles(self) -> int:
        return count_import_cycles(self.cache)
    @property
    def current_dead_code(self) -> int | float:
        raw = _report_dead_code(self.report)
        return raw if is_number(raw) else 0
def _collect_delta_regressions(ctx: _RegressionContext) -> list:
    return _count_delta_regressions([
        (ctx.baseline.get("file_count"), ctx.current_files, "new_files", "low",
         lambda p, c: f"新增 {c - p} 个文件 ({p} → {c})", False),
        (ctx.baseline.get("circular_imports"), ctx.current_cycles,
         "new_circular_import", "high",
         lambda p, c: f"新增循环依赖: {p} → {c}", False),
        (ctx.baseline.get("confirmed_dead_code"), ctx.current_dead_code,
         "dead_code_increase", "medium",
         lambda p, c: f"死代码增加: {p} → {c}", False),
    ])
def _collect_regressions(ctx: _RegressionContext) -> tuple[list, set, set]:
    regressions = _check_metric_regressions(ctx.baseline, ctx.report)
    regressions.extend(_collect_delta_regressions(ctx))
    api_regressions, curr_funcs, curr_classes = _check_api_surface_regressions(
        ctx.baseline, ctx.cache, behavior_metrics=ctx.behavior)
    regressions.extend(api_regressions)
    return regressions, curr_funcs, curr_classes
def _build_regression_metrics(ctx: _RegressionContext, delta, regressions: list,
                              curr_funcs, curr_classes) -> dict:
    return {
        "is_seed": not ctx.baseline,
        "previous_score": ctx.baseline.get("previous_score"),
        "current_score": _field(ctx.report, "health_score"),
        "delta": delta,
        "regression_count": len(regressions),
        "has_baseline": bool(ctx.baseline),
        "new_files": _new_file_count(ctx.current_files, ctx.baseline),
        "current_file_count": ctx.current_files,
        "api_function_count": len(curr_funcs),
        "api_class_count": len(curr_classes),
        "circular_imports": ctx.current_cycles,
        "dead_code_count": ctx.current_dead_code,
        "high_severity_regressions": _count_severity(regressions, "high"),
        "critical_regressions": _count_severity(regressions, "critical"),
        "regression_risk_score": _compute_regression_risk_score(
            regressions, delta if delta is not None else 0),
    }
_FILE_CACHE_ATTRS = ("all_functions", "all_classes", "valid_entries", "entries")
def _cache_matches_skill_dir(cache, skill_dir: str) -> bool:
    cached_dir = _path_arg(getattr(cache, "skill_dir", ""))
    if not cached_dir:
        return False
    try:
        return (os.path.normcase(os.path.realpath(cached_dir))
                == os.path.normcase(os.path.realpath(skill_dir)))
    except OSError:
        _log.debug("run_regression_tests: 缓存目录不可解析，按磁盘重建",
                   exc_info=True)
        return False
def _provides_source_face(cache, skill_dir: str) -> bool:
    if not (callable(getattr(cache, "get_source", None))
            and callable(getattr(cache, "get_ast", None))
            and getattr(cache, "py_files", None) is not None):
        return False
    intact = getattr(cache, "is_residency_intact", None)
    try:
        if not callable(intact) or not intact():
            return False
    except (OSError, RuntimeError, ValueError):
        _log.debug("run_regression_tests: 驻留探测失败，按磁盘重建",
                   exc_info=True)
        return False
    return _cache_matches_skill_dir(cache, skill_dir)
def _as_file_cache(skill_dir: str, cache):
    if cache is not None and all(
            hasattr(cache, name) for name in _FILE_CACHE_ATTRS):
        if (not _path_arg(getattr(cache, "skill_dir", ""))
                or _cache_matches_skill_dir(cache, skill_dir)):
            return cache
        _log.info(
            "run_regression_tests: FileCache 目录 %s 与目标 %s 不一致，按目标重建",
            getattr(cache, "skill_dir", ""), skill_dir)
    ctx = None
    if cache is not None:
        ctx = cache if _provides_source_face(cache, skill_dir) else None
        _log.info(
            "run_regression_tests: 缓存 %s 不含 FileCache 面，按目录重建"
            "（复用源码面=%s）", type(cache).__name__, ctx is not None)
    file_cache = FileCache(skill_dir, ctx=ctx)
    file_cache.load()
    return file_cache
def _transient_read_failures(cache) -> list[str]:
    failures = []
    for entry in cache.entries:
        if is_transient_io_error(getattr(entry, "parse_error", None)):
            failures.append(str(
                getattr(entry, "rel_path", "")
                or getattr(entry, "path", "")))
    return sorted(failures)
def _mark_scan_degraded(result: TestMethodResult,
                        read_failures: list[str] | None = None) -> None:
    result.status = "warn"
    result.score = min(result.score, 50)
    if read_failures:
        result.summary = (
            f"扫描降级：本轮 {len(read_failures)} 个文件读取失败"
            "（未做回归对比，未写入不完整基线）")
        return
    result.summary = ("扫描降级：本轮未读到任何文件"
                      "（旧基线已保留，未做回归对比）")
def _baseline_must_be_preserved(snapshot: dict, baseline: dict) -> bool:
    if not baseline:
        return False
    prev_files = baseline.get("file_count")
    if not is_number(prev_files) or prev_files <= 0:
        return False
    return snapshot.get("file_count") == 0
def run_regression_tests(skill_dir: str, report: dict | None = None, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name="回归测试",
        method_id="regression_test",
    )
    skill_dir = _path_arg(skill_dir)
    _invalid = _validate_regression_inputs(skill_dir)
    if _invalid is not None:
        return _abort_invalid_input(result, _invalid, start)
    cache = kwargs.get('_cache')
    if cache is None:
        cache = kwargs.get('cache')
    cache = _as_file_cache(skill_dir, cache)
    report = report if isinstance(report, dict) else None
    try:
        baseline = _resolve_baseline(skill_dir, report)
    except _T5BaselinePersistenceError as exc:
        return _abort_invalid_input(
            result, (str(exc), "回归基线不可读，未执行回归对比"), start)
    prev_score = baseline.get("previous_score")
    current_score = _field(report, "health_score")
    delta = _compute_health_delta(prev_score, current_score)
    ctx = _RegressionContext(
        cache=cache, report=report, baseline=baseline,
        behavior=collect_function_behavior_metrics(cache),
    )
    read_failures = _transient_read_failures(cache)
    preserved = (_baseline_must_be_preserved(
        {"file_count": ctx.current_files}, baseline)
        or bool(read_failures and baseline))
    scan_degraded = preserved or bool(read_failures)
    if scan_degraded:
        regressions, curr_funcs, curr_classes = [], set(), set()
    else:
        regressions, curr_funcs, curr_classes = _collect_regressions(ctx)
    result.metrics = _build_regression_metrics(
        ctx, delta, regressions, curr_funcs, curr_classes)
    result.findings = regressions
    if not scan_degraded:
        _finalize_regression_result(result, baseline, regressions, delta)
    snapshot = _collect_t5_snapshot(
        cache, behavior_metrics=ctx.behavior, runtime_current=report,
        current_score=current_score,
        circular_imports=ctx.current_cycles)
    result.metrics["baseline_preserved"] = preserved
    result.metrics["scan_degraded"] = scan_degraded
    result.metrics["scan_read_failures"] = read_failures
    if scan_degraded:
        if read_failures:
            _log.warning(
                "run_regression_tests: %d 个文件读取失败，跳过回归对比且不写入"
                "不完整基线: %s", len(read_failures), ", ".join(read_failures))
        else:
            _log.warning(
                "run_regression_tests: 本轮扫描 0 个文件（基线 %s 个），保留旧基线"
                "不覆盖: %s", baseline.get("file_count"), skill_dir)
        _mark_scan_degraded(result, read_failures)
    else:
        try:
            save_t5_baseline(
                skill_dir, _carry_forward_baseline(snapshot, baseline),
                _strict=True)
        except _T5BaselinePersistenceError as exc:
            return _abort_invalid_input(
                result, (str(exc), "回归基线保存失败，本轮结果未持久化"), start)
    return result.finish(start)
def _abort_invalid_input(result: TestMethodResult, _invalid: tuple,
                          start: float) -> TestMethodResult:
    result.status = "error"
    result.score = 0
    result.error = _invalid[0]
    result.summary = _invalid[1]
    return result.finish(start)
def _count_severity(regressions: list, severity: str) -> int:
    return sum(1 for r in regressions if r.get("severity") == severity)
def _new_file_count(curr_files: int, baseline: dict) -> int:
    _prev = baseline.get("file_count")
    if not is_number(_prev) or _prev < 0 or curr_files <= _prev:
        return 0
    return curr_files - _prev
def _validate_regression_inputs(skill_dir) -> tuple | None:
    if not isinstance(skill_dir, str) or not os.path.isdir(skill_dir):
        return (f"技能目录不存在: {skill_dir!r}", f"分析目录无效: {skill_dir!r}")
    try:
        t5_baseline_path(skill_dir)
    except (RuntimeError, ValueError) as exc:
        log_swallowed(
            __name__, exc,
            context=f'_validate_regression_inputs:{type(exc).__name__}')
        return (f"分析目录产物落点不可解析: {exc}",
                "分析目录无效（Temp 治理契约下无可用产物根）")
    return None
def _count_delta_regressions(checks: list) -> list:
    out = []
    for prev_val, curr_val, rtype, severity, msg_fn, require_prev_positive in checks:
        if not is_number(prev_val) or not is_number(curr_val):
            continue
        if require_prev_positive and prev_val <= 0:
            continue
        if curr_val > prev_val:
            out.append({
                "type": rtype, "severity": severity,
                "message": msg_fn(prev_val, curr_val),
            })
    return out
def _finalize_regression_result(result: TestMethodResult, baseline: dict,
                                regressions: list, delta) -> None:
    if not baseline:
        if regressions:
            result.status = "warn"
            result.score = max(0, 100 - len(regressions) * 15)
            result.summary = (
                f"首次审计检测到 {len(regressions)} 个问题（种子基线已持久化）")
            return
        result.status = "pass"
        result.score = 50
        result.summary = "首次审计：种子基线已持久化，下次审计将进行回归对比"
    elif not regressions:
        result.status = "pass"
        result.score = 100
        result.summary = "未检测到回归"
    elif (len(regressions) <= 1 and (delta is None or delta >= 0)
            and all(r.get("severity") == "low" for r in regressions)):
        result.status = "pass"
        result.score = 85
        result.summary = "轻微指标波动，无严重回归"
    else:
        result.status = "warn"
        result.score = max(0, 100 - len(regressions) * 15)
        result.summary = f"检测到 {len(regressions)} 个回归项"
_EMPTY_CONTAINER_CTORS = frozenset({"set", "frozenset", "dict", "list", "tuple"})
def _is_empty_container(node) -> bool:
    if isinstance(node, ast.Dict):
        return not node.keys
    if isinstance(node, (ast.List, ast.Set, ast.Tuple)):
        return not node.elts
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in _EMPTY_CONTAINER_CTORS
            and not node.args and not node.keywords)
def _is_stub_return(stmt) -> bool:
    if not isinstance(stmt, ast.Return):
        return False
    rv = stmt.value
    if rv is None:
        return True
    if (isinstance(rv, ast.Constant)
            and not isinstance(rv.value, bool)
            and rv.value in (None, 0, "")):
        return True
    return _is_empty_container(rv)
_STUB_RAISE_NAMES = frozenset({"NotImplementedError"})
def _is_stub_raise(stmt) -> bool:
    if not isinstance(stmt, ast.Raise) or stmt.exc is None:
        return False
    exc = stmt.exc.func if isinstance(stmt.exc, ast.Call) else stmt.exc
    if isinstance(exc, ast.Name):
        return exc.id in _STUB_RAISE_NAMES
    return (isinstance(exc, ast.Attribute)
            and exc.attr in _STUB_RAISE_NAMES
            and isinstance(exc.value, ast.Name)
            and exc.value.id == "builtins")
def count_meaningful_stmts(body: list) -> int:
    meaningful = 0
    for stmt in body:
        if isinstance(stmt, ast.Pass):
            continue
        if (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Constant)):
            continue
        if _is_stub_return(stmt):
            continue
        if _is_stub_raise(stmt):
            continue
        meaningful += 1
    return meaningful
class BaselineSnapshot:
    def __init__(self, root_dir: str) -> None:
        root_dir = _path_arg(root_dir)
        self.root_dir = os.path.abspath(root_dir) if root_dir else ""
        self.file_count = 0
        self.total_lines = 0
        self.file_lines: dict[str, int] = {}
        self.py_files: list[str] = []
        self.public_functions: dict[str, list[str]] = {}
        self.subsystems: list[str] = []
        self.unreadable_files: list[str] = []
        self.timestamp = datetime.now().isoformat()
        self._scan()
    def _scan(self) -> None:
        if not self.root_dir:
            return
        for rel, fpath in iter_py_source_files(self.root_dir):
            self._scan_py_file(fpath, rel)
        self.subsystems = sorted(
            {rel.rsplit("/", 1)[0] for rel in self.py_files if "/" in rel})
    def _scan_py_file(self, fpath: str, rel: str) -> None:
        code, _fingerprint = read_source_with_fingerprint(fpath, strict=True)
        if code is None:
            self.unreadable_files.append(rel)
            _log.debug("跳过不可读文件: %s", fpath)
            return
        line_count = count_lines(code)
        self.file_lines[rel] = line_count
        self.total_lines += line_count
        self.file_count += 1
        self.py_files.append(rel)
        funcs = extract_public_names(code, rel)
        if funcs:
            self.public_functions[rel] = funcs
def _rule_entry(iron_law: int, rule: str, detail: str) -> dict:
    return {"iron_law": iron_law, "rule": rule, "detail": detail}
def _check_red_line_limits(old_base: BaselineSnapshot,
                           new_base: BaselineSnapshot, metrics: dict,
                           violations: list[dict]) -> None:
    if old_base.file_count > 0:
        fc = (new_base.file_count - old_base.file_count) / old_base.file_count
        metrics["file_change"] = f"{fc:+.1%}"
        if fc < -0.30:
            violations.append(_rule_entry(
                5, "文件数红线",
                f"{old_base.file_count}->{new_base.file_count} ({fc:+.0%})"))
    if old_base.total_lines > 100:
        lc = (new_base.total_lines - old_base.total_lines) / old_base.total_lines
        metrics["line_change"] = f"{lc:+.1%}"
        if lc < -0.50:
            violations.append(_rule_entry(
                5, "行数红线",
                f"{old_base.total_lines:,}->{new_base.total_lines:,} ({lc:+.0%})"))
def _as_py_rel(name: str) -> str:
    raw = str(name or "").replace("\\", "/").strip().strip("/")
    if not raw:
        return ""
    rel = posixpath.normpath(raw)
    if rel == ".":
        return ""
    return rel if rel.lower().endswith(".py") else f"{rel}.py"
def _normalize_rename_map(rename_map: dict | None) -> dict[str, str]:
    if not isinstance(rename_map, dict):
        return {}
    normalized: dict[str, str] = {}
    for old, new in rename_map.items():
        if not (isinstance(old, str) and isinstance(new, str)):
            continue
        old_key = _as_py_rel(old)
        new_key = _as_py_rel(new)
        if old_key and new_key and old_key != new_key:
            normalized[old_key] = new_key
    return normalized
def _check_api_mapping(old_base: BaselineSnapshot,
                       new_base: BaselineSnapshot, metrics: dict,
                       violations: list[dict],
                       rename_map: dict[str, str]) -> None:
    lost_funcs: list[str] = []
    renamed: list[str] = []
    for mod, funcs in old_base.public_functions.items():
        target_mod = rename_map.get(mod, mod)
        if target_mod != mod:
            renamed.append(f"{mod}->{target_mod}")
        if target_mod in new_base.public_functions:
            lost_funcs.extend(
                f"{target_mod}::{fn}"
                for fn in set(funcs)
                - set(new_base.public_functions[target_mod]))
        else:
            lost_funcs.extend(f"{target_mod}::{fn}" for fn in funcs)
    metrics["lost_funcs"] = len(lost_funcs)
    metrics["renamed_modules"] = len(renamed)
    if renamed:
        metrics["rename_map_applied"] = renamed
    if lost_funcs:
        violations.append(_rule_entry(
            1, "公开函数丢失", f"丢失 {len(lost_funcs)} 个函数"))
def _parse_for_stub_check(full: str) -> tuple[ast.Module | None, int, int]:
    code, _fingerprint = read_source_with_fingerprint(full, strict=True)
    if code is None:
        _log.debug("桩统计跳过不可读文件: %s", full)
        return None, 0, 0
    try:
        tree = ast.parse(code)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(
            __name__, _e,
            context=f'_parse_for_stub_check:{type(_e).__name__}')
        return None, 1, 0
    try:
        compile(tree, full, "exec")
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(
            __name__, _e,
            context=f'_parse_for_stub_check:{type(_e).__name__}')
        return tree, 0, 1
    return tree, 0, 0
def _count_stub_functions(tree: ast.AST) -> tuple[int, int]:
    stubs = 0
    total = 0
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        total += 1
        if count_meaningful_stmts(node.body) == 0:
            stubs += 1
    return stubs, total
def _check_stub_syntax(new_base: BaselineSnapshot, metrics: dict,
                       violations: list[dict],
                       warnings: list[dict]) -> tuple[int, int]:
    sc, tf = 0, 0
    syn_errs = 0
    sem_errs = 0
    for fpath in new_base.py_files:
        full = os.path.join(new_base.root_dir, fpath)
        tree, _syn, _sem = _parse_for_stub_check(full)
        syn_errs += _syn
        sem_errs += _sem
        if tree is None:
            continue
        _stubs, _total = _count_stub_functions(tree)
        sc += _stubs
        tf += _total
    sr = sc / max(tf, 1)
    metrics["stub_ratio"] = f"{sr:.1%}"
    if sr > 0.40:
        violations.append(_rule_entry(2, "空桩率红线", f"{sr:.0%} ({sc}/{tf})"))
    elif sr > 0.10:
        warnings.append(_rule_entry(2, "空桩率偏高", f"{sr:.0%} ({sc}/{tf})"))
    return syn_errs, sem_errs
def _py_subsystems(snapshot: BaselineSnapshot,
                   rename_map: dict[str, str]) -> set[str]:
    return {
        mapped.split("/", 1)[0]
        for rel in snapshot.py_files
        if "/" in (mapped := rename_map.get(rel, rel))
    }
def _check_subsystem_integrity(old_base: BaselineSnapshot,
                               new_base: BaselineSnapshot,
                               violations: list[dict],
                               rename_map: dict[str, str]) -> None:
    old_subs = _py_subsystems(old_base, rename_map)
    new_subs = _py_subsystems(new_base, {})
    lost_subs = old_subs - new_subs
    if lost_subs:
        violations.append(_rule_entry(
            5, "子系统消失", f"{len(lost_subs)} 个子系统消失"))
def _missing_input_dirs(old_dir: str, new_dir: str) -> list[str]:
    return [str(d) for d in (old_dir, new_dir)
            if not isinstance(d, (str, os.PathLike)) or not os.path.isdir(d)]
def _guard_dir_violation(missing: list[str], stage: str) -> dict:
    _log.warning("run_guard: 输入目录不存在，拒绝放行: %s", missing)
    return {
        "passed": False,
        "violations": [_rule_entry(
            1, "目录不可用",
            f"{len(missing)} 个输入目录不存在: {', '.join(missing)}")],
        "warnings": [],
        "metrics": {"stage": stage, "missing_dirs": missing},
        "growth_report": {},
    }
def _check_source_readability(old_base: BaselineSnapshot,
                              new_base: BaselineSnapshot, metrics: dict,
                              violations: list[dict]) -> None:
    old_errors = list(old_base.unreadable_files)
    new_errors = list(new_base.unreadable_files)
    metrics["old_read_errors"] = old_errors
    metrics["new_read_errors"] = new_errors
    if not (old_errors or new_errors):
        return
    parts = []
    for label, errors in (("旧目录", old_errors), ("新目录", new_errors)):
        if errors:
            parts.append(
                f"{label} {len(errors)} 个: {', '.join(errors[:5])}"
                f"{'…' if len(errors) > 5 else ''}")
    violations.append(_rule_entry(4, "源文件读取失败", "；".join(parts)))
_SEVERITY_RANK = {"INFO": 0, "WARN": 1, "ERROR": 2}
_DEFAULT_BLOAT_PCT = 20.0
_DEFAULT_BLOAT_RATIO = _DEFAULT_BLOAT_PCT / 100.0
_DEFAULT_BLOAT_LINES = 50
_DEFAULT_MAX_ENTRIES = 50
def _channel_total(declared, entries: list) -> int:
    declared_count = finite_float_or_none(declared)
    return max(int(declared_count) if declared_count is not None else 0,
               len(entries))
@dataclass
class GrowthDelta:
    path: str = ""
    old_lines: int = 0
    new_lines: int = 0
    delta_lines: int = 0
    delta_pct: float = 0.0
    severity: str = "INFO"
    is_new: bool = False
    is_deleted: bool = False
    old_func_count: int = 0
    new_func_count: int = 0
    def to_dict(self) -> dict:
        return {
            "path": self.path,
            "old_lines": self.old_lines,
            "new_lines": self.new_lines,
            "delta_lines": self.delta_lines,
            "delta_pct": round(self.delta_pct, 4),
            "severity": self.severity,
            "is_new": self.is_new,
            "is_deleted": self.is_deleted,
            "old_func_count": self.old_func_count,
            "new_func_count": self.new_func_count,
        }
@dataclass
class GrowthReport:
    project_path: str = ""
    baseline_snapshot_id: str = ""
    current_snapshot_id: str = ""
    timestamp: str = ""
    total_delta_lines: int = 0
    total_delta_pct: float = 0.0
    severity: str = "INFO"
    bloated_total: int = 0
    shrunk_total: int = 0
    new_total: int = 0
    deleted_total: int = 0
    bloated_files: list[GrowthDelta] = field(default_factory=list)
    shrunk_files: list[GrowthDelta] = field(default_factory=list)
    new_files: list[GrowthDelta] = field(default_factory=list)
    deleted_files: list[GrowthDelta] = field(default_factory=list)
    def to_dict(self) -> dict:
        return {
            "project_path": self.project_path,
            "baseline_snapshot_id": self.baseline_snapshot_id,
            "current_snapshot_id": self.current_snapshot_id,
            "timestamp": self.timestamp,
            "total_delta_lines": self.total_delta_lines,
            "total_delta_pct": round(self.total_delta_pct, 4),
            "severity": self.severity,
            "bloated_files": [gd.to_dict() for gd in self.bloated_files],
            "shrunk_files": [gd.to_dict() for gd in self.shrunk_files],
            "new_files": [gd.to_dict() for gd in self.new_files],
            "deleted_files": [gd.to_dict() for gd in self.deleted_files],
            "bloated_total": _channel_total(self.bloated_total,
                                            self.bloated_files),
            "shrunk_total": _channel_total(self.shrunk_total,
                                           self.shrunk_files),
            "new_total": _channel_total(self.new_total, self.new_files),
            "deleted_total": _channel_total(self.deleted_total,
                                            self.deleted_files),
        }
@dataclass(frozen=True)
class _SideStats:
    lines: dict[str, int]
    funcs: dict[str, int]
    unreadable: set[str]
def _count_file_stats(
    root_dir: str,
) -> tuple[dict[str, int], dict[str, int], set[str]]:
    file_lines: dict[str, int] = {}
    file_funcs: dict[str, int] = {}
    unreadable: set[str] = set()
    for rel, fpath in iter_py_source_files(root_dir):
        code, _fingerprint = read_source_with_fingerprint(fpath, strict=True)
        if code is None:
            _log.debug("_count_file_stats: 读取失败标记为不可比，不入统计: %s", fpath)
            unreadable.add(rel)
            continue
        file_lines[rel] = count_lines(code)
        file_funcs[rel] = len(extract_public_names(code, fpath))
    return file_lines, file_funcs, unreadable
def _side_stats_of(snapshot: BaselineSnapshot) -> _SideStats:
    return _SideStats(
        lines=dict(snapshot.file_lines),
        funcs={rel: len(names)
               for rel, names in snapshot.public_functions.items()},
        unreadable=set(snapshot.unreadable_files),
    )
def _bloat_severity(pct: float, delta: int) -> str:
    return "ERROR" if (pct >= 0.5 or delta >= 200) else "WARN"
def _relative_delta(delta: int, baseline: int) -> float:
    if baseline > 0:
        return delta / baseline
    if delta > 0:
        return 1.0
    if delta < 0:
        return -1.0
    return 0.0
def _growth_entry(rel: str, old: _SideStats, new: _SideStats,
                  *, bloat_ratio: float,
                  bloat_lines: int) -> tuple[str, GrowthDelta] | None:
    ol = old.lines.get(rel)
    nl = new.lines.get(rel)
    of = old.funcs.get(rel, 0)
    nf = new.funcs.get(rel, 0)
    if ol is None:
        return "new", GrowthDelta(
            path=rel, old_lines=0, new_lines=nl, delta_lines=nl,
            delta_pct=1.0, severity="INFO", old_func_count=0,
            new_func_count=nf, is_new=True)
    if nl is None:
        return "deleted", GrowthDelta(
            path=rel, old_lines=ol, new_lines=0, delta_lines=-ol,
            delta_pct=-1.0, severity="INFO", old_func_count=of,
            new_func_count=0, is_deleted=True)
    delta = nl - ol
    pct = _relative_delta(delta, ol)
    if not _exceeds_growth_threshold(delta, pct, bloat_ratio, bloat_lines):
        return None
    if delta > 0:
        return "bloated", GrowthDelta(
            path=rel, old_lines=ol, new_lines=nl, delta_lines=delta,
            delta_pct=pct, severity=_bloat_severity(pct, delta),
            old_func_count=of, new_func_count=nf)
    return "shrunk", GrowthDelta(
        path=rel, old_lines=ol, new_lines=nl, delta_lines=delta,
        delta_pct=pct, severity="INFO", old_func_count=of,
        new_func_count=nf)
def _exceeds_growth_threshold(delta: int, pct: float,
                              bloat_ratio: float, bloat_lines: int) -> bool:
    return abs(delta) > 0 and (abs(pct) >= bloat_ratio
                               or abs(delta) >= bloat_lines)
def _classify_growth_entries(old: _SideStats, new: _SideStats,
                             report: GrowthReport, unreadable: set[str], *,
                             bloat_ratio: float,
                             bloat_lines: int) -> None:
    channels = {
        "new": report.new_files,
        "deleted": report.deleted_files,
        "bloated": report.bloated_files,
        "shrunk": report.shrunk_files,
    }
    for rel in sorted(set(old.lines) | set(new.lines)):
        if rel in unreadable:
            continue
        entry = _growth_entry(rel, old, new,
                              bloat_ratio=bloat_ratio,
                              bloat_lines=bloat_lines)
        if entry is None:
            continue
        channel, delta = entry
        channels[channel].append(delta)
def _growth_report_from_sides(
    old: _SideStats, new: _SideStats, old_dir: str, new_dir: str, *,
    bloat_ratio: float, bloat_lines: int, max_entries: int,
) -> GrowthReport:
    report = GrowthReport(
        project_path=new_dir,
        baseline_snapshot_id=os.path.abspath(old_dir) if old_dir else "",
        current_snapshot_id=os.path.abspath(new_dir) if new_dir else "",
        timestamp=datetime.now().isoformat(timespec="seconds"),
    )
    unreadable = old.unreadable | new.unreadable
    _log_unreadable(unreadable, old.unreadable)
    _classify_growth_entries(old, new, report, unreadable,
                             bloat_ratio=bloat_ratio,
                             bloat_lines=bloat_lines)
    _sort_growth_channels(report)
    report.total_delta_lines, report.total_delta_pct = _growth_totals(
        old, new, unreadable)
    report.severity = _overall_growth_severity(report)
    _truncate_growth_channels(report, max_entries)
    return report
def _non_negative_config(value, default: float) -> float:
    number = finite_float_or_none(value)
    return number if number is not None and number >= 0 else default
def _positive_int_config(value, default: int) -> int:
    number = finite_float_or_none(value)
    count = int(number) if number is not None else 0
    return count if count > 0 else default
def analyze_growth(old_dir: str, new_dir: str,
                   *, bloat_pct: float = _DEFAULT_BLOAT_PCT,
                   bloat_lines: int = _DEFAULT_BLOAT_LINES,
                   max_entries: int = _DEFAULT_MAX_ENTRIES) -> GrowthReport:
    old_dir, new_dir = _path_arg(old_dir), _path_arg(new_dir)
    bloat_pct = _non_negative_config(bloat_pct, _DEFAULT_BLOAT_PCT)
    bloat_lines = _non_negative_config(bloat_lines, _DEFAULT_BLOAT_LINES)
    max_entries = _positive_int_config(max_entries, _DEFAULT_MAX_ENTRIES)
    missing_dirs = _missing_input_dirs(old_dir, new_dir)
    if missing_dirs:
        _log.warning("analyze_growth: 输入目录不存在，拒绝出对比报告: %s",
                     missing_dirs)
        return _invalid_growth_report(old_dir, new_dir)
    return _growth_report_from_sides(
        _SideStats(*_count_file_stats(old_dir)),
        _SideStats(*_count_file_stats(new_dir)),
        old_dir, new_dir,
        bloat_ratio=bloat_pct / 100.0,
        bloat_lines=bloat_lines,
        max_entries=max_entries,
    )
def _invalid_growth_report(old_dir: str, new_dir: str) -> GrowthReport:
    return GrowthReport(
        project_path=new_dir,
        baseline_snapshot_id=os.path.abspath(old_dir) if old_dir else "",
        current_snapshot_id=os.path.abspath(new_dir) if new_dir else "",
        timestamp=datetime.now().isoformat(timespec="seconds"),
        severity="ERROR",
    )
def _log_unreadable(unreadable: set[str], old_unreadable: set[str]) -> None:
    for rel in sorted(unreadable):
        _log.warning(
            "analyze_growth: 文件读盘失败从膨胀分析中排除: %s（%s侧）",
            rel, "旧" if rel in old_unreadable else "新")
def _growth_totals(old: _SideStats, new: _SideStats,
                   unreadable: set[str]) -> tuple[int, float]:
    total_old = sum(v for r, v in old.lines.items() if r not in unreadable)
    total_new = sum(v for r, v in new.lines.items() if r not in unreadable)
    delta = total_new - total_old
    return delta, _relative_delta(delta, total_old)
def _sort_growth_channels(report: GrowthReport) -> None:
    report.bloated_files.sort(key=lambda g: g.delta_lines, reverse=True)
    report.shrunk_files.sort(key=lambda g: g.delta_lines)
    report.new_files.sort(key=lambda g: g.new_lines, reverse=True)
    report.deleted_files.sort(key=lambda g: g.old_lines, reverse=True)
def _overall_growth_severity(report: GrowthReport) -> str:
    if report.bloated_files:
        return max(
            (g.severity for g in report.bloated_files),
            key=lambda s: _SEVERITY_RANK.get(s, 0),
        )
    if report.total_delta_pct >= 0.3:
        return "WARN"
    return "INFO"
def _truncate_growth_channels(report: GrowthReport, max_entries: int) -> None:
    report.bloated_total = len(report.bloated_files)
    report.shrunk_total = len(report.shrunk_files)
    report.new_total = len(report.new_files)
    report.deleted_total = len(report.deleted_files)
    report.bloated_files = report.bloated_files[:max_entries]
    report.shrunk_files = report.shrunk_files[:max_entries]
    report.new_files = report.new_files[:max_entries]
    report.deleted_files = report.deleted_files[:max_entries]
DEFAULT_GUARD_STAGE = "post"
_GUARD_STAGES = ("pre", "mid", DEFAULT_GUARD_STAGE)
def run_guard(old_dir: str, new_dir: str, stage: str = DEFAULT_GUARD_STAGE,
              rename_map: dict | None = None) -> dict:
    old_dir, new_dir = _path_arg(old_dir), _path_arg(new_dir)
    violations: list[dict] = []
    warnings: list[dict] = []
    metrics: dict = {}
    if stage not in _GUARD_STAGES:
        _log.warning(
            "run_guard: stage=%r 不在 %s 内，仅作为报告标签（三个档位执行同一"
            "完整检查集）", stage, "/".join(_GUARD_STAGES))
    missing_dirs = _missing_input_dirs(old_dir, new_dir)
    if missing_dirs:
        return _guard_dir_violation(missing_dirs, stage)
    metrics["stage"] = stage
    old_base = BaselineSnapshot(old_dir)
    new_base = BaselineSnapshot(new_dir)
    normalized_rename_map = _normalize_rename_map(rename_map)
    metrics.update(_baseline_metrics(old_base, new_base))
    _check_source_readability(old_base, new_base, metrics, violations)
    _check_red_line_limits(old_base, new_base, metrics, violations)
    _check_api_mapping(old_base, new_base, metrics, violations,
                       normalized_rename_map)
    syn_errs, sem_errs = _check_stub_syntax(new_base, metrics,
                                            violations, warnings)
    _check_subsystem_integrity(old_base, new_base, violations,
                               normalized_rename_map)
    metrics["syntax_errors"] = syn_errs
    metrics["semantic_errors"] = sem_errs
    if syn_errs or sem_errs:
        violations.append(_rule_entry(
            4, "语法/语义错误",
            f"{syn_errs} 个语法错误, {sem_errs} 个语义错误"))
    growth_report = _growth_report_from_sides(
        _side_stats_of(old_base), _side_stats_of(new_base), old_dir, new_dir,
        bloat_ratio=_DEFAULT_BLOAT_RATIO,
        bloat_lines=_DEFAULT_BLOAT_LINES,
        max_entries=_DEFAULT_MAX_ENTRIES,
    )
    metrics["growth"] = _growth_metrics(growth_report)
    warnings.extend(_growth_warnings(growth_report))
    return {
        "passed": not violations,
        "violations": violations,
        "warnings": warnings,
        "metrics": metrics,
        "growth_report": growth_report.to_dict(),
    }
def _baseline_metrics(old_base: BaselineSnapshot,
                      new_base: BaselineSnapshot) -> dict:
    return {
        "old_files": old_base.file_count,
        "new_files": new_base.file_count,
        "old_lines": old_base.total_lines,
        "new_lines": new_base.total_lines,
        "old_funcs": sum(len(v) for v in old_base.public_functions.values()),
        "new_funcs": sum(len(v) for v in new_base.public_functions.values()),
    }
def _growth_metrics(growth_report: GrowthReport) -> dict:
    return {
        "total_delta_lines": growth_report.total_delta_lines,
        "total_delta_pct": growth_report.total_delta_pct,
        "severity": growth_report.severity,
        "bloated_count": _channel_total(growth_report.bloated_total,
                                        growth_report.bloated_files),
        "shrunk_count": _channel_total(growth_report.shrunk_total,
                                       growth_report.shrunk_files),
        "new_count": _channel_total(growth_report.new_total,
                                    growth_report.new_files),
        "deleted_count": _channel_total(growth_report.deleted_total,
                                        growth_report.deleted_files),
    }
def _growth_warnings(growth_report: GrowthReport) -> list[dict]:
    return [
        _rule_entry(
            5, "文件膨胀",
            f"{gd.path}: {gd.old_lines}->{gd.new_lines} 行 "
            f"({gd.delta_lines:+d}, {gd.delta_pct:+.1%})")
        for gd in growth_report.bloated_files[:5]
    ]
def _report_count(value) -> str:
    return str(value) if is_number(value) else "0"
def _report_signed_int(value) -> str:
    if not is_number(value):
        return "+0"
    if isinstance(value, float) and not value.is_integer():
        return f"{value:+.1f}"
    return f"{int(value):+d}"
def _report_signed_pct(value) -> str:
    return f"{value:+.1%}" if is_number(value) else "+0.0%"
def _bloat_line(entry) -> str:
    if not isinstance(entry, dict):
        return f"  [?] {entry}"
    return (f"  [{entry.get('severity') or '?'}] {entry.get('path') or '?'}: "
            f"{_report_count(entry.get('old_lines'))}->"
            f"{_report_count(entry.get('new_lines'))} 行 "
            f"({_report_signed_int(entry.get('delta_lines'))}, "
            f"{_report_signed_pct(entry.get('delta_pct'))})")
def _entry_list(entries) -> list:
    if entries is None:
        return []
    if isinstance(entries, (set, frozenset)):
        return sorted(entries, key=str)
    if isinstance(entries, (list, tuple)):
        return list(entries)
    if isinstance(entries, str):
        return [entries] if entries else []
    return [entries]
def _tagged_lines(entries, dict_line, str_tag: str) -> list[str]:
    lines: list[str] = []
    for item in _entry_list(entries):
        if isinstance(item, dict):
            lines.append(dict_line(item))
        else:
            lines.append(f"  [{str_tag}] {item}")
    return lines
def _as_dict_payload(value) -> dict:
    if isinstance(value, dict):
        return value
    to_dict = getattr(value, "to_dict", None)
    if callable(to_dict):
        try:
            return dict_or_empty(to_dict())
        except (TypeError, ValueError):
            return {}
    return {}
def _growth_lines(growth) -> list[str]:
    growth = _as_dict_payload(growth)
    bloated = growth.get("bloated_files")
    if not isinstance(bloated, (list, tuple)) or not bloated:
        return []
    declared = growth.get("bloated_count")
    if finite_float_or_none(declared) is None:
        declared = growth.get("bloated_total")
    count = _channel_total(declared, bloated)
    lines = [f"膨胀文件: {count} 个（前5）:"]
    lines.extend(_bloat_line(entry) for entry in bloated[:5])
    return lines
def _passed_flag(value) -> bool:
    if value is None:
        return False
    if isinstance(value, str):
        return normalize_passed(value)
    return bool(value)
def format_guard_report(result: dict) -> str:
    result = dict_or_empty(result)
    passed = _passed_flag(result.get("passed"))
    lines = [f"重构守护判定: {'通过' if passed else '阻断'}"]
    lines += _tagged_lines(
        result.get("violations"),
        lambda v: (f"  [铁律{v.get('iron_law', '?')}] "
                   f"{v.get('rule', '')}: {v.get('detail', '')}"),
        "阻断",
    )
    lines += _tagged_lines(
        result.get("warnings"),
        lambda w: f"  [警告] {w.get('rule', '')}: {w.get('detail', '')}",
        "警告",
    )
    metrics = dict_or_empty(result.get("metrics"))
    lines.append(f"指标: {json.dumps(metrics, ensure_ascii=False, default=str)}")
    lines += _growth_lines(result.get("growth_report"))
    return "\n".join(lines)
def _dominant_version(found: list[tuple[str, str]]) -> str:
    counts: dict[str, int] = {}
    for _, ver in found:
        counts[ver] = counts.get(ver, 0) + 1
    return max(counts, key=counts.get)
def _version_target_values(target: ast.AST, value: ast.AST) -> list[str]:
    if isinstance(target, ast.Name):
        if (target.id == "__version__"
                and isinstance(value, ast.Constant)
                and isinstance(value.value, str)):
            return [value.value]
        return []
    if isinstance(target, ast.Starred):
        return []
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))):
        return []
    targets, values = target.elts, value.elts
    starred = [i for i, item in enumerate(targets)
               if isinstance(item, ast.Starred)]
    if len(starred) > 1:
        return []
    if not starred:
        if len(targets) != len(values):
            return []
        pairs = list(zip(targets, values))
    else:
        star = starred[0]
        suffix = len(targets) - star - 1
        if len(values) < len(targets) - 1:
            return []
        pairs = list(zip(targets[:star], values[:star]))
        if suffix:
            pairs.extend(zip(targets[star + 1:], values[-suffix:]))
    return [version for item, item_value in pairs
            for version in _version_target_values(item, item_value)]
def _version_assignment_value(node: ast.AST) -> str | None:
    if isinstance(node, ast.Assign):
        targets, value = node.targets, node.value
    elif isinstance(node, ast.AnnAssign):
        targets, value = [node.target], node.value
    else:
        return None
    found = [version for target in targets
             for version in _version_target_values(target, value)]
    return found[-1] if found else None
def _version_values_from_tree(tree: ast.Module) -> list[str]:
    return [value for value in map(_version_assignment_value,
                                   iter_module_level_stmts(tree.body))
            if value is not None]
def _statement_scope_header(tokens) -> bool:
    names = [tok.string for tok in tokens if tok.type == tokenize.NAME]
    if not names:
        return False
    return names[0] in ("def", "class") or names[:2] == ["async", "def"]
def _statement_version_values(tokens) -> list[str]:
    prefix_types = {tokenize.NL, tokenize.COMMENT,
                    tokenize.INDENT, tokenize.DEDENT}
    start = 0
    while start < len(tokens) and tokens[start].type in prefix_types:
        start += 1
    statement = tokens[start:]
    if not statement:
        return []
    try:
        source = tokenize.untokenize(
            [(tok.type, tok.string) for tok in statement]).lstrip()
        tree = ast.parse(source)
    except PARSE_DEGRADE_EXC as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_statement_version_values:{type(_swallowed_exc).__name__}')
        return []
    return _version_values_from_tree(tree)
def _finish_version_statement(statement: list, scope_stack: list[bool],
                              found: list[str]) -> bool:
    if not any(scope_stack):
        found.extend(_statement_version_values(statement))
    return _statement_scope_header(statement)
def _consume_version_token(tok, statement: list, scope_stack: list[bool],
                           pending_scope: bool, found: list[str]) -> tuple[bool, list]:
    if tok.type == tokenize.INDENT:
        scope_stack.append(pending_scope)
        pending_scope = False
    elif tok.type == tokenize.DEDENT:
        if scope_stack:
            scope_stack.pop()
    else:
        statement.append(tok)
    if tok.type != tokenize.NEWLINE:
        return pending_scope, statement
    return _finish_version_statement(statement, scope_stack, found), []
def _module_version_values_tokenized(content: str) -> list[str]:
    content = "\n".join(ast_split_lines(content))
    found: list[str] = []
    statement = []
    scope_stack: list[bool] = []
    pending_scope = False
    try:
        for tok in tokenize.generate_tokens(io.StringIO(content).readline):
            pending_scope, statement = _consume_version_token(
                tok, statement, scope_stack, pending_scope, found)
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError):
        _log.debug("_module_version_values_tokenized: tokenize 降级收尾",
                   exc_info=True)
    return found
def _module_version_values(content: str) -> list[str]:
    try:
        tree = ast.parse(content)
    except PARSE_DEGRADE_EXC:
        _log.debug("_module_version_values: 源码不可解析，退回 token 模式",
                   exc_info=True)
        return _module_version_values_tokenized(content)
    return _version_values_from_tree(tree)
_FILE_READ_FAILURES = (OSError, UnicodeDecodeError, SyntaxError,
                      LookupError, ValueError)
def _version_arg(value) -> str | None:
    if isinstance(value, str):
        return value.strip() or None
    return str(value) if is_number(value) else None
def _scan_dir_available(directory: str, tag: str) -> bool:
    if os.path.isdir(directory):
        return True
    _log.warning("%s: 跳过（目录不存在）dir=%s skipped=1", tag, directory)
    return False
def check_version_uniformity(directory: str, expected_version: str | None = None) -> list[dict]:
    directory = _path_arg(directory)
    expected_version = _version_arg(expected_version)
    if not _scan_dir_available(directory, "check_version_uniformity"):
        return []
    found: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for rel, fp in iter_py_source_files(directory):
        try:
            content = read_source_strict(fp)
        except _FILE_READ_FAILURES as exc:
            _log.warning("check_version_uniformity: 跳过不可读文件 %s: %s", fp, exc)
            continue
        for ver in _module_version_values(content):
            if (rel, ver) in seen:
                continue
            seen.add((rel, ver))
            found.append((rel, ver))
    if not found:
        return []
    if expected_version is None:
        expected_version = _dominant_version(found)
    mismatches = [
        {"file": rel, "version": ver, "expected": expected_version}
        for rel, ver in found
        if ver != expected_version
    ]
    _log.info("check_version_uniformity: 完成 dir=%s entries=%d mismatch=%d",
                directory, len(found), len(mismatches))
    return mismatches
_LAZY_RESIDUE_PATTERNS: list[tuple[str, str]] = [
    (r"_lazy_\w+", "惰性加载标记"),
    (r"_degraded\s*=\s*True", "退化标记"),
    (r"fallback\s*=(?!=)", "fallback 兜底"),
]
_LAZY_EXEMPT_ENV = "SAFE_CODE_LAZY_REGISTRIES"
def _lazy_exempt_names() -> set[str]:
    names: set[str] = set()
    raw = os.environ.get(_LAZY_EXEMPT_ENV, "")
    if isinstance(raw, str) and raw.strip():
        names.update(os.path.basename(item.strip()).lower()
                     for item in raw.split(os.pathsep) if item.strip())
    return names
def _lazy_issue(rel: str, line: int, pattern: str,
                code: str) -> dict[str, Any]:
    return {"file": rel, "line": line, "pattern": pattern, "code": code}
_LAZY_MASK_TOKEN_TYPES = frozenset(
    tok_type for tok_type in (
        tokenize.COMMENT,
        tokenize.STRING,
        getattr(tokenize, "FSTRING_MIDDLE", None),
    ) if tok_type is not None
)
def _mask_lazy_token(masked: list[list[str]], tok) -> None:
    (start_row, start_col), (end_row, end_col) = tok.start, tok.end
    for row in range(start_row, end_row + 1):
        if not 1 <= row <= len(masked):
            continue
        start = start_col if row == start_row else 0
        end = end_col if row == end_row else len(masked[row - 1])
        for col in range(start, min(end, len(masked[row - 1]))):
            masked[row - 1][col] = " "
def _mask_lazy_noncode_lines(lines: list[str]) -> list[str]:
    source = "\n".join(lines)
    masked = [list(line) for line in lines]
    try:
        for tok in tokenize.generate_tokens(io.StringIO(source).readline):
            if tok.type not in _LAZY_MASK_TOKEN_TYPES:
                continue
            _mask_lazy_token(masked, tok)
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError):
        _log.debug("_mask_lazy_noncode_lines: tokenize 降级收尾", exc_info=True)
    return ["".join(line) for line in masked]
def _lazy_import_lines(source: str) -> dict[int, str] | None:
    try:
        tree = ast.parse(source)
    except PARSE_DEGRADE_EXC:
        _log.debug("_lazy_import_lines: 源码不可解析，退回文本模式",
                   exc_info=True)
        return None
    found: dict[int, str] = {}
    try_types = (ast.Try,) + (
        (ast.TryStar,) if hasattr(ast, "TryStar") else ()
    )
    def visit(node: ast.AST, inside_try: bool = False,
              inside_function: bool = False) -> None:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            if inside_try:
                found[node.lineno] = "try/except import"
            elif inside_function:
                found[node.lineno] = "function import"
            return
        deferred_body = isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        child_inside_try = ((inside_try and not deferred_body)
                            or isinstance(node, try_types))
        child_inside_function = inside_function or deferred_body
        for child in ast.iter_child_nodes(node):
            visit(child, child_inside_try, child_inside_function)
    visit(tree)
    return found
def _lazy_try_import_transition(
    stripped: str, indent: int, try_indents: list[int],
) -> bool:
    while try_indents and stripped and indent <= try_indents[-1]:
        try_indents.pop()
    import_found = bool(
        try_indents and stripped
        and re.match(r"import\s+\w+|from\s+[.\w]+", stripped))
    if not try_indents and re.match(r"try\s*:\s*(#.*)?$", stripped):
        try_indents.append(indent)
    return import_found
def _scan_lazy_file_lines(rel: str, lines: list[str],
                           issues: list[dict]) -> None:
    code_lines = _mask_lazy_noncode_lines(lines)
    import_lines = _lazy_import_lines("\n".join(lines))
    try_indents: list[int] = []
    if import_lines is None:
        import_lines = {}
        for i, code in enumerate(code_lines, 1):
            stripped = code.strip()
            indent = len(code) - len(code.lstrip())
            if _lazy_try_import_transition(stripped, indent, try_indents):
                import_lines[i] = "try/except import"
    for i, line in enumerate(lines, 1):
        code = code_lines[i - 1]
        display = line.strip()
        import_pattern = import_lines.get(i)
        if import_pattern is not None:
            issues.append(
                _lazy_issue(rel, i, import_pattern, display[:80]))
        for pat, desc in _LAZY_RESIDUE_PATTERNS:
            if re.search(pat, code):
                issues.append(_lazy_issue(rel, i, desc, display[:80]))
def check_lazy_loading(directory: str) -> list[dict]:
    issues: list[dict] = []
    directory = _path_arg(directory)
    if not _scan_dir_available(directory, "check_lazy_loading"):
        return issues
    _exempt = _lazy_exempt_names()
    for rel, fp in iter_py_source_files(directory):
        if os.path.basename(fp).lower() in _exempt:
            continue
        try:
            lines = read_source_strict(fp).split("\n")
        except _FILE_READ_FAILURES:
            _log.warning("check_lazy_loading: 跳过不可读文件 %s", fp,
                           exc_info=True)
            continue
        _scan_lazy_file_lines(rel, lines, issues)
    _log.info("check_lazy_loading: 完成 dir=%s residue=%d",
                directory, len(issues))
    return issues
API_RETENTION_FLOOR = 0.90
COPY_SUSPECT_SIMILARITY = 0.98
COPY_SUSPECT_MIN_LINES = 50
SKELETON_STUB_RATIO = 0.5
@dataclass
class IntegrityResult:
    filepath: str = ""
    old_lines: int = 0
    new_lines: int = 0
    text_similarity: float = 0.0
    ast_similarity: float = 0.0
    shared_signatures: int = 0
    old_signatures: int = 0
    new_signatures: int = 0
    verdict: str = "UNKNOWN"
    evidence: str = ""
def _line_ratio(a: list[str], b: list[str]) -> float:
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    matcher = difflib.SequenceMatcher(None, a, b)
    if max(len(a), len(b)) > 30_000:
        return round(matcher.quick_ratio(), 3)
    return round(matcher.ratio(), 3)
def _ast_node_histogram(tree: ast.Module) -> dict[str, int]:
    hist: dict[str, int] = {}
    for node in walk_nodes(tree):
        name = type(node).__name__
        hist[name] = hist.get(name, 0) + 1
    return hist
def _histogram_dice(h1: dict[str, int], h2: dict[str, int]) -> float:
    total1 = sum(h1.values())
    total2 = sum(h2.values())
    if total1 == 0 and total2 == 0:
        return 1.0
    if total1 == 0 or total2 == 0:
        return 0.0
    inter = sum(min(c, h2.get(k, 0)) for k, c in h1.items())
    return round(2.0 * inter / (total1 + total2), 3)
def compare_file_integrity(old_path: str, new_path: str) -> IntegrityResult:
    old_path, new_path = _path_arg(old_path), _path_arg(new_path)
    result = IntegrityResult(filepath=old_path)
    sources = _load_integrity_sources(old_path, new_path, result)
    if sources is None:
        return result
    return _finalize_integrity(result, *sources)
def _finalize_integrity(
    result: IntegrityResult, old_source: str, new_source: str,
) -> IntegrityResult:
    if not new_source.strip():
        result.old_lines = count_lines(old_source)
        result.verdict = "NOT_MIGRATED"
        result.evidence = ("新文件为空，未产生迁移内容" if old_source.strip()
                           else "新旧文件均为空，无迁移内容")
        return result
    if not _fill_integrity_similarity(result, old_source, new_source):
        return result
    _judge_integrity(result)
    return result
def _read_source_or_empty(path: str) -> tuple[str, bool]:
    try:
        return read_source_strict(path), False
    except OSError:
        _log.debug(
            "assess_honest_progress: 新文件读取失败按未证实完成计入骨架: %s",
            path, exc_info=True)
        return "", True
def _load_integrity_sources(
    old_path: str, new_path: str, result: IntegrityResult,
) -> tuple[str, str] | None:
    if not os.path.isfile(old_path):
        result.verdict = "NOT_MIGRATED"
        result.evidence = f"旧文件不存在: {old_path}"
        return None
    try:
        old_source = read_source_strict(old_path)
    except OSError as exc:
        log_swallowed(
            __name__, exc,
            context=f'_load_integrity_sources:{type(exc).__name__}')
        result.verdict = "SYNTAX_ERROR"
        result.evidence = f"读取失败: {exc}"
        return None
    if not os.path.isfile(new_path):
        result.old_lines = count_lines(old_source)
        result.verdict = "NOT_MIGRATED"
        result.evidence = f"新文件缺失: {new_path}"
        return None
    try:
        return old_source, read_source_strict(new_path)
    except OSError as exc:
        log_swallowed(
            __name__, exc,
            context=f'_load_integrity_sources:{type(exc).__name__}')
        result.old_lines = count_lines(old_source)
        result.verdict = "SYNTAX_ERROR"
        result.evidence = f"读取失败: {exc}"
        return None
def _fill_integrity_similarity(
    result: IntegrityResult, old_source: str, new_source: str,
) -> bool:
    result.old_lines = count_lines(old_source)
    result.new_lines = count_lines(new_source)
    result.text_similarity = _line_ratio(
        old_source.splitlines(), new_source.splitlines())
    try:
        old_tree = ast.parse(old_source)
        new_tree = ast.parse(new_source)
        compile(old_tree, "<old>", "exec")
        compile(new_tree, "<new>", "exec")
    except PARSE_DEGRADE_EXC as exc:
        log_swallowed(
            __name__, exc,
            context=f'_fill_integrity_similarity:{type(exc).__name__}')
        result.verdict = "SYNTAX_ERROR"
        result.evidence = f"源码编译失败: {exc}"
        return False
    result.ast_similarity = _histogram_dice(
        _ast_node_histogram(old_tree), _ast_node_histogram(new_tree))
    old_sigs = set(extract_public_names(old_source))
    new_sigs = set(extract_public_names(new_source))
    result.old_signatures = len(old_sigs)
    result.new_signatures = len(new_sigs)
    result.shared_signatures = len(old_sigs & new_sigs)
    return True
def _judge_integrity(result: IntegrityResult) -> None:
    if (result.text_similarity > COPY_SUSPECT_SIMILARITY
            and result.old_lines >= COPY_SUSPECT_MIN_LINES):
        result.verdict = "COPY_SUSPECT"
        result.evidence = (
            f"文本相似度 {result.text_similarity:.1%}（>{COPY_SUSPECT_SIMILARITY:.0%}），"
            f"疑为原样复制而非逐文件重写")
    elif result.text_similarity >= 0.90:
        result.verdict = "REWRITE_LIGHT"
        result.evidence = (
            f"文本相似度 {result.text_similarity:.1%}，轻改写（合规但需关注）")
    else:
        result.verdict = "REWRITTEN"
        result.evidence = (
            f"文本相似度 {result.text_similarity:.1%}，实质重写，"
            f"共享公开签名 {result.shared_signatures}/{result.old_signatures}")
@dataclass
class HonestProgressReport:
    old_dir: str = ""
    new_dir: str = ""
    total_old_files: int = 0
    migrated_files: int = 0
    pending_files: list[str] = field(default_factory=list)
    skeleton_files: list[str] = field(default_factory=list)
    real_done: int = 0
    pending: int = 0
    stub_ratio: float = 0.0
    api_retention: float = 0.0
    code_retention: float = 0.0
    copy_suspects: list[str] = field(default_factory=list)
    verdict: str = "UNKNOWN"
    honest_assessment: str = ""
    generated_at: float = 0.0
    def to_dict(self) -> dict[str, Any]:
        return {
            "old_dir": self.old_dir,
            "new_dir": self.new_dir,
            "total_old_files": self.total_old_files,
            "migrated_files": self.migrated_files,
            "pending_files": self.pending_files,
            "skeleton_files": self.skeleton_files,
            "real_done": self.real_done,
            "pending": self.pending,
            "stub_ratio": round(self.stub_ratio, 3),
            "api_retention": round(self.api_retention, 3),
            "code_retention": round(self.code_retention, 3),
            "copy_suspects": self.copy_suspects,
            "verdict": self.verdict,
            "honest_assessment": self.honest_assessment,
            "generated_at": self.generated_at,
        }
_RESIDUE_DIR_PREFIXES = (".", "__")
def _is_residue_segment(name: str) -> bool:
    return (name.startswith(_RESIDUE_DIR_PREFIXES)
            or is_backup_like_dir(name)
            or is_temp_artifact_dir(name))
def _has_residue_dir(rel: str) -> bool:
    return any(_is_residue_segment(seg) for seg in rel.split("/")[:-1])
def collect_py_source_files(root_dir: str) -> list[str]:
    root_dir = _path_arg(root_dir)
    if not os.path.isdir(root_dir):
        return []
    return sorted(
        rel for rel in (
            os.path.relpath(fp, root_dir).replace(os.sep, "/")
            for fp in collect_migration_py_files(root_dir))
        if not _has_residue_dir(rel))
def _parsable(source: str) -> bool:
    try:
        compile(source, "<_parsable>", "exec")
    except PARSE_DEGRADE_EXC:
        _log.debug("_parsable: 语法失败按不可编译计入", exc_info=True)
        return False
    return True
def _source_stats(source: str) -> tuple[int, int, int]:
    try:
        tree = ast.parse(source)
    except PARSE_DEGRADE_EXC:
        _log.debug("_source_stats: 语法失败按零函数零桩零实现计入", exc_info=True)
        return (0, 0, 0)
    stubs, total = _count_stub_functions(tree)
    return total, stubs, count_meaningful_stmts(tree.body)
@dataclass
class _MigrationEvidence:
    migrated_files: int = 0
    pending_files: list[str] = field(default_factory=list)
    skeleton_files: list[str] = field(default_factory=list)
    copy_suspects: list[str] = field(default_factory=list)
    similarities: list[float] = field(default_factory=list)
    total_funcs: int = 0
    total_stubs: int = 0
def _is_unproven_migration(new_source: str, read_failed: bool,
                           funcs: int, stubs: int, old_source: str | None,
                           old_funcs: int, old_meaningful: int,
                           new_meaningful: int) -> bool:
    if read_failed or (bool(new_source) and not _parsable(new_source)):
        return True
    if old_source is not None:
        if old_source.strip() and not new_source.strip():
            return True
        if old_funcs > 0 and funcs == 0:
            return True
        if old_meaningful > 0 and new_meaningful == 0:
            return True
    return funcs > 0 and stubs / funcs > SKELETON_STUB_RATIO
def _collect_migration_evidence(old_dir: str, new_dir: str,
                                 old_files: list[str]) -> _MigrationEvidence:
    ev = _MigrationEvidence()
    for rel in old_files:
        old_path = os.path.join(old_dir, rel)
        new_path = os.path.join(new_dir, rel)
        if not os.path.isfile(new_path):
            ev.pending_files.append(rel)
            continue
        ev.migrated_files += 1
        integrity = IntegrityResult(filepath=old_path)
        sources = _load_integrity_sources(old_path, new_path, integrity)
        old_source: str | None = None
        if sources is None:
            new_source, _ = _read_source_or_empty(new_path)
            _read_failed = True
        else:
            old_source, new_source = sources
            integrity = _finalize_integrity(integrity, old_source, new_source)
            _read_failed = False
        ev.similarities.append(integrity.text_similarity)
        if integrity.verdict == "COPY_SUSPECT":
            ev.copy_suspects.append(rel)
        old_funcs = 0
        old_meaningful = 0
        if old_source is not None:
            old_funcs, _old_stubs, old_meaningful = _source_stats(old_source)
        funcs, stubs, new_meaningful = _source_stats(new_source)
        ev.total_funcs += funcs
        ev.total_stubs += stubs
        if _is_unproven_migration(
                new_source, _read_failed, funcs, stubs, old_source,
                old_funcs, old_meaningful, new_meaningful):
            ev.skeleton_files.append(rel)
    return ev
def _honest_verdict(report: HonestProgressReport) -> str:
    if report.migrated_files == 0:
        return "NOT_STARTED"
    if report.real_done == 0:
        return "SKELETON_ONLY"
    if (report.api_retention < API_RETENTION_FLOOR
            or report.migrated_files < report.total_old_files * 0.8):
        return "PARTIAL"
    if (report.pending or report.copy_suspects
            or report.api_retention < 0.95 or report.skeleton_files):
        return "MOSTLY_DONE"
    return "HONEST_COMPLETE"
def _honest_assessment_text(report: HonestProgressReport) -> str:
    parts = [
        (
            f"旧目录 {report.total_old_files} 个 .py 文件：已迁移 "
            f"{report.migrated_files}（骨架 {len(report.skeleton_files)} / 真实 "
            f"{report.real_done}），未迁移 {report.pending}。"
        ),
        (
            f"公开 API 覆盖度 {report.api_retention:.1%}"
            f"（约束红线 {API_RETENTION_FLOOR:.0%}），"
            f"新目录空桩率 {report.stub_ratio:.1%}。"
        ),
    ]
    if report.copy_suspects:
        parts.append(f"复制嫌疑文件 {len(report.copy_suspects)} 个："
                     f"{', '.join(report.copy_suspects[:5])}"
                     f"{'…' if len(report.copy_suspects) > 5 else ''}。")
    parts.append(f"裁决: {report.verdict}")
    return " ".join(parts)
def _apply_migration_evidence(
    report: HonestProgressReport, ev: _MigrationEvidence,
) -> None:
    report.migrated_files = ev.migrated_files
    report.pending_files = ev.pending_files
    report.skeleton_files = ev.skeleton_files
    report.copy_suspects = ev.copy_suspects
    report.pending = len(ev.pending_files)
    report.real_done = ev.migrated_files - len(ev.skeleton_files)
    report.stub_ratio = ev.total_stubs / max(ev.total_funcs, 1)
    report.code_retention = (
        sum(ev.similarities) / len(ev.similarities) if ev.similarities else 0.0)
def _api_retention(old_dir: str, new_dir: str,
                   scope_files: list[str]) -> float:
    scope = set(scope_files)
    old_keys = _public_function_keys(BaselineSnapshot(old_dir), scope)
    new_keys = _public_function_keys(BaselineSnapshot(new_dir), scope)
    return len(old_keys & new_keys) / len(old_keys) if old_keys else 1.0
def _public_function_keys(snapshot: BaselineSnapshot,
                          scope: set[str]) -> set[tuple[str, str]]:
    return {(rel, name) for rel, funcs in snapshot.public_functions.items()
            if rel in scope for name in funcs}
def assess_honest_progress(old_dir: str, new_dir: str) -> HonestProgressReport:
    old_dir, new_dir = _path_arg(old_dir), _path_arg(new_dir)
    report = HonestProgressReport(
        old_dir=os.path.abspath(old_dir) if old_dir else "",
        new_dir=os.path.abspath(new_dir) if new_dir else "",
        generated_at=time.time(),
    )
    _log.info("assess_honest_progress: 开始 old=%s new=%s", old_dir, new_dir)
    old_files = collect_py_source_files(old_dir)
    report.total_old_files = len(old_files)
    if not old_files:
        report.verdict = "UNKNOWN"
        report.honest_assessment = f"旧目录无 .py 文件: {old_dir}"
        _log.info("assess_honest_progress: 完成 old=%s new=%s verdict=%s "
                    "(旧目录无 .py 文件)", old_dir, new_dir, report.verdict)
        return report
    ev = _collect_migration_evidence(old_dir, new_dir, old_files)
    _apply_migration_evidence(report, ev)
    report.api_retention = _api_retention(old_dir, new_dir, old_files)
    report.verdict = _honest_verdict(report)
    report.honest_assessment = _honest_assessment_text(report)
    _log.info(
        "assess_honest_progress: 完成 old=%s new=%s verdict=%s "
        "migrated=%d/%d real_done=%d pending=%d api_retention=%.3f "
        "copy_suspects=%d",
        old_dir, new_dir, report.verdict, report.migrated_files,
        report.total_old_files, report.real_done, report.pending,
        report.api_retention, len(report.copy_suspects))
    return report

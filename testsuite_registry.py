from __future__ import annotations

import ast
import importlib
import json
import logging
import os
from collections import Counter
from collections.abc import Iterable, Iterator, Mapping, MutableMapping
from dataclasses import dataclass, field, replace
from enum import IntEnum
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_shared_source_core import parse_cached
from jwsgj.diag_testing_coverage import (
    CoverageMap,
    resolve_project_path,
)
from jwsgj.diag_testing_source import iter_test_py_files
from jwsgj.diag_testing_test_index import (
    iter_collectable_test_functions,
    load_test_ast,
)
from jwsgj.diag_types_defs import (
    PreinterventionResult,
    TestMethodResult,
    finish_check,
    make_detail,
    result_status_bucket,
)
from jwsgj.diag_types_normalize import (
    as_number,
    clamp_unit,
    is_finite_num,
    is_pure_int,
    normalize_input,
    normalize_path_list,
    normalize_py_filename,
    safe_float,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    RESULT_STATUS_BUCKETS,
    register_check_provider,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    TEST_DIR_CANDIDATES,
    TEST_DIR_CANDIDATES_LOWER,
    is_pruned_scan_dir,
    is_test_source_basename,
    scan_prune_dirs,
)

METHOD_MODE_PARALLEL = "parallel"
METHOD_MODE_SERIAL_CACHE = "serial_cache"
METHOD_MODE_SERIAL_TIMEOUT = "serial_timeout"
_METHOD_TIMEOUT_QUICK = 15.0
_METHOD_TIMEOUT_STANDARD = 30.0
_METHOD_TIMEOUT_MUTATION = 60.0
_METHOD_TIMEOUT_LONG = 180.0
@dataclass(frozen=True)
class MethodSpec:
    __test__ = False
    name_zh: str
    impl: str
    timeout: float | None = None
    mode: str = METHOD_MODE_PARALLEL
METHOD_SPECS: dict[str, MethodSpec] = {
    "unit_test": MethodSpec(
        "单元测试", "diag_testing_runtime:run_unit_tests",
        _METHOD_TIMEOUT_LONG,
        METHOD_MODE_SERIAL_CACHE),
    "static_analysis": MethodSpec(
        "静态代码检查", "diag_testing_static:run_static_analysis",
        _METHOD_TIMEOUT_QUICK),
    "coverage": MethodSpec(
        "覆盖率度量", "diag_testing_coverage:run_coverage_analysis"),
    "integration_test": MethodSpec(
        "集成测试", "diag_testing_runtime:run_integration_tests",
        _METHOD_TIMEOUT_LONG,
        METHOD_MODE_SERIAL_TIMEOUT),
    "regression_test": MethodSpec(
        "回归测试", "refactor_post_validation:run_regression_tests"),
    "sca": MethodSpec("软件成分分析", "diag_testing_scan_sca:run_sca"),
    "smoke_test": MethodSpec("冒烟测试", "build_arch_gate:run_smoke_tests"),
    "e2e_test": MethodSpec(
        "端到端测试", "diag_testing_runtime:run_e2e_tests",
        _METHOD_TIMEOUT_QUICK),
    "performance": MethodSpec(
        "性能剖析", "diag_testing_perf:run_performance_profiling",
        _METHOD_TIMEOUT_QUICK),
    "compatibility": MethodSpec(
        "兼容性测试", "diag_testing_static:run_compatibility_tests"),
    "fuzz_test": MethodSpec(
        "模糊测试", "diag_testing_scan_ast:run_fuzz_tests", _METHOD_TIMEOUT_STANDARD),
    "stress_test": MethodSpec(
        "压力测试", "diag_testing_perf:run_stress_tests", _METHOD_TIMEOUT_QUICK),
    "mutation_test": MethodSpec(
        "突变测试", "diag_testing_mutation:run_mutation_tests",
        _METHOD_TIMEOUT_MUTATION,
        METHOD_MODE_SERIAL_TIMEOUT),
    "false_negative_probe": MethodSpec(
        "漏报注入探针", "diag_testing_mutation:run_false_negative_probe",
        _METHOD_TIMEOUT_QUICK,
        METHOD_MODE_SERIAL_CACHE),
    "complexity": MethodSpec(
        "代码复杂度度量", "diag_testing_perf_metrics:run_complexity_analysis",
        _METHOD_TIMEOUT_STANDARD),
    "architecture": MethodSpec(
        "架构测试", "build_arch_gate:run_architecture_tests",
        _METHOD_TIMEOUT_STANDARD),
    "contract_test": MethodSpec(
        "契约测试", "diag_testing_static:run_contract_tests"),
    "security_test": MethodSpec(
        "安全测试", "diag_testing_scan_ast:run_security_tests"),
}
METHOD_NAMES_ZH: dict[str, str] = {
    mid: spec.name_zh for mid, spec in METHOD_SPECS.items()}
_PROVIDER_MODULES: dict[str, Any] = {}
_PROVIDER_MODULE_NAMES = frozenset(
    spec.impl.partition(":")[0] for spec in METHOD_SPECS.values())
def _provider_module(module_name: str) -> Any:
    if module_name not in _PROVIDER_MODULE_NAMES:
        raise LookupError(f"未登记的方法实现域: {module_name}")
    module = _PROVIDER_MODULES.get(module_name)
    if module is None:
        package = __package__ or __name__.rpartition(".")[0]
        qualified = f"{package}.{module_name}" if package else module_name
        module = importlib.import_module(qualified)
        _PROVIDER_MODULES[module_name] = module
    return module
def _resolve_method_impl(spec: MethodSpec) -> Any:
    module_name, _, attr = spec.impl.partition(":")
    module = _provider_module(module_name)
    func = getattr(module, attr, None)
    if not callable(func):
        raise ImportError(f"方法实现不可调用: {spec.impl}")
    return func
class MethodImpls(MutableMapping):
    __test__ = False
    def __init__(self, specs: Mapping[str, MethodSpec]) -> None:
        self._specs = specs
        self._ids: list[str] = list(specs)
        self._impls: dict[str, Any] = {}
    def __getitem__(self, method_id: str) -> Any:
        if method_id not in self._ids:
            raise KeyError(method_id)
        if method_id not in self._impls:
            self._impls[method_id] = _resolve_method_impl(
                self._specs[method_id])
        return self._impls[method_id]
    def __setitem__(self, method_id: str, func: Any) -> None:
        if method_id not in self._ids:
            self._ids.append(method_id)
        self._impls[method_id] = func
    def __delitem__(self, method_id: str) -> None:
        if method_id not in self._ids:
            raise KeyError(method_id)
        self._ids.remove(method_id)
        self._impls.pop(method_id, None)
    def __contains__(self, method_id: object) -> bool:
        return method_id in self._ids
    def __iter__(self) -> Iterator[str]:
        return iter(self._ids)
    def __len__(self) -> int:
        return len(self._ids)
__all__ = [
    'ACTIVE_RULES_BY_LEVEL',
    'CONFIDENCE_MULTIPLIER_BY_LEVEL',
    'FALLBACK_TABLE',
    'METHOD_MODE_PARALLEL',
    'METHOD_MODE_SERIAL_CACHE',
    'METHOD_MODE_SERIAL_TIMEOUT',
    'METHOD_NAMES_ZH',
    'METHOD_SPECS',
    'RUN_STATUS_VALUES',
    'ConfidenceScorer',
    'MethodImpls',
    'MethodSpec',
    'RuleFallback',
    'TestMaturityLevel',
    'TestMetadata',
    'TestRegistry',
    'assess_test_maturity',
    'build_suite_diagnostic_summary',
    'check_test_skeleton',
    'coerce_result_view',
    'count_source_files',
    'get_confidence_multiplier',
    'get_rule_fallback',
    'get_test_maturity_report',
    'score_suite_confidence',
    'score_suite_finding',
    'test_asset_dirs',
    'test_asset_files',
    'test_tree_dirs',
]
logger = logging.getLogger(__name__)
logger.addHandler(logging.NullHandler())
_CONFIDENCE_DEFENSE_EXC = (
    KeyError, TypeError, ValueError, AttributeError, ZeroDivisionError)
def _degradation_record(method_id: str, field: str, dropped: int,
                        reason: str, offender_types: list | None = None) -> dict:
    record = {
        'method_id': method_id, 'field': field,
        'dropped': dropped, 'reason': reason,
    }
    if offender_types:
        record['offender_types'] = offender_types
    return record
def _result_field(result, name: str):
    if isinstance(result, Mapping):
        return result.get(name)
    return getattr(result, name, None)
def _normalize_findings_field(method_id: str, result,
                              degradation: list[dict]) -> list[dict]:
    findings_raw = _result_field(result, 'findings')
    if isinstance(findings_raw, (str, bytes, bytearray, Mapping)):
        degradation.append(_degradation_record(
            method_id, 'findings', 1,
            f'findings 容器非法（{type(findings_raw).__name__}），按空处理'))
        return []
    if isinstance(findings_raw, Iterable) and not isinstance(
            findings_raw, (list, tuple)):
        try:
            findings_raw = list(findings_raw)
        except TypeError as e:
            logger.warning('[Confidence] %s findings 物化失败: %s',
                           method_id, e)
            degradation.append(_degradation_record(
                method_id, 'findings', 1,
                f'findings 迭代失败（{type(e).__name__}），按空处理'))
            return []
    if isinstance(findings_raw, (list, tuple)):
        kept = [f for f in findings_raw if isinstance(f, dict)]
        if len(kept) != len(findings_raw):
            degradation.append(_degradation_record(
                method_id, 'findings', len(findings_raw) - len(kept),
                'findings 含非 dict 条目，已剔除',
                sorted({type(f).__name__ for f in findings_raw
                        if not isinstance(f, dict)})[:5]))
        return kept
    if findings_raw is not None:
        degradation.append(_degradation_record(
            method_id, 'findings', 1,
            f'findings 非可迭代容器（{type(findings_raw).__name__}），按空处理'))
    return []
def _normalize_metrics_field(method_id: str, result,
                             degradation: list[dict]) -> dict:
    metrics_raw = _result_field(result, 'metrics')
    if isinstance(metrics_raw, Mapping):
        return dict(metrics_raw)
    if metrics_raw is not None:
        degradation.append(_degradation_record(
            method_id, 'metrics', 1,
            f'metrics 非 Mapping（{type(metrics_raw).__name__}），按空处理'))
    return {}
def _coerce_result_status(value) -> str | None:
    if not isinstance(value, str):
        return None
    token = value.strip().lower()
    return token if token in RESULT_STATUS_BUCKETS else None
def _coerce_result_number(value) -> int | float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return value if is_finite_num(value) else None
def _as_elapsed_ms(value) -> float:
    try:
        result = float(value)
    except (OverflowError, TypeError, ValueError):
        return 0.0
    return result if is_finite_num(result) else 0.0
def _as_result_findings(value) -> list:
    return list(value) if isinstance(value, (list, tuple)) else []
def _as_result_metrics(value) -> dict:
    return dict(value) if isinstance(value, Mapping) else {}
def coerce_result_view(
        method_id: str, result, *, findings: list | None = None,
        metrics: dict | None = None,
        degradation: list[dict] | None = None) -> TestMethodResult:
    records = degradation if degradation is not None else []
    if isinstance(result, TestMethodResult):
        view = replace(result)
        view.findings = (_as_result_findings(findings)
                         if findings is not None
                         else _as_result_findings(view.findings))
        view.metrics = (dict(metrics) if metrics is not None
                        else _as_result_metrics(view.metrics))
        return view
    if isinstance(result, Mapping):
        status = _coerce_result_status(result.get('status'))
        score = _coerce_result_number(result.get('score'))
        if status is None:
            status = 'skip'
            records.append(_degradation_record(
                method_id, 'status', 1,
                f'status 缺失或非法（{result.get("status")!r}），按 skip 处理'))
            if score not in (None, 0):
                records.append(_degradation_record(
                    method_id, 'score', 1,
                    f'status 缺失或非法，score={score!r} 不作为证据，按 0 处理'))
            score = 0
        elif score is None:
            score = 0
            if 'score' in result:
                records.append(_degradation_record(
                    method_id, 'score', 1,
                    f'score 非法（{result.get("score")!r}），按 0 处理'))
        elapsed = _coerce_result_number(result.get('elapsed_ms'))
        if elapsed is None:
            elapsed = 0.0
            if 'elapsed_ms' in result:
                records.append(_degradation_record(
                    method_id, 'elapsed_ms', 1,
                    f'elapsed_ms 非法（{result.get("elapsed_ms")!r}），按 0 处理'))
        raw_name = result.get('method_name')
        method_name = (raw_name if isinstance(raw_name, str)
                       and raw_name.strip() else str(method_id))
        summary = result.get('summary')
        if summary is not None and not isinstance(summary, str):
            records.append(_degradation_record(
                method_id, 'summary', 1,
                f'summary 非 str（{type(summary).__name__}），按空处理'))
            summary = ''
        error = result.get('error')
        if error is not None and not isinstance(error, str):
            records.append(_degradation_record(
                method_id, 'error', 1,
                f'error 非 str（{type(error).__name__}），按 None 处理'))
            error = None
        return TestMethodResult(
            method_name=method_name,
            method_id=str(method_id),
            status=status,
            score=score,
            findings=(_as_result_findings(findings) if findings is not None
                      else _as_result_findings(result.get('findings'))),
            metrics=(dict(metrics) if metrics is not None
                     else _as_result_metrics(result.get('metrics'))),
            summary=summary or '',
            error=error,
            elapsed_ms=_as_elapsed_ms(elapsed),
        )
    records.append(_degradation_record(
        method_id, 'result', 0,
        f'结果对象非 TestMethodResult/Mapping（{type(result).__name__}），'
        '降级为 skip 占位'))
    return TestMethodResult(
        method_name=str(method_id), method_id=str(method_id),
        status='skip', score=0,
        findings=_as_result_findings(findings) if findings is not None else [],
        metrics=dict(metrics) if metrics is not None else {},
        summary='', error=None, elapsed_ms=0.0)
CONFIDENCE_LEVELS: tuple[str, ...] = (
    "confirmed", "likely", "possible", "unlikely", "false_positive",
)
def finding_type(finding: dict) -> str:
    return str(finding.get('type') or finding.get('dependency')
               or finding.get('check') or '')
def _dict_findings(method_id: str, result: TestMethodResult) -> Iterator[dict]:
    findings = result.findings
    if findings is None:
        return
    if not isinstance(findings, (list, tuple)):
        logger.warning(
            '[Confidence] %s 结果 findings 容器形态非法(%s)，整方法跳过评分与交叉验证',
            method_id, type(findings).__name__)
        return
    for finding in findings:
        if not isinstance(finding, dict):
            logger.warning(
                '[Confidence] %s 结果含非 dict finding(%s)，跳过评分与交叉验证',
                method_id, type(finding).__name__)
            continue
        yield finding
def _score_cache_key(finding: dict) -> str:
    return json.dumps(
        [finding_type(finding),
         _cache_key_part(finding.get('file')),
         _cache_key_part(finding.get('line'))],
        ensure_ascii=False)
def _cache_key_part(value) -> str:
    if value is None or isinstance(value, bool):
        return ''
    if isinstance(value, float) and value.is_integer():
        return str(int(value))
    return str(value)
def _method_metrics(result: TestMethodResult) -> dict:
    metrics = result.metrics
    return metrics if isinstance(metrics, dict) else {}
def _pct(part: int, total: int) -> float:
    return round(part / max(total, 1) * 100, 1)
def _evaluate_rule_trigger(rule: dict, method_result: TestMethodResult) -> float:
    if rule.get('logic') == 'metric_threshold':
        return _metric_threshold_trigger(rule, method_result)
    return _status_trigger(rule, method_result)
def _metric_threshold_trigger(rule: dict, method_result: TestMethodResult) -> float:
    metric_name = rule.get('metric', '')
    metrics = _method_metrics(method_result)
    if metric_name not in metrics:
        return 0.0
    metric_value = metrics[metric_name]
    if not (is_pure_int(metric_value) or is_finite_num(metric_value)):
        return 0.0
    threshold = as_number(rule.get('threshold'))
    if 'below' in rule and metric_value < threshold:
        return as_number(rule.get('below'))
    if 'above' in rule and metric_value > threshold:
        return as_number(rule.get('above'))
    return 0.0
def _status_trigger(rule: dict, method_result: TestMethodResult) -> float:
    logic = rule.get('logic')
    status = result_status_bucket(method_result.status)
    if logic in ('pass_supports', 'pass_refutes'):
        triggered = status == 'pass'
    elif logic in ('fail_supports', 'fail_refutes'):
        triggered = status in ('fail', 'warn')
    else:
        return 0.0
    if not triggered:
        return 0.0
    return as_number(rule.get('weight'))
_BASE_CONFIDENCE: dict[str, float] = {
    'bare_except': 0.50, 'broad_except': 0.60,
    'long_function': 0.60,
    'mutable_default': 0.75, 'unreachable_code': 0.60, 'none_comparison': 0.55,
    'unused_import': 0.70, 'mutable_global': 0.55, 'hardcoded_credential': 0.75,
    'duplicate_code': 0.55, 'shadowing_builtin': 0.45, 'global_statement': 0.50,
    'todo_marker': 0.60, 'missing_docstring': 0.40, 'chained_comparison': 0.70,
    'empty_except': 0.65, 'self_assignment': 0.80, 'constant_comparison': 0.70,
    'duplicate_string': 0.50, 'unused_definition': 0.60,
    'sql_injection': 0.80, 'path_traversal': 0.75, 'command_injection': 0.80,
    'ssrf': 0.70, 'xxe': 0.75, 'insecure_deserialization': 0.85,
    'debug_mode': 0.85, 'hardcoded_address': 0.65, 'weak_hash': 0.85,
    'insecure_tempfile': 0.80, 'insecure_xml': 0.75, 'version_conflict': 0.90,
    'circular_dependency': 0.85, 'broken_cross_call': 0.80,
    'module_level_call': 0.75, 'lazy_import': 0.70, 'conditional_import': 0.70,
    'excessive_coupling': 0.85, 'god_module': 0.85, 'orphan_module': 0.65,
    'layer_violation': 0.80, 'dependency_direction': 0.80,
    'dependency_inversion': 0.70, 'all_inconsistency': 0.85,
    'transitive_coupling': 0.75, 'unstable_dependency': 0.70,
    'naming_cluster': 0.80, 'fat_interface': 0.75,
    'srp_violation': 0.75, 'ocp_violation': 0.70,
    'too_many_params': 0.90, 'deep_nesting': 0.90,
    'low_cohesion': 0.75, 'high_rfc': 0.75,
    'slow_under_stress': 0.80, 'memory_error': 0.90,
    'crash_under_stress': 0.85, 'file_handle_leak': 0.85,
    'inconsistent_output': 0.90, 'unbounded_recursion': 0.80,
    'generator_io': 0.70, 'format_in_loop': 0.75,
    'crash': 0.90, 'type_confusion_crash': 0.85,
    'mutation_crash': 0.85, 'nested_crash': 0.85,
    'score_regression': 0.85, 'breakpoint_increase': 0.80,
    'orphan_increase': 0.75, 'syntax_error': 0.95,
    'blindspot_increase': 0.75, 'api_removed_functions': 0.90,
    'api_removed_classes': 0.90, 'signature_change': 0.85,
    'new_circular_import': 0.85, 'dead_code_increase': 0.80,
    'test_failure': 0.85, 'test_failures': 0.85, 'test_error': 0.85,
    'api_added_functions': 0.70,
    'new_files': 0.70, 'behavior_change': 0.70,
    'deprecated_api': 0.85, 'version_incompatibility': 0.90,
    'missing_annotations': 0.80, 'relative_import': 0.70,
    'assert_in_production': 0.75, 'deprecated_stdlib': 0.85,
    'unnecessary_coding_decl': 0.90,
    'init_parse': 0.90, 'init_exists': 0.95, 'syntax': 0.95,
    'version': 0.85, 'circular_import': 0.85, 'public_api': 0.85,
    'module_docstring': 0.80, 'entry_reachable': 0.75,
    'entry_signature': 0.80, 'entry_return_annotation': 0.75,
    'md_version': 0.80, 'md_changelog': 0.75, 'md_too_short': 0.80,
    '_default': 0.70,
}
_CROSS_VALIDATION_RULES: dict[str, list[dict]] = {
    'unused_definition': [
        {'method': 'coverage', 'logic': 'metric_threshold',
         'metric': 'function_coverage_pct', 'threshold': 50, 'below': -0.15,
         'desc': '低覆盖率佐证不可靠，未使用判定降权待运行时证据复核'},
        {'method': 'mutation_test', 'logic': 'pass_refutes',
         'weight': -0.10,
         'desc': '突变测试通过说明代码有活跃的测试验证'},
        {'method': 'fuzz_test', 'logic': 'fail_supports',
         'weight': +0.10,
         'desc': '模糊测试崩溃说明代码被实际调用'},
    ],
    'orphan_module': [
        {'method': 'integration_test', 'logic': 'pass_refutes',
         'weight': -0.15,
         'desc': '集成测试导入成功说明模块并非真正孤立'},
        {'method': 'e2e_test', 'logic': 'pass_refutes',
         'weight': -0.10,
         'desc': 'E2E测试完整导入说明模块可达'},
    ],
    'circular_dependency': [
        {'method': 'integration_test', 'logic': 'metric_threshold',
         'metric': 'circular_dependencies', 'threshold': 0, 'above': +0.10,
         'desc': '集成测试也检测到循环依赖→确认'},
        {'method': 'smoke_test', 'logic': 'fail_supports',
         'weight': +0.10,
         'desc': '冒烟测试失败说明循环依赖已影响结构'},
    ],
    'broad_except': [
        {'method': 'fuzz_test', 'logic': 'fail_supports',
         'weight': +0.10,
         'desc': '模糊测试触发异常说明except确实在捕获'},
        {'method': 'stress_test', 'logic': 'fail_supports',
         'weight': +0.05,
         'desc': '压力测试触发异常说明except在实际场景中执行'},
    ],
    'empty_except': [
        {'method': 'fuzz_test', 'logic': 'fail_supports',
         'weight': +0.10,
         'desc': '模糊测试崩溃可能源于空except吞没异常'},
    ],
    'long_function': [
        {'method': 'coverage', 'logic': 'metric_threshold',
         'metric': 'overall_coverage_pct', 'threshold': 50, 'below': -0.10,
         'desc': '低覆盖率佐证不可靠，复杂度判定降权复核'},
        {'method': 'mutation_test', 'logic': 'metric_threshold',
         'metric': 'mutation_score', 'threshold': 50, 'below': -0.10,
         'desc': '低突变分数佐证不可靠，复杂度判定降权复核'},
    ],
    'unreachable_code': [
        {'method': 'e2e_test', 'logic': 'metric_threshold',
         'metric': 'workflow_completeness_pct', 'threshold': 80, 'above': +0.05,
         'desc': '高工作流完整性说明诊断环境可信，不可达判定更可信'},
    ],
    'broken_cross_call': [
        {'method': 'integration_test', 'logic': 'fail_supports',
         'weight': +0.15,
         'desc': '集成测试导入失败确认调用链断裂'},
        {'method': 'e2e_test', 'logic': 'fail_supports',
         'weight': +0.10,
         'desc': 'E2E测试失败确认跨模块调用不可达'},
    ],
    'slow_under_stress': [
        {'method': 'stress_test', 'logic': 'fail_supports',
         'weight': +0.15,
         'desc': '压力测试确认性能问题'},
    ],
    'file_handle_leak': [
        {'method': 'stress_test', 'logic': 'fail_supports',
         'weight': +0.10,
         'desc': '压力测试触发资源问题确认泄漏'},
    ],
    'api_removed_functions': [
        {'method': 'regression_test', 'logic': 'fail_supports',
         'weight': +0.15,
         'desc': '回归测试确认API变更导致问题'},
    ],
    'duplicate_code': [
        {'method': 'coverage', 'logic': 'metric_threshold',
         'metric': 'overall_coverage_pct', 'threshold': 40, 'below': -0.10,
         'desc': '低覆盖率佐证不可靠，重复代码判定降权复核'},
    ],
    'low_cohesion': [
        {'method': 'complexity', 'logic': 'metric_threshold',
         'metric': 'avg_cyclomatic_complexity', 'threshold': 15, 'above': +0.05,
         'desc': '高复杂度+低内聚=重构紧迫性更高'},
    ],
    'srp_violation': [
        {'method': 'complexity', 'logic': 'metric_threshold',
         'metric': 'avg_cyclomatic_complexity', 'threshold': 15, 'above': +0.05,
         'desc': '高复杂度+多职责=确认SRP违规'},
    ],
}
_GLOBAL_ADJUSTMENT_RULES: tuple[tuple[str, frozenset[str], float], ...] = (
    ('structure_pass',
     frozenset({'init_parse', 'syntax', 'circular_import',
                'circular_dependency', 'broken_cross_call'}), 0.05),
    ('structure_fail',
     frozenset({'crash', 'crash_under_stress', 'slow_under_stress',
                'inconsistent_output', 'type_confusion_crash'}), -0.10),
    ('low_coverage',
     frozenset({'broad_except', 'empty_except', 'unreachable_code',
                'missing_docstring', 'chained_comparison'}), -0.05),
    ('high_mutation',
     frozenset({'crash', 'type_confusion_crash', 'broad_except',
                'empty_except'}), 0.05),
)
def _base_confidence(base_table: dict[str, float], finding_type: str) -> float:
    return base_table.get(finding_type, base_table['_default'])
def _clamp_weight(weight: float) -> float:
    return max(-0.5, min(0.5, weight))
def _confidence_level(confidence: float) -> str:
    if confidence >= 0.85:
        return 'confirmed'
    if confidence >= 0.70:
        return 'likely'
    if confidence >= 0.50:
        return 'possible'
    if confidence >= 0.30:
        return 'unlikely'
    return 'false_positive'
def _global_adj_desc(adj: float) -> str:
    if adj > 0:
        if adj >= 0.10:
            return f'全局信号增强(+{adj:.2f}): 测试环境验证充分'
        return f'全局信号微调(+{adj:.2f})'
    if adj < 0:
        if adj <= -0.10:
            return f'全局信号衰减({adj:.2f}): 测试环境不可靠，finding可能为假阳性'
        return f'全局信号微调({adj:.2f})'
    return '无全局调整'
def _global_factor(global_adj: float) -> dict:
    return {
        'method': '_global',
        'method_name': '全局调整',
        'logic': 'global',
        'weight': round(global_adj, 3),
        'desc': _global_adj_desc(global_adj),
    }
class ConfidenceScorer:
    BASE_CONFIDENCE: ClassVar[dict[str, float]] = _BASE_CONFIDENCE
    CROSS_VALIDATION_RULES: ClassVar[dict[str, list[dict]]] = _CROSS_VALIDATION_RULES
    L1_METHODS: ClassVar[set[str]] = {'smoke_test', 'integration_test', 'e2e_test'}
    L2_METHODS: ClassVar[set[str]] = {'static_analysis', 'coverage', 'complexity',
                                      'architecture', 'compatibility',
                                      'contract_test', 'security_test'}
    L3_METHODS: ClassVar[set[str]] = {'unit_test', 'fuzz_test', 'stress_test',
                                      'mutation_test', 'regression_test', 'sca',
                                      'performance'}
    def __init__(self, results: dict[str, TestMethodResult]):
        self.results = results
        self._confidence_cache: dict[str, dict] = {}
    def score_finding(self, finding: dict) -> dict:
        if not isinstance(finding, dict):
            raise TypeError(
                f"finding 必须为 dict，实际为 {type(finding).__name__}")
        ftype = finding_type(finding)
        cache_key = _score_cache_key(finding)
        cached = self._confidence_cache.get(cache_key)
        if cached is not None:
            return self._copy_score_dict(cached)
        base = _base_confidence(self.BASE_CONFIDENCE, ftype)
        weight, factors = self._rule_weight_factors(ftype)
        weight = self._apply_global_adjustment(ftype, weight, factors)
        return self._finalize_score(cache_key, base, weight, factors)
    def _apply_global_adjustment(self, finding_type: str, weight: float,
                                 factors: list[dict]) -> float:
        global_adj = self._global_adjustment(finding_type)
        if global_adj == 0:
            return weight
        factors.append(_global_factor(global_adj))
        return weight + global_adj
    def _finalize_score(self, cache_key: str, base: float, weight: float,
                        factors: list[dict]) -> dict:
        weight = _clamp_weight(weight)
        confidence = round(clamp_unit(base * (1 + weight)), 3)
        result = {
            'confidence': confidence,
            'level': _confidence_level(confidence),
            'base': round(base, 3),
            'weight': round(weight, 3),
            'factors': factors,
        }
        self._confidence_cache[cache_key] = self._copy_score_dict(result)
        return result
    def _rule_weight_factors(self, finding_type: str) -> tuple[float, list[dict]]:
        weight = 0.0
        factors: list[dict] = []
        for rule, method_id, rule_weight in self._iter_triggered_rules(finding_type):
            weight += rule_weight
            factors.append({
                'method': method_id,
                'method_name': self._display_name(method_id),
                'logic': rule['logic'],
                'weight': round(rule_weight, 3),
                'desc': rule.get('desc', ''),
            })
        return weight, factors
    def _iter_triggered_rules(
            self, finding_type: str) -> Iterator[tuple[dict, str, float]]:
        for rule in self.CROSS_VALIDATION_RULES.get(finding_type, []):
            method_id = rule['method']
            method_result = self.results.get(method_id)
            if method_result is None:
                continue
            rule_weight = _evaluate_rule_trigger(rule, method_result)
            if rule_weight != 0:
                yield rule, method_id, rule_weight
    def _global_adjustment(self, finding_type: str) -> float:
        adj = 0.0
        _signals: dict[str, bool] = {}
        for signal_name, affected_types, delta in _GLOBAL_ADJUSTMENT_RULES:
            if finding_type not in affected_types:
                continue
            if signal_name not in _signals:
                _signals[signal_name] = self._global_signal(signal_name)
            if _signals[signal_name]:
                adj += delta
        return adj
    def _global_signal(self, signal_name: str) -> bool:
        if signal_name == 'structure_pass':
            return self._l1_structure_pass()
        if signal_name == 'structure_fail':
            return self._l1_structure_fail()
        if signal_name == 'low_coverage':
            return self._coverage_below_threshold(20)
        if signal_name == 'high_mutation':
            return self._mutation_above_threshold(70)
        return False
    def _present_l1_methods(self) -> list[str]:
        return [m for m in self.L1_METHODS if m in self.results]
    def _l1_structure_pass(self) -> bool:
        present = self._present_l1_methods()
        return (len(present) == len(self.L1_METHODS)) and all(
            result_status_bucket(self.results[m].status) == 'pass'
            for m in present
        )
    def _l1_structure_fail(self) -> bool:
        return any(result_status_bucket(self.results[m].status)
                   in ('fail', 'warn')
                   for m in self._present_l1_methods())
    def _method_metric(self, method_id: str, metric_name: str) -> float | None:
        result = self.results.get(method_id)
        if result is None:
            return None
        value = _method_metrics(result).get(metric_name)
        return value if (is_pure_int(value) or is_finite_num(value)) else None
    def _coverage_below_threshold(self, threshold: float) -> bool:
        coverage = self._method_metric('coverage', 'overall_coverage_pct')
        return coverage is not None and coverage < threshold
    def _mutation_above_threshold(self, threshold: float) -> bool:
        score = self._method_metric('mutation_test', 'mutation_score')
        return score is not None and score > threshold
    @staticmethod
    def _copy_score_dict(score: dict) -> dict:
        return {
            **score,
            'factors': [dict(factor) for factor in score['factors']],
        }
    def score_all(self) -> dict:
        return self._score_report(list(self._iter_scored_findings()))
    def _display_name(self, method_id: str) -> str:
        name = getattr(self.results.get(method_id), 'method_name', None)
        return name if isinstance(name, str) and name.strip() else str(method_id)
    def _iter_scored_findings(self) -> Iterator[dict]:
        for method_id, result in self.results.items():
            method_name = self._display_name(method_id)
            for finding in _dict_findings(method_id, result):
                yield {
                    'method_id': method_id,
                    'method_name': method_name,
                    'finding': finding,
                    **self.score_finding(finding),
                }
    def _score_report(self, scored: list[dict]) -> dict:
        confidence_dist = Counter(item['level'] for item in scored)
        false_positives = [item for item in scored if item['level'] == 'false_positive']
        confirmed = [item for item in scored if item['level'] == 'confirmed']
        total = len(scored)
        return {
            'scored_findings': scored,
            'confidence_distribution': dict(confidence_dist),
            'cross_validation_summary': self._cross_validation_summary(scored),
            'false_positive_candidates': false_positives,
            'confirmed_findings': confirmed,
            'total_scored': total,
            'false_positive_rate': _pct(len(false_positives), total),
            'confirmation_rate': _pct(len(confirmed), total),
        }
    def _cross_validation_summary(self, scored: list[dict]) -> dict:
        corroborating_methods: set[str] = set()
        contradicting_methods: set[str] = set()
        triggered_pairs = 0
        for item in scored:
            for factor in item.get('factors', ()):
                if not isinstance(factor, dict):
                    continue
                ref_method = factor.get('method')
                if not isinstance(ref_method, str) or ref_method == '_global':
                    continue
                triggered_pairs += 1
                if as_number(factor.get('weight')) < 0:
                    contradicting_methods.add(ref_method)
                else:
                    corroborating_methods.add(ref_method)
        return {
            'l1_structure': self._layer_status(self.L1_METHODS),
            'l2_quality': self._layer_status(self.L2_METHODS),
            'l3_runtime': self._layer_status(self.L3_METHODS),
            'cross_rules_triggered': triggered_pairs,
            'corroborating_methods': len(corroborating_methods),
            'contradicting_methods': len(contradicting_methods),
        }
    def _layer_status(self, methods: set[str]) -> dict:
        active = [m for m in methods if m in self.results]
        if not active:
            return {'status': 'skip', 'pass': 0, 'warn': 0, 'fail': 0,
                    'skip': len(methods), 'error': 0}
        buckets = Counter(
            result_status_bucket(getattr(self.results[m], 'status', None))
            for m in active)
        p, w, f, e = (buckets['pass'], buckets['warn'], buckets['fail'],
                      buckets['error'])
        s = (len(methods) - len(active)) + buckets['skip']
        if f > 0:
            status = 'fail' if f >= 2 else 'warn'
        elif w > 0 or e > 0:
            status = 'warn'
        elif p == len(methods):
            status = 'pass'
        else:
            status = 'skip'
        return {'status': status, 'pass': p, 'warn': w, 'fail': f,
                'skip': s, 'error': e}
def _normalize_confidence_results(results: dict) -> tuple[dict, list[dict]]:
    normalized: dict[str, TestMethodResult] = {}
    degradation: list[dict] = []
    for mid, result in results.items():
        clean_findings = _normalize_findings_field(mid, result, degradation)
        clean_metrics = _normalize_metrics_field(mid, result, degradation)
        normalized[mid] = coerce_result_view(
            mid, result, findings=clean_findings, metrics=clean_metrics,
            degradation=degradation)
    return normalized, degradation
def _bucket_findings(scored_findings: list[dict]) -> dict[str, list[dict]]:
    buckets: dict[str, list[dict]] = {level: [] for level in CONFIDENCE_LEVELS}
    for item in scored_findings:
        level = item["level"]
        if level in buckets:
            buckets[level].append(item)
    return buckets
_ACTION_MESSAGE_LIMIT = 100
_ERROR_DETAIL_LIMIT = 200
def _action_message(finding: dict) -> str:
    return str(finding.get('message') or '')[:_ACTION_MESSAGE_LIMIT]
def _method_confidence_summary(all_scored: list[dict]) -> dict[str, dict]:
    method_confidence: dict[str, dict] = {}
    confidence_values: dict[str, list[float]] = {}
    for s in all_scored:
        mid = s['method_id']
        mc = method_confidence.get(mid)
        if mc is None:
            mc = method_confidence[mid] = {
                'method_name': s['method_name'], 'total': 0,
                **dict.fromkeys(CONFIDENCE_LEVELS, 0),
                'avg_confidence': 0.0,
            }
        level = s['level']
        if level not in CONFIDENCE_LEVELS:
            continue
        mc['total'] += 1
        mc[level] += 1
        confidence_values.setdefault(mid, []).append(s['confidence'])
    for mid, mc in method_confidence.items():
        confs = confidence_values.get(mid, [])
        mc['avg_confidence'] = round(sum(confs) / len(confs), 3) if confs else 0.0
    return method_confidence
def _build_summary_payload(scored: dict, all_scored: list[dict],
                           buckets: dict[str, list[dict]],
                           method_confidence: dict[str, dict],
                           priority_actions: list[dict]) -> dict:
    summary = {
        'confirmed_findings': buckets['confirmed'][:20],
        'likely_findings': buckets['likely'][:20],
        'possible_findings': buckets['possible'][:15],
        'false_positive_candidates': buckets['false_positive'][:15],
        'unlikely_findings': buckets['unlikely'][:10],
        'confidence_distribution': scored['confidence_distribution'],
        'cross_validation_summary': scored['cross_validation_summary'],
        'method_confidence': method_confidence,
        'total_findings': len(all_scored),
        'false_positive_rate': scored['false_positive_rate'],
        'confirmation_rate': scored['confirmation_rate'],
        'priority_actions': priority_actions,
    }
    if scored.get('degraded'):
        summary['degraded'] = True
        summary['error'] = scored.get('error', '')
    if 'payload_degradation' in scored:
        summary['payload_degradation'] = scored['payload_degradation']
    return summary
def _build_priority_actions(confirmed: list[dict], likely: list[dict],
                            fp_candidates: list[dict]) -> list[dict]:
    groups = (
        (confirmed[:10], 'P0', '立即修复'),
        (likely[:10], 'P1', '建议修复'),
        (fp_candidates[:5], 'P2', '人工复核（疑似误报）'),
    )
    return [
        {
            'priority': priority,
            'action': action,
            'finding_type': finding_type(item['finding']),
            'method': item['method_name'],
            'confidence': item['confidence'],
            'message': _action_message(item['finding']),
        }
        for items, priority, action in groups for item in items
    ]
def _log_confidence_report(confidence_report: dict) -> None:
    if confidence_report.get('degraded'):
        logger.info("  [!] 置信度评分防御降级: %s",
                    confidence_report.get('error', '')[:100])
        return
    logger.info("  [*] 置信度评分: %s findings, 确认率 %s%%, 疑似假阳性率 %s%%",
                confidence_report['total_scored'],
                confidence_report.get('confirmation_rate', 0),
                confidence_report.get('false_positive_rate', 0))
def _degraded_finding_score(reason: str) -> dict:
    return {
        'confidence': 0.0,
        'level': 'false_positive',
        'base': 0.0,
        'weight': 0.0,
        'factors': [{
            'method': '_defense', 'method_name': '防御降级',
            'logic': 'defense', 'weight': 0,
            'desc': f'置信度评分防御降级: {reason[:_ERROR_DETAIL_LIMIT]}',
        }],
        'degraded': True,
        'error': reason[:_ERROR_DETAIL_LIMIT],
    }
def _normalized_confidence_view(
        results: dict[str, TestMethodResult]) -> tuple[dict, list[dict]]:
    normalized, degradation = _normalize_confidence_results(results)
    if degradation:
        logger.warning("置信度载荷归一降级: %s", degradation)
    return normalized, degradation
def _degraded_confidence_report(exc: BaseException) -> dict:
    return {
        'scored_findings': [],
        'confidence_distribution': {},
        'cross_validation_summary': {},
        'false_positive_candidates': [],
        'confirmed_findings': [],
        'total_scored': 0,
        'false_positive_rate': 0.0,
        'confirmation_rate': 0.0,
        'degraded': True,
        'error': f"{type(exc).__name__}: {str(exc)[:_ERROR_DETAIL_LIMIT]}",
    }
def _empty_confidence_report(message: str) -> dict:
    return {
        'scored_findings': [],
        'confidence_distribution': {},
        'cross_validation_summary': {},
        'false_positive_candidates': [],
        'confirmed_findings': [],
        'total_scored': 0,
        'false_positive_rate': 0.0,
        'confirmation_rate': 0.0,
        'error': message,
    }
def _empty_summary_payload(message: str) -> dict:
    summary = _build_summary_payload(
        _empty_confidence_report(message), [],
        _bucket_findings([]), {}, [])
    summary['error'] = message
    return summary
def score_suite_confidence(results: dict[str, TestMethodResult]) -> dict:
    if not results:
        return _empty_confidence_report("无测试结果，请先运行测试")
    degradation: list[dict] = []
    try:
        normalized, degradation = _normalized_confidence_view(results)
        report = ConfidenceScorer(normalized).score_all()
    except _CONFIDENCE_DEFENSE_EXC as e:
        logger.warning("置信度评分失败,防御降级: %s", e, exc_info=True)
        report = _degraded_confidence_report(e)
    if degradation:
        report['payload_degradation'] = degradation
    _log_confidence_report(report)
    return report
def build_suite_diagnostic_summary(results: dict[str, TestMethodResult]) -> dict:
    if not results:
        return _empty_summary_payload("无测试结果")
    scored = score_suite_confidence(results)
    all_scored = sorted(scored['scored_findings'],
                        key=lambda x: x.get('confidence', 0), reverse=True)
    buckets = _bucket_findings(all_scored)
    method_confidence = _method_confidence_summary(all_scored)
    priority_actions = _build_priority_actions(
        buckets['confirmed'], buckets['likely'], buckets['false_positive'])
    return _build_summary_payload(
        scored, all_scored, buckets, method_confidence, priority_actions)
def score_suite_finding(results: dict[str, TestMethodResult],
                        finding: dict) -> dict:
    if not isinstance(finding, dict):
        logger.warning(
            "score_suite_finding: finding 载荷非 dict（%s），防御降级",
            type(finding).__name__)
        return _degraded_finding_score(
            f"finding 载荷非 dict（{type(finding).__name__}）")
    try:
        normalized, degradation = _normalized_confidence_view(results)
        score = ConfidenceScorer(normalized).score_finding(finding)
        if degradation:
            score['payload_degradation'] = degradation
        return score
    except _CONFIDENCE_DEFENSE_EXC as e:
        logger.warning("单 finding 置信度评分失败,防御降级: %s", e, exc_info=True)
        return _degraded_finding_score(
            f"{type(e).__name__}: {str(e)[:_ERROR_DETAIL_LIMIT]}")
RUN_STATUS_VALUES = ("passed", "failed", "error", "skipped", "not_run")
def _count_test_functions(filepath: str, source: str | None = None, tree: ast.AST | None = None) -> int:
    source, tree = load_test_ast(filepath, source, tree, "_count_test_functions")
    if tree is None:
        return 0
    return sum(1 for _ in iter_collectable_test_functions(tree))
def _mod_root_match(name: str, root: str) -> bool:
    return name == root or name.startswith(root + ".")
def _mod_family(mod_name: str) -> str | None:
    if _mod_root_match(mod_name, "pytest"):
        return "pytest"
    if (_mod_root_match(mod_name, "unittest")
            and not _mod_root_match(mod_name, "unittest.mock")):
        return "unittest"
    if _mod_root_match(mod_name, "nose") or _mod_root_match(mod_name, "nose2"):
        return "nose"
    return None
def _alias_families(node: ast.Import) -> set[str]:
    families: set[str] = set()
    for alias in node.names:
        fam = _mod_family(alias.name)
        if fam:
            families.add(fam)
    return families
def _import_from_family(node: ast.ImportFrom) -> set[str]:
    if node.module and node.level == 0:
        if (node.module == "unittest"
                and all(alias.name == "mock" for alias in node.names)):
            return set()
        fam = _mod_family(node.module)
        if fam:
            return {fam}
    return set()
class _PytestDecoratorBindings(NamedTuple):
    modules: frozenset[str]
    marks: frozenset[str]
_DEFAULT_PYTEST_DECORATOR_BINDINGS = _PytestDecoratorBindings(
    frozenset({'pytest'}), frozenset())
def _pytest_decorator_bindings(tree: ast.AST) -> _PytestDecoratorBindings:
    modules = set(_DEFAULT_PYTEST_DECORATOR_BINDINGS.modules)
    marks: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            modules.update(
                alias.asname or 'pytest' for alias in node.names
                if alias.name == 'pytest')
        elif (isinstance(node, ast.ImportFrom) and not node.level
              and node.module == 'pytest'):
            marks.update(
                alias.asname or alias.name for alias in node.names
                if alias.name == 'mark')
    return _PytestDecoratorBindings(frozenset(modules), frozenset(marks))
def _is_pytest_mark_or_fixture_attr(
    node: ast.AST, bindings: _PytestDecoratorBindings = _DEFAULT_PYTEST_DECORATOR_BINDINGS,
) -> bool:
    return (isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id in bindings.modules
            and node.attr in ("mark", "fixture"))
class _FrameworkSignals(NamedTuple):
    has_pytest_import: bool
    has_unittest_import: bool
    has_nose_import: bool
    has_pytest_mark: bool
    has_test_function: bool
def _collect_framework_signals(tree: ast.AST) -> _FrameworkSignals:
    families: set[str] = set()
    bindings = _pytest_decorator_bindings(tree)
    has_pytest_mark = False
    has_unittest_testcase = False
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            families |= _alias_families(node)
            continue
        if isinstance(node, ast.ImportFrom):
            families |= _import_from_family(node)
            continue
        if (isinstance(node, ast.ClassDef) and any(
                isinstance(base, ast.Attribute) and base.attr == 'TestCase'
                and isinstance(base.value, ast.Name)
                and base.value.id == 'unittest' for base in node.bases)):
            has_unittest_testcase = True
        if _is_pytest_mark_or_fixture_attr(node, bindings):
            has_pytest_mark = True
    has_test_function = next(iter_collectable_test_functions(tree), None) is not None
    return _FrameworkSignals(
        has_pytest_import="pytest" in families,
        has_unittest_import="unittest" in families or has_unittest_testcase,
        has_nose_import="nose" in families,
        has_pytest_mark=has_pytest_mark,
        has_test_function=has_test_function,
    )
def _detect_framework(filepath: str, source: str | None = None, tree: ast.AST | None = None) -> str:
    source, tree = load_test_ast(filepath, source, tree, "_detect_framework")
    if tree is None:
        return "unknown"
    signals = _collect_framework_signals(tree)
    if signals.has_pytest_import or signals.has_pytest_mark:
        return "pytest"
    if signals.has_unittest_import:
        return "unittest"
    if signals.has_nose_import:
        return "nose"
    if signals.has_test_function:
        return "pytest"
    return "unknown"
_PYTEST_BUILTIN_MARKS = frozenset({
    "parametrize", "parameterize", "skip", "skipif",
    "usefixtures", "xfail", "filterwarnings",
})
_PYTESTMARK_NAME = "pytestmark"
_PYTESTMARK_MUTATORS = frozenset({"append", "extend"})
def _is_pytestmark_target(node: ast.AST) -> bool:
    return isinstance(node, ast.Name) and node.id == _PYTESTMARK_NAME
def _flatten_pytestmark_expr(expr: ast.expr | None) -> Iterator[ast.expr]:
    if expr is None:
        return
    if isinstance(expr, (ast.List, ast.Tuple)):
        for elt in expr.elts:
            yield from _flatten_pytestmark_expr(elt)
        return
    if isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Add):
        yield from _flatten_pytestmark_expr(expr.left)
        yield from _flatten_pytestmark_expr(expr.right)
        return
    yield expr
def _iter_module_pytestmark_exprs(tree: ast.AST) -> Iterator[ast.expr]:
    if not isinstance(tree, (ast.Module, ast.ClassDef)):
        return
    for node in tree.body:
        if isinstance(node, ast.Assign):
            if not any(_is_pytestmark_target(t) for t in node.targets):
                continue
            yield from _flatten_pytestmark_expr(node.value)
            continue
        if isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            if not _is_pytestmark_target(node.target):
                continue
            yield from _flatten_pytestmark_expr(node.value)
            continue
        if (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
                and isinstance(node.value.func, ast.Attribute)
                and _is_pytestmark_target(node.value.func.value)
                and node.value.func.attr in _PYTESTMARK_MUTATORS):
            for arg in node.value.args:
                yield from _flatten_pytestmark_expr(arg)
def _extract_markers(filepath: str, source: str | None = None, tree: ast.AST | None = None) -> list[str]:
    source, tree = load_test_ast(filepath, source, tree, "_extract_markers")
    if tree is None:
        return []
    bindings = _pytest_decorator_bindings(tree)
    markers = []
    for expr in _iter_module_pytestmark_exprs(tree):
        mark_name = _extract_mark_from_decorator(expr, bindings)
        if mark_name and mark_name not in _PYTEST_BUILTIN_MARKS:
            markers.append(mark_name)
    for node in walk_nodes(tree):
        if isinstance(node, ast.ClassDef):
            for expr in _iter_module_pytestmark_exprs(node):
                mark_name = _extract_mark_from_decorator(expr, bindings)
                if mark_name and mark_name not in _PYTEST_BUILTIN_MARKS:
                    markers.append(mark_name)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            for decorator in node.decorator_list:
                mark_name = _extract_mark_from_decorator(decorator, bindings)
                if mark_name and mark_name not in _PYTEST_BUILTIN_MARKS:
                    markers.append(mark_name)
    return sorted(set(markers))
def _is_pytest_mark_member(
    node: ast.AST, bindings: _PytestDecoratorBindings = _DEFAULT_PYTEST_DECORATOR_BINDINGS,
) -> bool:
    if not isinstance(node, ast.Attribute):
        return False
    if isinstance(node.value, ast.Name):
        return node.value.id in bindings.marks
    return (isinstance(node.value, ast.Attribute)
            and node.value.attr == "mark"
            and isinstance(node.value.value, ast.Name)
            and node.value.value.id in bindings.modules)
def _is_pytest_mark_call(
    node: ast.AST, attr_name: str,
    bindings: _PytestDecoratorBindings = _DEFAULT_PYTEST_DECORATOR_BINDINGS,
) -> bool:
    return (isinstance(node, ast.Attribute)
            and node.attr == attr_name
            and _is_pytest_mark_member(node, bindings))
def _extract_mark_from_decorator(
    decorator: ast.expr,
    bindings: _PytestDecoratorBindings = _DEFAULT_PYTEST_DECORATOR_BINDINGS,
) -> str | None:
    expr = decorator.func if isinstance(decorator, ast.Call) else decorator
    if isinstance(expr, ast.Attribute) and _is_pytest_mark_member(expr, bindings):
        return expr.attr
    return None
def _extract_usefixtures_names(
    decorator: ast.expr,
    bindings: _PytestDecoratorBindings = _DEFAULT_PYTEST_DECORATOR_BINDINGS,
) -> Iterator[str]:
    if (not isinstance(decorator, ast.Call)
            or not _is_pytest_mark_call(
                decorator.func, "usefixtures", bindings)):
        return
    for arg in decorator.args:
        if (isinstance(arg, ast.Constant) and isinstance(arg.value, str)
                and arg.value.strip()):
            yield arg.value.strip()
def _extract_fixtures(filepath: str, source: str | None = None, tree: ast.AST | None = None) -> list[str]:
    source, tree = load_test_ast(filepath, source, tree, "_extract_fixtures")
    if tree is None:
        return []
    bindings = _pytest_decorator_bindings(tree)
    fixtures = []
    module_parametrize_args: set[str] = set()
    for expr in _iter_module_pytestmark_exprs(tree):
        module_parametrize_args.update(
            _extract_parametrize_arg_names(expr, bindings))
        fixtures.extend(_extract_parametrize_indirect_fixture_names(
            expr, bindings))
        fixtures.extend(_extract_usefixtures_names(expr, bindings))
    class_parametrize_args: dict[
        ast.FunctionDef | ast.AsyncFunctionDef, set[str]] = {}
    for cls in walk_nodes(tree):
        if isinstance(cls, ast.ClassDef):
            parametrized: set[str] = set()
            for expr in _iter_module_pytestmark_exprs(cls):
                parametrized.update(
                    _extract_parametrize_arg_names(expr, bindings))
                fixtures.extend(_extract_parametrize_indirect_fixture_names(
                    expr, bindings))
                fixtures.extend(_extract_usefixtures_names(expr, bindings))
            for decorator in cls.decorator_list:
                parametrized.update(
                    _extract_parametrize_arg_names(decorator, bindings))
                fixtures.extend(_extract_parametrize_indirect_fixture_names(
                    decorator, bindings))
                fixtures.extend(_extract_usefixtures_names(decorator, bindings))
            for member in cls.body:
                if isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    class_parametrize_args[member] = parametrized
    for node in iter_collectable_test_functions(tree):
        parametrize_args = set(module_parametrize_args)
        parametrize_args.update(class_parametrize_args.get(node, ()))
        for decorator in node.decorator_list:
            parametrize_args.update(
                _extract_parametrize_arg_names(decorator, bindings))
            fixtures.extend(_extract_parametrize_indirect_fixture_names(
                decorator, bindings))
            fixtures.extend(_extract_usefixtures_names(decorator, bindings))
        fixtures.extend(_iter_fixture_args(node, parametrize_args))
    return sorted(set(fixtures))
def _iter_fixture_args(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    parametrize_args: set[str],
) -> Iterator[str]:
    for arg in [*node.args.posonlyargs, *node.args.args, *node.args.kwonlyargs]:
        if arg.arg in ("self", "cls"):
            continue
        if arg.arg in parametrize_args:
            continue
        yield arg.arg
def _extract_parametrize_arg_names(
    decorator: ast.expr,
    bindings: _PytestDecoratorBindings = _DEFAULT_PYTEST_DECORATOR_BINDINGS,
) -> set[str]:
    if not isinstance(decorator, ast.Call):
        return set()
    if not _is_pytest_mark_call(decorator.func, "parametrize", bindings):
        return set()
    if decorator.args:
        return _parse_parametrize_first_arg(decorator.args[0]) or set()
    for keyword in decorator.keywords:
        if keyword.arg == "argnames":
            return _parse_parametrize_first_arg(keyword.value) or set()
    return set()
def _extract_parametrize_indirect_fixture_names(
    decorator: ast.expr,
    bindings: _PytestDecoratorBindings = _DEFAULT_PYTEST_DECORATOR_BINDINGS,
) -> set[str]:
    if (not isinstance(decorator, ast.Call)
            or not _is_pytest_mark_call(
                decorator.func, "parametrize", bindings)):
        return set()
    indirect = next(
        (keyword.value for keyword in decorator.keywords
         if keyword.arg == "indirect"),
        None,
    )
    argnames = _extract_parametrize_arg_names(decorator, bindings)
    if isinstance(indirect, ast.Constant) and indirect.value is True:
        return argnames
    if isinstance(indirect, (ast.List, ast.Tuple, ast.Set)):
        return {
            elt.value.strip()
            for elt in indirect.elts
            if (isinstance(elt, ast.Constant)
                and isinstance(elt.value, str)
                and elt.value.strip() in argnames)
        }
    return set()
def _parse_parametrize_first_arg(first_arg: ast.expr) -> set[str] | None:
    if isinstance(first_arg, ast.Constant) and isinstance(first_arg.value, str):
        return {s.strip() for s in first_arg.value.split(",")}
    if isinstance(first_arg, (ast.Tuple, ast.List)):
        return {
            elt.value.strip()
            for elt in first_arg.elts
            if isinstance(elt, ast.Constant) and isinstance(elt.value, str)
        }
    return None
def _find_conftest_deps(test_file: str, project_root: str) -> list[str]:
    conftests = []
    tf_abs = resolve_project_path(test_file, project_root)
    test_dir = os.path.dirname(tf_abs)
    current = test_dir
    project_root_abs = os.path.abspath(project_root)
    project_root_nc = os.path.normcase(project_root_abs)
    while current:
        try:
            if os.path.normcase(
                    os.path.commonpath([current, project_root_abs])) != project_root_nc:
                break
        except ValueError as e:
            logger.debug("跨盘符路径比较失败: %s", e)
            break
        conftest = os.path.join(current, "conftest.py")
        if os.path.isfile(conftest):
            conftests.append(os.path.normpath(conftest))
        if os.path.normcase(current) == project_root_nc:
            break
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    return conftests
def _own_scope_assertion_count(node: ast.FunctionDef | ast.AsyncFunctionDef) -> int:
    count = 0
    stack = list(ast.iter_child_nodes(node))
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(current, ast.Assert):
            count += 1
            continue
        if _is_assert_context_block(current):
            count += 1
            stack.extend(current.body)
            continue
        if _is_assert_method_call(current):
            count += 1
            continue
        stack.extend(ast.iter_child_nodes(current))
    return count
def _asserts_in_own_scope(tree: ast.AST) -> int:
    return sum(
        _own_scope_assertion_count(node)
        for node in iter_collectable_test_functions(tree)
    )
_DEFAULT_TEST_QUALITY = 0.5
def _estimate_quality(filepath: str, test_count: int, source: str | None = None, tree: ast.AST | None = None) -> float:
    source, tree = load_test_ast(filepath, source, tree, "_estimate_quality")
    if tree is None:
        return _DEFAULT_TEST_QUALITY
    if test_count <= 0:
        return 0.0
    assert_count = _asserts_in_own_scope(tree)
    density = assert_count / test_count
    if density >= 3.0:
        return 1.0
    if density >= 0.5:
        return 0.3 + 0.7 * (density - 0.5) / 2.5
    return 0.3 * density / 0.5
@dataclass
class TestMetadata:
    __test__ = False
    path: str
    test_count: int = 0
    framework: str = "unknown"
    markers: list[str] = field(default_factory=list)
    fixtures_used: list[str] = field(default_factory=list)
    conftest_deps: list[str] = field(default_factory=list)
    last_run_status: str = "not_run"
    last_run_duration: float = 0.0
    quality_score: float = _DEFAULT_TEST_QUALITY
    covers_source: list[str] = field(default_factory=list)
    def to_dict(self) -> dict[str, Any]:
        return {
            "path": self.path,
            "test_count": self.test_count,
            "framework": self.framework,
            "markers": list(self.markers),
            "fixtures_used": list(self.fixtures_used),
            "conftest_deps": list(self.conftest_deps),
            "last_run_status": self.last_run_status,
            "last_run_duration": round(self.last_run_duration, 2),
            "quality_score": round(self.quality_score, 3),
            "covers_source_count": len(self.covers_source),
        }
def _registry_key(path: Any) -> str | None:
    try:
        raw = os.fspath(path)
    except TypeError:
        return None
    if isinstance(raw, bytes):
        try:
            raw = os.fsdecode(raw)
        except (TypeError, ValueError):
            return None
    if not isinstance(raw, str) or not raw.strip():
        return None
    return os.path.normpath(raw)
def _coverage_link_key(path: str) -> str:
    return os.path.normcase(os.path.normpath(path))
@dataclass
class TestRegistry:
    __test__ = False
    entries: dict[str, TestMetadata] = field(default_factory=dict)
    total_tests: int = 0
    framework_distribution: dict[str, int] = field(default_factory=dict)
    average_quality: float = 0.0
    pass_rate: float = 0.0
    def register(self, path: str, metadata: TestMetadata) -> None:
        norm_path = _registry_key(path)
        if norm_path is None:
            logger.warning("[TestRegistry] 空路径登记被忽略: %r", path)
            return
        self.entries[_coverage_link_key(norm_path)] = replace(
            metadata,
            path=norm_path,
            markers=list(metadata.markers),
            fixtures_used=list(metadata.fixtures_used),
            conftest_deps=list(metadata.conftest_deps),
            covers_source=list(metadata.covers_source),
        )
    def get(self, path: str) -> TestMetadata | None:
        key = _registry_key(path)
        return (self.entries.get(_coverage_link_key(key))
                if key is not None else None)
    def get_by_status(self, status: str) -> list[TestMetadata]:
        return [m for m in self.entries.values() if m.last_run_status == status]
    def update_run_result(self, path: str, status: str, duration: float) -> None:
        if status not in RUN_STATUS_VALUES:
            raise ValueError(
                f"非法测试运行状态 {status!r}，可选值: {RUN_STATUS_VALUES}")
        if isinstance(duration, bool) or not isinstance(duration, (int, float)):
            raise ValueError(f"测试运行时长必须是有限非负数字: {duration!r}")
        try:
            normalized_duration = float(duration)
        except (TypeError, ValueError, OverflowError):
            raise ValueError(
                f"测试运行时长必须是有限非负数字: {duration!r}") from None
        if not is_finite_num(normalized_duration) or normalized_duration < 0:
            raise ValueError(f"测试运行时长必须是有限非负数字: {duration!r}")
        key = _registry_key(path)
        if key is None:
            raise ValueError(f"测试文件路径非法: {path!r}")
        entry = self.entries.get(_coverage_link_key(key))
        if entry is None:
            return
        entry.last_run_status = status
        entry.last_run_duration = normalized_duration
        self.pass_rate = self._compute_pass_rate()
    def update_coverage_links(self, coverage_map: CoverageMap) -> None:
        link_index: dict[str, list[str]] = {}
        for test_path, sources in coverage_map.reverse_index.items():
            if not isinstance(test_path, str):
                continue
            bucket = link_index.setdefault(_coverage_link_key(test_path), [])
            for source in (sources if isinstance(sources, (list, tuple))
                           else ()):
                if isinstance(source, str) and source not in bucket:
                    bucket.append(source)
        for test_path, meta in self.entries.items():
            meta.covers_source = list(
                link_index.get(_coverage_link_key(test_path), []))
    def compute_stats(self) -> None:
        self.total_tests = sum(m.test_count for m in self.entries.values())
        self.framework_distribution = self._compute_framework_distribution()
        self.average_quality = self._compute_average_quality()
        self.pass_rate = self._compute_pass_rate()
    def _compute_framework_distribution(self) -> dict[str, int]:
        distribution: dict[str, int] = {}
        for meta in self.entries.values():
            distribution[meta.framework] = distribution.get(meta.framework, 0) + 1
        return distribution
    def _compute_average_quality(self) -> float:
        if not self.entries:
            return 0.0
        return sum(m.quality_score for m in self.entries.values()) / len(self.entries)
    def _compute_pass_rate(self) -> float:
        run_results = [m for m in self.entries.values()
                       if m.last_run_status not in {"not_run", "skipped"}]
        if not run_results:
            return 0.0
        passed = sum(1 for m in run_results if m.last_run_status == "passed")
        return passed / len(run_results)
    @classmethod
    def build(
        cls,
        test_files: list[str],
        coverage_map: CoverageMap,
        project_root: str,
    ) -> TestRegistry:
        registry = cls()
        test_files = normalize_path_list(test_files, "test_files",
                                     log_prefix="[TestRegistry]")
        for tf in test_files:
            tf_abs = resolve_project_path(tf, project_root)
            meta = TestMetadata(path=tf_abs)
            source, tree = load_test_ast(
                tf_abs, None, None, f"TestRegistry.build: {tf_abs}")
            meta.conftest_deps = _find_conftest_deps(tf_abs, project_root)
            if tree is not None:
                meta.test_count = _count_test_functions(tf_abs, source, tree)
                meta.framework = _detect_framework(tf_abs, source, tree)
                meta.markers = _extract_markers(tf_abs, source, tree)
                meta.fixtures_used = _extract_fixtures(tf_abs, source, tree)
                meta.quality_score = _estimate_quality(
                    tf_abs, meta.test_count, source, tree)
            else:
                meta.quality_score = 0.0
            registry.register(tf_abs, meta)
        registry.update_coverage_links(coverage_map)
        registry.compute_stats()
        logger.info(
            "[TestRegistry] 构建完成: %d 文件, %d 测试, avg_quality=%.2f, framework=%s",
            len(registry.entries), registry.total_tests,
            registry.average_quality, registry.framework_distribution,
        )
        return registry
    def to_dict(self) -> dict[str, Any]:
        return {
            "total_files": len(self.entries),
            "total_tests": self.total_tests,
            "framework_distribution": dict(self.framework_distribution),
            "average_quality": round(self.average_quality, 3),
            "pass_rate": round(self.pass_rate, 3),
        }
_ASSERT_CONTEXT_MANAGERS = ("raises", "warns", "deprecated_call")
def _is_assert_context_manager(call: ast.Call) -> bool:
    func = call.func
    if isinstance(func, ast.Attribute):
        return func.attr in _ASSERT_CONTEXT_MANAGERS
    if isinstance(func, ast.Name):
        return func.id in _ASSERT_CONTEXT_MANAGERS
    return False
_TEST_ASSET_CACHE: dict[
    str, tuple[tuple[tuple[str, int], ...], tuple[str, ...]]] = {}
_TEST_ASSET_CACHE_MAX = 32
def _mtime_ns(path: str) -> int:
    try:
        return os.stat(path).st_mtime_ns
    except OSError:
        return -1
def _coerce_root(project_root) -> str:
    if isinstance(project_root, os.PathLike):
        try:
            project_root = os.fsdecode(project_root)
        except (TypeError, ValueError) as e:
            logger.debug("[TestAssets] 根路径 PathLike 归一失败: %r (%s)",
                         project_root, e)
            return ""
    if not isinstance(project_root, str) or not project_root:
        return ""
    try:
        root = os.path.abspath(project_root)
    except (OSError, ValueError) as e:
        logger.debug("[TestAssets] 根路径解析失败: %r (%s)", project_root, e)
        return ""
    return root if os.path.isdir(root) else ""
def _raise_walk_error(error: OSError) -> None:
    raise error


def _iter_scan_py_files(root: str, *, skip_test_dirs: bool = False) -> Iterator[str]:
    prune = scan_prune_dirs(root)
    excluded_test_roots = ({
        os.path.normcase(os.path.join(root, *tree.split("/")))
        for tree in test_tree_dirs(root)
    } if skip_test_dirs else set())
    for current, dirs, files in os.walk(root, onerror=_raise_walk_error):
        dirs[:] = sorted(
            name for name in dirs
            if not is_pruned_scan_dir(name, prune)
            and not (skip_test_dirs and (
                name.lower() in _TEST_DIR_NAMES
                or os.path.normcase(os.path.join(current, name))
                in excluded_test_roots
            )))
        for name in sorted(files):
            if name.startswith(".") or not name.lower().endswith(".py"):
                continue
            yield os.path.join(current, name)
def _asset_dirs(root: str) -> list[str]:
    found = [root]
    prune = scan_prune_dirs(root)
    for current, dirs, _files in os.walk(
            root, onerror=_raise_walk_error):
        dirs[:] = sorted(
            name for name in dirs if not is_pruned_scan_dir(name, prune))
        found.extend(os.path.join(current, name) for name in dirs)
    return found
def _asset_signature(root: str) -> tuple[tuple[str, int], ...]:
    return tuple((path, _mtime_ns(path)) for path in _asset_dirs(root))
def _rel_dir(path: str, root: str) -> str:
    rel = os.path.relpath(path, root)
    return "" if rel == os.curdir else rel.replace(os.sep, "/")
def _holds_test_files(files: Iterable[str]) -> bool:
    return any(
        name.lower().endswith(".py") and is_test_source_basename(name)
        for name in files)
def _inside_package_dir(root: str, rel_dir: str) -> bool:
    parts = [part for part in rel_dir.split("/") if part]
    for depth in range(1, len(parts) + 1):
        if os.path.isfile(os.path.join(root, *parts[:depth], "__init__.py")):
            return True
    return False
def test_tree_dirs(project_root: str) -> list[str]:
    root = _coerce_root(project_root)
    if not root:
        return []
    trees: set[str] = set()
    prune = scan_prune_dirs(root)
    for current, dirs, files in os.walk(root, onerror=_raise_walk_error):
        rel = _rel_dir(current, root)
        if rel and rel != ".." and not rel.startswith("../"):
            if os.path.basename(current).lower() in _TEST_DIR_NAMES:
                trees.add(rel)
                dirs[:] = []
                continue
            if _holds_test_files(files) and not _inside_package_dir(root, rel):
                trees.add(rel)
                dirs[:] = []
                continue
        dirs[:] = sorted(
            name for name in dirs if not is_pruned_scan_dir(name, prune))
    return sorted(trees, key=lambda path: (path.count("/"), path.lower()))
def test_asset_files(project_root: str) -> list[str]:
    root = _coerce_root(project_root)
    if not root:
        return []
    key = os.path.normcase(os.path.realpath(root))
    cached = _TEST_ASSET_CACHE.get(key)
    if cached is not None:
        signature, files = cached
        if all(_mtime_ns(path) == stamp for path, stamp in signature):
            return list(files)
    try:
        signature = _asset_signature(root)
        found = set(iter_test_py_files(root))
        found.update(
            fpath for fpath in _iter_scan_py_files(root)
            if os.path.basename(fpath) == "conftest.py")
        for tree in test_tree_dirs(root):
            found.update(_iter_scan_py_files(
                os.path.join(root, *tree.split("/"))))
        files = tuple(sorted(found))
    except OSError:
        logger.warning("[TestAssets] 测试面枚举失败: %s", root, exc_info=True)
        return []
    _TEST_ASSET_CACHE[key] = (signature, files)
    if len(_TEST_ASSET_CACHE) > _TEST_ASSET_CACHE_MAX:
        _TEST_ASSET_CACHE.pop(next(iter(_TEST_ASSET_CACHE)))
    return list(files)
def test_asset_dirs(project_root: str) -> list[str]:
    return sorted({os.path.dirname(fpath)
                   for fpath in test_asset_files(project_root)})
def _paired_test_stems(stem: str) -> tuple[str, ...]:
    if stem in ("__init__", "__main__"):
        return stem, stem.strip("_")
    return (stem,)
def _is_python_target(filename: str) -> bool:
    raw = str(filename or "").strip()
    if not raw:
        return True
    label = os.path.basename(raw)
    if not label or label.startswith("."):
        return False
    suffix = os.path.splitext(label)[1].lower()
    return suffix == ".py"
def _expected_test_filenames(filename: str) -> tuple[str, ...]:
    if not isinstance(filename, str):
        return ()
    label = os.path.basename(filename.strip())
    if not label or label.startswith(".") or not label.lower().endswith(".py"):
        return ()
    filename = normalize_py_filename(filename)
    if not filename or is_test_source_basename(filename):
        return ()
    stem = filename[:-len('.py')]
    if not stem:
        return ()
    return tuple(
        test_filename
        for candidate_stem in _paired_test_stems(stem)
        for test_filename in (
            f"test_{candidate_stem}.py", f"{candidate_stem}_test.py")
    )
def _test_file_present(skill_dir: str,
                       test_filenames: tuple[str, ...]) -> bool:
    wanted = {os.path.normcase(name) for name in test_filenames}
    if not wanted:
        return False
    return any(os.path.normcase(os.path.basename(fpath)) in wanted
               for fpath in test_asset_files(skill_dir))
def _test_existence_phase(skill_dir: str, filename: str,
                          details: list[dict],
                          suggestions: list[str]) -> bool:
    if not (skill_dir and filename):
        return False
    expected_tests = _expected_test_filenames(filename)
    if not expected_tests:
        return False
    if _test_file_present(skill_dir, expected_tests):
        return False
    details.append(make_detail(
        "missing_test_file", "TEST-01",
        filename, confidence=0.60,
        expected_test=expected_tests[0],
    ))
    suggestions.append(
        f"缺少测试文件: {_TEST_DIR_HINT}/{expected_tests[0]}")
    return True
def _is_assert_method_call(node: ast.AST) -> bool:
    if isinstance(node, ast.Call) and _is_assert_context_manager(node):
        return True
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)):
        return False
    attr = node.func.attr
    return (attr.startswith("assert_")
            or (attr.startswith("assert") and len(attr) > 6
                and attr[6].isupper()))
def _is_assert_context_block(node: ast.AST) -> bool:
    if not isinstance(node, (ast.With, ast.AsyncWith)):
        return False
    return any(
        isinstance(item.context_expr, ast.Call)
        and _is_assert_context_manager(item.context_expr)
        for item in node.items
    )
def _assert_completeness_phase(content: str, details: list[dict],
                               suggestions: list[str],
                               filename: str = "") -> bool:
    if not content:
        return False
    if filename and not _is_python_target(filename):
        return False
    violated = False
    try:
        tree = parse_cached(content)
        for node in iter_collectable_test_functions(tree):
            if _own_scope_assertion_count(node) == 0:
                violated = True
                details.append(make_detail(
                    "test_without_assert", "TEST-02",
                    f"line:{node.lineno}", confidence=0.65,
                    function=node.name,
                ))
                suggestions.append(f"L{node.lineno}: 测试函数 {node.name} 缺少断言")
    except PARSE_DEGRADE_EXC as e:
        logger.warning("test_skeleton_check: invalid test syntax: %s", e)
        violated = True
        details.append(make_detail(
            "test_invalid_syntax", "TEST-02", "content", confidence=1.0,
            error=str(e)[:_ERROR_DETAIL_LIMIT],
        ))
        suggestions.append("测试文件存在语法错误，无法验证测试与断言完整性")
    return violated
def check_test_skeleton(skill_dir: str | os.PathLike = "", content: str = "",
                        filename: str = "") -> PreinterventionResult:
    skill_dir = normalize_input(skill_dir, "check_test_skeleton 参数 skill_dir",
                                 allow_path=True)
    content = normalize_input(content, "check_test_skeleton 参数 content")
    filename = normalize_input(filename, "check_test_skeleton 参数 filename")
    details: list[dict] = []
    suggestions: list[str] = []
    violated_a = _test_existence_phase(skill_dir, filename, details, suggestions)
    violated_b = _assert_completeness_phase(
        content, details, suggestions, filename)
    passed = not (violated_a or violated_b)
    return finish_check("test_skeleton_check", "测试骨架检查", passed, "warning",
                   details, suggestions)
def _check_provider() -> dict:
    return {
        "test_skeleton_check": check_test_skeleton,
    }
register_check_provider(_check_provider)
class TestMaturityLevel(IntEnum):
    __test__ = False
    NONE = 0
    SMOKE = 1
    STANDARD = 2
    COMPLETE = 3
_STATIC_BASE_RULES = frozenset({
    "规则6", "规则7", "规则9", "规则10", "规则14", "规则15",
    "规则16", "规则17", "规则21", "规则22", "规则27",
    "规则32", "规则35", "规则36", "规则37", "规则39", "规则40",
})
_SMOKE_DYNAMIC_RULES = frozenset({"规则1", "规则4", "规则5", "规则24"})
_STANDARD_DYNAMIC_RULES = frozenset({
    "规则8", "规则11", "规则12", "规则13", "规则19",
    "规则25", "规则28", "规则29", "规则30",
    "规则33", "规则34",
})
_ALL_RULES_WILDCARD = "*"
def _all_rules_active(active_rules) -> bool:
    return _ALL_RULES_WILDCARD in active_rules
def _is_rule_active(rule_id: str, active_rules) -> bool:
    return _all_rules_active(active_rules) or rule_id in active_rules
ACTIVE_RULES_BY_LEVEL: dict[TestMaturityLevel, frozenset[str]] = {
    TestMaturityLevel.NONE: frozenset(_STATIC_BASE_RULES),
    TestMaturityLevel.SMOKE: frozenset(
        _STATIC_BASE_RULES | _SMOKE_DYNAMIC_RULES),
    TestMaturityLevel.STANDARD: frozenset(
        _STATIC_BASE_RULES | _SMOKE_DYNAMIC_RULES | _STANDARD_DYNAMIC_RULES),
    TestMaturityLevel.COMPLETE: frozenset({_ALL_RULES_WILDCARD}),
}
CONFIDENCE_MULTIPLIER_BY_LEVEL: dict[TestMaturityLevel, float] = {
    TestMaturityLevel.NONE: 0.70,
    TestMaturityLevel.SMOKE: 0.85,
    TestMaturityLevel.STANDARD: 0.95,
    TestMaturityLevel.COMPLETE: 1.00,
}
_MATURITY_LOW_PCT = 10.0
_MATURITY_HIGH_PCT = 60.0
def _pct_to_maturity_level(pct: float) -> TestMaturityLevel:
    if pct > _MATURITY_HIGH_PCT:
        return TestMaturityLevel.COMPLETE
    if pct >= _MATURITY_LOW_PCT:
        return TestMaturityLevel.STANDARD
    return TestMaturityLevel.SMOKE
@dataclass
class RuleFallback:
    rule_id: str
    primary_sources: str
    fallback_sources: str
    confidence_penalty: float
    fallback_description: str
    accuracy_loss: str
FALLBACK_TABLE: dict[str, RuleFallback] = {
    "规则1": RuleFallback(
        rule_id="规则1",
        primary_sources="A1(盲点)+F1(覆盖率)",
        fallback_sources="A1(盲点)+D1(调用图可达性)",
        confidence_penalty=0.15,
        fallback_description="用调用图可达性分析替代覆盖率验证死代码",
        accuracy_loss="中等：动态加载的函数可能被误判为死代码",
    ),
    "规则4": RuleFallback(
        rule_id="规则4",
        primary_sources="B1+F1(单元测试)",
        fallback_sources="A1+A2+B1(反模式)+AST语义等价",
        confidence_penalty=0.20,
        fallback_description="用AST语义分析和反模式检测替代单元测试验证",
        accuracy_loss="较大：运行时行为无法静态验证",
    ),
    "规则5": RuleFallback(
        rule_id="规则5",
        primary_sources="测试失败+诊断未发现",
        fallback_sources="A1(盲点扫描)+B1(并发分析)+异常路径静态分析",
        confidence_penalty=0.25,
        fallback_description="用盲点扫描和异常路径分析替代测试失败检测",
        accuracy_loss="较大：仅能发现静态可见的隐藏问题",
    ),
    "规则7": RuleFallback(
        rule_id="规则7",
        primary_sources="B1(cohesion CH01)+F1(集成)",
        fallback_sources="B1(cohesion CH01)+D1(调用图循环检测)",
        confidence_penalty=0.10,
        fallback_description="用调用图循环检测替代集成测试验证循环依赖",
        accuracy_loss="较小：循环依赖可通过静态分析可靠检测",
    ),
    "规则8": RuleFallback(
        rule_id="规则8",
        primary_sources="D1+B1+F1",
        fallback_sources="B1+A1+A2+E1(静态)",
        confidence_penalty=0.10,
        fallback_description="仅保留静态分析源，去除F1(单元测试)依赖",
        accuracy_loss="较小：宽泛异常主要通过AST检测",
    ),
    "规则11": RuleFallback(
        rule_id="规则11",
        primary_sources="D1(调用图)+F1(E2E)",
        fallback_sources="D1(调用图)+A1(运行时绑定分析)",
        confidence_penalty=0.15,
        fallback_description="用运行时绑定分析替代E2E测试验证调用断裂",
        accuracy_loss="中等：动态调用的断裂可能漏检",
    ),
    "规则12": RuleFallback(
        rule_id="规则12",
        primary_sources="E1+A1+F1(集成)",
        fallback_sources="E1+A1+AST路径分析",
        confidence_penalty=0.10,
        fallback_description="用AST路径分析替代集成测试验证路径穿越",
        accuracy_loss="较小：路径穿越可通过AST可靠检测",
    ),
    "规则13": RuleFallback(
        rule_id="规则13",
        primary_sources="A1+F1(性能)",
        fallback_sources="A1+文件大小+行数统计",
        confidence_penalty=0.15,
        fallback_description="用文件大小和行数统计替代性能测试",
        accuracy_loss="中等：性能问题不仅取决于文件大小",
    ),
    "规则19": RuleFallback(
        rule_id="规则19",
        primary_sources="B2(基线)+F1(回归)",
        fallback_sources="B2(基线)+B2(趋势分析)",
        confidence_penalty=0.20,
        fallback_description="用趋势分析替代回归测试验证基线退化",
        accuracy_loss="较大：无法检测运行时行为退化",
    ),
    "规则24": RuleFallback(
        rule_id="规则24",
        primary_sources="B1(日志异常)+B1(反模式)+F1(冒烟)",
        fallback_sources="B1(日志异常)+B1(反模式)+A1(AST)",
        confidence_penalty=0.15,
        fallback_description="用AST分析替代冒烟测试验证日志异常",
        accuracy_loss="中等：运行时日志异常可能漏检",
    ),
    "规则25": RuleFallback(
        rule_id="规则25",
        primary_sources="B2(API契约)+F1(兼容)+F1(回归)",
        fallback_sources="B2(API契约)+A4(API表面分析)",
        confidence_penalty=0.15,
        fallback_description="用API表面分析替代兼容性测试",
        accuracy_loss="中等：运行时兼容性问题可能漏检",
    ),
    "规则29": RuleFallback(
        rule_id="规则29",
        primary_sources="F1(回归)+F2(定向突变)+B1(静态)",
        fallback_sources="B1(死代码确认)+D1(调用图)+复杂度评分",
        confidence_penalty=0.30,
        fallback_description="用调用图和复杂度估算替代突变测试",
        accuracy_loss="大：突变测试需要运行时执行",
    ),
    "规则30": RuleFallback(
        rule_id="规则30",
        primary_sources="B2(趋势)+B2(缺陷)+F1(回归)",
        fallback_sources="B2(趋势)+B2(缺陷)+B2(基线)",
        confidence_penalty=0.15,
        fallback_description="用基线对比替代回归测试验证历史趋势",
        accuracy_loss="中等：无法检测运行时退化",
    ),
    "规则33": RuleFallback(
        rule_id="规则33",
        primary_sources="B1(类型)+F3(测试质量)+F1(覆盖)+A3(评分)",
        fallback_sources="B1(类型)+A3(评分)+A1(AST)+B1(AST)",
        confidence_penalty=0.20,
        fallback_description="用AST分析替代测试质量和覆盖率",
        accuracy_loss="较大：测试质量需要运行时评估",
    ),
    "规则34": RuleFallback(
        rule_id="规则34",
        primary_sources="B(AST)前置+C(调用图)+E(测试)交叉",
        fallback_sources="B(AST)前置+C(调用图)+A1(导入分析)",
        confidence_penalty=0.15,
        fallback_description="用导入分析替代单元测试验证隐式依赖",
        accuracy_loss="中等：动态导入可能漏检",
    ),
}
_TEST_DIR_NAMES = TEST_DIR_CANDIDATES_LOWER
_TEST_DIR_HINT = ("tests" if "tests" in TEST_DIR_CANDIDATES_LOWER
                  else TEST_DIR_CANDIDATES[0])
def _adapter_marks_test_file(adapter: Any, path: str) -> bool:
    checker = getattr(adapter, "is_test_file", None)
    if callable(checker):
        return bool(checker(path))
    return is_test_source_basename(os.path.basename(path))
def _collect_test_files(skill_dir: str, adapter: Any) -> list[str]:
    if adapter is None:
        root = _coerce_root(skill_dir)
        if not root:
            return []
        return [
            fpath for fpath in _iter_scan_py_files(root)
            if is_test_source_basename(os.path.basename(fpath))]
    candidates = normalize_path_list(
        adapter.get_test_files(), "test_files", log_prefix="[TestMaturity]")
    checker = getattr(adapter, "is_test_file", None)
    if not callable(checker):
        return candidates
    return [fpath for fpath in candidates if bool(checker(fpath))]
def _counts_as_source_file(fpath: Any, adapter: Any = None) -> bool:
    if not isinstance(fpath, str):
        return False
    if os.path.basename(fpath).lower() == "conftest.py":
        return False
    if adapter is not None:
        return not _adapter_marks_test_file(adapter, fpath)
    return not is_test_source_basename(os.path.basename(fpath))
def count_source_files(skill_dir: str, adapter: Any = None) -> int:
    if adapter is not None:
        paths = normalize_path_list(
            adapter.get_source_files(), "source_files",
            log_prefix="[TestMaturity]")
        return sum(1 for fpath in paths
                   if _counts_as_source_file(fpath, adapter))
    root = _coerce_root(skill_dir)
    if not root:
        return 0
    return sum(1 for fpath in _iter_scan_py_files(root, skip_test_dirs=True)
               if _counts_as_source_file(fpath))
def assess_test_maturity(skill_dir: str, adapter: Any = None,
                         coverage_data: dict | None = None) -> TestMaturityLevel:
    test_files = _collect_test_files(skill_dir, adapter)
    if not test_files:
        logger.info("[TestMaturity] 无测试文件 → NONE")
        return TestMaturityLevel.NONE
    if coverage_data and isinstance(coverage_data, dict):
        _raw_pct = coverage_data.get("percent")
        pct = safe_float(_raw_pct, None)
        if pct is not None and 0.0 <= pct <= 100.0:
            return _pct_to_maturity_level(pct)
        logger.warning("[TestMaturity] 覆盖率数据 percent=%r 非数值、非有限值或超出 [0, 100]，"
                       "降级按文件比率估算", _raw_pct)
    source_count = count_source_files(skill_dir, adapter)
    ratio = 0.0 if source_count == 0 else len(test_files) / source_count
    _level = _pct_to_maturity_level(ratio * 100)
    logger.info("[TestMaturity] 测试比率 %.1f%% → %s",
                ratio * 100, _level.name)
    return _level
def get_rule_fallback(
    rule_id: str,
    level: TestMaturityLevel,
) -> RuleFallback | None:
    if level == TestMaturityLevel.COMPLETE:
        return None
    fallback = FALLBACK_TABLE.get(rule_id)
    if fallback is None:
        return None
    active_rules = ACTIVE_RULES_BY_LEVEL.get(level, frozenset())
    return fallback if _is_rule_active(rule_id, active_rules) else None
def get_confidence_multiplier(level: TestMaturityLevel) -> float:
    return CONFIDENCE_MULTIPLIER_BY_LEVEL.get(
        level, CONFIDENCE_MULTIPLIER_BY_LEVEL[TestMaturityLevel.NONE])
def get_test_maturity_report(skill_dir: str, adapter: Any = None,
                             coverage_data: dict | None = None) -> dict:
    level = assess_test_maturity(skill_dir, adapter, coverage_data)
    mult = get_confidence_multiplier(level)
    active_rules = ACTIVE_RULES_BY_LEVEL.get(level, frozenset())
    fallback_rules: list[dict] = []
    skipped_rules: list[str] = []
    if not _all_rules_active(active_rules):
        for rule_id, fallback in FALLBACK_TABLE.items():
            if _is_rule_active(rule_id, active_rules):
                fallback_rules.append({
                    "rule_id": rule_id,
                    "fallback_sources": fallback.fallback_sources,
                    "confidence_penalty": fallback.confidence_penalty,
                    "description": fallback.fallback_description,
                })
            else:
                skipped_rules.append(rule_id)
    return {
        "level": level.name,
        "confidence_multiplier": mult,
        "active_rules": ([_ALL_RULES_WILDCARD]
                         if _all_rules_active(active_rules)
                         else sorted(active_rules)),
        "fallback_rules": fallback_rules,
        "skipped_rules": sorted(skipped_rules),
    }

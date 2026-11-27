from __future__ import annotations

import inspect
import logging
import math
import os
from collections.abc import Callable
from dataclasses import dataclass
from functools import cache, wraps
from typing import Any

from jwsgj.diag_types_normalize import (
    canonical_rule_key,
    clean_source_ids,
    finding_file_path,
    findings_container,
    get_max_severity,
    is_default_confidence,
    is_real_number,
    is_status_message_finding,
    is_valid_fp_rate,
    normalize_severity_rank,
    safe_finding_line,
    safe_int,
    safe_rule_id,
    signal_bool,
)
from jwsgj.diag_types_normalize import (
    finding_sub_engines as _finding_sub_engines,
)
from jwsgj.diag_types_vocab import (
    CAT_DYNAMIC_BINDING,
    CAT_MAINTAINABILITY,
    CONF_FLOOR,
    CONF_HIGH,
    CONF_MEDIUM,
    CONF_VERY_HIGH,
    CV_RULES,
    FP_RATE_CRITICAL,
    FP_RATE_HIGH,
    FP_RATE_LOW,
    FP_RATE_MEDIUM,
    HIGH_SEVERITY_PROTECTED,
    LEGACY_TO_MAIN,
    LEGACY_TO_SUB,
    LOW_RELIABILITY_BASE,
    METHOD_SUB_RULES,
    MSG_XV_VALIDATORS_IMPORT_FAIL,
    RULE_COMMAND_INJECTION,
    RULE_CONNECTION_LEAK,
    RULE_FAMILY_MAP,
    RULE_HARDCODED_CREDENTIAL,
    RULE_HIGH_COMPLEXITY,
    RULE_MISSING_DOCSTRING,
    RULE_MUTABLE_DEFAULT,
    SIGNAL_BASELINE_HIT_COUNT,
    SIGNAL_BASELINE_PERSISTENT_NOISE,
    SIGNAL_ENSEMBLE_GROUP_COUNT,
    SIGNAL_ENSEMBLE_LOW_CONFIDENCE,
    SIGNAL_MUTATION_CONFIRMED_DEAD,
    SIGNAL_MUTATION_VERIFIED,
    SIGNAL_REFDEPTH_CHAIN_DEPTH,
    SIGNAL_REFDEPTH_IN_DEGREE,
    SIGNAL_REFDEPTH_ISOLATED,
    SOURCE_SEQUENCE_TYPES,
    SUB_ENGINE_META,
)
from jwsgj.fix_guide_rule_identity import (
    KNOWN_HIGH_FP_FAMILIES,
    RULE_FAMILY_SETS,
    check_rule_exclusion,
    finding_family,
    get_rule_family_set,
    get_rule_metadata,
    get_rule_semantic,
    match_rule_families,
    normalize_rule,
)
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_scope import (
    call_with_timeout,
)
from jwsgj.xv_context_derivation import (
    _aggregate_func_coverage,
    _aggregate_module_coverage,
)
from jwsgj.xv_evidence_strength import (
    REGRESSION_FAMILIES,
    count_independent_sources,
    independent_sources,
    source_main_id,
)
from jwsgj.xv_evidence_strength import (
    family_reliability_base as _reliability_base,
)
from jwsgj.xv_threshold_learning import (
    COVERAGE_LOW_THRESHOLD,
    RULE_FP_TRACKER,
    SINGLE_SOURCE_CONFIRM_THRESHOLD,
    get_rule_weight,
)

logger = logging.getLogger(__name__)
__all__ = [
    'AUTO_FAMILY_TO_RULES',
    'PHASE_MODULE_DEPS',
    'RULE_CHECK_FN_MAP',
    'PhaseModuleState',
    'apply_confidence_adjustments',
    'check_rule_1',
    'check_rule_2',
    'check_rule_3',
    'check_rule_4',
    'check_rule_5',
    'check_rule_6',
    'check_rule_7',
    'check_rule_8',
    'check_rule_9',
    'check_rule_10',
    'check_rule_11',
    'check_rule_12',
    'check_rule_13',
    'check_rule_14',
    'check_rule_15',
    'check_rule_17',
    'check_rule_18',
    'check_rule_19',
    'check_rule_20',
    'check_rule_21',
    'check_rule_22',
    'check_rule_23',
    'check_rule_24',
    'check_rule_25',
    'check_rule_26',
    'check_rule_27',
    'check_rule_28',
    'check_rule_29',
    'check_rule_30',
    'check_rule_31',
    'check_rule_32',
    'check_rule_33',
    'check_rule_34',
    'check_rule_35',
    'check_rule_36',
    'check_rule_37',
    'check_rule_38',
    'check_rule_39',
    'check_rule_40',
    'check_rule_41',
    'check_rule_42',
    'check_rule_43',
    'check_rule_44',
    'check_rule_45',
    'check_rule_46',
    'check_rule_47',
    'check_rule_48',
    'check_rule_49',
    'check_rule_50',
    'check_rule_51',
    'check_rule_52',
    'check_rule_53',
    'check_rule_54',
    'check_rule_55',
    'check_rule_56',
    'check_rule_57',
    'check_rule_H1',
    'check_rule_H2',
    'check_rule_H4',
    'check_rule_H6',
    'check_rule_H7',
    'check_rule_H8',
    'default_meta_rule',
    'dispatch_rule_check',
    'get_refinement',
    'is_module_available',
    'is_phase_module_available',
    'match_rule',
    'rebuild_rules_applied',
    'resolve_exclusion_and_reselect',
    'resolve_rule_conflict',
    'rule4_low_coverage_blindspot',
    'rule21_runtime_idle',
    'rule22_unreachable',
    'rule23_equivalence_ok',
    'rule26_concurrency_risky',
    'rule27_doc_orphan',
    'rule28_pattern_confirmed',
    'rule29_mutation_survived',
    'run_candidate_checks',
    'set_phase_module_status',
    'validate_family_semantics',
    'validate_family_to_rules_consistency',
]
logger.info("xv_rule_checks 判定核已加载: %d 项导出", len(__all__))
_RECURSION_FAMILIES = frozenset(
    (get_rule_family_set("recursion") - {"infinite_loop"}) | {"fuzz_crash"})
def _source_set(sources) -> set:
    return set(clean_source_ids(sources))
def _norm_severity(f: dict) -> str:
    return str(f.get("severity", "P3")).strip().upper()
_E_TEST_ENGINES = frozenset({"E1", "E2", "E3"})
_TEST_FAILURE_FAMILIES = frozenset({
    "test_failure", "test_error", "test_smell",
    "method_anomaly", "e2e_failure", "smoke_failure",
})
_ENGINE_SOURCE_GROUPS = frozenset({"A", "B", "C", "D", "E"})
_DIAGNOSIS_SOURCE_GROUPS = _ENGINE_SOURCE_GROUPS - {"E"}
_PASS_TERMINAL_STATES = frozenset({"pass", "passed"})
_FAILURE_TERMINAL_STATES = frozenset({
    "fail", "failed", "blocked", "timeout", "error",
})
_SUCCESS_TERMINAL_STATES = _PASS_TERMINAL_STATES | {"warn"}
def _iter_dict_findings(data) -> list:
    return [ff for ff in findings_container(data) if isinstance(ff, dict)]
def _iter_evidence_findings(data: dict):
    for ff in _iter_dict_findings(data):
        if not is_status_message_finding(ff):
            yield ff
def _has_family(data: dict, families) -> bool:
    return any(finding_family(ff) in families for ff in _iter_evidence_findings(data))
def _match_rule_families(sources, data, gate, families, **kwargs):
    if isinstance(data, dict):
        data = {**data, "findings": list(_iter_evidence_findings(data))}
    return match_rule_families(sources, data, gate, families, **kwargs)
def _any_finding(data: dict, predicate) -> bool:
    return any(predicate(ff) for ff in _iter_dict_findings(data))
def _source_main_of(method) -> str:
    text = method.strip().upper() if isinstance(method, str) else ""
    if not text:
        return ""
    if text in SUB_ENGINE_META:
        return source_main_id(text) or text
    return (LEGACY_TO_MAIN.get(text)
            or source_main_id(LEGACY_TO_SUB.get(text, text))
            or text)
def _sub_engine_label(value) -> str:
    text = value.strip().upper() if isinstance(value, str) else ""
    if not text:
        return ""
    if text in SUB_ENGINE_META:
        return text
    sub_id = LEGACY_TO_SUB.get(text)
    return sub_id if sub_id in SUB_ENGINE_META else ""
def _detector_ids(ff: dict) -> set:
    ids = set(_finding_sub_engines(ff))
    for label in (_str_field(ff, "source"),
                  _str_field(ff, "_source_method")):
        sub_id = _sub_engine_label(label)
        if sub_id:
            ids.add(sub_id)
    return ids
def _has_sub_engine(data: dict, sub_id: str, *, evidence_only: bool = False) -> bool:
    source = _iter_evidence_findings(data) if evidence_only else _iter_dict_findings(data)
    return any(sub_id in _detector_ids(ff) for ff in source)
def _has_test_engine_cross(data: dict) -> bool:
    # 同一定位点可保留多条 finding，跨引擎证据应按集合并集判定。
    return len(_sub_engines_union(data) & _E_TEST_ENGINES) >= 2
def _sub_engines_union(data: dict) -> set:
    subs: set = set()
    for ff in _iter_evidence_findings(data):
        subs |= _detector_ids(ff)
    return subs
def _source_main_ids(ff: dict) -> set:
    return {main for main in (
        _source_main_of(ff.get("_source_method")),
        _source_main_of(_str_field(ff, "source")),
    ) if main}
def _f4_findings(data: dict) -> list:
    return [ff for ff in _iter_dict_findings(data)
            if "F" in _source_main_ids(ff) and "F4" in _detector_ids(ff)]
_Gate = Callable[[set[str]], bool]
def _source_gate(*, all_of: tuple[str, ...] = (),
                 any_of: tuple[str, ...] = (),
                 min_hits: int = 1) -> _Gate:
    required = frozenset(all_of)
    candidates = frozenset(any_of)
    def gate(source_set: set[str]) -> bool:
        if not required <= source_set:
            return False
        if not candidates:
            return True
        return len(candidates & source_set) >= min_hits
    return gate
def _str_field(ff: dict, key: str) -> str:
    value = ff.get(key)
    return value if isinstance(value, str) else ""
def _normalized_family(ff: dict) -> str:
    return normalize_rule(finding_family(ff))
def _normalize_confirm_inputs(sources, cross_sources):
    return clean_source_ids(sources), set(clean_source_ids(cross_sources))
def _a2_cross_present(ff: dict, sources, cross_sources,
                      same_group_cross: bool) -> bool:
    subs = _finding_sub_engines(ff)
    if "A2" not in subs:
        return False
    cross = bool(cross_sources & {s for s in sources if isinstance(s, str)})
    if same_group_cross:
        cross = cross or bool(subs - {"A2"})
    return cross
_HALLUCINATION_CONFIRM_THRESHOLD = 0.75
@dataclass(frozen=True)
class _HallucinationSpec:
    log_name: str
    families: frozenset[str]
    cross_sources: frozenset[str]
    threshold: float = _HALLUCINATION_CONFIRM_THRESHOLD
    same_group_cross: bool = False
def _a2_finding_confirms(ff, spec: _HallucinationSpec, sources,
                         cross_sources) -> bool:
    if _normalized_family(ff) not in spec.families:
        return False
    if _a2_cross_present(ff, sources, cross_sources, spec.same_group_cross):
        return True
    conf = ff.get("confidence", 0)
    return bool(is_real_number(conf) and conf >= spec.threshold)
def _hallucination_confirm(sources, data, spec: _HallucinationSpec) -> bool:
    try:
        sources, cross_sources = _normalize_confirm_inputs(
            sources, spec.cross_sources)
        if not isinstance(data, dict):
            return False
        for ff in _iter_evidence_findings(data):
            if _a2_finding_confirms(ff, spec, sources, cross_sources):
                return True
        return False
    except Exception as e:  # noqa: BLE001
        logger.warning("%s: %s", spec.log_name, e)
        return False
_GATE_REAL_EXECUTION_STATES = _SUCCESS_TERMINAL_STATES | _FAILURE_TERMINAL_STATES
def _dict_path(obj, *keys: str) -> dict:
    cur = obj
    for key in keys:
        cur = cur.get(key) if isinstance(cur, dict) else None
    return cur if isinstance(cur, dict) else {}
def _status_key(value) -> str:
    return str(value).strip().lower()
def _group_status(ir, group: str) -> str:
    return _status_key(_dict_path(ir, group).get("status", ""))
def _sub_result_status(sub_results, sub_id: str) -> str:
    result = _dict_path(sub_results, sub_id, "result")
    return _status_key(result.get("status", ""))
def _rule_guard(rule_name: str):
    def _decorator(fn):
        @wraps(fn)
        def _wrapped(*args, **kwargs):
            try:
                return fn(*args, **kwargs)
            except Exception as e:  # noqa: BLE001
                logger.warning("%s: %s", rule_name, e)
                return False
        return _wrapped
    return _decorator
def check_rule_1(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: bool({"C", "E"} & s),
        families=(get_rule_family_set("dead_code")
                  | get_rule_family_set("unused_symbols")
                  | {"quadrant_dead", "low_coverage",
                     "quadrant_undertested"}),
        log_name="check_rule_1")
def check_rule_2(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "E" in s and bool({"B", "D"} & s),
        families=(get_rule_family_set("security")
                  | get_rule_family_set("security_extended")),
        log_name="check_rule_2")
def check_rule_3(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "B" in s and "E" in s,
        families=get_rule_family_set("complexity"),
        log_name="check_rule_3")
def _rule4_has_high_severity(findings: list) -> bool:
    return any(
        _norm_severity(f) in HIGH_SEVERITY_PROTECTED
        for f in findings if isinstance(f, dict)
    )
def _rule4_max_confidence(findings: list) -> float:
    return max(
        (f.get("confidence") for f in findings
         if isinstance(f, dict) and is_real_number(f.get("confidence"))),
        default=0.0,
    )
_WL_FAMILIES_CACHE: frozenset[str] | None = None
def _rule4_whitelist_families() -> frozenset[str]:
    global _WL_FAMILIES_CACHE
    if _WL_FAMILIES_CACHE is None:
        _WL_FAMILIES_CACHE = (
            get_rule_family_set("security")
            | get_rule_family_set("security_extended")
            | get_rule_family_set("syntax_runtime")
            | get_rule_family_set("resource_leak") | {"handle_leak"}
            | get_rule_family_set("concurrency")
        )
    return _WL_FAMILIES_CACHE
def _rule4_has_whitelist_family(findings: list) -> bool:
    _wl_families = _rule4_whitelist_families()
    for f in findings:
        if not isinstance(f, dict):
            continue
        rf_raw = finding_family(f)
        if not rf_raw:
            continue
        if rf_raw in _wl_families or normalize_rule(rf_raw) in _wl_families:
            return True
    return False
def _has_specific_location(f: dict) -> bool:
    return _finding_location(f) is not None
def _confidence_at_least(f: dict, threshold: float) -> bool:
    conf = f.get("confidence")
    return is_real_number(conf) and conf >= threshold
def _is_protected_duplicate(f: dict) -> bool:
    rf = finding_family(f)
    if not rf:
        return False
    rf_norm = normalize_rule(rf)
    if rf not in ("duplicate_code", "AP-C11") \
            and rf_norm not in ("duplicate_code", "AP-C11"):
        return False
    return (_has_specific_location(f)
            or _confidence_at_least(f, SINGLE_SOURCE_CONFIRM_THRESHOLD)
            or _norm_severity(f) in HIGH_SEVERITY_PROTECTED)
def _rule4_has_protected_duplicate(findings: list) -> bool:
    for f in findings:
        if not isinstance(f, dict):
            continue
        if _is_protected_duplicate(f):
            return True
    return False
def _e_group_data(independent_results: dict | None) -> dict:
    if not isinstance(independent_results, dict):
        return {}
    e_data = independent_results.get("E")
    return e_data if isinstance(e_data, dict) else {}
def _e_group_payload(e_data: dict) -> dict:
    payload = e_data.get("payload", {})
    return payload if isinstance(payload, dict) else {}
def _pct_or_zero(val: float) -> float:
    return val if 0.0 <= val <= 100.0 else 0.0
def _pct_scaled(value) -> float:
    _v = float(value)
    return _pct_or_zero(_v * 100.0 if _v <= 1.0 else _v)
def _coverage_from_sub_results(host: dict) -> dict:
    if not isinstance(host, dict):
        return {}
    subs = host.get("sub_results")
    if not isinstance(subs, dict):
        return {}
    for key in ("E1", "F1"):
        entry = subs.get(key)
        if not isinstance(entry, dict):
            continue
        result = entry.get("result")
        if not isinstance(result, dict):
            continue
        payload = result.get("payload")
        for host_layer in (result, payload if isinstance(payload, dict) else {}):
            coverage = host_layer.get("coverage")
            if isinstance(coverage, dict) and coverage:
                return coverage
    return {}
def _coverage_mapping(host) -> dict | None:
    if not isinstance(host, dict):
        return None
    coverage = host.get("coverage")
    return coverage if isinstance(coverage, dict) and coverage else None
def _f1_coverage_metrics(f1_payload: dict) -> dict:
    if not isinstance(f1_payload, dict):
        return {}
    coverage = _coverage_mapping(f1_payload)
    if coverage:
        return coverage
    inner = f1_payload.get("payload")
    coverage = _coverage_mapping(inner)
    if coverage:
        return coverage
    for host in (f1_payload, inner):
        coverage = _coverage_from_sub_results(host)
        if coverage:
            return coverage
    return f1_payload
def _f1_overall_coverage_pct(f1_payload: dict) -> float | None:
    metrics = _f1_coverage_metrics(f1_payload)
    val = metrics.get("overall_coverage_pct")
    if is_real_number(val):
        return _pct_or_zero(float(val))
    val = metrics.get("overall_coverage")
    if is_real_number(val):
        return _pct_scaled(val)
    return None
def _file_cov_from_module_coverage(metrics: dict) -> dict[str, float]:
    return _aggregate_module_coverage(
        metrics.get("module_coverage") or metrics.get("modules"))
def _file_cov_from_mapping(metrics: dict) -> dict[str, float]:
    result: dict[str, float] = {}
    for key in ("coverage_by_file", "file_coverage"):
        mapping = metrics.get(key)
        if isinstance(mapping, dict) and mapping:
            for fpath, val in mapping.items():
                if (isinstance(fpath, str) and is_real_number(val)
                        and 0.0 <= val <= 100.0):
                    result[fpath] = float(val)
            if result:
                return result
    return result
def _file_cov_from_func_coverage(metrics: dict) -> dict[str, float]:
    func_coverage = metrics.get("func_coverage")
    if not (isinstance(func_coverage, dict) and func_coverage):
        return {}
    return _aggregate_func_coverage(func_coverage)
def _f1_file_coverage_map(f1_payload: dict) -> dict[str, float]:
    metrics = _f1_coverage_metrics(f1_payload)
    for strategy in (_file_cov_from_mapping,
                     _file_cov_from_func_coverage,
                     _file_cov_from_module_coverage):
        result = strategy(metrics)
        if result:
            return result
    return {}
def _affected_file_paths(findings: list) -> set:
    paths: set = set()
    for f in findings:
        if not isinstance(f, dict):
            continue
        ffile = finding_file_path(f)
        if ffile:
            paths.add(ffile)
    return paths
def _matching_coverage_values(file_path: str,
                              coverage_by_file: dict) -> list:
    matching_paths = set(_unambiguous_file_paths(file_path, coverage_by_file))
    return [
        cov for cov_path, cov in coverage_by_file.items()
        if cov_path in matching_paths and is_real_number(cov)
    ]
def _file_well_covered(file_path: str, coverage_by_file: dict) -> bool:
    return any(
        cov >= COVERAGE_LOW_THRESHOLD
        for cov in _matching_coverage_values(file_path, coverage_by_file))
def _files_well_covered(affected_files: set, coverage_by_file: dict) -> bool:
    return all(
        _file_well_covered(af, coverage_by_file) for af in affected_files
    )
def _rule4_file_coverage_ok(affected_files: set, coverage_by_file: dict) -> bool:
    if not affected_files:
        return True
    if not coverage_by_file:
        return False
    return _files_well_covered(affected_files, coverage_by_file)
def _rule4_global_coverage_ok(e_payload: dict) -> bool:
    coverage = _f1_overall_coverage_pct(e_payload)
    return coverage is not None and coverage >= COVERAGE_LOW_THRESHOLD
def _rule4_check_f1_coverage(findings: list, independent_results: dict) -> bool:
    e_data = _e_group_data(independent_results)
    affected_files = _affected_file_paths(findings)
    if affected_files:
        return _rule4_file_coverage_ok(
            affected_files, _f1_file_coverage_map(_e_group_payload(e_data)))
    return _rule4_global_coverage_ok(_e_group_payload(e_data))
_RULE4_P2_CONF_CEILING = 0.75
def _rule4_confidence_gate(findings: list, max_conf: float) -> bool:
    if max_conf >= CONF_VERY_HIGH:
        return False
    if max_conf < CONF_FLOOR and _rule4_has_whitelist_family(findings):
        return False
    has_p2 = any(normalize_severity_rank(f.get("severity")) == 2
                 for f in findings if isinstance(f, dict))
    return not (has_p2 and max_conf >= _RULE4_P2_CONF_CEILING)
def _rule4_weak_evidence_ok(findings: list) -> bool:
    if _rule4_has_high_severity(findings):
        return False
    if _rule4_has_protected_duplicate(findings):
        return False
    return _rule4_confidence_gate(findings, _rule4_max_confidence(findings))
@_rule_guard("check_rule_4")
def check_rule_4(sources: list[str], data: dict, independent_results: dict | None = None) -> bool:
    sources = clean_source_ids(sources)
    if not (_ENGINE_SOURCE_GROUPS & set(sources)):
        return False
    if count_independent_sources(sources) >= 2:
        return False
    findings = list(_iter_evidence_findings(data))
    e_status = _group_status(independent_results, "E")
    if not _rule4_weak_evidence_ok(findings):
        return False
    if e_status not in _PASS_TERMINAL_STATES:
        return False
    return _rule4_check_f1_coverage(findings, independent_results)
@_rule_guard("rule4_low_coverage_blindspot")
def rule4_low_coverage_blindspot(_sources: list[str], data: dict,
                                 independent_results: dict | None = None) -> bool:
    e_data = _e_group_data(independent_results)
    e_payload = _e_group_payload(e_data)
    affected_files = _affected_file_paths(list(_iter_evidence_findings(data)))
    if not affected_files:
        return False
    file_coverage = _f1_file_coverage_map(e_payload)
    if not file_coverage:
        return False
    return any(
        not _file_well_covered(fname, file_coverage)
        for fname in affected_files
    )
@_rule_guard("check_rule_5")
def check_rule_5(sources: list[str], data: dict, independent_results: dict | None = None) -> bool:
    has_analysis = bool(_DIAGNOSIS_SOURCE_GROUPS & _source_set(sources))
    if _has_test_engine_cross(data) and has_analysis:
        return False
    if _group_status(independent_results, "E") not in _FAILURE_TERMINAL_STATES:
        return False
    return bool(_has_family(data, _TEST_FAILURE_FAMILIES) or not has_analysis)
def check_rule_6(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: bool({"A", "B"} & s),
        families={"syntax_error"},
        log_name="check_rule_6")
def check_rule_7(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "B" in s and "E" in s,
        families=get_rule_family_set("circular_dep"),
        log_name="check_rule_7")
def _rule8_has_high_confidence(findings, broad_except_set) -> bool:
    for f in findings:
        if finding_family(f) not in broad_except_set:
            continue
        conf = f.get("confidence", 0)
        if is_real_number(conf) and conf >= CONF_HIGH:
            return True
    return False
@_rule_guard("check_rule_8")
def check_rule_8(sources: list[str], data: dict, independent_results: dict | None = None) -> bool:
    src = _source_set(sources)
    if not bool({"C", "B"} & src):
        return False
    broad_except_set = get_rule_family_set("broad_except")
    if not _has_family(data, broad_except_set):
        return False
    e_status = _group_status(independent_results, "E")
    if e_status in _FAILURE_TERMINAL_STATES:
        return True
    if e_status in _SUCCESS_TERMINAL_STATES:
        return (count_independent_sources(list(src)) >= 2
                or _rule8_has_high_confidence(
                    _iter_evidence_findings(data), broad_except_set))
    return False
def check_rule_9(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "B" in s and "E" in s,
        families=(get_rule_family_set("mutable_global")
                  | {RULE_MUTABLE_DEFAULT, "stress_issue"}),
        log_name="check_rule_9")
@_rule_guard("check_rule_10")
def check_rule_10(sources: list[str], data: dict) -> bool:
    src = _source_set(sources)
    if "E" not in src:
        return False
    if not (_DIAGNOSIS_SOURCE_GROUPS & src):
        return False
    return _has_family(data, _RECURSION_FAMILIES)
def check_rule_11(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "C" in s and "E" in s,
        families=(get_rule_family_set("broken_call")
                  | {"GF-08", "broken_cross_call"}),
        log_name="check_rule_11")
def check_rule_12(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: bool({"D", "B"} & s) and "E" in s,
        families={"path_traversal", "SE-06", "PT-01"},
        log_name="check_rule_12")
def check_rule_13(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "B" in s and "E" in s,
        families=get_rule_family_set("god_file") | {"GF-11", "SZ-01"},
        log_name="check_rule_13")
@_rule_guard("check_rule_14")
def check_rule_14(sources: list[str], _data: dict) -> bool:
    if count_independent_sources(sources) < 2:
        return False
    return any(True for _ in _iter_evidence_findings(_data))
_RULE15_KNOWN_FP_MIN_CONFIDENCE = 0.20
def _is_dynamic_high_fp_family(rf: str) -> bool:
    if not rf:
        return False
    try:
        rec = RULE_FP_TRACKER.get(rf)
        if not isinstance(rec, dict):
            return False
        total = rec.get("total", 0)
        if not is_real_number(total) or total < 5:
            return False
        fp_rate = rec.get("fp_rate", 0.0)
        return is_valid_fp_rate(fp_rate) and fp_rate >= FP_RATE_CRITICAL
    except Exception as e:  # noqa: BLE001
        logger.warning("_is_dynamic_high_fp_family(%s): %s", rf, e)
        return False
def _mark_high_conf_backstops(f: dict, rf: str, is_known_fp: bool) -> None:
    if rf and _reliability_base(rf) < LOW_RELIABILITY_BASE:
        f["_low_reliability_high_conf"] = True
    elif is_known_fp:
        f["_known_fp_high_severity"] = True
def _is_known_high_fp_family(rf_raw: str, rf_norm: str) -> bool:
    keys = (rf_raw,) if rf_norm == rf_raw else (rf_raw, rf_norm)
    return (any(key in KNOWN_HIGH_FP_FAMILIES for key in keys)
            or any(_is_dynamic_high_fp_family(key) for key in keys))
def _rule15_family_tags(f: dict) -> tuple[str, str, bool]:
    rf_raw = finding_family(f)
    rf_norm = normalize_rule(rf_raw) if rf_raw else ""
    return rf_raw, rf_norm, _is_known_high_fp_family(rf_raw, rf_norm)
def _rule15_high_severity_hit(f: dict, rf_norm: str, is_known_fp: bool,
                              is_default_conf: bool) -> bool:
    conf = f.get("confidence", 0.5)
    if not is_real_number(conf):
        return False
    if is_known_fp and conf < _RULE15_KNOWN_FP_MIN_CONFIDENCE:
        return False
    if conf >= SINGLE_SOURCE_CONFIRM_THRESHOLD:
        if not is_default_conf:
            _mark_high_conf_backstops(f, rf_norm, is_known_fp)
        return True
    if conf >= CONF_FLOOR:
        f["_low_confidence_high_severity"] = True
        return True
    return False
def _rule15_finding_hit(f: dict) -> bool:
    sev = _norm_severity(f)
    _rf_raw, rf_norm, is_known_fp = _rule15_family_tags(f)
    is_default_conf = is_default_confidence(f)
    if sev in HIGH_SEVERITY_PROTECTED:
        return _rule15_high_severity_hit(
            f, rf_norm, is_known_fp, is_default_conf)
    if is_default_conf:
        return False
    conf = f.get("confidence")
    if is_real_number(conf) and conf >= SINGLE_SOURCE_CONFIRM_THRESHOLD:
        _mark_high_conf_backstops(f, rf_norm, is_known_fp)
        return True
    return False
@_rule_guard("check_rule_15")
def check_rule_15(sources: list[str], data: dict) -> bool:
    sources = clean_source_ids(sources)
    if count_independent_sources(sources) != 1:
        return False
    matched = False
    for f in _iter_evidence_findings(data):
        if _rule15_finding_hit(f):
            matched = True
    return matched
@_rule_guard("check_rule_17")
def check_rule_17(sources: list[str], data: dict) -> bool:
    if "B" not in _source_set(sources):
        return False
    return (_has_sub_engine(data, "B1", evidence_only=True)
            and _has_sub_engine(data, "B2", evidence_only=True))
@_rule_guard("check_rule_18")
def check_rule_18(sources: list[str], data: dict,
                  independent_results: dict | None = None) -> bool:
    src = _source_set(sources)
    has_gate = False
    if "F" in src:
        f_sub = _dict_path(independent_results, "F", "payload", "sub_results")
        has_gate = any(
            _sub_result_status(f_sub, gate_sub)
            in _GATE_REAL_EXECUTION_STATES
            for gate_sub in ("F3", "F2"))
    _independent = set(independent_sources(list(src)))
    has_other = bool(_independent - {"F"})
    has_gate_family = _has_family(data, ("gate_failed", "gate_issue"))
    return has_gate and has_other and has_gate_family
def check_rule_19(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "B" in s and "E" in s,
        families=REGRESSION_FAMILIES,
        log_name="check_rule_19")
_APPLIED_FIX_COUNT_FIELDS: tuple[str, ...] = (
    "succeeded", "fixed", "fixes_applied", "fixed_count")
def _applied_fix_count(f1_result: dict) -> int:
    if not isinstance(f1_result, dict):
        return 0
    applied = 0
    for field in _APPLIED_FIX_COUNT_FIELDS:
        raw = f1_result.get(field)
        # 字段缺失是正常业务态，直接跳过，不走 safe_int 的异常通道。
        if raw is None:
            continue
        count = safe_int(raw, -1)
        if count >= 0:
            applied = count
            if field == "fixes_applied":
                return applied
            break
    ai_fixed = f1_result.get("ai_fixed")
    if ai_fixed is None:
        return applied
    return applied + max(0, safe_int(ai_fixed, 0))
def _rule20_f1_f3_state(independent_results: dict | None) -> tuple:
    f_sub = _dict_path(independent_results, "F", "payload", "sub_results")
    f1_result = _dict_path(f_sub, "F1", "result")
    f1_fixes = _applied_fix_count(f1_result)
    f3_status = _sub_result_status(f_sub, "F3")
    return f1_result, f1_fixes, f3_status
def _rule20_p0_after_fix_count(all_findings) -> int:
    return sum(1 for f in all_findings
               if isinstance(f, dict)
               and normalize_severity_rank(f.get("severity")) == 0
               and (_source_main_ids(f) & _DIAGNOSIS_SOURCE_GROUPS))
def _rule20_outcome(e_status: str, f3_status: str, f1_result: dict,
                    all_findings) -> bool:
    if e_status in _FAILURE_TERMINAL_STATES or f3_status in _FAILURE_TERMINAL_STATES:
        return True
    if (e_status not in _SUCCESS_TERMINAL_STATES
            or f3_status not in _PASS_TERMINAL_STATES):
        return False
    f1_rolled_back = f1_result.get("rolled_back", 0)
    if (f1_rolled_back is True
            or (is_real_number(f1_rolled_back) and f1_rolled_back > 0)
            or safe_int(f1_rolled_back, 0) > 0):
        return True
    return _rule20_p0_after_fix_count(all_findings) <= 0
@_rule_guard("check_rule_20")
def check_rule_20(sources: list[str], data: dict, independent_results: dict | None = None, all_findings: list | None = None) -> bool:
    if not isinstance(all_findings, (list, tuple)):
        all_findings = findings_container(data)
    f1_result, f1_fixes, f3_status = _rule20_f1_f3_state(
        independent_results)
    if f1_fixes <= 0:
        return False
    has_f3 = f3_status in _GATE_REAL_EXECUTION_STATES
    has_e = "E" in _source_set(sources)
    if not (has_e and has_f3):
        return False
    e_status = _group_status(independent_results, "E")
    return _rule20_outcome(e_status, f3_status, f1_result, all_findings)
def check_rule_21(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "B" in s,
        families={"dynamic_import", "dynamic_binding"},
        log_name="check_rule_21")
@_rule_guard("rule21_runtime_idle")
def rule21_runtime_idle(_sources: list[str], data: dict) -> bool:
    return _any_finding(
        data, lambda ff: "B1" in _detector_ids(ff)
        and ff.get("runtime_triggered") is False)
@_rule_guard("check_rule_22")
def check_rule_22(sources: list[str], data: dict) -> bool:
    if "D" not in _source_set(sources):
        return False
    subs = _sub_engines_union(data)
    return "D1" in subs and "D2" in subs
@_rule_guard("rule22_unreachable")
def rule22_unreachable(_sources: list[str], data: dict) -> bool:
    return _any_finding(
        data, lambda ff: "D2" in _detector_ids(ff)
        and ff.get("path_feasible") is False)
@_rule_guard("check_rule_23")
def check_rule_23(sources: list[str], data: dict) -> bool:
    if set(independent_sources(list(_source_set(sources)))) != {"F"}:
        return False
    f4 = _f4_findings(data)
    if not f4:
        return False
    return not any(
        _status_key(ff.get("verify_status")) == "regressed" for ff in f4)
@_rule_guard("rule23_equivalence_ok")
def rule23_equivalence_ok(_sources: list[str], data: dict) -> bool | str:
    f4_findings = _f4_findings(data)
    if not f4_findings:
        return False
    if all(ff.get("equivalence_ok") is True for ff in f4_findings):
        return True
    return "investigated"
def check_rule_26(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "B" in s,
        families=get_rule_family_set("concurrency"),
        log_name="check_rule_26")
@_rule_guard("rule26_concurrency_risky")
def rule26_concurrency_risky(_sources: list[str], data: dict) -> bool:
    return _any_finding(
        data, lambda ff: "B1" in _detector_ids(ff)
        and ff.get("rule_id", "") == "CS-UNPROTECTED")
def check_rule_27(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "A" in s and "B" in s,
        families=get_rule_family_set("doc_consistency"),
        log_name="check_rule_27")
@_rule_guard("rule27_doc_orphan")
def rule27_doc_orphan(_sources: list[str], data: dict) -> bool:
    return _any_finding(
        data, lambda ff: "A4" in _detector_ids(ff)
        and ff.get("rule_id", "") == "DOC-ORPHAN"
        and is_real_number(ff.get("confidence", 0))
        and ff.get("confidence", 0) >= CONF_MEDIUM)
@_rule_guard("check_rule_28")
def check_rule_28(sources: list[str], data: dict) -> bool:
    src = _source_set(sources)
    if "B" not in src:
        return False
    has_b2 = _has_sub_engine(data, "B2", evidence_only=True)
    has_cross = "E" in src or _has_sub_engine(data, "B1", evidence_only=True)
    return has_b2 and has_cross
def _cross_evidence_index(data: dict) -> set[tuple[str, int]]:
    index: set[tuple[str, int]] = set()
    for ff in _iter_evidence_findings(data):
        if not (_detector_ids(ff) & {"B1", "E1"}):
            continue
        location = _finding_location_key(ff)
        if location is not None:
            index.add(location)
    return index
def _finding_location(ff: dict) -> tuple[str, int] | None:
    file_id = finding_file_path(ff)
    line = safe_finding_line(ff)
    if file_id and line:
        return file_id, line
    return None
def _finding_location_key(ff: dict) -> tuple[str, int] | None:
    location = _finding_location(ff)
    if location is None:
        return None
    file_id, line = location
    normalized = os.path.normcase(
        os.path.normpath(file_id.replace("\\", "/")))
    return normalized, line
def _same_file_identity(left: str, right: str) -> bool:
    if not isinstance(left, str) or not isinstance(right, str):
        return False
    if not left or not right:
        return False
    left_norm = os.path.normcase(os.path.normpath(left.replace("\\", "/")))
    right_norm = os.path.normcase(os.path.normpath(right.replace("\\", "/")))
    if left_norm == right_norm:
        return True
    left_is_base = os.path.basename(left_norm) == left_norm
    right_is_base = os.path.basename(right_norm) == right_norm
    if left_is_base and right_is_base:
        return False
    if left_is_base:
        return right_norm.endswith(os.sep + left_norm)
    if right_is_base:
        return left_norm.endswith(os.sep + right_norm)
    if os.path.isabs(left_norm) != os.path.isabs(right_norm):
        return (left_norm.endswith(os.sep + right_norm)
                or right_norm.endswith(os.sep + left_norm))
    return False
def _unambiguous_file_paths(file_path: str, candidate_paths) -> list[str]:
    candidates = [path for path in candidate_paths
                  if isinstance(path, str) and path]
    if not isinstance(file_path, str) or not file_path:
        return []
    target = os.path.normcase(os.path.normpath(file_path.replace("\\", "/")))
    exact = [
        path for path in candidates
        if os.path.normcase(os.path.normpath(path.replace("\\", "/"))) == target
    ]
    if exact:
        return exact
    fallback = [path for path in candidates
                if _same_file_identity(path, target)]
    identities = {
        os.path.normcase(os.path.normpath(path.replace("\\", "/")))
        for path in fallback
    }
    return fallback if len(identities) == 1 else []
def _b2_has_same_line_cross(data: dict, b2_findings: list) -> bool:
    index = _cross_evidence_index(data)
    for df in b2_findings:
        location = _finding_location_key(df)
        if location is None:
            continue
        file_id, line = location
        same_line_files = {
            other_file for other_file, other_line in index if other_line == line
        }
        if _unambiguous_file_paths(file_id, same_line_files):
            return True
    return False
@_rule_guard("rule28_pattern_confirmed")
def rule28_pattern_confirmed(_sources: list[str], data: dict) -> bool:
    b2_findings = [ff for ff in _iter_evidence_findings(data)
                   if "B2" in _detector_ids(ff)]
    if not b2_findings:
        return False
    return _b2_has_same_line_cross(data, b2_findings)
@_rule_guard("check_rule_29")
def check_rule_29(sources: list[str], data: dict) -> bool:
    src = _source_set(sources)
    if "E" not in src or not _has_sub_engine(
            data, "E2", evidence_only=True):
        return False
    if "B" in src:
        return True
    return _has_test_engine_cross(data)
_MUTATION_SURVIVED_RULE_IDS = frozenset({
    "TM-SURVIVED", "TM-SURVIVED-BATCH",
})
@_rule_guard("rule29_mutation_survived")
def rule29_mutation_survived(_sources: list[str], data: dict) -> bool:
    if not _any_finding(
            data, lambda ff: "E2" in _detector_ids(ff)
            and ff.get("rule_id") in _MUTATION_SURVIVED_RULE_IDS):
        return False
    return not _any_finding(
        data, lambda ff: "E1" in _detector_ids(ff)
        and (_status_key(ff.get("status")) in _FAILURE_TERMINAL_STATES
             or normalize_severity_rank(ff.get("severity")) <= 1))
def check_rule_24(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "B" in s,
        families=get_rule_family_set("broad_except"),
        log_name="check_rule_24")
def check_rule_25(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=lambda s: "B" in s and "E" in s,
        families=get_rule_family_set("api_compat"),
        log_name="check_rule_25")
_H1_SPEC = _HallucinationSpec(
    log_name="check_rule_H1",
    families=frozenset({
        "hallucination", "hallucinated_api", "hallucinated_import",
        "hallucinated_exception", "context_contradiction",
        "ai_slop", "test_illusion", "memory_hallucination",
        "sandbox_reflection", "hallucination_general",
    }),
    cross_sources=frozenset({"B"}),
    same_group_cross=True,
)
_H2_SPEC = _HallucinationSpec(
    log_name="check_rule_H2",
    families=frozenset({"hallucinated_import", "hallucination"}),
    cross_sources=frozenset({"C", "B"}))
_H4_SPEC = _HallucinationSpec(
    log_name="check_rule_H4",
    families=frozenset({"context_contradiction", "hallucination"}),
    cross_sources=frozenset({"B"}))
_H6_SPEC = _HallucinationSpec(
    log_name="check_rule_H6",
    families=frozenset({"test_illusion", "hallucination"}),
    cross_sources=frozenset({"E"}))
_H7_SPEC = _HallucinationSpec(
    log_name="check_rule_H7",
    families=frozenset({"memory_hallucination", "hallucination"}),
    cross_sources=frozenset({"B"}))
_H8_SPEC = _HallucinationSpec(
    log_name="check_rule_H8",
    families=frozenset({"sandbox_reflection", "hallucination"}),
    cross_sources=frozenset({"D", "E"}), threshold=0.80)
def check_rule_H1(sources: list[str], data: dict) -> bool:
    return _hallucination_confirm(sources, data, _H1_SPEC)
def check_rule_H2(sources: list[str], data: dict) -> bool:
    return _hallucination_confirm(sources, data, _H2_SPEC)
def check_rule_H4(sources: list[str], data: dict) -> bool:
    return _hallucination_confirm(sources, data, _H4_SPEC)
def check_rule_H6(sources: list[str], data: dict) -> bool:
    return _hallucination_confirm(sources, data, _H6_SPEC)
def check_rule_H7(sources: list[str], data: dict) -> bool:
    return _hallucination_confirm(sources, data, _H7_SPEC)
def check_rule_H8(sources: list[str], data: dict) -> bool:
    return _hallucination_confirm(sources, data, _H8_SPEC)
_COLD_START_MIN_TOTAL = 5
_COLD_START_FP_CEILING = 0.50
def check_rule_30(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("B", "E")),
        families=REGRESSION_FAMILIES,
        log_name="check_rule_30")
def check_rule_31(_sources: list[str], _data: dict) -> bool:
    return False
def check_rule_32(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("A", "B")),
        families=get_rule_family_set("config_security"),
        log_name="check_rule_32")
def check_rule_33(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("B", "E")),
        families={
            "type_check", "type_error",
            "test_smell", "test_error", "test_failure",
            "method_anomaly", "test_quality",
        },
        normalize=True,
        log_name="check_rule_33")
def check_rule_34(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("B",), any_of=("C", "E")),
        families={"implicit_dep", "dynamic_import"},
        log_name="check_rule_34")
def _tracker_sample(fp_key: str) -> tuple | None:
    if not isinstance(fp_key, str) or fp_key not in RULE_FP_TRACKER:
        return None
    tracker = RULE_FP_TRACKER[fp_key]
    if not isinstance(tracker, dict):
        return None
    total = tracker.get("total", 0)
    if not is_real_number(total) or total <= 0:
        return None
    fp_rate = tracker.get("fp_rate")
    if not is_valid_fp_rate(fp_rate):
        return None
    return total, fp_rate
def _fp_rate_state(value: float, low_below: float,
                   high_above: float) -> str | None:
    if value <= low_below:
        return "low"
    if value >= high_above:
        return "high"
    return None
def _rule35_tracker_mark(fp_key: str) -> str | None:
    sample = _tracker_sample(fp_key)
    if sample is None:
        return None
    total, fp_rate = sample
    if total < _COLD_START_MIN_TOTAL and fp_rate <= _COLD_START_FP_CEILING:
        return None
    return _fp_rate_state(fp_rate, FP_RATE_MEDIUM, FP_RATE_CRITICAL)
def _rule35_finding_flags(ff) -> tuple[bool, bool]:
    rule_id = _str_field(ff, "rule_id")
    flag = None
    source_method = _str_field(ff, "_source_method")
    sub_rules = METHOD_SUB_RULES.get(_source_main_of(source_method), {})
    if isinstance(sub_rules, dict) and rule_id in sub_rules:
        sub_entry = sub_rules[rule_id]
        if isinstance(sub_entry, dict):
            fp_rate = sub_entry.get("fp_rate")
            if is_valid_fp_rate(fp_rate):
                flag = _fp_rate_state(
                    fp_rate, FP_RATE_LOW, FP_RATE_HIGH)
    rf_key = _str_field(ff, "rule_family") or rule_id
    rf_normalized = normalize_rule(rf_key) if rf_key else ""
    marks = {
        flag,
        *(_rule35_tracker_mark(key)
          for key in (rule_id, rf_key, rf_normalized)),
    }
    return "low" in marks, "high" in marks
def check_rule_35(_sources: list[str], data: dict) -> bool:
    try:
        has_high_fp = False
        has_low_fp = False
        for ff in _iter_evidence_findings(data):
            low, high = _rule35_finding_flags(ff)
            has_low_fp = has_low_fp or low
            has_high_fp = has_high_fp or high
        return bool(has_low_fp and not has_high_fp)
    except Exception as e:  # noqa: BLE001
        logger.warning("check_rule_35: %s", e)
        return False
_GOD_FILE_FAMILIES = frozenset({
    "god_file", "large_codebase", "architecture", "god_module",
})
_LOW_COMPLEXITY_FAMILIES = frozenset({"low_complexity", "simple_code"})
def _semantic_contradiction_flags(data: dict) -> tuple[bool, bool]:
    has_god_file = False
    has_low_complexity = False
    for ff in _iter_dict_findings(data):
        rf = _normalized_family(ff)
        if rf in _GOD_FILE_FAMILIES:
            has_god_file = True
        if rf in _LOW_COMPLEXITY_FAMILIES:
            has_low_complexity = True
    return has_god_file, has_low_complexity
def check_rule_36(sources: list[str], data: dict) -> bool:
    try:
        sources, _ = _normalize_confirm_inputs(sources, None)
        if "B" not in sources or "E" not in sources:
            return False
        has_god_file, has_low_complexity = _semantic_contradiction_flags(data)
        return has_god_file and has_low_complexity
    except Exception as e:  # noqa: BLE001
        logger.warning("check_rule_36: %s", e)
        return False
def check_rule_42(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("B", "E")),
        families={"perf_hotspot"},
        normalize=True, log_name="check_rule_42")
def check_rule_43(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("C", "E")),
        families={"resource_leak"},
        normalize=True, log_name="check_rule_43")
def check_rule_44(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("B", "E")),
        families={"compatibility", "api_change", "api_issue",
                  "api_compat"},
        normalize=True, log_name="check_rule_44")
def check_rule_45(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("B", "E")),
        families={"test_smell",
                  "test_quality", "dead_code"},
        normalize=True, log_name="check_rule_45")
def check_rule_46(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(any_of=("B", "E")),
        families={"high_coupling",
                  "quality_score", "health_score",
                  "god_file", RULE_HIGH_COMPLEXITY,
                  CAT_MAINTAINABILITY},
        normalize=True, log_name="check_rule_46")
def check_rule_47(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("D", "E")),
        families={"sql_injection", "path_traversal", RULE_HARDCODED_CREDENTIAL,
                  "danger_pattern"},
        normalize=True, log_name="check_rule_47")
def check_rule_48(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(any_of=("A", "D", "E"), min_hits=2),
        families={"config_drift",
                  "config_security"},
        normalize=True, log_name="check_rule_48")
def check_rule_49(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("A", "B")),
        families={"type_check", "type_error"},
        normalize=True, log_name="check_rule_49")
def check_rule_50(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("B", "C")),
        families={"implicit_dep", "dynamic_import"},
        log_name="check_rule_50")
def check_rule_51(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("A", "D")),
        families={"config_drift", "doc_consistency"},
        normalize=True, log_name="check_rule_51")
def check_rule_52(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(any_of=("A", "B")),
        families={"A1-over_limit", "A1-all_overwrite"},
        rule_id_first=True, log_name="check_rule_52")
def check_rule_53(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(any_of=("A", "B")),
        families={"A1-all_overwrite", "A1-import_override", "A1-undefined_name", "A1-broad_except"},
        rule_id_first=True, log_name="check_rule_53")
def check_rule_54(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(any_of=("A", "B")),
        families={"A1-over_limit"},
        rule_id_first=True, log_name="check_rule_54")
def check_rule_55(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("A", "B")),
        families={"cohesion_cycle"},
        log_name="check_rule_55")
def check_rule_56(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("A", "B")),
        families={"cohesion_split"},
        log_name="check_rule_56")
def check_rule_57(sources: list[str], data: dict) -> bool:
    return _match_rule_families(
        sources, data,
        gate=_source_gate(all_of=("A", "B")),
        families={"cohesion_migration"},
        log_name="check_rule_57")
PHASE_MODULE_DEPS: dict[str, str] = {
    "规则37": "xv_baseline",
    "规则38": "xv_phase_rules",
    "规则39": "xv_ref_depth",
    "规则40": "xv_ensemble",
    "规则41": "xv_mutation",
}
class PhaseModuleState:
    def __init__(self):
        self._available: dict[str, bool] = {}
    def set(self, module_name: str, available: bool) -> None:
        self._available[module_name] = available
    def is_module_available(self, module_name: str) -> bool:
        return bool(self._available.get(module_name, True))
    def is_available(self, rule_id: str) -> bool:
        try:
            dep = PHASE_MODULE_DEPS.get(rule_id)
            if dep is None:
                return True
            return self._available.get(dep, True)
        except Exception as e:  # noqa: BLE001
            logger.warning("is_available: %s", e)
            return True
_phase_module_state = PhaseModuleState()
def is_module_available(module_name: str) -> bool:
    try:
        return _phase_module_state.is_module_available(module_name)
    except Exception as e:  # noqa: BLE001
        logger.warning("is_module_available: %s", e)
        return True
def set_phase_module_status(module_name: str, available: bool) -> None:
    try:
        _phase_module_state.set(module_name, available)
    except Exception:
        logger.exception("[set_phase_module_status] 异常降级")
def is_phase_module_available(rule_id: str) -> bool:
    try:
        return _phase_module_state.is_available(rule_id)
    except Exception:
        logger.exception("[is_phase_module_available] 异常降级")
        return True
def _check_phase_module(rule_id: str, data: dict) -> bool:
    if not isinstance(data, dict):
        return False
    if not is_phase_module_available(rule_id):
        data["_phase_degraded"] = True
        data["_phase_degraded_rule"] = rule_id
        data["_phase_degraded_module"] = PHASE_MODULE_DEPS.get(rule_id, "unknown")
        return False
    return True
_RULE39_CHAIN_DEPTH_MIN = 5
_RULE39_IN_DEGREE_MIN = 5
_SIGNAL_REFDEPTH_ENTRY_POINT = "_refdepth_is_entry_point"
def _phase_findings(rule_id: str, data: dict) -> list[dict] | None:
    if not _check_phase_module(rule_id, data):
        return None
    findings = list(_iter_evidence_findings(data))
    return findings or None
def _has_signal(f: dict, signal_name: str, default: bool = False) -> bool:
    return signal_bool(f.get(signal_name, default))
def _numeric_signal(f: dict, signal_name: str, default: float = 0.0) -> float:
    val = f.get(signal_name, default)
    if not is_real_number(val):
        return default
    return float(val)
def _rule_check_guard(rule_id: str):
    def _decorator(fn):
        @wraps(fn)
        def _wrapped(*args, **kwargs):
            try:
                return fn(*args, **kwargs)
            except Exception:
                logger.exception("[%s] 异常降级", rule_id)
                return False
        return _wrapped
    return _decorator
def _has_any_signal(findings: list[dict], keys: tuple[str, ...]) -> bool:
    return any(key in f for f in findings for key in keys)
def _applicable_findings(rule_id: str, data: dict,
                         signal_keys: tuple[str, ...]) -> list[dict] | None:
    findings = _phase_findings(rule_id, data)
    if not findings:
        return None
    return findings if _has_any_signal(findings, signal_keys) else None
def _has_truthy(findings: list[dict], key: str) -> bool:
    return any(_has_signal(f, key) for f in findings)
def _all_signal_true(findings: list[dict], key: str) -> bool:
    return all(_has_signal(f, key) for f in findings)
def _bool_signal_observation(f: dict, key: str) -> bool | None:
    value = f.get(key)
    if isinstance(value, bool):
        return value
    if is_real_number(value):
        return value != 0
    if not isinstance(value, str):
        return None
    text = value.strip().lower()
    if text in {"true", "yes"}:
        return True
    if text in {"false", "no"}:
        return False
    try:
        number = float(text)
    except (TypeError, ValueError, OverflowError):
        return None
    return number != 0 if math.isfinite(number) else None
def _all_signal_false(findings: list[dict], key: str) -> bool:
    return all(_bool_signal_observation(f, key) is False for f in findings)
def _max_numeric_signal(findings: list[dict], key: str) -> float:
    return max((_numeric_signal(f, key) for f in findings), default=0)
@_rule_check_guard("check_rule_37")
def check_rule_37(_sources: list[str], data: dict) -> bool:
    findings = _applicable_findings("规则37", data, (
        "_baseline_is_new", SIGNAL_BASELINE_PERSISTENT_NOISE,
        SIGNAL_BASELINE_HIT_COUNT))
    if not findings:
        return False
    if any(_has_signal(f, "_baseline_is_new")
           and not _has_signal(f, SIGNAL_BASELINE_PERSISTENT_NOISE)
           for f in findings):
        return True
    persistent = [
        f for f in findings
        if _has_signal(f, SIGNAL_BASELINE_PERSISTENT_NOISE)
    ]
    return bool(persistent) and get_max_severity(
        persistent) in HIGH_SEVERITY_PROTECTED
@_rule_check_guard("check_rule_38")
def check_rule_38(_sources: list[str], data: dict) -> bool:
    findings = _applicable_findings("规则38", data, (
        "_bizflow_reachable", "_bizflow_entry_count",
        "_bizflow_fp_candidate", "_bizflow_unresolved"))
    if not findings:
        return False
    if _has_truthy(findings, "_bizflow_fp_candidate"):
        return False
    if _has_truthy(findings, "_bizflow_reachable"):
        return _max_numeric_signal(findings, "_bizflow_entry_count") >= 1
    if _has_truthy(findings, "_bizflow_unresolved"):
        return False
    return _all_signal_false(findings, "_bizflow_reachable")
@_rule_check_guard("check_rule_39")
def check_rule_39(_sources: list[str], data: dict) -> bool:
    findings = _applicable_findings("规则39", data, (
        SIGNAL_REFDEPTH_IN_DEGREE, SIGNAL_REFDEPTH_CHAIN_DEPTH,
        SIGNAL_REFDEPTH_ISOLATED, _SIGNAL_REFDEPTH_ENTRY_POINT))
    if not findings:
        return False
    max_in_degree = _max_numeric_signal(findings, SIGNAL_REFDEPTH_IN_DEGREE)
    max_chain_depth = _max_numeric_signal(
        findings, SIGNAL_REFDEPTH_CHAIN_DEPTH)
    has_isolated = _has_truthy(findings, SIGNAL_REFDEPTH_ISOLATED)
    has_entry = _has_truthy(findings, _SIGNAL_REFDEPTH_ENTRY_POINT)
    max_sev = get_max_severity(findings)
    return (
        max_chain_depth >= _RULE39_CHAIN_DEPTH_MIN
        or max_in_degree >= _RULE39_IN_DEGREE_MIN
        or has_entry
        or (has_isolated and max_sev in HIGH_SEVERITY_PROTECTED)
    )
@_rule_check_guard("check_rule_40")
def check_rule_40(_sources: list[str], data: dict) -> bool:
    findings = _applicable_findings("规则40", data, (
        "_ensemble_is_confirmed", SIGNAL_ENSEMBLE_LOW_CONFIDENCE,
        SIGNAL_ENSEMBLE_GROUP_COUNT))
    if not findings:
        return False
    has_confirmed = _has_truthy(findings, "_ensemble_is_confirmed")
    all_low_conf = _all_signal_true(
        findings, SIGNAL_ENSEMBLE_LOW_CONFIDENCE)
    return has_confirmed or (
        all_low_conf and _max_numeric_signal(findings, "confidence") >= CONF_VERY_HIGH
    )
@_rule_check_guard("check_rule_41")
def check_rule_41(_sources: list[str], data: dict) -> bool:
    findings = _applicable_findings("规则41", data, (
        SIGNAL_MUTATION_VERIFIED, SIGNAL_MUTATION_CONFIRMED_DEAD))
    if not findings:
        return False
    return _has_truthy(findings, SIGNAL_MUTATION_CONFIRMED_DEAD)
_REFINEMENT_DISPATCH: dict[str, tuple[Any, str, bool]] = {
    "规则21": (rule21_runtime_idle, "suppressed", False),
    "规则22": (rule22_unreachable, "suppressed", False),
    "规则23": (rule23_equivalence_ok, "confirmed", False),
    "规则26": (rule26_concurrency_risky, "confirmed", False),
    "规则27": (rule27_doc_orphan, "confirmed", False),
    "规则28": (rule28_pattern_confirmed, "confirmed", False),
    "规则29": (rule29_mutation_survived, "confirmed", False),
}
def get_refinement(rule_id: str) -> tuple[Any, str, bool] | None:
    return _REFINEMENT_DISPATCH.get(rule_id if isinstance(rule_id, str) else "")
RULE_CHECK_FN_MAP: dict[str, Callable] = {
    "规则1":  check_rule_1,
    "规则2":  check_rule_2,
    "规则3":  check_rule_3,
    "规则4":  check_rule_4,
    "规则5":  check_rule_5,
    "规则6":  check_rule_6,
    "规则7":  check_rule_7,
    "规则8":  check_rule_8,
    "规则9":  check_rule_9,
    "规则10": check_rule_10,
    "规则11": check_rule_11,
    "规则12": check_rule_12,
    "规则13": check_rule_13,
    "规则14": check_rule_14,
    "规则15": check_rule_15,
    "规则17": check_rule_17,
    "规则18": check_rule_18,
    "规则19": check_rule_19,
    "规则20": check_rule_20,
    "规则21": check_rule_21,
    "规则22": check_rule_22,
    "规则23": check_rule_23,
    "规则24": check_rule_24,
    "规则25": check_rule_25,
    "规则26": check_rule_26,
    "规则27": check_rule_27,
    "规则28": check_rule_28,
    "规则29": check_rule_29,
    "规则30": check_rule_30,
    "规则31": check_rule_31,
    "规则32": check_rule_32,
    "规则33": check_rule_33,
    "规则34": check_rule_34,
    "规则35": check_rule_35,
    "规则36": check_rule_36,
    "规则37": check_rule_37,
    "规则38": check_rule_38,
    "规则39": check_rule_39,
    "规则40": check_rule_40,
    "规则41": check_rule_41,
    "规则42": check_rule_42,
    "规则43": check_rule_43,
    "规则44": check_rule_44,
    "规则45": check_rule_45,
    "规则46": check_rule_46,
    "规则47": check_rule_47,
    "规则48": check_rule_48,
    "规则49": check_rule_49,
    "规则50": check_rule_50,
    "规则51": check_rule_51,
    "规则52": check_rule_52,
    "规则53": check_rule_53,
    "规则54": check_rule_54,
    "规则55": check_rule_55,
    "规则56": check_rule_56,
    "规则57": check_rule_57,
    "规则H1": check_rule_H1,
    "规则H2": check_rule_H2,
    "规则H4": check_rule_H4,
    "规则H6": check_rule_H6,
    "规则H7": check_rule_H7,
    "规则H8": check_rule_H8,
}
_PHASE_WORKER_RULES = frozenset({"规则58", "规则59", "规则60", "规则61"})
_OPTIONAL_CHECK_FN_RULES = (
    frozenset({"规则16", "规则31"}) | _PHASE_WORKER_RULES)
def _validate_check_fn_registration() -> list[str]:
    return [
        f"[NO_CHECK_FN] 规则 {rid} 在 RULE_CHECK_FN_MAP 中无 check_fn 注册"
        for rid in sorted(CV_RULES)
        if rid not in RULE_CHECK_FN_MAP and rid not in _OPTIONAL_CHECK_FN_RULES]
try:
    _check_fn_issues = _validate_check_fn_registration()
    if _check_fn_issues:
        logger.warning("[RuleCheckFnValidator] %s", "；".join(_check_fn_issues))
    else:
        logger.info("[RuleCheckFnValidator] check_fn 接线覆盖校验通过")
except Exception as _e:  # noqa: BLE001
    logger.warning("[RuleCheckFnValidator] 校验异常: %s", _e)
_FAMILY_SET_TO_RULE = {
    "dead_code": "规则1",
    "security": "规则2",
    "complexity": "规则3",
    "broad_except": "规则8",
    "circular_dep": "规则7",
    "mutable_global": "规则9",
    "mutable_default": "规则9",
    "trivial_delegation": "规则14",
    "recursion": "规则10",
    "broken_call": "规则11",
    "god_file": "规则13",
    "test_quality": "规则45",
    "perf_hotspot": "规则42",
    "resource_leak": "规则43",
    "api_compat": "规则44",
    CAT_MAINTAINABILITY: "规则46",
    "config_security": "规则48",
    "regression": "规则19",
    "fix_related": "规则20",
    "doc_consistency": "规则27",
    "hallucination": "规则H1",
    "concurrency": "规则26",
    "unused_symbols": "规则1",
    "syntax_runtime": "规则6",
    "security_extended": "规则2",
}
_FAMILY_RULE_OVERRIDES = {
    "path_traversal": "规则12",
    "PT-01": "规则12", "SE-06": "规则12",
    "unsafe_eval": "规则47", RULE_COMMAND_INJECTION: "规则47",
    "undertested": "规则45",
    "method_anomaly": "规则14", "quadrant_dead": "规则1",
    "high_coupling": "规则17", "architecture": "规则17",
    "large_codebase": "规则17",
    RULE_HIGH_COMPLEXITY: "规则13",
    "infinite_loop": "规则42",
    "deep_nesting": "规则46",
    "handle_leak": "规则43",
}
_EXTRA_FAMILY_RULES = {
    "low_coverage": "规则1",
    "quadrant_undertested": "规则1",
    "gate_failed": "规则18", "gate_issue": "规则18",
    "fix_safety_issue": "规则20",
    "baseline_noise": "规则37", "business_flow_dead": "规则38",
    "ref_depth_priority": "规则39", "ensemble_consensus": "规则40",
    "mutation_verified": "规则41",
    CAT_DYNAMIC_BINDING: "规则21", "dynamic_import": "规则21",
    "duplicate_code": "规则14",
    "diag_general": "规则14", "method_pass": "规则14",
    "policy_violation": "规则14", RULE_MISSING_DOCSTRING: "规则14",
    "shadowing_builtin": "规则14", "code_smell": "规则14",
    "sim_failure": "规则14", "quadrant_dynamic": "规则14",
    "lazy_import": "规则14", "facade_antipattern": "规则14",
    "stub_function": "规则14", "priority_rec": "规则14",
    "low_complexity": "规则36", "simple_code": "规则36",
    "e2e_failure": "规则5", "smoke_failure": "规则5",
    "fuzz_crash": "规则10", "stress_issue": "规则9",
    "empty_project": "规则17",
    "type_check": "规则49",
    "undefined_name": "规则14",
    "cohesion": "规则14",
    "cohesion_cycle": "规则55",
    "cohesion_split": "规则56",
    "cohesion_migration": "规则57",
}
def _build_auto_family_to_rules() -> dict[str, str]:
    mapping: dict[str, str] = {}
    for _grp, _members in RULE_FAMILY_SETS.items():
        _rule = _FAMILY_SET_TO_RULE.get(_grp)
        if not _rule:
            continue
        mapping[_grp] = _rule
        for _member in _members:
            # 多组共享成员：同名组（成员自名）优先，否则先声明者优先；
            # 显式覆盖表仍最后生效，避免组遍历顺序静默改写路由。
            if _member == _grp or _member not in mapping:
                mapping[_member] = _rule
    mapping.update(_EXTRA_FAMILY_RULES)
    mapping.update(_FAMILY_RULE_OVERRIDES)
    return mapping
AUTO_FAMILY_TO_RULES = _build_auto_family_to_rules()
def _ordered_family_strings(raw) -> list[str]:
    if not isinstance(raw, SOURCE_SEQUENCE_TYPES):
        return []
    items = [item for item in raw if isinstance(item, str)]
    if isinstance(raw, (set, frozenset)):
        items.sort()
    return items
def _entry_families_list(entry: dict) -> list:
    raw = entry.get("rule_families")
    if isinstance(raw, str):
        items = [raw] if raw else []
    else:
        items = _ordered_family_strings(raw)
    single = entry.get("rule_family")
    fallback = [single] if isinstance(single, str) and single else []
    return items or fallback
def resolve_rule_conflict(_cv2, rule_id: str, sources: list[str],
                            entry: dict) -> str:
    rule_id = safe_rule_id(rule_id)
    try:
        return _resolve_rule_conflict_impl(rule_id, sources, entry)
    except Exception as e:  # noqa: BLE001
        logger.warning("resolve_rule_conflict: %s", e)
        return rule_id
def _conflict_entry_normalized(entry: dict) -> tuple:
    max_conf = entry.get("max_confidence", SINGLE_SOURCE_CONFIRM_THRESHOLD)
    if isinstance(max_conf, bool):
        max_conf = SINGLE_SOURCE_CONFIRM_THRESHOLD
    elif not isinstance(max_conf, (int, float)):
        try:
            max_conf = float(max_conf)
        except (TypeError, ValueError, OverflowError) as _e:
            log_swallowed(
                __name__, _e,
                context=f'_conflict_entry_normalized:{type(_e).__name__}')
            max_conf = SINGLE_SOURCE_CONFIRM_THRESHOLD
    if not is_real_number(max_conf):
        max_conf = SINGLE_SOURCE_CONFIRM_THRESHOLD
    severities = entry.get("severities") or ["P3"]
    if isinstance(severities, str):
        severities = [severities]
    return max_conf, severities
def _single_source_upgrades(highest_rank: int, max_conf: float,
                           is_known_fp: bool) -> bool:
    return (highest_rank <= 1
            and max_conf >= SINGLE_SOURCE_CONFIRM_THRESHOLD
            and not is_known_fp)
def _log_rule4_hold(highest_rank: int, max_conf: float,
                    entry_families: set[str], is_known_fp: bool) -> None:
    if highest_rank <= 1:
        if is_known_fp:
            logger.debug(
                "[RuleConflict] 规则4 保持: P0/P1 但属于已知高FP族 (%s)",
                entry_families & KNOWN_HIGH_FP_FAMILIES
            )
        elif max_conf < SINGLE_SOURCE_CONFIRM_THRESHOLD:
            logger.debug(
                "[RuleConflict] 规则4 保持: P0/P1 单源低置信度 (conf=%.2f)",
                max_conf
            )
        return
    if max_conf < SINGLE_SOURCE_CONFIRM_THRESHOLD:
        logger.debug(
            "[RuleConflict] 规则4 保持: P2/P3 单源低置信度 (conf=%.2f)",
            max_conf
        )
    else:
        logger.debug(
            "[RuleConflict] 规则4 保持: P2/P3 未达严重度门槛 (rank=%d, conf=%.2f)",
            highest_rank, max_conf
        )
def _resolve_rule_conflict_impl(rule_id: str, sources: list[str],
                                entry: dict) -> str:
    if rule_id != "规则4" or count_independent_sources(sources) != 1:
        return rule_id
    max_conf, severities = _conflict_entry_normalized(entry)
    highest_rank = min(
        (normalize_severity_rank(s) for s in severities),
        default=3
    )
    entry_families = {
        normalize_rule(family) for family in _entry_families_list(entry)
    }
    is_known_fp = any(
        _is_known_high_fp_family(family, normalize_rule(family))
        for family in _entry_families_list(entry)
    )
    if _single_source_upgrades(highest_rank, max_conf, is_known_fp):
        logger.debug(
            "[RuleConflict] 规则4 → 规则15: P0/P1 单源非FP族 (conf=%.2f)",
            max_conf
        )
        return "规则15"
    _log_rule4_hold(highest_rank, max_conf, entry_families, is_known_fp)
    return rule_id
_METHOD_TO_RULES: dict[str, str] = {
    "C": "规则1",
    "E": "规则1",
    "D": "规则2",
    "F": "规则20",
    "B": "规则8",
    "A": "规则27",
    "B3": "规则39",
    "M1": "规则41",
}
_METHOD_FAMILY_FILTER: dict[str, frozenset[str]] = {
    "C": frozenset({"resource_leak", "memory_leak", "file_leak",
                    RULE_CONNECTION_LEAK}),
    "B": frozenset({"broad_except", "bare_except", "empty_except",
                    "silent_swallow", RULE_HARDCODED_CREDENTIAL,
                    "danger_pattern", "sql_injection", "path_traversal",
                    "unsafe_eval", RULE_COMMAND_INJECTION}),
    "D": frozenset({RULE_HARDCODED_CREDENTIAL, "danger_pattern",
                    "sql_injection", "path_traversal", "unsafe_eval",
                    RULE_COMMAND_INJECTION}),
}
_RULE_PREFIX_MAP: tuple[tuple[str, str], ...] = tuple(sorted({
    "BE-": "规则8", "EH-": "规则8", "SN-": "规则8",
    "GF-08": "规则11", "GF-07": "规则13", "GF-": "规则13",
    "SE-": "规则2",
    "DC-": "规则1", "CP-": "规则7", "AP-C6": "规则7",
    "SD-": "规则8", "SZ-": "规则3", "C2": "规则3",
    "C2_lazy_import": "规则14",
}.items(), key=lambda kv: -len(kv[0])))
def _normalize_match_entry(entry: dict) -> tuple[str, list, list]:
    rule_id = entry.get("rule_id")
    if not isinstance(rule_id, str):
        rule_id = ""
    families = _entry_families_list(entry)
    sources = clean_source_ids(entry.get("sources", []))
    return rule_id, families, sources
def match_rule(_cv2, entry: dict) -> str | None:
    try:
        return _match_rule_impl(entry)
    except Exception as e:  # noqa: BLE001
        logger.warning("match_rule: %s", e)
        return None
def _canonical_family_alias(family: str) -> str:
    canonical = normalize_rule(family)
    return (canonical
            if canonical_rule_key(canonical) == canonical_rule_key(family)
            else family)
def _match_by_family(families: list[str]) -> str | None:
    for family in families:
        rule = AUTO_FAMILY_TO_RULES.get(family)
        if rule is None:
            rule = AUTO_FAMILY_TO_RULES.get(_canonical_family_alias(family))
        if rule is not None:
            return rule
    return None
def _match_by_source(sources: list, families: list[str]) -> str | None:
    entry_families = {_canonical_family_alias(family) for family in families}
    for source in sources:
        if not isinstance(source, str):
            continue
        rule = _METHOD_TO_RULES.get(source)
        if rule is None:
            continue
        allowed_families = _METHOD_FAMILY_FILTER.get(source)
        if allowed_families is not None and not (entry_families & allowed_families):
            continue
        return rule
    return None
def _match_by_prefix(rule_id: str) -> str | None:
    upper = rule_id.upper()
    for prefix, rule in _RULE_PREFIX_MAP:
        if upper.startswith(prefix.upper()):
            return rule
    return None
def _match_rule_impl(entry: dict) -> str | None:
    rule_id, families, sources = _normalize_match_entry(entry)
    specific_families = [
        family for family in families
        if _canonical_family_alias(family) != "diag_general"
    ]
    return (_match_by_family(specific_families)
            or _match_by_prefix(rule_id)
            or _match_by_family(families)
            or _match_by_source(sources, families))
_RULE_PREFIX_ALLOWED_SETS: dict[str, frozenset[str]] = {
    "SE": RULE_FAMILY_SETS.get("security", frozenset()),
    "PT": RULE_FAMILY_SETS.get("security", frozenset()),
}
def _report_issues(issues: list[str], warn_template: str,
                   label: str) -> list[str]:
    if not issues:
        return issues
    for item in issues:
        logger.warning(warn_template, item)
    logger.info("[FamilyMapValidator] 发现 %d 个%s", len(issues), label)
    return issues
def _report_unmapped_families(mapped_families: frozenset[str]) -> list[str]:
    return _report_issues(
        sorted(set(RULE_FAMILY_MAP.values()) - mapped_families
               - {"unknown", "diag_general"}),
        "[FamilyMapValidator] rule_family '%s' 在 match_rule 的 "
        "family_to_rules 中无映射",
        "未映射的 rule_family")
def _report_broken_group_routes(mapped_families: frozenset[str]) -> list[str]:
    return _report_issues(
        sorted(group for group in _FAMILY_SET_TO_RULE
               if group not in mapped_families),
        "[FamilyMapValidator] 组名 '%s' 声明了组级路由"
        "（_FAMILY_SET_TO_RULE）但未进 family_to_rules，组名 finding "
        "将降级默认规则",
        "组名路由断裂")
def _report_undeclared_groups() -> list[str]:
    return _report_issues(
        sorted(group for group in RULE_FAMILY_SETS
               if group not in _FAMILY_SET_TO_RULE),
        "[FamilyMapValidator] 组 '%s' 在 RULE_FAMILY_SETS 中但缺组级"
        "路由声明（_FAMILY_SET_TO_RULE），其组员 finding 绕过层级1",
        "组未声明组级路由")
def _report_route_overrides() -> list[str]:
    return _report_issues(
        sorted(
            f"{key}:{_FAMILY_SET_TO_RULE[key]}→{rule}"
            for overrides in (_FAMILY_RULE_OVERRIDES, _EXTRA_FAMILY_RULES)
            for key, rule in overrides.items()
            if key in _FAMILY_SET_TO_RULE
            and _FAMILY_SET_TO_RULE[key] != rule),
        "[FamilyMapValidator] 组级路由 '%s' 被覆盖表静默改写",
        "组级路由被覆盖表改写")
def validate_family_to_rules_consistency() -> list[str]:
    issues: list[str] = []
    try:
        mapped_families = frozenset(AUTO_FAMILY_TO_RULES)
        issues.extend(_report_unmapped_families(mapped_families))
        issues.extend(_report_broken_group_routes(mapped_families))
        issues.extend(_report_undeclared_groups())
        issues.extend(_report_route_overrides())
        if not issues:
            logger.info("[FamilyMapValidator] family_to_rules 一致性校验通过")
    except Exception as _e:  # noqa: BLE001
        _issue = f"校验异常: {type(_e).__name__}: {_e}"
        logger.warning("[FamilyMapValidator] %s", _issue)
        issues.append(_issue)
    return issues
def _family_semantic_violation(rule_id: str, family: str) -> bool:
    prefix = rule_id.split("-", 1)[0].split("_", 1)[0]
    allowed = _RULE_PREFIX_ALLOWED_SETS.get(prefix)
    return bool(allowed) and family not in allowed and rule_id not in allowed
def validate_family_semantics() -> list[str]:
    bad: list[str] = []
    try:
        for rid, fam in RULE_FAMILY_MAP.items():
            if _family_semantic_violation(rid, fam):
                bad.append(f"{rid}->{fam}")
        if bad:
            _report_issues(sorted(bad),
                           "[FamilyMapValidator] 语义校验: %s 未落允许族组",
                           "语义未落允许族组")
        else:
            logger.info("[FamilyMapValidator] 映射语义校验通过")
    except Exception as _e:  # noqa: BLE001
        _issue = f"语义校验异常: {type(_e).__name__}: {_e}"
        logger.warning("[FamilyMapValidator] %s", _issue)
        bad.append(_issue)
    return bad
validate_family_to_rules_consistency()
validate_family_semantics()
_META_SOURCE_EXEMPT_RULES = frozenset({"规则14", "规则15", "规则16", "规则31"})
_PHASE_SIGNAL_RULES = frozenset({"规则37", "规则38", "规则39", "规则40", "规则41"})
def default_meta_rule(source_count: int) -> str:
    try:
        _count = int(source_count)
    except (TypeError, ValueError, OverflowError) as _swallow_e:
        log_swallowed(
            __name__, _swallow_e,
            context=f'default_meta_rule:{type(_swallow_e).__name__}')
        _count = 1
    return "规则14" if _count >= 2 else "规则15"
def _check_fn_context_params(check_fn):
    try:
        params = inspect.signature(check_fn).parameters
    except (TypeError, ValueError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'_check_fn_context_params:{type(_e).__name__}')
        return frozenset()
    return frozenset(
        name for name in ("independent_results", "all_findings")
        if name in params
    )
_cached_check_fn_context_params = cache(_check_fn_context_params)
def dispatch_rule_check(cv2, check_fn, sources, entry):
    try:
        context_params = _cached_check_fn_context_params(check_fn)
    except TypeError as _e:
        log_swallowed(__name__, _e, context='dispatch_rule_check:TypeError')
        context_params = _check_fn_context_params(check_fn)
    if not context_params:
        return call_with_timeout(check_fn, (sources, entry), {})
    extra = {}
    if "independent_results" in context_params:
        extra["independent_results"] = cv2.independent_results
    if "all_findings" in context_params:
        extra["all_findings"] = cv2.all_findings
    return call_with_timeout(check_fn, (sources, entry), extra)
def _candidate_rule_applicable(cand_rule: str, entry_sources: set) -> bool:
    if cand_rule in _META_SOURCE_EXEMPT_RULES:
        return True
    _cand_meta = get_rule_metadata(cand_rule)
    _cand_methods = set(_cand_meta.get("methods", []))
    return not _cand_methods or bool(_cand_methods & entry_sources)
def run_candidate_checks(cv2, sources, entry,
                          first_round_results: dict,
                          all_matched: set) -> None:
    _entry_sources = set(sources)
    for _cand_rule, _cand_fn in RULE_CHECK_FN_MAP.items():
        if not _candidate_rule_applicable(_cand_rule, _entry_sources):
            continue
        try:
            _cand_ok = dispatch_rule_check(cv2, _cand_fn, sources, entry)
            first_round_results[_cand_rule] = _cand_ok
            if _cand_ok:
                all_matched.add(_cand_rule)
        except Exception as _ie:  # noqa: BLE001
            logger.warning(MSG_XV_VALIDATORS_IMPORT_FAIL, _ie)
def resolve_exclusion_and_reselect(rule_id: str, locator: str,
                                   first_round_results: dict,
                                   all_matched: set) -> str:
    _excluded = check_rule_exclusion(rule_id, all_matched)
    if _excluded:
        _pa = get_rule_metadata(rule_id).get("priority", 50)
        _pb = get_rule_metadata(_excluded).get("priority", 50)
        if _pa <= _pb:
            logger.debug("[Rules] 互斥: %s(优先级%d) 胜过 %s(优先级%d), locator=%s",
                         rule_id, _pa, _excluded, _pb, locator)
        else:
            logger.debug("[Rules] 互斥: %s 被优先级更高的 %s 抑制, locator=%s",
                         rule_id, _excluded, locator)
            rule_id = _excluded
    if first_round_results.get(rule_id) is not True and all_matched:
        rule_id = _reselect_final_rule(
            rule_id, first_round_results, all_matched, locator)
    return rule_id
def _reselect_final_rule(rule_id: str, _first_round_results: dict,
                          _all_matched: set, locator: str) -> str:
    _cands = []
    for _r in _all_matched:
        try:
            _priority = _reselect_priority(_r, _first_round_results)
        except Exception as _re:  # noqa: BLE001
            logger.debug(
                "[Rules] 候选规则 %s 重选检查异常: %s", _r, _re)
            continue
        if _priority is not None:
            _cands.append((_r, _priority))
    if _cands:
        _cands.sort(key=lambda x: (x[1], x[0]))
        _new_rule = _cands[0][0]
        if _new_rule != rule_id:
            logger.debug(
                "[Rules] 初始规则 %s check 未通过，重选匹配规则 %s (locator=%s)",
                rule_id, _new_rule, locator)
            return _new_rule
    return rule_id
def _reselect_priority(rule: str, first_round_results: dict) -> int | None:
    if rule not in RULE_CHECK_FN_MAP:
        return None
    if rule in _PHASE_SIGNAL_RULES:
        return None
    if first_round_results.get(rule) is not True:
        return None
    if get_rule_semantic(rule) == "suppress":
        return None
    return get_rule_metadata(rule).get("priority", 50)
_EVIDENCE_BEARING_RULES = frozenset({"规则5", "规则8", "规则18", "规则20"})
def apply_confidence_adjustments(base_conf, rule_id, _all_matched, locator, _log_delta):
    base_conf = float(base_conf) if is_real_number(base_conf) else 0.0
    base_conf = max(0.0, min(1.0, base_conf))
    if not isinstance(_log_delta, dict):
        _log_delta = {}
    _rule_weight = get_rule_weight(rule_id)
    if not is_real_number(_rule_weight):
        _rule_weight = 1.0
    if not math.isclose(_rule_weight, 1.0):
        _original_base = base_conf
        base_conf = max(0.0, min(1.0, base_conf * _rule_weight))
        _log_delta.setdefault("rule_weight_applied", []).append({
            "locator": locator,
            "rule_id": rule_id,
            "weight": _rule_weight,
            "original_base": round(_original_base, 3),
            "adjusted_base": round(base_conf, 3),
        })
    if not isinstance(_all_matched, (set, frozenset, list, tuple)):
        _all_matched = set()
    _secondary_rules = sorted(set(_all_matched) - {rule_id, "规则14", "规则15"})
    _secondary_rules = [r for r in _secondary_rules if get_rule_semantic(r) != "suppress"]
    _multi_rule_boost = 0.0
    if _secondary_rules:
        _boost_eligible = rule_id in _EVIDENCE_BEARING_RULES
        if _boost_eligible:
            _multi_rule_boost = min(len(_secondary_rules) * 0.03, 0.09)
            base_conf = max(0.0, min(1.0, base_conf + _multi_rule_boost))
        _log_delta.setdefault("multi_rule_confirmations", []).append({
            "locator": locator,
            "primary_rule": rule_id,
            "secondary_rules": _secondary_rules,
            "boost": round(_multi_rule_boost, 3),
            "boost_applied": _boost_eligible,
        })
    return base_conf, _secondary_rules, _multi_rule_boost
_RULE_STATS_SKELETON: dict = {
    "rule_id": "", "description": "",
    "triggered": False, "confirmed": 0, "suppressed": 0,
    "investigated": 0, "review": 0, "likely": 0, "uncertain": 0,
    "findings_count": 0,
}
def _rule_stats_template(rule_id: str, description: str = "",
                         overrides: dict | None = None) -> dict:
    entry = dict(_RULE_STATS_SKELETON)
    if isinstance(overrides, dict):
        entry.update(overrides)
    entry["rule_id"] = rule_id
    if description:
        entry["description"] = description
    return entry
def rebuild_rules_applied(validator) -> None:
    _prevalidate_applied = validator.rules_applied
    if not isinstance(_prevalidate_applied, dict):
        _prevalidate_applied = {}
    validator.rules_applied = {}
    for rule_id, desc in CV_RULES.items():
        _pre = _prevalidate_applied.get(rule_id)
        validator.rules_applied[rule_id] = _rule_stats_template(
            rule_id, description=desc,
            overrides=_pre if isinstance(_pre, dict) else None)
    for _pv_key, _pv_info in _prevalidate_applied.items():
        if (_pv_key not in validator.rules_applied
                and isinstance(_pv_info, dict)):
            validator.rules_applied[_pv_key] = _rule_stats_template(
                _pv_key, overrides=_pv_info)

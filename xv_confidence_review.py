from __future__ import annotations

import json
import logging
import os
import re
import threading
import time
import uuid
from collections import Counter, defaultdict
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor, as_completed
from concurrent.futures import TimeoutError as _CFTimeoutError
from dataclasses import dataclass
from functools import wraps
from types import SimpleNamespace
from typing import Any, ClassVar, NamedTuple

from jwsgj.ai_review_queue import (
    reconcile_cv_uncertain_after_llm,
    run_uncertain_enqueue_channel,
)
from jwsgj.diag_detectors_registry import apply_detector_liveness_gate
from jwsgj.diag_shared_source_core import read_source_text
from jwsgj.diag_taint_tracker import (
    _looks_security_finding,
    validate_security_findings,
)
from jwsgj.diag_testing_mutation import (
    MutationVerifier,
    annotate_findings_with_mutation,
)
from jwsgj.diag_types_normalize import (
    finding_file_key,
    finding_file_path,
    int_or,
    is_real_number,
    normalize_severity_rank,
    normalize_sources,
    parse_locator_file,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    CONCLUSION_V2_MAP,
    CONF_BOOST_SMALL,
    CV_RULES,
    FIELD_FINDINGS_SUPPRESSED,
    FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
    FIELD_RULES_TRIGGERED,
    FIELD_TOTAL_INPUT_FINDINGS,
    MS_PER_SECOND,
)
from jwsgj.fp_rules_judge import finding_line_no
from jwsgj.log_config import (
    clear_trace_id,
    log_swallowed,
    perf_trace,
    set_trace_id,
    timed_log,
)
from jwsgj.memory_feedback_core import apply_cv_memory_enhancements
from jwsgj.testsuite_eval import (
    assess_cv_maturity,
    run_stage2b_test_bridge,
)
from jwsgj.xv_arbiter import (
    apply_annotation_adjustments,
    handle_contradictions,
    post_match_suppression,
)
from jwsgj.xv_conclusion_engine import (
    AUTO_STRENGTH_THRESHOLD as DEFAULT_AUTO_STRENGTH_THRESHOLD,
)
from jwsgj.xv_conclusion_engine import (
    PlDecision,
    assemble_xv_result,
    build_skipped_placeholder,
    call_rule_check_fn,
    determine_matched_conclusion,
    handle_unmatched_rule,
    pl_independent_sources,
    pl_rule4_safety_valve,
    pl_select_rule,
    prepare_locator_entry,
)
from jwsgj.xv_context_derivation import (
    COVERAGE_CRITICAL,
    CrossValidationEnricher,
    analyze_degradation_impact,
    available_evidence_methods,
    build_context_from_intermediates,
    check_coverage,
    derive_skill_dir_and_graph,
    inject_quadrant_findings,
    normalized_independent_results,
    verify_full_participation,
)
from jwsgj.xv_context_history import (
    annotate_findings,
    apply_round_human_decisions,
    build_oscillation_degraded_report,
    build_oscillation_report_for_cv,
    diff_findings_with_baseline,
    open_round_inputs,
)
from jwsgj.xv_cv_report_assemble import (
    attach_cv_report_summary,
    build_executive_summary,
    summarize_phase_health,
)
from jwsgj.xv_evidence_channels import (
    BusinessFlowValidator,
    CounterEvidenceAnalyzer,
    FalsificationAnalyzer,
    RefDepthAnalyzer,
    TestTriageVerifier,
    VCSRecencyAnalyzer,
    annotate_findings_with_bizflow,
    annotate_findings_with_counter_evidence,
    annotate_findings_with_falsification,
    annotate_findings_with_ref_depth,
    annotate_findings_with_test_triage,
    annotate_findings_with_vcs,
)
from jwsgj.xv_evidence_crosscheck import (
    EnsembleConsensusAnalyzer,
    annotate_findings_with_drift,
    annotate_findings_with_ensemble,
    attach_negatives_audit,
    build_drift_report,
    build_evidence_chain_audit,
    cross_locator_consistency_check,
    run_negatives_channels,
)
from jwsgj.xv_evidence_strength import (
    ANNOTATION_PHASE_MODULES,
    PHASE_MODULE_CRITICALITY,
    apply_annotation_completeness,
    count_independent_sources,
    set_available_methods,
    set_evidence_learning_dir,
    update_rule_weights,
)
from jwsgj.xv_findings_core import (
    _confirmed_method_counts,
    aggregate_by_function,
    apply_rule_stats,
    build_data_lineage,
    build_findings_index,
    collect_all_findings,
    collected_sources_before_gate,
    compute_p0p1_protection_log,
    compute_statistics,
    fuse_regression_into_xv,
    inner_finding_count,
    source_method_counts,
)
from jwsgj.xv_fp_filter_stages import (
    filter_false_positives,
    post_annotation_fp_filter,
    reinject_deferred_as_shadow,
    rescue_deferred_findings,
)
from jwsgj.xv_rule_checks import (
    PHASE_MODULE_DEPS,
    RULE_CHECK_FN_MAP,
    apply_confidence_adjustments,
    is_module_available,
    rebuild_rules_applied,
    set_phase_module_status,
)
from jwsgj.xv_threshold_learning import (
    apply_cv_threshold_adjustments,
    apply_feedback_thresholds,
    build_fp_tracker_state,
    calibrate_and_persist_fp_tracker,
    feed_channel_signals_to_fp_tracker,
    load_feedback_adjustments,
    load_fp_tracker_persisted,
    resolve_threshold,
    set_threshold_learning_dir,
)

__all__ = [
    'CrossValidatorV2',
    'HumanApplication',
    'LLMCrossValidator',
    'apply_rules',
    'apply_stage2b_enhancers',
    'build_cv_stage_context',
    'build_empty_degradation_report',
    'build_insufficient_coverage_report',
    'build_result_core_sections',
    'build_result_governance_sections',
    'build_result_observability_sections',
    'build_result_summary_sections',
    'build_rule_coverage',
    'coverage_gate_report',
    'elapsed_ms',
    'empty_degradation_report',
    'empty_rule_coverage',
    'ensure_confirmed_channel',
    'filter_false_positives_standalone',
    'materialize_confirmed_channel',
    'normalize_conclusion_v2',
    'pre_validate',
    'prepare_rule_phase',
    'process_locator',
    'refine_cv_findings_with_llm',
    'run_post_rule_channels',
    'run_stage2b_bidirectional_taint',
    'run_stage2b_execute',
    'summarize_cv_result',
    'validate_stage_statistics',
]
logger = logging.getLogger(__name__)
def _zeroed_stat_fields() -> dict:
    return {
        "findings_validated": 0,
        "confirmed": 0, "suppressed": 0,
        "investigated": 0, "review": 0,
        "likely": 0, "uncertain": 0,
        "contradictions": 0,
        "findings_confirmed": 0, FIELD_FINDINGS_SUPPRESSED: 0,
        "findings_investigated": 0, "findings_review": 0,
        "findings_likely": 0, "findings_uncertain": 0,
        "rules_applied_count": 0,
        "rules_detail": [],
    }
def _dict_copy(value) -> dict:
    return dict(value) if isinstance(value, dict) else {}
def _effective_thresholds(cv) -> dict:
    return {
        "auto_confirm": cv.AUTO_CONFIRM_THRESHOLD,
        "auto_strength": cv.AUTO_STRENGTH_THRESHOLD,
        "auto_min_adjusted": cv.AUTO_MIN_ADJUSTED,
    }
def _feedback_adjustment_sections(cv) -> dict:
    return {
        FIELD_METHOD_CONFIDENCE_MULTIPLIERS: _dict_copy(
            getattr(cv, "_method_confidence_multipliers", {})),
        "cv_confidence_thresholds_applied": _dict_copy(
            getattr(cv, "_cv_confidence_thresholds", {})),
        "effective_thresholds": _effective_thresholds(cv),
        "adjustments_loaded": bool(getattr(cv, "_feedback_adjustments", {})),
    }
def _drift_report_disabled(error: str = "") -> dict:
    report = {"enabled": False}
    if error:
        report["error"] = error
    return report
def _empty_uncertain_enqueue_report() -> dict:
    return {"attempted": False, "enqueued": 0, "failed": False,
            "error": "", "fp_suppressed_forced": 0,
            "fp_suppressed_skipped_human_rejected": 0,
            "fp_suppressed_skipped_history_rejected": 0}
def _human_confirmation_stats(applied_confirmed: int,
                             applied_suppressed: int,
                             store: Any) -> dict:
    return {"applied_confirmed": applied_confirmed,
            "applied_suppressed": applied_suppressed,
            "store_stats": _safe_human_store_stats(store)}
def _rules_applied_view(validator) -> dict:
    applied = getattr(validator, "rules_applied", None)
    return applied if isinstance(applied, dict) else {}
def _triggered_rule_records(validator) -> list[dict]:
    return [r for r in _rules_applied_view(validator).values()
            if isinstance(r, dict) and r.get("triggered")
            and isinstance(r.get("rule_id"), str) and r.get("rule_id")]
def _wired_check_fn_rules() -> set[str]:
    return set(CV_RULES) & (set(RULE_CHECK_FN_MAP) | _PHASE_DYNAMIC_CV_RULES)
def build_rule_coverage(validator) -> dict:
    _exec_log = getattr(validator, '_rule_execution_log', None)
    if not isinstance(_exec_log, dict):
        _exec_log = {}
    _triggered_records = _triggered_rule_records(validator)
    _triggered_ids = {r.get("rule_id") for r in _triggered_records}
    _defined_rules = set(CV_RULES)
    _wired_rules = _wired_check_fn_rules()
    _executed = _exec_log.get('rules_executed', [])
    if not isinstance(_executed, list):
        _executed = []
    return {
        "total_rules_defined": len(CV_RULES),
        "rules_with_check_fn": len(_wired_rules),
        "rules_executed": _executed,
        "rules_without_check_fn": sorted(_defined_rules - _wired_rules),
        FIELD_RULES_TRIGGERED: [r.get("rule_id") for r in _triggered_records],
        "rules_never_triggered": sorted(_defined_rules - _triggered_ids),
        "trigger_rate": round(
            len(_defined_rules & _triggered_ids) / max(len(CV_RULES), 1), 4),
    }
def empty_rule_coverage() -> dict:
    _wired = _wired_check_fn_rules()
    return {
        "total_rules_defined": len(CV_RULES),
        "rules_with_check_fn": len(_wired),
        "rules_executed": [],
        "rules_without_check_fn": sorted(set(CV_RULES) - _wired),
        FIELD_RULES_TRIGGERED: [],
        "rules_never_triggered": sorted(CV_RULES),
        "trigger_rate": 0.0,
    }
def _empty_report_shell(cv, coverage_report: dict,
                        degraded_reason: str) -> dict:
    deg = analyze_degradation_impact(cv)
    return {
        "timestamp": timestamp_ms(),
        FIELD_TOTAL_INPUT_FINDINGS: 0,
        "cross_validated": 0,
        "solo_findings": 0,
        **_zeroed_stat_fields(),
        "findings_index": [],
        "context_summary": {},
        "participation": verify_full_participation(cv),
        "degradation_impact": deg,
        "coverage_report": coverage_report,
        "human_confirmation_stats": _human_confirmation_stats(0, 0, None),
        "feedback_adjustments": _feedback_adjustment_sections(cv),
        "fp_filter_log": [],
        "p0p1_protection_log": [],
        "p0p1_protection_count": 0,
        "phase_errors": [],
        "executive_summary": build_executive_summary(
            0, 0, 0, 0, 0, 0, 0, degraded_reason=degraded_reason),
        "rule_coverage": empty_rule_coverage(),
        "rule_execution_log": {},
        "function_level_summary": [],
    }
def _coverage_ratio(value) -> float:
    return float(value) if is_real_number(value) else 0.0
def _missing_methods(value) -> list:
    if not isinstance(value, (list, tuple, set, frozenset)):
        return []
    return [item for item in value if isinstance(item, str) and item]
def build_insufficient_coverage_report(cv, coverage: dict) -> dict:
    _coverage = coverage if isinstance(coverage, dict) else {}
    _rate = _coverage_ratio(_coverage.get("coverage_rate", 0.0))
    _placeholder = _coverage.get("placeholder_count", 0)
    _placeholder = (_placeholder
                    if isinstance(_placeholder, int)
                    and not isinstance(_placeholder, bool) else 0)
    _missing = _missing_methods(_coverage.get("missing_methods"))
    _skipped = _missing_methods(_coverage.get("skipped_methods"))
    _degraded = _missing_methods(_coverage.get("degraded_methods"))
    return {  # jwsgj:suppress RT-01
        "total_raw_findings": len(cv.all_findings),
        "coverage_gate_triggered": True,
        "collected_before_gate": len(cv.all_findings),
        "collected_sources_before_gate": collected_sources_before_gate(cv),
        **_empty_report_shell(cv, _coverage, "insufficient_coverage"),
        "status": "insufficient_coverage",
        "reason": "coverage_insufficient",
        "missing_methods": _missing,
        "skipped_methods": _skipped,
        "degraded_methods": _degraded,
        "message": (f"Coverage {_rate:.1%} below "
                    f"{COVERAGE_CRITICAL:.0%} threshold: "
                    f"{_placeholder} methods not participating "
                    f"(missing={_missing}, skipped={_skipped}, "
                    f"degraded={_degraded})"),
        "phase_health": {"overall_status": "critical",
                         "summary": "insufficient coverage"},
    }
def build_empty_degradation_report(cv) -> dict:
    return {  # jwsgj:suppress RT-01
        "total_raw_findings": 0,
        **_empty_report_shell(
            cv, getattr(cv, "_coverage_report", {}), "empty_degradation"),
        "phase_health": {"overall_status": "degraded"},
        "status": "empty_degradation",
        "message": "所有方法均无findings输出，CV引擎返回降级报告",
        "_empty_report": True,
    }
def build_result_core_sections(validator, ctx: dict) -> dict:
    return {
        "timestamp": timestamp_ms(),
        FIELD_TOTAL_INPUT_FINDINGS: ctx['total_locators'],
        "cross_validated": ctx['validated_locators'],
        "solo_findings": ctx['total_locators'] - ctx['validated_locators'],
        "total_raw_findings": len(validator.all_findings),
        "findings_validated": ctx['xv_finding_count'],
        "confirmed": ctx['confirmed'], "suppressed": ctx['suppressed'],
        "investigated": ctx['investigated'], "review": ctx['review_c'],
        "likely": ctx['likely_c'], "uncertain": ctx['uncertain_c'],
        "contradictions": ctx['contradiction_count'],
        "contradiction_findings": ctx['contradictions'],
        "findings_confirmed": ctx['findings_confirmed'],
        FIELD_FINDINGS_SUPPRESSED: ctx[FIELD_FINDINGS_SUPPRESSED],
        "findings_investigated": ctx['findings_investigated'],
        "findings_review": ctx['findings_review'],
        "findings_likely": ctx['findings_likely'],
        "findings_uncertain": ctx['findings_uncertain'],
    }
def build_result_governance_sections(validator, ctx: dict) -> dict:
    _human_stats = _human_confirmation_stats(
        ctx['human_applied_confirmed'], ctx['human_applied_suppressed'],
        ctx['human_store'])
    _triggered = _triggered_rule_records(validator)
    return {
        "rules_applied_count": len(_triggered),
        "rules_detail": list(_rules_applied_view(validator).values()),
        "findings_index": ctx['xv_findings'],
        "self_audit_applied": getattr(validator, '_self_audit_applied', False),
        "context_summary": getattr(validator, '_context_summary', {}),
        "participation": ctx['participation'],
        "degradation_impact": ctx['degradation_impact'],
        "coverage_report": getattr(validator, "_coverage_report", {}),
        "human_confirmation_stats": _human_stats,
        "feedback_adjustments": _feedback_adjustment_sections(validator),
    }
def build_result_observability_sections(validator, ctx: dict) -> dict:
    _p0p1_log = ctx['p0p1_protection_log']
    return {
        "oscillation_report": getattr(validator, '_oscillation_report', {}),
        "uncertain_enqueue_report": getattr(
            validator, '_uncertain_enqueue_report',
            _empty_uncertain_enqueue_report()),
        "detector_liveness_report": getattr(validator, '_liveness_report', {}),
        "fp_filter_log": getattr(validator, '_fp_filter_log', []),
        "p0p1_protection_log": _p0p1_log,
        "p0p1_protection_count": len(_p0p1_log),
        "rule_execution_log": getattr(validator, '_rule_execution_log', {}),
    }
def build_result_summary_sections(validator, ctx: dict) -> dict:
    phase_health = summarize_phase_health(
        getattr(validator, '_phase_errors', []))
    return {
        "function_level_summary": aggregate_by_function(ctx['xv_findings']),
        "executive_summary": build_executive_summary(
            ctx['total_locators'], ctx['confirmed'], ctx['likely_c'],
            ctx['uncertain_c'], ctx['suppressed'], ctx['contradiction_count'],
            ctx['xv_finding_count'], phase_health=phase_health),
        "phase_errors": getattr(validator, '_phase_errors', []),
        "phase_health": phase_health,
        "rule_coverage": build_rule_coverage(validator),
    }
def build_cv_stage_context(stats_ctx, xv_findings,
                            human_applied_confirmed, human_applied_suppressed,
                            human_store) -> dict:
    return {
        'xv_findings': xv_findings,
        'contradictions': stats_ctx.contradictions,
        'contradiction_count': stats_ctx.contradiction_count,
        'total_locators': stats_ctx.total_locators,
        'validated_locators': stats_ctx.validated_locators,
        'xv_finding_count': stats_ctx.xv_finding_count,
        'confirmed': stats_ctx.confirmed, 'likely_c': stats_ctx.likely_c,
        'uncertain_c': stats_ctx.uncertain_c, 'suppressed': stats_ctx.suppressed,
        'investigated': stats_ctx.investigated, 'review_c': stats_ctx.review_c,
        'findings_confirmed': stats_ctx.findings_confirmed,
        FIELD_FINDINGS_SUPPRESSED: stats_ctx.findings_suppressed,
        'findings_likely': stats_ctx.findings_likely,
        'findings_uncertain': stats_ctx.findings_uncertain,
        'findings_investigated': stats_ctx.findings_investigated,
        'findings_review': stats_ctx.findings_review,
        'participation': stats_ctx.participation,
        'degradation_impact': stats_ctx.degradation_impact,
        'human_applied_confirmed': human_applied_confirmed,
        'human_applied_suppressed': human_applied_suppressed,
        'human_store': human_store,
        'p0p1_protection_log': stats_ctx.p0p1_protection_log,
    }
@dataclass(frozen=True)
class HumanApplication:
    store: Any
    confirmed: int
    suppressed: int
def _safe_human_store_stats(_human_store) -> dict:
    if _human_store is None:
        return {}
    try:
        _stats = _human_store.stats()
        return _stats if isinstance(_stats, dict) else {}
    except Exception as _e:  # noqa: BLE001
        logger.warning("[CV] human store stats 获取失败（降级空 dict）: %s", _e)
        return {}
def elapsed_ms(started_at: float) -> int:
    return int((time.perf_counter() - started_at) * MS_PER_SECOND)
def _conclusion_text(value) -> str:
    return value.strip().lower() if isinstance(value, str) else ""
def _conclusion_v2_of(entry: dict) -> str:
    conclusion = entry.get("conclusion")
    if not isinstance(conclusion, str):
        return "uncertain"
    return CONCLUSION_V2_MAP.get(_conclusion_text(conclusion), "uncertain")
def normalize_conclusion_v2(xv_findings: list) -> None:
    for f in xv_findings:
        if not isinstance(f, dict):
            continue
        f["conclusion_v2"] = _conclusion_v2_of(f)
def coverage_gate_report(validator, started_at: float) -> dict | None:
    validator._coverage_report = check_coverage(validator)
    if not validator._coverage_report.get("critical"):
        return None
    logger.error("[CV] Coverage critically insufficient, returning insufficient_coverage report")
    try:
        validator.all_findings = collect_all_findings(validator)
        logger.info("[CV] Coverage critical, but %d raw findings still collected for traceability",
                    len(validator.all_findings))
    except Exception as _collect_exc:
        logger.warning("[CV] Coverage critical fallback collection failed: %s", _collect_exc, exc_info=True)
        validator.all_findings = []
    _degraded = build_insufficient_coverage_report(validator, validator._coverage_report)
    _degraded["duration_ms"] = elapsed_ms(started_at)
    return _degraded
def empty_degradation_report(validator, started_at: float) -> dict:
    logger.warning("[CV] 所有方法均无 findings，跳过规则引擎，直接返回降级报告")
    _degraded = build_empty_degradation_report(validator)
    _degraded["duration_ms"] = elapsed_ms(started_at)
    return _degraded
def _unpack_stats(_stats: dict) -> tuple:
    return (
        _stats["confirmed"], _stats["likely_c"], _stats["uncertain_c"],
        _stats["suppressed"], _stats["investigated"], _stats["review_c"],
        _stats["findings_confirmed"], _stats[FIELD_FINDINGS_SUPPRESSED],
        _stats["findings_likely"], _stats["findings_uncertain"],
        _stats["findings_investigated"], _stats["findings_review"],
    )
class StageStatistics(NamedTuple):
    confirmed: int
    likely_c: int
    uncertain_c: int
    suppressed: int
    investigated: int
    review_c: int
    findings_confirmed: int
    findings_suppressed: int
    findings_likely: int
    findings_uncertain: int
    findings_investigated: int
    findings_review: int
    xv_finding_count: int
    contradictions: list
    contradiction_count: int
    participation: dict
    degradation_impact: dict
    total_locators: int
    validated_locators: int
    p0p1_protection_log: list
def _non_contradiction_findings(xv_findings: list) -> list:
    return [f for f in xv_findings
            if isinstance(f, dict)
            and not str(f.get("locator", "")).startswith("CONTRADICTION:")]
_MIN_CROSS_VALIDATION_SOURCES = 2
def _index_source_count(entry: object) -> int:
    if not isinstance(entry, dict):
        return 0
    sources = entry.get("sources")
    if isinstance(sources, (list, tuple, set, frozenset)):
        valid_sources = [
            source for source in sources
            if isinstance(source, str) and source.strip()
        ]
        if valid_sources:
            return count_independent_sources(valid_sources)
    return max(0, int_or(entry.get("source_count"), 0))
def _count_cross_validated_locators(findings_index: object) -> int:
    if isinstance(findings_index, dict):
        entries = findings_index.values()
    elif isinstance(findings_index, (list, tuple)):
        entries = findings_index
    else:
        return 0
    return sum(
        1 for entry in entries
        if _index_source_count(entry) >= _MIN_CROSS_VALIDATION_SOURCES)
def validate_stage_statistics(cv, xv_findings: list,
                               findings_index: dict) -> StageStatistics:
    non_contradiction = _non_contradiction_findings(xv_findings)
    counts = _unpack_stats(compute_statistics(non_contradiction))
    apply_rule_stats(cv, xv_findings)
    contradictions, contradiction_count = handle_contradictions(cv, xv_findings)
    if contradiction_count > 0:
        for f in contradictions:
            if isinstance(f, dict):
                f["conclusion_v2"] = _conclusion_v2_of(f)
        counts = _unpack_stats(compute_statistics(xv_findings))
        logger.info("[Stats] 含矛盾重计算: confirmed=%d, likely=%d, "
                    "uncertain=%d, suppressed=%d, contradictions=%d",
                    counts[0], counts[1], counts[2], counts[3],
                    contradiction_count)
    validated_locators = _count_cross_validated_locators(findings_index)
    logger.info("[Stats] 交叉验证定位点: %d/%d (>=%d 独立来源)",
                validated_locators, len(findings_index),
                _MIN_CROSS_VALIDATION_SOURCES)
    return StageStatistics(
        *counts,
        sum(inner_finding_count(f) or 1 for f in xv_findings),
        contradictions,
        contradiction_count,
        verify_full_participation(cv),
        analyze_degradation_impact(cv),
        len(findings_index),
        validated_locators,
        compute_p0p1_protection_log(xv_findings),
    )
def _bump_log_counter(log_delta: dict, key: str) -> None:
    log_delta[key] = log_delta.get(key, 0) + 1
_MULTI_SOURCE_BOOST_CAP = CONF_BOOST_SMALL * 4
def _pl_decide_rule_and_conclusion(
    cv2, locator: str, entry: dict, sources: list,
    base_conf: float, strength: float,
    _log_delta: dict, _exec_log_lock,
) -> PlDecision:
    source_count = len(pl_independent_sources(entry, sources))
    _degraded_info = None
    selection = pl_select_rule(cv2, entry, sources, locator)
    rule_id = selection.rule_id
    _selection_trace = selection.selection_trace
    _first_round_results = selection.first_round_results
    _all_matched = selection.all_matched
    _log_delta["rules_executed"].add(rule_id)
    rule_matched, check_fn = call_rule_check_fn(
        cv2, rule_id, sources, entry, locator, _first_round_results,
        _exec_log_lock,
    )
    base_conf, _secondary_rules, _multi_rule_boost = apply_confidence_adjustments(
        base_conf, rule_id, _all_matched, locator, _log_delta,
    )
    boost = min(source_count * CONF_BOOST_SMALL, _MULTI_SOURCE_BOOST_CAP)
    if rule_matched is True:
        _bump_log_counter(_log_delta, "rule_matched")
        conclusion, _log_delta = determine_matched_conclusion(
            cv2, rule_id, base_conf, strength, source_count, entry, locator, _log_delta,
        )
    else:
        _bump_log_counter(_log_delta, "rule_not_matched")
        conclusion, rule_id, boost, _degraded_info, _log_delta = handle_unmatched_rule(
            cv2, rule_id, sources, entry, locator, base_conf, strength,
            boost, _log_delta,
        )
    base_conf, strength, conclusion, adj_log = apply_annotation_adjustments(
        entry, base_conf, strength, conclusion, rule_id
    )
    return PlDecision(
        rule_id=rule_id,
        selection_trace=_selection_trace,
        first_round_results=_first_round_results,
        all_matched=_all_matched,
        rule_matched=rule_matched,
        check_fn=check_fn,
        base_conf=base_conf,
        strength=strength,
        secondary_rules=_secondary_rules,
        multi_rule_boost=_multi_rule_boost,
        boost=boost,
        conclusion=conclusion,
        adj_log=adj_log,
        degraded_info=_degraded_info,
        log_delta=_log_delta,
    )
def process_locator(
    cv2, locator: str, entry: dict,
    _exec_log_lock: threading.Lock | None = None,
) -> tuple:
    _log_delta = {"rules_executed": set()}
    pf = prepare_locator_entry(locator, entry)
    if isinstance(pf, tuple):
        result, log_delta = pf
        log_delta["skipped_placeholders"] = 1
        return result, log_delta
    sources = pf["sources"]
    dec = _pl_decide_rule_and_conclusion(
        cv2, locator, entry, sources, pf["base_conf"], pf["strength"],
        _log_delta, _exec_log_lock,
    )
    rule4 = pl_rule4_safety_valve(cv2, entry, sources, dec)
    xv_result = assemble_xv_result(cv2, locator, entry, sources, dec, rule4)
    if xv_result is None:
        # 退休规则不产出 finding：仍回传执行日志，保持规则命中统计完整。
        return None, dec.log_delta
    return xv_result, dec.log_delta
_PARALLEL_THRESHOLD = 50
_DEFAULT_WAIT_TIMEOUT_SEC = 60
def _cpu_bounded_workers(limit: int) -> int:
    return max(1, min(limit, os.cpu_count() or 1))
_MAX_WORKERS = _cpu_bounded_workers(4)
def _merge_exec_log(cv2, log_delta: dict) -> None:
    exec_log = cv2._rule_execution_log
    for key, value in log_delta.items():
        if key == "rules_executed":
            exec_log["rules_executed"].update(value)
        elif isinstance(value, int) and not isinstance(value, bool):
            exec_log[key] = exec_log.get(key, 0) + value
        elif isinstance(value, list):
            exec_log.setdefault(key, []).extend(value)
def apply_rules(cv2, findings_index: dict[str, dict]) -> list[dict]:
    cv2._rule_execution_log = {
        "total_locators": len(findings_index),
        "rule_matched": 0,
        "rule_not_matched": 0,
        "degraded_matched": 0,
        "generic_fallback": 0,
        "skipped_placeholders": 0,
        "rules_executed": set(),
    }
    use_parallel = (
        len(findings_index) > _PARALLEL_THRESHOLD
        and getattr(cv2, '_parallel_rules', True)
    )
    if use_parallel:
        xv_results = _ParallelRuleBatch(cv2, findings_index).run()
    else:
        xv_results = _apply_rules_sequential(cv2, findings_index)
    cv2._rule_execution_log["rules_executed"] = sorted(cv2._rule_execution_log["rules_executed"])
    logger.info("[Rules] 应用规则: %d locators -> %d xv_results "
                "(matched=%d, degraded=%d, generic=%d, parallel=%s)",
                len(findings_index), len(xv_results),
                cv2._rule_execution_log["rule_matched"],
                cv2._rule_execution_log["degraded_matched"],
                cv2._rule_execution_log["generic_fallback"],
                use_parallel)
    update_rule_weights(xv_results)
    return xv_results
def _apply_rules_sequential(cv2, findings_index: dict[str, dict]) -> list[dict]:
    xv_results = []
    _seq_errors = 0
    for locator, entry in findings_index.items():
        try:
            result, log_delta = process_locator(cv2, locator, entry)
            _merge_exec_log(cv2, log_delta)
            if result is not None:
                xv_results.append(result)
        except Exception as e:
            _seq_errors += 1
            logger.warning("[Rules-Seq] locator %s 处理异常，降级为 uncertain 占位: %s", locator, e,
                          exc_info=True)
            xv_results.append(build_skipped_placeholder(locator, entry, f"seq_exception: {e}"))
            _merge_exec_log(cv2, {"skipped_placeholders": 1})
    if _seq_errors:
        logger.warning("[Rules-Seq] %d/%d locators 处理失败（降级为 uncertain）",
                      _seq_errors, len(findings_index))
    return xv_results
def _shutdown_executor(executor) -> None:
    _shutdown = getattr(executor, "shutdown", None)
    if not callable(_shutdown):
        return
    try:
        _shutdown(wait=False)
        return
    except TypeError:
        logger.debug("[Rules-Parallel] executor.shutdown 不接受 wait 参数，改无参调用")
    except Exception:
        logger.debug("[Rules-Parallel] executor shutdown 失败（忽略）",
                     exc_info=True)
        return
    try:
        _shutdown()
    except Exception:
        logger.debug("[Rules-Parallel] executor shutdown 失败（忽略）",
                     exc_info=True)
def _recover_batch_timeout(futures: dict, collected: set,
                           batch, rule_timeout: int) -> None:
    for future, locator in futures.items():
        if locator in collected:
            continue
        if future.done() and not future.cancelled():
            batch._collect(locator, future, 0,
                           "parallel_batch_timeout_recover", "结果恢复失败")
        else:
            future.cancel()
            batch._note_placeholder(
                locator, f"parallel_batch_timeout({rule_timeout}s)")
class _ParallelRuleBatch:
    def __init__(self, cv2, findings_index: dict[str, dict]):
        self.cv2 = cv2
        self.findings_index = findings_index
        self.exec_log_lock = threading.Lock()
        self.results: list[dict] = []
        self.results_lock = threading.Lock()
        self.timeout = max(_DEFAULT_WAIT_TIMEOUT_SEC, len(findings_index))
    def _worker(self, locator_entry_tuple):
        locator, entry = locator_entry_tuple
        result, log_delta = process_locator(
            self.cv2, locator, entry, _exec_log_lock=self.exec_log_lock)
        return locator, result, log_delta
    def _append_result(self, result: dict) -> None:
        with self.results_lock:
            self.results.append(result)
    def _note_placeholder(self, locator: str, reason: str) -> None:
        self._append_result(build_skipped_placeholder(
            locator, self.findings_index.get(locator, {}), reason))
        with self.exec_log_lock:
            _merge_exec_log(self.cv2, {"skipped_placeholders": 1})
    def _collect(self, locator, future, result_timeout: int,
                 fail_reason: str, fail_verb: str) -> None:
        try:
            _, result, log_delta = future.result(timeout=result_timeout)
            with self.exec_log_lock:
                _merge_exec_log(self.cv2, log_delta)
            if result is not None:
                self._append_result(result)
        except (TimeoutError, _CFTimeoutError) as _te:
            logger.warning("[Rules-Parallel] locator %s 处理超时，降级为 uncertain 占位: %s", locator, _te)
            self._note_placeholder(locator, f"parallel_timeout: {_te}")
        except Exception as e:  # noqa: BLE001
            logger.warning("[Rules-Parallel] locator %s %s，降级为 uncertain 占位: %s", locator, fail_verb, e)
            self._note_placeholder(locator, f"{fail_reason}: {e}")
    def _ordered_results(self) -> list[dict]:
        _positions = {
            locator: idx for idx, locator in enumerate(self.findings_index)}
        _fallback = len(_positions)
        return sorted(
            self.results,
            key=lambda _r: _positions.get(
                _r.get("locator", "") if isinstance(_r, dict) else "",
                _fallback),
        )
    def run(self) -> list[dict]:
        executor = ThreadPoolExecutor(max_workers=_MAX_WORKERS)
        try:
            futures = {
                executor.submit(self._worker, (locator, entry)): locator
                for locator, entry in self.findings_index.items()
            }
            _collected_locators: set = set()
            try:
                for future in as_completed(futures, timeout=self.timeout):
                    locator = futures[future]
                    self._collect(locator, future, _RESULT_WAIT_TIMEOUT,
                                  "parallel_exception", "处理失败")
                    _collected_locators.add(locator)
            except (TimeoutError, _CFTimeoutError):
                logger.warning("[Rules-Parallel] 批次整体超时(%ds)，剩余 locator 降级为 uncertain 占位",
                               self.timeout)
                _recover_batch_timeout(
                    futures, _collected_locators, self, self.timeout)
            for future in futures:
                if not future.done():
                    future.cancel()
        finally:
            _shutdown_executor(executor)
        return self._ordered_results()
class CrossValidatorV2:
    AUTO_CONFIRM_THRESHOLD = 0.72
    AUTO_STRENGTH_THRESHOLD = DEFAULT_AUTO_STRENGTH_THRESHOLD
    AUTO_MIN_ADJUSTED = 0.50
    FINDING_FIELD_ALIASES: ClassVar[dict[str, list[str]]] = {
        "rule_id":   ["rule_id", "type", "rule", "check_id", "id", "category", "code"],
        "file":      ["file", "path", "filepath", "module", "filename", "source_file", "rel_path"],
        "line":      ["line", "lineno", "line_number", "line_no", "ln", "start_line", "row"],
        "severity":  ["severity", "level", "priority", "impact"],
        "confidence": ["confidence", "certainty", "score", "reliability"],
        "message":   ["message", "description", "msg", "desc", "detail", "text", "reason"],
        "column":    ["column", "col", "column_no"],
        "end_line":  ["end_line", "end_lineno", "end_line_no"],
        "category":  ["category", "type", "group", "family"],
        "fix_suggestion": ["fix_suggestion", "suggestion", "fix", "fix_hint", "recommendation"],
        "test_name": ["test_name", "test", "test_id", "nodeid"],
        "metric_value": ["metric_value", "value", "score_value", "measurement"],
    }
    def __init__(self, auto_confirm_threshold: float | None = None,
                 auto_strength_threshold: float | None = None,
                 auto_min_adjusted: float | None = None):
        self.independent_results: dict[str, dict] = {}
        self.all_findings: list[dict] = []
        self.rules_applied: dict[str, dict] = {}
        self.AUTO_CONFIRM_THRESHOLD = resolve_threshold(
            auto_confirm_threshold, "JWSGJ_AUTO_CONFIRM_THRESHOLD",
            self.AUTO_CONFIRM_THRESHOLD)
        self.AUTO_STRENGTH_THRESHOLD = resolve_threshold(
            auto_strength_threshold, "JWSGJ_AUTO_STRENGTH_THRESHOLD",
            self.AUTO_STRENGTH_THRESHOLD)
        self.AUTO_MIN_ADJUSTED = resolve_threshold(
            auto_min_adjusted, "JWSGJ_AUTO_MIN_ADJUSTED",
            self.AUTO_MIN_ADJUSTED)
        self._feedback_adjustments: dict[str, dict] = {}
        self._method_confidence_multipliers: dict[str, float] = {}
        self._cv_confidence_thresholds: dict[str, float] = {}
        self._test_maturity_multiplier: float = 1.0
        self._test_maturity_level: str = "UNKNOWN"
        load_feedback_adjustments(self)
    @timed_log()
    def _enrich_with_context(self, intermediate_dir: str) -> dict:
        context_summary: dict = {}
        if self.all_findings and intermediate_dir:
            try:
                _disk_ctx = build_context_from_intermediates(
                    intermediate_dir, getattr(self, "skill_dir", "") or "")
                if _disk_ctx is not None:
                    _enricher = CrossValidationEnricher(_disk_ctx)
                    self.all_findings = _enricher.enrich_findings(self.all_findings)
                    _ctx_summary = _enricher.get_context_summary()
                    context_summary = dict(_ctx_summary)
                    logger.info(
                        "[CV] CrossValidationEnricher: enriched %d findings "
                        "(context=%s, call_graph=%s orphans=%s blindspots=%s "
                        "uncovered_files=%s high_complexity=%s)",
                        len(self.all_findings), _disk_ctx.available_keys,
                        _ctx_summary.get("call_graph_available"),
                        _ctx_summary.get("orphan_count"),
                        _ctx_summary.get("blindspot_count"),
                        _ctx_summary.get("uncovered_file_count"),
                        _ctx_summary.get("high_complexity_count"),
                    )
            except Exception as _ctx_err:  # noqa: BLE001
                logger.warning("[CV] CrossValidationEnricher failed (non-blocking): %s", _ctx_err)
        return context_summary
    def _cv_open_round(self, intermediate_dir: str, skill_dir: str | None) -> None:
        open_round_inputs(self, intermediate_dir, skill_dir)
        try:
            set_threshold_learning_dir(self.skill_dir)
            set_evidence_learning_dir(self.skill_dir)
        except Exception as _ld_exc:  # noqa: BLE001
            logger.warning("[CV] 学习数据目录切换失败，保持默认路径: %s", _ld_exc)
        load_fp_tracker_persisted(self)
        load_feedback_adjustments(self)
        # 开轮重载只认演化节，会清掉/覆盖 run_stage2b_execute 已套用的管线调整
        # （含记忆驱动 CV 调优）；重载后按记录重新套用，保证本轮判定实际生效。
        _pipeline_adjustments = getattr(self, "_pipeline_adjustments", None)
        if isinstance(_pipeline_adjustments, dict) and _pipeline_adjustments:
            apply_cv_threshold_adjustments(_pipeline_adjustments, self)
        self._fp_deferred = []
        self._fp_unrescued_deferred = []
        self._fp_censored_families = {}
        self._fp_filter_log = []
        self._liveness_report = {}
        self._negatives_report = {"status": "not_run"}
        self._drift_report = _drift_report_disabled()
        self._evidence_chain_audit = {}
        self._cross_locator_audit = {}
        self._oscillation_report = {}
        self._uncertain_enqueue_report = _empty_uncertain_enqueue_report()
        self._coverage_report = {}
        self.rules_applied = {}
    def _cv_rescue_channel(self, xv_findings: list) -> None:
        try:
            rescue_deferred_findings(self, xv_findings)
        except Exception:
            logger.exception(
                "[CV] 延迟救援异常降级（被抑制项复核闭环改走挂账通道）")
            _dq = getattr(self, "_fp_deferred", [])
            self._fp_unrescued_deferred = (
                [f for f in _dq if isinstance(f, dict)]
                if isinstance(_dq, list) else [])
            self._fp_deferred = []
    def _cv_collect_findings(self, intermediate_dir: str) -> None:
        available = available_evidence_methods(self.independent_results)
        set_available_methods(available)
        self.all_findings = collect_all_findings(self)
        self._collected_before_filter = source_method_counts(self.all_findings)
        self.all_findings = filter_false_positives(self, self.all_findings)
        self._context_summary = self._enrich_with_context(intermediate_dir)
    def validate(self, intermediate_dir: str,
                 regression_ctx: dict[str, Any] | None = None,
                 skill_dir: str | None = None) -> dict:
        set_trace_id(str(uuid.uuid4()))
        _t0 = time.perf_counter()
        try:
            self._cv_open_round(intermediate_dir, skill_dir)
            _gated = coverage_gate_report(self, _t0)
            if _gated is not None:
                return _gated
            analyze_degradation_impact(self)
            self._cv_collect_findings(intermediate_dir)
            xv_findings, findings_index = _cv_rule_engine_stage(
                self, intermediate_dir)
            if (not self.all_findings
                    and not self._fp_deferred
                    and not self._fp_unrescued_deferred):
                return empty_degradation_report(self, _t0)
            _human_store, _human_confirmed, _human_suppressed = (
                apply_round_human_decisions(self, xv_findings))
            _human = HumanApplication(
                store=_human_store, confirmed=_human_confirmed,
                suppressed=_human_suppressed)
            xv_findings = _cv_fuse_regression(xv_findings, regression_ctx)
            result = _cv_measure_and_assemble(
                self, xv_findings, findings_index, _human)
            result["data_lineage"] = build_data_lineage(self, xv_findings)
            _decorate_evidence_result(self, result)
            result["duration_ms"] = elapsed_ms(_t0)
            _cv_log_perf(result)
            return result
        finally:
            clear_trace_id()
    def _build_cv_result(self, ctx: dict) -> dict:
        result = build_result_core_sections(self, ctx)
        result.update(build_result_governance_sections(self, ctx))
        result.update(build_result_observability_sections(self, ctx))
        result.update(build_result_summary_sections(self, ctx))
        return result
def _apply_liveness_gate(validator, xv_findings: list) -> None:
    try:
        report = apply_detector_liveness_gate(xv_findings)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e,
                      context=f'apply_liveness_gate:{type(e).__name__}')
        report = {"status": "error", "error": str(e)}
    try:
        validator._liveness_report = report
    except (AttributeError, TypeError) as e:
        log_swallowed(__name__, e, context='apply_liveness_gate:mount')
def _run_negatives_channel(validator, xv_findings: list) -> None:
    try:
        _neg_report = validator._negatives_report = run_negatives_channels(
            validator, xv_findings)
        if _neg_report.get("downgraded_dynamics") or _neg_report.get("downgraded_precise"):
            logger.info(
                "[CV] 反向证据通道: %d 条 confirmed/likely 降级 investigated",
                _neg_report.get("downgraded_dynamics", 0)
                + _neg_report.get("downgraded_precise", 0))
    except Exception as _neg_e:
        logger.warning("[CV] 反向证据通道降级跳过: %s", _neg_e, exc_info=True)
        validator._negatives_report = {"status": "error", "error": str(_neg_e)}
def _run_drift_guard(validator, xv_findings: list) -> None:
    _drift_sd = str(getattr(validator, "skill_dir", "") or "")
    if not _drift_sd:
        _drift_err = ("skill_dir 不可推导（cv.skill_dir/_intermediate_dir "
                      "均缺），漂移守卫无源文件基准，降级停用")
        logger.warning("[CV] 代码漂移守卫降级: %s", _drift_err)
        validator._drift_report = _drift_report_disabled(_drift_err)
        return
    try:
        validator._drift_report = build_drift_report(
            validator.independent_results, validator.all_findings, _drift_sd)
        _drift_downgraded = annotate_findings_with_drift(
            xv_findings, validator._drift_report)
        if _drift_downgraded:
            logger.info("[CV] 代码漂移守卫: %d 条 confirmed 降级 investigated", _drift_downgraded)
    except Exception as _drift_e:  # noqa: BLE001
        logger.warning("[CV] 代码漂移守卫降级: %s", _drift_e)
        validator._drift_report = _drift_report_disabled(str(_drift_e))
def _collect_evidence_audits(validator, xv_findings: list) -> None:
    validator._evidence_chain_audit = build_evidence_chain_audit(xv_findings)
    validator._cross_locator_audit = cross_locator_consistency_check(xv_findings)
def _decorate_evidence_result(validator, result: dict) -> None:
    result["evidence_chain_audit"] = getattr(validator, "_evidence_chain_audit", {})
    result["cross_locator_audit"] = getattr(validator, "_cross_locator_audit", {})
    result["code_drift_audit"] = getattr(
        validator, "_drift_report", _drift_report_disabled())
    attach_negatives_audit(result, validator)
    result["_fp_censored_families"] = dict(
        getattr(validator, "_fp_censored_families", {}) or {})
    try:
        calibrate_and_persist_fp_tracker(validator, result)
        result["fp_tracker_state"] = build_fp_tracker_state()
    except Exception as _cal_err:
        logger.warning("[CV] FP tracker 校准/持久化降级: %s",
                       _cal_err, exc_info=True)
        result.setdefault("fp_tracker_state", {})
        result["fp_tracker_calibration_error"] = str(_cal_err)[:200]
class _PhaseWorkerSpec(NamedTuple):
    rule_id: str
    module_key: str
    label: str
    phase: str
_PHASE_WORKER_SPECS: dict[str, _PhaseWorkerSpec] = {
    "baseline": _PhaseWorkerSpec(
        "规则37", PHASE_MODULE_DEPS["规则37"], "基线对比", "Phase1"),
    "bizflow": _PhaseWorkerSpec(
        "规则38", PHASE_MODULE_DEPS["规则38"], "业务流追踪", "Phase1"),
    "refdepth": _PhaseWorkerSpec(
        "规则39", PHASE_MODULE_DEPS["规则39"], "引用深度分析", "Phase1"),
    "ensemble": _PhaseWorkerSpec(
        "规则40", PHASE_MODULE_DEPS["规则40"], "集群共识分析", "Phase2"),
    "mutation": _PhaseWorkerSpec(
        "规则41", PHASE_MODULE_DEPS["规则41"], "变异验证", "Phase2"),
    "vcs": _PhaseWorkerSpec("规则58", "xv_channel_signals", "VCS近变性分析", "Phase3"),
    "counter": _PhaseWorkerSpec("规则59", "xv_channel_signals", "反驳负证据分析", "Phase3"),
    "testtriage": _PhaseWorkerSpec("规则60", "xv_channel_signals", "测试触发冒烟分析", "Phase3"),
    "falsify": _PhaseWorkerSpec("规则61", "xv_falsify", "反向可证伪分析", "Phase3"),
}
def _available_annotation_modules() -> set[str]:
    available: set[str] = set()
    for mod_name in ANNOTATION_PHASE_MODULES:
        try:
            if is_module_available(mod_name):
                available.add(mod_name)
            else:
                logger.warning("[XV_Core] 注解模块不可用,计为未完成: %s",
                               mod_name)
        except Exception as e:  # noqa: BLE001
            logger.warning(
                "[XV_Core] 注解完整性检查失败,计为未完成: %s: %s",
                mod_name, e)
    return available
def _phase_rule_info(worker_key: str, description: str, findings_count: int,
                     confirmed: int = 0, **extra) -> dict:
    info = {
        'rule_id': _PHASE_WORKER_SPECS[worker_key].rule_id, 'description': description,
        'triggered': True, 'confirmed': confirmed, 'suppressed': 0,
        'investigated': 0, 'review': 0, 'likely': 0, 'uncertain': 0,
        'findings_count': findings_count,
    }
    info.update(extra)
    return info
_PHASE_TIMEOUT = _DEFAULT_WAIT_TIMEOUT_SEC
_RESULT_WAIT_TIMEOUT = 10
_MAX_PHASE_WORKERS = 8
_PHASE3_MODULE_KEYS = frozenset(
    spec.module_key for spec in _PHASE_WORKER_SPECS.values()
    if spec.phase == "Phase3")
_PHASE_DYNAMIC_CV_RULES = frozenset(
    spec.rule_id for spec in _PHASE_WORKER_SPECS.values())
def _phase_label_of(module_name: str) -> str:
    return "Phase3" if module_name in _PHASE3_MODULE_KEYS else "Phase1/2"
class _PhaseWorkerResult(NamedTuple):
    rule_id: str
    rule_info: dict | None
    payload: Any
    module_key: str
    error: str | None
def _phase_worker_success(worker_key: str, rule_info: dict,
                          payload) -> _PhaseWorkerResult:
    spec = _PHASE_WORKER_SPECS[worker_key]
    return _PhaseWorkerResult(
        spec.rule_id, rule_info, payload, spec.module_key, None)
def _phase_worker_failure(worker_key: str,
                          exc: Exception) -> _PhaseWorkerResult:
    spec = _PHASE_WORKER_SPECS[worker_key]
    logger.warning('[%s] %s失败: %s', spec.phase, spec.label, exc, exc_info=True)  # noqa: LOG014
    return _PhaseWorkerResult(
        spec.rule_id, None, None, spec.module_key, str(exc))
def _phase_worker_guard(worker_key: str):
    def _decorator(fn):
        @wraps(fn)
        def _wrapped(*args, **kwargs):
            try:
                return fn(*args, **kwargs)
            except Exception as e:  # noqa: BLE001
                log_swallowed(__name__, e,
                              context=f'{fn.__name__}:{type(e).__name__}')
                return _phase_worker_failure(worker_key, e)
        return _wrapped
    return _decorator
@_phase_worker_guard("baseline")
def _pvrun_baseline(skill_dir, snapshot, _independent_results):
    diff_results, session_id = diff_findings_with_baseline(skill_dir, snapshot)
    baseline_count = len(diff_results)
    noise_count = sum(1 for r in diff_results.values() if r.is_persistent_noise)
    rule_info = _phase_rule_info(
        'baseline', '历史基线差异对比', baseline_count,
        phase1_baseline_session_id=session_id or '',
        phase1_noise_findings=noise_count)
    logger.info('[Phase1] 基线对比: %d findings, %d persistent noise',
                baseline_count, noise_count)
    return _phase_worker_success('baseline', rule_info, diff_results)
@_phase_worker_guard("bizflow")
def _pvrun_bizflow(skill_dir, snapshot, _independent_results, call_graph=None):
    bf_validator = BusinessFlowValidator(skill_dir)
    bf_report = bf_validator.validate(snapshot, call_graph)
    rule_info = _phase_rule_info(
        'bizflow', '业务流追踪验证', bf_report.total_findings,
        phase1_reachable=bf_report.reachable_findings,
        phase1_unreachable=bf_report.unreachable_findings,
        phase1_fp_candidates=bf_report.false_positive_candidates)
    logger.info('[Phase1] 业务流: %d reachable, %d unreachable, %d FP candidates',
                bf_report.reachable_findings, bf_report.unreachable_findings,
                bf_report.false_positive_candidates)
    return _phase_worker_success('bizflow', rule_info, bf_report)
@_phase_worker_guard("refdepth")
def _pvrun_refdepth(skill_dir, snapshot, _independent_results, call_graph=None):
    rd_analyzer = RefDepthAnalyzer(skill_dir)
    rd_results = rd_analyzer.analyze(snapshot, call_graph)
    boosted = sum(1 for r in rd_results.values() if r.priority_boost > 0)
    isolated = sum(1 for r in rd_results.values() if r.is_isolated)
    rule_info = _phase_rule_info(
        'refdepth', '引用深度加权排序', len(rd_results),
        phase1_priority_boosted=boosted, phase1_isolated=isolated)
    logger.info('[Phase1] 引用深度: %d findings, %d boosted, %d isolated',
                len(rd_results), boosted, isolated)
    return _phase_worker_success('refdepth', rule_info, rd_results)
@_phase_worker_guard("ensemble")
def _pvrun_ensemble(_skill_dir, snapshot):
    ensemble = EnsembleConsensusAnalyzer()
    ensemble_results = ensemble.analyze(snapshot)
    cross_group = sum(1 for r in ensemble_results.values() if r.is_confirmed)
    low_conf = sum(1 for r in ensemble_results.values() if r.is_low_confidence)
    rule_info = _phase_rule_info(
        'ensemble', '集群共识验证', len(ensemble_results),
        confirmed=cross_group,
        phase2_cross_group=cross_group, phase2_low_confidence=low_conf)
    logger.info('[Phase2] 集群共识: %d findings, %d cross-group, %d low-confidence',
                len(ensemble_results), cross_group, low_conf)
    return _phase_worker_success('ensemble', rule_info, ensemble_results)
@_phase_worker_guard("mutation")
def _pvrun_mutation(skill_dir, snapshot, _independent_results):
    mutation = MutationVerifier(skill_dir)
    mutation_report = mutation.validate(snapshot)
    rule_info = _phase_rule_info(
        'mutation', '变异测试确认', mutation_report.total_verified,
        confirmed=mutation_report.confirmed_dead,
        phase2_confirmed_dead=mutation_report.confirmed_dead,
        phase2_false_positive=mutation_report.false_positive,
        phase2_errors=mutation_report.errors)
    logger.info('[Phase2] 变异验证: %d verified, %d dead, %d FP, %d errors',
                mutation_report.total_verified, mutation_report.confirmed_dead,
                mutation_report.false_positive, mutation_report.errors)
    return _phase_worker_success('mutation', rule_info, mutation_report)
@_phase_worker_guard("vcs")
def _pvrun_vcs(skill_dir, snapshot, _independent_results):
    vcs = VCSRecencyAnalyzer(skill_dir)
    vcs_results = vcs.analyze(snapshot)
    boosted = sum(1 for r in vcs_results.values() if r.get("boost"))
    rule_info = _phase_rule_info(
        'vcs', 'VCS近变性证据', len(vcs_results),
        phase3_vcs_boosted=boosted,
        phase3_vcs_mode='git' if vcs.is_git else 'mtime')
    logger.info('[Phase3] VCS近变性: %d findings, %d boosted (mode=%s)',
                len(vcs_results), boosted, 'git' if vcs.is_git else 'mtime')
    return _phase_worker_success('vcs', rule_info, vcs_results)
@_phase_worker_guard("counter")
def _pvrun_counter(skill_dir, snapshot, _independent_results):
    ce = CounterEvidenceAnalyzer(skill_dir)
    ce_results = ce.analyze(snapshot)
    neg = sum(1 for r in ce_results.values() if r.get("counter_evidence"))
    rule_info = _phase_rule_info(
        'counter', '反驳型负证据', len(ce_results),
        phase3_counter_evidence=neg)
    logger.info('[Phase3] 反驳负证据: %d findings, %d counter-evidence',
                len(ce_results), neg)
    return _phase_worker_success('counter', rule_info, ce_results)
@_phase_worker_guard("testtriage")
def _pvrun_testtriage(skill_dir, snapshot, _independent_results):
    tt = TestTriageVerifier(skill_dir)
    tt_results = tt.analyze(snapshot)
    _p = sum(1 for r in tt_results.values() if r.get("smoke") == "pass")
    _f = sum(1 for r in tt_results.values() if r.get("smoke") == "fail")
    rule_info = _phase_rule_info(
        'testtriage', '测试触发定向冒烟', len(tt_results),
        phase3_smoke_pass=_p, phase3_smoke_fail=_f)
    logger.info('[Phase3] 测试触发冒烟: %d findings, pass=%d, fail=%d',
                len(tt_results), _p, _f)
    return _phase_worker_success('testtriage', rule_info, tt_results)
@_phase_worker_guard("falsify")
def _pvrun_falsify(skill_dir, snapshot, _independent_results):
    fa = FalsificationAnalyzer(skill_dir)
    fa_results = fa.analyze(snapshot)
    _ok = sum(1 for r in fa_results.values() if r.get("verified") is True)
    _bad = sum(1 for r in fa_results.values() if r.get("verified") is False)
    rule_info = _phase_rule_info(
        'falsify', '反向可证伪验证', len(fa_results),
        phase3_falsify_reproduced=_ok, phase3_falsify_absent=_bad)
    logger.info('[Phase3] 反向可证伪: %d findings, reproduced=%d, absent=%d',
                len(fa_results), _ok, _bad)
    return _phase_worker_success('falsify', rule_info, fa_results)
def _restore_completed_result(future, key: str, phase_results: dict) -> None:
    try:
        result = future.result(timeout=0)  # jwsgj:suppress TP-19
    except Exception as e:  # noqa: BLE001
        logger.warning('[Phase] 超时后处理 %s 结果失败: %s', key, e)
        return
    if result and result[0] not in phase_results:
        phase_results[result[0]] = result
        logger.info('[Phase] 超时后恢复分析器结果: %s', result[0])
def _recover_timed_out_results(futures: dict, phase_results: dict) -> None:
    for future, key in futures.items():
        if future.done() and not future.cancelled():
            _restore_completed_result(future, key, phase_results)
def _shutdown_phase_executor(executor, timed_out: bool) -> None:
    if timed_out:
        try:
            executor.shutdown(wait=False, cancel_futures=True)
        except TypeError as _e:
            log_swallowed(__name__, _e, context='pre_validate:TypeError')
            executor.shutdown(wait=False)
    else:
        executor.shutdown(wait=True)
def _drain_phase_futures(futures: dict, phase_results: dict) -> bool:
    try:
        for future in as_completed(futures, timeout=_PHASE_TIMEOUT):
            key = futures[future]
            try:
                result = future.result(timeout=_RESULT_WAIT_TIMEOUT)
                phase_results[result[0]] = result
            except (TimeoutError, _CFTimeoutError):
                logger.warning('[Phase] 分析器 %s 超时(%ds)，跳过', key, _PHASE_TIMEOUT)
            except Exception as e:  # noqa: BLE001
                logger.warning('[Phase] 分析器 %s 异常: %s', key, e)
    except (TimeoutError, _CFTimeoutError):
        logger.warning('[Phase] 整体超时(%ds)，处理已完成的future', _PHASE_TIMEOUT)
        return True
    return False
def _new_phase_executor():
    try:
        return ThreadPoolExecutor(
            max_workers=_cpu_bounded_workers(_MAX_PHASE_WORKERS))
    except (RuntimeError, OSError, ValueError):
        logger.exception('[Phase] 线程池创建失败，全部通道按结果缺失降级')
        return None
def _submit_phase_workers(executor, phase_workers: dict) -> dict:
    futures: dict = {}
    for key, fn in phase_workers.items():
        try:
            futures[executor.submit(fn)] = key
        except (RuntimeError, OSError) as e:
            logger.warning(
                '[Phase] 分析器 %s 调度失败，按结果缺失计入 phase_health: %s',
                key, e)
    return futures
def _run_phase_workers(phase_workers: dict) -> dict:
    phase_results: dict = {}
    _phase_timed_out = False
    executor = _new_phase_executor()
    if executor is None:
        return phase_results
    try:
        futures = _submit_phase_workers(executor, phase_workers)
        _phase_timed_out = _drain_phase_futures(futures, phase_results)
        if _phase_timed_out:
            _recover_timed_out_results(futures, phase_results)
        for future in futures:
            if not future.done():
                future.cancel()
    finally:
        _shutdown_phase_executor(executor, _phase_timed_out)
    return phase_results
def _record_phase_error(cv, module_name: str, error: str) -> None:
    record = {
        "module": module_name,
        "phase": _phase_label_of(module_name),
        "error": error}
    criticality = PHASE_MODULE_CRITICALITY.get(module_name, "")
    if criticality:
        record["criticality"] = criticality
    cv._phase_errors.append(record)
    try:
        set_phase_module_status(module_name, False)
    except Exception as e:  # noqa: BLE001
        logger.warning("[CV] Phase module status set failed: %s", e)
def _dispatch_phase_annotation(cv, worker_key: str, meta: tuple,
                               raw_results, findings_snapshot: list) -> None:
    if raw_results is None:
        return
    _rule_key, module_name, _annotate_fn = meta
    if not callable(_annotate_fn):
        logger.warning('[Phase] 注解函数缺失: %r（META 漂移），%s 通道按失败记账',
                       _annotate_fn, _rule_key)
        _record_phase_error(cv, module_name,
                            f"注解函数缺失({module_name}): {_rule_key} 未完成注解")
        return
    try:
        _annotate_fn(findings_snapshot, raw_results)
    except Exception as e:
        logger.warning('[Phase] 分析器 %s(%s) 注解失败: %s',
                       worker_key, _rule_key, e, exc_info=True)
        _record_phase_error(cv, module_name, f"注解失败({module_name}): {e}")
def _collect_and_annotate_phase_results(cv, phase_workers: dict,
                                        phase_results: dict,
                                        findings_snapshot: list) -> None:
    for _worker_key, _meta in _PHASE_WORKER_META.items():
        if _worker_key not in phase_workers:
            continue
        _rule_key, _module_name, _annotate_fn = _meta
        result = phase_results.get(_rule_key)
        if result is None:
            _record_phase_error(cv, _module_name,
                                f"分析器 {_worker_key}({_rule_key}) 结果缺失"
                                f"（{_PHASE_TIMEOUT}s 超时窗口内未完成或结果收集失败），"
                                f"按失败计入 phase_health")
            continue
        _, rule_info, _raw_results, module_name, error = result
        if error:
            _record_phase_error(cv, module_name, error)
            continue
        if rule_info:
            cv.rules_applied.setdefault(_rule_key, rule_info)
        _dispatch_phase_annotation(
            cv, _worker_key, _meta, _raw_results, findings_snapshot)
def _reset_phase_module_status() -> None:
    for mod in _PHASE_MODULES:
        try:
            set_phase_module_status(mod, True)
        except Exception as e:
            logger.warning("[pre_validate] phase 模块 %s 状态复位失败: %s",
                           mod, e, exc_info=True)
def _record_all_workers_missing(cv, reason: str) -> None:
    for _worker_key, (_rule_key, _module_name, _annotate_fn) in _PHASE_WORKER_META.items():
        _record_phase_error(
            cv, _module_name,
            f"{reason}，分析器 {_worker_key}({_rule_key}) 未运行，按失败计入 phase_health")
def _build_phase_workers(skill_dir: str, snapshot: list, ind_results: dict,
                         call_graph) -> dict:
    return {
        'baseline': lambda: _pvrun_baseline(skill_dir, snapshot, ind_results),
        'bizflow': lambda: _pvrun_bizflow(skill_dir, snapshot, ind_results, call_graph),
        'refdepth': lambda: _pvrun_refdepth(skill_dir, snapshot, ind_results, call_graph),
        'ensemble': lambda: _pvrun_ensemble(skill_dir, snapshot),
        'mutation': lambda: _pvrun_mutation(skill_dir, snapshot, ind_results),
        'vcs': lambda: _pvrun_vcs(skill_dir, snapshot, ind_results),
        'counter': lambda: _pvrun_counter(skill_dir, snapshot, ind_results),
        'testtriage': lambda: _pvrun_testtriage(skill_dir, snapshot, ind_results),
        'falsify': lambda: _pvrun_falsify(skill_dir, snapshot, ind_results),
    }
def pre_validate(cv) -> None:
    cv._phase_errors = []
    _reset_phase_module_status()
    if not cv.all_findings:
        return
    skill_dir, call_graph = derive_skill_dir_and_graph(cv)
    if not skill_dir:
        _record_all_workers_missing(cv, "skill_dir 推导失败")
        return
    _findings_snapshot = list(cv.all_findings)
    _ind_results = normalized_independent_results(cv)
    _phase_workers = _build_phase_workers(
        skill_dir, _findings_snapshot, _ind_results, call_graph)
    _phase_results = _run_phase_workers(_phase_workers)
    _collect_and_annotate_phase_results(
        cv, _phase_workers, _phase_results, _findings_snapshot)
    cv.all_findings = _findings_snapshot
    apply_annotation_completeness(
        cv.all_findings, _available_annotation_modules())
_PHASE_WORKER_ANNOTATIONS: dict[str, Callable[..., Any]] = {
    'baseline': annotate_findings,
    'bizflow': annotate_findings_with_bizflow,
    'refdepth': annotate_findings_with_ref_depth,
    'ensemble': annotate_findings_with_ensemble,
    'mutation': annotate_findings_with_mutation,
    'vcs': annotate_findings_with_vcs,
    'counter': annotate_findings_with_counter_evidence,
    'testtriage': annotate_findings_with_test_triage,
    'falsify': annotate_findings_with_falsification,
}
def _build_phase_worker_meta(
) -> dict[str, tuple[str, str, Callable[..., Any]]]:
    expected = set(_PHASE_WORKER_SPECS)
    registered = set(_PHASE_WORKER_ANNOTATIONS)
    missing = sorted(expected - registered)
    unexpected = sorted(registered - expected)
    if missing or unexpected:
        raise RuntimeError(
            "相位分析器注解函数登记漂移（_PHASE_WORKER_ANNOTATIONS 与 "
            f"_PHASE_WORKER_SPECS 失同步）: missing={missing}, "
            f"unexpected={unexpected}")
    return {
        key: (spec.rule_id, spec.module_key, _PHASE_WORKER_ANNOTATIONS[key])
        for key, spec in _PHASE_WORKER_SPECS.items()
    }
_PHASE_WORKER_META: dict[str, tuple[str, str, Callable[..., Any]]] = (
    _build_phase_worker_meta())
_PHASE_MODULES = tuple(dict.fromkeys(
    module_name
    for _rule_key, module_name, _annotate_fn in _PHASE_WORKER_META.values()))
def prepare_rule_phase(validator, intermediate_dir: str) -> None:
    pre_validate(validator)
    inject_quadrant_findings(validator, intermediate_dir)
    post_annotation_fp_filter(validator)
    reinject_deferred_as_shadow(validator)
    rebuild_rules_applied(validator)
    apply_feedback_thresholds(validator)
def _cv_rule_engine_stage(validator, intermediate_dir: str) -> tuple[list, dict]:
    prepare_rule_phase(validator, intermediate_dir)
    findings_index = build_findings_index(validator)
    xv_findings = apply_rules(validator, findings_index)
    validator._cv_rescue_channel(xv_findings)
    post_match_suppression(validator, xv_findings)
    _apply_liveness_gate(validator, xv_findings)
    _run_negatives_channel(validator, xv_findings)
    _run_drift_guard(validator, xv_findings)
    return xv_findings, findings_index
def _run_oscillation_channel(validator, skill_dir: str, xv_findings: list) -> None:
    try:
        validator._oscillation_report = build_oscillation_report_for_cv(
            skill_dir, xv_findings)
    except Exception as _osc_e:  # noqa: BLE001
        logger.warning("[CV] 振荡检测降级: %s", _osc_e)
        validator._oscillation_report = build_oscillation_degraded_report(_osc_e)
def _run_fp_signal_channel(skill_dir: str, xv_findings: list) -> None:
    try:
        families = feed_channel_signals_to_fp_tracker(skill_dir, xv_findings)
        if families:
            logger.info("[CV] 闭环C: %d 个规则族通道信号→FP固化统计", families)
    except Exception as _e:  # noqa: BLE001
        logger.debug("[CV] 闭环C 通道信号→FP统计降级: %s", _e)
def _run_uncertain_review_channel(validator, skill_dir: str,
                                  xv_findings: list) -> None:
    try:
        report = run_uncertain_enqueue_channel(
            validator, skill_dir, xv_findings)
    except Exception as exc:
        report = _empty_uncertain_enqueue_report()
        report.update({
            "attempted": True, "failed": True,
            "error": str(exc)[:300],
        })
        logger.warning(
            "[CV] uncertain 复核队列入队异常（降级继续）: %s",
            exc, exc_info=True)
    if not isinstance(report, dict):
        _report_type = type(report).__name__
        report = _empty_uncertain_enqueue_report()
        report.update({"attempted": True, "failed": True,
                       "error": f"non-dict report: {_report_type}"})
    validator._uncertain_enqueue_report = report
    if report.get("failed"):
        logger.warning("[CV] uncertain 复核队列入队失败（降级继续）: %s",
                       report.get("error", ""))
    elif report.get("enqueued"):
        logger.info("[CV] %s 个 finding 进入 AI 语义复核队列",
                    report["enqueued"])
def run_post_rule_channels(validator, xv_findings: list) -> None:
    _sd = str(getattr(validator, "skill_dir", "") or "")
    if not _sd:
        logger.debug("[CV] skill_dir 不可推导，后置规则通道（振荡/复核入队/FP 统计）跳过")
        return
    _run_oscillation_channel(validator, _sd, xv_findings)
    _run_uncertain_review_channel(validator, _sd, xv_findings)
    _run_fp_signal_channel(_sd, xv_findings)
def _cv_measure_and_assemble(validator, xv_findings, findings_index,
                             human: HumanApplication) -> dict:
    normalize_conclusion_v2(xv_findings)
    run_post_rule_channels(validator, xv_findings)
    _collect_evidence_audits(validator, xv_findings)
    _stats_ctx = validate_stage_statistics(validator, xv_findings, findings_index)
    return validator._build_cv_result(build_cv_stage_context(
        _stats_ctx, xv_findings, human.confirmed,
        human.suppressed, human.store))
def _cv_fuse_regression(xv_findings, regression_ctx):
    if not isinstance(regression_ctx, dict):
        return xv_findings
    if not regression_ctx.get("changed_files"):
        return xv_findings
    try:
        return fuse_regression_into_xv(xv_findings, regression_ctx)
    except Exception as _e:  # noqa: BLE001
        logger.warning("[CV] 回归融合执行失败，跳过回归融合: %s", _e)
        return xv_findings
def _cv_log_perf(result: dict) -> None:
    try:
        participation = result.get('participation')
        if not isinstance(participation, dict):
            participation = {}
        perf_trace(
            'cv_validate',
            result.get('duration_ms', 0),
            confirmed=result.get('confirmed', 0),
            suppressed=result.get('suppressed', 0),
            likely=result.get('likely', 0),
            uncertain=result.get('uncertain', 0),
            total_input=result.get(FIELD_TOTAL_INPUT_FINDINGS, 0),
            cross_validated=result.get('cross_validated', 0),
            participation_rate=participation.get('participation_rate', 0),
            all_participated=bool(participation.get('all_participated', False)),
            timestamp=result.get('timestamp', ''),
        )
    except Exception as _perf_exc:  # noqa: BLE001
        try:
            log_swallowed(__name__, _perf_exc, context='perf_trace:cv_validate')
        except Exception:
            logger.warning("CV perf_trace failed: %s", _perf_exc, exc_info=True)
def filter_false_positives_standalone(
    findings: list,
    suppressed_sink: list | None = None,
) -> list:
    try:
        validator = CrossValidatorV2()
        filtered = filter_false_positives(validator, findings)
    except Exception as e:  # noqa: BLE001
        logger.warning("filter_false_positives_standalone: %s", e)
        return findings
    _deferred = getattr(validator, "_fp_deferred", None)
    _removed = ([f for f in _deferred if isinstance(f, dict)]
                if isinstance(_deferred, list) else [])
    if _removed:
        logger.warning(
            "[FP-Filter-Standalone] %d 个 finding 被误报策略删除"
            "（独立入口无自动复核队列，须经 suppressed_sink 收集处置）",
            len(_removed))
        if isinstance(suppressed_sink, list):
            suppressed_sink.extend(_removed)
    return filtered
def _collect_cv_result_metrics(result: dict, cv_report: dict) -> None:
    result["total_findings"] = cv_report.get(FIELD_TOTAL_INPUT_FINDINGS, 0)
    result[FIELD_FINDINGS_SUPPRESSED] = cv_report.get(FIELD_FINDINGS_SUPPRESSED, 0)
    result["findings_investigated"] = cv_report.get("findings_investigated", 0)
    result[FIELD_RULES_TRIGGERED] = cv_report.get("rules_applied_count", 0)
    _phase_errors = cv_report.get("phase_errors")
    result["phase_errors"] = (len(_phase_errors)
                              if isinstance(_phase_errors, list) else 0)
    _participation = cv_report.get("participation")
    result["participation_rate"] = (
        _participation.get("participation_rate", 0)
        if isinstance(_participation, dict) else 0)
def _stage2b_llm_cv(ctx: Any, cv_report: dict, result: dict) -> None:
    if ctx.llm_call_fn is None:
        return
    try:
        out = refine_cv_findings_with_llm(
            cv_report, skill_dir=ctx.skill_dir, llm_call_fn=ctx.llm_call_fn)
        if out is None:
            return
        result["llm_cv_reconcile"] = out["reconcile"]
        if out["synced"]:
            logger.info("[Stage2b] LLM升级条目同步确认通道: %d 条", out["synced"])
        stats = out["stats"]
        result["llm_cv_stats"] = stats
        logger.info("[Stage2b] LLM语义验证: %d processed, %d upgraded, %d downgraded, %d uncertain",
                    stats["processed"], stats["upgraded"],
                    stats["downgraded"], stats["uncertain"])
    except Exception as e:  # noqa: BLE001
        logger.warning("[Stage2b] LLM语义验证跳过: %s", e)
        result["llm_cv_error"] = str(e)[:200]
def _attach_bi_taint_evidence(entry: dict) -> None:
    sources = entry.get("sources")
    sources = list(sources) if isinstance(
        sources, (list, tuple, set, frozenset)) else []
    entry["sources"] = sources
    for ev in ("BI_TAINT_FORWARD", "BI_TAINT_BACKWARD"):
        if ev not in sources:
            sources.append(ev)
    entry["source_count"] = max(int_or(entry.get("source_count"), 0),
                                len(sources))
    entry["_source_count"] = len(sources)
    entry["_independent_source_count"] = count_independent_sources(sources)
    entry["_bi_taint_confirmed"] = True
def _channel_dicts(cv_report: dict, channel: str) -> list:
    _entries = cv_report.get(channel)
    if not isinstance(_entries, list):
        return []
    return [entry for entry in _entries if isinstance(entry, dict)]
def _bi_taint_identity(entry: dict) -> tuple:
    filepath = _identity_text(finding_file_path(entry))
    line = finding_line_no(entry) or 0
    if filepath and line:
        return ("location", filepath, line)
    return ("locator", _identity_text(entry.get("locator")))
def _bi_taint_candidate_view(entry: dict, finding: dict) -> dict:
    candidate = dict(finding)
    if finding is not entry:
        for key in ("locator", "file", "line"):
            if key in entry:
                candidate.setdefault(key, entry[key])
    if not finding_file_path(candidate):
        filepath = parse_locator_file(candidate.get("locator"))
        if filepath:
            candidate["file"] = filepath
    line = finding_line_no(candidate)
    if line:
        candidate["line"] = line
    candidate["locator"] = _bi_taint_queue_locator(candidate)
    return candidate
def _bi_taint_candidate_views(entry: dict):
    yield _bi_taint_candidate_view(entry, entry)
    findings = entry.get("findings")
    if not isinstance(findings, list):
        return
    for finding in findings:
        if isinstance(finding, dict):
            yield _bi_taint_candidate_view(entry, finding)
def _bi_taint_candidates(cv_report: dict) -> list:
    candidates: dict[tuple, dict] = {}
    for channel in ("findings_index", "confirmed_findings"):
        for entry in _channel_dicts(cv_report, channel):
            for candidate in _bi_taint_candidate_views(entry):
                identity = _bi_taint_identity(candidate)
                current = candidates.get(identity)
                if current is None or (
                        not _looks_security_finding(current)
                        and _looks_security_finding(candidate)):
                    candidates[identity] = candidate
    return list(candidates.values())
def _bi_taint_queue_locator(entry: dict) -> str:
    filepath = _identity_text(finding_file_path(entry))
    line = finding_line_no(entry)
    if filepath and line:
        return f"{filepath}:{line}"
    return _identity_text(entry.get("locator"))
def _apply_bi_taint_confirmations(cv_report: dict, bi_result: dict) -> None:
    locators = {
        _loc for _loc, _info in bi_result["per_finding"].items()
        if isinstance(_info, dict) and _info.get("confirmed")
    }
    if not locators:
        return
    for entry in [*_channel_dicts(cv_report, "findings_index"),
                  *_channel_dicts(cv_report, "confirmed_findings")]:
        entry_candidate = _bi_taint_candidate_view(entry, entry)
        entry_confirmed = (
            _looks_security_finding(entry_candidate)
            and _bi_taint_queue_locator(entry_candidate) in locators)
        findings = entry.get("findings")
        if isinstance(findings, list):
            for finding in findings:
                if not isinstance(finding, dict):
                    continue
                candidate = _bi_taint_candidate_view(entry, finding)
                if (_looks_security_finding(candidate)
                        and _bi_taint_queue_locator(candidate) in locators):
                    _attach_bi_taint_evidence(finding)
                    entry_confirmed = True
        if entry_confirmed:
            _attach_bi_taint_evidence(entry)
def _refresh_cross_validated_totals(cv_report: dict) -> None:
    validated = _count_cross_validated_locators(
        cv_report.get("findings_index"))
    total = _metric_count(cv_report.get(FIELD_TOTAL_INPUT_FINDINGS))
    cv_report["cross_validated"] = validated
    cv_report["solo_findings"] = max(total - validated, 0)
def run_stage2b_bidirectional_taint(skill_dir: str, cv_report: dict,
                                   result: dict) -> None:
    try:
        _bi_candidates = _bi_taint_candidates(cv_report)
        _bi_result = validate_security_findings(skill_dir, _bi_candidates)
        if _bi_result["summary"]["sinks"] > 0:
            cv_report["bidirectional_taint"] = _bi_result["summary"]
            result["bidirectional_taint"] = _bi_result["summary"]
            _apply_bi_taint_confirmations(cv_report, _bi_result)
            _refresh_cross_validated_totals(cv_report)
            logger.info("[Stage2b] 双向污点验证: %d sinks, %d confirmed",
                        _bi_result["summary"]["sinks"],
                        _bi_result["summary"]["confirmed"])
    except Exception as _bi_err:  # noqa: BLE001
        logger.warning("[Stage2b] 双向污点验证跳过: %s", _bi_err)
def apply_stage2b_enhancers(ctx: Any, cv_report: dict,
                            result: dict) -> None:
    _stage2b_llm_cv(ctx, cv_report, result)
    run_stage2b_test_bridge(ctx.test_bridge, ctx.temp_dir, cv_report, result)
    run_stage2b_bidirectional_taint(ctx.skill_dir, cv_report, result)
def _metric_count(value) -> int:
    if isinstance(value, bool):
        return int(value)
    if is_real_number(value):
        return int(value)
    return int_or(value, 0)
def summarize_cv_result(result: dict) -> tuple[int, int, int]:
    return (
        _metric_count(result.get("total_findings")),
        _metric_count(result.get(FIELD_FINDINGS_SUPPRESSED)),
        _metric_count(result.get(FIELD_RULES_TRIGGERED)),
    )
def run_stage2b_execute(ctx: Any,
                        regression_ctx: dict | None) -> tuple[dict, dict]:
    result = {
        "stage": CAT_CROSS_VALIDATION,
        "timestamp": timestamp_ms(),
        "status": "running",
    }
    cv = CrossValidatorV2()
    assess_cv_maturity(ctx.skill_dir, cv, result)
    apply_cv_threshold_adjustments(ctx.adjustments, cv)
    cv_report = cv.validate(
        intermediate_dir=ctx.intermediate_dir,
        regression_ctx=regression_ctx,
        skill_dir=ctx.skill_dir,
    )
    ensure_confirmed_channel(cv_report)
    result["report"] = cv_report
    cv_report = apply_cv_memory_enhancements(
        getattr(ctx, "memory_context", None), cv_report, result)
    apply_stage2b_enhancers(ctx, cv_report, result)
    _collect_cv_result_metrics(result, cv_report)
    attach_cv_report_summary(cv_report, result)
    return result, cv_report
_LLM_ROUNDS = 3
_LLM_MAX_CALLS = 20
_DECIDABLE_VERDICTS = frozenset({"confirmed", "suppressed"})
_VERDICTS = _DECIDABLE_VERDICTS | {"uncertain"}
_LLM_REFINABLE_CONCLUSIONS = frozenset({
    "investigated", "suppressed", "review", "reviewed"})
_LLM_OUTCOME_FIELDS = (
    "_llm_upgraded",
    "_llm_suppression_affirmed",
    "_llm_downgraded",
    "_llm_vote_confidence",
    "_llm_verified",
    "_llm_reasoning",
    "_llm_disagreement",
    "_llm_uncertain",
)
def ensure_confirmed_channel(cv_report: dict) -> None:
    if not isinstance(cv_report.get("confirmed_findings"), list):
        cv_report["confirmed_findings"] = (
            materialize_confirmed_channel(cv_report))
def refine_cv_findings_with_llm(
    cv_report: dict,
    *,
    skill_dir: str,
    llm_call_fn: Callable | None,
    rounds: int | None = None,
    max_calls: int | None = None,
) -> dict | None:
    if llm_call_fn is None:
        return None
    findings_index = cv_report.get("findings_index", [])
    if not (isinstance(findings_index, list) and findings_index):
        return None
    llm_cv = LLMCrossValidator(
        llm_call_fn=llm_call_fn, rounds=rounds, max_calls=max_calls,
        base_dir=skill_dir)
    before_snapshot = _llm_before_snapshot(findings_index)
    refined = llm_cv.filter(findings_index)
    stats = _llm_refine_stats(refined)
    cv_report["findings_index"] = refined
    synced = _sync_confirmed_channel_after_llm(cv_report, refined)
    _refresh_refined_cv_statistics(cv_report, refined, before_snapshot)
    reconcile = _reconcile_after_refine(skill_dir, before_snapshot, refined)
    return {"stats": stats, "synced": synced, "reconcile": reconcile}
def _reconcile_after_refine(skill_dir: str, before_snapshot: list,
                            refined: list) -> dict:
    try:
        recon = reconcile_cv_uncertain_after_llm(
            skill_dir, before_snapshot, refined)
        if recon.get("failed"):
            logger.warning("[Stage2b] LLM复核队列对账未闭合: %s",
                           recon.get("error", ""))
        return recon
    except Exception as rc_e:  # noqa: BLE001
        logger.warning("[Stage2b] LLM复核队列对账降级（复核闭环可能未闭合）: %s",
                       rc_e)
        return {"attempted": True, "failed": True,
                "error": str(rc_e)[:300]}
_RULE_CONCLUSION_COUNT_FIELDS = (
    "confirmed", "suppressed", "investigated", "review", "likely", "uncertain",
)
def _empty_rule_conclusion_stats() -> dict:
    return {
        "triggered": False,
        "findings_count": 0,
        **dict.fromkeys(_RULE_CONCLUSION_COUNT_FIELDS, 0),
    }
def _rule_conclusion_stats_by_id(findings: list) -> dict:
    stats_by_id: dict[str, dict] = {}
    for finding in _dict_entries(findings):
        rule_id = finding.get("rule_applied")
        if isinstance(rule_id, str) and rule_id and rule_id not in stats_by_id:
            stats_by_id[rule_id] = _empty_rule_conclusion_stats()
    apply_rule_stats(SimpleNamespace(rules_applied=stats_by_id), findings)
    return stats_by_id
def _refresh_rule_details_after_llm(cv_report: dict, before: list,
                                    refined: list) -> None:
    details = _dict_entries(cv_report.get("rules_detail"))
    if not details:
        return
    before_by_id = _rule_conclusion_stats_by_id(before)
    after_by_id = _rule_conclusion_stats_by_id(refined)
    for detail in details:
        rule_id = detail.get("rule_id")
        if not isinstance(rule_id, str):
            continue
        before_rule = before_by_id.get(rule_id, {})
        after_rule = after_by_id.get(rule_id, {})
        for field in _RULE_CONCLUSION_COUNT_FIELDS:
            delta = (after_rule.get(field, 0)
                     - before_rule.get(field, 0))
            if delta:
                detail[field] = int_or(detail.get(field), 0) + delta
def _refresh_data_lineage_after_llm(cv_report: dict, refined: list) -> None:
    lineage = cv_report.get("data_lineage")
    if not isinstance(lineage, dict):
        return
    confirmed = _confirmed_method_counts(refined)
    for method_id, row in lineage.items():
        if isinstance(row, dict):
            row["confirmed"] = confirmed.get(method_id, 0)
def _refresh_refined_cv_statistics(cv_report: dict, refined: list,
                                   before: list) -> None:
    _refresh_rule_details_after_llm(cv_report, before, refined)
    _refresh_data_lineage_after_llm(cv_report, refined)
    stats = compute_statistics(refined)
    cv_report.update({
        "findings_validated": stats["xv_finding_count"],
        "confirmed": stats["confirmed"],
        "suppressed": stats["suppressed"],
        "investigated": stats["investigated"],
        "review": stats["review_c"],
        "likely": stats["likely_c"],
        "uncertain": stats["uncertain_c"],
        "findings_confirmed": stats["findings_confirmed"],
        FIELD_FINDINGS_SUPPRESSED: stats[FIELD_FINDINGS_SUPPRESSED],
        "findings_investigated": stats["findings_investigated"],
        "findings_review": stats["findings_review"],
        "findings_likely": stats["findings_likely"],
        "findings_uncertain": stats["findings_uncertain"],
    })
    cv_report["function_level_summary"] = aggregate_by_function(refined)
    protection_log = compute_p0p1_protection_log(refined)
    cv_report["p0p1_protection_log"] = protection_log
    cv_report["p0p1_protection_count"] = len(protection_log)
    cv_report["executive_summary"] = build_executive_summary(
        _metric_count(cv_report.get(FIELD_TOTAL_INPUT_FINDINGS)),
        stats["confirmed"], stats["likely_c"], stats["uncertain_c"],
        stats["suppressed"], _metric_count(cv_report.get("contradiction_count")),
        stats["xv_finding_count"],
        phase_health=cv_report.get("phase_health"),
    )
def _flatten_confirmed_entry(entry: dict, derived: list) -> None:
    inner_findings = entry.get("findings")
    candidates = (
        [finding for finding in inner_findings if isinstance(finding, dict)]
        if isinstance(inner_findings, list) else [])
    if not candidates:
        candidates = [entry]
    for finding in candidates:
        if entry.get("locator"):
            finding.setdefault("locator", entry["locator"])
        if entry.get("rule_family"):
            finding.setdefault("rule_family", entry["rule_family"])
        if "sources" in entry:
            finding.setdefault(
                "sources", normalize_sources(entry.get("sources")))
        finding["conclusion"] = "confirmed"
        finding["conclusion_v2"] = "confirmed"
        derived.append(finding)
def _dict_entries(value) -> list:
    if not isinstance(value, list):
        return []
    return [entry for entry in value if isinstance(entry, dict)]
def _is_confirmed_conclusion(entry: dict) -> bool:
    conclusion = entry.get("conclusion")
    return (isinstance(conclusion, str)
            and conclusion.strip().lower() == "confirmed")
def _confirmed_entries(index) -> list:
    return [entry for entry in _dict_entries(index)
            if _is_confirmed_conclusion(entry)]
def _identity_text(value) -> str:
    return value.strip() if isinstance(value, str) else ""
def _location_identity(entry: dict) -> tuple | None:
    filepath = _identity_text(finding_file_path(entry))
    rule_id = _identity_text(entry.get("rule_id") or entry.get("rule_applied"))
    line = finding_line_no(entry) or None
    if not filepath or not rule_id or line is None:
        return None
    return "location", filepath, line, rule_id
def _location_paths_match(left: str, right: str) -> bool:
    left = finding_file_key(left)
    right = finding_file_key(right)
    if left == right:
        return True
    left_absolute = os.path.isabs(left)
    right_absolute = os.path.isabs(right)
    if left_absolute == right_absolute:
        return False
    return left.endswith("/" + right) or right.endswith("/" + left)
def _identities_overlap(left: set[tuple], right: set[tuple]) -> bool:
    left_locations = {item for item in left
                      if item and item[0] == "location"}
    right_locations = {item for item in right
                       if item and item[0] == "location"}
    if left_locations and right_locations:
        return bool(left & right) or any(
            _location_paths_match(a[1], b[1]) and a[2:] == b[2:]
            for a in left_locations for b in right_locations
        )
    return bool(left & right)
def _finding_identities(entry) -> set[tuple]:
    if not isinstance(entry, dict):
        return set()
    identities = {
        (kind, token)
        for key, kind in (("locator", "locator"), ("finding_id", "finding_id"))
        if (token := _identity_text(entry.get(key)))
    }
    location = _location_identity(entry)
    if location is not None:
        identities.add(location)
    return identities
def _entry_identities(entry) -> set[tuple]:
    identities = _finding_identities(entry)
    if not isinstance(entry, dict):
        return identities
    findings = entry.get("findings")
    if isinstance(findings, list):
        for finding in findings:
            identities.update(_finding_identities(finding))
    return identities
def _llm_downgraded_identities(refined: list) -> set[tuple]:
    identities: set[tuple] = set()
    for entry in _dict_entries(refined):
        if (entry.get("_llm_verified")
                and not _is_confirmed_conclusion(entry)):
            identities.update(_entry_identities(entry))
    return identities
def _confirmed_channel_identities(channel: list) -> tuple[set[tuple], set[int]]:
    identities: set[tuple] = set()
    object_ids: set[int] = set()
    for finding in channel:
        if isinstance(finding, dict):
            identities.update(_entry_identities(finding))
            object_ids.add(id(finding))
    return identities, object_ids
def _sync_confirmed_channel_after_llm(cv_report: dict, refined: list) -> int:
    channel = cv_report.get("confirmed_findings")
    if not isinstance(channel, list):
        return 0
    downgraded = _llm_downgraded_identities(refined)
    if downgraded:
        kept = [
            finding for finding in channel
            if not _identities_overlap(
                _entry_identities(finding), downgraded)
        ]
        removed = len(channel) - len(kept)
        if removed:
            cv_report["confirmed_findings"] = channel = kept
            logger.info("[Stage2b] LLM降级条目从确认通道移除: %d 条", removed)
    seen_identities, seen_ids = _confirmed_channel_identities(channel)
    appended = 0
    for entry in _confirmed_entries(refined):
        batch: list = []
        _flatten_confirmed_entry(entry, batch)
        for finding in batch:
            identities = _entry_identities(finding)
            if (id(finding) in seen_ids
                    or _identities_overlap(identities, seen_identities)):
                continue
            channel.append(finding)
            seen_ids.add(id(finding))
            seen_identities.update(identities)
            appended += 1
    return appended
def materialize_confirmed_channel(cv_report: dict) -> list:
    derived: list = []
    for entry in _confirmed_entries(cv_report.get("findings_index")):
        _flatten_confirmed_entry(entry, derived)
    return derived
def _source_from_code_contexts(code_contexts: dict[str, str] | None,
                               filepath: str,
                               base_dir: str | None) -> str | None:
    if not isinstance(code_contexts, dict):
        return None
    direct = code_contexts.get(filepath)
    if isinstance(direct, str):
        return direct
    target = finding_file_key(_resolve_disk_path(filepath, base_dir))
    matched_sources: set[str] = set()
    for candidate_path, source in code_contexts.items():
        if not isinstance(candidate_path, str) or not isinstance(source, str):
            continue
        if (not base_dir and os.path.isabs(candidate_path)
                != os.path.isabs(filepath)):
            continue
        candidate = finding_file_key(
            _resolve_disk_path(candidate_path, base_dir))
        if candidate == target:
            matched_sources.add(source)
    return matched_sources.pop() if len(matched_sources) == 1 else None
class LLMCrossValidator:
    FILTER_RULES: ClassVar[dict] = {
        "min_severity": "MEDIUM",
        "require_context": True,
        "skip_rules": ["规则6", "规则7"],
    }
    def __init__(
        self,
        llm_call_fn: Callable | None = None,
        rounds: int | None = None,
        max_calls: int | None = None,
        base_dir: str | None = None,
    ):
        self.llm_call = llm_call_fn or self._default_llm_call
        self.rounds = _LLM_ROUNDS if rounds is None else rounds
        self.max_calls = _LLM_MAX_CALLS if max_calls is None else max_calls
        self.base_dir = os.path.abspath(base_dir) if base_dir else None
        self._call_count = 0
    def filter(
        self,
        xv_findings: list[dict[str, Any]],
        code_contexts: dict[str, str] | None = None,
    ) -> list[dict[str, Any]]:
        self._call_count = 0
        for finding in xv_findings:
            if isinstance(finding, dict):
                for key in _LLM_OUTCOME_FIELDS:
                    finding.pop(key, None)
        return [self._refine_one(finding, code_contexts)
                for finding in xv_findings]
    def _refine_one(self, finding, code_contexts: dict[str, str] | None):
        if not isinstance(finding, dict):
            return finding
        if _conclusion_text(
                finding.get("conclusion")) not in _LLM_REFINABLE_CONCLUSIONS:
            return finding
        if not self._should_process(finding):
            return finding
        if self._call_count >= self.max_calls:
            logger.info("LLM budget exhausted, skipping remaining findings")
            return finding
        code_snippet = self._extract_context(finding, code_contexts)
        if not code_snippet and self.FILTER_RULES["require_context"]:
            return finding
        final = self._aggregate(self._run_rounds(finding, code_snippet))
        self._apply_verdict(finding, final)
        return finding
    def _apply_verdict(self, finding: dict[str, Any],
                       final: dict[str, Any]) -> None:
        if final["verdict"] == "confirmed":
            finding["conclusion"] = "confirmed"
            finding["conclusion_v2"] = "confirmed"
            finding["_llm_upgraded"] = True
            self._mark_llm_verified(finding, final)
        elif final["verdict"] == "suppressed":
            _was_suppressed = (
                _conclusion_text(finding.get("conclusion")) == "suppressed")
            finding["conclusion"] = "suppressed"
            finding["conclusion_v2"] = "suppressed"
            if _was_suppressed:
                finding["_llm_suppression_affirmed"] = True
            else:
                finding["_llm_downgraded"] = True
            self._mark_llm_verified(finding, final)
        else:
            disagreement = final.get("disagreement", [])
            finding["_llm_disagreement"] = disagreement
            finding["_llm_reasoning"] = (
                "多轮推理分歧，保留原结论（investigated/suppressed/review/reviewed）"
                if disagreement else
                f"LLM 复核有效轮次不足，保留原结论（{final.get('reasoning', '')}）")
            finding["_llm_uncertain"] = True
    @staticmethod
    def _mark_llm_verified(finding: dict[str, Any], final: dict[str, Any]) -> None:
        finding["_llm_vote_confidence"] = final.get("confidence", 0.7)
        finding["_llm_verified"] = True
        finding["_llm_reasoning"] = final.get("reasoning", "")
    def _should_process(self, finding: dict[str, Any]) -> bool:
        rank = normalize_severity_rank(str(finding.get("severity", "P3")))
        min_rank = normalize_severity_rank(
            self.FILTER_RULES["min_severity"])
        if rank > min_rank:
            return False
        rule = str(
            finding.get("rule_applied") or finding.get("rule_id") or "")
        return not any(
            re.search(rf"{re.escape(skip)}(?!\d)", rule)
            for skip in self.FILTER_RULES["skip_rules"]
        )
    def _extract_context(
        self, finding: dict[str, Any],
        code_contexts: dict[str, str] | None,
    ) -> str | None:
        target = self._resolve_target(finding)
        if target is None:
            return None
        filepath, line = target
        source = self._resolve_source(filepath, code_contexts, self.base_dir)
        if not source:
            return None
        return self._build_snippet(source, line)
    @staticmethod
    def _resolve_target(finding: dict[str, Any]) -> tuple[str, int] | None:
        filepath = finding_file_path(finding)
        if not filepath:
            locator = finding.get("locator")
            filepath = (parse_locator_file(locator)
                        if isinstance(locator, str) else "")
        if not filepath:
            return None
        line = finding_line_no(finding) or None
        if line is None:
            return None
        return filepath, line
    @staticmethod
    def _resolve_source(filepath: str,
                        code_contexts: dict[str, str] | None,
                        base_dir: str | None = None) -> str | None:
        source = _source_from_code_contexts(
            code_contexts, filepath, base_dir)
        disk_path = _resolve_disk_path(filepath, base_dir)
        if not source and os.path.isfile(disk_path):
            try:
                source = read_source_text(disk_path)
            except Exception as e:  # noqa: BLE001
                log_swallowed(
                    __name__, e, context='_resolve_source:read')
                source = None
            if source is None:
                logger.warning("[CrossVal] 提取上下文失败,返回None: %s", filepath)
        return source or None
    @staticmethod
    def _build_snippet(source: str, line: int) -> str:
        lines = source.splitlines()
        if not lines or not 1 <= line <= len(lines):
            return ""
        start = max(0, line - 4)
        end = min(len(lines), line + 3)
        snippet_lines = []
        for i in range(start, end):
            prefix = ">>>" if i + 1 == line else "   "
            snippet_lines.append(f"{prefix} {i+1}: {lines[i]}")
        return "\n".join(snippet_lines)
    def _run_rounds(self, finding: dict[str, Any],
                    code_snippet: str) -> list[dict[str, Any]]:
        verdicts = []
        for i in range(self.rounds):
            if self._call_count >= self.max_calls:
                break
            prompt = self._build_prompt(finding, code_snippet)
            try:
                result = self.llm_call(prompt)
                if isinstance(result, str):
                    result = json.loads(result)
                if not isinstance(result, dict):
                    result = {"verdict": "uncertain",
                              "reasoning": f"non-dict llm result: {type(result).__name__}"}
                verdicts.append(result)
            except Exception as e:  # noqa: BLE001
                logger.warning("LLM round %d failed: %s", i + 1, e)
                verdicts.append({"verdict": "uncertain", "reasoning": str(e)})
            self._call_count += 1
        return verdicts
    @staticmethod
    def _default_llm_call(_prompt: str) -> str:
        return json.dumps({
            "verdict": "uncertain",
            "reasoning": "no llm_call_fn injected",
        })
    def _aggregate(self, verdicts: list[dict[str, Any]]) -> dict[str, Any]:
        if not verdicts:
            return {
                "verdict": "uncertain", "confidence": 0.0,
                "reasoning": "无有效验证轮次", "disagreement": [],
            }
        counts, reasoning_by_verdict = self._tally_verdicts(verdicts)
        total = len(verdicts)
        majority_verdict, majority_count = counts.most_common(1)[0]
        if (majority_verdict in _DECIDABLE_VERDICTS
                and majority_count * 2 > self.rounds):
            confidence = round(
                0.5 + 0.5 * (majority_count / max(total, self.rounds)), 3)
            merged_reasoning = " | ".join(
                reasoning_by_verdict[majority_verdict])[:500]
            return {
                "verdict": majority_verdict,
                "confidence": confidence,
                "reasoning": merged_reasoning,
                "disagreement": [],
            }
        if len(counts) == 1 and total < self.rounds:
            reason = (f"{total}/{self.rounds} 轮有效结论不足，"
                      f"未达 {self.rounds} 轮多数决要求({dict(counts)})")
        elif len(counts) == 1:
            reason = f"{total} 轮均为不可判定结论({dict(counts)})"
        else:
            reason = f"{total} 轮结论分歧({dict(counts)})，多数决不可达"
        disagreement = (self._disagreement_rows(counts, reasoning_by_verdict)
                        if len(counts) > 1 else [])
        return {
            "verdict": "uncertain",
            "confidence": 0.0,
            "reasoning": reason,
            "disagreement": disagreement,
        }
    @staticmethod
    def _tally_verdicts(verdicts: list[dict]) -> tuple[Counter, dict]:
        counts: Counter = Counter()
        reasoning_by_verdict: dict[str, list[str]] = defaultdict(list)
        for v in verdicts:
            verdict = str(v.get("verdict", "uncertain")).strip().lower()
            if verdict not in _VERDICTS:
                verdict = "uncertain"
            counts[verdict] += 1
            reason = str(v.get("reasoning", ""))
            if reason:
                reasoning_by_verdict[verdict].append(reason)
        return counts, reasoning_by_verdict
    @staticmethod
    def _disagreement_rows(counts: Counter, reasoning_by_verdict: dict) -> list:
        return [
            {
                "verdict": verdict,
                "count": count,
                "reasoning": " | ".join(
                    reasoning_by_verdict[verdict])[:200],
            }
            for verdict, count in counts.most_common()
        ]
    @staticmethod
    def _finding_message(finding: dict[str, Any]) -> str:
        msg = finding.get("message")
        if isinstance(msg, str) and msg:
            return msg
        sample = finding.get("sample_finding")
        if isinstance(sample, dict):
            sample_msg = sample.get("message")
            if isinstance(sample_msg, str) and sample_msg:
                return sample_msg
        return ""
    def _build_prompt(self, finding: dict[str, Any],
                      code_snippet: str) -> str:
        return f"""# 代码片段
```
{code_snippet}
```

# 诊断发现
规则: {finding.get("rule_applied") or finding.get("rule_id") or "unknown"}
问题描述: {self._finding_message(finding)}
严重程度: {finding.get("severity", "P3")}

# 判断要求
请从以下角度分析该代码是否确实存在上述问题：
1. 该代码片段是否真实存在描述中的缺陷？(yes/no/uncertain)
2. 如果是，危害程度如何？(high/medium/low)
3. 如果否，请说明为什么规则可能会误报。
4. 请给出你的推理链。

请严格按以下 JSON 格式输出，不要包含其他内容：
{{"verdict": "confirmed|suppressed|uncertain", "severity": "high|medium|low", "reasoning": "..."}}
"""
def _resolve_disk_path(filepath: str, base_dir: str | None) -> str:
    if os.path.isabs(filepath) or not base_dir:
        return filepath
    return os.path.join(base_dir, filepath)
def _llm_before_snapshot(findings_index: list) -> list:
    return [
        {"locator": _f.get("locator"), "file": finding_file_path(_f),
         "line": _f.get("line"),
         "lineno": _f.get("lineno"),
         "start_line": _f.get("start_line"),
         "rule_id": _f.get("rule_id"),
         "rule_family": _f.get("rule_family"),
         "rule_applied": _f.get("rule_applied"),
         "severity": _f.get("severity"),
         "sources": _f.get("sources"),
         "conclusion": _f.get("conclusion"),
         "conclusion_v2": _f.get("conclusion_v2"),
         "findings": _f.get("findings"),
         "confidence": _f.get("confidence"),
         "message": _f.get("message"),
         "code_context": _f.get("code_context")}
        if isinstance(_f, dict) else _f
        for _f in findings_index
    ]
def _llm_refine_stats(refined: list) -> dict:
    stats = Counter()
    for finding in _dict_entries(refined):
        verified = bool(finding.get("_llm_verified"))
        processed = bool(verified or finding.get("_llm_uncertain"))
        stats["processed"] += int(processed)
        stats["upgraded"] += int(
            verified and finding.get("conclusion") == "confirmed")
        stats["downgraded"] += int(bool(finding.get("_llm_downgraded")))
        stats["uncertain"] += int(bool(
            finding.get("_llm_disagreement")
            or finding.get("_llm_uncertain")))
    return {key: stats[key]
            for key in ("processed", "upgraded", "downgraded", "uncertain")}

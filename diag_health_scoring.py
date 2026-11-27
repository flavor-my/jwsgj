from __future__ import annotations

import logging
import math
import os
import re
import types
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any

from jwsgj.diag_detector_findings import normalize_severity
from jwsgj.diag_guard_injection_enforce import supplement_cie_sections
from jwsgj.diag_health_profile import (
    _call_depth_measured,
    apply_baseline_comparison,
    blindspot_total,
    compute_comment_ratio,
    record_degradation,
    score_test_coverage_ratio,
    supplement_graph_report_dimensions,
)
from jwsgj.diag_module_topology import (
    detect_skill_type,
    skill_type_name,
)
from jwsgj.diag_structure_arch import (
    analyze_export_consistency,
    analyze_facade_reachability,
    analyze_fragmentation,
    analyze_module_coupling,
    analyze_structural_health,
)
from jwsgj.diag_types_normalize import (
    append_judgment,
    append_recommendation_once,
    dict_items,
    float_metric,
    int_metric,
    int_or,
    method_status_bucket,
    normalize_list_field,
    num,
    ratio01,
    recommendations_list,
    safe_float,
    section_dict,
    severity_penalty_weight,
    strict_iterable_list,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    CAT_DYNAMIC_BINDING,
    CAT_MAINTAINABILITY,
    FIELD_RECOMMENDATIONS,
    FIELD_TOTAL_FUNCTIONS,
    FINDING_KEY_ALIASES,
)
from jwsgj.diag_warning_quality import (
    detect_warning_cascades,
    run_warning_quality_analysis,
)
from jwsgj.diag_wiring_import_scan import (
    detect_import_bloat,
)
from jwsgj.log_config import log_swallowed

__all__ = [
    'BLOCK_THRESHOLD',
    'CRITICAL_THRESHOLD',
    'QUALITY_DIMENSION_WEIGHTS',
    'QUALITY_GATES',
    'SEVERITY_DEDUCTION',
    'analyze_technical_debt',
    'append_core_judgments',
    'apply_health_report',
    'build_health_report',
    'build_quality_projection',
    'calculate_quality_score',
    'compute_bayesian_posterior',
    'compute_health_score',
    'generate_core_recommendations',
    'generate_quality_insights',
    'quantify_quality',
    'structural_health_component',
    'supplement_structure_dimensions',
    'supplement_warning_section',
]
logger = logging.getLogger(__name__)
logger.info("diag_health_scoring 健康评分与核心裁决域已加载: %d 项导出", len(__all__))
def _nonneg_int(section, key, default: int = 0) -> int:
    return max(0, int(num(section, key, default)))
def _step_penalty(value: float, steps: tuple[tuple[float, int], ...]) -> int:
    for threshold, penalty in steps:
        if value > threshold:
            return penalty
    return 0
def _score_api_surface(report: dict) -> int:
    penalty = 0
    bf_data = section_dict(report, "business_flows", {})
    api_surface = bf_data.get("api_surface", {})
    if isinstance(api_surface, dict) and num(api_surface, "total_apis") > 0:
        avg_quality = num(api_surface, "avg_quality", 100)
        total_apis = max(1, _nonneg_int(api_surface, "total_apis", 1))
        ready = _nonneg_int(api_surface, "ready")
        ready_ratio = ratio01(ready / max(total_apis, 1))
        if avg_quality < 30:
            penalty = 5
        elif avg_quality < 50:
            penalty = 3
        elif avg_quality < 70:
            penalty = 1
        if penalty > 0:
            append_judgment(
                report, "api_surface_quality",
                "warn" if penalty >= 3 else "info",
                f"API surface quality: avg={avg_quality:.1f}/100, "
                f"ready={ready_ratio * 100:.1f}% "
                f"({ready}/{total_apis})",
            )
        report["api_quality_assessment"] = {
            "avg_quality": avg_quality,
            "ready_ratio": round(ready_ratio, 4),
            "penalty": penalty,
        }
    return penalty
_TRYCERATOPS_WEIGHTS = {
    "try002_raise_vanilla_class": 3,
    "try003_raise_vanilla_args": 2,
    "try004_type_check_without_type_error": 2,
    "try201_verbose_raise": 2,
    "try203_useless_try_except": 3,
    "try300_try_consider_else": 1,
    "try301_raise_within_try": 2,
    "try400_error_instead_of_exception": 3,
    "try401_verbose_log_message": 1,
}
_EM_WEIGHTS = {
    "em001_nested_try_in_except": 2,
    "em002_catch_throw_different": 2,
    "em003_empty_catch_with_comment": 3,
    "em004_exception_control_flow": 1,
}
def _pattern_counts(by_pattern) -> dict[str, int]:
    counts: dict[str, int] = {}
    for _p in by_pattern:
        _c = _nonneg_int(by_pattern, _p)
        if isinstance(_p, str) and _c > 0:
            counts[_p] = _c
    return counts
def _weighted_pattern_penalty(counts: dict[str, int],
                              weights: dict[str, int], cap: int) -> int:
    penalty = 0
    for pattern, weight in weights.items():
        penalty += counts.get(pattern, 0) * weight
    return min(cap, penalty)
@dataclass(frozen=True)
class _PatternFamilySpec:
    section_key: str
    weights: dict[str, int]
    cap: int
    judgment_key: str
    label: str
    suffix: str
    prefix_of: Callable[[str], str]
    warn_floor: int | None
_TRYCERATOPS_SPEC = _PatternFamilySpec(
    section_key="tryceratops",
    weights=_TRYCERATOPS_WEIGHTS,
    cap=20,
    judgment_key="tryceratops_anti_patterns",
    label="Tryceratops anti-patterns:",
    suffix=" found",
    prefix_of=lambda p: p.split('_')[0].upper(),
    warn_floor=6,
)
_EM_SPEC = _PatternFamilySpec(
    section_key="exception_miner",
    weights=_EM_WEIGHTS,
    cap=10,
    judgment_key="exception_miner_patterns",
    label="Exception Miner:",
    suffix=" anti-patterns",
    prefix_of=lambda p: p[:5].upper(),
    warn_floor=None,
)
def _pattern_family_penalty(report: dict, metrics: dict,
                            spec: _PatternFamilySpec) -> int:
    section = metrics.get(spec.section_key)
    if not isinstance(section, dict):
        section = {}
    raw = section.get("by_pattern")
    if not isinstance(raw, dict):
        raw = {}
    counts = _pattern_counts(raw)
    penalty = _weighted_pattern_penalty(counts, spec.weights, spec.cap)
    if penalty > 0:
        parts = [f"{spec.prefix_of(p)}:{c}"
                 for p, c in sorted(counts.items()) if c]
        level = ("warn" if (spec.warn_floor is None or penalty >= spec.warn_floor)
                 else "info")
        append_judgment(
            report, spec.judgment_key, level,
            f"{spec.label} {_nonneg_int(section, 'total')}{spec.suffix}"
            f" ({' '.join(parts)})",
        )
    return penalty
def _hs_score_exception_antipatterns(report: dict) -> int:
    metrics = section_dict(report, "exception_metrics", {})
    penalty = 0
    tc_penalty = _pattern_family_penalty(report, metrics, _TRYCERATOPS_SPEC)
    penalty += tc_penalty
    em_penalty = _pattern_family_penalty(report, metrics, _EM_SPEC)
    penalty += em_penalty
    if penalty > 0:
        report["exception_antipattern_assessment"] = {
            "tryceratops_penalty": tc_penalty,
            "exception_miner_penalty": em_penalty,
            "penalty": penalty,
        }
    return penalty
def _hs_score_breakpoints(report, is_library) -> tuple[int, int]:
    cc = section_dict(report, "call_chain")
    if not cc:
        return 0, 0
    bp = _nonneg_int(cc, "break_points")
    bp_details = cc.get("break_point_details", [])
    if not isinstance(bp_details, list):
        bp_details = []
    info_bp = sum(
        1 for b in bp_details
        if isinstance(b, dict)
        and str(b.get("severity") or "").strip().lower() == "info")
    effective_bp = max(0, bp - info_bp) if is_library else bp
    bp_penalty = min(30, effective_bp * 10)
    if is_library:
        bp_penalty = bp_penalty // 2
    return bp_penalty, effective_bp
def _hs_blindspots_skipped_judgment(report, rw) -> None:
    _skipped = _nonneg_int(rw, "skipped_external_api")
    if _skipped > 0:
        _label_parts = [f"跳过 {_skipped} 个 external_api"]
        _unknown = _nonneg_int(rw, "unknown_retained")
        if _unknown > 0:
            _label_parts.append(f"保留 {_unknown} 个 unknown（20%惩罚）")
        append_judgment(
            report, "external_api_skipped", "info",
            f"评分优化: {', '.join(_label_parts)}（库型 external_api 豁免）",
        )
def _blindspot_severity_is_adjusted(bs: dict) -> bool:
    adjusted = bs.get("by_severity_adjusted")
    return isinstance(adjusted, dict) and bool(adjusted)
def _blindspot_severity_source(bs: dict) -> dict:
    if _blindspot_severity_is_adjusted(bs):
        return bs["by_severity_adjusted"]
    raw = bs.get("by_severity")
    return raw if isinstance(raw, dict) else {}
def _blindspot_external_api_count(bs: dict) -> int:
    raw = int_metric(bs.get("external_api_count"), -1)
    if raw >= 0:
        return raw
    return int_metric(section_dict(bs, "by_confidence", {}).get("external_api"))
def _blindspot_severity_penalty(bs: dict) -> float:
    sev = _blindspot_severity_source(bs)
    return (
        max(0, num(sev, "critical")) * 10
        + max(0, num(sev, "high")) * 5
        + max(0, num(sev, "medium")) * 2
        + max(0, num(sev, "low")) * 1
    )
def _blindspot_confidence_factor(bs: dict) -> float:
    if _blindspot_severity_is_adjusted(bs):
        return 1.0
    external_api = max(0, _blindspot_external_api_count(bs))
    total = max(blindspot_total(bs) or 0, 1)
    return ratio01(1.0 - external_api / total)
def _blindspot_effective_total(bs: dict) -> int:
    total = blindspot_total(bs) or 0
    if "effective_total" in bs:
        return int_metric(bs.get("effective_total"), total)
    return total
def _blindspot_library_factor(bs: dict, is_library: bool) -> float:
    if not is_library:
        return _DEFAULT_LIB_FACTOR
    by_level = section_dict(bs, "by_level", {})
    total = max(blindspot_total(bs) or 0, 1)
    func_ratio = max(0, num(by_level, "function")) / total
    code_ratio = max(0, num(by_level, "code")) / total
    return max(0.2, 1.0 - func_ratio * 0.9 - code_ratio * 0.7)
def _blindspot_mi_scale(report: dict) -> float:
    total_funcs = num(
        section_dict(report, "call_chain", {}), FIELD_TOTAL_FUNCTIONS, 0)
    if total_funcs <= 0:
        return 1.0
    return 3.0 / max(0.5, math.log10(max(total_funcs, 2)))
_BLINDSPOT_PENALTY_CAP = 40
_DEFAULT_LIB_FACTOR = 1.0
@dataclass(frozen=True)
class _BlindspotCalibration:
    mi_scale: float
    lib_factor: float
    skill_dir: str
    ctx: Any
def _blindspot_reliability_penalty(report: dict, rw: dict,
                                   calibration: _BlindspotCalibration
                                   ) -> tuple[int, float]:
    weighted_penalty = max(0.0, num(rw, "weighted_penalty", 0.0))
    scaled_penalty = min(float(_BLINDSPOT_PENALTY_CAP),
                         weighted_penalty * calibration.mi_scale)
    if num(rw, "high_complexity_count") > 0:
        scaled_penalty = min(float(_BLINDSPOT_PENALTY_CAP),
                             scaled_penalty * 1.2)
    if (scaled_penalty > 0
            and compute_comment_ratio(calibration.skill_dir,
                                     calibration.ctx) > 0.15):
        scaled_penalty = min(float(_BLINDSPOT_PENALTY_CAP),
                             scaled_penalty * 1.1)
    penalty_raw = int(scaled_penalty * calibration.lib_factor)
    _hs_blindspots_skipped_judgment(report, rw)
    return penalty_raw, scaled_penalty
def _hs_score_blindspots(report, skill_dir, ctx, is_library) -> tuple[int, int, float, float]:
    bs = section_dict(report, "blindspots")
    if not bs:
        return 0, 0, 0.0, _DEFAULT_LIB_FACTOR
    issues = _blindspot_effective_total(bs)
    lib_factor = _blindspot_library_factor(bs, is_library)
    if "effective_total" in bs and issues == 0:
        return 0, 0, 0.0, lib_factor
    mi_scale = _blindspot_mi_scale(report)
    rw = bs.get("reliability_weighted")
    if isinstance(rw, dict) and num(rw, "reliability_entries") > 0:
        penalty_raw, weighted_penalty = _blindspot_reliability_penalty(
            report, rw, _BlindspotCalibration(mi_scale, lib_factor,
                                              skill_dir, ctx))
        return penalty_raw, issues, weighted_penalty, lib_factor
    weighted_penalty = (min(_BLINDSPOT_PENALTY_CAP,
                            _blindspot_severity_penalty(bs) * mi_scale)
                        * _blindspot_confidence_factor(bs))
    return (int(weighted_penalty * lib_factor), issues,
            weighted_penalty, lib_factor)
_SYNTAX_ERROR_SEQUENCES = (list, tuple, set, frozenset)
def normalize_syntax_error_count(value) -> int:
    if isinstance(value, (str, bytes, bytearray)):
        return 0
    if isinstance(value, _SYNTAX_ERROR_SEQUENCES):
        return len(value)
    return max(0, int_metric(value, -1))
def _hs_score_syntax_errors(report) -> int:
    se = normalize_syntax_error_count(
        section_dict(report, "call_chain", {}).get("syntax_errors", 0))
    return min(20, se * 20)
def _hs_score_module_coupling(report, is_library) -> int:
    mc = section_dict(report, "module_coupling")
    if not mc:
        return 0
    cycles = _nonneg_int(mc, "cycles")
    isolated = _nonneg_int(mc, "isolated_modules")
    total_mods = max(_nonneg_int(mc, "total_modules", 1), 1)
    isolated_ratio = isolated / total_mods
    penalty = min(10, cycles * 5)
    if is_library:
        if isolated_ratio > 0.5:
            penalty += min(10, (isolated - int(total_mods * 0.3)) * 3)
    else:
        penalty += min(10, isolated * 5)
    return penalty
def _fragmentation_counts(fr: dict) -> tuple[int, int, float]:
    small_files = max(0, int_metric(fr.get("small_files")))
    readable = max(0, int_metric(fr.get("readable_files")))
    denom = max(readable or int_metric(fr.get("total_files")), 1)
    return small_files, denom, small_files / denom
def _hs_score_fragmentation(report) -> int:
    fr = section_dict(report, "fragmentation")
    if not fr:
        return 0
    _small_files, _denom, small_ratio = _fragmentation_counts(fr)
    return _step_penalty(small_ratio, ((0.5, 10), (0.3, 5), (0.15, 2)))
_DEEP_CHAIN_WARN_DEPTH = 8
_DEEP_CHAIN_MID_DEPTH = 10
_DEEP_CHAIN_EXTREME_DEPTH = 12
def _append_depth_unmeasured_judgment(report: dict, cd: dict) -> int:
    return int(append_judgment(
        report, "call_depth", "info",
        "Call depth not measured: "
        f"{cd.get('reason') or 'invalid call graph'}"))
def _hs_score_call_depth(report, is_library) -> int:
    cd = section_dict(report, "call_depth")
    if not cd or is_library:
        return 0
    if not _call_depth_measured(cd):
        _append_depth_unmeasured_judgment(report, cd)
        return 0
    depth_score = num(cd, "depth_score", 0.0)
    max_depth = num(cd, "max_depth")
    return max(
        _step_penalty(depth_score, ((0.7, 10), (0.5, 6), (0.3, 3))),
        _step_penalty(max_depth, ((_DEEP_CHAIN_EXTREME_DEPTH, 8),
                                  (_DEEP_CHAIN_MID_DEPTH, 5),
                                  (_DEEP_CHAIN_WARN_DEPTH, 2))),
    )
def _hs_score_simulation(report) -> int:
    sim = section_dict(report, "simulation")
    if not sim:
        return 0
    total = max(0, num(sim, "executed"))
    failed = max(0, num(sim, "failed"))
    if total <= 0:
        return 0
    fail_rate = failed / total
    return _step_penalty(fail_rate, ((0.8, 15), (0.5, 10), (0.2, 5), (0.1, 2)))
def _hs_score_resource_leaks(report) -> int:
    resource_leaks = section_dict(report, "resource_leaks", {})
    if not resource_leaks:
        return 0
    rl_total = _nonneg_int(resource_leaks, "total")
    rl_penalty = min(10, rl_total * 2)
    if rl_penalty > 0:
        append_judgment(
            report, "resource_leak_score",
            "warn" if rl_penalty >= 5 else "info",
            f"Resource leak penalty: -{rl_penalty}pts ({rl_total} potential leaks)",
        )
    return rl_penalty
_DIAG_ERROR_PENALTY_STEPS = ((5, 10), (2, 5), (0, 2))
def _diag_error_count_penalty(error_count: int) -> int:
    return _step_penalty(error_count, _DIAG_ERROR_PENALTY_STEPS)
def _hs_score_diag_errors(report) -> int:
    error_count = len(normalize_list_field(report.get("errors")))
    return _diag_error_count_penalty(error_count)
def _reconcile_late_diag_errors(report: dict, scored_error_count: int) -> bool:
    current_count = len(normalize_list_field(report.get("errors")))
    additional_penalty = (
        _diag_error_count_penalty(current_count)
        - _diag_error_count_penalty(scored_error_count))
    if additional_penalty <= 0:
        return False
    report["health_score"] = max(
        0, report["health_score"] - additional_penalty)
    return True
def _hs_score_facade_reachability(report: dict, skill_dir: str, is_library: bool, ctx=None) -> int:
    if not is_library:
        return 0
    metrics = analyze_facade_reachability(skill_dir, ctx)
    total_mods = int_metric(metrics.get("total_modules"))
    if total_mods <= 5:
        return 0
    unreachable_mods = int_metric(metrics.get("unreachable_modules"))
    unreachable_ratio = float_metric(metrics.get("unreachable_ratio"))
    penalty = _step_penalty(
        unreachable_ratio, ((0.5, 5), (0.3, 3), (0.15, 1)))
    if penalty > 0:
        append_judgment(
            report, "facade_reachability", "warn",
            f"Facade reachability: {unreachable_mods}/{total_mods} modules "
            f"({unreachable_ratio * 100:.1f}%) unreachable",
        )
    report["facade_reachability"] = {
        "total_modules": total_mods,
        "reachable_modules": int_metric(metrics.get("reachable_modules")),
        "unreachable_modules": unreachable_mods,
        "unreachable_ratio": round(unreachable_ratio, 4),
        "unreachable_names": list(metrics.get("unreachable_names") or ()),
        "penalty": penalty,
    }
    return penalty
def _hs_score_all_consistency(report: dict, skill_dir: str, ctx=None) -> int:
    metrics = analyze_export_consistency(skill_dir, ctx)
    if not metrics:
        return 0
    total_exported = int_metric(metrics.get("total_exported"))
    raw_in_all = metrics.get("in_all")
    raw_mismatch = metrics.get("mismatch_ratio")
    if raw_in_all is None or raw_mismatch is None:
        report["all_consistency"] = {
            "total_exported": total_exported,
            "in_all": None,
            "mismatch_ratio": None,
            "penalty": 0,
        }
        return 0
    in_all = int_metric(raw_in_all)
    mismatch_ratio = float_metric(raw_mismatch)
    penalty = (_step_penalty(mismatch_ratio, ((0.95, 3), (0.8, 2)))
               if total_exported > 20 else 0)
    if penalty:
        append_judgment(
            report, "all_consistency", "warn" if penalty >= 3 else "info",
            f"__all__ mismatch: {in_all}/{total_exported} "
            f"({mismatch_ratio * 100:.1f}% undeclared)",
        )
    report["all_consistency"] = {
        "total_exported": total_exported,
        "in_all": in_all,
        "mismatch_ratio": round(mismatch_ratio, 4),
        "penalty": penalty,
    }
    return penalty
def compute_bayesian_posterior(report: dict) -> dict:
    skill_type = skill_type_name(report)
    prior, baseline, baseline_valid, delta = _bayesian_prior(report, skill_type)
    likelihood, phase2_rej, phase3_rej, total = (
        _bayesian_base_likelihood(report))
    evidence_sources = _bayesian_evidence_sources(report)
    likelihood = _fuse_evidence_trust(
        likelihood, evidence_sources, baseline_valid, baseline, delta)
    false_positive_rate = (
        (phase2_rej + phase3_rej) / total if total > 0 else 0.3
    )
    p_evidence = likelihood * prior + false_positive_rate * (1 - prior)
    posterior = likelihood * prior / p_evidence if p_evidence > 0 else prior
    adjustment, verdict = _confidence_for(posterior)
    logger.info(
        "[Bayesian] compute_bayesian_posterior: skill_type=%s prior=%.2f "
        "likelihood=%.2f posterior=%.2f verdict=%s evidence_sources=%s",
        skill_type, prior, likelihood, posterior, verdict,
        evidence_sources or "none")
    return {
        "prior": round(prior, 4),
        "likelihood": round(likelihood, 4),
        "false_positive_rate": round(false_positive_rate, 4),
        "posterior": round(posterior, 4),
        "normalization": round(p_evidence, 4),
        "confidence_adjustment": adjustment,
        "model_verdict": verdict,
        "evidence_sources": evidence_sources,
        "skill_type": skill_type,
    }
_DEFAULT_BAYESIAN_PRIOR = 0.30
_BAYESIAN_PRIORS = {
    "library": 0.25,
    "cli": 0.35,
    "hybrid": _DEFAULT_BAYESIAN_PRIOR,
    "unknown": _DEFAULT_BAYESIAN_PRIOR,
}
def _bayesian_prior(report: dict, skill_type: str) -> tuple:
    prior = _BAYESIAN_PRIORS.get(skill_type, _DEFAULT_BAYESIAN_PRIOR)
    baseline = report.get("baseline")
    baseline_valid = (isinstance(baseline, dict)
                      and baseline.get("previous_score") is not None)
    delta = float_metric(baseline.get("delta", 0)) if baseline_valid else 0.0
    if baseline_valid:
        if delta > 5:
            prior = min(0.6, prior + 0.05)
        elif delta < -5:
            prior = max(0.15, prior - 0.05)
    return prior, baseline, baseline_valid, delta
def _bayesian_base_likelihood(report: dict) -> tuple:
    dp = report.get("dead_code_phases")
    if not isinstance(dp, dict):
        dp = {}
    confirmed = int_metric(dp.get("confirmed", 0))
    phase2_rej = int_metric(dp.get("phase2_rejected", 0))
    phase3_rej = int_metric(dp.get("phase3_rejected", 0))
    total = confirmed + phase2_rej + phase3_rej
    likelihood = confirmed / total if total > 0 else 0.5
    return likelihood, phase2_rej, phase3_rej, total
def _bayesian_evidence_sources(report: dict) -> dict:
    evidence_sources: dict[str, float] = {}
    cv = report.get(CAT_CROSS_VALIDATION, {})
    if isinstance(cv, dict):
        static_total = int_metric(cv.get(FIELD_TOTAL_FUNCTIONS, 0))
        qd = cv.get("quadrant_distribution", {})
        if isinstance(qd, dict) and static_total > 0:
            reachable_count = (
                int_metric(qd.get("active", 0))
                + int_metric(qd.get(CAT_DYNAMIC_BINDING, 0))
                + int_metric(qd.get("undertested", 0))
            )
            evidence_sources["static"] = round(
                ratio01(reachable_count / static_total), 4)
            covered_count = (int_metric(qd.get("active", 0))
                             + int_metric(qd.get(CAT_DYNAMIC_BINDING, 0)))
            evidence_sources["coverage"] = round(
                ratio01(covered_count / static_total), 4)
    return evidence_sources
def _baseline_trust_weights(baseline_valid: bool, baseline: Any,
                            delta: float) -> dict[str, float]:
    weights = {"static": 0.7, "coverage": 0.9}
    if baseline_valid:
        prev_score = float_metric(baseline.get("previous_score"), 80.0)
        if abs(delta) <= 3 and prev_score >= 70:
            weights["static"] = min(0.85, weights["static"] + 0.05)
        elif abs(delta) > 10:
            weights["static"] = max(0.5, weights["static"] - 0.1)
        if delta < -5:
            weights["coverage"] = min(0.95, weights["coverage"] + 0.03)
    return weights
def _fuse_evidence_trust(likelihood: float, evidence_sources: dict,
                          baseline_valid: bool, baseline: Any,
                          delta: float) -> float:
    if not evidence_sources:
        return likelihood
    weights = _baseline_trust_weights(baseline_valid, baseline, delta)
    weighted_sum = sum(
        evidence_sources[k] * weights.get(k, 0.7) for k in evidence_sources
    )
    weight_total = sum(weights.get(k, 0.7) for k in evidence_sources)
    if weight_total <= 0:
        return likelihood
    fused_likelihood = weighted_sum / weight_total
    return (likelihood + fused_likelihood) / 2
def _confidence_for(posterior: float) -> tuple:
    if posterior >= 0.7:
        return 1.0, "reliable"
    if posterior >= 0.4:
        return 0.7, "uncertain"
    return 0.4, "unreliable"
def _bayesian_model_usable(model: Any) -> bool:
    if not isinstance(model, dict):
        return False
    adj = model.get("confidence_adjustment")
    if (isinstance(adj, bool) or not isinstance(adj, (int, float))
            or not 0.0 <= adj <= 1.0):
        return False
    if model.get("model_verdict") not in ("reliable", "uncertain", "unreliable"):
        return False
    posterior = model.get("posterior")
    return (isinstance(posterior, (int, float)) and not isinstance(posterior, bool)
            and 0.0 <= posterior <= 1.0)
def _hs_bayesian_correction(report, weighted_penalty, lib_factor) -> int:
    bayesian = report.get("bayesian_model")
    if not _bayesian_model_usable(bayesian):
        bayesian = compute_bayesian_posterior(report)
        report["bayesian_model"] = bayesian
    verdict = bayesian.get("model_verdict")
    correction_specs = {
        "unreliable": (
            1 - bayesian["confidence_adjustment"],
            "Bayesian correction",
            f", verdict={verdict}",
        ),
        "uncertain": (0.15, "Bayesian correction (uncertain)", ""),
    }
    if weighted_penalty <= 0 or verdict not in correction_specs:
        return 0
    factor, label, verdict_detail = correction_specs[verdict]
    correction = int(min(_BLINDSPOT_PENALTY_CAP, weighted_penalty)
                     * lib_factor * factor)
    append_judgment(
        report, "bayesian_correction", "info",
        f"{label}: blindspot penalty reduced by {correction}pts "
        f"(posterior={num(bayesian, 'posterior'):.2f}{verdict_detail})",
    )
    return correction
def _hs_sim_compensation_cap(report, sim_penalty, correction, score) -> int:
    if sim_penalty > 0 and correction > sim_penalty // 2:
        reduced = correction - sim_penalty // 2
        score -= reduced
        _sim = section_dict(report, "simulation", {})
        _sim_failed = _nonneg_int(_sim, "failed")
        _sim_exec = _nonneg_int(_sim, "executed")
        append_judgment(
            report, "sim_compensation_cap", "info",
            f"Simulation compensation cap: Bayesian correction reduced by "
            f"{reduced}pts (sim failed={_sim_failed}/{_sim_exec})",
        )
    return score
def _hs_business_liveness(report, score) -> int:
    _bf_liveness = next(
        (cand for cand in (
            section_dict(report, "business_flows"),
            section_dict(report, "blindspots", {}).get("business_flows"),
        ) if isinstance(cand, dict)
            and num(cand, FIELD_TOTAL_FUNCTIONS) > 0),
        {})
    if _bf_liveness:
        _adj_liveness = num(
            _bf_liveness, "adjusted_liveness_rate",
            num(_bf_liveness, "liveness_rate", 1.0))
        if _adj_liveness < 0.6:
            score -= 5
            append_judgment(
                report, "business_liveness_adjusted", "warn",
                f"Adjusted business liveness: {_adj_liveness * 100:.1f}% (below 60% threshold)",
            )
        elif _adj_liveness < 0.8:
            score -= 3
            append_judgment(
                report, "business_liveness_adjusted", "info",
                f"Adjusted business liveness: {_adj_liveness * 100:.1f}% (below 80%)",
            )
    return score
def _hs_cascade_compensation(report: dict, score: int) -> int:
    try:
        cascades = report.get("warning_cascades")
        if not isinstance(cascades, dict) or "cascade_groups" not in cascades:
            cascades = detect_warning_cascades(report)
            report["warning_cascades"] = cascades
        if cascades["cascade_groups"] <= 0:
            return score
        cascaded_fail_warn = sum(
            1 for cg in cascades.get("details", [])
            for c in cg.get("cascaded", [])
            if c.get("status", "") in ("fail", "critical", "warn")
        )
        refund = min(15, cascaded_fail_warn * 2)
        if refund <= 0:
            return score
        append_judgment(
            report, "cascade_compensation", "info",
            f"Cascade compensation: +{refund}pts "
            f"({cascades['cascaded_warnings']} cascaded warnings deduplicated)",
        )
        return min(100, score + refund)
    except (KeyError, AttributeError, TypeError) as e:
        logger.debug("suppressed [cascade_compensation] "
                     "(KeyError, AttributeError, TypeError): %s", e)
        report["errors"] = normalize_list_field(report.get("errors"))
        report["errors"].append(
            {"step": "cascade_compensation", "error": str(e)})
        return score
def _hs_dimension_penalties(report, skill_dir, ctx, is_library) -> tuple[int, int, float, float, int]:
    penalty_total = 0
    issues = 0
    weighted_penalty = 0.0
    lib_factor = _DEFAULT_LIB_FACTOR
    _penalty, _issues = _hs_score_breakpoints(report, is_library)
    penalty_total += _penalty
    issues += _issues
    _penalty, _issues, weighted_penalty, lib_factor = _hs_score_blindspots(
        report, skill_dir, ctx, is_library)
    penalty_total += _penalty
    issues += _issues
    penalty_total += _hs_score_syntax_errors(report)
    penalty_total += _hs_score_module_coupling(report, is_library)
    penalty_total += _hs_score_fragmentation(report)
    penalty_total += _hs_score_call_depth(report, is_library)
    sim_penalty = _hs_score_simulation(report)
    penalty_total += sim_penalty
    penalty_total += _hs_score_resource_leaks(report)
    penalty_total += _hs_score_exception_antipatterns(report)
    penalty_total += score_test_coverage_ratio(report, skill_dir, ctx)
    penalty_total += _hs_score_facade_reachability(report, skill_dir, is_library, ctx)
    penalty_total += _hs_score_all_consistency(report, skill_dir, ctx)
    penalty_total += _score_api_surface(report)
    penalty_total += _hs_score_diag_errors(report)
    return penalty_total, issues, weighted_penalty, lib_factor, sim_penalty
def _set_health_verdict(report: dict, skill_name: str, *,
                        has_findings: bool) -> None:
    score = report["health_score"]
    if score >= 80:
        report["status"] = "healthy"
        health_summary = (
            f"{skill_name} is healthy overall, with findings to review."
            if has_findings else f"{skill_name} is healthy, no critical issues found.")
    elif score >= 50:
        report["status"] = "warning"
        health_summary = (
            f"{skill_name} has findings to address."
            if has_findings else f"{skill_name} requires improvement.")
    else:
        report["status"] = "critical"
        health_summary = (
            f"{skill_name} has critical findings; immediate action required."
            if has_findings else f"{skill_name} is critical; immediate action required.")
    report["health_summary"] = health_summary
def compute_health_score(skill_dir: str, report: dict, ctx: Any = None) -> dict:
    report["errors"] = normalize_list_field(report.get("errors"))
    scored_error_count = len(report["errors"])
    skill_type_label = skill_type_name(report)
    is_library = skill_type_label == "library"
    _penalty_total, issues, weighted_penalty, lib_factor, sim_penalty = (
        _hs_dimension_penalties(report, skill_dir, ctx, is_library))
    score = 100 - _penalty_total
    correction = _hs_bayesian_correction(report, weighted_penalty, lib_factor)
    score += correction
    score = _hs_sim_compensation_cap(report, sim_penalty, correction, score)
    score = _hs_business_liveness(report, score)
    score = max(0, min(100, score))
    score = _hs_cascade_compensation(report, score)
    report["health_score"] = score
    _reconcile_late_diag_errors(report, scored_error_count)
    skill_name = _skill_label(skill_dir)
    judgments = report.get("judgments")
    has_findings = bool(
        issues or _penalty_total > 0 or report["errors"]
        or (isinstance(judgments, list) and any(
            isinstance(j, dict) and j.get("status") not in ("pass", "info")
            for j in judgments)))
    _set_health_verdict(report, skill_name, has_findings=has_findings)
    logger.info(
        "[HealthScore] compute_health_score 完成: skill=%s type=%s "
        "score=%d status=%s primary_issues=%d has_findings=%s",
        skill_name, skill_type_label, report["health_score"], report["status"],
        issues, has_findings)
    return report
def generate_core_recommendations(report: dict) -> list[str]:
    recommendations = recommendations_list(report)
    _added_count = 0
    def _add(text: str) -> None:
        nonlocal _added_count
        if append_recommendation_once(report, text):
            _added_count += 1
    _recommend_call_chain(report, _add)
    _recommend_blindspots(report, _add)
    _recommend_runtime_bindings(report, _add)
    if _added_count:
        logger.info(
            "[Step12] 核心建议生成: %d 条（总 %d 条）",
            _added_count, len(recommendations))
    return recommendations
def _recommend_call_chain(report: dict, add: Callable[[str], None]) -> None:
    cc = section_dict(report, "call_chain")
    if not cc:
        return
    break_points = num(cc, "break_points")
    orphans = num(cc, "orphans")
    if break_points > 0:
        add(f"Fix {int(break_points)} call chain breakpoints")
    if orphans > 0:
        add(f"Review {int(orphans)} orphan functions")
    syntax_errors = normalize_syntax_error_count(cc.get("syntax_errors", 0))
    if syntax_errors > 0:
        add(f"Fix {syntax_errors} syntax errors")
def _recommend_blindspots(report: dict, add: Callable[[str], None]) -> None:
    blindspots = section_dict(report, "blindspots", {})
    total_blindspots = _blindspot_effective_total(blindspots)
    if total_blindspots > 0:
        add(f"Address {total_blindspots} blindspots "
            "(priority: critical > high > medium)")
def _recommend_runtime_bindings(report: dict, add: Callable[[str], None]) -> None:
    observed = section_dict(report, "call_chain", {}).get("binding_observed")
    if not isinstance(observed, dict):
        return
    total_bindings = sum(max(0, int_metric(value))
                         for value in observed.values())
    if total_bindings > 0:
        add(f"Runtime detected {total_bindings} dynamic bindings "
            "(events/registry/decorators) - static analysis would miss these")
def _judgments_view(report: dict) -> list:
    judgments = report.get("judgments")
    return judgments if isinstance(judgments, list) else []
def _is_library_skill(report: dict) -> bool:
    if skill_type_name(report) == "library":
        return True
    for j in _judgments_view(report):
        if not isinstance(j, dict):
            continue
        _st_label = j.get("label")
        if (j.get("key") == "skill_type"
                and isinstance(_st_label, str) and "library" in _st_label):
            return True
    return False
def _blindspot_severity_metrics(bs: dict) -> dict:
    merged_sev = _blindspot_severity_source(bs)
    by_level = bs.get("by_level") or {}
    if not isinstance(by_level, dict):
        by_level = {}
    return {
        "total": blindspot_total(bs) or 0,
        "func_blindspots": int_metric(by_level.get("function")),
        "critical": int_metric(merged_sev.get("critical")),
        "high": int_metric(merged_sev.get("high")),
    }
def _library_blindspot_exemption(metrics: dict) -> tuple:
    total = metrics["total"]
    func_ratio = ratio01(metrics["func_blindspots"] / max(total, 1))
    adjusted_critical = max(0, metrics["critical"] - int(metrics["critical"] * func_ratio))
    adjusted_high = max(0, metrics["high"] - int(metrics["high"] * func_ratio))
    non_func_total = max(0, total - metrics["func_blindspots"])
    return adjusted_critical, adjusted_high, non_func_total
def _blindspot_severity_available(bs: dict) -> bool:
    return any(
        isinstance(bs.get(key), dict) and bs.get(key)
        for key in ("by_severity", "by_severity_adjusted")
    )
def append_blindspot_severity_judgments(report: dict) -> int:
    bs = report.get("blindspots")
    if not isinstance(bs, dict) or not bs:
        return 0
    is_lib = _is_library_skill(report)
    metrics = _blindspot_severity_metrics(bs)
    total = metrics["total"]
    func_blindspots = metrics["func_blindspots"]
    critical = metrics["critical"]
    high = metrics["high"]
    if is_lib:
        adjusted_critical, adjusted_high, non_func_total = (
            _library_blindspot_exemption(metrics))
    else:
        adjusted_critical = critical
        adjusted_high = high
        non_func_total = total
    effective_total = _blindspot_effective_total(bs)
    ext_api_count = _blindspot_external_api_count(bs)
    key, status, label = _blindspot_verdict(_BlindspotEvidence(
        is_lib=is_lib,
        total=total,
        severity_known=_blindspot_severity_available(bs),
        effective_total=effective_total,
        ext_api_count=ext_api_count,
        adjusted_critical=adjusted_critical,
        critical=critical,
        adjusted_high=adjusted_high,
        func_blindspots=func_blindspots,
        non_func_total=non_func_total,
    ))
    return int(append_judgment(report, key, status, label))
@dataclass(frozen=True)
class _BlindspotEvidence:
    is_lib: bool
    total: int
    severity_known: bool
    effective_total: int
    ext_api_count: int
    adjusted_critical: int
    critical: int
    adjusted_high: int
    func_blindspots: int
    non_func_total: int
def _blindspot_verdict(evidence: _BlindspotEvidence) -> tuple:
    if evidence.effective_total == 0:
        if evidence.ext_api_count > 0:
            return ("blindspots_ok", "pass",
                    f"Blindspots: 0 effective ({evidence.ext_api_count} library API exports excluded)")
        return "blindspots_ok", "pass", "Blindspots: 0 effective"
    if not evidence.severity_known and evidence.total > 0:
        return ("blindspots_unknown_severity", "info",
                f"Blindspots: {evidence.total} total (severity breakdown unavailable)")
    if evidence.adjusted_critical > 0:
        label = f"Blindspots: {evidence.adjusted_critical} critical"
        if evidence.is_lib and evidence.critical != evidence.adjusted_critical:
            label += (f" (excluded {evidence.critical - evidence.adjusted_critical} "
                      f"library API funcs)")
        return "blindspots_critical", "fail", label
    if evidence.adjusted_high > 0:
        label = f"Blindspots: {evidence.adjusted_high} high"
        if evidence.is_lib:
            label += (f" (non-function) [{evidence.non_func_total} total non-func, "
                      f"{evidence.func_blindspots} func-level exempted as library APIs]")
        return "blindspots_high", "warn", label
    label = "Blindspots: no high/critical"
    if evidence.is_lib and evidence.func_blindspots > 0:
        label += f" ({evidence.func_blindspots} library API func-level exempted)"
    return "blindspots_ok", "pass", label
def append_coupling_judgments(report: dict) -> int:
    mc = report.get("module_coupling")
    if not isinstance(mc, dict) or not mc:
        return 0
    added = 0
    cycles = int_metric(mc.get("cycles", 0))
    import_edges = int_metric(mc.get("import_edges", 0))
    isolated = int_metric(mc.get("isolated_modules", 0))
    total_modules = max(int_metric(mc.get("total_modules"), 1), 1)
    if cycles > 0:
        added += append_judgment(
            report, "circular_deps", "fail",
            f"Circular dependencies: {cycles} cycles detected")
    if isolated > 0:
        added += append_judgment(
            report, "isolated_modules", "warn",
            f"Isolated modules: {isolated} modules with no deps")
    if import_edges > 0:
        edge_ratio = import_edges / total_modules
        status = "pass" if edge_ratio < 2.0 else ("warn" if edge_ratio < 4.0 else "fail")
        added += append_judgment(
            report, "module_coupling", status,
            f"Module coupling: {import_edges} edges, {edge_ratio:.1f}/module avg")
    return added
def append_fragmentation_judgment(report: dict) -> int:
    fr = report.get("fragmentation")
    if not isinstance(fr, dict) or not fr:
        return 0
    penalty = _hs_score_fragmentation(report)
    if penalty <= 0:
        return 0
    small_files, denom, small_ratio = _fragmentation_counts(fr)
    return int(append_judgment(
        report, "fragmentation", "warn" if penalty >= 5 else "info",
        f"Fragmentation: {small_files}/{denom} files <100 lines ({small_ratio:.0%})"))
def append_skill_type_judgment(report: dict) -> int:
    st = report.get("skill_type")
    if isinstance(st, str) and st:
        return int(append_judgment(
            report, "skill_type", "info",
            f"Skill type: {st} (orphan tolerance: normal)"))
    if not isinstance(st, dict):
        return 0
    ot = st.get("orphan_tolerance", "normal")
    if not isinstance(ot, str) or not ot:
        ot = "normal"
    return int(append_judgment(
        report, "skill_type", "info",
        f"Skill type: {skill_type_name(report)} "
        f"(orphan tolerance: {ot})"))
def _deep_chain_warning(max_depth: int, deep_chain_count: int,
                        skill_type: str) -> str | None:
    if max_depth > _DEEP_CHAIN_EXTREME_DEPTH:
        return f"Call chain extremely deep: max={max_depth}"
    if max_depth > _DEEP_CHAIN_WARN_DEPTH and deep_chain_count > 2:
        return (f"Multiple deep chains: {deep_chain_count} chains "
                f">5 depth, max={max_depth}")
    if max_depth > _DEEP_CHAIN_WARN_DEPTH and skill_type != "library":
        return f"Deep chain unexpected for {skill_type}: max={max_depth}"
    return None
def append_call_depth_judgments(report: dict) -> int:
    cd = report.get("call_depth")
    if not isinstance(cd, dict) or not cd:
        return 0
    if not _call_depth_measured(cd):
        return _append_depth_unmeasured_judgment(report, cd)
    depth_score_val = float_metric(cd.get("depth_score", 0))
    max_depth_val = int_metric(cd.get("max_depth", 0))
    avg_depth_val = float_metric(cd.get("avg_depth", 0))
    _deep_chains = cd.get("deep_chains")
    deep_chain_count = (len(_deep_chains)
                        if isinstance(_deep_chains, (list, tuple, set)) else 0)
    skill_type_label = skill_type_name(report)
    added = 0
    if depth_score_val > 0.5:
        added += append_judgment(
            report, "call_depth", "warn",
            f"Call depth unhealthy: score={depth_score_val:.2f} "
            f"(max={max_depth_val}, avg={avg_depth_val})")
    deep_warning = _deep_chain_warning(
        max_depth_val, deep_chain_count, skill_type_label)
    if deep_warning:
        added += append_judgment(
            report, "call_depth_deep", "warn", deep_warning)
    if added == 0:
        added += append_judgment(
            report, "call_depth", "pass",
            f"Call depth healthy: max={max_depth_val}, avg={avg_depth_val}, "
            f"score={depth_score_val:.2f}")
    return added
def _extract_cv_precision_metrics(report: dict) -> dict | None:
    cv_root = report.get(CAT_CROSS_VALIDATION)
    if isinstance(cv_root, dict):
        _pm = cv_root.get("precision_metrics")
        if isinstance(_pm, dict) and _pm:
            return _pm
        if "confirmed_dead" in cv_root:
            return cv_root
    _bs_root = report.get("blindspots")
    bs_metrics = _bs_root.get("metrics") if isinstance(_bs_root, dict) else None
    if isinstance(bs_metrics, dict):
        _pm = bs_metrics.get(CAT_CROSS_VALIDATION)
        if isinstance(_pm, dict):
            return _pm
    return None
def _cv_library_dead_code_judgment(report: dict, confirmed_dead: int,
                                   external_api_excluded: int) -> int:
    if external_api_excluded > 0:
        if confirmed_dead > 0:
            return append_judgment(
                report, "cv_dead_code",
                "warn" if confirmed_dead > 50 else "info",
                f"Cross-validate: {confirmed_dead} dead code "
                f"(excluded {external_api_excluded} library external APIs)")
        return append_judgment(
            report, "cv_dead_code", "pass",
            f"Cross-validate: 0 dead code "
            f"({external_api_excluded} library external APIs excluded)")
    return append_judgment(
        report, "cv_dead_code", "info",
        f"Cross-validate: {confirmed_dead} unreachable funcs "
        f"(library skill: public APIs awaiting external callers, not dead code)")
def _append_dynamic_binding_recommendation(report: dict, cv_root: Any) -> None:
    dyn_candidates = None
    if isinstance(cv_root, dict):
        dyn_candidates = cv_root.get("dynamic_binding_candidates")
    if isinstance(dyn_candidates, (list, tuple, set)) and dyn_candidates:
        append_recommendation_once(
            report,
            f"Cross-validate found {len(dyn_candidates)} dynamic binding candidates: "
            f"run RuntimeBindingScanner for deep scan")
def append_cv_dead_code_judgments(report: dict) -> int:
    pm = _extract_cv_precision_metrics(report)
    if not isinstance(pm, dict) or not pm:
        return 0
    cv_root = report.get(CAT_CROSS_VALIDATION)
    fp_orphans = int_metric(pm.get("false_positive_orphans"))
    confirmed_dead = int_metric(pm.get("confirmed_dead"))
    external_api_excluded = int_metric(pm.get("external_api_excluded"))
    static_precision = float_metric(pm.get("static_precision"), None)
    if (static_precision is not None
            and not 0.0 <= static_precision <= 100.0):
        logger.warning(
            "[Cross-validate] static_precision 超出 [0, 100]，忽略脏值: %s",
            static_precision)
        static_precision = None
    added = 0
    if fp_orphans > 0:
        added += append_judgment(
            report, "cv_false_positives", "warn",
            f"Cross-validate: {fp_orphans} false positive orphans "
            f"(covered but marked isolated)")
    if skill_type_name(report) == "library":
        added += _cv_library_dead_code_judgment(
            report, confirmed_dead, external_api_excluded)
    elif confirmed_dead > 0:
        added += append_judgment(
            report, "cv_dead_code", "warn",
            f"Cross-validate: {confirmed_dead} confirmed dead code functions")
    if static_precision is not None:
        added += append_judgment(
            report, "cv_precision",
            "pass" if static_precision >= 80 else "warn",
            f"Cross-validate: static analysis precision {static_precision:.1f}%")
    _append_dynamic_binding_recommendation(report, cv_root)
    return added
def append_import_bloat_judgment(report: dict, skill_dir: str, ctx: Any = None) -> int:
    try:
        _cached_bloat = report.get("import_bloat")
        if isinstance(_cached_bloat, dict) and _cached_bloat:
            bloat = _cached_bloat
        else:
            bloat = detect_import_bloat(skill_dir, ctx=ctx)
            if isinstance(bloat, dict):
                report["import_bloat"] = bloat
        if not isinstance(bloat, dict):
            return 0
        bloat_ratio = float_metric(bloat.get("bloat_ratio", 0))
        if bloat_ratio > 0.2:
            return int(append_judgment(
                report, "import_bloat", "warn",
                f"Import bloat: {int_metric(bloat.get('unused_imports', 0))}/"
                f"{int_metric(bloat.get('total_imports', 0))} unused ({bloat_ratio:.0%})"))
    except Exception as e:  # noqa: BLE001
        record_degradation(
            report, "import_bloat", "[import_bloat] 依赖膨胀检测失败", e)
    return 0
def _adjust_coverage_bands(j: dict, cov: float, *, pass_ratio: float,
                           warn_ratio: float, advice: str) -> bool:
    if cov >= pass_ratio:
        return False
    low = cov < warn_ratio
    j["status"] = "fail" if low else "warn"
    j["label"] = (f"公开函数覆盖率{'低' if low else '偏低'} "
                  f"{cov:.1%}（{advice}）")
    return True
_COVERAGE_BANDS_BY_TYPE: dict[str, tuple[float, float, str]] = {
    "cli": (0.6, 0.4, "CLI 工具建议 ≥60%"),
    "hybrid": (0.55, 0.35, "混合型建议 ≥55%"),
}
_PUBLIC_COVERAGE_TYPES = frozenset(_COVERAGE_BANDS_BY_TYPE) | {"library"}
def _adjust_coverage_library(j: dict, cov: float) -> bool:
    if cov >= 0.2:
        j["status"] = "pass"
        j["label"] = f"公开函数覆盖率 {cov:.1%}（库型技能，≥20% 正常）"
        return True
    if cov >= 0.1:
        j["status"] = "warn"
        j["label"] = f"公开函数覆盖率偏低 {cov:.1%}（库型技能建议 ≥20%）"
        return True
    j["status"] = "info"
    j["label"] = f"公开函数覆盖率低 {cov:.1%}（库型技能，大量 API 供外部调用）"
    return True
_COVERAGE_VALUE_FIELDS = ("coverage", "ratio", "value")
def _coverage_ratio_of(j: dict) -> float | None:
    for field in _COVERAGE_VALUE_FIELDS:
        raw = j.get(field)
        if isinstance(raw, bool) or not isinstance(raw, (int, float)):
            continue
        value = safe_float(raw, None)
        if value is None or value < 0:
            continue
        if value > 100:
            return None
        return value / 100 if value > 1 else value
    label = j.get("label")
    if isinstance(label, str):
        m = re.search(r"(\d+(?:\.\d+)?)\s*%", label)
        if m:
            percentage = float(m.group(1))
            if percentage > 100:
                return None
            return percentage / 100
    return None
def _adjust_public_coverage_entry(j: dict, st_name: str,
                                  key_name: str | None = None) -> bool:
    if (j.get("key") if key_name is None else key_name) != "public_coverage":
        return False
    cov = _coverage_ratio_of(j)
    if cov is None:
        return False
    if st_name == "library":
        return bool(_adjust_coverage_library(j, cov))
    band = _COVERAGE_BANDS_BY_TYPE.get(st_name)
    if band is None:
        return False
    return _adjust_coverage_bands(
        j, cov, pass_ratio=band[0], warn_ratio=band[1], advice=band[2])
def adjust_public_coverage_by_skill_type(report: dict) -> int:
    st_name = skill_type_name(report)
    if st_name not in _PUBLIC_COVERAGE_TYPES:
        return 0
    adjusted = 0
    for j in _judgments_view(report):
        if isinstance(j, dict) and _adjust_public_coverage_entry(j, st_name):
            adjusted += 1
            break
    cc = report.get("call_chain")
    if isinstance(cc, dict) and isinstance(cc.get("judgments"), dict):
        cj = cc["judgments"].get("public_coverage")
        if (isinstance(cj, dict)
                and _adjust_public_coverage_entry(cj, st_name,
                                                  "public_coverage")
                and append_judgment(report, "public_coverage",
                                    cj.get("status", "info"),
                                    cj.get("label", ""))):
            adjusted += 1
    return adjusted
def append_core_judgments(report: dict, skill_dir: str | None = None, ctx: Any = None) -> dict:
    added = {
        "blindspots": append_blindspot_severity_judgments(report),
        "coupling": append_coupling_judgments(report),
        "fragmentation": append_fragmentation_judgment(report),
        "skill_type": append_skill_type_judgment(report),
        "call_depth": append_call_depth_judgments(report),
        "cv_dead_code": append_cv_dead_code_judgments(report),
        "public_coverage_adjusted": adjust_public_coverage_by_skill_type(report),
    }
    if skill_dir:
        added["import_bloat"] = append_import_bloat_judgment(report, skill_dir, ctx)
    logger.info("[Verdicts] append_core_judgments 完成: %s", added)
    return added
def structural_health_component(skill_dir: str, findings: list, payload_parts: dict, ctx=None) -> None:
    st = detect_skill_type(skill_dir, ctx)
    analyze_structural_health(skill_dir, findings, payload_parts, st, ctx)
def supplement_structure_dimensions(report: dict, skill_dir: str,
                                    ctx: Any = None) -> str:
    report["skill_type"] = detect_skill_type(skill_dir, ctx)
    report["cross_skill_imports"] = {
        "consumer_count": report["skill_type"].get("cross_referenced_count", 0),
        "cross_referenced": report["skill_type"].get("cross_referenced", False),
    }
    report["module_coupling"] = analyze_module_coupling(skill_dir, ctx)
    report["fragmentation"] = analyze_fragmentation(skill_dir, ctx)
    report["bayesian_model"] = compute_bayesian_posterior(report)
    return skill_type_name(report)
def supplement_warning_section(report: dict, ctx: Any = None) -> dict:
    try:
        result = run_warning_quality_analysis(report, ctx)
    except Exception as err:  # noqa: BLE001
        log_swallowed(
            __name__, err,
            context=f'supplement_warning_section:{type(err).__name__}')
        record_degradation(
            report, "warning_quality", "[Step9] 警告质量增强分析失败", err)
        return report
    if not isinstance(result, dict):
        record_degradation(
            report, "warning_quality", "[Step9] 警告质量增强返回形态非法",
            TypeError(f"期望 dict，实际 {type(result).__name__}"))
        return report
    return result
_FAILED = object()
def _guarded_produce(report: dict, step: str, label: str,
                     producer: Callable[[], Any]) -> Any:
    try:
        return producer()
    except Exception as _err:  # noqa: BLE001
        log_swallowed(
            __name__, _err,
            context=f'_guarded_produce:{type(_err).__name__}')
        record_degradation(report, step, label, _err)
        return _FAILED
def _skill_label(skill_dir: str) -> str:
    return os.path.basename(os.path.abspath(skill_dir))
def build_health_report(skill_dir: str, report: dict | None = None,
                        ctx: Any = None, call_graph: Any = None) -> dict:
    report = dict(report) if isinstance(report, dict) else {}
    report["skill_dir"] = skill_dir
    report["errors"] = normalize_list_field(report.get("errors"))
    report[FIELD_RECOMMENDATIONS] = recommendations_list(report)
    logger.info(
        "[HealthReport] build_health_report 开始: skill=%s call_graph=%s "
        "输入sections=%d",
        _skill_label(skill_dir),
        "yes" if call_graph is not None else "no",
        len(report))
    supplement_structure_dimensions(report, skill_dir, ctx)
    supplement_graph_report_dimensions(report, skill_dir, ctx, call_graph)
    _guarded_produce(
        report, "core_judgments", "[Step6.5] 裁决层生成失败",
        lambda: append_core_judgments(report, skill_dir=skill_dir, ctx=ctx))
    report = compute_health_score(skill_dir, report, ctx)
    post_score_error_count = len(report["errors"])
    report = supplement_warning_section(report, ctx)
    supplement_cie_sections(report, skill_dir, ctx)
    _guarded_produce(
        report, "core_recommendations", "[Step12] 核心建议生成失败",
        lambda: generate_core_recommendations(report))
    if _reconcile_late_diag_errors(report, post_score_error_count):
        _set_health_verdict(
            report, _skill_label(skill_dir), has_findings=True)
    reconciled_error_count = len(report["errors"])
    pre_baseline_judgments = list(_judgments_view(report))
    pre_baseline_recommendations = list(recommendations_list(report))
    apply_baseline_comparison(
        skill_dir, report,
        data_dir=getattr(ctx, "data_dir", None) if ctx is not None else None)
    if _reconcile_late_diag_errors(report, reconciled_error_count):
        report.pop("baseline", None)
        report["judgments"] = pre_baseline_judgments
        report[FIELD_RECOMMENDATIONS] = pre_baseline_recommendations
        _set_health_verdict(
            report, _skill_label(skill_dir), has_findings=True)
    logger.info(
        "[HealthReport] build_health_report 完成: skill=%s health_score=%s "
        "status=%s 裁决数=%d 建议数=%d errors=%d",
        _skill_label(skill_dir),
        report.get("health_score", "N/A"),
        report.get("status", "N/A"),
        len(report.get("judgments") or []),
        len(report.get(FIELD_RECOMMENDATIONS) or []),
        len(report.get("errors") or []))
    return report
def apply_health_report(report: dict, skill_dir: str, ctx: Any = None) -> dict:
    try:
        health_report = build_health_report(skill_dir, report, ctx=ctx)
        if not isinstance(health_report, dict):
            logger.warning("[Aggregator] 健康报告返回非 dict(%s)，保留原报告",
                           type(health_report).__name__)
            return report
        return health_report
    except Exception as _hr_err:  # noqa: BLE001
        logger.warning("[Aggregator] 健康报告聚合失败（不阻塞后续步骤）: %s", _hr_err)
        return report
_SEV_WEIGHTS = {"P0": 10.0, "P1": 3.0, "P2": 1.0, "P3": 0.3}
_DEFAULT_SEVERITY_BUCKET = "P2"
_DEBT_CATEGORIES = {
    "security": {"label": "安全", "prefixes": ("SE-", "CV-", "CF-"), "dims": {"security"}, "weight": 1.5},
    "architecture": {"label": "架构", "prefixes": ("CC-", "CT-", "RG-", "RS-", "PA-"), "dims": {"modularity", "consistency"}, "weight": 1.3},
    "quality": {"label": "质量", "prefixes": ("LQ-", "NT-", "EX-", "EN-", "FM-", "VC-"), "dims": {"readability", CAT_MAINTAINABILITY}, "weight": 1.0},
    "performance": {"label": "性能", "prefixes": ("PF-", "MP-"), "dims": {"performance"}, "weight": 1.0},
}
QUALITY_DIMENSION_WEIGHTS = {
    CAT_MAINTAINABILITY: 1.2,
    "readability": 1.0,
    "security": 1.5,
    "performance": 1.0,
    "modularity": 1.3,
    "test_coverage": 1.0,
    "documentation": 0.8,
    "consistency": 1.0,
    "simplicity": 0.8,
    "robustness": 1.2,
}
_DEFAULT_DIMENSION_WEIGHT = 1.0
SEVERITY_DEDUCTION = {"P0": 10.0, "P1": 2.5, "P2": 0.3, "P3": 0.1}
_P0_ARCH_SEC_CATEGORIES = ('architecture', 'security')
_P0_ARCH_SEC_PREFIXES = tuple(
    _prefix
    for _cat_key in _P0_ARCH_SEC_CATEGORIES
    for _prefix in _DEBT_CATEGORIES[_cat_key]['prefixes'])
_P0_ARCH_SEC_DIMS = frozenset(
    _dim
    for _cat_key in _P0_ARCH_SEC_CATEGORIES
    for _dim in _DEBT_CATEGORIES[_cat_key]['dims'])
QUALITY_GATES = {"blocker": 50.0, "warning": 65.0, "pass": 75.0, "excellent": 88.0}
BLOCK_THRESHOLD = 500
CRITICAL_THRESHOLD = 1000
_MISSING: Any = object()
def _issue_get(issue: Any, key: str, *, skip_empty: bool = False) -> Any:
    for name in FINDING_KEY_ALIASES.get(key, (key,)):
        if isinstance(issue, dict):
            if name in issue:
                value = issue[name]
                if skip_empty and not value:
                    continue
                return value
        elif hasattr(issue, name):
            value = getattr(issue, name)
            if skip_empty and not value:
                continue
            return value
    return _MISSING
def _issue_attr_str(issue: Any, attr: str, default: str = '') -> str:
    value = _issue_get(issue, attr)
    return value if isinstance(value, str) else default
def _issue_dimension(issue: Any) -> str:
    dimension = _issue_attr_str(issue, "dimension")
    if dimension:
        return dimension
    category = _issue_attr_str(issue, "category")
    if category in QUALITY_DIMENSION_WEIGHTS or category == "quality":
        return category
    return ""
def _issue_category(issue: Any) -> str | None:
    rule_id = _issue_attr_str(issue, "rule_id")
    dimension = _issue_dimension(issue)
    category = _issue_attr_str(issue, "category")
    if dimension:
        for cat_key, cat_info in _DEBT_CATEGORIES.items():
            if dimension in cat_info["dims"]:
                return cat_key
    if rule_id:
        prefix_key = rule_id.upper()
        for cat_key, cat_info in _DEBT_CATEGORIES.items():
            if prefix_key.startswith(cat_info["prefixes"]):
                return cat_key
    if category in _DEBT_CATEGORIES:
        return category
    if rule_id or dimension or _issue_attr_str(issue, "severity"):
        return "quality"
    return None
def _quality_dimension_of(issue: Any) -> str:
    dimension = _issue_dimension(issue)
    if dimension:
        return dimension
    category = _issue_category(issue)
    dims = _DEBT_CATEGORIES.get(category, {}).get("dims", ())
    if len(dims) == 1:
        return next(iter(dims))
    return "quality"
def _issue_category_entry(issue: Any) -> dict[str, str]:
    entry = {
        "rule_id": _issue_attr_str(issue, "rule_id"),
        "severity": normalize_severity(
            _issue_attr_str(issue, "severity", _DEFAULT_SEVERITY_BUCKET)
            or _DEFAULT_SEVERITY_BUCKET),
        "dimension": _issue_dimension(issue),
        "category": _issue_attr_str(issue, "category"),
    }
    file_path = _issue_file_path(issue)
    if file_path:
        entry["file"] = file_path
    return entry
def _categorize_issues(issues: Any) -> dict[str, list[dict[str, str]]]:
    categorized: dict[str, list[dict[str, str]]] = {
        cat_key: [] for cat_key in _DEBT_CATEGORIES
    }
    for issue in issues:
        cat_key = _issue_category(issue)
        if cat_key is not None:
            categorized[cat_key].append(_issue_category_entry(issue))
    return categorized
def _issue_file_path(issue: Any) -> str:
    fp = _issue_get(issue, "file", skip_empty=True)
    return "" if fp is _MISSING else str(fp)
def _count_affected_files(cat_issues: list) -> int:
    return len({i["file"] for i in cat_issues if i.get("file")})
def _build_single_category_result(cat_key: str, cat_info: dict, cat_issues: list, affected_files: int) -> dict:
    cat_score = sum(_SEV_WEIGHTS.get(i["severity"], 1) for i in cat_issues)
    weighted = cat_score * cat_info["weight"]
    return {
        "key": cat_key, "label": cat_info.get("label", cat_key),
        "issue_count": len(cat_issues), "affected_files": affected_files,
        "raw_score": cat_score, "weight": cat_info["weight"],
        "weighted_score": weighted,
    }
_REWRITE_SIGNAL_MIN_SAMPLE = 3
_REWRITE_ARCH_SHARE = 0.35
_REWRITE_SEC_QUALITY_SHARE = 0.6
_REWRITE_MIN_WEIGHTED = 20.0
_P0_CONCENTRATION_SHARE = 0.6
def _category_weighted(result: dict, cat_key: str) -> float:
    return safe_float(
        section_dict(result, cat_key, {}).get("weighted_score"), 0.0)
def _category_issues(result: dict, cat_key: str) -> int:
    return int_metric(section_dict(result, cat_key, {}).get("issue_count"))
def _detect_rewrite_signal_architecture(result: dict, total_weighted: float
                                        ) -> str | None:
    if _category_issues(result, "architecture") < _REWRITE_SIGNAL_MIN_SAMPLE:
        return None
    if total_weighted <= 0:
        return None
    if (_category_weighted(result, "architecture") / total_weighted
            > _REWRITE_ARCH_SHARE):
        return "架构债务占比过高(>35%)"
    return None
def _detect_rewrite_signal_sec_quality(result: dict, total_weighted: float
                                       ) -> str | None:
    if (_category_issues(result, "security")
            + _category_issues(result, "quality")
            < _REWRITE_SIGNAL_MIN_SAMPLE):
        return None
    sec_q = (_category_weighted(result, "security")
             + _category_weighted(result, "quality"))
    if (total_weighted > _REWRITE_MIN_WEIGHTED
            and sec_q > total_weighted * _REWRITE_SEC_QUALITY_SHARE):
        return "安全+质量联合债务过高"
    return None
def _detect_rewrite_signal_density(issues: list) -> str | None:
    located_files = [fp for issue in issues
                     if (fp := _issue_file_path(issue))]
    if len(located_files) <= 50:
        return None
    affected_total = len(set(located_files))
    if len(located_files) / affected_total > 5:
        return "问题密度过高(>5个问题/文件)"
    return None
def _detect_rewrite_signal_p0_concentration(issues: list) -> str | None:
    p0_arch_sec = 0
    p0_total = 0
    for issue in issues:
        severity = normalize_severity(
            _issue_attr_str(issue, "severity") or _DEFAULT_SEVERITY_BUCKET)
        if severity != "P0":
            continue
        p0_total += 1
        _rule_upper = _issue_attr_str(issue, "rule_id").upper()
        if (_rule_upper.startswith(_P0_ARCH_SEC_PREFIXES)
                or _issue_attr_str(issue, "dimension") in _P0_ARCH_SEC_DIMS
                or _issue_attr_str(issue, "category") in _P0_ARCH_SEC_CATEGORIES):
            p0_arch_sec += 1
    if (p0_total >= _REWRITE_SIGNAL_MIN_SAMPLE
            and p0_arch_sec / p0_total > _P0_CONCENTRATION_SHARE):
        return f"P0问题集中于架构/安全({p0_arch_sec}/{p0_total})"
    return None
def _evaluate_rewrite_signals(result: dict, total_weighted: float, issues: list) -> tuple[int, list[str]]:
    reasons: list[str] = []
    for signal in (
        _detect_rewrite_signal_architecture(result, total_weighted),
        _detect_rewrite_signal_sec_quality(result, total_weighted),
        _detect_rewrite_signal_density(issues),
        _detect_rewrite_signal_p0_concentration(issues),
    ):
        if signal:
            reasons.append(signal)
    if total_weighted >= CRITICAL_THRESHOLD:
        reasons.append(
            f"债务加权总分 {total_weighted:.0f} 达关键重写阈值(≥{CRITICAL_THRESHOLD})，强烈建议重写")
    elif total_weighted >= BLOCK_THRESHOLD:
        reasons.append(
            f"债务加权总分 {total_weighted:.0f} 达建议重写阈值(≥{BLOCK_THRESHOLD})，建议评估重写")
    return len(reasons), reasons
def analyze_technical_debt(issues: Any) -> dict[str, Any]:
    issues = strict_iterable_list(issues)
    result: dict[str, Any] = {}
    total_weighted = 0.0
    categorized = _categorize_issues(issues)
    for cat_key, cat_info in _DEBT_CATEGORIES.items():
        cat_issues = categorized[cat_key]
        affected_files = _count_affected_files(cat_issues)
        cat_result = _build_single_category_result(cat_key, cat_info, cat_issues, affected_files)
        result[cat_key] = cat_result
        total_weighted += cat_result["weighted_score"]
    highest = (max(result.values(), key=lambda x: x["weighted_score"])["label"]
               if result and total_weighted > 0 else "N/A")
    classified_issues = [
        entry for cat_issues in categorized.values() for entry in cat_issues
    ]
    signals, reasons = _evaluate_rewrite_signals(
        result, total_weighted, classified_issues)
    return {
        "categories": result,
        "total_weighted_score": total_weighted,
        "highest_category": highest,
        "rewrite_signals": signals,
        "rewrite_reasons": reasons,
    }
def _insight(priority: int, category: str, message: str,
             action: str) -> dict:
    return {"priority": priority, "category": category,
            "message": message, "action": action}
def _insight_from_gate(quality_result: dict) -> list[dict]:
    insights: list[dict] = []
    score = safe_float(quality_result.get("score"), 100.0)
    gate = quality_result.get("gate", "pass")
    if gate == "blocker":
        p0_count = int_or(quality_result.get("p0_count"), 0)
        if p0_count > 0:
            insights.append(_insight(
                0, "阻断",
                f"质量门控阻断(评分{score}), P0问题{p0_count}个需立即修复",
                "优先修复所有P0安全问题,禁止发布"))
        else:
            insights.append(_insight(
                0, "阻断",
                f"质量门控阻断(评分{score}), "
                f"综合评分低于{QUALITY_GATES['warning']:.0f}分",
                "优先修复低分维度和高频严重问题,禁止发布"))
    elif gate == "warning":
        insights.append(_insight(
            1, "警告",
            f"质量评分低于{QUALITY_GATES['pass']:.0f}分({score}), 代码质量需提升",
            "修复高频P1问题,重点关注低分维度"))
    return insights
def _insight_from_dimensions(quality_result: dict) -> list[dict]:
    insights: list[dict] = []
    dim_scores = quality_result.get("dimension_scores", {})
    if not isinstance(dim_scores, dict):
        return insights
    scored = []
    for dim, dim_score in dim_scores.items():
        score_num = safe_float(dim_score, None)
        if score_num is not None:
            scored.append((dim, score_num))
    low_dims = sorted(scored, key=lambda x: x[1])[:3]
    for dim, dim_score in low_dims:
        if dim_score < 70:
            insights.append(_insight(
                2, "维度改进",
                f"维度 '{dim}' 评分仅{dim_score}分,低于70分阈值",
                f"诊断维度 '{dim}' 的规则违规,针对性修复"))
    return insights
def _insight_from_debt(debt_result: Any) -> list[dict]:
    insights: list[dict] = []
    if not isinstance(debt_result, dict):
        return insights
    cats = debt_result.get("categories")
    if not isinstance(cats, dict):
        return insights
    for cat_info in cats.values():
        if not isinstance(cat_info, dict):
            continue
        count = safe_float(cat_info.get("issue_count"), 0.0)
        if count > 5:
            _label = cat_info.get("label") or ""
            insights.append(_insight(
                3, "技术债务", f"{_label}累积{count:g}个问题",
                f"制定{_label}偿还计划,分批处理"))
    return insights
def _insight_from_density(quality_result: dict) -> list[dict]:
    insights: list[dict] = []
    density = safe_float(quality_result.get("density_per_kloc"), 0.0)
    if density and density > 50:
        insights.append(_insight(
            2, "代码密度", f"问题密度{density}/KLOC过高",
            "考虑模块拆分或重点区域重构"))
    return insights
def generate_quality_insights(quality_result: dict, debt_result: Any = None) -> list[dict]:
    if not isinstance(quality_result, dict):
        quality_result = {}
    insights: list[dict] = []
    insights.extend(_insight_from_gate(quality_result))
    insights.extend(_insight_from_dimensions(quality_result))
    insights.extend(_insight_from_debt(debt_result))
    insights.extend(_insight_from_density(quality_result))
    insights.sort(key=lambda x: x["priority"])
    return insights
def _empty_severity_counts() -> dict[str, int]:
    return dict.fromkeys(SEVERITY_DEDUCTION, 0)
def _bump_dimension_counts(dim_issues: dict, p_counts: dict,
                           dim: str, sev: str) -> None:
    if sev not in p_counts:
        return
    dim_counts = dim_issues.setdefault(dim, _empty_severity_counts())
    p_counts[sev] += 1
    dim_counts[sev] += 1
def _count_issues_by_dimension(issues: Any) -> tuple[dict, dict]:
    dim_issues: dict[str, dict[str, int]] = {}
    p_counts = _empty_severity_counts()
    for issue in issues:
        if (_issue_get(issue, 'severity') is _MISSING
                and _issue_category(issue) is None):
            continue
        _sev_raw = _issue_attr_str(issue, 'severity')
        _sev = (normalize_severity(_sev_raw) if _sev_raw
                else _DEFAULT_SEVERITY_BUCKET)
        if _sev not in SEVERITY_DEDUCTION:
            _sev = _DEFAULT_SEVERITY_BUCKET
        _bump_dimension_counts(dim_issues, p_counts,
                               _quality_dimension_of(issue), _sev)
    return dim_issues, p_counts
def _compute_dimension_scores(dim_issues: dict, total_lines: int) -> tuple[dict, float]:
    total_deduction = 0.0
    dimension_scores: dict[str, float] = {}
    kloc = total_lines / 1000.0
    extra_dims = sorted(d for d in dim_issues if d not in QUALITY_DIMENSION_WEIGHTS)
    for dim in (*QUALITY_DIMENSION_WEIGHTS, *extra_dims):
        weight = QUALITY_DIMENSION_WEIGHTS.get(dim, _DEFAULT_DIMENSION_WEIGHT)
        counts = dim_issues.get(dim) or _empty_severity_counts()
        raw_penalty = sum(counts.get(sev, 0) * deduction
                          for sev, deduction in SEVERITY_DEDUCTION.items())
        normalized_penalty = raw_penalty / max(kloc, 0.1) * 0.5
        weighted_penalty = normalized_penalty * weight
        total_deduction += weighted_penalty
        dim_score = max(0, 100 - weighted_penalty * 10)
        dimension_scores[dim] = round(dim_score, 1)
    return dimension_scores, total_deduction
_QUALITY_LADDER = (
    (QUALITY_GATES["excellent"], "A", "excellent"),
    (QUALITY_GATES["pass"], "B", "pass"),
    (QUALITY_GATES["warning"], "C", "warning"),
    (QUALITY_GATES["blocker"], "D", "blocker"),
)
def _ladder_rung(score: float) -> tuple[str, str]:
    for threshold, grade, gate in _QUALITY_LADDER:
        if score >= threshold:
            return grade, gate
    return "F", "blocker"
def _determine_gate(score: float, p0_count: int) -> str:
    if p0_count > 0:
        return "blocker"
    return _ladder_rung(score)[1]
def calculate_quality_score(issues: Any, total_lines: int, files_scanned: int) -> dict[str, Any]:
    issues = strict_iterable_list(issues)
    total_lines = max(int_or(total_lines, 0), 0)
    files_scanned = max(int_or(files_scanned, 0), 0)
    dim_issues, p_counts = _count_issues_by_dimension(issues)
    total_issues = sum(p_counts.values())
    if total_lines == 0 and total_issues == 0:
        return _quality_payload(
            score=0.0, grade="N/A", gate="unknown", total_issues=0,
            total_lines=0, files_scanned=files_scanned, kloc=0.0,
            density=0.0, severity_counts=p_counts, dimension_scores={},
            measured=False)
    dimension_scores, total_deduction = _compute_dimension_scores(dim_issues, total_lines)
    p0_extra = p_counts["P0"] * 5.0
    score = round(max(0, min(100, 100 - total_deduction - p0_extra)), 1)
    kloc = total_lines / 1000.0
    return _quality_payload(
        score=score, grade=_ladder_rung(score)[0],
        gate=_determine_gate(score, p_counts["P0"]),
        total_issues=total_issues, total_lines=total_lines,
        files_scanned=files_scanned, kloc=round(kloc, 2),
        density=round(total_issues / max(kloc, 0.1), 2),
        severity_counts=p_counts, dimension_scores=dimension_scores)
def _quality_payload(*, score: float, grade: str, gate: str,
                     total_issues: int, total_lines: int, files_scanned: int,
                     kloc: float, density: float, severity_counts: dict,
                     dimension_scores: dict, measured: bool = True) -> dict[str, Any]:
    return {
        "measured": measured,
        "score": score, "grade": grade, "gate": gate,
        "total_issues": total_issues, "total_lines": total_lines,
        "files_scanned": files_scanned,
        "kloc": kloc, "density": density, "density_per_kloc": density,
        "severity_counts": severity_counts,
        "dimension_scores": dimension_scores,
        "p0_count": severity_counts["P0"],
    }
def _report_list(report: dict, key: str) -> list:
    v = report.get(key) or []
    return list(v) if isinstance(v, (list, tuple, set)) else []
_EXTRA_FAILED_STEP_STATUSES = frozenset({"corrupted"})
def _is_failed_step(status: Any) -> bool:
    if not isinstance(status, str):
        return False
    text = status.strip().lower()
    if not text:
        return False
    if text in _EXTRA_FAILED_STEP_STATUSES:
        return True
    return method_status_bucket(text) == "failed"
def _step_stats(report: dict) -> tuple[int, int]:
    steps = report.get("steps", {})
    if isinstance(steps, dict):
        values = list(steps.values())
    elif isinstance(steps, (list, tuple)):
        values = list(steps)
    else:
        return 0, 0
    completed_steps = sum(
        1 for value in values
        if isinstance(value, dict)
        and method_status_bucket(value.get("status")) == "completed")
    return len(values), completed_steps
def _quality_level(score: float) -> str:
    return _ladder_rung(float(score))[0]
def _quality_score_breakdown(findings: list[dict], total_steps: int,
                             completed_steps: int, error_count: int,
                             file_count: int) -> tuple[int, dict]:
    step_success_rate = completed_steps / max(total_steps, 1)
    error_rate = error_count / max(total_steps, 1)
    severity_penalty = sum(
        severity_penalty_weight(f.get("severity")) for f in findings)
    finding_density = len(findings) / max(file_count / 100, 1)
    base_score = step_success_rate * 60
    error_penalty = min(error_rate * 100, 20)
    severity_score = max(0, 20 - severity_penalty * 0.5)
    density_score = max(0, 20 - finding_density * 2)
    raw_score = base_score + severity_score + density_score - error_penalty
    score = max(0, min(100, int(raw_score)))
    return score, {
        "step_success_rate": round(step_success_rate, 3),
        "error_count": error_count,
        "finding_count": len(findings),
        "severity_penalty": severity_penalty,
        "finding_density": round(finding_density, 3),
    }
def _no_quality_data(reason: str) -> dict:
    return {"score": 0, "level": "N/A", "details": {"reason": reason}}
def quantify_quality(report: object = None) -> dict:
    if report is None or not isinstance(report, dict):
        return _no_quality_data("no report provided")
    findings = [f for f in _report_list(report, "findings") if isinstance(f, dict)]
    total_steps, completed_steps = _step_stats(report)
    if total_steps == 0 and not findings:
        return _no_quality_data("no steps or findings provided")
    file_count = len(_report_list(report, "files")) or 1
    score, details = _quality_score_breakdown(
        findings, total_steps, completed_steps,
        len(_report_list(report, "errors")), file_count)
    return {"score": score, "level": _quality_level(score), "details": details}
_QUALITY_LINES_PER_FINDING = 50
def _soft_projection_chain(label: str, fn, *args) -> None:
    try:
        fn(*args)
    except Exception as _chain_err:  # noqa: BLE001
        logger.warning("[QualityProjection] %s失败: %s", label, _chain_err)
def _quality_findings_objects(confirmed: list[dict]) -> tuple[list, set]:
    fobjs = []
    files: set[str] = set()
    for _fi in confirmed:
        if not isinstance(_fi, dict):
            continue
        finding = types.SimpleNamespace(
            rule_id=_issue_attr_str(_fi, "rule_id"),
            severity=_fi.get("severity") or _DEFAULT_SEVERITY_BUCKET,
            dimension=_issue_dimension(_fi),
            category=_issue_attr_str(_fi, "category"),
        )
        file_path = _issue_file_path(_fi)
        if file_path:
            finding.file = file_path
            files.add(file_path)
        fobjs.append(finding)
    return fobjs, files
def _record_map(value: object) -> list[dict]:
    if isinstance(value, dict):
        return [item for item in value.values() if isinstance(item, dict)]
    return dict_items(value)
def _project_light_quality(out: dict, details: list,
                           confirmed: list[dict]) -> None:
    _quality = quantify_quality(report={
        "steps": details,
        "findings": confirmed,
        "errors": [d for d in details
                   if _is_failed_step(d.get("status"))],
        "files": [],
    })
    out["quality_score"] = _quality.get("score")
    out["quality_level"] = _quality.get("level")
def _project_deep_quality(out: dict, confirmed: list[dict]) -> None:
    if not confirmed:
        return
    _fobjs, _files = _quality_findings_objects(confirmed)
    _est_lines = len(_fobjs) * _QUALITY_LINES_PER_FINDING
    _qres = calculate_quality_score(_fobjs, total_lines=_est_lines,
                                    files_scanned=len(_files))
    _dres = analyze_technical_debt(_fobjs)
    out["quality_assessment"] = {
        "quality": _qres,
        "debt": _dres,
        "insights": generate_quality_insights(_qres, _dres)[:10],
    }
def build_quality_projection(details: object,
                             confirmed_findings: object) -> dict:
    out: dict = {}
    _details = _record_map(details)
    _confirmed = _record_map(confirmed_findings)
    _soft_projection_chain("质量量化评分", _project_light_quality, out,
                           _details, _confirmed)
    _soft_projection_chain("深度质量评分链", _project_deep_quality, out,
                           _confirmed)
    return out

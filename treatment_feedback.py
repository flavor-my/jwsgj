from __future__ import annotations

import argparse
import datetime as _dt
import json
import logging
import os
import sys
import time
from collections import defaultdict
from dataclasses import dataclass, field, replace
from typing import NamedTuple

from jwsgj.ai_review_item_plan import sync_adjustment_proposals
from jwsgj.diag_types_defs import (
    DiagnosisFeedback,
    FeedbackReport,
    TreatmentOutcome,
    TreatmentOutcomeSummary,
    default_feedback_history,
    summary_dict,
)
from jwsgj.diag_types_normalize import (
    as_list,
    cv_int,
    dict_or_empty,
    float_metric,
    int_or,
    is_finite_num,
    is_high_severity,
    is_placeholder_rule_id,
    safe_float,
    signal_bool,
    str_or_empty,
    strip_cv_target_prefix,
)
from jwsgj.diag_types_vocab import (
    AGGREGATE_CV_TARGETS,
    FIELD_CV_CONFIDENCE_THRESHOLDS,
    FIELD_CV_RULE_WEIGHTS,
    FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
    FIELD_METHOD_THRESHOLDS,
    FIELD_REGRESSION_FAILED,
    FIELD_ROUTED_TO_FIXER,
    FIELD_SAFETY_VERIFIER_USED,
    FIELD_SIDE_EFFECTS_DETECTED,
    FIELD_SUGGESTED_VALUE,
    FMT_DATETIME,
    FMT_DATETIME_ISO,
    SUMMARY_STATUS_BUCKETS,
)
from jwsgj.fp_rules_judge import (
    drop_fp_suppression_rule,
    load_fp_tracker_rates,
    suppression_min_severity,
)
from jwsgj.log_config import (
    log_swallowed,
    setup_logging,
)
from jwsgj.memory_bridge import DiagnosticMemoryContext
from jwsgj.memory_feedback_core import apply_memory_bridge
from jwsgj.retrospective_ledger import (
    _required_write_lock,
    load_treatment_items_for_evidence,
    normalized_enhancement_entries,
    read_enhancement_log,
    save_enhancement_log,
)
from jwsgj.runtime_paths import (
    read_evolution_section,
    write_evolution_section,
)
from jwsgj.runtime_scope import (
    normalize_skill_dir,
)
from jwsgj.treatment_state import (
    iter_unique_rule_observations,
    normalize_item_severity,
)
from jwsgj.treatment_verdict import (
    _DEFAULT_PROPAGATE_IO,
    AUTO_SAFE_REGISTRY_TARGET,
    EXECUTED_STATES,
    FIELD_REQUEST_COUNT,
    FIELD_TRIGGER_COUNT,
    FIXED_STATES,
    HISTORY_FIXER_SECTION,
    LIST_ADJUSTMENTS,
    LIST_FEEDBACKS,
    LIST_SUGGESTIONS,
    REGRESSED_STATES,
    DiagnosisFeedbackResolver,
    actionable_rule_ids,
    default_method_adjustments,
    failure_bucket,
    iter_details,
    normalize_feedback_history,
    normalize_fix_route_report,
)
from jwsgj.xv_intermediate_store import (
    load_retrospective_context,
    peek_round_start_ts,
)

__all__ = [
    'AGGREGATE_CV_TARGETS',
    'DiagnosisFeedback',
    'FeedbackApplier',
    'FeedbackReport',
    'TreatmentOutcome',
    'TreatmentOutcomeAnalyzer',
    'TreatmentOutcomeSummary',
    'bridge_feedbacks_to_enhancement_log',
    'build_treatment_context',
    'cv_int',
    'get_effective_adjustments',
    'is_finite_num',
    'is_placeholder_rule_id',
    'report_ai_adjustment_proposals',
    'run_feedback_loop',
    'str_or_empty',
    'strip_cv_target_prefix',
]
logger = logging.getLogger(__name__)
def _derive_module_path() -> str:
    spec_name = getattr(__spec__, "name", "") if __spec__ is not None else ""
    if spec_name and spec_name != "__main__":
        return spec_name
    stem = os.path.splitext(os.path.basename(__file__))[0]
    return f"{__package__}.{stem}" if __package__ else stem
_MODULE_PATH = _derive_module_path()
_MODULE_NAME = _MODULE_PATH.rsplit(".", 1)[-1]
_USAGE_ENTRY = (f"python -m {_MODULE_PATH}" if "." in _MODULE_PATH
                else f"python {os.path.basename(__file__)}")
logger.info("treatment_feedback 治疗反馈闭环已加载: %d 项导出", len(__all__))
def _count_or_zero(v) -> int:
    return max(0, int_or(v, 0))
def _rate_pct(numerator: int, denominator: int) -> float:
    return round(min(100.0, max(0.0, numerator / max(denominator, 1) * 100)), 1)
def _rule_id_text(value) -> str:
    return value.strip() if isinstance(value, str) else ""
def _status_key(value) -> str:
    return value.strip().lower() if isinstance(value, str) else ""
def _detail_side_effects(detail: dict) -> list:
    side_effects = as_list(detail.get("side_effects"))
    if side_effects:
        return side_effects
    result = detail.get("result")
    return as_list(result.get("side_effects")) if isinstance(result, dict) else []
def _outcomes_from_details(details: list) -> list[TreatmentOutcome]:
    outcomes: list[TreatmentOutcome] = []
    for detail in details if isinstance(details, (list, tuple)) else []:
        if not isinstance(detail, dict):
            continue
        line = detail.get("line")
        if not _count_or_zero(line):
            line = detail.get("line_number")
        outcomes.append(TreatmentOutcome(
            rule_id=_rule_id_text(detail.get("rule_id")),
            file=(str_or_empty(detail.get("file"))
                  or str_or_empty(detail.get("file_path"))),
            line=_count_or_zero(line),
            status=_status_key(detail.get("status")),
            severity=str_or_empty(detail.get("severity")),
            auto_safe=signal_bool(detail.get("auto_safe")),
            fixer_type=str_or_empty(detail.get("fixer_type")).strip(),
            reason=str_or_empty(detail.get("reason")),
            timestamp=str_or_empty(detail.get("timestamp")),
            side_effects=_detail_side_effects(detail),
        ))
    return outcomes
_NON_ATTEMPT_STATUSES: frozenset[str] = frozenset(
    status
    for _field in ("no_fixer", "file_not_found", "fp_confirmed", "needs_review")
    for status in SUMMARY_STATUS_BUCKETS.get(_field, ())
) | frozenset({"pending", "planned", "skipped", "pending_confirm", "dry_run"})
def _resolve_total_attempted(summary_data: dict, outcomes: list) -> int:
    if summary_data.get(FIELD_ROUTED_TO_FIXER) is not None:
        return _count_or_zero(summary_data.get(FIELD_ROUTED_TO_FIXER))
    return sum(
        1 for o in outcomes
        if o.status and o.status not in _NON_ATTEMPT_STATUSES)
_SIDE_EFFECT_NEW_ISSUE_TYPES: frozenset[str] = frozenset({"new_issue", "added"})
_SIDE_EFFECT_WORSENED_TYPES: frozenset[str] = frozenset({
    "worsened", "removed", "modified", "changed",
})
_SIDE_EFFECT_NEW_ISSUE_SUFFIX = "_added"
_SIDE_EFFECT_WORSENED_SUFFIXES = ("_removed", "_changed")
def _side_effect_bucket(change_type) -> str:
    kind = _status_key(change_type)
    if kind in _SIDE_EFFECT_NEW_ISSUE_TYPES or kind.endswith(
            _SIDE_EFFECT_NEW_ISSUE_SUFFIX):
        return "new_issue"
    if kind in _SIDE_EFFECT_WORSENED_TYPES or kind.endswith(
            _SIDE_EFFECT_WORSENED_SUFFIXES):
        return "worsened"
    return ""
def _count_side_effect_types(side_effects: list) -> tuple[int, int]:
    new_issues = worsened = 0
    for se in side_effects:
        if not isinstance(se, dict):
            continue
        bucket = _side_effect_bucket(se.get("type"))
        if bucket == "new_issue":
            new_issues += 1
        elif bucket == "worsened":
            worsened += 1
    return new_issues, worsened
def _summarize_side_effects(outcomes: list[TreatmentOutcome]) -> dict:
    total = introduced_new = worsened = 0
    for o in outcomes:
        if not o.side_effects:
            continue
        total += len(o.side_effects)
        _new, _worse = _count_side_effect_types(o.side_effects)
        introduced_new += _new
        worsened += _worse
    return {
        "total_side_effects": total,
        "introduced_new_issues": introduced_new,
        "worsened_existing": worsened,
    }
def _report_details_summary(report: dict) -> tuple[list[dict], dict]:
    details = iter_details(report)
    raw_summary = report.get("summary")
    summary = raw_summary if isinstance(raw_summary, dict) else {}
    return details, summary
def _rule_id_for_stats(outcome: TreatmentOutcome, skip_label: str) -> str | None:
    if is_placeholder_rule_id(outcome.rule_id):
        logger.warning(
            "[TreatmentOutcome] outcome rule_id 缺失/占位（status=%s, file=%s），%s",
            outcome.status, outcome.file, skip_label)
        return None
    return outcome.rule_id
def _count_outcomes_by_rule(items: list[TreatmentOutcome],
                            skip_label: str) -> dict:
    by_rule: dict[str, int] = defaultdict(int)
    for o in items:
        rid = _rule_id_for_stats(o, skip_label)
        if rid is None:
            continue
        by_rule[rid] += 1
    return dict(by_rule)
def _derived_coverage(coverage: dict):
    covered = safe_float(coverage.get("covered"), None)
    total = safe_float(coverage.get("total"), None)
    if covered is None or total is None or total <= 0:
        return None
    if covered < 0 or covered > total:
        logger.warning(
            "[TreatmentOutcome] fix_coverage 计数越界，跳过低覆盖判定: %r/%r",
            covered, total)
        return None
    return covered / total * 100
def _coverage_rate_value(coverage):
    if not isinstance(coverage, dict):
        return coverage
    if coverage.get("coverage_rate") is not None:
        return coverage.get("coverage_rate")
    return _derived_coverage(coverage)
def _fix_coverage_payload(fix_route_report: dict):
    if "fix_coverage" in fix_route_report:
        return fix_route_report.get("fix_coverage")
    summary = fix_route_report.get("summary")
    if isinstance(summary, dict):
        return summary.get("fix_coverage")
    return None
def _coverage_pct(coverage_rate) -> float | None:
    if is_finite_num(coverage_rate):
        parsed = float(coverage_rate)
    elif isinstance(coverage_rate, str):
        text = coverage_rate.strip()
        if text.endswith("%"):
            text = text[:-1].strip()
        try:
            parsed = float(text) if text and "%" not in text else float("nan")
        except ValueError:
            parsed = float("nan")
    else:
        parsed = float("nan")
    if not is_finite_num(parsed) or not 0.0 <= parsed <= 100.0:
        logger.warning(
            "[TreatmentOutcome] fix_coverage 覆盖率非法，跳过低覆盖判定: %r",
            coverage_rate)
        return None
    return parsed
def _low_fixer_coverage_issue(
        fix_route_report: dict, total_attempted: int) -> dict | None:
    if total_attempted <= 0:
        return None
    coverage_rate = _coverage_rate_value(
        _fix_coverage_payload(fix_route_report))
    if coverage_rate is None:
        return None
    cov_pct = _coverage_pct(coverage_rate)
    if cov_pct is None or cov_pct >= 20.0:
        return None
    return {
        "issue_type": "low_fixer_coverage",
        "severity": "low",
        "description": f"修复器覆盖率仅 {cov_pct}%，大量诊断发现无修复能力",
        "coverage_rate": cov_pct,
        "feedback_target": "fixer_registry",
    }
def _summary_count(summary_data: dict, outcomes: list,
                   field: str) -> int:
    if summary_data.get(field) is not None:
        return _count_or_zero(summary_data.get(field))
    statuses = SUMMARY_STATUS_BUCKETS.get(field, ())
    return sum(1 for o in outcomes if o.status in statuses)
_OUTCOME_BUCKETS: tuple[str, ...] = (
    "fixed", "rolled_back", "failed", "fp_confirmed")
def _group_outcomes_by_rule(outcomes) -> dict:
    by_rule = defaultdict(lambda: {
        "total": 0,
        "fixed": 0,
        "rolled_back": 0,
        "failed": 0,
        "fp_confirmed": 0,
        "executed": 0,
        "severities": {bucket: {} for bucket in _OUTCOME_BUCKETS},
    })
    for o in outcomes:
        bucket = failure_bucket(o.status)
        if not bucket:
            continue
        rid = _rule_id_for_stats(o, "跳过规则级失败模式统计")
        if rid is None:
            continue
        entry = by_rule[rid]
        entry["total"] += 1
        entry[bucket] += 1
        if bucket != "fp_confirmed":
            entry["executed"] += 1
        severity = normalize_item_severity(o.severity)
        bucket_severities = entry["severities"][bucket]
        bucket_severities[severity] = bucket_severities.get(severity, 0) + 1
    return by_rule
_DOMINANT_RATE_THRESHOLD = 0.5
_DEFAULT_DOMINANT_RATE_DENOMINATOR = "total"
def _dominant_rate_stats(rule_id: str, stats: dict, bucket: str,
                        min_sample: int,
                        denominator: str = _DEFAULT_DOMINANT_RATE_DENOMINATOR
                        ) -> dict | None:
    total = _count_or_zero(stats.get(denominator, 0))
    count = _count_or_zero(stats.get(bucket, 0))
    if (total <= 0 or total < min_sample
            or count / total <= _DOMINANT_RATE_THRESHOLD):
        return None
    ratio = count / total
    return {
        "rule_id": rule_id,
        "count": count,
        "sample_size": total,
        "rate": round(ratio * 100, 1),
        "severity": "high" if ratio > 0.75 else "medium",
        "severities": dict(
            (stats.get("severities") or {}).get(bucket) or {}),
    }
class _DominantRateSpec(NamedTuple):
    pattern_type: str
    bucket: str
    min_sample: int
    rate_key: str
    count_key: str
    description_template: str
    denominator: str = _DEFAULT_DOMINANT_RATE_DENOMINATOR
_MIN_FP_EVIDENCE_COUNT = 3
def _has_dominant_fp_evidence(fp_count: int, fp_rate: float) -> bool:
    return (fp_count >= _MIN_FP_EVIDENCE_COUNT
            and fp_rate > _DOMINANT_RATE_THRESHOLD)
_DOMINANT_RATE_SPECS = (
    _DominantRateSpec(
        "high_fp_rate_rule", "fp_confirmed", _MIN_FP_EVIDENCE_COUNT,
        "fp_rate", "fp_count",
        "规则 {rule_id} 误报率 {count}/{sample_size} ({rate:.1f}%)，"
        "诊断方法产出的该类finding大量为误报，需提高判定阈值或增加前置条件"),
    _DominantRateSpec(
        "high_rollback_rule", "rolled_back", 2, "rollback_rate",
        "rolled_back_count",
        "规则 {rule_id} 修复后回滚率 {count}/{sample_size}，"
        "修复器可能对该类问题不适用或修复逻辑有缺陷",
        denominator="executed"),
)
def _detect_dominant_rate_patterns(by_rule: dict) -> list:
    patterns = []
    for spec in _DOMINANT_RATE_SPECS:
        for rule_id, stats in by_rule.items():
            base = _dominant_rate_stats(
                rule_id, stats, spec.bucket, spec.min_sample,
                spec.denominator)
            if base is None:
                continue
            patterns.append({
                "type": spec.pattern_type,
                "rule_id": rule_id,
                spec.rate_key: base["rate"],
                spec.count_key: base["count"],
                "sample_size": base["sample_size"],
                "severity": base["severity"],
                "severities": base["severities"],
                "description": spec.description_template.format(
                    rule_id=rule_id, count=base["count"],
                    sample_size=base["sample_size"], rate=base["rate"]),
            })
    return patterns
def _fixer_exec_stats(outcomes) -> dict:
    stats = defaultdict(lambda: {"total": 0, "fixed": 0})
    for o in outcomes:
        if not o.fixer_type or o.status not in EXECUTED_STATES:
            continue
        stats[o.fixer_type]["total"] += 1
        if o.status in FIXED_STATES:
            stats[o.fixer_type]["fixed"] += 1
    return stats
def _is_weak_fixer(stats: dict) -> bool:
    total = stats["total"]
    return total >= 3 and stats["fixed"] / total < 0.3
def _detect_weak_fixer_types(outcomes) -> list:
    patterns = []
    for ftype, stats in _fixer_exec_stats(outcomes).items():
        if not _is_weak_fixer(stats):
            continue
        patterns.append({
            "type": "fixer_type_weakness",
            "fixer_type": ftype,
            "success_rate": round(stats["fixed"] / stats["total"] * 100, 1),
            "sample_size": stats["total"],
            "severity": "medium",
            "description": f"{ftype} 修复器成功率仅 {stats['fixed']}/{stats['total']}，"
                          f"修复器能力需增强",
        })
    return patterns
def _unique_rule_ids(values) -> list[str]:
    rule_ids = {_rule_id_text(value) for value in values}
    return sorted(rule_id for rule_id in rule_ids
                  if rule_id and not is_placeholder_rule_id(rule_id))
def _detect_auto_safe_mislabel(outcomes) -> list:
    false_safe = [o for o in outcomes
                  if o.auto_safe and o.status in REGRESSED_STATES]
    if not false_safe:
        return []
    return [{
        "type": "auto_safe_mislabel",
        "count": len(false_safe),
        "rule_ids": _unique_rule_ids(o.rule_id for o in false_safe),
        "severity": "high",
        "description": f"{len(false_safe)} 个标记为 auto_safe 的修复实际失败/回滚，"
                      f"auto_safe 标签不可靠",
    }]
def _is_risky_auto_safe(detail: dict) -> bool:
    return (signal_bool(detail.get("auto_safe"))
            and _status_key(detail.get("status")) in FIXED_STATES
            and str_or_empty(detail.get("fixer_type")).strip() == "eliminator"
            and is_high_severity(detail.get("severity"), "P1"))
def _collect_risky_auto_safe(details: list) -> list:
    risky_auto_safe = [d for d in details if _is_risky_auto_safe(d)]
    if not risky_auto_safe:
        return []
    return [{
        "issue_type": "risky_auto_safe_dry_run",
        "severity": "medium",
        "description": f"{len(risky_auto_safe)} 个 auto_safe 修复（eliminator+高严重度组合）可能引入副作用",
        "affected_rules": _unique_rule_ids(
            d.get("rule_id") for d in risky_auto_safe),
        "evidence": list(risky_auto_safe[:5]),
        "feedback_target": "fixer_safety",
    }]
def _collect_domain_coverage_gap(fix_route_report: dict) -> list:
    raw_cov = _fix_coverage_payload(fix_route_report)
    fix_coverage = raw_cov if isinstance(raw_cov, dict) else {}
    unfixable_rules = actionable_rule_ids(
        fix_coverage.get("unfixable_rules", []))
    if len(unfixable_rules) < 3:
        return []
    return [{
        "issue_type": "domain_fix_coverage_gap",
        "severity": "low",
        "description": f"{len(unfixable_rules)} 种规则无对应修复器，诊断-治疗域级覆盖缺口",
        "unfixable_rules": unfixable_rules[:20],
        "feedback_target": "fixer_registry",
    }]
def _regression_failed_details(details: list) -> list:
    return [d for d in details
            if _status_key(d.get("status")) == FIELD_REGRESSION_FAILED]
def _has_failed_targeted_regression(detail) -> bool:
    if not isinstance(detail, dict):
        return False
    candidates = [detail.get("targeted_regression")]
    result = detail.get("result")
    if isinstance(result, dict):
        candidates.append(result.get("targeted_regression"))
    return any(
        isinstance(regression, dict)
        and _status_key(regression.get("status")) == "failed"
        for regression in candidates)
def _regression_failed_results(details: list) -> list:
    return [d for d in details if _has_failed_targeted_regression(d)]
def _collect_regression_failed_signal(summary: dict, details: list) -> list:
    merged: list = []
    seen: set[int] = set()
    for detail in (_regression_failed_details(details)
                   + _regression_failed_results(details)):
        if id(detail) in seen:
            continue
        seen.add(id(detail))
        merged.append(detail)
    reg_details = merged
    reg_failed = _count_or_zero(summary.get(FIELD_REGRESSION_FAILED))
    if reg_failed <= 0:
        reg_failed = len(reg_details)
    if reg_failed <= 0:
        return []
    return [{
        "issue_type": "regression_test_failure_signal",
        "severity": "high",
        "description": f"{reg_failed} 项修复致回归测试失败，修复器可能引入新问题",
        "evidence": list(reg_details[:10]),
        "feedback_target": "fixer_quality",
    }]
def _collect_side_effects_signal(summary: dict, details: list) -> list:
    side_effect_details = [d for d in details
                           if _detail_side_effects(d)]
    side_effects_count = _count_or_zero(summary.get(FIELD_SIDE_EFFECTS_DETECTED))
    if side_effects_count <= 0:
        side_effects_count = sum(
            len(_detail_side_effects(d))
            for d in side_effect_details)
    safety_checks = _count_or_zero(summary.get(FIELD_SAFETY_VERIFIER_USED))
    if side_effects_count <= 0:
        return []
    return [{
        "issue_type": "fix_side_effects_detected",
        "severity": "high" if side_effects_count > 10 else "medium",
        "description": f"{side_effects_count} side effects detected during {safety_checks} safety checks",
        "side_effect_count": side_effects_count,
        "safety_checks": safety_checks,
        "evidence": list(side_effect_details[:10]),
        "feedback_target": "fixer_safety",
    }]
def _rule_distribution_issue(issue_type: str, items: list, severity: str,
                             description_fmt: str,
                             skip_label: str,
                             total_count: int | None = None) -> dict | None:
    total = (total_count if isinstance(total_count, int) and total_count > 0
             else len(items))
    if total <= 0:
        return None
    by_rule = _count_outcomes_by_rule(items, skip_label)
    return {
        "issue_type": issue_type,
        "severity": severity,
        "description": description_fmt.format(
            n=total, rules=len(by_rule)),
        "rule_distribution": dict(by_rule),
        "affected_rules": list(by_rule.keys()),
        "evidence": [o.to_dict() for o in items[:10]],
        "feedback_target": "cv_rules",
    }
def _issue_treatment_fp_confirmed(fp_confirmed_items,
                                  fp_confirmed_count: int) -> dict | None:
    count = max(fp_confirmed_count, len(fp_confirmed_items))
    issue = _rule_distribution_issue(
        "treatment_fp_confirmed", fp_confirmed_items,
        "high" if count > 50 else "medium",
        "治疗阶段确认 {n} 个误报(fp_confirmed)，涉及 {rules} 种规则，"
        "诊断方法和交叉验证需调整以减少误报产出",
        "跳过 fp 分布统计", total_count=count)
    if issue is not None:
        issue["fp_confirmed_count"] = count
    return issue
def _issue_invalid_paths(fnf_count: int, outcomes) -> dict | None:
    if fnf_count <= 0:
        return None
    fnf_outcomes = _status_outcomes(outcomes, ("file_not_found",))
    return {
        "issue_type": "diagnosis_invalid_path",
        "severity": "medium",
        "description": f"{fnf_count} 个finding的文件路径无效，诊断方法的路径输出需规范化",
        "sample_paths": [o.file for o in fnf_outcomes[:5] if o.file],
        "feedback_target": "methods",
    }
def _issue_fixer_coverage_gap(no_fixer_count: int, outcomes) -> dict | None:
    if no_fixer_count <= 0:
        return None
    no_fixer_rules = _unique_rule_ids(
        o.rule_id for o in _status_outcomes(outcomes, ("no_fixer",)))
    return {
        "issue_type": "fixer_coverage_gap",
        "severity": "medium",
        "description": f"{no_fixer_count} 个confirmed finding无对应修复器（{len(no_fixer_rules)} 种规则）",
        "unfixable_rules": no_fixer_rules,
        "feedback_target": "fixer_registry",
    }
def _status_outcomes(outcomes: list, statuses) -> list:
    return [o for o in outcomes if o.status in statuses]
class TreatmentOutcomeAnalyzer:
    def __init__(self, skill_dir: str):
        self.skill_dir = skill_dir
    def analyze(self, fix_route_report: dict) -> TreatmentOutcomeSummary:
        if not isinstance(fix_route_report, dict):
            fix_route_report = {}
        details, summary_data = _report_details_summary(fix_route_report)
        outcomes = _outcomes_from_details(details)
        total_attempted = _resolve_total_attempted(summary_data, outcomes)
        total_fixed = _summary_count(summary_data, outcomes, "auto_fixed")
        total_rolled_back = _summary_count(
            summary_data, outcomes, "fix_rolled_back")
        total_failed = _summary_count(summary_data, outcomes, "fix_failed")
        total_skipped = _summary_count(summary_data, outcomes, "needs_review")
        total_no_fixer = _summary_count(summary_data, outcomes, "no_fixer")
        total_file_not_found = _summary_count(
            summary_data, outcomes, "file_not_found")
        total_fp_confirmed = _summary_count(
            summary_data, outcomes, "fp_confirmed")
        success_rate = _rate_pct(total_fixed, total_attempted)
        rollback_rate = _rate_pct(total_rolled_back, total_attempted)
        fp_rate = _rate_pct(
            total_fp_confirmed, total_attempted + total_fp_confirmed)
        failure_patterns = self._detect_failure_patterns(outcomes)
        issues_discovered = self._discover_issues(
            outcomes, details, summary_data, fix_route_report, total_attempted)
        side_effects_summary = _summarize_side_effects(outcomes)
        result = TreatmentOutcomeSummary(
            total_attempted=total_attempted,
            total_fixed=total_fixed,
            total_rolled_back=total_rolled_back,
            total_failed=total_failed,
            total_skipped=total_skipped,
            total_no_fixer=total_no_fixer,
            total_file_not_found=total_file_not_found,
            total_fp_confirmed=total_fp_confirmed,
            success_rate=success_rate,
            rollback_rate=rollback_rate,
            fp_rate=fp_rate,
            failure_patterns=failure_patterns,
            issues_discovered=issues_discovered,
            side_effects_summary=side_effects_summary,
        )
        logger.info(
            "[TreatmentOutcome] 修复: %d/%d (%.1f%%), 回滚: %d (%.1f%%), 失败: %d, 无修复器: %d, 误报: %d (%.1f%%)",
            total_fixed, total_attempted, success_rate,
            total_rolled_back, rollback_rate,
            total_failed, total_no_fixer,
            total_fp_confirmed, fp_rate,
        )
        return result
    def _detect_failure_patterns(self, outcomes: list[TreatmentOutcome]) -> list[dict]:
        by_rule = _group_outcomes_by_rule(outcomes)
        return (_detect_dominant_rate_patterns(by_rule)
                + _detect_weak_fixer_types(outcomes)
                + _detect_auto_safe_mislabel(outcomes))
    def _discover_issues(self, outcomes: list[TreatmentOutcome],
                         details: list, summary_data: dict,
                         fix_route_report: dict, total_attempted: int) -> list[dict]:
        issues = []
        fp_confirmed_items = _status_outcomes(outcomes, ("fp_confirmed",))
        fp_confirmed_count = _summary_count(
            summary_data, outcomes, "fp_confirmed")
        false_positives = _status_outcomes(outcomes, REGRESSED_STATES)
        fnf_count = _summary_count(summary_data, outcomes, "file_not_found")
        no_fixer_count = _summary_count(summary_data, outcomes, "no_fixer")
        for _issue in (
            _issue_treatment_fp_confirmed(
                fp_confirmed_items, fp_confirmed_count),
            _rule_distribution_issue(
                "diagnosis_false_positive", false_positives, "high",
                "交叉验证confirmed的 {n} 个finding在修复中失败/回滚，"
                "可能是诊断误报或修复器能力不足",
                "跳过规则分布统计"),
            _issue_invalid_paths(fnf_count, outcomes),
            _issue_fixer_coverage_gap(no_fixer_count, outcomes),
            _low_fixer_coverage_issue(fix_route_report, total_attempted),
        ):
            if _issue is not None:
                issues.append(_issue)
        issues.extend(
            _collect_risky_auto_safe(details)
            + _collect_domain_coverage_gap(fix_route_report)
            + _collect_regression_failed_signal(summary_data, details)
            + _collect_side_effects_signal(summary_data, details))
        return issues
_CV_THRESHOLD_KEY_PREFIX = "CV-CONFIDENCE-"
_CV_THRESHOLD_KEY_FORMS = (_CV_THRESHOLD_KEY_PREFIX, "CONFIDENCE_")
def _cv_target_parts(target_id) -> tuple[str, str]:
    if not isinstance(target_id, str):
        return "", ""
    text = target_id.strip()
    form = next((p for p in _CV_THRESHOLD_KEY_FORMS if text.startswith(p)), "")
    if form:
        return form, text[len(form):].strip()
    return "", strip_cv_target_prefix(text).strip()
def _cv_threshold_key(target_id) -> str | None:
    form, rule_id = _cv_target_parts(target_id)
    if (not form or is_placeholder_rule_id(rule_id)
            or rule_id in AGGREGATE_CV_TARGETS):
        return None
    return f"{_CV_THRESHOLD_KEY_PREFIX}{rule_id}"
class _AdjustmentRule(NamedTuple):
    evidence_kind: str
    reason_default: str
    relaxation_types: tuple[str, ...]
    tightening_types: tuple[str, ...]
    up_on_relaxation: bool
    baseline: float
def _read_approved_adjustments(skill_dir: str) -> dict:
    try:
        approved = read_evolution_section(skill_dir, "approved_adjustments")
    except (OSError, ValueError, TypeError) as exc:
        logger.warning(
            "[FeedbackApplier] AI审核生效调整 section 读取失败，回退基础调整: %s",
            exc)
        return {}
    if not isinstance(approved, dict):
        if approved:
            logger.warning(
                "[FeedbackApplier] AI审核生效调整顶层非对象(%s)，回退基础调整",
                type(approved).__name__)
        return {}
    return approved
class FeedbackApplier:
    @staticmethod
    def _dict_section(container: dict, key: str) -> dict:
        section = container.get(key)
        if not isinstance(section, dict):
            section = {}
            container[key] = section
        return section
    def __init__(self, skill_dir: str):
        self.skill_dir = skill_dir
        self._history_path = "feedback_history"
        self._adjustments_path = "method_adjustments"
        self._history = normalize_feedback_history(self._load_json_dict(
            self._history_path, default_feedback_history,
            "反馈历史(feedback_history.json)", propagate_io=True))
        self._adjustments = self._load_json_dict(
            self._adjustments_path, default_method_adjustments,
            "方法调整配置(method_adjustments.json)")
        for key in (FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
                    FIELD_CV_CONFIDENCE_THRESHOLDS,
                    "fixer_safety_overrides"):
            self._dict_section(self._adjustments, key)
        self._approved_adjustments = _read_approved_adjustments(skill_dir)
        self._reset_session_adjustments()
        self._adjustment_evidence: dict[tuple, dict] = {}
    DECAY_HALF_LIFE_DAYS = 30
    DECAY_FLOOR = 0.1
    RECOVERY_THRESHOLD = 3
    RECOVERY_RATE = 0.02
    MAX_CUMULATIVE_ADJUST = 0.4
    _NUMERIC_ADJUSTMENT_FIELDS = (
        FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
        FIELD_CV_CONFIDENCE_THRESHOLDS,
    )
    _now_ts = None
    METHOD_MULTIPLIER_BASELINE = 1.0
    CV_CONFIDENCE_BASELINE = 0.6
    _METHOD_ADJUSTMENT_RULE = _AdjustmentRule(
        evidence_kind="method_confidence_multiplier",
        reason_default="诊断方法反馈触发置信度乘数调整",
        relaxation_types=("false_negative", "low_recall", "missed_detection"),
        tightening_types=("false_positive", "threshold_adjust"),
        up_on_relaxation=True,
        baseline=METHOD_MULTIPLIER_BASELINE,
    )
    _CV_ADJUSTMENT_RULE = _AdjustmentRule(
        evidence_kind="cv_confidence_threshold",
        reason_default="CV 规则反馈触发置信度阈值调整",
        relaxation_types=("false_negative", "low_recall", "over_suppression"),
        tightening_types=("false_positive", "weight_adjust",
                          "threshold_adjust"),
        up_on_relaxation=False,
        baseline=CV_CONFIDENCE_BASELINE,
    )
    @classmethod
    def _decay_factor(cls, days_elapsed: float) -> float:
        raw = (1 - cls.DECAY_FLOOR) * (0.5 ** (days_elapsed / cls.DECAY_HALF_LIFE_DAYS))
        return cls.DECAY_FLOOR + raw
    def _parse_timestamp_days(self, ts: str) -> float:
        try:
            then = _dt.datetime.fromisoformat(ts)
            if self._now_ts:
                now = _dt.datetime.fromisoformat(self._now_ts)
                if now.tzinfo is None and then.tzinfo is not None:
                    now = now.replace(tzinfo=then.tzinfo)
                elif now.tzinfo is not None and then.tzinfo is None:
                    then = then.replace(tzinfo=now.tzinfo)
            else:
                now = (_dt.datetime.now(then.tzinfo) if then.tzinfo is not None
                       else _dt.datetime.now())
            delta = (now - then).total_seconds() / 86400.0
            return max(0.0, delta)
        except (ValueError, TypeError) as te:
            logger.warning("treatment_feedback: timestamp parse failed: %s", te)
            return float("inf")
    def _decay_context(self, history, adj, hist_field, adj_field, sub_key):
        hist_map = history.get(hist_field, {})
        if not isinstance(hist_map, dict):
            hist_map = {}
        container = self._dict_section(adj, adj_field)
        entries = []
        for key in list(container.keys()):
            hist_entry = hist_map.get(key, {})
            if not isinstance(hist_entry, dict):
                hist_entry = {}
            sub = hist_entry.get(sub_key, [])
            if not isinstance(sub, list):
                sub = []
            entries.append((key, hist_entry, sub))
        return container, entries
    def _last_entry_decay(self, records):
        last = records[-1] if records else {}
        if not isinstance(last, dict):
            last = {}
        return self._decay_factor(
            self._parse_timestamp_days(last.get("timestamp", "")))
    @staticmethod
    def _effective_count(hist_entry, decay):
        return _count_or_zero(hist_entry.get(FIELD_TRIGGER_COUNT)) * decay
    def _recover_toward_default(self, container, key, current, target, label):
        if abs(current - target) <= 1e-9:
            return
        step = min(self.RECOVERY_RATE, abs(target - current))
        new_val = current + step if current < target else current - step
        container[key] = round(new_val, 3)
        if abs(container[key] - target) < 0.01:
            del container[key]
            logger.debug("[FeedbackDecay] %s %s已恢复默认", key, label)
        else:
            logger.debug("[FeedbackDecay] %s %s向默认恢复 → %.3f", key, label, container[key])
    def _decay_sections(self):
        return (
            (self._decay_context(
                self._history, self._adjustments, FIELD_METHOD_THRESHOLDS,
                FIELD_METHOD_CONFIDENCE_MULTIPLIERS, LIST_SUGGESTIONS),
             self.METHOD_MULTIPLIER_BASELINE, "置信度乘数", "乘数"),
            (self._decay_context(
                self._history, self._adjustments, FIELD_CV_RULE_WEIGHTS,
                FIELD_CV_CONFIDENCE_THRESHOLDS, LIST_ADJUSTMENTS),
             self.CV_CONFIDENCE_BASELINE, "CV阈值", "CV阈值"),
        )
    def _decay_section(self, container, entries, target, recover_label,
                       log_label) -> None:
        for key, hist_entry, records in entries:
            if not records:
                del container[key]
                continue
            decay = self._last_entry_decay(records)
            effective_count = self._effective_count(hist_entry, decay)
            current = container[key]
            if not is_finite_num(current):
                logger.warning("[FeedbackDecay] %s %s非数值(%s)，跳过衰减处理",
                               key, log_label, type(current).__name__)
                continue
            if effective_count < self.RECOVERY_THRESHOLD:
                self._recover_toward_default(
                    container, key, current, target, recover_label)
            else:
                logger.debug("[FeedbackDecay] %s 有效计数 %.1f (衰减%.2f), %s保持 %.3f",
                             key, effective_count, decay, log_label, current)
    def _prune_safety_overrides(self) -> None:
        safety, entries = self._decay_context(
            self._history, self._adjustments,
            HISTORY_FIXER_SECTION, "fixer_safety_overrides", LIST_FEEDBACKS)
        for key, _hist_entry, feedbacks in entries:
            if not feedbacks:
                del safety[key]
                logger.debug("[FeedbackDecay] %s 安全覆盖无历史记录移除", key)
            elif self._last_entry_decay(feedbacks) < 0.3:
                del safety[key]
                logger.debug("[FeedbackDecay] %s 安全覆盖已过期移除", key)
    def _decay_and_recover_adjustments(self):
        for (container, entries), target, recover_label, log_label in self._decay_sections():
            self._decay_section(container, entries, target, recover_label, log_label)
        self._prune_safety_overrides()
    def _enforce_cumulative_limits(self):
        for section_key, lo, hi, label in self._clamp_windows():
            self._clamp_section(self._dict_section(self._adjustments, section_key), lo, hi, label)
    @classmethod
    def _clamp_windows(cls) -> tuple:
        span = cls.MAX_CUMULATIVE_ADJUST
        return (
            (FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
             cls.METHOD_MULTIPLIER_BASELINE - span,
             cls.METHOD_MULTIPLIER_BASELINE + span, "乘数"),
            (FIELD_CV_CONFIDENCE_THRESHOLDS,
             cls.CV_CONFIDENCE_BASELINE - span,
             cls.CV_CONFIDENCE_BASELINE + span, "阈值"),
        )
    @staticmethod
    def _clamp_section(section: dict, lo: float, hi: float, label: str) -> None:
        for key, val in section.items():
            if not is_finite_num(val):
                logger.warning("[FeedbackLimit] %s %s非数值(%s)，跳过钳位",
                               key, label, type(val).__name__)
                continue
            if val < lo:
                section[key] = round(lo, 3)
                logger.warning("[FeedbackLimit] %s %s被下限保护钳位 → %.3f",
                               key, label, lo)
            elif val > hi:
                section[key] = round(hi, 3)
                logger.warning("[FeedbackLimit] %s %s被上限保护钳位 → %.3f",
                               key, label, hi)
    def _load_json_dict(self, section: str, default_factory, label: str,
                        propagate_io: bool = _DEFAULT_PROPAGATE_IO) -> dict:
        default = default_factory()
        try:
            data = read_evolution_section(section and self.skill_dir,
                                          section)
        except (OSError, ValueError, TypeError) as exc:
            if propagate_io:
                raise
            logger.warning("[FeedbackApplier] %s 读取失败，按默认值继续: %s",
                           label, exc)
            return default
        return data if isinstance(data, dict) else default
    def get_adjustments(self) -> dict:
        return self._adjustments
    def apply(self, feedbacks: list[DiagnosisFeedback],
              outcome_summary: TreatmentOutcomeSummary | None = None) -> FeedbackReport:
        self._decay_and_recover_adjustments()
        self._enforce_cumulative_limits()
        self._reset_session_adjustments()
        if isinstance(feedbacks, (list, tuple)):
            feedbacks = list(feedbacks)
        else:
            logger.warning(
                "[FeedbackApplier] feedbacks 非法形态(%s)，归一空列表处理",
                type(feedbacks).__name__)
            feedbacks = []
        feedbacks = [_normalize_feedback_identity(fb) for fb in feedbacks]
        diagnosis_feedbacks = []
        cv_feedbacks = []
        fixer_feedbacks = []
        handlers = {
            "method": (self._apply_method_feedback, diagnosis_feedbacks),
            "cv_rule": (self._apply_cv_feedback, cv_feedbacks),
            "fixer": (self._apply_fixer_feedback, fixer_feedbacks),
        }
        applied_count = sum(
            1 for fb in feedbacks if self._apply_one_feedback(fb, handlers))
        self._record_session(outcome_summary, len(feedbacks), applied_count)
        report_ai_adjustment_proposals(
            self.skill_dir,
            self._dict_section(
                self._adjustments, FIELD_METHOD_CONFIDENCE_MULTIPLIERS),
            self._dict_section(
                self._adjustments, FIELD_CV_CONFIDENCE_THRESHOLDS),
            self._dict_section(self._adjustments, "fixer_safety_overrides"),
            outcome_summary,
            self._adjustment_evidence)
        bridged = bridge_feedbacks_to_enhancement_log(
            self.skill_dir, feedbacks, outcome_summary)
        report = FeedbackReport(
            timestamp=time.strftime(FMT_DATETIME_ISO),
            treatment_summary=summary_dict(outcome_summary),
            diagnosis_feedbacks=diagnosis_feedbacks,
            cv_feedbacks=cv_feedbacks,
            fixer_feedbacks=fixer_feedbacks,
            applied_count=applied_count,
            pending_count=len(feedbacks) - applied_count,
        )
        logger.info(
            "[FeedbackApplier] 应用 %d/%d 条反馈，桥接 %d 条到enhancement_log，历史session: %d",
            applied_count, len(feedbacks), bridged, self._history["session_count"],
        )
        return report
    def _apply_one_feedback(self, fb: DiagnosisFeedback, handlers: dict) -> bool:
        if not isinstance(fb, DiagnosisFeedback):
            logger.warning(
                "[FeedbackApplier] 反馈条目非 DiagnosisFeedback(%s)，跳过应用",
                type(fb).__name__)
            return False
        target_id = fb.target_id
        if not isinstance(target_id, str) or not target_id.strip():
            logger.warning(
                "[FeedbackApplier] 反馈 target_id 非法(%r)，跳过应用",
                target_id)
            return False
        target_type = fb.target_type
        if not isinstance(target_type, str):
            logger.warning(
                "[FeedbackApplier] 反馈 target_type 非法(%s)，跳过应用",
                type(target_type).__name__)
            return False
        handler = handlers.get(target_type)
        if handler is None:
            return False
        apply_fn, bucket = handler
        apply_fn(fb)
        bucket.append(fb.to_dict())
        return True
    def _record_session(self, outcome_summary, feedback_count: int,
                        applied_count: int) -> None:
        self._history["session_count"] += 1
        self._history["sessions"].append({
            "timestamp": time.strftime(FMT_DATETIME_ISO),
            "round_start_ts": peek_round_start_ts(self.skill_dir),
            "outcome_summary": summary_dict(outcome_summary),
            "feedback_count": feedback_count,
            "applied_count": applied_count,
        })
        self._history["sessions"] = self._history["sessions"][-50:]
        self._save_history()
    def _touch_history_entry(self, section_key, key, list_field, count_field,
                             record):
        section = self._dict_section(self._history, section_key)
        entry = section.get(key)
        if not isinstance(entry, dict):
            entry = {}
        if not isinstance(entry.get(list_field), list):
            entry[list_field] = []
        n = _count_or_zero(entry.get(count_field))
        entry[count_field] = n + 1
        entry[list_field].append(record)
        entry[list_field] = entry[list_field][-20:]
        section[key] = entry
        return entry
    @staticmethod
    def _feedback_record(fb: DiagnosisFeedback, **extra) -> dict:
        record = {
            "timestamp": time.strftime(FMT_DATETIME_ISO),
            "feedback_type": fb.feedback_type,
            "reason": fb.reason,
            "confidence": float_metric(fb.confidence),
        }
        record.update(extra)
        return record
    def _reset_session_adjustments(self) -> None:
        self._session_adjustments = {
            key: {} for key in self._NUMERIC_ADJUSTMENT_FIELDS}
    def _effective_adjustment_section(self, section_key: str,
                                      base_section: dict) -> dict:
        return {
            **dict_or_empty(base_section),
            **dict_or_empty(self._approved_adjustments.get(section_key)),
            **dict_or_empty(self._session_adjustments.get(section_key)),
        }
    @staticmethod
    def _current_or_baseline(section: dict, key: str, baseline: float) -> float:
        current = section.get(key, baseline)
        return current if is_finite_num(current) else baseline
    @staticmethod
    def _confidence_step(conf):
        if conf >= 0.9:
            return 0.15
        if conf >= 0.7:
            return 0.10
        return 0.05
    def _directional_value(self, current: float, conf: float,
                           feedback_type: str, *,
                           rule: _AdjustmentRule) -> float | None:
        low = rule.baseline - self.MAX_CUMULATIVE_ADJUST
        high = rule.baseline + self.MAX_CUMULATIVE_ADJUST
        if feedback_type in rule.relaxation_types:
            step = 0.05
            direction = 1 if rule.up_on_relaxation else -1
        elif feedback_type in rule.tightening_types:
            step = self._confidence_step(conf)
            direction = -1 if rule.up_on_relaxation else 1
        else:
            return None
        adjusted = current + direction * step
        return round(min(high, max(low, adjusted)), 3)
    def _commit_directional_adjustment(
            self, fb: DiagnosisFeedback, *, section: dict, entry: dict,
            conf: float, rule: _AdjustmentRule, section_key: str,
            key: str | None = None) -> bool:
        target = fb.target_id if key is None else key
        if is_placeholder_rule_id(strip_cv_target_prefix(target)):
            logger.warning(
                "[FeedbackApplier] 调整目标 %r 为占位规则（空/UNKNOWN），仅记录趋势不写入调整",
                target)
            return False
        current = self._current_or_baseline(
            self._effective_adjustment_section(section_key, section),
            target, rule.baseline)
        new_value = self._directional_value(
            current, conf, fb.feedback_type, rule=rule)
        if new_value is None:
            return False
        section[target] = new_value
        self._session_adjustments[section_key][target] = new_value
        self._adjustment_evidence[(rule.evidence_kind, target)] = {
            "reason": fb.reason or rule.reason_default,
            "feedback_type": fb.feedback_type,
            "confidence": conf,
            FIELD_TRIGGER_COUNT: entry.get(FIELD_TRIGGER_COUNT, 1),
            "previous_value": current,
        }
        return True
    def _apply_method_feedback(self, fb: DiagnosisFeedback):
        key = fb.target_id
        entry = self._touch_history_entry(
            FIELD_METHOD_THRESHOLDS, key, LIST_SUGGESTIONS, FIELD_TRIGGER_COUNT,
            self._feedback_record(
                fb, **{FIELD_SUGGESTED_VALUE: fb.suggested_value}))
        adj = self._dict_section(self._adjustments, FIELD_METHOD_CONFIDENCE_MULTIPLIERS)
        conf = float_metric(fb.confidence)
        if entry[FIELD_TRIGGER_COUNT] >= 2 and conf > 0.6:
            self._commit_directional_adjustment(
                fb, section=adj, entry=entry, conf=conf,
                rule=self._METHOD_ADJUSTMENT_RULE,
                section_key=FIELD_METHOD_CONFIDENCE_MULTIPLIERS)
    def _apply_cv_feedback(self, fb: DiagnosisFeedback):
        key = _cv_threshold_key(fb.target_id)
        adj = self._dict_section(self._adjustments, FIELD_CV_CONFIDENCE_THRESHOLDS)
        cvw_entry = self._touch_history_entry(
            FIELD_CV_RULE_WEIGHTS, fb.target_id if key is None else key,
            LIST_ADJUSTMENTS, FIELD_TRIGGER_COUNT, self._feedback_record(fb))
        if key is None:
            return
        if fb.feedback_type == "over_suppression":
            # 过度抑制反馈作用在 L4 抑制规则（收集阶段），而确认阈值
            # 作用在 CV 阶段（更下游）。不撤销规则时，被抑制的 finding
            # 根本到不了阈值判定，反馈永远修不到问题。
            _rule_id = _cv_target_parts(fb.target_id)[1]
            if drop_fp_suppression_rule(self.skill_dir, _rule_id):
                logger.info(
                    "[FeedbackApplier] 过度抑制反馈已撤销抑制规则: rule=%s",
                    _rule_id)
        conf = float_metric(fb.confidence)
        if cvw_entry[FIELD_TRIGGER_COUNT] >= 2 and conf > 0.5:
            self._commit_directional_adjustment(
                fb, section=adj, entry=cvw_entry, conf=conf,
                rule=self._CV_ADJUSTMENT_RULE,
                section_key=FIELD_CV_CONFIDENCE_THRESHOLDS, key=key)
    def _apply_fixer_feedback(self, fb: DiagnosisFeedback):
        key = fb.target_id
        fn_entry = self._touch_history_entry(
            HISTORY_FIXER_SECTION, key, LIST_FEEDBACKS, FIELD_REQUEST_COUNT,
            self._feedback_record(fb))
        if fb.feedback_type == "safety_mislabel":
            safety_adj = self._dict_section(self._adjustments, "fixer_safety_overrides")
            if (fb.target_id != AUTO_SAFE_REGISTRY_TARGET
                    and not is_placeholder_rule_id(fb.target_id)):
                safety_adj[fb.target_id] = {"auto_safe": False, "reason": fb.reason}
                self._adjustment_evidence[("fixer_safety_override", fb.target_id)] = {
                    "reason": fb.reason or "修复器标记 auto_safe 但修复实际失败/回滚",
                    "feedback_type": fb.feedback_type,
                    "confidence": float_metric(fb.confidence),
                    FIELD_TRIGGER_COUNT: fn_entry.get(FIELD_REQUEST_COUNT, 1),
                }
    def _save_history(self):
        try:
            if not write_evolution_section(
                    self.skill_dir, "feedback_history", self._history):
                logger.warning("[FeedbackApplier] 反馈历史 section 落盘失败: %s",
                               self.skill_dir)
        except (OSError, ValueError, TypeError) as e:
            logger.warning("[FeedbackApplier] 保存反馈历史失败: %s", e)
def _normalize_feedback_identity(fb):
    if not isinstance(fb, DiagnosisFeedback):
        return fb
    target_id = (fb.target_id.strip()
                 if isinstance(fb.target_id, str) else fb.target_id)
    target_type = (fb.target_type.strip().lower()
                   if isinstance(fb.target_type, str) else fb.target_type)
    feedback_type = (fb.feedback_type.strip().lower()
                     if isinstance(fb.feedback_type, str)
                     else fb.feedback_type)
    if (target_id == fb.target_id and target_type == fb.target_type
            and feedback_type == fb.feedback_type):
        return fb
    return replace(fb, target_id=target_id, target_type=target_type,
                   feedback_type=feedback_type)
def get_effective_adjustments(skill_dir: str) -> dict:
    applier = FeedbackApplier(skill_dir)
    approved = applier._approved_adjustments
    if not approved:
        return dict(applier.get_adjustments())
    return _merge_approved_adjustments(applier.get_adjustments(), approved)
_MERGED_ADJUSTMENT_KEYS = (
    FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
    FIELD_CV_CONFIDENCE_THRESHOLDS,
    "fixer_safety_overrides",
    "misc",
)
def _merge_approved_adjustments(base: dict, approved: dict) -> dict:
    merged = dict(base)
    for key in _MERGED_ADJUSTMENT_KEYS:
        patch = dict_or_empty(approved.get(key))
        if not patch:
            continue
        merged[key] = {**dict_or_empty(merged.get(key)), **patch}
    merged["last_updated"] = (approved.get("last_updated")
                              or merged.get("last_updated", ""))
    return merged
def report_ai_adjustment_proposals(
        skill_dir: str, muls: dict, cvs: dict, fixs: dict,
        outcome_summary: TreatmentOutcomeSummary | None = None,
        evidence: dict | None = None) -> None:
    muls, cvs, fixs = (dict_or_empty(muls), dict_or_empty(cvs),
                       dict_or_empty(fixs))
    queue_note = (
        " —— 已入待审队列，由 AI 审核并执行（apply_approved_adjustment 采纳生效）"
    )
    for _label, _raw, _vals in (
        ("方法置信度乘数", muls,
         {k: v for k, v in muls.items() if k != "last_updated"}),
        ("CV置信度阈值", cvs,
         {k: v for k, v in cvs.items() if k != "last_updated"}),
        ("修复器安全标签", fixs,
         {k: v for k, v in fixs.items() if k != "last_updated"}),
    ):
        if _raw:
            logger.info(
                "[FeedbackApplier] [AI审核执行] 建议调整%s %s%s",
                _label, _vals, queue_note)
    try:
        sync_adjustment_proposals(
            skill_dir, muls, cvs, fixs,
            build_treatment_context(outcome_summary),
            load_retrospective_context(skill_dir),
            evidence if evidence is not None else {})
    except (OSError, ValueError, TypeError, RuntimeError) as pe:
        logger.warning("[FeedbackApplier] 调整建议落盘跳过: %s", pe, exc_info=True)
def _read_report_json(path: str) -> tuple[dict | None, str | None]:
    try:
        with open(path, encoding="utf-8-sig") as f:
            loaded = json.load(f)
        if not isinstance(loaded, dict):
            return None, f"顶层非对象({type(loaded).__name__})，要求 JSON 对象"
        return loaded, None
    except (OSError, ValueError, RecursionError) as e:
        log_swallowed(
            __name__, e,
            context=f'_read_report_json:{type(e).__name__}')
        return None, str(e)
_BRIDGE_DESC_PREFIX = f"{_MODULE_NAME}桥接: "
_BRIDGE_SOURCE = _MODULE_NAME
_BRIDGE_SUPPRESSION_SOURCE = f"{_MODULE_NAME}_bridge"
@dataclass(frozen=True)
class _SuppressionSpec:
    rule_id: str
    fp_count: int
    fp_rate: float
    min_severity: str
    message_patterns: list = field(default_factory=list)
    confidence: float = 0.0
    severities: dict = field(default_factory=dict)
    sample_files: list = field(default_factory=list)
def _pending_targets_from(entries: list) -> set:
    targets = set()
    for entry in entries:
        if not isinstance(entry, dict) or _status_key(
                entry.get("status")) != "pending":
            continue
        target = entry.get("target")
        if isinstance(target, str) and target.strip():
            targets.add(target.strip())
    return targets
def bridge_feedbacks_to_enhancement_log(
    skill_dir: str,
    feedbacks: list[DiagnosisFeedback],
    outcome_summary: TreatmentOutcomeSummary | None = None,
) -> int:
    if isinstance(feedbacks, (list, tuple)):
        feedbacks = list(feedbacks)
    else:
        if feedbacks:
            logger.warning(
                "[FeedbackApplier] feedbacks 非法形态(%s)，按空列表处理",
                type(feedbacks).__name__)
        feedbacks = []
    feedbacks = [_normalize_feedback_identity(fb) for fb in feedbacks]
    try:
        with _required_write_lock(skill_dir):
            enh_data, entries = _load_enh_log(skill_dir)
            if enh_data is None:
                logger.warning(
                    "[FeedbackApplier] enhancement_log 不可读（IO/内容损坏），"
                    "保留原文件并跳过本轮桥接写盘")
                return 0
            fp_from_state = _load_fp_state(skill_dir)
            fp_patterns = _extract_fp_patterns(outcome_summary)
            bridged = 0
            entry_start = len(entries)
            now = time.strftime(FMT_DATETIME)
            prov_base = _prov_base(skill_dir, outcome_summary)
            bridged += _bridge_state_entries(
                entries, fp_from_state, now, prov_base)
            bridged += _bridge_feedbacks(
                feedbacks, entries, fp_patterns, now, prov_base)
            return _persist_bridge_result(
                skill_dir, enh_data, bridged, entries[entry_start:], now)
    except (OSError, ValueError, RecursionError) as exc:
        logger.warning(
            "[FeedbackApplier] enhancement_log 桥接读写失败，跳过本轮写盘: %s",
            exc)
        return 0
def _persist_bridge_result(skill_dir: str, enh_data: dict, bridged: int,
                           bridged_entries: list, now: str) -> int:
    if bridged <= 0:
        return 0
    _append_bridge_session(enh_data, bridged, bridged_entries, now)
    if not _write_enh_log(skill_dir, enh_data):
        return 0
    logger.info("[FeedbackApplier] 桥接 %d 条FP反馈到enhancement_log", bridged)
    return bridged
def _append_bridge_session(enh_data: dict, bridged: int,
                           bridged_entries: list, now: str) -> None:
    sessions = enh_data.get("sessions")
    if not isinstance(sessions, list):
        sessions = []
    top_rules = list(dict.fromkeys(
        entry["rule_id"] for entry in bridged_entries
        if isinstance(entry, dict)
        and isinstance(entry.get("rule_id"), str) and entry["rule_id"]))
    sessions.append({
        "timestamp": now,
        "type": _BRIDGE_SUPPRESSION_SOURCE,
        "bridged_count": bridged,
        "top_rules": top_rules[:10],
    })
    enh_data["sessions"] = sessions
def _write_enh_log(skill_dir: str, enh_data: dict) -> bool:
    try:
        save_enhancement_log(skill_dir, enh_data)
        return True
    except (OSError, ValueError, RecursionError) as e:
        logger.warning("[FeedbackApplier] enhancement_log桥接写入失败: %s", e)
        return False
def build_treatment_context(
        outcome_summary: TreatmentOutcomeSummary | None) -> dict:
    os_dict = summary_dict(outcome_summary)
    return {
        "total_attempted": _count_or_zero(os_dict.get("total_attempted")),
        "total_fixed": _count_or_zero(os_dict.get("total_fixed")),
        "total_failed": _count_or_zero(os_dict.get("total_failed")),
        "total_rolled_back": _count_or_zero(os_dict.get("total_rolled_back")),
        "total_fp_confirmed": _count_or_zero(os_dict.get("total_fp_confirmed")),
        "fp_rate": min(100.0, max(0.0, safe_float(
            os_dict.get("fp_rate")))),
        "rollback_rate": min(100.0, max(0.0, safe_float(
            os_dict.get("rollback_rate")))),
    }
def _prov_base(skill_dir: str,
                outcome_summary: TreatmentOutcomeSummary | None) -> dict:
    prov = {
        "phase": "treatment_feedback",
        "treatment_context": build_treatment_context(outcome_summary),
    }
    prov["round_start_ts"] = peek_round_start_ts(skill_dir)
    rv_ctx = load_retrospective_context(skill_dir)
    if rv_ctx:
        prov["retrospective_context"] = rv_ctx
    return prov
def _entry_prov(prov_base: dict | None, spec: _SuppressionSpec,
                desc: str) -> dict:
    rid = spec.rule_id
    base = prov_base if isinstance(prov_base, dict) else {}
    tc = dict(base.get("treatment_context") or {})
    tc.update({"rule_fp_confirmed": spec.fp_count,
               "rule_fp_rate": spec.fp_rate})
    if spec.severities:
        tc["severities"] = spec.severities
        tc["sample_files"] = spec.sample_files or []
    prov = {
        "phase": base.get("phase", "treatment_feedback"),
        "diagnosis_context": {"rule_id": rid, "severity": "",
                              "description": desc},
        "treatment_context": tc,
    }
    if "round_start_ts" in base:
        prov["round_start_ts"] = base["round_start_ts"]
    rv = base.get("retrospective_context")
    if rv:
        prov["retrospective_context"] = rv
    return prov
def _fp_rule_accumulate(info: dict, item: dict) -> None:
    info["count"] += 1
    sev = normalize_item_severity(item.get("severity"))
    info["severities"][sev] = info["severities"].get(sev, 0) + 1
    msg = str_or_empty(item.get("message"))
    if not msg:
        result = item.get("result")
        if isinstance(result, dict):
            msg = str_or_empty(result.get("reason"))
    sample = msg[:200]
    if sample and len(info["samples"]) < 3 and sample not in info["samples"]:
        info["samples"].append(sample)
    fpath = str_or_empty(item.get("file_path")) or str_or_empty(item.get("file"))
    if fpath and len(info["files"]) < 5 and fpath not in info["files"]:
        info["files"].append(fpath)
def _aggregate_feedback_fp_by_rule(items) -> dict:
    fp_by_rule = {}
    items = items if isinstance(items, (list, tuple)) else []
    fp_items = [
        item for item in items
        if isinstance(item, dict)
        and _status_key(item.get("status")) == "fp_confirmed"
    ]
    for _rid, item in iter_unique_rule_observations(fp_items):
        rid = str_or_empty(item.get("rule_id")).strip()
        if is_placeholder_rule_id(rid):
            continue
        if rid not in fp_by_rule:
            fp_by_rule[rid] = {"count": 0, "severities": {}, "samples": [], "files": []}
        _fp_rule_accumulate(fp_by_rule[rid], item)
    return fp_by_rule
def _count_feedback_items_per_rule(items) -> dict:
    totals = {}
    items = items if isinstance(items, (list, tuple)) else []
    for _rid, item in iter_unique_rule_observations(items):
        rid = str_or_empty(item.get("rule_id")).strip()
        if not rid or is_placeholder_rule_id(rid):
            continue
        totals[rid] = totals.get(rid, 0) + 1
    return totals
def _feedback_tracker_fp_rate(tracker: dict, rid: str):
    entry = tracker.get(rid, {}) if isinstance(tracker, dict) else {}
    if not isinstance(entry, dict) or cv_int(entry.get("total", 0)) <= 0:
        return None
    rate = entry.get("fp_rate")
    if not is_finite_num(rate):
        return None
    parsed = float(rate)
    return parsed if 0.0 < parsed <= 1.0 else None
def _feedback_rule_fp_rate(rid: str, fp_count: int, total: int,
                            tracker: dict) -> float:
    rate = fp_count / total if total > 0 else 0.0
    override = _feedback_tracker_fp_rate(tracker, rid)
    return rate if override is None else override
def _load_fp_state(skill_dir: str) -> list:
    items = [item for item in load_treatment_items_for_evidence(skill_dir)
             if isinstance(item, dict)]
    fp_by_rule = _aggregate_feedback_fp_by_rule(items)
    totals = _count_feedback_items_per_rule(items)
    try:
        tracker = load_fp_tracker_rates(skill_dir)
    except OSError as _te:
        log_swallowed(__name__, _te, context='_load_fp_state:OSError')
        tracker = {}
    for rid, info in fp_by_rule.items():
        total = totals.get(rid, info["count"])
        info["total"] = total
        info["fp_rate"] = _feedback_rule_fp_rate(
            rid, info["count"], total, tracker)
    fp_from_state = [
        (rid, info) for rid, info in fp_by_rule.items()
        if _has_dominant_fp_evidence(info["count"], info["fp_rate"])
    ]
    if fp_from_state:
        logger.info("[FeedbackApplier] 从治疗状态读取 %d 条fp_confirmed规则",
                    len(fp_from_state))
    return fp_from_state
def _load_enh_log(skill_dir: str) -> tuple[dict | None, list]:
    enh_data, _readable = read_enhancement_log(
        skill_dir, label="FeedbackApplier")
    if enh_data is None:
        return None, []
    return enh_data, normalized_enhancement_entries(enh_data)
def _fp_pattern_entry(pattern) -> tuple[str, dict] | None:
    if not (isinstance(pattern, dict)
            and pattern.get("type") == "high_fp_rate_rule"):
        return None
    rid_raw = pattern.get("rule_id", "")
    rid = rid_raw.strip() if isinstance(rid_raw, str) else ""
    if is_placeholder_rule_id(rid):
        logger.warning(
            "[FeedbackApplier] high_fp_rate_rule 规则身份缺失/占位(%r)，"
            "跳过抑制桥接", pattern.get("rule_id"))
        return None
    fp_count = _count_or_zero(pattern.get("fp_count"))
    sample_size = _count_or_zero(pattern.get("sample_size"))
    if not (0 < fp_count <= sample_size):
        logger.warning(
            "[FeedbackApplier] high_fp_rate_rule 证据不完整"
            "（rule_id=%s, fp_count=%d, sample_size=%d），"
            "跳过抑制桥接", rid, fp_count, sample_size)
        return None
    fp_rate = fp_count / sample_size
    if not _has_dominant_fp_evidence(fp_count, fp_rate):
        logger.info(
            "[FeedbackApplier] high_fp_rate_rule 未满足样本/主导率门禁"
            "（rule_id=%s, fp_count=%d, sample_size=%d），跳过抑制桥接",
            rid, fp_count, sample_size)
        return None
    severities = pattern.get("severities")
    severities = ({
        str(severity): _count_or_zero(count)
        for severity, count in severities.items()
        if _count_or_zero(count) > 0
    } if isinstance(severities, dict) else {})
    return rid, {
        "fp_rate": fp_rate,
        "fp_count": fp_count,
        "sample_size": sample_size,
        "severities": severities,
    }
def _extract_fp_patterns(outcome_summary) -> dict:
    fp_patterns = {}
    fps = summary_dict(outcome_summary).get("failure_patterns")
    for pattern in (fps if isinstance(fps, list) else []):
        entry = _fp_pattern_entry(pattern)
        if entry is not None:
            fp_patterns[entry[0]] = entry[1]
    return fp_patterns
def _append_bridge_entry(entries: list, pending_targets: set,
                         spec: _SuppressionSpec, now: str,
                         prov_base: dict | None) -> int:
    rid = spec.rule_id
    target = f"fp_suppression/{rid}"
    if target in pending_targets:
        return 0
    desc = f"规则 {rid} 误报率{spec.fp_rate:.0%}({spec.fp_count}项)，生成抑制规则"
    suppression_rule = {
        "rule_id": rid,
        "fp_count": spec.fp_count,
        "fp_rate": spec.fp_rate,
        "line_zero_ratio": 0,
        "min_severity_to_suppress": spec.min_severity,
        "message_patterns": spec.message_patterns,
        "file_patterns": [],
        "source": _BRIDGE_SUPPRESSION_SOURCE,
    }
    prov_evo = _entry_prov(prov_base, spec, desc)
    pending_targets.add(target)
    entries.append({
        "timestamp": now,
        "target": target,
        "target_type": "fp_suppression",
        "target_id": rid,
        "action_type": "fp_suppression",
        "description": f"{_BRIDGE_DESC_PREFIX}{desc}",
        "suggested_value": json.dumps(suppression_rule, ensure_ascii=False, default=str),
        "expected_impact": f"应用抑制规则后预计减少 {spec.fp_count} 项误报",
        "confidence": min(0.95, spec.confidence),
        "status": "pending",
        "fp_pattern": True,
        "rule_id": rid,
        "fp_rate": spec.fp_rate,
        "fp_count": spec.fp_count,
        "source": _BRIDGE_SOURCE,
        **prov_evo,
    })
    return 1
def _bridge_state_entries(entries: list, fp_from_state: list,
                          now: str, prov_base: dict | None) -> int:
    pending_targets = _pending_targets_from(entries)
    n = 0
    for rid, info in fp_from_state:
        fp_count = info["count"]
        severities = info.get("severities", {}) or {}
        fp_rate = info.get("fp_rate", 1.0)
        n += _append_bridge_entry(
            entries, pending_targets,
            _SuppressionSpec(
                rule_id=rid,
                fp_count=fp_count,
                fp_rate=fp_rate,
                min_severity=suppression_min_severity(
                    fp_rate, fp_count, severities),
                message_patterns=[s[:60] for s in info["samples"][:2]],
                confidence=0.5 + fp_count / 50.0,
                severities=severities,
                sample_files=(info.get("files") or [])[:5]),
            now, prov_base)
    return n
def _fb_eligible_for_bridge(fb) -> bool:
    if not isinstance(fb, DiagnosisFeedback):
        logger.warning(
            "[FeedbackApplier] 桥接条目非 DiagnosisFeedback(%s)，跳过",
            type(fb).__name__)
        return False
    if not isinstance(fb.feedback_type, str) or fb.feedback_type != "false_positive":
        return False
    if not isinstance(fb.target_type, str) or fb.target_type != "cv_rule":
        return False
    return float_metric(fb.confidence) >= 0.6
def _bridge_target_rule_id(fb) -> str | None:
    rid_raw = fb.target_id
    if not isinstance(rid_raw, str):
        logger.warning(
            "[FeedbackApplier] false_positive 反馈 target_id 非 str（%s），跳过桥接",
            type(rid_raw).__name__)
        return None
    _form, rid = _cv_target_parts(rid_raw)
    if rid_raw in AGGREGATE_CV_TARGETS or rid in AGGREGATE_CV_TARGETS:
        logger.warning(
            "[FeedbackApplier] false_positive 反馈 target_id 为聚合伪目标(%s)，跳过桥接",
            rid_raw)
        return None
    if is_placeholder_rule_id(rid):
        return None
    return rid
def _bridge_feedbacks(feedbacks: list, entries: list,
                      fp_patterns: dict, now: str,
                      prov_base: dict | None) -> int:
    pending_targets = _pending_targets_from(entries)
    n = 0
    for fb in feedbacks:
        if not _fb_eligible_for_bridge(fb):
            continue
        rid = _bridge_target_rule_id(fb)
        if rid is None:
            continue
        fp_info = fp_patterns.get(rid, {})
        fp_rate = fp_info.get("fp_rate", 0)
        fp_count = fp_info.get("fp_count", 0)
        if fp_count <= 0:
            logger.info(
                "[FeedbackApplier] 反馈规则 %s 无FP计数证据，跳过抑制桥接",
                rid)
            continue
        severities = fp_info.get("severities") or {}
        n += _append_bridge_entry(
            entries, pending_targets,
            _SuppressionSpec(
                rule_id=rid,
                fp_count=fp_count,
                fp_rate=fp_rate,
                min_severity=suppression_min_severity(
                    fp_rate, fp_count, severities),
                confidence=float_metric(fb.confidence),
                severities=severities),
            now, prov_base)
    return n
def run_feedback_loop(
    skill_dir: str,
    fix_route_report: dict,
    diagnosis_report: dict | None = None,
    memory_context: DiagnosticMemoryContext | None = None,
) -> FeedbackReport:
    fix_route_report = normalize_fix_route_report(skill_dir, fix_route_report)
    analyzer = TreatmentOutcomeAnalyzer(skill_dir)
    outcome_summary = analyzer.analyze(fix_route_report)
    resolver = DiagnosisFeedbackResolver(skill_dir)
    feedbacks = resolver.resolve(outcome_summary, diagnosis_report, fix_route_report)
    applier = FeedbackApplier(skill_dir)
    report = applier.apply(feedbacks, outcome_summary)
    apply_memory_bridge(report, applier.get_adjustments(), memory_context)
    return report
if __name__ == "__main__":
    logger = logging.getLogger(_MODULE_PATH)
    setup_logging(console=True, force=True)
    if len(sys.argv) < 2:
        logger.info(f"Usage: {_USAGE_ENTRY} "
                    "<fix_route_report.json> [diagnosis_report.json] "
                    "[--skill-dir PROJECT_DIR]")
        sys.exit(1)
    parser = argparse.ArgumentParser(description="执行治疗反馈闭环")
    parser.add_argument("fix_route_report")
    parser.add_argument("diagnosis_report", nargs="?")
    parser.add_argument(
        "--skill-dir", default=None,
        help="目标技能或 Python 项目根目录；默认使用当前工作目录")
    args = parser.parse_args(sys.argv[1:])
    fix_path = args.fix_route_report
    if not os.path.isfile(fix_path):
        logger.error("修复路由报告不存在: %s", fix_path)
        sys.exit(1)
    diag_path = args.diagnosis_report
    skill_dir = normalize_skill_dir(args.skill_dir or os.getcwd())
    fix_report, fix_err = _read_report_json(fix_path)
    if fix_report is None:
        logger.error("修复路由报告 JSON 读取/解析失败: %s (%s)", fix_path, fix_err)
        sys.exit(1)
    diag_report = None
    if diag_path:
        if not os.path.isfile(diag_path):
            logger.error("诊断报告不存在: %s", diag_path)
            sys.exit(1)
        diag_report, diag_err = _read_report_json(diag_path)
        if diag_report is None:
            logger.error("诊断报告 JSON 读取/解析失败: %s (%s)",
                         diag_path, diag_err)
            sys.exit(1)
    result = run_feedback_loop(skill_dir, fix_report, diag_report)
    logger.info("=== 反馈闭环报告 ===")
    logger.info(json.dumps(result.to_dict(), ensure_ascii=False, indent=2, default=str))

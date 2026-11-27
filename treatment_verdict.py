from __future__ import annotations

import json
import logging
import os
import sys
from collections import defaultdict
from fractions import Fraction
from typing import NamedTuple

from jwsgj.diag_types_defs import (
    DiagnosisFeedback,
    TreatmentOutcomeSummary,
    default_feedback_history,
)
from jwsgj.diag_types_normalize import (
    as_list,
    has_finding_entries,
    int_or,
    is_placeholder_rule_id,
    is_pure_int,
    plan_index,
    safe_float,
    section_dict,
    source_id_text,
    str_or_empty,
    unwrap_cv_results,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    CAT_DYNAMIC_BINDING,
    CONCLUSION_V2_MAP,
    FIELD_CV_CONFIDENCE_THRESHOLDS,
    FIELD_CV_RULE_WEIGHTS,
    FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
    FIELD_METHOD_THRESHOLDS,
    FIELD_ROUTED_TO_FIXER,
    FIELD_SAFETY_VERIFIER_USED,
    FIELD_SIDE_EFFECTS_DETECTED,
    FIELD_THRESHOLD_ADJUST,
    FIELD_TOTAL_INPUT_FINDINGS,
    RULE_HARDCODED_CREDENTIAL,
    RULE_HIGH_COMPLEXITY,
    RULE_MISSING_DOCSTRING,
    RULE_MUTABLE_DEFAULT,
    RULE_ORPHAN_FUNCTION,
    SUB_ENGINE_META,
    SUMMARY_STATUS_BUCKETS,
    TX_FAILED_STATUSES,
    TX_FIXED_STATUSES,
    TX_FP_CONFIRMED_STATUSES,
    TX_ROLLED_BACK_STATUSES,
)
from jwsgj.runtime_paths import (
    read_evolution_section,
)
from jwsgj.treatment_state import (
    canonical_locator_key,
    load_treatment_items,
)

__all__ = [
    "AUTO_SAFE_REGISTRY_TARGET",
    "EXECUTED_STATES",
    "FIELD_REQUEST_COUNT",
    "FIELD_TRIGGER_COUNT",
    "FIXED_STATES",
    "HISTORY_FIXER_SECTION",
    "LIST_ADJUSTMENTS",
    "LIST_FEEDBACKS",
    "LIST_SUGGESTIONS",
    "REGRESSED_STATES",
    "CvFeedbackAnalyzer",
    "DiagnosisFeedbackResolver",
    "RuleMethodMapper",
    "actionable_rule_ids",
    "default_method_adjustments",
    "failure_bucket",
    "iter_details",
    "load_json_file",
    "normalize_feedback_history",
    "normalize_fix_route_report",
    "pct_or_zero",
]
logger = logging.getLogger(__name__)
logger.info("treatment_verdict 反馈裁决域已加载: %d 项导出", len(__all__))
_DEFAULT_PROPAGATE_IO = False
HISTORY_FIXER_SECTION = "fixer_needs"
LIST_SUGGESTIONS = "suggestions"
LIST_ADJUSTMENTS = "adjustments"
LIST_FEEDBACKS = "feedbacks"
FIELD_TRIGGER_COUNT = "trigger_count"
FIELD_REQUEST_COUNT = "request_count"
def pct_or_zero(v, default: float = 0.0):
    n = safe_float(v, default)
    if n is None:
        return default
    return n if 0.0 <= n <= 100.0 else default
def _contract_summary_ok(outcome_summary, label: str) -> bool:
    if isinstance(outcome_summary, TreatmentOutcomeSummary):
        return True
    logger.warning(
        "[FeedbackResolver] %s 的 outcome_summary 非契约实例(%s)，"
        "按无治疗证据返回空反馈",
        label, type(outcome_summary).__name__)
    return False
def load_json_file(path: str, default: dict, label: str, *,
                   propagate_io: bool = _DEFAULT_PROPAGATE_IO) -> dict:
    if os.path.isfile(path):
        try:
            with open(path, encoding="utf-8-sig") as f:
                loaded = json.load(f)
            if isinstance(loaded, dict):
                return loaded
            logger.warning(
                "[treatment_verdict] %s 顶层非对象(%s)，按默认值降级",
                label, type(loaded).__name__)
            return default
        except OSError as e:
            logger.warning("[treatment_verdict] %s 读取IO失败: %s", label, e)
            if propagate_io:
                raise
        except (ValueError, RecursionError) as e:
            logger.warning("[treatment_verdict] %s 内容损坏: %s", label, e)
    return default
def normalize_feedback_history(data) -> dict:
    default = default_feedback_history()
    if not isinstance(data, dict):
        return default
    data = dict(data)
    for key, default_val in default.items():
        if key not in data:
            data[key] = default_val
    for key in (FIELD_METHOD_THRESHOLDS, FIELD_CV_RULE_WEIGHTS,
                HISTORY_FIXER_SECTION):
        if not isinstance(data.get(key), dict):
            data[key] = {}
    if not isinstance(data.get("sessions"), list):
        data["sessions"] = []
    data["session_count"] = max(0, int_or(data.get("session_count"), 0))
    return data
def default_method_adjustments() -> dict:
    return {
        "version": "1.0",
        FIELD_METHOD_CONFIDENCE_MULTIPLIERS: {},
        FIELD_CV_CONFIDENCE_THRESHOLDS: {},
        "fixer_safety_overrides": {},
        "last_updated": "",
    }
def _finding_rows(value):
    return list(value) if isinstance(value, tuple) else value
def _cv_view_and_findings(diagnosis_report: dict) -> tuple[dict, list]:
    cv_result = section_dict(
        diagnosis_report, CAT_CROSS_VALIDATION, diagnosis_report)
    if cv_result is not diagnosis_report:
        cv_result = unwrap_cv_results(cv_result)
    idx = _finding_rows(cv_result.get("findings_index"))
    if has_finding_entries(idx):
        return cv_result, idx
    top_idx = _finding_rows(diagnosis_report.get("findings_index"))
    if top_idx is not idx and has_finding_entries(top_idx):
        return cv_result, top_idx
    return cv_result, as_list(idx)
def _status_key(value) -> str:
    return value.strip().lower() if isinstance(value, str) else ""
def _effective_conclusion(item: dict) -> str:
    candidate = _status_key(item.get("conclusion_v2"))
    mapped = CONCLUSION_V2_MAP.get(candidate)
    if mapped:
        return mapped
    return _status_key(item.get("conclusion"))
def _source_method_id(src) -> str:
    raw = src.get("method_id", "") if isinstance(src, dict) else src
    return source_id_text(raw)
def _unique_source_ids(item: dict) -> list[str]:
    sources = item.get("sources", [])
    if isinstance(sources, str):
        sources = [sources]
    elif isinstance(sources, (set, frozenset)):
        sources = sorted(sources, key=str)
    elif isinstance(sources, tuple):
        sources = list(sources)
    elif not isinstance(sources, list):
        return []
    seen: set[str] = set()
    unique: list[str] = []
    for src in sources:
        method_id = _source_method_id(src)
        if method_id and method_id not in seen:
            seen.add(method_id)
            unique.append(method_id)
    return unique
def _entry_findings(item: dict) -> list:
    findings = _finding_rows(item.get("findings", []))
    if has_finding_entries(findings):
        return findings
    sample = item.get("sample_finding")
    return [sample] if isinstance(sample, dict) else []
def _finding_rule_id(finding: dict) -> str:
    rule = finding.get("rule_id")
    if is_placeholder_rule_id(rule):
        rule = finding.get("rule_family")
    return rule.strip() if isinstance(rule, str) and rule.strip() else ""
def _extract_entry_rules(item: dict) -> set[str]:
    return {
        rule_id for rule_id in (
            _finding_rule_id(finding)
            for finding in _entry_findings(item)
            if isinstance(finding, dict))
        if rule_id and not is_placeholder_rule_id(rule_id)
    }
def _detail_rule_ids(detail: dict) -> set[str]:
    rule_ids = _extract_entry_rules(detail)
    direct_rule_id = _finding_rule_id(detail)
    if direct_rule_id and not is_placeholder_rule_id(direct_rule_id):
        rule_ids.add(direct_rule_id)
    return rule_ids
_LEGACY_FIXED_RULE_WILDCARD = ""
_COVERAGE_GAP_RULE_ISSUES = ("fixer_coverage_gap", "domain_fix_coverage_gap")
_FIXER_REGISTRY_TARGET = "FIXER_REGISTRY_OVERALL"
AUTO_SAFE_REGISTRY_TARGET = "AUTO_SAFE_REGISTRY"
def iter_details(fix_route_report) -> list[dict]:
    if not isinstance(fix_route_report, dict):
        return []
    details = fix_route_report.get("details", [])
    if not isinstance(details, (list, tuple)):
        return []
    return _latest_status_rows(details)
_RULE_PREFIX_MAP = {
    "AP": "B", "C4": "B", "C6": "B", "C8": "B",
    "C11": "B", "C16": "B", "C17": "B",
    "C18": "B", "C19": "B",
    "DP": "F", "IN": "F", "TO": "F", "LK": "F", "AY": "F",
    "SE": "D", "SC": "D", "SR": "D", "SN": "D", "POL": "D",
    "SZ": "A", "SD": "A", "EN": "A", "GM": "A",
    "GF": "B", "JS": "B", "TP": "B", "RG": "B",
    "EH": "B", "EX": "B", "BE": "B", "LP": "B", "TY": "B",
    "FM": "B", "PT": "B", "AT": "B", "TT": "B", "SK": "B",
    "AI": "F",
    "MM": "C", "SIM": "C", "CG": "C",
    "DC": "B", "TC": "E", "UT": "E", "SCA": "E",
    "RD": "B", "CF": "A", "C2": "A",
}
_RULE_FAMILY_TO_METHODS: dict[str, list[str]] = {
    "dead_code":           ["C", "A"],
    "sql_injection":       ["D", "A"],
    "high_coupling":       ["A"],
    RULE_HIGH_COMPLEXITY:     ["B", "A", "E"],
    "circular_dep":        ["C", "B", "E"],
    "broken_call":         ["C", "E", "B"],
    "mutable_global":      ["B", "A"],
    RULE_MUTABLE_DEFAULT:    ["B", "A"],
    "path_traversal":      ["D", "A", "E"],
    "broad_except":        ["B", "C", "E"],
    "empty_except":        ["B"],
    "resource_leak":       ["C", "B", "E"],
    "unbounded_recursion": ["B", "E"],
    "syntax_error":        ["B"],
    "code_smell":          ["B"],
    "health_score":        ["B"],
    "quality_score":       ["B"],
    "api_change":          ["C", "E", "B"],
    "regression":          ["B", "E"],
    "gate_issue":          ["F"],
    "fix_safety":          ["F", "E"],
    "sim_failure":         ["C", "E"],
    "perf_hotspot":        ["E"],
    "low_coverage":        ["E"],
    "diag_general":       ["B", "D", "F", "A"],
    "facade_antipattern":  ["B"],
    "lazy_import":         ["B", "F"],
    "stub_function":       ["B", "E"],
    "dynamic_import":      ["B", "F"],
    "silent_swallow":      ["D", "B"],
    "liveness_probe":      ["B", "E"],
    "policy_violation":     ["D", "F", "A"],
    "api_issue":           ["B"],
    "architecture":        ["C", "B", "E"],
    "duplicate_code":      ["B"],
    "unused_import":       ["B"],
    RULE_MISSING_DOCSTRING: ["B"],
    "shadowing_builtin":   ["B"],
    "compatibility":       ["E"],
    RULE_HARDCODED_CREDENTIAL: ["D", "B"],
    "danger_pattern":      ["D", "B"],
    "priority_rec":        ["F"],
    "method_anomaly":      ["B"],
    "method_pass":         ["B"],
    RULE_ORPHAN_FUNCTION:     ["C", "B"],
    "large_codebase":      ["B"],
    "empty_project":       ["B"],
    "god_file":            ["B", "E"],
    "undertested":         ["E"],
    CAT_DYNAMIC_BINDING:     ["C", "E"],
    "test_failure":        ["E"],
    "test_error":          ["E"],
    "test_smell":          ["E"],
    "vulnerability_scan":  ["E", "D", "A", "B"],
    "dependency_issue":    ["E"],
    "stress_failure":      ["E"],
    "resource_exhaustion": ["E", "C"],
    "concurrency_issue":   ["E", "C"],
}
_RULE_PREFIXES_BY_LEN: tuple[str, ...] = tuple(
    sorted(_RULE_PREFIX_MAP, key=len, reverse=True))
_MAIN_METHOD_IDS = frozenset({"A", "B", "C", "D", "E", "F"})
class RuleMethodMapper:
    def _prefix_method(self, rule_id: str) -> str | None:
        for prefix in _RULE_PREFIXES_BY_LEN:
            if rule_id.startswith(prefix) and self.prefix_match_ok(
                    rule_id, prefix):
                return _RULE_PREFIX_MAP[prefix]
        return None
    def _family_method(self, rule_id: str) -> str | None:
        for family, methods in _RULE_FAMILY_TO_METHODS.items():
            if (family and rule_id.startswith(family)
                    and self.prefix_match_ok(rule_id, family)):
                return methods[0] if methods else None
        return None
    @staticmethod
    def _main_method_of(rule_id: str) -> str | None:
        head, sep, _ = rule_id.partition("-")
        if not sep:
            head, sep, _ = rule_id.partition("_")
        if sep:
            meta = SUB_ENGINE_META.get(head)
            if isinstance(meta, dict) and meta.get("main"):
                return str(meta["main"]).upper()
        if rule_id[:1] in _MAIN_METHOD_IDS and rule_id[1:].isdigit():
            return rule_id[:1]
        return None
    def map_rule_to_method(self, rule_id: str) -> str:
        if not rule_id:
            return "UNKNOWN"
        rule_id = str(rule_id).strip()
        if not rule_id:
            return "UNKNOWN"
        method = (self._prefix_method(rule_id)
                  or self._family_method(rule_id)
                  or self._main_method_of(rule_id))
        if method:
            return method
        logger.debug("[FeedbackResolver] 规则归因未命中映射表, 兜底 UNKNOWN: rule_id=%s", rule_id)
        return "UNKNOWN"
    @staticmethod
    def prefix_match_ok(rule_id: str, prefix: str) -> bool:
        if not prefix:
            return False
        if len(rule_id) == len(prefix):
            return True
        nxt = rule_id[len(prefix)]
        if not nxt.isalnum():
            return True
        if not prefix[-1].isalnum():
            return False
        return nxt.isdigit() and not prefix[-1].isdigit()
    @staticmethod
    def rule_family_to_methods() -> dict[str, list[str]]:
        return {family: list(methods)
                for family, methods in _RULE_FAMILY_TO_METHODS.items()}
class CvFeedbackAnalyzer:
    def _accumulate_item_cv_stats(self, item, conclusion, entry_rules,
                                  method_stats, rules_by_method) -> None:
        for method_id in _unique_source_ids(item):
            method_stats[method_id]["total"] += 1
            if conclusion == "confirmed":
                method_stats[method_id]["confirmed"] += 1
            rules_by_method[method_id] |= entry_rules
    def _accumulate_method_cv_stats(self, findings_index) -> tuple:
        method_stats = defaultdict(lambda: {"confirmed": 0, "total": 0})
        rules_by_method: dict[str, set[str]] = defaultdict(set)
        for item in findings_index:
            if not isinstance(item, dict):
                continue
            self._accumulate_item_cv_stats(
                item, _effective_conclusion(item), _detail_rule_ids(item),
                method_stats, rules_by_method)
        return method_stats, rules_by_method
    @staticmethod
    def _collect_failed_rule_ids(fix_route_report) -> set:
        return {
            rule_id
            for detail in iter_details(fix_route_report)
            if _status_key(detail.get("status")) in REGRESSED_STATES
            for rule_id in _detail_rule_ids(detail)
        }
    @staticmethod
    def _precision_trigger_ok(stats, confirm_rate, own_failed,
                              has_rule_linkage, failed_rules) -> bool:
        if stats["confirmed"] < 3 or stats["total"] < 5:
            return False
        return confirm_rate > 0.7 and bool(
            own_failed or (not has_rule_linkage and failed_rules))
    @staticmethod
    def _method_precision_feedbacks(method_stats, rules_by_method,
                                    failed_rules) -> list:
        feedbacks = []
        for method_id, stats in method_stats.items():
            confirm_rate = stats["confirmed"] / max(stats["total"], 1)
            own_failed = failed_rules & rules_by_method.get(method_id, set())
            has_rule_linkage = bool(rules_by_method.get(method_id))
            if not CvFeedbackAnalyzer._precision_trigger_ok(
                    stats, confirm_rate, own_failed,
                    has_rule_linkage, failed_rules):
                continue
            fail_desc = (f"其产出的 {len(own_failed)} 种规则修复失败"
                         if own_failed else "存在修复失败项")
            ev_failed = (f"该方法产出规则修复失败: {len(own_failed)}"
                         if own_failed
                         else f"修复失败规则(全局): {len(failed_rules)}")
            feedbacks.append(DiagnosisFeedback(
                target_type="method",
                target_id=method_id,
                feedback_type=FIELD_THRESHOLD_ADJUST,
                current_value=f"确认率 {confirm_rate:.1%}",
                suggested_value="建议交叉验证对该方法产出的finding增加额外验证条件",
                reason=f"方法 {method_id} 产出的finding确认率 {confirm_rate:.1%}（{stats['confirmed']}/{stats['total']}），"
                       f"但{fail_desc}，交叉验证可能需要更严格的确认条件",
                confidence=min(0.85, 0.6 + (confirm_rate - 0.7)
                               + 0.05 * min(len(own_failed), 4)),
                evidence=[f"确认率 {confirm_rate:.1%}", ev_failed],
            ))
        return feedbacks
    @staticmethod
    def _overall_threshold_feedback(summary, confirm_ratio: float,
                                    confirmed_count: int,
                                    total_input: int) -> DiagnosisFeedback | None:
        rolled_back = max(0, _integral_count(
            summary.total_rolled_back, 0))
        attempted = max(0, _integral_count(summary.total_attempted, 0))
        if rolled_back > attempted:
            logger.warning(
                "[FeedbackResolver] 治疗聚合计数不一致，跳过整体阈值反馈: "
                "rolled_back=%d, attempted=%d", rolled_back, attempted)
            return None
        if attempted > 0:
            rb_rate = min(100.0, max(0.0, rolled_back / attempted * 100.0))
        else:
            rb_rate = pct_or_zero(summary.rollback_rate)
        if confirm_ratio <= 0.4 or rb_rate <= 20.0:
            return None
        return DiagnosisFeedback(
            target_type="cv_rule",
            target_id="CV-OVERALL-THRESHOLD",
            feedback_type="weight_adjust",
            current_value=f"确认率 {confirm_ratio:.1%}",
            suggested_value="提高整体确认阈值，减少过度确认",
            reason=f"交叉验证确认率 {confirm_ratio:.1%} 但修复回滚率 "
                   f"{rb_rate:.1f}%，"
                   f"确认条件可能过于宽松",
            confidence=0.7,
            evidence=[
                (f"确认率 {confirm_ratio:.1%} "
                 f"({confirmed_count}/{total_input})"),
                f"修复回滚率 {rb_rate:.1f}%",
            ],
        )
    @staticmethod
    def _overall_suppression_feedback(suppress_ratio: float,
                                      suppressed_count: int,
                                      total_input: int) -> DiagnosisFeedback | None:
        if suppress_ratio >= 0.1 or total_input <= 20:
            return None
        return DiagnosisFeedback(
            target_type="cv_rule",
            target_id="CV-SUPPRESSION-RULES",
            feedback_type="weight_adjust",
            current_value=f"抑制率 {suppress_ratio:.1%}",
            suggested_value="增强抑制规则（contradiction/independence检测）",
            reason=f"交叉验证抑制率仅 {suppress_ratio:.1%}（{suppressed_count}/{total_input}），"
                   f"大量噪声finding未被过滤，可能污染修复管线",
            confidence=0.6,
            evidence=[f"抑制率 {suppress_ratio:.1%}"],
        )
    @staticmethod
    def _overall_cv_feedbacks(summary, confirmed_count: int,
                              suppressed_count: int,
                              total_input: int) -> list:
        if total_input <= 0:
            return []
        if (confirmed_count < 0 or suppressed_count < 0
                or confirmed_count + suppressed_count > total_input):
            logger.warning(
                "[FeedbackResolver] CV 聚合计数不一致，跳过整体反馈: "
                "confirmed=%d, suppressed=%d, total=%d",
                confirmed_count, suppressed_count, total_input)
            return []
        confirm_ratio = confirmed_count / total_input
        suppress_ratio = suppressed_count / total_input
        feedbacks = []
        threshold_feedback = CvFeedbackAnalyzer._overall_threshold_feedback(
            summary, confirm_ratio, confirmed_count, total_input)
        if threshold_feedback is not None:
            feedbacks.append(threshold_feedback)
        suppression_feedback = CvFeedbackAnalyzer._overall_suppression_feedback(
            suppress_ratio, suppressed_count, total_input)
        if suppression_feedback is not None:
            feedbacks.append(suppression_feedback)
        return feedbacks
    def analyze_precision(
        self,
        summary: TreatmentOutcomeSummary,
        diagnosis_report: dict,
        fix_route_report: dict | None = None,
    ) -> list[DiagnosisFeedback]:
        feedbacks = []
        if not _contract_summary_ok(summary, "CV 精度分析"):
            return feedbacks
        if not isinstance(diagnosis_report, dict):
            logger.debug("[FeedbackResolver] 精度分析跳过: diagnosis_report 为非 dict 脏形态")
            return feedbacks
        cv_result, findings_index = _cv_view_and_findings(diagnosis_report)
        if findings_index:
            method_stats, rules_by_method = self._accumulate_method_cv_stats(
                findings_index)
            failed_rules = self._collect_failed_rule_ids(fix_route_report)
            feedbacks.extend(self._method_precision_feedbacks(
                method_stats, rules_by_method, failed_rules))
        else:
            logger.info(
                "[FeedbackResolver] 方法级精度分析跳过: findings_index 为空")
        report_summary = diagnosis_report.get("summary")
        if not isinstance(report_summary, dict):
            report_summary = {}
        confirmed_count = _cv_stat_count(
            cv_result, report_summary, "confirmed", "cv_confirmed")
        suppressed_count = _cv_stat_count(
            cv_result, report_summary, "suppressed", "cv_suppressed")
        total_input = _cv_stat_count(
            cv_result, report_summary, FIELD_TOTAL_INPUT_FINDINGS,
            FIELD_TOTAL_INPUT_FINDINGS)
        feedbacks.extend(self._overall_cv_feedbacks(
            summary, confirmed_count, suppressed_count, total_input))
        logger.info(
            "[FeedbackResolver] CV 精度分析完成: 产出 %d 条反馈"
            "（确认 %d / 抑制 %d / 输入 %d）",
            len(feedbacks), confirmed_count, suppressed_count, total_input)
        return feedbacks
    def _accumulate_suppressed_item(self, item, suppressed_by_method,
                                    rules_by_method_locator) -> None:
        locator = canonical_locator_key(str_or_empty(item.get("locator")))
        if not locator:
            return
        entry_rules = _detail_rule_ids(item)
        for mid in _unique_source_ids(item):
            method_locs = suppressed_by_method.setdefault(mid, [])
            if locator not in method_locs:
                method_locs.append(locator)
            if entry_rules:
                rules_by_method_locator.setdefault(
                    (mid, locator), set()).update(entry_rules)
    def _accumulate_suppressed_index(self, findings_index) -> tuple:
        suppressed_by_method: dict[str, list[str]] = {}
        rules_by_method_locator: dict[tuple[str, str], set[str]] = {}
        for item in findings_index:
            if (not isinstance(item, dict)
                    or _effective_conclusion(item) != "suppressed"):
                continue
            self._accumulate_suppressed_item(
                item, suppressed_by_method, rules_by_method_locator)
        return suppressed_by_method, rules_by_method_locator
    @staticmethod
    def _collect_fixed_rules_by_locator(fix_route_report) -> dict:
        fixed_rules_by_locator = {}
        for detail in iter_details(fix_route_report):
            if _status_key(detail.get("status")) not in TX_FIXED_STATUSES:
                continue
            loc = canonical_locator_key(
                str_or_empty(detail.get("locator")))
            if not loc:
                continue
            rule_ids = _detail_rule_ids(detail)
            fixed_rules_by_locator.setdefault(loc, set()).update(
                rule_ids or {_LEGACY_FIXED_RULE_WILDCARD})
        return fixed_rules_by_locator
    @staticmethod
    def _fn_method_feedback_entry(method_id, locators, false_negatives,
                                  fn_rate) -> DiagnosisFeedback:
        return DiagnosisFeedback(
            target_type="method",
            target_id=method_id,
            feedback_type="false_negative",
            current_value=f"被抑制 {len(locators)} 个 finding",
            suggested_value=f"放松确认阈值（{len(false_negatives)} 个被抑制的finding实际可修复）",
            reason=f"方法 {method_id} 产出的 {len(false_negatives)}/{len(locators)} 个被抑制的 "
                   f"finding 实际被修复成功，交叉验证可能过度抑制该方法的发现",
            confidence=min(0.85, 0.5 + fn_rate / 2),
            evidence=[f"假阴性: {len(false_negatives)}/{len(locators)} (rate={fn_rate:.0%})"],
        )
    @staticmethod
    def _emit_fn_rule_feedbacks(feedbacks, method_id, false_negatives,
                                locator_count, fn_rate,
                                emitted_fn_rules) -> None:
        for _loc, matched_rules in false_negatives:
            for rid in sorted(matched_rules):
                if rid in emitted_fn_rules:
                    continue
                emitted_fn_rules.add(rid)
                feedbacks.append(DiagnosisFeedback(
                    target_type="cv_rule",
                    target_id=f"CV-CONFIDENCE-{rid}",
                    feedback_type="over_suppression",
                    current_value="标准抑制阈值",
                    suggested_value=f"降低规则 {rid} 的确认阈值（{fn_rate:.0%}的抑制为假阴性）",
                    reason=f"规则 {rid} 被交叉验证抑制的 finding 实际修复成功"
                           f"（方法 {method_id} 假阴性率 {fn_rate:.0%}），"
                           f"CV 对该规则的抑制条件可能过于严格",
                    confidence=min(0.75, 0.4 + fn_rate / 2),
                    evidence=[f"假阴性规则: {rid}",
                              (f"方法假阴性率 {fn_rate:.0%} "
                               f"({len(false_negatives)}/{locator_count})")],
                ))
    def _fn_feedbacks_for_method(self, method_id: str, locators: list,
                                 fixed_rules_by_locator: dict,
                                 rules_by_method_locator: dict,
                                 emitted_fn_rules: set) -> list:
        false_negatives = []
        for loc in locators:
            if loc not in fixed_rules_by_locator:
                continue
            suppressed_rules = rules_by_method_locator.get(
                (method_id, loc), set())
            fixed_rules = fixed_rules_by_locator[loc]
            has_legacy_wildcard = _LEGACY_FIXED_RULE_WILDCARD in fixed_rules
            if not suppressed_rules:
                if has_legacy_wildcard:
                    false_negatives.append((loc, set()))
                continue
            matched_rules = (suppressed_rules if has_legacy_wildcard
                             else suppressed_rules & fixed_rules)
            if matched_rules:
                false_negatives.append((loc, matched_rules))
        if not false_negatives:
            return []
        fn_rate = len(false_negatives) / max(len(locators), 1)
        if fn_rate < 0.3:
            return []
        feedbacks = [self._fn_method_feedback_entry(
            method_id, locators, false_negatives, fn_rate)]
        self._emit_fn_rule_feedbacks(
            feedbacks, method_id, false_negatives, len(locators), fn_rate,
            emitted_fn_rules)
        return feedbacks
    def analyze_false_negative(
        self,
        _summary: TreatmentOutcomeSummary,
        diagnosis_report: dict | None = None,
        fix_route_report: dict | None = None,
    ) -> list[DiagnosisFeedback]:
        feedbacks = []
        if (not isinstance(diagnosis_report, dict)
                or not isinstance(fix_route_report, dict)):
            logger.debug("[FeedbackResolver] 假阴性分析跳过: 输入报告为非 dict 脏形态")
            return feedbacks
        _, findings_index = _cv_view_and_findings(diagnosis_report)
        suppressed_by_method, rules_by_method_locator = (
            self._accumulate_suppressed_index(findings_index))
        if not suppressed_by_method:
            logger.info("[FeedbackResolver] 假阴性分析跳过: 无被抑制条目")
            return feedbacks
        fixed_rules_by_locator = self._collect_fixed_rules_by_locator(
            fix_route_report)
        if not fixed_rules_by_locator:
            logger.info("[FeedbackResolver] 假阴性分析跳过: 修复报告无成功 locator")
            return feedbacks
        emitted_fn_rules: set[str] = set()
        for method_id, locators in suppressed_by_method.items():
            feedbacks.extend(self._fn_feedbacks_for_method(
                method_id, locators, fixed_rules_by_locator,
                rules_by_method_locator, emitted_fn_rules))
        logger.info(
            "[FeedbackResolver] 假阴性分析完成: 产出 %d 条反馈"
            "（涉及方法 %d 个 / 规则级落点 %d 个）",
            len(feedbacks), len(suppressed_by_method), len(emitted_fn_rules))
        return feedbacks
def _failure_pattern_dicts(summary) -> list[dict]:
    patterns = summary.failure_patterns
    if not isinstance(patterns, list):
        return []
    return [p for p in patterns if isinstance(p, dict)]
class _PatternScalars(NamedTuple):
    rule_id: str
    fp_rate: int | float
    rollback_rate: int | float
    fp_count: int
    sample_size: int
    rolled_back: int
def _integral_count(value, default: int) -> int:
    if isinstance(value, bool) or value is None:
        return default
    if is_pure_int(value):
        return value
    if isinstance(value, float):
        return int(value) if value.is_integer() else default
    if not isinstance(value, str):
        return default
    try:
        number = float(value.strip())
    except (TypeError, ValueError):
        return default
    return int(number) if number.is_integer() else default
def _cv_stat_count(cv_result: dict, report_summary: dict,
                   key: str, summary_key: str) -> int:
    value = _integral_count(cv_result.get(key), -1)
    if value >= 0:
        return value
    return _integral_count(report_summary.get(summary_key), -1)
def actionable_rule_ids(values) -> list[str]:
    if isinstance(values, str):
        values = [values]
    elif isinstance(values, (set, frozenset)):
        values = sorted(values, key=str)
    elif isinstance(values, tuple):
        values = list(values)
    elif not isinstance(values, list):
        return []
    rule_ids = []
    seen = set()
    for value in values:
        rule_id = value.strip() if isinstance(value, str) else ""
        if is_placeholder_rule_id(rule_id) or rule_id in seen:
            continue
        seen.add(rule_id)
        rule_ids.append(rule_id)
    return rule_ids
class DiagnosisFeedbackResolver:
    def __init__(self, skill_dir: str):
        self.skill_dir = skill_dir
        self._feedback_history_path = "feedback_history"
        try:
            _history_data = read_evolution_section(
                skill_dir, "feedback_history", default_feedback_history())
        except (OSError, ValueError, TypeError) as _exc:
            logger.warning("[TreatmentVerdict] 反馈历史 section 读取失败: %s",
                           _exc)
            _history_data = default_feedback_history()
        self._history = normalize_feedback_history(_history_data)
        self._cv_analyzer = CvFeedbackAnalyzer()
        self._rule_mapper = RuleMethodMapper()
    def _history_entry(self, section_key: str, key: str) -> dict:
        section = self._history.get(section_key)
        entry = section.get(key, {}) if isinstance(section, dict) else {}
        return entry if isinstance(entry, dict) else {}
    def resolve(self, outcome_summary: TreatmentOutcomeSummary,
                diagnosis_report: dict | None = None,
                fix_route_report: dict | None = None) -> list[DiagnosisFeedback]:
        feedbacks = []
        if not _contract_summary_ok(outcome_summary, "resolve"):
            return feedbacks
        feedbacks.extend(self._analyze_false_positive_patterns(outcome_summary))
        feedbacks.extend(self._analyze_path_issues(outcome_summary))
        feedbacks.extend(self._analyze_coverage_gaps(outcome_summary))
        if diagnosis_report:
            feedbacks.extend(self._cv_analyzer.analyze_precision(
                outcome_summary, diagnosis_report, fix_route_report))
        feedbacks.extend(self._analyze_safety_mislabels(outcome_summary))
        feedbacks.extend(self._cv_analyzer.analyze_false_negative(
            outcome_summary, diagnosis_report, fix_route_report))
        logger.info("[FeedbackResolver] 生成 %d 条反馈建议", len(feedbacks))
        return feedbacks
    @staticmethod
    def _pattern_scalar_fields(pattern) -> _PatternScalars:
        raw_rule_id = pattern.get("rule_id")
        rule_id = raw_rule_id.strip() if isinstance(raw_rule_id, str) else ""
        fp_rate = pct_or_zero(pattern.get("fp_rate", 0))
        rollback_rate = pct_or_zero(pattern.get("rollback_rate", 0))
        fp_count = max(0, _integral_count(pattern.get("fp_count"), 0))
        sample_size = max(0, _integral_count(
            pattern.get("sample_size"), 0))
        raw_rolled_back = pattern.get("rolled_back_count")
        explicit_rolled_back = _integral_count(raw_rolled_back, -1)
        if explicit_rolled_back >= 0:
            rolled_back = explicit_rolled_back
        elif raw_rolled_back is None:
            rollback_ratio = rollback_rate / 100
            if sample_size > sys.float_info.max:
                rolled_back = max(0, round(
                    Fraction(rollback_ratio) * sample_size))
            else:
                rolled_back = max(0, round(rollback_ratio * sample_size))
        else:
            rolled_back = -1
        return _PatternScalars(
            rule_id=rule_id,
            fp_rate=fp_rate,
            rollback_rate=rollback_rate,
            fp_count=fp_count,
            sample_size=sample_size,
            rolled_back=rolled_back,
        )
    @staticmethod
    def _pattern_has_evidence(pattern_type: str,
                              scalars: _PatternScalars) -> bool:
        if pattern_type == "high_fp_rate_rule":
            return bool(0 < scalars.fp_count <= scalars.sample_size
                        and scalars.fp_rate > 0)
        if pattern_type == "high_rollback_rule":
            return bool(0 < scalars.rolled_back <= scalars.sample_size
                        and scalars.rollback_rate > 0)
        return True
    def _cv_confirmation_feedback(self, rule_id: str, *, feedback_type: str,
                                  suggested_value: str, reason: str,
                                  confidence: float,
                                  evidence: list) -> DiagnosisFeedback:
        return DiagnosisFeedback(
            target_type="cv_rule",
            target_id=f"CV-CONFIDENCE-{rule_id}",
            feedback_type=feedback_type,
            current_value="标准确认阈值",
            suggested_value=suggested_value,
            reason=reason,
            confidence=confidence,
            evidence=evidence,
        )
    def _method_precondition_feedback(self, rule_id: str, *, reason: str,
                                      confidence: float,
                                      evidence: list) -> DiagnosisFeedback:
        return DiagnosisFeedback(
            target_type="method",
            target_id=self._rule_mapper.map_rule_to_method(rule_id),
            feedback_type="false_positive",
            current_value="当前灵敏度",
            suggested_value="增加前置条件检查或提高判定阈值",
            reason=reason,
            confidence=confidence,
            evidence=evidence,
        )
    def _fp_rule_feedbacks(self, scalars: _PatternScalars) -> list:
        rule_id = scalars.rule_id
        fp_rate = scalars.fp_rate
        fp_count = scalars.fp_count
        sample_size = scalars.sample_size
        return [
            self._cv_confirmation_feedback(
                rule_id,
                feedback_type="false_positive",
                suggested_value=f"提高确认阈值（误报率{fp_rate}%，{fp_count}项fp_confirmed）",
                reason=f"规则 {rule_id} 误报率 {fp_rate}%（{fp_count}/{sample_size}），"
                       f"交叉验证过度确认该类finding，需提高确认所需证据强度",
                confidence=min(0.95, 0.5 + fp_rate / 150),
                evidence=[f"误报率 {fp_rate}% (n={sample_size})", f"fp_confirmed: {fp_count}项"],
            ),
            self._method_precondition_feedback(
                rule_id,
                reason=f"规则 {rule_id} 产出的finding {fp_count}/{sample_size} 为误报，"
                       f"诊断方法存在过度检测，需提高判定标准",
                confidence=min(0.85, 0.6 + (fp_rate - 50) / 200),
                evidence=[f"误报率 {fp_rate}% (n={sample_size})"],
            ),
        ]
    def _rollback_rule_feedbacks(self, scalars: _PatternScalars) -> list:
        rule_id = scalars.rule_id
        rollback_rate = scalars.rollback_rate
        sample_size = scalars.sample_size
        rolled_back = scalars.rolled_back
        hist_key = f"CV-CONFIDENCE-{rule_id}"
        historical_count = max(0, int_or(
            self._history_entry(FIELD_CV_RULE_WEIGHTS, hist_key).get(
                FIELD_TRIGGER_COUNT), 0))
        feedbacks = self._rollback_cv_feedback(scalars, historical_count)
        feedbacks.append(self._method_precondition_feedback(
            rule_id,
            reason=f"规则 {rule_id} 产出的问题在修复阶段大量失败，"
                   f"诊断方法可能存在误报（过度检测非真实问题）",
            confidence=min(0.7, 0.6 + (rollback_rate - 50) / 200),
            evidence=[f"修复失败/回滚 {rolled_back} 次 (n={sample_size})"],
        ))
        return feedbacks
    def _rollback_cv_feedback(self, scalars: _PatternScalars,
                              historical_count: int) -> list:
        rule_id = scalars.rule_id
        rollback_rate = scalars.rollback_rate
        sample_size = scalars.sample_size
        if rollback_rate > 75:
            return [self._cv_confirmation_feedback(
                rule_id,
                feedback_type="weight_adjust",
                suggested_value=f"提高确认阈值（当前回滚率{rollback_rate}%，"
                                f"历史触发{historical_count}次）",
                reason=f"规则 {rule_id} 修复回滚率 {rollback_rate}%（样本{sample_size}），"
                       f"交叉验证可能过度确认该类finding，建议提高确认所需证据强度",
                confidence=min(0.9, 0.5 + rollback_rate / 200),
                evidence=[f"回滚率 {rollback_rate}% (n={sample_size})"],
            )]
        if rollback_rate > 50:
            return [self._cv_confirmation_feedback(
                rule_id,
                feedback_type="weight_adjust",
                suggested_value=f"适度提高确认阈值（回滚率{rollback_rate}%）",
                reason=f"规则 {rule_id} 修复回滚率 {rollback_rate}%，交叉验证确认精度可能不足",
                confidence=min(0.7, 0.4 + rollback_rate / 300),
                evidence=[f"回滚率 {rollback_rate}% (n={sample_size})"],
            )]
        return []
    def _analyze_false_positive_patterns(
        self, summary: TreatmentOutcomeSummary
    ) -> list[DiagnosisFeedback]:
        handlers = {
            "high_fp_rate_rule": self._fp_rule_feedbacks,
            "high_rollback_rule": self._rollback_rule_feedbacks,
        }
        feedbacks = []
        for pattern in _failure_pattern_dicts(summary):
            pattern_type = pattern.get("type")
            if not isinstance(pattern_type, str):
                logger.debug(
                    "[FeedbackResolver] failure_pattern type 非 str(%s)，跳过",
                    type(pattern_type).__name__)
                continue
            handler = handlers.get(pattern_type)
            if handler is None:
                continue
            scalars = self._pattern_scalar_fields(pattern)
            if is_placeholder_rule_id(scalars.rule_id):
                logger.warning(
                    "[FeedbackResolver] failure_pattern rule_id 缺失/非 str/占位 UNKNOWN（type=%s, rule_id=%r），"
                    "无法归因到真实规则，跳过CV反馈生成",
                    pattern_type, pattern.get("rule_id"))
                continue
            if not self._pattern_has_evidence(pattern_type, scalars):
                logger.warning(
                    "[FeedbackResolver] failure_pattern 零证据（type=%s, "
                    "rule_id=%s），跳过阈值反馈生成",
                    pattern_type, scalars.rule_id)
                continue
            feedbacks.extend(handler(scalars))
        return feedbacks
    def _analyze_path_issues(
        self, summary: TreatmentOutcomeSummary
    ) -> list[DiagnosisFeedback]:
        feedbacks = []
        fnf = max(0, _integral_count(summary.total_file_not_found, 0))
        if fnf > 0:
            feedbacks.append(DiagnosisFeedback(
                target_type="method",
                target_id="PATH_GENERATORS",
                feedback_type="path_normalize",
                current_value="原始路径输出",
                suggested_value="所有finding路径输出前经过resolve_file_path规范化",
                reason=f"{fnf} 个finding的文件路径无效，"
                       f"诊断方法产出的路径缺少规范化处理",
                confidence=0.85,
                evidence=[f"路径无效: {fnf} 个"],
            ))
        return feedbacks
    def _fixer_gap_feedback(self, rule_id) -> DiagnosisFeedback:
        request_count = max(0, int_or(
            self._history_entry(HISTORY_FIXER_SECTION, rule_id).get(
                FIELD_REQUEST_COUNT), 0)) + 1
        return DiagnosisFeedback(
            target_type="fixer",
            target_id=rule_id,
            feedback_type="coverage_gap",
            current_value="无修复器",
            suggested_value=f"需要开发修复器（第{request_count}次请求）",
            reason=f"规则 {rule_id} 有confirmed finding但无对应修复器，"
                   f"诊断产出无法转化为修复行动",
            confidence=0.9,
            evidence=[f"第{request_count}次被标记为无修复器"],
        )
    def _unfixable_rule_feedbacks(self, unfixable,
                                  emitted_rules: set | None = None) -> list:
        feedbacks = []
        seen = emitted_rules if isinstance(emitted_rules, set) else set()
        for rule_id in actionable_rule_ids(unfixable):
            if len(feedbacks) >= 20:
                break
            if rule_id in seen:
                continue
            seen.add(rule_id)
            feedbacks.append(self._fixer_gap_feedback(rule_id))
        return feedbacks
    @staticmethod
    def _fixer_registry_feedback(coverage_rate) -> DiagnosisFeedback:
        return DiagnosisFeedback(
            target_type="fixer",
            target_id=_FIXER_REGISTRY_TARGET,
            feedback_type="coverage_gap",
            current_value=f"覆盖率 {coverage_rate}",
            suggested_value="扩展修复器注册表覆盖范围，优先覆盖高频诊断规则",
            reason=f"修复器覆盖率仅 {coverage_rate}，大量诊断发现无修复能力，"
                   f"诊断-治疗链路存在覆盖缺口",
            confidence=0.7,
            evidence=[f"覆盖率: {coverage_rate}"],
        )
    def _coverage_gap_issue_feedbacks(
        self, issue: dict, emitted_rules: set | None
    ) -> list[DiagnosisFeedback]:
        issue_type = issue.get("issue_type")
        if issue_type in _COVERAGE_GAP_RULE_ISSUES:
            return self._unfixable_rule_feedbacks(
                issue.get("unfixable_rules", []), emitted_rules)
        if issue_type == "low_fixer_coverage":
            return [self._fixer_registry_feedback(
                issue.get("coverage_rate", "0%"))]
        return []
    def _analyze_coverage_gaps(
        self, summary: TreatmentOutcomeSummary
    ) -> list[DiagnosisFeedback]:
        issues = (summary.issues_discovered
                  if isinstance(summary.issues_discovered, list) else [])
        feedbacks = []
        emitted_rules: set[str] = set()
        emitted_registry = False
        for issue in issues:
            if not isinstance(issue, dict):
                continue
            for feedback in self._coverage_gap_issue_feedbacks(
                    issue, emitted_rules):
                if feedback.target_id == _FIXER_REGISTRY_TARGET:
                    if emitted_registry:
                        continue
                    emitted_registry = True
                feedbacks.append(feedback)
        return feedbacks
    def _analyze_safety_mislabels(
        self, summary: TreatmentOutcomeSummary
    ) -> list[DiagnosisFeedback]:
        patterns = [
            pattern for pattern in _failure_pattern_dicts(summary)
            if pattern.get("type") == "auto_safe_mislabel"
        ]
        if not patterns:
            return []
        count = sum(max(0, _integral_count(pattern.get("count"), 0))
                    for pattern in patterns)
        raw_rule_ids = []
        for pattern in patterns:
            if _integral_count(pattern.get("count"), 0) <= 0:
                continue
            values = pattern.get("rule_ids", [])
            if isinstance(values, str):
                raw_rule_ids.append(values)
            elif isinstance(values, (list, tuple, set, frozenset)):
                raw_rule_ids.extend(values)
        rule_ids = actionable_rule_ids(raw_rule_ids)
        if count <= 0:
            logger.warning(
                "[FeedbackResolver] auto_safe_mislabel 缺少失败/回滚计数，"
                "跳过安全误标反馈")
            return []
        feedbacks = [DiagnosisFeedback(
            target_type="fixer",
            target_id=AUTO_SAFE_REGISTRY_TARGET,
            feedback_type="safety_mislabel",
            current_value=f"{len(rule_ids)} 个规则标记为auto_safe",
            suggested_value=f"重新审查以下规则的auto_safe标签: {rule_ids[:10]}",
            reason=f"{count} 个auto_safe修复实际失败/回滚，"
                   f"安全验证机制存在系统性缺陷",
            confidence=0.85,
            evidence=[f"误标数量: {count}", f"涉及规则: {rule_ids[:10]}"],
        )]
        for rule_id in rule_ids[:20]:
            feedbacks.append(DiagnosisFeedback(
                target_type="fixer",
                target_id=rule_id,
                feedback_type="safety_mislabel",
                current_value="auto_safe=True",
                suggested_value=f"重新审查规则 {rule_id} 的 auto_safe 标签",
                reason=f"规则 {rule_id} 标记 auto_safe 的修复实际失败/回滚，"
                       f"安全标签与执行结果不符",
                confidence=0.85,
                evidence=[f"误标规则: {rule_id}",
                          f"同批误标修复: {count} 个"],
            ))
        return feedbacks
_STATUS_PATTERN_BUCKETS: dict[str, tuple[str, ...]] = {
    "fixed": TX_FIXED_STATUSES,
    "rolled_back": TX_ROLLED_BACK_STATUSES,
    "failed": TX_FAILED_STATUSES,
    "fp_confirmed": TX_FP_CONFIRMED_STATUSES,
}
FIXED_STATES = _STATUS_PATTERN_BUCKETS["fixed"]
_ROLLED_BACK_STATES = _STATUS_PATTERN_BUCKETS["rolled_back"]
_FAILED_STATES = _STATUS_PATTERN_BUCKETS["failed"]
EXECUTED_STATES = FIXED_STATES + _ROLLED_BACK_STATES + _FAILED_STATES
REGRESSED_STATES = _ROLLED_BACK_STATES + _FAILED_STATES
_STATUS_TO_BUCKET: dict[str, str] = {
    status: bucket
    for bucket, statuses in _STATUS_PATTERN_BUCKETS.items()
    for status in statuses
}
def failure_bucket(status: str) -> str:
    return _STATUS_TO_BUCKET.get(_status_key(status), "")
def _non_empty_str(value) -> str:
    return value.strip() if isinstance(value, str) else ""
def _nonnegative_plan_index(value) -> int | None:
    idx = plan_index(value)
    return idx if idx is not None and idx >= 0 else None
def _item_side_effects(it: dict) -> list | None:
    res = it.get("result")
    if isinstance(res, dict) and isinstance(res.get("side_effects"), list):
        return res["side_effects"]
    return None
def _item_reason(it: dict, reason_by_index: dict[int, str]) -> str:
    result = it.get("result")
    description = (_non_empty_str(result.get("description"))
                   if isinstance(result, dict) else "")
    det = it.get("detail")
    if not description and isinstance(det, dict):
        description = _non_empty_str(det.get("reason"))
    if description:
        return description
    idx = _nonnegative_plan_index(it.get("index"))
    if idx is not None:
        return reason_by_index.get(idx, "")
    return ""
def _enrich_treatment_item(it: dict, reason_by_index: dict[int, str]) -> dict:
    e = dict(it)
    if not e.get("file"):
        file_alias = str_or_empty(e.get("file_path"))
        if file_alias:
            e["file"] = file_alias
    if not e.get("side_effects"):
        side_effects = _item_side_effects(it)
        if side_effects is not None:
            e["side_effects"] = side_effects
    if not e.get("reason"):
        reason = _item_reason(it, reason_by_index)
        if reason:
            e["reason"] = reason
    return e
def _enrich_full_key_details(raw_details: list,
                             reason_by_index: dict[int, str]) -> tuple:
    enriched_details = []
    enriched_count = 0
    for d in raw_details:
        if not isinstance(d, dict):
            enriched_details.append(d)
            continue
        enriched = _enrich_treatment_item(d, reason_by_index)
        if enriched != d:
            enriched_count += 1
        enriched_details.append(enriched)
    return enriched_details, enriched_count
def _reason_entry(detail) -> tuple[int, str] | None:
    if not isinstance(detail, dict):
        return None
    idx = _nonnegative_plan_index(detail.get("index"))
    if idx is None:
        return None
    det = detail.get("detail")
    reason = _non_empty_str(det.get("reason")) if isinstance(det, dict) else ""
    if not reason:
        return None
    return idx, reason
def _reason_map_from_details(raw_details: list) -> dict:
    pairs = [pair for pair in map(_reason_entry, raw_details) if pair is not None]
    return dict(pairs)
_VERIFIER_RUN_STATES = ("ai_fixed", "rolled_back")
def _latest_status_rows(details: list) -> list[dict]:
    dict_items = [item for item in details if isinstance(item, dict)]
    latest: dict[int, int] = {}
    for pos, entry in enumerate(dict_items):
        idx = _nonnegative_plan_index(entry.get("index"))
        if idx is not None:
            latest[idx] = pos
    rows = []
    for pos, entry in enumerate(dict_items):
        idx = _nonnegative_plan_index(entry.get("index"))
        if idx is None or latest.get(idx) == pos:
            rows.append(entry)
    return rows
def _count_status_bucket(enriched: list, statuses) -> int:
    return sum(1 for e in enriched
               if _status_key(e.get("status")) in statuses)
def _rebuild_enriched_summary(enriched: list, summary) -> dict:
    new_summary = dict(summary) if isinstance(summary, dict) else {}
    dict_items = _latest_status_rows(enriched)
    if not dict_items:
        return new_summary
    for key, statuses in SUMMARY_STATUS_BUCKETS.items():
        new_summary[key] = _count_status_bucket(dict_items, statuses)
    new_summary[FIELD_ROUTED_TO_FIXER] = _count_status_bucket(
        dict_items, EXECUTED_STATES)
    detail_side_effects = sum(
        len(as_list(e.get("side_effects"))) for e in dict_items)
    declared_side_effects = max(0, _integral_count(
        new_summary.get(FIELD_SIDE_EFFECTS_DETECTED), 0))
    new_summary[FIELD_SIDE_EFFECTS_DETECTED] = max(
        declared_side_effects, detail_side_effects)
    detail_safety_checks = _count_status_bucket(
        dict_items, _VERIFIER_RUN_STATES)
    declared_safety_checks = max(0, _integral_count(
        new_summary.get(FIELD_SAFETY_VERIFIER_USED), 0))
    new_summary[FIELD_SAFETY_VERIFIER_USED] = max(
        declared_safety_checks, detail_safety_checks)
    return new_summary
def _enrich_full_key_report(fix_route_report: dict, raw_details: list,
                           reason_by_index: dict[int, str]) -> dict:
    new_details, enriched_count = _enrich_full_key_details(
        raw_details, reason_by_index)
    report = dict(fix_route_report)
    report["details"] = new_details
    report["summary"] = _rebuild_enriched_summary(
        new_details, fix_route_report.get("summary"))
    if enriched_count:
        logger.info("[TreatmentVerdict] 全键明细边界补全: %d 项",
                    enriched_count)
    return report
def _unplanned_regression_details(details) -> list[dict]:
    if not isinstance(details, (list, tuple)):
        return []
    return [
        detail for detail in details
        if isinstance(detail, dict)
        and _nonnegative_plan_index(detail.get("index")) is None
        and _status_key(detail.get("status")) in REGRESSED_STATES
    ]
def _normalize_items_report(skill_dir: str, fix_route_report: dict,
                            raw_details: list,
                            reason_by_index: dict[int, str]) -> dict:
    try:
        raw_items = load_treatment_items(skill_dir)
    except (OSError, RuntimeError, ValueError) as exc:
        logger.warning(
            "[TreatmentVerdict] item_details 归一化跳过：治疗条目不可读（%s）: %s",
            type(exc).__name__, exc)
        return _enrich_full_key_report(
            fix_route_report, raw_details, reason_by_index)
    items = [item for item in raw_items if isinstance(item, dict)]
    if not items:
        if raw_items:
            logger.warning(
                "[TreatmentVerdict] item_details 归一跳过: 治疗条目 %d 项"
                "全为非 dict 脏条目", len(raw_items))
        return _enrich_full_key_report(
            fix_route_report, raw_details, reason_by_index)
    enriched = [_enrich_treatment_item(item, reason_by_index) for item in items]
    enriched.extend(
        _enrich_treatment_item(detail, reason_by_index)
        for detail in _unplanned_regression_details(raw_details))
    new_summary = _rebuild_enriched_summary(
        enriched, fix_route_report.get("summary"))
    report = dict(fix_route_report)
    report["details"] = enriched
    report["summary"] = new_summary
    logger.info("[TreatmentVerdict] item_details三键形态已按items归一: "
                "details=%d, auto_fixed=%d, fp_confirmed=%d",
                len(enriched), new_summary.get("auto_fixed", 0),
                new_summary.get("fp_confirmed", 0))
    return report
def _has_full_key_details(details: list) -> bool:
    dict_details = [detail for detail in details if isinstance(detail, dict)]
    return bool(dict_details) and all(
        not is_placeholder_rule_id(detail.get("rule_id"))
        for detail in dict_details)
def normalize_fix_route_report(skill_dir: str, fix_route_report: dict) -> dict:
    if not isinstance(fix_route_report, dict):
        return fix_route_report
    raw_details = fix_route_report.get("details")
    if isinstance(raw_details, tuple):
        raw_details = list(raw_details)
    if not isinstance(raw_details, list) or not raw_details:
        return fix_route_report
    reason_by_index = _reason_map_from_details(raw_details)
    if _has_full_key_details(raw_details):
        return _enrich_full_key_report(
            fix_route_report, raw_details, reason_by_index)
    return _normalize_items_report(
        skill_dir, fix_route_report, raw_details, reason_by_index)

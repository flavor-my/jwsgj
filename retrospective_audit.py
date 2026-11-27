from __future__ import annotations  # noqa: I001
import json
import logging
import os
import re
from collections import defaultdict
from collections.abc import Iterator
from dataclasses import asdict, dataclass, field
from typing import ClassVar
from jwsgj.diag_types_normalize import (
    as_dict,
    clamp_unit,
    finite_float_or_none,
    int_metric,
    is_high_severity,
    plan_index,
    signal_bool,
    str_or,
    strict_iterable_list,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    CONCLUSION_V2_MAP,
    CV_RULES,
    FIELD_ADJUSTED_CONFIDENCE,
    FIELD_TOTAL_INPUT_FINDINGS,
    SUB_ENGINE_META,
    TX_FAILED_STATUSES,
    TX_FIXED_STATUSES,
    TX_ROLLED_BACK_STATUSES,
)
from jwsgj.treatment_feedback import _count_side_effect_types
from jwsgj.treatment_state import canonical_locator_key
__all__ = [
    "CrossValidationAudit",
    "CrossValidationAuditResult",
    "DiagnosisAudit",
    "DiagnosisAuditResult",
    "RetrospectiveReport",
    "TreatmentAudit",
    "TreatmentAuditResult",
]
logger = logging.getLogger(__name__)
class _AsDictMixin:
    def to_dict(self) -> dict:
        return asdict(self)
@dataclass
class RetrospectiveReport(_AsDictMixin):
    timestamp: str = ""
    session_id: str = ""
    skill_dir: str = ""
    round_start_ts: str = ""
    diagnosis_audit: list[dict] = field(default_factory=list)
    cv_audit: dict = field(default_factory=dict)
    treatment_audit: dict = field(default_factory=dict)
    scores: dict = field(default_factory=dict)
    good_practices: list[dict] = field(default_factory=list)
    issues_found: list[dict] = field(default_factory=list)
    enhancement_actions: list[dict] = field(default_factory=list)
    summary: str = ""
    enhancement_log: list[dict] = field(default_factory=list)
    code_feedback_result: dict | None = None
    rollback_audit: dict = field(default_factory=dict)
    memory_operations: list[dict] = field(default_factory=list)
    quality_gate_result: dict = field(default_factory=dict)
    pdca_tracking: dict = field(default_factory=dict)
    status: str = "completed"
@dataclass
class DiagnosisAuditResult(_AsDictMixin):
    method_id: str = ""
    method_name: str = ""
    total_findings: int = 0
    confirmed_count: int = 0
    suppressed_count: int = 0
    degraded_count: int = 0
    fixable_count: int = 0
    fixed_successfully: int = 0
    fixed_rolled_back: int = 0
    fixed_failed: int = 0
    precision: float = 0.0
    fix_success_rate: float = 0.0
    rollback_rate: float = 0.0
    fp_indicators: list[str] = field(default_factory=list)
    miss_indicators: list[str] = field(default_factory=list)
    score: float = 0.0
@dataclass
class CrossValidationAuditResult(_AsDictMixin):
    total_input_findings: int = 0
    confirmed: int = 0
    suppressed: int = 0
    degraded: int = 0
    partial_degraded: int = 0
    rule_audits: list[dict] = field(default_factory=list)
    contradictions_found: int = 0
    contradictions_examples: list[dict] = field(default_factory=list)
    confirmation_accuracy: float = 0.0
    suppression_accuracy: float = 0.0
    score: float = 0.0
@dataclass
class TreatmentAuditResult(_AsDictMixin):
    total_items: int = 0
    executed: int = 0
    succeeded: int = 0
    failed: int = 0
    rolled_back: int = 0
    pending_confirm: int = 0
    skipped: int = 0
    fp_confirmed: int = 0
    suggestion: int = 0
    no_fixer: int = 0
    introduced_new_issues: int = 0
    worsened_existing: int = 0
    net_improvement: int = 0
    priority_correct_rate: float = 0.0
    strategy_effectiveness: float = 0.0
    score: float = 0.0
    notes: list[str] = field(default_factory=list)
    priority_assessed: bool | None = None
def _record_entries(value) -> list[dict]:
    return [item for item in strict_iterable_list(value)
            if isinstance(item, dict)]
def _materialize_audit_iterators(value):
    if isinstance(value, dict):
        return {key: _materialize_audit_iterators(item)
                for key, item in value.items()}
    if isinstance(value, list):
        return [_materialize_audit_iterators(item) for item in value]
    if isinstance(value, tuple):
        return tuple(_materialize_audit_iterators(item) for item in value)
    if isinstance(value, Iterator):
        return [_materialize_audit_iterators(item) for item in value]
    return value
def _iter_source_method_ids(sources) -> Iterator[str]:
    seen: set[str] = set()
    for src in strict_iterable_list(sources):
        if isinstance(src, dict):
            mid = _normalize_method_id(src.get("method_id", ""))
        else:
            mid = _normalize_method_id(src)
        if mid and mid not in seen:
            seen.add(mid)
            yield mid
_PLACEHOLDER_METHOD_IDS: frozenset[str] = frozenset(
    {"unknown", "none", "null", "n/a", "na", "-", "?"})
def _normalize_method_id(raw) -> str | None:
    if raw is None or isinstance(raw, bool):
        return None
    if isinstance(raw, (dict, list, tuple, set, frozenset)):
        return None
    if not isinstance(raw, str):
        raw = str(raw)
    raw = raw.strip()
    if not raw or raw.lower() in _PLACEHOLDER_METHOD_IDS:
        return None
    return raw.upper()
_SCORE_BASE = 30.0
_SCORE_CEILING = 100.0
def _bounded_score(score: float) -> float:
    return max(0.0, min(_SCORE_CEILING, score))
def _count_ratio(numerator: int, denominator: int) -> float:
    if denominator <= 0 or numerator <= 0:
        return 0.0
    if numerator >= denominator:
        return 1.0
    return numerator / denominator
_FIX_STATUS_BUCKETS: tuple[tuple[tuple[str, ...], str], ...] = (
    (TX_FIXED_STATUSES, "succeeded"),
    (TX_ROLLED_BACK_STATUSES, "rolled_back"),
    (TX_FAILED_STATUSES, "failed"),
)
_FIX_RECORD_CARRIERS: tuple[str, ...] = (
    "items", "treatment_items", "details", "fix_details",
)
def _fix_bucket(status) -> str | None:
    if not isinstance(status, str):
        return None
    key = status.strip().lower()
    for statuses, bucket in _FIX_STATUS_BUCKETS:
        if key in statuses:
            return bucket
    return None
def _first_record_carrier(treatment_execution: dict, predicate) -> list:
    for key in _FIX_RECORD_CARRIERS:
        records = _record_entries(treatment_execution.get(key))
        if any(predicate(record) for record in records):
            return records
    return []
_SIDE_EFFECT_KEYS: tuple[str, ...] = (
    "introduced_new_issues", "worsened_existing",
    "side_effects_count", "side_effect_count", "total_side_effects",
    "side_effects_detected", "side_effects",
)
_NESTED_RECORD_CARRIERS: tuple[str, ...] = ("result", "detail")
def _has_positive_side_effect_value(key: str, value) -> bool:
    if key == "side_effects":
        return bool(strict_iterable_list(value))
    return int_metric(value, 0) > 0
def _side_effect_evidence(record: object) -> dict:
    if not isinstance(record, dict):
        return {}
    candidates = [record]
    for key in _NESTED_RECORD_CARRIERS:
        nested = record.get(key)
        if isinstance(nested, dict):
            candidates.append(nested)
    evidence = dict(record)
    for candidate in candidates[1:]:
        for key in _SIDE_EFFECT_KEYS:
            if key not in candidate:
                continue
            incoming = candidate[key]
            if key not in evidence or (
                    not _has_positive_side_effect_value(key, evidence[key])
                    and _has_positive_side_effect_value(key, incoming)):
                evidence[key] = incoming
    return evidence
def _has_side_effect_record(record: object) -> bool:
    evidence = _side_effect_evidence(record)
    # 必须是正向副作用值：仅“存在键”但值为 0/空列表时不算副作用记录，
    # 否则首个空记录会截断后续含真实副作用的载体，导致副作用漏计。
    return any(key in evidence
               and _has_positive_side_effect_value(key, evidence[key])
               for key in _SIDE_EFFECT_KEYS)
def _side_effect_records(treatment_execution: dict) -> list[dict]:
    carrier = _first_record_carrier(
        treatment_execution, _has_side_effect_record)
    if carrier:
        return carrier
    return _first_record_carrier(treatment_execution, _has_nonempty_status)
def _plan_path_arg(path) -> str | bytes | None:
    if path is None:
        return None
    try:
        candidate = os.fspath(path)
    except TypeError:
        logger.warning("[TreatmentAudit] 治疗方案路径形态非法(%s)，按未提供处理",
                       type(path).__name__)
        return None
    if isinstance(candidate, bytes):
        return candidate or None
    if not isinstance(candidate, str) or not candidate:
        logger.warning("[TreatmentAudit] 治疗方案路径非文本(%s)，按未提供处理",
                       type(candidate).__name__)
        return None
    return candidate
def _has_nonempty_status(record: object) -> bool:
    return (isinstance(record, dict)
            and isinstance(record.get("status"), str)
            and bool(record["status"].strip()))
def _has_fix_record(record: object) -> bool:
    return (_has_nonempty_status(record)
            and _resolve_fix_record(record)[0] is not None)
_FIX_RULE_KEYS: tuple[str, ...] = ("rule_id", "rule_applied")
def _resolve_fix_record(record: dict) -> tuple[str | None, object]:
    status = record.get("status", "")
    for carrier in (record, record.get("detail")):
        if not isinstance(carrier, dict):
            continue
        for key in _FIX_RULE_KEYS:
            rule_id = _normalize_method_id(carrier.get(key))
            if rule_id is not None:
                return rule_id, status
    return None, status
_CV_DEGRADED_CONCLUSIONS: frozenset[str] = frozenset(
    {"likely"} | {key for key, mapped in CONCLUSION_V2_MAP.items()
                  if mapped == "uncertain"})
_CV_RAW_UNCERTAIN_KEYS: tuple[str, ...] = ("investigated", "review")
def _conclusion_key(value) -> str:
    return str_or(value).strip().lower()
def _effective_conclusion(item: dict) -> str:
    if not isinstance(item, dict):
        return ""
    candidate = _conclusion_key(item.get("conclusion_v2"))
    if candidate:
        mapped = CONCLUSION_V2_MAP.get(candidate)
        if mapped is not None:
            return mapped
    raw = _conclusion_key(item.get("conclusion"))
    return CONCLUSION_V2_MAP.get(raw, raw)
def _finding_identities(item: dict) -> set[str]:
    if not isinstance(item, dict):
        return set()
    identities = set()
    finding_id = str_or(item.get("finding_id")).strip()
    if finding_id:
        identities.add(f"id:{finding_id}")
    locator = canonical_locator_key(str_or(item.get("locator")).strip())
    if locator:
        identities.add(f"locator:{locator}")
    return identities
def _conclusion_bucket(conclusion) -> str | None:
    if not isinstance(conclusion, str):
        return None
    key = _conclusion_key(conclusion)
    if key in ("confirmed", "suppressed"):
        return key
    if key in _CV_DEGRADED_CONCLUSIONS or "degraded" in key:
        return "degraded"
    return None
_VAGUE_PATTERNS: tuple[str, ...] = (
    "TODO", "FIXME", "consider", "review", "check",
    "待办", "待定", "考虑", "复核", "检查",
)
_VAGUE_PATTERN_RE = re.compile(
    r"(?<![a-z0-9_])(?:"
    + "|".join(re.escape(pattern) for pattern in _VAGUE_PATTERNS)
    + r")(?![a-z0-9_])",
    re.IGNORECASE,
)
def _is_vague_finding(finding) -> bool:
    if not isinstance(finding, dict):
        return False
    desc = str(finding.get("description") or finding.get("title")
               or finding.get("message") or "")
    return _VAGUE_PATTERN_RE.search(desc) is not None
def _log_audit_summary(results: list[DiagnosisAuditResult]) -> None:
    if not results:
        logger.info("[DiagnosisAudit] 审计完成: 0 路方法")
        return
    logger.info("[DiagnosisAudit] 审计完成: %d 路方法, "
                "平均评分=%.1f, 最低=%.1f(方法%s), 最高=%.1f(方法%s)",
                len(results), sum(r.score for r in results) / len(results),
                results[0].score, results[0].method_id,
                results[-1].score, results[-1].method_id)
class DiagnosisAudit:
    def audit(
        self, diagnosis_report: dict,
        treatment_execution: dict | None = None,
    ) -> list[DiagnosisAuditResult]:
        results = []
        if not isinstance(diagnosis_report, dict):
            logger.warning("[DiagnosisAudit] 诊断报告顶层非 dict(%s)，按空报告审计",
                           type(diagnosis_report).__name__)
            diagnosis_report = {}
        method_stats = self._extract_method_stats(diagnosis_report)
        fix_results = self._extract_fix_results(treatment_execution)
        for method_id, stats in method_stats.items():
            results.append(self._audit_single_method(method_id, stats, fix_results))
        results.sort(key=lambda r: r.score)
        _log_audit_summary(results)
        return results
    def _extract_method_stats(self, report: dict) -> dict[str, dict]:
        method_details = self._layered_method_details(report)
        method_stats = self._build_layered_stats(method_details)
        top_findings_index = _materialize_audit_iterators(
            self._resolve_top_findings_index(report))
        if top_findings_index:
            self._merge_top_level_findings(
                method_stats, top_findings_index,
                only_missing=bool(method_details))
        top_coverage = self._apply_cv_conclusion_stats(
            method_stats, top_findings_index)
        self._apply_layered_conclusion_stats(method_stats, top_coverage)
        return method_stats
    @staticmethod
    def _layered_method_details(report: dict) -> dict:
        layers = as_dict(report.get("layers"))
        layer2 = as_dict(layers.get("layer2"))
        return as_dict(layer2.get("method_details"))
    @staticmethod
    def _build_layered_stats(method_details: dict) -> dict[str, dict]:
        method_stats: dict[str, dict] = {}
        for raw_id, detail in method_details.items():
            method_id = _normalize_method_id(raw_id)
            if method_id is None or not isinstance(detail, dict):
                continue
            findings = _record_entries(detail.get("findings"))
            stats = method_stats.get(method_id)
            if stats is None:
                method_stats[method_id] = {
                    "method_name": detail.get("method_name", method_id),
                    "total_findings": len(findings),
                    "findings": list(findings),
                    "status": detail.get("status", "unknown"),
                }
                continue
            stats["findings"].extend(findings)
            stats["total_findings"] = len(stats["findings"])
        return method_stats
    @staticmethod
    def _resolve_top_findings_index(report: dict) -> list:
        top_findings_index = _record_entries(report.get("findings_index"))
        if top_findings_index:
            return top_findings_index
        cv_result = as_dict(report.get(CAT_CROSS_VALIDATION))
        cv_findings_index = _record_entries(cv_result.get("findings_index"))
        if cv_findings_index:
            return cv_findings_index
        return top_findings_index
    def _merge_top_level_findings(self, method_stats: dict,
                                  top_findings_index: list, *,
                                  only_missing: bool = False) -> None:
        known_identities: dict[str, set[str]] = {}
        layered_method_ids = set(method_stats) if only_missing else set()
        if only_missing:
            for mid, stats in method_stats.items():
                known_identities[mid] = {
                    identity
                    for finding in _record_entries(stats.get("findings"))
                    for identity in _finding_identities(finding)
                }
        for item in top_findings_index:
            if not isinstance(item, dict):
                continue
            finding_info = {
                "finding_id": item.get("finding_id", ""),
                "locator": item.get("locator", ""),
                "category": item.get("category", ""),
                "severity": item.get("severity", ""),
                "conclusion": _effective_conclusion(item),
                "confidence": item.get("confidence", 0.0),
                "description": item.get("description", ""),
                "title": item.get("title", ""),
                "message": item.get("message", ""),
            }
            identities = _finding_identities(item)
            for mid in _iter_source_method_ids(item.get("sources")):
                is_new_method = mid not in method_stats
                if is_new_method:
                    method_stats[mid] = {
                        "method_name": mid,
                        "total_findings": 0,
                        "findings": [],
                        "status": "from_top_level",
                    }
                elif only_missing:
                    known = known_identities.get(mid, set())
                    if ((not identities and mid in layered_method_ids)
                            or (identities and identities.intersection(known))):
                        continue
                method_stats[mid]["findings"].append(finding_info)
                method_stats[mid]["total_findings"] = len(method_stats[mid]["findings"])
                if only_missing:
                    known_identities.setdefault(mid, set()).update(identities)
    @staticmethod
    def _apply_layered_conclusion_stats(method_stats: dict,
                                        top_coverage: dict | None = None) -> None:
        coverage = top_coverage or {}
        for method_id, stats in method_stats.items():
            for item in _record_entries(stats.get("findings")):
                if method_id in coverage:
                    covered = coverage[method_id]
                    identities = _finding_identities(item)
                    if (covered is None or not identities
                            or identities.intersection(covered)):
                        continue
                stat_key = _conclusion_bucket(_effective_conclusion(item))
                if stat_key is not None:
                    stats[stat_key] = stats.get(stat_key, 0) + 1
    def _apply_cv_conclusion_stats(self, method_stats: dict,
                                   top_findings_index: list) -> dict:
        coverage: dict[str, set[str] | None] = {}
        counted_identities: dict[str, set[str]] = {}
        for item in top_findings_index:
            if not isinstance(item, dict):
                continue
            stat_key = _conclusion_bucket(_effective_conclusion(item))
            identities = _finding_identities(item)
            for mid in _iter_source_method_ids(item.get("sources")):
                if mid not in method_stats or stat_key is None:
                    continue
                counted = counted_identities.setdefault(mid, set())
                if identities and identities.intersection(counted):
                    continue
                counted.update(identities)
                covered = coverage.setdefault(mid, set())
                if covered is not None:
                    if identities:
                        covered.update(identities)
                    else:
                        coverage[mid] = None
                method_stats[mid][stat_key] = (
                    method_stats[mid].get(stat_key, 0) + 1)
        return coverage
    def _extract_fix_results(self, treatment_execution: dict | None) -> dict[str, dict]:
        fix_results = defaultdict(lambda: {
            "succeeded": 0, "rolled_back": 0, "failed": 0,
        })
        if not isinstance(treatment_execution, dict) or not treatment_execution:
            return dict(fix_results)
        for record in _first_record_carrier(treatment_execution,
                                            _has_fix_record):
            if not isinstance(record, dict):
                continue
            rule_id, status = _resolve_fix_record(record)
            if rule_id is None:
                continue
            bucket = _fix_bucket(status)
            if bucket is not None:
                fix_results[rule_id][bucket] += 1
        return dict(fix_results)
    def _method_fix_totals(self, fix_results: dict,
                           method_id: str) -> tuple[int, int, int]:
        succeeded = rolled_back = failed = 0
        for rule_id, result in (fix_results or {}).items():
            if self._rule_belongs_to_method(rule_id, method_id):
                succeeded += result.get("succeeded", 0) or 0
                rolled_back += result.get("rolled_back", 0) or 0
                failed += result.get("failed", 0) or 0
        return succeeded, rolled_back, failed
    def _audit_single_method(self, method_id: str, stats: dict,
                             fix_results: dict) -> DiagnosisAuditResult:
        raw_name = stats.get("method_name")
        audit = DiagnosisAuditResult(
            method_id=method_id,
            method_name=(raw_name.strip()
                         if isinstance(raw_name, str) and raw_name.strip()
                         else method_id),
            total_findings=int_metric(stats.get("total_findings"), 0))
        audit.confirmed_count = int_metric(stats.get("confirmed"), 0)
        audit.suppressed_count = int_metric(stats.get("suppressed"), 0)
        audit.degraded_count = int_metric(stats.get("degraded"), 0)
        classified_total = (audit.confirmed_count + audit.suppressed_count
                            + audit.degraded_count)
        audit.total_findings = max(audit.total_findings, classified_total)
        if audit.total_findings > 0:
            audit.precision = min(
                1.0, audit.confirmed_count / audit.total_findings)
        succeeded, rolled_back, failed = self._method_fix_totals(
            fix_results, method_id)
        audit.fixable_count = succeeded + rolled_back + failed
        audit.fixed_successfully = succeeded
        audit.fixed_rolled_back = rolled_back
        audit.fixed_failed = failed
        if audit.fixable_count > 0:
            audit.fix_success_rate = audit.fixed_successfully / audit.fixable_count
            audit.rollback_rate = audit.fixed_rolled_back / audit.fixable_count
        self._detect_fp_indicators(audit, stats)
        self._detect_miss_indicators(audit, stats)
        audit.score = self._compute_score(audit)
        return audit
    def _detect_fp_indicators(self, audit: DiagnosisAuditResult,
                              stats: dict) -> None:
        for msg in (self._high_suppression_indicator(audit),
                    self._vague_description_indicator(
                        _record_entries(stats.get("findings"))),
                    self._high_rollback_indicator(audit)):
            if msg is not None:
                audit.fp_indicators.append(msg)
    @staticmethod
    def _high_suppression_indicator(audit: DiagnosisAuditResult) -> str | None:
        if not (audit.total_findings >= 3
                and audit.suppressed_count / audit.total_findings > 0.6):
            return None
        return (
            f"高抑制率: {audit.suppressed_count}/{audit.total_findings} "
            f"({audit.suppressed_count / max(audit.total_findings, 1) * 100:.0f}%)"
        )
    @staticmethod
    def _vague_description_indicator(findings: list) -> str | None:
        vague_count = sum(1 for f in findings[:20] if _is_vague_finding(f))
        if vague_count < 2:
            return None
        return (
            f"描述模糊: {vague_count}/{min(len(findings), 20)} 个 finding "
            f"包含模糊词汇 ({', '.join(_VAGUE_PATTERNS)})"
        )
    @staticmethod
    def _high_rollback_indicator(audit: DiagnosisAuditResult) -> str | None:
        if not (audit.fixable_count >= 3
                and audit.fixed_rolled_back / audit.fixable_count > 0.5):
            return None
        return (
            f"高回滚率: {audit.fixed_rolled_back}/{audit.fixable_count} 修复被回滚"
        )
    def _detect_miss_indicators(self, audit: DiagnosisAuditResult,
                                stats: dict) -> None:
        if audit.total_findings == 0 and stats.get("status") == "ok":
            audit.miss_indicators.append(
                "零发现且状态ok：方法可能未实际执行扫描或目标代码无相关模式"
            )
        if audit.total_findings >= 5 and audit.confirmed_count == 0:
            audit.miss_indicators.append(
                f"{audit.total_findings}个发现零确认"
                f"（抑制{audit.suppressed_count}/降级{audit.degraded_count}）："
                f"判定标准可能偏差"
            )
    _RULE_PREFIX_TO_METHOD: ClassVar[dict[str, str]] = {
        "CG": "C", "callgraph": "C", "broken_call": "C", "broken_cross": "C",
        "C1": "C", "blindspot": "C",
        "SIM": "C", "sandbox": "C",
        "MM": "C", "resource_leak": "C", "file_leak": "C", "handle_leak": "C",
        "TRY": "B", "tryceratops": "B", "broad_except": "B", "empty_except": "B",
        "DC": "B", "dead_code": "B", "orphan": "B", "quadrant_dead": "B",
        "AP": "B", "antipattern": "B", "facade": "B",
        "A5": "B", "duplicate_code": "B",
        "GF": "B", "SN": "B", "SL": "B",
        "SZ": "B", "POL": "B", "SYNTAX": "B",
        "CQ": "A", "coupling": "A", "high_coupling": "A",
        "baseline": "A",
        "SD": "A",
        "AI": "A", "AST": "A",
        "A1": "A",
        "A2": "A", "lazy_import": "A", "dynamic_import": "A", "stub_function": "A",
        "A10": "A", "file_scan": "A",
        "D9": "A", "ARCH": "A", "D12": "A",
        "API": "A", "DOC": "A",
        "SE": "D", "SC": "D", "SEC": "D", "SR": "D",
        "vuln": "D", "security": "D", "sql_injection": "D", "path_traversal": "D",
        "TC": "E", "TS": "E", "undertested": "E", "low_coverage": "E",
        "test_quality": "E",
        "RF-MIG": "route_planning", "RF-RW": "route_planning",
        "RF-SPLIT": "boundary_analysis", "RF-MERGE": "boundary_analysis",
        "A7": "F", "auto_fix": "F",
        "A8": "F", "safe": "F", "guard": "F",
        "A9": "F", "gate": "F",
    }
    def _rule_belongs_to_method(self, rule_id: str, method_id: str) -> bool:
        rule_upper = str(rule_id).strip().upper()
        mid = str(method_id).strip().upper()
        if not mid:
            return False
        if rule_upper.startswith((mid + "-", mid + "_")):
            return True
        if rule_upper == mid:
            return True
        owner = _explicit_prefix_owner(rule_upper)
        if owner is not None:
            return owner == mid
        return (self._matches_compact_family(rule_id, mid)
                or self._matches_rule_sources(rule_id, mid))
    @staticmethod
    def _matches_compact_family(rule_id: str, mid: str) -> bool:
        if mid not in _MAIN_METHOD_IDS:
            return False
        rule_upper = rule_id.strip().upper()
        owner = _explicit_prefix_owner(rule_upper)
        if owner is not None:
            return owner == mid
        return _compact_token_owner(rule_upper) == mid
    @staticmethod
    def _matches_rule_sources(rule_id: str, mid: str) -> bool:
        rule = CV_RULES.get(rule_id)
        return bool(rule and mid in rule.source_methods)
    def _compute_score(self, audit: DiagnosisAuditResult) -> float:
        score = _SCORE_BASE
        has_findings = audit.total_findings > 0
        if has_findings:
            score += audit.precision * 35
        else:
            score -= 10
        if has_findings and audit.confirmed_count == 0:
            score -= 15
        score -= min(len(audit.fp_indicators) * 5, 20)
        score -= min(len(audit.miss_indicators) * 3, 15)
        if audit.fixable_count > 0:
            score += audit.fixed_successfully / audit.fixable_count * 35
            score -= audit.rollback_rate * 15
        elif audit.confirmed_count > 0:
            score += 15
        return _bounded_score(score)
_MAIN_METHOD_IDS = frozenset({"A", "B", "C", "D", "E", "F"})
_RULE_EXPLICIT_OWNERS: tuple[tuple[str, str], ...] = tuple(
    sorted(
        ((prefix.upper(), method.upper())
         for prefix, method in DiagnosisAudit._RULE_PREFIX_TO_METHOD.items()),
        key=lambda item: len(item[0]), reverse=True,
    )
)
def _compact_token_owner(rule_upper: str) -> str | None:
    head, sep, _ = rule_upper.partition("-")
    if not sep:
        head, sep, _ = rule_upper.partition("_")
    if sep:
        meta = SUB_ENGINE_META.get(head)
        if isinstance(meta, dict) and meta.get("main"):
            return str(meta["main"]).upper()
        if head in _MAIN_METHOD_IDS:
            return None
    if rule_upper[:1] in _MAIN_METHOD_IDS and rule_upper[1:].isdigit():
        return rule_upper[:1]
    return None
def _explicit_prefix_owner(rule_upper: str) -> str | None:
    for prefix, method in _RULE_EXPLICIT_OWNERS:
        compact_suffix = (rule_upper[len(prefix):]
                          if rule_upper.startswith(prefix) else "")
        if (rule_upper == prefix
                or rule_upper.startswith((prefix + "-", prefix + "_"))
                or (compact_suffix.isdecimal() and not prefix[-1].isdigit())):
            return method
    return None
def _has_execution_data(execution: object) -> bool:
    return isinstance(execution, dict) and bool(execution)
def _str_locator(record: dict) -> str:
    raw = str_or(record.get("locator", "")).strip()
    return canonical_locator_key(raw)
def _fix_record_locator(record: dict) -> str:
    if not isinstance(record, dict):
        return ""
    direct = _str_locator(record)
    if direct:
        return direct
    for key in _NESTED_RECORD_CARRIERS:
        nested = record.get(key)
        if isinstance(nested, dict):
            locator = _str_locator(nested)
            if locator:
                return locator
    return ""
_CONFIRM_STRONG_CONFIDENCE = 0.6
_DEGRADED_ACCURACY_CAP = 0.7
_RULE_OUTCOME_KEYS = (
    "confirmed", "suppressed", "investigated",
    "review", "likely", "uncertain",
)
_EXECUTION_COUNT_FIELDS = (
    "executed", "succeeded", "failed", "rolled_back",
    "pending_confirm", "skipped", "fp_confirmed", "suggestion", "no_fixer",
)
_ITEM_OUTCOME_BUCKETS = tuple(
    field for field in _EXECUTION_COUNT_FIELDS if field != "executed"
)
_ATTEMPTED_ITEM_OUTCOME_BUCKETS = ("succeeded", "failed", "rolled_back")
def _item_outcome_bucket(status: str) -> str | None:
    bucket = _fix_bucket(status)
    if bucket is not None:
        return bucket
    key = status.strip().lower()
    return key if key in _ITEM_OUTCOME_BUCKETS else None
def _count_item_outcomes(records: list) -> dict[str, int] | None:
    final_buckets: dict[object, str | None] = {}
    recognized = False
    for position, record in enumerate(records):
        if not isinstance(record, dict):
            continue
        status = record.get("status")
        if not isinstance(status, str) or not status.strip():
            continue
        recognized = True
        index = plan_index(record.get("index"))
        if index is None or index < 0:
            key: tuple[str, object] = ("position", position)
        else:
            key = ("index", index)
        bucket = _item_outcome_bucket(status)
        if bucket is None:
            logger.warning(
                "[TreatmentAudit] 未识别的非空执行状态 %r，按待确认计数",
                status)
            bucket = "pending_confirm"
        final_buckets[key] = bucket
    if not recognized:
        return None
    counts = {
        bucket: sum(1 for value in final_buckets.values() if value == bucket)
        for bucket in _ITEM_OUTCOME_BUCKETS
    }
    counts["total"] = len(final_buckets)
    return counts
def _valid_confidence(value) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return finite_float_or_none(value)
def _item_field_confidence(item: dict) -> float | None:
    for key in (FIELD_ADJUSTED_CONFIDENCE, "confidence"):
        confidence = _valid_confidence(item.get(key))
        if confidence is not None:
            return confidence
    return None
def _item_confidence(item: dict) -> float:
    confidence = _item_field_confidence(item)
    return 0.0 if confidence is None else confidence
def _source_confidence_index(item: dict) -> dict[str, float]:
    index: dict[str, float] = {}
    for f in _record_entries(item.get("findings")):
        method_id = _normalize_method_id(f.get("_source_method"))
        if method_id is None:
            continue
        confidence = _item_field_confidence(f)
        if confidence is None:
            continue
        if confidence > index.get(method_id, -1.0):
            index[method_id] = confidence
    return index
def _source_confidence(src: dict, mid: str,
                       source_conf: dict[str, float]) -> float | None:
    confidence = _item_field_confidence(src)
    if confidence is not None:
        return confidence
    return source_conf.get(mid) if mid else None
def _collect_source_signals(
        item: dict, sources,
) -> tuple[list[str], list[str], list[str], set[str]]:
    high_conf: list[str] = []
    low_conf: list[str] = []
    degraded: list[str] = []
    verdicts: set[str] = set()
    source_conf = _source_confidence_index(item)
    for raw_src in strict_iterable_list(sources):
        src = raw_src
        if isinstance(src, str):
            src = {"method_id": src}
        if not isinstance(src, dict):
            continue
        mid = _normalize_method_id(src.get("method_id")) or ""
        verdict = _conclusion_key(src.get("verdict"))
        verdict = (CONCLUSION_V2_MAP.get(verdict, verdict) if verdict
                   else _effective_conclusion(src))
        if verdict:
            verdicts.add(verdict)
        if not mid:
            continue
        if signal_bool(src.get("degraded")):
            degraded.append(mid)
        conf = _source_confidence(src, mid, source_conf)
        if conf is None:
            continue
        if conf >= 0.8:
            high_conf.append(mid)
        elif conf < 0.3:
            low_conf.append(mid)
    return high_conf, low_conf, degraded, verdicts
def _source_conflict_example(
        kind: str, sources: list, conclusion: str, confidence: float,
) -> dict:
    return {
        "type": kind,
        "sources": sources,
        "conclusion": conclusion,
        FIELD_ADJUSTED_CONFIDENCE: confidence,
    }
def _is_partial_degraded(finding: dict) -> bool:
    return (signal_bool(finding.get("_partial_degrade"))
            or finding.get("_degrade_status") == "partial_degraded")
def _count_partial_degraded(findings_index: list) -> int:
    count = 0
    for item in _record_entries(findings_index):
        candidates = [item, *_record_entries(item.get("findings"))]
        if any(_is_partial_degraded(finding) for finding in candidates):
            count += 1
    return count
def _has_suppression_basis(item: dict) -> bool:
    if str_or(item.get("suppression_reason")).strip():
        return True
    return bool(str_or(item.get("rule_applied")).strip())
def _collect_locators(items, predicate=None) -> set[str]:
    locators: set[str] = set()
    for item in items or []:
        if not isinstance(item, dict):
            continue
        if predicate is not None and not predicate(item):
            continue
        loc = _str_locator(item)
        if loc:
            locators.add(loc)
    return locators
def _items_with_conclusion(items, conclusion: str) -> list[dict]:
    expected = _conclusion_key(conclusion)
    return [item for item in _record_entries(items)
            if _effective_conclusion(item) == expected]
def _has_located_fix_status(record: object) -> bool:
    return (_has_nonempty_status(record)
            and bool(_fix_record_locator(record)))
def _fix_status_records(treatment_execution: dict) -> list:
    located = _first_record_carrier(
        treatment_execution, _has_located_fix_status)
    if located:
        return located
    return _first_record_carrier(treatment_execution, _has_nonempty_status)
def _final_fix_status_by_locator(details) -> dict[str, str | None]:
    final: dict[str, str | None] = {}
    for detail in _record_entries(details):
        loc = _fix_record_locator(detail)
        status = detail.get("status")
        if not loc or not isinstance(status, str) or not status.strip():
            continue
        final[loc] = _fix_bucket(status)
    return final
class CrossValidationAudit:
    def audit(
        self, diagnosis_report: dict,
        treatment_execution: dict | None = None,
    ) -> CrossValidationAuditResult:
        result = CrossValidationAuditResult()
        if not isinstance(diagnosis_report, dict):
            logger.warning("[CVAudit] 诊断报告顶层非 dict(%s)，按空报告审计",
                           type(diagnosis_report).__name__)
            diagnosis_report = {}
        treatment_execution = _materialize_audit_iterators(treatment_execution)
        cv, findings_index = self._resolve_cv_sections(diagnosis_report)
        self._seed_counts(result, cv, findings_index)
        result.rule_audits = self._audit_rules(
            _record_entries(cv.get("rules_detail")))
        result.contradictions_found, result.contradictions_examples = \
            self._detect_contradictions(findings_index)
        result.confirmation_accuracy = self._compute_confirmation_accuracy(
            findings_index, treatment_execution)
        result.suppression_accuracy = self._compute_suppression_accuracy(
            findings_index, treatment_execution)
        result.score = self._compute_score(result)
        logger.info("[CVAudit] 交叉验证审计: 确认精度=%.2f, 抑制精度=%.2f, "
                    "矛盾=%d, 评分=%.1f",
                     result.confirmation_accuracy,
                     result.suppression_accuracy,
                     result.contradictions_found,
                     result.score)
        return result
    @staticmethod
    def _resolve_cv_sections(diagnosis_report: dict) -> tuple[dict, list]:
        top_findings = _record_entries(diagnosis_report.get("findings_index"))
        cv = as_dict(diagnosis_report.get(CAT_CROSS_VALIDATION))
        if top_findings:
            return cv or diagnosis_report, top_findings
        if cv:
            return cv, _record_entries(cv.get("findings_index"))
        return diagnosis_report, top_findings
    @staticmethod
    def _seed_counts(result: CrossValidationAuditResult, cv: dict,
                     findings_index: list) -> None:
        measured = CrossValidationAudit._count_conclusion_index(findings_index)
        result.total_input_findings = int_metric(
            cv.get(FIELD_TOTAL_INPUT_FINDINGS), len(findings_index))
        result.confirmed = int_metric(
            cv.get("confirmed"), measured["confirmed"])
        result.suppressed = int_metric(
            cv.get("suppressed"), measured["suppressed"])
        uncertain = int_metric(cv.get("uncertain"), -1)
        if uncertain < 0:
            uncertain = max(
                measured["uncertain"],
                sum(int_metric(cv.get(key), 0)
                    for key in _CV_RAW_UNCERTAIN_KEYS),
            )
        result.degraded = (
            int_metric(cv.get("likely"), measured["likely"])
            + uncertain
            + int_metric(cv.get("degraded"), measured["degraded"])
        )
        result.partial_degraded = int_metric(
            cv.get("partial_degraded"), _count_partial_degraded(findings_index))
    @staticmethod
    def _count_conclusion_index(findings_index: list) -> dict[str, int]:
        counts = {key: 0 for key in _RULE_OUTCOME_KEYS}
        counts["degraded"] = 0
        for item in findings_index or []:
            if not isinstance(item, dict):
                continue
            conclusion = _effective_conclusion(item)
            if conclusion in counts and conclusion != "degraded":
                counts[conclusion] += 1
            elif _conclusion_bucket(conclusion) == "degraded":
                counts["degraded"] += 1
        return counts
    def _audit_rules(self, rules_detail: list) -> list[dict]:
        return [e for rule in _record_entries(rules_detail)
                if (e := self._audit_single_rule(rule)) is not None]
    @staticmethod
    def _rule_outcome_conclusion(rule: dict) -> str:
        parts = []
        for key in _RULE_OUTCOME_KEYS:
            count = int_metric(rule.get(key), 0)
            if count <= 0 and key in ("review", "likely", "uncertain"):
                count = int_metric(rule.get(f"{key}_c"), 0)
            if count > 0:
                parts.append(f"{key}={count}")
        return ", ".join(parts)
    @staticmethod
    def _rule_issue_messages(triggered: int, conclusion: str,
                             rule_name: str,
                             triggered_known: bool) -> list[str]:
        issues = []
        if triggered and not conclusion:
            issues.append("规则被触发但未产出结论，可能存在短路或条件分支缺失")
        if triggered == 0 and rule_name and triggered_known:
            issues.append("规则从未被触发，可能是死规则或触发条件过严")
        return issues
    @staticmethod
    def _rule_triggered_state(rule: dict) -> tuple[int, bool]:
        raw = rule.get("triggered")
        if raw is None or (isinstance(raw, str) and not raw.strip()):
            return 0, False
        return (1 if signal_bool(raw) else 0), True
    def _audit_single_rule(self, rule: dict) -> dict | None:
        if not isinstance(rule, dict):
            return None
        rule_name = str_or(rule.get("rule_id"))
        triggered, triggered_known = self._rule_triggered_state(rule)
        conclusion = self._rule_outcome_conclusion(rule)
        return {
            "rule_name": rule_name,
            "triggered": triggered,
            "triggered_known": triggered_known,
            "conclusion": conclusion,
            "applied_to": int_metric(rule.get("findings_count"), 0),
            "issues": self._rule_issue_messages(
                triggered, conclusion, rule_name, triggered_known),
        }
    def _detect_contradictions(self, findings_index: list) -> tuple[int, list[dict]]:
        contradictions = 0
        examples = []
        for item in _record_entries(findings_index):
            _c, _e = self._evaluate_item_contradictions(item)
            contradictions += _c
            examples.extend(_e)
        return contradictions, examples[:10]
    def _evaluate_item_contradictions(self, item: dict) -> tuple[int, list[dict]]:
        conclusion = _effective_conclusion(item)
        adjusted_confidence = _item_confidence(item)
        high_conf_sources, low_conf_sources, degraded_sources, source_verdicts = \
            _collect_source_signals(item, item.get("sources"))
        examples = [
            example for example in (
                self._hc_suppressed_example(
                    high_conf_sources, conclusion, adjusted_confidence),
                self._lc_confirmed_example(
                    low_conf_sources, conclusion, adjusted_confidence),
                self._divergence_example(
                    source_verdicts, conclusion, adjusted_confidence),
                self._degraded_confirm_example(
                    item, degraded_sources, conclusion),
            ) if example is not None
        ]
        return len(examples), examples
    @staticmethod
    def _hc_suppressed_example(
        high_conf_sources: list, conclusion: str, confidence: float,
    ) -> dict | None:
        if not (high_conf_sources and conclusion == "suppressed"):
            return None
        return _source_conflict_example(
            "high_confidence_suppressed", high_conf_sources, conclusion,
            confidence)
    @staticmethod
    def _lc_confirmed_example(
        low_conf_sources: list, conclusion: str, confidence: float,
    ) -> dict | None:
        if not (low_conf_sources and conclusion == "confirmed"):
            return None
        return _source_conflict_example(
            "low_confidence_confirmed", low_conf_sources, conclusion,
            confidence)
    @staticmethod
    def _divergence_example(
        source_verdicts: set, conclusion: str, confidence: float,
    ) -> dict | None:
        if not (len(source_verdicts) > 1
                and "confirmed" in source_verdicts
                and "suppressed" in source_verdicts):
            return None
        return {
            "type": "internal_source_divergence",
            "source_verdicts": sorted(source_verdicts),
            "conclusion": conclusion,
            FIELD_ADJUSTED_CONFIDENCE: confidence,
        }
    @staticmethod
    def _degraded_confirm_example(
        item: dict, degraded_sources: list, conclusion: str,
    ) -> dict | None:
        if not (conclusion == "confirmed"
                and (degraded_sources
                     or signal_bool(item.get("_is_degraded")))):
            return None
        return {
            "type": "degraded_but_confirmed",
            "source": ", ".join(degraded_sources),
            "conclusion": conclusion,
        }
    def _compute_confirmation_accuracy(self, findings_index: list,
                                       treatment_execution: dict | None) -> float:
        confirmed_items = _items_with_conclusion(findings_index, "confirmed")
        if not _has_execution_data(treatment_execution):
            return self._compute_confirmation_degraded(confirmed_items)
        confirmed_locators = _collect_locators(confirmed_items)
        if not confirmed_locators:
            return self._compute_confirmation_degraded(confirmed_items)
        details = _fix_status_records(treatment_execution)
        succeeded, total = self._count_fixed_in_confirmed(
            details, confirmed_locators)
        if total <= 0:
            return self._compute_confirmation_degraded(
                _items_with_conclusion(findings_index, "confirmed"))
        return succeeded / total
    @staticmethod
    def _compute_confirmation_degraded(confirmed_items: list) -> float:
        if not confirmed_items:
            return 0.0
        strong = sum(
            1 for item in confirmed_items
            if _item_confidence(item) >= _CONFIRM_STRONG_CONFIDENCE)
        return min(strong / len(confirmed_items), _DEGRADED_ACCURACY_CAP)
    @staticmethod
    def _count_fixed_in_confirmed(
        details, confirmed_locators: set[str],
    ) -> tuple[int, int]:
        final = _final_fix_status_by_locator(details)
        attempted = {loc for loc in confirmed_locators & final.keys()
                     if final[loc] is not None}
        succeeded = {
            loc for loc in attempted if final[loc] == "succeeded"
        }
        return len(succeeded), len(attempted)
    def _compute_suppression_accuracy(self, findings_index: list,
                                       treatment_execution: dict | None) -> float:
        suppressed = _items_with_conclusion(findings_index, "suppressed")
        if not suppressed:
            return 0.0
        false_suppressions = 0
        if not _has_execution_data(treatment_execution):
            return self._compute_suppression_degraded(suppressed)
        confirmed_locators = _collect_locators(
            _items_with_conclusion(findings_index, "confirmed"))
        fixed_locators = self._collect_fixed_locators(
            _fix_status_records(treatment_execution))
        if not (confirmed_locators or fixed_locators):
            return self._compute_suppression_degraded(suppressed)
        false_suppressions = self._count_false_suppressions(
            suppressed, fixed_locators, confirmed_locators)
        if false_suppressions > 0:
            logger.warning("[CVAudit] 发现 %d 个错误抑制（被抑制的 finding 实际被修复）",
                           false_suppressions)
        return (len(suppressed) - false_suppressions) / len(suppressed)
    @staticmethod
    def _compute_suppression_degraded(suppressed: list) -> float:
        if not suppressed:
            return 0.0
        has_reason = sum(
            1 for item in suppressed if _has_suppression_basis(item))
        raw_accuracy = has_reason / len(suppressed)
        return min(raw_accuracy, _DEGRADED_ACCURACY_CAP)
    @staticmethod
    def _collect_fixed_locators(details: list) -> set[str]:
        return {
            loc for loc, bucket in _final_fix_status_by_locator(details).items()
            if bucket == "succeeded"
        }
    @staticmethod
    def _count_false_suppressions(
        suppressed: list, fixed_locators: set[str], confirmed_locators: set[str],
    ) -> int:
        false_suppressions = 0
        for item in suppressed:
            loc = _str_locator(item)
            if loc and (loc in fixed_locators
                        or loc in confirmed_locators):
                false_suppressions += 1
        return false_suppressions
    def _compute_score(self, result: CrossValidationAuditResult) -> float:
        score = _SCORE_BASE
        score += result.confirmation_accuracy * 25
        score += result.suppression_accuracy * 15
        score -= min(result.contradictions_found * 3, 15)
        if result.total_input_findings > 0:
            coverage = _count_ratio(
                result.confirmed + result.suppressed + result.degraded,
                result.total_input_findings)
            score += coverage * 10
        return _bounded_score(score)
class TreatmentAudit:
    def audit(
        self, treatment_plan: dict,
        treatment_execution: dict | None = None,
        treatment_plan_json_path: str | None = None,
    ) -> TreatmentAuditResult:
        treatment_execution = _materialize_audit_iterators(treatment_execution)
        treatment_plan = _materialize_audit_iterators(treatment_plan)
        result = TreatmentAuditResult()
        result.priority_assessed = False
        self._evaluate_plan_input(result, treatment_plan, treatment_plan_json_path)
        self._extract_execution_metrics(result, treatment_execution)
        self._track_side_effect_sources(result, treatment_execution)
        result.score = self._compute_score(result)
        logger.info("[TreatmentAudit] 治疗审计: 成功=%d, 失败=%d, "
                    "回滚=%d, 净改善=%d, 评分=%.1f",
                     result.succeeded, result.failed, result.rolled_back,
                     result.net_improvement, result.score)
        return result
    def _evaluate_plan_input(self, result: TreatmentAuditResult,
                              treatment_plan: dict,
                              treatment_plan_json_path: str | None) -> None:
        plan: object = treatment_plan
        if not (isinstance(plan, dict) and plan.get("items") is not None):
            plan = self._load_plan_json(treatment_plan_json_path) or plan
        if isinstance(plan, dict) and plan:
            self._evaluate_plan_quality(
                result, _record_entries(plan.get("items")),
                plan.get("execution_order"))
    @staticmethod
    def _load_plan_json(path) -> dict | None:
        candidate = _plan_path_arg(path)
        if candidate is None or not os.path.isfile(candidate):
            return None
        try:
            with open(candidate, encoding="utf-8-sig") as f:
                plan = json.load(f)
        except (OSError, ValueError, RecursionError) as e:
            logger.warning(
                "[TreatmentAudit] 治疗方案加载失败，回退 dict 直传: %s", e)
            return None
        if isinstance(plan, dict):
            return plan
        logger.warning("[TreatmentAudit] 治疗方案顶层非 dict: %s",
                       type(plan).__name__)
        return None
    def _extract_execution_metrics(self, result: TreatmentAuditResult,
                                   treatment_execution: dict | None) -> None:
        if not isinstance(treatment_execution, dict) or not treatment_execution:
            return
        for attr in _EXECUTION_COUNT_FIELDS:
            setattr(result, attr,
                    int_metric(treatment_execution.get(attr), 0))
        result.succeeded += int_metric(treatment_execution.get("ai_fixed"), 0)
        outcomes = _count_item_outcomes(
            _first_record_carrier(treatment_execution, _has_nonempty_status))
        if outcomes is not None:
            for attr in _ITEM_OUTCOME_BUCKETS:
                setattr(result, attr, max(getattr(result, attr), outcomes[attr]))
        outcome_executed = sum(
            getattr(result, attr) for attr in _ATTEMPTED_ITEM_OUTCOME_BUCKETS)
        result.executed = max(result.executed, outcome_executed)
        result.total_items = max(
            result.total_items,
            int_metric(treatment_execution.get("total"), 0),
            int_metric(treatment_execution.get("total_items"), 0),
            outcomes["total"] if outcomes is not None else 0,
        )
        introduced, worsened = self._detail_side_effect_totals(
            _side_effect_records(treatment_execution))
        result.introduced_new_issues = max(
            int_metric(treatment_execution.get("introduced_new_issues"), 0),
            introduced)
        result.worsened_existing = max(
            int_metric(treatment_execution.get("worsened_existing"), 0),
            worsened)
        result.net_improvement = max(
            0, result.succeeded - result.introduced_new_issues
            - result.worsened_existing)
        if result.introduced_new_issues > 0:
            result.notes.append(
                f"治疗引入 {result.introduced_new_issues} 个新问题，"
                f"净改善 {result.net_improvement}")
        if result.worsened_existing > 0:
            result.notes.append(
                f"治疗恶化了 {result.worsened_existing} 个已有代码")
    @staticmethod
    def _detail_side_effect_totals(details: list) -> tuple[int, int]:
        introduced = 0
        worsened = 0
        for d in details:
            if isinstance(d, dict):
                d = _side_effect_evidence(d)
                d_introduced = int_metric(d.get("introduced_new_issues"), 0)
                d_worsened = int_metric(d.get("worsened_existing"), 0)
                side_effects = strict_iterable_list(d.get("side_effects"))
                structured_new, structured_worsened = _count_side_effect_types(
                    side_effects)
                se_count = max(
                    len(side_effects),
                    int_metric(d.get("side_effects_count"), 0),
                    int_metric(d.get("side_effect_count"), 0),
                    int_metric(d.get("total_side_effects"), 0),
                    int_metric(d.get("side_effects_detected"), 0),
                )
                new_count = max(d_introduced, structured_new)
                worsened_count = max(d_worsened, structured_worsened)
                unclassified_count = max(
                    0, se_count - new_count - worsened_count)
                introduced += new_count + unclassified_count
                worsened += worsened_count
        return introduced, worsened
    def _evaluate_plan_quality(self, result: TreatmentAuditResult,
                               items: list,
                               execution_order: list | None = None) -> None:
        items = _record_entries(items)
        result.total_items = len(items)
        if items:
            result.priority_assessed = True
            result.priority_correct_rate = self._check_priority_correctness(
                items, execution_order)
            result.strategy_effectiveness = self._check_strategy_effectiveness(items)
    @staticmethod
    def _is_high_priority_item(item) -> bool:
        if not isinstance(item, dict):
            return False
        level = str_or(item.get("priority")).strip()
        if not level:
            level = str_or(item.get("severity")).strip()
        return is_high_severity(level, "P1")
    def _check_priority_correctness(self, items: list,
                                     execution_order: list | None = None) -> float:
        if not items:
            return 1.0
        ordered = self._items_in_execution_order(items, execution_order)
        p0_p1_count = sum(
            1 for it in ordered if self._is_high_priority_item(it))
        total = len(ordered)
        if p0_p1_count == 0:
            return 1.0
        half = max(1, total // 2)
        p0_p1_in_first_half = sum(
            1 for it in ordered[:half] if self._is_high_priority_item(it))
        return p0_p1_in_first_half / min(p0_p1_count, half)
    @staticmethod
    def _execution_order_index(execution_order) -> dict[str, int]:
        index: dict[str, int] = {}
        for position, raw_locator in enumerate(strict_iterable_list(execution_order)):
            if not isinstance(raw_locator, str):
                continue
            locator = canonical_locator_key(raw_locator.strip())
            if locator and locator not in index:
                index[locator] = position
        return index
    @staticmethod
    def _items_in_execution_order(items: list,
                                   execution_order: list | None) -> list:
        order_index = TreatmentAudit._execution_order_index(execution_order)
        if not order_index:
            return items
        tail = max(order_index.values()) + 1
        return sorted(
            items,
            key=lambda it: (order_index.get(_str_locator(it), tail)
                            if isinstance(it, dict) else tail))
    def _check_strategy_effectiveness(self, items: list) -> float:
        if not items:
            return 1.0
        total = len(items)
        known = sum(1 for it in items
                    if isinstance(it, dict)
                    and isinstance(it.get("strategy"), str)
                    and it["strategy"].strip().lower() not in ("", "unknown"))
        return known / total
    def _track_side_effect_sources(self, result: TreatmentAuditResult,
                                   treatment_execution: dict | None) -> None:
        if not isinstance(treatment_execution, dict) or not treatment_execution:
            return
        for detail in _side_effect_records(treatment_execution):
            evidence = _side_effect_evidence(detail)
            side_effects = strict_iterable_list(evidence.get("side_effects"))
            if not side_effects:
                continue
            rule_id = (_normalize_method_id(detail.get("rule_id"))
                       or _normalize_method_id(detail.get("rule_applied"))
                       or _normalize_method_id(evidence.get("rule_id"))
                       or _normalize_method_id(evidence.get("rule_applied"))
                       or "unknown")
            for se in side_effects:
                result.notes.append(
                    f"副作用来源: 规则 {rule_id} 修复导致 {se}")
    def _compute_score(self, result: TreatmentAuditResult) -> float:
        score = _SCORE_BASE
        fixable = result.succeeded + result.failed + result.rolled_back
        if fixable > 0:
            score += clamp_unit(result.succeeded / fixable) * 30
        if result.total_items > 0:
            net_rate = _count_ratio(
                result.net_improvement, result.total_items)
            score += net_rate * 20
        side_effect_count = max(
            0, result.introduced_new_issues + result.worsened_existing)
        score -= side_effect_count * 5
        score += result.priority_correct_rate * 10
        score += result.strategy_effectiveness * 5
        return _bounded_score(score)

from __future__ import annotations  # noqa: I001
import logging
import math
import os
from dataclasses import dataclass, field
from decimal import Decimal, InvalidOperation
from typing import Any
from jwsgj.diag_types_defs import dict_findings, severity_breakdown_of
from jwsgj.diag_types_normalize import (
    degrade_factor_of,
    findings_container,
    get_max_severity,
    is_default_confidence,
    is_real_number,
    normalize_severity_rank,
    parse_locator_file,
    parse_locator_line,
    safe_finding_line,
    severity_literal_from_rank,
    source_id_text,
    timestamp_ms,
)
from jwsgj.diag_types_normalize import (
    signal_bool as _base_signal_bool,
)
from jwsgj.diag_types_vocab import (
    CONF_BOOST_MODERATE,
    CONF_CAP,
    CONF_FLOOR,
    CONF_HIGH,
    CONF_LOW,
    CONF_MEDIUM,
    CONF_VERY_HIGH,
    FIELD_ADJUSTED_CONFIDENCE,
    FIELD_BASE_CONFIDENCE,
    FIELD_EVIDENCE_FAMILIES,
    FIELD_EVIDENCE_STRENGTH,
    FIELD_MUTATION_CONFIRMED,
    FP_RATE_HIGH,
    HIGH_SEVERITY_PROTECTED,
    LOW_RELIABILITY_BASE,
    METHOD_SUB_RULES,
    SEVERITY_RANK,
    SIGNAL_BASELINE_HIT_COUNT,
    SIGNAL_BASELINE_PERSISTENT_NOISE,
    SIGNAL_BIZFLOW_CONFIDENCE_BOOST,
    SIGNAL_ENSEMBLE_GROUP_COUNT,
    SIGNAL_ENSEMBLE_LOW_CONFIDENCE,
    SIGNAL_MUTATION_CONFIRMED_DEAD,
    SIGNAL_MUTATION_VERIFIED,
    SIGNAL_REFDEPTH_CHAIN_DEPTH,
    SIGNAL_REFDEPTH_CONFIDENCE_BOOST,
    SIGNAL_REFDEPTH_IN_DEGREE,
    SIGNAL_REFDEPTH_ISOLATED,
    SIGNAL_REFDEPTH_PRIORITY_BOOST,
    SOURCE_SEQUENCE_TYPES,
)
from jwsgj.fix_guide_rule_identity import (
    CONFLICT_COMPLEXITY_FAMILIES,
    CONFLICT_DEAD_CODE_FAMILIES,
    CONFLICTING_PAIRS,
    matches_dead_code_signal,
)
from jwsgj.xv_evidence_strength import (
    dominant_rule_family_by_method,
    evidence_strength_by_rule_family,
    family_reliability_base,
    independent_sources,
)
from jwsgj.xv_threshold_learning import (
    PRECISE_SMOKE_FAMILIES,
    RULE_FP_TRACKER,
    SINGLE_SOURCE_CONFIRM_THRESHOLD,
)
logger = logging.getLogger(__name__)
__all__ = [
    'CONTRADICTION_SEVERITY_DECISION',
    'SIGNAL_REGISTRY',
    'ArbitrationResult',
    'XVArbiter',
    'apply_annotation_adjustments',
    'collect_arbiter_signals',
    'collect_processed_signals',
    'detect_contradiction',
    'find_conflicting_pair',
    'get_contradiction_decision',
    'handle_contradictions',
    'max_severity_of_findings',
    'post_match_suppression',
    'register_arbiter_signal',
    'upgrade_evidence_qualified',
]
logger.info("xv_arbiter 判定面已加载: %d 项导出", len(__all__))
SIGNAL_REGISTRY: dict[str, dict[str, Any]] = {  # jwsgj:suppress E1-MUTABLE-GLOBAL TP-07 — 审计认可：信号注册表容器（register_arbiter_signal 显式登记+参数校验），非共享状态缺陷
    SIGNAL_BASELINE_PERSISTENT_NOISE: {
        "key": "baseline_persistent_noise", "type": "bool", "agg": "any"},
    SIGNAL_BASELINE_HIT_COUNT: {
        "key": "baseline_hit_count", "type": "int", "agg": "max"},
    "_baseline_confidence_multiplier": {
        "key": "baseline_confidence_multiplier", "type": "float", "agg": "min"},
    "_bizflow_reachable": {"key": "bizflow_reachable", "type": "bool", "agg": "any"},
    "_bizflow_fp_candidate": {
        "key": "bizflow_fp_candidate", "type": "bool", "agg": "any"},
    "_bizflow_entry_count": {"key": "bizflow_entry_count", "type": "int", "agg": "max"},
    "_bizflow_unresolved": {"key": "bizflow_unresolved", "type": "bool", "agg": "any"},
    SIGNAL_REFDEPTH_ISOLATED: {
        "key": "refdepth_isolated", "type": "bool", "agg": "any"},
    SIGNAL_REFDEPTH_PRIORITY_BOOST: {
        "key": "refdepth_boosted", "type": "int", "agg": "any_positive"},
    SIGNAL_REFDEPTH_IN_DEGREE: {
        "key": "refdepth_in_degree", "type": "int", "agg": "max"},
    SIGNAL_REFDEPTH_CHAIN_DEPTH: {
        "key": "refdepth_chain_depth", "type": "int", "agg": "max"},
    "_ensemble_is_confirmed": {
        "key": "ensemble_confirmed", "type": "bool", "agg": "any"},
    SIGNAL_ENSEMBLE_LOW_CONFIDENCE: {
        "key": "ensemble_low_confidence", "type": "bool", "agg": "any"},
    SIGNAL_ENSEMBLE_GROUP_COUNT: {
        "key": "ensemble_group_count", "type": "int", "agg": "max"},
    "_ensemble_confidence_multiplier": {
        "key": "ensemble_multiplier", "type": "float", "agg": "min"},
    SIGNAL_MUTATION_CONFIRMED_DEAD: {
        "key": FIELD_MUTATION_CONFIRMED, "type": "bool", "agg": "any"},
    SIGNAL_MUTATION_VERIFIED: {
        "key": "mutation_verified", "type": "bool", "agg": "any"},
    "_mutation_inconclusive": {
        "key": "mutation_inconclusive", "type": "bool", "agg": "any"},
    "_partial_degrade": {"key": "has_partial_source", "type": "bool", "agg": "any"},
    "_vcs_recency_boost": {"key": "vcs_recency_boost", "type": "bool", "agg": "any"},
    "_counter_evidence": {"key": "counter_evidence", "type": "bool", "agg": "any"},
    "_test_triage_smoke_pass": {
        "key": "test_triage_smoke_pass", "type": "bool", "agg": "any"},
    "_test_triage_smoke_fail": {
        "key": "test_triage_smoke_fail", "type": "bool", "agg": "any"},
}
_SIGNAL_VALUE_TYPES: frozenset[str] = frozenset({"bool", "int", "float"})
_SIGNAL_AGGREGATORS: frozenset[str] = frozenset(
    {"any", "all", "max", "min", "any_positive"})
_SIGNAL_COMBINATIONS: frozenset[tuple[str, str]] = frozenset({
    ("bool", "any"), ("int", "any"), ("float", "any"),
    ("bool", "all"),
    ("int", "max"), ("int", "min"),
    ("float", "max"), ("float", "min"),
    ("int", "any_positive"), ("float", "any_positive"),
})
def register_arbiter_signal(
    field_name: str,
    signal_key: str,
    value_type: str = "bool",
    aggregator: str = "any",
) -> None:
    try:
        if (not isinstance(field_name, str) or not field_name.strip()
                or not isinstance(signal_key, str) or not signal_key.strip()):
            logger.error(
                "[SignalBus] 拒绝注册信号 %r: field_name/signal_key 必须为非空字符串",
                field_name)
            return
        if value_type not in _SIGNAL_VALUE_TYPES:
            logger.error("[SignalBus] 拒绝注册信号 %s: 非法 value_type=%r "
                         "(合法: bool/int/float)", field_name, value_type)
            return
        if aggregator not in _SIGNAL_AGGREGATORS:
            logger.error("[SignalBus] 拒绝注册信号 %s: 非法 aggregator=%r "
                         "(合法: any/all/max/min/any_positive)",
                         field_name, aggregator)
            return
        if (value_type, aggregator) not in _SIGNAL_COMBINATIONS:
            logger.error(
                "[SignalBus] 拒绝注册信号 %s: 组合 type=%s/agg=%s 永不命中"
                "聚合分支（该类型观测在该策略下恒不可聚合，属静默永久"
                "失效注册）", field_name, value_type, aggregator)
            return
        schema_owner = next((
            owner for owner, reg in SIGNAL_REGISTRY.items()
            if owner != field_name and isinstance(reg, dict)
            and reg.get("key") == signal_key
            and (reg.get("type") != value_type
                 or reg.get("agg") != aggregator)
        ), "")
        if schema_owner:
            logger.error(
                "[SignalBus] 拒绝注册信号 %s: signal_key=%s 已由 %s "
                "以不同 type/agg 登记；共享聚合值不得使用冲突模式",
                field_name, signal_key, schema_owner)
            return
        SIGNAL_REGISTRY[field_name] = {
            "key": signal_key,
            "type": value_type,
            "agg": aggregator,
        }
        logger.info("[SignalBus] 注册信号: %s -> %s (type=%s, agg=%s)",
                    field_name, signal_key, value_type, aggregator)
    except Exception:
        logger.exception("[SignalBus] 注册信号失败 %s", field_name)
def _numeric_signal_default(reg: dict) -> Any:
    if reg["type"] == "float" and reg["agg"] == "min":
        return 1.0
    return 0
def _init_signal_defaults() -> dict[str, Any]:
    signals: dict[str, Any] = {}
    for reg in SIGNAL_REGISTRY.values():
        sk = reg["key"]
        if sk in signals:
            continue
        if reg["type"] == "bool":
            signals[sk] = reg.get("agg") == "all"
            continue
        if reg["type"] in ("int", "float"):
            signals[sk] = _numeric_signal_default(reg)
    return signals
_MISSING_SIGNAL = object()
def _numeric_value(value: Any) -> int | float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return value if math.isfinite(value) else None
    if not isinstance(value, str):
        return None
    text = value.strip()
    if not text:
        return None
    try:
        number = float(text)
    except (TypeError, ValueError):  # jwsgj:silent-ok 非数值文本不是数值信号
        return None
    if math.isfinite(number):
        return int(number) if number.is_integer() else number
    try:
        arbitrary = Decimal(text)
    except InvalidOperation:  # jwsgj:silent-ok 非有限数值不是有效信号
        return None
    if not arbitrary.is_finite():
        return None
    return int(arbitrary) if arbitrary == arbitrary.to_integral_value() else None
def _as_counter(value: Any) -> int:
    number = _numeric_value(value)
    return max(int(number), 0) if number is not None else 0
def _signal_bool(value: Any) -> bool:
    if isinstance(value, str):
        number = _numeric_value(value)
        if number is not None:
            return number != 0
    return _base_signal_bool(value)
def _is_reachability_observation(value) -> bool:
    if isinstance(value, bool):
        return True
    if isinstance(value, int):
        return True
    if isinstance(value, float):
        return math.isfinite(value)
    if not isinstance(value, str):
        return False
    text = value.strip().lower()
    if text in {"true", "false", "yes", "no"}:
        return True
    return _numeric_value(text) is not None
def _classify_observation(reg: dict, val) -> tuple[bool, bool]:
    agg, vtype = reg["agg"], reg["type"]
    if agg == "any":
        return _classify_any_observation(vtype, val)
    if agg == "all":
        _bool_accepted = vtype == "bool"
        return _bool_accepted, _bool_accepted and _signal_bool(val)
    if agg in ("max", "min"):
        _numeric = _numeric_value(val)
        _observed = _numeric is not None
        return _observed, _observed and _numeric > 0
    if agg == "any_positive":
        _numeric = _numeric_value(val)
        _positive = _numeric is not None and _numeric > 0
        return _positive, _positive
    return False, False
def _classify_any_observation(vtype: str, val) -> tuple[bool, bool]:
    if vtype == "bool":
        _truthy = _signal_bool(val)
        return _truthy, _truthy
    if vtype in ("int", "float"):
        _numeric = _numeric_value(val)
        _positive = _numeric is not None and _numeric > 0
        return _positive, _positive
    return False, False
def _aggregate_signal(signals: dict[str, Any], sk: str, val, reg: dict,
                      first_observed: bool) -> bool:
    if reg["type"] in ("int", "float"):
        val = _numeric_value(val)
        if val is None:
            return False
    signals[sk] = _merged_signal_value(
        reg["agg"], reg["type"], signals.get(sk, _MISSING_SIGNAL),
        val, first_observed)
    return True
def _merge_any_value(current, val, vtype: str, first_observed: bool) -> Any:
    if vtype == "bool":
        return True
    if first_observed:
        return val
    return max(0 if current is _MISSING_SIGNAL else current, val)
def _merge_all_value(current, val) -> bool:
    return ((True if current is _MISSING_SIGNAL else current)
            and _signal_bool(val))
def _merge_extreme_value(current, val, agg: str,
                         first_observed: bool) -> Any:
    if first_observed or current is _MISSING_SIGNAL:
        return val
    return max(current, val) if agg == "max" else min(current, val)
def _merge_any_positive_value(current, val, first_observed: bool) -> Any:
    if first_observed or current is _MISSING_SIGNAL:
        return val
    return max(current, val)
def _merged_signal_value(agg: str, vtype: str, current, val,
                         first_observed: bool) -> Any:
    if agg == "any":
        return _merge_any_value(current, val, vtype, first_observed)
    if agg == "all":
        return _merge_all_value(current, val)
    if agg in ("max", "min"):
        return _merge_extreme_value(current, val, agg, first_observed)
    if agg == "any_positive":
        return _merge_any_positive_value(current, val, first_observed)
    return True
def _source_method_of(f: dict) -> str:
    return source_id_text(f.get("_source_method"))
def _record_signal_source(signal_sources: dict[str, list[str]],
                          signal_key: str, source_method: str) -> None:
    if not source_method or source_method == "unknown":
        return
    sources = signal_sources.setdefault(signal_key, [])
    if source_method not in sources:
        sources.append(source_method)
def collect_processed_signals(findings: list[dict] | None) -> set[str]:
    processed: set[str] = set()
    for f in (findings or []):
        if not isinstance(f, dict):
            continue
        _sig = f.get("_xv_processed_signals", set())
        if not isinstance(_sig, (set, frozenset, list, tuple)):
            continue
        processed.update(item for item in _sig if isinstance(item, str))
    return processed
def _collect_registry_pass(
        findings: list[dict]) -> tuple[dict[str, Any], set[str],
                                      dict[str, list[str]]]:
    signals = _init_signal_defaults()
    observed: set[str] = set()
    sources: dict[str, list[str]] = {}
    for f in findings:
        if not isinstance(f, dict):
            continue
        source_method = _source_method_of(f)
        for field_name, reg in SIGNAL_REGISTRY.items():
            sk = reg["key"]
            val = f.get(field_name)
            if val is None:
                continue
            accepted, activates = _classify_observation(reg, val)
            if accepted and _aggregate_signal(
                    signals, sk, val, reg, sk not in observed):
                observed.add(sk)
            if activates:
                _record_signal_source(sources, sk, source_method)
    return signals, observed, sources
def _finalize_all_aggregates(signals: dict[str, Any],
                             observed: set[str]) -> None:
    for reg in SIGNAL_REGISTRY.values():
        if reg.get("agg") == "all" and reg["key"] not in observed:
            signals[reg["key"]] = False
def _infer_bizflow_unreachable(findings: list[dict],
                               signals: dict[str, Any]) -> None:
    bizflow_observed = any(
        isinstance(f, dict)
        and _is_reachability_observation(f.get("_bizflow_reachable"))
        for f in findings)
    signals["bizflow_unreachable"] = bool(
        bizflow_observed
        and signals.get("bizflow_reachable") is False
        and not signals.get("bizflow_unresolved", False))
def _is_mutation_refuted(f: dict) -> bool:
    return (
        _signal_bool(f.get(SIGNAL_MUTATION_VERIFIED))
        and not _signal_bool(f.get(SIGNAL_MUTATION_CONFIRMED_DEAD))
        and not _signal_bool(f.get("_mutation_inconclusive"))
    )
def _infer_mutation_refuted(signals: dict[str, Any]) -> None:
    signals["mutation_refuted"] = bool(
        signals["mutation_verified"]
        and not signals[FIELD_MUTATION_CONFIRMED]
        and not signals.get("mutation_inconclusive", False))
def collect_arbiter_signals(findings: list[dict]) -> dict[str, Any]:
    findings = findings if isinstance(findings, (list, tuple)) else []
    signals, observed, sources = _collect_registry_pass(findings)
    _finalize_all_aggregates(signals, observed)
    _infer_bizflow_unreachable(findings, signals)
    _infer_mutation_refuted(signals)
    signals["_signal_sources"] = sources
    return signals
_ARBITRATION_CHAIN_MAX = 500
_SIGNAL_STRENGTH_WEIGHTS: dict[str, float] = {
    SIGNAL_MUTATION_CONFIRMED_DEAD: 0.30,
    "_ensemble_is_confirmed": 0.25,
    SIGNAL_BASELINE_PERSISTENT_NOISE: 0.20,
    "_bizflow_reachable": 0.15,
    SIGNAL_REFDEPTH_ISOLATED: 0.10,
}
_PARTIAL_SOURCE_CONF_CAP: float = 0.65
_FULLY_ISOLATED_CONF_FACTOR: float = 0.80
@dataclass
class ArbitrationResult:
    conclusion: str
    confidence: float
    arbitrations_applied: list[str] = field(default_factory=list)
    downgraded: bool = False
    upgraded: bool = False
    original_conclusion: str = ""
    original_confidence: float = 0.0
    signal_sources: dict[str, list[str]] = field(default_factory=dict)
def upgrade_evidence_qualified(findings: list[dict]) -> tuple[bool, str]:
    _fs = [f for f in (findings or []) if isinstance(f, dict)]
    if not _fs:
        return False, "no-evidence"
    if all(map(is_default_confidence, _fs)):
        return False, "all-default-confidence"
    if all(map(_is_weak_self_confidence, _fs)):
        return False, "weak-self-confidence"
    _bases = _family_bases_of(_fs)
    if _bases and max(_bases) < LOW_RELIABILITY_BASE:
        return False, "low-reliability-family"
    return True, ""
def _is_weak_self_confidence(f: dict) -> bool:
    confidence = _numeric_value(f.get("confidence"))
    return (confidence is None
            or confidence < SINGLE_SOURCE_CONFIRM_THRESHOLD)
def _family_bases_of(findings: list[dict]) -> list[float]:
    return [family_reliability_base(str(f.get("rule_family", "")))
            for f in findings if f.get("rule_family")]
_CONCLUSION_ORDER: dict[str, int] = {
    "contradictory": 0,
    "suppressed": 1,
    "uncertain": 2,
    "investigated": 2,
    "review": 2,
    "reviewed": 2,
    "likely": 3,
    "confirmed": 4,
}
_UPGRADABLE_CONCLUSIONS = frozenset(
    conclusion for conclusion, rank in _CONCLUSION_ORDER.items()
    if rank in (2, 3)
)
def _cappable_to_likely(conclusion: str) -> bool:
    if conclusion not in _UPGRADABLE_CONCLUSIONS:
        return False
    _rank = _CONCLUSION_ORDER.get(conclusion)
    return _rank is not None and _rank < _CONCLUSION_ORDER["likely"]
def _net_direction(original: str, final: str) -> tuple[bool, bool]:
    _orig_rank = _CONCLUSION_ORDER.get(original)
    _final_rank = _CONCLUSION_ORDER.get(final)
    if _orig_rank is None or _final_rank is None:
        return False, False
    return _final_rank < _orig_rank, _final_rank > _orig_rank
def _rule3_mutation_over_baseline(result: ArbitrationResult, signals: dict) -> None:
    if (signals.get(FIELD_MUTATION_CONFIRMED, False)
            and signals.get("baseline_persistent_noise", False)
            and result.conclusion in _UPGRADABLE_CONCLUSIONS):
        result.conclusion = "confirmed"
        result.upgraded = True
        result.arbitrations_applied.append("mutation>baseline:→confirmed")
def _rule3_ensemble_over_baseline(result: ArbitrationResult,
                                  signals: dict, findings) -> None:
    if not (signals.get("ensemble_confirmed", False)
            and signals.get("baseline_persistent_noise", False)
            and result.conclusion in _UPGRADABLE_CONCLUSIONS):
        return
    _qualified, _reason = upgrade_evidence_qualified(findings or [])
    if _qualified:
        result.conclusion = "confirmed"
        result.upgraded = True
        result.arbitrations_applied.append("ensemble>baseline:→confirmed")
        return
    if _cappable_to_likely(result.conclusion):
        result.conclusion = "likely"
        result.upgraded = True
        result.arbitrations_applied.append(
            f"upgrade_capped_likely:ensemble-baseline/{_reason}")
        return
    result.arbitrations_applied.append(
        f"upgrade_capped_likely:not_applicable({result.conclusion})"
        f"/ensemble-baseline/{_reason}")
def _rule3_mutation_refuted_bizflow(result: ArbitrationResult,
                                    signals: dict, is_high_sev: bool) -> None:
    if not (signals.get("mutation_refuted", False)
            and signals.get("bizflow_fp_candidate", False)):
        return
    if result.conclusion == "confirmed" and not is_high_sev:
        result.conclusion = "likely"
        result.downgraded = True
        result.arbitrations_applied.append("mutation>bizflow_fp:confirmed→likely")
    elif result.conclusion == "confirmed":
        result.arbitrations_applied.append("mutation>bizflow_fp:high_sev_protected(skip)")
    else:
        result.arbitrations_applied.append("mutation>bizflow_fp:not_confirmed(skip)")
def _downgrade_confirmed(result: ArbitrationResult, is_high_sev: bool,
                         rule_label: str) -> bool:
    if result.conclusion != "confirmed":
        result.arbitrations_applied.append(
            f"{rule_label}:skip(conclusion={result.conclusion})")
        return False
    if is_high_sev:
        result.arbitrations_applied.append(
            f"{rule_label}:high_sev_protected(skip)")
        return False
    result.conclusion = "likely"
    result.downgraded = True
    result.arbitrations_applied.append(f"{rule_label}:confirmed→likely")
    return True
def _rule3_contradictory_pairs(result: ArbitrationResult,
                               signals: dict, is_high_sev: bool) -> bool:
    # 返回“是否实际执行了降级”：矛盾对降级必须锁定后续单信号升级，
    # 否则 bizflow_unreachable 升级会在同一轮仲裁里把降级回滚成 confirmed。
    pair_downgraded = False
    if (signals.get("ensemble_confirmed", False)
            and signals.get("refdepth_isolated", False)):
        pair_downgraded = _downgrade_confirmed(
            result, is_high_sev, "ensemble+isolated") or pair_downgraded
    if (signals.get("bizflow_unreachable", False)
            and signals.get("refdepth_boosted", False)):
        pair_downgraded = _downgrade_confirmed(
            result, is_high_sev,
            "bizflow_unreachable+refdepth_boosted") or pair_downgraded
    return pair_downgraded
def _rule3_partial_confirmed(result: ArbitrationResult,
                             signals: dict, is_high_sev: bool) -> None:
    if not (signals.get("has_partial_source", False)
            and result.conclusion == "confirmed"):
        return
    if is_high_sev:
        result.arbitrations_applied.append(
            "partial+confirmed:high_sev_protected(skip)")
        return
    result.conclusion = "likely"
    result.downgraded = True
    result.arbitrations_applied.append("partial+confirmed:confirmed→likely")
def _bizflow_upgrade_allowed(result: ArbitrationResult,
                            signals: dict[str, Any], is_high_sev: bool,
                            locks: _BizflowUpgradeLocks) -> bool:
    return (
        signals.get("bizflow_unreachable", False)
        and not signals.get("bizflow_fp_candidate", False)
        and not is_high_sev
        and not locks.isolated_applied
        and not locks.partial_locked
        and not locks.mult_applied
        and not locks.pair_downgraded
        and result.conclusion in _UPGRADABLE_CONCLUSIONS
    )
@dataclass(frozen=True)
class _BizflowUpgradeLocks:
    partial_locked: bool = False
    isolated_applied: bool = False
    mult_applied: bool = False
    pair_downgraded: bool = False
def _normalize_confidence(value: Any) -> float:
    number = _numeric_value(value)
    if number is None or number <= 0:
        return 0.0
    if number >= 1:
        return 1.0
    return float(number)
def _finalize_result(result: ArbitrationResult) -> ArbitrationResult:
    result.confidence = _normalize_confidence(result.confidence)
    result.downgraded, result.upgraded = _net_direction(
        result.original_conclusion, result.conclusion)
    return result
def _pristine_result(conclusion: str,
                     base_confidence: float) -> ArbitrationResult:
    _base = _normalize_confidence(base_confidence)
    return ArbitrationResult(
        conclusion=conclusion,
        confidence=_base,
        original_conclusion=conclusion,
        original_confidence=_base,
    )
def _cap_partial_confidence(result: ArbitrationResult, conf_cap: float) -> None:
    if result.confidence > conf_cap:
        result.confidence = conf_cap
        result.arbitrations_applied.append(
            f"partial_source_confidence_cap:{conf_cap}")
class XVArbiter:
    def __init__(self):
        self.stats = {
            "arbiter_calls": 0,
            "downgrades": 0,
            "upgrades": 0,
            "high_sev_protected": 0,
            "partial_excluded": 0,
            "arbiter_errors": 0,
        }
        self._arbitration_chain: list[dict[str, Any]] = []
    def _stamp_chain(self, result: ArbitrationResult, findings: list[dict],
                     signals: dict[str, Any], is_high_sev: bool) -> None:
        self._arbitration_chain.append({
            "original_conclusion": result.original_conclusion,
            "final_conclusion": result.conclusion,
            "confidence_change": round(
                result.confidence - result.original_confidence, 3),
            "applied_rules": result.arbitrations_applied.copy(),
            "findings_count": len(findings),
            "is_high_sev": is_high_sev,
            "signal_strength": self._calculate_signal_strength(signals),
        })
        if len(self._arbitration_chain) > _ARBITRATION_CHAIN_MAX:
            del self._arbitration_chain[:-_ARBITRATION_CHAIN_MAX]
    def arbitrate(
        self,
        conclusion: str,
        base_confidence: float,
        findings: list[dict],
    ) -> ArbitrationResult:
        try:
            self.stats["arbiter_calls"] += 1
            findings = dict_findings(findings)
            result = _pristine_result(conclusion, base_confidence)
            if not findings:
                _finalize_result(result)
                self._stamp_chain(result, findings, {}, is_high_sev=False)
                return result
            max_sev = get_max_severity(findings)
            sev_upper = str(max_sev).upper()
            is_high_sev = sev_upper in HIGH_SEVERITY_PROTECTED
            signals = collect_arbiter_signals(findings)
            _signal_sources = signals.pop("_signal_sources", {})
            _early_result = self._protect_suppressed_high_sev(
                result, signals, findings, sev_upper, is_high_sev, _signal_sources)
            if _early_result is not None:
                return _early_result
            _p2_lock = SEVERITY_RANK.get(sev_upper, 3) == 2 and conclusion == "confirmed"
            self._apply_partial_source_exclusion(
                result, signals, is_high_sev, _p2_lock)
            result, pair_downgraded = self._arbitrate_complex_signals(
                result, signals, is_high_sev, findings)
            result = self._dampen_contradictory_signals(
                result, signals, is_high_sev, findings, _p2_lock,
                pair_downgraded)
            _finalize_result(result)
            self._stamp_chain(result, findings, signals, is_high_sev)
            result.signal_sources = _signal_sources
            if "partial_excluded:confirmed→likely" in result.arbitrations_applied:
                self.stats["partial_excluded"] += 1
            if result.downgraded:
                self.stats["downgrades"] += 1
            if result.upgraded:
                self.stats["upgrades"] += 1
            return result
        except Exception:
            logger.exception("[Arbiter] arbitrate 降级 (conclusion=%s)", conclusion)
            self.stats["arbiter_errors"] += 1
            return _finalize_result(_pristine_result(conclusion, base_confidence))
    def _apply_partial_source_exclusion(
        self, result: ArbitrationResult, signals: dict[str, Any],
        is_high_sev: bool, p2_lock: bool,
    ) -> None:
        if not signals.get("has_partial_source", False):
            return
        if result.conclusion == "confirmed" and not is_high_sev:
            result.conclusion = "likely"
            result.arbitrations_applied.append("partial_excluded:confirmed→likely")
        _cap_partial_confidence(
            result, CONF_HIGH if p2_lock else _PARTIAL_SOURCE_CONF_CAP)
    def _protect_suppressed_high_sev(
        self, result: ArbitrationResult, signals: dict[str, Any],
        findings: list[dict], sev_upper: str, is_high_sev: bool,
        signal_sources: dict[str, list[str]],
    ) -> ArbitrationResult | None:
        if not (is_high_sev and result.original_conclusion == "suppressed"):
            return None
        mutation_confirmed = signals.get(FIELD_MUTATION_CONFIRMED, False)
        is_dead_code_family = self._is_dead_code_family(findings)
        _sev_rank = SEVERITY_RANK.get(sev_upper, 3)
        if mutation_confirmed and is_dead_code_family:
            result.conclusion = "confirmed"
            result.arbitrations_applied.append(
                f"mutation_overrides_suppression:P{_sev_rank}")
        else:
            result.conclusion = "likely"
            result.arbitrations_applied.append(f"high_sev_protect:P{_sev_rank}")
            self.stats["high_sev_protected"] += 1
        if signals.get("has_partial_source", False):
            _cap_partial_confidence(result, _PARTIAL_SOURCE_CONF_CAP)
        result.signal_sources = signal_sources
        _finalize_result(result)
        if result.upgraded:
            self.stats["upgrades"] += 1
        self._stamp_chain(result, findings, signals, is_high_sev)
        return result
    def _calculate_signal_strength(self, signals: dict[str, Any]) -> float:
        strength = 0.0
        for field_name, weight in _SIGNAL_STRENGTH_WEIGHTS.items():
            _reg = SIGNAL_REGISTRY.get(field_name)
            if _reg is not None and signals.get(_reg["key"], False):
                strength += weight
        total_weight = sum(_SIGNAL_STRENGTH_WEIGHTS.values())
        return min(1.0, strength / total_weight) if total_weight > 0 else 0.0
    def _arbitrate_complex_signals(
        self,
        result: ArbitrationResult,
        signals: dict[str, Any],
        is_high_sev: bool,
        findings: list[dict],
    ) -> tuple[ArbitrationResult, bool]:
        _rule3_mutation_over_baseline(result, signals)
        _rule3_ensemble_over_baseline(result, signals, findings)
        _rule3_mutation_refuted_bizflow(result, signals, is_high_sev)
        pair_downgraded = _rule3_contradictory_pairs(
            result, signals, is_high_sev)
        _rule3_partial_confirmed(result, signals, is_high_sev)
        return result, pair_downgraded
    def _dampen_contradictory_signals(
        self,
        result: ArbitrationResult,
        signals: dict[str, Any],
        is_high_sev: bool,
        findings: list[dict],
        p2_lock: bool,
        pair_downgraded: bool = False,
    ) -> ArbitrationResult:
        _processed = collect_processed_signals(findings)
        isolated_applied = self._apply_fully_isolated_dampen(
            result, signals, is_high_sev, p2_lock,
            "refdepth_mult" in _processed)
        partial_locked = signals.get("has_partial_source", False)
        self._apply_bizflow_unreachable_upgrade(
            result, signals, is_high_sev, findings,
            _BizflowUpgradeLocks(
                partial_locked=partial_locked,
                isolated_applied=isolated_applied,
                mult_applied="bizflow_mult" in _processed,
                pair_downgraded=pair_downgraded))
        return result
    def _apply_fully_isolated_dampen(self, result: ArbitrationResult,
                                     signals: dict[str, Any],
                                     is_high_sev: bool, p2_lock: bool,
                                     refdepth_already_processed: bool) -> bool:
        dampen_allowed = all((
            signals.get("refdepth_isolated", False),
            signals.get("refdepth_in_degree", 0) == 0,
            signals.get("refdepth_chain_depth", 0) == 0,
            not is_high_sev,
            not p2_lock,
            not refdepth_already_processed,
        ))
        if not dampen_allowed:
            return False
        if result.conclusion == "confirmed":
            result.conclusion = "likely"
            result.arbitrations_applied.append("fully_isolated:confirmed→likely")
        result.confidence = round(
            result.confidence * _FULLY_ISOLATED_CONF_FACTOR, 3)
        result.arbitrations_applied.append(
            f"fully_isolated:confidence*{_FULLY_ISOLATED_CONF_FACTOR:.2f}")
        return True
    def _apply_bizflow_unreachable_upgrade(
            self, result: ArbitrationResult, signals: dict[str, Any],
            is_high_sev: bool, findings,
            locks: _BizflowUpgradeLocks) -> None:
        if not _bizflow_upgrade_allowed(result, signals, is_high_sev, locks):
            return
        is_dead_code = self._is_dead_code_family(findings)
        _qualified, _reason = upgrade_evidence_qualified(findings or [])
        if is_dead_code and _qualified:
            result.conclusion = "confirmed"
            result.upgraded = True
            result.arbitrations_applied.append("bizflow_unreachable:→confirmed(dead_code)")
            return
        _capped = _cappable_to_likely(result.conclusion)
        if _capped:
            result.conclusion = "likely"
            result.upgraded = True
            if not is_dead_code:
                result.arbitrations_applied.append("bizflow_unreachable:→likely(non_dead_code)")
        if is_dead_code:
            if _capped:
                result.arbitrations_applied.append(
                    f"upgrade_capped_likely:bizflow-dead-code/{_reason}")
            else:
                result.arbitrations_applied.append(
                    f"upgrade_capped_likely:not_applicable({result.conclusion})"
                    f"/bizflow-dead-code/{_reason}")
    @staticmethod
    def _is_dead_code_family(findings: list[dict]) -> bool:
        return any(
            matches_dead_code_signal(f.get("rule_family", ""))
            or matches_dead_code_signal(f.get("rule_id", ""))
            for f in (findings or [])
            if isinstance(f, dict)
        )
_ARBITER: XVArbiter = XVArbiter()
_FP_TRACKER_MIN_SAMPLES = 5
def _is_high_severity_finding(finding) -> bool:
    return (
        isinstance(finding, dict)
        and normalize_severity_rank(finding.get("severity")) <= 1
    )
def _flag_any(findings, key) -> bool:
    return any(_signal_bool(f.get(key)) for f in dict_findings(findings))
def _numeric_signals(findings, key) -> list:
    return [
        value for value in (
            _numeric_value(f.get(key)) for f in dict_findings(findings))
        if value is not None
    ]
def _multiplier_signals(findings, key, upper: float) -> list:
    return [
        value for value in _numeric_signals(findings, key)
        if 0.0 <= value <= upper
    ]
def _apply_conf_multiplier(base_conf, adjustments, label, mult, detail=""):
    mult = max(0.0, min(2.0, mult))
    base_conf = max(0.0, min(1.0, base_conf * mult))
    adjustments.append(f"{label}={mult:.2f}{detail}")
    return base_conf

def _multiplier_from_boost(boost: int | float) -> float:
    if boost >= 1.0:
        return 2.0
    if boost <= -1.0:
        return 0.0
    return 1.0 + boost

def _format_boost(boost: int | float) -> str:
    return f"{Decimal(boost):+.2f}"
def _has_strong_smoke_fail(rows) -> bool:
    return any(
        _signal_bool(f.get("_test_triage_smoke_fail"))
        and not _signal_bool(f.get("_test_triage_symbol_level_fail"))
        for f in dict_findings(rows)
    )
def _adj_falsify(findings, base_conf, conclusion, adjustments):
    if not _flag_any(findings, "_falsify_failed"):
        return base_conf, conclusion
    _strong = any((
        _flag_any(findings, SIGNAL_MUTATION_CONFIRMED_DEAD),
        _flag_any(findings, "_ensemble_is_confirmed"),
        _has_strong_smoke_fail(findings),
    ))
    if _strong:
        return base_conf, conclusion
    _level = {"confirmed": "likely", "likely": "uncertain"}
    if conclusion in _level:
        adjustments.append(f"falsify_pattern_absent_downgrade:{conclusion}->{_level[conclusion]}")
        base_conf = max(0.0, base_conf - 0.15)
        return base_conf, _level[conclusion]
    return base_conf, conclusion
def _adj_rule15_narrowed(findings, base_conf, conclusion, adjustments) -> tuple:
    for _adj in _NARROWED_CHAIN:
        base_conf, conclusion = _adj(
            findings, base_conf, conclusion, adjustments)
    return base_conf, conclusion
def _all_findings_default_confidence(findings) -> bool:
    _rows = dict_findings(findings)
    return bool(_rows) and all(is_default_confidence(f) for f in _rows)
def _note_annotation_trace(adjustments, trace_before, base_conf,
                           conclusion, strength):
    adjustments.append({
        "_trace": "annotation_before_after",
        "before": trace_before,
        "after": {
            "conclusion": conclusion,
            "base_conf": base_conf,
            "strength": strength,
        },
        "applied_steps": [a for a in adjustments if isinstance(a, str)],
    })
def _adj_post_chain(findings, base_conf, conclusion, adjustments, rule_id):
    _pre_arbiter_conf = base_conf
    _pre_arbiter_conclusion = conclusion
    base_conf, conclusion = _adj_arbiter(
        findings, base_conf, conclusion, adjustments)
    base_conf, conclusion = _adj_degradation_protection(
        base_conf, conclusion, adjustments, _pre_arbiter_conf,
        pre_arbiter_conclusion=_pre_arbiter_conclusion)
    if (conclusion == "confirmed" and rule_id != "规则15"
            and _all_findings_default_confidence(findings)):
        conclusion = "likely"
        adjustments.append("all_default_confidence_cap: confirmed->likely")
    return base_conf, conclusion
def apply_annotation_adjustments(
    entry: dict, base_conf: float, strength: float,
    conclusion: str, rule_id: str,
) -> tuple:
    adjustments = []
    base_conf = _normalize_confidence(base_conf)
    findings = entry.get("findings", []) if isinstance(entry, dict) else []
    findings = findings if isinstance(findings, (list, tuple)) else []
    if not findings:
        return base_conf, strength, conclusion, adjustments
    _trace_before = {"conclusion": conclusion, "base_conf": base_conf,
                     "strength": strength}
    if rule_id == "规则15" and conclusion == "confirmed":
        base_conf, conclusion = _adj_rule15_narrowed(
            findings, base_conf, conclusion, adjustments)
        _note_annotation_trace(adjustments, _trace_before, base_conf,
                               conclusion, strength)
        return base_conf, strength, conclusion, adjustments
    for _adj in _ADJ_CHAIN:
        base_conf, conclusion = _adj(
            findings, base_conf, conclusion, adjustments)
    base_conf = max(0.0, min(1.0, base_conf))
    base_conf, conclusion = _adj_post_chain(
        findings, base_conf, conclusion, adjustments, rule_id)
    _note_annotation_trace(adjustments, _trace_before, base_conf,
                           conclusion, strength)
    return base_conf, strength, conclusion, adjustments
def _baseline_eligible_rows(findings) -> list:
    return [f for f in dict_findings(findings)
            if not _is_high_severity_finding(f)]
def _baseline_multiplier(findings) -> float:
    mults = _multiplier_signals(
        _baseline_eligible_rows(findings),
        "_baseline_confidence_multiplier", 1.0)
    return min(mults) if mults else 1.0
def _baseline_noise_flagged(findings) -> bool:
    return _flag_any(
        _baseline_eligible_rows(findings), SIGNAL_BASELINE_PERSISTENT_NOISE)
def _adj_baseline(findings, base_conf, conclusion, adjustments):
    baseline_mult = _baseline_multiplier(findings)
    if baseline_mult < 1.0:
        base_conf = _apply_conf_multiplier(
            base_conf, adjustments, "baseline_mult", baseline_mult)
    if conclusion == "confirmed" and _baseline_noise_flagged(findings):
        conclusion = "likely"
        adjustments.append("baseline_noise: confirmed->likely")
    return base_conf, conclusion
def _channel_boost(findings, key: str) -> int | float | None:
    boosts = [boost for boost in _numeric_signals(findings, key) if boost != 0]
    if not boosts:
        return None
    return min(boosts) if any(boost < 0 for boost in boosts) else max(boosts)
def _adj_bizflow(findings, base_conf, conclusion, adjustments):
    bizflow_boost = _channel_boost(findings, SIGNAL_BIZFLOW_CONFIDENCE_BOOST)
    if bizflow_boost is not None:
        base_conf = _apply_conf_multiplier(
            base_conf, adjustments, "bizflow_mult",
            _multiplier_from_boost(bizflow_boost),
            f"(boost={_format_boost(bizflow_boost)})")
    if (conclusion == "confirmed"
            and _flag_any(findings, "_bizflow_fp_candidate")
            and not _mutation_refuted_bizflow_high_severity_protected(findings)):
        conclusion = "likely"
        adjustments.append("bizflow_fp: confirmed->likely")
    return base_conf, conclusion
def _ensemble_multiplier(valid_rows) -> float:
    mults = _multiplier_signals(
        valid_rows, "_ensemble_confidence_multiplier", 2.0)
    return min(mults) if mults else 1.0
def _ensemble_signals(findings) -> tuple:
    valid_rows = dict_findings(findings)
    ensemble_confirmed = _flag_any(valid_rows, "_ensemble_is_confirmed")
    ensemble_low_conf = bool(valid_rows) and all(
        _signal_bool(f.get(SIGNAL_ENSEMBLE_LOW_CONFIDENCE))
        for f in valid_rows)
    return (ensemble_confirmed, ensemble_low_conf,
            _ensemble_multiplier(valid_rows))
def _adj_ensemble(findings, base_conf, conclusion, adjustments):
    ensemble_confirmed, ensemble_low_conf, ensemble_mult = (
        _ensemble_signals(findings))
    if ensemble_confirmed and conclusion in _UPGRADABLE_CONCLUSIONS:
        _qualified, _reason = upgrade_evidence_qualified(findings)
        if _qualified:
            conclusion = "confirmed"
            adjustments.append("ensemble_cross_group: ->confirmed")
        else:
            conclusion = "likely"
            adjustments.append(f"ensemble_cross_group: ->likely({_reason})")
    if ensemble_low_conf and conclusion == "confirmed" and not ensemble_confirmed:
        conclusion = "likely"
        adjustments.append("ensemble_single_group: confirmed->likely")
    if (is_real_number(ensemble_mult)
            and not math.isclose(ensemble_mult, 1.0)):
        base_conf = _apply_conf_multiplier(
            base_conf, adjustments, "ensemble_mult", ensemble_mult)
    return base_conf, conclusion
def _reachability_state(finding: dict) -> bool | None:
    value = finding.get("_bizflow_reachable")
    if not _is_reachability_observation(value):
        return None
    return _signal_bool(value)
def _any_bizflow_reachable(findings) -> bool:
    return any(_reachability_state(f) is True for f in dict_findings(findings))
def _refdepth_all_unreachable(findings) -> bool:
    _rows = dict_findings(findings)
    if not _rows:
        return False
    for finding in _rows:
        if _signal_bool(finding.get("_bizflow_unresolved", False)):
            return False
        if _reachability_state(finding) is not False:
            return False
    return True
def _refdepth_arbitration(findings) -> tuple:
    any_bizflow_reachable = _any_bizflow_reachable(findings)
    any_refdepth_isolated = _flag_any(findings, SIGNAL_REFDEPTH_ISOLATED)
    any_refdepth_boosted = any(
        boost > 0
        for boost in _numeric_signals(
            findings, SIGNAL_REFDEPTH_PRIORITY_BOOST))
    return (
        any_bizflow_reachable and any_refdepth_isolated
        and not any_refdepth_boosted,
        _refdepth_all_unreachable(findings) and any_refdepth_boosted,
    )
def _adj_refdepth(findings, base_conf, conclusion, adjustments):
    refdepth_boost = _channel_boost(findings, SIGNAL_REFDEPTH_CONFIDENCE_BOOST)
    _neutralize_isolated, _trust_bizflow = _refdepth_arbitration(findings)
    if refdepth_boost is not None:
        if _neutralize_isolated or _trust_bizflow:
            adjustments.append(
                "refdepth_mult=1.00"
                f"(boost={_format_boost(refdepth_boost)}, neutralized)")
        else:
            base_conf = _apply_conf_multiplier(
                base_conf, adjustments, "refdepth_mult",
                _multiplier_from_boost(refdepth_boost),
                f"(boost={_format_boost(refdepth_boost)})")
    if _neutralize_isolated:
        adjustments.append("arbitrate:bizflow_reachable+refdepth_isolated->neutralize")
    elif _trust_bizflow:
        adjustments.append("arbitrate:bizflow_unreachable+refdepth_boosted->trust_bizflow")
    return base_conf, conclusion
def _mutation_signals(findings) -> tuple:
    _rows = dict_findings(findings)
    mutation_confirmed = _flag_any(_rows, SIGNAL_MUTATION_CONFIRMED_DEAD)
    any_mutation_refuted = bool(
        not mutation_confirmed
        and any(_is_mutation_refuted(f) for f in _rows)
        and not _flag_any(_rows, "_mutation_inconclusive")
    )
    return mutation_confirmed, any_mutation_refuted
def _mutation_refuted_bizflow_high_severity_protected(findings) -> bool:
    _rows = dict_findings(findings)
    return (
        any(_is_high_severity_finding(f) for f in _rows)
        and _mutation_signals(_rows)[1]
        and _flag_any(_rows, "_bizflow_fp_candidate")
    )
def _adj_mutation(findings, base_conf, conclusion, adjustments):
    mutation_confirmed, any_mutation_refuted = _mutation_signals(findings)
    if mutation_confirmed:
        if conclusion == "suppressed":
            adjustments.append(
                "mutation_verified: suppressed->confirmed(变异确证推翻误抑制)")
        else:
            adjustments.append("mutation_verified: ->confirmed")
        conclusion = "confirmed"
    if (any_mutation_refuted and not mutation_confirmed
            and conclusion == "confirmed"
            and not _mutation_refuted_bizflow_high_severity_protected(findings)):
        conclusion = "likely"
        adjustments.append("mutation_refuted: confirmed->likely")
    return base_conf, conclusion
def _apply_fp_rate_downgrade(base_conf, conclusion, _rate, _worst_rf,
                             adjustments) -> tuple:
    if _rate >= 0.80:
        fp_mult = 0.15
    elif _rate >= 0.50:
        fp_mult = max(0.15, (1.0 - _rate) * 0.50)
    else:
        fp_mult = max(0.50, 1.0 - _rate)
    base_conf = base_conf * fp_mult
    adjustments.append(
        f"fp_rate_downgrade:mult={fp_mult:.2f}(fp_rate={_rate:.2f},family={_worst_rf})"
    )
    if conclusion == "confirmed" and _rate > FP_RATE_HIGH:
        if _rate >= 0.80:
            conclusion = "uncertain"
            adjustments.append(
                f"fp_rate_confirmed_reject:confirmed->uncertain(fp_rate={_rate:.2f})"
            )
        else:
            conclusion = "likely"
            adjustments.append(
                f"fp_rate_confirmed_downgrade:confirmed->likely(fp_rate={_rate:.2f})"
            )
    return base_conf, conclusion
def _adj_fp_rate(findings, base_conf, conclusion, adjustments):
    try:
        _global_max_fp_rate, _worst_rf = _collect_max_fp_rate(findings)
        _has_high_sev_finding = any(
            _is_high_severity_finding(f) for f in dict_findings(findings))
        if _global_max_fp_rate > 0 and _has_high_sev_finding:
            adjustments.append(
                f"fp_rate_downgrade:exempt_high_severity(fp_rate={_global_max_fp_rate:.2f},family={_worst_rf})"
            )
        elif _global_max_fp_rate > 0:
            base_conf, conclusion = _apply_fp_rate_downgrade(
                base_conf, conclusion, _global_max_fp_rate,
                _worst_rf, adjustments)
    except Exception:
        logger.warning("[Rules] _adj_fp_rate 降权通道异常（跳过）", exc_info=True)
    return base_conf, conclusion
def _record_fp_rate(f, value: float, source: str, _state: list) -> None:
    if value > _state[0]:
        _state[0] = value
        _state[1] = source
    if value > FP_RATE_HIGH:
        f["_high_fp_rate"] = value
def _validated_fp_rate(entry: dict) -> int | float | None:
    rate = _numeric_value(entry.get("fp_rate", 0.0))
    return rate if rate is not None and 0.0 <= rate <= 1.0 else None
def _note_tracker_fp_rate(f, _rf, _state: list) -> None:
    _tracker_entry = RULE_FP_TRACKER.get(_rf) if _rf else None
    if not isinstance(_tracker_entry, dict):
        return
    _fp = _validated_fp_rate(_tracker_entry)
    _total = _tracker_entry.get("total", 0)
    if _fp is None:
        return
    total = _numeric_value(_total)
    if total is not None and total >= _FP_TRACKER_MIN_SAMPLES:
        _record_fp_rate(f, _fp, _rf, _state)
    else:
        f["_fp_rate_cold_start"] = _fp
def _note_subrule_fp_rate(f, _src, _rid, _state: list) -> None:
    _sub = METHOD_SUB_RULES.get(_src) if _src else None
    _sub_entry = _sub.get(_rid) if isinstance(_sub, dict) else None
    if not isinstance(_sub_entry, dict):
        return
    _fp = _validated_fp_rate(_sub_entry)
    if _fp is None:
        return
    _record_fp_rate(f, _fp, f"{_src}/{_rid}", _state)
def _collect_max_fp_rate(findings) -> tuple:
    _state: list = [0.0, ""]
    for f in dict_findings(findings):
        _rf = str(f.get("rule_family") or f.get("rule_id") or "")
        _note_tracker_fp_rate(f, _rf, _state)
        _src = str(f.get("_source_method") or "")
        _rid = str(f.get("rule_id") or "")
        _note_subrule_fp_rate(f, _src, _rid, _state)
    return _state[0], _state[1]
def _test_triage_direction(_smoke_findings) -> tuple:
    any_smoke_pass = _flag_any(_smoke_findings, "_test_triage_smoke_pass")
    any_smoke_fail = _flag_any(_smoke_findings, "_test_triage_smoke_fail")
    _any_strong_fail = _has_strong_smoke_fail(_smoke_findings)
    return (
        any_smoke_pass and not _any_strong_fail,
        any_smoke_fail and (not any_smoke_pass or _any_strong_fail),
        _any_strong_fail,
        any_smoke_pass and any_smoke_fail,
    )
def _triage_smoke_scope(findings):
    _smoke_findings = [
        f for f in dict_findings(findings)
        if (_signal_bool(f.get("_test_triage_smoke_pass"))
            or _signal_bool(f.get("_test_triage_smoke_fail")))
    ]
    if not _smoke_findings:
        return None
    if not all(str(f.get("rule_family", "")) in PRECISE_SMOKE_FAMILIES for f in _smoke_findings):
        return None
    return _smoke_findings
def _adj_test_triage(findings, base_conf, conclusion, adjustments):
    _smoke_findings = _triage_smoke_scope(findings)
    if _smoke_findings is None:
        return base_conf, conclusion
    _neg_direction, _pos_direction, _any_strong_fail, _mixed = (
        _test_triage_direction(_smoke_findings))
    if _mixed:
        adjustments.append(
            "test_triage_mixed: "
            + ("strong_fail_over_pass" if _any_strong_fail else "pass_over_symbol_fail")
        )
    if _neg_direction and conclusion == "confirmed":
        conclusion = "likely"
        adjustments.append("test_triage_pass: confirmed->likely")
    elif _pos_direction and conclusion in _UPGRADABLE_CONCLUSIONS:
        if _any_strong_fail:
            conclusion = "confirmed"
            adjustments.append("test_triage_fail: ->confirmed")
        else:
            conclusion = "likely"
            adjustments.append("test_triage_symbol_fail: ->likely(symbol-level cap)")
    return base_conf, conclusion
def _proportional_restore(base_conf, conclusion, adjustments,
                         degradation, pre_arbiter_conf,
                         _arbiter_downgraded) -> tuple:
    _restored = pre_arbiter_conf * 0.70
    if _restored <= base_conf:
        return base_conf, conclusion
    _old = base_conf
    base_conf = _restored
    adjustments.append(
        f"degradation_protection_proportional:restored {_old:.2f}->{base_conf:.2f}"
        f"(degradation={degradation:.2f}, pre_arbiter={pre_arbiter_conf:.2f})"
    )
    if (conclusion != "confirmed" and base_conf >= CONF_HIGH
            and _arbiter_downgraded):
        conclusion = "likely"
        adjustments.append(
            "degradation_protection:conclusion_restored_capped_likely"
        )
    return base_conf, conclusion
def _restore_absolute(current_conf, conclusion, adjustments, degradation,
                      pre_arbiter_conf, _arbiter_downgraded_conclusion) -> tuple:
    base_conf = pre_arbiter_conf
    if _arbiter_downgraded_conclusion:
        conclusion = "likely"
        adjustments.append(
            f"degradation_protection:restored_conf {current_conf:.2f}->{base_conf:.2f}"
            f"(conclusion_capped_likely, degradation={degradation:.2f})"
        )
    else:
        adjustments.append(
            f"degradation_protection:conf_only_restored {current_conf:.2f}->{base_conf:.2f}"
            f"(conclusion_not_arbiter_downgraded, degradation={degradation:.2f})"
        )
    return base_conf, conclusion
def _adj_degradation_protection(base_conf, conclusion, adjustments,
                               pre_arbiter_conf,
                               pre_arbiter_conclusion):
    degradation = pre_arbiter_conf - base_conf
    _arbiter_downgraded_conclusion = (
        pre_arbiter_conclusion == "confirmed" and conclusion != "confirmed"
    )
    if degradation > CONF_FLOOR and base_conf < CONF_LOW and pre_arbiter_conf > CONF_MEDIUM:
        return _restore_absolute(
            base_conf, conclusion, adjustments, degradation, pre_arbiter_conf,
            _arbiter_downgraded_conclusion)
    if pre_arbiter_conf > CONF_MEDIUM and degradation > pre_arbiter_conf * 0.40:
        return _proportional_restore(
            base_conf, conclusion, adjustments, degradation,
            pre_arbiter_conf, _arbiter_downgraded_conclusion)
    return base_conf, conclusion
def _mark_all_demoted(findings):
    for f in dict_findings(findings):
        f["_arbiter_demoted"] = True
def _note_processed_signals(findings, adjustments) -> None:
    current_signals = set()
    for _signal in ("baseline_mult", "bizflow_mult",
                    "ensemble_mult", "refdepth_mult"):
        if any(str(_a).startswith(f"{_signal}=") for _a in adjustments):
            current_signals.add(_signal)
    for finding in dict_findings(findings):
        processed = collect_processed_signals([finding]) | current_signals
        finding["_xv_processed_signals"] = sorted(processed)
def _apply_arbitration_result(conclusion, base_conf, findings,
                              _arb_result, adjustments) -> tuple:
    if _arb_result.conclusion != conclusion:
        old_conclusion = conclusion
        conclusion = _arb_result.conclusion
        if _arb_result.downgraded:
            _mark_all_demoted(findings)
            adjustments.append(
                f"arbiter_demoted:{old_conclusion}->{conclusion}"
            )
        elif _arb_result.upgraded:
            adjustments.append(
                f"arbiter_upgraded:{old_conclusion}->{conclusion}"
            )
        else:
            adjustments.append(
                f"arbiter_reclassified:{old_conclusion}->{conclusion}"
            )
    if _arb_result.confidence != base_conf:
        old_conf = base_conf
        base_conf = max(0.0, min(1.0, _arb_result.confidence))
        adjustments.append(
            f"arbiter_conf:{old_conf:.3f}->{base_conf:.3f}"
        )
    if _arb_result.arbitrations_applied:
        for rule in _arb_result.arbitrations_applied:
            adjustments.append(f"arbiter:{rule}")
    return conclusion, base_conf
def _adj_arbiter(findings, base_conf, conclusion, adjustments):
    _note_processed_signals(findings, adjustments)
    if not findings:
        return base_conf, conclusion
    try:
        _arb_result = _ARBITER.arbitrate(conclusion, base_conf, findings)
        conclusion, base_conf = _apply_arbitration_result(
            conclusion, base_conf, findings, _arb_result, adjustments)
    except Exception as _e:  # noqa: BLE001
        logger.warning("[Arbiter] _adj_arbiter 仲裁失败，跳过: %s", _e)
    return base_conf, conclusion
_NARROWED_CHAIN = (
    _adj_mutation, _adj_test_triage, _adj_falsify,
)
_ADJ_CHAIN = (
    _adj_baseline, _adj_bizflow, _adj_ensemble, _adj_refdepth,
    _adj_mutation, _adj_fp_rate, _adj_test_triage, _adj_falsify,
)
def post_match_suppression(_cv2, xv_findings: list) -> int:
    xv_findings = xv_findings if isinstance(xv_findings, (list, tuple)) else []
    _cap_arbiter_demoted_confirmed(xv_findings)
    suppressed_count, _ = _govern_single_source_likely(xv_findings)
    return suppressed_count
def _cap_arbiter_demoted_confirmed(xv_findings: list) -> int:
    arbiter_demoted_capped = 0
    for f in dict_findings(xv_findings):
        if not f.get("_arbiter_demoted"):
            continue
        if f.get("conclusion") != "confirmed":
            continue
        f["conclusion"] = "likely"
        f["_arbiter_demoted_capped"] = True
        arbiter_demoted_capped += 1
    if arbiter_demoted_capped > 0:
        logger.info(
            "[CV-PostMatch] 仲裁降级守卫: %d 条 arbiter 降级后仍 confirmed 的 finding 降级为 likely",
            arbiter_demoted_capped,
        )
    return arbiter_demoted_capped
def _govern_single_source_likely(xv_findings: list) -> tuple[int, int]:
    suppressed_count = 0
    review_flagged = 0
    for f in dict_findings(xv_findings):
        if not _govern_candidate(f):
            continue
        action = _govern_apply_one(f)
        if action == "suppressed":
            suppressed_count += 1
        elif action == "review":
            review_flagged += 1
    if suppressed_count > 0:
        logger.info("[CV-PostMatch] 后置抑制: %d 条单源P2/P3 likely降级为uncertain", suppressed_count)
    if review_flagged > 0:
        logger.info("[CV-PostMatch] 复核标记: %d 条普通单源P2/P3 likely标记待复核", review_flagged)
    return suppressed_count, review_flagged
_GOVERN_SEVERITIES: frozenset[str] = frozenset(
    _sev for _sev, _rank in SEVERITY_RANK.items() if _rank in (2, 3))
def _govern_candidate(f: dict) -> bool:
    if f.get("conclusion") != "likely":
        return False
    sev = str(f.get("severity", "") or "").strip().upper()
    if sev not in _GOVERN_SEVERITIES:
        return False
    sources = f.get("sources")
    if isinstance(sources, SOURCE_SEQUENCE_TYPES):
        indep_count = len(independent_sources(list(sources)))
    else:
        source_count = _numeric_value(f.get("_source_count", 0))
        indep_count = source_count if source_count is not None else 0
    return indep_count < 2
def _govern_apply_one(f: dict) -> str | None:
    rule_family = str(f.get("rule_family", "") or "")
    rule_id = str(f.get("rule_id", "") or "")
    is_tm = "TM-" in rule_family or "TM-" in rule_id
    is_batch = _signal_bool(f.get("_batch_source_rule", False))
    if not (is_tm or is_batch):
        f["_review_required"] = True
        f["_review_reason"] = "单源P2/P3 likely，缺乏多源交叉验证，建议人工复核"
        return "review"
    if _signal_bool(f.get("_rule_matched", False)):
        return None
    f["conclusion"] = "uncertain"
    f["_suppressed_by"] = "post_match_suppression"
    return "suppressed"
def _finding_family_strict(f: dict) -> str:
    v = f.get("rule_family", "") if isinstance(f, dict) else ""
    return v if isinstance(v, str) else ""
def _parse_locator_file_line(loc: str) -> tuple[str, int]:
    if not isinstance(loc, str):
        return ("", 0)
    return parse_locator_file(loc), parse_locator_line(loc)
def _any_family_in(findings, families) -> bool:
    return any(_finding_family_strict(f) in families for f in findings)
def _min_severity_rank(findings) -> int:
    return min(
        (normalize_severity_rank(str(f.get("severity", "P3")))
         for f in dict_findings(findings)),
        default=3,
    )
_DEAD_FAMILIES = CONFLICT_DEAD_CODE_FAMILIES
_COMPLEX_FAMILIES = CONFLICT_COMPLEXITY_FAMILIES
_SIGNAL_ADJUSTMENTS: tuple[tuple[Any, float], ...] = (
    (lambda fs: _flag_any(fs, SIGNAL_BASELINE_PERSISTENT_NOISE), 0.90),
    (lambda fs: (_any_bizflow_reachable(fs)
                 and _any_family_in(fs, _DEAD_FAMILIES)), 0.90),
    (lambda fs: (_flag_any(fs, SIGNAL_REFDEPTH_ISOLATED)
                 and _any_family_in(fs, _COMPLEX_FAMILIES)), 1.15),
    (lambda fs: _flag_any(fs, SIGNAL_MUTATION_CONFIRMED_DEAD), 1.10),
    (lambda fs: _flag_any(fs, "_ensemble_is_confirmed"), 1.08),
)
@dataclass(frozen=True)
class _ContradictionRecordInput:
    loc_label: str
    decision: str
    left_max: str
    right_max: str
    left: frozenset[str]
    right: frozenset[str]
    findings_list: list
    families: set
    pair_type: str
    adj_conf: Any
    ev_str: Any
    sample_file: str
    sample_line: int
    is_func_level: bool
@dataclass(frozen=True)
class _ContradictionScanContext:
    filepath: str
    sorted_findings: list
    existing_locs: set
@dataclass(frozen=True, slots=True)
class _FuncPair:
    ctx: _ContradictionScanContext
    f_a: dict
    f_b: dict
    i: int
    j: int
class _ContradictionDetector:
    __slots__ = ("cv2", "existing_locs")
    def __init__(self, cv2, existing_locs=None):
        self.cv2 = cv2
        self.existing_locs = set() if existing_locs is None else existing_locs
    @staticmethod
    def source_id(f: dict) -> str:
        return _source_method_of(f) or "unknown"
    @staticmethod
    def finding_file(f: dict) -> str:
        v = f.get("file", "")
        return v if isinstance(v, str) else ""
    @staticmethod
    def finding_locator(f: dict) -> str:
        filepath = _ContradictionDetector.finding_file(f)
        if not filepath:
            return ""
        line = safe_finding_line(f)
        return f"{filepath}:{line if line > 0 else 'FILE_LEVEL'}"
    @classmethod
    def real_source_ids(cls, findings) -> list:
        return sorted({
            sid for sid in (cls.source_id(f) for f in dict_findings(findings))
            if sid != "unknown"
        })
    @classmethod
    def real_source_count(cls, findings) -> int:
        return len(cls.real_source_ids(findings))
    @staticmethod
    def sev_boost_of(findings) -> float:
        sev_boost = 0.0
        for f in findings:
            if not isinstance(f, dict):
                continue
            sev_rank = normalize_severity_rank(f.get("severity"))
            if sev_rank <= 1:
                sev_boost = max(sev_boost, CONF_BOOST_MODERATE)
            elif sev_rank == 2:
                sev_boost = max(sev_boost, 0.08)
        return sev_boost
    @classmethod
    def degrade_factors_of(cls, findings) -> dict:
        _deg_factors = {}
        for f in findings:
            if isinstance(f, dict) and _signal_bool(f.get("_partial_degrade")):
                _sm = cls.source_id(f)
                if _sm != "unknown":
                    _df = degrade_factor_of(f)
                    _deg_factors[_sm] = min(_deg_factors.get(_sm, 1.0), _df)
        return _deg_factors
    @classmethod
    def compute_evidence_strength(cls, findings):
        sev_boost = cls.sev_boost_of(findings)
        _source_ids = cls.real_source_ids(findings)
        source_count = len(_source_ids)
        if _source_ids:
            _deg_factors = cls.degrade_factors_of(findings)
            _method_rf_map = dominant_rule_family_by_method(findings)
            try:
                _weighted = evidence_strength_by_rule_family(
                    _method_rf_map, _source_ids,
                    _deg_factors if _deg_factors else None)
                return round(min(CONF_CAP, _weighted + sev_boost), 3)
            except Exception as _e:  # noqa: BLE001 — 证据强度计算异常回退硬编码阶梯
                logger.warning("[M5] evidence_strength_by_rule_family failed, "
                               "using fallback: %s", _e)
        if source_count >= 3:
            strength = CONF_HIGH
        elif source_count == 2:
            strength = 0.50
        else:
            strength = CONF_FLOOR
        return round(min(CONF_CAP, strength + sev_boost), 3)
    @staticmethod
    def _max_confidence(findings) -> float | None:
        _vals = [value for value in (
            _numeric_value(f.get("confidence"))
            for f in dict_findings(findings))
            if value is not None]
        return max(_vals) if _vals else None
    @classmethod
    def compute_severity_decision(cls, left_findings, right_findings):
        left_max = severity_literal_from_rank(_min_severity_rank(left_findings))
        right_max = severity_literal_from_rank(_min_severity_rank(right_findings))
        decision = get_contradiction_decision(
            left_max, right_max,
            cls._max_confidence(left_findings),
            cls._max_confidence(right_findings),
            cls.real_source_count(left_findings),
            cls.real_source_count(right_findings))
        return decision, left_max, right_max
    @staticmethod
    def contradiction_signal_factor(findings, base: float) -> float:
        _conf = base
        for applies, factor in _SIGNAL_ADJUSTMENTS:
            if applies(findings):
                _conf *= factor
        return _conf
    @classmethod
    def compute_contradiction_confidence(cls, findings: list,
                                         base: float) -> float:
        findings = dict_findings(findings)
        _conf = cls.contradiction_signal_factor(findings, base)
        return round(min(1.0, max(0.1, _conf)), 3)
    @staticmethod
    def contradiction_family_universe() -> frozenset[str]:
        universe: set[str] = set()
        for left_fs, right_fs, _ctype in CONFLICTING_PAIRS:
            universe |= left_fs
            universe |= right_fs
        return frozenset(universe)
    @staticmethod
    def neighbor_window(i: int, j: int, size: int) -> list[int]:
        window = (set(range(max(0, i - 5), min(i + 6, size)))
                  | set(range(max(0, j - 5), min(j + 6, size))))
        window.discard(i)
        window.discard(j)
        return sorted(window)
    @classmethod
    def collect_adjacent_findings(cls, file_findings_sorted, i, j,
                                  left_families, right_families):
        _func_findings = [file_findings_sorted[i], file_findings_sorted[j]]
        _relevant_families = left_families | right_families
        if _relevant_families:
            for _k in cls.neighbor_window(i, j, len(file_findings_sorted)):
                _fc = file_findings_sorted[_k]
                if _finding_family_strict(_fc) in _relevant_families:
                    _func_findings.append(_fc)
        return _func_findings
    @staticmethod
    def match_pair_of(fam_a: str, fam_b: str):
        for left_fs, right_fs, ctype in CONFLICTING_PAIRS:
            if (fam_a in left_fs and fam_b in right_fs) or (
                    fam_b in left_fs and fam_a in right_fs):
                return left_fs, right_fs, ctype
        return None
    @staticmethod
    def read_proximity_env(key: str, default: int) -> int:
        raw = os.environ.get(key, "")
        try:
            val = int(raw)
        except (TypeError, ValueError):
            if raw:
                logger.warning("[XV] 环境变量 %s=%r 非法，回退默认 %d",
                               key, raw, default)
            return default
        return val if val > 0 else default
    @classmethod
    def proximity_windows(cls) -> tuple:
        _BASE = cls.read_proximity_env("JWSGJ_CONTRADICTION_PROXIMITY", 15)
        _EXTENDED = cls.read_proximity_env(
            "JWSGJ_CONTRADICTION_PROXIMITY_EXTENDED", 30)
        if _EXTENDED < _BASE:
            logger.warning(
                "[XV] 邻近窗口误配 PROXIMITY(%d)>PROXIMITY_EXTENDED(%d)，"
                "EXTENDED 归一提升至 %d 恢复双级窗口序",
                _BASE, _EXTENDED, _BASE)
            _EXTENDED = _BASE
        return _BASE, _EXTENDED
    @staticmethod
    def group_findings(all_findings, key_of) -> dict:
        grouped: dict[str, list[dict]] = {}
        for finding in dict_findings(all_findings):
            key = key_of(finding)
            if key:
                grouped.setdefault(key, []).append(finding)
        return grouped
    @staticmethod
    def sorted_family_candidates(file_findings, all_families) -> list:
        return sorted(
            (f for f in file_findings
             if _finding_family_strict(f) in all_families
             and safe_finding_line(f) > 0),
            key=safe_finding_line)
    @staticmethod
    def confidence_gate_ok(f_a, f_b) -> bool:
        conf_a = _numeric_value(f_a.get("confidence"))
        conf_b = _numeric_value(f_b.get("confidence"))
        return (conf_a is not None and conf_a >= CONF_MEDIUM
                and conf_b is not None and conf_b >= CONF_MEDIUM)
    @staticmethod
    def same_function_scope(f_a, f_b) -> bool:
        func_a = f_a.get("_refdepth_function_name", "")
        func_b = f_b.get("_refdepth_function_name", "")
        return not (func_a and func_b and func_a != func_b)
    @classmethod
    def proximity_pair_ok(cls, f_a, fam_a, f_b, line_dist, base) -> bool:
        if line_dist > base and not cls.confidence_gate_ok(f_a, f_b):
            return False
        fam_b = _finding_family_strict(f_b)
        if not fam_b or fam_a == fam_b:
            return False
        return cls.same_function_scope(f_a, f_b)
    @staticmethod
    def record_prefix(is_func_level: bool) -> tuple[str, str]:
        if is_func_level:
            return "func_conflict", "函数级矛盾(邻近行): "
        return "conflict", "矛盾检测: "
    @staticmethod
    def family_text(families: frozenset[str]) -> str:
        return ",".join(sorted(families))
    @classmethod
    def build_contradiction_record(cls,
                                   spec: _ContradictionRecordInput) -> dict:
        _sources = set(cls.real_source_ids(spec.findings_list))
        _type_prefix, _msg_prefix = cls.record_prefix(spec.is_func_level)
        _left_text = cls.family_text(spec.left & spec.families) or cls.family_text(spec.left)
        _right_text = cls.family_text(spec.right & spec.families) or cls.family_text(spec.right)
        _adj_conf = (round(spec.adj_conf, 3)
                     if is_real_number(spec.adj_conf) else spec.adj_conf)
        _sev_breakdown = severity_breakdown_of(spec.findings_list)
        record = {
            "locator": f"CONTRADICTION:{spec.loc_label}",
            "rule_applied": "规则16",
            "conclusion": spec.decision,
            "sources": sorted(_sources),
            "source_count": len(_sources),
            FIELD_EVIDENCE_FAMILIES: sorted(spec.families),
            FIELD_EVIDENCE_STRENGTH: spec.ev_str,
            FIELD_BASE_CONFIDENCE: spec.ev_str,
            FIELD_ADJUSTED_CONFIDENCE: _adj_conf,
            "findings": spec.findings_list,
            "findings_count": len(spec.findings_list),
            "contradiction_type": (f"{_type_prefix}:{spec.pair_type}:"
                                   f"{_left_text} vs {_right_text}"),
            "contradiction_decision": spec.decision,
            "timestamp": timestamp_ms(),
            "sample_finding": {
                "total_findings": len(spec.findings_list),
                "severity_breakdown": _sev_breakdown,
                "message": f"{_msg_prefix}{_left_text} vs {_right_text} "
                           f"({spec.left_max} vs {spec.right_max} -> "
                           f"{spec.decision})",
                "file": spec.sample_file,
                "line": spec.sample_line,
            },
        }
        if not spec.is_func_level:
            record["max_sev_left"] = spec.left_max
            record["max_sev_right"] = spec.right_max
        return record
    @staticmethod
    def family_members(findings, left, right) -> tuple:
        return ([f for f in findings if _finding_family_strict(f) in left],
                [f for f in findings if _finding_family_strict(f) in right])
    @staticmethod
    def locator_families(findings) -> set:
        families = set()
        for f in findings:
            fam = _finding_family_strict(f)
            if fam:
                families.add(fam)
        return families
    @staticmethod
    def arbitrate_decision(decision, conf, findings, loc_label) -> tuple:
        try:
            _arb_result = _ARBITER.arbitrate(decision, conf, findings)
            if _arb_result.arbitrations_applied:
                return _arb_result.conclusion, _arb_result.confidence
        except Exception:
            logger.warning("[XV] 矛盾检测仲裁异常 %s, "
                           "保留已检测矛盾", loc_label, exc_info=True)
        return decision, conf
    @classmethod
    def locator_contradiction_record(cls, loc, findings):
        families = cls.locator_families(findings)
        matched = find_conflicting_pair(families)
        if matched is None:
            return None
        left, right, pair_type = matched
        left_findings, right_findings = cls.family_members(
            findings, left, right)
        decision, left_max, right_max = cls.compute_severity_decision(
            left_findings, right_findings)
        _ev_str = cls.compute_evidence_strength(findings)
        _exact_conf = cls.compute_contradiction_confidence(
            findings, base=_ev_str)
        _loc_f, _loc_l = _parse_locator_file_line(loc)
        decision, _exact_conf = cls.arbitrate_decision(
            decision, _exact_conf, findings, f"loc={loc}")
        return cls.build_contradiction_record(_ContradictionRecordInput(
            loc_label=loc,
            decision=decision,
            left_max=left_max,
            right_max=right_max,
            left=left,
            right=right,
            findings_list=findings,
            families=families,
            pair_type=pair_type,
            adj_conf=_exact_conf,
            ev_str=_ev_str,
            sample_file=os.path.basename(_loc_f),
            sample_line=_loc_l,
            is_func_level=False,
        ))
    @staticmethod
    def window_candidates(ctx: _ContradictionScanContext, i: int, line_a: int,
                          extended: int):
        for j in range(i + 1, len(ctx.sorted_findings)):
            f_b = ctx.sorted_findings[j]
            _line_dist = abs(safe_finding_line(f_b) - line_a)
            if _line_dist > extended:
                break
            yield j, f_b, _line_dist
    @classmethod
    def match_and_build_func_contradiction(cls,
                                           ctx: _ContradictionScanContext,
                                           f_a, f_b, i, j):
        fam_a = _finding_family_strict(f_a)
        fam_b = _finding_family_strict(f_b)
        matched = cls.match_pair_of(fam_a, fam_b)
        if matched is None:
            return None
        left, right, pair_type = matched
        func_loc = (f"{ctx.filepath}:"
                    f"{min(safe_finding_line(f_a), safe_finding_line(f_b))}")
        if func_loc in ctx.existing_locs:
            return None
        record = cls.build_func_record(
            _FuncPair(ctx=ctx, f_a=f_a, f_b=f_b, i=i, j=j),
            func_loc, left, right, frozenset((fam_a, fam_b)), pair_type)
        ctx.existing_locs.add(func_loc)
        return record
    @classmethod
    def build_func_record(cls, pair: _FuncPair, func_loc: str,
                          left: frozenset[str], right: frozenset[str],
                          pair_families: frozenset[str],
                          pair_type: str) -> dict:
        left_findings, right_findings = cls.family_members(
            [pair.f_a, pair.f_b], left, right)
        decision, left_max, right_max = cls.compute_severity_decision(
            left_findings, right_findings)
        func_findings = cls.collect_adjacent_findings(
            pair.ctx.sorted_findings, pair.i, pair.j, left, right)
        ev_str = cls.compute_evidence_strength([pair.f_a, pair.f_b])
        conf = cls.compute_contradiction_confidence(func_findings, base=ev_str)
        decision, conf = cls.arbitrate_decision(
            decision, conf, func_findings, f"func_loc={func_loc}")
        return cls.build_contradiction_record(_ContradictionRecordInput(
            loc_label=func_loc,
            decision=decision,
            left_max=left_max,
            right_max=right_max,
            left=left,
            right=right,
            findings_list=func_findings,
            families=pair_families | cls.locator_families(func_findings),
            pair_type=pair_type,
            adj_conf=conf,
            ev_str=ev_str,
            sample_file=os.path.basename(pair.ctx.filepath),
            sample_line=int(min(safe_finding_line(pair.f_a),
                                safe_finding_line(pair.f_b)) or 0),
            is_func_level=True,
        ))
    @classmethod
    def scan_pair_records(cls, ctx: _ContradictionScanContext, i, f_a,
                          base, extended) -> list:
        records = []
        line_a = safe_finding_line(f_a)
        fam_a = _finding_family_strict(f_a)
        for j, f_b, _line_dist in cls.window_candidates(
                ctx, i, line_a, extended):
            if not cls.proximity_pair_ok(f_a, fam_a, f_b, _line_dist, base):
                continue
            record = cls.match_and_build_func_contradiction(
                ctx, f_a, f_b, i, j)
            if record is not None:
                records.append(record)
        return records
    def detect_func_level(self) -> list:
        contradictions = []
        _BASE_PROXIMITY, _EXTENDED_PROXIMITY = self.proximity_windows()
        by_file = self.group_findings(
            self.cv2.all_findings, self.finding_file)
        _all_contradiction_families = self.contradiction_family_universe()
        for filepath, file_findings in by_file.items():
            if len(file_findings) < 2:
                continue
            file_findings_sorted = self.sorted_family_candidates(
                file_findings, _all_contradiction_families)
            if len(file_findings_sorted) < 2:
                continue
            scan_ctx = _ContradictionScanContext(
                filepath, file_findings_sorted, self.existing_locs)
            for i, f_a in enumerate(file_findings_sorted):
                contradictions.extend(self.scan_pair_records(
                    scan_ctx, i, f_a,
                    _BASE_PROXIMITY, _EXTENDED_PROXIMITY))
        return contradictions
    def check(self) -> list[dict]:
        contradictions = []
        by_location = self.group_findings(
            self.cv2.all_findings, self.finding_locator)
        for loc, findings in by_location.items():
            if len(findings) < 2:
                continue
            record = self.locator_contradiction_record(loc, findings)
            if record is not None:
                contradictions.append(record)
                self.existing_locs.add(loc)
        contradictions.extend(self.detect_func_level())
        if contradictions:
            logger.info("[Contradiction] 检测到 %d 个矛盾",
                        len(contradictions))
        return contradictions
def max_severity_of_findings(c: dict) -> str:
    return severity_literal_from_rank(_min_severity_rank(findings_container(c)))
_INHERIT_AGGREGATOR_OVERRIDES: dict[str, str] = {
    SIGNAL_ENSEMBLE_LOW_CONFIDENCE: "all",
}
def _inherit_signal_aggregator(field_name: str, reg: dict[str, Any]) -> str:
    override = _INHERIT_AGGREGATOR_OVERRIDES.get(field_name)
    if override is not None:
        return override
    agg = reg["agg"]
    if agg == "any_positive" or (
            agg == "any" and reg["type"] in ("int", "float")):
        return "max"
    return agg
def _aggregate_inner_signal(inner: list, signal_key: str, agg: str):
    if agg == "any":
        return any(_signal_bool(f.get(signal_key)) for f in inner)
    if agg == "all":
        return all(_signal_bool(f.get(signal_key)) for f in inner)
    values = _numeric_signals(inner, signal_key)
    if not values:
        return None
    return min(values) if agg == "min" else max(values)
def _observed_signal_rows(inner: list, signal_key: str) -> list:
    return [f for f in inner if f.get(signal_key) is not None]
def _inherit_inner_signals(c: dict, inner: list) -> None:
    inner = dict_findings(inner)
    for signal_key, reg in SIGNAL_REGISTRY.items():
        agg = _inherit_signal_aggregator(signal_key, reg)
        _rows = (inner if agg == "all"
                 else _observed_signal_rows(inner, signal_key))
        if not _rows:
            continue
        value = _aggregate_inner_signal(_rows, signal_key, agg)
        if value is None:
            continue
        c[signal_key] = value
def _fallback_rule16_decision(c: dict) -> str:
    rank = normalize_severity_rank(max_severity_of_findings(c))
    if rank <= 1:
        return "confirmed"
    if rank == 2:
        return "investigated"
    return "reviewed"
_R16_DECISION_ROUTES: dict[str, tuple[str, bool]] = {
    "confirmed": ("confirmed", False),
    "suppressed": ("suppressed", False),
    "likely": ("likely", False),
    "investigated": ("investigated", True),
    "reviewed": ("review", True),
    "review": ("review", True),
    "uncertain": ("uncertain", False),
}
_R16_STATS_KEYS: tuple[str, ...] = (
    "triggered", "confirmed", "suppressed", "investigated",
    "review", "likely", "uncertain", "findings_count",
)
def _update_rule16_stats(r16: dict, contradictions: list) -> None:
    for _k in _R16_STATS_KEYS:
        r16[_k] = _as_counter(r16.get(_k))
    r16["triggered"] = True
    findings_total = 0
    for c in contradictions:
        count = len(findings_container(c)) or 1
        decision = c.get("contradiction_decision") or _fallback_rule16_decision(c)
        _count_decision(r16, decision, count)
        findings_total += count
    r16["findings_count"] += findings_total
def _count_decision(r16: dict, decision, count: int = 1) -> None:
    route = (_R16_DECISION_ROUTES.get(decision.strip().lower())
             if isinstance(decision, str) else None)
    if route is None:
        r16["investigated"] += count
        r16["uncertain"] += count
        return
    key, also_uncertain = route
    r16[key] += count
    if also_uncertain:
        r16["uncertain"] += count
def handle_contradictions(cv, xv_findings: list) -> tuple:
    contradictions = _ContradictionDetector(cv).check()
    if not contradictions:
        return contradictions, 0
    for c in contradictions:
        inner = findings_container(c)
        if inner:
            _inherit_inner_signals(c, inner)
    if isinstance(xv_findings, list):
        xv_findings.extend(contradictions)
    rules_applied = getattr(cv, "rules_applied", None)
    if not isinstance(rules_applied, dict):
        rules_applied = {}
        try:
            cv.rules_applied = rules_applied
        except AttributeError:  # pragma: no cover - 只读 cv 对象
            logger.warning("[Contradiction] cv 缺少可写 rules_applied，规则16 统计仅本次生效")
    r16 = rules_applied.get("规则16")
    if not isinstance(r16, dict):
        r16 = dict.fromkeys(_R16_STATS_KEYS, 0)
        rules_applied["规则16"] = r16
    _update_rule16_stats(r16, contradictions)
    return contradictions, len(contradictions)
CONTRADICTION_SEVERITY_DECISION: dict[tuple[int, int], str] = {
    (0, 0): "confirmed",
    (0, 1): "confirmed",
    (0, 2): "confirmed",
    (0, 3): "confirmed",
    (0, 4): "confirmed",
    (1, 1): "confirmed",
    (1, 2): "investigated",
    (1, 3): "investigated",
    (1, 4): "investigated",
    (2, 2): "investigated",
    (2, 3): "investigated",
    (2, 4): "reviewed",
    (3, 3): "reviewed",
    (3, 4): "reviewed",
    (4, 4): "reviewed",
}
_CONTRADICTION_MULTI_SOURCE_MIN = 2
def get_contradiction_decision(
    left_max_sev: str,
    right_max_sev: str,
    left_confidence: float | None = None,
    right_confidence: float | None = None,
    left_source_count: int | None = None,
    right_source_count: int | None = None,
) -> str:
    try:
        left_rank = normalize_severity_rank(left_max_sev)
        right_rank = normalize_severity_rank(right_max_sev)
        if left_rank > right_rank:
            left_rank, right_rank = right_rank, left_rank
        base = CONTRADICTION_SEVERITY_DECISION.get(
            (left_rank, right_rank), "reviewed"
        )
        if base == "confirmed":
            base = _calibrate_confirmed_contradiction(
                left_confidence, right_confidence,
                left_source_count, right_source_count,
            )
        return base
    except Exception as e:
        logger.warning("get_contradiction_decision: %s", e, exc_info=True)
        return "reviewed"
def _calibrate_confirmed_contradiction(
    left_confidence: float | None,
    right_confidence: float | None,
    left_source_count: int | None,
    right_source_count: int | None,
) -> str:
    _left = _numeric_value(left_confidence)
    _right = _numeric_value(right_confidence)
    if _left is None or _right is None:
        return "confirmed"
    hi, lo = max(_left, _right), min(_left, _right)
    if hi < CONF_VERY_HIGH or lo >= SINGLE_SOURCE_CONFIRM_THRESHOLD:
        return "confirmed"
    if _left == _right:
        _low_sources = min(
            _as_counter(left_source_count), _as_counter(right_source_count))
    else:
        _low_sources = _as_counter(
            left_source_count if lo == _left else right_source_count)
    if _low_sources >= _CONTRADICTION_MULTI_SOURCE_MIN:
        return "confirmed"
    logger.info(
        "get_contradiction_decision: 高置信源(%s)被低置信单源(%s)"
        "对冲，降级为investigated",
        hi, lo,
    )
    return "investigated"
def find_conflicting_pair(families: set[str]):
    families = (set(families)
                if isinstance(families, (list, tuple, set, frozenset))
                else set())
    for left, right, ctype in CONFLICTING_PAIRS:
        left_hits = families & left
        right_hits = families & right
        if any(left_family != right_family
               for left_family in left_hits
               for right_family in right_hits):
            return left, right, ctype
    return None
def detect_contradiction(families: set[str]) -> tuple[bool, str]:
    try:
        pair = find_conflicting_pair(families)
        return (True, pair[2]) if pair is not None else (False, "")
    except Exception as e:  # noqa: BLE001 -- 保守按有冲突处理，交由完整比对兜底
        logger.warning("detect_contradiction 预检异常，保守继续逐对比对: %s", e)
        return (True, "")

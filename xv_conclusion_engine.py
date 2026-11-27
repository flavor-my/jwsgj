from __future__ import annotations

import json
import logging
import os
from collections.abc import Callable, Iterable
from contextlib import nullcontext
from dataclasses import dataclass, field
from functools import partial
from typing import Any, NamedTuple

from jwsgj.diag_types_defs import (
    dict_findings,
)
from jwsgj.diag_types_normalize import (
    clamp_unit,
    clean_source_ids,
    degrade_factor_of,
    env_number,
    extract_symbol,
    is_default_confidence,
    is_real_number,
    is_status_message_finding,
    is_valid_fp_rate,
    normalize_severity_rank,
    normalize_sources,
    safe_confidence,
    safe_dict_get,
    safe_float,
    signal_bool,
    source_id_text,
    strict_iterable_list,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    AUTO_THRESHOLD_DECAY,
    CAT_MAINTAINABILITY,
    CONF_BOOST_MODERATE,
    CONF_BOOST_STEP,
    CONF_DEFAULT_PENALTY,
    CONF_FLOOR,
    CONF_HIGH,
    CONF_LOW,
    CONF_VERY_HIGH,
    FIELD_ADJUSTED_CONFIDENCE,
    FIELD_BASE_CONFIDENCE,
    FIELD_EVIDENCE_FAMILIES,
    FIELD_EVIDENCE_STRENGTH,
    FP_RATE_LOW,
    FP_RATE_MEDIUM,
    FP_RATE_VERY_LOW,
    MESSAGE_TRUNCATE_LEN,
    RULE_COMMAND_INJECTION,
    RULE_HIGH_COMPLEXITY,
    RULE_INSECURE_CONFIG,
    RULE_MUTABLE_DEFAULT,
    RULE_TOO_MANY_PARAMS,
    SEVERITY_RANK,
    SIGNAL_MUTATION_CONFIRMED_DEAD,
    SIGNAL_PARTIAL_SOURCES,
    SOURCE_SEQUENCE_TYPES,
)
from jwsgj.fix_guide_rule_identity import (
    CONFLICT_COMPLEXITY_FAMILIES,
    CONFLICT_DEAD_CODE_FAMILIES,
    CONFLICT_TEST_FAILURE_FAMILIES,
    KNOWN_HIGH_FP_FAMILIES,
    get_rule_family_set,
    get_rule_semantic,
    is_family_member,
)
from jwsgj.log_config import log_swallowed
from jwsgj.xv_evidence_strength import (
    REGRESSION_FAMILIES,
    available_methods,
    count_independent_sources,
    dominant_rule_family_by_method,
    evidence_meta,
    evidence_strength_by_rule_family,
    evidence_strength_weighted,
    family_reliability_base,
    independent_sources,
    partial_deg_factors_map,
    source_family_names,
    source_main_id,
)
from jwsgj.xv_findings_core import (
    normalize_finding_input,
    normalized_confidence,
    propagate_finding_metadata,
    summarize_findings,
)
from jwsgj.xv_rule_checks import (
    RULE_CHECK_FN_MAP,
    check_rule_15,
    default_meta_rule,
    dispatch_rule_check,
    get_refinement,
    match_rule,
    resolve_exclusion_and_reselect,
    resolve_rule_conflict,
    rule4_low_coverage_blindspot,
    run_candidate_checks,
)
from jwsgj.xv_threshold_learning import (
    RULE_FP_TRACKER,
    SINGLE_SOURCE_CONFIRM_THRESHOLD,
    calibrate_confidence,
    get_rule_threshold,
    get_rule_weight,
    is_rule_retired,
)

_DEAD_CODE_FAMILIES = CONFLICT_DEAD_CODE_FAMILIES
_COMPLEXITY_FAMILIES = CONFLICT_COMPLEXITY_FAMILIES
_TEST_FAILURE_FAMILIES = CONFLICT_TEST_FAILURE_FAMILIES
__all__ = [
    "AUTO_STRENGTH_THRESHOLD",
    "MULTISRC_BACKING_FLOOR",
    "RULE_MATCHED_THRESHOLD_FLOOR",
    "SECURITY_CONFIRM_MATCHED",
    "SECURITY_CONFIRM_UNMATCHED",
    "SECURITY_UNCERTAIN_THRESHOLD",
    "SINGLE_SOURCE_STRENGTH_THRESHOLD",
    "STRENGTH_INFLATION_TIGHTENED",
    "STRENGTH_INFLATION_TRIGGER",
    "STYLE_RULE_PREFIXES",
    "PlDecision",
    "PlRule4",
    "apply_symbol_separation",
    "assemble_xv_result",
    "build_finding",
    "build_skipped_placeholder",
    "calibrate_base_by_source_fp",
    "call_rule_check_fn",
    "check_degraded_rules",
    "collect_matched_rules",
    "compute_adjusted_confidence",
    "compute_base_confidence",
    "compute_finding_strength",
    "conclusion_params_of",
    "determine_matched_conclusion",
    "enhanced_determine_conclusion",
    "handle_unmatched_rule",
    "has_real_confirmable_conf",
    "pl_independent_sources",
    "pl_rule4_safety_valve",
    "pl_select_rule",
    "prepare_locator_entry",
    "retired_suppression_stats",
    "style_rule_code",
    "symbol_separated_source_ids",
]
logger = logging.getLogger(__name__)
SECURITY_CONFIRM_MATCHED = env_number("JWSGJ_SEC_CONFIRM_MATCHED", 0.50, float)
SECURITY_CONFIRM_UNMATCHED = env_number("JWSGJ_SEC_CONFIRM_UNMATCHED", 0.60, float)
SECURITY_UNCERTAIN_THRESHOLD = env_number("JWSGJ_SEC_UNCERTAIN", 0.40, float)
AUTO_STRENGTH_THRESHOLD = env_number("JWSGJ_AUTO_STRENGTH_THRESHOLD", 0.55, float)
RULE_MATCHED_THRESHOLD_FLOOR = 0.45
MULTISRC_BACKING_FLOOR = 0.50
SINGLE_SOURCE_STRENGTH_THRESHOLD = 0.80
STRENGTH_INFLATION_TRIGGER = 0.80
STRENGTH_INFLATION_TIGHTENED = 0.90
_DEFAULT_RULE_SEMANTIC = "confirm"
_DEFAULT_RULE_MATCHED = False
_FP_COEFF_STRONG = 0.75
_FP_COEFF_MEDIUM = 0.55
_SECURITY_GATE_RULES = frozenset({"规则2", "规则12", "规则22"})
_SECURITY_DOWNGRADE_RULES = frozenset(_SECURITY_GATE_RULES | {"规则47"})
_REFINEMENT_CONCLUSIONS = frozenset(
    ("confirmed", "suppressed", "likely", "investigated", "uncertain"))
def _tm_family_marker(rule_family, rule_id) -> bool:
    return "TM-" in str(rule_family or "") or "TM-" in str(rule_id or "")
@dataclass(frozen=True, slots=True)
class _ConclusionStage:
    rule_id: str = ""
    rule_matched: bool = _DEFAULT_RULE_MATCHED
    rule_semantic: str = _DEFAULT_RULE_SEMANTIC
    base_conf: float = 0.0
    strength: float = 0.0
    effective_base: float = 0.0
    threshold: float = 0.0
    source_count: int = 1
    auto_strength_threshold: float = AUTO_STRENGTH_THRESHOLD
    finding_meta: dict = field(default_factory=dict)
    weak_confidence: bool = False
    low_reliability: bool = False
def _has_multisource_strength(stage: _ConclusionStage) -> bool:
    return (stage.source_count >= 2
            and stage.strength >= stage.auto_strength_threshold)
def _conclude_arbitrate(stage: _ConclusionStage) -> str:
    if (stage.source_count < 2
            and stage.effective_base < stage.threshold - CONF_BOOST_MODERATE):
        return "contradictory"
    if stage.effective_base >= stage.threshold:
        if stage.weak_confidence or stage.low_reliability:
            return "likely"
        return "confirmed"
    if _has_multisource_strength(stage):
        return "likely"
    return "uncertain"
@dataclass(frozen=True, slots=True)
class _StageOptions:
    rule_id: str
    rule_matched: bool
    rule_thresholds: dict[str, float] | None
    multi_source_bonus: float
    rule_semantic: str
    finding_meta: dict | None
def _build_stage(normalized: tuple,
                 options: _StageOptions) -> _ConclusionStage:
    (base_conf, strength, source_count,
     auto_strength_threshold) = normalized
    meta = options.finding_meta or {}
    return _ConclusionStage(
        rule_id=options.rule_id,
        rule_matched=options.rule_matched,
        rule_semantic=options.rule_semantic,
        base_conf=base_conf,
        strength=strength,
        effective_base=_resolve_effective_base(
            base_conf, source_count, options.multi_source_bonus),
        threshold=_resolve_rule_threshold(
            options.rule_thresholds, options.rule_id, options.rule_matched),
        source_count=source_count,
        auto_strength_threshold=auto_strength_threshold,
        finding_meta=meta,
        weak_confidence=signal_bool(meta.get("_weak_confidence")),
        low_reliability=signal_bool(meta.get("_low_reliability_dominant")),
    )
def enhanced_determine_conclusion(
    base_conf: float,
    strength: float,
    source_count: int,
    rule_id: str,
    rule_matched: bool = _DEFAULT_RULE_MATCHED,
    rule_thresholds: dict[str, float] | None = None,
    multi_source_bonus: float = 0.02,
    auto_strength_threshold: float | None = None,
    rule_semantic: str = _DEFAULT_RULE_SEMANTIC,
    finding_meta: dict | None = None,
    independent_source_count: int | None = None,
) -> str:
    try:
        normalized = _normalize_conf_inputs(
            base_conf, strength, source_count, independent_source_count,
            auto_strength_threshold)
        options = _StageOptions(
            rule_id=rule_id,
            rule_matched=rule_matched,
            rule_thresholds=_normalize_rule_thresholds(rule_thresholds),
            multi_source_bonus=_coerce_positive_float(multi_source_bonus),
            rule_semantic=(rule_semantic if isinstance(rule_semantic, str)
                           else _DEFAULT_RULE_SEMANTIC),
            finding_meta=(finding_meta
                          if isinstance(finding_meta, dict) else {}),
        )
        stage = _build_stage(normalized, options)
        for _stage_fn in _CONCLUDE_STAGES:
            _verdict = _stage_fn(stage)
            if _verdict is not None:
                return _verdict
        return _conclude_terminal_fallback(stage)
    except Exception:
        logger.exception("[enhanced_determine_conclusion] 异常降级为 uncertain（保守）")
        return "uncertain"
def _coerce_source_count(value, fallback, *, context: str = "source_count"):
    if isinstance(value, bool):
        return fallback
    try:
        return int(value)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'_coerce_source_count:{type(_e).__name__}({context})')
        return fallback
def _coerce_positive_float(value) -> float:
    parsed = safe_float(value, 0.0)
    if parsed is None or parsed <= 0.0:
        return 0.0
    return parsed
def _normalize_rule_thresholds(rule_thresholds: Any) -> dict[str, float]:
    if not isinstance(rule_thresholds, dict):
        return {}
    normalized: dict[str, float] = {}
    for rule_key, raw_threshold in rule_thresholds.items():
        parsed = safe_float(raw_threshold, None)
        if parsed is None:
            continue
        normalized[rule_key] = clamp_unit(parsed)
    return normalized
def _normalize_conf_inputs(base_conf, strength, source_count,
                           independent_source_count,
                           auto_strength_threshold):
    base_conf = safe_float(base_conf, 0.0)
    strength = safe_float(strength, 0.0)
    source_count = _coerce_source_count(source_count, 1)
    auto_strength_threshold = safe_float(
        auto_strength_threshold, AUTO_STRENGTH_THRESHOLD)
    if independent_source_count is not None:
        independent_source_count = _coerce_source_count(
            independent_source_count, None,
            context="independent_source_count")
    effective_source_count = (
        independent_source_count if independent_source_count is not None
        else source_count)
    return base_conf, strength, effective_source_count, auto_strength_threshold
def _resolve_rule_threshold(rule_thresholds, rule_id, rule_matched):
    threshold = (rule_thresholds or {}).get(rule_id, CONF_HIGH)
    if rule_matched:
        threshold = max(threshold - CONF_BOOST_STEP,
                        RULE_MATCHED_THRESHOLD_FLOOR)
    return threshold
def _resolve_effective_base(base_conf, effective_source_count,
                            multi_source_bonus):
    bonus = (max(0, effective_source_count - 2)
             * max(0.0, multi_source_bonus))
    return min(1.0, max(0.0, base_conf + bonus))
def _conclude_without_source(stage: _ConclusionStage) -> str | None:
    if stage.source_count <= 0:
        return "uncertain"
    return None
def _security_confirm_threshold(stage: _ConclusionStage) -> float:
    return (SECURITY_CONFIRM_MATCHED if stage.rule_matched
            else SECURITY_CONFIRM_UNMATCHED)
def _conclude_security_gate(stage: _ConclusionStage) -> str | None:
    if stage.rule_id not in _SECURITY_GATE_RULES:
        return None
    security_threshold = _security_confirm_threshold(stage)
    if stage.source_count >= 2 and stage.base_conf >= security_threshold:
        if stage.weak_confidence or stage.low_reliability:
            return "likely"
        return "confirmed"
    if stage.base_conf < SECURITY_UNCERTAIN_THRESHOLD:
        return "uncertain"
    return None
def _conclude_by_semantic(stage: _ConclusionStage) -> str | None:
    if stage.rule_semantic == "suppress" and stage.rule_matched:
        return "suppressed"
    if stage.rule_semantic == "arbitrate":
        return _conclude_arbitrate(stage)
    return None
def _conclude_standard(stage: _ConclusionStage) -> str | None:
    if stage.rule_id in _SECURITY_GATE_RULES:
        return None
    if stage.effective_base >= stage.threshold:
        if stage.weak_confidence or stage.low_reliability:
            return "likely"
        return "confirmed"
    return None
def _conclude_multisrc_backing(stage: _ConclusionStage) -> str | None:
    floor = min(stage.threshold, MULTISRC_BACKING_FLOOR)
    if stage.rule_id in _SECURITY_GATE_RULES:
        floor = max(floor, _security_confirm_threshold(stage))
    if _has_multisource_strength(stage):
        if (stage.base_conf >= floor and not stage.weak_confidence
                and not stage.low_reliability):
            return "confirmed"
        return "likely"
    return None
def _conclude_likely_multisrc(stage: _ConclusionStage) -> str | None:
    if (stage.effective_base >= stage.threshold - CONF_BOOST_STEP
            and stage.source_count >= 2):
        return "likely"
    return None
def _single_source_family_blocked(stage: _ConclusionStage) -> bool:
    meta = stage.finding_meta
    rule_family = str(meta.get("rule_family") or "")
    is_tm_family = (
        signal_bool(meta.get("_tm_family_present"))
        or _tm_family_marker(rule_family, stage.rule_id)
    )
    is_high_fp_family = (
        signal_bool(meta.get("_high_fp_family_present"))
        or is_family_member(rule_family, KNOWN_HIGH_FP_FAMILIES)
    )
    return (
        signal_bool(meta.get("_batch_source_rule", False))
        or is_tm_family
        or is_high_fp_family
    )
def _conclude_terminal_fallback(stage: _ConclusionStage) -> str:
    if (stage.effective_base < stage.auto_strength_threshold
            or stage.strength < stage.auto_strength_threshold):
        return "uncertain"
    if stage.source_count >= 2:
        return "likely"
    if stage.source_count == 1 and not _single_source_family_blocked(stage):
        return "likely"
    return "uncertain"
_CONCLUDE_STAGES: tuple[Callable[[_ConclusionStage], str | None], ...] = (
    _conclude_without_source,
    _conclude_security_gate,
    _conclude_by_semantic,
    _conclude_standard,
    _conclude_multisrc_backing,
    _conclude_likely_multisrc,
)
def _independent_source_ids(sources) -> list[str]:
    return independent_sources(normalize_sources(sources))
def _coerce_entry(entry) -> dict:
    if not isinstance(entry, dict):
        return {}
    if "findings" in entry and not isinstance(entry["findings"], list):
        entry["findings"] = dict_findings(entry["findings"])
    return entry
def _dominant_grouped_sources(grouped_sources) -> tuple[list[str], str] | None:
    if not isinstance(grouped_sources, dict):
        return None
    valid_groups = {}
    for family, sources in grouped_sources.items():
        if not isinstance(sources, SOURCE_SEQUENCE_TYPES):
            continue
        source_ids = sorted({
            source_id for source in sources
            if (source_id := source_id_text(source))
        })
        if source_ids:
            valid_groups[family] = source_ids
    if not valid_groups:
        return None
    dominant_key, dominant_ids = min(
        valid_groups.items(),
        key=lambda item: (-len(item[1]), str(item[0])))
    return dominant_ids, dominant_key
def _family_counts(findings: list) -> dict[str, int]:
    counts: dict[str, int] = {}
    for finding in findings:
        family = _finding_family(finding)
        if family:
            counts[family] = counts.get(family, 0) + 1
    return counts
def _source_methods_of(findings: list, family: str = "") -> list[str]:
    methods: set[str] = set()
    for finding in findings:
        method = source_id_text(finding.get("_source_method"))
        if not method:
            continue
        if family and _finding_family(finding) != family:
            continue
        methods.add(method)
    return sorted(methods)
def _rebuild_dominant_family_base(findings: list) -> tuple[list[str], str]:
    counts = _family_counts(findings)
    dominant_family = (
        max(sorted(counts), key=counts.get) if counts else "")
    return _source_methods_of(findings, dominant_family), dominant_family
def _extract_base_source_set(findings: list, grouped_sources,
                              fallback_sources) -> tuple[list[str], str]:
    _grouped = _dominant_grouped_sources(grouped_sources)
    if _grouped is not None:
        _base, _dominant_rf = _grouped
    else:
        _base, _dominant_rf = _rebuild_dominant_family_base(findings)
    if not _base:
        _base = sorted({
            source_id for source in normalize_sources(fallback_sources)
            if (source_id := source_id_text(source))
        })
    return _base, _dominant_rf
def _symbol_method_map(findings: list, base_set: set[str],
                       dominant_family: str) -> dict[str, set[str]]:
    symbols: dict[str, set[str]] = {}
    for finding in findings:
        if not isinstance(finding, dict):
            continue
        method = source_id_text(finding.get("_source_method"))
        if not method or method not in base_set:
            continue
        if _finding_family(finding) != dominant_family:
            continue
        symbol = extract_symbol(finding.get("message", ""))
        symbols.setdefault(symbol, set()).add(method)
    return symbols
def _dominant_symbol(symbols: dict[str, set[str]]) -> str:
    named_symbols = [symbol for symbol in symbols if symbol]
    if not named_symbols:
        return ""
    return max(sorted(named_symbols), key=lambda symbol: len(symbols[symbol]))
def apply_symbol_separation(findings: list, base: list[str],
                             dominant_rf: str) -> list[str]:
    if not dominant_rf:
        return base
    base_ids = [sid for sid in normalize_sources(base)
                if isinstance(sid, str) and sid]
    if not base_ids:
        return base
    base_set = set(base_ids)
    symbols = _symbol_method_map(findings, base_set, dominant_rf)
    dominant_symbol = _dominant_symbol(symbols)
    other_symbols = {
        symbol for symbol in symbols
        if symbol and symbol != dominant_symbol}
    if not (dominant_symbol and other_symbols):
        return base
    return sorted(
        (symbols.get(dominant_symbol, set()) | symbols.get("", set()))
        & base_set)
def symbol_separated_source_ids(entry_findings: Any, grouped_sources: Any=None, fallback_sources: Any=None) -> Any:
    _findings = dict_findings(entry_findings)
    _base, _dominant_rf = _extract_base_source_set(
        _findings, grouped_sources, fallback_sources)
    return apply_symbol_separation(_findings, _base, _dominant_rf)
def _numeric_confidence(finding: dict) -> float | None:
    value = finding.get("confidence")
    if not is_real_number(value):
        return None
    return float(value)
def _real_self_report(finding: dict) -> bool:
    return (
        _numeric_confidence(finding) is not None
        and not is_default_confidence(finding)
        and not signal_bool(finding.get("_low_reliability_high_conf"))
        and not signal_bool(finding.get("_known_fp_high_severity"))
    )
def _confirmable_self_report(finding: dict) -> bool:
    confidence = _numeric_confidence(finding)
    return (
        _real_self_report(finding)
        and confidence is not None
        and confidence >= SINGLE_SOURCE_CONFIRM_THRESHOLD
    )
def has_real_confirmable_conf(entry: dict) -> bool:
    entry = _coerce_entry(entry)
    return any(
        _confirmable_self_report(ff)
        for ff in dict_findings(entry.get("findings"))
    )
@dataclass(frozen=True, slots=True)
class _DowngradeRequest:
    conclusion: str
    rule_id: str
    entry: dict
    sources: list = field(default_factory=list)
    strength: float = 0.0
    exempt_by_strength: bool = False
    fallback_count: int | None = None
@dataclass(frozen=True, slots=True)
class _DowngradeLedger:
    key: str
    message: str
    delta: dict
_DOWNGRADE_LEDGERS: dict[str, tuple[str, str]] = {
    "matched": ("evtype_single_downgrade",
                "[CV] 单源降级保护失效，confirmed 降 likely 兜底并标记复核: %s"),
    "degraded": ("degraded_single_downgrade",
                 "[XV_Rule] 降级单源保护降级处理异常: %s"),
    "generic": ("generic_single_downgrade",
                "[XV_Rule] 通用回退单源保护异常(不阻断): %s"),
}
def _downgrade_ledger(path: str, delta: dict) -> _DowngradeLedger:
    key, message = _DOWNGRADE_LEDGERS[path]
    return _DowngradeLedger(key=key, message=message, delta=delta)
def _bump_log_counter(delta: dict, key: str) -> None:
    delta[key] = delta.get(key, 0) + 1
def _single_source_downgrade(request: _DowngradeRequest,
                             ledger: _DowngradeLedger) -> tuple[str, bool]:
    strength = safe_float(request.strength, 0.0)
    entry = _coerce_entry(request.entry)
    fallback_sources = normalize_sources(request.sources)
    _src_ids = symbol_separated_source_ids(
        entry.get("findings", []),
        grouped_sources=entry.get("_grouped_sources"),
        fallback_sources=fallback_sources,
    )
    if fallback_sources:
        fallback_count = count_independent_sources([
            sid for sid in fallback_sources
            if isinstance(sid, str) and sid
        ])
    else:
        fallback_count = _coerce_source_count(
            request.fallback_count, 0, context="fallback_count")
    _indep_count = (
        count_independent_sources(_src_ids) if _src_ids else fallback_count
    )
    if _indep_count >= 2:
        return request.conclusion, False
    if _strength_exemption_applies(request, entry, strength):
        return request.conclusion, False
    conclusion = ("likely" if request.rule_id in _SECURITY_DOWNGRADE_RULES
                  else "investigated")
    _bump_log_counter(ledger.delta, ledger.key)
    return conclusion, True
def _strength_exemption_applies(request: _DowngradeRequest, entry: dict,
                                strength: float) -> bool:
    if not request.exempt_by_strength:
        return False
    threshold = env_number("JWSGJ_SINGLE_SOURCE_STRENGTH_THRESHOLD",
                           SINGLE_SOURCE_STRENGTH_THRESHOLD, float)
    if strength >= STRENGTH_INFLATION_TRIGGER:
        threshold = max(threshold, STRENGTH_INFLATION_TIGHTENED)
    return strength >= threshold and has_real_confirmable_conf(entry)
def _record_refinement(delta: dict, locator, rule_id: str,
                       refined_to: str) -> None:
    _bump_log_counter(delta, "refinements_applied")
    delta.setdefault("refinement_paths", []).append({
        "locator": locator,
        "rule_id": rule_id,
        "refined_to": refined_to,
    })
@dataclass(frozen=True, slots=True)
class _MatchedRequest:
    cv2: Any
    rule_id: str
    base_conf: float
    strength: float
    source_count: int
    entry: dict
def _matched_base_conclusion(request: _MatchedRequest) -> tuple[str, str]:
    rule_semantic = get_rule_semantic(request.rule_id)
    if rule_semantic == "suppress":
        return "suppressed", rule_semantic
    if request.rule_id == "规则15":
        conclusion = ("confirmed" if has_real_confirmable_conf(request.entry)
                      else "investigated")
        return conclusion, rule_semantic
    conclusion = _determine_conclusion(
        request.cv2, request.base_conf, request.strength,
        request.source_count, request.rule_id, rule_matched=True,
        entry_findings=request.entry.get("findings", []),
        entry_grouped_sources=request.entry.get("_grouped_sources"))
    return conclusion, rule_semantic
def determine_matched_conclusion(cv2: Any, rule_id: Any, base_conf: Any, strength: Any, source_count: Any, entry: Any, locator: Any, _log_delta: Any) -> Any:
    entry = _coerce_entry(entry)
    _log_delta = _log_delta if isinstance(_log_delta, dict) else {}
    request = _MatchedRequest(
        cv2=cv2,
        rule_id=rule_id,
        base_conf=base_conf,
        strength=strength,
        source_count=source_count,
        entry=entry,
    )
    conclusion, _rule_semantic = _matched_base_conclusion(request)
    _refine_guard = not (_rule_semantic == "suppress" and conclusion == "suppressed")
    refinement = _apply_refinement(
        cv2, rule_id, sources=entry.get("sources", []), entry=entry)
    if refinement and _refine_guard:
        conclusion = refinement
        _record_refinement(_log_delta, locator, rule_id, refinement)
    if conclusion == "confirmed" and rule_id != "规则15":
        conclusion = _downgrade_confirmed_single_source(
            _DowngradeRequest(
                conclusion=conclusion,
                rule_id=rule_id,
                entry=entry,
                sources=entry.get("sources", []),
                strength=strength,
                exempt_by_strength=True,
                fallback_count=source_count,
            ),
            _downgrade_ledger("matched", _log_delta))
    return conclusion, _log_delta
def _entry_has_low_cv_family(entry: dict) -> bool:
    if not entry:
        return False
    for _ef in dict_findings(entry.get("findings")):
        if (_tm_family_marker(_finding_family(_ef), _ef.get("rule_id"))
                or signal_bool(_ef.get("_batch_source_rule"))):
            return True
    return False
def _mark_guard_failure_review(entry: dict) -> None:
    if not isinstance(entry, dict):
        return
    for _ef in dict_findings(entry.get("findings")):
        _ef["_review_required"] = True
        _ef["_review_reason"] = (
            "单源降级保护内部异常：confirmed 资格未经验证，已降 likely 待复核")
def _downgrade_confirmed_single_source(request: _DowngradeRequest,
                                       ledger: _DowngradeLedger) -> str:
    if request.conclusion != "confirmed":
        return request.conclusion
    try:
        conclusion, _ = _single_source_downgrade(request, ledger)
    except Exception as _e:
        logger.warning(ledger.message, _e, exc_info=True)
        conclusion = "likely"
        if isinstance(ledger.delta, dict):
            _bump_log_counter(ledger.delta, "single_downgrade_guard_failed")
        _mark_guard_failure_review(request.entry)
    return conclusion
def _rule15_fallback_conclusion(sources, entry) -> str:
    try:
        _r15_pass = check_rule_15(sources, entry)
    except Exception as e:  # noqa: BLE001
        logger.warning("[XV_Rule] 规则15检查失败,标记未通过: %s", e)
        _r15_pass = False
    if _r15_pass:
        return "confirmed" if has_real_confirmable_conf(entry) else "investigated"
    return "uncertain"
def _apply_degraded_match(degraded: dict, rule_id: str, entry: dict,
                          sources: list, strength, _log_delta: dict
                          ) -> tuple:
    _bump_log_counter(_log_delta, "degraded_matched")
    raw_rule = degraded.get("rule", rule_id)
    matched_rule = degraded.get("rule_base") or rule_id
    conclusion = degraded.get("conclusion", "likely")
    boost = degraded.get("boost", 0.0)
    conclusion = _downgrade_confirmed_single_source(
        _DowngradeRequest(
            conclusion=conclusion,
            rule_id=matched_rule,
            entry=entry,
            sources=sources,
            strength=strength,
            exempt_by_strength=False,
        ),
        _downgrade_ledger("degraded", _log_delta))
    degraded_info = {
        "is_degraded": True,
        "raw_rule": raw_rule,
        "reason": degraded.get("reason", ""),
    }
    return conclusion, matched_rule, boost, degraded_info
def _apply_generic_fallback(cv2, rule_id: str, entry: dict, sources: list,
                            base_conf, strength,
                            _log_delta: dict) -> tuple:
    source_count = len(pl_independent_sources(entry, sources))
    _bump_log_counter(_log_delta, "generic_fallback")
    _is_low_cv_family = _entry_has_low_cv_family(entry)
    if source_count == 1 and not _is_low_cv_family:
        return _rule15_fallback_conclusion(sources, entry), "规则15"
    conclusion = _determine_conclusion(cv2,
        base_conf, strength, source_count, rule_id,
        rule_matched=False,
        entry_findings=entry.get("findings", []),
        entry_grouped_sources=entry.get("_grouped_sources"))
    if source_count == 1:
        _bump_log_counter(_log_delta, "low_cv_family_skip")
        if conclusion in ("confirmed", "likely"):
            conclusion = "uncertain"
        return conclusion, rule_id
    conclusion = _downgrade_confirmed_single_source(
        _DowngradeRequest(
            conclusion=conclusion,
            rule_id=rule_id,
            entry=entry,
            sources=sources,
            strength=strength,
            exempt_by_strength=True,
        ),
        _downgrade_ledger("generic", _log_delta))
    return conclusion, rule_id
_AST_RELIABLE = frozenset({"B", "D"})
def _group_result_safe(independent_results, key) -> dict:
    _r = (independent_results or {}).get(key, {})
    return _r if isinstance(_r, dict) else {}
_E_ABNORMAL_STATUSES = frozenset({
    "fail", "failed", "blocked", "timeout", "error",
})
def _e_method_abnormal(independent_results) -> bool:
    status = _group_result_safe(independent_results, "E").get("status", "")
    return str(status).strip().lower() in _E_ABNORMAL_STATUSES
def _all_default_confidence(findings_data) -> bool:
    return bool(findings_data) and all(
        is_default_confidence(ff)
        for ff in dict_findings(findings_data)
    )
def _finding_family(ff: dict) -> str:
    family = source_id_text(ff.get("rule_family"))
    return family or source_id_text(ff.get("rule_id"))
def _findings_have_family(findings_data, families) -> bool:
    return any(_finding_family(ff) in families for ff in findings_data)
def _aggregate_severity_confidence(findings_data):
    max_sev_rank = 3
    max_conf = 0.0
    for ff in findings_data:
        c = ff.get("confidence", 0.5)
        if is_real_number(c):
            max_conf = max(max_conf, c)
        max_sev_rank = min(
            max_sev_rank, normalize_severity_rank(ff.get("severity")))
    return max_sev_rank, max_conf
def _degrade_conclusion_verdict(has_ast, is_high_sev, has_security_finding,
                                is_single_source, max_conf):
    if has_ast and is_high_sev:
        if has_security_finding and is_single_source:
            return "likely", 0
        return "confirmed", CONF_BOOST_MODERATE
    if has_ast or is_high_sev or max_conf >= CONF_VERY_HIGH:
        return "likely", 0
    return "uncertain", 0
def _degraded_conclusion(sources_set, findings_data):
    max_sev_rank, max_conf = _aggregate_severity_confidence(findings_data)
    has_ast = bool(_AST_RELIABLE & sources_set)
    is_high_sev = max_sev_rank <= 1
    has_security_finding = _findings_have_family(
        findings_data, _SECURITY_FAMILIES_DEGRADED)
    is_single_source = count_independent_sources(
        normalize_sources(sources_set)) < 2
    return _degrade_conclusion_verdict(has_ast, is_high_sev,
                                        has_security_finding, is_single_source, max_conf)
def _degraded_result(rule_base, conc, boost, reason) -> dict:
    return {"rule": f"{rule_base}(降级)", "rule_base": rule_base,
            "conclusion": conc, "boost": boost, "reason": reason}
_SECURITY_UPGRADE_FAMILIES = frozenset(
    (get_rule_family_set("security")
     | get_rule_family_set("security_extended")
     | {"SE-04"})
    - {"path_traversal", "PT-01", "SE-06"})
_TRAVERSAL_FAMILIES = frozenset({"path_traversal", "PT-01", "SE-06"})
_SECURITY_FAMILIES_DEGRADED = frozenset(
    _SECURITY_UPGRADE_FAMILIES | _TRAVERSAL_FAMILIES)
_CIRCULAR_DEP_FAMILIES = frozenset(
    get_rule_family_set("circular_dep") | {"CH01-HARD-CYCLE"})
_RECURSION_DEGRADED_FAMILIES = frozenset(
    (get_rule_family_set("recursion") - {"infinite_loop"}) | {"fuzz_crash"})
_BROKEN_CALL_FAMILIES = frozenset(
    get_rule_family_set("broken_call") | {"GF-08", "broken_cross_call"})
_GOD_FILE_FAMILIES = frozenset(
    get_rule_family_set("god_file") | {"GF-11", "SZ-01", "GF-13"})
_MUTABLE_GLOBAL_FAMILIES = frozenset(
    get_rule_family_set("mutable_global")
    | {RULE_MUTABLE_DEFAULT, "stress_issue"})
_FIX_RELATED_FAMILIES = frozenset(get_rule_family_set("fix_related"))
_API_COMPAT_FAMILIES = frozenset(get_rule_family_set("api_compat"))
_API_COMPAT_SELF_FAMILIES = frozenset(_API_COMPAT_FAMILIES | {"api_compat"})
_SECURITY_DEEP_FAMILIES = frozenset(
    {"danger_pattern", "unsafe_eval", RULE_COMMAND_INJECTION, "xxe", "ssrf"})
_CONFIG_SECURITY_FAMILIES = frozenset({
    "config_drift", RULE_INSECURE_CONFIG, "missing_config",
    "config_error", "config_security"})
_HISTORICAL_ANALYSIS_FAMILIES = frozenset(
    REGRESSION_FAMILIES | {"dead_code", "historical_pattern"})
_RULE29_FAMILIES = frozenset({"test_smell", "test_failure",
                              "low_mutation_score", "dead_code"})
_BROAD_EXCEPT_FAMILIES = frozenset(get_rule_family_set("broad_except"))
_R14_PRIMARY_FAMILIES = frozenset({
    "dead_code", "broad_except", "circular_dep", "path_traversal",
    "unbounded_recursion", "broken_call", "sql_injection", RULE_HIGH_COMPLEXITY,
    "mutable_global", "architecture", "fix_safety"})
_AVAILABILITY_RULES = [
    ("规则8", {"B"},
     "E", _BROAD_EXCEPT_FAMILIES,
     "E不可用,宽泛异常诊断单源发现降级"),
    ("规则9", {"B"}, "E", _MUTABLE_GLOBAL_FAMILIES,
     "E不可用,全局变量诊断单源发现降级"),
    ("规则13", {"B"}, "E", _GOD_FILE_FAMILIES,
     "E不可用,大文件诊断单源发现降级"),
]
def _special_upgrade(source_set, findings_data, conc, *,
                     families=None, require_ast=False):
    if (conc != "likely"
            or count_independent_sources(normalize_sources(source_set)) < 2):
        return None
    if require_ast and not (_AST_RELIABLE & source_set):
        return None
    if _all_default_confidence(findings_data):
        return None
    if families is not None and not _findings_have_family(
            findings_data, families):
        return None
    return "confirmed", CONF_BOOST_MODERATE
_SECURITY_UPGRADE = partial(
    _special_upgrade, families=_SECURITY_UPGRADE_FAMILIES)
_TRAVERSAL_UPGRADE = partial(_special_upgrade, require_ast=True)
_STRICT_COMPLEXITY_FAMILIES = frozenset(
    {RULE_HIGH_COMPLEXITY, "AST-complexity", "complexity"})
_DEGRADED_SIMPLE_RULES = [
    ("规则1", {"E"}, {"C"}, _DEAD_CODE_FAMILIES, "C不可用,E单源死代码发现降级"),
    ("规则1b", {"C"}, {"E"}, _DEAD_CODE_FAMILIES, "E不可用,C单源死代码发现降级"),
    ("规则3", {"B"}, {"E"}, _COMPLEXITY_FAMILIES,
     "E不可用,复杂度诊断单源发现降级"),
    ("规则7", {"B"}, {"E"}, _CIRCULAR_DEP_FAMILIES,
     "E不可用,B循环依赖单源发现降级"),
    ("规则10", {"B"}, {"E"}, _RECURSION_DEGRADED_FAMILIES,
     "E不可用,B递归单源发现降级"),
    ("规则11", {"C"}, {"E"}, _BROKEN_CALL_FAMILIES,
     "E不可用,C调用断裂单源发现降级"),
    ("规则19", {"B"}, {"E"}, REGRESSION_FAMILIES,
     "E不可用,B基线退化单源发现降级"),
    ("规则20", {"F"}, {"E"}, _FIX_RELATED_FAMILIES,
     "E回归不可用,F修复单源发现降级"),
    ("规则22", {"D"}, set(), _SECURITY_DEEP_FAMILIES,
     "D组污点分析单源发现降级"),
    ("规则25", {"B"}, {"E"}, _API_COMPAT_FAMILIES,
     "E不可用,B API兼容性单源发现降级"),
    ("规则30", {"B"}, {"E"}, _HISTORICAL_ANALYSIS_FAMILIES,
     "E不可用,B历史分析单源发现降级"),
    ("规则44", {"B"}, {"E"}, _API_COMPAT_SELF_FAMILIES,
     "E不可用,B API向后兼容单源发现降级"),
    ("规则48", {"A"}, {"D", "E"}, _CONFIG_SECURITY_FAMILIES,
     "D/E不可用,A配置安全单源发现降级"),
    ("规则3b", set(), {"E"},
     _STRICT_COMPLEXITY_FAMILIES | {
         "SZ-01", "SZ-02", "long_function", "deep_nesting",
         RULE_TOO_MANY_PARAMS},
     "T14单源复杂度降级(多源family不匹配)"),
    ("规则4b", set(), {"B"},
     {"code_smell", "AST-lint", "diag_general", "AST-pattern",
      "facade_antipattern", "AST-antipattern"},
     "多源误报抑制降级(family不匹配)"),
    ("规则28b", set(), {"B"},
     {"dead_code", "AST-verification", "historical_pattern", "HP-006", "HP-003"},
     "D15单源历史缺陷降级(多源family不匹配)"),
    ("规则33b", set(), {"B"},
     {"type_check", "AST-pattern", "TY-01", "missing_type_annotation"},
     "D20单源类型注解降级(多源family不匹配)"),
    ("规则42b", set(), {"E"},
     frozenset({"perf_hotspot", "dynamic_exec", "performance", "perf_issue",
                "infinite_loop"}),
     "T9单源性能热点降级(多源family不匹配)"),
    ("规则43b", set(), {"C", "E"},
     {"resource_leak", "AST-resource", "memory_leak", "dynamic_exec"},
     "多源内存泄漏降级(family不匹配)"),
    ("规则46b", set(), {"E"},
     _STRICT_COMPLEXITY_FAMILIES | {CAT_MAINTAINABILITY},
     "T14单源可维护性降级(多源family不匹配)"),
    ("规则51b", set(), {"A"},
     {"config_drift", "doc_consistency", "static_text"},
     "D19/A14单源配置漂移降级(family不匹配)"),
]
_DEGRADED_CONDITIONAL_RULES = [
    ("规则2", {"B", "D"}, {"E"},
     _SECURITY_UPGRADE_FAMILIES,
     "E不可用,安全诊断单源发现降级", _SECURITY_UPGRADE),
    ("规则12", {"D", "B"}, {"E"},
     _TRAVERSAL_FAMILIES,
     "E不可用,安全诊断路径穿越单源发现降级", _TRAVERSAL_UPGRADE),
]
def _emit_degraded_hit(rule_name, source_set, findings_data, reason,
                       _degraded_logger, upgrade=None) -> dict:
    conc, boost = _degraded_conclusion(source_set, findings_data)
    if upgrade is not None:
        _upgraded = upgrade(source_set, findings_data, conc)
        if _upgraded:
            conc, boost = _upgraded
    _degraded_logger.debug("[降级] %s: sources=%s, conclusion=%s",
                           rule_name, source_set, conc)
    return _degraded_result(rule_name, conc, boost, f"{reason}({conc})")
def _rule_row_applicable(required, excluded, families, source_set,
                         findings_data) -> bool:
    if excluded & source_set:
        return False
    if required:
        if not (required & source_set):
            return False
    elif count_independent_sources(normalize_sources(source_set)) != 1:
        return False
    return _findings_have_family(findings_data, families)
def _match_simple_rules(source_set, findings_data, _degraded_logger):
    for rule_name, required, excluded, families, reason in _DEGRADED_SIMPLE_RULES:
        if not _rule_row_applicable(required, excluded, families,
                                    source_set, findings_data):
            continue
        return _emit_degraded_hit(rule_name, source_set, findings_data, reason,
                                  _degraded_logger)
    return None
def _match_conditional_rules(source_set, findings_data, _degraded_logger):
    for rule_name, required_any, excluded, families, reason, upgrade_fn in _DEGRADED_CONDITIONAL_RULES:
        if not _rule_row_applicable(required_any, excluded, families,
                                    source_set, findings_data):
            continue
        return _emit_degraded_hit(rule_name, source_set, findings_data, reason,
                                  _degraded_logger, upgrade=upgrade_fn)
    return None
def _rule5_test_failure_match(source_set, findings_data, independent_results,
                             _degraded_logger):
    if "E" not in source_set:
        return None
    if (_e_method_abnormal(independent_results)
            and _findings_have_family(findings_data, _TEST_FAILURE_FAMILIES)):
        return _emit_degraded_hit(
            "规则5", source_set, findings_data,
            "测试方法异常,无诊断源交叉,降级", _degraded_logger)
    return None
def _rule18_single_high_sev_match(source_set, findings_data, _degraded_logger):
    _independent = _independent_source_ids(source_set)
    if "F" in source_set or len(_independent) != 1:
        return None
    src = _independent[0]
    for ff in findings_data:
        if normalize_severity_rank(ff.get("severity")) <= 1:
            return _emit_degraded_hit(
                "规则18", source_set, findings_data,
                f"{src}单源高严重度发现降级", _degraded_logger)
    return None
def _check_rules_5_18(source_set, findings_data, independent_results, _degraded_logger):
    result = _rule5_test_failure_match(source_set, findings_data,
                                       independent_results, _degraded_logger)
    if result is not None:
        return result
    return _rule18_single_high_sev_match(source_set, findings_data, _degraded_logger)
def _check_rule29_degraded(source_set, findings_data, independent_results, _degraded_logger):
    if "E" not in source_set or "B" in source_set:
        return None
    if _e_method_abnormal(independent_results):
        return None
    if not _findings_have_family(findings_data, _RULE29_FAMILIES):
        return None
    return _emit_degraded_hit(
        "规则29", source_set, findings_data,
        "B不可用,E突变覆盖单源发现降级", _degraded_logger)
def _check_availability_rules(source_set, findings_data, _degraded_logger):
    _available_methods = available_methods()
    if _available_methods is None:
        return None
    for rule_name, required_any, missing_method, families, reason in _AVAILABILITY_RULES:
        if not (required_any & source_set):
            continue
        if missing_method in _available_methods:
            continue
        if not _findings_have_family(findings_data, families):
            continue
        return _emit_degraded_hit(
            rule_name, source_set, findings_data, reason, _degraded_logger)
    return None
def _partial_degrade_reason(ff: dict) -> str:
    factor = degrade_factor_of(ff)
    method = ff.get("_source_method") or "?"
    reason = ff.get("_partial_reason") or "?"
    return f"{method}({reason},-{round((1 - factor) * 100)}%)"
_ES_CONFIRM_THRESHOLD = 0.55
def _es_tier_result(rule_base, es_val, confirmed_reason, likely_reason):
    if es_val >= _ES_CONFIRM_THRESHOLD:
        return _degraded_result(rule_base, "confirmed",
                                CONF_BOOST_STEP, confirmed_reason)
    return _degraded_result(rule_base, "likely", 0.0, likely_reason)
def _rule14_multi_source_match(source_set, findings_data, _degraded_logger):
    _independent = _independent_source_ids(source_set)
    if len(_independent) < 2:
        return None
    if not _findings_have_family(findings_data, _R14_PRIMARY_FAMILIES):
        return None
    _es_val = evidence_strength_weighted(sorted(_independent))
    _result = _es_tier_result(
        "规则14", _es_val,
        f"多源文件级匹配(es={_es_val:.2f})",
        f"多源文件级匹配但证据不足(es={_es_val:.2f})")
    _degraded_logger.debug("[降级] 规则14: %s, es=%.2f, sources=%s",
                           _result["conclusion"], _es_val, source_set)
    return _result
def _rule17_metric_match(source_set, findings_data):
    _metric_sources = {"B"}
    _independent = set(_independent_source_ids(source_set))
    if not ((_independent & _metric_sources)
            and (_independent - _metric_sources)):
        return None
    if not any(not is_status_message_finding(ff) for ff in findings_data):
        return None
    _es_val17 = evidence_strength_weighted(sorted(_independent))
    return _es_tier_result(
        "规则17", _es_val17,
        f"指标越界交叉确认(es={_es_val17:.2f})",
        f"指标越界但证据不足(es={_es_val17:.2f})")
def _generic_partial_result(source_set, findings_data, _degraded_logger):
    partial_findings = [
        ff for ff in findings_data if signal_bool(ff.get("_partial_degrade"))]
    if source_set or not partial_findings:
        return None
    conc, boost = _degraded_conclusion(source_set, findings_data)
    detail = "; ".join(
        _partial_degrade_reason(ff) for ff in partial_findings[:3])
    _degraded_logger.debug("[降级] 通用partial: %s, conclusion=%s", detail, conc)
    return _degraded_result("规则-通用partial", conc, boost,
                            f"部分结果来源降级({detail})→{conc}")
def _check_rules_14_17_partial(source_set, findings_data, _degraded_logger):
    result = _rule14_multi_source_match(source_set, findings_data, _degraded_logger)
    if result is not None:
        return result
    result = _rule17_metric_match(source_set, findings_data)
    if result is not None:
        return result
    return _generic_partial_result(source_set, findings_data, _degraded_logger)
def _normalize_context(data, independent_results) -> tuple[dict, dict]:
    if not isinstance(data, dict):
        data = {}
    if not isinstance(independent_results, dict):
        independent_results = {}
    return data, independent_results
def _normalize_sources(sources) -> set:
    return {
        source_id for source in normalize_sources(sources)
        if (source_id := source_id_text(source))
    }
def check_degraded_rules(sources: Iterable[str], data: dict, _locator: str,
                         independent_results: dict | None = None) -> dict | None:
    try:
        data, independent_results = _normalize_context(data, independent_results)
        source_set = _normalize_sources(sources)
        _degraded_logger = logger.getChild("degraded")
        findings_data = [
            ff for ff in dict_findings(data.get("findings"))
            if not is_status_message_finding(ff)
        ]
        _r = _match_simple_rules(source_set, findings_data, _degraded_logger)
        if _r:
            return _r
        _r = _match_conditional_rules(source_set, findings_data, _degraded_logger)
        if _r:
            return _r
        _r = _check_rules_5_18(source_set, findings_data, independent_results, _degraded_logger)
        if _r:
            return _r
        _r = _check_rule29_degraded(source_set, findings_data, independent_results, _degraded_logger)
        if _r:
            return _r
        _r = _check_availability_rules(source_set, findings_data, _degraded_logger)
        if _r:
            return _r
        return _check_rules_14_17_partial(source_set, findings_data, _degraded_logger)
    except Exception as e:  # noqa: BLE001
        logger.warning("[XV] 降级规则检查失败 in check_degraded_rules(): %s", e)
        return None
def handle_unmatched_rule(cv2: Any, rule_id: Any, sources: Any, entry: Any, locator: Any, base_conf: Any, strength: Any, boost: Any, _log_delta: Any) -> Any:
    sources = normalize_sources(sources)
    entry = _coerce_entry(entry)
    _log_delta = _log_delta if isinstance(_log_delta, dict) else {}
    try:
        degraded = check_degraded_rules(
            sources, entry, locator, cv2.independent_results
        )
    except Exception as e:  # noqa: BLE001
        logger.warning("[XV_Rule] 规则匹配降级,回退uncertain: rule=%s: %s", rule_id, e)
        return "uncertain", rule_id, boost, None, _log_delta
    if degraded:
        conclusion, rule_id, boost, degraded_info = _apply_degraded_match(
            degraded, rule_id, entry, sources, strength, _log_delta)
        return conclusion, rule_id, boost, degraded_info, _log_delta
    conclusion, rule_id = _apply_generic_fallback(
        cv2, rule_id, entry, sources, base_conf, strength, _log_delta)
    return conclusion, rule_id, boost, None, _log_delta
def _aggregate_protection_flags(meta_findings: list) -> tuple[bool, bool, bool]:
    _any_tm = False
    _any_high_fp = False
    _any_batch = False
    for _f in meta_findings:
        _rf_f = _finding_family(_f)
        _any_tm = _any_tm or _tm_family_marker(_rf_f, _f.get("rule_id"))
        _any_high_fp = (_any_high_fp or is_family_member(
            _rf_f, KNOWN_HIGH_FP_FAMILIES))
        _any_batch = _any_batch or signal_bool(
            _f.get("_batch_source_rule"))
    return _any_tm, _any_high_fp, _any_batch
def _low_reliability_dominant(meta_findings: list) -> bool:
    try:
        counts = _family_counts(meta_findings)
        dominant = max(sorted(counts), key=counts.get) if counts else ""
        return bool(dominant) and family_reliability_base(dominant) < 0.90
    except Exception as e:  # noqa: BLE001
        logger.warning("[Conclusion] 可靠性元数据查询异常(中性回退，不应发生): %s", e)
        return False
def _all_confidences_weak(meta_findings: list) -> bool:
    return all(
        (confidence := _numeric_confidence(f)) is None or confidence < 0.50
        for f in meta_findings
    )
def _build_finding_meta(entry_findings) -> dict:
    _meta_findings = dict_findings(entry_findings)
    if not _meta_findings:
        return {}
    _first_f = _meta_findings[0]
    _any_tm, _any_high_fp, _any_batch = _aggregate_protection_flags(_meta_findings)
    _finding_meta: dict = {
        "rule_family": _finding_family(_first_f),
        "_batch_source_rule": _any_batch,
        "_tm_family_present": _any_tm,
        "_high_fp_family_present": _any_high_fp,
    }
    if _all_confidences_weak(_meta_findings):
        _finding_meta["_weak_confidence"] = True
    if _low_reliability_dominant(_meta_findings):
        _finding_meta["_low_reliability_dominant"] = True
    return _finding_meta
def _safe_rule_semantic(rule_id: str) -> str:
    try:
        return get_rule_semantic(rule_id)
    except Exception:  # noqa: BLE001
        logger.warning(
            "[Conclusion] get_rule_semantic failed for %s, using default %s",
            rule_id, _DEFAULT_RULE_SEMANTIC)
        return _DEFAULT_RULE_SEMANTIC
def _effective_base_conf(base_conf: float, entry_findings) -> float:
    if not entry_findings:
        return base_conf
    findings = [
        f for f in dict_findings(entry_findings)
        if not is_status_message_finding(f)
    ]
    if not any(is_default_confidence(f) for f in findings):
        return base_conf
    real_confs = [
        f["confidence"]
        for f in findings
        if not is_default_confidence(f)
        and is_real_number(f.get("confidence"))
    ]
    if any(c >= base_conf for c in real_confs):
        return base_conf
    return base_conf * CONF_DEFAULT_PENALTY
def _determine_conclusion(cv2, base_conf: float, strength: float,
                          source_count: int, rule_id: str,
                          rule_matched: bool = _DEFAULT_RULE_MATCHED,
                          entry_findings: list | None = None,
                          entry_grouped_sources: Any = None) -> str:
    base_conf = safe_float(base_conf, 0.0)
    strength = safe_float(strength, 0.0)
    entry_findings = dict_findings(entry_findings)
    if entry_findings and all(
            is_status_message_finding(f) for f in entry_findings):
        return "uncertain"
    _effective_conf = _effective_base_conf(base_conf, entry_findings)
    try:
        threshold = get_rule_threshold(rule_id)
        _semantic = _safe_rule_semantic(rule_id)
        _finding_meta = _build_finding_meta(entry_findings)
        _source_ids = symbol_separated_source_ids(
            entry_findings, grouped_sources=entry_grouped_sources)
        _independent_source_count = (
            count_independent_sources(_source_ids) if _source_ids else source_count
        )
        enh_conclusion = enhanced_determine_conclusion(
            base_conf=_effective_conf, strength=strength,
            source_count=source_count, rule_id=rule_id,
            rule_matched=rule_matched,
            rule_thresholds={rule_id: threshold},
            auto_strength_threshold=cv2.AUTO_STRENGTH_THRESHOLD,
            rule_semantic=_semantic,
            finding_meta=_finding_meta,
            independent_source_count=_independent_source_count,
        )
        return enh_conclusion
    except Exception as e:  # noqa: BLE001
        logger.warning("[Conclusion-Enh] raised: %s", e)
        return "uncertain"
def _apply_refinement(cv2, rule_id: str, sources: list, entry: dict) -> str | None:
    sources = normalize_sources(sources)
    entry = _coerce_entry(entry)
    dispatch = get_refinement(rule_id)
    if dispatch is None:
        return None
    try:
        refine_func, result_str, needs_cv2_results = dispatch
        if needs_cv2_results:
            _refined = refine_func(sources, entry, cv2.independent_results)
        else:
            _refined = refine_func(sources, entry)
        if _refined:
            if isinstance(_refined, str):
                return (_refined if _refined in _REFINEMENT_CONCLUSIONS
                        else result_str)
            return result_str
    except Exception as _ie:  # noqa: BLE001
        logger.debug("[XV_Rule] 精炼函数异常,降级沿用原结论: %s", _ie)
        return None
    return None
class _PlRuleSelection(NamedTuple):
    rule_id: str
    selection_trace: dict
    first_round_results: dict
    all_matched: set
class PlRule4(NamedTuple):
    conclusion: str
    rule4_suppression_applied: bool
    safety_valve_override: str
class PlDecision(NamedTuple):
    rule_id: str
    selection_trace: dict
    first_round_results: dict
    all_matched: set
    rule_matched: object
    check_fn: object
    base_conf: float
    strength: float
    secondary_rules: list
    multi_rule_boost: float
    boost: float
    conclusion: str
    adj_log: list
    degraded_info: object
    log_delta: dict
def _coerce_decision(dec: Any) -> Any:
    replacements: dict[str, Any] = {}
    if not isinstance(getattr(dec, "selection_trace", None), dict):
        replacements["selection_trace"] = {}
    if not isinstance(getattr(dec, "first_round_results", None), dict):
        replacements["first_round_results"] = {}
    if not isinstance(getattr(dec, "all_matched", None), (set, frozenset)):
        replacements["all_matched"] = set()
    if not isinstance(getattr(dec, "secondary_rules", None), list):
        replacements["secondary_rules"] = []
    _degraded = getattr(dec, "degraded_info", None)
    if _degraded is not None and not isinstance(_degraded, dict):
        replacements["degraded_info"] = None
    if not isinstance(getattr(dec, "adj_log", None), list):
        replacements["adj_log"] = []
    if not isinstance(getattr(dec, "log_delta", None), dict):
        replacements["log_delta"] = {}
    _raw_boost = getattr(dec, "multi_rule_boost", 0.0)
    _boost = safe_float(_raw_boost, 0.0)
    if not isinstance(_raw_boost, float) or not is_real_number(_raw_boost):
        replacements["multi_rule_boost"] = _boost if _boost is not None else 0.0
    if not replacements:
        return dec
    replace = getattr(dec, "_replace", None)
    if callable(replace):
        try:
            return replace(**replacements)
        except TypeError:
            return dec
    for _field, _value in replacements.items():
        try:
            setattr(dec, _field, _value)
        except (AttributeError, TypeError):
            continue
    return dec
def pl_independent_sources(entry: dict, sources: list) -> list:
    entry = entry if isinstance(entry, dict) else {}
    try:
        _ids = symbol_separated_source_ids(
            entry.get("findings", []),
            grouped_sources=entry.get("_grouped_sources"),
            fallback_sources=sources,
        )
    except Exception as _src_e:  # noqa: BLE001
        log_swallowed(
            __name__, _src_e,
            context=f'pl_independent_sources:{type(_src_e).__name__}')
        _ids = []
    return independent_sources(_ids or sources)
def pl_select_rule(cv2, entry: dict, sources: list,
                    locator: str) -> _PlRuleSelection:
    _independent = pl_independent_sources(entry, sources)
    source_count = len(_independent)
    _initial_match_rule = match_rule(cv2, entry)
    rule_id = _initial_match_rule
    _selection_trace = {
        "initial_match": _initial_match_rule or "",
        "used_default": not bool(_initial_match_rule),
        "default_rule": (default_meta_rule(source_count)
                         if not _initial_match_rule else ""),
        "conflict_resolved_rule": "",
        "all_matched": [],
        "final_rule": "",
    }
    if not rule_id:
        rule_id = _selection_trace["default_rule"]
    rule_id = resolve_rule_conflict(cv2, rule_id, _independent, entry)
    _selection_trace["conflict_resolved_rule"] = rule_id
    rule_id, _first_round_results, _all_matched = collect_matched_rules(
        cv2, rule_id, sources, entry, locator)
    _selection_trace["all_matched"] = sorted(_all_matched) if _all_matched else []
    _selection_trace["final_rule"] = rule_id
    return _PlRuleSelection(rule_id, _selection_trace,
                            _first_round_results, _all_matched)
def collect_matched_rules(cv2: Any, rule_id: Any, sources: Any, entry: Any, locator: Any) -> Any:
    sources = clean_source_ids(normalize_sources(sources))
    _first_round_results = {}
    _all_matched = set()
    try:
        run_candidate_checks(
            cv2, sources, entry, _first_round_results, _all_matched)
        rule_id = resolve_exclusion_and_reselect(
            rule_id, locator, _first_round_results, _all_matched)
    except Exception as _ie:  # noqa: BLE001
        log_swallowed(__name__, _ie, context='collect_matched_rules')
        logger.debug("[Rules] collect_matched_rules 部分失败: %s", _ie)
    return rule_id, _first_round_results, _all_matched
def _record_rule_check_failure(cv2: Any, rule_id: Any, locator: Any,
                               error: Exception) -> None:
    log = getattr(cv2, "_rule_execution_log", None)
    if not isinstance(log, dict):
        return
    failures = log.setdefault("rule_check_failures", [])
    if not isinstance(failures, list):
        return
    failures.append({
        "locator": locator,
        "rule_id": rule_id,
        "error": str(error)[:MESSAGE_TRUNCATE_LEN],
    })
def call_rule_check_fn(cv2: Any, rule_id: Any, sources: Any, entry: Any, locator: Any, _first_round_results: Any, _exec_log_lock: Any=None) -> Any:
    entry = _coerce_entry(entry)
    first_round = _first_round_results if isinstance(_first_round_results, dict) else {}
    rule_matched = first_round.get(rule_id, None)
    check_fn = RULE_CHECK_FN_MAP.get(rule_id)
    if rule_matched is None and check_fn is not None:
        try:
            rule_matched = dispatch_rule_check(cv2, check_fn, sources, entry)
            first_round[rule_id] = rule_matched
        except Exception as e:  # noqa: BLE001
            logger.warning("[Rules] 规则 %s check 异常: %s", rule_id, e)
            rule_matched = False
            with (_exec_log_lock if _exec_log_lock is not None else nullcontext()):
                _record_rule_check_failure(cv2, rule_id, locator, e)
    elif rule_matched is None:
        # 可选 worker 可以只提供首轮结果；无本地 check_fn 不等于否定已有命中。
        rule_matched = False
    return rule_matched, check_fn
def _entry_has_flag(entry: dict, key: str) -> bool:
    return any(
        signal_bool(f.get(key))
        for f in dict_findings(_coerce_entry(entry).get("findings")))
def _pl_rule4_strong_confirm(entry: dict, sources: list) -> bool:
    entry = _coerce_entry(entry)
    _has_mutation_confirm = _entry_has_flag(
        entry, SIGNAL_MUTATION_CONFIRMED_DEAD)
    _raw_mc = entry.get("max_confidence", 0.0)
    _structural_conf = _raw_mc if is_real_number(_raw_mc) else 0.0
    _has_ensemble_with_corroboration = (
        _entry_has_flag(entry, "_ensemble_is_confirmed")
        and len(pl_independent_sources(entry, sources)) >= 2
        and _structural_conf >= SINGLE_SOURCE_CONFIRM_THRESHOLD
    )
    return _has_mutation_confirm or _has_ensemble_with_corroboration
def _pl_rule4_blindspot_override(cv2, entry: dict, sources: list,
                                 dec: PlDecision) -> PlRule4 | None:
    if not rule4_low_coverage_blindspot(
            sources, entry, cv2.independent_results):
        return None
    if dec.conclusion == "suppressed" and dec.rule_id != "规则4":
        return PlRule4(dec.conclusion, False, "")
    prior = dec.conclusion
    conclusion = "likely" if prior in ("confirmed", "suppressed") else prior
    override = (
        "rule4_blindspot_protected: 涉及文件覆盖率低于阈值,"
        "'测试通过'不构成误报反驳证据,解除规则4抑制"
        f"({prior}->{conclusion})")
    _bump_log_counter(dec.log_delta, "rule4_blindspot_protected")
    return PlRule4(conclusion, False, override)
def _pl_rule4_single_confirm_override(
        entry: dict, dec: PlDecision) -> PlRule4 | None:
    if not (dec.conclusion == "confirmed" and dec.rule_id == "规则15"
            and has_real_confirmable_conf(entry)):
        return None
    override = (
        "rule4_single_confirm_preserved: 规则15单源确认资格"
        "(带资格背书)优先于规则4弱启发式抑制,confirmed改判"
        "investigated保留人工复核")
    _bump_log_counter(dec.log_delta, "rule4_single_confirm_preserved")
    return PlRule4("investigated", False, override)
def pl_rule4_safety_valve(cv2, entry: dict, sources: list,
                           dec: PlDecision) -> PlRule4:
    entry = _coerce_entry(entry)
    dec = _coerce_decision(dec)
    if dec.first_round_results.get("规则4") is not True:
        return PlRule4(dec.conclusion, False, "")
    if _pl_rule4_strong_confirm(entry, sources):
        _bump_log_counter(dec.log_delta, "rule4_overridden_by_strong_evidence")
        if isinstance(dec.adj_log, list):
            dec.adj_log.append("rule4_skipped: strong_confirm_signal_present")
        return PlRule4(dec.conclusion, False, "")
    blindspot = _pl_rule4_blindspot_override(cv2, entry, sources, dec)
    if blindspot is not None:
        return blindspot
    single_confirm = _pl_rule4_single_confirm_override(entry, dec)
    if single_confirm is not None:
        return single_confirm
    _bump_log_counter(dec.log_delta, "rule4_suppressed")
    return PlRule4("suppressed", True, "")
def _max_fp_rate_of(rule_families) -> float:
    if isinstance(rule_families, str):
        rule_families = (rule_families,)
    max_fp_rate = 0.0
    for fam in rule_families:
        family = source_id_text(fam)
        rec = RULE_FP_TRACKER.get(family) if family else None
        if not isinstance(rec, dict):
            continue
        fr = rec.get("fp_rate", FP_RATE_LOW)
        if not is_valid_fp_rate(fr):
            continue
        max_fp_rate = max(max_fp_rate, fr)
    return max_fp_rate
def calibrate_base_by_source_fp(base_conf: Any, rule_families: Any) -> Any:
    if base_conf is None or not rule_families:
        return base_conf
    bc = safe_float(base_conf, None)
    if bc is None:
        return base_conf
    try:
        max_fp_rate = _max_fp_rate_of(rule_families)
    except (TypeError, ValueError, AttributeError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'calibrate_base_by_source_fp:{type(_e).__name__}')
        return base_conf
    if max_fp_rate <= FP_RATE_LOW:
        return base_conf
    penalty = max_fp_rate - FP_RATE_LOW
    calibrated = bc * (1.0 - penalty)
    return round(min(1.0, max(0.0, calibrated)), 3)
def compute_finding_strength(data, sources, full_sources, partial_sources, strength):
    data = _coerce_entry(data)
    _deg_factors = partial_deg_factors_map(dict_findings(data.get("findings")))
    _deg_kwarg = _deg_factors if _deg_factors else None
    if strength is not None:
        _s = safe_float(strength, None)
        if _s is not None:
            return clamp_unit(_s)
    if full_sources:
        strength = evidence_strength_weighted(full_sources, _deg_kwarg)
        if partial_sources:
            _avg_deg = sum(
                _deg_factors.get(s, CONF_VERY_HIGH) for s in partial_sources
            ) / len(partial_sources)
            strength = strength * (0.5 + 0.5 * _avg_deg)
    else:
        strength = evidence_strength_weighted(sources, _deg_kwarg)
        strength = max(strength * AUTO_THRESHOLD_DECAY, CONF_FLOOR)
    return strength
def _env_score_map() -> dict[str, float] | None:
    raw = os.environ.get("JWSGJ_SCORE_MAP", "")
    if not raw:
        return {}
    try:
        parsed = json.loads(raw)
    except (ValueError, RecursionError):
        logger.warning("[XV_Rule] _env_score_map score map parse failed", exc_info=True)
        return None
    if not isinstance(parsed, dict):
        logger.warning("[XV_Rule] score map 顶层非 dict(%s)，回退中性置信度",
                       type(parsed).__name__)
        return None
    injected: dict[str, float] = {}
    for k, v in parsed.items():
        num = safe_float(v, None)
        if num is None:
            logger.warning("[XV_Rule] score map 非数值跳过 %s=%r", k, v)
            continue
        if 0.0 <= num <= 1.0:
            injected[str(k)] = num
        else:
            logger.warning("[XV_Rule] score map 超界[0,1]跳过 %s=%r", k, v)
    return injected
def _findings_self_assessed_max(data) -> float | None:
    raw_confs = []
    for _f in dict_findings(data.get("findings")):
        if is_status_message_finding(_f) or is_default_confidence(_f):
            continue
        _c = _numeric_confidence(_f)
        if _c is None:
            continue
        if signal_bool(_f.get("_partial_degrade")):
            _c = _c * degrade_factor_of(_f)
        raw_confs.append(_c)
    if raw_confs:
        return clamp_unit(max(raw_confs))
    return None
def _normalized_source_score(record: dict) -> float:
    for score_key in ("score", "health_score", "quality_score", "coverage"):
        raw = record.get(score_key)
        if raw is None:
            continue
        score = safe_float(raw, None)
        if score is None or score < 0:
            continue
        if score_key == "coverage" and 0 < score <= 1:
            score *= 100
        return score
    return 0
def _source_record(ir: dict, source) -> dict:
    record = safe_dict_get(ir, source, None)
    if isinstance(record, dict):
        return record
    main = source_main_id(source)
    if main and main != source:
        record = safe_dict_get(ir, main, None)
        if isinstance(record, dict):
            return record
    return {}
def _avg_independent_score(sources, independent_results) -> float:
    ir = independent_results if isinstance(independent_results, dict) else {}
    source_scores = [_normalized_source_score(_source_record(ir, s))
                     for s in clean_source_ids(normalize_sources(sources))]
    return sum(source_scores) / len(source_scores) if source_scores else 0
_SCORE_TIER_TABLE: tuple[tuple[int, str, float], ...] = (
    (90, "90", 0.85),
    (70, "70", 0.65),
    (50, "50", 0.45),
    (30, "30", 0.30),
)
_DEFAULT_SCORE_FLOOR = 0.20
def _map_avg_score_to_base(avg_score) -> float:
    _injected = _env_score_map()
    if _injected is None:
        return 0.5
    for _threshold, _key, _default in _SCORE_TIER_TABLE:
        if avg_score >= _threshold:
            return _injected.get(_key, _default)
    return _injected.get("0", _DEFAULT_SCORE_FLOOR)
def compute_base_confidence(data, sources, independent_results):
    data = _coerce_entry(data)
    sources = normalize_sources(sources)
    _self_max = _findings_self_assessed_max(data)
    if _self_max is not None:
        return _self_max
    avg_score = _avg_independent_score(sources, independent_results)
    return _map_avg_score_to_base(avg_score)
def _dominant_family_fp_coefficient(findings) -> float | None:
    try:
        _rf_list = [family for f in findings if isinstance(f, dict)
                    and not is_status_message_finding(f)
                    and (family := _finding_family(f))]
        _rf = max(sorted(set(_rf_list)), key=_rf_list.count) if _rf_list else ""
        if _rf and _rf in RULE_FP_TRACKER:
            record = RULE_FP_TRACKER[_rf]
            if not isinstance(record, dict):
                return None
            fp_rate = record.get("fp_rate", FP_RATE_LOW)
            if not is_real_number(fp_rate) or not 0.0 <= fp_rate <= 1.0:
                return None
            return _fp_coefficient_for_rate(fp_rate)
    except Exception as e:  # noqa: BLE001
        logger.warning("[XV_Rule] 置信度计算失败,安全回退: %s", e)
        return None
    return _FP_COEFF_MEDIUM
def _fp_coefficient_for_rate(fp_rate: float) -> float:
    if fp_rate <= FP_RATE_VERY_LOW:
        return _FP_COEFF_STRONG
    if fp_rate <= FP_RATE_MEDIUM:
        return _FP_COEFF_MEDIUM
    return CONF_LOW
def _multi_source_family_bonus(sources) -> float:
    _fam_count = len(source_family_names(sources))
    if _fam_count <= 1:
        return 0.0
    if _fam_count == 2:
        return 0.03
    if _fam_count == 3:
        return 0.06
    return CONF_BOOST_STEP
def compute_adjusted_confidence(data, sources, base, strength, boost):
    data = _coerce_entry(data)
    sources = normalize_sources(sources)
    _strength_coeff = _dominant_family_fp_coefficient(data.get("findings", []))
    if _strength_coeff is None:
        return safe_confidence(base + strength * 0.3 + boost, base)
    strength_contrib = (1.0 - base) * strength * _strength_coeff
    multi_source_bonus = _multi_source_family_bonus(sources)
    _result = base + strength_contrib + multi_source_bonus + boost
    return safe_confidence(_result, base)
def conclusion_params_of(rule, sources, strength, base, boost, adjusted) -> dict:
    return {
        "base_conf": round(base, 3),
        "strength": round(strength, 3),
        "source_count": len(sources),
        "rule_id": rule,
        "boost": round(boost, 3),
        "adjusted_conf": round(adjusted, 3),
        "rule_weight": round(get_rule_weight(rule), 3),
        "calibrated_confidence": round(adjusted, 3),
    }
def prepare_locator_entry(locator: str, entry: dict):
    if not isinstance(entry, dict):
        logger.warning(
            "[Rules] 非法 entry 类型(%s)，locator=%s 降级为 uncertain 占位（不丢弃）",
            type(entry).__name__, locator,
        )
        return (
            build_skipped_placeholder(
                locator, entry, f"invalid_entry_type:{type(entry).__name__}"),
            {"rules_executed": set(), "skipped_invalid_entry": 1},
        )
    _pl_clean_entry_findings(locator, entry)
    sources = _pl_clean_entry_sources(locator, entry)
    base_conf = entry.get("max_confidence", 0.0)
    if not is_real_number(base_conf):
        logger.warning(
            "[Rules] locator=%s max_confidence 为非数值形态(%s)，归一 0.0",
            locator, type(base_conf).__name__,
        )
        base_conf = 0.0
        entry["max_confidence"] = 0.0
    base_conf = calibrate_base_by_source_fp(base_conf, entry.get("rule_families", []))
    _deg_factors = partial_deg_factors_map(entry.get("findings", []))
    _method_rf_map = _pl_collect_method_rf_map(entry)
    strength = evidence_strength_by_rule_family(
        _method_rf_map, sources, _deg_factors if _deg_factors else None
    )
    return {
        "sources": sources,
        "base_conf": base_conf,
        "strength": strength,
    }
def _pl_clean_entry_findings(locator: str, entry: dict) -> None:
    _missing = object()
    _raw_findings = entry.get("findings", _missing)
    if _raw_findings is _missing:
        return
    if isinstance(_raw_findings, (list, tuple)):
        _clean_findings = [f for f in _raw_findings if isinstance(f, dict)]
        if len(_clean_findings) != len(_raw_findings):
            logger.warning(
                "[Rules] locator=%s findings 含 %d 个非 dict 元素，已过滤",
                locator, len(_raw_findings) - len(_clean_findings),
            )
            entry["findings"] = _clean_findings
        elif isinstance(_raw_findings, tuple):
            entry["findings"] = _clean_findings
        return
    _materialized = [f for f in strict_iterable_list(_raw_findings)
                     if isinstance(f, dict)]
    if _materialized:
        logger.debug(
            "[Rules] locator=%s findings 载体非序列(%s)，已物化 %d 条",
            locator, type(_raw_findings).__name__, len(_materialized),
        )
        entry["findings"] = _materialized
        return
    logger.warning(
        "[Rules] locator=%s findings 为不可用形态(%s)，归一为空列表",
        locator, type(_raw_findings).__name__,
    )
    entry["findings"] = []
def _pl_clean_entry_sources(locator: str, entry: dict) -> list:
    _missing_sources = object()
    sources = entry.get("sources", _missing_sources)
    if sources is _missing_sources:
        return []
    if not isinstance(sources, SOURCE_SEQUENCE_TYPES):
        _materialized_sources = normalize_sources(sources)
        if not _materialized_sources:
            logger.warning(
                "[Rules] locator=%s sources 为不可用形态(%s)，归一为空列表",
                locator, type(sources).__name__,
            )
            entry["sources"] = []
            return []
        logger.debug(
            "[Rules] locator=%s sources 载体非序列(%s)，已物化为列表",
            locator, type(sources).__name__,
        )
        sources = _materialized_sources
    clean_sources = clean_source_ids(sources)
    if len(clean_sources) != len(sources):
        logger.warning(
            "[Rules] locator=%s sources 含 %d 个无效或重复来源 ID，已过滤",
            locator, len(sources) - len(clean_sources),
        )
    entry["sources"] = clean_sources
    return clean_sources
def _pl_collect_method_rf_map(entry: dict) -> dict:
    findings = dict_findings(_coerce_entry(entry).get("findings"))
    _hashable: list = []
    for _f in findings:
        try:
            hash(_f.get("_source_method"))
        except TypeError:
            logger.debug(
                "[Rules] 方法→家族映射跳过（_source_method 不可哈希）: %r",
                _f.get("_source_method"))
            continue
        _hashable.append(_f)
    _method_rf_map = dict(dominant_rule_family_by_method(_hashable))
    for _f in _hashable:
        _m = _f.get("_source_method")
        _rf = _finding_family(_f)
        if _m and _rf and _m not in _method_rf_map:
            _method_rf_map[_m] = _rf
    return _method_rf_map
def build_skipped_placeholder(locator: str, entry: dict, reason: str) -> dict:
    _entry = entry if isinstance(entry, dict) else {}
    _srcs = clean_source_ids(normalize_sources(_entry.get("sources")))
    return {
        "locator": locator,
        "rule_id": "规则14",
        "conclusion": "uncertain",
        "conclusion_v2": "uncertain",
        "confidence": 0.0,
        "base": 0.0,
        "boost": 0,
        "strength": "degraded",
        "sources": _srcs,
        "source_count": len(_srcs),
        "message": f"[CV-SKIP] 规则匹配基础设施异常，降级为 uncertain 待人工复核: {reason}",
        "skipped_reason": reason,
        "_cv_skipped_placeholder": True,
    }
def build_finding(
    locator: str, data: dict, rule: str,
    conclusion: str, base: float | None = None, adjusted: float | None = None,
    boost: float = 0.0,
    independent_results: dict | None = None,
    strength: float | None = None,
) -> dict:
    data, sources, full_sources, partial_sources = normalize_finding_input(data)
    sources = clean_source_ids(sources)
    full_sources = [source for source in sources if source not in partial_sources]
    strength = compute_finding_strength(data, sources, full_sources, partial_sources, strength)
    if base is None:
        base = compute_base_confidence(data, sources, independent_results)
    base = normalized_confidence(base)
    boost = clamp_unit(safe_float(boost, 0.0))
    if adjusted is None:
        adjusted = compute_adjusted_confidence(data, sources, base, strength, boost)
    adjusted = normalized_confidence(adjusted, base)
    _calibrated = calibrate_confidence(rule, adjusted)
    if _calibrated != adjusted:
        adjusted = _calibrated
    families_sorted, ev_type_str = evidence_meta(sources)
    _raw_findings = dict_findings(data.get("findings", []))
    _shadow_findings = dict_findings(data.get("_shadow_findings", []))
    result = {
        "locator": locator,
        "rule_applied": rule,
        "conclusion": conclusion,
        "_conclusion_params": conclusion_params_of(
            rule, sources, strength, base, boost, adjusted),
        "sources": sorted(sources, key=str),
        "source_count": len(sources),
        FIELD_EVIDENCE_FAMILIES: families_sorted,
        "evidence_type": ev_type_str,
        FIELD_EVIDENCE_STRENGTH: round(strength, 2),
        FIELD_BASE_CONFIDENCE: round(base, 2),
        FIELD_ADJUSTED_CONFIDENCE: round(adjusted, 2),
        "findings": _raw_findings,
        "findings_count": len(_raw_findings),
        "sample_finding": summarize_findings(_raw_findings),
        "timestamp": timestamp_ms(),
    }
    if _shadow_findings:
        result["_shadow_findings"] = _shadow_findings
    propagate_finding_metadata(result, data, sources)
    if partial_sources:
        result[SIGNAL_PARTIAL_SOURCES] = sorted(partial_sources, key=str)
        result["_full_sources"] = sorted(full_sources, key=str)
        result["_has_partial_evidence"] = True
    return result
_STYLE_FAMILY_PREFIXES = ("SIM", "UP", "PIE", "NPY", "PERF1", "PERF2",
                          "PERF3", "PERF4", "RUF", "PLR", "PLW", "COM",
                          "T20")
_STYLE_EXACT_CODES = frozenset({"I001", "E501", "C901", "F401", "B009", "B010"})
STYLE_RULE_PREFIXES = _STYLE_FAMILY_PREFIXES + tuple(sorted(_STYLE_EXACT_CODES))
_RUFF_RULE_NAMESPACE = "RUFF-"
def style_rule_code(rule_id: str) -> str:
    text = rule_id.strip() if isinstance(rule_id, str) else str(rule_id)
    if text.startswith(_RUFF_RULE_NAMESPACE):
        return text[len(_RUFF_RULE_NAMESPACE):].strip()
    return text
def _style_code_is_style(rule_id: str) -> bool:
    if rule_id in _STYLE_EXACT_CODES:
        return True
    return any(
        rule_id.startswith(prefix)
        and rule_id[len(prefix):].isascii()
        and rule_id[len(prefix):].isdigit()
        for prefix in _STYLE_FAMILY_PREFIXES
    )
def _pl_style_demote_applies(entry: dict) -> bool:
    rows = [
        f for f in dict_findings(_coerce_entry(entry).get("findings"))
        if not is_status_message_finding(f)
    ]
    if not rows:
        return False
    for finding in rows:
        rule_id = style_rule_code(str(finding.get("rule_id", "")))
        if not rule_id or not _style_code_is_style(rule_id):
            return False
    return True
def _has_adjustment_prefix(adj_log: list, prefix: str) -> bool:
    return any(
        isinstance(_a, str) and _a.startswith(prefix) for _a in adj_log)
def _pl_attach_annotation_metadata(xv_result: dict, adj_log: list) -> None:
    if adj_log:
        xv_result["_annotation_adjustments"] = adj_log
        if _has_adjustment_prefix(adj_log, "arbiter_demoted:"):
            xv_result["_arbiter_demoted"] = True
        if _has_adjustment_prefix(adj_log, "arbiter_upgraded:suppressed->"):
            xv_result["_preserved_from_suppressed"] = True
def _pl_style_demote(xv_result: dict, entry: dict,
                     conclusion: str) -> tuple[str, str]:
    if conclusion not in ("confirmed", "likely"):
        return conclusion, ""
    if not _pl_style_demote_applies(entry):
        return conclusion, ""
    _demoted = "investigated"
    xv_result["conclusion"] = _demoted
    _sev_rank = SEVERITY_RANK.get(
        str(xv_result.get("severity", "")).strip().upper(), 3)
    if _sev_rank <= 2:
        xv_result["severity"] = "P3"
    return _demoted, (
        "style_only_demote: 全风格/格式类finding不得保留"
        "confirmed,降级investigated")
def _pl_attach_rule_ledger(xv_result: dict, dec: PlDecision) -> None:
    if dec.secondary_rules:
        xv_result["_secondary_rules"] = dec.secondary_rules
        xv_result["_multi_rule_boost"] = round(dec.multi_rule_boost, 3)
        xv_result["_all_matched_rules"] = sorted(dec.all_matched)
    xv_result["_rule_matched"] = dec.rule_matched
    xv_result["_rule_check_executed"] = dec.check_fn is not None
    if dec.degraded_info:
        xv_result["_is_degraded"] = True
        xv_result["_degraded_raw_rule"] = dec.degraded_info.get("raw_rule", "")
        xv_result["_degraded_reason"] = dec.degraded_info.get("reason", "")
    else:
        xv_result["_is_degraded"] = False
def _pl_attach_selection_trace(xv_result: dict, dec: PlDecision,
                               style_demote_reason: str,
                               safety_valve_override: str) -> None:
    conclusion_params = xv_result.get("_conclusion_params")
    if not isinstance(conclusion_params, dict):
        return
    conclusion_params["rule_selection_reason"] = dec.selection_trace
    if style_demote_reason:
        conclusion_params["style_demote_reason"] = style_demote_reason
    if safety_valve_override:
        conclusion_params["safety_valve_override"] = safety_valve_override
def _pl_attach_independent_source_count(xv_result: dict, entry: dict, sources: list) -> None:
    xv_result["_independent_source_count"] = len(
        pl_independent_sources(entry, sources))
_RETIRED_RULE_SUPPRESSION: dict[str, int] = {}
def retired_suppression_stats() -> dict[str, int]:
    """退休规则被跳过的累计次数（观测用：确认退休规则确实不再产出）。"""
    return dict(_RETIRED_RULE_SUPPRESSION)
def assemble_xv_result(cv2, locator: str, entry: dict, sources: list,
                       dec: PlDecision, rule4: PlRule4) -> dict | None:
    dec = _coerce_decision(dec)
    _conclusion = rule4.conclusion
    if _conclusion == "confirmed" and is_rule_retired(dec.rule_id):
        # 退休规则直接不产出 finding：``suggestion`` 是
        # ``SOFT_CLOSURE_BANNED_STATUSES`` 里的禁用软销项，产出来会让
        # ``check_zero_residual`` 永久阻断交付（死锁），而退休规则本身是噪声、
        # 没有修复器可走真实修复。可见性由 ``retired_rule_ids()`` 与
        # ``retired_suppression_stats()`` 保证。
        _rid = str(dec.rule_id or "").strip() or "<unknown>"
        _RETIRED_RULE_SUPPRESSION[_rid] = (
            _RETIRED_RULE_SUPPRESSION.get(_rid, 0) + 1)
        logger.info(
            "[XV_Rule] 规则 %s 处于退休态，跳过产出（locator=%s，累计 %d 次）",
            _rid, locator, _RETIRED_RULE_SUPPRESSION[_rid])
        return None
    xv_result = build_finding(
        locator=locator,
        data=entry,
        rule=dec.rule_id,
        conclusion=_conclusion,
        base=dec.base_conf,
        boost=dec.boost,
        independent_results=cv2.independent_results,
        strength=dec.strength,
    )
    _, style_override = _pl_style_demote(
        xv_result, entry, _conclusion)
    if rule4.rule4_suppression_applied:
        xv_result["_suppression_rule"] = "规则4"
    _pl_attach_independent_source_count(xv_result, entry, sources)
    _pl_attach_rule_ledger(xv_result, dec)
    _pl_attach_annotation_metadata(xv_result, dec.adj_log)
    _pl_attach_selection_trace(
        xv_result, dec, style_override, rule4.safety_valve_override)
    return xv_result

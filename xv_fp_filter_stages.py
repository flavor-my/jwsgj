from __future__ import annotations

import logging
import os
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Any

from jwsgj.diag_types_defs import dict_findings
from jwsgj.diag_types_normalize import (
    finding_file_key,
    finding_file_path,
    finding_rule_family,
    finite_float_or_zero,
    is_real_number,
    normalize_severity_rank,
    parse_locator_file,
    parse_locator_line,
    safe_finding_line,
)
from jwsgj.diag_types_vocab import (
    AUTO_THRESHOLD_DECAY,
    CONF_FLOOR,
    CONF_HIGH,
    CONF_LOW,
    CONF_MEDIUM,
    DEFAULT_CONFIDENCE_FALLBACK,
    PROJECT_ROOT_MARKERS,
    SIGNAL_BASELINE_PERSISTENT_NOISE,
    SIGNAL_ENSEMBLE_LOW_CONFIDENCE,
    SIGNAL_MUTATION_CONFIRMED_DEAD,
    SIGNAL_MUTATION_VERIFIED,
    SIGNAL_REFDEPTH_ISOLATED,
    SIGNAL_STAGE1_FP_CANDIDATE,
    SIGNAL_STATS_DRIVEN_CANDIDATE,
)
from jwsgj.fix_guide_rule_identity import (
    CONFLICTING_PAIRS,
    FILE_LEVEL_FAMILIES,
    KNOWN_HIGH_FP_FAMILIES,
    get_rule_family_set,
    is_family_member,
    matches_rule_family,
    normalize_rule,
)
from jwsgj.fp_rules_judge import (
    DEFAULT_SEVERITY,
    SUPPRESSION_DEFAULT_MIN_SEVERITY,
    SelfAuditAwareness,
    get_fp_rule_ids,
    load_cv_fp_suppression_rules,
    load_cv_fp_tracker_rates,
    load_fp_rules,
)
from jwsgj.xv_evidence_strength import (
    count_independent_sources,
)
from jwsgj.xv_findings_core import (
    _effective_conclusion,
    _index_file_identity,
)

logger = logging.getLogger(__name__)
__all__ = [
    'FP_FILTER_WHITELIST',
    'SHADOW_EVIDENCE_MARKER',
    'censor_fp_family',
    'check_individual_fp_signals',
    'check_p0p1_fp_signals',
    'count_p2_fp_signals',
    'ensure_deferred_queue',
    'filter_false_positives',
    'load_fp_filter_state',
    'norm_source_method',
    'passes_fp_filter',
    'post_annotation_fp_filter',
    'reinject_deferred_as_shadow',
    'rescue_deferred_findings',
]
def _is_target_project_root(path: str) -> bool:
    if not path or not os.path.isdir(path):
        return False
    return any(os.path.exists(os.path.join(path, marker))
               for marker in PROJECT_ROOT_MARKERS)
def _marked_project_root(candidates) -> str:
    for candidate in candidates:
        if _is_target_project_root(candidate):
            return candidate
    return ""
def _ladder_skill_root(mid: str) -> str:
    _ladder = (
        os.path.dirname(mid),
        os.path.dirname(os.path.dirname(mid)),
        os.path.dirname(os.path.dirname(os.path.dirname(mid))),
    )
    return _marked_project_root(_ladder)
def _source_dir_from_results(cv2) -> str:
    _ir = getattr(cv2, "independent_results", None)
    for result in (_ir.values() if isinstance(_ir, dict) else ()):
        if not isinstance(result, dict):
            continue
        src = result.get("_source", "")
        if src and isinstance(src, str):
            base = os.path.dirname(src)
            candidates = (
                base,
                os.path.dirname(base),
                os.path.dirname(os.path.dirname(base)),
                os.path.dirname(os.path.dirname(os.path.dirname(base))),
            )
            resolved = _marked_project_root(candidates)
            if resolved:
                return resolved
    return ""
def _resolve_fp_skill_dir(cv2) -> str:
    sd = getattr(cv2, "skill_dir", "")
    if sd and os.path.isdir(sd):
        return sd
    mid = getattr(cv2, "_intermediate_dir", "")
    if mid:
        _cand = _ladder_skill_root(mid)
        if _cand:
            return _cand
    return _source_dir_from_results(cv2)
def _load_fp_rule_stores(cv2: Any, skill_dir: str) -> None:
    try:
        cv2._fp_rule_ids = get_fp_rule_ids(skill_dir) if skill_dir else set()
    except Exception as _e:  # noqa: BLE001
        logger.warning("[XV-FP] 策略11规则库加载降级: %s", _e)
        cv2._fp_rule_ids = set()
    try:
        _rules = (load_fp_rules(skill_dir) if skill_dir else {}).get("rules", {})
        cv2._fp_rules_meta = _rules if isinstance(_rules, dict) else {}
    except Exception as _e:  # noqa: BLE001
        logger.warning("[XV-FP] 策略13规则元数据加载降级: %s", _e)
        cv2._fp_rules_meta = {}
    cv2._fp_tracker_rates = load_cv_fp_tracker_rates(skill_dir)
    cv2._fp_suppression_rules = load_cv_fp_suppression_rules(skill_dir)
def _activate_self_audit(
    cv2: Any, skill_dir: str,
) -> SelfAuditAwareness | None:
    _saa = None
    _saa_active = False
    try:
        if skill_dir:
            _saa = SelfAuditAwareness(skill_dir)
            if _saa.is_self_audit:
                _saa_active = True
                logger.info("[XV-FP] 策略12(自审感知)激活: 检测到自审上下文")
            else:
                logger.warning("[XV-FP] 策略12(自审感知)未激活: is_self_audit=False, skill_dir=%s", skill_dir)
        else:
            logger.warning("[XV-FP] 策略12(自审感知)未激活: skill_dir解析失败")
    except Exception as _e:  # noqa: BLE001
        logger.warning("[XV-FP] 策略12自审感知加载降级: %s", _e)
    cv2._self_audit_applied = _saa_active
    return _saa if _saa_active else None
def load_fp_filter_state(cv2: Any) -> SelfAuditAwareness | None:
    skill_dir = _resolve_fp_skill_dir(cv2)
    _load_fp_rule_stores(cv2, skill_dir=skill_dir)
    _saa = _activate_self_audit(cv2, skill_dir=skill_dir)
    cv2._fp_censored_families = Counter()
    return _saa
def _rule_store_dict(cv2: Any, attr: str) -> dict:
    raw = getattr(cv2, attr, None)
    return raw if isinstance(raw, dict) else {}
def _rule_id_store(cv2: Any):
    raw = getattr(cv2, "_fp_rule_ids", None)
    if isinstance(raw, (set, frozenset, list, tuple)):
        return raw
    return frozenset()
def _suppression_store(cv2: Any) -> list:
    raw = getattr(cv2, "_fp_suppression_rules", None)
    if isinstance(raw, list):
        return raw
    return list(raw) if isinstance(raw, tuple) else []
FP_FILTER_WHITELIST = {
    "security_critical": {
        "families": get_rule_family_set("security") | get_rule_family_set("security_extended"),
        "max_sev_rank": 3,
    },
    "syntax_error": {
        "families": get_rule_family_set("syntax_runtime"),
        "max_sev_rank": 3,
    },
    "resource_leak": {
        "families": get_rule_family_set("resource_leak") | {"handle_leak"},
        "max_sev_rank": 2,
    },
    "concurrency": {
        "families": get_rule_family_set("concurrency"),
        "max_sev_rank": 2,
    },
}
def _check_whitelist_protection(finding: dict) -> tuple:
    rule_family = finding_rule_family(finding)
    sev_rank_val = normalize_severity_rank(
        finding.get("severity", DEFAULT_SEVERITY))
    for category, config in FP_FILTER_WHITELIST.items():
        if (is_family_member(rule_family, config["families"])
                and sev_rank_val <= config["max_sev_rank"]):
            return True, category
    return False, ""
def censor_fp_family(cv2, f: dict) -> None:
    try:
        counter = getattr(cv2, "_fp_censored_families", None)
        if counter is None:
            return
        fam = finding_rule_family(f)
        if fam:
            if counter.get(fam) is None:
                counter[fam] = 0
            counter[fam] += 1
    except Exception as e:  # noqa: BLE001
        logger.debug("[fp_filter] 删失计数失败（不阻断主流程）: %s: %s",
                     type(e).__name__, e)
def _patterns_hit(patterns, text: str) -> bool:
    if not isinstance(patterns, (list, tuple)):
        return False
    if not patterns:
        return True
    return any(_p in text for _p in patterns
               if isinstance(_p, str) and _p)
def _match_suppression_rule(f: dict, suppression_rules: list, rid: str) -> dict | None:
    _sev_rank = normalize_severity_rank(
        str(f.get("severity", DEFAULT_SEVERITY)))
    if _sev_rank <= 1:
        return None
    _msg = str(f.get("message", ""))
    _file = finding_file_path(f)
    for _sp_rule in suppression_rules:
        if not isinstance(_sp_rule, dict):
            continue
        _sp_rid = _sp_rule.get("rule_id", "")
        if not _sp_rid or _sp_rid != rid:
            continue
        _sp_min_sev = _sp_rule.get(
            "min_severity_to_suppress", SUPPRESSION_DEFAULT_MIN_SEVERITY)
        if _sev_rank < normalize_severity_rank(_sp_min_sev):
            continue
        if not _patterns_hit(_sp_rule.get("message_patterns", []), _msg):
            continue
        if not _patterns_hit(_sp_rule.get("file_patterns", []), _file):
            continue
        return _sp_rule
    return None
def _suppression_hit_reason(sp_rule: dict, *, multi_source: bool) -> str:
    _sp_rid = sp_rule.get("rule_id", "")
    _sp_min_sev = sp_rule.get(
        "min_severity_to_suppress", SUPPRESSION_DEFAULT_MIN_SEVERITY)
    tag = "多源不豁免," if multi_source else ""
    return f"策略16:模式抑制({tag}rule={_sp_rid},sev>={_sp_min_sev})"
def _policy7_known_fp_family(f: dict, rule_family: str, sev: str,
                             whitelist_protected: bool,
                             is_high_severity: bool) -> None:
    if not is_family_member(rule_family, KNOWN_HIGH_FP_FAMILIES):
        return
    if is_high_severity:
        f["_known_fp_family_high_sev"] = True
    if whitelist_protected or f.get("_multi_source_confirmed", False):
        return
    _sev_rank7 = normalize_severity_rank(sev)
    if _sev_rank7 >= 3:
        f[SIGNAL_STAGE1_FP_CANDIDATE] = f"策略7:已知误报规则族({rule_family})"
    elif _sev_rank7 == 2:
        conf_val = f.get("confidence", DEFAULT_CONFIDENCE_FALLBACK)
        if not (is_real_number(conf_val) and conf_val >= CONF_MEDIUM):
            f[SIGNAL_STAGE1_FP_CANDIDATE] = f"策略7:已知误报规则族P2低置信度({rule_family})"
def _mark_multisource_review(f: dict, reason: str) -> None:
    f["_review_required"] = True
    f["_review_reason"] = reason
def _multi_source_exempt(f: dict) -> bool:
    if not f.get("_multi_source_confirmed"):
        return False
    _mark_multisource_review(f, "FP过滤多源豁免: 交由规则14(多源确认)仲裁")
    return True
@dataclass(frozen=True)
class _FindingCtx:
    f: dict
    line: int
    sev_upper: str
    sev_rank: int
    is_high_severity: bool
    whitelist_protected: bool
    conf: object
    conf_is_real: bool
    rid: str
    rule_family: str
def _severity_parts(f: dict) -> tuple[str, int]:
    raw = f.get("severity", DEFAULT_SEVERITY)
    sev_upper = raw.strip().upper() if isinstance(raw, str) else "UNKNOWN"
    return sev_upper, normalize_severity_rank(sev_upper)
def _build_finding_ctx(f: dict) -> _FindingCtx:
    sev_upper, sev_rank = _severity_parts(f)
    rid = _norm_batch_key(f.get("rule_id", ""))
    rule_family = finding_rule_family(f)
    _whitelist_protected, _whitelist_category = _check_whitelist_protection(f)
    if _whitelist_protected:
        logger.debug(
            "[FP-Whitelist] %s 保护(策略2/3/7): %s (sev=%s)",
            _whitelist_category, rule_family, sev_upper
        )
    conf = f.get("confidence", DEFAULT_CONFIDENCE_FALLBACK)
    return _FindingCtx(
        f=f,
        line=safe_finding_line(f),
        sev_upper=sev_upper,
        sev_rank=sev_rank,
        is_high_severity=sev_rank <= 1,
        whitelist_protected=_whitelist_protected,
        conf=conf,
        conf_is_real=is_real_number(conf),
        rid=rid,
        rule_family=rule_family,
    )
def _fp_ghost_line_filter(ctx: _FindingCtx) -> str | None:
    if ctx.line > 0:
        return None
    if ctx.sev_rank < 3:
        return None
    if (not is_family_member(ctx.rule_family, FILE_LEVEL_FAMILIES)
            and not _multi_source_exempt(ctx.f)):
        return "策略1:零行号幽灵finding(低严重度P3/P4)"
    return None
def _fp_low_confidence_filter(ctx: _FindingCtx) -> str | None:
    if not (ctx.conf_is_real and ctx.conf < CONF_FLOOR):
        return None
    if ctx.sev_rank >= 4:
        return None
    if ctx.is_high_severity:
        ctx.f["_low_confidence_high_severity"] = True
        return None
    if not ctx.whitelist_protected and not _multi_source_exempt(ctx.f):
        return "策略2:置信度过低(<0.30)"
    return None
def _fp_empty_message_filter(ctx: _FindingCtx) -> str | None:
    msg = str(ctx.f.get("message", "")).strip()
    if msg and msg.lower() not in ("-", "none", "unknown", "n/a"):
        return None
    if (not ctx.is_high_severity and not ctx.whitelist_protected
            and not _multi_source_exempt(ctx.f)):
        return "策略3:空message"
    ctx.f["message"] = f"[自动补充] {ctx.sev_upper} 级发现（原始消息缺失）"
    return None
def _fp_source_method_filter(ctx: _FindingCtx) -> str | None:
    src = norm_source_method(ctx.f.get("_source_method", ""))
    if src and src.lower() != "unknown":
        return None
    if ctx.is_high_severity:
        ctx.f["_review_required"] = True
        ctx.f["_review_reason"] = "P0/P1 source method missing"
        return None
    return "策略4:源方法缺失(P2/P3/P4)"
def _fp_internal_path_filter(ctx: _FindingCtx) -> str | None:
    filepath = finding_file_path(ctx.f)
    _segs = [s.lower() for s in filepath.replace("\\", "/").split("/") if s]
    _seg_set = set(_segs)
    if (_seg_set & {"__pycache__", "site-packages", "node_modules"}) \
            or any(s.endswith(".git") for s in _segs):
        return "策略5:内部路径"
    if "_intermediate" in _seg_set or "_cache" in _seg_set:
        return "策略6:中间文件路径"
    return None
def _fp_p4_low_confidence_filter(ctx: _FindingCtx) -> str | None:
    if (ctx.sev_rank >= 4 and ctx.conf_is_real and ctx.conf < CONF_FLOOR
            and not _multi_source_exempt(ctx.f)):
        return "策略8:P4严重度且低置信度"
    return None
def _is_batch_summary_rule(rule_id: str) -> bool:
    folded = rule_id.upper()
    return folded.endswith(("-BATCH", "_BATCH"))
def _fp_info_aggregate_filter(ctx: _FindingCtx) -> str | None:
    if _is_batch_summary_rule(ctx.rid) and ctx.sev_rank >= 3:
        return f"策略9:{ctx.rid}批量汇总(信息性)"
    _extra_raw = ctx.f.get("extra", {})
    extra = _extra_raw if isinstance(_extra_raw, dict) else {}
    if extra.get("aggregated") is True:
        return "策略10:聚合型finding(非个体)"
    return None
def _fp_dynamic_rule_filter(cv2, ctx: _FindingCtx) -> str | None:
    if not ctx.rid or ctx.line > 0:
        return None
    if (ctx.sev_rank > 1
            and ctx.rid in _rule_id_store(cv2)):
        return "策略11:动态固化误报规则(line=0)"
    return None
def _suppression_hit(cv2, ctx: _FindingCtx, *,
                     multi_source: bool = False) -> str | None:
    _suppression_rules = _suppression_store(cv2)
    if not (_suppression_rules and ctx.rid):
        return None
    _sp_rule = _match_suppression_rule(ctx.f, _suppression_rules, ctx.rid)
    if not _sp_rule:
        return None
    return _suppression_hit_reason(_sp_rule, multi_source=multi_source)
def _fp_multi_source_gate(cv2, ctx: _FindingCtx):
    if not ctx.f.get("_multi_source_confirmed"):
        return None
    _hit = _suppression_hit(cv2, ctx, multi_source=True)
    if _hit:
        return False, _hit
    _mark_multisource_review(
        ctx.f, "FP率过滤多源豁免: 交由规则14(多源确认)仲裁")
    return True, ""
def _stats_driven_hit(ctx: _FindingCtx, reason: str) -> str:
    ctx.f[SIGNAL_STATS_DRIVEN_CANDIDATE] = True
    return reason
_META_STATS_TIER_SPECS: tuple = (
    (100.0, 0.90, 2, "policy14", "p2_plus"),
    (20.0, 0.80, 3, "policy13", "p3_p4"),
)
_META_STATS_TIER_LABELS: dict[str, str] = {
    "policy13": "策略13:高频误报规则",
    "policy14": "策略14:极端高频误报规则",
}
_META_STATS_TIER_SUFFIXES: dict[str, str] = {
    "p3_p4": "P3/P4过滤",
    "p2_plus": "P2+过滤",
}
_FP_RATE_TIER_SPECS: tuple[tuple[float, float, int], ...] = (
    (0.95, 50.0, 2),
    (0.80, 20.0, 3),
)
def _fp_rate_tier(fp_rate: float, total: float,
                  sev_rank: int) -> int | None:
    for index, (min_rate, min_total, min_rank) in enumerate(
            _FP_RATE_TIER_SPECS):
        if (fp_rate >= min_rate and total >= min_total
                and sev_rank >= min_rank):
            return index
    return None
def _meta_stats_reason(count: float, confidence: float, fp_rate: float,
                       sev_rank: int) -> str | None:
    for min_count, min_conf, min_rank, policy, suffix_key in (
            _META_STATS_TIER_SPECS):
        if (count >= min_count and confidence >= min_conf
                and sev_rank >= min_rank):
            label = _META_STATS_TIER_LABELS[policy]
            suffix = _META_STATS_TIER_SUFFIXES[suffix_key]
            return (f"{label}(count={count},conf={confidence:.2f}){suffix}")
    if _fp_rate_tier(fp_rate, count, sev_rank) == 0:
        return f"策略14b:FP率驱动规则(fp_rate={fp_rate:.2f},count={count})P2+过滤"
    return None
def _fp_meta_stats_filter(cv2, ctx: _FindingCtx) -> str | None:
    if not ctx.rid:
        return None
    _rule_meta = _rule_store_dict(cv2, "_fp_rules_meta").get(ctx.rid, {})
    if not (_rule_meta and isinstance(_rule_meta, dict)):
        return None
    _reason = _meta_stats_reason(
        finite_float_or_zero(_rule_meta.get("count", 0)),
        finite_float_or_zero(_rule_meta.get("confidence", 0)),
        finite_float_or_zero(_rule_meta.get("fp_rate", 0)),
        ctx.sev_rank)
    return _stats_driven_hit(ctx, _reason) if _reason else None
_TRACKER_RATE_TIER_LABELS: tuple[str, ...] = (
    "策略15b:FP率驱动极端({label})P2+过滤",
    "策略15a:FP率驱动({label})P3/P4过滤",
)
def _tracker_rate_reason(fp_rate: float, total: float,
                         sev_rank: int) -> str | None:
    tier = _fp_rate_tier(fp_rate, total, sev_rank)
    if tier is None:
        return None
    return _TRACKER_RATE_TIER_LABELS[tier].format(
        label=f"fp_rate={fp_rate:.2f},total={total}")
def _fp_tracker_rate_filter(cv2, ctx: _FindingCtx) -> str | None:
    if not ctx.rid:
        return None
    _tracker_rates = _rule_store_dict(cv2, "_fp_tracker_rates")
    _tracker_entry = _tracker_rates.get(ctx.rid)
    if not _tracker_entry or not isinstance(_tracker_entry, dict):
        _tracker_entry = _tracker_rates.get(ctx.rule_family)
    if not (_tracker_entry and isinstance(_tracker_entry, dict)):
        return None
    _reason = _tracker_rate_reason(
        finite_float_or_zero(_tracker_entry.get("fp_rate", 0)),
        finite_float_or_zero(_tracker_entry.get("total", 0)),
        ctx.sev_rank)
    return _stats_driven_hit(ctx, _reason) if _reason else None
def _first_ctx_reason(ctx: _FindingCtx, *filters) -> str | None:
    for _filter in filters:
        reason = _filter(ctx)
        if reason:
            return reason
    return None
def _first_bound_reason(cv2, ctx: _FindingCtx, *filters) -> str | None:
    for _filter in filters:
        reason = _filter(cv2, ctx)
        if reason:
            return reason
    return None
def passes_fp_filter(cv2, f: dict) -> tuple[bool, str]:
    ctx = _build_finding_ctx(f)
    _reason = _first_ctx_reason(
        ctx, _fp_ghost_line_filter, _fp_low_confidence_filter,
        _fp_empty_message_filter, _fp_source_method_filter,
        _fp_internal_path_filter)
    if _reason:
        return False, _reason
    _policy7_known_fp_family(f, ctx.rule_family, ctx.sev_upper,
                             ctx.whitelist_protected, ctx.is_high_severity)
    _reason = _first_ctx_reason(
        ctx, _fp_p4_low_confidence_filter, _fp_info_aggregate_filter)
    if _reason:
        return False, _reason
    _reason = _fp_dynamic_rule_filter(cv2, ctx)
    if _reason:
        return False, _reason
    _ms_verdict = _fp_multi_source_gate(cv2, ctx)
    if _ms_verdict is not None:
        return _ms_verdict
    _reason = _first_bound_reason(
        cv2, ctx, _fp_meta_stats_filter, _fp_tracker_rate_filter,
        _suppression_hit)
    if _reason:
        return False, _reason
    return True, ""
def _conf_below(f, ceiling: float) -> bool:
    conf = f.get("confidence", DEFAULT_CONFIDENCE_FALLBACK)
    return is_real_number(conf) and conf < ceiling
def _mutation_refutes_finding(f) -> bool:
    return (bool(f.get(SIGNAL_MUTATION_VERIFIED))
            and not f.get(SIGNAL_MUTATION_CONFIRMED_DEAD)
            and not f.get("_mutation_inconclusive"))
def _mutation_inconclusive_dead_code(f) -> bool:
    return (bool(f.get("_mutation_inconclusive"))
            and matches_rule_family(finding_rule_family(f), "dead_code")
            and _conf_below(f, 0.35))
def _baseline_persistent_noise(f) -> bool:
    return (bool(f.get(SIGNAL_BASELINE_PERSISTENT_NOISE))
            and _conf_below(f, CONF_FLOOR))
def _ensemble_low_confidence(f) -> bool:
    return bool(f.get(SIGNAL_ENSEMBLE_LOW_CONFIDENCE)) and _conf_below(f, CONF_LOW)
def _refdepth_isolated(f) -> bool:
    return (bool(f.get(SIGNAL_REFDEPTH_ISOLATED))
            and _refdepth_family(finding_rule_family(f))
            and _conf_below(f, 0.50))
def _refdepth_family(rf) -> bool:
    return (matches_rule_family(rf, "dead_code")
            or matches_rule_family(rf, "unused_symbols"))
def check_p0p1_fp_signals(f) -> tuple:
    p0p1_strong_signals = sum((
        bool(f.get("_bizflow_fp_candidate")),
        _mutation_refutes_finding(f),
        bool(f.get("_arbiter_demoted")),
        bool(f.get(SIGNAL_ENSEMBLE_LOW_CONFIDENCE)
             and _conf_below(f, CONF_FLOOR)),
        _baseline_persistent_noise(f),
    ))
    if p0p1_strong_signals >= 3:
        return True, f"p0p1_multi_signal_fp({p0p1_strong_signals} signals)"
    return False, ""
def _mutation_refuted_dead_code(f) -> bool:
    return (_mutation_refutes_finding(f)
            and matches_rule_family(finding_rule_family(f), "dead_code"))
_INDIVIDUAL_FP_SIGNALS: tuple[tuple, ...] = (
    (lambda f: bool(f.get("_bizflow_fp_candidate")), "bizflow_fp_candidate"),
    (_baseline_persistent_noise, "baseline_persistent_noise+low_conf"),
    (_mutation_refuted_dead_code, "mutation_refuted_dead_code"),
    (_ensemble_low_confidence, "ensemble_low_confidence"),
    (_refdepth_isolated, "refdepth_isolated"),
    (lambda f: bool(f.get("_arbiter_demoted")), "arbiter_demoted"),
    (_mutation_inconclusive_dead_code, "mutation_inconclusive_low_conf"),
)
def check_individual_fp_signals(f) -> tuple:
    for _predicate, _reason in _INDIVIDUAL_FP_SIGNALS:
        if _predicate(f):
            return True, _reason
    return False, ""
def count_p2_fp_signals(f) -> int:
    independent_count = sum((
        _mutation_refutes_finding(f),
        bool(f.get(SIGNAL_STAGE1_FP_CANDIDATE)),
        _mutation_inconclusive_dead_code(f),
    ))
    _noise_group = bool(
        f.get("_bizflow_fp_candidate") or _baseline_persistent_noise(f))
    _isolation_group = bool(_ensemble_low_confidence(f) or _refdepth_isolated(f))
    _arbiter_group = bool(f.get("_arbiter_demoted"))
    return independent_count + _noise_group + _isolation_group + _arbiter_group
def norm_source_method(val: Any) -> Any:
    if not val:
        return val
    text = val if isinstance(val, str) else str(val)
    return text.strip()
def _known_source_method(val: Any) -> str:
    source = norm_source_method(val)
    if not source:
        return ""
    text = str(source)
    return "" if text.casefold() == "unknown" else text
def _locator_line_slot(line: int) -> str | int:
    return line if line > 0 else "FILE_LEVEL"
def _normalized_finding_family(f: dict) -> str:
    family = finding_rule_family(f).strip()
    return normalize_rule(family) if family else ""
def _finding_group_file_key(f: dict, cv2: Any = None) -> str:
    filepath = finding_file_path(f)
    return (_index_file_identity(cv2, filepath) if cv2 is not None
            else finding_file_key(filepath))
def _locator_group_key(f: dict, cv2: Any = None) -> str:
    _family = _normalized_finding_family(f)
    _slot = _locator_line_slot(safe_finding_line(f))
    return f"{_finding_group_file_key(f, cv2)}:{_slot}:{_family}"
def _index_locator_groups(findings: list, cv2: Any = None) -> tuple[dict, dict]:
    locator_groups = {}
    multi_source_map = {}
    for f in findings:
        if not isinstance(f, dict):
            continue
        if finding_rule_family(f) and _finding_group_file_key(f, cv2):
            key = _locator_group_key(f, cv2)
            locator_groups.setdefault(key, []).append(f)
            _sm = _known_source_method(f.get("_source_method", ""))
            if _sm:
                multi_source_map.setdefault(key, set()).add(_sm)
    return locator_groups, multi_source_map
def _build_family_partners() -> dict[str, set[str]]:
    family_partners: dict[str, set[str]] = {}
    for left_fs, right_fs, _ in CONFLICTING_PAIRS:
        for _lf in left_fs:
            family_partners.setdefault(_lf, set()).update(right_fs - {_lf})
        for _rf in right_fs:
            family_partners.setdefault(_rf, set()).update(left_fs - {_rf})
    return family_partners
def _build_fp_context(cv2: Any, findings: list) -> dict:
    locator_groups, multi_source_map = _index_locator_groups(findings, cv2)
    _mark_multi_source_flags(findings, multi_source_map, cv2)
    context = {
        "locator_groups": locator_groups,
        "multi_source_map": multi_source_map,
        "locator_family_keys": _index_locator_families(findings, cv2),
        "family_partners": {},
        "_cv2": cv2,
    }
    try:
        context["family_partners"] = _build_family_partners()
    except Exception:
        logger.warning("xv_fp_filter_stages: _build_fp_context CONFLICTING_PAIRS failed", exc_info=True)
        context["_fp_context_failed"] = True
    return context
def _index_locator_families(findings: list, cv2: Any = None) -> set:
    keys: set = set()
    if not isinstance(findings, list):
        return keys
    for f in findings:
        if not isinstance(f, dict):
            continue
        fam = finding_rule_family(f)
        if not fam:
            continue
        if not _finding_group_file_key(f, cv2):
            continue
        keys.add(_locator_group_key(f, cv2))
    return keys
def _contradiction_hit_at_locator(finding: dict, locator_keys: set,
                                  family_partners: dict,
                                  cv2: Any = None) -> bool:
    rf = finding_rule_family(finding)
    if not rf:
        return False
    partners = family_partners.get(normalize_rule(rf))
    if not partners or not locator_keys:
        return False
    f_file = _finding_group_file_key(finding, cv2)
    if not f_file:
        return False
    _slot = _locator_line_slot(safe_finding_line(finding))
    return any(f"{f_file}:{_slot}:{normalize_rule(p)}" in locator_keys
               for p in partners)
def _check_locator_confirm_signal(finding: dict, context: dict) -> bool:
    floc = _locator_group_key(finding, context.get("_cv2"))
    group = (context.get("locator_groups") or {}).get(floc, [finding])
    for gf in group:
        if gf is finding:
            continue
        if (gf.get("_ensemble_is_confirmed")
                or gf.get(SIGNAL_MUTATION_CONFIRMED_DEAD)):
            return True
    return False
def _log_fp_removal(filter_log: list, finding: dict, reason: str) -> None:
    filter_log.append({
        "file": finding_file_path(finding),
        "line": safe_finding_line(finding),
        "rule_id": _norm_batch_key(finding.get("rule_id")),
        "severity": str(finding.get("severity") or ""),
        "reason": reason,
        "confidence": finding.get("confidence"),
        "rule_family": finding_rule_family(finding),
        "message": str(finding.get("message") or "")[:300],
        "_source_method": finding.get("_source_method", ""),
        "locator": finding.get("locator", ""),
        "finding_id": finding.get("finding_id", ""),
        "source_count": len(finding["sources"]) if isinstance(finding.get("sources"), (list, tuple, set, frozenset)) else None,
        "category": finding.get("category", ""),
        "_partial_degrade": finding.get("_partial_degrade", False),
        "confidence_source": finding.get("_confidence_source", ""),
    })
def _mark_protected(f: dict, stage_name: str, filter_reason: str,
                    detail: str) -> None:
    f["_review_required"] = True
    f["_review_reason"] = f"FP filter {stage_name} skipped: {detail} ({filter_reason})"
    logger.debug("[FP-Filter-%s] %s，跳过过滤: %s",
                 stage_name, detail, _locator_group_key(f))
def _check_fp_protections(
    f: dict, ctx: dict, stage_name: str, filter_reason: str,
) -> bool:
    if _check_locator_confirm_signal(f, ctx):
        _mark_protected(f, stage_name, filter_reason,
                        "locator has confirm signal")
        return True
    if _contradiction_hit_at_locator(
            f, ctx.get("locator_family_keys") or set(),
            ctx.get("family_partners") or {}, ctx.get("_cv2")):
        f["_contradiction_participant"] = True
        _mark_protected(f, stage_name, filter_reason,
                        "contradiction participant")
        return True
    return False
def _norm_batch_key(val) -> str:
    if isinstance(val, str):
        return val
    if not val:
        return ""
    if isinstance(val, (list, tuple)):
        return _norm_batch_key(val[0])
    return str(val)
def _norm_src_rule(f: dict) -> tuple[str, str]:
    _src = f.get("_source_method", "")
    _rid = f.get("rule_id", "")
    return _norm_batch_key(_src), _norm_batch_key(_rid)
def _mark_batch_findings(findings: list[dict],
                         batch_threshold: int = 50) -> None:
    grouped: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for f in findings:
        if isinstance(f, dict):
            f.pop("_batch_source_rule", None)
            grouped[_norm_src_rule(f)].append(f)
    marked: dict[str, int] = {}
    for (src, rid), items in grouped.items():
        if len(items) > batch_threshold:
            marked[f"{src}:{rid}"] = len(items)
            for f in items:
                f["_batch_source_rule"] = True
    if marked:
        logger.info("[FP-Filter] 检测到批量同质finding: %s", marked)
def _postprocess_review_flags(filtered: list[dict]) -> None:
    for f in filtered:
        if not isinstance(f, dict) or not f.get("_known_fp_family_high_sev"):
            continue
        f["_review_required"] = True
        f["_review_reason"] = "P0/P1 finding from known false-positive family"
        if "_fp_confidence_decayed" in f or "confidence" not in f:
            continue
        orig_conf = f["confidence"]
        if not is_real_number(orig_conf):
            continue
        f["_fp_confidence_decayed"] = orig_conf
        f["confidence"] = max(
            0.0, min(1.0, float(orig_conf) * AUTO_THRESHOLD_DECAY))
def ensure_deferred_queue(cv2: Any) -> list:
    dq = getattr(cv2, "_fp_deferred", None)
    if isinstance(dq, list):
        return dq
    if dq:
        logger.warning("[FP-Filter] _fp_deferred 撕裂形态(%s)，重置为空队列",
                       type(dq).__name__)
    dq = cv2._fp_deferred = []
    return dq
def _mark_multi_source_confirmed(
        f: dict, multi_source_map: dict, cv2: Any = None) -> None:
    f["_multi_source_confirmed"] = False
    if not finding_rule_family(f):
        return
    src_set = (multi_source_map or {}).get(_locator_group_key(f, cv2), set())
    f["_multi_source_confirmed"] = (
        len(src_set) >= 2
        and count_independent_sources(sorted(src_set)) >= 2
    )
def _mark_multi_source_flags(
        findings, multi_source_map: dict, cv2: Any = None) -> None:
    for finding in (findings if isinstance(findings, list) else ()):
        if isinstance(finding, dict):
            _mark_multi_source_confirmed(finding, multi_source_map, cv2)
@dataclass
class _Stage1Pipeline:
    cv2: Any
    ctx: dict
    findings: list
    filtered: list
    pending_censor: list[dict]
def _count_saa_filtered(filter_log) -> int:
    total = 0
    for entry in filter_log:
        if not isinstance(entry, dict):
            continue
        if '策略12' in str(entry.get('reason') or ''):
            total += 1
    return total
def _enqueue_deferred(cv2: Any, f: dict) -> None:
    deferred = ensure_deferred_queue(cv2)
    if any(item is f for item in deferred):
        return
    deferred.append(f)
def _record_fp_deletion(cv2: Any, log_list: list, f: dict, reason: str,
                        stage: str | None = None) -> None:
    _log_fp_removal(log_list, f, reason)
    f.pop("_rescued", None)
    f.pop("_rescued_from", None)
    f["_fp_deferred_reason"] = reason
    if stage:
        f["_fp_deferred_stage"] = stage
    _enqueue_deferred(cv2, f)
def _stage1_remove_with_protection(f: dict, pipe: _Stage1Pipeline,
                                   protect_reason: str,
                                   defer_reason: str) -> None:
    if _check_fp_protections(f, pipe.ctx, "stage1", protect_reason):
        f.pop(SIGNAL_STATS_DRIVEN_CANDIDATE, None)
        pipe.filtered.append(f)
        return
    _record_fp_deletion(pipe.cv2, pipe.cv2._fp_filter_log, f, defer_reason)
    if f.pop(SIGNAL_STATS_DRIVEN_CANDIDATE, False):
        pipe.pending_censor.append(f)
_FP_ROLLBACK_MARKERS = (
    SIGNAL_STAGE1_FP_CANDIDATE,
    SIGNAL_STATS_DRIVEN_CANDIDATE,
    "_fp_deferred_reason",
    "_fp_deferred_stage",
    "_rescued",
    "_rescued_from",
    "message",
    "confidence",
    "_fp_confidence_decayed",
    "_review_required",
    "_review_reason",
    "_multi_source_confirmed",
    "_known_fp_family_high_sev",
    "_batch_source_rule",
    "_contradiction_participant",
    "_low_confidence_high_severity",
)
_FP_MARKER_MISSING = object()
def _snapshot_fp_markers(findings: list) -> dict[int, dict]:
    return {
        id(finding): {key: finding[key] for key in _FP_ROLLBACK_MARKERS
                      if key in finding}
        for finding in (findings if isinstance(findings, list) else [])
        if isinstance(finding, dict)
    }
def _restore_fp_markers(findings: list, snapshot: dict[int, dict]) -> None:
    for finding in findings:
        if not isinstance(finding, dict) or id(finding) not in snapshot:
            continue
        markers = snapshot[id(finding)]
        for key in _FP_ROLLBACK_MARKERS:
            value = markers.get(key, _FP_MARKER_MISSING)
            if value is _FP_MARKER_MISSING:
                finding.pop(key, None)
            else:
                finding[key] = value
def _rollback_fp_deferred(cv2: Any, deferred_baseline: int) -> None:
    del cv2._fp_deferred[deferred_baseline:]
def _censor_pending_families(cv2, pending: list[dict]) -> None:
    for _cf in pending:
        censor_fp_family(cv2, _cf)
def _stage1_filter_one(f: dict, _saa, pipe: _Stage1Pipeline) -> None:
    if _saa is not None:
        try:
            _saa_r = _saa.check_finding(f)
        except Exception as _saa_err:
            logger.warning("[FP-Filter] 策略12自审判定降级(单条跳过): %s",
                           _saa_err, exc_info=True)
        else:
            if _saa_r.is_fp:
                _stage1_remove_with_protection(
                    f, pipe,
                    protect_reason=f"策略12(自审感知:{_saa_r.pattern})",
                    defer_reason=f"策略12:{_saa_r.pattern}:{_saa_r.reason}")
                return
    passed, reason = passes_fp_filter(pipe.cv2, f)
    if not passed:
        _stage1_remove_with_protection(
            f, pipe,
            protect_reason=reason, defer_reason=reason)
        return
    pipe.filtered.append(f)
def filter_false_positives(cv2: Any, findings: list[dict]) -> list[dict]:
    if findings and not isinstance(findings, list):
        logger.warning("[FP-Filter] findings 非 list 形态（撕裂态），跳过误报过滤: %s",
                       type(findings).__name__)
        return findings
    _deferred_baseline = len(ensure_deferred_queue(cv2))
    _marker_baseline = _snapshot_fp_markers(findings)
    try:
        if not findings:
            cv2._fp_filter_log = []
            return []
        _saa = load_fp_filter_state(cv2)
        _ctx = _build_fp_context(cv2, findings)
        if _ctx.get("_fp_context_failed"):
            logger.warning("[XV-FP] FP上下文构建失败，FP过滤器以降级模式运行（矛盾保护映射为空）")
        _mark_batch_findings(findings)
        cv2._fp_filter_log = []
        pipe = _Stage1Pipeline(cv2=cv2, ctx=_ctx, findings=findings,
                               filtered=[], pending_censor=[])
        for f in pipe.findings:
            if isinstance(f, dict):
                _stage1_filter_one(f, _saa, pipe)
            else:
                pipe.filtered.append(f)
        _postprocess_review_flags(pipe.filtered)
        _saa_filtered = _count_saa_filtered(cv2._fp_filter_log)
        logger.info("[FP-Filter] %d -> %d findings (removed %d, deferred %d, self_audit_filtered=%d)",
                    len(findings), len(pipe.filtered),
                    len(findings) - len(pipe.filtered),
                    len(cv2._fp_deferred) - _deferred_baseline,
                    _saa_filtered)
        _censor_pending_families(cv2, pipe.pending_censor)
        return pipe.filtered
    except Exception:
        logger.exception("[FP-Filter] filter_false_positives 降级，返回原始findings")
        cv2._fp_filter_log = []
        _rollback_fp_deferred(cv2, _deferred_baseline)
        _restore_fp_markers(findings, _marker_baseline)
        return findings
def _fp_removal_entry_key(entry: dict) -> tuple:
    finding_id = _norm_batch_key(entry.get("finding_id"))
    if finding_id:
        return ("finding_id", finding_id)
    return (
        "evidence",
        finding_file_key(finding_file_path(entry)),
        safe_finding_line(entry),
        _norm_batch_key(entry.get("rule_id")),
        _norm_batch_key(entry.get("_source_method")),
        _norm_message_text(entry.get("message")),
    )
def _norm_fp_filter_log(cv2) -> list:
    _fl = getattr(cv2, "_fp_filter_log", None)
    if isinstance(_fl, list):
        return _fl
    cv2._fp_filter_log = []
    return []
def _dedup_fp_removal_log(cv2, removed_log) -> int:
    if not removed_log:
        return 0
    _norm_fp_filter_log(cv2)
    existing_keys = {
        _fp_removal_entry_key(e)
        for e in cv2._fp_filter_log if isinstance(e, dict)
    }
    dedup_count = 0
    for entry in removed_log:
        if not isinstance(entry, dict):
            logger.warning("[FP-Filter-2] 移除日志条目非 dict 形态，跳过登记: %r", entry)
            continue
        key = _fp_removal_entry_key(entry)
        if "severity" not in entry:
            entry["severity"] = ""
        if key in existing_keys:
            dedup_count += 1
            continue
        cv2._fp_filter_log.append(entry)
        existing_keys.add(key)
    return dedup_count
def _converge_stage1_marker(f: dict, reason: str,
                            should_remove: bool) -> tuple[str, bool]:
    if not f.get(SIGNAL_STAGE1_FP_CANDIDATE):
        return reason, False
    if not should_remove:
        return reason, False
    stage1_reason = f.pop(SIGNAL_STAGE1_FP_CANDIDATE, "")
    return f"{stage1_reason} + {reason}", True
def _stage2_removal_verdict(f: dict, ctx: dict) -> tuple[bool, str]:
    _sev_upper, sev_rank = _severity_parts(f)
    if sev_rank <= 1:
        should_remove, reason = check_p0p1_fp_signals(f)
    else:
        should_remove, reason = check_individual_fp_signals(f)
        if (should_remove and sev_rank == 2
                and count_p2_fp_signals(f) < 2):
            should_remove, reason = False, ""
    if should_remove and _check_fp_protections(f, ctx, "stage2", reason):
        should_remove, reason = False, ""
    return should_remove, reason
def _eval_stage2_finding(f: dict, ctx: dict) -> tuple[bool, str, bool]:
    should_remove, reason = _stage2_removal_verdict(f, ctx)
    reason, _was_stage1_fp = _converge_stage1_marker(
        f, reason, should_remove)
    return should_remove, reason, _was_stage1_fp
def _apply_stage2_filter(cv2: Any, ctx: dict, findings: list) -> tuple[list, list, list]:
    filtered: list = []
    removed_log: list = []
    pending_censor: list[dict] = []
    for f in findings:
        if not isinstance(f, dict):
            filtered.append(f)
            continue
        should_remove, reason, _was_stage1_fp = _eval_stage2_finding(f, ctx)
        if not should_remove:
            filtered.append(f)
            continue
        if _was_stage1_fp:
            pending_censor.append(f)
        _record_fp_deletion(cv2, removed_log, f, reason, stage="stage2_annotation")
    return filtered, removed_log, pending_censor
def _rollback_stage2_filter(cv2: Any, deferred_baseline: int,
                            filter_log_baseline: int,
                            marker_baseline: dict[int, dict]) -> None:
    _rollback_fp_deferred(cv2, deferred_baseline)
    _restore_fp_markers(cv2.all_findings, marker_baseline)
    _fl = getattr(cv2, "_fp_filter_log", None)
    if isinstance(_fl, list):
        del _fl[filter_log_baseline:]
def _stage2_input_guard(cv2: Any) -> bool:
    findings = cv2.all_findings
    if isinstance(findings, list):
        return bool(findings)
    if findings:
        logger.warning("[FP-Filter-2] all_findings 非 list 形态（撕裂态），跳过注解后过滤: %s",
                       type(findings).__name__)
    return False
def _run_stage2_filter(cv2: Any) -> None:
    pre_count = len(cv2.all_findings)
    ctx = _build_fp_context(cv2, cv2.all_findings)
    if ctx.get("_fp_context_failed"):
        logger.warning("[XV-FP] Stage2 FP上下文构建失败，保护检查降级运行（矛盾保护映射为空）")
    filtered, removed_log, pending_censor = _apply_stage2_filter(
        cv2, ctx, cv2.all_findings)
    dedup_count = _dedup_fp_removal_log(cv2, removed_log)
    if removed_log:
        logger.info("[FP-Filter-2] %d -> %d findings (removed %d by annotation, dedup %d)",
                    pre_count, len(filtered),
                    len(removed_log) - dedup_count, dedup_count)
    cv2.all_findings = filtered
    _censor_pending_families(cv2, pending_censor)
def post_annotation_fp_filter(cv2: Any) -> None:
    if not _stage2_input_guard(cv2):
        return
    _deferred_baseline = len(ensure_deferred_queue(cv2))
    _filter_log_baseline = len(_norm_fp_filter_log(cv2))
    _findings_baseline = cv2.all_findings
    _marker_baseline = _snapshot_fp_markers(_findings_baseline)
    try:
        _run_stage2_filter(cv2)
    except Exception:
        logger.exception("[FP-Filter-2] post_annotation_fp_filter 降级，保留原始findings")
        cv2.all_findings = _findings_baseline
        _rollback_stage2_filter(
            cv2, _deferred_baseline, _filter_log_baseline, _marker_baseline)
SHADOW_EVIDENCE_MARKER = "_fp_shadow"
_CONFIRMED_CONCLUSIONS: frozenset[str] = frozenset({"confirmed", "likely"})
def _is_confirmed_conclusion(value: Any) -> bool:
    return str(value or "").strip().lower() in _CONFIRMED_CONCLUSIONS
def _is_shadow(f: Any) -> bool:
    return isinstance(f, dict) and bool(f.get(SHADOW_EVIDENCE_MARKER))
def _norm_message_text(raw: Any, *, lower: bool = False) -> str:
    text = (raw if isinstance(raw, str) else "").strip()
    return text.lower() if lower else text
_SHADOW_EXCLUDE_REASON_SUBSTRINGS = (
    "策略5:", "策略6:",
    "策略9:", "策略10",
    "策略12",
    "策略16",
    "mutation_refuted",
    "bizflow_fp_candidate",
    "arbiter_demoted",
    "baseline_persistent_noise",
    "ensemble_low_confidence",
    "refdepth_isolated",
    "p0p1_multi_signal_fp",
)
def _reinjectable(df: dict) -> bool:
    reason = str(df.get("_fp_deferred_reason", ""))
    return not any(sub in reason for sub in _SHADOW_EXCLUDE_REASON_SUBSTRINGS)
def _reinject_shadow_items(deferred: list, all_findings: list) -> int:
    reinjected = 0
    for df in deferred:
        if not isinstance(df, dict):
            continue
        if not _reinjectable(df):
            continue
        if _is_shadow(df):
            continue
        df[SHADOW_EVIDENCE_MARKER] = True
        all_findings.append(df)
        reinjected += 1
    return reinjected
def reinject_deferred_as_shadow(cv2: Any) -> int:
    try:
        deferred = ensure_deferred_queue(cv2)
        if not deferred:
            return 0
        if not isinstance(cv2.all_findings, list):
            logger.warning(
                "[FP-Shadow] all_findings 非 list 形态(%s)，影子回注跳过",
                type(cv2.all_findings).__name__)
            return 0
        reinjected = _reinject_shadow_items(deferred, cv2.all_findings)
        if reinjected:
            logger.info(
                "[FP-Shadow] %d 个 deferred findings 以影子证据身份回注规则匹配"
                "（队列共 %d，未回注 %d：排除类/撕裂形态/已回注）",
                reinjected, len(deferred), len(deferred) - reinjected)
        return reinjected
    except Exception as _shadow_e:  # noqa: BLE001
        logger.warning("[FP-Shadow] 影子回注降级跳过: %s", _shadow_e)
    return 0
def _xvr_findings_of(xvr: dict) -> list | tuple:
    _fl = xvr.get("findings")
    return _fl if isinstance(_fl, (list, tuple)) else []
def _xvr_rule_families(xvr: dict) -> set:
    _rf_raw = xvr.get("rule_families")
    if isinstance(_rf_raw, str):
        raw_families = {_rf_raw} if _rf_raw else set()
    elif isinstance(_rf_raw, (list, tuple, set, frozenset)):
        raw_families = {_rf for _rf in _rf_raw if isinstance(_rf, str)}
    else:
        raw_families = set()
    families = {normalize_rule(family) for family in raw_families if family}
    families.add(_normalized_finding_family(xvr))
    families.update(_normalized_finding_family(ef)
                    for ef in _xvr_findings_of(xvr) if isinstance(ef, dict))
    families.discard("")
    return families
_CJK_SEGMENT_RE = re.compile(r"[\u4e00-\u9fff]+")
def _message_tokens(text: str) -> set[str]:
    tokens = set(text.split())
    for segment in _CJK_SEGMENT_RE.findall(text):
        if len(segment) == 1:
            tokens.add(segment)
        else:
            tokens.update(segment[i:i + 2]
                          for i in range(len(segment) - 1))
    return tokens
def _jaccard_hits(df_words: set, ef_msg: str) -> bool:
    ef_words = _message_tokens(ef_msg)
    if not df_words or not ef_words:
        return False
    _threshold = CONF_HIGH if (len(df_words) < 5 or len(ef_words) < 5) else 0.5
    return len(df_words & ef_words) / len(df_words | ef_words) >= _threshold
def _is_rescue_message_similar(df: dict, xvr: dict) -> bool:
    df_fam = _normalized_finding_family(df)
    if df_fam and df_fam in _xvr_rule_families(xvr):
        return True
    df_msg = _norm_message_text(df.get("message"), lower=True)
    if not df_msg:
        return True
    df_words = _message_tokens(df_msg)
    for ef in _xvr_findings_of(xvr):
        if not isinstance(ef, dict):
            continue
        ef_msg = _norm_message_text(ef.get("message"), lower=True)
        if ef_msg and _jaccard_hits(df_words, ef_msg):
            return True
    return False
def _finding_locator_parts(df: dict) -> tuple[str, int, str]:
    fpath = finding_file_key(finding_file_path(df))
    fline = safe_finding_line(df)
    frf = _normalized_finding_family(df) or "diag_general"
    return fpath, fline, frf
def _mark_rescued(f: dict) -> None:
    f["_rescued"] = True
    f["_rescued_from"] = f.pop("_fp_deferred_reason", "")
    f.pop("_fp_deferred_stage", None)
def _finding_rescue_dedup_key(f: dict) -> tuple:
    fpath, fline, frf = _finding_locator_parts(f)
    source = _known_source_method(f.get("_source_method", ""))
    return (fpath, fline, frf, source, _norm_message_text(f.get("message")))
def _drain_shadow_removed(cv2: Any) -> list:
    _removed = getattr(cv2, "_shadow_removed_unrescued", None)
    cv2._shadow_removed_unrescued = []
    if not isinstance(_removed, list):
        return []
    return [df for df in _removed if isinstance(df, dict)]
def _adjudicate_one_shadow_group(xvr: dict, rescued: list[dict],
                                 collect_removed) -> None:
    # 规则计算阶段影子被隔离在专用队列；此处才与真实结论会合。
    # 同时兼容旧调用方直接把影子放在 findings 中的结构。
    fl = list(_xvr_findings_of(xvr))
    fl.extend(dict_findings(xvr.pop("_shadow_findings", [])))
    if not any(_is_shadow(_f) for _f in fl):
        return
    conclusion_ok = _is_confirmed_conclusion(_effective_conclusion(xvr))
    kept: list = []
    for _f in fl:
        if not _is_shadow(_f):
            kept.append(_f)
            continue
        if conclusion_ok:
            _f.pop(SHADOW_EVIDENCE_MARKER, None)
            _mark_rescued(_f)
            rescued.append(_f)
            kept.append(_f)
        else:
            collect_removed(_f)
    xvr["findings"] = kept
    xvr["findings_count"] = len(kept)
def _prune_all_findings(cv2: Any, rescued_ids: set[int], collect_removed) -> None:
    if not isinstance(cv2.all_findings, list):
        return
    _keep_all = []
    for _f in cv2.all_findings:
        if _is_shadow(_f) and id(_f) not in rescued_ids:
            collect_removed(_f)
            continue
        _keep_all.append(_f)
    cv2.all_findings = _keep_all
def _adjudicate_shadow_evidence(cv2: Any, xv_findings: list) -> list:
    rescued: list[dict] = []
    removed_shadows: list[dict] = []
    _removed_ids: set[int] = set()
    def _collect_removed(df: dict) -> None:
        if id(df) not in _removed_ids:
            _removed_ids.add(id(df))
            removed_shadows.append(df)
    for xvr in xv_findings:
        if isinstance(xvr, dict):
            _adjudicate_one_shadow_group(xvr, rescued, _collect_removed)
    rescued_ids = {id(_f) for _f in rescued}
    _prune_all_findings(cv2, rescued_ids, _collect_removed)
    removed_shadows = [df for df in removed_shadows
                       if id(df) not in rescued_ids]
    cv2._shadow_removed_unrescued = removed_shadows
    if rescued:
        logger.info("[FP-Shadow] 影子证据裁决: %d 个转正（交叉验证确认）",
                    len(rescued))
    if removed_shadows:
        logger.info("[FP-Shadow] 影子证据裁决: %d 个未获规则确认移除（挂账待强制复核）",
                    len(removed_shadows))
    return rescued
def _canonical_confirmed_locator(locator: str, family_fallback: str) -> str:
    file_part = parse_locator_file(locator)
    locator_tail = locator[len(file_part):]
    family = (locator_tail.rsplit(":", 1)[1]
              if locator_tail.count(":") >= 2 else "")
    return _rescue_locator_of({
        "file": file_part,
        "line": parse_locator_line(locator),
        "rule_family": family or family_fallback,
    })
def _confirmed_family_fallback(xvr: dict) -> str:
    families = {family for family in _xvr_rule_families(xvr) if family}
    return next(iter(families)) if len(families) == 1 else ""
def _confirmed_locator_of(xvr: Any) -> tuple[str, dict] | None:
    if not isinstance(xvr, dict):
        return None
    loc = xvr.get("locator", "")
    if not (isinstance(loc, str) and loc):
        return None
    if not _is_confirmed_conclusion(_effective_conclusion(xvr)):
        return None
    return _canonical_confirmed_locator(
        loc, _confirmed_family_fallback(xvr)), xvr
def _rescue_locator_of(df: dict) -> str:
    fpath, fline, frf = _finding_locator_parts(df)
    return f"{fpath}:{_locator_line_slot(fline)}:{frf}"
def _account_unrescued(cv2: Any, deferred_items: list) -> None:
    _seen: set[int] = set()
    _unrescued: list = []
    for df in [*(deferred_items or ()), *_drain_shadow_removed(cv2)]:
        if not isinstance(df, dict) or df.get("_rescued"):
            continue
        if id(df) in _seen:
            continue
        _seen.add(id(df))
        _unrescued.append(df)
    cv2._fp_unrescued_deferred = _unrescued
    cv2._fp_deferred = []
def _confirmed_locator_index(xv_findings: list) -> dict:
    confirmed_locators: dict = {}
    for xvr in xv_findings:
        item = _confirmed_locator_of(xvr)
        if item is not None:
            confirmed_locators.setdefault(item[0], []).append(item[1])
    return confirmed_locators
def _xvr_dedup_state(xvr_findings: list) -> tuple[set, set]:
    existing_sources: set = set()
    existing_keys: set = set()
    for ef in xvr_findings:
        if not isinstance(ef, dict):
            continue
        _src_f = _known_source_method(ef.get("_source_method", ""))
        if _src_f:
            existing_sources.add(_src_f)
        existing_keys.add(_finding_rescue_dedup_key(ef))
    return existing_sources, existing_keys
def _reinject_finding(df: dict, xvr: dict) -> str:
    xvr_findings = xvr.get("findings")
    if isinstance(xvr_findings, tuple):
        xvr_findings = xvr["findings"] = list(xvr_findings)
    elif not isinstance(xvr_findings, list):
        xvr_findings = xvr["findings"] = []
    existing_sources, existing_keys = _xvr_dedup_state(xvr_findings)
    if _finding_rescue_dedup_key(df) in existing_keys:
        _mark_rescued(df)
        return "duplicate"
    source = _known_source_method(df.get("_source_method", ""))
    if ((source and source in existing_sources)
            or not _is_rescue_message_similar(df, xvr)):
        return "unmatched"
    xvr_findings.append(df)
    xvr["findings_count"] = len(xvr_findings)
    _mark_rescued(df)
    return "rescued"
def _rescue_legacy_items(legacy_items: list, confirmed_locators: dict) -> list[dict]:
    rescued: list[dict] = []
    for df in legacy_items:
        if not isinstance(df, dict) or not _reinjectable(df):
            continue
        candidates = confirmed_locators.get(_rescue_locator_of(df), ())
        for xvr in candidates:
            outcome = _reinject_finding(df, xvr)
            if outcome in {"duplicate", "rescued"}:
                rescued.append(df)
                break
    return rescued
def rescue_deferred_findings(cv2: Any, xv_findings: list) -> list:
    deferred = ensure_deferred_queue(cv2)
    if not deferred:
        _account_unrescued(cv2, deferred)
        return []
    rescued: list[dict] = []
    _shadow_items = [df for df in deferred if _is_shadow(df)]
    legacy_items = [df for df in deferred if not _is_shadow(df)]
    if _shadow_items:
        rescued.extend(_adjudicate_shadow_evidence(cv2, xv_findings))
    if not legacy_items:
        _account_unrescued(cv2, deferred)
        return rescued
    rescued.extend(_rescue_legacy_items(legacy_items,
                                        _confirmed_locator_index(xv_findings)))
    if rescued:
        logger.info("[FP-Rescue] 救援 %d 个被延迟删除的finding（共 %d 个deferred）",
                    len(rescued), len(deferred))
    _account_unrescued(cv2, deferred)
    return rescued

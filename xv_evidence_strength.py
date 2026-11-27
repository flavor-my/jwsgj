from __future__ import annotations

import json
import logging
import math
import os
import threading
import time
from typing import Any, NamedTuple

from jwsgj.diag_guard_io import (
    replace_with_retry,
    safe_delete,
)
from jwsgj.diag_types_normalize import (
    coerce_text_list,
    degrade_factor_of,
    is_real_number,
    safe_confidence,
    safe_dict_get,
    safe_float,
    safe_int,
    safe_str,
    signal_bool,
)
from jwsgj.diag_types_vocab import (
    CONCLUSION_V2_MAP,
    CONF_BOOST_MODERATE,
    CONF_BOOST_SMALL,
    CONF_BOOST_STEP,
    CONF_CAP,
    CONF_FLOOR,
    CONF_LOW,
    CONF_PENALTY_MODERATE,
    CONF_VERY_HIGH,
    FP_RATE_HIGH,
    FP_RATE_VERY_LOW,
    SIGNAL_BASELINE_HIT_COUNT,
    SIGNAL_BASELINE_PERSISTENT_NOISE,
    SIGNAL_BIZFLOW_CONFIDENCE_BOOST,
    SIGNAL_ENSEMBLE_GROUP_COUNT,
    SIGNAL_ENSEMBLE_LOW_CONFIDENCE,
    SIGNAL_MUTATION_VERIFIED,
    SIGNAL_REFDEPTH_CHAIN_DEPTH,
    SIGNAL_REFDEPTH_CONFIDENCE_BOOST,
    SIGNAL_REFDEPTH_IN_DEGREE,
    SIGNAL_REFDEPTH_ISOLATED,
    SIGNAL_REFDEPTH_PRIORITY_BOOST,
    SUB_ENGINE_META,
)
from jwsgj.log_config import locked_artifact, log_swallowed
from jwsgj.runtime_paths import evidence_weights_path, fp_rules_path
from jwsgj.xv_context_derivation import (
    METHOD_EVIDENCE_TYPES,
    METHOD_REGISTRY,
)
from jwsgj.xv_threshold_learning import (
    PRECISE_SMOKE_FAMILIES,
    learning_dir_request,
    record_threshold_outcome,
)

logger = logging.getLogger(__name__)
__all__ = [
    "ANNOTATION_PENALTY_CAP",
    "ANNOTATION_PHASE_MODULES",
    "DEPTH_CONFIDENCE_BOOST_CAP",
    "DEPTH_PRIORITY_BOOST_CAP",
    "EVIDENCE_FAMILY_NAMES",
    "ISOLATED_CONFIDENCE_PENALTY",
    "PHASE_CRITICALITY_LEVELS",
    "PHASE_MODULE_CRITICALITY",
    "REGRESSION_FAMILIES",
    "RULE_FAMILY_TO_FAMILY",
    "SOURCE_FAMILIES",
    "apply_annotation_completeness",
    "available_methods",
    "bizflow_signal_payload",
    "business_flow_confidence_boost",
    "count_independent_sources",
    "counter_evidence_confidence_penalty",
    "dominant_rule_family_by_method",
    "evidence_channel_scale",
    "evidence_meta",
    "evidence_strength_base",
    "evidence_strength_by_rule_family",
    "evidence_strength_weighted",
    "evidence_types_of",
    "family_of_source",
    "family_reliability_base",
    "get_evidence_family_weight",
    "independent_sources",
    "partial_deg_factors_map",
    "refdepth_boosts",
    "refdepth_signal_payload",
    "reset_evidence_ladder",
    "set_available_methods",
    "set_evidence_ladder",
    "set_evidence_learning_dir",
    "source_family_names",
    "source_main_id",
    "sub_engine_meta",
    "test_triage_confidence_boost",
    "unreviewed_suppression_stats",
    "update_evidence_family_weight",
    "update_rule_weights",
    "validate_source_family_consistency",
    "vcs_recency_confidence_boost",
]
logger.info("xv_evidence_strength 证据强度面已加载: %d 项导出", len(__all__))
ANNOTATION_PENALTY_CAP: float = 0.30
PHASE_CRITICALITY_LEVELS: frozenset[str] = frozenset({"critical", "degraded"})
class _AnnotationSpec(NamedTuple):
    flag_key: str
    evidence_keys: tuple[str, ...]
    criticality: str
_ANNOTATION_SPECS: dict[str, _AnnotationSpec] = {
    "xv_baseline": _AnnotationSpec(
        "_baseline_annotated",
        (SIGNAL_BASELINE_HIT_COUNT, "_baseline_is_new",
         SIGNAL_BASELINE_PERSISTENT_NOISE),
        "degraded"),
    "xv_phase_rules": _AnnotationSpec(
        "_bizflow_annotated", ("_bizflow_reachable", "_bizflow_fp_candidate"),
        "degraded"),
    "xv_ref_depth": _AnnotationSpec(
        "_refdepth_annotated",
        (SIGNAL_REFDEPTH_ISOLATED, SIGNAL_REFDEPTH_IN_DEGREE,
         SIGNAL_REFDEPTH_CHAIN_DEPTH),
        "degraded"),
    "xv_ensemble": _AnnotationSpec(
        "_ensemble_annotated",
        ("_ensemble_is_confirmed", SIGNAL_ENSEMBLE_GROUP_COUNT,
         SIGNAL_ENSEMBLE_LOW_CONFIDENCE),
        "critical"),
    "xv_mutation": _AnnotationSpec(
        "_mutation_annotated",
        (SIGNAL_MUTATION_VERIFIED, "_mutation_inconclusive",
         "_mutation_annotation_done", "_mutation_not_applicable"),
        "critical"),
}
ANNOTATION_PHASE_MODULES = tuple(_ANNOTATION_SPECS)
PHASE_MODULE_CRITICALITY: dict[str, str] = {
    module: spec.criticality for module, spec in _ANNOTATION_SPECS.items()
    if spec.criticality in PHASE_CRITICALITY_LEVELS
}
def _has_annotation_evidence(f: dict, ev_keys: tuple[str, ...]) -> bool:
    return any(k in f for k in ev_keys)
_ANNOTATION_BASE_CONF_KEY = "_annotation_base_confidence"
def _annotation_base_confidence(f: dict) -> float | None:
    base = f.get(_ANNOTATION_BASE_CONF_KEY)
    if is_real_number(base):
        return float(base)
    cur = f.get("confidence")
    if not is_real_number(cur):
        return None
    f[_ANNOTATION_BASE_CONF_KEY] = cur
    return float(cur)
def _annotate_finding_completeness(f: dict, completed: set,
                                   expected_count: int) -> None:
    f["_completed_annotations"] = [
        mod for mod in ANNOTATION_PHASE_MODULES if mod in completed]
    for mod, spec in _ANNOTATION_SPECS.items():
        f[spec.flag_key] = mod in completed
    base = _annotation_base_confidence(f)
    if base is None:
        return
    _missing = max(0, expected_count - len(completed))
    _penalty_amount = min(CONF_BOOST_SMALL * _missing, ANNOTATION_PENALTY_CAP)
    _retain_factor = 1.0 - _penalty_amount
    f["confidence"] = safe_confidence(
        round(base * _retain_factor, 3), base)
def apply_annotation_completeness(all_findings: list, available) -> None:
    if not isinstance(all_findings, (list, tuple)):
        logger.warning(
            "[Annotation] all_findings 形态非法(%s)，跳过完整性注解",
            type(all_findings).__name__)
        return
    _expected_count = len(ANNOTATION_PHASE_MODULES)
    if isinstance(available, str):
        _available = {available}
    elif isinstance(available, (list, tuple, set, frozenset)):
        _available = set(available)
    else:
        _available = set()
    for f in all_findings:
        if isinstance(f, dict):
            _completed = {
                mod for mod, spec in _ANNOTATION_SPECS.items()
                if mod in _available
                and _has_annotation_evidence(f, spec.evidence_keys)
            }
            _annotate_finding_completeness(f, _completed, _expected_count)
SOURCE_FAMILIES: dict[str, frozenset] = {
    "AST-pattern":      frozenset(["A"]),
    "AST-controlflow":  frozenset(),
    "AST-antipattern":  frozenset(["B"]),
    "AST-lint":         frozenset(),
    "AST-complexity":   frozenset(),
    "AST-resource":     frozenset(),
    "AST-security":     frozenset(["D", "SE-20"]),
    "AST-blindspot":    frozenset(),
    "runtime":          frozenset(),
    "coverage":         frozenset(["E"]),
    "dynamic_exec":     frozenset(),
    "call_graph":       frozenset(["C"]),
    "static_text":      frozenset(),
    "metrics":          frozenset(),
    "AST-verification": frozenset(["F"]),
    "history":          frozenset(),
    "human_confirmation": frozenset(["HUMAN_CONFIRM"]),
    "log_analysis":     frozenset(),
    "type_check":       frozenset(),
    "test_quality":     frozenset(),
    "bidirectional_taint": frozenset(["BI_TAINT_BACKWARD","BI_TAINT_FORWARD"]),
    "llm_cv":            frozenset(["LLM_CV"]),
    "baseline":         frozenset(),
    "business_flow":    frozenset(),
    "ref_depth":        frozenset(["B3"]),
    "ensemble":         frozenset(),
    "mutation":         frozenset(["M1"]),
    "hallucination":    frozenset(["H1_API"]),
}
REGRESSION_FAMILIES = frozenset({
    "regression", "baseline_degradation", "degraded",
    "score_regression", "blindspot_increase",
})
_AUTO_DEPS_CACHE = None
def _extract_all_dependencies() -> dict[str, list[str]]:
    global _AUTO_DEPS_CACHE
    if _AUTO_DEPS_CACHE is not None:
        return _AUTO_DEPS_CACHE
    auto_deps: dict[str, list[str]] = {}
    for method_id, cfg in METHOD_REGISTRY.items():
        for dep in cfg.depends_on:
            if dep in METHOD_REGISTRY:
                auto_deps.setdefault(method_id, []).append(dep)
    _AUTO_DEPS_CACHE = auto_deps
    return auto_deps
def _source_id_text(source) -> str:
    if isinstance(source, str):
        return source.strip()
    if isinstance(source, (bytes, bytearray)):
        return bytes(source).decode("utf-8", "replace").strip()
    return ""
def _dedup_sources(source_ids) -> list:
    if isinstance(source_ids, (str, bytes, bytearray)):
        source_ids = [source_ids]
    try:
        iterator = iter(source_ids)
    except TypeError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc, context='_dedup_sources:TypeError')
        return []
    _seen: set[str] = set()
    _deduped: list[str] = []
    for source in iterator:
        _sid = _source_id_text(source)
        if _sid and _sid not in _seen:
            _seen.add(_sid)
            _deduped.append(_sid)
    return _deduped
def _sub_engine_main(source) -> str | None:
    main = source_main_id(source)
    return main if main and main != source else None
def _source_engine_ids(source_ids) -> set[str]:
    ids: set[str] = set()
    for s in source_ids:
        if not isinstance(s, str) or not s:
            continue
        ids.add(s)
        main = _sub_engine_main(s)
        if main is not None:
            ids.add(main)
    return ids
def _select_independent_sources(source_ids: list[str],
                                  auto_deps: dict) -> list[str]:
    source_set = set(source_ids)
    reachability: dict[str, set[str]] = {}
    for source in source_ids:
        reached: set[str] = set()
        stack = list(auto_deps.get(source, []))
        main = _sub_engine_main(source)
        if main is not None and main in source_set:
            stack.append(main)
        while stack:
            dependency = stack.pop()
            if dependency in reached:
                continue
            reached.add(dependency)
            stack.extend(auto_deps.get(dependency, []))
        reachability[source] = reached
    components: list[set[str]] = []
    assigned: set[str] = set()
    for source in source_ids:
        if source in assigned:
            continue
        reached = reachability[source]
        component = {
            candidate for candidate in source_ids
            if candidate == source or (
                candidate in reached
                and source in reachability[candidate]
            )
        }
        components.append(component)
        assigned.update(component)
    independent: list[str] = []
    for component in components:
        # 依赖方向的含义是「下游结果已包含上游证据」：保留下游综合源，
        # 剔除被其他所选源依赖的上游组件，避免同一证据重复计数。
        is_dependency_of_external_source = any(
            not component.isdisjoint(reachability[source])
            for source in source_ids if source not in component
        )
        if is_dependency_of_external_source:
            continue
        independent.append(next(
            source for source in source_ids if source in component))
    return independent
def independent_sources(source_ids: list[str]) -> list[str]:
    _fallback_single: list = []
    try:
        if isinstance(source_ids, (set, frozenset)):
            source_ids = sorted(source_ids, key=str)
        source_ids = _dedup_sources(source_ids)
        _fallback_single = source_ids[:1]
        auto_deps = _extract_all_dependencies()
        return _select_independent_sources(source_ids, auto_deps)
    except Exception as e:  # noqa: BLE001
        logger.warning("independent_sources: 依赖提取失败，保守按单源回退: %s", e)
        return _fallback_single
def count_independent_sources(source_ids: list[str]) -> int:
    return len(independent_sources(source_ids))
def partial_deg_factors_map(findings) -> dict:
    _deg_factors = {}
    if findings is None:
        return _deg_factors
    try:
        iterator = iter(findings)
    except TypeError as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context='partial_deg_factors_map:TypeError')
        return _deg_factors
    for _f in iterator:
        if not isinstance(_f, dict) or not signal_bool(
                _f.get("_partial_degrade")):
            continue
        _sm = _source_id_text(_f.get("_source_method", ""))
        if not _sm:
            continue
        _deg_factors[_sm] = min(
            _deg_factors.get(_sm, 1.0), degrade_factor_of(_f))
    return _deg_factors
RULE_FAMILY_TO_FAMILY: dict[str, str] = {
    "broad_except": "AST-antipattern",
    "empty_except": "AST-antipattern",
    "sql_injection": "AST-security",
    "path_traversal": "AST-security",
    "hardcoded_credential": "AST-security",
    "danger_pattern": "AST-security",
    "high_complexity": "AST-complexity",
    "dead_code": "call_graph",
    "circular_dep": "AST-antipattern",
    "broken_call": "call_graph",
    "mutable_global": "AST-antipattern",
    "mutable_default": "AST-antipattern",
    "duplicate_code": "AST-antipattern",
    "unused_import": "AST-antipattern",
    "missing_docstring": "static_text",
    "doc_consistency": "static_text",
    "code_smell": "AST-antipattern",
    "shadowing_builtin": "AST-antipattern",
    "global_statement": "AST-antipattern",
    "test_failure": "runtime",
    "test_error": "runtime",
    "test_smell": "runtime",
    "hallucinated_api": "hallucination",
    "hallucinated_import": "hallucination",
    "hallucinated_exception": "hallucination",
    "context_contradiction": "hallucination",
    "ai_slop": "hallucination",
    "test_illusion": "hallucination",
    "memory_hallucination": "hallucination",
    "sandbox_reflection": "hallucination",
    "hallucinated_module": "hallucination",
    "hallucination_general": "hallucination",
}
_DEFAULT_LADDER: dict[int, float] = {
    0: CONF_FLOOR,
    1: CONF_LOW,
    2: 0.50,
    3: 0.60,
    4: 0.68,
    5: 0.75,
    6: CONF_VERY_HIGH,
}
_EVIDENCE_LADDER: dict[int, float] = dict(_DEFAULT_LADDER)
_LADDER_MAX_LEVEL: int = 6
def _ladder_levels() -> range:
    return range(_LADDER_MAX_LEVEL + 1)
def _is_unit_interval_number(value) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and 0 <= value <= 1
    )
def _is_valid_ladder(ladder) -> bool:
    return all(
        k in ladder and _is_unit_interval_number(ladder[k])
        for k in _ladder_levels()) and all(
        ladder[k] <= ladder[k + 1] for k in range(_LADDER_MAX_LEVEL))
def set_evidence_ladder(ladder: dict[int, float]) -> None:
    global _EVIDENCE_LADDER
    try:
        if _is_valid_ladder(ladder):
            _EVIDENCE_LADDER = {k: ladder[k] for k in _ladder_levels()}
            logger.info("[Evidence] 证据强度梯子已更新: %s", ladder)
        else:
            logger.warning(
                "[Evidence] 梯子更新失败: 缺少键或值域越界 "
                "(需要 0-6 全部键且值为 [0,1] 域内数值)")
    except Exception:
        logger.exception("[set_evidence_ladder] 异常降级")
def reset_evidence_ladder() -> None:
    global _EVIDENCE_LADDER
    try:
        _EVIDENCE_LADDER = dict(_DEFAULT_LADDER)
    except Exception:
        logger.exception("[reset_evidence_ladder] 异常降级")
def _ladder_confidence(fam_sources: dict[str, float]) -> float:
    intra_bonus = sum(max(0, cnt - 1) * CONF_BOOST_MODERATE for cnt in fam_sources.values())
    effective = max(0.0, min(
        sum(min(cnt, 1.0) for cnt in fam_sources.values()) + intra_bonus,
        float(_LADDER_MAX_LEVEL)))
    low = int(effective)
    high = min(low + 1, _LADDER_MAX_LEVEL)
    frac = effective - low
    ladder = _EVIDENCE_LADDER
    low_value = ladder[low]
    high_value = ladder[high]
    return round(low_value + (high_value - low_value) * frac, 3)
_FAMILY_OVERRIDE: dict[str, str] = {
    "E": "coverage",
    "F3": "coverage",
}
def _sub_engine_family(s: str) -> str | None:
    meta = SUB_ENGINE_META.get(s)
    if not isinstance(meta, dict):
        return None
    family = meta.get("family")
    return family if isinstance(family, str) and family in SOURCE_FAMILIES else None
def family_of_source(s: str, *, use_override: bool = True) -> str | None:
    s = _source_id_text(s)
    if not s:
        return None
    if use_override:
        _fam = _FAMILY_OVERRIDE.get(s)
        if _fam is not None:
            return _fam
    _fam = _sub_engine_family(s)
    if _fam is not None:
        return _fam
    for family, members in SOURCE_FAMILIES.items():
        if s in members:
            return family
    _main = source_main_id(s)
    if _main and _main != s:
        return family_of_source(_main, use_override=False)
    return None
def _normalized_degrade_factor(v) -> float:
    value = safe_float(v, None)
    return value if value is not None and 0 <= value <= 1 else 1.0
def _normalized_degrade_map(degraded_sources) -> dict:
    if not isinstance(degraded_sources, dict):
        return {}
    normalized = {}
    for source, factor in degraded_sources.items():
        _sid = _source_id_text(source)
        if not _sid:
            continue
        _factor = _normalized_degrade_factor(factor)
        normalized[_sid] = min(normalized.get(_sid, 1.0), _factor)
    return normalized
def _aggregate_family_sources(indep_sources: list, degrade_map: dict,
                              resolve_family) -> dict:
    _resolve = resolve_family or family_of_source
    fam_sources = {}
    for s in indep_sources:
        if not isinstance(s, str):
            continue
        _fam = _resolve(s)
        if _fam is not None:
            fam_sources[_fam] = (
                fam_sources.get(_fam, 0)
                + _normalized_degrade_factor(degrade_map.get(s, 1.0)))
    return fam_sources
def _domain_coverage_bonus(engine_ids: set) -> float:
    domains = set()
    for s in engine_ids:
        cfg = METHOD_REGISTRY.get(s)
        if cfg is not None and cfg.domain:
            domains.add(cfg.domain)
    return min(0.02 * max(len(domains) - 1, 0), 0.04)
def _family_sources_of(source_ids: list[str], degraded_sources: dict | None,
                        resolver) -> tuple[list[str], dict]:
    indep_sources = independent_sources(source_ids)
    if not indep_sources:
        return indep_sources, {}
    degrade_map = _normalized_degrade_map(degraded_sources)
    indep_sources = [
        source for source in indep_sources
        if degrade_map.get(source, 1.0) > 0.0
    ]
    if not indep_sources:
        return indep_sources, {}
    return indep_sources, _aggregate_family_sources(
        indep_sources, degrade_map, resolver)
def _ladder_base_of(source_ids: list[str], degraded_sources: dict | None,
                    resolver=None) -> tuple[list, dict, float]:
    indep_sources, fam_sources = _family_sources_of(
        source_ids, degraded_sources, resolver)
    if not indep_sources:
        return indep_sources, fam_sources, CONF_FLOOR
    if not fam_sources:
        return indep_sources, fam_sources, CONF_LOW
    return indep_sources, fam_sources, _ladder_confidence(fam_sources)
def _base_with_bonus(indep_sources: list, fam_sources: dict,
                     result: float) -> float:
    if not any(fam_sources.values()):
        return result
    engine_ids = _source_engine_ids(indep_sources)
    bonus = 0.0
    if "B" in engine_ids and "coverage" in fam_sources:
        bonus = CONF_BOOST_SMALL
    bonus += _domain_coverage_bonus(engine_ids)
    return round(min(result + bonus, 1.0), 3)
def evidence_strength_base(source_ids: list[str], degraded_sources: dict | None = None) -> float:
    indep_sources, fam_sources, result = _ladder_base_of(
        source_ids, degraded_sources)
    return _base_with_bonus(indep_sources, fam_sources, result)
_INITIAL_EVIDENCE_WEIGHTS: dict[str, float] = {
    "AST-pattern": 1.0,
    "AST-controlflow": 1.15,
    "AST-antipattern": 1.0,
    "AST-lint": 0.90,
    "AST-complexity": 1.0,
    "AST-resource": 1.15,
    "AST-security": 1.25,
    "AST-blindspot": 1.0,
    "runtime": 1.35,
    "coverage": 1.15,
    "dynamic_exec": 1.25,
    "call_graph": 1.15,
    "static_text": 0.80,
    "metrics": 1.0,
    "AST-verification": 1.15,
    "history": 0.85,
    "human_confirmation": 1.50,
    "log_analysis": 1.0,
    "type_check": 1.0,
    "test_quality": 1.15,
    "bidirectional_taint": 1.25,
    "llm_cv": 1.0,
    "baseline": 0.90,
    "business_flow": 1.15,
    "ref_depth": 1.0,
    "ensemble": 1.15,
    "mutation": 1.30,
    "hallucination": 1.25,
}
EVIDENCE_FAMILY_NAMES: tuple[str, ...] = tuple(sorted(_INITIAL_EVIDENCE_WEIGHTS))
_EVIDENCE_WEIGHT_DB: dict[str, dict[str, Any]] = {}
_EVIDENCE_WEIGHT_DB_LOCK = threading.Lock()
_EVIDENCE_WEIGHTS_FILENAME = "evidence_weights.json"
_DEFAULT_METHOD_ID = ""
_DEFAULT_EVENT_WEIGHT = 1.0
_DEFAULT_PERSIST = True
def _weights_file_in(jinhua_dir: str) -> str:
    return os.path.join(jinhua_dir, _EVIDENCE_WEIGHTS_FILENAME) if jinhua_dir else ""
_EVIDENCE_DB_LOADED_PATH: str | None = None
_EVIDENCE_DB_LOAD_FAILED: bool = False
_EVIDENCE_WEIGHT_DB_PATH: str | None = None
def _evidence_db_path() -> str:
    global _EVIDENCE_WEIGHT_DB_PATH
    if _EVIDENCE_WEIGHT_DB_PATH is None:
        _EVIDENCE_WEIGHT_DB_PATH = ""
    return _EVIDENCE_WEIGHT_DB_PATH
_LEARNING_SKILL_DIR = ""
_REVIEWED_FP_RULES: set[str] = set()
_UNREVIEWED_SUPPRESSED: dict[str, int] = {}
def _refresh_reviewed_fp_rules() -> None:
    """加载「已复核误报规则」集合。

    只有过了 ``audit_fp_mask``（全量逐条 + 固定比例抽样）复核并固化进
    ``fp_rules.json`` 的规则才算“确认误报”—— ``fixate_fp_rules`` 会给它们
    写 ``_fp_keys`` 身份账本。CV 的 rule4 自动抑制没有这一步复核，直接当
    误报学习会让错误抑制自我强化（阈值上调 → 真问题更难检出）。
    """
    _REVIEWED_FP_RULES.clear()
    if not _LEARNING_SKILL_DIR:
        return
    try:
        path = fp_rules_path(_LEARNING_SKILL_DIR)
        if not os.path.isfile(path):
            return
        with open(path, encoding="utf-8-sig", errors="replace") as handle:
            document = json.load(handle)
    except (OSError, ValueError, TypeError, RecursionError) as exc:
        log_swallowed(__name__, exc, context="reviewed_fp_rules:load")
        return
    rules = document.get("rules") if isinstance(document, dict) else document
    if isinstance(rules, dict):
        entries = list(rules.items())
    elif isinstance(rules, list):
        entries = [
            (item.get("rule_id"), item)
            for item in rules if isinstance(item, dict)]
    else:
        return
    for key, entry in entries:
        if not isinstance(entry, dict):
            continue
        rid = str(entry.get("rule_id") or key or "").strip()
        keys = entry.get("_fp_keys")
        if rid and isinstance(keys, (list, tuple, set, frozenset)) and keys:
            _REVIEWED_FP_RULES.add(rid)
def is_fp_rule_reviewed(rule_id: Any) -> bool:
    """规则是否已过误报复核（只有复核过的抑制才能作为负样本学习）。"""
    rid = str(rule_id or "").strip()
    return bool(rid) and rid in _REVIEWED_FP_RULES
def unreviewed_suppression_stats() -> dict[str, int]:
    """未复核抑制的累计计数（观测用：高计数说明复核工作欠账）。"""
    return dict(_UNREVIEWED_SUPPRESSED)
def _count_unreviewed_suppression(rule_id: Any) -> None:
    rid = str(rule_id or "").strip() or "<unknown>"
    _UNREVIEWED_SUPPRESSED[rid] = _UNREVIEWED_SUPPRESSED.get(rid, 0) + 1
    logger.debug(
        "[M5-AdaptiveLearning] %s 的抑制未经复核，本次不计入误报学习"
        "（累计 %d 次）", rid, _UNREVIEWED_SUPPRESSED[rid])
def set_evidence_learning_dir(skill_dir: str) -> None:
    global _EVIDENCE_WEIGHT_DB_PATH, _EVIDENCE_DB_LOADED_PATH
    global _EVIDENCE_DB_LOAD_FAILED, _LEARNING_SKILL_DIR
    skill_dir, _raw_truthy = learning_dir_request(skill_dir)
    try:
        with _EVIDENCE_WEIGHT_DB_LOCK:
            previous_path = _EVIDENCE_WEIGHT_DB_PATH
            previous_loaded_path = _EVIDENCE_DB_LOADED_PATH
            previous_db = dict(_EVIDENCE_WEIGHT_DB)
            previous_failed = _EVIDENCE_DB_LOAD_FAILED
            try:
                if skill_dir and os.path.isdir(skill_dir):
                    _db_dir = os.path.dirname(
                        evidence_weights_path(skill_dir))
                    os.makedirs(_db_dir, exist_ok=True)
                    _EVIDENCE_WEIGHT_DB_PATH = _weights_file_in(_db_dir)
                elif _raw_truthy:
                    logger.warning(
                        "[Evidence] 学习目录无效或不存在(%r)，进入纯内存模式",
                        skill_dir or type(skill_dir).__name__)
                    _EVIDENCE_WEIGHT_DB_PATH = ""
                else:
                    _EVIDENCE_WEIGHT_DB_PATH = ""
                _EVIDENCE_WEIGHT_DB.clear()
                _EVIDENCE_DB_LOADED_PATH = None
                _LEARNING_SKILL_DIR = skill_dir
                _load_evidence_weights()
                _refresh_reviewed_fp_rules()
            except Exception:
                _EVIDENCE_WEIGHT_DB_PATH = previous_path
                _EVIDENCE_DB_LOADED_PATH = previous_loaded_path
                _EVIDENCE_WEIGHT_DB.clear()
                _EVIDENCE_WEIGHT_DB.update(previous_db)
                _EVIDENCE_DB_LOAD_FAILED = previous_failed
                raise
    except (OSError, PermissionError, RuntimeError) as e:
        logger.warning("[Evidence] set_evidence_learning_dir 失败，保持原路径: %s", e)
_AVAILABLE_METHODS: set[str] | None = None
def set_available_methods(methods) -> None:
    global _AVAILABLE_METHODS
    if methods is None:
        _AVAILABLE_METHODS = None
        return
    if isinstance(methods, (str, bytes, bytearray)):
        methods = (methods,)
    if not isinstance(methods, (list, tuple, set, frozenset)):
        try:
            methods = list(methods)
        except TypeError as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc,
                context='set_available_methods:TypeError')
            methods = ()
    _AVAILABLE_METHODS = set(_dedup_sources(methods))
def available_methods() -> set[str] | None:
    return None if _AVAILABLE_METHODS is None else set(_AVAILABLE_METHODS)
def _get_platform_confidence_ceiling() -> float:
    available = available_methods()
    producing = {
        mid for mid, cfg in METHOD_REGISTRY.items() if cfg.produces_findings}
    total = len(producing)
    if available is None:
        return CONF_CAP
    if not available or total == 0:
        return 0.50
    ratio = len(available & producing) / total
    return round(min(0.50 + ratio * 0.45, CONF_CAP), 3)
def _read_evidence_db_file(db_path: str) -> dict:
    with open(db_path, encoding="utf-8-sig") as f:
        _loaded = json.load(f)
    if not isinstance(_loaded, dict):
        raise TypeError(
            f"证据权重文件顶层非 dict: {type(_loaded).__name__}")
    return _loaded
_DEFAULT_EVIDENCE_WEIGHT: float = 1.0
_FP_RATE_SLOPE: float = 5.0
_FP_RATE_PENALTY_SLOPE: float = 3.0
_OBSERVED_WEIGHT_FLOOR: float = 0.5
_OBSERVED_WEIGHT_CEILING: float = 1.0 + FP_RATE_VERY_LOW * _FP_RATE_SLOPE
_FAMILY_WEIGHT_MULTIPLIER_CAP: float = 1.4
_RECORD_DEFAULTS = {
    "weight": _DEFAULT_EVIDENCE_WEIGHT, "hits": 0, "fp": 0, "last_update": 0}
_COUNT_RECORD_FIELDS = ("hits", "fp")
_VALIDATED_RECORD_FIELDS = (*_COUNT_RECORD_FIELDS, "last_update")
def _is_bad_record_field(field_name: str, value) -> bool:
    if not is_real_number(value):
        return True
    return field_name in _COUNT_RECORD_FIELDS and value < 0
def _bad_record_keys(loaded: dict) -> list:
    return [
        k for k, v in loaded.items()
        if not isinstance(v, dict)
        or any(
            _is_bad_record_field(_kk, v[_kk])
            for _kk in _VALIDATED_RECORD_FIELDS if _kk in v)
    ]
def _filter_bad_records(loaded: dict, db_path: str) -> dict:
    _bad_keys = _bad_record_keys(loaded)
    for _k in _bad_keys:
        logger.warning(
            "xv_evidence: 证据权重记录非法(%r)，剔除该条目: %s",
            _k, db_path)
        loaded.pop(_k)
    return loaded
def _load_evidence_weights() -> None:
    global _EVIDENCE_DB_LOADED_PATH, _EVIDENCE_DB_LOAD_FAILED
    _db_path = _evidence_db_path()
    if _db_path == _EVIDENCE_DB_LOADED_PATH:
        return
    _EVIDENCE_DB_LOADED_PATH = _db_path
    _EVIDENCE_DB_LOAD_FAILED = False
    _EVIDENCE_WEIGHT_DB.clear()
    if _db_path and os.path.exists(_db_path):
        try:
            _loaded = _read_evidence_db_file(_db_path)
            _EVIDENCE_WEIGHT_DB.update(
                _filter_bad_records(_loaded, _db_path))
        except (json.JSONDecodeError, UnicodeDecodeError, OSError, TypeError,
                RecursionError, MemoryError) as e:
            _EVIDENCE_DB_LOAD_FAILED = True
            logger.warning("xv_evidence: 证据权重加载失败，降级空库: %s (%s)", _db_path, e)
def _save_evidence_weights() -> None:
    _db_path = _evidence_db_path()
    if not _db_path:
        return
    if _EVIDENCE_DB_LOAD_FAILED:
        logger.warning(
            "xv_evidence: 历史权重库未能读取，跳过本次落盘以免覆盖历史: %s",
            _db_path)
        return
    if not _EVIDENCE_WEIGHT_DB and _has_payload_on_disk(_db_path):
        logger.warning(
            "xv_evidence: 内存权重库为空但磁盘库有数据，跳过本次落盘以免清空历史: %s",
            _db_path)
        return
    _tmp_path = (f"{_db_path}.{os.getpid()}.{threading.get_ident()}."
                 f"{time.time_ns()}.tmp")
    try:
        with locked_artifact(_db_path) as locked:
            if not locked:
                logger.warning(
                    "xv_evidence: 权重库写锁不可用，跳过本次落盘: %s", _db_path)
                return
            _merged = _merged_weights_for_save(_db_path)
            if _merged is None:
                logger.warning(
                    "xv_evidence: 权重库锁内重读失败，跳过本次落盘: %s",
                    _db_path)
                return
            with open(_tmp_path, "w", encoding="utf-8") as f:
                json.dump(_merged, f, indent=2, default=str)
                f.flush()
                os.fsync(f.fileno())
            replace_with_retry(_tmp_path, _db_path)
    except Exception:
        logger.warning("xv_evidence: _save_evidence_weights failed", exc_info=True)
        safe_delete(_tmp_path)
def _merged_weights_for_save(db_path: str) -> dict | None:
    """锁内重读磁盘，保留其他进程/项目在本次学习期间新增的证据类型。

    证据权重库是跨目标共享账本；若直接拿内存快照覆盖，后写者会丢掉前者
    刚落的条目。同一证据类型的并发更新按最后写入胜出（LWW），不同 key 的
    更新全部保留。现存账本不可读或结构非法时返回 None，由调用方取消写盘。
    """
    merged: dict = {}
    try:
        if os.path.isfile(db_path):
            loaded = _read_evidence_db_file(db_path)
            merged.update(_filter_bad_records(loaded, db_path))
    except (json.JSONDecodeError, UnicodeDecodeError, OSError, TypeError,
            RecursionError, MemoryError) as e:
        logger.warning(
            "xv_evidence: 落盘前重读失败，禁止按内存库覆盖历史: %s (%s)",
            db_path, e)
        return None
    merged.update(_EVIDENCE_WEIGHT_DB)
    return merged
def _has_payload_on_disk(db_path: str) -> bool:
    try:
        return os.path.getsize(db_path) > 0
    except OSError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc, context='_has_payload_on_disk:OSError')
        return False
def _evidence_weight_key(
        family_name: str, method_id: str = _DEFAULT_METHOD_ID) -> str:
    return f"{method_id}:{family_name}" if method_id else family_name
def _canonical_family_name(family_name: str) -> str:
    return RULE_FAMILY_TO_FAMILY.get(family_name, family_name)
def family_reliability_base(family_name: str) -> float:
    if not isinstance(family_name, str):
        return _DEFAULT_EVIDENCE_WEIGHT
    _ev_family = _canonical_family_name(family_name.strip())
    return _INITIAL_EVIDENCE_WEIGHTS.get(
        _ev_family, _DEFAULT_EVIDENCE_WEIGHT)
def _fp_rate_weight(fp_rate: float) -> float:
    if fp_rate < FP_RATE_VERY_LOW:
        return min(
            _OBSERVED_WEIGHT_CEILING,
            1.0 + (FP_RATE_VERY_LOW - fp_rate) * _FP_RATE_SLOPE)
    if fp_rate > FP_RATE_HIGH:
        return max(
            _OBSERVED_WEIGHT_FLOOR,
            1.0 - (fp_rate - FP_RATE_HIGH) * _FP_RATE_PENALTY_SLOPE)
    return 1.0
_COLD_START_MIN_SAMPLES = 5
def _cold_start_weight(family_name: str, hits: float, fp: float) -> float:
    initial = family_reliability_base(family_name)
    observed = _fp_rate_weight(min(1.0, max(0.0, fp / max(hits, 1.0))))
    sample_ratio = min(1.0, max(0.0, hits / _COLD_START_MIN_SAMPLES))
    return round(
        initial * (1.0 - sample_ratio) + observed * sample_ratio, 3)
def _lookup_weight_record(family_name: str, method_id: str) -> dict | None:
    _fine_key = _evidence_weight_key(family_name, method_id)
    record = _EVIDENCE_WEIGHT_DB.get(_fine_key)
    if record is None and _fine_key != family_name:
        record = _EVIDENCE_WEIGHT_DB.get(family_name)
    return record
def get_evidence_family_weight(
        family_name: str, method_id: str = _DEFAULT_METHOD_ID) -> float:
    if not isinstance(family_name, str):
        return _DEFAULT_EVIDENCE_WEIGHT
    raw_family_name = family_name.strip()
    canonical_family_name = _canonical_family_name(raw_family_name)
    method_id = method_id.strip() if isinstance(method_id, str) else ""
    try:
        with _EVIDENCE_WEIGHT_DB_LOCK:
            if not _EVIDENCE_WEIGHT_DB:
                _load_evidence_weights()
            record = _lookup_weight_record(canonical_family_name, method_id)
            if record is None and canonical_family_name != raw_family_name:
                record = _lookup_weight_record(raw_family_name, method_id)
            if not record:
                return family_reliability_base(canonical_family_name)
            return _record_dynamic_weight(record, canonical_family_name)
    except Exception:
        logger.exception("[get_evidence_family_weight] 异常降级")
    return _DEFAULT_EVIDENCE_WEIGHT
def evidence_channel_scale(family: str) -> float:
    w = get_evidence_family_weight(family)
    if not is_real_number(w):
        return 1.0
    return max(_OBSERVED_WEIGHT_FLOOR,
               min(_OBSERVED_WEIGHT_CEILING, float(w)))
DEPTH_CONFIDENCE_BOOST_CAP = 0.15
DEPTH_PRIORITY_BOOST_CAP = 3
ISOLATED_CONFIDENCE_PENALTY = 0.10
_DEEP_CHAIN_MIN = 10
_MID_CHAIN_MIN = 5
_HIGH_IN_DEGREE_MIN = 5
_CHAIN_DEPTH_PER_PRIORITY = 5
_IN_DEGREE_PER_PRIORITY = 5
_IN_DEGREE_PRIORITY_CAP = 2
_ENTRY_CONF_PER_CALLER = 0.03
_CHAIN_CONF_PER_DEPTH = 0.015
_IN_DEGREE_CONF_PER_CALLER = 0.02
def vcs_recency_confidence_boost() -> float:
    return CONF_BOOST_MODERATE * evidence_channel_scale("vcs_recency")
def test_triage_confidence_boost(smoke: str) -> float:
    if smoke == "pass":
        return CONF_BOOST_SMALL * evidence_channel_scale("test_triage_smoke_pass")
    if smoke == "fail":
        return CONF_BOOST_SMALL * evidence_channel_scale("test_triage")
    return 0.0
def counter_evidence_confidence_penalty() -> float:
    return CONF_PENALTY_MODERATE * evidence_channel_scale("counter_evidence")
def business_flow_confidence_boost(reachable: bool, dead_code: bool,
                                   entry_count: int) -> float:
    _entry_count = max(0, safe_int(entry_count, 0))
    if reachable:
        if dead_code:
            return -CONF_PENALTY_MODERATE
        return min(_entry_count * CONF_BOOST_SMALL, CONF_BOOST_MODERATE)
    return CONF_BOOST_MODERATE if dead_code else 0.0
def refdepth_boosts(in_degree: int, chain_depth: int, is_entry: bool,
                    is_isolated: bool) -> tuple[int, float]:
    _in_degree = max(0, safe_int(in_degree, 0))
    _chain_depth = max(0, safe_int(chain_depth, 0))
    if is_isolated:
        return -1, -ISOLATED_CONFIDENCE_PENALTY
    if is_entry:
        return 0, min(_in_degree * _ENTRY_CONF_PER_CALLER, CONF_BOOST_STEP)
    if _chain_depth >= _DEEP_CHAIN_MIN:
        return (min(_chain_depth // _CHAIN_DEPTH_PER_PRIORITY,
                    DEPTH_PRIORITY_BOOST_CAP),
                min(_chain_depth * _CHAIN_CONF_PER_DEPTH,
                    DEPTH_CONFIDENCE_BOOST_CAP))
    if _chain_depth >= _MID_CHAIN_MIN:
        return 1, CONF_BOOST_SMALL
    if _in_degree >= _HIGH_IN_DEGREE_MIN:
        return (min(_in_degree // _IN_DEGREE_PER_PRIORITY,
                    _IN_DEGREE_PRIORITY_CAP),
                min(_in_degree * _IN_DEGREE_CONF_PER_CALLER, CONF_BOOST_STEP))
    return 0, 0.0
_RESULT_MISSING = object()
def _result_field(result, name: str, default):
    if isinstance(result, dict):
        value = result.get(name, _RESULT_MISSING)
    else:
        value = getattr(result, name, _RESULT_MISSING)
    return default if value is _RESULT_MISSING or value is None else value
def bizflow_signal_payload(result, unresolved: bool = True) -> dict[str, Any]:
    if result is None:
        return {
            "_bizflow_reachable": False,
            "_bizflow_entry_count": 0,
            SIGNAL_BIZFLOW_CONFIDENCE_BOOST: 0.0,
            "_bizflow_fp_candidate": False,
            "_bizflow_function_name": "",
            "_bizflow_impacted_entries": [],
            "_bizflow_unresolved": unresolved,
        }
    return {
        "_bizflow_reachable": signal_bool(
            _result_field(result, "reachable", False)),
        "_bizflow_entry_count": safe_int(
            _result_field(result, "entry_count", 0), 0),
        SIGNAL_BIZFLOW_CONFIDENCE_BOOST: safe_float(
            _result_field(result, "confidence_boost", 0.0), 0.0),
        "_bizflow_fp_candidate": signal_bool(
            _result_field(result, "is_false_positive_candidate", False)),
        "_bizflow_function_name": safe_str(
            _result_field(result, "function_name", "")),
        "_bizflow_impacted_entries": coerce_text_list(
            _result_field(result, "impacted_entry_points", []))[:5],
        "_bizflow_unresolved": unresolved,
    }
def refdepth_signal_payload(result) -> dict[str, Any]:
    if result is None:
        return {
            SIGNAL_REFDEPTH_IN_DEGREE: 0,
            SIGNAL_REFDEPTH_CHAIN_DEPTH: 0,
            SIGNAL_REFDEPTH_ISOLATED: False,
            SIGNAL_REFDEPTH_PRIORITY_BOOST: 0,
            SIGNAL_REFDEPTH_CONFIDENCE_BOOST: 0.0,
            "_refdepth_function_name": "",
            "_refdepth_is_entry_point": False,
        }
    return {
        SIGNAL_REFDEPTH_IN_DEGREE: safe_int(
            _result_field(result, "in_degree", 0), 0),
        SIGNAL_REFDEPTH_CHAIN_DEPTH: safe_int(
            _result_field(result, "call_chain_depth", 0), 0),
        SIGNAL_REFDEPTH_ISOLATED: signal_bool(
            _result_field(result, "is_isolated", False)),
        SIGNAL_REFDEPTH_PRIORITY_BOOST: safe_int(
            _result_field(result, "priority_boost", 0), 0),
        SIGNAL_REFDEPTH_CONFIDENCE_BOOST: safe_float(
            _result_field(result, "confidence_boost", 0.0), 0.0),
        "_refdepth_function_name": safe_str(
            _result_field(result, "function_name", "")),
        "_refdepth_is_entry_point": signal_bool(
            _result_field(result, "is_entry_point", False)),
    }
def _normalized_event_weight(event_weight) -> float:
    try:
        _w = float(event_weight)
    except (TypeError, ValueError, OverflowError) as e:
        logger.debug("[EvidenceWeight] event_weight 解析失败（%r），回退全强度 1.0", e)
        return _DEFAULT_EVENT_WEIGHT
    return (_w if _w > 0.0 and math.isfinite(_w)
            else _DEFAULT_EVENT_WEIGHT)
_DECAY_FACTOR = 0.95
_DECAY_INTERVAL = 3600
def _ensure_weight_record(family_name: str, method_id: str) -> dict:
    _wkey = _evidence_weight_key(family_name, method_id)
    rec = _EVIDENCE_WEIGHT_DB.get(_wkey)
    if not isinstance(rec, dict):
        rec = dict(_RECORD_DEFAULTS)
        _EVIDENCE_WEIGHT_DB[_wkey] = rec
        return rec
    for _field, _default in _RECORD_DEFAULTS.items():
        rec.setdefault(_field, _default)
    return rec
def _apply_time_decay(rec: dict, now: int) -> None:
    last_update = int(max(0.0, safe_float(rec.get("last_update", 0), 0.0)))
    if last_update > 0 and (now - last_update) >= _DECAY_INTERVAL:
        decay_rounds = (now - last_update) // _DECAY_INTERVAL
        decay = _DECAY_FACTOR ** decay_rounds
        _prev_hits = max(0.0, safe_float(rec.get("hits", 0), 0.0))
        rec["hits"] = _prev_hits * decay
        _prev_fp = max(0.0, safe_float(rec.get("fp", 0), 0.0))
        rec["fp"] = _prev_fp * decay
def _record_dynamic_weight(rec: dict, family_name: str) -> float:
    _hits = max(0.0, safe_float(rec.get("hits", 0), 0.0))
    _fp = max(0.0, safe_float(rec.get("fp", 0), 0.0))
    if _hits >= _COLD_START_MIN_SAMPLES:
        _fp_rate = min(1.0, max(0.0, _fp / max(_hits, 1.0)))
        return _fp_rate_weight(_fp_rate)
    return _cold_start_weight(family_name, _hits, _fp)
def _recompute_weight(rec: dict, family_name: str) -> None:
    rec["weight"] = round(_record_dynamic_weight(rec, family_name), 3)
def update_evidence_family_weight(
        family_name: str, confirmed: bool = True,
        method_id: str = _DEFAULT_METHOD_ID,
        event_weight: float = _DEFAULT_EVENT_WEIGHT,
        *, persist: bool = _DEFAULT_PERSIST) -> None:
    if not isinstance(family_name, str) or not family_name.strip():
        logger.debug("[EvidenceWeight] 非法证据家族名(%r)，跳过更新", family_name)
        return
    family_name = _canonical_family_name(family_name.strip())
    method_id = method_id.strip() if isinstance(method_id, str) else ""
    try:
        _ev_w = _normalized_event_weight(event_weight)
        with _EVIDENCE_WEIGHT_DB_LOCK:
            _load_evidence_weights()
            rec = _ensure_weight_record(family_name, method_id)
            now = int(time.time())
            _apply_time_decay(rec, now)
            rec["hits"] = max(
                0.0, safe_float(rec.get("hits", 0), 0.0)) + _ev_w
            if not confirmed:
                rec["fp"] = max(
                    0.0, safe_float(rec.get("fp", 0), 0.0)) + _ev_w
            _recompute_weight(rec, family_name)
            rec["last_update"] = now
            if persist:
                _save_evidence_weights()
    except Exception:
        logger.exception("[update_evidence_family_weight] 异常降级")
def _family_weight_averages(indep_sources: list, resolve_family) -> list[float]:
    _fam_weight_sum: dict[str, float] = {}
    _fam_source_cnt: dict[str, int] = {}
    for s in indep_sources:
        if not isinstance(s, str):
            continue
        _fam = resolve_family(s)
        if not _fam:
            continue
        _fam_weight_sum[_fam] = (
            _fam_weight_sum.get(_fam, 0.0)
            + get_evidence_family_weight(_fam, method_id=s))
        _fam_source_cnt[_fam] = _fam_source_cnt.get(_fam, 0) + 1
    return [
        _fam_weight_sum[_fam] / _fam_source_cnt[_fam]
        for _fam in _fam_weight_sum
    ]
def _apply_family_weights(base: float, fam_weights: list[float]) -> float:
    if not fam_weights:
        return round(min(base, 1.0), 3)
    avg_weight = sum(fam_weights) / len(fam_weights)
    multiplier = max(_OBSERVED_WEIGHT_FLOOR,
                     min(_FAMILY_WEIGHT_MULTIPLIER_CAP, avg_weight))
    adjusted = min(base * multiplier, _get_platform_confidence_ceiling())
    return round(min(adjusted, 1.0), 3)
def _evidence_strength_with_resolver(
        source_ids: list[str], degraded_sources: dict | None,
        resolver) -> float:
    indep_sources, fam_sources, ladder = _ladder_base_of(
        source_ids, degraded_sources, resolver)
    base = _base_with_bonus(indep_sources, fam_sources, ladder)
    if not indep_sources or not any(fam_sources.values()):
        return base
    fam_weights = _family_weight_averages(indep_sources, resolver)
    if not fam_weights:
        return base
    return _apply_family_weights(base, fam_weights)
def evidence_strength_weighted(source_ids: list[str], degraded_sources: dict | None = None) -> float:
    try:
        source_ids = _dedup_sources(source_ids)
        return _evidence_strength_with_resolver(
            source_ids, degraded_sources, family_of_source)
    except Exception:
        logger.exception("[evidence_strength_weighted] 异常降级")
        return CONF_FLOOR
def _finding_method_family(f) -> tuple[str, str] | None:
    if not isinstance(f, dict):
        return None
    m = _source_id_text(f.get("_source_method"))
    rf = f.get("rule_family")
    rf = rf.strip() if isinstance(rf, str) else ""
    if not m or not rf:
        return None
    return m, rf
def _collect_method_family_counts(findings: list) -> dict:
    counts: dict = {}
    _seq = 0
    for f in findings:
        pair = _finding_method_family(f)
        if pair is None:
            continue
        m, rf = pair
        per = counts.setdefault(m, {})
        if rf not in per:
            per[rf] = [0, _seq]
            _seq += 1
        per[rf][0] += 1
    return counts
def dominant_rule_family_by_method(findings) -> dict:
    if findings is None or isinstance(findings, (str, bytes)):
        return {}
    try:
        iter(findings)
    except TypeError as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context='dominant_rule_family_by_method:TypeError')
        return {}
    counts = _collect_method_family_counts(findings)
    return {
        m: min(per.items(), key=lambda kv: (-kv[1][0], kv[1][1]))[0]
        for m, per in counts.items()
    }
def _resolve_source_family(s: str, method_rf_map) -> str | None:
    rf = method_rf_map.get(s, "") if isinstance(method_rf_map, dict) else ""
    if isinstance(rf, str) and rf:
        if rf in _INITIAL_EVIDENCE_WEIGHTS:
            return rf
        fam = RULE_FAMILY_TO_FAMILY.get(rf, "")
        if fam:
            return fam
    return family_of_source(s)
def _normalized_method_rule_families(method_rf_map) -> dict:
    if not isinstance(method_rf_map, dict):
        return {}
    normalized = {}
    for source, rule_family in method_rf_map.items():
        _sid = _source_id_text(source)
        if _sid and _sid not in normalized:
            normalized[_sid] = (
                rule_family.strip() if isinstance(rule_family, str)
                else rule_family)
    return normalized
def evidence_strength_by_rule_family(method_rf_map: dict, source_ids: list[str],
                                     degraded_sources: dict | None = None) -> float:
    method_rf_map = _normalized_method_rule_families(method_rf_map)
    source_ids = _dedup_sources(source_ids)
    def _resolver(source: str) -> str | None:
        return _resolve_source_family(source, method_rf_map)
    return _evidence_strength_with_resolver(
        source_ids, degraded_sources, _resolver)
def update_rule_weights(xv_results: Any) -> None:
    _learned = False
    try:
        for xvr in xv_results:
            try:
                if not isinstance(xvr, dict):
                    logger.warning("[M5-AdaptiveLearning] xv_results 含非 dict 元素(%s)，跳过该条", type(xvr).__name__)
                    continue
                _learned = _learn_from_locator(xvr, persist=False) or _learned
            except Exception as _e:  # noqa: BLE001
                logger.warning("[M5-AdaptiveLearning] skipped: %s", _e)
    except Exception as _e:  # noqa: BLE001
        logger.warning("[M5-AdaptiveLearning] skipped: %s", _e)
    finally:
        if _learned:
            _save_evidence_weights()
def _learn_source_families(xvr: dict, is_fp: bool, ev_w: float) -> None:
    _srcs = xvr.get("sources", [])
    for _s in _dedup_sources(_srcs):
        _fam_name = family_of_source(_s)
        if _fam_name is not None:
            for method_id in ("", _s):
                update_evidence_family_weight(
                    _fam_name, confirmed=not is_fp, method_id=method_id,
                    event_weight=ev_w, persist=False)
def _record_signal_channel(channel: str, is_pos_ch: bool, is_neg_ch: bool,
                           pos_w: float, *, positive_hit: bool) -> None:
    if positive_hit:
        _hit_side, _miss_side = is_pos_ch, is_neg_ch
        _hit_weight, _miss_weight = pos_w, 1.0
    else:
        _hit_side, _miss_side = is_neg_ch, is_pos_ch
        _hit_weight, _miss_weight = 1.0, pos_w
    if _hit_side:
        update_evidence_family_weight(
            channel, event_weight=_hit_weight, persist=False)
    elif _miss_side:
        update_evidence_family_weight(
            channel, confirmed=False, event_weight=_miss_weight,
            persist=False)
_SIGNAL_CHANNELS: tuple[tuple[str, str, bool, bool], ...] = (
    ("_vcs_recency_boost", "vcs_recency", True, False),
    ("_counter_evidence", "counter_evidence", False, False),
    ("_test_triage_smoke_fail", "test_triage", True, True),
    ("_test_triage_smoke_pass", "test_triage_smoke_pass", False, True),
)
def _channel_applies(finding: dict, signal_key: str, needs_precise: bool,
                     precise_smoke: bool) -> bool:
    return signal_bool(finding.get(signal_key)) and (
        not needs_precise or precise_smoke)
def _learn_signal_channels(xvr: dict, is_confirmed: bool, is_fp: bool,
                            effective_conclusion: str) -> None:
    is_pos_ch = effective_conclusion in ("confirmed", "likely")
    is_neg_ch = is_fp
    pos_w = 1.0 if is_confirmed else 0.5
    findings = xvr.get("findings", [])
    if not isinstance(findings, (list, tuple)):
        return
    learned_channels = set()
    for finding in findings:
        if not isinstance(finding, dict):
            continue
        precise_smoke = (
            str(finding.get("rule_family", "")) in PRECISE_SMOKE_FAMILIES)
        for signal_key, channel, positive_hit, needs_precise in _SIGNAL_CHANNELS:
            if not _channel_applies(
                    finding, signal_key, needs_precise, precise_smoke):
                continue
            if channel in learned_channels:
                continue
            learned_channels.add(channel)
            _record_signal_channel(
                channel, is_pos_ch, is_neg_ch, pos_w,
                positive_hit=positive_hit)
def _effective_conclusion(xvr: dict) -> str:
    for _key in ("conclusion_v2", "conclusion"):
        _val = xvr.get(_key)
        if not isinstance(_val, str):
            continue
        _val = _val.strip().lower()
        if _val in CONCLUSION_V2_MAP:
            return _val
    return ""
def _learn_from_locator(
        xvr: dict, *, persist: bool = _DEFAULT_PERSIST) -> bool:
    _concl = _effective_conclusion(xvr)
    _is_confirmed = _concl == "confirmed"
    _is_likely = _concl == "likely"
    _is_fp = _concl == "suppressed"
    if not _is_confirmed and not _is_fp and not _is_likely:
        return False
    _rid = xvr.get("rule_applied", "")
    if _is_fp and not is_fp_rule_reviewed(_rid):
        # 自动抑制不是“确认误报”：只有过了 audit_fp_mask 复核的规则才计负
        # 样本（由 fixate_fp_rules 在复核通过时回写）。未复核抑制只记一次
        # 中性 hit（表示规则被触发），既不记 fp 也不记 confirmed——否则要么
        # 错误抑制自我强化，要么被当成正样本反向放大。证据族/信号通道同样
        # 跳过，避免任何单向漂移。
        _count_unreviewed_suppression(_rid)
        if _rid:
            record_threshold_outcome(
                _rid, confirmed=False, was_false_positive=False)
        return True
    if _rid:
        record_threshold_outcome(
            _rid, confirmed=_is_confirmed, was_false_positive=_is_fp)
    _ev_w = 1.0 if _concl in ("confirmed", "suppressed") else 0.5
    _learn_source_families(xvr, _is_fp, _ev_w)
    _learn_signal_channels(xvr, _is_confirmed, _is_fp, _concl)
    if persist:
        _save_evidence_weights()
    return True
def sub_engine_meta(source) -> dict:
    if not isinstance(source, str) or not source:
        return {}
    meta = SUB_ENGINE_META.get(source)
    return meta if isinstance(meta, dict) else {}
def source_main_id(source) -> str:
    main = sub_engine_meta(source).get("main")
    return main if isinstance(main, str) and main else ""
def source_family_names(sources) -> set[str]:
    families: set[str] = set()
    for _s in _dedup_sources(sources):
        family = family_of_source(_s)
        if family is not None:
            families.add(family)
    return families
_VIRTUAL_SOURCE_IDS = frozenset({
    "SE-20",
    "H1_API",
    "HUMAN_CONFIRM",
    "BI_TAINT_FORWARD",
    "BI_TAINT_BACKWARD",
    "LLM_CV",
    "B3",
    "M1",
})
def _known_source_ids() -> frozenset[str]:
    return (frozenset(METHOD_REGISTRY) | frozenset(SUB_ENGINE_META)
            | _VIRTUAL_SOURCE_IDS)
def _normalized_evidence_types(value) -> set[str]:
    if isinstance(value, str):
        return {value} if value else set()
    if not isinstance(value, (list, tuple, set, frozenset)):
        return set()
    return {item for item in value if isinstance(item, str) and item}
def evidence_types_of(source) -> set[str]:
    direct = _normalized_evidence_types(
        safe_dict_get(METHOD_EVIDENCE_TYPES, source, None))
    if direct:
        return direct
    types = _normalized_evidence_types(sub_engine_meta(source).get("types"))
    if types:
        return types
    main = source_main_id(source)
    if main and main != source:
        return _normalized_evidence_types(
            safe_dict_get(METHOD_EVIDENCE_TYPES, main, None))
    return set()
def evidence_meta(sources) -> tuple[list, str]:
    sources = _dedup_sources(sources)
    families = source_family_names(sources)
    ev_types_collected = set()
    for s in sources:
        ev_types_collected.update(evidence_types_of(s))
    ev_type_str = ("/".join(sorted(ev_types_collected))
                   if ev_types_collected else "unknown")
    return sorted(families), ev_type_str
def validate_source_family_consistency() -> list[str]:
    issues: list[str] = []
    try:
        _registry_methods = set(METHOD_REGISTRY.keys())
        orphans = []
        conflicts = []
        for fam_name, members in SOURCE_FAMILIES.items():
            for m in members:
                if m not in _registry_methods and m not in _VIRTUAL_SOURCE_IDS:
                    orphans.append((fam_name, m))
                    continue
                resolved = family_of_source(m, use_override=False)
                if resolved is not None and resolved != fam_name:
                    conflicts.append((fam_name, m, resolved))
        if orphans:
            logger.warning(
                "[G07] SOURCE_FAMILIES 中有 %d 个方法不在 METHOD_REGISTRY: %s",
                len(orphans), orphans[:5])
            issues.extend(
                f"orphan:{fam_name}->{member}"
                for fam_name, member in orphans)
        if conflicts:
            logger.warning(
                "[G07] SOURCE_FAMILIES 存在跨家族重复归属 %d 处: %s",
                len(conflicts), conflicts[:5])
            issues.extend(
                f"conflict:{fam_name}->{member}(resolved:{resolved})"
                for fam_name, member, resolved in conflicts)
    except Exception as e:  # noqa: BLE001
        logger.warning("[G07] 一致性校验异常: %s", e)
        issues.append(f"validator_error:{type(e).__name__}:{e}")
    return issues
validate_source_family_consistency()

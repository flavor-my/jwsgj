from __future__ import annotations

import ast
import io
import keyword
import logging
import os
import re
import symtable
import token as _token
import tokenize
from dataclasses import dataclass, field

from jwsgj.diag_shared_ast_nodes import BUILTIN_NAMES, first_symbol_field
from jwsgj.diag_shared_source_scan import IDENTIFIER_SOURCE
from jwsgj.diag_types_normalize import (
    compact_ts_to_ms,
    env_number,
    extract_symbol,
    finding_file_key,
    finding_file_path,
    make_locator_fast,
)
from jwsgj.diag_types_normalize import (
    safe_finding_line as _safe_finding_line,
)
from jwsgj.diag_types_vocab import (
    CONF_BOOST_SMALL,
    CONF_BOOST_STEP,
    CV_RULES,
    SIGNAL_ENSEMBLE_GROUP_COUNT,
    SIGNAL_ENSEMBLE_LOW_CONFIDENCE,
)
from jwsgj.fix_guide_rule_identity import (
    SECURITY_FAMILY_UNION,
    get_rule_family_set,
    is_family_member,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.shared_cache import peek_warmed_cache
from jwsgj.xv_evidence_strength import (
    _dedup_sources,
    _known_source_ids,
    _source_id_text,
    independent_sources,
    source_main_id,
)

logger = logging.getLogger(__name__)
__all__ = [
    "CAPABILITY_GROUPS",
    "GROUP_DETECTION_AXES",
    "METRICS_SUBGROUP_DECAY_BASE",
    "NEGATIVES_AUDIT_KEY",
    "STALE_MARGIN_S",
    "EnsembleConsensusAnalyzer",
    "EnsembleResult",
    "annotate_findings_with_drift",
    "annotate_findings_with_ensemble",
    "attach_negatives_audit",
    "build_drift_report",
    "build_evidence_chain_audit",
    "cross_locator_consistency_check",
    "method_to_groups",
    "run_negatives_channels",
]
logger.info("xv_evidence_crosscheck 证据交叉核验面已加载: %d 项导出", len(__all__))
_SINGLE_SOURCE_MULTIPLIER: float = 0.75
CAPABILITY_GROUPS: dict[str, set[str]] = {
    "ast_detection": {"A"},
    "runtime": {"E"},
    "call_graph": {"C"},
    "security": {"D"},
    "metrics_complexity": {"B"},
    "coverage": {"E3"},
    "metrics_quality": set(),
    "metrics_gate": set(),
}
METRICS_SUBGROUP_DECAY_BASE: float = min(
    0.99, max(0.0, env_number(
        "JWSGJ_METRICS_DECAY_BASE", 0.3, float
    ))
)
GROUP_DETECTION_AXES: dict[str, str] = {
    "ast_detection":  "syntax_structure",
    "runtime":        "execution_behavior",
    "coverage":       "code_utilization",
    "call_graph":     "dependency_flow",
    "security":       "security_resource",
    "metrics_complexity": "metrics_complexity",
    "metrics_quality":   "metrics_quality",
    "metrics_gate":      "metrics_gate",
}
_DEFAULT_ENSEMBLE_GROUP = "ast_detection"
def _group_of_member(member: str) -> str | None:
    for gname, members in CAPABILITY_GROUPS.items():
        if member in members:
            return gname
    return None
def method_to_groups(method_id: str) -> list[str]:
    try:
        specific = method_id if isinstance(method_id, str) else ""
        group = _group_of_member(specific) if specific else None
        if group is None:
            main = source_main_id(specific) or specific
            group = _group_of_member(main) if main else None
        return [group or _DEFAULT_ENSEMBLE_GROUP]
    except Exception as e:  # noqa: BLE001 - 方法分组失败回退默认组
        logger.warning("[XV] 方法分组失败 in method_to_groups(): %s", e)
        return [_DEFAULT_ENSEMBLE_GROUP]
@dataclass
class EnsembleResult:
    locator: str
    source_methods: list[str] = field(default_factory=list)
    source_groups: list[str] = field(default_factory=list)
    group_count: int = 0
    axis_count: int = 0
    consensus_level: str = "single"
    is_confirmed: bool = False
    is_low_confidence: bool = False
    confidence_multiplier: float = 1.0
    def to_dict(self) -> dict:
        try:
            return {
                "locator": self.locator,
                "source_methods": self.source_methods,
                "source_groups": self.source_groups,
                "group_count": self.group_count,
                "axis_count": self.axis_count,
                "consensus_level": self.consensus_level,
                "is_confirmed": self.is_confirmed,
                "is_low_confidence": self.is_low_confidence,
                "confidence_multiplier": self.confidence_multiplier,
            }
        except Exception as e:  # noqa: BLE001 - 序列化异常返回结构化错误标记
            logger.warning("[XV] ensemble结果序列化失败 in to_dict(): %s", e)
            return {"_error": True, "_partial": True}
_METRICS_SUBGROUPS = frozenset({"metrics_complexity", "metrics_quality", "metrics_gate"})
def _locator_with_valid_line(f: dict) -> str:
    if not isinstance(f, dict):
        return ""
    locator = make_locator_fast(f)
    line_num = _safe_finding_line(f)
    if line_num <= 0:
        return ""
    if not locator.rsplit(":", 2)[0].strip():
        return ""
    return locator
def _index_from_findings_snapshot(findings: list[dict]) -> dict[str, set[str]]:
    method_finding_index: dict[str, set[str]] = {}
    for f in findings:
        locator = _locator_with_valid_line(f)
        if not locator:
            continue
        mid = f.get("_source_method", "")
        if not isinstance(mid, str) or not mid:
            continue
        method_finding_index.setdefault(locator, set()).add(mid)
    return method_finding_index
def _metrics_effective_count(seen_groups: set[str]) -> tuple[float, int]:
    effective_count = 0.0
    metrics_count = 0
    non_metrics_count = 0
    for g in seen_groups:
        if g in _METRICS_SUBGROUPS:
            metrics_count += 1
        else:
            effective_count += 1.0
            non_metrics_count += 1
    if metrics_count >= 2:
        metrics_bonus = sum(
            METRICS_SUBGROUP_DECAY_BASE ** i
            for i in range(1, metrics_count)
        )
        effective_count += 1.0 + metrics_bonus
    elif metrics_count == 1:
        effective_count += 1.0
    return effective_count, non_metrics_count
def _compute_consensus(
    seen_groups: set[str], axis_count: int, method_count: int
) -> tuple:
    group_count = len(seen_groups)
    if group_count < 2 or method_count < 2:
        return ("single", False, True, _SINGLE_SOURCE_MULTIPLIER)
    effective_count, non_metrics_count = _metrics_effective_count(seen_groups)
    if effective_count >= 2.0 and non_metrics_count > 0:
        consensus_level = "cross_group"
        is_confirmed = True
        is_low_confidence = False
        confidence_multiplier = min(1.30, 1.0 + (effective_count - 1) * CONF_BOOST_STEP)
    else:
        consensus_level = "single"
        is_confirmed = False
        is_low_confidence = True
        confidence_multiplier = _SINGLE_SOURCE_MULTIPLIER
    if is_confirmed and axis_count >= 2:
        consensus_level = "multi_axis"
        confidence_multiplier = min(1.30, confidence_multiplier + (axis_count - 1) * CONF_BOOST_SMALL)
    return (consensus_level, is_confirmed, is_low_confidence, confidence_multiplier)
def _no_independent_evidence_result(locator: str) -> EnsembleResult:
    return EnsembleResult(
        locator=locator,
        consensus_level="single",
        is_low_confidence=True,
        confidence_multiplier=_SINGLE_SOURCE_MULTIPLIER,
    )
def _groups_axes_for_methods(source_methods: list[str]) -> tuple:
    source_groups: list[str] = []
    seen_groups: set[str] = set()
    seen_axes: set[str] = set()
    for mid in source_methods:
        for g in method_to_groups(mid):
            if g not in seen_groups:
                seen_groups.add(g)
                source_groups.append(g)
    for g in seen_groups:
        axis = GROUP_DETECTION_AXES.get(g, "")
        if axis:
            seen_axes.add(axis)
    return source_groups, seen_groups, seen_axes
class EnsembleConsensusAnalyzer:
    def _consensus_one_finding(
        self, f: dict, method_finding_index: dict[str, set[str]],
    ) -> EnsembleResult | None:
        if not isinstance(f, dict):
            return None
        locator = _locator_with_valid_line(f)
        if not locator:
            return None
        source_methods = sorted(method_finding_index.get(locator, set()))
        src_method = f.get("_source_method", "")
        if (isinstance(src_method, str) and src_method
                and src_method not in source_methods):
            source_methods.append(src_method)
            source_methods.sort()
        if not source_methods:
            return _no_independent_evidence_result(locator)
        source_methods = independent_sources(source_methods)
        if not source_methods:
            return _no_independent_evidence_result(locator)
        source_groups, seen_groups, seen_axes = _groups_axes_for_methods(source_methods)
        group_count = len(seen_groups)
        axis_count = len(seen_axes)
        consensus_level, is_confirmed, is_low_confidence, confidence_multiplier = \
            _compute_consensus(seen_groups, axis_count, len(source_methods))
        return EnsembleResult(
            locator=locator,
            source_methods=source_methods,
            source_groups=source_groups,
            group_count=group_count,
            axis_count=axis_count,
            consensus_level=consensus_level,
            is_confirmed=is_confirmed,
            is_low_confidence=is_low_confidence,
            confidence_multiplier=confidence_multiplier,
        )
    def analyze(
        self,
        findings: list[dict],
    ) -> dict[str, EnsembleResult]:
        results: dict[str, EnsembleResult] = {}
        try:
            method_finding_index = _index_from_findings_snapshot(findings)
            for f in findings:
                er = self._consensus_one_finding(f, method_finding_index)
                if er is not None:
                    results[er.locator] = er
            logger.info("[Ensemble] %d findings -> %d analyzed, %d cross-group confirmed",
                        len(findings), len(results),
                        sum(1 for r in results.values() if r.is_confirmed))
            return results
        except Exception as e:  # noqa: BLE001 - 信号分析异常返回已处理的部分结果
            logger.warning("[XV] 信号分析失败 in analyze(): %s", e)
            return results
_UNKNOWN_CONSENSUS_LEVEL = "unknown"
def _unknown_ensemble_result(locator: str) -> EnsembleResult:
    return EnsembleResult(
        locator=locator,
        consensus_level=_UNKNOWN_CONSENSUS_LEVEL,
        is_low_confidence=True,
        confidence_multiplier=_SINGLE_SOURCE_MULTIPLIER,
    )
def _apply_ensemble_signal(f: dict, r: EnsembleResult) -> None:
    f[SIGNAL_ENSEMBLE_GROUP_COUNT] = r.group_count
    f["_ensemble_consensus_level"] = r.consensus_level
    f["_ensemble_is_confirmed"] = r.is_confirmed
    f[SIGNAL_ENSEMBLE_LOW_CONFIDENCE] = r.is_low_confidence
    f["_ensemble_confidence_multiplier"] = r.confidence_multiplier
    f["_ensemble_source_groups"] = r.source_groups
def annotate_findings_with_ensemble(
    findings: list[dict],
    ensemble_results: dict[str, EnsembleResult],
) -> list[dict]:
    if not isinstance(findings, (list, tuple)):
        logger.warning(
            "[XV] ensemble注解输入非法(%s)，返回空列表",
            type(findings).__name__)
        return []
    if not isinstance(ensemble_results, dict):
        ensemble_results = {}
    try:
        annotated = []
        for f in findings:
            if not isinstance(f, dict):
                annotated.append(f)
                continue
            locator = make_locator_fast(f)
            r = ensemble_results.get(locator)
            _apply_ensemble_signal(
                f,
                r if isinstance(r, EnsembleResult)
                else _unknown_ensemble_result(locator),
            )
            annotated.append(f)
        return annotated
    except Exception as e:  # noqa: BLE001 - 注解失败返回原始 findings
        logger.warning("[XV] ensemble注解失败 in annotate_findings_with_ensemble(): %s", e)
        return findings
def _declared_sources(xvr: dict) -> set:
    sources = xvr.get("sources")
    return set(_dedup_sources(() if sources is None else sources))
def _evidence_src_methods(xvr: dict) -> set:
    inner = xvr.get("findings")
    if not isinstance(inner, (list, tuple)):
        inner = []
    src_methods = {
        sid for f in inner if isinstance(f, dict)
        for sid in (_source_id_text(f.get("_source_method")),) if sid
    }
    src_methods.update(_declared_sources(xvr))
    _top_src = _source_id_text(xvr.get("_source_method"))
    if _top_src:
        src_methods.add(_top_src)
    return src_methods
def _semantic_mismatch_break(xvr: dict) -> str | None:
    _rule_id = xvr.get("rule_applied", "")
    _rf = xvr.get("rule_family", "")
    if not (_rule_id and _rf):
        return None
    try:
        _rule_cat = getattr(CV_RULES.get(_rule_id), "category", "")
        if (_rule_cat == "safety"
                and not is_family_member(_rf, SECURITY_FAMILY_UNION)):
            return f"semantic_mismatch: rule={_rule_id}(safety) but family={_rf}"
    except Exception as e:  # noqa: BLE001
        logger.warning("[CVAudit] 语义校验异常降级(不阻断): rule=%s family=%s: %s", _rule_id, _rf, e)
    return None
def _evidence_chain_breaks(xvr: dict, src_methods: set) -> list:
    broken = []
    if not src_methods:
        broken.append("no_source_method")
    else:
        _known = _known_source_ids()
        _invalid = [m for m in src_methods if m not in _known]
        if _invalid:
            broken.append(f"invalid_method:{','.join(sorted(_invalid))}")
    if not xvr.get("rule_applied", ""):
        broken.append("no_rule_applied")
    _sm = _semantic_mismatch_break(xvr)
    if _sm:
        broken.append(_sm)
    return broken
def _mark_investigated(xvr: dict) -> None:
    xvr["conclusion"] = "investigated"
    xvr["conclusion_v2"] = "uncertain"
def build_evidence_chain_audit(xv_findings: list) -> dict:
    audit = {
        "total_confirmed": 0, "intact": 0, "broken": 0,
        "broken_details": [],
    }
    entries = _as_entry_list(xv_findings)
    if not entries:
        return audit
    for xvr in entries:
        if not isinstance(xvr, dict):
            continue
        if xvr.get("conclusion") != "confirmed":
            xvr.pop("_evidence_chain_intact", None)
            continue
        xvr.pop("_evidence_chain_broken", None)
        xvr.pop("_evidence_chain_intact", None)
        audit["total_confirmed"] += 1
        src_methods = _evidence_src_methods(xvr)
        broken = _evidence_chain_breaks(xvr, src_methods)
        if broken:
            audit["broken"] += 1
            _mark_investigated(xvr)
            xvr["_evidence_chain_broken"] = broken
            audit["broken_details"].append({
                "locator": xvr.get("locator", ""),
                "broken": broken,
                "rule_applied": xvr.get("rule_applied", ""),
                "source_methods": sorted(src_methods),
            })
        else:
            audit["intact"] += 1
            xvr["_evidence_chain_intact"] = True
    if audit["broken"]:
        logger.warning("[EvidenceChain] %d/%d confirmed 断链降级为 investigated",
                       audit["broken"], audit["total_confirmed"])
    return audit
_SYMBOL_BOUND_CONTRADICTIONS = frozenset({"dead_vs_called", "dead_vs_complex"})
_AFFIRMATIVE_CONCLUSIONS = ("confirmed", "likely")
_DEMOTE_SIDE_A = "a"
_DEMOTE_SIDE_B = "b"
_DEMOTE_BOTH = "both"
_CROSS_LOCATOR_RULES: list[
    tuple[frozenset[str], frozenset[str], str, str]] = [
    (frozenset({"dead_code", "orphan_function", "orphan_module"}),
     frozenset({"broken_call"}),
     "dead_vs_called", _DEMOTE_BOTH),
    (frozenset({"dead_code", "unreachable_code", "unused_definition"}),
     frozenset({"high_complexity", "long_function", "deep_nesting"}),
     "dead_vs_complex", _DEMOTE_BOTH),
    (frozenset({"syntax_error", "undefined_name"}),
     frozenset({"dead_code", "high_complexity", "broad_except",
                "resource_leak"})
     | SECURITY_FAMILY_UNION
     | get_rule_family_set("concurrency"),
     "syntax_vs_analysis", _DEMOTE_SIDE_B),
]
def _xv_binding_symbols(xvr: dict) -> set:
    inner = xvr.get("findings")
    if not isinstance(inner, (list, tuple)):
        return set()
    symbols: set = set()
    for finding in inner:
        if isinstance(finding, dict):
            symbols |= _binding_symbols_of(finding)
    return symbols
def _binding_symbols_of(finding: dict) -> set:
    symbols: set = set()
    func_name = finding.get("_refdepth_function_name", "")
    if isinstance(func_name, str) and func_name:
        symbols.add(func_name)
    message = finding.get("message", "")
    if isinstance(message, str):
        symbol = extract_symbol(message)
        if symbol:
            symbols.add(symbol)
    return symbols
def _demote_affirmative_side(xvr: dict, desc: str) -> None:
    _mark_investigated(xvr)
    xvr["_cross_locator_contradiction"] = desc
def _family_pair_findings(_family_map: dict, fam_a: frozenset,
                          fam_b: frozenset) -> tuple:
    a_findings: list = []
    b_findings: list = []
    for rf, findings in _family_map.items():
        if is_family_member(rf, fam_a):
            a_findings.extend(findings)
        if is_family_member(rf, fam_b):
            b_findings.extend(findings)
    return a_findings, b_findings
def _is_affirmative(xvr: dict) -> bool:
    return xvr.get("conclusion", "") in _AFFIRMATIVE_CONCLUSIONS
def _demoted_pools(desc: str, demote: str, a_pool: list,
                   b_pool: list) -> tuple:
    if demote == _DEMOTE_SIDE_A:
        return (a_pool,)
    if demote == _DEMOTE_SIDE_B:
        return (b_pool,)
    if demote != _DEMOTE_BOTH:
        logger.warning(
            "[CrossLocator] 矛盾 %s 的降级方向非法(%r)，按两侧降级",
            desc, demote)
    return (a_pool, b_pool)
def _demote_contradiction_targets(desc: str, binding_symbols: list,
                                  *pools) -> None:
    for _pool in pools:
        for _xvr in _pool:
            if not isinstance(_xvr, dict) or not _is_affirmative(_xvr):
                continue
            if binding_symbols and not (
                    set(binding_symbols) & _xv_binding_symbols(_xvr)):
                continue
            _demote_affirmative_side(_xvr, desc)
def _check_rule_pair(af: dict, bf: dict, desc: str, fpath: str,
                     audit: dict, a_pool: list, b_pool: list,
                     demote: str = _DEMOTE_BOTH) -> None:
    if af is bf:
        return
    _a_concl = af.get("conclusion", "")
    _b_concl = bf.get("conclusion", "")
    if (_a_concl not in _AFFIRMATIVE_CONCLUSIONS
            or _b_concl not in _AFFIRMATIVE_CONCLUSIONS):
        return
    _binding_symbols: list = []
    if desc in _SYMBOL_BOUND_CONTRADICTIONS:
        _binding_symbols = sorted(
            _xv_binding_symbols(af) & _xv_binding_symbols(bf)
        )
        if not _binding_symbols:
            return
    audit["total_checks"] += 1
    audit["contradictions"].append({
        "file": fpath,
        "type": desc,
        "family_a": af.get("rule_family", ""),
        "locator_a": af.get("locator", ""),
        "conclusion_a": _a_concl,
        "family_b": bf.get("rule_family", ""),
        "locator_b": bf.get("locator", ""),
        "conclusion_b": _b_concl,
        "binding_symbols": _binding_symbols,
    })
    _demote_contradiction_targets(
        desc, _binding_symbols,
        *_demoted_pools(desc, demote, a_pool, b_pool))
def _detect_cross_locator_contradictions(group: list, fpath: str,
                                         cross_rules: list, audit: dict) -> None:
    _family_map = _group_by_family(group)
    for fam_a, fam_b, desc, demote in cross_rules:
        a_findings, b_findings = _family_pair_findings(
            _family_map, fam_a, fam_b)
        for af in a_findings:
            for bf in b_findings:
                _check_rule_pair(af, bf, desc, fpath, audit,
                                 a_pool=a_findings, b_pool=b_findings,
                                 demote=demote)
def _rule_family_text(xvr: dict) -> str:
    family = xvr.get("rule_family", "")
    return family.strip() if isinstance(family, str) else ""
def _group_by_family(group: list) -> dict:
    family_map: dict = {}
    for xvr in group:
        family = _rule_family_text(xvr)
        if family:
            family_map.setdefault(family, []).append(xvr)
    return family_map
def _file_grouped(xv_findings: list) -> dict:
    _file_groups: dict = {}
    for xvr in xv_findings:
        if not isinstance(xvr, dict):
            continue
        fpath = finding_file_path(xvr)
        if not fpath.strip():
            continue
        file_identity = finding_file_key(fpath)
        _file_groups.setdefault(file_identity, []).append(xvr)
    return _file_groups
def _append_consistency_boost(group: list, families,
                              boost_type: str, fpath: str,
                              audit: dict) -> None:
    confirmed = [xvr for xvr in group
                 if is_family_member(_rule_family_text(xvr), families)
                 and xvr.get("conclusion") == "confirmed"]
    distinct_locators = {
        locator.strip()
        for xvr in confirmed
        if isinstance(locator := xvr.get("locator", ""), str)
        and locator.strip()
    }
    if len(confirmed) >= 2 and len(distinct_locators) >= 2:
        for xvr in confirmed:
            xvr["_cross_locator_consistent"] = True
        audit["consistency_boosts"].append({
            "file": fpath,
            "type": boost_type,
            "count": len(confirmed),
            "locators": [xvr.get("locator", "") for xvr in confirmed],
        })
def cross_locator_consistency_check(xv_findings: list) -> dict:
    audit = {"contradictions": [], "consistency_boosts": [], "total_checks": 0}
    entries = _as_entry_list(xv_findings)
    if not entries:
        return audit
    for entry in entries:
        if isinstance(entry, dict):
            entry.pop("_cross_locator_consistent", None)
    try:
        _file_groups = _file_grouped(entries)
        for _file_key, group in _file_groups.items():
            _display_path = finding_file_path(group[0]) or _file_key
            _detect_cross_locator_contradictions(
                group, _display_path, _CROSS_LOCATOR_RULES, audit)
            _append_consistency_boost(group, _DEADCODE_FAMILIES,
                                      "dead_code_multi_confirm",
                                      _display_path, audit)
            _append_consistency_boost(group, SECURITY_FAMILY_UNION,
                                      "security_multi_confirm",
                                      _display_path, audit)
        if audit["contradictions"]:
            logger.info("[CrossLocator] 检测到 %d 个跨locator矛盾 (%d checks)",
                        len(audit["contradictions"]), audit["total_checks"])
        if audit["consistency_boosts"]:
            logger.info("[CrossLocator] 检测到 %d 个跨locator一致性增强",
                        len(audit["consistency_boosts"]))
    except Exception as e:
        logger.warning("[CrossLocator] 跨locator一致性检查异常: %s", e, exc_info=True)
    return audit
STALE_MARGIN_S: float = 5.0
def _parse_report_ts(ts) -> float | None:
    ms_epoch = compact_ts_to_ms(ts)
    if ms_epoch is None:
        return None
    return ms_epoch / 1000.0
def _finding_scope(f: dict) -> tuple[str, str]:
    return (finding_file_path(f), str(f.get("_source_method", "") or ""))
def _resolve_filepath(fp: str, skill_dir: str) -> str:
    if os.path.isabs(fp) or not skill_dir:
        return fp
    return os.path.join(skill_dir, fp)
def _collect_stale_pairs(findings: list, method_ts: dict,
                         skill_dir: str) -> tuple[dict, int, int]:
    stale: dict[str, list[str]] = {}
    checked = 0
    stale_pairs: set[tuple[str, str]] = set()
    _mtime_cache: dict[str, float | None] = {}
    for f in findings:
        if not isinstance(f, dict):
            continue
        fp, src = _finding_scope(f)
        if not fp or src not in method_ts:
            continue
        real_fp = _resolve_filepath(fp, skill_dir)
        if real_fp not in _mtime_cache:
            try:
                _mtime_cache[real_fp] = (
                    os.path.getmtime(real_fp)
                    if os.path.isfile(real_fp) else None)
            except OSError as e:
                logger.debug("文件状态探测失败（跳过）: %s: %s", real_fp, e)
                _mtime_cache[real_fp] = None
        mtime = _mtime_cache[real_fp]
        if mtime is None:
            continue
        checked += 1
        if mtime <= method_ts[src] + STALE_MARGIN_S:
            continue
        stale_pairs.add((fp, src))
        stale.setdefault(fp, [])
        if src not in stale[fp]:
            stale[fp].append(src)
    return stale, len(stale_pairs), checked
def _method_timestamps(independent_results: dict) -> dict[str, float]:
    method_ts: dict[str, float] = {}
    for mid, result in independent_results.items():
        if not isinstance(result, dict):
            continue
        ts = _parse_report_ts(result.get("_report_timestamp", ""))
        if ts is not None:
            method_ts[mid] = ts
    return method_ts
def build_drift_report(independent_results: dict,
                       findings: list,
                       skill_dir: str = "") -> dict:
    if not isinstance(independent_results, dict):
        return {
            "enabled": False,
            "error": (
                "independent_results 非映射形态("
                f"{type(independent_results).__name__})，漂移守卫停用"),
        }
    findings = _as_entry_list(findings) or []
    method_ts = _method_timestamps(independent_results)
    if not method_ts:
        return {"enabled": True, "method_ts": {}, "stale": {},
                "stale_pair_count": 0, "checked_finding_count": 0}
    stale, stale_pair_count, checked = _collect_stale_pairs(
        findings, method_ts, skill_dir)
    return {
        "enabled": True,
        "method_ts": {k: round(v, 3) for k, v in method_ts.items()},
        "stale": stale,
        "stale_pair_count": stale_pair_count,
        "checked_finding_count": checked,
    }
def _stale_hit(ef, stale: dict) -> bool:
    if not isinstance(ef, dict) or not isinstance(stale, dict):
        return False
    fp, src = _finding_scope(ef)
    sources = stale.get(fp)
    if not isinstance(sources, (list, tuple, set, frozenset)):
        return False
    return src in sources
def _entry_is_stale(entry: dict, drift: dict) -> bool:
    inner = entry.get("findings")
    evidence = ([ef for ef in inner if isinstance(ef, dict)]
                if isinstance(inner, (list, tuple)) else [])
    if not evidence:
        evidence = [entry]
    stale = drift.get("stale", {})
    return any(_stale_hit(ef, stale) for ef in evidence)
def _annotate_stale_entry(entry: dict, drift: dict) -> tuple[int, int]:
    flagged = 0
    downgraded = 0
    try:
        if not _entry_is_stale(entry, drift):
            return 0, 0
        entry["_stale_evidence"] = True
        entry["_stale_reason"] = (
            "源文件在诊断后被修改，确认结论基于陈旧证据，需复扫验证")
        flagged += 1
        if entry.get("conclusion") == "confirmed":
            _mark_investigated(entry)
            entry["_downgraded_by"] = "code_drift_guard"
            entry["_review_required"] = True
            entry["_review_reason"] = (
                "代码漂移守卫降级(confirmed→investigated)：源文件诊断后被"
                "修改，确认结论基于陈旧证据——AI复核裁决降级是否成立")
            downgraded += 1
    except (KeyError, AttributeError, TypeError) as _e:
        logger.debug("[DriftGuard] 单条标注异常: %s", _e)
    return flagged, downgraded
def _drift_stale_map(drift) -> dict | None:
    if not isinstance(drift, dict) or not drift.get("enabled"):
        return None
    stale_map = drift.get("stale", {})
    if not isinstance(stale_map, dict):
        logger.warning(
            "[DriftGuard] 漂移报告 stale 键形态无效(%s)，本轮跳过降级",
            type(stale_map).__name__)
        return None
    return stale_map
def annotate_findings_with_drift(xv_findings: list, drift: dict) -> int:
    stale_map = _drift_stale_map(drift)
    if stale_map is None:
        return 0
    entries = _as_entry_list(xv_findings)
    if not entries:
        return 0
    downgraded = 0
    flagged = 0
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        entry.pop("_stale_evidence", None)
        entry.pop("_stale_reason", None)
        if not stale_map:
            continue
        _fl, _dg = _annotate_stale_entry(entry, drift)
        flagged += _fl
        downgraded += _dg
    if flagged:
        logger.info(
            "[DriftGuard] 代码漂移: %d 条命中（%d 条 confirmed 降级 investigated）",
            flagged, downgraded)
    return downgraded
NEGATIVES_AUDIT_KEY = "negatives_audit"
_DEADCODE_FAMILIES = frozenset({
    "dead_code", "call_graph", "DC", "orphan", "orphan_function",
    "orphan_module", "unused_function", "unused_class", "unused_method",
    "unused_definition", "unreachable_code",
})
_SYMTABLE_REFUTABLE_FAMILIES = frozenset({"undefined_name"})
_IDENT_RE = re.compile(rf"(?<!\w){IDENTIFIER_SOURCE}(?!\w)")
_DEF_NAME_RE = re.compile(
    rf"(?:def|class)\s+({IDENTIFIER_SOURCE})"
)
_ASSIGN_TARGETS_RE = re.compile(
    rf"^(?P<targets>{IDENTIFIER_SOURCE}(?:\s*,\s*{IDENTIFIER_SOURCE})*)"
    r"\s*(?::[^=\n]+)?=(?!=)"
)
_FOR_HEAD_RE = re.compile(r"^for\s+(?P<head>.+?)\s+in\b")
_AS_TARGETS_RE = re.compile(rf"\bas\s+({IDENTIFIER_SOURCE})(?!\w)")
_GLOBAL_STMT_RE = re.compile(
    r"^(?:global|nonlocal)\s+(?P<names>[\w\s,]+?)\s*(?:#.*)?$"
)
_QUOTED_NAME_RE = re.compile(rf"['\"]({IDENTIFIER_SOURCE})['\"]")
def _as_entry_list(value) -> list | None:
    if value is None or isinstance(value, (str, bytes)):
        return None
    if isinstance(value, (list, tuple)):
        return list(value)
    try:
        return list(value)
    except TypeError as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc, context='_as_entry_list:TypeError')
        return None
def _matched_identifier(match) -> str:
    if not match:
        return ""
    candidate = match.group(1)
    return candidate if candidate.isidentifier() else ""
def _identifiers(text: str) -> list[str]:
    return [match.group() for match in _IDENT_RE.finditer(text)
            if match.group().isidentifier()]
def _strip_async_prefix(line: str) -> str:
    probe = line.lstrip()
    if probe.startswith("async "):
        probe = probe[len("async "):].lstrip()
    return probe
def _assignment_binds(symbol: str, probe: str) -> bool:
    m = _ASSIGN_TARGETS_RE.match(probe)
    return bool(m and symbol in (t.strip() for t in m.group("targets").split(",")))
def _for_head_binds(symbol: str, probe: str) -> bool:
    m = _FOR_HEAD_RE.match(probe)
    return bool(m and symbol in _identifiers(m.group("head")))
def _as_target_binds(symbol: str, probe: str) -> bool:
    return bool(probe.startswith(("with ", "except ", "except* "))
                and symbol in (am.group(1)
                                for am in _AS_TARGETS_RE.finditer(probe)))
def _global_stmt_declares(symbol: str, probe: str) -> bool:
    m = _GLOBAL_STMT_RE.match(probe)
    return bool(m and symbol in _identifiers(m.group("names")))
def _finding_target_symbol(f: dict) -> str:
    explicit = first_symbol_field(
        f, ("symbol", "function_name", "code_name", "target_symbol"))
    if explicit:
        return explicit
    snippet = str(f.get("code_snippet", "") or "")
    m = _DEF_NAME_RE.search(snippet)
    if m:
        return _matched_identifier(m)
    message = str(f.get("message", "") or f.get("summary", "") or "")
    m = _DEF_NAME_RE.search(message)
    if m:
        return _matched_identifier(m)
    return extract_symbol(message) or ""
_DYNAMIC_REF_CONTEXT_NAMES = frozenset({
    "getattr", "setattr", "hasattr", "delattr",
    "vars", "globals", "locals", "eval", "exec",
    "importlib", "import_module", "__import__",
    "__getattr__", "__getattribute__", "__dir__",
})
_DYNAMIC_STRING_ARG_INDEX = {
    "getattr": 1, "setattr": 1, "hasattr": 1, "delattr": 1,
    "__getattr__": 0, "__getattribute__": 0,
    "eval": 0, "exec": 0,
    "import_module": 0, "__import__": 0,
}
_DYNAMIC_STRING_KWARG_NAMES = {
    "import_module": "name",
    "__import__": "name",
}
_DYNAMIC_NO_STRING_ARG_CALLS = frozenset({
    "vars", "globals", "locals", "__dir__",
})
def _token_hit_lines(src: str, symbol: str
                     ) -> tuple[set[int], set[int], set[int]]:
    name_hit_lines: set[int] = set()
    string_hit_lines: set[int] = set()
    dyn_ctx_lines: set[int] = set()
    _sym_pat = re.compile(rf"(?<!\w){re.escape(symbol)}(?!\w)")
    for tok in tokenize.generate_tokens(io.StringIO(src).readline):
        if tok.type == _token.NAME:
            if tok.string == symbol:
                name_hit_lines.add(tok.start[0])
            elif tok.string in _DYNAMIC_REF_CONTEXT_NAMES:
                dyn_ctx_lines.add(tok.start[0])
        elif tok.type == _token.STRING and _sym_pat.search(tok.string):
            string_hit_lines.add(tok.start[0])
    return name_hit_lines, string_hit_lines, dyn_ctx_lines
def _line_excluded(symbol: str, ln: int, lines: list[str]) -> bool:
    if not (1 <= ln <= len(lines)):
        return False
    line = lines[ln - 1]
    if re.search(rf"(?:def|class)\s+{re.escape(symbol)}\b", line):
        return True
    probe = _strip_async_prefix(line)
    if probe.startswith(("import ", "from ")):
        return True
    return bool(_assignment_binds(symbol, probe)
                or _for_head_binds(symbol, probe)
                or _as_target_binds(symbol, probe)
                or _global_stmt_declares(symbol, probe))
def _dynamic_func_uses_context(func: ast.AST) -> bool:
    return any(
        (isinstance(part, ast.Name)
         and part.id in _DYNAMIC_REF_CONTEXT_NAMES)
        or (isinstance(part, ast.Attribute)
            and part.attr in _DYNAMIC_REF_CONTEXT_NAMES)
        for part in walk_nodes(func))
def _dynamic_string_constants(tree: ast.AST, symbol: str) -> set[ast.Constant]:
    pattern = re.compile(rf"(?<!\w){re.escape(symbol)}(?!\w)")
    strings: set[ast.Constant] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call) and _dynamic_func_uses_context(node.func):
            if isinstance(node.func, ast.Name):
                func_name = node.func.id
            elif isinstance(node.func, ast.Attribute):
                func_name = node.func.attr
            else:
                func_name = ""
            arg_index = _DYNAMIC_STRING_ARG_INDEX.get(func_name)
            if arg_index is not None:
                values = node.args[arg_index:arg_index + 1]
                kwarg_name = _DYNAMIC_STRING_KWARG_NAMES.get(func_name)
                if not values and kwarg_name:
                    values = [kw.value for kw in node.keywords
                              if kw.arg == kwarg_name]
            elif func_name in _DYNAMIC_NO_STRING_ARG_CALLS:
                values = []
            else:
                values = [*node.args, *(kw.value for kw in node.keywords)]
        elif (isinstance(node, ast.Subscript)
              and isinstance(node.value, ast.Call)
              and _dynamic_func_uses_context(node.value.func)):
            values = [node.slice]
        else:
            continue
        for value in values:
            for candidate in walk_nodes(value):
                if (isinstance(candidate, ast.Constant)
                        and isinstance(candidate.value, str)
                        and pattern.search(candidate.value)):
                    strings.add(candidate)
    return strings
def _same_symbol_definition_body_ids(tree: ast.AST, symbol: str) -> set[int]:
    ignored: set[int] = set()
    for node in walk_nodes(tree):
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
                and node.name == symbol):
            for statement in node.body:
                ignored.update(id(part) for part in walk_nodes(statement))
    return ignored
def _ast_symbol_refs(tree: ast.AST, symbol: str) -> tuple[int, int]:
    ignored = _same_symbol_definition_body_ids(tree, symbol)
    code_hits = sum(
        1 for node in walk_nodes(tree)
        if id(node) not in ignored
        and ((isinstance(node, ast.Name) and node.id == symbol
              and isinstance(node.ctx, ast.Load))
             or (isinstance(node, ast.Attribute) and node.attr == symbol
                 and isinstance(node.ctx, ast.Load))))
    dynamic_hits = sum(
        1 for node in _dynamic_string_constants(tree, symbol)
        if id(node) not in ignored)
    return code_hits, dynamic_hits
def _scan_symbol_refs(src: str, symbol: str) -> tuple[int, int]:
    try:
        tree = ast.parse(src)
    except (SyntaxError, ValueError, TypeError):
        name_hit_lines, string_hit_lines, dyn_ctx_lines = _token_hit_lines(
            src, symbol)
        lines = src.split("\n")
        code_hits = sum(
            1 for ln in name_hit_lines
            if not _line_excluded(symbol, ln, lines))
        dyn_hits = sum(
            1 for ln in string_hit_lines
            if ln in dyn_ctx_lines and not _line_excluded(symbol, ln, lines))
        return code_hits, dyn_hits
    return _ast_symbol_refs(tree, symbol)
def _collect_dynamic_refs(cache, symbol: str) -> int:
    if not symbol or symbol in BUILTIN_NAMES:
        return 0
    return sum(_count_refs_in_source(cache, fp, symbol)
               for fp in _cache_py_files(cache))
def _cache_py_files(cache) -> list[str]:
    try:
        return list(cache.py_files)
    except Exception as e:
        logger.debug("[Precise] cache 结构不可用（%s）", e)
        raise RuntimeError("动态引用证据缓存文件清单不可用") from e
def _guard_source(cache, fp: str) -> str | None:
    if not fp:
        return ""
    try:
        return cache.get_source(fp)
    except Exception:
        logger.debug("[Negatives] get_source 失败降级跳过: %s", fp,
                     exc_info=True)
        return None
def _count_refs_in_source(cache, fp: str, symbol: str) -> int:
    src = _guard_source(cache, fp)
    if src is None:
        raise RuntimeError(f"动态引用证据源码读取失败: {fp}")
    if not src:
        return 0
    try:
        code_hits, dyn_hits = _scan_symbol_refs(src, symbol)
    except Exception as exc:
        logger.debug("[Negatives] tokenize 失败，转单条候选错误桶: %s",
                     fp, exc_info=True)
        raise RuntimeError(f"动态引用证据扫描失败: {fp}") from exc
    return code_hits + dyn_hits
def _symbol_bound(sym) -> bool:
    try:
        return bool(
            sym.is_assigned() or sym.is_imported() or sym.is_parameter())
    except Exception as _e:  # noqa: BLE001 —— 判定异常时保守视为不可反证
        log_swallowed(__name__, _e, context='_symbol_bound:Exc')
        return False
def _scope_nodes_by_identity(tree: ast.AST) -> dict:
    scopes: dict[tuple[str, int], list[ast.AST]] = {}
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            name = node.name
        elif isinstance(node, ast.Lambda):
            name = "lambda"
        elif isinstance(node, ast.ListComp):
            name = "listcomp"
        elif isinstance(node, ast.SetComp):
            name = "setcomp"
        elif isinstance(node, ast.DictComp):
            name = "dictcomp"
        elif isinstance(node, ast.GeneratorExp):
            name = "genexpr"
        else:
            continue
        scopes.setdefault((name, node.lineno), []).append(node)
    return scopes
def _definition_site_expressions(node: ast.AST) -> list[ast.AST]:
    expressions: list[ast.AST] = []
    expressions.extend(getattr(node, "decorator_list", ()) or ())
    args = getattr(node, "args", None)
    if isinstance(args, ast.arguments):
        expressions.extend(args.defaults)
        expressions.extend(value for value in args.kw_defaults
                           if value is not None)
        all_args = [
            *args.posonlyargs, *args.args, *args.kwonlyargs,
            *([args.vararg] if args.vararg else []),
            *([args.kwarg] if args.kwarg else []),
        ]
        expressions.extend(arg.annotation for arg in all_args
                           if arg.annotation is not None)
    returns = getattr(node, "returns", None)
    if returns is not None:
        expressions.append(returns)
    expressions.extend(getattr(node, "bases", ()) or ())
    expressions.extend(keyword_node.value
                       for keyword_node in getattr(node, "keywords", ()) or ())
    for type_param in getattr(node, "type_params", ()) or ():
        for attr in ("bound", "default"):
            expression = getattr(type_param, attr, None)
            if expression is not None:
                expressions.append(expression)
    if isinstance(node, (ast.ListComp, ast.SetComp,
                         ast.DictComp, ast.GeneratorExp)):
        generators = node.generators
        if generators:
            expressions.append(generators[0].iter)
    return expressions
def _definition_site_lines(node: ast.AST) -> set[int]:
    lines: set[int] = set()
    for expression in _definition_site_expressions(node):
        start = getattr(expression, "lineno", 0)
        end = getattr(expression, "end_lineno", None) or start
        if start > 0:
            lines.update(range(start, end + 1))
    return lines
def _scope_at_line(table, scopes: dict, line: int, node: ast.AST):
    if line <= 0:
        return table, node
    matches = []
    for child in table.get_children():
        identity = (child.get_name(), child.get_lineno())
        for candidate in scopes.get(identity, ()):
            end_line = getattr(candidate, "end_lineno", None) or candidate.lineno
            if (candidate.lineno <= line <= end_line
                    and line not in _definition_site_lines(candidate)):
                matches.append((child, candidate))
    if len(matches) != 1:
        return table, node
    child, child_node = matches[0]
    return _scope_at_line(child, scopes, line, child_node)
def _table_parents(table) -> dict:
    parents = {}
    def _visit(parent) -> None:
        for child in parent.get_children():
            parents[id(child)] = parent
            _visit(child)
    _visit(table)
    return parents
def _table_symbol(table, name: str):
    for sym in table.get_symbols():
        if sym.get_name() == name:
            return sym
    return None
def _table_has_binding(table, name: str) -> bool:
    sym = _table_symbol(table, name)
    return sym is not None and _symbol_bound(sym)
def _symbol_is_global(sym) -> bool:
    try:
        return bool(sym.is_global())
    except Exception as _e:  # noqa: BLE001 —— 判定异常时保守视为不可反证
        log_swallowed(__name__, _e, context='_symbol_is_global:Exc')
        return False
def _name_visible_from_table(table, name: str, parents: dict, root):
    current = table
    while current is not None:
        sym = _table_symbol(current, name)
        if sym is not None:
            if _symbol_bound(sym):
                return current
            if _symbol_is_global(sym):
                return root if _table_has_binding(root, name) else None
        parent = parents.get(id(current))
        while (parent is not None and table.get_type() != "class"
               and parent.get_type() == "class"):
            parent = parents.get(id(parent))
        current = parent
    return None
def _scope_node_for_table(table, scopes: dict, tree: ast.AST):
    if table.get_type() == "module":
        return tree
    candidates = scopes.get((table.get_name(), table.get_lineno()), ())
    return candidates[0] if len(candidates) == 1 else None
class _StatementScopeBindingLines(ast.NodeVisitor):
    def __init__(self, name: str) -> None:
        self.name = name
        self.lines: list[int] = []
        self.deleted_lines: list[int] = []
        self.conditional_events: list[tuple[int, bool]] = []
        self.conditional_depth = 0
    def _record_event(self, line: int, bound: bool) -> None:
        if line <= 0:
            return
        if self.conditional_depth:
            self.conditional_events.append((line, bound))
        elif bound:
            self.lines.append(line)
        else:
            self.deleted_lines.append(line)
    def _record(self, line: int) -> None:
        self._record_event(line, True)
    def _record_deletion(self, line: int) -> None:
        self._record_event(line, False)
    def _visit_conditional(self, node: ast.AST) -> None:
        self.conditional_depth += 1
        try:
            self.generic_visit(node)
        finally:
            self.conditional_depth -= 1
    visit_If = _visit_conditional
    visit_For = _visit_conditional
    visit_AsyncFor = _visit_conditional
    visit_While = _visit_conditional
    visit_Try = _visit_conditional
    visit_TryStar = _visit_conditional
    visit_With = _visit_conditional
    visit_AsyncWith = _visit_conditional
    visit_Match = _visit_conditional
    visit_IfExp = _visit_conditional
    visit_BoolOp = _visit_conditional
    def visit_Name(self, node: ast.Name) -> None:
        if node.id != self.name:
            return
        if isinstance(node.ctx, ast.Store):
            self._record(node.lineno)
        elif isinstance(node.ctx, ast.Del):
            self._record_deletion(node.lineno)
    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.value is None:
            self.visit(node.annotation)
            return
        self.generic_visit(node)
    def visit_Import(self, node: ast.Import) -> None:
        for imported in node.names:
            local_name = imported.asname or imported.name.partition(".")[0]
            if local_name == self.name:
                self._record(node.lineno)
    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        for imported in node.names:
            if imported.name != "*" and (imported.asname or imported.name) == self.name:
                self._record(node.lineno)
    def visit_ExceptHandler(self, node: ast.ExceptHandler) -> None:
        if node.name == self.name:
            self._record(node.lineno)
        self.generic_visit(node)
        if node.name == self.name:
            self._record_deletion((node.end_lineno or node.lineno) + 1)
    def visit_MatchAs(self, node: ast.MatchAs) -> None:
        if node.name == self.name:
            self._record(node.lineno)
        self.generic_visit(node)
    def visit_MatchStar(self, node: ast.MatchStar) -> None:
        if node.name == self.name:
            self._record(node.lineno)
    def visit_MatchMapping(self, node: ast.MatchMapping) -> None:
        if node.rest == self.name:
            self._record(node.lineno)
        self.generic_visit(node)
    def _visit_nested_scope(self, node: ast.AST) -> None:
        if getattr(node, "name", "") == self.name:
            self._record(getattr(node, "lineno", 0))
        for expression in _definition_site_expressions(node):
            self.visit(expression)
    visit_FunctionDef = _visit_nested_scope
    visit_AsyncFunctionDef = _visit_nested_scope
    visit_ClassDef = _visit_nested_scope
    visit_Lambda = _visit_nested_scope
    def _visit_comprehension(self, node: ast.AST) -> None:
        generators = getattr(node, "generators", ())
        if generators:
            self.visit(generators[0].iter)
        self.conditional_depth += 1
        try:
            for index, generator in enumerate(generators):
                self.visit(generator.target)
                if index:
                    self.visit(generator.iter)
                for condition in generator.ifs:
                    self.visit(condition)
            if isinstance(node, ast.DictComp):
                self.visit(node.key)
                self.visit(node.value)
            else:
                self.visit(node.elt)
        finally:
            self.conditional_depth -= 1
    visit_ListComp = _visit_comprehension
    visit_SetComp = _visit_comprehension
    visit_DictComp = _visit_comprehension
    visit_GeneratorExp = _visit_comprehension
def _merge_statement_binding_state(state, collector) -> bool | None:
    possible = ({True, False} if state is None
                else {state})
    certain = set()
    if collector.lines:
        certain.add(True)
    if collector.deleted_lines:
        certain.add(False)
    if certain == {True, False}:
        possible = {True, False}
    elif certain == {True}:
        possible = {True}
    elif certain == {False}:
        possible = {False}
    if any(bound for _line, bound in collector.conditional_events):
        possible.add(True)
    if any(not bound for _line, bound in collector.conditional_events):
        possible.add(False)
    if possible == {True}:
        return True
    if possible == {False}:
        return False
    return None
def _if_else_binding_state(state, statement: ast.If,
                           name: str) -> bool | None:
    test_collector = _StatementScopeBindingLines(name)
    test_collector.visit(statement.test)
    inherited = _merge_statement_binding_state(state, test_collector)
    branch_states = []
    for block in (statement.body, statement.orelse):
        branch_state = inherited
        for child in block:
            branch_state = _statement_binding_state(
                branch_state, child, name)
        branch_states.append(branch_state)
    body_state, else_state = branch_states
    return body_state if body_state == else_state else None
def _statement_binding_state(state, statement: ast.AST,
                             name: str) -> bool | None:
    if isinstance(statement, ast.If) and statement.orelse:
        return _if_else_binding_state(state, statement, name)
    collector = _StatementScopeBindingLines(name)
    collector.visit(statement)
    return _merge_statement_binding_state(state, collector)
def _node_contains_line(node: ast.AST, line: int) -> bool:
    start = getattr(node, "lineno", 0)
    end = getattr(node, "end_lineno", None) or start
    return start <= line <= end
def _header_binding_state(owner: ast.AST, field_name: str,
                          name: str, state) -> bool | None:
    nodes: list[ast.AST] = []
    if (isinstance(owner, (ast.If, ast.While))
            and field_name in ("body", "orelse")):
        nodes = [owner.test]
    elif isinstance(owner, (ast.For, ast.AsyncFor)):
        if field_name in ("body", "orelse"):
            nodes = [owner.iter]
        if field_name == "body":
            target_collector = _StatementScopeBindingLines(name)
            target_collector.visit(owner.target)
            if target_collector.lines:
                return True
    elif (isinstance(owner, (ast.With, ast.AsyncWith))
          and field_name == "body"):
        for item in owner.items:
            nodes.append(item.context_expr)
            if item.optional_vars is not None:
                nodes.append(item.optional_vars)
    elif isinstance(owner, ast.ExceptHandler) and field_name == "body":
        if owner.name == name:
            return True
        if owner.type is not None:
            nodes = [owner.type]
    elif (isinstance(owner, ast.match_case) and field_name == "body"):
        nodes = [owner.pattern]
        if owner.guard is not None:
            nodes.append(owner.guard)
    if not nodes:
        return state
    collector = _StatementScopeBindingLines(name)
    for node in nodes:
        collector.visit(node)
    return _merge_statement_binding_state(state, collector)
def _statement_child_binding_at_line(node: ast.AST, name: str, line: int,
                                     state) -> tuple[bool, bool | None]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)):
        return False, state
    for field_name, value in ast.iter_fields(node):
        values = value if isinstance(value, list) else [value]
        if (isinstance(value, list) and value
                and all(isinstance(item, ast.stmt) for item in value)
                and any(_node_contains_line(item, line) for item in value)):
            header_state = _header_binding_state(
                node, field_name, name, state)
            return _statement_block_binding_at_line(
                value, name, line, header_state)
        for child in values:
            if not isinstance(child, ast.AST):
                continue
            if getattr(child, "lineno", 0) and not _node_contains_line(
                    child, line):
                continue
            found, child_state = _statement_child_binding_at_line(
                child, name, line, state)
            if found:
                return True, child_state
    return False, state
def _statement_block_binding_at_line(block: list[ast.stmt], name: str,
                                     line: int, state) -> tuple[
                                         bool, bool | None]:
    for statement in block:
        if _node_contains_line(statement, line):
            found, child_state = _statement_child_binding_at_line(
                statement, name, line, state)
            return True, child_state if found else state
        state = _statement_binding_state(state, statement, name)
    return False, state
def _guaranteed_binding_precedes_line(scope_node: ast.AST, name: str,
                                      line: int, inherited: bool) -> bool:
    found, state = _statement_block_binding_at_line(
        scope_node.body, name, line, inherited)
    return found and state is True
def _ast_position(node: ast.AST) -> tuple[int, int]:
    return (getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
def _ast_contains_node(container: ast.AST, candidate: ast.AST) -> bool:
    start = _ast_position(container)
    end = (getattr(container, "end_lineno", None) or start[0],
           getattr(container, "end_col_offset", None) or start[1])
    return start <= _ast_position(candidate) < end
def _generator_target_binds(generator: ast.comprehension,
                            name: str) -> bool:
    return any(isinstance(part, ast.Name) and part.id == name
               and isinstance(part.ctx, ast.Store)
               for part in walk_nodes(generator.target))
def _comprehension_target_guarantees_load(
        node: ast.AST, load: ast.Name, name: str) -> bool:
    generators = getattr(node, "generators", ())
    if generators and _ast_contains_node(generators[0].iter, load):
        return False
    result_nodes = ([node.key, node.value] if isinstance(node, ast.DictComp)
                    else [node.elt])
    if any(_ast_contains_node(result, load) for result in result_nodes):
        return any(_generator_target_binds(generator, name)
                   for generator in generators)
    for generator in generators:
        if not _generator_target_binds(generator, name):
            continue
        if _ast_contains_node(generator.iter, load):
            continue
        if _ast_position(generator.target) <= _ast_position(load):
            return True
    return False
def _comprehension_guarantees_binding(scope_node: ast.AST, name: str,
                                      line: int) -> bool:
    visibility: list[bool] = []
    comprehension_types = (ast.ListComp, ast.SetComp,
                           ast.DictComp, ast.GeneratorExp)
    for node in walk_nodes(scope_node):
        if (not isinstance(node, comprehension_types)
                or not _node_contains_line(node, line)):
            continue
        loads = [
            part for part in walk_nodes(node)
            if isinstance(part, ast.Name) and part.id == name
            and isinstance(part.ctx, ast.Load) and part.lineno == line
        ]
        visibility.extend(
            _comprehension_target_guarantees_load(node, load, name)
            for load in loads)
    return bool(visibility) and all(visibility)
def _current_binding_precedes_line(table, scope_node: ast.AST,
                                   name: str, line: int) -> bool:
    if (line <= 0 or not isinstance(
            scope_node, (ast.Module, ast.FunctionDef,
                         ast.AsyncFunctionDef, ast.ClassDef))):
        return True
    sym = _table_symbol(table, name)
    if sym is None or not _symbol_bound(sym):
        return True
    if _comprehension_guarantees_binding(scope_node, name, line):
        return True
    inherited_binding = (
        table.get_type() != "module" and _symbol_is_global(sym))
    try:
        inherited_binding = (
            inherited_binding or sym.is_nonlocal() or sym.is_parameter())
    except Exception as _e:  # noqa: BLE001 —— 无法判定绑定类别时保守不反证
        log_swallowed(__name__, _e, context='_current_binding_precedes_line:Exc')
        return False
    collector = _StatementScopeBindingLines(name)
    for statement in scope_node.body:
        collector.visit(statement)
    events = ([(binding_line, True, True) for binding_line in collector.lines]
              + [(deleted_line, False, True)
                 for deleted_line in collector.deleted_lines]
              + [(event_line, bound, False)
                 for event_line, bound in collector.conditional_events])
    if inherited_binding:
        events.append((0, True, True))
    if any(event_line == line and not bound
           for event_line, bound, _certain in events):
        return False
    if _guaranteed_binding_precedes_line(
            scope_node, name, line, inherited_binding):
        return True
    if not events:
        return False
    prior_events = sorted(
        (event for event in events if event[0] < line),
        key=lambda event: event[0])
    if not prior_events:
        return False
    possible = {True} if inherited_binding else {False}
    for event_line in dict.fromkeys(event[0] for event in prior_events):
        line_events = [event for event in prior_events
                       if event[0] == event_line]
        certain = {bound for _line, bound, is_certain in line_events
                   if is_certain}
        conditional = {bound for _line, bound, is_certain in line_events
                       if not is_certain}
        if certain == {True, False}:
            possible = {True, False}
        elif certain == {True}:
            possible = {True}
            if False in conditional:
                possible.add(False)
        elif certain == {False}:
            possible = {False}
            if True in conditional:
                possible.add(True)
        else:
            if True in conditional:
                possible.add(True)
            if False in conditional:
                possible.add(False)
    return possible == {True}
class _DirectScopeCallLines(ast.NodeVisitor):
    def __init__(self, name: str) -> None:
        self.name = name
        self.lines: list[int] = []
    def visit_Call(self, node: ast.Call) -> None:
        if isinstance(node.func, ast.Name) and node.func.id == self.name:
            self.lines.append(node.lineno)
        self.generic_visit(node)
    def _visit_nested_function(self, node: ast.AST) -> None:
        for expression in _definition_site_expressions(node):
            self.visit(expression)
    visit_FunctionDef = _visit_nested_function
    visit_AsyncFunctionDef = _visit_nested_function
    visit_Lambda = _visit_nested_function
def _deferred_callable_names(binding_node: ast.AST,
                               function_node: ast.AST) -> tuple[str, ...]:
    if isinstance(function_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return (function_node.name,)
    if not isinstance(function_node, ast.Lambda):
        return ()
    names: list[str] = []
    for node in walk_nodes(binding_node):
        if isinstance(node, ast.Assign) and node.value is function_node:
            targets = node.targets
        elif (isinstance(node, (ast.AnnAssign, ast.NamedExpr))
              and node.value is function_node):
            targets = [node.target]
        else:
            continue
        names.extend(target.id for target in targets
                     if isinstance(target, ast.Name))
    return tuple(dict.fromkeys(names))
def _deferred_function_called_before_binding(
        binding_table, binding_node: ast.AST, function_node: ast.AST,
        name: str,
) -> bool:
    if binding_table.get_type() not in ("module", "function"):
        return False
    callable_names = _deferred_callable_names(binding_node, function_node)
    collectors = [_DirectScopeCallLines(callable_name)
                  for callable_name in callable_names]
    for statement in binding_node.body:
        for collector in collectors:
            collector.visit(statement)
    call_lines = [
        node.lineno for node in walk_nodes(binding_node)
        if isinstance(node, ast.Call) and node.func is function_node
    ]
    for collector in collectors:
        call_lines.extend(collector.lines)
    return any(
        not _current_binding_precedes_line(
            binding_table, binding_node, name, call_line)
        for call_line in call_lines)
def _class_body_runs_during_module_execution(table, parents: dict) -> bool:
    if table.get_type() != "class":
        return False
    current = table
    while current is not None and current.get_type() == "class":
        current = parents.get(id(current))
    return current is not None and current.get_type() == "module"
def _symtable_has_name(src: str, name: str, line: int = 0) -> bool:
    try:
        tree = ast.parse(src)
        table = symtable.symtable(src, "<finding>", "exec")
    except (SyntaxError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e, context='_symtable_has_name:SyntaxError')
        return False
    try:
        scopes = _scope_nodes_by_identity(tree)
        target, scope_node = _scope_at_line(table, scopes, line, tree)
        parents = _table_parents(table)
        binding_table = _name_visible_from_table(
            target, name, parents, table)
        if binding_table is None:
            return False
        if target.get_type() == "function" and binding_table is not target:
            binding_node = _scope_node_for_table(binding_table, scopes, tree)
            if (binding_node is not None
                    and _deferred_function_called_before_binding(
                        binding_table, binding_node, scope_node, name)):
                return False
        if (target.get_type() == "class" and binding_table is not target
                and binding_table.get_type() == "function"):
            binding_node = _scope_node_for_table(binding_table, scopes, tree)
            if binding_node is None:
                return False
            return _current_binding_precedes_line(
                binding_table, binding_node, name, line)
        symbol = _table_symbol(target, name)
        if (symbol is not None and _symbol_is_global(symbol)
                and _class_body_runs_during_module_execution(target, parents)):
            return _current_binding_precedes_line(table, tree, name, line)
        return _current_binding_precedes_line(target, scope_node, name, line)
    except Exception as _e:  # noqa: BLE001 —— symtable 遍历异常兜底不反证
        log_swallowed(__name__, _e, context='_symtable_has_name:Exc')
        return False
def _snippet_symbol_guess(snippet: str) -> str:
    lines = snippet.split("\n")
    for idx, line in enumerate(lines, 1):
        for ident in _identifiers(line):
            if ident in BUILTIN_NAMES or keyword.iskeyword(ident):
                continue
            if _line_excluded(ident, idx, lines):
                continue
            return ident
    return ""
def _finding_target_name_for_precise(f: dict) -> str:
    explicit = first_symbol_field(
        f, ("symbol", "name", "undefined_name", "identifier"),
        skip_builtins=True)
    if explicit:
        return explicit
    message = str(f.get("message", "") or "")
    name = _matched_identifier(_QUOTED_NAME_RE.search(message))
    if name and name not in BUILTIN_NAMES:
        return name
    return _snippet_symbol_guess(str(f.get("code_snippet", "") or ""))
def _run_negatives_item(cache, xvf: dict, report: dict) -> None:
    findings = [f for f in (xvf.get("findings") or [])
                if isinstance(f, dict)]
    if not findings:
        report["skipped"] += 1
        return
    file_path = finding_file_path(xvf) or finding_file_path(findings[0])
    families = [_rule_family_of(f) for f in findings]
    if all(is_family_member(rf, _DEADCODE_FAMILIES) for rf in families):
        _neg_refute_by_dynamics(cache, findings, xvf, report)
    elif any(is_family_member(rf, _SYMTABLE_REFUTABLE_FAMILIES)
             for rf in families):
        _neg_refute_by_symtable(cache, findings, file_path, xvf, report)
    else:
        report["skipped"] += 1
def _rule_family_of(f: dict) -> str:
    return str(f.get("rule_family", "") or "")
def _deadcode_symbols(findings: list) -> list[str]:
    symbols: list[str] = []
    for f in findings:
        rf = _rule_family_of(f)
        if is_family_member(rf, _DEADCODE_FAMILIES):
            sym = _finding_target_symbol(f)
            if sym and sym not in symbols:
                symbols.append(sym)
    return symbols
def _all_symbols_referenced(cache, symbols: list[str]) -> tuple[bool, int]:
    refs_total = 0
    for sym in symbols:
        refs = _collect_dynamic_refs(cache, sym)
        if refs <= 0:
            return False, 0
        refs_total += refs
    return True, refs_total
def _demote_confirmed_to_reviewed(xvf: dict, review_reason: str) -> None:
    was_confirmed = xvf.get("conclusion") == "confirmed"
    _mark_investigated(xvf)
    if was_confirmed:
        xvf["_review_required"] = True
        xvf["_review_reason"] = review_reason
def _neg_refute_by_dynamics(cache, findings: list, xvf: dict,
                            report: dict) -> None:
    symbols = _deadcode_symbols(findings)
    if not symbols:
        report["skipped"] += 1
        return
    all_refuted, refs_total = _all_symbols_referenced(cache, symbols)
    if all_refuted:
        _demote_confirmed_to_reviewed(
            xvf,
            "动态引用反证降级(confirmed→investigated)：死代码目标"
            "符号发现引用痕迹——AI复核裁决反证降级是否成立")
        xvf["_neg_dynamics_refuted"] = True
        xvf["_neg_dynamics_refs"] = refs_total
        report["downgraded_dynamics"] += 1
        logger.info(
            "[Negatives-A] 动态引用反证: %s 引用痕迹 %d 处, "
            "confirmed/likely→investigated", "/".join(symbols), refs_total)
    else:
        xvf["_neg_dynamics_corroborated"] = True
        report["corroborated_dynamics"] += 1
def _compile_precheck(src: str, file_path: str) -> str:
    try:
        compile(src, file_path or "<finding>", "exec")
    except SyntaxError as _e:
        log_swallowed(__name__, _e, context='_compile_precheck:SyntaxError')
        return "corroborate"
    except ValueError as _e:
        log_swallowed(__name__, _e, context='_compile_precheck:ValueError')
        return "skip"
    return "ok"
def _all_symbols_visible(src: str, findings: list) -> bool:
    if not findings:
        return False
    for f in findings:
        name = _finding_target_name_for_precise(f)
        if not name or not _symtable_has_name(
                src, name, _safe_finding_line(f)):
            return False
    return True
def _all_precise_family(findings: list) -> bool:
    return all(is_family_member(_rule_family_of(f), _SYMTABLE_REFUTABLE_FAMILIES)
               for f in findings)
def _neg_refute_by_symtable(cache, findings: list, file_path: str,
                            xvf: dict, report: dict) -> None:
    if not _all_precise_family(findings):
        report["skipped"] += 1
        return
    src = _guard_source(cache, file_path)
    if not src:
        report["skipped"] += 1
        return
    source_line_count = len(src.splitlines())
    if any(not 1 <= _safe_finding_line(f) <= source_line_count
           for f in findings):
        report["skipped"] += 1
        return
    _compile_state = _compile_precheck(src, file_path)
    if _compile_state == "skip":
        report["skipped"] += 1
        return
    if _compile_state == "corroborate":
        report["corroborated_precise"] += 1
        logger.debug(
            "[Negatives-B] 源码语法错误，精确族反证不成立（保持结论）: %s",
            file_path)
        return
    if _all_symbols_visible(src, findings):
        _demote_confirmed_to_reviewed(
            xvf,
            "精确族符号表反证降级(confirmed→investigated)：compile+"
            "symtable印证目标符号可见——AI复核裁决反证降级是否成立")
        xvf["_neg_precise_refuted"] = True
        report["downgraded_precise"] += 1
        logger.info(
            "[Negatives-B] 精确族反证: %s 符号表可见, "
            "confirmed/likely→investigated", file_path)
    else:
        xvf["_neg_precise_corroborated"] = True
        report["corroborated_precise"] += 1
        logger.debug(
            "[Negatives-B] 精确族反证不成立（符号表不可见）: %s", file_path)
def _probe_negatives_cache(cv2):
    try:
        return peek_warmed_cache(getattr(cv2, "skill_dir", "") or "")
    except Exception as e:  # noqa: BLE001 —— 缓存探测失败降级为未预热（degraded 状态已显性化，此处留异常原因）
        logger.debug("[Negatives] peek_warmed_cache 探测异常（%s），降级未预热", e)
        return None
_NEGATIVES_RUN_FIELDS = (
    "_neg_dynamics_refuted", "_neg_dynamics_refs",
    "_neg_dynamics_corroborated", "_neg_precise_refuted",
    "_neg_precise_corroborated",
)
def _run_channel_items(cache, xv_findings, report) -> None:
    for xvf in xv_findings or []:
        if not isinstance(xvf, dict):
            continue
        for field_name in _NEGATIVES_RUN_FIELDS:
            xvf.pop(field_name, None)
        if xvf.get("conclusion") not in ("confirmed", "likely"):
            continue
        report["candidates"] += 1
        try:
            _run_negatives_item(cache, xvf, report)
        except Exception as _item_e:
            report["errors"] += 1
            logger.debug(
                "[Negatives] 单条处理异常隔离（计 errors，通道继续）: %s",
                _item_e, exc_info=True)
def _new_negatives_report() -> dict:
    return {
        "status": "ok",
        "cache_available": False,
        "candidates": 0,
        "downgraded_dynamics": 0,
        "downgraded_precise": 0,
        "corroborated_dynamics": 0,
        "corroborated_precise": 0,
        "skipped": 0,
        "errors": 0,
        "message": "",
    }
def _finalize_negatives_message(report: dict) -> None:
    candidates = report["candidates"]
    downgraded = (report["downgraded_dynamics"]
                  + report["downgraded_precise"])
    corroborated = (report["corroborated_dynamics"]
                    + report["corroborated_precise"])
    skipped = report["skipped"]
    errors = report["errors"]
    if not candidates:
        report["message"] = "无候选 xv_findings（0 条待反证）"
    elif candidates == corroborated and not (downgraded or skipped or errors):
        report["message"] = (
            f"{candidates} 条候选全部通过反证检验（无降级）")
    else:
        parts = []
        if downgraded:
            parts.append(
                f"反向证据通道降级 {report['downgraded_dynamics']} 条(动态引用) "
                f"+ {report['downgraded_precise']} 条(精确族符号表反证)")
        if corroborated:
            parts.append(f"{corroborated} 条候选通过反证检验（无降级）")
        if skipped:
            parts.append(f"{skipped} 条候选不适用或缺少证据，未执行反证")
        accounted = downgraded + corroborated + skipped + errors
        if accounted != candidates:
            report["status"] = "degraded"
            parts.append(
                f"{abs(candidates - accounted)} 条候选计数未闭合"
                f"（候选 {candidates}，已归桶 {accounted}）")
        report["message"] = "；".join(parts)
    if errors:
        report["status"] = "degraded"
        _err_part = f"单条异常隔离 {errors} 条"
        report["message"] = (f"{report['message']}；{_err_part}"
                             if report["message"] else _err_part)
def _store_negatives_report(cv2, report: dict) -> None:
    try:
        cv2._negatives_report = report
    except (AttributeError, TypeError) as _e:
        logger.debug(
            "[Negatives] 报告无法挂载到调用方(%s): %s",
            type(cv2).__name__, _e)
def run_negatives_channels(cv2, xv_findings: list) -> dict:
    report = _new_negatives_report()
    if xv_findings is not None and not isinstance(xv_findings, (list, tuple)):
        report["status"] = "degraded"
        report["message"] = (
            f"xv_findings 形态非法({type(xv_findings).__name__})，"
            "反向证据通道跳过")
        logger.warning("[Negatives] %s", report["message"])
        _store_negatives_report(cv2, report)
        return report
    cache = _probe_negatives_cache(cv2)
    if cache is None:
        report["status"] = "degraded"
        report["message"] = "SharedCache 未预热（非管线直调），反向证据通道跳过"
        logger.warning("[Negatives] %s", report["message"])
    else:
        report["cache_available"] = True
        _run_channel_items(cache, xv_findings, report)
        _finalize_negatives_message(report)
        logger.info("[Negatives] %s", report["message"])
    _store_negatives_report(cv2, report)
    return report
def attach_negatives_audit(result: dict, cv2) -> None:
    report = getattr(
        cv2, "_negatives_report", {"status": "not_run"})
    if not isinstance(result, dict):
        logger.warning(
            "[Negatives] 审计报告无法挂载：result 非映射(%s)",
            type(result).__name__)
        return
    result[NEGATIVES_AUDIT_KEY] = report

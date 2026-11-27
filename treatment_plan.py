from __future__ import annotations

import heapq
import logging
from collections import defaultdict
from dataclasses import asdict, dataclass, field
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_types_normalize import (
    as_count,
    as_str,
    coerce_line,
    count_tasks,
    dict_or_empty,
    finding_file_key,
    has_finding_entries,
    normalize_severity_rank,
    normalize_sources,
    parse_locator_line,
    safe_float,
    severity_literal_from_rank,
    signal_bool,
    str_or_empty,
    strict_iterable_list,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    FIELD_ADJUSTED_CONFIDENCE,
    FIELD_EVIDENCE_STRENGTH,
    FIELD_SIDE_EFFECT_SUMMARY,
    RULE_HARDCODED_CREDENTIAL,
    RULE_ID_PREFIX_CATEGORY,
    SEVERITY_RANK,
)
from jwsgj.fix_guide_rule_identity import (
    DependencyType as _DependencyType,
)
from jwsgj.fix_guide_rule_identity import (
    build_dependency_graph as _build_dependency_graph,
)
from jwsgj.fix_guide_rule_identity import (
    get_fix_guidance,
)
from jwsgj.fp_rules_judge import SelfAuditAwareness
from jwsgj.memory_bridge import normalize_rule_id
from jwsgj.memory_feedback_core import (
    get_failed_fix_avoidance,
    get_fix_pattern_suggestions,
    get_fixer_success_rates,
    recommend_fix_strategy,
)
from jwsgj.runtime_scope import (
    resolve_finding_file_path,
)
from jwsgj.treatment_evidence import default_regression_plan
from jwsgj.treatment_state import reset_treatment_artifacts

__all__ = [
    'CONCLUSION_RANK',
    'SEVERITY_RANK_TABLE',
    'TreatmentItem',
    'TreatmentPlan',
    'TreatmentPlanGenerator',
    'add_a1_verdict_items',
    'apply_safety_overrides',
    'attach_fix_coverage',
    'augment_plan_step_out',
    'auto_safe_split',
    'build_fix_index',
    'enhance_plan_with_memory',
    'enhance_treatment_plan',
    'enhance_treatment_with_fix_patterns',
    'execution_order_index',
    'extract_cv_findings',
    'generate_treatment_plan',
    'infer_domain',
    'infer_severity',
    'iter_plan_items',
    'log_plan_generated',
    'make_treatment_item',
    'norm_plan_dict_key',
    'order_items_by_execution',
    'plan_dict_or_empty',
    'plan_item_preview',
    'plan_items_of',
    'plan_step_extras',
    'project_plan_stage_result',
    'reset_artifacts_after_plan',
    'set_plan_items',
    'verify_and_filter_self_audit',
]
logger = logging.getLogger(__name__)
@dataclass
class TreatmentItem:
    locator: str
    rule_id: str
    rule_applied: str
    conclusion: str
    severity: str
    priority: str
    strategy: str
    domain: str
    sources: list[str] = field(default_factory=list)
    evidence_strength: float = 0.0
    adjusted_confidence: float = 0.0
    evidence_type: str = ''
    sample_message: str = ''
    code_snippet: str = ''
    file_path: str = ''
    line: int = 0
    fixer_available: bool = False
    fixer_type: str = ''
    auto_safe: bool = False
    risk_score: float = 0.0
    risk_factors: list[str] = field(default_factory=list)
    dependencies: list[str] = field(default_factory=list)
    notes: str = ''
    side_effect_assessment: dict[str, Any] = field(default_factory=dict)
    regression_plan: dict[str, Any] = field(default_factory=dict)
    raw_finding: dict[str, Any] = field(default_factory=dict)
    finding_id: str = ''
    cv_context: dict[str, Any] = field(default_factory=dict)
    fix_guidance: str = ''
    governance_method: str = ''
    fanout_group: str = ''
    fanout_seed: str = ''
    fanout_level: str = ''
    fanout_strategy: str = ''
    fanout_module_tier: str = ''
    fanout_governance_level: str = ''
    fanout_governance_label: str = ''
    fanout_module_role: str = ''
    fanout_module_role_label: str = ''
    fanout_module_fanout: int | None = None
    fanout_mandatory: bool = False
    fanout_benefit_required: bool = False
    def to_dict(self) -> dict:
        return asdict(self)
@dataclass
class TreatmentPlan:
    items: list[TreatmentItem] = field(default_factory=list)
    total_items: int = 0
    by_priority: dict[str, int] = field(default_factory=dict)
    by_strategy: dict[str, int] = field(default_factory=dict)
    by_domain: dict[str, int] = field(default_factory=dict)
    risk_summary: dict[str, int] = field(default_factory=dict)
    dependency_chains: list[list[str]] = field(default_factory=list)
    execution_order: list[str] = field(default_factory=list)
    summary: str = ''
    generation_notes: list[str] = field(default_factory=list)
    side_effect_summary: dict[str, Any] = field(default_factory=dict)
    def to_dict(self) -> dict:
        return asdict(self)
CONCLUSION_RANK = {'confirmed': 0, 'investigated': 1, 'likely': 2, 'review': 3}
SEVERITY_RANK_TABLE = {**{k.lower(): v for k, v in SEVERITY_RANK.items()}, **SEVERITY_RANK}
_FINDING_MESSAGE_MAX_CHARS = 300
_DEFAULT_SKILL_DIR = ''
_DEFAULT_STRATEGY = 'manual_confirm'
_AUTO_SAFE_STRATEGY = 'auto_safe'
def _iter_sub_findings(raw) -> list:
    if isinstance(raw, (list, tuple)):
        return list(raw)
    return []
def _saa_check(saa, rule_id, file_path, line, locator, message):
    return saa.check_finding({
        'rule_id': rule_id,
        'file_path': file_path,
        'line': line,
        'locator': locator,
        'message': message,
    })
def _inner_finding_is_fp(saa, finding: dict, inner) -> bool:
    if not isinstance(inner, dict):
        return False
    inner_locator = inner.get('locator') or ''
    has_inner_locator = bool(inner_locator)
    inner_line = inner.get('line')
    if inner_line is None:
        inner_line = 0 if has_inner_locator else finding.get('line', 0)
    inner_file = inner.get('file') or inner.get('file_path')
    if not inner_file and not has_inner_locator:
        inner_file = finding.get('file') or finding.get('file_path') or ''
    result = _saa_check(
        saa,
        (inner.get('rule_id') or finding.get('rule_id') or ''),
        inner_file or '',
        inner_line,
        inner_locator or finding.get('locator', ''),
        (inner.get('message') or finding.get('message')
         or finding.get('sample_message') or ''))
    return result.is_fp
def _saa_finding_filter(saa, finding) -> tuple[bool, Any]:
    if not isinstance(finding, dict):
        return False, finding
    inner_findings = _iter_sub_findings(finding.get('findings'))
    if inner_findings:
        real_inner = [
            inner for inner in inner_findings
            if not _inner_finding_is_fp(saa, finding, inner)]
        if not real_inner:
            return True, finding
        sample = finding.get('sample_finding')
        sample_is_fp = (isinstance(sample, dict)
                        and _inner_finding_is_fp(saa, finding, sample))
        if len(real_inner) != len(inner_findings) or sample_is_fp:
            finding = {**finding, 'findings': real_inner}
            if sample_is_fp:
                finding['sample_finding'] = next(
                    (inner for inner in real_inner if isinstance(inner, dict)),
                    {})
        return False, finding
    result = _saa_check(
        saa,
        finding.get('rule_id', ''),
        finding.get('file') or finding.get('file_path') or '',
        finding.get('line', 0),
        finding.get('locator', ''),
        finding.get('message') or finding.get('sample_message') or '')
    return result.is_fp, finding
def _saa_filter(saa, findings) -> tuple:
    filtered = []
    fp_count = 0
    for finding in findings:
        is_fp, candidate = _saa_finding_filter(saa, finding)
        if is_fp:
            fp_count += 1
            continue
        filtered.append(candidate)
    return filtered, fp_count
def _coerce_findings(raw) -> list:
    if isinstance(raw, list):
        return raw
    if isinstance(raw, dict) and any(
            key in raw for key in ('locator', 'rule_id', 'conclusion')):
        return [raw]
    items = strict_iterable_list(raw)
    if raw is not None and not items:
        logger.warning('[PlanGen] findings 非序列形态(%s)，按空列表处理',
                       type(raw).__name__)
    return items
def _self_audit_flag_sources(report: dict):
    yield report
    cv_node = report.get(CAT_CROSS_VALIDATION)
    if not isinstance(cv_node, dict):
        return
    yield cv_node
    nested = cv_node.get('report')
    if isinstance(nested, dict):
        yield nested
def _self_audit_applied_of(report: dict) -> bool:
    for source in _self_audit_flag_sources(report):
        if 'self_audit_applied' in source:
            return signal_bool(source.get('self_audit_applied'))
    return False
def verify_and_filter_self_audit(findings: list[dict], diagnosis_report: dict, skill_dir: str=_DEFAULT_SKILL_DIR) -> list[dict]:
    findings = _coerce_findings(findings)
    if not isinstance(diagnosis_report, dict):
        logger.warning('[PlanGen] 诊断报告非 dict(%s)，跳过自审安全网过滤',
                       type(diagnosis_report).__name__)
        return findings
    saa_applied = _self_audit_applied_of(diagnosis_report)
    if saa_applied:
        logger.info('[PlanGen] 自审感知层标记确认: CV报告已执行自审感知过滤 (self_audit_applied=True)')
        return findings
    logger.warning('[PlanGen] 自审感知层标记缺失或为False (self_audit_applied=%s), 启动安全网过滤', saa_applied)
    try:
        saa = SelfAuditAwareness(skill_dir)
        if not saa.is_self_audit:
            logger.info('[PlanGen] 安全网过滤跳过: 非自审上下文 (is_self_audit=False)')
            return findings
        filtered, fp_count = _saa_filter(saa, findings)
        if fp_count > 0:
            logger.warning('[PlanGen] 安全网过滤: %d -> %d findings (自审感知安全网拦截 %d 项, CV阶段策略12未生效)', len(findings), len(filtered), fp_count)
        else:
            logger.info('[PlanGen] 安全网过滤完成: %d findings 全部通过 (0 项拦截)', len(findings))
        return filtered
    except Exception as e:
        logger.warning('[PlanGen] 自审感知安全网过滤异常(不阻断): %s, 返回原始findings', e)
        return findings
@dataclass(frozen=True)
class _A1Verdict:
    filepath: str
    needs_split: bool
    needs_refactor: bool
    health_score: float
    level: str
    top_suggestions: str
@dataclass(frozen=True)
class _A1ItemSpec:
    rule_id: str
    severity: str
    evidence: float
    confidence: float
    risk: float
    headline: str
    include_level: bool
    fallback_notes: str
_A1_SPLIT_SPEC = _A1ItemSpec(
    rule_id="A1-FILE-SPLIT", severity="P1", evidence=0.8, confidence=0.85,
    risk=0.3, headline="File needs splitting", include_level=False,
    fallback_notes="File exceeds size limit, consider splitting",
)
_A1_REFACTOR_SPEC = _A1ItemSpec(
    rule_id="A1-FILE-REFACTOR", severity="P2", evidence=0.7, confidence=0.75,
    risk=0.2, headline="File needs refactoring", include_level=True,
    fallback_notes="Multiple issues detected, consider refactoring",
)
def _make_a1_structural_item(verdict: _A1Verdict,
                             spec: _A1ItemSpec) -> TreatmentItem:
    detail = f"health_score={verdict.health_score}"
    if spec.include_level:
        detail += f", level={verdict.level}"
    return TreatmentItem(
        locator=verdict.filepath,
        rule_id=spec.rule_id,
        rule_applied='A1',
        conclusion='confirmed',
        severity=spec.severity,
        priority=spec.severity,
        strategy=_DEFAULT_STRATEGY,
        domain='structure',
        sources=['A1'],
        evidence_strength=spec.evidence,
        adjusted_confidence=spec.confidence,
        sample_message=f"{spec.headline}: {verdict.filepath} ({detail})",
        file_path=verdict.filepath,
        line=0,
        fixer_available=True,
        fixer_type='',
        auto_safe=False,
        risk_score=spec.risk,
        notes=verdict.top_suggestions or spec.fallback_notes,
    )
_A1_METHOD_KEYS = ("A1", "A")
_A1_METHOD_CONTAINER_KEYS = ("sub_results", "detector_results", "method_results")
_A1_ENTRY_PROFILE_PATHS: tuple[tuple[str, ...], ...] = (
    (),
    ("payload",),
    ("result",),
    ("result", "payload"),
    ("payload", "result"),
    ("payload", "result", "payload"),
)
def _profiles_of(node) -> list:
    if not isinstance(node, dict):
        return []
    profiles = node.get("profiles")
    return profiles if isinstance(profiles, list) and profiles else []
def _profiles_of_entry(entry) -> list:
    for path in _A1_ENTRY_PROFILE_PATHS:
        node = entry
        for key in path:
            node = node.get(key) if isinstance(node, dict) else None
        profiles = _profiles_of(node)
        if profiles:
            return profiles
    return []
def _profiles_of_container(container) -> list:
    profiles = _profiles_of(container)
    if profiles or not isinstance(container, dict):
        return profiles
    for key in _A1_METHOD_KEYS:
        profiles = _profiles_of_entry(container.get(key))
        if profiles:
            return profiles
    return []
def _a1_candidate_containers(report: dict) -> list[dict]:
    _payload = dict_or_empty(report.get("payload"))
    _cv_node = report.get(CAT_CROSS_VALIDATION)
    _cv_dict = dict_or_empty(_cv_node)
    _roots: list = [
        report,
        _payload,
        _payload.get("result"),
        _cv_node,
        _cv_dict.get("report"),
        _cv_dict.get("payload"),
        dict_or_empty(report.get("conclusion_layers"))
        .get("layer_2_detailed"),
    ]
    containers: list[dict] = []
    def _add(node) -> None:
        if (isinstance(node, dict) and node
                and all(node is not seen for seen in containers)):
            containers.append(node)
    for root in _roots:
        if not isinstance(root, dict):
            continue
        _add(root)
        for _key in _A1_METHOD_CONTAINER_KEYS:
            _add(root.get(_key))
    return containers
def _a1_profiles_from(diagnosis_report) -> list:
    if not isinstance(diagnosis_report, dict):
        return []
    for container in _a1_candidate_containers(diagnosis_report):
        profiles = _profiles_of_container(container)
        if profiles:
            return profiles
    return []
def _top_suggestions_of(verdict: dict) -> str:
    suggestions = verdict.get("suggestions", [])
    if not isinstance(suggestions, (list, tuple)):
        return ""
    return "; ".join(str(s) for s in suggestions[:3]) if suggestions else ""
def _a1_verdict_fields(p) -> _A1Verdict | None:
    if not isinstance(p, dict):
        return None
    verdict = p.get("verdict", {})
    if not isinstance(verdict, dict) or not verdict:
        return None
    filepath = p.get("filepath", "")
    if not isinstance(filepath, str) or not filepath.strip():
        return None
    return _A1Verdict(
        filepath=filepath.strip(),
        needs_split=signal_bool(verdict.get("needs_split", False)),
        needs_refactor=signal_bool(verdict.get("needs_refactor", False)),
        health_score=safe_float(verdict.get("health_score"), 1.0),
        level=str_or_empty(verdict.get("level")) or "healthy",
        top_suggestions=_top_suggestions_of(verdict),
    )
def _append_a1_structural_items(plan, verdict: _A1Verdict) -> int:
    if verdict.needs_split:
        plan.items.append(_make_a1_structural_item(verdict, _A1_SPLIT_SPEC))
        return 1
    if verdict.needs_refactor:
        plan.items.append(
            _make_a1_structural_item(verdict, _A1_REFACTOR_SPEC))
        return 1
    return 0
def _append_a1_profiles(plan, profiles: list) -> int:
    added = 0
    for p in profiles:
        verdict_fields = _a1_verdict_fields(p)
        if verdict_fields is None:
            continue
        added += _append_a1_structural_items(plan, verdict_fields)
    return added
def add_a1_verdict_items(plan, diagnosis_report: dict) -> None:
    try:
        profiles = _a1_profiles_from(diagnosis_report)
        if not profiles:
            return
        added = _append_a1_profiles(plan, profiles)
        logger.info("[A1-Treatment] Added %d verdict-based treatment items from A1 profiles",
                    added)
    except Exception as e:
        logger.warning("[A1-Treatment] Failed to add A1 verdict items: %s", e)
def _is_degraded_review(item: dict) -> bool:
    return (item.get('conclusion') == 'review'
            and '(降级)' in str(item.get('rule_applied', '')))
def _has_high_severity_subfinding(item: dict) -> bool:
    return any(
        isinstance(ff, dict)
        and normalize_severity_rank(ff.get('severity', 'P3')) <= 1
        for ff in _iter_sub_findings(item.get('findings')))
def _degraded_review_qualifies(item: dict) -> bool:
    """降级复核是否入治疗清单。

    全严重度强制口径：P0–P3 一律不得因严重度被丢弃。原实现只放行带
    P0/P1 子发现的降级复核，P2/P3 降级复核被静默丢弃，等于用严重度
    阈值把真实问题从治疗清单里抹掉。现在只保留置信度下限，严重度不再
    参与取舍；是否需要修复由治疗/审核环节逐项裁决。
    """
    if not _is_degraded_review(item):
        return False
    return safe_float(item.get(FIELD_ADJUSTED_CONFIDENCE)) >= 0.5
def _normalized_conclusion(value) -> str:
    return str_or_empty(value).strip().lower()
def _locator_rule_key(locator, rule_id) -> tuple[str, str] | None:
    locator_key = str(locator or '').strip()
    if not locator_key:
        return None
    return locator_key, str(rule_id or '').strip().upper()
def _finding_dedupe_key(finding: dict) -> tuple[str, str] | None:
    f0 = next((entry for entry in _iter_sub_findings(finding.get('findings'))
               if isinstance(entry, dict)), None)
    rule_id = ''
    for carrier in (f0, finding, finding.get('sample_finding')):
        if isinstance(carrier, dict) and carrier.get('rule_id'):
            rule_id = str(carrier['rule_id'])
            break
    return _locator_rule_key(finding.get('locator'), rule_id)
def _accept_finding_item(item: dict, findings: list, seen_keys: set) -> None:
    conclusion = _normalized_conclusion(item.get('conclusion'))
    if conclusion != item.get('conclusion'):
        item = {**item, 'conclusion': conclusion}
    candidate = None
    if conclusion in ('confirmed', 'investigated', 'likely'):
        candidate = item
    elif _degraded_review_qualifies(item):
        candidate = {**item, '_degraded_review': True}
    identity_key = _finding_dedupe_key(item)
    if identity_key is not None and identity_key in seen_keys:
        if candidate is None:
            return
        for index, existing in enumerate(findings):
            if _finding_dedupe_key(existing) != identity_key:
                continue
            if _cv_finding_sort_key(candidate) < _cv_finding_sort_key(existing):
                findings[index] = candidate
            return
    if candidate is None:
        return
    findings.append(candidate)
    if identity_key is not None:
        seen_keys.add(identity_key)
def _cv_findings_index_of(report) -> list:
    cv_data = dict_or_empty(report.get(CAT_CROSS_VALIDATION))
    nested_cv = dict_or_empty(cv_data.get('report'))
    for _candidate in (cv_data.get('findings_index'),
                       nested_cv.get('findings_index'),
                       report.get('findings_index')):
        if has_finding_entries(_candidate):
            return _candidate
    return []
def _accept_from_list(raw_items, findings, seen_keys) -> None:
    for item in strict_iterable_list(raw_items):
        if isinstance(item, dict):
            _accept_finding_item(item, findings, seen_keys)
def _accept_from_cv_results(report, findings, seen_keys) -> None:
    cv_results = dict_or_empty(
        dict_or_empty(report.get('layer_2')).get('cv_results'))
    for locator, result in cv_results.items():
        if not isinstance(result, dict):
            continue
        _accept_finding_item({**result, 'locator': locator}, findings, seen_keys)
def _accept_from_summary_keys(report, findings, seen_keys) -> None:
    summary = dict_or_empty(report.get('summary'))
    for key in ('confirmed_findings', 'investigated_findings', 'likely_findings'):
        conclusion = key.removesuffix('_findings')
        for item in strict_iterable_list(summary.get(key)):
            if not isinstance(item, dict):
                continue
            candidate = (item if item.get('conclusion')
                         else {**item, 'conclusion': conclusion})
            _accept_finding_item(candidate, findings, seen_keys)
def _severity_literals_of(finding: dict) -> list[str]:
    literals: list[str] = []
    for carrier in (finding.get('sample_finding'), finding):
        if isinstance(carrier, dict) and carrier.get('severity'):
            literals.append(str(carrier['severity']))
    return literals
def _finding_severity_rank(finding: dict) -> int:
    best = None
    for literal in _severity_literals_of(finding):
        rank = normalize_severity_rank(literal)
        best = rank if best is None else min(best, rank)
    sub_rank = _sub_severity_rank(finding)
    if sub_rank is not None:
        best = sub_rank if best is None else min(best, sub_rank)
    return 3 if best is None else best
def _cv_finding_sort_key(f) -> tuple:
    return (CONCLUSION_RANK.get(str(f.get('conclusion') or ''), 3),
            _finding_severity_rank(f),
            -safe_float(f.get(FIELD_ADJUSTED_CONFIDENCE)))
def extract_cv_findings(report: dict) -> list[dict]:
    findings = []
    seen_keys = set()
    if not isinstance(report, dict):
        logger.warning('[TreatmentPlan] 诊断报告非 dict(%s)，提取降级为空',
                       type(report).__name__)
        return findings
    _accept_from_list(_cv_findings_index_of(report), findings, seen_keys)
    _accept_from_cv_results(report, findings, seen_keys)
    _accept_from_summary_keys(report, findings, seen_keys)
    _accept_from_list(report.get('xv_findings'), findings, seen_keys)
    findings.sort(key=_cv_finding_sort_key)
    return findings
def _fix_details_of(fix_report) -> list:
    if not isinstance(fix_report, dict):
        logger.warning('[TreatmentPlan] fix_route_report 非 dict(%s)，索引降级为空',
                       type(fix_report).__name__)
        return []
    raw_details = fix_report.get('details') or []
    if not isinstance(raw_details, list):
        logger.warning('[TreatmentPlan] fix details 非 list(%s)，索引降级为空',
                       type(raw_details).__name__)
        raw_details = []
    return [d for d in raw_details if isinstance(d, dict)]
def _fix_basename(value) -> str:
    return finding_file_key(value).rsplit('/', 1)[-1]
def _rule_key(value) -> str:
    return str(value or '').strip().upper()
def _rule_file_of(detail: dict) -> tuple[str, str]:
    return (_rule_key(detail.get('rule_id')),
            finding_file_key(detail.get('file') or detail.get('file_path')))
class _FixIndex(dict):
    def __init__(self) -> None:
        super().__init__()
        self.primary_keys: set[str] = set()
        self.ambiguous_locator_keys: set[str] = set()
        self.ambiguous_basename_keys: set[str] = set()
        self.ambiguous_fuzzy_keys: set[str] = set()
        self.ambiguous_composite_keys: set[str] = set()
        self.basename_owners: dict[str, set[str]] = {}
def _fix_line_key(rule_val: str, file_val: str, line_val) -> str:
    return f'{rule_val}:{file_val}:{line_val}'
def _fix_fuzzy_key(rule_val: str, file_val: str) -> str:
    return f'{rule_val}:{file_val}'
def _rule_file_key_usable(file_val: str, rule_val: str) -> bool:
    return bool(file_val) and file_val != '?' and bool(rule_val)
def _index_locator_keys(index: _FixIndex, details: list) -> None:
    routes_by_locator: dict[str, set[tuple[str, str, int]]] = defaultdict(set)
    for d in details:
        locator = str(d.get('locator') or '')
        if not locator:
            continue
        rule_val, file_val = _rule_file_of(d)
        routes_by_locator[locator].add((
            rule_val, file_val, _to_line(d.get('line'), 'fix_detail')))
        if locator not in index:
            index[locator] = d
    index.ambiguous_locator_keys.update(
        locator for locator, routes in routes_by_locator.items()
        if len(routes) > 1)
def _index_composite_keys(index: dict, details: list) -> None:
    owners: dict[str, set[str]] = defaultdict(set)
    for d in details:
        rule_val, file_val = _rule_file_of(d)
        if not (rule_val or file_val):
            continue
        locator = str(d.get('locator') or '')
        key = _fix_line_key(rule_val, file_val,
                            _to_line(d.get('line'), 'fix_detail'))
        owners[key].add(locator)
        if key not in index:
            index[key] = d
    index.ambiguous_composite_keys.update(
        key for key, locators in owners.items() if len(locators) > 1)
def _index_fuzzy_keys(index: _FixIndex, details: list) -> None:
    lines_by_key: dict[str, set[int]] = defaultdict(set)
    for d in details:
        rule_val, file_val = _rule_file_of(d)
        if not _rule_file_key_usable(file_val, rule_val):
            continue
        fuzzy_key = _fix_fuzzy_key(rule_val, file_val)
        lines_by_key[fuzzy_key].add(_to_line(d.get('line'), 'fix_detail'))
        if fuzzy_key not in index:
            index[fuzzy_key] = d
    index.ambiguous_fuzzy_keys.update(
        key for key, lines in lines_by_key.items() if len(lines) > 1)
def _index_basename_keys(index: _FixIndex, details: list) -> None:
    owners: dict[str, set[str]] = defaultdict(set)
    fuzzy_lines: dict[str, set[int]] = defaultdict(set)
    for d in details:
        rule_val, file_val = _rule_file_of(d)
        if not _rule_file_key_usable(file_val, rule_val):
            continue
        line_val = _to_line(d.get('line'), 'fix_detail')
        bn = _fix_basename(file_val)
        fuzzy_key = _fix_fuzzy_key(rule_val, bn)
        fuzzy_lines[fuzzy_key].add(line_val)
        for key in (_fix_line_key(rule_val, bn, line_val), fuzzy_key):
            owners[key].add(file_val)
            if key not in index:
                index[key] = d
    index.ambiguous_basename_keys.update(
        key for key, paths in owners.items() if len(paths) > 1)
    index.ambiguous_fuzzy_keys.update(
        key for key, lines in fuzzy_lines.items() if len(lines) > 1)
    index.basename_owners = owners
def build_fix_index(fix_report: dict) -> dict[str, dict]:
    index = _FixIndex()
    details = _fix_details_of(fix_report)
    _index_locator_keys(index, details)
    _index_composite_keys(index, details)
    _index_fuzzy_keys(index, details)
    index.primary_keys.update(index)
    _index_basename_keys(index, details)
    return index
def _to_line(raw, source: str) -> int:
    line = coerce_line(raw)
    if line == 0 and raw not in (None, 0, ''):
        logger.debug('[TreatmentPlan] %s line 字段不可用(%r)，降级为 0',
                     source, raw)
    return line
def _snippet_from(carrier) -> str:
    if not isinstance(carrier, dict):
        return ''
    snippet = str(carrier.get('code_snippet', '') or '')
    if not snippet:
        snippet = str(dict_or_empty(carrier.get('raw_finding'))
                      .get('code_snippet', '') or '')
    return snippet
def _f0_and_sample(finding) -> tuple:
    sample = finding.get('sample_finding', {})
    findings_list = _iter_sub_findings(finding.get('findings'))
    f0 = next(
        (entry for entry in findings_list if isinstance(entry, dict)), None)
    return f0, sample
def _resolve_file_path(file_path: str, skill_dir: str) -> str:
    if file_path:
        _resolved = resolve_finding_file_path(file_path, skill_dir or '')
        if _resolved:
            return _resolved
    return file_path
def _finding_message_of(carrier: dict) -> str:
    return str(
        carrier.get('message') or carrier.get('sample_message') or ''
    )[:_FINDING_MESSAGE_MAX_CHARS]
def _finding_text_fields(carrier: dict, source: str) -> tuple[str, str, int, str]:
    return (str(carrier.get('rule_id') or ''),
            str(carrier.get('file') or carrier.get('file_path') or ''),
            _to_line(carrier.get('line'), source),
            _finding_message_of(carrier))
def _main_fields_of(f0, sample, carrier) -> tuple:
    rule_id, file_path, line, message = '', '', 0, ''
    if isinstance(f0, dict):
        rule_id, file_path, line, message = _finding_text_fields(
            f0, 'findings[0]')
    for src in (carrier, sample):
        if not isinstance(src, dict):
            continue
        if not rule_id:
            rule_id = str(src.get('rule_id') or '')
        if not file_path:
            file_path = str(src.get('file') or src.get('file_path') or '')
        if line == 0:
            line = _to_line(src.get('line'), 'finding')
        if not message:
            message = _finding_message_of(src)
    return rule_id, file_path, line, message
def _fix_lookup_keys(locator: str, rule_id: str,
                     file_path: str, line: int) -> list[tuple[str, bool, bool]]:
    keys: list[tuple[str, bool, bool]] = (
        [(locator, False, False)] if locator else [])
    rule_key = _rule_key(rule_id)
    file_key = finding_file_key(file_path)
    if rule_key or file_key:
        keys.append((_fix_line_key(rule_key, file_key, line), False, False))
    if rule_key and file_key:
        bn = _fix_basename(file_key)
        keys += [(_fix_fuzzy_key(rule_key, file_key), False, True),
                 (_fix_line_key(rule_key, bn, line), True, False),
                 (_fix_fuzzy_key(rule_key, bn), True, True)]
    return keys
def _is_absolute_file_key(file_key: str) -> bool:
    return (file_key.startswith('/')
            or (len(file_key) >= 3 and file_key[1] == ':'
                and file_key[2] == '/'))
def _basename_crosses_file_paths(key: str, file_path: str,
                                  owners: dict) -> bool:
    file_key = finding_file_key(file_path)
    if _is_absolute_file_key(file_key):
        return any(_is_absolute_file_key(owner) and owner != file_key
                   for owner in owners.get(key, ()))
    if '/' not in file_key:
        return False
    return any('/' in owner and not _is_absolute_file_key(owner)
               and owner != file_key
               for owner in owners.get(key, ()))
def _lookup_fix_info(fix_index, locator, rule_id, file_path, line) -> dict:
    ambiguous = getattr(fix_index, 'ambiguous_basename_keys', frozenset())
    ambiguous_fuzzy = getattr(fix_index, 'ambiguous_fuzzy_keys', frozenset())
    ambiguous_locators = getattr(fix_index, 'ambiguous_locator_keys', frozenset())
    ambiguous_composites = getattr(
        fix_index, 'ambiguous_composite_keys', frozenset())
    primary_keys = getattr(fix_index, 'primary_keys', frozenset())
    basename_owners = getattr(fix_index, 'basename_owners', {})
    lookup_locator = '' if locator in ambiguous_locators else locator
    for key, is_basename_fallback, is_fuzzy in _fix_lookup_keys(
            lookup_locator, rule_id, file_path, line):
        if ((is_fuzzy or not key) and key in ambiguous_fuzzy) or (
                not is_basename_fallback and key in ambiguous_composites
                and key != lookup_locator):
            continue
        if ((key in ambiguous or key in ambiguous_composites)
                and (is_basename_fallback or key not in primary_keys)):
            continue
        if (is_basename_fallback and _basename_crosses_file_paths(
                key, file_path, basename_owners)):
            continue
        _hit = fix_index.get(key)
        if isinstance(_hit, dict) and _hit:
            return _hit
    return {}
def _code_snippet_of(finding, f0, sample) -> str:
    return (_snippet_from(f0)
            or _snippet_from(sample)
            or str(finding.get('code_snippet', '') or ''))
def _line_with_locator_fallback(line: int, locator: str) -> int:
    if line != 0 or not locator:
        return line
    _parsed = parse_locator_line(locator)
    if _parsed > 0:
        return _parsed
    logger.debug('[TreatmentPlan] locator行号解析失败: %s', locator)
    return line
def _raw_and_finding_id(finding, f0, sample) -> tuple:
    _sample = dict_or_empty(sample)
    raw_finding = f0 or _sample or dict_or_empty(finding)
    finding_id = ''
    for carrier in (f0, _sample or None, finding):
        if carrier is not None and carrier.get('finding_id'):
            finding_id = str(carrier['finding_id'])
            break
    return raw_finding, finding_id
def _cv_context_of(finding) -> dict:
    _cv_ctx = {}
    for _ck in ("conclusion", "rule_applied", "rule_family", "_confidence_source",
                "_is_degraded", "_degraded_reason", "_source_count", "source_count",
                "_multi_rule_boost", "_secondary_rules", "_all_matched_rules"):
        if finding.get(_ck) is not None:
            _cv_ctx[_ck] = finding.get(_ck)
    if "conclusion" in _cv_ctx:
        _cv_ctx["conclusion"] = _normalized_conclusion(_cv_ctx["conclusion"])
    if finding.get("_annotation_adjustments"):
        _cv_ctx["_annotation_adjustments"] = finding.get("_annotation_adjustments")
    if finding.get("_conclusion_params"):
        _cv_ctx["_conclusion_params"] = finding.get("_conclusion_params")
    return _cv_ctx
def _fixer_available_of(fix_info: dict) -> bool:
    return (bool(fix_info)
            and signal_bool(fix_info.get('has_fixer', False))
            and fix_info.get('status') != 'no_fixer')
def _item_notes_of(finding: dict) -> str:
    return '[降级来源]需人工确认' if finding.get('_degraded_review') else ''
def _optional_int(value: object) -> int | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    if isinstance(value, float) and not value.is_integer():
        return None
    return int(value)
def make_treatment_item(finding: dict, fix_index: dict, skill_dir: str=_DEFAULT_SKILL_DIR) -> TreatmentItem:
    if not isinstance(finding, dict):
        logger.warning('[PlanGen] finding 非 dict(%s)，按空条目处理',
                       type(finding).__name__)
    finding = dict_or_empty(finding)
    fix_index = dict_or_empty(fix_index)
    locator = str_or_empty(finding.get('locator'))
    f0, sample = _f0_and_sample(finding)
    rule_id, file_path, line, message = _main_fields_of(f0, sample, finding)
    original_file_path = file_path
    file_path = _resolve_file_path(file_path, skill_dir)
    line = _line_with_locator_fallback(line, locator)
    fix_info = _lookup_fix_info(
        fix_index, locator, rule_id, original_file_path, line)
    if not fix_info and file_path != original_file_path:
        fix_info = _lookup_fix_info(
            fix_index, locator, rule_id, file_path, line)
    sources = normalize_sources(finding.get('sources'))
    domain = infer_domain(sources)
    code_snippet = _code_snippet_of(finding, f0, sample)
    raw_finding, finding_id = _raw_and_finding_id(finding, f0, sample)
    _cv_ctx = _cv_context_of(finding)
    severity = infer_severity(finding)
    fixer_available = _fixer_available_of(fix_info)
    auto_safe = fixer_available and signal_bool(
        fix_info.get('auto_safe') or False)
    return TreatmentItem(
        locator=locator,
        rule_id=rule_id,
        rule_applied=str_or_empty(finding.get('rule_applied')),
        conclusion=_normalized_conclusion(finding.get('conclusion')) or 'review',
        severity=severity,
        priority='',
        strategy=_AUTO_SAFE_STRATEGY if auto_safe else _DEFAULT_STRATEGY,
        domain=domain,
        sources=sources,
        evidence_strength=safe_float(finding.get(FIELD_EVIDENCE_STRENGTH)),
        adjusted_confidence=safe_float(finding.get(FIELD_ADJUSTED_CONFIDENCE)),
        evidence_type=str_or_empty(finding.get('evidence_type')),
        sample_message=message,
        code_snippet=code_snippet,
        file_path=file_path,
        line=line,
        fixer_available=fixer_available,
        fixer_type=str_or_empty(fix_info.get('fixer_type')),
        auto_safe=auto_safe,
        risk_score=0.0,
        notes=_item_notes_of(finding),
        raw_finding=raw_finding,
        finding_id=finding_id,
        cv_context=_cv_ctx,
        fix_guidance=get_fix_guidance(rule_id, message),
        governance_method=_governance_method_of(rule_id, finding),
        fanout_group=str_or_empty(finding.get('fanout_group')),
        fanout_seed=str_or_empty(finding.get('fanout_seed')),
        fanout_level=str_or_empty(finding.get('fanout_level')),
        fanout_strategy=str_or_empty(finding.get('fanout_strategy')),
        fanout_module_tier=str_or_empty(finding.get('fanout_module_tier')),
        fanout_governance_level=str_or_empty(
            finding.get('fanout_governance_level')),
        fanout_governance_label=str_or_empty(
            finding.get('fanout_governance_label')),
        fanout_module_role=str_or_empty(finding.get('fanout_module_role')),
        fanout_module_role_label=str_or_empty(
            finding.get('fanout_module_role_label')),
        fanout_module_fanout=_optional_int(
            finding.get('fanout_module_fanout')),
        fanout_mandatory=signal_bool(finding.get('fanout_mandatory')),
        fanout_benefit_required=signal_bool(
            finding.get('fanout_benefit_required')),
    )
_FAN_GOVERNANCE_RULES = frozenset({
    "D9-HIGH-FANOUT", "D9-HIGH-FANIN", "D9-LAYER",
    "D9-LAYER-IMPLICIT", "D9-CYCLE", "D9-HUB",
    "excessive_coupling",
})
def _governance_method_of(rule_id: str, finding: dict | None = None) -> str:
    declared = str(dict_or_empty(finding).get('governance_method') or '')
    if declared:
        return declared
    normalized_rule_id = normalize_rule_id(rule_id) or ""
    return "converge_dependency" if normalized_rule_id in _FAN_GOVERNANCE_RULES else ""
_DOMAIN_SOURCE_IDS = {
    'diagnosis': {'A1', 'A2', 'B1', 'B2', 'C2', 'A', 'B'},
    'fanout': {'fanout'},
    'diag': {'D1', 'E1', 'E2', 'C', 'D'},
    'test': {'F1', 'F2', 'F3', 'E'},
    'treatment': {'G1', 'G2', 'G3', 'G4', 'G5', 'G6', 'F'},
}
def infer_domain(sources: list[str]) -> str:
    src_set = set(normalize_sources(sources))
    domains = [domain for domain, ids in _DOMAIN_SOURCE_IDS.items()
               if src_set & ids]
    if len(domains) >= 2:
        return 'mixed'
    return domains[0] if domains else 'unknown'
def _sub_severity_rank(finding: dict) -> int | None:
    best_rank = None
    for sub in _iter_sub_findings(finding.get('findings')):
        if not isinstance(sub, dict) or not sub.get('severity'):
            continue
        rank = normalize_severity_rank(sub['severity'])
        if rank == 0:
            return 0
        best_rank = rank if best_rank is None else min(best_rank, rank)
    return best_rank
def infer_severity(finding: dict) -> str:
    return severity_literal_from_rank(_finding_severity_rank(finding))
def _locator_groups_index(items) -> dict[str, list]:
    locator_groups: dict[str, list] = {}
    for item in items:
        if item.locator:
            locator_groups.setdefault(item.locator, []).append(item)
    return locator_groups
def _lead_index_of(locator_groups: dict) -> dict:
    return {locator: group[0] for locator, group in locator_groups.items()}
def _locator_groups_of(plan: TreatmentPlan) -> tuple:
    locator_groups = _locator_groups_index(plan.items)
    groups: list[list] = list(locator_groups.values())
    groups.extend([item] for item in plan.items if not item.locator)
    return locator_groups, groups
def _category_indexes_of(locator_groups) -> tuple:
    item_categories: dict[str, set[str]] = {}
    category_to_locators: dict[str, list[str]] = defaultdict(list)
    for loc, grp in locator_groups.items():
        categories = set()
        for member in grp:
            if not member.rule_id:
                continue
            cat = (_resolve_rule_category(member.rule_id)
                   or _suffix_cohort_category(member.rule_id))
            if cat:
                categories.add(cat)
        item_categories[loc] = categories
        for cat in sorted(categories):
            if loc not in category_to_locators[cat]:
                category_to_locators[cat].append(loc)
    return item_categories, category_to_locators
def _file_locators_of(plan: TreatmentPlan) -> dict:
    file_to_locators: dict[str, list[str]] = defaultdict(list)
    for item in plan.items:
        if (item.file_path and item.locator
                and item.locator not in file_to_locators[item.file_path]):
            file_to_locators[item.file_path].append(item.locator)
    return file_to_locators
class _DependencyIndex(NamedTuple):
    groups: list
    locator_groups: dict
    item_categories: dict
    category_to_locators: dict
    file_to_locators: dict
def _dependency_index_of(plan: TreatmentPlan) -> _DependencyIndex:
    locator_groups, groups = _locator_groups_of(plan)
    item_categories, category_to_locators = _category_indexes_of(locator_groups)
    return _DependencyIndex(groups, locator_groups, item_categories,
                            category_to_locators, _file_locators_of(plan))
class _PriorityPolicy:
    @staticmethod
    def is_p0(sev_rank, conc_rank, is_security, conclusion) -> bool:
        return ((sev_rank <= 0 and conc_rank <= 0)
                or (is_security and conclusion == 'confirmed'))
    @staticmethod
    def is_p1(sev_rank, conc_rank, conclusion) -> bool:
        return ((sev_rank <= 1 and conclusion == 'confirmed')
                or (sev_rank <= 0 and conc_rank == 1))
    @staticmethod
    def is_p2(sev_rank, conclusion) -> bool:
        return conclusion in ('confirmed', 'investigated', 'likely') and sev_rank <= 2
    @classmethod
    def priority_of(cls, item) -> str:
        sev_rank = normalize_severity_rank(item.severity)
        conc_rank = CONCLUSION_RANK.get(item.conclusion, 3)
        rule_family = item.rule_id.lower() if item.rule_id else ''
        is_security = (
            _resolve_rule_category(item.rule_id) == 'security'
            or any(sec in rule_family for sec in _SECURITY_RULE_SUBSTRINGS)
        )
        if cls.is_p0(sev_rank, conc_rank, is_security, item.conclusion):
            return 'P0'
        if cls.is_p1(sev_rank, conc_rank, item.conclusion):
            return 'P1'
        if cls.is_p2(sev_rank, item.conclusion):
            return 'P2'
        return 'P3'
class _PlanSummarizer:
    @staticmethod
    def counts(plan) -> None:
        plan.total_items = len(plan.items)
        plan.by_priority = defaultdict(int)
        plan.by_strategy = defaultdict(int)
        plan.by_domain = defaultdict(int)
        plan.risk_summary = {'low': 0, 'medium': 0, 'high': 0}
        for item in plan.items:
            plan.by_priority[item.priority] += 1
            plan.by_strategy[item.strategy] += 1
            plan.by_domain[item.domain] += 1
            plan.risk_summary[_RiskAssessor.level(item.risk_score)] += 1
    @staticmethod
    def _dist_text(index) -> str:
        return '、'.join(f'{k}={v}' for k, v in sorted(index.items()))
    @classmethod
    def text(cls, plan) -> str:
        parts = []
        if plan.total_items > 0:
            parts.append(f'共{plan.total_items}项治疗条目')
            if plan.by_priority:
                parts.append(f'优先级分布: {cls._dist_text(plan.by_priority)}')
            if plan.by_strategy:
                parts.append(f'策略分布: {cls._dist_text(plan.by_strategy)}')
        else:
            parts.append('无需治疗')
        return '。'.join(parts) + '。'
    @staticmethod
    def side_effect(plan) -> dict:
        risk_levels = [_RiskAssessor.level(item.risk_score)
                       for item in plan.items]
        high_risk = risk_levels.count('high')
        medium_risk = risk_levels.count('medium')
        low_risk = risk_levels.count('low')
        full_regression_needed = sum(
            1 for item in plan.items
            if item.regression_plan.get('full_regression'))
        return {
            'high_risk_items': high_risk,
            'medium_risk_items': medium_risk,
            'low_risk_items': low_risk,
            'full_regression_needed': full_regression_needed,
            'targeted_regression': full_regression_needed == 0,
            'assessment': (f'{high_risk}高风险/{medium_risk}中风险/{low_risk}低风险, '
                           + ('全部走定向回归(不跑全量)'
                              if full_regression_needed == 0
                              else f'{full_regression_needed}项需全量回归'))}
    @classmethod
    def apply(cls, plan) -> None:
        cls.counts(plan)
        plan.summary = cls.text(plan)
        plan.side_effect_summary = cls.side_effect(plan)
class _PriorityFrontier:
    def __init__(self, sort_key_fn=None) -> None:
        self._heap: list = []
        self._counter = 0
        self._sort_key_fn = sort_key_fn
    def push(self, node) -> None:
        key = self._sort_key_fn(node) if self._sort_key_fn else (node,)
        heapq.heappush(self._heap, (key, self._counter, node))
        self._counter += 1
    def pop(self):
        return heapq.heappop(self._heap)[2]
    def __bool__(self) -> bool:
        return bool(self._heap)
class _ExecutionOrderBuilder:
    _STRATEGY_ORDER: ClassVar[dict[str, int]] = {
        _DEFAULT_STRATEGY: 1, _AUTO_SAFE_STRATEGY: 1}
    @staticmethod
    def views(plan) -> tuple:
        locator_groups = _locator_groups_index(plan.items)
        locator_deps: dict[str, set[str]] = defaultdict(set)
        for item in plan.items:
            if item.locator:
                locator_deps[item.locator].update(item.dependencies or [])
        return locator_groups, locator_deps
    def sort_key(self, locator, locator_groups) -> tuple:
        group = locator_groups.get(locator)
        if not group:
            return (9, 9, 1.0)
        best_prio = min(
            SEVERITY_RANK_TABLE.get(str(it.priority or '').strip().upper(), 9)
            for it in group)
        best_strat = min(self._STRATEGY_ORDER.get(it.strategy, 9) for it in group)
        max_risk = max(it.risk_score or 0.0 for it in group)
        return (best_prio, best_strat, max_risk)
    @staticmethod
    def _in_degree_table(deps) -> tuple:
        in_degree = dict.fromkeys(deps, 0)
        reverse_adj: dict[str, list[str]] = defaultdict(list)
        for node, node_deps in deps.items():
            for dep in node_deps:
                if dep in deps:
                    in_degree[node] += 1
                    reverse_adj[dep].append(node)
        return in_degree, reverse_adj
    @staticmethod
    def _relax_dependents(node, reverse_adj, in_degree, in_result,
                          frontier) -> None:
        for dependent in reverse_adj.get(node, []):
            if dependent in in_result:
                continue
            in_degree[dependent] -= 1
            if in_degree[dependent] == 0:
                frontier.push(dependent)
    def topological_sort(self, deps: dict[str, set[str]], sort_key_fn=None) -> list[str]:
        in_degree, reverse_adj = self._in_degree_table(deps)
        frontier = _PriorityFrontier(sort_key_fn)
        for node, deg in in_degree.items():
            if deg == 0:
                frontier.push(node)
        result = []
        in_result = set()
        while frontier:
            node = frontier.pop()
            if node in in_result:
                continue
            result.append(node)
            in_result.add(node)
            self._relax_dependents(
                node, reverse_adj, in_degree, in_result, frontier)
        for node in deps:
            if node not in in_result:
                result.append(node)
        return result
class _RiskAssessor:
    @staticmethod
    def uncertainty(item) -> tuple[float, list[str]]:
        score = 0.0
        factors = []
        conclusion = item.conclusion if isinstance(item.conclusion, str) else ''
        if conclusion in ('investigated', 'likely'):
            factors.append(f'结论为{conclusion}（未完全确认）')
            score += 0.25
        elif conclusion == 'review':
            factors.append('结论仅为review级别')
            score += 0.4
        if item.adjusted_confidence < 0.5:
            factors.append(f'调整后置信度偏低({item.adjusted_confidence:.2f})')
            score += 0.2
        elif item.adjusted_confidence < 0.7:
            score += 0.1
        if item.evidence_strength < 0.5:
            factors.append(f'证据强度偏低({item.evidence_strength:.2f})')
            score += 0.15
        return score, factors
    @staticmethod
    def impact(item) -> tuple[float, list[str]]:
        score = 0.0
        factors = []
        if not item.fixer_available:
            factors.append('无可用修复器')
            score += 0.15
        if item.fixer_type == 'eliminator' and item.conclusion != 'confirmed':
            factors.append('eliminator修复器+非confirmed结论，回滚风险较高')
            score += 0.2
        if item.domain == 'mixed':
            factors.append('跨域发现，修复可能影响多处')
            score += 0.1
        return score, factors
    @staticmethod
    def scale(same_file_count: int) -> tuple[float, list[str]]:
        if same_file_count >= 3:
            return 0.1, [f'同文件有{same_file_count}处修复，累积影响']
        return 0.0, []
    @staticmethod
    def baseline_of(item) -> float:
        prior = item.side_effect_assessment
        cached = prior.get('_baseline_risk') if isinstance(prior, dict) else None
        if isinstance(cached, (int, float)) and not isinstance(cached, bool):
            return float(cached)
        return item.risk_score
    @classmethod
    def factor_score(cls, item, same_file_count: int,
                     baseline: float | None = None) -> tuple:
        factors = []
        score = item.risk_score if baseline is None else baseline
        if score > 0:
            factors.append(f'构造期预置基线风险({score:.2f})')
        for delta, part_factors in (
                cls.uncertainty(item),
                cls.impact(item),
                cls.scale(same_file_count)):
            score += delta
            factors.extend(part_factors)
        return min(score, 1.0), factors
    @staticmethod
    def level(risk_score: float) -> str:
        if risk_score >= 0.5:
            return 'high'
        if risk_score >= 0.25:
            return 'medium'
        return 'low'
    @classmethod
    def assess(cls, plan) -> None:
        file_count_cache: dict[str, int] = defaultdict(int)
        for item in plan.items:
            if item.file_path:
                file_count_cache[item.file_path] += 1
        for item in plan.items:
            same_file_count = max(
                0, file_count_cache.get(item.file_path, 0) - 1)
            baseline = cls.baseline_of(item)
            item.risk_score, factors = cls.factor_score(
                item, same_file_count, baseline)
            item.risk_factors = factors
            item.side_effect_assessment = {
                'risk_level': cls.level(item.risk_score),
                'risk_score': round(item.risk_score, 3),
                'factors': factors,
                '_baseline_risk': baseline}
            item.regression_plan = default_regression_plan(item.file_path)
class _DependencyPlanner:
    def __init__(self, log, skill_dir: str) -> None:
        self._log = log
        self.skill_dir = skill_dir
    @staticmethod
    def _group_prio_rank(group) -> int:
        return min(
            (normalize_severity_rank(member.priority) for member in group),
            default=normalize_severity_rank('P3'))
    def apply(self, plan: TreatmentPlan) -> None:
        index = _dependency_index_of(plan)
        for group in index.groups:
            self._apply_category_dependencies(group, index)
        lead_index = _lead_index_of(index.locator_groups)
        for group in index.groups:
            self._apply_file_priority_edges(group, index, lead_index)
        self._enrich_region_dependencies(plan, lead_index)
        self._collect_dependency_chains(plan, lead_index)
    def _priority_precedes(self, other_locator: str, index: _DependencyIndex,
                           lead, item_prio_rank: int) -> bool:
        return (self._group_prio_rank(index.locator_groups[other_locator])
                < item_prio_rank
                and other_locator not in lead.dependencies)
    def _apply_file_priority_edges(self, group: list,
                                   index: _DependencyIndex, lead_index: dict) -> None:
        lead = group[0]
        locator = lead.locator
        if not (lead.file_path and locator):
            return
        item_prio_rank = self._group_prio_rank(group)
        for other_locator in index.file_to_locators.get(lead.file_path, []):
            if other_locator == locator:
                continue
            if not self._priority_precedes(other_locator, index,
                                           lead, item_prio_rank):
                continue
            if self._would_create_cycle(other_locator, locator, lead_index):
                continue
            for member in group:
                member.dependencies.append(other_locator)
    @staticmethod
    def _dependency_categories_of(group: list, index: _DependencyIndex) -> list[str]:
        categories = index.item_categories.get(group[0].locator, set())
        if not categories:
            return (['syntax_error']
                    if any(member.rule_id for member in group) else [])
        deps: list[str] = []
        for cat in sorted(categories):
            for dep_cat in _FIX_DEPENDENCIES.get(cat, ['syntax_error']):
                if dep_cat not in deps:
                    deps.append(dep_cat)
        return deps
    @staticmethod
    def _merge_dependencies(member, deps: list[str]) -> None:
        merged = [dep for dep in (member.dependencies or ())
                  if dep != member.locator]
        for dep in deps:
            if dep != member.locator and dep not in merged:
                merged.append(dep)
        member.dependencies = merged
    @classmethod
    def _apply_category_dependencies(cls, group: list,
                                    index: _DependencyIndex) -> None:
        lead = group[0]
        locator = lead.locator
        deps: list[str] = []
        for dep_cat in cls._dependency_categories_of(group, index):
            for other_locator in index.category_to_locators.get(dep_cat, []):
                if other_locator != locator and other_locator not in deps:
                    deps.append(other_locator)
        for member in group:
            cls._merge_dependencies(member, deps)
    def _collect_dependency_chains(self, plan: TreatmentPlan,
                                   lead_index: dict) -> None:
        visited = set()
        for item in plan.items:
            if not item.locator or item.locator in visited:
                continue
            chain = self._trace_dependency_chain(item.locator, lead_index, set())
            if len(chain) > 1:
                plan.dependency_chains.append(chain)
                visited.update(chain)
    def _trace_dependency_chain(self, locator: str, index: dict, visited: set) -> list[str]:
        if locator in visited or locator not in index:
            return [locator]
        visited.add(locator)
        chain = []
        item = index[locator]
        for dep_loc in item.dependencies:
            for seg in self._trace_dependency_chain(dep_loc, index, visited):
                if seg not in chain:
                    chain.append(seg)
        if locator not in chain:
            chain.append(locator)
        return chain
    @staticmethod
    def _would_create_cycle(start: str, target: str, locator_index: dict) -> bool:
        if start == target:
            return True
        stack = [start]
        seen = {start}
        while stack:
            cur = stack.pop()
            cur_item = locator_index.get(cur)
            if cur_item is None:
                continue
            for dep in cur_item.dependencies:
                if dep == target:
                    return True
                if dep not in seen:
                    seen.add(dep)
                    stack.append(dep)
        return False
    @staticmethod
    def _region_candidates(plan) -> list:
        seen: set[str] = set()
        candidates = []
        for it in plan.items:
            if it.file_path and it.line and it.locator and it.locator not in seen:
                seen.add(it.locator)
                candidates.append(it)
        return candidates
    @staticmethod
    def _must_before_map(graph) -> dict:
        before_map: dict[str, set[str]] = {}
        for edge in graph.edges:
            if edge.dep_type == _DependencyType.MUST_BEFORE:
                before_map.setdefault(edge.target, set()).add(edge.source)
        return before_map
    def _add_predecessor(self, item, pred: str, locator_index: dict) -> bool:
        if pred == item.locator or pred in item.dependencies:
            return False
        if self._would_create_cycle(pred, item.locator, locator_index):
            return False
        item.dependencies.append(pred)
        return True
    def _merge_before_edges(self, plan, before_map, lead_index: dict) -> int:
        added = 0
        for item in plan.items:
            for pred in before_map.get(item.locator, ()):
                if self._add_predecessor(item, pred, lead_index):
                    added += 1
        return added
    def _enrich_region_dependencies(self, plan: TreatmentPlan,
                                    lead_index: dict | None = None) -> None:
        candidates = self._region_candidates(plan)
        if len(candidates) < 2:
            return
        findings = [{"id": it.locator, "file": it.file_path, "line": it.line,
                     "rule_id": it.rule_id} for it in candidates]
        try:
            graph = _build_dependency_graph(findings, self.skill_dir)
        except Exception as e:
            self._log.debug('区域级依赖构建失败(降级为类目级推断): %s', e)
            return
        if lead_index is None:
            lead_index = _lead_index_of(_locator_groups_index(plan.items))
        added = self._merge_before_edges(
            plan, self._must_before_map(graph), lead_index)
        if added:
            self._log.info('[DepGraph] 区域级依赖增强: +%d 边', added)
class TreatmentPlanGenerator:
    def __init__(self, skill_dir: str=_DEFAULT_SKILL_DIR):
        self.skill_dir = skill_dir
        self._log = logger.getChild('plan_generator')
    def generate(self, diagnosis_report: dict, fix_route_report: dict | None=None,
                 extra_findings: list[dict] | None=None) -> TreatmentPlan:
        plan = TreatmentPlan()
        plan.generation_notes.append('治疗方案从交叉验证报告自动生成')
        fix_index = build_fix_index(fix_route_report) if fix_route_report else {}
        findings = extract_cv_findings(diagnosis_report)
        _had_findings = bool(findings)
        if findings:
            findings = verify_and_filter_self_audit(findings, diagnosis_report, self.skill_dir)
        if findings:
            self._log.info('[PlanGen] 提取 %d 个 confirmed/investigated findings (自审感知验证后)', len(findings))
            for finding in findings:
                item = make_treatment_item(finding, fix_index, self.skill_dir)
                plan.items.append(item)
        _append_extra_findings(plan, extra_findings, self.skill_dir, fix_index)
        add_a1_verdict_items(plan, diagnosis_report)
        if not plan.items:
            plan.summary = ('所有 findings 被自审感知层安全网过滤，无需治疗方案'
                            if _had_findings
                            else '无 confirmed/investigated findings，无需治疗方案')
            return plan
        for item in plan.items:
            item.priority = _PriorityPolicy.priority_of(item)
            if not item.strategy:
                item.strategy = _DEFAULT_STRATEGY
        _RiskAssessor.assess(plan)
        _DependencyPlanner(self._log, self.skill_dir).apply(plan)
        builder = _ExecutionOrderBuilder()
        locator_groups, locator_deps = builder.views(plan)
        sorted_locators = builder.topological_sort(
            dict(locator_deps),
            lambda loc: builder.sort_key(loc, locator_groups))
        plan.execution_order = [
            loc for loc in sorted_locators if loc in locator_groups]
        _PlanSummarizer.apply(plan)
        return plan
_EXTRA_FINDING_MERGE_FIELDS = (
    'fanout_group', 'fanout_seed', 'fanout_level',
    'fanout_strategy', 'governance_method',
    'fanout_module_tier', 'fanout_governance_level',
    'fanout_governance_label', 'fanout_module_role',
    'fanout_module_role_label', 'fanout_module_fanout',
    'fanout_mandatory', 'fanout_benefit_required',
)
_EXTRA_FINDING_ACCUMULATIVE_BOOL_FIELDS = frozenset({
    'fanout_mandatory', 'fanout_benefit_required',
})
def _merge_extra_finding_fields(existing: TreatmentItem,
                                candidate: TreatmentItem) -> None:
    for field_name in _EXTRA_FINDING_MERGE_FIELDS:
        incoming = getattr(candidate, field_name)
        if field_name in _EXTRA_FINDING_ACCUMULATIVE_BOOL_FIELDS:
            if incoming:
                setattr(existing, field_name, True)
            continue
        if getattr(existing, field_name) in (None, ''):
            setattr(existing, field_name, incoming)
def _append_extra_findings(plan: TreatmentPlan, extra_findings,
                           skill_dir: str, fix_index: dict) -> None:
    if not extra_findings:
        return
    by_item_key = {
        key: item for item in plan.items
        if (key := _locator_rule_key(item.locator, item.rule_id)) is not None}
    added = 0
    for finding in strict_iterable_list(extra_findings):
        if not isinstance(finding, dict):
            continue
        item = make_treatment_item(finding, fix_index, skill_dir)
        item_key = _locator_rule_key(item.locator, item.rule_id)
        existing = by_item_key.get(item_key) if item_key is not None else None
        if existing is not None:
            _merge_extra_finding_fields(existing, item)
            continue
        plan.items.append(item)
        if item_key is not None:
            by_item_key[item_key] = item
        added += 1
    if added:
        logger.info('[PlanGen] 扇出扩族并入 %d 个治疗项', added)
def generate_treatment_plan(diagnosis_report: dict, fix_route_report: dict | None=None,
                            skill_dir: str=_DEFAULT_SKILL_DIR,
                            extra_findings: list[dict] | None=None) -> TreatmentPlan:
    generator = TreatmentPlanGenerator(skill_dir)
    plan = generator.generate(diagnosis_report, fix_route_report,
                              extra_findings=extra_findings)
    logger.info('[TreatmentPlan] 生成完成: %s', plan.summary)
    return plan
_SEMANTIC_NAME_MAP: dict[str, str] = {
    'broad_exception': 'exception_handling', 'bare_except': 'exception_handling',
    'empty_except': 'exception_handling', 'silent_swallow': 'exception_handling',
    'high_complexity': 'complexity', 'too_many_params': 'complexity', 'deep_nesting': 'complexity',
    'unused_import': 'unused_import',
    'dead_code': 'dead_code', 'orphan_function': 'dead_code', 'orphan_module': 'dead_code',
    'unreachable_code': 'dead_code', 'unused_definition': 'dead_code',
    'hardcoded_credential': 'security', 'hardcoded_secret': 'security',
    'insecure_deserialization': 'security', 'xss': 'security',
    'ssti': 'security', 'ldap_injection': 'security',
    'sql_injection': 'security', 'path_traversal': 'security', 'command_injection': 'security',
    'insecure_random': 'security', 'insecure_config': 'security',
    'xxe': 'security', 'ssrf': 'security', 'csrf': 'security', 'weak_crypto': 'security',
    'unsafe_eval': 'security', 'danger_pattern': 'security',
    'connection_leak': 'resource', 'file_leak': 'resource', 'handle_leak': 'resource',
    'mutable_default': 'bug_risk', 'mutable_global': 'bug_risk', 'global_statement': 'bug_risk',
    'circular_dep': 'architecture', 'circular_dependency': 'architecture', 'import_cycle': 'architecture',
    'excessive_coupling': 'architecture', 'god_module': 'architecture',
    'srp_violation': 'architecture', 'naming_cluster': 'architecture',
    'fat_interface': 'architecture', 'ocp_violation': 'architecture',
    'broken_call': 'architecture', 'missing_import': 'architecture',
    'unbounded_recursion': 'bug_risk', 'recursion': 'bug_risk',
    'api_change': 'api_compat', 'api_issue': 'api_compat', 'breaking_change': 'api_compat', 'compatibility': 'api_compat',
    'config_drift': 'config', 'missing_config': 'config',
    'test_smell': 'testing', 'test_failure': 'testing', 'test_error': 'testing',
    'low_mutation_score': 'testing', 'low_coverage': 'testing', 'undertested': 'testing',
    'missing_docstring': 'docs', 'missing_annotations': 'docs',
}
_SECURITY_RULE_SUBSTRINGS: frozenset[str] = frozenset({
    'sql_injection', 'path_traversal', RULE_HARDCODED_CREDENTIAL,
    'danger_pattern', 'se-04', 'se-06', 'se-20'})
_SECURITY_RULE_IDS: set[str] = {
    'SE-01','SE-02','SE-03','SE-04','SE-05','SE-06','SE-07','SE-08','SE-09','SE-10',
    'SE-11','SE-12','SE-13','SE-14','SE-15','SE-16','SE-17','SE-18','SE-19','SE-20',
    'SC-01','SC-02','SC-03','SC-04','SC-05','SC-06','SC-07','SC-08',
    'SC-09','SC-10','SC-11',
    'SS-01','SS-02','SS-03',
    'SEC-01','SEC-02','SEC-03','SEC-04','SEC-05',
    'SR-01','SR-02','SR-03','SR-04','SR-05',
    'PT-01',
}
_RULE_PREFIX_TO_CATEGORY: dict[str, str] = dict(RULE_ID_PREFIX_CATEGORY)
_RULE_PREFIXES_BY_LENGTH = tuple(sorted(
    _RULE_PREFIX_TO_CATEGORY, key=len, reverse=True))
_FIX_DEPENDENCIES: dict[str, list[str]] = {
    'syntax_error': [],
    'unused_import': ['syntax_error'],
    'exception_handling': ['syntax_error'],
    'complexity': ['syntax_error'],
    'dead_code': ['syntax_error', 'unused_import'],
    'resource': ['syntax_error'],
    'bug_risk': ['syntax_error'],
    'architecture': ['syntax_error', 'unused_import'],
    'security': ['syntax_error', 'unused_import', 'exception_handling'],
    'api_compat': ['syntax_error', 'unused_import'],
    'config': ['syntax_error'],
    'testing': ['syntax_error'],
    'docs': ['syntax_error'],
}
def _resolve_rule_category(rule_id: str) -> str:
    if not rule_id:
        return ''
    rid = rule_id.strip()
    rid_lower = rid.lower()
    if rid_lower in _SEMANTIC_NAME_MAP:
        return _SEMANTIC_NAME_MAP[rid_lower]
    if rid in _SECURITY_RULE_IDS:
        return 'security'
    upper = rid.upper()
    for prefix in _RULE_PREFIXES_BY_LENGTH:
        if not upper.startswith(prefix):
            continue
        suffix = upper[len(prefix):]
        if suffix.startswith(('-', '_')) or suffix.isdigit():
            return _RULE_PREFIX_TO_CATEGORY[prefix]
    return ''
def _suffix_cohort_category(rule_id: str) -> str:
    rid = rule_id.strip().lower()
    if not rid:
        return ''
    for _cat in _FIX_DEPENDENCIES:
        if rid == _cat or rid.endswith('_' + _cat):
            return _cat
    return ''
def plan_items_of(plan: dict) -> list:
    if not isinstance(plan, dict):
        return []
    if "items" in plan:
        return strict_iterable_list(plan.get("items"))
    return strict_iterable_list(plan.get("treatment_items"))
def set_plan_items(plan: dict, items: list) -> None:
    plan["items"] = items
    if "treatment_items" in plan:
        plan["treatment_items"] = items
def _plan_to_dict(plan) -> dict:
    if isinstance(plan, dict):
        cloned = dict(plan)
        set_plan_items(cloned, [
            dict(item) if isinstance(item, dict) else item
            for item in plan_items_of(cloned)])
        return cloned
    to_dict = getattr(plan, 'to_dict', None)
    if not callable(to_dict):
        logger.warning('[Stage3b] 治疗方案形态不支持(%s)，按空计划处理',
                       type(plan).__name__)
        return {}
    try:
        data = to_dict()
    except Exception as err:
        logger.warning('[Stage3b] 治疗方案序列化失败(%s): %s',
                       type(plan).__name__, err)
        return {}
    if isinstance(data, dict):
        return data
    logger.warning('[Stage3b] 治疗方案序列化返回非 dict(%s)，按空计划处理',
                   type(data).__name__)
    return {}
def _safety_override_of(item: dict, safety_overrides: dict) -> dict | None:
    rid = as_str(item.get("rule_id", ""))
    fixer_type = as_str(item.get("fixer_type", ""))
    for key in (rid, fixer_type):
        if key not in safety_overrides:
            continue
        override_info = safety_overrides[key]
        if (isinstance(override_info, dict)
                and "auto_safe" in override_info
                and not signal_bool(override_info.get("auto_safe"))):
            return override_info
    return None
def _sync_strategy_projection_after_override(plan_dict: dict) -> None:
    if 'by_strategy' not in plan_dict:
        return
    items = list(iter_plan_items(plan_dict))
    by_strategy: dict[str, int] = defaultdict(int)
    for item in items:
        strategy = str_or_empty(item.get('strategy')) or _DEFAULT_STRATEGY
        by_strategy[strategy] += 1
    plan_dict['by_strategy'] = dict(by_strategy)
    summary = plan_dict.get('summary')
    if not isinstance(summary, str) or '策略分布:' not in summary:
        return
    total_items = as_count(plan_dict.get('total_items'))
    if total_items <= 0:
        total_items = len(items)
    plan_dict['summary'] = _PlanSummarizer.text(TreatmentPlan(
        total_items=total_items,
        by_priority=dict_or_empty(plan_dict.get('by_priority')),
        by_strategy=by_strategy,
    ))
def apply_safety_overrides(plan_dict: dict, adjustments: dict) -> int:
    safety_overrides = (adjustments.get("fixer_safety_overrides", {})
                        if isinstance(adjustments, dict) else {})
    if not isinstance(safety_overrides, dict) or not safety_overrides:
        return 0
    override_count = 0
    for item in plan_items_of(plan_dict):
        if not isinstance(item, dict) or not signal_bool(
                item.get("auto_safe", False)):
            continue
        override_info = _safety_override_of(item, safety_overrides)
        if override_info is None:
            continue
        item["auto_safe"] = False
        if item.get('strategy') == _AUTO_SAFE_STRATEGY:
            item['strategy'] = _DEFAULT_STRATEGY
        item["_safety_overridden"] = True
        item["_safety_override_reason"] = override_info.get(
            "reason", "反馈系统标记为不安全")
        override_count += 1
    if override_count:
        _sync_strategy_projection_after_override(plan_dict)
        logger.info("[Stage3b] fixer_safety_overrides 应用: %d项 auto_safe→False",
                    override_count)
    return override_count
def attach_fix_coverage(plan_dict: dict, fix_report: dict) -> None:
    plan_dict = plan_dict_or_empty(plan_dict, "plan 键")
    fix_coverage = (fix_report.get("fix_coverage")
                    if isinstance(fix_report, dict) else None)
    if isinstance(fix_coverage, dict) and fix_coverage:
        plan_dict["fix_coverage"] = fix_coverage
_PLAN_PREVIEW_KEYS = ("rule_id", "severity", "strategy",
                      "file_path", "line", "sample_message", "locator")
def plan_dict_or_empty(raw, label: str) -> dict:
    if raw is not None and not isinstance(raw, dict):
        logger.warning("[TreatmentPlanStep] %s 非 dict 脏形态(%s)，归一空 dict",
                       label, type(raw).__name__)
    return dict_or_empty(raw)
def norm_plan_dict_key(plan_dict: dict, key: str) -> dict:
    plan_dict = plan_dict_or_empty(plan_dict, "plan 键")
    return plan_dict_or_empty(plan_dict.get(key), f"{key} 键")
def iter_plan_items(plan_dict: dict):
    for item in plan_items_of(plan_dict):
        if isinstance(item, dict):
            yield item
def execution_order_index(execution_order) -> dict[str, int]:
    order_index: dict[str, int] = {}
    for _i, _loc in enumerate(strict_iterable_list(execution_order)):
        if isinstance(_loc, str) and _loc:
            order_index.setdefault(_loc, _i)
    return order_index
def order_items_by_execution(items: list, execution_order) -> list:
    order_index = execution_order_index(execution_order)
    items = strict_iterable_list(items)
    if not items or not order_index:
        return items
    _tail = len(order_index)
    def _key(it):
        _loc = it.get("locator") if isinstance(it, dict) else None
        return order_index.get(_loc, _tail) if isinstance(_loc, str) else _tail
    return sorted(items, key=_key)
def plan_item_preview(index: int, item: dict) -> dict:
    item = dict_or_empty(item)
    preview = {"index": index}
    preview.update({key: item.get(key, "") for key in _PLAN_PREVIEW_KEYS})
    return preview
def auto_safe_split(plan_dict: dict, by_strategy: dict) -> tuple[int, int]:
    items = list(iter_plan_items(plan_dict))
    if items:
        auto_safe = sum(1 for item in items
                        if signal_bool(item.get("auto_safe", False)))
        return auto_safe, len(items) - auto_safe
    stats = dict_or_empty(by_strategy)
    return (as_count(stats.get(_AUTO_SAFE_STRATEGY)),
            as_count(stats.get(_DEFAULT_STRATEGY)))
def augment_plan_step_out(out: dict, plan_result: dict,
                           plan_dict: dict, by_strategy: dict) -> None:
    plan_result = plan_dict_or_empty(plan_result, "plan_result")
    plan_dict = plan_dict_or_empty(plan_dict, "plan 键")
    by_strategy = dict_or_empty(by_strategy)
    if by_strategy:
        out["by_strategy"] = dict(by_strategy)
    _by_priority = norm_plan_dict_key(plan_dict, "by_priority")
    if _by_priority:
        out["by_priority"] = dict(_by_priority)
    _ses = plan_result.get(FIELD_SIDE_EFFECT_SUMMARY)
    if isinstance(_ses, dict) and _ses:
        out["side_effect_summary"] = _ses
    _items = plan_items_of(plan_dict)
    if _items:
        _ordered = order_items_by_execution(
            _items, plan_dict.get("execution_order"))
        out["treatment_items_preview"] = [
            plan_item_preview(_i, _it) for _i, _it in enumerate(_ordered)]
        out["treatment_items_total"] = len(_ordered)
def plan_step_extras(plan_result: dict, plan_dict: dict) -> dict:
    by_strategy = norm_plan_dict_key(plan_dict, "by_strategy")
    auto_safe_count, manual_confirm_count = auto_safe_split(
        plan_dict, by_strategy)
    extras: dict = {
        "auto_safe_count": auto_safe_count,
        "manual_confirm_count": manual_confirm_count,
    }
    augment_plan_step_out(extras, plan_result, plan_dict, by_strategy)
    return extras
def project_plan_stage_result(result: dict, plan_dict: dict) -> None:
    plan_dict = plan_dict_or_empty(plan_dict, "plan 键")
    _total_items = as_count(plan_dict.get("total_items"))
    if _total_items <= 0:
        _total_items = len(plan_items_of(plan_dict))
    result["total_items"] = _total_items
    result["by_priority"] = norm_plan_dict_key(plan_dict, "by_priority")
    result["by_strategy"] = norm_plan_dict_key(plan_dict, "by_strategy")
    result[FIELD_SIDE_EFFECT_SUMMARY] = norm_plan_dict_key(
        plan_dict, FIELD_SIDE_EFFECT_SUMMARY)
def log_plan_generated(result: dict) -> None:
    result = dict_or_empty(result)
    side_effect = result.get(FIELD_SIDE_EFFECT_SUMMARY)
    logger.info("[Stage3b] 治疗方案生成: %d 项, 副作用汇总: %s (耗时 %.1fs)",
                as_count(result.get("total_items")),
                (side_effect.get("assessment", "N/A")
                 if isinstance(side_effect, dict) else "N/A"),
                safe_float(result.get("elapsed_s")))
def _enhanced_plan_item(item, fixer_rates: dict) -> dict:
    if not isinstance(item, dict):
        return item
    rule_id = normalize_rule_id(item.get("rule_id")) or ""
    enh = fixer_rates.get(rule_id) if rule_id else None
    item_copy = dict(item)
    if not enh:
        item_copy["_memory_enhanced"] = False
        return item_copy
    item_copy["_memory_enhanced"] = True
    item_copy["_preferred_fixer"] = enh.preferred_fixer
    item_copy["_skip_fixers"] = enh.skip_fixers
    item_copy["_historical_success_rate"] = enh.success_rate
    item_copy["_historical_attempts"] = enh.total_attempts
    if enh.success_rate >= 0.8 and item.get("priority") in ("P2", "P3"):
        item_copy["_priority_boost"] = True
    return item_copy
def _count_items(items: list, predicate) -> int:
    return sum(1 for item in items
               if isinstance(item, dict) and predicate(item))
def _rule_ids_of(items: list) -> list[str]:
    rule_ids: list[str] = []
    for i in items:
        if not isinstance(i, dict):
            continue
        rid = normalize_rule_id(i.get("rule_id")) or ""
        if rid:
            rule_ids.append(rid)
    return rule_ids
def _fix_pattern_item(item, suggestions: dict, avoidance: dict) -> dict:
    if not isinstance(item, dict):
        return item
    item_copy = dict(item)
    rid = normalize_rule_id(item_copy.get("rule_id")) or ""
    if rid and rid in suggestions:
        sug = suggestions[rid]
        item_copy["_fix_pattern_suggestion"] = sug.get("suggested_fixer")
        item_copy["_fix_pattern_confidence"] = sug.get("confidence")
    if rid and rid in avoidance:
        item_copy["_avoid_fixers"] = avoidance[rid]
    return item_copy
def enhance_treatment_plan(
    plan: dict,
    ctx: Any,
) -> dict:
    if not ctx:
        return plan
    try:
        if not ctx.historical_fix_rates:
            return plan
        fixer_rates = get_fixer_success_rates(ctx)
        enhanced = dict(plan)
        items = plan_items_of(enhanced)
        enhanced_items = [_enhanced_plan_item(item, fixer_rates)
                          for item in items]
        set_plan_items(enhanced, enhanced_items)
    except Exception as e:
        logger.warning("[MemoryBridge] 治疗方案记忆增强异常: %s", e)
        return plan
    enhanced["_memory_enhanced"] = True
    enhanced["_memory_enhanced_count"] = _count_items(
        enhanced_items, lambda i: bool(i.get("_memory_enhanced")))
    logger.info("[MemoryBridge] 治疗方案增强: %d/%d项有历史数据",
                enhanced["_memory_enhanced_count"], len(enhanced_items))
    return enhanced
def enhance_treatment_with_fix_patterns(
    plan: dict,
    ctx: Any,
) -> dict:
    if not ctx:
        return plan
    try:
        items = plan_items_of(plan)
        fixer_rates = get_fixer_success_rates(ctx)
        suggestions = get_fix_pattern_suggestions(
            ctx, _rule_ids_of(items), fixer_rates=fixer_rates)
        avoidance = get_failed_fix_avoidance(ctx, fixer_rates=fixer_rates)
        enhanced = dict(plan)
        enhanced_items = [_fix_pattern_item(item, suggestions, avoidance)
                          for item in items]
        set_plan_items(enhanced, enhanced_items)
    except Exception as e:
        logger.warning("[MemoryBridge] 治疗修复模式增强异常: %s", e)
        return plan
    enhanced["_memory_fix_pattern_enhanced"] = _count_items(
        enhanced_items, lambda i: "_fix_pattern_suggestion" in i)
    enhanced["_memory_failed_fixer_marked"] = _count_items(
        enhanced_items, lambda i: "_avoid_fixers" in i)
    return enhanced
def _mark_success_rate_marks(item: dict, fix_rates: dict) -> bool:
    rid = normalize_rule_id(item.get("rule_id")) or ""
    if rid not in fix_rates:
        return False
    rate_info = fix_rates[rid]
    success_rate = safe_float(getattr(rate_info, 'success_rate', 0))
    item["_historical_success_rate"] = round(success_rate, 3)
    if success_rate >= 0.8:
        item["_priority_boost"] = True
        return True
    if success_rate < 0.3:
        item["_low_success_flag"] = True
    return False
def _apply_fixer_success_rates(ctx: Any, plan_dict: dict) -> None:
    try:
        fix_rates = get_fixer_success_rates(ctx.memory_context)
        if fix_rates:
            high_priority_count = sum(
                1 for item in iter_plan_items(plan_dict)
                if _mark_success_rate_marks(item, fix_rates))
            if high_priority_count:
                logger.info("[Stage3b] 修复器成功率: %d项高优先级(>=80%%)", high_priority_count)
    except Exception as err:
        logger.warning("[Stage3b] 修复器成功率跳过: %s", err)
def _attach_fix_strategy(item: dict, mem_ctx) -> bool:
    rid = normalize_rule_id(item.get("rule_id")) or ""
    if not rid:
        return False
    finding = {"rule_id": rid, "severity": item.get("severity", "")}
    strategy = recommend_fix_strategy(finding, mem_ctx)
    if not (strategy.get("recommended_fixer") or strategy.get("avoid_fixers")):
        return False
    item["_fix_strategy"] = strategy
    return True
def _apply_fix_strategy_recommendations(ctx: Any, plan_dict: dict) -> None:
    try:
        strategy_count = sum(
            1 for item in iter_plan_items(plan_dict)
            if _attach_fix_strategy(item, ctx.memory_context))
        if strategy_count:
            logger.info("[Stage3b] 修复策略推荐: %d项有策略建议", strategy_count)
    except Exception as err:
        logger.warning("[Stage3b] 修复策略推荐跳过: %s", err)
def _memory_enhanced_plan(plan, mem_ctx) -> dict:
    plan_dict = _plan_to_dict(plan)
    if not plan_dict and not isinstance(plan, dict):
        raise ValueError('治疗方案序列化失败：未生成有效 dict，拒绝按空计划继续')
    if not mem_ctx:
        return plan_dict
    try:
        enhanced_plan = enhance_treatment_plan(plan_dict, mem_ctx)
        if not isinstance(enhanced_plan, dict):
            logger.warning("[Stage3b] 治疗方案记忆增强返回非 dict（%s），保留原计划",
                           type(enhanced_plan).__name__)
            return plan_dict
        logger.info("[Stage3b] 记忆增强治疗方案: %d项有历史数据",
                    enhanced_plan.get('_memory_enhanced_count', 0))
        return enhanced_plan
    except Exception as mem_err:
        logger.warning("[Stage3b] 治疗方案记忆增强失败(不阻断): %s", mem_err)
        return plan_dict
def _fix_pattern_enhanced_plan(plan_dict: dict, mem_ctx) -> dict:
    if not mem_ctx:
        return plan_dict
    try:
        enhanced = enhance_treatment_with_fix_patterns(plan_dict, mem_ctx)
    except Exception as treat_mem_err:
        logger.warning("[Stage3b] 治疗记忆增强跳过: %s", treat_mem_err)
        return plan_dict
    if not isinstance(enhanced, dict):
        logger.warning("[Stage3b] 治疗记忆增强返回非 dict（%s），原样返回",
                       type(enhanced).__name__)
        return plan_dict
    fix_enhanced = enhanced.get("_memory_fix_pattern_enhanced", 0)
    fix_avoided = enhanced.get("_memory_failed_fixer_marked", 0)
    if fix_enhanced or fix_avoided:
        logger.info("[Stage3b] 记忆增强治疗: 修复模式=%d, 失败规避=%d",
                    fix_enhanced, fix_avoided)
    return enhanced
def _soft_apply_chain(action, label: str, ctx: Any,
                      plan_dict: dict) -> None:
    try:
        action(ctx, plan_dict)
    except Exception as err:
        logger.warning("[Stage3b] %s跳过: %s", label, err)
def enhance_plan_with_memory(ctx: Any, plan) -> dict:
    _mem_ctx = getattr(ctx, 'memory_context', None)
    plan_dict = _memory_enhanced_plan(plan, _mem_ctx)
    plan_dict = _fix_pattern_enhanced_plan(plan_dict, _mem_ctx)
    if _mem_ctx:
        _soft_apply_chain(_apply_fixer_success_rates, "修复器成功率",
                          ctx, plan_dict)
        _soft_apply_chain(_apply_fix_strategy_recommendations, "修复策略推荐",
                          ctx, plan_dict)
    return plan_dict
def reset_artifacts_after_plan(sd: str, plan_result: dict,
                                 plan_dict: dict) -> None:
    plan_result = dict_or_empty(plan_result)
    plan_dict = dict_or_empty(plan_dict)
    status = plan_result.get("status")
    if status != "completed":
        logger.warning(
            "[TreatmentPlanStep] 方案生成未完成(status=%s)，保留既有治疗状态与修复方案清单",
            status)
        return
    if not plan_dict:
        logger.warning(
            "[TreatmentPlanStep] 方案载荷为空，拒绝重置既有治疗状态与修复方案清单")
        return
    items_key = ("items" if "items" in plan_dict else
                 "treatment_items" if "treatment_items" in plan_dict else "")
    if not items_key:
        logger.warning(
            "[TreatmentPlanStep] 方案缺少治疗明细键，拒绝按空计划重置既有产物")
        return
    raw_items = plan_dict.get(items_key)
    if (isinstance(raw_items, (str, bytes, bytearray, dict))
            or not hasattr(raw_items, "__iter__")):
        logger.warning(
            "[TreatmentPlanStep] 治疗明细形态非法(%s)，拒绝重置既有产物",
            type(raw_items).__name__)
        return
    items = plan_items_of(plan_dict)
    if any(not isinstance(item, dict) for item in items):
        logger.warning(
            "[TreatmentPlanStep] 治疗明细包含非映射条目，拒绝重置既有产物")
        return
    if "total_items" in plan_dict:
        declared_total = count_tasks(
            plan_dict.get("total_items"), clamp_negative=False)
        if declared_total is None or declared_total != len(items):
            logger.warning(
                "[TreatmentPlanStep] 治疗明细数与声明总数不一致(declared=%r, "
                "actual=%d)，拒绝重置既有产物",
                plan_dict.get("total_items"), len(items))
            return
    ordered_items = order_items_by_execution(
        items, plan_dict.get("execution_order"))
    reset_treatment_artifacts(
        sd, ordered_items, plan_dict.get("fix_coverage"))

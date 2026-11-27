from __future__ import annotations

import json
from collections.abc import Callable, Sequence
from dataclasses import asdict
from typing import Any

from jwsgj.diag_types_normalize import (
    as_list,
    dict_or_empty,
    finding_file_key,
    int_or,
    round_anchor_matches,
    signal_bool,
    str_or,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    FANOUT_DEPENDENCY_THRESHOLD,
    FANOUT_GOVERNANCE_RULE,
    FANOUT_LEVEL_EXCLUDED,
    FANOUT_LEVEL_L1,
    FANOUT_LEVEL_L2,
    FANOUT_LEVEL_L3,
    FANOUT_LEVEL_L4,
    FANOUT_LEVEL_UNKNOWN,
    FANOUT_LEVELS,
    FANOUT_ROLE_EXCLUDED,
    FANOUT_ROLE_MODULE,
    FANOUT_THRESHOLD_PROFILE,
    FANOUT_TIER_EXCLUDED,
    fanout_advisory_scope_text,
    fanout_degree_of,
    fanout_level_is_mandatory,
    fanout_level_label,
    fanout_mandatory_scope_text,
    resolve_fanout_degree,
    resolve_fanout_governance_level,
)
from jwsgj.diag_zero_backlog_gate import fanout_residual_gate
from jwsgj.fanout_report import (
    _KNOWN_LINE_TOLERANCE,
    FANOUT_REPORT_SCHEMA,
    FANOUT_STAGE_ID,
    FANOUT_STAGE_LABEL,
    FanoutConfig,
    FanoutReport,
    _attach_module_governance,
    _existing_index,
    _family_payload,
    _family_signature_payloads,
    _governance_tier_of,
    _has_existing,
    _is_treatable_occurrence,
    _module_degrees,
    _orchestrator_roster,
    _read_report_payload,
    _refresh_report_summary,
    _role_label,
    build_fanout_report,
    fanout_module_counts,
    fanout_treatment_handoff,
    load_fanout_report,
    save_fanout_report,
    scan_signatures,
    summarize_fanout_report,
    summarize_fanout_strategies,
)
from jwsgj.fix_guide_rule_identity import (
    FanoutOccurrence,
    FanoutSignature,
    signature_from_dict,
)
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.runtime_paths import first_json_artifact
from jwsgj.runtime_scope import normalize_skill_dir

logger = get_module_logger(__name__)
__all__ = [
    'FANOUT_GATE_BLOCKED_STAGE',
    'FANOUT_GATE_ENFORCEMENT',
    'FANOUT_GATE_PHASE_BASELINE',
    'FANOUT_GATE_PHASE_PRE_TREATMENT',
    'emit_fanout_html',
    'emit_fanout_report',
    'fanout_evolution_signal',
    'fanout_pre_treatment_block',
    'fanout_pre_treatment_gate',
    'rebuild_report_after_fix',
    'run_fanout_diagnosis',
    'verify_fanout_residual',
]
FANOUT_GATE_PHASE_BASELINE = 'diagnosis_baseline'
FANOUT_GATE_PHASE_PRE_TREATMENT = 'pre_treatment'
FANOUT_GATE_ENFORCEMENT = 'blocking'
FANOUT_GATE_BLOCKED_STAGE = 'treatment'
_EVOLUTION_LEVEL_RANK = {
    FANOUT_LEVEL_L4: 0, FANOUT_LEVEL_L3: 1,
    FANOUT_LEVEL_L2: 2, FANOUT_LEVEL_L1: 3,
    FANOUT_LEVEL_UNKNOWN: 4, FANOUT_LEVEL_EXCLUDED: 5,
}
def _evolution_row_level(row: dict) -> str:
    data = dict_or_empty(row)
    if not data:
        return FANOUT_LEVEL_UNKNOWN
    if not str_or(data.get('file')):
        data['file'] = str_or(data.get('module'))
    return resolve_fanout_governance_level(data)
_EVOLUTION_GROUP_BY_LEVEL = {
    FANOUT_LEVEL_L4: 'mandatory',
    FANOUT_LEVEL_L1: 'advisory', FANOUT_LEVEL_L2: 'advisory',
    FANOUT_LEVEL_L3: 'advisory', FANOUT_LEVEL_UNKNOWN: 'unknown',
    FANOUT_LEVEL_EXCLUDED: 'excluded',
}
def _evolution_groups(modules: Sequence[dict]) -> tuple[list[dict], ...]:
    groups = {key: [] for key in (
        'mandatory', 'advisory', 'unknown', 'excluded')}
    for row in modules:
        key = _EVOLUTION_GROUP_BY_LEVEL.get(_evolution_row_level(row))
        if key is not None:
            groups[key].append(row)
    return tuple(groups[key] for key in (
        'mandatory', 'advisory', 'unknown', 'excluded'))
def _evolution_module(row: dict, *, detailed: bool = True) -> dict:
    payload = {'module': str_or(row.get('module'))}
    if detailed:
        payload['governance_level'] = _evolution_row_level(row)
    payload.update({
        'module_role': str_or(row.get('module_role')),
        'module_role_label': str_or(row.get('module_role_label')),
    })
    if detailed:
        payload['dependency_fanout'] = fanout_degree_of(
            row.get('dependency_fanout'))
    payload['treatable'] = int_or(row.get('treatable'))
    return payload
def _evolution_tier_changes(modules: Sequence[dict],
                            prior_summary: dict) -> list[dict]:
    prior_by_key: dict[str, dict] = {}
    for raw in as_list(prior_summary.get('module_counts')):
        row = dict_or_empty(raw)
        key = str_or(row.get('module_key')) or str_or(row.get('module'))
        if key:
            prior_by_key[key] = row
    changes: list[dict] = []
    for row in modules:
        key = str_or(row.get('module_key')) or str_or(row.get('module'))
        prev = prior_by_key.get(key)
        if not prev:
            continue
        before = _evolution_row_level(prev)
        after = _evolution_row_level(row)
        if before == after:
            continue
        changes.append({
            'module': str_or(row.get('module')),
            'module_key': key,
            'from_level': before,
            'to_level': after,
            'from_tier': _governance_tier_of(before),
            'to_tier': _governance_tier_of(after),
            'module_role': str_or(row.get('module_role')),
            'module_role_label': str_or(row.get('module_role_label')),
            'dependency_fanout': fanout_degree_of(
                row.get('dependency_fanout')),
            'prior_dependency_fanout': fanout_degree_of(
                prev.get('dependency_fanout')),
            'treatable': int_or(row.get('treatable')),
        })
    changes.sort(key=lambda item: (
        _EVOLUTION_LEVEL_RANK.get(str_or(item.get('to_level')), 4),
        item.get('module') or ''))
    return changes
def _evolution_convergence(prior: dict | None, tiers: dict,
                           prior_tiers: dict) -> dict:
    current_levels = dict_or_empty(tiers.get('level_modules'))
    prior_levels = dict_or_empty(prior_tiers.get('level_modules'))
    current_sites = dict_or_empty(tiers.get('level_sites'))
    prior_sites = dict_or_empty(prior_tiers.get('level_sites'))
    convergence = {
        'prior_round_start_ts': str_or(dict_or_empty(prior).get(
            'round_start_ts')),
        'level_modules': current_levels,
        'level_sites': current_sites,
        'prior_level_modules': prior_levels,
        'prior_level_sites': prior_sites,
        'delta_level_modules': {
            level: (int_or(current_levels.get(level))
                    - int_or(prior_levels.get(level)))
            for level in FANOUT_LEVELS
        },
        'delta_level_sites': {
            level: (int_or(current_sites.get(level))
                    - int_or(prior_sites.get(level)))
            for level in FANOUT_LEVELS
        },
    }
    for prefix in ('mandatory', 'advisory', 'excluded'):
        for suffix in ('modules', 'sites'):
            key = f'{prefix}_{suffix}'
            convergence[key] = int_or(tiers.get(key))
    for key in ('mandatory_modules', 'mandatory_sites',
                'advisory_modules', 'advisory_sites'):
        prior_value = int_or(prior_tiers.get(key))
        convergence[f'prior_{key}'] = prior_value
        convergence[f'delta_{key}'] = convergence[key] - prior_value
    return convergence
def _surface_signals(mandatory: list[dict], advisory: list[dict],
                     unknown: list[dict], enforced: int,
                     total_sites: int) -> list[str]:
    signals: list[str] = []
    if unknown:
        signals.append(
            f"module_fanout_unmeasured: {len(unknown)} 个模块未能映射到依赖图"
            "（路径不在目标根内或依赖图扫描失败）——按 unknown 档留痕，"
            "不阻断治疗，需人工确认模块归属")
    if total_sites and enforced / total_sites > 0.5:
        signals.append(
            f"mandatory_surface: 强制治理位点占 {enforced}/{total_sites}"
            f"（{enforced / total_sites:.0%}），优先治理高扇出模块")
    if advisory and not mandatory and not unknown:
        signals.append(
            f"advisory_only: 本轮 {len(advisory)} 个模块均为建议性治理"
            "——逐模块补齐 pros/cons/net_benefit 后再决定治理或留痕")
    return signals
def _change_signals(tier_changes: list[dict], convergence: dict) -> list[str]:
    signals: list[str] = []
    escalations = [item for item in tier_changes
                   if item['to_level'] == FANOUT_LEVEL_L4
                   and item['from_level'] != FANOUT_LEVEL_L4]
    relaxations = [item for item in tier_changes
                   if item['from_level'] == FANOUT_LEVEL_L4
                   and item['to_level'] != FANOUT_LEVEL_L4]
    if escalations:
        sample = '、'.join(item['module'] for item in escalations[:3])
        signals.append(
            f"module_tier_escalation: {len(escalations)} 个模块升为 L4 危机"
            f"（强制治理）（{sample}）——复核新增导入与同族位点")
    if relaxations:
        sample = '、'.join(item['module'] for item in relaxations[:3])
        signals.append(
            f"module_tier_relaxation: {len(relaxations)} 个模块从 L4 危机降档"
            f"（{sample}）——利弊分析仍须逐模块留痕")
    delta = int_or(convergence.get('delta_mandatory_sites'))
    if delta > 0:
        signals.append(
            f'mandatory_growth: 强制治理位点较上一轮增加 {delta} 处，'
            '复核新增同族位点')
    elif delta < 0:
        signals.append(
            f'mandatory_convergence: 强制治理位点较上一轮减少 {abs(delta)} 处，'
            '治理收敛')
    return signals
def _excluded_module_rows(report: dict) -> list[dict]:
    section = dict_or_empty(dict_or_empty(report).get('module_fanout'))
    rows: list[dict] = []
    for raw_name in as_list(dict_or_empty(section.get('excluded')).get(
            'modules')):
        name = str_or(raw_name)
        if not name:
            continue
        rows.append({
            'module': name,
            'module_key': name,
            'module_role': FANOUT_ROLE_EXCLUDED,
            'module_role_label': _role_label(FANOUT_ROLE_EXCLUDED),
            'governance_level': FANOUT_LEVEL_EXCLUDED,
            'governance_tier': FANOUT_TIER_EXCLUDED,
            'dependency_fanout': None,
            'treatable': 0,
        })
    return rows
def _evolution_payload(report: dict, prior: dict | None) -> dict:
    summary = dict_or_empty(dict_or_empty(report).get('summary'))
    tiers = dict_or_empty(summary.get('governance_tiers'))
    modules = [row for row in (
        dict_or_empty(raw) for raw in as_list(summary.get('module_counts')))
        if row]
    mandatory, advisory, unknown, excluded = _evolution_groups(
        [*modules, *_excluded_module_rows(report)])
    total_sites = sum(int_or(row.get('treatable')) for row in modules)
    enforced = sum(int_or(row.get('treatable')) for row in mandatory)
    prior_summary = dict_or_empty(dict_or_empty(prior).get('summary'))
    prior_tiers = dict_or_empty(prior_summary.get('governance_tiers'))
    tier_changes = _evolution_tier_changes(modules, prior_summary)
    convergence = (_evolution_convergence(prior, tiers, prior_tiers)
                   if prior_tiers else {})
    signals = _surface_signals(
        mandatory, advisory, unknown, enforced, total_sites)
    signals.extend(_change_signals(tier_changes, convergence))
    return {
        'round_start_ts': str_or(dict_or_empty(report).get('round_start_ts')),
        'threshold': FANOUT_DEPENDENCY_THRESHOLD,
        'thresholds': dict(FANOUT_THRESHOLD_PROFILE),
        'rule': FANOUT_GOVERNANCE_RULE,
        'tiers': dict(tiers),
        'levels': dict_or_empty(tiers.get('levels')),
        'level_modules': dict_or_empty(tiers.get('level_modules')),
        'level_sites': dict_or_empty(tiers.get('level_sites')),
        'mandatory_modules': [
            _evolution_module(row) for row in mandatory],
        'advisory_modules': [
            _evolution_module(row) for row in advisory],
        'excluded_modules': [
            _evolution_module(row, detailed=False) for row in excluded],
        'excluded': dict_or_empty(dict_or_empty(
            dict_or_empty(report).get('module_fanout')).get('excluded')),
        'strategy_distribution': dict_or_empty(summary.get('strategies')),
        'tier_changes': tier_changes,
        'prior_round': convergence,
        'signals': signals,
    }
def _fanout_baseline_gate(skill_dir: str, report: dict) -> dict:
    try:
        gate = dict(fanout_residual_gate(skill_dir, report))
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context='_fanout_baseline_gate')
        return {
            'passed': False,
            'skipped': False,
            'reason': 'gate_error',
            'error': f'{type(exc).__name__}: {exc}'[:300],
            'phase': FANOUT_GATE_PHASE_BASELINE,
            'enforcement': FANOUT_GATE_ENFORCEMENT,
            'blocked_stage': FANOUT_GATE_BLOCKED_STAGE,
        }
    gate['phase'] = FANOUT_GATE_PHASE_BASELINE
    gate['enforcement'] = FANOUT_GATE_ENFORCEMENT
    gate['blocked_stage'] = FANOUT_GATE_BLOCKED_STAGE
    gate['module_counts'] = fanout_module_counts(report)
    gate['governance_tiers'] = dict_or_empty(
        dict_or_empty(report.get('summary')).get('governance_tiers'))
    gate['note'] = (
        '阶段G诊断基线（分档阻断）：L4 危机'
        f'（{fanout_mandatory_scope_text()}）的强制治理位点必须全部纳入'
        '治疗计划；'
        'L1-L3 先给 pros/cons/net_benefit 利弊分析，再决定治理或'
        '留痕跳过；强制档残留、策略违规或新增模块文件任一命中即阻断')
    return gate
def run_fanout_diagnosis(skill_dir: str, report: dict | None = None, *,
                         config: FanoutConfig | None = None,
                         round_start_ts: str = '',
                         source_report_path: str = '') -> dict:
    sd = normalize_skill_dir(skill_dir)
    source_report = dict_or_empty(report)
    if not source_report:
        return {
            'status': 'skipped',
            'reason': 'cv_report_unavailable',
            'message': '无可用交叉验证报告，扇出诊断跳过',
        }
    try:
        fanout_report = build_fanout_report(
            sd, source_report, config=config,
            round_start_ts=str_or(round_start_ts),
            source_report_path=str_or(source_report_path))
    except (OSError, ValueError, RecursionError, TypeError) as exc:
        log_swallowed(__name__, exc, context='run_fanout_diagnosis:build')
        return {
            'status': 'degraded',
            'reason': f'{type(exc).__name__}: {exc}'[:300],
            'message': '扇出诊断构建失败（降级，不阻断主链）',
        }
    if not fanout_report.summary.get('seeds'):
        return {
            'status': 'skipped',
            'reason': 'no_seed_findings',
            'message': '无达线可治疗种子，扇出诊断跳过',
            'summary': fanout_report.summary,
        }
    if not fanout_report.summary.get('signatures'):
        return {
            'status': 'degraded',
            'reason': 'no_valid_signatures',
            'message': '种子均未生成有效签名，扇出诊断降级且不产空报告',
            'summary': fanout_report.summary,
            'degraded_seeds': list(fanout_report.degraded_seeds),
        }
    prior = load_fanout_report(sd)
    fanout_report.evolution = _evolution_payload(
        fanout_report.to_dict(), prior)
    fanout_report.gate = _fanout_baseline_gate(sd, fanout_report.to_dict())
    path = save_fanout_report(sd, fanout_report)
    logger.info('[FanoutDiag] %s', summarize_fanout_report(
        fanout_report.to_dict()))
    return {
        'status': 'completed',
        'report_path': path,
        'stage_id': FANOUT_STAGE_ID,
        'stage_label': FANOUT_STAGE_LABEL,
        'summary': fanout_report.summary,
        'gate': fanout_report.gate,
        'message': summarize_fanout_report(fanout_report.to_dict()),
    }
def _plan_snapshot(skill_dir: str) -> dict:
    path = first_json_artifact(skill_dir, 'treatment_plan_latest.json')
    if not path:
        return {}
    try:
        with open(path, encoding='utf-8') as handle:
            data = json.load(handle)
    except (OSError, ValueError, RecursionError) as exc:
        log_swallowed(__name__, exc, context='_plan_snapshot')
        return {}
    return data if isinstance(data, dict) else {}
def _family_rule_index(report: dict) -> dict[str, str]:
    index: dict[str, str] = {}
    for raw in as_list(dict_or_empty(report).get('families')):
        family = dict_or_empty(raw)
        family_id = str_or(family.get('family_id'))
        if family_id:
            index[family_id] = str_or(family.get('rule_id'))
    return index
def _uncovered_gate_item(occurrence: dict, rules: dict, index: dict,
                         skill_dir: str) -> dict | None:
    rule_id = (str_or(occurrence.get('rule_id'))
               or rules.get(str_or(occurrence.get('family_id')), ''))
    file_path = str_or(occurrence.get('file'))
    line = int_or(occurrence.get('line'))
    if _has_existing(index, rule_id, file_path, line, skill_dir):
        return None
    level = resolve_fanout_governance_level(occurrence)
    role = str_or(occurrence.get('module_role')) or FANOUT_ROLE_MODULE
    degree = resolve_fanout_degree(occurrence)
    return {
        'rule_id': rule_id,
        'family_id': str_or(occurrence.get('family_id')),
        'file': file_path,
        'line': line,
        'level': str_or(occurrence.get('level')),
        'module_dependency_fanout': degree,
        'module_governance_level': level,
        'module_governance_label': fanout_level_label(level),
        'module_role': role,
        'module_role_label': (str_or(occurrence.get('module_role_label'))
                              or _role_label(role)),
        'module_governance_tier': _governance_tier_of(level),
    }
def _gate_coverage_defaults() -> dict:
    return {
        'total': 0, 'covered': 0, 'uncovered': 0, 'uncovered_items': [],
        'advisory_uncovered': 0, 'advisory_items': [],
        'mandatory_total': 0, 'mandatory_covered': 0,
        'advisory_total': 0, 'advisory_covered': 0, 'excluded_total': 0,
    }
_RESIDUAL_GATE_DEFAULTS: dict = {
    'residual': 0, 'residual_items': [],
    'advisory_residual': 0, 'strategy_violations': [],
    'file_integrity': {}, 'actions_required': [],
}
def _copy_shape(shape: dict) -> dict:
    return {
        key: (list(value) if isinstance(value, list)
              else dict(value) if isinstance(value, dict) else value)
        for key, value in shape.items()
    }
def _is_governed_occurrence(occurrence: dict) -> bool:
    data = dict_or_empty(occurrence)
    return (_is_treatable_occurrence(data)
            and resolve_fanout_governance_level(data) != FANOUT_LEVEL_EXCLUDED)
def _gate_coverage(data: dict, plan_dict: dict, skill_dir: str) -> dict:
    index = _existing_index(plan_dict)
    rules = _family_rule_index(data)
    mandatory_total = 0
    advisory_total = 0
    excluded_total = 0
    uncovered: list[dict] = []
    advisory_items: list[dict] = []
    for raw in as_list(data.get('occurrences')):
        occurrence = dict_or_empty(raw)
        if not _is_treatable_occurrence(occurrence):
            continue
        level = resolve_fanout_governance_level(occurrence)
        if level == FANOUT_LEVEL_EXCLUDED:
            excluded_total += 1
            continue
        mandatory = fanout_level_is_mandatory(level)
        if mandatory:
            mandatory_total += 1
        else:
            advisory_total += 1
        item = _uncovered_gate_item(occurrence, rules, index, skill_dir)
        if item is None:
            continue
        if mandatory:
            uncovered.append(item)
        else:
            advisory_items.append(item)
    total = mandatory_total + advisory_total
    coverage = _gate_coverage_defaults()
    coverage.update({
        'total': total,
        'covered': total - len(uncovered) - len(advisory_items),
        'uncovered': len(uncovered),
        'uncovered_items': uncovered,
        'advisory_uncovered': len(advisory_items),
        'advisory_items': advisory_items,
        'mandatory_total': mandatory_total,
        'mandatory_covered': mandatory_total - len(uncovered),
        'advisory_total': advisory_total,
        'advisory_covered': advisory_total - len(advisory_items),
        'excluded_total': excluded_total,
    })
    return coverage
def _gate_actions(uncovered: list[dict], advisory_items: list[dict],
                  residual: dict) -> list[str]:
    actions: list[str] = []
    if uncovered:
        sample = '、'.join(
            f"{item['file']}:{item['line']}" for item in uncovered[:5])
        actions.append(
            f"fanout_plan_gap: {len(uncovered)} 处 L4 危机位点未纳入治疗计划"
            f"（{sample}）——{fanout_mandatory_scope_text()}，"
            "先补计划再执行治疗")
    if advisory_items:
        sample = '、'.join(
            f"{item['file']}:{item['line']}" for item in advisory_items[:5])
        actions.append(
            f"fanout_advisory: {len(advisory_items)} 处非强制位点"
            f"（L1-L3/unknown）未纳入计划（{sample}）——"
            f"{fanout_advisory_scope_text()}，先做方案对比"
            "（pros/cons/net_benefit）再决定治理或留痕跳过；"
            "unknown 档先确认模块映射；不阻断治疗")
    actions.extend(str_or(action)
                   for action in as_list(residual.get('actions_required')))
    return actions
def _report_payload(skill_dir: str,
                    report: dict | None) -> tuple[dict, bool]:
    if report is None:
        return load_fanout_report(skill_dir), False
    return dict_or_empty(report), True
def fanout_pre_treatment_gate(skill_dir: str, report: dict | None = None,
                              plan: dict | None = None) -> dict:
    sd = normalize_skill_dir(skill_dir)
    data, explicit = _report_payload(sd, report)
    base = {
        'phase': FANOUT_GATE_PHASE_PRE_TREATMENT,
        'enforcement': FANOUT_GATE_ENFORCEMENT,
        'blocked_stage': FANOUT_GATE_BLOCKED_STAGE,
        'benefit_analysis_required': True,
        'governance_threshold': FANOUT_DEPENDENCY_THRESHOLD,
        'governance_thresholds': dict(FANOUT_THRESHOLD_PROFILE),
    }
    try:
        residual = dict(fanout_residual_gate(
            sd, data if explicit else (data or None)))
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context='fanout_pre_treatment_gate')
        error = f'{type(exc).__name__}: {exc}'[:300]
        return {
            **base, **_copy_shape(_GATE_SKIPPED_SHAPE),
            'passed': False, 'skipped': False, 'reason': 'gate_error',
            'error': error,
            'actions_required': [
                f'fanout_gate_error: {error}；门禁证据不可用，阻断治疗'],
        }
    if residual.get('skipped'):
        return _skipped_gate(base, str_or(residual.get('reason'))
                              or 'no_fanout_report', residual)
    if residual.get('gate_error'):
        reason = str_or(residual.get('reason')) or 'gate_error'
        return {
            **base, **_copy_shape(_GATE_SKIPPED_SHAPE),
            'passed': False, 'skipped': False, 'reason': reason,
            'error': str_or(residual.get('gate_error')),
            'actions_required': as_list(residual.get('actions_required')),
        }
    plan_payload = _plan_snapshot(sd) if plan is None else dict_or_empty(plan)
    coverage = _gate_coverage(data, plan_payload, sd)
    uncovered = coverage['uncovered_items']
    advisory_items = coverage['advisory_items']
    actions = _gate_actions(uncovered, advisory_items, residual)
    reasons = [
        reason for reason, hit in (
            ('plan_gap', uncovered),
            ('strategy_violation',
             as_list(residual.get('strategy_violations'))),
            ('split_file',
             not dict_or_empty(residual.get('file_integrity')).get(
                 'passed', True)),
        ) if hit
    ]
    passed = not reasons
    return {
        **base,
        **coverage,
        'passed': passed,
        'skipped': False,
        'reason': '' if passed else '+'.join(reasons),
        'residual': int_or(residual.get('residual')),
        'residual_items': as_list(residual.get('residual_items')),
        'advisory_residual': int_or(residual.get('advisory_residual')),
        'strategy_violations': as_list(residual.get('strategy_violations')),
        'file_integrity': dict_or_empty(residual.get('file_integrity')),
        'actions_required': actions,
        'module_counts': fanout_module_counts(data),
        'note': (
            '治疗前强制阻断：L4 危机'
            f'（{fanout_mandatory_scope_text()}）'
            '位点必须全部纳入治疗计划；L1-L3 由 AI 分析并做方案对比'
            '（pros/cons/net_benefit）后决定治理或留痕；unknown 档先确认'
            '模块映射，同样不阻断；'
            '包根/入口位点按排除面单列、不阻断；'
            '策略违规与新增模块文件恒阻断'),
    }
_GATE_SKIPPED_SHAPE: dict = {
    **_gate_coverage_defaults(),
    **_RESIDUAL_GATE_DEFAULTS,
}
def _skipped_gate(base: dict, reason: str,
                  residual: dict | None = None) -> dict:
    payload = {**base, **_copy_shape(_GATE_SKIPPED_SHAPE), 'passed': True,
               'skipped': True, 'reason': reason}
    for key in ('total', 'residual', 'residual_items', 'advisory_residual',
                'strategy_violations', 'file_integrity'):
        if key in dict_or_empty(residual):
            payload[key] = residual[key]
    if residual and 'actions_required' in residual:
        payload['actions_required'] = as_list(residual.get('actions_required'))
    return payload
def fanout_evolution_signal(skill_dir: str,
                            *, round_start_ts: str = '') -> dict:
    sd = normalize_skill_dir(skill_dir)
    try:
        report = load_fanout_report(sd)
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context='fanout_evolution_signal:load')
        return {}
    summary = dict_or_empty(report.get('summary'))
    tiers = dict_or_empty(summary.get('governance_tiers'))
    if not tiers:
        return {}
    report_round = str_or(report.get('round_start_ts'))
    current_round = str_or(round_start_ts)
    if (not report_round or not current_round
            or not round_anchor_matches(report_round, current_round)):
        logger.info('[FanoutEvolution] 轮次锚不完整或跨轮报告不消费: %s != %s',
                    report_round, current_round)
        return {}
    evolution = dict_or_empty(report.get('evolution'))
    return {
        'status': 'ok',
        'round_start_ts': report_round,
        'threshold': int_or(tiers.get('threshold'),
                            FANOUT_DEPENDENCY_THRESHOLD),
        'thresholds': (dict_or_empty(tiers.get('thresholds'))
                       or dict(FANOUT_THRESHOLD_PROFILE)),
        'levels': dict_or_empty(tiers.get('levels')),
        'level_modules': dict_or_empty(tiers.get('level_modules')),
        'level_sites': dict_or_empty(tiers.get('level_sites')),
        'mandatory_modules': int_or(tiers.get('mandatory_modules')),
        'advisory_modules': int_or(tiers.get('advisory_modules')),
        'unknown_modules': int_or(tiers.get('unknown_modules')),
        'mandatory_sites': int_or(tiers.get('mandatory_sites')),
        'advisory_sites': int_or(tiers.get('advisory_sites')),
        'enforced_sites': int_or(tiers.get('enforced_sites')),
        'strategy_distribution': dict_or_empty(summary.get('strategies')),
        'tier_changes': [row for row in (
            dict_or_empty(item)
            for item in as_list(evolution.get('tier_changes'))) if row],
        'prior_round': dict_or_empty(evolution.get('prior_round')),
        'signals': [str(item) for item in as_list(evolution.get('signals'))
                    if isinstance(item, str)],
        'rule': str_or(evolution.get('rule')) or FANOUT_GOVERNANCE_RULE,
    }
def _signatures_of(report: dict) -> list[FanoutSignature]:
    signatures: list[FanoutSignature] = []
    for raw_family in as_list(dict_or_empty(report).get('families')):
        family = dict_or_empty(raw_family)
        for payload in _family_signature_payloads(family):
            signature = signature_from_dict(payload)
            if signature is not None and not signature.degraded:
                signatures.append(signature)
    return signatures
def _merge_gate_reasons(reason: str, extra: str) -> str:
    parts = [part for part in str_or(reason).split('+') if part]
    if extra not in parts:
        parts.append(extra)
    return '+'.join(parts)
def verify_fanout_residual(skill_dir: str, report: dict | None = None, *,
                            rescan: bool = False,
                            config: FanoutConfig | None = None) -> dict:
    sd = normalize_skill_dir(skill_dir)
    data, explicit = _report_payload(sd, report)
    rescan_summary: dict = {}
    rescan_error = ''
    gate_level: list[dict] = []
    files_failed = 0
    truncated_families: list = []
    if rescan and data:
        if not _signatures_of(data):
            unverifiable = [
                dict_or_empty(item) for item in as_list(data.get('occurrences'))
                if _is_governed_occurrence(item)]
            rescan_summary = {'skipped': True, 'reason': 'no_signature'}
            if unverifiable:
                rescan_summary['unverifiable'] = len(unverifiable)
                rescan_error = (
                    'signature_unavailable: 报告仍含可治疗位点，'
                    '但没有可用于复扫的有效签名')
        else:
            try:
                data = rebuild_report_after_fix(sd, data, config=config)
            except (OSError, ValueError, RecursionError, TypeError) as exc:
                log_swallowed(
                    __name__, exc, context='verify_fanout_residual:scan')
                rescan_error = f'{type(exc).__name__}: {exc}'[:200]
                rescan_summary = {'skipped': True, 'reason': rescan_error}
            else:
                occurrences = [dict_or_empty(item) for item in as_list(
                    data.get('occurrences'))]
                gate_level = [
                    item for item in occurrences
                    if _is_governed_occurrence(item)]
                summary = dict_or_empty(data.get('summary'))
                files_failed = int_or(summary.get('files_failed'))
                truncated_families = as_list(
                    summary.get('truncated_families'))
                rescan_summary = {
                    'skipped': False,
                    'occurrences': len(gate_level),
                    'weak_sites': sum(
                        1 for item in occurrences
                        if str_or(item.get('level')) == 'weak'),
                    'files_scanned': int_or(summary.get('files_scanned')),
                    'files_failed': files_failed,
                    'truncated_families': list(truncated_families),
                }
    try:
        gate = fanout_residual_gate(
            sd, data if explicit else (data or None))
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context='verify_fanout_residual:gate')
        error = f'{type(exc).__name__}: {exc}'[:300]
        gate = {
            'passed': False, 'skipped': False, 'reason': 'gate_error',
            'handled': 0, 'total': 0, 'residual_total': 0,
            'advisory_items': [],
            **_copy_shape(_RESIDUAL_GATE_DEFAULTS),
            'actions_required': [
                f'fanout_gate_error: {error}；门禁证据不可用，阻断验收'],
        }
    result = {
        'passed': bool(gate.get('passed')),
        'residual': int_or(gate.get('residual')),
        'handled': int_or(gate.get('handled')),
        'total': int_or(gate.get('total')),
        'residual_total': int_or(gate.get('residual_total')),
        'residual_items': as_list(gate.get('residual_items')),
        'advisory_residual': int_or(gate.get('advisory_residual')),
        'advisory_items': as_list(gate.get('advisory_items')),
        'actions_required': as_list(gate.get('actions_required')),
        'skipped': bool(gate.get('skipped')),
        'reason': str_or(gate.get('reason')),
        'strategy_violations': as_list(gate.get('strategy_violations')),
        'file_integrity': dict_or_empty(gate.get('file_integrity')),
        'strategies': summarize_fanout_strategies(data),
        'rescan': rescan_summary,
    }
    if rescan_error:
        result['passed'] = False
        result['reason'] = _merge_gate_reasons(
            result['reason'], 'rescan_error')
        result['actions_required'].append(
            f'fanout_rescan_error: 复扫失败（{rescan_error}），阻断残留放行')
        return result
    if not rescan_summary or rescan_summary.get('skipped'):
        return result
    unhandled_mandatory = as_list(gate.get('residual_items'))
    if unhandled_mandatory:
        result['passed'] = False
        result['reason'] = _merge_gate_reasons(
            result['reason'], 'rescan_residual')
        result['rescan']['residual'] = len(unhandled_mandatory)
        result['actions_required'].append(
            f'fanout_rescan: 复扫仍有 {len(unhandled_mandatory)} 处未处理强制位点')
    for reason, hit, action in (
            ('rescan_incomplete', files_failed,
             (f'fanout_rescan_incomplete: {files_failed} 个文件读取/解析失败，'
              '阻断残留放行')),
            ('rescan_truncated', truncated_families,
             'fanout_rescan_truncated: 同族位点达到扫描上限，阻断残留放行')):
        if not hit:
            continue
        result['passed'] = False
        result['reason'] = _merge_gate_reasons(result['reason'], reason)
        result['actions_required'].append(action)
    return result
def _prior_site_index(previous: Sequence[dict],
                     ) -> dict[tuple[str, str], list[tuple[int, dict]]]:
    index: dict[tuple[str, str], list[tuple[int, dict]]] = {}
    for raw in previous:
        record = dict_or_empty(raw)
        family_id = str_or(record.get('family_id'))
        file_key = finding_file_key(record.get('file'))
        line = int_or(record.get('line'))
        if not family_id or not file_key or line <= 0:
            continue
        index.setdefault((family_id, file_key), []).append((line, record))
    return index
def _match_prior_site(index: dict[tuple[str, str], list[tuple[int, dict]]],
                     occurrence: dict, *, exact_only: bool = False
                     ) -> dict | None:
    family_id = str_or(occurrence.get('family_id'))
    file_key = finding_file_key(occurrence.get('file'))
    line = int_or(occurrence.get('line'))
    if not family_id or not file_key or line <= 0:
        return None
    candidates = index.get((family_id, file_key))
    if not candidates:
        return None
    limit = 0 if exact_only else _KNOWN_LINE_TOLERANCE
    best: tuple[int, int, dict] | None = None
    for position, (known_line, record) in enumerate(candidates):
        distance = abs(known_line - line)
        if distance > limit:
            continue
        # 最早可行匹配保留后续位点的候选，避免最近点贪心造成假新增。
        rank = known_line
        if best is None or rank < best[0]:
            best = (rank, position, record)
    if best is None:
        return None
    _rank, position, record = best
    candidates.pop(position)
    return record
def _mark_new_sites(prior_sites: dict[tuple[str, str], list[tuple[int, dict]]],
                    occurrences: Sequence[FanoutOccurrence]) -> list[FanoutOccurrence]:
    new_sites: list[FanoutOccurrence] = []
    ordered = sorted(
        occurrences,
        key=lambda item: (str_or(item.family_id),
                          finding_file_key(item.file), int_or(item.line)),
    )
    for item in ordered:
        prior = _match_prior_site(prior_sites, item.to_dict())
        item.is_new_site = prior is None
        if prior is None:
            new_sites.append(item)
    return new_sites
def rebuild_report_after_fix(skill_dir: str, report: dict | None = None, *,
                             config: FanoutConfig | None = None) -> dict:
    sd = normalize_skill_dir(skill_dir)
    source_report = dict_or_empty(report) or load_fanout_report(sd)
    if not source_report:
        return {}
    data = dict(source_report)
    signatures = _signatures_of(data)
    if not signatures:
        return data
    family_rows = [
        dict_or_empty(raw) for raw in as_list(data.get('families'))
        if dict_or_empty(raw)]
    cfg = FanoutConfig.from_report(data, config)
    scan = scan_signatures(sd, signatures, cfg)
    prior_sites = _prior_site_index([
        dict_or_empty(item)
        for item in as_list(data.get('occurrences'))
        if dict_or_empty(item)])
    _mark_new_sites(prior_sites, scan.occurrences)
    degrees = _module_degrees(sd)
    roster = _orchestrator_roster(sd)
    module_fanout = _attach_module_governance(
        scan.occurrences, sd, file_universe=scan.files,
        degrees=degrees, orchestrator_roster=roster)
    by_family: dict[str, list[FanoutOccurrence]] = {}
    for item in scan.occurrences:
        by_family.setdefault(item.family_id, []).append(item)
    families: list[dict] = []
    for payload in family_rows:
        family_signatures: list[FanoutSignature] = []
        for seed in _family_signature_payloads(payload):
            signature = signature_from_dict(seed)
            if signature is None or signature.degraded:
                raise ValueError(
                    'fanout_signature_unavailable: 复扫期间签名证据发生变化')
            family_signatures.append(signature)
        if not family_signatures:
            raise ValueError(
                'fanout_signature_unavailable: 复扫期间签名证据发生变化')
        primary = family_signatures[0]
        families.append(_family_payload(
            primary, by_family.get(primary.family_id, ()),
            module_fanout, sd, degrees=degrees,
            orchestrator_roster=roster,
            additional_signatures=family_signatures[1:]))
    occurrences = [item.to_dict() for item in scan.occurrences]
    prior_report = dict(source_report)
    data['occurrences'] = occurrences
    data['families'] = families
    data['module_fanout'] = module_fanout
    data['config'] = asdict(cfg)
    data['errors'] = list(scan.errors)
    data.pop('report_hash', None)
    data.pop('report_path', None)
    data['generated_at'] = timestamp_ms()
    summary = _refresh_report_summary(
        dict_or_empty(data.get('summary')), families, occurrences, scan, sd,
        module_fanout)
    summary['treatment_handoff'] = fanout_treatment_handoff(
        {'families': families}, skill_dir=sd)
    data['summary'] = summary
    data['evolution'] = _evolution_payload(data, prior_report)
    if dict_or_empty(prior_report.get('gate')):
        data['gate'] = _fanout_baseline_gate(sd, data)
    return data
def emit_fanout_report(sd: str, step_result: dict, *,
                       renderer: Callable[..., dict]) -> dict:
    report: dict = {}
    report_path = str_or(step_result.get("report_path"))
    if report_path:
        report = dict_or_empty(_read_report_payload(report_path))
    if not report:
        report = {
            "status": str_or(step_result.get("status")) or "skipped",
            "reason": str_or(step_result.get("reason")),
            "message": (str_or(step_result.get("message"))
                        or str_or(step_result.get("error"))),
            "summary": dict_or_empty(step_result.get("summary")),
            "gate": dict_or_empty(step_result.get("gate")),
        }
    try:
        return emit_fanout_html(sd, report, renderer=renderer)
    except Exception as exc:  # noqa: BLE001
        logger.warning("[FanoutStep] 阶段G HTML 发射失败(降级): %s", exc)
        return {"status": "error",
                "error": f"{type(exc).__name__}: {exc}"[:300]}
def emit_fanout_html(skill_dir: str, report: dict | None = None, *,
                     renderer: Callable[..., dict]) -> dict:
    sd = normalize_skill_dir(skill_dir)
    if isinstance(report, FanoutReport):
        data = report.to_dict()
    else:
        data = dict_or_empty(report) or load_fanout_report(sd)
    if not data:
        data = {
            'schema': FANOUT_REPORT_SCHEMA,
            'status': 'skipped',
            'reason': 'no_fanout_report',
            'summary': {'stage_id': FANOUT_STAGE_ID,
                        'stage_label': FANOUT_STAGE_LABEL},
        }
    data = dict(data)
    data.setdefault('stage_id', FANOUT_STAGE_ID)
    data.setdefault('stage_label', FANOUT_STAGE_LABEL)
    try:
        result = renderer(data, sd, report_type='fanout')
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context='emit_fanout_html')
        return {'status': 'error',
                'error': f'{type(exc).__name__}: {exc}'[:300]}
    if not isinstance(result, dict):
        error = (f'renderer_invalid_result: expected dict, got '
                 f'{type(result).__name__}')
        logger.warning('[FanoutStep] %s', error)
        return {
            'status': 'error', 'error': error,
            'message': '扇出 HTML 渲染器返回非法结果（期望 dict）',
        }
    if result.get('status') != 'ok':
        detail = (str_or(result.get('message'))
                  or str_or(result.get('error'))
                  or 'renderer_failed')[:300]
        return {'status': 'error', 'error': detail, 'message': detail}
    payload = dict_or_empty(result.get('data'))
    path = str_or(payload.get('path'))
    html = str_or(payload.get('html'))
    if not path and not html:
        error = 'renderer_empty_result: status=ok 但未返回 path 或 html'
        logger.warning('[FanoutStep] %s', error)
        return {
            'status': 'error', 'error': error,
            'message': '扇出 HTML 渲染器未返回任何可消费产物',
        }
    return {
        'status': 'ok',
        'path': path,
        'html': html,
        'degraded': signal_bool(payload.get('degraded')),
    }
def fanout_pre_treatment_block(skill_dir: str) -> dict | None:
    try:
        gate = fanout_pre_treatment_gate(skill_dir)
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context='fanout_pre_treatment_block')
        error = f'{type(exc).__name__}: {exc}'[:300]
        gate = {
            'passed': False, 'skipped': False, 'reason': 'gate_error',
            'error': error,
        }
        return {
            'reason': 'gate_error', 'uncovered': 0,
            'message': f'阶段G门禁异常，证据不可用，阻断治疗执行：{error}',
            'gate': gate,
        }
    if gate.get("passed", True):
        return None
    uncovered = int_or(gate.get("uncovered"))
    reason = gate.get("reason")
    return {
        "reason": reason,
        "uncovered": uncovered,
        "message": _gate_block_message(reason, uncovered, gate),
        "gate": gate,
    }
def _gate_block_message(reason: Any, uncovered: int, gate: dict) -> str:
    head = f'阶段G门禁阻断治疗执行（{reason}）'
    if uncovered > 0:
        return f'{head}：未覆盖 {uncovered} 处扇出位点，先补治疗计划再执行'
    actions = [str_or(item) for item in as_list(dict_or_empty(gate).get(
        'actions_required')) if str_or(item)]
    if actions:
        return f'{head}：{actions[0]}'
    return f'{head}：按 gate.actions_required 修复后重跑门禁'

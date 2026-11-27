from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import re
import time
from dataclasses import dataclass
from typing import Any, NamedTuple

from jwsgj.diag_delivery_integrity_gate import (
    check_diagnosis_ledger_coverage,
    check_false_negative_probe,
    check_memory_injection_quality,
    check_precision_evidence,
    check_precision_trend,
    check_stage_pair_integrity,
)
from jwsgj.diag_types_normalize import (
    as_list,
    as_num,
    as_str,
    coerce_round_anchor_strict,
    count_tasks,
    dict_or_empty,
    int_or,
    normalize_list_field,
    now_iso,
    require_dict,
    round_anchor_matches,
    safe_float,
    signal_bool,
    str_or,
)
from jwsgj.diag_types_vocab import (
    FANOUT_DEPENDENCY_THRESHOLD,
    FANOUT_FORBIDDEN_ACTIONS,
    FANOUT_GOVERNANCE_RULE,
    FANOUT_LEVEL_EXCLUDED,
    FANOUT_LEVEL_UNKNOWN,
    FANOUT_ROLE_MODULE,
    FANOUT_STRATEGIES,
    FANOUT_STRATEGY_GOVERNANCE,
    FANOUT_THRESHOLD_PROFILE,
    MANDATORY_PIPELINE_TRIGGER_KEYWORDS,
    P_SCALE_LEVELS,
    SEVERITY_RANK,
    fanout_advisory_scope_text,
    fanout_level_is_mandatory,
    fanout_level_label,
    fanout_mandatory_scope_text,
    is_fanout_excluded_file,
    resolve_fanout_governance_level,
)
from jwsgj.diag_zero_backlog_ledger import (
    _BACKLOG_ITEMS_PREVIEW,
    _DEFAULT_ROUND_START_TS,
    _LEDGER_MISSING_ACTION,
    _MAX_CARRIED_FINDINGS,
    _STATE_EVENT_TYPES,
    CARRY_SNAPSHOT_EVENT,
    FIXED_RESOLUTIONS,
    P0_SEVERITIES,
    TerminalVerdictContext,
    _audit_fp_mask_from_snapshot,
    _build_empty_backlog_report,
    _finding_keys,
    _last_state_by_fid,
    _latest_events_by_idx,
    _latest_finding_seen,
    _load_fp_rules_snapshot,
    _load_ledger_snapshot,
    _pipeline_round_ledger_missing,
    _report_skeleton,
    _severity_rank_of,
    _treatment_fix_proof,
    _verdict_hit_for_context,
    audit_fp_mask,
    build_terminal_context,
    carried_findings,
    classify_terminal,
    current_round_ts,
    finding_identity,
    fp_mask_actions,
    load_ledger_events,
    p0_has_fixed_proof,
    project_round_events,
    resolved_map,
    terminal_verb,
)
from jwsgj.fp_rules_judge import (
    get_fp_rule_ids,
    is_static_fp_rule,
    load_fp_rules,
    load_fp_tracker_rates,
    rules_of,
    save_fp_rules,
)
from jwsgj.log_config import (
    log_swallowed,
)
from jwsgj.runtime_paths import (
    TRIGGER_ENFORCEMENT_FILENAME,
    get_temp_dir,
    json_artifact_path,
    path_scoped_namespace,
)
from jwsgj.runtime_scope import (
    collect_python_files,
    normalize_skill_dir,
)
from jwsgj.treatment_state import (
    SOFT_CLOSURE_BANNED_STATUSES,
    fp_item_identity,
    iter_unique_rule_observations,
    load_treatment_items,
    normalize_item_severity,
)

logger = logging.getLogger(__name__)
__all__ = [
    "DEFAULT_MIN_COUNT",
    "apply_delivery_gates",
    "check_memory_injection_gate",
    "check_method_reachability",
    "check_precision_gate",
    "check_trigger_enforcement",
    "check_zero_backlog",
    "check_zero_residual",
    "fanout_residual_gate",
    "fixate_fp_rules",
    "get_zero_backlog_status",
    "pending_delivery_reviews",
    "run_fp_fixation_step",
]
_CONCLUSION_TO_STAGE = {
    "confirmed": "treatment_open",
    "investigated": "treatment_open",
    "likely": "treatment_open",
    "uncertain": "cv_no_channel",
    "contradictory": "cv_no_channel",
    "review": "cv_no_channel",
    "suppressed": "fp_unreviewed",
}
FUZZY_TERMINAL_MAX_RATIO = 0.5
FUZZY_TERMINAL_MIN_GUARD_TOTAL = 20
def _severity_key(value) -> str:
    return str_or(value).strip().upper()
def _resolution_word(value) -> str:
    return str_or(value).strip().lower()
def _item_status(item: dict) -> str:
    return _resolution_word(item.get("status"))
class _BucketResult(NamedTuple):
    backlog: list
    by_domain: dict
    by_severity: dict
    by_stage: dict
    terminal_count: int
    fuzzy_terminal: int
def _classify_bucketed(findings_all: list,
                      ctx: TerminalVerdictContext) -> _BucketResult:
    backlog = []
    by_domain: dict = {}
    by_severity: dict = {}
    by_stage: dict = {}
    terminal_count = 0
    fuzzy_terminal = 0
    for occurrence, f in enumerate(findings_all):
        source = classify_terminal(f, ctx)
        if source:
            terminal_count += 1
            if source.startswith("ai_verdict_fuzzy"):
                fuzzy_terminal += 1
            continue
        conclusion = str_or(f.get("conclusion")).strip().lower()
        if f.get("carried"):
            stage = "carried_unresolved"
        else:
            stage = _CONCLUSION_TO_STAGE.get(conclusion, "unknown_stage")
        domain = str_or(f.get("domain")).strip() or "unknown"
        severity = _severity_key(f.get("severity")) or "unknown"
        backlog.append({
            "finding_id": finding_identity(f, occurrence=occurrence),
            "stage": stage,
            "domain": domain,
            "severity": severity,
            "rule_id": str_or(f.get("rule_id")),
            "conclusion": conclusion,
            "file": str_or(f.get("file")),
            "line": int_or(f.get("line"), 0),
            "locator": str_or(f.get("locator")),
            "message": str_or(f.get("message"))[:120],
            "carried": bool(f.get("carried")),
            "origin_round": str_or(f.get("origin_round")),
        })
        by_domain[domain] = by_domain.get(domain, 0) + 1
        by_severity[severity] = by_severity.get(severity, 0) + 1
        by_stage[stage] = by_stage.get(stage, 0) + 1
    return _BucketResult(backlog, by_domain, by_severity, by_stage,
                         terminal_count, fuzzy_terminal)
class _P0GuardResult(NamedTuple):
    findings: list
    terminal_ids: set
    backlog_ids: set
    semantic_sweep_ids: list
def _evaluate_p0_guard(findings_all: list,
                       ctx: TerminalVerdictContext) -> _P0GuardResult:
    p0_findings = []
    p0_terminal_ids = set()
    p0_backlog_ids = set()
    p0_semantic_sweep_ids = []
    for occurrence, f in enumerate(findings_all):
        if _severity_key(f.get("severity")) not in P0_SEVERITIES:
            continue
        p0_findings.append(f)
        fid = finding_identity(f, occurrence=occurrence)
        src = classify_terminal(f, ctx)
        if not src:
            p0_backlog_ids.add(fid)
            continue
        p0_resolution = terminal_verb(f, ctx)
        if p0_has_fixed_proof(f, ctx):
            p0_terminal_ids.add(fid)
            continue
        p0_semantic_sweep_ids.append({
            "finding_id": fid,
            "resolution": p0_resolution or src,
            "file": str_or(f.get("file")),
            "line": int_or(f.get("line"), 0),
            "rule_id": str_or(f.get("rule_id")),
        })
    return _P0GuardResult(p0_findings, p0_terminal_ids, p0_backlog_ids,
                          p0_semantic_sweep_ids)
def _stage_actions(by_stage: dict, fp_audit: dict) -> list:
    actions = []
    if by_stage.get("treatment_open"):
        actions.append(f"treatment_open: {by_stage['treatment_open']} 项治疗未终态"
                       "——逐项 AI 审核执行修复或裁决销项（run_next_ai_review）")
    if by_stage.get("cv_no_channel"):
        actions.append(f"cv_no_channel: {by_stage['cv_no_channel']} 项 CV 结论"
                       " uncertain/contradictory/review 无处置通道——逐项裁决"
                       "（resolve_backlog_item：真实问题转修复/误报批 fp_confirmed）")
    if by_stage.get("fp_unreviewed"):
        actions.append(f"fp_unreviewed: {by_stage['fp_unreviewed']} 项被抑制 finding"
                       " 未经复核——逐项复核（resolve_backlog_item resolution="
                       "suppressed_reviewed 确认误报，或转修复）")
    if by_stage.get("unknown_stage"):
        actions.append(f"unknown_stage: {by_stage['unknown_stage']} 项结论未知"
                       "——人工逐条鉴定（拒绝静默放行）")
    if by_stage.get("carried_unresolved"):
        actions.append(f"carried_unresolved: {by_stage['carried_unresolved']} 项"
                       "跨轮结转未终态——轮次切换不销账，逐项处置"
                       "（resolve_backlog_item，幽灵防护认转结 finding_id）")
    actions.extend(fp_mask_actions(fp_audit))
    return actions
def _fuzzy_guard_status(findings_all: list,
                        fuzzy_terminal: int) -> tuple[float, bool]:
    total_all = len(findings_all)
    fuzzy_ratio = (fuzzy_terminal / total_all) if total_all else 0.0
    fuzzy_guard_failed = (
        total_all >= FUZZY_TERMINAL_MIN_GUARD_TOTAL
        and fuzzy_terminal > 0
        and fuzzy_ratio > FUZZY_TERMINAL_MAX_RATIO)
    return fuzzy_ratio, fuzzy_guard_failed
def _p0_guard_actions(p0_backlog_ids: set, p0_semantic_sweep_ids: list) -> list:
    actions = []
    if p0_backlog_ids:
        actions.append(f"p0_guard: {len(p0_backlog_ids)} 项 P0 finding 未终态"
                       "——P0 必须真实修复（fixed/ai_fixed/succeeded），"
                       "不接受任何语义销项（rejected/deferred/suggestion/"
                       "fp_confirmed 一律拒绝）")
    if p0_semantic_sweep_ids:
        actions.append(f"p0_sweep_guard: {len(p0_semantic_sweep_ids)} 项 P0 "
                       "finding 以非修复语义销项——P0 无销项豁免，必须撤回"
                       "该处置并转真实修复（resolve_backlog_item resolution="
                       "fixed/ai_fixed/succeeded）")
    return actions
def _carry_overflow_action(overflow: int) -> str:
    return (
        f"carry_overflow: 未复核积压超出追踪上限 "
        f"{_MAX_CARRIED_FINDINGS} 条，最旧 {overflow} 条"
        "只记计数不再逐条保留——先用 resolve_backlog_item 清理积压"
        "再重跑（不得静默丢弃未复核 finding）")
def _backlog_items_for_stage(backlog: list, stage: str) -> list:
    return [b for b in backlog if b["stage"] == stage]
class _GuardInputs(NamedTuple):
    findings_all: list
    backlog: list
    by_domain: dict
    by_severity: dict
    by_stage: dict
    terminal_count: int
    fp_audit: dict
    fuzzy_terminal: int
    ctx: TerminalVerdictContext
    ledger_missing: bool
    carry_overflow: int = 0
@dataclass(frozen=True)
class _GuardReport:
    passed: bool
    actions: list
    fuzzy_ratio: float
    fuzzy_guard_passed: bool
    p0_guard_passed: bool
    p0_findings: list
    p0_terminal_ids: set
    p0_backlog_ids: set
    p0_semantic_sweep_ids: list
    treatment_guard_passed: bool
    treatment_open_items: list
    cv_channel_guard_passed: bool
    cv_no_channel_items: list
def _evaluate_gate_guards(inputs: _GuardInputs) -> _GuardReport:
    actions = _stage_actions(inputs.by_stage, inputs.fp_audit)
    fuzzy_ratio, fuzzy_failed = _fuzzy_guard_status(
        inputs.findings_all, inputs.fuzzy_terminal)
    if fuzzy_failed:
        actions.append(f"fuzzy_terminal_guard: 株连式模糊终态 {inputs.fuzzy_terminal} 项"
                       f" 占比 {fuzzy_ratio:.0%} 超上限 "
                       f"{FUZZY_TERMINAL_MAX_RATIO:.0%}——对 rule_id/basename "
                       "株连判终态的 findings 逐项复核（resolve_backlog_item）"
                       "或补精确裁决（locator/file+line+rule）")
    p0 = _evaluate_p0_guard(inputs.findings_all, inputs.ctx)
    p0_failed = bool(p0.backlog_ids or p0.semantic_sweep_ids)
    actions.extend(_p0_guard_actions(p0.backlog_ids, p0.semantic_sweep_ids))
    treatment_items = _backlog_items_for_stage(inputs.backlog, "treatment_open")
    cv_items = _backlog_items_for_stage(inputs.backlog, "cv_no_channel")
    if inputs.ledger_missing:
        actions.append(_LEDGER_MISSING_ACTION)
    if inputs.carry_overflow:
        actions.append(_carry_overflow_action(inputs.carry_overflow))
    passed = (not inputs.backlog and inputs.fp_audit["passed"]
              and not fuzzy_failed and not p0_failed
              and not treatment_items and not cv_items
              and not inputs.ledger_missing
              and not inputs.carry_overflow)
    return _GuardReport(
        passed=passed, actions=actions, fuzzy_ratio=fuzzy_ratio,
        fuzzy_guard_passed=not fuzzy_failed, p0_guard_passed=not p0_failed,
        p0_findings=p0.findings, p0_terminal_ids=p0.terminal_ids,
        p0_backlog_ids=p0.backlog_ids,
        p0_semantic_sweep_ids=p0.semantic_sweep_ids,
        treatment_guard_passed=not treatment_items,
        treatment_open_items=treatment_items,
        cv_channel_guard_passed=not cv_items,
        cv_no_channel_items=cv_items)
def _gate_block_reasons(inputs: _GuardInputs, guard: _GuardReport) -> list:
    reasons = []
    if inputs.backlog:
        reasons.append(f"{len(inputs.backlog)} 项 finding 未终态")
    reasons.extend(_fp_audit_block_reasons(inputs.fp_audit))
    if not guard.fuzzy_guard_passed:
        reasons.append(
            f"模糊终态 {inputs.fuzzy_terminal} 项占比 {guard.fuzzy_ratio:.0%} "
            f"超上限 {FUZZY_TERMINAL_MAX_RATIO:.0%}")
    if not guard.p0_guard_passed:
        reasons.append(
            f"P0 守卫未过（未终态 {len(guard.p0_backlog_ids)} 项, "
            f"非修复销项 {len(guard.p0_semantic_sweep_ids)} 项）")
    if not guard.treatment_guard_passed:
        reasons.append(f"治疗通道 {len(guard.treatment_open_items)} 项待执行")
    if not guard.cv_channel_guard_passed:
        reasons.append(f"CV 通道 {len(guard.cv_no_channel_items)} 项无处置")
    if inputs.carry_overflow:
        reasons.append(
            f"结转积压溢出 {inputs.carry_overflow} 条（超出追踪上限 "
            f"{_MAX_CARRIED_FINDINGS}）")
    if inputs.ledger_missing:
        reasons.append("台账缺当前轮 round_open 登记")
    return reasons
def _fp_audit_block_reasons(fp_audit: dict) -> list:
    reasons = []
    sampled = fp_audit.get("fp_sampled_unreviewed") or []
    sampled_n = (len(sampled)
                 if isinstance(sampled, (list, tuple, set)) else 0)
    unreviewed = int_or(fp_audit.get("unreviewed"), 0)
    if not fp_audit.get("passed", False):
        if fp_audit.get("gate_error"):
            reasons.append(
                "误报掩盖审计执行异常"
                f"（{str(fp_audit.get('gate_error'))[:120]}）")
        elif unreviewed < 0:
            reasons.append(
                "误报掩盖审计计数异常（-1 为异常哨兵，不是待复核条数）")
        elif unreviewed or sampled_n:
            reasons.append(
                "误报掩盖审计未通过"
                f"（{unreviewed} 条被抑制未复核, "
                f"{sampled_n}/{int_or(fp_audit.get('fp_sampled_count'), 0)} "
                "条抽样规则未复核）")
    if fp_audit.get("ledger_errors"):
        reasons.append(
            f"台账读取/解析错误 {len(fp_audit['ledger_errors'])} 条")
    if fp_audit.get("fp_rule_errors"):
        reasons.append(
            f"误报规则读取/解析错误 {len(fp_audit['fp_rule_errors'])} 条")
    return reasons
def _log_gate_outcome(inputs: _GuardInputs, guard: _GuardReport,
                      carried_count: int) -> None:
    if inputs.ledger_missing:
        logger.error("[ZeroBacklog] 登记缺失阻塞: 管线轮存在但台账无该轮"
                     "round_open 事件（登记软失败=静默绕过通道已封闭）")
    if guard.passed:
        logger.info("[ZeroBacklog] 归零门禁通过: %d/%d 全终态"
                    "（含结转 %d，模糊终态 %d）",
                    inputs.terminal_count, len(inputs.findings_all),
                    carried_count, inputs.fuzzy_terminal)
        return
    logger.warning("[ZeroBacklog] 归零门禁阻塞: %s（未终态 %d/%d, "
                   "按域=%s, 按级别=%s, 按阶段=%s）",
                   "；".join(_gate_block_reasons(inputs, guard))
                   or "未知阻塞（守卫判据不一致）",
                   len(inputs.backlog), len(inputs.findings_all),
                   inputs.by_domain, inputs.by_severity, inputs.by_stage)
def _compose_gate_report(round_ts: str, cur_count: int, carried: list,
                         inputs: _GuardInputs, guard: _GuardReport) -> dict:
    backlog = inputs.backlog
    return {
        **_report_skeleton(round_ts, inputs.fp_audit),
        "passed": guard.passed,
        "ledger_missing": inputs.ledger_missing,
        "total_findings": len(inputs.findings_all),
        "total_findings_current_round": cur_count,
        "carried_count": len(carried),
        "carry_overflow": inputs.carry_overflow,
        "terminal_count": inputs.terminal_count,
        "terminal_exact_count": inputs.terminal_count - inputs.fuzzy_terminal,
        "terminal_fuzzy_count": inputs.fuzzy_terminal,
        "fuzzy_terminal_ratio": round(guard.fuzzy_ratio, 4),
        "fuzzy_terminal_guard_passed": guard.fuzzy_guard_passed,
        "p0_guard_passed": guard.p0_guard_passed,
        "p0_total": len(guard.p0_findings),
        "p0_terminal": len(guard.p0_terminal_ids),
        "p0_backlog": len(guard.p0_backlog_ids),
        "p0_semantic_sweep": guard.p0_semantic_sweep_ids[:_BACKLOG_ITEMS_PREVIEW],
        "p0_semantic_sweep_truncated": max(
            0, len(guard.p0_semantic_sweep_ids) - _BACKLOG_ITEMS_PREVIEW),
        "treatment_guard_passed": guard.treatment_guard_passed,
        "treatment_open_count": len(guard.treatment_open_items),
        "cv_channel_guard_passed": guard.cv_channel_guard_passed,
        "cv_no_channel_count": len(guard.cv_no_channel_items),
        "backlog_count": len(backlog),
        "backlog_by_domain": inputs.by_domain,
        "backlog_by_severity": inputs.by_severity,
        "backlog_by_stage": inputs.by_stage,
        "backlog_items": backlog[:_BACKLOG_ITEMS_PREVIEW],
        "backlog_truncated": max(0, len(backlog) - _BACKLOG_ITEMS_PREVIEW),
        "actions_required": guard.actions,
    }
class _ZeroBacklogAnalysis(NamedTuple):
    report: dict
    events: list
    round_ts: str
    cur: list
    findings_all: list
    backlog_ids: set
    ctx: TerminalVerdictContext
def _carry_overflow_count(events: list, project: str = "") -> int:
    """本项目最近的 ``carry_snapshot`` 溢出条数（0 表示未超上限）。

    溢出意味着「未复核积压超出 ``_MAX_CARRIED_FINDINGS`` 条追踪上限」，
    最旧的那部分只记计数、不再逐条保留。此时必须阻断：静默丢弃会让门禁
    看不到积压而误判通过（安全倒退）。新快照已清零或其他项目的溢出均
    不得继续阻断本项目。
    """
    wanted = str_or(project).strip()
    for event in reversed(as_list(events)):
        if not isinstance(event, dict):
            continue
        if event.get("event") != CARRY_SNAPSHOT_EVENT:
            continue
        event_project = str_or(event.get("project")).strip()
        if wanted and event_project and event_project != wanted:
            continue
        return max(0, int_or(event.get("overflow_count"), 0))
    return 0
def _analyze_zero_backlog(
        skill_dir: str, round_start_ts: str,
) -> _ZeroBacklogAnalysis:
    sd = normalize_skill_dir(skill_dir)
    events, ledger_errors = _load_ledger_snapshot(sd)
    requested_round = coerce_round_anchor_strict(round_start_ts)
    if requested_round is None:
        logger.warning("[ZeroBacklog] round_start_ts 形态非法(%s)，按当前轮解析",
                       type(round_start_ts).__name__)
        requested_round = ""
    else:
        requested_round = requested_round.strip()
    project = path_scoped_namespace(sd)
    round_ts = requested_round or current_round_ts(events, project)
    cur = project_round_events(events, round_ts, project)
    round_absent = bool(requested_round) and not any(
        str_or(ev.get("round_start_ts")).strip() == requested_round
        for ev in events)
    if round_absent:
        logger.error("[ZeroBacklog] 轮次锚 %s 在台账中无任何事件"
                     "（登记缺失=静默绕过通道已封闭）", requested_round)
    findings = _latest_finding_seen(cur)
    carried = carried_findings(events, cur, round_ts, project=project)
    findings_all = list(findings) + carried
    ctx = build_terminal_context(sd, resolved_map(cur), round_ts)
    fp_audit = _audit_fp_mask_from_snapshot(
        sd, events, round_ts, ledger_errors, ctx=ctx)
    if not findings_all:
        report = _build_empty_backlog_report(sd, round_ts, fp_audit, events)
        carry_overflow = _carry_overflow_count(events, project=project)
        report["carry_overflow"] = carry_overflow
        actions = list(report.get("actions_required") or [])
        if round_absent:
            report["passed"] = False
            report["ledger_missing"] = True
            if _LEDGER_MISSING_ACTION not in actions:
                actions.insert(0, _LEDGER_MISSING_ACTION)
        if carry_overflow:
            # 保留项可能已全部终结，但被溢出的未复核项仍不可静默消失。
            report["passed"] = False
            action = _carry_overflow_action(carry_overflow)
            if action not in actions:
                actions.insert(0, action)
        report["actions_required"] = actions
        return _ZeroBacklogAnalysis(
            report, events, round_ts, cur, findings_all, set(), ctx)
    _, ledger_missing = _pipeline_round_ledger_missing(sd, events)
    ledger_missing = ledger_missing or round_absent
    buckets = _classify_bucketed(findings_all, ctx)
    inputs = _GuardInputs(
        findings_all=findings_all, backlog=buckets.backlog,
        by_domain=buckets.by_domain, by_severity=buckets.by_severity,
        by_stage=buckets.by_stage, terminal_count=buckets.terminal_count,
        fp_audit=fp_audit, fuzzy_terminal=buckets.fuzzy_terminal, ctx=ctx,
        ledger_missing=ledger_missing,
        carry_overflow=_carry_overflow_count(events, project=project))
    guard = _evaluate_gate_guards(inputs)
    _log_gate_outcome(inputs, guard, len(carried))
    report = _compose_gate_report(
        round_ts, len(findings), carried, inputs, guard)
    backlog_ids = {str_or(item.get("finding_id"))
                   for item in buckets.backlog} - {""}
    return _ZeroBacklogAnalysis(
        report, events, round_ts, cur, findings_all, backlog_ids, ctx)
_FANOUT_REPORT_LATEST = "fanout_report_latest.json"
_FANOUT_GATE_LEVELS = frozenset({"exact", "variant"})
def _load_fanout_report_snapshot(sd: str) -> tuple[dict, str, str]:
    path = ""
    try:
        path = json_artifact_path(sd, _FANOUT_REPORT_LATEST)
        if not os.path.isfile(path):
            return {}, "", ""
        with open(path, encoding="utf-8-sig", errors="replace") as handle:
            payload = json.load(handle)
    except (OSError, ValueError, RuntimeError, RecursionError) as exc:
        log_swallowed(__name__, exc, context="_load_fanout_report_snapshot")
        return {}, "report_unreadable", f"{type(exc).__name__}: {exc}"[:300]
    if not isinstance(payload, dict):
        logger.warning("[FanoutGate] 扇出报告形态非法(%s)，保守阻断: %s",
                       type(payload).__name__, path)
        return {}, "invalid_report", f"payload is {type(payload).__name__}"
    if not payload:
        logger.warning("[FanoutGate] 扇出报告为空对象（存在但无内容），"
                       "保守阻断: %s", path)
        return {}, "invalid_report", "payload is empty object"
    return dict(payload), "", ""
def _fanout_gate_occurrence(item: dict) -> bool:
    if not isinstance(item, dict) or not item:
        return False
    return bool(
        str_or(item.get("level")).strip().lower() in _FANOUT_GATE_LEVELS
        and item.get("guarded") is not True
        and not is_fanout_excluded_file(str_or(item.get("file")))
        and str_or(item.get("module_governance_level")).strip().lower()
        != FANOUT_LEVEL_EXCLUDED)
def _fanout_report_shape_error(data: dict) -> str:
    if "occurrences" not in data:
        return "occurrences is required"
    for field, kind in (("occurrences", dict), ("families", dict),
                        ("file_universe", str), ("errors", dict)):
        if field not in data:
            continue
        values = data.get(field)
        if not isinstance(values, list):
            return f"{field} is {type(values).__name__}, expected list"
        for item in values:
            if not isinstance(item, kind):
                return (f"{field} contains {type(item).__name__}, "
                        f"expected {kind.__name__}")
    config = dict_or_empty(data).get("config")
    if config is not None and not isinstance(config, dict):
        return f"config is {type(config).__name__}, expected dict"
    summary = dict_or_empty(data).get("summary")
    if summary is not None and not isinstance(summary, dict):
        return f"summary is {type(summary).__name__}, expected dict"
    return ""
def _fanout_scan_incomplete(data: dict) -> str:
    details: list[str] = []
    errors = as_list(data.get("errors"))
    if errors:
        details.append(f"errors={len(errors)}")
    summary = dict_or_empty(data.get("summary"))
    raw_files_failed = summary.get("files_failed", 0)
    files_failed = count_tasks(raw_files_failed, clamp_negative=False)
    files_failed_number = safe_float(raw_files_failed, None)
    if (files_failed is None or files_failed_number is None
            or not float(files_failed_number).is_integer()):
        details.append(f"files_failed_invalid={raw_files_failed!r}")
    elif files_failed:
        details.append(f"files_failed={files_failed}")
    truncated = summary.get("truncated_families", [])
    if not isinstance(truncated, list):
        details.append(
            f"truncated_families_invalid={type(truncated).__name__}")
    elif truncated:
        details.append(f"truncated_families={len(truncated)}")
    return "；".join(details)
def _fanout_governance_violations(data: dict) -> list[str]:
    violations: list[str] = []
    for raw_family in as_list(dict_or_empty(data).get("families")):
        family = dict_or_empty(raw_family)
        if not family:
            continue
        family_id = (str_or(family.get("family_id"))
                     or str_or(family.get("rule_id")))
        treatable = [
            item for item in (
                dict_or_empty(raw)
                for raw in as_list(family.get("occurrences")))
            if _fanout_gate_occurrence(item)
        ]
        if not treatable:
            continue
        governance = dict_or_empty(family.get("governance"))
        if not governance:
            violations.append(f"{family_id}: 族缺治理策略声明")
            continue
        strategy = str_or(governance.get("strategy"))
        if strategy not in FANOUT_STRATEGIES:
            violations.append(f"{family_id}: 未知治理策略 {strategy!r}")
            continue
        expected = FANOUT_STRATEGY_GOVERNANCE.get(strategy)
        if expected is None:
            violations.append(
                f"{family_id}: 策略 {strategy} 缺治理方法映射")
            continue
        method = str_or(governance.get("governance_method"))
        if method != expected:
            violations.append(
                f"{family_id}: 策略 {strategy} 应映射治理方法 "
                f"{expected}，实为 {method!r}")
        forbidden = {
            str_or(item) for item in as_list(governance.get("forbidden_actions"))
        }
        missing = set(FANOUT_FORBIDDEN_ACTIONS) - forbidden
        if missing:
            violations.append(
                f"{family_id}: 未声明禁止动作 {'/'.join(sorted(missing))}")
    return violations
def _fanout_file_integrity(skill_dir: str, data: dict) -> dict:
    if "file_universe" not in data:
        return {"enabled": False, "passed": True, "new_files": []}
    snapshot = [
        str_or(item) for item in as_list(data.get("file_universe"))
    ]
    snapshot = [item for item in snapshot if item]
    summary = dict_or_empty(data.get("summary"))
    if (not snapshot
            and type(summary.get("signatures")) is int
            and summary.get("signatures") == 0
            and type(summary.get("files_scanned")) is int
            and summary.get("files_scanned") == 0
            and not data.get("occurrences")
            and not data.get("families")):
        return {"enabled": False, "passed": True, "new_files": [],
                "reason": "no_signatures"}
    config = dict_or_empty(data.get("config"))
    include_tests = signal_bool(config.get("include_tests", True))
    max_files = int_or(config.get("max_files"), 0)
    walk_errors: list[OSError] = []
    current = {
        os.path.relpath(path, skill_dir).replace("\\", "/")
        for path in collect_python_files(
            skill_dir, include_tests=include_tests, max_files=max_files,
            walk_errors=walk_errors)
    }
    if walk_errors:
        detail = "; ".join(
            f"{type(exc).__name__}: {exc}"[:120] for exc in walk_errors[:3])
        raise OSError(f"current file scan incomplete: {detail}")
    known = set(snapshot)
    new_files = sorted(current - known)
    return {
        "enabled": True,
        "passed": not new_files,
        "baseline": len(known),
        "current": len(current),
        "new_files": new_files,
        "removed_files": sorted(known - current),
    }
def _fanout_gate_findings(occurrences) -> list[dict]:
    findings: list[dict] = []
    for raw in occurrences if isinstance(occurrences, list) else []:
        item = dict_or_empty(raw)
        if not _fanout_gate_occurrence(item):
            continue
        findings.append({
            "finding_id": str_or(item.get("occurrence_id")),
            "locator": (f"{str_or(item.get('file'))}:"
                        f"{int_or(item.get('line'), 0)}:"
                        f"{str_or(item.get('rule_id'))}"),
            "file": str_or(item.get("file")),
            "line": int_or(item.get("line"), 0),
            "rule_id": str_or(item.get("rule_id")),
            "module_governance_level": str_or(
                item.get("module_governance_level")),
            "module_governance_label": fanout_level_label(
                str_or(item.get("module_governance_level"))
                or FANOUT_LEVEL_UNKNOWN),
            "module_role": str_or(item.get("module_role"))
            or FANOUT_ROLE_MODULE,
            "module_role_label": str_or(
                item.get("module_role_label")),
            "module_governance_tier": str_or(
                item.get("module_governance_tier")),
            "module_dependency_fanout": item.get(
                "module_dependency_fanout"),
        })
    return findings
def _fanout_gate_mandatory(item: dict) -> bool:
    return fanout_level_is_mandatory(
        resolve_fanout_governance_level(dict_or_empty(item)))
_FANOUT_NO_REPORT_REASON = "no_fanout_report"
_FANOUT_GATE_SKIPPED: dict = {
    "passed": True, "skipped": True, "reason": _FANOUT_NO_REPORT_REASON,
    "total": 0, "handled": 0, "residual": 0, "residual_total": 0,
    "advisory_residual": 0, "residual_items": [], "advisory_items": [],
    "actions_required": [], "strategy_violations": [],
    "file_integrity": {},
}
def _fanout_gate_skipped(reason: str = "") -> dict:
    payload = {
        key: (list(value) if isinstance(value, list)
              else dict(value) if isinstance(value, dict) else value)
        for key, value in _FANOUT_GATE_SKIPPED.items()
    }
    payload["reason"] = reason or _FANOUT_NO_REPORT_REASON
    return payload
def _fanout_gate_failure(reason: str, detail: str, action: str) -> dict:
    payload = _fanout_gate_skipped(reason)
    payload.update({"passed": False, "skipped": False,
                    "gate_error": detail[:300], "actions_required": [action]})
    return payload
def _fanout_gate_residual_split(
    findings: list[dict], sd: str, round_ts: str,
    events: list | None = None,
) -> tuple[list[dict], list[dict], list[dict]]:
    if events is None:
        events = load_ledger_events(sd)
    project = path_scoped_namespace(normalize_skill_dir(sd))
    anchor = round_ts or current_round_ts(events, project)
    current_events = project_round_events(events, anchor, project)
    ctx = build_terminal_context(
        sd, resolved_map(current_events), anchor)
    unresolved = [item for item in findings
                  if not classify_terminal(item, ctx)]
    residual = [item for item in unresolved if _fanout_gate_mandatory(item)]
    advisory_residual = [item for item in unresolved
                         if not _fanout_gate_mandatory(item)]
    return unresolved, residual, advisory_residual
def _fanout_gate_actions(
    residual: list[dict],
    advisory_residual: list[dict],
    strategy_violations: list[str],
    file_integrity: dict,
) -> list[str]:
    actions: list[str] = []
    if residual:
        sample = "、".join(
            f"{item['file']}:{item['line']}" for item in residual[:5])
        actions.append(
            f"fanout_residual: {len(residual)} 处 L4 危机位点未处置"
            f"（{sample}）——{fanout_mandatory_scope_text()}，"
            f"按族根因修复或逐条误报留痕")
    if advisory_residual:
        sample = "、".join(
            f"{item['file']}:{item['line']}" for item in advisory_residual[:5])
        actions.append(
            f"fanout_advisory: {len(advisory_residual)} 处 L1-L3 位点"
            f"未处置（{sample}）——{fanout_advisory_scope_text()}，"
            "补方案对比（pros/cons/net_benefit）后治理或留痕；不阻断")
    if strategy_violations:
        actions.append(
            "fanout_strategy: " + "；".join(strategy_violations[:5]))
    if not file_integrity.get("passed", True):
        new_files = file_integrity.get("new_files") or []
        actions.append(
            f"fanout_split: 治理新增 {len(new_files)} 个模块文件"
            f"（{', '.join(new_files[:5])}）——扇出治理禁止拆分文件")
    return actions
def _fanout_gate_reasons(
    residual: list[dict],
    strategy_violations: list[str],
    file_integrity: dict,
) -> list[str]:
    return [
        reason for reason, hit in (
            ("residual_unhandled", residual),
            ("strategy_violation", strategy_violations),
            ("split_file", not file_integrity.get("passed", True)),
        ) if hit
    ]
def fanout_residual_gate(skill_dir: str, report: dict | None = None) -> dict:
    sd = normalize_skill_dir(skill_dir)
    load_error = ""
    error_detail = ""
    if report is None:
        data, load_error, error_detail = _load_fanout_report_snapshot(sd)
    elif isinstance(report, dict):
        data = dict(report)
    else:
        data, load_error, error_detail = (
            {}, "invalid_report", f"payload is {type(report).__name__}")
    if load_error:
        return _fanout_gate_failure(
            load_error, error_detail,
            "fanout_report: 扇出证据缺失或损坏时不得按未启用放行；"
            "重新生成可读报告后重跑门禁")
    if not data:
        if report is not None:
            return _fanout_gate_failure(
                "invalid_report", "payload is empty object",
                "fanout_report: 显式空报告不是『无报告』，重新生成完整报告后重跑")
        return _fanout_gate_skipped()
    shape_error = _fanout_report_shape_error(data)
    if shape_error:
        logger.warning("[FanoutGate] 扇出报告内层形态非法(%s)，保守阻断",
                       shape_error)
        return _fanout_gate_failure(
            "invalid_report", shape_error,
            "fanout_report: 扇出报告字段形态非法（occurrences/families "
            "须为对象列表、file_universe 须为字符串列表）；重新生成报告后重跑门禁")
    raw_report_round = data.get("round_start_ts")
    report_round = coerce_round_anchor_strict(raw_report_round)
    if report_round is None:
        return _fanout_gate_failure(
            "invalid_report", "round_start_ts has invalid type or value",
            "fanout_round: 轮次锚必须是字符串或有限数值；重新生成报告后重跑")
    report_round = report_round.strip()
    events, ledger_errors = _load_ledger_snapshot(sd)
    if ledger_errors:
        detail = "; ".join(str(item)[:120] for item in ledger_errors[:3])
        return _fanout_gate_failure(
            "ledger_unreadable", detail,
            "fanout_ledger: 台账读取/解析失败，轮次与终态证据不可用——"
            "修复台账后重跑扇出门禁")
    try:
        current_round, _ = _pipeline_round_ledger_missing(sd, events)
    except Exception as exc:
        log_swallowed(__name__, exc, context="fanout_residual_gate:ledger_round")
        return _fanout_gate_failure(
            "ledger_unreadable", f"{type(exc).__name__}: {exc}",
            "fanout_round: 无法读取台账轮次，修复台账后重跑扇出门禁")
    if not current_round:
        # 管线中间态缺失（产物清理、会话恢复、独立门禁调用）时，若报告轮次
        # 与台账本项目轮次一致，则归属可确认——否则台账已有轮次锚仍被判
        # round_unverifiable 永久阻断交付。仅当两者一致才采用该回落，轮次
        # 不一致仍保守阻断（不把「无法归属」降级为放行）。
        ledger_round = current_round_ts(events, path_scoped_namespace(sd))
        if ledger_round and round_anchor_matches(report_round, ledger_round):
            current_round = ledger_round
    if current_round and not report_round:
        return _fanout_gate_failure(
            "round_missing",
            f"current round is {current_round}, but report round is missing",
            "fanout_round: 当前管线已有轮次锚，报告缺轮次不得按过期报告放行；"
            "重新生成带 round_start_ts 的报告")
    if not round_anchor_matches(report_round, current_round):
        if not current_round:
            return _fanout_gate_failure(
                "round_unverifiable",
                f"report round is {report_round!r}, but neither pipeline nor "
                "ledger has a current round anchor",
                "fanout_round: 管线与台账均无当前轮次锚，无法确认扇出报告"
                "归属——先登记/恢复管线轮次后重跑扇出门禁")
        return _fanout_gate_skipped("stale_round")
    incomplete = _fanout_scan_incomplete(data)
    if incomplete:
        logger.warning("[FanoutGate] 扇出扫描证据不完整(%s)，保守阻断", incomplete)
        return _fanout_gate_failure(
            "scan_incomplete", incomplete,
            "fanout_scan: 报告含扫描错误、文件失败或族截断；"
            "修复扫描并重跑，残缺证据不得按零残留放行")
    findings = _fanout_gate_findings(data.get("occurrences"))
    try:
        unresolved, residual, advisory_residual = _fanout_gate_residual_split(
            findings, sd, report_round or current_round, events)
    except Exception as exc:
        log_swallowed(__name__, exc, context="fanout_residual_gate:terminal")
        return _fanout_gate_failure(
            "terminal_unavailable", f"{type(exc).__name__}: {exc}",
            "fanout_ledger: 终态索引不可用，无法区分已处理与残留位点——"
            "修复终态证据后重跑扇出门禁")
    strategy_violations = _fanout_governance_violations(data)
    try:
        file_integrity = _fanout_file_integrity(sd, data)
    except (OSError, ValueError, RuntimeError, RecursionError) as exc:
        log_swallowed(
            __name__, exc, context="fanout_residual_gate:file_integrity")
        return _fanout_gate_failure(
            "file_integrity_error", f"{type(exc).__name__}: {exc}",
            "fanout_file: 无法重建当前文件面（技能根/文件系统不可用）——"
            "修复后重跑扇出门禁")
    actions = _fanout_gate_actions(
        residual, advisory_residual, strategy_violations, file_integrity)
    reasons = _fanout_gate_reasons(residual, strategy_violations, file_integrity)
    passed = not reasons
    return {
        "passed": passed,
        "skipped": False,
        "reason": "" if passed else "+".join(reasons),
        "total": len(findings),
        "handled": len(findings) - len(unresolved),
        "residual": len(residual),
        "residual_items": residual,
        "residual_total": len(unresolved),
        "advisory_residual": len(advisory_residual),
        "advisory_items": advisory_residual,
        "governance_threshold": FANOUT_DEPENDENCY_THRESHOLD,
        "governance_thresholds": dict(FANOUT_THRESHOLD_PROFILE),
        "governance_rule": FANOUT_GOVERNANCE_RULE,
        "strategy_violations": strategy_violations,
        "file_integrity": file_integrity,
        "actions_required": actions,
    }
def _attach_fanout_gate(report: dict, skill_dir: str) -> dict:
    gate = fanout_residual_gate(skill_dir)
    report["fanout"] = gate
    if _gate_passed(gate):
        return report
    report["passed"] = False
    actions = report.get("actions_required")
    if not isinstance(actions, list):
        actions = []
        report["actions_required"] = actions
    actions.extend(gate.get("actions_required") or [])
    return report
def check_zero_backlog(
        skill_dir: str, round_start_ts: str = _DEFAULT_ROUND_START_TS) -> dict:
    report = _analyze_zero_backlog(skill_dir, round_start_ts).report
    return _attach_fanout_gate(report, skill_dir)
_STATUS_REPORT_KEYS = ("round_start_ts", "total_findings", "carried_count",
                       "terminal_count", "terminal_fuzzy_count",
                       "backlog_count")
def get_zero_backlog_status(skill_dir: str) -> dict:
    report = check_zero_backlog(skill_dir)
    status = {key: report.get(key, 0) for key in _STATUS_REPORT_KEYS}
    status["round_start_ts"] = str_or(status["round_start_ts"])
    status["passed"] = _gate_passed(report)
    return status
SOFT_CLOSURE_STATUSES = SOFT_CLOSURE_BANNED_STATUSES
SOFT_CLOSURE_RESOLUTIONS = (
    frozenset({"deferred", "rejected"}) | SOFT_CLOSURE_STATUSES)
_VERDICT_EXECUTED = frozenset({"approve_and_fix", "approve"})
_VERDICT_SOFT = frozenset({"defer", "reject"})
_VERDICT_FP = "reject_as_fp"
_SEVERITY_ORDER = tuple(sorted(
    P_SCALE_LEVELS, key=lambda level: SEVERITY_RANK[level]))
_RESIDUAL_PREVIEW = 40
def _residual_item(ev: dict, kind: str, reason: str) -> dict:
    return {
        "kind": kind,
        "finding_id": str_or(ev.get("finding_id")),
        "rule_id": str_or(ev.get("rule_id")),
        "severity": _severity_key(ev.get("severity")) or "unknown",
        "domain": str_or(ev.get("domain")).strip() or "unknown",
        "file": str_or(ev.get("file")),
        "line": int_or(ev.get("line"), 0),
        "resolution": str_or(ev.get("resolution")),
        "reason": reason,
    }
def _soft_ledger_closures(events: list) -> list:
    out = []
    for _idx, ev in _latest_events_by_idx(events, _STATE_EVENT_TYPES):
        if ev.get("event") != "finding_resolved":
            continue
        if _resolution_word(ev.get("resolution")) not in SOFT_CLOSURE_RESOLUTIONS:
            continue
        out.append(_residual_item(
            ev, "soft_ledger_closure",
            "台账以 deferred/rejected/suggestion 销项：既未改码也未固化误报"))
    return out
def _soft_treatment_closures(items: list,
                             proof_ctx: TerminalVerdictContext) -> list:
    out = []
    for idx, item in enumerate(items):
        if not isinstance(item, dict):
            continue
        if _item_status(item) not in SOFT_CLOSURE_STATUSES:
            continue
        keys = _finding_keys({
            "locator": item.get("locator"),
            "file": item.get("file_path") or item.get("file"),
            "line": item.get("line"),
            "rule_id": item.get("rule_id"),
        })
        if _treatment_fix_proof(keys, proof_ctx):
            continue
        out.append({
            "kind": "soft_treatment_closure",
            "index": idx,
            "finding_id": str_or(item.get("finding_id")),
            "rule_id": str_or(item.get("rule_id")),
            "severity": _severity_key(item.get("severity")) or "unknown",
            "domain": str_or(item.get("domain")).strip() or "unknown",
            "file": str_or(item.get("file_path") or item.get("file")),
            "line": int_or(item.get("line"), 0),
            "resolution": str_or(item.get("status")),
            "reason": "治疗项以 suggestion 收口（reject/defer 落点）："
                      "未改码也未固化误报，强口径下计为残留",
        })
    return out
def _verdict_only_evidence(finding: dict,
                           ctx: TerminalVerdictContext) -> frozenset:
    fid = str_or(finding.get("finding_id"))
    if fid and fid in ctx.resolved:
        return frozenset()
    keys = _finding_keys(finding)
    if ctx.t_index.has_evidence(keys):
        return frozenset()
    return _verdict_hit_for_context(keys, ctx)[1]
def _soft_verdict_closures(findings_all: list,
                           ctx: TerminalVerdictContext) -> list:
    out = []
    for finding in findings_all:
        verdicts = _verdict_only_evidence(finding, ctx)
        soft = verdicts & _VERDICT_SOFT
        if not soft or verdicts & _VERDICT_EXECUTED or _VERDICT_FP in verdicts:
            continue
        item = _residual_item(
            finding, "soft_verdict_closure",
            f"AI 裁决以 {'/'.join(sorted(soft))} 结案："
            "既未改码也未固化误报")
        item["resolution"] = "/".join(sorted(soft))
        out.append(item)
    return out
def _verdict_fp_rules(findings_all: list,
                      ctx: TerminalVerdictContext) -> set:
    rules = set()
    for finding in findings_all:
        verdicts = _verdict_only_evidence(finding, ctx)
        if _VERDICT_FP not in verdicts or verdicts & _VERDICT_EXECUTED:
            continue
        rule_id = _fp_rule_id_or_empty(finding.get("rule_id"))
        if rule_id:
            rules.add(rule_id)
    return rules
def _rule_id_by_finding(events: list) -> dict[str, str]:
    out: dict[str, str] = {}
    for ev in events:
        if ev.get("event") != "finding_seen":
            continue
        fid = str_or(ev.get("finding_id"))
        rid = str_or(ev.get("rule_id"))
        if fid and rid:
            out[fid] = rid
    return out
def _substantive_fp_evidence(value, depth: int = 0) -> bool:
    if depth > 8 or value is None or isinstance(value, (bool, int, float)):
        return False
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, dict):
        return any(_substantive_fp_evidence(item, depth + 1)
                   for item in value.values())
    if isinstance(value, (list, tuple, set, frozenset)):
        return any(_substantive_fp_evidence(item, depth + 1)
                   for item in value)
    return False
def _fp_evidence_present(record: dict) -> bool:
    if not isinstance(record, dict):
        return False
    result = dict_or_empty(record.get("result"))
    assessment = dict_or_empty(result.get("ai_review_assessment"))
    return any(_substantive_fp_evidence(value) for value in (
        record.get("fp_evidence"), record.get("rationale"),
        result.get("fp_evidence"), result.get("ai_fix_reason"),
        result.get("reason"), assessment.get("fp_evidence"),
    ))
def _fp_rule_id_or_empty(value) -> str:
    rule_id = str_or(value).strip()
    return "" if not rule_id or rule_id.lower() == "unknown" else rule_id
def _fp_confirmed_rules(events: list, items: list,
                        proof_ctx: TerminalVerdictContext) -> set:
    rules = set()
    rule_by_fid = _rule_id_by_finding(events)
    for ev in _last_state_by_fid(events).values():
        if (ev.get("event") == "finding_resolved"
                and _resolution_word(ev.get("resolution")) == "fp_confirmed"
                and _fp_evidence_present(ev)):
            _rid = _fp_rule_id_or_empty(
                str_or(ev.get("rule_id"))
                or rule_by_fid.get(str_or(ev.get("finding_id")), ""))
            if _rid:
                rules.add(_rid)
    for item in items:
        if not (isinstance(item, dict)
                and _item_status(item) == "fp_confirmed"
                and _fp_evidence_present(item)):
            continue
        keys = _finding_keys({
            "locator": item.get("locator"),
            "file": item.get("file_path") or item.get("file"),
            "line": item.get("line"),
            "rule_id": item.get("rule_id"),
        })
        if _treatment_fix_proof(keys, proof_ctx):
            continue
        _rid = _fp_rule_id_or_empty(item.get("rule_id"))
        if _rid:
            rules.add(_rid)
    return rules
def _unproven_fp_closures(events: list, items: list,
                          proof_ctx: TerminalVerdictContext,
                          findings_all: list | None = None) -> list:
    out = []
    rule_by_fid = _rule_id_by_finding(events)
    for ev in _last_state_by_fid(events).values():
        if not (ev.get("event") == "finding_resolved"
                and _resolution_word(ev.get("resolution")) == "fp_confirmed"):
            continue
        has_evidence = _fp_evidence_present(ev)
        rule_id = (str_or(ev.get("rule_id"))
                   or rule_by_fid.get(str_or(ev.get("finding_id")), ""))
        if has_evidence and _fp_rule_id_or_empty(rule_id):
            continue
        kind = "fp_evidence_missing" if not has_evidence else "fp_rule_id_missing"
        reason = ("fp_confirmed 缺 rationale/fp_evidence，不得作为误报终态"
                  if not has_evidence else
                  "fp_confirmed 缺有效 rule_id（空/unknown），无法固化且不得放行")
        item = _residual_item(ev, kind, reason)
        if not item["rule_id"]:
            item["rule_id"] = rule_id
        out.append(item)
    for idx, item in enumerate(items):
        if not (isinstance(item, dict)
                and _item_status(item) == "fp_confirmed"):
            continue
        keys = _finding_keys({
            "locator": item.get("locator"),
            "file": item.get("file_path") or item.get("file"),
            "line": item.get("line"),
            "rule_id": item.get("rule_id"),
        })
        if _treatment_fix_proof(keys, proof_ctx):
            continue
        has_evidence = _fp_evidence_present(item)
        rule_id = str_or(item.get("rule_id"))
        if has_evidence and _fp_rule_id_or_empty(rule_id):
            continue
        kind = "fp_evidence_missing" if not has_evidence else "fp_rule_id_missing"
        reason = ("fp_confirmed 缺 fp_evidence/ai_fix_reason/reason，"
                  "不得固化规则或放行交付" if not has_evidence else
                  "fp_confirmed 缺有效 rule_id（空/unknown），无法固化且不得放行")
        out.append({
            "kind": kind,
            "index": idx,
            "finding_id": str_or(item.get("finding_id")),
            "rule_id": rule_id,
            "severity": _severity_key(item.get("severity")) or "unknown",
            "domain": str_or(item.get("domain")).strip() or "unknown",
            "file": str_or(item.get("file_path") or item.get("file")),
            "line": int_or(item.get("line"), 0),
            "resolution": str_or(item.get("status")),
            "reason": reason,
        })
    for finding in findings_all or []:
        if not isinstance(finding, dict):
            continue
        verdicts = _verdict_only_evidence(finding, proof_ctx)
        if (_VERDICT_FP not in verdicts or verdicts & _VERDICT_EXECUTED
                or _fp_rule_id_or_empty(finding.get("rule_id"))):
            continue
        out.append(_residual_item(
            finding, "fp_rule_id_missing",
            "AI 裁决 reject_as_fp 缺有效 rule_id（空/unknown），"
            "无法固化且不得放行"))
    return out
def _unfixated_fp_rules(skill_dir: str, events: list, items: list,
                        proof_ctx: TerminalVerdictContext,
                        verdict_rules: set | None = None) -> list:
    active, _fp_rule_errors = _load_fp_rules_snapshot(skill_dir)
    active_keys = {str_or(r) for r in active}
    confirmed = _fp_confirmed_rules(events, items, proof_ctx)
    confirmed |= set(verdict_rules or ())
    out = []
    for rid in sorted(confirmed):
        if rid in active_keys:
            continue
        try:
            static_fp = is_static_fp_rule(rid, skill_dir=skill_dir)
        except (OSError, ValueError, RuntimeError, RecursionError) as exc:
            log_swallowed(__name__, exc, context="_unfixated_fp_rules:static")
            static_fp = False
        if static_fp:
            continue
        out.append({
            "kind": "fp_not_fixated",
            "rule_id": rid,
            "reason": "以 fp_confirmed 收口，但规则未进 fp_rules.json 且不在"
                      "静态误报表——同一误报下一轮必然复现（延迟掩盖）",
        })
    return out
def _reappeared_fixed(events: list, cur: list, round_ts: str) -> list:
    seen_events = _latest_finding_seen(cur)
    if not seen_events:
        return []
    pending = {id(ev): ev for ev in seen_events}
    prior_fixes: dict[str, list] = {}
    reported: set = set()
    out = []
    def _report(seen_ev: dict) -> None:
        _fid = str_or(seen_ev.get("finding_id"))
        if not _fid or _fid in reported:
            return
        _seen_round = str_or(seen_ev.get("round_start_ts")) or round_ts
        for fix_ev in prior_fixes.get(_fid, []):
            _fix_round = str_or(fix_ev.get("round_start_ts")) or round_ts
            stage = ("同一轮" if _seen_round == _fix_round
                     else f"第 {_fix_round} 轮")
            reported.add(_fid)
            out.append(_residual_item(
                seen_ev, "fixed_but_reappeared",
                f"{stage}已声明 "
                f"{_resolution_word(fix_ev.get('resolution'))}，"
                "本轮同一 finding 再次出现：修复未触及根因或被回退"))
            return
    for ev in events:
        pending_ev = pending.pop(id(ev), None)
        if pending_ev is not None:
            _report(pending_ev)
            continue
        if ev.get("event") != "finding_resolved":
            continue
        if _resolution_word(ev.get("resolution")) not in FIXED_RESOLUTIONS:
            continue
        _fid = str_or(ev.get("finding_id"))
        if not _fid:
            continue
        prior_fixes.setdefault(_fid, []).append(ev)
    for seen_ev in pending.values():
        _report(seen_ev)
    return out
def _severity_coverage(findings: list, residual_ids: set) -> dict:
    ranks = [_severity_rank_of(f) for f in findings]
    ranks = [rank if rank is not None and rank < len(_SEVERITY_ORDER)
             else None for rank in ranks]
    identities = [finding_identity(f, occurrence=occurrence)
                  for occurrence, f in enumerate(findings)]
    cov = {}
    for severity in _SEVERITY_ORDER:
        target = SEVERITY_RANK[severity]
        indexes = [index for index, rank in enumerate(ranks)
                   if rank == target]
        cov[severity] = {
            "total": len(indexes),
            "residual": sum(1 for index in indexes
                            if identities[index] in residual_ids),
        }
    unknown = [index for index, rank in enumerate(ranks) if rank is None]
    cov["unknown"] = {
        "total": len(unknown),
        "residual": sum(1 for index in unknown
                        if identities[index] in residual_ids),
    }
    return cov
def _residual_actions(soft: list, fp_unfixated: list,
                      reappeared: list, unproven_fp: list | None = None) -> list:
    actions = []
    unproven_fp = unproven_fp or []
    missing_identity = [item for item in unproven_fp
                        if item.get("kind") == "fp_rule_id_missing"]
    missing_evidence = [item for item in unproven_fp
                        if item.get("kind") != "fp_rule_id_missing"]
    if missing_evidence:
        actions.append(
            f"fp_evidence_missing: {len(missing_evidence)} 项 fp_confirmed 缺审计证据"
            "——补逐项 rationale/fp_evidence 后重新审核；不得固化或放行")
    if missing_identity:
        actions.append(
            f"fp_rule_id_missing: {len(missing_identity)} 项误报终态缺有效 rule_id"
            "——补逐项规则身份后重新审核并固化；不得放行")
    if soft:
        actions.append(
            f"soft_closure: {len(soft)} 项以 reject/defer/suggestion 软销项"
            "——强口径不接受：改为真实修复（fixed/ai_fixed），"
            "或以 fp_confirmed 附 fp_evidence 固化误报规则"
            "（fixate_fp_rules），或改规则根除误报来源")
    if fp_unfixated:
        _rules = "、".join(sorted({str_or(f.get("rule_id"))
                                   for f in fp_unfixated})[:5])
        actions.append(f"fp_not_fixated: {len(fp_unfixated)} 条误报规则未固化"
                       f"（{_rules}）——fixate_fp_rules 写入 fp_rules.json，"
                       "或把规则从缺陷通道退役（RETIRED_RULE_IDS 附理由）")
    if reappeared:
        actions.append(f"fix_not_durable: {len(reappeared)} 项声明已修复"
                       "但本轮复现——重新定位根因修复并补回归锚定")
    return actions
def _residual_identity(item: dict) -> tuple:
    fid = str_or(item.get("finding_id"))
    if fid:
        return ("finding", fid)
    idx = item.get("index")
    if idx is not None:
        return (str_or(item.get("kind")), f"index:{idx}")
    return (str_or(item.get("kind")), str_or(item.get("rule_id")))
def _precision_items(payload: dict, key: str) -> list[dict]:
    raw = payload.get(key)
    if raw is None:
        return []
    if not isinstance(raw, (list, tuple)):
        logger.warning("[ZeroResidual] 精确证据门禁 %s 形态非 list/tuple"
                       "(%s)，按空清单处理", key, type(raw).__name__)
        return []
    items = [item for item in raw if isinstance(item, dict)]
    if len(items) != len(raw):
        logger.warning("[ZeroResidual] 精确证据门禁 %s 含 %d 条非映射元素，"
                       "已忽略", key, len(raw) - len(items))
    return items
def _project_history_events(events: list, project: str) -> list:
    """按项目 round_open 的轮次集合隔离共享台账历史。

    finding_seen/finding_resolved 的历史格式没有 project 字段，不能按事件
    自身字段直接过滤；轮次锚由其项目 round_open 声明，是可信归属边界。
    """
    wanted = str_or(project).strip()
    source = [ev for ev in as_list(events) if isinstance(ev, dict)]
    if not wanted:
        return source
    rounds = {
        str_or(ev.get("round_start_ts")).strip()
        for ev in source
        if ev.get("event") == "round_open"
        and str_or(ev.get("project")).strip() == wanted
        and str_or(ev.get("round_start_ts")).strip()
    }
    return [
        ev for ev in source
        if str_or(ev.get("round_start_ts")).strip() in rounds
        or str_or(ev.get("project")).strip() == wanted
    ]
def check_zero_residual(skill_dir: str) -> dict:
    sd = normalize_skill_dir(skill_dir)
    analysis = _analyze_zero_backlog(sd, _DEFAULT_ROUND_START_TS)
    backlog_report = analysis.report
    events = _project_history_events(
        analysis.events, path_scoped_namespace(sd))
    round_ts = (str_or(backlog_report.get("round_start_ts"))
                or current_round_ts(events, path_scoped_namespace(sd)))
    cur = analysis.cur
    findings_all = analysis.findings_all
    treatment_items = analysis.ctx.t_items
    treatment_ctx = analysis.ctx
    soft = (_soft_ledger_closures(events)
            + _soft_treatment_closures(treatment_items, treatment_ctx)
            + _soft_verdict_closures(findings_all, treatment_ctx))
    fp_unfixated = _unfixated_fp_rules(
        sd, events, treatment_items, treatment_ctx,
        _verdict_fp_rules(findings_all, treatment_ctx))
    reappeared = _reappeared_fixed(events, cur, round_ts)
    unproven_fp = _unproven_fp_closures(
        events, treatment_items, treatment_ctx, findings_all)
    precision = _precision_gate_guarded(sd)
    masked = _precision_items(precision, "masked_items")
    p0_semantic = _precision_items(precision, "p0_semantic_items")
    masked_count = max(len(masked),
                       int_or(precision.get("masked_count"), 0))
    p0_semantic_count = max(
        len(p0_semantic), int_or(precision.get("p0_semantic_count"), 0))
    backlog_ids = analysis.backlog_ids
    backlog_passed = _gate_passed(backlog_report)
    hard_backlog = int_or(backlog_report.get("backlog_count"), 0)
    soft_count = len(soft)
    backlog_residual_count = max(len(backlog_ids), max(0, hard_backlog))
    if not backlog_passed and not backlog_residual_count:
        backlog_residual_count = 1
    residual_count = (backlog_residual_count + len(soft) + len(fp_unfixated)
                      + len(reappeared) + len(unproven_fp) + masked_count
                      + p0_semantic_count)
    if precision.get("gate_error"):
        residual_count += 1
    residual_ids = set(backlog_ids)
    residual_ids |= {str_or(r.get("finding_id"))
                     for r in soft + reappeared + unproven_fp}
    residual_ids |= {str_or(r.get("finding_id")) for r in masked}
    residual_ids |= {str_or(r.get("finding_id")) for r in p0_semantic}
    residual_ids.discard("")
    precision_passed = precision.get("passed") is True
    precision_skipped = precision.get("skipped") is True
    passed = bool(
        backlog_passed
        and not soft_count
        and not fp_unfixated
        and not reappeared
        and not unproven_fp
        and precision_passed
        and not masked_count
        and not p0_semantic_count
    )
    actions = _residual_actions(
        soft, fp_unfixated, reappeared, unproven_fp)
    actions.extend(as_list(precision.get("actions_required")))
    if not backlog_passed:
        actions = list(backlog_report.get("actions_required") or []) + actions
    if passed:
        logger.info("[ZeroResidual] 强口径通过: %d 项 finding 全部证据终态",
                    len(findings_all))
    else:
        logger.warning("[ZeroResidual] 强口径阻塞: 软销项=%d, 误报未固化=%d, "
                       "修复复现=%d, 模糊销项=%d, P0语义销项=%d, 未终态=%d",
                       soft_count, len(fp_unfixated), len(reappeared),
                       masked_count, p0_semantic_count, hard_backlog)
    return {
        "passed": passed,
        "round_start_ts": round_ts,
        "total_findings": len(findings_all),
        "backlog_count": hard_backlog,
        "soft_closure_count": soft_count,
        "fp_unfixated_count": len(fp_unfixated),
        "fix_reappeared_count": len(reappeared),
        "fp_evidence_missing_count": len(unproven_fp),
        "precision_masked_count": masked_count,
        "p0_semantic_sweep_count": p0_semantic_count,
        "precision_evidence_gate": {
            "passed": precision_passed,
            "skipped": precision_skipped,
            "reason": str_or(precision.get("reason")),
        },
        "residual_count": residual_count,
        "severity_coverage": _severity_coverage(findings_all, residual_ids),
        "zero_backlog_gate": {
            "passed": backlog_passed,
            "backlog_by_domain": backlog_report.get("backlog_by_domain", {}),
            "backlog_by_severity": backlog_report.get("backlog_by_severity", {}),
            "p0_guard_passed": backlog_report.get("p0_guard_passed"),
            "fuzzy_terminal_guard_passed":
                backlog_report.get("fuzzy_terminal_guard_passed"),
        },
        "soft_closures": soft[:_RESIDUAL_PREVIEW],
        "soft_closures_truncated": max(0, soft_count - _RESIDUAL_PREVIEW),
        "fp_not_fixated": fp_unfixated[:_RESIDUAL_PREVIEW],
        "fix_reappeared": reappeared[:_RESIDUAL_PREVIEW],
        "fp_evidence_missing": unproven_fp[:_RESIDUAL_PREVIEW],
        "fp_evidence_missing_truncated": max(
            0, len(unproven_fp) - _RESIDUAL_PREVIEW),
        "precision_masked": masked[:_RESIDUAL_PREVIEW],
        "precision_masked_truncated": max(0, masked_count - len(masked)),
        "p0_semantic_sweep": p0_semantic[:_RESIDUAL_PREVIEW],
        "p0_semantic_truncated": max(
            0, p0_semantic_count - len(p0_semantic)),
        "actions_required": actions,
    }
def check_precision_gate(skill_dir: str) -> dict:
    sd = normalize_skill_dir(skill_dir)
    return _precision_gate_guarded(sd)
def check_memory_injection_gate(skill_dir: str) -> dict:
    sd = normalize_skill_dir(skill_dir)
    return _call_gate(
        check_memory_injection_quality, sd,
        count_key="memory_ops_count", label="复盘记忆注入质量门禁")
def _precision_payload_error(gate: dict) -> str:
    for items_key, count_key in (
            ("masked_items", "masked_count"),
            ("p0_semantic_items", "p0_semantic_count")):
        raw = gate.get(items_key)
        if not isinstance(raw, (list, tuple)):
            return f"{items_key} 必须是 list/tuple，实为 {type(raw).__name__}"
        dirty = sum(1 for item in raw if not isinstance(item, dict))
        if dirty:
            return f"{items_key} 含 {dirty} 条非映射元素"
        count = gate.get(count_key)
        if isinstance(count, bool) or not isinstance(count, int) or count < 0:
            return f"{count_key} 必须是非负整数，实为 {count!r}"
        if count < len(raw):
            return f"{count_key}={count} 小于 {items_key} 长度 {len(raw)}"
    return ""
def _precision_gate_guarded(sd: str) -> dict:
    try:
        gate = check_precision_evidence(sd)
        if not isinstance(gate, dict):
            raise TypeError(
                f"精确证据门禁返回非 dict: {type(gate).__name__}")
        if not isinstance(gate.get("passed"), bool):
            raise TypeError("精确证据门禁缺 passed 布尔终态")
        shape_error = _precision_payload_error(gate)
        if shape_error:
            raise TypeError(f"精确证据门禁返回形态非法: {shape_error}")
        return gate
    except Exception as exc:
        logger.exception("[ZeroResidual] 精确证据门禁执行异常，保守阻塞交付")
        return {
            "passed": False,
            "skipped": False,
            "reason": "precision_gate_error",
            "gate_error": f"{type(exc).__name__}: {exc}"[:500],
            "masked_count": 0,
            "p0_semantic_count": 0,
            "masked_items": [],
            "p0_semantic_items": [],
            "actions_required": [
                (f"precision_gate_error: 精确证据门禁执行异常"
                 f"（{str(exc)[:200]}）——修复异常后重跑，"
                 "异常不得当作放行信号"),
            ],
        }
_TRIGGER_LATE_PHASES = frozenset(
    {"code_feedback_done", "evolution_pending", "all_completed"})
_TRIGGER_FAILURE_STATUSES = frozenset({
    "ai_review_pending", "blocked", "early_stopped", "error", "failed",
    "max_batches_reached", "max_rounds_reached", "max_steps_reached",
    "stalled",
})
_RUNNING_RECORD_STALE_SECONDS = 4 * 60 * 60
def _trigger_record_path(sd: str) -> str:
    return os.path.join(get_temp_dir(sd), TRIGGER_ENFORCEMENT_FILENAME)
def _trigger_record_age_seconds(sd: str) -> float | None:
    try:
        return max(0.0, time.time() - os.path.getmtime(
            _trigger_record_path(sd)))
    except Exception as exc:
        log_swallowed(__name__, exc, context="_trigger_record_age_seconds")
        return None
def _read_trigger_enforcement_record(sd: str) -> tuple[dict, str]:
    try:
        path = _trigger_record_path(sd)
    except Exception as exc:
        logger.warning("[AutoEnhanceStep] 触发强制记录路径不可用，按阻断处理: %s", exc)
        return {}, f"触发强制记录路径不可用: {type(exc).__name__}: {exc}"[:300]
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as fh:
            data = json.load(fh)
    except FileNotFoundError:
        return {}, ""
    except (OSError, ValueError, TypeError, RecursionError) as exc:
        return {}, f"触发强制记录不可读: {exc}"
    if not isinstance(data, dict):
        return {}, f"触发强制记录形态非 dict: {type(data).__name__}"
    if not data:
        return {}, "触发强制记录形态非法: empty object"
    return data, ""
def _mandatory_hits_in_text(text: str) -> list[str]:
    lowered = text.lower()
    hits: list[str] = []
    for kw in MANDATORY_PIPELINE_TRIGGER_KEYWORDS:
        key = kw.lower()
        if not key:
            continue
        if key.isascii():
            if re.search(rf"(?<![a-z0-9_]){re.escape(key)}(?![a-z0-9_])",
                         lowered):
                hits.append(key)
        elif key in lowered:
            hits.append(key)
    return hits
def check_trigger_enforcement(skill_dir: str, text: str = "") -> dict:
    record, read_err = _read_trigger_enforcement_record(skill_dir)
    text_hits = (_mandatory_hits_in_text(text)
                 if isinstance(text, str) and text.strip() else [])
    base: dict = {
        "gate_id": "GATE-TRIGGER",
        "gate_name": "触发强制管线",
        "trigger_violation_count": 0,
        "mandatory_keywords": list(MANDATORY_PIPELINE_TRIGGER_KEYWORDS),
        "evidence": {"record": record},
        "failure_reasons": [],
        "actions_required": [],
    }
    if read_err:
        base.update(
            passed=False, status="FAIL", trigger_violation_count=1,
            failure_reasons=[read_err],
            actions_required=[
                "清理或重建 trigger_enforcement.json 后以全管线重跑",
            ],
        )
        return base
    if not record:
        if text_hits:
            base.update(
                passed=False, status="FAIL", trigger_violation_count=1,
                failure_reasons=[
                    f"本次话语强制词 {text_hits} 未留下触发执行记录",
                ],
                actions_required=[
                    ("以 run_pipeline_from_trigger(..., full=True) 执行并登记，"
                     "确认 phase=all_completed 后再交付"),
                ],
            )
            return base
        base.update(
            passed=True, status="SKIP", skipped=True,
            reason="无触发强制管线记录（非触发式运行，跳过门禁）",
        )
        return base
    reasons: list[str] = []
    if record.get("contract_passed") is not True:
        reasons.append(
            "触发记录 contract_passed!=true（入口词表契约未通过）")
    if record.get("executed") is not True:
        reasons.append("触发记录未标记 executed=true（入口未执行管线）")
    if record.get("full_pipeline") is not True:
        reasons.append(
            "触发记录 full_pipeline=false（单步推进不得交付）")
    status = as_str(record.get("status", "")).strip().lower()
    phase = as_str(record.get("phase", "")).strip().lower()
    recorded_hits = {as_str(hit).strip().lower()
                     for hit in normalize_list_field(
                         record.get("mandatory_hits"))}
    recorded_hits.discard("")
    missing_hits = sorted(set(text_hits) - recorded_hits)
    if missing_hits:
        reasons.append(f"本次话语强制词未进入触发记录: {missing_hits}")
    if text_hits:
        recorded_text_hash = as_str(
            record.get("text_sha256", "")).strip().lower()
        expected_text_hash = hashlib.sha256(text.encode("utf-8")).hexdigest()
        if not recorded_text_hash:
            reasons.append("触发记录缺本次话语文本哈希，无法排除复用旧执行证据")
        elif recorded_text_hash != expected_text_hash:
            reasons.append("本次话语与触发记录的文本哈希不一致，不得复用旧执行证据")
    if (status == "running" and record.get("full_pipeline") is True
            and record.get("executed") is True and not reasons):
        age = _trigger_record_age_seconds(skill_dir)
        if age is None:
            reasons.append("全管线执行中记录的心跳时间不可读，无法排除崩溃或记录丢失")
        elif age > _RUNNING_RECORD_STALE_SECONDS:
            reasons.append(
                f"全管线执行中记录已存活 {age / 60:.0f} 分钟，"
                f"超过心跳窗口 {_RUNNING_RECORD_STALE_SECONDS // 60} 分钟"
                "（进程可能已崩溃或被超时终止）")
        if reasons:
            base.update(
                passed=False, status="FAIL",
                trigger_violation_count=len(reasons),
                failure_reasons=reasons,
                actions_required=[
                    ("以 run_pipeline_from_trigger(..., full=True) 重跑，"
                     "确认 phase=all_completed 后再交付"),
                ],
            )
            return base
        base.update(
            passed=True, status="WARN",
            reason=("全管线执行中，6d 放行；终态必须达到 "
                    "phase=all_completed"),
        )
        return base
    if status in _TRIGGER_FAILURE_STATUSES:
        reasons.append(f"全管线未完成：status={status}")
    elif status != "completed":
        reasons.append(
            f"全管线终态状态未确认完成: status={status or 'unknown'}")
    if phase not in _TRIGGER_LATE_PHASES:
        reasons.append(
            f"阶段未达到 6c/6e/完成：phase={phase or 'unknown'}")
    if reasons:
        base.update(
            passed=False, status="FAIL",
            trigger_violation_count=len(reasons),
            failure_reasons=reasons,
            actions_required=[
                ("以 run_pipeline_from_trigger(..., full=True) 重跑，"
                 "确认 phase=all_completed 后再交付"),
            ],
        )
        return base
    base.update(
        passed=True, status="PASS",
        reason=f"触发强制管线已执行（status={status}, phase={phase}）",
    )
    return base
def _gate_passed(gate: dict) -> bool:
    if not isinstance(gate, dict):
        return False
    return gate.get("passed") is True
def check_method_reachability(skill_dir: str) -> dict:
    """ 0 号门禁：方法注册表可达性（注册即必须可执行）。

    历史缺陷：F 组挂在 TREATMENT_PHASE 上，而 all_method_ids 只遍历 PHASES，
    结果 F 注册齐备却永不进入 ``next_method``——完整管线静默跳过死代码检测，
    归零门禁反而因为「没有发现」而放行。本门禁把「注册了但不可达」变成硬阻断。
    """
    try:
        from jwsgj.xv_context_derivation import (
            check_method_registry_reachability,
        )
        report = check_method_registry_reachability()
    except Exception as exc:  # noqa: BLE001 — 门禁异常保守阻塞
        logger.exception(
            "[AutoEnhanceStep] 方法可达性门禁执行异常，保守阻塞交付")
        return {"passed": False, "gate_error": str(exc)[:500],
                "unreachable_count": -1,
                "failure_reasons": [f"方法可达性门禁执行异常: {exc}"],
                "actions_required": ["修复方法注册表导入链后重跑"]}
    if not isinstance(report, dict):
        return {"passed": False,
                "gate_error": (f"方法可达性守卫返回非 dict: "
                               f"{type(report).__name__}"),
                "unreachable_count": -1,
                "failure_reasons": ["方法可达性守卫返回形态非法"],
                "actions_required": ["修复守卫返回值后重跑"]}
    ok = report.get("ok") is True
    issues = [str(item) for item in (report.get("issues") or [])]
    return {
        "passed": ok,
        "unreachable_count": (0 if ok else max(1, len(issues))),
        "methods": list(report.get("methods") or []),
        "failure_reasons": issues,
        "actions_required": [str(item) for item in
                              (report.get("actions_required") or [])],
    }
def _call_gate(check_fn, sd, *, count_key: str, label: str) -> dict:
    try:
        gate = check_fn(sd)
        if not isinstance(gate, dict):
            raise TypeError(f"{label}返回非 dict: {type(gate).__name__}")
    except Exception as exc:
        logger.exception("[AutoEnhanceStep] %s执行异常，保守阻塞交付", label)
        return {"passed": False, "gate_error": str(exc)[:500],
                count_key: -1,
                "actions_required": [f"{label}执行异常——人工排查后重跑"]}
    return gate
def _zero_backlog_block_route(gate: dict) -> tuple[str, str]:
    if gate.get("gate_error"):
        return "backlog_blocked", "fix_zero_backlog_gate_error"
    fp_audit = dict_or_empty(gate.get("fp_mask_audit"))
    if fp_audit.get("gate_error"):
        return "backlog_blocked", "fix_zero_backlog_gate_error"
    if fp_audit.get("ledger_errors") or fp_audit.get("fp_rule_errors"):
        return "backlog_blocked", "repair_ledger_and_fp_rules"
    if (int_or(fp_audit.get("unreviewed"), 0) > 0
            or as_list(fp_audit.get("fp_sampled_unreviewed"))):
        return "backlog_blocked", "review_suppressed_findings"
    guards_failed = any(gate.get(key) is False for key in (
        "fuzzy_terminal_guard_passed", "p0_guard_passed",
        "treatment_guard_passed", "cv_channel_guard_passed"))
    fanout = dict_or_empty(gate.get("fanout"))
    if (fanout.get("passed") is False
            and int_or(gate.get("backlog_count"), 0) <= 0
            and not gate.get("ledger_missing")
            and not guards_failed):
        return "fanout_blocked", "handle_fanout_residual"
    if gate.get("ledger_missing"):
        return "backlog_blocked", "register_round_and_resolve_backlog"
    return "backlog_blocked", "resolve_backlog_items"
def _validate_pending_reviews(agg: Any) -> tuple[dict, int, str]:
    if not isinstance(agg, dict):
        return {}, 0, f"待审核清单返回非 dict: {type(agg).__name__}"
    raw_pending = agg.get("pending_ai_review")
    pending = (None if raw_pending is None
               else count_tasks(raw_pending, clamp_negative=False))
    if pending is not None:
        try:
            if not float(raw_pending).is_integer():
                pending = None
        except (TypeError, ValueError, OverflowError):
            pending = None
    if pending is None:
        return {}, 0, f"待审核清单计数非法: {raw_pending!r}"
    raw_reviews = agg.get("reviews")
    if not isinstance(raw_reviews, list):
        return {}, 0, (f"待审核清单 reviews 须为 list: "
                       f"{type(raw_reviews).__name__}")
    reviews = raw_reviews
    if pending != len(reviews):
        return {}, 0, (f"待审核清单计数与 reviews 数量不一致: "
                       f"pending_ai_review={pending}, reviews={len(reviews)}")
    dirty = sum(1 for item in reviews if not isinstance(item, dict))
    if dirty:
        return {}, 0, f"reviews 含 {dirty} 条非映射元素"
    normalized = dict(agg)
    normalized["pending_ai_review"] = pending
    normalized["reviews"] = reviews
    return normalized, pending, ""
def pending_delivery_reviews(skill_dir: str, list_pending=None) -> dict:
    if list_pending is None:
        logger.warning("[AutoEnhanceStep] 待审核清单读取器未注入，停留待重试")
        return {"status": "unreadable", "pending": None, "reviews": [],
                "error": ("阶段6d 待审核清单读取器未注入（待审核裁决须由编排层"
                          "注入 list_pending_ai_reviews，门禁域不反向依赖编排域）")}
    try:
        aggregate = list_pending(skill_dir)
        if not isinstance(aggregate, dict):
            raise TypeError(
                f"待审核清单返回非 dict: {type(aggregate).__name__}")
    except Exception as exc:
        logger.warning("[AutoEnhanceStep] 待审核清单读取失败，停留待重试: %s",
                       exc, exc_info=True)
        return {"status": "unreadable", "pending": None, "reviews": [],
                "error": f"阶段6d 待审核清单读取失败: {str(exc)[:400]}"}
    normalized, pending, validation_error = _validate_pending_reviews(aggregate)
    if validation_error:
        raw_reviews = aggregate.get("reviews")
        reviews = raw_reviews if isinstance(raw_reviews, list) else []
        logger.warning("[AutoEnhanceStep] 待审核清单校验失败，停留待重试: %s",
                       validation_error)
        return {"status": "invalid", "pending": None, "reviews": reviews,
                "error": f"阶段6d {validation_error}"}
    reviews = normalized["reviews"]
    if pending == 0:
        return {"status": "clear", "pending": 0, "reviews": [],
                "error": ""}
    return {"status": "pending", "pending": pending, "reviews": reviews,
            "error": ""}
_GATE_OUTPUT_KEYS = (
    "method_reachability_gate", "zero_backlog_gate", "zero_residual_gate",
    "diagnosis_coverage_gate", "stage_pair_gate", "memory_injection_gate",
    "false_negative_gate", "precision_trend_gate", "trigger_enforcement_gate",
)
_DELIVERY_BLOCKED_STATUSES = frozenset({
    "method_reachability_blocked", "diagnosis_coverage_blocked",
    "backlog_blocked", "fanout_blocked", "residual_blocked",
    "stage_pair_blocked", "memory_injection_blocked",
    "false_negative_blocked", "precision_trend_blocked", "trigger_blocked",
})
def apply_delivery_gates(sd, out: dict) -> bool:
    for _key in _GATE_OUTPUT_KEYS:
        out.pop(_key, None)
    # 0 号门禁：方法可达性。注册齐备却枚举不到的引擎会被完整管线静默跳过，
    # 归零门禁反而因为「没有发现」而放行，必须在其他门禁前先卡住。
    _reach_gate = _call_gate(
        check_method_reachability, sd,
        count_key="unreachable_count", label="方法可达性门禁")
    out["method_reachability_gate"] = _reach_gate
    if not _gate_passed(_reach_gate):
        out["status"] = "method_reachability_blocked"
        out["next_action"] = "fix_method_registry_reachability"
        logger.error(
            "[AutoEnhanceStep] 方法可达性门禁阻塞交付: %s——%s",
            "；".join(_reach_gate.get("failure_reasons") or []),
            "；".join(_reach_gate.get("actions_required") or []))
        return False
    _zb_gate = _call_gate(check_zero_backlog, sd,
                          count_key="backlog_count", label="归零门禁")
    out["zero_backlog_gate"] = _zb_gate
    _residual_gate = _call_gate(check_zero_residual, sd,
                                count_key="residual_count",
                                label="零残留守卫")
    out["zero_residual_gate"] = _residual_gate
    if not _gate_passed(_zb_gate):
        out["status"], out["next_action"] = _zero_backlog_block_route(
            _zb_gate)
        _gate_error = _zb_gate.get("gate_error")
        if _gate_error:
            logger.error(
                "[AutoEnhanceStep] 归零门禁执行异常，保守阻塞交付: %s"
                "——修复门禁异常后重跑（backlog_count=-1 为异常哨兵，"
                "非未终态计数）", _gate_error)
        elif _zb_gate.get("ledger_missing"):
            logger.error(
                "[AutoEnhanceStep] 归零门禁阻塞交付: 管线当前轮未在台账登记"
                "（ledger_missing）——重跑诊断聚合补 round_open 后重试"
                "（register_cv_findings_snapshot）")
        else:
            logger.warning(
                "[AutoEnhanceStep] 归零门禁阻塞交付: %s 项未终态 "
                "(按域=%s, 按级别=%s, 按阶段=%s)——逐项处置后重跑",
                _zb_gate.get("backlog_count", 0),
                _zb_gate.get("backlog_by_domain", {}),
                _zb_gate.get("backlog_by_severity", {}),
                _zb_gate.get("backlog_by_stage", {}))
        return False
    if not _gate_passed(_residual_gate):
        out["status"] = "residual_blocked"
        out["next_action"] = (
            "fix_zero_residual_gate_error"
            if _residual_gate.get("gate_error")
            else "provide_fp_evidence_and_review"
            if int_or(_residual_gate.get("fp_evidence_missing_count"), 0) > 0
            else "close_soft_closures_and_fp_fixation")
        logger.warning(
            "[AutoEnhanceStep] 零残留守卫阻塞交付: 软销项=%s, 误报未固化=%s, "
            "修复复现=%s, 缺误报证据=%s, 模糊销项=%s, P0语义销项=%s——"
            "按 actions_required 逐项处置后重跑",
            _residual_gate.get("soft_closure_count"),
            _residual_gate.get("fp_unfixated_count"),
            _residual_gate.get("fix_reappeared_count"),
            _residual_gate.get("fp_evidence_missing_count"),
            _residual_gate.get("precision_masked_count"),
            _residual_gate.get("p0_semantic_sweep_count"))
        return False
    # 诊断全量入账门禁：其余门禁只看台账里的 finding，若诊断结果在聚合/
    # 交叉验证阶段被静默丢弃，就永远不会进入任何统计。本道反向比对诊断
    # 阶段报告与台账，全严重度（P0–P3）缺一即阻断，堵住「没入账=没发现」。
    _coverage_gate = _call_gate(
        check_diagnosis_ledger_coverage, sd,
        count_key="masked_count", label="诊断全量入账门禁")
    out["diagnosis_coverage_gate"] = _coverage_gate
    if not _gate_passed(_coverage_gate):
        out["status"] = "diagnosis_coverage_blocked"
        out["next_action"] = "register_diagnosis_findings"
        logger.warning(
            "[AutoEnhanceStep] 诊断全量入账门禁阻塞交付: 未入账=%s "
            "（诊断 %s 条 / 台账 %s 条）——%s",
            _coverage_gate.get("masked_count"),
            _coverage_gate.get("diagnosis_findings"),
            _coverage_gate.get("ledger_findings"),
            "；".join(_coverage_gate.get("actions_required") or []))
        return False
    _stage_pair_gate = _call_gate(
        check_stage_pair_integrity, sd,
        count_key="pair_violation_count", label="阶段报告配对门禁")
    out["stage_pair_gate"] = _stage_pair_gate
    if not _gate_passed(_stage_pair_gate):
        out["status"] = "stage_pair_blocked"
        out["next_action"] = "repair_stage_pairs"
        logger.warning(
            "[AutoEnhanceStep] 阶段报告配对门禁阻塞交付: 缺JSON=%s, "
            "不一致=%s, 结构非法=%s, 孤儿快照=%s——%s",
            _stage_pair_gate.get("missing_count"),
            _stage_pair_gate.get("mismatch_count"),
            _stage_pair_gate.get("invalid_count"),
            _stage_pair_gate.get("orphan_json_count"),
            "；".join(_stage_pair_gate.get("actions_required") or []))
        return False
    _memory_gate = _call_gate(
        check_memory_injection_quality, sd,
        count_key="memory_ops_count", label="复盘记忆注入质量门禁")
    out["memory_injection_gate"] = _memory_gate
    if not _gate_passed(_memory_gate):
        out["status"] = "memory_injection_blocked"
        out["next_action"] = "record_review_memory_injection"
        logger.warning(
            "[AutoEnhanceStep] 复盘记忆注入质量门禁阻塞交付: %s——%s",
            "；".join(_memory_gate.get("failure_reasons") or []),
            "；".join(_memory_gate.get("actions_required") or []))
        return False
    # 漏报探针门禁：与精确证据门禁互为补角。精确门禁防「假阳性被当终态
    # 放行」，本门禁防「真实缺陷根本没 finding 可放行」——findings 为空时
    # 下游所有门禁都会通过，漏报因此最隐蔽。首轮只记基线，第二轮起按阈值
    # 阻断（probe_history 为空时中性跳过）。
    _fn_gate = _call_gate(
        check_false_negative_probe, sd,
        count_key="survived_count", label="漏报探针门禁")
    out["false_negative_gate"] = _fn_gate
    if not _gate_passed(_fn_gate):
        out["status"] = "false_negative_blocked"
        out["next_action"] = "fix_false_negative_leak"
        logger.warning(
            "[AutoEnhanceStep] 漏报探针门禁阻塞交付: 漏报率 %s（%s/%s）——%s",
            _fn_gate.get("fn_rate", 0.0),
            _fn_gate.get("survived_count", 0),
            _fn_gate.get("templates", 0),
            "；".join(_fn_gate.get("actions_required") or []))
        return False
    # 精度趋势门禁：前两道看快照（误报率/漏报率），本道看方向。连续退步
    # 说明反哺在反向生效（越治越差），必须停下来定位根因，不能继续漂移。
    _trend_gate = _call_gate(
        check_precision_trend, sd,
        count_key="trend_worsening_rounds", label="精度趋势门禁")
    out["precision_trend_gate"] = _trend_gate
    if not _gate_passed(_trend_gate):
        out["status"] = "precision_trend_blocked"
        out["next_action"] = "stop_and_fix_precision_regression"
        logger.warning(
            "[AutoEnhanceStep] 精度趋势门禁阻塞交付: %s +%.1f%%——%s",
            _trend_gate.get("worst_metric") or "unknown",
            float(_trend_gate.get("delta") or 0.0) * 100,
            "；".join(_trend_gate.get("actions_required") or []))
        return False
    _trigger_gate = _call_gate(
        check_trigger_enforcement, sd,
        count_key="trigger_violation_count", label="触发强制管线门禁")
    out["trigger_enforcement_gate"] = _trigger_gate
    if not _gate_passed(_trigger_gate):
        out["status"] = "trigger_blocked"
        out["next_action"] = "run_full_pipeline_from_trigger"
        logger.warning(
            "[AutoEnhanceStep] 触发强制管线门禁阻塞交付: %s——%s",
            "；".join(_trigger_gate.get("failure_reasons") or []),
            "；".join(_trigger_gate.get("actions_required") or []))
        return False
    if out.get("status") in _DELIVERY_BLOCKED_STATUSES:
        out["status"] = "completed"
        out.pop("next_action", None)
    return True
DEFAULT_MIN_COUNT = 3
def _normalize_min_count(min_count) -> int:
    parsed = min_count
    if isinstance(parsed, str):
        try:
            parsed = float(parsed.strip())
        except (TypeError, ValueError):
            parsed = None
    is_count = (isinstance(parsed, (int, float))
                and not isinstance(parsed, bool)
                and (not isinstance(parsed, float)
                     or (math.isfinite(parsed) and parsed.is_integer())))
    if not is_count or parsed < 1:
        if min_count is not None and min_count != DEFAULT_MIN_COUNT:
            logger.warning("fixate_fp_rules: min_count=%r 非法（须为 >=1 "
                           "的整数），按默认 %d", min_count,
                           DEFAULT_MIN_COUNT)
        parsed = DEFAULT_MIN_COUNT
    return int(parsed)
def _normalize_items(skill_dir: str, items) -> list:
    if items is None:
        return load_treatment_items(skill_dir)
    if isinstance(items, (list, tuple)):
        return list(items)
    normalized = normalize_list_field(items)
    logger.warning("fixate_fp_rules: items 形态非 list/tuple（%s），按可迭代"
                   "归一 %d 条", type(items).__name__, len(normalized))
    return normalized
def _append_sample(samples: list, value: str, limit: int) -> None:
    if value and len(samples) < limit and value not in samples:
        samples.append(value)
def _text_samples(raw, limit: int) -> list[str]:
    if not isinstance(raw, (list, tuple)):
        return []
    out: list[str] = []
    for value in raw:
        text = str_or(value)
        if text and text not in out:
            out.append(text)
        if len(out) >= limit:
            break
    return out
_FP_KEY_LIMIT = 500
def _ordered_fp_keys(raw) -> list[str]:
    if not isinstance(raw, (list, tuple, set, frozenset)):
        return []
    ledger: list[str] = []
    seen: set[str] = set()
    for value in raw:
        key = as_str(value)
        if key and key not in seen:
            seen.add(key)
            ledger.append(key)
    return ledger
def _merge_fp_key_ledger(prev_ledger: list[str], new_raw) -> list[str]:
    if not isinstance(new_raw, (list, tuple, set, frozenset)):
        return prev_ledger[-_FP_KEY_LIMIT:]
    return _ordered_fp_keys([*prev_ledger, *new_raw])[-_FP_KEY_LIMIT:]
def _merge_fp_item_into_entry(entry: dict, it: dict, result: dict) -> None:
    reason = as_str(result.get("reason", ""))
    sev = normalize_item_severity(it.get("severity"))
    identity = fp_item_identity(it)
    entry["count"] += 1
    entry.setdefault("identities", []).append(identity)
    counts = entry.setdefault("identity_counts", {})
    counts[identity] = counts.get(identity, 0) + 1
    entry.setdefault("identity_severities", {})[identity] = sev
    if reason:
        entry["reasons"].add(reason)
    entry["severities"][sev] = entry["severities"].get(sev, 0) + 1
    _append_sample(entry["sample_files"],
                   as_str(it.get("file_path", "")), 10)
    msg = (as_str(it.get("message", ""))
           or as_str(result.get("reason", "")))
    _append_sample(entry["sample_messages"], msg, 3)
def _aggregate_fp_by_rule(fp: list) -> dict:
    agg: dict = {}
    for rid, it in iter_unique_rule_observations(fp):
        raw_result = it.get("result")
        result = raw_result if isinstance(raw_result, dict) else {}
        entry = agg.setdefault(
            rid,
            {"count": 0, "reasons": set(), "severities": {},
             "sample_files": [], "sample_messages": [], "identities": [],
             "identity_counts": {}, "identity_severities": {}},
        )
        _merge_fp_item_into_entry(entry, it, result)
    return agg
def _count_items_per_rule(items: list) -> dict:
    items_per_rule: dict[str, int] = {}
    for rid, _it in iter_unique_rule_observations(items):
        items_per_rule[rid] = items_per_rule.get(rid, 0) + 1
    return items_per_rule
def _clamp_rate(value) -> float:
    return min(1.0, max(0.0, as_num(value)))
def _tracker_fp_rate(rule_id: str, tracker_cache: dict):
    entry = tracker_cache.get(rule_id, {}) if tracker_cache else {}
    if not isinstance(entry, dict) or as_num(entry.get("total", 0)) <= 0:
        return None
    rate = safe_float(entry.get("fp_rate"), None)
    return None if rate is None else _clamp_rate(rate)
def _resolve_rule_fp_rate(rule_id: str, fp_count: int, items_for_rule: int,
                          tracker_cache: dict) -> float:
    fp_rate = (round(fp_count / items_for_rule, 3)
               if items_for_rule > 0 else 0.0)
    override = _tracker_fp_rate(rule_id, tracker_cache)
    return fp_rate if override is None else override
def _merge_severity_counts(base, extra) -> dict:
    merged: dict = {}
    for source in (base, extra):
        if not isinstance(source, dict):
            continue
        for sev_k, sev_n in source.items():
            key = normalize_item_severity(sev_k)
            merged[key] = (max(0, int(as_num(merged.get(key, 0))))
                           + max(0, int(as_num(sev_n))))
    return merged
def _merge_fixated_entry(prev, e: dict, fp_rate: float, now: str) -> dict:
    if not isinstance(prev, dict):
        prev = {}
    prev_count = max(0, int(as_num(prev.get("count", 0))))
    prev_ledger = _ordered_fp_keys(prev.get("_fp_keys"))
    prev_keys = set(prev_ledger)
    prev_has_ledger = isinstance(
        prev.get("_fp_keys"), (list, tuple, set, frozenset))
    e_keys_raw = e.get("identities")
    has_identity = e_keys_raw is not None
    merged_keys = None
    add_evidence = True
    new_sev_counts = None
    if has_identity:
        e_keys = set(_ordered_fp_keys(e_keys_raw))
        merged_keys = _merge_fp_key_ledger(prev_ledger, e_keys_raw)
        if prev_has_ledger:
            new_keys = e_keys - prev_keys
            id_counts = e.get("identity_counts")
            id_sevs = e.get("identity_severities")
            added_count = 0
            new_sev_counts = {}
            for key in new_keys:
                count = 1
                if isinstance(id_counts, dict):
                    count = max(1, int(as_num(id_counts.get(key, 1))))
                severity = "P3"
                if isinstance(id_sevs, dict):
                    severity = normalize_item_severity(id_sevs.get(key))
                added_count += count
                new_sev_counts[severity] = (
                    new_sev_counts.get(severity, 0) + count)
            add_evidence = added_count > 0
            total = prev_count + added_count
        else:
            total = prev_count + e["count"]
    else:
        total = prev_count + e["count"]
    if add_evidence:
        prev_reasons = set(_ordered_fp_keys(prev.get("reasons", [])))
        prev_reasons.update(e["reasons"])
        prev_sevs = _merge_severity_counts(
            prev.get("severities"),
            new_sev_counts if new_sev_counts is not None else e["severities"])
        sample_files = _text_samples(
            _text_samples(prev.get("sample_files"), 10)
            + _text_samples(e.get("sample_files"), 10), 10)
        sample_messages = _text_samples(
            _text_samples(prev.get("sample_messages"), 3)
            + _text_samples(e.get("sample_messages"), 3), 3)
    else:
        prev_reasons = set(_ordered_fp_keys(prev.get("reasons", [])))
        prev_sevs = _merge_severity_counts(prev.get("severities"), {})
        sample_files = _text_samples(prev.get("sample_files"), 10)
        sample_messages = _text_samples(prev.get("sample_messages"), 3)
    confidence = round(min(0.95, 0.5 + max(0, total) / 50.0), 3)
    merged = {
        "count": total,
        "first_seen": as_str(prev.get("first_seen")) or now,
        "last_seen": now,
        "reasons": sorted(prev_reasons),
        "severities": prev_sevs,
        "sample_files": sample_files,
        "sample_messages": sample_messages,
        "confidence": confidence,
        "fp_rate": fp_rate,
    }
    if merged_keys is not None:
        merged["_fp_keys"] = merged_keys
    return merged
def _fp_confirmed_items(items: list) -> list:
    out: list = []
    invalid = 0
    missing_evidence = 0
    for item in items:
        if not isinstance(item, dict) or _item_status(item) != "fp_confirmed":
            continue
        rule_id = _fp_rule_id_or_empty(item.get("rule_id"))
        if not rule_id:
            invalid += 1
            continue
        if not _fp_evidence_present(item):
            missing_evidence += 1
            continue
        out.append(item)
    if invalid:
        logger.warning("[FpRuleBank] %d 条 fp_confirmed 治疗项缺有效 "
                       "rule_id（空/unknown），已跳过固化", invalid)
    if missing_evidence:
        logger.warning("[FpRuleBank] %d 条 fp_confirmed 治疗项缺审计证据，"
                       "已跳过固化", missing_evidence)
    return out
def _record_reviewed_fp_samples(skill_dir: str,
                               fixated: list) -> int:
    """将复核通过的误报规则回写为阈值学习的可信负样本。

    CV 的自动抑制（rule4 安全阀）没有复核前置，不能直接当负样本；只有
    ``fixate_fp_rules`` 在 ``audit_fp_mask`` 通过后固化的规则才是“确认
    误报”。这里回写负样本，让阈值随复核结果上升（减少误报），而不是随
    自动抑制漂移；学习链路不可用时只告警，不影响固化本身。
    """
    if not fixated:
        return 0
    try:
        from jwsgj.xv_threshold_learning import (
            record_threshold_outcome,
            set_threshold_learning_dir,
        )
    except Exception:  # noqa: BLE001 — 学习链路不可用不影响固化
        logger.warning("[FpRuleBank] 阈值学习模块不可用，跳过负样本回写")
        return 0
    try:
        set_threshold_learning_dir(skill_dir)
    except Exception as exc:  # noqa: BLE001 — 目录切换失败时继续内存学习
        logger.warning("[FpRuleBank] 阈值学习目录切换失败（继续内存模式）: %s", exc)
    recorded = 0
    for rid in fixated:
        try:
            record_threshold_outcome(
                rid, confirmed=False, was_false_positive=True)
            recorded += 1
        except Exception as exc:  # noqa: BLE001 — 单条失败不连坐
            logger.warning("[FpRuleBank] 负样本回写失败 %s: %s", rid, exc)
    return recorded


def fixate_fp_rules(skill_dir: str, items: list | None = None,
                    min_count: int = DEFAULT_MIN_COUNT) -> dict:
    blocked = _audit_fp_mask_guarded(skill_dir)
    if blocked.get("passed") is not True:
        blocked_report = _blocked_fixation_report(blocked)
        logger.warning(
            "[FpRuleBank] 误报规则固化被归零门禁阻断: %s（未写规则库）",
            "；".join(fp_mask_actions(blocked_report["fp_mask_audit"]))
            or "未复核项计数缺失（审计视图不含阻断源）")
        return {
            "fixated": [],
            "total_fp": 0,
            "blocked_by_zero_gate": True,
            "fp_mask_unreviewed": blocked.get("unreviewed", 0),
            "fp_mask_total_suppressed": blocked.get("total_suppressed", 0),
            "fp_mask_audit": blocked_report["fp_mask_audit"],
            "next_action": blocked_report["next_action"],
        }
    min_count = _normalize_min_count(min_count)
    items = _normalize_items(skill_dir, items)
    fp = _fp_confirmed_items(items)
    if not fp:
        return {"fixated": [], "total_fp": 0,
                "rules_count": len(get_fp_rule_ids(skill_dir))}
    agg = _aggregate_fp_by_rule(fp)
    data = load_fp_rules(skill_dir)
    rules = rules_of(data)
    data["rules"] = rules
    now = now_iso()
    try:
        tracker_cache = load_fp_tracker_rates(skill_dir)
    except (OSError, ValueError, TypeError, RecursionError) as exc:
        log_swallowed(__name__, exc, context="fixate_fp_rules:tracker_rates")
        tracker_cache = {}
    items_per_rule = _count_items_per_rule(items)
    fixated: list = []
    new_evidence_rules: list = []
    for rid, e in agg.items():
        if e["count"] < min_count:
            continue
        fp_rate = _resolve_rule_fp_rate(
            rid, e["count"], items_per_rule.get(rid, 0), tracker_cache)
        previous = rules.get(rid, {})
        previous_count = (max(0, int(as_num(previous.get("count", 0))))
                          if isinstance(previous, dict) else 0)
        merged = _merge_fixated_entry(previous, e, fp_rate, now)
        rules[rid] = merged
        fixated.append(rid)
        if merged["count"] > previous_count:
            new_evidence_rules.append(rid)
    save_fp_rules(skill_dir, data)
    # 规则库按身份幂等合并，学习样本也只能消费真正新增的证据。
    _recorded = _record_reviewed_fp_samples(skill_dir, new_evidence_rules)
    logger.info("[FpRuleBank] 固化 %d 条误报规则 (total_fp=%d, 规则库=%d, "
                "负样本回写=%d)",
                len(fixated), len(fp), len(rules), _recorded)
    return {"fixated": fixated, "total_fp": len(fp),
            "rules_count": len(rules), "negative_samples_recorded": _recorded}
_FIXATION_REVIEW_METHOD = (
    "逐项复核被抑制 findings（resolve_backlog_item："
    "误报确认 suppressed_reviewed / 真实问题转修复）")
_FIXATION_REVIEW_NEXT_ACTION = (
    f"{_FIXATION_REVIEW_METHOD}，audit_fp_mask 通过后重跑本步骤固化")
_FIXATION_AUDIT_ERROR_NEXT_ACTION = (
    "误报掩盖审计执行异常（并非复核未通过）——修复 audit_fp_mask 异常"
    "后重跑本步骤；unreviewed=-1 为异常哨兵，不得当作待复核条数")
_FIXATION_AUDIT_SAMPLE_KEYS = (
    "fp_sampled_rules", "fp_sampled_count", "fp_sampled_reviewed",
    "fp_sampled_unreviewed", "fp_sample_passed")
def _fixation_next_action(audit_view: dict) -> str:
    actions = fp_mask_actions(audit_view)
    if not actions:
        return _FIXATION_REVIEW_NEXT_ACTION
    steps = ([_FIXATION_REVIEW_METHOD]
             if int_or(audit_view.get("unreviewed"), 0) > 0 else [])
    return "；".join([*steps, *actions, "复核完成后重跑本步骤固化"])
def _blocked_fixation_report(fp_mask_audit: dict) -> dict:
    audit_view = {
        "unreviewed": fp_mask_audit.get("unreviewed", 0),
        "total_suppressed": fp_mask_audit.get("total_suppressed", 0),
        "per_rule_suppressed": fp_mask_audit.get("per_rule_suppressed", {}),
        "ledger_errors": list(fp_mask_audit.get("ledger_errors") or []),
        "fp_rule_errors": list(fp_mask_audit.get("fp_rule_errors") or []),
    }
    for _key in _FIXATION_AUDIT_SAMPLE_KEYS:
        if _key in fp_mask_audit:
            audit_view[_key] = fp_mask_audit[_key]
    gate_error = fp_mask_audit.get("gate_error")
    if gate_error:
        audit_view["gate_error"] = str(gate_error)[:300]
        next_action = _FIXATION_AUDIT_ERROR_NEXT_ACTION
    else:
        next_action = _fixation_next_action(audit_view)
    return {
        "fixated": [],
        "total_fp": 0,
        "rules_count": 0,
        "blocked_by_zero_gate": True,
        "fp_mask_audit": audit_view,
        "next_action": next_action,
    }
def _audit_fp_mask_guarded(skill_dir: str) -> dict:
    try:
        audit = audit_fp_mask(skill_dir)
    except Exception as _afm_e:
        logger.exception("[Stage6c] 误报掩盖审计执行异常，保守阻断固化")
        return {"passed": False, "gate_error": str(_afm_e)[:300],
                "unreviewed": -1, "total_suppressed": -1}
    if not isinstance(audit, dict) or not isinstance(audit.get("passed"), bool):
        shape = type(audit).__name__
        logger.error("[Stage6c] 误报掩盖审计返回形态非法(%s)，保守阻断固化", shape)
        return {"passed": False,
                "gate_error": f"invalid audit result: {shape}",
                "unreviewed": -1, "total_suppressed": -1}
    return audit
def _fixate_fp_rules_report(skill_dir: str) -> dict:
    try:
        _fp_result = require_dict(
            fixate_fp_rules(skill_dir), "误报固化结果")
    except Exception as fp_e:
        logger.warning("[Stage6c] 误报规则固化异常: %s", fp_e, exc_info=True)
        return {
            "fixated": [],
            "total_fp": 0,
            "rules_count": 0,
            "status": "error",
            "error": f"{type(fp_e).__name__}: {fp_e}"[:500],
            "next_action": "修复误报规则固化异常后重跑本步骤",
        }
    if _fp_result.get("blocked_by_zero_gate"):
        report = dict(_fp_result)
        report.setdefault("rules_count", 0)
        report["status"] = "blocked_by_zero_gate"
        return report
    logger.info("[Stage6c] 误报规则固化: %d条 (total_fp=%d, 规则库=%d，"
                "掩盖审计已通过)",
                len(_fp_result.get("fixated", [])),
                _fp_result.get("total_fp", 0),
                _fp_result.get("rules_count", 0))
    return {
        "fixated": _fp_result.get("fixated", []),
        "total_fp": _fp_result.get("total_fp", 0),
        "rules_count": _fp_result.get("rules_count", 0),
        "fp_mask_audit_passed": True,
    }
def _log_fixation_blocked(fp_mask_audit: dict) -> None:
    gate_error = fp_mask_audit.get("gate_error")
    if gate_error:
        logger.error(
            "[Stage6c] 误报掩盖审计执行异常，误报规则固化保守阻断: %s"
            "——修复审计异常后重跑本步骤（unreviewed=-1 为异常哨兵，非复核计数）",
            gate_error)
        return
    actions = fp_mask_actions(fp_mask_audit)
    logger.warning(
        "[Stage6c] 误报规则固化被归零门禁阻断: %s"
        "——先复核后固化，防未确认问题被规则库永久掩盖",
        "；".join(actions) or "未复核项计数缺失（审计视图不含阻断源）")
def run_fp_fixation_step(skill_dir: str, result: dict) -> None:
    fixation_report = _fixate_fp_rules_report(skill_dir)
    result["fp_rule_fixation"] = fixation_report
    if fixation_report.get("blocked_by_zero_gate"):
        _log_fixation_blocked(
            dict_or_empty(fixation_report.get("fp_mask_audit")))

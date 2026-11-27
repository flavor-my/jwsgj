from __future__ import annotations

import logging
import re
from collections.abc import Mapping
from dataclasses import replace
from typing import Any, NamedTuple
from urllib.parse import quote

from jwsgj.diag_types_normalize import (
    as_list,
    dict_or_empty,
    safe_float,
    unwrap_cv_results,
)
from jwsgj.hallucination_norms import check_process_norms
from jwsgj.memory_bridge import (
    CATEGORY_CROSS_SESSION_LESSON,
    CATEGORY_DIAGNOSTIC_SUMMARY,
    CATEGORY_FIX_LEARNING,
    CATEGORY_PDCA_TRACKING,
    CATEGORY_RULE_EVOLUTION,
    RULE_ID_BARE_RE,
    WIKI_LESSONS_PREFIX,
    WIKI_PROJECTS_PREFIX,
    DiagnosticMemoryContext,
    DiagnosticMemoryOperation,
    baseline_count,
    cv_confirmed_signal,
    cv_fp_count_signal,
    extract_bare_rule_id,
    first_valid_count_signal,
    fix_failed,
    fix_succeeded,
    is_valid_count_form,
    is_valid_memory_score,
    last_summary_dict,
    md_cell,
    memory_date_stamp,
    normalize_rule_id,
    path_segment,
    pick_first,
    pick_text,
    pipeline_stage_views,
    rules_triggered_signal,
    safe_int,
    str_memory_paths,
    total_findings_signal,
    treatment_counts,
    treatment_items,
)

logger = logging.getLogger(__name__)
__all__ = [
    "fm_scalar",
    "generate_cross_session_lessons_ops",
    "generate_diagnostic_summary_op",
    "generate_fix_pattern_learning_ops",
    "generate_fupan_memory_ops",
    "generate_pdca_tracking_ops",
    "generate_retrospective_memory_ops",
    "generate_rule_evolution_ops",
]
logger.info("memory_op_generation 已加载: %d 项导出", len(__all__))
def _as_context(ctx: Any) -> DiagnosticMemoryContext | None:
    if isinstance(ctx, DiagnosticMemoryContext):
        return ctx
    if not isinstance(ctx, Mapping):
        return None
    names = DiagnosticMemoryContext.__dataclass_fields__
    return DiagnosticMemoryContext(**{
        name: ctx[name] for name in names if name in ctx})
def _existing_page_content(ctx: DiagnosticMemoryContext, path: str) -> str:
    for memory in as_list(ctx.raw_search_results):
        if not isinstance(memory, dict) or memory.get("path") != path:
            continue
        content = memory.get("content")
        if not (isinstance(content, str) and content.strip()):
            continue
        fallback_texts = (memory.get("snippet"), memory.get("summary"))
        if any(isinstance(text, str) and text.strip() and content == text
               for text in fallback_texts):
            continue
        return content
    return ""
def _existing_page_write_op(
    op: DiagnosticMemoryOperation | None,
    ctx: DiagnosticMemoryContext | None,
) -> DiagnosticMemoryOperation | None:
    if op is None or ctx is None:
        return op
    anchor = _existing_page_content(ctx, op.path)
    if op.path not in str_memory_paths(ctx) and not anchor:
        return op
    if not anchor:
        logger.warning(
            "[MemoryBridge] 记忆页已存在但缺少全文锚点，跳过新增操作: %s",
            op.path)
        return None
    if anchor == op.content:
        return None
    return replace(op, operation="patch", old_text=anchor)
def _rolled_back_count(tx: dict) -> int:
    if not isinstance(tx, dict):
        return 0
    raw = tx.get("rolled_back")
    if is_valid_count_form(raw):
        return safe_int(raw)
    return sum(
        1 for item in treatment_items(tx)
        if isinstance(item, dict) and item.get("status") == "rolled_back")
_CV_FINDINGS_KEYS = ("total_findings", "total_input_findings")
def _cv_findings_signal(cv_results: dict) -> int | None:
    if not isinstance(cv_results, dict) or not cv_results:
        return None
    return first_valid_count_signal(cv_results, _CV_FINDINGS_KEYS)
_ENHANCEMENT_COUNT_KEYS = ("auto_enhancements", "enhancements_applied",
                           "enhancement_actions")
_ENHANCEMENT_APPLIED_KEYS = ("applied", "count")
def _report_applied_count(report: Mapping) -> int | None:
    return next(
        (max(0, safe_int(report[key]))
         for key in _ENHANCEMENT_APPLIED_KEYS
         if is_valid_count_form(report.get(key))),
        None)
def _enhancements_count_signal(review_results: dict | None) -> int | None:
    if not isinstance(review_results, dict):
        return None
    for key in _ENHANCEMENT_COUNT_KEYS:
        raw = review_results.get(key)
        if isinstance(raw, Mapping):
            applied = _report_applied_count(raw)
            if applied is not None:
                return applied
            continue
        if isinstance(raw, (list, tuple, set, frozenset)):
            return len(raw)
        if is_valid_count_form(raw):
            return max(0, safe_int(raw))
    return None
def _summary_delta_row(label: str, previous: float | None,
                       current: float | None, *,
                       decimal: bool = False) -> str:
    value_format = ".1f" if decimal else "d"
    previous_cell = (format(previous, value_format)
                     if previous is not None else "N/A")
    current_cell = (format(current, value_format)
                    if current is not None else "N/A")
    delta_cell = (format(current - previous, f"+{value_format}")
                  if previous is not None and current is not None else "—")
    return f"| {label} | {previous_cell} | {current_cell} | {delta_cell} |\n"
def _is_unit_rate(value: Any) -> bool:
    parsed = safe_float(value, None)
    return parsed is not None and 0 <= parsed <= 1
def _build_summary_delta(last_summary: dict | None,
                         total_findings: int | None,
                         cv_confirmed: int | None, review_score: float,
                         score_valid: bool) -> str:
    if not last_summary:
        return ""
    prev_findings = baseline_count(
        last_summary, ("total_findings",), ("findings",))
    prev_cv_confirmed = baseline_count(
        last_summary, ("cv_confirmed", "confirmed_count", "confirmed"),
        ("confirmed_findings",))
    prev_score = _score_signal(pick_first(last_summary, ("review_score",)))
    current_score = review_score if score_valid else None
    header = ("\n\n## 与上次诊断对比\n\n| 指标 | 上次 | 本次 | 变化 |\n"
              "|------|------|------|------|\n")
    rows = (
        _summary_delta_row("总发现", prev_findings, total_findings),
        _summary_delta_row("CV确认", prev_cv_confirmed, cv_confirmed),
        _summary_delta_row("复盘评分", prev_score, current_score,
                           decimal=True),
    )
    return header + "".join(rows)
def _summary_counts(
    diagnosis_results: dict,
    cv_results: dict,
    treatment_results: dict,
    review_results: dict | None,
) -> dict:
    methods_executed = first_valid_count_signal(
        diagnosis_results, ("methods_executed",))
    methods_passed = first_valid_count_signal(
        diagnosis_results, ("methods_passed",))
    methods_failed = first_valid_count_signal(
        diagnosis_results, ("methods_failed",))
    total_signal = total_findings_signal(diagnosis_results)
    cv_findings_signal = _cv_findings_signal(cv_results)
    confirmed_signal = cv_confirmed_signal(cv_results)
    cv_findings_known = cv_findings_signal is not None
    cv_findings = cv_findings_signal if cv_findings_signal is not None else 0
    cv_confirmed = confirmed_signal or 0
    if cv_findings_known:
        cv_confirmed = min(cv_confirmed, cv_findings)
    total_findings_known = total_signal is not None or cv_findings_known
    total_findings = total_signal if total_signal is not None else 0
    if cv_findings_signal is not None:
        total_findings = max(total_findings, cv_findings_signal)
    cv_rules_triggered = rules_triggered_signal(cv_results)
    fp_signal = cv_fp_count_signal(cv_results)
    tx_counts = treatment_counts(treatment_results)
    tx_rolled_back = _rolled_back_count(treatment_results)
    review_score = (_first_score_signal(
        review_results, ("overall_score", "score"))
        if review_results else None)
    score_valid = review_score is not None
    return {
        "methods_executed": methods_executed or 0,
        "methods_executed_known": methods_executed is not None,
        "methods_passed": methods_passed or 0,
        "methods_passed_known": methods_passed is not None,
        "methods_failed": methods_failed or 0,
        "methods_failed_known": methods_failed is not None,
        "total_findings": total_findings,
        "total_findings_known": total_findings_known,
        "cv_findings": cv_findings,
        "cv_findings_known": cv_findings_known,
        "cv_confirmed": cv_confirmed,
        "cv_confirmed_known": confirmed_signal is not None,
        "cv_rules_triggered": cv_rules_triggered or 0,
        "cv_rules_triggered_known": cv_rules_triggered is not None,
        "tx_executed": tx_counts["executed"],
        "tx_succeeded": tx_counts["fixed"],
        "tx_failed": tx_counts["failed"],
        "tx_rolled_back": tx_rolled_back,
        "fp_filtered": fp_signal or 0,
        "fp_known": fp_signal is not None,
        "score_valid": score_valid,
        "review_score": review_score if review_score is not None else 0.0,
        "cv_tunings_count": (first_valid_count_signal(
            cv_results, ("cv_tuning_count", "tunings_count")) or 0),
        "enhancements_count": _enhancements_count_signal(review_results) or 0,
    }
def _clamped_ratio(numerator: float, denominator: float) -> float | None:
    if denominator <= 0:
        return None
    return min(1.0, max(0.0, numerator / denominator))
def _clamped_rate(numerator: float, denominator: float) -> float:
    return round(_clamped_ratio(numerator, denominator) or 0.0, 4)
def _trend_label(score_valid: bool, review_score: float) -> str:
    if not score_valid:
        return "N/A"
    if review_score >= 70:
        return "改善"
    if review_score >= 50:
        return "稳定"
    return "需改进"
def _rate_cell(numerator: float, denominator: float) -> str:
    ratio = _clamped_ratio(numerator, denominator)
    if ratio is None:
        return "N/A(0)"
    return f"{ratio * 100:.1f}% ({numerator}/{denominator})"
def _rate_display(numerator: float, denominator: float) -> str:
    ratio = _clamped_ratio(numerator, denominator)
    return "N/A" if ratio is None else f"{ratio:.4f}"
def _summary_rate_cells(counts: dict) -> dict:
    cv_confirmed = counts["cv_confirmed"]
    cv_findings = counts["cv_findings"]
    tx_succeeded = counts["tx_succeeded"]
    tx_attempted = tx_succeeded + counts["tx_failed"]
    fp_rate = ("N/A" if not (counts["fp_known"]
                              and counts["total_findings_known"])
               else _rate_display(counts["fp_filtered"],
                                  counts["total_findings"]))
    return {
        "cv_participation": (
            _rate_cell(cv_confirmed, cv_findings)
            if (counts["cv_confirmed_known"]
                and counts["cv_findings_known"]) else "N/A"),
        "fp_rate": fp_rate,
        "fix_rate": _rate_display(tx_succeeded, tx_attempted),
        "tx_success": _rate_cell(tx_succeeded, tx_attempted),
        "quality_trend": _trend_label(counts["score_valid"],
                                      counts["review_score"]),
    }
def _summary_cells(counts: dict) -> dict[str, str]:
    return {
        **_summary_count_cells(counts),
        **_summary_rate_cells(counts),
    }
def _count_cell(value: int, known: bool) -> str:
    return str(value) if known else "N/A"
def _summary_count_cells(counts: dict) -> dict[str, str]:
    return {
        "methods_executed": _count_cell(
            counts["methods_executed"], counts["methods_executed_known"]),
        "methods_passed": _count_cell(
            counts["methods_passed"], counts["methods_passed_known"]),
        "methods_failed": _count_cell(
            counts["methods_failed"], counts["methods_failed_known"]),
        "total_findings": _count_cell(
            counts["total_findings"], counts["total_findings_known"]),
        "cv_findings": _count_cell(
            counts["cv_findings"], counts["cv_findings_known"]),
        "cv_confirmed": _count_cell(
            counts["cv_confirmed"], counts["cv_confirmed_known"]),
        "cv_rules_triggered": _count_cell(
            counts["cv_rules_triggered"],
            counts["cv_rules_triggered_known"]),
    }
def _score_cell(counts: dict) -> str:
    return f"{counts['review_score']:.1f}" if counts["score_valid"] else "N/A"
def _summary_snapshot_rows(findings: Any) -> list[str]:
    if not isinstance(findings, list):
        return []
    pairs: set[tuple[str, str]] = set()
    for finding in findings:
        if not isinstance(finding, dict):
            continue
        rule_id = normalize_rule_id(finding.get("rule_id"))
        if not rule_id:
            continue
        raw_severity = finding.get("severity")
        severity = (raw_severity if isinstance(raw_severity, str)
                    and raw_severity else "")
        pairs.add((rule_id, severity))
    return [f"| {md_cell(rule_id)} | {md_cell(severity)} |"
            for rule_id, severity in sorted(pairs)]
def _build_summary_findings_snapshot(findings: Any) -> str:
    if not isinstance(findings, list):
        return ""
    rows = "\n".join(_summary_snapshot_rows(findings))
    # 无行时不输出表头：零发现（清洁一轮）时原来会落一个只有表头的悬空表，
    # 在诊断摘要记忆页里形成“| 规则ID | 严重度 |”空壳段落。
    if not rows:
        return ""
    return ("\n\n## 规则严重度快照\n\n"
            "| 规则ID | 严重度 |\n"
            "|------|------|\n"
            f"{rows}")
def _build_summary_content(
    counts: dict, cells: dict[str, str], delta_info: str, ts: str,
    findings: list | None = None,
) -> str:
    tx_succeeded = counts["tx_succeeded"]
    tx_executed = counts["tx_executed"]
    methods_cell = cells["methods_executed"]
    methods_ratio_cell = f"{cells['methods_passed']}/{cells['methods_failed']}"
    total_findings_cell = cells["total_findings"]
    cv_findings_cell = cells["cv_findings"]
    cv_confirmed_cell = cells["cv_confirmed"]
    score_cell = _score_cell(counts)
    score_summary_label = (f"复盘{score_cell}分" if counts["score_valid"]
                           else "复盘评分N/A")
    findings_snapshot = _build_summary_findings_snapshot(findings)
    return f"""---
title: 诊断摘要 ({ts})
summary: 诊断{methods_cell}方法/{total_findings_cell}发现, CV确认{cv_confirmed_cell}/{cv_findings_cell}, 治疗{tx_succeeded}/{tx_executed}成功, {score_summary_label}
---

## 诊断概要

| 指标 | 值 |
|------|-----|
| 诊断方法执行 | {methods_cell} |
| 方法通过/失败 | {methods_ratio_cell} |
| 总发现数 | {total_findings_cell} |
| CV发现数 | {cv_findings_cell} |
| CV确认数 | {cv_confirmed_cell} |
| CV规则触发 | {cells['cv_rules_triggered']} |
| 治疗执行 | {tx_executed} |
| 治疗成功 | {tx_succeeded} |
| 治疗失败 | {counts['tx_failed']} |
| 治疗回滚 | {counts['tx_rolled_back']} |
| 复盘评分 | {score_cell} |
| FP率 | {cells['fp_rate']} |
| 修复成功率 | {cells['fix_rate']} |
| CV调优数 | {counts['cv_tunings_count']} |
| 增强建议数 | {counts['enhancements_count']} |
{delta_info}{findings_snapshot}

## 关键指标

- CV参与率: {cells['cv_participation']}
- 治疗成功率: {cells['tx_success']}
- 质量趋势: {cells['quality_trend']}
"""
def _passes_claim_gate(claim_text: str) -> bool:
    try:
        claim_gate = check_process_norms({
            "operation": "memory_write",
            "claim_text": claim_text,
        })
    except Exception:
        logger.exception("[MemoryBridge] 铁律门禁异常，阻断记忆写入")
        return False
    violations = [v for v in as_list(claim_gate.get("violations"))
                  if isinstance(v, dict)]
    if claim_gate.get("status") == "blocked":
        blocked_ids = [v.get("rule_id", "") for v in violations]
        logger.error("[MemoryBridge] 诊断摘要记忆写入被铁律门阻断(规则: %s): %s",
                     ",".join(blocked_ids), claim_text)
        return False
    for violation in violations:
        logger.warning("[MemoryBridge] 诊断摘要铁律提醒 [%s] %s",
                       violation.get("rule_id", ""),
                       violation.get("detail", ""))
    return True
def generate_diagnostic_summary_op(
    diagnosis_results: dict,
    cv_results: dict,
    treatment_results: dict,
    review_results: dict | None = None,
    ctx: DiagnosticMemoryContext | None = None,
) -> DiagnosticMemoryOperation | None:
    ctx = _as_context(ctx)
    review_results = dict_or_empty(review_results)
    diagnosis_results = dict_or_empty(diagnosis_results)
    treatment_results = dict_or_empty(treatment_results)
    cv_results = unwrap_cv_results(cv_results)
    counts = _summary_counts(
        diagnosis_results, cv_results, treatment_results, review_results)
    cells = _summary_cells(counts)
    current_total = (counts["total_findings"]
                     if counts["total_findings_known"] else None)
    current_cv_confirmed = (counts["cv_confirmed"]
                            if counts["cv_confirmed_known"] else None)
    delta_info = _build_summary_delta(
        last_summary_dict(ctx), current_total,
        current_cv_confirmed, counts["review_score"],
        counts["score_valid"])
    ts = memory_date_stamp()
    path = f"{WIKI_PROJECTS_PREFIX}/诊断摘要-{ts}"
    content = _build_summary_content(
        counts, cells, delta_info, ts, diagnosis_results.get("findings"))
    cv_findings_cell = cells["cv_findings"]
    cv_confirmed_cell = cells["cv_confirmed"]
    total_findings_cell = cells["total_findings"]
    summary_claim = (f"诊断{cells['methods_executed']}方法/{total_findings_cell}发现, "
                     f"CV确认{cv_confirmed_cell}/{cv_findings_cell}, "
                     f"治疗{counts['tx_succeeded']}/{counts['tx_executed']}成功")
    if not _passes_claim_gate(summary_claim):
        return None
    return _existing_page_write_op(DiagnosticMemoryOperation(
        operation="add",
        path=path,
        content=content,
        category=CATEGORY_DIAGNOSTIC_SUMMARY,
        quality_score=6.0,
        reason=(f"诊断摘要: {total_findings_cell}发现/"
                f"{cv_confirmed_cell}确认/{counts['tx_succeeded']}修复成功"),
        confidence=0.8,
        tags=["diagnostic_summary", ts],
    ), ctx)
def _check_entry(item: str, expected: str, actual: str,
                 result: str) -> dict:
    return {"item": item, "expected": expected,
            "actual": actual, "result": result}
def _delta_result(delta: float, *, lower_is_better: bool) -> str:
    if delta == 0:
        return "neutral"
    improved = delta < 0 if lower_is_better else delta > 0
    return "effective" if improved else "ineffective"
def _pdca_check_cv_tuning(prev: dict, counts: dict,
                           has_prev_tuning: bool) -> list[dict]:
    checks: list[dict] = []
    if has_prev_tuning:
        prev_fp_raw = prev.get("fp_rate")
        if not counts["fp_known"]:
            checks.append(_check_entry(
                "CV规则调优", "FP率下降",
                "CV数据缺失，FP率不可比", "neutral"))
        elif not _is_unit_rate(prev_fp_raw):
            checks.append(_check_entry(
                "CV规则调优", "FP率下降",
                "上轮FP率未记录，无可比基线", "neutral"))
        elif not (counts["total_findings_known"]
                  and counts["total_findings"] > 0):
            checks.append(_check_entry(
                "CV规则调优", "FP率下降",
                "本轮无诊断发现，FP率不可比", "neutral"))
        else:
            prev_fp_rate = safe_float(prev_fp_raw)
            curr_fp_rate = _clamped_rate(counts["fp_filtered"],
                                         counts["total_findings"])
            fp_delta = curr_fp_rate - prev_fp_rate
            checks.append(_check_entry(
                "CV规则调优", "FP率下降",
                f"FP率{prev_fp_rate:.2%}→{curr_fp_rate:.2%}(Δ{fp_delta:+.2%})",
                _delta_result(fp_delta, lower_is_better=True)))
    return checks
def _pdca_check_fixer_avoidance(prev: dict, counts: dict) -> list[dict]:
    curr_failed = counts["tx_failed"]
    if not counts["tx_executed"]:
        return [_check_entry(
            "失败修复器规避", "失败数下降",
            "本轮无治疗执行，失败数不可比", "neutral")]
    if not is_valid_count_form(prev.get("failed_count")):
        return [_check_entry(
            "失败修复器规避", "失败数下降",
            "上轮失败数未记录，无可比基线", "neutral")]
    prev_failed = safe_int(prev.get("failed_count"))
    return [_check_entry(
        "失败修复器规避", "失败数下降",
        f"失败{prev_failed}→{curr_failed}(Δ{curr_failed - prev_failed:+d})",
        _delta_result(curr_failed - prev_failed, lower_is_better=True))]
def _pdca_check_score_trend(prev: dict, review: dict) -> list[dict]:
    prev_score = _score_signal(prev.get("review_score"))
    curr_score = _first_score_signal(
        review, ("overall_score", "score"))
    if prev_score is None or curr_score is None:
        return [_check_entry(
            "整体评分", "评分提升",
            "评分无可比基线(上轮或本轮未记录)", "neutral")]
    return [_check_entry(
        "整体评分", "评分提升",
        f"评分{prev_score:.1f}→{curr_score:.1f}(Δ{curr_score - prev_score:+.1f})",
        _delta_result(curr_score - prev_score, lower_is_better=False))]
_PDCA_TREND_ITEM = "跨会话PDCA趋势"
_PDCA_SUMMARY_NAME_CAP = 5
_PDCA_INEFFECTIVE_ROW = re.compile(
    r'\|\s*([^|]+)\s*\|\s*[^|]+\s*\|\s*[^|]+\s*\|\s*ineffective\s*\|')
_PDCA_INEFFECTIVE_HEAD_RE = re.compile(r"无效[:：]\s*([^\"\n]*)")
_PDCA_NAME_SPLIT_RE = re.compile(r"[、,，|/]+")
def _ineffective_names_from_head(content: str) -> list[str]:
    names: list[str] = []
    for match in _PDCA_INEFFECTIVE_HEAD_RE.finditer(content):
        names.extend(part.strip().strip('"').strip("'")
                     for part in _PDCA_NAME_SPLIT_RE.split(match.group(1)))
    return [name for name in names if name]
def _historical_ineffective_counts(history: list) -> dict[str, int]:
    counts: dict[str, int] = {}
    for entry in history:
        content = entry.get("content") if isinstance(entry, dict) else None
        if not isinstance(content, str):
            continue
        names = [
            *_ineffective_names_from_head(content),
            *(match.group(1).strip()
              for match in _PDCA_INEFFECTIVE_ROW.finditer(content)),
        ]
        for name in dict.fromkeys(names):
            if not name or name == _PDCA_TREND_ITEM:
                continue
            counts[name] = counts.get(name, 0) + 1
    return counts
def _pdca_trend_insights(
    ctx: DiagnosticMemoryContext,
) -> tuple[list[str], dict | None]:
    insights: list[str] = []
    history = as_list(ctx.pdca_history)
    if not history:
        return insights, None
    insights.extend(
        f"- {item_name}: 历史PDCA中{ineff_count}次标记为无效，建议升级处理策略"
        for item_name, ineff_count in _historical_ineffective_counts(history).items()
        if ineff_count >= 2)
    if not insights:
        return insights, None
    return insights, _check_entry(
        _PDCA_TREND_ITEM, "无持续无效措施",
        f"历史{len(history)}轮PDCA中{len(insights)}项持续无效",
        "ineffective")
def _pdca_summary_line(checks: list[dict], effective: list[dict],
                       ineffective: list[dict]) -> str:
    ineff_names = [c["item"] for c in ineffective[:_PDCA_SUMMARY_NAME_CAP]]
    summary_line = (f"PDCA闭环检查{len(checks)}项(有效{len(effective)}"
                    f"/无效{len(ineffective)}"
                    f"/中性{len(checks) - len(effective) - len(ineffective)})")
    if ineff_names:
        summary_line += f"; 无效: {'、'.join(ineff_names)}"
    return fm_scalar(summary_line)
def _pdca_act_lines(ineffective: list[dict], effective: list[dict],
                    trend_insights: list[str]) -> list[str]:
    act_lines: list[str] = []
    act_measures = [c for c in ineffective if c["item"] != _PDCA_TREND_ITEM]
    if act_measures:
        act_lines.append("### 需调整的措施")
        act_lines.extend(
            f"- {c['item']}: {c['actual']}，上轮措施未达预期，需重新评估策略"
            for c in act_measures)
    if effective:
        act_lines.append("### 已验证的措施")
        act_lines.extend(
            f"- {c['item']}: {c['actual']}，效果良好，建议保持"
            for c in effective)
    if trend_insights:
        act_lines.append("### 持续无效措施升级建议")
        act_lines.extend(trend_insights)
    return act_lines
def _build_pdca_content(checks: list[dict], effective: list[dict],
                        ineffective: list[dict], trend_insights: list[str],
                        prev_cv_tunings: list, prev_enhancements: list,
                        date_str: str) -> str:
    summary_line = _pdca_summary_line(checks, effective, ineffective)
    check_lines = [f"| {c['item']} | {c['expected']} | {c['actual']} | {c['result']} |"
                   for c in checks]
    act_lines = _pdca_act_lines(ineffective, effective, trend_insights)
    return f"""---
title: PDCA追踪 ({date_str})
summary: {summary_line}
---

## PDCA闭环追踪

### Plan (上轮改进)
- CV调优: {len(prev_cv_tunings)}项
- 增强建议: {len(prev_enhancements)}项

### Check (效果检查)

| 措施 | 预期 | 实际 | 结果 |
|------|------|------|------|
{chr(10).join(check_lines)}

### Act (改进措施)

{chr(10).join(act_lines) if act_lines else "所有措施效果中性，维持现状"}
"""
def _split_check_results(checks: list[dict]) -> tuple[list[dict], list[dict]]:
    effective = [c for c in checks if c["result"] == "effective"]
    ineffective = [c for c in checks if c["result"] == "ineffective"]
    return effective, ineffective
def generate_pdca_tracking_ops(
    pipeline_result: dict,
    ctx: DiagnosticMemoryContext | None,
) -> list[DiagnosticMemoryOperation]:
    ctx = _as_context(ctx)
    ops: list[DiagnosticMemoryOperation] = []
    prev = last_summary_dict(ctx)
    if not prev:
        return ops
    if not pipeline_result:
        return ops
    try:
        diag, cv, tx, review = pipeline_stage_views(pipeline_result)
        counts = _summary_counts(diag, cv, tx, review)
        prev_enhancements = as_list(prev.get("enhancements"))
        prev_cv_tunings = as_list(prev.get("cv_tunings"))
        checks: list[dict] = []
        checks.extend(_pdca_check_cv_tuning(
            prev, counts, bool(prev_cv_tunings)))
        checks.extend(_pdca_check_fixer_avoidance(prev, counts))
        checks.extend(_pdca_check_score_trend(prev, review))
        pdca_trend_insights, trend_check = _pdca_trend_insights(ctx)
        if trend_check is not None:
            checks.append(trend_check)
        effective, ineffective = _split_check_results(checks)
        date_str = memory_date_stamp()
        path = f"{WIKI_LESSONS_PREFIX}/PDCA追踪-{date_str}"
        content = _build_pdca_content(
            checks, effective, ineffective, pdca_trend_insights,
            prev_cv_tunings, prev_enhancements, date_str)
        write_op = _existing_page_write_op(DiagnosticMemoryOperation(
            operation="add",
            path=path,
            content=content,
            category=CATEGORY_PDCA_TRACKING,
            quality_score=8.5,
            reason=f"PDCA追踪: {len(effective)}有效/{len(ineffective)}无效",
            confidence=0.85,
            tags=["pdca", "feedback_loop"],
        ), ctx)
        if write_op is not None:
            ops.append(write_op)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] PDCA追踪操作生成异常: %s", e)
    return ops
def _quality_report_fallback(fupan_result: dict, raw_score,
                              grade: str) -> tuple:
    quality_report = fupan_result.get("quality_report")
    if not isinstance(quality_report, dict):
        return raw_score, grade
    if _score_signal(raw_score) is None:
        nested_score = quality_report.get("overall_score")
        if _score_signal(nested_score) is not None:
            raw_score = nested_score
    if not grade:
        nested_grade = quality_report.get("grade")
        if isinstance(nested_grade, str):
            grade = nested_grade.strip()
    return raw_score, grade
def _score_signal(raw: Any) -> float | None:
    parsed = safe_float(raw, None)
    return parsed if is_valid_memory_score(parsed) else None
def _first_score_signal(source: Mapping, keys: tuple[str, ...]) -> float | None:
    if not isinstance(source, Mapping):
        return None
    for key in keys:
        score = _score_signal(source.get(key))
        if score is not None:
            return score
    return None
def _fupan_score_grade(fupan_result: dict) -> tuple[float | None, str]:
    score = _first_score_signal(
        fupan_result, ("score", "overall_score", "quality_score"))
    grade_raw = fupan_result.get("grade")
    grade = grade_raw.strip() if isinstance(grade_raw, str) else ""
    if score is None or not grade:
        raw_score, grade = _quality_report_fallback(
            fupan_result, score, grade)
        score = _score_signal(raw_score)
    return score, grade
def generate_fupan_memory_ops(
    fupan_result: dict,
    ctx: DiagnosticMemoryContext | None = None,
) -> list[DiagnosticMemoryOperation]:
    ctx = _as_context(ctx)
    if not fupan_result:
        return []
    try:
        score, grade = _fupan_score_grade(fupan_result)
        if score is None or not grade:
            return []
        op = _existing_page_write_op(_fupan_memory_op(score, grade, ctx), ctx)
        return [op] if op is not None else []
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] fupan记忆操作生成异常: %s", e)
        return []
def _fupan_memory_op(score: float, grade: str,
                     ctx: DiagnosticMemoryContext | None) -> DiagnosticMemoryOperation:
    ts = memory_date_stamp()
    return DiagnosticMemoryOperation(
        operation="add",
        path=f"{WIKI_PROJECTS_PREFIX}/复盘-{ts}",
        content=_fupan_memory_content(ts, score, grade, ctx),
        category=CATEGORY_DIAGNOSTIC_SUMMARY,
        quality_score=7.0,
        reason=f"复盘: {score:.1f}分/{grade}级",
        confidence=0.8,
        tags=["fupan"],
    )
def _fupan_memory_content(ts: str, score: float, grade: str,
                          ctx: DiagnosticMemoryContext | None) -> str:
    return f"""---
title: 复盘 ({ts})
summary: {fm_scalar(f"复盘{score:.1f}分/{grade}级, 记忆桥接增强")}
---

## 复盘摘要

| 指标 | 值 |
|------|-----|
| 复盘评分 | {score:.1f} |
| 评级 | {md_cell(grade)} |
{_fupan_prev_score_rows(ctx, score)}"""
def _fupan_prev_score_rows(ctx: DiagnosticMemoryContext | None,
                           score: float) -> str:
    summary = last_summary_dict(ctx)
    if not isinstance(summary, dict):
        return ""
    prev = _score_signal(pick_first(summary, ("review_score",)))
    if prev is None:
        return "| 上次评分 | N/A |\n| 评分变化 | — |\n"
    return f"| 上次评分 | {prev:.1f} |\n| 评分变化 | {score - prev:+.1f} |\n"
def generate_retrospective_memory_ops(
    retro_result: dict,
    ctx: DiagnosticMemoryContext | None = None,
) -> list[DiagnosticMemoryOperation]:
    ctx = _as_context(ctx)
    ops: list[DiagnosticMemoryOperation] = []
    if not retro_result:
        return ops
    try:
        improvements = as_list(retro_result.get("improvements"))
        valid_improvements = [
            i for i in improvements
            if isinstance(i, dict)
            and pick_text(i, ("description", "title")).strip()
        ]
        score = _first_score_signal(
            retro_result, ("overall_score", "score"))
        if valid_improvements and score is not None:
            ts = memory_date_stamp()
            path = f"{WIKI_PROJECTS_PREFIX}/复盘改进-{ts}"
            imp_text = _improvement_lines(valid_improvements)
            content = f"""---
title: 复盘改进建议 ({ts})
summary: 复盘{score:.1f}分, {len(valid_improvements)}条改进建议
---

## 改进建议

{imp_text}
"""
            write_op = _existing_page_write_op(DiagnosticMemoryOperation(
                operation="add",
                path=path,
                content=content,
                category=CATEGORY_DIAGNOSTIC_SUMMARY,
                quality_score=7.0,
                reason=f"复盘改进: {score:.1f}分, {len(valid_improvements)}条建议",
                confidence=0.8,
                tags=["retrospective"],
            ), ctx)
            if write_op is not None:
                ops.append(write_op)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] retrospective记忆操作生成异常: %s", e)
    return ops
def _improvement_lines(improvements: list) -> str:
    return "\n".join(
        f"  - [{md_cell(pick_text(i, ('priority',), '?'))}] "
        f"{md_cell(pick_text(i, ('description', 'title'))[:80])}"
        for i in improvements[:10]
    )
def _canonical_rule_id(value: Any) -> str | None:
    rule_id = normalize_rule_id(value)
    return rule_id.upper() if rule_id else None
def _canonical_rule_findings(records: list):
    for record in records if isinstance(records, list) else ():
        if not isinstance(record, dict):
            continue
        canonical = _canonical_rule_id(record.get("rule_id"))
        if canonical is None:
            canonical = _canonical_rule_id(record.get("rule_family"))
        if canonical:
            yield canonical, record
def _new_rule_history() -> dict:
    return {"tunings": [], "fp_count": 0, "tp_count": 0}
def _rule_history_entry(rule_history: dict[str, dict], rule_id: str) -> dict:
    entry = rule_history.get(rule_id)
    if entry is None:
        entry = rule_history[rule_id] = _new_rule_history()
    return entry
def _accumulate_rule_history(tuning_history: list, fp_patterns: list,
                             tp_patterns: list,
                             evolution_records: list) -> dict[str, dict]:
    rule_history: dict[str, dict] = {}
    for rid, tuning in _canonical_rule_findings(tuning_history):
        _rule_history_entry(rule_history, rid)["tunings"].append({
            "adjustment": tuning.get("adjustment", ""),
            "reason": tuning.get("reason", ""),
            "timestamp": tuning.get("timestamp", ""),
        })
    for rid, _fp in _canonical_rule_findings(fp_patterns):
        _rule_history_entry(rule_history, rid)["fp_count"] += 1
    for rid, _tp in _canonical_rule_findings(tp_patterns):
        _rule_history_entry(rule_history, rid)["tp_count"] += 1
    for rid, _rev in _canonical_rule_findings(evolution_records):
        _rule_history_entry(rule_history, rid)["has_evolution_history"] = True
    return rule_history
def _rule_evolution_op_for(rid: str,
                           hist: dict) -> DiagnosticMemoryOperation | None:
    tuning_count = len(hist["tunings"])
    fp_count = hist["fp_count"]
    tp_count = hist["tp_count"]
    if tuning_count < 2 and fp_count + tp_count < 3:
        return None
    direction = _evolution_direction(fp_count, tp_count)
    content = f"""---
title: {fm_scalar(f"规则{rid}演进追踪")}
summary: {fm_scalar(f"规则{rid}历史{tuning_count}次调优/{fp_count}FP/{tp_count}TP, 方向: {direction}")}
---

## 规则演进

| 维度 | 值 |
|------|-----|
| 调优次数 | {tuning_count} |
| FP出现次数 | {fp_count} |
| TP出现次数 | {tp_count} |
| 演进方向 | {direction} |
| 历史演进记录 | {'有' if hist.get('has_evolution_history') else '无'} |

## 调优历史

"""
    for t in hist["tunings"][-5:]:
        content += (f"- [{md_cell(t.get('timestamp', '?'))}] "
                    f"{md_cell(t.get('adjustment', ''))}: "
                    f"{md_cell(t.get('reason', ''))}\n")
    return DiagnosticMemoryOperation(
        operation="add",
        path=f"{WIKI_LESSONS_PREFIX}/规则演进-{path_segment(rid)}",
        content=content,
        category=CATEGORY_RULE_EVOLUTION,
        quality_score=7.5,
        reason=f"规则{rid}演进: {tuning_count}次调优, FP={fp_count}, TP={tp_count}",
        rule_id=rid,
        confidence=0.8,
        tags=["rule_evolution", rid],
    )
def _evolution_direction(fp_count: int, tp_count: int) -> str:
    if fp_count > tp_count and fp_count >= 3:
        return "高FP风险(建议降权或禁用)"
    if tp_count > fp_count and tp_count >= 3:
        return "高TP价值(建议保持或提升)"
    return "稳定"
def generate_rule_evolution_ops(
    ctx: DiagnosticMemoryContext | None,
) -> list[DiagnosticMemoryOperation]:
    ctx = _as_context(ctx)
    ops: list[DiagnosticMemoryOperation] = []
    if not ctx:
        return ops
    try:
        rule_history = _accumulate_rule_history(
            as_list(ctx.cv_tuning_history),
            as_list(ctx.known_fp_patterns),
            as_list(ctx.known_tp_patterns),
            as_list(ctx.rule_evolution))
        for rid, hist in rule_history.items():
            evolution_op = _existing_page_write_op(
                _rule_evolution_op_for(rid, hist), ctx)
            if evolution_op is not None:
                ops.append(evolution_op)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 规则演进操作生成异常: %s", e)
    return ops
def _confirmed_cv_findings(cv_results: dict) -> list:
    confirmed = cv_results.get("confirmed_findings")
    if not isinstance(confirmed, list):
        confirmed = cv_results.get("findings")
    return confirmed if isinstance(confirmed, list) else []
def _lesson_rules_from_history(lessons: list) -> set[str]:
    rules: set[str] = set()
    for lesson in lessons:
        if not isinstance(lesson, dict):
            continue
        content = lesson.get("content", "")
        if not isinstance(content, str):
            continue
        for match in RULE_ID_BARE_RE.finditer(content):
            rule_id = extract_bare_rule_id(match.group(1))
            if rule_id:
                rules.add(rule_id)
    return rules
def _historical_rule_types(fp_patterns: list,
                           tp_patterns: list) -> dict[str, str]:
    historical: dict[str, str] = {}
    for pattern_type, patterns in (("fp", fp_patterns), ("tp", tp_patterns)):
        for rid, _pattern in _canonical_rule_findings(patterns):
            previous = historical.get(rid)
            historical[rid] = (
                "fp+tp" if previous is not None and previous != pattern_type
                else pattern_type)
    return historical
def _valid_rule_ids(records: list) -> set[str]:
    return {rid for rid, _record in _canonical_rule_findings(records)}
def _persistent_lesson_content(persistent_rules: set[str],
                               historical_rules: dict[str, str],
                               date_str: str) -> str:
    persistent_list = sorted(persistent_rules)
    details = chr(10).join(
        f"- {md_cell(rid)} (历史类型: "
        f"{md_cell(historical_rules.get(rid, 'unknown'))})"
        for rid in persistent_list)
    return f"""---
title: 跨会话顽固问题 ({date_str})
summary: {len(persistent_rules)}个规则在多次会话中反复出现, 需根因分析
---

## 顽固问题清单

{details}

## 根因分析建议

这些规则在历史和当前诊断中均出现，建议:
1. 分析规则检测逻辑是否存在系统性误判
2. 检查目标代码是否存在结构性问题导致同一类缺陷反复出现
3. 考虑是否需要代码架构层面重构而非逐处修复
"""
def _persistent_lesson_op(fp_patterns: list, tp_patterns: list,
                          findings: list, confirmed_findings: list,
                          historical_lesson_rules: set) -> DiagnosticMemoryOperation | None:
    if not (fp_patterns or tp_patterns or historical_lesson_rules):
        return None
    historical_rules = _historical_rule_types(fp_patterns, tp_patterns)
    current_rules = _valid_rule_ids(findings) | _valid_rule_ids(
        confirmed_findings)
    persistent_rules = set(historical_rules) & current_rules
    persistent_rules |= (historical_lesson_rules & current_rules)
    if len(persistent_rules) < 3:
        return None
    date_str = memory_date_stamp()
    return DiagnosticMemoryOperation(
        operation="add",
        path=f"{WIKI_LESSONS_PREFIX}/跨会话顽固问题-{date_str}",
        content=_persistent_lesson_content(
            persistent_rules, historical_rules, date_str),
        category=CATEGORY_CROSS_SESSION_LESSON,
        quality_score=8.0,
        reason=f"跨会话顽固问题: {len(persistent_rules)}个规则反复出现",
        confidence=0.85,
        tags=["cross_session", "persistent_issues"],
    )
def _fixer_identity(
    source: Mapping, keys: tuple[str, ...] = ("fixer_name", "fixer"),
) -> str:
    for key in keys:
        raw = source.get(key)
        if not isinstance(raw, str):
            continue
        text = raw.strip()
        if text:
            return text
    return ""
def _matching_fixes(tx_items: list, predicate) -> list[dict]:
    return [t for t in tx_items if isinstance(t, dict) and predicate(t)]
def _top_tallies(items: list, key_of, limit: int = 5) -> list[tuple]:
    counts: dict = {}
    for item in items:
        key = key_of(item)
        counts[key] = counts.get(key, 0) + 1
    return sorted(counts.items(),
                  key=lambda kv: (-kv[1], str(kv[0])))[:limit]
def _successful_strategy_op(tx_items: list) -> DiagnosticMemoryOperation | None:
    successful_fixes = _matching_fixes(
        tx_items, lambda f: fix_succeeded(f) and bool(_fixer_identity(f)))
    if len(successful_fixes) < 5:
        return None
    top_fixers = _top_tallies(
        successful_fixes,
        lambda f: _fixer_identity(f) or "unknown")
    date_str = memory_date_stamp()
    _top_fixer = md_cell(top_fixers[0][0])
    content = f"""---
title: 跨会话成功修复策略 ({date_str})
summary: {fm_scalar(f"本轮{len(successful_fixes)}项成功修复, Top修复器: {top_fixers[0][0]}({top_fixers[0][1]}次)")}
---

## 成功修复器排名

| 修复器 | 成功次数 | 占比 |
|--------|---------|------|
"""
    for fixer, count in top_fixers:
        pct = count / len(successful_fixes) * 100
        content += f"| {md_cell(fixer)} | {count} | {pct:.0f}% |\n"
    content += f"""
## 可复用策略

优先使用{_top_fixer}修复器处理高频规则：该修复器本轮成功{top_fixers[0][1]}次，成功修复次数最多（按次数排序，非成功率）。
"""
    return DiagnosticMemoryOperation(
        operation="add",
        path=f"{WIKI_LESSONS_PREFIX}/跨会话成功修复策略-{date_str}",
        content=content,
        category=CATEGORY_CROSS_SESSION_LESSON,
        quality_score=7.5,
        reason=f"成功修复策略: {len(successful_fixes)}项修复, Top修复器{top_fixers[0][0]}",
        confidence=0.8,
        tags=["cross_session", "successful_strategy"],
    )
def _failed_strategy_op(tx_items: list) -> DiagnosticMemoryOperation | None:
    failed_fixes = _matching_fixes(
        tx_items, lambda f: (fix_failed(f)
                             and bool(_canonical_rule_id(f.get("rule_id")))
                             and bool(_fixer_identity(f))))
    if len(failed_fixes) < 3:
        return None
    top_fails = [(f"{rid}::{fixer}", count) for (rid, fixer), count in
                 _top_tallies(failed_fixes, lambda f: (
                     _canonical_rule_id(f.get("rule_id")) or "unknown",
                     _fixer_identity(f) or "unknown"))]
    date_str = memory_date_stamp()
    _top_fail = top_fails[0][0]
    content = f"""---
title: 跨会话失败修复总结 ({date_str})
summary: {fm_scalar(f"本轮{len(failed_fixes)}项修复失败, 高频失败组合: {top_fails[0][0]}({top_fails[0][1]}次)")}
---

## 失败修复组合排名

| 规则::修复器 | 失败次数 |
|--------------|---------|
"""
    for combo, count in top_fails:
        content += f"| {md_cell(combo)} | {count} |\n"
    content += """
## 规避建议

以上修复器-规则组合失败频繁，建议:
1. 在后续治疗中标记为低优先级
2. 考虑使用替代修复器或手动修复
3. 分析失败根因，改进修复器逻辑
"""
    return DiagnosticMemoryOperation(
        operation="add",
        path=f"{WIKI_LESSONS_PREFIX}/跨会话失败修复总结-{date_str}",
        content=content,
        category=CATEGORY_CROSS_SESSION_LESSON,
        quality_score=7.0,
        reason=f"失败修复总结: {len(failed_fixes)}项失败, "
               f"Top失败组合{_top_fail}",
        confidence=0.75,
        tags=["cross_session", "failed_strategy"],
    )
class _LessonInputs(NamedTuple):
    findings: list
    confirmed_findings: list
    tx_items: list
    lessons: list
    fp_patterns: list
    tp_patterns: list
def _normalize_lesson_inputs(pipeline_result: dict,
                             ctx: DiagnosticMemoryContext) -> _LessonInputs:
    diag, cv, tx, _review = pipeline_stage_views(pipeline_result)
    return _LessonInputs(
        findings=as_list(diag.get("findings")),
        confirmed_findings=_confirmed_cv_findings(cv),
        tx_items=treatment_items(tx),
        lessons=as_list(ctx.cross_session_lessons),
        fp_patterns=as_list(ctx.known_fp_patterns),
        tp_patterns=as_list(ctx.known_tp_patterns),
    )
def generate_cross_session_lessons_ops(
    pipeline_result: dict,
    ctx: DiagnosticMemoryContext | None,
) -> list[DiagnosticMemoryOperation]:
    ctx = _as_context(ctx)
    ops: list[DiagnosticMemoryOperation] = []
    if not ctx or not pipeline_result:
        return ops
    try:
        inputs = _normalize_lesson_inputs(pipeline_result, ctx)
        historical_lesson_rules = _lesson_rules_from_history(inputs.lessons)
        persistent_op = _existing_page_write_op(_persistent_lesson_op(
            inputs.fp_patterns, inputs.tp_patterns, inputs.findings,
            inputs.confirmed_findings, historical_lesson_rules), ctx)
        if persistent_op is not None:
            ops.append(persistent_op)
        success_op = _existing_page_write_op(
            _successful_strategy_op(inputs.tx_items), ctx)
        if success_op is not None:
            ops.append(success_op)
        failed_op = _existing_page_write_op(
            _failed_strategy_op(inputs.tx_items), ctx)
        if failed_op is not None:
            ops.append(failed_op)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 跨会话经验提炼异常: %s", e)
    return ops
def _fix_pattern_path_candidates(rid: str, fixer: str) -> tuple[str, str]:
    encoded_rid = quote(str(rid), safe="-:")
    encoded_fixer = quote(str(fixer), safe="-:")
    canonical = f"{WIKI_LESSONS_PREFIX}/修复模式-{encoded_rid}-{encoded_fixer}"
    legacy = f"{WIKI_LESSONS_PREFIX}/修复模式-{rid}-{fixer}"
    return canonical, legacy
def _seed_known_pattern_paths(ctx: DiagnosticMemoryContext | None,
                              existing_paths: set[str]) -> None:
    for fp in (as_list(ctx.fix_patterns) if ctx else []):
        if not isinstance(fp, dict):
            continue
        rid = _canonical_rule_id(fp.get("rule_id"))
        fixer = _fixer_identity(fp)
        if rid and fixer:
            existing_paths.update(_fix_pattern_path_candidates(rid, fixer))
def _group_success_patterns(items: list) -> dict[tuple[str, str], list[dict]]:
    success_patterns: dict[tuple[str, str], list[dict]] = {}
    for item in items:
        if not isinstance(item, dict):
            continue
        if not fix_succeeded(item):
            continue
        rid = _canonical_rule_id(item.get("rule_id"))
        fixer = _fixer_identity(item)
        if not rid or not fixer:
            continue
        success_patterns.setdefault((rid, fixer), []).append({
            "file": pick_text(item, ("file", "file_path")),
        })
    return success_patterns
_YAML_RESTRICTED_CONTROL_RE = re.compile(r"[\x00-\x1f\x7f-\x9f]")
def fm_scalar(value: str) -> str:
    flat = re.sub(r"\s+", " ", str(value)).strip()
    escaped = flat.replace("\\", "\\\\").replace('"', '\\"')
    escaped = _YAML_RESTRICTED_CONTROL_RE.sub(
        lambda match: f"\\u{ord(match.group()):04x}", escaped)
    return f'"{escaped}"'
def _fix_pattern_content(
    rid: str, fixer: str, count: int, files_affected: list[str],
    total_files: int,
) -> str:
    _fx = md_cell(fixer)
    _rid_cell = md_cell(rid)
    _files_cell = (", ".join(md_cell(f) for f in files_affected)
                   if files_affected else "N/A")
    if total_files > len(files_affected):
        _files_cell = f"{_files_cell} 等{total_files}个文件"
    files_summary = (f"涉及{total_files}个文件" if total_files
                     else "文件信息缺失")
    title = fm_scalar(f"修复模式: {fixer} → {rid}")
    summary = fm_scalar(
        f"修复器{fixer}处理规则{rid}成功{count}次, "
        f"{files_summary}, 可复用修复模板")
    return f"""---
title: {title}
summary: {summary}
---

## 修复模式

| 维度 | 值 |
|------|-----|
| 修复器 | {_fx} |
| 规则ID | {_rid_cell} |
| 成功次数 | {count} |
| 涉及文件 | {_files_cell} |
| 可复用性 | 高(成功≥2次) |

## 使用建议

当诊断发现规则{_rid_cell}的finding时，优先使用修复器{_fx}，该组合在本轮治疗中成功{count}次（仅统计成功案例，实际成功率需结合总尝试次数评估）。
"""
def _fix_pattern_op_for_group(
    rid: str, fixer: str, patterns: list[dict], existing_paths: set[str],
) -> DiagnosticMemoryOperation | None:
    count = len(patterns)
    if count < 2:
        return None
    path, legacy_path = _fix_pattern_path_candidates(rid, fixer)
    if path in existing_paths or legacy_path in existing_paths:
        return None
    all_files = sorted({p["file"] for p in patterns if p["file"]})
    files_affected = all_files[:5]
    return DiagnosticMemoryOperation(
        operation="add",
        path=path,
        content=_fix_pattern_content(
            rid, fixer, count, files_affected, total_files=len(all_files)),
        category=CATEGORY_FIX_LEARNING,
        quality_score=8.5,
        reason=f"修复模式学习: {fixer}→{rid} 成功{count}次",
        rule_id=rid,
        confidence=0.9,
        tags=["fix_pattern", fixer, rid],
    )
def generate_fix_pattern_learning_ops(
    treatment_results: dict,
    ctx: DiagnosticMemoryContext | None,
) -> list[DiagnosticMemoryOperation]:
    ctx = _as_context(ctx)
    ops: list[DiagnosticMemoryOperation] = []
    if not treatment_results:
        return ops
    try:
        items = treatment_items(treatment_results)
        existing_paths = str_memory_paths(ctx)
        _seed_known_pattern_paths(ctx, existing_paths)
        success_patterns = _group_success_patterns(items)
        for (rid, fixer), patterns in success_patterns.items():
            op = _fix_pattern_op_for_group(rid, fixer, patterns, existing_paths)
            if op is not None:
                ops.append(op)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 修复模式学习操作生成异常: %s", e)
    if ops:
        logger.info("[MemoryBridge] 修复模式学习: %d条可复用模式", len(ops))
    return ops

from __future__ import annotations

import html as _html
import logging
import math
import os
import re
import time
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any

from jwsgj.diag_types_normalize import (
    as_dict,
    as_list,
    dict_items,
    plan_index,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    FANOUT_FORBIDDEN_ACTIONS,
    FANOUT_GOVERNANCE_RULE,
    FANOUT_LEVEL_L1,
    FANOUT_LEVEL_L2,
    FANOUT_LEVEL_L3,
    FANOUT_LEVEL_L4,
    FANOUT_ROLE_LABELS,
    FANOUT_ROLE_MODULE,
    FANOUT_STRATEGIES,
    FANOUT_STRATEGY_GOVERNANCE,
    FANOUT_STRATEGY_LABELS,
    FIELD_ADJUSTED_CONFIDENCE,
    FIELD_BASE_CONFIDENCE,
    FIELD_TOTAL_INPUT_FINDINGS,
    TX_FAILED_STATUSES,
    TX_FIXED_STATUSES,
    TX_ROLLED_BACK_STATUSES,
    fanout_level_label,
)
from jwsgj.fanout_report import fanout_module_counts
from jwsgj.html_render_diag import (
    artifacts_section,
    render_fallback_html,
    render_feedback_step_html,
    render_single_method_html,
)
from jwsgj.html_render_review import (
    render_ai_review_html,
    render_coverage_report_html,
    render_degradation_report_html,
    render_dependency_report_html,
    render_fupan_report_html,
    render_retro_report_html,
    render_treatment_item_html,
)
from jwsgj.html_report_primitives import (
    DISCLOSURE_ROWS_COMPACT,
    DISCLOSURE_ROWS_WIDE,
    HTMLReport,
    ReportSection,
    alert_tone,
    apply_target_identity,
    empty_card,
    esc_or,
    extend_sections,
    extract_finding_coords,
    kv_table,
    kv_table_preescaped,
    read_field,
    render_badge,
    render_health_badge,
    render_progress_bar,
    render_stat,
    render_table,
    safe_filename,
    safe_text,
    scalar_detail,
    status_badge_css,
    text_or,
    to_bool,
    to_finite_float,
    to_float,
    to_int,
)
from jwsgj.html_report_stage_doc import (
    DEFAULT_SKILL_DIR,
    STAGES,
    emit_final_block,
    emit_to_stage,
    normalize_skill_key,
    read_stage_meta,
    stage_pair_status,
)
from jwsgj.runtime_paths import (
    get_html_report_base,
    stage_json_artifact_path,
)

logger = logging.getLogger(__name__)
_DEFAULT_SKILL_DIR = DEFAULT_SKILL_DIR
_CATEGORY_RULES: tuple[tuple[tuple[str, ...], str], ...] = (
    # 中文名口径（诊断A/交叉验证/扇出G/审核治疗/复盘反哺/最终报告）
    (("诊断",), "诊断项"),
    (("交叉验证",), "交叉验证"),
    (("扇出G",), "扇出诊断"),
    (("审核治疗",), "审核治疗"),
    (("复盘反哺",), "复盘反哺"),
    (("最终报告",), "最终报告"),
    # 旧英文前缀：历史产物只读兼容
    (("final_report_",), "最终报告"),
    (("stage_fanout_",), "扇出诊断"),
    (("stage_treat_review_",), "审核治疗"),
    (("stage_retro_feedback_",), "复盘反哺"),
    (("diag_",), "诊断项"),
    (("cv_report_",), "交叉验证"),
    (("treat_",), "治疗项"),
    (("aireview_",), "AI审核执行"),
    (("fupan_report",), "复盘反哺"),
    (("batch_",), "批量总览"),
    (("retro_",), "复盘反哺"),
    (("security_",), "安全审计"),
    (("blindspot_",), "盲点扫描"),
    (("step_",), "管线步骤"),
    (("cv_",), "交叉验证"),
    (("degradation_report",), "降级报告"),
    (("dependency_", "coverage_", "pipeline_report", "pipeline_summary"), "阶段报告"),
)
_STAGE_CATEGORY_LABELS: dict[str, str] = {
    "diag": "诊断阶段",
    "cv": "交叉验证",
    "fanout": "扇出诊断",
    "treat_review": "审核治疗",
    "retro_feedback": "复盘反哺",
    "final": "最终报告",
}
def _category(fn: str, stage: str = "") -> str:
    if fn in ("final_report.html", "最终报告.html"):
        return "最终报告"
    for _prefixes, _label in _CATEGORY_RULES:
        if fn.startswith(_prefixes):
            return _label
    stage = text_or(stage).strip()
    if stage:
        return _STAGE_CATEGORY_LABELS.get(stage, stage)
    return "其他"
def _artifact_entry(fp: str, fn: str, meta: dict | None = None,
                    skill_dir: str = _DEFAULT_SKILL_DIR) -> dict | None:
    try:
        st = os.stat(fp)
    except OSError as e:
        logger.debug("探测文件状态失败（跳过）: %s: %s", fp, e)
        return None
    stage = text_or(as_dict(meta).get("stage"))
    entry = {
        "category": _category(fn, stage),
        "filename": fn,
        "path": fp,
        "mtime": st.st_mtime,
        "size": st.st_size,
    }
    try:
        pair = stage_pair_status(fp, skill_dir)
        if pair.get("json_path"):
            entry["json_path"] = pair["json_path"]
        entry["item_count"] = pair.get("html_items")
        entry["json_item_count"] = pair.get("json_items")
        entry["pair_status"] = pair.get("status")
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        logger.debug("阶段配对校验失败（跳过状态）: %s: %s", fp, exc)
    return entry
def _dir_html_names(d) -> list[str]:
    try:
        return sorted(os.listdir(d)) if os.path.isdir(d) else []
    except OSError as e:
        logger.debug("目录扫描失败（跳过）: %s: %s", d, e)
        return []
def _scan_dir_html(d, seen: set, skill_dir: str = _DEFAULT_SKILL_DIR) -> list[dict]:
    out: list[dict] = []
    for fn in _dir_html_names(d):
        if not fn.endswith(".html"):
            continue
        fp = os.path.join(d, fn)
        if not os.path.isfile(fp):
            continue
        key = os.path.normcase(os.path.realpath(fp))
        if key in seen:
            continue
        seen.add(key)
        meta = read_stage_meta(fp)
        owner = text_or(as_dict(meta).get("skill"))
        if normalize_skill_key(owner) != skill_dir:
            continue
        entry = _artifact_entry(fp, fn, meta, skill_dir)
        if entry is None:
            continue
        out.append(entry)
    return out
def _normalize_extra_dirs(extra_dirs) -> list:
    if isinstance(extra_dirs, str):
        return [extra_dirs]
    if not isinstance(extra_dirs, (list, tuple)):
        return []
    return [d for d in extra_dirs if isinstance(d, (str, os.PathLike))]
def collect_html_artifacts(skill_dir: str, extra_dirs: list[str] | None = None) -> list[dict]:
    scope = normalize_skill_key(skill_dir) if skill_dir else ""
    scan_dirs = [get_html_report_base(), *_normalize_extra_dirs(extra_dirs)]
    artifacts: list[dict] = []
    seen: set[str] = set()
    for d in scan_dirs:
        artifacts.extend(_scan_dir_html(d, seen, scope))
    artifacts.sort(key=lambda a: a["mtime"], reverse=True)
    return artifacts
def _skill_arg(skill_dir) -> str:
    text = text_or(skill_dir).strip()
    return os.path.abspath(text) if text else ""
def _report_not_landed_reason(result: Any) -> str:
    info = as_dict(result)
    data = as_dict(info.get("data"))
    parts: list[str] = []
    for key in ("status", "message"):
        val = text_or(info.get(key))
        if val:
            parts.append(f"{key}={val}")
    suppressed = text_or(data.get("suppressed"))
    if suppressed:
        parts.append(f"suppressed={suppressed}")
    return ", ".join(parts) or "no_path"
def _log_report_landing(result: Any, tag: str, subject: str = "") -> str:
    path = html_report_path(result)
    suffix = f"（{subject}）" if subject else ""
    if path:
        logger.info("[%s] HTML 报告已生成%s: %s", tag, suffix, path)
        return path
    logger.warning("[%s] HTML 报告留痕失败（未落盘，不阻断）%s: %s", tag, suffix,
                   _report_not_landed_reason(result))
    return ""
def _fbfix_report_payload(mod: Any, plan: dict) -> tuple[dict, str]:
    plan = as_dict(plan)
    raw_mod = mod.to_dict() if hasattr(mod, "to_dict") else mod
    mod_dict = as_dict(raw_mod)
    ident = "unknown"
    for candidate in (mod_dict.get("modification_id"), plan.get("plan_id"),
                      plan.get("target")):
        if candidate:
            ident = safe_text(candidate)[:40]
            break
    payload = {
        "status": ("applied" if to_bool(mod_dict.get("applied"))
                   else "not_applied"),
        "review_id": f"fbfix-{ident}",
        "channel": "feedback_fix",
        "reason": safe_text(mod_dict.get("error_message") or "")[:500],
        "result": mod_dict,
    }
    return payload, ident
def emit_feedback_fix_report(mod: Any, plan: dict, skill_dir: str) -> None:
    try:
        payload, ident = _fbfix_report_payload(mod, plan)
        result = generate_html_report(
            payload, _skill_arg(skill_dir), "ai_review")
        _log_report_landing(
            result, "CodeLevelFeedback", f"反哺修改执行 {ident}")
    except Exception as html_err:
        logger.warning("[CodeLevelFeedback] 反哺修改执行 HTML 留痕失败(不阻断): %s",
                       html_err)
__all__ = [
    "ReportFormatter",
    "collect_html_artifacts",
    "cv_report_findings",
    "emit_aggregate_report_html",
    "emit_ai_fix_trace",
    "emit_coverage_report_html",
    "emit_dependency_report_html",
    "emit_feedback_fix_report",
    "emit_final_summary_block",
    "emit_fupan_report_html",
    "emit_html_report",
    "emit_single_method_html",
    "emit_step_html",
    "emit_step_trace",
    "emit_treatment_item_report",
    "format_impact_report",
    "generate_html_report",
    "html_report_path",
    "render_batch_report_html",
    "render_cv_report_html",
    "render_fanout_report_html",
    "render_pipeline_report_html",
    "render_pipeline_summary_html",
]
logger.info("html_render_pipeline 已加载: %d 项导出（管道编排、分发路由与发射出口）", len(__all__))
_CV_COUNT_KEYS = ("confirmed", "likely", "uncertain", "suppressed", "contradictions")
_CV_PAYLOAD_MARKERS = (
    "findings_index", "findings", "rules_detail", "rule_analysis",
    "executive_summary", "phase_health", "uncertain_enqueue_report",
    "health", "health_description", FIELD_TOTAL_INPUT_FINDINGS,
    *_CV_COUNT_KEYS, "conclusion",
)
_CV_CONCLUSION_ORDER = ("confirmed", "likely", "uncertain", "suppressed")
_CV_CONCLUSION_BADGE = {"confirmed": "badge-danger", "likely": "badge-warning",
                        "uncertain": "badge-info"}
_RAW_SCALAR_SAMPLE_CAP = DISCLOSURE_ROWS_COMPACT
def _finite_number(value) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    num = to_finite_float(value, math.nan)
    return num if math.isfinite(num) else None
def _count_or_none(value) -> int | None:
    if value is None or isinstance(value, bool):
        return None
    count = None
    if isinstance(value, int):
        count = value
    elif isinstance(value, str) and re.fullmatch(r"[+-]?\d+", value.strip()):
        try:
            count = int(value)
        except ValueError:
            logger.debug("计数字符串超出解释器整数转换限制，按未度量处理")
            count = None
    else:
        num = _finite_number(value)
        if num is not None and num.is_integer():
            count = int(num)
    return count if count is not None and count >= 0 else None
def _count_value(value) -> int:
    count = _count_or_none(value)
    return 0 if count is None else count
def _raw_scalar_sample(items) -> list:
    return [item for item in list(items)[:_RAW_SCALAR_SAMPLE_CAP]
            if not isinstance(item, (dict, list, tuple))]
def _compact_raw_node(node: dict, depth: int = 0) -> dict:
    view: dict = {}
    def _container_summary_key(key, kind: str) -> str:
        base = f"{key}_{kind}"
        candidate = base
        serial = 2
        while candidate in node or candidate in view:
            candidate = f"{base}_{serial}"
            serial += 1
        return candidate
    for key, value in node.items():
        if depth >= 3 and isinstance(value, (dict, list, tuple)):
            kind = "keys" if isinstance(value, dict) else "count"
            view[_container_summary_key(key, kind)] = len(value)
        elif isinstance(value, dict):
            view[key] = _compact_raw_node(value, depth + 1)
        elif isinstance(value, (list, tuple)):
            view[_container_summary_key(key, "count")] = len(value)
            _scalars = _raw_scalar_sample(value)
            if _scalars:
                view[key] = _scalars
        else:
            view[key] = value
    return view
def _report_raw(payload: dict, target: str) -> dict:
    raw = dict(payload) if isinstance(payload, dict) else {}
    stages = raw.get("stages")
    if isinstance(stages, dict):
        raw["stages"] = {
            key: (_compact_raw_node(value) if isinstance(value, dict) else value)
            for key, value in stages.items()}
    return apply_target_identity(raw, target)
def _stage_report_or_top(stage: dict) -> dict:
    rep = stage.get("report")
    return stage if rep is None else as_dict(rep)
def _adapt_cv_payload(cv_result: dict) -> dict:
    if not isinstance(cv_result, dict):
        return {}
    rep = cv_result.get("report")
    if isinstance(rep, dict) and any(m in rep for m in _CV_PAYLOAD_MARKERS):
        merged = dict(rep)
        for k, v in cv_result.items():
            if k != "report" and k not in merged:
                merged[k] = v
        return merged
    return cv_result
def _cv_counts(src: dict) -> dict:
    es = as_dict(src.get("executive_summary"))
    counts = {}
    for key in _CV_COUNT_KEYS:
        raw = src.get(key)
        if raw is None:
            raw = es.get(key, 0)
        counts[key] = _count_value(raw)
    return counts
def _cv_health_view(cv_result: dict) -> tuple[str, str]:
    es = cv_result.get("executive_summary")
    es_dict = as_dict(es)
    health = ""
    for candidate in (cv_result.get("health"), es_dict.get("health"),
                      as_dict(cv_result.get("phase_health")).get("overall_status")):
        health = _text_scalar(candidate)
        if health:
            break
    health = health or "unknown"
    if isinstance(es, dict):
        desc = ""
        for candidate in (es.get("description"), es.get("health_description"),
                          es.get("summary"), es.get("message")):
            desc = _text_scalar(candidate)
            if desc:
                break
    elif isinstance(es, str):
        desc = es
    else:
        desc = ""
    return health, desc
def _cv_stat_tiles(counts: dict, total: int | None = None) -> str:
    tiles = "" if total is None else render_stat(total, "发现总数", "info")
    return tiles + (
        render_stat(counts["confirmed"], "已确认",
                     alert_tone(counts["confirmed"], "danger"))
        + render_stat(counts["likely"], "较可信", "warning")
        + render_stat(counts["uncertain"], "不确定", "info")
        + render_stat(counts["suppressed"], "已抑制",
                       "muted" if counts["suppressed"] == 0 else "")
        + render_stat(counts["contradictions"], "矛盾",
                       alert_tone(counts["contradictions"], "danger")))
def _cv_summary_section(cv_result: dict) -> ReportSection:
    _cv_health, _cv_health_desc = _cv_health_view(cv_result)
    health_desc = text_or(cv_result.get("health_description")) or _cv_health_desc
    total_raw = cv_result.get(FIELD_TOTAL_INPUT_FINDINGS)
    if total_raw is None:
        total_raw = as_dict(cv_result.get("executive_summary")).get(
            "total_findings")
    stats = _cv_stat_tiles(_cv_counts(cv_result), _count_or_none(total_raw))
    summary_html = f"""
<div class="stat-grid">{stats}</div>
<div class="card">
    <h3>健康评估</h3>
    {render_health_badge(_cv_health)}
    <span style="margin-left:16px;color:#718096;">{_html.escape(health_desc)}</span>
</div>
"""
    return ReportSection(
        title="执行摘要", section_id="summary", icon="📊", html_content=summary_html,
    )
def _cv_split_findings(findings: list) -> tuple[list, list]:
    buckets: dict[str, list] = {_c: [] for _c in _CV_CONCLUSION_ORDER}
    other_findings: list = []
    for f in findings:
        conclusion = f.get("conclusion")
        if isinstance(conclusion, str):
            conclusion = conclusion.strip().lower()
        if isinstance(conclusion, str) and conclusion in buckets:
            buckets[conclusion].append(f)
        else:
            other_findings.append(f)
    suppressed = buckets["suppressed"]
    ordered = [f for _c in _CV_CONCLUSION_ORDER if _c != "suppressed"
               for f in buckets[_c]]
    return ordered + other_findings, suppressed
def _cv_confidence_pct(f: dict) -> str:
    conf = f.get(FIELD_ADJUSTED_CONFIDENCE)
    if conf is None:
        conf = f.get(FIELD_BASE_CONFIDENCE)
    if isinstance(conf, bool):
        return "N/A"
    num = to_float(conf, math.nan)
    if not math.isfinite(num):
        return "N/A"
    return f"{min(max(num, 0.0), 1.0)*100:.0f}%"
def _cv_finding_row(f: dict) -> list:
    sev_raw = text_or(f.get("severity"), "P3")
    sev = _html.escape(sev_raw)
    sev_class = f"severity-{safe_filename(sev_raw)}"
    conf_pct = _cv_confidence_pct(f)
    conclusion_raw = f.get("conclusion")
    conclusion = (conclusion_raw.strip().lower()
                  if isinstance(conclusion_raw, str) else "")
    conclusion = conclusion or "unknown"
    badge_css = _CV_CONCLUSION_BADGE.get(conclusion, "badge-muted")
    _ff, _fl = extract_finding_coords(f)
    return [
        render_badge(conclusion, badge_css),
        f'<span class="{sev_class}">{sev}</span>',
        esc_or(f.get("rule_applied") or f.get("rule_id")),
        _html.escape(_ff),
        _html.escape(_fl),
        conf_pct,
        esc_or(f.get("message") or f.get("sample_message")
               or f.get("sample_finding")),
    ]
def _cv_findings_and_suppressed(cv_result: dict) -> tuple[ReportSection, list]:
    findings = dict_items(cv_report_findings(cv_result))
    all_findings, suppressed_findings = _cv_split_findings(findings)
    if all_findings:
        rows = [_cv_finding_row(f) for f in all_findings]
        findings_html = render_table(
            ["状态", "级别", "规则", "文件", "行号", "置信度", "描述"],
            rows, table_id="findings_table", initial_visible=100,
        )
    else:
        findings_html = empty_card("无发现")
    _find_sec = ReportSection(
        title="问题详情", section_id="findings", icon="🔍", html_content=findings_html,
    )
    return _find_sec, suppressed_findings
def _cv_suppressed_section(suppressed_findings: list) -> ReportSection | None:
    if suppressed_findings:
        _sup_rows = []
        for _sf in suppressed_findings:
            _sff, _sfl = extract_finding_coords(_sf)
            _sup_rows.append([
                esc_or(_sf.get("_suppression_rule")
                       or _sf.get("rule_applied")
                       or _sf.get("rule_id")),
                _html.escape(_sff),
                _html.escape(_sfl),
                esc_or(_sf.get("severity"), "P3"),
                esc_or(_sf.get("message")),
            ])
        _sup_html = (
            "<div class='card'><p style='color:#b7791f;'>以下 finding 已被"
            " CV 抑制（ suppressed ）。被抑制项强制进入 AI 语义复核队列"
            "（cv_uncertain 通道，不限严重度）：AI 裁决抑制是否成立——"
            "误判抑制将恢复 confirmed 重见天日，正确抑制才固化为误报规则。"
            "</p></div>"
            + render_table(
                ["抑制来源规则", "文件", "行号", "级别", "描述"],
                _sup_rows, table_id="suppressed_table",
                initial_visible=100))
        return ReportSection(
            title=f"被抑制项（{len(suppressed_findings)} 项·强制 AI 复核）",
            section_id="suppressed", icon="🚫", html_content=_sup_html)
    return None
def _cv_enqueue_section(cv_result: dict) -> ReportSection | None:
    _enqueue_rep = as_dict(cv_result.get("uncertain_enqueue_report"))
    if _enqueue_rep:
        _eq_attempted = to_bool(_enqueue_rep.get("attempted"))
        _eq_failed = to_bool(_enqueue_rep.get("failed"))
        _eq_count = to_int(_enqueue_rep.get("enqueued"))
        _eq_status = ("入队失败·复核闭环未闭合" if _eq_failed
                      else (f"已入队 {_eq_count} 项" if _eq_attempted
                            else "未执行"))
        _eq_kind = "danger" if _eq_failed else ("info" if _eq_attempted else "muted")
        _eq_html = ("<div class='stat-grid'>" + render_stat(
            _eq_status, "AI 复核队列入队", _eq_kind) + "</div>")
        if _eq_failed and _enqueue_rep.get("error"):
            _eq_html += ("<div class='card'><h3>失败原因</h3><p>"
                         + _html.escape(safe_text(_enqueue_rep.get("error")))
                         + "</p></div>")
        return ReportSection(
            title="AI 复核队列入队状态", section_id="enqueue_health",
            icon="📮", html_content=_eq_html)
    return None
def _cv_rule_row(r: dict) -> list:
    triggered_badge = (render_badge("触发", "badge-warning")
                       if to_bool(r.get("triggered"))
                       else render_badge("未触发", "badge-muted"))
    return [
        triggered_badge,
        esc_or(r.get("rule_id")),
        esc_or(r.get("description")),
        esc_or(r.get("trigger_count"), "0"),
    ]
def _cv_rules_section(cv_result: dict) -> ReportSection:
    rules_detail = dict_items(cv_result.get("rules_detail"))
    if not rules_detail:
        rule_analysis = as_dict(cv_result.get("rule_analysis"))
        rules_detail = (dict_items(rule_analysis.get("triggered"))
                        + dict_items(rule_analysis.get("never_triggered")))
    if rules_detail:
        triggered = [r for r in rules_detail if to_bool(r.get("triggered"))]
        never_triggered = [r for r in rules_detail
                           if not to_bool(r.get("triggered"))]
        rules_stats = (
            render_stat(len(rules_detail), "规则总数", "info")
            + render_stat(len(triggered), "已触发", alert_tone(triggered, "warning"))
            + render_stat(len(never_triggered), "未触发", "muted")
        )
        rule_rows = [_cv_rule_row(r) for r in rules_detail]
        rules_html = f'<div class="stat-grid">{rules_stats}</div>' + render_table(
            ["状态", "规则ID", "描述", "触发次数"], rule_rows, table_id="rules_table",
            initial_visible=50,
        )
    else:
        rules_html = empty_card("无规则数据")
    return ReportSection(
        title="规则分析", section_id="rules", icon="📋", html_content=rules_html,
    )
def _cv_phases_section(cv_result: dict) -> ReportSection:
    phase_health = as_dict(cv_result.get("phase_health"))
    logger.debug("[HtmlReport] render_cv_report_html 渲染: phase_health=%d 键", len(phase_health))
    if phase_health:
        phase_rows = []
        for phase, info in phase_health.items():
            if isinstance(info, dict):
                health = _text_scalar(info.get("health")) or "unknown"
                count = _count_or_none(info.get("finding_count"))
            else:
                health = _text_scalar(info) or "unknown"
                count = None
            phase_rows.append([
                _html.escape(safe_text(phase)),
                render_health_badge(health),
                _html.escape("-" if count is None else str(count)),
            ])
        phase_html = render_table(["阶段", "健康度", "发现数"], phase_rows, table_id="phases_table")
    else:
        phase_html = empty_card("无阶段数据")
    return ReportSection(
        title="阶段健康", section_id="phases", icon="🩺", html_content=phase_html,
    )
def _cv_evidence_sections(cv_result: dict) -> list[ReportSection]:
    find_sec, suppressed = _cv_findings_and_suppressed(cv_result)
    sections = [find_sec]
    extend_sections(sections, (
        _cv_suppressed_section(suppressed),
        _cv_enqueue_section(cv_result),
    ))
    return sections
def _cv_report_sections(cv_result: dict) -> list[ReportSection]:
    return [
        _cv_summary_section(cv_result),
        *_cv_evidence_sections(cv_result),
        _cv_rules_section(cv_result),
        _cv_phases_section(cv_result),
    ]
def render_cv_report_html(cv_result: dict, skill_dir: str = _DEFAULT_SKILL_DIR) -> str:
    cv_result = _adapt_cv_payload(cv_result)
    return HTMLReport(
        title="交叉验证诊断报告",
        sections=_cv_report_sections(cv_result),
        raw_data=_report_raw(cv_result, skill_dir)).render()
_TREATMENT_COUNT_KEYS = (
    "executed", "succeeded", "fixed", "failed", "error", "rolled_back",
    "skipped", "fp_confirmed", "pending_confirm", "suggestion", "no_fixer",
    "ai_fixed",
)
_TREATMENT_EXEC_COUNT_KEYS = ("total", *_TREATMENT_COUNT_KEYS)
_TREATMENT_FIX_STATUS_GROUPS = {
    "applied": frozenset({"applied", *TX_FIXED_STATUSES}),
    "failed": frozenset({*TX_FAILED_STATUSES, *TX_ROLLED_BACK_STATUSES}),
    "skipped": frozenset({
        "skipped", "fp_confirmed", "pending_confirm", "suggestion", "no_fixer",
    }),
}
def _text_scalar(value) -> str:
    if isinstance(value, str):
        return value.strip()
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return safe_text(value)
    return ""
def _seconds_text(value, *, unit: str = "s", digits: int = 2) -> str:
    num = _finite_number(value)
    if num is None:
        return "—"
    return f"{num:.{digits}f}{unit}"
def _number_text(value, *, digits: int = 1) -> str:
    num = _finite_number(value)
    if num is None:
        return "-"
    return f"{num:.{digits}f}"
def _treatment_alias_count(src: dict, canonical: str, alias: str) -> int:
    value = src.get(canonical)
    if value is None:
        value = src.get(alias)
    return _count_value(value)
def _treatment_canonical_stats(src: dict) -> dict:
    applied = (
        _count_value(src.get("applied"))
        + _treatment_alias_count(src, "succeeded", "fixed")
        + _count_value(src.get("ai_fixed"))
    )
    failed = (
        _treatment_alias_count(src, "failed", "error")
        + _count_value(src.get("rolled_back"))
    )
    skipped = sum(_count_value(src.get(status))
                  for status in _TREATMENT_FIX_STATUS_GROUPS["skipped"])
    if src.get("total") is not None:
        total = _count_value(src.get("total"))
    elif src.get("executed") is not None:
        total = _count_value(src.get("executed"))
    else:
        total = applied + failed + skipped
    return {
        "applied": applied,
        "failed": failed,
        "skipped": skipped,
        "total": total,
    }
def _treatment_fixes_stats(src: dict) -> dict:
    fixes = dict_items(src.get("fixes"))
    statuses = [text_or(f.get("status")).strip().lower() for f in fixes]
    stats = {
        group: sum(1 for status in statuses if status in members)
        for group, members in _TREATMENT_FIX_STATUS_GROUPS.items()
    }
    stats["total"] = len(fixes)
    return stats
def _treatment_exec_stats(src: dict) -> dict:
    outcome_keys = (k for k in _TREATMENT_EXEC_COUNT_KEYS if k != "total")
    if any(src.get(k) is not None for k in outcome_keys):
        return _treatment_canonical_stats(src)
    stats = _treatment_fixes_stats(src)
    if src.get("total") is not None:
        stats["total"] = _count_value(src.get("total"))
    return stats
def _pl_stages(pipeline_result: dict) -> dict:
    return {k: v for k, v in as_dict(pipeline_result.get("stages")).items()
           if isinstance(v, dict)}
_COMPLETE_STAGE_STATUSES = frozenset({"ok", "completed"})
def _pl_overview_section(pipeline_result: dict, stages: dict) -> ReportSection:
    stage_names = ["diagnosis", CAT_CROSS_VALIDATION, "fanout",
                   "treatment_plan", "treatment_execution", "review",
                   "feedback"]
    stage_labels = ["诊断", "交叉验证", "扇出", "治疗计划", "治疗执行",
                    "复盘", "反哺"]
    overview_stats = ""
    _incomplete: list[str] = []
    for key, label in zip(stage_names, stage_labels, strict=True):
        stage_data = stages.get(key) or {}
        status = safe_text(stage_data.get("status") or "unknown").strip().lower()
        if status not in _COMPLETE_STAGE_STATUSES:
            _incomplete.append(f"{label}（{status}）")
        css = status_badge_css(status)
        overview_stats += render_stat(
                render_badge(status, f"badge-{css}"),
                label)
    overview_html = f'<div class="stat-grid">{overview_stats}</div>'
    if _incomplete:
        overview_html += (
            '<div class="card" style="border-left:4px solid #e53e3e;'
            'background:#fff5f5"><h3 style="color:#c53030">'
            '⚠ 数据完整性告警</h3>'
            '<p>以下阶段未取得有效数据，对应段落为降级展示'
            '（非“全部正常”）：</p>'
            '<ul style="margin:8px 0 0 20px">'
            + "".join(f"<li>{_html.escape(item)}</li>"
                      for item in _incomplete)
            + '</ul></div>')
    total_time = _seconds_text(pipeline_result.get("total_time"))
    overview_html += (
        '<div class="card"><h3>总耗时</h3>'
        f'<p style="font-size:24px;color:#667eea;">{total_time}</p></div>')
    return ReportSection(
        title="管道概览", section_id="overview", icon="🏠", html_content=overview_html,
    )
def _pl_diagnosis_section(stages: dict) -> ReportSection:
    diag = _stage_report_or_top(as_dict(stages.get("diagnosis")))
    diag_findings = dict_items(diag.get("findings"))
    diag_html = f'<div class="stat-grid">{render_stat(len(diag_findings), "发现总数", "info")}</div>'
    if diag_findings:
        def _cell(f: dict, key: str, default: str = "") -> str:
            v = f.get(key)
            return default if v is None else safe_text(v)
        rows = []
        for f in diag_findings:
            _f_file, _f_line = extract_finding_coords(f)
            rows.append([
                _html.escape(_cell(f, "rule_id")),
                _html.escape(_cell(f, "severity", "P3")),
                _html.escape(_f_file),
                _html.escape(_f_line),
                _html.escape(_cell(f, "message")),
            ])
        diag_html += render_table(["规则", "级别", "文件", "行号", "描述"], rows,
                                    table_id="diag_table", initial_visible=50)
    return ReportSection(
        title="诊断结果", section_id="diagnosis", icon="🔬", html_content=diag_html,
    )
def _pl_cv_section(stages: dict) -> ReportSection:
    cv_stage = as_dict(stages.get(CAT_CROSS_VALIDATION))
    cv_rep = _stage_report_or_top(cv_stage)
    cv_data = (as_dict(cv_rep.get("data")) if "data" in cv_rep else cv_rep)
    if cv_data:
        cv_html = (f'<div class="stat-grid">'
                   f'{_cv_stat_tiles(_cv_counts(cv_data))}</div>')
    else:
        cv_html = empty_card("无CV数据")
    return ReportSection(
        title="交叉验证", section_id="cv", icon="⚖️", html_content=cv_html,
    )
def _fanout_gate_status(gate: dict) -> tuple[str, str]:
    if not gate:
        return "N/A", "badge-muted"
    if to_bool(gate.get("skipped")) and to_bool(gate.get("passed")):
        return "SKIPPED", "badge-muted"
    if to_bool(gate.get("passed")):
        return "PASS", "badge-success"
    return "BLOCK", "badge-danger"
def _governance_label_of(module: dict) -> str:
    label = text_or(module.get("governance_label")).strip()
    if label:
        return label
    level = text_or(module.get("governance_level")).strip().upper()
    return fanout_level_label(level)
def _dependency_degree_cell(module: dict) -> str:
    degree = _count_or_none(module.get("dependency_fanout"))
    return "-" if degree is None else str(degree)
def _role_label(module: dict) -> str:
    role = safe_text(module.get("module_role") or FANOUT_ROLE_MODULE)
    return safe_text(module.get("module_role_label")
                     or FANOUT_ROLE_LABELS.get(role, role))
def _module_rows_of(raw) -> list[dict]:
    rows = [item for item in (as_dict(entry) for entry in as_list(raw)) if item]
    rows.sort(key=lambda item: (-to_int(item.get("total")),
                                safe_text(item.get("module"))))
    return rows
def _pl_fanout_module_row(item) -> list[str]:
    module = as_dict(item)
    return [
        esc_or(module.get("module"), "-"),
        str(to_int(module.get("total"))),
        str(to_int(module.get("exact"))),
        str(to_int(module.get("variant"))),
        str(to_int(module.get("new_sites"))),
        _dependency_degree_cell(module),
        esc_or(_role_label(module)),
        esc_or(_governance_label_of(module)),
        f"{to_finite_float(module.get('share')):.1f}%",
    ]
def _pl_fanout_section(stages: dict) -> ReportSection:
    fanout_stage = as_dict(stages.get("fanout"))
    data = _stage_report_or_top(fanout_stage)
    if not data:
        return ReportSection(
            title="扇出诊断与治疗", section_id="fanout", icon="🌊",
            html_content=empty_card("无扇出数据"))
    summary = as_dict(data.get("summary"))
    gate = as_dict(data.get("gate"))
    tiers = as_dict(summary.get("governance_tiers"))
    stats = (
        render_stat(to_int(summary.get("families")), "同族组", "info")
        + render_stat(to_int(summary.get("occurrences")), "位点", "info")
        + render_stat(to_int(summary.get("exact")), "exact", "danger")
        + render_stat(to_int(summary.get("variant")), "variant", "warning")
        + render_stat(to_int(summary.get("new_sites")), "新增", "success")
        + render_stat(to_int(as_dict(tiers.get("level_modules")).get(
            FANOUT_LEVEL_L4)), "L4 危机模块", "danger")
        + render_stat(to_int(tiers.get("advisory_modules")),
                      "L1-L3 模块", "info")
    )
    gate_label, gate_css = _fanout_gate_status(gate)
    enforcement = esc_or(gate.get("enforcement"))
    block_note = ("治疗前强制阻断" if enforcement == "blocking" else "仅登记")
    _uncovered = gate.get("uncovered")
    if _uncovered is None:
        _uncovered = gate.get("residual", 0)
    html_content = (
        f'<div class="stat-grid">{stats}</div>'
        f'<div class="card"><h3>阶段G · 扇出诊断与治疗</h3>'
        f'<p>门禁 {render_badge(gate_label, gate_css)}'
        f' · 口径 <code>{enforcement or "-"}</code>（{block_note}）'
        f' · 未覆盖 {to_int(_uncovered)}'
        f' · 涉及模块 {len(as_list(summary.get("module_counts")))}'
        f' · 残留 {to_int(gate.get("residual"))}'
        f'（建议性 {to_int(gate.get("advisory_residual"))}）'
        f' · L4/L1-L3 模块 '
        f'{to_int(as_dict(tiers.get("level_modules")).get(FANOUT_LEVEL_L4))}/'
        f'{to_int(tiers.get("advisory_modules"))}'
        f' · 治理策略 '
        f'<code>{esc_or(data.get("stage_label") or "代码迁移 > 统一入口 > 分层与边界调整", "-")}</code></p>'
        f'<p style="color:#718096;font-size:13px;">'
        f'禁止动作：split_file / split_module；报告 '
        f'<code>{esc_or(data.get("report_path") or "-", "-")}</code></p></div>')
    strategies = as_dict(summary.get("strategies"))
    strategy_rows = [
        [strategy, str(to_int(strategies.get(strategy, 0)))]
        for strategy in FANOUT_STRATEGIES
    ]
    html_content += render_table(
        ["治理策略", "族数"], strategy_rows,
        table_id="pl_fanout_strategy_table")
    _pl_modules = _module_rows_of(summary.get("module_counts"))
    if not _pl_modules:
        _pl_modules = _module_rows_of(fanout_module_counts(data))
    module_rows = [_pl_fanout_module_row(item) for item in _pl_modules[:10]]
    if module_rows:
        html_content += (
            f'<div class="card"><h3>模块扇出数量（Top {len(module_rows)}）</h3>'
            f'<p style="color:#718096;font-size:13px;">'
            f'按位点总数降序；{_html.escape(FANOUT_GOVERNANCE_RULE)}；'
            f'完整明细见阶段G报告。</p></div>')
        html_content += render_table(
            ["模块", "位点", "exact", "variant", "新增",
             "依赖扇出", "角色", "治理档位", "占比"],
            module_rows, table_id="pl_fanout_module_table")
    return ReportSection(
        title="扇出诊断与治疗", section_id="fanout", icon="🌊",
        html_content=html_content)
_FANOUT_LEVEL_BADGE = {
    "exact": "badge-danger",
    "variant": "badge-warning",
    "weak": "badge-info",
    "seed": "badge-success",
}
_FANOUT_STRATEGY_COLORS = {
    "code_migration": "#38a169",
    "unified_entry": "#3182ce",
    "layer_boundary": "#dd6b20",
}
_FANOUT_MODULE_ROWS_CAP = DISCLOSURE_ROWS_WIDE
_FANOUT_OCCURRENCE_ROWS_CAP = DISCLOSURE_ROWS_WIDE * 5
def _fanout_status_badge(report: dict) -> str:
    raw = safe_text(report.get("status") or "completed").strip() or "completed"
    css = {
        "completed": "badge-success",
        "degraded": "badge-warning",
        "skipped": "badge-muted",
        "error": "badge-danger",
    }.get(raw.lower(), "badge-info")
    return render_badge(raw, css)
def _fanout_overview_section(report: dict) -> ReportSection:
    summary = as_dict(report.get("summary"))
    tiers = as_dict(summary.get("governance_tiers"))
    stats = (
        render_stat(to_int(summary.get("families")), "同族组", "info")
        + render_stat(to_int(summary.get("occurrences")), "位点总数", "info")
        + render_stat(to_int(summary.get("exact")), "exact", "danger")
        + render_stat(to_int(summary.get("variant")), "variant", "warning")
        + render_stat(to_int(summary.get("weak")), "weak", "muted")
        + render_stat(to_int(summary.get("new_sites")), "新增位点", "success")
        + render_stat(to_int(summary.get("guarded")), "局部守卫", "warning")
        + render_stat(to_int(summary.get("files_scanned")), "扫描文件", "info")
        + render_stat(to_int(tiers.get("excluded_sites")),
                      "排除面位点", "muted")
    )
    trace = (
        f"<div class='card'><h3>阶段身份</h3>"
        f"<p>阶段 <strong>{_html.escape(safe_text(report.get('stage_id') or 'G'))}</strong>"
        f" · {_html.escape(safe_text(report.get('stage_label') or '扇出诊断与治疗'))}</p>"
        f"<p>状态 {_fanout_status_badge(report)}"
        f" · 轮次锚 <code>{_html.escape(safe_text(report.get('round_start_ts') or '-'))}</code>"
        f" · 生成时间 {_html.escape(safe_text(report.get('generated_at') or '-'))}</p>"
        f"</div>"
    )
    return ReportSection(
        title="阶段G概览", section_id="fanout_overview", icon="🌊",
        html_content=f'<div class="stat-grid">{stats}</div>{trace}')
def _fanout_strategy_section(report: dict) -> ReportSection:
    summary = as_dict(report.get("summary"))
    strategies = as_dict(summary.get("strategies"))
    total = sum(to_int(strategies.get(strategy, 0))
                for strategy in FANOUT_STRATEGIES) or 1
    cards = []
    for strategy in FANOUT_STRATEGIES:
        count = to_int(strategies.get(strategy, 0))
        label = FANOUT_STRATEGY_LABELS.get(strategy, strategy)
        method = FANOUT_STRATEGY_GOVERNANCE.get(strategy, "")
        pct = count / total * 100
        cards.append(
            f"<div class='card'><h3>{_html.escape(label)} "
            f"{render_badge(safe_text(count))}</h3>"
            f"<p>治理方法 <code>{_html.escape(method)}</code>"
            f" · 族占比 {pct:.1f}%</p>"
            f"{render_progress_bar(count, total, _FANOUT_STRATEGY_COLORS.get(strategy, '#667eea'))}"
            f"</div>")
    forbidden = "".join(
        render_badge(action, "badge-danger")
        for action in FANOUT_FORBIDDEN_ACTIONS)
    html_content = (
        f"<div class='stat-grid'>{''.join(cards)}</div>"
        f"<div class='card'><h3>治理优先级</h3>"
        f"<p>代码迁移 &gt; 统一入口 &gt; 分层与边界调整；"
        f"拆分文件/模块恒为禁止动作：{forbidden}</p></div>")
    return ReportSection(
        title="策略分布", section_id="fanout_strategy", icon="🧭",
        html_content=html_content)
def _fanout_module_rows(modules: list) -> list[list[str]]:
    rows: list[list[str]] = []
    peak = max((to_int(as_dict(item).get("total")) for item in modules),
               default=0) or 1
    for raw in modules[:_FANOUT_MODULE_ROWS_CAP]:
        module = as_dict(raw)
        if not module:
            continue
        total = to_int(module.get("total"))
        level = safe_text(module.get("governance_level") or "unknown").strip().upper()
        level_label = _governance_label_of(module)
        level_css = {
            FANOUT_LEVEL_L4: "badge-danger",
            FANOUT_LEVEL_L3: "badge-warning",
            FANOUT_LEVEL_L2: "badge-info",
            FANOUT_LEVEL_L1: "badge-success",
        }.get(level, "badge-muted")
        role_label = _role_label(module)
        rows.append([
            ("<span class='path-cell'>"
             f"{_html.escape(safe_text(module.get('module') or ''))}</span>"),
            str(total),
            str(to_int(module.get("exact"))),
            str(to_int(module.get("variant"))),
            str(to_int(module.get("weak"))),
            str(to_int(module.get("new_sites"))),
            str(to_int(module.get("guarded"))),
            str(to_int(module.get("family_count"))),
            _dependency_degree_cell(module),
            _html.escape(role_label),
            render_badge(level_label, level_css),
            render_progress_bar(total, peak, "#4299e1"),
            f"{to_finite_float(module.get('share')):.1f}%",
        ])
    return rows
def _fanout_modules_section(report: dict) -> ReportSection:
    summary = as_dict(report.get("summary"))
    modules = _module_rows_of(summary.get("module_counts"))
    if not modules:
        modules = _module_rows_of(fanout_module_counts(report))
    if not modules:
        return ReportSection(
            title="模块扇出明细", section_id="fanout_modules", icon="📦",
            html_content=empty_card("无模块扇出数据"))
    totals = [to_int(item.get("total")) for item in modules]
    top = modules[0]
    stats = (
        render_stat(len(modules), "涉及模块", "info")
        + render_stat(max(totals, default=0), "单模块最多", "danger")
        + render_stat(f"{sum(totals) / len(totals):.1f}", "平均位点", "warning")
        + render_stat(sum(1 for item in modules
                          if safe_text(item.get("governance_level")).strip().upper()
                          == FANOUT_LEVEL_L4),
                      "L4 危机模块", "danger")
        + render_stat(sum(1 for item in modules
                          if safe_text(item.get("governance_level")).strip().upper()
                          in {FANOUT_LEVEL_L1, FANOUT_LEVEL_L2,
                              FANOUT_LEVEL_L3}),
                      "L1-L3 模块", "info")
    )
    headline = (
        f"<div class='card'><h3>扇出最集中的模块</h3>"
        f"<p><code>{_html.escape(safe_text(top.get('module') or '-'))}</code>"
        f" 聚合 {to_int(top.get('total'))} 个位点"
        f"（{to_finite_float(top.get('share')):.1f}%），"
        f"涵盖 {to_int(top.get('family_count'))} 个同族组</p>"
        f"<p style='color:#718096;font-size:13px;'>"
        f"模块排序：位点总数降序；占比 = 该模块位点 / 全部位点；"
        f"{_html.escape(FANOUT_GOVERNANCE_RULE)}。"
        f"</p></div>")
    rows = _fanout_module_rows(modules)
    hidden_count = max(0, len(modules) - len(rows))
    truncation_note = ""
    if hidden_count:
        truncation_note = (
            f"<div class='card'><p style='color:#b7791f;'>页内仅渲染前 "
            f"{len(rows)} 个模块，其余 {hidden_count} 个未展开；"
            f"完整明细见同名 JSON。</p></div>")
    return ReportSection(
        title=f"模块扇出明细 ({len(modules)})",
        section_id="fanout_modules", icon="📦",
        html_content=(
            f"<div class='stat-grid'>{stats}</div>{headline}{truncation_note}"
            + render_table(
                ["模块", "位点", "exact", "variant", "weak",
                 "新增", "守卫", "族数", "依赖扇出", "角色",
                 "治理档位", "分布", "占比"],
                rows,
                table_id="fanout_module_table", initial_visible=30)))
def _fanout_family_rows(families: list) -> list[list[str]]:
    rows: list[list[str]] = []
    for raw in families:
        family = as_dict(raw)
        if not family:
            continue
        counts = as_dict(family.get("counts"))
        governance = as_dict(family.get("governance"))
        seed = as_dict(family.get("seed"))
        rows.append([
            _html.escape(safe_text(family.get("family_id") or "")),
            _html.escape(safe_text(family.get("rule_id") or "")),
            _html.escape(safe_text(seed.get("seed_locator") or "")),
            _html.escape(safe_text(governance.get("label")
                                   or governance.get("strategy") or "")),
            _html.escape(safe_text(governance.get("governance_method") or "")),
            str(to_int(family.get("occurrence_count"))),
            str(to_int(counts.get("exact"))),
            str(to_int(counts.get("variant"))),
            str(to_int(counts.get("weak"))),
            str(to_int(family.get("new_site_count"))),
            str(to_int(family.get("guarded_count"))),
            str(len(as_list(family.get("files")))),
        ])
    return rows
def _fanout_families_section(report: dict) -> ReportSection:
    families = [item for item in
                (as_dict(raw) for raw in as_list(report.get("families"))) if item]
    if not families:
        return ReportSection(
            title="同族位点", section_id="fanout_families", icon="🧬",
            html_content=empty_card("无同族位点"))
    rows = _fanout_family_rows(families)
    return ReportSection(
        title=f"同族位点 ({len(rows)})", section_id="fanout_families",
        icon="🧬",
        html_content=render_table(
            ["族", "规则", "种子", "策略", "治理方法", "位点",
             "exact", "variant", "weak", "新增", "守卫", "文件"],
            rows, table_id="fanout_family_table", initial_visible=20))
def _fanout_occurrence_rows(occurrences: list) -> list[list[str]]:
    rows: list[list[str]] = []
    for raw in occurrences[:_FANOUT_OCCURRENCE_ROWS_CAP]:
        occurrence = as_dict(raw)
        if not occurrence:
            continue
        level = safe_text(occurrence.get("level") or "").strip().lower()
        line = _count_or_none(occurrence.get("line"))
        score = _number_text(occurrence.get("score"), digits=2)
        rows.append([
            _html.escape(safe_text(occurrence.get("family_id") or "")),
            render_badge(level or "none",
                         _FANOUT_LEVEL_BADGE.get(level, "badge-info")),
            _html.escape(safe_text(occurrence.get("file") or "")),
            "-" if line is None else str(line),
            _html.escape(safe_text(occurrence.get("scope_kind") or "")),
            render_badge("guarded", "badge-warning")
            if to_bool(occurrence.get("guarded")) else "—",
            score,
            "是" if to_bool(occurrence.get("is_new_site")) else "否",
            _html.escape(safe_text(occurrence.get("snippet") or "")),
        ])
    return rows
def _fanout_occurrences_section(report: dict) -> ReportSection:
    occurrences = [item for item in
                   (as_dict(raw) for raw in as_list(report.get("occurrences"))) if item]
    if not occurrences:
        return ReportSection(
            title="位点明细", section_id="fanout_occurrences", icon="📍",
            html_content=empty_card("无位点明细"))
    rows = _fanout_occurrence_rows(occurrences)
    hidden_count = max(0, len(occurrences) - len(rows))
    truncation_note = ""
    title = f"位点明细 ({len(occurrences)})"
    if hidden_count:
        title = f"位点明细 ({len(occurrences)}，页内 {len(rows)})"
        truncation_note = (
            f"<div class='card'><p style='color:#b7791f;'>页内仅渲染前 "
            f"{len(rows)} 条，其余 {hidden_count} 条未展开；完整 "
            f"{len(occurrences)} 条位点见同名 JSON。</p></div>")
    return ReportSection(
        title=title,
        section_id="fanout_occurrences", icon="📍",
        html_content=truncation_note + render_table(
            ["族", "级别", "文件", "行", "作用域", "守卫",
             "分数", "新增", "片段"],
            rows, table_id="fanout_occurrence_table", initial_visible=50))
def _fanout_handoff_section(report: dict) -> ReportSection:
    handoff = as_dict(as_dict(report.get("summary")).get("treatment_handoff"))
    if not handoff:
        return ReportSection(
            title="治疗交接", section_id="fanout_handoff", icon="🩹",
            html_content=empty_card("无治疗交接数据"))
    strategies = as_dict(handoff.get("strategies"))
    strategy_rows = [
        [FANOUT_STRATEGY_LABELS.get(strategy, strategy),
         FANOUT_STRATEGY_GOVERNANCE.get(strategy, ""),
         str(to_int(strategies.get(strategy, 0)))]
        for strategy in FANOUT_STRATEGIES
        if to_int(strategies.get(strategy, 0))
    ]
    stats = (
        render_stat(to_int(handoff.get("site_candidates")), "候选位点", "info")
        + render_stat(to_int(handoff.get("groups")), "治疗组", "success")
        + render_stat(to_int(handoff.get("members")), "组员", "info")
        + render_stat(to_int(handoff.get("seeds")), "种子", "warning")
    )
    methods = "".join(
        render_badge(safe_text(method))
        for method in as_list(handoff.get("governance_methods")))
    html_content = (
        f"<div class='stat-grid'>{stats}</div>"
        f"<div class='card'><h3>治理方法</h3><p>{methods or '—'}</p>"
        f"<p style='color:#718096;font-size:13px;'>阶段G只产出交接方案；"
        f"治疗项由阶段3b并入计划，写盘仍走 AI 审核通道。</p></div>")
    if strategy_rows:
        html_content += render_table(
            ["策略", "治理方法", "组数"], strategy_rows,
            table_id="fanout_handoff_table")
    return ReportSection(
        title="治疗交接", section_id="fanout_handoff", icon="🩹",
        html_content=html_content)
def _fanout_gate_section(report: dict) -> ReportSection:
    gate = as_dict(report.get("gate"))
    if not gate:
        return ReportSection(
            title="残留门禁", section_id="fanout_gate", icon="🚦",
            html_content=empty_card("未运行扇出残留门禁"))
    label, css = _fanout_gate_status(gate)
    residual = to_int(gate.get("residual"))
    stats = (
        render_stat(to_int(gate.get("total")), "门禁位点", "info")
        + render_stat(to_int(gate.get("handled")), "已终态", "success")
        + render_stat(residual, "残留", "danger" if residual else "success")
    )
    actions = as_list(gate.get("actions_required"))
    action_html = "".join(
        f"<li>{_html.escape(safe_text(action))}</li>" for action in actions)
    note = safe_text(gate.get("note") or "")
    html_content = (
        f"<div class='stat-grid'>{stats}</div>"
        f"<div class='card'><h3>门禁结论 {render_badge(label, css)}</h3>"
        f"<p>{_html.escape(note)}</p>"
        f"<p>原因 <code>{_html.escape(safe_text(gate.get('reason') or '—'))}</code>"
        f" · 阶段 <code>{_html.escape(safe_text(gate.get('phase') or '—'))}</code></p>"
        f"{('<ul>' + action_html + '</ul>') if action_html else ''}</div>")
    integrity = as_dict(gate.get("file_integrity"))
    if integrity:
        html_content += render_table(
            ["项", "值"],
            [[_html.escape(safe_text(key)), _html.escape(safe_text(value))]
             for key, value in integrity.items()],
            table_id="fanout_integrity_table")
    return ReportSection(
        title="残留门禁", section_id="fanout_gate", icon="🚦",
        html_content=html_content)
def _fanout_trace_section(report: dict) -> ReportSection:
    summary = as_dict(report.get("summary"))
    rows = [
        ("阶段", (f"{safe_text(report.get('stage_id') or 'G')} · "
                  f"{safe_text(report.get('stage_label') or '扇出诊断与治疗')}")),
        ("Schema", report.get("schema") or ""),
        ("轮次锚", report.get("round_start_ts") or ""),
        ("生成时间", report.get("generated_at") or ""),
        ("报告路径", report.get("report_path") or ""),
        ("来源报告", report.get("source_report_path") or ""),
        ("内容哈希", report.get("report_hash") or ""),
        ("扫描文件", to_int(summary.get("files_scanned"))),
        ("降级种子", len(as_list(report.get("degraded_seeds")))),
        ("错误", len(as_list(report.get("errors")))),
        ("文件面快照", len(as_list(report.get("file_universe")))),
    ]
    table = "".join(
        f"<tr><td style='width:28%;font-weight:600;'>{_html.escape(str(key))}</td>"
        f"<td>{_html.escape(safe_text(value))}</td></tr>"
        for key, value in rows)
    html_content = (
        f"<div class='card'><table>{table}</table></div>")
    degraded = [item for item in
                (as_dict(raw) for raw in as_list(report.get("degraded_seeds"))) if item]
    if degraded:
        html_content += render_table(
            ["种子", "原因", "描述"],
            [[_html.escape(safe_text(as_dict(item).get("seed") or "")),
              _html.escape(safe_text(as_dict(item).get("reason") or "")),
              _html.escape(safe_text(as_dict(item).get("description") or ""))]
             for item in degraded],
            table_id="fanout_degraded_table")
    errors = [item for item in
              (as_dict(raw) for raw in as_list(report.get("errors"))) if item]
    if errors:
        html_content += render_table(
            ["文件", "错误"],
            [[_html.escape(str(as_dict(item).get("file") or "")),
              _html.escape(str(as_dict(item).get("error") or ""))]
             for item in errors],
            table_id="fanout_error_table")
    return ReportSection(
        title="可追溯信息", section_id="fanout_trace", icon="🔗",
        html_content=html_content)
def _fanout_report_sections(report: dict) -> list[ReportSection]:
    return [
        _fanout_overview_section(report),
        _fanout_modules_section(report),
        _fanout_families_section(report),
        _fanout_occurrences_section(report),
        _fanout_strategy_section(report),
        _fanout_handoff_section(report),
        _fanout_gate_section(report),
        _fanout_trace_section(report),
    ]
def render_fanout_report_html(report: dict, skill_dir: str = _DEFAULT_SKILL_DIR) -> str:
    report = as_dict(report)
    return HTMLReport(
        title="扇出诊断与治疗报告（阶段G）",
        sections=_fanout_report_sections(report),
        raw_data=_report_raw(report, skill_dir)).render()
def _pl_treatment_section(stages: dict) -> ReportSection:
    exec_stage = as_dict(stages.get("treatment_execution"))
    _exec_src = _stage_report_or_top(exec_stage)
    _exec_stats = _treatment_exec_stats(_exec_src)
    exec_html = (
        f'<div class="stat-grid">'
        f'{render_stat(_exec_stats["applied"], "已修复", "success")}'
        f'{render_stat(_exec_stats["failed"], "失败回滚", "danger")}'
        f'{render_stat(_exec_stats["skipped"], "待定跳过", "muted")}'
        f'{render_stat(_exec_stats["total"], "总计", "info")}'
        f'</div>'
    )
    return ReportSection(
        title="治疗执行", section_id="treatment", icon="🔧", html_content=exec_html,
    )
def _pl_review_section(stages: dict) -> ReportSection:
    review_stage = as_dict(stages.get("review"))
    rev_data = _stage_report_or_top(review_stage)
    _rev_score = rev_data.get("score")
    _rev_grade = rev_data.get("grade")
    if isinstance(_rev_score, bool):
        _rev_score = None
    if isinstance(_rev_grade, bool):
        _rev_grade = None
    if _rev_score not in (None, "") or _rev_grade not in (None, ""):
        _rev_score_disp = (scalar_detail(_rev_score)
                           if _rev_score not in (None, "") else "—")
        _rev_grade_disp = (_html.escape(str(_rev_grade))
                           if _rev_grade not in (None, "") else "—")
        rev_stats = (
            render_stat(_rev_score_disp, "复盘评分", "info")
            + render_stat(_rev_grade_disp, "复盘等级", "success")
        )
        rev_html = f'<div class="stat-grid">{rev_stats}</div>'
    else:
        rev_html = empty_card("无复盘数据")
    return ReportSection(
        title="复盘", section_id="review", icon="🎯", html_content=rev_html,
    )
def _pl_feedback_section(stages: dict) -> ReportSection:
    feedback = as_dict(stages.get("feedback"))
    _fb_rep = feedback.get("report")
    fb_data = feedback if _fb_rep is None else _fb_rep
    if isinstance(fb_data, dict):
        coord = as_dict(fb_data.get("coordinator"))
        # 协调器状态视图（pipeline_report_delivery._coordinator_status_report）只产出
        # tracked_parameters / session_count / frozen / conflicts 四个计数键。
        fb_stats = (
            render_stat(to_int(coord.get("tracked_parameters", 0)),
                        "跟踪参数", "success")
            + render_stat(to_int(coord.get("session_count", 0)),
                          "会话数", "info")
            + render_stat(to_int(coord.get("frozen", 0)), "冻结", "warning")
            + render_stat(to_int(coord.get("conflicts", 0)), "冲突", "danger")
        )
        for _fb_key, _fb_label in (
                ("fupan_quality_score", "复盘质量分"),
                ("fupan_memory_ops", "记忆操作"),
                ("diagnosis_feedbacks", "诊断反馈"),
                ("cv_feedbacks", "CV 反馈"),
                ("fixer_feedbacks", "修复器反馈"),
                ("code_feedback_l1_applied", "代码反哺 L1")):
            _fb_val = fb_data.get(_fb_key)
            if isinstance(_fb_val, bool) or _fb_val in (None, ""):
                continue
            if _finite_number(_fb_val) is None:
                continue
            fb_stats += render_stat(_html.escape(str(_fb_val)), _fb_label, "info")
        fb_html = f'<div class="stat-grid">{fb_stats}</div>'
    else:
        fb_html = empty_card("无反馈数据")
    return ReportSection(
        title="反馈协调", section_id="feedback", icon="🔄", html_content=fb_html,
    )
def _pl_report_sections(pipeline_result: dict,
                        stages: dict) -> list[ReportSection]:
    return [
        _pl_overview_section(pipeline_result, stages),
        _pl_diagnosis_section(stages),
        _pl_cv_section(stages),
        _pl_fanout_section(stages),
        _pl_treatment_section(stages),
        _pl_review_section(stages),
        _pl_feedback_section(stages),
    ]
def render_pipeline_report_html(pipeline_result: dict, skill_dir: str = _DEFAULT_SKILL_DIR) -> str:
    pipeline_result = as_dict(pipeline_result)
    logger.debug("[HtmlReport] render_pipeline_report_html 渲染: pipeline_result=%d 键", len(pipeline_result))
    stages = _pl_stages(pipeline_result)
    return HTMLReport(
        title="完整诊断管道报告",
        sections=_pl_report_sections(pipeline_result, stages),
        raw_data=_report_raw(pipeline_result, skill_dir)).render()
def _name_part(result: dict, *keys: str, fallback: str) -> str:
    for k in keys:
        v = result.get(k)
        if v is not None:
            return safe_text(v)
    return fallback
@dataclass(frozen=True)
class _TypeMeta:
    stage: str
    icon: str
    title: str = ""
_TYPE_META: dict[str, _TypeMeta] = {
    "single_method": _TypeMeta("diag", "🔬"),
    "cv": _TypeMeta("cv", "🧪", "交叉验证报告"),
    "fanout": _TypeMeta("fanout", "🌊", "阶段G扇出诊断与治疗报告"),
    "treatment_item": _TypeMeta("treat_review", "🩹"),
    "ai_review": _TypeMeta("treat_review", "🤖"),
    "fupan": _TypeMeta("retro_feedback", "🔄", "复盘报告"),
    "retro": _TypeMeta("retro_feedback", "♻️", "反哺进化报告"),
    "pipeline": _TypeMeta("final", "🧭", "管线报告"),
    "pipeline_summary": _TypeMeta("final", "🏁", "全流程汇总"),
    "coverage": _TypeMeta("treat_review", "📊", "覆盖报告"),
    "batch": _TypeMeta("final", "📦", "批量推进总览"),
    "degradation": _TypeMeta("final", "⚠️", "管线降级报告"),
}
_TYPE_META_FALLBACK = _TypeMeta("", "📄")
def _meta_for(report_type: str) -> _TypeMeta:
    return _TYPE_META.get(report_type, _TYPE_META_FALLBACK)
_STEP_STAGE_RULES: tuple[tuple[str, str], ...] = (
    ("cv", "cv"),
    ("regression", "cv"),
    ("fupan", "retro_feedback"),
    ("feedback", "retro_feedback"),
    ("enhance", "retro_feedback"),
    ("enhancement", "retro_feedback"),
    ("retro", "retro_feedback"),
    ("evolution", "retro_feedback"),
    ("treatment", "treat_review"),
    ("review", "treat_review"),
    ("adjust", "treat_review"),
    ("cleanup", "treat_review"),
    ("coexistence", "treat_review"),
    ("fix", "treat_review"),
    ("dry", "treat_review"),
    ("refactor", "treat_review"),
    ("stub", "treat_review"),
    ("preintervention", "treat_review"),
    ("fanout", "fanout"),
    ("diag", "diag"),
    ("coverage", "final"),
    ("perf", "final"),
    ("pipeline", "final"),
    ("diagnosis", "final"),
)
_STEP_STAGE_TOKEN_RE = re.compile(r"[a-z0-9]+")
def _step_stage(result: dict) -> str:
    name = str(result.get("_step_name") or "").lower()
    tokens = set(_STEP_STAGE_TOKEN_RE.findall(name))
    for key, stage in _STEP_STAGE_RULES:
        if key in tokens:
            return stage
    return ""
def _route_type_stage(report_type: str, result: dict) -> tuple[str, str] | None:
    stage = _meta_for(report_type).stage
    mid = ""
    if not stage and report_type == "step":
        stage = _step_stage(result)
    # 诊断阶段按方法字母（A–F）分文件：step 路由到 diag 时同样要带
    # method_id，否则诊断A–F 会退化成同一个“诊断<ts>.html”。
    if stage == "diag":
        mid = _name_part(result, "method_id", fallback="")
    if not stage:
        return None
    return (stage, mid)
def _safe_mid(value) -> str:
    _m = str(value).strip() if value is not None else ""
    return safe_filename(_m) if _m else ""
def _route_stage(report_type: str, result: dict) -> tuple[str, str] | None:
    hint = result.get("_stage_hint") if isinstance(result, dict) else None
    if isinstance(hint, str) and hint:
        if hint == "suppress":
            return None
        if hint.startswith("diag:"):
            return ("diag", _safe_mid(hint.split(":", 1)[1]))
        if hint in STAGES:
            return (hint, "")
    route = _route_type_stage(report_type, result)
    if route is None:
        return None
    return (route[0], _safe_mid(route[1]))
def _stage_item_title(report_type: str, result: dict) -> str:
    if report_type == "single_method":
        return f"诊断方法 {_name_part(result, 'method_id', fallback='?')} 报告"
    if report_type == "ai_review":
        return f"AI 审核 {_name_part(result, 'review_id', fallback='item')}"
    if report_type == "treatment_item":
        return f"治疗项 #{_name_part(result, 'item_index', 'index', fallback='?')}"
    if report_type == "step":
        return f"步骤 {_name_part(result, '_step_name', fallback='step')}"
    return _meta_for(report_type).title or report_type
def _render_with_fallback(render_fn, report_type: str, result: dict,
                          skill_dir: str) -> tuple[str, bool]:
    try:
        return render_fn(result, skill_dir), False
    except Exception as _re:
        _err = f"{type(_re).__name__}: {_re}"
        logger.exception("[HTMLReport] %s 主渲染链失败，降级 fallback HTML: %s",
                         report_type, _err)
        return render_fallback_html(report_type, result, _err), True
def _emit_stage_report(report_type: str, stage: str, mid: str,
                       result: dict, skill_dir: str,
                       html_content: str) -> str:
    try:
        return emit_to_stage(
            stage, skill_dir, _stage_item_title(report_type, result),
            html_content, mid=mid, icon=_meta_for(report_type).icon,
            payload=result, report_type=report_type)
    except Exception as _ee:
        logger.warning("[HTMLReport] %s 阶段聚合发射异常(不阻断): %s",
                       report_type, _ee)
        return ""
def _resolve_render_fn(report_type: str, result: dict) -> tuple[str, Callable | None]:
    if not isinstance(report_type, str):
        return report_type, None
    if report_type == "auto":
        report_type = "pipeline" if "stages" in result else "cv"
    return report_type, _REPORT_RENDERERS.get(report_type)
def _emit_consolidated_report(report_type: str, result: dict, skill_dir: str,
                              html_content: str, degraded: bool) -> dict:
    route = _route_stage(report_type, result)
    if route is None:
        logger.info("[HTMLReport] %s 报告按阶段整合口径抑制"
                    "（超阶段独立调用不产生 HTML）", report_type)
        return {"status": "ok",
                "data": {"html": "", "path": "", "degraded": degraded,
                         "suppressed": "stage_consolidation"}}
    stage, mid = route
    filepath = _emit_stage_report(report_type, stage, mid, result,
                                  skill_dir, html_content)
    if not filepath:
        logger.warning("[HTMLReport] %s 阶段聚合落盘失败(不阻断)", report_type)
    else:
        logger.info("[HTMLReport] 已生成 %s 报告%s（阶段聚合 %s）: %s",
                    report_type, "（降级兜底）" if degraded else "",
                    stage, filepath)
    json_path = ""
    if filepath:
        try:
            candidate = stage_json_artifact_path(filepath, skill_dir)
            json_path = candidate if os.path.isfile(candidate) else ""
        except (OSError, RuntimeError, ValueError):
            logger.debug("阶段配套 JSON 路径解析失败", exc_info=True)
    return {"status": "ok", "data": {
        "html": html_content, "path": filepath, "json_path": json_path,
        "degraded": degraded, "stage": stage}}
def generate_html_report(
    result: dict,
    skill_dir: str = _DEFAULT_SKILL_DIR,
    report_type: str = "auto",
) -> dict:
    result = as_dict(result)
    report_type, render_fn = _resolve_render_fn(report_type, result)
    if render_fn is None:
        return {"status": "error",
                "message": f"未知报告类型: {report_type}", "data": None}
    html_content, degraded = _render_with_fallback(
        render_fn, report_type, result, skill_dir)
    return _emit_consolidated_report(
        report_type, result, skill_dir, html_content, degraded)
def html_report_path(html_result) -> str:
    data = as_dict(html_result).get("data")
    path = as_dict(data).get("path")
    return path.strip() if isinstance(path, str) else ""
_STAGE_TIMELINE_LABELS = ("诊断", "回归CV", "主CV", "扇出", "治疗计划",
                          "治疗执行", "AI修复", "复盘", "反哺", "全部完成")
_STAGE_TIMELINE_RANKS = (1, 3, 4, 5, 6, 7, 8, 9, 10, 11)
# 相位 → 「当前正在推进/等待的阶段」在 _STAGE_TIMELINE_RANKS 中的秩；
# 口径与 pipeline_round_trace._PHASE_LABELS 的「阶段N完成: 等待X」一致（X 即当前阶段）。
_PHASE_RANK = {
    "pending_diagnosis": 1, "diagnosis_done": 3,
    "cv_regression_done": 4, "cv_main_done": 5, "fanout_done": 6,
    "plan_dry_done": 6, "plan_generated": 7, "treatment_done": 8,
    "ai_fix_pending": 8, "ai_fix_done": 9, "review_done": 10,
    "fupan_done": 10, "feedback_done": 10, "code_feedback_done": 10,
    "evolution_pending": 10, "all_completed": 11,
}
def _stage_badge(label: str, rank: int, cur_rank: int) -> str:
    if cur_rank >= _STAGE_TIMELINE_RANKS[-1] or rank < cur_rank:
        css, mark = "success", "✔"
    elif rank == cur_rank:
        css, mark = "warning", "▶"
    else:
        css, mark = "muted", "·"
    return f"<span class='badge badge-{css}' style='margin:2px'>{mark} {label}</span>"
def _stage_meta_rows(progress: dict, phase: str,
                     summary_data: dict) -> list[tuple[str, str]]:
    return [
        ("管线阶段", esc_or(progress.get("phase_label") or phase, "-")),
        ("状态哈希", (f"<span class='path-cell'>"
         f"{esc_or(progress.get('source_hash'), '-')}</span>")),
        ("完成时间", esc_or(summary_data.get("timestamp"), "-")),
    ]
def _stage_timeline_section(progress: dict, phase: str, summary_data: dict) -> ReportSection:
    cur_rank = _PHASE_RANK.get(phase, 0)
    badges = [_stage_badge(label, rk, cur_rank)
              for label, rk in zip(_STAGE_TIMELINE_LABELS,
                                   _STAGE_TIMELINE_RANKS, strict=True)]
    return ReportSection(
        title="阶段状态（含阶段G）", section_id="stages", icon="🧭",
        html_content=f"<div class='card'><p>{''.join(badges)}</p>"
                     f"<div style='margin-top:12px'>"
                     f"{kv_table_preescaped(_stage_meta_rows(progress, phase, summary_data))}"
                     f"</div></div>")
@dataclass(frozen=True)
class _SummaryFacts:
    raw: dict
    skill_dir: str
    progress: dict
    diag: dict
    treat: dict
    cv_stats: dict
    artifacts: list
    report_dir: str
    phase: str
    @classmethod
    def of(cls, summary_data: dict, skill_dir: str) -> _SummaryFacts:
        summary_data = as_dict(summary_data)
        progress = as_dict(summary_data.get("progress"))
        artifacts = summary_data.get("artifacts")
        if artifacts is None:
            artifacts = collect_html_artifacts(
                skill_dir, summary_data.get("extra_dirs"))
        report_dir = text_or(summary_data.get("report_dir"))
        return cls(
            raw=summary_data,
            skill_dir=skill_dir,
            progress=progress,
            diag=as_dict(progress.get("diagnosis")),
            treat=as_dict(progress.get("treatment")),
            cv_stats=as_dict(summary_data.get("cv_stats")),
            artifacts=as_list(artifacts),
            report_dir=report_dir,
            phase=text_or(progress.get("phase")),
        )
def _summary_overview_section(facts: _SummaryFacts) -> ReportSection:
    diag_total = to_int(facts.diag.get("total"))
    diag_done = to_int(facts.diag.get("completed"))
    treat_total = _count_value(facts.treat.get("total"))
    treat_exec = _count_value(facts.treat.get("executed"))
    ai_fixed = _count_value(facts.treat.get("ai_fixed"))
    findings_count = _count_or_none(facts.raw.get("findings_count"))
    cv_confirmed = _count_or_none(facts.cv_stats.get("confirmed"))
    cv_suppressed = _count_or_none(facts.cv_stats.get("suppressed"))
    diag_text = f"{diag_done}/{diag_total}"
    diag_css = "success" if diag_done >= diag_total > 0 else "info"
    treat_text = f"{treat_exec}/{treat_total}"
    findings_text = "-" if findings_count is None else str(findings_count)
    confirmed_text = "-" if cv_confirmed is None else str(cv_confirmed)
    suppressed_text = "-" if cv_suppressed is None else str(cv_suppressed)
    overview = (
        f"{render_stat(diag_text, '诊断方法完成', diag_css)}"
        f"{render_stat(findings_text, '发现总数', 'warning')}"
        f"{render_stat(confirmed_text, 'CV已确认', 'danger')}"
        f"{render_stat(suppressed_text, 'CV已抑制', 'info')}"
        f"{render_stat(treat_text, '治疗项执行', 'info')}"
        f"{render_stat(ai_fixed, 'AI修复落地', 'success')}"
    )
    return ReportSection(
        title="执行概览", section_id="overview", icon="🏁",
        html_content=f"<div class='stat-grid'>{overview}</div>")
def _summary_sections(facts: _SummaryFacts) -> list[ReportSection]:
    return [
        _summary_overview_section(facts),
        _stage_timeline_section(facts.progress, facts.phase, facts.raw),
        ReportSection(
            title="治疗计数器", section_id="treatment", icon="💉",
            html_content="<div class='card'>" + kv_table(
                [(k, _count_value(facts.treat.get(k)))
                 for k in _TREATMENT_COUNT_KEYS]
            ) + "</div>"),
        artifacts_section(facts.artifacts, facts.report_dir),
    ]
def render_pipeline_summary_html(summary_data: dict, skill_dir: str = _DEFAULT_SKILL_DIR) -> str:
    facts = _SummaryFacts.of(summary_data, skill_dir)
    rep = HTMLReport(title="全流程审计总报告（诊断→CV→治疗→AI修复→复盘→反哺）",
                     sections=_summary_sections(facts),
                     raw_data=_report_raw(facts.raw, facts.skill_dir))
    return rep.render()
_BATCH_STEPS_SHOW_CAP = DISCLOSURE_ROWS_WIDE
def _batch_stopped_card(reason: str) -> str:
    if not reason:
        return ""
    return (f"<div class='card'><h3>停止原因</h3>"
            f"<p style='color:#e53e3e;font-weight:600;'>"
            f"{_html.escape(reason)}</p>"
            f"<p style='color:#718096;font-size:13px;'>任一步骤 blocked/failed/"
            f"error 即停（透传 AI 接续处理）；可切回逐步模式接续。</p></div>")
def _batch_next_action_card(action: str) -> str:
    if not action:
        return ""
    return (f"<div class='card'><h3>接续动作</h3>"
            f"<p><code>{_html.escape(action)}</code></p></div>")
def _batch_overview_section(result: dict) -> ReportSection:
    status = text_or(result.get("status"), "unknown")
    phase = text_or(result.get("phase"), "unknown")
    steps_executed = to_int(result.get("steps_executed"))
    treat_n = to_int(result.get("treatment_items_executed"))
    reused = to_bool(result.get("diagnosis_reused"))
    diagnosis_source = '复用' if reused else '新诊断'
    diagnosis_css = 'info' if reused else 'success'
    stat_cls = status_badge_css(status)
    elapsed_text = _seconds_text(result.get("elapsed_s"), unit="", digits=1)
    stats = (
        f"{render_stat(_html.escape(status), '批次状态', stat_cls)}"
        f"{render_stat(_html.escape(phase), '停止阶段', 'info')}"
        f"{render_stat(steps_executed, '执行步数', 'info')}"
        f"{render_stat(treat_n, '治疗项执行', 'info')}"
        f"{render_stat(diagnosis_source, '诊断来源', diagnosis_css)}"
        f"{render_stat(elapsed_text, '总耗时(秒)', 'info')}"
    )
    overview_html = (f"<div class='stat-grid'>{stats}</div>"
                     + _batch_stopped_card(text_or(result.get("stopped_reason")))
                     + _batch_next_action_card(text_or(result.get("next_action"))))
    return ReportSection(
        title="执行概览", section_id="overview", icon="🚀",
        html_content=overview_html)
def _batch_step_row(i: int, st: dict) -> list:
    _st_status = text_or(st.get("status"), "-")
    _st_cls = status_badge_css(_st_status, default="warning")
    _mid = st.get("method_id")
    _mid_text = safe_text(_mid).strip() if _mid is not None else ""
    _sub = _mid if _mid_text else st.get("index")
    if _sub is None:
        _sub = ""
    _fc = st.get("findings_count")
    return [
        str(i),
        esc_or(st.get("task_type"), "-"),
        _html.escape(str(_sub)) if _sub != "" else "-",
        f"<span class='badge badge-{_st_cls}'>{_html.escape(_st_status)}</span>",
        _html.escape(str(_fc)) if _fc is not None else "-",
        _number_text(st.get("elapsed_s")),
    ]
def _batch_steps_section(result: dict) -> ReportSection:
    step_results = as_list(result.get("step_results"))
    rows = [_batch_step_row(i, st) for i, st in enumerate(step_results, 1)
            if isinstance(st, dict)]
    if rows:
        steps_html = ("<div class='card'>"
                      + render_table(
                          ["#", "步骤类型", "方法/索引", "状态", "发现数", "耗时(秒)"],
                          rows, table_id="tbl_batch_steps",
                          initial_visible=_BATCH_STEPS_SHOW_CAP)
                      + "</div>")
    else:
        steps_html = empty_card("无步骤轨迹数据")
    return ReportSection(
        title=f"步骤轨迹（{len(rows)} 步）",
        section_id="steps", icon="🧾", html_content=steps_html)
def _batch_progress_section(result: dict) -> ReportSection | None:
    progress = result.get("progress")
    if not (isinstance(progress, dict) and progress):
        return None
    diag = as_dict(progress.get("diagnosis"))
    treat = as_dict(progress.get("treatment"))
    _diag_t = to_int(diag.get("total"))
    _diag_d = to_int(diag.get("completed"))
    _treat_t = to_int(treat.get("total"))
    _treat_e = to_int(treat.get("executed"))
    prog_stats = (
        f"{render_stat(f'{_diag_d}/{_diag_t}', '诊断方法', 'info')}"
        f"{render_stat(f'{_treat_e}/{_treat_t}', '治疗项', 'info')}"
        f"{render_stat(esc_or(progress.get('phase'), '-'), '管线阶段', 'info')}"
    )
    prog_html = (f"<div class='stat-grid'>{prog_stats}</div>"
                 f"<div class='card'><h3>阶段说明</h3><p style='color:#4a5568;'>"
                 f"{_html.escape(text_or(progress.get('phase_label')))}</p></div>")
    return ReportSection(
        title="管线进度", section_id="progress", icon="🧭",
        html_content=prog_html)
def render_batch_report_html(result: dict, skill_dir: str = _DEFAULT_SKILL_DIR) -> str:
    if not isinstance(result, dict):
        result = {"status": "error",
                  "stopped_reason": f"非法输入类型: {type(result).__name__}"}
    title = "批量推进总报告（run_pipeline_batch）"
    sections: list[ReportSection] = [
        _batch_overview_section(result),
        _batch_steps_section(result),
    ]
    _prog_sec = _batch_progress_section(result)
    if _prog_sec is not None:
        sections.append(_prog_sec)
    rep = HTMLReport(title=title, sections=sections,
                     raw_data=_report_raw(result, skill_dir))
    return rep.render()
_REPORT_RENDERERS: dict[str, Callable[[dict, str], str]] = {
    "pipeline": render_pipeline_report_html,
    "coverage": lambda _r, s: render_coverage_report_html(s),
    "degradation": render_degradation_report_html,
    "cv": render_cv_report_html,
    "single_method": render_single_method_html,
    "treatment_item": render_treatment_item_html,
    "step": lambda r, s: render_feedback_step_html(
        r, s, _name_part(r, '_step_name', fallback='step')),
    "pipeline_summary": render_pipeline_summary_html,
    "ai_review": render_ai_review_html,
    "fupan": lambda r, s: render_fupan_report_html(r, "", skill_dir=s),
    "batch": render_batch_report_html,
    "retro": render_retro_report_html,
    "fanout": render_fanout_report_html,
}
def emit_single_method_html(result: dict, skill_dir: str) -> None:
    try:
        _outcome = generate_html_report(result, skill_dir,
                                        report_type="single_method")
        _log_report_landing(_outcome, "Single", "htm 归口")
    except Exception as _dhe:
        logger.warning("[Single] 诊断 HTML 报告生成失败(不阻断): %s", _dhe)
def _emit_step_payload(step_name: str, skill_dir: Any, result: Any) -> bool:
    if not isinstance(result, dict):
        return False
    try:
        payload = dict(result)
        payload["_step_name"] = step_name
        outcome = generate_html_report(payload, skill_dir, "step")
        if not isinstance(outcome, dict) or outcome.get("status") != "ok":
            logger.warning("[%s] HTML 报告分发返回失败(不阻断): %s",
                           step_name, str(outcome)[:200])
            return False
        path = as_dict(outcome.get("data")).get("path")
        if not isinstance(path, str) or not path.strip():
            logger.info("[%s] HTML 报告未落盘（阶段抑制或发射失败）", step_name)
            return False
        return True
    except Exception as _e:
        logger.warning("[%s] HTML 报告生成失败(不阻断): %s", step_name, _e)
        return False
def emit_html_report(sd: str, payload: dict,
                      report_type: str = "ai_review",
                      context: str = "审核 HTML 报告生成失败") -> bool:
    tag = "AIReview" if report_type == "ai_review" else f"HTML:{report_type}"
    try:
        _outcome = generate_html_report(payload, sd, report_type)
    except Exception as _ahe:
        logger.warning("[%s] %s(不阻断): %s", tag, context, _ahe)
        return False
    if html_report_path(_outcome):
        logger.debug("[%s] %s: 已落盘", tag, context)
        return True
    logger.warning("[%s] %s(不阻断): %s", tag, context,
                   _report_not_landed_reason(_outcome))
    return False
def emit_step_trace(step_name: str, skill_dir: str, payload: Any, *,
                     extra: dict | None = None, context: str = "") -> bool:
    _payload = dict(payload) if isinstance(payload, dict) else {"result": payload}
    if extra:
        _payload.update(extra)
    _payload["_step_name"] = step_name
    return emit_html_report(
        skill_dir, _payload, "step",
        context or f"{step_name} HTML 留痕失败")
def emit_step_html(step_name: str, skill_dir: str, result: dict) -> None:
    if not isinstance(step_name, str) or not isinstance(result, dict):
        logger.warning(
            "[HTMLReport] emit_step_html 传参口径为 "
            "(step_name, skill_dir, result)：收到 step_name=%s / result=%s，"
            "已跳过留痕", type(step_name).__name__, type(result).__name__)
        return
    try:
        get_html_report_base()
    except Exception as _base_err:
        logger.warning("[%s] HTML 报告基目录不可用(不阻断): %s",
                       step_name, _base_err)
        return
    if _emit_step_payload(step_name, skill_dir, result):
        logger.info("[%s] HTML 报告已生成", step_name)
def emit_ai_fix_trace(skill_dir: str, index: int, result: dict) -> None:
    try:
        _trace_idx = plan_index(index)
        _trace_display = _trace_idx if _trace_idx is not None else index
        _payload = {
            "status": result.get("status", "unknown"),
            "review_id": f"fix-{_trace_display}",
            "channel": "treatment_fix",
            "reason": str(result.get("reason", ""))[:500],
            "result": result,
        }
        _sd = _skill_arg(skill_dir)
        _outcome = generate_html_report(_payload, _sd, "ai_review")
        _log_report_landing(
            _outcome, "AIManualFix",
            f"修复执行 index={_trace_display}, "
            f"status={safe_text(result.get('status', 'unknown'))}")
    except Exception as _fhe:
        logger.warning("[AIManualFix] 修复执行 HTML 留痕失败(不阻断): %s", _fhe)
def emit_treatment_item_report(skill_dir: str, payload: dict) -> None:
    try:
        _outcome = generate_html_report(payload, skill_dir, "treatment_item")
        _log_report_landing(_outcome, "TreatmentStep", "治疗项")
    except Exception as _the:
        logger.warning("[TreatmentStep] 治疗 HTML 报告生成失败(不阻断): %s", _the)
def cv_report_findings(cv_report: dict) -> list:
    if not isinstance(cv_report, dict):
        return []
    cv_report = _adapt_cv_payload(cv_report)
    for _fk in ("findings_index", "findings"):
        _fs = cv_report.get(_fk)
        if isinstance(_fs, list):
            return _fs
        if isinstance(_fs, tuple):
            return list(_fs)
    return []
def _emit_report_document(sd: str, html_doc: str, output_html: str | None,
                          default_name: str, stage_title: str,
                          icon: str, tag: str, *, payload=None,
                          report_type: str = "") -> None:
    if output_html:
        logger.info(
            "[%s] 独立 HTML 输出已按阶段配对契约归并（不另写 %s/%s）",
            tag, output_html, default_name)
    path = emit_to_stage(
        "treat_review", sd, stage_title, html_doc, icon=icon,
        payload=payload, report_type=report_type)
    if path:
        logger.info("[%s] 报告已汇入审核治疗阶段文件: %s", tag, path)
    else:
        logger.warning("[%s] 阶段聚合未落盘(不阻断): %s", tag, stage_title)
def emit_coverage_report_html(sd: str, output_html: str | None) -> None:
    try:
        _emit_report_document(
            sd, render_coverage_report_html(sd), output_html,
            "coverage_report.html", "覆盖报告", "📊", "ReviewStep",
            payload={"skill_dir": sd, "source": "coverage_report"},
            report_type="coverage")
    except Exception as _he:
        logger.warning("[ReviewStep] HTML 覆盖报告生成失败: %s", _he)
def emit_dependency_report_html(cv_report: dict, sd: str,
                                 output_html: str | None) -> None:
    try:
        _emit_report_document(
            sd, render_dependency_report_html(cv_report_findings(cv_report), sd),
            output_html, "dependency_report.html", "依赖图报告", "🕷",
            "TreatmentPlan", payload={"findings": cv_report_findings(cv_report)},
            report_type="dependency")
    except Exception as _he:
        logger.warning("[TreatmentPlan] HTML 依赖图报告生成失败: %s", _he)
def emit_fupan_report_html(result: dict, output_html: str | None,
                           skill_dir: str | None = None) -> None:
    try:
        if output_html:
            logger.info(
                "[fupan] 独立 HTML 输出已归并复盘反哺阶段（不另写无配套 JSON 文件）: %s",
                output_html)
        _gen = generate_html_report(result, skill_dir or "", "fupan")
        _log_report_landing(_gen, "fupan", "复盘反哺阶段")
    except Exception as html_err:
        logger.warning("[fupan] HTML 报告生成失败(不阻断): %s", html_err)
def emit_final_summary_block(skill_dir: str, payload: dict) -> dict:
    payload = as_dict(payload)
    produced: list[str] = []
    items: list[tuple[str, str, str]] = []
    report_dir = text_or(payload.get("report_dir"))
    if not report_dir:
        return {"path": "", "json_path": "", "produced_keys": produced,
                "report_dir": ""}
    try:
        artifacts = collect_html_artifacts(skill_dir, [report_dir])
        _summary = {
            "progress": as_dict(payload.get("progress")),
            "findings_count": payload.get("findings_count"),
            "cv_stats": as_dict(payload.get("cv_stats")),
            "artifacts": artifacts,
            "report_dir": report_dir,
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        }
        items.append((
            "全流程汇总与阶段导航",
            render_pipeline_summary_html(_summary, skill_dir),
            _meta_for("pipeline_summary").icon))
        produced.append("pipeline_summary")
        final_payload = dict(payload)
        final_payload["artifacts"] = artifacts
        final_payload["view"] = "summary_and_stage_navigation"
    except Exception as _fhe:
        logger.warning("[FinalSummary] 总报告 HTML 生成失败(不阻断): %s", _fhe)
        final_payload = dict(payload)
    final_path = ""
    if items:
        try:
            final_path = emit_final_block(skill_dir, items, payload=final_payload)
        except Exception as _emit_err:
            logger.warning(
                "[FinalSummary] 最终汇总发射异常(不阻断): %s", _emit_err)
    json_path = ""
    if final_path:
        try:
            candidate = stage_json_artifact_path(final_path, skill_dir)
            json_path = candidate if os.path.isfile(candidate) else ""
        except (OSError, RuntimeError, ValueError):
            logger.debug("最终报告配套 JSON 路径解析失败", exc_info=True)
        logger.info("[FinalSummary] 最终汇总与阶段导航已生成: %s", final_path)
    if produced and not final_path:
        logger.warning(
            "[FinalSummary] 最终汇总块未落盘，撤回 produced_keys: %s", produced)
    return {"path": final_path or "", "json_path": json_path,
            "produced_keys": produced if final_path else [],
            "report_dir": report_dir}
def _md_escape_cell(value) -> str:
    return (safe_text(value).replace("\\", "\\\\").replace("|", "\\|")
            .replace("\r", " ").replace("\n", " "))
def _count_field(stat: dict, primary: str, fallback: str):
    value = stat.get(primary)
    return (stat.get(fallback) or 0) if value is None else value
def _file_stats_row(stat: dict) -> str:
    filepath = stat.get("filepath") or stat.get("file") or ""
    lines_count = _count_field(stat, "lines", "line_count")
    issues_count = _count_field(stat, "issues", "issue_count")
    severity = stat.get("severity") or "UNKNOWN"
    return (f"| {_md_escape_cell(filepath)} | {_md_escape_cell(lines_count)} "
            f"| {_md_escape_cell(issues_count)} | {_md_escape_cell(severity)} |")
class ReportFormatter:
    @staticmethod
    def format_file_stats_table(file_stats) -> str:
        if not file_stats:
            return ""
        if not isinstance(file_stats, (list, tuple, dict)):
            return str(file_stats)
        if isinstance(file_stats, dict):
            file_stats = [file_stats]
        lines = ["| 文件 | 行数 | 问题数 | 严重度 |", "|------|------|--------|--------|"]
        for stat in file_stats:
            if not isinstance(stat, dict):
                continue
            lines.append(_file_stats_row(stat))
        return "\n".join(lines)
    @staticmethod
    def to_json(issues=None, stats=None) -> dict:
        result: dict[str, Any] = {"issues": [], "stats": {}}
        issues = _as_issue_list(issues)
        for issue in issues:
            if hasattr(issue, "to_dict"):
                result["issues"].append(issue.to_dict())
            elif isinstance(issue, dict):
                result["issues"].append(issue)
        result["stats"] = as_dict(stats)
        return result
    @staticmethod
    def to_markdown(issues: list | None = None, stats: dict | None = None) -> str:
        stats = as_dict(stats)
        issues = _as_issue_list(issues)
        normalized = []
        for issue in issues:
            data = _markdown_issue_data(issue)
            if data is not None:
                normalized.append(data)
        lines = ["# 诊断报告", ""]
        lines.extend(_markdown_stats_lines(stats, normalized))
        lines.extend(_markdown_issue_lines(normalized))
        return "\n".join(lines)
def _markdown_issue_data(issue):
    if isinstance(issue, dict):
        return issue
    if hasattr(issue, "to_dict"):
        data = issue.to_dict()
        if isinstance(data, dict):
            return data
    if hasattr(issue, "rule_id"):
        return issue
    return None
def _is_markdown_issue(issue) -> bool:
    return isinstance(issue, dict) or hasattr(issue, "rule_id")
def _markdown_stats_lines(stats: dict, issues: list) -> list[str]:
    if not stats:
        return []
    total_issues = stats.get("total_issues")
    if total_issues is None:
        total_issues = sum(1 for issue in issues if _is_markdown_issue(issue))
    return [
        f"- 扫描文件数: {safe_text(stats.get('files_scanned', 0))}",
        f"- 总行数: {safe_text(stats.get('total_lines', 0))}",
        f"- 问题总数: {safe_text(total_issues)}",
        "",
    ]
def _markdown_field(issue, *names: str):
    for name in names:
        value = read_field(issue, name, "")
        if value is not None and value != "":
            return value
    return ""
def _markdown_issue_lines(issues: list) -> list[str]:
    if not issues:
        return []
    lines = ["## 问题列表", "",
             "| 规则 | 严重度 | 文件 | 行号 | 描述 |",
             "|------|--------|------|------|------|"]
    for issue in issues:
        if not _is_markdown_issue(issue):
            continue
        cells = (
            _markdown_field(
                issue, "rule_id", "rule", "rule_ref", "detector_id", "id"),
            read_field(issue, "severity", ""),
            _markdown_field(issue, "file", "filepath", "location"),
            read_field(issue, "line", 0),
            _markdown_field(issue, "message", "description", "title"),
        )
        lines.append("| " + " | ".join(
            _md_escape_cell(cell) for cell in cells) + " |")
    return lines
def format_impact_report(impact_report: dict | None) -> str:
    if impact_report is None:
        return ""
    if isinstance(impact_report, dict):
        lines = ["# 影响分析报告", ""]
        for key, value in impact_report.items():
            lines.append(f"- **{_md_escape_cell(key)}**: {_md_escape_cell(value)}")
        return "\n".join(lines)
    if hasattr(impact_report, "to_dict"):
        return format_impact_report(impact_report.to_dict())
    return str(impact_report)
def _as_issue_list(value) -> list:
    return list(value) if isinstance(value, (list, tuple)) else []
def emit_aggregate_report_html(report: dict, skill_dir: str) -> None:
    try:
        _xv_view = report.get(CAT_CROSS_VALIDATION) if isinstance(report, dict) else None
        _outcome = generate_html_report(
            _xv_view if isinstance(_xv_view, dict) else report,
            skill_dir, "cv")
        _log_report_landing(_outcome, "Aggregator", "htm 归口")
    except Exception as _ahe:
        logger.warning("[Aggregator] 聚合 HTML 报告生成失败（不阻断）: %s", _ahe)

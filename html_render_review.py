from __future__ import annotations

import html as _html
import logging
import math
from dataclasses import dataclass

from jwsgj.diag_types_normalize import (
    as_dict,
    as_list,
    dict_items,
    grade_from_score,
)
from jwsgj.diag_types_vocab import (
    RETRO_SCORE_DIMENSIONS,
    STRUCTURED_EXCLUDED_KEYS,
    STRUCTURED_PRIORITY_KEYS,
)
from jwsgj.fix_guide_rule_identity import get_fix_order_for_findings
from jwsgj.html_report_primitives import (
    DISCLOSURE_ROWS_COMPACT,
    DISCLOSURE_ROWS_MEDIUM,
    DISCLOSURE_ROWS_STANDARD,
    DISCLOSURE_ROWS_TINY,
    DISCLOSURE_ROWS_WIDE,
    DISCLOSURE_TEXT_CAP,
    TEXT_BLOCK_SAFE_CAP,
    HTMLReport,
    ReportSection,
    alert_tone,
    apply_target_identity,
    derive_header_meta,
    disclosure_value,
    dump_or_str,
    emit_html,
    empty_card,
    esc_or,
    extend_sections,
    full_value,
    kv_table,
    kv_table_preescaped,
    normalize_line_value,
    payload_is_skill,
    raw_dump_section,
    read_field,
    render_badge,
    render_code_block,
    render_ctx_cell,
    render_list_progressive,
    render_progress_bar,
    render_report,
    render_stat,
    render_structured_details,
    render_table,
    risk_level_label_css,
    safe_text,
    scalar_detail,
    score_band_css,
    status_badge_css,
    text_or,
    to_bool,
    to_finite_float,
    to_int,
    wrap_html,
)
from jwsgj.runtime_paths import resolve_direct_output_path
from jwsgj.testsuite_coverage_map import get_coverage_report

logger = logging.getLogger(__name__)
__all__ = [
    "adapt_fupan_payload",
    "render_ai_review_html",
    "render_coverage_report_html",
    "render_degradation_report_html",
    "render_dependency_report_html",
    "render_fupan_report_html",
    "render_retro_report_html",
    "render_treatment_item_html",
]
logger.info("html_render_review 已加载: %d 项导出（覆盖/依赖/AI 审核/复盘/反哺/降级裁决报告）", len(__all__))
_TONE_SUCCESS = "#38a169"
_TONE_WARNING = "#dd6b20"
_TONE_DANGER = "#e53e3e"
_BAND_COLORS = {
    "success": _TONE_SUCCESS, "warning": _TONE_WARNING, "danger": _TONE_DANGER,
}
_TRUNCATION_NOTICE = ("\n...（载体超 {cap} 字符安全阀已截断，"
                      "完整数据见 JSONL 留痕）")
_SHOW_CAP_TINY = DISCLOSURE_ROWS_TINY
_SHOW_CAP_COMPACT = DISCLOSURE_ROWS_COMPACT
_SHOW_CAP_MEDIUM = DISCLOSURE_ROWS_MEDIUM
_SHOW_CAP_STANDARD = DISCLOSURE_ROWS_STANDARD
_SHOW_CAP_WIDE = DISCLOSURE_ROWS_WIDE
_COVERAGE_TONES = ((0.7, _TONE_SUCCESS), (0.4, _TONE_WARNING))
_COVERAGE_TONE_FALLBACK = _TONE_DANGER
_DEFAULT_METRIC = 0.0
_DEFAULT_DIM_WEIGHT = 1.0
_RATIO_LIMIT = 1.0
_SCORE_LIMIT = 100.0
def _finite_metric(val, default: float = _DEFAULT_METRIC) -> float:
    if isinstance(val, bool):
        return default
    return to_finite_float(val, default)
def _bounded_metric(val, *, maximum: float,
                    default: float = _DEFAULT_METRIC) -> float:
    number = _finite_metric(val, math.nan)
    if not math.isfinite(number) or not 0 <= number <= maximum:
        return default
    return number
def _coverage_tone(rate: float) -> str:
    for threshold, color in _COVERAGE_TONES:
        if rate >= threshold:
            return color
    return _COVERAGE_TONE_FALLBACK
def _coverage_stats_html(total: int, tested: int, untested: int,
                         rate: float) -> str:
    stats = (
        render_stat(total, "修复器总数", "info")
        + render_stat(tested, "已测试", "success")
        + render_stat(untested, "未测试", alert_tone(untested, "danger"))
        + render_stat(f"{rate*100:.1f}%", "覆盖率", "info")
    )
    progress = render_progress_bar(rate, 1.0, _coverage_tone(rate))
    return (f'<div class="stat-grid">{stats}</div>'
            f'<div class="card"><h3>覆盖率</h3>{progress}</div>')
def _coverage_entries(details) -> list:
    valid = []
    for cov in as_list(details):
        if not (hasattr(cov, "fixer") and hasattr(cov, "has_test")):
            continue
        fixer = getattr(cov, "fixer", None)
        if fixer is None:
            continue
        if any(not hasattr(fixer, _attr)
               for _attr in ("rule_id", "class_name", "module")):
            continue
        valid.append(cov)
    return valid
def _coverage_table_html(details: list) -> str:
    if not details:
        return ""
    rows = []
    for cov in details:
        status_badge = (render_badge("已测试", "badge-success")
                        if cov.has_test
                        else render_badge("未测试", "badge-danger"))
        rows.append([
            status_badge,
            esc_or(cov.fixer.rule_id),
            esc_or(cov.fixer.class_name),
            esc_or(cov.fixer.module),
            str(to_int(getattr(cov, "test_count", 0))) if cov.has_test else "—",
        ])
    return render_table(["状态", "规则ID", "类名", "模块", "测试数"],
                         rows, table_id="coverage_table")
def _coverage_raw_details(details: list) -> list:
    out = []
    for cov in details or []:
        fx = getattr(cov, "fixer", None)
        out.append({
            "rule_id": getattr(fx, "rule_id", ""),
            "class_name": getattr(fx, "class_name", ""),
            "module": getattr(fx, "module", ""),
            "has_test": bool(getattr(cov, "has_test", False)),
            "test_count": to_int(getattr(cov, "test_count", 0))})
    return out
def render_coverage_report_html(skill_dir: str) -> str:
    logger.debug("[HtmlReport] render_coverage_report_html 渲染: skill_dir=%s", skill_dir)
    report_data = get_coverage_report(skill_dir)
    total = to_int(report_data.total_fixers)
    tested = to_int(report_data.tested_fixers)
    untested = to_int(report_data.untested_fixers)
    rate = _bounded_metric(report_data.coverage_rate, maximum=_RATIO_LIMIT)
    details = _coverage_entries(report_data.details)
    html = (_coverage_stats_html(total, tested, untested, rate)
            + _coverage_table_html(details))
    if total <= 0:
        html += empty_card(
            "未发现修复器：目标未使用修复器约定，覆盖率不适用")
    _raw_details = _coverage_raw_details(details)
    rep = HTMLReport(
        title="修复器覆盖报告",
        sections=[ReportSection(
            title="覆盖概览", section_id="coverage", icon="🧪",
            html_content=html)],
        raw_data=apply_target_identity(
            {"skill_dir": skill_dir,
             "total_fixers": total, "tested_fixers": tested,
             "untested_fixers": untested, "coverage_rate": rate,
             "details": _raw_details}, skill_dir))
    return rep.render()
def _dep_groups_card(groups: list) -> str:
    if not groups:
        return ""
    card = '<div class="card"><h3>执行分组（同组可并行）</h3>'
    for i, group in enumerate(groups):
        card += f'<p><strong>批次 {i+1}:</strong> {", ".join(_html.escape(safe_text(n)) for n in group)}</p>'
    return card + '</div>'
def _dep_conflicts_card(conflicts: list) -> str:
    if not conflicts:
        return ""
    conflict_rows = []
    for c in conflicts:
        sev = text_or(c.get("severity"))
        _sev_key = sev.strip().lower() or "unknown"
        _sev_tone = ("danger" if _sev_key in ("error", "critical", "fatal", "high")
                     else "info" if _sev_key in ("info", "low")
                     else "warning")
        sev_badge = render_badge(_sev_key.upper(), f"badge-{_sev_tone}")
        conflict_rows.append([
            sev_badge,
            esc_or(c.get("finding_a")),
            esc_or(c.get("finding_b")),
            esc_or(c.get("reason")),
            esc_or(c.get("recommendation")),
        ])
    return ('<div class="card"><h3>冲突</h3>'
            + render_table(["级别", "Finding A", "Finding B", "原因", "建议"], conflict_rows, table_id="conflicts_table")
            + '</div>')
def render_dependency_report_html(findings: list[dict], skill_dir: str = "") -> str:
    findings = as_list(findings)
    logger.debug("[HtmlReport] render_dependency_report_html 渲染: findings=%d 键", len(findings))
    order = as_dict(get_fix_order_for_findings(findings, skill_dir))
    total_nodes = to_int(order.get("total_nodes"))
    total_edges = to_int(order.get("total_edges"))
    conflicts = _entries(order.get("conflicts"), context="依赖冲突")
    cyclic_nodes = as_list(order.get("cyclic_nodes"))
    groups = [as_list(g) for g in as_list(order.get("groups"))]
    stats = (
        render_stat(total_nodes, "节点数", "info")
        + render_stat(total_edges, "依赖边数", "info")
        + render_stat(len(conflicts), "冲突数", alert_tone(conflicts, "danger"))
        + render_stat(len(cyclic_nodes), "环路节点", alert_tone(cyclic_nodes, "danger"))
    )
    html = f'<div class="stat-grid">{stats}</div>'
    html += _dep_groups_card(groups)
    html += _dep_conflicts_card(conflicts)
    rep = HTMLReport(
        title="修复依赖图报告",
        sections=[ReportSection(
            title="依赖执行序", section_id="dependency", icon="🔗",
            html_content=html)],
        raw_data=apply_target_identity(
            {"skill_dir": skill_dir,
             "findings": findings, "fix_order": order,
             "total_nodes": total_nodes, "total_edges": total_edges},
            skill_dir))
    return rep.render()
def _full_value_rows(mapping: dict) -> list[tuple]:
    return [(k, full_value(v)) for k, v in mapping.items()]
def _scalar_rows(mapping: dict, *, drop_empty: bool = False,
                 exclude: tuple = ()) -> list[tuple]:
    return [(k, scalar_detail(v)) for k, v in mapping.items()
            if k not in exclude
            and isinstance(v, (str, int, float, bool))
            and not (drop_empty and v == "")]
_AWAITING_DEDICATED_KEYS = (
    "code_context", "fix_plan", "memory_operation", "provenance",
    "diagnosis_context", "treatment_context", "retrospective_context",
)
def _awaiting_scalar_card(awaiting: dict) -> str:
    rows = _scalar_rows(awaiting, drop_empty=True,
                        exclude=_AWAITING_DEDICATED_KEYS)
    if not rows:
        return ""
    return f"<div class='card'>{kv_table_preescaped(rows)}</div>"
def _carrier_present(value) -> bool:
    if value is None:
        return False
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (dict, list, tuple, set, frozenset)):
        return bool(value)
    return True
def _truncate_carrier(text: str) -> str:
    if len(text) <= TEXT_BLOCK_SAFE_CAP:
        return text
    return (text[:TEXT_BLOCK_SAFE_CAP]
            + _TRUNCATION_NOTICE.format(cap=TEXT_BLOCK_SAFE_CAP))
def _carrier_text(value, *, compact: bool = False) -> str:
    if isinstance(value, str):
        return _truncate_carrier(value)
    indent = None if compact or not isinstance(
        value, (dict, list, tuple)) else 2
    return _truncate_carrier(
        dump_or_str(value, TEXT_BLOCK_SAFE_CAP + 1, indent=indent))
def _card_html(body: str, *, title: str = "") -> str:
    heading = f"<h3>{title}</h3>" if title else ""
    return f"<div class='card'>{heading}{body}</div>"
def _code_card(value, *, title: str = "") -> str:
    if not _carrier_present(value):
        return ""
    return _card_html(render_code_block(_carrier_text(value)), title=title)
_AWAITING_CARRIERS = (
    ("fix_plan", "修复方案"),
    ("memory_operation", "记忆操作（待执行）"),
    ("entry", "增强建议条目"),
)
_AWAITING_TARGET_DEDUPED = frozenset({"entry"})
def _awaiting_carrier_cards(awaiting: dict, target: dict) -> str:
    return "".join(
        _code_card(awaiting.get(key), title=title)
        for key, title in _AWAITING_CARRIERS
        if not (key in _AWAITING_TARGET_DEDUPED
                and _carrier_present(target.get(key))))
_PROVENANCE_CARDS = (
    ("diagnosis_context", "诊断层溯源"),
    ("treatment_context", "治疗层溯源"),
    ("retrospective_context", "复盘层溯源"),
)
def _awaiting_provenance_view(awaiting: dict) -> dict:
    sources = [awaiting]
    nested = awaiting.get("provenance")
    if isinstance(nested, dict):
        sources.append(nested)
    view = {}
    for key, _title in _PROVENANCE_CARDS:
        for source in sources:
            value = source.get(key)
            if _carrier_present(value):
                view[key] = value
                break
    return view
def _awaiting_provenance_cards(awaiting: dict) -> str:
    view = _awaiting_provenance_view(awaiting)
    return "".join(
        _code_card(view.get(key), title=title)
        for key, title in _PROVENANCE_CARDS)
def _ai_review_awaiting_section(awaiting: dict,
                                  target: dict) -> ReportSection | None:
    content = "".join(card for card in (
        _awaiting_scalar_card(awaiting),
        _code_card(awaiting.get("code_context"), title="代码现场"),
        _awaiting_carrier_cards(awaiting, target),
        _awaiting_provenance_cards(awaiting),
    ) if card)
    if not content:
        return None
    return ReportSection(
        title="待 AI 亲自执行（接续指令）", section_id="awaiting", icon="➡️",
        html_content=content)
_TARGET_DEDICATED_KEYS = (
    "function_summary", "fix_precheck", "fixer_risk", "fix_experience",
    "diagnosis_evidence", "cv_context", "plan", "entry", "proposal",
)
def _target_scalar_section(tgt: dict) -> ReportSection | None:
    _rows = _scalar_rows(tgt, drop_empty=True, exclude=_TARGET_DEDICATED_KEYS)
    if not _rows:
        return None
    return ReportSection(
        title="审核候选详情",
        html_content=f"<div class='card'>{kv_table_preescaped(_rows)}</div>",
        section_id="target", icon="🧾")
def _target_evidence_section(tgt: dict) -> ReportSection | None:
    ev = tgt.get("diagnosis_evidence")
    if not (isinstance(ev, dict) and ev):
        return None
    _ev_rows = _full_value_rows({
        k: v for k, v in ev.items()
        if k != "code_snippet" and v not in (None, "", [], {})})
    _ev_html = (f"<div class='card'>{kv_table(_ev_rows)}</div>"
                if _ev_rows else "")
    _ev_snip = ev.get("code_snippet")
    if _ev_snip:
        _ev_html += ("<div class='card'><h3>诊断现场代码片段</h3>"
                     + render_code_block(_ev_snip) + "</div>")
    if not _ev_html:
        return None
    return ReportSection(
        title="诊断证据链", section_id="evidence", icon="🔗",
        html_content=_ev_html)
def _full_map_section(mapping, title: str, section_id: str,
                      icon: str) -> ReportSection | None:
    if not (isinstance(mapping, dict) and mapping):
        return None
    return ReportSection(
        title=title,
        html_content=("<div class='card'>"
                      + kv_table(_full_value_rows(mapping))
                      + "</div>"),
        section_id=section_id, icon=icon)
def _aux_summary_card(tgt: dict) -> str:
    summary = tgt.get("function_summary")
    if not summary:
        return ""
    return ("<div class='card'><h3>函数语义摘要</h3><p>"
            f"{_html.escape(safe_text(summary))}</p></div>")
def _kv_card_rows(mapping: dict) -> list[tuple]:
    return [(key, render_ctx_cell(value, DISCLOSURE_TEXT_CAP))
            for key, value in mapping.items()]
def _kv_card(mapping: dict, *, title: str = "") -> str:
    if not mapping:
        return ""
    return _card_html(kv_table_preescaped(_kv_card_rows(mapping)),
                      title=title)
def _aux_dict_card(tgt: dict, key: str, title: str) -> str:
    value = tgt.get(key)
    if not (isinstance(value, dict) and value):
        return ""
    return _kv_card(value, title=title)
def _aux_experience_card(tgt: dict) -> str:
    experience = tgt.get("fix_experience")
    if not (isinstance(experience, list) and experience):
        return ""
    return (f"<div class='card'><h3>历史修复经验（{len(experience)} 条）</h3>"
            + render_list_progressive(
                [_html.escape(full_value(it)) for it in experience],
                list_id="ai_review_fix_experience",
                initial_visible=_SHOW_CAP_TINY)
            + "</div>")
def _target_aux_section(tgt: dict) -> ReportSection | None:
    parts = [card for card in (
        _aux_summary_card(tgt),
        _aux_dict_card(tgt, "fix_precheck", "修复前三问预检"),
        _aux_dict_card(tgt, "fixer_risk", "修复器风险元数据"),
        _aux_experience_card(tgt),
    ) if card]
    if not parts:
        return None
    return ReportSection(
        title="审核辅助信息", section_id="aux", icon="🧰",
        html_content="".join(parts))
_FEEDBACK_CARRIERS = (
    ("plan", "反哺修改方案（feedback 通道）"),
    ("entry", "增强建议条目（enhancement 通道）"),
    ("proposal", "调整建议（adjustment 通道）"),
)
def _feedback_carrier_section(tgt: dict, key: str,
                              title: str) -> ReportSection | None:
    carrier = tgt.get(key)
    if not _carrier_present(carrier):
        return None
    return ReportSection(
        title=title, section_id=f"fb_{key}", icon="♻️",
        html_content=("<div class='card'>"
                       + render_code_block(_carrier_text(carrier)) + "</div>"))
def _ai_review_target_sections(tgt: dict) -> list[ReportSection]:
    sections: list[ReportSection] = []
    extend_sections(sections, (
        _target_scalar_section(tgt),
        _target_evidence_section(tgt),
        _full_map_section(tgt.get("cv_context"),
                          "CV 结论上下文", "cv_context", "🧮"),
        _target_aux_section(tgt),
    ))
    extend_sections(sections, (
        _feedback_carrier_section(tgt, key, title)
        for key, title in _FEEDBACK_CARRIERS
    ))
    return sections
@dataclass(frozen=True)
class _AiReviewFacts:
    result: dict
    rid: str
    channel: str
    status: str
    inner: object
    @classmethod
    def of(cls, result: dict) -> _AiReviewFacts:
        return cls(
            result=result,
            rid=safe_text(result.get("review_id") or ""),
            channel=safe_text(result.get("channel") or ""),
            status=safe_text(result.get("status") or "unknown"),
            inner=result.get("result"),
        )
    @property
    def title(self) -> str:
        return f"AI 审核执行报告 · {self.channel} · {self.rid}"
def _ai_review_overview_section(facts: _AiReviewFacts) -> ReportSection:
    stat_cls = status_badge_css(facts.status)
    _remaining = facts.result.get("remaining")
    _remaining_text = "-" if _remaining is None else to_int(_remaining)
    stats = (
        f"{render_stat(_html.escape(facts.status), '状态', stat_cls)}"
        f"{render_stat(_html.escape(facts.channel or '-'), '通道', 'info')}"
        f"{render_stat(_remaining_text, '剩余待审核', 'info')}"
    )
    return ReportSection(
        title="执行概览", section_id="overview", icon="🤖",
        html_content=f"<div class='stat-grid'>{stats}</div>")
def _ai_review_detail_section(facts: _AiReviewFacts) -> ReportSection:
    result = facts.result
    detail_rows = [
        ("review_id", _html.escape(facts.rid)),
        ("channel", _html.escape(facts.channel)),
        ("verdict", _html.escape(safe_text(result.get("verdict") or "-"))),
        ("next_action", _html.escape(safe_text(result.get("next_action") or "-"))),
    ]
    if result.get("reason"):
        detail_rows.append(("reason", disclosure_value(result.get("reason"))))
    if isinstance(facts.inner, dict):
        detail_rows.extend(
            (f"result.{k}", v) for k, v in _scalar_rows(facts.inner))
    return ReportSection(
        title="审核项详情", section_id="detail", icon="🧾",
        html_content=f"<div class='card'>{kv_table_preescaped(detail_rows)}</div>")
def _ai_review_sections(facts: _AiReviewFacts) -> list[ReportSection]:
    result = facts.result
    sections = [
        _ai_review_overview_section(facts),
        _ai_review_detail_section(facts),
    ]
    awaiting = result.get("awaiting_ai_execution")
    target = result.get("review_target")
    target = target if isinstance(target, dict) else {}
    awaiting_section = (
        _ai_review_awaiting_section(awaiting, target)
        if isinstance(awaiting, dict) else None)
    extend_sections(sections, (
        awaiting_section,
        _full_map_section(result.get("assessment"),
                          "四维审核评估", "assessment", "⚖️"),
    ))
    if target:
        sections.extend(_ai_review_target_sections(target))
    if isinstance(facts.inner, dict):
        details = render_structured_details(
            facts.inner, priority_keys=STRUCTURED_PRIORITY_KEYS,
            excluded_keys=STRUCTURED_EXCLUDED_KEYS)
        if details:
            sections.append(ReportSection(
                title="执行结果结构化详情", section_id="result_structured",
                icon="📊", html_content=details))
    return sections
def render_ai_review_html(result: dict, skill_dir: str = "") -> str:
    if not isinstance(result, dict):
        result = {"status": "error",
                  "reason": f"非法输入类型: {type(result).__name__}"}
    facts = _AiReviewFacts.of(result)
    sections = _ai_review_sections(facts)
    return render_report(facts.title, sections, skill_dir, facts.result)
_SEV_BADGE_CSS = {"critical": "badge-danger", "high": "badge-danger",
                  "medium": "badge-warning", "low": "badge-info"}
def _present_items(value) -> list:
    return [x for x in as_list(value) if x is not None]
def _evidence_items(ev) -> list[str]:
    if isinstance(ev, (list, tuple)) and ev:
        return [safe_text(x) for x in ev if x is not None]
    return [safe_text(ev)] if ev else []
def _score_cell(val) -> str:
    if val is None:
        return "-"
    if isinstance(val, (int, float)) and not isinstance(val, bool):
        return f"{to_finite_float(val):g}"
    return safe_text(val)
_MEMOP_VERB_KEYS = ("operation", "action")
def _memop_verb(m: dict) -> str:
    for _key in _MEMOP_VERB_KEYS:
        _verb = m.get(_key)
        if _verb is not None and _verb != "":
            return text_or(_verb)
    return ""
def _memop_row(m: dict, *, with_score: bool = False) -> list:
    row = [
        _html.escape(_memop_verb(m)),
        f"<span class='path-cell'>{esc_or(m.get('path'))}</span>",
        esc_or(m.get("reason")),
    ]
    if with_score:
        row.append(_html.escape(_score_cell(m.get("quality_score"))))
    return row
def _confidence_pct_text(val) -> str:
    if not isinstance(val, (int, float)) or isinstance(val, bool):
        return "-"
    ratio = _bounded_metric(
        val, maximum=_RATIO_LIMIT, default=math.nan)
    return f"{ratio:.0%}" if math.isfinite(ratio) else "-"
def _fupan_stats_html(overall_score: float, grade: str,
                      risk_count: int, memops_count: int) -> str:
    grade_text = text_or(grade).strip() or "-"
    _grade_key = grade_text.upper()
    grade_css = score_band_css(overall_score)
    grade_display = (_grade_key if len(_grade_key) == 1 and _grade_key.isalpha()
                     else grade_text)
    return f"""
<div class="stat-grid">
  {render_stat(f"{overall_score:.0f}", "综合评分", score_band_css(overall_score))}
  {render_stat(_html.escape(grade_display), "等级", grade_css)}
  {render_stat(risk_count, "风险数", "danger" if risk_count else "success")}
  {render_stat(memops_count, "记忆操作", "info")}
</div>
"""
def _fupan_overview_html(risk_level: str, auto_analyzed,
                         pdca: dict, summary_text) -> str:
    rl_label, rl_css = risk_level_label_css(risk_level)
    _pdca_ok = (to_bool(pdca.get("checked"))
                or to_bool(pdca.get("pdca_available")))
    return f"""
<div class="card">
  <h3>复盘概览</h3>
  <span class="health-badge {rl_css}">{_html.escape(rl_label)}</span>
  <span style="margin-left:12px;">
    自动分析: {"已启用" if to_bool(auto_analyzed) else "未启用"} |
    PDCA: {"可用" if _pdca_ok else "不可用"}
  </span>
</div>
<div class="card">
  <h3>摘要</h3>
  <p style="color:#4a5568;">{_html.escape(summary_text)}</p>
</div>
"""
def _fupan_dim_row(d) -> list:
    dim_name = text_or(read_field(d, "dimension")).replace("QualityDimension.", "")
    dim_score = _bounded_metric(
        read_field(d, "score", _DEFAULT_METRIC), maximum=_SCORE_LIMIT)
    dim_weight = _finite_metric(
        read_field(d, "weight"), _DEFAULT_DIM_WEIGHT)
    return [
        _html.escape(dim_name),
        render_stat(f"{dim_score:.0f}", "", score_band_css(dim_score)),
        f"{dim_weight:.1f}",
        _html.escape("；".join(_evidence_items(read_field(d, "evidence")))),
    ]
def _is_dimension_entry(entry) -> bool:
    return isinstance(entry, dict) or hasattr(entry, "dimension")
def _fupan_dims_section(dimensions: list) -> ReportSection | None:
    if not dimensions:
        return None
    dim_rows = [_fupan_dim_row(d) for d in dimensions
                if _is_dimension_entry(d)]
    if not dim_rows:
        return None
    dim_html = render_table(["维度", "评分", "权重", "证据"], dim_rows, table_id="fupan_dims")
    return ReportSection(title="维度评分", section_id="dims", icon="🎯", html_content=dim_html)
def _progressive_card(title: str, color: str, items: list, list_id: str,
                      *, min_visible: int) -> str:
    return ('<div class="card">'
            f'<h3 style="color:{color};">{title}（{len(items)}）</h3>'
            + render_list_progressive(
                [_html.escape(safe_text(x)) for x in items],
                list_id=list_id, initial_visible=min_visible)
            + "</div>")
def _fupan_sw_section(strengths: list, weaknesses: list) -> ReportSection | None:
    if not (strengths or weaknesses):
        return None
    sw_html = '<div class="stat-grid" style="grid-template-columns:1fr 1fr;">'
    sw_html += _progressive_card("优势", _TONE_SUCCESS, strengths,
                                 "fupan_strengths",
                                 min_visible=_SHOW_CAP_TINY)
    sw_html += _progressive_card("待改进", _TONE_DANGER, weaknesses,
                                 "fupan_weaknesses",
                                 min_visible=_SHOW_CAP_TINY)
    sw_html += "</div>"
    return ReportSection(title="优势与待改进", section_id="sw", icon="⚖️", html_content=sw_html)
def _lineno_text(lineno) -> str:
    if isinstance(lineno, bool):
        return "-"
    return _html.escape(normalize_line_value(lineno) or "-")
def _fupan_risk_row(r: dict) -> list:
    sev = text_or(r.get("severity"), "low").strip().lower()
    lineno_text = _lineno_text(r.get("lineno"))
    return [
        render_badge(sev.upper(), _SEV_BADGE_CSS.get(sev, "badge-muted")),
        esc_or(r.get("category")),
        esc_or(r.get("risk_id"), "-"),
        esc_or(r.get("matched_keyword"), "-"),
        esc_or(r.get("method"), "-"),
        _confidence_pct_text(r.get("confidence")),
        lineno_text,
        esc_or(r.get("suggestion")),
    ]
def _fupan_risks_section(detected_risks: list) -> ReportSection | None:
    if not detected_risks:
        return None
    risk_rows = [_fupan_risk_row(r) for r in detected_risks
                 if isinstance(r, dict)]
    if not risk_rows:
        return None
    risk_html = render_table(
        ["级别", "类别", "风险ID", "命中关键词", "检测方式",
         "置信度", "行号", "建议"],
        risk_rows, table_id="fupan_risks",
        initial_visible=_SHOW_CAP_MEDIUM)
    return ReportSection(title=f"风险详情 ({len(risk_rows)})", section_id="risks", icon="⚠️", html_content=risk_html)
def _fupan_memops_section(memory_ops: list) -> ReportSection | None:
    if not memory_ops:
        return None
    mo_rows = [_memop_row(m, with_score=True)
               for m in memory_ops if isinstance(m, dict)]
    if not mo_rows:
        return None
    mo_html = render_table(["操作", "路径", "原因", "评分"], mo_rows,
                            table_id="fupan_mem_ops",
                            initial_visible=_SHOW_CAP_MEDIUM)
    return ReportSection(title=f"记忆操作 ({len(mo_rows)})", section_id="memops", icon="🧠", html_content=mo_html)
def _carrier_entries(value, *, key_field: str = "") -> list:
    if isinstance(value, dict) and value:
        entries: list = []
        for key, item in value.items():
            if not isinstance(item, dict):
                continue
            if key_field and not item.get(key_field):
                item = {**item, key_field: str(key)}
            entries.append(item)
        return entries
    return dict_items(value)
def _entries(value, *, key_field: str = "", context: str = "") -> list:
    entries = _carrier_entries(value, key_field=key_field)
    if context and value:
        if isinstance(value, dict):
            raw = list(value.values())
        else:
            raw = value if isinstance(value, (list, tuple)) else [value]
        dropped = len(raw) - len(entries)
        if dropped > 0:
            logger.warning(
                "[HtmlReport] %s 丢弃 %d 个非映射条目（共 %d 项）",
                context, dropped, len(raw))
    return entries
def _fupan_overall_score(fupan_result: dict, qr) -> float:
    for raw in (read_field(qr, "overall_score"),
                fupan_result.get("fupan_quality_score"),
                fupan_result.get("quality_score")):
        score = _bounded_metric(
            raw, maximum=_SCORE_LIMIT, default=math.nan)
        if math.isfinite(score):
            return score
    return _DEFAULT_METRIC
def _normalize_fupan_quality_report(
    fupan_result: dict) -> tuple[float, str, str, list, list, list]:
    qr = fupan_result.get("quality_report", {})
    score = _fupan_overall_score(fupan_result, qr)
    grade = grade_from_score(score)
    return (
        score,
        grade,
        text_or(read_field(qr, "risk_level"), "low").strip().lower(),
        _present_items(read_field(qr, "dimensions")),
        _present_items(read_field(qr, "strengths")),
        _present_items(read_field(qr, "weaknesses")),
    )
@dataclass(frozen=True)
class _FupanFacts:
    raw: dict
    target_dir: str
    is_skill: bool
    overall_score: float
    grade: str
    risk_level: str
    dimensions: list
    strengths: list
    weaknesses: list
    detected_risks: list
    memory_ops: list
    summary_text: str
    auto_analyzed: bool
    pdca: dict
    @property
    def identity_key(self) -> str:
        return "skill_dir" if self.is_skill else "target_dir"
    @classmethod
    def of(cls, fupan_result: dict, skill_dir: str = "") -> _FupanFacts:
        fupan_result = adapt_fupan_payload(as_dict(fupan_result))
        (overall_score, grade, risk_level,
         dimensions, strengths, weaknesses) = _normalize_fupan_quality_report(
             fupan_result)
        target_dir = (skill_dir or text_or(fupan_result.get("skill_dir"))
                     or text_or(fupan_result.get("project_root"))
                     or text_or(fupan_result.get("target_dir")))
        return cls(
            raw=fupan_result,
            target_dir=target_dir,
            is_skill=bool(skill_dir) or payload_is_skill(fupan_result),
            overall_score=overall_score,
            grade=grade,
            risk_level=risk_level,
            dimensions=dimensions,
            strengths=strengths,
            weaknesses=weaknesses,
            detected_risks=_carrier_entries(
                fupan_result.get("detected_risks"), key_field="risk_id"),
            memory_ops=_carrier_entries(
                fupan_result.get("memory_operations")),
            summary_text=text_or(fupan_result.get("summary")),
            auto_analyzed=fupan_result.get("auto_analyzed", False),
            pdca=as_dict(fupan_result.get("pdca")),
        )
def _fupan_detail_sections(facts: _FupanFacts) -> list[ReportSection]:
    sections: list[ReportSection] = []
    extend_sections(sections, (
        _fupan_dims_section(facts.dimensions),
        _fupan_sw_section(facts.strengths, facts.weaknesses),
        _fupan_risks_section(facts.detected_risks),
        _fupan_memops_section(facts.memory_ops),
    ))
    return sections
def _fupan_sections(facts: _FupanFacts) -> list[ReportSection]:
    sections: list[ReportSection] = [
        ReportSection(
            title="执行摘要", section_id="summary", icon="📊",
            html_content=(
                _fupan_stats_html(facts.overall_score, facts.grade,
                                  len(facts.detected_risks),
                                  len(facts.memory_ops))
                + _fupan_overview_html(facts.risk_level, facts.auto_analyzed,
                                       facts.pdca, facts.summary_text)),
        ),
    ]
    sections.extend(_fupan_detail_sections(facts))
    extend_sections(sections, (
        raw_dump_section({**facts.raw, facts.identity_key: facts.target_dir}),))
    return sections
def render_fupan_report_html(fupan_result: dict, output_path: str,
                             *, skill_dir: str = "") -> str:
    facts = _FupanFacts.of(fupan_result, skill_dir)
    sections = _fupan_sections(facts)
    title = "复盘报告"
    full_html = wrap_html(title, sections, meta=derive_header_meta(
        {facts.identity_key: facts.target_dir}))
    return emit_html(
        full_html, resolve_direct_output_path(output_path),
        log_message="[HTMLReport] 复盘报告已保存: %s (评分: %.0f)",
        log_args=(facts.overall_score,))
def _first_list(*values) -> list | dict:
    for value in values:
        if isinstance(value, dict):
            return value
        if isinstance(value, (list, tuple)):
            return value if isinstance(value, list) else list(value)
    return []
_DIRTY_CARRIER_TYPES = (list, tuple, set, frozenset, str, bytes,
                        int, float, bool)
def _quality_report_usable(qr) -> bool:
    if isinstance(qr, _DIRTY_CARRIER_TYPES):
        return False
    if isinstance(qr, dict):
        return bool(qr)
    return qr is not None
def adapt_fupan_payload(result: dict) -> dict:
    if not isinstance(result, dict):
        return {}
    adapted = dict(result)
    qr = adapted.get("quality_report")
    if not _quality_report_usable(qr):
        adapted["quality_report"] = {
            "overall_score": _fupan_overall_score(adapted, {})}
    adapted["detected_risks"] = _first_list(
        adapted.get("detected_risks"), adapted.get("fupan_detected_risks"))
    adapted["memory_operations"] = _first_list(
        adapted.get("memory_operations"), adapted.get("fupan_memory_ops"))
    if not isinstance(adapted.get("pdca"), dict):
        adapted["pdca"] = {}
    return adapted
_RETRO_SCORE_DIMS = RETRO_SCORE_DIMENSIONS
@dataclass(frozen=True)
class _RetroExtract:
    overall: float
    summary_text: str
    scores: dict
    issues: list
    actions: list
    practices: list
    memory_ops: list
    @classmethod
    def of(cls, result: dict) -> _RetroExtract:
        scores = as_dict(result.get("scores"))
        overall = 0.0
        overall_missing = True
        for overall_raw in (scores.get("overall"),
                            result.get("overall_score")):
            overall_num = _bounded_metric(
                overall_raw, maximum=_SCORE_LIMIT, default=math.nan)
            if not math.isfinite(overall_num):
                continue
            overall = overall_num
            overall_missing = False
            break
        if overall_missing:
            overall = round(sum(
                _bounded_metric(scores.get(k), maximum=_RATIO_LIMIT) * w
                for k, _l, w in _RETRO_SCORE_DIMS) * 100, 2)
        return cls(
            overall=overall,
            summary_text=text_or(result.get("summary")),
            scores=scores,
            issues=_entries(result.get("issues_found"), context="发现问题"),
            actions=_entries(result.get("enhancement_actions"),
                            context="增强行动"),
            practices=_entries(result.get("good_practices"),
                               context="优质操作"),
            memory_ops=_entries(result.get("memory_operations"),
                                context="记忆操作"),
        )
def _retro_overview_sections(extract: _RetroExtract):
    ov_cls = score_band_css(extract.overall)
    issues_css = 'danger' if extract.issues else 'success'
    actions_css = 'warning' if extract.actions else 'success'
    stats = (
        f"{render_stat(f'{extract.overall:.1f}', '五维加权总分', ov_cls)}"
        f"{render_stat(len(extract.issues), '发现问题', issues_css)}"
        f"{render_stat(len(extract.actions), '增强行动', actions_css)}"
        f"{render_stat(len(extract.practices), '优质操作', 'info')}"
        f"{render_stat(len(extract.memory_ops), '记忆操作', 'info')}"
    )
    summary_html = (f"<div class='stat-grid'>{stats}</div>"
                    f"<div class='card'><h3>摘要</h3>"
                    f"<p style='color:#4a5568;'>"
                    f"{_html.escape(extract.summary_text)}</p>"
                    f"</div>")
    return [ReportSection(
        title="执行摘要", section_id="summary", icon="📊",
        html_content=summary_html)]
def _retro_dim_band(val: float) -> tuple[str, str]:
    cls = score_band_css(val * 100)
    return cls, _BAND_COLORS[cls]
def _retro_dims_sections(scores: dict):
    if not scores:
        return []
    dim_rows = []
    for key, label, _w in _RETRO_SCORE_DIMS:
        if key not in scores:
            continue
        val = _bounded_metric(scores.get(key), maximum=_RATIO_LIMIT)
        cls, bar_color = _retro_dim_band(val)
        dim_rows.append([
            _html.escape(label),
            render_stat(f"{val * 100:.0f}", "", cls),
            render_progress_bar(val, 1.0, bar_color),
        ])
    if not dim_rows:
        return []
    return [ReportSection(
        title="五维评分", section_id="dims", icon="🎯",
        html_content=render_table(["维度", "评分", "达成度"], dim_rows,
                                   table_id="tbl_retro_dims"))]
def _score_tile(audit, label: str) -> str | None:
    if not (isinstance(audit, dict) and audit):
        return None
    _score = audit.get("score")
    if _score is None or isinstance(_score, bool):
        return None
    return render_stat(
        _bounded_metric(_score, maximum=_SCORE_LIMIT), label, "info")
def _audit_summary_tiles(diag_audit, cv_audit, treat_audit) -> list[str]:
    tiles: list[str] = []
    _diag_rows = _entries(diag_audit, context="诊断方法审计")
    if _diag_rows:
        tiles.append(render_stat(len(_diag_rows), '诊断方法审计数', 'info'))
    for _audit, _label in ((cv_audit, "CV 审计评分"),
                           (treat_audit, "治疗审计评分")):
        _tile = _score_tile(_audit, _label)
        if _tile is not None:
            tiles.append(_tile)
    return tiles
def _audit_summary_section(diag_audit, cv_audit,
                            treat_audit) -> ReportSection | None:
    _audit_parts = _audit_summary_tiles(diag_audit, cv_audit, treat_audit)
    if not _audit_parts:
        return None
    return ReportSection(
        title="三阶段审计摘要", section_id="audits", icon="🔬",
        html_content=f"<div class='stat-grid'>{''.join(_audit_parts)}</div>")
def _diag_audit_row(it: dict) -> list:
    score = _bounded_metric(it.get("score"), maximum=_SCORE_LIMIT)
    fp_items = [safe_text(x) for x in _present_items(it.get("fp_indicators"))]
    miss_items = [safe_text(x) for x in _present_items(it.get("miss_indicators"))]
    return [
        esc_or(it.get("method_id"), "-"),
        esc_or(it.get("method_name")),
        render_badge(f"{score:.0f}", f"badge-{score_band_css(score)}"),
        str(to_int(it.get("total_findings"))),
        str(to_int(it.get("confirmed_count"))),
        str(to_int(it.get("suppressed_count"))),
        str(to_int(it.get("degraded_count"))),
        str(to_int(it.get("fixable_count"))),
        str(to_int(it.get("fixed_successfully"))),
        str(to_int(it.get("fixed_rolled_back"))),
        f"{_bounded_metric(it.get('precision'), maximum=_RATIO_LIMIT):.0%}",
        f"{_bounded_metric(it.get('fix_success_rate'), maximum=_RATIO_LIMIT):.0%}",
        _html.escape("；".join(fp_items)),
        _html.escape("；".join(miss_items)),
    ]
def _diag_audit_detail_section(_da) -> ReportSection | None:
    _da_rows = [_diag_audit_row(it)
                for it in _entries(_da, context="诊断方法审计明细")]
    if not _da_rows:
        return None
    return ReportSection(
        title=f"诊断方法审计明细（{len(_da_rows)}）",
        section_id="diag_audit", icon="🔎",
        html_content=("<div class='card'>"
                      + render_table(
                          ["方法", "名称", "评分", "总发现", "确认",
                           "抑制", "降级", "可修复", "修复成功",
                           "回滚", "精准度", "修复成功率",
                           "误报指标", "漏报指标"],
                          _da_rows, table_id="tbl_retro_diag_audit",
                          initial_visible=_SHOW_CAP_COMPACT)
                      + "</div>"))
def _json_card_section(title: str, section_id: str, payload,
                       icon: str) -> ReportSection:
    return ReportSection(title=title, section_id=section_id, icon=icon,
                         html_content=_code_card(payload))
def _retro_audit_sections(result: dict):
    sections: list[ReportSection] = []
    _da = result.get("diagnosis_audit")
    extend_sections(sections, (
        _audit_summary_section(
            _da, result.get("cv_audit"), result.get("treatment_audit")),
        _diag_audit_detail_section(_da),
    ))
    for _ak, _atitle in (("cv_audit", "CV 审计明细"),
                         ("treatment_audit", "治疗审计明细")):
        _av = result.get(_ak)
        if isinstance(_av, dict) and _av:
            sections.append(_json_card_section(_atitle, _ak, _av, "🧾"))
    return sections
def _retro_trace_sections(result: dict):
    sections: list[ReportSection] = []
    _enh_log = result.get("enhancement_log")
    if isinstance(_enh_log, list) and _enh_log:
        sections.append(ReportSection(
            title=f"增强实施日志（{len(_enh_log)}）", section_id="enh_log",
            icon="🧬",
            html_content=("<div class='card'>"
                          + render_list_progressive(
                              [_html.escape(_carrier_text(it, compact=True))
                               for it in _enh_log],
                              list_id="retro_enh_log",
                              initial_visible=_SHOW_CAP_COMPACT)
                          + "</div>")))
    _rb_audit = result.get("rollback_audit")
    if isinstance(_rb_audit, dict) and _rb_audit:
        sections.append(_json_card_section(
            "回滚审计", "rollback_audit", _rb_audit, "↩️"))
    return sections
def _issue_row(it: dict) -> list:
    sev = text_or(it.get("severity"), "low").strip().lower()
    _ev_items = _evidence_items(it.get("evidence"))
    return [
        render_badge(sev.upper(), _SEV_BADGE_CSS.get(sev, "badge-muted")),
        esc_or(it.get("phase")),
        esc_or(it.get("method_id"), "-"),
        esc_or(it.get("description")),
        esc_or(it.get("impact")),
        esc_or(it.get("root_cause")),
        esc_or(it.get("remedy")),
        _html.escape("；".join(_ev_items)),
    ]
def _card_table_section(items: list, *, title: str, section_id: str, icon: str,
                        headers: list, row_fn, table_id: str,
                        initial_visible: int):
    if not items:
        return []
    rows = [row_fn(item) for item in _entries(items, context=title)]
    if not rows:
        return []
    return [ReportSection(
        title=f"{title}（{len(rows)}）", section_id=section_id, icon=icon,
        html_content=("<div class='card'>"
                      + render_table(headers, rows, table_id=table_id,
                                      initial_visible=initial_visible)
                      + "</div>"))]
def _priority_badge(it: dict) -> str:
    pri = text_or(it.get("priority"), "P2").strip().upper() or "P2"
    pri_cls = "badge-danger" if pri == "P0" else (
        "badge-warning" if pri == "P1" else "badge-info")
    return render_badge(pri, pri_cls)
def _action_row(it: dict) -> list:
    return [
        _priority_badge(it),
        esc_or(it.get("action_id"), "-"),
        esc_or(it.get("target_type")),
        esc_or(it.get("target_id"), "-"),
        esc_or(it.get("action_type")),
        esc_or(it.get("description")),
        esc_or(it.get("current_value")),
        esc_or(it.get("suggested_value")),
        _confidence_pct_text(it.get("confidence")),
        esc_or(it.get("expected_impact")),
        "已应用" if to_bool(it.get("applied")) else "待审核",
    ]
def _practice_item(p: dict) -> str:
    _mid = p.get("method_id")
    _mid_html = (f" <code>{_html.escape(safe_text(_mid))}</code>"
                 if _mid not in (None, "", "-") else "")
    _ev_items = _evidence_items(p.get("evidence"))
    _ev_html = (
        f"<br><small style='color:#718096'>证据: "
        f"{_html.escape('；'.join(_ev_items))}</small>"
        if _ev_items else "")
    return (
        f"<strong>[{esc_or(p.get('phase'))}]</strong>"
        f"{_mid_html} "
        f"{esc_or(p.get('description'))}"
        + ("（可复用）" if to_bool(p.get("reusable"), default=True) else "")
        + _ev_html)
def _retro_practices_sections(practices: list):
    if not practices:
        return []
    _items = [_practice_item(p) for p in practices if isinstance(p, dict)]
    if not _items:
        return []
    return [ReportSection(
        title=f"优质操作（{len(_items)}）", section_id="practices", icon="⭐",
        html_content=("<div class='card'>"
                      + render_list_progressive(
                          _items, list_id="retro_practices",
                          initial_visible=_SHOW_CAP_COMPACT)
                      + "</div>"))]
def _retro_analysis_sections(extract: _RetroExtract,
                             result: dict) -> list[ReportSection]:
    return [
        *_retro_overview_sections(extract),
        *_retro_dims_sections(extract.scores),
        *_retro_audit_sections(result),
        *_retro_trace_sections(result),
    ]
def _retro_learning_sections(extract: _RetroExtract) -> list[ReportSection]:
    return [
        *_card_table_section(
            extract.issues, title="发现的问题", section_id="issues", icon="⚠️",
            headers=["级别", "阶段", "方法", "描述", "影响",
                     "根因", "建议对策", "证据"],
            row_fn=_issue_row, table_id="tbl_retro_issues",
            initial_visible=_SHOW_CAP_STANDARD),
        *_card_table_section(
            extract.actions, title="增强行动项", section_id="actions", icon="🛠",
            headers=["优先级", "行动ID", "目标类型", "目标ID",
                     "行动类型", "描述", "当前值", "建议值",
                     "置信度", "预期影响", "状态"],
            row_fn=_action_row, table_id="tbl_retro_actions",
            initial_visible=_SHOW_CAP_STANDARD),
        *_retro_practices_sections(extract.practices),
        *_card_table_section(
            extract.memory_ops, title="记忆操作", section_id="memops", icon="🧠",
            headers=["操作", "路径", "原因"], row_fn=_memop_row,
            table_id="tbl_retro_memops",
            initial_visible=_SHOW_CAP_MEDIUM),
    ]
def render_retro_report_html(result: dict, skill_dir: str = "") -> str:
    if not isinstance(result, dict):
        result = {"summary": f"非法输入类型: {type(result).__name__}"}
    extract = _RetroExtract.of(result)
    title = "复盘反哺报告（聚合通道 retrospective）"
    sections = [
        *_retro_analysis_sections(extract, result),
        *_retro_learning_sections(extract),
    ]
    return render_report(title, sections, skill_dir, result)
def _degradation_target_display(it: dict) -> str:
    target = safe_text(it.get("method_id") or it.get("rule_id") or "-")
    name = text_or(it.get("method_name"))
    return f"{target} ({name})" if name else target
def _degradation_status_badge(status: str) -> str:
    label = text_or(status, "-")
    key = label.strip().lower() or "-"
    if key in ("pending", "blocked"):
        tone = "warning"
    else:
        tone = status_badge_css(key, default="danger")
    return render_badge(label, f"badge-{tone}")
def _degradation_item_row(it: dict) -> list:
    status = text_or(it.get("status"), "-")
    return [
        esc_or(it.get("stage"), "-"),
        _html.escape(_degradation_target_display(it)),
        esc_or(it.get("file_path"), "-"),
        _lineno_text(it.get("line")),
        _degradation_status_badge(status),
        esc_or(it.get("reason"), "-"),
        esc_or(it.get("action"), "-"),
    ]
_DEGRADATION_DIAG_LEDGER: tuple[tuple[str, str], ...] = (
    ("总方法数", "total"),
    ("正常完成", "passed"),
    ("失败", "failed"),
    ("降级", "degraded"),
    ("跳过", "skipped"),
)
_DEGRADATION_TREAT_LEDGER: tuple[tuple[str, str], ...] = (
    ("总项数", "total"),
    ("自动修复完成", "fixed"),
    ("AI 修复完成", "ai_fixed"),
    ("已生成修复方案", "planned"),
    ("失败", "failed"),
    ("回滚", "rolled_back"),
    ("降级", "degraded"),
    ("建议销项", "suggestion"),
    ("无修复器", "no_fixer"),
    ("跳过", "skipped"),
    ("误报确认", "fp_confirmed"),
    ("待 AI 审核", "pending_confirm"),
)
def _degradation_ledger_cards(diag: dict, treat: dict) -> str:
    diag_rows = [(label, to_int(diag.get(key)))
                 for label, key in _DEGRADATION_DIAG_LEDGER]
    treat_rows = [(label, to_int(treat.get(key)))
                  for label, key in _DEGRADATION_TREAT_LEDGER]
    return ('<div class="card"><h3>诊断分账</h3>' + kv_table(diag_rows) + '</div>'
            + '<div class="card"><h3>治疗分账</h3>' + kv_table(treat_rows) + '</div>')
def render_degradation_report_html(report: dict, skill_dir: str = "") -> str:
    report = as_dict(report)
    logger.debug("[HtmlReport] render_degradation_report_html 渲染: report=%d 键", len(report))
    diag = as_dict(report.get("diagnosis"))
    treat = as_dict(report.get("treatment"))
    verdict = as_dict(report.get("verdict"))
    verdict_items = _entries(report.get("verdict_items"), context="诊断结论未通过项")
    degraded = _entries(report.get("degraded_items"), context="降级项明细")
    fp_items = _entries(report.get("fp_confirmed_items"), context="误报确认项")
    pending_items = _entries(report.get("pending_confirm_items"),
                             context="待 AI 审核项")
    errors = _entries(report.get("collection_errors"), context="采集错误")
    recs = [safe_text(r) for r in as_list(report.get("recommendations")) if r]
    cnt = _degradation_counters(diag, treat, verdict)
    html = _degradation_stats_html(report, cnt)
    html += _degradation_ledger_cards(diag, treat)
    html += _degradation_verdict_card(verdict, verdict_items)
    html += _degradation_detail_cards(degraded, fp_items, pending_items, recs)
    html += _degradation_error_card(errors)
    return render_report(
        "全流程降级报告",
        [ReportSection(
            title="降级总览", section_id="degradation", icon="⚠️",
            html_content=html)],
        skill_dir, report)
def _degradation_counters(diag: dict, treat: dict,
                          verdict: dict | None = None) -> dict:
    _verdict = as_dict(verdict)
    return {
        "diag_deg": to_int(diag.get("degraded")),
        "diag_fail": to_int(diag.get("failed")),
        "verdict_fail": to_int(_verdict.get("fail")),
        "tx_fail": to_int(treat.get("failed")),
        "tx_deg": to_int(treat.get("degraded")),
        "tx_rb": to_int(treat.get("rolled_back")),
    }
def _degradation_verdict_card(verdict: dict, items: list) -> str:
    """诊断结论分账：verdict=fail 是结论未通过，不是方法执行失败。"""
    if not verdict and not items:
        return ""
    rows = [(label, to_int(verdict.get(key))) for label, key in (
        ("结论未通过（P0）", "fail"),
        ("结论警告", "warn"),
        ("结论通过", "pass"),
    )]
    html = ('<div class="card"><h3>诊断结论（verdict）</h3>'
            '<p>方法均已执行完成；本卡片只记录「诊断结论」的通过与否，'
            '与执行健康（status）分账，不表示方法失败。</p>'
            + kv_table(rows) + '</div>')
    if items:
        html += _degradation_items_card("结论未通过项", "verdict_table", items)
    return html
def _degradation_stats_html(report: dict, cnt: dict) -> str:
    status = text_or(report.get("overall_status"), "unknown")
    _status_key = status.strip().lower()
    status_tone = ("success" if _status_key == "completed"
                   else "danger" if _status_key == "failed" else "warning")
    stats = (
        render_stat(_html.escape(status), "总体状态", status_tone)
        + render_stat(cnt["diag_deg"], "诊断降级", alert_tone(cnt["diag_deg"], "danger"))
        + render_stat(cnt["diag_fail"], "诊断执行失败", alert_tone(cnt["diag_fail"], "danger"))
        + render_stat(cnt["verdict_fail"], "结论未通过(P0)", alert_tone(cnt["verdict_fail"], "warning"))
        + render_stat(cnt["tx_fail"], "治疗失败", alert_tone(cnt["tx_fail"], "danger"))
        + render_stat(cnt["tx_deg"], "治疗降级", alert_tone(cnt["tx_deg"], "warning"))
        + render_stat(cnt["tx_rb"], "回滚", alert_tone(cnt["tx_rb"], "warning"))
    )
    return (f'<div class="stat-grid">{stats}</div>'
            f'<div class="card"><h3>生成时间</h3>'
            f'<p>{esc_or(report.get("generated_at"), "-")}</p></div>')
_DEGRADATION_TABLE_HEADERS = (
    "阶段", "方法/规则", "文件", "行", "状态", "原因", "处置动作")
def _degradation_items_card(title: str, table_id: str, items: list) -> str:
    return ('<div class="card"><h3>' + f'{title} ({len(items)})</h3>'
            + render_table(_DEGRADATION_TABLE_HEADERS,
                            [_degradation_item_row(it) for it in items],
                            table_id=table_id,
                            initial_visible=_SHOW_CAP_WIDE)
            + '</div>')
def _degradation_detail_cards(degraded: list, fp_items: list,
                              pending_items: list, recs: list) -> str:
    cards = ""
    for _title, _table_id, _items in (
            ("降级项明细", "degraded_table", degraded),
            ("误报确认项", "fp_table", fp_items),
            ("待 AI 审核项", "pending_table", pending_items)):
        if _items:
            cards += _degradation_items_card(_title, _table_id, _items)
    if recs:
        cards += ('<div class="card"><h3>处置建议</h3><ul>'
                 + "".join(f"<li>{_html.escape(r)}</li>" for r in recs)
                 + '</ul></div>')
    return cards
def _degradation_error_card(errors: list) -> str:
    if not errors:
        return ""
    rows = [
        [esc_or(it.get("stage"), "-"), esc_or(it.get("error"), "-")]
        for it in errors
    ]
    return ('<div class="card"><h3>' + f'采集错误 ({len(rows)})</h3>'
            + render_table(["阶段", "错误"], rows, table_id="collect_errors",
                           initial_visible=_SHOW_CAP_WIDE)
            + '</div>')
def _treatment_detail_rows(ctx, plan_ctx: dict) -> list:
    raw_rows = []
    for key in ("item_index", "index", "status", "strategy", "priority",
                "rule_id", "severity", "file", "line", "message", "reason",
                "locator", "fix_guidance", "elapsed_s"):
        value = ctx(key)
        if key == "line":
            value = normalize_line_value(value) or "-"
        raw_rows.append((key, value))
    raw_rows = [(k, v) for k, v in raw_rows if v not in ("-", None, "")
                or k in ("status", "strategy")]
    _canonical = plan_ctx.get("rule_id_canonical", "")
    if _canonical not in ("", None, "-"):
        raw_rows.append(("rule_id_canonical", _canonical))
    return [(key, render_ctx_cell(value, DISCLOSURE_TEXT_CAP))
            for key, value in raw_rows]
def _treatment_index(result: dict):
    idx = result.get("item_index")
    if idx is None:
        idx = result.get("index")
    if idx is None or isinstance(idx, bool) or idx == "":
        return "-"
    return safe_text(idx)
_TREATMENT_PLAN_KEYS: tuple[tuple[str, str], ...] = (
    ("plan_id", "计划 ID"),
    ("status", "计划状态"),
    ("strategy", "策略"),
    ("ai_action", "AI 动作"),
    ("has_fixer", "匹配修复器"),
    ("fixer_name", "修复器"),
    ("fixer_tier", "修复器等级"),
    ("fixer_type", "修复器类型"),
    ("auto_safe", "可自动修复"),
    ("regression_plan", "回归计划"),
)
def _treatment_plan_rows(plan_ctx: dict) -> list[tuple[str, str]]:
    rows: list[tuple[str, str]] = []
    for key, label in _TREATMENT_PLAN_KEYS:
        value = plan_ctx.get(key)
        if value in (None, "", "-"):
            continue
        rows.append((label, render_ctx_cell(value, DISCLOSURE_TEXT_CAP)))
    return rows
def _treatment_plan_section(plan_ctx: dict) -> ReportSection | None:
    rows = _treatment_plan_rows(plan_ctx)
    if not rows:
        return None
    return ReportSection(
        title="修复方案（执行决策 · 完整载荷见 JSON 落盘文件）",
        html_content=("<div class='card'>" + kv_table_preescaped(rows)
                      + "</div>"),
        section_id="plan", icon="🛠")
def _treatment_optional_sections(plan_ctx: dict, ctx) -> list[ReportSection]:
    sections: list[ReportSection] = []
    for key, title, section_id, icon in (
        ("fix_precheck", "修复前三问预检", "precheck", "❓"),
        ("fixer_risk", "修复器风险元数据", "fixer_risk", "⚠️"),
    ):
        value = plan_ctx.get(key)
        if isinstance(value, dict) and value:
            sections.append(ReportSection(
                title=title, section_id=section_id, icon=icon,
                html_content=_kv_card(value)))
    snippet = ctx("code_snippet")
    if snippet and snippet != "-":
        sections.append(ReportSection(
            title="问题代码片段",
            html_content=f"<div class='card'>{render_code_block(snippet)}</div>",
            section_id="snippet", icon="📜"))
    return sections
def render_treatment_item_html(result: dict, skill_dir: str = "") -> str:
    result = as_dict(result)
    logger.debug("[HtmlReport] render_treatment_item_html 渲染: result=%d 键", len(result))
    idx = _treatment_index(result)
    status = safe_text(result.get("status") or "-")
    _treat = f"TREAT-{idx} · " if idx != "-" else ""
    title = f"治疗项报告 · {_treat}{status}"
    fix_plan = result.get("fix_plan") or result.get("plan")
    plan_ctx = fix_plan if isinstance(fix_plan, dict) else {}
    raw_finding = plan_ctx.get("raw_finding")
    raw_ctx = raw_finding if isinstance(raw_finding, dict) else {}
    def _ctx(key: str):
        for source in (result, plan_ctx):
            value = source.get(key)
            if value not in (None, "", "-"):
                return value
        return raw_ctx.get(key, "-")
    rows = _treatment_detail_rows(_ctx, plan_ctx)
    sections = [ReportSection(
        title="治疗项详情",
        html_content=f"<div class='card'>{kv_table_preescaped(rows)}</div>",
        section_id="detail", icon="💉")]
    sections.extend(_treatment_optional_sections(plan_ctx, _ctx))
    if fix_plan:
        extend_sections(sections, (_treatment_plan_section(plan_ctx),))
    return render_report(title, sections, skill_dir, result)

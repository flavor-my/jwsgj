from __future__ import annotations

import html as _html
import logging
import math
import os
import sys
from dataclasses import dataclass
from typing import NamedTuple

from jwsgj.diag_types_normalize import (
    coerce_mapping,
    grade_from_score,
    iter_payload_finding_items,
    normalize_passed,
)
from jwsgj.diag_types_vocab import (
    ANTIPATTERN_PREFIXES,
    FIELD_POTENTIAL_FP,
    FINDING_LIST_KEYS,
    SEVERITY_RANK,
    STRUCTURED_EXCLUDED_KEYS,
    STRUCTURED_PRIORITY_KEYS,
    diag_severity_to_p,
)
from jwsgj.html_report_primitives import (
    DISCLOSURE_ROWS_COMPACT,
    DISCLOSURE_ROWS_STANDARD,
    DISCLOSURE_ROWS_TINY,
    TEXT_BLOCK_SAFE_CAP,
    HTMLReport,
    ReportSection,
    artifact_row,
    derive_header_meta,
    dump_or_str,
    emit_html,
    empty_card,
    extend_sections,
    extract_finding_coords,
    is_nonfinite_float,
    kv_table,
    list_card_section,
    normalize_line_value,
    payload_is_skill,
    raw_dump_section,
    read_field,
    render_badge,
    render_json_summary,
    render_report,
    render_stat,
    render_structured_details,
    render_table,
    risk_level_label_css,
    safe_text,
    score_band_css,
    status_badge_css,
    text_or,
    to_finite_float,
    to_int,
    wrap_html,
)
from jwsgj.html_report_stage_doc import artifact_root_hint

logger = logging.getLogger(__name__)
__all__ = [
    "artifacts_section",
    "render_blindspot_report_html",
    "render_diagnosis_report_html",
    "render_fallback_html",
    "render_feedback_step_html",
    "render_file_scan_report_html",
    "render_health_report_html",
    "render_security_report_html",
    "render_single_method_html",
]
logger.info("html_render_diag 已加载: %d 项导出（单方法/诊断/盲点/健康/扫描/安全证据报告）", len(__all__))
_DEFAULT_TABLE_INITIAL_VISIBLE = DISCLOSURE_ROWS_STANDARD
_DEFAULT_OUTPUT_PATH: str = ""
_DEFAULT_SKILL_DIR = ""
def _is_finding_list_key(k) -> bool:
    if not isinstance(k, str):
        return False
    if k.endswith("findings") or k == "findings_list":
        return True
    if k in FINDING_LIST_KEYS:
        return True
    return any(k.startswith(p) for p in ANTIPATTERN_PREFIXES)
_SCAN_CONTAINER_KEYS = frozenset({"payload", "result", "data"})
_SCAN_ID_KEYED_KEYS = frozenset({
    "sub_results", "detector_results", "results", "engines",
})
_FINDING_SEQUENCE_TYPES = (list, tuple)
_SCAN_MAX_DEPTH = 6
def _severity_text(value) -> str:
    if value is None:
        return ""
    return safe_text(getattr(value, "value", value) or "").strip()
def _finding_row(fd: dict) -> tuple[tuple, list[str]]:
    rid = safe_text(fd.get("rule_id") or fd.get("id") or "-")
    sev = _severity_text(fd.get("severity") or fd.get("level")) or "-"
    f, ln_disp = extract_finding_coords(fd)
    msg = safe_text(fd.get("message") or fd.get("summary")
                    or fd.get("description") or "-")
    identity = safe_text(fd.get("finding_id") or "")
    key = (identity, rid, f, ln_disp, msg)
    row = [
        _html.escape(rid), _html.escape(sev), _html.escape(f),
        _html.escape(ln_disp or "-"), _html.escape(msg),
    ]
    return key, row
def _summary_card(text: str) -> str:
    return (f"<div class='card'><h3>摘要</h3>"
            f"<p>{_html.escape(safe_text(text))}</p></div>")
def _as_mapping(value) -> dict:
    if isinstance(value, dict):
        return value
    return coerce_mapping(value) or {}
def _mapping_items(value) -> list[dict]:
    if not isinstance(value, (list, tuple)):
        return []
    items: list[dict] = []
    dropped = 0
    for item in value:
        mapping = coerce_mapping(item)
        if mapping is None:
            dropped += 1
            continue
        items.append(mapping)
    if dropped:
        logger.debug("条目载体非映射已跳过 %d 条: 集合类型=%s",
                     dropped, type(value).__name__)
    return items
def _sequence_items(value) -> list:
    return list(value) if isinstance(value, (list, tuple)) else []
_ISSUE_TEXT_CAP = 300
def _issue_text(issue) -> str:
    mapping = coerce_mapping(issue)
    if mapping is None:
        return safe_text(issue)
    for key in ("message", "description", "label", "title", "reason",
                "suggestion", "dimension"):
        value = mapping.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    if not mapping:
        return ""
    return dump_or_str(mapping, _ISSUE_TEXT_CAP)
class _FindingCollector:
    __slots__ = ("_seen", "cap", "rows")
    def __init__(self, cap: int | None = None):
        self.rows: list[list] = []
        self.cap = 2 ** 31 - 1 if cap is None else cap
        self._seen: set = set()
    def full(self) -> bool:
        return len(self.rows) >= self.cap
    def push(self, fd: dict) -> None:
        key, row = _finding_row(fd)
        if key in self._seen:
            return
        self._seen.add(key)
        self.rows.append(row)
    def push_items(self, items) -> None:
        if self.full():
            return
        for item in items:
            mapping = coerce_mapping(item)
            if mapping is not None:
                self.push(mapping)
            if self.full():
                return
    def scan(self, node, depth: int = 0) -> None:
        if depth > _SCAN_MAX_DEPTH or self.full():
            return
        if isinstance(node, dict):
            for k, v in node.items():
                if self.full():
                    return
                self._scan_value(k, v, depth)
            return
        if isinstance(node, _FINDING_SEQUENCE_TYPES):
            for it in node:
                self.scan(it, depth + 1)
                if self.full():
                    return
    def _scan_value(self, key, value, depth: int) -> None:
        if (_is_finding_list_key(key)
                and isinstance(value, _FINDING_SEQUENCE_TYPES)):
            self.push_items(value)
            return
        if key in _SCAN_ID_KEYED_KEYS and isinstance(value, dict):
            for entry in value.values():
                self.scan(entry, depth + 1)
                if self.full():
                    return
            return
        if (isinstance(value, (dict, *_FINDING_SEQUENCE_TYPES))
                and key in _SCAN_CONTAINER_KEYS):
            self.scan(value, depth + 1)
def _extract_findings_rows(result: dict, cap: int | None = None) -> list[list]:
    if not isinstance(result, dict):
        return []
    collector = _FindingCollector(cap)
    _top = result.get("findings_list")
    if isinstance(_top, _FINDING_SEQUENCE_TYPES):
        collector.push_items(_top)
    _pl = result.get("payload")
    if isinstance(_pl, dict) and not collector.full():
        collector.push_items(iter_payload_finding_items(_pl))
    collector.scan(result)
    return collector.rows
def _single_method_overview_section(result: dict,
                                   findings_total: int) -> ReportSection:
    status = result.get("status") or "-"
    stat_cls = status_badge_css(status)
    findings_count = max(_count_total(result.get("findings_count"), 0),
                         findings_total)
    stats = (
        f"{render_stat(_html.escape(safe_text(status)), '状态', stat_cls)}"
        f"{render_stat(findings_count, '发现项数', 'info')}"
        f"{render_stat(_elapsed_text(result.get('elapsed_s')), '耗时(秒)', 'info')}"
    )
    error_html = (
        f"<div class='card'><h3>错误</h3><pre>"
        f"{_html.escape(safe_text(result.get('error', '')))}</pre></div>"
        if result.get("error") else "")
    summary_text = _str_field(result, "summary")
    summary = _summary_card(summary_text) if summary_text else ""
    return ReportSection(
        title="执行概览",
        html_content=f"<div class='stat-grid'>{stats}</div>{summary}{error_html}",
        section_id="overview", icon="📋")
def _single_method_findings_section(rows: list[list]) -> ReportSection | None:
    if not rows:
        return None
    return ReportSection(
        title=f"发现项明细（{len(rows)}）",
        html_content=("<div class='card'>"
                      + render_table(
                          ["规则", "严重度", "文件", "行号", "消息"],
                          rows, table_id="tbl_sm_findings",
                          initial_visible=_DEFAULT_TABLE_INITIAL_VISIBLE)
                      + "</div>"),
        section_id="findings", icon="🔎")
_LEAN_PAYLOAD_SCALAR_KEYS = (
    "status", "summary", "findings_count", "elapsed_ms", "elapsed_s", "error",
    "warnings", "file_count", "profile_count", "total_defects",
    "verdict_stats", "avg_health_score", "needs_split", "needs_refactor",
    "engine", "sub_engines", "detectors", "stats", "source_fingerprint",
    "conflicts", "degradation_context", "quality_flags", "evidence_types",
)
_LEAN_SUB_ENTRY_KEYS = (
    "sub_status", "empty_scan", "findings_count", "elapsed_ms", "warnings",
    "error", "summary",
)
_LEAN_PROFILE_SAMPLE = 5
def _lean_sequence(key: str, items) -> dict:
    if _is_finding_list_key(key):
        return {f"{key}_count": len(items)}
    return {f"{key}_count": len(items),
            key: list(items[:DISCLOSURE_ROWS_COMPACT])}
def _verdict_histogram(profiles: list) -> dict:
    counts: dict = {}
    for profile in profiles:
        if not isinstance(profile, dict):
            continue
        verdict = safe_text(profile.get("verdict") or "-")
        counts[verdict] = counts.get(verdict, 0) + 1
    return counts
def _lean_profile(profile: dict) -> dict:
    view: dict = {}
    for key, value in profile.items():
        if isinstance(value, (list, tuple)):
            view[f"{key}_count"] = len(value)
        elif isinstance(value, dict):
            view[f"{key}_keys"] = len(value)
        else:
            view[key] = value
    return view
def _lean_result_view(result: dict) -> dict:
    view: dict = {}
    for key, value in result.items():
        if key == "payload" and isinstance(value, dict):
            view["payload"] = _lean_payload_view(value)
        elif key in _LEAN_PAYLOAD_SCALAR_KEYS:
            view[key] = value
        elif isinstance(value, (list, tuple)):
            view.update(_lean_sequence(key, value))
        elif isinstance(value, dict):
            view[f"{key}_keys"] = len(value)
        else:
            view[key] = value
    return view
def _lean_sub_results(sub_results: dict) -> dict:
    view: dict = {}
    for sub_id, entry in sub_results.items():
        if not isinstance(entry, dict):
            view[safe_text(sub_id)] = entry
            continue
        lean_entry = {key: entry[key] for key in _LEAN_SUB_ENTRY_KEYS
                      if key in entry}
        result = entry.get("result")
        if isinstance(result, dict):
            lean_entry["result"] = _lean_result_view(result)
        view[safe_text(sub_id)] = lean_entry
    return view
def _lean_payload_view(payload: dict) -> dict:
    view: dict = {}
    for key, value in payload.items():
        if key in ("sub_results", "detector_results") and isinstance(value, dict):
            view[key] = _lean_sub_results(value)
        elif key == "profiles" and isinstance(value, list):
            view["profile_count"] = len(value)
            view["profile_verdicts"] = _verdict_histogram(value)
            view["profiles_sample"] = [
                _lean_profile(p) for p in value[:_LEAN_PROFILE_SAMPLE]
                if isinstance(p, dict)]
        elif isinstance(value, (list, tuple)):
            view.update(_lean_sequence(key, value))
        elif isinstance(value, dict) and len(value) > DISCLOSURE_ROWS_COMPACT:
            view[f"{key}_keys"] = len(value)
        else:
            view[key] = value
    return view
def _single_method_payload_section(result: dict,
                                   skill_dir: str = _DEFAULT_SKILL_DIR) -> ReportSection | None:
    payload = _as_mapping(result.get("payload"))
    if not payload:
        return None
    inner = _as_mapping(payload.get("payload"))
    if inner:
        source = {key: value for key, value in payload.items()
                  if key != "payload"}
        source.update(inner)
    else:
        source = payload
    payload_view = _lean_payload_view(source)
    return ReportSection(
        title="业务 Payload（摘要视图 · 完整明细见 JSON 落盘文件）",
        html_content=("<div class='card'>"
                      + render_json_summary(
                          payload_view,
                          source_hint=artifact_root_hint(skill_dir))
                      + "</div>"),
        section_id="payload", icon="📦")
def render_single_method_html(result: dict, skill_dir: str = _DEFAULT_SKILL_DIR) -> str:
    result = _as_mapping(result)
    logger.debug("[HtmlReport] render_single_method_html 渲染: result=%d 键", len(result))
    mid = safe_text(result.get("method_id") or "")
    name = safe_text(result.get("method_name") or "")
    suffix = " ".join(part for part in (mid, name) if part)
    title = f"诊断方法报告 · {suffix}" if suffix else "诊断方法报告"
    rows = _extract_findings_rows(result)
    sections = [_single_method_overview_section(result, len(rows))]
    extend_sections(sections, (
        _single_method_findings_section(rows),
        _single_method_payload_section(result, skill_dir),
    ))
    return render_report(title, sections, skill_dir, result)
def _feedback_overview_section(result: dict, status: str) -> ReportSection:
    stats = (
        f"{render_stat(_html.escape(safe_text(status)), '状态', status_badge_css(status))}"
        f"{render_stat(_elapsed_text(result.get('elapsed_s')), '耗时(秒)', 'info')}"
    )
    summary_text = _str_field(result, "summary", "message")
    summary = _summary_card(summary_text) if summary_text else ""
    return ReportSection(
        title="执行概览",
        html_content=f"<div class='stat-grid'>{stats}</div>{summary}",
        section_id="overview", icon="🔄")
def _feedback_fields_section(result: dict) -> ReportSection | None:
    interesting = {k: v for k, v in result.items()
                   if k not in ("status", "elapsed_s", "summary", "message")
                   and isinstance(v, (str, int, float, bool))}
    if not interesting:
        return None
    field_rows = [(k, "N/A" if is_nonfinite_float(v) else v)
                  for k, v in sorted(interesting.items(),
                                     key=lambda kv: safe_text(kv[0]))]
    return ReportSection(
        title="关键结果字段",
        html_content=f"<div class='card'>{kv_table(field_rows)}</div>",
        section_id="fields", icon="🧾")
def render_feedback_step_html(result: dict, skill_dir: str = _DEFAULT_SKILL_DIR,
                              step_name: str = "") -> str:
    result = _as_mapping(result)
    logger.debug("[HtmlReport] render_feedback_step_html 渲染: result=%d 键", len(result))
    title = ("反哺步骤报告 · "
             f"{safe_text(step_name or result.get('step') or 'step')}")
    status = safe_text(result.get("status") or "unknown")
    sections = [_feedback_overview_section(result, status)]
    extend_sections(sections, (_feedback_fields_section(result),))
    structured_html = render_structured_details(
        result, priority_keys=STRUCTURED_PRIORITY_KEYS,
        excluded_keys=STRUCTURED_EXCLUDED_KEYS)
    if structured_html:
        sections.append(ReportSection(
            title="结构化详情", section_id="structured", icon="🗂",
            html_content=structured_html))
    return render_report(title, sections, skill_dir, result,
                          step=step_name or result.get("step") or "")
_JUDGMENT_STATUS_STYLE: dict[str, tuple[str, str]] = {
    "pass": ("PASS", "badge-success"),
    "warn": ("WARN", "badge-warning"),
    "fail": ("FAIL", "badge-danger"),
    "info": ("INFO", "badge-info"),
}
_BS_SEVERITIES: tuple[tuple[str, str, str], ...] = (
    ("critical", "badge-danger", "#e53e3e"),
    ("high", "badge-danger", "#f97316"),
    ("medium", "badge-warning", "#eab308"),
    ("low", "badge-info", "#3b82f6"),
    ("info", "badge-muted", "#6b7280"),
)
_BS_SEV_ORDER = [sev for sev, _badge, _color in _BS_SEVERITIES]
_BS_SEV_RANK = {sev: rank for rank, sev in enumerate(_BS_SEV_ORDER)}
_BS_SEV_COLORS = {sev: color for sev, _badge, color in _BS_SEVERITIES}
def _severity_keys(merged: dict) -> list[str]:
    return [*_BS_SEV_ORDER, *sorted(k for k in merged if k not in _BS_SEV_RANK)]
def _norm_key(value) -> str:
    return safe_text(value).strip().lower()
def _sum_count_values(values) -> float:
    total = 0.0
    for value in values:
        count = max(to_finite_float(value), 0.0)
        if count > sys.float_info.max - total:
            return sys.float_info.max
        total += count
    return total
def _merge_counts(counts: dict) -> dict[str, float]:
    merged: dict[str, float] = {}
    for key, count in counts.items():
        name = _norm_key(key)
        merged[name] = _sum_count_values((merged.get(name, 0.0), count))
    return merged
def _count_total(raw_total, fallback: float) -> int:
    fallback_count = max(0, int(_sum_count_values((fallback,))))
    if raw_total is None:
        return fallback_count
    num = to_finite_float(raw_total, math.nan)
    return fallback_count if math.isnan(num) else max(fallback_count, 0, int(num))
def _finite_value(value) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    number = to_finite_float(value, math.nan)
    return number if math.isfinite(number) else None
def _score_text(score) -> str:
    return "-" if score is None else f"{score:.0f}"
def _elapsed_text(value) -> str:
    seconds = _finite_value(value)
    return "-" if seconds is None else f"{round(seconds, 1)}"
def _pct_text(value) -> str:
    pct = _finite_value(value)
    return "-" if pct is None else f"{pct}%"
def _liveness_value(value) -> float | None:
    rate = _finite_value(value)
    return rate if rate is not None and 0.0 <= rate <= 1.0 else None
def _liveness_text(value) -> str:
    rate = _liveness_value(value)
    return "-" if rate is None else f"{rate:.0%}"
def _ms_text(value) -> str:
    millis = _finite_value(value)
    return "-" if millis is None else f"{millis:.0f}ms"
def _kb_text(value) -> str:
    size = _finite_value(value)
    return "-" if size is None else f"{size / 1024:.1f}KB"
def _str_field(raw: dict, *keys: str) -> str:
    for key in keys:
        value = raw.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""
_BS_SEV_BADGE = {sev: badge for sev, badge, _color in _BS_SEVERITIES}
_IDENTITY_DIR_KEYS = ("skill_dir", "skill_path", "project_root", "root",
                      "path", "target_dir", "target")
def _first_text(raw: dict, *keys: str) -> str:
    for key in keys:
        value = raw.get(key)
        if value is None:
            continue
        text = safe_text(value).strip()
        if text:
            return text
    return ""
class _DiagHeaderFields(NamedTuple):
    target_name: str
    version: str
    mode: str
    target_dir: str
    summary: str
    is_skill: bool
_DIAG_STATUS_STYLE: dict[str, tuple[str, str]] = {
    "healthy": ("HEALTHY", "health-clean"),
    "warning": ("WARNING", "health-warning"),
    "critical": ("CRITICAL", "health-critical"),
}
def _dir_name(path) -> str:
    text = safe_text(path or "").strip()
    if not text:
        return ""
    return os.path.basename(os.path.normpath(text))
def _as_text(value, default: str = "") -> str:
    if value is None:
        return default
    return safe_text(value) or default
def _fmt_location(filepath, line) -> str:
    _fp = safe_text(filepath or "").strip()
    _line = normalize_line_value(line)
    if _fp and _line:
        return f"{_fp}:{_line}"
    if _fp:
        return _fp
    return f"行 {_line}" if _line else ""
def _payload_line(line):
    if isinstance(line, (bool, float)):
        return None
    return line
def _count_stat_text(value) -> str:
    if value is None or isinstance(value, bool):
        return "-"
    if isinstance(value, int):
        count = value
    else:
        count = None
        if isinstance(value, str):
            try:
                count = int(value.strip())
            except (ValueError, OverflowError):
                pass
        if count is None:
            number = _finite_value(value)
            if number is None:
                return "-"
            count = to_int(number)
    return _html.escape(str(count))
def _failure_count_css(value) -> str:
    count = _finite_value(value)
    if count is None:
        return "info"
    return "danger" if count > 0 else "success"
def _strip_null_items(items: list) -> list:
    return [x for x in items if x is not None]
def _issue_entries(value) -> list[dict]:
    entries: list[dict] = []
    for item in _sequence_items(value):
        mapping = coerce_mapping(item)
        if mapping is not None:
            entries.append(mapping)
            continue
        text = _issue_text(item)
        if text:
            entries.append({"description": text})
    return entries
def _diag_baseline_html(baselines: dict) -> str:
    previous_raw = baselines.get("previous_score")
    if previous_raw is None:
        return ""
    current_raw = baselines.get("current_score")
    delta_raw = baselines.get("delta")
    previous = to_finite_float(previous_raw, math.nan)
    current = to_finite_float(current_raw, math.nan)
    delta = to_finite_float(delta_raw, math.nan)
    if not math.isfinite(delta) and math.isfinite(current) and math.isfinite(previous):
        delta = current - previous
    delta_known = math.isfinite(delta)
    arrow = ("&#9650;" if delta > 0 else "&#9660;" if delta < 0
             else "&#8594;")
    delta_color = ("#38a169" if delta > 0 else "#e53e3e" if delta < 0
                   else "#718096")
    delta_text = f"{abs(delta):g}" if delta_known else "-"
    previous_text = f"{previous:g}" if math.isfinite(previous) else "-"
    current_text = f"{current:g}" if math.isfinite(current) else "-"
    return (
        f'<div style="margin-top:12px;padding-top:12px;border-top:1px solid #e2e8f0;">'
        f'<span style="color:#718096;font-size:13px;">基线对比:</span> '
        f'<span style="font-weight:600;">{_html.escape(previous_text)} -> {_html.escape(current_text)}</span> '
        f'<span style="color:{delta_color};margin-left:8px;">{arrow} {delta_text}</span>'
        f'</div>'
    )
def _diag_judgment_row(j: dict) -> list[str]:
    s = _norm_key(j.get("status") or "info")
    label, badge = _JUDGMENT_STATUS_STYLE.get(
        s, (s.upper() or "UNKNOWN", "badge-muted"))
    return [render_badge(label, badge),
            _html.escape(safe_text(j.get("label") or ""))]
def _diag_judgments_section(judgments: list) -> ReportSection:
    j_rows = [_diag_judgment_row(j) for j in judgments if isinstance(j, dict)]
    judgments_html = render_table(["状态", "判定项"], j_rows, table_id="judgments_table")
    return ReportSection(title="判定详情", section_id="judgments", icon="⚖", html_content=judgments_html)
def _diag_callchain_section(cc: dict) -> ReportSection:
    o_class = _failure_count_css(cc.get("orphans"))
    bp_class = _failure_count_css(cc.get("break_points"))
    se_class = _failure_count_css(cc.get("syntax_errors"))
    cc_html = f"""
<div class="card">
  <div class="stat-grid" style="grid-template-columns:repeat(auto-fit, minmax(120px, 1fr));">
    {render_stat(_count_stat_text(cc.get("total_functions")), "总函数", "info")}
    {render_stat(_count_stat_text(cc.get("public_functions")), "公开函数", "info")}
    {render_stat(_count_stat_text(cc.get("total_calls")), "总调用", "info")}
    {render_stat(_count_stat_text(cc.get("cross_file_calls")), "跨文件调用", "info")}
    {render_stat(_count_stat_text(cc.get("orphans")), "孤立函数", o_class)}
    {render_stat(_count_stat_text(cc.get("break_points")), "断裂点", bp_class)}
    {render_stat(_count_stat_text(cc.get("external_deps")), "外部依赖", "info")}
    {render_stat(_count_stat_text(cc.get("syntax_errors")), "语法错误", se_class)}
  </div>
</div>"""
    return ReportSection(title="调用链诊断", section_id="callchain", icon="🔗", html_content=cc_html)
def _diag_blindspots_section(bs: dict) -> ReportSection:
    by_sev = _merge_counts(_as_mapping(bs.get("by_severity")))
    derived_total = _count_total(
        bs.get("total_blindspots"), _sum_count_values(by_sev.values()))
    bs_total = _count_total(bs.get("total"), derived_total)
    if by_sev:
        _sev_items = sorted(
            by_sev.items(),
            key=lambda kv: (_BS_SEV_RANK.get(kv[0], len(_BS_SEV_RANK)), kv[0]))
        sev_rows = [[
            f'<span style="color:{_BS_SEV_COLORS.get(s, "#6b7280")};font-weight:bold;">{_html.escape(s.upper())}</span>',
            _count_stat_text(c),
        ] for s, c in _sev_items]
        bs_html = f"""
<div class="card">
  <div class="stat-grid">{render_stat(bs_total, "盲点总数", "warning" if bs_total > 0 else "success")}</div>
</div>
<div class="card">
  <h3>按严重度分布</h3>
  {render_table(["严重度", "数量"], sev_rows, table_id="blindspots_table")}
</div>"""
    else:
        bs_html = f'<div class="card">{render_stat(bs_total, "盲点总数", "warning" if bs_total > 0 else "success")}</div>'
    return ReportSection(title="盲点扫描", section_id="blindspots", icon="🔦", html_content=bs_html)
def _diag_bizflow_section(bf: dict) -> ReportSection:
    _liveness_f = _liveness_value(bf.get("liveness_rate"))
    l_class = "info" if _liveness_f is None else _liveness_css(_liveness_f)
    _liveness_txt = _liveness_text(_liveness_f)
    bf_html = f'<div class="card"><div class="stat-grid">{render_stat(_html.escape(_liveness_txt), "活性率", l_class)}</div></div>'
    return ReportSection(title="业务流活性", section_id="bizflows", icon="🔄", html_content=bf_html)
def _diag_simulation_section(sim: dict) -> ReportSection:
    f_class = _failure_count_css(sim.get("failed"))
    sim_dur = _finite_value(sim.get("duration_sec"))
    sim_dur_txt = "-" if sim_dur is None else f"{round(sim_dur, 1)}s"
    sim_html = f"""
<div class="card">
  <div class="stat-grid" style="grid-template-columns:repeat(auto-fit, minmax(140px, 1fr));">
    {render_stat(_count_stat_text(sim.get("entry_points")), "入口点", "info")}
    {render_stat(_count_stat_text(sim.get("executed")), "已执行", "success")}
    {render_stat(_count_stat_text(sim.get("failed")), "失败", f_class)}
    {render_stat(sim_dur_txt, "耗时", "info")}
  </div>
</div>"""
    return ReportSection(title="模拟诊断", section_id="simulation", icon="🧪", html_content=sim_html)
def _diag_header_fields(report: dict) -> _DiagHeaderFields:
    target_dir = _first_text(report, *_IDENTITY_DIR_KEYS)
    target_name = _first_text(
        report, "skill", "skill_name", "project", "project_name", "name")
    target_name = target_name or _dir_name(target_dir)
    version = _first_text(report, "version", "tool_version", "jws_version")
    return _DiagHeaderFields(
        target_name=target_name or "Unknown",
        version=version or "?",
        mode=_first_text(report, "mode") or "?",
        target_dir=target_dir,
        summary=_str_field(report, "health_summary", "summary"),
        is_skill=payload_is_skill(report),
    )
@dataclass(frozen=True)
class _DiagFacts:
    report: dict
    header: _DiagHeaderFields
    score: float | None
    status: str
    errors: list
    judgments: list
    recs: list
    baselines: dict
    cc: dict
    bs: dict
    bf: dict
    sim: dict
    @classmethod
    def of(cls, report: dict) -> _DiagFacts:
        report = _as_mapping(report)
        return cls(
            report=report,
            header=_diag_header_fields(report),
            score=_finite_value(report.get("health_score")),
            status=_norm_key(report.get("status") or "unknown"),
            errors=[text for item in _sequence_items(report.get("errors"))
                    if item is not None and (text := _issue_text(item))],
            judgments=_mapping_items(report.get("judgments")),
            recs=_strip_null_items(_sequence_items(report.get("recommendations"))),
            baselines=_as_mapping(report.get("baseline")),
            cc=_as_mapping(report.get("call_chain")),
            bs=_as_mapping(report.get("blindspots")),
            bf=_as_mapping(report.get("business_flows")),
            sim=_as_mapping(report.get("simulation")),
        )
def _diag_summary_section(facts: _DiagFacts) -> ReportSection:
    header = facts.header
    health_label, health_css = _DIAG_STATUS_STYLE.get(
        facts.status, (facts.status.upper() or "UNKNOWN", "health-warning"))
    score_css = "info" if facts.score is None else score_band_css(facts.score)
    info_title = "技能信息" if header.is_skill else "项目信息"
    name_label = "技能名称" if header.is_skill else "项目名称"
    html_content = f"""
<div class="stat-grid">
  {render_stat(_score_text(facts.score), "健康评分", score_css)}
  {render_stat(len(facts.errors), "错误数", "danger" if facts.errors else "success")}
  {render_stat(len(facts.judgments), "判定项", "info")}
  {render_stat(len(facts.recs), "建议数", "info")}
</div>
<div class="card">
  <h3>状态概览</h3>
  <span class="health-badge {health_css}">{_html.escape(health_label)}</span>
  <span style="margin-left:16px;color:#4a5568;">{_html.escape(header.summary)}</span>
  {_diag_baseline_html(facts.baselines)}
</div>
<div class="card">
  <h3>{info_title}</h3>
  <table style="width:auto;">
    <tr><td style="color:#718096;padding-right:16px;">{name_label}</td><td><strong>{_html.escape(header.target_name)}</strong></td></tr>
    <tr><td style="color:#718096;">版本</td><td>{_html.escape(header.version)}</td></tr>
    <tr><td style="color:#718096;">模式</td><td>{_html.escape(header.mode)}</td></tr>
    <tr><td style="color:#718096;">路径</td><td style="font-size:13px;word-break:break-all;">{_html.escape(header.target_dir)}</td></tr>
  </table>
</div>
"""
    return ReportSection(title="执行摘要", section_id="summary", icon="📊",
                         html_content=html_content)
def _diag_sections(facts: _DiagFacts) -> list[ReportSection]:
    sections: list[ReportSection] = [_diag_summary_section(facts)]
    extend_sections(sections, (
        _diag_judgments_section(facts.judgments) if facts.judgments else None,
        _diag_callchain_section(facts.cc) if facts.cc else None,
        _diag_blindspots_section(facts.bs) if facts.bs else None,
        _diag_bizflow_section(facts.bf) if facts.bf else None,
        _diag_simulation_section(facts.sim) if facts.sim else None,
        list_card_section(facts.recs, title="改进建议",
                          section_id="recommendations", icon="💡")
        if facts.recs else None,
        list_card_section(facts.errors, title="错误日志",
                          section_id="errors", icon="❌",
                          item_style="color:#e53e3e;")
        if facts.errors else None,
    ))
    extend_sections(sections, (raw_dump_section(facts.report),))
    return sections
def render_diagnosis_report_html(report: dict, output_path: str | None = _DEFAULT_OUTPUT_PATH) -> str:
    facts = _DiagFacts.of(report)
    sections = _diag_sections(facts)
    header = facts.header
    title = f"诊断报告 - {header.target_name}"
    _identity_key = "skill_dir" if header.is_skill else "project_root"
    full_html = wrap_html(title, sections, meta=derive_header_meta(
        {_identity_key: header.target_dir}))
    return emit_html(
        full_html, output_path,
        log_message="[HTMLReport] 诊断报告已保存: %s (评分: %s/100)",
        log_args=(_score_text(facts.score),))
_BS_TYPE_SHOW_CAP = DISCLOSURE_ROWS_COMPACT
_BS_CONF_ROWS: tuple[tuple[str, str, str, str], ...] = (
    ("confirmed", "确认盲区", "danger", "#e53e3e"),
    ("confirmed_untested", "确认未覆盖", "warning", "#805ad5"),
    (FIELD_POTENTIAL_FP, "潜在误报", "warning", "#dd6b20"),
    ("external_api", "外部API", "info", "#3182ce"),
)
_BS_CONF_TILES = tuple((key, label, css) for key, label, css, _color in _BS_CONF_ROWS)
_BS_CONF_COLORS = {key: color for key, _label, _css, color in _BS_CONF_ROWS}
_BS_CONF_LABELS = {key: label for key, label, _css, _color in _BS_CONF_ROWS}
_BS_CONF_UNKNOWN_COLOR = "#6c757d"
_BS_LIVENESS_HEALTHY = 0.8
_BS_LIVENESS_WARNING = 0.4
def _liveness_css(lv: float) -> str:
    if lv >= _BS_LIVENESS_HEALTHY:
        return "success"
    if lv >= _BS_LIVENESS_WARNING:
        return "warning"
    return "danger"
def _bs_severity_stat_html(by_severity: dict) -> str:
    merged = _merge_counts(by_severity)
    parts = []
    for sev in _severity_keys(merged):
        cnt = merged.get(sev, 0.0)
        css = ("danger" if sev in ("critical", "high") and cnt > 0
               else ("warning" if sev == "medium" and cnt > 0 else "info"))
        parts.append(render_stat(_count_stat_text(cnt),
                                 sev.upper() or "UNKNOWN", css))
    return "".join(parts)
def _bs_confidence_stat_html(by_confidence: dict) -> str:
    merged = _merge_counts(by_confidence)
    known = {key for key, _label, _css in _BS_CONF_TILES}
    tiles = [*_BS_CONF_TILES,
             *((key, key.upper() or "UNKNOWN", "info")
               for key in sorted(merged) if key not in known)]
    parts = []
    for key, label, css in tiles:
        count = merged.get(key, 0.0)
        tile_css = css if (count > 0 or css == "info") else "success"
        parts.append(render_stat(_count_stat_text(count), label, tile_css))
    return "".join(parts)
@dataclass(frozen=True)
class _BlindspotFacts:
    summary: dict
    entries: list
    metrics: dict
    report_data: dict
    project_root: str
    timestamp: str
    total: float
    by_severity: dict
    by_confidence: dict
    effective_total: float | None
    @classmethod
    def of(cls, report_data: dict) -> _BlindspotFacts:
        report_data, s, entries, metrics, project_root, timestamp = (
            _normalize_blindspot_report(report_data))
        by_severity = _as_mapping(s.get("by_severity"))
        total_raw = s.get("total_blindspots")
        total = (to_finite_float(total_raw, math.nan)
                 if total_raw is not None else math.nan)
        derived_total = max(_sum_count_values(by_severity.values()),
                            float(len(entries)))
        if math.isnan(total):
            total = derived_total
        total = max(total, derived_total, 0.0)
        effective_total = s.get("effective_total")
        if effective_total is not None:
            effective_total = to_finite_float(effective_total, math.nan)
            effective_total = (None if math.isnan(effective_total)
                               else max(effective_total, 0.0))
        return cls(
            summary=s, entries=entries, metrics=metrics, report_data=report_data,
            project_root=project_root, timestamp=timestamp, total=total,
            by_severity=by_severity,
            by_confidence=_as_mapping(s.get("by_confidence")),
            effective_total=effective_total,
        )
def _bs_summary_html(facts: _BlindspotFacts) -> str:
    effective_total = facts.effective_total
    effective_stat = (
        render_stat(_count_stat_text(effective_total), "有效盲点(误报感知)",
                     "warning" if effective_total > 0 else "success")
        if effective_total is not None else "")
    return f"""
<div class="stat-grid">
  {render_stat(_count_stat_text(facts.total), "盲点总数",
                "danger" if facts.total > 0 else "success")}
  {_bs_severity_stat_html(facts.by_severity)}
  {effective_stat}
</div>
<div class="card">
  <h3>置信度分布</h3>
  <div class="stat-grid" style="grid-template-columns:repeat(auto-fit, minmax(140px, 1fr));">
    {_bs_confidence_stat_html(facts.by_confidence)}
  </div>
</div>
<div class="card">
  <h3>项目信息</h3>
  <table style="width:auto;">
    <tr><td style="color:#718096;">路径</td><td style="font-size:13px;">{_html.escape(facts.project_root)}</td></tr>
    <tr><td style="color:#718096;">时间</td><td>{_html.escape(facts.timestamp)}</td></tr>
  </table>
</div>
"""
def _bs_confidence_pie_html(by_confidence: dict) -> str:
    segments: list[str] = []
    legend: list[str] = []
    normalized = [
        (label, max(0.0, count))
        for label, count in _merge_counts(by_confidence).items()
    ]
    scale = max((count for _, count in normalized), default=0.0)
    scaled_total = (math.fsum(count / scale for _, count in normalized)
                    if scale else 0.0)
    cumulative = 0.0
    for conf_key, conf_count in normalized:
        pct = ((conf_count / scale) / scaled_total * 100
               if scaled_total else 0.0)
        color = _BS_CONF_COLORS.get(conf_key, _BS_CONF_UNKNOWN_COLOR)
        if conf_count:
            segments.append(f"{color} {cumulative}% {cumulative + pct}%")
            cumulative += pct
        label = _BS_CONF_LABELS.get(conf_key) or conf_key.upper() or "UNKNOWN"
        legend.append(
            f'<div style="margin:4px 0">'
            f'<span style="display:inline-block;width:12px;height:12px;background:{color};'
            f'border-radius:2px;margin-right:6px;vertical-align:middle"></span>'
            f'<span>{_html.escape(label)}: '
            f'{_count_stat_text(conf_count)} ({pct:.1f}%)</span></div>')
    if not segments:
        segments.append(f"{_BS_CONF_UNKNOWN_COLOR} 0% 100%")
    return (
        '<div style="display:flex;align-items:center;gap:24px;margin:12px 0">'
        '<div style="width:120px;height:120px;border-radius:50%;'
        'background:conic-gradient(' + ", ".join(segments) + ')"></div>'
        '<div>' + "".join(legend) + '</div></div>'
    )
def _bs_precision_stats_html(precision: dict) -> str:
    if not (isinstance(precision, dict) and precision):
        return ""
    return (
        '<div class="stat-grid" style="margin-top:8px">'
        + render_stat(_pct_text(precision.get('confirmed_pct')), "确认盲区占比", "danger")
        + render_stat(_pct_text(precision.get('confirmed_untested_pct')), "确认未覆盖占比", "warning")
        + render_stat(_pct_text(precision.get('potential_false_positive_pct')), "潜在误报占比", "warning")
        + render_stat(_pct_text(precision.get('external_api_pct')), "外部API占比", "info")
        + '</div>'
    )
def _bs_precision_section(s: dict, by_confidence: dict) -> ReportSection | None:
    if not by_confidence:
        return None
    return ReportSection(
        title="精度估算", section_id="precision", icon="🎯",
        html_content=(_bs_confidence_pie_html(by_confidence)
                      + _bs_precision_stats_html(s.get("precision_estimate", {}))),
    )
def _bs_severity_table(
    by_severity: dict, by_severity_adjusted: dict
) -> tuple[list[str], list[list[str]]]:
    adjusted = bool(by_severity_adjusted)
    raw_counts = _merge_counts(by_severity)
    adjusted_counts = _merge_counts(by_severity_adjusted) if adjusted else {}
    rows: list[list[str]] = []
    for sev_key in _severity_keys({**raw_counts, **adjusted_counts}):
        raw = to_int(raw_counts.get(sev_key, 0))
        adjusted_value = (to_int(adjusted_counts.get(sev_key, 0))
                          if adjusted else None)
        if not raw and not adjusted_value:
            continue
        row = [_html.escape(sev_key.upper()), str(raw)]
        if adjusted:
            row.append(str(adjusted_value))
        rows.append(row)
    header = ["严重度", "原始数量", "误报感知"] if adjusted else ["严重度", "数量"]
    return header, rows
def _bs_severity_section(
    by_severity: dict, by_severity_adjusted: dict
) -> ReportSection | None:
    if not by_severity and not by_severity_adjusted:
        return None
    header, rows = _bs_severity_table(by_severity, by_severity_adjusted)
    return ReportSection(title="严重度分布", section_id="severity", icon="📊",
                         html_content=render_table(header, rows, table_id="bs_sev"))
def _bs_count_section(
    by_count: dict, *, title: str, section_id: str, icon: str, label: str,
    table_id: str, initial_visible: int | None = None,
) -> ReportSection | None:
    if not by_count:
        return None
    rows = [[_html.escape(safe_text(key)), _count_stat_text(value)]
            for key, value in sorted(
                by_count.items(),
                key=lambda item: (-to_finite_float(item[1]),
                                  safe_text(item[0])))]
    return ReportSection(
        title=title, section_id=section_id, icon=icon,
        html_content=render_table([label, "数量"], rows, table_id=table_id,
                                   initial_visible=initial_visible),
    )
def _bs_liveness_stat(bf: dict) -> str:
    lv_f = _liveness_value(bf.get("liveness_rate"))
    if lv_f is None:
        return ""
    return render_stat(_liveness_text(lv_f), "链活性率", _liveness_css(lv_f))
def _bs_bizflow_section(report_data: dict) -> ReportSection | None:
    bf = report_data.get("business_flows") or {}
    if not isinstance(bf, dict) or not bf:
        return None
    bf_stats = render_stat(
        _count_stat_text(bf.get("entry_points")), "入口函数", "info")
    bf_stats += render_stat(
        _count_stat_text(bf.get("business_chains")), "业务链", "info")
    bf_stats += render_stat(
        f"{_count_stat_text(bf.get('simulated_chains'))}/"
        f"{_count_stat_text(bf.get('business_chains'))}", "已模拟", "info")
    bf_stats += render_stat(_count_stat_text(bf.get("blindspots_rescued")),
                             "救回盲区", "warning")
    bf_stats += render_stat(_count_stat_text(bf.get("blindspots_confirmed")),
                             "确认盲区", "danger")
    biz_html = f'''
<div class="stat-grid">
  {bf_stats}
  {_bs_liveness_stat(bf)}
</div>
'''
    return ReportSection(title="业务链活性验证", section_id="bizflow", icon="🔗",
                         html_content=biz_html)
def _extract_syntax_errors(metrics: dict) -> list[dict]:
    _call_graph = metrics.get("call_graph")
    raw = (
        metrics.get("syntax_errors")
        or (_call_graph.get("syntax_errors") if isinstance(_call_graph, dict) else None)
    )
    return _mapping_items(raw)
def _bs_syntax_row(e: dict) -> list:
    fp = e.get("filepath") or e.get("file") or ""
    msg = safe_text(e.get("message") or e.get("error") or "")
    return [
        f"<span class='path-cell'>{_html.escape(_fmt_location(fp, _payload_line(e.get('line'))))}</span>",
        _html.escape(msg),
    ]
def _bs_syntax_errors_section(metrics: dict) -> ReportSection | None:
    syntax_errors = _extract_syntax_errors(metrics)
    if not syntax_errors:
        return None
    se_rows = [_bs_syntax_row(e) for e in syntax_errors]
    return ReportSection(
        title=f"语法错误 ({len(syntax_errors)})", section_id="syntax", icon="❌",
        html_content=render_table(["位置", "错误"], se_rows,
                                   table_id="bs_syntax_err",
                                   initial_visible=_DEFAULT_TABLE_INITIAL_VISIBLE),
    )
def _bs_clustering_section(metrics: dict) -> ReportSection | None:
    clustering = _as_mapping(metrics.get("clustering"))
    if not clustering:
        return None
    _collapse = _as_mapping(clustering.get("pattern_collapse"))
    _prox = _as_mapping(clustering.get("proximity_clustering"))
    _struct = _as_mapping(clustering.get("structural_clustering"))
    cl_counts = (
        _finite_value(_collapse.get("collapsed_groups")),
        _finite_value(_collapse.get("affected_entries")),
        _finite_value(_prox.get("clusters")),
        _finite_value(_struct.get("clusters")),
    )
    if not any(count for count in cl_counts if count):
        return None
    cl_stats = render_stat(_count_stat_text(cl_counts[0]), "模式崩溃组", "warning")
    cl_stats += render_stat(_count_stat_text(cl_counts[1]), "受影响条目", "warning")
    cl_stats += render_stat(_count_stat_text(cl_counts[2]), "邻近聚类组", "info")
    cl_stats += render_stat(_count_stat_text(cl_counts[3]), "结构相似组", "info")
    cl_html = f'''
<div class="stat-grid">
  {cl_stats}
</div>
<p style="color:#718096;font-size:13px;margin:8px 0;">
  同类/邻近/结构相似的盲区条目已按聚类置信度系数降权降噪（三类聚类互补：
  模式崩溃按类型聚类、邻近聚类按行号距离、结构聚类按 AST 相似性）。
</p>
'''
    return ReportSection(title="聚类降噪", section_id="clustering", icon="🧩",
                         html_content=cl_html)
def _bs_entry_row(i: int, e: dict) -> list:
    sev = _severity_text(e.get("severity")).lower() or "info"
    return [
        str(i),
        render_badge(sev.upper(), _BS_SEV_BADGE.get(sev, "badge-muted")),
        _html.escape(safe_text(e.get("level") or "")),
        _html.escape(safe_text(e.get("blindspot_type") or "")),
        f"<span class='path-cell'>{_html.escape(_fmt_location(e.get('filepath', ''), _payload_line(e.get('line'))))}</span>",
        _html.escape(safe_text(e.get("message") or "")),
        _html.escape(safe_text(e.get("confidence") or "")),
    ]
def _bs_entries_section(entries) -> ReportSection | None:
    valid_entries = _mapping_items(entries)
    if not valid_entries:
        return None
    e_rows = [_bs_entry_row(i, e) for i, e in enumerate(valid_entries, 1)]
    return ReportSection(title=f"条目详情 ({len(valid_entries)} 条)", section_id="entries", icon="🔍",
                         html_content=render_table(
                             ["#", "严重度", "层级", "类型", "位置", "描述", "置信度"],
                             e_rows, table_id="bs_entries",
                             initial_visible=_DEFAULT_TABLE_INITIAL_VISIBLE))
def _normalize_blindspot_report(
        report_data: dict) -> tuple[dict, dict, list, dict, str, str]:
    report_data = _as_mapping(report_data)
    s = _as_mapping(report_data.get("summary"))
    entries = _mapping_items(report_data.get("entries"))
    metrics = _as_mapping(report_data.get("metrics"))
    return (report_data, s, entries, metrics,
            _as_text(report_data.get("project_root")),
            _as_text(report_data.get("timestamp")))
def _bs_distribution_sections(facts: _BlindspotFacts) -> list[ReportSection]:
    summary = facts.summary
    sections: list[ReportSection] = []
    extend_sections(sections, (
        _bs_precision_section(summary, facts.by_confidence),
        _bs_severity_section(
            facts.by_severity, _as_mapping(summary.get("by_severity_adjusted"))),
        _bs_count_section(_as_mapping(summary.get("by_level")), title="层级分布",
                          section_id="levels", icon="🏗", label="层级",
                          table_id="bs_level"),
        _bs_count_section(_as_mapping(summary.get("by_type")), title="类型分布",
                          section_id="types", icon="📋", label="类型",
                          table_id="bs_type", initial_visible=_BS_TYPE_SHOW_CAP),
    ))
    return sections
def render_blindspot_report_html(
        report_data: dict, output_path: str | None = _DEFAULT_OUTPUT_PATH) -> str:
    facts = _BlindspotFacts.of(report_data)
    sections: list[ReportSection] = [
        ReportSection(
            title="执行摘要", section_id="summary", icon="🔦",
            html_content=_bs_summary_html(facts),
        ),
    ]
    sections.extend(_bs_distribution_sections(facts))
    extend_sections(sections, (
        _bs_bizflow_section(facts.report_data),
        _bs_syntax_errors_section(facts.metrics),
        _bs_clustering_section(facts.metrics),
        _bs_entries_section(facts.entries),
    ))
    title = ("盲点报告 - "
             f"{_dir_name(facts.project_root) or 'Unknown'}")
    full_html = wrap_html(title, sections, meta=derive_header_meta(
        {"project_root": facts.project_root}))
    return emit_html(
        full_html, output_path,
        log_message="[HTMLReport] 盲点报告已保存: %s (盲点数: %d)",
        log_args=(facts.total,))
_GRADE_BADGE_CSS = {"A": "badge-success", "B": "badge-success", "C": "badge-warning",
                    "D": "badge-danger", "F": "badge-danger"}
def _grade_badge_css(grade, default: str = "badge-muted") -> str:
    return _GRADE_BADGE_CSS.get(safe_text(grade).strip().upper(), default)
def _health_grade(raw_grade, score: float | None) -> str:
    text = safe_text(raw_grade).strip().upper() if raw_grade is not None else ""
    if text:
        return text
    return grade_from_score(score) if score is not None else "-"
def _health_issues_section(issues: list) -> ReportSection:
    iss_rows = [[str(i+1), _html.escape(_issue_text(iss))]
                for i, iss in enumerate(issues)]
    iss_html = render_table(["#", "问题"], iss_rows,
                             table_id="health_issues",
                             initial_visible=_DEFAULT_TABLE_INITIAL_VISIBLE)
    return ReportSection(title=f"问题列表 ({len(issues)})", section_id="issues",
                         icon="🔍", html_content=iss_html)
def _dim_label(d) -> str:
    if isinstance(d, str):
        return d
    return safe_text(read_field(d, "label") or read_field(d, "name") or "")
_DIM_RECORD_FIELDS = ("label", "name", "grade", "score", "suggestions")
def _is_dim_record(d) -> bool:
    return isinstance(d, dict) or any(hasattr(d, f) for f in _DIM_RECORD_FIELDS)
def _health_dim_row(d) -> list[str]:
    if not _is_dim_record(d):
        return [_html.escape(_dim_label(d)), "-",
                render_badge("-", "badge-muted"), "-"]
    _label = _dim_label(d)
    _score_num = _finite_value(read_field(d, "score"))
    _grade = _health_grade(read_field(d, "grade"), _score_num)
    _sugg = read_field(d, "suggestions")
    _sugg_txt = ("; ".join(safe_text(x) for x in _sugg if x is not None)
                 if isinstance(_sugg, (list, tuple)) and _sugg else "")
    return [
        _html.escape(_label),
        "-" if _score_num is None else f"{_score_num:.0f}",
        render_badge(_grade, _grade_badge_css(_grade)),
        _html.escape(_sugg_txt),
    ]
def _health_dims_section(dimensions: list) -> ReportSection:
    dim_rows = [_health_dim_row(d) for d in dimensions]
    dim_html = render_table(["维度", "评分", "等级", "建议"], dim_rows, table_id="health_dims")
    return ReportSection(title="维度分析", section_id="dims", icon="📊", html_content=dim_html)
@dataclass(frozen=True)
class _HealthFacts:
    raw: dict
    score: float | None
    grade: str
    dimensions: list
    issues: list
    target_name: str
    report_type: str
    is_skill: bool
    @classmethod
    def of(cls, health_result: dict) -> _HealthFacts:
        health_result = _as_mapping(health_result)
        score = None
        for key in ("score", "overall_score", "health_score"):
            score = _finite_value(health_result.get(key))
            if score is not None:
                break
        target_name = _first_text(
            health_result, "skill_name", "skill", "project_name",
            "project", "name")
        target_dir = _first_text(health_result, *_IDENTITY_DIR_KEYS)
        if not target_name and target_dir:
            target_name = _dir_name(target_dir)
        return cls(
            raw=health_result,
            score=score,
            grade=_health_grade(
                health_result.get("grade") or health_result.get("overall_grade"),
                score),
            dimensions=[x for x in _sequence_items(health_result.get("dimensions")) if x is not None],
            issues=[x for x in _sequence_items(health_result.get("issues")) if x is not None],
            target_name=safe_text(target_name or "Unknown"),
            report_type=safe_text(health_result.get("type") or "健康评估"),
            is_skill=payload_is_skill(health_result),
        )
def _health_summary_html(facts: _HealthFacts) -> str:
    score_css = "info" if facts.score is None else score_band_css(facts.score)
    grade_css = _grade_badge_css(facts.grade).removeprefix("badge-")
    name_label = "技能" if facts.is_skill else "项目"
    return f"""
<div class="stat-grid">
  {render_stat(_score_text(facts.score), "综合评分", score_css)}
  {render_stat(_html.escape(safe_text(facts.grade)), "等级", grade_css)}
  {render_stat(len(facts.dimensions), "评估维度", "info")}
  {render_stat(len(facts.issues), "发现问题", "danger" if facts.issues else "success")}
</div>
<div class="card">
  <h3>评估信息</h3>
  <table style="width:auto;">
    <tr><td style="color:#718096;padding-right:16px;">{name_label}</td><td><strong>{_html.escape(safe_text(facts.target_name))}</strong></td></tr>
    <tr><td style="color:#718096;">类型</td><td>{_html.escape(safe_text(facts.report_type))}</td></tr>
  </table>
</div>
"""
def _health_sections(facts: _HealthFacts) -> list[ReportSection]:
    sections: list[ReportSection] = [
        ReportSection(title="执行摘要", section_id="summary", icon="🏥",
                      html_content=_health_summary_html(facts)),
    ]
    if facts.dimensions:
        sections.append(_health_dims_section(facts.dimensions))
    if facts.issues:
        sections.append(_health_issues_section(facts.issues))
    extend_sections(sections, (raw_dump_section(facts.raw),))
    return sections
def render_health_report_html(health_result: dict, output_path: str | None = _DEFAULT_OUTPUT_PATH) -> str:
    facts = _HealthFacts.of(health_result)
    sections = _health_sections(facts)
    title = f"健康评估报告 - {facts.target_name}"
    full_html = wrap_html(title, sections, meta=derive_header_meta(facts.raw))
    return emit_html(
        full_html, output_path,
        log_message="[HTMLReport] 健康评估报告已保存: %s (评分: %s)",
        log_args=(_score_text(facts.score),))
def _fallback_reason_section(error: str) -> ReportSection:
    return ReportSection(
        title="降级原因", section_id="reason", icon="⚠️",
        html_content=("<div class='card'><pre style='color:#e53e3e;"
                      "font-weight:600;white-space:pre-wrap;"
                      "word-break:break-all;overflow:auto;"
                      "max-height:480px;margin:0 0 8px;'>"
                      + _html.escape(safe_text(error))
                      + "</pre><p style='color:#718096;font-size:13px;'>"
                      "主渲染链异常，本页为极简兜底留痕——原始"
                      "动作已执行完毕，仅可视化降级。</p></div>"))
def _fallback_payload_section(result: dict) -> ReportSection:
    return ReportSection(
        title="原始载荷（完整转储 · 滚动查看）", section_id="payload",
        icon="🧾",
        html_content=("<div class='card'><pre style='overflow:auto;"
                      "max-height:480px;white-space:pre-wrap;"
                      "word-break:break-all;'>"
                      + _html.escape(dump_or_str(
                          result, TEXT_BLOCK_SAFE_CAP, indent=2))
                      + "</pre></div>"))
def render_fallback_html(report_type: str, result: dict, error: str) -> str:
    title = f"{safe_text(report_type)} 报告降级留痕（主渲染链失败兜底）"
    try:
        sections = [
            _fallback_reason_section(error),
            _fallback_payload_section(result),
        ]
        rep = HTMLReport(title=title, sections=sections,
                         raw_data={"report_type": report_type,
                                   "degraded": True})
        return rep.render()
    except Exception as _fb_err:
        logger.warning(
            "html_render_diag: 三层降级链兜底生效（纯拼接最小页）: %s",
            _fb_err)
        return ("<!DOCTYPE html><html><head><meta charset='utf-8'>"
                "<title>" + _html.escape(title) + "</title></head><body>"
                "<h1>" + _html.escape(title) + "</h1>"
                "<p><b>失败原因:</b></p><pre style='white-space:pre-wrap;word-break:break-all;'>"
                + _html.escape(safe_text(error)) + "</pre>"
                "<p><b>载荷摘要:</b></p><pre>"
                + _html.escape(safe_text(result)[:TEXT_BLOCK_SAFE_CAP])
                + "</pre></body></html>")
def _artifacts_idx_stats(valid_artifacts: list) -> str:
    cat_counts: dict[str, int] = {}
    for a in valid_artifacts:
        cat = text_or(a.get("category"), "其他")
        cat_counts[cat] = cat_counts.get(cat, 0) + 1
    return "".join(
        render_stat(cnt, cat, "info") for cat, cnt in sorted(cat_counts.items()))
def _valid_artifacts(artifacts) -> list[dict]:
    valid: list[dict] = []
    for entry in _mapping_items(artifacts):
        path = entry.get("path")
        if not (isinstance(path, str) and path):
            continue
        if not (isinstance(entry.get("filename"), str) and entry["filename"]):
            entry = {**entry, "filename": os.path.basename(path)}
        valid.append(entry)
    return valid
def artifacts_section(artifacts: list, report_dir: str) -> ReportSection:
    valid_artifacts = _valid_artifacts(artifacts)
    if not valid_artifacts:
        return ReportSection(
            title="HTML 可视化产物索引", section_id="artifacts", icon="🗂",
            html_content=empty_card("未发现管线 HTML 产物（各落点目录为空）"))
    rows = [artifact_row(a, report_dir) for a in valid_artifacts]
    idx_stats = _artifacts_idx_stats(valid_artifacts)
    return ReportSection(
        title=f"HTML 可视化产物索引（共 {len(valid_artifacts)} 份）",
        section_id="artifacts", icon="🗂",
        html_content=f"<div class='stat-grid'>{idx_stats}</div>"
                     + render_table(
                         ["类别", "文件", "大小", "生成时间", "完整路径"],
                         rows, table_id="artifact_table"))
_SCAN_TREE_MAX_DEPTH = 32
def _render_scan_tree_html(tree: dict, depth: int = 0) -> str:
    if depth > _SCAN_TREE_MAX_DEPTH:
        return ('&nbsp;&nbsp;&nbsp;… '
                f'<small>(超过 {_SCAN_TREE_MAX_DEPTH} 层，已截断)</small><br>')
    parts = []
    indent = "&nbsp;" * (depth * 3)
    entries = sorted(tree.items(), key=lambda kv: safe_text(kv[0]))
    for i, (name, node) in enumerate(entries):
        branch = "└─" if i == len(entries) - 1 else "├─"
        esc_name = _html.escape(safe_text(name))
        if isinstance(node, dict) and node.get("type") == "file":
            parts.append(f'{indent}{branch} <code>{esc_name}</code> '
                         f'<small>({_count_stat_text(node.get("lines"))}行)</small><br>')
        elif isinstance(node, dict):
            parts.append(f'{indent}{branch} <strong>{esc_name}/</strong><br>')
            parts.append(_render_scan_tree_html(node, depth + 1))
    return "".join(parts)
def _coerce_path_value_pair(item, value_key) -> tuple[str, float | None] | None:
    if isinstance(item, dict):
        path = safe_text(item.get("path") or "")
        raw = item.get(value_key)
    elif isinstance(item, (tuple, list)) and len(item) >= 2:
        path = safe_text(item[0] or "")
        raw = item[1]
    else:
        return None
    return (path, _finite_value(raw))
def _normalize_path_value_pairs(items, value_key) -> list[tuple[str, float | None]]:
    pairs = []
    for item in items:
        pair = _coerce_path_value_pair(item, value_key)
        if pair is not None:
            pairs.append(pair)
    return pairs
def _category_file_total(*groups: dict) -> float:
    totals = [_sum_count_values(group.values()) for group in groups]
    return max(totals, default=0.0)
def _category_percentage_basis(raw_total: float, *groups: dict) -> tuple[float, float]:
    counts = [[max(to_finite_float(value), 0.0)
               for value in group.values()] for group in groups]
    finite_raw = raw_total if math.isfinite(raw_total) else 0.0
    scale = max([1.0, finite_raw,
                 *(count for group_counts in counts for count in group_counts)])
    scaled_totals = [math.fsum(count / scale for count in group_counts)
                     for group_counts in counts]
    derived = max(scaled_totals, default=0.0)
    return max(finite_raw / scale, derived, 1.0), scale
def _scan_category_section(data: dict, total_files_f: float, *, title: str,
                           section_id: str, icon: str, table_id: str,
                           header: str, count_scale: float = 1.0) -> ReportSection:
    rows = []
    for key, value in sorted(
            data.items(),
            key=lambda x: (-to_finite_float(x[1]), safe_text(x[0]))):
        count = max(to_finite_float(value), 0.0)
        rows.append([_html.escape(safe_text(key)), _html.escape(str(to_int(count))),
                     f"{(count / count_scale) / total_files_f * 100:.1f}%"])
    return ReportSection(title=title, section_id=section_id, icon=icon,
                         html_content=render_table(
                             [header, "文件数", "占比"], rows, table_id=table_id))
def _scan_largest_section(largest_files: list) -> ReportSection:
    lf_rows = [[_html.escape(safe_text(p)), _count_stat_text(ln)]
               for p, ln in largest_files]
    return ReportSection(title=f"最大文件 ({len(largest_files)})", section_id="largest",
                         icon="📦",
                         html_content=render_table(
                             ["路径", "行数"], lf_rows, table_id="largest_table",
                             initial_visible=DISCLOSURE_ROWS_TINY))
def _scan_complex_section(most_complex: list) -> ReportSection:
    mc_rows = []
    for path, cc in most_complex:
        if cc is None:
            mc_rows.append([_html.escape(safe_text(path)),
                            render_badge("-", "badge-muted")])
            continue
        css = "badge-danger" if cc > 15 else ("badge-warning" if cc > 10 else "badge-success")
        mc_rows.append([_html.escape(safe_text(path)), render_badge(f"{cc:.1f}", css)])
    return ReportSection(title=f"最复杂文件 ({len(most_complex)})", section_id="complex",
                         icon="🧩",
                         html_content=render_table(
                             ["路径", "圈复杂度"], mc_rows, table_id="complex_table",
                             initial_visible=DISCLOSURE_ROWS_TINY))
def _scan_errors_section(errors: list[dict]) -> ReportSection | None:
    if not errors:
        return None
    rows = [[
        _html.escape(safe_text(error.get("phase") or "-")),
        _html.escape(safe_text(error.get("path") or "-")),
        _html.escape(safe_text(error.get("error") or error.get("message") or "-")),
    ] for error in errors]
    return ReportSection(
        title=f"扫描错误 ({len(errors)})", section_id="errors", icon="❌",
        html_content=render_table(
            ["阶段", "路径", "错误"], rows, table_id="scan_errors",
            initial_visible=_DEFAULT_TABLE_INITIAL_VISIBLE))
_SCAN_CATEGORY_SPECS = (
    ("by_language", "languages", "🗣", "lang_table", "语言", "按语言"),
    ("by_type", "types", "📄", "type_table", "类型", "按类型"),
)
@dataclass(frozen=True)
class _ScanFacts:
    scan_data: dict
    summary: dict
    by_language: dict
    by_type: dict
    largest_files: list[tuple[str, float]]
    most_complex: list[tuple[str, float]]
    warnings: list
    errors: list[dict]
    tree: dict
    project_root: str
    total_files: float | None
    total_files_f: float
    percentage_scale: float
    @classmethod
    def of(cls, scan_data: dict) -> _ScanFacts:
        scan_data = _as_mapping(scan_data)
        s = _as_mapping(scan_data.get("summary"))
        by_language = _as_mapping(scan_data.get("by_language"))
        by_type = _as_mapping(scan_data.get("by_type"))
        _derived_total = _category_file_total(by_language, by_type)
        _raw_total = to_finite_float(s.get("total_files"), math.nan)
        _percentage_total, _percentage_scale = _category_percentage_basis(
            _raw_total, by_language, by_type)
        total_files = (
            (_derived_total if (by_language or by_type) else None)
            if math.isnan(_raw_total)
            else max(_raw_total, _derived_total, 0.0))
        return cls(
            scan_data=scan_data,
            summary=s,
            by_language=by_language,
            by_type=by_type,
            largest_files=_normalize_path_value_pairs(
                _sequence_items(scan_data.get("largest_files")), "lines"),
            most_complex=_normalize_path_value_pairs(
                _sequence_items(scan_data.get("most_complex_files")), "complexity"),
            warnings=[w for w in _sequence_items(scan_data.get("warnings")) if w is not None],
            errors=_mapping_items(scan_data.get("errors")),
            tree=_as_mapping(scan_data.get("tree")),
            project_root=safe_text(scan_data.get("project_root") or ""),
            total_files=total_files,
            total_files_f=_percentage_total,
            percentage_scale=_percentage_scale,
        )
_SCAN_SUMMARY_TILES = (
    ("total_files", "文件数", _count_stat_text),
    ("total_lines", "总行数", _count_stat_text),
    ("total_code_lines", "代码行", _count_stat_text),
    ("total_comment_lines", "注释行", _count_stat_text),
    ("total_blank_lines", "空行", _count_stat_text),
    ("total_size_bytes", "总大小", _kb_text),
    ("total_functions", "函数数", _count_stat_text),
    ("total_classes", "类数", _count_stat_text),
)
def _scan_summary_tiles(facts: _ScanFacts) -> str:
    tiles = []
    for key, label, fmt in _SCAN_SUMMARY_TILES:
        value = (facts.total_files if key == "total_files"
                 else facts.summary.get(key))
        tiles.append(render_stat(fmt(value), label, "info"))
    return "".join(tiles)
def _scan_summary_section(facts: _ScanFacts) -> ReportSection:
    summary = facts.summary
    tiles = _scan_summary_tiles(facts)
    html_content = f"""
<div class="stat-grid">
  {tiles}
</div>
<div class="card">
  <h3>项目信息</h3>
  <table style="width:auto;">
    <tr><td style="color:#718096;padding-right:16px;">路径</td><td style="font-size:13px;">{_html.escape(facts.project_root)}</td></tr>
    <tr><td style="color:#718096;">耗时</td><td>{_ms_text(summary.get("scan_duration_ms"))}</td></tr>
  </table>
</div>
"""
    return ReportSection(title="执行摘要", section_id="summary", icon="📁",
                         html_content=html_content)
def _scan_sections(facts: _ScanFacts) -> list[ReportSection]:
    sections: list[ReportSection] = [_scan_summary_section(facts)]
    for key, section_id, icon, table_id, header, title in _SCAN_CATEGORY_SPECS:
        cat = getattr(facts, key)
        if cat:
            sections.append(_scan_category_section(
                cat, facts.total_files_f, title=title, section_id=section_id,
                icon=icon, table_id=table_id, header=header,
                count_scale=facts.percentage_scale))
    for data, section_fn in (
        (facts.largest_files, _scan_largest_section),
        (facts.most_complex, _scan_complex_section),
    ):
        if data:
            sections.append(section_fn(data))
    extend_sections(sections, (_scan_errors_section(facts.errors),))
    if facts.warnings:
        sections.append(list_card_section(
            facts.warnings, title="警告", section_id="warnings", icon="⚠️"))
    if facts.tree:
        sections.append(ReportSection(title="目录结构", section_id="tree", icon="🌲",
                                      html_content=_render_scan_tree_html(facts.tree)))
    extend_sections(sections, (raw_dump_section(facts.scan_data),))
    return sections
def render_file_scan_report_html(scan_data: dict, output_path: str | None = _DEFAULT_OUTPUT_PATH) -> str:
    facts = _ScanFacts.of(scan_data)
    sections = _scan_sections(facts)
    project_root = facts.project_root
    title = f"文件扫描报告 - {_dir_name(project_root) or 'Unknown'}"
    full_html = wrap_html(title, sections, meta=derive_header_meta(
        {"project_root": project_root}))
    return emit_html(full_html, output_path,
                      log_message="[HTMLReport] 文件扫描报告已保存: %s")
_SECURITY_SEV_ORDER = [sev.upper() for sev in _BS_SEV_ORDER]
_SECURITY_SEV_BADGE = {
    **{sev.upper(): badge for sev, badge, _color in _BS_SEVERITIES},
    "INFO": "badge-info",
}
@dataclass(frozen=True)
class _SeverityCounts:
    critical: int
    high: int
    medium: int
    low: int
    info: int
    @classmethod
    def of(cls, sev_groups: dict[str, list[dict]]) -> _SeverityCounts:
        return cls(*(len(sev_groups.get(sev) or ()) for sev in _SECURITY_SEV_ORDER))
    @property
    def total(self) -> int:
        return self.critical + self.high + self.medium + self.low + self.info
@dataclass(frozen=True)
class _SecurityFacts:
    target_name: str
    target_path: str
    risk_level: str
    passed: bool
    issues: list[dict]
    sev_groups: dict[str, list[dict]]
    counts: _SeverityCounts
    is_skill: bool
    @classmethod
    def of(cls, report: dict) -> _SecurityFacts:
        (target_name, target_path, risk_level, passed, issues,
         is_skill) = _normalize_security_report(report)
        sev_groups = _group_issue_dicts_by_severity(issues)
        if not risk_level:
            risk_level = next(
                (sev.lower() for sev in _SECURITY_SEV_ORDER[:4]
                 if sev_groups.get(sev)), "low")
        return cls(target_name, target_path, risk_level, passed, issues,
                   sev_groups, _SeverityCounts.of(sev_groups), is_skill)
def _security_stat_grid(facts: _SecurityFacts) -> str:
    counts, passed = facts.counts, facts.passed
    return f"""
<div class="stat-grid">
  {render_stat(counts.total, "问题总数", "danger" if counts.total > 0 else "success")}
  {render_stat(counts.critical, "严重", "danger" if counts.critical > 0 else "success")}
  {render_stat(counts.high, "高危", "danger" if counts.high > 0 else "success")}
  {render_stat(counts.medium, "中危", "warning" if counts.medium > 0 else "success")}
  {render_stat(counts.low, "低危", "info")}
  {render_stat(counts.info, "提示", "info")}
  {render_stat("PASS" if passed else "FAIL", "审计结果", "success" if passed else "danger")}
</div>
"""
def _security_risk_card(facts: _SecurityFacts) -> str:
    rl_label, rl_css = risk_level_label_css(facts.risk_level)
    verdict = ("安全审计通过" if facts.passed
               else f"发现 {facts.counts.total} 项安全问题需要处理")
    return f"""
<div class="card">
  <h3>风险等级</h3>
  <span class="health-badge {rl_css}">{_html.escape(rl_label)}</span>
  <span style="margin-left:16px;color:#718096;">{verdict}</span>
</div>
"""
def _target_info_card(facts: _SecurityFacts) -> str:
    info_title = "技能信息" if facts.is_skill else "项目信息"
    name_label = "技能名称" if facts.is_skill else "项目名称"
    return f"""
<div class="card">
  <h3>{info_title}</h3>
  <table style="width:auto;">
    <tr><td style="color:#718096;padding-right:16px;">{name_label}</td><td><strong>{_html.escape(facts.target_name)}</strong></td></tr>
    <tr><td style="color:#718096;">路径</td><td style="font-size:13px;word-break:break-all;">{_html.escape(facts.target_path)}</td></tr>
  </table>
</div>
"""
def _security_summary_html(facts: _SecurityFacts) -> str:
    return "".join((
        _security_stat_grid(facts),
        _security_risk_card(facts),
        _target_info_card(facts),
    ))
def _security_issues_section(sev_groups: dict[str, list[dict]]) -> ReportSection:
    all_rows = []
    for sev in _SECURITY_SEV_ORDER:
        for issue in sev_groups.get(sev) or ():
            all_rows.append([
                render_badge(sev, _SECURITY_SEV_BADGE.get(sev, "badge-muted")),
                _html.escape(safe_text(issue.get("category") or "")),
                _html.escape(safe_text(issue.get("description") or "")),
                f"<span class='path-cell'>{_html.escape(safe_text(issue.get('location') or ''))}</span>",
                _html.escape(safe_text(issue.get("recommendation") or "")),
            ])
    if all_rows:
        issues_html = render_table(
            ["严重度", "类别", "描述", "位置", "建议"],
            all_rows,
            table_id="security_issues_table",
        )
    else:
        issues_html = '<div class="card"><p style="color:#38a169;">无安全问题</p></div>'
    return ReportSection(
        title="问题详情", section_id="issues", icon="🔍",
        html_content=issues_html,
    )
def _security_category_section(issues: list[dict]) -> ReportSection | None:
    if not issues:
        return None
    cat_counts: dict[str, int] = {}
    for issue in issues:
        cat = safe_text(issue.get("category") or "unknown")
        cat_counts[cat] = cat_counts.get(cat, 0) + 1
    cat_rows = [[_html.escape(c), _html.escape(str(n))]
                for c, n in sorted(cat_counts.items(),
                                   key=lambda x: (-x[1], x[0]))]
    cat_html = render_table(["类别", "数量"], cat_rows, table_id="category_table")
    return ReportSection(
        title="按类别分布", section_id="categories", icon="📊",
        html_content=cat_html,
    )
def _normalize_security_report(
        report: dict) -> tuple[str, str, str, bool, list[dict], bool]:
    report = _as_mapping(report)
    target_name = _first_text(
        report, "skill_name", "name", "project_name", "project")
    target_path = _first_text(report, *_IDENTITY_DIR_KEYS)
    issues = _issue_entries(report.get("issues"))
    raw_passed = report.get("passed")
    passed = (not issues if raw_passed is None
              else normalize_passed(raw_passed))
    return (
        target_name or _dir_name(target_path) or "Unknown",
        target_path,
        _norm_key(report.get("risk_level") or ""),
        passed,
        issues,
        payload_is_skill(report),
    )
def _group_issue_dicts_by_severity(issues: list[dict]) -> dict[str, list[dict]]:
    sev_groups: dict[str, list[dict]] = {s: [] for s in _SECURITY_SEV_ORDER}
    for issue in issues:
        text = _severity_text(issue.get("severity") or "LOW").upper()
        if text in sev_groups:
            sev = text
        else:
            rank = SEVERITY_RANK.get(text)
            if rank is None:
                rank = SEVERITY_RANK.get(diag_severity_to_p(text))
            sev = (_SECURITY_SEV_ORDER[rank]
                   if rank is not None and 0 <= rank < len(_SECURITY_SEV_ORDER)
                   else "LOW")
        sev_groups[sev].append(issue)
    return sev_groups
def render_security_report_html(
        report: dict, output_path: str | None = _DEFAULT_OUTPUT_PATH) -> str:
    facts = _SecurityFacts.of(report)
    sections: list[ReportSection] = [
        ReportSection(title="执行摘要", section_id="summary", icon="🛡️",
                      html_content=_security_summary_html(facts)),
        _security_issues_section(facts.sev_groups),
    ]
    extend_sections(sections, (_security_category_section(facts.issues),))
    title = f"安全审计报告 - {facts.target_name}"
    _identity_key = "skill_dir" if facts.is_skill else "project_root"
    full_html = wrap_html(title, sections, meta=derive_header_meta(
        {_identity_key: facts.target_path}))
    return emit_html(
        full_html, output_path,
        log_message="[HTMLReport] 安全审计报告已保存: %s (风险: %s, 问题: %d)",
        log_args=(facts.risk_level, facts.counts.total))

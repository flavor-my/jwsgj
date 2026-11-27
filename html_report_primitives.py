from __future__ import annotations

import hashlib
import html as _html
import json
import logging
import math
import os
import re
import time
import uuid
from dataclasses import dataclass, field
from typing import Any
from urllib.parse import quote

from jwsgj.diag_types_vocab import (
    FINDING_KEY_ALIASES,
    FMT_DATETIME,
)
from jwsgj.html_report_stage_doc import CSS, JS, artifact_root_hint
from jwsgj.log_config import log_swallowed

logger = logging.getLogger(__name__)
__all__ = [
    'DISCLOSURE_ROWS_COMPACT',
    'DISCLOSURE_ROWS_MEDIUM',
    'DISCLOSURE_ROWS_STANDARD',
    'DISCLOSURE_ROWS_TINY',
    'DISCLOSURE_ROWS_WIDE',
    'DISCLOSURE_TEXT_CAP',
    'TEXT_BLOCK_SAFE_CAP',
    'HTMLReport',
    'ReportSection',
    'alert_tone',
    'apply_target_identity',
    'artifact_row',
    'derive_header_meta',
    'disclosure_value',
    'dump_or_str',
    'emit_html',
    'empty_card',
    'esc_or',
    'extend_sections',
    'extract_finding_coords',
    'full_value',
    'is_nonfinite_float',
    'kv_table',
    'kv_table_preescaped',
    'list_card_section',
    'normalize_line_value',
    'payload_is_skill',
    'raw_dump_section',
    'read_field',
    'render_badge',
    'render_code_block',
    'render_ctx_cell',
    'render_health_badge',
    'render_json_interactive',
    'render_json_summary',
    'render_list_progressive',
    'render_progress_bar',
    'render_report',
    'render_show_more_button',
    'render_stat',
    'render_structured_details',
    'render_table',
    'risk_level_label_css',
    'safe_filename',
    'safe_text',
    'scalar_detail',
    'score_band_css',
    'status_badge_css',
    'text_or',
    'to_bool',
    'to_finite_float',
    'to_float',
    'to_int',
    'wrap_html',
    'write_html_file',
]
DISCLOSURE_ROWS_WIDE = 100
DISCLOSURE_ROWS_STANDARD = 50
DISCLOSURE_ROWS_MEDIUM = 30
DISCLOSURE_ROWS_COMPACT = 20
DISCLOSURE_ROWS_TINY = 10
@dataclass
class ReportSection:
    title: str
    html_content: str
    section_id: str = ""
    icon: str = ""
_TARGET_IDENTITY_KEYS: tuple[tuple[str, str], ...] = (
    ("skill_dir", "目标技能"),
    ("skill_name", "目标技能"),
    ("project_root", "目标项目"),
    ("project_name", "目标项目"),
    ("target_dir", "目标路径"),
    ("target", "目标路径"),
)
def derive_header_meta(raw_data) -> list[tuple[str, str]]:
    if not isinstance(raw_data, dict):
        return []
    for key, label in _TARGET_IDENTITY_KEYS:
        value = raw_data.get(key)
        if isinstance(value, str) and value.strip():
            return [(label, value.strip())]
    return []
def _meta_row(item) -> str:
    if not (isinstance(item, (list, tuple)) and len(item) == 2):
        return ""
    _k, _v = item
    _v_html = _html.escape(safe_text(_v))
    if not _v_html.strip():
        return ""
    return (f'<div class="meta-row">'
            f'<strong>{_html.escape(safe_text(_k))}</strong>: {_v_html}</div>')
def _render_header_meta(meta) -> str:
    if not isinstance(meta, (list, tuple)) or not meta:
        return ""
    return "".join(row for row in map(_meta_row, meta) if row)
def _render_section_parts(sections: list[ReportSection]) -> tuple[str, str]:
    tabs: list[str] = []
    contents: list[str] = []
    used_ids: set[str] = set()
    for i, sec in enumerate(sections):
        base_sid = sec.section_id or f"section_{i}"
        sid = base_sid
        suffix = 2
        while sid in used_ids:
            sid = f"{base_sid}_{suffix}"
            suffix += 1
        used_ids.add(sid)
        active = "active" if i == 0 else ""
        icon = (f'<span class="tab-icon">'
                f'{_html.escape(safe_text(sec.icon), quote=True)} </span>'
                if sec.icon else "")
        _sid_esc = _html.escape(safe_text(sid), quote=True)
        _sid_js = _html.escape(json.dumps(safe_text(sid), ensure_ascii=False), quote=True)
        tabs.append(f'<button class="tab {active}" data-tab="{_sid_esc}" '
                    f'onclick="showTab({_sid_js})">{icon}{_html.escape(safe_text(sec.title))}</button>\n')
        contents.append(f'<div id="{_sid_esc}" class="tab-content {active}">\n'
                        f'{sec.html_content or ""}\n</div>\n')
    return "".join(tabs), "".join(contents)
_DEFAULT_REPORT_FOOTER = "本报告由自动分析工具生成"
def _footer_html(footer: str) -> str:
    text = safe_text(footer or "").strip()
    return f'<div class="footer">{_html.escape(text)}</div>' if text else ''
def wrap_html(title: str, sections: list[ReportSection],
               meta: list[tuple[str, str]] | None = None,
               *, footer: str = _DEFAULT_REPORT_FOOTER,
               lang: str = "zh-CN") -> str:
    tabs_html, contents_html = _render_section_parts(sections)
    _lang = _html.escape(safe_text(lang).strip() or "zh-CN", quote=True)
    return f"""<!DOCTYPE html>
<html lang="{_lang}">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>{_html.escape(safe_text(title))}</title>
<style>{CSS}</style>
</head>
<body>
<button class="theme-toggle" onclick="toggleTheme()">🌙 深色</button>
<button class="fullscreen-toggle" onclick="toggleFullscreen()">⛶</button>
<button class="back-top" onclick="scrollToTop()" title="返回顶部">↑</button>
<div class="container">
<div class="header">
<h1>{_html.escape(safe_text(title))}</h1>
<div class="meta">生成时间: {time.strftime(FMT_DATETIME)}{_render_header_meta(meta)}</div>
</div>
<div class="tabs">{tabs_html}</div>
{contents_html}
{_footer_html(footer)}
</div>
<script>{JS}</script>
</body>
</html>"""
_DEFAULT_FLOAT = 0.0
def to_float(value, default: float = _DEFAULT_FLOAT) -> float:
    if value is None:
        return default
    if isinstance(value, bool):
        logger.debug("to_float 布尔非数值，按默认值降级")
        return default
    try:
        return float(value)
    except (ValueError, OverflowError):
        logger.debug("to_float 契约内脏值降级: value_type=%s",
                     type(value).__name__)
        return default
    except TypeError as _e:
        log_swallowed(__name__, _e, context='to_float:TypeError')
        return default
def to_finite_float(value, default: float = _DEFAULT_FLOAT) -> float:
    num = to_float(value, math.nan)
    if not math.isfinite(num):
        return default
    return num
def _int_default(default) -> int:
    if isinstance(default, int):
        return int(default)
    return int(to_finite_float(default, 0.0))
def to_int(value, default: int = 0) -> int:
    if isinstance(value, bool):
        logger.debug("to_int 布尔非计数，按默认值降级")
        return _int_default(default)
    if isinstance(value, int):
        return int(value)
    if isinstance(value, str) and re.fullmatch(r"[+-]?\d+", value.strip()):
        try:
            return int(value)
        except ValueError as _e:
            log_swallowed(__name__, _e, context='to_int:ValueError')
            return _int_default(default)
    num = to_finite_float(value, math.nan)
    if math.isfinite(num):
        return int(num)
    return _int_default(default)
_BOOL_FALSE_TEXTS = frozenset({"false", "0", "no", "off", "n", "none", "null", ""})
_BOOL_TRUE_TEXTS = frozenset({"true", "1", "yes", "on", "y"})
def to_bool(value, default: bool = False) -> bool:
    if value is None:
        return default
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        if isinstance(value, float) and not math.isfinite(value):
            return default
        return value != 0
    text = safe_text(value).strip().lower()
    if text in _BOOL_TRUE_TEXTS:
        return True
    if text in _BOOL_FALSE_TEXTS:
        return False
    return default
def text_or(value, default: str = "") -> str:
    return default if not value else safe_text(value)
def esc_or(value, default: str = "") -> str:
    return _html.escape(text_or(value, default))
def read_field(obj, name: str, default=None):
    if isinstance(obj, dict):
        return obj.get(name, default)
    return getattr(obj, name, default)
def write_html_file(filepath: str, content: str) -> None:
    os.makedirs(os.path.dirname(filepath) or ".", exist_ok=True)
    with open(filepath, "w", encoding="utf-8", errors="backslashreplace") as f:
        f.write(content)
_SAFE_COMPONENT_MAX_LEN = 60
_SAFE_ID_DIGEST_LEN = 8
def safe_filename(name) -> str:
    cleaned = re.sub(r"[^\w.-]+", "_", safe_text(name))
    cleaned = re.sub(r"\.\.+", "_", cleaned)
    return cleaned[:_SAFE_COMPONENT_MAX_LEN].rstrip(". ") or "item"
def safe_text(v) -> str:
    try:
        return str(v)
    except RecursionError as _e:
        log_swallowed(__name__, _e, context='safe_text:RecursionError')
        return f"<{type(v).__name__} 嵌套过深，无法序列化展示>"
    except Exception as _e:
        log_swallowed(__name__, _e, context='safe_text:Exc')
        return f"<{type(v).__name__} 无法转为文本>"
_JSON_CONTAINER_TYPES = (dict, list, tuple)
_CONTAINER_HINT_TYPES = (*_JSON_CONTAINER_TYPES, set, frozenset)
def _json_or_str(v, *, indent: int | None = None) -> str:
    try:
        return json.dumps(v, ensure_ascii=False, indent=indent, default=safe_text)
    except Exception as _e:
        log_swallowed(__name__, _e, context='_json_or_str:Exc')
        return safe_text(v)
def full_value(v) -> str:
    if isinstance(v, _JSON_CONTAINER_TYPES):
        return _json_or_str(v)
    return safe_text(v)
DISCLOSURE_TEXT_CAP = 200
def is_nonfinite_float(value) -> bool:
    return isinstance(value, float) and not math.isfinite(value)
def scalar_detail(v) -> str:
    if is_nonfinite_float(v):
        return "N/A"
    return disclosure_value(v)
def disclosure_value(v, n: int = DISCLOSURE_TEXT_CAP) -> str:
    s = full_value(v)
    if len(s) <= n:
        return _html.escape(s)
    return (f"{_html.escape(s[:n])}… "
            f"<span class='val-more'>（共 {len(s)} 字符，"
            "完整内容见 JSON 落盘文件）</span>")
_JSON_TREE_MAX_DEPTH = 6
_JSON_TREE_MAX_NODES = 800
_JSON_SCALAR_TEXT_CAP = 300
_JSON_REMAINDER_TEXT_CAP = 512
_JSON_INLINE_BUDGET = 24 * 1024
_JSON_TREE_HTML_CAP = 48 * 1024
_JSON_LEN_UNBOUNDED = 1 << 62
def _json_compact_len(v) -> int:
    text = dump_or_str(v, _JSON_LEN_UNBOUNDED)
    return len(text.encode("utf-8", "surrogatepass"))
def _json_kind(v) -> str:
    if isinstance(v, dict):
        return "对象"
    if isinstance(v, _JSON_CONTAINER_TYPES):
        return "数组"
    if isinstance(v, bool):
        return "布尔"
    if v is None:
        return "空值"
    if isinstance(v, (int, float)):
        return "数值"
    return "文本"
def _json_node_count(v) -> str:
    if isinstance(v, _JSON_CONTAINER_TYPES):
        return str(len(v))
    return "-"
def _json_size_text(size: int) -> str:
    if size >= 1024 * 1024:
        return f"{size / (1024 * 1024):.2f} MB"
    if size >= 1024:
        return f"{size / 1024:.1f} KB"
    return f"{size} B"
_JSON_SUMMARY_MAX_ROWS = DISCLOSURE_ROWS_COMPACT
_STRUCTURED_LIST_ITEM_MAX = 160
def _json_summary_table(
        data, *, total_size: int = 0,
        max_rows: int = _JSON_SUMMARY_MAX_ROWS,
        top_level: bool = False,
        more_text: str = "… 其余 {rest} 项（完整数据见 JSON 落盘文件）") -> str:
    if not isinstance(data, _JSON_CONTAINER_TYPES):
        return ""
    items, is_dict = _json_items(data)
    if not items:
        return ""
    rows = []
    for key, value in items[:max_rows]:
        rows.append(
            "<tr>"
            f"<td style='font-family:monospace'>{_html.escape(safe_text(key))}</td>"
            f"<td>{_json_kind(value)}</td>"
            f"<td style='text-align:right'>{_json_node_count(value)}</td>"
            "</tr>")
    rest = len(items) - len(rows)
    more = (f"<tr><td colspan='3' style='color:#718096'>"
            f"{more_text.format(rest=rest)}</td></tr>"
            if rest > 0 else "")
    head = ("<tr><th>键</th><th>类型</th><th>条目数</th></tr>"
            if is_dict else
            "<tr><th>下标</th><th>类型</th><th>条目数</th></tr>")
    _total = ""
    if total_size > 0:
        _caption = f"整体规模：{_json_size_text(total_size)}"
        if top_level:
            _caption += f" · 顶层 {len(items)} 项"
        _total = ("<p style='color:#718096;font-size:13px;margin:0 0 8px'>"
                  f"{_caption}</p>")
    return ("<div class='json-summary-wrap'>" + _total
            + "<table class='json-summary' style='margin-bottom:12px'>"
            + head + "".join(rows) + more + "</table></div>")
def _json_hint_html(source_hint: str) -> str:
    hint = text_or(source_hint).strip()
    if not hint:
        return ""
    return (f"<p class='json-hint' style='color:#718096;font-size:13px;"
            f"margin:8px 0 0'>完整数据见 JSON 落盘文件："
            f"<code>{_html.escape(hint)}</code></p>")
def _render_json_scalar(v) -> str:
    if v is None:
        return "<span class='json-null'>null</span>"
    if isinstance(v, bool):
        return f"<span class='json-bool'>{'true' if v else 'false'}</span>"
    if isinstance(v, (int, float)):
        return (f"<span class='json-number'>"
                f"{_html.escape(_json_or_str(v))}</span>")
    text = safe_text(v)
    if len(text) > _JSON_SCALAR_TEXT_CAP:
        head = _html.escape(json.dumps(text[:_JSON_SCALAR_TEXT_CAP],
                                       ensure_ascii=False))
        return (f"<span class='json-string'>{head}…</span>"
                f"<span class='json-tree-fallback'>（共 {len(text)} 字符）</span>")
    return (f"<span class='json-string'>"
            f"{_html.escape(json.dumps(text, ensure_ascii=False))}</span>")
def _json_items(node) -> tuple[list, bool]:
    if isinstance(node, dict):
        return list(node.items()), True
    return list(enumerate(node)), False
def _json_key_html(k, is_dict: bool) -> str:
    if is_dict:
        return (f"<span class='json-key'>"
                f"{_html.escape(json.dumps(safe_text(k), ensure_ascii=False))}"
                f"</span>: ")
    return f"<span class='json-index'>[{k}]</span> "
def _render_json_remainder(items, idx: int, is_dict: bool) -> str:
    rest = _json_remainder_rest(items, idx, is_dict)
    unit = "键" if is_dict else "项"
    count = len(items) - idx
    _text = dump_or_str(rest, _JSON_REMAINDER_TEXT_CAP, indent=2)
    return (f"<div class='json-row json-truncated'>"
            f"<span class='json-tree-fallback'>… 其余 {count} {unit}"
            f"（超出页内渲染预算，仅展示前 "
            f"{_JSON_REMAINDER_TEXT_CAP} 字符；完整数据见 JSON 落盘文件）: "
            f"{_html.escape(_text)}</span></div>")
def _json_remainder_rest(items, idx: int, is_dict: bool):
    if is_dict:
        return dict(items[idx:])
    return [val for _k, val in items[idx:]]
def _render_json_children(items, is_dict: bool, depth: int,
                          budget: list[int]) -> str:
    parts: list[str] = []
    for idx, (k, val) in enumerate(items):
        if budget[0] <= 0:
            parts.append(_render_json_remainder(items, idx, is_dict))
            break
        parts.append(
            f"<div class='json-row'>{_json_key_html(k, is_dict)}"
            f"{_render_json_tree(val, depth + 1, budget)}</div>")
    return "".join(parts)
def _render_json_tree(node, _depth: int = 0,
                      _budget: list[int] | None = None) -> str:
    if _budget is None:
        _budget = [_JSON_TREE_MAX_NODES]
    if not isinstance(node, _JSON_CONTAINER_TYPES):
        _budget[0] -= 1
        return _render_json_scalar(node)
    items, is_dict = _json_items(node)
    ob, cb, unit = ("{", "}", "键") if is_dict else ("[", "]", "项")
    over_budget = _depth >= _JSON_TREE_MAX_DEPTH or _budget[0] <= 0
    _budget[0] -= 1
    if not items:
        return f"<span class='json-bracket'>{ob}{cb}</span>"
    if over_budget:
        return (f"<span class='json-tree-fallback'>{ob} … {len(items)} {unit}"
                f"（已折叠，完整数据见 JSON 落盘文件） {cb}</span>")
    return (
        "<div class='json-node'>"
        "<span class='json-toggle' onclick=\"toggleJsonNode(this)\">▾</span>"
        f"<span class='json-bracket'>{ob}</span>"
        f"<span class='json-ellipsis'> … {len(items)} {unit} … </span>"
        f"<span class='json-bracket json-close-inline'>{cb}</span>"
        "<div class='json-children'>"
        f"{_render_json_children(items, is_dict, _depth, _budget)}"
        "</div>"
        f"<span class='json-bracket json-close'>{cb}</span>"
        "</div>"
    )
def _json_viewer_toolbar(viewer_id: str, json_len: int,
                         max_height: int) -> str:
    return f"""<div class="json-toolbar">
  <button type="button" class="json-btn" onclick="expandAllJson('{viewer_id}')">展开全部</button>
  <button type="button" class="json-btn" onclick="collapseAllJson('{viewer_id}')">折叠全部</button>
  <input type="text" placeholder="搜索…" onkeyup="searchJson('{viewer_id}', this.value)"
         style="padding:4px 8px;border:1px solid var(--border);border-radius:4px;font-size:12px;">
  <span class="json-search-count"></span>
  <span class="json-meta">{json_len} 字符 · 单份树形渲染 · 完整数据见同名 JSON</span>
</div>
<div class="json-content" style="max-height:{max_height}px;overflow:auto;">"""
def _normalized_payload(v):
    if isinstance(v, str):
        try:
            v = json.loads(v)
        except (ValueError, TypeError, RecursionError) as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='_coerce_json_payload:Exc+')
    if (not isinstance(v, (*_JSON_CONTAINER_TYPES, str, int, float, bool))
            and v is not None):
        return safe_text(v)
    return v
def _coerce_json_payload(v) -> tuple[Any, str]:
    payload = _normalized_payload(v)
    return payload, _json_or_str(payload, indent=2)
_JSON_VIEWER_DEFAULT_HEIGHT = 500
_CODE_BLOCK_DEFAULT_HEIGHT = 480
def _height_px(value, default: int) -> int:
    if isinstance(value, bool):
        return default
    if isinstance(value, (int, float)):
        num = to_finite_float(value, math.nan)
        if math.isfinite(num) and num >= 0:
            return int(num)
    return default
def render_json_interactive(
        v, *, max_height: int = _JSON_VIEWER_DEFAULT_HEIGHT,
        source_hint: str = "") -> str:
    viewer_id = f"json_viewer_{uuid.uuid4().hex}"
    _h = _height_px(max_height, _JSON_VIEWER_DEFAULT_HEIGHT)
    payload, json_str = _coerce_json_payload(v)
    if len(json_str) > _JSON_INLINE_BUDGET:
        return render_json_summary(payload, source_hint=source_hint)
    tree = _render_json_tree(payload)
    if len(tree) > _JSON_TREE_HTML_CAP:
        return render_json_summary(payload, source_hint=source_hint)
    return (f'<div class="json-viewer" id="{viewer_id}">'
            + _json_viewer_toolbar(viewer_id, len(json_str), _h)
            + f'<div class="json-tree">{tree}</div></div>'
            + _json_hint_html(source_hint)
            + '</div>')
def render_json_summary(v, *, source_hint: str = "") -> str:
    payload = _normalized_payload(v)
    summary = _json_summary_table(payload, total_size=_json_compact_len(payload))
    if not summary:
        summary = empty_card("无结构化摘要（标量数据见落盘文件）")
    return ("<div class='json-viewer'>" + summary
            + _json_hint_html(source_hint) + "</div>")
def _json_dumps_prefix(obj, limit: int, *, indent: int | None = None) -> str:
    parts: list[str] = []
    n = 0
    for chunk in json.JSONEncoder(ensure_ascii=False, indent=indent,
                                  default=safe_text).iterencode(obj):
        parts.append(chunk)
        n += len(chunk)
        if n >= limit:
            break
    return "".join(parts)[:limit]
def dump_or_str(obj, limit: int, *, indent: int | None = None) -> str:
    try:
        return _json_dumps_prefix(obj, limit, indent=indent)
    except Exception as _e:
        log_swallowed(__name__, _e, context='dump_or_str:Exc')
        return safe_text(obj)[:limit]
_RAW_POINTER_KEY_CAP = 8
def raw_dump_section(raw_data, *, source_hint: str = "") -> ReportSection | None:
    if not raw_data:
        return None
    _size = _json_compact_len(raw_data)
    _hint = source_hint or artifact_root_hint()
    return ReportSection(
        title=f"原始数据落盘指针（{_json_size_text(_size)}）",
        section_id="raw_data_dump", icon="🧾",
        html_content=(
            "<div class='card'><p style='color:#4a5568'>"
            "可读结论已在上方各章节呈现；完整原始数据"
            f"（{_json_size_text(_size)}）不在页内重复嵌入，"
            "以 JSON 落盘文件为准（数据零丢失）。</p>"
            + _json_summary_table(
                raw_data, total_size=_size,
                max_rows=_RAW_POINTER_KEY_CAP, top_level=True,
                more_text="… 其余 {rest} 项见 JSON 落盘文件")
            + _json_hint_html(_hint)
            + "</div>"))
_SCORE_BAND_WARNING = 60
_SCORE_BAND_SUCCESS = 80
_RISK_LEVEL_STYLES = {
    "critical": ("CRITICAL", "health-critical"), "high": ("HIGH", "health-critical"),
    "medium": ("MEDIUM", "health-warning"), "low": ("LOW", "health-clean"),
}
_HEALTH_BADGE_CSS = {"clean": "health-clean", "healthy": "health-healthy",
                     "warning": "health-warning", "critical": "health-critical"}
def score_band_css(score) -> str:
    num = to_finite_float(score, math.nan)
    if num >= _SCORE_BAND_SUCCESS:
        return "success"
    if num >= _SCORE_BAND_WARNING:
        return "warning"
    return "danger"
def risk_level_label_css(risk_level) -> tuple[str, str]:
    key = safe_text(risk_level).strip().lower()
    label, css = _RISK_LEVEL_STYLES.get(
        key, (key.upper(), "health-warning"))
    return label, css
_STATUS_BADGE_CSS = {
    "ok": "success", "completed": "success", "pass": "success",
    "planned": "success", "approved": "success", "applied": "success",
    "approved_fixed": "success", "ai_fixed": "success",
    "warn": "warning", "needs_fixed_source": "warning",
    "fail": "danger", "failed": "danger", "error": "danger",
    "timeout": "danger", "blocked": "danger", "early_stopped": "danger",
    "skipped": "muted",
    "missing": "danger", "degraded": "warning",
}
def status_badge_css(status, *, default: str = "info") -> str:
    return _STATUS_BADGE_CSS.get(safe_text(status).strip().lower(), default)
def alert_tone(value, alert_cls: str) -> str:
    return alert_cls if value else "success"
TEXT_BLOCK_SAFE_CAP = 200_000
def _hide_start(total: int, initial_visible, need_id: bool) -> int | None:
    if (need_id and isinstance(initial_visible, int)
            and not isinstance(initial_visible, bool)
            and 0 <= initial_visible < total):
        return initial_visible
    return None
def _row_hidden_cls(idx: int, hide_from: int | None) -> str:
    return ' class="row-hidden"' if hide_from is not None and idx >= hide_from else ''
def render_show_more_button(target_id: str, rest: int, total: int) -> str:
    _tid = _safe_id(target_id)
    return (f'<button type="button" class="show-more-btn" '
            f'onclick="showAllHidden(\'{_tid}\', this)">'
            f'▼ 显示剩余 {rest} 条（共 {total} 条）</button>')
def _maybe_show_more(html: str, tid: str, hide_from: int | None,
                     total: int) -> str:
    if hide_from is None:
        return html
    return html + render_show_more_button(tid, total - hide_from, total)
def _safe_id(raw, fallback: str = '') -> str:
    is_text = isinstance(raw, str)
    if not fallback and (raw is None or (is_text and not raw)):
        return fallback
    text = safe_text(raw)
    cleaned = safe_filename(text)
    if is_text and cleaned == text and len(text) <= _SAFE_COMPONENT_MAX_LEN:
        return cleaned
    identity = text if is_text else f"{type(raw).__qualname__}:{text}"
    digest = hashlib.sha256(
        identity.encode("utf-8", "surrogatepass")).hexdigest()[:_SAFE_ID_DIGEST_LEN]
    base_len = _SAFE_COMPONENT_MAX_LEN - _SAFE_ID_DIGEST_LEN - 1
    base = cleaned[:base_len].rstrip(". ") or "item"
    return f"{base}_{digest}"
def _id_attr(tid: str) -> str:
    return f' id="{tid}"' if tid else ''
def empty_card(text: str) -> str:
    return ('<div class="card"><p style="color:#718096;">'
            f'{_html.escape(safe_text(text))}</p></div>')
def render_stat(value, label: str, css_class: str = '') -> str:
    _css = _html.escape(safe_text(css_class), quote=True)
    _value = value if isinstance(value, str) else _html.escape(safe_text(value))
    return (f'<div class="stat {_css}"><div class="value">{_value}</div>'
            f'<div class="label">{_html.escape(safe_text(label))}</div></div>')
def render_badge(text: str, css_class: str = 'badge-info') -> str:
    _css = _html.escape(safe_text(css_class), quote=True)
    return f'<span class="badge {_css}">{_html.escape(safe_text(text))}</span>'
def render_progress_bar(value, max_val=1.0, color: str = '#667eea') -> str:
    v = to_finite_float(value)
    m = to_finite_float(max_val)
    pct = (v / m * 100) if m > 0 else 0.0
    pct = max(0.0, min(100.0, pct))
    _color = _html.escape(safe_text(color), quote=True)
    return (f'<div class="progress-bar"><div class="progress-fill" '
            f'style="width:{pct:.1f}%;background:{_color}"></div></div>')
def render_health_badge(health: str) -> str:
    key = safe_text(health).strip().lower()
    css = _HEALTH_BADGE_CSS.get(key, 'health-warning')
    return (f'<span class="health-badge {css}">'
            f'{_html.escape(key.upper())}</span>')
def _table_filter_bar(_tid: str) -> str:
    if not _tid:
        return ''
    return (
        f'<div class="filter-bar"><input type="text" id="filter_{_tid}" '
        f'placeholder="筛选..." '
        f'onkeyup="filterTable(\'filter_{_tid}\', \'{_tid}\')"></div>')
def _table_header_html(headers: list, _tid: str, sortable: bool) -> str:
    header_html = ''
    for i, h in enumerate(headers):
        onclick = f' onclick="sortTable(\'{_tid}\', {i})"' if sortable and _tid else ''
        header_html += f'<th{onclick}>{_html.escape(safe_text(h))}</th>'
    return header_html
def _pad_row_items(row_items, n_cols: int) -> list:
    items = list(row_items)
    if n_cols > 0:
        items = items[:n_cols]
    if n_cols > len(items):
        items.extend([""] * (n_cols - len(items)))
    return items
def _table_body_rows(rows: list, hide_from: int | None,
                     n_cols: int = 0) -> str:
    body_html = ''
    for r_idx, row in enumerate(rows):
        row_items = row if isinstance(row, (list, tuple)) else [row]
        row_items = _pad_row_items(row_items, n_cols)
        cells = ''
        for cell in row_items:
            text = cell if isinstance(cell, str) else _html.escape(safe_text(cell))
            cells += f'<td>{text}</td>'
        body_html += f'<tr{_row_hidden_cls(r_idx, hide_from)}>{cells}</tr>'
    return body_html
def _as_row_list(value) -> list:
    if isinstance(value, (list, tuple)):
        return list(value)
    if not value:
        return []
    if isinstance(value, (str, bytes, dict)):
        return [value]
    try:
        return list(value)
    except TypeError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_as_row_list:TypeError')
        return [value]
def _progressive_window(raw_id, total: int, initial_visible,
                        ) -> tuple[str, str, int | None]:
    item_id = _safe_id(raw_id)
    hide_from = _hide_start(total, initial_visible, bool(item_id))
    return item_id, _id_attr(item_id), hide_from
def _table_row_overflow(rows: list, n_cols: int) -> int:
    if n_cols <= 0:
        return 0
    return sum(1 for row in rows
               if len(row if isinstance(row, (list, tuple)) else (row,)) > n_cols)
def render_table(headers: list | tuple, rows: list | tuple,
                 table_id: str = '', sortable: bool = True,
                 initial_visible: int | None = None) -> str:
    headers = _as_row_list(headers)
    rows = _as_row_list(rows)
    _tid, tid, _hide_from = _progressive_window(
        table_id, len(rows), initial_visible)
    _overflow = _table_row_overflow(rows, len(headers))
    if _overflow:
        logger.warning(
            "[html_report_primitives] 表格 %s 有 %d 行超出表头列数(%d)，"
            "尾部单元格已按契约丢弃", _tid or "<anonymous>", _overflow,
            len(headers))
    filter_html = _table_filter_bar(_tid)
    header_html = _table_header_html(headers, _tid, sortable)
    body_html = _table_body_rows(rows, _hide_from, len(headers))
    _hide_attr = (f' data-jw-hide-from="{_hide_from}"'
                  if _hide_from is not None else '')
    table_html = (f'{filter_html}\n<table{tid}{_hide_attr}>\n'
                  f'<thead><tr>{header_html}'
                  f'</tr></thead>\n<tbody>{body_html}</tbody>\n</table>')
    return _maybe_show_more(table_html, _tid, _hide_from, len(rows))
def _kv_rows(rows) -> list[tuple]:
    if isinstance(rows, dict):
        return list(rows.items())
    if not isinstance(rows, (list, tuple)):
        if rows is not None:
            logger.warning(
                "[html_report_primitives] 键值表行载体非 list/tuple(%s)，按空表渲染",
                type(rows).__name__)
        return []
    normalized: list[tuple] = []
    skipped = 0
    for row in rows:
        if isinstance(row, (list, tuple)) and len(row) == 2:
            normalized.append((row[0], row[1]))
        else:
            skipped += 1
    if skipped:
        logger.warning(
            "[html_report_primitives] 键值表跳过 %d 行非二元组条目（共 %d 行）",
            skipped, len(rows))
    return normalized
def kv_table_preescaped(rows: list, table_id: str = '',
                         initial_visible: int | None = None) -> str:
    body = ''
    rows = _kv_rows(rows)
    _tid, _tid_attr, _hide_from = _progressive_window(
        table_id, len(rows), initial_visible)
    for i, kv in enumerate(rows):
        k, v = kv
        _cls = _row_hidden_cls(i, _hide_from)
        body += (f'<tr{_cls}><td style=\'width:32%;font-weight:600\'>'
                 f'{_html.escape(safe_text(k))}</td><td>{v}</td></tr>')
    table_html = f'<table{_tid_attr}>{body}</table>'
    return _maybe_show_more(table_html, _tid, _hide_from, len(rows))
def render_list_progressive(item_htmls: list, list_id: str = '',
                            initial_visible: int | None = DISCLOSURE_ROWS_STANDARD,
                            *, ordered: bool = False) -> str:
    items = [safe_text(x) for x in _as_row_list(item_htmls)]
    _lid, _lid_attr, _hide_from = _progressive_window(
        list_id, len(items), initial_visible)
    tag = 'ol' if ordered else 'ul'
    if not items:
        return f'<{tag}{_lid_attr}></{tag}>'
    li_parts = []
    for i, it in enumerate(items):
        li_parts.append(f'<li{_row_hidden_cls(i, _hide_from)}>{it}</li>')
    list_html = (f'<{tag}{_lid_attr} style=\'padding-left:20px;\'>'
                 + "".join(li_parts) + f'</{tag}>')
    return _maybe_show_more(list_html, _lid, _hide_from, len(items))
def render_code_block(text, max_height_px: int = _CODE_BLOCK_DEFAULT_HEIGHT) -> str:
    _h = _height_px(max_height_px, _CODE_BLOCK_DEFAULT_HEIGHT)
    return (f"<pre style='overflow:auto;max-height:{_h}px;"
            f"white-space:pre-wrap;word-break:break-all;'>"
            f"{_html.escape(safe_text(text))}</pre>")
def kv_table(rows: Any) -> str:
    return kv_table_preescaped(
        [(k, _html.escape(full_value(v))) for k, v in _kv_rows(rows)])
def _artifact_href(path, report_dir: str) -> str:
    path = text_or(path)
    if not path:
        return ""
    if report_dir:
        try:
            rel = os.path.relpath(path, report_dir).replace(os.sep, "/")
            return _html.escape(quote(rel, safe="/", errors="backslashreplace"))
        except ValueError as _e:
            log_swallowed(__name__, _e, context='_artifact_row:ValueError')
    _url_path = quote(path.replace(os.sep, "/"), safe="/:",
                      errors="backslashreplace")
    _escaped_path = _html.escape(_url_path)
    if _escaped_path.startswith("//"):
        return "file:" + _escaped_path
    if _escaped_path.startswith("/"):
        return "file://" + _escaped_path
    return "file:///" + _escaped_path
def _artifact_mtime_text(a: dict) -> str:
    _raw_mt = a.get("mtime")
    if isinstance(_raw_mt, bool) or not isinstance(_raw_mt, (int, float)):
        return "-"
    if isinstance(_raw_mt, float) and not math.isfinite(_raw_mt):
        return "-"
    try:
        return time.strftime("%Y-%m-%d %H:%M:%S",
                             time.localtime(to_int(_raw_mt)))
    except (OSError, OverflowError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_artifact_row:OSError')
        return "-"
def artifact_row(a: dict, report_dir: str) -> list:
    _href = _artifact_href(a.get("path", ""), report_dir)
    _name = esc_or(a.get("filename"))
    html_link = f"<a href='{_href}'>{_name}</a>" if _href else _name
    json_path = text_or(a.get("json_path"))
    if json_path:
        json_link = _artifact_href(json_path, report_dir)
        html_link += (f"<br><a href='{json_link}'>同名 JSON</a>"
                      if json_link else "<br>同名 JSON")
        status = safe_text(a.get("pair_status"))
        if status == "mismatch":
            html_link += (
                f"<br><span class='badge badge-danger'>条目不一致 "
                f"{to_int(a.get('item_count'))}↔"
                f"{to_int(a.get('json_item_count'))}</span>")
        elif status == "paired":
            html_link += (
                f"<br><span class='badge badge-success'>条目一致 "
                f"{to_int(a.get('item_count'))}</span>")
        elif status == "invalid":
            html_link += ("<br><span class='badge badge-danger'>"
                          "配套 JSON 结构非法</span>")
    elif safe_text(a.get("pair_status")) == "missing":
        html_link += ("<br><span class='badge badge-warning'>"
                      "缺配套 JSON</span>")
    return [
        esc_or(a.get("category"), "其他"),
        html_link,
        f"{to_finite_float(a.get('size')) / 1024:.1f} KB",
        _artifact_mtime_text(a),
        (f"<span class='path-cell'>"
         f"{esc_or(a.get('path'))}</span>"),
    ]
@dataclass
class HTMLReport:
    title: str
    sections: list[ReportSection] = field(default_factory=list)
    raw_data: dict | None = None
    raw_hint: str = ""
    def render(self) -> str:
        sections = list(self.sections)
        _raw_sec = raw_dump_section(self.raw_data, source_hint=self.raw_hint)
        if _raw_sec is not None:
            sections.append(_raw_sec)
        return wrap_html(self.title, sections,
                          meta=derive_header_meta(self.raw_data))
    def save(self, filepath: str) -> str:
        write_html_file(filepath, self.render())
        logger.info("[HTMLReport] 已保存: %s", filepath)
        return filepath
def emit_html(full_html: str, output_path, *, log_message: str,
               log_args: tuple = ()) -> str:
    if not output_path:
        return full_html
    write_html_file(output_path, full_html)
    try:
        logger.info(log_message % (output_path, *log_args))
    except (TypeError, ValueError) as _fmt_err:
        log_swallowed(__name__, _fmt_err, context='emit_html:log_format')
        logger.info("%s: %s", log_message, output_path)
    return output_path
_SKILL_IDENTITY_KEYS = ("skill", "skill_name", "skill_dir", "skill_path",
                        "skill_profile")
def payload_is_skill(raw: dict) -> bool:
    for key in _SKILL_IDENTITY_KEYS:
        value = raw.get(key)
        if isinstance(value, str) and value.strip():
            return True
    return to_bool(raw.get("is_skill"), default=False)
def apply_target_identity(raw: dict, target) -> dict:
    text = text_or(target).strip()
    if not text:
        return raw
    active, stale = (("skill_dir", "target_dir") if payload_is_skill(raw)
                     else ("target_dir", "skill_dir"))
    raw[active] = text
    raw.pop(stale, None)
    return raw
def render_report(title: str, sections: list[ReportSection], target: str,
                   payload: dict, **extra_raw) -> str:
    raw_data = {**payload, **extra_raw}
    apply_target_identity(raw_data, target)
    return HTMLReport(title=title, sections=sections,
                      raw_data=raw_data).render()
def extend_sections(sections: list, candidates) -> None:
    sections.extend(section for section in candidates if section is not None)
def list_card_section(items: list | tuple, *, title: str,
                       section_id: str, icon: str,
                       item_style: str = "") -> ReportSection:
    items = _as_row_list(items)
    style_attr = f' style="{item_style}"' if item_style else ""
    item_html = "".join(
        f"<li{style_attr}>{_html.escape(safe_text(item))}</li>" for item in items)
    return ReportSection(
        title=f"{title} ({len(items)})", section_id=section_id, icon=icon,
        html_content=(f'<div class="card"><ul style="padding-left:20px;">'
                      f'{item_html}</ul></div>'))
def normalize_line_value(v) -> str:
    if v in (None, "") or (isinstance(v, str) and not v.strip()):
        return ""
    if isinstance(v, bool):
        logger.debug("normalize_line_value 布尔值非行号，按空行号降级")
        return ""
    try:
        if isinstance(v, int):
            return str(v) if v > 0 else ""
        if isinstance(v, str) and re.fullmatch(r"[+-]?\d+", v.strip()):
            line = int(v)
            return str(line) if line > 0 else ""
    except ValueError as _e:
        log_swallowed(__name__, _e, context='normalize_line_value:ValueError')
        return ""
    try:
        num = float(v)
    except (ValueError, OverflowError):
        logger.debug("normalize_line_value 契约内脏值降级: value_type=%s",
                     type(v).__name__)
        return ""
    except TypeError as _e:
        log_swallowed(__name__, _e, context='normalize_line_value:TypeError')
        return ""
    if math.isfinite(num) and num > 0 and num.is_integer():
        return str(int(num))
    return ""
def _locator_looks_like_path(text: str) -> bool:
    if not text:
        return False
    if "/" in text or "\\" in text:
        return True
    stem, dot, ext = text.rpartition(".")
    return bool(dot and stem) and ext.isalnum() and len(ext) <= 10
def _split_locator(locator) -> tuple[str, str | None]:
    loc = safe_text(locator or "")
    if ":" not in loc:
        return (loc, None) if _locator_looks_like_path(loc) else ("", None)
    parts = loc.rsplit(":", 2)
    if len(parts) == 3 and parts[1].isdecimal():
        return parts[0], parts[1]
    head, _, tail = loc.rpartition(":")
    if len(head) == 1 and head.isascii() and head.isalpha() and tail[:1] in ("\\", "/"):
        return loc, None
    if head and (_locator_looks_like_path(head) or tail[:1] in ("\\", "/")
                 or tail.isdecimal()):
        return head, tail
    return "", None
def _finding_file(fd) -> str:
    for name in FINDING_KEY_ALIASES["file"]:
        value = read_field(fd, name)
        if value:
            text = safe_text(value)
            if text.strip():
                return text
    return ""
def _finding_line(fd) -> Any:
    current = read_field(fd, "line")
    if normalize_line_value(current):
        return current
    for name in FINDING_KEY_ALIASES["line"][1:]:
        alternate = read_field(fd, name)
        if normalize_line_value(alternate):
            return alternate
    return current
def extract_finding_coords(fd: dict) -> tuple[str, str]:
    file = _finding_file(fd)
    line = _finding_line(fd)
    if file == "" or not normalize_line_value(line):
        locator_file, locator_line = _split_locator(read_field(fd, "locator"))
        file = file or locator_file
        if locator_line is not None:
            line = _locator_line_or_current(line, locator_line)
    return file, normalize_line_value(line)
def _locator_line_or_current(current, locator_line) -> Any:
    if not normalize_line_value(current):
        try:
            return int(locator_line)
        except (ValueError, TypeError):
            logger.debug("locator 尾段非数值行号，按空行号降级: %r", locator_line)
            return current or ""
    return current
_STRUCTURED_MAX_ROWS = DISCLOSURE_ROWS_COMPACT
_CTX_CELL_TEXT_CAP = 600
def _ctx_cell_container_hint(v) -> str:
    if isinstance(v, dict):
        return (f"<span class='json-tree-fallback'>"
                f"{{dict · {len(v)} 键}}</span>")
    return (f"<span class='json-tree-fallback'>"
            f"[{type(v).__name__} · {len(v)} 条]</span>")
def render_ctx_cell(v, text_cap: int = _CTX_CELL_TEXT_CAP) -> str:
    if isinstance(v, _CONTAINER_HINT_TYPES) and v:
        return _ctx_cell_container_hint(v)
    return disclosure_value(v, text_cap)
_STRUCTURED_CARD_LIST_MAX = 5
def _is_scalar_field(value) -> bool:
    return isinstance(value, (str, int, float, bool)) and value != ""
def _is_dict_field(value) -> bool:
    return isinstance(value, dict) and bool(value)
_SEQUENCE_FIELD_TYPES = (list, tuple, set, frozenset)
def _is_list_field(value) -> bool:
    return isinstance(value, _SEQUENCE_FIELD_TYPES) and bool(value)
def _is_nested_field(value) -> bool:
    return _is_dict_field(value) or _is_list_field(value)
def _is_other_field(value) -> bool:
    if value is None:
        return False
    return not isinstance(
        value, (str, int, float, bool, dict, *_SEQUENCE_FIELD_TYPES))
def _bucket_item_fields(item: dict) -> tuple[list, dict, dict]:
    scalars: list = []
    nested: dict = {}
    lists: dict = {}
    for key, value in item.items():
        if _is_dict_field(value):
            nested[key] = value
        elif _is_list_field(value):
            lists[key] = value
        elif _is_scalar_field(value) or _is_other_field(value):
            scalars.append((key, disclosure_value(value)))
    return scalars, nested, lists
def _nested_label(name, unit: str, count: int) -> str:
    return (f"<div style='margin:8px 0 2px;font-weight:600;color:#4a5568'>"
            f"{_html.escape(safe_text(name))}（{count} {unit}）</div>")
def _item_nested_tables(i: int, nested: dict, id_scope: str) -> list[str]:
    parts = []
    prefix = f"{_safe_id(id_scope)}_" if id_scope else ""
    for nk, nv in nested.items():
        sub = [(kk, render_ctx_cell(vv, DISCLOSURE_TEXT_CAP))
               for kk, vv in nv.items()]
        _tid = "card_" + prefix + _safe_id(nk, 'item') + f"_{i}"
        parts.append(
            _nested_label(nk, "键", len(nv))
            + kv_table_preescaped(
                sub,
                table_id=_tid,
                initial_visible=_STRUCTURED_MAX_ROWS))
    return parts
def _item_nested_lists(i: int, lists: dict, id_scope: str) -> list[str]:
    parts = []
    prefix = f"{_safe_id(id_scope)}_" if id_scope else ""
    for lk, lv in lists.items():
        _lid = "cards_" + prefix + _safe_id(lk, 'item') + f"_{i}"
        li = render_list_progressive(
            [render_ctx_cell(it, _STRUCTURED_LIST_ITEM_MAX) for it in lv],
            list_id=_lid, initial_visible=_STRUCTURED_MAX_ROWS)
        parts.append(_nested_label(lk, "条", len(lv)) + li)
    return parts
def _item_card(i: int, item, id_scope: str = "") -> str:
    if not isinstance(item, dict):
        return f"<div class='card'>{disclosure_value(item)}</div>"
    scalars, nested, lists = _bucket_item_fields(item)
    parts = [f"<h4 style='margin:8px 0 4px;color:#2d3748'>条目 #{i}</h4>"]
    if scalars:
        parts.append(kv_table_preescaped(scalars))
    parts.extend(_item_nested_tables(i, nested, id_scope))
    parts.extend(_item_nested_lists(i, lists, id_scope))
    return f"<div class='card'>{''.join(parts)}</div>"
def _collect_unique_keys(items) -> list:
    return list(dict.fromkeys(kk for item in items for kk in item))
def _iter_structured_fields(result: dict,
                             priority_keys: tuple[str, ...],
                             excluded_keys: frozenset[str]):
    for key in priority_keys:
        if key in result and key not in excluded_keys:
            yield key, result[key]
    for key, value in result.items():
        if key not in priority_keys and key not in excluded_keys:
            yield key, value
def render_structured_details(
        result: Any, *, priority_keys: tuple[str, ...] = (),
        excluded_keys: frozenset[str] = frozenset()) -> str:
    if not isinstance(result, dict):
        return ""
    return "".join(
        _render_field_card(key, value)
        for key, value in _iter_structured_fields(
            result, tuple(priority_keys), frozenset(excluded_keys))
        if _is_nested_field(value))
def _has_nested_payload(item: dict) -> bool:
    return any(_is_nested_field(val) for val in item.values())
def _dict_list_body(_fid: str, v: list) -> tuple[str, str]:
    has_nested = any(_has_nested_payload(item) for item in v)
    if len(v) <= _STRUCTURED_CARD_LIST_MAX and has_nested:
        return ("".join(_item_card(i, item, _fid)
                         for i, item in enumerate(v, 1)),
                f"（{len(v)} 条 · 含上下文明细）")
    headers = _collect_unique_keys(v)
    rows = [[render_ctx_cell(item.get(header, ""), DISCLOSURE_TEXT_CAP)
             for header in headers]
            for item in v]
    return (render_table(headers, rows, table_id=_fid,
                          initial_visible=_STRUCTURED_MAX_ROWS),
            f"（{len(v)} 条）")
def _field_list_body(_fid: str, v: list) -> tuple[str, str]:
    if all(isinstance(item, dict) for item in v):
        return _dict_list_body(_fid, v)
    return (render_list_progressive(
        [render_ctx_cell(item, _STRUCTURED_LIST_ITEM_MAX) for item in v],
        list_id=_fid, initial_visible=_STRUCTURED_MAX_ROWS),
        f"（{len(v)} 条）")
def _render_field_card(k, v) -> str:
    _fid = "sd_" + _safe_id(k, "item")
    if isinstance(v, dict):
        rows = [(kk, render_ctx_cell(vv)) for kk, vv in v.items()]
        note = f"（dict · {len(v)} 键）"
        body = kv_table_preescaped(rows, table_id=_fid,
                              initial_visible=_STRUCTURED_MAX_ROWS)
    else:
        body, note = _field_list_body(_fid, v)
    return (f"<div class='card'><h3>{_html.escape(safe_text(k))}"
            f"<small style='color:#718096;font-weight:400;'>{note}</small></h3>"
            f"{body}</div>")

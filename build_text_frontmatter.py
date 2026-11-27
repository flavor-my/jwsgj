from __future__ import annotations

import logging
import re
from collections.abc import Mapping
from dataclasses import dataclass, field
from functools import cache
from pathlib import Path
from typing import Any, NamedTuple

from jwsgj.build_text_document import (
    _NULL_TAGGED_SCALAR_RE,
    _QUOTE_CHARS,
    _YAML_BOOL_NULL_TOKENS,
    _YAML_NUMBER_RE,
    _YAML_TIMESTAMP_RE,
    BLOCK_SCALAR_INDICATORS,
    _as_path,
    _desc_length,
    _description_scalar,
    _description_sequence_item,
    _flow_breaks_at_unindented_field,
    _fold_flow_scalar,
    _is_block_scalar_head,
    _is_empty_yaml_scalar,
    _name_text,
    _parse_flow_scalars,
    _quote_starts_flow_scalar,
    _restore_line_endings,
    _scalar_item,
    _scan_quoted_span_end,
    _split_keep_endings,
    _version_scalar,
    detect_doc_profile,
    normalize_newlines,
    read_skill_text_interpreter_encoding,
    resolve_entry_document,
    safe_text,
    scan_fence_state,
    strip_inline_comment,
    truncate_description,
    unquote_yaml_scalar,
    write_markdown_text,
    write_text_preserving_form,
)
from jwsgj.diag_types_normalize import (
    yaml_safe_desc_line,
    yaml_safe_quote,
)
from jwsgj.diag_types_vocab import DESC_MAX
from jwsgj.log_config import emit_fix_logs, log_swallowed
from jwsgj.runtime_scope import normalize_text

try:
    import yaml as _yaml
except ImportError as _imp_err:
    logging.getLogger(__name__).debug(
        "[build_text_frontmatter] PyYAML 导入失败，回退简单键值解析: %s",
        _imp_err)
    _yaml = None
__all__ = [
    'DEFAULT_SKILL_VERSION',
    'INLINE_KEYWORDS_MAX',
    'INLINE_KEYWORDS_PATTERN',
    'UPLOAD_ALLOWED_FIELDS',
    'UPLOAD_DESC_MAX_CHARS',
    'DescriptionField',
    'detect_doc_profile_text',
    'ensure_complete_frontmatter',
    'extract_description',
    'extract_description_lenient',
    'extract_frontmatter_fields',
    'frontmatter_keywords',
    'frontmatter_value_present',
    'insert_frontmatter_description',
    'is_field_key_line',
    'is_frontmatter_fence',
    'load_frontmatter',
    'locate_frontmatter',
    'locate_frontmatter_body_start',
    'normalize_description_field',
    'normalize_fm_scalar',
    'parse_frontmatter',
    'parse_frontmatter_description',
    'parse_frontmatter_dict',
    'parse_frontmatter_fields',
    'parse_frontmatter_text',
    'parse_skill_md_text',
    'purify_skill_md',
    'read_frontmatter_skill_name',
    'read_meta_degraded',
    'read_skill_md',
    'render_minimal_skill_md',
    'replace_frontmatter_desc_keywords',
    'replace_frontmatter_description',
    'skill_md_verdict',
    'split_frontmatter',
    'split_frontmatter_document',
    'strip_yaml_control_chars',
    'update_frontmatter_desc_keywords',
    'yaml_quote_scalar',
    'yaml_scalar_line',
]
_log = logging.getLogger(__name__)
UPLOAD_ALLOWED_FIELDS: frozenset[str] = frozenset({
    "name", "description", "license", "allowed-tools", "metadata",
    "version",
})
UPLOAD_DESC_MAX_CHARS = 1024
_FM_FENCE_LINE_RE = re.compile(r"---[ \t\r]*\Z")
_YAML_STR_TAG_RE = re.compile(
    r"^(?:!!str|!<tag:yaml\.org,2002:str>)(?=$|[ \t])")
def _split_explicit_str_tag(raw: str) -> tuple[str, bool]:
    text = normalize_text(raw).lstrip()
    match = _YAML_STR_TAG_RE.match(text)
    if match is None:
        return strip_inline_comment(raw), False
    return strip_inline_comment(text[match.end():]), True
def _field_key_pattern(field: str) -> str:
    plain = re.escape(field)
    return rf"^(?:{plain}|'{plain}'|\"{plain}\")[ \t]*:"
@cache
def _field_line_re(field: str) -> re.Pattern[str]:
    return re.compile(_field_key_pattern(field) + r"[ \t]*(.*)$", re.MULTILINE)
def _unclosed_flow_value(text: str) -> bool:
    value = normalize_text(text).lstrip()
    if not value.startswith(("[", "{")):
        return False
    depth = 0
    i = 0
    while i < len(value):
        ch = value[i]
        if ch in _QUOTE_CHARS and _quote_starts_flow_scalar(value, i, 0):
            end = _scan_quoted_span_end(value, i + 1, ch)
            if end is None:
                return True
            i = end
            continue
        if ch == "#" and (i == 0 or value[i - 1] in " \t\r\n"):
            line_end = value.find("\n", i)
            i = len(value) if line_end < 0 else line_end + 1
            continue
        if ch in "[{":
            depth += 1
        elif ch in "]}" and depth:
            depth -= 1
        i += 1
    return depth > 0
def is_field_key_line(line: str, field: str) -> bool:
    if not isinstance(line, str) or not isinstance(field, str) or not field:
        return False
    return (not line[:1].isspace()
            and bool(re.match(_field_key_pattern(field), line)))
def _find_field_line(fm: str, field: str) -> re.Match[str] | None:
    lines = fm.splitlines(keepends=True)
    structural = set(_field_line_numbers(lines, field))
    starts: list[int] = []
    offset = 0
    for line in lines:
        starts.append(offset)
        offset += len(line)
    valid_offsets = {starts[index] for index in structural if index < len(starts)}
    matches = [match for match in _field_line_re(field).finditer(fm)
               if match.start() in valid_offsets]
    return matches[-1] if matches else None
def is_frontmatter_fence(line: str) -> bool:
    return not line[:1].isspace() and bool(_FM_FENCE_LINE_RE.fullmatch(line))
def _frontmatter_leading_blank_end(content: str) -> int:
    offset = 0
    while offset < len(content):
        line_end = content.find("\n", offset)
        if line_end < 0:
            line_end = len(content)
        line = content[offset:line_end]
        if offset == 0:
            line = line.removeprefix("\ufeff")
        if line.strip():
            return offset
        offset = line_end + 1
    return len(content)
def _frontmatter_opening_end(content: str, start: int = 0) -> int | None:
    line_end = content.find("\n", start)
    first_line = content[start:] if line_end < 0 else content[start:line_end]
    first_line = first_line.removeprefix("\ufeff").rstrip("\r")
    if not is_frontmatter_fence(first_line):
        return None
    return len(content) if line_end < 0 else line_end + 1
def locate_frontmatter_body_start(lines: list[str]) -> int:
    if not isinstance(lines, (list, tuple)):
        return 0
    first = 0
    while first < len(lines):
        line = str(lines[first])
        if first == 0:
            line = line.removeprefix("\ufeff")
        if line.strip():
            break
        first += 1
    if first >= len(lines):
        return 0
    opening = str(lines[first]).lstrip("\ufeff").rstrip("\r\n")
    if not is_frontmatter_fence(opening):
        return 0
    for i in range(first + 1, len(lines)):
        if is_frontmatter_fence(str(lines[i]).rstrip("\r\n")):
            return i + 1
    return 0
def split_frontmatter(content: str) -> list[str]:
    text = normalize_newlines(normalize_text(content))
    located = _frontmatter_span_norm(text)
    if located is None:
        return [text]
    view, opening_end, close_start, close_end = located
    bom_len = len(text) - len(view)
    prefix_end = _frontmatter_leading_blank_end(view)
    return [text[:bom_len + prefix_end],
            view[opening_end:close_start + 1],
            view[close_end:]]
def _block_scalar_indicator(header: str) -> int | None:
    match = re.search(r'[1-9]', header or "")
    return int(match.group(0)) if match else None
def _render_block_scalar(style: str, lines: list[str]) -> str:
    if style != ">":
        return "\n".join(lines)
    out: list[str] = []
    blanks = 0
    previous_more_indented = False
    for line in lines:
        if not line:
            blanks += 1
            continue
        more_indented = line[:1] in (" ", "\t")
        if not out:
            out.append("\n" * blanks)
        elif previous_more_indented or more_indented:
            out.append("\n" * (1 + blanks))
        elif blanks:
            out.append("\n" * blanks)
        else:
            out.append(" ")
        out.append(line)
        blanks = 0
        previous_more_indented = more_indented
    return "".join(out)
@dataclass
class _BlockScalarCollector:
    key: str | None = None
    style: str = "|"
    indicator: int | None = None
    base_indent: int | None = None
    lines: list[str] = field(default_factory=list)
    pending_blanks: int = 0
    def start(self, key: str | None, header: str = "") -> None:
        self.key = key
        header = (header or "").strip()
        self.style = header[:1] if header[:1] in ("|", ">") else "|"
        self.indicator = _block_scalar_indicator(header)
        self.base_indent = None
        self.lines = []
        self.pending_blanks = 0
    def append_blank(self) -> None:
        if self.key is not None:
            self.pending_blanks += 1
    def append_indented(self, line: str) -> None:
        if self.key is None:
            return
        indent = len(line) - len(line.lstrip(" \t"))
        if self.base_indent is None:
            self.base_indent = self.indicator or indent or 0
        if indent >= self.base_indent:
            content = line[self.base_indent:]
        else:
            content = line.lstrip(" \t")
        self.lines.extend("" for _ in range(self.pending_blanks))
        self.pending_blanks = 0
        self.lines.append(content.rstrip(" \t"))
    def flush_into(self, scan: _FrontmatterScan) -> None:
        block_key, block_style = self.key, self.style
        block_lines = self.lines
        self.start(None)
        text = _render_block_scalar(block_style, block_lines)
        if block_key == "name":
            scan.name = _name_text(text)
        elif block_key == "description":
            scan.description = text
        elif block_key == "version":
            scan.version = text.strip()
@dataclass
class _FrontmatterScan:
    keys: list[str] = field(default_factory=list)
    key_line_numbers: list[tuple[str, int]] = field(default_factory=list)
    name: str = ""
    description: str = ""
    version: str = ""
    block: _BlockScalarCollector = field(default_factory=_BlockScalarCollector)
    pending_key: str | None = None
    pending_quote: str = ""
    pending_text: str = ""
    pending_plain_key: str | None = None
    pending_plain_sequence: bool = False
    pending_plain_sequence_valid: bool = True
    pending_plain_sequence_quote: str = ""
    pending_plain_sequence_raw: bool = False
    pending_plain_explicit_str: bool = False
    pending_plain_sequence_indent: int | None = None
    pending_plain_lines: list[str] = field(default_factory=list)
    pending_plain_blanks: int = 0
    _line_number: int = -1
    def consume_line(self, line: str) -> None:
        self._line_number += 1
        if self.pending_key is not None:
            self._consume_pending_scalar(line)
            return
        if self.pending_plain_key is not None:
            if self._consume_pending_sequence_quote(line):
                return
            if not line.strip():
                self.pending_plain_blanks += 1
                return
            stripped = line.strip()
            if self._consume_flow_continuation(line):
                return
            if stripped.startswith("#"):
                if (self.pending_plain_sequence
                        or not any(text.strip()
                                   for text in self.pending_plain_lines)):
                    return
                self._flush_pending_plain()
            elif self._consume_pending_description_sequence(line):
                return
            if line[:1] in (" ", "\t"):
                continuation = _plain_scalar_text(line)
                if self.pending_plain_sequence:
                    if not self.pending_plain_sequence_valid:
                        self.pending_plain_blanks = 0
                        return
                    if (continuation is None
                            or not self.pending_plain_sequence_raw):
                        self.pending_plain_sequence_valid = False
                        self.pending_plain_sequence_raw = False
                        if self.pending_plain_lines:
                            self.pending_plain_lines[-1] = ""
                        self.pending_plain_blanks = 0
                        return
                    if self.pending_plain_lines:
                        self.pending_plain_lines[-1] += (
                            "\n" * (1 + self.pending_plain_blanks) + line)
                        self.pending_plain_blanks = 0
                        return
                    self._flush_pending_plain()
                    return
                if continuation is None:
                    self._flush_pending_plain()
                    return
                self.pending_plain_lines.extend(
                    "" for _ in range(self.pending_plain_blanks))
                self.pending_plain_blanks = 0
                self.pending_plain_lines.append(continuation)
                return
            self._flush_pending_plain()
        if not line.strip():
            self.block.append_blank()
            return
        if line[:1] in (" ", "\t"):
            self.block.append_indented(line)
            return
        self.block.flush_into(self)
        self._consume_top_level(line.rstrip("\r\n"))
    def _finish_pending_sequence_item(self) -> None:
        if not self.pending_plain_lines:
            self.pending_plain_sequence_quote = ""
            self.pending_plain_sequence_raw = False
            return
        quote = self.pending_plain_sequence_quote
        if quote:
            self.pending_plain_lines[-1] = _fold_flow_scalar(
                self.pending_plain_lines[-1], quote).rstrip()
        elif self.pending_plain_sequence_raw and self.pending_plain_sequence_valid:
            folded = _fold_flow_scalar(self.pending_plain_lines[-1])
            self.pending_plain_lines[-1] = _description_sequence_item(folded)
        self.pending_plain_sequence_quote = ""
        self.pending_plain_sequence_raw = False
    def _consume_pending_sequence_quote(self, line: str) -> bool:
        quote = self.pending_plain_sequence_quote
        if not quote:
            return False
        if not line.strip():
            self.pending_plain_lines[-1] += "\n"
            return True
        if line[:1] not in (" ", "\t"):
            self._finish_pending_sequence_item()
            return False
        self.pending_plain_lines[-1] += "\n" + line
        raw = self.pending_plain_lines[-1]
        end = _scan_quoted_span_end(raw, 0, quote)
        if end is not None:
            self.pending_plain_lines[-1] = _fold_flow_scalar(
                raw[:end - 1], quote)
            self.pending_plain_sequence_quote = ""
        self.pending_plain_blanks = 0
        return True
    def _consume_flow_continuation(self, line: str) -> bool:
        pending = "\n".join(self.pending_plain_lines)
        if not _unclosed_flow_value(pending):
            return False
        if (line[:1] not in (" ", "\t")
                and _flow_breaks_at_unindented_field("\n" + line, 0)):
            return False
        self.pending_plain_lines.extend(
            "" for _ in range(self.pending_plain_blanks))
        self.pending_plain_lines.append(line)
        self.pending_plain_blanks = 0
        return True
    def _consume_pending_description_sequence(self, line: str) -> bool:
        stripped = line.strip()
        if (self.pending_plain_key != "description"
                or not _is_dash_sequence_item(stripped)):
            return False
        if (not self.pending_plain_sequence
                and any(text.strip() for text in self.pending_plain_lines)):
            return False
        indent = len(line) - len(line.lstrip(" \t"))
        if not self.pending_plain_sequence:
            self.pending_plain_sequence = True
            self.pending_plain_sequence_indent = indent
            self.pending_plain_lines = []
        else:
            if indent != self.pending_plain_sequence_indent:
                return False
            self._finish_pending_sequence_item()
        raw_item = strip_inline_comment(stripped[1:].strip())
        self.pending_plain_sequence_valid = True
        self.pending_plain_sequence_quote = ""
        self.pending_plain_sequence_raw = False
        self.pending_plain_lines.append("")
        if raw_item[:1] in _QUOTE_CHARS:
            quote = raw_item[0]
            end = _scan_quoted_span_end(raw_item, 1, quote)
            if end is None:
                self.pending_plain_sequence_quote = quote
                self.pending_plain_lines[-1] = raw_item[1:]
            else:
                self.pending_plain_lines[-1] = _fold_flow_scalar(
                    raw_item[1:end - 1], quote)
        elif raw_item and _plain_scalar_text(raw_item) is None:
            self.pending_plain_sequence_valid = False
        else:
            self.pending_plain_sequence_raw = True
            self.pending_plain_lines[-1] = raw_item
        self.pending_plain_blanks = 0
        return True
    def finish(self) -> tuple[list[str], str, str]:
        self._flush_unclosed_quote()
        self._flush_pending_plain()
        self.block.flush_into(self)
        return self.keys, self.name, self.description
    def _flush_unclosed_quote(self) -> None:
        if self.pending_key is None:
            return
        key = self.pending_key
        quote = self.pending_quote
        text = self.pending_text
        self.pending_key = None
        self.pending_quote = ""
        self.pending_text = ""
        self._assign_scalar(
            key, _fold_flow_scalar(text, quote).rstrip(), quoted=True)
    def _flush_pending_plain(self) -> None:
        key = self.pending_plain_key
        if key is None:
            return
        if self.pending_plain_sequence:
            self._finish_pending_sequence_item()
        lines = self.pending_plain_lines
        sequence = self.pending_plain_sequence
        explicit_str = self.pending_plain_explicit_str
        self.pending_plain_key = None
        self.pending_plain_sequence = False
        self.pending_plain_sequence_valid = True
        self.pending_plain_sequence_quote = ""
        self.pending_plain_sequence_raw = False
        self.pending_plain_explicit_str = False
        self.pending_plain_sequence_indent = None
        self.pending_plain_lines = []
        self.pending_plain_blanks = 0
        if sequence:
            self._assign_scalar(
                key, "\n".join(item for item in lines if item), quoted=True)
            return
        joined = "\n".join(lines)
        value = (joined.strip()
                 if not explicit_str and joined.lstrip().startswith(("[", "{"))
                 else _fold_flow_scalar(joined).strip())
        self._assign_scalar(key, value, quoted=explicit_str)
    def _consume_pending_scalar(self, line: str) -> None:
        self.pending_text += "\n" + line
        end = _scan_quoted_span_end(self.pending_text, 0, self.pending_quote)
        if end is None:
            return
        value = _fold_flow_scalar(
            self.pending_text[:end - 1], self.pending_quote)
        self._assign_scalar(self.pending_key, value, quoted=True)
        self.pending_key = None
        self.pending_quote = ""
        self.pending_text = ""
    def _assign_scalar(self, key: str | None, value: str,
                       *, quoted: bool = False) -> None:
        if key == "name":
            text = value.strip()
            if not quoted and (
                not text
                or text.lower() in _YAML_BOOL_NULL_TOKENS
                or _is_empty_yaml_scalar(text)
                or text.startswith(("[", "{"))
            ):
                self.name = ""
            else:
                self.name = _name_text(text)
        elif key == "description":
            self.description = _description_scalar(value, quoted=quoted)
        elif key == "version":
            self.version = _version_scalar(value, quoted=quoted)
    def _record_key(self, key: str) -> None:
        if key:
            self.key_line_numbers.append((key, self._line_number))
        if key and key not in self.keys:
            self.keys.append(key)
    def _consume_top_level(self, stripped: str) -> None:
        if stripped.startswith("#"):
            return
        if _is_dash_sequence_item(stripped):
            return
        if ":" in stripped:
            self._consume_kv(stripped)
    def _consume_kv(self, stripped: str) -> None:
        key, _, raw_value = stripped.partition(":")
        key = unquote_yaml_scalar(key)
        if not key:
            return
        self._record_key(key)
        value, explicit_str = _split_explicit_str_tag(raw_value)
        if _is_block_scalar_head(value):
            self.block.start(key, value)
            return
        if value[:1] in _QUOTE_CHARS:
            end = _scan_quoted_span_end(value, 1, value[0])
            if end is None:
                self.pending_key = key
                self.pending_quote = value[0]
                self.pending_text = value[1:]
                return
            self._assign_scalar(
                key, _fold_flow_scalar(value[1:end - 1], value[0]), quoted=True)
            return
        if _unclosed_flow_value(value):
            self.pending_plain_key = key
            self.pending_plain_sequence = False
            self.pending_plain_explicit_str = explicit_str
            self.pending_plain_lines = [value]
            return
        if key in ("name", "description", "version"):
            self.pending_plain_key = key
            self.pending_plain_sequence = False
            self.pending_plain_explicit_str = explicit_str
            self.pending_plain_lines = [unquote_yaml_scalar(value)]
            return
        self._assign_scalar(key, unquote_yaml_scalar(value))
def _is_root_flow_mapping(fm: str) -> bool:
    """frontmatter 正文是否为根级 flow mapping（首有效字符为 '{'）。"""
    first = _first_significant_line(fm)
    return first is not None and first[2].startswith("{")


def _parse_root_flow_fields(fm: str) -> tuple[list[str], str, str]:
    """根级 flow mapping 走 PyYAML 解析；不可用时返回空字段，避免伪造键。"""
    parsed, _reason, _detail = _yaml_safe_load(fm.strip())
    if not isinstance(parsed, dict):
        return [], "", ""
    canonical = _canonical_meta_fields(parsed, fm, safe_loaded=True)
    return (
        list(canonical.keys()),
        _normalize_scalar_field(canonical.get("name", "")),
        normalize_description_field(canonical.get("description", "")),
    )


def parse_frontmatter_fields(fm_lines: list[str]) -> tuple[list[str], str, str]:
    if not isinstance(fm_lines, (list, tuple)):
        return [], "", ""
    lines = list(fm_lines)
    joined = "\n".join(lines)
    if _is_root_flow_mapping(joined):
        return _parse_root_flow_fields(joined)
    # 整体缩进的 frontmatter 对 YAML 合法，但字段锚点只识别顶格键；
    # 读路径与修复/写回路径必须同源归一，否则合法文档会被判定为缺少字段。
    base_indent = _frontmatter_body_indent(lines)
    if base_indent:
        lines = [_dedent_frontmatter_line(line, base_indent) for line in lines]
    scan = _FrontmatterScan()
    for line in lines:
        scan.consume_line(line)
    return scan.finish()
def _field_line_numbers(fm_lines: list[str], field: str) -> list[int]:
    scan = _FrontmatterScan()
    for line in fm_lines:
        scan.consume_line(line.rstrip("\r\n"))
    return [number for key, number in scan.key_line_numbers if key == field]
class DescriptionField(NamedTuple):
    value: str
    empty_block_marker: str = ""
def parse_frontmatter_description(fm: str) -> DescriptionField:
    fm = normalize_text(fm)
    _keys, _name, description = parse_frontmatter_fields(fm.splitlines())
    desc_m = _find_field_line(fm, "description")
    inline = (_split_explicit_str_tag(desc_m.group(1))[0]
              if desc_m is not None else "")
    if description:
        return DescriptionField(description, "")
    if desc_m is None:
        return DescriptionField("", "")
    return DescriptionField("", inline if _is_block_scalar_head(inline) else "")
def _first_significant_line(text: str) -> tuple[int, str, str] | None:
    offset = 0
    for line in text.splitlines(keepends=True):
        stripped = strip_inline_comment(line)
        if stripped:
            return offset, line, stripped
        offset += len(line)
    return None
def _leading_flow_list_start(text: str) -> int | None:
    found = _first_significant_line(text)
    if found is None:
        return None
    offset, line, stripped = found
    if not stripped.startswith("["):
        return None
    return offset + len(line) - len(line.lstrip(" \t"))
def _is_null_field_value(value: str) -> bool:
    text = normalize_text(value).strip()
    return (not text or text.lower() in ("null", "~")
            or _NULL_TAGGED_SCALAR_RE.match(text) is not None)
def _keyword_field_is_null(fm: str, match: re.Match[str]) -> bool:
    head = strip_inline_comment(match.group(1))
    if head:
        return _is_null_field_value(head)
    value_lines: list[str] = []
    for line in fm[match.end():].splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if (line[:1] not in (" ", "\t")
                and not _is_dash_sequence_item(stripped)):
            break
        value = strip_inline_comment(stripped)
        if value:
            value_lines.append(value)
    return _is_null_field_value("\n".join(value_lines))
def _complete_field_value(fm: str, match: re.Match[str], field: str) -> str:
    lines = fm.splitlines(keepends=True)
    anchors = _field_line_numbers(lines, field)
    if not anchors:
        return match.group(1)
    start = anchors[-1]
    end = _field_value_end(lines, start, field)
    if end is None:
        return match.group(1)
    value_offset = match.start(1) - match.start()
    return "".join(lines[start:end])[value_offset:]
def _parse_keyword_scalar(value: str) -> list[str]:
    text, explicit_str = _split_explicit_str_tag(value)
    if not text:
        return []
    if text[0] in _QUOTE_CHARS:
        quote = text[0]
        end = _scan_quoted_span_end(text, 1, quote)
        if end is None:
            return []
        keyword = _fold_flow_scalar(text[1:end - 1], quote)
        return [line.strip() for line in keyword.splitlines() if line.strip()]
    folded = _fold_flow_scalar(text).strip()
    if explicit_str:
        return _split_keyword_scalar_text(folded)
    value = _scalar_item(folded)
    return _split_keyword_scalar_text(value) if value else []
def _parse_keyword_field(fm: str, field: str) -> list[str]:
    kw_m = _find_field_line(fm, field)
    if kw_m is None:
        return []
    value_start = kw_m.start(1)
    if fm.startswith("[", value_start):
        return _parse_flow_scalars(fm, value_start + 1)
    head, explicit_str = _split_explicit_str_tag(kw_m.group(1))
    if _is_block_scalar_head(head):
        return _parse_block_scalar_keywords(fm[kw_m.end():], head.strip())
    if head:
        if _is_dash_sequence_item(head):
            head = head[1:].strip()
            return _parse_keyword_scalar(head)
        return _parse_keyword_scalar(_complete_field_value(fm, kw_m, field))
    if explicit_str:
        return _parse_keyword_scalar(_complete_field_value(fm, kw_m, field))
    tail = fm[kw_m.end():]
    flow_start = _leading_flow_list_start(tail)
    if flow_start is not None:
        return _parse_flow_scalars(tail, flow_start + 1)
    return _parse_block_keywords(tail)
def _parse_keywords(fm: str) -> list[str]:
    kw_m = _find_field_line(fm, "keywords")
    if kw_m is None:
        return _parse_keyword_field(fm, "tags")
    keywords = _parse_keyword_field(fm, "keywords")
    if keywords:
        return keywords
    if _keyword_field_is_null(fm, kw_m):
        return _parse_keyword_field(fm, "tags")
    return keywords
def _split_block_scalar_line(line: str) -> list[str]:
    segments: list[str] = []
    buf: list[str] = []
    i, n = 0, len(line)
    while i < n:
        ch = line[i]
        if ch in _QUOTE_CHARS and _quote_starts_flow_scalar(line, i, 0):
            end = _scan_quoted_span_end(line, i + 1, ch)
            if end is None:
                buf.append(line[i:])
                break
            buf.append(line[i:end])
            i = end
            continue
        if ch in ",，、":
            segments.append("".join(buf))
            buf = []
            i += 1
            continue
        buf.append(ch)
        i += 1
    segments.append("".join(buf))
    return segments
def _keyword_item_text(segment: str) -> str:
    text = normalize_text(segment).strip()
    if not text:
        return ""
    if len(text) >= 2 and text[0] == text[-1] and text[0] in _QUOTE_CHARS:
        return unquote_yaml_scalar(text)
    return text
def _keyword_line_items(line: str) -> list[str]:
    text = normalize_text(line).strip()
    if not text:
        return []
    if _is_dash_sequence_item(text):
        text = text[1:].strip()
        if not text:
            return []
    return [item for item in
            (_keyword_item_text(seg) for seg in _split_block_scalar_line(text))
            if item]
def _split_keyword_scalar_text(text: str) -> list[str]:
    items: list[str] = []
    for line in normalize_text(text).splitlines():
        items.extend(_keyword_line_items(line))
    return items
def _parse_block_scalar_keywords(block: str, header: str = "|") -> list[str]:
    collector = _BlockScalarCollector()
    collector.start("keywords", header)
    for line in normalize_text(block).split("\n"):
        if not line.strip():
            collector.append_blank()
            continue
        if line[:1] not in (" ", "\t"):
            break
        collector.append_indented(line)
    rendered = _render_block_scalar(collector.style, collector.lines)
    return _split_keyword_scalar_text(rendered)
def _parse_block_keywords(block: str) -> list[str]:
    lines: list[str] = []
    quoted_raw = ""
    quoted_char = ""
    for line in block.splitlines():
        stripped = line.strip()
        if quoted_char:
            if stripped == "---":
                break
            if (stripped and line[:1] not in (" ", "\t")
                    and not _is_dash_sequence_item(stripped)):
                break
            lines.append(stripped)
            quoted_raw += "\n" + stripped
            if _scan_quoted_span_end(quoted_raw, 0, quoted_char) is not None:
                quoted_char = ""
            continue
        if not stripped or stripped.startswith("#"):
            continue
        if stripped == "---":
            break
        if line[:1] not in (" ", "\t") and not _is_dash_sequence_item(stripped):
            break
        lines.append(stripped)
        if _is_dash_sequence_item(stripped):
            raw_item = strip_inline_comment(stripped[1:].strip())
            if (raw_item[:1] in _QUOTE_CHARS and _scan_quoted_span_end(
                    raw_item, 1, raw_item[0]) is None):
                quoted_char = raw_item[0]
                quoted_raw = raw_item[1:]
    if not lines:
        return []
    if not _is_dash_sequence_item(lines[0]):
        if any(_plain_scalar_text(line) is None for line in lines):
            return []
        return _parse_flow_scalars("[" + " ".join(lines) + "]", 1)
    keywords: list[str] = []
    pending_lines: list[str] = []
    pending_valid = False
    pending_quote = ""
    def flush_pending() -> None:
        nonlocal pending_quote
        pending_quote = ""
        if not pending_valid or not pending_lines:
            return
        raw = "\n".join(pending_lines)
        if not raw:
            return
        if raw[0] in _QUOTE_CHARS:
            end = _scan_quoted_span_end(raw, 1, raw[0])
            inner = raw[1:] if end is None else raw[1:end - 1]
            keyword = _fold_flow_scalar(inner, raw[0])
            if end is None:
                keyword = keyword.rstrip()
        else:
            keyword = _scalar_item(_fold_flow_scalar(raw))
        if keyword:
            keywords.extend(line.strip() for line in keyword.splitlines()
                            if line.strip())
    for stripped in lines:
        if pending_quote:
            pending_lines.append(stripped)
            raw = "\n".join(pending_lines)
            if _scan_quoted_span_end(raw, 1, pending_quote) is not None:
                pending_quote = ""
            continue
        if not stripped:
            continue
        if _is_dash_sequence_item(stripped):
            flush_pending()
            raw_item = strip_inline_comment(stripped[1:].strip())
            pending_lines = [raw_item]
            pending_valid = (
                not raw_item or raw_item[0] in _QUOTE_CHARS
                or _plain_scalar_text(raw_item) is not None
            )
            if (raw_item[:1] in _QUOTE_CHARS and _scan_quoted_span_end(
                    raw_item, 1, raw_item[0]) is None):
                pending_quote = raw_item[0]
            continue
        continuation = _plain_scalar_text(stripped)
        if continuation is None:
            pending_valid = False
            continue
        if pending_valid:
            pending_lines.append(continuation)
    flush_pending()
    return keywords
def parse_skill_md_text(text: str, default_name: str = "") -> dict[str, Any]:
    text = normalize_text(text)
    default_name = normalize_text(default_name)
    text = normalize_newlines(text.lstrip("\ufeff"))
    fm = _frontmatter_body(text)
    if fm is None:
        return {"name": default_name, "description": "", "keywords": [], "version": ""}
    parsed, _reason, _detail = _yaml_safe_load(fm)
    if parsed is not None:
        parsed = _canonical_meta_fields(parsed, fm, safe_loaded=True)
        keywords = (parsed["keywords"] if "keywords" in parsed
                    else parsed.get("tags", []))
        return {
            "name": parsed.get("name", "") or default_name,
            "description": parsed.get("description", ""),
            "keywords": keywords or [],
            "version": parsed.get("version", ""),
        }
    scan = _FrontmatterScan()
    for line in fm.splitlines():
        scan.consume_line(line)
    _keys, name, description = scan.finish()
    return {
        "name": name.strip() or default_name,
        "description": description,
        "keywords": _parse_keywords(fm),
        "version": scan.version,
    }
def _frontmatter_body(text: str) -> str | None:
    parts = split_frontmatter(text)
    if len(parts) >= 3 and not parts[0].lstrip("\ufeff").strip():
        return parts[1]
    return None
def read_skill_md(skill_dir: Path | str) -> dict[str, Any]:
    try:
        skill_dir = _as_path(skill_dir)
    except (TypeError, ValueError) as exc:
        raise OSError(f"skill_dir 类型非法: {skill_dir!r}") from exc
    md_path = resolve_entry_document(skill_dir)
    if md_path is None:
        return parse_skill_md_text("", default_name=skill_dir.name)
    try:
        text = md_path.read_text(encoding="utf-8-sig")
    except (OSError, UnicodeDecodeError) as e:
        _log.warning("无法读取入口文档 %s：%s", md_path, e)
        raise
    return parse_skill_md_text(text, default_name=skill_dir.name)
_YAML_CTRL_CHARS_RE = re.compile(r'[\x00-\x1f\x7f-\x9f]')
_YAML_UNPRINTABLE_CHARS_RE = re.compile(r'[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]')
def strip_yaml_control_chars(value: str) -> str:
    return _YAML_CTRL_CHARS_RE.sub("", value)
_YAML_LINESEP_ESCAPES = {"\x85": "\\N", "\u2028": "\\L", "\u2029": "\\P"}
_YAML_LINESEP_RE = re.compile("[" + "".join(_YAML_LINESEP_ESCAPES) + "]")
def yaml_quote_scalar(value) -> str:
    s = safe_text(value).replace('\\', '\\\\').replace('"', '\\"')
    s = s.replace('\n', '\\n').replace('\r', '\\r').replace('\t', '\\t')
    s = _YAML_LINESEP_RE.sub(lambda _m: _YAML_LINESEP_ESCAPES[_m.group()], s)
    s = _YAML_UNPRINTABLE_CHARS_RE.sub(lambda _m: f'\\x{ord(_m.group()):02x}', s)
    return '"' + s + '"'
def _yaml_needs_quoting(v: str) -> bool:
    return (v.lower() in _YAML_BOOL_NULL_TOKENS
            or bool(_YAML_NUMBER_RE.fullmatch(v))
            or bool(_YAML_TIMESTAMP_RE.fullmatch(v))
            or bool(_YAML_LINESEP_RE.search(v)))
def yaml_scalar_line(key: str, value) -> str:
    v = safe_text(value)
    if (not v or v == "=" or v != v.strip() or re.search(r'[:#"\']', v)
            or v[0] in _PLAIN_SCALAR_UNSAFE_INITIALS or v[0] in "-?"
            or _YAML_CTRL_CHARS_RE.search(v)
            or _yaml_needs_quoting(v)):
        return f"{key}: {yaml_quote_scalar(v)}"
    return f"{key}: {v}"
INLINE_KEYWORDS_MAX = 10
INLINE_KEYWORDS_PATTERN = (
    r'(?m)' + _field_key_pattern("keywords") + r'\s*\['
    r'(?:\s|[^\]"\']|\'[^\']*\'|"(?:[^"\\]|\\.)*")*\]'
)
_FRONTMATTER_DOC_PREFIX = r"\A\ufeff?(?:[ \t]*\r?\n)*"
_FRONTMATTER_BLOCK_PATTERN = re.compile(
    _FRONTMATTER_DOC_PREFIX
    + r'---[ \t]*\r?\n(.*?)(?:\r?\n)?(?m:^---)[ \t]*(?=\r?\n|\Z)',
    re.DOTALL)
def _replace_last_match(pattern: str | re.Pattern[str], replacement: str,
                        text: str, field: str) -> tuple[str, int]:
    anchor = _find_field_line(text, field)
    if anchor is None:
        return text, 0
    matcher = (pattern.finditer if hasattr(pattern, "finditer")
               else lambda value: re.finditer(pattern, value))
    matches = [match for match in matcher(text)
               if match.start() == anchor.start()]
    if not matches:
        return text, 0
    last = matches[-1]
    return text[:last.start()] + replacement + text[last.end():], 1
def _field_value_end(lines: list[str], start: int, field: str) -> int | None:
    head = _field_line_re(field).match(lines[start])
    raw_value = head.group(1) if head is not None else ""
    value, _explicit_str = _split_explicit_str_tag(raw_value)
    indentless_sequence = not value
    if value[:1] in _QUOTE_CHARS and _scan_quoted_span_end(
            value, 1, value[0]) is None:
        quote = value[0]
        pending = value[1:]
        for cursor in range(start + 1, len(lines)):
            pending += "\n" + lines[cursor].rstrip("\r\n")
            if _scan_quoted_span_end(pending, 0, quote) is not None:
                return cursor + 1
        return None
    if _unclosed_flow_value(value):
        pending = value
        for cursor in range(start + 1, len(lines)):
            body = lines[cursor].rstrip("\r\n")
            if (body[:1] not in (" ", "\t")
                    and _flow_breaks_at_unindented_field("\n" + body, 0)):
                break
            pending += "\n" + body
            if not _unclosed_flow_value(pending):
                return cursor + 1
        return None
    end = start + 1
    for cursor in range(start + 1, len(lines)):
        body = lines[cursor].rstrip("\r\n")
        if not body.strip():
            continue
        if indentless_sequence and _is_dash_sequence_item(body):
            end = cursor + 1
            continue
        if body[:1] in (" ", "\t"):
            end = cursor + 1
            continue
        if body.startswith("#"):
            continue
        break
    return end
def _replace_field_block(fm_body: str, field: str,
                         replacement: str) -> tuple[str, int]:
    lines = fm_body.splitlines(keepends=True)
    anchors = [index for index in _field_line_numbers(lines, field)
               if is_field_key_line(lines[index].rstrip("\r\n"), field)]
    if not anchors:
        return fm_body, 0
    start = anchors[-1]
    end = _field_value_end(lines, start, field)
    if end is None:
        return fm_body, 0
    if end < len(lines) and not replacement.endswith(("\n", "\r")):
        head_eol = lines[start][len(lines[start].rstrip("\r\n")):]
        replacement += head_eol or "\n"
    return "".join(lines[:start]) + replacement + "".join(lines[end:]), 1
def _insert_after_field(fm_body: str, field: str, new_line: str,
                        ) -> tuple[str, int]:
    lines = fm_body.splitlines(keepends=True)
    anchors = [index for index in _field_line_numbers(lines, field)
               if is_field_key_line(lines[index].rstrip("\r\n"), field)]
    if not anchors:
        return fm_body, 0
    end = _field_value_end(lines, anchors[-1], field)
    if end is None:
        return fm_body, 0
    prefix = "".join(lines[:end])
    suffix = "".join(lines[end:])
    before = "" if not prefix or prefix.endswith(("\n", "\r")) else "\n"
    after = "\n" if suffix else ""
    return prefix + before + new_line + after + suffix, 1
def _inline_flow_crosses_top_level_field(match: re.Match[str]) -> bool:
    for line in match.group(0).splitlines()[1:]:
        if (not line.strip() or line.startswith("#")
                or line[:1] in (" ", "\t", "]", "}", ",")):
            continue
        key, separator, _value = line.partition(":")
        if separator and key and key == key.strip():
            return True
    return False
def _replace_keywords_in_fm(fm_body: str, optimized_keywords: list[str],
                            md_label: str) -> tuple:
    kw_str = ", ".join(
        yaml_quote_scalar(kw) for kw in optimized_keywords[:INLINE_KEYWORDS_MAX])
    kw_line = f'keywords: [{kw_str}]'
    inline_matches = list(re.finditer(INLINE_KEYWORDS_PATTERN, fm_body))
    n_replaced = 0
    if any(_inline_flow_crosses_top_level_field(match)
           for match in inline_matches):
        _log.warning(
            "replace_frontmatter_desc_keywords: %s keywords 流式列表跨越"
            "顶层字段，按未识别形态仅替换字段头", md_label)
    else:
        fm_body, n_replaced = _replace_last_match(
            INLINE_KEYWORDS_PATTERN, kw_line, fm_body, "keywords")
    has_field = _find_field_line(fm_body, "keywords") is not None
    if not n_replaced and has_field:
        fm_body, n_replaced = _replace_field_block(
            fm_body, "keywords", kw_line)
        if not n_replaced:
            _log.warning(
                "replace_frontmatter_desc_keywords: %s 存在未识别的 keywords "
                "键形态，keywords 写回未落盘", md_label)
            return fm_body, 0
    if not n_replaced:
        desc_anchor = _find_field_line(fm_body, "description")
        name_anchor = _find_field_line(fm_body, "name")
        anchor = ("description" if desc_anchor is not None and (
            name_anchor is None or desc_anchor.start() > name_anchor.start())
            else "name")
        fm_body, n_replaced = _insert_after_field(fm_body, anchor, kw_line)
        if not n_replaced:
            _log.warning(
                "replace_frontmatter_desc_keywords: %s 无 keywords 键且无 "
                "description/name 锚点，keywords 写回未落盘", md_label)
    return fm_body, n_replaced
def _replace_description_in_fm(fm_body: str, optimized_desc: str,
                               md_label: str) -> tuple[str, int]:
    safe_desc = yaml_safe_desc_line(optimized_desc)
    fm_body, n_desc = _replace_field_block(
        fm_body, "description", safe_desc)
    if not n_desc:
        _log.warning(
            "replace_frontmatter_desc_keywords: %s 无 description 锚点，"
            "description 写回未落盘", md_label)
    return fm_body, n_desc
def split_frontmatter_document(content: str) -> tuple[str, str] | None:
    normalized = normalize_newlines(normalize_text(content))
    match = _FRONTMATTER_BLOCK_PATTERN.match(normalized)
    if not match:
        return None
    return normalized[:match.end()], normalized[match.end():]
def replace_frontmatter_desc_keywords(content: str, optimized_desc: str | None,
                                       optimized_keywords: list[str],
                                       md_label: str = "",
                                       status_out: dict | None = None) -> str:
    content = normalize_newlines(normalize_text(content))
    optimized_keywords = frontmatter_keywords(optimized_keywords)
    if optimized_desc is not None:
        optimized_desc = normalize_text(optimized_desc)
    status: dict = status_out if isinstance(status_out, dict) else {}
    fm_match = _FRONTMATTER_BLOCK_PATTERN.match(content)
    if not fm_match:
        _log.warning(
            "replace_frontmatter_desc_keywords: %s 未找到 --- 界定的 "
            "frontmatter 块，description/keywords 写回未落盘", md_label)
        status["desc_written"] = False
        status["keywords_written"] = False
        return content
    fm_body = fm_match.group(1)
    if optimized_desc is None:
        n_desc = 0
    else:
        fm_body, n_desc = _replace_description_in_fm(
            fm_body, optimized_desc, md_label)
    n_replaced = 0
    if optimized_keywords:
        fm_body, n_replaced = _replace_keywords_in_fm(
            fm_body, optimized_keywords, md_label)
    if fm_body != fm_match.group(1):
        content = content[:fm_match.start(1)] + fm_body + content[fm_match.end(1):]
    status["desc_written"] = bool(n_desc)
    status["keywords_written"] = bool(n_replaced)
    return content
_FM_EMPTY_FIELD_KEYS = r"(?:depends_on|category|requires|compatibility)"
_FM_EMPTY_FIELD_TAIL = (
    r"(?=(?:\n(?:[ \t]*\n)*(?:---[ \t]*(?:\n|\Z)|[\w\"'][^\n:]*:|\Z))|\n?\Z)")
_PURIFY_RULES = (
    (r'\n## 版本历史.*?(?=\n## [^#]|\n# [^#]|\Z)', '', True),
    (r'\n## Version History.*?(?=\n## [^#]|\n# [^#]|\Z)', '', True),
    (r'\n## CHANGELOG.*?(?=\n## [^#]|\n# [^#]|\Z)', '', True),
    (r'\n## Changelog.*?(?=\n## [^#]|\n# [^#]|\Z)', '', True),
    (r'\n## 变更记录.*?(?=\n## [^#]|\n# [^#]|\Z)', '', True),
    (r'\n## 更新日志.*?(?=\n## [^#]|\n# [^#]|\Z)', '', True),
    (r'\n## 修订记录.*?(?=\n## [^#]|\n# [^#]|\Z)', '', True),
    (r'\n## 修改记录.*?(?=\n## [^#]|\n# [^#]|\Z)', '', True),
    (r'\n### 版本变更.*?(?=\n### [^#]|\n## [^#]|\Z)', '', True),
    (r'\n[-*]\s+v\d+\.\d+\.\d+.*?(?=\n)', '', False),
    (r'\n>\s+v\d+\.\d+\.\d+.*?(?=\n)', '', False),
    (r'\n> \*\*历史遗留\*\*.*?(?=\n[^>]|\Z)', '', True),
    (r'\n> \*\*已废弃\*\*.*?(?=\n[^>]|\Z)', '', True),
    (r'\n> \[已废弃\].*?(?=\n[^>]|\Z)', '', True),
    (r'\nv\d+\.\d+\.\d+\s*[：:].*?(?=\n)', '', False),
    (r'\n---\n\*[Gg]enerated by.*?\*\n?', '\n', False),
    (r'\n---\n\*[Aa]uto-generated by.*?\*\n?', '\n', False),
    (r'\n\*[Gg]enerated by .*?\*(?=\n)', '', False),
    (r'\n\*[Aa]uto-generated.*?\*(?=\n)', '', False),
    (r'\n---\n_[Gg]enerated .*?_(?=\n)', '', False),
    (r'\n_[Gg]enerated .*?_(?=\n)', '', False),
    (r'\n## 历史记录\s*\n\s*(?=\n)', '', False),
    (r'\n## 存档\s*\n\s*(?=\n)', '', False),
    (r'\n> \*\*注意\*\*：.*?历史.*?(?=\n)', '', False),
    (r'\nv\d+\.\d+\.\d+\s*(?:至|到)\s*v\d+\.\d+\.\d+.*?(?=\n|\Z)', '', False),
    (r'\n.*?\[CHANGELOG\.md\]\(CHANGELOG\.md\).*?(?=\n)', '', False),
    (r'\n.*?版本变更记录.*?CHANGELOG.*?(?=\n)', '', False),
    (r'\n\d{4}-\d{2}-\d{2}[\uff1a:]\s*.*?(?:修复|更新|新增|删除|移除|优化|清理|重构).*?(?=\n)', '', False),
    (r'\n.*?自\s*v\d+\.\d+\.\d+.*?变更.*?(?=\n)', '', False),
    (r'\n.*?since\s*v\d+\.\d+\.\d+.*?(?=\n)', '', False),
    (r'\n##\s*(?:变更|更新日志|修订记录|修改记录|历史|归档|Archive|Changelog).*?(?=\n##|\n#|\Z)', '', True),
    (r'\n---\s*\n\(.*?\)\s*$', '', False),
    (r'\n' + _FM_EMPTY_FIELD_KEYS + r':[ \t]*(?:\[\]|""|\'\')[ \t]*'
     + _FM_EMPTY_FIELD_TAIL, '', False),
    (r'\n' + _FM_EMPTY_FIELD_KEYS + r':[ \t]*'
     + _FM_EMPTY_FIELD_TAIL, '', False),
    (r'\n.*?拆分自.*?(?=\n)', '', False),
    (r'\n.*?v\d+\.\d+\.\d+\s*重构.*?(?=\n)', '', False),
    (r'\n注：.*?(?:排除|合并|待移除|待修复).*?(?=\n)', '', False),
    (r'\nv\d+\.\d+\.\d+[^\n]*?(?:重构|拆分|合并|移除|新增|修复|更新|删除|清理).*?(?=\n)', '', False),
    (r'\n来源:.*?(?=\n)', '', False),
    (r'\nSource:.*?(?=\n)', '', False),
    (r'\n##\s+\n(?=\n##|\n#|\Z)', '\n', False),
    (r'\n#+\s*合并自:.*?(?=\n)', '', False),
    (r'\n#+\s*Merged from:.*?(?=\n)', '', False),
    (r'\n#+\s*来源:.*?(?=\n)', '', False),
    (r'\n#+\s*Source:.*?(?=\n)', '', False),
    (r'\nv\d+\.\d+\.\d+\s*[：:—\-].*?(?=\n)', '', False),
    (r'\n源文件:.*?(?=\n)', '', False),
    (r'\n源:\s.*?(?=\n)', '', False),
    (r'\n.*?重构[：:]\s*.*?(?=\n)', '', False),
    (r'\n.*?\[已修复\].*?(?=\n)', '', False),
    (r'\n.*?Internal helper.*?(?=\n)', '', False),
    ((r'\n\d{4}-\d{2}-\d{2}[ \t]*[：:]?[ \t]*'
      r'(?:修复|更新|新增|删除|移除|优化|清理|重构|修正|调整|改进|升级|发布|变更|迁移|合并|拆分|废弃'
      r'|(?i:fix|update|add|remove|refactor|release|change|upgrade|migrat|merge|deprecat))'
      r'.*?(?=\n)'), '', False),
    (r'\nv\d+\.\d+\.\d+\s*\([^)]*\)[：:].*?(?=\n)', '', False),
    (r'\n.*?旧版[：:].*?(?=\n)', '', False),
    (r'\n.*?新版[：:].*?(?=\n)', '', False),
    (r'\n.*?与旧版.*?的区别.*?(?=\n)', '', False),
    (r'\n.*?(?:已迁移至|迁移到|已移至|migrated to|moved to).*?(?=\n)', '', False),
    (r'\n#+\s*(?:已迁移|迁移说明|Migration).*?(?=\n)', '', False),
    (r'\n.*?向后兼容.*?(?=\n)', '', False),
    (r'\n.*?兼容性说明.*?(?=\n)', '', False),
    (r'\n.*?过渡期.*?(?=\n)', '', False),
    (r'\n.*?过渡版本.*?(?=\n)', '', False),
    (r'\n.*?(?:将在下个版本|计划在|将于).*?(?:移除|删除|废弃).*?(?=\n)', '', False),
    (r'\n.*?TODO\s*(?:旧版|移除|删除|废弃).*?(?=\n)', '', False),
    (r'\nv\d+\.\d+\.\d+\s*(?:根本性)?(?:改造|变更|重构)[^\n]*?(?=\n)', '', False),
    (r'\n{3,}', '\n\n', False),
)
def _apply_purify_rules_to_prose(text: str) -> str:
    anchored = bool(text) and not text.startswith("\n")
    if anchored:
        text = "\n" + text
    for pattern, repl, dotall in _PURIFY_RULES:
        text = re.sub(pattern, repl, text, flags=re.DOTALL if dotall else 0)
    if anchored and text.startswith("\n"):
        text = text[1:]
    return text
def _purify_prose(text: str) -> str:
    if not text:
        return text
    out: list[str] = []
    buf: list[str] = []
    in_fence = False
    fence_char = ""
    fence_len = 0
    for line in text.splitlines(keepends=True):
        in_fence, fence_char, fence_len, line_kind = scan_fence_state(
            in_fence, fence_char, fence_len, line)
        if line_kind == "open":
            if buf:
                out.append(_apply_purify_rules_to_prose("".join(buf)))
                buf = []
            out.append(line)
        elif in_fence or line_kind == "close":
            out.append(line)
        else:
            buf.append(line)
    if buf:
        out.append(_apply_purify_rules_to_prose("".join(buf)))
    return "".join(out)
def _apply_purify_rules(content: str) -> str:
    text = normalize_newlines(normalize_text(content))
    match = _FRONTMATTER_BLOCK_PATTERN.match(text)
    if match is None:
        opening_end = _frontmatter_opening_end(
            text, _frontmatter_leading_blank_end(text))
        if opening_end is not None:
            _log.warning(
                "purify_skill_md: frontmatter 未闭合，跳过净化以保护原文")
            return text
        return _purify_prose(text)
    return text[:match.end()] + _purify_prose(text[match.end():])
def update_frontmatter_desc_keywords(
    skill_md_path: str,
    optimized_desc: str | None,
    optimized_keywords: list[str] | None,
    *,
    md_label: str = "",
) -> bool:
    try:
        path = Path(skill_md_path)
    except (TypeError, ValueError) as exc:
        log_swallowed(__name__, exc,
                      context=f"update_frontmatter_desc_keywords:path:{type(exc).__name__}")
        return False
    if not path.exists():
        return False
    label = md_label or str(path)
    description = (None if optimized_desc is None
                   else normalize_text(optimized_desc))
    keywords = frontmatter_keywords(optimized_keywords)
    try:
        raw = path.read_bytes()
        content = raw.decode("utf-8-sig").replace("\r\n", "\n").replace("\r", "\n")
        status: dict[str, Any] = {}
        updated = replace_frontmatter_desc_keywords(
            content, description, keywords,
            md_label=label, status_out=status)
        desc_required = description is not None
        keywords_required = bool(keywords)
        if not (desc_required or keywords_required):
            return False
        if ((desc_required and not status.get("desc_written"))
                or (keywords_required and not status.get("keywords_written"))):
            _log.warning(
                "update_frontmatter_desc_keywords: %s 请求字段未全部匹配，"
                "取消整体写回以避免部分成功", label)
            return False
        write_text_preserving_form(path, updated, raw)
        return True
    except Exception as exc:  # noqa: BLE001 — 写回失败降级为 False，由调用方告警
        log_swallowed(__name__, exc,
                      context=f"update_frontmatter_desc_keywords:{type(exc).__name__}")
        return False
def purify_skill_md(skill_md_path: str) -> None:
    try:
        raw = Path(skill_md_path).read_bytes()
        content = raw.decode("utf-8-sig")
    except (OSError, UnicodeDecodeError, TypeError, ValueError) as e:
        _log.warning("purify_skill_md: 读取SKILL.md失败: %s: %s", skill_md_path, e)
        return
    normalized = normalize_newlines(content)
    purified = _apply_purify_rules(normalized)
    if purified == normalized:
        return
    try:
        write_text_preserving_form(skill_md_path, purified, raw)
    except (OSError, RuntimeError) as e:
        _log.warning("purify_skill_md: 写回SKILL.md失败: %s: %s", skill_md_path, e)
_FM_CLOSE_LINE_PAT = re.compile(r"\n---[ \t]*(?=\r?\n|$)")
def _frontmatter_span_norm(content: str) -> tuple[str, int, int, int] | None:
    view = normalize_text(content).removeprefix("\ufeff")
    opening_end = _frontmatter_opening_end(
        view, _frontmatter_leading_blank_end(view))
    if opening_end is None:
        return None
    close = _FM_CLOSE_LINE_PAT.search(view, max(0, opening_end - 1))
    if close is None:
        return None
    return view, opening_end, close.start(), close.end()
def parse_frontmatter(content: str) -> tuple[str | None, str]:
    text = normalize_newlines(normalize_text(content))
    located = _frontmatter_span_norm(text)
    if located is None:
        return None, text.removeprefix("\ufeff")
    view, opening_end, close_start, close_end = located
    return view[opening_end:close_start + 1], view[close_end:]
def _yaml_safe_load(fm_text: str) -> tuple[dict | None, str, str]:
    if _yaml is None:
        return None, "no_yaml", ""
    try:
        meta = _yaml.safe_load(fm_text)
    except Exception as exc:  # noqa: BLE001 — 解析失败回退简单键值解析
        _log.debug("[Quality] PyYAML 解析失败，回退简单解析", exc_info=True)
        return None, "parse_error", f"{type(exc).__name__}: {exc}"
    if not isinstance(meta, dict):
        return None, "not_dict", ""
    return meta, "", ""
def _canonical_keywords_value(fm_text: str, value: Any) -> list[str]:
    if isinstance(value, str) and (
            _find_field_line(fm_text, "keywords") is not None
            or _find_field_line(fm_text, "tags") is not None):
        return _parse_keywords(fm_text)
    return frontmatter_keywords(value)


def _canonical_meta_fields(
    meta: dict[str, Any], fm_text: str, *, safe_loaded: bool = False,
) -> dict[str, Any]:
    result = dict(meta)
    significant = _first_significant_line(fm_text)
    if safe_loaded or (significant is not None and significant[2].startswith("{")):
        if "name" in meta:
            result["name"] = _normalize_scalar_field(meta["name"])
        if "description" in meta:
            result["description"] = normalize_description_field(meta["description"])
        if "version" in meta:
            value = meta["version"]
            result["version"] = (
                "" if value is None or isinstance(value, (bool,) + _CONTAINER_FORMS)
                else normalize_fm_scalar(value).strip())
        if "keywords" in meta:
            raw_keywords = meta["keywords"]
            if raw_keywords is None and "tags" in meta:
                raw_keywords = meta["tags"]
            result["keywords"] = _canonical_keywords_value(fm_text, raw_keywords)
        elif "tags" in meta:
            result["tags"] = _canonical_keywords_value(fm_text, meta["tags"])
        return result
    scan = _FrontmatterScan()
    for line in fm_text.splitlines():
        scan.consume_line(line)
    _keys, name, description = scan.finish()
    if _find_field_line(fm_text, "name") is not None:
        result["name"] = _normalize_scalar_field(name)
    if _find_field_line(fm_text, "description") is not None:
        result["description"] = normalize_description_field(description)
    if _find_field_line(fm_text, "version") is not None:
        result["version"] = scan.version
    if _find_field_line(fm_text, "keywords") is not None:
        result["keywords"] = _parse_keywords(fm_text)
    elif _find_field_line(fm_text, "tags") is not None:
        result["tags"] = _parse_keywords(fm_text)
    return result
def parse_frontmatter_dict(content: str) -> dict[str, Any]:
    located = _frontmatter_span_norm(normalize_newlines(normalize_text(content)))
    if located is None:
        return {}
    view, opening_end, close_start, _close_end = located
    fm_text = view[opening_end:close_start].strip()
    parsed, _reason, _detail = _yaml_safe_load(fm_text)
    if parsed is not None:
        return _canonical_meta_fields(parsed, fm_text, safe_loaded=True)
    meta = {}
    for line in fm_text.splitlines():
        if not line.strip() or line[:1] in (" ", "\t", "#"):
            continue
        key_raw, sep, value = line.partition(":")
        if not sep:
            continue
        key = unquote_yaml_scalar(key_raw.strip())
        if key:
            meta[key] = unquote_yaml_scalar(strip_inline_comment(value))
    return _canonical_meta_fields(meta, fm_text)
def skill_md_verdict(content: str) -> tuple[str, str]:
    text = normalize_text(content)
    section = _frontmatter_section(text)
    if section is not None:
        if _yaml is None:
            return "warn", "未安装 PyYAML，无法严格校验 frontmatter"
        _meta, reason, detail = _yaml_safe_load(section[1])
        if reason == "parse_error":
            return "warn", f"frontmatter YAML 解析失败: {detail}"
        if reason == "not_dict":
            return "warn", "frontmatter 必须是 YAML 映射"
    meta = parse_frontmatter_dict(text)
    fm_lines = section[1].splitlines() if section else []
    def _field_has_value(key: str) -> bool:
        if key not in meta:
            return (bool(fm_lines) and frontmatter_value_present(
                fm_lines, key, scalar_only=key in ("name", "version")))
        value = meta[key]
        if isinstance(value, str):
            if value.strip() and not _is_block_scalar_head(value):
                return _yaml_text_has_value(value)
        elif value is not None:
            if key == "description":
                if normalize_description_field(value).strip():
                    return True
            elif key in ("keywords", "tags"):
                if frontmatter_keywords(value):
                    return True
            elif key == "name":
                if _normalize_scalar_field(value):
                    return True
            else:
                return True
        return False
    if not _field_has_value("name") or not _field_has_value("description"):
        return "warn", "SKILL.md 缺少 name 或 description"
    if not (_field_has_value("keywords") or _field_has_value("tags")):
        return "warn", "缺少 keywords"
    return "pass", ""
def locate_frontmatter(content: str) -> tuple[str | None, int | None]:
    if not isinstance(content, str):
        return None, None
    normalized = normalize_newlines(content).removeprefix("\ufeff")
    fm_text, body = parse_frontmatter(normalized)
    if fm_text is None:
        return None, None
    return fm_text, len(normalized) - len(body.lstrip("\r\n"))
def load_frontmatter(fm_text: str | None) -> tuple[dict | None, str, str]:
    if fm_text is None:
        return None, "missing", ""
    return _yaml_safe_load(fm_text)
def normalize_fm_scalar(value) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    try:
        return str(value)
    except Exception as _e:  # noqa: BLE001 — 病态 __str__ 与解析降级同口径归空
        log_swallowed(__name__, _e,
                      context=f'normalize_fm_scalar:{type(_e).__name__}')
        return ""
def _normalize_scalar_field(value: Any) -> str:
    if isinstance(value, (bool, _CONTAINER_FORMS)):
        return ""
    return _name_text(normalize_fm_scalar(value))
def extract_frontmatter_fields(content: str) -> tuple[str, str, list[str], int | None]:
    fm_text, body_start = locate_frontmatter(content)
    if fm_text is None:
        return "", "", [], None
    fm, reason, detail = load_frontmatter(fm_text)
    if reason == "no_yaml":
        _log.warning("[SkillDoc] PyYAML 未安装，frontmatter 字段提取降级为空"
                     "（补装：python -m pip install pyyaml）")
        return "", "", [], body_start
    if reason == "parse_error":
        _log.warning("[SkillDoc] frontmatter YAML 解析失败，"
                     "字段按空处理（根因由 UV-001 透出）: %s", detail)
        return "", "", [], body_start
    if reason == "not_dict":
        return "", "", [], body_start
    meta = _canonical_meta_fields(fm, fm_text, safe_loaded=True)
    keywords = meta["keywords"] if "keywords" in meta else meta.get("tags", [])
    return (meta.get("name", ""), meta.get("description", ""),
            keywords or [], body_start)
_CONTAINER_FORMS = (Mapping, list, tuple, set, frozenset)
def frontmatter_keywords(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return _split_keyword_scalar_text(value)
    if isinstance(value, (list, tuple)):
        sequence: Any = value
    elif isinstance(value, (set, frozenset)):
        sequence = sorted(value, key=str)
    else:
        return []
    items: list[str] = []
    for item in sequence:
        if isinstance(item, str):
            items.extend(line.strip() for line in item.splitlines()
                         if line.strip())
    return items
def normalize_description_field(raw: Any) -> str:
    if raw is None or isinstance(raw, bool):
        return ""
    if isinstance(raw, (list, tuple)):
        return "\n".join(
            text for x in raw
            if x is not None and not isinstance(x, (bool,) + _CONTAINER_FORMS)
            and (text := normalize_fm_scalar(x))).rstrip("\n")
    if isinstance(raw, _CONTAINER_FORMS):
        _log.debug("frontmatter description 容器形态按空处理: %s",
                   type(raw).__name__)
        return ""
    return normalize_fm_scalar(raw).rstrip("\n")
def _is_dash_sequence_item(text: str) -> bool:
    return text == '-' or text.startswith(('- ', '-\t'))
def _frontmatter_section(content: str) -> tuple[str, str] | None:
    located = _frontmatter_span_norm(
        normalize_newlines(normalize_text(content)))
    if located is None:
        return None
    view, opening_end, close_start, _close_end = located
    return view, view[opening_end:close_start]
def extract_description_lenient(content: str) -> str:
    text = normalize_newlines(normalize_text(content))
    section = _frontmatter_section(text)
    if section is None:
        return ""
    _view, frontmatter = section
    return parse_frontmatter_description(frontmatter).value
_PLAIN_SCALAR_UNSAFE_INITIALS = frozenset(",[]{}#&*!|>'\"%@`")
def _yaml_text_has_value(value: str) -> bool:
    text = value.strip()
    if not text:
        return False
    if len(text) >= 2 and text[0] == text[-1] and text[0] in ("'", '"'):
        return bool(text[1:-1].strip())
    compact = re.sub(r"[ \t]+", "", text)
    if compact in ("[]", "{}"):
        return False
    return not _is_empty_yaml_scalar(text)
def _block_body_has_value(
    fm_lines: list[str], start: int, *, key: str,
    scalar_only: bool = False, block_scalar: bool = False,
) -> bool:
    for line in fm_lines[start:]:
        stripped = line.strip()
        if not stripped:
            continue
        indented = line[:1] in (" ", "\t")
        if not indented:
            if stripped.startswith("#"):
                continue
            if block_scalar:
                return False
        elif block_scalar:
            return True
        if stripped.startswith("#"):
            continue
        if _is_dash_sequence_item(stripped):
            if scalar_only:
                return False
            raw_item = strip_inline_comment(stripped[1:].strip())
            if (raw_item[:1] not in _QUOTE_CHARS
                    and raw_item.strip().lower() in _YAML_BOOL_NULL_TOKENS):
                continue
            value = (_description_sequence_item(raw_item)
                     if key == "description" else _scalar_item(raw_item))
            if value.strip():
                return True
            continue
        if not indented:
            return False
        if stripped.startswith(("[", "{")):
            if scalar_only or stripped.startswith("{"):
                return False
            if key == "description":
                return bool(_description_scalar(stripped).strip())
            if key in ("keywords", "tags"):
                return bool(_parse_flow_scalars(stripped, 1))
            return False
        text = _plain_scalar_text(line)
        if text is None:
            return False
        if ((scalar_only or key in ("name", "description", "version",
                                    "keywords", "tags"))
                and text.strip().lower() in _YAML_BOOL_NULL_TOKENS):
            return False
        return _yaml_text_has_value(text)
    return False
def frontmatter_value_present(fm_lines: list[str], key: str, *,
                              scalar_only: bool = False) -> bool:
    if not isinstance(fm_lines, (list, tuple)) or not isinstance(key, str):
        return False
    pattern = _field_line_re(key)
    anchors = _field_line_numbers(fm_lines, key)
    for idx in reversed(anchors):
        head = pattern.match(fm_lines[idx])
        if head is None:
            continue
        field_lines = list(fm_lines[idx:])
        if key in ("keywords", "tags"):
            return bool(_parse_keyword_field("\n".join(field_lines), key))
        if key in ("name", "description", "version"):
            scan = _FrontmatterScan()
            for field_line in field_lines:
                scan.consume_line(field_line)
            _keys, name, description = scan.finish()
            value = {"name": name, "description": description,
                     "version": scan.version}[key]
            return bool(value.strip())
        value = strip_inline_comment(head.group(1))
        if _is_block_scalar_head(value):
            return _block_body_has_value(
                fm_lines, idx + 1, key=key, block_scalar=True)
        if value:
            if scalar_only and (
                    value.lstrip().startswith(("[", "{"))
                    or value.strip().lower() in _YAML_BOOL_NULL_TOKENS):
                return False
            return _yaml_text_has_value(value)
        return _block_body_has_value(
            fm_lines, idx + 1, key=key, scalar_only=scalar_only)
    return False
def _plain_scalar_text(line: str) -> str | None:
    stripped = line.strip()
    if not stripped:
        return None
    head, nxt = stripped[0], stripped[1:2]
    if head in "-?:":
        return None if nxt in ("", " ", "\t") else stripped
    if head in _PLAIN_SCALAR_UNSAFE_INITIALS or ": " in stripped:
        return None
    if stripped.endswith(":"):
        return None
    return strip_inline_comment(stripped) or None
def _description_line_index(lines: list[str]) -> int | None:
    first = 0
    while first < len(lines) and not lines[first].strip():
        first += 1
    if first >= len(lines):
        return None
    if not is_frontmatter_fence(
            lines[first].lstrip("\ufeff").rstrip("\r\n")):
        return None
    end = None
    for index in range(first + 1, len(lines)):
        if is_frontmatter_fence(lines[index].rstrip("\r\n")):
            end = index
            break
    if end is None:
        return None
    anchors = _field_line_numbers(lines[first + 1:end], "description")
    if not anchors:
        return None
    index = first + 1 + anchors[-1]
    return (index if is_field_key_line(
        lines[index].rstrip("\r\n"), "description") else None)
def replace_frontmatter_description(content: str, safe_desc: str) -> str:
    if not isinstance(content, str):
        return content
    if not isinstance(safe_desc, str):
        safe_desc = safe_text(safe_desc)
    lines = content.splitlines(keepends=True)
    index = _description_line_index(lines)
    if index is None:
        return content
    eol = lines[index][len(lines[index].rstrip("\r\n")):] or "\n"
    value_end = _field_value_end(lines, index, "description")
    if value_end is None:
        return content
    replacement = eol.join(normalize_newlines(safe_desc).split("\n"))
    suffix = "".join(lines[value_end:])
    if suffix and not replacement.endswith(("\n", "\r")):
        replacement += eol
    return "".join(lines[:index]) + replacement + suffix
def insert_frontmatter_description(head: str, desc: str) -> str:
    head = normalize_text(head)
    lines = head.split("\n")
    line = yaml_safe_desc_line(desc)
    anchors = [idx for idx in _field_line_numbers(lines, "name")
               if is_field_key_line(lines[idx].rstrip("\r"), "name")]
    if anchors:
        value_end = _field_value_end(lines, anchors[-1], "name")
        if value_end is None:
            return head
        anchor = value_end - 1
    else:
        anchor = next((idx for idx, item in enumerate(lines)
                       if is_frontmatter_fence(item.lstrip("\ufeff"))), 0)
    eol = "\r" if lines[anchor].endswith("\r") else ""
    if eol:
        line = line.replace("\n", "\r\n") + eol
    lines.insert(anchor + 1, line)
    return "\n".join(lines)
def read_frontmatter_skill_name(content: str, fallback: str) -> str:
    fallback = normalize_text(fallback)
    section = _frontmatter_section(content)
    if section is None:
        return fallback
    _view, frontmatter = section
    _keys, parsed_name, _description = parse_frontmatter_fields(
        frontmatter.splitlines())
    return parsed_name.strip() or fallback
def extract_description(content_or_path: str | Path) -> str:
    if isinstance(content_or_path, Path):
        try:
            text = read_skill_text_interpreter_encoding(content_or_path)
        except (OSError, UnicodeDecodeError, SyntaxError) as exc:
            _log.warning("[Quality] Text read failed: %s", exc)
            raise
    else:
        text = normalize_text(content_or_path)
    return extract_description_lenient(text)
def read_meta_degraded(skill_path: Path | str, caller: str) -> dict[str, Any]:
    try:
        candidate = _as_path(skill_path)
    except (TypeError, ValueError) as exc:
        _log.warning("%s: 技能路径非法(%r)，降级为空元数据: %s",
                     caller, skill_path, exc)
        return parse_skill_md_text("")
    try:
        return read_skill_md(candidate)
    except (OSError, UnicodeDecodeError) as exc:
        _log.warning(
            "%s: 读取 %s/SKILL.md 失败，降级为空元数据: %s",
            caller, candidate, exc
        )
        return parse_skill_md_text("", default_name=candidate.name)
_DESC_MIN_REPLACE_CHARS = 10
DEFAULT_SKILL_VERSION = "0.0.1"
_TODO_PLACEHOLDER_RE = re.compile(r'^\s*["\']?\s*\[\s*TODO\b', re.IGNORECASE)
def _create_missing_frontmatter(content: str, skill_name: str,
                                description: str, version: str,
                                logs: list[str]) -> str | None:
    if not skill_name:
        return None
    safe_desc = yaml_safe_desc_line(description or '技能功能描述')
    fm = (f"---\nname: {yaml_safe_quote(skill_name)}\n{safe_desc}\n"
          f"version: {yaml_safe_quote(version)}\n---\n\n")
    logs.append("已自动创建 frontmatter（缺少起始标记）")
    return fm + content
def _handle_missing_frontmatter(content: str, skill_name: str,
                                 description: str, version: str,
                                 logs: list[str]) -> tuple[str, list[str]] | None:
    opening_end = _frontmatter_opening_end(
        content, _frontmatter_leading_blank_end(content))
    if opening_end is not None:
        return None
    created = _create_missing_frontmatter(content, skill_name,
                                          description, version, logs)
    if created is None:
        return content, ["无法自动修复: 缺少 frontmatter 且无 skill_name 参数"]
    emit_fix_logs(logs, _log, prefix="frontmatter fixer",
                  warn_prefixes=("无法",))
    return created, logs
def _normalize_frontmatter_inputs(content: str, skill_name: str,
                                   description: str,
                                   version: str) -> tuple[str, str, str, str]:
    content = normalize_newlines(
        normalize_text(content)).removeprefix("\ufeff")
    return (content, normalize_text(skill_name).strip(),
            normalize_text(description),
            normalize_text(version).strip() or DEFAULT_SKILL_VERSION)
def ensure_complete_frontmatter(content: str, skill_name: str = "",
                                 description: str = "",
                                 version: str = DEFAULT_SKILL_VERSION) -> tuple[str, list[str]]:
    logs = []
    content, skill_name, description, version = _normalize_frontmatter_inputs(
        content, skill_name, description, version)
    result = content
    early = _handle_missing_frontmatter(
        content, skill_name, description, version, logs)
    if early is not None:
        return early
    parts = split_frontmatter(content)
    if len(parts) < 3:
        logs.append("无法自动修复: frontmatter 格式不完整")
        emit_fix_logs(logs, _log, prefix="frontmatter fixer",
                      warn_prefixes=("无法",))
        return content, logs
    fm = parts[1]
    shape_error = _root_mapping_shape_error(fm)
    if shape_error:
        logs.append(f"无法自动修复: {shape_error}，已拒绝改写以避免破坏原文")
        emit_fix_logs(logs, _log, prefix="frontmatter fixer",
                      warn_prefixes=("无法",))
        return content, logs
    # 根级 flow mapping 对 YAML 合法，但字段锚点只识别块映射键；
    # 不先归一就会在 flow 行前后插入块字段，写出不可解析的 YAML。
    fm, flow_state = _normalize_root_flow_frontmatter(fm)
    if flow_state == "unsupported":
        logs.append(
            "无法自动修复: 根级 flow frontmatter 无法安全解析/序列化，"
            "已拒绝改写以避免破坏原文")
        emit_fix_logs(logs, _log, prefix="frontmatter fixer",
                      warn_prefixes=("无法",))
        return content, logs
    if flow_state == "normalized":
        logs.append("已归一根级 flow frontmatter 为块格式（保留全部字段）")
    # 整体缩进的 frontmatter 对 PyYAML 合法，但字段锚点只识别顶格键；
    # 不先归一就会在缩进块前后重复补 name/description，写出不可解析的 YAML。
    fm, indent_normalized = _normalize_frontmatter_body_indent(fm)
    if indent_normalized:
        logs.append("已归一缩进式 frontmatter（字段统一顶格）")
    fm, _name_modified = _ensure_name_field(fm, skill_name, logs)
    if not fm.endswith("\n"):
        fm += "\n"
    fm, _desc_modified = _ensure_description_field(fm, description, logs)
    fm, _ver_modified = _ensure_version_field(fm, version, logs)
    if (_name_modified or _desc_modified or _ver_modified
            or indent_normalized or flow_state == "normalized"):
        result = f"{parts[0]}---\n{fm}---{parts[2]}"
    emit_fix_logs(logs, _log, prefix="frontmatter fixer",
                  warn_prefixes=("无法",))
    return result, logs
def _ensure_name_field(fm: str, skill_name: str,
                       logs: list[str]) -> tuple[str, bool]:
    if not skill_name:
        return fm, False
    if _find_field_line(fm, "name") is None:
        fm = f"name: {yaml_safe_quote(skill_name)}\n{fm}"
        logs.append(f"已补全 name 字段: '{skill_name}'")
        return fm, True
    if parse_frontmatter_fields(fm.splitlines())[1]:
        return fm, False
    fm, _replaced = _replace_field_block(
        fm, "name", f"name: {yaml_safe_quote(skill_name)}\n")
    if not _replaced:
        logs.append("无法自动修复: name 字段行未匹配")
        return fm, False
    logs.append(f"已补全空白 name 字段: '{skill_name}'")
    return fm, True
def _ensure_version_field(fm: str, version: str,
                          logs: list[str]) -> tuple[str, bool]:
    match = _find_field_line(fm, "version")
    if match is None:
        fm = f"{fm}version: {yaml_safe_quote(version)}\n"
        logs.append(f"已补全 version 字段: '{version}'")
        return fm, True
    if frontmatter_value_present(fm.splitlines(), "version", scalar_only=True):
        return fm, False
    fm, _replaced = _replace_field_block(
        fm, "version", f"version: {yaml_safe_quote(version)}\n")
    if not _replaced:
        logs.append("无法自动修复: version 字段行未匹配")
        return fm, False
    logs.append(f"已补全空白 version 字段: '{version}'")
    return fm, True
def _replace_description_field(fm: str, description: str,
                               logs: list[str], message: str) -> tuple[str, bool]:
    updated, replaced = _replace_field_block(
        fm, "description", yaml_safe_desc_line(description) + "\n")
    if not replaced:
        _log.warning("frontmatter fixer: %s 未匹配到字段行，保持原值", message)
        return fm, False
    logs.append(message)
    return updated, True
def _ensure_description_field(fm: str, description: str,
                              logs: list[str]) -> tuple[str, bool]:
    has_desc = _find_field_line(fm, "description") is not None
    if not has_desc:
        if not description:
            return fm, False
        fm = f"{fm}{yaml_safe_desc_line(description)}\n"
        logs.append("已补全 description 字段")
        return fm, True
    if not description:
        return fm, False
    desc_text = parse_frontmatter_description(fm).value
    if _TODO_PLACEHOLDER_RE.match(desc_text):
        return _replace_description_field(
            fm, description, logs, "已替换 TODO 占位 description")
    if len(desc_text) < _DESC_MIN_REPLACE_CHARS:
        candidate = description.strip()
        if len(candidate) > len(desc_text):
            return _replace_description_field(
                fm, description, logs,
                f"description 过短({len(desc_text)}字符)，已替换")
        logs.append(
            f"无法自动修复: description 过短({len(desc_text)}字符)，"
            f"替换文本仅 {len(candidate)} 字符未更长，保持原值")
        return fm, False
    return fm, False
def render_minimal_skill_md(
        base_name: str, description: str | None = None,
        version: str = DEFAULT_SKILL_VERSION) -> str:
    base_name = normalize_text(base_name)
    version = normalize_text(version).strip() or DEFAULT_SKILL_VERSION
    desc_line = ("description: 技能功能描述" if description is None
                 else yaml_safe_desc_line(description))
    return (f"---\nname: {yaml_safe_quote(base_name)}\n{desc_line}\n"
            f"version: {yaml_safe_quote(version)}\n---\n\n# {base_name}\n")
def parse_frontmatter_text(content: str) -> tuple[str, str]:
    content = normalize_text(content).removeprefix("\ufeff")
    if not content or not content.lstrip().startswith("---"):
        return "", ""
    parts = split_frontmatter(content)
    if len(parts) < 3:
        return "", ""
    fm = parts[1]
    _keys, name, description = parse_frontmatter_fields(fm.splitlines())
    return name, description
def detect_doc_profile_text(content: str) -> str:
    normalized = normalize_newlines(normalize_text(content)).removeprefix("\ufeff")
    _fm_text, body_start = locate_frontmatter(normalized)
    body = normalized if body_start is None else normalized[body_start:]
    return detect_doc_profile(None, body)



# ---- frontmatter 缩进归一与定点写回 ----
_CTRL_TO_SPACE_TABLE = dict.fromkeys(
    [*range(0x09), 0x0B, 0x0C, *range(0x0E, 0x20), *range(0x7F, 0xA0)], " ")


def _frontmatter_body_indent(lines: list[str]) -> int:
    """返回 frontmatter 正文首个有效行的缩进宽度。"""
    for line in lines:
        if not line.strip() or line.lstrip(" \t").startswith("#"):
            continue
        return len(line) - len(line.lstrip(" \t"))
    return 0


def _dedent_frontmatter_line(line: str, indent: int) -> str:
    """按给定缩进宽度去缩进，不足时原样返回。"""
    if len(line) - len(line.lstrip(" \t")) >= indent:
        return line[indent:]
    return line


def _normalize_frontmatter_body_indent(fm: str) -> tuple[str, bool]:
    """把整体缩进的 frontmatter 正文按首个有效行宽度去缩进；未缩进时原样返回。"""
    lines = fm.split("\n")
    base_indent = _frontmatter_body_indent(lines)
    if not base_indent:
        return fm, False
    return "\n".join(
        _dedent_frontmatter_line(line, base_indent) for line in lines), True


def _root_mapping_shape_error(fm: str) -> str:
    """PyYAML 能解析但根节点不是映射时返回拒绝理由；解析失败交由既有修复链处理。"""
    if not fm.strip():
        return ""
    if _yaml is None:
        return _fallback_root_mapping_shape_error(fm)
    parsed, reason, _detail = _yaml_safe_load(fm.strip())
    if reason == "parse_error":
        return ""
    if isinstance(parsed, dict):
        return ""
    if parsed is None:
        return ("" if _first_significant_line(fm) is None else
                "frontmatter 根节点不是键值映射（仅支持映射）")
    return f"frontmatter 根节点是 {type(parsed).__name__}，不是键值映射"


_NON_MAPPING_ROOT_REASON = "frontmatter 根节点不是键值映射（仅支持映射）"


def _fallback_root_mapping_shape_error(fm: str) -> str:
    """无 PyYAML 时的保守形态判定，口径与 PyYAML 路径对齐：
    首个有效行是块/流序列项，或全文没有任何顶层键且不是 flow 映射，均视为非映射，
    拒绝改写以免在序列/标量前插入字段写出不可解析的 YAML。"""
    found = _first_significant_line(fm)
    if found is None:
        return ""
    head = found[2].strip()
    if head.startswith("[") or re.match(r"-(?:[ \t]|$)", head):
        return _NON_MAPPING_ROOT_REASON
    keys, _name, _description = parse_frontmatter_fields(fm.splitlines())
    if keys or head.startswith("{"):
        return ""
    return _NON_MAPPING_ROOT_REASON


def _normalize_root_flow_frontmatter(fm: str) -> tuple[str, str]:
    """把根级 flow mapping 归一为块格式；无法安全解析/序列化时返回 unsupported。"""
    if not _is_root_flow_mapping(fm):
        return fm, "none"
    parsed, _reason, _detail = _yaml_safe_load(fm.strip())
    if not isinstance(parsed, dict) or _yaml is None:
        return fm, "unsupported"
    if not parsed:
        return "", "normalized"
    try:
        dumped = _yaml.safe_dump(
            parsed, allow_unicode=True, sort_keys=False,
            default_flow_style=False, width=10 ** 9)
    except Exception as exc:  # noqa: BLE001 — 任意不可序列化值均拒绝改写
        _log.warning(
            "frontmatter fixer: 根级 flow frontmatter 无法序列化，拒绝改写: %s",
            exc)
        return fm, "unsupported"
    return dumped if dumped.endswith("\n") else dumped + "\n", "normalized"


def _yaml_field_indent(line: str) -> int | None:
    """识别顶层 YAML 字段行的缩进宽度，非字段行返回 None。"""
    match = re.match(r"^[ \t]*[\w\-'\"][^\n:]*:", line)
    if match is None:
        return None
    return len(line) - len(line.lstrip(" \t"))


def _is_desc_field_line(line: str, idx: int, end_idx: int) -> bool:
    """判断该行是否为 frontmatter 内的 description 顶层字段行。"""
    return 0 < idx < end_idx and is_field_key_line(line, "description")


def _scan_quoted_end(text: str, start: int, quote: str) -> int | None:
    """从 start 起扫描引号标量终点，支持 YAML 单引号双写转义。"""
    idx = start
    total = len(text)
    while idx < total:
        ch = text[idx]
        if quote == '"' and ch == "\\":
            idx += 2
            continue
        if ch == quote:
            if quote == "'" and text[idx + 1:idx + 2] == "'":
                idx += 2
                continue
            return idx + 1
        idx += 1
    return None


def _skip_indented_body(lines: list[str], start: int, end_idx: int) -> int:
    """跳过块标量的缩进行与空行，返回下一个顶层行下标。"""
    idx = start
    while idx < end_idx:
        line = lines[idx]
        if not line.strip() or line[:1] in (" ", "\t"):
            idx += 1
            continue
        break
    return idx


def _description_body_end(lines: list[str], idx: int,
                          end_idx: int) -> int | None:
    """求 description 字段值体的结束行；引号未闭合时返回 None 以拒绝写回。"""
    line = lines[idx]
    raw_value = line.split(":", 1)[1]
    value = strip_inline_comment(raw_value).strip()
    if not value:
        return _field_value_end(lines[:end_idx], idx, "description")
    if value in BLOCK_SCALAR_INDICATORS:
        return _skip_indented_body(lines, idx + 1, end_idx)
    quote = value[0]
    if quote in _QUOTE_CHARS:
        leading = len(raw_value) - len(raw_value.lstrip(" \t"))
        quote_col = len(line) - len(raw_value) + leading
        text = "\n".join(lines[idx:end_idx])
        end = _scan_quoted_end(text, quote_col + 1, quote)
        if end is None:
            return None
        return min(idx + text[:end].count("\n") + 1, end_idx)
    key_indent = _yaml_field_indent(line)
    pos = idx + 1
    last_content = pos
    while pos < end_idx:
        candidate = lines[pos]
        if not candidate.strip():
            pos += 1
            continue
        candidate_indent = _yaml_field_indent(candidate)
        if (candidate_indent is not None and key_indent is not None
                and candidate_indent <= key_indent):
            break
        if candidate[:1] not in (" ", "\t"):
            break
        pos += 1
        last_content = pos
    return last_content


def _replace_desc_lines(lines: list[str], endings: list[str],
                        new_line: str, end_idx: int
                        ) -> tuple[list[str], list[str]] | None:
    """整体替换 description 字段（含块标量/多行值体），缺失时按位置插入。"""
    new_lines: list[str] = []
    new_endings: list[str] = []
    replaced = False
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        ending = endings[idx] if idx < len(endings) else ""
        if _is_desc_field_line(line, idx, end_idx):
            stop = _description_body_end(lines, idx, end_idx)
            if stop is None:
                _log.warning(
                    "[best_practices] description 引号标量未闭合，拒绝写回以免丢字段")
                return None
            if not replaced:
                new_lines.append(new_line)
                new_endings.append(ending)
                replaced = True
            idx = max(stop, idx + 1)
            continue
        new_lines.append(line)
        new_endings.append(ending)
        idx += 1
    if not replaced:
        if not 0 < end_idx < len(new_lines):
            return None
        ending = (new_endings[end_idx - 1] or new_endings[end_idx]
                  or "\n")
        new_lines.insert(end_idx, new_line)
        new_endings.insert(end_idx, ending)
    return new_lines, new_endings


def _indented_frontmatter(text: str) -> tuple[list[str], list[str], int] | None:
    """把整体缩进的 frontmatter 归一为顶格，返回行/行尾与正文结束下标。"""
    lines, endings = _split_keep_endings(text)
    first = 0
    while first < len(lines) and not lines[first].strip():
        first += 1
    if (len(lines) - first < 3
            or not is_frontmatter_fence(
                lines[first].removeprefix("\ufeff"))
            or not any(is_frontmatter_fence(line)
                       for line in lines[first + 1:])):
        return None
    end_idx = next(index for index in range(first + 1, len(lines))
                   if is_frontmatter_fence(lines[index]))
    body_lines = lines[first + 1:end_idx]
    base_indent = _frontmatter_body_indent(body_lines)
    if not base_indent:
        return None
    normalized_lines = lines[:first + 1]
    normalized_lines.extend(
        _dedent_frontmatter_line(line, base_indent) for line in body_lines)
    normalized_lines.extend(lines[end_idx:])
    return normalized_lines, endings, end_idx


def _encode_dq_description(optimized_desc: str) -> str:
    """把 description 归一为单行、控制字符转空格，超长截断后做双引号 YAML 编码。"""
    normalized = (optimized_desc.strip()
                  .replace("\n", " ").replace("\t", " ").replace("\r", " "))
    normalized = normalized.translate(_CTRL_TO_SPACE_TABLE)
    if _desc_length(normalized) > DESC_MAX:
        normalized = truncate_description(
            normalized, DESC_MAX, "。", clamp_within_limit=True)
    return "description: " + yaml_quote_scalar(normalized)


def _merge_indented_desc_keywords(text: str, description: str | None,
                                  keywords: list[str],
                                  md_label: str) -> tuple[str | None, bool]:
    """缩进式 frontmatter 下合并写回 description 与 keywords；引号未闭合时放弃写回并告警。"""
    indented = _indented_frontmatter(text)
    if indented is None:
        return None, False
    lines, endings, end_idx = indented
    if description is not None:
        replaced = _replace_desc_lines(
            lines, endings, _encode_dq_description(description), end_idx)
        if replaced is None:
            _log.warning(
                "[best_practices] %s description 引号标量未闭合，合并写回被拒绝",
                md_label)
            return None, True
        lines, endings = replaced
    normalized = "".join(line + ending for line, ending in
                         zip(lines, endings, strict=True))
    status: dict[str, Any] = {}
    merged = replace_frontmatter_desc_keywords(
        normalized, None, keywords, md_label=md_label,
        status_out=status)
    if keywords and not status.get("keywords_written"):
        _log.warning(
            "[best_practices] %s 缩进 frontmatter keywords 写回未落盘",
            md_label)
    return _restore_line_endings(text, merged), True


# SKILL.md 文档读取结构：写回自读，也允许调用方注入已读结果复用
@dataclass(frozen=True)
class _SkillMdDocument:
    lines: list[str]
    endings: list[str]
    has_bom: bool
    end_idx: int | None


def _load_skill_md_document(skill_dir: str) -> _SkillMdDocument | None:
    skill_md = Path(skill_dir) / "SKILL.md"
    if not skill_md.exists():
        return None
    try:
        raw = skill_md.read_bytes()
        content = raw.decode("utf-8-sig")
    except (OSError, UnicodeDecodeError) as e:
        _log.warning("[best_practices] 读取 SKILL.md 失败: %s", e)
        return None
    has_bom = raw.startswith(b"\xef\xbb\xbf")
    lines, endings = _split_keep_endings(content)
    # 读取路径允许 frontmatter 前存在前导空行；写回定位必须同口径，
    # 否则同一份合法文档会在自动修复时被判为“无 frontmatter”而静默跳过。
    first = 0
    while first < len(lines) and not lines[first].strip():
        first += 1
    if first >= len(lines) or not is_frontmatter_fence(
            lines[first].removeprefix("\ufeff")):
        return None
    end_idx = next((i for i in range(first + 1, len(lines))
                    if is_frontmatter_fence(lines[i])), None)
    if end_idx is None:
        return _SkillMdDocument(lines=lines, endings=endings,
                                has_bom=has_bom, end_idx=None)
    body_lines = lines[first + 1:end_idx]
    base_indent = _frontmatter_body_indent(body_lines)
    if base_indent:
        norm_lines = lines[:first + 1]
        norm_endings = endings[:first + 1]
        for line, ending in zip(
                body_lines, endings[first + 1:end_idx], strict=True):
            norm_lines.append(_dedent_frontmatter_line(line, base_indent))
            norm_endings.append(ending)
        norm_lines.extend(lines[end_idx:])
        norm_endings.extend(endings[end_idx:])
        lines, endings = norm_lines, norm_endings
    return _SkillMdDocument(lines=lines, endings=endings,
                            has_bom=has_bom, end_idx=end_idx)


def _write_back_description(skill_dir: str, optimized_desc: str,
                            read_document=None) -> bool:
    """读取 SKILL.md 文档结构，定点替换 description 后受控写回；失败只告警不抛出。"""
    if read_document is None:
        read_document = _load_skill_md_document
    doc = read_document(skill_dir)
    if doc is None:
        return False
    if doc.end_idx is None:
        _log.warning("[best_practices] frontmatter 未闭合，跳过 description 写回: %s",
                     Path(skill_dir) / "SKILL.md")
        return False
    replaced = _replace_desc_lines(
        doc.lines, doc.endings, _encode_dq_description(optimized_desc),
        doc.end_idx)
    if replaced is None:
        return False
    new_lines, new_endings = replaced
    try:
        write_markdown_text(
            Path(skill_dir) / "SKILL.md",
            "".join(line + ending for line, ending in
                     zip(new_lines, new_endings, strict=True)),
            doc.has_bom,
            newline="",
        )
    except (OSError, ValueError) as e:
        _log.warning("[best_practices] description 写回失败: %s", e)
        return False
    return True

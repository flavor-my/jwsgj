from __future__ import annotations

import functools
import logging
import math
import os
import re
from collections.abc import Iterator, Mapping, Sequence
from pathlib import Path
from typing import Any
from urllib.parse import unquote

from jwsgj.diag_guard_io import (
    SKILL_DOC_FILENAME,
    fs_path_text,
    guarded_open,
    normalize_path_arg,
)
from jwsgj.diag_shared_source_core import (
    read_source,
    read_source_interpreter_encoding,
)
from jwsgj.diag_types_normalize import text_or_empty
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_scope import (
    SCAN_COLLECT_PRUNE_DIRS_LOWER,
    is_audit_skip_dir,
    is_out_of_scope_dir,
    normalize_text,
)

__all__ = [
    'BLOCK_SCALAR_INDICATORS',
    'CORE_ACTION_VERBS',
    'DESCRIPTION_MAX_LEN',
    'DOMAIN_KEYWORDS',
    'ENTRY_DOC_NAME',
    'LANGUAGE_EN',
    'LANGUAGE_ZH',
    'PY_FILE_REF_PATTERN',
    'SETEXT_UNDERLINE_RE',
    'SKILL_ACTION_VERBS',
    'SLOT_NOISE_CHARS',
    '_DEFAULT_DOC_PROFILE',
    '_GENERIC_BOUNDARY_RE',
    '_REF_DIR_RE',
    '_RESOURCE_DIR_ALT',
    '_aligned_prefix_len',
    '_aligned_suffix_len',
    '_body_h2_titles',
    '_desc_length',
    '_dominant_line_ending',
    '_iter_local_links',
    '_local_md_refs',
    '_md_local_paths',
    '_normalize_sections_found',
    '_ref_escapes_skill_dir',
    '_restore_line_endings',
    '_split_keep_endings',
    'contains_term',
    'count_words_cn_aware',
    'detect_doc_profile',
    'detect_text_language',
    'find_first_sentence_period',
    'first_content_paragraph',
    'has_cjk',
    'has_section',
    'identifier_pattern',
    'is_skill_dir',
    'is_skill_dir_strict',
    'iter_atx_headings',
    'iter_doc_entry_candidates',
    'iter_fence_lines',
    'iter_fence_state',
    'iter_fenced_blocks',
    'iter_fenced_code_blocks',
    'iter_matching_files',
    'iter_skill_dirs',
    'jaccard',
    'locate_section',
    'match_domain',
    'match_source_eol',
    'normalize_domain_key',
    'normalize_newlines',
    'normalize_str',
    'normalize_str_list',
    'normalize_text',
    'parse_atx_heading',
    'path_exists',
    'read_skill_text',
    'read_skill_text_interpreter_encoding',
    'readable_skill_name',
    'replace_atx_level',
    'resolve_entry_document',
    'resource_dir_names',
    'restore_text_form',
    'safe_is_dir',
    'safe_text',
    'scan_fence_state',
    'strip_atx_closing',
    'strip_fenced_blocks',
    'strip_inline_comment',
    'tokenize_words',
    'truncate_description',
    'unquote_yaml_scalar',
    'word_pattern',
    'write_markdown_text',
    'write_text_preserving_form',
]
_log = logging.getLogger(__name__)
def safe_text(value: Any) -> str:
    try:
        return str(value)
    except Exception as exc:  # noqa: BLE001 — 超深/异形对象的 __str__ 可能抛任意异常
        log_swallowed(__name__, exc,
                      context=f'safe_text:{type(exc).__name__}')
        return f"<{type(value).__name__}>"
DESCRIPTION_MAX_LEN = 280
_DEFAULT_TERMINAL = "."
_PERIOD_CUT_MIN = 200
_SPACE_CUT_MIN = 180
_CLAUSE_CUT_CHARS = "。；;！!？?，,、：:"
_CLAUSE_TERMINAL_CHARS = "。！!？?"
_CLAUSE_TAIL_PUNCT = "、，,：:；;"
_SENTENCE_TERMINAL_PUNCT = ".。!！?？…"
def _is_word_char(ch: str) -> bool:
    return bool(ch) and (ch.isalnum() or ch == "_")
def _is_intra_word_dot(desc: str, pos: int) -> bool:
    prev_ch = desc[pos - 1] if pos > 0 else ""
    next_ch = desc[pos + 1] if pos + 1 < len(desc) else ""
    return _is_word_char(prev_ch) and _is_word_char(next_ch)
def _is_abbreviation_dot(desc: str, pos: int) -> bool:
    next_ch = desc[pos + 1] if pos + 1 < len(desc) else ""
    if next_ch.isascii() and next_ch.islower():
        return True
    start = pos - 1
    while (start >= 2 and desc[start - 1] == "."
           and desc[start - 2].isascii() and desc[start - 2].isalpha()):
        start -= 2
    return (start != pos - 1
            and (start == 0
                 or not (desc[start - 1].isascii()
                         and desc[start - 1].isalpha())))
def _sentence_period_positions(desc: str) -> list[int]:
    return [
        pos for pos, ch in enumerate(desc)
        if ch == "。" or (
            ch == "."
            and not _is_intra_word_dot(desc, pos)
            and not _is_abbreviation_dot(desc, pos)
        )
    ]
def find_first_sentence_period(desc: str) -> int:
    positions = _sentence_period_positions(desc)
    return positions[0] if positions else -1
def _find_last_sentence_period(desc: str) -> int:
    positions = _sentence_period_positions(desc)
    return positions[-1] if positions else -1
def _normalize_limit(limit: Any) -> int:
    if isinstance(limit, bool) or not isinstance(limit, (int, float)):
        _log.warning(
            "truncate_description limit 类型 %s 非法（应为 int），按默认 %d 处理",
            type(limit).__name__, DESCRIPTION_MAX_LEN)
        return DESCRIPTION_MAX_LEN
    if isinstance(limit, float) and not math.isfinite(limit):
        _log.warning(
            "truncate_description limit 非有限值 %r，按默认 %d 处理",
            limit, DESCRIPTION_MAX_LEN)
        return DESCRIPTION_MAX_LEN
    return int(limit)
def _normalize_terminal(terminal: Any) -> str:
    if isinstance(terminal, str) and terminal.strip():
        return terminal.strip()
    _log.warning(
        "truncate_description terminal 类型 %s 非法（应为非空 str），按 %r 处理",
        type(terminal).__name__, _DEFAULT_TERMINAL)
    return _DEFAULT_TERMINAL
def truncate_description(text: str, limit: int = DESCRIPTION_MAX_LEN,
                         terminal: str = _DEFAULT_TERMINAL, *,
                         clamp_within_limit: bool = False) -> str:
    if not isinstance(text, str):
        return ""
    limit = _normalize_limit(limit)
    if limit <= 0:
        return text
    if len(text) <= limit:
        if not clamp_within_limit or not text:
            return text
        terminal = _normalize_terminal(terminal)
        return _close_with_terminal(
            text.rstrip(_CLAUSE_TAIL_PUNCT + " 	"), terminal, limit)
    terminal = _normalize_terminal(terminal)
    truncated = text[:limit]
    last_period = _find_last_sentence_period(text[:limit + 1])
    if _PERIOD_CUT_MIN < last_period < limit:
        return truncated[:last_period + 1]
    clause_cut = _last_clause_cut(truncated, _PERIOD_CUT_MIN)
    if clause_cut > 0:
        if truncated[clause_cut] in _CLAUSE_TERMINAL_CHARS:
            return truncated[:clause_cut + 1]
        return _close_with_terminal(
            truncated[:clause_cut].rstrip(_CLAUSE_TAIL_PUNCT), terminal, limit)
    last_space = truncated.rfind(" ")
    cut = (truncated[:last_space] if last_space > _SPACE_CUT_MIN
           else truncated[:limit - 1])
    return _close_with_terminal(cut, terminal, limit)
def _is_clause_boundary(text: str, index: int, char: str) -> bool:
    if char not in _CLAUSE_CUT_CHARS:
        return False
    if char in ":：":
        next_char = text[index + 1] if index + 1 < len(text) else ""
        if text[index + 1:index + 3] == "//" or next_char in "/\\":
            return False
        prev_char = text[index - 1] if index else ""
        if prev_char.isdigit() and next_char.isdigit():
            return False
    return True
def _last_clause_cut(text: str, minimum: int) -> int:
    best = -1
    for _idx, _ch in enumerate(text):
        if _idx > minimum and _is_clause_boundary(text, _idx, _ch):
            best = _idx
    return best
def _close_with_terminal(cut: str, terminal: str, limit: int) -> str:
    cut = cut.rstrip(_CLAUSE_TAIL_PUNCT + " \t")
    if not cut:
        return terminal[:limit]
    if cut[-1:] in _SENTENCE_TERMINAL_PUNCT:
        return cut[:limit]
    content_limit = max(0, limit - len(terminal))
    trimmed = cut[:content_limit].rstrip(_CLAUSE_TAIL_PUNCT + " \t")
    if not trimmed:
        return terminal[:limit]
    if trimmed[-1:] in _SENTENCE_TERMINAL_PUNCT:
        return trimmed
    return trimmed + terminal
def _scan_quoted_span_end(text: str, i: int, quote: str) -> int | None:
    if quote == '"':
        return _scan_double_quoted_end(text, i)
    return _scan_single_quoted_end(text, i)
def _scan_double_quoted_end(text: str, i: int) -> int | None:
    n = len(text)
    while i < n:
        if text[i] == "\\" and i + 1 < n:
            i += 2
            continue
        if text[i] == '"':
            return i + 1
        i += 1
    return None
def _scan_single_quoted_end(text: str, i: int) -> int | None:
    n = len(text)
    while i < n:
        if text[i] != "'":
            i += 1
            continue
        if text[i + 1:i + 2] == "'":
            i += 2
            continue
        return i + 1
    return None
def _quote_starts_flow_scalar(text: Sequence[str], i: int, seg_start: int) -> bool:
    j = i - 1
    while j >= seg_start and text[j] in " \t\r\n":
        j -= 1
    return j < seg_start or text[j] in ",:[{"
_FLOW_UNINDENTED_FIELD_RE = re.compile(
    r"^[^ \t#:,\[\]{}]+[ \t]*:(?:[ \t]|$)")
def _flow_closes_on_next_line(text: str, index: int) -> bool:
    depth = 0
    line_start = index + 1
    line_end = text.find("\n", line_start)
    if line_end < 0:
        line_end = len(text)
    i = line_start
    while i < line_end:
        ch = text[i]
        if ch in ('"', "'") and _quote_starts_flow_scalar(text, i, line_start):
            end = _scan_quoted_span_end(text, i + 1, ch)
            if end is None:
                return False
            i = end
            continue
        if ch in "[{":
            depth += 1
        elif ch in "]}":
            if depth > 0:
                depth -= 1
            elif ch == "]":
                return True
        i += 1
    return False
def _flow_breaks_at_unindented_field(text: str, index: int) -> bool:
    n = len(text)
    next_index = index + 1
    while next_index < n and text[next_index] in " \t":
        next_index += 1
    if not (next_index == index + 1 and next_index < n
            and _FLOW_UNINDENTED_FIELD_RE.match(text[next_index:]) is not None):
        return False
    return not _flow_closes_on_next_line(text, index)
def _split_flow_segments(text: str, start: int) -> list[str]:
    segs: list[str] = []
    seg_start = start
    depth = 0
    i = start
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == "\n" and _flow_breaks_at_unindented_field(text, i):
            segs.append(text[seg_start:i])
            return segs
        if ch in ('"', "'") and _quote_starts_flow_scalar(text, i, seg_start):
            end = _scan_quoted_span_end(text, i + 1, ch)
            if end is None:
                break
            i = end
            continue
        if ch in "[{":
            depth += 1
        elif ch in "]}":
            if depth > 0:
                depth -= 1
                i += 1
                continue
            if ch == "]":
                segs.append(text[seg_start:i])
                return segs
        elif ch == "," and depth == 0:
            segs.append(text[seg_start:i])
            seg_start = i + 1
        i += 1
    segs.append(text[seg_start:])
    return segs
def _mask_flow_comments(text: str, start: int) -> str:
    chars = list(text)
    i = start
    while i < len(text):
        ch = text[i]
        if ch in ('"', "'") and _quote_starts_flow_scalar(chars, i, start):
            end = _scan_quoted_span_end(text, i + 1, ch)
            if end is None:
                return text
            i = end
            continue
        if ch == "#" and (i == 0 or text[i - 1] in " \t\r\n"):
            line_end = text.find("\n", i)
            if line_end < 0:
                line_end = len(text)
            chars[i:line_end] = " " * (line_end - i)
            i = line_end + 1
            continue
        i += 1
    return "".join(chars)
_DQ_ESCAPE_MAP: dict[str, str] = {
    "0": "\0", "a": "\a", "b": "\b", "t": "\t", "n": "\n",
    "v": "\v", "f": "\f", "r": "\r", "e": "\x1b", " ": " ",
    '"': '"', "/": "/", "\\": "\\",
    "N": "\x85", "_": "\xa0", "L": "\u2028", "P": "\u2029",
}
_HEX_DIGITS = frozenset("0123456789abcdefABCDEF")
_HEX_ESCAPE_WIDTHS: dict[str, int] = {"x": 2, "u": 4, "U": 8}
def _decode_hex_escape(content: str, start: int) -> tuple[str, int] | None:
    width = _HEX_ESCAPE_WIDTHS.get(content[start + 1])
    if width is None:
        return None
    hex_part = content[start + 2:start + 2 + width]
    if len(hex_part) != width or not _HEX_DIGITS.issuperset(hex_part):
        return None
    code = int(hex_part, 16)
    if code > 0x10FFFF or 0xD800 <= code <= 0xDFFF:
        return None
    return chr(code), 2 + width
def _decode_dq_scalar(content: str) -> str:
    if "\\" not in content:
        return content
    out: list[str] = []
    i, n = 0, len(content)
    while i < n:
        ch = content[i]
        if ch != "\\" or i + 1 >= n:
            out.append(ch)
            i += 1
            continue
        esc = content[i + 1]
        mapped = _DQ_ESCAPE_MAP.get(esc)
        if mapped is not None:
            out.append(mapped)
            i += 2
            continue
        hex_decoded = _decode_hex_escape(content, i)
        if hex_decoded is not None:
            out.append(hex_decoded[0])
            i += hex_decoded[1]
            continue
        out.append(ch)
        out.append(esc)
        i += 2
    return "".join(out)
def unquote_yaml_scalar(value: str) -> str:
    value = normalize_text(value).strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in ("'", '"'):
        inner = value[1:-1]
        if value[0] == "'":
            return inner.replace("''", "'")
        return _decode_dq_scalar(inner)
    return value
_YAML_EMPTY_SCALAR_FORMS = frozenset({"null", "~", "[]", "{}"})
_NULL_TAGGED_SCALAR_RE = re.compile(r"^!!?null(?:[ \t]|$)", re.IGNORECASE)
def _is_empty_yaml_scalar(value: str) -> bool:
    text = normalize_text(value).strip()
    if text.lower() in _YAML_EMPTY_SCALAR_FORMS:
        return True
    return _NULL_TAGGED_SCALAR_RE.match(text) is not None
def strip_inline_comment(raw: str) -> str:
    value = normalize_text(raw).lstrip()
    if not value.strip():
        return ""
    if value[0] in ("'", '"'):
        end = _scan_quoted_span_end(value, 1, value[0])
        return value[:end] if end is not None else value
    value = value.rstrip()
    comment = _INLINE_COMMENT_START_RE.search(value)
    return value[:comment.start()].rstrip() if comment else value
_QUOTE_CHARS = frozenset(("\"", "'"))
def _is_yaml_mapping_item(text: str) -> bool:
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in _QUOTE_CHARS and _quote_starts_flow_scalar(text, i, 0):
            end = _scan_quoted_span_end(text, i + 1, ch)
            if end is None:
                return False
            i = end
            continue
        if ch == ":" and (i + 1 == len(text) or text[i + 1] in " \t\r\n"):
            return True
        i += 1
    return False
def _scalar_item(raw: str) -> str:
    text = normalize_text(raw).strip()
    if not text or _is_yaml_mapping_item(text):
        return ""
    if text[0] in _QUOTE_CHARS:
        if len(text) >= 2 and text[-1] == text[0]:
            return _fold_flow_scalar(text[1:-1], text[0])
        return unquote_yaml_scalar(text)
    if text[0] in "[{":
        return ""
    text = _fold_flow_scalar(text).strip()
    if (_is_empty_yaml_scalar(text)
            or text.lower() in _YAML_BOOL_NULL_TOKENS
            or _YAML_NUMBER_RE.fullmatch(text)
            or _YAML_TIMESTAMP_RE.fullmatch(text)):
        return ""
    return unquote_yaml_scalar(text)
def _decode_scalar_segments(segs: list[str]) -> list[str]:
    out: list[str] = []
    for seg in segs:
        value = _scalar_item(seg)
        if value:
            out.extend(line.strip() for line in value.splitlines()
                       if line.strip())
    return out
def _parse_flow_scalars(text: str, start: int) -> list[str]:
    text = _mask_flow_comments(normalize_text(text), start)
    return _decode_scalar_segments(_split_flow_segments(text, start))
def _description_scalar(value: str, *, quoted: bool = False) -> str:
    if quoted:
        return value
    text = normalize_text(value).strip()
    if not text:
        return ""
    if text[0] == "[" and text.endswith("]"):
        return "\n".join(_parse_description_flow_scalars(text, 1))
    if text[0] == "{" and text.endswith("}"):
        return ""
    if (text.lower() in _YAML_BOOL_NULL_TOKENS
            or _is_empty_yaml_scalar(text)
            or _YAML_NUMBER_RE.fullmatch(text)
            or _YAML_TIMESTAMP_RE.fullmatch(text)):
        return ""
    return value
def _description_sequence_item(raw: str) -> str:
    text = normalize_text(raw).strip()
    if not text or _is_yaml_mapping_item(text):
        return ""
    if text[0] in _QUOTE_CHARS:
        if (len(text) >= 2 and text[-1] == text[0]
                and ("\n" in text or "\r" in text)):
            return _fold_flow_scalar(text[1:-1], text[0])
        return unquote_yaml_scalar(text)
    if text.startswith(("[", "{")):
        return ""
    if "\n" in text or "\r" in text:
        text = _fold_flow_scalar(text).strip()
    return _description_scalar(text)
def _parse_description_flow_scalars(text: str, start: int) -> list[str]:
    text = _mask_flow_comments(normalize_text(text), start)
    items: list[str] = []
    for segment in _split_flow_segments(text, start):
        value = _description_sequence_item(segment)
        if value:
            items.append(value)
    return items
def _name_text(value: str) -> str:
    return re.sub(r"\s+", " ", normalize_text(value)).strip()
def _version_scalar(value: str, *, quoted: bool = False) -> str:
    text = normalize_text(value).strip()
    if quoted:
        return text
    if (not text
            or text.lower() in _YAML_BOOL_NULL_TOKENS
            or _is_empty_yaml_scalar(text)
            or text.startswith(("[", "{"))
            or _is_block_scalar_head(text)):
        return ""
    return text
def _flow_fold_separator(pending_breaks: int) -> str:
    return " " if pending_breaks == 1 else "\n" * (pending_breaks - 1)
def _rstrip_flow_line(content: str, quote: str) -> str:
    end = len(content)
    while end and content[end - 1] in " \t":
        if quote == '"' and content[end - 1] == " ":
            slash_start = end - 1
            while slash_start and content[slash_start - 1] == "\\":
                slash_start -= 1
            if (end - 1 - slash_start) % 2:
                break
        end -= 1
    return content[:end]
def _fold_flow_scalar(raw: str, quote: str = "") -> str:
    if not raw:
        return ""
    text = normalize_text(raw).replace("\r\n", "\n").replace("\r", "\n")
    if quote == '"':
        text = re.sub(
            r"(\\+)\n[ \t]*",
            lambda match: (match.group(1)[:-1]
                           if len(match.group(1)) % 2 else match.group(0)),
            text,
        )
    lines = text.split("\n")
    out: list[str] = []
    pending_breaks = 0
    for index, line in enumerate(lines):
        if index:
            pending_breaks += 1
        if not line.strip():
            continue
        content = line if index == 0 else line.lstrip(" \t")
        if index != len(lines) - 1:
            content = _rstrip_flow_line(content, quote)
        if out or pending_breaks:
            out.append(_flow_fold_separator(pending_breaks))
        out.append(content)
        pending_breaks = 0
    if out and pending_breaks:
        out.append(_flow_fold_separator(pending_breaks))
    folded = "".join(out)
    if quote == "'":
        return folded.replace("''", "'")
    if quote == '"':
        return _decode_dq_scalar(folded)
    return folded
_INLINE_COMMENT_START_RE = re.compile(r"(?:^|[ \t])#")
_NON_CONTENT_LINE_RE = re.compile(r"^#{1,6}\s+|^(?:=+|-+)$")
SETEXT_UNDERLINE_RE = re.compile(r"^(?:=+|-+)$")
def _is_body_content_line(lines: list[str], index: int) -> bool:
    line = lines[index]
    if _NON_CONTENT_LINE_RE.match(line):
        return False
    followed_by_setext = (
        index + 1 < len(lines)
        and SETEXT_UNDERLINE_RE.match(lines[index + 1])
    )
    return not followed_by_setext
def _paragraph_content_lines(paragraph: str) -> list[str]:
    lines = [line.strip() for line in paragraph.split("\n") if line.strip()]
    setext_lines: set[int] = set()
    for underline, line in enumerate(lines):
        if underline == 0 or not SETEXT_UNDERLINE_RE.match(line):
            continue
        start = underline - 1
        if start in setext_lines or _NON_CONTENT_LINE_RE.match(lines[start]):
            continue
        while start > 0:
            previous = start - 1
            if (previous in setext_lines
                    or _NON_CONTENT_LINE_RE.match(lines[previous])):
                break
            start = previous
        setext_lines.update(range(start, underline + 1))
    return [
        line for index, line in enumerate(lines)
        if index not in setext_lines and _is_body_content_line(lines, index)
    ]
_FENCE_LINE_RE = re.compile(r'^[ ]{0,3}(`{3,}|~{3,})')
def scan_fence_state(in_fence: bool, fence_char: str, fence_len: int,
                     ln: str) -> tuple[bool, str, int, str]:
    if not isinstance(ln, str):
        return in_fence, fence_char, fence_len, ""
    m = _FENCE_LINE_RE.match(ln)
    if not m:
        return in_fence, fence_char, fence_len, ""
    fc = m.group(1)[0]
    if not in_fence:
        if fc == '`' and '`' in ln[m.end():]:
            return in_fence, fence_char, fence_len, ""
        return True, fc, len(m.group(1)), "open"
    if (fc == fence_char
            and len(m.group(1)) >= fence_len
            and m.group(1) == ln.strip()):
        return False, '', 0, "close"
    return in_fence, fence_char, fence_len, "content"
_ATX_CLOSING_RE = re.compile(r'[ \t]+#+[ \t]*$')
_ALL_HASH_TITLE_RE = re.compile(r'#+')
def strip_atx_closing(title: str) -> str:
    title = (title or "").strip()
    closing = _ATX_CLOSING_RE.search(title)
    if closing:
        return title[:closing.start()].strip()
    return "" if _ALL_HASH_TITLE_RE.fullmatch(title) else title
def iter_fence_lines(lines) -> Iterator[tuple[str, bool]]:
    in_fence = False
    fence_char = ""
    fence_len = 0
    for line in lines:
        in_fence, fence_char, fence_len, _line_kind = scan_fence_state(
            in_fence, fence_char, fence_len, line)
        yield line, in_fence
_TOLERANT_FENCE_LINE_RE = re.compile(r"(`{3,}|~{3,})(.*)$")
def _parse_fence_line(line: str):
    if not isinstance(line, str):
        return None
    stripped = line.strip()
    match = _TOLERANT_FENCE_LINE_RE.match(stripped)
    if not match:
        return None
    ticks = match.group(1)
    return ticks[0], len(ticks), match.group(2)
def iter_fence_state(lines: Any) -> Iterator[tuple[str, bool]]:
    in_fence = False
    fence_char = ""
    fence_len = 0
    for line in lines:
        parsed = _parse_fence_line(line)
        if parsed:
            char, ticks, rest = parsed
            if not in_fence:
                if not (char == "`" and "`" in rest):
                    in_fence, fence_char, fence_len = True, char, ticks
            elif (char == fence_char and ticks >= fence_len
                    and not rest.strip()):
                in_fence, fence_char, fence_len = False, "", 0
        yield line, in_fence
def strip_fenced_blocks(text: str) -> str:
    if not isinstance(text, str):
        return ""
    out: list[str] = []
    in_fence = False
    fence_char = ''
    fence_len = 0
    for ln in text.split("\n"):
        in_fence, fence_char, fence_len, line_kind = scan_fence_state(
            in_fence, fence_char, fence_len, ln)
        if line_kind:
            if line_kind == "open" and out and out[-1].strip():
                out.append("")
            continue
        if not in_fence:
            out.append(ln)
    return "\n".join(out)
def _fence_tag_of(ln: str) -> str:
    m = _FENCE_LINE_RE.match(ln)
    info = ln[m.end():].strip() if m else ''
    return info.split(None, 1)[0] if info else ''
def _iter_fence_block_segments(text: str):
    if not isinstance(text, str):
        return
    cur: list[str] = []
    tag = ''
    in_fence = False
    fence_char = ''
    fence_len = 0
    for ln in text.split("\n"):
        in_fence, fence_char, fence_len, line_kind = scan_fence_state(
            in_fence, fence_char, fence_len, ln)
        if line_kind == "open":
            tag = _fence_tag_of(ln)
            cur = []
        elif line_kind == "close":
            if cur:
                yield tag, cur
            cur = []
            tag = ''
        elif in_fence:
            cur.append(ln)
    if in_fence and cur:
        yield tag, cur
def iter_fenced_blocks(text: str) -> list[str]:
    return ["\n".join(lines) for _tag, lines in _iter_fence_block_segments(text)]
def iter_fenced_code_blocks(text: str) -> list[tuple[str, str]]:
    return [(tag, "\n".join(lines))
            for tag, lines in _iter_fence_block_segments(text)]
_ATX_HEADING_RE = re.compile(r"^[ ]{0,3}(#{1,6})(?:[ \t]+(.*))?$")
def parse_atx_heading(line: str) -> tuple[int, str] | None:
    if not isinstance(line, str):
        return None
    m = _ATX_HEADING_RE.match(line.rstrip("\r\n"))
    if not m:
        return None
    return len(m.group(1)), strip_atx_closing(m.group(2) or "")
def replace_atx_level(line: str, new_level: int) -> str | None:
    if not isinstance(line, str):
        return None
    m = _ATX_HEADING_RE.match(line.rstrip("\r\n"))
    if not m:
        return None
    try:
        level = max(1, min(6, int(new_level)))
    except (TypeError, ValueError):
        return None
    return line[:m.start(1)] + "#" * level + line[m.end(1):]
def iter_atx_headings(content: str,
                      level: int | None = None) -> Iterator[tuple[int, int, int, str]]:
    if not isinstance(content, str):
        return
    in_fence = False
    fence_char = ""
    fence_len = 0
    pos = 0
    for line in content.splitlines(keepends=True):
        line_start = pos
        pos += len(line)
        in_fence, fence_char, fence_len, line_kind = scan_fence_state(
            in_fence, fence_char, fence_len, line)
        if line_kind or in_fence:
            continue
        parsed = parse_atx_heading(line)
        if parsed is None:
            continue
        heading_level, title = parsed
        if level is not None and heading_level != level:
            continue
        yield line_start, pos, heading_level, title
def locate_section(content: str, header: str) -> tuple[int, int] | None:
    target = parse_atx_heading(header)
    if target is None:
        return None
    level, title = target
    start = None
    for line_start, _line_end, heading_level, heading_title in iter_atx_headings(content):
        if start is None:
            if heading_level == level and heading_title == title:
                start = line_start
        elif heading_level <= level:
            return start, line_start
    if start is not None:
        return start, len(content)
    return None
def has_section(content: str, header: str) -> bool:
    return locate_section(content, header) is not None
def match_source_eol(source: str, text: str) -> tuple[str, str]:
    source = normalize_text(source)
    normalized = normalize_newlines(normalize_text(text))
    if "\r\n" in source:
        return "\r\n", normalized.replace("\n", "\r\n")
    if "\r" in source and "\n" not in source:
        return "\r", normalized.replace("\n", "\r")
    return "\n", normalized
def first_content_paragraph(body_text: str) -> str:
    normalized = normalize_newlines(normalize_text(body_text))
    normalized = strip_fenced_blocks(normalized)
    paragraphs = [
        p.strip() for p in re.split(r"\n[ \t]*\n", normalized) if p.strip()
    ]
    for paragraph in paragraphs:
        content = _paragraph_content_lines(paragraph)
        if content:
            return " ".join(content)
    return ""
ENTRY_DOC_NAME = SKILL_DOC_FILENAME
_README_STEM = "readme"
_DOC_ENTRY_SUFFIXES = (".md", ".markdown", ".rst", ".txt")
_DOC_ENTRY_DIRS = ("", "docs", "doc", "documentation")
_DOC_ENTRY_INDEX_STEMS = ("index", "readme")
def _readme_family(name: str) -> bool:
    stem = os.path.splitext(name)[0].casefold()
    if os.path.splitext(name)[1].casefold() not in _DOC_ENTRY_SUFFIXES:
        return False
    if stem == _README_STEM:
        return True
    return stem.startswith(_README_STEM) and stem[len(_README_STEM)] in "._-"
def _doc_entry_files(directory: Path) -> list[Path]:
    try:
        entries = [
            entry for entry in directory.iterdir()
            if entry.is_file()
            and entry.suffix.casefold() in _DOC_ENTRY_SUFFIXES
        ]
    except (OSError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'doc_entry_files:{type(_e).__name__}')
        return []
    return sorted(entries, key=lambda entry: entry.name.casefold())
def iter_doc_entry_candidates(root: Path | str) -> Iterator[Path]:
    try:
        base = _as_path(root)
    except (OSError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'doc_entry_candidates:{type(_e).__name__}')
        return
    yield base / ENTRY_DOC_NAME
    yield base / ENTRY_DOC_NAME.lower()
    for subdir in _DOC_ENTRY_DIRS:
        directory = base if not subdir else base / subdir
        for entry in _doc_entry_files(directory):
            if _readme_family(entry.name):
                yield entry
        for stem in _DOC_ENTRY_INDEX_STEMS:
            for suffix in _DOC_ENTRY_SUFFIXES:
                yield directory / f"{stem}{suffix}"
def resolve_entry_document(
    root: Path | str, *, preferred: Any = None,
) -> Path | None:
    try:
        base = _as_path(root)
    except (OSError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'doc_entry_resolve:{type(_e).__name__}')
        return None
    if preferred is not None and not isinstance(preferred, (dict, list, tuple, set)):
        try:
            candidate = Path(os.fspath(preferred))
        except (TypeError, ValueError) as _e:
            log_swallowed(__name__, _e,
                          context=f'doc_entry_preferred:{type(_e).__name__}')
            candidate = None
        if candidate is not None:
            candidate = candidate if candidate.is_absolute() else base / candidate
            if _safe_is_file(candidate):
                return candidate
    for candidate in iter_doc_entry_candidates(base):
        if _safe_is_file(candidate):
            return candidate
    return None
def read_skill_text(skill_md: Path) -> str:
    try:
        path = _as_path(skill_md)
    except (TypeError, ValueError) as exc:
        raise OSError(f"SKILL.md 路径非法: {skill_md!r}") from exc
    text = read_source(str(path))
    if text is None:
        raise OSError(f"SKILL.md 读取失败: {skill_md}")
    return text
def read_skill_text_interpreter_encoding(skill_md: Path | str) -> str:
    try:
        path = _as_path(skill_md)
    except (TypeError, ValueError) as exc:
        raise OSError(f"SKILL.md 路径非法: {skill_md!r}") from exc
    return read_source_interpreter_encoding(str(path))
_YAML_BOOL_NULL_TOKENS = frozenset(
    ("true", "false", "yes", "no", "on", "off", "null", "~"))
_YAML_NUMBER_RE = re.compile(r"""[-+]?(?:
      0b[01_]+
    | 0[0-7_]+
    | 0x[0-9a-fA-F_]+
    | (?:0|[1-9][0-9_]*)(?:\.[0-9_]*)?(?:[eE][-+]?[0-9]+)?
    | \.[0-9_]+(?:[eE][-+]?[0-9]+)?
    | \.(?:inf|Inf|INF)
    | \.(?:nan|NaN|NAN)
)""", re.VERBOSE)
_YAML_TIMESTAMP_RE = re.compile(r"""
    (?:\d{4}-\d{2}-\d{2}
    |\d{4}-\d{1,2}-\d{1,2}(?:[Tt]|[ \t]+)
      \d{1,2}:\d{2}:\d{2}(?:\.\d*)?
      (?:[ \t]*(?:Z|[-+]\d{1,2}(?::\d{2})?))?)
""", re.VERBOSE)
_BLOCK_SCALAR_HEADER = r"[|>](?:[1-9][+-]?|[+-][1-9]?)?"
_BLOCK_SCALAR_HEAD_PAT = re.compile(_BLOCK_SCALAR_HEADER)
def _is_block_scalar_head(value: str) -> bool:
    return bool(_BLOCK_SCALAR_HEAD_PAT.fullmatch((value or "").strip()))
_BLOCK_SCALAR_HEADS = ("|", ">")
_CHOMPING_INDICATORS = ("-", "+")
_INDENT_INDICATOR_DIGITS = tuple("123456789")
BLOCK_SCALAR_INDICATORS = frozenset(
    # jwsgj:suppress large_list_alloc
    [head + suffix
     for head in _BLOCK_SCALAR_HEADS
     for suffix in ("",) + _CHOMPING_INDICATORS]
    # jwsgj:suppress large_list_alloc
    + [head + digit
       for head in _BLOCK_SCALAR_HEADS
       for digit in _INDENT_INDICATOR_DIGITS]
    # jwsgj:suppress large_list_alloc
    + [head + digit + chomp
       for head in _BLOCK_SCALAR_HEADS
       for digit in _INDENT_INDICATOR_DIGITS
       for chomp in _CHOMPING_INDICATORS]
    # jwsgj:suppress large_list_alloc
    + [head + chomp + digit
       for head in _BLOCK_SCALAR_HEADS
       for chomp in _CHOMPING_INDICATORS
       for digit in _INDENT_INDICATOR_DIGITS])
@functools.lru_cache(maxsize=8192)
def _cached_identifier_pattern(name: str) -> re.Pattern[str]:
    return re.compile(
        rf'(?<![A-Za-z0-9_]){re.escape(name)}(?![A-Za-z0-9_])')
def identifier_pattern(name: str) -> re.Pattern[str]:
    if not isinstance(name, str) or not name:
        return re.compile(r'(?!)')
    return _cached_identifier_pattern(name)
PY_FILE_REF_PATTERN = r'(?i)(?<![A-Za-z0-9_./])([A-Za-z0-9_]+\.py)(?![A-Za-z0-9_.])'
CORE_ACTION_VERBS: list[str] = [
    "create", "edit", "delete", "search", "analyze", "convert", "merge", "check",
    "extract", "monitor", "deploy", "backup", "restore", "optimize", "format",
    "calculate", "compare",
    "创建", "编辑", "删除", "搜索", "分析", "转换", "合并", "检查", "提取", "监控",
    "部署", "备份", "恢复", "优化", "格式化", "计算", "对比",
]
SKILL_ACTION_VERBS: frozenset[str] = frozenset(CORE_ACTION_VERBS) | frozenset({
    "diag", "verify", "build", "generate", "process", "handle", "manage",
    "refactor", "诊断", "验证", "构建", "生成", "处理", "管理", "重构",
})
def jaccard(a: set | frozenset, b: set | frozenset) -> float:
    if not isinstance(a, (set, frozenset)) or not isinstance(b, (set, frozenset)):
        return 0.0
    if not a or not b:
        return 0.0
    return len(a & b) / len(a | b)
DOMAIN_KEYWORDS: dict[str, tuple[str, ...]] = {
    "excel": ("excel", "xlsx", "表格"),
    "word": ("word", "docx", "文档"),
    "pdf": ("pdf",),
    "ppt": ("pptx", "ppt", "幻灯片"),
    "code": ("code", "代码", "audit", "审查", "诊断"),
    "skill": ("skill", "技能", "build", "创建"),
}
SLOT_NOISE_CHARS = '。.;；,，、 \t\r\n'
def readable_skill_name(skill_name: str) -> str:
    return normalize_text(skill_name).replace('-', ' ').replace('_', ' ')
def normalize_domain_key(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    return re.sub(r"[\s-]+", "_", value.strip().lower())
def normalize_str(value) -> str:
    return value if isinstance(value, str) else ""
def _clean_str_items(items) -> list[str]:
    return [k.strip() for k in items if isinstance(k, str) and k.strip()]
def _iterable_items(value) -> list:
    try:
        return list(value)
    except TypeError:
        _log.warning("字符串列表载荷非可迭代类型，忽略: %r", value)
        return []
def normalize_str_list(value) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value.strip()] if value.strip() else []
    if isinstance(value, Mapping):
        _log.warning("字符串列表载荷为 Mapping 形态，键不得视为关键词，按空处理: %r",
                       list(value)[:3])
        return []
    if isinstance(value, (set, frozenset)):
        return sorted(_clean_str_items(value))
    return _clean_str_items(_iterable_items(value))
def _keyword_hit(keyword: str, text_lower: str) -> bool:
    if keyword.isascii():
        return re.search(word_pattern(keyword), text_lower) is not None
    return keyword in text_lower
def match_domain(desc_lower: str, domain: str) -> bool:
    if not isinstance(desc_lower, str) or not desc_lower:
        return False
    if not isinstance(domain, str) or not domain.strip():
        return False
    key = normalize_domain_key(domain)
    aliases = DOMAIN_KEYWORDS.get(key) or DOMAIN_KEYWORDS.get(
        domain.strip().lower())
    if aliases:
        return any(_keyword_hit(kw, desc_lower) for kw in aliases)
    probes = {domain.strip().lower(), key,
              key.replace("_", " "), key.replace("_", "-")}
    return any(probe and _keyword_hit(probe, desc_lower) for probe in probes)
@functools.lru_cache(maxsize=512)
def _cached_word_pattern(word: str) -> str:
    esc = re.escape(word)
    return rf"(?<![A-Za-z0-9_]){esc}(?![A-Za-z0-9_])" if word.isascii() else esc
def word_pattern(word: str) -> str:
    if not isinstance(word, str) or not word:
        return r"(?!)"
    return _cached_word_pattern(word)
def _as_path(value: Any) -> Path:
    return value if isinstance(value, Path) else Path(value)
def safe_is_dir(path: Any) -> bool:
    try:
        return _as_path(path).is_dir()
    except (OSError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'safe_is_dir:{type(_e).__name__}')
        return False
def path_exists(path: Any) -> bool:
    try:
        return _as_path(path).exists()
    except (OSError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'path_exists:{type(_e).__name__}')
        return False
def _safe_is_file(path: Any) -> bool:
    try:
        return _as_path(path).is_file()
    except (OSError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'safe_is_file:{type(_e).__name__}')
        return False
def is_skill_dir(path: Path | str) -> bool:
    try:
        candidate = _as_path(path)
    except (OSError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'is_skill_dir:{type(_e).__name__}')
        return False
    return safe_is_dir(candidate) and _safe_is_file(candidate / ENTRY_DOC_NAME)
def is_skill_dir_strict(entry: Path) -> bool:
    try:
        candidate = _as_path(entry)
    except (OSError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'is_skill_dir_strict:{type(_e).__name__}')
        return False
    return (not candidate.name.startswith((".", "_"))
            and safe_is_dir(candidate)
            and _safe_is_file(candidate / ENTRY_DOC_NAME))
def iter_skill_dirs(skills_root: str) -> tuple[list[Path], str]:
    normalized = normalize_path_arg(skills_root)
    if not isinstance(normalized, str):
        if skills_root is not None:
            _log.warning(
                "skills_root 类型 %s 非法（应为 str/PathLike），按空技能清单处理",
                type(skills_root).__name__,
            )
        normalized = None
    if normalized is None or not normalized.strip():
        return [], f"skills_root 不存在或不是目录: {skills_root!r}"
    root = Path(normalized)
    if not root.is_dir():
        return [], f"skills_root 不存在或不是目录: {normalized}"
    try:
        return sorted(
            d for d in root.iterdir()
            if is_skill_dir_strict(d) and not is_audit_skip_dir(d.name)
        ), ""
    except OSError as exc:
        log_swallowed(__name__, exc,
                      context=f'iter_skill_dirs:{type(exc).__name__}')
        return [], f"遍历技能根目录失败: {exc}"
def iter_matching_files(dir_path: str, pattern: str) -> Iterator[str]:
    try:
        base = os.fsdecode(os.fspath(dir_path))
    except (TypeError, ValueError):
        _log.warning("iter_matching_files 目录参数非法: %r，跳过枚举", dir_path)
        return
    if not base or not os.path.isdir(base):
        _log.warning("iter_matching_files 目录不存在或不是目录: %r，跳过枚举",
                     dir_path)
        return
    try:
        filename_pattern = os.fsdecode(os.fspath(pattern))
    except (TypeError, ValueError):
        _log.warning("iter_matching_files 文件名参数非法: %r，跳过枚举", pattern)
        return
    if not filename_pattern:
        _log.warning("iter_matching_files 文件名为空，跳过枚举")
        return
    def _on_walk_error(error: OSError) -> None:
        log_swallowed(__name__, error,
                      context=f'iter_matching_files:{type(error).__name__}')
    for root, dirs, files in os.walk(base, onerror=_on_walk_error):
        dirs[:] = sorted(
            d for d in dirs
            if not (d.lower() in SCAN_COLLECT_PRUNE_DIRS_LOWER
                    or is_audit_skip_dir(d) or is_out_of_scope_dir(d)))
        for filename in sorted(files):
            if filename == filename_pattern:
                yield os.path.join(root, filename)
_TOKEN_SEG_RE = re.compile(r"[\u4e00-\u9fff]+|[^\u4e00-\u9fff]+")
_TOKEN_ASCII_WORD_RE = re.compile(r"[a-z0-9]+")
_TOKEN_UNICODE_WORD_RE = re.compile(r"[^\W_]+")
def has_cjk(text: str) -> bool:
    if not isinstance(text, str):
        return False
    return any("\u4e00" <= c <= "\u9fff" for c in text)
LANGUAGE_ZH = "zh"
LANGUAGE_EN = "en"
def detect_text_language(*texts: Any) -> str:
    for text in texts:
        if has_cjk(text):
            return LANGUAGE_ZH
    return LANGUAGE_EN
def count_words_cn_aware(text: str) -> int:
    text = normalize_text(text)
    if not text:
        return 0
    cn = sum(
        len(match.group(0))
        for match in _TOKEN_SEG_RE.finditer(text)
        if has_cjk(match.group(0))
    )
    en = len(re.findall(r"[A-Za-z]+", text))
    return en + (cn + 1) // 2
def _add_cjk_tokens(tokens: set[str], chars: str | list[str]) -> None:
    if len(chars) == 1:
        tokens.add(chars[0])
    else:
        tokens.update(chars[i] + chars[i + 1] for i in range(len(chars) - 1))
def _add_mixed_token(tokens: set[str], tok: str) -> None:
    for seg_match in _TOKEN_SEG_RE.finditer(tok):
        seg = seg_match.group(0)
        if has_cjk(seg):
            _add_cjk_tokens(tokens, seg)
        else:
            word_re = (_TOKEN_ASCII_WORD_RE if seg.isascii()
                       else _TOKEN_UNICODE_WORD_RE)
            tokens.update(w for w in word_re.findall(seg) if len(w) >= 2)
def tokenize_words(text: str) -> set[str]:
    tokens: set[str] = set()
    for tok in normalize_text(text).lower().split():
        _add_mixed_token(tokens, tok)
    return tokens
def contains_term(term: str, text_lower: str) -> bool:
    if not isinstance(term, str) or not isinstance(text_lower, str):
        return False
    term_lower = term.lower()
    if not term_lower:
        return False
    if term_lower.isascii():
        return re.search(word_pattern(term_lower), text_lower) is not None
    return term_lower in text_lower
_DEFAULT_PRESERVE_CRLF = True
def restore_text_form(
    raw: bytes, text: str, preserve_crlf: bool = _DEFAULT_PRESERVE_CRLF,
) -> str:
    raw = raw or b""
    text = normalize_text(text)
    has_bom = raw.startswith(b"\xef\xbb\xbf")
    use_crlf = preserve_crlf and b"\r\n" in raw
    use_cr = (preserve_crlf and not use_crlf
              and b"\r" in raw and b"\n" not in raw)
    out = normalize_newlines(text)
    if has_bom and out.startswith("\ufeff"):
        out = out[1:]
    if use_crlf:
        out = out.replace("\n", "\r\n")
    elif use_cr:
        out = out.replace("\n", "\r")
    return ("\ufeff" if has_bom else "") + out
def write_text_preserving_form(
    path: str | Path, text: str, raw: bytes = b"",
    preserve_crlf: bool = _DEFAULT_PRESERVE_CRLF,
) -> None:
    with guarded_open(str(path), "w", encoding="utf-8",
                      newline="") as out_file:
        out_file.write(restore_text_form(raw, text, preserve_crlf))


def _desc_length(description: Any) -> int:
    """按折行合并后的可见字符数计算 description 长度（单一来源）。"""
    lines = text_or_empty(description).strip().splitlines()
    return len(" ".join(stripped for line in lines
                        if (stripped := line.strip())))


def _split_keep_endings(text: str) -> tuple[list[str], list[str]]:
    """按 CRLF / CR / LF 切行，逐行保留原始行尾以便原样还原。"""
    lines: list[str] = []
    endings: list[str] = []
    start = 0
    idx = 0
    total = len(text)
    while idx < total:
        ch = text[idx]
        if ch == "\r":
            lines.append(text[start:idx])
            if idx + 1 < total and text[idx + 1] == "\n":
                endings.append("\r\n")
                idx += 2
            else:
                endings.append("\r")
                idx += 1
            start = idx
            continue
        if ch == "\n":
            lines.append(text[start:idx])
            endings.append("\n")
            idx += 1
            start = idx
            continue
        idx += 1
    lines.append(text[start:])
    endings.append("")
    return lines, endings


def _dominant_line_ending(text: str) -> str:
    """返回文本中占优的行尾风格，用于新增行的行尾锚定。"""
    crlf = text.count("\r\n")
    cr = text.count("\r") - crlf
    lf = text.count("\n") - crlf
    if crlf and crlf >= lf and crlf >= cr:
        return "\r\n"
    if cr and cr > lf:
        return "\r"
    return "\n"


def _aligned_prefix_len(orig_lines: list[str], merged_lines: list[str]) -> int:
    """求原文与合并结果的最长相同前缀行数。"""
    limit = min(len(orig_lines), len(merged_lines))
    prefix = 0
    while prefix < limit and orig_lines[prefix] == merged_lines[prefix]:
        prefix += 1
    return prefix


def _aligned_suffix_len(orig_lines: list[str], merged_lines: list[str],
                        prefix: int) -> int:
    """在已确定前缀后求最长相同后缀行数。"""
    limit = min(len(orig_lines), len(merged_lines)) - prefix
    suffix = 0
    while (suffix < limit
           and orig_lines[-1 - suffix] == merged_lines[-1 - suffix]):
        suffix += 1
    return suffix


def _restore_line_endings(original: str, merged_lf: str) -> str:
    """把统一 LF 的合并结果还原为原文的混合行尾；按前/后缀对齐，仅对中间新增行使用锚点行尾。"""
    if "\r" not in original:
        return merged_lf
    orig_lines, orig_endings = _split_keep_endings(original)
    merged_lines = merged_lf.split("\n")
    n_orig, n_merged = len(orig_lines), len(merged_lines)
    prefix = _aligned_prefix_len(orig_lines, merged_lines)
    if prefix == n_orig and n_merged > n_orig:
        prefix -= 1
    suffix = _aligned_suffix_len(orig_lines, merged_lines, prefix)
    anchor = orig_endings[prefix] if prefix < n_orig else ""
    inserted_eol = anchor or _dominant_line_ending(original)
    out = [merged_lines[i] + orig_endings[i] for i in range(prefix)]
    out.extend(merged_lines[i] + inserted_eol
               for i in range(prefix, n_merged - suffix))
    out.extend(merged_lines[n_merged - suffix + k]
               + orig_endings[n_orig - suffix + k] for k in range(suffix))
    out[-1] = merged_lines[-1]
    text = "".join(out)
    if text.replace("\r\n", "\n").replace("\r", "\n") != merged_lf:
        return _dominant_line_ending(original).join(merged_lines)
    return text


def write_markdown_text(md_file: Path, text: str, had_bom: bool,
                         *, newline: str) -> None:
    """受控写盘：显式指定换行策略并保留 BOM，路径经 fs_path_text 归一后交给 guarded_open。"""
    path_text = fs_path_text(md_file)
    if not path_text:
        raise ValueError(
            f"write_markdown_text: 路径为空或类型非法: {md_file!r}")
    body = text.removeprefix("\ufeff")
    with guarded_open(path_text, "w", encoding="utf-8", newline=newline) as fh:
        fh.write(("\ufeff" if had_bom else "") + body)
def normalize_newlines(text: str) -> str:
    text = normalize_text(text)
    if "\r" not in text:
        return text
    return text.replace("\r\n", "\n").replace("\r", "\n")
_DEFAULT_DOC_PROFILE = "template"
_TEMPLATE_MARKER_ALIASES = (
    ("技能能力边界", "skill capability boundary", "capability boundary"),
    ("Agent 决策指引", "agent decision"),
    ("触发条件", "trigger condition"),
    ("快速入门", "quick start", "quickstart", "getting started"),
    ("域总览", "domain overview"),
)
_LOCAL_MD_REF_RE = re.compile(
    r'(?<![\w./:\\-])((?:[\w.-]+/)*[\w.-]+\.md)\b', re.IGNORECASE)
_NON_LOCAL_MD_REF_RE = re.compile(
    r'^(?:[a-z][a-z0-9+.-]*:|[/\\])', re.IGNORECASE)
_GENERIC_BOUNDARY_RE = re.compile(
    r'不支持|不适用|不覆盖|不处理|不具备|仅支持|只支持|适用范围|'
    r'能力边界|限制|limitations?|out\s+of\s+scope|not\s+for|'
    r'capabilit(?:y|ies)\s+boundar(?:y|ies)|boundar(?:y|ies)|'
    r'does\s+not\s+(?:support|handle|cover)|out\s+of\s+range',
    re.IGNORECASE)
_RESOURCE_DIRS = ('scripts', 'references', 'assets')
_RESOURCE_DIR_ALT = '|'.join(_RESOURCE_DIRS)
def resource_dir_names() -> tuple[str, ...]:
    return _RESOURCE_DIRS
_URI_SCHEME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9+.\-]*:")
_WINDOWS_ABS_RE = re.compile(r"^[A-Za-z]:[\\/]")
_REF_DIR_RE = re.compile(
    r"(?<![A-Za-z0-9_+\-.\/])"
    r"(" + _RESOURCE_DIR_ALT + r")"
    r"/",
    re.IGNORECASE,
)
_MD_LINK_RE = re.compile(r"\[([^\]]*)\]\(((?:[^()]|\([^()]*\))+)\)")
_MD_BLANK_LINE_RE = re.compile(r"\r?\n[ \t]*\r?\n")
_MD_LINK_DEST_RE = re.compile(
    r'''^\s*(?:<([^<>\n]*)>|(\S+))\s*(?:["'][^"']*["']|\([^()]*\))?\s*$'''
)
_MD_ESCAPABLE_PUNCT = frozenset("!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~")
def _markdown_unescape(text: str, *, stop_at_suffix: bool = False) -> str:
    out: list[str] = []
    i = 0
    while i < len(text):
        ch = text[i]
        if (ch == "\\" and i + 1 < len(text)
                and text[i + 1] in _MD_ESCAPABLE_PUNCT):
            out.append(text[i + 1])
            i += 2
            continue
        if stop_at_suffix and ch in "#?":
            break
        out.append(ch)
        i += 1
    return "".join(out)
def _ref_escapes_skill_dir(ref: str) -> bool:
    normalized = unquote(normalize_text(ref)).replace("\\", "/")
    if (normalized == ".." or normalized.startswith("/")
            or bool(_WINDOWS_ABS_RE.match(normalized))):
        return True
    depth = 0
    for part in normalized.split("/"):
        if part in ("", "."):
            continue
        if part == "..":
            depth -= 1
            if depth < 0:
                return True
        else:
            depth += 1
    return False
def _has_uri_scheme(target: str) -> bool:
    return bool(_URI_SCHEME_RE.match(target)) and not _WINDOWS_ABS_RE.match(target)
def _link_destination(link_target: str) -> str:
    m = _MD_LINK_DEST_RE.match(link_target)
    if not m:
        return link_target.strip()
    return (m.group(1) if m.group(1) is not None else m.group(2)) or ""
def _iter_local_links(text: str) -> Iterator[tuple[str, str, str]]:
    for match in _MD_LINK_RE.finditer(text):
        if _MD_BLANK_LINE_RE.search(match.group(0)):
            continue
        raw_target = match.group(2)
        target = _link_destination(raw_target)
        unescaped_target = _markdown_unescape(target)
        if not unescaped_target or unescaped_target.startswith(('#', '//')):
            continue
        if _has_uri_scheme(unescaped_target):
            continue
        path = unquote(_markdown_unescape(target, stop_at_suffix=True))
        if path:
            yield match.group(1), raw_target, path
def _md_local_paths(text: str) -> Iterator[str]:
    for _label, _raw_target, path in _iter_local_links(text):
        yield path
def _local_md_refs(body_text: str) -> set:
    prose = strip_fenced_blocks(body_text or "")
    refs = {p for p in _md_local_paths(prose) if p.lower().endswith('.md')}
    # 链接整体（含 [label](target)）都不参与裸引用扫描：label 只是展示文本，
    # `[guide.md](https://…)` 的 label 不是本地引用；本地目标已由 _md_local_paths 收集。
    masked_prose = list(prose)
    for match in _MD_LINK_RE.finditer(prose):
        start, end = match.span(0)
        masked_prose[start:end] = " " * (end - start)
    refs.update(_LOCAL_MD_REF_RE.findall("".join(masked_prose)))
    return {ref for ref in refs
            if not _NON_LOCAL_MD_REF_RE.match(ref)
            and not _ref_escapes_skill_dir(ref)}
def _body_h2_titles(body_text) -> list[str]:
    if not isinstance(body_text, str):
        return []
    return [title for _start, _end, _level, title
            in iter_atx_headings(strip_fenced_blocks(body_text), level=2)]
def _normalize_sections_found(sections_found) -> list:
    if not isinstance(sections_found, (list, tuple)):
        return []
    sections = []
    for entry in sections_found:
        if (isinstance(entry, (list, tuple)) and len(entry) == 2
                and isinstance(entry[0], str) and isinstance(entry[1], str)):
            sections.append((entry[0], entry[1]))
    return sections
def detect_doc_profile(sections_found=None, body_text: str = "") -> str:
    if not isinstance(body_text, str):
        body_text = ""
    sections_found = _normalize_sections_found(sections_found)
    titles = [title for title, _content in sections_found if title.strip()]
    if not titles:
        titles = _body_h2_titles(body_text)
    folded_titles = [title.casefold() for title in titles]
    hits = sum(
        1 for aliases in _TEMPLATE_MARKER_ALIASES
        if any(any(alias.casefold() in title for alias in aliases)
               for title in folded_titles))
    has_discoverability = any(
        "六维可发现性" in title or "discoverability" in folded
        for title, folded in zip(titles, folded_titles, strict=True))
    if hits >= 5 and has_discoverability:
        return _DEFAULT_DOC_PROFILE
    nonempty = sum(1 for line in body_text.splitlines() if line.strip())
    links = _local_md_refs(body_text)
    if not titles and not links:
        return "general"
    if nonempty <= 60 and len(links) >= 2:
        return "router"
    return "general"

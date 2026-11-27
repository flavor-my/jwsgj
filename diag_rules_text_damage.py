from __future__ import annotations  # noqa: I001
import ast
import re
import tokenize
import unicodedata
from collections.abc import Callable
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Any, NamedTuple
from jwsgj.diag_shared_ast_nodes import (
    PY_STDLIB_HINTS,
)
from jwsgj.diag_shared_source_core import (
    ast_split_lines,
)
from jwsgj.diag_shared_source_scan import (
    string_comment_spans,
)
from jwsgj.diag_types_defs import finding_scan_exempt
from jwsgj.diag_types_normalize import (
    is_python_keyword,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
logger = get_module_logger(__name__)
__all__ = [
    "TextDamagePolicy",
    "check_PY09",
    "check_PY10",
    "check_PY11",
    "run_text_checks",
]
logger.info("diag_rules_text_damage 源码文本面破损规则域已加载: %d 项导出",
            len(__all__))
def _source_lines(source: Any) -> list[str]:
    if isinstance(source, str):
        return ast_split_lines(source)
    if source is None or isinstance(source, (bytes, bytearray)):
        return []
    try:
        members = list(source)
    except TypeError:
        return []
    return [line if isinstance(line, str) else "" for line in members]
def _find_quote_close(line: str, start: int, quote: str, triple: bool):
    i = start
    n = len(line)
    tok = quote * 3 if triple else quote
    while i < n:
        if line[i] == "\\":
            i += 2
            continue
        if line.startswith(tok, i):
            return i + len(tok)
        i += 1
    return None
@lru_cache(maxsize=32768)
def _line_string_spans(line: str) -> tuple[tuple[int, int | None, str], ...]:
    spans: list[tuple[int, int | None, str]] = []
    i = 0
    n = len(line)
    while i < n:
        ch = line[i]
        if ch == "\\":
            i += 2
            continue
        if ch not in ("'", '"'):
            i += 1
            continue
        triple = line.startswith(ch * 3, i)
        close = _find_quote_close(
            line, i + (3 if triple else 1), ch, triple=triple)
        spans.append((i, close, ch))
        if close is None:
            return tuple(spans)
        i = close
    return tuple(spans)
def _first_comment_index(line: str) -> int | None:
    i = 0
    for s, _e, _q in _line_string_spans(line):
        if s > i:
            _hash = line.find("#", i, s)
            if _hash >= 0:
                return _hash
        if _e is None:
            return None
        i = _e
    _hash = line.find("#", i)
    return _hash if _hash >= 0 else None
def _line_code_spans(line: str) -> list[tuple[int, int]]:
    cut = _first_comment_index(line)
    if cut is None:
        cut = len(line)
    spans: list[tuple[int, int]] = []
    i = 0
    for s, e, _q in _line_string_spans(line):
        if s >= cut:
            break
        if s > i:
            spans.append((i, s))
        if e is None:
            return spans
        i = e
        if i >= cut:
            break
    if i < cut:
        spans.append((i, cut))
    return spans
def _strip_line_comment(line: str) -> str:
    cut = _first_comment_index(line)
    return line if cut is None else line[:cut]
def _mask_non_code(line: str) -> str:
    masked: list[str] = []
    cursor = 0
    for _cs, _ce in _line_code_spans(line):
        masked.append(" " * max(0, _cs - cursor))
        masked.append(line[_cs:_ce])
        cursor = _ce
    masked.append(" " * max(0, len(line) - cursor))
    return "".join(masked)
def _adjust_bracket_depth(chars: str, depth: int) -> int:
    for _ch in chars:
        if _ch in "([{":
            depth += 1
        elif _ch in ")]}":
            depth = max(0, depth - 1)
    return depth
def _pos_outside_string(line: str, pos: int, spans: list) -> bool:
    _n = len(line)
    return not any(s <= pos < (e if e is not None else _n)
                   for s, e, _q in spans)
def _has_marker_outside_string(line: str, marker: str) -> bool:
    _spans = _line_string_spans(line)
    _pos = line.find(marker)
    while _pos >= 0:
        if _pos_outside_string(line, _pos, _spans):
            return True
        _pos = line.find(marker, _pos + len(marker))
    return False
def _find_open_triple(text: str) -> str | None:
    for start, end, quote in _line_string_spans(_strip_line_comment(text)):
        if end is None and text.startswith(quote * 3, start):
            return quote
    return None
def _continued_string_quote(text: str) -> str | None:
    _segment = _strip_line_comment(text)
    _spans = _line_string_spans(_segment)
    if not _spans:
        return None
    _start, _end, quote = _spans[-1]
    if _end is not None or not _has_line_continuation(_segment):
        return None
    if _segment.startswith(quote * 3, _start):
        return None
    return quote
def _cross_line_string_state(text: str) -> tuple[str | None, str | None]:
    _segment = _strip_line_comment(text)
    _open = _find_open_triple(_segment)
    if _open is not None:
        return "triple", _open
    _quote = _continued_string_quote(_segment)
    if _quote is not None:
        return "line", _quote
    return None, None
def _scan_triple_quotes(lines) -> tuple:
    _mode = None
    _quote = None
    quoted = set()
    close_positions: dict = {}
    for i, line in enumerate(lines, 1):
        if _mode is not None:
            quoted.add(i)
            close = _find_quote_close(
                line, 0, _quote, triple=_mode == "triple")
            if close is None:
                continue
            close_positions[i] = close
            _mode, _quote = _cross_line_string_state(line[close:])
            continue
        if line.strip().startswith("#"):
            continue
        _mode, _quote = _cross_line_string_state(line)
    return quoted, close_positions
def _line_scan_view(line: str, lineno: int, triple_quoted: set,
                    close_positions: dict) -> tuple:
    if lineno in triple_quoted:
        _close = close_positions.get(lineno)
        if _close is None:
            return None, []
        _scan_text = line[_close:]
        return _scan_text, _line_code_spans(_scan_text)
    return line, _line_code_spans(line)
def _position_in_spans(position: int, spans) -> bool:
    return any(start <= position < end for start, end in spans)
def _fstring_degraded_fullwidth(code: str, characters) -> dict[int, set[str]]:
    start_type = getattr(tokenize, "FSTRING_START", -1)
    end_type = getattr(tokenize, "FSTRING_END", -1)
    if start_type < 0 or end_type < 0:
        return {}
    literal_types = frozenset({
        tokenize.STRING, tokenize.COMMENT,
        getattr(tokenize, "FSTRING_MIDDLE", -1),
    })
    frames: list[int] = []
    hits: dict[int, set[str]] = {}
    try:
        for tok in tokenize.generate_tokens(_source_readline(code)):
            if tok.type == start_type:
                frames.append(0)
                continue
            if tok.type == end_type:
                if frames:
                    frames.pop()
                continue
            if not frames:
                continue
            if tok.type == tokenize.OP and tok.string == "{":
                frames[-1] += 1
                continue
            if tok.type == tokenize.OP and tok.string == "}":
                if frames[-1] > 0:
                    frames[-1] -= 1
                continue
            if not frames[-1] or tok.type in literal_types:
                continue
            row, column = tok.start
            for char in tok.string:
                if char == "\n":
                    row += 1
                    column = 0
                    continue
                if char in characters:
                    hits.setdefault(row, set()).add(char)
                column += 1
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as exc:
        logger.debug("f-string partial token scan stopped: %s", exc)
    return hits
def _fstring_expression_fullwidth(lines: list[str], scan_state: tuple,
                                  characters) -> dict[int, set[str]]:
    code = "\n".join(lines)
    literal_spans = string_comment_spans(code)
    if literal_spans is None:
        return _fstring_degraded_fullwidth(code, characters)
    quoted, close_positions = scan_state
    hits: dict[int, set[str]] = {}
    for lineno, line in enumerate(lines, 1):
        scan_text, code_spans = _line_scan_view(
            line, lineno, quoted, close_positions)
        base = len(line) - len(scan_text) if scan_text is not None else 0
        existing_code = [(base + start, base + end)
                         for start, end in code_spans]
        masked_literals = literal_spans.get(lineno, ())
        for position, char in enumerate(line):
            if (char not in characters
                    or _position_in_spans(position, existing_code)
                    or _position_in_spans(position, masked_literals)):
                continue
            hits.setdefault(lineno, set()).add(char)
    return hits
def _code_text_of(line_view: tuple) -> str:
    scan_text, code_spans = line_view
    if scan_text is None:
        return ""
    return "".join(scan_text[start:end] for start, end in code_spans)
def _has_line_continuation(code_text: str) -> bool:
    _code_tail = _strip_line_comment(code_text).rstrip()
    _bs_run = len(_code_tail) - len(_code_tail.rstrip("\\"))
    return _bs_run % 2 == 1
def _previous_code_line(lines, lineno: int) -> int:
    pl = lineno - 1
    while pl > 0 and (not lines[pl - 1].strip()
                      or lines[pl - 1].strip().startswith("#")):
        pl -= 1
    return pl
def _indent_columns(line: str) -> int:
    leading = line[:len(line) - len(line.lstrip())]
    return len(leading.expandtabs(8))
def _finding(rule_id: str, severity: str, lineno: int, message: str,
             suggestion: str, category: str) -> dict:
    return {"rule_id": rule_id, "severity": severity, "line": lineno,
            "message": message, "suggestion": suggestion,
            "category": category}
_FULLWIDTH_MAP: dict = {
    "（": ("全角左括号", "("),
    "）": ("全角右括号", ")"),
    "，": ("全角逗号", ","),
    "；": ("全角分号", ";"),
    "：": ("全角冒号", ":"),
    "＝": ("全角等号", "="),
    "？": ("全角问号", "?"),
    "！": ("全角叹号", "!"),
    "“": ("全角左引号（双）", '"'),
    "”": ("全角右引号（双）", '"'),
    "‘": ("全角左单引号", "'"),
    "’": ("全角右单引号", "'"),
    "【": ("全角左方括号", "["),
    "】": ("全角右方括号", "]"),
    "｛": ("全角左花括号", "{"),
    "｝": ("全角右花括号", "}"),
    "、": ("全角顿号", ","),
    "。": ("全角句号", "."),
    "．": ("全角句点", "."),
}
_PY09_BRACKET_CHARS = frozenset("\uff08\uff09")
_PY09_BRACKETS = tuple(
    (char, desc) for char, (desc, _hw) in _FULLWIDTH_MAP.items()
    if char in _PY09_BRACKET_CHARS)
def _py09_line_fullwidth(code_part: str) -> str | None:
    return next((name for char, name in _PY09_BRACKETS if char in code_part), None)
def _code_segments_excluding_spans(
        line: str, scan_text: str, code_spans: list,
        excluded_spans) -> list[str]:
    base = len(line) - len(scan_text)
    return [
        "".join(
            char for offset, char in enumerate(scan_text[start:end], start)
            if not _position_in_spans(base + offset, excluded_spans))
        for start, end in code_spans
    ]
def _py09_finding(line_num: int, name: str, filepath: Any) -> dict:
    finding = _finding(
        "PY-09", "P1", line_num,
        (f"PY-09: 代码位检测到{name}，解释器会将其视为非法字符，"
         f"常导致语法错误。"),
        "在 Python 代码中使用半角括号 ( )，字符串内可保留全角",
        "syntax")
    finding["file"] = filepath
    finding["rule_ref"] = "PEP 8 / Python 语法：代码位全角标点"
    return finding
def check_PY09(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    lines = _source_lines(source_lines)
    if not lines:
        return issues
    scan_state = _scan_triple_quotes(lines)
    quoted, close_positions = scan_state
    literal_spans = string_comment_spans("\n".join(lines))
    fstring_hits = _fstring_expression_fullwidth(
        lines, scan_state, _PY09_BRACKET_CHARS)
    for line_num, line in enumerate(lines, start=1):
        # 不能按行首 # 整行跳过：多行字符串内以 # 开头的行可能在行内闭合，
        # 闭合后的代码位仍需检查（纯注释行由 _line_code_spans 自然得到空代码段）。
        scan_text, code_spans = _line_scan_view(
            line, line_num, quoted, close_positions)
        _name = None
        if scan_text is not None:
            excluded = (literal_spans.get(line_num, ())
                        if literal_spans is not None else ())
            code_parts = _code_segments_excluding_spans(
                line, scan_text, code_spans, excluded)
            for code_part in code_parts:
                _name = _py09_line_fullwidth(code_part)
                if _name is not None:
                    break
        if _name is None:
            _name = next(
                (name for char, name in _PY09_BRACKETS
                 if char in fstring_hits.get(line_num, ())),
                None)
        if _name is not None:
            issues.append(_py09_finding(line_num, _name, filepath))
    return issues
def _py10_hits(source_lines) -> list[tuple[int, int]]:
    hits = []
    for idx, line in enumerate(source_lines, start=1):
        code_text = _strip_line_comment(line)
        if "\\\\n" in code_text:
            hits.append((idx, code_text.count("\\\\n")))
    return hits
def check_PY10(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    issues = []
    lines = _source_lines(source_lines)
    if not lines:
        return issues
    _hits = _py10_hits(lines)
    _total = sum(count for _lineno, count in _hits)
    if _total <= 0:
        return issues
    issue = _finding(
        "PY-10", "P3", _hits[0][0],
        f"检测到双反斜杠转义序列 {_total} 处,可能存在误用",
        "检查是否需要原始字符串 r'' 或正则转义", "quality")
    issue["file"] = filepath
    issues.append(issue)
    return issues
def _gf01_issue(lineno: int, desc: str, hw: str) -> dict:
    return _finding("GF-01", "P1", lineno,
                    f"全角标点混入: {desc} 出现在代码中(非字符串内)",
                    f"替换为 {hw}", "syntax")
def _gf01_line_issues(lineno: int, line: str, quoted: set,
                      close_positions: dict, fstring_chars=frozenset(),
                      literal_spans=()) -> list:
    scan_text, code_spans = _line_scan_view(
        line, lineno, quoted, close_positions)
    if scan_text is None:
        scan_text, code_spans = "", []
    code_parts = _code_segments_excluding_spans(
        line, scan_text, code_spans, literal_spans)
    return [
        _gf01_issue(lineno, desc, hw)
        for fw, (desc, hw) in _FULLWIDTH_MAP.items()
        if fw in fstring_chars
        or any(fw in code_part for code_part in code_parts)
    ]
def _check_fullwidth(code: Any) -> Any:
    lines = _source_lines(code)
    scan_state = _scan_triple_quotes(lines)
    quoted, close_positions = scan_state
    literal_spans = string_comment_spans("\n".join(lines))
    fstring_hits = _fstring_expression_fullwidth(
        lines, scan_state, _FULLWIDTH_MAP)
    issues = []
    for lineno, line in enumerate(lines, 1):
        # 同 check_PY09：以 # 开头但行内闭合多行字符串的行，闭合后的代码位仍需检查。
        issues.extend(_gf01_line_issues(
            lineno, line, quoted, close_positions,
            fstring_hits.get(lineno, frozenset()),
            literal_spans.get(lineno, ()) if literal_spans is not None else ()))
    return issues
def _gf03_is_repeat(curr: str, prev: str) -> bool:
    curr_text = curr.strip()
    return (bool(curr_text) and curr_text == prev.strip()
            and _indent_columns(curr) == _indent_columns(prev)
            and not curr_text.startswith(("#", "@", "import ", "from ")))
def _gf03_streak_issue(streak_start: int, streak: int) -> dict:
    return _finding("GF-03", "P2", streak_start + 1,
                    f"连续重复语句: 行{streak_start + 1}起连续{streak}行相同",
                    f"移除{streak - 1}行重复,保留第{streak_start + 1}行",
                    "duplication")
def _gf03_statement_start_lines(lines: list, scan_state: tuple) -> set:
    starts: set = set()
    quoted, close_positions = scan_state
    depth = 0
    continued = False
    for lineno, line in enumerate(lines, 1):
        stripped = line.strip()
        if (depth == 0 and not continued and lineno not in quoted
                and stripped and not stripped.startswith("#")):
            starts.add(lineno)
        code_text = _code_text_of(_line_scan_view(
            line, lineno, quoted, close_positions))
        depth = _adjust_bracket_depth(code_text, depth)
        continued = _has_line_continuation(code_text)
    return starts
def _check_duplicate_lines(code: Any) -> Any:
    issues = []
    lines = _source_lines(code)
    scan_state = _scan_triple_quotes(lines)
    quoted = scan_state[0]
    starts = _gf03_statement_start_lines(lines, scan_state)
    streak_start = 0
    streak = 1
    for i in range(1, len(lines)):
        if ((i + 1) in quoted or (i + 1) not in starts
                or i not in starts):
            if streak >= 3:
                issues.append(_gf03_streak_issue(streak_start, streak))
            streak = 1
            continue
        if _gf03_is_repeat(lines[i], lines[i - 1]):
            streak += 1
            if streak == 3:
                streak_start = i - 2
            continue
        if streak >= 3:
            issues.append(_gf03_streak_issue(streak_start, streak))
        streak = 1
    if streak >= 3:
        issues.append(_gf03_streak_issue(streak_start, streak))
    return issues
_DEFAULT_LAZY_MARKERS: tuple[str, ...] = ("lazy",)
_DEFAULT_RESIDUE_MARKERS: tuple[str, ...] = ("[AUTOFIX]",)
def _policy_marker_tuple(markers: Any,
                         fallback: tuple[str, ...]) -> tuple[str, ...]:
    if isinstance(markers, str):
        members: tuple = (markers,)
    else:
        try:
            members = tuple(markers)
        except TypeError:
            return fallback
    cleaned = tuple(m for m in members if isinstance(m, str) and m)
    return cleaned or fallback
@dataclass(frozen=True)
class TextDamagePolicy:
    lazy_markers: tuple[str, ...] = _DEFAULT_LAZY_MARKERS
    residue_markers: tuple[str, ...] = _DEFAULT_RESIDUE_MARKERS
    def __post_init__(self) -> None:
        object.__setattr__(
            self, "lazy_markers",
            _policy_marker_tuple(self.lazy_markers, _DEFAULT_LAZY_MARKERS))
        object.__setattr__(
            self, "residue_markers",
            _policy_marker_tuple(self.residue_markers,
                                 _DEFAULT_RESIDUE_MARKERS))
_DEFAULT_TEXT_DAMAGE_POLICY = TextDamagePolicy()
@lru_cache(maxsize=16)
def _lazy_marker_re(markers: tuple[str, ...]) -> re.Pattern:
    alternation = "|".join(re.escape(marker) for marker in markers)
    return re.compile(rf"@(?:{alternation})(?!\w)")
def _gf04_marker(line: str, policy: TextDamagePolicy) -> str | None:
    if len(line) - len(line.lstrip()) != 0:
        return None
    stripped = line.strip()
    marker_re = _lazy_marker_re(policy.lazy_markers)
    if stripped.startswith("#"):
        match = marker_re.search(stripped)
    else:
        match = marker_re.match(_mask_non_code(line).strip())
    return match.group(0) if match is not None else None
def _gf04_probe_module(probe: str) -> str | None:
    stripped = probe.strip()
    if stripped.startswith("#"):
        return None
    relative = re.match(
        r"from\s+\.+([\w.]*)\s+import\s+"
        r"(?:\(?\s*([A-Za-z_]\w*)|\*)", stripped)
    if relative is not None:
        module = relative.group(1) or relative.group(2) or ""
        return module.split(".")[0] or None
    match = re.match(r"(?:import\s+|from\s+)([\w.]+)", stripped)
    if match is None:
        return None
    module = match.group(1).lstrip(".").split(".")[0]
    if not module or module in PY_STDLIB_HINTS:
        return None
    return module
def _gf04_probe_following_import(lines: list, quoted: set,
                                 lineno: int) -> str | None:
    for next_lineno in range(lineno + 1, len(lines) + 1):
        if next_lineno in quoted:
            continue
        _probe = lines[next_lineno - 1]
        if _probe[:1] in (" ", "\t"):
            continue
        if not _probe.strip() or _probe.lstrip().startswith("#"):
            continue
        return _gf04_probe_module(_probe)
    return None
def _check_redundant_lazy(code: Any, policy: TextDamagePolicy) -> Any:
    issues = []
    lines = _source_lines(code)
    _quoted = _scan_triple_quotes(lines)[0]
    for lineno, line in enumerate(lines, 1):
        if lineno in _quoted:
            continue
        marker = _gf04_marker(line, policy)
        if marker is not None:
            mod = _gf04_probe_following_import(lines, _quoted, lineno)
            if mod is not None:
                issues.append(_finding(
                    "GF-04", "P2", lineno,
                    f'{marker}标记的模块"{mod}"需验证是否为同包内模块',
                    f"若为同包内模块则移除{marker}改为直接导入", "lazy_load"))
    return issues
@dataclass
class _Gf10State:
    bracket_depth: int = 0
    indent_stack: list = field(default_factory=lambda: [0])
    logical_tail: str = ""
    opens_block: bool = False
    in_line_join: bool = False
    quoted: set = field(default_factory=set)
    close_positions: dict = field(default_factory=dict)
def _gf10_hanging_finding(lineno: int, indent: int, expected: int) -> dict:
    return _finding(
        "GF-10", "P0", lineno,
        f"悬挂缩进: 第{lineno}行出现{indent}列缩进,与当前块层级{expected}列不匹配",
        "检查上方是否移除了 try:/if:/for: 等块开头,调整缩进至正确层级",
        "indentation")
def _gf10_indent_finding(state: _Gf10State, indent: int,
                         lineno: int) -> dict | None:
    stack = state.indent_stack
    if indent > stack[-1]:
        if state.opens_block:
            stack.append(indent)
            return None
        return _gf10_hanging_finding(lineno, indent, stack[-1])
    while len(stack) > 1 and indent < stack[-1]:
        stack.pop()
    if indent == stack[-1]:
        return None
    return _gf10_hanging_finding(lineno, indent, stack[-1])
def _gf10_step(state: _Gf10State, lineno: int, line: str) -> dict | None:
    stripped = line.strip()
    if not stripped or stripped.startswith("#"):
        return None
    quoted_line = lineno in state.quoted
    if quoted_line and state.close_positions.get(lineno) is None:
        return None
    line_start_depth = state.bracket_depth
    join_tail = state.in_line_join
    code_text = _code_text_of(_line_scan_view(
        line, lineno, state.quoted, state.close_positions))
    state.bracket_depth = _adjust_bracket_depth(code_text, state.bracket_depth)
    state.in_line_join = _has_line_continuation(code_text)
    state.logical_tail = (state.logical_tail + code_text)[-256:]
    if join_tail or line_start_depth > 0:
        if state.bracket_depth or state.in_line_join:
            return None
        state.opens_block = state.logical_tail.rstrip().endswith(":")
        state.logical_tail = ""
        return None
    if quoted_line:
        state.opens_block = state.logical_tail.rstrip().endswith(":")
        state.logical_tail = ""
        return None
    finding = _gf10_indent_finding(state, _indent_columns(line), lineno)
    state.opens_block = state.logical_tail.rstrip().endswith(":")
    state.logical_tail = ""
    return finding
def _check_hanging_indent(code: Any) -> Any:
    lines = _source_lines(code)
    quoted, close_positions = _scan_triple_quotes(lines)
    state = _Gf10State(quoted=quoted, close_positions=close_positions)
    for lineno, line in enumerate(lines, 1):
        finding = _gf10_step(state, lineno, line)
        if finding is not None:
            return [finding]
    return []
_GF06_TRY_RE = re.compile(r"^try\s*:")
_GF06_EXCEPT_RE = re.compile(r"^except\b")
def _gf06_misindent_issue(lineno: int, indent: int, try_lineno: int,
                          try_indent: int) -> dict:
    return _finding(
        "GF-06", "P0", lineno,
        f"except缩进与所属try不匹配: 第{lineno}行缩进{indent}列, "
        f"第{try_lineno}行的try:缩进{try_indent}列",
        f"把except对齐到第{try_lineno}行try:的{try_indent}列; "
        f"仅当try:确实已被删除时才整体移除except块",
        "indentation")
def _check_orphaned_except(code: Any) -> Any:
    issues = []
    lines = _source_lines(code)
    scan_state = _scan_triple_quotes(lines)
    open_tries: list[tuple[int, int]] = []
    for lineno in sorted(_gf03_statement_start_lines(lines, scan_state)):
        line = lines[lineno - 1]
        stripped = line.strip()
        indent = _indent_columns(line)
        if _GF06_EXCEPT_RE.match(stripped):
            open_tries = [entry for entry in open_tries if entry[0] <= indent]
            if not open_tries:
                issues.append(_finding(
                    "GF-06", "P0", lineno,
                    "孤立except块: try:已移除但except残留,将导致IndentationError",
                    "移除整个except块（包括其处理代码）", "syntax"))
                continue
            try_indent, try_lineno = open_tries[-1]
            if try_indent < indent:
                issues.append(_gf06_misindent_issue(
                    lineno, indent, try_lineno, try_indent))
            continue
        if _GF06_TRY_RE.match(stripped):
            open_tries = [entry for entry in open_tries if entry[0] < indent]
            open_tries.append((indent, lineno))
            continue
        open_tries = [entry for entry in open_tries if entry[0] < indent]
    return issues
_LAMBDA_WORD_RE = re.compile(r"\blambda\b")
def _gf07_lambda_default_exempts(match_text: str, eq_off: int) -> bool:
    _lam_hits = list(_LAMBDA_WORD_RE.finditer(match_text[:eq_off]))
    return bool(_lam_hits) and ":" not in match_text[_lam_hits[-1].end():eq_off]
def _gf07_call_kwarg_exempts(stripped: str, m_start: int) -> bool:
    line_start = stripped.rfind("\n", 0, m_start) + 1
    search_start = line_start
    if not stripped[line_start:m_start].strip():
        prefix = stripped[:line_start]
        continued = (_adjust_bracket_depth(prefix, 0) > 0
                     or _has_line_continuation(prefix))
        if continued:
            search_start = 0
    before = re.sub(
        r"\\\r?\n[ \t]*", "", stripped[search_start:m_start]).rstrip()
    if before.endswith((")", "]", "}")):
        return True
    pre_word = re.search(r"[A-Za-z_]\w*$", before)
    if pre_word is None:
        return False
    return not is_python_keyword(pre_word.group())
_GF07_INSERT_CALL_RE = re.compile(
    r"(?<![\w.])(?:sys|_sys)\.path\.insert\(")
_GF07_TOKEN_SKIP = frozenset({
    tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
    tokenize.INDENT, tokenize.DEDENT,
})
def _gf07_is_zero_expression(tokens: list) -> bool:
    if not tokens:
        return False
    allowed_ops = {"+", "-", "(", ")"}
    if any(not (tok.type == tokenize.NUMBER
                or (tok.type == tokenize.OP and tok.string in allowed_ops))
           for tok in tokens):
        return False
    expression = " ".join(tok.string for tok in tokens)
    def _evaluate(node: ast.AST) -> int | float | complex:
        if isinstance(node, ast.Expression):
            return _evaluate(node.body)
        if (isinstance(node, ast.Constant)
                and isinstance(node.value, (int, float, complex))):
            return node.value
        if (isinstance(node, ast.UnaryOp)
                and isinstance(node.op, (ast.UAdd, ast.USub))):
            value = _evaluate(node.operand)
            return value if isinstance(node.op, ast.UAdd) else -value
        if (isinstance(node, ast.BinOp)
                and isinstance(node.op, (ast.Add, ast.Sub))):
            left, right = _evaluate(node.left), _evaluate(node.right)
            return left + right if isinstance(node.op, ast.Add) else left - right
        raise ValueError("非受支持的数值表达式")
    try:
        value = _evaluate(ast.parse(expression, mode="eval"))
    except PARSE_DEGRADE_EXC as exc:
        log_swallowed(__name__, exc, context="_gf07_is_zero_expression")
        return False
    return value == 0
def _gf07_index_segment_is_zero(segment: list) -> bool:
    if len(segment) < 3:
        return False
    name, equals = segment[:2]
    return (name.type == tokenize.NAME
            and unicodedata.normalize("NFKC", name.string) == "index"
            and equals.type == tokenize.OP and equals.string == "="
            and _gf07_is_zero_expression(segment[2:]))
def _gf07_insert_has_index_keyword(arguments: str) -> bool:
    try:
        tokens = [
            tok for tok in tokenize.generate_tokens(_source_readline(
                f"({arguments})"))
            if tok.type not in _GF07_TOKEN_SKIP
        ]
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as exc:
        log_swallowed(
            __name__, exc, context="_gf07_insert_has_index_keyword")
        return False
    depth = 0
    segment: list = []
    for tok in tokens:
        if tok.type == tokenize.OP and tok.string in "([{":
            depth += 1
            if depth == 1:
                segment = []
                continue
        elif tok.type == tokenize.OP and tok.string in ")]}":
            if depth == 1 and tok.string == ")":
                return _gf07_index_segment_is_zero(segment)
            depth = max(0, depth - 1)
            if depth == 0:
                break
        if depth < 1:
            continue
        if depth == 1 and tok.type == tokenize.OP and tok.string == ",":
            if _gf07_index_segment_is_zero(segment):
                return True
            segment = []
            continue
        segment.append(tok)
    return False
def _gf07_insert_residue_offset(stripped: str) -> int | None:
    for call in _GF07_INSERT_CALL_RE.finditer(stripped):
        depth = 1
        close = None
        for offset, char in enumerate(stripped[call.end():]):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    close = call.end() + offset
                    break
        if close is None:
            continue
        if _gf07_insert_has_index_keyword(stripped[call.end():close]):
            return call.start()
    return None
def _gf07_check_insert_residue(scan: _Gf07Scan) -> list:
    issues = []
    stripped = scan.stripped
    offset = _gf07_insert_residue_offset(stripped)
    if offset is None:
        return issues
    issues.append(_finding(
        "GF-07", "P0", stripped.count("\n", 0, offset) + 1,
        "正则替换残留: sys.path.insert 调用带有无效 keyword arg index=0",
        "替换为标准 if VAR not in sys.path: sys.path.insert(0, VAR)",
        "syntax"))
    return issues
class _Gf07Scan(NamedTuple):
    stripped: str
def _mask_triple_line(line: str, close) -> str:
    if close is None:
        return " " * len(line)
    return " " * close + _mask_non_code(line[close:])
def _gf07_code_view(lines: list[str], quoted: set,
                    close_positions: dict) -> list[str]:
    literal_spans = string_comment_spans("\n".join(lines))
    if literal_spans is not None:
        projected: list[str] = []
        for lineno, line in enumerate(lines, 1):
            chars = list(line)
            for start, end in literal_spans.get(lineno, ()):
                start = max(0, min(len(chars), start))
                end = max(start, min(len(chars), end))
                chars[start:end] = " " * (end - start)
            projected.append("".join(chars))
        return projected
    return [
        (_mask_triple_line(line, close_positions.get(lineno))
         if lineno in quoted else _mask_non_code(line))
        for lineno, line in enumerate(lines, 1)
    ]
def _gf07_prepare_scan(code: Any) -> _Gf07Scan:
    _lines = _source_lines(code)
    _quoted, _close_positions = _scan_triple_quotes(_lines)
    _code_lines = _gf07_code_view(_lines, _quoted, _close_positions)
    return _Gf07Scan("\n".join(_code_lines))
def _gf07_assignment_exempt(scan: _Gf07Scan, match_text: str,
                            start: int) -> bool:
    stripped = scan.stripped
    _eq_m = re.search(r"\w\s*=(?!=)", match_text)
    _eq_off = _eq_m.end() if _eq_m else 0
    if _gf07_lambda_default_exempts(match_text, _eq_off):
        return True
    return _gf07_call_kwarg_exempts(stripped, start)
def _check_regex_substitution_damage(code: Any) -> Any:
    issues = []
    assign_in_paren = r"\([^()]*?\b\w+\s*=\s*[^=](?:[^()]|\([^()]*\))*?\)"
    scan = _gf07_prepare_scan(code)
    for match in re.finditer(rf"(?=({assign_in_paren}))", scan.stripped):
        match_text = match.group(1)
        if _gf07_assignment_exempt(scan, match_text, match.start()):
            continue
        issues.append(_finding(
            "GF-07", "P0",
            scan.stripped.count("\n", 0, match.start()) + 1,
            "疑似正则替换副作用: 括号内出现赋值语法",
            "将括号内的赋值改写为独立 if 语句, 恢复正确语法",
            "syntax"))
        break
    issues.extend(_gf07_check_insert_residue(scan))
    return issues
def _gf12_syntax_error_issue(code: Any) -> dict | None:
    try:
        compile(code, "<gf12>", "exec")
        return None
    except PARSE_DEGRADE_EXC as e:
        logger.debug("suppressed parse failure: %s", e)
        _se_line = getattr(e, "lineno", None) or 1
        _se_msg = getattr(e, "msg", None) or str(e)
        return _finding(
            "GF-12", "P0", _se_line,
            f"Broken artifact: syntax error ({_se_msg}), module unimportable",
            f"Fix syntax error at L{_se_line}", "artifact_integrity")
def _gf12_marker_hit(line: str, policy: TextDamagePolicy) -> str | None:
    for marker in policy.residue_markers:
        if marker in line and _has_marker_outside_string(line, marker):
            return marker
    return None
def _gf12_autofix_issue(lineno: int, marker: str) -> dict:
    return _finding(
        "GF-12", "P1", lineno + 1,
        f"{marker} residue: import still indented after the recorded fix",
        "De-indent import to module level (0 spaces)", "artifact_integrity")
def _gf12_residue_evidence(lines: list, lineno: int) -> bool:
    next_line = lines[lineno]
    if not (next_line.strip().startswith(("import ", "from "))
            and _indent_columns(next_line) > 0):
        return False
    prev_lineno = _previous_code_line(lines, lineno)
    if prev_lineno <= 0:
        return True
    prev_line = lines[prev_lineno - 1]
    if _strip_line_comment(prev_line).rstrip().endswith(":"):
        return False
    return _indent_columns(prev_line) == 0
def _gf12_import_nested_in_ast(code: Any, lineno: int) -> bool | None:
    lines = _source_lines(code)
    if lineno <= 0 or lineno > len(lines):
        return None
    try:
        tree = ast.parse("\n".join(lines[:lineno]))
    except PARSE_DEGRADE_EXC as exc:
        logger.debug("residue import scope parse failed: %s", exc)
        if (isinstance(exc, IndentationError)
                and getattr(exc, "lineno", None) == lineno):
            return False
        return None
    top_level = {id(node) for node in tree.body}
    imports = [
        node for node in walk_nodes(tree)
        if (isinstance(node, (ast.Import, ast.ImportFrom))
            and node.lineno == lineno)
    ]
    if not imports:
        return None
    return any(id(node) not in top_level for node in imports)
def _gf12_autofix_residue_issues(
        code: Any, policy: TextDamagePolicy) -> list:
    issues = []
    lines = _source_lines(code)
    quoted = _scan_triple_quotes(lines)[0]
    for lineno, line in enumerate(lines, 1):
        if lineno in quoted:
            continue
        if lineno >= len(lines):
            continue
        marker = _gf12_marker_hit(line, policy)
        if marker is None or not _gf12_residue_evidence(lines, lineno):
            continue
        if _gf12_import_nested_in_ast(code, lineno + 1) is not False:
            continue
        issues.append(_gf12_autofix_issue(lineno, marker))
        break
    return issues
def _check_artifact_integrity(
        code: Any, policy: TextDamagePolicy,
        duplicate_argument_lines=()) -> Any:
    issues = []
    _issue = _gf12_syntax_error_issue(code)
    if (_issue is not None
            and not (_issue.get('line') in duplicate_argument_lines
                     and 'duplicate argument' in str(
                         _issue.get('message', '')).lower())):
        issues.append(_issue)
    issues.extend(_gf12_autofix_residue_issues(code, policy))
    return issues
_PY11_TOKEN_SKIP = frozenset({
    tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
    tokenize.DEDENT,
})
_PY11_SIG_SCAN_SKIP = _PY11_TOKEN_SKIP - {tokenize.NEWLINE}
def _source_readline(text: str) -> Callable[[], str]:
    pending = text.replace("\r\n", "\n").replace("\r", "\n")
    def _readline() -> str:
        nonlocal pending
        if not pending:
            return ""
        line, sep, pending = pending.partition("\n")
        return line + sep
    return _readline
def _py11_param_from_segment(segment: list) -> tuple[str, int] | None:
    tokens = [tok for tok in segment if tok.type not in _PY11_TOKEN_SKIP]
    index = 0
    while index < len(tokens):
        tok = tokens[index]
        if tok.type == tokenize.OP and tok.string in ('*', '**', '/', '('):
            index += 1
            continue
        break
    if index >= len(tokens):
        return None
    tok = tokens[index]
    if tok.type != tokenize.NAME or not tok.string.isidentifier():
        return None
    return tok.string, tok.start[0]
def _py11_parse_param_list(tokens: list, open_index: int) -> tuple[list, int]:
    params: list[tuple[str, int]] = []
    segment: list = []
    depth = 0
    lambda_depth = 0
    for index in range(open_index, len(tokens)):
        tok = tokens[index]
        if tok.type == tokenize.OP:
            if tok.string in '([{':
                depth += 1
            elif tok.string in ')]}':
                depth -= 1
                if depth == 0:
                    found = _py11_param_from_segment(segment)
                    if found is not None:
                        params.append(found)
                    return params, index
            elif tok.string == ',' and depth == 1 and lambda_depth == 0:
                found = _py11_param_from_segment(segment)
                if found is not None:
                    params.append(found)
                segment = []
                continue
            elif tok.string == ':' and depth == 1 and lambda_depth > 0:
                lambda_depth -= 1
        elif (tok.type == tokenize.NAME and tok.string == 'lambda'
              and depth == 1):
            lambda_depth += 1
        segment.append(tok)
    return params, len(tokens) - 1
def _py11_duplicate_findings(params: list) -> list:
    seen: dict[str, int] = {}
    issues = []
    for name, lineno in params:
        normalized_name = unicodedata.normalize("NFKC", name)
        if normalized_name not in seen:
            seen[normalized_name] = lineno
            continue
        issues.append(_finding(
            "PY-11", "P0", lineno,
            f"重复参数名 '{name}': 同一函数签名内同名参数重复定义, "
            "Python 无法导入该模块",
            f"删除或重命名重复参数 '{name}', 保持签名唯一",
            "syntax"))
    return issues
def _py11_def_name_index(tokens: list, start: int) -> int:
    for index in range(start, len(tokens)):
        tok = tokens[index]
        if tok.type == tokenize.NEWLINE:
            return -1
        if tok.type in _PY11_SIG_SCAN_SKIP:
            continue
        return index if tok.type == tokenize.NAME else -1
    return -1
def _py11_signature_open_index(tokens: list, start: int) -> int:
    type_params_seen = False
    depth = 0
    for index in range(start, len(tokens)):
        tok = tokens[index]
        if tok.type == tokenize.NEWLINE:
            return -1
        if tok.type in _PY11_SIG_SCAN_SKIP:
            continue
        if depth:
            if tok.type == tokenize.OP and tok.string in '([{':
                depth += 1
            elif tok.type == tokenize.OP and tok.string in ')]}':
                depth -= 1
                if depth < 0:
                    return -1
            continue
        if tok.type == tokenize.OP and tok.string == '(':
            return index
        if (tok.type == tokenize.OP and tok.string == '['
                and not type_params_seen):
            type_params_seen = True
            depth = 1
            continue
        return -1
    return -1
def check_PY11(code: Any) -> list[dict]:
    if not isinstance(code, str) or not code.strip():
        return []
    tokens = []
    try:
        tokens.extend(tokenize.generate_tokens(_source_readline(code)))
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc,
                      context=f'check_PY11:{type(_swallowed_exc).__name__}')
    issues = []
    index = 0
    while index < len(tokens):
        tok = tokens[index]
        if not (tok.type == tokenize.NAME and tok.string == 'def'):
            index += 1
            continue
        cursor = _py11_def_name_index(tokens, index + 1)
        if cursor < 0:
            index += 1
            continue
        cursor = _py11_signature_open_index(tokens, cursor + 1)
        if cursor < 0:
            index += 1
            continue
        params, end = _py11_parse_param_list(tokens, cursor)
        issues.extend(_py11_duplicate_findings(params))
        index = max(end, index + 1)
    return issues
_GF12_OVERFLOW_FINDING = {
    "rule_id": "GF-12",
    "severity": "P0",
    "line": 1,
    "message": ("Broken artifact: pathologically nested source "
                 "exhausts recursion depth, module unimportable"),
    "suggestion": "Fix or regenerate the pathologically nested source",
    "category": "artifact_integrity",
}
def _text_wear_checks(code: Any, parse_overflow: bool, skip,
                      policy: TextDamagePolicy) -> list:
    issues = []
    if not skip("GF-01") and not parse_overflow:
        issues.extend(_check_fullwidth(code))
    if not skip("GF-03"):
        issues.extend(_check_duplicate_lines(code))
    if not skip("GF-04"):
        issues.extend(_check_redundant_lazy(code, policy))
    return issues
def _text_syntax_split_checks(code: Any, syntax_ok: bool, skip) -> list:
    issues = []
    if not syntax_ok and not skip("GF-06"):
        issues.extend(_check_orphaned_except(code))
    if not skip("GF-07"):
        issues.extend(_check_regex_substitution_damage(code))
    if not syntax_ok and not skip("GF-10"):
        issues.extend(_check_hanging_indent(code))
    return issues
def _text_artifact_check(code: Any, parse_overflow: bool, skip,
                         policy: TextDamagePolicy) -> list:
    issues: list = []
    duplicate_issues: list = []
    if not parse_overflow and not skip("PY-11"):
        duplicate_issues = check_PY11(code)
        issues.extend(duplicate_issues)
    if skip("GF-12"):
        return issues
    if parse_overflow:
        issues.append(dict(_GF12_OVERFLOW_FINDING))
        return issues
    issues.extend(_check_artifact_integrity(
        code, policy,
        duplicate_argument_lines={issue['line'] for issue in duplicate_issues}))
    return issues
def _no_rule_excluded(_rule_id: str) -> bool:
    return False
def _rule_skipper(is_excluded: Any) -> Callable[[str], bool]:
    if callable(is_excluded):
        return is_excluded
    if is_excluded is None or isinstance(is_excluded, (bytes, bytearray)):
        return _no_rule_excluded
    if isinstance(is_excluded, str):
        excluded = frozenset((is_excluded,))
    else:
        try:
            excluded = frozenset(
                rule for rule in is_excluded if isinstance(rule, str))
        except TypeError:
            return _no_rule_excluded
    return excluded.__contains__
def _attach_filepath(issues: list, filepath: str) -> list:
    if not filepath:
        return issues
    for issue in issues:
        if isinstance(issue, dict) and not issue.get("file"):
            issue["file"] = filepath
    return issues
def run_text_checks(code: Any, *, syntax_ok: bool = True,
                    parse_overflow: bool = False, is_excluded=None,
                    filepath: str = "",
                    policy: TextDamagePolicy | None = None) -> list:
    if not isinstance(code, str):
        return []
    resolved_policy = (policy if isinstance(policy, TextDamagePolicy)
                       else _DEFAULT_TEXT_DAMAGE_POLICY)
    skip = _rule_skipper(is_excluded)
    issues: list = []
    issues.extend(_text_wear_checks(
        code, parse_overflow, skip, resolved_policy))
    issues.extend(_text_syntax_split_checks(code, syntax_ok, skip))
    issues.extend(_text_artifact_check(
        code, parse_overflow, skip, resolved_policy))
    return _attach_filepath(issues, filepath)
def wiring_declarations() -> dict:
    bindings = {'PY09': check_PY09, 'PY10': check_PY10, 'PY11': check_PY11}
    for checker in bindings.values():
        checker._jwsgj_requires_tree = False
    return {"catalogs": {"rule_bindings": bindings}}

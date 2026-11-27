from __future__ import annotations  # noqa: I001
import ast
import bisect
import codecs
import hashlib
import io
import logging
import os
import re
import threading
import tokenize
import weakref
from collections.abc import Iterable, Iterator
from contextlib import contextmanager
from functools import cache, lru_cache
from typing import Any, Protocol
from jwsgj.diag_shared_ast_nodes import (
    FRAME_BOUNDARY_NODES,
    TRY_NODE_TYPES,
    argument_param_names,
    parse_ast_safely,
)
from jwsgj.diag_types_vocab import (
    DEFAULT_VIRTUAL_FILENAME,
    MSG_SYNTAX_ERROR_SKIP,
    MSG_SYNTAX_ERROR_SKIP_DETECTION,
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed, write_module_run
logger = logging.getLogger(__name__)
CONTEXT_ACCESS_ERRORS = (KeyError, AttributeError, OSError, ValueError,
                         TypeError, RecursionError)
_DEFAULT_CONTEXT_LINES = 2
_LINE_OFFSET_CACHE_MAX = 32
def _universal_newlines(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\r", "\n")
def _parse_module_source(text: str) -> ast.AST | None:
    try:
        return ast.parse(text)
    except PARSE_DEGRADE_EXC as _e:
        logger.debug("os 导入判定解析失败(降级文本匹配): %s", _e)
        return None
_CODING_DECL_RE = re.compile(r'^[ \t\f]*#.*?coding[:=][ \t]*([-\w.]+)')
def _quote_state_step(line_text: str, i: int, in_str: str) -> tuple[int, str, bool]:
    c = line_text[i]
    if in_str:
        if c == "\\":
            return i + 2, in_str, False
        if line_text.startswith(in_str, i):
            return i + len(in_str), "", False
        return i + 1, in_str, False
    if c in ("'", '"'):
        _quote = c * (3 if line_text.startswith(c * 3, i) else 1)
        return i + len(_quote), _quote, False
    if c == "#":
        return i, in_str, True
    return i + 1, in_str, False
def scan_line_quote_state(line_text: str, in_str: str = "") -> tuple[int, str]:
    i, n = 0, len(line_text)
    while i < n:
        i, in_str, _hit = _quote_state_step(line_text, i, in_str)
        if _hit:
            return i, in_str
    return -1, in_str
def leading_quote_states(code_lines: list) -> list[str]:
    states: list[str] = []
    cur = ""
    for text in code_lines:
        states.append(cur)
        _, cur = scan_line_quote_state(text, cur)
    return states
def byte_col_to_char_col(line_text: str, byte_col: int) -> int:
    if byte_col <= 0 or not line_text:
        return 0
    return len(line_text.encode('utf-8')[:byte_col].decode('utf-8', errors='ignore'))
def utf8_span_to_char_span(line_text: str, byte_start: int,
                            byte_end: int) -> tuple[int, int]:
    return (byte_col_to_char_col(line_text, byte_start),
            byte_col_to_char_col(line_text, byte_end))
def node_line_span(node: Any) -> int:
    start = getattr(node, "lineno", None)
    end = getattr(node, "end_lineno", None)
    if not start or not end:
        return 0
    return end - start + 1
def _join_physical_lines(lines: Iterable[str]) -> str:
    rows = list(lines)
    last_index = len(rows) - 1
    return "".join(
        line if index == last_index or line.endswith(("\n", "\r"))
        else line + "\n"
        for index, line in enumerate(rows)
    )
def join_source_lines(source_lines: Any) -> str:
    if isinstance(source_lines, str):
        return source_lines
    if isinstance(source_lines, (bytes, bytearray)):
        return _decode_source_bytes(bytes(source_lines))
    if isinstance(source_lines, (list, tuple)):
        return _join_physical_lines(str(line) for line in source_lines)
    return ""
@lru_cache(maxsize=_LINE_OFFSET_CACHE_MAX)
def _line_offsets(code: str) -> tuple[int, ...]:
    offsets = [0]
    i = 0
    n = len(code)
    while i < n:
        ch = code[i]
        if ch == '\n':
            i += 1
            offsets.append(i)
        elif ch == '\r':
            i += 2 if (i + 1 < n and code[i + 1] == '\n') else 1
            offsets.append(i)
        else:
            i += 1
    if offsets[-1] != len(code):
        offsets.append(len(code))
    return tuple(offsets)
def line_num_fast(code: str, offset: int) -> int:
    offsets = _line_offsets(code)
    index = bisect.bisect_right(offsets, offset)
    if not code:
        return 1
    line_count = max(len(offsets) - 1, 1)
    return min(max(index, 1), line_count)
def _normalized_source_lines(source, invalid_log=""):
    if not source:
        return None
    if isinstance(source, (bytes, bytearray)):
        source = decode_source_bytes(bytes(source))
    if isinstance(source, str):
        lines = _universal_newlines(source).split("\n")
        if lines and lines[-1] == "":
            lines.pop()
        return lines
    if isinstance(source, (list, tuple)):
        return source
    if invalid_log:
        logger.debug("源类型非法(%s): %r", invalid_log, type(source).__name__)
    return None
def _coerce_lineno(lineno: Any, invalid_log: str = "") -> int | None:
    if isinstance(lineno, bool):
        if invalid_log:
            logger.debug("行号非法(%s): %r", invalid_log, lineno)
        return None
    try:
        return int(lineno)
    except (TypeError, ValueError, OverflowError):
        if invalid_log:
            logger.debug("行号非法(%s): %r", invalid_log, lineno)
        return None
def _line_window(
        source: Any, lineno: Any, context: int = _DEFAULT_CONTEXT_LINES):
    lines = _normalized_source_lines(source, invalid_log="返回空上下文")
    if not lines:
        return None
    line_no = _coerce_lineno(lineno, invalid_log="返回空上下文")
    if line_no is None:
        return None
    if line_no < 1 or line_no > len(lines):
        logger.debug("行号越界(返回空上下文): %r", lineno)
        return None
    start = max(0, line_no - context - 1)
    end = min(len(lines), line_no + context)
    if end <= start:
        return None
    return start, end, lines, line_no
def extract_code_lines(source, lineno, context=_DEFAULT_CONTEXT_LINES):
    window = _line_window(source, lineno, context)
    if window is None:
        return ""
    start, end, lines, line_no = window
    return "\n".join(
        f"{'>>>' if idx == line_no - 1 else '   '} {idx + 1}: {str(lines[idx]).rstrip()}"
        for idx in range(start, end)
    )
def line_start_offset(code: str, lineno: int) -> int:
    line_no = _coerce_lineno(lineno)
    if not _is_valid_lineno(line_no) or line_no <= 1:
        return 0
    offsets = _line_offsets(code)
    index = line_no - 1
    return offsets[index] if index < len(offsets) else len(code)
def _is_valid_lineno(lineno: object) -> bool:
    return (not isinstance(lineno, bool) and isinstance(lineno, int)
            and lineno >= 1)
_INLINE_LINE_CACHE_MAX = 512
_MTIME_UNREADABLE = object()
class _LinesWindow:
    __slots__ = ("bridge", "frozen", "lines", "token")
    def __init__(self) -> None:
        self.frozen = False
        self.bridge: Any | None = None
        self.token: Any | None = None
        self.lines: dict[str, tuple[Any, list[str]]] = {}
_LINES_WINDOW_LOCAL = threading.local()
_INLINE_LINE_CACHE: dict[str, tuple[Any, list[str]]] = {}
def _inline_line_cache_guard() -> None:
    if len(_INLINE_LINE_CACHE) > _INLINE_LINE_CACHE_MAX:
        _INLINE_LINE_CACHE.clear()
def _lines_window() -> _LinesWindow:
    window = getattr(_LINES_WINDOW_LOCAL, "window", None)
    if window is None:
        window = _LinesWindow()
        _LINES_WINDOW_LOCAL.window = window
    return window
def _snapshot_window_stack() -> list:
    stack = getattr(_LINES_WINDOW_LOCAL, "stack", None)
    if stack is None:
        stack = []
        _LINES_WINDOW_LOCAL.stack = stack
    return stack
def _reset_lines_window() -> None:
    window = _lines_window()
    window.frozen = False
    window.bridge = None
    window.token = None
    window.lines = {}
def begin_snapshot_lines_window(source_bridge: Any | None) -> None:
    window = _lines_window()
    _snapshot_window_stack().append(
        (window.frozen, window.bridge, window.token, window.lines))
    window.frozen = True
    window.token = object()
    window.lines = {}
    if source_bridge is not None:
        window.bridge = source_bridge
def end_snapshot_lines_window() -> None:
    window = _lines_window()
    stack = _snapshot_window_stack()
    if stack:
        (window.frozen,
         window.bridge,
         window.token,
         window.lines) = stack.pop()
    else:
        _reset_lines_window()
def src_lines(filepath: str) -> list[str]:
    if not filepath:
        return []
    memory_source = _lookup_memory_source(filepath)
    fingerprint = (('memory', source_digest(memory_source))
                   if memory_source is not None
                   else _line_cache_mtime(filepath))
    if fingerprint is _MTIME_UNREADABLE:
        return []
    window = _lines_window()
    line_cache = window.lines if window.frozen else _INLINE_LINE_CACHE
    hit = line_cache.get(filepath)
    if hit is not None and hit[0] == fingerprint:
        return hit[1]
    return _rebuild_lines(filepath, fingerprint)
def _line_cache_mtime(filepath: str):
    window = _lines_window()
    if window.frozen:
        return window.token
    try:
        stat = os.stat(filepath)
        return stat.st_mtime_ns, stat.st_size
    except OSError as _e:
        log_swallowed(__name__, _e, context='src_lines:OSError')
        return _MTIME_UNREADABLE
def _rebuild_lines(filepath: str, fingerprint: Any) -> list[str]:
    window = _lines_window()
    memory_source = _lookup_memory_source(filepath)
    if memory_source is not None:
        lines = _universal_newlines(memory_source).split("\n")
    else:
        src = _coerce_bridge_source(
            window.bridge, filepath, context='src_lines:bridge')
        if src is not None:
            lines = _universal_newlines(src).split("\n")
        else:
            lines = _read_local_lines(filepath)
            if lines is None:
                return []
    if window.frozen:
        window.lines[filepath] = (fingerprint, lines)
    else:
        _inline_line_cache_guard()
        _INLINE_LINE_CACHE[filepath] = (fingerprint, lines)
    return lines
def _coerce_bridge_source(cache: Any, filepath: str, *,
                          context: str) -> str | None:
    if cache is None:
        return None
    try:
        source = cache.get_source(filepath)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context=f'{context}:{filepath}')
        return None
    if source is not None and not isinstance(source, str):
        logger.debug("共享缓存桥源码非 str 形态 %s，按未命中处理: %s",
                     type(source).__name__, filepath)
        return None
    return source
def _read_local_lines(filepath: str) -> list[str] | None:
    try:
        source = read_source(filepath)
    except Exception as e:  # noqa: BLE001
        logger.debug("源码行集读取失败，降级空行集（豁免判定将保守上报）: %s: %s",
                     filepath, e)
        return None
    return (None if source is None
            else _universal_newlines(source).split("\n"))
def iter_unquoted(line: str):
    quote = ""
    i, n = 0, len(line)
    while i < n:
        ch = line[i]
        if quote:
            if ch == "\\":
                i += 2
                continue
            if line.startswith(quote, i):
                i += len(quote)
                quote = ""
                continue
        elif ch in "\"'":
            quote = ch * (3 if line.startswith(ch * 3, i) else 1)
            i += len(quote)
            continue
        else:
            yield i, ch
        i += 1
def _comment_start(line: str) -> int:
    for _i, ch in iter_unquoted(line):
        if ch == "#":
            return _i
    return -1
def code_part(line: str) -> str:
    start = _comment_start(line)
    return line if start < 0 else line[:start]
@cache
def marker_pattern(marker: str) -> re.Pattern[str]:
    expr = re.escape(marker)
    if marker[:1].isalnum() or marker[:1] == "_":
        expr = r"(?<![\w])" + expr
    return re.compile(expr)
def marker_hit(source: str, marker: str) -> bool:
    if not marker:
        return False
    return marker_pattern(marker).search(source) is not None
_CONSTANT_NAME_RE = re.compile(r"^[A-Z][A-Z0-9_]*$")
def is_constant_name(name: str) -> bool:
    return bool(_CONSTANT_NAME_RE.match(name))
_REGEX_META_TOKENS = ('\\s', '\\S', '\\b', '\\w', '\\W', '\\d', '\\D',
                     '.*', '.+', '(?', '[^', '\\(', '^[')
def is_regex_pattern_text(value_str: str) -> bool:
    """值文本是否呈正则元语法形态（SE-03 与 AST 凭据通道共用的非凭据排除）。

    正则常量（``_PASSWORD_TAIL = r"\\s*\\(.*?(?i:password)"``）目标名带
    凭据词，但值是模式串而非凭据本身；两条硬编码凭据检测通道必须用
    同一判定排除，否则 AST 通道会对 SE-03 已豁免的行重复报 high。
    """
    if not isinstance(value_str, str):
        return False
    return any(tok in value_str for tok in _REGEX_META_TOKENS)
def is_rule_name_constant(value: str, hit_names: Iterable[str]) -> bool:
    if not isinstance(value, str):
        return False
    if isinstance(hit_names, str):
        hit_names = (hit_names,)
    normalized = value.lower().replace('_', '')
    if not normalized:
        return False
    for name in hit_names:
        if not isinstance(name, str):
            continue
        leaf = name.rsplit(".", 1)[-1]
        normalized_name = leaf.lower().replace('_', '')
        if not normalized_name or normalized not in normalized_name:
            continue
        if normalized == normalized_name:
            if "_" in leaf:
                return True
            continue
        name_parts = {part for part in leaf.lower().split("_") if part}
        if name_parts & {"rule", "rules", "name", "names"}:
            return True
    return False
def net_paren_depth(line: str) -> int:
    depth = 0
    for _i, ch in iter_unquoted(line):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
    return depth
def join_balanced_stmt(lines: list[str], lineno: int, max_extra: int = 5) -> str:
    line_no = _coerce_lineno(lineno)
    if not _is_valid_lineno(line_no) or line_no > len(lines):
        logger.debug("行号越界(返回空语句): %r, total=%s", lineno, len(lines))
        return ""
    stmt = code_part(lines[line_no - 1])
    depth = net_paren_depth(stmt)
    i = line_no
    while depth > 0 and i < len(lines) and i < line_no + max_extra:
        nxt = code_part(lines[i])
        stmt += " " + nxt.strip()
        depth += net_paren_depth(nxt)
        i += 1
    return stmt
_ASSIGN_TARGET_TOKEN_RE = re.compile(r"[\w\[\].]+")
_ASSIGN_EQ_PREV_EXCLUDE = frozenset("=!<>+-*/%&|^@:")
_OPEN_BRACKETS = frozenset("([{")
_CLOSE_BRACKETS = frozenset(")]}")
def _is_assignment_eq(stmt: str, pos: int) -> bool:
    prev = stmt[:pos].rstrip()[-1:]
    return prev not in _ASSIGN_EQ_PREV_EXCLUDE and stmt[pos + 1:pos + 2] != "="
def _independent_assign_eq(stmt: str) -> int:
    i, n = 0, len(stmt)
    while i < n:
        if stmt[i] != "=":
            i += 1
            continue
        nxt = stmt[i + 1:i + 2]
        if _is_assignment_eq(stmt, i):
            return i
        i += 2 if nxt == "=" else 1
    return -1
def _split_assignment_targets(lhs: str) -> list[str]:
    tokens: list[str] = []
    depth = 0
    start = 0
    for index, char in iter_unquoted(lhs):
        if char in _OPEN_BRACKETS:
            depth += 1
        elif char in _CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif char == "," and depth == 0:
            tokens.append(lhs[start:index])
            start = index + 1
    tokens.append(lhs[start:])
    return tokens
def _strip_target_annotation(token: str) -> str:
    depth = 0
    for index, char in iter_unquoted(token):
        if char in _OPEN_BRACKETS:
            depth += 1
        elif char in _CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif char == ":" and depth == 0:
            return token[:index].strip()
    return token.strip()
def assign_target_of(stmt: str) -> str | None:
    pos = _independent_assign_eq(stmt)
    if pos < 0:
        return None
    tokens = [_strip_target_annotation(token)
              for token in _split_assignment_targets(stmt[:pos])]
    if any(not _ASSIGN_TARGET_TOKEN_RE.fullmatch(tok) for tok in tokens):
        return None
    return tokens[-1]
_READ_ERRORS = "replace"
def _fallback_source_encoding(data: bytes) -> str:
    return "utf-8-sig" if data.startswith(codecs.BOM_UTF8) else "utf-8"
def _decode_source_bytes(data: bytes) -> str:
    try:
        enc = tokenize.detect_encoding(io.BytesIO(data).readline)[0]
        return data.decode(enc, errors=_READ_ERRORS)
    except (LookupError, SyntaxError) as e:
        logger.debug("[Cache] 编码声明解析失败，按 BOM 兜底读入: %s", e)
        return data.decode(_fallback_source_encoding(data),
                           errors=_READ_ERRORS)
def decode_source_bytes(data: bytes) -> str:
    return _universal_newlines(_decode_source_bytes(data))
def redundant_coding_decl_line(source: str) -> int | None:
    lines = source.splitlines()[:2]
    for idx, line in enumerate(lines):
        if idx == 1 and lines[0].strip() and not lines[0].lstrip().startswith("#"):
            return None
        match = _CODING_DECL_RE.match(line)
        if match is None:
            continue
        try:
            normalized = codecs.lookup(match.group(1)).name
        except LookupError as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc,
                context='redundant_coding_decl_line:LookupError')
            return None
        return idx + 1 if normalized == 'utf-8' else None
    return None
def read_source_interpreter_encoding(filepath: str) -> str:
    with open(filepath, 'rb') as f:
        raw = f.read()
    try:
        encoding, _ = tokenize.detect_encoding(io.BytesIO(raw).readline)
        with io.TextIOWrapper(io.BytesIO(raw), encoding=encoding,
                              newline=None) as f:
            return f.read()
    except (SyntaxError, LookupError, UnicodeDecodeError) as _enc_err:
        logger.warning(
            "diag_shared_source_core.py:read_source_interpreter_encoding: "
            "编码声明非法，按 BOM/UTF-8 兜底解码: %s (%s)", filepath, _enc_err)
        return decode_source_bytes(raw)
def read_source_text(file_path: str) -> str | None:
    try:
        with tokenize.open(file_path) as f:
            return f.read().removeprefix("\ufeff")
    except (OSError, *PARSE_DEGRADE_EXC) as e:
        logger.warning(
            "diag_shared_source_core.py:read_source_text: 源文件读取失败: %s (%s)",
            file_path,
            e,
        )
        return None
def _decode_source_strict(data: bytes) -> str | None:
    try:
        enc = tokenize.detect_encoding(io.BytesIO(data).readline)[0]
        with io.TextIOWrapper(io.BytesIO(data), encoding=enc,
                              newline=None) as f:
            return f.read()
    except (LookupError, SyntaxError, ValueError) as e:
        logger.debug("[Cache] 严格解码失败: %s", e)
        return None
def read_source_with_fingerprint(fp: str, *,
                                 strict: bool = False) -> tuple[str | None,
                                                               tuple[int, int] | None]:
    try:
        with open(fp, "rb") as f:
            st = os.fstat(f.fileno())
            data = f.read()
    except OSError as e:
        logger.debug("[Cache] 读取失败 %s: %s", fp, e)
        return None, None
    _fp = (st.st_mtime_ns, st.st_size)
    if strict:
        text = _decode_source_strict(data)
        return (text, _fp) if text is not None else (None, None)
    return decode_source_bytes(data), _fp
def read_source(filepath: str, ctx: Any = None) -> str | None:
    memory_source = _lookup_memory_source(filepath)
    if memory_source is not None:
        return memory_source
    if ctx is not None:
        ctx_source = _coerce_bridge_source(
            ctx, filepath, context='read_source_cached')
        if ctx_source is not None:
            return ctx_source
    bridged = _coerce_bridge_source(
        bound_shared_cache(), filepath, context='read_source:bridge')
    if bridged is not None:
        return bridged
    source, _fingerprint = read_source_with_fingerprint(filepath)
    return source
def read_source_via_channel(filepath: str, ctx: Any, channel: str) -> str | None:
    source = read_source(filepath, ctx)
    if source is None:
        logger.debug("%s: 跳过无法读取的文件 %s", channel, filepath)
    return source
def read_source_strict(filepath: str) -> str:
    source, _fingerprint = read_source_with_fingerprint(filepath, strict=True)
    if source is None:
        with open(filepath, "rb"):
            pass
        raise OSError(f"源码不可读: {filepath}")
    return source
def read_source_auto(py_path) -> str:
    with open(py_path, "rb") as f:
        return decode_source_bytes(f.read())
def read_py_source(filepath: str) -> str | None:
    memory_source = _lookup_memory_source(filepath)
    if memory_source is not None:
        return memory_source
    source, _fingerprint = read_source_with_fingerprint(filepath, strict=True)
    if source is None:
        logger.warning("[Cache] 读取文件失败,返回已收集: %s", filepath)
    return source
_FILE_CACHE_MAX_ENTRIES = 6000
_CONTENT_CACHE: dict[str, tuple[tuple[int, int], str | None]] = {}
_CONTENT_CACHE_MAX = _FILE_CACHE_MAX_ENTRIES
_CONTENT_CACHE_LOCK = threading.Lock()
def read_cached(fp: str) -> str | None:
    try:
        stat = os.stat(fp)
    except OSError as _e:
        log_swallowed(__name__, _e, context='read_cached:OSError')
        return None
    fingerprint = (stat.st_mtime_ns, stat.st_size)
    with _CONTENT_CACHE_LOCK:
        hit = _CONTENT_CACHE.get(fp)
        if hit is not None and hit[0] == fingerprint:
            return hit[1]
    try:
        with open(fp, "rb") as f:
            data = f.read()
    except OSError as _e:
        log_swallowed(__name__, _e, context='read_cached:OSError')
        return None
    content = _decode_source_strict(data)
    with _CONTENT_CACHE_LOCK:
        if len(_CONTENT_CACHE) >= _CONTENT_CACHE_MAX:
            _CONTENT_CACHE.clear()
        _CONTENT_CACHE[fp] = (fingerprint, content)
    return content
def iter_frame_nodes(roots: Any) -> Iterator[ast.AST]:
    stack: list[ast.AST] = list(roots)
    while stack:
        node = stack.pop()
        if isinstance(node, FRAME_BOUNDARY_NODES):
            continue
        yield node
        stack.extend(ast.iter_child_nodes(node))
def build_ast_issue(rule: dict, source: Any, filepath: Any, node: Any,
                    title: str, description: str,
                    suggestion: str) -> dict:
    lineno = getattr(node, "lineno", 0) or 0
    return {
        **rule, "file": filepath, "line": lineno,
        "title": title, "message": title,
        "description": description,
        "code_snippet": extract_code_lines(source, lineno) if lineno else "",
        "suggestion": suggestion,
    }
_PARSE_CACHE_MAX = 1024
_PARSE_CACHE: dict = {}
_PARSE_CACHE_LOCK = threading.Lock()
def clear_shared_parse_cache() -> int:
    with _PARSE_CACHE_LOCK:
        n = len(_PARSE_CACHE)
        _PARSE_CACHE.clear()
        return n
def clear_source_parse_cache() -> int:
    with _SOURCE_PARSE_LOCK:
        n = len(_SOURCE_PARSE_CACHE)
        _SOURCE_PARSE_CACHE.clear()
        return n
_SOURCE_PARSE_CACHE: dict[str, ast.Module] = {}
_SOURCE_PARSE_CACHE_MAX = 1024
_SOURCE_PARSE_LOCK = threading.Lock()
_NATIVE_AST_PARSE = ast.parse
def parse_cached(
        source: str, filename: str = DEFAULT_VIRTUAL_FILENAME) -> ast.Module:
    if not isinstance(source, str):
        return ast.parse(source, filename=filename)
    _cur_parse = ast.parse
    if _cur_parse is not _NATIVE_AST_PARSE:
        return _cur_parse(source, filename=filename)
    key = source_digest(source)
    cached = _source_parse_lookup(key)
    if cached is not None:
        return cached
    tree = _borrow_parsed_tree(source, filename)
    if tree is None:
        tree = ast.parse(source, filename=filename)
        write_module_run("diag_shared_source_core", "parse_cached", "ok")
    _source_parse_store(key, tree)
    return tree
def guard_tree(code: Any, tree: Any = None, *, strict: bool = False) -> Any:
    if tree is not None:
        return tree
    try:
        return parse_cached(code)
    except (SyntaxError, ValueError, TypeError, RecursionError, MemoryError) as exc:
        log_swallowed(__name__, exc, context='guard_tree:parse_failure')
        if strict:
            logger.warning(MSG_SYNTAX_ERROR_SKIP)
        else:
            logger.debug("suppressed parse failure: %s", exc)
            logger.debug(MSG_SYNTAX_ERROR_SKIP_DETECTION)
        return None
def _source_parse_lookup(key: str) -> ast.Module | None:
    with _SOURCE_PARSE_LOCK:
        cached = _SOURCE_PARSE_CACHE.get(key)
        if cached is None:
            return None
        del _SOURCE_PARSE_CACHE[key]
        _SOURCE_PARSE_CACHE[key] = cached
        return cached
def _source_parse_store(key: str, tree: ast.Module) -> None:
    with _SOURCE_PARSE_LOCK:
        _SOURCE_PARSE_CACHE[key] = tree
        if len(_SOURCE_PARSE_CACHE) > _SOURCE_PARSE_CACHE_MAX:
            del _SOURCE_PARSE_CACHE[next(iter(_SOURCE_PARSE_CACHE))]
def _borrow_parsed_tree(source: str, filename: str) -> ast.Module | None:
    bsrc, btree = _borrow_shared_cache_tree(filename)
    if bsrc is not None and btree is not None and _same_source_text(bsrc, source):
        return btree
    return _borrow_shared_cache_tree_by_digest(source)
def _borrow_shared_cache_tree_by_digest(source: str) -> ast.Module | None:
    _bc = bound_shared_cache()
    if _bc is None:
        return None
    _probe = getattr(_bc, "get_ast_by_digest", None)
    if not callable(_probe):
        return None
    try:
        tree = _probe(source_digest(source))
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='parse_cached:digest_bridge')
        return None
    if tree is not None and not isinstance(tree, ast.Module):
        logger.debug("共享缓存摘要 AST 非 Module 形态 %s，按未命中处理",
                     type(tree).__name__)
        return None
    return tree
_MEM_SOURCES: dict[str, str] = {}
_MEM_SOURCES_LOCK = threading.Lock()
def _lookup_memory_source(path: str) -> str | None:
    with _MEM_SOURCES_LOCK:
        return _MEM_SOURCES.get(path)
def register_memory_source(path: str, source: str) -> None:
    with _MEM_SOURCES_LOCK:
        _MEM_SOURCES[path] = source
def unregister_memory_source(path: str) -> None:
    with _MEM_SOURCES_LOCK:
        _MEM_SOURCES.pop(path, None)
def is_memory_source(path: str) -> bool:
    return _lookup_memory_source(path) is not None
class SharedCacheBridge(Protocol):
    def get_source(self, filepath: str) -> str | None:
        ...
    def get_ast(self, filepath: str) -> ast.Module | None:
        ...
_SHARED_CACHE_REF = None
_SHARED_CACHE_SCOPE_LOCAL = threading.local()
def _new_shared_cache_ref(cache: SharedCacheBridge):
    try:
        return weakref.ref(cache)
    except TypeError as _e:
        logger.debug("bind_shared_cache: 对象不可弱引用，降级强引用: %s (%s)",
                     type(cache).__name__, _e)
        return lambda _c=cache: _c
def bound_shared_cache():
    stack = getattr(_SHARED_CACHE_SCOPE_LOCAL, "stack", None)
    ref = stack[-1] if stack else _SHARED_CACHE_REF
    return ref() if ref is not None else None
def bind_shared_cache(cache: SharedCacheBridge | None) -> None:
    global _SHARED_CACHE_REF
    _SHARED_CACHE_REF = (
        _new_shared_cache_ref(cache) if cache is not None else None)
@contextmanager
def shared_cache_bridge_scope(cache: SharedCacheBridge | None) -> Iterator[None]:
    if cache is None:
        yield
        return
    stack = getattr(_SHARED_CACHE_SCOPE_LOCAL, "stack", None)
    if stack is None:
        stack = []
        _SHARED_CACHE_SCOPE_LOCAL.stack = stack
    stack.append(_new_shared_cache_ref(cache))
    try:
        yield
    finally:
        stack.pop()
class _SharedSnapshotSource:
    __slots__ = ("_reader",)
    def __init__(self) -> None:
        self._reader = None
    def set_reader(self, reader):
        prev = self._reader
        self._reader = reader
        return prev
    def read(self, fpath: str) -> str | None:
        reader = self._reader
        if reader is None:
            return None
        try:
            content = reader(fpath)
        except Exception as e:  # noqa: BLE001
            logger.debug("共享快照读源读取失败，回退盘读: %s: %s", fpath, e)
            return None
        return content if isinstance(content, str) else None
_SNAPSHOT_SOURCE = _SharedSnapshotSource()
set_shared_snapshot_reader = _SNAPSHOT_SOURCE.set_reader
read_shared_snapshot = _SNAPSHOT_SOURCE.read
def _is_synthetic_filepath(filepath: object) -> bool:
    return isinstance(filepath, str) and filepath.startswith("<")
def _fetch_bridged_pair(cache, filepath: str) -> tuple[str | None, ast.Module | None]:
    try:
        _csaa = getattr(cache, "get_source_and_ast", None)
        if callable(_csaa):
            pair = _csaa(filepath)
            if not (isinstance(pair, tuple) and len(pair) == 2):
                logger.debug(
                    "共享缓存 get_source_and_ast 返回非二元组 %s，按未命中处理: %s",
                    type(pair).__name__, filepath)
                return None, None
            source, tree = pair
        else:
            source = cache.get_source(filepath)
            tree = cache.get_ast(filepath) if source is not None else None
        if source is not None and not isinstance(source, str):
            logger.debug("共享缓存桥源码非 str 形态 %s，按未命中处理: %s",
                         type(source).__name__, filepath)
            return None, None
        if tree is not None and not isinstance(tree, ast.Module):
            logger.debug("共享缓存桥 AST 非 Module 形态 %s，按未命中处理: %s",
                         type(tree).__name__, filepath)
            return None, None
        return source, tree
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context=f"shared_cache_bridge:{filepath}")
        return None, None
def _cache_scope_allows(cache: Any, filepath: str) -> bool:
    store = getattr(cache, "store", None)
    probe = getattr(store, "in_scope", None)
    if not callable(probe):
        return cache is not None
    try:
        return bool(probe(filepath))
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='_cache_scope_allows:in_scope')
        return False
def _borrow_shared_cache_tree(filepath: str) -> tuple[str | None, ast.Module | None]:
    _bc = bound_shared_cache()
    if (_bc is None or _is_synthetic_filepath(filepath)
            or not _cache_scope_allows(_bc, filepath)):
        return None, None
    source, tree = _fetch_bridged_pair(_bc, filepath)
    if source is not None and tree is not None:
        return source, tree
    return None, None
def shared_source_and_tree(filepath: str) -> tuple[str | None, ast.Module | None]:
    if is_memory_source(filepath):
        return parse_py_file(filepath, quiet=True)
    _bsrc, _btree = _borrow_shared_cache_tree(filepath)
    if _bsrc is not None and _btree is not None:
        return _bsrc, _btree
    try:
        source, _fingerprint = read_source_with_fingerprint(filepath, strict=True)
        if source is None:
            logger.debug("源文件读取失败(跳过): %s", filepath)
            return None, None
        tree = ast.parse(source, filename=filepath)
    except (OSError, UnicodeDecodeError, SyntaxError, ValueError,
            RecursionError, MemoryError) as _e:
        logger.debug("源文件读取/解析失败(跳过): %s (%s)", filepath, _e)
        return None, None
    write_module_run("diag_shared_source_core", "shared_source_and_tree", "ok",
                     file=os.path.basename(filepath))
    return source, tree
def read_source_tree(filepath: str, cache=None):
    memory_source = _lookup_memory_source(filepath)
    if memory_source is not None:
        return _ast_parse_or_none(
            memory_source, filepath, quiet=True,
            context='read_source_tree:memory_source')
    if cache is not None:
        try:
            tree = coerce_ctx_tree(filepath, cache.get_ast(filepath))
            if tree is not None:
                return tree
        except Exception as _e:
            logger.debug("[Cache] cache get_ast failed: %s: %s",
                         filepath, _e, exc_info=True)
    source, _fingerprint = read_source_with_fingerprint(filepath, strict=True)
    if source is None:
        return None
    try:
        return ast.parse(source)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as _e:
        logger.debug("[Cache] ast.parse failed（源码语法损坏/深嵌套）: %s", _e)
        return None
def _cache_source_matches(cache: Any, filepath: str, source: Any) -> bool:
    if not isinstance(source, str) or not callable(
            getattr(cache, "get_source", None)):
        return False
    cached_source = _coerce_bridge_source(
        cache, filepath, context='parse_cache:source_check')
    return (cached_source is not None
            and _same_source_text(cached_source, source))
def parse_or_cache(src_path: str, src, cache=None) -> Any:
    tree = None
    if cache is not None and _cache_source_matches(cache, src_path, src):
        try:
            tree = coerce_ctx_tree(src_path, cache.get_ast(src_path))
        except Exception as _e:
            logger.debug("[Cache] cache get_ast failed: %s: %s",
                         src_path, _e, exc_info=True)
    if tree is not None:
        return tree
    try:
        return ast.parse(src)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e, context='parse_or_cache:SyntaxError')
        return None
read_source_cached = read_source
def source_digest(source: str) -> str:
    return hashlib.md5(
        source.encode("utf-8", "surrogatepass"),
        usedforsecurity=False).hexdigest()
def files_fingerprint(files: Iterable[str]) -> tuple:
    mtimes: list[int] = []
    sizes: list[int] = []
    identity: list[str] = []
    fingerprints: list[tuple[str, int, int]] = []
    for path in files:
        try:
            stat = os.stat(path)
        except OSError as _swallow_e:
            log_swallowed(
                __name__, _swallow_e, context='files_fingerprint:OSError')
            continue
        mtimes.append(stat.st_mtime_ns)
        sizes.append(stat.st_size)
        identity.append(path)
        fingerprints.append((path, stat.st_mtime_ns, stat.st_size))
    return (len(mtimes), max(mtimes, default=0), sum(mtimes), sum(sizes),
            tuple(sorted(identity)), tuple(sorted(fingerprints)))
def _parse_cache_hit(filepath: str, digest: str):
    with _PARSE_CACHE_LOCK:
        hit = _PARSE_CACHE.get(filepath)
    if hit is None or hit[0] != digest:
        return None
    return hit[1], hit[2]
def parse_py_file(filepath: str, *, quiet: bool = False):
    _mem_src = _lookup_memory_source(filepath)
    if _mem_src is not None:
        return _parse_memory_source(filepath, _mem_src, quiet=quiet)
    _bsrc, _btree = _borrow_shared_cache_tree(filepath)
    if _bsrc is not None and _btree is not None:
        _store_parse_cache(filepath, source_digest(_bsrc), _bsrc, _btree)
        return _bsrc, _btree
    source, _ = read_source_with_fingerprint(filepath)
    if source is None:
        log = logger.debug if quiet else logger.warning
        log("parse failed, skip %s", filepath)
        return None, None
    _digest = source_digest(source)
    hit = _parse_cache_hit(filepath, _digest)
    if hit is not None:
        return hit
    return _parse_and_cache(filepath, source, _digest, quiet=quiet)
class ASTUtils:
    @staticmethod
    def parse_file(filepath: str) -> tuple[ast.Module, str] | None:
        if not isinstance(filepath, str):
            return None
        source, tree = parse_py_file(filepath, quiet=True)
        if source is None or tree is None:
            return None
        return tree, source
    @staticmethod
    def resolve_call_name(node: ast.Call) -> str:
        func = node.func
        if isinstance(func, ast.Name):
            return func.id
        if isinstance(func, ast.Attribute):
            parts = []
            cur = func
            while isinstance(cur, ast.Attribute):
                parts.append(cur.attr)
                cur = cur.value
            if isinstance(cur, ast.Name):
                parts.append(cur.id)
            elif isinstance(cur, ast.Call):
                parts.append('call')
            return '.'.join(reversed(parts))
        if isinstance(func, ast.Subscript):
            return 'subscript'
        if isinstance(func, ast.Call):
            return 'call'
        return ''
def _ast_parse_or_none(source: str, filepath: str, *, quiet: bool,
                       context: str) -> ast.Module | None:
    try:
        return ast.parse(source, filename=filepath)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e, context=context)
        log = logger.debug if quiet else logger.warning
        log("parse failed, skip %s: %s", filepath, _e)
        return None
def _log_parse_success(filepath: str, *, channel: str, quiet: bool) -> None:
    if quiet:
        logger.debug("module_run: diag_shared_source_core._parse_py_file"
                     " outcome=ok channel=%s file=%s", channel, filepath)
        return
    write_module_run("diag_shared_source_core", "_parse_py_file", "ok",
                     channel=channel, file=filepath)
def _same_source_text(left: str, right: str) -> bool:
    return left == right or left.rstrip("\r\n") == right.rstrip("\r\n")
def _parse_memory_source(filepath: str, mem_src: str, *, quiet: bool = False):
    _digest = source_digest(mem_src)
    hit = _parse_cache_hit(filepath, _digest)
    if hit is not None:
        return hit
    _bsrc, _btree = _borrow_shared_cache_tree(filepath)
    if (_bsrc is not None and _btree is not None
            and _same_source_text(_bsrc, mem_src)):
        _store_parse_cache(filepath, _digest, mem_src, _btree)
        return mem_src, _btree
    tree = _ast_parse_or_none(
        mem_src, filepath, quiet=quiet, context='_parse_py_file:SyntaxError')
    if tree is None:
        return None, None
    _store_parse_cache(filepath, _digest, mem_src, tree)
    _log_parse_success(filepath, channel="memory_source", quiet=quiet)
    return mem_src, tree
def _store_parse_cache(filepath: str, digest: str, source: str, tree) -> None:
    with _PARSE_CACHE_LOCK:
        if len(_PARSE_CACHE) >= _PARSE_CACHE_MAX:
            _PARSE_CACHE.clear()
        _PARSE_CACHE[filepath] = (digest, source, tree)
def _parse_and_cache(filepath: str, source: str, digest: str, *,
                     quiet: bool = False):
    tree = _ast_parse_or_none(
        source, filepath, quiet=quiet, context='_parse_py_file:SyntaxError')
    if tree is None:
        return None, None
    _store_parse_cache(filepath, digest, source, tree)
    _log_parse_success(filepath, channel="disk_source", quiet=quiet)
    return source, tree
def load_source_tree(filepath: str) -> tuple[str, ast.Module] | None:
    source, tree = parse_py_file(filepath, quiet=True)
    if source is None or tree is None:
        return None
    return source, tree
def coerce_source_text(code: Any) -> str | None:
    if isinstance(code, (bytes, bytearray)):
        return _decode_source_bytes(bytes(code)).removeprefix("\ufeff")
    if isinstance(code, str):
        return code.removeprefix("\ufeff")
    if (isinstance(code, (list, tuple))
            and all(isinstance(line, str) for line in code)):
        return _join_physical_lines(code).removeprefix("\ufeff")
    logger.warning(MSG_SYNTAX_ERROR_SKIP)
    return None
def count_lines(source: str) -> int:
    if not isinstance(source, str) or not source:
        return 0
    normalized = _universal_newlines(source)
    return normalized.count("\n") + (
        0 if normalized.endswith("\n") else 1)
_SOURCE_READ_ERRORS = (OSError, UnicodeDecodeError)
SOURCE_READ_PARSE_ERRORS = (*_SOURCE_READ_ERRORS, *PARSE_DEGRADE_EXC)
def _decode_py_source(data: bytes) -> str:
    try:
        encoding = tokenize.detect_encoding(io.BytesIO(data).readline)[0]
    except (SyntaxError, LookupError) as _enc_err:
        logger.debug("[diag_shared_source_core] 编码声明探测失败，回退 utf-8: %s", _enc_err)
        encoding = "utf-8"
    return data.decode(encoding).removeprefix("\ufeff")
def read_py_source_with_error(filepath: str) -> tuple[str | None, BaseException | None]:
    try:
        with open(filepath, "rb") as f:
            data = f.read()
        return _decode_py_source(data), None
    except _SOURCE_READ_ERRORS as e:
        log_swallowed(__name__, e, context='read_py_source_with_error:_SOURCE_READ_ERRORS')
        return None, e
def parse_py_source(source: str) -> tuple[ast.Module | None, BaseException | None]:
    try:
        return ast.parse(source), None
    except PARSE_DEGRADE_EXC as e:
        log_swallowed(__name__, e, context='parse_py_source:PARSE_DEGRADE_EXC')
        return None, e
def parse_py_source_with_details(source: str, details: list[str]) -> ast.Module | None:
    tree, err = parse_py_source(source)
    if tree is None:
        details.append(f"{type(err).__name__} — 无法解析")
    return tree
_SHARED_AST_CACHE: dict = {}
_SHARED_AST_SOURCE_DIGESTS: dict[str, str] = {}
_CACHE_MISS = object()
MAX_SHARED_AST_CACHE = 2000
_AST_CACHE_LOCK = threading.Lock()
def lru_put(cache: dict, key, value, max_size: int) -> None:
    """有界 LRU 写入：淘汰**最久未用的一项**，而不是「满即整体清空」。

    「满即清空」在工作集 > 上限时会让缓存**完全失效**：每次写入都清空，
    下一次读取必然 miss，O(1) 查找退化成「每次都重建」。
    ``diag_shared_ast_views._LEXICAL_SCOPE_MEMO``（上限 32）在 307 模块
    规模下正是这种抖动源——词法作用域表被反复重建。

    依赖 CPython dict 保持插入序：最旧项即 ``next(iter(cache))``。
    """
    if max_size <= 0:
        cache.clear()
        return
    cache.pop(key, None)
    cache[key] = value
    while len(cache) > max_size:
        cache.pop(next(iter(cache)), None)
def lru_get(cache: dict, key, default=None):
    """读取并提升优先级（真 LRU：命中即移到队尾，避免被先淘汰）。"""
    try:
        value = cache.pop(key)
    except KeyError:
        return default
    cache[key] = value
    return value
def _put_with_cap_eviction(cache: dict, limit: int, key, value, label: str) -> bool:
    evicted = len(cache) >= limit and key not in cache
    if evicted:
        logger.warning("%s达上限 %d，整体清空（内存加固兜底触发）", label, limit)
        cache.clear()
    cache[key] = value
    return evicted
def _set_shared_ast(filepath, tree, source=None):
    if tree is not None and not isinstance(tree, ast.Module):
        logger.warning("共享 AST 缓存拒绝非 Module 形态 %s: %s，按不可解析登记",
                       type(tree).__name__, filepath)
        tree = None
    evicted = _put_with_cap_eviction(_SHARED_AST_CACHE, MAX_SHARED_AST_CACHE,
                                     filepath, tree, "共享 AST 缓存")
    if evicted:
        _SHARED_AST_SOURCE_DIGESTS.clear()
    if isinstance(source, str):
        _SHARED_AST_SOURCE_DIGESTS[filepath] = source_digest(source)
    else:
        _SHARED_AST_SOURCE_DIGESTS.pop(filepath, None)
    return tree
def clear_shared_ast_cache() -> None:
    with _AST_CACHE_LOCK:
        _SHARED_AST_CACHE.clear()
        _SHARED_AST_SOURCE_DIGESTS.clear()
def _parse_ast_cached(filepath, source, ctx=None):
    ctx_cache = getattr(ctx, "_ast_cache", None) if ctx is not None else None
    if (ctx_cache is not None
            and _cache_source_matches(ctx, filepath, source)):
        cached = ctx_cache.get(filepath)
        if isinstance(cached, ast.Module):
            return cached
    digest = source_digest(source)
    with _AST_CACHE_LOCK:
        cached = _SHARED_AST_CACHE.get(filepath, _CACHE_MISS)
        cached_digest = _SHARED_AST_SOURCE_DIGESTS.get(filepath)
    if cached is not _CACHE_MISS and cached_digest == digest:
        return cached
    _bsrc, _btree = _borrow_shared_cache_tree(filepath)
    if (_btree is not None and _bsrc is not None
            and _same_source_text(_bsrc, source)):
        with _AST_CACHE_LOCK:
            return _set_shared_ast(filepath, _btree, source=source)
    tree = _ast_parse_or_none(
        source, filepath, quiet=True, context='_parse_ast_cached:parse')
    with _AST_CACHE_LOCK:
        cached = _SHARED_AST_CACHE.get(filepath, _CACHE_MISS)
        if (cached is not _CACHE_MISS
                and _SHARED_AST_SOURCE_DIGESTS.get(filepath) == digest):
            return cached
        _set_shared_ast(filepath, tree, source=source)
        return tree
def load_module(filepath: str, ctx=None) -> tuple[str, ast.Module] | None:
    source = read_source(filepath, ctx)
    if source is None:
        logger.debug('[BlindSpot] 读取源码失败,跳过低效解析: %s', filepath)
        return None
    try:
        tree = _parse_ast_cached(filepath, source, ctx=ctx)
    except SyntaxError as e:
        logger.debug('[BlindSpot] 解析异常降级: %s: %s', filepath, e)
        return None
    if tree is None:
        logger.debug('[BlindSpot] 解析失败缓存 None: %s', filepath)
        return None
    return source, tree
def iter_file_trees(fpaths: Any, ctx=None) -> Iterator[tuple[str, ast.AST]]:
    for fpath in fpaths:
        source = read_source(fpath, ctx)
        if source is None:
            continue
        tree = _tree_from_ctx_or_parse(fpath, source, ctx)
        if tree is not None:
            yield fpath, tree
def _tree_from_ctx_or_parse(fpath: str, source: str, ctx) -> ast.Module | None:
    if (ctx is not None and hasattr(ctx, "get_ast")
            and _cache_source_matches(ctx, fpath, source)):
        try:
            tree = coerce_ctx_tree(fpath, ctx.get_ast(fpath))
        except Exception:
            logger.debug("[Cache] ctx AST 通道故障，回退直解析: %s", fpath,
                         exc_info=True)
        else:
            if tree is not None:
                return tree
            logger.debug("[Cache] ctx AST 未命中，回退直解析: %s", fpath)
    return _ast_parse_or_none(
        source, fpath, quiet=True, context='_tree_from_ctx_or_parse:parse')
def sync_shared_ast_cache(ctx: Any) -> None:
    if ctx is None or not hasattr(ctx, "_ast_cache"):
        return
    with _AST_CACHE_LOCK:
        pending = [(fp, tree) for fp, tree in list(ctx._ast_cache.items())
                   if tree is not None and fp not in _SHARED_AST_CACHE]
    for fp, tree in pending:
        source = _coerce_bridge_source(
            ctx, fp, context='read_source_cached')
        with _AST_CACHE_LOCK:
            if fp not in _SHARED_AST_CACHE:
                _set_shared_ast(fp, tree, source=source)
_AST_LINE_BOUNDARY = re.compile(r'\r\n|\r|\n')
ast_split_lines = _AST_LINE_BOUNDARY.split
def physical_lines_keepends(src: str) -> list[str]:
    if not src:
        return []
    lines: list[str] = []
    start = 0
    for segment in ast_split_lines(src):
        if not segment and start >= len(src):
            break
        end = start + len(segment)
        if src.startswith("\r\n", end):
            end += 2
        elif end < len(src) and src[end] in "\r\n":
            end += 1
        lines.append(src[start:end])
        start = end
    return lines
source_line_count = count_lines
def aligned_source_lines(code: str) -> list[str]:
    segments = ast_split_lines(code)
    if segments and segments[-1] == "":
        segments = segments[:-1]
    return segments
_DOCSTRING_OPEN_DELIM_RE = re.compile(r'("""|\'\'\'|"|\')')
_DOCSTRING_CLOSE_DELIM_RE = re.compile(r'("""|\'\'\'|"|\')[ \t]*$')
def physical_docstring_lines(source: Any, first: ast.Expr) -> list[str] | None:
    text = coerce_source_text(source)
    if text is None:
        return None
    doc_node = first.value
    end_lineno = getattr(doc_node, "end_lineno", None)
    if end_lineno is not None and end_lineno > source_line_count(text):
        return None
    segment = ast.get_source_segment(text, doc_node)
    if segment is None:
        return None
    lines = aligned_source_lines(segment)
    if not lines:
        return lines
    opening = _DOCSTRING_OPEN_DELIM_RE.search(lines[0])
    if opening is not None:
        lines[0] = lines[0][opening.end():]
    closing = _DOCSTRING_CLOSE_DELIM_RE.search(lines[-1])
    if closing is not None:
        lines[-1] = lines[-1][:closing.start()]
    return lines
def source_lines_or(code: str, source_lines: list[str] | None) -> list[str]:
    return aligned_source_lines(code) if source_lines is None else source_lines
def resolve_module_name(filepath: str) -> str:
    if not filepath:
        return ''
    filename = os.path.basename(filepath.replace('\\', '/'))
    stem = filename[:-3] if filename.lower().endswith('.py') else filename
    directory = os.path.dirname(os.path.abspath(filepath))
    segments: list[str] = []
    while directory and os.path.isfile(os.path.join(directory, '__init__.py')):
        segments.append(os.path.basename(directory))
        parent = os.path.dirname(directory)
        if parent == directory:
            break
        directory = parent
    if not segments:
        return stem
    _pkg = '.'.join(reversed(segments))
    return _pkg if stem == '__init__' else _pkg + '.' + stem
def count_effective_lines(source_lines: Any) -> int:
    if isinstance(source_lines, str):
        source_lines = ast_split_lines(source_lines)
    if not isinstance(source_lines, (list, tuple)):
        return 0
    count = 0
    for line in source_lines:
        stripped = line.strip() if isinstance(line, str) else ""
        if stripped and not stripped.startswith('#'):
            count += 1
    return count
def is_consolidated_code(code: str) -> bool:
    if not isinstance(code, str):
        return False
    return any('源文件:' in ln for ln in ast_split_lines(code)[:50])
TRY_TYPES = TRY_NODE_TYPES
def safe_source_line(lines: list[str], line_no: int) -> str:
    line_no = _coerce_lineno(line_no)
    if _is_valid_lineno(line_no) and line_no <= len(lines):
        return lines[line_no - 1].strip()
    logger.warning("[AuditPatterns] 提取源码行失败,置空: line=%s, total=%s",
                 line_no, len(lines))
    return ""
def suggest(root_cause: str, fix_strategy: str, reference: str = "PEP 8 / pylint / SonarQube") -> str:
    return f"根因: {root_cause}\n修复策略: {fix_strategy}\n参考标准: {reference}"
def coerce_ctx_tree(filepath, tree) -> ast.Module | None:
    if tree is not None and not isinstance(tree, ast.Module):
        logger.warning(
            "[WarnQ] ctx.get_ast 返回非 Module 形态 %s，AST 置空: %s",
            type(tree).__name__, filepath)
        return None
    return tree
decode_source = _decode_source_strict
def stat_fingerprint(fp: str, context: str) -> tuple[int, int] | None:
    try:
        stat = os.stat(fp)
        return stat.st_mtime_ns, stat.st_size
    except OSError as _e:
        log_swallowed(__name__, _e, context=context)
        return None
_GUARD_AST_CACHE: dict[str, tuple[tuple[int, int], ast.Module | None]] = {}
_GUARD_AST_CACHE_MAX = _FILE_CACHE_MAX_ENTRIES
_GUARD_AST_CACHE_LOCK = threading.Lock()
def parse_guard_cached(fp: str) -> ast.Module | None:
    fingerprint = stat_fingerprint(fp, 'parse_guard_cached:OSError')
    if fingerprint is None:
        return None
    with _GUARD_AST_CACHE_LOCK:
        hit = _GUARD_AST_CACHE.get(fp)
        if hit is not None and hit[0] == fingerprint:
            return hit[1]
    content = read_cached(fp)
    if content is None:
        return None
    tree, exc = parse_ast_safely(content)
    if exc is not None:
        logger.warning("[Guard] 文件解析失败，跳过: %s (%s: %s)",
                       fp, type(exc).__name__, exc)
    with _GUARD_AST_CACHE_LOCK:
        if len(_GUARD_AST_CACHE) >= _GUARD_AST_CACHE_MAX:
            _GUARD_AST_CACHE.clear()
        _GUARD_AST_CACHE[fp] = (fingerprint, tree)
    return tree
def clear_guard_ast_cache() -> int:
    with _GUARD_AST_CACHE_LOCK:
        n = len(_GUARD_AST_CACHE)
        _GUARD_AST_CACHE.clear()
        return n
def parse_with_compile(
    source: str | bytes | bytearray,
    filename: str = DEFAULT_VIRTUAL_FILENAME,
) -> ast.AST:
    tree = compile(source, filename, "exec", flags=ast.PyCF_ONLY_AST)
    compile(tree, filename, "exec")
    return tree
def parse_or_none(source_code: str, _tree: ast.AST | None) -> ast.AST | None:
    if isinstance(_tree, ast.AST):
        return _tree
    if not isinstance(source_code, (str, bytes, bytearray)):
        return None
    try:
        return parse_with_compile(source_code)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
        logger.warning("[HallsDetect] 源码解析失败,本次检测跳过(返回无发现): %s", e)
        return None
_PARAM_DOC_MARKERS = (":param", "Args:", "Arguments:", "Parameters:")
_NUMPY_PARAM_SECTION_RE = re.compile(
    r"(?m)^[ \t]*Parameters[ \t]*\r?\n-{3,}[ \t]*$")
def _qualname_of(node: ast.AST, parents: list[str]) -> str | None:
    name = getattr(node, "name", "")
    if not name:
        return None
    return ".".join([*parents, name])
def _body_fingerprint(node) -> str:
    body = list(getattr(node, "body", []))
    if (body and isinstance(body[0], ast.Expr)
            and isinstance(body[0].value, ast.Constant)
            and isinstance(body[0].value.value, str)):
        body = body[1:]
    return "|".join(ast.dump(n) for n in body)
def _contract_fingerprint(node) -> tuple:
    decorators = tuple(ast.dump(n) for n in getattr(node, "decorator_list", ()))
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return (
            ast.dump(node.args),
            ast.dump(node.returns) if node.returns is not None else "",
            decorators,
        )
    if isinstance(node, ast.ClassDef):
        return (
            tuple(ast.dump(n) for n in node.bases),
            tuple(ast.dump(n) for n in node.keywords),
            decorators,
        )
    return ()
def _collect_symbols(tree: ast.AST) -> dict[str, dict]:
    symbols: dict[str, dict] = {}
    occurrences: dict[str, int] = {}
    def _walk(node: ast.AST, parents: list[str]) -> None:
        for child in ast.iter_child_nodes(node):
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                      ast.ClassDef)):
                _walk(child, parents)
                continue
            name = getattr(child, "name", "")
            qn = _qualname_of(child, parents)
            if qn:
                occurrence = occurrences.get(qn, 0) + 1
                occurrences[qn] = occurrence
                key = qn if occurrence == 1 else f"{qn}#{occurrence}"
                symbols[key] = {
                    "params": (argument_param_names(child.args)
                               if isinstance(child, (ast.FunctionDef,
                                                     ast.AsyncFunctionDef))
                               else []),
                    "docstring": ast.get_docstring(child),
                    "body_fp": _body_fingerprint(child),
                    "contract_fp": _contract_fingerprint(child),
                }
            _walk(child, [*parents, name])
    _walk(tree, [])
    return symbols
def check_comment_docstring_sync(original_source: str, fixed_source: str,
                                 filepath: str = "") -> list[dict]:
    _orig = coerce_source_text(original_source) or ""
    _fixed = coerce_source_text(fixed_source) or ""
    try:
        orig_tree = ast.parse(_orig)
        fixed_tree = ast.parse(_fixed)
    except PARSE_DEGRADE_EXC as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='check_comment_docstring_sync:PARSE_DEGRADE_EXC')
        return []
    _where = filepath or "<memory>"
    issues: list[dict] = []
    if (ast.get_docstring(orig_tree)
            and not ast.get_docstring(fixed_tree)):
        issues.append({
            "kind": "module_docstring_removed",
            "symbol": "<module>",
            "detail": f"{_where}: 模块级 docstring 在修复后被删除"
                      "（原版存在，新版缺失）",
        })
    issues.extend(_symbol_sync_issues(
        _collect_symbols(orig_tree), _collect_symbols(fixed_tree), _where))
    return issues
def _docstring_removed_issue(qn: str, orig: dict,
                             fixed: dict, where: str) -> dict | None:
    if (orig["docstring"] and not fixed["docstring"]
            and (fixed["body_fp"] != orig["body_fp"]
                 or fixed["contract_fp"] != orig["contract_fp"])):
        return {
            "kind": "docstring_removed",
            "symbol": qn,
            "detail": f"{where}: {qn} 实现已修改但原 docstring 被删除"
                      "未重写（fix_scope.comments：修复改变行为/语义/"
                      "契约时须同步更新 docstring）",
        }
    return None
def _stale_param_refs(removed: list[str], doc: str) -> list[str]:
    if (not any(m in doc for m in _PARAM_DOC_MARKERS)
            and _NUMPY_PARAM_SECTION_RE.search(doc) is None):
        return []
    return [
        p for p in removed
        if re.search(rf"(?<![A-Za-z0-9_]){re.escape(p)}(?![A-Za-z0-9_])", doc)
    ]
def _param_doc_stale_issue(qn: str, orig: dict,
                           fixed: dict, where: str) -> dict | None:
    _removed = [p for p in orig["params"] if p not in fixed["params"]]
    _doc = fixed["docstring"]
    if not _removed or not _doc:
        return None
    _stale = _stale_param_refs(_removed, _doc)
    if not _stale:
        return None
    return {
        "kind": "param_doc_stale",
        "symbol": qn,
        "detail": f"{where}: {qn} 签名已删除参数"
                  f" {', '.join(_stale[:5])}，但 docstring 参数"
                  "文档段仍引用（参数文档与新签名矛盾）",
    }
def _symbol_sync_issues(orig_syms: dict, fixed_syms: dict,
                        where: str) -> list[dict]:
    issues: list[dict] = []
    for qn, orig in orig_syms.items():
        fixed = fixed_syms.get(qn)
        if fixed is None:
            continue
        symbol = qn.split("#", 1)[0]
        for _rule in (_docstring_removed_issue, _param_doc_stale_issue):
            _issue = _rule(symbol, orig, fixed, where)
            if _issue:
                issues.append(_issue)
    return issues
def release_source_caches() -> int:
    n = len(_INLINE_LINE_CACHE)
    _INLINE_LINE_CACHE.clear()
    _snapshot_window_stack().clear()
    _reset_lines_window()
    _line_offsets.cache_clear()
    marker_pattern.cache_clear()
    with _CONTENT_CACHE_LOCK:
        _CONTENT_CACHE.clear()
    clear_shared_parse_cache()
    clear_source_parse_cache()
    clear_shared_ast_cache()
    clear_guard_ast_cache()
    return n
__all__ = [
    "ASTUtils",
    "CONTEXT_ACCESS_ERRORS",
    "FRAME_BOUNDARY_NODES",
    "MAX_SHARED_AST_CACHE",
    "SOURCE_READ_PARSE_ERRORS",
    "SharedCacheBridge",
    "TRY_TYPES",
    "aligned_source_lines",
    "assign_target_of",
    "ast_split_lines",
    "begin_snapshot_lines_window",
    "bind_shared_cache",
    "bound_shared_cache",
    "build_ast_issue",
    "byte_col_to_char_col",
    "check_comment_docstring_sync",
    "clear_guard_ast_cache",
    "clear_shared_ast_cache",
    "clear_shared_parse_cache",
    "clear_source_parse_cache",
    "code_part",
    "coerce_ctx_tree",
    "coerce_source_text",
    "count_effective_lines",
    "count_lines",
    "decode_source",
    "decode_source_bytes",
    "end_snapshot_lines_window",
    "extract_code_lines",
    "files_fingerprint",
    "guard_tree",
    "is_consolidated_code",
    "is_constant_name",
    "is_memory_source",
    "is_regex_pattern_text",
    "is_rule_name_constant",
    "iter_file_trees",
    "iter_frame_nodes",
    "iter_unquoted",
    "join_balanced_stmt",
    "join_source_lines",
    "leading_quote_states",
    "line_num_fast",
    "line_start_offset",
    "load_module",
    "load_source_tree",
    "logger",
    "lru_get",
    "lru_put",
    "marker_hit",
    "marker_pattern",
    "net_paren_depth",
    "node_line_span",
    "parse_cached",
    "parse_guard_cached",
    "parse_or_cache",
    "parse_or_none",
    "parse_py_file",
    "parse_py_source",
    "parse_py_source_with_details",
    "parse_with_compile",
    "physical_docstring_lines",
    "physical_lines_keepends",
    "read_cached",
    "read_py_source",
    "read_py_source_with_error",
    "read_shared_snapshot",
    "read_source",
    "read_source_auto",
    "read_source_cached",
    "read_source_interpreter_encoding",
    "read_source_strict",
    "read_source_text",
    "read_source_tree",
    "read_source_via_channel",
    "read_source_with_fingerprint",
    "redundant_coding_decl_line",
    "register_memory_source",
    "release_source_caches",
    "resolve_module_name",
    "safe_source_line",
    "scan_line_quote_state",
    "set_shared_snapshot_reader",
    "shared_cache_bridge_scope",
    "shared_source_and_tree",
    "source_digest",
    "source_line_count",
    "source_lines_or",
    "src_lines",
    "stat_fingerprint",
    "suggest",
    "sync_shared_ast_cache",
    "unregister_memory_source",
    "utf8_span_to_char_span",
]
def _markdown_table_cells(line: str) -> list[str]:
    if not re.match(r'^ {0,3}\S', line):
        return []
    stripped = line.strip()
    if '|' not in stripped:
        return []
    stripped = stripped.removeprefix('|')
    if stripped.endswith('|'):
        before_pipe = stripped[:-1]
        backslash_count = len(before_pipe) - len(before_pipe.rstrip('\\'))
        if backslash_count % 2 == 0:
            stripped = before_pipe
    return [cell.strip() for _start, _end, cell in _l5_markdown_cells(stripped)]

def _l5_markdown_cells(line: str) -> list[tuple[int, int, str]]:
    cells = []
    start = 0
    index = 0
    code_ticks = 0
    escaped = False
    while index < len(line):
        char = line[index]
        if char == '`' and (code_ticks or not escaped):
            run_end = index + 1
            while run_end < len(line) and line[run_end] == '`':
                run_end += 1
            run_length = run_end - index
            if not code_ticks:
                code_ticks = run_length
            elif run_length == code_ticks:
                code_ticks = 0
            index = run_end
            escaped = False
            continue
        if char == '|' and not code_ticks and not escaped:
            cells.append((start, index, line[start:index]))
            start = index + 1
        if char == '\\' and not code_ticks:
            escaped = not escaped
        else:
            escaped = False
        index += 1
    cells.append((start, len(line), line[start:]))
    return cells


logger.info(
    "diag_shared_source_core L0 源码装载域（读取/解码/行区间与偏移投影/解析缓存/共享桥/文档同步）已加载: %d 项导出",
    len(__all__))

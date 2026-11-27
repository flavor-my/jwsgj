from __future__ import annotations

import ast
import io
import logging
import os
import re
import threading
import tokenize
from collections.abc import Iterator
from functools import lru_cache
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    is_docstring_stmt,
    iter_own_scope,
    iter_unpack_target_names,
    module_level_binding_names,
    parse_ast_safely,
    walk_stmts,
)
from jwsgj.diag_shared_source_core import (
    _CODING_DECL_RE,
    _DEFAULT_CONTEXT_LINES,
    _coerce_lineno,
    _is_valid_lineno,
    _join_physical_lines,
    _line_window,
    _normalized_source_lines,
    _parse_module_source,
    _universal_newlines,
    code_part,
    decode_source_bytes,
    iter_unquoted,
    leading_quote_states,
    release_source_caches,
    scan_line_quote_state,
    src_lines,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
_TOKEN_PROJECTION_CACHE_MAX = 4096
_FULL_LINE_COL = 1 << 30
_FSTRING_TOKEN_TYPES = frozenset(
    _t for _t in (
        getattr(tokenize, _name, None)
        for _name in ('FSTRING_START', 'FSTRING_MIDDLE', 'FSTRING_END')
    ) if _t is not None
)
_STRING_TOKEN_TYPES = frozenset({tokenize.STRING}) | _FSTRING_TOKEN_TYPES
_FSTRING_MIDDLE_TYPE = getattr(tokenize, 'FSTRING_MIDDLE', -1)
_COMMENT_TOKEN_TYPES = frozenset({tokenize.COMMENT})
_LONE_CR_RE = re.compile(r"\r(?!\n)")
def _tokenize_input(source: str) -> str:
    return _LONE_CR_RE.sub("\n", source)
def _token_expand_rows(tok, spans: dict[int, list[tuple[int, int]]]) -> None:
    (srow, scol), (erow, ecol) = tok.start, tok.end
    for r in range(srow, erow + 1):
        s = scol if r == srow else 0
        e = ecol if r == erow else _FULL_LINE_COL
        spans.setdefault(r, []).append((s, e))
def _token_type_spans(code: str, token_types: set[int],
                       domain_label: str) -> dict[int, list[tuple[int, int]]] | None:
    spans: dict[int, list[tuple[int, int]]] = {}
    text = _universal_newlines(code)
    try:
        for tok in tokenize.generate_tokens(io.StringIO(text).readline):
            if tok.type not in token_types:
                continue
            _token_expand_rows(tok, spans)
    except (tokenize.TokenError, IndentationError, SyntaxError,
            ValueError) as _e:
        logger.debug("%s tokenize 失败(返回 None): %s", domain_label, _e)
        return None
    return spans
def _freeze_row_spans(
    spans: dict[int, list[tuple[int, int]]] | None,
) -> tuple[tuple[int, tuple[tuple[int, int], ...]], ...] | None:
    if spans is None:
        return None
    return tuple((row, tuple(items)) for row, items in spans.items())
def _thaw_row_spans(
    spans: tuple[tuple[int, tuple[tuple[int, int], ...]], ...] | None,
) -> dict[int, list[tuple[int, int]]] | None:
    if spans is None:
        return None
    return {row: list(items) for row, items in spans}
@lru_cache(maxsize=_TOKEN_PROJECTION_CACHE_MAX)
def _token_type_span_items(
    code: str, token_types: frozenset[int], domain_label: str,
) -> tuple[tuple[int, tuple[tuple[int, int], ...]], ...] | None:
    return _freeze_row_spans(_token_type_spans(code, token_types, domain_label))
def string_comment_spans(code: str) -> dict[int, list[tuple[int, int]]] | None:
    token_types = _STRING_TOKEN_TYPES | _COMMENT_TOKEN_TYPES
    return _thaw_row_spans(
        _token_type_span_items(code, token_types, "注释行区间"))
def comment_only_spans(code: str) -> dict[int, list[tuple[int, int]]] | None:
    return _thaw_row_spans(
        _token_type_span_items(code, _COMMENT_TOKEN_TYPES, "注释专表"))
@lru_cache(maxsize=_TOKEN_PROJECTION_CACHE_MAX)
def comment_tokens(code: str) -> tuple[tokenize.TokenInfo, ...] | None:
    if not isinstance(code, str):
        return None
    try:
        return tuple(tok for tok in
                     tokenize.generate_tokens(
                         io.StringIO(_tokenize_input(code)).readline)
                     if tok.type == tokenize.COMMENT)
    except (tokenize.TokenError, IndentationError, SyntaxError,
            ValueError) as _e:
        logger.debug("注释 token 采集失败(返回 None): %s", _e)
        return None
_NOSEC_MARKER_RE = re.compile(r"\bnosec\b", re.IGNORECASE)
def nosec_comment_lines(source: str) -> set[int] | None:
    tokens = comment_tokens(source)
    if tokens is None:
        return None
    return {tok.start[0] for tok in tokens if _NOSEC_MARKER_RE.search(tok.string)}
def has_nosec_marker(source: Any, lineno: int,
                     nosec_lines: set[int] | None) -> bool:
    line_no = _coerce_lineno(lineno)
    if not _is_valid_lineno(line_no):
        return False
    if nosec_lines is not None:
        return line_no in nosec_lines
    source_text = normalize_rule_source(source)
    source_nosec_lines = nosec_comment_lines(source_text)
    if source_nosec_lines is not None:
        return line_no in source_nosec_lines
    try:
        src_lines = source_text.splitlines()
        if 0 < line_no <= len(src_lines):
            for tok in tokenize.generate_tokens(
                    io.StringIO(src_lines[line_no - 1] + "\n").readline):
                if (tok.type == tokenize.COMMENT
                        and _NOSEC_MARKER_RE.search(tok.string)):
                    return True
        return False
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='has_nosec_marker:Exc')
        return False
def identifier_tokens(code: str) -> tuple[tuple[int, int, str], ...] | None:
    tokens = tokenize_source_cached(code) if isinstance(code, str) else None
    if tokens is None:
        return None
    return tuple((tok.start[0], tok.start[1], tok.string)
                 for tok in tokens if tok.type == tokenize.NAME)
_SAFE_TOKEN_IGNORE = frozenset({tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE})
def code_token_signature(source: str) -> tuple[tuple[int, str], ...]:
    tokens = tokenize_source_cached(source)
    if tokens is None:
        return ((tokenize.ERRORTOKEN, source),)
    return tuple((tok.type, tok.string)
                 for tok in tokens if tok.type not in _SAFE_TOKEN_IGNORE)
def _is_future_import(node: ast.AST) -> bool:
    return isinstance(node, ast.ImportFrom) and node.module == "__future__"
_OS_IMPORT_LINE_RE = re.compile(
    r"^import\s+os(?=\s*[,;#]|$)"
    r"|^import\s+os\.[\w.]+(?=\s*[,;#]|$)",
    re.MULTILINE,
)
def _os_import_text_fallback_bound(text: str) -> bool:
    normalized = _universal_newlines(text)
    spans = string_comment_spans(normalized)
    lines = normalized.split("\n")
    if spans is None:
        states = leading_quote_states(lines)
        visible = [line if not state else "" for line, state in zip(lines, states, strict=True)]
        return bool(_OS_IMPORT_LINE_RE.search("\n".join(visible)))
    for row, row_spans in spans.items():
        if not 0 < row <= len(lines):
            continue
        chars = list(lines[row - 1])
        for start, end in row_spans:
            for index in range(max(0, start), min(len(chars), end)):
                chars[index] = " "
        lines[row - 1] = "".join(chars)
    return bool(_OS_IMPORT_LINE_RE.search("\n".join(lines)))
def _os_import_alias_binds_os(alias: ast.alias) -> bool:
    if alias.asname:
        return alias.name == "os" and alias.asname == "os"
    return alias.name == "os" or alias.name.startswith("os.")
def _os_import_affects_name(alias: ast.alias) -> bool:
    return alias.asname == "os" or (
        alias.asname is None
        and (alias.name == "os" or alias.name.startswith("os.")))
def _os_delete_or_nested_import_shadow(node: ast.AST) -> bool:
    if isinstance(node, ast.Delete):
        return any(
            name == "os" for target in node.targets
            for name in iter_unpack_target_names(target))
    if isinstance(node, ast.ImportFrom):
        return any(alias.name == "*" or (alias.asname or alias.name) == "os"
                   for alias in node.names)
    return (isinstance(node, ast.Import)
            and any(_os_import_affects_name(alias)
                    and not _os_import_alias_binds_os(alias)
                    for alias in node.names))
def _module_stmt_shadows_os(stmt: ast.stmt) -> bool:
    module = ast.Module(body=[stmt], type_ignores=[])
    if "os" in module_level_binding_names(module):
        return True
    return any(_os_delete_or_nested_import_shadow(node)
               for node in iter_own_scope(stmt, include_self=True))
def _module_stmt_loads_os(stmt: ast.stmt) -> bool:
    return any(
        isinstance(node, ast.Name) and node.id == "os"
        and isinstance(node.ctx, ast.Load)
        for node in iter_own_scope(stmt, include_self=True)
    )
def _module_os_import_plan(tree: ast.AST, insert_at: int) -> list[int]:
    bound = False
    shadow_end = 0
    injection_points: list[int] = []
    for stmt in getattr(tree, "body", ()):
        if not bound and _module_stmt_loads_os(stmt):
            injection_points.append(max(
                insert_at, shadow_end, getattr(stmt, "lineno", 1) - 1))
            bound = True
        if isinstance(stmt, ast.ImportFrom):
            for alias in stmt.names:
                if (alias.name != "*"
                        and (alias.asname or alias.name) != "os"):
                    continue
                bound = False
                shadow_end = max(shadow_end, stmt.end_lineno or 0)
            continue
        if isinstance(stmt, ast.Import):
            for alias in stmt.names:
                if not _os_import_affects_name(alias):
                    continue
                bound = _os_import_alias_binds_os(alias)
                if not bound:
                    shadow_end = max(shadow_end, stmt.end_lineno or 0)
            continue
        if _module_stmt_shadows_os(stmt):
            bound = False
            shadow_end = max(shadow_end, stmt.end_lineno or 0)
    if not bound:
        injection_points.append(max(insert_at, shadow_end))
    return sorted(set(injection_points))
def _os_insert_point_head_scan(lines: list) -> int:
    insert_at = 0
    for idx, line in enumerate(lines[:5]):
        stripped = line.lstrip()
        if not stripped:
            continue
        if not _is_header_decl(stripped):
            break
        insert_at = idx + 1
    return insert_at
def _is_header_decl(stripped: str) -> bool:
    if stripped.startswith("#!"):
        return True
    return bool(_CODING_DECL_RE.match(stripped))
def _os_insert_point_ast_advance(text: str, insert_at: int,
                                 tree: ast.AST | None = None) -> int:
    if tree is None:
        tree, _exc = parse_ast_safely(text)
        if tree is None:
            logger.debug("插入点定位解析失败(降级原位置): %s", _exc)
            return insert_at
    _body = getattr(tree, "body", ())
    _head_idx = 0
    if _body and is_docstring_stmt(_body[0]):
        insert_at = max(insert_at, _body[0].end_lineno)
        _head_idx = 1
    while _head_idx < len(_body) and _is_future_import(_body[_head_idx]):
        insert_at = max(insert_at, _body[_head_idx].end_lineno)
        _head_idx += 1
    return insert_at
def ensure_os_import(text: str) -> str:
    # BOM 必须留在首行首字符：ast.parse 不接受带 BOM 的 str，首行也不被
    # 识别为 shebang/coding 头，故先剥离 BOM 再按行号计算插入点，所有
    # 返回路径统一前缀回，避免 import os 被插到 BOM 之前。
    bom = text[:1] if text.startswith("\ufeff") else ""
    text = text[len(bom):]
    tree = _parse_module_source(text)
    if tree is None and _os_import_text_fallback_bound(text):
        return bom + text
    lines = text.splitlines(keepends=True)
    if not lines:
        return bom + "import os\n"
    insert_at = _os_insert_point_head_scan(lines)
    insert_at = _os_insert_point_ast_advance(text, insert_at, tree)
    line_count = len(lines)
    insert_at = min(max(insert_at, 0), line_count)
    points = (_module_os_import_plan(tree, insert_at)
              if tree is not None else [insert_at])
    points = [min(max(point, 0), line_count) for point in points]
    if not points:
        return bom + text
    line_ending = next(
        ("\r\n" if line.endswith("\r\n") else line[-1]
         for line in lines if line.endswith(("\n", "\r"))),
        "\n",
    )
    trailing_newline = lines[-1].endswith(("\n", "\r"))
    if points[-1] == line_count and not trailing_newline:
        lines[-1] += line_ending
    for offset, point in enumerate(points):
        ending = "" if point == line_count and not trailing_newline else line_ending
        lines.insert(point + offset, "import os" + ending)
    return bom + "".join(lines)
def _count_own_definitions(tree: ast.AST) -> int:
    return sum(
        1 for _n in walk_nodes(tree)
        if isinstance(_n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        and not (_n.name.startswith("__") and _n.name.endswith("__"))
    )
def check_s02_portal_file(filepath: str, encoding: str) -> None:
    try:
        with open(filepath, encoding=encoding) as _f:
            _src = _f.read()
        _tree = ast.parse(_src)
        if _count_own_definitions(_tree) == 0 and not _has_business_stmt(_tree):
            logger.warning(
                "[S02] 写入后检测到纯门户文件: %s（仅 import，无自身定义）",
                os.path.basename(filepath),
            )
    except (SyntaxError, ValueError, RecursionError, MemoryError,
            OSError, LookupError) as _s02_err:
        logger.debug("S02 portal-file check skipped (%s): %s", type(_s02_err).__name__, _s02_err)
def _is_dunder_all_target(target: ast.AST) -> bool:
    return isinstance(target, ast.Name) and target.id == "__all__"
def _is_import_stmt(node: ast.AST) -> bool:
    return isinstance(node, (ast.Import, ast.ImportFrom))
def _is_dunder_all_assign_stmt(node: ast.AST) -> bool:
    if isinstance(node, ast.Assign):
        return any(_is_dunder_all_target(target) for target in node.targets)
    if isinstance(node, (ast.AnnAssign, ast.AugAssign)):
        return _is_dunder_all_target(node.target)
    return False
_PORTAL_STMT_PREDICATES = (
    _is_import_stmt,
    is_docstring_stmt,
    _is_dunder_all_assign_stmt,
)
def _is_portal_allowed_stmt(node: ast.AST) -> bool:
    return any(predicate(node) for predicate in _PORTAL_STMT_PREDICATES)
def _has_business_stmt(tree: ast.AST) -> bool:
    return any(not _is_portal_allowed_stmt(_n)
               for _n in ast.iter_child_nodes(tree))
IDENTIFIER_SOURCE = r"[^\W\d]\w*"
NOQA_ANY_RE = re.compile(r"#\s*noqa\b", re.IGNORECASE)
def _line_continues_to_next(source_lines: Any, lineno: int) -> bool:
    # 仅当上一行留下未闭合括号或显式续行时，下一行才是同一逻辑语句的
    # 续行；否则上一行的 noqa 属于上一条语句，不能泄漏到当前行。
    if not 1 <= lineno <= len(source_lines):
        return False
    code = code_part(str(source_lines[lineno - 1]))
    depth = 0
    for _pos, ch in iter_unquoted(code):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
    stripped = code.rstrip()
    backslashes = len(stripped) - len(stripped.rstrip("\\"))
    return depth > 0 or backslashes % 2 == 1
def has_noqa(source_lines: Any, lineno: int) -> bool:
    source_lines = _normalized_source_lines(source_lines)
    if source_lines is None:
        return False
    line_no = _coerce_lineno(lineno, invalid_log="按无 noqa 处理")
    if line_no is None:
        return False
    for check_line in (line_no, line_no - 1):
        if (check_line == line_no - 1
                and not _line_continues_to_next(source_lines, check_line)):
            continue
        if not 1 <= check_line <= len(source_lines):
            continue
        text = str(source_lines[check_line - 1])
        if not NOQA_ANY_RE.search(text):
            continue
        _start = _comment_start_at(source_lines, check_line)
        if _start >= 0 and NOQA_ANY_RE.search(text[_start:]):
            return True
    return False
_SILENT_LOG_LEVELS = {'debug', 'info'}
_LOG_LEVEL_BY_NUM = {10: 'debug', 20: 'info', 30: 'warning',
                     40: 'error', 50: 'critical'}
_UNDECODED_LEVEL = object()
def extract_log_level(node: Any) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    if not is_logger_call(node):
        return None
    func = node.func
    if func.attr == 'log' and node.args:
        decoded = _log_level_first_arg(node.args[0])
        if decoded is not _UNDECODED_LEVEL:
            return decoded
    return func.attr
def _log_level_first_arg(first: Any) -> Any:
    if isinstance(first, ast.Attribute):
        return first.attr.lower()
    if isinstance(first, ast.Constant) and isinstance(first.value, str):
        return first.value.lower()
    if isinstance(first, ast.Constant) and isinstance(first.value, int):
        return _LOG_LEVEL_BY_NUM.get(first.value)
    return _UNDECODED_LEVEL
def is_empty_handler_body(body: Any) -> bool:
    return not body or (len(body) == 1 and isinstance(body[0], ast.Pass))
def has_reraise(stmts: Any) -> bool:
    return any(isinstance(node, ast.Raise) for node in walk_stmts(stmts))
def _is_recovery_assignment(stmt: Any) -> bool:
    return (isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.AugAssign))
            and isinstance(stmt.value, (ast.Call, ast.Await)))
def has_recovery_assignment(stmts: Any) -> bool:
    return any(_is_recovery_assignment(stmt) for stmt in walk_stmts(stmts))
def has_warning_or_higher(stmts: Any) -> bool:
    for stmt in walk_stmts(stmts):
        if isinstance(stmt, ast.Call):
            level = extract_log_level(stmt)
            if level in ('warning', 'warn', 'error', 'critical',
                         'exception', 'fatal'):
                return True
    return False
def _classify_silent_stmt(stmt: Any) -> tuple[str, str | None]:
    if isinstance(stmt, ast.Pass):
        return "pass", None
    if isinstance(stmt, ast.Expr):
        if isinstance(stmt.value, ast.Call):
            level = extract_log_level(stmt.value)
            if level in _SILENT_LOG_LEVELS:
                return "log", level
            return "meaningful", None
        if isinstance(stmt.value, (ast.Constant, ast.Name)):
            return "literal_noop", None
        return "meaningful", None
    if isinstance(stmt, ast.Return):
        if any(isinstance(node, (ast.Call, ast.Await))
               for node in iter_own_scope(stmt, include_self=True)):
            return "meaningful", None
        return "return", None
    if isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        if _is_recovery_assignment(stmt):
            return "meaningful", None
        return "assignment", None
    if isinstance(stmt, (ast.Import, ast.ImportFrom)):
        return "local_import", None
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return "local_def", None
    return "meaningful", None
def _collect_silent_signals(stmts: Any) -> tuple[bool, bool, set[str], bool, bool]:
    has_only_log_or_pass = True
    has_log = False
    log_levels_found: set = set()
    has_return = False
    has_effective = False
    for stmt in stmts:
        kind, level = _classify_silent_stmt(stmt)
        if kind == "log":
            has_log = True
            log_levels_found.add(level)
            continue
        if kind == "return":
            has_return = True
            continue
        if kind == "local_def":
            continue
        if kind == "meaningful":
            has_only_log_or_pass = False
            has_effective = True
    return (has_only_log_or_pass, has_log, log_levels_found, has_return,
            has_effective)
def is_silent_handler(handler: Any, source_lines: Any = None) -> tuple[bool, str]:
    if source_lines is not None and has_noqa(source_lines, handler.lineno):
        return False, "has_noqa"
    stmts = handler.body
    if is_empty_handler_body(stmts):
        return True, "empty_body" if not stmts else "bare_pass"
    if has_reraise(stmts):
        return False, "has_reraise"
    if has_warning_or_higher(stmts):
        return False, "has_warning"
    return _judge_silent_signals(stmts)
def _judge_silent_signals(stmts: Any) -> tuple[bool, str]:
    (has_only_log_or_pass, has_log, log_levels_found, has_return,
     has_effective) = _collect_silent_signals(stmts)
    if has_only_log_or_pass and has_log:
        return True, f"silent_log:{','.join(sorted(log_levels_found))}"
    if has_only_log_or_pass and not has_log and not has_return:
        return True, "silent_pass_chain"
    if has_return and not has_effective:
        return True, "silent_return"
    return False, "has_meaningful_handling"
def _is_logger_varname(nm: str) -> bool:
    n = nm.strip('_').lower()
    return n in ('log', 'logger') or n.endswith(('logger', '_log'))
_LOGGER_METHOD_NAMES = frozenset({
    'debug', 'info', 'warning', 'warn', 'error', 'critical',
    'exception', 'fatal', 'log',
})
def _logger_receiver_is_logging(receiver: ast.AST) -> bool:
    if isinstance(receiver, ast.Name):
        return receiver.id == 'logging' or _is_logger_varname(receiver.id)
    if isinstance(receiver, ast.Attribute):
        return _is_logger_varname(receiver.attr)
    return _is_inline_getlogger_call(receiver)
def is_logger_call(call: ast.Call) -> bool:
    fn = call.func
    return (isinstance(fn, ast.Attribute)
            and fn.attr in _LOGGER_METHOD_NAMES
            and _logger_receiver_is_logging(fn.value))
def _is_inline_getlogger_call(v: ast.AST) -> bool:
    return (isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute)
            and v.func.attr == 'getLogger'
            and isinstance(v.func.value, ast.Name)
            and (v.func.value.id == 'logging'
                 or _is_logger_varname(v.func.value.id)))
def get_code_snippet(
        source: Any, line: Any, context=_DEFAULT_CONTEXT_LINES) -> str:
    window = _line_window(source, line, context)
    if window is None:
        return ""
    start, end, window_lines, _line_no = window
    return "\n".join(str(s) for s in window_lines[start:end])
_SUPPRESS_NAMESPACE = r'[A-Za-z_][\w.\-]*'
_SUPPRESS_RE = re.compile(
    rf'#\s*{_SUPPRESS_NAMESPACE}:suppress[\s=]+(.+?)\s*$',
    re.IGNORECASE
)
_NOQA_RE = re.compile(
    r'#\s*noqa(?::\s*([A-Za-z\d_.\-](?:[,.\w\s]|-(?!-))*?))?'
    r'(?:\s+(?:--|#|[-\u2013\u2014])\s*.*)?\s*$',
    re.IGNORECASE
)
_RULE_ID_RE = re.compile(
    r'^(?:SYM-[A-Z_]\w*(?:\.[A-Z_]\w*)*'
    r'|[A-Z]{1,4}[-]?[A-Z]?\d{1,3}[A-Z]?'
    r'|[A-Z]{2,}-[A-Z](?:[A-Z0-9]|-(?=[A-Z0-9]))*'
    r'|[A-Za-z][A-Za-z0-9]*(?:_[A-Za-z0-9]+)+'
    r'|[A-Z]{1,4}\d{1,3}(?:-[A-Za-z0-9_]+)+)$',
    re.IGNORECASE
)
_SUPPRESS_KEYWORD_MAP = {
    'eval': 'code_execution', 'exec': 'code_execution',
    'os.system': 'code_execution', 'system': 'code_execution',
    'shell': 'code_execution', 'subprocess': 'code_execution',
    '__import__': 'code_execution', 'dynamic_import': 'code_execution',
    'os.remove': 'file_operations', 'os.unlink': 'file_operations',
    'os.rmdir': 'file_operations', 'shutil.rmtree': 'file_operations',
    'file_deletion': 'file_operations', 'recursive_deletion': 'file_operations',
    'path_traversal': 'file_operations',
    'network': 'network', 'http': 'network', 'socket': 'network',
    'orphan': 'rule:ORPHAN',
    'empty_function': 'rule:D07', 'pass_stub': 'rule:D07',
    'stub_function': 'rule:D18', 'dead_stub': 'rule:D18',
}
def _parse_noqa_categories(noqa_m) -> set:
    categories = set()
    noqa_rules = noqa_m.group(1)
    if not noqa_rules:
        categories.add('all')
        return categories
    for part in re.split(r"[,\s]+", noqa_rules):
        _kw = part.strip().lower()
        if not _kw:
            continue
        categories |= (_suppress_part_category(_kw, literal_titles=False)
                       or {f'rule:{_kw.upper()}'})
    return categories
_SUPPRESS_FAMILY_TAGS = frozenset({'sym-taint', 'taint'})
def _suppress_part_category(part: str, *, literal_titles: bool = True) -> set:
    _kw = part.strip()
    _lower = _kw.lower()
    if _lower == 'all':
        return {'all'}
    if _lower in _SUPPRESS_KEYWORD_MAP:
        return {_SUPPRESS_KEYWORD_MAP[_lower]}
    if _lower in ('code_execution', 'file_operations', 'network'):
        return {_lower}
    if _lower in _SUPPRESS_FAMILY_TAGS:
        return {f'rule:{_kw.upper()}'}
    if _RULE_ID_RE.match(part.upper()):
        return {f'rule:{part.upper()}'}
    token = _kw.strip()
    if literal_titles and token and not token.isascii():
        return {token}
    return set()
def _parse_suppress_categories(m) -> set:
    categories = set()
    spec = m.group(1).strip()
    if spec == 'all':
        categories.add('all')
        return categories
    for part in spec.replace(',', ' ').split():
        categories |= _suppress_part_category(part)
    return categories
def _apply_module_level_suppressions(suppressions: dict,
                                     line_count: int,
                                     module_suppress: set) -> dict:
    if not module_suppress:
        return suppressions
    for i in range(1, line_count + 1):
        suppressions.setdefault(i, set()).update(module_suppress)
    return suppressions
def _comment_suppress_categories(comment: str):
    m = _SUPPRESS_RE.search(comment)
    noqa_m = _NOQA_RE.search(comment)
    if not m and not noqa_m:
        return None
    categories = set()
    if noqa_m:
        categories |= _parse_noqa_categories(noqa_m)
    if m:
        categories |= _parse_suppress_categories(m)
    return categories
_SUPPRESS_HINT_RE = re.compile(
    rf"#.*(?:noqa|{_SUPPRESS_NAMESPACE}:suppress)", re.IGNORECASE)
_INLINE_SUPPRESS_MARKER_RE = re.compile(
    rf'#\s*(nosec|noqa|{_SUPPRESS_NAMESPACE}:suppress)\b(.*)$',
    re.IGNORECASE)
def _inline_comment_categories(marker, comment: str) -> set:
    keyword = (marker.group(1) or "").lower()
    if keyword == "nosec":
        ids = _audit_rule_ids(marker.group(2) or "")
        return {"all"} if not ids else {f"rule:{rule_id}" for rule_id in ids}
    return _comment_suppress_categories(comment) or set()
def _inline_category_targets(category: str) -> set:
    raw = str(category).strip()
    targets = {raw.lower()}
    canonical = _CATEGORY_TITLE_ALIASES.get(raw, raw)
    targets.add(canonical.lower())
    targets.update(rule_id.lower()
                   for rule_id in _E1_CATEGORY_NOSEC_RULES.get(canonical, ()))
    return targets
def _inline_categories_hit(categories: set, targets: set) -> bool:
    for item in categories:
        token = item.removeprefix('rule:')
        if token.lower() in targets:
            return True
    return False
def _comment_hash_index(line: str, line_start: int, spans) -> int:
    for index, char in enumerate(line):
        if char != '#':
            continue
        offset = line_start + index
        if any(span[0] <= offset < span[1] for span in spans or ()):
            continue
        return index
    return -1
def inline_suppressed_at(content: str, pos: int, category: str,
                         string_spans=None) -> bool:
    line_start = max(
        content.rfind('\n', 0, pos), content.rfind('\r', 0, pos)) + 1
    line_end = min(
        (index for index in (content.find('\n', pos), content.find('\r', pos))
         if index >= 0),
        default=len(content),
    )
    line = content[line_start:line_end]
    spans = (string_spans if string_spans is not None
             else py_string_token_offsets(content))
    comment_start = _comment_hash_index(line, line_start, spans)
    if comment_start < 0:
        return False
    comment = line[comment_start:]
    marker = _INLINE_SUPPRESS_MARKER_RE.search(comment)
    if marker is None:
        return False
    categories = _inline_comment_categories(marker, comment[marker.start():])
    if not categories:
        return False
    if 'all' in categories:
        return True
    if _inline_categories_hit(categories, _inline_category_targets(category)):
        return True
    return _category_suppressed(categories, category)
def _comment_start_rows(lines: list) -> dict:
    spans = comment_only_spans(_join_physical_lines(lines))
    if spans is not None:
        return {row: items[0][0] for row, items in spans.items() if items}
    starts: dict = {}
    _quote_state = ""
    for i, line in enumerate(lines, 1):
        _start, _quote_state = scan_line_quote_state(line, _quote_state)
        if _start >= 0:
            starts[i] = _start
    return starts
def _comment_start_at(lines: Any, lineno: int) -> int:
    texts = [str(line) for line in lines]
    if not 1 <= lineno <= len(texts):
        return -1
    if "#" not in texts[lineno - 1]:
        return -1
    return _comment_start_rows(texts).get(lineno, -1)
def _statement_enclosing_spans(lines: list) -> tuple[tuple[int, int], ...]:
    tree, _exc = parse_ast_safely(_join_physical_lines(lines))
    if tree is None:
        return ()
    return tuple(
        (node.lineno, node.end_lineno)
        for node in walk_nodes(tree)
        if isinstance(node, ast.stmt) and node.end_lineno is not None
        and node.end_lineno > node.lineno
    )
def parse_suppressions(source_code: str) -> dict:
    suppressions = {}
    lines = _normalized_source_lines(source_code) or []
    _candidates = [i for i, line in enumerate(lines, 1)
                   if _SUPPRESS_HINT_RE.search(line)]
    if not _candidates:
        return suppressions
    _module_level_suppress = set()
    _starts = _comment_start_rows(lines)
    _enclosing_spans = (
        _statement_enclosing_spans(lines)
        if any(lines[i - 1].startswith('#') for i in _candidates) else ()
    )
    for i in _candidates:
        _cstart = _starts.get(i, -1)
        if _cstart < 0:
            continue
        categories = _comment_suppress_categories(lines[i - 1][_cstart:])
        if not categories:
            continue
        if (lines[i - 1].startswith('#')
                and not any(start < i <= end for start, end in _enclosing_spans)):
            _module_level_suppress.update(categories)
        suppressions[i] = categories
    return _apply_module_level_suppressions(
        suppressions, len(lines), _module_level_suppress)
def _rule_id_fallback_hit(suppressed: set, category: str) -> bool:
    _cat_norm = re.sub(r'[-_]', '', category.upper())
    if not _cat_norm:
        return False
    return any(
        _sup.startswith('rule:')
        and re.sub(r'[-_]', '', _sup[5:].upper()) == _cat_norm
        for _sup in suppressed
    )
def _category_suppressed(suppressed: set, category: str) -> bool:
    if not isinstance(category, str):
        return False
    if category in suppressed:
        return True
    canonical_name = _CATEGORY_TITLE_ALIASES.get(category, category)
    if any(_CATEGORY_TITLE_ALIASES.get(token, token) == canonical_name
           for token in suppressed):
        return True
    if _rule_id_fallback_hit(suppressed, category):
        return True
    mapped = _SUPPRESS_KEYWORD_MAP.get(category.lower())
    if mapped and mapped in suppressed:
        return True
    if any(f"rule:{rid}" in suppressed for rid in equiv_rule_ids(category)):
        return True
    canonical = _CATEGORY_TITLE_ALIASES.get(category, category)
    family = _E1_CATEGORY_NOSEC_RULES.get(canonical, frozenset())
    return any(f"rule:{rule_id}" in suppressed for rule_id in family)
def is_suppressed(suppressions: dict, lineno: int, category: str) -> bool:
    if not suppressions or not _is_valid_lineno(lineno):
        return False
    suppressed = suppressions.get(lineno)
    if not suppressed:
        return False
    return 'all' in suppressed or _category_suppressed(suppressed, category)
def _finding_is_suppressed(v: dict, suppressions: dict,
                           rule_category_map: dict) -> bool:
    line = v.get("line")
    rule_id = str(v.get("rule_id") or "")
    if rule_id and is_suppressed(suppressions, line, rule_id):
        return True
    category = rule_category_map.get(rule_id)
    return bool(category and is_suppressed(suppressions, line, category))
def filter_suppressed_findings(
    findings: list, suppressions: dict, rule_category_map: dict,
) -> list:
    return [
        v for v in findings
        if not isinstance(v, dict)
        or not _finding_is_suppressed(v, suppressions, rule_category_map)
    ]
def normalize_rule_source(source: Any) -> str:
    if isinstance(source, str):
        return source
    if isinstance(source, (bytes, bytearray)):
        return decode_source_bytes(bytes(source))
    if isinstance(source, (list, tuple)):
        try:
            return _join_physical_lines(source)
        except (AttributeError, TypeError) as _e:
            log_swallowed(__name__, _e, context='normalize_rule_source:SourceTypeError')
            return ""
    return ""
def _suppress_line(finding: Any) -> int:
    if isinstance(finding, dict):
        line = finding.get('line', 0)
    else:
        line = getattr(finding, 'line', 0)
    return line if isinstance(line, int) and not isinstance(line, bool) \
        and line > 0 else 0
def apply_rule_suppress(findings: list, source: Any,
                        rule_id: str) -> list:
    if not findings:
        return findings
    code = normalize_rule_source(source)
    if not code:
        return findings
    try:
        suppress_map = parse_suppressions(code)
    except Exception:  # noqa: BLE001 -- suppress解析失败不阻断检测主流程(容错降级)
        logger.warning("suppress解析失败, %s跳过suppress检查", rule_id)
        return findings
    if not suppress_map:
        return findings
    kept: list = []
    for finding in findings:
        line_num = _suppress_line(finding)
        try:
            suppressed = is_suppressed(suppress_map, line_num, rule_id)
        except Exception:  # noqa: BLE001 -- suppress检查失败不阻断检测(容错降级)
            logger.warning("suppress检查失败, %s:%s跳过suppress",
                           rule_id, line_num)
            suppressed = False
        if not suppressed:
            kept.append(finding)
    return kept
_INLINE_SUPPRESS_CACHE_MAX = 1024
def release_scan_base_caches() -> int:
    n = release_source_caches()
    _INLINE_SUPPRESS_CACHE.clear()
    _token_type_span_items.cache_clear()
    comment_tokens.cache_clear()
    _string_token_row_spans_cached.cache_clear()
    release_tokenize_caches()
    clear_shared_tokenize_cache()
    return n
_NOSEC_RULE_ID_RE = re.compile(
    r"(?<![A-Z0-9-])"
    r"(?:[A-Z]{1,6}\d{1,4}(?:-[A-Z]{1,12}|-\d{1,3})*"
    r"|[A-Z]{1,6}(?:-[A-Z]{1,12}|-\d{1,3})+)"
    r"(?![A-Z0-9-])")
def _audit_rule_ids(comment_tail: str) -> set[str]:
    return set(_NOSEC_RULE_ID_RE.findall(comment_tail.upper()))
_INLINE_SUPPRESS_CACHE: dict[str, tuple[tuple[str, ...], dict]] = {}
def _inline_suppressions(filepath: str, lines: list) -> dict:
    snapshot = tuple(lines)
    cached = _INLINE_SUPPRESS_CACHE.get(filepath)
    if cached is not None and cached[0] == snapshot:
        return cached[1]
    parsed = parse_suppressions("\n".join(lines))
    if len(_INLINE_SUPPRESS_CACHE) < _INLINE_SUPPRESS_CACHE_MAX:
        _INLINE_SUPPRESS_CACHE[filepath] = (snapshot, parsed)
    return parsed
def has_inline_suppression(filepath: str, lineno: int, rule_id: str) -> bool:
    lines = src_lines(filepath)
    if not lines or not (1 <= lineno <= len(lines)):
        return False
    suppressions = _inline_suppressions(filepath, lines)
    ids = equiv_rule_ids(rule_id)
    category_targets = tuple(
        category for category, rules in _E1_CATEGORY_NOSEC_RULES.items()
        if ids & rules
    )
    if any(is_suppressed(suppressions, lineno, target)
           for target in (rule_id, *category_targets)):
        return True
    start = _comment_start_at(lines, lineno)
    if start < 0:
        return False
    comment = lines[lineno - 1][start:]
    marker = _INLINE_SUPPRESS_MARKER_RE.search(comment)
    if marker is None:
        return False
    if marker.group(1).lower() != "nosec":
        return False
    audit_ids = _audit_rule_ids(comment[marker.start():])
    if not audit_ids:
        return True
    return bool(audit_ids & ids)
_RULE_EQUIV = {
    "S102": "B102", "S105": "B105", "S106": "B106", "S107": "B107",
    "S110": "B110", "S112": "B112", "S301": "B301", "S307": "B307",
    "S310": "B310",
    "S324": "B324", "S506": "B506", "S602": "B602", "S603": "B603",
    "S604": "B604", "S605": "B605", "S606": "B606", "S607": "B607",
    "S608": "B608", "S609": "B609",
}
_RULE_EQUIV_REV = {v: k for k, v in _RULE_EQUIV.items()}
def equiv_rule_ids(rule_id: str) -> set[str]:
    ids = {rule_id, _RULE_EQUIV.get(rule_id, ""), _RULE_EQUIV_REV.get(rule_id, "")}
    ids.discard("")
    return ids
_E1_NOSEC_RE = re.compile(r"#\s*(nosec|noqa)\b(.*)", re.IGNORECASE)
_E1_CATEGORY_NOSEC_RULES = {
    "command_injection": frozenset({
        "SE-02", "B602", "B603", "B604", "B605", "B606", "B607", "B609"}),
    "code_execution": frozenset({"B102", "B307", "S102", "S307"}),
    "code_injection": frozenset({"B307"}),
    "sql_injection": frozenset({"SE-05", "B608"}),
    "deserialization": frozenset({
        "SE-04", "S301", "S302", "B301", "B302", "B303", "B306"}),
    "path_traversal": frozenset({"SE-06", "B310", "SS-02"}),
    "hardcoded_secret": frozenset({
        "SE-03", "B105", "B106", "B107", "SS-03"}),
    "xss": frozenset({"SE-16"}),
    "xxe": frozenset({"SE-19"}),
    "weak_crypto": frozenset({"SE-10"}),
    "ssrf": frozenset({"S113", "B113"}),
}
_CATEGORY_TITLE_ALIASES = {
    '危险系统调用': 'code_execution',
    '不安全的反序列化': 'deserialization',
    '路径穿越风险': 'path_traversal',
    '网络请求无超时': 'ssrf',
    '硬编码密钥': 'hardcoded_secret',
    '命令注入': 'command_injection',
    '代码注入': 'code_injection',
    'SQL注入': 'sql_injection',
}
def line_has_applicable_nosec(
    source: str, line_no: int, category: str,
    extra_rules: frozenset = frozenset(),
) -> bool:
    if isinstance(line_no, bool):
        return False
    line_no = _coerce_lineno(line_no)
    if not source or not _is_valid_lineno(line_no):
        return False
    lines = _universal_newlines(source).split("\n")
    line = lines[line_no - 1] if line_no <= len(lines) else None
    if line is None or _E1_NOSEC_RE.search(line) is None:
        return False
    start = _comment_start_at(lines, line_no)
    m = _E1_NOSEC_RE.search(line[start:]) if start >= 0 else None
    if m is None:
        return False
    if m.group(1).lower() == "noqa":
        categories = _comment_suppress_categories(m.group(0)) or set()
        return 'all' in categories or any(
            _category_suppressed(categories, target)
            for target in (category, *extra_rules)
        )
    ids = _audit_rule_ids(m.group(2) or "")
    if not ids:
        return True
    return _nosec_ids_apply(ids, category, extra_rules)
_TAINT_SUPPRESS_TAGS: tuple[str, ...] = ("SYM-TAINT", "TAINT")
def line_has_taint_suppression(source: str, lineno: int,
                               sink: str = "") -> bool:
    if not source or isinstance(lineno, bool):
        return False
    lineno = _coerce_lineno(lineno)
    if not _is_valid_lineno(lineno):
        return False
    suppressions = parse_suppressions(source)
    if not suppressions:
        return False
    tags = _TAINT_SUPPRESS_TAGS + ((f"SYM-{sink}",) if sink else ())
    return any(is_suppressed(suppressions, lineno, tag) for tag in tags)
def _nosec_ids_apply(ids: set[str], category: str,
                     extra_rules: frozenset) -> bool:
    canonical = _CATEGORY_TITLE_ALIASES.get(category or "", category or "")
    wanted = _E1_CATEGORY_NOSEC_RULES.get(canonical, frozenset())
    if extra_rules:
        wanted = wanted | frozenset(extra_rules)
    equiv_ext: set[str] = set()
    for rid in ids:
        equiv_ext.update(equiv_rule_ids(rid))
    return bool(equiv_ext & wanted)
_TOKENIZE_CACHE_MAX = 16
_TOKENIZE_CACHE: dict[str, tuple] = {}
_TOKENIZE_CACHE_LOCK = threading.Lock()
def clear_shared_tokenize_cache() -> None:
    with _TOKENIZE_CACHE_LOCK:
        _TOKENIZE_CACHE.clear()
def tokenize_source_cached(src: str):
    if not isinstance(src, str):
        return None
    with _TOKENIZE_CACHE_LOCK:
        cached = _TOKENIZE_CACHE.get(src)
    if cached is not None:
        return cached
    try:
        tokens = tuple(tokenize.generate_tokens(
            io.StringIO(_tokenize_input(src)).readline))
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as _e:
        logger.debug("tokenize 失败(返回 None): %s", _e)
        return None
    with _TOKENIZE_CACHE_LOCK:
        if len(_TOKENIZE_CACHE) >= _TOKENIZE_CACHE_MAX:
            _TOKENIZE_CACHE.clear()
        _TOKENIZE_CACHE[src] = tokens
    return tokens
def split_lines_lf(content: str) -> list[str]:
    if not content:
        return []
    rows = content.split("\n")
    if rows[-1] == "":
        rows.pop()
    return rows
def _collect_string_token_spans(content: str, string_types: set[int],
                                row_lengths: dict[int, int]) -> dict[int, list[tuple[int, int]]]:
    spans: dict[int, list[tuple[int, int]]] = {}
    for tok in tokenize.generate_tokens(io.StringIO(content).readline):
        if tok.type not in string_types:
            continue
        for row, begin, stop in _token_row_ranges(tok, row_lengths):
            spans.setdefault(row, []).append((begin, stop))
    return spans
@lru_cache(maxsize=_TOKEN_PROJECTION_CACHE_MAX)
def _string_token_row_spans_cached(
    content: str,
) -> tuple[tuple[int, tuple[tuple[int, int], ...]], ...] | None:
    try:
        content = _tokenize_input(content)
        row_lengths = {
            row_no: len(row) for row_no, row in enumerate(split_lines_lf(content), 1)
        }
        spans = _collect_string_token_spans(
            content, _STRING_TOKEN_TYPES, row_lengths)
        return _freeze_row_spans(spans)
    except (tokenize.TokenError, SyntaxError, ValueError) as _e:
        log_swallowed(__name__, _e, context='string_token_row_spans:tokenize.TokenError')
        return None
def string_token_row_spans(content: str) -> dict[int, list[tuple[int, int]]] | None:
    return _thaw_row_spans(_string_token_row_spans_cached(content))
def _token_row_ranges(tok: tokenize.TokenInfo,
                      row_lengths: dict[int, int]) -> Iterator[tuple[int, int, int]]:
    (srow, scol), (erow, ecol) = tok.start, tok.end
    for row in range(srow, erow + 1):
        begin = scol if row == srow else 0
        stop = ecol if row == erow else row_lengths.get(row, 0)
        yield row, begin, stop
def _row_spans_record(row_spans: dict, r0: int, c0: int, r1: int, c1: int,
                      lines: list) -> None:
    if r0 == r1:
        row_spans.setdefault(r0, []).append((c0, c1))
        return
    row_spans.setdefault(r0, []).append((c0, len(lines[r0 - 1]) + 1))
    for r in range(r0 + 1, r1):
        row_spans.setdefault(r, []).append((0, len(lines[r - 1]) + 1))
    row_spans.setdefault(r1, []).append((0, c1))
def _line_start_offsets(lines: list[str]) -> list[int]:
    starts = [0]
    for ln in lines[:-1]:
        starts.append(starts[-1] + len(ln) + 1)
    return starts
def _append_token_projection(tok, line_starts: list[int], lines: list[str],
                             masked: list, str_offsets: list,
                             row_spans: dict) -> None:
    (r0, c0), (r1, c1) = tok.start, tok.end
    is_fstring = tok.type in _FSTRING_TOKEN_TYPES
    if (tok.type not in (tokenize.STRING, tokenize.COMMENT)
            and not is_fstring):
        return
    s = line_starts[r0 - 1] + c0
    e = line_starts[r1 - 1] + c1
    masked.append((s, e))
    if tok.type != tokenize.STRING and tok.type != _FSTRING_MIDDLE_TYPE:
        return
    str_offsets.append((s, e, tok.string,
                        tok.type == _FSTRING_MIDDLE_TYPE))
    _row_spans_record(row_spans, r0, c0, r1, c1, lines)
@lru_cache(maxsize=_TOKEN_PROJECTION_CACHE_MAX)
def _tokenize_projections(content: str) -> tuple | None:
    try:
        content = _tokenize_input(content)
        toks = tuple(tokenize.generate_tokens(io.StringIO(content).readline))
    except Exception as e:  # noqa: BLE001
        logger.warning("[SecAudit] tokenize 失败（共享缓存降级空序列）: %s", e)
        return None
    lines = content.split('\n')
    line_starts = _line_start_offsets(lines)
    masked: list[tuple[int, int]] = []
    str_offsets: list[tuple[int, int, str, bool]] = []
    row_spans: dict[int, list[tuple[int, int]]] = {}
    for tok in toks:
        _append_token_projection(
            tok, line_starts, lines, masked, str_offsets, row_spans)
    return (tuple(masked), tuple(str_offsets),
            {r: tuple(spans) for r, spans in row_spans.items()})
def scan_masked_spans(content: str, is_py: bool) -> list[tuple[int, int]]:
    if not is_py:
        return []
    _p = _tokenize_projections(content)
    return list(_p[0]) if _p is not None else []
def is_masked_offset(spans: list[tuple[int, int]], pos: int) -> bool:
    return any(s <= pos < e for s, e in spans)
def release_tokenize_caches() -> int:
    n = _tokenize_projections.cache_info().currsize
    _tokenize_projections.cache_clear()
    return n
def py_string_token_offsets(content: str) -> list[tuple[int, int, str, bool]] | None:
    _p = _tokenize_projections(content)
    return list(_p[1]) if _p is not None else None
def string_token_body(raw: str, is_text_segment: bool = False) -> str:
    if is_text_segment:
        return raw
    m = re.match(r"^[rbfuRBFU]{0,3}", raw)
    rest = raw[m.end():]
    if not rest or rest[0] not in ("\"", "'"):
        return raw
    q = rest[0]
    delim = q * 3 if rest[:3] == q * 3 else q
    return rest[len(delim):].removesuffix(delim)
def py_string_row_spans(content: str) -> dict[int, tuple[tuple[int, int], ...]] | None:
    _p = _tokenize_projections(content)
    return dict(_p[2]) if _p is not None else None
_IM_HEAD_IMPORT_RE = re.compile(r"import\s+")
_IM_FROM_IMPORT_HEAD_RE = re.compile(
    rf"from\s+(?:{IDENTIFIER_SOURCE}[\w.]*\s+import"
    r"|\.+[\w.]*\s+import|\.+import)(?=\s|\(|\*)"
)
_IM_MODULE_TOKEN_RE = re.compile(rf"{IDENTIFIER_SOURCE}[\w.]*")
_IM_IMPORTED_NAME_TOKEN_RE = re.compile(
    rf"(?:{IDENTIFIER_SOURCE}|\*)[\w.*]*")
_IM_COMMA_TOKEN_RE = re.compile(r"\s*,\s*")
_IM_AS_CLAUSE_RE = re.compile(rf"\s+as\s+{IDENTIFIER_SOURCE}")
_IM_OPEN_PAREN_RE = re.compile(r"\(\s*")
_IM_CLOSE_PAREN_RE = re.compile(r"\s*\)")
def _im_skip_spaces(s: str, pos: int) -> int:
    while pos < len(s) and s[pos].isspace():
        pos += 1
    return pos
def _im_match_import_head(s: str) -> tuple[int, re.Pattern[str], bool] | None:
    m = _IM_HEAD_IMPORT_RE.match(s)
    if m is not None:
        return m.end(), _IM_MODULE_TOKEN_RE, False
    m = _IM_FROM_IMPORT_HEAD_RE.match(s)
    if m is None:
        return None
    paren = False
    pos = _im_skip_spaces(s, m.end())
    pm = _IM_OPEN_PAREN_RE.match(s, pos)
    if pm is not None:
        paren = True
        pos = pm.end()
    return pos, _IM_IMPORTED_NAME_TOKEN_RE, paren
def strip_import_line_comment(line: str) -> str:
    return code_part(line).rstrip()
def is_import_like_line(line: str) -> bool:
    s = strip_import_line_comment(line)
    if not s:
        return False
    head = _im_match_import_head(s)
    if head is None:
        return False
    pos, token_re, paren = head
    tm = token_re.match(s, pos)
    if tm is None:
        return paren and not s[pos:]
    pos = _im_consume_import_items(s, tm.end(), token_re)
    if paren:
        pos = _im_consume_paren_tail(s, pos)
    return not s[pos:]
def _im_consume_import_items(s: str, pos: int,
                             token_re: re.Pattern[str]) -> int:
    while True:
        am = _IM_AS_CLAUSE_RE.match(s, pos)
        if am is not None:
            pos = am.end()
        cm = _IM_COMMA_TOKEN_RE.match(s, pos)
        if cm is None:
            break
        tm = token_re.match(s, cm.end())
        if tm is None:
            break
        pos = tm.end()
    return pos
def _im_consume_paren_tail(s: str, pos: int) -> int:
    tc = _IM_COMMA_TOKEN_RE.match(s, pos)
    if tc is not None:
        pos = tc.end()
    cp = _IM_CLOSE_PAREN_RE.match(s, pos)
    if cp is not None:
        pos = cp.end()
    return pos
__all__ = [
    "IDENTIFIER_SOURCE",
    "NOQA_ANY_RE",
    "apply_rule_suppress",
    "check_s02_portal_file",
    "clear_shared_tokenize_cache",
    "code_token_signature",
    "comment_only_spans",
    "comment_tokens",
    "ensure_os_import",
    "equiv_rule_ids",
    "extract_log_level",
    "filter_suppressed_findings",
    "get_code_snippet",
    "has_inline_suppression",
    "has_noqa",
    "has_nosec_marker",
    "has_recovery_assignment",
    "has_reraise",
    "has_warning_or_higher",
    "identifier_tokens",
    "inline_suppressed_at",
    "is_empty_handler_body",
    "is_import_like_line",
    "is_logger_call",
    "is_masked_offset",
    "is_silent_handler",
    "is_suppressed",
    "line_has_applicable_nosec",
    "line_has_taint_suppression",
    "normalize_rule_source",
    "nosec_comment_lines",
    "parse_suppressions",
    "py_string_row_spans",
    "py_string_token_offsets",
    "release_scan_base_caches",
    "release_tokenize_caches",
    "scan_masked_spans",
    "split_lines_lf",
    "string_comment_spans",
    "string_token_body",
    "string_token_row_spans",
    "strip_import_line_comment",
    "tokenize_source_cached",
]
logger.info(
    "diag_shared_source_scan L0 文本扫描域（词法投影/抑制解析/静默判定/导入行语义/导入注入）已加载: %d 项导出",
    len(__all__))

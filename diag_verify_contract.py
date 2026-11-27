from __future__ import annotations

import ast
import io
import logging
import os
import re
import sqlite3
import tokenize
from collections.abc import Iterable
from functools import lru_cache, partial
from pathlib import Path
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    MATCH_CAPTURE_NODES,
    MATCH_REST_NODES,
    collect_param_names,
    import_alias_bound_names,
    is_docstring_stmt,
    pattern_capture_name,
)
from jwsgj.diag_shared_source_core import (
    _markdown_table_cells,
    parse_cached,
    read_source,
    scan_line_quote_state,
)
from jwsgj.diag_shared_source_scan import (
    comment_only_spans,
)
from jwsgj.diag_types_vocab import (
    DEFAULT_VIRTUAL_FILENAME,
    MSG_EXCEPTION_BROAD_HANDLER,
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import is_pruned_dirname

_PathInput = str | bytes | bytearray | os.PathLike[str]
_log = logging.getLogger(__name__)
__all__ = [
    "detect_table_sql_mismatch",
    "extract_code_sql_tables",
    "wiring_declarations",
]
_CHECK_ID = "XT01"
_NAME_PREVIEW_LIMIT = 5
_ERROR_TEXT_LIMIT = 80
_SQLITE_TIMEOUT_S = 5
_STRUCTURE_MASK_CACHE_SIZE = 16
_SQL_UNQUOTED_IDENTIFIER = r"(?:[^\W\d]\w*)"
_SQL_IDENTIFIER = (
    r'(?:\w+'
    r'|"(?:[^"]|"")*"'
    r"|'(?:[^']|'')*'"
    r'|`(?:[^`]|``)*`'
    r'|\[[^\]]+\])'
)
_TABLE_NAME_SUFFIX = (
    rf'(?:{_SQL_IDENTIFIER}\.)*'
    r'(?:'
    r'"((?:[^"]|"")*)"'
    r"|'((?:[^']|'')*)'"
    r'|`((?:[^`]|``)*)`'
    r'|(\w+)(?![\w?%{$])'
    r'|\[([^\]]+)\])'
)
def _table_name_of(match: re.Match) -> str:
    for group, quote in ((1, '"'), (2, "'"), (3, '`')):
        value = match.group(group)
        if value is not None:
            return value.replace(quote * 2, quote)
    return match.group(4) or match.group(5) or ""
_RE_INSERT = re.compile(
    r'\b(?:INSERT\s+(?:OR\s+\w+\s+)?|REPLACE\s+)INTO\s+'
    + _TABLE_NAME_SUFFIX,
    re.IGNORECASE
)
_RE_CREATE_TABLE = re.compile(
    r'\bCREATE\s+(?:TEMP(?:ORARY)?\s+)?(?:VIRTUAL\s+)?TABLE\s+'
    r'(?:IF\s+NOT\s+EXISTS\s+)?' + _TABLE_NAME_SUFFIX,
    re.IGNORECASE
)
_RE_CREATE_VIEW = re.compile(
    r'\bCREATE\s+(?:TEMP(?:ORARY)?\s+)?VIEW\s+'
    r'(?:IF\s+NOT\s+EXISTS\s+)?' + _TABLE_NAME_SUFFIX,
    re.IGNORECASE
)
_RE_FROM_TABLE = re.compile(
    r'\bFROM\s+' + _TABLE_NAME_SUFFIX,
    re.IGNORECASE
)
_RE_DELETE_TABLE = re.compile(
    r'\bDELETE\s+FROM\s+' + _TABLE_NAME_SUFFIX,
    re.IGNORECASE
)
_RE_JOIN_TABLE = re.compile(
    r'\bJOIN\s+' + _TABLE_NAME_SUFFIX,
    re.IGNORECASE
)
_RE_UPDATE_TABLE = re.compile(
    r'\bUPDATE\s+(?:OR\s+\w+\s+)?' + _TABLE_NAME_SUFFIX,
    re.IGNORECASE
)
_RE_DROP_TABLE = re.compile(
    r'\bDROP\s+TABLE\s+(?:IF\s+EXISTS\s+)?' + _TABLE_NAME_SUFFIX,
    re.IGNORECASE
)
_RE_ALTER_TABLE = re.compile(
    r'\bALTER\s+TABLE\s+' + _TABLE_NAME_SUFFIX,
    re.IGNORECASE
)
_EXCLUDED_TABLES = {
    'sqlite_master', 'sqlite_sequence', 'sqlite_stat1', 'sqlite_stat4',
}
_SQL_STATEMENT_LEAD_RE = re.compile(
    r'[\s;()]*(?:EXPLAIN(?:\s+QUERY\s+PLAN)?\b[\s(]*)?'
    r'(?:(?:UNION|EXCEPT|INTERSECT|ALL)\b[\s(]*)*',
    re.IGNORECASE)
_SQL_BOUNDARY_RE = re.compile(
    r'(?:;|\n|\b(?:UNION|EXCEPT|INTERSECT)\b)', re.IGNORECASE)
_SQL_WITH_START_RE = re.compile(
    r'^\s*WITH\s+(?:RECURSIVE\s+)?'
    rf'(?:{_SQL_UNQUOTED_IDENTIFIER}|"(?:[^"]|"")*"|`(?:[^`]|``)*`|\[[^\]]+\])',
    re.IGNORECASE)
_SQL_CTE_BODY_RE = re.compile(
    r'\bAS\s+(?:(?:NOT\s+)?MATERIALIZED\s+)?\(', re.IGNORECASE)
def _blank_range(chars: list[str], start: int, end: int) -> None:
    for offset in range(max(start, 0), min(end, len(chars))):
        if chars[offset] not in '\r\n':
            chars[offset] = ' '
@lru_cache(maxsize=_STRUCTURE_MASK_CACHE_SIZE)
def _sql_structure_mask(text: str, mask_identifiers: bool = False) -> str:
    chars = list(text)
    quote = ''
    literal_start = -1
    index = 0
    while index < len(text):
        char = text[index]
        if quote:
            if char == quote:
                if index + 1 < len(text) and text[index + 1] == quote:
                    index += 2
                    continue
                if quote == "'" or mask_identifiers:
                    _blank_range(chars, literal_start, index + 1)
                quote = ''
            index += 1
            continue
        if char in ("'", '"', '`'):
            quote = char
            literal_start = index
            index += 1
            continue
        if char == '[':
            end = text.find(']', index + 1)
            next_index = len(text) if end < 0 else end + 1
            if mask_identifiers:
                _blank_range(chars, index, next_index)
            index = next_index
            continue
        if text.startswith('--', index):
            end = text.find('\n', index + 2)
            end = len(text) if end < 0 else end
        elif text.startswith('/*', index):
            end = text.find('*/', index + 2)
            end = len(text) if end < 0 else end + 2
        else:
            index += 1
            continue
        _blank_range(chars, index, end)
        index = end
    if quote and (quote == "'" or mask_identifiers):
        _blank_range(chars, literal_start, len(chars))
    return ''.join(chars)
def _is_masked_position(source: str, masked: str, start: int) -> bool:
    return source[start:start + 1] != masked[start:start + 1]
def _has_balanced_cte_parentheses(prefix: str) -> bool:
    depth = 0
    seen_open = False
    quote = ''
    index = 0
    while index < len(prefix):
        char = prefix[index]
        if quote:
            if char == quote:
                if index + 1 < len(prefix) and prefix[index + 1] == quote:
                    index += 2
                    continue
                quote = ''
            index += 1
            continue
        if char in ("'", '"', '`'):
            quote = char
        elif char == '[':
            end = prefix.find(']', index + 1)
            index = len(prefix) if end < 0 else end + 1
            continue
        elif char == '(':
            depth += 1
            seen_open = True
        elif char == ')':
            depth -= 1
            if depth < 0:
                return False
        index += 1
    return seen_open and depth == 0 and not quote and prefix.rstrip().endswith(')')
def _is_cte_statement_prefix(prefix: str) -> bool:
    return bool(
        _SQL_WITH_START_RE.match(prefix)
        and _SQL_CTE_BODY_RE.search(prefix)
        and _has_balanced_cte_parentheses(prefix)
    )
def _is_sql_statement_start(sql_text: str, start: int) -> bool:
    if start <= 0:
        return True
    masked = _sql_structure_mask(sql_text, True)
    if _is_masked_position(sql_text, masked, start):
        return False
    statement_start = max(0, masked.rfind(';', 0, start) + 1)
    statement_prefix = masked[statement_start:start]
    prefix = statement_prefix
    boundary = 0
    for match in _SQL_BOUNDARY_RE.finditer(prefix):
        boundary = match.end()
    prefix = prefix[boundary:]
    parentheses: list[int] = []
    for index in range(statement_start, start):
        if masked[index] == '(':
            parentheses.append(index)
        elif masked[index] == ')' and parentheses:
            parentheses.pop()
    query_start = parentheses[-1] + 1 if parentheses else statement_start
    cte_prefix = _sql_structure_mask(sql_text)[query_start:start]
    return bool(
        _SQL_STATEMENT_LEAD_RE.fullmatch(prefix)
        or _is_cte_statement_prefix(cte_prefix)
        or (masked[:start].rstrip().endswith('(')
            and _has_sql_statement_context(sql_text, start))
    )
_SQL_STATEMENT_HEAD_RE = re.compile(
    r'\b(?:WITH|SELECT|INSERT|REPLACE|UPDATE|DELETE|CREATE|DROP|ALTER)\b',
    re.IGNORECASE)
_SELECT_CONTINUATION_HEADS = frozenset({'INSERT', 'REPLACE', 'CREATE'})
def _is_valid_sql_head(sql_text: str, head: re.Match) -> bool:
    if _is_sql_statement_start(sql_text, head.start()):
        return True
    return (head.group(0).upper() == 'SELECT'
            and _is_sql_select_start(sql_text, head.start()))
def _has_sql_statement_context(sql_text: str, start: int) -> bool:
    masked = _sql_structure_mask(sql_text, True)
    if _is_masked_position(sql_text, masked, start):
        return False
    statement_start = max(0, masked.rfind(';', 0, start) + 1)
    head = None
    for candidate in _SQL_STATEMENT_HEAD_RE.finditer(
            masked, statement_start, start):
        head = candidate
    return head is not None and _is_valid_sql_head(sql_text, head)
def _is_sql_table_reference(sql_text: str, start: int, *,
                            continuation: bool = False) -> bool:
    if continuation:
        return _has_sql_statement_context(sql_text, start)
    return _is_sql_statement_start(sql_text, start)
def _is_sql_select_start(sql_text: str, start: int) -> bool:
    if _is_sql_statement_start(sql_text, start):
        return True
    masked = _sql_structure_mask(sql_text, True)
    if masked[:start].rstrip().endswith('('):
        return _has_sql_statement_context(sql_text, start)
    statement_start = max(0, masked.rfind(';', 0, start) + 1)
    candidates = iter(_SQL_STATEMENT_HEAD_RE.finditer(
        masked, statement_start, start))
    candidate = next(candidates, None)
    depth = 0
    scope_heads: dict[int, re.Match] = {}
    for index in range(statement_start, start):
        while candidate is not None and candidate.start() == index:
            if candidate.group(0).upper() != 'WITH':
                scope_heads[depth] = candidate
            candidate = next(candidates, None)
        if masked[index] == '(':
            depth += 1
        elif masked[index] == ')' and depth:
            scope_heads.pop(depth, None)
            depth -= 1
    head = scope_heads.get(depth)
    return bool(
        head is not None
        and head.group(0).upper() in _SELECT_CONTINUATION_HEADS
        and _is_valid_sql_head(sql_text, head)
    )
_FTS_SUFFIXES = ('_fts', '_fts_data', '_fts_idx', '_fts_docsize', '_fts_config')
_ASCII_LOWER = str.maketrans(
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ", "abcdefghijklmnopqrstuvwxyz")
def _sql_name_key(name: str) -> str:
    return name.translate(_ASCII_LOWER)
def is_excluded_table(name: str) -> bool:
    _key = _sql_name_key(name)
    return _key in _EXCLUDED_TABLES or _key.endswith(_FTS_SUFFIXES)
def _rw_table_names(text: str) -> set[str]:
    names: set[str] = set()
    cte_cache: dict[tuple[int, int], _CteDefinitionScopes] = {}
    patterns = (
        (_RE_FROM_TABLE, True, True), (_RE_JOIN_TABLE, True, True),
        (_RE_CREATE_VIEW, False, False),
        (_RE_UPDATE_TABLE, False, False), (_RE_DELETE_TABLE, False, False),
        (_RE_DROP_TABLE, False, False), (_RE_ALTER_TABLE, False, False),
    )
    for rx, continuation, cte_visible in patterns:
        for match in rx.finditer(text):
            if not _is_sql_table_reference(
                    text, match.start(), continuation=continuation):
                continue
            name = _table_name_of(match)
            if name:
                cte_keys = (_statement_cte_keys(text, match.start(), cte_cache)
                            if cte_visible else set())
                if _sql_name_key(name) not in cte_keys:
                    names.add(name)
            if cte_visible:
                names.update(_from_list_table_names(
                    text, match.end(), cte_cache))
    return {t for t in names if not is_excluded_table(t)}
_RE_FROM_LIST_SEP_RE = re.compile(
    rf'\s*(?:AS\s+)?(?:{_SQL_IDENTIFIER})?\s*(?P<sep>,)\s*',
    re.IGNORECASE)
_TABLE_NAME_SUFFIX_RE = re.compile(_TABLE_NAME_SUFFIX, re.IGNORECASE)
def _from_list_table_names(
    text: str, offset: int,
    cte_cache: dict[tuple[int, int], _CteDefinitionScopes],
) -> set[str]:
    """FROM/JOIN 逗号列表中首个表之后的后续表引用（`FROM a, b AS c, d`）。

    每个后续项须以代码区逗号分隔（字符串/注释内的逗号终止扫描），
    并按所在语句的 CTE 定义排除同名 CTE。
    """
    names: set[str] = set()
    masked: str | None = None
    while True:
        sep_match = _RE_FROM_LIST_SEP_RE.match(text, offset)
        if sep_match is None:
            break
        if masked is None:
            masked = _sql_structure_mask(text, True)
        if _is_masked_position(text, masked, sep_match.start('sep')):
            break
        table_match = _TABLE_NAME_SUFFIX_RE.match(text, sep_match.end())
        if table_match is None:
            break
        offset = table_match.end()
        name = _table_name_of(table_match)
        if (name and _sql_name_key(name) not in _statement_cte_keys(
                text, table_match.start(), cte_cache)):
            names.add(name)
    return names
_RE_WITH_CLAUSE = re.compile(r'\bWITH\s+(?:RECURSIVE\s+)?', re.IGNORECASE)
_RE_CTE_DEFINITION = re.compile(
    rf'(?P<name>{_SQL_UNQUOTED_IDENTIFIER}|["`][^"`]+["`]|\[[^\]]+\])'
    r'(?:\s*\([^)]*\))?\s+AS\s+(?:(?:NOT\s+)?MATERIALIZED\s+)?\(',
    re.IGNORECASE)
_CteDefinitionScopes = tuple[tuple[str, int, int], ...]
def _cte_definition_scopes(text: str) -> _CteDefinitionScopes:
    masked = _sql_structure_mask(text)
    if _RE_WITH_CLAUSE.search(masked) is None:
        return ()
    definitions = list(_RE_CTE_DEFINITION.finditer(masked))
    if not definitions:
        return ()
    by_start = {match.start(): match for match in definitions}
    structural = _sql_structure_mask(text, True)
    scope_open_at: dict[int, int] = {}
    scope_close_at: dict[int, int] = {}
    parentheses: list[int] = []
    for index, char in enumerate(structural):
        if index in by_start:
            scope_open_at[index] = parentheses[-1] if parentheses else -1
        if char == '(':
            parentheses.append(index)
        elif char == ')' and parentheses:
            opening = parentheses.pop()
            scope_close_at[opening] = index
    result = []
    for match in definitions:
        opening = scope_open_at[match.start()]
        closing = scope_close_at.get(opening, len(text))
        name = _sql_name_key(_clean_column_name(match.group('name')))
        if name:
            result.append((name, opening, closing))
    return tuple(result)
def _statement_cte_keys(
    text: str, start: int,
    cache: dict[tuple[int, int], _CteDefinitionScopes],
) -> set[str]:
    masked = _sql_structure_mask(text, True)
    statement_start = max(0, masked.rfind(';', 0, start) + 1)
    statement_end = masked.find(';', start)
    if statement_end < 0:
        statement_end = len(text)
    span = (statement_start, statement_end)
    if span not in cache:
        cache[span] = _cte_definition_scopes(
            text[statement_start:statement_end])
    relative_start = start - statement_start
    return {
        name for name, opening, closing in cache[span]
        if opening < relative_start < closing
    }
_ORM_EXEC_METHODS = {"execute", "query", "raw", "executemany", "executescript"}
_ORM_EXEC_SQL_KWARGS = ('sql', 'statement', 'query', 'operation')
_ORM_TEXT_FUNCS = {"text"}
def _constant_sql_text(value: object) -> str | None:
    if isinstance(value, str):
        return value
    if isinstance(value, bytes):
        return value.decode('utf-8', errors='replace')
    return None
def _sql_segment_of(part: ast.AST, resolve) -> tuple[str, bool]:
    if isinstance(part, ast.Constant):
        text = _constant_sql_text(part.value)
        if text is not None:
            return text, True
    if isinstance(part, ast.Name):
        bound = resolve(part.id) if resolve is not None else None
        if bound is not None:
            return bound, True
    return '?', False
def _fold_sql_expr(node: ast.AST, resolve=None) -> str | None:
    parts: list[str] = []
    stack: list[ast.AST] = [node]
    static_seen = False
    while stack:
        part = stack.pop()
        if isinstance(part, ast.BinOp) and isinstance(part.op, ast.Add):
            stack.append(part.right)
            stack.append(part.left)
            continue
        if isinstance(part, ast.JoinedStr):
            stack.extend(reversed(part.values))
            continue
        if isinstance(part, ast.FormattedValue):
            stack.append(part.value)
            continue
        seg, is_static = _sql_segment_of(part, resolve)
        parts.append(seg)
        static_seen = static_seen or is_static
    return ''.join(parts) if static_seen else None
def _text_wrapper_arg(node: ast.AST) -> ast.expr | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    name = (func.id if isinstance(func, ast.Name)
            else func.attr if isinstance(func, ast.Attribute) else None)
    if name not in _ORM_TEXT_FUNCS:
        return None
    if node.args:
        return node.args[0]
    return next(
        (kw.value for kw in node.keywords
         if kw.arg in ('text', 'sql', 'statement')),
        None)
def _extract_orm_exec_sql(first_arg, sql_texts: list, resolve=None) -> None:
    if isinstance(first_arg, ast.Call):
        wrapped = _text_wrapper_arg(first_arg)
        if wrapped is None:
            return
        first_arg = wrapped
    folded = _fold_sql_expr(first_arg, resolve)
    if folded is not None:
        sql_texts.append(folded)
def _register_docstring_identity(node: ast.AST, doc_ids: set[int]) -> None:
    if node.body and is_docstring_stmt(node.body[0]):
        doc_ids.add(id(node.body[0].value))
_SQL_SHAPE_RE = re.compile(
    rf'(?:\b(?:INSERT\s+(?:OR\s+\w+\s+)?|REPLACE\s+)INTO\s+'
    rf'(?:{_SQL_IDENTIFIER}\.)*{_SQL_IDENTIFIER}\s*(?:\(|VALUES\b)'
    rf'|\bCREATE\s+(?:TEMP(?:ORARY)?\s+)?(?:VIRTUAL\s+)?TABLE\s+'
    rf'(?:IF\s+NOT\s+EXISTS\s+)?(?:{_SQL_IDENTIFIER}\.)*{_SQL_IDENTIFIER}\s*\('
    r'|\bSELECT\b[^;]*\bFROM\s+[^\s(]'
    r'|\bDELETE\s+FROM\s+[^\s(]'
    r'|\bUPDATE\s+(?:OR\s+\w+\s+)?[^\s(]+\s+SET\b'
    r'|\bDROP\s+TABLE\s+[^\s(]+'
    r'|\bALTER\s+TABLE\s+[^\s(]+'
    r'|\bJOIN\s+[^\s(]+)',
    re.IGNORECASE)
def _append_sql_candidate(text: str | None, sql_texts: list[str]) -> None:
    if text is None:
        return
    if len(text) > 20 or _SQL_SHAPE_RE.search(text):
        sql_texts.append(text)
def _collect_node_sql_strings(node: ast.AST, doc_ids: set[int],
                             sql_texts: list[str]) -> None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        _register_docstring_identity(node, doc_ids)
        return
    if isinstance(node, ast.Constant):
        text = _constant_sql_text(node.value)
        if text is not None and id(node) not in doc_ids:
            _append_sql_candidate(text, sql_texts)
        return
    if isinstance(node, ast.JoinedStr):
        _append_sql_candidate(_fold_sql_expr(node), sql_texts)
        return
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        _append_sql_candidate(_fold_sql_expr(node), sql_texts)
def _collect_sql_text_candidates(stmts: list[ast.stmt],
                                sql_texts: list[str]) -> None:
    doc_ids: set[int] = set()
    for idx, stmt in enumerate(stmts):
        if idx == 0 and is_docstring_stmt(stmt):
            continue
        stack: list[ast.AST] = [stmt]
        while stack:
            node = stack.pop()
            if (isinstance(node, ast.Expr)
                    and id(node.value) not in doc_ids
                    and _fold_sql_expr(node.value) is not None):
                continue
            _collect_node_sql_strings(node, doc_ids, sql_texts)
            stack.extend(ast.iter_child_nodes(node))
def _docstring_spans(tree: ast.AST) -> list[tuple[int, int, int, int]]:
    spans: list[tuple[int, int, int, int]] = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Module, ast.FunctionDef,
                                 ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        body = getattr(node, "body", ())
        if not body or not is_docstring_stmt(body[0]):
            continue
        stmt = body[0]
        end_lineno = getattr(stmt, "end_lineno", None) or stmt.lineno
        end_col = getattr(stmt, "end_col_offset", None)
        spans.append((stmt.lineno, stmt.col_offset, end_lineno,
                      stmt.col_offset if end_col is None else end_col))
    return spans
def _byte_col_to_char(line: str, byte_col: int) -> int:
    if byte_col <= 0:
        return 0
    raw = line.encode("utf-8")
    if byte_col >= len(raw):
        return len(line)
    return len(raw[:byte_col].decode("utf-8", errors="ignore"))
def _blank_span(lines: list[str], start_line: int, start_col: int,
                end_line: int, end_col: int) -> None:
    for lineno in range(max(start_line, 1), min(end_line, len(lines)) + 1):
        line = lines[lineno - 1]
        content_end = len(line.rstrip("\r\n"))
        begin = start_col if lineno == start_line else 0
        stop = end_col if lineno == end_line else content_end
        begin = min(max(begin, 0), content_end)
        stop = min(max(stop, 0), content_end)
        if stop > begin:
            lines[lineno - 1] = (
                line[:begin] + " " * (stop - begin) + line[stop:])
def _comment_spans_lexical_fallback(code: str) -> dict[int, list[tuple[int, int]]]:
    spans: dict[int, list[tuple[int, int]]] = {}
    quote = ""
    for row, line in enumerate(code.splitlines(), 1):
        comment_col, quote = scan_line_quote_state(line, quote)
        if comment_col >= 0:
            spans.setdefault(row, []).append((comment_col, len(line)))
    return spans
def _mask_non_code_text(code: str, filename: str) -> str:
    if not code:
        return code
    lines = code.splitlines(keepends=True)
    spans: list[tuple[int, int, int, int]] = []
    try:
        tree = parse_cached(code, filename=filename)
    except PARSE_DEGRADE_EXC as exc:
        log_swallowed(
            __name__, exc,
            context=f"_mask_non_code_text:{type(exc).__name__}")
    else:
        spans.extend(
            (start_line,
             _byte_col_to_char(lines[start_line - 1], start_col)
             if 1 <= start_line <= len(lines) else 0,
             end_line,
             _byte_col_to_char(lines[end_line - 1], end_col)
             if 1 <= end_line <= len(lines) else 0)
            for start_line, start_col, end_line, end_col
            in _docstring_spans(tree))
    comment_spans = comment_only_spans(code)
    if comment_spans is None:
        comment_spans = _comment_spans_lexical_fallback(code)
    for row, row_spans in comment_spans.items():
        spans.extend((row, start, row, end) for start, end in row_spans)
    for start_line, start_col, end_line, end_col in spans:
        if start_line <= end_line:
            _blank_span(lines, start_line, start_col, end_line, end_col)
    return "".join(lines)
def _is_standalone_string_token(
    tokens: list[tokenize.TokenInfo], index: int,
) -> bool:
    left = index - 1
    while left >= 0 and (
            tokens[left].type == tokenize.STRING or tokens[left].string == '('):
        left -= 1
    if left >= 0 and not (
            tokens[left].type in (tokenize.NEWLINE, tokenize.INDENT,
                                  tokenize.DEDENT)
            or tokens[left].string == ';'):
        return False
    right = index + 1
    while right < len(tokens) and (
            tokens[right].type == tokenize.STRING or tokens[right].string == ')'):
        right += 1
    return right >= len(tokens) or (
        tokens[right].type in (tokenize.NEWLINE, tokenize.DEDENT,
                               tokenize.ENDMARKER)
        or tokens[right].string == ';')
def _literal_sql_candidates(code: str) -> list[str]:
    token_list: list[tokenize.TokenInfo] = []
    tokens = tokenize.generate_tokens(io.StringIO(code).readline)
    while True:
        try:
            token = next(tokens)
        except StopIteration:
            break
        except (tokenize.TokenError, IndentationError, SyntaxError,
                ValueError) as exc:
            log_swallowed(
                __name__, exc,
                context=f'_literal_sql_candidates:{type(exc).__name__}')
            break
        token_list.append(token)
    significant = [token for token in token_list
                   if token.type not in (tokenize.NL, tokenize.COMMENT)]
    texts: list[str] = []
    index = 0
    while index < len(significant):
        token = significant[index]
        if token.type != tokenize.STRING:
            index += 1
            continue
        end = index + 1
        while end < len(significant) and significant[end].type == tokenize.STRING:
            end += 1
        if _is_standalone_string_token(significant, index):
            index = end
            continue
        text = _string_literal_text(
            " ".join(part.string for part in significant[index:end]))
        if text:
            texts.append(text)
        index = end
    return texts
def _string_literal_text(raw: str) -> str | None:
    try:
        value = ast.literal_eval(raw)
    except (SyntaxError, ValueError):
        return None
    return _constant_sql_text(value)
def _sql_texts_for_column_scan(
    code: str, filename: str, texts_cache: dict[str, list[str]],
) -> list[str]:
    cached = texts_cache.get(filename)
    if cached is not None:
        return cached
    try:
        candidates = _extract_sql_text_candidates(code, filename)
    except PARSE_DEGRADE_EXC:
        candidates = (_literal_sql_candidates(code)
                      or [_mask_non_code_text(code, filename)])
    texts = [text for text in candidates if _SQL_SHAPE_RE.search(text)]
    texts_cache[filename] = texts
    return texts
def _add_table_name(result: dict[str, set[str]], key: str, name: str) -> None:
    if not is_excluded_table(name):
        result[key].add(name)
def _scan_sql_text(text: str, result: dict[str, set[str]]) -> None:
    for match in _RE_INSERT.finditer(text):
        if not _is_sql_table_reference(text, match.start()):
            continue
        name = _table_name_of(match)
        if name:
            _add_table_name(result, 'insert', name)
    for match in _RE_CREATE_TABLE.finditer(text):
        if not _is_sql_table_reference(text, match.start()):
            continue
        name = _table_name_of(match)
        if name:
            _add_table_name(result, 'create', name)
    result['rw'] |= _rw_table_names(text)
def _extract_sql_text_candidates(source_code: str,
                                  filename: str) -> list[str]:
    tree = parse_cached(source_code, filename=filename)
    sql_texts: list[str] = []
    _collect_sql_text_candidates(tree.body, sql_texts)
    _scan_scopes_for_execute_sql(tree, sql_texts)
    return list(dict.fromkeys(sql_texts))
def extract_code_sql_tables(
        source_code: str,
        filename: str = DEFAULT_VIRTUAL_FILENAME,
) -> dict[str, set[str]]:
    result: dict[str, set[str]] = {'insert': set(), 'create': set(), 'rw': set()}
    try:
        sql_texts = _extract_sql_text_candidates(source_code, filename)
    except PARSE_DEGRADE_EXC:
        _log.warning("AST解析失败，回退到词法字符串抽取", exc_info=True)
        if isinstance(source_code, str):
            texts = (_literal_sql_candidates(source_code)
                     or [_mask_non_code_text(source_code, filename)])
            for text in texts:
                _scan_sql_text(text, result)
        return result
    for text in sql_texts:
        _scan_sql_text(text, result)
    return result
_DELETED_BINDING = object()
def _resolve_binding(name: str, pos, chain) -> str | None:
    for _, _, scope_info in chain:
        if scope_info is not None and len(scope_info) > 4:
            pos = scope_info[4]
            break
    for events, is_class, info in chain:
        if info is not None and name in info[1]:
            return _resolve_binding(name, pos, chain[-1:])
        if info is not None and name not in info[0]:
            continue
        value = None
        found = False
        best_pos = None
        for ev_pos, ev_val in events.get(name, ()):
            if ev_pos >= pos:
                continue
            if best_pos is None or ev_pos > best_pos:
                best_pos = ev_pos
                value = ev_val
                found = True
        if found and is_class and value is _DELETED_BINDING:
            continue
        if found or not is_class:
            return value
    return None
def _record_binding(events: dict, name: str, pos, value) -> None:
    events.setdefault(name, []).append((pos, value))
def _end_position(node: ast.AST) -> tuple[int, int]:
    end_col = getattr(node, "end_col_offset", None)
    return (getattr(node, "end_lineno", None) or node.lineno,
            node.col_offset if end_col is None else end_col)
def _bind_assign_target(route, target, pos, value) -> None:
    if isinstance(target, ast.Name):
        _record_binding(route(target.id), target.id, pos, value)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for el in target.elts:
            _bind_assign_target(route, el, pos, None)
    elif isinstance(target, ast.Starred):
        _bind_assign_target(route, target.value, pos, None)
def _bind_delete_target(route, target, pos, class_events) -> None:
    if isinstance(target, ast.Name):
        events = route(target.id)
        value = _DELETED_BINDING if events is class_events else None
        _record_binding(events, target.id, pos, value)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            _bind_delete_target(route, element, pos, class_events)
def _scope_binding_forms(node: ast.AST) -> tuple[set[str], set[str], set[str]]:
    if isinstance(node, ast.Name):
        stored = isinstance(node.ctx, (ast.Store, ast.Del))
        return ({node.id} if stored else set()), set(), set()
    if isinstance(node, ast.Global):
        return set(), set(node.names), set()
    if isinstance(node, ast.Nonlocal):
        return set(), set(), set(node.names)
    names = _bound_names_of(node)
    if names:
        return names, set(), set()
    return set(), set(), set()
def _bound_names_of(node: ast.AST) -> set[str]:
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return set(import_alias_bound_names(node))
    if isinstance(node, (ast.ExceptHandler, *MATCH_CAPTURE_NODES, *MATCH_REST_NODES)):
        name = pattern_capture_name(node)
        return {name} if name else set()
    return set()
def _collect_scope_bindings(body, params=()):
    bound: set[str] = set(params)
    globals_decl: set[str] = set()
    nonlocals_decl: set[str] = set()
    stack: list[ast.AST] = list(body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef)):
            bound.add(node.name)
            stack.extend(node.decorator_list)
            stack.extend(getattr(node, "type_params", ()) or ())
            if isinstance(node, ast.ClassDef):
                stack.extend(node.bases)
                stack.extend(k.value for k in node.keywords)
            else:
                stack.extend(_function_defaults(node.args))
                stack.extend(_function_annotation_expressions(node))
            continue
        if isinstance(node, ast.Lambda):
            stack.extend(_function_defaults(node.args))
            continue
        if isinstance(node, ast.comprehension):
            stack.append(node.iter)
            stack.extend(node.ifs)
            continue
        _b, _g, _n = _scope_binding_forms(node)
        bound |= _b
        globals_decl |= _g
        nonlocals_decl |= _n
        stack.extend(ast.iter_child_nodes(node))
    bound -= globals_decl | nonlocals_decl
    return bound, globals_decl, nonlocals_decl
def _scope_route(chain):
    events_here = chain[0][0]
    info = chain[0][2]
    if info is None:
        return lambda name: events_here
    _, globals_decl, nonlocals_decl = info[:3]
    def route(name):
        if name in globals_decl:
            return chain[-1][0]
        if name in nonlocals_decl:
            fallback = None
            for events, is_class, scope_info in chain[1:]:
                if is_class:
                    continue
                if fallback is None:
                    fallback = events
                if scope_info is not None and name in scope_info[0]:
                    return events
            if fallback is not None:
                return fallback
        return events_here
    return route
def _namedexpr_route(chain, name: str):
    info = chain[0][2]
    is_comprehension = bool(info is not None and len(info) > 3 and info[3])
    if is_comprehension:
        for index, (_, is_class, scope_info) in enumerate(chain[1:], 1):
            if scope_info is not None and len(scope_info) > 3 and scope_info[3]:
                continue
            if not is_class:
                return _scope_route(chain[index:])(name)
    return _scope_route(chain)(name)
def _push_scope_node(node, chain, stack) -> None:
    if isinstance(node, ast.ClassDef):
        _push_class_scope(node, chain, stack)
    elif isinstance(node, ast.Lambda):
        _push_lambda_scope(node, chain, stack)
    elif isinstance(node, (ast.ListComp, ast.SetComp,
                           ast.DictComp, ast.GeneratorExp)):
        _push_comprehension_scope(node, chain, stack)
    else:
        _push_function_scope(node, chain, stack)
def _push_class_scope(node: ast.ClassDef, chain, stack) -> None:
    info = _collect_scope_bindings(node.body)
    child_chain = [({}, True, info)] + [c for c in chain if not c[1]]
    _push_body(node.body, child_chain, stack)
    stack.extend((d, chain) for d in reversed(node.decorator_list))
    stack.extend((b, chain) for b in reversed(node.bases))
    stack.extend((k.value, chain) for k in reversed(node.keywords))
    stack.extend((p, chain) for p in reversed(
        getattr(node, "type_params", ()) or ()))
def _function_annotation_expressions(node) -> list[ast.expr]:
    args = node.args
    params = [*args.posonlyargs, *args.args, *args.kwonlyargs]
    params.extend(p for p in (args.vararg, args.kwarg) if p is not None)
    expressions = [p.annotation for p in params if p.annotation is not None]
    returns = getattr(node, "returns", None)
    if returns is not None:
        expressions.append(returns)
    return expressions
def _push_function_scope(node, chain, stack) -> None:
    info = _collect_scope_bindings(node.body, collect_param_names(node))
    child_chain = [({}, False, info)] + [c for c in chain if not c[1]]
    _push_body(node.body, child_chain, stack)
    stack.extend((d, chain) for d in reversed(node.decorator_list))
    stack.extend((d, chain)
                 for d in reversed(_function_defaults(node.args)))
    stack.extend((a, chain) for a in reversed(
        _function_annotation_expressions(node)))
    stack.extend((p, chain) for p in reversed(
        getattr(node, "type_params", ()) or ()))
def _push_lambda_scope(node: ast.Lambda, chain, stack) -> None:
    info = _collect_scope_bindings([node.body], collect_param_names(node))
    child_chain = [({}, False, info)] + [c for c in chain if not c[1]]
    stack.append((node.body, child_chain))
    stack.extend((d, chain)
                 for d in reversed(_function_defaults(node.args)))
def _target_names(target: ast.AST) -> set[str]:
    if isinstance(target, ast.Name):
        return {target.id}
    if isinstance(target, (ast.Tuple, ast.List)):
        return {name for element in target.elts
                for name in _target_names(element)}
    if isinstance(target, ast.Starred):
        return _target_names(target.value)
    return set()
def _push_comprehension_scope(node: ast.AST, chain, stack) -> None:
    generators = node.generators
    if not generators:
        return
    bound = {name for generator in generators
             for name in _target_names(generator.target)}
    events: dict[str, list] = {}
    child_chain = [(events, False, (bound, set(), set(), True))]
    child_chain.extend(c for c in chain if not c[1])
    evaluation_order = [(generators[0].iter, chain)]
    for index, generator in enumerate(generators):
        for name in _target_names(generator.target):
            _record_binding(events, name, _end_position(generator.iter), None)
        if index:
            evaluation_order.append((generator.iter, child_chain))
        evaluation_order.extend(
            (condition, child_chain) for condition in generator.ifs)
    values = (node.key, node.value) if isinstance(node, ast.DictComp) else (node.elt,)
    element_info = (*child_chain[0][2], _end_position(node))
    element_chain = [(events, False, element_info), *child_chain[1:]]
    evaluation_order.extend((value, element_chain) for value in values)
    stack.extend(reversed(evaluation_order))
def _push_body(body, chain, stack) -> None:
    stack.extend((s, chain) for s in reversed(body))
def _function_defaults(args: ast.arguments) -> list[ast.expr]:
    return [*args.defaults, *(d for d in args.kw_defaults if d is not None)]
def _augassign_folded_value(node: ast.AugAssign, chain, pos) -> str | None:
    cur = _resolve_binding(node.target.id, pos, chain)
    add = _fold_sql_expr(node.value, partial(_resolve_binding, pos=pos, chain=chain))
    return (cur + add) if (cur is not None and add is not None) else None
def _record_assign_binding(node: ast.Assign, route, pos, chain,
                           sql_texts: list[str]) -> None:
    folded = _fold_sql_expr(node.value, partial(_resolve_binding, pos=pos, chain=chain))
    _append_sql_candidate(folded, sql_texts)
    bind_pos = _end_position(node.value)
    for target in node.targets:
        _bind_assign_target(route, target, bind_pos, folded)
def _record_annassign_binding(node: ast.AnnAssign, route, pos, chain,
                              sql_texts: list[str]) -> None:
    if isinstance(node.target, ast.Name) and node.value is not None:
        folded = _fold_sql_expr(
            node.value, partial(_resolve_binding, pos=pos, chain=chain))
        _append_sql_candidate(folded, sql_texts)
        _record_binding(route(node.target.id), node.target.id,
                        _end_position(node.value), folded)
def _record_augassign_binding(node: ast.AugAssign, route, pos, chain,
                              sql_texts: list[str]) -> None:
    if isinstance(node.target, ast.Name):
        folded = _augassign_folded_value(node, chain, pos)
        _append_sql_candidate(folded, sql_texts)
        _record_binding(route(node.target.id), node.target.id,
                        _end_position(node.value), folded)
def _record_scope_binding(node, chain, sql_texts: list[str]) -> None:
    route = _scope_route(chain)
    pos = (node.lineno, node.col_offset)
    if isinstance(node, ast.Assign):
        _record_assign_binding(node, route, pos, chain, sql_texts)
    elif isinstance(node, ast.AnnAssign):
        _record_annassign_binding(node, route, pos, chain, sql_texts)
    elif isinstance(node, ast.AugAssign):
        _record_augassign_binding(node, route, pos, chain, sql_texts)
    elif isinstance(node, (ast.For, ast.AsyncFor)):
        _bind_assign_target(route, node.target, _end_position(node.iter), None)
    elif isinstance(node, (ast.With, ast.AsyncWith)):
        for item in node.items:
            if item.optional_vars is not None:
                _bind_assign_target(
                    route, item.optional_vars,
                    _end_position(item.context_expr), None)
    elif isinstance(node, ast.NamedExpr):
        value = _fold_sql_expr(node.value, partial(_resolve_binding, pos=pos, chain=chain))
        _append_sql_candidate(value, sql_texts)
        _record_binding(_namedexpr_route(chain, node.target.id),
                        node.target.id, _end_position(node.value), value)
    elif isinstance(node, ast.Delete):
        class_events = chain[0][0] if chain[0][1] else None
        for target in node.targets:
            _bind_delete_target(route, target, pos, class_events)
    else:
        for name in _bound_names_of(node):
            _record_binding(route(name), name, pos, None)
def _record_definition_binding(node: ast.AST, chain) -> None:
    name = node.name
    pos = ((node.body[0].lineno, node.body[0].col_offset)
           if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
           else _end_position(node))
    _record_binding(_scope_route(chain)(name), name, pos, None)
def _scan_exec_call(node: ast.Call, chain, sql_texts: list[str]) -> None:
    func = node.func
    if not (isinstance(func, ast.Attribute)
            and func.attr in _ORM_EXEC_METHODS):
        return
    statement = node.args[0] if node.args else next(
        (kw.value for kw in node.keywords
         if kw.arg in _ORM_EXEC_SQL_KWARGS),
        None,
    )
    if statement is None:
        return
    pos = (node.lineno, node.col_offset)
    _extract_orm_exec_sql(
        statement, sql_texts, partial(_resolve_binding, pos=pos, chain=chain))
_BINDING_VALUE_NODES = (
    ast.Assign, ast.AnnAssign, ast.AugAssign,
    ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
    ast.NamedExpr, ast.Delete, ast.Import, ast.ImportFrom, ast.ExceptHandler,
    *MATCH_CAPTURE_NODES, *MATCH_REST_NODES,
)
def _scan_scope_node(node: ast.AST, chain, stack: list,
                     sql_texts: list[str]) -> bool:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda, ast.ListComp,
                         ast.SetComp, ast.DictComp, ast.GeneratorExp)):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            _record_definition_binding(node, chain)
        _push_scope_node(node, chain, stack)
        return True
    if isinstance(node, _BINDING_VALUE_NODES):
        _record_scope_binding(node, chain, sql_texts)
    if isinstance(node, ast.Call):
        _scan_exec_call(node, chain, sql_texts)
    return False
def _scan_scopes_for_execute_sql(tree: ast.Module, sql_texts: list[str]) -> None:
    module_events: dict[str, list] = {}
    stack: list[tuple[ast.AST, list]] = [
        (stmt, [(module_events, False, None)]) for stmt in reversed(tree.body)]
    while stack:
        node, chain = stack.pop()
        if _scan_scope_node(node, chain, stack, sql_texts):
            continue
        stack.extend((child, chain)
                     for child in reversed(list(ast.iter_child_nodes(node))))
_BROAD_ERRORS = (OSError, AttributeError, KeyError, TypeError, ValueError,
                 RuntimeError)
_DB_ERRORS = (*_BROAD_ERRORS, sqlite3.Error)
def _db_file_ready(db_path: object) -> bool:
    return bool(db_path) and os.path.isfile(db_path)
def _try_get_db_tables(db_path: str) -> set[str] | None:
    if not _db_file_ready(db_path):
        return None
    try:
        tables = {row[0] for row in _query_ro_db(
            db_path,
            "SELECT name FROM sqlite_master "
            "WHERE type IN ('table', 'view')")}
        return {t for t in tables if not is_excluded_table(t)}
    except _DB_ERRORS as e:
        _log.warning("数据库不可达 %s: %s",
                     db_path, str(e)[:_ERROR_TEXT_LIMIT])
        return None
def _query_ro_db(db_path: str, sql: str) -> list[tuple]:
    uri = Path(db_path).resolve().as_uri() + "?mode=ro"
    conn = sqlite3.connect(uri, uri=True, timeout=_SQLITE_TIMEOUT_S)
    try:
        cur = conn.cursor()
        cur.execute(sql)
        return cur.fetchall()
    finally:
        conn.close()
def _try_get_table_columns(db_path: str, table_name: str) -> set[str] | None:
    if not _db_file_ready(db_path):
        return None
    try:
        escaped_name = table_name.replace(chr(39), chr(39) * 2)
        rows = _query_ro_db(
            db_path, f"PRAGMA table_xinfo('{escaped_name}')")
        if not rows:
            rows = _query_ro_db(
                db_path, f"PRAGMA table_info('{escaped_name}')")
        return {row[1] for row in rows}
    except _DB_ERRORS as e:
        _log.warning("表列查询失败 %s.%s: %s",
                     db_path, table_name, str(e)[:_ERROR_TEXT_LIMIT])
        return None
_FENCE_RE = re.compile(r'^(?P<marker>`{3,}|~{3,})(?P<info>.*)$')
_HEADING_RE = re.compile(r'^#{1,6}\s+(.+?)\s*$')
_BOLD_LINE_RE = re.compile(r'^\*\*(.+?)\*\*\s*$')
# 边界用 ASCII 显式环视：`\b` 在 str 模式下按 Unicode 判定，`orders表` 整体是一个词，
# `\b` 会在 `s|表` 之间不成立而漏掉表名。
_TABLE_NAME_IN_HEADING_RE = re.compile(
    r'(?<![A-Za-z0-9_])([A-Za-z_][A-Za-z0-9_]*)(?![A-Za-z0-9_])')
_TABLE_HEADING_PREFIX_WORDS = frozenset({'table', 'tables', 'schema', 'schemas'})
_FIELD_TYPE_RE = re.compile(
    r'[A-Za-z_][A-Za-z0-9_]*(?:\(\s*[0-9]+(?:\s*,\s*[0-9]+)?\s*\))?'
    r'(?:\s+(?:NOT\s+NULL|NULL|PRIMARY\s+KEY|UNIQUE|AUTOINCREMENT|'
    r'DEFAULT\s+\S+|CHECK\s*\(.*\)|COLLATE\s+\w+|'
    r'REFERENCES\s+\w+(?:\s*\([^)]*\))?))*\s*$',
    re.IGNORECASE)
_SEPARATOR_CELL_RE = re.compile(r'^:?-{3,}:?$')
def _is_separator_row(cells: list[str]) -> bool:
    return bool(cells) and all(_SEPARATOR_CELL_RE.fullmatch(c) for c in cells)
def _heading_table_name(line: str) -> tuple[bool, str | None]:
    heading = _HEADING_RE.match(line) or _BOLD_LINE_RE.match(line)
    if not heading:
        return False, None
    names = _TABLE_NAME_IN_HEADING_RE.findall(heading.group(1))
    for name in names:
        if name.lower() not in _TABLE_HEADING_PREFIX_WORDS:
            return True, name.lower()
    return True, None
def _field_row_name_type(cells: list[str]) -> tuple[str, str] | None:
    field_name = cells[0].strip('`')
    type_cell = cells[1].strip('`')
    if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', field_name) \
            or not _FIELD_TYPE_RE.fullmatch(type_cell):
        return None
    return field_name, type_cell
def _read_skill_md_content(skill_md_path: str) -> str | None:
    if not skill_md_path or not os.path.isfile(skill_md_path):
        return None
    try:
        with open(skill_md_path, encoding='utf-8-sig') as f:
            return f.read()
    except (OSError, UnicodeDecodeError) as e:
        _log.warning("SKILL.md 读取失败 %s: %s",
                     skill_md_path, str(e)[:_ERROR_TEXT_LIMIT])
        return None
def _extract_skill_fields(skill_md_path: str) -> dict[str, set[str]]:
    fields: dict[str, set[str]] = {}
    content = _read_skill_md_content(skill_md_path)
    if content is None:
        return fields
    current_table: str | None = None
    in_table = False
    fence: str | None = None
    for raw_line in content.splitlines():
        line = raw_line.strip()
        if fence is not None:
            if len(line) >= len(fence) and set(line) == {fence[0]}:
                fence = None
            continue
        fence_match = _FENCE_RE.fullmatch(line)
        if fence_match is not None:
            marker = fence_match.group('marker')
            info = fence_match.group('info')
            if marker[0] != '`' or '`' not in info:
                fence = marker
                continue
        current_table, in_table = _feed_skill_line(
            line, current_table, in_table, fields)
    return fields
def _feed_skill_line(line: str, current_table: str | None, in_table: bool,
                     fields: dict[str, set[str]]) -> tuple[str | None, bool]:
    cells = _markdown_table_cells(line)
    if not cells:
        is_heading, heading_table = _heading_table_name(line)
        return (heading_table if is_heading else current_table), False
    if _is_separator_row(cells):
        if not in_table and current_table and fields.get(current_table):
            return None, False
        return current_table, True
    if not in_table or len(cells) < 2:
        return current_table, in_table
    pair = _field_row_name_type(cells)
    if pair is not None and current_table:
        fields.setdefault(current_table, set()).add(pair[0])
    return current_table, in_table
def _walk_code_files(root_dir: str) -> list[str]:
    code_files: list[str] = []
    for dirpath, dirs, filenames in os.walk(root_dir):
        dirs[:] = sorted(
            d for d in dirs if not is_pruned_dirname(d, prune_tests=True))
        for fn in sorted(filenames):
            if fn.lower().endswith('.py'):
                code_files.append(os.path.join(dirpath, fn))
    return code_files
def _collect_code_files(filepath: str, root_dir: str) -> list[str]:
    if filepath and os.path.isfile(filepath):
        return [filepath]
    scan_root = root_dir or (filepath if os.path.isdir(filepath) else "")
    if scan_root and os.path.isdir(scan_root):
        return _walk_code_files(scan_root)
    return []
def _extract_all_sql_refs(
    code_files: list[str],
    code_cache: dict[str, str | None],
) -> tuple[set[str], set[str], dict[str, dict[str, set[str]]]]:
    all_insert_tables: set[str] = set()
    all_create_tables: set[str] = set()
    file_sql_map: dict[str, dict[str, set[str]]] = {}
    for fp in code_files:
        try:
            code = _read_code_cached(fp, code_cache)
            if code is None:
                continue
            tables = extract_code_sql_tables(code, filename=fp)
            all_insert_tables.update(tables.get('insert', set()))
            all_create_tables.update(tables.get('create', set()))
            file_sql_map[fp] = tables
        except _BROAD_ERRORS:
            _log.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
            continue
    return all_insert_tables, all_create_tables, file_sql_map
def _collect_db_paths(
    db_path: object, db_paths: object,
) -> tuple[list[str], list[str]]:
    candidates = _db_path_candidates(db_paths)
    candidates.extend(_db_path_candidates(db_path))
    usable: list[str] = []
    unusable: list[str] = []
    for path in candidates:
        (usable if os.path.isfile(path) else unusable).append(path)
    return list(dict.fromkeys(usable)), list(dict.fromkeys(unusable))
def _path_text(value: object) -> str | None:
    if isinstance(value, (bytes, bytearray)):
        return os.fsdecode(bytes(value)) or None
    if not isinstance(value, (str, os.PathLike)):
        return None
    try:
        path = os.fspath(value)
    except TypeError:
        return None
    return path if isinstance(path, str) and path else None
def _db_path_candidates(db_paths) -> list[str]:
    unordered = isinstance(db_paths, (set, frozenset))
    if isinstance(db_paths, (str, bytes, bytearray, os.PathLike)):
        candidates = [db_paths]
    elif isinstance(db_paths, Iterable) and not isinstance(
            db_paths, (bytes, bytearray, dict)):
        candidates = list(db_paths)
    else:
        return []
    paths = [p for p in map(_path_text, candidates) if p is not None]
    return sorted(paths) if unordered else paths
def _query_db_tables(
    paths: list[str],
) -> tuple[dict[str, set[str]], int]:
    db_table_map: dict[str, set[str]] = {}
    unreachable = 0
    for dbp in paths:
        tables = _try_get_db_tables(dbp)
        if tables is None:
            unreachable += 1
            continue
        for t in tables:
            db_table_map.setdefault(t, set()).add(dbp)
    return db_table_map, unreachable
def _finding(pattern: str, message: str, severity: str, filepath: str,
             suggestion: str) -> dict[str, Any]:
    return {
        "check_id": _CHECK_ID,
        "pattern": pattern,
        "lineno": 0,
        "col": 0,
        "message": message,
        "severity": severity,
        "filepath": filepath,
        "suggestion": suggestion,
    }
def _insert_source_files_by_key(
    file_sql_map: dict[str, dict[str, set[str]]],
) -> dict[str, list[str]]:
    sources: dict[str, list[str]] = {}
    for filepath, table_map in file_sql_map.items():
        keys = {_sql_name_key(table)
                for table in table_map.get('insert', set())}
        for key in keys:
            sources.setdefault(key, []).append(filepath)
    return {key: sorted(paths) for key, paths in sources.items()}
def _check_insert_targets(
    all_insert_tables: set[str],
    all_create_tables: set[str],
    db_table_map: dict[str, set[str]],
    file_sql_map: dict[str, dict[str, set[str]]],
    db_unreachable: bool,
    db_incomplete: bool,
    root_dir: str,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    if db_unreachable:
        return findings
    create_keys = {_sql_name_key(t) for t in all_create_tables}
    db_keys = {_sql_name_key(t) for t in db_table_map}
    seen: set[str] = set()
    source_files_by_key: dict[str, list[str]] | None = None
    for table in sorted(all_insert_tables):
        key = _sql_name_key(table)
        if key in seen:
            continue
        seen.add(key)
        if key in create_keys or is_excluded_table(table):
            continue
        if key not in db_keys:
            if db_incomplete:
                continue
            if source_files_by_key is None:
                source_files_by_key = _insert_source_files_by_key(file_sql_map)
            source_files = source_files_by_key.get(key, [])
            findings.append(_finding(
                "INSERT目标表不存在",
                f"INSERT INTO '{table}' — 表在数据库中不存在且代码未建表",
                "ERROR",
                source_files[0] if source_files else (root_dir or ""),
                f"创建表 '{table}' 或添加 CREATE TABLE IF NOT EXISTS 语句",
            ))
    return findings
def _check_orphan_tables(
    db_table_map: dict[str, set[str]],
    all_insert_tables: set[str],
    all_create_tables: set[str],
    db_unreachable: bool,
    root_dir: str,
    all_rw_tables: set[str] | None = None,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    if db_unreachable:
        return findings
    all_code_tables = all_insert_tables | all_create_tables | (all_rw_tables or set())
    code_keys = {_sql_name_key(t) for t in all_code_tables}
    for table in sorted(db_table_map):
        if is_excluded_table(table):
            continue
        if _sql_name_key(table) not in code_keys:
            findings.append(_finding(
                "孤立表(无代码操作)",
                f"表 '{table}' 在数据库中存在但代码中从未引用"
                f"(INSERT/CREATE/SELECT/UPDATE/DELETE/JOIN)",
                "INFO",
                root_dir or "",
                f"确认 '{table}' 是否仍在使用，或标记为废弃",
            ))
    return findings
def _clean_column_name(raw: str) -> str:
    col = raw.strip()
    if len(col) < 2:
        return col
    if col[0] == '[' and col[-1] == ']':
        return col[1:-1].strip()
    if col[0] in ('"', "'", '`') and col[-1] == col[0]:
        quote = col[0]
        return col[1:-1].replace(quote * 2, quote)
    return col
_COLUMN_IDENTIFIER_RE = re.compile(
    rf"(?:{_SQL_UNQUOTED_IDENTIFIER}"
    r"|\"(?:[^\"]|\"\")*\"|'(?:[^']|'')*'"
    r"|`(?:[^`]|``)*`|\[[^\]]+\])"
)
def _static_insert_columns(match: re.Match) -> set[str] | None:
    raw_columns = [c.strip() for c in match.group(1).split(',')]
    if not raw_columns or not all(
            _COLUMN_IDENTIFIER_RE.fullmatch(c) for c in raw_columns):
        return None
    return {_clean_column_name(c) for c in raw_columns}
def _table_ref_fragment(table: str) -> str:
    forms = [re.escape(table)] if re.fullmatch(r"\w+", table) else []
    forms.extend((
        rf'"{re.escape(table.replace(chr(34), chr(34) * 2))}"',
        rf"'{re.escape(table.replace(chr(39), chr(39) * 2))}'",
        rf'`{re.escape(table.replace(chr(96), chr(96) * 2))}`',
        rf'\[{re.escape(table)}\]',
    ))
    return '(?:' + '|'.join(forms) + ')'
def _insert_columns_pattern(table: str) -> re.Pattern[str]:
    return re.compile(
        rf'\b(?:INSERT\s+(?:OR\s+\w+\s+)?|REPLACE\s+)INTO\s+'
        rf'(?:(?:{_SQL_IDENTIFIER})\.)*'
        rf'{_table_ref_fragment(table)}\s*\(([^)]+)\)',
        re.IGNORECASE | re.DOTALL
    )
def _read_code_cached(
    fp: str, code_cache: dict[str, str | None],
) -> str | None:
    if fp in code_cache:
        return code_cache[fp]
    try:
        code = read_source(fp)
    except _BROAD_ERRORS:
        _log.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
        code = None
    code_cache[fp] = code
    return code
def _match_insert_columns(table: str, insert_pattern: re.Pattern,
                          db_columns: set[str], fp: str,
                          code: str, findings: list[dict[str, Any]],
                          seen: set[tuple[str, str, frozenset[str]]]) -> None:
    try:
        db_keys = {_sql_name_key(c) for c in db_columns}
        table_key = _sql_name_key(table)
        for match in insert_pattern.finditer(code):
            if not _is_sql_statement_start(code, match.start()):
                continue
            sql_columns = _static_insert_columns(match)
            if sql_columns is None:
                continue
            unknown_cols = {c for c in sql_columns
                            if _sql_name_key(c) not in db_keys}
            if not unknown_cols:
                continue
            signature = (fp, table_key,
                         frozenset(_sql_name_key(c) for c in unknown_cols))
            if signature in seen:
                continue
            seen.add(signature)
            findings.append(_finding(
                "INSERT列名不匹配",
                f"表 '{table}' INSERT 使用了未知列: "
                f"{', '.join(sorted(unknown_cols)[:_NAME_PREVIEW_LIMIT])}",
                "WARNING",
                fp,
                "检查列名拼写或更新表结构",
            ))
    except _BROAD_ERRORS:
        _log.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
def _db_columns_for_table(
    dbp: str, table: str, db_table_map: dict[str, set[str]],
) -> tuple[str, set[str]] | None:
    key = _sql_name_key(table)
    for db_table, paths in db_table_map.items():
        if _sql_name_key(db_table) != key or dbp not in paths:
            continue
        columns = _try_get_table_columns(dbp, db_table)
        if not isinstance(columns, set) or not columns:
            return None
        return db_table, columns
    return None
def _unique_schema_views(
    all_db_paths: list[str], all_insert_tables: set[str],
    db_table_map: dict[str, set[str]],
) -> list[tuple[str, set[str]]]:
    seen: set[tuple[str, frozenset[str]]] = set()
    views: list[tuple[str, set[str]]] = []
    for dbp in all_db_paths:
        for table in sorted(all_insert_tables):
            hit = _db_columns_for_table(dbp, table, db_table_map)
            if hit is None:
                continue
            db_table, db_columns = hit
            signature = (_sql_name_key(db_table),
                         frozenset(_sql_name_key(c) for c in db_columns))
            if signature in seen:
                continue
            seen.add(signature)
            views.append((db_table, db_columns))
    return views
def _check_insert_columns(
    all_insert_tables: set[str],
    db_table_map: dict[str, set[str]],
    all_db_paths: list[str],
    code_files: list[str],
    file_sql_map: dict[str, dict[str, set[str]]],
    db_unreachable: bool,
    db_incomplete: bool,
    code_cache: dict[str, str | None],
    texts_cache: dict[str, list[str]],
) -> list[dict[str, Any]]:
    if db_unreachable or db_incomplete:
        return []
    patterns = {_sql_name_key(t): _insert_columns_pattern(t)
                for t in all_insert_tables}
    findings: list[dict[str, Any]] = []
    seen: set[tuple[str, str, frozenset[str]]] = set()
    for table, db_columns in _unique_schema_views(
            all_db_paths, all_insert_tables, db_table_map):
        findings.extend(_insert_column_findings(
            table, patterns[_sql_name_key(table)], db_columns,
            code_files, file_sql_map, code_cache, texts_cache, seen))
    return findings
def _insert_column_findings(
    table: str, insert_pattern: re.Pattern, db_columns: set[str],
    code_files: list[str], file_sql_map: dict[str, dict[str, set[str]]],
    code_cache: dict[str, str | None],
    texts_cache: dict[str, list[str]],
    seen: set[tuple[str, str, frozenset[str]]],
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    key = _sql_name_key(table)
    for fp in code_files:
        inserts = file_sql_map.get(fp, {}).get('insert', set())
        if not any(_sql_name_key(t) == key for t in inserts):
            continue
        code = _read_code_cached(fp, code_cache)
        if code is None:
            continue
        try:
            sql_texts = _sql_texts_for_column_scan(code, fp, texts_cache)
        except _BROAD_ERRORS:
            _log.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
            continue
        for sql_text in sql_texts:
            _match_insert_columns(
                table, insert_pattern, db_columns, fp, sql_text, findings,
                seen)
    return findings
_RE_SELECT_START = re.compile(r'\bSELECT\b', re.IGNORECASE)
_RE_SELECT_TABLE = re.compile(
    r'\bSELECT\s+(?:(?:DISTINCT|ALL)\s+)?(?P<columns>[^;()]*?)\s+FROM\s+'
    rf'(?P<table>(?:{_SQL_IDENTIFIER}\.)*{_SQL_IDENTIFIER})'
    r'(?P<tail>[^;]*)',
    re.IGNORECASE | re.DOTALL,
)
_SELECT_IDENTIFIER = (
    rf'(?:{_SQL_UNQUOTED_IDENTIFIER}'
    r'|"(?:[^"]|"")*"|`(?:[^`]|``)*`|\[[^\]]+\])'
)
_RE_SELECT_ITEM = re.compile(
    rf'(?P<qualifiers>(?:{_SELECT_IDENTIFIER}\s*\.\s*)*)'
    rf'(?P<column>{_SELECT_IDENTIFIER})'
    rf'(?:\s+(?:AS\s+)?{_SELECT_IDENTIFIER})?',
    re.IGNORECASE,
)
_RE_SELECT_FROM_STOP = re.compile(
    r'\b(?:WHERE|GROUP\s+BY|ORDER\s+BY|HAVING|LIMIT|UNION|EXCEPT|'
    r'INTERSECT|WINDOW)\b',
    re.IGNORECASE,
)
_RE_SELECT_MULTI_TABLE = re.compile(r'\bJOIN\b|,', re.IGNORECASE)
_SQL_LITERAL_COLUMNS = frozenset({
    'null', 'true', 'false', 'current_date', 'current_time',
    'current_timestamp',
})
def _unquote_table_ref(text: str) -> str:
    identifiers = list(re.finditer(_SQL_IDENTIFIER, text))
    return _clean_column_name(identifiers[-1].group(0)) if identifiers else ""
def _select_column_refs(sql_text: str) -> list[tuple[str, set[str]]]:
    refs: list[tuple[str, set[str]]] = []
    cte_cache: dict[tuple[int, int], _CteDefinitionScopes] = {}
    for start in (m.start() for m in _RE_SELECT_START.finditer(sql_text)):
        if not _is_sql_select_start(sql_text, start):
            continue
        match = _RE_SELECT_TABLE.match(sql_text, start)
        if match is None:
            continue
        columns_text = match.group('columns').strip()
        if not columns_text or '*' in columns_text:
            continue
        tail = match.group('tail')
        stop = _RE_SELECT_FROM_STOP.search(tail)
        from_clause = tail[:stop.start()] if stop else tail
        if _RE_SELECT_MULTI_TABLE.search(from_clause):
            continue
        table = _unquote_table_ref(match.group('table'))
        cte_keys = _statement_cte_keys(sql_text, start, cte_cache)
        if (not table or is_excluded_table(table)
                or _sql_name_key(table) in cte_keys):
            continue
        columns: set[str] = set()
        for item in columns_text.split(','):
            parsed = _RE_SELECT_ITEM.fullmatch(item.strip())
            if parsed is None:
                columns.clear()
                break
            raw_column = parsed.group('column')
            if (not parsed.group('qualifiers')
                    and re.fullmatch(_SQL_UNQUOTED_IDENTIFIER, raw_column)
                    and raw_column.lower() in _SQL_LITERAL_COLUMNS):
                continue
            columns.add(_clean_column_name(raw_column))
        if columns:
            refs.append((table, columns))
    return refs
def _check_select_columns(
    db_table_map: dict[str, set[str]],
    all_db_paths: list[str],
    code_files: list[str],
    code_cache: dict[str, str | None],
    texts_cache: dict[str, list[str]],
    db_unreachable: bool,
    db_incomplete: bool,
) -> list[dict[str, Any]]:
    if db_unreachable or db_incomplete:
        return []
    findings: list[dict[str, Any]] = []
    seen: set[tuple[str, str, frozenset[str]]] = set()
    for fp in code_files:
        code = _read_code_cached(fp, code_cache)
        if code is None:
            continue
        try:
            sql_texts = _sql_texts_for_column_scan(code, fp, texts_cache)
        except _BROAD_ERRORS:
            _log.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
            continue
        for sql_text in sql_texts:
            for table, columns in _select_column_refs(sql_text):
                for dbp in all_db_paths:
                    hit = _db_columns_for_table(dbp, table, db_table_map)
                    if hit is None:
                        continue
                    db_table, db_columns = hit
                    db_keys = {_sql_name_key(c) for c in db_columns}
                    unknown = frozenset(
                        c for c in columns
                        if _sql_name_key(c) not in db_keys)
                    signature = (fp, _sql_name_key(db_table), unknown)
                    if signature in seen:
                        continue
                    seen.add(signature)
                    if unknown:
                        findings.append(_finding(
                            "SELECT列名不匹配",
                            f"表 '{db_table}' SELECT 使用了未知列: "
                            f"{', '.join(sorted(unknown)[:_NAME_PREVIEW_LIMIT])}",
                            "WARNING",
                            fp,
                            "检查列名拼写或更新表结构",
                        ))
    return findings
def _skill_field_findings_for_file(
    fp: str,
    skill_fields: dict[str, set[str]],
    code: str,
    patterns: dict[str, re.Pattern],
    seen: set[tuple[str, str, frozenset[str]]],
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for table, expected_fields in skill_fields.items():
        insert_pattern = patterns[table]
        table_key = _sql_name_key(table)
        for match in insert_pattern.finditer(code):
            if not _is_sql_statement_start(code, match.start()):
                continue
            code_fields = _static_insert_columns(match)
            if code_fields is None:
                continue
            code_keys = {_sql_name_key(c) for c in code_fields}
            missing = {f for f in expected_fields
                       if _sql_name_key(f) not in code_keys}
            if not missing:
                continue
            signature = (fp, table_key,
                         frozenset(_sql_name_key(f) for f in missing))
            if signature in seen:
                continue
            seen.add(signature)
            findings.append(_finding(
                "SKILL.md字段缺失",
                f"表 '{table}' SKILL.md 定义字段 "
                f"{', '.join(sorted(missing)[:_NAME_PREVIEW_LIMIT])}"
                " 未包含在 INSERT 中",
                "WARNING",
                fp,
                "更新 INSERT 以包含 SKILL.md 定义的全部字段",
            ))
    return findings
def _check_skill_md_fields(
    skill_md_path: str | None,
    code_files: list[str],
    code_cache: dict[str, str | None],
    texts_cache: dict[str, list[str]],
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    if not skill_md_path:
        return findings
    skill_fields = _extract_skill_fields(skill_md_path)
    if not skill_fields:
        return findings
    patterns = {t: _insert_columns_pattern(t) for t in skill_fields}
    seen: set[tuple[str, str, frozenset[str]]] = set()
    for fp in code_files:
        try:
            code = _read_code_cached(fp, code_cache)
            if code is None:
                continue
            for sql_text in _sql_texts_for_column_scan(
                    code, fp, texts_cache):
                findings.extend(_skill_field_findings_for_file(
                    fp, skill_fields, sql_text, patterns, seen))
        except _BROAD_ERRORS:
            _log.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
            continue
    return findings
def _normalize_path_args(filepath: Any, root_dir: Any, db_path: Any,
                        skill_md_path: Any
                        ) -> tuple[str, str | None, str | None, str | None]:
    return (
        _path_text(filepath) or "",
        _path_text(root_dir),
        _path_text(db_path),
        _path_text(skill_md_path),
    )
_MEMORY_FILEPATH = "<memory>"
def _memory_source_text(tree: ast.AST | None,
                        source_lines: list | tuple | str | None
                        ) -> str | None:
    if isinstance(source_lines, str):
        return source_lines
    if source_lines is not None:
        try:
            return "\n".join(
                str(line).rstrip("\r\n") for line in source_lines)
        except (TypeError, ValueError) as _e:
            log_swallowed(
                __name__, _e,
                context=f'_memory_source_text:{type(_e).__name__}')
    if tree is None:
        return None
    try:
        return ast.unparse(tree)
    except (AttributeError, TypeError, ValueError, RecursionError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'_memory_source_text:{type(_e).__name__}')
    return None
def detect_table_sql_mismatch(tree: ast.AST | None=None,
                              source_lines: list | tuple | str | None=None,
                              filepath: _PathInput | None = None,
                              db_path: _PathInput | None=None,
                              db_paths: list[_PathInput] | _PathInput | None=None,
                              skill_md_path: _PathInput | None=None,
                              root_dir: _PathInput | None=None,
                              ) -> list[dict[str, Any]]:
    filepath, root_dir, db_path, skill_md_path = _normalize_path_args(
        filepath, root_dir, db_path, skill_md_path)
    code_files = _collect_code_files(filepath, root_dir or "")
    code_cache: dict[str, str | None] = {}
    memory_text = _memory_source_text(tree, source_lines)
    if memory_text is not None:
        memory_fp = filepath or _MEMORY_FILEPATH
        if memory_fp not in code_files:
            code_files.insert(0, memory_fp)
        code_cache[memory_fp] = memory_text
    elif not code_files:
        if filepath or root_dir:
            _log.warning(
                "XT01 无可用源码输入（filepath=%r, root_dir=%r），跳过",
                filepath, root_dir or "")
        return []
    all_insert_tables, all_create_tables, file_sql_map = _extract_all_sql_refs(
        code_files, code_cache)
    texts_cache: dict[str, list[str]] = {}
    all_db_paths, unusable_db_paths = _collect_db_paths(db_path, db_paths)
    if unusable_db_paths:
        _log.warning(
            "XT01 数据库路径不可用（非可读文件，已跳过 %d 个）: %s",
            len(unusable_db_paths),
            ", ".join(unusable_db_paths[:_NAME_PREVIEW_LIMIT]))
    db_table_map, db_unreachable_count = _query_db_tables(all_db_paths)
    db_unreachable = not all_db_paths or (
        db_unreachable_count >= len(all_db_paths))
    db_incomplete = bool(unusable_db_paths) or (
        bool(all_db_paths) and db_unreachable_count > 0)
    findings: list[dict[str, Any]] = []
    findings.extend(_check_insert_targets(
        all_insert_tables, all_create_tables, db_table_map,
        file_sql_map, db_unreachable, db_incomplete, root_dir or "",
    ))
    all_rw_tables = {
        t for table_map in file_sql_map.values()
        for t in table_map.get('rw', set())}
    findings.extend(_check_orphan_tables(
        db_table_map, all_insert_tables, all_create_tables,
        db_unreachable, root_dir or "",
        all_rw_tables=all_rw_tables,
    ))
    findings.extend(_check_insert_columns(
        all_insert_tables, db_table_map, all_db_paths,
        code_files, file_sql_map, db_unreachable, db_incomplete,
        code_cache, texts_cache,
    ))
    findings.extend(_check_select_columns(
        db_table_map, all_db_paths, code_files, code_cache, texts_cache,
        db_unreachable, db_incomplete))
    findings.extend(_check_skill_md_fields(
        skill_md_path, code_files, code_cache, texts_cache))
    return findings
def wiring_declarations() -> dict:
    return {"registry": {_CHECK_ID: detect_table_sql_mismatch}}

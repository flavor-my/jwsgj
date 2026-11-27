from __future__ import annotations  # noqa: I001
import ast
import io
import keyword
import logging
import os
import re
import tokenize
from collections.abc import Callable, Collection
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from jwsgj.diag_shared_ast_nodes import (
    _type_checking_guard_node_polarities,
    is_docstring_stmt,
    iter_own_scope,
    split_identifier,
)
from jwsgj.diag_shared_source_core import (
    parse_py_source,
    utf8_span_to_char_span,
)
from jwsgj.prevention_scope_facts import walk_nodes
_log = logging.getLogger(__name__)
__all__ = [
    'LineSegments',
    'LoggerSourceScan',
    'RenameDecision',
    'build_post_migration_sync_plan',
    'clean_pycache_for_file',
    'decide_rename',
    'detect_logger_lines',
    'rename_with_ast_sync',
    'scan_line_segments',
    'unify_logger',
]
_log.info(
    "refactor_source_rewrite 源码改写域已加载: %d 项导出",
    len(__all__))
def _source_line_break(source: str) -> str:
    return "\r" if "\r" in source and "\n" not in source else "\n"
def _split_source_lines(source: str) -> list[str]:
    if "\n" not in source:
        return source.split(_source_line_break(source))
    return re.sub(r"\r(?!\n)", "\n", source).split("\n")
class _EditSet:
    __slots__ = ("_by_line",)
    def __init__(self) -> None:
        self._by_line: dict[int, list[tuple[int, int, str]]] = {}
    def add(self, row: int, start: int, end: int, text: str) -> None:
        self._by_line.setdefault(row, []).append((start, end, text))
    def __bool__(self) -> bool:
        return bool(self._by_line)
    def apply_to_lines(self, lines: list[str]) -> list[str]:
        new_lines = list(lines)
        for row, edit_list in self._by_line.items():
            text = new_lines[row]
            for col_start, col_end, new_text in sorted(
                    self._dedupe(edit_list), key=lambda e: -e[0]):
                text = text[:col_start] + new_text + text[col_end:]
            new_lines[row] = text
        return new_lines
    def apply_to(self, source: str) -> str:
        line_break = _source_line_break(source)
        return line_break.join(
            self.apply_to_lines(_split_source_lines(source)))
    @staticmethod
    def _dedupe(
        edit_list: list[tuple[int, int, str]],
    ) -> list[tuple[int, int, str]]:
        kept: list[tuple[int, int, str]] = []
        for start, end, new_text in edit_list:
            if any(k_start < end and start < k_end
                   for k_start, k_end, _ in kept):
                continue
            kept.append((start, end, new_text))
        return kept
@dataclass(frozen=True)
class _RenameContext:
    lines: list[str]
    old_name: str
    new_name: str
    edits: _EditSet
    def add_span(self, row: int, start: int, end: int) -> None:
        self.edits.add(row, start, end, self.new_name)
_SIMPLE_ASSIGN_RE = re.compile(r"[A-Za-z_]\w*\s*=(?!=)")
_LEADING_NAME_RE = re.compile(r"[A-Za-z_]\w*")
_UNIFIED_LOGGER_NAME = "logger"
_DEFAULT_LOGGING_ALIASES = frozenset({"logging"})
_DEFAULT_BARE_GETLOGGER_NAMES = frozenset({"getLogger"})
_GETLOGGER_CALL_RE = re.compile(r"\bgetLogger\s*\(")
_LOGGER_USE_METHODS = frozenset({
    "addFilter", "addHandler", "critical", "debug", "error", "exception",
    "fatal", "findCaller", "getChild", "handle", "hasHandlers", "info",
    "isEnabledFor", "log", "makeRecord", "removeFilter", "removeHandler",
    "setLevel", "warn", "warning",
})
_LOGGER_NAME_SEGMENTS = frozenset({"log", "logger", "logs"})
_LOGGER_PREFIX_RE = re.compile(r"^log(?:ger|s)?(?:\d|_|$)")
def _logger_name_like(name: str) -> bool:
    core = name.lower().lstrip("_")
    if core == "logging":
        return False
    if _LOGGER_PREFIX_RE.match(core):
        return True
    return bool(set(split_identifier(name)) & _LOGGER_NAME_SEGMENTS)
def _leading_identifier(line: str) -> str | None:
    match = _LEADING_NAME_RE.match(line.lstrip())
    return match.group(0) if match is not None else None
_CONTINUATION_SUFFIXES = ("\\", "(", "[", "{", ",")
def _iter_code_spans(ln: str, start_col: int = 0):
    for start, end, is_code in scan_line_segments(ln).spans:
        if end <= start_col:
            continue
        yield max(start, start_col), end, is_code
def _has_inline_separators(ln: str) -> bool:
    segments = scan_line_segments(ln)
    if segments.unterminated_triple or segments.comment_start is not None:
        return True
    return any(";" in ln[start:end]
               for start, end, is_code in segments.spans if is_code)
_WALRUS_OP_RE = re.compile(r":=")
_ASSIGN_OP_RE = re.compile(r"(?<![=!<>+\-*/%&|^:])=(?!=)")
def _map_segments(
    ln: str,
    code: Callable[[str], str],
    other: Callable[[str], str],
) -> str:
    return "".join(
        (code if is_code else other)(ln[start:end])
        for start, end, is_code in scan_line_segments(ln).spans)
def _blank_string_literals(ln: str) -> str:
    return _map_segments(ln, lambda seg: seg, lambda seg: " " * len(seg))
def _count_line_binding_ops(ln: str) -> int:
    text = _blank_string_literals(ln)
    return len(_WALRUS_OP_RE.findall(text)) + len(_ASSIGN_OP_RE.findall(text))
def _has_bare_name_use(
    lines: list[str],
    interior: set[int],
    own_def_line_nos: set[int],
    name: str,
) -> bool:
    pat = re.compile(rf"(?<![\w.]){re.escape(name)}\b(?!\s*\.)")
    for i, line in enumerate(lines):
        if i in interior or i in own_def_line_nos:
            continue
        if pat.search(line):
            return True
    return False
def _replace_attr_refs_outside_strings(ln: str, name: str) -> str:
    pat = re.compile(rf"(?<![\w.]){re.escape(name)}\.")
    return _map_segments(ln, lambda seg: pat.sub("logger.", seg), lambda seg: seg)
def _definition_lines_by_name(
    name_by_line: dict[int, str | None],
) -> dict[str, set[int]]:
    grouped: dict[str, set[int]] = {}
    for i, name in name_by_line.items():
        if name is not None:
            grouped.setdefault(name, set()).add(i)
    return grouped
def _drop_bare_name_users(
    lines: list[str],
    interior: set[int],
    def_lines_by_name: dict[str, set[int]],
    names: set[str],
) -> set[str]:
    return {
        name for name in names
        if not _has_bare_name_use(
            lines, interior, def_lines_by_name.get(name, set()), name)
    }
def _fallback_rewritable_lines(
    ctx: LoggerSourceScan,
) -> tuple[set[str], set[int]]:
    lines, interior = ctx.lines, ctx.interior
    name_by_line, simple_by_line = _definition_line_shapes(ctx)
    def_lines_by_name = _definition_lines_by_name(name_by_line)
    unsafe_names = {
        name for i, name in name_by_line.items()
        if name is not None and not simple_by_line[i]
    }
    safe_names = _drop_bare_name_users(
        lines, interior, def_lines_by_name,
        set(ctx.replaced_names) - unsafe_names)
    if len(safe_names) > 1:
        return set(), set()
    safe_def_lines = {
        i for i in ctx.def_line_nos
        if name_by_line.get(i) in safe_names and simple_by_line[i]
    }
    return safe_names, safe_def_lines
def _definition_line_shapes(
    ctx: LoggerSourceScan,
) -> tuple[dict[int, str | None], dict[int, bool]]:
    name_by_line: dict[int, str | None] = {}
    simple_by_line: dict[int, bool] = {}
    for i in ctx.def_line_nos:
        stripped = ctx.lines[i].lstrip()
        name = _leading_identifier(stripped)
        name_by_line[i] = name
        simple_by_line[i] = (
            name is not None
            and bool(_SIMPLE_ASSIGN_RE.match(stripped))
            and not _has_inline_separators(stripped)
            and _count_line_binding_ops(stripped) == 1
            and not stripped.endswith(_CONTINUATION_SUFFIXES))
    return name_by_line, simple_by_line
def _unify_logger_line_fallback(ctx: LoggerSourceScan) -> list[str]:
    lines, interior = ctx.lines, ctx.interior
    safe_names, safe_def_lines = _fallback_rewritable_lines(ctx)
    new_lines: list[str] = []
    for i, line in enumerate(lines):
        if i in safe_def_lines:
            stripped = line.lstrip()
            indent = line[: len(line) - len(stripped)]
            name = _leading_identifier(stripped)
            assert name is not None
            new_lines.append(f"{indent}logger{stripped[len(name):]}")
            continue
        text = line
        if safe_names and i not in interior:
            for name in safe_names:
                text = _replace_attr_refs_outside_strings(text, name)
        new_lines.append(text)
    return new_lines
def _collect_logger_edits_from_ast(
    tree: ast.Module,
    ctx: LoggerSourceScan,
) -> tuple[_EditSet, set[str]]:
    confirmed_defs, confirmed_names = _collect_confirmed_logger_defs(
        tree, ctx.def_line_nos, ctx.replaced_names)
    if len(confirmed_names) > 1:
        return _EditSet(), set()
    edits = _EditSet()
    for def_node, target in confirmed_defs:
        line = ctx.lines[def_node.lineno - 1]
        target_start, target_end = utf8_span_to_char_span(
            line, target.col_offset, target.end_col_offset)
        edits.add(def_node.lineno - 1, target_start, target_end,
                  _UNIFIED_LOGGER_NAME)
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Name)
                and node.id in confirmed_names
                and isinstance(node.ctx, (ast.Load, ast.Del))):
            char_start, char_end = utf8_span_to_char_span(
                ctx.lines[node.lineno - 1], node.col_offset,
                node.end_col_offset)
            edits.add(node.lineno - 1, char_start, char_end, "logger")
    if len(confirmed_names) == 1:
        export_ctx = _RenameContext(
            ctx.lines, next(iter(confirmed_names)), _UNIFIED_LOGGER_NAME,
            edits)
        for node in walk_nodes(tree):
            if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                _sync_all_assignment(node, export_ctx)
            elif isinstance(node, ast.Call):
                _sync_all_mutation(node, export_ctx)
    return edits, confirmed_names
def _rewrite_unified_logger_lines(
    source: str,
    ctx: LoggerSourceScan,
) -> list[str] | None:
    tree, _parse_error = parse_py_source(source)
    if tree is None:
        if any(re.search(r"\blogger\b", ctx.lines[i])
               for i in range(len(ctx.lines)) if i not in ctx.interior):
            return None
        new_lines = _unify_logger_line_fallback(ctx)
        if new_lines == ctx.lines:
            return None
    else:
        edits, confirmed_names = _collect_logger_edits_from_ast(tree, ctx)
        if not confirmed_names:
            return None
        new_lines = edits.apply_to_lines(ctx.lines)
    if (_logging_name_required(tree, ctx.lines, ctx.interior)
            and not _logging_import_bound(tree, ctx.lines, ctx.interior)):
        eol_suffix = "\r" if "\r\n" in source else ""
        new_lines.insert(_find_logging_insert_position(new_lines),
                         "import logging" + eol_suffix)
    return new_lines
def unify_logger(source: str) -> str:
    ctx = LoggerSourceScan.of(source)
    if not ctx.def_line_nos:
        return source
    new_lines = _rewrite_unified_logger_lines(source, ctx)
    if new_lines is None:
        return source
    return _source_line_break(source).join(new_lines)
@dataclass
class RenameDecision:
    action: str
    symbol: str = ""
    new_name: str = ""
    reason: str = ""
def decide_rename(
    symbol: str,
    is_private: bool,
    is_public_secondary: bool = False,
    is_type_definition_override: bool = False,
) -> RenameDecision:
    if is_type_definition_override:
        return RenameDecision(
            "abandon", symbol=symbol,
            reason="同名类型定义覆盖（本地定义 vs 导入定义，字段语义不同）最高危，"
                   "不重命名，直接放弃合并该文件",
        )
    if is_private:
        return RenameDecision(
            "rename", symbol=symbol, new_name=f"{symbol}_merged",
            reason="同名私有 helper → 重命名其一（重命名后须用 AST 同步更新文件内所有调用点）",
        )
    if is_public_secondary:
        return RenameDecision(
            "rename", symbol=symbol, new_name=f"{symbol}_imported",
            reason="同名公开符号 → 重命名次要用方",
        )
    return RenameDecision("keep", symbol=symbol, reason="无冲突，保留原名")
def _ident_token_at_boundary(text: str, i: int, n: int, token: str) -> bool:
    if not text.startswith(token, i):
        return False
    before_ok = i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")
    end = i + len(token)
    after_ok = end >= n or not (text[end].isalnum() or text[end] == "_")
    return before_ok and after_ok
def _advance_bracket_depth(ch: str, depth: int) -> int:
    if ch in "([{":
        return depth + 1
    if ch in ")]}":
        return depth - 1
    return depth
def _as_binding_span(
    lines: list[str], row: int, start: int, last_row: int, bound_name: str,
) -> tuple[int, int, int] | None:
    position = _skip_definition_gap(lines, row, start, last_row)
    if position is None:
        return None
    row, k = position
    line = lines[row]
    if _ident_token_at_boundary(line, k, len(line), bound_name):
        return row, k, k + len(bound_name)
    return None
def _locate_except_as_name(
        lines: list[str], row: int, start_col: int, bound_name: str,
        last_row: int, depth_start: int,
) -> tuple[tuple[int, int, int] | None, int]:
    line = lines[row]
    depth = depth_start
    for span_start, span_end, is_code in _iter_code_spans(line, start_col):
        if not is_code:
            continue
        for j in range(span_start, span_end):
            ch = line[j]
            next_depth = _advance_bracket_depth(ch, depth)
            if next_depth != depth:
                depth = next_depth
                continue
            if depth == 0 and _ident_token_at_boundary(
                    line, j, len(line), "as"):
                return _as_binding_span(
                    lines, row, j + 2, last_row, bound_name), depth
    return None, depth
def _sync_except_as_name(
    node: ast.ExceptHandler,
    ctx: _RenameContext,
) -> None:
    last_line = ((node.body[0].lineno - 1) if node.body
                 else node.lineno - 1)
    depth = 0
    for li in range(node.lineno - 1, last_line + 1):
        line = ctx.lines[li]
        start_col = 0
        if li == node.lineno - 1:
            start_col, _ = utf8_span_to_char_span(
                line, node.col_offset, node.col_offset)
        span, depth = _locate_except_as_name(
            ctx.lines, li, start_col, ctx.old_name, last_line, depth)
        if span is not None:
            ctx.add_span(*span)
            break
def _sync_global_decl_name(
    node: ast.Global | ast.Nonlocal,
    ctx: _RenameContext,
) -> None:
    first_row = node.lineno - 1
    last_row = node.end_lineno - 1
    for row in range(first_row, last_row + 1):
        line = ctx.lines[row]
        stmt_start = 0
        stmt_end = len(line)
        if row == first_row:
            stmt_start, _ = utf8_span_to_char_span(
                line, node.col_offset, node.col_offset)
        if row == last_row:
            _, stmt_end = utf8_span_to_char_span(
                line, node.end_col_offset, node.end_col_offset)
        seg = line[stmt_start:stmt_end]
        new_seg = re.sub(
            rf"\b{re.escape(ctx.old_name)}\b", ctx.new_name, seg)
        if new_seg != seg:
            ctx.edits.add(row, stmt_start, stmt_end, new_seg)
def _sync_name_token(node: ast.arg | ast.keyword,
                     ctx: _RenameContext) -> None:
    if node.arg != ctx.old_name:
        return
    line = ctx.lines[node.lineno - 1]
    char_start, char_end = utf8_span_to_char_span(
        line, node.col_offset,
        node.col_offset + len(ctx.old_name.encode("utf-8")))
    if line[char_start:char_end] == ctx.old_name:
        ctx.add_span(node.lineno - 1, char_start, char_end)
def _match_capture_span(
    node: ast.AST, lines: list[str], old_name: str,
) -> tuple[int, int, int] | None:
    start_row = node.lineno - 1
    end_row = node.end_lineno - 1
    start_col, _ = utf8_span_to_char_span(
        lines[start_row], node.col_offset, node.col_offset)
    _, end_col = utf8_span_to_char_span(lines[end_row], 0, node.end_col_offset)
    if start_row == end_row:
        text = lines[start_row][start_col:end_col]
    else:
        text = "\n".join(
            [lines[start_row][start_col:], *lines[start_row + 1:end_row],
             lines[end_row][:end_col]])
    matches = list(re.finditer(
        rf"(?<!\w){re.escape(old_name)}(?!\w)", text))
    if not matches:
        return None
    prefix = text[:matches[-1].start()]
    row = start_row + prefix.count("\n")
    col = (start_col + matches[-1].start() if "\n" not in prefix
           else len(prefix) - prefix.rfind("\n") - 1)
    line = lines[row]
    if line[col:col + len(old_name)] != old_name:
        return None
    return row, col, col + len(old_name)
def _sync_match_capture_name(node: ast.AST, ctx: _RenameContext) -> None:
    span = _match_capture_span(node, ctx.lines, ctx.old_name)
    if span is not None:
        ctx.add_span(*span)
def _sync_match_class_keyword_names(
    node: ast.MatchClass,
    ctx: _RenameContext,
) -> None:
    start_row = node.lineno - 1
    start_col, _ = utf8_span_to_char_span(
        ctx.lines[start_row], node.col_offset, node.col_offset)
    for attr, pattern in zip(
            node.kwd_attrs, node.kwd_patterns, strict=True):
        if attr != ctx.old_name:
            continue
        end_row = pattern.lineno - 1
        end_col, _ = utf8_span_to_char_span(
            ctx.lines[end_row], pattern.col_offset, pattern.col_offset)
        parts: list[str] = []
        for row in range(start_row, end_row + 1):
            line = _blank_string_literals(ctx.lines[row])
            part_start = start_col if row == start_row else 0
            part_end = end_col if row == end_row else len(line)
            parts.append(line[part_start:part_end])
        prefix = "\n".join(parts)
        matches = list(re.finditer(
            rf"(?<!\w){re.escape(ctx.old_name)}(?!\w)"
            r"(?:\s|\\\r?\n)*=", prefix))
        if not matches:
            continue
        before = prefix[:matches[-1].start()]
        row = start_row + before.count("\n")
        col = (start_col + matches[-1].start() if "\n" not in before
               else len(before) - before.rfind("\n") - 1)
        ctx.add_span(row, col, col + len(ctx.old_name))
_DEFINITION_KEYWORD_RE = re.compile(r"\b(?:def|class)\b")
_LINE_CONTINUATION_TAIL_RE = re.compile(r"\\[ \t]*\r?$")
def _definition_keyword_end(line: str) -> int | None:
    for start, end, is_code in _iter_code_spans(line):
        if not is_code:
            continue
        match = _DEFINITION_KEYWORD_RE.search(line[start:end])
        if match is not None:
            return start + match.end()
    return None
def _skip_definition_gap(
    lines: list[str], row: int, col: int, last_row: int,
) -> tuple[int, int] | None:
    while row <= last_row:
        line = lines[row]
        while col < len(line) and line[col].isspace():
            col += 1
        if col < len(line) and _LINE_CONTINUATION_TAIL_RE.match(line[col:]):
            row += 1
            col = 0
            continue
        if col >= len(line):
            return None
        return row, col
    return None
def _definition_name_span(
    node: ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef,
    lines: list[str],
    old_name: str,
) -> tuple[int, int, int] | None:
    keyword_row = node.lineno - 1
    keyword_end = _definition_keyword_end(lines[keyword_row])
    while keyword_end is None and keyword_row < node.end_lineno - 1:
        keyword_row += 1
        keyword_end = _definition_keyword_end(lines[keyword_row])
    if keyword_end is None:
        return None
    position = _skip_definition_gap(
        lines, keyword_row, keyword_end, node.end_lineno - 1)
    if position is None:
        return None
    row, col = position
    line = lines[row]
    end = col + len(old_name)
    if line[col:end] != old_name:
        return None
    if end < len(line) and (line[end].isalnum() or line[end] == "_"):
        return None
    return row, col, end
def _sync_definition_name(
    node: ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef,
    ctx: _RenameContext,
) -> None:
    span = _definition_name_span(node, ctx.lines, ctx.old_name)
    if span is not None:
        ctx.add_span(*span)
def _sync_from_module_name(node: ast.ImportFrom,
                            ctx: _RenameContext) -> None:
    module = node.module or ""
    if not module or ctx.old_name not in module.split("."):
        return
    new_module = _rename_dotted_segments(
        module, ctx.old_name, ctx.new_name)
    if new_module == module:
        return
    _collect_import_module_edit(
        node, ctx.lines, {module: new_module}, ctx.edits)
def _argument_names(args: ast.arguments) -> set[str]:
    return {arg.arg for arg in (*args.args, *args.kwonlyargs)}
def _assignment_target_values(
        target: ast.AST, value: ast.AST,
) -> list[tuple[ast.Name, ast.AST]]:
    if isinstance(target, ast.Name):
        return [(target, value)]
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))):
        return []
    if (any(isinstance(item, ast.Starred) for item in target.elts)
            or any(isinstance(item, ast.Starred) for item in value.elts)):
        return []
    if len(target.elts) != len(value.elts):
        return []
    pairs: list[tuple[ast.Name, ast.AST]] = []
    for target_item, value_item in zip(target.elts, value.elts, strict=True):
        pairs.extend(_assignment_target_values(target_item, value_item))
    return pairs
_COMPREHENSION_SCOPE_NODES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
_LEXICAL_SCOPE_NODES = (
    ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
    *_COMPREHENSION_SCOPE_NODES,
)
_FUNCTION_SCOPE_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
    *_COMPREHENSION_SCOPE_NODES,
)
_CALLABLE_DEFINITION_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
)
_EMPTY_VISITING: frozenset = frozenset()
class _KeywordOwnerResolver:
    def __init__(self, tree: ast.Module, old_name: str) -> None:
        self.old_name = old_name
        self._parents = {
            child: parent
            for parent in walk_nodes(tree)
            for child in ast.iter_child_nodes(parent)
        }
        self._scopes = {
            node: self._find_scope(node) for node in walk_nodes(tree)
        }
        self._align_outermost_comprehension_iter_scopes(tree)
        self._bindings: dict[
            ast.AST, dict[str, list[ast.AST]]
        ] = {}
        self._unpacked_values: dict[ast.Name, ast.AST] = {}
        self._attribute_values: dict[
            tuple[ast.ClassDef, str], list[ast.AST | None]
        ] = {}
        self._index_bindings(tree)
        self._index_receiver_attributes(tree)
    def _align_outermost_comprehension_iter_scopes(self, tree: ast.Module) -> None:
        for node in walk_nodes(tree):
            if (not isinstance(node, _COMPREHENSION_SCOPE_NODES)
                    or not node.generators):
                continue
            outer_scope = self._scopes[node]
            stack = [node.generators[0].iter]
            while stack:
                sub = stack.pop()
                self._scopes[sub] = outer_scope
                if isinstance(sub, _LEXICAL_SCOPE_NODES):
                    continue
                stack.extend(ast.iter_child_nodes(sub))
    def _store_binding_scope(self, node: ast.Name) -> ast.AST | None:
        scope = self._scopes[node]
        if isinstance(self._parents.get(node), ast.NamedExpr):
            while isinstance(scope, _COMPREHENSION_SCOPE_NODES):
                scope = self._scopes.get(scope)
        return scope
    def _find_scope(self, node: ast.AST) -> ast.AST | None:
        current = self._parents.get(node)
        while current is not None:
            if isinstance(current, _LEXICAL_SCOPE_NODES):
                return current
            current = self._parents.get(current)
        return None
    def _add_binding(self, scope: ast.AST | None, name: str,
                     binding: ast.AST) -> None:
        if scope is not None:
            self._bindings.setdefault(scope, {}).setdefault(
                name, []).append(binding)
    def _index_bindings(self, tree: ast.Module) -> None:
        assignment_target_ids: set[int] = set()
        for node in walk_nodes(tree):
            scope = self._scopes[node]
            if isinstance(node, _CALLABLE_DEFINITION_NODES):
                self._add_binding(scope, node.name, node)
            elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets = (
                    node.targets if isinstance(node, ast.Assign)
                    else [node.target]
                )
                for target in targets:
                    if isinstance(target, ast.Name):
                        assignment_target_ids.add(id(target))
                        self._add_binding(scope, target.id, node)
                    elif isinstance(node, ast.Assign):
                        for target_name, bound_value in _assignment_target_values(
                                target, node.value):
                            assignment_target_ids.add(id(target_name))
                            self._unpacked_values[target_name] = bound_value
                            self._add_binding(
                                scope, target_name.id, target_name)
            elif isinstance(node, ast.arg):
                self._add_binding(scope, node.arg, node)
            elif isinstance(node, ast.alias):
                bound = node.asname or node.name.split(".")[0]
                self._add_binding(scope, bound, node)
            elif isinstance(
                    node, (ast.ExceptHandler, ast.MatchAs, ast.MatchStar)):
                if node.name:
                    self._add_binding(scope, node.name, node)
            elif isinstance(node, ast.MatchMapping) and node.rest:
                self._add_binding(scope, node.rest, node)
        for node in walk_nodes(tree):
            if (isinstance(node, ast.Name)
                    and isinstance(node.ctx, ast.Store)
                    and id(node) not in assignment_target_ids):
                self._add_binding(self._store_binding_scope(node), node.id, node)
    def _index_receiver_attributes(self, tree: ast.Module) -> None:
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.Assign, ast.AnnAssign)):
                continue
            targets = (
                node.targets if isinstance(node, ast.Assign)
                else [node.target]
            )
            for target in targets:
                if not (isinstance(target, ast.Attribute)
                        and isinstance(target.value, ast.Name)):
                    continue
                visible = self._visible_bindings(
                    target.value.id, self._scopes[target.value])
                if visible is None:
                    continue
                bindings, _binding_scope = visible
                for binding in bindings:
                    owner = self._implicit_receiver_class(binding)
                    if owner is not None:
                        self._attribute_values.setdefault(
                            (owner, target.attr), []).append(node.value)

    def _visible_bindings(
            self, name: str, scope: ast.AST | None,
    ) -> tuple[list[ast.AST], ast.AST] | None:
        crossed_function = False
        current = scope
        while current is not None:
            if not (isinstance(current, ast.ClassDef) and crossed_function):
                bindings = self._bindings.get(current, {}).get(name)
                if bindings:
                    return bindings, current
            if isinstance(current, _FUNCTION_SCOPE_NODES):
                crossed_function = True
            current = self._scopes.get(current)
        return None
    def _name_accepts(self, name: str, scope: ast.AST | None,
                      visiting: frozenset[tuple[ast.AST, str]]) -> bool:
        visible = self._visible_bindings(name, scope)
        if visible is None:
            return False
        bindings, binding_scope = visible
        key = (binding_scope, name)
        if key in visiting:
            return False
        next_visiting = visiting | {key}
        return all(
            self._binding_accepts(binding, binding_scope, next_visiting)
            for binding in bindings
        )
    def _binding_value(self, binding: ast.AST) -> ast.AST | None:
        if isinstance(binding, (ast.Assign, ast.AnnAssign)):
            return binding.value
        if isinstance(binding, ast.Name):
            return self._unpacked_values.get(binding)
        return None
    @staticmethod
    def _if_exp_branches(node: ast.IfExp) -> tuple[ast.AST, ...]:
        if isinstance(node.test, ast.Constant):
            return (node.body if bool(node.test.value) else node.orelse,)
        return node.body, node.orelse
    def _callable_value_accepts(
            self, value: ast.AST | None, scope: ast.AST,
            visiting: frozenset[tuple[ast.AST, str]],
    ) -> bool:
        if isinstance(value, ast.Lambda):
            return self.old_name in _argument_names(value.args)
        if isinstance(value, ast.Name):
            return self._name_accepts(value.id, scope, visiting)
        if isinstance(value, ast.IfExp):
            return all(
                self._callable_value_accepts(branch, scope, visiting)
                for branch in self._if_exp_branches(value))
        return False
    def _binding_accepts(
            self, binding: ast.AST, scope: ast.AST,
            visiting: frozenset[tuple[ast.AST, str]],
    ) -> bool:
        if isinstance(binding, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return self.old_name in _argument_names(binding.args)
        if isinstance(binding, ast.ClassDef):
            return self._class_accepts(binding, scope, visiting)
        return self._callable_value_accepts(
            self._binding_value(binding), scope, visiting)
    def _class_accepts(
            self, node: ast.ClassDef, scope: ast.AST,
            visiting: frozenset[tuple[ast.AST, str]],
    ) -> bool:
        constructors = [
            stmt for stmt in node.body
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef))
            and stmt.name in {"__init__", "__new__"}
        ]
        if constructors:
            return any(
                self.old_name in _argument_names(stmt.args)
                for stmt in constructors
            )
        return any(
            self._name_accepts(base.id, scope, visiting)
            for base in node.bases if isinstance(base, ast.Name)
        )
    def _class_bindings(
            self, name: str, scope: ast.AST | None) -> list[ast.ClassDef]:
        visible = self._visible_bindings(name, scope)
        if visible is None:
            return []
        bindings, _binding_scope = visible
        if not all(isinstance(binding, ast.ClassDef) for binding in bindings):
            return []
        return list(bindings)
    def _implicit_receiver_class(self, binding: ast.AST) -> ast.ClassDef | None:
        if not isinstance(binding, ast.arg):
            return None
        arguments = self._parents.get(binding)
        owner = self._parents.get(arguments)
        if not isinstance(owner, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return None
        positional = (*owner.args.posonlyargs, *owner.args.args)
        if not positional or positional[0] is not binding:
            return None
        if any(
                (isinstance(decorator, ast.Name)
                 and decorator.id == "staticmethod")
                or (isinstance(decorator, ast.Attribute)
                    and decorator.attr == "staticmethod")
                for decorator in owner.decorator_list):
            return None
        class_node = self._parents.get(owner)
        return class_node if isinstance(class_node, ast.ClassDef) else None
    def _receiver_classes_from_name(
            self, name: str, scope: ast.AST | None,
            visiting: frozenset[tuple[ast.AST, str]] = _EMPTY_VISITING,
    ) -> list[ast.ClassDef]:
        visible = self._visible_bindings(name, scope)
        if visible is None:
            return []
        bindings, binding_scope = visible
        key = (binding_scope, name)
        if key in visiting:
            return []
        next_visiting = visiting | {key}
        classes: list[ast.ClassDef] = []
        for binding in bindings:
            if isinstance(binding, ast.ClassDef):
                classes.append(binding)
                continue
            value = self._binding_value(binding)
            if value is not None:
                bound_classes = self._receiver_classes(value, next_visiting)
                if not bound_classes:
                    return []
                classes.extend(bound_classes)
                continue
            class_node = self._implicit_receiver_class(binding)
            if class_node is None:
                return []
            classes.append(class_node)
        return classes
    def _receiver_classes(
            self, receiver: ast.AST | None,
            visiting: frozenset[tuple[ast.AST, str]] = _EMPTY_VISITING,
    ) -> list[ast.ClassDef]:
        if isinstance(receiver, ast.IfExp):
            branch_classes = [
                self._receiver_classes(branch, visiting)
                for branch in self._if_exp_branches(receiver)
            ]
            if not all(branch_classes):
                return []
            return [
                class_node for classes in branch_classes
                for class_node in classes
            ]
        if isinstance(receiver, ast.Attribute):
            if receiver.attr == "__class__":
                return self._receiver_classes(receiver.value, visiting)
            owner_classes = self._receiver_classes(receiver.value, visiting)
            if not owner_classes:
                return []
            classes: list[ast.ClassDef] = []
            for owner in owner_classes:
                key = (owner, receiver.attr)
                if key in visiting:
                    return []
                values = self._attribute_values.get(key)
                if not values:
                    return []
                next_visiting = visiting | {key}
                for value in values:
                    value_classes = self._receiver_classes(
                        value, next_visiting)
                    if not value_classes:
                        return []
                    classes.extend(value_classes)
            return classes
        if isinstance(receiver, ast.Call) and isinstance(receiver.func, ast.Name):
            return self._receiver_classes_from_name(
                receiver.func.id, self._scopes[receiver.func], visiting)
        if not isinstance(receiver, ast.Name):
            return []
        return self._receiver_classes_from_name(
            receiver.id, self._scopes[receiver], visiting)
    @staticmethod
    def _own_methods_named(
            class_node: ast.ClassDef, name: str,
    ) -> list[ast.FunctionDef | ast.AsyncFunctionDef]:
        return [
            stmt for stmt in class_node.body
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef))
            and stmt.name == name
        ]
    @staticmethod
    def _merge_class_mros(
            linearizations: list[list[ast.ClassDef]],
            bases: list[ast.ClassDef],
    ) -> list[ast.ClassDef] | None:
        sequences = [list(mro) for mro in linearizations] + [list(bases)]
        merged: list[ast.ClassDef] = []
        while any(sequences):
            candidate = next((
                sequence[0] for sequence in sequences if sequence
                and not any(sequence[0] in other[1:]
                            for other in sequences if other)
            ), None)
            if candidate is None:
                return None
            merged.append(candidate)
            for sequence in sequences:
                if sequence and sequence[0] is candidate:
                    sequence.pop(0)
        return merged
    def _class_mro(
            self, class_node: ast.ClassDef,
            visiting: frozenset[ast.ClassDef] = _EMPTY_VISITING,
    ) -> list[ast.ClassDef]:
        if class_node in visiting:
            return []
        bases: list[ast.ClassDef] = []
        for base in class_node.bases:
            if not isinstance(base, ast.Name):
                return []
            bindings = self._class_bindings(base.id, self._scopes[class_node])
            if len(bindings) != 1:
                return []
            bases.append(bindings[0])
        next_visiting = visiting | {class_node}
        linearizations: list[list[ast.ClassDef]] = []
        for base in bases:
            linearization = self._class_mro(base, next_visiting)
            if not linearization:
                return []
            linearizations.append(linearization)
        merged = self._merge_class_mros(linearizations, bases)
        return [class_node, *merged] if merged is not None else []
    def _methods_from_linearization(
            self, linearization: list[ast.ClassDef], name: str,
    ) -> list[ast.FunctionDef | ast.AsyncFunctionDef]:
        for owner in linearization:
            own = self._own_methods_named(owner, name)
            if own:
                return own
        return []
    def _methods_named(
            self, class_node: ast.ClassDef, name: str,
            visiting: frozenset[ast.ClassDef] = _EMPTY_VISITING,
    ) -> list[ast.FunctionDef | ast.AsyncFunctionDef]:
        linearization = self._class_mro(class_node)
        if linearization:
            return self._methods_from_linearization(linearization, name)
        own = self._own_methods_named(class_node, name)
        if own or class_node in visiting:
            return own
        next_visiting = visiting | {class_node}
        inherited: list[ast.FunctionDef | ast.AsyncFunctionDef] = []
        for base in class_node.bases:
            if not isinstance(base, ast.Name):
                continue
            for base_class in self._class_bindings(
                    base.id, self._scopes[class_node]):
                inherited.extend(self._methods_named(
                    base_class, name, next_visiting))
        return inherited
    def _inherited_methods_named(
            self, class_node: ast.ClassDef, name: str,
    ) -> list[ast.FunctionDef | ast.AsyncFunctionDef]:
        linearization = self._class_mro(class_node)
        if linearization:
            return self._methods_from_linearization(linearization[1:], name)
        inherited: list[ast.FunctionDef | ast.AsyncFunctionDef] = []
        for base in class_node.bases:
            if not isinstance(base, ast.Name):
                continue
            for base_class in self._class_bindings(
                    base.id, self._scopes[class_node]):
                inherited.extend(self._methods_named(base_class, name))
        return inherited
    def _enclosing_class(self, node: ast.AST) -> ast.ClassDef | None:
        current = self._parents.get(node)
        while current is not None:
            if isinstance(current, ast.ClassDef):
                return current
            current = self._parents.get(current)
        return None
    def _is_builtin_super_call(self, node: ast.AST) -> bool:
        return (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "super"
            and self._visible_bindings(
                "super", self._scopes[node.func]) is None
        )
    def _super_method_groups(
            self, call: ast.Call, name: str,
    ) -> list[list[ast.FunctionDef | ast.AsyncFunctionDef]]:
        if call.keywords:
            return []
        if not call.args:
            class_node = self._enclosing_class(call)
            if class_node is None:
                return []
            return [self._inherited_methods_named(class_node, name)]
        if len(call.args) != 2 or not isinstance(call.args[0], ast.Name):
            return []
        start_classes = self._class_bindings(
            call.args[0].id, self._scopes[call.args[0]])
        receiver_classes = self._receiver_classes(call.args[1])
        if not start_classes or not receiver_classes:
            return []
        groups: list[list[ast.FunctionDef | ast.AsyncFunctionDef]] = []
        for receiver_class in receiver_classes:
            linearization = self._class_mro(receiver_class)
            if not linearization:
                return []
            for start_class in start_classes:
                start_index = next((
                    index for index, candidate in enumerate(linearization)
                    if candidate is start_class
                ), None)
                if start_index is None:
                    return []
                groups.append(self._methods_from_linearization(
                    linearization[start_index + 1:], name))
        return groups
    def _attribute_accepts(self, call: ast.Call) -> bool:
        if not isinstance(call.func, ast.Attribute):
            return False
        receiver = call.func.value
        if self._is_builtin_super_call(receiver):
            methods_by_class = self._super_method_groups(
                receiver, call.func.attr)
        else:
            classes = self._receiver_classes(receiver)
            if not classes:
                return False
            methods_by_class = [
                self._methods_named(class_node, call.func.attr)
                for class_node in classes
            ]
        return all(methods_by_class) and all(
            self.old_name in _argument_names(method.args)
            for methods in methods_by_class for method in methods)
    def accepts_call(self, call: ast.Call) -> bool:
        if isinstance(call.func, ast.Attribute):
            return self._attribute_accepts(call)
        return self._callable_value_accepts(
            call.func, self._scopes[call.func], frozenset())
def _sync_call_keyword_names(
        call: ast.Call, ctx: _RenameContext,
        keyword_owners: _KeywordOwnerResolver) -> None:
    if not keyword_owners.accepts_call(call):
        return
    for keyword_node in call.keywords:
        _sync_name_token(keyword_node, ctx)
_TYPE_PARAM_NODES = tuple(
    node_type for node_type in (
        getattr(ast, "TypeVar", None),
        getattr(ast, "ParamSpec", None),
        getattr(ast, "TypeVarTuple", None),
    ) if isinstance(node_type, type)
)
def _sync_type_parameter_name(node: ast.AST, ctx: _RenameContext) -> None:
    if node.name != ctx.old_name:
        return
    line = ctx.lines[node.lineno - 1]
    node_start, _ = utf8_span_to_char_span(
        line, node.col_offset, node.col_offset)
    declaration_prefix = re.match(r"\s*(?:\*\*|\*)?\s*", line[node_start:])
    char_start = node_start + declaration_prefix.end()
    char_end = char_start + len(ctx.old_name)
    if line[char_start:char_end] == ctx.old_name:
        ctx.add_span(node.lineno - 1, char_start, char_end)
def _import_alias_segment_spans(
    node: ast.alias, lines: list[str],
) -> list[tuple[int, int, int]] | None:
    line = lines[node.lineno - 1]
    char_start, _ = utf8_span_to_char_span(
        line, node.col_offset, node.col_offset)
    expected = node.name.split(".")
    tokens = tokenize.generate_tokens(io.StringIO("\n".join(lines)).readline)
    found = False
    names: list[str] = []
    spans: list[tuple[int, int, int]] = []
    for token in tokens:
        if not found:
            if (token.type == tokenize.NAME
                    and token.start == (node.lineno, char_start)
                    and token.string == expected[0]):
                found = True
            else:
                continue
        elif token.type != tokenize.NAME:
            continue
        elif token.string == "as":
            break
        names.append(token.string)
        spans.append((token.start[0] - 1, token.start[1], token.end[1]))
        if names != expected[:len(names)]:
            return None
        if names == expected:
            return spans
    return None
def _collect_import_alias_edit(
    node: ast.alias, lines: list[str], new_name: str, edits: _EditSet,
) -> None:
    spans = _import_alias_segment_spans(node, lines)
    if spans is None:
        return
    for old_segment, new_segment, span in zip(
            node.name.split("."), new_name.split("."), spans, strict=True):
        if old_segment != new_segment:
            edits.add(*span, new_segment)
def _sync_import_alias_name(node: ast.alias, ctx: _RenameContext) -> None:
    if ctx.old_name in node.name.split("."):
        new_module = _rename_dotted_segments(
            node.name, ctx.old_name, ctx.new_name)
        _collect_import_alias_edit(node, ctx.lines, new_module, ctx.edits)
    if node.asname == ctx.old_name:
        span = _match_capture_span(node, ctx.lines, ctx.old_name)
        if span is not None:
            ctx.add_span(*span)
_ALL_MUTATION_METHODS = frozenset({"append", "extend", "insert", "remove"})
def _sync_all_export_string(node: ast.AST, ctx: _RenameContext) -> None:
    if not (isinstance(node, ast.Constant) and node.value == ctx.old_name):
        return
    if node.end_lineno != node.lineno:
        return
    line = ctx.lines[node.lineno - 1]
    char_start, char_end = utf8_span_to_char_span(
        line, node.col_offset, node.end_col_offset)
    ctx.edits.add(
        node.lineno - 1, char_start, char_end, repr(ctx.new_name))
def _sync_all_export_strings(value: ast.AST | None,
                             ctx: _RenameContext) -> None:
    if value is None:
        return
    for sub in walk_nodes(value):
        _sync_all_export_string(sub, ctx)
def _sync_all_assignment(
        node: ast.Assign | ast.AnnAssign | ast.AugAssign,
        ctx: _RenameContext) -> None:
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    if any(isinstance(target, ast.Name) and target.id == "__all__"
           for target in targets):
        _sync_all_export_strings(node.value, ctx)
def _sync_all_mutation(node: ast.Call, ctx: _RenameContext) -> None:
    func = node.func
    if not (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id == "__all__"
            and func.attr in _ALL_MUTATION_METHODS):
        return
    for arg in node.args:
        _sync_all_export_strings(arg, ctx)
_SYMBOL_NAME_EDIT_HANDLERS = {
    ast.arg: ("arg", _sync_name_token),
    ast.FunctionDef: ("name", _sync_definition_name),
    ast.AsyncFunctionDef: ("name", _sync_definition_name),
    ast.ClassDef: ("name", _sync_definition_name),
    ast.MatchAs: ("name", _sync_match_capture_name),
    ast.MatchStar: ("name", _sync_match_capture_name),
    ast.MatchMapping: ("rest", _sync_match_capture_name),
    ast.ExceptHandler: ("name", _sync_except_as_name),
}
def _collect_symbol_edits(
    tree: ast.Module,
    ctx: _RenameContext,
) -> None:
    keyword_owners = _KeywordOwnerResolver(tree, ctx.old_name)
    for node in walk_nodes(tree):
        _collect_symbol_edit_for_node(node, ctx, keyword_owners)
def _collect_symbol_edit_for_node(
    node: ast.AST,
    ctx: _RenameContext,
    keyword_owners: _KeywordOwnerResolver,
) -> None:
    if isinstance(node, (ast.Name, ast.Attribute)):
        span = _rename_node_span(node, ctx.lines, ctx.old_name)
        if span is not None:
            ctx.add_span(*span)
        return
    if isinstance(node, (ast.Global, ast.Nonlocal)):
        if ctx.old_name in node.names:
            _sync_global_decl_name(node, ctx)
        return
    if isinstance(node, ast.ImportFrom):
        _sync_from_module_name(node, ctx)
        return
    if isinstance(node, ast.Call):
        _sync_all_mutation(node, ctx)
        _sync_call_keyword_names(node, ctx, keyword_owners)
        return
    if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        _sync_all_assignment(node, ctx)
        return
    if isinstance(node, ast.MatchClass):
        _sync_match_class_keyword_names(node, ctx)
        return
    if isinstance(node, _TYPE_PARAM_NODES):
        _sync_type_parameter_name(node, ctx)
        return
    if isinstance(node, ast.alias):
        _sync_import_alias_name(node, ctx)
        return
    handler_spec = _SYMBOL_NAME_EDIT_HANDLERS.get(type(node))
    if handler_spec is None:
        return
    name_attr, handler = handler_spec
    if getattr(node, name_attr) == ctx.old_name:
        handler(node, ctx)
def _rename_node_span(
    node: ast.AST,
    lines: list[str],
    old_name: str,
) -> tuple[int, int, int] | None:
    if isinstance(node, ast.Name) and node.id == old_name:
        char_start, char_end = utf8_span_to_char_span(
            lines[node.lineno - 1], node.col_offset, node.end_col_offset)
        return node.lineno - 1, char_start, char_end
    if not (isinstance(node, ast.Attribute) and node.attr == old_name):
        return None
    line = lines[node.end_lineno - 1]
    attr_start = node.end_col_offset - len(old_name.encode("utf-8"))
    char_start, char_end = utf8_span_to_char_span(
        line, attr_start, node.end_col_offset)
    if line[char_start:char_end] != old_name:
        return None
    return node.end_lineno - 1, char_start, char_end
def rename_with_ast_sync(source: str, old_name: str, new_name: str) -> str:
    for label, name in (("old_name", old_name), ("new_name", new_name)):
        if (not isinstance(name, str) or not name.isidentifier()
                or keyword.iskeyword(name)):
            raise ValueError(
                f"{label} must be a valid non-keyword Python identifier")
    if old_name == new_name:
        return source
    tree = ast.parse(source)
    ctx = _RenameContext(
        lines=_split_source_lines(source),
        old_name=old_name, new_name=new_name,
        edits=_EditSet())
    _collect_symbol_edits(tree, ctx)
    return ctx.edits.apply_to(source)
def _rename_dotted_segments(module: str, source_stem: str, target_stem: str) -> str:
    segs = module.split(".")
    if not any(seg == source_stem for seg in segs):
        return module
    return ".".join(
        target_stem if seg == source_stem else seg for seg in segs)
def _collect_import_module_renames(
    tree: ast.Module, source_stem: str, target_stem: str,
) -> dict[str, str]:
    renames: dict[str, str] = {}
    for node in walk_nodes(tree):
        mods: list[str] = []
        if isinstance(node, ast.Import):
            mods = [a.name for a in node.names]
        elif isinstance(node, ast.ImportFrom):
            if node.module:
                mods.append(node.module)
            mods.extend(a.name for a in node.names)
        for mod in mods:
            new_mod = _rename_dotted_segments(mod, source_stem, target_stem)
            if new_mod != mod:
                renames[mod] = new_mod
    return renames
def _collect_import_source_edits(
    tree: ast.Module,
    lines: list[str],
    renames: dict[str, str],
) -> _EditSet:
    edits = _EditSet()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            _collect_import_alias_edits(node, lines, renames, edits)
        elif isinstance(node, ast.ImportFrom):
            if node.module:
                _collect_import_module_edit(node, lines, renames, edits)
            _collect_import_alias_edits(node, lines, renames, edits)
    return edits
def _collect_import_alias_edits(
    node: ast.Import | ast.ImportFrom,
    lines: list[str],
    renames: dict[str, str],
    edits: _EditSet,
) -> None:
    for alias in node.names:
        new_name = renames.get(alias.name)
        if new_name is None:
            continue
        _collect_import_alias_edit(alias, lines, new_name, edits)
def _import_from_module_segment_spans(
    node: ast.ImportFrom,
    lines: list[str],
    module: str,
) -> list[tuple[int, int, int]] | None:
    first_line = lines[node.lineno - 1]
    statement_start, _ = utf8_span_to_char_span(
        first_line, node.col_offset, node.col_offset)
    tokens = tokenize.generate_tokens(io.StringIO("\n".join(lines)).readline)
    found_from = False
    names: list[str] = []
    spans: list[tuple[int, int, int]] = []
    for token in tokens:
        if not found_from:
            if (token.type == tokenize.NAME and token.string == "from"
                    and token.start == (node.lineno, statement_start)):
                found_from = True
            continue
        if token.type == tokenize.NAME and token.string == "import":
            break
        if token.type != tokenize.NAME:
            continue
        names.append(token.string)
        spans.append((token.start[0] - 1, token.start[1], token.end[1]))
    if names != module.split("."):
        return None
    return spans
def _collect_import_module_edit(
    node: ast.ImportFrom,
    lines: list[str],
    renames: dict[str, str],
    edits: _EditSet,
) -> None:
    module = node.module or ""
    new_mod = renames.get(module)
    if new_mod is None:
        return
    spans = _import_from_module_segment_spans(node, lines, module)
    if spans is None:
        return
    for old_segment, new_segment, span in zip(
            module.split("."), new_mod.split("."), spans, strict=True):
        if old_segment != new_segment:
            edits.add(*span, new_segment)
def _rewrite_import_source(imp: str, source_stem: str, target_stem: str) -> str | None:
    if not source_stem or source_stem == target_stem:
        return None
    tree, _parse_error = parse_py_source(imp)
    if tree is None:
        lines = _split_source_lines(imp)
        interior = _collect_string_interior_lines(lines)
        pattern = re.compile(rf"\b{re.escape(source_stem)}\b")
        rewritten = _source_line_break(imp).join(
            line if row in interior else _map_segments(
                line,
                lambda segment: pattern.sub(target_stem, segment),
                lambda segment: segment,
            )
            for row, line in enumerate(lines)
        )
        return rewritten if rewritten != imp else None
    renames = _collect_import_module_renames(tree, source_stem, target_stem)
    if not renames:
        return None
    edits = _collect_import_source_edits(
        tree, _split_source_lines(imp), renames)
    if not edits:
        return None
    return edits.apply_to(imp)
def _as_import_strings(consumer_imports: Any) -> list[str]:
    if isinstance(consumer_imports, str):
        return [consumer_imports]
    if isinstance(consumer_imports, (list, tuple)):
        return [imp for imp in consumer_imports if isinstance(imp, str)]
    if consumer_imports is not None:
        _log.warning("[Migration] consumer_imports 形态非法(须为清单或单"
                     "条 import 字符串),按空清单处理: %s",
                     type(consumer_imports).__name__)
    return []
def build_post_migration_sync_plan(
    source_file: str,
    target_file: str,
    lazy_imports: dict[str, str],
    consumer_imports: list[str] | tuple[str, ...] | str | None,
) -> dict[str, Any]:
    source_path = os.fspath(source_file)
    target_path = os.fspath(target_file)
    for label, path in (("source_file", source_path), ("target_file", target_path)):
        if not str(path).strip():
            raise ValueError(f"{label} must be a non-empty file path")
    source_stem = Path(source_path).stem
    target_stem = Path(target_path).stem
    for label, stem in (("source_file", source_stem),
                        ("target_file", target_stem)):
        if not stem.isidentifier() or keyword.iskeyword(stem):
            raise ValueError(
                f"{label} stem must be a valid non-keyword Python identifier: "
                f"{stem!r}")
    same_file = (
        os.path.normcase(os.path.realpath(os.path.abspath(source_path)))
        == os.path.normcase(os.path.realpath(os.path.abspath(target_path)))
    )
    lazy_sync: dict[str, str] = {}
    lazy_map = lazy_imports if isinstance(lazy_imports, dict) else {}
    if not isinstance(lazy_imports, dict):
        _log.warning("[Migration] lazy_imports 形态非法(须为映射),按空映射"
                     "处理: %s", type(lazy_imports).__name__)
    for symbol, mod in lazy_map.items():
        if not isinstance(mod, str):
            _log.warning("[Migration] lazy_imports 模块名非 str,按不迁移"
                         "处理: %r", symbol)
            continue
        new_mod = _rename_dotted_segments(mod, source_stem, target_stem)
        if new_mod != mod:
            lazy_sync[symbol] = new_mod
    consumer_sync: list[str] = []
    for imp in _as_import_strings(consumer_imports):
        rewritten = _rewrite_import_source(imp, source_stem, target_stem)
        if rewritten is not None:
            consumer_sync.append(rewritten)
    return {
        "lazy_sync": lazy_sync,
        "consumer_sync": consumer_sync,
        "delete_source": not same_file,
        "pycache_clean": not same_file,
        "source_file": source_file,
        "target_file": target_file,
    }
_PYC_TAG_RE = re.compile(
    r"^[A-Za-z0-9_]+-[A-Za-z0-9_.-]+(?:\.opt-\d+)?\.pyc$")
def _is_pyc_for_source(pyc_name: str, stem: str) -> bool:
    prefix = stem + "."
    if not pyc_name.startswith(prefix) or not pyc_name.endswith(".pyc"):
        return False
    return _PYC_TAG_RE.fullmatch(pyc_name[len(prefix):]) is not None
def clean_pycache_for_file(file_path: str) -> list[str]:
    fp = Path(file_path)
    pycache_dir = fp.parent / "__pycache__"
    cleaned: list[str] = []
    if not pycache_dir.is_dir():
        return cleaned
    stem = fp.stem
    try:
        pyc_entries = list(pycache_dir.iterdir())
    except OSError as e:
        _log.warning("[Boundary] pycache 清理异常: %s", e)
        return cleaned
    for pyc in pyc_entries:
        if pyc.suffix == ".pyc" and _is_pyc_for_source(pyc.name, stem):
            try:
                pyc.unlink()
                cleaned.append(str(pyc))
            except OSError as e:
                _log.warning("[Boundary] pycache 清理异常: %s", e)
    return cleaned
def _skip_quoted_literal(ln: str, j: int) -> int:
    ch = ln[j]
    k = j + 1
    n = len(ln)
    while k < n:
        if ln[k] == "\\":
            k += 2
            continue
        if ln[k] == ch:
            break
        k += 1
    return k + 1 if k < n else n
def _scan_to_triple_quote(ln: str, start: int) -> tuple[int, str] | None:
    seg = scan_line_segments(ln[start:])
    for begin, end, is_code in seg.spans:
        if is_code:
            continue
        text = ln[start + begin:start + end]
        if text.startswith("'''"):
            return start + begin, "'''"
        if text.startswith('"""'):
            return start + begin, '"""'
    return None
def _find_unescaped_triple(ln: str, delim: str, start: int) -> int:
    i = start
    while True:
        i = ln.find(delim, i)
        if i == -1:
            return -1
        bs = 0
        j = i - 1
        while j >= 0 and ln[j] == "\\":
            bs += 1
            j -= 1
        if bs % 2 == 0:
            return i
        i += 1
@dataclass(frozen=True)
class LineSegments:
    spans: tuple[tuple[int, int, bool], ...]
    comment_start: int | None
    unterminated_triple: bool
def _literal_span_end(ln: str, start: int, quote: str) -> tuple[int, bool]:
    delim = quote * 3
    if ln.startswith(delim, start):
        close = _find_unescaped_triple(ln, delim, start + 3)
        return (len(ln), True) if close == -1 else (
            min(len(ln), close + 3), False)
    return _skip_quoted_literal(ln, start), False
def scan_line_segments(ln: str) -> LineSegments:
    spans: list[tuple[int, int, bool]] = []
    n = len(ln)
    seg_start = 0
    j = 0
    while j < n:
        ch = ln[j]
        if ch == "#":
            if seg_start < j:
                spans.append((seg_start, j, True))
            spans.append((j, n, False))
            return LineSegments(tuple(spans), j, False)
        if ch not in ("'", '"'):
            j += 1
            continue
        if seg_start < j:
            spans.append((seg_start, j, True))
        lit_end, unterminated = _literal_span_end(ln, j, ch)
        spans.append((j, lit_end, False))
        if unterminated:
            return LineSegments(tuple(spans), None, True)
        seg_start = j = lit_end
    if seg_start < n:
        spans.append((seg_start, n, True))
    return LineSegments(tuple(spans), None, False)
def _collect_string_interior_lines(lines: list[str]) -> set[int]:
    interior: set[int] = set()
    quote = ""
    in_str = False
    for i, ln in enumerate(lines):
        quote, in_str, is_interior = _scan_line_string_state(
            ln, quote, in_str)
        if is_interior:
            interior.add(i)
    return interior
def _scan_line_string_state(ln: str, quote: str,
                            in_str: bool) -> tuple[str, bool, bool]:
    started_in_string = in_str
    pos = 0
    while pos <= len(ln):
        if in_str:
            idx = _find_unescaped_triple(ln, quote, pos)
            if idx == -1:
                return quote, True, started_in_string
            pos, in_str = idx + 3, False
        else:
            found = _scan_to_triple_quote(ln, pos)
            if found is None:
                return quote, False, started_in_string
            delim_start, quote = found
            pos, in_str = delim_start + 3, True
    return quote, in_str, started_in_string
def _row_after_docstring(new_lines: list[str], row: int, quote: str) -> int:
    first = new_lines[row].strip()
    if _find_unescaped_triple(first, quote, first.index(quote) + 3) != -1:
        return row + 1
    close_row = _docstring_close_row(new_lines, row, quote)
    return -1 if close_row == -1 else close_row + 1
def _logging_symbol_names(tree: ast.AST) -> tuple[set[str], set[str]]:
    module_aliases = set(_DEFAULT_LOGGING_ALIASES)
    bare_getlogger_names = set(_DEFAULT_BARE_GETLOGGER_NAMES)
    confirmed_import_ids: set[int] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if (alias.name == "logging"
                        or alias.name.startswith("logging.")):
                    module_aliases.add(
                        alias.asname or alias.name.split(".")[0])
                    confirmed_import_ids.add(id(alias))
        elif isinstance(node, ast.ImportFrom) and node.module == "logging":
            for alias in node.names:
                if alias.name == "getLogger":
                    bare_getlogger_names.add(alias.asname or alias.name)
                    confirmed_import_ids.add(id(alias))
    candidates = module_aliases | bare_getlogger_names
    shadowed = _collect_shadow_binding_names(
        tree, candidates, confirmed_import_ids)
    return module_aliases - shadowed, bare_getlogger_names - shadowed
def _is_logger_getlogger_call(
        value: ast.AST | None,
        logging_aliases: Collection[str],
        bare_getlogger_names: Collection[str],
) -> bool:
    if not isinstance(value, ast.Call):
        return False
    func = value.func
    if isinstance(func, ast.Attribute):
        return (func.attr == "getLogger"
                and isinstance(func.value, ast.Name)
                and func.value.id in logging_aliases)
    if isinstance(func, ast.Name):
        return func.id in bare_getlogger_names
    return False
def _is_pure_condition(node: ast.AST | None) -> bool:
    return (isinstance(node, ast.Constant)
            or (isinstance(node, ast.Name) and node.id == "__debug__"))
def _value_is_pure_getlogger(
        value: ast.AST | None,
        logging_aliases: Collection[str],
        bare_getlogger_names: Collection[str],
) -> bool:
    if _is_logger_getlogger_call(
            value, logging_aliases, bare_getlogger_names):
        return True
    if isinstance(value, ast.IfExp):
        return (
            _is_pure_condition(value.test)
            and _value_is_pure_getlogger(
                value.body, logging_aliases, bare_getlogger_names)
            and _value_is_pure_getlogger(
                value.orelse, logging_aliases, bare_getlogger_names))
    return False
def _is_logger_def_line(raw_line: str) -> bool:
    code_line = _blank_string_literals(raw_line)
    name = _leading_identifier(code_line)
    return (name is not None
            and "=" in code_line
            and _GETLOGGER_CALL_RE.search(code_line) is not None)
def _scan_logger_def_candidates(
    lines: list[str],
    interior: set[int],
) -> tuple[set[str], set[int]]:
    replaced_names: set[str] = set()
    def_line_nos: set[int] = set()
    for i, line in enumerate(lines):
        if i in interior:
            continue
        stripped = line.lstrip()
        if _is_logger_def_line(line):
            name = _leading_identifier(stripped)
            if name is not None:
                replaced_names.add(name)
            def_line_nos.add(i)
    return replaced_names, def_line_nos
def _detect_logger_evidence_ast(source: str) -> list[str] | None:
    tree, _parse_error = parse_py_source(source)
    if tree is None:
        return None
    scan = LoggerSourceScan.of(source)
    confirmed_defs, confirmed_names = _collect_confirmed_logger_defs(
        tree, scan.def_line_nos, scan.replaced_names)
    def_rows = {
        node.lineno for node, target in confirmed_defs
        if target.id != _UNIFIED_LOGGER_NAME
    }
    use_names = {
        name for name in confirmed_names if name != _UNIFIED_LOGGER_NAME
    }
    use_names.update(
        name for name in _logger_like_use_names(tree)
        if name != _UNIFIED_LOGGER_NAME)
    if not use_names:
        return []
    return _format_logger_evidence(
        scan.lines, def_rows, _collect_logger_use_rows(tree, use_names))
def _logger_like_use_names(tree: ast.AST) -> set[str]:
    return {node.id for node in walk_nodes(tree)
            if isinstance(node, ast.Name) and _logger_name_like(node.id)}
def _collect_logger_use_rows(tree: ast.AST, names: set[str]) -> set[int]:
    return {node.lineno for node in walk_nodes(tree)
            if isinstance(node, ast.Attribute)
            and isinstance(node.ctx, (ast.Load, ast.Del))
            and node.attr in _LOGGER_USE_METHODS
            and isinstance(node.value, ast.Name)
            and node.value.id in names}
def _evidence_line(row: int, text: str, non_unified: bool = False) -> str:
    suffix = "（logger 变量名非统一命名）" if non_unified else ""
    text = text.removesuffix("\r")
    return f"行{row}: {text}{suffix}"
def _format_logger_evidence(
    lines: list[str],
    def_rows: set[int],
    use_rows: set[int],
) -> list[str]:
    return [
        _evidence_line(row, lines[row - 1].lstrip(), row in def_rows)
        for row in sorted(use_rows | def_rows)
    ]
def detect_logger_lines(source: str) -> list[str]:
    ast_evidence = _detect_logger_evidence_ast(source)
    if ast_evidence is not None:
        return ast_evidence
    return _detect_logger_evidence_lines(LoggerSourceScan.of(source))
def _detect_logger_evidence_lines(scan: LoggerSourceScan) -> list[str]:
    evidence: list[str] = []
    names = {name for name in scan.replaced_names
             if name != _UNIFIED_LOGGER_NAME}
    for i, line in enumerate(scan.lines, start=1):
        if (i - 1) in scan.interior:
            continue
        stripped = line.lstrip()
        if stripped.startswith("#"):
            continue
        code_line = _blank_string_literals(line)
        if any(re.search(rf"\b{re.escape(name)}\.", code_line)
               for name in names) or _logger_like_attribute_use(code_line):
            evidence.append(_evidence_line(i, stripped))
        elif _is_logger_def_line(line):
            name = _leading_identifier(stripped)
            if name is not None and name != _UNIFIED_LOGGER_NAME:
                evidence.append(_evidence_line(i, stripped, non_unified=True))
    return evidence
def _logger_like_attribute_use(code_line: str) -> bool:
    return any(_logger_name_like(name)
               and name != _UNIFIED_LOGGER_NAME
               and attr in _LOGGER_USE_METHODS
               for name, attr in re.findall(
                   r"\b([A-Za-z_]\w*)\.([A-Za-z_]\w*)", code_line))
_DOCSTRING_OPEN_RE = re.compile(
    r"(?:[rR][bBfF]?|[bB][rR]?|[fF][rR]?|[uU])?(\"\"\"|''')")
def _docstring_open_quote(s: str) -> str | None:
    m = _DOCSTRING_OPEN_RE.match(s)
    if m is None:
        return None
    if any(c in "bBfF" for c in s[:m.start(1)]):
        return None
    return m.group(1)
def _docstring_close_row(
        lines: list[str], open_row: int, quote: str) -> int:
    for row in range(open_row + 1, len(lines)):
        if _find_unescaped_triple(lines[row].strip(), quote, 0) != -1:
            return row
    return -1
def _is_future_import(stmt: ast.stmt) -> bool:
    return (isinstance(stmt, ast.ImportFrom) and stmt.level == 0
            and stmt.module == "__future__")
def _ast_logging_insert_position(lines: list[str]) -> int | None:
    tree, _parse_error = parse_py_source("\n".join(lines))
    if tree is None:
        return None
    return _header_insert_position(tree.body)
def _future_imports_end(stmts: list[ast.stmt]) -> int:
    end = 0
    for stmt in stmts:
        if not _is_future_import(stmt):
            break
        end = stmt.end_lineno or stmt.lineno
    return end
def _header_insert_position(body: list[ast.stmt]) -> int:
    head_end = 0
    rest = body
    if body and is_docstring_stmt(body[0]):
        head_end = body[0].end_lineno or body[0].lineno
        rest = body[1:]
    future_end = _future_imports_end(rest)
    if future_end or head_end:
        return future_end or head_end
    if not rest:
        return 0
    first = rest[0]
    first_row = min(
        [first.lineno,
         *(decorator.lineno
           for decorator in getattr(first, "decorator_list", ()))])
    return first_row - 1
def _future_import_end_row(lines: list[str], row: int) -> int:
    depth = 0
    while row < len(lines):
        line = lines[row]
        code_parts: list[str] = []
        for start, end, is_code in scan_line_segments(line).spans:
            if not is_code:
                continue
            code_parts.append(line[start:end])
            depth += sum(line.count(ch, start, end) for ch in "([{")
            depth -= sum(line.count(ch, start, end) for ch in ")]}")
            depth = max(depth, 0)
        if depth == 0 and not "".join(code_parts).rstrip().endswith("\\"):
            return row
        row += 1
    return len(lines) - 1
def _find_logging_insert_position(new_lines: list[str]) -> int:
    _ast_row = _ast_logging_insert_position(new_lines)
    if _ast_row is not None:
        return _ast_row
    insert_at = 0
    doc_seen = False
    row = 0
    while row < len(new_lines):
        s = new_lines[row].strip()
        if s.startswith("from __future__ import"):
            row = _future_import_end_row(new_lines, row)
            insert_at = row + 1
            row += 1
            continue
        if not s or s.startswith("#"):
            row += 1
            continue
        quote = _docstring_open_quote(s) if not doc_seen else None
        if quote is None:
            if not insert_at:
                insert_at = row
            break
        doc_seen = True
        row = _row_after_docstring(new_lines, row, quote)
        if row == -1:
            break
        insert_at = row
    return insert_at
def _alias_binds_logging(dotted_name: str, asname: str | None) -> bool:
    return (asname or dotted_name.split(".", maxsplit=1)[0]) == "logging"
def _module_import_binds_logging(tree: ast.Module) -> bool:
    return any(
        _alias_binds_logging(alias.name, alias.asname)
        for node in iter_own_scope(
                tree, skip_type_checking_body=True,
                tc_polarities=_type_checking_guard_node_polarities(tree))
        if isinstance(node, ast.Import)
        for alias in node.names
    )
def _lines_bind_logging(lines: list[str], interior: set[int]) -> bool:
    for i, ln in enumerate(lines):
        if i in interior:
            continue
        m = re.match(r"import\s+(.*)$", ln)
        if not m:
            continue
        body = m.group(1).split("#", 1)[0]
        for alias in body.split(","):
            seg = alias.strip()
            if not seg:
                continue
            parts = re.split(r"\s+as\s+", seg, maxsplit=1)
            if _alias_binds_logging(
                    parts[0].strip(),
                    parts[1].strip() if len(parts) > 1 else None):
                return True
    return False
def _logging_import_bound(
        tree: ast.Module | None, lines: list[str],
        interior: set[int]) -> bool:
    if tree is not None:
        return _module_import_binds_logging(tree)
    return _lines_bind_logging(lines, interior)
def _logging_name_required(
    tree: ast.Module | None, lines: list[str], interior: set[int],
) -> bool:
    if tree is not None:
        return any(
            isinstance(node, ast.Name) and node.id == "logging"
            for node in walk_nodes(tree))
    return any(
        re.search(r"\blogging\b", _blank_string_literals(line)) is not None
        for row, line in enumerate(lines) if row not in interior)
_CLASS_SCOPE_DEFINITION_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
)
_CLASS_SCOPE_COMPREHENSIONS = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
def _iter_class_body_nodes(body: list[ast.AST]):
    stack: list[ast.AST] = list(body)
    while stack:
        sub = stack.pop()
        if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield sub
            stack.extend(sub.decorator_list)
            stack.append(sub.args)
            if isinstance(sub.returns, ast.AST):
                stack.append(sub.returns)
            stack.extend(getattr(sub, "type_params", ()))
            continue
        if isinstance(sub, ast.ClassDef):
            yield sub
            stack.extend(sub.decorator_list)
            stack.extend(sub.bases)
            stack.extend(keyword.value for keyword in sub.keywords)
            stack.extend(getattr(sub, "type_params", ()))
            continue
        if isinstance(sub, ast.Lambda):
            stack.append(sub.args)
            continue
        if isinstance(sub, _CLASS_SCOPE_COMPREHENSIONS):
            if sub.generators:
                stack.append(sub.generators[0].iter)
            continue
        yield sub
        stack.extend(ast.iter_child_nodes(sub))
def _iter_class_scope_binding_nodes(tree: ast.AST):
    for node in walk_nodes(tree):
        if isinstance(node, ast.ClassDef):
            yield from _iter_class_body_nodes(node.body)
def _class_scope_binding_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
        return node.id
    if isinstance(node, _CLASS_SCOPE_DEFINITION_NODES):
        return node.name
    if isinstance(node, ast.alias):
        return node.asname or node.name.split(".")[0]
    if isinstance(node, ast.ExceptHandler):
        return node.name
    if isinstance(node, (ast.MatchAs, ast.MatchStar)):
        return node.name
    if isinstance(node, ast.MatchMapping):
        return node.rest
    return None
def _collect_class_body_binding_ids(tree: ast.AST) -> tuple[set[int], set[int]]:
    stmt_ids: set[int] = set()
    binding_ids: set[int] = set()
    for sub in _iter_class_scope_binding_nodes(tree):
        if isinstance(sub, (ast.Assign, ast.AnnAssign)):
            stmt_ids.add(id(sub))
        if _class_scope_binding_name(sub) is not None:
            binding_ids.add(id(sub))
    return stmt_ids, binding_ids
def _store_shadow_name(node: ast.Name, candidate_names: set[str],
                       confirmed_target_ids: set[int],
                       class_body_binding_ids: set[int]) -> set[str]:
    if (node.id in candidate_names
            and isinstance(node.ctx, ast.Store)
            and id(node) not in confirmed_target_ids
            and id(node) not in class_body_binding_ids):
        return {node.id}
    return set()
def _definition_shadow_name(node: ast.AST, candidate_names: set[str],
                            _confirmed_target_ids: set[int],
                            class_body_binding_ids: set[int]) -> set[str]:
    if id(node) in class_body_binding_ids:
        return set()
    return {node.name} if node.name in candidate_names else set()
def _pattern_shadow_name(node: ast.AST, candidate_names: set[str],
                         _confirmed_target_ids: set[int],
                         class_body_binding_ids: set[int]) -> set[str]:
    if id(node) in class_body_binding_ids:
        return set()
    name = getattr(node, "name", None) or getattr(node, "rest", None)
    return {name} if name in candidate_names else set()
def _alias_shadow_name(node: ast.alias, candidate_names: set[str],
                       confirmed_target_ids: set[int],
                       class_body_binding_ids: set[int]) -> set[str]:
    if id(node) in confirmed_target_ids or id(node) in class_body_binding_ids:
        return set()
    bound = node.asname or node.name.split(".")[0]
    return {bound} if bound in candidate_names else set()
def _arg_shadow_name(node: ast.arg, candidate_names: set[str],
                     _confirmed_target_ids: set[int],
                     _class_body_binding_ids: set[int]) -> set[str]:
    return {node.arg} if node.arg in candidate_names else set()
def _declaration_shadow_name(node: ast.Global | ast.Nonlocal,
                             candidate_names: set[str],
                             _confirmed_target_ids: set[int],
                             _class_body_binding_ids: set[int]) -> set[str]:
    return {nm for nm in node.names if nm in candidate_names}
def _except_shadow_name(node: ast.ExceptHandler, candidate_names: set[str],
                        _confirmed_target_ids: set[int],
                        class_body_binding_ids: set[int]) -> set[str]:
    if id(node) in class_body_binding_ids:
        return set()
    return {node.name} if node.name and node.name in candidate_names else set()
_SHADOW_NAME_COLLECTORS = (
    (ast.Name, _store_shadow_name),
    (_CLASS_SCOPE_DEFINITION_NODES, _definition_shadow_name),
    (_TYPE_PARAM_NODES, _definition_shadow_name),
    ((ast.MatchAs, ast.MatchStar, ast.MatchMapping), _pattern_shadow_name),
    (ast.arg, _arg_shadow_name),
    ((ast.Global, ast.Nonlocal), _declaration_shadow_name),
    (ast.alias, _alias_shadow_name),
    (ast.ExceptHandler, _except_shadow_name),
)
def _shadow_names_from_node(
    node: ast.AST,
    candidate_names: set[str],
    confirmed_target_ids: set[int],
    class_body_binding_ids: set[int],
) -> set[str]:
    for node_types, collector in _SHADOW_NAME_COLLECTORS:
        if isinstance(node, node_types):
            return collector(node, candidate_names,
                             confirmed_target_ids, class_body_binding_ids)
    return set()
def _collect_class_body_bound_names(classdef: ast.ClassDef) -> set[str]:
    names: set[str] = set()
    for sub in _iter_class_body_nodes(classdef.body):
        name = _class_scope_binding_name(sub)
        if name is not None:
            names.add(name)
    return names
def _class_body_local_use_shadows(tree: ast.AST,
                                  names: set[str]) -> set[str]:
    if not names:
        return set()
    shadowed: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        bound = _collect_class_body_bound_names(node) & names
        if not bound:
            continue
        used: set[str] = set()
        for sub in _iter_class_body_nodes(node.body):
            if (isinstance(sub, ast.Name)
                    and isinstance(sub.ctx, (ast.Load, ast.Del))):
                used.add(sub.id)
            elif (isinstance(sub, ast.AugAssign)
                  and isinstance(sub.target, ast.Name)):
                used.add(sub.target.id)
        shadowed |= bound & used
    return shadowed
def _collect_shadow_binding_names(
    tree: ast.AST,
    candidate_names: set[str],
    confirmed_target_ids: set[int],
    class_body_binding_ids: set[int] | None = None,
) -> set[str]:
    if class_body_binding_ids is None:
        class_body_binding_ids = _collect_class_body_binding_ids(tree)[1]
    shadowed: set[str] = set()
    for node in walk_nodes(tree):
        shadowed |= _shadow_names_from_node(
            node, candidate_names, confirmed_target_ids,
            class_body_binding_ids)
    return shadowed
def _statement_binds_only_target(node: ast.Assign | ast.AnnAssign) -> bool:
    if isinstance(node, ast.Assign) and len(node.targets) != 1:
        return False
    value = node.value
    if value is None:
        return True
    return not any(isinstance(sub, ast.NamedExpr)
                   for sub in walk_nodes(value))
def _assign_target_name(node: ast.Assign | ast.AnnAssign) -> ast.AST | None:
    if isinstance(node, ast.Assign):
        return node.targets[0] if node.targets else None
    return node.target
def _is_confirmed_def_candidate(
    node: ast.AST,
    target: ast.AST | None,
    def_line_nos: set[int],
    class_body_ids: set[int],
    replaced_names: set[str],
    logging_aliases: set[str],
    bare_getlogger_names: set[str],
) -> bool:
    return (
        isinstance(node, (ast.Assign, ast.AnnAssign))
        and node.lineno - 1 in def_line_nos
        and id(node) not in class_body_ids
        and isinstance(target, ast.Name)
        and target.id in replaced_names
        and _value_is_pure_getlogger(
            node.value, logging_aliases, bare_getlogger_names)
        and node.end_lineno == node.lineno
        and _statement_binds_only_target(node)
    )
@dataclass(frozen=True)
class LoggerSourceScan:
    lines: list[str]
    interior: set[int]
    replaced_names: set[str]
    def_line_nos: set[int]
    @classmethod
    def of(cls, source: str) -> LoggerSourceScan:
        lines = _split_source_lines(source)
        interior = _collect_string_interior_lines(lines)
        replaced_names, def_line_nos = _scan_logger_def_candidates(
            lines, interior)
        tree, _parse_error = parse_py_source(source)
        if tree is not None:
            logging_aliases, bare_getlogger_names = _logging_symbol_names(tree)
            for node in walk_nodes(tree):
                if (not isinstance(node, (ast.Assign, ast.AnnAssign))
                        or node.end_lineno != node.lineno):
                    continue
                target = _assign_target_name(node)
                if (isinstance(target, ast.Name)
                        and _value_is_pure_getlogger(
                            node.value, logging_aliases, bare_getlogger_names)):
                    replaced_names.add(target.id)
                    def_line_nos.add(node.lineno - 1)
        return cls(lines, interior, replaced_names, def_line_nos)
def _logger_target_has_existing_use(tree: ast.AST) -> bool:
    class_body_ids: set[int] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.ClassDef):
            for sub in _iter_class_body_nodes(node.body):
                class_body_ids.add(id(sub))
    return any(
        isinstance(node, ast.Name) and node.id == _UNIFIED_LOGGER_NAME
        and isinstance(node.ctx, (ast.Load, ast.Del, ast.Store))
        and id(node) not in class_body_ids
        for node in walk_nodes(tree))
def _collect_confirmed_logger_defs(
    tree: ast.AST,
    def_line_nos: set[int],
    replaced_names: set[str],
) -> tuple[list[tuple[ast.AST, ast.Name]], set[str]]:
    class_body_ids, class_body_binding_ids = _collect_class_body_binding_ids(tree)
    logging_aliases, bare_getlogger_names = _logging_symbol_names(tree)
    confirmed_defs = list(_iter_confirmed_def_candidates(
        tree, def_line_nos, replaced_names, class_body_ids, logging_aliases,
        bare_getlogger_names))
    confirmed_names = {target.id for _node, target in confirmed_defs}
    if not confirmed_names or (
            _UNIFIED_LOGGER_NAME not in confirmed_names
            and _logger_target_has_existing_use(tree)):
        return [], set()
    confirmed_target_ids = {id(t) for _, t in confirmed_defs}
    shadowed = _collect_shadow_binding_names(
        tree, confirmed_names | {_UNIFIED_LOGGER_NAME}, confirmed_target_ids,
        class_body_binding_ids)
    shadowed |= _class_body_local_use_shadows(tree, confirmed_names)
    if _UNIFIED_LOGGER_NAME in shadowed:
        return [], set()
    confirmed_names -= shadowed
    return [(n, t) for n, t in confirmed_defs if t.id in confirmed_names], confirmed_names
def _iter_confirmed_def_candidates(
    tree: ast.AST,
    def_line_nos: set[int],
    replaced_names: set[str],
    class_body_ids: set[int],
    logging_aliases: set[str],
    bare_getlogger_names: set[str],
):
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        target = _assign_target_name(node)
        if _is_confirmed_def_candidate(
                node, target, def_line_nos, class_body_ids, replaced_names,
                logging_aliases, bare_getlogger_names):
            yield node, target

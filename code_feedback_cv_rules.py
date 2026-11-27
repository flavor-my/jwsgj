from __future__ import annotations

import ast
import io
import itertools
import math
import os
import re
import time
import tokenize
from collections.abc import Callable, Generator
from dataclasses import dataclass, replace
from typing import Any

from jwsgj.diag_guard_io import (
    archive_backup,
    atomic_write_text,
    detect_newline,
    format_diff_preview,
    resolve_within_root,
    verify_syntax,
)
from jwsgj.diag_guard_state import (
    rollback_note,
)
from jwsgj.diag_shared_source_core import byte_col_to_char_col
from jwsgj.diag_types_defs import FeedbackModification
from jwsgj.diag_types_normalize import safe_float, safe_short_text
from jwsgj.diag_types_vocab import (
    DEFAULT_CONFIDENCE_FALLBACK,
    FMT_DATETIME,
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.runtime_scope import normalize_skill_dir
from jwsgj.testsuite_runner import regression_test_candidates, run_pytest_regression

logger = get_module_logger(__name__)
__all__ = [
    'CV_RULE_TARGETS',
    'CVRuleModifier',
    'cv_rule_registry',
]
_EVAL_ERRORS = PARSE_DEGRADE_EXC
def cv_rule_registry(targets: dict | None) -> dict:
    return targets if isinstance(targets, dict) else CV_RULE_TARGETS
def _copy_targets(registry: dict) -> dict:
    return {name: dict(target) if isinstance(target, dict) else target
            for name, target in registry.items()}
def _prepare_targets(
        skill_dir: str,
        registry_of: Callable[[dict | None], dict],
        targets: dict | None,
) -> tuple[str, dict]:
    return normalize_skill_dir(skill_dir), _copy_targets(registry_of(targets))
_BRACKET_DIRECTIONS = {"(": 1, "[": 1, "{": 1,
                       ")": -1, "]": -1, "}": -1}
_VALUE_STOP_CHARS = ",#\n\r"
_MAX_VALUE_DEPTH = 64
def _find_def_line(lines: list[str], name: str) -> int | None:
    pattern = re.compile(
        rf'^\ufeff?{re.escape(name)}\s*(?:=(?!=)|:(?!=))')
    bare_annotation = re.compile(
        rf'^\ufeff?{re.escape(name)}\s*:(?!=)')
    last_any = None
    last_value = None
    for i, line in enumerate(lines):
        if pattern.match(line) is None:
            continue
        last_any = i
        if (bare_annotation.match(line) is not None
                and "=" not in _strip_line_comment(line)):
            continue
        last_value = i
    return last_value if last_value is not None else last_any
def _strip_line_comment(line: str) -> str:
    in_str: str | None = None
    triple = False
    i = 0
    n = len(line)
    while i < n:
        if in_str:
            i, closed = _string_step(line, i, in_str, triple)
            if closed:
                in_str = None
                triple = False
            continue
        span = _quote_span(line, i)
        if span:
            in_str = line[i]
            triple = span == 3
            i += span
            continue
        if line[i] == "#":
            return line[:i]
        i += 1
    return line
def _coerce_entry_literal(entry: Any) -> Any:
    if not isinstance(entry, str):
        return entry
    try:
        return ast.literal_eval(entry)
    except _EVAL_ERRORS:
        return entry
def _entry_source_text(entry: Any) -> str:
    if isinstance(entry, str):
        try:
            node = ast.parse(entry.strip(), mode="eval")
        except (SyntaxError, ValueError):
            return repr(entry)
        if isinstance(node.body, ast.Tuple):
            return f"({entry})"
        if not isinstance(node.body, (ast.Name, ast.Attribute)):
            return entry
    return repr(entry)
def _module_literal_assignment(
        tree: ast.Module,
        name: str) -> tuple[ast.stmt | None, ast.AST | None]:
    for node in reversed(tree.body):
        if isinstance(node, ast.Assign):
            targets, value = node.targets, node.value
        elif isinstance(node, ast.AnnAssign):
            if node.value is None:
                continue
            targets, value = [node.target], node.value
        else:
            continue
        if any(isinstance(t, ast.Name) and t.id == name for t in targets):
            return node, value
    return None, None
def _eval_module_literal(source: str, name: str):
    try:
        tree = ast.parse(source)
    except _EVAL_ERRORS as _e:
        log_swallowed(__name__, _e, context='eval_module_literal:SyntaxError')
        return None
    value = _module_literal_assignment(tree, name)[1]
    if value is None:
        return None
    try:
        return ast.literal_eval(value)
    except _EVAL_ERRORS as _e:
        log_swallowed(__name__, _e, context='eval_module_literal:ValueError')
        return None
def _normalize_entry_text(text: str) -> str:
    code = " ".join(_strip_line_comment(ln) for ln in text.splitlines())
    code = " ".join(code.split())
    if code.endswith(","):
        code = code[:-1].rstrip()
    return code
def _canonical_entry_shape(text: str) -> str | None:
    code = text.strip()
    if not code:
        return None
    try:
        node = ast.parse(code.strip(), mode="eval")
    except _EVAL_ERRORS as _e:
        log_swallowed(__name__, _e, context='_canonical_entry_shape:SyntaxError')
        return None
    return ast.dump(node)
def _entry_segment_matches(segment: str, entry_shape: str | None,
                           entry_norm: str) -> bool:
    if entry_shape is not None:
        segment_shape = _canonical_entry_shape(segment)
        if segment_shape is not None:
            return segment_shape == entry_shape
    return _normalize_entry_text(segment) == entry_norm
def _list_contains_entry(source: str, target_name: str,
                         entry: object) -> bool:
    parse_source = source.lstrip("\ufeff")
    try:
        tree = ast.parse(parse_source)
    except _EVAL_ERRORS as _e:
        log_swallowed(__name__, _e, context='list_contains_entry:SyntaxError')
        return False
    value_node = _module_literal_assignment(tree, target_name)[1]
    if not isinstance(value_node, ast.List):
        return False
    entry_text = _entry_source_text(entry)
    try:
        old_val = ast.literal_eval(value_node)
    except _EVAL_ERRORS as _e:
        log_swallowed(__name__, _e, context='list_contains_entry:ValueError')
        old_val = None
    if isinstance(old_val, list):
        expected = _coerce_entry_literal(entry)
        return any(actual == expected and type(actual) is type(expected)
                   for actual in old_val)
    entry_shape = _canonical_entry_shape(entry_text)
    entry_norm = _normalize_entry_text(entry_text)
    for element in value_node.elts:
        segment = ast.get_source_segment(parse_source, element)
        if segment is not None and _entry_segment_matches(segment, entry_shape, entry_norm):
            return True
    return False
def _verify_expected_literal(original_content: str,
                             modified_content: str,
                             target_name: str, action: str,
                             entry: object = None,
                             written: dict | None = None) -> str | None:
    if action == "list_append":
        return _check_list_append(
            original_content, modified_content, target_name, entry)
    old_val = _eval_module_literal(original_content, target_name)
    new_val = _eval_module_literal(modified_content, target_name)
    if old_val is None or new_val is None:
        return _check_dict_shape_value(
            original_content, modified_content, target_name, written,
            merge=action == "dict_merge")
    if action == "dict_merge":
        return _check_dict_merge_value(old_val, new_val, target_name, written)
    if action == "dict_modify":
        return _check_dict_modify_value(old_val, new_val, target_name, written)
    return None
def _mismatch_reason(target_name: str, actual, expected, hint: str) -> str:
    return (f"语义校验失败: {target_name} 写盘值 {str(actual)[:120]} "
            f"与期望 {str(expected)[:120]} 不符（{hint}），拒绝写盘")
def _list_element_shapes(source: str, target_name: str) -> list[str] | None:
    try:
        tree = ast.parse(source.lstrip("\ufeff"))
    except _EVAL_ERRORS as _e:
        log_swallowed(
            __name__, _e, context='_list_element_shapes:SyntaxError')
        return None
    value_node = _module_literal_assignment(tree, target_name)[1]
    if not isinstance(value_node, ast.List):
        return None
    return [ast.dump(ast.Expression(element)) for element in value_node.elts]
def _dict_value_key_token(key: Any) -> tuple[str, Any] | None:
    try:
        hash(key)
    except (TypeError, RecursionError):
        return None
    return "value", key
def _dict_node_key_token(key: ast.AST) -> tuple[str, Any] | None:
    try:
        value = ast.literal_eval(key)
    except _EVAL_ERRORS:
        return "shape", ast.dump(ast.Expression(key))
    return _dict_value_key_token(value)
def _dict_shape_map(
        source: str, target_name: str,
) -> dict[tuple[str, Any], str] | None:
    try:
        tree = ast.parse(source.lstrip("\ufeff"))
    except _EVAL_ERRORS as _e:
        log_swallowed(
            __name__, _e, context='_dict_shape_map:SyntaxError')
        return None
    value_node = _module_literal_assignment(tree, target_name)[1]
    if not isinstance(value_node, ast.Dict):
        return None
    shapes: dict[tuple[str, Any], str] = {}
    for key, value in zip(value_node.keys, value_node.values):
        if key is None:
            return None
        key_token = _dict_node_key_token(key)
        if key_token is None:
            return None
        shapes[key_token] = ast.dump(ast.Expression(value))
    return shapes
def _check_list_append(original_content: str, modified_content: str,
                       target_name: str, entry: object) -> str | None:
    entry_shape = _canonical_entry_shape(_entry_source_text(entry))
    old_shapes = _list_element_shapes(original_content, target_name)
    new_shapes = _list_element_shapes(modified_content, target_name)
    if (entry_shape is not None and old_shapes is not None
            and new_shapes is not None):
        expected = [*old_shapes, entry_shape]
        if new_shapes == expected:
            return None
        return _mismatch_reason(
            target_name, new_shapes, expected,
            "列表追加写盘内容与条目源码形态不一致（疑似被转义为字符串）")
    return _check_list_append_value(
        _eval_module_literal(original_content, target_name),
        _eval_module_literal(modified_content, target_name),
        target_name, entry)
def _check_list_append_value(old_val, new_val, target_name: str,
                             entry: object) -> str | None:
    if not isinstance(old_val, list) or not isinstance(new_val, list):
        return None
    entry_val = _coerce_entry_literal(entry)
    if isinstance(entry, str) and entry_val is entry:
        return None
    expected = old_val + [entry_val]
    if new_val == expected:
        return None
    return _mismatch_reason(
        target_name, new_val, expected, "疑似隐式拼接/误入嵌套容器的静默损坏")
def _updated_expected_dict(old_val: dict, delta: dict | None) -> dict:
    expected = dict(old_val)
    expected.update(delta or {})
    return expected
def _check_dict_merge_value(old_val, new_val, target_name: str,
                            written: dict | None) -> str | None:
    if not isinstance(old_val, dict) or not isinstance(new_val, dict):
        return None
    expected = _updated_expected_dict(old_val, written)
    if new_val == expected:
        return None
    return _mismatch_reason(target_name, new_val, expected, "疑似静默损坏")
def _check_dict_modify_value(old_val, new_val, target_name: str,
                             written: dict | None) -> str | None:
    if not isinstance(old_val, dict) or not isinstance(new_val, dict):
        return None
    delta = written or {}
    expected = _updated_expected_dict(old_val, delta)
    missing = [str(k) for k in delta if k not in old_val]
    if missing:
        return _mismatch_reason(
            target_name, new_val, expected,
            f"目标键在写入前不存在（键位定位错误: {', '.join(missing)}）")
    if new_val == expected:
        return None
    return _mismatch_reason(
        target_name, new_val, expected,
        "疑似嵌套同名键/错位替换的静默损坏")
def _check_dict_shape_value(original_content: str, modified_content: str,
                            target_name: str, written: dict | None,
                            merge: bool) -> str | None:
    old_shapes = _dict_shape_map(original_content, target_name)
    new_shapes = _dict_shape_map(modified_content, target_name)
    if old_shapes is None or new_shapes is None:
        return (f"语义校验失败: {target_name} 含动态字典展开或不可解析键，"
                "无法证明写盘等价，拒绝写盘")
    if not written:
        return f"语义校验失败: {target_name} 缺少写入键值审计，拒绝写盘"
    expected = dict(old_shapes)
    missing: list[str] = []
    for key, value in written.items():
        key_shape = _dict_value_key_token(key)
        value_shape = _canonical_entry_shape(repr(value))
        if key_shape is None or value_shape is None:
            return None
        if merge:
            if key_shape in old_shapes:
                return _mismatch_reason(
                    target_name, new_shapes, expected,
                    f"待合键已存在却仍被写入（幂等守卫失效: {key_shape}）")
        elif key_shape not in old_shapes:
            missing.append(str(key))
        expected[key_shape] = value_shape
    if missing:
        return _mismatch_reason(
            target_name, new_shapes, expected,
            f"目标键在写入前不存在（键位定位错误: {', '.join(missing)}）")
    if new_shapes == expected:
        return None
    return _mismatch_reason(
        target_name, new_shapes, expected,
        "疑似嵌套同名键/错位替换的静默损坏")
_STRING_KEY_PREFIX_RE = re.compile(
    r"(?P<literal>'(?:\\.|[^'\\])*'|\"(?:\\.|[^\"\\])*\")\s*:\s*"
)
def _key_prefix_match(line: str, key: str,
                      start_col: int | None = None) -> re.Match | None:
    if start_col is None:
        matches = _STRING_KEY_PREFIX_RE.finditer(line)
    else:
        match = _STRING_KEY_PREFIX_RE.match(line, start_col)
        matches = () if match is None else (match,)
    for match in matches:
        try:
            actual = ast.literal_eval(match.group("literal"))
        except _EVAL_ERRORS:
            continue
        if actual == key:
            return match
    return None
def _find_dict_key_site(lines: list[str], dict_name: str,
                        key: str) -> tuple[int, int] | None:
    span = _find_container_span(lines, dict_name, "{")
    if span is None:
        return None
    dict_start, open_line, open_col, dict_end = span
    regions: dict[int, list[int]] = {}
    for line_no, col in _top_level_regions(
            lines, open_line, open_col, dict_end):
        regions.setdefault(line_no, []).append(col)
    string_intervals = _string_intervals_by_line(
        lines, open_line, open_col, dict_end)
    for i in range(dict_start, min(dict_end + 1, len(lines))):
        cols = regions.get(i)
        if not cols:
            continue
        code_part = _strip_line_comment(lines[i])
        for col in sorted(cols):
            match = _key_prefix_match(code_part, key, start_col=col)
            if match is None:
                continue
            if any(start <= match.start() < end
                   for start, end in string_intervals.get(i, ())):
                continue
            return i, match.start()
    return None
def _string_intervals_by_line(
        lines: list[str], open_line: int, open_col: int,
        close_idx: int) -> dict[int, list[tuple[int, int]]]:
    intervals: dict[int, list[tuple[int, int]]] = {}
    opened: tuple[int, int] | None = None
    for kind, i, j, _ch, quote_span in _quote_aware_events(
            lines, open_line, open_col, close_idx):
        if kind == "str_start":
            opened = (i, j + quote_span)
            continue
        if kind != "str_end" or opened is None:
            continue
        start_line, start_col = opened
        if start_line == i:
            intervals.setdefault(i, []).append((start_col, j))
        else:
            intervals.setdefault(start_line, []).append(
                (start_col, len(lines[start_line])))
            for k in range(start_line + 1, i):
                intervals.setdefault(k, []).append((0, len(lines[k])))
            intervals.setdefault(i, []).append((0, j))
        opened = None
    return intervals
def _quote_span(line: str, col: int) -> int:
    ch = line[col]
    if ch not in "\"'":
        return 0
    return 3 if line.startswith(ch * 3, col) else 1
def _string_step(line: str, col: int, quote: str, triple: bool) -> tuple:
    if line[col] == "\\":
        return col + 2, 0
    if triple:
        return ((col + 3, 3) if line.startswith(quote * 3, col)
                else (col + 1, 0))
    if line[col] == quote:
        return col + 1, 1
    return col + 1, 0
def _iter_lex_units(lines: list[str], open_line: int, open_col: int,
                    close_idx: int) -> Generator[tuple, None, None]:
    start = _first_container_bracket(lines, open_line, open_col, close_idx)
    if start is None:
        return
    in_str: str | None = None
    triple = False
    for i in range(start[0], close_idx + 1):
        line = lines[i]
        j = start[1] if i == start[0] else 0
        n = len(line)
        while j < n:
            ch = line[j]
            if in_str:
                j, closed = _string_step(line, j, in_str, triple)
                if closed:
                    yield ("str_end", i, j - closed, in_str, closed)
                    in_str = None
                    triple = False
                continue
            if ch == "#":
                j = n
                continue
            span = _quote_span(line, j)
            if span:
                yield ("str_start", i, j, ch, span)
                in_str = ch
                triple = span == 3
                j += span
                continue
            direction = _BRACKET_DIRECTIONS.get(ch)
            if direction is not None:
                yield ("bracket", i, j, ch, direction)
                j += 1
                continue
            yield ("char", i, j, ch, 0)
            j += 1
def _quote_aware_events(lines: list[str], open_line: int,
                        open_col: int, close_idx: int) -> Generator[tuple, None, None]:
    depth = 0
    for kind, i, j, ch, extra in _iter_lex_units(
            lines, open_line, open_col, close_idx):
        if kind == "bracket":
            if extra > 0:
                depth += 1
                yield ("open", i, j, ch, depth)
                continue
            event, depth, stop = _closing_event(i, j, ch, depth)
            yield event
            if stop:
                return
            continue
        if kind == "char":
            yield (kind, i, j, ch, depth)
            continue
        yield (kind, i, j, ch, extra)
def _scan_bracket_close(lines: list[str], start_line: int,
                        start_col: int,
                        end_line: int | None = None) -> int | None:
    if not lines:
        return None
    end = len(lines) - 1 if end_line is None else min(end_line, len(lines) - 1)
    for kind, i, _j, _c, _d in _quote_aware_events(lines, start_line, start_col, end):
        if kind == "container_close":
            return i
    return None
def _container_span_from_ast(
        lines: list[str], name: str,
        open_char: str) -> tuple[bool, tuple[int, int, int, int] | None]:
    source = "".join(lines)
    bom_bytes = 0
    if source.startswith("\ufeff"):
        source = source[1:]
        bom_bytes = len("\ufeff".encode("utf-8"))
    try:
        tree = ast.parse(source)
    except _EVAL_ERRORS as _e:
        log_swallowed(
            __name__, _e, context='_find_container_span:SyntaxError')
        return False, None
    stmt, value = _module_literal_assignment(tree, name)
    expected = ast.Dict if open_char == "{" else ast.List
    if stmt is None or not isinstance(value, expected):
        return True, None
    start_line = value.lineno - 1
    start_col = byte_col_to_char_col(
        lines[start_line],
        value.col_offset + (bom_bytes if start_line == 0 else 0))
    close_idx = _scan_bracket_close(
        lines, start_line, start_col, value.end_lineno - 1)
    if close_idx != value.end_lineno - 1:
        return True, None
    return True, (stmt.lineno - 1, start_line, start_col, close_idx)
def _next_container_open(lines: list[str], def_line: int,
                        open_char: str) -> tuple[int, int] | None:
    for i in range(def_line + 1, len(lines)):
        code = _strip_line_comment(lines[i])
        stripped = code.lstrip()
        if not stripped:
            continue
        if stripped[0] != open_char:
            return None
        return i, len(code) - len(stripped)
    return None
def _find_container_span_by_lines(
        lines: list[str], name: str,
        open_char: str) -> tuple[int, int, int, int] | None:
    def_line = _find_def_line(lines, name)
    if def_line is None:
        return None
    code = _strip_line_comment(lines[def_line])
    eq_pos = _assignment_eq_index(code)
    if eq_pos is not None:
        tail = code[eq_pos + 1:]
        body = tail.lstrip()
        if body.startswith(open_char):
            start_line = def_line
            start_col = eq_pos + 1 + (len(tail) - len(body))
        else:
            site = _next_container_open(lines, def_line, open_char)
            if site is None:
                return None
            start_line, start_col = site
    else:
        site = _next_container_open(lines, def_line, open_char)
        if site is None:
            return None
        start_line, start_col = site
    close_idx = _scan_bracket_close(lines, start_line, start_col)
    if close_idx is None:
        return None
    return def_line, start_line, start_col, close_idx
def _find_container_span(lines: list[str], name: str,
                         open_char: str) -> tuple[int, int, int, int] | None:
    parsed, span = _container_span_from_ast(lines, name, open_char)
    if parsed:
        return span
    return _find_container_span_by_lines(lines, name, open_char)
def _first_container_bracket(lines: list[str], open_line: int,
                            open_col: int, close_idx: int
                            ) -> tuple[int, int] | None:
    for i in range(open_line, close_idx + 1):
        line = lines[i]
        start = open_col if i == open_line else 0
        for j in range(start, len(line)):
            if line[j] in "([{":
                return i, j + 1
    return None
def _closing_event(i: int, j: int, ch: str,
                   depth: int) -> tuple[tuple, int, bool]:
    if depth == 0:
        return ("container_close", i, j, ch, 0), depth, True
    return ("close", i, j, ch, depth - 1), depth - 1, False
def _top_level_regions(lines: list[str], open_line: int,
                       open_col: int, close_idx: int) -> list[tuple[int, int]]:
    regions: list[tuple[int, int]] = []
    depth = 0
    elem_open = True
    for event in _quote_aware_events(
            lines, open_line, open_col, close_idx):
        depth, elem_open, start, stop = _region_step(
            *event, depth=depth, elem_open=elem_open)
        if start is not None:
            regions.append(start)
        if stop:
            break
    return regions
def _region_open_step(kind: str, i: int, j: int, depth: int,
                      elem_open: bool) -> tuple[int, bool, tuple[int, int] | None]:
    new_depth = depth + 1 if kind == "open" else depth
    if depth == 0 and elem_open:
        return new_depth, False, (i, j)
    return new_depth, elem_open, None
def _region_char_step(i: int, j: int, ch: str, depth: int,
                      elem_open: bool) -> tuple[bool, tuple[int, int] | None]:
    if depth != 0:
        return elem_open, None
    if ch == ",":
        return True, None
    if elem_open and not ch.isspace():
        return False, (i, j)
    return elem_open, None
def _region_step(kind: str, i: int, j: int, ch: str, _quote_span: int,
                 depth: int, elem_open: bool
                 ) -> tuple[int, bool, tuple[int, int] | None, bool]:
    if kind in ("open", "str_start"):
        depth, elem_open, start = _region_open_step(
            kind, i, j, depth, elem_open)
        return depth, elem_open, start, False
    if kind == "close":
        return depth - 1, elem_open, None, False
    if kind == "container_close":
        return depth, elem_open, None, True
    if kind == "char":
        elem_open, start = _region_char_step(i, j, ch, depth, elem_open)
        return depth, elem_open, start, False
    return depth, elem_open, None, False
def _scan_last_item_end(lines: list[str], open_line: int,
                         open_col: int, close_idx: int) -> tuple[int, int] | None:
    depth = 0
    last: tuple[int, int] | None = None
    for event in _quote_aware_events(
            lines, open_line, open_col, close_idx):
        depth, end, stop = _item_end_step(*event, depth=depth)
        if end is not None:
            last = end
        if stop:
            break
    return last
def _item_end_step(kind: str, i: int, j: int, ch: str, span: int,
                   depth: int) -> tuple[int, tuple[int, int] | None, bool]:
    if kind == "str_end":
        return depth, ((i, j + span) if depth == 0 else None), False
    if kind == "open":
        return depth + 1, None, False
    if kind == "close":
        new_depth = depth - 1
        return new_depth, ((i, j + 1) if new_depth == 0 else None), False
    if kind == "container_close":
        return depth, None, True
    if kind == "char":
        end = (i, j + 1) if depth == 0 and not ch.isspace() else None
        return depth, end, False
    return depth, None, False
def _ensure_trailing_comma(lines: list[str], open_line: int,
                           open_col: int, close_idx: int) -> list[str]:
    found = _scan_last_item_end(
        lines, open_line, open_col, close_idx)
    if found is None or found[0] >= close_idx:
        return lines
    last_line, last_end = found
    if lines[last_line][last_end - 1] == ",":
        return lines
    fixed = (lines[last_line][:last_end] + ","
             + lines[last_line][last_end:])
    return [*lines[:last_line], fixed, *lines[last_line + 1:]]
def _extract_dict_value(line: str, key: str,
                        start_col: int | None) -> str | None:
    match = _key_prefix_match(line, key, start_col=start_col)
    if match is None:
        return None
    rest = line[match.end():]
    end = _scan_value_end(rest)
    value = rest[:end].strip()
    return value or None
def _skip_string_literal(text: str, start: int, quote: str,
                         triple: bool = False) -> int:
    i = start
    while i < len(text):
        i, closed = _string_step(text, i, quote, triple)
        if closed:
            return i
    return i
def _scan_value_end(rest: str) -> int:
    depth = 0
    i = 0
    while i < len(rest):
        ch = rest[i]
        quote_span = _quote_span(rest, i)
        if quote_span:
            i = _skip_string_literal(
                rest, i + quote_span, ch, triple=quote_span == 3)
            continue
        direction = _BRACKET_DIRECTIONS.get(ch)
        if direction is not None:
            depth += direction
            if depth < 0:
                return i
        elif depth == 0 and ch in _VALUE_STOP_CHARS:
            return i
        i += 1
    return 0 if depth > 0 else len(rest)
def _replace_dict_value(line: str, key: str,
                        new_value: Any,
                        original_value: str,
                        start_col: int | None) -> str:
    match = _key_prefix_match(line, key, start_col=start_col)
    if match is None:
        return line
    rest = line[match.end():]
    end = _scan_value_end(rest)
    if end == 0:
        return line
    value_part = rest[:end]
    gap = value_part[len(value_part.rstrip()):]
    tail = rest[end:]
    tail_nl = ''
    while tail.endswith(('\n', '\r')):
        tail_nl = tail[-1] + tail_nl
        tail = tail[:-1]
    note = "" if _has_original_marker(tail) else (
        f"  # [original: {original_value}]")
    return f'{line[:match.end()]}{new_value}{gap}{tail}{note}{tail_nl}'
@dataclass(frozen=True)
class _MergeKey:
    text: str
    pattern: str
    final: Any
def _normalize_merge_key(key: Any, target_name: str) -> _MergeKey:
    if isinstance(key, str) and re.match(r'^\s*\(.*\)\s*$', key):
        try:
            parsed = ast.literal_eval(key)
        except _EVAL_ERRORS as e:
            logger.debug("[L3] tuple 键还原失败，按字符串键处理 %s[%r]: %s",
                         target_name, key, e)
        else:
            if isinstance(parsed, tuple):
                try:
                    hash(parsed)
                except (TypeError, RecursionError) as e:
                    logger.debug(
                        "[L3] tuple 键不可哈希，按字符串键处理 %s[%r]: %s",
                        target_name, key, e)
                else:
                    return _MergeKey(repr(parsed),
                                     rf'{re.escape(repr(parsed))}\s*:', parsed)
    if isinstance(key, str):
        return _MergeKey(repr(key), rf'["\']{re.escape(key)}["\']\s*:', key)
    return _MergeKey(repr(key), rf'{re.escape(repr(key))}\s*:', key)
def _merge_key_exists(key: _MergeKey, old_val, top_regions: list,
                      raw_lines: list) -> bool:
    if isinstance(old_val, dict) and key.final in old_val:
        return True
    if isinstance(key.final, str):
        return any(
            _key_prefix_match(
                raw_lines[line], key.final, start_col=col) is not None
            for line, col in top_regions)
    return any(re.match(key.pattern, raw_lines[region[0]][region[1]:])
               for region in top_regions)
def _collect_merge_lines(entries: dict, target_name: str,
                         old_val, old_shapes: dict | None, top_regions: list,
                         raw_lines: list) -> tuple:
    merge_lines: list = []
    skipped_keys: list = []
    written: dict = {}
    for k, v in entries.items():
        key = _normalize_merge_key(k, target_name)
        key_token = _dict_value_key_token(key.final)
        if ((old_shapes is not None and key_token in old_shapes)
                or _merge_key_exists(key, old_val, top_regions, raw_lines)):
            skipped_keys.append(str(k))
            logger.info("[L3] dict_merge 跳过已存在键 %s[%s]", target_name, k)
            continue
        written[key.final] = v
        merge_lines.append(
            f"    {key.text}: {v!r},  # [auto-injected by feedback]\n"
        )
    return merge_lines, skipped_keys, written
def _insert_after_last_item(lines: list, insert_code: str, open_line: int,
                            open_col: int, list_end: int) -> list:
    last = _scan_last_item_end(lines, open_line, open_col, list_end)
    if last is None or last[0] != list_end:
        return [*lines[:list_end], insert_code, *lines[list_end:]]
    last_end = last[1]
    close_line = lines[list_end]
    head = close_line[:last_end]
    sep = "" if head.rstrip().endswith(",") else ","
    split = head + sep + "\n" + insert_code + close_line[last_end:]
    return [*lines[:list_end], *split.splitlines(True), *lines[list_end + 1:]]
def _find_nonfinite(value: Any, path: str) -> str | None:
    stack: list[tuple[str, Any]] = [(path, value)]
    visited: set[int] = set()
    while stack:
        cur_path, node = stack.pop()
        if isinstance(node, float):
            if not math.isfinite(node):
                return cur_path or "value"
            continue
        if isinstance(node, complex):
            if not (math.isfinite(node.real) and math.isfinite(node.imag)):
                return cur_path or "value"
            continue
        if not isinstance(node, (dict, list, tuple, set, frozenset)):
            continue
        identity = id(node)
        if identity in visited:
            continue
        visited.add(identity)
        stack.extend(reversed(list(_container_items(node, cur_path))))
    return None
def _container_items(value: Any, path: str):
    if isinstance(value, dict):
        for k, v in value.items():
            key_path = f"{path}.{k}" if path else str(k)
            yield key_path, v
            yield f"{key_path}<key>", k
    elif isinstance(value, (list, tuple, set, frozenset)):
        for i, v in enumerate(value):
            yield f"{path}[{i}]", v
def _child_values(value: Any):
    if isinstance(value, dict):
        yield from value.keys()
        yield from value.values()
    elif isinstance(value, (list, tuple, set, frozenset)):
        yield from value
def _value_too_deep(value: Any, limit: int = _MAX_VALUE_DEPTH) -> bool:
    stack: list[tuple[Any, int, bool]] = [(value, 1, False)]
    active: set[int] = set()
    visited_depths: dict[int, int] = {}
    while stack:
        node, depth, exiting = stack.pop()
        if depth > limit:
            return True
        if not isinstance(node, (dict, list, tuple, set, frozenset)):
            continue
        identity = id(node)
        if exiting:
            active.remove(identity)
            previous = visited_depths.get(identity)
            if previous is None or depth < previous:
                visited_depths[identity] = depth
            continue
        if identity in active:
            return True
        previous = visited_depths.get(identity)
        if previous is not None and depth <= previous:
            continue
        active.add(identity)
        stack.append((node, depth, True))
        stack.extend((child, depth + 1, False)
                     for child in _child_values(node))
    return False
_LITERAL_SCALAR_TYPES = frozenset({
    type(None), bool, int, float, complex, str, bytes, type(...),
})
_LITERAL_CONTAINER_TYPES = frozenset({dict, list, tuple, set, frozenset})
def _find_unserializable_type(value: Any, path: str) -> tuple[str, type] | None:
    stack: list[tuple[str, Any]] = [(path, value)]
    visited: set[int] = set()
    while stack:
        cur_path, node = stack.pop()
        node_type = type(node)
        if node_type in _LITERAL_SCALAR_TYPES:
            continue
        if node_type not in _LITERAL_CONTAINER_TYPES:
            return cur_path or "value", node_type
        identity = id(node)
        if identity in visited:
            continue
        visited.add(identity)
        stack.extend(reversed(list(_container_items(node, cur_path))))
    return None
def _value_repr_error(value: Any) -> str | None:
    try:
        repr(value)
    except Exception as exc:  # noqa: BLE001 — 任意用户对象的 repr 均可能失败
        log_swallowed(__name__, exc, context='_value_repr_error:repr')
        return f"{type(value).__name__}: {exc}"
    return None
def _value_guard_error(value: Any, path: str = "") -> str | None:
    if _value_too_deep(value):
        return f"嵌套层级超过上限({_MAX_VALUE_DEPTH})"
    hit = _find_nonfinite(value, path)
    if hit is not None:
        return f"含非有限数值（{hit}）"
    unserializable = _find_unserializable_type(value, path)
    if unserializable is not None:
        hit_path, node_type = unserializable
        return f"含不可安全序列化类型（{hit_path}: {node_type.__name__}）"
    repr_error = _value_repr_error(value)
    if repr_error is not None:
        return f"无法安全序列化（{repr_error}）"
    return None
def _target_file_field(target: dict | None) -> str:
    target_file = target.get("file") if target is not None else None
    return target_file if isinstance(target_file, str) and target_file else ""
def _type_field(value: Any) -> str:
    return value if isinstance(value, str) else ""
def _target_type(target: Any) -> str:
    return _type_field(target.get("type") if isinstance(target, dict) else None)
def _l3_fail(mod_id: str, target: dict | None, target_name: str,
             confidence: float, error_message: str,
             **audit: Any) -> FeedbackModification:
    kwargs: dict[str, Any] = {
        "modification_id": mod_id, "level": "L3",
        "target_name": target_name, "action_type": "rule_modify",
        "applied": False, "confidence": confidence,
        "error_message": error_message,
    }
    target_file = _target_file_field(target)
    if target_file:
        kwargs["target_file"] = target_file
    kwargs.update(audit)
    return FeedbackModification(**kwargs)
@dataclass(frozen=True)
class _EditTarget:
    skill_dir: str
    file_path: str
    target: dict
    target_name: str
    mod_id: str
    confidence: float
    source_enhancement_id: str
    eol: str
    bom: bool = False
    encoding: str = "utf-8"
@dataclass(frozen=True)
class _WritePlan:
    raw_lines: list
    modified_lines: list
    modified_content: str
    backup_tag: str
    original_value: str
    new_value: str
    tag: str
    success_log: tuple
    action: str = ""
    entry: object = None
    written: dict | None = None
def _reject(ctx: _EditTarget, message: str, **audit: Any) -> FeedbackModification:
    return _l3_fail(ctx.mod_id, ctx.target, ctx.target_name, ctx.confidence,
                    message,
                    source_enhancement_id=ctx.source_enhancement_id,
                    **audit)
def _weight_bounds(target: dict) -> tuple[float, float] | None:
    if "min_weight" not in target or "max_weight" not in target:
        return None
    low = safe_float(target.get("min_weight"), None)
    high = safe_float(target.get("max_weight"), None)
    if low is None or high is None or low > high:
        return None
    return low, high
def _weight_declared(target: dict) -> bool:
    return "min_weight" in target or "max_weight" in target
def _normalize_weight_value(ctx: _EditTarget, value) -> tuple:
    bounds = _weight_bounds(ctx.target)
    if bounds is None:
        return _reject(
            ctx,
            ("目标未注册合法数值修改域(min_weight/max_weight)，"
             f"标量值修改不受支持: {ctx.target_name}")), None
    try:
        numeric = float(value)
    except (TypeError, ValueError, OverflowError) as _conv_err:
        logger.debug("[L3] 权重值 float() 转换异常: %s — %s",
                     safe_short_text(value), _conv_err)
        return _reject(ctx, f"权重值无效: {safe_short_text(value)}"), None
    if not math.isfinite(numeric):
        return _reject(ctx, f"权重值无效: {value}"), None
    low, high = bounds
    return None, max(low, min(high, numeric))
def _normalize_mapping_value(ctx: _EditTarget, value: dict) -> tuple:
    guard = _value_guard_error(value)
    if guard is not None:
        return _reject(ctx, f"new_value {guard}，拒绝写盘"), None
    return None, value
def _normalize_new_value(ctx: _EditTarget, new_value) -> tuple:
    if isinstance(new_value, bool):
        return _reject(
            ctx, f"不支持的值类型: {type(new_value).__name__}"), None
    if _weight_declared(ctx.target):
        if not isinstance(new_value, (int, float)):
            return _reject(
                ctx,
                (f"不支持的值类型: {type(new_value).__name__}"
                 "（标量权重目标只接受数值）")), None
        return _normalize_weight_value(ctx, new_value)
    if isinstance(new_value, dict):
        return _normalize_mapping_value(ctx, new_value)
    return _reject(
        ctx, f"不支持的值类型: {type(new_value).__name__}"), None
def _resolve_container_span(ctx: _EditTarget, raw_lines: list,
                            open_char: str, kind: str) -> tuple:
    span = _find_container_span(raw_lines, ctx.target_name, open_char)
    if span is None:
        return _reject(ctx, f"未找到{kind} {ctx.target_name} 的结束位置"), None
    start, _open_line, _open_col, end = span
    if end == start:
        return _reject(
            ctx,
            f"紧凑单行定义形态暂不支持: {ctx.target_name}（须展开为多行）"), None
    return None, span
def _validate_merge_entries(ctx: _EditTarget, modification: dict) -> tuple:
    entries = modification.get("entries", {})
    if not isinstance(entries, dict):
        return _reject(ctx, f"entries 类型错误: 期望 dict，实际 "
                            f"{type(entries).__name__}"), {}
    if not entries:
        return _reject(ctx, "缺少 entries"), {}
    normalized_keys: dict = {}
    for k, v in entries.items():
        for item in (k, v):
            guard = _value_guard_error(item, safe_short_text(k))
            if guard is not None:
                return _reject(
                    ctx, f"entries 键或值{guard}，拒绝写盘"), {}
        normalized_key = _normalize_merge_key(k, ctx.target_name)
        if normalized_key.final in normalized_keys:
            previous = normalized_keys[normalized_key.final]
            return _reject(
                ctx,
                (f"entries 键规范化后重复: {safe_short_text(previous)} 与 "
                 f"{safe_short_text(k)} -> {normalized_key.text}")), {}
        normalized_keys[normalized_key.final] = k
    return None, entries
def _verify_write_plan(ctx: _EditTarget, original_content: str,
                       plan: _WritePlan) -> tuple:
    fail_reason = _verify_expected_literal(
        original_content, plan.modified_content, ctx.target_name,
        plan.action, entry=plan.entry, written=plan.written)
    if fail_reason:
        return _reject(
            ctx, fail_reason, original_value=plan.original_value,
            new_value=plan.new_value), None
    return None, plan
def _plan_dict_modify(ctx: _EditTarget, original_content: str,
                      modification: dict) -> tuple:
    key_to_modify = modification.get("key", "")
    new_value = modification.get("new_value")
    if not isinstance(key_to_modify, str):
        return _reject(ctx, f"key 类型错误: 期望 str，实际 "
                            f"{type(key_to_modify).__name__}"), None
    if not key_to_modify or new_value is None:
        return _reject(ctx, "缺少 key 或 new_value"), None
    fail_mod, new_value = _normalize_new_value(ctx, new_value)
    if fail_mod is not None:
        return fail_mod, None
    # 值级零变更判定：_replace_dict_value 会追加 # [original: ...] 注释，
    # 使 new_line != original_line，仅靠行比对无法识别“同值重放”，会把
    # 未改动值的写入误报为 applied。此处按字典实际值比对，与 L1 的
    # _build_edited_source 零变更口径对齐。
    old_val = _eval_module_literal(original_content, ctx.target_name)
    if (isinstance(old_val, dict) and key_to_modify in old_val
            and old_val[key_to_modify] == new_value):
        return _reject(
            ctx,
            f"幂等重放: {ctx.target_name}[{key_to_modify}] "
            f"磁盘值已是 {new_value}，无变化",
            original_value=str(old_val[key_to_modify]),
            new_value=str(new_value)), None
    lines = original_content.splitlines(True)
    site = _find_dict_key_site(lines, ctx.target_name, key_to_modify)
    if site is None:
        return _reject(ctx, f"未找到 {ctx.target_name}[{key_to_modify}]"), None
    target_line_idx, key_col = site
    original_line = lines[target_line_idx]
    original_value_str = _extract_dict_value(
        original_line, key_to_modify, start_col=key_col) or "unknown"
    new_line = _replace_dict_value(
        original_line, key_to_modify, new_value, original_value_str,
        start_col=key_col)
    if new_line == original_line:
        if (_has_original_marker(original_line)
                and str(new_value) in original_line):
            return _reject(
                ctx,
                f"幂等重放: {ctx.target_name}[{key_to_modify}] "
                f"磁盘值已是 {new_value}，无变化",
                original_value=original_value_str,
                new_value=str(new_value)), None
        return _reject(
            ctx,
            (f"值行替换未生效: {ctx.target_name}[{key_to_modify}] "
             "的值不在键所在行（多行值形态暂不支持）"),
            original_value=original_value_str,
            new_value=str(new_value)), None
    modified_lines = lines.copy()
    modified_lines[target_line_idx] = new_line
    modified_content = "".join(modified_lines)
    plan = _WritePlan(
        raw_lines=lines, modified_lines=modified_lines,
        modified_content=modified_content, backup_tag="L3",
        original_value=original_value_str, new_value=str(new_value),
        tag="_modify_dict_value",
        success_log=("[L3] CV规则修改成功: %s[%s]: %s → %s",
                     ctx.target_name, key_to_modify, original_value_str,
                     new_value),
        action="dict_modify", written={key_to_modify: new_value})
    return _verify_write_plan(ctx, original_content, plan)
def _is_conflict_family_expr(node: ast.AST, _iterable: bool = False) -> bool:
    if isinstance(node, ast.Name):
        return True
    if isinstance(node, ast.Set) or (
            _iterable and isinstance(node, (ast.List, ast.Tuple))):
        return all(isinstance(item, ast.Constant)
                   and isinstance(item.value, str) for item in node.elts)
    if isinstance(node, ast.BinOp):
        return (isinstance(node.op, (ast.BitOr, ast.Sub))
                and _is_conflict_family_expr(node.left)
                and _is_conflict_family_expr(node.right))
    if isinstance(node, ast.Call):
        return (isinstance(node.func, ast.Name) and node.func.id == "frozenset"
                and not node.keywords and len(node.args) <= 1
                and (not node.args
                     or _is_conflict_family_expr(node.args[0], _iterable=True)
                     or (isinstance(node.args[0], ast.Constant)
                         and isinstance(node.args[0].value, str))))
    return False
def _list_entry_contract_error(ctx: _EditTarget, entry: object) -> str | None:
    if ctx.target_name != "CONFLICTING_PAIRS":
        return None
    try:
        node = ast.parse(_entry_source_text(entry).strip(), mode="eval")
    except _EVAL_ERRORS as exc:
        log_swallowed(__name__, exc, context="list_entry_contract:parse")
        return "CONFLICTING_PAIRS entry 不是可解析的 Python 表达式"
    items = node.body.elts if isinstance(node.body, ast.Tuple) else ()
    if (len(items) != 3 or any(isinstance(item, ast.Starred) for item in items)
            or not isinstance(items[2], ast.Constant)
            or not isinstance(items[2].value, str)):
        return ("CONFLICTING_PAIRS entry 必须是三项元组（三元组），"
                "且第三项为字符串")
    if not all(_is_conflict_family_expr(item) for item in items[:2]):
        return ("CONFLICTING_PAIRS entry 前两项必须是集合表达式"
                "（命名常量、集合字面量、frozenset 或集合差集/并集），"
                "不得包含任意函数调用")
    return None
def _plan_list_append(ctx: _EditTarget, original_content: str,
                      modification: dict) -> tuple:
    entry = modification.get("entry")
    if entry is None:
        return _reject(ctx, "缺少 entry"), None
    contract_error = _list_entry_contract_error(ctx, entry)
    if contract_error is not None:
        return _reject(ctx, contract_error), None
    guard = _value_guard_error(entry, "entry")
    if guard is not None:
        return _reject(ctx, f"entry {guard}，拒绝写盘"), None
    raw_lines = original_content.splitlines(True)
    fail_mod, span = _resolve_container_span(ctx, raw_lines, "[", "列表")
    if fail_mod is not None:
        return fail_mod, None
    _list_start, open_line, open_col, list_end = span
    if _list_contains_entry(original_content, ctx.target_name, entry):
        return _reject(
            ctx, f"列表 {ctx.target_name} 已含相同条目，跳过重复追加"), None
    lines = _ensure_trailing_comma(raw_lines, open_line, open_col, list_end)
    insert_code = (
        f"    {_entry_source_text(entry)},  # [auto-injected by feedback]\n")
    modified_lines = _insert_after_last_item(
        lines, insert_code, open_line, open_col, list_end)
    modified_content = "".join(modified_lines)
    plan = _WritePlan(
        raw_lines=raw_lines, modified_lines=modified_lines,
        modified_content=modified_content, backup_tag="L3-list",
        original_value="list_append", new_value=str(entry)[:100],
        tag="_append_to_list",
        success_log=("[L3] CV规则列表追加成功: %s", ctx.target_name),
        action="list_append", entry=entry)
    return _verify_write_plan(ctx, original_content, plan)
def _plan_dict_merge(ctx: _EditTarget, original_content: str,
                     modification: dict) -> tuple:
    fail_mod, entries = _validate_merge_entries(ctx, modification)
    if fail_mod is not None:
        return fail_mod, None
    raw_lines = original_content.splitlines(True)
    fail_mod, span = _resolve_container_span(ctx, raw_lines, "{", "字典")
    if fail_mod is not None:
        return fail_mod, None
    _dict_start, open_line, open_col, dict_end = span
    top_regions = _top_level_regions(raw_lines, open_line, open_col, dict_end)
    old_val = _eval_module_literal(original_content, ctx.target_name)
    old_shapes = _dict_shape_map(original_content, ctx.target_name)
    merge_lines, skipped_keys, written = _collect_merge_lines(
        entries, ctx.target_name, old_val, old_shapes, top_regions, raw_lines)
    merge_code = "".join(merge_lines)
    if not merge_code:
        return _reject(
            ctx, "待合并键全部已存在（应走 dict_modify 更新通道）: "
                 f"{ctx.target_name}[{', '.join(skipped_keys[:5])}]",
            original_value="dict_merge",
            new_value=str(entries)[:100]), None
    lines = _ensure_trailing_comma(raw_lines, open_line, open_col, dict_end)
    modified_lines = _insert_after_last_item(
        lines, merge_code, open_line, open_col, dict_end)
    modified_content = "".join(modified_lines)
    plan = _WritePlan(
        raw_lines=raw_lines, modified_lines=modified_lines,
        modified_content=modified_content, backup_tag="L3-dict",
        original_value="dict_merge", new_value=str(entries)[:100],
        tag="_merge_to_dict",
        success_log=("[L3] CV规则字典合并成功: %s, %d entries",
                     ctx.target_name, len(written)),
        action="dict_merge", written=written)
    return _verify_write_plan(ctx, original_content, plan)
def _load_edit_target(ctx: _EditTarget) -> tuple:
    if not os.path.isfile(ctx.file_path):
        return _reject(ctx, f"文件不存在: {ctx.file_path}"), None, None
    try:
        raw_content, encoding = _read_source_with_encoding(ctx.file_path)
    except (OSError, UnicodeDecodeError, LookupError, SyntaxError) as e:
        log_swallowed(__name__, e, context='CVRuleModifier.modify:OSError')
        return _reject(ctx, f"文件读取失败: {e}"), None, None
    has_bom = raw_content.startswith("\ufeff")
    text = raw_content[1:] if has_bom else raw_content
    ctx = replace(ctx, eol=detect_newline(text), bom=has_bom,
                  encoding=encoding)
    return None, ctx, text.replace("\r\n", "\n")
@dataclass(frozen=True)
class _WriteAttempt:
    ctx: _EditTarget
    plan: _WritePlan
    backup_path: str
    diff_preview: str
def _write_fail(attempt: _WriteAttempt, message: str,
                **flags: Any) -> FeedbackModification:
    ctx, plan = attempt.ctx, attempt.plan
    return _l3_fail(
        ctx.mod_id, ctx.target, ctx.target_name, ctx.confidence, message,
        source_enhancement_id=ctx.source_enhancement_id,
        original_value=plan.original_value, new_value=plan.new_value,
        diff_preview=attempt.diff_preview, backup_path=attempt.backup_path,
        **flags)
def _precheck_content(attempt: _WriteAttempt) -> FeedbackModification | None:
    ctx, plan = attempt.ctx, attempt.plan
    try:
        compile(plan.modified_content, ctx.file_path, "exec")
    except (SyntaxError, ValueError, MemoryError, RecursionError) as e:
        log_swallowed(__name__, e, context='CVRuleModifier._write_and_finalize:SyntaxError')
        return _write_fail(
            attempt, f"写盘前语法预检失败（磁盘未修改）: {e}",
            syntax_valid=False, regression_passed=False)
    return None
def _commit_content(attempt: _WriteAttempt) -> FeedbackModification | None:
    ctx, plan, backup_path = attempt.ctx, attempt.plan, attempt.backup_path
    payload = (("\ufeff" if ctx.bom else "")
               + plan.modified_content.replace("\n", ctx.eol))
    try:
        atomic_write_text(ctx.file_path, payload, tag=plan.backup_tag,
                          newline="", encoding=ctx.encoding)
    except Exception as e:  # noqa: BLE001 — 写盘异常统一回滚
        log_swallowed(__name__, e, context='CVRuleModifier._write_and_finalize:Exc')
        return _write_fail(
            attempt,
            f"写入失败: {e}{rollback_note(ctx.file_path, backup_path, plan.tag)}")
    return None
def _verify_and_finalize(attempt: _WriteAttempt,
                         run_regression: Callable[[], tuple]) -> FeedbackModification:
    ctx, plan = attempt.ctx, attempt.plan
    backup_path, diff_preview = attempt.backup_path, attempt.diff_preview
    syntax_valid = verify_syntax(ctx.file_path, tag="[L3]")
    if not syntax_valid:
        return _write_fail(
            attempt,
            f"语法验证失败{rollback_note(ctx.file_path, backup_path, plan.tag)}",
            syntax_valid=False,
            regression_passed=False)
    regression_passed, _regression_output = run_regression()
    if not regression_passed:
        return _write_fail(
            attempt,
            f"回归测试失败{rollback_note(ctx.file_path, backup_path, plan.tag)}",
            syntax_valid=True, regression_passed=False)
    return FeedbackModification(
        modification_id=ctx.mod_id, level="L3",
        target_file=ctx.target["file"],
        target_name=ctx.target_name,
        action_type="rule_modify",
        original_value=plan.original_value,
        new_value=plan.new_value,
        diff_preview=diff_preview,
        syntax_valid=syntax_valid,
        regression_passed=regression_passed,
        backup_path=backup_path,
        applied=True,
        timestamp=time.strftime(FMT_DATETIME),
        confidence=ctx.confidence,
        source_enhancement_id=ctx.source_enhancement_id,
    )
def _finalize_write(ctx: _EditTarget, plan: _WritePlan,
                    run_regression: Callable[[], tuple]) -> FeedbackModification:
    attempt = _WriteAttempt(
        ctx=ctx, plan=plan, backup_path="",
        diff_preview=format_diff_preview(
            plan.raw_lines, plan.modified_lines, ctx.target["file"]))
    fail_mod = _precheck_content(attempt)
    if fail_mod is not None:
        return fail_mod
    try:
        backup_path = archive_backup(
            ctx.file_path, ctx.skill_dir, plan.backup_tag)
    except (OSError, RuntimeError, ValueError) as e:
        logger.warning("[L3] 备份归口不可用，拒绝无备份修改: %s", e)
        backup_path = ""
    attempt = replace(attempt, backup_path=backup_path)
    if not backup_path:
        return _write_fail(attempt, "备份失败，磁盘未修改")
    fail_mod = _commit_content(attempt)
    if fail_mod is not None:
        return fail_mod
    result = _verify_and_finalize(attempt, run_regression)
    if result.applied:
        logger.info(plan.success_log[0], *plan.success_log[1:])
    return result
_L3_MOD_SEQ = itertools.count(1)
def _next_mod_id(level: str, seq) -> str:
    return f"MOD-{level}-{int(time.time() * 1000)}-{next(seq):04d}"
_CV_INTEGRATION_TEST_MODULES: tuple[str, ...] = ()
_PLAN_BUILDERS: dict[str, Any] = {
    "dict_modify": _plan_dict_modify,
    "list_append": _plan_list_append,
    "dict_merge": _plan_dict_merge,
}
class CVRuleModifier:
    def __init__(self, skill_dir: str,
                 targets: dict[str, dict[str, Any]] | None = None,
                 integration_test_modules: tuple[str, ...] | None = None):
        self.skill_dir, self._targets = _prepare_targets(
            skill_dir, cv_rule_registry, targets)
        self._cv_test_modules = list(
            integration_test_modules if integration_test_modules is not None
            else (path for path in _CV_INTEGRATION_TEST_MODULES
                  if os.path.isfile(os.path.join(self.skill_dir, path))))
        self._last_target_file = ""
    @property
    def targets(self) -> dict[str, dict[str, Any]]:
        return _copy_targets(self._targets)
    def modify(self, target_name: str, modification: dict[str, Any],
               source_enhancement_id: str = "",
               confidence: float = DEFAULT_CONFIDENCE_FALLBACK) -> FeedbackModification:
        mod_id = _next_mod_id("L3", _L3_MOD_SEQ)
        if not isinstance(target_name, str):
            return _l3_fail(
                mod_id, None, safe_short_text(target_name), confidence,
                f"target_name 类型错误: 期望 str，实际 "
                f"{type(target_name).__name__}",
                source_enhancement_id=source_enhancement_id)
        target = self._targets.get(target_name)
        if not target:
            return _l3_fail(mod_id, None, target_name, confidence,
                            f"未知CV规则目标: {target_name}",
                            source_enhancement_id=source_enhancement_id)
        if not isinstance(target, dict):
            return _l3_fail(
                mod_id, None, target_name, confidence,
                f"CV规则目标配置必须是 dict（实际 {type(target).__name__}）",
                source_enhancement_id=source_enhancement_id)
        if not isinstance(modification, dict):
            return _l3_fail(mod_id, target, target_name, confidence,
                            f"modification 类型错误: 期望 dict，实际 "
                            f"{type(modification).__name__}",
                            source_enhancement_id=source_enhancement_id)
        file_path, path_error = _target_file_path(self.skill_dir, target)
        if path_error is not None:
            return _l3_fail(mod_id, target, target_name, confidence,
                            path_error,
                            source_enhancement_id=source_enhancement_id)
        planner = _PLAN_BUILDERS.get(_target_type(target))
        if planner is None:
            return _l3_fail(mod_id, target, target_name, confidence,
                            f"未知修改类型: {target.get('type')!r}",
                            source_enhancement_id=source_enhancement_id)
        self._last_target_file = target["file"]
        ctx = _EditTarget(
            skill_dir=self.skill_dir,
            file_path=file_path,
            target=target, target_name=target_name, mod_id=mod_id,
            confidence=confidence,
            source_enhancement_id=source_enhancement_id, eol="\n")
        fail_mod, ctx, original_content = _load_edit_target(ctx)
        if fail_mod is not None:
            return fail_mod
        return self._apply_plan(ctx, planner, original_content, modification)
    def _apply_plan(self, ctx: _EditTarget, planner: Any,
                    original_content: str,
                    modification: dict) -> FeedbackModification:
        fail_mod, plan = planner(ctx, original_content, modification)
        if fail_mod is not None:
            return fail_mod
        return _finalize_write(
            ctx, plan, self._run_cv_regression_test)
    def _regression_modules(self) -> list[str]:
        # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
        modules = list(self._cv_test_modules)
        if self._last_target_file:
            modules.extend(regression_test_candidates(self._last_target_file))
        return list(dict.fromkeys(modules))
    def _run_cv_regression_test(self) -> tuple:
        # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
        return run_pytest_regression(
            self.skill_dir, self._regression_modules(),
            tag="[L3]", skip_msg="CV regression skipped",
        )
CV_RULE_TARGETS: dict[str, dict[str, Any]] = {
    "CONFLICTING_PAIRS": {
        "file": "fix_guide_rule_identity.py",
        "type": "list_append",
        "description": "矛盾对列表，可追加新的矛盾对",
    },
    "CONTRADICTION_SEVERITY_DECISION": {
        "file": "xv_arbiter.py",
        "type": "dict_merge",
        "description": "矛盾严重度决策表，可合并新条目",
    },
    "_INITIAL_EVIDENCE_WEIGHTS": {
        "file": "xv_evidence_strength.py",
        "type": "dict_modify",
        "description": "证据家族权重，可调整具体家族的权重值",
        "min_weight": 0.3, "max_weight": 2.5,
    },
    "RULE_FP_TRACKER": {
        "file": "xv_threshold_learning.py",
        "type": "dict_modify",
        "description": "规则FP率追踪，可更新历史FP率",
    },
}
def _l1_skip_string_literal(text: str, i: int) -> int | None:
    quote = text[i:i + 3]
    if quote != text[i] * 3:
        quote = text[i]
    i += len(quote)
    n = len(text)
    while i < n:
        if text[i] == "\\":
            i += 2
            continue
        if text.startswith(quote, i):
            return i + len(quote)
        i += 1
    return None
def _has_original_marker(text: str) -> bool:
    return "# [original:" in text or "# original:" in text
_NON_ASSIGNMENT_EQ_PREFIX_CHARS = frozenset("=!<>:")
def _assignment_eq_index(code: str, start: int = 0) -> int | None:
    depth = 0
    idx = max(0, start)
    while idx < len(code):
        ch = code[idx]
        if ch == "#":
            break
        if ch in ("'", '"'):
            end = _l1_skip_string_literal(code, idx)
            if end is None:
                return None
            idx = end
            continue
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == "=" and depth == 0:
            prev_ch = code[idx - 1] if idx > 0 else ""
            next_ch = code[idx + 1] if idx + 1 < len(code) else ""
            if (prev_ch not in _NON_ASSIGNMENT_EQ_PREFIX_CHARS
                    and next_ch != "="):
                return idx
        idx += 1
    return None
def _target_file_path(skill_dir: str, target: dict) -> tuple[str | None, str | None]:
    if not isinstance(target, dict):
        return None, f"阈值目标配置必须是 dict（实际 {type(target).__name__}）"
    rel = target.get("file")
    if not isinstance(rel, str) or not rel.strip():
        return None, f"阈值目标缺少 file 配置: {rel!r}"
    normalized = os.path.normpath(rel)
    escapes_root = (normalized == os.pardir
                    or normalized.startswith(os.pardir + os.sep))
    if os.path.isabs(rel) or escapes_root:
        return None, f"阈值目标 file 必须是项目内相对路径: {rel!r}"
    full = os.path.join(skill_dir, rel)
    if resolve_within_root(skill_dir, rel) is None:
        return None, f"阈值目标 file 指向项目根外: {rel!r}"
    return full, None
def _read_source_with_encoding(file_path: str) -> tuple[str, str]:
    with open(file_path, "rb") as f:
        raw = f.read()
    encoding, _ = tokenize.detect_encoding(io.BytesIO(raw).readline)
    if encoding.lower().replace("-", "") == "utf8sig":
        encoding = "utf-8"
    return raw.decode(encoding), encoding

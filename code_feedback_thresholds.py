from __future__ import annotations

import ast
import itertools
import keyword
import logging
import math
import os
import re
import time
from dataclasses import dataclass
from decimal import ROUND_HALF_EVEN, Decimal, InvalidOperation
from typing import Any

from jwsgj.code_feedback_cv_rules import (
    _assignment_eq_index,
    _has_original_marker,
    _l1_skip_string_literal,
    _module_literal_assignment,
    _next_mod_id,
    _prepare_targets,
    _read_source_with_encoding,
    _strip_line_comment,
    _target_file_field,
    _target_file_path,
    _target_type,
    _type_field,
)
from jwsgj.diag_guard_io import (
    archive_backup,
    format_diff_preview,
    split_tokenizer_lines,
    verify_syntax,
)
from jwsgj.diag_guard_state import (
    rollback_note,
    write_with_rollback,
)
from jwsgj.diag_shared_source_core import (
    iter_frame_nodes,
    parse_cached,
    read_source_interpreter_encoding,
)
from jwsgj.diag_types_defs import FeedbackModification, str_field
from jwsgj.diag_types_normalize import safe_float
from jwsgj.diag_types_vocab import (
    DEFAULT_CONFIDENCE_FALLBACK,
    FIELD_ADJUSTED_CONFIDENCE,
    FIELD_THRESHOLD_ADJUST,
    FMT_DATETIME,
)
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    EVOLUTION_STATE_SECTIONS,
    get_jinhua_dir,
    get_temp_base,
    read_evolution_section,
    read_evolution_state,
    write_evolution_section,
)
from jwsgj.xv_intermediate_store import load_cv_findings_index

logger = get_module_logger(__name__)
__all__ = [
    'THRESHOLD_TARGETS',
    'ThresholdModifier',
    'build_replacement',
    'extract_disk_default',
    'extract_value_from_line',
    'find_constant_line',
    'infer_threshold_from_entry',
    'load_threshold_baselines',
    'numeric_threshold_target',
    'parse_disk_default',
    'parse_threshold_value',
    'register_threshold_target',
    'save_threshold_baselines',
    'simulate_threshold_effect',
    'threshold_direction_from_text',
    'threshold_registry',
    'validate_threshold_value',
]
THRESHOLD_TARGETS: dict[str, dict[str, Any]] = {  # jwsgj:suppress E1-MUTABLE-GLOBAL TP-07 — 审计认可：阈值注册表容器（register_threshold_target 显式登记），非共享状态缺陷
    "SINGLE_SOURCE_CONFIRM_THRESHOLD": {
        "file": "xv_threshold_learning.py",
        "type": "float",
        "default": 0.50,
        "min": 0.20, "max": 0.90,
        "description": "单源确认的置信度阈值",
        "keywords": ("confirm", "确认阈值"),
    },
    "COVERAGE_LOW_THRESHOLD": {
        "file": "xv_threshold_learning.py",
        "type": "int",
        "default": 40,
        "min": 10, "max": 80,
        "description": "低覆盖率分类阈值",
        "keywords": ("coverage", "覆盖率"),
    },
}
def threshold_registry(targets: dict | None) -> dict:
    return targets if isinstance(targets, dict) else THRESHOLD_TARGETS
def _is_valid_constant_name(value: Any) -> bool:
    return (isinstance(value, str) and value.isidentifier()
            and not keyword.iskeyword(value))
def numeric_threshold_target(constant_name: str,
                             targets: dict | None = None) -> dict | None:
    target = threshold_registry(targets).get(constant_name)
    if not isinstance(target, dict):
        return None
    return target if _target_type(target) in _SUPPORTED_TARGET_TYPES else None
_L1_MOD_SEQ = itertools.count(1)
def _is_valid_baseline(value: Any) -> bool:
    return (not isinstance(value, bool)
            and isinstance(value, (int, float)) and safe_float(value, None) is not None)
def _read_threshold_history(skill_dir: str):
    state = read_evolution_state(skill_dir, for_update=True)
    data = (state["threshold_history"] if "threshold_history" in state
            else read_evolution_section(skill_dir, "threshold_history"))
    if data is None:
        legacy_path = os.path.join(
            get_jinhua_dir(skill_dir),
            EVOLUTION_STATE_SECTIONS["threshold_history"])
        if "threshold_history" in state or os.path.isfile(legacy_path):
            raise ValueError(f"漂移基线历史存在但不可读: {legacy_path}")
    return data
def load_threshold_baselines(
    skill_dir: str, read_failures: list[str] | None = None,
) -> dict:
    if not skill_dir:
        return {}
    try:
        data = _read_threshold_history(skill_dir)
        if data is None:
            return {}
        if not isinstance(data, dict):
            detail = f"漂移基线历史顶层非对象({type(data).__name__})"
            logger.warning("[L1] %s，按空历史处理", detail)
            if read_failures is not None:
                read_failures.append(detail)
            return {}
        cleaned = _clean_history_entries(data)
        if len(cleaned) != len(data):
            detail = f"漂移基线历史含 {len(data) - len(cleaned)} 条非法记录"
            logger.warning("[L1] %s", detail)
            if read_failures is not None:
                read_failures.append(detail)
        return cleaned
    except (OSError, ValueError, RecursionError) as e:
        logger.warning("[L1] 漂移基线历史加载失败: %s", e)
        if read_failures is not None:
            read_failures.append(str(e))
    return {}
def _clean_history_entries(data: dict) -> dict:
    cleaned: dict = {}
    for name, entry in data.items():
        if not isinstance(name, str) or not name:
            continue
        original = entry.get("original") if isinstance(entry, dict) else entry
        if _is_valid_baseline(original):
            cleaned[name] = {"original": original}
    return cleaned
def save_threshold_baselines(history: dict, skill_dir: str) -> None:
    if not skill_dir:
        logger.warning(
            "[L1] 无可用持久化路径（jinhua 归口降级），跳过落盘")
        return
    if not isinstance(history, dict):
        logger.warning(
            "[L1] 漂移基线历史必须是 dict（实际 %s），跳过落盘",
            type(history).__name__)
        return
    normalized = _clean_history_entries(history)
    if len(normalized) != len(history):
        logger.warning(
            "[L1] 漂移基线历史存在 %d 条不可重载条目（应为 "
            "{name: {original: 数值}}），已丢弃: %s",
            len(history) - len(normalized),
            sorted(str(name) for name in history
                   if name not in normalized)[:5])
    try:
        if not write_evolution_section(
                skill_dir, "threshold_history", normalized):
            logger.warning("[L1] 漂移基线历史 section 落盘失败: %s", skill_dir)
    except (OSError, ValueError) as e:
        logger.warning("[L1] 漂移基线历史保存失败: %s", e)
def _clamp_step_value(old_val: float, new_value: float,
                      constant_name: str, decimals: int) -> float:
    if old_val == 0:
        return new_value
    old_decimal = _coerce_decimal(old_val)
    new_decimal = _coerce_decimal(new_value)
    if (old_decimal is None or new_decimal is None
            or not old_decimal.is_finite() or not new_decimal.is_finite()):
        raise ValueError("幅度钳位只接受有限数值")
    delta = new_decimal - old_decimal
    max_delta = abs(old_decimal) * Decimal("0.5")
    if abs(delta) <= max_delta:
        return new_value
    clamped = old_decimal + (max_delta if delta > 0 else -max_delta)
    ratio = abs(delta) / abs(old_decimal)
    logger.warning(
        "[L1] 调整幅度 %.0f%% 超过50%%限制，钳位: %s %s → %s",
        ratio * 100, constant_name, old_val, clamped,
    )
    if decimals == 0:
        return int(clamped.to_integral_value(rounding=ROUND_HALF_EVEN))
    return round(float(clamped), decimals)
def _check_cumulative_drift(history: dict, constant_name: str, disk_current_value: float, new_value: float) -> tuple:
    if constant_name not in history:
        baseline = disk_current_value
    else:
        _hist_entry = history[constant_name]
        baseline = (_hist_entry.get("original")
                    if isinstance(_hist_entry, dict) else _hist_entry)
    if not _is_valid_baseline(baseline):
        return False, (
            f"{constant_name} 漂移基线缺失或为脏值"
            f"({type(baseline).__name__})，拒绝按磁盘当前值重置基线")
    if baseline == 0:
        return True, ""
    baseline_decimal = _coerce_decimal(baseline)
    new_decimal = _coerce_decimal(new_value)
    if (baseline_decimal is None or new_decimal is None
            or not baseline_decimal.is_finite() or not new_decimal.is_finite()):
        return False, "累积漂移校验只接受有限数值"
    cumulative_ratio = abs(new_decimal - baseline_decimal) / abs(baseline_decimal)
    if cumulative_ratio > Decimal("0.6"):
        return False, (
            f"累积偏移 {cumulative_ratio:.0%} 超过60%安全阈值 "
            f"(基线={baseline}, 目标={new_value})，需人工审查"
        )
    return True, ""
_SUPPORTED_TARGET_TYPES = frozenset({"float", "int"})
_MIN_FLOAT_DECIMALS = 2
_MAX_FLOAT_DECIMALS = 8
def _threshold_target_error(target: Any) -> str | None:
    if not isinstance(target, dict):
        return f"阈值目标配置必须是 dict（实际 {type(target).__name__}）"
    if "type" not in target:
        return "阈值目标配置缺少字段: type"
    if _target_type(target) not in _SUPPORTED_TARGET_TYPES:
        return (f"阈值目标配置 type 非法: {target.get('type')!r}"
                f"（支持 float/int）")
    for key in ("default", "min", "max"):
        if key not in target:
            return f"阈值目标配置缺少字段: {key}"
        value = target[key]
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            return f"阈值目标配置字段 {key} 必须是有限数值: {value!r}"
        if safe_float(value, None) is None:
            return f"阈值目标配置字段 {key} 非有限数值: {value!r}"
    if target["min"] > target["max"]:
        return (f"阈值目标配置区间非法: min={target['min']} > "
                f"max={target['max']}")
    if not target["min"] <= target["default"] <= target["max"]:
        return (f"阈值目标配置 default 越界: default={target['default']} "
                f"不在 [{target['min']}, {target['max']}]")
    return None
def _float_precision(target: dict) -> int:
    values = [abs(value) for key in ("min", "max", "default")
              if (value := safe_float(target.get(key), None)) not in (None, 0)]
    scale = min(values, default=0.0)
    if scale == 0 or scale >= 0.1:
        return _MIN_FLOAT_DECIMALS
    decimals = -math.floor(math.log10(scale)) + 2
    return min(_MAX_FLOAT_DECIMALS, max(_MIN_FLOAT_DECIMALS, decimals))
def validate_threshold_value(
    target: dict, constant_name: str, val_type: str,
    new_value: Any, history: dict,
) -> tuple[str | None, Any]:
    if isinstance(new_value, bool):
        return f"bool 不是合法阈值新值: {new_value}", new_value
    if not isinstance(constant_name, str):
        return (f"常量名必须是 str（实际 {type(constant_name).__name__}）",
                new_value)
    target_error = _threshold_target_error(target)
    if target_error is not None:
        logger.warning("[L1] %s", target_error)
        return target_error, new_value
    if val_type != target.get("type"):
        return (f"阈值类型不匹配: 目标={target.get('type')!r}, "
                f"校验={val_type!r}"), new_value
    if not isinstance(history, dict):
        history = {}
    if val_type == "float":
        return _validate_float_value(target, constant_name, new_value, history)
    if val_type == "int":
        return _validate_int_value(target, constant_name, new_value, history)
    return f"不支持的阈值校验类型: {val_type!r}", new_value
def _apply_bounds_and_drift(target: dict, constant_name: str, new_value: Any,
                            history: dict, decimals: int,
                            *, as_int: bool) -> tuple[str | None, Any]:
    old_val = target["default"]
    value = _clamp_step_value(old_val, new_value, constant_name, decimals)
    value = round(max(target["min"], min(target["max"], value)), decimals)
    if as_int:
        value = int(value)
    if not target["min"] <= value <= target["max"]:
        reason = (f"阈值经精度/类型归一化后越界: {constant_name}="
                  f"{value} 不在 [{target['min']}, {target['max']}]")
        logger.warning("[L1] %s", reason)
        return reason, value
    drift_ok, drift_reason = _check_cumulative_drift(
        history, constant_name, old_val, value)
    if not drift_ok:
        logger.warning("[L1] %s", drift_reason)
        return drift_reason, value
    return None, value
def _validate_float_value(target: dict, constant_name: str, new_value: Any,
                          history: dict) -> tuple[str | None, Any]:
    try:
        new_value = float(new_value)
    except (ValueError, TypeError, OverflowError) as _e:
        log_swallowed(__name__, _e, context='validate_threshold_value:float_conv')
        return f"无法将值转为float: {new_value}", new_value
    if not math.isfinite(new_value):
        return f"float 值非有限（inf/nan）: {new_value}", new_value
    return _apply_bounds_and_drift(
        target, constant_name, new_value, history,
        _float_precision(target), as_int=False)
def _coerce_decimal(value: Any) -> Decimal | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        if isinstance(value, Decimal):
            return value
        if isinstance(value, float):
            value = str(value)
        return Decimal(value)
    except (InvalidOperation, TypeError, ValueError, OverflowError):
        return None
def _validate_int_value(target: dict, constant_name: str, new_value: Any,
                        history: dict) -> tuple[str | None, Any]:
    original_value = new_value
    numeric_value = _coerce_decimal(new_value)
    if numeric_value is None:
        return f"无法将值转为int: {new_value}", original_value
    if not numeric_value.is_finite():
        return f"int 值非有限（inf/nan/超出表示范围）: {new_value}", original_value
    if numeric_value != numeric_value.to_integral_value():
        return f"int 值必须是整数，收到: {new_value}", original_value
    return _apply_bounds_and_drift(
        target, constant_name, int(numeric_value), history, 0, as_int=True)
_ENV_GET_DEFAULT_RE = re.compile(
    r'(?<![\w.])(?:os\.environ\.get|os\.getenv)\((?:\s|#[^\n\r]*)*(["\'])[^"\']+\1\s*,\s*(["\'])([^"\']+)\2')
_ENV_NUMBER_DEFAULT_RE = re.compile(
    r'(?<![\w.])(env_number\((?:\s|#[^\n\r]*)*(["\'])[^"\']+\2\s*,\s*)([\w.+-]+)')
_ENV_NUMERIC_LITERAL_PATTERN = (
    r"[+-]?(?:"
    r"0[xX]_?[0-9a-fA-F](?:_?[0-9a-fA-F])*"
    r"|0[bB]_?[01](?:_?[01])*"
    r"|0[oO]_?[0-7](?:_?[0-7])*"
    r"|(?:\d(?:_?\d)*(?:\.(?:\d(?:_?\d)*)?)?|\.\d(?:_?\d)*)"
    r"(?:[eE][+-]?\d(?:_?\d)*)?"
    r")"
)
_ENV_GET_NUMERIC_DEFAULT_RE = re.compile(
    r'(?<![\w.])((?:os\.environ\.get|os\.getenv)\((?:\s|#[^\n\r]*)*(["\'])[^"\']+\2\s*,\s*)'
    rf'({_ENV_NUMERIC_LITERAL_PATTERN})\s*\)')
_ENV_DEFAULT_PATTERNS = (_ENV_NUMBER_DEFAULT_RE, _ENV_GET_DEFAULT_RE,
                         _ENV_GET_NUMERIC_DEFAULT_RE)
_ENV_LOOKUP_RE = re.compile(
    r'(?<![\w.])(?:os\.environ\.get|os\.getenv|env_number)\s*\(')
def _line_tail(line: str) -> str:
    return line[len(line.rstrip("\r\n")):]
def _comment_pos(text: str, start: int = 0) -> int | None:
    segment = text[max(0, start):]
    code = _strip_line_comment(segment)
    if code == segment:
        return None
    return len(text) - len(segment) + len(code)
def _unbalanced_bracket_depth(code: str) -> int:
    depth = 0
    i, n = 0, len(code)
    while i < n:
        ch = code[i]
        if ch in ("'", '"'):
            end = _l1_skip_string_literal(code, i)
            if end is None:
                break
            i = end
            continue
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        i += 1
    return depth
def _code_comment_spans(text: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    offset = 0
    for line in split_tokenizer_lines(text):
        cpos = _comment_pos(line)
        if cpos is not None:
            spans.append((offset + cpos, offset + len(line)))
        offset += len(line)
    return spans
def _string_literal_spans(text: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    i = 0
    n = len(text)
    while i < n:
        if text[i] == "#":
            while i < n and text[i] not in "\r\n":
                i += 1
            continue
        if text[i] not in ("'", '"'):
            i += 1
            continue
        start = i
        end = _l1_skip_string_literal(text, i)
        if end is None:
            spans.append((start, n))
            break
        spans.append((start, end))
        i = end
    return spans
def _search_code_default(pattern: re.Pattern, text: str):
    comment_spans = _code_comment_spans(text)
    string_spans = _string_literal_spans(text)
    for m in pattern.finditer(text):
        if any(s <= m.start(3) < e for s, e in comment_spans):
            continue
        if any(s <= m.start() < e for s, e in string_spans):
            continue
        return m
    return None
def _append_original_note(line_core: str, old_default: str) -> str:
    pos = _comment_pos(line_core)
    comment = line_core[pos:] if pos is not None else ""
    if _has_original_marker(comment):
        return line_core
    if pos is not None:
        return (f"{line_core[:pos].rstrip()}  # [original: {old_default}] "
                f"{line_core[pos:]}")
    return f"{line_core.rstrip()}  # [original: {old_default}]"
def _annotate_line(line: str, old_default: str) -> str:
    return (_append_original_note(line.rstrip("\r\n"), old_default)
            + _line_tail(line))
def _replace_match_span(line: str, match: re.Match, new_value: Any) -> str:
    return line[:match.start(3)] + str(new_value) + line[match.end(3):]
def _is_numeric_literal_value(value: Any) -> bool:
    if isinstance(value, bool):
        return False
    return isinstance(value, (int, float)) or (
        isinstance(value, str) and safe_float(value, None) is not None)
def _is_literal_default(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return _is_numeric_literal_value(node.value)
    return (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.UAdd, ast.USub))
            and isinstance(node.operand, ast.Constant)
            and isinstance(node.operand.value, (int, float))
            and not isinstance(node.operand.value, bool))
def _is_numeric_wrapper(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in {"float", "int"}
            and len(node.args) == 1 and not node.keywords)
def _is_os_env_get(func: ast.AST) -> bool:
    if (isinstance(func, ast.Attribute) and func.attr == "getenv"
            and isinstance(func.value, ast.Name) and func.value.id == "os"):
        return True
    return (
        isinstance(func, ast.Attribute) and func.attr == "get"
        and isinstance(func.value, ast.Attribute)
        and func.value.attr == "environ"
        and isinstance(func.value.value, ast.Name)
        and func.value.value.id == "os"
    )
def _is_env_default_call(node: ast.AST) -> bool:
    while _is_numeric_wrapper(node):
        node = node.args[0]
    if not isinstance(node, ast.Call) or len(node.args) < 2:
        return False
    is_env_number = (isinstance(node.func, ast.Name)
                     and node.func.id == "env_number")
    is_env_get = _is_os_env_get(node.func)
    return (is_env_number or is_env_get) and _is_literal_default(node.args[1])
def _single_assignment_statement(
        text: str) -> ast.Assign | ast.AnnAssign | None:
    tree = _parse_lines(split_tokenizer_lines(text))
    if tree is None or len(tree.body) != 1:
        return None
    statement = tree.body[0]
    return (statement if isinstance(statement, (ast.Assign, ast.AnnAssign))
            else None)
def _rewritable_env_default_node(text: str) -> ast.AST | None:
    statement = _single_assignment_statement(text)
    if statement is None or not _is_env_default_call(statement.value):
        return None
    node = statement.value
    while _is_numeric_wrapper(node):
        node = node.args[0]
    return node.args[1]
def _has_rewritable_simple_shape(text: str) -> bool:
    statement = _single_assignment_statement(text)
    return statement is not None and _is_literal_default(statement.value)
def _is_single_named_assignment(text: str, constant_name: str) -> bool:
    statement = _single_assignment_statement(text)
    if statement is None:
        return False
    targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
    return len(targets) == 1 and _assign_target_names(statement) == [constant_name]
def _match_rewrites_env_default(
        text: str, match: re.Match, original_default: ast.AST) -> bool:
    original_shape = ast.dump(original_default)
    for probe_value in ("918273645.0", "-918273645.0"):
        probe = (text[:match.start(3)] + probe_value
                 + text[match.end(3):])
        probe_default = _rewritable_env_default_node(probe)
        if (probe_default is not None
                and ast.dump(probe_default) != original_shape):
            return True
    return False
def _find_env_default(text: str) -> re.Match | None:
    original_default = _rewritable_env_default_node(text)
    if original_default is None:
        return None
    for pattern in _ENV_DEFAULT_PATTERNS:
        match = _search_code_default(pattern, text)
        if (match is not None and _match_rewrites_env_default(
                text, match, original_default)):
            return match
    return None
def _statement_window(lines: list[str], target_line_idx: int,
                      constant_name: str) -> list[str]:
    span = min(len(lines) - target_line_idx,
               _own_statement_span(lines, target_line_idx, constant_name))
    return lines[target_line_idx:target_line_idx + span]
def _assign_target_names(node: ast.Assign | ast.AnnAssign) -> list[str]:
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    return [t.id for t in targets if isinstance(t, ast.Name)]
def _parse_lines(lines: list[str]) -> ast.Module | None:
    try:
        return parse_cached("".join(lines).lstrip("\ufeff"))
    except (SyntaxError, ValueError, RecursionError, MemoryError) as _e:
        log_swallowed(
            __name__, _e, context=f'_parse_lines:{type(_e).__name__}')
        return None
def _own_statement_span(lines: list[str], target_line_idx: int,
                        constant_name: str) -> int:
    tree = _parse_lines(lines)
    if tree is None:
        return 1
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        if node.lineno - 1 != target_line_idx:
            continue
        if constant_name in _assign_target_names(node):
            return max(1, node.end_lineno - target_line_idx)
    return 1
def build_replacement(lines: list[str], target_line_idx: int,
                       constant_name: str, new_value: Any,
                       original_value_str: str) -> tuple[str, int, str]:
    line = lines[target_line_idx]
    window = _statement_window(lines, target_line_idx, constant_name)
    if not _is_single_named_assignment("".join(window), constant_name):
        return line, target_line_idx, original_value_str
    found = _rewrite_window_default(window, target_line_idx, new_value)
    if found is not None:
        return found
    return (_build_modified_line(line, new_value, original_value_str),
            target_line_idx, original_value_str)
def _rewrite_window_default(window: list[str], target_line_idx: int,
                            new_value: Any) -> tuple[str, int, str] | None:
    window_text = "".join(window)
    match = _find_env_default(window_text)
    if match is None:
        return None
    old_default = match.group(3)
    replaced = (window_text[:match.start(3)] + str(new_value)
                + window_text[match.end(3):])
    new_window = split_tokenizer_lines(replaced)
    if len(new_window) != len(window):
        return None
    for k, new_line in enumerate(new_window):
        if new_line != window[k]:
            return (_annotate_line(new_line, old_default),
                    target_line_idx + k, old_default)
    return None
def parse_disk_default(value_str: str, val_type: str) -> float | int | None:
    if (_type_field(val_type) not in _SUPPORTED_TARGET_TYPES
            or not isinstance(value_str, str)):
        return None
    try:
        literal = ast.literal_eval(value_str)
    except (SyntaxError, ValueError, TypeError, MemoryError, RecursionError):
        literal = value_str
    if isinstance(literal, bool):
        return None
    if val_type == "float":
        return (safe_float(literal, None)
                if isinstance(literal, (int, float, str)) else None)
    if isinstance(literal, int):
        return literal
    if not isinstance(literal, (float, str)):
        return None
    parsed = _coerce_decimal(literal)
    if (parsed is None or not parsed.is_finite()
            or parsed != parsed.to_integral_value()):
        return None
    return int(parsed)
def extract_disk_default(lines: list[str], target_line_idx: int,
                          single_line_value: str,
                          constant_name: str) -> str:
    if safe_float(single_line_value, None) is not None:
        return single_line_value
    window = _statement_window(lines, target_line_idx, constant_name)
    match = _find_env_default("".join(window))
    if match:
        return match.group(3)
    return single_line_value
def _module_const_line(tree: ast.Module, constant_name: str) -> int | None:
    found: int | None = None
    found_with_value: int | None = None
    assignments = [node for node in iter_frame_nodes([tree])
                   if isinstance(node, (ast.Assign, ast.AnnAssign))]
    for node in sorted(assignments, key=lambda item: item.lineno):
        if constant_name not in _assign_target_names(node):
            continue
        found = node.lineno - 1
        if isinstance(node, ast.AnnAssign) and node.value is None:
            continue
        found_with_value = node.lineno - 1
    return found_with_value if found_with_value is not None else found
def _textual_const_line(lines: list[str], constant_name: str) -> int | None:
    pattern = re.compile(
        rf'^\ufeff?{re.escape(constant_name)}\s*[:=](?!=)\s*')
    found: int | None = None
    found_with_value: int | None = None
    for i, line in enumerate(lines):
        if pattern.match(line) is None:
            continue
        found = i
        if extract_value_from_line(line):
            found_with_value = i
    return found_with_value if found_with_value is not None else found
def find_constant_line(lines: list[str],
                        constant_name: str) -> int | None:
    tree = _parse_lines(lines)
    if tree is None:
        return _textual_const_line(lines, constant_name)
    return _module_const_line(tree, constant_name)
def _assignment_value_eq_pos(code: str, first_eq: int) -> int:
    pos = first_eq
    while True:
        next_eq = _assignment_eq_index(code, pos + 1)
        if next_eq is None or not code[pos + 1:next_eq].strip().isidentifier():
            return pos
        pos = next_eq
def extract_value_from_line(line: str) -> str | None:
    stripped = line.strip()
    cpos = _comment_pos(stripped)
    code_part = stripped[:cpos].strip() if cpos is not None else stripped
    eq_idx = _assignment_eq_index(code_part)
    if eq_idx is not None:
        eq_pos = _assignment_value_eq_pos(code_part, eq_idx)
        return code_part[eq_pos + 1:].strip().rstrip(",")
    return None
def _rewrite_wrapped_default(stripped: str, new_value: Any) -> str | None:
    match = _find_env_default(stripped)
    if match is None:
        return None
    return _annotate_line(_replace_match_span(stripped, match, new_value),
                          match.group(3))
def _rewrite_simple_assignment(stripped: str, new_value: Any,
                               original_value: str) -> str | None:
    first_eq = _assignment_eq_index(stripped)
    if first_eq is None:
        return None
    eq_pos = _assignment_value_eq_pos(stripped, first_eq)
    name_part = stripped[:eq_pos + 1]
    comment_pos = _comment_pos(stripped, eq_pos + 1)
    if comment_pos is None:
        return f"{name_part} {new_value}  # [original: {original_value}]"
    comment = stripped[comment_pos:]
    if _has_original_marker(comment):
        return f"{name_part} {new_value}  {comment}"
    return (f"{name_part} {new_value}"
            f"  # [original: {original_value}] {comment}")
def _build_modified_line(original_line: str, new_value: Any,
                         original_value: str) -> str:
    stripped = original_line.strip()
    cpos = _comment_pos(stripped)
    code_only = (stripped[:cpos].rstrip() if cpos is not None
                 else stripped.rstrip())
    if _unbalanced_bracket_depth(code_only) > 0:
        return original_line
    rewritten = _rewrite_wrapped_default(stripped, new_value)
    if rewritten is None and _ENV_LOOKUP_RE.search(code_only):
        return original_line
    if rewritten is None and not _has_rewritable_simple_shape(stripped):
        return original_line
    if rewritten is None:
        rewritten = _rewrite_simple_assignment(
            stripped, new_value, original_value)
    if rewritten is None:
        return original_line
    indent = original_line[:len(original_line) - len(original_line.lstrip())]
    return indent + rewritten + _line_tail(original_line)
@dataclass(frozen=True, slots=True)
class _L1Ref:
    mod_id: str
    target: dict | None
    constant_name: str
    confidence: float = DEFAULT_CONFIDENCE_FALLBACK
    source_enhancement_id: str = ""
@dataclass(frozen=True, slots=True)
class _L1WritePlan:
    file_path: str
    modified_content: str
    backup_path: str
    original_value_str: str
    new_value: Any
    diff_preview: str
    encoding: str = "utf-8"
@dataclass(frozen=True, slots=True)
class _AuditFields:
    original_value_str: str = ""
    new_value: Any = ""
    diff_preview: str = ""
    backup_path: str = ""
@dataclass(frozen=True, slots=True)
class _TargetSource:
    lines: list[str]
    content: str
    line_idx: int
    value_str: str
    disk_default: Any
def _l1_fail(ref: _L1Ref, error_message: str,
             **audit: Any) -> FeedbackModification:
    kwargs: dict[str, Any] = {
        "modification_id": ref.mod_id, "level": "L1",
        "target_name": ref.constant_name,
        "action_type": FIELD_THRESHOLD_ADJUST,
        "applied": False, "confidence": ref.confidence,
        "error_message": error_message,
        "source_enhancement_id": ref.source_enhancement_id,
    }
    target_file = _target_file_field(ref.target)
    if target_file:
        kwargs["target_file"] = target_file
    kwargs.update(audit)
    return FeedbackModification(**kwargs)
def _fail_with_audit(ref: _L1Ref, message: str,
                     audit: Any, **extra: Any) -> FeedbackModification:
    return _l1_fail(
        ref, message,
        original_value=audit.original_value_str, new_value=str(audit.new_value),
        diff_preview=audit.diff_preview, backup_path=audit.backup_path, **extra)
def _build_edited_source(src: _TargetSource, new_value: Any, ref: _L1Ref) -> tuple:
    if src.disk_default is not None and new_value == src.disk_default:
        return (_zero_change_failure(
            src.disk_default, new_value, ref, src.value_str), "", "", "")
    new_line, actual_idx, original_value_str = build_replacement(
        src.lines, src.line_idx, ref.constant_name,
        new_value, src.value_str)
    modified_lines = src.lines.copy()
    modified_lines[actual_idx] = new_line
    modified_content = "".join(modified_lines)
    if modified_content == src.content:
        return (_zero_change_failure(
            src.disk_default, new_value, ref, src.value_str), "", "", "")
    return None, original_value_str, modified_content, format_diff_preview(
        src.lines, modified_lines, ref.target["file"])
def _zero_change_failure(disk_default: Any, new_value: Any, ref: _L1Ref,
                         value_str: str = "") -> FeedbackModification:
    if disk_default is not None and new_value == disk_default:
        return _l1_fail(
            ref,
            f"幂等重放: {ref.constant_name} 磁盘当前值已是 "
            f"{new_value}，无变化")
    if _ENV_LOOKUP_RE.search(value_str or ""):
        return _l1_fail(
            ref,
            f"环境变量默认值形态无法安全改写（未匹配可改写模式），"
            f"已拒绝修改: {ref.constant_name}={value_str}")
    return _l1_fail(
        ref,
        f"修改未产生实际内容变更（默认值替换未命中）: "
        f"{ref.constant_name}")
def _load_target_source(file_path: str, ref: _L1Ref) -> tuple:
    if not os.path.isfile(file_path):
        return _l1_fail(ref, f"文件不存在: {file_path}"), None, "", ""
    try:
        original_content, encoding = _read_source_with_encoding(file_path)
        return (None, split_tokenizer_lines(original_content),
                original_content, encoding)
    except (OSError, UnicodeDecodeError, LookupError, SyntaxError) as e:
        log_swallowed(__name__, e, context='ThresholdModifier.modify:read_source')
        return _l1_fail(ref, f"文件读取失败: {e}"), None, "", ""
def _align_registry_to_disk(original_lines: list, ref: _L1Ref) -> tuple:
    target = ref.target
    target_line_idx = find_constant_line(
        original_lines, ref.constant_name)
    if target_line_idx is None:
        return (_l1_fail(
            ref, f"未找到常量定义: {ref.constant_name}"), -1, "", None)
    original_value_str = extract_value_from_line(
        original_lines[target_line_idx])
    if original_value_str is None:
        original_value_str = "unknown"
    disk_value_str = extract_disk_default(
        original_lines, target_line_idx, original_value_str,
        ref.constant_name)
    disk_default = parse_disk_default(disk_value_str, target.get("type", ""))
    if disk_default is not None:
        target["default"] = disk_default
        original_value_str = disk_value_str
    return None, target_line_idx, original_value_str, disk_default
def _finalize_success(history: dict, history_path: str, original_value_str: str, new_value: Any, diff_preview: str, backup_path: str, file_path: str, ref: _L1Ref) -> FeedbackModification:
    target = ref.target
    constant_name = ref.constant_name
    audit = _AuditFields(
        original_value_str, new_value, diff_preview, backup_path)
    updated_history = dict(history)
    hist_entry = updated_history.get(constant_name)
    hist_entry = dict(hist_entry) if isinstance(hist_entry, dict) else {}
    hist_entry.setdefault("original", target["default"])
    updated_history[constant_name] = hist_entry
    expected_history = _clean_history_entries(updated_history)
    save_threshold_baselines(updated_history, history_path)
    persisted_history = load_threshold_baselines(history_path)
    if persisted_history != expected_history:
        rb_note = rollback_note(
            file_path, backup_path, "[L1] 漂移基线持久化失败回滚")
        return _fail_with_audit(
            ref, f"漂移基线持久化或回读校验失败{rb_note}",
            audit, syntax_valid=True)
    history.clear()
    history.update(expected_history)
    target["default"] = new_value
    logger.info(
        "[L1] 阈值修改成功: %s.%s: %s → %s (Ratchet: PASS)",
        target["file"], constant_name,
        original_value_str, str(new_value),
    )
    return FeedbackModification(
        modification_id=ref.mod_id, level="L1",
        target_file=target["file"],
        target_name=constant_name,
        action_type=FIELD_THRESHOLD_ADJUST,
        original_value=original_value_str,
        new_value=str(new_value),
        diff_preview=diff_preview,
        syntax_valid=True,
        backup_path=backup_path,
        applied=True,
        timestamp=time.strftime(FMT_DATETIME),
        confidence=ref.confidence,
        source_enhancement_id=ref.source_enhancement_id,
    )
def _literal_all_exports(tree: ast.AST) -> tuple[str, ...] | None:
    _stmt, value = _module_literal_assignment(tree, "__all__")
    if value is None:
        return ()
    if not isinstance(value, (ast.List, ast.Tuple)):
        return None
    names = []
    for item in value.elts:
        if not isinstance(item, ast.Constant) or not isinstance(item.value, str):
            return None
        names.append(item.value)
    return tuple(names)
def _ratchet_verify(file_path: str, backup_path: str) -> tuple[bool, str]:
    tree, compile_err = _parse_source_tree(file_path)
    if tree is None:
        return False, compile_err
    new_exports = _literal_all_exports(tree)
    if new_exports is None:
        return False, "__all__必须是可核验的字符串字面量列表/元组"
    if not (backup_path and os.path.isfile(backup_path)):
        return False, "Ratchet备份不可用，无法比较__all__导出"
    old_tree, backup_err = _parse_source_tree(backup_path)
    if old_tree is None:
        return False, f"Ratchet备份编译失败: {backup_err}"
    old_exports = _literal_all_exports(old_tree)
    if old_exports is None:
        return False, "Ratchet备份__all__不是可核验的字符串字面量列表/元组"
    missing = sorted(set(old_exports) - set(new_exports))
    if missing:
        return False, (
            f"__all__导出丢失: {', '.join(missing)} "
            f"(总数 {len(old_exports)}→{len(new_exports)})")
    return True, "OK"
def _parse_source_tree(path: str) -> tuple[ast.AST | None, str]:
    try:
        source = read_source_interpreter_encoding(path)
        return parse_cached(source, filename=path), ""
    except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
        log_swallowed(__name__, e,
                      context='ThresholdModifier._ratchet_verify:compile')
        return None, f"编译失败: {e}"
_CONFIDENCE_DOMAIN: tuple[float, float] = (0.0, 1.0)
def _in_confidence_domain(old_float: float, new_float: float) -> bool:
    low, high = _CONFIDENCE_DOMAIN
    return low <= old_float <= high and low <= new_float <= high
def _skip_simulation(details: dict, reason: str,
                     warn: bool = False) -> tuple[bool, dict]:
    details["reason"] = reason
    logger.log(logging.WARNING if warn else logging.INFO, "[L1] %s", reason)
    return True, details
def simulate_threshold_effect(skill_dir: str, constant_name: str,
                              old_value, new_value) -> tuple[bool, dict]:
    details = {"simulated": False}
    old_float = safe_float(old_value, None)
    new_float = safe_float(new_value, None)
    if old_float is None or new_float is None:
        return _skip_simulation(
            details,
            f"阈值非数值或非有限（old={old_value!r}, new={new_value!r}），跳过模拟")
    if not _in_confidence_domain(old_float, new_float):
        return _skip_simulation(
            details,
            f"阈值超出置信度值域 {_CONFIDENCE_DOMAIN}（old={old_float}, "
            f"new={new_float}），跳过模拟")
    if old_float == new_float:
        return _skip_simulation(details, "旧值=新值，无变化")
    try:
        temp_dir = get_temp_base(skill_dir)
    except (OSError, RuntimeError, ValueError) as e:
        log_swallowed(__name__, e, context='_simulate_threshold_effect:OSError+')
        return _skip_simulation(
            details, f"产物根解析失败，跳过模拟（允许修改）: {e}",
            warn=True)
    try:
        findings_index = load_cv_findings_index(temp_dir)
        if not findings_index:
            return _skip_simulation(
                details, "无可用 findings_index（无 CV 报告或索引为空），跳过模拟")
        total, would_flip = _count_flip_states(
            findings_index, old_float, new_float)
    except (OSError, ValueError, TypeError, RecursionError, MemoryError) as e:
        log_swallowed(
            __name__, e, context='_simulate_threshold_effect:index')
        return _skip_simulation(
            details, f"findings_index 读取/统计异常，跳过模拟（允许修改）: {e}",
            warn=True)
    return _evaluate_flip_rate(
        constant_name, details, total, would_flip, old_float, new_float)
def _evaluate_flip_rate(constant_name: str, details: dict, total: int,
                        would_flip: int, old_float: float,
                        new_float: float) -> tuple[bool, dict]:
    if total <= 0:
        return _skip_simulation(
            details, "findings_index 无有效数值置信度样本，跳过模拟")
    flip_rate = would_flip / total
    details["simulated"] = True
    details["total_findings"] = total
    details["would_flip"] = would_flip
    details["flip_rate"] = round(flip_rate, 3)
    details["old_threshold"] = old_float
    details["new_threshold"] = new_float
    if flip_rate > 0.20:
        details["blocked"] = True
        details["reason"] = (
            f"阈值变更导致 {would_flip}/{total} "
            f"({flip_rate:.1%}) findings 状态翻转，超过 20% 安全限制"
        )
        logger.warning("[L1] 效果模拟阻断: %s %.3f->%.3f, 翻转率 %.1f%%",
                       constant_name, old_float, new_float, flip_rate * 100)
        return False, details
    details["blocked"] = False
    details["reason"] = f"翻转率 {flip_rate:.1%} 在安全范围内"
    logger.info("[L1] 效果模拟通过: %s %.3f->%.3f, 翻转率 %.1f%%",
                constant_name, old_float, new_float, flip_rate * 100)
    return True, details
def _count_flip_states(findings_index: list, old_float: float,
                       new_float: float) -> tuple[int, int]:
    total = 0
    would_flip = 0
    for entry in findings_index:
        if not isinstance(entry, dict):
            continue
        confidence = entry.get(FIELD_ADJUSTED_CONFIDENCE)
        if (not isinstance(confidence, (int, float))
                or isinstance(confidence, bool)):
            continue
        if isinstance(confidence, float) and not math.isfinite(confidence):
            continue
        total += 1
        old_confirmed = confidence >= old_float
        new_confirmed = confidence >= new_float
        if old_confirmed != new_confirmed:
            would_flip += 1
    return total, would_flip
class ThresholdModifier:
    def __init__(self, skill_dir: str, targets: dict | None = None):
        self.skill_dir, self._targets = _prepare_targets(
            skill_dir, threshold_registry, targets)
        self._history_skill_dir = self.skill_dir if self.skill_dir else ""
        self._history_read_failures: list[str] = []
        self._adjustment_history = load_threshold_baselines(
            self._history_skill_dir, self._history_read_failures)
        _sync_registry_defaults(self.skill_dir, self._targets)
    def _validate_and_clamp_value(
        self, val_type: str, new_value: Any, ref: _L1Ref,
    ) -> tuple[FeedbackModification | None, Any]:
        reason, new_value = validate_threshold_value(
            ref.target, ref.constant_name, val_type, new_value,
            self._adjustment_history)
        if reason is not None:
            return _l1_fail(ref, reason), new_value
        return None, new_value
    def _write_modify_and_verify(
        self, plan: _L1WritePlan, ref: _L1Ref,
    ) -> FeedbackModification | None:
        write_err = write_with_rollback(
            plan.file_path, plan.modified_content,
            plan.backup_path, "L1", "[L1] modify",
            encoding=plan.encoding)
        if write_err:
            return _fail_with_audit(ref, write_err, plan)
        syntax_valid = verify_syntax(plan.file_path, tag="[L1]")
        if not syntax_valid:
            rb_note = rollback_note(plan.file_path, plan.backup_path,
                                     "[L1] modify")
            return _fail_with_audit(
                ref, f"语法验证失败{rb_note}", plan, syntax_valid=False)
        ratchet_passed = True
        ratchet_reason = ""
        try:
            ratchet_passed, ratchet_reason = _ratchet_verify(
                plan.file_path, plan.backup_path)
        except Exception as ratchet_err:  # noqa: BLE001 — 门禁异常必须回滚，不得放行
            logger.warning("[L1] Ratchet验证异常，阻断修改: %s", ratchet_err)
            ratchet_passed = False
            ratchet_reason = f"验证异常: {ratchet_err}"
        if not ratchet_passed:
            rb_note = rollback_note(plan.file_path, plan.backup_path,
                                     "[L1] Ratchet回滚")
            return _fail_with_audit(
                ref, f"Ratchet质量验证失败{rb_note}: {ratchet_reason}",
                plan, syntax_valid=syntax_valid)
        return None
    def modify(
            self, constant_name: str, new_value: Any,
            source_enhancement_id: str = "",
            confidence: float = DEFAULT_CONFIDENCE_FALLBACK,
    ) -> FeedbackModification:
        mod_id = _next_mod_id("L1", _L1_MOD_SEQ)
        if not _is_valid_constant_name(constant_name):
            logger.warning("[L1] 常量名形态非法 %r，拒绝修改", constant_name)
            return _l1_fail(
                _L1Ref(mod_id, None, str(constant_name), confidence,
                       source_enhancement_id),
                f"常量名必须是合法 Python 标识符: {constant_name!r}")
        target = self._targets.get(constant_name)
        if not isinstance(target, dict):
            return _l1_fail(
                _L1Ref(mod_id, None, constant_name, confidence,
                       source_enhancement_id),
                f"未知阈值目标: {constant_name}")
        ref = _L1Ref(mod_id, target, constant_name, confidence,
                     source_enhancement_id)
        if self._history_read_failures:
            return _l1_fail(
                ref, f"漂移基线历史不可信，拒绝修改: "
                     f"{self._history_read_failures[0]}")
        file_path, path_error = _target_file_path(self.skill_dir, target)
        if path_error is not None:
            return _l1_fail(ref, path_error)
        err_mod, original_lines, original_content, source_encoding = (
            _load_target_source(file_path, ref))
        if err_mod is not None:
            return err_mod
        err_mod, target_line_idx, original_value_str, disk_default = (
            _align_registry_to_disk(original_lines, ref))
        if err_mod is not None:
            return err_mod
        err_mod, new_value = self._validate_and_clamp_value(
            target.get("type", ""), new_value, ref)
        if err_mod is not None:
            return err_mod
        err_mod, original_value_str, modified_content, diff_preview = (
            _build_edited_source(
                _TargetSource(original_lines, original_content,
                              target_line_idx, original_value_str,
                              disk_default), new_value, ref))
        if err_mod is not None:
            return err_mod
        sim_err = self._simulation_gate(
            original_value_str, new_value, diff_preview, ref)
        if sim_err is not None:
            return sim_err
        try:
            backup_path = archive_backup(file_path, self.skill_dir, "L1")
        except (OSError, RuntimeError, ValueError) as e:
            logger.warning("[L1] 备份归口不可用，拒绝无备份修改: %s", e)
            backup_path = ""
        if not backup_path:
            return _fail_with_audit(
                ref, "备份失败，磁盘未修改",
                _AuditFields(original_value_str, new_value, diff_preview))
        write_err = self._write_modify_and_verify(
            _L1WritePlan(file_path, modified_content, backup_path,
                       original_value_str, new_value, diff_preview,
                       source_encoding), ref)
        if write_err is not None:
            return write_err
        return _finalize_success(
            self._adjustment_history, self._history_skill_dir,
            original_value_str, new_value, diff_preview, backup_path,
            file_path, ref)
    def _simulation_gate(self, original_value_str: str, new_value: Any,
                         diff_preview: str,
                         ref: _L1Ref) -> FeedbackModification | None:
        sim_ok, sim_details = simulate_threshold_effect(
            self.skill_dir, ref.constant_name, original_value_str, new_value)
        if sim_ok:
            return None
        return _fail_with_audit(
            ref, f"效果模拟阻断: {sim_details.get('reason', '')}",
            _AuditFields(original_value_str, new_value, diff_preview))
def register_threshold_target(
    constant_name: str, *, file: str, type: str = "float",
    default: float = _CONFIDENCE_DOMAIN[0], min: float = _CONFIDENCE_DOMAIN[0],
    max: float = _CONFIDENCE_DOMAIN[1], description: str = "",
    keywords: tuple[str, ...] = (),
) -> dict:
    if not _is_valid_constant_name(constant_name):
        raise ValueError(f"常量名必须是合法 Python 标识符: {constant_name!r}")
    if _type_field(type) not in _SUPPORTED_TARGET_TYPES:
        raise ValueError(f"不支持的阈值类型: {type!r}")
    target: dict[str, Any] = {"file": file, "type": type, "default": default,
                              "min": min, "max": max,
                              "description": description}
    target_error = _threshold_target_error(target)
    if target_error is not None:
        raise ValueError(target_error)
    if keywords:
        target["keywords"] = tuple(keywords)
    THRESHOLD_TARGETS[constant_name] = target
    return target
def _sync_registry_defaults(skill_dir: str,
                            targets: dict | None = None) -> None:
    registry = threshold_registry(targets)
    for constant_name, target in registry.items():
        ref = _L1Ref("MOD-L1-SYNC", target, constant_name)
        file_path, path_error = _target_file_path(skill_dir, target)
        if path_error is not None:
            logger.warning("[L1] %s（跳过磁盘对齐）", path_error)
            continue
        err_mod, lines, _content, _encoding = _load_target_source(
            file_path, ref)
        if err_mod is not None:
            continue
        _align_registry_to_disk(lines, ref)
def infer_threshold_from_entry(entry: dict,
                              targets: dict | None = None) -> str | None:
    entry = entry if isinstance(entry, dict) else {}
    registry = threshold_registry(targets)
    combined = (f"{str_field(entry, 'description')} "
                f"{str_field(entry, 'target')}").lower()
    for name, target in registry.items():
        if not isinstance(target, dict):
            continue
        keywords = target.get("keywords")
        if isinstance(keywords, (tuple, list)) and any(
                isinstance(k, str) and k.strip()
                and k.strip().lower() in combined
                for k in keywords):
            return name
    return None
_NUMBER_TEXT_PATTERN = r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?"
_PERCENT_ABSOLUTE_CONTEXT_RE = re.compile(
    r"(?:到|至|设为|设置为|调整为|=|\bto\b|\bset\b)\s*[:：]?\s*$",
    re.IGNORECASE)
def _parse_direct_value(suggested_value: str,
                        target: dict) -> tuple[bool, float | int | None]:
    if _has_negated_threshold_directive(suggested_value):
        logger.warning("parse_threshold_value: 显式否定指令，拒绝修改: %s",
                       suggested_value)
        return True, None
    pattern = (rf"(?<![\w.])(?P<number>{_NUMBER_TEXT_PATTERN})"
               rf"(?P<percent>\s*%)?")
    matches = list(re.finditer(pattern, suggested_value, re.ASCII))
    if not matches:
        return False, None
    contexts = [
        suggested_value[(matches[index - 1].end() if index else 0):candidate.start()]
        for index, candidate in enumerate(matches)
    ]
    absolute_indexes = [
        index for index, context in enumerate(contexts)
        if _PERCENT_ABSOLUTE_CONTEXT_RE.search(context) is not None
    ]
    selected_index = absolute_indexes[-1] if absolute_indexes else len(matches) - 1
    match = matches[selected_index]
    absolute_context = contexts[selected_index]
    is_percent = match.group("percent") is not None
    tail = suggested_value[match.end():]
    invalid_suffix = r"[A-Za-z0-9_%]" if is_percent else r"[\w%]"
    if (re.match(r"\.(?:\d|\.)", tail)
            or re.match(invalid_suffix, tail)):
        return True, None
    relative_percent = (
        is_percent and threshold_direction_from_text(suggested_value) != 0
        and _PERCENT_ABSOLUTE_CONTEXT_RE.search(absolute_context) is None)
    raw_value = match.group("number")
    try:
        parsed = float(raw_value)
    except (ValueError, OverflowError):
        logger.warning(
            "parse_threshold_value: 显式阈值数值解析失败，拒绝方向降级",
            exc_info=True)
        return True, None
    if not math.isfinite(parsed):
        logger.warning(
            "parse_threshold_value: 显式阈值数值非有限，拒绝方向降级: %s",
            raw_value)
        return True, None
    if relative_percent:
        return True, _infer_directional_value(
            suggested_value, target, relative_percent=parsed)
    if is_percent and _target_type(target) == "float":
        domain = [safe_float(target.get(key), None)
                  for key in ("default", "min", "max")]
        if all(value is not None and 0 <= value <= 1 for value in domain):
            parsed /= 100
    return True, parsed
_THRESHOLD_TIGHTEN_PHRASES: tuple[str, ...] = (
    "降低误报", "减少误报", "reduce_fp", "reduce false positive",
    "lower false positive", "fewer false positive", "cut false positive",
)
_THRESHOLD_LOOSEN_PHRASES: tuple[str, ...] = (
    "提升召回", "提高召回", "increase_recall", "increase recall",
    "improve recall", "raise recall", "boost recall",
)
_THRESHOLD_TIGHTEN_WORDS: tuple[str, ...] = (
    "收紧", "提高", "提升", "上调", "调高", "增大",
    "increase", "raise", "严格", "strict",
)
_THRESHOLD_LOOSEN_WORDS: tuple[str, ...] = (
    "放松", "放宽", "降低", "下调", "调低", "减小",
    "decrease", "lower", "宽松", "loose",
)
# 情态否定（不能/不可/不应…）与英文 cannot/should not 同族：
# 紧邻方向短语或指令词时判为否定指令
_CN_MODAL_NEGATION_ALT = (
    "不能|不能够|不可|不可以|不应|不应该|不该|不许|不准|不宜|无法")
# 句首判定取无条件形态；「不可」易与「不可避免」等非否定开头撞词，只允许后接指令动词
_CN_LEADING_MODAL_NEGATION_ALT = "不能|不应|不该|不许|不准|不宜|无法"
_DIRECTION_NEGATION_RE = re.compile(
    r"(?:\b(?:not|never|no|don't|dont|cannot|can't|cant|shouldn't|mustn't)"
    r"|不要|不是|别|禁止|避免|无需|无须|" + _CN_MODAL_NEGATION_ALT
    + r"|不)\s*$")
_NEGATED_THRESHOLD_INSTRUCTION_RE = re.compile(
    r"^\s*(?:(?:请\s*)?(?:不要|别|禁止|无需|无须|"
    + _CN_LEADING_MODAL_NEGATION_ALT + r")|请勿|"
    r"(?:不可以|不可|不)(?=\s*(?:(?:将|把)[^，。,；;！!？?]{0,24}?)?"
    r"\s*(?:调整|修改|改变|设定|设置|提高|降低|增大|减小|收紧|放宽))|"
    r"(?:please\s+)?(?:do\s+not|don't|dont|never|cannot|can't|cant|"
    r"should\s+not|must\s+not|shouldn't|mustn't)\b)", re.IGNORECASE)
_ABSOLUTE_DIRECTIVE_RE = re.compile(
    r"到|至|设为|设置为|调整为|=|\bto\b|\bset\b", re.IGNORECASE)
def _is_negated_directive_prefix(lowered: str, end: int) -> bool:
    return (_NEGATED_THRESHOLD_INSTRUCTION_RE.match(lowered) is not None
            or _DIRECTION_NEGATION_RE.search(lowered[:end]) is not None)
def _has_negated_phrase(lowered: str, phrases: tuple[str, ...]) -> bool:
    for phrase in phrases:
        start = 0
        while (index := lowered.find(phrase, start)) >= 0:
            if _is_negated_directive_prefix(lowered, index):
                return True
            start = index + len(phrase)
    return False
def _has_negated_threshold_directive(text: str) -> bool:
    lowered = text.lower() if isinstance(text, str) else ""
    direction_phrases = (
        _THRESHOLD_TIGHTEN_PHRASES + _THRESHOLD_LOOSEN_PHRASES
        + _THRESHOLD_TIGHTEN_WORDS + _THRESHOLD_LOOSEN_WORDS)
    if _has_negated_phrase(lowered, direction_phrases):
        return True
    return any(
        _is_negated_directive_prefix(lowered, match.start())
        for match in _ABSOLUTE_DIRECTIVE_RE.finditer(lowered))
def _has_unnegated_phrase(lowered: str, phrases: tuple[str, ...]) -> bool:
    for phrase in phrases:
        start = 0
        while (index := lowered.find(phrase, start)) >= 0:
            if not _is_negated_directive_prefix(lowered, index):
                return True
            start = index + len(phrase)
    return False
def threshold_direction_from_text(text: str) -> int:
    lowered = text.lower() if isinstance(text, str) else ""
    tighten = _has_unnegated_phrase(lowered, _THRESHOLD_TIGHTEN_PHRASES)
    loosen = _has_unnegated_phrase(lowered, _THRESHOLD_LOOSEN_PHRASES)
    if tighten or loosen:
        return 0 if tighten and loosen else (1 if tighten else -1)
    has_tighten = _has_unnegated_phrase(lowered, _THRESHOLD_TIGHTEN_WORDS)
    has_loosen = _has_unnegated_phrase(lowered, _THRESHOLD_LOOSEN_WORDS)
    if has_tighten == has_loosen:
        return 0
    return 1 if has_tighten else -1
def _infer_directional_value(suggested_value: str,
                             target: dict,
                             relative_percent: float | None = None) -> float | int | None:
    if not isinstance(target, dict):
        return None
    direction = threshold_direction_from_text(suggested_value)
    if direction == 0:
        return None
    if (relative_percent is not None
            and (not math.isfinite(relative_percent) or relative_percent < 0)):
        return None
    percent = 10.0 if relative_percent is None else relative_percent
    if _target_type(target) == "int":
        default_decimal = _coerce_decimal(target.get("default"))
        if (default_decimal is None or not default_decimal.is_finite()
                or default_decimal != default_decimal.to_integral_value()
                or default_decimal <= 0):
            return None
        default_int = int(default_decimal)
        factor = (Decimal(100) + Decimal(direction) * Decimal(str(percent))) / Decimal(100)
        candidate = int((Decimal(default_int) * factor).to_integral_value(
            rounding=ROUND_HALF_EVEN))
        if relative_percent is not None:
            return candidate
        return (max(default_int + 1, candidate) if direction > 0
                else min(default_int - 1, candidate))
    default = safe_float(target.get("default"), None)
    if default is None or default <= 0:
        return None
    decimals = _float_precision(target)
    value = round(default * (1 + direction * percent / 100), decimals)
    return value if math.isfinite(value) else None
def parse_threshold_value(suggested_value: str, target_key: str,
                          targets: dict | None = None) -> float | int | None:
    if not isinstance(suggested_value, str):
        suggested_value = ""
    if not isinstance(target_key, str) or not target_key:
        logger.warning(
            "parse_threshold_value: target_key 形态非法 %r，返回 None",
            target_key)
        return None
    target = numeric_threshold_target(target_key, targets)
    if target is None:
        logger.warning(
            "parse_threshold_value: 未知或非数值阈值目标 %r，返回 None",
            target_key)
        return None
    found, direct = _parse_direct_value(suggested_value, target)
    if found:
        return direct
    return _infer_directional_value(suggested_value, target)

from __future__ import annotations

import argparse
import dataclasses
import inspect
import json
import logging
import math
import os
import threading
import time
import traceback
import types
import typing
from collections.abc import Callable, Iterable, Iterator, Mapping, Sized
from concurrent.futures import ThreadPoolExecutor
from concurrent.futures import TimeoutError as FuturesTimeout
from dataclasses import dataclass, field
from functools import wraps
from typing import Any, ClassVar, NoReturn, Self

from jwsgj.diag_guard_state import (
    write_json_artifact,
)
from jwsgj.diag_types_defs import ContractViolationError
from jwsgj.log_config import log_swallowed, trace_module_run
from jwsgj.runtime_paths import (
    get_temp_base,
    is_dir_creation_allowed,
    normalize_skill_name,
)

_log = logging.getLogger(__name__)
__all__ = [
    "ADAPT_CONTRACT",
    "DEFAULT_PROJECT_ROOT",
    "DIAG_CONTRACT",
    "INIT_CONTRACT",
    "JSON_REPORT_ERRORS",
    "PREFLIGHT_CONTRACT",
    "REGISTER_CONTRACT",
    "SKILL_CREATION_CONTRACT",
    "TREATMENT_CONTRACT",
    "ActiveContract",
    "BoundaryContract",
    "ContractRegistry",
    "EntryGuard",
    "EntryGuardError",
    "ExceptionContract",
    "InvariantContract",
    "PostconditionError",
    "PreconditionError",
    "RepairFn",
    "SkillContract",
    "ToolRegistry",
    "TypeContract",
    "cli_boundary",
    "contract_assert",
    "dump_json_report",
    "dump_json_report_checked",
    "emit_json_report",
    "exit_code_of",
    "fail_cli",
    "field_of",
    "finish_cli_command",
    "get_cli_report_dir",
    "guard_result",
    "invariant_check",
    "json_text",
    "load_json_file",
    "logged_cli_command",
    "norm_display",
    "norm_list",
    "norm_warnings",
    "num_of",
    "parse_csv_option",
    "promote_single_dir",
    "require_dict",
    "require_dir",
    "require_file",
    "require_non_empty",
    "requires_contract",
    "resolve_project_root",
    "resolve_report_path",
    "run_cli_action",
    "split_csv",
    "to_mapping",
    "tool",
    "write_json_payload",
]
_log.info("%s 已加载：%d 项导出", __name__, len(__all__))
_INT_LIMIT_LABELS = frozenset({"max_lines_per_file", "max_input_length"})
_BOUNDARY_SCALAR_FIELDS: tuple[tuple[str, str, str, str], ...] = (
    ("file_size_mb", "max_file_size_mb", "文件大小", "MB"),
    ("lines", "max_lines_per_file", "行数", ""),
)
_BOUNDARY_FIELD_LABELS: dict[str, tuple[str, str]] = {
    key: (label, unit)
    for key, _attr, label, unit in _BOUNDARY_SCALAR_FIELDS
}
_FORBIDDEN_PATTERN_KEYS: tuple[str, ...] = (
    "file_path", "skill_dir", "path", "content", "code")
_OPERATION_KEYS: tuple[str, ...] = ("operation", "action", "task_type")
_CODE_CONTENT_KEYS: tuple[str, ...] = ("code", "content")
_INPUT_LENGTH_KEYS: tuple[str, ...] = (
    "content", "code", "source", "text", "input")
RepairFn = Callable[[dict[str, Any]], dict[str, Any]]
def _sequence_items(value: Any) -> list:
    if value is None:
        return []
    if isinstance(value, (str, bytes, bytearray, Mapping)):
        return [value]
    if isinstance(value, (set, frozenset)):
        try:
            return sorted(value, key=repr)
        except Exception as exc:
            _log.debug("_sequence_items: 集合排序失败，按原序返回: %s", exc)
            return list(value)
    if isinstance(value, Iterable):
        try:
            return list(value)
        except Exception as exc:
            _log.debug("_sequence_items: 可迭代物化失败，按单条处理: %s", exc)
            return [value]
    return [value]
_BOOL_TRUE_TOKENS = frozenset({"1", "true", "yes", "on", "y", "t"})
_BOOL_FALSE_TOKENS = frozenset({"0", "false", "no", "off", "n", "f", ""})
def _coerce_bool(value: Any) -> bool:
    if isinstance(value, str):
        token = value.strip().lower()
        if token in _BOOL_TRUE_TOKENS:
            return True
        if token in _BOOL_FALSE_TOKENS:
            return False
        parsed = _as_float(token)
        if parsed is not None and math.isfinite(parsed):
            return parsed != 0.0
        raise ValueError(f"无法解析的布尔字符串: {value!r}")
    return bool(value)
_COERCER_TABLE: dict[type, Callable[[Any], Any]] = {
    str: str,
    int: int,
    float: float,
    list: _sequence_items,
}
_UNION_TYPE: Any = getattr(types, "UnionType", ())
def _union_args(tp: Any) -> tuple[Any, ...] | None:
    origin = getattr(tp, "__origin__", None)
    if origin is typing.Union or isinstance(tp, _UNION_TYPE):
        return tuple(getattr(tp, "__args__", (tp,)))
    return None
def _as_float(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        result = float(value)
    except (OverflowError, ValueError, TypeError) as e:
        _log.debug("_as_float: 不可数值化，按 None 处理: %r (%s)", value, e)
        return None
    if math.isnan(result):
        _log.debug("_as_float: nan 无序不可比较，按 None 处理（防绕过边界判定）")
        return None
    return result
def _safe_str(value: Any) -> str | None:
    try:
        if not value:
            return None
        return str(value)
    except Exception as e:
        _log.debug("_safe_str: 对象字符串化失败，该键按不可判定跳过: %s", e)
        return None
def _reject_negative_limit(limit: float, label: str) -> float | int | None:
    if limit < 0:
        _log.warning(
            "BoundaryContract.%s 为负边界 %r，按未设置处理", label, limit)
        return None
    return limit
def _norm_limit(value: Any, label: str) -> float | int | None:
    if value is None:
        return None
    if isinstance(value, bool):
        _log.warning(
            "BoundaryContract.%s 为布尔阈值（bool 是 int 子类，语义不明），按未设置处理",
            label)
        return None
    if isinstance(value, int):
        return _reject_negative_limit(value, label)
    if label in _INT_LIMIT_LABELS and isinstance(value, str):
        try:
            integer_limit = int(value.strip(), 10)
        except ValueError:
            pass
        else:
            return _reject_negative_limit(integer_limit, label)
    parsed = _as_float(value)
    if parsed is None:
        _log.warning(
            "BoundaryContract.%s 非数值或 NaN，按未设置处理: %r", label, value)
        return None
    if label in _INT_LIMIT_LABELS and math.isfinite(parsed):
        nonnegative = _reject_negative_limit(parsed, label)
        return int(nonnegative) if nonnegative is not None else None
    return _reject_negative_limit(parsed, label)
def _norm_str_items(value: Any, label: str) -> list[str] | None:
    if value is None:
        return None
    kept: list[str] = []
    for item in _sequence_items(value):
        if isinstance(item, str):
            kept.append(item)
        else:
            _log.warning("%s 过滤非字符串条目: %r", label, item)
    return kept
def _norm_sequence_field(value: Any) -> list[Any] | None:
    if value is None:
        return None
    return _sequence_items(value)
def _context_number(value: Any) -> float | int | None:
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    return _as_float(value)
def _validator_entries(found: Any, label: str) -> list:
    if isinstance(found, str):
        return [found] if found else []
    try:
        if not found:
            return []
    except Exception as e:
        _log.debug("%s验证器返回值真值判定异常: %s", label, e)
        return [f"{label}验证器返回值真值判定异常: {e}"]
    try:
        items = list(found)
    except TypeError:
        _log.debug("%s验证器返回不可迭代真值，按单条违规处理: %r",
                   label, found)
        items = [found]
    except Exception as e:
        _log.debug("%s验证器返回值展开异常，降级为单条违规: %s", label, e)
        return [f"{label}验证器返回值不可展开: {e}"]
    entries: list[str] = []
    for item in items:
        try:
            entries.append(item if isinstance(item, str) else str(item))
        except Exception as e:
            _log.debug("%s验证器违规条目字符串化失败，跳过该条: %s",
                       label, e)
    return entries
@dataclass
class BoundaryContract:
    max_file_size_mb: float | None = None
    max_lines_per_file: int | None = None
    allowed_extensions: list[str] | None = None
    forbidden_patterns: list[str] | None = None
    input_validators: list[Callable[[dict[str, Any]], list[str]]] | None = None
    max_input_length: int | None = None
    required_input_keys: list[str] | None = None
    output_validators: list[Callable[[Any], list[str]]] | None = None
    required_output_keys: list[str] | None = None
    max_output_size_mb: float | None = None
    forbidden_operations: list[str] | None = None
    allowed_side_effects: list[str] | None = None
    def __post_init__(self) -> None:
        for attr in ("max_file_size_mb", "max_lines_per_file",
                     "max_input_length", "max_output_size_mb"):
            setattr(self, attr, _norm_limit(getattr(self, attr), attr))
        for attr in ("allowed_extensions", "required_input_keys",
                     "required_output_keys", "allowed_side_effects"):
            setattr(self, attr, _norm_str_items(
                getattr(self, attr), f"BoundaryContract.{attr}"))
        for attr in ("input_validators", "output_validators"):
            setattr(self, attr, _norm_sequence_field(getattr(self, attr)))
        for attr in ("forbidden_patterns", "forbidden_operations"):
            items = _norm_str_items(
                getattr(self, attr), f"BoundaryContract.{attr}")
            if items is not None:
                items = [item for item in items if item.strip()]
            setattr(self, attr, items)
    def _over_limit_fields(
            self, context: dict[str, Any]) -> list[tuple[str, Any, float]]:
        over: list[tuple[str, Any, float]] = []
        for key, attr, _label, _unit in _BOUNDARY_SCALAR_FIELDS:
            limit = _norm_limit(getattr(self, attr), attr)
            if limit is None:
                continue
            value = _context_number(context.get(key))
            if value is not None and value > limit:
                over.append((key, context.get(key), limit))
        return over
    def truncate(self, context: dict[str, Any]) -> dict[str, Any]:
        result = dict(context)
        for key, _raw, limit in self._over_limit_fields(context):
            result[key] = limit
            _log.info("BoundaryContract.truncate 裁剪: %s %s -> %s",
                      key, context.get(key), limit)
        return result
    def find_violations(self, context: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        violations.extend(self._violations_basic_boundary(context))
        violations.extend(self._violations_input(context))
        violations.extend(self._violations_output(context))
        violations.extend(self._violations_side_effects(context))
        return violations
    def find_input_violations(self, context: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        violations.extend(self._violations_basic_boundary(context))
        violations.extend(self._violations_input(context))
        violations.extend(self._violations_side_effects(context))
        return violations
    def _violations_basic_boundary(self, context: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        violations.extend(self._violations_invalid_measurements(context))
        for key, raw, limit in self._over_limit_fields(context):
            label, unit = _BOUNDARY_FIELD_LABELS[key]
            violations.append(
                f"{label} {raw}{unit} 超过边界 {limit}{unit}")
        violations.extend(self._violations_forbidden_patterns(context))
        violations.extend(self._violations_extension(context))
        return violations
    @staticmethod
    def _violations_invalid_measurements(
            context: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        for key, _attr, label, unit in _BOUNDARY_SCALAR_FIELDS:
            raw = context.get(key)
            if raw is not None and _context_number(raw) is None:
                violations.append(
                    f"{label}测量值 {raw!r}{unit} 不是可判定的数值")
        return violations
    def _violations_forbidden_patterns(self, context: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        if not self.forbidden_patterns:
            return violations
        for pattern in self.forbidden_patterns:
            if self._first_matching_text(context, _FORBIDDEN_PATTERN_KEYS, pattern):
                violations.append(f"路径/内容包含禁止模式: {pattern}")
        return violations
    @staticmethod
    def _first_matching_text(context: dict[str, Any], keys: tuple[str, ...],
                             needle: str) -> str | None:
        for key in keys:
            text = _safe_str(context.get(key))
            if text and needle in text:
                return text
        return None
    def _violations_extension(self, context: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        if self.allowed_extensions is None:
            return violations
        file_path = (_safe_str(context.get("file_path"))
                     or _safe_str(context.get("path")) or "")
        if not file_path:
            return violations
        ext = os.path.splitext(file_path)[1]
        allowed = {self._normalize_extension(item)
                   for item in self.allowed_extensions}
        if self._normalize_extension(ext) not in allowed:
            violations.append(
                f"文件扩展名 {ext or '（无扩展名）'} 不在允许列表 "
                f"{self.allowed_extensions} 中")
        return violations
    @staticmethod
    def _normalize_extension(ext: str) -> str:
        text = ext.strip().lower()
        if text and not text.startswith("."):
            text = "." + text
        return text
    def _violations_input(self, context: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        if self.required_input_keys:
            for key in self.required_input_keys:
                if self._safe_key_missing(context, key, "输入"):
                    violations.append(
                        f"输入约束违反: 缺少必需的输入键 '{key}'"
                    )
        input_limit = _norm_limit(self.max_input_length, "max_input_length")
        if input_limit is not None:
            for key in _INPUT_LENGTH_KEYS:
                val = context.get(key, "")
                if isinstance(val, (str, bytes, bytearray)) and len(val) > input_limit:
                    violations.append(
                        f"输入约束违反: '{key}' 长度 {len(val)} 超过最大值 {input_limit}"
                    )
        if self.input_validators:
            violations.extend(self._run_validators(
                self.input_validators, context, "输入"))
        return violations
    @staticmethod
    def _run_validators(validators, payload: Any, label: str) -> list[str]:
        violations: list[str] = []
        for validator in validators or ():
            try:
                found = validator(payload)
            except Exception as e:
                _log.debug("%s验证器执行异常已抑制: %s", label, e)
                violations.append(f"{label}验证器异常: {e}")
                continue
            violations.extend(_validator_entries(found, label))
        return violations
    def _violations_output(self, context: dict[str, Any]) -> list[str]:
        if "output" in context:
            output = context["output"]
        elif "result" in context:
            output = context["result"]
        else:
            return []
        return self.find_output_violations(output)
    def find_output_violations(self, output: Any) -> list[str]:
        violations: list[str] = []
        violations.extend(self._violations_output_keys(output))
        violations.extend(self._violations_output_size(output))
        if self.output_validators:
            violations.extend(self._run_validators(
                self.output_validators, output, "输出"))
        return violations
    @staticmethod
    def _safe_key_missing(mapping: Any, key: str, label: str) -> bool:
        try:
            return key not in mapping
        except Exception as e:
            _log.debug(
                "BoundaryContract: %s键 '%s' 存在性判定异常，按缺失处理: %s",
                label, key, e)
            return True
    def _violations_output_keys(self, output: Any) -> list[str]:
        keys = self.required_output_keys
        if not keys:
            return []
        if isinstance(output, Mapping):
            return [f"输出约束违反: 缺少必需的输出键 '{key}'"
                    for key in keys
                    if self._safe_key_missing(output, key, "输出")]
        if isinstance(output, str):
            return [f"输出约束违反: 输出中缺少必需键 '{key}'"
                    for key in keys if key not in output]
        return [
            f"输出约束违反: 输出类型 {type(output).__name__} "
            f"无法提供必需键 '{key}'"
            for key in keys
        ]
    @staticmethod
    def _payload_size_bytes(output: Any) -> int:
        if isinstance(output, memoryview):
            return output.nbytes
        if isinstance(output, (bytes, bytearray)):
            return len(output)
        if isinstance(output, str):
            return len(output.encode("utf-8"))
        return len(str(output).encode("utf-8"))
    def _violations_output_size(self, output: Any) -> list[str]:
        violations: list[str] = []
        size_limit = _norm_limit(self.max_output_size_mb, "max_output_size_mb")
        if size_limit is None:
            return violations
        try:
            output_size = self._payload_size_bytes(output) / (1024 * 1024)
            if output_size > size_limit:
                violations.append(
                    f"输出约束违反: 输出大小 {output_size:.2f}MB 超过最大值 {size_limit}MB"
                )
        except Exception as _e:
            _log.warning("BoundaryContract: output size calculation failed: %s", _e)
            violations.append(
                "输出约束违反: 输出大小不可判定 "
                f"({type(_e).__name__}: {_e})"
            )
        return violations
    def _violations_side_effects(self, context: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        violations.extend(self._violations_forbidden_operations(context))
        violations.extend(self._violations_allowed_side_effects(context))
        return violations
    def _violations_forbidden_operations(self, context: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        if not self.forbidden_operations:
            return violations
        code_texts = [
            text for text in
            (_safe_str(context.get(key)) for key in _CODE_CONTENT_KEYS)
            if text]
        for op in self.forbidden_operations:
            hit = self._first_matching_text(context, _OPERATION_KEYS, op)
            if hit:
                violations.append(
                    f"副作用约束违反: 操作 '{hit}' 包含禁止操作 '{op}'"
                )
            if any(op in text for text in code_texts):
                violations.append(
                    f"副作用约束违反: 代码内容包含禁止操作 '{op}'"
                )
        return violations
    @staticmethod
    def _side_effect_items(
            context: dict[str, Any]) -> tuple[list[Any], Exception | None]:
        side_effects = context.get("side_effects", [])
        try:
            if not side_effects:
                return [], None
            return _sequence_items(side_effects), None
        except Exception as e:
            _log.debug(
                "BoundaryContract: side_effects 判定异常，按违规处理: %s", e)
            return [], e
    def _violations_allowed_side_effects(self, context: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        if self.allowed_side_effects is None:
            return violations
        items, inspection_error = self._side_effect_items(context)
        if inspection_error is not None:
            return [
                ("副作用约束违反: 副作用集合不可判定 "
                 f"({type(inspection_error).__name__}: {inspection_error})")
            ]
        for se in items:
            try:
                if se not in self.allowed_side_effects:
                    violations.append(
                        f"副作用约束违反: 副作用 '{se}' 不在允许列表 {self.allowed_side_effects} 中"
                    )
            except Exception as e:
                _log.debug(
                    "BoundaryContract: 副作用条目 %s 判定异常，按违规处理: %s",
                    type(se).__name__, e)
                violations.append(
                    "副作用约束违反: 副作用条目不可判定 "
                    f"({type(se).__name__}: {type(e).__name__}: {e})"
                )
        return violations
def _repair_skill_dir(state: dict[str, Any]) -> dict[str, Any]:
    result = dict(state)
    skill_dir = state.get("skill_dir", "")
    if skill_dir and isinstance(skill_dir, str) and os.path.isabs(skill_dir):
        try:
            _ensure_abs_skill_dir(skill_dir)
        except (OSError, ValueError) as exc:
            _log.warning("Failed to create skill_dir %s: %s", skill_dir, exc)
    return result
def _ensure_abs_skill_dir(skill_dir: str) -> None:
    if os.path.isdir(skill_dir):
        return
    if not is_dir_creation_allowed(skill_dir):
        _log.warning(
            "拒绝隐式创建 skill_dir（盘根直属凭空生长，防外部污染）: %s",
            skill_dir)
        return
    os.makedirs(skill_dir, exist_ok=True)
@dataclass
class TypeContract:
    param_types: dict[str, type] = field(default_factory=dict)
    return_type: type | None = None
    @staticmethod
    def _coerce_value(value: Any, expected: type) -> Any:
        if expected in (int, float) and isinstance(value, bool):
            return value
        coercer = _coerce_bool if expected is bool else _COERCER_TABLE.get(expected)
        if coercer is None:
            return value
        try:
            return coercer(value)
        except Exception as e:
            _log.warning("[Contract] 类型强制转换失败,返回原值: %s", e)
            return value
    def coerce(self, kwargs: dict[str, Any]) -> dict[str, Any]:
        result = dict(kwargs)
        for name, expected in self.param_types.items():
            if name not in result or result[name] is None:
                continue
            result[name] = self._coerce_to_expected(result[name], expected)
        return result
    def _coerce_to_expected(self, value: Any, expected: Any) -> Any:
        members = self._member_types(expected)
        if self._safe_isinstance(value, members):
            return value
        for member in members:
            coerced = self._coerce_value(value, member)
            if self._safe_isinstance(coerced, member):
                return coerced
        return value
    def find_violations(self, kwargs: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        for name, expected in self.param_types.items():
            if name in kwargs:
                expected_types = self._member_types(expected)
                if not self._safe_isinstance(kwargs[name], expected_types):
                    actual = type(kwargs[name])
                    exp_name = getattr(expected, '__name__', str(expected))
                    violations.append(
                        f"参数 {name!r} 期望 {exp_name}，实际 {actual.__name__}"
                    )
        return violations
    def find_return_violations(self, value: Any) -> list[str]:
        expected = self.return_type
        if expected is None or self._safe_isinstance(
                value, self._member_types(expected)):
            return []
        exp_name = getattr(expected, '__name__', str(expected))
        return [f"返回值期望 {exp_name}，实际 {type(value).__name__}"]
    @classmethod
    def _safe_isinstance(cls, value: Any, tp: Any) -> bool:
        if isinstance(tp, tuple):
            return any(cls._safe_isinstance(value, member) for member in tp)
        if tp is int and isinstance(value, bool):
            return False
        try:
            return isinstance(value, tp)
        except TypeError:
            origin = getattr(tp, "__origin__", None)
            if isinstance(origin, type):
                return isinstance(value, origin)
            _log.debug("_safe_isinstance: 类型不可规约，按 True 放行: %r", tp)
            return True
    @classmethod
    def _member_types(cls, tp: Any) -> tuple:
        members = cls._unwrap_optional(tp)
        return members if isinstance(members, tuple) else (members,)
    @staticmethod
    def _unwrap_optional(tp: type) -> type | tuple[type, ...]:
        args = _union_args(tp)
        if args is not None:
            return args if len(args) > 1 else args[0]
        return tp
@dataclass
class ExceptionContract:
    expected_exceptions: tuple[type, ...] = ()
    never_raises: tuple[type, ...] = ()
    def __post_init__(self) -> None:
        for label in ("expected_exceptions", "never_raises"):
            members = tuple(_norm_sequence_field(getattr(self, label)) or ())
            setattr(self, label, members)
            bad = [
                member for member in members
                if not isinstance(member, type)
                or not issubclass(member, BaseException)
            ]
            if bad:
                raise TypeError(
                    f"ExceptionContract.{label} 成员必须是异常类，"
                    "实际含非异常类项: "
                    f"{[getattr(b, '__name__', type(b).__name__) for b in bad]}")
    @staticmethod
    def _is_subclass(raised: type, member: Any) -> bool:
        try:
            return issubclass(raised, member)
        except TypeError:
            _log.warning(
                "ExceptionContract: 成员 %r 不可 issubclass 判定，跳过该成员",
                member)
            return False
    def validate_post(self, raised: type | None) -> None:
        if not raised:
            return
        for member in self.never_raises:
            if self._is_subclass(raised, member):
                raise ContractViolationError(
                    f"契约违反: 函数承诺绝不抛出 {raised.__name__}, 但实际抛出了该异常"
                )
        if not self.expected_exceptions:
            return
        if any(self._is_subclass(raised, member)
               for member in self.expected_exceptions):
            return
        expected = ", ".join(getattr(m, "__name__", str(m))
                             for m in self.expected_exceptions)
        raise ContractViolationError(
            f"契约违反: 函数抛出了未声明异常 {raised.__name__}, 预期 {expected}"
        )
@dataclass
class InvariantContract:
    invariants: list[Callable[[dict[str, Any]], bool]] = field(default_factory=list)
    description: str = ""
    _repair_fns: list[RepairFn] = field(default_factory=list)
    def __post_init__(self) -> None:
        self.invariants = _norm_sequence_field(self.invariants) or []
        self._repair_fns = _norm_sequence_field(self._repair_fns) or []
    @staticmethod
    def _safe_eval(inv: Callable[[dict[str, Any]], bool],
                   state: dict[str, Any]) -> tuple[bool, Exception | None]:
        try:
            return bool(inv(state)), None
        except Exception as e:
            log_swallowed(__name__, e, context='InvariantContract._safe_eval:Exc')
            return False, e
    def _iter_checks(self, state: dict[str, Any]
                     ) -> Iterator[tuple[Callable[[dict[str, Any]], bool], bool, Exception | None]]:
        for inv in self.invariants:
            ok, err = self._safe_eval(inv, state)
            yield inv, ok, err
    def check_post(self, state: dict[str, Any]) -> None:
        for _inv, ok, err in self._iter_checks(state):
            if err is not None:
                raise ContractViolationError(
                    f"不变性谓词执行异常(后置): {self.description}: {err}") from err
            if not ok:
                raise ContractViolationError(f"不变性违反(后置): {self.description}")
    def repair(self, state: dict[str, Any],
               extra_repairs: list[RepairFn] | None = None) -> dict[str, Any]:
        if not self.find_violations(state):
            return dict(state)
        result = dict(state)
        all_repairs = list(self._repair_fns or []) + (extra_repairs or [])
        for repair_fn in all_repairs:
            candidate = self._apply_repair_fn(repair_fn, result)
            if candidate is None:
                continue
            all_ok, predicate_error = self._candidate_verdict(candidate)
            if predicate_error:
                continue
            if all_ok:
                _log.info("InvariantContract.repair 修复收敛: %s",
                          self.description or type(self).__name__)
                return candidate
            result = candidate
        return result
    @staticmethod
    def _apply_repair_fn(repair_fn: RepairFn, result: dict[str, Any]) -> dict[str, Any] | None:
        try:
            candidate = repair_fn(dict(result))
        except Exception as _e:
            _log.warning("InvariantContract.repair: repair function failed: %s", _e)
            return None
        if not isinstance(candidate, dict):
            _log.warning(
                "InvariantContract.repair: repair function returned "
                "non-mapping %s, candidate discarded",
                type(candidate).__name__)
            return None
        return candidate
    def _candidate_verdict(self, candidate: dict[str, Any]) -> tuple[bool, bool]:
        for _inv, ok, err in self._iter_checks(candidate):
            if err is not None:
                _log.warning(
                    "InvariantContract.repair: invariant predicate failed: %s", err)
                return False, True
            if not ok:
                return False, False
        return True, False
    def find_violations(self, state: dict[str, Any]) -> list[str]:
        violations: list[str] = []
        for inv, ok, err in self._iter_checks(state):
            desc = getattr(inv, "_invariant_description", "") or self.description
            if err is not None:
                violations.append(f"不变性谓词异常: {desc}: {err}")
            elif not ok:
                violations.append(f"不变性违反: {desc}")
        return violations
def _repair_skill_name(state: dict[str, Any]) -> dict[str, Any]:
    result = dict(state)
    name = state.get("skill_name", "")
    if name:
        result["skill_name"] = normalize_skill_name(name)
    return result
def _nonempty_str(state: dict[str, Any], key: str) -> bool:
    val = state.get(key)
    return isinstance(val, str) and val.strip() != ""
_RAISED_UNSET = object()
@dataclass
class SkillContract:
    type_c: TypeContract = field(default_factory=TypeContract)
    boundary_c: BoundaryContract | None = None
    exception_c: ExceptionContract = field(default_factory=ExceptionContract)
    invariant_c: InvariantContract | None = None
    description: str = ""
    version: str = "1.0.0"
    def validate_post(self, raised: Any = _RAISED_UNSET, /, **kwargs: Any) -> None:
        if raised is _RAISED_UNSET:
            raised = None
            legacy = kwargs.get("raised")
            if isinstance(legacy, type) and issubclass(legacy, BaseException):
                raised = kwargs.pop("raised")
        self.exception_c.validate_post(raised)
        if self.invariant_c:
            self.invariant_c.check_post(kwargs)
    def validate_result(self, result: Any) -> None:
        violations: list[str] = []
        if self.type_c:
            violations.extend(self.type_c.find_return_violations(result))
        if self.boundary_c:
            violations.extend(self.boundary_c.find_output_violations(result))
        if violations:
            raise ContractViolationError(f"契约违反(返回值): {violations}")
    def find_all_violations(self, **kwargs: Any) -> list[str]:
        return self._collect_violations(kwargs, include_output=True)
    def find_input_violations(self, **kwargs: Any) -> list[str]:
        return self._collect_violations(kwargs, include_output=False)
    def _collect_violations(self, kwargs: dict[str, Any],
                            include_output: bool) -> list[str]:
        violations: list[str] = []
        if self.type_c:
            violations.extend(self.type_c.find_violations(kwargs))
        if self.boundary_c:
            finder = (self.boundary_c.find_violations if include_output
                      else self.boundary_c.find_input_violations)
            violations.extend(finder(kwargs))
        if self.invariant_c:
            violations.extend(self.invariant_c.find_violations(kwargs))
        return violations
def _std_exception_contract() -> ExceptionContract:
    return ExceptionContract(
        expected_exceptions=(
            FileNotFoundError, PermissionError, OSError, ContractViolationError),
        never_raises=(RuntimeError,),
    )
def _skill_name_present(state: dict[str, Any]) -> bool:
    return state.get("skill_name") is not None
def _skill_name_invariant(description: str) -> InvariantContract:
    return InvariantContract(
        invariants=[_skill_name_present],
        description=description,
        _repair_fns=[_repair_skill_name],
    )
def _nonempty_fields_invariant(description: str, keys: tuple[str, ...],
                               repair_fns: list[RepairFn] | None = None,
                               ) -> InvariantContract:
    return InvariantContract(
        invariants=[lambda s, key=key: _nonempty_str(s, key) for key in keys],
        description=description,
        _repair_fns=list(repair_fns or []),
    )
REGISTER_CONTRACT = SkillContract(
    type_c=TypeContract(
        param_types={"skill_name": str, "skill_type": str, "skill_dir": str},
        return_type=dict,
    ),
    exception_c=_std_exception_contract(),
    invariant_c=_nonempty_fields_invariant(
        "注册步骤: skill_name/skill_type/skill_dir不可为空",
        ("skill_name", "skill_type", "skill_dir"),
        [_repair_skill_name, _repair_skill_dir],
    ),
    description="技能注册步骤契约",
)
DIAG_CONTRACT = SkillContract(
    type_c=TypeContract(
        param_types={"skills_dir": str},
        return_type=None,
    ),
    exception_c=_std_exception_contract(),
    invariant_c=_nonempty_fields_invariant(
        "诊断步骤: skills_dir不可为空", ("skills_dir",)),
    description="技能诊断步骤契约",
)
SKILL_CREATION_CONTRACT = SkillContract(
    type_c=TypeContract(
        param_types={"skill_name": str, "description": str, "skill_dir": str},
        return_type=dict,
    ),
    boundary_c=BoundaryContract(max_file_size_mb=10.0),
    exception_c=_std_exception_contract(),
    invariant_c=_skill_name_invariant(
        "技能创建: skill_name 不可为 None（空名由 ensure_valid_skill_name 生成默认名）"),
    description="技能创建操作契约（引导式创建入口）",
)
PREFLIGHT_CONTRACT = SkillContract(
    type_c=TypeContract(
        param_types={"skill_name": str},
        return_type=dict,
    ),
    exception_c=_std_exception_contract(),
    invariant_c=_skill_name_invariant("预检步骤: skill_name 不可为 None"),
    description="技能预检步骤契约",
)
INIT_CONTRACT = SkillContract(
    type_c=TypeContract(
        param_types={"skill_name": str, "description": str},
        return_type=dict,
    ),
    exception_c=_std_exception_contract(),
    invariant_c=_skill_name_invariant("初始化步骤: skill_name 不可为 None"),
    description="技能初始化步骤契约",
)
def invariant_check(description: str) -> Callable:
    def decorator(func: Callable[[dict[str, Any]], bool]) -> Callable[[dict[str, Any]], bool]:
        func._invariant_description = description
        return func
    return decorator
@invariant_check("适配入口: source_skill 不可为空")
def _adapt_source_skill_nonempty(state: dict[str, Any]) -> bool:
    return _nonempty_str(state, "source_skill")
ADAPT_CONTRACT = SkillContract(
    type_c=TypeContract(
        param_types={"source_skill": str},
        return_type=None,
    ),
    exception_c=_std_exception_contract(),
    invariant_c=InvariantContract(
        invariants=[_adapt_source_skill_nonempty],
        description="适配入口: source_skill 不可为空",
    ),
    description="技能适配入口契约（消费方 build_skill_lifecycle.adapt_skill）",
)
@invariant_check("治疗执行: skill_dir 不可为空")
def _treatment_skill_dir_nonempty(state: dict[str, Any]) -> bool:
    return _nonempty_str(state, "skill_dir")
@invariant_check("治疗执行: fixed_source 不可为空")
def _treatment_fixed_source_nonempty(state: dict[str, Any]) -> bool:
    return _nonempty_str(state, "fixed_source")
TREATMENT_CONTRACT = SkillContract(
    type_c=TypeContract(
        param_types={"skill_dir": str, "index": int, "fixed_source": str},
        return_type=dict,
    ),
    exception_c=ExceptionContract(
        expected_exceptions=(FileNotFoundError, PermissionError, ValueError,
                             OSError, ContractViolationError),
        never_raises=(RuntimeError,),
    ),
    invariant_c=InvariantContract(
        invariants=[_treatment_skill_dir_nonempty, _treatment_fixed_source_nonempty],
        description="治疗执行: skill_dir/fixed_source 不可为空",
    ),
    description="AI 审核模式修复执行契约（消费方 treatment_experience.apply_ai_fix）",
)
class ActiveContract:
    @staticmethod
    def _state_changed(before: dict[str, Any], after: dict[str, Any]) -> bool:
        if before.keys() != after.keys():
            return True
        return any(before[k] is not after[k] for k in before)
    def __init__(self: Self, contract: SkillContract,
                 extra_repairs: list[RepairFn] | RepairFn | None = None) -> None:
        self._contract = contract
        if extra_repairs is None:
            self._extra_repairs: list[RepairFn] = []
        elif isinstance(extra_repairs, (list, tuple)):
            self._extra_repairs = list(extra_repairs)
        elif callable(extra_repairs):
            self._extra_repairs = [extra_repairs]
        else:
            raise TypeError(
                "extra_repairs 必须是修复函数列表、单个修复函数或 None，"
                f"实际为 {type(extra_repairs).__name__}")
        for _idx, _fn in enumerate(self._extra_repairs):
            if not callable(_fn):
                raise TypeError(
                    "extra_repairs 的每个元素都必须是可调用的修复函数，"
                    f"extra_repairs[{_idx}] 实际为 {type(_fn).__name__}")
        self._repair_log: list[str] = []
    def validate_or_repair(self, **kwargs: Any) -> tuple[dict[str, Any], list[str]]:
        return self._validate_or_repair(kwargs, include_output=True)
    def validate_or_repair_inputs(
            self, **kwargs: Any) -> tuple[dict[str, Any], list[str]]:
        return self._validate_or_repair(kwargs, include_output=False)
    def _validate_or_repair(
            self, kwargs: dict[str, Any],
            include_output: bool) -> tuple[dict[str, Any], list[str]]:
        repaired = dict(kwargs)
        self._repair_log.clear()
        repairs: list[tuple[Callable[[dict[str, Any]], dict[str, Any]], str]] = []
        if self._contract.type_c:
            repairs.append((self._contract.type_c.coerce, "type_coerce: 参数类型已自动转换"))
        if self._contract.boundary_c:
            repairs.append((self._contract.boundary_c.truncate,
                            "boundary_truncate: 边界值已自动裁剪"))
        invariant_c = self._contract.invariant_c
        if invariant_c:
            repairs.append((
                lambda state: invariant_c.repair(state, self._extra_repairs),
                "invariant_repair: 不变性已自动修复",
            ))
        for repair, message in repairs:
            before = dict(repaired)
            repaired = repair(repaired)
            if self._state_changed(before, repaired):
                self._repair_log.append(message)
        if include_output:
            residual_violations = self._contract.find_all_violations(**repaired)
        else:
            residual_violations = self._contract.find_input_violations(**repaired)
        return repaired, residual_violations
class ContractRegistry:
    _contracts: ClassVar[dict[str, SkillContract]] = {}
    _active_contracts: ClassVar[dict[str, ActiveContract]] = {}
    _enforce_mode: ClassVar[bool] = True
    @classmethod
    def register(cls, func_name: str, contract: Any) -> None:
        cls._contracts[func_name] = contract
    @classmethod
    def register_active(cls, func_name: str, active: Any) -> None:
        cls._active_contracts[func_name] = active
    @classmethod
    def get(cls, func_name: str) -> Any:
        return cls._contracts.get(func_name)
    @classmethod
    def enforce(cls, func_name: str | None = None, **kwargs: Any) -> bool:
        if not cls._enforce_mode:
            return True
        if func_name is not None:
            return cls._enforce_one(func_name, **kwargs)
        return cls._enforce_all(**kwargs)
    @classmethod
    def _safe_violations(cls, func_name: str, active: ActiveContract | None,
                         contract: Any, kwargs: dict[str, Any]) -> list[str] | None:
        try:
            if active is not None:
                return active.validate_or_repair(**kwargs)[1]
            return contract.find_all_violations(**kwargs)
        except (TypeError, ValueError, AttributeError) as e:
            _log.warning("[ContractRegistry] contract %s validation failed closed: %s",
                         func_name, e)
            return [f"契约验证异常({type(e).__name__}): {e}"]
    @classmethod
    def _enforce_one(cls, func_name: str, **kwargs: Any) -> bool:
        active = cls._active_contracts.get(func_name)
        contract = None if active is not None else cls._contracts.get(func_name)
        if active is None and contract is None:
            return True
        violations = cls._safe_violations(func_name, active, contract, kwargs)
        if violations:
            raise ContractViolationError(f"契约违反({func_name}): {violations}")
        return True
    @classmethod
    def _enforce_all(cls, **kwargs: Any) -> bool:
        for fname in sorted(cls._contracts.keys()
                            | cls._active_contracts.keys()):
            cls._enforce_one(fname, **kwargs)
        return True
def _restore_call_args(cached_sig: inspect.Signature,
                       repaired_kwargs: dict[str, Any]) -> tuple[list[Any], dict[str, Any]]:
    call_kwargs = dict(repaired_kwargs)
    _var_pos_value = _pop_var_pos_capture(cached_sig, call_kwargs)
    pos_args = _collect_positional_args(cached_sig, call_kwargs, _var_pos_value)
    call_kwargs = _merge_varkw_capture(cached_sig, call_kwargs)
    return pos_args, call_kwargs
def _parameter_names(cached_sig: inspect.Signature, kind: Any) -> list[str]:
    return [name for name, param in cached_sig.parameters.items()
            if param.kind is kind]
def _pop_var_pos_capture(cached_sig: inspect.Signature,
                         call_kwargs: dict[str, Any]) -> Any:
    var_pos_names = _parameter_names(
        cached_sig, inspect.Parameter.VAR_POSITIONAL)
    return call_kwargs.pop(var_pos_names[0], ()) if var_pos_names else ()
def _collect_positional_args(cached_sig: inspect.Signature,
                             call_kwargs: dict[str, Any],
                             var_pos_value: Any) -> list[Any]:
    pos_args: list[Any] = []
    pos_only_names = _parameter_names(
        cached_sig, inspect.Parameter.POSITIONAL_ONLY)
    place_pos_or_kw = _needs_positional_placeholders(
        pos_only_names, call_kwargs, var_pos_value)
    for pname, param in cached_sig.parameters.items():
        if param.kind is inspect.Parameter.VAR_POSITIONAL:
            pos_args.extend(var_pos_value)
            continue
        if pname not in call_kwargs:
            continue
        if (param.kind is inspect.Parameter.POSITIONAL_ONLY
                or (param.kind is inspect.Parameter.POSITIONAL_OR_KEYWORD
                    and place_pos_or_kw)):
            pos_args.append(call_kwargs.pop(pname))
    return pos_args
def _needs_positional_placeholders(pos_only_names: list[str],
                                   call_kwargs: dict[str, Any],
                                   var_pos_value: Any) -> bool:
    if var_pos_value:
        return True
    return bool(pos_only_names) and all(
        name in call_kwargs for name in pos_only_names)
def _merge_varkw_capture(cached_sig: inspect.Signature,
                         call_kwargs: dict[str, Any]) -> dict[str, Any]:
    for pname in _parameter_names(cached_sig, inspect.Parameter.VAR_KEYWORD):
        if pname not in call_kwargs:
            continue
        extra = call_kwargs.pop(pname)
        if isinstance(extra, dict):
            call_kwargs.update(extra)
        else:
            call_kwargs[pname] = extra
    return call_kwargs
def _make_contract_wrapper(func: Callable, contract: SkillContract,
                           extra_repairs: list[RepairFn] | None = None) -> Callable:
    func_name = f"{func.__module__}.{func.__qualname__}"
    active = ActiveContract(contract, extra_repairs)
    ContractRegistry.register(func_name, contract)
    ContractRegistry.register_active(func_name, active)
    _cached_sig = inspect.signature(func)
    @wraps(func)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        if not ContractRegistry._enforce_mode:
            return func(*args, **kwargs)
        bound = _cached_sig.bind(*args, **kwargs)
        bound.apply_defaults()
        repaired_kwargs, violations = active.validate_or_repair_inputs(
            **bound.arguments)
        if violations:
            msgs = "; ".join(violations)
            raise ContractViolationError(
                f"契约违反(不可修复): {func_name!r} — {msgs}"
            )
        pos_args, call_kwargs = _restore_call_args(_cached_sig, repaired_kwargs)
        return _call_with_contract(
            func, contract, pos_args, call_kwargs, repaired_kwargs)
    return wrapper
def _call_with_contract(func: Callable, contract: SkillContract,
                        pos_args: list[Any], call_kwargs: dict[str, Any],
                        repaired_kwargs: dict[str, Any]) -> Any:
    try:
        result = func(*pos_args, **call_kwargs)
    except Exception as exc:
        try:
            contract.validate_post(type(exc), **repaired_kwargs)
        except ContractViolationError as violation:
            raise violation from exc
        raise
    contract.validate_post(None, **repaired_kwargs)
    contract.validate_result(result)
    return result
def requires_contract(contract: Any, extra_repairs: Any = None) -> Callable:
    if isinstance(contract, str):
        contract = SkillContract(description=contract)
    def decorator(func: Callable) -> Callable:
        return _make_contract_wrapper(func, contract, extra_repairs)
    return decorator
class EntryGuardError(ValueError):
    pass
class PreconditionError(EntryGuardError):
    pass
def _value_is_empty(value: Any) -> bool:
    return isinstance(value, Sized) and len(value) == 0
class PostconditionError(EntryGuardError):
    pass
def contract_assert(condition: bool, msg: str = "contract violated") -> None:
    if not condition:
        raise PreconditionError(msg)
def require_non_empty(value: Any, name: str = "argument") -> None:
    if value is None:
        raise PreconditionError(f"{name} must not be None")
    if _value_is_empty(value):
        raise PreconditionError(f"{name} must not be empty")
def guard_result(value: Any, predicate: Callable[[Any], bool],
                 msg: str = "invalid result") -> Any:
    if not predicate(value):
        raise PostconditionError(msg)
    return value
def _runtime_checkable(expected: Any) -> Any:
    if expected is Any:
        return object
    origin = getattr(expected, "__origin__", None)
    if origin is Any:
        return object
    if isinstance(origin, type):
        return origin
    if isinstance(expected, tuple):
        return tuple(_runtime_checkable(e) for e in expected)
    if origin is not None or _union_args(expected) is not None:
        reduced = _reduce_union(expected)
        if reduced is not None:
            return reduced
    return expected
def _reduce_union(expected: Any) -> Any:
    args = tuple(a for a in getattr(expected, "__args__", ())
                 if a is not type(None))
    if not args:
        return None
    reduced = tuple(_runtime_checkable(a) for a in args)
    if all(isinstance(r, type) for r in reduced):
        return reduced[0] if len(reduced) == 1 else reduced
    return None
def _runtime_type_matches(value: Any, expected: Any) -> bool:
    if isinstance(expected, tuple):
        return any(_runtime_type_matches(value, member) for member in expected)
    if expected is int and isinstance(value, bool):
        return False
    return isinstance(value, expected)
def _guard_signature(guard_name: str, func: Callable,
                     param_names: Any) -> inspect.Signature:
    sig = inspect.signature(func)
    unknown = [n for n in param_names if n not in sig.parameters]
    if unknown:
        raise ValueError(
            f"{func.__name__}: EntryGuard.{guard_name} 参数名 {unknown} "
            f"不在函数签名中，请修正装饰器配置")
    return sig
class EntryGuard:
    @staticmethod
    def _guarded(func: Callable, guard_name: str, param_names: Any,
                 check: Callable[[str, Any], None]) -> Callable:
        sig = _guard_signature(guard_name, func, param_names)
        @wraps(func)
        def wrapper(*args: Any, **kwargs: Any) -> Any:
            bound = sig.bind(*args, **kwargs)
            bound.apply_defaults()
            for name in param_names:
                check(name, bound.arguments.get(name))
            return func(*args, **kwargs)
        return wrapper
    @staticmethod
    def not_none(*param_names: str) -> Callable:
        def decorator(func: Callable) -> Callable:
            def check(name: str, value: Any) -> None:
                if value is None:
                    raise PreconditionError(
                        f"{func.__name__}: parameter '{name}' must not be None")
                if _value_is_empty(value):
                    raise PreconditionError(
                        f"{func.__name__}: parameter '{name}' must not be empty")
            return EntryGuard._guarded(func, "not_none", param_names, check)
        return decorator
    @staticmethod
    def require_types(**type_map: type) -> Callable:
        def decorator(func: Callable) -> Callable:
            runtime_map = {name: _runtime_checkable(expected)
                           for name, expected in type_map.items()}
            def check(name: str, value: Any) -> None:
                if value is None:
                    return
                expected = runtime_map[name]
                try:
                    type_ok = _runtime_type_matches(value, expected)
                except TypeError:
                    _log.debug(
                        "类型守卫: 注解 %r 不可规约，参数 %s 判定为校验失败",
                        expected, name)
                    type_ok = False
                if not type_ok:
                    raise PreconditionError(
                        f"{func.__name__}: parameter '{name}' must be "
                        f"{getattr(expected, '__name__', str(expected))}, "
                        f"got {type(value).__name__}")
            return EntryGuard._guarded(func, "require_types", type_map, check)
        return decorator
    @staticmethod
    def file_must_exist(*param_names: str) -> Callable:
        def decorator(func: Callable) -> Callable:
            def check(name: str, value: Any) -> None:
                if value is None:
                    return
                try:
                    raw_path = os.fspath(value)
                except TypeError as _e:
                    log_swallowed(__name__, _e,
                                  context='_path_param_check:TypeError')
                    raw_path = str(value)
                path = os.path.abspath(raw_path)
                if not os.path.isfile(path):
                    raise PreconditionError(
                        f"{func.__name__}: file '{name}' does not exist: {path}")
            return EntryGuard._guarded(func, "file_must_exist", param_names, check)
        return decorator
_DEFAULT_TOOL_CATEGORY = "general"
def _schema_mapping(value: Any, label: str) -> dict[str, Any]:
    if value is None:
        return {}
    try:
        return dict(value)
    except (TypeError, ValueError) as exc:
        _log.warning("%s 非映射载体，按空 schema 处理: %s", label, exc)
        return {}
class ToolRegistry:
    _DEFAULT_TIMEOUT_S: float = 30.0
    _DEFAULT_RETRY_COUNT: int = 0
    _MAX_TIMEOUT_S: float = threading.TIMEOUT_MAX
    @dataclass(frozen=True)
    class _Attempt:
        name: str
        func: Callable
        args: tuple[Any, ...]
        kwargs: dict[str, Any]
        timeout: float
    @staticmethod
    def _coerce_timeout(value: Any) -> float:
        default = float(ToolRegistry._DEFAULT_TIMEOUT_S)
        if value is None:
            return default
        if isinstance(value, bool):
            _log.debug("布尔超时值语义不明，按默认处理: %r", value)
            return default
        try:
            v = float(value)
        except (TypeError, ValueError, OverflowError) as _e:
            log_swallowed(__name__, _e, context='_coerce_timeout:TypeError')
            return default
        if not math.isfinite(v):
            log_swallowed(__name__, ValueError(f"非有限超时值: {value!r}"),
                          context='_coerce_timeout:非有限值')
            return default
        if v > ToolRegistry._MAX_TIMEOUT_S:
            log_swallowed(__name__, OverflowError(f"超时超出上界: {value!r}"),
                          context='_coerce_timeout:超上界')
            return ToolRegistry._MAX_TIMEOUT_S
        return v if v > 0 else 0.0
    @staticmethod
    def _coerce_retry_count(value: Any) -> int:
        default = int(ToolRegistry._DEFAULT_RETRY_COUNT)
        if value is None:
            return default
        if isinstance(value, bool):
            _log.debug("布尔重试值语义不明，按默认处理: %r", value)
            return default
        try:
            v = int(value)
        except (TypeError, ValueError, OverflowError) as _e:
            log_swallowed(__name__, _e, context='_coerce_retry_count:TypeError')
            return default
        return max(0, v)
    def __init__(self, skill_name: str = ""):
        self.skill_name = skill_name
        self._tools: dict[str, dict[str, Any]] = {}
        self._stat_lock = threading.Lock()
    def register(self, name: str, func: Callable,
                 description: str = "",
                 category: str = _DEFAULT_TOOL_CATEGORY,
                 input_schema: dict[str, Any] | None = None,
                 output_schema: dict[str, Any] | None = None,
                 timeout: float | None = None,
                 retry_count: int | None = None,
                 tags: list[str] | None = None) -> None:
        if not callable(func):
            raise TypeError(
                f"工具 {name!r} 的 func 必须可调用，"
                f"实际为 {type(func).__name__}")
        params = self._describe_params(name, func)
        timeout = self._coerce_timeout(timeout)
        retry_count = self._coerce_retry_count(retry_count)
        self._tools[name] = {
            "name": name, "func": func, "description": description,
            "category": category, "params": params,
            "input_schema": _schema_mapping(
                input_schema, f"ToolRegistry.{name}.input_schema"),
            "output_schema": _schema_mapping(
                output_schema, f"ToolRegistry.{name}.output_schema"),
            "timeout": timeout, "retry_count": retry_count,
            "tags": _norm_str_items(tags, "ToolRegistry.tags") or [],
            "call_count": 0, "error_count": 0,
        }
    @staticmethod
    def _describe_params(name: str, func: Callable) -> list[dict[str, Any]]:
        try:
            sig = inspect.signature(func)
        except (TypeError, ValueError) as exc:
            _log.warning(
                "[ToolRegistry] 工具 %r 无可提取签名，参数表降级为空: %s",
                name, exc)
            return []
        return [
            {
                "name": pname,
                "type": (getattr(param.annotation, "__name__", None)
                         or str(param.annotation)
                         if param.annotation is not inspect.Parameter.empty
                         else "Any"),
                "default": (str(param.default)
                            if param.default is not inspect.Parameter.empty
                            else None),
            }
            for pname, param in sig.parameters.items()
        ]
    def list_tools(self) -> list[str]:
        return list(self._tools.keys())
    def get_tool(self, name: str) -> dict[str, Any] | None:
        return self._tools.get(name)
    def call(self, name: str, *args: Any, **kwargs: Any) -> Any:
        info = self._tools.get(name)
        if info is None:
            raise KeyError(
                f"工具未注册: {name!r}（已注册: {self.list_tools()}）")
        func: Callable = info["func"]
        timeout = self._coerce_timeout(info.get("timeout"))
        attempts = self._coerce_retry_count(info.get("retry_count")) + 1
        attempt = self._Attempt(name, func, args, kwargs, timeout)
        for attempt_index in range(1, attempts + 1):
            self._bump(info, "call_count")
            try:
                if timeout <= 0:
                    return func(*args, **kwargs)
                result, timeout_exc = self._run_timed_attempt(info, attempt)
            except Exception:
                self._bump(info, "error_count")
                if attempt_index >= attempts:
                    raise
                continue
            if timeout_exc is None:
                return result
            if attempt_index >= attempts:
                raise timeout_exc
        raise AssertionError("工具调用循环必须返回结果或抛出异常")
    def _bump(self, info: dict[str, Any], key: str) -> None:
        with self._stat_lock:
            info[key] += 1
    def _run_timed_attempt(
        self, info: dict[str, Any], attempt: _Attempt,
    ) -> tuple[Any, TimeoutError | None]:
        executor = ThreadPoolExecutor(
            max_workers=1, thread_name_prefix="tool-registry")
        try:
            fut = executor.submit(
                attempt.func, *attempt.args, **attempt.kwargs)
            try:
                return fut.result(timeout=attempt.timeout), None
            except (TimeoutError, FuturesTimeout) as _e:
                if fut.done() and not fut.cancelled():
                    return fut.result(), None
                fut.cancel()
                log_swallowed(__name__, _e, context='ToolRegistry.call:TimeoutError')
                self._bump(info, "error_count")
                return None, TimeoutError(
                    f"工具 {attempt.name!r} 执行超时（>{attempt.timeout}s）")
        finally:
            executor.shutdown(wait=False)
    def register_decorated(self, func: Callable) -> ToolRegistry:
        meta = getattr(func, "_tool_meta", None)
        if not isinstance(meta, dict):
            raise TypeError(
                f"函数 {getattr(func, '__name__', repr(func))} 未被 @tool 装饰器标记")
        self.register(
            str(meta.get("name") or getattr(func, "__name__", repr(func))),
            func,
            description=str(meta.get("description") or ""),
            category=str(meta.get("category") or _DEFAULT_TOOL_CATEGORY),
            tags=_norm_str_items(
                meta.get("tags"), "ToolRegistry.register_decorated.tags") or [],
        )
        return self
def tool(name: str | None = None, description: str = "",
         category: str = _DEFAULT_TOOL_CATEGORY,
         tags: list[str] | None = None) -> Any:
    def decorator(func: Any) -> Any:
        func._tool_meta = {
            "name": name or getattr(func, "__name__", repr(func)),
            "description": description or (getattr(func, "__doc__", "") or ""),
            "category": category,
            "tags": _norm_str_items(tags, "tool.tags") or [],
        }
        return func
    return decorator
DEFAULT_PROJECT_ROOT = "."
_DEFAULT_CLI_ERROR_CODE = 1
JSON_REPORT_ERRORS = (OSError, TypeError, ValueError, RecursionError)
def exit_code_of(result: Any) -> int:
    if isinstance(result, int) and not isinstance(result, bool):
        return result
    return 0
def fail_cli(tag: str, message: str, detail: str | None = None,
             cause: BaseException | None = None, *, code: int = _DEFAULT_CLI_ERROR_CODE,
             hint: str = "") -> NoReturn:
    _log.error("[cli:%s] %s", tag,
               detail if detail is not None else message)
    print(f"[ERROR] {message}")
    if hint:
        print(f"  {hint}")
    raise SystemExit(code) from cause
def require_dict(value: Any, tag: str, label: str) -> dict:
    if not isinstance(value, dict):
        fail_cli(tag, f"{label}必须是 dict（契约违约）: {type(value).__name__}")
    return value
def run_cli_action(tag: str, label: str, action: Callable[..., Any],
                   /, *args: Any, code: int = _DEFAULT_CLI_ERROR_CODE,
                   verbose: bool = False,
                   **kwargs: Any) -> Any:
    try:
        return action(*args, **kwargs)
    except Exception as e:
        if verbose:
            _log.exception("%s failed", tag)
            traceback.print_exc()
        fail_cli(tag, f"{label}: {e}", cause=e, code=code)
def cli_boundary(tag: str, label: str):
    def deco(fn):
        @wraps(fn)
        def wrapper(*args: Any, **kwargs: Any):
            return run_cli_action(tag, label, lambda: fn(*args, **kwargs))
        return wrapper
    return deco
def require_dir(path: Any, tag: str) -> None:
    if not os.path.isdir(path):
        fail_cli(tag, f"目录不存在: {path}")
def require_file(path: Any, tag: str) -> None:
    if not os.path.isfile(path):
        fail_cli(tag, f"文件不存在: {path}")
def finish_cli_command(cli_tag: str, command: str, started: float, *,
                       ok: bool, outcome: str, message: str,
                       run_fields: dict | None = None) -> NoReturn:
    log_fn = _log.info if ok else _log.warning
    log_fn("[cli:%s] %s", cli_tag, message)
    trace_module_run(
        "__main__", command, started, outcome=outcome, **(run_fields or {}))
    raise SystemExit(0 if ok else _DEFAULT_CLI_ERROR_CODE)
def logged_cli_command(entry: str):
    def deco(fn):
        @wraps(fn)
        def wrapper(args: argparse.Namespace):
            started = time.monotonic()
            outcome = "ok"
            try:
                result = fn(args)
            except SystemExit as e:
                outcome = "ok" if e.code in (0, None) else "error"
                raise
            except BaseException:
                outcome = "error"
                raise
            else:
                if exit_code_of(result) != 0:
                    outcome = "error"
                return result
            finally:
                trace_module_run(
                    "__main__", entry, started, outcome=outcome, command=entry)
        return wrapper
    return deco
def get_cli_report_dir() -> str:
    report_dir = os.path.join(
        get_temp_base(os.path.dirname(os.path.abspath(__file__))), "reports")
    os.makedirs(report_dir, exist_ok=True)
    return report_dir
def resolve_report_path(args: argparse.Namespace, default_name: str) -> str:
    return (getattr(args, "output", None)
            or os.path.join(get_cli_report_dir(), default_name))
def write_json_payload(data, json_path: str) -> None:
    if not os.path.isdir(os.path.dirname(os.path.abspath(json_path))):
        raise FileNotFoundError(2, "No such file or directory", json_path)
    write_json_artifact(json_path, data, indent=2)
def load_json_file(tag: str, path: str, missing_label: str,
                   parse_label: str, *, code: int = _DEFAULT_CLI_ERROR_CODE):
    if not os.path.isfile(path):
        fail_cli(tag, f"{missing_label}: {path}", code=code)
    try:
        with open(path, encoding="utf-8-sig") as f:
            return json.load(f)
    except (OSError, ValueError, RecursionError) as e:
        fail_cli(tag, f"{parse_label}: {e}", cause=e, code=code)
def dump_json_report(data, json_path: str) -> bool:
    try:
        write_json_payload(data, json_path)
        print(f"\n[JSON -> {json_path}]")
        return True
    except JSON_REPORT_ERRORS as e:
        _log.error("[cli] JSON 报告写盘失败: %s", e)
        print(f"[ERROR] JSON 报告写盘失败: {e}")
        return False
def json_text(data) -> str:
    return json.dumps(data, indent=2, ensure_ascii=False, default=str)
def emit_json_report(data, output: str | None = None) -> bool:
    if output:
        if dump_json_report(data, output):
            return True
        raise SystemExit(2)
    print(json_text(data))
    return True
def promote_single_dir(project_root: str, entries):
    if (project_root in ("", DEFAULT_PROJECT_ROOT)
            and isinstance(entries, list) and len(entries) == 1):
        candidate = entries[0]
        if isinstance(candidate, str) and os.path.isdir(candidate):
            return candidate, []
    return project_root, entries
def resolve_project_root(args: argparse.Namespace, tag: str) -> str:
    project_root = getattr(args, "project", None)
    if project_root is None:
        project_root = DEFAULT_PROJECT_ROOT
    promoted_root, promoted_paths = promote_single_dir(
        project_root, getattr(args, "paths", None))
    project_root = promoted_root
    if isinstance(promoted_paths, list):
        args.paths = promoted_paths
    if not os.path.isdir(project_root):
        fail_cli(tag, f"项目目录不存在: {project_root}")
    return project_root
def split_csv(raw) -> list[str]:
    if isinstance(raw, Mapping):
        return []
    if isinstance(raw, (list, tuple)):
        items: list[str] = []
        for item in raw:
            items.extend(split_csv(item))
        return items
    if isinstance(raw, (set, frozenset)):
        items = []
        for item in sorted(raw, key=str):
            items.extend(split_csv(item))
        return items
    if isinstance(raw, (bytes, bytearray)):
        text = bytes(raw).decode("utf-8", "replace")
    else:
        text = "" if raw is None else str(raw)
    return [item.strip() for item in text.split(",") if item.strip()]
def parse_csv_option(value) -> list[str] | None:
    if value is None or isinstance(value, Mapping):
        return None
    if isinstance(value, (list, tuple, set, frozenset)):
        return split_csv(value) or None
    if not str(value).strip():
        return None
    return split_csv(value) or None
def num_of(value: Any) -> float | int:
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return value
    return 0
_MAPPING_CONVERTERS = ("_asdict", "to_dict")
def _converter_mapping(value: Any) -> dict | None:
    for method_name in _MAPPING_CONVERTERS:
        try:
            converter = getattr(value, method_name, None)
            if not callable(converter):
                continue
            mapped = converter()
        except Exception as exc:
            _log.debug("载荷 %s() 失败，尝试下一归一通道: %s",
                       method_name, exc)
            continue
        if isinstance(mapped, Mapping):
            return dict(mapped)
    return None
def _public_attr_mapping(value: Any) -> dict:
    attrs = getattr(value, '__dict__', None)
    if not isinstance(attrs, dict):
        return {}
    return {key: val for key, val in attrs.items() if not key.startswith('_')}
def to_mapping(value: Any) -> dict:
    if isinstance(value, dict):
        return dict(value)
    if isinstance(value, Mapping):
        return dict(value)
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        return {f.name: getattr(value, f.name) for f in dataclasses.fields(value)}
    mapped = _converter_mapping(value)
    return mapped if mapped is not None else _public_attr_mapping(value)
def norm_list(value: Any) -> list:
    if isinstance(value, list):
        return list(value)
    if isinstance(value, (set, frozenset)):
        return sorted(value, key=str)
    if isinstance(value, tuple):
        return list(value)
    if (isinstance(value, Iterable)
            and not isinstance(value, (str, bytes, bytearray, Mapping))):
        try:
            return list(value)
        except Exception as exc:
            _log.debug("norm_list: 可迭代物化失败，降级空列表: %s", exc)
    return []
def norm_warnings(value: Any) -> list:
    if isinstance(value, (str, Mapping)):
        return [value]
    if isinstance(value, (set, frozenset)):
        return sorted(value, key=str)
    if isinstance(value, (list, tuple)):
        return list(value)
    if (isinstance(value, Iterable)
            and not isinstance(value, (bytes, bytearray))):
        try:
            return list(value)
        except Exception as exc:
            _log.debug("norm_warnings: 可迭代物化失败，降级空列表: %s", exc)
    return []
def field_of(data: dict, key: str, default: Any = 0) -> Any:
    value = data.get(key)
    return default if value is None else value
def norm_display(value: Any) -> Any:
    return "?" if value is None else value
def dump_json_report_checked(path: str, payload: dict, cli_tag: str) -> None:
    try:
        write_json_payload(payload, path)
    except JSON_REPORT_ERRORS as e:
        fail_cli(cli_tag, f"报告写入失败: {e}", code=2)
    print(f"JSON 报告已写入: {path}")

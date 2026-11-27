from __future__ import annotations

import datetime
import json
import keyword
import math
import os
import re
import time
from collections.abc import Callable, Iterable, Mapping
from decimal import Decimal
from typing import Any

from jwsgj.diag_types_vocab import (
    ALL_FAMILY_KEYS,
    ANTIPATTERN_PREFIXES,
    CONF_VERY_HIGH,
    DEFAULT_CONFIDENCE_FALLBACK,
    FIELD_RECOMMENDATIONS,
    FINDING_LIST_KEYS,
    OUTPUT_TRUNCATE_LEN,
    SEVERITY_PENALTY_WEIGHTS,
    SEVERITY_RANK,
    SIGNAL_DEGRADE_FACTOR,
    SOURCE_SEQUENCE_TYPES,
)
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.runtime_scope import canonical_path

logger = get_module_logger(__name__)
def safe_dict_get(mapping, key, default=None):
    try:
        return mapping.get(key, default)
    except (AttributeError, TypeError) as _e:
        log_swallowed(__name__, _e, context=f'safe_dict_get:{type(_e).__name__}')
        return default
def conf_chain(f: dict, *keys, default: float = 0.0) -> float:
    if not isinstance(f, dict):
        return default
    for k in keys:
        v = f.get(k)
        if is_real_number(v):
            return v
    return default
def is_default_confidence(f: dict) -> bool:
    _src = dict_or_empty(f).get("_confidence_source", "default")
    return not isinstance(_src, str) or _src == "default"
def is_valid_fp_rate(value) -> bool:
    return is_real_number(value) and 0.0 <= value <= 1.0
def degrade_factor_of(f: dict) -> float:
    _df = dict_or_empty(f).get(SIGNAL_DEGRADE_FACTOR, CONF_VERY_HIGH)
    _v = safe_float(_df, None)
    if _v is None:
        return CONF_VERY_HIGH
    return clamp_unit(_v)
def str_or(value: Any, default: str = "") -> str:
    return value if isinstance(value, str) else default
def coerce_path_str(value: object) -> str:
    if isinstance(value, (os.PathLike, bytes)):
        try:
            value = os.fspath(value)
            if isinstance(value, bytes):
                value = os.fsdecode(value)
        except (TypeError, ValueError, OSError) as exc:
            log_swallowed(
                __name__, exc,
                context=f"coerce_path_str:{type(exc).__name__}")
            return ""
    return value if isinstance(value, str) else ""
def dict_or_empty(value: Any) -> dict:
    return value if isinstance(value, dict) else {}
def require_dict(value: Any, label: str) -> dict:
    if not isinstance(value, dict):
        raise TypeError(f"{label}格式非法: {type(value).__name__}")
    return value
def int_or(value: Any, default: int = 0) -> int:
    if isinstance(value, bool) or value is None:
        return default
    if not isinstance(value, (int, float, str)):
        return default
    try:
        return int(value)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context="int_or:coerce")
        return default
def int_metric(value: Any, default: int = 0) -> int:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return default
    if isinstance(value, int):
        return value if value >= 0 else default
    if not math.isfinite(value) or value < 0:
        return default
    return int(value)
def ratio01(value: Any, default: float = 0.0) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return default
    if isinstance(value, int):
        return float(min(1, max(0, value)))
    if not math.isfinite(value):
        return default
    return min(1.0, max(0.0, value))
def float_metric(value: Any, default: float = 0.0) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return default
    try:
        metric = float(value)
    except OverflowError as _e:
        log_swallowed(__name__, _e, context="float_metric:OverflowError")
        return default
    return metric if math.isfinite(metric) else default
def as_declared(value: Any, expected: type) -> Any:
    if expected is int:
        if not is_finite_num(value):
            return 0
        try:
            return int(value)
        except (TypeError, ValueError, OverflowError) as _e:
            log_swallowed(__name__, _e, context="as_declared:int")
            return 0
    if expected in (list, dict, str):
        return value if isinstance(value, expected) else expected()
    return value if value is not None else expected()
def append_judgment(report: dict, key: str, status: str, label: str) -> bool:
    if not isinstance(report, dict):
        return False
    judgments = report.get("judgments")
    if not isinstance(judgments, list):
        judgments = []
        report["judgments"] = judgments
    for j in judgments:
        if isinstance(j, dict) and j.get("key") == key:
            return False
    judgments.append({"key": key, "status": status, "label": label})
    return True
def judgment_dicts(judgments: Any) -> list[dict]:
    return [j for j in strict_iterable_list(judgments) if isinstance(j, dict)]
def judgment_str_fields(j: dict) -> tuple[str, str, str]:
    if not isinstance(j, dict):
        return ("", "", "")
    return (str(j.get("key") or ""), str(j.get("label") or ""),
            str(j.get("status") or ""))
def recommendations_list(report: dict) -> list:
    if not isinstance(report, dict):
        return []
    value = report.get(FIELD_RECOMMENDATIONS)
    if isinstance(value, list):
        return value
    normalized = normalize_list_field(value)
    report[FIELD_RECOMMENDATIONS] = normalized
    return normalized
def append_recommendation_once(report: dict, text: str) -> bool:
    if not isinstance(report, dict):
        return False
    recommendations = recommendations_list(report)
    if text in recommendations:
        return False
    recommendations.append(text)
    return True
def _finite_number(v: Any):
    if isinstance(v, bool):
        return None
    if isinstance(v, int):
        return v
    if isinstance(v, float) and math.isfinite(v):
        return v
    return None
as_count = int_metric
def count_tasks(value: Any, *, clamp_negative: bool = True) -> int | None:
    if value is None:
        return 0
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        number = value
    elif isinstance(value, str):
        try:
            number = float(value)
        except (TypeError, ValueError, OverflowError) as _e:
            log_swallowed(__name__, _e, context='count_tasks:ValueError')
            return None
    else:
        return None
    try:
        if not math.isfinite(number):
            return None
    except OverflowError as _e:
        log_swallowed(__name__, _e, context='count_tasks:OverflowError')
        return None
    if number < 0 and not clamp_negative:
        return None
    return max(0, int(number))
def len_safe(raw: object) -> int:
    return len(raw) if isinstance(raw, (list, tuple, set, dict)) else 0
def dict_items(value: object) -> list[dict]:
    if not isinstance(value, (list, tuple)):
        return []
    return [item for item in value if isinstance(item, dict)]
def as_pure_count(v: Any) -> int:
    count = integral_count(v)
    return max(0, count) if count is not None else 0
def as_number(v: Any, default: float = 0.0) -> float:
    n = _finite_number(v)
    return default if n is None else n
def is_number(value: Any) -> bool:
    return not isinstance(value, bool) and isinstance(value, (int, float))
def numeric_or(value: Any, default: Any) -> Any:
    return value if is_real_number(value) else default
_PASSED_FALSE_TEXT = frozenset({
    "false", "0", "no", "off", "fail", "failed", "failure", "error",
    "n", "", "未通过", "不通过", "失败", "否",
})
_PASSED_TRUE_TEXT = frozenset({
    "true", "1", "yes", "on", "pass", "passed", "success",
    "succeeded", "successful", "y", "通过", "成功", "是",
})
def normalize_passed(passed) -> bool:
    if passed is None:
        return True
    if isinstance(passed, bool):
        return passed
    if isinstance(passed, (int, float)):
        number = safe_float(passed, None)
        return number is not None and number != 0.0
    text = safe_text(passed).strip().lower()
    if text in _PASSED_FALSE_TEXT:
        return False
    if text in _PASSED_TRUE_TEXT:
        return True
    number = safe_float(text, None)
    if number is None:
        log_swallowed(
            __name__, ValueError(f"无法判定的 passed 值: {text!r}"),
            context="normalize_passed:ValueError",
        )
        return False
    return number != 0.0
def finite_float_or_none(value: Any) -> float | None:
    if not is_number(value):
        return None
    try:
        number = float(value)
    except (OverflowError, ValueError) as _e:
        log_swallowed(__name__, _e, context="finite_float_or_none:float")
        return None
    return number if math.isfinite(number) else None
def as_entry_list(value: Any) -> list:
    return list(value) if isinstance(value, (list, tuple)) else []
def normalize_execute_timeout(timeout: Any, default: float) -> float:
    if timeout is not None and finite_float_or_none(timeout) is None:
        logger.warning(
            "execute timeout 非法或非有限: %r，回退默认 %ss", timeout, default)
    return coerce_timeout(timeout, default, allow_zero=True)
_METHOD_STATUS_DETAIL_ALIASES: dict[str, str] = {
    "pass": "pass", "passed": "pass", "ok": "pass",
    "success": "pass", "succeeded": "pass", "successful": "pass",
    "completed": "pass", "complete": "pass", "done": "pass",
    "warn": "warn", "warning": "warn", "warned": "warn",
    "fail": "fail", "failed": "fail", "failure": "fail",
    "failures": "fail",
    "timeout": "timeout", "timed_out": "timeout",
    "error": "error", "errors": "error",
    "skip": "skip", "skipped": "skip",
    "corrupted": "corrupted", "corrupt": "corrupted",
}
def method_status_detail(status: Any) -> str:
    if not isinstance(status, str):
        return "corrupted"
    text = status.strip().lower()
    return _METHOD_STATUS_DETAIL_ALIASES.get(text, "corrupted")
def method_status_bucket(status: Any) -> str | None:
    detail = method_status_detail(status)
    if detail in ("pass", "warn"):
        return "completed"
    if detail in ("fail", "timeout", "error"):
        return "failed"
    if detail == "skip":
        return "skipped"
    return None
_YAML11_SCALAR_LITERALS = frozenset({
    "true", "false", "yes", "no", "on", "off", "null", "~",
})
_YAML11_INT_RE = re.compile(
    r"[-+]?(?:0b[0-1_]+|0[0-7_]+|0x[0-9a-fA-F_]+|0|[1-9][0-9_]*"
    r"|[1-9][0-9_]*(?::(?=[0-5]?[0-9])[0-5]?[0-9])+)"
)
_YAML11_FLOAT_RE = re.compile(
    r"(?:[-+]?[0-9][0-9_]*\.[0-9_]*(?:[eE][-+]?[0-9]+)?"
    r"|[-+]?[0-9][0-9_]*(?:[eE][-+]?[0-9]+)"
    r"|\.[0-9_]+(?:[eE][-+]?[0-9]+)?"
    r"|[-+]?\.(?:inf|Inf|INF)|\.(?:nan|NaN|NAN)"
    r"|[-+]?[0-9][0-9_]*(?::[0-5]?[0-9])+(?:\.[0-9_]*)?)"
)
_YAML11_TIMESTAMP_RE = re.compile(
    r"[0-9]{4}-[0-9]{2}-[0-9]{2}"
    r"|[0-9]{4}-[0-9]{1,2}-[0-9]{1,2}(?:[Tt]|[ \t]+)[0-9]{1,2}"
    r"(?::[0-9]{2}(?::[0-9]{2}(?:\.[0-9]*)?)?)?"
    r"(?:[ \t]*(?:Z|[-+][0-9]{1,2}(?::[0-9]{2})?))?"
)
_YAML_UNPRINTABLE_RE = re.compile(
    "[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f"
    "\ud800-\udfff\u2028\u2029\ufffe\uffff]"
)
_YAML_LINESEP_RE = re.compile("\r\n|[\r\x85\u2028\u2029]")
def _yaml_escape_unprintable(match) -> str:
    cp = ord(match.group())
    return f"\\x{cp:02x}" if cp <= 0xFF else f"\\u{cp:04x}"
def _yaml11_scalar_metamorphoses(value: str) -> bool:
    return (value.lower() in _YAML11_SCALAR_LITERALS
            or _YAML11_INT_RE.fullmatch(value) is not None
            or _YAML11_FLOAT_RE.fullmatch(value) is not None
            or _YAML11_TIMESTAMP_RE.fullmatch(value) is not None)
def yaml_safe_quote(value: str) -> str:
    if not value:
        return '""'
    if _yaml_needs_quote(value):
        escaped = (value.replace('\\', '\\\\')
                       .replace('"', '\\"')
                       .replace('\n', '\\n')
                       .replace('\r', '\\r')
                       .replace('\t', '\\t'))
        escaped = _YAML_UNPRINTABLE_RE.sub(_yaml_escape_unprintable, escaped)
        return f'"{escaped}"'
    return value
def _yaml_needs_quote(value: str) -> bool:
    if not value:
        return True
    return (_yaml11_scalar_metamorphoses(value)
            or value == "="
            or re.search(r'["#:|><\n\r\t]', value) is not None
            or _YAML_UNPRINTABLE_RE.search(value) is not None
            or value[0] in "-*&!%@`[]{}'\"?, \t"
            or value[-1] in " \t")
def yaml_safe_desc_line(desc: str) -> str:
    desc = desc or ""
    if _YAML_LINESEP_RE.search(desc):
        desc = _YAML_LINESEP_RE.sub("\n", desc)
    if _YAML_UNPRINTABLE_RE.search(desc):
        desc = _YAML_UNPRINTABLE_RE.sub("", desc)
    desc = desc.lstrip()
    if not desc:
        return 'description: ""'
    indented = "\n  ".join(desc.split("\n"))
    return f'description: |\n  {indented}'
def escape_dq_text(text: str) -> str:
    return text.replace('\\', '\\\\').replace('"', '\\"')
def escape_dq_inline(text: str) -> str:
    return (escape_dq_text(text)
            .replace('\r', '\\r').replace('\n', '\\n'))
def is_pure_int(v) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)
def is_finite_num(v) -> bool:
    if isinstance(v, bool):
        return False
    if isinstance(v, int):
        return True
    return isinstance(v, float) and math.isfinite(v)
FALSE_SIGNAL_TEXT: frozenset[str] = frozenset(
    {"", "0", "false", "no", "none", "null"})
def signal_bool(value) -> bool:
    if isinstance(value, Decimal):
        return safe_isfinite(value) and value != 0
    if isinstance(value, float):
        return math.isfinite(value) and value != 0.0
    if not isinstance(value, str):
        return bool(value)
    text = value.strip().lower()
    if text in FALSE_SIGNAL_TEXT:
        return False
    try:
        number = float(text)
    except (TypeError, ValueError):  # jwsgj:silent-ok
        return True
    return math.isfinite(number) and number != 0.0
def cv_int(v) -> int:
    count = integral_count(v)
    return 0 if count is None else count
def str_or_empty(v) -> str:
    if isinstance(v, str):
        return v
    return str(v) if v else ""
def text_or_empty(value: Any) -> str:
    if value is None:
        return ""
    return value if isinstance(value, str) else str(value)
def strip_bom(content: str) -> str:
    if not isinstance(content, str):
        return content
    if content.startswith("\ufeff"):
        return content[1:]
    return content
def safe_short_text(value: Any, limit: int = 50) -> str:
    try:
        text = value if isinstance(value, str) else repr(value)
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context='safe_short_text:repr')
        return f"<{type(value).__name__}>"
    return text[:limit]
def safe_text(value: Any, limit: int | None = None) -> str:
    try:
        text = str(value)
    except RecursionError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='safe_text:RecursionError')
        text = f"<recursion {type(value).__name__}>"
    except Exception as _exc:  # noqa: BLE001
        log_swallowed(__name__, _exc, context='safe_text:Exception')
        text = f"<unprintable {type(value).__name__}>"
    return text[:limit] if limit is not None else text
_PLACEHOLDER_RULE_ID = "UNKNOWN"
def is_placeholder_rule_id(rule_id) -> bool:
    if not isinstance(rule_id, str):
        return True
    text = rule_id.strip()
    return not text or text.upper() == _PLACEHOLDER_RULE_ID
def strip_cv_target_prefix(target_id: str) -> str:
    if not isinstance(target_id, str):
        target_id = str(target_id or "")
    if target_id.startswith("CV-CONFIDENCE-"):
        return target_id[len("CV-CONFIDENCE-"):]
    if target_id.startswith("CV-"):
        return target_id[3:]
    return target_id
as_dict = dict_or_empty
def coerce_mapping(item: Any) -> dict | None:
    if isinstance(item, Mapping):
        return dict(item)
    for attr in ('to_dict', '_asdict'):
        method = getattr(item, attr, None)
        if not callable(method):
            continue
        try:
            projected = method()
        except Exception as _exc:  # noqa: BLE001
            log_swallowed(__name__, _exc,
                          context=f'coerce_mapping:{attr}')
            continue
        if isinstance(projected, dict):
            return dict(projected)
    if hasattr(item, '__dict__'):
        try:
            return dict(item.__dict__)
        except (TypeError, ValueError) as _exc:
            log_swallowed(__name__, _exc,
                          context='coerce_mapping:__dict__')
    return None
def as_list(value) -> list:
    return value if isinstance(value, list) else []
def has_finding_entries(value: object) -> bool:
    return isinstance(value, list) and any(
        isinstance(item, dict) for item in value)
def section_dict(report: Any, key, default: dict | None = None) -> dict:
    section = report.get(key) if isinstance(report, dict) else None
    return section if isinstance(section, dict) and section else dict_or_empty(default)
def unwrap_cv_results(cv_results: dict) -> dict:
    if not isinstance(cv_results, dict):
        return {}
    report = cv_results.get("report")
    if isinstance(report, dict):
        merged = dict(report)
        merged.update({k: v for k, v in cv_results.items() if k != "report"})
        return merged
    return cv_results
def num(section: Any, key, default=0) -> float:
    if not isinstance(section, dict):
        return default
    return as_number(section.get(key, default), default)
def normalize_list_field(value) -> list:
    if isinstance(value, list):
        return value
    if value is None:
        return []
    if isinstance(value, (str, bytes, bytearray, Mapping)):
        return [value]
    if hasattr(value, "__iter__"):
        try:
            return list(value)
        except TypeError as _e:  # pragma: no cover
            log_swallowed(__name__, _e, context='normalize_list_field:TypeError')
            return [value]
    return [value]
def _ordered_items(value: Iterable) -> list:
    if isinstance(value, (set, frozenset)):
        return sorted(value, key=repr)
    return list(value)
def strict_iterable_list(value: Any) -> list:
    if isinstance(value, (str, bytes, bytearray, dict)):
        return []
    if not hasattr(value, "__iter__"):
        return []
    try:
        return _ordered_items(value)
    except TypeError as _e:
        log_swallowed(__name__, _e, context="strict_iterable_list:TypeError")
        return []
def as_sequence(value) -> list:
    if isinstance(value, str):
        return [value]
    if isinstance(value, (list, tuple, set, frozenset)):
        return _ordered_items(value)
    return []
def normalize_sources(raw) -> list:
    if isinstance(raw, str):
        return [raw] if raw else []
    if isinstance(raw, (Mapping, bytes, bytearray)):
        return []
    if not isinstance(raw, SOURCE_SEQUENCE_TYPES):
        if not hasattr(raw, "__iter__"):
            return []
        try:
            raw = list(raw)
        except TypeError as _e:
            log_swallowed(__name__, _e,
                          context="normalize_sources:materialize")
            return []
    return [value for value in _ordered_items(raw) if isinstance(value, str)]
def clean_str_list(value) -> list:
    return [c.strip() for c in as_list(value)
            if isinstance(c, str) and c.strip()]
def coerce_text_list(value: Any) -> list[str]:
    if isinstance(value, Mapping):
        return []
    if isinstance(value, (str, bytes, bytearray)):
        if not value:
            return []
        if isinstance(value, str):
            return [value]
        return [bytes(value).decode("utf-8", "replace")]
    if not isinstance(value, (list, tuple, set, frozenset)):
        if not hasattr(value, "__iter__"):
            return [safe_str(value)] if value else []
        try:
            value = list(value)
        except TypeError as _e:
            log_swallowed(__name__, _e,
                          context="coerce_text_list:materialize")
            return [safe_str(value)] if value else []
    return [safe_str(item) for item in value if item is not None]
def normalize_str_seq(value: Any) -> tuple[str, ...]:
    return tuple(norm_str_list(value))
def source_id_text(value: object) -> str:
    return value.strip() if isinstance(value, str) else ""
def clean_source_ids(sources) -> list[str]:
    if not isinstance(sources, SOURCE_SEQUENCE_TYPES):
        return []
    cleaned: list[str] = []
    seen: set[str] = set()
    for source in _ordered_items(sources):
        source_id = source_id_text(source)
        if not source_id or source_id in seen:
            continue
        seen.add(source_id)
        cleaned.append(source_id)
    return cleaned
as_str = str_or_empty
def as_num(v: Any) -> int | float:
    if isinstance(v, bool):
        return 0
    if isinstance(v, int):
        return v
    if not isinstance(v, (float, str)):
        return 0
    try:
        num = float(v)
    except (TypeError, ValueError) as _e:
        log_swallowed(__name__, _e, context='as_num:TypeError')
        return 0
    return num if math.isfinite(num) else 0
def safe_float(value: Any, default: float | None = 0.0) -> float | None:
    if value is None or isinstance(value, bool):
        return default
    try:
        parsed = float(value)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context='safe_float:TypeError')
        return default
    return parsed if math.isfinite(parsed) else default
def meta_num(value: Any) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return 0.0
    try:
        number = float(value)
    except OverflowError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='meta_num:OverflowError')
        return 0.0
    return number if math.isfinite(number) else 0.0
def float_field(item: dict, key: str, default: float = 0.0) -> float:
    return float_metric(dict_or_empty(item).get(key, default), default)
def list_field(item: dict, key: str) -> list:
    return as_list(dict_or_empty(item).get(key, []))
def plan_index(value) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float) and value.is_integer():
        return int(value)
    if isinstance(value, str):
        try:
            return int(value.strip())
        except ValueError as _e:
            log_swallowed(__name__, _e, context='plan_index:ValueError')
            return None
    return None
def norm_rule_id(value) -> str:
    return str(value or "unknown").strip() or "unknown"
def now_iso() -> str:
    return datetime.datetime.now().isoformat(timespec="seconds")
def as_item_list(items, *, log_tag: str) -> list:
    if items is None:
        return []
    if isinstance(items, (str, bytes, bytearray, Mapping)):
        logger.warning(
            "%s items 非列表形态(%s)，按空清单处理",
            log_tag, type(items).__name__,
        )
        return []
    try:
        return list(items)
    except TypeError:
        logger.warning(
            "%s items 不可迭代(%s)，按空清单处理",
            log_tag, type(items).__name__,
        )
        return []
normalize_file_ref = str_or_empty
def coerce_tolerance(raw: Any, default: float = 5.0) -> float:
    if isinstance(raw, bool) or raw is None:
        return default
    if not isinstance(raw, (int, float, str)):
        return default
    try:
        tolerance = float(raw)
    except (TypeError, ValueError, OverflowError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='coerce_tolerance:TypeError+')
        return default
    return max(0.0, tolerance) if math.isfinite(tolerance) else default
def coerce_timeout(value: Any, default: float, *,
                   allow_zero: bool = False) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return default
    timeout = safe_float(value, None)
    if timeout is None:
        return default
    if timeout > 0:
        return timeout
    return 0.0 if allow_zero and timeout == 0 else default
def normalize_success_rate(value: Any) -> float:
    if not is_finite_num(value):
        return 0.0
    if value < 0.0 or value > 100.0:
        return 0.0
    if value > 1.0:
        value = value / 100.0
    return value
def normalize_files_list(raw) -> list[str]:
    if raw is None:
        return []
    if isinstance(raw, (str, os.PathLike)):
        raw = [raw]
    if isinstance(raw, (bytes, bytearray, dict)) or not isinstance(raw, Iterable):
        return []
    result: list[str] = []
    seen: set[str] = set()
    for item in _ordered_items(raw):
        if isinstance(item, os.PathLike):
            try:
                item = os.fsdecode(item)
            except (TypeError, ValueError):
                continue
        if isinstance(item, str) and item and item not in seen:
            seen.add(item)
            result.append(item)
    return result
def normalize_path_list(files, label: str,
                        log_prefix: str = "[PathList]") -> list[str]:
    if files is not None and not isinstance(files, (str, os.PathLike)) and (
            isinstance(files, (bytes, bytearray, dict))
            or not isinstance(files, Iterable)):
        logger.warning("%s %s 清单形态非法(%s)，按空清单处理",
                       log_prefix, label, type(files).__name__)
        return []
    if isinstance(files, (str, os.PathLike)):
        files = [files]
    elif files is None:
        files = ()
    result: list[str] = []
    seen: set[str] = set()
    dropped = 0
    for item in _ordered_items(files):
        if isinstance(item, os.PathLike):
            try:
                item = os.fsdecode(item)
            except (TypeError, ValueError):
                dropped += 1
                continue
        if not isinstance(item, str):
            dropped += 1
            continue
        if not item:
            dropped += 1
            continue
        norm = os.path.normpath(item)
        if norm in seen:
            continue
        seen.add(norm)
        result.append(norm)
    if dropped:
        logger.warning("%s %s 清单含 %d 个非字符串条目，已过滤",
                       log_prefix, label, dropped)
    return result
def normalize_target_path(target_path) -> str:
    if isinstance(target_path, str):
        return target_path
    if isinstance(target_path, os.PathLike):
        try:
            return os.fsdecode(target_path)
        except (TypeError, ValueError) as _e:
            log_swallowed(__name__, _e,
                          context='normalize_target_path:PathLike')
    if target_path is not None:
        logger.warning('target_path 类型非法 %r，已归一空串', target_path)
    return ''
def anchor_to_skill(fp, skill_dir):
    if not fp or not skill_dir:
        return fp
    path = coerce_path_str(fp)
    root_path = coerce_path_str(skill_dir)
    if not path or not root_path:
        logger.warning("anchor_to_skill 路径形态非法，已拒绝: %r", fp)
        return ""
    anchored = path if os.path.isabs(path) else os.path.join(root_path, path)
    try:
        root = canonical_path(root_path)
        candidate = canonical_path(anchored)
        contained = os.path.commonpath((root, candidate)) == root
    except ValueError:
        contained = False
    except (OSError, TypeError) as exc:
        log_swallowed(__name__, exc, context='anchor_to_skill:validate')
        return ""
    if not contained:
        logger.warning("anchor_to_skill 路径越出技能根，已拒绝: %r", fp)
        return ""
    return anchored
_SCALAR_JUNK_ITEM_TYPES: tuple = (
    str, bytes, bytearray, bool, int, float, complex, type(None),
)
def drop_scalar_items(items: list, *, log_tag: str) -> list:
    kept = [it for it in items if not isinstance(it, _SCALAR_JUNK_ITEM_TYPES)]
    dropped = len(items) - len(kept)
    if dropped:
        logger.warning(
            "%s 跳过 %d 个标量基元条目"
            "（str/数值/bool/None 等形态不可能承载字段）", log_tag, dropped)
    return kept
def normalize_entry_inputs(value: Any, all_issues: list | None,
                           *, text: bool = False) -> tuple[Any, list]:
    value = (value if isinstance(value, str) else "") if text else (
        [] if value is None else value)
    if all_issues is None:
        all_issues = []
    return value, all_issues
def coerce_line(value) -> int:
    if isinstance(value, (list, tuple)):
        value = value[0] if value else 0
    if isinstance(value, bool) or value is None:
        return 0
    if isinstance(value, float):
        if not (math.isfinite(value) and value.is_integer()):
            return 0
        return max(0, int(value))
    num = safe_to_int(value)
    return max(0, num) if num is not None else 0
coerce_line_number = coerce_line
normalize_line_no = coerce_line
def identifier_text(value) -> str:
    if isinstance(value, (list, tuple)):
        value = value[0] if value else ""
    if (isinstance(value, bool) or not value
            or isinstance(value, (dict, set, frozenset, list, tuple))):
        return ""
    if isinstance(value, float) and not math.isfinite(value):
        return ""
    return value if isinstance(value, str) else str(value)
def normalize_input(value: object, field_desc: str, *,
                    allow_path: bool = False) -> str:
    if allow_path and isinstance(value, os.PathLike):
        try:
            value = os.fsdecode(value)
        except (TypeError, ValueError) as e:
            logger.warning("[normalize] %s PathLike 归一失败 %r: %s",
                           field_desc, value, e)
            return ""
    if isinstance(value, str):
        return value.removeprefix("\ufeff")
    if value is not None:
        logger.warning("[normalize] %s 类型非法 %r，已归一空串", field_desc, value)
    return ""
def normalize_py_filename(filename: str) -> str:
    if not isinstance(filename, str):
        return ""
    stripped = filename.strip()
    label = os.path.basename(stripped) if stripped else ""
    if not label:
        return ""
    if not label.lower().endswith(".py"):
        return f"{label}.py"
    return label
def env_number(name: str, default: float,
               cast: Callable[[str], float]) -> float:
    raw = os.environ.get(name, "")
    if not raw.strip():
        return default
    try:
        val = cast(raw.strip())
    except (TypeError, ValueError, OverflowError):
        logger.warning(
            "环境变量 %s=%r 不是合法数值，回退默认值 %r", name, raw, default
        )
        return default
    if isinstance(val, float) and not math.isfinite(val):
        logger.warning(
            "环境变量 %s=%r 解析为非有限数值 %r，回退默认值 %r",
            name, raw, val, default,
        )
        return default
    return val
def safe_confidence(
        value: float, default: float = DEFAULT_CONFIDENCE_FALLBACK) -> float:
    try:
        if isinstance(value, bool):
            return default
        v = float(value)
        if not math.isfinite(v):
            return default
        return max(0.0, min(1.0, v))
    except (TypeError, ValueError, OverflowError) as e:
        logger.debug("safe_confidence: 置信度值非法，降级 default: %r (%s)", value, e)
        return default
normalize_confidence = safe_confidence
def clamp_unit(value: float) -> float:
    return min(max(finite_float_or_zero(value), 0.0), 1.0)
def adjust_finding_confidence(
        f: dict, delta: float, *, increasing: bool) -> bool:
    if not isinstance(f, dict) or not is_real_number(delta):
        return False
    current = f.get("confidence", DEFAULT_CONFIDENCE_FALLBACK)
    if not is_real_number(current):
        return False
    if (increasing and delta < 0) or (not increasing and delta > 0):
        return False
    try:
        adjusted = float(current) + float(delta)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context="adjust_finding_confidence:coerce")
        return False
    if not math.isfinite(adjusted):
        return False
    f["confidence"] = round(clamp_unit(adjusted), 3)
    return True
def safe_int(value, default: int = 0) -> int:
    if isinstance(value, bool):
        return default
    try:
        return int(value)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context=f'safe_int:{type(_e).__name__}')
        return default
int_coerce = safe_int
def finite_float_or_zero(value) -> float:
    if isinstance(value, bool):
        return 0.0
    try:
        v = float(value)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e,
                      context=f'finite_float_or_zero:{type(_e).__name__}')
        return 0.0
    if not math.isfinite(v):
        return 0.0
    return v
def grade_from_score(score: float) -> str:
    try:
        value = float(score)
    except (TypeError, ValueError, OverflowError):
        return "F"
    if not math.isfinite(value):
        return "F"
    if value >= 90:
        return "A"
    if value >= 75:
        return "B"
    if value >= 60:
        return "C"
    if value >= 40:
        return "D"
    return "F"
norm_dict = dict_or_empty
def norm_dict_list(value) -> list:
    if not isinstance(value, list):
        return []
    return [x for x in value if isinstance(x, dict)]
def norm_str_list(value, fallback=None) -> list:
    for candidate in (value, fallback):
        if isinstance(candidate, (list, tuple)):
            return [safe_str(x) for x in candidate if x is not None]
    return []
def timestamp_ms() -> str:
    return datetime.datetime.now().strftime("%Y%m%d%H%M%S%f")[:17]
def timestamp_human() -> str:
    return datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:23]
def compact_ts_to_ms(ts: str) -> int | None:
    if not (isinstance(ts, str) and len(ts) in (14, 17) and ts.isdigit()):
        return None
    try:
        _ms = int(ts[14:17]) if len(ts) == 17 else 0
        return int(time.mktime(time.strptime(
            ts[:14], "%Y%m%d%H%M%S")) * 1000) + _ms
    except (ValueError, OverflowError, OSError) as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context='compact_ts_to_ms:ValueError+')
        return None
def format_compact_ts(ms: int) -> str:
    return (time.strftime("%Y%m%d%H%M%S", time.localtime(ms / 1000.0))
            + f"{ms % 1000:03d}")
def elapsed_seconds(stage_start: float) -> float:
    return round(time.time() - stage_start, 2)
def coerce_round_anchor_strict(value: Any) -> str | None:
    if value is None or value == "":
        return ""
    if isinstance(value, str):
        return value
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        if isinstance(value, int):
            return str(value)
        if not math.isfinite(value):
            return None
        return str(int(value)) if value.is_integer() else str(value)
    except (OverflowError, ValueError) as exc:
        log_swallowed(__name__, exc,
                      context="coerce_round_anchor_strict:OverflowError")
        return None
def coerce_round_anchor(value: Any) -> str:
    anchor = coerce_round_anchor_strict(value)
    return anchor if isinstance(anchor, str) else ""
def round_anchor_matches(report_round: Any, current_round: Any) -> bool:
    report = coerce_round_anchor_strict(report_round)
    current = coerce_round_anchor_strict(current_round)
    if report is None or current is None:
        return False
    if not report and not current:
        return True
    return bool(report and current and report == current)
def entry_round_anchor(entry: Any) -> str:
    if not isinstance(entry, dict):
        return ""
    return coerce_round_anchor(entry.get("round_start_ts"))
def safe_isfinite(value) -> bool:
    try:
        return math.isfinite(value)
    except (OverflowError, TypeError, ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=f'safe_isfinite:{type(_e).__name__}')
        return False
is_real_number = is_finite_num
def safe_contains(container, key) -> bool:
    try:
        return key in container
    except TypeError as _e:
        log_swallowed(__name__, _e, context='safe_contains:TypeError')
        return False
_RANK_TO_SEVERITY: dict[int, str] = {
    rank: f"P{rank}" for rank in sorted(set(SEVERITY_RANK.values()))
}
_SEVERITY_RANK_FLOOR: int = max(SEVERITY_RANK.values(), default=3) + 1
def severity_literal_from_rank(rank: int) -> str:
    if isinstance(rank, bool) or not isinstance(rank, int):
        return "P3"
    return _RANK_TO_SEVERITY.get(rank, "P3")
def severity_penalty_weight(severity: Any, default: int | None = None) -> int:
    fallback = (SEVERITY_PENALTY_WEIGHTS.get("P2", 0)
                if default is None else default)
    if not isinstance(severity, str):
        return fallback
    rank = SEVERITY_RANK.get(severity.strip().upper())
    if rank is None:
        return fallback
    return SEVERITY_PENALTY_WEIGHTS.get(
        severity_literal_from_rank(rank), fallback)
def normalize_severity_rank(severity: Any) -> int:
    if not isinstance(severity, str):
        return 3
    return SEVERITY_RANK.get(severity.upper().strip(), 3)
def severity_text_value(value: Any) -> str | None:
    value = getattr(value, 'value', None) or getattr(value, 'name', None) or value
    if value is None or (not isinstance(value, str) and not value):
        return None
    text = str(value).strip().upper()
    return text or None
def severity_rank_of(value: Any) -> int:
    return normalize_severity_rank(severity_text_value(value) or "")
def severity_key(value: Any, default: str = "") -> str:
    if not isinstance(value, str):
        return default
    rank = SEVERITY_RANK.get(value.strip().upper())
    if rank is None:
        return default
    return severity_literal_from_rank(rank)
def is_high_severity(severity: str, threshold: str = "P2") -> bool:
    try:
        if (not isinstance(severity, str) or not isinstance(threshold, str)
                or severity.upper().strip() not in SEVERITY_RANK
                or threshold.upper().strip() not in SEVERITY_RANK):
            return False
        return normalize_severity_rank(severity) <= normalize_severity_rank(threshold)
    except Exception as e:
        logger.warning("is_high_severity: %s", e, exc_info=True)
        return False
def _track_max_severity(raw: Any, max_rank: int,
                        max_sev: str) -> tuple[int, str]:
    _sev = severity_text_value(raw) or "P3"
    _rank = normalize_severity_rank(_sev)
    if _sev not in SEVERITY_RANK:
        _sev = _RANK_TO_SEVERITY.get(_rank, "P3")
    if _rank < max_rank:
        return _rank, _sev
    if (_rank == max_rank and _sev != max_sev
            and _sev == _RANK_TO_SEVERITY.get(_rank)):
        return _rank, _sev
    return max_rank, max_sev
def _max_severity_of(raws) -> str:
    max_sev = "P3"
    max_rank = _SEVERITY_RANK_FLOOR
    for raw in raws:
        max_rank, max_sev = _track_max_severity(raw, max_rank, max_sev)
    return max_sev
def get_max_severity(severities: Any) -> str:
    try:
        if severities is None:
            return "P3"
        if isinstance(severities, dict):
            return _max_severity_from_mapping(severities)
        if isinstance(severities, SOURCE_SEQUENCE_TYPES):
            return _max_severity_from_list(severities)
        return "P3"
    except Exception as e:
        logger.warning("get_max_severity: %s", e, exc_info=True)
        return "P3"
def _max_severity_from_mapping(grouped: dict) -> str:
    return _max_severity_of(
        _f.get("severity")
        for _findings in grouped.values()
        if isinstance(_findings, SOURCE_SEQUENCE_TYPES)
        for _f in _findings if isinstance(_f, dict))
def _max_severity_from_list(items: Iterable) -> str:
    return _max_severity_of(
        item.get("severity") if isinstance(item, dict) else item
        for item in items if isinstance(item, (dict, str)))
def safe_rule_id(rule_id: Any) -> str:
    try:
        return str(rule_id)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='safe_rule_id:str')
        return f"<{type(rule_id).__name__}>"
def safe_str(value: Any) -> str:
    if isinstance(value, str):
        return value
    try:
        return str(value)
    except Exception as exc:  # noqa: BLE001
        logger.debug("safe_str 降级：value_type=%s exc_type=%s",
                   type(value).__name__, type(exc).__name__)
        return f"<{type(value).__name__}:{type(exc).__name__}>"
def rule_id_of(issue: Any) -> str:
    if not isinstance(issue, dict):
        return "UNKNOWN"
    return safe_str(
        issue.get("rule_id") or issue.get("rule") or issue.get("id")
        or "UNKNOWN")
def make_locator_fast(f: dict) -> str:
    f = norm_dict(f)
    fp = f.get("file_path") or f.get("file") or f.get("filepath") or ""
    ln = safe_finding_line(f)
    rf = f.get("rule_family") or f.get("rule_id") or "diag_general"
    return f"{fp}:{ln}:{rf}"
def _is_locator_line_slot(seg: str) -> bool:
    _body = seg.strip()
    if not _body or _body == "FILE_LEVEL":
        return True
    if safe_to_int(_body) is not None:
        return True
    return _body.startswith("-") and safe_to_int(_body[1:]) is not None
def _is_strippable_tail(seg: str) -> bool:
    return not seg.strip() or _is_locator_line_slot(seg.strip())
def _locator_parts(locator: Any) -> list[str]:
    if not isinstance(locator, str) or not locator:
        return []
    return locator.rsplit(":", 2)
def finding_file_key(value: Any) -> str:
    text = str(value or "").strip()
    if not text:
        return ""
    normalized = os.path.normpath(text.replace("\\", "/"))
    return os.path.normcase(normalized).replace("\\", "/")
def path_key(path: str, skill_dir: str = '') -> str:
    text = str_or(path).strip()
    if not text:
        return ''
    key = finding_file_key(text)
    root = finding_file_key(str_or(skill_dir).strip())
    prefix = root if root.endswith('/') else root + '/'
    if key and root and key.startswith(prefix):
        return key[len(prefix):]
    return key
def same_file(left: str, right: str, skill_dir: str = '') -> bool:
    left_key = path_key(left, skill_dir)
    right_key = path_key(right, skill_dir)
    if not left_key or not right_key:
        return False
    if left_key == right_key:
        return True
    if left_key.rsplit('/', 1)[-1] != right_key.rsplit('/', 1)[-1]:
        return False
    left_full = finding_file_key(left)
    right_full = finding_file_key(right)
    if '/' in left_full and '/' in right_full:
        return False
    root = str_or(skill_dir).strip()
    if root:
        root_prefix = finding_file_key(os.path.abspath(root)).rstrip('/') + '/'
        for candidate in (left, right):
            if os.path.isabs(candidate):
                absolute = finding_file_key(os.path.abspath(candidate))
                if not absolute.startswith(root_prefix):
                    return False
    left_dir = left_key.rsplit('/', 1)[0] if '/' in left_key else ''
    right_dir = right_key.rsplit('/', 1)[0] if '/' in right_key else ''
    return not left_dir or not right_dir
def seed_key(finding: dict) -> str:
    _f = dict_or_empty(finding)
    return '|'.join((
        str_or(_f.get('rule_id')) or str_or(_f.get('rule_applied')),
        str_or(_f.get('file')) or str_or(_f.get('file_path')),
        str(safe_finding_line(_f)),
    ))
def finding_file_path(ff: Any) -> str:
    if not isinstance(ff, dict):
        return ""
    raw = ff.get("file_path") or ff.get("file") or ff.get("filepath") or ""
    return raw if isinstance(raw, str) else ""
def finding_rule_family(ff: Any) -> str:
    if not isinstance(ff, dict):
        return ""
    return str(ff.get("rule_family") or ff.get("rule_id") or "")
def safe_finding_line(f: dict) -> int:
    return coerce_line(f.get("line", 0) if isinstance(f, dict) else 0)
def make_locator(file: str, line: int, rule_family: str) -> str:
    line_int = safe_finding_line({"line": line})
    if not rule_family:
        rule_family = "diag_general"
    return f"{file or ''}:{line_int}:{rule_family}"
def channel_locator(f: Any) -> str:
    if not isinstance(f, dict):
        return ""
    if finding_file_path(f):
        return make_locator_fast(f)
    return f":{safe_finding_line(f)}:{finding_rule_family(f) or 'diag_general'}"
def finding_sub_engines(ff: dict) -> set:
    ff = norm_dict(ff)
    se = ff.get("detectors")
    if not isinstance(se, SOURCE_SEQUENCE_TYPES) or not se:
        se = ff.get("sub_engines")
    if isinstance(se, SOURCE_SEQUENCE_TYPES):
        return {str(x) for x in se}
    return set()
_STATUS_MESSAGE_TEXTS = (
    "方法正常通过", "全部通过",
    "all tests passed", "all checks passed", "all passed",
    "tests passed", "test passed", "method passed",
    "method completed successfully", "completed successfully",
)
_STATUS_NEGATIONS = ("未", "不", "非", "无", "没", "否", "别")
_STATUS_FAILURE_TAILS = ("失败", "错误", "异常", "例外", "缺", "漏",
                         "告警", "警告", "率")
_EN_STATUS_NEGATION_RE = re.compile(
    r"(?:\b(?:not|never|no|without)\b|\b[\w-]+n't)\s+"
    r"(?:[\w-]+\s+){0,2}$", re.IGNORECASE)
_EN_STATUS_FAILURE_RE = re.compile(
    r"\b(?P<failure>fail(?:ed|ures?|ing|s)?|errors?|exceptions?|warnings?)\b"
    r"|(?P<rate>\brate\b)", re.IGNORECASE)
_ZERO_COUNT_PREFIX_RE = re.compile(
    r"(?<![\d.])(?:0(?:\.0+)?|zero)\s*(?:个|条|次|项|处|例|起)?\s*$",
    re.IGNORECASE,
)
_ZERO_FAILURE_NUMBER = r"(?:0(?:\.0+)?|zero)"
_ZERO_FAILURE_WORD = (
    r"(?:fail(?:ed|ures?|ing|s)?|errors?|exceptions?|warnings?|"
    r"失败|错误|异常|例外|告警|警告)"
)
_ZERO_FAILURE_PREFIX_RE = re.compile(
    rf"(?<![\d.]){_ZERO_FAILURE_NUMBER}\s*"
    rf"(?:%|个|条|次|项|处|例|起)?\s*"
    rf"(?:tests?|测试|用例)?\s*{_ZERO_FAILURE_WORD}"
    rf"(?:\s*(?:率|rate))?",
    re.IGNORECASE,
)
_ZERO_FAILURE_SUFFIX_RE = re.compile(
    rf"{_ZERO_FAILURE_WORD}(?:\s*(?:率|rate))?\s*"
    rf"(?:为|是|=|:|is|are)?\s*{_ZERO_FAILURE_NUMBER}(?![\d.])\s*"
    rf"(?:%|个|条|次|项|处|例|起)?",
    re.IGNORECASE,
)
def _mask_zero_failure_expressions(text: str) -> str:
    masked = _ZERO_FAILURE_PREFIX_RE.sub(" ", text)
    return _ZERO_FAILURE_SUFFIX_RE.sub(" ", masked)
def _zero_count_prefix(text: str, start: int) -> bool:
    return (_ZERO_COUNT_PREFIX_RE.search(text[max(0, start - 16):start])
            is not None)
def _status_phrase_pattern(phrase: str) -> re.Pattern[str]:
    if phrase.isascii():
        return re.compile(
            rf"(?<![A-Za-z0-9_]){re.escape(phrase)}(?![A-Za-z0-9_])",
            re.IGNORECASE)
    return re.compile(re.escape(phrase))
_STATUS_MESSAGE_PATTERNS = tuple(
    (phrase, _status_phrase_pattern(phrase))
    for phrase in _STATUS_MESSAGE_TEXTS)
_STATUS_RATE_CONTEXT_CHARS = 24
def _negated_status_prefix(text: str, start: int) -> bool:
    chinese_before = text[max(0, start - 4):start]
    if any(token in chinese_before for token in _STATUS_NEGATIONS):
        return True
    english_before = text[max(0, start - 40):start]
    return _EN_STATUS_NEGATION_RE.search(english_before) is not None
def _has_failure_signal(text: str, *, include_rate: bool = False) -> bool:
    text = _mask_zero_failure_expressions(text)
    for token in _STATUS_FAILURE_TAILS:
        if token == "率" and not include_rate:
            continue
        start = text.find(token)
        while start != -1:
            if (not _zero_count_prefix(text, start)
                    and not _negated_status_prefix(text, start)):
                return True
            start = text.find(token, start + 1)
    for matched in _EN_STATUS_FAILURE_RE.finditer(text):
        if matched.group("rate") is not None and not include_rate:
            continue
        if (not _zero_count_prefix(text, matched.start())
                and not _negated_status_prefix(text, matched.start())):
            return True
    return False
def is_status_message_finding(ff: dict) -> bool:
    ff = norm_dict(ff)
    if ff.get("rule_id") == "method_pass":
        return True
    msg = ff.get("message") or ""
    if not isinstance(msg, str):
        return False
    for _phrase, pattern in _STATUS_MESSAGE_PATTERNS:
        for matched in pattern.finditer(msg):
            before = msg[:matched.start()]
            after = msg[matched.end():]
            if (not _negated_status_prefix(msg, matched.start())
                    and not _has_failure_signal(before)
                    and not _has_failure_signal(
                        after[:_STATUS_RATE_CONTEXT_CHARS], include_rate=True)
                    and not _has_failure_signal(after)):
                return True
    return False
def _is_ascii_digits(text: str) -> bool:
    return bool(text) and text.isascii() and text.isdigit()
def parse_locator_line(locator: Any) -> int:
    parts = _locator_parts(locator)
    if len(parts) < 2:
        return 0
    candidates = (parts[1], parts[-1]) if len(parts) == 3 else (parts[-1],)
    for candidate in candidates:
        num = safe_to_int(candidate)
        if num is not None:
            return max(0, num)
    return 0
def extract_finding_line(finding: dict) -> int:
    finding = norm_dict(finding)
    line = safe_finding_line(finding)
    if line > 0:
        return line
    return parse_locator_line(finding.get("locator", ""))
def parse_locator_file(locator: Any) -> str:
    parts = _locator_parts(locator)
    if not parts:
        return ""
    if len(parts) == 1:
        return locator
    if len(parts) == 3:
        return parts[0] if _is_locator_line_slot(parts[1]) else parts[0] + ":" + parts[1]
    if not parts[-1].strip() or _is_locator_line_slot(parts[-1]):
        return parts[0]
    return locator
_PYTHON_IDENTIFIER_TOKEN = r"[^\W\d]\w*"
_QUOTED_SYMBOL_PATTERN = re.compile(
    r"['\"`](" + _PYTHON_IDENTIFIER_TOKEN + r")(?:\(\))?['\"`]")
_SYMBOL_PREFIX_PATTERN = re.compile(
    r"(?:(?<![A-Za-z0-9_])(?:function|method|class)\b|函数|方法|变量)"
    r"(?![\u4e00-\u9fff])"
    r"\s*[：:]*\s*['\"`]?(" + _PYTHON_IDENTIFIER_TOKEN + r")",
    re.IGNORECASE,
)
def is_python_keyword(name: Any) -> bool:
    return isinstance(name, str) and keyword.iskeyword(name)
def extract_symbol(message: str) -> str:
    if not message or not isinstance(message, str):
        return ""
    for _m in _SYMBOL_PREFIX_PATTERN.finditer(message):
        _symbol = _m.group(1)
        if not _symbol.isidentifier() or is_python_keyword(_symbol):
            continue
        return _symbol
    for _m in _QUOTED_SYMBOL_PATTERN.finditer(message):
        _symbol = _m.group(1)
        if not _symbol.isidentifier() or is_python_keyword(_symbol):
            continue
        return _symbol
    return ""
def safe_to_int(value: Any) -> int | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return value
    if not isinstance(value, str) or not _is_ascii_digits(value.strip()):
        return None
    try:
        return int(value.strip())
    except ValueError as _e:
        log_swallowed(__name__, _e, context='safe_to_int:ValueError')
        return None
def parse_json_dict(value: Any) -> tuple[dict, bool]:
    if isinstance(value, dict):
        return value, True
    if not isinstance(value, str) or not value.strip():
        return {}, False
    text = strip_bom(value).strip()
    try:
        parsed = json.loads(text)
    except (json.JSONDecodeError, TypeError, RecursionError) as _e:
        log_swallowed(__name__, _e,
                      context='parse_json_dict:parse')
        return {}, False
    return (parsed, True) if isinstance(parsed, dict) else ({}, False)
def findings_container(data, types: tuple[type, ...] = (list, tuple)) -> list:
    findings = data.get("findings") if isinstance(data, dict) else None
    return list(findings) if isinstance(findings, types) else []
def canonical_rule_key(rule_id: str) -> str:
    return "_".join(str(rule_id).strip().lower().replace("-", "_").split())
_G5_RULE_ID_RE = re.compile(r"^\s*\[([^\]\s]+)\]")
def _g5_text_finding(text: str) -> dict:
    matched = _G5_RULE_ID_RE.match(text)
    return {
        "rule_id": matched.group(1) if matched else "G5-violation",
        "message": text, "file": "", "line": 0, "severity": "P3",
    }
def _is_g5_text_entry(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())
def _action_group_findings(action: dict):
    """展开 action 容器内层 findings（按文件分组的修复动作）。

    F 组的 action 形如 ``{file, ai_action, findings: [...]}``：缺陷在内层，
    容器本身只有 ``file``。直接把容器当 finding 产出会让 rule_id/severity/line
    全空，CV 与归零门禁拿到的是无法裁决的伪 finding。
    """
    inner = action.get("findings")
    if not isinstance(inner, (list, tuple)):
        return
    group_file = action.get("file", "")
    group_engine = action.get("sub_engine", "")
    for finding in inner:
        if not isinstance(finding, dict):
            continue
        merged = dict(finding)
        if group_file and not merged.get("file"):
            merged["file"] = group_file
        if group_engine and not merged.get("sub_engine"):
            merged["sub_engine"] = group_engine
        yield merged
def _iter_g5_value(key: str, items: Any, *,
                   dict_covered: bool | None = None):
    if not isinstance(items, (list, tuple)):
        return
    covered = (key in FINDING_LIST_KEYS
               if dict_covered is None else dict_covered)
    for item in items:
        if _is_g5_text_entry(item):
            yield _g5_text_finding(item)
        elif isinstance(item, dict) and not covered:
            if key == "actions" and isinstance(item.get("findings"), (list, tuple)):
                yield from _action_group_findings(item)
                continue
            yield item
def _iter_g5_items(payload: dict):
    for key in ("violations", "actions"):
        yield from _iter_g5_value(key, payload.get(key, []))
def _iter_dict_items(maybe_list):
    if isinstance(maybe_list, (list, tuple)):
        for x in maybe_list:
            if isinstance(x, dict):
                yield x
def _iter_standard_key_items(payload: dict):
    for key in sorted(FINDING_LIST_KEYS):
        yield from _iter_dict_items(payload.get(key, []))
def _is_antipattern_key(key) -> bool:
    if not isinstance(key, str):
        return False
    return any(key.startswith(p) for p in ANTIPATTERN_PREFIXES)
def _iter_antipattern_key_items(payload: dict):
    for key, val in payload.items():
        if _is_antipattern_key(key):
            yield from _iter_dict_items(val)
def _has_collectable_top_items(key: str, value: Any) -> bool:
    if not isinstance(value, (list, tuple)) or not value:
        return False
    if key in ("violations", "actions"):
        return any(isinstance(item, dict) or _is_g5_text_entry(item)
                   for item in value)
    return any(isinstance(item, dict) for item in value)
def _iter_raw_result_items(payload: dict):
    raw_result = payload.get("raw_result")
    if isinstance(raw_result, dict):
        for rk, rv in raw_result.items():
            if not (_is_antipattern_key(rk) or rk in FINDING_LIST_KEYS
                    or rk == "actions"):
                continue
            top = payload.get(rk) if isinstance(rk, str) else None
            if isinstance(rk, str) and _has_collectable_top_items(rk, top):
                continue
            if rk in ("violations", "actions"):
                yield from _iter_g5_value(rk, rv, dict_covered=False)
            else:
                yield from _iter_dict_items(rv)
def iter_payload_finding_items(payload: dict):
    if not isinstance(payload, dict):
        return
    yield from _iter_standard_key_items(payload)
    yield from _iter_antipattern_key_items(payload)
    yield from _iter_raw_result_items(payload)
    yield from _iter_g5_items(payload)
def integral_count(value) -> int | None:
    if not is_real_number(value):
        return None
    if isinstance(value, float):
        if not value.is_integer():
            return None
        return int(value)
    return int(value)
def derive_rule_id(f: dict) -> str:
    if not isinstance(f, dict):
        return ""
    rule_id = identifier_text(f.get("rule_id"))
    if rule_id:
        return rule_id
    for key in ("blindspot_type", "name", "type"):
        value = identifier_text(f.get(key))
        if value:
            return value
    return ""
def _valid_explicit_count(raw: dict) -> int | None:
    declared = integral_count(raw.get("findings_count"))
    if declared is None or declared <= 0:
        return None
    return declared
def count_findings_in_payload(raw: dict) -> int:
    if not isinstance(raw, dict):
        return 0
    explicit = _valid_explicit_count(raw)
    if explicit is not None:
        return explicit
    return sum(1 for _ in iter_payload_finding_items(raw))
def extract_cv_metadata(payload: dict) -> tuple:
    findings_list = []
    rule_families = set()
    if not isinstance(payload, dict) or not payload:
        return findings_list, rule_families, []
    for item in iter_payload_finding_items(payload):
        findings_list.append(item)
        rule_id = derive_rule_id(item) or str(item.get("rule") or "")
        if rule_id in ALL_FAMILY_KEYS:
            rule_families.add(rule_id)
    declared = integral_count(payload.get("findings_count"))
    finding_count = len(findings_list)
    quality_rules = (
        ("findings_count_mismatch",
         declared is not None and declared != finding_count),
        ("high_volume_findings", finding_count > OUTPUT_TRUNCATE_LEN),
        ("no_explicit_findings", not findings_list),
    )
    quality_flags = [flag for flag, active in quality_rules if active]
    return findings_list, rule_families, quality_flags
def mean_std(values: Iterable[float]) -> tuple[float, float]:
    seq = [value for value in values] if values is not None else []
    if not seq:
        return 0.0, 0.0
    mean = sum(seq) / len(seq)
    variance = sum((value - mean) ** 2 for value in seq) / len(seq)
    return mean, variance ** 0.5
__all__ = [
    'FALSE_SIGNAL_TEXT',
    'adjust_finding_confidence',
    'anchor_to_skill',
    'append_judgment',
    'append_recommendation_once',
    'as_count',
    'as_declared',
    'as_dict',
    'as_entry_list',
    'as_item_list',
    'as_list',
    'as_num',
    'as_number',
    'as_pure_count',
    'as_sequence',
    'as_str',
    'canonical_rule_key',
    'channel_locator',
    'clamp_unit',
    'clean_source_ids',
    'clean_str_list',
    'coerce_line',
    'coerce_line_number',
    'coerce_mapping',
    'coerce_path_str',
    'coerce_round_anchor',
    'coerce_round_anchor_strict',
    'coerce_text_list',
    'coerce_timeout',
    'coerce_tolerance',
    'compact_ts_to_ms',
    'conf_chain',
    'count_findings_in_payload',
    'count_tasks',
    'cv_int',
    'degrade_factor_of',
    'derive_rule_id',
    'dict_items',
    'dict_or_empty',
    'drop_scalar_items',
    'elapsed_seconds',
    'entry_round_anchor',
    'env_number',
    'escape_dq_inline',
    'escape_dq_text',
    'extract_cv_metadata',
    'extract_finding_line',
    'extract_symbol',
    'finding_file_key',
    'finding_file_path',
    'finding_rule_family',
    'finding_sub_engines',
    'findings_container',
    'finite_float_or_none',
    'finite_float_or_zero',
    'float_field',
    'float_metric',
    'format_compact_ts',
    'get_max_severity',
    'grade_from_score',
    'has_finding_entries',
    'identifier_text',
    'int_coerce',
    'int_metric',
    'int_or',
    'integral_count',
    'is_default_confidence',
    'is_finite_num',
    'is_high_severity',
    'is_number',
    'is_placeholder_rule_id',
    'is_pure_int',
    'is_python_keyword',
    'is_real_number',
    'is_status_message_finding',
    'is_valid_fp_rate',
    'iter_payload_finding_items',
    'judgment_dicts',
    'judgment_str_fields',
    'len_safe',
    'list_field',
    'make_locator',
    'make_locator_fast',
    'mean_std',
    'meta_num',
    'method_status_bucket',
    'method_status_detail',
    'norm_dict',
    'norm_dict_list',
    'norm_rule_id',
    'norm_str_list',
    'normalize_confidence',
    'normalize_entry_inputs',
    'normalize_execute_timeout',
    'normalize_file_ref',
    'normalize_files_list',
    'normalize_input',
    'normalize_line_no',
    'normalize_list_field',
    'normalize_passed',
    'normalize_path_list',
    'normalize_py_filename',
    'normalize_severity_rank',
    'normalize_sources',
    'normalize_str_seq',
    'normalize_success_rate',
    'normalize_target_path',
    'now_iso',
    'num',
    'numeric_or',
    'parse_json_dict',
    'parse_locator_file',
    'parse_locator_line',
    'path_key',
    'plan_index',
    'ratio01',
    'recommendations_list',
    'require_dict',
    'round_anchor_matches',
    'rule_id_of',
    'safe_confidence',
    'safe_contains',
    'safe_dict_get',
    'safe_finding_line',
    'safe_float',
    'safe_int',
    'safe_isfinite',
    'safe_rule_id',
    'safe_short_text',
    'safe_str',
    'safe_text',
    'safe_to_int',
    'same_file',
    'section_dict',
    'seed_key',
    'severity_key',
    'severity_literal_from_rank',
    'severity_penalty_weight',
    'severity_rank_of',
    'severity_text_value',
    'signal_bool',
    'source_id_text',
    'str_or',
    'str_or_empty',
    'strict_iterable_list',
    'strip_bom',
    'strip_cv_target_prefix',
    'text_or_empty',
    'timestamp_human',
    'timestamp_ms',
    'unwrap_cv_results',
    'yaml_safe_desc_line',
    'yaml_safe_quote',
]

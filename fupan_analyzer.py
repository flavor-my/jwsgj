from __future__ import annotations

import copy
import logging
import math
import os
import re
import shlex
from collections import Counter
from dataclasses import dataclass, field
from typing import Any, NamedTuple

from jwsgj.diag_types_normalize import coerce_text_list
from jwsgj.log_config import log_swallowed

__all__ = [
    "DEFAULT_CONFIG",
    "AnalysisResult",
    "analyze_session",
    "as_bool",
    "as_float",
    "as_int",
    "build_trigger_signals",
    "close_loop_check",
    "collect_tools_used",
    "detect_fupan",
    "detect_fupan_execution",
    "ensure_list",
    "ensure_str_list",
    "normalize_scalar",
    "normalize_tool_calls",
    "should_fupan",
    "to_fupan_params",
]
logger = logging.getLogger(__name__)
logger.info("fupan_analyzer 已加载：%d 项导出", len(__all__))
@dataclass
class AnalysisResult:
    summary: str = ""
    risks: list[str] = field(default_factory=list)
    improvements: list[str] = field(default_factory=list)
    memory_candidates: list[dict[str, Any]] = field(default_factory=list)
    complexity_score: int = 0
    extraction_confidence: float = 0.0
    tool_stats: dict[str, int] = field(default_factory=dict)
    error_patterns: list[dict[str, Any]] = field(default_factory=list)
    root_causes: list[dict[str, Any]] = field(default_factory=list)
    prioritized_improvements: list[dict[str, Any]] = field(default_factory=list)
    reflexion_rounds: int = 0
    pattern_matches: list[dict[str, Any]] = field(default_factory=list)
FUPAN_PATTERNS = [
    {"id": "P001", "name": "导入缺失", "error_type": "import_error",
     "error_pattern": r"ModuleNotFoundError|ImportError",
     "risk": "模块导入链不完整，存在依赖断裂风险",
     "improvement": "建立导入依赖检查清单，编码后执行 AST 导入验证",
     "memory_category": "避坑",
     "memory_detail": "编码后必须验证所有 import 语句可达，避免 ModuleNotFoundError",
     "priority": "P0-红线"},
    {"id": "P002", "name": "类型不匹配", "error_type": "type_error",
     "error_pattern": r"TypeError|AttributeError",
     "risk": "类型注解缺失导致运行时类型错误",
     "improvement": "增加参数类型注解和运行时类型校验",
     "memory_category": "避坑",
     "memory_detail": "函数参数必须添加类型注解，关键路径增加 isinstance 校验",
     "priority": "P1-核心"},
    {"id": "P003", "name": "文件缺失", "error_type": "io_error",
     "error_pattern": r"FileNotFoundError|No such file",
     "risk": "文件路径依赖未做前置检查",
     "improvement": "文件操作前增加 os.path.exists 前置检查",
     "memory_category": "避坑",
     "memory_detail": "所有文件读写操作前必须检查文件存在性，使用绝对路径",
     "priority": "P1-核心"},
    {"id": "P004", "name": "超时/性能", "error_type": "connection_error",
     "error_pattern": r"timeout|timed out|Timeout",
     "risk": "操作耗时过长，缺乏超时控制和进度反馈",
     "improvement": "增加超时重试机制和进度提示",
     "memory_category": "优化",
     "memory_detail": "长耗时操作必须设置超时参数，并输出进度提示",
     "priority": "P2-通用"},
    {"id": "P005", "name": "权限拒绝", "error_type": "io_error",
     "error_pattern": r"Permission denied|Access denied",
     "risk": "文件/目录权限不足，操作被拒绝",
     "improvement": "预设文件权限检查，使用临时目录存放中间文件",
     "memory_category": "避坑",
     "memory_detail": "文件写入前检查目标目录写权限，必要时使用临时目录",
     "priority": "P1-核心"},
    {"id": "P006", "name": "编码问题", "error_type": "io_error",
     "error_pattern": r"UnicodeDecodeError|UnicodeEncodeError|encoding",
     "risk": "文件编码不一致导致读写失败",
     "improvement": "统一使用 UTF-8 编码，文件操作显式指定 encoding='utf-8'",
     "memory_category": "避坑",
     "memory_detail": "所有文件操作必须显式指定 encoding='utf-8'",
     "priority": "P2-通用"},
    {"id": "P007", "name": "语法错误", "error_type": "syntax_error",
     "error_pattern": r"SyntaxError|IndentationError",
     "risk": "代码存在语法错误，AST 解析失败",
     "improvement": "编码后增加 AST 语法验证步骤",
     "memory_category": "避坑",
     "memory_detail": "代码写入后立即执行 ast.parse() 验证语法正确性",
     "priority": "P0-红线"},
    {"id": "P008", "name": "键缺失", "error_type": "value_error",
     "error_pattern": r"KeyError",
     "risk": "字典键访问未做安全检查",
     "improvement": "字典访问前使用 .get() 或 in 安全检查",
     "memory_category": "避坑",
     "memory_detail": "字典键访问必须使用 .get() 或先检查 key in dict",
     "priority": "P1-核心"},
    {"id": "P009", "name": "连接失败", "error_type": "connection_error",
     "error_pattern": r"Connection|connect|Network|socket",
     "risk": "网络连接不稳定，操作可能中断",
     "improvement": "网络操作增加超时和重试机制",
     "memory_category": "避坑",
     "memory_detail": "网络请求必须设置 timeout 参数，并实现指数退避重试",
     "priority": "P2-通用"},
    {"id": "P010", "name": "值错误", "error_type": "value_error",
     "error_pattern": r"ValueError",
     "risk": "输入值不符合预期格式或范围",
     "improvement": "增加输入值范围校验和格式检查",
     "memory_category": "避坑",
     "memory_detail": "函数入口处增加参数值校验，对非法值提前返回或抛出自定义异常",
     "priority": "P2-通用"},
]
ERROR_PATTERNS = {
    "import_error": (r"ModuleNotFoundError|ImportError", "导入错误"),
    "type_error": (r"TypeError|AttributeError", "类型/属性错误"),
    "value_error": (r"ValueError|KeyError", "值/键错误"),
    "index_error": (r"IndexError", "索引错误"),
    "syntax_error": (r"SyntaxError|IndentationError", "语法错误"),
    "io_error": (r"IOError|FileNotFoundError|PermissionError", "文件/IO错误"),
    "runtime_error": (r"RuntimeError|RecursionError", "运行时错误"),
    "name_error": (r"NameError|UnboundLocalError", "名称错误"),
    "zero_division": (r"ZeroDivisionError|OverflowError", "数学运算错误"),
    "connection_error": (r"ConnectionError|TimeoutError|BrokenPipeError", "网络连接错误"),
    "os_error": (r"OSError|FileExistsError", "系统错误"),
    "memory_error": (r"MemoryError|SystemError", "资源不足"),
}
IMPROVEMENT_BY_ERROR_TYPE = {
    "import_error": "补全缺失的模块导入，建立导入检查清单",
    "type_error": "增加参数类型注解和运行时类型校验",
    "value_error": "字典/参数访问前使用 .get() 或显式值域校验",
    "index_error": "索引访问前增加边界与键存在性检查",
    "syntax_error": "编码后增加 AST 语法验证步骤",
    "io_error": "统一使用 UTF-8 编码显式指定 encoding，文件操作前预设权限检查",
    "runtime_error": "检查递归终止条件，必要时改用迭代实现，避免无限递归",
    "name_error": "补全未定义变量/函数引用，建立符号引用检查清单",
    "zero_division": "数值计算前增加除零/溢出防护",
    "connection_error": "网络与长耗时操作增加超时和重试机制",
    "os_error": "增加文件存在性前置检查，使用绝对路径，避免锁定冲突",
    "memory_error": "优化内存使用，对大对象及时释放或使用生成器",
}
ERROR_TYPE_SEVERITY = {
    "syntax_error": 10, "import_error": 9, "name_error": 8,
    "runtime_error": 8, "memory_error": 8, "type_error": 7,
    "zero_division": 7, "index_error": 6, "io_error": 6,
    "os_error": 6, "value_error": 5, "connection_error": 5,
}
_RISK_TEXT_ERROR_REPEAT = "同一类错误重复出现（{error_type}，{count}次），存在系统性问题"
_RISK_TEXT_CORE_MODULE_TOUCHED = "核心模块被修改（{files}），可能影响下游依赖"
_RISK_TEXT_NO_TEST_RUN = "本次修改未运行测试，缺少回归验证"
_RISK_TEXT_LONG_SESSION = "会话耗时过长（{duration}s），可能存在效率瓶颈"
_RISK_TEXT_LOW_CONFIDENCE = "自动提取置信度低（{confidence:.0%}），复盘可能不准确"
_RISK_TEXT_MANY_FILES_CHANGED = "大量文件变更（{count}个），变更范围过大"
_RISK_TEXT_MIXED_ERROR_TYPES = "多种类型错误混合出现（{types}），排查复杂度高"
_RISK_TEXT_RECURSIVE_ERROR = "存在递归溢出错误，可能存在无限循环或递归过深"
_RISK_TEXT_MEMORY_ERROR = "存在内存不足错误，需优化内存使用或增加资源"
_RISK_TEXT_TOOL_FAILURE_CHAIN = "工具调用链中失败调用较多（≥3 次），可能存在级联故障"
_CORE_MODULE_NAMES = ("__init__", "__main__", "main", "app",
                     "core", "base")
_LOW_CONFIDENCE_THRESHOLD = 0.55
_LONG_SESSION_THRESHOLD_S = 600
_BLOCK_MSG_MAX_CHARS = 20
_DEFAULT_CODE_MODIFIED = False
_DEFAULT_TASK_SUCCESS = True
_DEFAULT_DURATION = 0
_DEFAULT_ERROR_COUNT = 0
_DEFAULT_REFLEXION_ROUNDS = 2
_DEFAULT_ANALYSIS_FEATURE_ENABLED = True
_DEFAULT_TOOL_THRESHOLD = 3
_DEFAULT_MSG_LENGTH_THRESHOLD = 100
_DEFAULT_DURATION_THRESHOLD_SECONDS = 60
_DEFAULT_SCORE_MIN = 15
_LONG_TASK_IMPROVEMENT_THRESHOLD_S = 300
def analyze_session(
    user_messages: list[str] | None = None,
    tool_calls: list[dict[str, Any]] | None = None,
    errors: list[str] | None = None,
    code_modified: bool = _DEFAULT_CODE_MODIFIED,
    changed_files: list[str] | None = None,
    duration: int = _DEFAULT_DURATION,
    task_success: bool = _DEFAULT_TASK_SUCCESS,
    session_summary_hint: str = "",
    enable_reflexion: bool = _DEFAULT_ANALYSIS_FEATURE_ENABLED,
    reflexion_rounds: int = _DEFAULT_REFLEXION_ROUNDS,
    enable_root_cause: bool = _DEFAULT_ANALYSIS_FEATURE_ENABLED,
    enable_pattern_match: bool = _DEFAULT_ANALYSIS_FEATURE_ENABLED,
) -> AnalysisResult:
    messages = ensure_str_list(user_messages)
    calls = normalize_tool_calls(tool_calls)
    error_texts = ensure_str_list(errors)
    files_changed = ensure_str_list(changed_files)
    code_modified = as_bool(code_modified, default=_DEFAULT_CODE_MODIFIED)
    task_success = as_bool(task_success, default=_DEFAULT_TASK_SUCCESS)
    duration = max(0, normalize_scalar(
        duration, _DEFAULT_DURATION, want_int=True))
    hint = _ensure_str(session_summary_hint, default="")
    rounds = normalize_scalar(
        reflexion_rounds, _DEFAULT_REFLEXION_ROUNDS, want_int=True)
    enable_pattern_match = as_bool(
        enable_pattern_match, default=_DEFAULT_ANALYSIS_FEATURE_ENABLED)
    enable_root_cause = as_bool(
        enable_root_cause, default=_DEFAULT_ANALYSIS_FEATURE_ENABLED)
    enable_reflexion = as_bool(
        enable_reflexion, default=_DEFAULT_ANALYSIS_FEATURE_ENABLED)
    result = AnalysisResult()
    result.tool_stats = _compute_tool_stats(calls)
    result.error_patterns = [_classify_error(err) for err in error_texts]
    if enable_pattern_match:
        result.pattern_matches = _match_patterns(error_texts)
    result.risks = _identify_risks(
        error_patterns=result.error_patterns, tool_calls=calls,
        code_modified=code_modified, changed_files=files_changed,
        pattern_matches=result.pattern_matches, duration=duration,
        errors=error_texts)
    result.improvements = _extract_improvements(
        error_patterns=result.error_patterns, duration=duration,
        task_success=task_success, pattern_matches=result.pattern_matches)
    result.summary = _generate_summary(
        user_messages=messages, tool_stats=result.tool_stats,
        duration=duration, task_success=task_success, hint=hint,
        errors=error_texts, code_modified=code_modified)
    result.memory_candidates = _generate_memory_candidates_from_session(
        risks=result.risks, improvements=result.improvements,
        error_patterns=result.error_patterns,
        pattern_matches=result.pattern_matches)
    result.complexity_score = _compute_complexity(
        user_messages=messages, tool_calls=calls, errors=error_texts,
        duration=duration)
    if enable_root_cause and error_texts:
        result.root_causes = _analyze_root_causes(
            result.error_patterns, files_changed)
    if enable_reflexion and rounds > 0:
        _reflexion_loop(result, rounds, error_texts)
    result.prioritized_improvements = _prioritize_improvements(
        result.improvements, result.error_patterns)
    result.extraction_confidence = _compute_confidence(
        summary=result.summary, risks=result.risks,
        improvements=result.improvements)
    _apply_low_confidence_note(result)
    return result
def _apply_low_confidence_note(result: AnalysisResult) -> None:
    if result.extraction_confidence >= _LOW_CONFIDENCE_THRESHOLD:
        return
    logger.warning("[fupan_analyzer] 提取置信度低 %.2f"
                   "（summary=%d字符 risks=%d improvements=%d），复盘结论可靠性受限",
                   result.extraction_confidence, len(result.summary),
                   len(result.risks), len(result.improvements))
    _add_unique(result.risks, _RISK_TEXT_LOW_CONFIDENCE.format(
        confidence=result.extraction_confidence))
def _decode_text(value: Any) -> str:
    if isinstance(value, (bytes, bytearray)):
        return bytes(value).decode("utf-8", "replace")
    if isinstance(value, str):
        return value
    try:
        return str(value)
    except Exception as exc:
        log_swallowed(__name__, exc, context='_decode_text')
        return f"<{type(value).__name__}:{type(exc).__name__}>"
_USE_FALSEY_TEXT = object()
def _ensure_str(val: Any, default: Any = _USE_FALSEY_TEXT) -> str:
    if isinstance(val, (bytes, bytearray)):
        return _decode_text(val)
    if isinstance(val, str):
        return val
    if val:
        return str(val)
    if default is not _USE_FALSEY_TEXT:
        return default
    return "" if val is None else str(val)
def _finite_number(val: Any) -> float | None:
    if isinstance(val, bool):
        return None
    try:
        parsed = float(val)
    except (TypeError, ValueError, OverflowError) as _e:
        logger.debug(
            '静默降级[_finite_number]: %s: %s', type(_e).__name__, _e)
        return None
    return parsed if math.isfinite(parsed) else None
def as_float(val, default: float) -> float:
    number = _finite_number(val)
    return default if number is None else number
def as_int(val) -> int:
    number = _finite_number(val)
    return 0 if number is None else int(number)
_TRUE_SIGNAL_TEXT = frozenset({
    "true", "1", "yes", "y", "t", "ok", "success", "on", "enabled", "enable",
    "completed", "complete", "done", "finished", "passed", "pass",
    "succeeded", "successful",
})
_FALSE_SIGNAL_TEXT = frozenset({
    "false", "0", "no", "n", "f", "none", "null", "off", "disabled", "disable",
    "failed", "failure", "error", "cancelled", "canceled", "skipped",
})
def as_bool(val, default: bool) -> bool:
    if isinstance(val, bool):
        return val
    if val is None:
        return default
    if isinstance(val, (bytes, bytearray)):
        return as_bool(_decode_text(val), default)
    if isinstance(val, str):
        text = val.strip().casefold()
        if text in _TRUE_SIGNAL_TEXT:
            return True
        if text in _FALSE_SIGNAL_TEXT:
            return False
        number = _finite_number(text)
        return default if number is None else number != 0.0
    if isinstance(val, (int, float)):
        number = _finite_number(val)
        return default if number is None else number != 0.0
    return default
def ensure_str_list(val) -> list[str]:
    if isinstance(val, (set, frozenset)):
        val = sorted(val, key=lambda item: _decode_text(item).strip())
    return [text for item in coerce_text_list(val) if (text := item.strip())]
def ensure_list(val) -> list:
    if isinstance(val, (list, tuple, set, frozenset)):
        return list(val)
    return []
def normalize_scalar(val: Any, default: Any, want_int: bool = False) -> Any:
    parsed = _finite_number(val)
    if parsed is None:
        return default
    if want_int or parsed.is_integer():
        return int(parsed)
    return parsed
_TOOL_CALL_RECORD_KEYS = frozenset({
    "name", "count", "success", "command", "cmd", "args", "arguments",
    "input",
})
def _tool_calls_from_mapping(mapping: dict) -> list[dict[str, Any]]:
    if _TOOL_CALL_RECORD_KEYS & set(mapping):
        return [mapping]
    if mapping:
        return [{"name": key, "count": value}
                for key, value in mapping.items()]
    return []
def normalize_tool_calls(tool_calls: list) -> list[dict[str, Any]]:
    if isinstance(tool_calls, (set, frozenset)):
        tool_calls = sorted(
            tool_calls, key=lambda item: _decode_text(item).strip())
    elif isinstance(tool_calls, (list, tuple)):
        tool_calls = list(tool_calls)
    elif isinstance(tool_calls, dict):
        tool_calls = _tool_calls_from_mapping(tool_calls)
    elif tool_calls is None or isinstance(
            tool_calls, (str, bytes, bytearray)):
        tool_calls = [] if tool_calls is None else [tool_calls]
    else:
        try:
            tool_calls = list(tool_calls)
        except TypeError:
            tool_calls = [tool_calls]
    normalized: list[dict[str, Any]] = []
    for tc in tool_calls:
        if isinstance(tc, (bytes, bytearray)):
            tc = _decode_text(tc)
        if tc is None or (isinstance(tc, str) and not tc.strip()):
            continue
        if isinstance(tc, dict):
            normalized.append(tc)
        else:
            normalized.append({"name": _decode_text(tc), "count": 1})
    return normalized
def _norm_call_count(value: Any) -> int:
    number = _finite_number(value)
    if number is None:
        return 1
    return max(0, int(number))
def _tool_call_executed(tool_call: dict[str, Any]) -> bool:
    return _norm_call_count(tool_call.get("count")) > 0
def _tool_names(tool_calls: Any) -> list[str]:
    names: list[str] = []
    for record in normalize_tool_calls(tool_calls):
        if not _tool_call_executed(record):
            continue
        name = _decode_text(record.get("name") or "").strip()
        if name:
            names.append(name)
    return names
def _tool_text(value: Any) -> str:
    if isinstance(value, (str, bytes, bytearray)):
        return _decode_text(value)
    return " ".join(_tool_names(value))
def _compute_tool_stats(tool_calls: list[dict[str, Any]]) -> dict[str, int]:
    stats: dict[str, int] = {}
    for tc in tool_calls:
        if isinstance(tc, dict):
            name = _decode_text(tc.get("name") or "").strip()
            count = tc.get("count")
        else:
            name = _decode_text(tc).strip()
            count = None
        if not name:
            continue
        normalized_count = _norm_call_count(count)
        if normalized_count <= 0:
            continue
        stats[name] = stats.get(name, 0) + normalized_count
    return stats
def _classify_error(err: str) -> dict[str, Any]:
    for pattern_key, (regex, label) in ERROR_PATTERNS.items():
        if re.search(regex, err, re.IGNORECASE):
            return {"type": pattern_key, "label": label, "detail": err[:200]}
    return {"type": "unknown", "label": "未知错误", "detail": err[:200]}
def _match_patterns(errors):
    all_error_text = " ".join(errors)
    return [
        {
            "pattern_id": pattern["id"], "pattern_name": pattern["name"],
            "risk": pattern["risk"], "improvement": pattern["improvement"],
            "memory_category": pattern["memory_category"],
            "memory_detail": pattern["memory_detail"],
            "priority": pattern["priority"],
        }
        for pattern in FUPAN_PATTERNS
        if re.search(pattern["error_pattern"], all_error_text, re.IGNORECASE)
    ]
def _is_core_module_path(path: str) -> bool:
    base = os.path.basename(str(path or "").replace("\\", "/"))
    stem, ext = os.path.splitext(base)
    return ext.lower() == ".py" and stem in _CORE_MODULE_NAMES
def _core_touched_files(changed_files: list[str]) -> list[str]:
    return [f for f in changed_files if _is_core_module_path(f)]
_COMMAND_PATH_PREFIX_PATTERN = (
    r"(?:[\w./\\:-]*[\\/]|\"?[A-Za-z]:[\w./\\: -]*[\\/])?"
)
_PY_EXE_PATTERN = (
    rf"(?:{_COMMAND_PATH_PREFIX_PATTERN}python[0-9.]*(?:\.exe)?[\"']?"
    r"|py(?:\.exe)?(?=\s|[\"']?\s*,))"
)
_PY_MODULE_SEP_PATTERN = r"(?:\s+|[\"']?\s*,\s*[\"']?)"
_PY_INTERPRETER_OPTIONS_PATTERN = (
    rf"(?:{_PY_MODULE_SEP_PATTERN}(?:"
    rf"(?:-W|-X|--check-hash-based-pycs)"
    rf"{_PY_MODULE_SEP_PATTERN}[^\s,]+|-[^\s,]+))*?"
)
_PY_MODULE_TEST_PATTERN = (
    rf"(?<![A-Za-z0-9_]){_PY_EXE_PATTERN}"
    rf"{_PY_INTERPRETER_OPTIONS_PATTERN}"
    rf"{_PY_MODULE_SEP_PATTERN}-m{_PY_MODULE_SEP_PATTERN}"
    r"(?:pytest|unittest)(?![A-Za-z0-9_])"
)
_COVERAGE_RUN_VALUE_OPTIONS_PATTERN = (
    r"(?:--source|--omit|--include|--data-file|--rcfile|--context|--debug)"
    r"(?:\s+|=)[^\s,]+"
)
_COVERAGE_RUN_SCRIPT_OPTIONS_PATTERN = (
    rf"(?:\s+(?:{_COVERAGE_RUN_VALUE_OPTIONS_PATTERN}|-\S+))*"
)
_COVERAGE_RUN_TEST_PATTERN = (
    rf"(?<![A-Za-z0-9_])(?:{_PY_EXE_PATTERN}"
    rf"{_PY_INTERPRETER_OPTIONS_PATTERN}"
    rf"{_PY_MODULE_SEP_PATTERN}-m{_PY_MODULE_SEP_PATTERN})?"
    rf"{_COMMAND_PATH_PREFIX_PATTERN}coverage(?:\.exe)?"
    rf"{_PY_MODULE_SEP_PATTERN}run(?:"
    rf"(?:\s+[^\r\n]*?)?{_PY_MODULE_SEP_PATTERN}"
    rf"-m{_PY_MODULE_SEP_PATTERN}(?:pytest|unittest)(?![A-Za-z0-9_])"
    rf"|{_COVERAGE_RUN_SCRIPT_OPTIONS_PATTERN}\s+[\"']?[\w./\\:-]*"
    r"test_[A-Za-z0-9_]+\.py(?![A-Za-z0-9_]))"
)
_PY_MODULE_TEST_RE = re.compile(_PY_MODULE_TEST_PATTERN, re.IGNORECASE)
_TEST_SCRIPT_NAME_PATTERN = r"test(?::[A-Za-z0-9_.-]+)*"
_GO_TEST_COMMAND_PATTERN = (
    rf"{_COMMAND_PATH_PREFIX_PATTERN}go(?:\.exe)?[\"']?\s+test(?=\s|$)"
)
_GO_TEST_RE = re.compile(rf"^{_GO_TEST_COMMAND_PATTERN}", re.IGNORECASE)
_GO_COMPILE_ONLY_RE = re.compile(
    r"(?<![A-Za-z0-9_])-c(?![A-Za-z0-9_])", re.IGNORECASE)
_TEST_RUN_RE = re.compile(
    rf"^(?:{_COMMAND_PATH_PREFIX_PATTERN}(?:pytest|unittest|tox|nox)"
    rf"(?:\.exe)?[\"']?(?=\s|$)|{_GO_TEST_COMMAND_PATTERN}"
    rf"|npm\s+(?:run\s+{_TEST_SCRIPT_NAME_PATTERN}|test)(?=\s|$)"
    rf"|yarn\s+(?:run\s+)?{_TEST_SCRIPT_NAME_PATTERN}(?=\s|$)"
    rf"|pnpm\s+(?:run\s+)?{_TEST_SCRIPT_NAME_PATTERN}(?=\s|$)"
    rf"|bun\s+(?:run\s+{_TEST_SCRIPT_NAME_PATTERN}|test)(?=\s|$)"
    rf"|{_PY_MODULE_TEST_PATTERN}"
    rf"|{_COVERAGE_RUN_TEST_PATTERN}"
    rf"|{_PY_EXE_PATTERN}{_PY_INTERPRETER_OPTIONS_PATTERN}"
    rf"{_PY_MODULE_SEP_PATTERN}[\"']?[\w./\\:-]*"
    rf"test_[A-Za-z0-9_]+\.py(?![A-Za-z0-9_]))",
    re.IGNORECASE)
_TEST_TOOL_NAME_RE = re.compile(
    r"(?<![a-z0-9])(?:pytest|unittest|tests?)(?![a-z0-9])")
_TOOL_CALL_TEXT_FIELDS = ("command", "cmd", "args", "arguments", "input")
def _tool_text_values(value: Any, _include_numbers: bool = False) -> tuple[str, ...]:
    if isinstance(value, (str, bytes, bytearray)):
        return (_decode_text(value),)
    if _include_numbers and isinstance(value, (int, float)):
        return (_decode_text(value),)
    if isinstance(value, dict):
        return tuple(part for v in value.values()
                     for part in _tool_text_values(v))
    if isinstance(value, (list, tuple)):
        return tuple(part for v in value
                     for part in _tool_text_values(v, _include_numbers=True))
    return ()
def _tool_call_command_text(tc: dict[str, Any]) -> str:
    return " ".join(
        part
        for key in _TOOL_CALL_TEXT_FIELDS
        for part in _tool_text_values(tc.get(key))
    )
_ENV_ASSIGNMENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")
_ENV_OPTIONS_WITH_VALUE = frozenset({
    "-u", "--unset", "-C", "--chdir",
})
_ENV_SPLIT_STRING_OPTIONS = frozenset({"-S", "--split-string"})
_UV_RUN_OPTIONS_WITH_VALUE = frozenset({
    "-p", "--python", "--with", "--with-editable", "--extra", "--group",
    "--project", "--package", "--env-file", "--directory",
})
_POSIX_SHELL_LAUNCHERS = frozenset({"bash", "sh", "zsh"})
_WINDOWS_SHELL_LAUNCHERS = frozenset({"cmd", "powershell", "pwsh"})
# bash/sh 带值的启动选项：其值是下一个 token，不是待执行的命令
_POSIX_SHELL_OPTIONS_WITH_VALUE = frozenset({
    "-o", "--option", "-O", "--rcfile", "--init-file",
})
def _command_launcher_name(token: str) -> str:
    return (token.replace("\\", "/").rsplit("/", 1)[-1]
            .lower().removesuffix(".exe"))
def _executable_command_text(tokens: list[str]) -> str:
    index = 0
    while index < len(tokens):
        token = tokens[index]
        if _ENV_ASSIGNMENT_RE.match(token):
            index += 1
            continue
        if _command_launcher_name(token) == "env":
            index += 1
            while index < len(tokens):
                option = tokens[index]
                if _ENV_ASSIGNMENT_RE.match(option):
                    index += 1
                    continue
                if (option in _ENV_SPLIT_STRING_OPTIONS
                        or option.startswith("--split-string=")):
                    if option.startswith("--split-string="):
                        split_text = option.partition("=")[2]
                        remaining = tokens[index + 1:]
                    elif index + 1 < len(tokens):
                        split_text = tokens[index + 1]
                        remaining = tokens[index + 2:]
                    else:
                        return ""
                    split_lexer = shlex.shlex(split_text, posix=True)
                    split_lexer.whitespace_split = True
                    split_lexer.commenters = ""
                    split_lexer.escape = ""
                    return _executable_command_text(
                        [*split_lexer, *remaining])
                if option in _ENV_OPTIONS_WITH_VALUE:
                    index += 2
                    continue
                if option == "-":
                    index += 1
                    continue
                if not option.startswith("-"):
                    break
                index += 1
            continue
        break
    if index + 1 < len(tokens):
        launcher = _command_launcher_name(tokens[index])
        argument = tokens[index + 1].lower()
        is_run_launcher = (
            launcher in {"uv", "poetry", "pipenv"} and argument == "run")
        if is_run_launcher:
            index += 2
            options_with_value = (
                _UV_RUN_OPTIONS_WITH_VALUE if launcher == "uv" else ())
            while index < len(tokens):
                option = tokens[index]
                if option == "--":
                    index += 1
                    break
                if not option.startswith("-"):
                    break
                index += 1
                if option in options_with_value and index < len(tokens):
                    index += 1
        elif launcher in _POSIX_SHELL_LAUNCHERS | _WINDOWS_SHELL_LAUNCHERS:
            cursor = index + 1
            while cursor < len(tokens):
                option = tokens[cursor].lower()
                if launcher in _POSIX_SHELL_LAUNCHERS:
                    is_command = option == "-c" or (
                        option.startswith("-")
                        and not option.startswith("--")
                        and "c" in option[1:])
                    if option == "--" or (
                            not is_command and not option.startswith("-")):
                        break
                    takes_next_value = (
                        option in _POSIX_SHELL_OPTIONS_WITH_VALUE
                        or (option.startswith("-")
                            and not option.startswith("--")
                            and option.endswith("o")))
                    if takes_next_value:
                        cursor += 2
                        continue
                else:
                    is_command = option in {"/c", "-c", "-command"}
                if is_command:
                    index = cursor + 1
                    break
                cursor += 1
    return " ".join(tokens[index:])
_MAX_NESTED_COMMAND_DEPTH = 8
def _command_segments(tokens: list[str], depth: int) -> list[str]:
    command = _executable_command_text(tokens)
    if not command:
        return []
    if depth >= _MAX_NESTED_COMMAND_DEPTH or command == " ".join(tokens):
        return [command]
    return _shell_command_segments(command, depth + 1)
def _shell_command_segments(text: str, depth: int = 0) -> list[str]:
    segments: list[str] = []
    for line in text.splitlines() or [text]:
        lexer = shlex.shlex(line, posix=True, punctuation_chars=";&|")
        lexer.whitespace_split = True
        lexer.commenters = "#"
        lexer.escape = ""
        current: list[str] = []
        try:
            for token in lexer:
                if token and set(token) <= set(";&|"):
                    segments.extend(_command_segments(current, depth))
                    current = []
                else:
                    current.append(token)
            segments.extend(_command_segments(current, depth))
        except ValueError as exc:
            logger.debug("测试命令分段失败，保留已识别命令段: %s", exc)
            continue
    return segments
_NON_EXECUTING_TEST_OPTION_RE = re.compile(
    r"(?<![A-Za-z0-9_])(?:--help|-h|--version|--co(?:llect-only)?"
    r"|--fixtures|--funcargs|--markers|--notest|--list)"
    r"(?![A-Za-z0-9_])", re.IGNORECASE)
def _is_test_execution_segment(segment: str) -> bool:
    option_scope = segment.partition(" -- ")[0]
    if (_TEST_RUN_RE.search(segment) is None
            or _NON_EXECUTING_TEST_OPTION_RE.search(option_scope) is not None):
        return False
    return not (_GO_TEST_RE.search(segment)
                and _GO_COMPILE_ONLY_RE.search(option_scope))
def _ran_test_tool(tool_calls: list[dict[str, Any]]) -> bool:
    for tc in tool_calls:
        if not isinstance(tc, dict) or not _tool_call_executed(tc):
            continue
        tool_name = _decode_text(tc.get("name") or "").lower()
        command_text = _tool_call_command_text(tc)
        segments = _shell_command_segments(command_text)
        if any(_is_test_execution_segment(segment) for segment in segments):
            return True
        if (_TEST_TOOL_NAME_RE.search(tool_name)
                and not any(_NON_EXECUTING_TEST_OPTION_RE.search(
                    segment.partition(" -- ")[0]) for segment in segments)):
            return True
    return False
def _add_unique(items: list[str], item: str) -> None:
    if item not in items:
        items.append(item)
def _scan_code_risks(changed_files, code_modified, tool_calls):
    risks: list[str] = []
    core_touched = _core_touched_files(changed_files)
    if core_touched:
        _add_unique(risks, _RISK_TEXT_CORE_MODULE_TOUCHED.format(
            files=", ".join(core_touched[:3])))
    if len(changed_files) > 10:
        _add_unique(risks, _RISK_TEXT_MANY_FILES_CHANGED.format(
            count=len(changed_files)))
    if code_modified and not _ran_test_tool(tool_calls):
        _add_unique(risks, _RISK_TEXT_NO_TEST_RUN)
    return risks
def _has_error_marker(error_patterns, marker):
    folded_marker = marker.casefold()
    return any(
        folded_marker in str(e.get("detail") or "").casefold()
        for e in error_patterns
    )
_RESOURCE_RISK_MARKERS: tuple[tuple[str, str], ...] = (
    ("RecursionError", _RISK_TEXT_RECURSIVE_ERROR),
    ("MemoryError", _RISK_TEXT_MEMORY_ERROR),
)
def _append_resource_risks(risks, error_patterns, errors=None):
    full_text = (" ".join(str(e) for e in errors).casefold()
                 if errors else "")
    for marker, risk_text in _RESOURCE_RISK_MARKERS:
        if marker.casefold() in full_text or _has_error_marker(error_patterns, marker):
            _add_unique(risks, risk_text)
def _error_type_labels(error_patterns) -> dict[str, str]:
    labels: dict[str, str] = {}
    for ep in error_patterns:
        etype = str(ep.get("type") or "unknown")
        labels.setdefault(etype, str(ep.get("label") or etype))
    return labels
def _append_error_type_risks(risks, error_patterns):
    labels = _error_type_labels(error_patterns)
    type_counts = Counter(str(e.get("type") or "unknown") for e in error_patterns)
    for etype, count in type_counts.items():
        if count >= 3:
            _add_unique(risks, _RISK_TEXT_ERROR_REPEAT.format(
                error_type=labels.get(etype, etype), count=count))
    if len(type_counts) >= 3:
        _add_unique(risks, _RISK_TEXT_MIXED_ERROR_TYPES.format(
            types=", ".join(labels.get(etype, etype)
                            for etype in list(type_counts)[:5])))
def _append_failure_chain_risk(risks, tool_calls):
    failure_count = 0
    for tc in tool_calls:
        if not isinstance(tc, dict):
            continue
        if as_bool(tc.get("success", True), default=True):
            continue
        failure_count += _norm_call_count(tc.get("count"))
    if failure_count >= 3:
        _add_unique(risks, _RISK_TEXT_TOOL_FAILURE_CHAIN)
def _pattern_risk_texts(pattern_matches) -> list[str]:
    return list(dict.fromkeys(
        risk for pm in pattern_matches or ()
        if isinstance(pm, dict) and (risk := pm.get("risk"))))
def _scan_process_risks(error_patterns, tool_calls, pattern_matches,
                        duration, errors=None):
    risks = _pattern_risk_texts(pattern_matches)
    if duration > _LONG_SESSION_THRESHOLD_S:
        _add_unique(risks, _RISK_TEXT_LONG_SESSION.format(duration=duration))
    _append_resource_risks(risks, error_patterns, errors)
    _append_error_type_risks(risks, error_patterns)
    _append_failure_chain_risk(risks, tool_calls)
    return risks
def _identify_risks(error_patterns, tool_calls, code_modified, changed_files,
                    pattern_matches, duration, errors=None):
    code_risks = _scan_code_risks(changed_files, code_modified, tool_calls)
    process_risks = _scan_process_risks(
        error_patterns, tool_calls, pattern_matches,
        duration=duration, errors=errors)
    return list(dict.fromkeys(code_risks + process_risks))
def _extract_improvements(
    error_patterns: list[dict[str, Any]],
    duration: int,
    task_success: bool,
    pattern_matches: list[dict[str, Any]],
) -> list[str]:
    candidates = [pm["improvement"] for pm in pattern_matches]
    candidates.extend(
        IMPROVEMENT_BY_ERROR_TYPE[ep["type"]]
        for ep in error_patterns
        if ep.get("type", "") in IMPROVEMENT_BY_ERROR_TYPE)
    improvements = list(dict.fromkeys(candidates))
    if not task_success:
        improvements.append("分步执行并在每步后运行定向测试，提前阻断错误传播")
    if duration > _LONG_TASK_IMPROVEMENT_THRESHOLD_S:
        improvements.append("拆分大型任务为子任务，逐步执行并逐步验证")
    return improvements
def _impact_source_by_improvement() -> dict[str, str]:
    type_by_improvement: dict[str, str] = {}
    impact_sources = [
        (pattern["error_type"], pattern["improvement"])
        for pattern in FUPAN_PATTERNS
    ]
    impact_sources.extend(IMPROVEMENT_BY_ERROR_TYPE.items())
    for etype, imp in impact_sources:
        held = type_by_improvement.get(imp)
        if held is None or (ERROR_TYPE_SEVERITY.get(etype, 5)
                            > ERROR_TYPE_SEVERITY.get(held, 5)):
            type_by_improvement[imp] = etype
    return type_by_improvement
def _prioritize_improvements(
    improvements: list[str],
    error_patterns: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    type_by_improvement = _impact_source_by_improvement()
    error_type_counts = Counter(ep.get("type", "") for ep in error_patterns)
    prioritized = []
    for imp in improvements:
        source_type = type_by_improvement.get(imp)
        impact = ERROR_TYPE_SEVERITY.get(source_type, 5) if source_type else 5
        urgency = error_type_counts.get(source_type, 0) if source_type else 0
        priority_score = impact * (1 + math.log(urgency + 1))
        prioritized.append({"improvement": imp, "impact": round(float(impact), 1),
                            "urgency": urgency,
                            "priority_score": round(priority_score, 1)})
    prioritized.sort(key=lambda x: x["priority_score"], reverse=True)
    return prioritized
def _summary_subject_part(hint, user_messages) -> list[str]:
    if hint and str(hint).strip():
        return [str(hint).strip()]
    if not user_messages:
        return []
    first_msg = user_messages[0].strip()
    if len(first_msg) > 80:
        first_msg = first_msg[:77] + "..."
    return [f"用户请求: {first_msg}"]
def _summary_tools_part(tool_stats) -> list[str]:
    top_tools = sorted(tool_stats.items(), key=lambda x: (-x[1], x[0]))[:5]
    if not top_tools:
        return []
    tool_desc = ", ".join(f"{n}({c}次)" for n, c in top_tools)
    return [f"工具使用: {tool_desc}"]
def _generate_summary(user_messages, tool_stats, duration, task_success, hint, errors, code_modified):
    parts: list[str] = []
    parts.extend(_summary_subject_part(hint, user_messages))
    parts.extend(_summary_tools_part(tool_stats))
    status = "成功" if task_success else f"失败({len(errors)}个错误)"
    parts.append(f"任务状态: {status}")
    if code_modified:
        parts.append("涉及代码修改")
    if duration > 0:
        parts.append(f"用时{duration}s")
    return " | ".join(parts)
def _pattern_candidates(pattern_matches, candidates) -> None:
    for pm in pattern_matches[:3]:
        detail = pm.get("memory_detail", "")
        if not detail or len(detail) < 15:
            continue
        candidates.append({
            "detail": f"[模式匹配:{pm['pattern_name']}] {detail[:200]}",
            "category": pm.get("memory_category", "避坑"),
            "source": "自动复盘-模式匹配",
            "priority": pm.get("priority", "P1-核心"),
        })
def _error_candidates(error_patterns, candidates) -> None:
    seen_types = set()
    for ep in error_patterns:
        etype = ep.get("type", "")
        if etype in seen_types or etype == "unknown":
            continue
        seen_types.add(etype)
        detail = f"[自动提取] {ep.get('label', '错误')}: {ep.get('detail', '')[:150]}"
        candidates.append({
            "detail": detail,
            "category": "避坑",
            "source": "自动复盘-错误分析",
            "priority": "P1-核心",
        })
        if len(seen_types) >= 5:
            break
def _accept_risk_candidate(risk, seen_risks, candidates) -> bool:
    if not risk or len(risk) < 10:
        return False
    risk_key = risk[:50]
    if risk_key in seen_risks:
        return False
    if any(risk[:30] in c.get("detail", "") for c in candidates):
        return False
    seen_risks.add(risk_key)
    return True
def _risk_candidates(risks, candidates) -> None:
    seen_risks = set()
    for risk in risks[:3]:
        if not _accept_risk_candidate(risk, seen_risks, candidates):
            continue
        candidates.append({
            "detail": f"[自动提取-风险] {risk[:200]}",
            "category": "避坑",
            "source": "自动复盘-风险检测",
            "priority": "P1-核心",
        })
def _improvement_candidates(improvements, candidates) -> None:
    for imp in improvements[:2]:
        if not any(imp[:30] in c.get("detail", "") for c in candidates):
            candidates.append({
                "detail": f"[自动提取] {imp[:200]}",
                "category": "优化",
                "source": "自动复盘-改进建议",
                "priority": "P2-通用",
            })
def _generate_memory_candidates_from_session(risks, improvements, error_patterns, pattern_matches):
    candidates: list[dict[str, Any]] = []
    _pattern_candidates(pattern_matches, candidates)
    _error_candidates(error_patterns, candidates)
    _risk_candidates(risks, candidates)
    _improvement_candidates(improvements, candidates)
    return candidates
def _chars_score(user_messages):
    total_chars = sum(len(m) for m in user_messages)
    if total_chars > 2000:
        return 25
    if total_chars > 500:
        return 15
    return 0
def _tools_score(tool_calls):
    tool_stats = _compute_tool_stats(tool_calls)
    unique_tools = len(tool_stats)
    score = 0
    if unique_tools >= 4:
        score += 20
    elif unique_tools >= 2:
        score += 10
    if sum(tool_stats.values()) >= 15:
        score += 10
    return score
def _errors_score(errors):
    if len(errors) >= 5:
        return 25
    if len(errors) >= 2:
        return 15
    if len(errors) >= 1:
        return 5
    return 0
def _duration_score(duration):
    if duration > _LONG_SESSION_THRESHOLD_S:
        return 20
    if duration > 120:
        return 10
    return 0
def _compute_complexity(user_messages, tool_calls, errors, duration):
    score = (_chars_score(user_messages) + _tools_score(tool_calls)
             + _errors_score(errors) + _duration_score(duration))
    return min(score, 100)
def _first_error_root_cause(error_patterns: list[dict[str, Any]]) -> dict[str, Any]:
    first_error = error_patterns[0]
    return {
        "type": "first_error", "error_type": first_error.get("type", ""),
        "confidence": 0.7 if len(error_patterns) > 1 else 0.5,
        "description": f"首个错误为{first_error.get('label', '未知')}，可能是级联故障的根因",
    }
def _cascade_root_cause(error_patterns: list[dict[str, Any]]) -> dict[str, Any]:
    cascade_types = [ep.get("type", "") for ep in error_patterns[1:]]
    return {
        "type": "cascade", "cascade_types": cascade_types, "confidence": 0.6,
        "description": (f"后续{len(cascade_types)}个错误可能是级联故障: "
                        f"{', '.join(cascade_types[:3])}"),
    }
def _file_correlation_root_cause(changed_files: list[str]) -> dict[str, Any]:
    return {
        "type": "file_correlation", "changed_files": changed_files[:5],
        "confidence": 0.5,
        "description": (f"变更了{len(changed_files)}个文件，错误可能与以下文件相关: "
                        f"{', '.join(changed_files[:3])}"),
    }
def _analyze_root_causes(error_patterns, changed_files):
    if not error_patterns:
        return []
    root_causes = [_first_error_root_cause(error_patterns)]
    if len(error_patterns) >= 2:
        root_causes.append(_cascade_root_cause(error_patterns))
    if changed_files:
        root_causes.append(_file_correlation_root_cause(changed_files))
    return root_causes
def _reflexion_loop(result, max_rounds, errors):
    for round_num in range(max_rounds):
        quality_issues = _evaluate_analysis_quality(result)
        if not quality_issues:
            break
        if not _apply_reflexion_fixes(result, quality_issues, errors):
            break
        result.reflexion_rounds = round_num + 1
    return result
def _vague_improvement_count(improvements: list[str]) -> int:
    return sum(1 for imp in improvements if _is_vague(imp))
def _evaluate_analysis_quality(result: AnalysisResult) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if len(result.risks) < 2 and len(result.error_patterns) >= 2:
        issues.append({"type": "missing_risk", "severity": "medium"})
    vague_count = _vague_improvement_count(result.improvements)
    if vague_count > 0:
        issues.append({"type": "vague_improvement", "severity": "low", "count": vague_count})
    return issues
def _apply_missing_risk_fix(result, errors) -> bool:
    if not errors:
        return False
    new_risk = _infer_missing_risk(errors, result.risks)
    if new_risk and new_risk not in result.risks:
        result.risks.append(new_risk)
        return True
    return False
def _apply_vague_fix(result, errors) -> bool:
    refined = _refine_improvement(errors)
    if not (refined and refined not in result.improvements):
        return False
    for i, imp in enumerate(result.improvements):
        if _is_vague(imp):
            result.improvements[i] = refined
            return True
    return False
def _apply_reflexion_fixes(result, quality_issues, errors) -> bool:
    logger.debug("[fupan_analyzer] reflexion 修复 %d 项质量问题: %s",
                 len(quality_issues), [i.get("type") for i in quality_issues])
    fixes: list[bool] = []
    for issue in quality_issues:
        fixer = _REFLEXION_FIXERS.get(issue["type"])
        if fixer is not None:
            fixes.append(fixer(result, errors))
    return any(fixes)
_REFLEXION_FIXERS = {
    "missing_risk": _apply_missing_risk_fix,
    "vague_improvement": _apply_vague_fix,
}
_VAGUE_PREFIXES = (
    "建议", "考虑", "可以", "尝试", "或许", "也许", "应当", "应该",
    "consider", "suggest", "try", "maybe", "perhaps", "you should",
    "recommend", "should",
)
_CJK_CHAR_RE = re.compile(r"[\u4e00-\u9fff]")
_ASCII_WORD_RE = re.compile(r"[A-Za-z][A-Za-z0-9_'-]*")
_VAGUE_PREFIXES_FOLDED = tuple(prefix.casefold()
                                  for prefix in _VAGUE_PREFIXES)
_VAGUE_ADVICE_MAX_UNITS = 30
def _advice_units(text: str) -> int:
    return (len(_CJK_CHAR_RE.findall(text))
            + 2 * len(_ASCII_WORD_RE.findall(text)))
def _is_vague(improvement):
    if not isinstance(improvement, str):
        return False
    text = improvement.strip()
    if _advice_units(text) >= _VAGUE_ADVICE_MAX_UNITS:
        return False
    return text.casefold().startswith(_VAGUE_PREFIXES_FOLDED)
def _refine_improvement(errors):
    for err in errors[:3]:
        if "ModuleNotFoundError" in err:
            m = re.search(r"No module named '([\w.]+)'", err)
            if m:
                return f"安装缺失模块: pip install {m.group(1)}"
        if "FileNotFoundError" in err:
            m = re.search(r"No such file[^'\"]*['\"]([^'\"]+)['\"]", err)
            if m:
                return f"创建缺失文件或修正路径: {m.group(1)}"
    return None
def _risk_mentions(risks, markers) -> bool:
    folded_markers = tuple(str(marker).casefold() for marker in markers)
    return any(
        marker in str(risk).casefold()
        for risk in risks or ()
        for marker in folded_markers
    )
def _infer_missing_risk(errors, existing_risks):
    all_text = " ".join(errors).casefold()
    if ("recursionerror" in all_text
            and not _risk_mentions(existing_risks,
                                   ("递归", "recursion", "recursive"))):
        return _RISK_TEXT_RECURSIVE_ERROR
    if ("memoryerror" in all_text
            and not _risk_mentions(existing_risks,
                                   ("内存", "memory", "out of memory"))):
        return _RISK_TEXT_MEMORY_ERROR
    return None
def _compute_confidence(summary, risks, improvements):
    confidence = 0.5
    if summary and len(summary) > 20:
        confidence += 0.10
    if risks:
        confidence += min(0.15, len(risks) * 0.04)
    if improvements:
        confidence += min(0.10, len(improvements) * 0.03)
    return min(confidence, 0.95)
def to_fupan_params(result: AnalysisResult) -> dict[str, Any]:
    return {"summary": result.summary, "risks": list(result.risks),
            "improvements": list(result.improvements),
            "memory_candidates": [
                copy.deepcopy(item) for item in result.memory_candidates
                if isinstance(item, dict)]}
_CODE_WRITE_TOOLS = frozenset({
    "file", "python_cell_exec", "bash", "shell", "terminal", "exec",
    "python", "ipython", "apply_patch", "write_file", "edit_file",
    "create_file", "str_replace_editor", "notebook_edit",
})
_CODE_WRITE_MARKERS = ("write", "edit", "patch", "apply", "create",
                       "save", "replace", "modify")
_CODE_SUBJECT_MARKERS = ("file", "code", "source", "script", "module")
def _is_code_write_token(token: str) -> bool:
    if token in _CODE_WRITE_TOOLS:
        return True
    if not any(subject in token for subject in _CODE_SUBJECT_MARKERS):
        return False
    return (any(marker in token for marker in _CODE_WRITE_MARKERS)
            or "update" in token)
def _check_code_modified(tools_used: str) -> tuple[bool, str, str]:
    for token in _extract_tool_types(tools_used):
        if _is_code_write_token(token):
            return True, "代码级操作", "R7-代码修改"
    return False, "", ""
_TOOL_TOKEN_SPLIT_RE = re.compile(r"[\s,;|()\[\]{}]+")
_TOOL_TOKEN_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.:/\\-]*$")
def _normalize_tool_token(value: Any) -> str:
    text = _decode_text(value).strip().lower().replace("\\", "/")
    text = text.rsplit("/", 1)[-1]
    if text.endswith(".exe"):
        text = text[:-4]
    else:
        namespace, dot, suffix = text.rpartition(".")
        if namespace and dot and suffix and not suffix[0].isdigit():
            text = suffix
    return text.replace("-", "_")
def _extract_tool_types(tools_used: str) -> set:
    if not isinstance(tools_used, (str, bytes, bytearray)):
        return set()
    tokens = _TOOL_TOKEN_SPLIT_RE.split(_decode_text(tools_used))
    return {_normalize_tool_token(token)
            for token in tokens if _TOOL_TOKEN_RE.match(token)}
def _calc_importance(score: int, code_modified: bool, task_type: str) -> int:
    if task_type and code_modified:
        return 4
    if score >= 3:
        return 3
    return 2
def detect_fupan_execution(
    tools_used: str = "",
    outcome_detail: str = "",
    task_type: str = "",
) -> dict[str, Any]:
    tools_used = _tool_text(tools_used)
    outcome_detail = _ensure_str(outcome_detail)
    task_type = _ensure_str(task_type).strip()
    score = 0
    reasons: list[str] = []
    signals: list[str] = []
    code_modified, reason, signal = _check_code_modified(tools_used)
    if code_modified:
        score += 1
        reasons.append(reason)
        signals.append(signal)
    tool_types = _extract_tool_types(tools_used)
    if len(tool_types) >= 3:
        score += 1
        reasons.append(f"多工具调用({len(tool_types)})")
        signals.append("R4-复杂任务")
    if len(outcome_detail) > 300:
        score += 1
        reasons.append("深度输出")
    importance = _calc_importance(score, code_modified, task_type)
    should = score >= 2
    logger.info("detect_fupan_execution 判定: should=%s score=%s importance=%s",
                should, score, importance)
    return {"should": should, "score": score, "reasons": reasons,
            "signals": signals or ["非闲聊任务"], "importance": importance}
def _keyword_spans(text: str, keyword: str) -> list[tuple[int, int]]:
    if not text or not keyword:
        return []
    pattern = re.escape(keyword)
    if keyword.isascii():
        if keyword[0].isalnum() or keyword[0] == "_":
            pattern = rf"(?<![A-Za-z0-9_]){pattern}"
        if keyword[-1].isalnum() or keyword[-1] == "_":
            pattern = rf"{pattern}(?![A-Za-z0-9_])"
    return [match.span() for match in re.finditer(
        pattern, text, re.IGNORECASE)]
def _unshadowed_occurrences(
    occurrences: list[tuple[int, int, Any]],
) -> list[tuple[int, int, Any]]:
    active: list[tuple[int, int, Any]] = []
    for index, occurrence in enumerate(occurrences):
        start, end, _payload = occurrence
        shadowed = False
        for other_index, (other_start, other_end, _other) in enumerate(
                occurrences):
            if index == other_index or not (
                    other_start <= start and end <= other_end):
                continue
            length, other_length = end - start, other_end - other_start
            if (other_length > length
                    or (other_length == length and other_index < index)):
                shadowed = True
                break
        if not shadowed:
            active.append(occurrence)
    return active
def _keyword_hits(text: Any, keywords: Any) -> list[str]:
    text = _ensure_str(text)
    if not text.strip():
        return []
    candidates: list[str] = []
    seen: set[str] = set()
    for keyword in ensure_str_list(keywords):
        folded = keyword.casefold()
        if not folded or folded in seen:
            continue
        seen.add(folded)
        candidates.append(keyword)
    occurrences = [
        (start, end, keyword)
        for keyword in candidates
        for start, end in _keyword_spans(text, keyword)
    ]
    active_keywords = {
        keyword for _start, _end, keyword in _unshadowed_occurrences(occurrences)
    }
    return [keyword for keyword in candidates if keyword in active_keywords]
_LOOP_STEPS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("S1-复盘沉淀", (
        "复盘", "陷阱", "反思", "踩坑", "问题总结",
        "retrospective", "reflection", "reflect", "pitfall",
        "lessons learned", "lesson learned", "root cause",
    )),
    ("S2-隐患排查", (
        "隐患", "核查", "风险", "潜在", "排查",
        "risk", "hazard", "audit", "investigation", "potential issue",
    )),
    ("S3-迭代优化", (
        "改进", "优化", "修复", "避坑",
        "improvement", "optimization", "refactor", "fix",
        "remediation", "prevent recurrence",
    )),
    ("S4-记忆注入", (
        "记忆写入", "经验沉淀", "记忆注入", "复盘完成",
        "memory write", "memory written", "memory update",
        "experience captured", "lesson recorded",
        "retrospective complete", "retrospective completed",
    )),
)
_BLOCK_FILLER_TOKENS = (
    "there", "please", "everyone", "all", "again", "now", "team", "guys",
    "呀", "啊", "哦", "呢", "哈", "嘛", "啦", "吧", "吗", "了", "的",
    "哟", "哇",
)
_BLOCK_FILLERS_SORTED = tuple(
    sorted(_BLOCK_FILLER_TOKENS, key=len, reverse=True))
_NON_WORD_CHARS_RE = re.compile(r"[\W_]+", re.UNICODE)
def _normalized_blocker_text(value: Any) -> str:
    residual = _NON_WORD_CHARS_RE.sub("", _ensure_str(value).casefold())
    for filler in _BLOCK_FILLERS_SORTED:
        residual = residual.replace(filler, "")
    return residual
def _blocker_hits(text: str, keywords) -> list[str]:
    residual = _normalized_blocker_text(text)
    if not residual:
        return []
    hits: list[str] = []
    for keyword in ensure_str_list(keywords):
        normalized_keyword = _normalized_blocker_text(keyword)
        if normalized_keyword and residual == normalized_keyword:
            hits.append(keyword)
    return hits
def _loop_step_hits(combined: str) -> dict[str, bool]:
    hits: dict[str, bool] = {}
    for name, keywords in _LOOP_STEPS:
        occurrences: list[tuple[int, int, str]] = [
            (start, end, keyword)
            for keyword in ensure_str_list(keywords)
            for start, end in _keyword_spans(combined, keyword)
        ]
        hits[name] = bool(_unshadowed_occurrences(occurrences))
    return hits
def close_loop_check(
    tools_used: str = "", outcome_detail: str = "",
) -> dict[str, Any]:
    tools_used = _tool_text(tools_used)
    outcome_detail = _ensure_str(outcome_detail)
    detected = detect_fupan_execution(
        tools_used=tools_used, outcome_detail=outcome_detail)
    combined = tools_used + " " + outcome_detail
    steps = _loop_step_hits(combined)
    found = [name for name, ok in steps.items() if ok]
    missing = [name for name, ok in steps.items() if not ok]
    loop_complete = all(steps.values())
    logger.info("close_loop_check 判定: loop_complete=%s found=%d missing=%d",
                loop_complete, len(found), len(missing))
    return {"fupan_executed": detected, "loop_complete": loop_complete,
            "steps_found": found, "steps_missing": missing}
DEFAULT_CONFIG = {
    "enabled": True,
    "block_keywords": ["你好", "在吗", "测试", "ping", "hello", "hi",
                       "are you there", "test"],
    "review_keywords": [
        "复盘", "反思", "经验沉淀", "回顾", "教训", "总结", "改进", "记忆",
        "retrospective", "reflection", "reflect", "review",
        "postmortem", "post-mortem", "lessons learned", "lesson",
        "summary", "improvement",
    ],
    "tool_threshold": _DEFAULT_TOOL_THRESHOLD,
    "msg_length_threshold": _DEFAULT_MSG_LENGTH_THRESHOLD,
    "duration_threshold_seconds": _DEFAULT_DURATION_THRESHOLD_SECONDS,
    "score_min": _DEFAULT_SCORE_MIN,
    "version": "1.0.0",
}
def _cfg_text_list(cfg: dict, key: str, fallback: list[str]) -> list[str]:
    values = cfg.get(key, fallback)
    if not isinstance(values, (list, tuple, set, frozenset)):
        return list(dict.fromkeys(ensure_str_list(fallback)))
    return list(dict.fromkeys(ensure_str_list(values)))
_NUMERIC_CONFIG_MINIMUMS = {
    "tool_threshold": 1, "msg_length_threshold": 1,
    "duration_threshold_seconds": 0, "score_min": 0,
}
def _load_config() -> dict:
    cfg = copy.deepcopy(DEFAULT_CONFIG)
    for key in ("block_keywords", "review_keywords"):
        cfg[key] = _cfg_text_list(cfg, key, DEFAULT_CONFIG[key])
    for key, minimum in _NUMERIC_CONFIG_MINIMUMS.items():
        default = max(
            minimum,
            normalize_scalar(DEFAULT_CONFIG[key], minimum, want_int=True))
        value = normalize_scalar(cfg.get(key), default, want_int=True)
        cfg[key] = value if value >= minimum else default
    default_enabled = as_bool(
        DEFAULT_CONFIG.get("enabled"), default=True)
    cfg["enabled"] = as_bool(cfg.get("enabled"), default=default_enabled)
    return cfg
def _blocked_result(reasons: list[str], signals: list[str]) -> dict[str, Any]:
    return {"should": False, "score": 0, "reasons": reasons,
            "importance": 1, "signals": signals, "rule": "R1_blocker"}
def _sr_check_blocker(user_msg, cfg):
    if not user_msg or not user_msg.strip():
        return None
    if len(_normalized_blocker_text(user_msg)) >= _BLOCK_MSG_MAX_CHARS:
        return None
    for kw in _blocker_hits(user_msg, cfg["block_keywords"]):
        logger.info("should_fupan 阻断: 命中 blocker=%s", kw)
        return _blocked_result([f"命中 blocker: {kw}"], ["blocked"])
    return None
def _rule_no_hit() -> tuple[int, list[str], list[str], int, str]:
    return 0, [], [], 0, ""
def _sr_rule_r2(error_count, task_success):
    reasons: list[str] = []
    signals: list[str] = []
    if error_count > 0:
        reasons.append(f"错误信号: {error_count}个错误")
        signals.append(f"error:{error_count}")
    if not task_success:
        reasons.append("任务执行失败")
        signals.append("task_failed")
    if reasons:
        return 40, reasons, signals, 5, "R2_p0"
    return _rule_no_hit()
def _sr_rule_r3(combined_text, cfg):
    score, reasons, signals, importance, rule = _rule_no_hit()
    for kw in _keyword_hits(combined_text, cfg["review_keywords"]):
        score = max(score, 75)
        reasons.append(f"关键词触发: {kw}")
        signals.append(f"keyword:{kw}")
        importance = max(importance, 4)
        if not rule:
            rule = "R3_keyword"
    return score, reasons, signals, importance, rule
def _count_tool_types(tools_used) -> int:
    return len(_extract_tool_types(_tool_text(tools_used)))
def _sr_rule_r4(tools_used, cfg):
    tool_count = _count_tool_types(tools_used)
    if tool_count >= cfg["tool_threshold"]:
        return 25, [f"工具链丰富: {tool_count}种"], [f"tools:{tool_count}"], 3, "R4_tools"
    return _rule_no_hit()
def _sr_rule_r5(msg_len, duration, cfg):
    score, reasons, signals, importance, rule = _rule_no_hit()
    if msg_len >= cfg["msg_length_threshold"]:
        score += 20
        reasons.append(f"任务复杂: {msg_len}字")
        signals.append(f"length:{msg_len}")
        rule = "R5_complex"
    if duration >= cfg["duration_threshold_seconds"]:
        score += 10
        reasons.append(f"执行耗时: {duration}s")
        signals.append(f"duration:{duration}")
        if not rule:
            rule = "R5_complex"
    if score >= 30:
        importance = 3
    return score, reasons, signals, importance, rule
def _sr_rule_r6(task_success, outcome_detail, summary):
    if task_success and (len(outcome_detail) > 50 or len(summary) > 50):
        return 15, ["任务成功且有产出"], ["success_with_output"], 0, "R6_success"
    return _rule_no_hit()
def _sr_rule_r7(code_modified):
    if code_modified:
        return 30, ["代码修改"], ["code_modified"], 4, "R7_code_mod"
    return _rule_no_hit()
class _RuleAggregate(NamedTuple):
    score: int
    importance: int
    rule: str
    reasons: list[str]
    signals: list[str]
def _aggregate_rule_results(rule_results) -> _RuleAggregate:
    reasons: list[str] = []
    signals: list[str] = []
    score = 0
    rule = ""
    importance = 2
    for d, r, s, i, ru in rule_results:
        reasons.extend(r)
        signals.extend(s)
        if d > score:
            score = d
            rule = ru or rule
        elif d == score and not rule and ru:
            rule = ru
        importance = max(importance, i)
    return _RuleAggregate(score, importance, rule, reasons, signals)
def collect_tools_used(auto_ctx: dict) -> str:
    ctx = auto_ctx if isinstance(auto_ctx, dict) else {}
    declared = ctx.get("tools_used", "")
    if isinstance(declared, (str, bytes, bytearray)):
        declared_text = _ensure_str(declared).strip()
        if declared_text:
            return declared_text
    else:
        declared_names = _tool_names(declared)
        if declared_names:
            return " ".join(declared_names)
    return " ".join(_tool_names(ctx.get("tool_calls")))
def build_trigger_signals(
    *, tools_used: str, user_messages: list[str], outcome_detail: str,
    summary: str, duration: int, task_success: bool, error_count: int,
    code_modified: bool,
) -> dict[str, Any]:
    user_msg = " ".join(ensure_str_list(user_messages))
    return {
        "should_fupan": should_fupan(
            tools_used=tools_used,
            outcome_detail=outcome_detail,
            summary=summary,
            user_msg=user_msg,
            duration=duration,
            task_success=task_success,
            error_count=error_count,
            code_modified=code_modified,
        ),
        "fupan_detected": detect_fupan(
            user_msg=user_msg,
            summary=summary,
            tools_used=tools_used,
            outcome_detail=outcome_detail,
        ),
        "loop_check": close_loop_check(
            tools_used=tools_used,
            outcome_detail=outcome_detail,
        ),
    }
def should_fupan(
    tools_used: Any = "", outcome_detail: str = "", summary: str = "",
    user_msg: str = "", duration: int = _DEFAULT_DURATION,
    task_success: bool = _DEFAULT_TASK_SUCCESS,
    error_count: int = _DEFAULT_ERROR_COUNT,
    code_modified: bool = _DEFAULT_CODE_MODIFIED,
) -> dict[str, Any]:
    tools_used_text = _tool_text(tools_used)
    outcome_detail = _ensure_str(outcome_detail)
    summary = _ensure_str(summary)
    user_msg = _ensure_str(user_msg)
    task_success = as_bool(task_success, default=_DEFAULT_TASK_SUCCESS)
    code_modified = as_bool(code_modified, default=_DEFAULT_CODE_MODIFIED)
    duration = max(0, normalize_scalar(
        duration, _DEFAULT_DURATION, want_int=True))
    error_count = max(0, normalize_scalar(
        error_count, _DEFAULT_ERROR_COUNT, want_int=True))
    cfg = _load_config()
    if not cfg.get("enabled", True):
        logger.info("should_fupan 跳过: 触发器已禁用")
        return {"should": False, "score": 0, "reasons": ["触发器已禁用"],
                "importance": 1, "signals": [], "rule": "disabled"}
    blocker_result = (
        None if error_count > 0 or not task_success or code_modified
        else _sr_check_blocker(user_msg, cfg)
    )
    if blocker_result is not None:
        return blocker_result
    combined_text = f"{user_msg} {summary} {outcome_detail} {tools_used_text}"
    aggregate = _aggregate_rule_results([
        _sr_rule_r2(error_count, task_success),
        _sr_rule_r3(combined_text, cfg),
        _sr_rule_r4(tools_used, cfg),
        _sr_rule_r5(len(user_msg), duration, cfg),
        _sr_rule_r6(task_success, outcome_detail, summary),
        _sr_rule_r7(code_modified),
    ])
    threshold = cfg["score_min"]
    should = aggregate.score >= threshold
    if not should:
        aggregate.reasons.append(
            f"得分({aggregate.score})低于阈值({threshold})")
    logger.info("should_fupan 判定: should=%s score=%s rule=%s importance=%s",
                should, aggregate.score, aggregate.rule or "none",
                aggregate.importance)
    return {"should": should, "score": aggregate.score,
            "reasons": aggregate.reasons, "importance": aggregate.importance,
            "signals": aggregate.signals, "rule": aggregate.rule or "none"}
def detect_fupan(user_msg: str = "", summary: str = "",
                 tools_used: str = "", outcome_detail: str = "") -> dict[str, Any]:
    user_msg = _ensure_str(user_msg)
    summary = _ensure_str(summary)
    outcome_detail = _ensure_str(outcome_detail)
    tools_used = _tool_text(tools_used)
    combined = f"{user_msg} {summary} {outcome_detail} {tools_used}"
    review_keywords = _load_config()["review_keywords"]
    found = _keyword_hits(combined, review_keywords)
    logger.info("detect_fupan 后验检测: detected=%s keyword_count=%d",
                len(found) >= 2, len(found))
    return {"detected": len(found) >= 2, "keywords_found": found,
            "keyword_count": len(found)}

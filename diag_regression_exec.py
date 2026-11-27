from __future__ import annotations

import ast
import atexit
import hashlib
import importlib.util
import io
import json
import keyword
import logging
import math
import os
import re as _re
import subprocess
import sys
import threading
import time as _time
import tokenize
import uuid
from collections.abc import Sequence
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field
from enum import Enum
from typing import Any

from jwsgj.diag_guard_io import (
    decode_source_strict,
    guarded_open,
    two_level_rmtree,
    two_level_unlink,
)
from jwsgj.diag_types_defs import (
    ContractViolationError,
)
from jwsgj.diag_types_normalize import safe_str
from jwsgj.diag_types_vocab import (
    MSG_EXCEPTION_BROAD_HANDLER,
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_paths import (
    SOURCE_LAYOUT_ROOT_NAMES,
    detect_package_root,
    get_temp_base,
    subprocess_noartifact_env,
)

__all__ = [
    'DEFAULT_BEHAVIOR_TIMEOUT_SEC',
    'REAL_TEST_RESTORE_FAILED',
    'VERIFY_EXC',
    'BehaviorRegressionExecutor',
    'BehaviorRegressionReport',
    'EquivalenceStatus',
    'TestCase',
    'TestResult',
    'compare_outputs',
    'delete_carrier_module',
    'disk_baseline_path',
    'normalize_repr',
    'reset_state_sandbox',
    'restore_file_content',
    'run_real_tests',
    'write_carrier_module',
]
_log = logging.getLogger(__name__)
_log.addHandler(logging.NullHandler())
_log.info("diag_regression_exec 已加载: %d 项导出", len(__all__))
DEFAULT_BEHAVIOR_TIMEOUT_SEC = 5.0
# 用例子进程并发上限：用例彼此独立，串行执行白付解释器启动成本
_MAX_PARALLEL_CASES = 8
_DEFAULT_SOURCE_ROOTS = ()
_DEFAULT_SOURCE_ENCODING = "utf-8"
_DEFAULT_TEST_SEARCH_MAX_LEVELS = 5
class EquivalenceStatus(Enum):
    PASSED = "passed"
    ENHANCED = "enhanced"
    REGRESSED = "regressed"
    UNVERIFIABLE = "unverifiable"
    ERROR = "error"
@dataclass
class TestCase:
    case_id: str
    function_name: str
    inputs: tuple = ()
    kwargs: dict[str, Any] = field(default_factory=dict)
    target_kind: str = "function"
    # 目标函数是否绑定真实桌面/COM/硬件（其异常类型不可重放，
    # 见 diag_regression_guard._references_env_boundary）
    env_bound: bool = False
@dataclass
class TestResult:
    case_id: str
    function_name: str
    passed: bool
    original_output: Any = None
    fixed_output: Any = None
    original_exception: str | None = None
    fixed_exception: str | None = None
    diff_detail: str = ""
    verdict: str = ""
@dataclass
class BehaviorRegressionReport:
    status: EquivalenceStatus = EquivalenceStatus.UNVERIFIABLE
    total_tests: int = 0
    passed_tests: int = 0
    failed_tests: int = 0
    test_results: list[TestResult] = field(default_factory=list)
    api_surface_changes: list[str] = field(default_factory=list)
    requires_manual_review: bool = False
    error_detail: str = ""
    elapsed_ms: float = 0.0
    baseline_unavailable_tests: int = 0
    dangerous_content: bool = False
    restore_failed: bool = False
    # 环境绑定用例：无头环境建立不了可重放基线，不参与等价判定
    environment_excluded_cases: list[str] = field(default_factory=list)
    @property
    def is_equivalent(self) -> bool:
        return self.status in (EquivalenceStatus.PASSED,
                              EquivalenceStatus.ENHANCED)
    @property
    def pass_rate(self) -> float:
        if self.total_tests == 0:
            return 0.0
        return self.passed_tests / self.total_tests
_ADDR_RE = _re.compile(r" at 0x[0-9a-fA-F]+(?=[>;])")
_CARRIER_MODULE_PREFIX = "_jws_bequiv"
_TMP_MOD_RE = _re.compile(
    _CARRIER_MODULE_PREFIX + r"_(?:orig|fixed)_[0-9a-f]+_[0-9a-f]+_[0-9a-f]+")
def normalize_repr(val: Any) -> Any:
    if not isinstance(val, str):
        return val
    def normalize_fragment(fragment: str) -> str:
        normalized = _ADDR_RE.sub(" at 0xADDR", fragment)
        return _TMP_MOD_RE.sub(_CARRIER_MODULE_PREFIX + "_tmp", normalized)
    line_offsets = [0]
    for line in val.splitlines(keepends=True):
        line_offsets.append(line_offsets[-1] + len(line))
    literal_spans: list[tuple[int, int]] = []
    try:
        for token in tokenize.generate_tokens(io.StringIO(val).readline):
            if token.type != tokenize.STRING:
                continue
            start = line_offsets[token.start[0] - 1] + token.start[1]
            end = line_offsets[token.end[0] - 1] + token.end[1]
            literal_spans.append((start, end))
    except (tokenize.TokenError, IndentationError, SyntaxError):
        pass
    if not literal_spans:
        return normalize_fragment(val)
    parts: list[str] = []
    cursor = 0
    for start, end in literal_spans:
        parts.append(normalize_fragment(val[cursor:start]))
        # 字面量内部不归一化地址（用户字符串数据可合法含 " at 0x..."），
        # 但 repr(cls)/repr(module) 会把载体模块名放进引号内
        # （<class 'mod.Foo'>），载体名差异必须同样归一化，否则
        # orig/fixed 两次加载的不同载体名被误判为输出不一致
        parts.append(_TMP_MOD_RE.sub(
            _CARRIER_MODULE_PREFIX + "_tmp", val[start:end]))
        cursor = end
    parts.append(normalize_fragment(val[cursor:]))
    return "".join(parts)
VERIFY_EXC = (OSError, AttributeError, KeyError, TypeError, ValueError,
               RuntimeError, ContractViolationError)
_CHANNEL_EXC_PREFIXES = ("ExecutionError",)
_PROCESS_DIED_PREFIX = "ProcessDied: rc="
_INFRA_EXC_PREFIXES = ("MODULE_IMPORT_ERROR", "UNINSTANTIABLE",
                       "TARGET_BINDING_ERROR", "SKIP", "TimeoutExpired",
                       _PROCESS_DIED_PREFIX) + _CHANNEL_EXC_PREFIXES
class _TargetException(str):
    pass
def _is_infra_exc(exc: Any, prefixes: str | tuple[str, ...]) -> bool:
    if exc is None or isinstance(exc, _TargetException):
        return False
    text = str(exc)
    candidates = (prefixes,) if isinstance(prefixes, str) else prefixes
    for prefix in candidates:
        if prefix == "TimeoutExpired":
            if text == prefix:
                return True
        elif text.startswith(prefix):
            return True
    return False
def _exc_type_str(exc: Any) -> str:
    text = str(exc)
    if (not isinstance(exc, _TargetException)
            and text.startswith(_PROCESS_DIED_PREFIX)):
        return text
    return text.split(":", 1)[0]
def compare_outputs(
    orig_output: Any, orig_exc: Any, fixed_output: Any, fixed_exc: Any,
) -> tuple[str, str]:
    infra_verdict = _infra_failure_verdict(orig_exc, fixed_exc)
    if infra_verdict is not None:
        return infra_verdict
    if orig_exc is None and fixed_exc is None:
        return _both_returned_verdict(orig_output, fixed_output)
    if orig_exc is not None and fixed_exc is not None:
        return _both_raised_verdict(orig_exc, fixed_exc)
    if orig_exc is None:
        if _is_infra_exc(fixed_exc, _INFRA_EXC_PREFIXES):
            return "regressed", f"修复侧执行通道不可用: {fixed_exc}"
        return "regressed", f"原始正常返回({orig_output}),修复后抛异常({fixed_exc})"
    return "regressed", f"行为变化: 原始抛异常({orig_exc}),修复后正常返回({fixed_output})"
def _infra_failure_verdict(
    orig_exc: Any, fixed_exc: Any
) -> tuple[str, str] | None:
    if not _is_infra_exc(orig_exc, _INFRA_EXC_PREFIXES):
        return None
    if (_is_infra_exc(fixed_exc, _INFRA_EXC_PREFIXES)
            and _exc_type_str(fixed_exc) == _exc_type_str(orig_exc)):
        return ("baseline_unavailable",
                f"双侧执行通道均不可用: {str(orig_exc)[:80]}")
    return "baseline_unavailable", f"orig 侧基线不可得: {str(orig_exc)[:80]}"
def _both_returned_verdict(
    orig_output: Any, fixed_output: Any
) -> tuple[str, str]:
    if normalize_repr(orig_output) == normalize_repr(fixed_output):
        return "passed", ""
    return "regressed", f"输出不一致: 原始={orig_output}, 修复后={fixed_output}"
def _both_raised_verdict(
    orig_exc: Any, fixed_exc: Any
) -> tuple[str, str]:
    if _is_infra_exc(fixed_exc, _INFRA_EXC_PREFIXES):
        return "regressed", f"修复侧执行通道不可用: {fixed_exc}"
    orig_type = _exc_type_str(orig_exc)
    fixed_type = _exc_type_str(fixed_exc)
    if orig_type == fixed_type:
        if orig_type == "SystemExit" and str(orig_exc) != str(fixed_exc):
            return ("regressed",
                    (f"SystemExit 退出行为不一致: 原始={orig_exc}, "
                     f"修复后={fixed_exc}"))
        return "passed", ""
    return "regressed", f"异常类型不一致: 原始={orig_type}, 修复后={fixed_type}"
_NONDET_PREFIX = "非确定性输出（orig 两次执行不一致，无法建立行为基线）"
def _nondet_diff(diff: object) -> str:
    return f"{_NONDET_PREFIX}: {diff}"
def _build_test_result(
    case: Any, orig_output: Any, orig_exc: Any,
    fixed_output: Any, fixed_exc: Any, *,
    nondet: bool = False,
) -> TestResult:
    verdict, diff = compare_outputs(orig_output, orig_exc, fixed_output, fixed_exc)
    passed = verdict == "passed"
    if not passed and nondet:
        verdict = "baseline_unavailable"
        diff = _nondet_diff(diff)
        passed = False
    return TestResult(
        case_id=case.case_id,
        function_name=case.function_name,
        passed=passed,
        original_output=orig_output,
        fixed_output=fixed_output,
        original_exception=orig_exc,
        fixed_exception=fixed_exc,
        diff_detail=diff,
        verdict=verdict,
    )
def _nondet_seq(_outs: list[tuple[Any, Any]]) -> bool:
    if len(_outs) < 2:
        return False
    return any(compare_outputs(_outs[0][0], _outs[0][1], o, e)[0] == "regressed"
               for o, e in _outs[1:])
_SYMMETRIC_CHANNEL_SPECS: tuple[
    tuple[str, str | tuple[str, ...], str], ...] = (
    ("symmetric_modimport_detail", "MODULE_IMPORT_ERROR",
     ("产物模块依赖不可解析（模块级导入失败），"
      "无法验证行为等价性")),
    ("symmetric_uninst_detail", "UNINSTANTIABLE",
     ("产物类无法无参实例化（构造含必选参数），"
      "实例方法行为无法验证")),
    ("symmetric_target_binding_detail", "TARGET_BINDING_ERROR",
     ("产物中不存在用例指定目标，目标未执行，无法验证行为等价性")),
    ("symmetric_skip_detail", "SKIP",
     ("产物文件名非安全标识符（子进程执行通道拒绝），"
      "无法验证行为等价性")),
    ("symmetric_timeout_detail", "TimeoutExpired",
     ("产物子进程执行超时（验证预算内未完成），"
      "无法验证行为等价性")),
    ("symmetric_process_died_detail", _PROCESS_DIED_PREFIX,
     ("产物子进程异常退出（未返回行为协议结果），"
      "无法验证行为等价性")),
    ("symmetric_channel_detail", _CHANNEL_EXC_PREFIXES,
     ("产物子进程执行载体不可用（无法启动解释器子进程），"
      "无法验证行为等价性")),
)
_SYMMETRIC_DETAILS = {
    key: detail for key, _prefix, detail in _SYMMETRIC_CHANNEL_SPECS}
_SYMMETRIC_CHANNELS = tuple(
    (key, prefix) for key, prefix, _detail in _SYMMETRIC_CHANNEL_SPECS)
def _symmetric_pairs(
    test_results: list, details: dict[str, str],
) -> tuple[tuple[str, int], ...]:
    return tuple(
        (details[key], _symmetric_failures(test_results, prefix))
        for key, prefix in _SYMMETRIC_CHANNELS)
def _finalize_report_aggregation(
    report: BehaviorRegressionReport,
    n_cases: int,
    *,
    all_baseline_detail: str,
    symmetric_details: dict[str, str] | None = None,
) -> None:
    _baseline = _count_verdict_buckets(report)
    _symmetric = _symmetric_pairs(
        report.test_results, symmetric_details or _SYMMETRIC_DETAILS)
    _symmetric_total = sum(pairs for _detail, pairs in _symmetric)
    report.total_tests = report.passed_tests + report.failed_tests
    report.baseline_unavailable_tests = _baseline
    _decide_aggregation_status(
        report, n_cases, _baseline, _symmetric_total, _symmetric,
        all_baseline_detail)
def _no_comparable_evidence(n_cases: int, baseline: int,
                            total_tests: int) -> bool:
    return baseline == n_cases or total_tests == 0
def _all_verdicts_symmetric_infra(
    n_cases: int, symmetric_total: int,
) -> bool:
    return bool(n_cases) and symmetric_total == n_cases
def _decide_aggregation_status(
    report: BehaviorRegressionReport, n_cases: int, baseline: int,
    symmetric_total: int, symmetric: tuple, all_baseline_detail: str,
) -> None:
    if _all_verdicts_symmetric_infra(n_cases, symmetric_total):
        report.status = EquivalenceStatus.UNVERIFIABLE
        report.error_detail = _classify_symmetric_detail(symmetric, n_cases)
        report.requires_manual_review = True
    elif _no_comparable_evidence(n_cases, baseline, report.total_tests):
        report.status = EquivalenceStatus.UNVERIFIABLE
        report.error_detail = all_baseline_detail
        report.requires_manual_review = True
    elif baseline and report.failed_tests == 0:
        report.status = EquivalenceStatus.UNVERIFIABLE
        report.error_detail = (
            f"{baseline}/{n_cases} 个用例基线不可用；"
            "其余可比较用例通过，但行为等价性仅部分验证"
        )
        report.requires_manual_review = True
    elif report.failed_tests == 0:
        report.status = EquivalenceStatus.PASSED
        report.requires_manual_review = False
        report.error_detail = ""
    else:
        report.status = EquivalenceStatus.REGRESSED
        report.requires_manual_review = True
def _count_verdict_buckets(report: BehaviorRegressionReport) -> int:
    report.passed_tests = 0
    report.failed_tests = 0
    baseline = 0
    for _tr in report.test_results:
        if _tr.verdict == "baseline_unavailable":
            baseline += 1
            continue
        if _tr.passed:
            report.passed_tests += 1
        else:
            report.failed_tests += 1
    return baseline
def _symmetric_failures(test_results: list,
                        prefix: str | tuple[str, ...]) -> int:
    return sum(
        1 for _tr in test_results
        if _is_infra_exc(_tr.original_exception, prefix)
        and _is_infra_exc(_tr.fixed_exception, prefix))
def _classify_symmetric_detail(detail_pairs: tuple, total_tests: int) -> str:
    for _detail, _pairs in detail_pairs:
        if _pairs == total_tests:
            return _detail
    return "；".join(_detail for _detail, _pairs in detail_pairs if _pairs)
def _verdict_passed(orig_pair: tuple, fixed_pair: tuple) -> bool:
    return compare_outputs(orig_pair[0], orig_pair[1],
                          fixed_pair[0], fixed_pair[1])[0] == "passed"
def _divergent_indices(
    test_cases: list[TestCase], orig_results: dict, fixed_results: dict,
) -> list[int]:
    common_indices = orig_results.keys() & fixed_results.keys()
    return [i for i in range(len(test_cases))
            if i in common_indices
            and not _verdict_passed(orig_results[i], fixed_results[i])]
def _batch_key_covers(results: dict | None, n_cases: int) -> bool:
    return results is not None and all(i in results for i in range(n_cases))
_DRIFT_DIFF_TEXT = ("跨轮状态漂移（两版在同一窗口态输出一致，"
                    "差异随轮间状态推进消解）")
def _drift_detail(detail: object) -> str:
    return str(detail).replace(_NONDET_PREFIX, _DRIFT_DIFF_TEXT, 1)
def _mark_error(report: BehaviorRegressionReport, exc: Exception) -> None:
    report.status = EquivalenceStatus.ERROR
    report.error_detail = str(exc)
    report.requires_manual_review = True
    if isinstance(exc, ContractViolationError):
        report.dangerous_content = True
def _mark_restore_failed(report: BehaviorRegressionReport,
                         filepath: str) -> None:
    _detail = (f"收尾还原原始代码失败（磁盘停留修复版，"
               f"须人工恢复原始内容）: {filepath}")
    report.status = EquivalenceStatus.ERROR
    report.error_detail = (f"{report.error_detail}；{_detail}"
                           if report.error_detail else _detail)
    report.requires_manual_review = True
    report.restore_failed = True
def _reject_non_source_input(
    original_code: Any, fixed_code: Any,
) -> BehaviorRegressionReport | None:
    for _label, _value in (("original_code", original_code),
                           ("fixed_code", fixed_code)):
        if isinstance(_value, str):
            continue
        _log.warning(
            "[BehaviorRegression] %s 非源码字符串形态(%s)，"
            "无法建立行为基线，按不可验证降级",
            _label, type(_value).__name__)
        return BehaviorRegressionReport(
            status=EquivalenceStatus.UNVERIFIABLE,
            requires_manual_review=True,
            error_detail=(f"{_label} 非源码字符串形态"
                          f"({type(_value).__name__})，无法建立行为基线"),
        )
    return None
def _is_python_identifier(value: object) -> bool:
    return isinstance(value, str) and value.isidentifier()
_TOKENIZE_FAILURES = tuple(
    _exc for _exc in (
        getattr(tokenize, "TokenizeError", None),
        getattr(tokenize, "TokenError", None),
    ) if _exc is not None)
_UNTRUSTED_PARSE_FAILURES = PARSE_DEGRADE_EXC + _TOKENIZE_FAILURES
_SOURCE_READ_FAILURES = (OSError, LookupError) + PARSE_DEGRADE_EXC
_CHILD_IO_ENV = {"PYTHONIOENCODING": "utf-8"}
_CARRIER_TARGET_KINDS = (
    "method", "property", "property_setter", "property_deleter")
_TARGET_KINDS = ("function", *_CARRIER_TARGET_KINDS, "ctor")
_ACCESSOR_FUNC_ATTR_BY_TARGET_KIND = {
    "property_setter": "fset",
    "property_deleter": "fdel",
}
_CASE_MARKER = "__JWS_CASE__:"
_RESULT_MARKER = "__JWS_RESULT__:"
_PROTOCOL_ID_PLACEHOLDER = "{__JWS_PROTOCOL_ID__}"
_UNBOUND_CASE_MARKER = f"{_CASE_MARKER}{_PROTOCOL_ID_PLACEHOLDER}:"
_UNBOUND_RESULT_MARKER = f"{_RESULT_MARKER}{_PROTOCOL_ID_PLACEHOLDER}:"
_PROTOCOL_SCRIPT_BINDINGS = (
    f"_JWS_CASE_MARKER = {_UNBOUND_CASE_MARKER!r}\n"
    f"_JWS_RESULT_MARKER = {_UNBOUND_RESULT_MARKER!r}\n"
)
_SPAWN_FAILURES = (OSError, ValueError, TypeError)
def _normalize_timeout_sec(value: Any) -> float:
    if isinstance(value, bool):
        return DEFAULT_BEHAVIOR_TIMEOUT_SEC
    try:
        number = float(value)
    except (TypeError, ValueError, OverflowError) as _exc:
        log_swallowed(__name__, _exc, context='_normalize_timeout_sec:非数值')
        return DEFAULT_BEHAVIOR_TIMEOUT_SEC
    if not math.isfinite(number) or number <= 0:
        return DEFAULT_BEHAVIOR_TIMEOUT_SEC
    return number
def _normalize_pythonpath_list(raw: Any) -> list[str]:
    if raw is None:
        return []
    if isinstance(raw, str):
        raw = [raw]
    elif not isinstance(raw, (list, tuple, set, frozenset)):
        _log.warning(
            "[BehaviorRegression] extra_pythonpath 形态非法(%s)，按空处理",
            type(raw).__name__)
        return []
    items: list[str] = []
    for p in raw:
        if not isinstance(p, str) or not p:
            continue
        try:
            items.append(os.path.abspath(p))
        except (OSError, ValueError) as _e:
            log_swallowed(
                __name__, _e,
                context='_normalize_pythonpath_list:abspath')
    if isinstance(raw, (set, frozenset)):
        return sorted(items)
    return items
def _append_unique(parts: list[str], path: str) -> None:
    norm = path.replace('\\', '/')
    if norm and norm not in parts:
        parts.append(norm)
def _prepend_unique(parts: list[str], path: str) -> None:
    norm = path.replace('\\', '/')
    if not norm:
        return
    if norm in parts:
        parts.remove(norm)
    parts.insert(0, norm)
def subprocess_env(module_dir: str,
                   extra_pythonpath: Sequence[str] | None,
                   skill_parent_dir: str = "") -> dict[str, str]:
    """子进程环境单一来源：解析根（预热池与直跑子进程共用）。

    线程本地的状态沙箱变量不在此注入：Popen 的 env 在预热 worker 启动时
    即固化，若沙箱路径（含线程 id）进入 env 与池 key，主线程预热的
    worker 永远不会被工作线程取用，且每个线程各建一池直到进程退出才
    回收。沙箱改由 ``_sandbox_prelude`` 在脚本开头按用例注入。
    """
    env = subprocess_noartifact_env()
    pythonpath_parts: list[str] = []
    for p in _normalize_pythonpath_list(extra_pythonpath):
        _append_unique(pythonpath_parts, p)
    if skill_parent_dir:
        _prepend_unique(pythonpath_parts, skill_parent_dir)
    _append_unique(pythonpath_parts, module_dir)
    for path in _normalize_pythonpath_list(
            env.get("PYTHONPATH", "").split(os.pathsep)):
        _append_unique(pythonpath_parts, path)
    return {
        **env,
        **_CHILD_IO_ENV,
        "PYTHONPATH": os.pathsep.join(pythonpath_parts),
        "PYTHONHASHSEED": "0",
    }
def _invalid_case(case_id: object, detail: str) -> ValueError:
    return ValueError(f"非法测试用例: {detail} (case_id={case_id!r})")
_LITERAL_SCALAR_TYPES = frozenset({
    type(None), bool, int, float, complex, str, bytes, type(Ellipsis),
})
def _is_builtin_literal_value(value: object) -> bool:
    value_type = type(value)
    if value_type in _LITERAL_SCALAR_TYPES:
        return True
    if value_type is dict:
        return all(
            _is_builtin_literal_value(key) and _is_builtin_literal_value(item)
            for key, item in value.items())
    if value_type in (list, tuple, set):
        return all(_is_builtin_literal_value(item) for item in value)
    return False
def _literal_repr(value: object, *, case_id: str, where: str) -> str:
    try:
        literal_domain = _is_builtin_literal_value(value)
    except RecursionError as exc:
        raise _invalid_case(
            case_id, f"实参值 {where!r} 的内置字面量嵌套过深") from exc
    if not literal_domain:
        raise _invalid_case(
            case_id,
            f"实参值 {where!r} 含非内置字面量对象 "
            f"({type(value).__name__})，禁止按 repr 静默换型")
    try:
        r = "..." if value is Ellipsis else repr(value)
        ast.literal_eval(r)
    except _UNTRUSTED_PARSE_FAILURES as exc:
        raise _invalid_case(
            case_id,
            f"实参值 {where!r} 的 repr 非字面量域,"
            f"回解失败 ({type(value).__name__}: {exc})") from exc
    try:
        _has_comment = any(
            tok.type == tokenize.COMMENT
            for tok in tokenize.generate_tokens(io.StringIO(r).readline))
    except _UNTRUSTED_PARSE_FAILURES as _te:
        raise _invalid_case(
            case_id,
            f"实参值 {where!r} 的 repr 无法 tokenize"
            f"判别注释向量 ({r!r}: {_te})") from _te
    if _has_comment:
        raise _invalid_case(
            case_id,
            f"实参值 {where!r} 的 repr 含行内注释注入向量 ({r!r})")
    return r
def _require_identifier(name: str, kind: str, case_id: str) -> None:
    if not _is_python_identifier(name):
        raise _invalid_case(case_id, f"{kind} {name!r} 不是合法标识符")
def _validate_call_shape(case: TestCase) -> list[str]:
    if not isinstance(case.function_name, str):
        raise _invalid_case(
            case.case_id,
            f"function_name 须为 str, 实际 {type(case.function_name).__name__}")
    parts = case.function_name.split('.')
    _validate_identifiers(case, parts)
    _validate_target_kind(case)
    _validate_carrier_arity(case, parts)
    return parts
def _validate_identifiers(case: TestCase, parts: list[str]) -> None:
    for seg in parts:
        _require_identifier(seg, "function_name 段", case.case_id)
    if not isinstance(case.kwargs, dict):
        raise _invalid_case(
            case.case_id,
            f"kwargs 须为 dict, 实际 {type(case.kwargs).__name__}")
    for k in case.kwargs:
        _require_identifier(k, "kwargs 键", case.case_id)
        if keyword.iskeyword(k):
            raise _invalid_case(
                case.case_id,
                f"kwargs 键 {k!r} 是 Python 关键字,不可作实参名")
def _validate_target_kind(case: TestCase) -> None:
    if case.target_kind not in _TARGET_KINDS:
        raise _invalid_case(
            case.case_id,
            f"未知 target_kind={case.target_kind!r},"
            f"合法值域 {'/'.join(_TARGET_KINDS)}")
def _validate_carrier_arity(case: TestCase, parts: list[str]) -> None:
    if case.target_kind in _CARRIER_TARGET_KINDS and len(parts) != 2:
        raise _invalid_case(
            case.case_id,
            f"target_kind={case.target_kind!r} 的 function_name 须为 "
            f"'类名.成员名' 两段, 实际 {case.function_name!r} 共 {len(parts)} 段")
    if case.target_kind == "property" and (case.inputs or case.kwargs):
        raise _invalid_case(
            case.case_id,
            "target_kind='property' 不接受 inputs/kwargs；"
            "属性求值没有调用实参，禁止静默丢弃")
    if case.target_kind == "ctor":
        _validate_ctor_arity(case, parts)
def _validate_ctor_arity(case: TestCase, parts: list[str]) -> None:
    if len(parts) not in (1, 2):
        raise _invalid_case(
            case.case_id,
            f"target_kind='ctor' 的 function_name 须为 '类名' 或 "
            f"'类名.__init__', 实际 {case.function_name!r} 共 {len(parts)} 段")
    if len(parts) == 2 and parts[1] != "__init__":
        raise _invalid_case(
            case.case_id,
            f"target_kind='ctor' 的 function_name 两段形态第二段须为 "
            f"'__init__', 实际 {parts[1]!r}")
def _case_inputs(case: TestCase) -> tuple:
    raw = case.inputs
    if raw is None:
        return ()
    if isinstance(raw, (tuple, list)):
        return tuple(raw)
    raise _invalid_case(
        case.case_id,
        f"inputs 须为 tuple/list 序列, 实际 {type(raw).__name__}"
        "（str/bytes 会被逐字符拆分、dict 会被按键展开）")
def _call_expr(case: TestCase) -> tuple[str, list[str]]:
    _inputs = _case_inputs(case)
    parts = _validate_call_shape(case)
    args_repr = ", ".join(
        _literal_repr(v, case_id=case.case_id, where="inputs")
        for v in _inputs)
    kwargs_repr = ", ".join(
        f"{k}={_literal_repr(v, case_id=case.case_id, where=f'kwargs[{k}]')}"
        for k, v in case.kwargs.items())
    _call_parts = ", ".join(filter(None, (args_repr, kwargs_repr)))
    expr = f"_fn({_call_parts})" if _call_parts else "_fn()"
    return expr, parts
_INFRA_PREFIX_BY_STATUS = {
    "module_import_error": "MODULE_IMPORT_ERROR: ",
    "uninstantiable": "UNINSTANTIABLE: ",
    "target_binding_error": "TARGET_BINDING_ERROR: ",
}
def _parse_case_payload(data: dict) -> tuple[str | None, str | None]:
    status = data.get("status")
    if status == "ok":
        return data.get("value", "None"), None
    detail = (f"{_INFRA_PREFIX_BY_STATUS.get(status, '')}"
              f"{data.get('type', 'Error')}: {data.get('message', '')}")
    if status == "error":
        return None, _TargetException(detail)
    return None, detail
def _parse_payload_json(payload: str) -> dict | None:
    try:
        data = json.loads(payload)
    except _UNTRUSTED_PARSE_FAILURES as exc:
        _log.debug("JSON 解析失败（跳过污染行）: %s", exc)
        return None
    return data if isinstance(data, dict) else None
_MODULE_IMPORT_PAYLOAD = (
    '{"status": "module_import_error", "type": type(_e).__name__, '
    '"message": str(_e)}')
_UNINSTANTIABLE_PAYLOAD = (
    '{"status": "uninstantiable", "type": type(_ie).__name__, '
    '"message": str(_ie)}')
_TARGET_BINDING_PAYLOAD = (
    '{"status": "target_binding_error", "type": type(_be).__name__, '
    '"message": str(_be)}')
_ERROR_PAYLOAD = (
    '{"status": "error", "type": type(_e).__name__, '
    '"message": str(_e), "traceback": _tb.format_exc()}')
_SYSTEM_EXIT_PAYLOAD = (
    '{"status": "error", "type": "SystemExit", '
    '"message": repr(_e.code), "traceback": _tb.format_exc()}')
_OK_PAYLOAD = '{"status": "ok", "value": %s}'
_CTOR_STATE_REPR = (
    "def _jws_ctor_state_repr(value):\n"
    "    dict_state = getattr(value, '__dict__', None)\n"
    "    slot_state = []\n"
    "    for cls in type(value).__mro__:\n"
    "        names = cls.__dict__.get('__slots__', ())\n"
    "        if isinstance(names, str):\n"
    "            names = (names,)\n"
    "        for name in names:\n"
    "            if name in ('__dict__', '__weakref__'):\n"
    "                continue\n"
    "            attr_name = name\n"
    "            if name.startswith('__') and not name.endswith('__'):\n"
    "                attr_name = '_' + cls.__name__.lstrip('_') + name\n"
    "            try:\n"
    "                slot_value = getattr(value, attr_name)\n"
    "            except AttributeError:\n"
    "                slot_value = '<UNSET>'\n"
    "            slot_state.append((cls.__name__, name, slot_value))\n"
    "    if slot_state:\n"
    "        return repr((dict_state, slot_state))\n"
    "    if dict_state is not None:\n"
    "        return repr(dict_state)\n"
    "    return repr(value)\n\n"
)
_ASYNC_RESULT_SETTLE = (
    "async def _jws_settle_async_result(value):\n"
    "    if _insp.isawaitable(value):\n"
    "        value = await value\n"
    "    if isinstance(value, _abc.AsyncIterator):\n"
    "        value = [item async for item in value]\n"
    "    return value\n\n"
)
_BINDING_SUPPORT = (
    "class _JwsTargetBindingError(Exception):\n"
    "    pass\n"
    "def _jws_bind(obj, name):\n"
    "    try:\n"
    "        return getattr(obj, name)\n"
    "    except AttributeError:\n"
    "        try:\n"
    "            _insp.getattr_static(obj, name)\n"
    "        except AttributeError as _be:\n"
    "            raise _JwsTargetBindingError(name) from _be\n"
    "        raise\n\n"
    "def _jws_accessor(cls, obj, name, accessor_name):\n"
    "    descriptor = _jws_bind(cls, name)\n"
    "    func = getattr(descriptor, accessor_name, None)\n"
    "    if func is None:\n"
    "        raise _JwsTargetBindingError(name + '.' + accessor_name)\n"
    "    return func.__get__(obj, cls)\n\n"
)
_BATCH_PROLOGUE = (
    "import sys as _sys, json as _json, traceback as _tb, inspect as _insp\n"
    "import asyncio as _aio, collections.abc as _abc\n"
    + _PROTOCOL_SCRIPT_BINDINGS
    + _CTOR_STATE_REPR
    + _ASYNC_RESULT_SETTLE
    + _BINDING_SUPPORT
    + '_MODNAME = "{MODULE_NAME}"\n\n'
    "def _emit(_idx, _payload):\n"
    "    print()\n"
    "    print(_JWS_CASE_MARKER + str(_idx) + _JWS_RESULT_MARKER + _payload)\n\n"
)
def _emit_batch(idx: int):
    def emit(payload: str, indent: str) -> str:
        return f'{indent}_emit({idx}, _json.dumps({payload}))\n'
    return emit
def _emit_single(payload: str, indent: str) -> str:
    return (f'{indent}print()\n'
            f'{indent}print(_JWS_RESULT_MARKER + _json.dumps({payload}))\n')
_SINGLE_PROLOGUE = (
    "\nimport json as _json, traceback as _tb, inspect as _insp\n"
    "import asyncio as _aio, collections.abc as _abc\n"
    + _PROTOCOL_SCRIPT_BINDINGS
    + _CTOR_STATE_REPR
    + _ASYNC_RESULT_SETTLE
    + _BINDING_SUPPORT
    + "try:\n"
    "    import importlib as _imp\n"
    '    _m = _imp.import_module("{MODULE_NAME}")\n'
    "except Exception as _e:\n"
    + _emit_single(_MODULE_IMPORT_PAYLOAD, "    ")
    + "else:\n"
)
def _await_settle(indent: str) -> list[str]:
    return [
        (f"{indent}if _insp.isawaitable(result) "
         "or isinstance(result, _abc.AsyncIterator):"),
        f"{indent}    result = _aio.run(_jws_settle_async_result(result))",
        f"{indent}if isinstance(result, _abc.Iterator):",
        f"{indent}    result = list(result)",
    ]
def _render_body(case: TestCase, parts: list[str], call_expr: str, emit) -> str:
    if case.target_kind in _CARRIER_TARGET_KINDS:
        return _render_carrier_body(case, parts, call_expr, emit)
    return _render_direct_body(case, parts, call_expr, emit)
def _render_direct_body(case: TestCase, parts: list[str],
                        call_expr: str, emit) -> str:
    if case.target_kind == "ctor":
        bindings = [f"        _fn = _jws_bind(_m, {parts[0]!r})"]
        value_expr = '_jws_ctor_state_repr(result)'
    else:
        bindings = ["        _fn = _m",
                    f"        for _part in {parts!r}:",
                    "            _fn = _jws_bind(_fn, _part)"]
        value_expr = "repr(result)"
    lines = ["    try:", *bindings, f"        result = {call_expr}"]
    if case.target_kind != "ctor":
        lines += _await_settle("        ")
    lines += [emit(_OK_PAYLOAD % value_expr, "        ").rstrip("\n"),
              "    except _JwsTargetBindingError as _be:",
              emit(_TARGET_BINDING_PAYLOAD, "        ").rstrip("\n"),
              "    except SystemExit as _e:",
              emit(_SYSTEM_EXIT_PAYLOAD, "        ").rstrip("\n"),
              "    except Exception as _e:",
              emit(_ERROR_PAYLOAD, "        ").rstrip("\n")]
    return "\n".join(lines) + "\n"
def _render_carrier_body(case: TestCase, parts: list[str],
                         call_expr: str, emit) -> str:
    bindings = [f"        _cls = _jws_bind(_m, {parts[0]!r})",
                "        _obj = _cls()"]
    member_bind = []
    value_expr = "repr(result)"
    if case.target_kind == "method":
        member_bind.append(f"            _fn = _jws_bind(_obj, {parts[-1]!r})")
        expression = call_expr
    elif case.target_kind in _ACCESSOR_FUNC_ATTR_BY_TARGET_KIND:
        accessor_attr = _ACCESSOR_FUNC_ATTR_BY_TARGET_KIND[case.target_kind]
        member_bind.append(
            f"            _fn = _jws_accessor(_cls, _obj, {parts[-1]!r}, "
            f"{accessor_attr!r})")
        expression = call_expr
        value_expr = "_jws_ctor_state_repr(_obj)"
    else:
        expression = f"_jws_bind(_obj, {parts[-1]!r})"
    lines = ["    try:", *bindings,
             "    except _JwsTargetBindingError as _be:",
             emit(_TARGET_BINDING_PAYLOAD, "        ").rstrip("\n"),
             "    except Exception as _ie:",
             emit(_UNINSTANTIABLE_PAYLOAD, "        ").rstrip("\n"),
             "    else:", "        try:", *member_bind,
             f"            result = {expression}"]
    lines += _await_settle("            ")
    lines += [emit(_OK_PAYLOAD % value_expr, "            ").rstrip("\n"),
              "        except _JwsTargetBindingError as _be:",
              emit(_TARGET_BINDING_PAYLOAD, "            ").rstrip("\n"),
              "        except SystemExit as _e:",
              emit(_SYSTEM_EXIT_PAYLOAD, "            ").rstrip("\n"),
              "        except Exception as _e:",
              emit(_ERROR_PAYLOAD, "            ").rstrip("\n")]
    return "\n".join(lines) + "\n"
def _batch_case_block(idx: int, case: TestCase) -> str:
    emit = _emit_batch(idx)
    head = (
        "try:\n"
        "    _sys.modules.pop(_MODNAME, None)\n"
        "    import importlib as _imp\n"
        "    _m = _imp.import_module(_MODNAME)\n"
        "except Exception as _e:\n"
        + emit(_MODULE_IMPORT_PAYLOAD, "    ")
        + "else:\n"
    )
    call_expr, parts = _call_expr(case)
    return head + _render_body(case, parts, call_expr, emit)
def generate_batch_script(cases: list[TestCase]) -> str:
    return _BATCH_PROLOGUE + "".join(
        _batch_case_block(idx, case) for idx, case in enumerate(cases))
def generate_test_script(case: TestCase) -> str:
    call_expr, parts = _call_expr(case)
    return _SINGLE_PROLOGUE + _render_body(case, parts, call_expr, _emit_single)
def _path_within_root(path: str, root: str) -> bool:
    path_key = os.path.normcase(os.path.abspath(path))
    root_key = os.path.normcase(os.path.abspath(root))
    try:
        return os.path.commonpath((path_key, root_key)) == root_key
    except ValueError:
        return False
def _dedup_absolute_paths(paths) -> list[str]:
    result: list[str] = []
    seen: set[str] = set()
    for path in paths:
        if not isinstance(path, str) or not path:
            continue
        absolute = os.path.abspath(path)
        key = os.path.normcase(absolute)
        if key not in seen:
            seen.add(key)
            result.append(absolute)
    return result
_LAYOUT_ROOT_NAMES_LOWER = frozenset(
    os.path.normcase(name) for name in SOURCE_LAYOUT_ROOT_NAMES)
def _conventional_layout_root(module_path: str) -> str:
    current = os.path.dirname(os.path.abspath(module_path))
    while True:
        if os.path.normcase(os.path.basename(current)) in _LAYOUT_ROOT_NAMES_LOWER:
            return current
        parent = os.path.dirname(current)
        if parent == current:
            return ""
        current = parent
def _module_source_roots(module_path: str, project_root: str,
                         source_roots) -> list[str]:
    candidates: list[str] = []
    if project_root:
        root = os.path.abspath(project_root)
        candidates.append(root)
        candidates.extend(os.path.join(root, name)
                          for name in SOURCE_LAYOUT_ROOT_NAMES)
    conventional_root = _conventional_layout_root(module_path)
    if conventional_root:
        candidates.append(conventional_root)
    candidates.extend(_normalize_pythonpath_list(source_roots))
    return _dedup_absolute_paths(candidates)
def _module_name_from_root(module_path: str, source_root: str) -> str:
    if not _path_within_root(module_path, source_root):
        return ""
    try:
        relative = os.path.relpath(module_path, source_root)
    except (OSError, ValueError) as exc:
        log_swallowed(__name__, exc, context='_module_name_from_root')
        return ""
    parts = [part for part in relative.replace(os.sep, '/').split('/')
             if part and part != '.']
    if not parts:
        return ""
    parts[-1] = os.path.splitext(parts[-1])[0]
    if parts[-1] == '__init__':
        parts = parts[:-1]
    if not parts or not all(_is_python_identifier(part) for part in parts):
        return ""
    return '.'.join(parts)
def _resolve_module(module_path: str, project_root: str = "",
                    source_roots=_DEFAULT_SOURCE_ROOTS) -> tuple[str, str] | None:
    abs_path = os.path.abspath(module_path)
    matches = []
    for source_root in _module_source_roots(
            abs_path, project_root, source_roots):
        module_name = _module_name_from_root(abs_path, source_root)
        if module_name:
            matches.append((source_root, module_name))
    if matches:
        source_root, module_name = max(
            enumerate(matches),
            key=lambda item: (len(os.path.normcase(item[1][0])), item[0]),
        )[1]
        return source_root.replace('\\', '/'), module_name
    package_root = detect_package_root(abs_path)
    module_name = _module_name_from_root(abs_path, package_root)
    if not module_name:
        return None
    return package_root.replace('\\', '/'), module_name
def _prepare_child_script(script: str, module_path: str,
                          action: str,
                          source_roots=_DEFAULT_SOURCE_ROOTS) -> tuple[str, str] | None:
    resolved = _resolve_module(module_path, "", source_roots)
    if resolved is None:
        _log.warning(
            "[BehaviorRegression] 模块名非安全标识符，%s跳过: %r",
            action, os.path.splitext(os.path.basename(module_path))[0])
        return None
    module_dir, module_name = resolved
    return script.replace("{MODULE_NAME}", module_name, 1), module_dir
def _bind_child_protocol(
    script: str, protocol_id: str | None = None,
) -> tuple[str, str, str] | None:
    token = protocol_id or uuid.uuid4().hex
    case_marker = f"{_CASE_MARKER}{token}:"
    result_marker = f"{_RESULT_MARKER}{token}:"
    bindings = (
        ("_JWS_CASE_MARKER", _UNBOUND_CASE_MARKER, case_marker),
        ("_JWS_RESULT_MARKER", _UNBOUND_RESULT_MARKER, result_marker),
    )
    for name, unbound, bound in bindings:
        old = f"{name} = {unbound!r}"
        if script.count(old) != 1:
            _log.warning("[BehaviorRegression] 子进程协议绑定缺失或重复: %s", name)
            return None
        script = script.replace(old, f"{name} = {bound!r}", 1)
    return script, case_marker, result_marker
_SANDBOX_PATHS_SEEN: set[str] = set()
_SANDBOX_ATEXIT_REGISTERED = False
def _cleanup_sandboxes_at_exit(paths: set[str]) -> None:
    for _p in list(paths):
        try:
            two_level_rmtree(_p)
        except Exception:  # noqa: BLE001
            _log.debug("[sandbox] atexit 兜底清理单条失败（继续其余路径）: %s",
                       _p, exc_info=True)
            continue
def state_sandbox_root() -> str:
    return os.path.join(
        get_temp_base(), f"jwsgj_br_sandbox_{os.getpid()}_t{threading.get_ident()}")
def reset_state_sandbox() -> dict[str, str]:
    sandbox_root = state_sandbox_root()
    if not two_level_rmtree(sandbox_root) and os.path.lexists(sandbox_root):
        _log.warning("[sandbox] 沙箱目录清理失败（残留可能污染下次执行）: %s",
                     sandbox_root)
        raise OSError(f"沙箱目录清理失败，拒绝复用受污染状态: {sandbox_root}")
    os.makedirs(sandbox_root, exist_ok=True)
    global _SANDBOX_ATEXIT_REGISTERED
    _SANDBOX_PATHS_SEEN.add(sandbox_root)
    if not _SANDBOX_ATEXIT_REGISTERED:
        _SANDBOX_ATEXIT_REGISTERED = True
        atexit.register(_cleanup_sandboxes_at_exit, _SANDBOX_PATHS_SEEN)
    return {
        "JWSGJ_TEMP_ROOT": sandbox_root,
        "WORKSPACE_DIR": sandbox_root,
    }
def _sandbox_pycache_prefix(sandbox_env: dict[str, str]) -> str:
    return os.path.join(sandbox_env["JWSGJ_TEMP_ROOT"], "pycache")
_UTF8_COOKIE_NAMES = frozenset({
    'utf-8', 'utf8', 'utf-8-sig', 'utf8-sig', 'cp65001',
})
_CODING_COOKIE_DECL_RE = _re.compile(r"(?i)(coding[:=][ \t]*)([-\w.]+)")
def _declared_source_encoding(code: str) -> str:
    try:
        encoded = code.encode('utf-8', 'surrogatepass')
        encoding = tokenize.detect_encoding(io.BytesIO(encoded).readline)[0]
    except _UNTRUSTED_PARSE_FAILURES + (LookupError,) as _e:
        log_swallowed(__name__, _e, context='_declared_source_encoding')
        return ''
    return encoding or ''
def _cookie_candidate_lines(lines: list[str]):
    if not lines:
        return
    yield 0
    first = lines[0].strip()
    if len(lines) > 1 and (not first or first.startswith('#')):
        yield 1
def _rewrite_cookie_to_utf8(code: str, encoding: str) -> str:
    lines = code.splitlines(keepends=True)
    for index in _cookie_candidate_lines(lines):
        rewritten, count = _CODING_COOKIE_DECL_RE.subn(
            r"\1utf-8", lines[index], count=1)
        if count:
            lines[index] = rewritten
            _log.info(
                "[BehaviorRegression] 载体编码声明 %s 与内容不兼容，"
                "改写为 utf-8", encoding)
            break
    return "".join(lines)
def _carrier_payload(code: str) -> tuple[str, str]:
    text = code.removeprefix('\ufeff')
    encoding = _declared_source_encoding(code)
    if encoding and 'sig' in encoding.lower():
        return text, encoding
    if not encoding or encoding.lower().replace('_', '-') in _UTF8_COOKIE_NAMES:
        return text, 'utf-8'
    try:
        text.encode(encoding)
    except (UnicodeEncodeError, LookupError) as _e:
        log_swallowed(__name__, _e, context='_carrier_payload:编码不兼容')
        return _rewrite_cookie_to_utf8(text, encoding), 'utf-8'
    return text, encoding
def _write_variant_content(filepath: str, code: str) -> None:
    text, encoding = _carrier_payload(code)
    with guarded_open(filepath, 'w', encoding=encoding, newline='') as f:
        f.write(text)
def write_carrier_module(code: str, prefix: str) -> str:
    text, encoding = _carrier_payload(code)
    code_hash = hashlib.sha256(text.encode(encoding)).hexdigest()[:8]
    uniq = f"{os.getpid():x}_{os.urandom(4).hex()}"
    path = os.path.join(get_temp_base(os.path.dirname(__file__)),
                        "behavior_regression",
                        f"{_CARRIER_MODULE_PREFIX}_{prefix}_{code_hash}_{uniq}.py")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with guarded_open(path, 'w', encoding=encoding, newline='') as f:
        f.write(text)
    return path
def delete_carrier_module(path: str | None) -> None:
    if path and os.path.exists(path) and not two_level_unlink(path):
        _log.warning("[BehaviorRegression] 临时模块清理失败: %s", path)
_WARM_PRELUDE = (
    "import sys as _s\n"
    "import json, traceback, inspect, asyncio, collections.abc\n"
    "_s.stdin.reconfigure(encoding='utf-8', errors='replace')\n"
    "exec(compile(_s.stdin.read(), '<behavior-case>', 'exec'))\n"
)
_WARM_POOL_IDLE = 4
class _WarmChildPool:
    """预热的空解释器池；每个 worker 只服务一个用例（进程隔离不妥协）。

    预热 worker 启动后立即完成前导 stdlib 导入，然后阻塞在 stdin 读取上；
    用例到达时把脚本写入 stdin，worker 执行完即退出，同时补一个新 worker
    让下一次启动开销与本用例并行。CPU 总量不变，关键路径上只剩用例体。
    """
    def __init__(self, module_dir: str, env: dict[str, str]) -> None:
        self._cwd = module_dir or None
        self._env = env
        self._idle: list[subprocess.Popen] = []
        self._lock = threading.Lock()
        self._closed = False
    def _spawn(self) -> subprocess.Popen:
        return subprocess.Popen(
            [sys.executable, "-c", _WARM_PRELUDE],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True, encoding="utf-8",
            errors="replace", cwd=self._cwd, env=self._env)
    def _top_up_locked(self, count: int = 1) -> None:
        """补位：每次只补 ``count`` 个，避免把多次启动开销压到一个用例上。"""
        for _ in range(count):
            if self._closed or len(self._idle) >= _WARM_POOL_IDLE:
                return
            try:
                self._idle.append(self._spawn())
            except OSError:
                return
    def warm(self, count: int = _WARM_POOL_IDLE) -> None:
        """预启动空解释器（批次开始前调用，摊掉首批用例的启动成本）。"""
        with self._lock:
            self._top_up_locked(count)
    def run(self, script: str,
            timeout_sec: float) -> subprocess.CompletedProcess:
        with self._lock:
            worker = self._idle.pop() if self._idle else None
        if worker is None:
            worker = self._spawn()
        with self._lock:
            self._top_up_locked()
        try:
            out, err = worker.communicate(script, timeout=timeout_sec)
        except subprocess.TimeoutExpired:
            worker.kill()
            try:
                worker.communicate(timeout=5)
            except (subprocess.TimeoutExpired, OSError, ValueError):
                pass
            raise
        finally:
            if worker.poll() is None:
                worker.kill()
        return subprocess.CompletedProcess(
            worker.args, worker.returncode, out, err)
    def close(self) -> None:
        with self._lock:
            self._closed = True
            idle, self._idle = self._idle, []
        for worker in idle:
            try:
                worker.kill()
                worker.communicate(timeout=5)
            except (subprocess.TimeoutExpired, OSError, ValueError):
                pass
_WARM_POOLS: dict[tuple, _WarmChildPool] = {}
_WARM_POOLS_LOCK = threading.Lock()
def _warm_pool_for(module_dir: str,
                   env: dict[str, str]) -> _WarmChildPool:
    key = (os.path.normcase(os.path.abspath(module_dir or "")),
           env.get("PYTHONPATH", ""), env.get("PYTHONPYCACHEPREFIX", ""))
    with _WARM_POOLS_LOCK:
        pool = _WARM_POOLS.get(key)
        if pool is None:
            pool = _WarmChildPool(module_dir, env)
            _WARM_POOLS[key] = pool
        return pool
def _close_warm_pools() -> None:
    with _WARM_POOLS_LOCK:
        pools = list(_WARM_POOLS.values())
        _WARM_POOLS.clear()
    for pool in pools:
        pool.close()
atexit.register(_close_warm_pools)
_SANDBOX_PRELUDE = (
    "import os as _jws_os, sys as _jws_sys\n"
    "_jws_os.environ['JWSGJ_TEMP_ROOT'] = {root!r}\n"
    "_jws_os.environ['WORKSPACE_DIR'] = {root!r}\n"
    "_jws_os.environ['PYTHONPYCACHEPREFIX'] = {pycache!r}\n"
    "_jws_sys.pycache_prefix = {pycache!r}\n"
)
def _sandbox_prelude() -> str:
    """重置本线程状态沙箱并生成注入该沙箱的脚本前导。"""
    sandbox_env = reset_state_sandbox()
    return _SANDBOX_PRELUDE.format(
        root=sandbox_env["JWSGJ_TEMP_ROOT"],
        pycache=_sandbox_pycache_prefix(sandbox_env))
def prewarm_case_workers(module_dir: str,
                         extra_pythonpath: Sequence[str] | None,
                         skill_parent_dir: str,
                         count: int = _WARM_POOL_IDLE) -> None:
    """批次开始前预启动空解释器，把首批用例的启动成本提前摊掉。"""
    _warm_pool_for(
        module_dir, subprocess_env(module_dir, extra_pythonpath,
                                   skill_parent_dir)).warm(count)
def _run_child(script: str, module_dir: str, *, timeout_sec: float,
               extra_pythonpath: Sequence[str] | None,
               skill_parent_dir: str) -> subprocess.CompletedProcess:
    """在独立子进程中执行脚本（经预热池，每用例独占解释器）。

    脚本经 **stdin** 传输而非命令行：Windows CreateProcess 命令行硬上限
    32767 字符，多用例批量脚本（实测 200 用例 = 240042 字符）会被内核以
    ``WinError 206`` 拒绝启动；stdin 无长度限制，且仍以 ``-c`` 执行，
    保持 ``sys.path[0] == ''``（即 cwd）语义与原先一致。
    """
    return _warm_pool_for(
        module_dir, subprocess_env(module_dir, extra_pythonpath,
                                   skill_parent_dir)).run(
        _sandbox_prelude() + script, timeout_sec)
def _iter_protocol_payloads(stdout: str, marker: str):
    for raw_line in stdout.split("\n"):
        line = raw_line.removesuffix("\r")
        if line.startswith(marker):
            yield line[len(marker):]
def _parse_batch_lines(
    stdout: str, n_cases: int, case_marker: str, result_marker: str,
) -> dict[int, tuple[str | None, str | None]]:
    results: dict[int, tuple[str | None, str | None]] = {}
    for blob in _iter_protocol_payloads(stdout, case_marker):
        try:
            idx_str, payload = blob.split(result_marker, 1)
            idx = int(idx_str)
        except ValueError as e:
            _log.debug("协议行索引解析失败（跳过）: %s", e)
            continue
        data = _parse_payload_json(payload)
        if data is None or not 0 <= idx < n_cases:
            continue
        results[idx] = _parse_case_payload(data)
    return results
def _parse_single_stdout(
    stdout: str, result_marker: str,
) -> tuple[str | None, str | None] | None:
    parsed: tuple[str | None, str | None] | None = None
    for payload in _iter_protocol_payloads(stdout, result_marker):
        data = _parse_payload_json(payload)
        if data is None:
            continue
        parsed = _parse_case_payload(data)
    return parsed
def execute_batch(
    script: str, module_path: str, n_cases: int,
    timeout_sec: float, extra_pythonpath: Sequence[str] | None,
    skill_parent_dir: str = "",
) -> dict[int, tuple[str | None, str | None]] | None:
    resolution_roots = _normalize_pythonpath_list(extra_pythonpath)
    if skill_parent_dir:
        resolution_roots.append(skill_parent_dir)
    prepared = _prepare_child_script(
        script, module_path, "批量执行", source_roots=resolution_roots)
    if prepared is None:
        return None
    script, module_dir = prepared
    bound = _bind_child_protocol(script)
    if bound is None:
        return None
    script, case_marker, result_marker = bound
    per_case_timeout = _normalize_timeout_sec(timeout_sec)
    try:
        result = _run_child(
            script, module_dir,
            timeout_sec=per_case_timeout * max(1, n_cases) + 5.0,
            extra_pythonpath=extra_pythonpath,
            skill_parent_dir=skill_parent_dir)
    except subprocess.TimeoutExpired as exc:
        _log.debug("suppressed subprocess.TimeoutExpired (batch): %s", exc)
        return None
    except _SPAWN_FAILURES:
        _log.warning(
            "[BehaviorRegression] 批量执行子进程启动失败(module=%s): %s",
            os.path.basename(module_path), MSG_EXCEPTION_BROAD_HANDLER,
            exc_info=True)
        return None
    return _parse_batch_lines(result.stdout, n_cases, case_marker, result_marker)
def execute_test(script: str, module_path: str, skill_parent_dir: str = "",
                 timeout_sec: float = DEFAULT_BEHAVIOR_TIMEOUT_SEC,
                 extra_pythonpath: Sequence[str] | None = None,
                 ) -> tuple[str | None, str | None]:
    resolution_roots = _normalize_pythonpath_list(extra_pythonpath)
    if skill_parent_dir:
        resolution_roots.append(skill_parent_dir)
    prepared = _prepare_child_script(
        script, module_path, "执行", source_roots=resolution_roots)
    if prepared is None:
        module_name = os.path.splitext(os.path.basename(module_path))[0]
        return None, f"SKIP: module name is not a safe identifier: {module_name!r}"
    script, module_dir = prepared
    bound = _bind_child_protocol(script)
    if bound is None:
        return None, "ExecutionError: child script lacks authenticated protocol"
    script, _case_marker, result_marker = bound
    per_case_timeout = _normalize_timeout_sec(timeout_sec)
    for _ in range(2):
        try:
            result = _run_child(
                script, module_dir, timeout_sec=per_case_timeout,
                extra_pythonpath=extra_pythonpath,
                skill_parent_dir=skill_parent_dir)
        except subprocess.TimeoutExpired as exc:
            _log.debug("suppressed subprocess.TimeoutExpired: %s", exc)
            continue
        except _SPAWN_FAILURES as exc:
            _log.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
            return None, f"ExecutionError: {exc}"
        parsed = _parse_single_stdout(result.stdout, result_marker)
        if parsed is not None:
            return parsed
        if result.returncode != 0:
            detail = result.stderr.strip()[:500]
            suffix = f"; stderr={detail}" if detail else ""
            return None, f"{_PROCESS_DIED_PREFIX}{result.returncode}{suffix}"
        if result.stderr:
            return None, (
                "ExecutionError: child produced no protocol result: "
                f"{result.stderr.strip()[:500]}")
        return None, f"{_PROCESS_DIED_PREFIX}0"
    return None, "TimeoutExpired"
@dataclass(frozen=True)
class _RunConfig:
    timeout_sec: float
    extra_pythonpath: tuple[str, ...]
def _case_parallelism(n_cases: int) -> int:
    """用例并发度：受 CPU 核数与本机负载上限约束，至少 1。"""
    return max(1, min(_MAX_PARALLEL_CASES, os.cpu_count() or 1, n_cases))
def _execute_case(case: TestCase, module_path: str, skill_parent: str,
                  config: _RunConfig) -> tuple:
    script = generate_test_script(case)
    return execute_test(
        script, module_path, skill_parent_dir=skill_parent,
        timeout_sec=config.timeout_sec,
        extra_pythonpath=config.extra_pythonpath)
def _probe_nondet_replay(
    test_cases: list[TestCase], indices: list[int],
    first_pairs: list[tuple] | dict[int, tuple], module_path: str,
    skill_parent: str,
    config: _RunConfig, first_replay: dict[int, tuple] | None = None,
) -> set[int]:
    nondet: set[int] = set()
    for idx in indices:
        observations = [first_pairs[idx]]
        for round_idx in (0, 1):
            pair = _execute_case(test_cases[idx], module_path,
                                 skill_parent, config)
            observations.append(pair)
            if first_replay is not None and round_idx == 0:
                first_replay[idx] = pair
        if _nondet_seq(observations):
            nondet.add(idx)
    return nondet
def _probe_observations(index: int, orig_results: dict,
                        runs: list[dict]) -> list:
    outs = [(orig_results[index][0], orig_results[index][1])]
    outs.extend((run[index][0], run[index][1])
                for run in runs if index in run)
    return outs
@dataclass
class _BatchRun:
    original_code: str
    test_cases: list[TestCase]
    batch_script: str
    fixed_results: dict | None = None
    orig_results: dict | None = None
    orig_path: str | None = None
    fixed_path: str | None = None
    nondet_idx: set[int] = field(default_factory=set)
@dataclass
class _WindowDriftProbe:
    filepath: str
    fixed_code: str
    backup: str
    encoding: str
    skill_parent: str
    test_cases: list[TestCase]
    candidates: list[int]
    window_orig: dict[int, tuple]
    orig_results: list[tuple]
    fixed_results: list[tuple]
    nondet_idx: set[int]
def _read_source_keep_newlines(filepath: str) -> tuple[str, str]:
    with open(filepath, 'rb') as _bf:
        raw = _bf.read()
    return decode_source_strict(raw)
def restore_file_content(filepath: str, content: str,
                         encoding: str = _DEFAULT_SOURCE_ENCODING) -> bool:
    try:
        expected = content.encode(encoding)
        with open(filepath, 'rb') as _f:
            if _f.read() == expected:
                return True
    except _SOURCE_READ_FAILURES as _e:
        log_swallowed(__name__, _e,
                      context=f'restore_file_content:{type(_e).__name__}')
    for _attempt in (0, 1):
        try:
            expected = content.encode(encoding)
            with open(filepath, 'w', encoding=encoding, newline='') as _f:
                _f.write(content)
            with open(filepath, 'rb') as _f:
                if _f.read() == expected:
                    return True
            _log.error("CRITICAL: 还原原始文件读回不一致(第 %d 次): %s",
                       _attempt + 1, filepath)
        except _SOURCE_READ_FAILURES as _e:
            _log.error("CRITICAL: 还原原始文件失败(第 %d 次) %s: %s",
                       _attempt + 1, filepath, _e, exc_info=True)
    return False
_REAL_TEST_TIMEOUT_SEC = 30.0
_TEST_DIR_NAMES = ("tests", "test")
_TEST_FILE_TEMPLATES = ("test_{stem}.py", "{stem}_test.py")
def _pytest_available() -> bool:
    try:
        return importlib.util.find_spec("pytest") is not None
    except (ImportError, ValueError, OSError):
        _log.warning(
            "[BehaviorRegression] pytest 可用性探测异常，按不可用降级"
            "(交合成通道兜底)", exc_info=True)
        return False
def _find_test_candidates(
    start_dir: str, stem: str, max_levels: int = _DEFAULT_TEST_SEARCH_MAX_LEVELS,
    project_root: str = "",
) -> list[str] | None:
    search_dir = os.path.abspath(start_dir)
    boundary = os.path.abspath(project_root) if project_root else search_dir
    if not _path_within_root(search_dir, boundary):
        return None
    for _ in range(max_levels):
        candidates = _direct_test_candidates(search_dir, stem)
        if candidates:
            return candidates
        for dir_name in _TEST_DIR_NAMES:
            test_dir = os.path.join(search_dir, dir_name)
            if not os.path.isdir(test_dir):
                continue
            candidates = _select_test_candidates(test_dir, stem)
            if candidates:
                return candidates
        if os.path.normcase(search_dir) == os.path.normcase(boundary):
            return None
        parent = os.path.dirname(search_dir)
        if parent == search_dir or not _path_within_root(parent, boundary):
            return None
        search_dir = parent
    return None
def _direct_test_files(test_dir: str, stem: str) -> list[str]:
    return [os.path.join(test_dir, template.format(stem=stem))
            for template in _TEST_FILE_TEMPLATES]
def _direct_test_candidates(test_dir: str, stem: str) -> list[str] | None:
    candidates = [direct for direct in _direct_test_files(test_dir, stem)
                  if os.path.isfile(direct)]
    return candidates or None
def _test_name_matches_stem(name: str, stem: str) -> bool:
    if not stem or not (name.startswith("test_") and name.endswith(".py")):
        return False
    core = name[len("test_"):-len(".py")]
    return core == stem or core.startswith(f"{stem}_")
def _select_test_candidates(test_dir: str, stem: str) -> list[str] | None:
    exact = _direct_test_candidates(test_dir, stem)
    if exact:
        return exact
    try:
        entries = os.listdir(test_dir)
    except OSError as e:
        _log.warning("[BehaviorRegression] 测试目录读取失败: %s: %s", test_dir, e)
        return None
    matched: list[str] = []
    for name in sorted(entries):
        if not _test_name_matches_stem(name, stem):
            continue
        candidate = os.path.join(test_dir, name)
        if os.path.isfile(candidate):
            matched.append(candidate)
    return matched or None
def _default_project_root(import_root: str) -> str:
    if os.path.normcase(os.path.basename(import_root)) in _LAYOUT_ROOT_NAMES_LOWER:
        return os.path.dirname(import_root)
    return import_root
def _locate_real_test_files(
    filepath: str, project_root: str, source_roots, max_levels: int,
) -> tuple[list[str], str, str] | None:
    stem = os.path.splitext(os.path.basename(filepath))[0]
    if stem == '__init__':
        stem = os.path.basename(os.path.dirname(os.path.abspath(filepath)))
    resolved = _resolve_module(
        filepath, project_root=project_root, source_roots=source_roots)
    if resolved is None:
        return None
    import_root, _module_name = resolved
    boundary = (os.path.abspath(project_root) if project_root
                else _default_project_root(import_root))
    if not _path_within_root(filepath, boundary):
        return None
    candidates = _find_test_candidates(
        os.path.dirname(os.path.abspath(filepath)), stem,
        max_levels=max_levels, project_root=boundary)
    if not candidates:
        return None
    if not _pytest_available():
        _log.warning(
            "[BehaviorRegression] 宿主环境 pytest 不可导入，真实测试"
            "通道不可用，降级交合成通道兜底: %s", filepath)
        return None
    return candidates, import_root, boundary
def run_real_tests(
    filepath: str, fixed_code: str, project_root: str = "",
    source_roots=_DEFAULT_SOURCE_ROOTS,
    max_levels: int = _DEFAULT_TEST_SEARCH_MAX_LEVELS,
) -> tuple[str, str] | None:
    located = _locate_real_test_files(
        filepath, project_root=project_root, source_roots=source_roots,
        max_levels=max_levels)
    if located is None:
        return None
    candidates, import_root, run_root = located
    try:
        backup, encoding = _read_source_keep_newlines(filepath)
    except _SOURCE_READ_FAILURES as e:
        _log.warning("[BehaviorRegression] 运行测试失败,返回None: %s: %s", filepath, e)
        return None
    execution_roots = _module_source_roots(
        filepath, project_root=run_root, source_roots=source_roots)
    return _swap_verify_real_tests(
        filepath, fixed_code, backup, candidates, run_root, import_root,
        encoding, extra_pythonpath=execution_roots)
_REAL_PYTEST_ARGS = ("-q", "--tb=line", "-p", "no:cacheprovider",
                     "-o", "addopts=")
REAL_TEST_RESTORE_FAILED = "restore_failed"
def _pytest_failure_summary(stdout: str, stderr: str) -> str:
    lines = stdout.strip().splitlines()
    failed = [ln for ln in lines if "failed" in ln.lower()]
    summary = failed[-1] if failed else (lines[-1] if lines else stderr[:200])
    return summary[:200]
def _pythonpath_with_import_root(
    import_root: str, inherited: str,
    extra_pythonpath: Sequence[str] = _DEFAULT_SOURCE_ROOTS,
) -> str:
    parts: list[str] = []
    if import_root:
        _append_unique(parts, import_root)
    for path in _normalize_pythonpath_list(extra_pythonpath):
        _append_unique(parts, path)
    for path in _normalize_pythonpath_list(inherited.split(os.pathsep)):
        _append_unique(parts, path)
    return os.pathsep.join(parts)
def _real_pytest_once(
    candidates: list[str], skill_dir: str, import_root: str = "",
    extra_pythonpath: Sequence[str] = _DEFAULT_SOURCE_ROOTS,
) -> tuple[bool, str, bool]:
    env = {**subprocess_noartifact_env(), **_CHILD_IO_ENV}
    env["PYTHONPATH"] = _pythonpath_with_import_root(
        import_root, env.get("PYTHONPATH", ""), extra_pythonpath)
    sandbox_env = reset_state_sandbox()
    env.update(sandbox_env)
    env["PYTHONPYCACHEPREFIX"] = _sandbox_pycache_prefix(sandbox_env)
    try:
        result = subprocess.run(
            [sys.executable, "-m", "pytest", *_REAL_PYTEST_ARGS, *candidates],
            capture_output=True, text=True,
            timeout=_REAL_TEST_TIMEOUT_SEC, cwd=skill_dir, check=False,
            encoding="utf-8", errors="replace", env=env,
        )
        if result.returncode == 0:
            return True, "", False
        return False, _pytest_failure_summary(result.stdout, result.stderr), False
    except subprocess.TimeoutExpired as _e:
        _log.debug("[BehaviorRegression] 真实测试通道超时: %s", _e)
        return False, "pytest超时", True
    except (OSError, ValueError) as e:
        _log.debug("[BehaviorRegression] 真实测试通道启动异常: %s", e)
        return False, f"pytest异常: {safe_str(e)}", True
def _compare_real_rounds(
    fixed_passed: bool, fixed_error: str, fixed_env: bool,
    orig_passed: bool, orig_env: bool,
) -> tuple[str, str]:
    if fixed_env or orig_env:
        _log.warning(
            "[BehaviorRegression] 真实测试执行环境异常(不可判定): "
            "fixed_env=%s orig_env=%s", fixed_env, orig_env)
        return "inconclusive", ""
    if orig_passed and not fixed_passed:
        return "regressed", fixed_error
    if orig_passed and fixed_passed:
        return "passed", ""
    return "inconclusive", ""
def _swap_verify_real_tests(
    filepath: str, fixed_code: str, backup: str,
    candidates: list[str], skill_dir: str, import_root: str = "",
    encoding: str = _DEFAULT_SOURCE_ENCODING,
    extra_pythonpath: Sequence[str] = _DEFAULT_SOURCE_ROOTS,
) -> tuple[str, str] | None:
    result: tuple[str, str] | None
    restored = False
    try:
        _write_variant_content(filepath, fixed_code)
        fixed_passed, fixed_error, fixed_env = _real_pytest_once(
            candidates, skill_dir, import_root, extra_pythonpath)
        if fixed_env:
            result = _compare_real_rounds(
                fixed_passed, fixed_error, fixed_env, False, False)
        else:
            if not restore_file_content(filepath, backup, encoding):
                raise RuntimeError(
                    f"中段还原原始代码失败（磁盘停留 fixed 版，"
                    f"真实测试通道无法建立 orig 基线）: {filepath}")
            orig_passed, _orig_error, _orig_env = _real_pytest_once(
                candidates, skill_dir, import_root, extra_pythonpath)
            result = _compare_real_rounds(
                fixed_passed, fixed_error, fixed_env, orig_passed, _orig_env)
    except VERIFY_EXC as _ve:
        _log.warning("[BehaviorRegression] 真实测试通道异常"
                     "(降级跳过，合成通道兜底): %s", _ve, exc_info=True)
        result = None
    finally:
        restored = restore_file_content(filepath, backup, encoding)
    if not restored:
        return REAL_TEST_RESTORE_FAILED, (
            f"真实测试通道收尾还原原始代码失败（磁盘停留 fixed 版，"
            f"合成通道将自比对同一份代码，禁止降级）: {filepath}")
    return result
def _normalize_source_for_compare(text: str) -> str:
    return (text.lstrip('\ufeff').replace('\r\n', '\n')
            .replace('\r', '\n').rstrip())
def _file_matches_original(filepath: str,
                           original_code: str) -> bool | None:
    try:
        disk, _encoding = _read_source_keep_newlines(filepath)
    except _SOURCE_READ_FAILURES as _e:
        log_swallowed(__name__, _e,
                      context=f'_file_matches_original:{type(_e).__name__}')
        return None
    return (_normalize_source_for_compare(disk)
            == _normalize_source_for_compare(original_code))
def disk_baseline_path(filepath: Any, original_code: str) -> str:
    if not filepath:
        return ""
    if not isinstance(original_code, str):
        _log.warning(
            "[BehaviorRegression] original_code 非源码字符串形态(%s)，"
            "无法校验磁盘基线，改用内存批模式",
            type(original_code).__name__)
        return ""
    try:
        _path = os.fspath(filepath)
    except TypeError:
        _log.warning(
            "[BehaviorRegression] filepath 非路径形态(%s)，"
            "跳过真实测试通道与就地交换，改用内存批模式",
            type(filepath).__name__)
        return ""
    if isinstance(_path, bytes):
        _path = os.fsdecode(_path)
    if not isinstance(_path, str) or not os.path.isfile(_path):
        return ""
    matched = _file_matches_original(_path, original_code)
    if matched is None:
        _log.warning(
            "[BehaviorRegression] 磁盘基线不可读，就地交换基线不可信"
            "（真实测试通道与合成就地通道一并跳过，改用内存批模式）: %s",
            _path)
        return ""
    if matched:
        return _path
    _log.warning(
        "[BehaviorRegression] 磁盘内容与调用方传入的原始代码不一致，"
        "就地交换基线不可信（真实测试通道与合成就地通道一并跳过，"
        "改用内存批模式）: %s", _path)
    return ""
def _run_fresh_batch(batch_script: str, code: str, n_cases: int,
                     timeout_sec: float,
                     extra_pythonpath: Sequence[str]) -> dict | None:
    path = write_carrier_module(code, "orig")
    try:
        return execute_batch(batch_script, path, n_cases,
                             timeout_sec, extra_pythonpath)
    finally:
        delete_carrier_module(path)
class _InplaceSwapVerifier:
    def __init__(self, config: _RunConfig) -> None:
        self.config = config
    def verify(
        self, filepath: str, original_code: str, fixed_code: str,
        test_cases: list[TestCase], t0: float,
    ) -> BehaviorRegressionReport:
        report = BehaviorRegressionReport(total_tests=len(test_cases))
        resolved = _resolve_module(
            filepath, source_roots=self.config.extra_pythonpath)
        skill_parent = (resolved[0] if resolved is not None
                        else detect_package_root(filepath))
        backup_pair = self._read_backup(filepath, report, t0)
        if backup_pair is None:
            return report
        backup, encoding = backup_pair
        if not self._baseline_matches(backup, original_code):
            report.status = EquivalenceStatus.ERROR
            report.error_detail = (
                "磁盘内容与调用方原始代码不一致，拒绝以磁盘内容作为行为基线"
                f"（先核对磁盘版本，或改走内存批模式）: {filepath}")
            report.requires_manual_review = True
            report.elapsed_ms = (_time.time() - t0) * 1000
            return report
        try:
            self._verify_two_rounds(report, filepath, fixed_code, backup,
                                    encoding, skill_parent, test_cases)
        except VERIFY_EXC as e:
            _log.warning('就地验证过程发生异常: %s', e, exc_info=True)
            _mark_error(report, e)
        finally:
            if not restore_file_content(filepath, backup, encoding):
                _mark_restore_failed(report, filepath)
        report.elapsed_ms = (_time.time() - t0) * 1000
        return report
    @staticmethod
    def _baseline_matches(backup: str, original_code: str) -> bool:
        return (_normalize_source_for_compare(backup)
                == _normalize_source_for_compare(original_code))
    def _read_backup(self, filepath: str,
                     report: BehaviorRegressionReport,
                     t0: float) -> tuple[str, str] | None:
        try:
            return _read_source_keep_newlines(filepath)
        except _SOURCE_READ_FAILURES as e:
            log_swallowed(__name__, e,
                          context=f'_read_backup:{type(e).__name__}')
            report.status = EquivalenceStatus.ERROR
            report.error_detail = f"无法读取原始文件: {e}"
            report.requires_manual_review = True
            report.elapsed_ms = (_time.time() - t0) * 1000
            return None
    def _verify_two_rounds(
        self, report: BehaviorRegressionReport, filepath: str,
        fixed_code: str, backup: str, encoding: str, skill_parent: str,
        test_cases: list[TestCase],
    ) -> None:
        orig_results, fixed_results = self._run_two_rounds(
            filepath, fixed_code, backup, encoding, skill_parent, test_cases)
        _pre_fail, _nondet_idx, _window_orig = self._probe_nondet_inplace(
            filepath, test_cases, orig_results, fixed_results,
            skill_parent)
        _drift_candidates = [i for i in _pre_fail if i not in _nondet_idx]
        probe = _WindowDriftProbe(
            filepath=filepath, fixed_code=fixed_code, backup=backup,
            encoding=encoding, skill_parent=skill_parent,
            test_cases=test_cases,
            candidates=_drift_candidates, window_orig=_window_orig,
            orig_results=orig_results, fixed_results=fixed_results,
            nondet_idx=_nondet_idx)
        _drift_removed = (
            self._resolve_window_drift(probe) if _drift_candidates else [])
        self._assemble_results(report, probe, _drift_removed)
        _finalize_report_aggregation(
            report, len(test_cases),
            all_baseline_detail=(
                "无有效可裁决用例（orig 侧无可复现基线："
                "执行通道不可用或输出非确定性），无法验证行为等价性"),
        )
    def _run_two_rounds(
        self, filepath: str, fixed_code: str, backup: str, encoding: str,
        skill_parent: str, test_cases: list[TestCase],
    ) -> tuple[list[tuple], list[tuple]]:
        fixed_results = self._run_fixed_round(
            filepath, fixed_code, skill_parent, test_cases)
        orig_results = self._run_orig_round(
            filepath, backup, encoding, skill_parent, test_cases)
        return orig_results, fixed_results
    def _run_fixed_round(
        self, filepath: str, fixed_code: str, skill_parent: str,
        test_cases: list[TestCase],
    ) -> list[tuple]:
        _write_variant_content(filepath, fixed_code)
        return self._run_case_series(filepath, skill_parent, test_cases)
    def _run_orig_round(
        self, filepath: str, backup: str, encoding: str, skill_parent: str,
        test_cases: list[TestCase],
    ) -> list[tuple]:
        if not restore_file_content(filepath, backup, encoding):
            raise RuntimeError(
                f"中段还原原始代码失败（磁盘停留 fixed 版，"
                f"orig 侧无法建立行为基线）: {filepath}")
        return self._run_case_series(filepath, skill_parent, test_cases)
    def _assemble_results(
        self, report: BehaviorRegressionReport, probe: _WindowDriftProbe,
        drift_removed: list[int],
    ) -> None:
        for i, case in enumerate(probe.test_cases):
            orig_out, orig_exc = probe.orig_results[i]
            fixed_out, fixed_exc = probe.fixed_results[i]
            _tr = _build_test_result(
                case, orig_out, orig_exc, fixed_out, fixed_exc,
                nondet=i in probe.nondet_idx)
            if i in drift_removed:
                _tr.diff_detail = _drift_detail(_tr.diff_detail)
            report.test_results.append(_tr)
    def _probe_nondet_inplace(
        self, filepath: str, test_cases: list[TestCase],
        orig_results: list, fixed_results: list, skill_parent: str,
    ) -> tuple[list, set[int], dict[int, tuple]]:
        _window_orig: dict[int, tuple] = {}
        _pre_fail = [i for i in range(len(test_cases))
                     if not _verdict_passed(orig_results[i], fixed_results[i])]
        _nondet_idx = _probe_nondet_replay(
            test_cases, _pre_fail, orig_results, filepath, skill_parent,
            self.config, _window_orig)
        if _nondet_idx:
            _log.info("[BehaviorRegression] 确定性探针剔除 %d 个非确定"
                      "性用例: %s", len(_nondet_idx), sorted(_nondet_idx))
        return _pre_fail, _nondet_idx, _window_orig
    def _run_case_series(self, filepath: str, skill_parent: str,
                         test_cases: list[TestCase]) -> list[tuple]:
        """跑完整组用例，每个用例独占一个解释器子进程。

        用例之间彼此独立（各自独立解释器 + 独立状态沙箱），串行执行却要
        白付 N × 1.19 s 的解释器启动与治理包 import 固定成本（实测 200
        用例 376 s 中 238 s 是固定成本）。这里改成有界并行，语义与逐用例
        串行完全一致（每用例仍是独立子进程，不共享模块状态）。

        曾试过「单子进程批量协议」，实测同一份代码三次运行里两次裁决漂移
        （含一次误判 regressed）——共享进程的跨用例状态会污染行为基线，
        对回滚决策不可接受，故不采用。
        """
        if len(test_cases) <= 1:
            return [_execute_case(case, filepath, skill_parent, self.config)
                    for case in test_cases]
        prewarm_case_workers(skill_parent, self.config.extra_pythonpath,
                             skill_parent)
        with ThreadPoolExecutor(
                max_workers=_case_parallelism(len(test_cases)),
                thread_name_prefix="br-case") as pool:
            return list(pool.map(
                lambda case: _execute_case(
                    case, filepath, skill_parent, self.config),
                test_cases))
    def _resolve_window_drift(
        self, probe: _WindowDriftProbe,
    ) -> list[int]:
        _window_fixed = self._collect_window_fixed(probe)
        _drift_removed: list[int] = []
        for i in probe.candidates:
            _ow = probe.window_orig.get(i)
            _fw = _window_fixed.get(i)
            if not self._is_window_drift(probe, i, _ow, _fw):
                continue
            probe.nondet_idx.add(i)
            _drift_removed.append(i)
        if _drift_removed:
            _log.info(
                "[BehaviorRegression] 跨轮状态漂移消解复核剔除 "
                "%d 个状态敏感用例: %s", len(_drift_removed),
                sorted(_drift_removed))
        return _drift_removed
    def _collect_window_fixed(
        self, probe: _WindowDriftProbe,
    ) -> dict[int, tuple]:
        window_fixed: dict[int, tuple] = {}
        try:
            _write_variant_content(probe.filepath, probe.fixed_code)
            for i in probe.candidates:
                window_fixed[i] = _execute_case(
                    probe.test_cases[i], probe.filepath, probe.skill_parent,
                    self.config)
        finally:
            restore_file_content(probe.filepath, probe.backup, probe.encoding)
        return window_fixed
    @staticmethod
    def _is_window_drift(
        probe: _WindowDriftProbe, idx: int,
        window_orig_pair: tuple | None, window_fixed_pair: tuple | None,
    ) -> bool:
        if window_orig_pair is None or window_fixed_pair is None:
            return False
        same_window = _verdict_passed(window_orig_pair, window_fixed_pair)
        drift = (
            not _verdict_passed(probe.orig_results[idx], window_orig_pair)
            or not _verdict_passed(probe.fixed_results[idx], window_fixed_pair))
        return same_window and drift
class BehaviorRegressionExecutor:
    def __init__(self, timeout_sec: float = DEFAULT_BEHAVIOR_TIMEOUT_SEC,
                 extra_pythonpath: Sequence[str] | None = None) -> None:
        self._config = _RunConfig(
            timeout_sec=_normalize_timeout_sec(timeout_sec),
            extra_pythonpath=tuple(
                _normalize_pythonpath_list(extra_pythonpath)))
        self._inplace = _InplaceSwapVerifier(self._config)
    @property
    def timeout_sec(self) -> float:
        return self._config.timeout_sec
    @property
    def extra_pythonpath(self) -> list[str]:
        return list(self._config.extra_pythonpath)
    def verify_equivalence(
        self, original_code: str, fixed_code: str, test_cases: list[TestCase],
        filepath: str = "",
    ) -> BehaviorRegressionReport:
        t0 = _time.time()
        rejected = _reject_non_source_input(original_code, fixed_code)
        if rejected is not None:
            rejected.elapsed_ms = (_time.time() - t0) * 1000
            return rejected
        if not test_cases:
            empty = BehaviorRegressionReport(total_tests=0)
            _finalize_report_aggregation(
                empty, 0,
                all_baseline_detail=(
                    "未提供测试用例（无可对比证据，行为未被执行），"
                    "无法验证行为等价性"),
            )
            empty.elapsed_ms = (_time.time() - t0) * 1000
            return empty
        if filepath:
            return self._inplace.verify(
                filepath, original_code, fixed_code, test_cases, t0)
        report = self._run_batch_verification(original_code, fixed_code,
                                              test_cases)
        report.elapsed_ms = (_time.time() - t0) * 1000
        return report
    def _run_batch_verification(
        self, original_code: str, fixed_code: str,
        test_cases: list[TestCase],
    ) -> BehaviorRegressionReport:
        report = BehaviorRegressionReport(total_tests=len(test_cases))
        run = _BatchRun(original_code=original_code, test_cases=test_cases,
                        batch_script="")
        try:
            run.batch_script = generate_batch_script(test_cases)
            run.fixed_path = write_carrier_module(fixed_code, "fixed")
            run.fixed_results = execute_batch(
                run.batch_script, run.fixed_path, len(test_cases),
                self._config.timeout_sec, self._config.extra_pythonpath)
            self._run_orig_batch(run)
            self._probe_nondeterministic_cases(run)
            self._assemble_verdicts(report, run)
            _finalize_report_aggregation(
                report, len(test_cases),
                all_baseline_detail=(
                    "orig 侧无可复现行为基线（模块导入失败/"
                    "类无法无参实例化/输出非确定性），"
                    "无法对比行为等价性"),
            )
            return report
        except VERIFY_EXC as e:
            _log.warning(
                "[BehaviorRegression] 批量等价验证异常(降低为 error 报告): %s",
                MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
            _mark_error(report, e)
            return report
        finally:
            for path in (run.orig_path, run.fixed_path):
                delete_carrier_module(path)
    def _run_orig_batch(self, run: _BatchRun) -> None:
        run.orig_path = write_carrier_module(run.original_code, "orig")
        if _batch_key_covers(run.fixed_results, len(run.test_cases)):
            run.orig_results = execute_batch(
                run.batch_script, run.orig_path, len(run.test_cases),
                self._config.timeout_sec, self._config.extra_pythonpath)
    def _assemble_verdicts(self, report: BehaviorRegressionReport,
                           run: _BatchRun) -> None:
        _fallback_idx: list[int] = []
        if run.orig_results is None or run.fixed_results is None:
            common_indices = ()
        else:
            common_indices = run.orig_results.keys() & run.fixed_results.keys()
        for i, case in enumerate(run.test_cases):
            if i in common_indices:
                orig_output, orig_exc = run.orig_results[i]
                fixed_output, fixed_exc = run.fixed_results[i]
                result = _build_test_result(
                    case, orig_output, orig_exc, fixed_output, fixed_exc,
                    nondet=i in run.nondet_idx)
            else:
                result = self._run_single_test(
                    run.orig_path, run.fixed_path, case)
                _fallback_idx.append(i)
            report.test_results.append(result)
        if _fallback_idx and run.orig_path:
            self._demote_fallback_nondet(report, _fallback_idx, run)
    def _demote_fallback_nondet(
        self, report: BehaviorRegressionReport,
        fallback_idx: list[int], run: _BatchRun,
    ) -> None:
        for idx in self._probe_fallback_nondet(
                run.test_cases, report.test_results, fallback_idx,
                run.orig_path):
            result = report.test_results[idx]
            result.verdict = "baseline_unavailable"
            result.passed = False
            result.diff_detail = _nondet_diff(result.diff_detail)
            run.nondet_idx.add(idx)
    def _probe_nondeterministic_cases(self, run: _BatchRun) -> set:
        if run.orig_results is None or run.fixed_results is None:
            return set()
        _pre_fail = _divergent_indices(run.test_cases, run.orig_results,
                                       run.fixed_results)
        if not _pre_fail:
            return set()
        _np_runs = self._collect_probe_runs(run)
        _nondet_idx: set[int] = set()
        for i in _pre_fail:
            if _nondet_seq(_probe_observations(
                    i, run.orig_results, _np_runs)):
                _nondet_idx.add(i)
        if _nondet_idx:
            _log.info(
                "[BehaviorRegression] 确定性探针剔除 %d 个非确定性用例: %s",
                len(_nondet_idx), sorted(_nondet_idx))
        run.nondet_idx = _nondet_idx
        return _nondet_idx
    def _collect_probe_runs(self, run: _BatchRun) -> list[dict]:
        runs: list[dict] = []
        for _ in range(2):
            try:
                fresh = _run_fresh_batch(
                    run.batch_script, run.original_code, len(run.test_cases),
                    self._config.timeout_sec, self._config.extra_pythonpath)
            except OSError as exc:
                _log.warning(
                    "[BehaviorRegression] 确定性探针写盘失败(降级跳过): %s",
                    exc)
                break
            if fresh is not None:
                runs.append(fresh)
        return runs
    def _probe_fallback_nondet(
        self, test_cases: list, results: list,
        fallback_idx: list, orig_path: str,
    ) -> set:
        _pre_fail = [i for i in fallback_idx
                     if results[i].verdict == "regressed"]
        _first_pairs = {i: (results[i].original_output,
                            results[i].original_exception)
                        for i in _pre_fail}
        _nondet = _probe_nondet_replay(
            test_cases, _pre_fail, _first_pairs, orig_path, "", self._config)
        if _nondet:
            _log.info(
                "[BehaviorRegression] 补跑路径确定性探针剔除 %d 个非"
                "确定性用例: %s", len(_nondet), sorted(_nondet))
        return _nondet
    def _run_single_test(self, orig_path: Any, fixed_path: Any, case: Any) -> TestResult:
        if orig_path is None or fixed_path is None:
            return TestResult(
                case_id=case.case_id,
                function_name=case.function_name,
                passed=False,
                original_exception=(
                    "UNAVAILABLE: orig 执行载体缺失"
                    if orig_path is None else None),
                fixed_exception=(
                    "UNAVAILABLE: fixed 执行载体缺失"
                    if fixed_path is None else None),
                diff_detail=(
                    "执行通道不可用（补跑路径执行载体缺失），"
                    "该用例无法建立行为对比证据"),
                verdict="baseline_unavailable",
            )
        orig_output, orig_exc = _execute_case(
            case, orig_path, "", self._config)
        fixed_output, fixed_exc = _execute_case(
            case, fixed_path, "", self._config)
        return _build_test_result(case, orig_output, orig_exc, fixed_output, fixed_exc)

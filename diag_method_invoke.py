from __future__ import annotations

import inspect
import io
import json
import logging
import math
import os
import queue as _queue
import sys
import threading
import time
import tokenize
import traceback
from collections.abc import Callable
from contextlib import (
    contextmanager,
    nullcontext,
)
from dataclasses import dataclass, field
from typing import (
    Any,
)

from jwsgj.diag_blindspot_report import run_callgraph_channel
from jwsgj.diag_detector_findings import (
    consolidate_findings,
    detector_entry,
    filter_retired_findings,
    group_envelope,
    normalize_conf_enum,
    worst_sub_status,
)
from jwsgj.diag_exception_verdict import (
    EM_KNOWN_FP_PATTERNS,
    assemble_exception_result,
    d4_tc_entry,
)
from jwsgj.diag_exception_verdict import (
    safe_analyze_exceptions as _safe_analyze_exceptions,
)
from jwsgj.diag_simulate_runner import (
    ReuseArtifacts,
    project_sandbox_channel,
    simulate_and_diagnose,
)
from jwsgj.diag_types_normalize import (
    as_entry_list,
    as_list,
    as_number,
    coerce_line,
    count_findings_in_payload,
    dict_or_empty,
    extract_cv_metadata,
    finite_float_or_zero,
    is_real_number,
    safe_int,
    safe_text,
    signal_bool,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    DIAGNOSIS_METHOD_BUDGET_S,
    FIELD_EXECUTION_ERROR,
    MESSAGE_TRUNCATE_LEN,
    MS_PER_SECOND,
    OUTPUT_TRUNCATE_LEN,
    TRACEBACK_TRUNCATE_LEN,
    is_finding_carrier_key,
)
from jwsgj.log_config import (
    log_swallowed,
    perf_trace,
)
from jwsgj.shared_cache import (
    CacheNotWarmedError,
    as_diag_ctx,
    diagnostic_read_scope,
    ensure_entry_warmed,
    fingerprint_freeze_window,
    get_or_create_cache,
    get_process_call_lock,
    require_warmed,
)
from jwsgj.xv_context_derivation import (
    METHOD_EVIDENCE_TYPES,
    METHOD_REGISTRY,
    lookup_method_phase,
    sub_engine_payload,
)
from jwsgj.xv_context_derivation import (
    TERMINAL_STATUSES as _TERMINAL_STATUSES,
)
from jwsgj.xv_intermediate_store import (
    compute_skill_source_hash,
    get_round_start_ts,
    list_source_files,
    load_intermediate,
    locate_sub_results,
    resolve_intermediate_dirs,
    save_intermediate,
)

__all__ = [  # noqa: RUF022
    'MethodResult',
    'METHOD_CALLABLES',
    'RuntimeAnalyzer',
    'WorkflowViolationError',
    'ensure_method_cache',
    'method_process_scope',
    'run_d1_runtime_analysis',
    'run_engine_C',
    'run_full_runtime_analysis',
    'run_in_fingerprint_window',
    'run_one_with_timeout',
    'run_single_method',
]
logger = logging.getLogger(__name__)
def _derive_duration_ms(elapsed_s) -> int:
    try:
        return int(finite_float_or_zero(elapsed_s) * MS_PER_SECOND)
    except (OverflowError, ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_derive_duration_ms:{type(_e).__name__}')
        return 0
def _normalized_duration_ms(value, elapsed_s) -> int:
    normalized = 0 if isinstance(value, bool) else safe_int(value)
    return max(0, normalized or _derive_duration_ms(elapsed_s))
@dataclass
class MethodResult:
    method_id: str
    method_name: str = ""
    domain: str = ""
    status: str = "pending"
    verdict: str = ""
    verdict_reason: str = ""
    elapsed_s: float = 0.0
    findings_count: int = 0
    score: float = 0.0
    summary: str = ""
    payload: dict = field(default_factory=dict)
    error: str = ""
    findings_list: list = field(default_factory=list)
    rule_families_produced: set = field(default_factory=set)
    partial: bool = False
    quality_flags: list = field(default_factory=list)
    evidence_types: set = field(default_factory=set)
    execution_mode: str = "full"
    degradation_context: dict = field(default_factory=dict)
    timestamp: str = ""
    duration_ms: int = 0
    phase: str = ""
    def __post_init__(self):
        self.elapsed_s = max(0.0, finite_float_or_zero(self.elapsed_s))
        self.duration_ms = _normalized_duration_ms(
            self.duration_ms, self.elapsed_s)
        if not self.execution_mode:
            self.execution_mode = "full"
        if not self.timestamp:
            self.timestamp = timestamp_ms()
    def to_dict(self) -> dict:
        try:
            d = {
                "method_id": self.method_id,
                "method_name": self.method_name,
                "domain": self.domain,
                "status": self.status,
                "verdict": self.verdict,
                "verdict_reason": self.verdict_reason,
                "elapsed_s": round(
                    max(0.0, finite_float_or_zero(self.elapsed_s)), 2),
                "findings_count": max(0, safe_int(self.findings_count)),
                "score": self.score if is_real_number(self.score) else 0.0,
                "summary": self.summary,
                "error": self.error,
                "payload": self.payload,
            }
            d["findings_list"] = self.findings_list
            d["rule_families_produced"] = sorted(self.rule_families_produced)
            d["partial"] = self.partial
            d["quality_flags"] = self.quality_flags
            d["evidence_types"] = sorted(self.evidence_types)
            d["execution_mode"] = self.execution_mode
            d["degradation_context"] = self.degradation_context
            d["timestamp"] = self.timestamp
            d["duration_ms"] = _normalized_duration_ms(
                self.duration_ms, self.elapsed_s)
            d["phase"] = self.phase
            return d
        except Exception as e:
            logger.warning("to_dict: %s", e, exc_info=True)
            return {"_error": True, "_partial": True}
    def to_meta_summary(self) -> dict:
        try:
            d = self.to_dict()
            payload_size = (len(self.payload)
                            if isinstance(self.payload, dict) and self.payload
                            else 0)
            d.pop("payload", None)
            d["payload_size"] = payload_size
            return d
        except Exception as e:
            logger.warning("to_meta_summary: %s", e, exc_info=True)
            return {"_error": True, "_partial": True}
class WorkflowViolationError(Exception):
    pass
_PROCESS_CALL_COUNT: int = 0
def _claim_process_slot(_internal: bool) -> None:
    global _PROCESS_CALL_COUNT
    _PROCESS_CALL_COUNT += 1
    if _PROCESS_CALL_COUNT > 1 and not _internal:
        raise WorkflowViolationError(
            "工作流违规：run_single_method 在同一进程中已被调用过。\n"
            "这通常意味着你在一个脚本中用 for/while 循环批量执行多个方法。\n"
            "P0 强制规则：每个方法必须单独一个命令轮次（一个 Python 进程）。\n"
            "正确做法：退出当前脚本，为下一个方法发起新的 Python 调用。\n"
            f"当前进程已调用 {_PROCESS_CALL_COUNT} 次，仅允许 1 次。"
        )
@contextmanager
def method_process_scope(_internal: bool = False):
    with get_process_call_lock():
        _claim_process_slot(_internal)
        yield
def ensure_method_cache(skill_dir: str, cache: Any = None) -> Any:
    """确保方法执行前的共享缓存已全量预热；驻留残缺时自愈重建。

    历史缺陷：单条 AST 驻留缺失（LRU 逐出、单条解析失败后未回填、并发释放）
    会让 ``ensure_warmed()`` 抛 ``CacheNotWarmedError``，而批量入口对此直接
    上抛——六个诊断方法只能完成第一个，调用方必须手工 ``clear`` 再预热才能
    续跑（实测 307 模块规模下 A 完成后 B 必然中断）。

    驻留残缺是**可恢复**状态：释放实例后重新预热即可，代价是一次全量解析，
    远低于整批诊断作废。因此这里把它收敛为「释放 + 重建」，其余异常照常上抛。
    """
    if cache is None:
        return get_or_create_cache(skill_dir)
    ensure = getattr(cache, "ensure_warmed", None)
    if not callable(ensure):
        return cache
    try:
        ensure()
        return cache
    except CacheNotWarmedError:
        logger.warning(
            "[Cache] 方法前置校验发现驻留残缺，释放并重新预热后继续",
            exc_info=True)
    release = getattr(cache, "release", None)
    if callable(release):
        try:
            release()
        except Exception as _release_err:  # noqa: BLE001 — 释放失败不阻断重建
            log_swallowed(__name__, _release_err,
                          context="ensure_method_cache:release")
    return get_or_create_cache(skill_dir)
def run_in_fingerprint_window(cfg, cache: Any, skill_dir: str,
                              body: Callable) -> tuple:
    _fp_before = source_fingerprint_before(cfg, skill_dir)
    if cache is None or getattr(cfg, "domain", "") == "treatment":
        return body(), _fp_before
    with fingerprint_freeze_window(cache, "Single"):
        return body(), _fp_before
# 单个诊断方法的执行时间预算（秒）。
#
# 历史缺陷：本函数名为 ``run_one_with_timeout``，但 ``_t.join()`` **没有传
# timeout**——方法一旦变慢就是无限挂起，管线永远停在 ``pending_diagnosis``，
# 既拿不到结果也不进降级通道（静默挂死的典型形态）。
# ``file`` 维度按「文件数 × 检测器数」逐检测器独立遍历 AST，307 模块规模下
# 实测单方法可达一小时以上，必须给硬预算。
_METHOD_TIMEOUT_ENV = "JWSGJ_METHOD_TIMEOUT_S"
# 单一真源：见 ``diag_types_vocab.DIAGNOSIS_METHOD_BUDGET_S``。
_METHOD_TIMEOUT_DEFAULT_S = DIAGNOSIS_METHOD_BUDGET_S
_METHOD_TIMEOUT_MIN_S = 60.0
def method_timeout_budget() -> float:
    """读取单方法时间预算（秒），非法值回落默认。"""
    raw = os.environ.get(_METHOD_TIMEOUT_ENV, "").strip()
    if not raw:
        return _METHOD_TIMEOUT_DEFAULT_S
    try:
        budget = float(raw)
    except (TypeError, ValueError):
        logger.warning("[MethodTimeout] %s=%r 非数值，回落 %.0fs",
                       _METHOD_TIMEOUT_ENV, raw, _METHOD_TIMEOUT_DEFAULT_S)
        return _METHOD_TIMEOUT_DEFAULT_S
    return (budget
            if math.isfinite(budget) and budget >= _METHOD_TIMEOUT_MIN_S
            else _METHOD_TIMEOUT_DEFAULT_S)
def run_one_with_timeout(mid: str, func: Callable, cache: Any,
                         extra_kwargs: dict | None = None,
                         skill_dir: str | None = None) -> MethodResult:
    cfg = METHOD_REGISTRY.get(mid)
    name = getattr(cfg, "name", None) or mid
    domain = getattr(cfg, "domain", None) or "unknown"
    extra_kwargs = extra_kwargs or {}
    _sd = getattr(cache, "skill_dir", "") or skill_dir or ""
    start = time.perf_counter()
    _reader = getattr(cache, "get_source", None) if cache is not None else None
    worker, result_box = _run_worker(
        func, _sd, cache, extra_kwargs, mid,
        scope_kwargs={
            "memoize_walk": cache is not None and domain != "treatment",
            "bind_reader": callable(_reader),
            "reader": _reader,
        })
    budget = method_timeout_budget()
    worker.join(budget)
    if worker.is_alive():
        logger.error("[MethodTimeout] 方法 %s 超过时间预算 %.0fs，按超时降级",
                     mid, budget)
        return _error_result(
            mid, name, domain, time.perf_counter() - start,
            summary=f"方法执行超时（>{budget:.0f}s）",
            error=(f"method {mid} exceeded {budget:.0f}s budget; "
                   f"worker thread left as daemon"),
            reason="method_timeout",
        )
    result = _drain_worker_result(result_box, mid, name, domain, start)
    _trace_method_perf(result)
    return result
def _trace_method_perf(result: MethodResult) -> None:
    try:
        perf_trace(result.method_id, result.duration_ms,
                        status=result.status,
                        method_name=result.method_name,
                        domain=result.domain)
    except Exception as _perf_exc:  # noqa: BLE001
        log_swallowed(__name__, _perf_exc,
                      context=(f'perf_trace:{result.method_id}'
                               f':{type(_perf_exc).__name__}'))
def _run_worker(func: Callable, sd: str, cache: Any, extra_kwargs: dict,
                mid: str,
                scope_kwargs: dict | None = None) -> tuple:
    """启动方法执行线程，返回 ``(thread, result_box)``。

    join 与超时裁决留在调用方：只有那里同时持有 ``name``/``domain``/
    ``start``，才能把超时降级成合规的 ``MethodResult``。
    """
    result_box: _queue.Queue = _queue.Queue(maxsize=1)
    _quiesce_coverage_tracing()
    def _worker():
        # 分析线程必须脱离进程级 coverage tracer。``run_one_with_timeout``
        # 允许超时放弃 worker（daemon 线程继续运行），残留线程若仍参与
        # tracing，就会与后续新建 Collector 的 ``data_lock`` 互等，形成
        # 不可恢复的硬死锁（实测 E 方法 9 线程全部阻塞在 lock_data）。
        sys.settrace(None)
        try:
            _scope = (diagnostic_read_scope(cache, **scope_kwargs)
                      if scope_kwargs is not None else nullcontext())
            with _scope:
                value = _invoke_with_cache(func, sd, cache, extra_kwargs)
        except Exception as e:  # noqa: BLE001
            log_swallowed(__name__, e,
                          context='run_one_with_timeout._worker'
                                  f':{type(e).__name__}')
            result_box.put_nowait(("error", e))
            return
        result_box.put_nowait(("ok", value))
    _t = threading.Thread(target=_worker, name="diag-" + str(mid), daemon=True)
    _t.start()
    return _t, result_box
def _is_coverage_tracer(tracer: Any) -> bool:
    """判断 tracer 是否由 coverage 安装（只识别自家钩子）。

    ``threading.gettrace()`` 返回的是 ``Collector._installation_trace``
    这种**绑定方法**（``type(...)`` 为 ``builtins.method``），因此必须看
    ``__self__`` 的归属模块；``sys.gettrace()`` 返回 ``CTracer`` 实例，直接
    看类型模块。两条通道都要覆盖，否则 threading 钩子会漏清。
    """
    if not tracer:
        return False
    owner = getattr(tracer, "__self__", None) or tracer
    module = getattr(type(owner), "__module__", "") or ""
    return module.split(".", 1)[0] == "coverage"
def _quiesce_coverage_tracing() -> None:
    """清除残留的进程级 coverage tracer。

    ``Coverage.start()`` 会把 tracer 同时装到 ``sys`` 与 ``threading`` 上；
    方法切换后 Collector 的数据可能已关闭，继续 tracing 会抛错，更会在并行
    worker 超时被放弃后与 ``data_lock`` 互等死锁。仅在钩子确实来自 coverage
    时清除，不影响调用方自己的调试器。
    """
    try:
        if _is_coverage_tracer(sys.gettrace()):
            sys.settrace(None)
        get_thread_trace = getattr(threading, "gettrace", None)
        if get_thread_trace is not None and _is_coverage_tracer(
                get_thread_trace()):
            threading.settrace(None)
    except (AttributeError, TypeError, RuntimeError) as _exc:  # 降级：不清也不阻断
        log_swallowed(__name__, _exc,
                      context=f'_quiesce_coverage_tracing:{type(_exc).__name__}')
_CACHE_PARAMETER_NAMES = ("_cache", "cache")
def _cache_parameter_name(signature: inspect.Signature, sd: str,
                          kwargs: dict) -> str | None:
    ordered_names = sorted(
        _CACHE_PARAMETER_NAMES,
        key=lambda name: name not in signature.parameters)
    parameter_names = tuple(signature.parameters)
    for name in ordered_names:
        parameter = signature.parameters.get(name)
        candidate = dict(kwargs)
        try:
            if (parameter is not None
                    and parameter.kind is inspect.Parameter.POSITIONAL_ONLY):
                if parameter_names.index(name) != 1:
                    continue
                signature.bind(sd, None, **candidate)
            else:
                candidate[name] = None
                signature.bind(sd, **candidate)
        except TypeError:
            continue
        return name
    return None
def _invoke_with_cache(func: Callable, sd: str, cache: Any,
                       extra_kwargs: dict) -> Any:
    kwargs = dict(extra_kwargs or {})
    try:
        signature = inspect.signature(func)
    except (TypeError, ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_invoke_with_cache:signature'
                              f':{type(_e).__name__}')
        return func(sd, _cache=cache, **kwargs)
    parameter = _cache_parameter_name(signature, sd, kwargs)
    if parameter is not None:
        declared = signature.parameters.get(parameter)
        if (declared is not None
                and declared.kind is inspect.Parameter.POSITIONAL_ONLY):
            return func(sd, cache, **kwargs)
        kwargs[parameter] = cache
    return func(sd, **kwargs)
def _drain_worker_result(result_box: _queue.Queue, mid: str, name: str,
                         domain: str, start: float) -> MethodResult:
    try:
        tag, val = result_box.get_nowait()
    except _queue.Empty as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context=('_drain_worker_result'
                               f':{type(_swallow_e).__name__}'))
        return _error_result(
            mid, name, domain, time.perf_counter() - start,
            summary="worker died without result",
            error="execution thread terminated without result",
            reason="worker_died",
        )
    if tag == "error":
        e = val
        elapsed = time.perf_counter() - start
        tb_str = "".join(
            traceback.format_exception(type(e), e, e.__traceback__)
        )[-TRACEBACK_TRUNCATE_LEN:]
        return _error_result(
            mid, name, domain, elapsed,
            summary="Exception: " + type(e).__name__ + ": "
                    + safe_text(e, MESSAGE_TRUNCATE_LEN),
            error=tb_str,
            reason="unhandled_exception",
        )
    elapsed = time.perf_counter() - start
    return _build_result(val, mid, name, domain, elapsed)
DEGRADED_RULE_ID = "METHOD_DEGRADED"
def _degraded_finding(mid: str, summary: str, reason: str) -> dict:
    """构造「方法降级」的 P0 finding。

    历史缺陷（最危险的静默）：方法超时/异常时 ``findings_list`` 为空，
    聚合报告里的 ``findings_count`` 就是 0——**长得和「零缺陷」一模一样**。
    使用者会据此判定代码健康，而实际上该维度根本没被检查过。

    现在任何降级都必须产出一条 P0，并显式说明「结论不可用」，
    使「未检查」与「无问题」在报告层可区分。
    """
    return {
        "rule_id": DEGRADED_RULE_ID,
        "severity": "P0",
        "source": mid,
        "file": "",
        "line": 0,
        "confidence": 1.0,
        "degraded_reason": reason,
        "message": (
            f"诊断方法 {mid} 执行降级（{reason}）：{summary}"
            f"——本方法结论不可用，禁止按「无缺陷」解读"),
    }
def _error_result(
    mid: str, name: str, domain: str, elapsed: float,
    summary: str, error: str, reason: str,
) -> MethodResult:
    degraded = [_degraded_finding(mid, summary, reason)]
    return MethodResult(
        method_id=mid, method_name=name, domain=domain,
        status="error", elapsed_s=elapsed,
        summary=summary,
        error=error,
        partial=True,
        findings_count=len(degraded),
        findings_list=degraded,
        quality_flags=[FIELD_EXECUTION_ERROR],
        evidence_types=set(METHOD_EVIDENCE_TYPES.get(mid, set())),
        execution_mode="error",
        degradation_context={"affected_rules": [], "reason": reason},
        timestamp=timestamp_ms(),
        duration_ms=int(elapsed * MS_PER_SECOND),
        phase=lookup_method_phase(mid),
    )
def _build_result(
    raw: Any, mid: str, name: str, domain: str,
    elapsed: float,
):
    ctx = _result_ctx(mid, elapsed)
    if hasattr(raw, "status") and hasattr(raw, "method_name"):
        result = _result_from_named_tuple(
            raw, mid, name, domain, elapsed, ctx)
    elif isinstance(raw, dict) and raw.get("__error__"):
        result = _result_from_error_dict(
            raw, mid, name, domain, elapsed, ctx)
    elif isinstance(raw, dict):
        result = _result_from_plain_dict(raw, mid, name, domain, elapsed, ctx)
    else:
        result = _result_from_other_type(raw, mid, name, domain, elapsed, ctx)
    return _ensure_degraded_evidence(result, mid)
def _ensure_degraded_evidence(result: MethodResult, mid: str) -> MethodResult:
    if not result.partial:
        return result
    if FIELD_EXECUTION_ERROR not in result.quality_flags:
        result.quality_flags = [*result.quality_flags, FIELD_EXECUTION_ERROR]
    if result.findings_count <= 0 and result.findings_list:
        result.findings_count = len(result.findings_list)
    if result.findings_count > 0 or result.findings_list:
        return result
    context = (result.degradation_context
               if isinstance(result.degradation_context, dict) else {})
    reason = str(context.get("reason") or result.execution_mode or "degraded")
    result.findings_list = [
        _degraded_finding(mid, result.summary, reason)]
    result.findings_count = 1
    return result
def _namedtuple_findings_fallback(raw: Any, payload: dict) -> int:
    findings = getattr(raw, "findings", None)
    if findings is not None:
        try:
            return len(findings)
        except (TypeError, ValueError) as _count_exc:
            log_swallowed(__name__, _count_exc,
                          context=('_namedtuple_findings_fallback:len'
                                   f':{type(_count_exc).__name__}'))
    return count_findings_in_payload(payload)
def _status_field(value: Any, default: str) -> tuple[str, str]:
    if value is None:
        return default, ""
    if isinstance(value, str):
        return value or default, ""
    return "error", f"非法执行状态类型: {type(value).__name__}"
_LEGACY_FAIL_STATUSES = frozenset({"fail", "failed"})
_VERDICT_VALUES = frozenset({"pass", "warn", "fail"})
_LEGACY_FAIL_VERDICT_REASON = "诊断结论未通过（发现 P0 阻断项）"
def _split_status_verdict(status: str, verdict: Any,
                          verdict_reason: Any) -> tuple[str, str, str]:
    """把「诊断结论 fail」从「执行健康 status」中拆出。

    fail 表示方法已执行完成、但诊断结论存在 P0 阻断项；它不是执行失败。
    历史中间结果与尚未改造的子引擎仍可能给出 status=fail，在此统一归一为
    execution status=warn + verdict=fail，避免下游报告误报「诊断方法失败」。
    """
    _status = status.strip().lower() if isinstance(status, str) else status
    _verdict = (verdict.strip().lower()
                if isinstance(verdict, str) else "")
    _reason = _text_field(verdict_reason)
    if _status in _LEGACY_FAIL_STATUSES:
        if _verdict not in _VERDICT_VALUES:
            _verdict = "fail"
        if not _reason and _verdict == "fail":
            _reason = _LEGACY_FAIL_VERDICT_REASON
        _status = "warn"
    elif _verdict not in _VERDICT_VALUES:
        _verdict = ""
    return _status, _verdict, _reason
def _result_from_named_tuple(raw: Any, mid: str, name: str, domain: str,
                             elapsed: float, ctx: tuple) -> MethodResult:
    _phase, _ts_str, _dur_ms, _ev_types = ctx
    ts_payload = _serializable_payload(raw)
    fl, rf, qf = extract_cv_metadata(ts_payload)
    _status, _status_error = _status_field(raw.status, "warn")
    _verdict = getattr(raw, "verdict", "")
    _verdict_reason = getattr(raw, "verdict_reason", "")
    _status, _verdict, _verdict_reason = _split_status_verdict(
        _status, _verdict, _verdict_reason)
    _err_out = _text_field(getattr(raw, "error", ""))
    if _status_error:
        _err_out = (f"{_status_error}; {_err_out}"
                    if _err_out else _status_error)
        if FIELD_EXECUTION_ERROR not in qf:
            qf = [*qf, FIELD_EXECUTION_ERROR]
    if not _err_out and _status == "error":
        _err_out = _aggregate_sub_engine_error(ts_payload)
    _status = _status_with_error(_status, _err_out)
    is_partial, _exec_mode = _resolve_execution_state(_status, _err_out)
    _deg_ctx = _deg_ctx_from(rf, _exec_mode, is_partial)
    _ms = getattr(raw, "elapsed_ms", None)
    _elapsed_s, _dur_ms = _elapsed_pair(_ms, elapsed, _dur_ms)
    _fc = getattr(raw, "findings_count", None)
    if not is_real_number(_fc) or _fc <= 0:
        _fc = _namedtuple_findings_fallback(raw, ts_payload)
    _sc = getattr(raw, "score", None)
    return MethodResult(
        method_id=mid, method_name=raw.method_name or name,
        domain=domain,
        status=_status,
        verdict=_verdict,
        verdict_reason=_verdict_reason,
        elapsed_s=_elapsed_s,
        findings_count=_fc,
        score=_sc if is_real_number(_sc) else 0.0,
        summary=_text_field(getattr(raw, "summary", ""), MESSAGE_TRUNCATE_LEN),
        error=_err_out,
        payload=ts_payload,
        findings_list=fl,
        rule_families_produced=rf,
        partial=is_partial,
        quality_flags=qf,
        evidence_types=set(_ev_types),
        execution_mode=_exec_mode,
        degradation_context=_deg_ctx,
        timestamp=_ts_str,
        duration_ms=_dur_ms,
        phase=_phase,
    )
def _result_from_error_dict(raw: dict, mid: str, name: str, domain: str,
                            elapsed: float, ctx: tuple) -> MethodResult:
    _phase, _ts_str, _dur_ms, _ev_types = ctx
    err_payload = {"error_detail": _safe_serialize(raw)}
    fl, rf, qf = extract_cv_metadata(raw)
    if FIELD_EXECUTION_ERROR not in qf:
        qf = [*qf, FIELD_EXECUTION_ERROR]
    return MethodResult(
        method_id=mid, method_name=name, domain=domain,
        status="error", elapsed_s=elapsed,
        summary=f"执行异常: {safe_text(raw.get('error_type') or 'Unknown')}",
        error=_text_field(raw.get("error_message", "")),
        payload=err_payload,
        findings_list=fl,
        rule_families_produced=rf,
        partial=True,
        quality_flags=qf,
        evidence_types=set(_ev_types),
        execution_mode="error",
        degradation_context=_deg_ctx_from(rf, FIELD_EXECUTION_ERROR, True),
        timestamp=_ts_str,
        duration_ms=_dur_ms,
        phase=_phase,
    )
def _result_from_plain_dict(raw: dict, mid: str, name: str, domain: str,
                            elapsed: float, ctx: tuple) -> MethodResult:
    _phase, _ts_str, _dur_ms, _ev_types = ctx
    dict_payload = _serializable_payload(raw)
    fl, rf, qf = extract_cv_metadata(dict_payload)
    _ms = raw.get("elapsed_ms")
    _elapsed_s, _dur_ms = _elapsed_pair(_ms, elapsed, _dur_ms)
    _status, _status_error = _status_field(raw.get("status"), "pass")
    _status, _verdict, _verdict_reason = _split_status_verdict(
        _status, raw.get("verdict"), raw.get("verdict_reason"))
    _err_out = _text_field(raw.get("error", ""))
    if _status_error:
        _err_out = (f"{_status_error}; {_err_out}"
                    if _err_out else _status_error)
        if FIELD_EXECUTION_ERROR not in qf:
            qf = [*qf, FIELD_EXECUTION_ERROR]
    if not _err_out and _status == "error":
        _err_out = _aggregate_sub_engine_error(raw)
    _status = _status_with_error(_status, _err_out)
    is_partial, _exec_mode = _resolve_execution_state(_status, _err_out)
    return MethodResult(
        method_id=mid, method_name=name, domain=domain,
        status=_status,
        verdict=_verdict,
        verdict_reason=_verdict_reason,
        elapsed_s=_elapsed_s,
        findings_count=count_findings_in_payload(raw),
        score=_resolve_dict_score(raw),
        summary=_text_field(raw.get("summary", ""), MESSAGE_TRUNCATE_LEN),
        error=_err_out,
        payload=dict_payload,
        findings_list=fl,
        rule_families_produced=rf,
        partial=is_partial,
        quality_flags=qf,
        evidence_types=set(_ev_types),
        execution_mode=_exec_mode,
        degradation_context=_deg_ctx_from(rf, _exec_mode, is_partial),
        timestamp=_ts_str,
        duration_ms=_dur_ms,
        phase=_phase,
    )
def _status_with_error(status: str, error: str) -> str:
    return "error" if error and status in ("pass", "warn") else status
def _resolve_execution_state(status, error) -> tuple[bool, str]:
    is_partial = bool(error) or status in ("timeout", "error")
    if status == "timeout":
        return is_partial, "timeout"
    if status == "error":
        return is_partial, "error"
    return is_partial, "partial" if is_partial else "full"
def _resolve_dict_score(raw: dict) -> float:
    _score = raw.get("score")
    if not is_real_number(_score):
        _score = raw.get("health_score")
    if not is_real_number(_score):
        _score = 0.0
    return _score
def _result_from_other_type(raw: Any, mid: str, name: str, domain: str,
                            elapsed: float, ctx: tuple) -> MethodResult:
    del ctx
    _type_name = type(raw).__name__
    _detail = f"诊断方法返回非结构化类型: {_type_name}"
    result = _error_result(
        mid, name, domain, elapsed,
        summary=_detail, error=_detail, reason="non_structured_payload")
    result.payload = {"raw": safe_text(raw, OUTPUT_TRUNCATE_LEN)}
    result.quality_flags = ["non_structured_payload", FIELD_EXECUTION_ERROR]
    return result
def _result_ctx(mid: str, elapsed: float) -> tuple[str, str, int, set]:
    return (lookup_method_phase(mid), timestamp_ms(),
            int(elapsed * MS_PER_SECOND), METHOD_EVIDENCE_TYPES.get(mid, set()))
def _deg_ctx_from(rf: set, reason: str, active: bool) -> dict:
    if not active:
        return {}
    return {"affected_rules": sorted(rf), "reason": reason}
def _elapsed_pair(ms: Any, elapsed: float, dur_ms: int) -> tuple[float, int]:
    if is_real_number(ms):
        try:
            return ms / float(MS_PER_SECOND), int(ms)
        except (OverflowError, ValueError) as _e:
            log_swallowed(__name__, _e,
                          context=f'_elapsed_pair:{type(_e).__name__}')
    return elapsed, dur_ms
def _text_field(value: Any, limit: int | None = None) -> str:
    return safe_text(value or "", limit)
def _aggregate_sub_engine_error(raw: Any) -> str:
    if not isinstance(raw, dict):
        return ""
    _summary = ""
    try:
        _sub = locate_sub_results(raw)
        if _sub:
            _summary = _join_sub_error_parts(_collect_sub_error_parts(_sub))
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context=('_aggregate_sub_engine_error'
                               f':{type(_e).__name__}'))
    return _summary
def _collect_sub_error_parts(_sub: dict) -> list[str]:
    _parts: list[str] = []
    for det_id, det in _sub.items():
        if not isinstance(det, dict):
            continue
        entry = _sub_error_entry(det_id, det)
        if entry is not None:
            _parts.append(entry)
    return _parts
_SUB_ENGINE_ERROR_STATUSES = frozenset({"error", "timeout", "blocked"})
def _sub_error_entry(det_id: str, det: dict) -> str | None:
    _st = _first_text(det.get("sub_status"), det.get("status"))
    # warn/fail/skip 都是「已产出结果」的正常终端：fail 属诊断结论（P0），
    # 不得拼成执行错误文本，否则下游会把质量裁决当成方法崩溃。
    if _st not in _SUB_ENGINE_ERROR_STATUSES:
        return None
    _inner = det.get("result") if isinstance(det.get("result"), dict) else {}
    _reason = _first_text(det.get("error"), det.get("summary"),
                          _inner.get("error"), _inner.get("summary"))
    return f"{det_id}({_st}): {_reason}" if _reason else f"{det_id}({_st})"
def _first_text(*values: Any) -> str:
    for value in values:
        if value:
            return safe_text(value)
    return ""
def _join_sub_error_parts(_parts: list[str]) -> str:
    if not _parts:
        return ""
    def _rank_key(_p: str) -> int:
        _, _sep, _tail = _p.partition("(")
        if not _sep:
            return 2
        return {"error": 0, "fail": 1}.get(_tail.split(")", 1)[0], 2)
    _ordered = sorted(_parts, key=_rank_key)
    return "子引擎非pass: " + "; ".join(_ordered)[:MESSAGE_TRUNCATE_LEN]
def _call_dict_method(obj: Any, method_name: str) -> dict | None:
    _fn = getattr(obj, method_name, None)
    if not callable(_fn):
        return None
    try:
        _value = _fn()
    except Exception as _e:  # noqa: BLE001
        logger.warning("[MethodInvoke] %s() 调用失败，降级后续转换分支: %s",
                       method_name, _e)
        return None
    return _value if isinstance(_value, dict) else None
def _serializable_payload(raw: Any) -> dict:
    _d = _call_dict_method(raw, "_asdict")
    if _d is not None:
        return _safe_serialize(_d)
    _d = _call_dict_method(raw, "to_dict")
    if _d is not None:
        return _safe_serialize(_d)
    if isinstance(raw, dict):
        return _safe_serialize(raw)
    return {"raw": safe_text(raw, OUTPUT_TRUNCATE_LEN)}
def _safe_json_key(key: Any) -> str:
    if isinstance(key, str):
        return key
    try:
        encoded = json.dumps({key: None}, allow_nan=False)
        return next(iter(json.loads(encoded)))
    except (TypeError, ValueError, RecursionError) as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc,
                      context=(f'_safe_json_key:{type(_swallowed_exc).__name__}'))
        return safe_text(key, MESSAGE_TRUNCATE_LEN)
def _safe_nested_json_value(value, active: set[int], memo: dict[int, Any]):
    if not isinstance(value, (dict, list, tuple)):
        json.dumps(value, allow_nan=False)
        return value
    marker = id(value)
    if marker in active:
        raise RecursionError("circular container")
    if marker in memo:
        return memo[marker]
    active.add(marker)
    try:
        if isinstance(value, dict):
            converted = {}
            changed = False
            items = sorted(
                value.items(), key=lambda item: not isinstance(item[0], str))
            for key, item in items:
                base_key = _safe_json_key(key)
                safe_key = base_key
                suffix = 2
                while safe_key in converted:
                    safe_key = f"{base_key}#{suffix}"
                    suffix += 1
                new_item = _safe_nested_json_value(item, active, memo)
                converted[safe_key] = new_item
                changed |= safe_key != key or new_item is not item
            result = converted if changed else value
        else:
            items = [_safe_nested_json_value(item, active, memo)
                     for item in value]
            changed = any(new is not old
                          for new, old in zip(items, value, strict=False))
            result = ((items if isinstance(value, list) else tuple(items))
                      if changed else value)
    finally:
        active.remove(marker)
    memo[marker] = result
    return result
def _safe_serialize(d: dict) -> dict:
    safe = {}
    memo: dict[int, Any] = {}
    items = sorted(d.items(), key=lambda item: not isinstance(item[0], str))
    for k, v in items:
        base_key = _safe_json_key(k)
        safe_key = base_key
        suffix = 2
        while safe_key in safe:
            safe_key = f"{base_key}#{suffix}"
            suffix += 1
        try:
            safe[safe_key] = _safe_nested_json_value(v, set(), memo)
        except (TypeError, ValueError, RecursionError) as e:
            logger.warning(
                "[MethodInvoke] 值 JSON 序列化失败，降级 str: %s (%s)", k, e)
            safe[safe_key] = safe_text(v, MESSAGE_TRUNCATE_LEN)
    return safe
_STATUS_ORDER = {"pass": 0, "warn": 1, "fail": 2, "error": 3}
def _merge_status(sub: dict) -> str:
    if not isinstance(sub, dict):
        return "warn"
    _st = sub.get("status", "pass")
    if not isinstance(_st, str) or _st not in _STATUS_ORDER:
        return "warn"
    return _st
def _join_summaries(subs) -> str:
    parts: list[str] = []
    for sub in subs:
        if not isinstance(sub, dict):
            continue
        summary = sub.get("summary")
        if isinstance(summary, str) and summary:
            parts.append(summary)
    return "; ".join(parts)
def _worst_status(subs, all_findings: list) -> str:
    worst = "pass"
    for sub in subs:
        _st = _merge_status(sub)
        if _STATUS_ORDER[_st] > _STATUS_ORDER[worst]:
            worst = _st
    if all_findings and worst == "pass":
        worst = "warn"
    return worst
class RuntimeAnalyzer:
    def __init__(self, skill_dir: str, cache: Any = None):
        self.skill_dir = skill_dir
        self.cache = cache
    def _cache_slots(self):
        if self.cache is not None and hasattr(self.cache, "slots"):
            return self.cache.slots
        return None
    def _call_graph_from_cache(self) -> Any:
        slots = self._cache_slots()
        if slots is not None and slots.has_call_graph():
            return slots.get_call_graph()
        return None
    def _diag_ctx_from_cache(self) -> Any:
        if self._cache_slots() is not None:
            return as_diag_ctx(self.cache)
        return None
    def _cached_blindspot_report(self):
        slots = self._cache_slots()
        if slots is not None:
            return slots.get_blindspot_report()
        return None
    def _run_simulation(self):
        return simulate_and_diagnose(
            self.skill_dir,
            reuse=ReuseArtifacts(
                call_graph=self._call_graph_from_cache(),
                blindspot_report=self._cached_blindspot_report(),
                skip_blindspot_scan=False,
            ),
            ctx=self._diag_ctx_from_cache(),
        )
    def run_sandbox(self) -> dict:
        sim_report, blindspot_report = self._run_simulation()
        return project_sandbox_channel(
            sim_report, blindspot_report, self.skill_dir)
    def run_resource_leak(self) -> dict:
        _cg = self._call_graph_from_cache()
        slots = self._cache_slots()
        if slots is not None and slots.has_exception_result():
            result = slots.get_exception_result()
            if isinstance(result, dict):
                return assemble_exception_result(
                    result, self.skill_dir, self.cache)
        result = _safe_analyze_exceptions(
            self.skill_dir, ctx=self._diag_ctx_from_cache(), graph=_cg)
        return assemble_exception_result(result, self.skill_dir, self.cache)
    def _run_sub_safe(self, channel: str, fn) -> dict:
        try:
            result = fn()
            if not isinstance(result, dict):
                raise TypeError(
                    f"通道返回非字典: {type(result).__name__}")
            return result
        except Exception as e:
            logger.warning("[RuntimeAnalyzer] %s 通道异常（降级 error）: %s",
                           channel, e, exc_info=True)
            return {"status": "error", "findings": [],
                    "summary": f"{channel} 通道异常（降级）: {e}"}
    def analyze(self) -> dict:
        sandbox_result = self._run_sub_safe("sandbox", self.run_sandbox)
        leak_result = self._run_sub_safe("resource_leak", self.run_resource_leak)
        subs = (sandbox_result, leak_result)
        all_findings = (as_entry_list(sandbox_result.get("findings"))
                        + as_entry_list(leak_result.get("findings")))
        return {
            "status": _worst_status(subs, all_findings),
            "findings_count": len(all_findings),
            "findings": all_findings,
            "summary": _join_summaries(subs),
            "sandbox": sandbox_result,
            "resource_leak": leak_result,
        }
@dataclass
class _BytecodeGuardState:
    depth: int = 0
    original: bool = False
_BYTECODE_GUARD_LOCK = threading.Lock()
_BYTECODE_GUARD_STATE = _BytecodeGuardState()
@contextmanager
def _bytecode_write_scope():
    with _BYTECODE_GUARD_LOCK:
        if _BYTECODE_GUARD_STATE.depth == 0:
            _BYTECODE_GUARD_STATE.original = sys.dont_write_bytecode
        _BYTECODE_GUARD_STATE.depth += 1
        sys.dont_write_bytecode = True
    try:
        yield
    finally:
        with _BYTECODE_GUARD_LOCK:
            _BYTECODE_GUARD_STATE.depth -= 1
            if _BYTECODE_GUARD_STATE.depth == 0:
                sys.dont_write_bytecode = _BYTECODE_GUARD_STATE.original
def run_full_runtime_analysis(skill_dir: str, cache: Any = None) -> dict:
    with _bytecode_write_scope():
        cache = ensure_entry_warmed(
            skill_dir, cache, who="run_full_runtime_analysis")
        analyzer = RuntimeAnalyzer(skill_dir, cache)
        return analyzer.analyze()
_D1_RETIRED_DETAIL_CAP = 50
def _retired_count(items) -> int:
    if not items:
        return 0
    last = items[-1]
    if isinstance(last, dict) and last.get("truncated"):
        total = last.get("total")
        if (isinstance(total, int) and not isinstance(total, bool)
                and total >= 0):
            return total
        return len(items) - 1
    return len(items)
def _status_or_error(value) -> str:
    return value if value in ("pass", "warn", "error") else "error"
def _result_status_findings(result: dict) -> tuple:
    return (_status_or_error(result.get("status")),
            as_list(result.get("findings")))
def _stage_error_part(error) -> dict:
    return {"status": "error", "findings_count": 0,
            "error": safe_text(error, MESSAGE_TRUNCATE_LEN)}
_SANDBOX_BLINDSPOT_METRIC_KEYS = (
    "clustering", "exception_propagation",
    "cross_validation", "cross_validation_full",
)
def _sandbox_blindspot_metrics(d3_result: dict) -> dict:
    metrics = dict_or_empty(
        dict_or_empty(d3_result.get("blindspots")).get("metrics"))
    return {key: metrics[key] for key in _SANDBOX_BLINDSPOT_METRIC_KEYS
            if isinstance(metrics.get(key), dict) and metrics[key]}
def _sandbox_payload_part(d3_result: dict, d3_status: str, d3_findings: list,
                          sim: dict, degraded_skip: list,
                          sim_errors_sample: list) -> dict:
    return {
        "simulation": dict(sim),
        "blindspot_metrics": _sandbox_blindspot_metrics(d3_result),
        "status": _status_or_error(d3_status),
        "findings_count": len(d3_findings),
        "executed": as_number(sim.get("executed", 0), 0),
        "succeeded": as_number(sim.get("succeeded", 0), 0),
        "failed": as_number(sim.get("failed", 0), 0),
        "degraded_skipped": len(degraded_skip),
        "degraded_skipped_sample": degraded_skip[:10],
        "sim_errors_count": as_number(
            d3_result.get("sim_errors_count", 0), 0),
        "sim_errors_sample": sim_errors_sample,
        "entries_discovered": as_number(
            d3_result.get("entries_discovered", 0), 0),
        "entries_truncated": as_number(
            d3_result.get("entries_truncated", 0), 0),
    }
def _d1_sandbox_stage(skill_dir: str, cache) -> tuple:
    analyzer = None
    try:
        analyzer = RuntimeAnalyzer(skill_dir, cache)
        d3_result = analyzer.run_sandbox()
        d3_status, d3_findings = _result_status_findings(d3_result)
        _sim = dict_or_empty(d3_result.get("simulation"))
        _ds_raw = d3_result.get("degraded_skipped")
        _degraded_skip = _ds_raw if isinstance(_ds_raw, (list, tuple)) else []
        _ses_raw = d3_result.get("sim_errors_sample", [])
        _sim_errors_sample = (_ses_raw
                              if isinstance(_ses_raw, (list, tuple)) else [])
        sandbox_part = _sandbox_payload_part(
            d3_result, d3_status, d3_findings, _sim,
            _degraded_skip, _sim_errors_sample)
        dead_code_part = None
        if d3_result.get("dead_code_phases"):
            dead_code_part = {
                "dead_code_phases": d3_result["dead_code_phases"],
            }
        return (sandbox_part, dead_code_part, d3_findings,
                # 口径必须与 ``_sandbox_verdict`` 一致：只有「全部入口都跳过」
                # 才算无可运行性证据。部分入口成功时即使有跳过，也已拿到
                # 执行证据，再降级会把「依赖一条未放行」误判成「整个沙箱
                # 没验证」。
                ((bool(_degraded_skip)
                  and as_number(sandbox_part.get("succeeded", 0), 0) <= 0)
                 or d3_status in ("error", "warn")),
                analyzer)
    except Exception as e:  # noqa: BLE001
        logger.warning("[D1] 沙箱执行失败: %s", e)
        return (_stage_error_part(e), None, [], True, analyzer)
def _noop_audit(*_args) -> None:  # jwsgj:suppress dead_stub IA-03 SK-01 C8_dead_code empty_function — 审计回调默认空实现，由 d4_tc_entry 按需替换为真实审计器
    pass  # jwsgj:suppress empty_function — 审计回调默认空实现，按需替换
def _d1_tc_pattern_counts(tc_raw, skill_dir: str) -> dict:
    tc_counts: dict = {}
    for _f in as_list(tc_raw):
        if not (isinstance(_f, dict) and _f.get("pattern")):
            continue
        _pat = str(_f["pattern"]).strip()
        if d4_tc_entry(_f, skill_dir, _noop_audit)[0] != "keep":
            continue
        tc_counts[_pat] = tc_counts.get(_pat, 0) + 1
    return tc_counts
def _d1_em_pattern_counts(em_raw) -> tuple:
    em_retired = 0
    _bp_raw = dict_or_empty(dict_or_empty(em_raw).get("by_pattern"))
    em_counts: dict = {}
    for _pat, _n in _bp_raw.items():
        if not is_real_number(_n) or _n < 0:
            continue
        _pat = str(_pat)
        if _pat in EM_KNOWN_FP_PATTERNS:
            em_retired += _n
            continue
        em_counts[_pat] = _n
    return em_counts, em_retired
def _d1_exception_metrics(d4_metrics, skill_dir: str) -> tuple:
    exception_metrics = None
    em_retired = 0
    if isinstance(d4_metrics, dict):
        tc_counts = _d1_tc_pattern_counts(
            d4_metrics.get("tryceratops"), skill_dir)
        em_counts, em_retired = _d1_em_pattern_counts(
            d4_metrics.get("exception_miner"))
        if tc_counts or em_counts:
            exception_metrics = {
                "tryceratops": {
                    "total": sum(tc_counts.values()),
                    "by_pattern": tc_counts,
                },
                "exception_miner": {
                    "total": sum(em_counts.values()),
                    "by_pattern": em_counts,
                },
            }
    return exception_metrics, em_retired
def _d1_retired_detail(tc_retired) -> list:
    return tc_retired[:_D1_RETIRED_DETAIL_CAP] + (
        [{"truncated": True,
          "total": _retired_count(tc_retired)}]
        if len(tc_retired) > _D1_RETIRED_DETAIL_CAP else [])
def _d1_resource_leak_stage(analyzer, skill_dir: str,
                            sandbox_error: str) -> tuple:
    if analyzer is None:
        _msg = (f"RuntimeAnalyzer 构造失败: {sandbox_error}"
                if sandbox_error else "RuntimeAnalyzer 构造失败")
        logger.warning("[D1] 资源泄漏检测失败: %s", _msg)
        return _stage_error_part(_msg), [], True
    try:
        d4_result = analyzer.run_resource_leak()
        d4_status, d4_findings = _result_status_findings(d4_result)
        _metrics_base = dict_or_empty(d4_result.get("metrics"))
        exception_metrics, em_retired = _d1_exception_metrics(
            _metrics_base, skill_dir)
        _tc_retired = as_list(
            _metrics_base.get("tryceratops_retired"))
        payload_part = {
            "status": _status_or_error(d4_status),
            "findings_count": len(d4_findings),
            "exception_metrics": exception_metrics,
            "filter_audit": _metrics_base.get("filter_audit"),
            "tryceratops_retired": _retired_count(_tc_retired),
            "em_retired": em_retired,
            "tryceratops_retired_detail": _d1_retired_detail(_tc_retired),
        }
        return payload_part, d4_findings, d4_status in ("error", "warn")
    except Exception as e:  # noqa: BLE001
        logger.warning("[D1] 资源泄漏检测失败: %s", e)
        return _stage_error_part(e), [], True
def _merge_stage(payload_parts: dict, all_findings: list, key: str,
                 part: dict, findings: list) -> None:
    payload_parts[key] = part
    all_findings.extend(findings)
_D1_CHANNEL_LABELS: tuple[tuple[str, str], ...] = (
    ("callgraph", "调用图"),
    ("sandbox", "沙箱模拟"),
    ("resource_leak", "资源泄漏"),
)
def _d1_channel_descriptor(key: str, part: dict, state: str) -> str:
    """单个通道的降级描述：状态 + 关键计数。

    状态是诊断结论，warn/error 必须能指回具体通道。只报「共 0 个发现」
    时，读者无法区分「检查通过」与「检查降级」，报告会变成
    「warn + 0 发现」这种无法解释的组合。

    ``state`` 由 ``_d1_channel_state`` 给出而非从 ``part["status"]`` 重算：
    沙箱的降级还包含 ``degraded_skipped`` 非空这一支，只看 status 会漏报。
    """
    status = state
    label = dict(_D1_CHANNEL_LABELS).get(key, key)
    detail = ""
    if key == "sandbox":
        failed = int(as_number(part.get("failed", 0), 0))
        executed = int(as_number(part.get("executed", 0), 0))
        skipped = int(as_number(part.get("degraded_skipped", 0), 0))
        if failed > 0:
            detail = f"（{failed}/{executed} 入口执行失败）"
        elif skipped > 0:
            detail = f"（跳过 {skipped} 项）"
    return f"{label}={status}{detail}"
def _d1_degraded_channels(payload_parts: dict,
                          channel_states: dict[str, str]) -> str:
    """列出所有非 pass 通道；全部 pass 时返回空串。"""
    degraded = [
        _d1_channel_descriptor(
            key, dict_or_empty(payload_parts.get(key)),
            channel_states.get(key, "pass"))
        for key, _label in _D1_CHANNEL_LABELS
        if channel_states.get(key, "pass") != "pass"
    ]
    return "、".join(degraded)
def _build_d1_result(all_findings: list, payload_parts: dict,
                     status: str,
                     channel_states: dict[str, str] | None = None) -> dict:
    n = len(all_findings)
    if n and status == "pass":
        status = "warn"
    _summary = f"运行时分析引擎: 调用图+沙箱+资源泄漏, 共{n}个发现"
    if status != "pass" and not n:
        _degraded = _d1_degraded_channels(
            payload_parts, channel_states if channel_states is not None else {})
        if _degraded:
            _summary += f"；降级通道: {_degraded}"
    result = {
        "status": status,
        "findings_count": n,
        "summary": _summary,
        "findings": all_findings,
        "payload": payload_parts,
    }
    _dc = dict_or_empty(
        payload_parts.get("dead_code_confirmation")).get("dead_code_phases")
    if _dc:
        result["dead_code_phases"] = _dc
    _em_metrics = dict_or_empty(
        payload_parts.get("resource_leak")).get("exception_metrics")
    if _em_metrics:
        result["exception_metrics"] = _em_metrics
    _sandbox = dict_or_empty(payload_parts.get("sandbox"))
    if _sandbox.get("simulation"):
        result["simulation"] = _sandbox["simulation"]
    if _sandbox.get("blindspot_metrics"):
        result["blindspot_metrics"] = _sandbox["blindspot_metrics"]
    return result
def _d1_channel_state(part: dict, degraded: bool) -> str:
    status = _status_or_error(dict_or_empty(part).get("status"))
    if status == "error":
        return "error"
    if degraded or status == "warn":
        return "warn"
    return "pass"
def _d1_aggregate_status(channel_states: list[str]) -> str:
    if any(state == "error" for state in channel_states):
        return "error"
    return "warn" if any(state != "pass" for state in channel_states) else "pass"
def run_d1_runtime_analysis(skill_dir: str, cache=None) -> dict:
    all_findings: list = []
    payload_parts: dict = {}
    _channel_states: dict[str, str] = {}
    cg_part, cg_findings, cg_degraded = run_callgraph_channel(skill_dir, cache)
    _merge_stage(payload_parts, all_findings, "callgraph", cg_part, cg_findings)
    _channel_states["callgraph"] = _d1_channel_state(cg_part, cg_degraded)
    (sb_part, sb_dead_code, sb_findings,
     sb_degraded, analyzer) = _d1_sandbox_stage(skill_dir, cache)
    _merge_stage(payload_parts, all_findings, "sandbox", sb_part, sb_findings)
    _channel_states["sandbox"] = _d1_channel_state(sb_part, sb_degraded)
    if sb_dead_code is not None:
        payload_parts["dead_code_confirmation"] = sb_dead_code
    rl_part, rl_findings, rl_degraded = _d1_resource_leak_stage(
        analyzer, skill_dir, str(sb_part.get("error") or ""))
    _merge_stage(payload_parts, all_findings, "resource_leak",
                 rl_part, rl_findings)
    _channel_states["resource_leak"] = _d1_channel_state(rl_part, rl_degraded)
    return _build_d1_result(
        all_findings, payload_parts,
        _d1_aggregate_status(list(_channel_states.values())),
        _channel_states)
_C_DETECTOR_IDS = ("C1",)
def _run_d1_runtime_stage(skill_dir: str, cache) -> dict:
    require_warmed(cache, "D1 运行时分析引擎")
    with diagnostic_read_scope(cache):
        return normalize_conf_enum(
            run_d1_runtime_analysis(skill_dir, cache=cache))
def _run_c1_detector(skill_dir: str, cache) -> list:
    det_results: list = []
    with fingerprint_freeze_window(cache, "C组"):
        det_results.append(detector_entry(
            "C1", _run_d1_runtime_stage, skill_dir, cache,
            logger=logger, engine_tag="engine_c"))
    return det_results
def _c_group_summary(det_results: list, stats: dict) -> str:
    return (
        f"主引擎C: 检测器{len(det_results)}个, "
        f"原始发现{stats['raw_findings']}, "
        f"预合并后{stats['merged_findings']}, 冲突{stats['conflicts']}"
    )
def _log_engine_c_run(worst, det_results, merged, conflicts,
                      elapsed_ms) -> None:
    logger.info(
        "run_engine_C 完成: 状态=%s, 检测器=%d个, 发现=%d, 耗时=%.1fms",
        worst, len(det_results), len(merged), elapsed_ms,
        extra={
            "event": "engine_run",
            "payload": {
                "engine": "C",
                "status": worst,
                "detectors": len(det_results),
                "findings_count": len(merged),
                "conflicts": len(conflicts),
            },
            "duration_ms": elapsed_ms,
        })
def run_engine_C(skill_dir: str, cache=None) -> dict:
    cache = ensure_entry_warmed(skill_dir, cache, "主引擎 C 组")
    t0 = time.perf_counter()
    det_results = _run_c1_detector(skill_dir, cache)
    merged, conflicts, stats = consolidate_findings(
        det_results, source_method="C", merged_from="engine_c")
    worst = worst_sub_status(det_results, merged)
    summary = _c_group_summary(det_results, stats)
    elapsed_ms = round((time.perf_counter() - t0) * 1000, 1)
    _log_engine_c_run(worst, det_results, merged, conflicts, elapsed_ms)
    return group_envelope(
        "C", _C_DETECTOR_IDS, worst, merged, stats, det_results, t0,
        summary=summary, conflicts=conflicts)
def _engine_a(sd, **kw):
    from jwsgj.build_skill_quality_a2 import (
        run_engine_a,  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    )
    return run_engine_a(sd, kw.get("_cache"))
def _engine_b(sd, **kw):
    from jwsgj.engine_b2_history import (
        run_engine_B,  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    )
    return run_engine_B(sd, kw.get("_cache"))
def _engine_d(sd, **kw):
    from jwsgj.engine_d_security import (
        run_engine_D,  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    )
    return run_engine_D(sd, kw.get("_cache"))
def _engine_e(sd, **kw):
    from jwsgj.testsuite_orchestrator import (
        run_engine_E,  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    )
    cache = kw.pop("_cache", None)
    return run_engine_E(sd, cache, **kw)
def _engine_f(sd, **kw):
    from jwsgj.engine_f_deadcode import (
        run_engine_f,  # lazy-by-design — 引擎分派/平台条件/可选依赖按需装载，顶层导入会引入环或拖慢启动
    )
    return run_engine_f(sd, kw.get("_cache"))
METHOD_CALLABLES: dict[str, Callable] = {
    "A": _engine_a,
    "B": _engine_b,
    "C": run_engine_C,
    "D": _engine_d,
    "E": _engine_e,
    "F": _engine_f,
}
def _resolve_callable(mid: str) -> Callable:
    raw = METHOD_CALLABLES.get(mid)
    if raw is None:
        raise ValueError(f"未注册的方法: {mid}")
    return raw
def _default_intermediate_dir(method_id: str, skill_dir: str,
                               intermediate_dir: str) -> str:
    try:
        return resolve_intermediate_dirs(skill_dir)[2]
    except (OSError, RuntimeError, ValueError) as _de:
        logger.warning(
            "[Single] %s 默认中间目录解析失败，跳过默认回退通道"
            "（主 intermediate_dir 不受影响）: %s", method_id, _de)
        return intermediate_dir
def _load_dependency_channel(method_id: str, dep_id: str, directory: str,
                             freshness_cutoff: str, channel: str):
    try:
        return load_intermediate(
            directory, dep_id, strict_provenance=False,
            freshness_cutoff=freshness_cutoff)
    except Exception as _dep_exc:  # noqa: BLE001
        logger.warning("[Single] %s 依赖 %s %s读取失败，视为未就绪: %s",
                       method_id, dep_id, channel, _dep_exc)
        return None
def _read_dependency_payload(method_id: str, dep_id: str, intermediate_dir: str,
                             fallback_dir_of: Callable[[], str],
                             freshness_cutoff: str,
                             current_hash_of: Callable[[], str | None]):
    def _usable(dep_data) -> bool:
        return (_is_terminal_result(dep_data)
                and _source_cache_valid(
                    dep_id, dep_data, current_hash_of()))
    dep_data = _load_dependency_channel(
        method_id, dep_id, intermediate_dir, freshness_cutoff, "中间结果")
    if _usable(dep_data):
        return dep_data
    fallback_dir = fallback_dir_of()
    if fallback_dir == intermediate_dir:
        return None
    dep_data = _load_dependency_channel(
        method_id, dep_id, fallback_dir, freshness_cutoff, "默认目录回退")
    return dep_data if _usable(dep_data) else None
def _check_method_dependencies(method_id, cfg, intermediate_dir, skill_dir,
                               freshness_cutoff: str = ""):
    missing_deps = []
    default_intermediate: str | None = None
    _hash_cell: list = []
    def _current_hash() -> str | None:
        if not _hash_cell:
            _hash_cell.append(_current_source_hash(method_id, skill_dir))
        return _hash_cell[0]
    def _fallback_dir() -> str:
        nonlocal default_intermediate
        if default_intermediate is None:
            default_intermediate = _default_intermediate_dir(
                method_id, skill_dir, intermediate_dir)
        return default_intermediate
    for dep_id in cfg.depends_on:
        dep_data = _read_dependency_payload(
            method_id, dep_id, intermediate_dir, _fallback_dir,
            freshness_cutoff, _current_hash)
        if dep_data is None:
            missing_deps.append(dep_id)
    if missing_deps:
        return _dependency_skip_result(method_id, cfg, missing_deps)
    return None
def _dependency_skip_result(method_id: str, cfg,
                            missing_deps: list[str]) -> dict:
    return MethodResult(
        method_id=method_id,
        method_name=cfg.name,
        domain=cfg.domain,
        status="skip",
        summary=(f"依赖方法未完成: {','.join(missing_deps)}，"
                 f"请先执行上述依赖方法后再重试"),
        payload={"missing_dependencies": missing_deps},
        phase=lookup_method_phase(method_id),
    ).to_dict()
def _prepare_extra_kwargs(method_id: str, intermediate_dir: str,
                          skill_dir: str, cache,
                          report_provider: Callable[..., dict] | None,
                          ) -> dict:
    if method_id == "E" and report_provider is not None:
        return {"report": report_provider(intermediate_dir, skill_dir, cache)}
    return {}
def _is_terminal_result(data: object) -> bool:
    return isinstance(data, dict) and data.get("status") in _TERMINAL_STATUSES
def _try_resume_completed(method_id: str, intermediate_dir: str,
                          skill_dir: str) -> dict | None:
    _round_ts = get_round_start_ts(skill_dir)
    try:
        data = load_intermediate(intermediate_dir, method_id,
                                 strict_provenance=False,
                                 freshness_cutoff=_round_ts)
    except Exception as _li_exc:  # noqa: BLE001
        logger.warning("[Single] %s 中间结果读取失败，降级重新执行: %s",
                       method_id, _li_exc)
        return None
    if not isinstance(data, dict):
        return None
    if not _source_cache_valid(method_id, data,
                               _current_source_hash(method_id, skill_dir)):
        return None
    if _is_terminal_result(data):
        logger.info("[Single] %s 已完成（断点续传跳过）", method_id)
        data.setdefault("method_id", method_id)
        return data
    if data.get("status") == "skip":
        logger.info("[Single] %s 上次为 skip（依赖未满足），尝试重新执行", method_id)
    return None
def _current_source_hash(method_id: str, skill_dir: str) -> str | None:
    try:
        return compute_skill_source_hash(skill_dir)
    except Exception as _fp_exc:  # noqa: BLE001
        logger.warning("[Single] %s 源码指纹校验失败，缓存结果不可用: %s",
                       method_id, _fp_exc)
        return None
def _source_cache_valid(method_id: str, data: dict,
                        current_hash: str | None) -> bool:
    if current_hash is None:
        return False
    if data.get("_source_hash") == current_hash:
        return True
    logger.info("[Single] %s 源码已变更，缓存结果作废", method_id)
    return False
def _handle_dependency_skip(method_id: str, cfg, intermediate_dir: str,
                           skill_dir: str) -> dict | None:
    if not cfg.depends_on:
        return None
    _dep_cutoff = get_round_start_ts(skill_dir)
    _dep_result = _check_method_dependencies(
        method_id, cfg, intermediate_dir, skill_dir,
        freshness_cutoff=_dep_cutoff)
    if _dep_result is None:
        return None
    os.makedirs(intermediate_dir, exist_ok=True)
    save_intermediate(intermediate_dir, method_id, _dep_result,
                      skill_dir=skill_dir)
    return _dep_result
def run_single_method(
    skill_dir: str,
    method_id: str,
    output_dir: str | None = None,
    resume: bool = True,
    cache: Any | None = None,
    report_provider: Callable[..., dict] | None = None,
    _internal: bool = False,
) -> dict:
    if method_id not in METHOD_REGISTRY:
        raise ValueError(
            f"未注册的方法 ID: {method_id}，"
            f"可用: {list(METHOD_REGISTRY)}"
        )
    with method_process_scope(_internal):
        return _execute_single_method_pipeline(
            skill_dir, method_id, output_dir, resume, cache, report_provider)
_STATUS_ICONS = {"pass": "✓", "warn": "⚠", "fail": "✗",
                 "timeout": "⏱", "skip": "−", "error": "✗"}
def _log_method_outcome(method_id: str, result) -> None:
    logger.info("[%s] %s %s (%.1fs) — %s",
                _STATUS_ICONS.get(result.status, "?"), method_id,
                result.status, result.elapsed_s, result.summary[:80])
def _early_terminal_result(method_id: str, cfg, intermediate_dir: str,
                           skill_dir: str, resume: bool) -> dict | None:
    if resume:
        _resumed = _try_resume_completed(
            method_id, intermediate_dir, skill_dir)
        if _resumed is not None:
            return _resumed
    return _handle_dependency_skip(
        method_id, cfg, intermediate_dir, skill_dir)
def _execute_single_method_pipeline(skill_dir: str, method_id: str,
                                    output_dir: str | None, resume: bool,
                                    cache,
                                    report_provider: Callable[..., dict] | None,
                                    ) -> dict:
    cfg = METHOD_REGISTRY[method_id]
    skill_dir, output_dir, intermediate_dir = resolve_intermediate_dirs(
        skill_dir, output_dir)
    _early = _early_terminal_result(
        method_id, cfg, intermediate_dir, skill_dir, resume)
    if _early is not None:
        return _early
    cache = ensure_method_cache(skill_dir, cache)
    func = _resolve_callable(method_id)
    extra_kwargs = _prepare_extra_kwargs(
        method_id, intermediate_dir, skill_dir, cache, report_provider)
    logger.info("[Single] 执行 %s %s (完整执行, 单方法超时预算 %.0fs)",
                method_id, cfg.name, method_timeout_budget())
    os.makedirs(intermediate_dir, exist_ok=True)
    result, _source_fp_before = run_in_fingerprint_window(
        cfg, cache, skill_dir,
        lambda: run_one_with_timeout(
            method_id, func, cache,
            extra_kwargs=extra_kwargs, skill_dir=skill_dir))
    _finalize_single_method(
        result, method_id, skill_dir, intermediate_dir, cache,
        source_fp_before=_source_fp_before)
    _log_method_outcome(method_id, result)
    return result.to_dict()
def _resolve_snapshot_path(fp: str, skill_dir: str) -> str | None:
    if (os.path.isabs(fp)
            and (os.name != "nt" or os.path.splitdrive(fp)[0])
            and os.path.isfile(fp)):
        return fp
    rel = fp.lstrip("/\\")
    if rel:
        cand = os.path.join(skill_dir, rel)
        if os.path.isfile(cand):
            return cand
    if os.path.isabs(fp) and os.path.isfile(fp):
        return fp
    return None
def _snapshot_ref(f: dict) -> tuple[str, int] | None:
    fp = f.get("file") or f.get("file_path") or f.get("location") or ""
    ln = coerce_line(f.get("line"))
    valid = isinstance(fp, str) and bool(fp) and ln > 0
    return (fp, ln) if valid else None
def _memo_read_lines(fp: str, skill_dir: str,
                     lines_cache: dict[str, list[str]], cache,
                     ) -> list[str] | None:
    fp = _resolve_snapshot_path(fp, skill_dir)
    if fp is None:
        return None
    lines = lines_cache.get(fp)
    if lines is not None:
        return lines
    source = _read_snippet_source(fp, cache)
    if source is None:
        return None
    lines = source.split("\n")
    lines_cache[fp] = lines
    return lines
def _read_snippet_source(fp: str, cache) -> str | None:
    getter = getattr(cache, "get_source", None) if cache is not None else None
    if callable(getter):
        try:
            source = getter(fp)
        except Exception as _cache_e:  # noqa: BLE001
            logger.debug("[InjectCodeSnippets] 缓存读源失败，回退盘读: %s",
                         _cache_e)
            source = None
        if isinstance(source, str):
            return source
    try:
        with open(fp, "rb") as fh:
            raw = fh.read()
        encoding, _lines = tokenize.detect_encoding(io.BytesIO(raw).readline)
        return raw.decode(encoding)
    except (OSError, SyntaxError, ValueError, LookupError) as _e:
        logger.warning("[InjectCodeSnippets] 读取 %s 失败: %s", fp, _e)
        return None
def _inject_diag_code_snippets(result, skill_dir: str, cache=None) -> list:
    findings = getattr(result, "findings_list", None) or []
    if not findings:
        return findings
    _lines_cache: dict[str, list[str]] = {}
    for f in findings:
        _inject_one_snippet(f, skill_dir, _lines_cache, cache)
    return findings
def _inject_one_snippet(f: dict, skill_dir: str,
                        lines_cache: dict[str, list[str]],
                        cache) -> None:
    if not isinstance(f, dict):
        return
    if f.get("code_snippet"):
        return
    ref = _snapshot_ref(f)
    if ref is None:
        return
    fp, ln = ref
    lines = _memo_read_lines(fp, skill_dir, lines_cache, cache)
    if lines is not None and 0 < ln <= len(lines):
        f["code_snippet"] = lines[ln - 1].strip()
_EMPTY_SCAN_KEYS = (
    "file_count", "files_scanned", "scanned_files", "analyzed_files",
    "profile_count", "checked_files", "examined_files", "scanned_count",
)
def _apply_empty_scan_guard(result, cache) -> None:
    try:
        payload = getattr(result, "payload", None)
        if not isinstance(payload, dict):
            return
        declared = _declared_zero_scan_counts(payload)
        if declared is None:
            return
        project_files = _project_file_count(cache)
        if project_files <= 0:
            return
        _status = getattr(result, "status", "")
        if _status in ("fail", "error", "timeout", "skip"):
            return
        _mark_empty_scan(result, declared, project_files)
    except Exception as _guard_e:
        logger.warning("[Single] 空扫描哨兵异常(降级跳过): %s", _guard_e, exc_info=True)
def _project_file_count(cache) -> int:
    try:
        return cache.file_count if cache is not None else 0
    except Exception as _e:  # noqa: BLE001
        logger.warning("cache.file_count 读取失败(归零): %s", _e)
        return 0
def _declared_scan_counts(scope: dict) -> dict:
    declared: dict = {}
    for key in _EMPTY_SCAN_KEYS:
        value = scope.get(key)
        if is_real_number(value) and value >= 0:
            declared[key] = value
    return declared
def _iter_sub_scope_results(host: dict):
    for host_key in ("sub_results", "detector_results"):
        subs = host.get(host_key)
        if not isinstance(subs, dict):
            continue
        for entry in subs.values():
            if isinstance(entry, dict):
                yield entry.get("result")
def _unseen_dict_scope(scope, seen: set[int]) -> dict | None:
    if not isinstance(scope, dict) or id(scope) in seen:
        return None
    seen.add(id(scope))
    return scope
def _iter_scan_count_scopes(payload: dict):
    seen: set[int] = set()
    hosts: list[dict] = []
    for candidate in (payload, payload.get("payload")):
        scope = _unseen_dict_scope(candidate, seen)
        if scope is not None:
            hosts.append(scope)
            yield scope
    for host in hosts:
        results = (_unseen_dict_scope(item, seen)
                   for item in _iter_sub_scope_results(host))
        for result in filter(lambda scope: scope is not None, results):
            yield result
            sub_payload = _unseen_dict_scope(result.get("payload"), seen)
            if sub_payload is not None:
                yield sub_payload
def _positive_finite_scan_count(value: float) -> bool:
    if isinstance(value, float) and not math.isfinite(value):
        return False
    return value > 0
def _declared_zero_scan_counts(payload: dict) -> dict | None:
    declared: dict = {}
    nonzero = False
    for scope in _iter_scan_count_scopes(payload):
        for key, value in _declared_scan_counts(scope).items():
            declared.setdefault(key, value)
            if _positive_finite_scan_count(value):
                nonzero = True
    if not declared or nonzero:
        return None
    return declared
def _ensure_quality_flags(result) -> list:
    flags = getattr(result, "quality_flags", None)
    if flags is None:
        result.quality_flags = flags = []
    return flags
def _mark_quality_error(result, reason: str) -> None:
    result.status = "error"
    result.partial = True
    result.execution_mode = "error"
    previous = getattr(result, "degradation_context", None)
    context = dict(previous) if isinstance(previous, dict) else {}
    context.setdefault(
        "affected_rules",
        sorted(getattr(result, "rule_families_produced", None) or ()),
    )
    context["reason"] = reason
    result.degradation_context = context
def _mark_empty_scan(result, declared: dict, project_files: int) -> None:
    _mark_quality_error(result, "empty_scan")
    flags = _ensure_quality_flags(result)
    if "empty_scan" not in flags:
        flags.append("empty_scan")
    _detail = (f"[empty_scan] 方法声明扫描 {dict(declared)} 但项目含 "
               f"{project_files} 个 py 文件，扫描疑似失效，结果不可作为证据。")
    result.summary = _detail + " 原summary: " + str(getattr(result, "summary", ""))[:200]
    result.error = (str(getattr(result, "error", "")) + "\n" + _detail).strip()
    logger.warning("[Single] 空扫描哨兵触发: %s", _detail)
_FINDING_CONTAINER_TYPES = (list, tuple)
_FINDING_SCOPE_CHILD_KEYS = ("payload", "result", "raw_result")
_FINDING_SCOPE_COLLECTION_KEYS = (
    "sub_results", "detector_results", "results", "engines", "data",
)
def _iter_finding_scopes(root: dict, *, with_ancestors: bool = False):
    seen: set[int] = set()
    stack = [(root, frozenset())]
    while stack:
        scope, ancestors = stack.pop()
        if not isinstance(scope, dict) or id(scope) in seen:
            continue
        seen.add(id(scope))
        yield (scope, ancestors) if with_ancestors else scope
        next_ancestors = ancestors | {id(scope)}
        for key in _FINDING_SCOPE_CHILD_KEYS:
            child = scope.get(key)
            if isinstance(child, dict):
                stack.append((child, next_ancestors))
        for key in _FINDING_SCOPE_COLLECTION_KEYS:
            child = scope.get(key)
            if isinstance(child, dict):
                stack.extend((v, next_ancestors) for v in child.values()
                             if isinstance(v, dict))
            elif isinstance(child, _FINDING_CONTAINER_TYPES):
                stack.extend((v, next_ancestors) for v in child
                             if isinstance(v, dict))
def _removed_finding_items(original: list | tuple, kept: list) -> list:
    kept_ids = {id(item) for item in kept}
    return [item for item in original if id(item) not in kept_ids]
def _retired_rule_key(finding: Any) -> str:
    if not isinstance(finding, dict):
        return ""
    return str(finding.get("rule_id") or finding.get("rule_family")
               or finding.get("id") or "")
def _retired_filtered_list(
    value: list | tuple,
    seen_lists: dict[int, tuple[list | tuple, list, int]],
    seen_items: set[int],
    by_rule: dict[str, int],
) -> tuple[list, int]:
    value_id = id(value)
    prior = seen_lists.get(value_id)
    if prior is not None and prior[0] is value:
        return prior[1], prior[2]
    kept, _retired = filter_retired_findings(value)
    removed = _removed_finding_items(value, kept)
    seen_lists[value_id] = (value, kept, len(removed))
    for item in removed:
        if id(item) in seen_items:
            continue
        seen_items.add(id(item))
        _rid = _retired_rule_key(item)
        by_rule[_rid] = by_rule.get(_rid, 0) + 1
    return kept, len(removed)
def _filter_scope_findings(
    scope: dict,
    seen_lists: dict[int, tuple[list | tuple, list, int]],
    seen_items: set[int],
    by_rule: dict[str, int],
) -> tuple[bool, int, int]:
    has_primary = False
    primary_removed = 0
    total_removed = 0
    counted_lists: set[int] = set()
    for key in tuple(scope):
        if not is_finding_carrier_key(key):
            continue
        value = scope.get(key)
        if not isinstance(value, _FINDING_CONTAINER_TYPES):
            continue
        if key == "findings":
            has_primary = True
        kept, removed_count = _retired_filtered_list(
            value, seen_lists, seen_items, by_rule)
        if removed_count:
            scope[key] = tuple(kept) if isinstance(value, tuple) else kept
        value_id = id(value)
        if value_id not in counted_lists:
            counted_lists.add(value_id)
            total_removed += removed_count
        if key == "findings":
            primary_removed += removed_count
    return has_primary, primary_removed, total_removed
def _decrement_finding_counts(scope: dict, dropped: int) -> None:
    if dropped <= 0:
        return
    for key in ("findings_count", "merged_findings"):
        value = scope.get(key)
        if not is_real_number(value):
            continue
        if isinstance(value, float) and not value.is_integer():
            continue
        zero = 0.0 if isinstance(value, float) else 0
        scope[key] = max(zero, value - dropped)
def _sync_sub_result_finding_counts(payload: dict) -> None:
    for scope in _iter_finding_scopes(payload):
        for host_key in ("sub_results", "detector_results"):
            subs = scope.get(host_key)
            if not isinstance(subs, dict):
                continue
            for entry in subs.values():
                if not isinstance(entry, dict) or "findings_count" not in entry:
                    continue
                nested = entry.get("result")
                findings = nested.get("findings") if isinstance(nested, dict) else None
                if isinstance(findings, _FINDING_CONTAINER_TYPES):
                    entry["findings_count"] = len(findings)
def _apply_retired_rule_filter(result, method_id: str) -> None:
    try:
        payload = getattr(result, "payload", None)
        if not isinstance(payload, dict):
            return
        seen_lists: dict[int, tuple[list | tuple, list, int]] = {}
        seen_items: set[int] = set()
        by_rule: dict[str, int] = {}
        root_has_primary = False
        root_primary_removed = 0
        scoped_root_dropped = 0
        list_counted_scopes: dict[int, list[int]] = {}
        for scope, ancestors in _iter_finding_scopes(
                payload, with_ancestors=True):
            carrier_list_ids = {
                id(value)
                for key in tuple(scope)
                if is_finding_carrier_key(key)
                for value in (scope.get(key),)
                if isinstance(value, _FINDING_CONTAINER_TYPES)
            }
            primary_list_id = (
                id(scope["findings"])
                if isinstance(scope.get("findings"), _FINDING_CONTAINER_TYPES)
                else None)
            has_primary, primary, total = _filter_scope_findings(
                scope, seen_lists, seen_items, by_rule)
            if scope is payload:
                root_has_primary = has_primary
                root_primary_removed = primary
            elif total:
                _decrement_finding_counts(
                    scope, primary if has_primary else total)
            if root_has_primary:
                continue
            counted_list_ids = ({primary_list_id}
                                if has_primary else carrier_list_ids)
            for value_id in counted_list_ids:
                removed = seen_lists[value_id][2]
                if not removed:
                    continue
                counted_scopes = list_counted_scopes.setdefault(value_id, [])
                if any(scope_id in ancestors for scope_id in counted_scopes):
                    continue
                scoped_root_dropped += removed
                counted_scopes.append(id(scope))
        unique_removed = len(seen_items)
        if not unique_removed:
            return
        _sync_findings_list(result)
        _sync_sub_result_finding_counts(payload)
        payload["retired_findings"] = {
            "count": unique_removed,
            "by_rule": by_rule,
            "source": "diag_detectors_registry.RETIRED_RULE_IDS",
            "note": "退役规则：度量/设计气味/伪冲突不进缺陷通道",
        }
        root_dropped = (
            root_primary_removed if root_has_primary else scoped_root_dropped)
        _decrement_finding_counts(payload, root_dropped)
        stats = payload.get("stats")
        if isinstance(stats, dict):
            _decrement_finding_counts(stats, root_dropped)
        result.findings_count = max(
            0, safe_int(result.findings_count) - root_dropped)
        marker = f"[retired_filtered={unique_removed}]"
        summary = str(getattr(result, "summary", "") or "")
        if marker not in summary:
            result.summary = f"{summary} {marker}".strip()
        logger.info("[RetiredFilter] %s 剔除退役规则 finding %d 项: %s",
                    method_id, unique_removed, by_rule)
    except Exception as _rf_exc:
        logger.warning("[RetiredFilter] %s 退役过滤异常(降级跳过): %s",
                       method_id, _rf_exc, exc_info=True)
def _sync_findings_list(result) -> None:
    findings_list = getattr(result, "findings_list", None)
    if isinstance(findings_list, list):
        result.findings_list = filter_retired_findings(findings_list)[0]
def source_fingerprint_before(cfg, skill_dir: str) -> str | None:
    if cfg is not None and getattr(cfg, "domain", "") == "treatment":
        return None
    try:
        return compute_skill_source_hash(skill_dir)
    except Exception as _fp_exc:
        logger.warning("[TearGuard] 运行前源码指纹计算失败(守卫不启用): %s",
                       _fp_exc, exc_info=True)
        return None
_TEAR_FP_SUB_SCOPE = "F1"
def _source_fingerprint_scopes(payload) -> list[dict]:
    if not isinstance(payload, dict) or not payload:
        return []
    scopes: list[dict] = []
    seen: set[int] = set()
    def _push(candidate) -> None:
        if (isinstance(candidate, dict) and candidate
                and id(candidate) not in seen):
            seen.add(id(candidate))
            scopes.append(candidate)
    _push(sub_engine_payload(payload, ""))
    _push(payload)
    _push(sub_engine_payload(payload, _TEAR_FP_SUB_SCOPE))
    return scopes
def _source_tear_evidence(scope: dict) -> bool:
    fp = scope.get("source_fingerprint")
    return (isinstance(fp, dict)
            and signal_bool(fp.get("changed_during_run")))
def _changed_source_files(skill_dir: str, elapsed_s: float) -> list[str]:
    cutoff = time.time() - max(0.0, finite_float_or_zero(elapsed_s)) - 1.0
    changed: list[str] = []
    try:
        for rel, fpath in list_source_files(skill_dir):
            try:
                if os.path.getmtime(fpath) >= cutoff:
                    changed.append(rel)
            except OSError:
                continue
    except Exception:  # noqa: BLE001 — 定位失败不影响撕裂判定
        return changed
    return sorted(changed)
def _annotate_source_fingerprint(result, before_hash: str | None,
                                 skill_dir: str) -> None:
    if not before_hash:
        return
    try:
        after_hash = compute_skill_source_hash(skill_dir)
    except Exception as _fp_exc:
        logger.warning("[TearGuard] 运行后源码指纹计算失败(守卫不启用): %s",
                       _fp_exc, exc_info=True)
        return
    payload = getattr(result, "payload", None)
    if not isinstance(payload, dict):
        return
    scopes = _source_fingerprint_scopes(payload) or [payload]
    _torn = after_hash != before_hash
    _fingerprint = {
        "changed_during_run": _torn,
        "before": before_hash[:12],
        "after": after_hash[:12],
    }
    if _torn:
        _fingerprint["changed_files"] = _changed_source_files(
            skill_dir, getattr(result, "elapsed_s", 0.0))[:20]
    scopes[0]["source_fingerprint"] = _fingerprint
def _apply_source_tear_guard(result) -> None:
    try:
        scopes = _source_fingerprint_scopes(getattr(result, "payload", None))
        if not any(_source_tear_evidence(scope) for scope in scopes):
            return
        _mark_source_torn(result)
    except Exception as _tg_exc:
        logger.warning("[TearGuard] 源码撕裂守卫异常(降级跳过): %s", _tg_exc,
                       exc_info=True)
def _mark_source_torn(result) -> None:
    _mark_quality_error(result, "source_changed_during_run")
    flags = _ensure_quality_flags(result)
    if "source_changed_during_run" not in flags:
        flags.append("source_changed_during_run")
    marker = "[source_torn_during_run] "
    summary = str(getattr(result, "summary", "") or "")
    if not summary.startswith(marker):
        result.summary = marker + summary
    _changed: list[str] = []
    try:
        _payload = getattr(result, "payload", None)
        for _scope in _source_fingerprint_scopes(_payload):
            _fp = _scope.get("source_fingerprint") or {}
            _changed.extend(_fp.get("changed_files") or [])
    except Exception:  # noqa: BLE001 — 定位失败不阻断撕裂判定
        _changed = []
    logger.warning(
        "[TearGuard] %s 运行期源码被并发修改（changed_during_run），"
        "结果为撕裂态：findings/覆盖率混合新旧版本，采信前须复跑；"
        "变更文件: %s",
        getattr(result, "method_id", "?"),
        ", ".join(sorted(set(_changed))[:10])
        or "（mtime 反查不可用）")
def apply_result_quality_guards(result, method_id: str, skill_dir: str,
                                cache=None,
                                source_fp_before: str | None = None):
    _apply_retired_rule_filter(result, method_id)
    _apply_empty_scan_guard(result, cache)
    _annotate_source_fingerprint(result, source_fp_before, skill_dir)
    _apply_source_tear_guard(result)
    _ensure_degraded_evidence(result, method_id)
    try:
        _inject_diag_code_snippets(result, skill_dir, cache)
    except Exception as _inj_exc:
        logger.warning("[Single] code_snippet 注入失败(不阻断落盘): %s",
                       _inj_exc, exc_info=True)
    return result
def _finalize_single_method(result, method_id: str, skill_dir: str,
                            intermediate_dir: str, cache,
                            source_fp_before: str | None) -> None:
    apply_result_quality_guards(
        result, method_id, skill_dir, cache, source_fp_before)
    saved = save_intermediate(
        intermediate_dir, method_id, result, skill_dir=skill_dir)
    if saved:
        return
    reason = "intermediate_save_failed"
    _mark_quality_error(result, reason)
    flags = _ensure_quality_flags(result)
    if reason not in flags:
        flags.append(reason)
    detail = (f"[{reason}] 方法 {method_id} 中间结果落盘失败，"
              "本次结果不可供断点续传或依赖检查消费。")
    result.summary = detail + " 原summary: " + str(
        getattr(result, "summary", "") or "")[:200]
    result.error = (str(getattr(result, "error", "") or "") +
                    "\n" + detail).strip()
    _ensure_degraded_evidence(result, method_id)
    logger.error("[Single] %s %s", method_id, detail)

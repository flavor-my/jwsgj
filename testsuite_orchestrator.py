from __future__ import annotations

import gc
import hashlib
import logging
import os
import re
import sys
import threading
import time
from collections.abc import MutableMapping
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
from dataclasses import dataclass
from queue import Empty, Queue
from typing import Any, ClassVar

from jwsgj.diag_detector_findings import (
    apply_inline_suppressions,
    consolidate_findings,
    detector_entry,
    group_envelope,
    worst_sub_status,
)
from jwsgj.diag_testing_coverage import iter_py_files_under, iter_scoped_py
from jwsgj.diag_testing_metrics import (
    analyze_call_frequency,
    analyze_test_quality,
    resolve_e1_snapshot_source,
)
from jwsgj.diag_testing_source import FileCache, iter_test_py_files
from jwsgj.diag_types_defs import (
    TestMethodResult,
    result_status_bucket,
    result_to_dict,
)
from jwsgj.diag_types_normalize import (
    as_number,
    coerce_timeout,
    is_finite_num,
    safe_float,
)
from jwsgj.engine_e2_mutation import run_f2_mutation_targeted
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.runtime_paths import diag_intermediate_dir
from jwsgj.runtime_scope import (
    is_diagnosis_out_of_scope,
    is_test_source_basename,
    source_fingerprint,
)
from jwsgj.shared_cache import ensure_entry_warmed, fingerprint_freeze_window
from jwsgj.testsuite_coverage_map import ensure_supplemental_tests
from jwsgj.testsuite_registry import (
    METHOD_MODE_PARALLEL as _MODE_PARALLEL,
)
from jwsgj.testsuite_registry import (
    METHOD_MODE_SERIAL_CACHE as _MODE_SERIAL_CACHE,
)
from jwsgj.testsuite_registry import (
    METHOD_MODE_SERIAL_TIMEOUT as _MODE_SERIAL_TIMEOUT,
)
from jwsgj.testsuite_registry import (
    METHOD_NAMES_ZH,
    METHOD_SPECS,
    MethodImpls,
    assess_test_maturity,
    build_suite_diagnostic_summary,
    coerce_result_view,
    count_source_files,
)

__all__ = [
    "METHOD_NAMES_ZH",
    "TestingSuite",
    "run_engine_E",
    "run_f3_test_postprocessor",
    "run_test_suite",
]
logger = get_module_logger(__name__, __file__)
logger.addHandler(logging.NullHandler())
def _f3_production_py_count(skill_dir: str) -> int:
    return sum(1 for p in iter_scoped_py(skill_dir)
               if not is_diagnosis_out_of_scope(p))
def _f3_tests_py_count(skill_dir: str) -> int:
    return sum(1 for p in iter_test_py_files(skill_dir)
               if is_test_source_basename(os.path.basename(p)))
_F1_SNAPSHOT_GRACE_S = 2.0
_TS_MIN_LEN = 14
def _f3_finite_epoch(value) -> float | None:
    if not is_finite_num(value):
        return None
    epoch = float(value)
    return epoch if epoch > 0 else None
def _f3_latest_source_mtime(skill_dir: str) -> float:
    latest = 0.0
    for fpath in iter_scoped_py(skill_dir):
        try:
            latest = max(latest, os.path.getmtime(fpath))
        except OSError as e:
            logger.debug("文件状态探测失败（跳过）: %s", e)
            continue
    return latest
def _memory_payload(e1_result: dict | None) -> dict | None:
    if isinstance(e1_result, dict):
        payload = e1_result.get("payload")
        if isinstance(payload, dict):
            return payload
    return None
def _read_fingerprint_state(e1_fp: dict | None) -> tuple:
    f1_torn = None
    f1_torn_note = ""
    if e1_fp is None:
        return f1_torn, f1_torn_note
    fp = e1_fp.get("source_fingerprint")
    if not isinstance(fp, dict):
        return f1_torn, f1_torn_note
    f1_torn = fp.get("changed_during_run")
    _torn_n = fp.get("torn_findings")
    if (isinstance(_torn_n, int) and not isinstance(_torn_n, bool)
            and _torn_n > 0):
        f1_torn_note = (f"（{_torn_n} 条 test_failure/"
                        f"test_error 已标注待复扫）")
    return f1_torn, f1_torn_note
def _resolve_f1_epoch(ts_raw: str, epoch_from_memory: bool,
                       e1_done_epoch: float | None) -> float | None:
    if epoch_from_memory:
        return _f3_finite_epoch(e1_done_epoch)
    if not isinstance(ts_raw, str) or len(ts_raw) < _TS_MIN_LEN:
        return None
    try:
        return time.mktime(
            time.strptime(ts_raw[:_TS_MIN_LEN], "%Y%m%d%H%M%S"))
    except (ValueError, OverflowError, OSError) as _e:
        log_swallowed(__name__, _e, context='_resolve_f1_epoch:ValueError')
        return None
def _f3_finding(rule_id: str, severity: str, confidence: float,
                   message: str, pattern_name: str) -> dict:
    return {
        "rule_id": rule_id,
        "severity": severity,
        "confidence": confidence,
        "message": message,
        "file": "",
        "line": 0,
        "source": "F3",
        "pattern_name": pattern_name,
    }
def _f3_f1_snapshot_findings(intermediate_dir: str, skill_dir: str,
                             e1_payload: dict | None = None,
                             e1_done_epoch: float | None = None) -> list[dict]:
    resolved = resolve_e1_snapshot_source(intermediate_dir or "", e1_payload)
    if resolved is None:
        return []
    payload, ts_raw, epoch_from_memory = resolved
    findings = _torn_guard_findings(payload)
    findings.extend(
        _stale_guard_findings(ts_raw, epoch_from_memory, skill_dir,
                              e1_done_epoch))
    return findings
def _torn_guard_findings(e1_fp: dict | None) -> list[dict]:
    f1_torn, f1_torn_note = _read_fingerprint_state(e1_fp)
    if f1_torn is None or not isinstance(f1_torn, bool):
        logger.warning(
            "[F3] E1 快照缺少可用的 source_fingerprint.changed_during_run"
            "（字段缺失或非 bool 形态漂移），撕裂守卫无法评估"
            "（schema 漂移或 E1 产物异常），显式降级声明")
        return [_f3_finding(
            "F3-F1-CONCURRENT-GUARD-DISABLED", "P3", 0.9,
            "E1 快照 source_fingerprint.changed_during_run"
            " 缺失或形态异常（非 bool，schema 漂移或"
            " E1 产物异常），撕裂守卫无法评估快照一致性，"
            "撕裂/混合态不可检出，需检查 E1 payload 结构后重跑",
            "f1_guard_disabled_torn")]
    if f1_torn is True:
        return [_f3_finding(
            "F3-F1-CONCURRENT", "P2", 1.0,
            "E1 快照为撕裂混合态：E1 运行期间源码被并发修改"
            "（payload.source_fingerprint.changed_during_run=true）"
            + f1_torn_note +
            "，pytest 按导入时点定格新旧版本，覆盖率数据不可信，"
            "需在源码落定后重跑 E1+E3",
            "f1_snapshot_torn")]
    return []
def _stale_guard_findings(ts_raw: str, epoch_from_memory: bool, skill_dir: str,
                          e1_done_epoch: float | None) -> list[dict]:
    if not isinstance(ts_raw, str):
        ts_raw = ""
    f1_epoch = _resolve_f1_epoch(ts_raw, epoch_from_memory, e1_done_epoch)
    if f1_epoch is None:
        logger.warning(
            "[F3] E1 快照缺少可解析的快照时刻（内存通道 e1_done_epoch="
            "%r，磁盘通道 _report_timestamp=%r），过期守卫无法评估，"
            "显式降级声明", e1_done_epoch, ts_raw[:20])
        return [_f3_finding(
            "F3-F1-STALE-GUARD-DISABLED", "P3", 0.9,
            "E1 快照缺少可解析的快照时刻，快照过期"
            "守卫无法评估（schema 漂移或产物异常），落盘后"
            "源码变更不可检出，需检查 E1 产物结构后重跑",
            "f1_guard_disabled_stale")]
    latest = _f3_latest_source_mtime(skill_dir)
    if latest > f1_epoch + _F1_SNAPSHOT_GRACE_S:
        _t = time.strftime("%H:%M:%S", time.localtime(latest))
        return [_f3_finding(
            "F3-F1-STALE-SNAPSHOT", "P2", 1.0,
            "E1 覆盖率快照已过期：E1 落盘后源码又有修改"
            f"（最新源码 mtime {_t} 晚于 E1 快照时刻），"
            "覆盖率对当前源码不再成立，需重跑 E1+E3",
            "f1_snapshot_stale")]
    return []
_COMPONENT_ERROR_DETAIL_MAX = 200
def _component_error(exc: BaseException) -> dict:
    return {"error": str(exc)[:_COMPONENT_ERROR_DETAIL_MAX]}
def _run_t17_heatmap(skill_dir: str, intermediate_dir: str | None,
                     cache, e1_payload: dict | None) -> tuple[list, dict, bool]:
    try:
        h_findings, heatmap_part = analyze_call_frequency(
            skill_dir, intermediate_dir, cache, e1_payload)
        if (heatmap_part.get("total_functions", 0) == 0
                and _f3_production_py_count(skill_dir) > 0):
            h_findings.append(_f3_finding(
                'F3-T17-EMPTY-COVERAGE', 'P2', 1.0,
                'T17 调用频率热力图输入为空（total_functions=0）但项目存'
                '在生产 py 文件，F1 覆盖率数据未到达 T17，函数覆盖盲区信号全部丢失'
                '，需检查 F1 payload.coverage 链路后重跑 F1+F3',
                'empty_coverage_input'))
        return h_findings, heatmap_part, False
    except Exception as e:
        logger.warning("[F3] 调用频率热力图失败: %s", e)
        return [], _component_error(e), True
def _run_t18_quality(skill_dir: str, cache) -> tuple[list, dict, bool]:
    try:
        t18_findings, quality_part = analyze_test_quality(skill_dir, cache)
        if (quality_part.get("metrics", {}).get("total_test_functions", 0) == 0
                and _f3_tests_py_count(skill_dir) > 0):
            t18_findings.append(_f3_finding(
                'F3-T18-EMPTY-TESTS', 'P2', 1.0,
                'T18 测试质量评估输入为空（total_test_functions=0）'
                '但测试目录存在 py 文件，测试文件解析疑似全部失败，测试质量信号全部丢失，'
                '需检查测试目录与缓存链路后重跑 F3',
                'empty_tests_input'))
        return t18_findings, quality_part, False
    except Exception as e:
        logger.warning("[F3] 测试质量评估失败: %s", e)
        return [], _component_error(e), True
@dataclass(slots=True)
class _F3RunState:
    findings: list
    payload_parts: dict
def _f3_run_components_guarded(skill_dir: str, intermediate_dir: str,
                               cache, e1_payload,
                               state: _F3RunState) -> bool:
    gc_was = gc.isenabled()
    if gc_was:
        gc.disable()
    try:
        with fingerprint_freeze_window(cache, "F3-snap"):
            h_findings, heatmap_part, _t17_failed = _run_t17_heatmap(
                skill_dir, intermediate_dir, cache, e1_payload)
            state.findings.extend(h_findings)
            state.payload_parts["heatmap"] = heatmap_part
            t18_findings, quality_part, _t18_failed = _run_t18_quality(
                skill_dir, cache)
            state.findings.extend(t18_findings)
            state.payload_parts["test_quality"] = quality_part
            return _t17_failed or _t18_failed
    finally:
        if gc_was:
            gc.enable()
def _f3_fingerprint_guard(skill_dir: str, fp_start: tuple,
                          state: _F3RunState) -> bool:
    fp_end = source_fingerprint(skill_dir)
    source_changed = fp_start != fp_end
    state.payload_parts["source_fingerprint"] = {
        "start": {"files": fp_start[0], "digest": fp_start[1]},
        "end": {"files": fp_end[0], "digest": fp_end[1]},
        "changed_during_run": source_changed,
    }
    if source_changed:
        state.findings.append(_f3_finding(
            'F3-CONCURRENT-MOD', 'P2', 1.0,
            "F3 运行期间源码被并发修改"
            f"（文件数 {fp_start[0]}→{fp_end[0]}，"
            f"指纹 {fp_start[1][:8]}→{fp_end[1][:8]}），"
            "结果为撕裂混合态，需在本轮修改落定后重跑 F3 复核",
            'concurrent_modification'))
    return source_changed
_F3_GUARD_KEYS = ("source_fingerprint", "f1_snapshot_check")
def _f3_error_keys(payload_parts: dict) -> list[str]:
    return [k for k, v in payload_parts.items()
            if isinstance(v, dict) and "error" in v]
def _f3_component_status(payload_parts: dict, key: str) -> str:
    part = payload_parts.get(key)
    return "error" if isinstance(part, dict) and "error" in part else "ok"
def _f3_has_disk_source(intermediate_dir: str) -> bool:
    return bool(intermediate_dir) and os.path.isdir(intermediate_dir)
def _f3_resolve_status(payload_parts: dict, component_failed: bool,
                        n: int) -> str:
    if not component_failed:
        return "pass" if n == 0 else "warn"
    _comp_keys = [k for k in payload_parts if k not in _F3_GUARD_KEYS]
    return ("error" if len(_f3_error_keys(payload_parts))
            == len(_comp_keys) else "warn")
def _f3_build_summary(n: int, payload_parts: dict,
                      component_failed: bool) -> str:
    if not component_failed:
        return f"测试后处理: 热力图+质量评估, 共{n}个发现"
    return (f"测试后处理: 热力图+质量评估, 共{n}个发现"
            + " [子组件失败: " + ",".join(_f3_error_keys(payload_parts))
            + "]")
_F3_AI_EXECUTION = {
    "next_action": "review_and_execute_test_quality_fixes",
    "instruction": (
        "逐项审核 findings 中的测试质量问题（无断言/宽泛断言/冒烟"
        "测试）；确认后直接修改对应测试文件补齐具体断言，改后跑该"
        "测试文件确认通过；不成立的发现按证据驳回"
    ),
}
def _f3_skip_result() -> dict:
    logger.info("[F3] 测试后处理跳过: 无中间结果目录且无 E1 内存直传")
    return {"status": "skip", "findings_count": 0,
            "summary": "测试后处理跳过(无中间结果目录)",
            "findings": [], "payload": {"skipped": True},
            "ai_execution": dict(_F3_AI_EXECUTION)}
def _f3_collect_snapshot_gate(intermediate_dir: str, skill_dir: str,
                              e1_payload: dict | None,
                              e1_done_epoch: float | None,
                              state: _F3RunState) -> None:
    snap_findings = _f3_f1_snapshot_findings(
        intermediate_dir or "", skill_dir,
        e1_payload=e1_payload, e1_done_epoch=e1_done_epoch)
    state.findings.extend(snap_findings)
    state.payload_parts["f1_snapshot_check"] = {
        "findings": len(snap_findings),
        "rule_ids": [f.get("rule_id") for f in snap_findings],
    }
def run_f3_test_postprocessor(skill_dir: str, cache=None,
                               e1_result: dict | None = None,
                               e1_done_epoch: float | None = None) -> dict:
    cache = ensure_entry_warmed(skill_dir, cache, who="F3 测试后处理")
    intermediate_dir = diag_intermediate_dir(
        getattr(cache, "output_dir", "") or "")
    if not _f3_has_disk_source(intermediate_dir) and e1_result is None:
        return _f3_skip_result()
    _e1_payload = _memory_payload(e1_result)
    state = _F3RunState(findings=[], payload_parts={})
    _f3_collect_snapshot_gate(
        intermediate_dir, skill_dir, _e1_payload, e1_done_epoch, state)
    fp_start = source_fingerprint(skill_dir)
    component_failed = _f3_run_components_guarded(
        skill_dir, intermediate_dir, cache, _e1_payload, state)
    _f3_fingerprint_guard(skill_dir, fp_start, state)
    findings = state.findings
    payload_parts = state.payload_parts
    n = len(findings)
    status = _f3_resolve_status(payload_parts, component_failed, n)
    if component_failed:
        payload_parts["component_failed"] = True
    logger.info(
        "[F3] 测试后处理完成: status=%s, findings=%d, heatmap=%s, quality=%s",
        status, n,
        _f3_component_status(payload_parts, "heatmap"),
        _f3_component_status(payload_parts, "test_quality"))
    return {
        "status": status,
        "findings_count": n,
        "summary": _f3_build_summary(n, payload_parts, component_failed),
        "findings": findings,
        "payload": payload_parts,
        "ai_execution": dict(_F3_AI_EXECUTION),
    }
try:
    import psutil
except ImportError as _imp_err:
    psutil = None
    logging.getLogger(__name__).debug(
        "[testsuite_runner] 导入失败，方法级孤儿回收降级空操作: %s",
        _imp_err)
_PYTHON_PROCESS_NAME_RE = re.compile(
    r"(?:python(?:w)?(?:[-.]?\d+(?:\.\d+)*)?(?:[_-]d)?"
    r"|pytest(?:[-.]?\d+(?:\.\d+)*)?)(?:\.exe)?")
def _is_python_process_name(name: Any) -> bool:
    if not isinstance(name, str):
        return False
    return _PYTHON_PROCESS_NAME_RE.fullmatch(name.strip().lower()) is not None
def _snapshot_python_pids() -> set | None:
    if psutil is None:
        return None
    try:
        return {p.info['pid'] for p in psutil.process_iter(['pid', 'name'])
                if _is_python_process_name(p.info.get('name'))}
    except Exception as e:
        logger.warning("[orchestrator] 快照Python进程失败,本轮放弃孤儿清理: %s", e)
        return None
def _snapshot_protected_pids() -> set | None:
    pids = _snapshot_python_pids()
    if pids is None or psutil is None:
        return pids
    try:
        pids.update(child.pid
                    for child in psutil.Process().children(recursive=True))
    except (OSError, RuntimeError, psutil.Error):
        logger.warning(
            "[orchestrator] 既有子进程快照失败,本轮放弃孤儿清理(防误杀既有子进程)")
        return None
    return pids
def _kill_orphan_child(child) -> None:
    try:
        child.kill()
        child.wait(timeout=3)
    except psutil.Error:
        logger.debug("_kill_orphan_child: suppressed psutil error", exc_info=True)
def _cleanup_orphan_pythons(before_pids: set | None):
    if psutil is None:
        return
    if before_pids is None:
        logger.warning("[orchestrator] PID快照不可用,跳过孤儿清理(防误杀既有子进程)")
        return
    try:
        children = psutil.Process().children(recursive=True)
    except (OSError, RuntimeError, psutil.Error):
        logger.debug(
            "_cleanup_orphan_pythons: suppressed OSError/RuntimeError/psutil error",
            exc_info=True)
        return
    for child in children:
        if child.pid in before_pids:
            continue
        try:
            child_name = child.name()
        except (OSError, RuntimeError, psutil.Error):
            logger.debug(
                "_cleanup_orphan_pythons: 子进程名读取失败，跳过防误杀",
                exc_info=True)
            continue
        if _is_python_process_name(child_name):
            _kill_orphan_child(child)
_DEFAULT_TIMEOUT_FALLBACK_S = 120.0
_active_method_lock = threading.Lock()
_active_method_workers: dict[int, int] = {}
@contextmanager
def _active_method_scope():
    worker_id = threading.get_ident()
    with _active_method_lock:
        _active_method_workers[worker_id] = (
            _active_method_workers.get(worker_id, 0) + 1)
    try:
        yield
    finally:
        with _active_method_lock:
            remaining = _active_method_workers.get(worker_id, 1) - 1
            if remaining:
                _active_method_workers[worker_id] = remaining
            else:
                _active_method_workers.pop(worker_id, None)
def _other_methods_running(current_worker_id: int | None) -> bool:
    with _active_method_lock:
        return any(worker_id != current_worker_id
                   for worker_id in _active_method_workers)
def _derive_overall_status(run_results: list, warn_count: int,
                           fail_count: int, skip_count: int,
                           error_count: int) -> str:
    if not run_results:
        return "skip"
    if fail_count > 0:
        return ("fail" if fail_count >= _VERDICT_FAIL_MIN_COUNT
                else "warn")
    if warn_count > 0 or error_count > 0:
        return "warn"
    if skip_count:
        return "skip" if skip_count == len(run_results) else "warn"
    return "pass"
def _summarize_results(run_results: list) -> tuple[int, dict[str, int]]:
    total_score = 0
    counts = {"pass": 0, "warn": 0, "fail": 0, "skip": 0, "error": 0}
    for r in run_results:
        total_score += as_number(getattr(r, 'score', None))
        counts[result_status_bucket(getattr(r, 'status', None))] += 1
    return total_score, counts
_VERDICT_FAIL_MIN_COUNT = 3
_MAX_PARALLEL_METHODS = 2
def _invoke_method(func, method_id: str, skill_dir: str, cache,
                   report: dict | None) -> Any:
    if method_id == "regression_test":
        return func(
            skill_dir, report=report if report is not None else {},
            _cache=cache)
    return func(skill_dir, _cache=cache)
def _resolve_method_timeout(method_id: str, cache, timeouts: dict[str, float],
                            default_timeout: float | None,
                            tiers: tuple[tuple[int, float], ...]) -> float:
    default_timeout = coerce_timeout(
        default_timeout, _DEFAULT_TIMEOUT_FALLBACK_S, allow_zero=True)
    base = coerce_timeout(
        timeouts.get(method_id, default_timeout), default_timeout,
        allow_zero=True)
    if base <= 0:
        return 0.0
    file_count = len(cache.entries) if cache and cache.entries else 0
    for tier_files, tier_scale in tiers:
        if file_count > tier_files:
            return base * tier_scale
    return base
def _normalize_method_ids(methods, registry) -> list[str]:
    if methods is None:
        return list(registry.keys())
    if isinstance(methods, (bytes, bytearray)):
        methods = methods.decode("utf-8", "replace")
    if isinstance(methods, str) or not hasattr(methods, "__iter__"):
        raw = [methods]
    elif isinstance(methods, (set, frozenset)):
        raw = sorted(methods, key=str)
    else:
        raw = list(methods)
    raw = [mid for mid in raw if mid is not None]
    return list(dict.fromkeys(mid if isinstance(mid, str) else str(mid)
                              for mid in raw))
def _execute_with_timeout(method_id: str, method_name: str, func, cache,
                          report, timeout: float,
                          skill_dir: str) -> TestMethodResult:
    result_box: Queue = Queue()
    if timeout == 0:
        return TestMethodResult.skipped(
            method_id, method_name, "timeout=0 (跳过)", "超时值为 0，跳过")
    worker_state: dict[str, int] = {}
    def _pop_result():
        succeeded, payload = result_box.get_nowait()
        if not succeeded:
            raise payload
        return payload
    def _worker():
        # 测试方法 worker 同样不得继承进程级 coverage tracer：超时放弃后
        # 残留的 daemon 线程会持锁阻塞同进程其余 worker（见 diag_method_invoke
        # 中同一处的根因说明）。
        sys.settrace(None)
        worker_state["id"] = threading.get_ident()
        with _active_method_scope():
            try:
                result = _invoke_method(
                    func, method_id, skill_dir, cache, report)
            except Exception as e:
                logger.warning(
                    "方法执行异常，转交调用方按既有契约收口: %s", e,
                    exc_info=True)
                result_box.put((False, e))
                return
            result_box.put((True, result))
    _before_pids = _snapshot_protected_pids()
    _quiesce_coverage_tracing()
    worker = threading.Thread(target=_worker, daemon=True)
    worker.start()
    worker.join(timeout=timeout)
    _timed_out = worker.is_alive()
    if _timed_out:
        try:
            return _pop_result()
        except Empty as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc, context='_execute_with_timeout:Empty')
        _reap_orphans_after_timeout(
            method_name, timeout, _before_pids, worker_state.get("id"))
        return TestMethodResult.skipped(
            method_id, method_name, f"timeout after {timeout}s",
            f"超时跳过 ({timeout}s) — 不死磕，直接跳过继续后续方法")
    try:
        return _pop_result()
    except Empty:
        logger.warning("worker 结束但结果队列为空（BaseException 击穿信封）")
        return TestMethodResult.skipped(
            method_id, method_name, "worker died without result",
            "执行线程异常终止，跳过")
def _is_coverage_tracer(tracer) -> bool:
    """判断 tracer 是否由 coverage 安装（见 diag_method_invoke 同名函数）。"""
    if not tracer:
        return False
    owner = getattr(tracer, "__self__", None) or tracer
    module = getattr(type(owner), "__module__", "") or ""
    return module.split(".", 1)[0] == "coverage"
def _quiesce_coverage_tracing() -> None:
    """清除残留的进程级 coverage tracer（见 diag_method_invoke 同名函数）。"""
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
def _reap_orphans_after_timeout(method_name: str, timeout: float,
                                before_pids: set | None,
                                current_worker_id: int | None) -> None:
    if _other_methods_running(current_worker_id):
        logger.warning(
            "[orchestrator] %s 超时(%ss)，存在并行运行的方法，"
            "跳过孤儿进程清理防误杀", method_name, timeout)
        return
    _cleanup_orphan_pythons(before_pids)
class TestingSuite:
    __test__ = False
    METHOD_REGISTRY: ClassVar[MutableMapping[str, Any]] = MethodImpls(
        METHOD_SPECS)
    METHOD_NAMES_ZH: ClassVar[dict[str, str]] = METHOD_NAMES_ZH
    def __init__(self, skill_dir: str, ctx=None):
        self.skill_dir = (os.fspath(skill_dir)
                          if isinstance(skill_dir, os.PathLike) else skill_dir)
        self._ctx = ctx
        self.results: dict[str, TestMethodResult] = {}
        self._cache: FileCache | None = None
    def _skill_dir_valid(self) -> bool:
        return isinstance(self.skill_dir, str) and os.path.isdir(self.skill_dir)
    def _get_cache(self) -> FileCache:
        if self._cache is None:
            self._cache = FileCache(self.skill_dir, ctx=self._ctx)
            self._cache.load()
        return self._cache
    _METHOD_TIMEOUTS: ClassVar[dict[str, float]] = {
        mid: spec.timeout for mid, spec in METHOD_SPECS.items()
        if spec.timeout is not None}
    _TIMEOUT_SCALE_TIERS: ClassVar[tuple[tuple[int, float], ...]] = (
        (200, 4.0),
        (100, 3.0),
        (30, 2.0),
    )
    _READONLY_METHODS: ClassVar[frozenset] = frozenset(
        mid for mid, spec in METHOD_SPECS.items()
        if spec.mode == _MODE_PARALLEL)
    _WRITES_CACHE_METHODS: ClassVar[frozenset] = frozenset(
        mid for mid, spec in METHOD_SPECS.items()
        if spec.mode == _MODE_SERIAL_CACHE)
    _TIMEOUT_SERIAL_METHODS: ClassVar[frozenset] = frozenset(
        mid for mid, spec in METHOD_SPECS.items()
        if spec.mode == _MODE_SERIAL_TIMEOUT)
    def _run_method_with_timeout(
            self, method_id: str, func, cache, report) -> TestMethodResult:
        timeout = _resolve_method_timeout(
            method_id, cache, self._METHOD_TIMEOUTS,
            _DEFAULT_TIMEOUT_FALLBACK_S, self._TIMEOUT_SCALE_TIERS)
        return _execute_with_timeout(
            method_id, self.METHOD_NAMES_ZH.get(method_id, method_id),
            func, cache, report, timeout, self.skill_dir)
    def _canonicalize_results(self, ordered_ids: list[str]) -> None:
        ordered: dict[str, TestMethodResult] = {
            mid: self.results[mid] for mid in ordered_ids if mid in self.results}
        for mid, result in self.results.items():
            if mid not in ordered:
                ordered[mid] = result
        self.results = ordered
    def run_all(self, report: dict | None = None,
                methods: list[str] | None = None) -> dict:
        method_ids = _normalize_method_ids(methods, self.METHOD_REGISTRY)
        cache = self._get_cache() if self._skill_dir_valid() else None
        suite_start = time.perf_counter()
        self._run_phases(method_ids, cache, report)
        _run_ids = [mid for mid in method_ids if mid in self.results]
        self._canonicalize_results(_run_ids)
        _run_results = [self.results[mid] for mid in _run_ids]
        total_score, counts = _summarize_results(_run_results)
        pass_count = counts["pass"]
        warn_count = counts["warn"]
        fail_count = counts["fail"]
        skip_count = counts["skip"]
        error_count = counts["error"]
        suite_elapsed = (time.perf_counter() - suite_start) * 1000
        overall_score = (round(total_score / max(len(_run_results), 1))
                         if _run_results else 0)
        overall_status = _derive_overall_status(_run_results, warn_count,
                                                fail_count, skip_count,
                                                error_count)
        return {
            "overall_score": overall_score,
            "overall_status": overall_status,
            "total_methods": len(_run_ids),
            "passed": pass_count,
            "warned": warn_count,
            "failed": fail_count,
            "skipped": skip_count,
            "errored": error_count,
            "total_elapsed_ms": round(suite_elapsed, 2),
            "results": {mid: self.results[mid].to_dict() for mid in _run_ids},
        }
    def _run_one_method(self, mid: str, cache, report) -> TestMethodResult:
        try:
            func = self.METHOD_REGISTRY[mid]
        except KeyError:
            func = None
        except Exception as e:
            log_swallowed(__name__, e, context='TestingSuite._run_one:resolve')
            result = TestMethodResult.from_execution_error(
                e, mid, self.METHOD_NAMES_ZH.get(mid, mid))
            result.error = f"方法实现解析失败: {e}"
            result.summary = (
                f"方法实现解析失败: {type(e).__name__}: {str(e)[:200]}")
            self.results[mid] = result
            return result
        if func is None:
            result = TestMethodResult(
                method_name=mid, method_id=mid,
                status="skip", score=0,
                error=f"未知方法: {mid}",
            )
            self.results[mid] = result
            return result
        if not self._skill_dir_valid():
            result = TestMethodResult.invalid_input(
                self.skill_dir, self.METHOD_NAMES_ZH.get(mid, mid), mid,
                "测试", time.perf_counter())
            self.results[mid] = result
            return result
        try:
            result = self._run_method_with_timeout(mid, func, cache, report)
        except Exception as e:
            log_swallowed(__name__, e, context='TestingSuite.run_all._run_one:Exc')
            result = TestMethodResult.from_execution_error(
                e, mid, self.METHOD_NAMES_ZH.get(mid, mid))
        if not isinstance(result, TestMethodResult):
            logger.warning("%s 返回值非 TestMethodResult（%s），降级 skip",
                           mid, type(result).__name__)
            result = TestMethodResult(
                method_name=self.METHOD_NAMES_ZH.get(mid, mid),
                method_id=mid, status="skip", score=0,
                error=f"返回值非 TestMethodResult（{type(result).__name__}）",
                summary=f"返回值形态违约: {type(result).__name__}",
            )
        self.results[mid] = result
        return result
    def _print_one_method(self, mid: str) -> None:
        result = self.results[mid]
        name = self.METHOD_NAMES_ZH.get(mid, mid)
        icon = {"pass": "✓", "warn": "⚠", "fail": "✗", "skip": "−",
                "error": "!"}[result_status_bucket(
                    getattr(result, "status", None))]
        logger.info("  [%s] %s: %s (%.0fms)", icon, name, result.summary,
                    as_number(getattr(result, "elapsed_ms", None)))
    def _run_phases(self, method_ids: list[str], cache, report) -> None:
        groups = (
            (self._run_parallel_group, self._READONLY_METHODS),
            (self._run_serial_group, self._WRITES_CACHE_METHODS),
            (self._run_serial_group, self._TIMEOUT_SERIAL_METHODS),
        )
        for run_group, members in groups:
            run_group([m for m in method_ids if m in members], cache, report)
        grouped = (self._READONLY_METHODS | self._WRITES_CACHE_METHODS
                   | self._TIMEOUT_SERIAL_METHODS)
        self._run_serial_group(
            [m for m in method_ids if m not in grouped], cache, report)
    def _run_parallel_group(self, method_ids: list[str], cache, report) -> None:
        if not method_ids:
            return
        with ThreadPoolExecutor(max_workers=_MAX_PARALLEL_METHODS) as pool:
            futures = {pool.submit(self._run_one_method, mid, cache, report): mid
                       for mid in method_ids}
            for f in as_completed(futures):
                f.result()
                self._print_one_method(futures[f])
    def _run_serial_group(self, method_ids: list[str], cache, report) -> None:
        for mid in method_ids:
            self._run_one_method(mid, cache, report)
            self._print_one_method(mid)
    def run_method(self, method_id: str,
                   report: dict | None = None) -> TestMethodResult:
        if not self._skill_dir_valid():
            return self._run_one_method(method_id, None, report)
        return self._run_one_method(method_id, self._get_cache(), report)
def _f1_file_digests(skill_dir: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for fpath in iter_py_files_under(skill_dir):
        rel = os.path.relpath(fpath, skill_dir).replace("\\", "/")
        try:
            with open(fpath, "rb") as fh:
                out[rel] = hashlib.md5(
                    fh.read(), usedforsecurity=False).hexdigest()
        except OSError as e:
            logger.debug("文件读取失败（跳过）: %s: %s", fpath, e)
            continue
    return out
_POLICY_EXCLUDE_METHODS = frozenset({"mutation_test"})
_POLICY_EXCLUDE_TYPES = frozenset({
    "string_concat_in_loop", "generator_io", "format_in_loop",
    "CONTRACT-MISSING-PARAM-ANNOT", "CONTRACT-MISSING-RETURN-ANNOT",
    "api_removed_functions", "api_removed_classes", "api_added_functions",
    "signature_change", "behavior_change",
})
_POLICY_HOTSPOT_CC_MIN = 50
_DIFF_DETAIL_LIMIT = 50
def _cc_numeric(finding: dict) -> float:
    return safe_float(finding.get("cc"), None) or 0.0
def _policy_drop_reason(f: dict, mid: str) -> str | None:
    ftype = f.get("type") or ""
    if mid in _POLICY_EXCLUDE_METHODS:
        return f"excluded_method:{mid}"
    if ftype in _POLICY_EXCLUDE_TYPES:
        return f"excluded_type:{ftype}"
    if (mid == "complexity" and "cc" in f
            and _cc_numeric(f) < _POLICY_HOTSPOT_CC_MIN):
        return "hotspot_below_threshold:complexity"
    if (mid == "performance" and ftype != "loop_io"
            and "cc" in f and _cc_numeric(f) < _POLICY_HOTSPOT_CC_MIN):
        return "hotspot_below_threshold:performance"
    return None
def _apply_default_output_policy(
        findings: list, method_id: str | None = None) -> tuple[list, dict]:
    kept: list = []
    suppressed: dict[str, int] = {}
    for f in findings:
        if not isinstance(f, dict):
            kept.append(f)
            continue
        _mid = method_id if method_id is not None else f.get("_test_method", "")
        _reason = _policy_drop_reason(f, _mid)
        if _reason is None:
            kept.append(f)
        else:
            suppressed[_reason] = suppressed.get(_reason, 0) + 1
    return kept, suppressed
_METHOD_EXECUTION_ORDER = (
    "smoke_test",
    "static_analysis",
    "contract_test",
    "security_test",
    "unit_test",
    "coverage",
    "sca",
    "complexity",
    "architecture",
    "regression_test",
    "integration_test",
    "e2e_test",
    "performance",
    "compatibility",
    "fuzz_test",
    "stress_test",
    "mutation_test",
)
def _method_execution_order() -> list[str]:
    preferred = [mid for mid in _METHOD_EXECUTION_ORDER if mid in METHOD_SPECS]
    return [*preferred,
            *(mid for mid in METHOD_SPECS
              if mid not in _METHOD_EXECUTION_ORDER)]
TEST_METHOD_IDS = _method_execution_order()
def _lift_channel_metrics(method_id: str, result_dict: dict,
                          coverage_payload: dict) -> None:
    if method_id == "coverage":
        cov_metrics = result_dict.get("metrics", {})
        if isinstance(cov_metrics, dict) and cov_metrics:
            coverage_payload["coverage"].update(cov_metrics)
    if method_id == "regression_test":
        reg_metrics = result_dict.get("metrics", {})
        if isinstance(reg_metrics, dict) and reg_metrics:
            coverage_payload["regression"] = reg_metrics
def _mark_findings_source(findings: list, method_id: str,
                          all_findings: list) -> None:
    if not isinstance(findings, (list, tuple)):
        return
    for f in findings:
        if isinstance(f, dict):
            f["source"] = "TEST_SUITE"
            f["_test_method"] = method_id
        all_findings.append(f)
def _sub_result_entry(result_dict: dict, elapsed_ms: float) -> dict:
    findings = result_dict.get("findings")
    findings_count = len(findings) if isinstance(findings, (list, tuple)) else 0
    entry = {
        "status": result_dict.get("status", "unknown"),
        "findings_count": findings_count,
        "elapsed_ms": round(elapsed_ms, 1),
        "summary": str(result_dict.get("summary", ""))[:200],
    }
    _mt = result_dict.get("metrics")
    if isinstance(_mt, dict):
        for _mk in ("pytest_status", "tests_run"):
            if _mk in _mt:
                entry[_mk] = _mt[_mk]
    return entry
def _method_error_entry(e: Exception, elapsed_ms: float) -> dict:
    return {
        "status": "error",
        "findings_count": 0,
        "elapsed_ms": round(elapsed_ms, 1),
        "error": str(e)[:200],
    }
def _policy_skipped_entry() -> dict:
    return {
        "status": "skipped_by_policy",
        "findings_count": 0,
        "elapsed_ms": 0.0,
    }
def _run_test_method(suite: TestingSuite, method_id: str, skill_dir: str,
                     report: dict | None, test_cache: FileCache,
                     all_findings: list,
                     coverage_payload: dict) -> tuple[dict | None, float]:
    try:
        func = suite.METHOD_REGISTRY.get(method_id)
    except Exception as e:
        logger.warning("[TestSuite] 方法 %s 实现解析失败: %s", method_id, e)
        return _method_error_entry(e, 0.0), 0.0
    if func is None:
        logger.warning("[TestSuite] 方法 %s 未注册，跳过", method_id)
        return None, 0.0
    method_name = suite.METHOD_NAMES_ZH.get(method_id, method_id)
    method_start = time.perf_counter()
    result_dict: dict = {}
    error: Exception | None = None
    try:
        result = suite._run_method_with_timeout(
            method_id, func, test_cache, report)
        result_dict = result_to_dict(result)
        _status = result_dict.get("status")
        if result_status_bucket(_status) != _status:
            raise TypeError(
                f"方法返回状态缺失或非法（{type(result).__name__} → "
                f"status={_status!r}），无法作为诊断证据")
        suite.results[method_id] = result
        _lift_channel_metrics(method_id, result_dict, coverage_payload)
        findings = result_dict.get("findings")
        if not isinstance(findings, (list, tuple)):
            findings = []
            result_dict["findings"] = findings
        _mark_findings_source(findings, method_id, all_findings)
        logger.info("[TestSuite] %s: %d findings", method_name, len(findings))
    except Exception as e:
        error = e
        logger.warning("[TestSuite] %s 执行异常: %s", method_name, e,
                       exc_info=True)
    method_elapsed = (time.perf_counter() - method_start) * 1000
    if error is not None:
        return _method_error_entry(error, method_elapsed), method_elapsed
    return _sub_result_entry(result_dict, method_elapsed), method_elapsed
def _execute_test_methods(
        suite: TestingSuite, skill_dir: str, report: dict | None,
        test_cache: FileCache) -> tuple[list, dict, float, dict]:
    all_findings: list = []
    sub_results: dict[str, dict] = {}
    total_elapsed = 0.0
    coverage_payload = {"coverage": {}}
    for method_id in TEST_METHOD_IDS:
        if method_id in _POLICY_EXCLUDE_METHODS:
            sub_results[method_id] = _policy_skipped_entry()
            continue
        entry, method_elapsed = _run_test_method(
            suite, method_id, skill_dir, report, test_cache,
            all_findings, coverage_payload)
        if entry is None:
            continue
        total_elapsed += method_elapsed
        sub_results[method_id] = entry
    return all_findings, sub_results, total_elapsed, coverage_payload
def _dedup_text(value) -> str:
    return "" if value is None else str(value)
def _dedup_key(f: dict) -> tuple:
    line = f.get("line")
    line_key = ("" if isinstance(line, bool) or line in (None, 0, "")
                else str(line))
    key = (
        _dedup_text(f.get("file")),
        line_key,
        _dedup_text(f.get("rule_id") or f.get("type")),
        _dedup_text(f.get("test")),
        _dedup_text(f.get("function")),
    )
    if not any(key):
        return key + (_dedup_text(f.get("check")),
                      _dedup_text(f.get("message")))
    return key
def _dedup_test_findings(all_findings: list) -> list:
    seen = set()
    deduped = []
    for f in all_findings:
        if not isinstance(f, dict):
            deduped.append(f)
            continue
        key = _dedup_key(f)
        if key not in seen:
            seen.add(key)
            deduped.append(f)
    return deduped
def _policy_filtered_summary(suite: TestingSuite) -> dict | None:
    if not suite.results:
        return None
    try:
        _filtered_view: dict = {}
        for _mid, _res in suite.results.items():
            raw_findings = (_res.get("findings", [])
                            if isinstance(_res, dict)
                            else getattr(_res, "findings", []))
            _kept, _ = _apply_default_output_policy(
                list(raw_findings or []), method_id=_mid)
            _filtered_view[_mid] = coerce_result_view(
                _mid, _res, findings=_kept)
        return build_suite_diagnostic_summary(_filtered_view)
    except Exception as e:
        logger.warning("[TestSuite] 诊断摘要生成失败: %s", e)
        return None
def _diff_file_digests(fp_start: dict[str, str],
                       fp_end: dict[str, str]) -> dict:
    _changed = sorted(
        k for k in set(fp_start) & set(fp_end)
        if fp_start[k] != fp_end[k])
    _added = sorted(set(fp_end) - set(fp_start))
    _removed = sorted(set(fp_start) - set(fp_end))
    _diff = sorted(set(_changed) | set(_added) | set(_removed))
    return {
        "count": len(_diff),
        "files": _diff[:_DIFF_DETAIL_LIMIT],
        "truncated": len(_diff) > _DIFF_DETAIL_LIMIT,
        "changed": _changed[:_DIFF_DETAIL_LIMIT],
        "added": _added[:_DIFF_DETAIL_LIMIT],
        "removed": _removed[:_DIFF_DETAIL_LIMIT],
    }
def _prepare_test_cache(skill_dir: str, cache):
    if isinstance(cache, FileCache):
        return cache
    _test_cache = FileCache(skill_dir, ctx=cache)
    _test_cache.load()
    return _test_cache
def _count_method_stats(deduped: list) -> dict:
    method_stats: dict[str, int] = {}
    for f in deduped:
        if not isinstance(f, dict):
            continue
        mid = f.get("_test_method", "unknown")
        method_stats[mid] = method_stats.get(mid, 0) + 1
    return method_stats
def _evaluate_test_maturity(skill_dir: str,
                            coverage_payload: dict) -> dict | None:
    try:
        _cov_pct = coverage_payload.get("coverage", {}).get("overall_coverage_pct")
        _pct = safe_float(_cov_pct, None)
        _cov_data = {"percent": _pct} if _pct is not None else None
        _level = assess_test_maturity(skill_dir, coverage_data=_cov_data)
        logger.info("[TestSuite] 测试成熟度: %s", _level.name)
        return {
            "level": _level.name,
            "value": int(_level),
            "coverage_percent": _pct,
        }
    except Exception as e:
        logger.warning("[TestSuite] 成熟度评估失败: %s", e)
        return None
def _mark_torn_findings(deduped: list, fp_start: dict, fp_end: dict
                        ) -> tuple[int, bool, dict | None]:
    changed = fp_start != fp_end
    detail = _diff_file_digests(fp_start, fp_end) if changed else None
    torn_count = 0
    if changed:
        for f in deduped:
            if isinstance(f, dict) and f.get("type") in ("test_failure", "test_error"):
                f["torn_snapshot"] = True
                f["confirm_status"] = "pending_confirm"
                torn_count += 1
        if torn_count:
            logger.warning(
                "[TestSuite] 运行期源码被修改（撕裂快照）：%d 条 "
                "test_failure/test_error 已标注 torn_snapshot/"
                "pending_confirm，须在源码稳定窗口复扫确认", torn_count)
    return torn_count, changed, detail
def _sub_error_mids(sub_results: dict) -> list:
    return [m for m, st in sub_results.items()
            if isinstance(st, dict) and st.get("status") == "error"]
def _sub_failed_mids(sub_results: dict) -> list:
    return [m for m, st in sub_results.items()
            if isinstance(st, dict)
            and st.get("status") in {"failed", "fail"}]
def _overall_suite_status(sub_results: dict,
                          has_source: bool | None = None) -> tuple[str, str]:
    _err_mids = _sub_error_mids(sub_results)
    _failed_mids = _sub_failed_mids(sub_results)
    _unit_sr = sub_results.get("unit_test")
    if not isinstance(_unit_sr, dict):
        _unit_sr = {}
    _unit_status = _unit_sr.get("status")
    _unit_channel_dead = (
        (_unit_status == "warn"
         or (_unit_status == "skip" and has_source is True))
        and (_unit_sr.get("tests_run") or 0) == 0)
    if _failed_mids:
        return "warn", f" | 子方法失败: {','.join(_failed_mids[:5])}"
    if _unit_channel_dead:
        return "warn", (" | unit_test通道降级(0用例执行,"
                        "测试结果不可作为证据)")
    if _err_mids:
        return "warn", f" | 子方法异常: {','.join(_err_mids[:5])}"
    executed = {
        mid: result for mid, result in sub_results.items()
        if isinstance(result, dict)
        and result.get("status") != "skipped_by_policy"
    }
    if not executed:
        return "skip", " | 无可执行子方法（全部按策略跳过）"
    _warn_mids = [mid for mid, result in executed.items()
                  if result.get("status") == "warn"]
    if _warn_mids:
        return "warn", f" | 子方法警告: {','.join(_warn_mids[:5])}"
    _skip_mids = [mid for mid, result in executed.items()
                  if result.get("status") == "skip"]
    if _skip_mids:
        status = "skip" if len(_skip_mids) == len(executed) else "warn"
        return status, f" | 子方法跳过: {','.join(_skip_mids[:5])}"
    return "pass", ""
def run_test_suite(skill_dir: str, cache: Any = None,
                  report: dict | None = None) -> dict:
    cache = ensure_entry_warmed(skill_dir, cache, who="run_test_suite")
    start = time.perf_counter()
    supplemental = ensure_supplemental_tests(skill_dir)
    if not isinstance(supplemental, dict):
        logger.warning("[TestSuite] 补足测试返回形态异常(%s)，按空结果继续",
                       type(supplemental).__name__)
        supplemental = {}
    _fp_files_start = _f1_file_digests(skill_dir)
    if supplemental.get("status") in ("generated", "rebuilt"):
        logger.info("[TestSuite] 目标技能无自带测试，已自动生成补足测试套件: %s",
                    supplemental.get("summary"))
    suite = TestingSuite(skill_dir)
    _test_cache = _prepare_test_cache(skill_dir, cache)
    all_findings, sub_results, total_elapsed, coverage_payload = (
        _execute_test_methods(suite, skill_dir, report, _test_cache))
    return _finalize_suite_run(
        skill_dir, suite, all_findings, sub_results, coverage_payload,
        _fp_files_start, start, total_elapsed, supplemental)
def _suite_summary_text(total_deduped: int, total_raw: int,
                        dedup_drop: int, policy_drop: int, sub_count: int,
                        elapsed: float, torn_note: str,
                        degrade_note: str) -> str:
    return (
        f"测试套件: {total_deduped} findings ({total_raw}原始, "
        f"去重{dedup_drop}, 策略抑制{policy_drop}) | "
        f"{sub_count}个子方法, {elapsed:.0f}ms{torn_note}{degrade_note}"
    )
def _finalize_suite_run(skill_dir: str, suite, all_findings: list,
                        sub_results: dict, coverage_payload: dict,
                        fp_start: dict, start: float, total_elapsed: float,
                        supplemental: dict) -> dict:
    deduped = _dedup_test_findings(all_findings)
    _dedup_drop_count = len(all_findings) - len(deduped)
    deduped, _suppressed_stats = _apply_default_output_policy(deduped)
    _policy_drop_count = sum(_suppressed_stats.values())
    method_stats = _count_method_stats(deduped)
    total_raw = len(all_findings)
    total_deduped = len(deduped)
    elapsed = round((time.perf_counter() - start) * 1000, 1)
    maturity_info = _evaluate_test_maturity(skill_dir, coverage_payload)
    _fp_files_end = _f1_file_digests(skill_dir)
    _torn_count, _changed_during_run, _changed_files_detail = (
        _mark_torn_findings(deduped, fp_start, _fp_files_end))
    _torn_note = ""
    if _changed_during_run:
        _torn_note = (f" | 撕裂快照: {_torn_count}条待复扫确认"
                      if _torn_count else " | 撕裂快照: 源码运行期变化，结果需复扫")
    _has_source = count_source_files(skill_dir) > 0
    _overall_status, _degrade_note = _overall_suite_status(
        sub_results, has_source=_has_source)
    if _changed_during_run and _overall_status == "pass":
        _overall_status = "warn"
    return {
        "status": _overall_status,
        "findings_count": total_deduped,
        "summary": _suite_summary_text(
            total_deduped, total_raw, _dedup_drop_count, _policy_drop_count,
            len(sub_results), elapsed, _torn_note, _degrade_note),
        "findings": deduped,
        "payload": {
            "method_stats": method_stats,
            "sub_results": sub_results,
            "total_elapsed_ms": round(total_elapsed, 1),
            "methods_executed": sum(
                1 for _st in sub_results.values()
                if isinstance(_st, dict)
                and _st.get("status") != "skipped_by_policy"),
            "coverage": coverage_payload.get("coverage", {}),
            "regression": coverage_payload.get("regression", {}),
            "maturity": maturity_info,
            "diagnostic_summary": _policy_filtered_summary(suite),
            "suppressed": _suppressed_stats,
            "supplemental": supplemental,
            "source_fingerprint": {
                "changed_during_run": _changed_during_run,
                "torn_findings": _torn_count,
                "changed_files": _changed_files_detail,
            },
        },
    }
_E_DETECTORS: dict[str, Any] = {
    "E1": run_test_suite,
    "E2": run_f2_mutation_targeted,
    "E3": run_f3_test_postprocessor,
}
_E_DETECTOR_IDS = tuple(_E_DETECTORS)
def _run_e_detectors(skill_dir: str, cache, report) -> list:
    det_results: list = []
    _e1_entry: dict | None = None
    _e1_done_epoch: float | None = None
    for det_id, det_fn in _E_DETECTORS.items():
        fn_kwargs = None
        if det_id == "E3" and _e1_entry is not None:
            fn_kwargs = {"e1_result": _e1_entry.get("result"),
                         "e1_done_epoch": _e1_done_epoch}
        entry = detector_entry(
            det_id, det_fn, skill_dir, cache,
            engine_tag="engine_e", logger=logger, report=report,
            fn_kwargs=fn_kwargs)
        det_results.append(entry)
        if det_id == "E1":
            _e1_entry = entry
            _e1_done_epoch = time.time()
    return det_results
def run_engine_E(skill_dir: str, cache=None, **kw) -> dict:
    cache = ensure_entry_warmed(skill_dir, cache, "主引擎 E 组")
    t0 = time.perf_counter()
    with fingerprint_freeze_window(cache, "E组"):
        det_results = _run_e_detectors(
            skill_dir, cache, kw.get("report"))
    merged, conflicts, stats = consolidate_findings(det_results, "E", "engine_e")
    merged, _suppressed = apply_inline_suppressions(merged, skill_dir)
    if _suppressed:
        stats = {**stats, "inline_suppressed": _suppressed,
                 "merged_findings": len(merged)}
    worst = worst_sub_status(det_results, merged)
    return group_envelope(
        "E", _E_DETECTOR_IDS, worst, merged, stats, det_results, t0,
        summary=(f"主引擎E: 检测器{len(det_results)}个, "
                 f"原始发现{stats['raw_findings']}, "
                 f"预合并后{stats['merged_findings']}, "
                 f"冲突{stats['conflicts']}"),
        conflicts=conflicts,
    )

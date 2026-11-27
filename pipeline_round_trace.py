# ruff: noqa: I001
from __future__ import annotations
import functools
import glob as _glob
import hashlib
import json
import logging
import math
import os
import re
import signal
import sys
import threading
import time
from collections.abc import Callable
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any, NamedTuple, Self
from jwsgj.diag_guard_io import (
    guarded_open,
    safe_delete,
)
from jwsgj.diag_guard_state import (
    ProcessLock,
    ProvenanceGuard,
    StateIntegrityGuard,
    StateTamperError,
    verify_provenance_logged,
)
from jwsgj.diag_types_defs import (
    ConcurrentExecutionError,
)
from jwsgj.diag_types_normalize import (
    coerce_round_anchor,
    coerce_round_anchor_strict,
    compact_ts_to_ms,
    dict_items,
    dict_or_empty,
    format_compact_ts,
    int_or,
    is_real_number,
    safe_float,
    str_or_empty,
    timestamp_ms,
)
from jwsgj.log_config import (
    locked_artifact,
    log_swallowed,
    perf_trace,
    write_audit,
    write_module_run,
)
from jwsgj.runtime_paths import (
    PIPELINE_STATE_FILENAME,
    first_json_artifact,
    get_temp_dir,
    is_artifact_destination_allowed,
    json_artifact_glob,
    json_artifact_path,
)
from jwsgj.runtime_paths import (
    json_artifact_dir as internal_json_artifact_dir,
)
from jwsgj.runtime_scope import (
    normalize_skill_dir,
)
from jwsgj.shared_cache import (
    BatchDetector,
    get_warmed_cache,
    mem_bus_peek,
    mem_bus_put,
)
from jwsgj.treatment_state import (
    TREATMENT_COUNT_KEYS,
    get_treatment_state_path,
    load_treatment_state,
    treatment_progress,
)
from jwsgj.xv_context_derivation import (
    METHOD_REGISTRY,
    PHASES,
    TERMINAL_STATUSES,
    TREATMENT_PHASE,
    all_method_ids,
)
from jwsgj.xv_intermediate_store import (
    append_stage_trace_entry,
    compute_skill_source_hash,
    get_round_start_ts,
    load_intermediate,
    normalize_round_start_ts,
    resolve_intermediate_dirs,
)
import ctypes
from ctypes import wintypes
logger = logging.getLogger(__name__)
_INITIAL_PHASE = "pending_diagnosis"
__all__ = [
    'ARCHIVE_DIRNAME',
    'PipelineContext',
    'PipelineGuard',
    'advance_diagnosis_done',
    'advance_pipeline_phase',
    'archive_step_result',
    'check_diagnosis_reusable',
    'cleanup_legacy_fix_route_report',
    'count_intermediate_payloads',
    'current_round_anchor',
    'diagnosis_fresh_complete',
    'diagnosis_progress_dict',
    'ensure_diagnosis_round',
    'get_diagnosis_progress',
    'get_pipeline_progress',
    'get_pipeline_state_path',
    'get_treatment_progress',
    'guarded_step',
    'is_step_guard_blocked',
    'list_methods',
    'load_pipeline_state',
    'load_review_evidence',
    'normalize_count',
    'persist_review_result',
    'pipeline_step_guard',
    'progress_of',
    'publish_step_result',
    'query_methods_progress',
    'render_method_status_table',
    'resolve_method_id',
    'resume_phase',
    'round_start_epoch',
    'run_step_shell',
    'save_pipeline_state',
    'save_treatment_plan',
    'treatment_exec_result',
    'treatment_progress_of',
    'treatment_trace_metrics',
]
def get_pipeline_state_path(skill_dir: str) -> str:
    return os.path.join(get_temp_dir(skill_dir), PIPELINE_STATE_FILENAME)
@contextmanager
def _pipeline_state_locked(skill_dir: str):
    state_path = get_pipeline_state_path(skill_dir)
    with locked_artifact(state_path) as locked:
        if not locked:
            raise RuntimeError(f"管线状态写锁不可用，拒绝无锁读写事务: {state_path}")
        yield
def _normalize_pipeline_state(data: dict) -> dict:
    if not isinstance(data, dict):
        return _initial_pipeline_state()
    data["artifacts"] = dict_or_empty(data.get("artifacts"))
    for _k in ("phase", "timestamp", "recovery_strategy", "source_hash"):
        _v = data.get(_k)
        if not isinstance(_v, str) or not _v:
            data.pop(_k, None)
    data.setdefault("phase", _INITIAL_PHASE)
    data.setdefault("timestamp", timestamp_ms())
    data.setdefault("recovery_strategy", "resume")
    data.setdefault("source_hash", "")
    return data
def _initial_pipeline_state() -> dict:
    return {
        "phase": _INITIAL_PHASE, "timestamp": timestamp_ms(),
        "artifacts": {}, "recovery_strategy": "from_start", "source_hash": "",
    }
def _unverified_pipeline_state(exc: Exception) -> dict:
    state = _initial_pipeline_state()
    state["_state_load_error"] = str(exc)[:500] or type(exc).__name__
    return state

def load_pipeline_state(skill_dir: str) -> dict:
    state_path = get_pipeline_state_path(skill_dir)
    if not os.path.isfile(state_path):
        return _initial_pipeline_state()
    try:
        data = StateIntegrityGuard.load_verified(skill_dir, state_path)
    except StateTamperError as e:
        logger.warning(
            "[PipelineState] 签名验证失败，拒绝使用未验证内容并重置: %s", e)
        return _unverified_pipeline_state(e)
    except Exception as e:  # noqa: BLE001
        logger.warning("[PipelineState] 加载失败（签名验证或读取错误）: %s，重置为初始状态", e)
        return _unverified_pipeline_state(e)
    return _normalize_pipeline_state(data)
def save_pipeline_state(skill_dir: str, state: dict):
    if not isinstance(state, dict):
        raise TypeError(
            f"管线状态必须是 dict，收到 {type(state).__name__}: {state!r}")
    os.makedirs(get_temp_dir(skill_dir), exist_ok=True)
    state.pop("_state_load_error", None)
    _normalize_pipeline_state(state)
    state["timestamp"] = timestamp_ms()
    with _pipeline_state_locked(skill_dir):
        StateIntegrityGuard.save_signed(
            skill_dir, get_pipeline_state_path(skill_dir), state)
def save_treatment_plan(plan: Any, output_dir: str) -> str:
    if (not output_dir
            or not is_artifact_destination_allowed(str(output_dir))):
        raise RuntimeError(
            f"治疗方案落点非法: {output_dir!r}——过程产物落点只能是"
            "会话工作空间（Temp 治理契约，不设其他位置兜底）；"
            "请传入会话工作空间内的目录。")
    os.makedirs(output_dir, exist_ok=True)
    path = os.path.join(output_dir, "treatment_plan_latest.json")
    payload = plan if isinstance(plan, dict) else plan.to_dict()
    with guarded_open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2, default=str)
    logger.info("[TreatmentPlan] 已保存: %s", path)
    return path
_REUSE_MIN_INTERMEDIATE_PAYLOADS = 1
def diagnosis_fresh_complete(progress: Any) -> bool:
    if not isinstance(progress, dict):
        return False
    _total = progress.get("total")
    _completed = progress.get("completed")
    if isinstance(_total, bool) or not isinstance(_total, int) or _total <= 0:
        return False
    if isinstance(_completed, bool) or not isinstance(_completed, int):
        return False
    return progress.get("next_method") is None and _completed >= _total
def count_intermediate_payloads(intermediate_dir: str) -> int:
    count = 0
    method_ids = set(all_method_ids()) or set(METHOD_REGISTRY)
    for path in _glob.glob(os.path.join(intermediate_dir, "*.json")):
        basename = os.path.basename(path)
        if not basename.startswith("round_"):
            if any(basename == f"{mid}.json"
                   or basename.startswith(f"{mid}_") for mid in method_ids):
                count += 1
            continue
        try:
            with open(path, encoding="utf-8-sig") as _fh:
                doc = json.load(_fh)
            _methods = doc.get("methods") if isinstance(doc, dict) else None
            count += len(_methods) if isinstance(_methods, dict) else 1
        except (OSError, ValueError, RecursionError) as _e:
            logger.debug("[Pipeline] consolidated 计数读取失败(按 1 计): %s", _e)
            count += 1
    return count
def _reuse_round_mismatch(p_state: dict) -> bool:
    _round_ts = str(p_state.get("round_start_ts", "") or "")
    _hash_round_ts = str(p_state.get("diagnosis_round_ts", "") or "")
    if not _hash_round_ts or not _round_ts:
        return False
    normalized_round = normalize_round_start_ts(_round_ts)
    normalized_hash_round = normalize_round_start_ts(_hash_round_ts)
    if not normalized_round or not normalized_hash_round:
        return _hash_round_ts != _round_ts
    return normalized_hash_round != normalized_round
def check_diagnosis_reusable(skill_dir: str) -> dict:
    sd = normalize_skill_dir(skill_dir)
    p_state = load_pipeline_state(sd)
    cached_hash = p_state.get("source_hash", "")
    try:
        current_hash = compute_skill_source_hash(sd)
    except OSError as exc:
        return {"reusable": False, "cached_hash": cached_hash,
                "current_hash": "",
                "reason": f"源码指纹不可用，历史诊断结果不可复用: {exc}"}
    def _reject(reason: str, cached: str = cached_hash, **extra: Any) -> dict:
        _payload: dict = {"reusable": False, "cached_hash": cached,
                          "current_hash": current_hash, "reason": reason}
        _payload.update(extra)
        return _payload
    if not cached_hash:
        return _reject("无历史哈希", "")
    if cached_hash != current_hash:
        return _reject("源码已变更")
    if _reuse_round_mismatch(p_state):
        return _reject("诊断轮次已切换，历史哈希产生于其他轮次")
    try:
        intermediate_dir = internal_json_artifact_dir(sd)
    except (RuntimeError, ValueError) as _dir_err:
        return _reject(f"中间结果目录不可解析: {_dir_err}")
    if not os.path.isdir(intermediate_dir):
        return _reject("中间结果目录不存在")
    _payload_count = count_intermediate_payloads(intermediate_dir)
    if _payload_count < _REUSE_MIN_INTERMEDIATE_PAYLOADS:
        return _reject(f"中间结果载荷不足: {_payload_count} 个")
    prog = dict_or_empty(get_diagnosis_progress(sd))
    if not diagnosis_fresh_complete(prog):
        _total = prog.get("total", 0)
        _completed = prog.get("completed", 0)
        return _reject(
            f"本轮诊断中间结果不完整: 新鲜完成 {_completed}/{_total}",
            fresh_completed=_completed, diag_total=_total)
    return {"reusable": True, "cached_hash": cached_hash,
            "current_hash": current_hash,
            "reason": "源码未变更，历史诊断结果可复用",
            "intermediate_files_count": _payload_count}
def ensure_diagnosis_round(skill_dir: str) -> str:
    current_hash = compute_skill_source_hash(skill_dir)
    with _pipeline_state_locked(skill_dir):
        state = load_pipeline_state(skill_dir)
        ts = coerce_round_anchor(state.get("round_start_ts"))
        active = state.get("diagnosis_round_active") is True
        bound_hash = str(state.get("round_source_hash", "") or "")
        valid_ts = normalize_round_start_ts(ts)
        if not valid_ts or not active or bound_hash != current_hash:
            _reset_reason = (
                "启动新" if (not valid_ts or not active)
                else f"源码已变更（{bound_hash[:8] or '-'}→{current_hash[:8]}），重置")
            ts = timestamp_ms()
            state["round_start_ts"] = ts
            state["diagnosis_round_active"] = True
            state["round_source_hash"] = current_hash
            state.pop(_RESUME_DEGRADED_KEY, None)
            save_pipeline_state(skill_dir, state)
            logger.info("[PipelineNext] %s诊断轮次 round_start_ts=%s", _reset_reason, ts)
        return ts
def current_round_anchor(skill_dir: str) -> str:
    try:
        raw = load_pipeline_state(skill_dir).get("round_start_ts")
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context=f'current_round_anchor:{type(_e).__name__}')
        return ""
    anchor = coerce_round_anchor_strict(raw)
    return normalize_round_start_ts(anchor) if isinstance(anchor, str) else ""
def round_start_epoch(skill_dir: str) -> float:
    try:
        anchor = current_round_anchor(skill_dir)
        epoch_ms = compact_ts_to_ms(anchor) if anchor else None
        return epoch_ms / 1000.0 if epoch_ms is not None else 0.0
    except Exception:
        logger.debug("[PruneConsumed] round_start_ts 解析失败，退化无当轮保护",
                     exc_info=True)
    return 0.0
_ARTIFACT_PATH_KEYS = (
    "cv_report_path",
    "full_report_path",
    "plan_path",
    "fix_report_path",
    "review_path",
    "fanout_html_path",
)
DEFAULT_ADVANCE_DIRECTION = "advance"
def advance_pipeline_phase(skill_dir: str, new_phase: str,
                            extra: dict | None = None,
                            advance_kind: str = DEFAULT_ADVANCE_DIRECTION
                            ) -> dict:
    if not isinstance(new_phase, str) or not new_phase.strip():
        raise ValueError("new_phase 须为非空字符串")
    new_phase = new_phase.strip()
    if new_phase not in _PHASE_LABELS:
        raise ValueError(f"未登记的管线相位: {new_phase!r}")
    with _pipeline_state_locked(skill_dir):
        state = load_pipeline_state(skill_dir)
        _prev_phase = state.get("phase", "")
        _incoming_artifacts = None
        if extra:
            _extra = dict(extra)
            _raw_artifacts = _extra.pop("artifacts", None)
            if isinstance(_raw_artifacts, dict):
                _incoming_artifacts = _raw_artifacts
            _extra.pop("round_start_ts", None)
            state.update(_extra)
        _artifacts = dict_or_empty(state.get("artifacts"))
        if _incoming_artifacts:
            _artifacts.update(_incoming_artifacts)
        if extra:
            for _k in _ARTIFACT_PATH_KEYS:
                if extra.get(_k):
                    _artifacts[_k] = str(extra[_k])
        state["artifacts"] = _artifacts
        state["phase"] = new_phase
        if new_phase == "diagnosis_done":
            state["diagnosis_round_active"] = False
        state["recovery_strategy"] = "resume"
        save_pipeline_state(skill_dir, state)
    _ts = state.get("timestamp", "")
    try:
        write_audit("pipeline_phase_transition",
                     phase=new_phase,
                     from_phase=_prev_phase,
                     skill_dir=os.path.basename(skill_dir),
                     timestamp=_ts)
    except Exception as _ae:  # noqa: BLE001
        log_swallowed(__name__, _ae,
                      context=f'advance_pipeline_phase:{type(_ae).__name__}')
    _append_stage_trace(
        skill_dir, _prev_phase, new_phase, extra or {}, _ts, advance_kind,
        round_start_ts=coerce_round_anchor(state.get("round_start_ts")))
    return state
def advance_diagnosis_done(skill_dir: str, progress: Any,
                          **extra: Any) -> None:
    _progress = dict_or_empty(progress)
    advance_pipeline_phase(skill_dir, "diagnosis_done", {
        "diag_completed": normalize_count(_progress.get("completed", 0)),
        "diag_total": normalize_count(_progress.get("total", 0)),
        "source_hash": compute_skill_source_hash(skill_dir),
        "diagnosis_round_ts": coerce_round_anchor(
            load_pipeline_state(skill_dir).get("round_start_ts")),
        **extra,
    })
def _plan_is_empty(sd: str, current: str) -> bool:
    _pfs = sorted(json_artifact_glob(sd, "treatment_plan_*.json"),
                  reverse=True)
    for path in _pfs:
        if not _resume_plan_is_current(sd, path, current):
            continue
        payload = _resume_json_object(path)
        if payload is None:
            continue
        items = payload.get("items")
        if isinstance(items, list) and not items:
            return True
    return False
_PHASE_LABELS = {
    "pending_diagnosis": "阶段1: 诊断方法执行中",
    "diagnosis_done": "阶段1完成: 等待回归CV",
    "cv_regression_done": "阶段2a完成: 等待主CV",
    "cv_main_done": "阶段2b完成: 等待扇出诊断",
    "fanout_done": "阶段G完成: 扇出诊断与治疗完成，等待治疗方案",
    "plan_dry_done": "阶段3a完成: 等待治疗方案生成",
    "plan_generated": "阶段3b完成: 等待治疗执行",
    "treatment_done": "阶段4完成(治疗项执行): 等待AI手动修复",
    "ai_fix_pending": "阶段4b: 待 AI 审核执行（逐项）",
    "ai_fix_done": "阶段4b完成(AI手动修复): 等待复盘",
    "review_done": "阶段5完成: 等待反哺增强",
    "fupan_done": "阶段6a完成: 等待feedback_loop",
    "feedback_done": "阶段6b完成: 等待code_feedback",
    "code_feedback_done": "阶段6c完成: 等待auto_enhance",
    "evolution_pending": "阶段6e: 复盘反哺待 AI 审核执行（逐项）",
    "all_completed": "全部完成",
}
_PHASE_CHAIN = tuple(_PHASE_LABELS)
def _phase_slice(start: str, end: str | None = None, *,
                 inclusive: bool = False) -> tuple:
    _start = _PHASE_CHAIN.index(start)
    if end is None:
        return _PHASE_CHAIN[_start:]
    _stop = _PHASE_CHAIN.index(end) + (1 if inclusive else 0)
    return _PHASE_CHAIN[_start:_stop]
_PNS_RESUME_CV_PHASES = _phase_slice("cv_main_done", "all_completed")
_PNS_RESUME_PLAN_PHASES = _phase_slice(
    "plan_generated", "review_done", inclusive=True)
_PNS_RESUME_STATE_PHASES = _phase_slice(
    "treatment_done", "review_done", inclusive=True)
_PNS_RESUME_REVIEW_PHASES = _phase_slice("review_done", "all_completed")
def _rewind_phase_for_resume(sd: str, target_phase: str) -> bool:
    try:
        advance_pipeline_phase(sd, target_phase,
                                advance_kind="rewind_resume")
        return True
    except Exception:
        logger.warning("[PipelineNext] 回退相位写盘失败（保持原相位待重试）: "
                       "target=%s", target_phase, exc_info=True)
        return False
def _resume_json_object(path: str) -> dict | None:
    try:
        with open(path, encoding="utf-8-sig") as handle:
            payload = json.load(handle)
    except (OSError, ValueError, RecursionError) as exc:
        logger.debug("[PipelineNext] 恢复产物不可读，按非本轮证据跳过: %s: %s",
                     path, exc)
        return None
    return payload if isinstance(payload, dict) else None
def _resume_payload_usable(payload: Any) -> bool:
    return (isinstance(payload, dict) and bool(payload)
            and payload.get("_error") is not True)
def _resume_payload_anchor(payload: dict) -> str | None:
    if "round_start_ts" not in payload:
        return None
    try:
        anchor = coerce_round_anchor_strict(payload.get("round_start_ts"))
    except (TypeError, ValueError):  # jwsgj:silent-ok
        return None
    normalized = (normalize_round_start_ts(anchor)
                  if isinstance(anchor, str) else "")
    return normalized or None
def _resume_payload_is_current(payload: dict, current: str) -> bool:
    anchor = _resume_payload_anchor(payload)
    return bool(anchor and anchor == current)
def _resume_cv_report_present(sd: str) -> bool:
    current = current_round_anchor(sd)
    if not current:
        return False
    for path in json_artifact_glob(sd, "cv_final_report_*.json"):
        payload = _resume_json_object(path)
        if (_resume_payload_usable(payload)
                and _resume_payload_is_current(payload, current)):
            return True
    return False
def _resume_mtime_is_current(sd: str, path: str) -> bool:
    epoch = round_start_epoch(sd)
    if epoch <= 0:
        return False
    try:
        return os.path.getmtime(path) >= epoch
    except OSError:  # jwsgj:silent-ok
        return False
def _resume_plan_is_current(sd: str, path: str, current: str) -> bool:
    payload = _resume_json_object(path)
    if not _resume_payload_usable(payload):
        return False
    if "round_start_ts" in payload:
        return _resume_payload_anchor(payload) == current
    return _resume_mtime_is_current(sd, path)
def _resume_plan_present(sd: str) -> bool:
    current = current_round_anchor(sd)
    if not current:
        return False
    return any(
        _resume_plan_is_current(sd, path, current)
        for path in json_artifact_glob(sd, "treatment_plan_*.json"))
def _resume_treatment_state_present(sd: str) -> bool:
    current = current_round_anchor(sd)
    if not current:
        return False
    state_path = get_treatment_state_path(sd)
    if os.path.isfile(state_path):
        _state = load_treatment_state(sd)
        _status = _state.get("status") if isinstance(_state, dict) else None
        if _status == "error":
            logger.warning("[PipelineNext] 治疗状态文件损坏，按缺失回退重生成")
            return False
        if isinstance(_state, dict) and "round_start_ts" in _state:
            if _resume_payload_anchor(_state) != current:
                logger.warning(
                    "[PipelineNext] 治疗状态属于其他轮次或锚非法，按缺失重生成")
                return False
        elif not _resume_mtime_is_current(sd, state_path):
            logger.warning(
                "[PipelineNext] 无锚治疗状态早于本轮，拒绝跨轮恢复: %s",
                state_path)
            return False
        if _status == "no_plan":
            logger.info("[PipelineNext] 治疗计划为空（无待执行项），无需回退")
        return True
    if _plan_is_empty(sd, current):
        logger.info("[PipelineNext] 本轮治疗计划为空（无待执行项），无需回退")
        return True
    return False
def _resume_review_present(sd: str) -> bool:
    if not os.path.isfile(_review_result_path(sd)):
        return False
    try:
        review = _load_review_result(sd, use_mem=False)
    except ValueError as exc:
        logger.warning("[PipelineNext] 复盘结果不可读，按缺失回退重跑阶段5: %s", exc)
        return False
    return _validated_review_evidence(sd, review) is not None
_PNS_RESUME_ARTIFACTS = (
    (_PNS_RESUME_CV_PHASES, _resume_cv_report_present,
     _INITIAL_PHASE, "CV报告缺失", "cv_main_done"),
    (_PNS_RESUME_PLAN_PHASES, _resume_plan_present,
     "cv_main_done", "治疗计划缺失", "plan_generated"),
    (_PNS_RESUME_STATE_PHASES, _resume_treatment_state_present,
     "plan_generated", "治疗状态文件缺失", "treatment_done"),
    (_PNS_RESUME_REVIEW_PHASES, _resume_review_present,
     "ai_fix_done", "阶段5复盘结果缺失", "review_done"),
)
_RESUME_DEGRADED_KEY = "resume_degraded"
def _record_resume_degraded(sd: str, phase: str, target: str,
                            reason: str) -> None:
    try:
        with _pipeline_state_locked(sd):
            state = load_pipeline_state(sd)
            degraded = dict_or_empty(state.get(_RESUME_DEGRADED_KEY))
            degraded[phase] = {"target": target,
                               "reason": reason,
                               "ts": timestamp_ms()}
            state[_RESUME_DEGRADED_KEY] = degraded
            save_pipeline_state(sd, state)
        logger.info(
            "[PipelineNext] 恢复降级登记: phase=%s 回退目标=%s 原因=%s",
            phase, target, reason)
    except Exception as _re:  # noqa: BLE001
        log_swallowed(__name__, _re,
                      context=f'_record_resume_degraded:{type(_re).__name__}')
def _pns_validate_resume(sd: str, phase: str) -> str:
    if phase in (_INITIAL_PHASE, "all_completed"):
        return phase
    logger.info("[PipelineNext] 检测到会话中断恢复，当前阶段: %s", phase)
    for _phases, _present, _target, _msg, _anchor in _PNS_RESUME_ARTIFACTS:
        if phase not in _phases or _present(sd):
            continue
        if phase != _anchor:
            logger.warning(
                "[PipelineNext] %s（历史产物缺失，降级继续不回退）: "
                "phase=%s 产出相位=%s 回退目标=%s",
                _msg, phase, _anchor, _target)
            _record_resume_degraded(sd, phase, _target, _msg)
            continue
        logger.warning("[PipelineNext] %s，回退到 %s 重跑", _msg, _target)
        if _rewind_phase_for_resume(sd, _target):
            return _target
        logger.warning(
            "[PipelineNext] %s 回退落盘失败，保持 phase=%s 待下次调用重试",
            _msg, phase)
        return phase
    return phase
def resume_phase(sd: str) -> str:
    return _pns_validate_resume(
        sd, load_pipeline_state(sd).get("phase", _INITIAL_PHASE))
_TRACE_STR_MAX_CHARS = 200
_TRACE_IDENTITY_KEYS = frozenset({"phase", "round_start_ts", "timestamp"})
def _stage_trace_metrics(extra: dict) -> dict:
    metrics: dict = {}
    for _k, _v in extra.items():
        if not isinstance(_k, str) or _k.startswith("_"):
            continue
        if _k in _TRACE_IDENTITY_KEYS or _k in _ARTIFACT_PATH_KEYS:
            continue
        if isinstance(_v, (bool, int, float)):
            metrics[_k] = _v
        elif isinstance(_v, str):
            metrics[_k] = _v[:_TRACE_STR_MAX_CHARS]
        elif isinstance(_v, (list, dict, tuple, set)):
            metrics[f"{_k}_count"] = len(_v)
    return metrics
def treatment_trace_metrics(treatment_progress: Any) -> dict:
    if not isinstance(treatment_progress, dict):
        return {}
    counts = _normalized_treatment_counts(treatment_progress)
    out = {f"treat_{_k}": counts[_k]
           for _k in _TREATMENT_TRACE_COUNT_KEYS}
    _status = treatment_progress.get("status")
    out["treat_status"] = (
        _status if isinstance(_status, str) else "")[:_TRACE_STR_MAX_CHARS]
    return out
def _append_stage_trace(skill_dir: str, from_phase: str, new_phase: str,
                        extra: dict, timestamp: str, direction: str,
                        round_start_ts: str | None = None) -> None:
    try:
        if round_start_ts is None:
            round_start_ts = load_pipeline_state(skill_dir).get(
                "round_start_ts")
        _nested_artifacts = dict_or_empty(extra.get("artifacts"))
        _entry = {
            "round_start_ts": round_start_ts,
            "from_phase": from_phase,
            "phase": new_phase,
            "timestamp": timestamp,
            "direction": direction,
            "skill_dir": str(skill_dir or ""),
            "metrics": _stage_trace_metrics(extra),
            "artifacts": {
                _k: str(extra.get(_k) or _nested_artifacts.get(_k))
                for _k in _ARTIFACT_PATH_KEYS
                if extra.get(_k) or _nested_artifacts.get(_k)
            },
        }
        append_stage_trace_entry(skill_dir, _entry)
    except Exception as _te:  # noqa: BLE001
        log_swallowed(__name__, _te,
                      context=f'_append_stage_trace:{type(_te).__name__}')
_REVIEW_RESULT_FILENAME = "_review_result.json"
_REVIEW_DONE_STATUS = "completed"
def _review_result_path(skill_dir: str) -> str:
    return json_artifact_path(skill_dir, _REVIEW_RESULT_FILENAME)
def _review_is_done(review: object) -> bool:
    if not isinstance(review, dict):
        return False
    status = review.get("status")
    return (isinstance(status, str)
            and status.strip().lower() == _REVIEW_DONE_STATUS)
def _review_result_error(review_path: str, exc: Exception) -> ValueError:
    _name = os.path.basename(review_path)
    if isinstance(exc, OSError):
        return ValueError(
            f"复盘结果文件不可读: {_name}（{exc}），"
            f"请检查文件权限后重新执行 run_review_step(skill_dir) 覆盖生成")
    return ValueError(
        f"复盘结果文件损坏: {_name}（{exc}），"
        f"请重新执行 run_review_step(skill_dir) 覆盖生成")
def _load_review_result(skill_dir: str, *, use_mem: bool = True) -> dict:
    _m = mem_bus_peek("review_result", skill_dir) if use_mem else None
    if isinstance(_m, dict) and _m:
        return _m
    review_path = _review_result_path(skill_dir)
    if not os.path.isfile(review_path):
        return {}
    try:
        with open(review_path, encoding="utf-8-sig") as f:
            loaded = json.load(f)
    except (ValueError, OSError, RecursionError) as e:
        raise _review_result_error(review_path, e) from e
    if not isinstance(loaded, dict):
        raise ValueError(  # noqa: TRY004
            f"复盘结果文件损坏: {os.path.basename(review_path)}"
            f"（顶层非 dict: {type(loaded).__name__}），"
            f"请重新执行 run_review_step(skill_dir) 覆盖生成")
    return loaded
def _review_belongs_to_current_round(skill_dir: str, review: dict) -> bool:
    current = current_round_anchor(skill_dir)
    if not current:
        logger.warning(
            "[ReviewStep] 当前轮次锚缺失/非法，拒绝消费无归属复盘证据")
        return False
    anchor = coerce_round_anchor_strict(review.get("round_start_ts"))
    if anchor is None or not normalize_round_start_ts(anchor):
        logger.warning(
            "[ReviewStep] 复盘证据缺失/非法轮次锚，拒绝跨轮消费: %s",
            review.get("round_start_ts"))
        return False
    normalized = normalize_round_start_ts(anchor)
    if normalized != current:
        logger.info("[ReviewStep] 复盘证据非本轮(round=%s != %s)，拒绝",
                    normalized, current)
        return False
    return True
def persist_review_result(skill_dir: str, out: dict) -> None:
    if not isinstance(out, dict):
        logger.warning("[ReviewStep] 复盘结果形态非法(%s)，不写入复盘证据位",
                       type(out).__name__)
        return
    review_path = _review_result_path(skill_dir)
    if not _review_is_done(out):
        _cause = out.get("error") or out.get("reason") or ""
        logger.warning(
            "[ReviewStep] 复盘未完成(status=%s)，不写入复盘证据位，"
            "phase 停留待重试（错误: %s）", out.get("status"),
            str(_cause)[:200])
        return
    out["status"] = _REVIEW_DONE_STATUS
    if not _review_belongs_to_current_round(skill_dir, out):
        out["status"] = "failed"
        out["error"] = "复盘轮次锚缺失、非法或不属于当前轮，未写入复盘证据位"
        return
    with guarded_open(review_path, "w", encoding="utf-8") as f:
        json.dump(out, f, ensure_ascii=False, indent=2, default=str)
    mem_bus_put("review_result", out, skill_dir)
    advance_pipeline_phase(skill_dir, "review_done", {
        "review_score": out.get("overall_score"),
        "review_grade": out.get("overall_grade"),
        "review_path": review_path,
    })
    logger.info("[ReviewStep] 完成: score=%s, grade=%s, %.1fs",
                 out.get("overall_score"), out.get("overall_grade"),
                 safe_float(out.get("elapsed_s")))
def _validated_review_evidence(skill_dir: str, review: dict | None) -> dict | None:
    if not isinstance(review, dict):
        return None
    if not _review_is_done(review):
        logger.warning(
            "[ReviewStep] 复盘证据未完成(status=%s)，拒绝作为阶段6输入: %s",
            review.get("status"), str(review.get("error", ""))[:200])
        return None
    if not _review_belongs_to_current_round(skill_dir, review):
        return None
    return review
def load_review_evidence(skill_dir: str) -> dict | None:
    review = _load_review_result(skill_dir) or None
    evidence = _validated_review_evidence(skill_dir, review)
    if evidence is not None:
        return evidence
    if (mem_bus_peek("review_result", skill_dir)
            and os.path.isfile(_review_result_path(skill_dir))):
        disk_review = _load_review_result(skill_dir, use_mem=False) or None
        return _validated_review_evidence(skill_dir, disk_review)
    return None
@dataclass
class PipelineContext:
    skill_dir: str
    dry_run: bool = True
    timeout: int = 30
    adapter: Any = None
    llm_call_fn: Any = None
    incremental: bool = False
    memory_context: Any = None
    temp_dir: str = ""
    report_dir: str = ""
    intermediate_dir: str = ""
    pipeline_id: str = ""
    stages: dict[str, dict[str, Any]] = field(default_factory=dict)
    adjustments: dict = field(default_factory=dict)
    hallucination_ledger: list = field(default_factory=list)
    test_bridge: Any = None
    batch_fp_result: dict | None = None
    @property
    def json_artifact_dir(self) -> str:
        if self.intermediate_dir:
            return self.intermediate_dir
        try:
            return internal_json_artifact_dir(self.skill_dir)
        except (RuntimeError, ValueError):
            return self.temp_dir
    @classmethod
    def from_skill_dir(cls, skill_dir: str) -> PipelineContext:
        return cls(skill_dir=normalize_skill_dir(skill_dir))
def normalize_count(value: Any) -> int:
    if is_real_number(value):
        return max(0, int(value))
    return 0
def progress_of(sd: str) -> dict:
    try:
        return get_pipeline_progress(sd)
    except Exception as e:  # noqa: BLE001
        logger.warning("[PhaseHandler] 进度读取失败，降级占位视图: %s", e)
        return {"phase": "unknown", "error": str(e)[:200],
                "diagnosis": {}, "treatment": {}}
def _progress_view_or_empty(getter: Callable[[str], Any], sd: str,
                            label: str) -> dict:
    try:
        _progress = getter(sd)
    except Exception as e:  # noqa: BLE001
        logger.warning("[PhaseHandler] %s进度读取失败，降级空视图: %s", label, e)
        return {}
    if not isinstance(_progress, dict):
        logger.warning("[PhaseHandler] %s进度视图非 dict(%s)，降级空视图",
                       label, type(_progress).__name__)
        return {}
    return _progress
def treatment_progress_of(sd: str) -> dict:
    return _progress_view_or_empty(get_treatment_progress, sd, "治疗")
def diagnosis_progress_dict(sd: str) -> dict:
    return _progress_view_or_empty(get_diagnosis_progress, sd, "诊断")
def get_treatment_progress(skill_dir: str) -> dict:
    state = load_treatment_state(skill_dir)
    if not isinstance(state, dict):
        state = {}
    return treatment_progress(state)
_TREATMENT_COUNT_KEYS = TREATMENT_COUNT_KEYS
_EXEC_COUNT_KEYS = tuple(_k for _k in _TREATMENT_COUNT_KEYS
                         if _k not in ("total", "current_index"))
_TREATMENT_TRACE_COUNT_KEYS = tuple(_k for _k in _TREATMENT_COUNT_KEYS
                                    if _k != "current_index")
def _normalized_treatment_counts(state: dict) -> dict[str, int]:
    return {key: max(0, int_or(state.get(key, 0)))
            for key in _TREATMENT_COUNT_KEYS}
def _base_exec_result(state: dict) -> dict:
    _raw_status = state.get("status")
    counts = _normalized_treatment_counts(state)
    result = {
        "status": _coerce_status(_raw_status) or "",
        "total_items": counts["total"],
    }
    result.update({key: counts[key] for key in _EXEC_COUNT_KEYS})
    return result
def treatment_exec_result(skill_dir: str, *,
                          with_fix_coverage: bool = False) -> dict:
    treatment_state = get_treatment_progress(skill_dir)
    if not isinstance(treatment_state, dict):
        logger.warning("[TreatmentExec] 治疗进度视图非字典(%s)，按空视图继续",
                       type(treatment_state).__name__)
        treatment_state = {}
    exec_result = _base_exec_result(treatment_state)
    exec_result["details"] = [
        dict(item) for item in dict_items(treatment_state.get("items"))]
    if with_fix_coverage:
        exec_result["fix_coverage"] = dict_or_empty(
            treatment_state.get("fix_coverage"))
    return exec_result
def _phase_label(phase: str) -> str:
    if not isinstance(phase, str):
        return str(phase)
    label = _PHASE_LABELS.get(phase)
    return label if label else phase
_CV_DONE_PHASES = _phase_slice("cv_main_done")
def get_pipeline_progress(skill_dir: str) -> dict:
    sd = normalize_skill_dir(skill_dir)
    p_state = load_pipeline_state(sd)
    diag_progress = diagnosis_progress_dict(sd)
    treatment_progress = treatment_progress_of(sd)
    _phase_now = p_state.get("phase", _INITIAL_PHASE)
    _diag_view = diag_progress if isinstance(diag_progress, dict) else {}
    return {
        "phase": _phase_now,
        # 状态文件读取/签名验证失败时 load_pipeline_state 会降级为初始状态：
        # 透传该标记，让消费方（尤其是最终报告）能区分「真的还没开始」与
        # 「状态丢失」，不把降级快照当作事实。
        "state_load_error": str_or_empty(p_state.get("_state_load_error")),
        "round_start_ts": str_or_empty(p_state.get("round_start_ts")),
        "phase_label": _phase_label(_phase_now),
        "completed": _diag_view.get("completed"),
        "total": _diag_view.get("total"),
        "next_method": _diag_view.get("next_method"),
        "diagnosis": diag_progress,
        "treatment": treatment_progress,
        "cv_done": _phase_now in _CV_DONE_PHASES,
        "timestamp": p_state.get("timestamp", ""),
        "recovery_strategy": p_state.get("recovery_strategy", "from_start"),
        "source_hash": p_state.get("source_hash", ""),
        "resume_degraded": dict_or_empty(p_state.get(_RESUME_DEGRADED_KEY)),
    }
query_methods_progress = diagnosis_progress_dict
@dataclass(frozen=True, slots=True)
class _StepRun:
    skill_dir: str
    started_at: float
    @property
    def elapsed_s(self) -> float:
        return round(time.time() - self.started_at, 2)
_STEP_DONE_STATUS = "completed"
_PARENT_WATCHDOG_LOCK = threading.Lock()
_PARENT_WATCHDOG_INSTALLED = False
def install_parent_death_watchdog(*, poll_interval_ms: int = 1000) -> bool:
    global _PARENT_WATCHDOG_INSTALLED
    with _PARENT_WATCHDOG_LOCK:
        if _PARENT_WATCHDOG_INSTALLED:
            return True
        parent_pid = os.getppid()
        if parent_pid <= 0:
            return False
        try:
            worker = threading.Thread(
                target=_watch_parent_death,
                args=(parent_pid, max(100, int(poll_interval_ms))),
                name="jwsgj-parent-death-watchdog",
                daemon=True,
            )
            worker.start()
        except (RuntimeError, OSError) as exc:
            log_swallowed(__name__, exc,
                          context='install_parent_death_watchdog:start')
            return False
        _PARENT_WATCHDOG_INSTALLED = True
        logger.debug("[PipelineGuard] 父进程看门狗已安装 (ppid=%d)", parent_pid)
        return True
def _watch_parent_death(parent_pid: int, poll_interval_ms: int) -> None:
    try:
        if sys.platform == "win32":
            _watch_parent_death_windows(parent_pid, poll_interval_ms)
        else:
            _watch_parent_death_posix(parent_pid, poll_interval_ms)
    except BaseException as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context='_watch_parent_death')
def _watch_parent_death_windows(parent_pid: int, poll_interval_ms: int) -> None:
    _SYNCHRONIZE = 0x00100000
    _WAIT_OBJECT_0 = 0x00000000
    _WAIT_FAILED = 0xFFFFFFFF
    _ERROR_INVALID_PARAMETER = 0x00000057
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel32.OpenProcess.restype = wintypes.HANDLE
    kernel32.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
    kernel32.WaitForSingleObject.restype = wintypes.DWORD
    kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
    kernel32.CloseHandle.restype = wintypes.BOOL
    handle = kernel32.OpenProcess(_SYNCHRONIZE, False, parent_pid)
    if not handle:
        error = ctypes.get_last_error()
        if error == _ERROR_INVALID_PARAMETER:
            _terminate_on_parent_death(parent_pid)
            return
        logger.warning(
            "[PipelineGuard] 无法打开父进程 %d 句柄(error=%d)，"
            "看门狗降级停用，不终止当前进程", parent_pid, error)
        return
    try:
        while True:
            rc = kernel32.WaitForSingleObject(handle, poll_interval_ms)
            if rc == _WAIT_OBJECT_0:
                _terminate_on_parent_death(parent_pid)
                return
            if rc == _WAIT_FAILED:
                return
    finally:
        kernel32.CloseHandle(handle)
def _watch_parent_death_posix(parent_pid: int, poll_interval_ms: int) -> None:
    interval_s = max(poll_interval_ms, 100) / 1000.0
    while True:
        time.sleep(interval_s)
        if os.getppid() != parent_pid:
            _terminate_on_parent_death(parent_pid)
            return
        try:
            os.kill(parent_pid, 0)
        except ProcessLookupError:
            _terminate_on_parent_death(parent_pid)
            return
        except PermissionError:
            continue
def _terminate_on_parent_death(parent_pid: int) -> None:
    try:
        logger.warning(
            "[PipelineGuard] 父进程 %d 已退出，终止当前管线进程 (pid=%d)",
            parent_pid, os.getpid())
    except BaseException as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context='_terminate_on_parent_death:log')
    finally:
        os._exit(1)
class PipelineGuard:
    def __init__(self, skill_dir: str, step_name: str):
        _raw = (os.fspath(skill_dir) if isinstance(skill_dir, os.PathLike)
                else skill_dir)
        if not isinstance(_raw, str) or not _raw.strip():
            raise ValueError("skill_dir 为空，拒绝把管线守卫锁落到进程 cwd")
        self.skill_dir = os.path.abspath(_raw)
        self.step_name = step_name
        self._lock = ProcessLock(self.skill_dir, step_name)
        self._entered = False
    def enter(self, *, check_batch: bool = True) -> None:
        try:
            install_parent_death_watchdog()
        except BaseException as exc:  # noqa: BLE001
            log_swallowed(__name__, exc,
                          context='PipelineGuard.enter:parent_watchdog')
        if check_batch:
            BatchDetector.check_and_record(self.step_name, self.skill_dir)
        try:
            get_warmed_cache(self.skill_dir)
            self._lock.acquire()
        except Exception:
            if check_batch:
                BatchDetector._rollback_pending_record(
                    self.step_name, self.skill_dir)
            raise
        self._entered = True
        try:
            _register_signal_handlers()
        except Exception:
            try:
                self.exit()
            except Exception as _exit_err:  # noqa: BLE001
                logger.warning("[PipelineGuard] 进入失败释放守卫异常: %s", _exit_err)
            if check_batch:
                BatchDetector._rollback_pending_record(
                    self.step_name, self.skill_dir)
            raise
        logger.info("[PipelineGuard] 步骤 '%s' 守卫已激活 (pid=%d, 预热前置=已满足)",
                     self.step_name, os.getpid())
    def exit(self) -> None:
        if not self._entered:
            return
        try:
            self._lock.release()
        finally:
            self._entered = False
            _restore_signal_handlers()
    def __enter__(self) -> Self:
        self.enter()
        return self
    def __exit__(self, exc_type, exc_val, exc_tb) -> bool:
        self.exit()
        return False
def guarded_step(step_name: str) -> Callable[..., Any]:
    def decorator(func):
        @functools.wraps(func)
        def wrapper(skill_dir, *args, **kwargs):
            guard = PipelineGuard(skill_dir, step_name)
            try:
                guard.enter()
                return func(skill_dir, *args, **kwargs)
            finally:
                try:
                    guard.exit()
                except Exception as _exit_err:  # noqa: BLE001
                    logger.warning("[%s] 步骤守卫释放失败(已忽略): %s",
                                   step_name, _exit_err)
        wrapper._guarded_step = step_name
        return wrapper
    return decorator
@contextmanager
def pipeline_step_guard(skill_dir: str, step_name: str, provenance_label: str):
    guard = PipelineGuard(skill_dir, step_name)
    try:
        guard.enter()
        verify_provenance_logged(provenance_label, skill_dir)
        yield
    finally:
        try:
            guard.exit()
        except Exception as exit_err:  # noqa: BLE001
            logger.warning("[%s] 步骤守卫释放失败(已忽略): %s", step_name, exit_err)
def is_step_guard_blocked(exc: BaseException) -> bool:
    return isinstance(exc, ConcurrentExecutionError)
_signal_install_depth = 0
_saved_signal_handlers: dict[int, Any] = {}
def _signal_handler(signum, _frame):
    logger.warning("[PipelineGuard] 收到信号 %d，退出进程 (exit=1)", signum)
    sys.exit(1)
def _register_signal_handlers() -> None:
    global _signal_install_depth
    if threading.current_thread() is not threading.main_thread():
        return
    _signal_install_depth += 1
    if _signal_install_depth > 1:
        return
    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            _saved_signal_handlers[sig] = signal.getsignal(sig)
            signal.signal(sig, _signal_handler)
        except (OSError, ValueError):
            _saved_signal_handlers.pop(sig, None)
            logger.warning("[PipelineGuard] signal registration failed",
                           exc_info=True)
def _restore_signal_handlers() -> None:
    global _signal_install_depth
    if threading.current_thread() is not threading.main_thread():
        return
    if _signal_install_depth <= 0:
        return
    _signal_install_depth -= 1
    if _signal_install_depth:
        return
    for sig, handler in list(_saved_signal_handlers.items()):
        try:
            signal.signal(sig, handler)
        except (OSError, ValueError):
            logger.warning("[PipelineGuard] signal restore failed",
                           exc_info=True)
    _saved_signal_handlers.clear()
def _blocked_out(run: _StepRun, exc: ConcurrentExecutionError) -> dict:
    return {"status": "blocked", "reason": str(exc)[:500],
            "elapsed_s": run.elapsed_s}
def _failed_out(run: _StepRun, exc: Exception) -> dict:
    return {"status": "failed", "error": str(exc)[:500],
            "elapsed_s": run.elapsed_s}
def _record_step_run(module_name: str, entry: str, out: dict,
                     duration_ms: float, payload_fn) -> None:
    if not module_name:
        return
    try:
        payload = payload_fn(out) if payload_fn is not None else {}
        write_module_run(module_name, entry,
                         outcome=str(out.get("status", "ok")),
                         duration_ms=duration_ms, **payload)
    except Exception as _run_err:  # noqa: BLE001
        logger.warning("[%s] 模块运行留痕失败(不阻断): %s", entry, _run_err)
def run_step_shell(skill_dir: str, *, guard_name: str, label: str,
                   body, emit=None, perf_name: str = "",
                   module_name: str = "", entry: str = "",
                   payload_fn=None) -> dict:
    sd = normalize_skill_dir(skill_dir)
    run = _StepRun(sd, time.time())
    started = time.perf_counter()
    guard = None
    try:
        get_warmed_cache(sd)
        guard = PipelineGuard(sd, guard_name)
        guard.enter()
        verify_provenance_logged(label, sd)
        out = body(run)
        ProvenanceGuard.stamp(guard_name, out)
    except ConcurrentExecutionError as e:
        logger.warning("[%s] guard blocked: %s", label, e)
        out = _blocked_out(run, e)
    except Exception as e:
        out = _failed_out(run, e)
        logger.error("[%s] 失败: %s", label, e, exc_info=True)  # noqa: G201
    finally:
        if guard is not None:
            try:
                guard.exit()
            except Exception as _exit_err:
                logger.warning("[%s] 守卫释放失败(降级): %s", label,
                               _exit_err, exc_info=True)
    if emit is not None:
        try:
            emit(sd, out)
        except Exception as _ee:  # noqa: BLE001
            logger.warning("[%s] 步骤留痕失败(不阻断): %s", label, _ee)
    duration_ms = (time.perf_counter() - started) * 1000.0
    if perf_name:
        perf_trace(perf_name, duration_ms, function=entry)
    _record_step_run(module_name, entry, out, duration_ms, payload_fn)
    return out
def publish_step_result(channel: str, step_name: str, skill_dir: str,
                        result: dict) -> bool:
    if not isinstance(result, dict):
        logger.warning("[%s] 步骤结果非字典(%s)，按未完成处理",
                       step_name, type(result).__name__)
        return False
    if str(result.get("status", "")) != _STEP_DONE_STATUS:
        return False
    mem_bus_put(channel, result, skill_dir)
    archive_step_result(step_name, skill_dir, result)
    return True
ARCHIVE_DIRNAME = "pipeline_archive"
_ARCHIVE_KEEP_PER_STEP = 2
_ARCHIVE_TS_LEN = len(timestamp_ms())
_ARCHIVE_PEER_RE = re.compile(rf"\d{{{_ARCHIVE_TS_LEN}}}\.json")
_ARCHIVE_NAME_MAX = 80
def _archive_payload(step_name, skill_dir, result):
    payload = dict(result) if isinstance(result, dict) else {"result": result}
    payload["_step_name"] = step_name
    payload["_archived_at"] = timestamp_ms()
    payload["_schema_version"] = "1.0"
    try:
        anchor = payload.get("round_start_ts")
        if anchor is None or anchor == "":
            anchor = load_pipeline_state(skill_dir).get("round_start_ts")
        payload["round_start_ts"] = coerce_round_anchor_strict(anchor) or ""
    except Exception as _e:  # noqa: BLE001
        logger.debug('静默降级[archive_step_result:Exc]: %s: %s', type(_e).__name__, _e)
        payload["round_start_ts"] = ""
    return payload
def _archive_peer_names(arch_dir, name) -> list[str]:
    _prefix = f"{name}_"
    return sorted(
        p for p in os.listdir(arch_dir)
        if p.startswith(_prefix)
        and _ARCHIVE_PEER_RE.fullmatch(p[len(_prefix):]) is not None)
def _normalize_keep(keep) -> int:
    if isinstance(keep, int) and not isinstance(keep, bool):
        return keep
    if isinstance(keep, float) and math.isfinite(keep):
        return int(keep)
    return _ARCHIVE_KEEP_PER_STEP
def _write_archive_file(arch_dir: str, name: str, payload: dict) -> str:
    _text = json.dumps(payload, ensure_ascii=False, indent=2, default=str)
    _ms = compact_ts_to_ms(timestamp_ms())
    if _ms is None:
        _ms = int(time.time() * 1000)
    for _ in range(1000):
        path = os.path.join(arch_dir, f"{name}_{format_compact_ts(_ms)}.json")
        try:
            fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        except FileExistsError as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc, context='_write_archive_file:FileExistsError')
            _ms += 1
            continue
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as _af:
                _af.write(_text)
        except Exception:
            try:
                os.close(fd)
            except OSError as _swallowed_exc:
                log_swallowed(
                    __name__, _swallowed_exc, context='_write_archive_file:OSError')
            safe_delete(path)
            raise
        return path
    raise RuntimeError("归档文件名连续冲突")
def _prune_step_archives(arch_dir, name, keep):
    _keep = _normalize_keep(keep)
    _peers = _archive_peer_names(arch_dir, name)
    _to_prune = list(_peers) if _keep <= 0 else _peers[:-_keep]
    for _old in _to_prune:
        _old_path = os.path.join(arch_dir, _old)
        if not safe_delete(_old_path):
            logger.warning(
                "[Archive] 旧归档删除失败(剪裁未完成，存在膨胀风险): %s",
                _old)
def _register_archive_artifact(skill_dir, step_name, path):
    try:
        with _pipeline_state_locked(skill_dir):
            _state = load_pipeline_state(skill_dir)
            _artifacts = _state.setdefault("artifacts", {})
            _key = f"archive_{step_name}"
            if path:
                _artifacts[_key] = path
            else:
                _artifacts.pop(_key, None)
            save_pipeline_state(skill_dir, _state)
    except Exception:
        logger.debug("[Archive] artifacts 登记失败(忽略)", exc_info=True)
def archive_step_result(step_name: str, skill_dir: str, result: dict,
                         keep: int = _ARCHIVE_KEEP_PER_STEP) -> str:
    try:
        arch_dir = os.path.join(get_temp_dir(skill_dir), ARCHIVE_DIRNAME)
        os.makedirs(arch_dir, exist_ok=True)
        payload = _archive_payload(step_name, skill_dir, result)
        _name = _safe_archive_name(step_name)
        path = _write_archive_file(arch_dir, _name, payload)
        try:
            _prune_step_archives(arch_dir, _name, keep)
        except Exception as _pe:  # noqa: BLE001
            logger.warning("[Archive] 旧归档剪裁异常(本次归档已落盘): %s", _pe)
        _retained_path = path if os.path.isfile(path) else ""
        _register_archive_artifact(skill_dir, step_name, _retained_path)
        if _retained_path:
            logger.info("[Archive] 步骤结果已归档: %s -> %s",
                        step_name, _retained_path)
        return _retained_path
    except Exception as _ae:  # noqa: BLE001
        logger.warning("[Archive] 步骤结果归档失败(不阻断): %s", _ae)
        return ""
def _safe_archive_name(step_name: str) -> str:
    raw = str(step_name)
    safe = "".join(c if (c.isalnum() or c in "-_") else "_" for c in raw)
    if safe == raw and 0 < len(raw) <= _ARCHIVE_NAME_MAX:
        return raw
    digest = hashlib.sha256(
        raw.encode("utf-8", errors="replace")).hexdigest()[:12]
    stem = safe[:_ARCHIVE_NAME_MAX - len(digest) - 1] or "step"
    return f"{stem}_{digest}"
class _CachedMeta(NamedTuple):
    fingerprint: tuple
    status: str | None
    findings_count: int
    elapsed_s: float
    verdict: str = ""
    verdict_reason: str = ""
_PROGRESS_META_CACHE: dict[tuple[str, str], _CachedMeta] = {}
_PROGRESS_META_CACHE_MAX = 512
def _intermediate_source_fingerprint(intermediate_dir: str,
                                     freshness_cutoff: str) -> tuple:
    try:
        names = sorted(os.listdir(intermediate_dir))
    except OSError as e:
        logger.debug("中间结果目录快照失败（跳过缓存）: %s: %s",
                     intermediate_dir, e)
        return ()
    entries: list[tuple[str, int, int]] = []
    for name in names:
        if not name.endswith(".json"):
            continue
        try:
            _st = os.stat(os.path.join(intermediate_dir, name))
        except OSError as e:
            logger.debug("中间结果源文件 stat 失败（跳过缓存）: %s: %s",
                         name, e)
            return ()
        entries.append((name, _st.st_mtime_ns, _st.st_size))
    if not entries:
        return ()
    return (str(freshness_cutoff), tuple(entries))
def _load_method_meta(intermediate_dir: str, mid: str,
                      freshness_cutoff: str) -> dict | None:
    _cutoff = str(freshness_cutoff)
    _cache_key = (intermediate_dir, mid)
    _pre_fp = _intermediate_source_fingerprint(intermediate_dir, _cutoff)
    _hit = _read_cached_meta(_cache_key, _pre_fp)
    if _hit is not None:
        return _hit
    data = load_intermediate(intermediate_dir, mid,
                             strict_provenance=False,
                             freshness_cutoff=freshness_cutoff)
    if not isinstance(data, dict):
        return data
    _meta = (data.get("status"), data.get("findings_count", 0),
             data.get("elapsed_s", 0), data.get("verdict", ""),
             data.get("verdict_reason", ""))
    _store_cached_meta(_cache_key, intermediate_dir, _cutoff,
                       _pre_fp, _meta)
    return _meta_payload(*_meta)
def _read_cached_meta(cache_key: tuple[str, str],
                      fingerprint: tuple) -> dict | None:
    if not fingerprint:
        return None
    cached = _PROGRESS_META_CACHE.get(cache_key)
    if not cached:
        return None
    if cached.fingerprint != fingerprint:
        return None
    return _meta_payload(cached.status, cached.findings_count,
                         cached.elapsed_s, cached.verdict,
                         cached.verdict_reason)
def _store_cached_meta(cache_key: tuple[str, str], intermediate_dir: str,
                       freshness_cutoff: str, pre_fp: tuple,
                       meta: tuple) -> None:
    if not pre_fp:
        return
    if _intermediate_source_fingerprint(
            intermediate_dir, freshness_cutoff) != pre_fp:
        return
    if (cache_key not in _PROGRESS_META_CACHE
            and len(_PROGRESS_META_CACHE) >= _PROGRESS_META_CACHE_MAX):
        _PROGRESS_META_CACHE.clear()
    _PROGRESS_META_CACHE[cache_key] = _CachedMeta(pre_fp, *meta)
def _meta_payload(status, findings_count, elapsed_s,
                  verdict="", verdict_reason="") -> dict:
    return {
        "status": _coerce_status(status),
        "findings_count": max(0, int_or(findings_count)),
        "elapsed_s": max(0.0, safe_float(elapsed_s, 0.0)),
        "verdict": _coerce_status(verdict) or "",
        "verdict_reason": (verdict_reason
                           if isinstance(verdict_reason, str) else ""),
    }
def _coerce_status(value: Any) -> str | None:
    if isinstance(value, str):
        text = value.strip().lower()
        return text or None
    return None
def _meta_status(meta) -> str | None:
    return _coerce_status(meta.get("status")) if isinstance(meta, dict) else None
def _is_terminal_status(status: str | None) -> bool:
    return status in TERMINAL_STATUSES
def _judge_effective_done(all_mids: list, raw_meta: dict) -> dict[str, bool]:
    return {
        mid: _is_terminal_status(_meta_status(raw_meta.get(mid)))
        for mid in all_mids
    }
def _collect_raw_meta(intermediate_dir: str, all_mids: list,
                      round_ts: str) -> dict:
    _raw_meta: dict[str, Any] = {}
    for mid in all_mids:
        try:
            _raw_meta[mid] = _load_method_meta(
                intermediate_dir, mid, freshness_cutoff=round_ts)
        except Exception as exc:  # noqa: BLE001
            logger.warning(
                "[Pipeline] 诊断中间结果读取失败，按未完成处理: %s (%s)",
                mid, exc)
            _raw_meta[mid] = None
    return _raw_meta
_DEGRADED_DETAIL_STATUSES = frozenset(
    {"skip", "missing", "corrupted", "error"})
def _partition_progress(all_mids: list, effective_done: dict,
                        raw_meta: dict) -> tuple[list, list, list]:
    completed: list = []
    pending: list = []
    details: list = []
    for mid in all_mids:
        _st = _meta_status(raw_meta.get(mid))
        if effective_done.get(mid):
            completed.append(mid)
            details.append(_detail_entry(mid, raw_meta.get(mid), _st or "pending", True))
        else:
            pending.append(mid)
            details.append(_detail_entry(
                mid, raw_meta.get(mid),
                _st if _st in _DEGRADED_DETAIL_STATUSES else "pending",
                False))
    return completed, pending, details
def _detail_entry(mid: str, data, status: str, completed: bool) -> dict:
    cfg = METHOD_REGISTRY.get(mid)
    entry = {
        "method_id": mid,
        "method_name": cfg.name if cfg else mid,
        "status": status,
        "completed": completed,
    }
    if isinstance(data, dict):
        entry["verdict"] = _coerce_status(data.get("verdict")) or ""
        entry["verdict_reason"] = (
            data.get("verdict_reason")
            if isinstance(data.get("verdict_reason"), str) else "")
    if completed:
        entry["findings_count"] = data.get("findings_count", 0) if isinstance(data, dict) else 0
        entry["elapsed_s"] = data.get("elapsed_s", 0) if isinstance(data, dict) else 0
    return entry
def get_diagnosis_progress(skill_dir: str) -> dict:
    skill_dir, _output_dir, intermediate_dir = resolve_intermediate_dirs(skill_dir)
    _round_ts = get_round_start_ts(skill_dir)
    all_mids = all_method_ids()
    _raw_meta = _collect_raw_meta(intermediate_dir, all_mids, _round_ts)
    _effective_done = _judge_effective_done(all_mids, _raw_meta)
    completed, pending, details = _partition_progress(
        all_mids, _effective_done, _raw_meta)
    return {
        "total": len(all_mids),
        "completed": len(completed),
        "pending": len(pending),
        "pending_methods": pending,
        "next_method": pending[0] if pending else None,
        "completed_methods": completed,
        "details": details,
        "all_methods": all_mids,
    }
def cleanup_legacy_fix_route_report(sd: str) -> None:
    _rr_path = first_json_artifact(sd, "_fix_route_report.json")
    if not _rr_path:
        return
    try:
        if not safe_delete(_rr_path):
            logger.warning(
                "[TreatmentPlanStep] 历史遗留路由报告清理失败"
                "（safe_delete 返回 False，降级不阻断）: %s", _rr_path)
    except OSError as _rr_e:
        logger.warning(
            "[TreatmentPlanStep] 历史遗留路由报告清理异常"
            "（降级不阻断）: %s: %s", _rr_path, _rr_e)
def _phase_method_entries(phase) -> list[dict]:
    entries = []
    for mid in phase.methods:
        cfg = METHOD_REGISTRY.get(mid)
        if cfg is None:
            logger.warning(
                "[Pipeline] 阶段方法未登记，按占位展示: phase=%s mid=%s",
                phase.name, mid)
            entries.append({
                "id": mid,
                "name": mid,
                "domain": "",
                "phase": phase.name,
                "produces_findings": False,
                "depends_on": [],
            })
            continue
        entries.append({
            "id": mid,
            "name": cfg.name,
            "domain": cfg.domain,
            "phase": phase.name,
            "produces_findings": cfg.produces_findings,
            "depends_on": list(cfg.depends_on),
        })
    return entries
def list_methods() -> list[dict]:
    result = []
    for phase in PHASES:
        result.extend(_phase_method_entries(phase))
    result.extend(_phase_method_entries(TREATMENT_PHASE))
    return result
def resolve_method_id(sd: str, method_id: str | None):
    if method_id is not None and not isinstance(method_id, str):
        raise TypeError(
            f"method_id 须为 str 或 None，实际为 "
            f"{type(method_id).__name__}: {method_id!r}")
    if method_id is None:
        progress = get_diagnosis_progress(sd)
        if progress["next_method"] is None:
            return None, {
                "status": "all_completed",
                "message": ("所有诊断方法已执行完成，可调用 "
                            "pipeline_trigger_route.run_next_pipeline_step(skill_dir) "
                            "执行后续阶段"),
                "progress": progress,
            }
        method_id = progress["next_method"]
        logger.info("[DiagnosisStep] 自动选择下一个待执行方法: %s", method_id)
    method_id = method_id.strip().upper()
    if method_id not in METHOD_REGISTRY:
        raise ValueError(
            f"未注册的方法 ID: {method_id}，"
            f"可用: {all_method_ids()}"
        )
    return method_id, None
_STATUS_DISPLAY = {
    "pass": "✓pass",
    "warn": "⚠warn",
    "fail": "✗fail",
    "skip": "−skip",
}
def _collect_done_status(intermediate_dir: str, methods: list,
                         skill_dir: str) -> dict:
    done_status = {}
    if not os.path.isdir(intermediate_dir):
        return done_status
    _round_ts = get_round_start_ts(skill_dir)
    for method in methods:
        mid = method["id"]
        try:
            meta = _load_method_meta(intermediate_dir, mid, _round_ts)
        except Exception as exc:  # noqa: BLE001
            logger.warning("[CLI] 中间结果读取失败，按未完成展示: %s (%s)",
                           mid, exc)
            continue
        status = _meta_status(meta)
        if status is not None:
            done_status[mid] = status
    return done_status
def _missing_dependencies(deps: list, effective_done: dict) -> list:
    return [d for d in deps if not effective_done.get(d, False)]
def _status_cell(status: str | None) -> str:
    if status in _STATUS_DISPLAY:
        return _STATUS_DISPLAY[status]
    if status in ("error", "timeout", "corrupted", "missing"):
        return f"✗{status}"
    return "  待执行"
def _dependency_hint(deps: list, missing: list) -> str:
    if not deps:
        return ""
    return f"需先执行: {','.join(missing)}" if missing else "依赖已就绪"
def _execution_marker(completed: bool, deps: list,
                      missing: list) -> str:
    if completed or (deps and missing):
        return " "
    return "→"
def _method_row(seq: int, method: dict, done_status: dict,
                effective_done: dict) -> str:
    mid = method["id"]
    deps = method.get("depends_on", [])
    st = done_status.get(mid)
    _missing = _missing_dependencies(deps, effective_done)
    _completed = effective_done.get(mid, False)
    return (f"{seq:>3d}{_execution_marker(_completed, deps, _missing)}"
            f" {mid:>4s} | {method['name']:<20s} | {_status_cell(st):<6s} | "
            f"{method['phase']:<14s} | {(','.join(deps) if deps else '-'):<12s} | "
            f"{_dependency_hint(deps, _missing)}")
def _cli_command_hint(args: str = "") -> str:
    _module = (f"{__package__}.pipeline_trigger_route"
               if __package__ else "pipeline_trigger_route")
    return f"python -m {_module}" + (f" {args}" if args else "")
def _render_method_table(methods: list, done_status: dict) -> None:
    method_ids = [method["id"] for method in methods]
    raw_meta = {mid: {"status": done_status[mid]}
                for mid in method_ids if mid in done_status}
    effective_done = _judge_effective_done(method_ids, raw_meta)
    done_count = sum(1 for mid in method_ids if effective_done.get(mid, False))
    print(f"\n执行进度: {done_count}/{len(methods)} 已完成")
    print()
    print(f"{'序号':>4s}  {'ID':>4s} | {'名称':<20s} | {'状态':<6s} | {'阶段':<14s} | 依赖          | 提示")
    print("-" * 86)
    for seq, method in enumerate(methods, start=1):
        print(_method_row(seq, method, done_status, effective_done))
    print("-" * 86)
    print(f"共 {len(methods)} 个方法 | ✓已完成 {done_count} | 待执行 {len(methods) - done_count}")
    print("标记说明: → = 下一个可执行 | ✓=已完成 | ⚠=有警告 | ✗=失败/错误 | −=跳过")
    print(f"执行命令: {_cli_command_hint('<方法ID>')}")
def render_method_status_table(output_dir: str, skill_dir: str) -> None:
    methods = list_methods()
    done_status = _collect_done_status(
        resolve_intermediate_dirs(skill_dir, output_dir)[2], methods, skill_dir)
    _render_method_table(methods, done_status)

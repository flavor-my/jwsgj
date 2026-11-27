# ruff: noqa: I001
from __future__ import annotations
from collections.abc import Callable
import hashlib
import json
import logging
import os
import re
import sys
import threading
import time
from dataclasses import dataclass, field
from typing import Any
from jwsgj.ai_review_governance import (
    MAX_AI_REVIEW_ITEMS,
    read_pending_reviews,
    run_all_ai_reviews,
)
from jwsgj.build_text_scoring import (
    PIPELINE_TRIGGER_KEYWORDS,
    TRIGGER_CONTEXT_TOKENS,
    TRIGGER_NEGATIVE_CONTEXTS,
    TRIGGER_WEAK_TOKENS,
    VERB_SYNONYM_EXPANSION,
    load_custom_trigger_keywords,
    match_pipeline_trigger,
    normalize_trigger_text,
    probe_pipeline_trigger,
    seed_token_pairs,
    trigger_tokens,
    validate_pipeline_trigger_contract,
)
from jwsgj.cleanup_residue import cleanup_after_diagnosis
from jwsgj.diag_guard_io import (
    atomic_write_text,
    diagnosis_readonly_scope,
)
from jwsgj.diag_method_invoke import run_single_method
from jwsgj.diag_solidify_rules import (
    invalidate_solidified_ssot,
    load_solidified_ssot,
)
from jwsgj.diag_types_defs import (
    ConcurrentExecutionError,
)
from jwsgj.diag_types_normalize import (
    safe_float,
    safe_isfinite,
    signal_bool,
)
from jwsgj.diag_types_vocab import DIAGNOSIS_METHOD_BUDGET_S
from jwsgj.html_report_stage_doc import stage_report_batch
from jwsgj.html_render_pipeline import (
    emit_single_method_html,
    emit_step_html,
    generate_html_report,
)
from jwsgj.log_config import (
    TRIGGER_EVENTS_FILE,
    append_jsonl_locked,
    get_log_dir,
    locked_artifact,
    log_swallowed,
    now_iso_seconds,
    parse_log_ts,
)
from jwsgj.pipeline_report_assembly import aggregate_report
from jwsgj.pipeline_report_delivery import finalize_pipeline_reports
from jwsgj.pipeline_round_trace import (
    PipelineGuard,
    _cli_command_hint,
    advance_diagnosis_done,
    advance_pipeline_phase,
    check_diagnosis_reusable,
    diagnosis_fresh_complete,
    diagnosis_progress_dict,
    ensure_diagnosis_round,
    get_pipeline_progress,
    get_treatment_progress,
    list_methods,
    load_pipeline_state,
    progress_of,
    render_method_status_table,
    resolve_method_id,
    resume_phase,
    treatment_progress_of,
    treatment_trace_metrics,
)
from jwsgj.pipeline_steps_phases import (
    advance_phase_safe,
    attach_pending_review_info,
    execute_treatment_item,
    iter_shell_steps,
    phase_reached,
    run_phase_handler,
    stay_result,
    step_result,
)
from jwsgj.runtime_paths import (
    TRIGGER_ENFORCEMENT_FILENAME,
    diag_intermediate_dir,
    get_temp_dir,
    is_artifact_destination_allowed,
    json_artifact_dir,
)
from jwsgj.runtime_scope import (
    normalize_skill_dir,
)
from jwsgj.shared_cache import (
    BatchDetector,
    CacheNotWarmedError,
    clear_all_process_memory,
    get_warmed_cache,
    set_handoff_persistence,
)
from jwsgj.treatment_state import (
    treatment_save_deferral,
)
from jwsgj.xv_cv_report_assemble import build_f1_report
__all__ = [
    'MINER_NOISE_TOKENS',
    'finalize_diagnosis_stage',
    'main',
    'mine_trigger_events',
    'read_trigger_events',
    'record_trigger_event',
    'render_miner_report',
    'run_batch_diagnosis_methods',
    'run_diagnosis_step',
    'run_next_pipeline_step',
    'run_pipeline_batch',
    'run_pipeline_from_trigger',
]
logger = logging.getLogger(__name__)
_FAILED_STEP_STATUSES: frozenset[str] = frozenset(
    {"blocked", "failed", "error"})
def _post_diagnosis_temp_cleanup(skill_dir: str) -> None:
    try:
        cleanup_after_diagnosis(skill_dir)
    except Exception:
        logger.warning("[PipelineNext] 诊断后Temp清理钩子异常（已忽略）",
                       exc_info=True)
def finalize_diagnosis_stage(sd: str, progress, **extra) -> None:
    advance_diagnosis_done(sd, progress, **extra)
    _post_diagnosis_temp_cleanup(sd)
def _emit_html_soft(emitter, tag: str, label: str, *args) -> None:
    if not callable(emitter):
        return
    try:
        emitter(*args)
    except Exception as exc:  # noqa: BLE001
        logger.warning("[%s] %s HTML 生成失败(不阻断): %s", tag, label, exc)
def _run_with_error_sentinel(action, sentinel: dict, emit_html=None,
                             label: str = "") -> dict:
    try:
        res = action()
    except CacheNotWarmedError:
        raise
    except Exception as _e:  # noqa: BLE001
        logger.warning("[PipelineBatch] %s: %s", label or "子步骤异常", _e)
        res = {**sentinel, "status": "error", "error": str(_e)[:500]}
        _emit_html_soft(emit_html, "PipelineBatch", label or "子步骤异常", res)
        return res
    if isinstance(res, dict):
        return res
    logger.warning("[PipelineBatch] %s 返回非映射(%s)，按 error 归一",
                   label or "子步骤", type(res).__name__)
    res = {**sentinel, "status": "error",
           "error": f"子步骤返回非映射: {type(res).__name__}"}
    _emit_html_soft(emit_html, "PipelineBatch", label or "子步骤", res)
    return res
def _diagnose_once(sd: str, mid: str, *, output_dir: str | None = None,
                   cache=None, internal: bool = False,
                   capture_errors: bool = True) -> dict:
    def _call() -> dict:
        return run_single_method(
            sd, mid, output_dir=output_dir, resume=True, cache=cache,
            report_provider=build_f1_report, _internal=internal)
    with diagnosis_readonly_scope(sd):
        if capture_errors:
            res = _run_with_error_sentinel(
                _call, {"method_id": mid}, label="诊断异常哨兵")
        else:
            res = _call()
    _emit_html_soft(emit_single_method_html, "DiagnosisStep", "诊断留痕",
                    res, sd)
    return res
def run_batch_diagnosis_methods(sd: str, max_steps: int,
                                step_results: list[dict],
                                output_dir: str, cache, *,
                                should_stop: Callable[[], bool] | None = None) -> str:
    while True:
        progress = diagnosis_progress_dict(sd)
        mid = progress.get("next_method")
        if mid is None:
            break
        if should_stop is not None and should_stop():
            return "time_budget_exceeded"
        if len(step_results) >= max_steps:
            return "max_steps_reached"
        res = _diagnose_once(sd, mid, output_dir=output_dir, cache=cache,
                             internal=True)
        _derr = res.get("error", "")
        step_results.append({
            "task_type": "diagnosis",
            "method_id": mid,
            "status": res.get("status", "unknown"),
            "verdict": res.get("verdict", ""),
            "verdict_reason": res.get("verdict_reason", ""),
            "findings_count": _as_count(res.get("findings_count")),
            "elapsed_s": _as_float(res.get("elapsed_s")),
            **({"error": _derr} if _derr else {}),
        })
        if str(res.get("status", "")) in _FAILED_STEP_STATUSES:
            return "diagnosis_error"
    return ""
def _release_process_cache_soft(error_label: str, ok_label: str = "",
                                *, skill_dir: str) -> None:
    try:
        invalidate_solidified_ssot(skill_dir)
    except Exception:
        logger.warning("[DiagnosisStep] 固化 SSOT 失效失败(降级)", exc_info=True)
    try:
        clear_all_process_memory(skill_dir=skill_dir)
        if ok_label:
            logger.info("[DiagnosisStep] %s", ok_label)
    except Exception:
        logger.warning("[DiagnosisStep] %s", error_label, exc_info=True)
def _run_method_and_collect_progress(sd: str, method_id: str):
    result = _diagnose_once(sd, method_id, capture_errors=False)
    return result, diagnosis_progress_dict(sd)
def _log_method_completion(method_id: str, result: dict, progress: dict,
                           *, skill_dir: str) -> None:
    logger.info("[DiagnosisStep] %s 完成: status=%s, findings=%s, elapsed=%.1fs",
                method_id, result.get("status"),
                _as_count(result.get("findings_count")),
                _as_float(result.get("elapsed_s")))
    if not progress:
        logger.warning("[DiagnosisStep] 进度视图不可用（已降级为空），"
                       "跳过收口判定与缓存释放")
        return
    _next = progress.get("next_method")
    _completed = progress.get("completed", 0)
    _total = progress.get("total", 0)
    if _next:
        logger.info("[DiagnosisStep] 下一个待执行方法: %s (进度: %s/%s)",
                    _next, _completed, _total)
    else:
        logger.info("[DiagnosisStep] 全部诊断方法已执行完成! (%s/%s)",
                    _completed, _total)
        _release_process_cache_soft("缓存释放跳过", skill_dir=skill_dir)
def _handle_blocked(sd: str, method_id: str, err: Exception) -> dict:
    logger.warning("[DiagnosisStep] 并发执行被阻止: %s", err)
    _blocked = {"status": "blocked", "reason": str(err)[:500],
                "method_id": method_id, "elapsed_s": 0.0}
    _emit_html_soft(emit_single_method_html, "DiagnosisStep", "blocked 留痕",
                    _blocked, sd)
    return _blocked
def _build_step_payload(method_id: str, result: dict, progress: dict) -> dict:
    return {
        "method_id": method_id,
        "method_name": result.get("method_name", ""),
        "status": result.get("status", "unknown"),
        "verdict": result.get("verdict", ""),
        "verdict_reason": result.get("verdict_reason", ""),
        "findings_count": result.get("findings_count", 0),
        "elapsed_s": result.get("elapsed_s", 0),
        "summary": result.get("summary", ""),
        "error": result.get("error"),
        "progress": progress,
        "next_method": progress.get("next_method"),
    }
def _exit_guard_soft(guard: PipelineGuard, label: str) -> None:
    try:
        guard.exit()
    except Exception as exc:
        logger.warning("[%s] 守卫释放失败(降级): %s", label, exc, exc_info=True)
def run_diagnosis_step(skill_dir: str, method_id: str | None = None) -> dict:
    sd = normalize_skill_dir(skill_dir, require_valid=True)
    load_solidified_ssot(sd, force=False)
    method_id, _early = resolve_method_id(sd, method_id)
    if _early is not None:
        return _early
    guard = PipelineGuard(sd, "diagnosis")
    try:
        guard.enter()
        result, progress = _run_method_and_collect_progress(sd, method_id)
    except ConcurrentExecutionError as e:
        log_swallowed(__name__, e, context='run_diagnosis_step:ConcurrentExecutionError')
        return _handle_blocked(sd, method_id, e)
    except Exception as _de:
        _emit_html_soft(
            emit_single_method_html, "DiagnosisStep", "异常留痕",
            {"status": "error", "method_id": method_id,
             "error": str(_de)[:500], "elapsed_s": 0.0}, sd)
        _release_process_cache_soft("中断缓存释放跳过",
                                    ok_label="诊断中断，进程内缓存已释放",
                                    skill_dir=sd)
        raise
    else:
        _log_method_completion(method_id, result, progress, skill_dir=sd)
        return _build_step_payload(method_id, result, progress)
    finally:
        _exit_guard_soft(guard, "DiagnosisStep")
def _cli_resolve_output_dir(skill_dir: str) -> str:
    _output_env = os.environ.get("JWS_OUTPUT_DIR", "")
    if _output_env:
        if not is_artifact_destination_allowed(_output_env):
            print(f"错误: JWS_OUTPUT_DIR={_output_env!r} 不是合法产物落点"
                  "（产物落点只能是会话工作空间，含经工作空间守卫的"
                  " JWSGJ_TEMP_ROOT 显式产物根；不设其他位置兜底）")
            sys.exit(1)
        return _output_env
    return json_artifact_dir(skill_dir)
def _cli_list_mode(output_dir: str, skill_dir: str) -> None:
    render_method_status_table(output_dir, skill_dir)
    sys.exit(0)
def _cli_aggregate_mode(output_dir: str, skill_dir: str) -> None:
    intermediate_dir = diag_intermediate_dir(output_dir)
    if not os.path.isdir(intermediate_dir):
        print(f"错误: 中间结果目录不存在: {intermediate_dir}")
        print(f"请先逐个执行方法: {_cli_command_hint('<method_id>')}")
        sys.exit(1)
    report_path = aggregate_report(
        intermediate_dir, output_dir, skill_dir=skill_dir)
    if not report_path:
        print("错误: 最终报告生成失败（聚合构建异常，详见日志）")
        sys.exit(1)
    print(f"最终报告已生成: {report_path}")
    sys.exit(0)
def _cli_single_method_mode(command: str, skill_dir: str, output_dir: str) -> None:
    try:
        method_id, _ = resolve_method_id(skill_dir, command)
    except (TypeError, ValueError) as exc:
        log_swallowed(
            __name__, exc,
            context=f"_cli_single_method_mode:{type(exc).__name__}")
        print(f"错误: {exc}")
        sys.exit(1)
    load_solidified_ssot(skill_dir, force=False)
    with diagnosis_readonly_scope(skill_dir):
        result = run_single_method(skill_dir, method_id,
                                   output_dir=output_dir,
                                   resume=True,
                                   report_provider=build_f1_report)
    emit_single_method_html(result, skill_dir)
    print(f"method_id:   {result.get('method_id', method_id)}")
    print(f"method_name: {result.get('method_name', '')}")
    print(f"domain:      {result.get('domain', '')}")
    print(f"status:      {result.get('status', 'unknown')}")
    print(f"findings:    {result.get('findings_count', 0)}")
    print(f"elapsed_s:   {result.get('elapsed_s', 0)}")
    print(f"summary:     {result.get('summary', '')[:200]}")
    if result.get('error'):
        print(f"error:       {result['error'][:200]}")
    intermediate_dir = diag_intermediate_dir(output_dir)
    print(f"saved_to:    {intermediate_dir}/")
def main():
    if len(sys.argv) < 2:
        _cli = _cli_command_hint()
        print("用法:")
        print(f"  {_cli} <method_id>   # 执行单个方法")
        print(f"  {_cli} aggregate      # 汇总交叉验证")
        print(f"  {_cli} list           # 列出全部方法")
        print(f"可用方法 ID: {[m['id'] for m in list_methods()]}")
        print("可用环境变量: JWSGJ_SKILL_DIR=<技能或Python项目目录> "
              "指定诊断目标（默认诊断当前工作目录）")
        sys.exit(1)
    command = sys.argv[1].strip()
    configured_skill_dir = os.environ.get("JWSGJ_SKILL_DIR", "").strip()
    skill_dir = (normalize_skill_dir(configured_skill_dir)
                 if configured_skill_dir
                 else normalize_skill_dir(os.getcwd()))
    output_dir = _cli_resolve_output_dir(skill_dir)
    if command == "list":
        _cli_list_mode(output_dir, skill_dir)
    elif command == "aggregate":
        _cli_aggregate_mode(output_dir, skill_dir)
    else:
        _cli_single_method_mode(command, skill_dir, output_dir)
def _release_method_memory(note: str = "", *, skill_dir: str) -> None:
    try:
        clear_all_process_memory(keep_shared_cache=True, skill_dir=skill_dir)
        if note:
            logger.info(
                "[PipelineNext] %s，方法级缓存已释放（共享缓存驻留复用）", note)
    except Exception:
        logger.warning("[PipelineNext] 缓存释放跳过", exc_info=True)
def _finalize_terminal_step(sd: str, result: dict) -> dict:
    try:
        degradation_report = finalize_pipeline_reports(sd)
    except Exception:
        logger.warning("[PipelineNext] 终态报告定稿失败(不阻断)", exc_info=True)
        degradation_report = None
    task_result = result.get("task_result")
    if isinstance(task_result, dict):
        task_result["degradation_report"] = degradation_report
    try:
        released = clear_all_process_memory(skill_dir=sd)
        logger.info("[PipelineNext] 管道完成，已统一释放进程内缓存: %s", released)
    except Exception:
        logger.warning("[PipelineNext] 缓存释放跳过", exc_info=True)
    return result
def _pns_try_reuse_diagnosis(sd: str) -> dict | None:
    reuse = _as_dict(check_diagnosis_reusable(sd))
    if not reuse.get("reusable"):
        return None
    _reuse_reason = reuse.get("reason", "")
    logger.info("[PipelineNext] 源码未变更，复用历史诊断结果（%s）", _reuse_reason)
    finalize_diagnosis_stage(
        sd, diagnosis_progress_dict(sd), diagnosis_reused=True,
        reuse_reason=_reuse_reason)
    _release_method_memory("诊断阶段完成", skill_dir=sd)
    _reuse_payload = {"status": "diagnosis_reused", "reason": _reuse_reason}
    _emit_html_soft(emit_step_html, "PipelineNext", "复用留痕",
                    "diagnosis_reuse", sd, _reuse_payload)
    return step_result(
        "pending_diagnosis", "阶段1完成: 诊断结果复用（源码未变更）",
        "diagnosis_reuse", _reuse_payload,
        "diagnosis_done", get_pipeline_progress(sd))
def _pns_prepare_new_round(sd: str) -> None:
    _release_method_memory(skill_dir=sd)
    ensure_diagnosis_round(sd)
def _pns_run_pending_diagnosis(sd: str) -> dict:
    task_result = run_diagnosis_step(sd)
    new_progress = diagnosis_progress_dict(sd)
    next_phase = "pending_diagnosis"
    if diagnosis_fresh_complete(new_progress):
        finalize_diagnosis_stage(sd, new_progress)
        next_phase = "diagnosis_done"
        _release_note = "诊断阶段完成"
    else:
        _release_note = "诊断步骤完成"
    _release_method_memory(_release_note, skill_dir=sd)
    return step_result(
        "pending_diagnosis", "阶段1: 诊断方法执行中", "diagnosis",
        task_result, next_phase, new_progress)
def _pns_close_diagnosis_phase(sd: str) -> dict:
    _adv_diag = diagnosis_progress_dict(sd)
    finalize_diagnosis_stage(sd, _adv_diag)
    _close_payload = {
        "status": "diagnosis_complete",
        "completed": _adv_diag.get("completed", 0),
        "total": _adv_diag.get("total", 0),
    }
    _emit_html_soft(emit_step_html, "PipelineNext", "收口留痕",
                   "diagnosis_complete", sd, _close_payload)
    return step_result(
        "pending_diagnosis", "阶段1完成: 所有诊断方法已执行完成",
        "diagnosis_complete", _close_payload,
        "diagnosis_done", get_pipeline_progress(sd))
def _pns_handle_pending_diagnosis(sd: str, phase: str) -> dict | None:
    if phase != "pending_diagnosis":
        return None
    _reuse_result = _pns_try_reuse_diagnosis(sd)
    if _reuse_result is not None:
        return _reuse_result
    _pns_prepare_new_round(sd)
    if diagnosis_fresh_complete(diagnosis_progress_dict(sd)):
        return _pns_close_diagnosis_phase(sd)
    return _pns_run_pending_diagnosis(sd)
def _pns_self_heal_unknown_phase(sd: str, phase: str) -> dict:
    try:
        advance_pipeline_phase(sd, "pending_diagnosis",
                                advance_kind="self_heal")
    except Exception as exc:
        logger.warning("[PipelineNext] 未知阶段回退失败（下次调用仍将重试）", exc_info=True)
        return stay_result(
            sd, phase, f"未知阶段: {phase}（回退写盘失败，停留待重试）",
            "unknown", str(exc)[:500])
    logger.warning("[PipelineNext] 未知阶段 %s，已回退 pending_diagnosis 自愈", phase)
    return step_result(
        phase, f"未知阶段: {phase}（已回退 pending_diagnosis，下次调用重新路由）",
        "unknown", {"status": "unknown_phase", "phase": phase},
        "pending_diagnosis", progress_of(sd))
def run_next_pipeline_step(skill_dir: str, *,
                           _internal: bool = False) -> dict:
    sd = normalize_skill_dir(skill_dir, require_valid=True)
    if not _internal:
        BatchDetector.check_and_record("next_pipeline_step", sd)
    try:
        get_warmed_cache(sd)
    except Exception:
        if not _internal:
            BatchDetector._rollback_pending_record("next_pipeline_step", sd)
        raise
    phase = resume_phase(sd)
    _pending_result = _pns_handle_pending_diagnosis(sd, phase)
    if _pending_result is not None:
        return _pending_result
    _phase_result = run_phase_handler(phase, sd)
    if _phase_result is not None:
        if _phase_result.get("is_terminal"):
            return _finalize_terminal_step(sd, _phase_result)
        return _phase_result
    return _pns_self_heal_unknown_phase(sd, phase)
# 批量推进的单次预算：不得短于单个方法预算，否则「一步还没跑完就到点」，
# 每轮都要重启进程重新 import 200+ 模块。单一真源见
# ``diag_types_vocab.DIAGNOSIS_METHOD_BUDGET_S``。
DEFAULT_BATCH_MAX_SECONDS = DIAGNOSIS_METHOD_BUDGET_S


@dataclass
class _BatchRun:
    step_results: list = field(default_factory=list)
    stopped_reason: str = ""
    treatment_count: int = 0
    diagnosis_reused: bool = False
    consumed_phase: str = ""
    deadline: float = 0.0


def _batch_budget_exhausted(run: _BatchRun) -> bool:
    """时间预算是否耗尽（单次批量调用的墙钟上限）。"""
    if run.deadline <= 0:
        return False
    if time.time() < run.deadline:
        return False
    if not run.stopped_reason:
        run.stopped_reason = "time_budget_exceeded"
    return True
_TREATMENT_STREAK_LIMIT = 3


def _batch_run_treatment_items(
    sd: str, max_steps: int, step_results: list[dict], *,
    should_stop: Callable[[], bool] | None = None,
) -> tuple[str, int]:
    """逐条推进治疗项。

    单条失败不是整批失败：失败/无修复器都是合法中间态，其条目的终态裁决由
    AI 审核环节完成；原实现遇到一条 failed 就停整个批次（stopped_reason=
    treatment_error），使前序成果全部搁置、必须重启进程重跑，是重复劳动的
    主要来源。现改为：失败持续计数，连续 3 条无进展才停（防死循环）。
    """
    skipped_streak = 0
    failed_streak = 0
    stopped_reason = ""
    treatment_count = 0
    with treatment_save_deferral(sd), stage_report_batch():
        while True:
            prog = treatment_progress_of(sd)
            if prog.get("status") in ("completed", "no_plan"):
                break
            if should_stop is not None and should_stop():
                stopped_reason = "time_budget_exceeded"
                break
            if len(step_results) >= max_steps:
                stopped_reason = "max_steps_reached"
                break
            _status, _stop = _append_treatment_result(sd, prog, step_results)
            treatment_count += 1
            if _stop:
                stopped_reason = _stop
                break
            skipped_streak = skipped_streak + 1 if _status == "skipped" else 0
            if skipped_streak >= _TREATMENT_STREAK_LIMIT:
                stopped_reason = "treatment_skipped_streak"
                break
            failed_streak = (failed_streak + 1
                             if _status in _FAILED_STEP_STATUSES else 0)
            if failed_streak >= _TREATMENT_STREAK_LIMIT:
                stopped_reason = "treatment_failed_streak"
                break
    return stopped_reason, treatment_count
def _append_treatment_result(sd: str, prog: dict,
                             step_results: list[dict]) -> tuple[str, str]:
    _tres = execute_treatment_item(sd, _run_with_error_sentinel)
    _status = str(_tres.get("status", "unknown"))
    _terr = _tres.get("error", "")
    _index = _tres.get("index")
    if not isinstance(_index, int) or isinstance(_index, bool) or _index < 0:
        _index = _as_count(prog.get("current_index"))
    step_results.append({
        "task_type": "treatment",
        "index": _index,
        "status": _status,
        "elapsed_s": _as_float(_tres.get("elapsed_s")),
        **({"error": _terr} if _terr else {}),
    })
    return _status, ""
def _batch_aggregate_ai_fix_candidates(sd: str, step_results: list[dict]) -> str:
    try:
        _agg_result = run_phase_handler("treatment_done", sd)
    except CacheNotWarmedError:
        raise
    except Exception as _ae:  # noqa: BLE001
        log_swallowed(
            __name__, _ae,
            context=f'_batch_aggregate_ai_fix_candidates:{type(_ae).__name__}')
        _agg_result = {"task_result": {"status": "error",
                                       "error": str(_ae)[:500]},
                       "next_phase": None}
    if not isinstance(_agg_result, dict):
        if _agg_result is not None:
            logger.warning(
                "[PipelineBatch] ai_manual_fix 聚合处理器返回非映射(%s)，"
                "按空结果降级", type(_agg_result).__name__)
        _agg_result = {}
    _task_result = _as_dict(_agg_result.get("task_result"))
    step_results.append({
        "task_type": "ai_manual_fix",
        "status": _task_result.get("status", "unknown"),
        "next_phase": _agg_result.get("next_phase"),
        "detail": _agg_result,
    })
    if _agg_result.get("next_phase") not in ("ai_fix_pending", "ai_fix_done"):
        return "ai_fix_unexpected_phase"
    return ""
def _step_findings_count(result: dict) -> int | None:
    for _key in ("findings_count", "total_findings"):
        _value = result.get(_key)
        if (isinstance(_value, int) and not isinstance(_value, bool)
                and _value >= 0):
            return _value
    return None
def _batch_run_shell_steps(sd: str, phase: str, max_steps: int,
                           step_results: list[dict], *,
                           should_stop: Callable[[], bool] | None = None) -> str:
    for label, step_fn in iter_shell_steps(phase):
        if should_stop is not None and should_stop():
            return "time_budget_exceeded"
        if len(step_results) >= max_steps:
            return "max_steps_reached"
        _r = _run_with_error_sentinel(
            lambda fn=step_fn: fn(sd), {}, None, f"{label}异常哨兵")
        _record = {
            "task_type": label,
            "status": _r.get("status", "unknown"),
            "elapsed_s": _as_float(_r.get("elapsed_s")),
            "detail": _r,
        }
        _findings = _step_findings_count(_r)
        if _findings is not None:
            _record["findings_count"] = _findings
        step_results.append(_record)
        if str(_r.get("status", "")) in _FAILED_STEP_STATUSES:
            return f"step_failed:{label}"
    return ""
def _batch_run_diagnosis_stage(
    sd: str, max_steps: int, step_results: list[dict], *,
    should_stop: Callable[[], bool] | None = None,
) -> tuple[str, str, bool]:
    stopped_reason = ""
    phase = "pending_diagnosis"
    diagnosis_reused = False
    if len(step_results) >= max_steps:
        return "max_steps_reached", phase, diagnosis_reused
    reuse = _as_dict(check_diagnosis_reusable(sd))
    if reuse.get("reusable"):
        finalize_diagnosis_stage(
            sd, diagnosis_progress_dict(sd), diagnosis_reused=True,
            reuse_reason=reuse.get("reason", ""))
        phase = "diagnosis_done"
        diagnosis_reused = True
        step_results.append({
            "task_type": "diagnosis_reuse",
            "status": "completed",
            "reason": reuse.get("reason", ""),
        })
    else:
        ensure_diagnosis_round(sd)
        output_dir = json_artifact_dir(sd)
        _shared_cache = get_warmed_cache(sd)
        stopped_reason = run_batch_diagnosis_methods(
            sd, max_steps, step_results, output_dir, _shared_cache,
            should_stop=should_stop)
        if not stopped_reason:
            new_progress = diagnosis_progress_dict(sd)
            if diagnosis_fresh_complete(new_progress):
                finalize_diagnosis_stage(sd, new_progress)
                phase = "diagnosis_done"
            else:
                stopped_reason = "diagnosis_incomplete"
    return stopped_reason, phase, diagnosis_reused
def _build_batch_error_detail(step_results: list[dict]) -> dict | None:
    _fail_steps = [
        _sr for _sr in step_results
        if isinstance(_sr, dict)
        and str(_sr.get("status", "")) in _FAILED_STEP_STATUSES
    ]
    if not _fail_steps:
        return None
    _first_fail = _fail_steps[0]
    return {
        "step": str(_first_fail.get("method_id")
                    or _first_fail.get("task_type")
                    or _first_fail.get("step") or "unknown")[:40],
        "status": str(_first_fail.get("status", ""))[:20],
        "error": _step_error_text(_first_fail)[:500],
        "failed_steps": len(_fail_steps),
    }
def _step_error_text(step_result: dict) -> str:
    _direct = step_result.get("error") or step_result.get("summary")
    if _direct:
        return str(_direct)
    _task_result = step_result.get("task_result")
    if isinstance(_task_result, dict):
        _task_error = _task_result.get("error") or _task_result.get("summary")
        if _task_error:
            return str(_task_error)
    _detail = step_result.get("detail")
    if not isinstance(_detail, dict):
        return ""
    _nested = _detail.get("error") or _detail.get("summary")
    if _nested:
        return str(_nested)
    _inner = _detail.get("task_result")
    if isinstance(_inner, dict):
        return str(_inner.get("error") or _inner.get("summary") or "")
    return ""
# 审核队列相关相位分两类：
# * DRAIN：可以尝试用 provider 排空审核队列的相位；
# * STOP：排空无进展时必须停批的相位（终态交付门禁点）。
# 历史上两者是同一个集合，导致 `ai_fix_pending` 在排空零进展时直接 return，
# 整条管线永远到不了复盘/反哺/进化（放行相位不可达）。
_BATCH_AI_REVIEW_DRAIN_PHASES = frozenset({"ai_fix_pending", "evolution_pending"})
_BATCH_AI_REVIEW_STOP_PHASES = frozenset({"evolution_pending"})
def _as_text(value: Any, default: str = "") -> str:
    return value if isinstance(value, str) and value else default
def _as_float(value: Any, default: float = 0.0) -> float:
    num = safe_float(value, None)
    return default if num is None or not safe_isfinite(num) else num
def _as_count(value: Any) -> int:
    if isinstance(value, bool):
        return 0
    if isinstance(value, int):
        return max(value, 0)
    num = _as_float(value, float("nan"))
    if not safe_isfinite(num) or num < 0 or not num.is_integer():
        return 0
    return int(num)
def _as_dict(value: Any) -> dict:
    return dict(value) if isinstance(value, dict) else {}
def _as_entries(value: Any) -> list:
    if value is None:
        return []
    if isinstance(value, (list, tuple, set, frozenset)):
        return list(value)
    return [value]
def _as_path_text(value: Any) -> str:
    if value is None:
        return ""
    try:
        text = os.fspath(value)
    except (TypeError, ValueError):
        return ""
    if isinstance(text, bytes):
        text = text.decode("utf-8", errors="replace")
    return text.strip() if isinstance(text, str) else ""
def _as_str_sequence(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        raw_items: list[Any] = [value]
    elif isinstance(value, (list, tuple, set, frozenset)):
        raw_items = list(value)
    else:
        return []
    result: list[str] = []
    for item in raw_items:
        if not isinstance(item, str):
            continue
        text = item.strip()
        if text:
            result.append(text)
    return result
def _step_status_of(result: Any) -> str:
    if not isinstance(result, dict):
        return "error"
    for _candidate in (result.get("status"),
                       _as_dict(result.get("task_result")).get("status")):
        if isinstance(_candidate, str) and _candidate:
            return _candidate
    return "unknown"
def _step_elapsed_s(result: Any) -> float:
    if not isinstance(result, dict):
        return 0.0
    elapsed = result.get("elapsed_s")
    if elapsed is None:
        elapsed = _as_dict(result.get("task_result")).get("elapsed_s")
    return _as_float(elapsed, 0.0)
def _batch_run_final_stages(sd: str, max_steps: int,
                            run: _BatchRun) -> None:
    _visited: list[str] = []
    while True:
        phase = _as_text(_as_dict(load_pipeline_state(sd)).get("phase"))
        if phase == "all_completed":
            return
        if not phase:
            run.stopped_reason = "phase_unavailable"
            logger.warning("[PipelineBatch] 管线相位不可读（空），停批待重试")
            return
        if _batch_budget_exhausted(run):
            return
        if len(run.step_results) >= max_steps:
            run.stopped_reason = "max_steps_reached"
            return
        if phase and phase == run.consumed_phase:
            run.stopped_reason = f"phase_stalled:{phase}"
            logger.info(
                "[PipelineBatch] 阶段已由前序聚合消费，跳过重复执行: phase=%s",
                phase)
            return
        if phase in _BATCH_AI_REVIEW_STOP_PHASES:
            pending = _pending_review_count(sd)
            if pending is None:
                run.stopped_reason = "pending_review_unavailable"
                logger.warning(
                    "[PipelineBatch] 审核队列不可读，停批待重试: phase=%s", phase)
                return
            if pending != 0:
                logger.info(
                    "[PipelineBatch] 停在人工审核停批点: phase=%s", phase)
                return
            logger.info(
                "[PipelineBatch] 审核队列已清零，继续推进: phase=%s", phase)
        if _visited.count(phase) >= 2:
            run.stopped_reason = f"phase_loop_detected:{phase}"
            logger.warning(
                "[PipelineBatch] 阶段 5~6e 检测到回退环路，停批: %s", phase)
            return
        _visited.append(phase)
        _r = _run_with_error_sentinel(
            lambda: run_next_pipeline_step(sd, _internal=True), {}, None,
            f"final_phase[{phase}]异常哨兵")
        _status = _step_status_of(_r)
        _next = _as_text(_r.get("next_phase")) or phase
        run.step_results.append({
            "task_type": _as_text(_r.get("task_type")) or phase,
            "status": _status,
            "phase": phase,
            "next_phase": _next,
            "elapsed_s": _step_elapsed_s(_r),
        })
        if _status in _FAILED_STEP_STATUSES:
            run.stopped_reason = f"step_failed:{phase}"
            return
        _advanced = _as_text(_as_dict(load_pipeline_state(sd)).get("phase"))
        if _advanced == phase:
            run.stopped_reason = f"phase_stalled:{phase}"
            logger.warning(
                "[PipelineBatch] 阶段停留未推进，停批待重试: phase=%s "
                "status=%s", phase, _status)
            return
        if _advanced in _BATCH_AI_REVIEW_STOP_PHASES:
            logger.info(
                "[PipelineBatch] 到达人工审核停批点: next_phase=%s", _advanced)
            return
def _batch_advance_stages(sd: str, max_steps: int, run: _BatchRun) -> None:
    def _budget_exhausted() -> bool:
        return _batch_budget_exhausted(run)

    phase = resume_phase(sd)
    if phase == "pending_diagnosis":
        run.stopped_reason, phase, run.diagnosis_reused = (
            _batch_run_diagnosis_stage(
                sd, max_steps, run.step_results, should_stop=_budget_exhausted))
    if not run.stopped_reason and not _budget_exhausted():
        run.stopped_reason = _batch_run_shell_steps(
            sd, phase, max_steps, run.step_results,
            should_stop=_budget_exhausted)
    if not run.stopped_reason and not _budget_exhausted():
        _batch_run_treatment_stage(sd, max_steps, run)
    if not run.stopped_reason and not _budget_exhausted():
        _batch_run_final_stages(sd, max_steps, run)
def _batch_run_treatment_stage(sd: str, max_steps: int,
                              run: _BatchRun) -> None:
    _cur_phase = _as_text(_as_dict(load_pipeline_state(sd)).get("phase"))
    if (phase_reached(_cur_phase, "plan_generated")
            and not phase_reached(_cur_phase, "treatment_done")):
        _stop, _tc = _batch_run_treatment_items(
            sd, max_steps, run.step_results,
            should_stop=lambda: _batch_budget_exhausted(run))
        run.stopped_reason = _stop
        run.treatment_count += _tc
        if not run.stopped_reason and _batch_budget_exhausted(run):
            return
        if not run.stopped_reason:
            _ok, _adv_err = advance_phase_safe(
                sd, "treatment_done",
                treatment_trace_metrics(get_treatment_progress(sd)))
            if not _ok:
                run.stopped_reason = "phase_advance_failed:treatment_done"
                run.step_results.append({
                    "task_type": "treatment_done_advance",
                    "status": "error",
                    "error": _adv_err,
                })
    if run.stopped_reason:
        return
    if len(run.step_results) >= max_steps:
        run.stopped_reason = "max_steps_reached"
        return
    if _as_text(_as_dict(load_pipeline_state(sd)).get("phase")) == "treatment_done":
        run.consumed_phase = "treatment_done"
        run.stopped_reason = _batch_aggregate_ai_fix_candidates(
            sd, run.step_results)
def _batch_finalize_result(sd: str, batch_start: float, run: _BatchRun) -> dict:
    final_phase = (_as_text(_as_dict(load_pipeline_state(sd)).get("phase"))
                   or "unknown")
    out = {
        "status": "ok" if not run.stopped_reason else "early_stopped",
        "phase": final_phase,
        "steps_executed": len(run.step_results),
        "treatment_items_executed": run.treatment_count,
        "diagnosis_reused": run.diagnosis_reused,
        "elapsed_s": round(time.time() - batch_start, 2),
        "step_results": run.step_results,
        "stopped_reason": run.stopped_reason,
        "progress": get_pipeline_progress(sd),
    }
    if run.stopped_reason:
        _detail = _build_batch_error_detail(run.step_results)
        if _detail is not None:
            out["error_detail"] = _detail
    if final_phase in ("ai_fix_pending", "evolution_pending"):
        attach_pending_review_info(out, sd)
    needs_review = (
        bool(out.get("pending_ai_review"))
        or ("pending_ai_review" not in out
            and final_phase in ("ai_fix_pending", "evolution_pending")
            and run.stopped_reason != "pending_review_unavailable")
    )
    if needs_review and not run.stopped_reason:
        run.stopped_reason = "ai_review_pending"
        out["status"] = "early_stopped"
        out["stopped_reason"] = run.stopped_reason
    out["next_action"] = (
        "run_next_ai_review" if needs_review
        else "" if final_phase == "all_completed"
        else "run_next_pipeline_step"
    )
    try:
        generate_html_report(out, sd, "batch")
        logger.info("[PipelineBatch] 批量总览 HTML 已生成")
    except Exception as _bhe:  # noqa: BLE001
        logger.warning("[PipelineBatch] 批量总览 HTML 生成失败(不阻断): %s", _bhe)
    logger.info("[PipelineBatch] 批量推进完成: status=%s, phase=%s, %d步, %.1fs%s",
                out["status"], final_phase, out["steps_executed"], out["elapsed_s"],
                f", stopped_reason={run.stopped_reason}" if run.stopped_reason else "")
    return out
# 进程级重入权（模块级全局 + 锁）。
#
# 必须**不能**用 ``threading.local()``：链模拟器
# （``diag_business_flow._call_with_timeout``）会把入口函数丢进新建的
# ``chain-sim`` 线程执行，线程本地状态在该线程里是空的，守卫被直接绕过——
# 实测嵌套治理的阶段报告仍会写进真实 ``htm/`` 交付目录
# （``诊断F*.html`` / ``审核治疗*.html``，报告头 ``skill=...\\test``）。
# 且外泄入口是治疗/复盘阶段函数，本就不经过管线入口，故还需报告落点隔离
# （``diag_business_flow._isolated_report_root``）双重兜底。
_PIPELINE_REENTRY_OWNER = ""
_PIPELINE_REENTRY_LOCK = threading.Lock()


def _pipeline_reentry_owner() -> str:
    with _PIPELINE_REENTRY_LOCK:
        return _PIPELINE_REENTRY_OWNER
def _claim_pipeline_reentry(skill_dir: str, entry: str) -> str:
    """认领进程级管线重入权，返回原持有者（供 finally 恢复）。

    沙箱/自测执行目标源码时可能再次调用管线入口；这类**嵌套运行**的阶段报告
    会写进工作空间的真实 ``htm/`` 交付目录，把无关目标的报告混入本次交付
    （实测方法 C 沙箱在 ``<工作空间>/test`` 上跑出 诊断F/审核治疗 两份报告）。

    ``PipelineGuard`` 的 ``ProcessLock`` 按 ``skill_dir`` 分键，换一个目标就天然
    绕过，因此必须在进程级兜住：**同一个进程只允许治理一个目标**。
    """
    global _PIPELINE_REENTRY_OWNER
    with _PIPELINE_REENTRY_LOCK:
        owner = _PIPELINE_REENTRY_OWNER
        if owner:
            raise ConcurrentExecutionError(
                f"检测到同进程嵌套管线入口 {entry}：已存在治理目标 {owner}，"
                f"拒绝并发治理 {skill_dir}（沙箱/自测执行源码时不得重入管线，"
                f"否则阶段报告会写进真实 htm/ 交付目录）")
        _PIPELINE_REENTRY_OWNER = skill_dir
        return ""


def _release_pipeline_reentry(previous: str) -> None:
    global _PIPELINE_REENTRY_OWNER
    with _PIPELINE_REENTRY_LOCK:
        _PIPELINE_REENTRY_OWNER = previous or ""
def run_pipeline_batch(
    skill_dir: str, max_steps: int = MAX_AI_REVIEW_ITEMS,
    *, _internal: bool = False,
    max_seconds: float = DEFAULT_BATCH_MAX_SECONDS,
) -> dict:
    """批量推进管线相位（官方批量入口）。

    同一进程内可反复调用以续跑：批量入口本身以 ``max_steps`` 与
    ``max_seconds`` 双重预算控制单次调用的资源上限，不再受“每命令轮次只
    执行一步”守卫限制。否则每轮续跑都必须重启进程，重新 import 200+ 模块
    并重预热共享缓存（实测 jwsgj 自诊断单次预热 5.3s），属纯重复劳动。
    """
    # 内部续跑（_run_full_pipeline 传 _internal=True）沿用外层守卫，不重复认领。
    # 认领必须**先于**路径校验：沙箱目标往往不是合法技能根，先校验会把重入
    # 拒绝伪装成「无效的技能目录」，掩盖真正的并发治理冲突。
    _reentry_prev = (None if _internal
                     else _claim_pipeline_reentry(str(skill_dir),
                                                  "run_pipeline_batch"))
    try:
        sd = normalize_skill_dir(skill_dir, require_valid=True)
    except BaseException:
        if _reentry_prev is not None:
            _release_pipeline_reentry(_reentry_prev)
            _reentry_prev = None
        raise
    load_solidified_ssot(sd)
    batch_start = time.time()
    run = _BatchRun()
    _budget = safe_float(max_seconds, DEFAULT_BATCH_MAX_SECONDS)
    run.deadline = (batch_start + _budget) if _budget > 0 else 0.0
    guard = PipelineGuard(sd, "pipeline_batch")
    _prev_handoff_disk: bool | None = None
    _guard_entered = False
    _skip_cache_cleanup = False
    try:
        guard.enter(check_batch=False)
        _guard_entered = True
        _prev_handoff_disk = set_handoff_persistence(False)
        _batch_advance_stages(sd, max_steps, run)
    except CacheNotWarmedError:
        raise
    except ConcurrentExecutionError as e:
        log_swallowed(__name__, e, context='run_pipeline_batch:ConcurrentExecutionError')
        _skip_cache_cleanup = not _guard_entered
        run.stopped_reason = f"blocked:{str(e)[:200]}"
    except Exception as e:
        logger.exception("[PipelineBatch] 批量推进异常，转 error 哨兵停批")
        if not run.stopped_reason:
            run.stopped_reason = f"exception:{type(e).__name__}:{str(e)[:200]}"
        run.step_results.append({
            "task_type": "pipeline_batch_exception",
            "status": "error",
            "error": str(e)[:500],
        })
    finally:
        if _reentry_prev is not None:
            _release_pipeline_reentry(_reentry_prev)
        if _prev_handoff_disk is not None:
            try:
                set_handoff_persistence(_prev_handoff_disk)
            except Exception:
                logger.warning("[PipelineBatch] 交棒持久化恢复失败(降级)",
                               exc_info=True)
        if not _skip_cache_cleanup:
            try:
                clear_all_process_memory(skill_dir=sd)
            except Exception:
                logger.warning("[PipelineBatch] 缓存释放跳过", exc_info=True)
        try:
            guard.exit()
        except Exception:
            logger.warning("[PipelineBatch] 守卫释放失败(降级)", exc_info=True)
    return _batch_finalize_result(sd, batch_start, run)
def _match_trigger_hits(text: str) -> list:
    hits = match_pipeline_trigger(text)
    if not hits and isinstance(text, str):
        normalized = normalize_trigger_text(text)
        if normalized != text:
            hits = match_pipeline_trigger(normalized)
    return hits
def _run_step_or_error(skill_dir: str, hits, probe, log_tag: str):
    try:
        step = run_next_pipeline_step(skill_dir)
    except Exception as e:
        logger.exception(log_tag)
        return None, {"status": "error", "data": {"keywords": hits, "probe": probe},
                      "message": f"管线执行失败: {e}"}
    if not isinstance(step, dict):
        return None, {
            "status": "error",
            "data": {"keywords": hits, "probe": probe},
            "message": f"管线执行失败: 单步返回非映射 {type(step).__name__}",
        }
    status = _step_status_of(step)
    if status in _FAILED_STEP_STATUSES:
        detail = _step_error_text(step) or f"单步状态为 {status}"
        logger.warning("[Trigger] 单步推进返回失败状态: %s: %s", status, detail)
        return None, {
            "status": "error",
            "data": {"keywords": hits, "probe": probe,
                     "pipeline_step": step},
            "message": f"管线执行失败（{status}）: {detail}",
        }
    return step, None
# 自驱预算：单次调用的步数上限 = 每批步数 × 批数。
#
# 历史值 240 × 20 = 4800 步，而治理工作量是 O(findings)：
# 以 jwsgj 自身为例，2721 项治疗 + 4279 项审核 ≈ 6994 步，
# 因此默认预算**必然**在中途耗尽，表现为「管线无法一次跑完」。
# 这里按「单次可覆盖一个完整治理轮」的量级上调；
# 无限循环由 phase_stalled / phase_loop_detected 独立兜底，
# 不依赖预算值做唯一保险。
PIPELINE_STEP_BUDGET = 1200
PIPELINE_BATCH_BUDGET = 60

# 外部 AI 审核 provider（自驱循环在审核相位自动裁决用）。
# provider 签名：Callable[[dict], dict]，入参为单条待审材料，
# 返回四维评估（严重性/可修复性/利弊/误报）。
# 未注册时保持原行为：停批并交外部逐项审核。
_AI_REVIEW_PROVIDER: Any = None


def set_ai_review_provider(provider: Any) -> None:
    """注册外部 AI 审核 provider（不注册则自驱循环按无 provider 停批）。"""
    global _AI_REVIEW_PROVIDER
    _AI_REVIEW_PROVIDER = provider
def _pipeline_phase(sd: str) -> str:
    try:
        return str(load_pipeline_state(sd).get("phase", ""))
    except Exception:
        logger.warning("[Trigger] 管线相位读取失败(降级为空)", exc_info=True)
        return ""
def _pending_review_count(sd: str) -> int | None:
    try:
        aggregate, read_error = read_pending_reviews(sd)
    except Exception:
        logger.warning("[Trigger] 待审核清单读取失败", exc_info=True)
        return None
    if read_error:
        logger.warning("[Trigger] 待审核清单读取失败: %s", read_error)
        return None
    value = aggregate.get("pending_ai_review")
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        logger.warning("[Trigger] 待审核计数非法: %r", value)
        return None
    return value
def _recorded_mandatory_hits(probe) -> list[str]:
    evidence = probe.get("evidence") if isinstance(probe, dict) else None
    raw = evidence.get("mandatory_hits") if isinstance(evidence, dict) else None
    return _as_str_sequence(raw)
def _build_enforcement_record(text: str, hits, probe, decision: str,
                              full: bool, ai_hit: bool) -> dict:
    return {
        "schema": "jwsgj/trigger-enforcement/1",
        "text": str(text or "")[:120],
        "text_sha256": hashlib.sha256(
            str(text or "").encode("utf-8")).hexdigest(),
        "keywords": _as_str_sequence(hits),
        "mandatory_hits": _recorded_mandatory_hits(probe),
        "decision": decision,
        "confidence": probe.get("confidence", ""),
        "contract_passed": True,
        "ai_hit": bool(ai_hit),
        "executed": True,
        "full_pipeline": bool(full),
        "status": "running",
        "phase": "",
        "steps_executed": 0,
        "review_batches": 0,
        "started_at": now_iso_seconds(),
        "finished_at": "",
        "stopped_reason": "",
    }
def _write_enforcement_record(sd: str, record: dict) -> bool:
    try:
        path = os.path.join(get_temp_dir(sd), TRIGGER_ENFORCEMENT_FILENAME)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        atomic_write_text(
            path, json.dumps(record, ensure_ascii=False, indent=2),
            tag="trigger_enforcement")
        return True
    except Exception as exc:  # noqa: BLE001
        logger.warning("[Trigger] 强制记录写入失败(不阻断): %s", exc)
        return False
def _record_pipeline_event(skill_dir: str, text: str, hits, probe,
                           decision: str, ai_hit: bool,
                           record: dict) -> None:
    record_trigger_event(
        skill_dir, decision=decision,
        confidence=str(probe.get("confidence", "")),
        text=text, evidence=probe.get("evidence"),
        extra={"ai_hit": bool(ai_hit), "executed": True,
               "full_pipeline": bool(record.get("full_pipeline")),
               "pipeline_status": record.get("status", ""),
               "pipeline_phase": record.get("phase", "")})
def _run_full_pipeline(
        sd: str, max_steps: int | None = None,
        max_batches: int | None = None,
) -> tuple[str, list[dict], list[dict], dict, str]:
    max_steps = PIPELINE_STEP_BUDGET if max_steps is None else max_steps
    max_batches = (PIPELINE_BATCH_BUDGET if max_batches is None
                   else max_batches)
    steps: list[dict] = []
    review_batches: list[dict] = []
    last_step: dict = {}
    remaining_steps = max_steps
    # 审核队列已「排空无进展」（无 provider 或全部 defer）时置位：不再重复
    # 尝试排空，改为把未审项作为载荷继续推进复盘/反哺/进化，由 6d/6e 的
    # 交付门禁统一阻断。否则整条管线永远到不了放行相位。
    review_drain_exhausted = False
    # 审核相位历史缺陷：`remaining > 0` 直接 return，导致每批只消费
    # ``MAX_AI_REVIEW_ITEMS``（=200）条就停批，`max_batches` 循环形同虚设——
    # 4279 条积压永远清不完，“自动推进到归零”不可能。
    # 正确语义：只要有进展（remaining 下降）就继续下一批，**零进展**才停。
    for _ in range(max_batches):
        if remaining_steps <= 0:
            return ("max_steps_reached", steps, review_batches, last_step,
                    f"达到最大步数 {max_steps}")
        try:
            batch = run_pipeline_batch(
                sd, max_steps=remaining_steps, _internal=True)
        except CacheNotWarmedError as exc:
            return ("error", steps, review_batches, last_step,
                    f"缓存未预热: {exc}")
        except Exception as exc:
            logger.exception("[Trigger] 全管线批量推进异常")
            return ("error", steps, review_batches, last_step, str(exc))
        if not isinstance(batch, dict):
            return ("error", steps, review_batches, last_step,
                    f"批量管线返回非映射: {type(batch).__name__}")
        _batch_steps = _as_entries(batch.get("step_results"))
        _dict_steps = [item for item in _batch_steps if isinstance(item, dict)]
        if _dict_steps:
            steps.extend(_dict_steps)
            last_step = steps[-1]
        _executed = _as_count(batch.get("steps_executed"))
        remaining_steps -= _executed
        phase = _as_text(batch.get("phase"))
        status = _as_text(batch.get("status"))
        reason = _as_text(batch.get("stopped_reason"))
        if reason.startswith("blocked:"):
            return "blocked", steps, review_batches, last_step, reason
        error_detail = _as_dict(batch.get("error_detail"))
        if status == "error" or reason.startswith("exception:") or error_detail:
            detail = _step_error_text(error_detail)
            return ("error", steps, review_batches, last_step,
                    detail or reason or "批量管线异常")
        if phase == "all_completed":
            return "completed", steps, review_batches, last_step, ""
        if phase in _BATCH_AI_REVIEW_DRAIN_PHASES:
            pending = _pending_review_count(sd)
            if pending is None:
                return ("error", steps, review_batches, last_step,
                        "待审核清单不可读，保守停批")
            if pending == 0 and not _batch_steps and _executed <= 0:
                return ("stalled", steps, review_batches, last_step,
                        f"审核相位零待审且批量未产生步骤: phase={phase}")
            if pending > 0 and not review_drain_exhausted:
                try:
                    review = run_all_ai_reviews(
                        sd, provider=_AI_REVIEW_PROVIDER)
                except Exception as exc:  # noqa: BLE001
                    return ("error", steps, review_batches, last_step,
                            f"AI 审核执行失败: {exc}")
                if not isinstance(review, dict):
                    return ("error", steps, review_batches, last_step,
                            f"AI 审核返回非映射: {type(review).__name__}")
                review_batches.append(review)
                if str(review.get("status", "")) == "error":
                    return ("error", steps, review_batches, last_step,
                            str(review.get("error") or "AI 审核失败"))
                remaining = review.get("remaining")
                if (isinstance(remaining, bool)
                        or not isinstance(remaining, int)
                        or remaining < 0):
                    return ("error", steps, review_batches, last_step,
                            f"AI 审核剩余计数不可读: {remaining!r}")
                if remaining > 0 and remaining < pending:
                    # 基线必须是「本批调用前」的待审数，才能判定本批有无推进。
                    # 本批确有推进：继续下一批，直到清零或零进展。
                    logger.info(
                        "[Trigger] 审核队列推进: %d -> %d，继续批推"
                        "(batch=%d)", pending, remaining,
                        len(review_batches))
                    continue
                if remaining > 0:
                    # 零进展：本进程内已无可用裁决能力（未注入 provider 或
                    # 全部 defer）。不把「审核队列未清空」当作整条管线终点——
                    # 复盘/反哺/进化不写被审源码，必须继续推进到放行相位，
                    # 由 6d/6e 交付门禁（zero_backlog）统一阻断。
                    review_drain_exhausted = True
                    logger.warning(
                        "[Trigger] 审核队列本批零进展（%d 项），停止排空，"
                        "继续推进复盘/反哺/进化，由交付门禁统一阻断",
                        remaining)
            elif (review_drain_exhausted and pending > 0
                    and not _batch_steps and _executed <= 0):
                # 已停止排空且管线在审核相位无步骤可走：只能由交付门禁
                # （backlog）阻断，没有代码层可推进的动作。
                return ("early_stopped", steps, review_batches, last_step,
                        (f"审核队列未清空（{pending} 项）且管线在 {phase} "
                         "无法继续推进：由交付门禁阻断"))
            continue
        if reason == "max_steps_reached":
            if _executed <= 0:
                return ("max_steps_reached", steps, review_batches,
                        last_step, f"达到最大步数 {max_steps}")
            continue
        if reason.startswith(("phase_stalled:", "phase_loop_detected:")):
            return ("stalled", steps, review_batches, last_step, reason)
        if status == "early_stopped":
            return ("early_stopped", steps, review_batches, last_step,
                    reason or "管线提前停批")
        if not _batch_steps:
            return ("stalled", steps, review_batches, last_step,
                    f"批量未产生步骤且未终态: phase={phase or 'unknown'}")
    return ("max_batches_reached", steps, review_batches, last_step,
            f"达到最大批次数 {max_batches}")
def _execute_trigger_pipeline(skill_dir: str, text: str, hits, probe,
                              decision: str, full: bool,
                              ai_hit: bool = False,
                              max_steps: int | None = None,
                              max_batches: int | None = None) -> dict:
    public_status = "hit" if ai_hit else decision
    _prefix = ("miss 强制接管（force=True）" if ai_hit
               else f"命中探测（{decision}）")
    record = _build_enforcement_record(
        text, hits, probe, decision, full, ai_hit)
    _write_enforcement_record(skill_dir, record)
    if not full:
        step, _err = _run_step_or_error(
            skill_dir, hits, probe, "[Trigger] 单步推进执行失败")
        if _err is not None:
            record.update(status="error", phase=_pipeline_phase(skill_dir),
                          finished_at=now_iso_seconds(),
                          stopped_reason=str(_err.get("message", ""))[:500])
            _write_enforcement_record(skill_dir, record)
            _record_pipeline_event(skill_dir, text, hits, probe, decision,
                                   ai_hit, record)
            return _err
        actual_phase = (_pipeline_phase(skill_dir)
                        or _as_text(step.get("next_phase"))
                        or _as_text(step.get("phase")))
        record.update(status="single_step",
                      phase=actual_phase,
                      steps_executed=1,
                      finished_at=now_iso_seconds())
        _write_enforcement_record(skill_dir, record)
        _record_pipeline_event(skill_dir, text, hits, probe, decision,
                               ai_hit, record)
        return {"status": public_status,
                "data": {"keywords": hits, "probe": probe,
                         "pipeline_step": step,
                         "pipeline_status": "single_step",
                         "phase": record["phase"],
                         "enforcement": record},
                "message": (f"{_prefix}，单步推进完成: "
                            f"phase={record['phase']}, "
                            f"is_terminal={step.get('is_terminal')}")}
    try:
        status, steps, review_batches, last_step, reason = (
            _run_full_pipeline(skill_dir, max_steps, max_batches))
    except BaseException as exc:
        record.update(
            status="error",
            phase=_pipeline_phase(skill_dir),
            finished_at=now_iso_seconds(),
            stopped_reason=(
                f"{type(exc).__name__}: {str(exc)[:400]}"),
        )
        _write_enforcement_record(skill_dir, record)
        raise
    record.update(status=status, phase=_pipeline_phase(skill_dir),
                  steps_executed=len(steps),
                  review_batches=len(review_batches),
                  finished_at=now_iso_seconds(),
                  stopped_reason=str(reason or "")[:500])
    _write_enforcement_record(skill_dir, record)
    _rounds = [{"step": idx + 1,
                "phase": _as_text(item.get("phase")),
                "next_phase": _as_text(item.get("next_phase")),
                "status": _step_status_of(item)}
               for idx, item in enumerate(steps)]
    _record_pipeline_event(skill_dir, text, hits, probe, decision,
                           ai_hit, record)
    if status in ("blocked", "error"):
        return {"status": "error",
                "data": {"keywords": hits, "probe": probe,
                         "pipeline_step": last_step,
                         "pipeline_status": status,
                         "phase": record["phase"],
                         "rounds": _rounds,
                         "review_batches": review_batches,
                         "enforcement": record},
                "message": f"全管线推进失败（{status}）: {reason}"}
    _done = status == "completed"
    return {"status": public_status,
            "data": {"keywords": hits, "probe": probe,
                     "pipeline_step": last_step,
                     "pipeline_status": status,
                     "phase": record["phase"],
                     "rounds": _rounds,
                     "review_batches": review_batches,
                     "enforcement": record},
            "message": (f"{_prefix}，全管线"
                        + ("已完成（all_completed）" if _done
                           else f"停批（{status}）: {reason}"))}
def _probe_only_result(decision: str, hits, probe) -> dict:
    return {"status": decision,
            "data": {"keywords": hits, "probe": probe},
            "message": (f"命中探测（{decision}，"
                        f"confidence={probe.get('confidence')}）"
                        "（探测模式，未执行管线）")}
def _soft_pending_result(skill_dir: str, text: str, hits, probe) -> dict:
    record_trigger_event(
        skill_dir, decision="soft", confidence=probe.get("confidence", ""),
        text=text, evidence=probe.get("evidence"), extra={"executed": False})
    return {"status": "soft",
            "data": {"keywords": hits, "probe": probe},
            "message": ("软命中（弱词语境/模糊近义）：默认不执行；"
                        "确认意图后以 allow_soft=True 重入或显式调用管线入口")}
def run_pipeline_from_trigger(text: str, skill_dir: str,
                              execute: bool = True,
                              allow_soft: bool = False,
                              force: bool = False,
                              full: bool = True,
                              max_steps: int | None = None,
                              max_batches: int | None = None) -> dict:
    """触发探测 + 全链路推进（进程级重入守卫的外层入口）。

    仅探测（``execute=False``）不治理任何目标，不占重入权。
    """
    if not execute:
        return _run_pipeline_from_trigger_impl(
            text, skill_dir, execute, allow_soft, force, full,
            max_steps, max_batches)
    try:
        previous = _claim_pipeline_reentry(
            _as_path_text(skill_dir), "run_pipeline_from_trigger")
    except ConcurrentExecutionError as exc:
        return {"status": "error",
                "data": {"keywords": [], "probe": {}},
                "message": str(exc)}
    try:
        return _run_pipeline_from_trigger_impl(
            text, skill_dir, execute, allow_soft, force, full,
            max_steps, max_batches)
    finally:
        _release_pipeline_reentry(previous)
def _run_pipeline_from_trigger_impl(text: str, skill_dir: str,
                                    execute: bool = True,
                                    allow_soft: bool = False,
                                    force: bool = False,
                                    full: bool = True,
                                    max_steps: int | None = None,
                                    max_batches: int | None = None) -> dict:
    skill_text = _as_path_text(skill_dir)
    contract = validate_pipeline_trigger_contract()
    if not contract.get("passed"):
        return {"status": "error",
                "data": {"keywords": [], "probe": {},
                         "contract": contract},
                "message": ("触发强制词表契约不满足，拒绝进入管线: "
                            f"missing={contract.get('missing')}, "
                            f"unmatched={contract.get('unmatched')}")}
    hits = _match_trigger_hits(text)
    probe = probe_pipeline_trigger(text, strong_hits=hits, skill_dir=skill_text)
    decision = probe.get("decision", "miss")
    if decision == "miss" and force and execute:
        if not skill_text:
            return {"status": "error",
                    "data": {"keywords": hits, "probe": probe},
                    "message": ("--force 需要非空 skill_dir"
                                "（空白路径不得回退到当前目录）")}
        return _execute_trigger_pipeline(
            skill_text, text, hits, probe, decision="miss",
            full=full, ai_hit=True, max_steps=max_steps,
            max_batches=max_batches)
    if decision == "miss":
        return {"status": "miss",
                "data": {"keywords": [], "probe": probe},
                "message": "未命中诊断管线触发（强词/弱词语境/模糊近义三层均未命中）"}
    if not execute:
        return _probe_only_result(decision, hits, probe)
    if not skill_text:
        return {"status": "error",
                "data": {"keywords": hits, "probe": probe},
                "message": ("执行管线需要非空 skill_dir"
                            "（空白路径不得回退到当前目录）")}
    if decision == "soft" and not allow_soft:
        return _soft_pending_result(skill_text, text, hits, probe)
    return _execute_trigger_pipeline(
        skill_text, text, hits, probe, decision=decision, full=full,
        max_steps=max_steps, max_batches=max_batches)
TRIGGER_EVENTS_MAX_AGE_DAYS = 35
TRIGGER_EVENTS_MAX_LINES = 5000
def _parse_trigger_event_line(raw_line: str) -> dict[str, Any] | None:
    line = raw_line.strip()
    if not line:
        return None
    try:
        entry = json.loads(line)
    except (ValueError, TypeError, RecursionError) as _e:
        logger.debug("触发留痕坏行跳过: %s", _e)
        return None
    return entry if isinstance(entry, dict) else None
def _line_epoch_or_none(stripped: str) -> float | None:
    entry = _parse_trigger_event_line(stripped)
    if entry is None:
        return None
    ts = entry.get("ts", "")
    if not isinstance(ts, str) or not ts:
        return None
    dt = parse_log_ts(ts)
    if dt is None:
        logger.debug("触发留痕时间戳不可解析，按污染行清理: %r", ts)
        return None
    try:
        epoch = dt.timestamp()
    except (OverflowError, OSError, ValueError) as _e:
        logger.debug("触发留痕时间戳越界，按污染行清理: %r: %s", ts, _e)
        return None
    if epoch - time.time() > TRIGGER_EVENTS_MAX_AGE_DAYS * 86400:
        logger.debug("触发留痕时间戳超出保留窗口，按污染行清理: %r", ts)
        return None
    return epoch
def _collect_kept_trigger_lines(path: str,
                                cutoff_epoch: float) -> tuple[list[str], int]:
    kept: list[str] = []
    removed = 0
    with open(path, encoding="utf-8-sig", errors="replace") as f:
        for line in f:
            stripped = line.strip()
            if not stripped:
                removed += 1
                continue
            epoch = _line_epoch_or_none(stripped)
            if epoch is None or epoch < cutoff_epoch:
                removed += 1
                continue
            kept.append(stripped)
    return kept, removed
def _apply_trigger_line_cap(kept: list[str]) -> tuple[list[str], int]:
    overflow = len(kept) - TRIGGER_EVENTS_MAX_LINES
    if overflow <= 0:
        return kept, 0
    return kept[-TRIGGER_EVENTS_MAX_LINES:], overflow
def _prune_trigger_events(log_dir: str) -> None:
    path = os.path.join(log_dir, TRIGGER_EVENTS_FILE)
    try:
        if not os.path.isfile(path):
            return
        with locked_artifact(path) as locked:
            if not locked or not os.path.isfile(path):
                return
            cutoff_epoch = time.time() - TRIGGER_EVENTS_MAX_AGE_DAYS * 86400
            kept, removed = _collect_kept_trigger_lines(path, cutoff_epoch)
            kept, capped = _apply_trigger_line_cap(kept)
            removed += capped
            if removed == 0:
                return
            atomic_write_text(
                path, "\n".join(kept) + ("\n" if kept else ""),
                tag="trigger_events")
    except Exception:
        logger.warning("触发留痕裁剪失败（留痕不再有界，下次追加重试）",
                       exc_info=True)
def _build_trigger_entry(decision: str, confidence: str, text: str,
                         source: str, evidence: dict | None,
                         extra: dict | None,
                         skill_dir: str | None = None) -> dict:
    entry = _as_dict(extra)
    entry.update({
        "ts": now_iso_seconds(),
        "decision": decision,
        "confidence": (confidence if isinstance(confidence, str)
                       else str(confidence or "")),
        "source": source,
        "text": (str(text) if text else "")[:120],
    })
    if evidence:
        entry["evidence"] = evidence
    skill_text = _as_path_text(skill_dir)
    if skill_text:
        entry["skill_dir"] = normalize_skill_dir(skill_text)
    return entry
def _append_trigger_entry(log_dir: str, entry: dict) -> bool:
    written = append_jsonl_locked(
        os.path.join(log_dir, TRIGGER_EVENTS_FILE),
        json.dumps(entry, ensure_ascii=False))
    _prune_trigger_events(log_dir)
    return written
def record_trigger_event(skill_dir: str | None, decision: str, confidence: str,
                         text: str, evidence: dict | None = None,
                         source: str = "session",
                         extra: dict | None = None) -> bool:
    skill_text = _as_path_text(skill_dir)
    if os.environ.get("JWSGJ_TRIGGER_LOG", "1") == "0" or not skill_text:
        return False
    try:
        log_dir = get_log_dir()
        if not log_dir:
            return False
        return _append_trigger_entry(log_dir, _build_trigger_entry(
            decision, confidence, text, source, evidence, extra,
            skill_dir=skill_text))
    except Exception as e:  # noqa: BLE001
        logger.debug("触发留痕跳过: %s", e)
        return False
MINER_NOISE_TOKENS: frozenset[str] = frozenset((
    "帮我", "麻烦", "请问", "可以", "能够", "应该", "想要", "需要",
    "一下", "这个", "那个", "一个", "这些", "那些", "什么", "怎么",
    "看看", "给一", "给我", "没有", "不是", "不会", "能否", "可否",
    "好好", "尽快", "顺手", "稍微", "大概", "其实", "就是", "还是",
    "the", "is", "to", "of", "and", "in", "on", "for", "with",
    "at", "by", "an", "be", "this", "that", "it", "my", "me",
    "we", "our", "your", "do", "can", "please", "help", "need",
    "want", "have", "has", "are", "was", "were", "not", "but",
    "so", "if", "then", "you", "i",
))
_DIGITS_ONLY = re.compile(r"^[0-9]+$")
_CJK_CHAR_RE = re.compile(r"^[\u4e00-\u9fff]+$")
_WEAK_CHARS = frozenset("的这那一里上下之其在与和一是只")
def _trigger_events_path(skill_dir: str | None) -> str | None:
    if not _as_path_text(skill_dir):
        return None
    try:
        _dir = get_log_dir()
        return os.path.join(_dir, TRIGGER_EVENTS_FILE) if _dir else None
    except (OSError, RuntimeError, TypeError, ValueError):
        logger.debug("[TriggerMiner] 留痕路径归口解析失败: %r", skill_dir)
        return None
def _read_event_file(path: str) -> list[dict[str, Any]]:
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as f:
            entries: list[dict[str, Any]] = []
            for raw_line in f:
                entry = _parse_trigger_event_line(raw_line)
                if entry is not None:
                    entries.append(entry)
            return entries
    except OSError:
        logger.warning("[TriggerMiner] 留痕文件读取失败: %s", path)
        return []
def _event_belongs_to_skill(entry: dict[str, Any], current: str) -> bool:
    raw = entry.get("skill_dir")
    if raw is None or raw == "":
        return False
    raw_text = _as_path_text(raw)
    if not raw_text:
        return False
    try:
        raw_project = os.path.normcase(os.path.realpath(
            normalize_skill_dir(raw_text)))
        current_project = os.path.normcase(os.path.realpath(current))
        return raw_project == current_project
    except (OSError, RuntimeError, TypeError, ValueError):
        logger.debug("[TriggerMiner] 丢弃非法项目归属的留痕: %r", raw)
        return False
def read_trigger_events(skill_dir: str | None) -> list[dict[str, Any]]:
    path = _trigger_events_path(skill_dir)
    if not path or not os.path.isfile(path):
        return []
    skill_text = _as_path_text(skill_dir)
    if not skill_text:
        return []
    try:
        current = normalize_skill_dir(skill_text)
    except (OSError, RuntimeError, TypeError, ValueError):
        logger.debug("[TriggerMiner] 当前项目归属非法，不读取共享留痕: %r",
                     skill_dir)
        return []
    return [entry for entry in _read_event_file(path)
            if _event_belongs_to_skill(entry, current)]
def _event_weight(entry: dict[str, Any]) -> int:
    if signal_bool(entry.get("ai_hit")):
        return 3
    if entry.get("decision") == "soft" and signal_bool(entry.get("executed")):
        return 2
    return 1
def _is_negative_entry(text: str) -> bool:
    return any(ctx in text for ctx in TRIGGER_NEGATIVE_CONTEXTS)
def _is_weak_bigram(token: str, verb_values: frozenset[str]) -> bool:
    tok = token.lower()
    if len(tok) != 2 or not _CJK_CHAR_RE.match(tok):
        return False
    if tok in verb_values:
        return False
    return any(ch in _WEAK_CHARS for ch in tok)
def _verb_cluster(token: str, verb_map: dict[str, list[str]]) -> str | None:
    tok = token.lower()
    for verb, synonyms in verb_map.items():
        if tok == verb or tok in synonyms:
            return verb
    return None
def _fuzzy_seed(token: str, seed_pairs: tuple[tuple[str, frozenset], ...]) -> str | None:
    tok = token.lower()
    for seed, seed_tokens in seed_pairs:
        if tok in seed_tokens:
            return seed
    return None
@dataclass(frozen=True)
class _MinerFilterBases:
    strong: frozenset[str]
    custom: frozenset[str]
    weak: frozenset[str]
    ctx_tokens: frozenset[str]
    verb_values: frozenset[str]
    blocked: frozenset[str] = field(init=False)
    def __post_init__(self) -> None:
        blocked = (self.strong | self.custom | self.weak | self.ctx_tokens
                   | MINER_NOISE_TOKENS)
        object.__setattr__(self, "blocked", blocked)
def _load_miner_filter_bases(skill_dir: str | None) -> _MinerFilterBases:
    verb_values = frozenset(VERB_SYNONYM_EXPANSION) | frozenset(
        v for vs in VERB_SYNONYM_EXPANSION.values() for v in vs)
    return _MinerFilterBases(
        strong=frozenset(k.lower() for k in PIPELINE_TRIGGER_KEYWORDS),
        custom=frozenset(k.lower() for k in load_custom_trigger_keywords(skill_dir)),
        weak=frozenset(TRIGGER_WEAK_TOKENS),
        ctx_tokens=frozenset(TRIGGER_CONTEXT_TOKENS),
        verb_values=verb_values,
    )
def _accumulate_entry(acc: dict, entry: dict[str, Any],
                      bases: _MinerFilterBases) -> int:
    raw_text = entry.get("text")
    if not isinstance(raw_text, str):
        return 0
    text = raw_text.strip()
    if not text or _is_negative_entry(text):
        return 0
    weight = _event_weight(entry)
    for token in trigger_tokens(normalize_trigger_text(text)):
        key = token.lower()
        if _token_filtered(key, bases):
            continue
        _accumulate_slot(acc, key, token, weight, text)
    return weight
def _accumulate_candidate_weights(entries, bases: _MinerFilterBases) -> tuple[dict, int]:
    acc: dict[str, dict[str, Any]] = {}
    total_weight = 0
    for entry in entries:
        total_weight += _accumulate_entry(acc, entry, bases)
    return acc, total_weight
def _token_filtered(key: str, bases: _MinerFilterBases) -> bool:
    return (key in bases.blocked or bool(_DIGITS_ONLY.match(key))
            or _is_weak_bigram(key, bases.verb_values))
def _accumulate_slot(acc: dict, key: str, token: str, w, text: str) -> None:
    slot = acc.setdefault(key, {"word": token, "weight": 0,
                                "event_count": 0, "examples": []})
    slot["weight"] += w
    slot["event_count"] += 1
    if text not in slot["examples"] and len(slot["examples"]) < 3:
        slot["examples"].append(text)
def _passes_candidate_gate(key: str, slot: dict, min_weight: int,
                           verb_values) -> bool:
    if slot["weight"] < min_weight:
        return False
    if min_weight <= 1:
        return True
    return key in verb_values or slot["event_count"] >= 2
def _finalize_candidates(acc, min_weight, verb_values, seed_pairs) -> tuple[list, dict]:
    candidates: list[dict[str, Any]] = []
    clusters: dict[str, list[str]] = {}
    for key, slot in acc.items():
        if not _passes_candidate_gate(key, slot, min_weight, verb_values):
            continue
        token = slot["word"]
        verb = _verb_cluster(key, VERB_SYNONYM_EXPANSION)
        seed = _fuzzy_seed(key, seed_pairs)
        slot["cluster"] = verb
        slot["fuzzy_seed"] = seed
        if verb:
            clusters.setdefault(verb, []).append(token)
        candidates.append(slot)
    candidates.sort(key=lambda c: (-c["weight"], c["word"]))
    for words in clusters.values():
        words.sort()
    return candidates, clusters
_DEFAULT_MINER_MIN_WEIGHT = 2
def _norm_min_weight(value: Any) -> int:
    if isinstance(value, bool):
        value = None
    if isinstance(value, str):
        text = value.strip()
        try:
            value = float(text) if text else None
        except ValueError:
            value = None
    if isinstance(value, int) and value >= 0:
        return value
    if isinstance(value, float) and 0 <= value < float("inf"):
        return int(value)
    logger.warning("[TriggerMiner] 权重门槛脏值 %r，已归默认 %d",
                   value, _DEFAULT_MINER_MIN_WEIGHT)
    return _DEFAULT_MINER_MIN_WEIGHT
def mine_trigger_events(skill_dir: str | None,
                        min_weight: int = _DEFAULT_MINER_MIN_WEIGHT) -> dict[str, Any]:
    min_weight = _norm_min_weight(min_weight)
    entries = read_trigger_events(skill_dir)
    bases = _load_miner_filter_bases(skill_dir)
    seed_pairs = seed_token_pairs()
    acc, total_weight = _accumulate_candidate_weights(entries, bases)
    candidates, clusters = _finalize_candidates(
        acc, min_weight, bases.verb_values, seed_pairs)
    _src = _trigger_events_path(skill_dir) or ""
    return {
        "generated_at": now_iso_seconds(),
        "source": _src,
        "min_weight": min_weight,
        "events": len(entries),
        "total_weight": total_weight,
        "candidates": candidates,
        "clusters": clusters,
    }
def _md_cell(text: str) -> str:
    if not isinstance(text, str):
        text = ""
    return (text.replace("|", "\\|")
            .replace("\r\n", " ")
            .replace("\n", " ")
            .replace("\r", " "))
def _cell_int(v) -> int:
    return v if isinstance(v, int) and not isinstance(v, bool) else 0
def _cell_list(v) -> list:
    return v if isinstance(v, list) else []
def _cell_key(v) -> str:
    if isinstance(v, str):
        return _md_cell(v)
    try:
        return str(v)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context=f'_cell_key:{type(_e).__name__}')
        return f"<{type(v).__name__}>"
def render_miner_report(report: dict[str, Any]) -> str:
    if not isinstance(report, dict):
        report = {}
    lines = [
        "# 触发词挖掘建议报告",
        "",
        f"- 生成时间: {_md_cell(report.get('generated_at', ''))}",
        f"- 留痕来源: `{_md_cell(report.get('source', ''))}`",
        (f"- 留痕条目: {_cell_int(report.get('events', 0))}"
         f"（总权重 {_cell_int(report.get('total_weight', 0))}）"),
        f"- 权重门槛: {_cell_int(report.get('min_weight', 0))}",
        "",
        "## 建议新词",
        "",
    ]
    candidates = _cell_list(report.get("candidates"))
    if not candidates:
        lines.append("（无达到权重门槛的候选词）")
        lines.append("")
        return "\n".join(lines)
    _render_candidates_table(lines, candidates)
    clusters = report.get("clusters")
    _render_clusters_section(lines, clusters if isinstance(clusters, dict) else {})
    lines.append("> 人工审核：候选词并入目标项目的触发词注册表后，"
                 "必须运行对应的正负语料回归，并同步该项目示例集、"
                 "触发条件文档与版本元数据。")
    return "\n".join(lines)
def _render_candidates_table(lines: list[str], candidates: list) -> None:
    lines.append("| 候选词 | 权重 | 事件数 | 动词同义组 | 模糊种子 | 示例 |")
    lines.append("|--------|------|--------|-----------|---------|------|")
    for c in candidates:
        if not isinstance(c, dict):
            continue
        word = _md_cell(c.get("word") or "")
        weight = _cell_int(c.get("weight", 0))
        event_count = _cell_int(c.get("event_count", 0))
        cluster = _md_cell(c.get("cluster") or "")
        seed = _md_cell(c.get("fuzzy_seed") or "")
        examples = "<br>".join(
            _md_cell(e) for e in _cell_list(c.get("examples")))
        lines.append(
            f"| {word} | {weight} | {event_count} "
            f"| {cluster} | {seed} | {examples} |")
    lines.append("")
def _render_clusters_section(lines: list[str], clusters: dict) -> None:
    if not clusters:
        return
    lines.append("## 近义词簇")
    lines.append("")
    for verb in sorted(clusters, key=_cell_key):
        lines.append(f"- **{_cell_key(verb)}**: " + "、".join(
            _md_cell(w) for w in _cell_list(clusters[verb])))
    lines.append("")
if __name__ == "__main__":
    main()

from __future__ import annotations

import logging
import os
import time
import traceback
from collections import Counter
from collections.abc import Callable
from typing import Any

import jwsgj.treatment_experience as _stage4
from jwsgj.ai_review_governance import (
    list_pending_ai_reviews,
    read_pending_reviews,
)
from jwsgj.ai_review_item_plan import (
    apply_code_level_feedback_step,
    code_feedback_phase_payload,
    stage_code_feedback,
)
from jwsgj.cleanup_artifacts import run_post_completion_governance
from jwsgj.diag_types_normalize import (
    as_list,
    dict_items,
    dict_or_empty,
    elapsed_seconds,
    int_coerce,
    int_or,
    len_safe,
    method_status_bucket,
    safe_float,
    signal_bool,
    str_or,
    timestamp_human,
    timestamp_ms,
)
from jwsgj.diag_zero_backlog_gate import (
    _validate_pending_reviews,
    apply_delivery_gates,
    run_fp_fixation_step,
)
from jwsgj.fanout_governance import (
    emit_fanout_report,
    fanout_evolution_signal,
    fanout_pre_treatment_block,
    run_fanout_diagnosis,
)
from jwsgj.fanout_report import load_fanout_findings
from jwsgj.fupan_engine import (
    build_stage5_fupan_context,
    run_stage6a_fupan,
)
from jwsgj.html_render_pipeline import (
    emit_coverage_report_html,
    emit_dependency_report_html,
    emit_step_html,
    emit_treatment_item_report,
    generate_html_report,
    html_report_path,
)
from jwsgj.log_config import timed_log
from jwsgj.memory_feedback_core import build_pipeline_context
from jwsgj.pipeline_report_assembly import (
    build_review_quality_augmentation,
    run_stage2a_regression_cv,
    run_stage2b_main_cv,
)
from jwsgj.pipeline_report_delivery import (
    cv_out_view,
    cv_phase_extra,
    emit_cv_report,
    finalize_completed_pipeline,
    load_cv_report_tolerant,
    load_method_adjustments_tolerant,
    load_stage6_inputs,
    load_stage_cv_report,
    load_stages_from_files,
    regression_out_view,
    resolve_treatment_plan,
    step_run_payload,
)
from jwsgj.pipeline_round_trace import (
    PipelineContext,
    advance_pipeline_phase,
    cleanup_legacy_fix_route_report,
    current_round_anchor,
    persist_review_result,
    progress_of,
    publish_step_result,
    query_methods_progress,
    round_start_epoch,
    run_step_shell,
    save_treatment_plan,
    treatment_exec_result,
    treatment_progress_of,
    treatment_trace_metrics,
)
from jwsgj.retrospective_enhancer import (
    extract_stage5_cv_metrics,
    run_stage5_review_engine,
    run_stage6d_auto_enhance,
)
from jwsgj.retrospective_evolution import (
    persist_review_enhancements_step,
    record_main_cv_defense_feedback,
    record_regression_cv_defense_feedback,
    run_defense_feedback_step,
    run_feedback_loop_stage,
    run_fp_evolution_step,
    zero_batch_fp_result,
)
from jwsgj.shared_cache import (
    carry_failure_detail,
    get_warmed_cache,
    mem_bus_put,
    mem_bus_take,
)
from jwsgj.treatment_evidence import (
    build_dry_route_report,
)
from jwsgj.treatment_experience import execute_treatment_item_core
from jwsgj.treatment_feedback import run_feedback_loop
from jwsgj.treatment_plan import (
    apply_safety_overrides,
    attach_fix_coverage,
    enhance_plan_with_memory,
    generate_treatment_plan,
    log_plan_generated,
    plan_dict_or_empty,
    plan_step_extras,
    project_plan_stage_result,
    reset_artifacts_after_plan,
)
from jwsgj.xv_intermediate_store import (
    normalize_round_start_ts,
)

__all__ = [
    "FANOUT_ADVANCE_STATUSES",
    "advance_phase_safe",
    "attach_pending_review_info",
    "build_review_out",
    "complete_stage6d_governance",
    "execute_treatment_item",
    "iter_shell_steps",
    "load_round_fanout_findings",
    "phase_reached",
    "resolve_fanout_diagnosis_inputs",
    "run_ai_manual_fix_step",
    "run_auto_enhance_step",
    "run_code_feedback_step",
    "run_cv_step",
    "run_dry_route_step",
    "run_fanout_diagnosis_step",
    "run_feedback_loop_step",
    "run_fupan_step",
    "run_phase_handler",
    "run_regression_cv_step",
    "run_review_body",
    "run_review_step",
    "run_stage5_review",
    "run_stage6b_feedback_loop",
    "run_stage6c_code_feedback",
    "run_traced_entry",
    "run_treatment_plan_step",
    "run_treatment_step",
    "stay_result",
    "step_result",
]
logger = logging.getLogger(__name__)
_MODULE_NAME = __name__.rsplit(".", 1)[-1]
_STEP_DONE_STATUS = "completed"
logger.info("pipeline_steps_phases 域已加载: %d 项导出", len(__all__))
def _entry_failure(skill_dir: str, exc: Exception) -> dict[str, Any]:
    return {"ok": False, "skill_dir": skill_dir, "error": str(exc),
            "status": "failed"}
def run_traced_entry(entry: str, step_name: str, skill_dir: str,
                     body: Any) -> Any:
    result: Any = None
    try:
        get_warmed_cache(skill_dir)
        result = body()
        return result
    except Exception as e:
        logger.warning("%s except: %s", entry, e, exc_info=True)
        result = _entry_failure(skill_dir, e)
        return result
    finally:
        try:
            emit_step_html(step_name, skill_dir, result)
        except Exception as emit_exc:  # noqa: BLE001
            logger.warning("%s 步骤留痕失败(不阻断): %s", entry, emit_exc)
def step_result(phase: str, phase_label: str, task_type: str,
                task_result, next_phase, progress: dict,
                **extra) -> dict:
    out = {
        "phase": phase,
        "phase_label": phase_label,
        "task_type": task_type,
        "task_result": task_result,
        "next_phase": next_phase,
        "is_terminal": False,
        "progress": progress,
    }
    out.update(extra)
    return out
def _coerce_step_result(task_result) -> dict:
    if isinstance(task_result, dict):
        return task_result
    return {
        "status": "error",
        "error": (f"phase step returned non-dict "
                  f"{type(task_result).__name__}"),
    }
def _invoke_step(step_fn, *args, step_name: str = "", **kwargs) -> dict:
    try:
        return _coerce_step_result(step_fn(*args, **kwargs))
    except Exception as e:
        logger.warning("[PhaseHandler] 步骤 %s 上抛异常，归一 error 停留本相位: %s",
                       getattr(step_fn, "__name__", step_fn), e, exc_info=True)
        _err = {"status": "error", "error": str(e)[:500]}
        try:
            emit_step_html(_step_emit_name(step_fn, step_name),
                            _step_skill_dir(args, kwargs), _err)
        except Exception as _he:  # noqa: BLE001
            logger.warning("[PhaseHandler] 异常兜底 HTML 生成失败(不阻断): %s", _he)
        return _err
def _step_emit_name(step_fn, step_name: str) -> str:
    _raw = step_name or getattr(step_fn, "__name__", "") or ""
    return _raw if _raw and not _raw.startswith("<") else "pipeline_step"
def _step_skill_dir(args, kwargs) -> str:
    if args and isinstance(args[0], (str, os.PathLike)):
        return str(args[0])
    return str(kwargs.get("skill_dir") or "")
def stay_result(sd: str, phase: str, label: str, task_type: str,
                 error: str) -> dict:
    return step_result(phase, label, task_type,
                        {"status": "error", "error": error}, phase,
                        progress_of(sd),
                        next_action="run_next_pipeline_step")
def _read_valid_pending_reviews(sd: str) -> tuple[dict, int, str]:
    agg, read_err = read_pending_reviews(sd)
    if read_err:
        return {}, 0, read_err
    return _validate_pending_reviews(agg)
def _read_pending_or_stay(sd: str, phase: str, label: str,
                          task_type: str,
                          log_tag: str = "[PhaseHandler]") -> tuple[dict, dict | None]:
    agg, _pending_n, read_err = _read_valid_pending_reviews(sd)
    if not read_err:
        return agg, None
    logger.warning("%s 待审核清单读取失败，停留本相位待重试: %s",
                   log_tag, read_err)
    return {}, stay_result(sd, phase, label, task_type, read_err)
def advance_phase_safe(sd: str, new_phase: str,
                        extra: dict | None = None) -> tuple[bool, str]:
    try:
        advance_pipeline_phase(sd, new_phase, extra)
        return True, ""
    except Exception as e:
        logger.warning("[PhaseHandler] 相位推进写盘失败（停留待重试）:"
                       " → %s: %s", new_phase, e, exc_info=True)
        return False, str(e)[:500]
_PNS_PHASE_CHAIN = (
    "pending_diagnosis", "diagnosis_done", "cv_regression_done",
    "cv_main_done", "fanout_done", "plan_dry_done", "plan_generated",
    "treatment_done",
    "ai_fix_pending", "ai_fix_done", "review_done", "fupan_done",
    "feedback_done", "code_feedback_done", "evolution_pending",
    "all_completed",
)
_PNS_PHASE_REACHED: dict[str, int] = {p: i for i, p in enumerate(_PNS_PHASE_CHAIN)}
def phase_reached(current: str, milestone: str) -> bool:
    if not isinstance(current, str) or not isinstance(milestone, str):
        return False
    _ci = _PNS_PHASE_REACHED.get(current)
    _mi = _PNS_PHASE_REACHED.get(milestone)
    if _ci is None or _mi is None:
        return False
    return _ci >= _mi
def _make_simple_phase_handler(phase: str, step, label: str,
                               task_type: str, done_phase: str):
    def _handler(sd: str) -> dict:
        task_result = _invoke_step(step, sd, step_name=task_type)
        next_phase = (done_phase
                      if task_result.get("status") == _STEP_DONE_STATUS
                      else phase)
        return step_result(phase, label, task_type, task_result,
                            next_phase, progress_of(sd))
    return _handler
def _fanout_pre_treatment_block(sd: str) -> dict | None:
    blocked = fanout_pre_treatment_block(sd)
    if blocked is None:
        return None
    gate = blocked.get("gate")
    logger.warning("[PhaseHandler] 阶段G门禁阻断治疗执行: %s",
                   blocked.get("reason"))
    return step_result(
        "plan_generated", blocked.get("message"), "fanout_gate",
        {"status": "blocked", "reason": blocked.get("reason"),
         "gate": gate}, "plan_generated",
        progress_of(sd), next_action="fix_fanout_plan_gap",
        fanout_gate=gate)
def _pns_phase_plan_generated(sd: str) -> dict:
    _blocked = _fanout_pre_treatment_block(sd)
    if _blocked is not None:
        return _blocked
    task_result = _invoke_step(run_treatment_step, sd, step_name="treatment")
    treatment_progress = treatment_progress_of(sd)
    step_status = task_result.get("status")
    if step_status not in ("planned", "skipped", "fp_confirmed", "no_more_items"):
        return step_result(
            "plan_generated",
            f"阶段4: 治疗执行未完成({step_status or 'missing'})，停留待重试",
            "treatment", task_result, "plan_generated", progress_of(sd))
    if treatment_progress.get("status") in (_STEP_DONE_STATUS, "no_plan"):
        _ok, _adv_err = advance_phase_safe(
            sd, "treatment_done",
            treatment_trace_metrics(treatment_progress))
        if not _ok:
            return stay_result(
                sd, "plan_generated",
                "阶段4治疗完成但相位推进写盘失败，停留待重试",
                "treatment", _adv_err)
        return step_result(
            "plan_generated", "阶段3完成 → 阶段4: 治疗完成", "treatment",
            task_result, "treatment_done", progress_of(sd))
    return step_result(
        "plan_generated", "阶段4: 治疗执行中（逐项）", "treatment",
        task_result, "plan_generated", progress_of(sd))
def _pending_reviews_payload(agg: Any, pending_n: Any) -> dict:
    _agg = dict_or_empty(agg)
    return {
        "pending_ai_review": int_coerce(pending_n),
        "pending_reviews": as_list(_agg.get("reviews")),
    }
def _pending_channel_payload(agg: Any, pending_n: Any) -> dict:
    _agg = dict_or_empty(agg)
    return {"pending_ai_review": int_coerce(pending_n),
            "by_channel": dict_or_empty(_agg.get("by_channel"))}
def attach_pending_review_info(out: dict, sd: str) -> None:
    if not isinstance(out, dict):
        logger.warning("[PipelineBatch] 收尾结果非 dict(%s)，跳过待审核回填",
                       type(out).__name__)
        return
    _agg, _pending_n, _err = _read_valid_pending_reviews(sd)
    if _err:
        logger.warning("[PipelineBatch] 待审核清单读取失败: %s", _err)
        return
    out.update(_pending_reviews_payload(_agg, _pending_n))
    out["review_framework"] = _agg.get("review_framework")
def _treatment_route_to_pending(sd: str, agg: dict, pending_n: int,
                                task_result: dict) -> dict:
    _ok, _adv_err = advance_phase_safe(
        sd, "ai_fix_pending", {"pending_ai_review": pending_n})
    if not _ok:
        return stay_result(
            sd, "treatment_done",
            "阶段4完成但改道待审核写盘失败，停留待重试",
            "ai_manual_fix", _adv_err)
    return step_result(
        "treatment_done",
        f"阶段4完成(方案已生成) → 阶段4b: 待 AI 审核执行（{pending_n} 项）",
        "ai_manual_fix", task_result, "ai_fix_pending",
        progress_of(sd),
        next_action="run_next_ai_review",
        **_pending_reviews_payload(agg, pending_n))
def _treatment_stay_on_list_error(sd: str, task_result: dict,
                                  task_status, list_err: str) -> dict:
    _ok, _adv_err = advance_phase_safe(
        sd, "treatment_done",
        treatment_trace_metrics(treatment_progress_of(sd)))
    if not _ok:
        return stay_result(
            sd, "treatment_done",
            "待审核清单读取失败且回拨写盘失败，停留待重试",
            "ai_manual_fix", f"{list_err}; 回拨: {_adv_err}")
    _list_msg = ("阶段4零遗留门禁阻塞且待审核清单读取失败，停留待重试"
                 if task_status == "leftover_blocked"
                 else "阶段4完成但待审核清单读取失败，停留待重试")
    return step_result(
        "treatment_done",
        _list_msg,
        "ai_manual_fix", task_result, "treatment_done",
        progress_of(sd),
        next_action="run_next_pipeline_step")
def _leftover_desc(leftover: dict) -> str:
    if leftover.get("state_integrity") == "torn":
        return str(leftover.get("state_integrity_reason") or "治疗状态撕裂")
    return f"{leftover.get('leftover_count', '?')} 项未终态"
def _treatment_leftover_blocked(sd: str, task_result: dict) -> dict:
    _leftover = dict_or_empty(task_result.get("zero_leftover"))
    return step_result(
        "treatment_done",
        (f"阶段4完成但零遗留门禁阻塞（"
         f"{_leftover_desc(_leftover)}，"
         "审核队列已空 — 按 actions_required 逐项处置）"),
        "zero_leftover_blocked", task_result, "treatment_done",
        progress_of(sd),
        next_action="handle_leftover_items",
        **_pending_reviews_payload({}, 0))
def _pns_phase_treatment_done(sd: str) -> dict:
    task_result = _invoke_step(run_ai_manual_fix_step, sd,
                               step_name="ai_fix")
    _task_status = task_result.get("status")
    if _task_status not in (_STEP_DONE_STATUS, "preview",
                            "leftover_blocked", "blocked", "error"):
        _task_status = "error"
    if _task_status in ("blocked", "error"):
        return step_result(
            "treatment_done",
            f"阶段4b: AI 修复候选导出未完成({_task_status})，停留待重试",
            "ai_manual_fix", task_result, "treatment_done",
            progress_of(sd))
    _leftover = dict_or_empty(task_result.get("zero_leftover"))
    if _leftover.get("state_integrity") == "torn":
        return step_result(
            "treatment_done",
            (f"阶段4b: 治疗状态撕裂（{_leftover_desc(_leftover)}），"
             "零遗留无法核验，停留待重试"),
            "zero_leftover_blocked", task_result, "treatment_done",
            progress_of(sd), next_action="run_next_pipeline_step")
    _agg, _pending_n, _list_err = _read_valid_pending_reviews(sd)
    if _list_err:
        logger.warning("[TreatmentDone] 待审核清单读取失败，停留本阶段待重试: %s", _list_err)
    if _pending_n > 0:
        return _treatment_route_to_pending(sd, _agg, _pending_n, task_result)
    if _list_err:
        return _treatment_stay_on_list_error(sd, task_result, _task_status, _list_err)
    if _task_status == "leftover_blocked":
        return _treatment_leftover_blocked(sd, task_result)
    _ok, _adv_err = advance_phase_safe(
        sd, "ai_fix_done", {"pending_ai_review": 0})
    if not _ok:
        return stay_result(
            sd, "treatment_done",
            "阶段4b候选装配完成但相位推进写盘失败，停留待重试",
            "ai_manual_fix", _adv_err)
    return step_result(
        "treatment_done",
        "阶段4完成(治疗项执行) → 阶段4b: AI手动修复",
        "ai_manual_fix", task_result, "ai_fix_done",
        progress_of(sd), pending_ai_review=0,
        next_action="run_next_pipeline_step")
def _pns_phase_ai_fix_pending(sd: str) -> dict:
    _agg, _stay = _read_pending_or_stay(
        sd, "ai_fix_pending", "阶段4b: 待审核清单读取失败，待重试",
        "ai_review_pending", "[AIReviewPending]")
    if _stay is not None:
        return _stay
    _pending_n = _agg["pending_ai_review"]
    if _pending_n == 0:
        _ok, _adv_err = advance_phase_safe(
            sd, "ai_fix_done", {"pending_ai_review": 0})
        if not _ok:
            return stay_result(
                sd, "ai_fix_pending",
                "阶段4b: 审核清零但推进写盘失败，停留待重试",
                "ai_review_complete", _adv_err)
        return step_result(
            "ai_fix_pending", "阶段4b: AI 审核执行完成",
            "ai_review_complete", {"status": "all_reviews_done"},
            "ai_fix_done", progress_of(sd),
            pending_ai_review=0, next_action="run_next_pipeline_step")
    # 审核队列未清零不再冻结整条管线：复盘（5）与反哺（6a~6c）只分析诊断
    # 质量与修复成效，不写被审源码，与「治疗是否清零」没有依赖关系。原实现
    # 无条件停留 ai_fix_pending，使 16 相位链永远到不了放行相位
    # （code_feedback_done / evolution_pending），复盘反哺进化整段不可达——
    # 这是「全链不能自动推进」的结构性根因。
    # 正确语义：待审项作为载荷向下传递（队列由治疗状态派生，不会丢失），
    # 由阶段 6d/6e 的交付门禁（apply_delivery_gates → zero_backlog）统一
    # 阻断；未审核条目也不会被写盘。
    _ok, _adv_err = advance_phase_safe(
        sd, "ai_fix_done",
        {"pending_ai_review": _pending_n, "review_deferred": True})
    if not _ok:
        return stay_result(
            sd, "ai_fix_pending",
            "阶段4b: 审核队列未清零且推进写盘失败，停留待重试",
            "ai_review_pending", _adv_err)
    return step_result(
        "ai_fix_pending",
        (f"阶段4b: 审核队列未清零（{_pending_n} 项）→ 先推进复盘/反哺，"
         "由交付门禁统一阻断"),
        "ai_review_deferred",
        {**_pending_channel_payload(_agg, _pending_n),
         "status": "review_deferred"},
        "ai_fix_done", progress_of(sd),
        pending_ai_review=_pending_n,
        review_deferred=True,
        review_framework=_agg.get("review_framework"),
        next_action="run_next_pipeline_step")
def _aifix_route_back_to_pending(
    sd: str, agg: dict, pass_n: int, *, task_result: dict | None = None,
    phase_label: str = "", task_type: str = "ai_review_pending",
) -> dict:
    _ok, _adv_err = advance_phase_safe(
        sd, "ai_fix_pending", {"pending_ai_review": pass_n})
    if not _ok:
        return stay_result(
            sd, "ai_fix_done",
            "阶段4b放行点改道写盘失败，停留待重试",
            task_type, _adv_err)
    payload = dict_or_empty(task_result)
    payload.update(_pending_channel_payload(agg, pass_n))
    return step_result(
        "ai_fix_done",
        phase_label or (
            f"阶段4b: 待审核队列未清零（{pass_n} 项），改道回审核执行"),
        task_type, payload,
        "ai_fix_pending", progress_of(sd),
        next_action="run_next_ai_review",
        **_pending_reviews_payload(agg, pass_n))
def _aifix_leftover_blocked(sd: str, leftover: dict) -> dict:
    _overlay = dict_or_empty(leftover)
    _agg, _pend_n, _read_err = _read_valid_pending_reviews(sd)
    if _read_err:
        logger.warning("[AiFixDone] 待审核清单读取失败，停留待重试: %s",
                       _read_err)
        return step_result(
            "ai_fix_done",
            (f"阶段4b完成但零遗留门禁阻塞（"
             f"{_leftover_desc(_overlay)}，"
             "待审核清单读取失败 — 停留待重试）"),
            "zero_leftover_blocked",
            {**_overlay, "status": "error", "error": _read_err},
            "ai_fix_done", progress_of(sd),
            next_action="run_next_pipeline_step")
    _queue_hint = ("审核队列已空 — 按 actions_required 逐项处置"
                   if _pend_n == 0 else "审核队列未排空 — 继续审核")
    _label = (f"阶段4b完成但零遗留门禁阻塞（"
              f"{_leftover_desc(_overlay)}，{_queue_hint}）")
    if _pend_n > 0:
        return _aifix_route_back_to_pending(
            sd, _agg, _pend_n,
            task_result={**_overlay, "status": "leftover_blocked"},
            phase_label=_label, task_type="zero_leftover_blocked")
    return step_result(
        "ai_fix_done", _label, "zero_leftover_blocked",
        {**_overlay, "status": "leftover_blocked"}, "ai_fix_done",
        progress_of(sd), next_action="handle_leftover_items",
        **_pending_reviews_payload(_agg, 0))
def _pns_phase_ai_fix_done(sd: str) -> dict:
    # 待审核清单必须先读：它是「放行到阶段5」与「改道回审核」的唯一分叉依据。
    # 原实现把零遗留门禁放在前面，且门禁未过就无条件改道回 ai_fix_pending，
    # 使审核队列非空时复盘/反哺/进化整段不可达（16 相位链永远到不了放行相位）。
    _agg, _pass_n, _pass_list_err = _read_valid_pending_reviews(sd)
    if _pass_list_err:
        logger.warning("[AiFixDone] 放行点待审核清单读取失败，保守阻塞待重试: %s", _pass_list_err)
        return step_result(
            "ai_fix_done",
            "阶段4b完成但待审核清单读取失败，保守阻塞待重试（未清零不放行）",
            "ai_review_pending",
            {"status": "error", "error": _pass_list_err},
            "ai_fix_done", progress_of(sd),
            next_action="run_next_pipeline_step")
    leftover = _stage4.verify_treatment_zero_leftover(sd)
    if leftover.get("state_integrity") == "error":
        return step_result(
            "ai_fix_done", "阶段4b完成但零遗留门禁核验异常，保守阻塞待重试",
            "zero_leftover_blocked",
            {**dict_or_empty(leftover), "passed": False, "status": "error"},
            "ai_fix_done", progress_of(sd),
            next_action="run_next_pipeline_step")
    _leftover_ok = (leftover.get("state_integrity") != "torn"
                    and bool(leftover.get("passed", False)))
    if not _leftover_ok:
        if _pass_n <= 0:
            # 队列已空且仍有非终态遗留项：没有任何通道能消费它们，属实打实
            # 的状态机死点，保守阻塞并暴露到 actions_required。
            return _aifix_leftover_blocked(sd, {**leftover, "passed": False})
        # 队列非空：遗留项就是待审候选，交给阶段 6d/6e 的交付门禁统一阻断，
        # 不在 4b 提前截断，否则复盘/反哺/进化永远跑不到。
        logger.warning(
            "[AiFixDone] 零遗留门禁未通过（%s），但审核队列仍有 %d 项："
            "复盘/反哺不写被审源码，放行到阶段5，交付门禁统一阻断",
            _leftover_desc(leftover), _pass_n)
    task_result = _invoke_step(run_review_step, sd, step_name="review")
    return step_result(
        "ai_fix_done", "阶段4b完成(AI手动修复) → 阶段5: 复盘",
        "review", task_result,
        ("review_done" if task_result.get("status") == _STEP_DONE_STATUS
         else "ai_fix_done"),
        progress_of(sd),
        pending_ai_review=_pass_n)
def _pns_auto_enhance_pending_result(sd: str, phase: str,
                                     task_result: dict) -> dict:
    pending = int_coerce(task_result.get("pending_ai_review"))
    return step_result(
        phase, f"阶段6d/6e: 待 AI 审核执行（{pending} 项）",
        "evolution_pending", task_result, "evolution_pending",
        progress_of(sd), next_action="run_next_ai_review",
        **_pending_reviews_payload(
            {"reviews": task_result.get("pending_reviews", [])}, pending))
def _pns_phase_code_feedback_done(sd: str) -> dict:
    _agg, _stay = _read_pending_or_stay(
        sd, "code_feedback_done", "阶段6c完成 → 待审核清单读取失败，待重试",
        "evolution_pending", "[CodeFeedbackDone]")
    if _stay is not None:
        return _stay
    _pending_n = _agg["pending_ai_review"]
    if _pending_n > 0:
        _ok, _adv_err = advance_phase_safe(
            sd, "evolution_pending", {"pending_ai_review": _pending_n})
        if not _ok:
            return stay_result(
                sd, "code_feedback_done",
                "阶段6c完成但反哺改道写盘失败，停留待重试",
                "evolution_pending", _adv_err)
        return step_result(
            "code_feedback_done",
            f"阶段6c完成 → 阶段6e: 复盘反哺待 AI 审核执行（{_pending_n} 项）",
            "evolution_pending",
            _pending_channel_payload(_agg, _pending_n),
            "evolution_pending", progress_of(sd),
            next_action="run_next_ai_review",
            **_pending_reviews_payload(_agg, _pending_n))
    task_result = _invoke_step(run_auto_enhance_step, sd, step_name="auto_enhance")
    if task_result.get("status") == "evolution_pending":
        return _pns_auto_enhance_pending_result(sd, phase="code_feedback_done",
                                               task_result=task_result)
    is_terminal = task_result.get("status") == _STEP_DONE_STATUS
    return step_result(
        "code_feedback_done", "阶段6c完成 → 阶段6d: auto_enhance (最终)",
        "auto_enhance", task_result,
        "all_completed" if is_terminal else "code_feedback_done",
        progress_of(sd), is_terminal=is_terminal)
def _pns_phase_evolution_pending(sd: str) -> dict:
    _agg, _stay = _read_pending_or_stay(
        sd, "evolution_pending", "阶段6e: 待审核清单读取失败，待重试",
        "evolution_review_pending", "[EvolutionPending]")
    if _stay is not None:
        return _stay
    _pending_n = _agg["pending_ai_review"]
    if _pending_n == 0:
        task_result = _invoke_step(run_auto_enhance_step, sd,
                                  step_name="auto_enhance")
        if task_result.get("status") == "evolution_pending":
            return _pns_auto_enhance_pending_result(
                sd, phase="evolution_pending", task_result=task_result)
        _done = task_result.get("status") == _STEP_DONE_STATUS
        return step_result(
            "evolution_pending",
            ("阶段6e: 复盘反哺 AI 审核执行完成" if _done
             else "阶段6e: auto_enhance 收尾未完成，待重试"),
            "evolution_complete" if _done else "auto_enhance",
            task_result,
            "all_completed" if _done else "evolution_pending",
            progress_of(sd),
            pending_ai_review=0, next_action="run_next_pipeline_step",
            is_terminal=_done)
    return step_result(
        "evolution_pending",
        f"阶段6e: 复盘反哺待 AI 审核执行（{_pending_n} 项，逐项）",
        "evolution_review_pending",
        _pending_channel_payload(_agg, _pending_n),
        "evolution_pending", progress_of(sd),
        review_framework=_agg.get("review_framework"),
        next_action="run_next_ai_review",
        **_pending_reviews_payload(_agg, _pending_n))
def _pns_phase_all_completed(sd: str) -> dict:
    return step_result(
        "all_completed", "全部阶段（含阶段G）已完成", "none",
        {"status": "all_completed"}, None, progress_of(sd), is_terminal=True)
def resolve_fanout_diagnosis_inputs(skill_dir: str) -> tuple[dict, str, str]:
    try:
        source_report, source_path = load_cv_report_tolerant(skill_dir)
    except Exception as exc:  # noqa: BLE001
        logger.warning("[FanoutInputs] 源报告不可读(降级为无报告): %s", exc)
        source_report, source_path = {}, ''
    return source_report, source_path, current_round_anchor(skill_dir)
def _run_regression_cv_body(sd: str, stage_start: float) -> dict:
    ctx = build_pipeline_context(sd)
    result = run_stage2a_regression_cv(ctx)
    _status = result.get("status") or "failed"
    if _status == _STEP_DONE_STATUS:
        advance_pipeline_phase(sd, "cv_regression_done", {
            "regression_has_changes": bool(result.get("has_changes")),
            "regression_changed_files": int_or(result.get("changed_files_count")),
        })
    record_regression_cv_defense_feedback(sd, _status)
    out = regression_out_view(_status, result, stage_start)
    logger.info("[RegressionCVStep] 完成: has_changes=%s, %.1fs",
                 out["has_changes"], out["elapsed_s"])
    return out
def run_regression_cv_step(skill_dir: str) -> dict:
    return run_step_shell(
        skill_dir, guard_name="regression_cv", label="RegressionCVStep",
        body=lambda run: _run_regression_cv_body(run.skill_dir,
                                                 run.started_at),
        emit=lambda sd, out: emit_step_html("regression_cv", sd, out),
        perf_name="stage_regression_cv",
        module_name=_MODULE_NAME, entry="run_regression_cv_step",
        payload_fn=step_run_payload,
    )
def _run_cv_body(sd: str, output_html: str | None, stage_start: float) -> dict:
    logger.info("[CVStep] 阶段2: 交叉验证开始: %s", timestamp_human())
    diag_progress = query_methods_progress(sd)
    if not isinstance(diag_progress, dict):
        logger.warning("[CVStep] 诊断进度视图非 dict(%s)，按空进度继续",
                       type(diag_progress).__name__)
        diag_progress = {}
    if diag_progress.get("next_method") is not None:
        total = int_or(diag_progress.get("total"))
        completed = int_or(diag_progress.get("completed"))
        logger.warning(
            "[CVStep] 诊断未完成: %d/%d 方法, 继续执行交叉验证",
            completed, total
        )
    ctx = build_pipeline_context(sd)
    result = run_stage2b_main_cv(ctx)
    _status = result.get("status") or "failed"
    record_main_cv_defense_feedback(sd, result)
    emit_cv_report(sd, output_html, result)
    out = cv_out_view(_status, result, stage_start)
    if _status == _STEP_DONE_STATUS:
        advance_pipeline_phase(sd, "cv_main_done", cv_phase_extra(out, result))
    logger.info("[CVStep] 完成: %d findings, %.1fs",
                 out["total_findings"], out["elapsed_s"])
    return out
def run_cv_step(skill_dir: str, output_html: str | None = None) -> dict:
    return run_step_shell(
        skill_dir, guard_name="cv", label="CVStep",
        body=lambda run: _run_cv_body(
            run.skill_dir, output_html, run.started_at),
        emit=lambda sd, out: emit_step_html("cv", sd, out),
        perf_name="stage_cv",
        module_name=_MODULE_NAME, entry="run_cv_step",
        payload_fn=step_run_payload,
    )
_pns_phase_diagnosis_done = _make_simple_phase_handler(
    "diagnosis_done", run_regression_cv_step,
    "阶段1完成 → 阶段2: 交叉验证", "regression_cv", "cv_regression_done")
_pns_phase_cv_regression_done = _make_simple_phase_handler(
    "cv_regression_done", run_cv_step,
    "阶段2a完成 → 阶段2b: 主交叉验证", "cv", "cv_main_done")
FANOUT_ADVANCE_STATUSES = (_STEP_DONE_STATUS, "skipped", "degraded")
def load_round_fanout_findings(skill_dir: str) -> list[dict]:
    try:
        return load_fanout_findings(
            skill_dir, round_start_ts=current_round_anchor(skill_dir))
    except Exception as exc:  # noqa: BLE001
        logger.warning("[FanoutStep] 扩族输入装载失败(降级为空): %s", exc)
        return []
def _run_fanout_body(sd: str, stage_start: float) -> dict:
    try:
        _source_report, _source_path, _round_ts = (
            resolve_fanout_diagnosis_inputs(sd))
        result = run_fanout_diagnosis(
            sd, _source_report,
            round_start_ts=_round_ts,
            source_report_path=_source_path)
    except Exception as exc:  # noqa: BLE001
        logger.warning("[FanoutStep] 扇出诊断异常(降级): %s", exc)
        result = {"status": "degraded", "error": str(exc)[:500]}
    out = dict(result) if isinstance(result, dict) else {}
    if not str_or(out.get("status")).strip():
        logger.warning(
            "[FanoutStep] 扇出诊断结果非法(降级): type=%s, status=%r",
            type(result).__name__, out.get("status"))
        out["status"] = "degraded"
        out["error"] = (f"扇出诊断结果非法: 期望含非空 status 的 dict，"
                        f"实际 {type(result).__name__}")
    out["elapsed_s"] = elapsed_seconds(stage_start)
    out["findings_count"] = int_or(
        dict_or_empty(out.get("summary")).get("occurrences"), 0)
    _html = emit_fanout_report(sd, out, renderer=generate_html_report)
    out["html_path"] = str_or(_html.get("path"))
    out["html_status"] = str_or(_html.get("status"))
    if out.get("status") in FANOUT_ADVANCE_STATUSES:
        try:
            advance_pipeline_phase(sd, "fanout_done", {
                "fanout_summary": dict_or_empty(out.get("summary")),
                "fanout_html_path": out["html_path"],
            })
        except Exception as _adv_err:  # noqa: BLE001
            logger.warning("[FanoutStep] 相位推进写盘失败: %s", _adv_err)
            out["status"] = "error"
            out["error"] = f"phase_advance_failed: {_adv_err}"[:500]
    return out
def run_fanout_diagnosis_step(skill_dir: str) -> dict:
    return run_step_shell(
        skill_dir, guard_name="fanout", label="FanoutStep",
        body=lambda run: _run_fanout_body(run.skill_dir, run.started_at),
        emit=lambda sd, out: emit_step_html("fanout", sd, out),
        module_name=_MODULE_NAME, entry="run_fanout_diagnosis_step",
    )
def _pns_phase_cv_main_done(sd: str) -> dict:
    task_result = _invoke_step(run_fanout_diagnosis_step, sd,
                               step_name="fanout")
    next_phase = ("fanout_done"
                  if task_result.get("status") in FANOUT_ADVANCE_STATUSES
                  else "cv_main_done")
    return step_result(
        "cv_main_done", "阶段2b完成 → 阶段G: 扇出诊断与治疗", "fanout",
        task_result, next_phase, progress_of(sd))
def _run_stage3a_dry_route(ctx: PipelineContext, cv_report: dict) -> dict:
    stage_start = time.time()
    ts = timestamp_ms()
    logger.info("[Stage3a] 修复路由 dry_run 开始: %s", timestamp_human())
    result = {
        "stage": "dry_route",
        "timestamp": ts,
        "status": "running",
    }
    try:
        fix_report = build_dry_route_report(cv_report)
        _round_ts = current_round_anchor(ctx.skill_dir)
        if isinstance(fix_report, dict) and _round_ts:
            fix_report = dict(fix_report, round_start_ts=_round_ts)
        mem_bus_put("fix_route", fix_report, ctx.skill_dir)
        result["total_confirmed"] = dict_or_empty(
            fix_report.get("summary")).get("total_confirmed", 0)
        result["fix_coverage"] = fix_report.get("fix_coverage", {})
        result["status"] = "completed"
        result["elapsed_s"] = elapsed_seconds(stage_start)
        logger.info("[Stage3a] 修复路由 dry_run 完成: %d confirmed, %.1fs",
                    result["total_confirmed"], result["elapsed_s"])
    except Exception as e:
        result["status"] = "failed"
        result["error"] = str(e)[:500]
        result["elapsed_s"] = elapsed_seconds(stage_start)
        logger.exception("[Stage3a] 修复路由 dry_run 失败")
    ctx.stages["stage3a"] = result
    return result
def _resolve_fix_report(ctx: PipelineContext, cv_report: dict) -> dict:
    fix_report = mem_bus_take("fix_route", ctx.skill_dir)
    _current_round = current_round_anchor(ctx.skill_dir)
    _report_round = (normalize_round_start_ts(str(
        fix_report.get("round_start_ts") or ""))
        if isinstance(fix_report, dict) else "")
    _stale = bool(isinstance(fix_report, dict)
                  and (not _current_round or _report_round != _current_round))
    if not isinstance(fix_report, dict) or _stale:
        if not isinstance(fix_report, dict):
            if fix_report is not None:
                logger.warning("[Stage3b] mem_bus fix_route 载荷非 dict（%s），重算兜底",
                               type(fix_report).__name__)
        else:
            logger.info("[Stage3b] 路由报告非本轮(round=%s != %s)，按当前CV重算",
                        _report_round or "(无锚)", _current_round)
        fix_report = build_dry_route_report(cv_report)
        if not isinstance(fix_report, dict):
            fix_report = {}
    else:
        _fr_summary = fix_report.get("summary")
        logger.info("[Stage3b] 路由报告内存直传命中: %d confirmed",
                    (_fr_summary.get("total_confirmed", 0)
                     if isinstance(_fr_summary, dict) else 0))
    return fix_report
def _self_audit_applied(cv_report: object) -> bool:
    return signal_bool(dict_or_empty(cv_report).get(
        "self_audit_applied", False))
def _log_self_audit_assertion(cv_report: dict) -> None:
    _saa_applied = _self_audit_applied(cv_report)
    _fi_raw = dict_or_empty(cv_report).get("findings_index", [])
    _findings_count = len(_fi_raw) if isinstance(_fi_raw, list) else 0
    if _saa_applied:
        logger.info("[Stage3b] 自审感知层断言通过: self_audit_applied=True, "
                    "%d findings已过滤", _findings_count)
    else:
        logger.warning("[Stage3b] 自审感知层断言未通过: self_audit_applied=False, "
                       "CV报告可能未执行策略12自审感知过滤, 治疗计划将启动安全网过滤")
def _run_stage3b_generate_plan(ctx: PipelineContext, cv_report: dict,
                               extra_findings: list[dict] | None) -> dict:
    stage_start = time.time()
    ts = timestamp_ms()
    logger.info("[Stage3b] 治疗方案生成开始: %s", timestamp_human())
    result = {
        "stage": "treatment_plan",
        "timestamp": ts,
        "status": "running",
    }
    try:
        fix_report = _resolve_fix_report(ctx, cv_report)
        _log_self_audit_assertion(cv_report)
        plan = generate_treatment_plan(
            diagnosis_report=cv_report,
            fix_route_report=fix_report if fix_report else None,
            skill_dir=ctx.skill_dir,
            extra_findings=list(extra_findings or []),
        )
        plan_dict = enhance_plan_with_memory(ctx, plan)
        apply_safety_overrides(
            plan_dict, getattr(ctx, "adjustments", {}) or {})
        attach_fix_coverage(plan_dict, fix_report)
        result["plan"] = plan_dict
        project_plan_stage_result(result, plan_dict)
        result["status"] = "completed"
        result["elapsed_s"] = elapsed_seconds(stage_start)
        result["plan_path"] = save_treatment_plan(
            plan_dict, ctx.json_artifact_dir)
        log_plan_generated(result)
    except Exception as e:
        result["status"] = "failed"
        result["error"] = str(e)[:500]
        result["traceback"] = traceback.format_exc()[:1000]
        logger.exception("[Stage3b] 治疗方案生成失败")
    ctx.stages["stage3b"] = result
    return result
def _advance_dry_route_done(sd: str, result: dict) -> None:
    if result.get("status") != _STEP_DONE_STATUS:
        return
    advance_pipeline_phase(sd, "plan_dry_done", {
        "dry_route_confirmed": result.get("total_confirmed", 0),
    })
def _advance_plan_generated(sd: str, out: dict) -> None:
    advance_pipeline_phase(sd, "plan_generated", {
        "plan_total_items": out["total_items"],
        "plan_auto_safe": out["auto_safe_count"],
        "plan_path": out.get("plan_path", ""),
    })
    cleanup_legacy_fix_route_report(sd)
def _cv_unavailable_out(stage_start: float, has_candidates: bool,
                        rerun_hint: str) -> dict:
    if has_candidates:
        error = ("CV报告不可解析（最新候选撕裂/脏形态且无更旧可用），请重跑 "
                 + rerun_hint)
    else:
        error = "CV报告不存在，请先执行 " + rerun_hint
    return {"status": "failed", "error": error,
            "elapsed_s": elapsed_seconds(stage_start)}
def _compose_dry_route_out(result: dict, stage_start: float) -> dict:
    out = {
        "status": result.get("status", "completed"),
        "total_confirmed": result.get("total_confirmed", 0),
        "elapsed_s": elapsed_seconds(stage_start),
    }
    fix_coverage = result.get("fix_coverage")
    if isinstance(fix_coverage, dict) and fix_coverage:
        out["fix_coverage"] = fix_coverage
    carry_failure_detail(out, result)
    return out
@timed_log("stage_dry_route")
def run_dry_route_step(skill_dir: str) -> dict:
    def _body(run) -> dict:
        sd = run.skill_dir
        ctx = build_pipeline_context(sd)
        cv_report, _cv_path, has_candidates = load_stage_cv_report(sd)
        if not _cv_path:
            return _cv_unavailable_out(
                run.started_at, has_candidates, "run_cv_step(skill_dir)")
        result = _run_stage3a_dry_route(ctx, cv_report)
        _advance_dry_route_done(sd, result)
        out = _compose_dry_route_out(result, run.started_at)
        logger.info("[DryRouteStep] 完成: %d confirmed, %.1fs",
                    out["total_confirmed"], out["elapsed_s"])
        return out
    return run_step_shell(
        skill_dir, guard_name="dry_route", label="DryRouteStep", body=_body,
        emit=lambda sd, out: emit_step_html("dry_route", sd, out))
def _build_plan_step_out(plan_result: dict, plan_dict: dict,
                         cv_report: dict, stage_start: float) -> dict:
    extras = plan_step_extras(plan_result, plan_dict)
    _saa_applied = _self_audit_applied(cv_report)
    if not _saa_applied:
        logger.warning("[TreatmentPlanStep] CV报告未标记self_audit_applied, "
                       "治疗计划已启动安全网过滤")
    out = {
        "status": plan_result.get("status", "failed"),
        "total_items": plan_result.get("total_items", 0),
        "auto_safe_count": extras.pop("auto_safe_count", 0),
        "manual_confirm_count": extras.pop("manual_confirm_count", 0),
        "plan_path": plan_result.get("plan_path", ""),
        "self_audit_applied": _saa_applied,
        "elapsed_s": elapsed_seconds(stage_start),
    }
    out.update(extras)
    carry_failure_detail(out, plan_result)
    return out
@timed_log("stage_treatment")
def execute_treatment_item(sd: str, error_runner) -> dict:
    result = error_runner(
        lambda: execute_treatment_item_core(sd),
        {"index": -1}, None, "治疗异常哨兵")
    emit_treatment_item_report(sd, result)
    return result
@timed_log("stage_treatment_plan")
def run_treatment_plan_step(skill_dir: str,
                            output_html: str | None = None,
                            *,
                            extra_findings: list[dict] | None = None) -> dict:
    def _body(run) -> dict:
        sd = run.skill_dir
        ctx = build_pipeline_context(sd)
        cv_report, cv_path, has_candidates = load_stage_cv_report(
            sd, plan_mode=True)
        if not cv_path:
            return _cv_unavailable_out(
                run.started_at, has_candidates, "run_cv_step()")
        plan_result = _run_stage3b_generate_plan(
            ctx, cv_report, extra_findings)
        plan_dict = plan_dict_or_empty(plan_result.get("plan"), "plan 键")
        reset_artifacts_after_plan(sd, plan_result, plan_dict)
        out = _build_plan_step_out(
            plan_result, plan_dict, cv_report, run.started_at)
        emit_dependency_report_html(cv_report, sd, output_html)
        if out.get("status") == _STEP_DONE_STATUS:
            _advance_plan_generated(sd, out)
        logger.info("[TreatmentPlanStep] 完成: %d 项, %.1fs",
                    out["total_items"], out["elapsed_s"])
        return out
    return run_step_shell(
        skill_dir, guard_name="treatment_plan", label="TreatmentPlanStep",
        body=_body,
        emit=lambda sd, out: emit_step_html("treatment_plan", sd, out))
def _run_treatment_plan_step_with_fanout(sd: str) -> dict:
    return run_treatment_plan_step(
        sd, extra_findings=load_round_fanout_findings(sd))
def run_fupan_step(skill_dir: str) -> dict:
    def _body(run):
        sd = run.skill_dir
        logger.info("[FupanStep] 阶段6a: fupan_engine 开始: %s", timestamp_human())
        ctx = build_pipeline_context(sd)
        review, _cv_report, exec_result = load_stage6_inputs(sd)
        if review is None:
            return _review_missing_out(run)
        out = run_stage6a_fupan(ctx, review, exec_result)
        if _advance_feedback_phase(
                sd, out, phase="fupan_done", label="FupanStep", step="fupan",
                payload={
                    "fupan_quality_score": out.get("fupan_quality_score"),
                    "fupan_memory_ops": len_safe(out.get("memory_operations")),
                    "fupan_risks": len_safe(out.get("fupan_detected_risks")),
                }):
            logger.info("[FupanStep] 完成: score=%s, memory_ops=%d, risks=%d, %.1fs",
                         out.get("fupan_quality_score"),
                         len_safe(out.get("memory_operations")),
                         len_safe(out.get("fupan_detected_risks")),
                         safe_float(out.get("elapsed_s")))
        return out
    return run_step_shell(skill_dir, guard_name="fupan", label="FupanStep",
                           body=_body, emit=_emit_fupan_step_html)
def run_phase_handler(phase: str, skill_dir: str) -> dict | None:
    if not isinstance(phase, str):
        return None
    handler = _PNS_PHASE_HANDLERS.get(phase)
    if handler is None:
        return None
    try:
        result = handler(skill_dir)
    except Exception as exc:
        logger.warning("[PhaseHandler] 相位 %s 处理异常，停留待重试: %s",
                       phase, exc, exc_info=True)
        return stay_result(
            skill_dir, phase, f"相位 {phase} 处理异常，停留待重试",
            "phase_handler", str(exc)[:500])
    if not isinstance(result, dict):
        error = f"phase handler returned non-dict {type(result).__name__}"
        logger.warning("[PhaseHandler] 相位 %s 返回类型非法，停留待重试: %s",
                       phase, error)
        return stay_result(
            skill_dir, phase, f"相位 {phase} 返回类型非法，停留待重试",
            "phase_handler", error)
    return result
_PNS_SHELL_STEPS = (
    ("regression_cv", "cv_regression_done", run_regression_cv_step),
    ("cv", "cv_main_done", run_cv_step),
    ("fanout", "fanout_done", run_fanout_diagnosis_step),
    ("dry_route", "plan_dry_done", run_dry_route_step),
    ("treatment_plan", "plan_generated",
     _run_treatment_plan_step_with_fanout),
)
def iter_shell_steps(phase: str):
    if not isinstance(phase, str) or phase not in _PNS_PHASE_REACHED:
        logger.warning("[PipelineBatch] 未知阶段 %r，跳过阶段2~3b 步骤"
                       "（交由自愈回退）", phase)
        return
    for _label, _done_phase, _step in _PNS_SHELL_STEPS:
        if not phase_reached(phase, _done_phase):
            yield _label, _step
def _extract_confirmed_findings(cv_report: object) -> list[dict]:
    if not isinstance(cv_report, dict):
        return []
    direct = cv_report.get("confirmed_findings")
    if isinstance(direct, list):
        return dict_items(direct)
    index = cv_report.get("findings_index")
    if not isinstance(index, list):
        return []
    confirmed: list[dict] = []
    for entry in index:
        if not isinstance(entry, dict):
            continue
        if str_or(entry.get("conclusion")).strip().lower() != "confirmed":
            continue
        findings = entry.get("findings")
        if isinstance(findings, list):
            confirmed.extend(dict_items(findings))
    return confirmed
def _safe_num(val) -> int:
    return max(0, int_or(val))
def _status_counts(details: list) -> Counter:
    counts: Counter = Counter()
    for d in dict_items(details):
        _status = d.get("status")
        # 历史记录里的 fail 是「诊断结论未通过（P0）」，方法已执行完成，
        # 不计入执行失败；与降级报告/阶段1计数保持同一口径。
        if isinstance(_status, str) and _status.strip().lower() == "fail":
            _status = "warn"
        bucket = method_status_bucket(_status)
        if bucket is None:
            logger.warning(
                "[ReviewStep] 诊断方法状态无法归类，按失败计入复盘: %r",
                d.get("status"))
            bucket = "failed"
        counts[bucket] += 1
    return counts
def _build_diag_result(diag_progress: dict, details: list) -> dict:
    _progress = dict_or_empty(diag_progress)
    _details = dict_items(details)
    status_counts = _status_counts(_details)
    return {
        "status": "completed",
        "methods_executed": _safe_num(_progress.get("completed", 0)),
        "methods_passed": status_counts["completed"],
        "methods_failed": status_counts["failed"],
        "methods_skipped": status_counts["skipped"],
        "total_findings": sum(_safe_num(d.get("findings_count", 0))
                              for d in _details),
        "total_methods": _safe_num(_progress.get("total", 0)),
    }
def run_review_body(skill_dir: str, output_html: str | None,
                    stage_start: float) -> dict:
    ctx = build_pipeline_context(skill_dir)
    diag_progress = query_methods_progress(skill_dir)
    _details_raw = (diag_progress.get("details")
                    if isinstance(diag_progress, dict) else None)
    if not isinstance(_details_raw, (list, tuple)):
        logger.warning("[ReviewStep] 诊断进度视图不可读(%s)，跳过复盘待重试",
                       type(diag_progress).__name__
                       if not isinstance(diag_progress, dict)
                       else f"details={type(_details_raw).__name__}")
        return {"status": "skipped", "reason": "诊断进度不可读",
                "elapsed_s": elapsed_seconds(stage_start)}
    if diag_progress.get("next_method") is not None:
        return {"status": "skipped", "reason": "诊断未完成",
                "elapsed_s": elapsed_seconds(stage_start)}
    details = dict_items(_details_raw)
    diag_result = _build_diag_result(diag_progress, details)
    cv_report, _cv_path = load_cv_report_tolerant(skill_dir)
    plan_result = resolve_treatment_plan(skill_dir)
    exec_result = treatment_exec_result(skill_dir)
    cv_result = {"report": cv_report, "report_path": _cv_path if _cv_path else ""}
    review = run_stage5_review(ctx, diag_result, cv_result, plan_result,
                               exec_result)
    out = build_review_out(review, exec_result, stage_start)
    _confirmed = _extract_confirmed_findings(cv_report)
    out.update(build_review_quality_augmentation(skill_dir, details, _confirmed))
    emit_coverage_report_html(skill_dir, output_html)
    persist_review_result(skill_dir, out)
    return out
def run_stage5_review(ctx: PipelineContext, diag_result: dict, cv_result: dict,
                      plan_result: dict, exec_result: dict) -> dict:
    diag_result = dict_or_empty(diag_result)
    cv_result = dict_or_empty(cv_result)
    plan_result = dict_or_empty(plan_result)
    exec_result = dict_or_empty(exec_result)
    stage_start = time.time()
    ts = timestamp_ms()
    logger.info("[Stage5] 复盘阶段开始: %s", timestamp_human())
    _cv_report, _cv_findings_total, _cv_rules_total = extract_stage5_cv_metrics(cv_result)
    result = {
        "stage": "review",
        "timestamp": ts,
        "round_start_ts": current_round_anchor(ctx.skill_dir),
        "status": "running",
        "engine_used": "none",
    }
    try:
        engine_result = run_stage5_review_engine(
            skill_dir=ctx.skill_dir,
            round_start_ts=result["round_start_ts"],
            memory_context=getattr(ctx, 'memory_context', None),
            cv_report=_cv_report, cv_result=cv_result,
            plan_result=plan_result,
            exec_result=exec_result, result=result, stage_start=stage_start)
        if not isinstance(engine_result, dict):
            raise TypeError(
                "复盘引擎返回非 dict: "
                f"{type(engine_result).__name__}")
        result = engine_result
        if result.get("status") == _STEP_DONE_STATUS:
            result["_review_context_for_fupan"] = build_stage5_fupan_context(
                diag_result, exec_result, _cv_findings_total,
                _cv_rules_total, result.get("overall_score", 0))
        ctx.stages["stage5"] = result
        return result
    except Exception as e:
        result["status"] = "failed"
        result["error"] = str(e)[:500]
        result["traceback"] = traceback.format_exc()[:1000]
        logger.exception("[Stage5] 六环复盘引擎失败")
        result["_review_context_for_fupan"] = build_stage5_fupan_context(
            diag_result, exec_result, _cv_findings_total,
            _cv_rules_total, 0)
    ctx.stages["stage5"] = result
    return result
def _carry_review_memory_ops(out: dict, review: dict) -> None:
    ops = review.get("_memory_operations")
    if isinstance(ops, list) and ops:
        out["_memory_operations"] = ops
def build_review_out(review: dict, exec_result: dict,
                      stage_start: float) -> dict:
    review = dict_or_empty(review)
    exec_result = dict_or_empty(exec_result)
    out = {
        "status": str_or(review.get("status")) or "unknown",
        "timestamp": review.get("timestamp"),
        "round_start_ts": str_or(review.get("round_start_ts")),
        "overall_score": review.get("overall_score"),
        "overall_grade": review.get("overall_grade"),
        "risk_level": review.get("risk_level"),
        "scores": dict_or_empty(review.get("scores")),
        "enhancement_actions": as_list(review.get("enhancement_actions")),
        "issues_found": as_list(review.get("issues_found")),
        "good_practices": as_list(review.get("good_practices")),
        "summary": str_or(review.get("summary")),
        "diagnosis_audit": as_list(review.get("diagnosis_audit")),
        "treatment_summary": _treatment_summary(exec_result),
        "_review_context_for_fupan": review.get("_review_context_for_fupan", {}),
        "elapsed_s": elapsed_seconds(stage_start),
    }
    for _key in ("error", "traceback", "reason"):
        _val = str_or(review.get(_key))
        if _val:
            out[_key] = _val
    _carry_review_memory_ops(out, review)
    return out
def _treatment_summary(exec_result: dict) -> dict:
    keys = ("total_items", "executed", "succeeded", "failed",
            "rolled_back", "skipped", "fp_confirmed", "pending_confirm",
            "suggestion", "no_fixer", "ai_fixed")
    return {key: exec_result.get(key, 0) for key in keys}
def run_review_step(skill_dir: str, output_html: str | None = None) -> dict:
    def _body(run):
        return run_review_body(run.skill_dir, output_html, run.started_at)
    return run_step_shell(
        skill_dir, guard_name="review", label="ReviewStep", body=_body,
        emit=lambda sd, out: emit_step_html("review", sd, out))
@timed_log("stage_treatment")
def run_treatment_step(skill_dir: str, item_index: int | None = None) -> dict:
    def _body(run) -> dict:
        return execute_treatment_item_core(
            run.skill_dir, item_index=item_index,
            stage_start=run.started_at)
    return run_step_shell(
        skill_dir, guard_name="treatment", label="TreatmentStep", body=_body,
        emit=emit_treatment_item_report)
def _fix_step_payload(out: dict) -> dict:
    return {
        "candidates": out.get("total_candidates", 0),
        "applied": out.get("applied", 0),
        "rejected": out.get("rejected", 0),
        "failed": out.get("failed", 0),
    }
def run_ai_manual_fix_step(
    skill_dir: str, llm_call_fn: Callable | None = None,
    dry_run: bool = _stage4.DEFAULT_AI_FIX_DRY_RUN,
) -> dict:
    def _body(run) -> dict:
        sd = run.skill_dir
        backend = _stage4.run_fix_backend(sd, llm_call_fn, dry_run)
        out = _stage4.build_fix_step_out(backend, run.elapsed_s)
        phase_payload = _stage4.evaluate_zero_leftover(
            sd, out, allow_phase_advance=backend.executed)
        if phase_payload is not None:
            advance_pipeline_phase(sd, "ai_fix_done", phase_payload)
        return out
    return run_step_shell(
        skill_dir, guard_name="ai_manual_fix", label="AIFixStep", body=_body,
        emit=lambda sd, out: emit_step_html("ai_fix", sd, out),
        module_name=_MODULE_NAME, entry="run_ai_manual_fix_step",
        payload_fn=_fix_step_payload)
def _review_missing_out(run: Any) -> dict:
    return {"status": "failed",
            "error": ("复盘结果文件缺失或复盘未完成(status!=completed)，"
                      "请先执行 run_review_step(skill_dir) 重新复盘"),
            "elapsed_s": run.elapsed_s}
def _advance_feedback_phase(sd: str, out: dict, *, phase: str, payload: dict,
                           label: str, step: str) -> bool:
    if str(out.get("status", "")) == _STEP_DONE_STATUS:
        advance_pipeline_phase(sd, phase, payload)
        return True
    logger.warning("[%s] %s 未完成(status=%s)，phase 停留待重试",
                   label, step, out.get("status"))
    return False
def _emit_fupan_step_html(sd: str, out: dict) -> None:
    if str_or(out.get("status")) == _STEP_DONE_STATUS:
        logger.debug("[FupanStep] 复盘已完成，复用 fupan_engine 已发射的阶段报告")
        return
    try:
        rich = generate_html_report(out, sd, "fupan")
    except Exception as _fhe:  # noqa: BLE001
        logger.warning("[FupanStep] fupan 富报告 HTML 生成失败(不阻断): %s", _fhe)
        return
    rich_path = html_report_path(rich)
    if rich_path:
        logger.info("[FupanStep] fupan 富报告 HTML 已生成: %s", rich_path)
    else:
        logger.warning("[FupanStep] fupan 富报告 HTML 未落盘(不阻断)，"
                       "阶段聚合未返回路径")
def _stage6d_fanout_signal(skill_dir: str) -> dict:
    try:
        return fanout_evolution_signal(
            skill_dir, round_start_ts=current_round_anchor(skill_dir))
    except Exception as _err:  # noqa: BLE001
        logger.warning("[Stage6d] 扇出反哺信号读取失败(跳过): %s", _err)
        return {}
def run_stage6b_feedback_loop(ctx: Any, exec_result: dict,
                              cv_report: dict) -> dict:
    logger.info("[Stage6b] feedback_loop 开始: %s", timestamp_human())
    result = run_feedback_loop_stage(
        ctx.skill_dir, exec_result, cv_report,
        feedback_runner=run_feedback_loop,
        memory_context=getattr(ctx, "memory_context", None))
    ctx.batch_fp_result = result.get("batch_fp_marking")
    ctx.stages["stage6b"] = result
    return result
def run_feedback_loop_step(skill_dir: str) -> dict:
    def _body(run):
        sd = run.skill_dir
        logger.info("[FeedbackLoopStep] 阶段6b: feedback_loop 开始: %s", timestamp_human())
        ctx = build_pipeline_context(sd)
        _review, cv_report, exec_result = load_stage6_inputs(
            sd, with_fix_coverage=True)
        out = run_stage6b_feedback_loop(ctx, exec_result, cv_report)
        if _advance_feedback_phase(
                sd, out, phase="feedback_done",
                label="FeedbackLoopStep", step="feedback_loop",
                payload={
                    "feedback_diag_count": len_safe(
                        out.get("diagnosis_feedbacks")),
                    "feedback_cv_count": len_safe(out.get("cv_feedbacks")),
                    "feedback_fixer_count": len_safe(
                        out.get("fixer_feedbacks")),
                }):
            logger.info("[FeedbackLoopStep] 完成: diag_fb=%d, cv_fb=%d, fixer_fb=%d, %.1fs",
                         len_safe(out.get("diagnosis_feedbacks")),
                         len_safe(out.get("cv_feedbacks")),
                         len_safe(out.get("fixer_feedbacks")),
                         safe_float(out.get("elapsed_s")))
        return out
    def _emit(sd, out):
        emit_step_html("feedback_loop", sd, out)
        if str(out.get("status", "")) != _STEP_DONE_STATUS:
            logger.warning(
                "[FeedbackLoopStep] 未完成结果不入阶段6b证据通道"
                "(status=%s)，phase 停留待重试", out.get("status"))
            return
        publish_step_result("stage6b_feedback_loop", "feedback_loop", sd, out)
    return run_step_shell(skill_dir, guard_name="feedback_loop",
                           label="FeedbackLoopStep", body=_body, emit=_emit)
def run_stage6c_code_feedback(ctx: PipelineContext, review_result: dict | None,
                              cv_report: dict) -> dict:
    stage_start = time.time()
    logger.info("[Stage6c] code_feedback 开始: %s", timestamp_human())
    result = {"stage": "code_feedback", "timestamp": timestamp_ms(),
              "status": "running"}
    result["batch_fp_marking"] = dict_or_empty(
        getattr(ctx, "batch_fp_result", None))
    run_fp_evolution_step(ctx.skill_dir, result)
    run_fp_fixation_step(ctx.skill_dir, result)
    run_defense_feedback_step(ctx.skill_dir, cv_report, result)
    persist_review_enhancements_step(ctx, review_result, result)
    apply_code_level_feedback_step(ctx.skill_dir, result)
    _clfb = stage_code_feedback(result)
    _feedback_status = str_or(_clfb.get("status")).strip().lower()
    _degraded = result.get("degraded_steps")
    _degraded = _degraded if isinstance(_degraded, list) else []
    if _feedback_status == "ok" and not _degraded:
        result["status"] = "completed"
    else:
        result["status"] = "failed"
        if _degraded:
            _degraded_sample = "；".join(
                f"{item.get('step')}({str_or(item.get('error'))[:80]})"
                for item in _degraded[:5] if isinstance(item, dict))
            result["error"] = (
                f"{len(_degraded)} 个反哺步骤降级，进化未真正落地："
                f"{_degraded_sample}")
        else:
            result["error"] = (str_or(
                _clfb.get("error") or _clfb.get("message"))
                or f"代码级反哺未完成(status={_feedback_status or 'missing'})")
        result["next_action"] = "retry_code_feedback"
    result["elapsed_s"] = elapsed_seconds(stage_start)
    ctx.stages["stage6c"] = result
    logger.info("[Stage6c] code_feedback结束: phase_status=%s, status=%s, "
                "处理%d项, 方案%d个, %.1fs"
                "（L1-L4 应用统计产生于 apply_approved_fix 之后,见代码反哺审计链）",
                result["status"], _clfb.get("status", "unknown"),
                _clfb.get("total_processed", 0),
                len(_clfb.get("plans") or []),
                result["elapsed_s"])
    return result
def run_code_feedback_step(skill_dir: str) -> dict:
    def _body(run):
        sd = run.skill_dir
        logger.info("[CodeFeedbackStep] 阶段6c: code_feedback 开始: %s", timestamp_human())
        ctx = build_pipeline_context(sd)
        review, cv_report, _exec_result = load_stage6_inputs(sd)
        if review is None:
            return _review_missing_out(run)
        if getattr(ctx, "batch_fp_result", None) is None:
            ctx.batch_fp_result = zero_batch_fp_result()
        out = run_stage6c_code_feedback(ctx, review, cv_report)
        _payload = code_feedback_phase_payload(out)
        if _advance_feedback_phase(
                sd, out, phase="code_feedback_done",
                label="CodeFeedbackStep", step="code_feedback",
                payload=_payload):
            logger.info("[CodeFeedbackStep] 完成: l1=%d, l2=%d, l3=%d, %.1fs",
                         _payload["code_feedback_l1"],
                         _payload["code_feedback_l2"],
                         _payload["code_feedback_l3"],
                         safe_float(out.get("elapsed_s")))
        return out
    return run_step_shell(
        skill_dir, guard_name="code_feedback", label="CodeFeedbackStep",
        body=_body,
        emit=lambda sd, out: emit_step_html("code_feedback", sd, out))
_pns_phase_fanout_done = _make_simple_phase_handler(
    "fanout_done", run_dry_route_step,
    "阶段G完成 → 阶段3a: 修复路由 dry_run", "dry_route", "plan_dry_done")
_pns_phase_plan_dry_done = _make_simple_phase_handler(
    "plan_dry_done", _run_treatment_plan_step_with_fanout,
    "阶段3a完成 → 阶段3b: 治疗方案生成", "treatment_plan", "plan_generated")
_pns_phase_review_done = _make_simple_phase_handler(
    "review_done", run_fupan_step,
    "阶段5完成 → 阶段6a: fupan_engine", "fupan", "fupan_done")
_pns_phase_fupan_done = _make_simple_phase_handler(
    "fupan_done", run_feedback_loop_step,
    "阶段6a完成 → 阶段6b: feedback_loop", "feedback_loop", "feedback_done")
_pns_phase_feedback_done = _make_simple_phase_handler(
    "feedback_done", run_code_feedback_step,
    "阶段6b完成 → 阶段6c: code_feedback", "code_feedback", "code_feedback_done")
_PNS_PHASE_HANDLERS = {
    "diagnosis_done": _pns_phase_diagnosis_done,
    "cv_regression_done": _pns_phase_cv_regression_done,
    "cv_main_done": _pns_phase_cv_main_done,
    "fanout_done": _pns_phase_fanout_done,
    "plan_dry_done": _pns_phase_plan_dry_done,
    "plan_generated": _pns_phase_plan_generated,
    "treatment_done": _pns_phase_treatment_done,
    "ai_fix_pending": _pns_phase_ai_fix_pending,
    "ai_fix_done": _pns_phase_ai_fix_done,
    "review_done": _pns_phase_review_done,
    "fupan_done": _pns_phase_fupan_done,
    "feedback_done": _pns_phase_feedback_done,
    "code_feedback_done": _pns_phase_code_feedback_done,
    "evolution_pending": _pns_phase_evolution_pending,
    "all_completed": _pns_phase_all_completed,
}
def _run_fn_probe_baseline(skill_dir: str, out: dict) -> None:
    """每轮落一次漏报探针基线，供 GATE-FALSE-NEGATIVE 与精度趋势判定。

    探针是「正向构造缺陷」的唯一度量手段：反哺链的学习信号全部来自已产出
    finding 的裁决，漏报（真实缺陷根本没有 finding）无法进入该回路，必须靠
    注入模板独立度量。异常不阻断本轮，但要留可见标记——探针静默失效会让
    门禁永远停在 skipped，等于没有召回保障。
    """
    try:
        from jwsgj.diag_testing_mutation import (
            run_cached_false_negative_probe,
        )

        result = run_cached_false_negative_probe(skill_dir)
        metrics = dict_or_empty(getattr(result, "metrics", None))
        out["fn_probe"] = {
            "status": str_or(getattr(result, "status", "")),
            "score": safe_float(getattr(result, "score", 0.0)),
            "fn_rate": safe_float(metrics.get("fn_rate")),
            "templates": int_or(metrics.get("templates"), 0),
            "killed": int_or(metrics.get("killed"), 0),
            "survived": int_or(metrics.get("survived"), 0),
            "persisted": int_or(metrics.get("persisted"), 0),
        }
    except Exception as exc:
        logger.warning(
            "[AutoEnhanceStep] 漏报探针执行异常（本轮按无样本跳过门禁）: %s",
            exc, exc_info=True)
        out["fn_probe"] = {"status": "error", "error": str(exc)[:300]}


def run_auto_enhance_step(skill_dir: str) -> dict:
    def _body(run):
        sd = run.skill_dir
        logger.info("[AutoEnhanceStep] 阶段6d: auto_enhance 开始: %s", timestamp_human())
        ctx = build_pipeline_context(sd)
        review, cv_report, _exec_result = load_stage6_inputs(sd)
        if review is None:
            return _review_missing_out(run)
        if getattr(ctx, "stages", None) is not None:
            load_stages_from_files(ctx)
        out = run_stage6d_auto_enhance(
            ctx, review, cv_report,
            method_adjustments=load_method_adjustments_tolerant(sd),
            fanout_signal=_stage6d_fanout_signal(sd))
        _run_fn_probe_baseline(sd, out)
        _completed = str(out.get("status", "")) == _STEP_DONE_STATUS
        if not _completed:
            logger.warning("[AutoEnhanceStep] 收尾未完成(status=%s)，phase 停留待重试"
                           "（不做后置治理清理，保留重试所需备份与一次性产物）",
                           out.get("status"))
        elif complete_stage6d_governance(
                sd, out, list_pending=list_pending_ai_reviews):
            finalize_completed_pipeline(sd, out)
            run_post_completion_governance(
                sd, out, protect_ts=round_start_epoch(sd) - 60.0)
        return out
    return run_step_shell(
        skill_dir, guard_name="auto_enhance", label="AutoEnhanceStep",
        body=_body,
        emit=lambda sd, out: emit_step_html("auto_enhance", sd, out))
def _read_stage6d_pending_reviews(
    skill_dir: str, list_pending,
) -> tuple[dict, int, str]:
    if list_pending is None:
        return {}, 0, "阶段6d 待审核清单读取器未注入"
    try:
        aggregate = list_pending(skill_dir)
    except Exception as exc:
        logger.warning("[AutoEnhanceStep] 待审核清单读取失败，停留待重试: %s",
                       exc, exc_info=True)
        return {}, 0, f"阶段6d 待审核清单读取失败: {str(exc)[:400]}"
    return _validate_pending_reviews(aggregate)
def _route_evolution_pending_reviews(skill_dir: str, out: dict,
                                    list_pending) -> bool:
    aggregate, pending, read_err = _read_stage6d_pending_reviews(
        skill_dir, list_pending)
    if read_err:
        out["status"] = "failed"
        out["error"] = str(read_err)[:400]
        out["next_action"] = "run_next_pipeline_step"
        return True
    if pending == 0:
        return False
    _ok, _adv_err = advance_phase_safe(
        skill_dir, "evolution_pending", {"pending_ai_review": pending})
    if not _ok:
        out["status"] = "failed"
        out["error"] = f"阶段6d 待审核改道写盘失败: {_adv_err}"[:400]
        out["next_action"] = "run_next_pipeline_step"
        return True
    out.update({
        "status": "evolution_pending",
        "pending_ai_review": pending,
        "pending_reviews": as_list(aggregate.get("reviews")),
        "next_action": "run_next_ai_review",
    })
    logger.info("[AutoEnhanceStep] 阶段6d 新增/剩余 %d 条待审核项，改道6e",
                pending)
    return True
def complete_stage6d_governance(skill_dir: str, out: dict, *,
                                list_pending) -> bool:
    if not apply_delivery_gates(skill_dir, out):
        return False
    return not _route_evolution_pending_reviews(
        skill_dir, out, list_pending=list_pending)

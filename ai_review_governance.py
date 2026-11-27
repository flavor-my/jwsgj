from __future__ import annotations

import logging
import math
from collections.abc import Callable
from typing import Any, NamedTuple

from jwsgj.ai_review_governance_review import (
    APPROVAL_VERDICTS,
    REVIEW_FRAMEWORK,
    VERDICT_VALUES,
    approval_flag,
    as_text,
    is_missing_dimension,
    record_review_verdict,
    resolve_review_decision,
    validate_review_assessment,
)
from jwsgj.ai_review_item_channels import (
    CHANNEL_REVIEW_INPUT_CONTRACT,
    CHANNELS,
    collect_adjustment_reviews,
    collect_cv_uncertain_reviews,
    collect_enhancement_reviews,
    collect_feedback_reviews,
    collect_security_reviews,
    collect_treatment_reviews,
    describe_review_item_keys,
    normalize_review_item,
)
from jwsgj.ai_review_item_plan import (
    FIELD_SUGGESTED_VALUE,
    MAX_ADJUSTMENT_PLANS,
    apply_enhancement_verdict,
    apply_feedback_verdict,
    cleanup_operation,
    find_pending_entry,
    load_pending_security_plan,
    needs_fixed_source,
    provided_source,
    prune_consumed_items,
    verdict_text,
)
from jwsgj.ai_review_queue import (
    REVIEW_ID_PREFIX,
    review_entry_key,
)
from jwsgj.cleanup_residue import (
    apply_cleanup_verdict,
    apply_security_verdict,
    collect_cleanup_reviews,
)
from jwsgj.diag_guard_state import (
    max_review_seq,
    read_queue_json,
    write_queue_json,
)
from jwsgj.diag_types_normalize import (
    as_dict,
    as_list,
    normalize_confidence,
    normalize_line_no,
    now_iso,
    plan_index,
    safe_float,
    signal_bool,
)
from jwsgj.diag_zero_backlog_gate import (
    fixate_fp_rules as _fixate_fp_rules_impl,
)
from jwsgj.diag_zero_backlog_ledger import (
    build_review_target_digest,
    fixed_source_sha256,
    write_verdict_trace,
)
from jwsgj.fix_guide_rule_identity import (
    make_locator_from_finding,
)
from jwsgj.fp_rules_judge import (
    drop_fp_suppression_rule,
)
from jwsgj.html_render_pipeline import (
    emit_ai_fix_trace,
    emit_html_report,
    emit_step_trace,
)
from jwsgj.log_config import (
    locked_artifact,
    log_swallowed,
)
from jwsgj.runtime_paths import (
    adjustment_plan_path,
    cv_uncertain_path,
    fp_tracker_rules_path,
    read_evolution_state,
    write_evolution_section,
)
from jwsgj.runtime_scope import (
    normalize_skill_dir,
)
from jwsgj.treatment_experience import (
    apply_ai_fix,
    brief_fix_experience,
    record_item_failure,
)
from jwsgj.treatment_state import (
    HumanConfirmationStore,
    apply_item_status,
    canonical_locator_key,
    item_status,
    load_treatment_state,
    locate_treatment_item,
    mark_fix_plan_status,
    save_treatment_state,
    warm_shared_ast_cache,
)

__all__ = [
    'apply_approved_adjustment',
    'apply_cv_uncertain_review',
    'apply_cv_uncertain_verdict',
    'apply_treatment_verdict',
    'build_awaiting_payload',
    'dispatch_channel_apply',
    'fix_experience_history',
    'fixate_fp_rules',
    'has_evidence_value',
    'list_pending_ai_reviews',
    'read_pending_reviews',
    'rule_fp_history',
    'run_all_ai_reviews',
    'run_next_ai_review',
    'writes_source',
]
logger = logging.getLogger(__name__)
logger.info("ai_review_governance 已加载: %d 项导出", len(__all__))
MAX_AI_REVIEW_ITEMS = 200
_COMPLETED_APPLY_STATUSES = frozenset((
    "approved_fixed", "approved_removed", "already_absent", "applied",
    "approved", "ai_fixed", "fp_confirmed", "closed", "deferred",
    "rejected", "invalid_plan_consumed",
))
_CLOSING_VERDICTS = frozenset(("reject", "reject_as_fp", "defer"))
_FILE_PATH_KEYS = ("file_path", "file")
_SHAPE_FS_ASM = ("fs", "asm", "approved")
_SHAPE_FS_APPROVED = ("fs", "approved")
_SHAPE_FS_APPROVED_ASM = ("fs", "approved", "asm")
def _assert_channel_specs_cover_contract() -> None:
    declared = tuple(spec[0] for spec in _CHANNEL_SPECS)
    if len(declared) != len(CHANNELS) or set(declared) != set(CHANNELS):
        raise RuntimeError(
            "通道规格表与 CHANNELS 契约分叉："
            f"specs={sorted(declared)} contract={sorted(CHANNELS)}")
    for name, collector, handler, order in _CHANNEL_SPECS:
        if not callable(collector) or not callable(handler):
            raise TypeError(
                f"通道 {name!r} 的采集器/执行器不可调用："
                f"collector={collector!r} handler={handler!r}")
        if not isinstance(order, tuple) or not order:
            raise RuntimeError(f"通道 {name!r} 的参数顺序声明非法: {order!r}")
        if len(set(order)) != len(order) or not set(order) <= {
                "fs", "asm", "approved"}:
            raise RuntimeError(
                f"通道 {name!r} 的参数顺序含未知/重复键: {order!r}；"
                "合法键=fs/asm/approved")
def _collect_channel_items(skill_dir: str) -> list[dict]:
    sd = normalize_skill_dir(skill_dir)
    items: list[dict] = []
    for _name, collector, _handler, _order in _CHANNEL_SPECS:
        collected = collector(sd)
        if not isinstance(collected, list):
            raise TypeError(
                f"审核通道 {_name!r} 采集器返回非 list: "
                f"{type(collected).__name__}")
        items.extend(collected)
    return items
def dispatch_channel_apply(channel: str, sd: str, target: dict,
                            fs: str, asm: dict | None,
                            approved: bool) -> dict:
    spec = next((item for item in _CHANNEL_SPECS if item[0] == channel), None)
    if spec is None:
        return {"status": "error", "reason": f"未知通道: {channel}"}
    _values = {"fs": fs, "asm": asm,
               "approved": approval_flag(approved)}
    return spec[2](sd, target, *[_values[key] for key in spec[3]])
def _skip_invalid_review_item(it) -> bool:
    if not isinstance(it, dict):
        logger.warning("[AIReview] 跳过非 dict review 条目: %r",
                       type(it).__name__)
        return True
    if not it.get("channel"):
        logger.warning("[AIReview] 跳过缺 channel 键的 review 条目: "
                       "review_id=%r", it.get("review_id"))
        return True
    _rid = it.get("review_id")
    if not isinstance(_rid, str) or not _rid.strip():
        logger.warning("[AIReview] 跳过缺可用 review_id 的 review 条目: "
                       "channel=%r, review_id=%r",
                       it.get("channel"), _rid)
        return True
    if it["channel"] not in CHANNELS:
        logger.warning("[AIReview] 跳过未知通道的 review 条目: "
                       "channel=%r, review_id=%r",
                       it.get("channel"), it.get("review_id"))
        return True
    return False
def list_pending_ai_reviews(skill_dir: str) -> dict:
    sd = normalize_skill_dir(skill_dir)
    reviews: list[dict] = []
    by_channel = dict.fromkeys(CHANNELS, 0)
    for it in _collect_channel_items(sd):
        if _skip_invalid_review_item(it):
            continue
        _inject_review_evidence(it, sd)
        normalize_review_item(it)
        by_channel[it["channel"]] += 1
        reviews.append(it)
    return {
        "pending_ai_review": len(reviews),
        "by_channel": by_channel,
        "reviews": reviews,
        "review_framework": REVIEW_FRAMEWORK,
    }
def read_pending_reviews(skill_dir: str) -> tuple[dict, str]:
    try:
        aggregate = list_pending_ai_reviews(skill_dir)
    except Exception as _le: # noqa: BLE001
        log_swallowed(__name__, _le, context=f'read_pending_reviews:{type(_le).__name__}')
        return {}, str(_le)[:500]
    if not isinstance(aggregate, dict):
        return {}, ("待审核清单返回非 dict: "
                    f"{type(aggregate).__name__}")
    return aggregate, ""
def _read_pending_count(skill_dir: str, *, _collected: int | None = None,
                        _consumed: bool = False) -> tuple[int | None, str]:
    """返回剩余待审条数。

    ``_collected`` 非空时直接由「本轮已采集清单长度」推导，不再重跑一次
    全量采集：`_collect_channel_items` 要为每条 pending 提取代码上下文
    （实测 65 条约 0.255 s），而单条审核原本会触发 2–3 次全量采集。
    消费成功（status=completed，verdict 已落账）即从 pending 消失，故减 1。
    """
    if _collected is not None:
        return (max(0, _collected - 1) if _consumed else _collected), ""
    aggregate, error = read_pending_reviews(skill_dir)
    if error:
        return None, error
    count = aggregate.get("pending_ai_review")
    if not isinstance(count, int) or isinstance(count, bool) or count < 0:
        return None, f"待审核清单计数非法: {count!r}"[:500]
    return count, ""
def _pending_read_error(error: str) -> dict:
    return {
        "status": "error", "error": error,
        "reason": f"待审核清单读取失败: {error}",
        "pending_ai_review": None, "remaining": None,
        "next_action": _next_action(None),
    }
def rule_fp_history(skill_dir: str, rule_id) -> dict | None:
    _rid = as_text(rule_id)
    if not _rid:
        return None
    try:
        _data = read_queue_json(fp_tracker_rules_path(skill_dir), {})
    except Exception as _e: # noqa: BLE001
        log_swallowed(__name__, _e, context=f'rule_fp_history:{type(_e).__name__}')
        return None
    _hit = _data.get(_rid) if isinstance(_data, dict) else None
    if isinstance(_hit, dict) and _hit.get("total"):
        return {
            "total": _hit.get("total", 0),
            "fp": _hit.get("fp", 0),
            "fp_rate": _hit.get("fp_rate", 0.0),
        }
    return None
def fix_experience_history(skill_dir: str, rule_id: str,
                           code_context: str = "") -> list[dict]:
    try:
        return brief_fix_experience(skill_dir, rule_id,
                                    code_context or "") or []
    except Exception as exc: # noqa: BLE001
        log_swallowed(__name__, exc, context=f'fix_experience_history:{type(exc).__name__}')
        return []
def _inject_fix_experience(item: dict, skill_dir: str, rule_id: str) -> None:
    if has_evidence_value(item.get("fix_experience")):
        return
    experience = fix_experience_history(
        skill_dir, rule_id, item.get("code_context", "") or "")
    if experience:
        item["fix_experience"] = experience
def _inject_review_evidence(item: dict, skill_dir: str) -> dict:
    if not isinstance(item, dict):
        return item
    _rid = as_text(item.get("rule_id"))
    if not _rid:
        return item
    _fp_hist = rule_fp_history(skill_dir, _rid)
    if _fp_hist:
        item["rule_fp_history"] = _fp_hist
    _inject_fix_experience(item, skill_dir, _rid)
    return item
def _first_file_path(container) -> str:
    if not isinstance(container, dict):
        return ""
    for key in _FILE_PATH_KEYS:
        value = container.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""
def _target_file_path(sd: str, target: dict, channel: str) -> str:
    plan = as_dict(target.get("plan"))
    for container in (target, plan, as_dict(target.get("entry")),
                      as_dict(plan.get("entry")),
                      as_dict(target.get("proposal"))):
        file_path = _first_file_path(container)
        if file_path:
            return file_path
    if channel == "security":
        plan = load_pending_security_plan(
            sd, as_text(target.get("review_id")))
        return _first_file_path(plan)
    return ""
def _governance_verification(sd: str, target: dict, fixed_source,
                            channel: str) -> dict:
    payload: dict = {}
    if writes_source(target, channel, fixed_source):
        source = _effective_source(target, channel, fixed_source)
        if source:
            payload["fixed_source"] = source
    file_path = _target_file_path(sd, target, channel)
    if file_path:
        payload["file_path"] = file_path
    return payload
def _validate_or_reject(
    sd: str, target: dict, reviews: list, asm: dict,
    fixed_source, channel: str, *, label: str,
) -> tuple[dict | None, dict | None]:
    ok, errors, normalized = validate_review_assessment(
        asm, skill_dir=sd,
        verification=_governance_verification(sd, target, fixed_source,
                                              channel))
    if ok:
        return normalized, None
    return None, _reject_with_html(
        sd, target, reviews,
        f"{label} assessment 不合规: " + "; ".join(errors),
        "resubmit_with_valid_assessment", asm)
def _decision_or_payload(sd: str, target: dict, reviews: list, fixed_source,
                         provider, assessment) -> tuple:
    _decision, _provider_err = _resolve_decision_guarded(
        target, fixed_source, provider, assessment)
    if _provider_err:
        return None, None, None, _reject_with_html(
            sd, target, reviews, _provider_err, "fix_provider_and_retry",
            assessment)
    fs, approved, asm = _decision
    return fs, approved, asm, None
def _gate_chain_or_payload(sd: str, target: dict, reviews: list, fs,
                           asm, channel: str, assessment) -> tuple:
    _gate_payload = _gate_mandatory_assessment(target, channel, asm, reviews)
    if _gate_payload is not None:
        return None, _err_ret_with_html(sd, _gate_payload)
    _write_gate = _gate_source_write_verdict(target, channel, asm, fs, reviews)
    if _write_gate is not None:
        return None, _err_ret_with_html(sd, _write_gate)
    if asm is None:
        return asm, None
    label = "审核信息" if assessment is not None else "provider"
    return _validate_or_reject(
        sd, target, reviews, asm, fs, channel, label=label)
def _reject_with_html(sd: str, target: dict, reviews: list,
                     reason: str, next_action: str,
                     assessment_echo) -> dict:
    return _err_ret_with_html(sd, {
        "status": "error",
        "reason": reason,
        "review_id": as_text(target.get("review_id")),
        "channel": as_text(target.get("channel")),
        "remaining": len(reviews),
        "next_action": next_action,
        "assessment": assessment_echo,
        "review_target": build_review_target_digest(target)})
def _err_ret_with_html(sd: str, payload: dict) -> dict:
    emit_html_report(sd, payload)
    return payload
def _reject_trace(sd: str, target: dict, assessment, payload: dict) -> dict:
    try:
        write_verdict_trace(target, assessment, payload, sd)
    except Exception as exc: # noqa: BLE001
        log_swallowed(__name__, exc,
                      context=f'_reject_trace:{type(exc).__name__}')
    return payload
def _needs_assessment_payload(target: dict, channel: str,
                             reviews: list) -> dict:
    _input_contract = CHANNEL_REVIEW_INPUT_CONTRACT.get(
        channel,
        "审核输入：review_target 完整证据面（code_context/载体四层溯源/"
        "历史基线）＋ provenance_strata 信息完整度判定")
    return {
        "status": "needs_assessment",
        "reason": ("未提交四维审核信息 assessment（严重性/可修复性/"
                   "利弊权衡/误报判定）——本通道（" + channel +
                   "）属强制审核门通道（" +
                   "/".join(CHANNELS) +
                   "），必须先审核后执行。" + _input_contract +
                   "。请基于 review_target 携带的上述完整证据面完成"
                   "四维审核后，携 assessment={verdict:...} 重新调用"),
        "review_id": as_text(target.get("review_id")), "channel": channel,
        "remaining": len(reviews),
        "next_action": "resubmit_with_assessment",
        "review_target": build_review_target_digest(target),
        "review_item_schema": describe_review_item_keys(),
        "review_framework": REVIEW_FRAMEWORK}
def _normalize_final_status(result, channel: str) -> tuple[dict, str]:
    if not isinstance(result, dict):
        logger.warning("[AIReview] 通道 %s 返回非 dict 结果（归一为 failed）: %s",
                       channel, type(result).__name__)
        result = {"status": "failed",
                  "reason": f"通道返回非 dict 结果: {type(result).__name__}"}
    status = result.get("status")
    if isinstance(status, str):
        status = status.strip()
        result["status"] = status
    if not isinstance(status, str) or not status:
        logger.warning(
            "[AIReview] 通道 %s 返回非法 status（%s，归一为 failed）",
            channel,
            type(status).__name__ if not isinstance(status, str) else repr(status))
        status = "failed"
        result["status"] = status
    # 回滚成功的写盘（rolled_back=True）源码已恢复原样，治疗项仍是待审候选，
    # 不得按「已消费」映射 completed（否则 remaining 少计 1 且误报 all_reviews_done）。
    if (status in _COMPLETED_APPLY_STATUSES
            and result.get("rolled_back") is not True):
        status = "completed"
    return result, status
def _find_review_target(reviews: list, review_id: str | None) -> dict | None:
    if review_id is not None:
        normalized_id = as_text(review_id)
        if not normalized_id:
            return None
        return next((r for r in reviews
                     if isinstance(r, dict)
                     and as_text(r.get("review_id")) == normalized_id), None)
    return next(iter(reviews), None)
def _is_aggregate_review(target: dict) -> bool:
    """聚合复核标记以队列条目（entry）为权威位置。

    审核条目由收集层从队列条目派生，``aggregate_review`` 落在 ``entry``
    与 ``cv_evidence`` 视图层而非条目顶层；三处任一为真即聚合复核。
    """
    for _container in (target, as_dict(target.get("entry")),
                       as_dict(target.get("cv_evidence"))):
        if signal_bool(_container.get("aggregate_review")):
            return True
    return False
def _missing_review_id_payload(reviews: list, review_id: str,
                              assessment) -> dict:
    return {
        "status": "error",
        "reason": f"未找到 review_id={review_id}",
        "remaining": len(reviews),
        "next_action": "retry_with_valid_review_id",
        "available_review_ids": [
            f"{r.get('review_id', '')}({r.get('channel', '')})"
            for r in reviews[:20]],
        "assessment": assessment}
def _resolve_decision_guarded(target: dict, fixed_source, provider,
                             assessment) -> tuple[tuple | None, str]:
    try:
        return (resolve_review_decision(target, fixed_source, provider,
                                          assessment), "")
    except Exception as _pe:
        logger.exception("[AIReview] provider 审核回调异常 %s",
                         target.get("review_id", ""))
        return None, f"provider 回调异常: {str(_pe)[:200]}"
def _gate_mandatory_assessment(target: dict, channel: str, asm,
                               reviews: list) -> dict | None:
    if channel in CHANNELS and asm is None:
        return _needs_assessment_payload(target, channel, reviews)
    return None
def _gate_source_write_verdict(target: dict, channel: str, asm,
                               fixed_source, reviews: list) -> dict | None:
    if not writes_source(target, channel, fixed_source):
        return None
    if asm is None:
        return _needs_assessment_payload(target, channel, reviews)
    if not isinstance(asm, dict):
        return None
    verdict = as_text(verdict_text(asm))
    if verdict in _CLOSING_VERDICTS:
        return None
    if verdict == "approve_and_fix":
        return None
    if not verdict:
        return _needs_assessment_payload(target, channel, reviews)
    logger.warning(
        "[AIReview] %s 通道裁决 %s 不能执行源码写盘（须 approve_and_fix）: %s",
        channel, verdict, target.get("review_id", ""))
    return {
        "status": "error",
        "reason": (f"verdict={verdict} 不能执行源码写盘：approve 仅适用于"
                   "编排器代执行的非源码动作；源码全文替换须 verdict="
                   "approve_and_fix 并附 fixability/net_benefit/"
                   "fix_approach=root_cause，请补全四维后重新提交"),
        "review_id": as_text(target.get("review_id")), "channel": channel,
        "remaining": len(reviews),
        "next_action": "resubmit_with_valid_assessment",
        "assessment": asm,
        "review_target": build_review_target_digest(target)}
def _execute_channel_apply_guarded(channel: str, sd: str, target: dict,
                                   fs, asm, approved: bool) -> dict:
    try:
        return dispatch_channel_apply(channel, sd, target, fs, asm, approved)
    except Exception as e:
        logger.exception("[AIReview] 审核执行异常 %s",
                         as_text(target.get("review_id")))
        return {"status": "failed", "reason": str(e)[:200]}
def _next_action(remaining: int | None) -> str:
    if remaining is None:
        return "retry_pending_review_read"
    return "run_next_ai_review" if remaining > 0 else "all_reviews_done"
def _build_review_result_payload(target: dict, channel: str, status: str,
                                 asm, remaining: int | None,
                                 result: dict) -> dict:
    _asm_view = asm if isinstance(asm, dict) else {}
    return {
        "status": status,
        "review_id": as_text(target.get("review_id")),
        "channel": channel,
        "verdict": as_text(_asm_view.get("verdict")),
        "remaining": remaining,
        "pending_ai_review": remaining,
        "next_action": _next_action(remaining),
        "awaiting_ai_execution": build_awaiting_payload(target, result, status),
        "result": result,
        "assessment": asm,
        "review_target": build_review_target_digest(target),
        "review_framework": REVIEW_FRAMEWORK,
    }
def run_next_ai_review(skill_dir: str, fixed_source: str | None = None,
                       provider: Callable[[dict], dict] | None = None,
                       review_id: str | None = None,
                       assessment: dict | None = None,
                       *, _reviews: list | None = None,
                       _emit_html: bool = True) -> dict:
    sd = normalize_skill_dir(skill_dir)
    if _reviews is None:
        agg, read_err = read_pending_reviews(sd)
        if read_err:
            return _pending_read_error(read_err)
        reviews = [r for r in as_list(agg.get("reviews"))
                   if isinstance(r, dict)]
    else:
        reviews = [r for r in _reviews if isinstance(r, dict)]
    if not reviews:
        return {"status": "no_pending", "pending_ai_review": 0,
                "remaining": 0, "next_action": "none",
                "message": "无待 AI 审核执行任务"}
    warm_shared_ast_cache(sd)
    target = _find_review_target(reviews, review_id)
    if target is None:
        return _reject_trace(
            sd, {}, assessment,
            _err_ret_with_html(
                sd, _missing_review_id_payload(reviews, review_id,
                                               assessment)))
    fs, approved, asm, _payload = _decision_or_payload(
        sd, target, reviews, fixed_source, provider, assessment)
    if _payload is not None:
        return _reject_trace(sd, target, assessment, _payload)
    channel = as_text(target.get("channel"))
    asm, _payload = _gate_chain_or_payload(
        sd, target, reviews, fs, asm, channel, assessment)
    if _payload is not None:
        return _reject_trace(sd, target, assessment or asm, _payload)
    result = _execute_channel_apply_guarded(channel, sd, target, fs, asm,
                                            approved)
    result, status = _normalize_final_status(result, channel)
    record_review_verdict(
        target, asm, result, skill_dir=sd,
        fixed_source_sha256=fixed_source_sha256(
            _effective_source(target, channel, fs)))
    # 聚合复核会消费聚合项并展开多条明细；批准 FP 预过滤/展开项会复活
    # 治疗项（fp_suppression_revoked）。两者都使待审集合净增条目，
    # 不能按「采集数-1」推导剩余数，必须重读。
    if (status == "completed" and channel == "cv_uncertain"
            and (_is_aggregate_review(target)
                 or result.get("fp_suppression_revoked") is True)):
        remaining, remaining_err = _read_pending_count(sd)
    else:
        # 普通通道本轮只消费一个条目，沿用已采集清单避免重复提取代码上下文。
        remaining, remaining_err = _read_pending_count(
            sd, _collected=len(reviews), _consumed=status == "completed")
    _ret = _build_review_result_payload(target, channel, status, asm,
                                        remaining, result)
    if remaining_err:
        _ret.update(_pending_read_error(remaining_err))
    if _emit_html and emit_html_report(sd, _ret):
        logger.info("[AIReview] 审核 HTML 报告已生成: %s",
                    as_text(target.get("review_id")))
    return _ret
def _batch_trace_item(res: dict) -> dict:
    _item = {"review_id": res.get("review_id"), "status": res.get("status"),
             "channel": res.get("channel")}
    _inject_present_values(_item, res, (
        "review_target", "verdict", "awaiting_ai_execution"))
    _rsn = res.get("reason") or (res.get("result") or {}).get("reason")
    if _rsn:
        _item["reason"] = _rsn
    return _item
def _pending_materials_payload(sd: str, limit: int) -> dict:
    """无 AI provider 时一次返回全部待审材料（不逐条空转）。

    原实现在无 provider 时逐条调用 ``run_next_ai_review``，每条都返回
    ``needs_assessment`` 并立即 break——一轮只处理 1 条，而每次都要重新
    全量采集 60+ 条待审材料（含代码上下文提取）。改为一次性返回材料，
    调用方拿到全量后统一提交四维审核，彻底消除重复采集。
    """
    aggregate, read_err = read_pending_reviews(sd)
    if read_err:
        return _pending_read_error(read_err)
    reviews = [r for r in as_list(aggregate.get("reviews"))
               if isinstance(r, dict)]
    materials = reviews[:limit] if limit else []
    return {
        "status": "needs_assessment",
        "processed": 0,
        "remaining": len(reviews),
        "next_action": "submit_assessments",
        "reason": ("未提供 AI provider：一次性返回全部待审材料"
                   "（严重性/可修复性/利弊权衡/误报判定四维），"
                   "避免逐条空转与重复采集"),
        "pending_materials": materials,
        "pending_materials_truncated": max(0, len(reviews) - len(materials)),
        "items": [],
        "pending_ai_executions": [],
    }


def _run_batch_loop(sd: str, provider,
                    max_items: int) -> tuple[list, int, dict | None, str]:
    done = []
    processed = 0
    _consumed_ids: set[str] = set()
    _batch_framework: dict | None = None
    while processed < max_items:
        aggregate, read_err = read_pending_reviews(sd)
        if read_err:
            return done, processed, _batch_framework, read_err
        _pending_reviews = as_list(aggregate.get("reviews"))
        if not _pending_reviews:
            break
        _head_id = as_text(_pending_reviews[0].get("review_id"))
        if _head_id and _head_id in _consumed_ids:
            logger.info("[AIReview] 批量审核提前停止：%s 未被消费",
                        _head_id)
            break
        # 逐条重渲染整份审核报表是 O(n²)（实测 65 条 × 0.22 s ≈ 14 s）：
        # 批量循环内抑制，改由 run_all_ai_reviews 末尾一次性发射全量。
        res = run_next_ai_review(sd, provider=provider,
                                 _reviews=_pending_reviews,
                                 _emit_html=False)
        done.append(_batch_trace_item(res))
        _rf = as_dict(res.get("review_framework"))
        if _rf:
            _batch_framework = _rf
        processed += 1
        for _done_id in (_head_id, as_text(res.get("review_id"))):
            if _done_id:
                _consumed_ids.add(_done_id)
        if res.get("status") in ("needs_assessment", "needs_fixed_source",
                                 "error", "failed", "no_pending"):
            break
    return done, processed, _batch_framework, ""
def _normalize_max_items(value) -> int | None:
    if value is None:
        return MAX_AI_REVIEW_ITEMS
    index = plan_index(value)
    if index is None or index < 0:
        logger.warning("[AIReview] max_items 非法（按拒绝启动处理）: %r", value)
        return None
    return index
def run_all_ai_reviews(skill_dir: str,
                       provider: Callable[[dict], dict] | None = None,
                       max_items: int = MAX_AI_REVIEW_ITEMS) -> dict:
    sd = normalize_skill_dir(skill_dir)
    limit = _normalize_max_items(max_items)
    if limit is None:
        return {
            "status": "error",
            "error": f"max_items 须为非负整数或省略，当前: {max_items!r}",
            "reason": ("批量审核上限非法：拒绝以不确定上限启动批量"
                       "（fail-safe）"),
            "processed": 0,
            "remaining": None,
            "next_action": "fix_max_items",
            "items": [],
            "pending_ai_executions": [],
        }
    if provider is None:
        return _pending_materials_payload(sd, limit)
    done, processed, _batch_framework, read_err = _run_batch_loop(
        sd, provider, limit)
    remaining = None
    if not read_err:
        remaining, read_err = _read_pending_count(sd)
    _pending_execs = [d["awaiting_ai_execution"] for d in done
                     if d.get("awaiting_ai_execution")]
    out = {
        "processed": processed,
        "remaining": remaining,
        "next_action": _next_action(remaining),
        "items": done,
        "pending_ai_executions": _pending_execs,
    }
    if read_err:
        out.update(_pending_read_error(read_err))
    if _batch_framework:
        out["review_framework"] = _batch_framework
    if _emit_step_trace_safe(
            "ai_review_batch", sd, out,
            context="批量审核总览 HTML 生成失败"):
        logger.info(
            "[AIReview] 批量审核总览 HTML 已生成: processed=%d, remaining=%s",
            processed, "unknown" if remaining is None else remaining)
    return out
_FIX_AWAITING_EVIDENCE_KEYS = (
    "diagnosis_evidence", "cv_context", "fix_precheck", "fixer_risk",
    "function_summary", "fix_experience", "rule_id_canonical",
    "rule_fp_history", "treatment_history", "evidence_completeness",
)
_AWAITING_PROVENANCE_KEYS = (
    "phase", "source", "diagnosis_context", "treatment_context",
    "retrospective_context",
)
def _effective_source(target: dict, channel: str, fixed_source) -> str:
    target = as_dict(target)
    explicit = provided_source(fixed_source)
    if channel == "cleanup":
        plan = as_dict(target.get("plan"))
        if cleanup_operation(target, plan) == "delete_temp_residue":
            return ""
        return explicit or provided_source(plan.get("fixed_source"))
    return explicit
def writes_source(target: dict, channel: str, fixed_source) -> bool:
    target = as_dict(target)
    if channel in ("treatment", "security"):
        return bool(provided_source(fixed_source))
    if channel == "cleanup":
        return bool(_effective_source(target, channel, fixed_source))
    if channel == "feedback":
        return bool(target.get("requires_fixed_source")
                    and provided_source(fixed_source))
    return False
def _aggregate_expansion_error(target: dict, review_id: str) -> dict | None:
    details = target.get("suppressed_details")
    if (isinstance(details, list) and details
            and all(isinstance(detail, dict)
                    and as_text(detail.get("locator")) for detail in details)):
        return None
    return {
        "status": "error",
        "review_id": review_id,
        "reason": ("聚合复核明细缺失、类型非法或 locator 为空，无法保证所有"
                   "抑制项展开复核；条目保持待审"),
        "next_action": "repair_aggregate_review_details",
        "review_retained": True,
    }
def apply_cv_uncertain_verdict(
        skill_dir: str, review_id: str, approved: bool | None = None,
        verdict: str = "", fp_evidence: Any = "") -> dict:
    sd = normalize_skill_dir(skill_dir)
    verdict = as_text(verdict)
    if verdict and verdict not in VERDICT_VALUES:
        logger.warning("[AIReview] CV 复核裁决非法（拒绝执行）: %r", verdict)
        return {"status": "error", "review_id": review_id,
                "reason": (f"未知 CV 复核裁决 {verdict!r}（合法值: "
                           f"{'/'.join(VERDICT_VALUES)}）"),
                "next_action": "provide_valid_cv_verdict"}
    if not verdict and approved is None:
        return {"status": "error", "review_id": review_id,
                "reason": "CV 复核缺裁决信号，不得默认确认问题存在",
                "next_action": "provide_cv_verdict_or_approval"}
    path = cv_uncertain_path(sd)
    # 队列读改写必须持锁：诊断入队（ai_review_queue._persist_merged_entries 持锁
    # 读改写）与本裁决写回并发时，无锁写回会用陈旧 entries 覆盖新入队条目
    # （lost update，待审条目静默丢失）。
    with locked_artifact(path) as _cv_lock:
        if not _cv_lock:
            return {"status": "error", "review_id": review_id,
                    "reason": "cv_uncertain 队列锁不可用，拒绝无锁读改写",
                    "next_action": "retry_cv_verdict",
                    "review_retained": True}
        return _apply_cv_verdict_under_lock(
            sd, path, review_id, approved, verdict, fp_evidence)
def _apply_cv_verdict_under_lock(sd: str, path: str, review_id, approved,
                                 verdict: str, fp_evidence) -> dict:
    data = read_queue_json(path, {})
    entries = as_list(data.get("entries"))
    target = find_pending_entry(entries, "review_id", review_id)
    if target is None:
        return {"status": "error", "reason": f"未找到 {review_id}"}
    if verdict in ("reject", "defer"):
        return _retain_cv_entry_pending(
            path, data, target, review_id, verdict)
    if verdict in APPROVAL_VERDICTS:
        approved = True
    elif verdict == "reject_as_fp":
        approved = False
    else:
        approved = approval_flag(approved)
    if not approved and is_missing_dimension(fp_evidence):
        return {"status": "error", "review_id": review_id,
                "reason": "CV 误报销项须附 fp_evidence，条目保持待审",
                "next_action": "provide_cv_fp_evidence",
                "soft_closure_rejected": True}
    if not approved:
        target["fp_evidence"] = fp_evidence
    if approved and target.get("aggregate_review"):
        _aggregate_error = _aggregate_expansion_error(target, review_id)
        if _aggregate_error is not None:
            return _aggregate_error
    _revoked = _revoke_fp_prefilter_suppression(sd, target, approved)
    if _revoked is not None and _revoked.get("revoke_error"):
        return {
            "status": "failed",
            "review_id": review_id,
            "reason": ("CV 复核撤销 FP 抑制失败，条目保持待审: "
                       + str(_revoked["revoke_error"])),
            "next_action": "retry_cv_verdict",
            "review_retained": True,
            **_revoked,
        }
    _mark_cv_resolved(target, approved)
    aggregate_result = _apply_cv_aggregate_review(
        sd, path, data, target, review_id, approved)
    if aggregate_result is not None:
        if _revoked is not None:
            aggregate_result.update(_revoked)
        return aggregate_result
    write_queue_json(path, data)
    _record_cv_verdict(sd, target, approved)
    logger.info("[AIReview] CV uncertain 复核裁决 %s -> %s",
                review_id, "confirmed" if approved else "rejected")
    _out = {"status": "approved" if approved else "rejected",
            "review_id": review_id,
            "reason": "AI确认问题存在" if approved else "AI判定为误报"}
    if _revoked is not None:
        _out.update(_revoked)
    return _out
def _revoke_fp_prefilter_suppression(sd: str, target: dict,
                                     approved: bool) -> dict | None:
    if not approved or not (
            signal_bool(target.get("fp_filter_suppressed"))
            or signal_bool(target.get("aggregate_expanded"))):
        return None
    _raw_locator = target.get("locator")
    _locator = canonical_locator_key(
        _raw_locator if isinstance(_raw_locator, str) else "")
    if not _locator:
        _locator = canonical_locator_key(make_locator_from_finding(target))
    if not _locator:
        logger.warning(
            "[AIReview] FP 预过滤复核缺 locator，无法撤销治疗项误报销项")
        return {"fp_suppression_revoked": False,
                "revoke_error": ("FP 预过滤复核缺 locator，"
                                 "无法定位治疗项（需人工复核）")}
    _rule_id = as_text(target.get("rule_id"))
    try:
        state = load_treatment_state(sd)
        items = as_list(state.get("items"))
    except (OSError, ValueError, TypeError) as _se:
        logger.warning(
            "[AIReview] FP 预过滤撤销抑制读取治疗状态失败（需人工复核）: %s", _se)
        return {"fp_suppression_revoked": False,
                "revoke_error": str(_se)}
    for _pos, _item in enumerate(items):
        if not isinstance(_item, dict):
            continue
        if item_status(_item) != "fp_confirmed":
            continue
        _raw_item_locator = _item.get("locator")
        _item_locator = canonical_locator_key(
            _raw_item_locator if isinstance(_raw_item_locator, str) else ""
        ) or canonical_locator_key(make_locator_from_finding(_item))
        if _item_locator != _locator:
            continue
        if _rule_id and as_text(_item.get("rule_id")) != _rule_id:
            continue
        result = as_dict(_item.get("result"))
        for _key in ("ai_fix_reason", "ai_review_verdict",
                     "ai_review_assessment", "fp_evidence",
                     "cv_context_at_review"):
            result.pop(_key, None)
        result["fp_prefilter_revoked"] = {
            "review_id": as_text(target.get("review_id")),
            "reason": "AI 裁决误报抑制不成立，条目复活重新治疗",
            "revoked_at": now_iso(),
        }
        _index = plan_index(_item.get("index", _pos))
        if _index is None:
            _index = _pos
        try:
            apply_item_status(state, _index, "pending", result)
            save_treatment_state(sd, state)
        except (OSError, ValueError, TypeError) as _se:
            logger.warning(
                "[AIReview] FP 预过滤撤销抑制写回治疗状态失败"
                "（需人工复核）: %s", _se)
            return {"fp_suppression_revoked": False,
                    "revoke_error": str(_se)}
        _mark_treatment_plan_status_safe(
            sd, _index, "pending",
            {"fp_prefilter_revoked_at": result["fp_prefilter_revoked"][
                "revoked_at"],
             "fp_prefilter_review_id": as_text(target.get("review_id"))})
        _rule_removed = drop_fp_suppression_rule(sd, _rule_id)
        logger.info(
            "[AIReview] FP 预过滤抑制被撤销，治疗项 #%d 复活为 pending: %s "
            "(抑制规则移除=%s)",
            _index, _rule_id, _rule_removed)
        return {"fp_suppression_revoked": True,
                "revoked_index": _index,
                "suppression_rule_removed": _rule_removed,
                "next_action": "run_ai_manual_fix"}
    logger.info(
        "[AIReview] FP 预过滤批准但未找到 fp_confirmed 治疗项（可能已重建）: %s",
        _rule_id)
    return {"fp_suppression_revoked": False}
def _retain_cv_entry_pending(path: str, data: dict, target: dict,
                             review_id: str, verdict: str) -> dict:
    target["status"] = "pending_review"
    target["ai_verdict"] = verdict
    target["soft_closure_rejected_at"] = now_iso()
    if verdict == "defer":
        target["deferred_at"] = target["soft_closure_rejected_at"]
    write_queue_json(path, data)
    logger.warning(
        "[AIReview] CV uncertain 复核 %s 的 %s 软销项被拒绝"
        "（条目保持 pending）", review_id, verdict)
    return {"status": "failed", "review_id": review_id,
            "reason": (f"CV verdict={verdict} 不是终态：请确认问题存在"
                       "（approve）或判定误报（reject_as_fp 附 "
                       "fp_evidence）后重跑"),
            "next_action": "provide_cv_verdict_or_fp_evidence",
            "soft_closure_rejected": True}
def _mark_cv_resolved(target: dict, approved: bool) -> None:
    target["status"] = "resolved"
    target["ai_verdict"] = "confirmed" if approved else "rejected"
    target["resolved_at"] = now_iso()
def _apply_cv_aggregate_review(sd: str, path: str, data: dict, target: dict,
                               review_id: str, approved: bool) -> dict | None:
    if not target.get("aggregate_review"):
        return None
    if approved:
        expanded = _expand_aggregate_suppressed(target, data)
        write_queue_json(path, data)
        logger.info("[AIReview] 聚合复核 %s approved：展开 %d 条明细入队逐条复核",
                    review_id, expanded)
        return {"status": "approved", "review_id": review_id,
                "reason": f"批量抑制判定过宽：已展开 {expanded} 条明细逐条复核"}
    if target.get("suppressed_details"):
        _backfill_aggregate_members(sd, target, review_id)
    return None
def _open_confirmation_store(sd: str, unavailable_reason: str):
    try:
        return HumanConfirmationStore(sd)
    except Exception as _he: # noqa: BLE001
        logger.warning("[AIReview] %s: %s", unavailable_reason, _he)
        return None
def _try_record_confirmation(store, locator, verdict: str, *,
                             rule_id="", severity="", reason: str) -> bool:
    try:
        persisted = store.record(
            as_text(locator), verdict,
            rule_id=as_text(rule_id), severity=as_text(severity), reason=reason)
        if persisted is False:
            logger.warning(
                "[AIReview] 确认库回填未持久化(%s，不阻断销项)", reason)
            return False
        return True
    except Exception as _he: # noqa: BLE001
        logger.warning(
            "[AIReview] 确认库回填失败(%s，不阻断销项): %s", reason, _he)
        return False
def _backfill_aggregate_members(sd, target: dict, review_id: str) -> None:
    _hstore_agg = _open_confirmation_store(
        sd, "聚合复核成员回填确认库不可用（下轮将重新入队）")
    if _hstore_agg is None:
        return
    _backfilled = 0
    for _d in target.get("suppressed_details") or []:
        if not isinstance(_d, dict):
            continue
        _dloc = as_text(_d.get("locator"))
        if not _dloc:
            continue
        if _try_record_confirmation(
                _hstore_agg, _dloc, "false_positive",
                rule_id=target.get("rule_id"), severity=_d.get("severity"),
                reason="ai_semantic_arbitration:cv_uncertain_aggregate"):
            _backfilled += 1
    if _backfilled:
        logger.info(
            "[AIReview] 聚合复核 %s rejected：%d 条成员回填确认库"
            " false_positive（90 天背书期防复核振荡）",
            review_id, _backfilled)
def _record_cv_verdict(sd, target: dict, approved: bool) -> None:
    if target.get("aggregate_review"):
        return
    _hstore = _open_confirmation_store(
        sd, "仲裁裁决回填 HumanConfirmationStore 失败（队列条目已销项）")
    if _hstore is None:
        return
    _try_record_confirmation(
        _hstore, target.get("locator"),
        "confirmed" if approved else "false_positive",
        rule_id=target.get("rule_id"), severity=target.get("severity"),
        reason="ai_semantic_arbitration:cv_uncertain")
def _expand_aggregate_suppressed(target: dict, data: dict) -> int:
    entries = data.get("entries")
    if not isinstance(entries, list):
        entries = data["entries"] = []
    _pending_keys, _rejected_keys = _blocking_review_keys(entries)
    _floor = max_review_seq(entries, REVIEW_ID_PREFIX)
    details = target.get("suppressed_details")
    if not isinstance(details, list):
        details = []
    _rid = as_text(target.get("rule_id"))
    added = 0
    for d in details:
        if not isinstance(d, dict):
            continue
        _loc = as_text(d.get("locator"))
        _key = review_entry_key({"locator": _loc, "rule_id": _rid})
        if not _loc or _key in _pending_keys or _key in _rejected_keys:
            continue
        _floor += 1
        entries.append(_aggregate_expanded_entry(d, _rid, _loc, _floor))
        _pending_keys.add(_key)
        added += 1
    return added
def _blocking_review_keys(entries: list) -> tuple[set, set]:
    pending: set = set()
    rejected: set = set()
    for e in entries:
        if not isinstance(e, dict):
            continue
        _key = review_entry_key(e)
        if e.get("status") == "pending_review":
            pending.add(_key)
        elif (e.get("status") == "resolved"
                and e.get("ai_verdict") == "rejected"):
            rejected.add(_key)
    return pending, rejected
def _aggregate_member_confidence(value) -> float:
    if isinstance(value, str):
        try:
            value = float(value.strip())
        except ValueError:
            return 0.0
    try:
        confidence = float(normalize_confidence(value, 0.0))
    except (OverflowError, TypeError, ValueError):
        return 0.0
    return confidence if math.isfinite(confidence) else 0.0
def _aggregate_expanded_entry(d: dict, rule_id: str, loc: str,
                              seq: int) -> dict:
    _src_method = as_text(d.get("source_method"))
    _conf = _aggregate_member_confidence(d.get("confidence", 0))
    return {
        "review_id": f"{REVIEW_ID_PREFIX}-{seq:03d}",
        "channel": "cv_uncertain",
        "locator": loc,
        "file_path": as_text(d.get("file")),
        "line": normalize_line_no(d.get("line")),
        "rule_id": rule_id,
        "rule_family": as_text(d.get("rule_family")),
        "severity": as_text(d.get("severity")),
        "conclusion": "suppressed",
        "confidence": _conf,
        "suppressed_review": True,
        "suppression_rule": as_text(
            d.get("fp_deferred_reason"))[:120],
        "aggregate_expanded": True,
        "message": as_text(d.get("message")),
        "code_context": "",
        "sources": [_src_method] if _src_method else [],
        "evidence_detail": ([{
            "source_method": _src_method[:60],
            "confidence": _conf,
            "rule_id": rule_id[:40],
        }] if _src_method else []),
        "counter_evidence": bool(d.get("counter_evidence")),
        "notes": "expanded_from_aggregate_review",
        "status": "pending_review",
    }
def apply_cv_uncertain_review(sd: str, review: dict,
                              assessment: dict | None = None,
                              approved: bool | None = None) -> dict:
    review = as_dict(review)
    verdict = as_text(verdict_text(as_dict(assessment)))
    approved_flag = (None if approved is None
                     else approval_flag(approved))
    if not verdict and approved_flag is None:
        return {"status": "error",
                "review_id": as_text(review.get("review_id")),
                "reason": ("CV 复核缺裁决信号：须提供 assessment.verdict "
                           "或 approved 布尔值（不得默认确认）"),
                "next_action": "provide_cv_verdict_or_approval"}
    options: dict[str, Any] = {
        "verdict": verdict,
        "fp_evidence": as_dict(assessment).get("fp_evidence", ""),
    }
    if approved_flag is not None:
        options["approved"] = approved_flag
    return apply_cv_uncertain_verdict(
        sd, review.get("review_id", ""), **options)
def _mark_treatment_plan_status_safe(sd: str, index: int, status: str,
                                     extra: dict) -> None:
    try:
        mark_fix_plan_status(sd, index, status, extra)
    except Exception as e: # noqa: BLE001
        logger.warning("[AIReview] 修复方案清单状态回写失败: %s", e)
class _TreatmentTarget(NamedTuple):
    state: dict
    index: int
    item: dict
def _treatment_review_identity_mismatch(review: dict, item: dict) -> str:
    for field in ("rule_id", "finding_id"):
        expected = as_text(review.get(field))
        current = as_text(item.get(field))
        if expected and current and expected != current:
            return (f"{field}: 审核={expected!r}, 当前={current!r}")
    expected_file = _first_file_path(review)
    current_file = _first_file_path(item)
    if expected_file and current_file and expected_file != current_file:
        return f"file_path: 审核={expected_file!r}, 当前={current_file!r}"
    expected_line = normalize_line_no(review.get("line"))
    current_line = normalize_line_no(item.get("line"))
    if expected_line > 0 and current_line > 0 and expected_line != current_line:
        return f"line: 审核={expected_line}, 当前={current_line}"
    return ""
def _load_treatment_target(sd: str, review: dict
                           ) -> tuple[_TreatmentTarget | None, dict | None]:
    state = load_treatment_state(sd)
    items = as_list(state.get("items"))
    _raw_idx = review.get("index", -1)
    idx = plan_index(_raw_idx)
    if idx is None or idx < 0:
        return None, {"status": "error",
                      "reason": f"无效治疗项索引: {_raw_idx!r}"}
    item, _loc_error = locate_treatment_item(items, idx)
    if item is None:
        _audit_reason, _return_reason = _loc_error
        if idx >= len(items):
            _return_reason = f"无效治疗项索引: {_raw_idx!r}"
        return None, {"status": "error", "reason": _return_reason}
    mismatch = _treatment_review_identity_mismatch(review, item)
    if mismatch:
        logger.warning(
            "[AIReview] 治疗审核身份与当前条目冲突，拒绝执行: "
            "review_id=%s index=%d %s",
            as_text(review.get("review_id")), idx, mismatch)
        return None, {
            "status": "error",
            "reason": f"治疗审核身份与当前条目不一致（{mismatch}）",
            "review_id": as_text(review.get("review_id")),
            "channel": "treatment",
            "next_action": "refresh_treatment_review",
            "review_retained": True,
        }
    return _TreatmentTarget(state, idx, item), None
def _commit_treatment_status(sd: str, target: _TreatmentTarget, new_status: str,
                             result_fields: dict, plan_status: str,
                             plan_extra: dict) -> None:
    result = as_dict(target.item.get("result"))
    result.update(result_fields)
    apply_item_status(target.state, target.index, new_status, result)
    save_treatment_state(sd, target.state)
    _mark_treatment_plan_status_safe(sd, target.index, plan_status, plan_extra)
def _record_treatment_fp(sd: str, target: _TreatmentTarget,
                         review: dict, assessment: dict) -> str:
    fp_evidence = assessment.get("fp_evidence")
    _cv_ctx = review.get("cv_context")
    _cv_note = ""
    if isinstance(_cv_ctx, dict) and _cv_ctx.get("cv_conclusion"):
        _cv_note = (f"[CV结论={_cv_ctx.get('cv_conclusion')}, "
                    f"独立源={_cv_ctx.get('cv_source_count', 0)}, "
                    f"置信={_cv_ctx.get('cv_confidence', 0)}]")
        fp_evidence = f"{fp_evidence} {_cv_note}"
    _result_fields = {
        "ai_fix_reason": fp_evidence,
        "ai_review_verdict": "reject_as_fp",
        "ai_review_assessment": assessment,
    }
    if isinstance(_cv_ctx, dict):
        _result_fields["cv_context_at_review"] = _cv_ctx
    _commit_treatment_status(
        sd, target, "fp_confirmed", _result_fields, "fp_confirmed",
        {"ai_review_verdict": "reject_as_fp", "fp_evidence": fp_evidence})
    return fp_evidence
def _mark_treatment_fp(sd: str, review: dict, assessment: dict) -> dict:
    target, error = _load_treatment_target(sd, review)
    if error is not None:
        return error
    idx = target.index
    fp_evidence = _record_treatment_fp(sd, target, review, assessment)
    fixated: list = []
    _fixation_blocked: dict | None = None
    try:
        fr = _fixate_fp_rules_impl(sd, items=[target.item], min_count=1)
    except Exception as e: # noqa: BLE001
        logger.warning("[AIReview] 误报即时固化失败（状态已置 fp_confirmed，反哺阶段兜底）: %s", e)
        fr = {}
    fr = as_dict(fr)
    if fr.get("blocked_by_zero_gate"):
        _fixation_blocked = {
            "blocked_by_zero_gate": True,
            "fp_mask_unreviewed": fr.get("fp_mask_unreviewed", 0),
            "next_action": "被抑制 findings 逐项复核（resolve_backlog_item）"
                           "通过后，反哺阶段 fixate_fp_rules 补固化",
        }
        logger.warning(
            "[AIReview] 误报即时固化被归零门禁阻断（裁决已登记，未固化）: "
            "%s 条被抑制 finding 未复核", fr.get("fp_mask_unreviewed"))
    else:
        fixated = fr.get("fixated", []) or []
    logger.info("[AIReview] 治疗项 #%d 判定误报: %s (fixated=%s)",
                idx, review.get("rule_id", ""), fixated)
    _fp_out = {"status": "fp_confirmed",
               "reason": f"AI 判定误报: {fp_evidence}",
               "fixated_rules": fixated,
               "fp_feedback": "误报规则已固化（或将于反哺阶段固化），诊断阶段将自动过滤"}
    if _fixation_blocked is not None:
        _fp_out["fixation_gate"] = _fixation_blocked
    return _fp_out
def _mark_treatment_closed(sd: str, review: dict, assessment: dict,
                           verdict: str) -> dict:
    target, error = _load_treatment_target(sd, review)
    if error is not None:
        return error
    rationale = assessment.get("verdict_rationale") or (
        "AI 审核后决定不修复（利弊权衡后 cons 大于 pros）" if verdict == "reject"
        else "AI 审核后暂缓处理（可修复性不足或依赖未就绪）")
    reason = (
        f"软销项被拒绝（verdict={verdict}）：治疗项 #{target.index} 保持 "
        "pending，真实问题不得以 suggestion/reject/defer 跳过。"
        "请提供 fixed_source 真实修复，或改判 reject_as_fp 并附 "
        "fp_evidence 完成误报规则固化。原审核理由："
        f"{str(rationale)[:300]}")
    logger.error("[AIReview] 治疗项 #%d 软销项被拒绝(%s): %s",
                 target.index, verdict, str(rationale)[:200])
    return {
        "status": "failed",
        "verdict": verdict,
        "reason": reason,
        "review_id": as_text(review.get("review_id")),
        "channel": as_text(review.get("channel")) or "treatment",
        "next_action": "provide_fixed_source_or_fp_evidence",
        "soft_closure_rejected": True,
        "assessment": assessment,
    }
def apply_treatment_verdict(
        sd: str, review: dict, fixed_source: str,
        assessment: dict | None = None, approved: bool | None = None) -> dict:
    review = as_dict(review)
    ok, errors, normalized = validate_review_assessment(
        assessment, skill_dir=sd,
        verification=_governance_verification(
            sd, review, fixed_source, "treatment"))
    if not ok:
        logger.warning(
            "[AIReview] 治疗执行器拒绝未通过契约的 assessment: %s；%s",
            as_text(review.get("review_id")), "; ".join(errors))
        return {"status": "error",
                "review_id": as_text(review.get("review_id")),
                "channel": "treatment",
                "reason": "治疗 assessment 不合规: " + "; ".join(errors),
                "next_action": "resubmit_with_valid_assessment",
                "assessment": assessment}
    assessment = normalized
    verdict = as_text(verdict_text(assessment))
    write_gate = _gate_source_write_verdict(
        review, "treatment", assessment, fixed_source, [review])
    if write_gate is not None:
        return write_gate
    approved = (verdict in APPROVAL_VERDICTS if approved is None
                else approval_flag(approved))
    if verdict == "reject_as_fp":
        return _mark_treatment_fp(sd, review, assessment)
    if verdict in ("reject", "defer") or not approved:
        return _mark_treatment_closed(sd, review, assessment,
                                      verdict if verdict in ("reject", "defer")
                                      else "reject")
    if not provided_source(fixed_source):
        return needs_fixed_source("治疗")
    res = apply_ai_fix(sd, review.get("index"), fixed_source,
                       review.get("description", ""))
    emit_ai_fix_trace(sd, review.get("index"), res)
    # 失败尝试必须落非 pending 终态：否则条目不落账、待审队列队首
    # 恒为同一项，反复重跑整轮回归（实测 76 s/项）而永不推进。
    if res.get("status") not in _COMPLETED_APPLY_STATUSES:
        record_item_failure(sd, review.get("index"), res)
    _out = {"status": res.get("status"), "reason": res.get("reason", ""),
            "regression_verified": res.get("regression_verified", False),
            "targeted_regression": res.get("targeted_regression", {}),
            "rolled_back": res.get("rolled_back", False),
            "fix_result_path": res.get("fix_result_path", "")}
    if res.get("state_save_warning"):
        _out["state_save_warning"] = res["state_save_warning"]
    return _out
def _emit_step_trace_safe(step_name: str, skill_dir: str, payload: Any, *,
                          extra: dict | None = None,
                          context: str) -> bool:
    try:
        return emit_step_trace(step_name, skill_dir, payload,
                               extra=extra, context=context)
    except Exception as exc: # noqa: BLE001
        logger.warning("[AIReview] %s: %s", context, exc)
        return False
def fixate_fp_rules(skill_dir: str, items: list | None = None,
                    min_count: int | None = None) -> dict:
    skill_dir = normalize_skill_dir(skill_dir)
    options: dict[str, Any] = {"items": items}
    if min_count is not None:
        options["min_count"] = min_count
    result = _fixate_fp_rules_impl(skill_dir, **options)
    _emit_step_trace_safe("fp_fixate", skill_dir, result,
                          extra={"skill_dir": skill_dir},
                          context="固化 HTML 留痕失败")
    return result
def _build_memory_awaiting(target: dict, mem_op) -> dict:
    awaiting = {
        "action": "execute_memory_operation",
        "instruction": ("审核已通过且状态已落盘；请按 memory_operation 执行"
                        "对应的记忆同步操作，完成本次增强相关操作；"
                        "provenance 为本条增强的四层溯源（phase/source/"
                        "diagnosis_context/treatment_context/"
                        "retrospective_context），记忆内容须一并写入，"
                        "保证进化记忆可独立追溯完整上下文链"),
        "memory_operation": mem_op,
    }
    _prov = as_dict(target.get("provenance"))
    if _prov:
        awaiting["provenance"] = _prov
    _entry = as_dict(target.get("entry"))
    if _entry:
        awaiting["entry"] = _entry
    return awaiting
def _inject_present_values(awaiting: dict, source: dict, keys) -> None:
    for key in keys:
        value = source.get(key)
        if has_evidence_value(value):
            awaiting[key] = value
_EMPTY_EVIDENCE_TYPES = (list, tuple, set, frozenset, dict)
def has_evidence_value(value: Any) -> bool:
    if isinstance(value, str):
        return bool(value.strip())
    if value is None:
        return False
    if isinstance(value, _EMPTY_EVIDENCE_TYPES):
        return bool(value)
    return True
def _resolve_provenance_source(target: dict) -> dict | None:
    _plan_entry = as_dict(as_dict(target.get("plan")).get("entry"))
    if _plan_entry:
        return _plan_entry
    return as_dict(target.get("entry")) or None
def _inject_awaiting_provenance(awaiting: dict, target: dict) -> None:
    for source in (as_dict(_resolve_provenance_source(target)),
                   as_dict(target.get("provenance"))):
        for key in _AWAITING_PROVENANCE_KEYS:
            value = source.get(key)
            if has_evidence_value(value):
                awaiting.setdefault(key, value)
    strata = target.get("provenance_strata")
    if isinstance(strata, int) and not isinstance(strata, bool):
        awaiting.setdefault("provenance_strata", strata)
def _inject_fix_awaiting_evidence(target: dict, awaiting: dict) -> None:
    _inject_present_values(awaiting, target, _FIX_AWAITING_EVIDENCE_KEYS)
    _inject_awaiting_provenance(awaiting, target)
def _build_fix_awaiting(target: dict) -> dict:
    _plan = as_dict(target.get("plan"))
    _plan_entry = as_dict(_plan.get("entry"))
    awaiting = {
        "action": "generate_and_submit_fixed_source",
        "instruction": (f"审核通过，待 AI 执行修复：基于 code_context/fix_plan/fix_guidance "
                        f"生成修复后源码全文（含受影响注释/docstring 的同步更新，"
                        f"改代码也改注释），再次调用 run_next_ai_review("
                        f"skill_dir, fixed_source=..., "
                        f"review_id='{target.get('review_id', '')}', "
                        f"assessment=...) 提交写盘；源码写盘的 assessment 必须为 "
                        f"verdict='approve_and_fix'、fix_approach='root_cause' 并附 "
                        f"severity_assessment/fixability/net_benefit/fp_or_real，"
                        f"不得直接复用仅 approve 的评估（写盘门会退回）；写盘后仅跑"
                        f"对应修改的定向回归，不跑全量回归"),
        "review_id": target.get("review_id", ""),
        "target": target.get("target", ""),
        "rule_id": target.get("rule_id", ""),
        "description": target.get("description", ""),
        "severity": target.get("severity", ""),
        "line": target.get("line", 0),
        "strategy": target.get("strategy", ""),
        "file_path": target.get("file_path", ""),
        "code_context": target.get("code_context", ""),
        "fix_plan": _plan_entry.get("fixed_source_hint") or target.get("fix_plan"),
        "fix_guidance": target.get("fix_guidance", ""),
    }
    _inject_fix_awaiting_evidence(target, awaiting)
    return awaiting
def build_awaiting_payload(target: dict, result: dict,
                            status: str) -> dict | None:
    target = as_dict(target)
    result = as_dict(result)
    mem_op = result.get("memory_operation")
    if (mem_op and status in ("applied", "completed")
            and not result.get("review_retained")):
        return _build_memory_awaiting(target, mem_op)
    if status == "needs_fixed_source":
        return _build_fix_awaiting(target)
    return None
_ADJUSTMENT_BUCKETS = {
    "method_confidence_multiplier": "method_confidence_multipliers",
    "cv_confidence_threshold": "cv_confidence_thresholds",
    "fixer_safety_override": "fixer_safety_overrides",
}
_ADJUSTMENT_NUMERIC_KINDS = frozenset((
    "method_confidence_multiplier", "cv_confidence_threshold"))
def _normalized_adjustment_value(kind: str, val):
    if kind in _ADJUSTMENT_NUMERIC_KINDS:
        return safe_float(val, None)
    return val
def _empty_approved_adjustments() -> dict:
    skeleton = {"version": "1.0"}
    skeleton.update({bucket: {} for bucket in _ADJUSTMENT_BUCKETS.values()})
    skeleton["last_updated"] = ""
    return skeleton
def apply_approved_adjustment(
        skill_dir: str, review_id: str | dict, approved: bool = True,
        assessment: dict | None = None) -> dict:
    if isinstance(review_id, dict):
        review_id = review_id.get("review_id", "")
    sd = normalize_skill_dir(skill_dir)
    if assessment is None:
        target = {"review_id": as_text(review_id), "channel": "adjustment"}
        return _needs_assessment_payload(
            target, "adjustment", [target])
    verdict = verdict_text(as_dict(assessment))
    if verdict and verdict not in VERDICT_VALUES:
        logger.warning(
            "[AIReview] 调整建议裁决非法（保留待审）: review_id=%r verdict=%r",
            review_id, verdict)
        return {
            "status": "error",
            "review_id": as_text(review_id),
            "channel": "adjustment",
            "reason": (f"未知调整建议裁决 {verdict!r}（合法值: "
                       f"{'/'.join(VERDICT_VALUES)}）"),
            "next_action": "provide_valid_adjustment_verdict",
            "review_retained": True,
            "assessment": assessment,
        }
    if assessment is not None:
        ok, errors, normalized = validate_review_assessment(
            assessment, skill_dir=sd)
        if not ok:
            logger.warning(
                "[AIReview] 调整执行器拒绝未通过契约的 assessment: %s；%s",
                as_text(review_id), "; ".join(errors))
            return {
                "status": "error",
                "review_id": as_text(review_id),
                "channel": "adjustment",
                "reason": "调整 assessment 不合规: " + "; ".join(errors),
                "next_action": "resubmit_with_valid_assessment",
                "review_retained": True,
                "assessment": assessment,
            }
        assessment = normalized
        verdict = verdict_text(assessment)
    approved = (verdict in APPROVAL_VERDICTS if verdict
                else approval_flag(approved))
    result = as_dict(_apply_approved_adjustment_impl(
        sd, review_id, approved, assessment))
    result.setdefault("reason", "")
    _emit_step_trace_safe("adjustment_apply", sd, result,
                          extra={"review_id": review_id, "approved": approved},
                          context="adjustment HTML 留痕失败")
    return result
def _apply_approved_adjustment_impl(
        sd: str, review_id: str, approved: bool,
        assessment: dict | None = None) -> dict:
    plan_file = adjustment_plan_path(sd)
    # 与 sync_adjustment_proposals/enqueue_adjustment_proposals 同口径持锁读改写：
    # 反哺入队与本裁决销项并发时，无锁写回会用陈旧 proposals 覆盖新入队建议。
    with locked_artifact(plan_file) as _adj_lock:
        if not _adj_lock:
            return {"status": "error",
                    "reason": "调整建议队列锁不可用，拒绝无锁读改写",
                    "next_action": "retry_adjustment_apply",
                    "review_retained": True}
        return _apply_adjustment_under_lock(
            sd, plan_file, review_id, approved, assessment)
def _apply_adjustment_under_lock(sd: str, plan_file: str, review_id: str,
                                 approved: bool,
                                 assessment: dict | None) -> dict:
    data = read_queue_json(plan_file, {})
    proposals = as_list(data.get("proposals"))
    target = find_pending_entry(proposals, "review_id", review_id)
    if target is None:
        return {"status": "error", "reason": f"未找到调整建议 {review_id}"}
    if not approved:
        assessment = as_dict(assessment)
        resolve_status = (
            "deferred" if verdict_text(assessment) == "defer" else "rejected")
        default_reason = (
            "AI 审核后暂缓处理" if resolve_status == "deferred"
            else "AI 判定不采纳")
        reason = (as_text(assessment.get("verdict_rationale")
                          or assessment.get("fp_evidence"))
                  or default_reason)
        _close_adjustment_proposal(
            plan_file, data, target, resolve_status, reject_reason=reason)
        logger.info("[AIReview] 调整建议已%s: %s",
                    "暂缓" if resolve_status == "deferred" else "拒绝", review_id)
        return {"status": resolve_status, "reason": reason}
    return _approve_adjustment_proposal(sd, plan_file, data, target, review_id)
def _approve_adjustment_proposal(sd: str, plan_file: str, data: dict,
                                 target: dict, review_id: str) -> dict:
    invalid_reason = _invalid_adjustment_reason(target)
    if invalid_reason:
        _close_adjustment_proposal(
            plan_file, data, target, "rejected", reject_reason=invalid_reason)
        logger.warning("[AIReview] 调整建议键位无效，已拒绝销项: %s", review_id)
        return {"status": "rejected", "reason": invalid_reason}
    kind = target["kind"]
    key = target["target"].strip()
    target["target"] = key
    val = _normalized_adjustment_value(kind, target[FIELD_SUGGESTED_VALUE])
    _write_approved_value(sd, kind, key, val)
    _close_adjustment_proposal(plan_file, data, target, "approved")
    logger.info("[AIReview] 调整建议已采纳生效: %s (%s)", review_id, kind)
    return {"status": "approved", "kind": kind, "target": key, "value": val}
def _invalid_adjustment_reason(target: dict) -> str:
    key = target.get("target", "")
    val = target.get(FIELD_SUGGESTED_VALUE)
    kind = target.get("kind", "")
    if ((not isinstance(key, str) or not key.strip())
            or val is None
            or not isinstance(kind, str) or not kind.strip()):
        return ("调整建议键位无效（target 缺失或空白、"
                "suggested_value 缺失或为 None、"
                "kind 缺失/非 str/空白），脏数据已拒绝销项")
    if kind not in _ADJUSTMENT_BUCKETS:
        return (f"调整建议 kind 不在生效域内（{kind!r}，合法值: "
                f"{'/'.join(sorted(_ADJUSTMENT_BUCKETS))}）——"
                "写入兜底桶不会被任何消费端读取，脏数据已拒绝销项")
    if kind in _ADJUSTMENT_NUMERIC_KINDS and safe_float(val, None) is None:
        return (f"调整建议数值无效（{kind!r} 须为有限数值或数值字符串，"
                "bool/NaN/文本会被消费端静默跳过），脏数据已拒绝销项")
    if (kind == "fixer_safety_override"
            and not (isinstance(val, dict) and "auto_safe" in val
                     and not signal_bool(val.get("auto_safe")))):
        return ("调整建议覆盖无效（fixer_safety_override 须为含 "
                "auto_safe=false 的对象，否则不会被任何消费端生效），"
                "脏数据已拒绝销项")
    return ""
def _write_approved_value(sd: str, kind: str, key: str, val) -> None:
    state = read_evolution_state(sd, for_update=True)
    approved_data = state.get("approved_adjustments")
    if approved_data is None:
        approved_data = _empty_approved_adjustments()
    if not isinstance(approved_data, dict):
        raise TypeError(
            "approved_adjustments section 顶层非对象"
            f"（{type(approved_data).__name__}），拒绝按默认值覆盖")
    bucket = _ADJUSTMENT_BUCKETS[kind]
    current_bucket = approved_data.get(bucket)
    if current_bucket is None:
        current_bucket = approved_data[bucket] = {}
    elif not isinstance(current_bucket, dict):
        raise TypeError(
            f"approved_adjustments.{bucket} 非对象"
            f"（{type(current_bucket).__name__}），拒绝按默认值覆盖")
    current_bucket[key] = val
    approved_data["last_updated"] = now_iso()
    if not write_evolution_section(sd, "approved_adjustments", approved_data):
        raise OSError(f"AI审核生效调整 section 落盘失败: {sd}")
def _close_adjustment_proposal(
        plan_file: str, data: dict, target: dict, status: str,
        reject_reason: str = "") -> None:
    target["status"] = status
    if status in ("rejected", "deferred"):
        target["reject_reason"] = as_text(reject_reason)[:200]
    data["proposals"] = prune_consumed_items(
        data["proposals"], MAX_ADJUSTMENT_PLANS)
    write_queue_json(plan_file, data)
_CHANNEL_SPECS = (
    ("treatment", collect_treatment_reviews, apply_treatment_verdict,
     _SHAPE_FS_ASM),
    ("feedback", collect_feedback_reviews, apply_feedback_verdict,
     _SHAPE_FS_ASM),
    ("enhancement", collect_enhancement_reviews, apply_enhancement_verdict,
     _SHAPE_FS_APPROVED_ASM),
    ("adjustment", collect_adjustment_reviews, apply_approved_adjustment,
     ("approved", "asm")),
    ("cleanup", collect_cleanup_reviews, apply_cleanup_verdict,
     _SHAPE_FS_APPROVED),
    ("cv_uncertain", collect_cv_uncertain_reviews, apply_cv_uncertain_review,
     ("asm", "approved")),
    ("security", collect_security_reviews, apply_security_verdict,
     _SHAPE_FS_APPROVED),
)
_assert_channel_specs_cover_contract()

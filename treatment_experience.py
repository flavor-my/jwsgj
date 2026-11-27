from __future__ import annotations

import logging
import os
import time
from collections.abc import Callable
from dataclasses import dataclass
from typing import NamedTuple

from jwsgj.ai_review_queue import (
    apply_step_fp_prefilter,
    partition_fp_prefiltered,
)
from jwsgj.build_contract import (
    TREATMENT_CONTRACT,
    requires_contract,
)
from jwsgj.diag_types_normalize import (
    as_str,
    coerce_line,
    dict_or_empty,
    elapsed_seconds,
    finite_float_or_none,
    list_field,
    parse_locator_line,
    plan_index,
    str_or,
)
from jwsgj.fix_safety_gate import (
    _REGRESSION_VERIFIED_STATUSES,
    AafCtx,
    _enforce_session_write_budget,
    rollback_unverified_fix,
    run_fix_verify_chain,
    run_post_write_hallucination_check,
    write_fix_file,
)
from jwsgj.html_render_pipeline import emit_ai_fix_trace
from jwsgj.log_config import (
    log_swallowed,
    perf_trace,
    safe_write_audit,
    timed_log,
    write_module_run,
)
from jwsgj.runtime_scope import (
    resolve_finding_file_path,
    resolve_skill_relative_path,
)
from jwsgj.testsuite_runner import (
    locate_targeted_tests,
    run_post_write_regression,
)
from jwsgj.treatment_evidence import (
    CvContextIndex,
    build_diagnosis_evidence,
    default_regression_plan,
    extract_code_context,
    find_diag_snippet,
    get_summary_cache_stats,
    plan_fix_knowledge,
    plan_single_fix,
    revalidate_finding_line,
    summarize_function_at_line,
)
from jwsgj.treatment_state import (
    FixRecord,
    check_treatment_zero_leftover,
    item_index,
    item_result,
    item_result_reason,
    item_status,
    load_fix_target,
    load_treatment_fix_plans,
    load_treatment_state,
    locate_treatment_item,
    normalize_item_severity,
    normalize_rule_key,
    parse_locator_rule_family,
    query_fix_experience,
    record_fix_experience,
    record_fix_result,
    record_treatment_fix_plan,
    rule_id_of,
    save_treatment_state,
    treatment_items_integrity,
    treatment_progress,
    update_treatment_item_state,
)

logger = logging.getLogger(__name__)
DEFAULT_AI_FIX_DRY_RUN = True
__all__ = [
    "DEFAULT_AI_FIX_DRY_RUN",
    "FixBackendResult",
    "apply_ai_fix",
    "brief_fix_experience",
    "build_fix_step_out",
    "evaluate_zero_leftover",
    "execute_treatment_item_core",
    "get_ai_fix_candidates",
    "preview_targeted_tests",
    "record_item_failure",
    "run_ai_manual_fix",
    "run_fix_backend",
    "verify_treatment_zero_leftover",
]
def _experience_confidence(record) -> float:
    if not isinstance(record, dict):
        return 0.0
    score = finite_float_or_none(record.get("confidence", 0))
    return 0.0 if score is None else score
def brief_fix_experience(skill_dir: str, rule_id: str,
                         code_context: str) -> list[dict]:
    code_context = str_or(code_context, "")
    try:
        rid = normalize_rule_key(rule_id)
        experiences = query_fix_experience(
            skill_dir, rid, code_snippet=code_context)
        if not experiences:
            experiences = query_fix_experience(skill_dir, rid)
        experiences = sorted(
            (e for e in experiences if isinstance(e, dict)),
            key=_experience_confidence, reverse=True)
    except Exception as e:
        logger.debug("[AIManualFix] 历史修复经验查询失败(不影响主流程): %s", e)
        return []
    return [
        {
            "old_snippet": exp.get("old_snippet", ""),
            "new_snippet": exp.get("new_snippet", ""),
            "description": exp.get("description", ""),
            "confidence": _experience_confidence(exp),
            "success_count": exp.get("success_count", 0),
        }
        for exp in experiences[:3]
    ]
_LOG_SUMMARY_MAX_CHARS = 150
@dataclass(frozen=True)
class _FixOutcome:
    verify: dict
    targeted_regression: dict
    backup_path: str
    hallucination_api_findings: list
    start_time: float
def apply_ai_fix(skill_dir: str, index: int, fixed_source: str,
                 description: str = "", *,
                 expected_original: str | None = None) -> dict:
    """应用一项 AI 手动修复（逐项 7 道门禁 + 失败自动回滚）。

    ``expected_original``：批量场景的**乐观并发校验**。
    ``fixed_source`` 是整份文件内容，若它是基于旧快照生成的，写入会
    **静默回退**此前已应用的修复，而 ``write_fix_file`` 自带的一致性
    守卫只在单次调用内比较（两侧都是本次刚读的新鲜快照），拦不住。
    传入``expected_original``后，只要磁盘现状与快照不一致就直接拒绝，
    强制调用方重新基于最新内容生成。
    """
    try:
        result = _apply_ai_fix_impl(
            skill_dir, index, fixed_source, description,
            expected_original=expected_original)
    except Exception as _impl_err:
        logger.exception(
            "[AIManualFix] apply_ai_fix 内部异常(兜底转 error 终态)")
        return _error_result(
            f"AI 修复执行内部异常: "
            f"{type(_impl_err).__name__}: {_impl_err}")
    if isinstance(result, dict):
        return result
    logger.error("[AIManualFix] apply_ai_fix 返回形态异常(%s)，归一为 error 终态",
                 type(result).__name__)
    return _error_result(
        f"AI 修复返回值形态异常: {type(result).__name__}")
_BATCH_APPLIED_STATUSES = frozenset({"ai_fixed"})


def apply_ai_fix_batch(skill_dir: str, fixes: list, *,
                       max_items: int | None = None,
                       stop_on_failure: bool = False) -> dict:
    """批量应用 AI 手动修复（同文件串行、逐项完整门禁）。

    ``fixes`` 每项：``{"index": int, "fixed_source": str,
    "description": str, "expected_original": str | None}``。

    质量契约（批量不降质）：
    - 每一项都走 ``apply_ai_fix`` 完整门禁链：备份 → 写盘 → 写后幻觉
      API 校验 → L1 语法 / L2 导入 / L3 定向测试 / L4 运行时 → 定向回归
      → 会话预算门 → 落账；任一步失败自动回滚原码；
    - 同一文件多项**必须串行**，后一项的 ``fixed_source`` 应基于前一项
      结果生成；传 ``expected_original`` 时由乐观并发校验强制拒绝陈旧
      快照，避免静默回退此前已应用的修复；
    - 单项失败默认不中断整批（``stop_on_failure=True`` 时中途停）。

    返回：``{status, total, applied, failed, results}``。
    """
    items = [dict(spec) for spec in (fixes or [])
             if isinstance(spec, dict)]
    if max_items is not None:
        try:
            items = items[:max(0, int(max_items))]
        except (TypeError, ValueError):
            logger.warning("[AIManualFix] max_items 非法，按不限制处理: %r",
                           max_items)
    results: list[dict] = []
    applied = 0
    for seq, spec in enumerate(items):
        try:
            index = int(spec.get("index"))
        except (TypeError, ValueError):
            results.append({"seq": seq, "status": "error",
                            "reason": "index 非整数"})
            continue
        fixed_source = spec.get("fixed_source")
        if not isinstance(fixed_source, str) or not fixed_source:
            results.append({"seq": seq, "index": index,
                            "status": "error",
                            "reason": "fixed_source 为空"})
            continue
        expected = spec.get("expected_original")
        outcome = apply_ai_fix(
            skill_dir, index, fixed_source,
            str(spec.get("description") or ""),
            expected_original=(expected
                               if isinstance(expected, str) else None))
        status = str(outcome.get("status") or "unknown")
        results.append({"seq": seq, "index": index, "status": status,
                        "reason": str(outcome.get("reason") or "")[:300]})
        if status in _BATCH_APPLIED_STATUSES:
            applied += 1
        elif stop_on_failure:
            logger.warning(
                "[AIManualFix] 批量修复中途停: seq=%d index=%d status=%s",
                seq, index, status)
            break
    return {"status": "ok", "total": len(items), "applied": applied,
            "failed": len(results) - applied, "results": results}


@requires_contract(TREATMENT_CONTRACT)
def _apply_ai_fix_impl(skill_dir: str, index: int, fixed_source: str,
                       description: str, *,
                       expected_original: str | None = None) -> dict:
    _aaf_start = time.monotonic()
    target = load_fix_target(skill_dir, index, description)
    if target.error:
        return _error_result(target.error)
    if (expected_original is not None
            and target.original_source != expected_original):
        reason = ("fixed_source 已陈旧：磁盘内容与生成时的基线不一致，"
                  "强行写入会静默回退此前已应用的修复；"
                  "请基于最新文件内容重新生成 fixed_source 后重试")
        logger.warning("[AIManualFix] %s: %s", reason, target.file_path)
        return _error_result(reason)
    integrity_ok, integrity_reason = treatment_items_integrity(target.state)
    if _is_corrupt_state(target.state) or not integrity_ok:
        _state_reason = ("治疗状态完整性异常（status=error/items 容器撕裂），"
                         "拒绝 AI 写盘以免覆盖损坏状态文件: "
                         f"{integrity_reason or '状态文件不可信'}")
        logger.error("[AIManualFix] %s", _state_reason)
        return _error_result(_state_reason)
    ctx = AafCtx(
        skill_dir=skill_dir, index=target.index, item=target.item,
        file_path=target.file_path, fixed_source=fixed_source,
        original_source=target.original_source,
        description=target.description)
    reject, verify = run_fix_verify_chain(ctx)
    if reject:
        _record_failed_fix(ctx)
        return reject
    reject, backup_path = write_fix_file(
        ctx, verify["safety_ok"],
        original_bytes=target.original_bytes,
        source_encoding=target.source_encoding,
        on_content_failure=_record_failed_fix)
    if reject:
        return reject
    hallucination_api_findings, post_write_failure = (
        _aaf_post_write_hallucination_gate(ctx))
    if post_write_failure is not None:
        return _aaf_rollback_rejected_write(
            ctx, backup_path, target.state, post_write_failure,
            original_bytes=target.original_bytes,
            source_encoding=target.source_encoding)
    reject, targeted_regression = _aaf_targeted_regression(
        ctx, backup_path, target.state,
        original_bytes=target.original_bytes,
        source_encoding=target.source_encoding)
    if reject:
        return reject
    reject = _aaf_session_budget_gate(
        ctx, backup_path, target.state,
        original_bytes=target.original_bytes,
        source_encoding=target.source_encoding)
    if reject:
        return reject
    try:
        return _finalize_fix_success(
            ctx, target.state,
            _FixOutcome(
                verify=verify,
                targeted_regression=targeted_regression,
                backup_path=backup_path,
                hallucination_api_findings=hallucination_api_findings,
                start_time=_aaf_start,
            ))
    except Exception as exc:
        logger.warning("[AIManualFix] 成功结果落账异常，转入回滚: %s",
                       exc, exc_info=True)
        summary = f"修复成功结果落账异常: {type(exc).__name__}: {exc}"
        return _aaf_rollback_rejected_write(
            ctx, backup_path, target.state,
            {
                "status": "error",
                "stage": "finalize_success",
                "verdict_label": "修复成功结果落账未通过",
                "summary": summary,
                "error": str(exc)[:500],
            },
            original_bytes=target.original_bytes,
            source_encoding=target.source_encoding)
def _error_result(reason: str) -> dict:
    return {"status": "error", "reason": reason,
            "regression_verified": False}
def _aaf_post_write_hallucination_gate(
    ctx: AafCtx,
) -> tuple[list, dict | None]:
    try:
        findings = run_post_write_hallucination_check(
            ctx, record_budget=False)
        if not isinstance(findings, list):
            raise TypeError(
                "写后幻觉校验返回形态异常: "
                f"{type(findings).__name__}")
    except Exception as exc:
        logger.warning("[AIManualFix] 写后幻觉校验异常，转入回滚: %s",
                       exc, exc_info=True)
        return [], {
            "status": "error", "stage": "post_write_hallucination",
            "verdict_label": "写后幻觉API校验未获通过结论",
            "summary": f"写后幻觉API校验异常: {type(exc).__name__}: {exc}",
            "error": str(exc)[:500],
        }
    if findings:
        summary = (f"写后幻觉API复检发现 {len(findings)} 个"
                   f"新引入的疑似不存在API调用")
        return findings, {
            "status": "failed", "stage": "post_write_hallucination",
            "verdict_label": "写后幻觉API复检未通过",
            "summary": summary, "error": summary,
            "hallucination_api_findings": findings,
        }
    return findings, None
def _aaf_rollback_rejected_write(
    ctx: AafCtx, backup_path: str, state: dict, failure: dict, *,
    original_bytes: bytes | None, source_encoding: str,
) -> dict:
    rollback_ok = rollback_unverified_fix(
        ctx, backup_path, original_bytes=original_bytes,
        source_encoding=source_encoding)
    return _finalize_rolled_back(
        ctx, state, backup_path, failure, rollback_ok)
def _aaf_targeted_regression(ctx: AafCtx, backup_path: str,
                             state: dict, *,
                             original_bytes: bytes | None,
                             source_encoding: str
                             ) -> tuple[dict | None, dict]:
    try:
        regression = run_post_write_regression(ctx.skill_dir, ctx.file_path)
    except Exception as exc:
        logger.warning("[AIManualFix] 定向回归执行异常，转入回滚: %s",
                       exc, exc_info=True)
        regression = {
            "status": "error",
            "summary": f"定向回归执行异常: {type(exc).__name__}: {exc}",
            "error": str(exc)[:500],
        }
    if not isinstance(regression, dict):
        regression = {
            "status": "error",
            "summary": ("定向回归返回形态非法: "
                        f"{type(regression).__name__}"),
        }
    if regression.get("status") in _REGRESSION_VERIFIED_STATUSES:
        return None, regression
    regression.setdefault("stage", "targeted_regression")
    reject = _aaf_rollback_rejected_write(
        ctx, backup_path, state, regression, original_bytes=original_bytes,
        source_encoding=source_encoding)
    return reject, regression
def _aaf_session_budget_gate(ctx: AafCtx, backup_path: str,
                             state: dict, *,
                             original_bytes: bytes | None,
                             source_encoding: str) -> dict | None:
    try:
        _enforce_session_write_budget(ctx)
    except Exception as exc:
        logger.warning("[AIManualFix] 会话预算未通过，转入回滚: %s",
                       exc, exc_info=True)
        summary = (f"会话写盘预算未获通过结论: "
                   f"{type(exc).__name__}: {exc}")
        return _aaf_rollback_rejected_write(
            ctx, backup_path, state,
            {
                "status": "error",
                "stage": "session_budget",
                "verdict_label": "会话写盘预算未通过",
                "summary": summary,
                "error": str(exc)[:500],
            },
            original_bytes=original_bytes,
            source_encoding=source_encoding)
    return None
def _finalize_rolled_back(ctx: AafCtx, state: dict, backup_path: str,
                          regression: dict, rollback_ok: bool) -> dict:
    final_status = "rolled_back" if rollback_ok else "failed"
    _, persist_warning, _ = record_fix_result(
        ctx.skill_dir, state,
        FixRecord(
            skill_dir=ctx.skill_dir, index=ctx.index, item=ctx.item,
            file_path=ctx.file_path, description=ctx.description,
            status=final_status, targeted_regression=regression,
            backup_path=backup_path, side_effects=ctx.side_effects,
            original_source=ctx.original_source,
            fixed_source=ctx.fixed_source, success=False,
            plan_payload={
                "targeted_regression": regression.get("summary", ""),
                "failure_stage": regression.get("stage", "targeted_regression"),
            },
            context_label="回滚已生效"))
    rollback_reason_extra = ("；治疗状态落盘失败，状态文件可能不同步"
                             "(人工介入核对)") if persist_warning else ""
    _summary = str(regression.get("summary", ""))[:_LOG_SUMMARY_MAX_CHARS]
    _status = str(regression.get("status") or "unknown")
    _verdict = str(regression.get("verdict_label") or (
        "定向回归失败" if _status == "failed"
        else f"定向回归未获验证结论(status={_status})"))
    safe_write_audit("ai_fix_rolled_back", index=ctx.index, file=ctx.file_path,
                     reason=f"{_verdict}: {_summary}")
    reason = (f"{_verdict}已回滚恢复原码: {_summary}"
              if rollback_ok else
              f"{_verdict}且回滚写盘失败(人工介入): {_summary}") + rollback_reason_extra
    return {"status": "rejected" if rollback_ok else "failed",
            "reason": reason,
            "regression_verified": False,
            "targeted_regression": regression,
            "failure_stage": regression.get("stage", "targeted_regression"),
            "rolled_back": rollback_ok}
def _finalize_fix_success(ctx: AafCtx, state: dict,
                          outcome: _FixOutcome) -> dict:
    skill_dir, index, item = ctx.skill_dir, ctx.index, ctx.item
    verify = outcome.verify
    targeted_regression = outcome.targeted_regression
    hallucination_api_findings = outcome.hallucination_api_findings
    regression_verified = verify["regression_verified"]
    file_path = ctx.file_path
    _, state_save_warning, fix_result_path = record_fix_result(
        skill_dir, state,
        FixRecord(
            skill_dir=skill_dir, index=index, item=item,
            file_path=file_path, description=ctx.description,
            status="ai_fixed", targeted_regression=targeted_regression,
            backup_path=outcome.backup_path, side_effects=ctx.side_effects,
            original_source=ctx.original_source,
            fixed_source=ctx.fixed_source, success=True,
            plan_payload={"applied_description": ctx.description or "AI 手动修复"},
            write_artifact=True,
            extras={
                "regression_verified": regression_verified,
                "inline_verification": verify["inline_verification"],
                "behavior_regression": verify["behavior_regression"],
                "diag_regression": verify["diag_regression"],
            }))
    if state_save_warning:
        raise RuntimeError(
            "治疗状态未可靠落盘，拒绝保留无状态背书的源码修改: "
            f"{state_save_warning}")
    _rule_id = rule_id_of(item)
    logger.info("[AIManualFix] 应用 AI 修复成功: index=%d rule=%s", index, _rule_id)
    safe_write_audit("ai_fix_applied", index=index, file=file_path,
                     rule_id=_rule_id, description=ctx.description)
    perf_trace("ai_manual_fix",
                    round((time.monotonic() - outcome.start_time) * 1000, 1),
                    index=index, file=file_path, status="ai_fixed")
    return {"status": "ai_fixed", "reason": "AI 手动修复已应用",
            "regression_verified": regression_verified,
            "inline_verification": verify["inline_verification"],
            "behavior_regression": verify["behavior_regression"],
            "diag_regression": verify["diag_regression"],
            "targeted_regression": targeted_regression,
            "hallucination_api_findings": hallucination_api_findings,
            **({"state_save_warning": state_save_warning}
               if state_save_warning else {}),
            "backup": outcome.backup_path,
            "fix_result_path": fix_result_path}
def _record_failed_fix(ctx: AafCtx) -> None:
    record_fix_experience(
        ctx.skill_dir, ctx.item, ctx.original_source, ctx.fixed_source,
        ctx.description, success=False, file_path=ctx.file_path)
logger.info("treatment_experience AI修复结果与经验域已加载: %d 项导出", len(__all__))
def _refresh_changed_file_candidate(skill_dir: str, cand: dict) -> dict | None:
    refreshed = get_ai_fix_candidates(skill_dir, brief_fix_experience)
    if refreshed.get("state_integrity") == "torn":
        raise RuntimeError(refreshed.get("state_integrity_reason", "治疗状态撕裂"))
    return next(
        (current for current in refreshed.get("candidates", [])
         if isinstance(current, dict)
         and current.get("index") == cand.get("index")
         and current.get("file_path") == cand.get("file_path")),
        None,
    )
def run_ai_manual_fix(skill_dir: str, llm_call_fn: Callable | None = None,
                      dry_run: bool = DEFAULT_AI_FIX_DRY_RUN) -> dict:
    try:
        result = get_ai_fix_candidates(skill_dir, brief_fix_experience)
        candidates = result["candidates"]
        if result.get("state_integrity") == "torn":
            return _batch_report(
                "error", 0, items=[],
                reason=result.get("state_integrity_reason", ""))
    except Exception as e:
        logger.warning("[AIManualFix] 候选装配失败(治疗状态可能撕裂): %s",
                       e, exc_info=True)
        return _batch_report(
            "error", 0, items=[],
            reason=f"候选装配失败(治疗状态可能撕裂，人工介入核对): {str(e)[:200]}")
    total = len(candidates)
    if llm_call_fn is None or dry_run:
        return _batch_report(
            "preview", total,
            message=("预览模式：候选已纯内存导出（见 candidates 字段）；"
                     "待 AI 审核并执行相关操作（生成 fixed_source 后调 apply_ai_fix 写盘）"),
            candidates=candidates)
    counts = {"applied": 0, "rejected": 0, "failed": 0}
    report = []
    changed_files = set()
    for cand in candidates:
        try:
            cand_file = cand.get("file_path") if isinstance(cand, dict) else ""
            if cand_file and cand_file in changed_files:
                current = _refresh_changed_file_candidate(skill_dir, cand)
                if current is None:
                    counts["rejected"] += 1
                    report.append({
                        "index": cand.get("index", -1), "status": "skipped",
                        "reason": "同文件前序修复后候选已失效，未使用陈旧修复方案",
                    })
                    continue
                cand = current
            _outcome = _fix_one_candidate(skill_dir, cand, llm_call_fn)
        except Exception as e:
            logger.debug("[AIManualFix] 批量修复单候选异常(标记error后继续): %s", e)
            counts["failed"] += 1
            _cand_index = cand.get("index", -1) if isinstance(cand, dict) else -1
            report.append({"index": _cand_index, "status": "error",
                           "reason": str(e)[:200]})
            continue
        counts[_outcome["class"]] += 1
        report.append(_outcome["entry"])
        if _outcome["entry"].get("rolled_back") is False:
            return _batch_report(
                "error", total, counts, items=report,
                reason=("修复回滚写盘失败，已停止后续候选执行；"
                        "需人工介入核对源码与治疗状态"))
        if _outcome["class"] == "applied":
            applied_file = cand.get("file_path") if isinstance(cand, dict) else ""
            if applied_file:
                changed_files.add(applied_file)
    return _batch_report("completed", total, counts, items=report)
def _llm_fix_plan(llm_result) -> tuple[str | None, str, str | None]:
    if not isinstance(llm_result, dict):
        if llm_result:
            return None, "", ("LLM 未返回修复方案"
                              f"（返回形态异常: {type(llm_result).__name__}）")
        return None, "", "LLM 未返回修复方案"
    fixed_src = llm_result.get("fixed_source")
    if fixed_src is None or fixed_src == "":
        return None, "", "LLM 未返回修复方案"
    if not isinstance(fixed_src, str):
        return None, "", ("LLM 修复方案形态异常"
                          f"（fixed_source: {type(fixed_src).__name__}，"
                          "须为 str）")
    if not fixed_src.strip():
        return None, "", "LLM 未返回修复方案"
    return fixed_src, str_or(llm_result.get("description"), ""), None
def _emit_fix_trace_safe(skill_dir: str, index: int,
                         fix_result: dict) -> None:
    try:
        emit_ai_fix_trace(skill_dir, index, fix_result)
    except Exception as _trace_err:
        log_swallowed(
            __name__, _trace_err,
            context=f"emit_ai_fix_trace:{type(_trace_err).__name__}")
        logger.warning("[AIManualFix] 修复留痕失败(不影响修复结论): %s",
                       _trace_err)
def _fix_one_candidate(skill_dir: str, cand, llm_call_fn: Callable) -> dict:
    llm_result = llm_call_fn(cand)
    fixed_src, description, _reject_reason = _llm_fix_plan(llm_result)
    if _reject_reason is not None:
        return {"class": "rejected",
                "entry": {"index": cand["index"], "status": "skipped",
                          "reason": _reject_reason}}
    fix_result = apply_ai_fix(
        skill_dir, cand["index"],
        fixed_src,
        description,
    )
    _emit_fix_trace_safe(skill_dir, cand["index"], fix_result)
    _status = fix_result["status"]
    if _status == "ai_fixed":
        _cls = "applied"
    elif _status in ("failed", "error"):
        _cls = "failed"
    else:
        _cls = "rejected"
    entry = {"index": cand["index"], "status": _status,
             "reason": fix_result.get("reason", "")}
    if "rolled_back" in fix_result:
        entry["rolled_back"] = fix_result["rolled_back"]
    return {"class": _cls, "entry": entry}
_BATCH_OUTCOME_KEYS: tuple[str, ...] = ("applied", "rejected", "failed")
def _batch_report(status: str, total: int, counts: dict | None = None,
                  **extra) -> dict:
    report = {"status": status, "total_candidates": total}
    for key in _BATCH_OUTCOME_KEYS:
        report[key] = (counts or {}).get(key, 0)
    report.update(extra)
    return report
def _extract_rule_family(item: dict, result: dict) -> str:
    cv_ctx = item.get("cv_context")
    raw_finding = item.get("raw_finding")
    candidates = (
        cv_ctx.get("rule_family") if isinstance(cv_ctx, dict) else "",
        parse_locator_rule_family(item.get("locator")),
        raw_finding.get("rule_family") if isinstance(raw_finding, dict) else "",
        result.get("rule_family"),
    )
    for candidate in candidates:
        text = str_or(candidate, "")
        if text:
            return text
    return ""
def _group_fix_plans_by_index(plans: list) -> dict[int, dict]:
    plans_by_index: dict[int, dict] = {}
    for plan in plans:
        if isinstance(plan, dict):
            _pi = plan_index(plan.get("index"))
            if _pi is not None:
                plans_by_index[_pi] = plan
    return plans_by_index
def _group_treatment_history_by_index(state: dict) -> dict:
    history_by_index: dict[int, list[dict]] = {}
    raw_details = state.get("item_details")
    if isinstance(raw_details, list):
        for detail in raw_details:
            if not isinstance(detail, dict):
                continue
            idx = plan_index(detail.get("index"))
            if idx is None or idx < 0:
                continue
            history_by_index.setdefault(idx, []).append(
                {"status": str_or(detail.get("status"), ""),
                 "reason": _history_reason(detail.get("detail"))})
    return history_by_index
def _history_reason(detail) -> str:
    if isinstance(detail, dict):
        reason = str_or(detail.get("reason"), "") or str_or(detail.get("error"), "")
        if not reason:
            regression = detail.get("targeted_regression")
            if isinstance(regression, dict):
                reason = (str_or(regression.get("summary"), "")
                          or str_or(regression.get("error"), ""))
    elif detail:
        reason = str(detail)
    else:
        reason = ""
    return reason[:200]
def preview_targeted_tests(skill_dir: str, file_path: str,
                          regression_plan: dict) -> None:
    resolved_path = (resolve_finding_file_path(str(file_path), skill_dir)
                     if file_path else "")
    if not (resolved_path
            and os.path.splitext(resolved_path)[1].lower() == ".py"
            and os.path.isfile(resolved_path)):
        return
    try:
        tests, mode = locate_targeted_tests(skill_dir, resolved_path)
    except Exception as _loc_err:
        logger.debug("[AIManualFix] 定向回归预览定位异常(不阻断): %s", _loc_err)
        return
    if tests:
        regression_plan["preview_tests"] = tests[:10]
        regression_plan["preview_mode"] = mode
def _resolve_candidate_fix_plan(skill_dir: str, cand: dict, item: dict,
                                plans_by_index: dict,
                                code_snippet: str) -> dict:
    idx, file_path = cand["index"], cand["file_path"]
    plan = plans_by_index.get(idx)
    if isinstance(plan, dict):
        plan = dict(plan)
    else:
        plan = _generate_fallback_plan(item, cand, code_snippet)
    _ensure_regression_plan(plan, file_path)
    preview_targeted_tests(skill_dir, file_path, plan["regression_plan"])
    return plan
def _generate_fallback_plan(item: dict, cand: dict, code_snippet: str) -> dict:
    plan = plan_single_fix(
        {
            "rule_id": cand["rule_id"],
            "message": (str_or(item.get("sample_message"), "")
                        or str_or(item.get("message"), "")),
            "code_snippet": code_snippet,
            "severity": cand["severity"],
            "line": cand["line"],
            "locator": str_or(item.get("locator"), ""),
            "raw_finding": item.get("raw_finding"),
        },
        cand["file_path"],
    )
    plan["index"] = cand["index"]
    return plan
def _ensure_regression_plan(plan: dict, file_path: str) -> None:
    plan["regression_plan"] = default_regression_plan(
        file_path, plan.get("regression_plan"))
@dataclass(frozen=True)
class _CandidateFields:
    index: int
    rule_id: str
    severity: str
    file_path: str
    line: int
    message: str
    code_snippet: str
    status: str
    result: dict
@dataclass(frozen=True)
class _CandidateContext:
    cv_index: CvContextIndex
    plans_by_index: dict
    history_by_index: dict
    experience_brief: Callable[..., list] | None = None
def _item_finding_line(item: dict) -> int:
    """治疗项 finding 行号：line 缺失/为 0 时回退解析 locator。

    候选装配与实际治疗 finding 必须对同一治疗项得到相同行号，
    否则 AI 审核候选 line=0 会丢失 code_context/function_summary。
    """
    _line = coerce_line(item.get("line", 0))
    if _line == 0 and item.get("locator"):
        _line = parse_locator_line(item["locator"])
        if _line <= 0:
            logger.debug("[TreatmentStep] locator行号解析失败: %s",
                         item.get("locator", ""))
    return _line
def _item_finding_message(item: dict, result: dict) -> str:
    """候选描述取 finding 原文（message 为入库时折叠的 sample_message）。

    result.reason 在 planned 态是规划备注（"已生成修复方案…"）、failed 态
    是失败原因，二者已由 treatment_history 单独传给审核方，不得占用
    finding 描述位；仅在治疗项没有 finding 原文时回退。
    """
    _message = (str_or(item.get("sample_message"), "")
                or str_or(item.get("message"), ""))
    return _message if _message.strip() else item_result_reason(item, result)
def _normalize_candidate_fields(item: dict, skill_dir: str,
                                 status: str, fallback_index: int
                                 ) -> _CandidateFields:
    result = item_result(item)
    return _CandidateFields(
        index=item_index(item, fallback_index),
        rule_id=str_or(item.get("rule_id"), ""),
        severity=normalize_item_severity(item.get("severity")),
        file_path=resolve_skill_relative_path(
            str_or(item.get("file_path"), ""), skill_dir),
        line=_item_finding_line(item),
        message=_item_finding_message(item, result),
        code_snippet=str_or(item.get("code_snippet"), ""),
        status=status,
        result=result,
    )
def _assemble_candidate(skill_dir: str, item: dict, status: str,
                        ctx: _CandidateContext,
                        fallback_index: int) -> dict:
    f = _normalize_candidate_fields(item, skill_dir, status, fallback_index)
    function_summary = summarize_function_at_line(f.file_path, f.line)
    code_context = extract_code_context(
        f.file_path, f.line, severity=f.severity,
        function_summary=function_summary)
    cand = {
        "index": f.index,
        "rule_id": f.rule_id,
        "strategy": str_or(item.get("strategy"), ""),
        "severity": f.severity,
        "file_path": f.file_path,
        "line": f.line,
        "message": f.message,
        "orig_status": f.status,
        "code_context": code_context,
        "function_summary": function_summary,
        **plan_fix_knowledge(f.rule_id, f.message, f.code_snippet),
        "fix_experience": (ctx.experience_brief or brief_fix_experience)(
            skill_dir, f.rule_id, code_context),
        "cv_context": ctx.cv_index.match(
            f.file_path, f.line, _extract_rule_family(item, f.result)),
        "diagnosis_evidence": build_diagnosis_evidence(
            item, f.code_snippet),
    }
    cand["fix_plan"] = _resolve_candidate_fix_plan(
        skill_dir, cand, item, ctx.plans_by_index, f.code_snippet)
    _hist = ctx.history_by_index.get(f.index) or []
    if _hist:
        cand["treatment_history"] = _hist[-5:]
    return cand
def get_ai_fix_candidates(skill_dir: str,
                          experience_brief: Callable[..., list] | None = None) -> dict:
    state = load_treatment_state(skill_dir)
    integrity_ok, integrity_reason = treatment_items_integrity(state)
    if not integrity_ok:
        logger.warning("[AIManualFix] 候选导出受阻: %s", integrity_reason)
        return {
            "total_candidates": 0,
            "candidates": [],
            "fp_filtered": 0,
            "fp_enqueued": 0,
            "summary_cache": get_summary_cache_stats().to_dict(),
            "state_integrity": "torn",
            "state_integrity_reason": integrity_reason,
        }
    items = list_field(state, "items")
    cv_index = CvContextIndex.load(skill_dir)
    plans_by_index = _group_fix_plans_by_index(
        load_treatment_fix_plans(skill_dir))
    history_by_index = _group_treatment_history_by_index(state)
    candidates, fp_filtered, fp_enqueued = _collect_candidates(
        skill_dir, state, items,
        _CandidateContext(cv_index, plans_by_index, history_by_index,
                          experience_brief))
    if fp_filtered > 0:
        try:
            save_treatment_state(skill_dir, state)
        except Exception as _fp_save_err:
            log_swallowed(
                __name__, _fp_save_err,
                context=f"get_ai_fix_candidates:{type(_fp_save_err).__name__}")
            logger.warning(
                "[AIManualFix] FP预过滤状态落盘失败(降级): 本轮仍按内存结果导出"
                " %d 项，下一轮将重新预过滤: %s", fp_filtered, _fp_save_err)
        logger.info("[AIManualFix] FP预过滤: %d 项自动标记为fp_confirmed（%d 项已入队AI复核），剩余 %d 项候选", fp_filtered, fp_enqueued, len(candidates))
    summary_cache = get_summary_cache_stats().to_dict()
    logger.info("[AIManualFix] 导出 AI 修复候选 %d 项 (FP预过滤 %d 项)",
                len(candidates), fp_filtered)
    return {
        "total_candidates": len(candidates),
        "candidates": candidates,
        "fp_filtered": fp_filtered,
        "fp_enqueued": fp_enqueued,
        "summary_cache": summary_cache,
        "state_integrity": "ok",
        "state_integrity_reason": integrity_reason,
    }
def _collect_candidates(skill_dir: str, state: dict, items: list,
                        ctx: _CandidateContext) -> tuple[list, int, int]:
    partition = partition_fp_prefiltered(skill_dir, state, items)
    candidates = [
        _assemble_candidate(skill_dir, item, status, ctx, position)
        for position, item, status in partition.kept
    ]
    return candidates, partition.filtered, partition.enqueued
def verify_treatment_zero_leftover(skill_dir: str) -> dict:
    try:
        leftover = dict_or_empty(check_treatment_zero_leftover(skill_dir))
    except Exception as _le:
        logger.warning("[Stage4b] 零遗留门禁核验异常: %s", _le)
        return {"passed": False, "error": str(_le)[:500],
                "state_integrity": "error"}
    verdict = leftover.get("passed")
    if not isinstance(verdict, bool):
        _reason = ("零遗留门禁未返回裁决(passed)布尔值"
                   f"，实际裁决形态: {type(verdict).__name__}")
        logger.warning("[Stage4b] %s，保守阻塞", _reason)
        return {"passed": False, "error": _reason[:500],
                "state_integrity": "error",
                "state_integrity_reason": _reason}
    if leftover.get("state_integrity") == "torn":
        logger.warning("[Stage4b] 治疗状态撕裂，零遗留无法核验，保守阻塞: %s",
                       leftover.get("state_integrity_reason", ""))
        return {**leftover, "passed": False}
    return leftover
class FixBackendResult(NamedTuple):
    task_result: dict
    applied: int
    rejected: int
    failed: int
    status: str
    executed: bool
@timed_log("stage_ai_manual_fix")
def run_fix_backend(sd: str, llm_call_fn: Callable | None,
                     dry_run: bool) -> FixBackendResult:
    executed = llm_call_fn is not None and not dry_run
    task_result = run_ai_manual_fix(
        sd, llm_call_fn=llm_call_fn, dry_run=dry_run)
    if executed:
        return FixBackendResult(
            task_result,
            task_result.get("applied", 0),
            task_result.get("rejected", 0),
            task_result.get("failed", 0),
            task_result.get("status", "completed"),
            True)
    return FixBackendResult(task_result, 0, 0, 0,
                             task_result.get("status", "preview"), False)
def _is_actionable_item(item: object) -> bool:
    return not isinstance(item, dict) or item_status(item) == "pending"
def _first_actionable_index(items: list) -> int | None:
    return next(
        (item_index(item, position) if isinstance(item, dict) else position
         for position, item in enumerate(items) if _is_actionable_item(item)),
        None,
    )
def _is_corrupt_state(state: dict) -> bool:
    return isinstance(state, dict) and state.get("status") == "error"
def _valid_index(index: int, items: list) -> bool:
    return 0 <= index < len(items)
def _precheck_explicit_item(
    item: object, item_index: int, stage_start: float,
) -> dict | None:
    if not isinstance(item, dict):
        return {"status": "skipped", "index": item_index,
                "item_status": "invalid_entry",
                "reason": "治疗项非 dict 脏条目（invalid_entry），"
                          "须人工修复，详见零遗留门禁",
                "elapsed_s": elapsed_seconds(stage_start)}
    status = item_status(item)
    if status != "pending":
        return {"status": "skipped", "index": item_index,
                "item_status": status,
                "reason": "状态非pending，可能已在其他会话中执行",
                "elapsed_s": elapsed_seconds(stage_start)}
    return None
def _no_more_items_result(sd: str) -> dict:
    return {"status": "no_more_items",
            "message": "无待执行治疗项",
            "progress": treatment_progress(load_treatment_state(sd))}
def _self_heal_contradiction(state: dict, items: list, sd: str) -> dict | None:
    _st = state.get("status", "")
    if _st not in ("no_plan", "completed"):
        return None
    if not any(_is_actionable_item(_it) for _it in items):
        return _no_more_items_result(sd)
    logger.warning("[TreatmentStep] %s 但仍有 pending/损坏项"
                   "（矛盾形态），自愈降级接续裁决", _st)
    return None
def _resolve_auto_item_index(sd: str, state: dict,
                             items: list) -> tuple[int | None, dict | None]:
    item_index = _first_actionable_index(items)
    if item_index is None:
        return None, _finish_no_pending_items(sd, state, items)
    return item_index, None
def _finish_no_pending_items(sd: str, state: dict, items: list) -> dict:
    state["total"] = len(items)
    state["current_index"] = state["total"]
    state["status"] = "completed"
    save_treatment_state(sd, state)
    return _no_more_items_result(sd)
def _item_trace_fields(item: dict, *, severity: bool = False) -> dict:
    fields = {
        "file": as_str(item.get("file_path")),
        "rule_id": as_str(item.get("rule_id")),
        "locator": as_str(item.get("locator")),
    }
    if severity:
        fields["severity"] = normalize_item_severity(item.get("severity"))
    return fields
def _resolve_item_context(sd: str, item: dict, item_index: int,
                           stage_start: float) -> tuple[str, str, dict, dict | None]:
    orig_file_path = as_str(item.get("file_path", ""))
    rule_id = as_str(item.get("rule_id", ""))
    file_path = resolve_finding_file_path(orig_file_path, sd)
    _snippet = item.get("code_snippet")
    if not isinstance(_snippet, str) or not _snippet:
        _cs = find_diag_snippet(sd, item)
        item = dict(item)
        item["code_snippet"] = _cs if isinstance(_cs, str) else ""
    fail_result = None
    if not file_path:
        _fail_reason = f"路径无法解析或不存在: {orig_file_path}"
        fail_result = {"status": "failed", "index": item_index,
                       **_item_trace_fields(item),
                       "reason": _fail_reason,
                       "elapsed_s": elapsed_seconds(stage_start)}
    return rule_id, file_path, item, fail_result
def _build_treatment_finding(item: dict, file_path: str, rule_id: str) -> dict:
    _line = _item_finding_line(item)
    finding = {
        "rule_id": rule_id,
        "file": file_path,
        "line": _line,
        "severity": normalize_item_severity(item.get("severity")),
        "locator": item.get("locator", ""),
        "message": item.get("sample_message", "") or item.get("message", ""),
        "code_snippet": item.get("code_snippet", ""),
        "raw_finding": item.get("raw_finding", {}) if isinstance(item.get("raw_finding"), dict) else {},
        "finding_id": item.get("finding_id", ""),
    }
    finding["line"] = revalidate_finding_line(
        file_path, _line, rule_id, item.get("code_snippet", ""))
    return finding
def _record_single_item_plan(sd: str, item: dict, finding: dict,
                             item_index: int, resolved: str) -> dict:
    _plan = plan_single_fix(finding, resolved)
    _plan["index"] = item_index
    _plan["locator"] = as_str(item.get("locator"))
    try:
        record_treatment_fix_plan(sd, _plan)
    except (OSError, ValueError, TypeError):
        logger.warning("[TreatmentStep] 修复方案清单写入失败（不阻断治疗）", exc_info=True)
    update_treatment_item_state(sd, item_index, "planned",
                                  {"reason": "已生成修复方案，待 AI 审核执行验证"})
    return _plan
def _resolve_execution_item(sd: str, state: dict, items: list,
                            item_index: int | None,
                            stage_start: float, *,
                            raw_index, index_provided: bool,
                            ) -> tuple[int | None, dict | None, dict | None]:
    if index_provided and item_index is None:
        return None, None, {
            "status": "invalid_index",
            "message": f"无效索引 {raw_index!r}"
                        "（须为整数或整数值字符串）",
            "elapsed_s": elapsed_seconds(stage_start),
        }
    if not items and state.get("status") == "no_plan" and not index_provided:
        return item_index, None, _no_more_items_result(sd)
    if item_index is None:
        _heal = _self_heal_contradiction(state, items, sd)
        if _heal is not None:
            return item_index, None, _heal
        item_index, _early = _resolve_auto_item_index(sd, state, items)
        if _early is not None:
            return item_index, None, _early
    selected_item, locate_error = locate_treatment_item(items, item_index)
    if selected_item is None:
        if _valid_index(item_index, items):
            positional_item = items[item_index]
            if not isinstance(positional_item, dict):
                return item_index, None, _precheck_explicit_item(
                    positional_item, item_index, stage_start)
        reason = (locate_error[1] if locate_error
                  else f"无效索引 {item_index}")
        if index_provided:
            failure = {"status": "invalid_index", "message": reason,
                       "elapsed_s": elapsed_seconds(stage_start)}
        else:
            failure = {"status": "error", "index": item_index,
                       "error": reason,
                       "elapsed_s": elapsed_seconds(stage_start)}
        return item_index, None, failure
    _skip = _precheck_explicit_item(selected_item, item_index, stage_start)
    if _skip is not None:
        return item_index, None, _skip
    return item_index, selected_item, None
def execute_treatment_item_core(sd: str, item_index: int | None = None,
                                 stage_start: float | None = None) -> dict:
    raw_index = item_index
    index_provided = item_index is not None
    item_index = plan_index(item_index)
    if stage_start is None:
        stage_start = time.time()
    state = load_treatment_state(sd)
    if _is_corrupt_state(state):
        logger.error("[TreatmentStep] 治疗状态文件损坏（load 回退 error），"
                     "拒绝以空状态推进（防覆盖损坏文件）")
        return _record_treatment_run(
            {"status": "error", "index": -1,
                 "error": "治疗状态文件损坏（load 回退 error），"
                          "拒绝以空状态推进以免覆盖原文件",
                 "elapsed_s": elapsed_seconds(stage_start)}, stage_start)
    integrity_ok, integrity_reason = treatment_items_integrity(state)
    if not integrity_ok:
        logger.error("[TreatmentStep] 治疗状态 items 容器撕裂，拒绝推进: %s",
                     integrity_reason)
        return _record_treatment_run(
            {"status": "error", "index": -1,
             "error": ("治疗状态 items 容器撕裂，拒绝推进以免覆盖原状态: "
                       f"{integrity_reason}"),
             "elapsed_s": elapsed_seconds(stage_start)}, stage_start)
    items = list_field(state, "items")
    state["items"] = items
    item_index, item, _early = _resolve_execution_item(
        sd, state, items, item_index, stage_start,
        raw_index=raw_index, index_provided=index_provided)
    if _early is not None:
        return _record_treatment_run(_early, stage_start)
    if item is None:
        return _record_treatment_run(
            {"status": "error", "index": item_index,
             "error": "治疗执行项定位成功但未返回目标条目",
             "elapsed_s": elapsed_seconds(stage_start)}, stage_start)
    _fp_result = apply_step_fp_prefilter(
        sd, item, item_index, stage_start, state=state)
    if _fp_result is not None:
        return _record_treatment_run(
            {**_item_trace_fields(item, severity=True), **_fp_result},
            stage_start)
    rule_id, file_path, item, _fail = _resolve_item_context(
        sd, item, item_index, stage_start)
    if _fail is not None:
        record_item_failure(sd, item_index, _fail)
        return _record_treatment_run(_fail, stage_start)
    finding = _build_treatment_finding(item, file_path, rule_id)
    _plan = _record_single_item_plan(sd, item, finding, item_index, file_path)
    return _record_treatment_run(
        {"status": "planned", "index": item_index,
         "plan": _plan,
         "elapsed_s": elapsed_seconds(stage_start)}, stage_start)
_ITEM_FAILURE_STATUSES = frozenset({"failed", "error", "no_fixer"})


def record_item_failure(sd: str, item_index: int, fail: dict) -> None:
    """把一次失败的修复尝试落账为非 pending 终态（状态机不变式）。

    治疗项失败若仍停在 pending，下一轮批处理/AI 审核会再次选中同一条，
    形成“失败→重试→再失败”的死循环，并重复支付整轮回归验证成本
    （实测 76 s/项）；这里把失败终态与失败原因写进治疗状态，使
    ``item_details`` 携带失败历史，交由 AI 审核环节基于证据裁定，
    而不是无证据地反复重试。

    该不变式对「自动修复器」与「AI 审核写盘」两条通道同样成立，
    故统一由本函数实现，不允许各通道各自决定是否落账。
    """
    status = str(fail.get("status") or "failed").strip().lower()
    if status not in _ITEM_FAILURE_STATUSES:
        status = "failed"
    # 两条通道的失败载荷键名不同：自动修复器用 error/message，
    # AI 审核写盘用 reason/summary；统一在这里归一，避免失败证据丢失。
    reason = str(fail.get("error") or fail.get("message")
                 or fail.get("reason") or fail.get("summary") or "")[:500]
    try:
        update_treatment_item_state(sd, item_index, status,
                                    {"reason": reason} if reason else None)
    except Exception as _state_err:  # noqa: BLE001 —— 落账失败不阻断，零遗留门禁会暴露
        logger.warning("[TreatmentStep] 失败状态落账异常(index=%s): %s",
                       item_index, _state_err)


def _record_treatment_run(r: dict, stage_start: float) -> dict:
    r.setdefault("elapsed_s", elapsed_seconds(stage_start))
    write_module_run(
        "treatment_experience",
        "execute_treatment_item_core",
        outcome=str(r.get("status", "ok")),
        duration_ms=(time.time() - stage_start) * 1000.0,
        index=r.get("index"))
    return r
def evaluate_zero_leftover(sd: str, out: dict, *,
                           allow_phase_advance: bool) -> dict | None:
    if out["status"] == "error":
        logger.warning(
            "[AIFixStep] 候选装配 error 透出，跳过零遗留门禁裁决与阶段推进: %s",
            out.get("reason", "")[:200])
        return None
    leftover_check = verify_treatment_zero_leftover(sd)
    out["zero_leftover"] = leftover_check
    if leftover_check.get("state_integrity") == "error":
        out["status"] = "error"
        out["reason"] = ("零遗留门禁核验异常，拒绝 ai_fix_done 阶段推进: "
                         + str(leftover_check.get("error", "未知错误")))
        logger.error("[AIFixStep] %s", out["reason"])
        return None
    if _is_corrupt_state(load_treatment_state(sd)):
        out["status"] = "error"
        out["reason"] = ("治疗状态文件损坏（load 回退 error），"
                         "拒绝零遗留放行与 ai_fix_done 阶段推进")
        logger.error("[AIFixStep] %s", out["reason"])
        return None
    if leftover_check.get("state_integrity") == "torn":
        out["status"] = "error"
        out["reason"] = (
            "治疗状态 items 容器撕裂，零遗留无法核验，"
            "拒绝 ai_fix_done 阶段推进: "
            + str(leftover_check.get("state_integrity_reason", "")))
        logger.error("[AIFixStep] %s", out["reason"])
        return None
    if not leftover_check["passed"]:
        out["status"] = "leftover_blocked"
        out["message"] = _leftover_blocked_message(leftover_check)
        logger.warning("[AIFixStep] Zero-leftover gate blocked: %s", out["message"])
        return None
    if not allow_phase_advance:
        logger.info("[AIFixStep] 只读预览零遗留校验通过，不推进 ai_fix_done")
        return None
    logger.info("[AIFixStep] done (zero-leftover OK): total=%d applied=%d rejected=%d failed=%d, %.1fs",
                out["total_candidates"], out["applied"], out["rejected"],
                out["failed"], out["elapsed_s"])
    return {
        "ai_fix_total": out["total_candidates"],
        "ai_fix_applied": out["applied"],
        "ai_fix_rejected": out["rejected"],
        "ai_fix_failed": out["failed"],
        "zero_leftover_passed": True,
    }
def _leftover_blocked_message(leftover_check: dict) -> str:
    return (
        "Zero-leftover gate FAILED: "
        f"{leftover_check.get('leftover_count', 0)}"
        f"/{leftover_check.get('total', 0)} items not terminal. "
        f"By status: {leftover_check.get('leftover_by_status', {})}. "
        f"Actions: {leftover_check.get('actions_required', [])}"
    )
def build_fix_step_out(backend: FixBackendResult, elapsed_s: float) -> dict:
    task_result, out_status = backend.task_result, backend.status
    out = {
        "status": out_status,
        "total_candidates": task_result.get("total_candidates", 0),
        "applied": backend.applied,
        "rejected": backend.rejected,
        "failed": backend.failed,
        "candidates": task_result.get("candidates", []),
        "items": task_result.get("items", []),
        "elapsed_s": elapsed_s,
    }
    if out_status == "error":
        out["reason"] = task_result.get("reason", "")
    elif task_result.get("message"):
        out["message"] = task_result["message"]
    return out

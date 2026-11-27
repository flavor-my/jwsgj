from __future__ import annotations

import glob
import json
import logging
import os
from typing import Any

from jwsgj.diag_types_normalize import (
    as_entry_list,
    as_pure_count,
    coerce_round_anchor,
    coerce_round_anchor_strict,
    compact_ts_to_ms,
    dict_items,
    dict_or_empty,
    elapsed_seconds,
    entry_round_anchor,
    int_metric,
    int_or,
    is_pure_int,
    len_safe,
    method_status_bucket,
    safe_float,
    signal_bool,
    str_or,
    str_or_empty,
    timestamp_human,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    FIELD_FINDINGS_SUPPRESSED,
    FIELD_INTERMEDIATE_REPORTS,
    FIELD_METHODS_EXECUTED,
    FIELD_RULES_TRIGGERED,
    FIELD_TOTAL_INPUT_FINDINGS,
)
from jwsgj.diag_zero_backlog_ledger import get_ai_review_verdicts
from jwsgj.feedback_coordinator import FeedbackCoordinator
from jwsgj.html_render_pipeline import (
    emit_final_summary_block,
    generate_html_report,
)
from jwsgj.log_config import log_swallowed
from jwsgj.pipeline_report_assembly import (
    _as_str_list,
    _normalize_status_text,
    attach_degradation_report,
)
from jwsgj.pipeline_round_trace import (
    ARCHIVE_DIRNAME,
    PipelineContext,
    _resume_plan_is_current,
    advance_pipeline_phase,
    get_pipeline_progress,
    load_pipeline_state,
    load_review_evidence,
    normalize_count,
    query_methods_progress,
    treatment_exec_result,
)
from jwsgj.runtime_paths import (
    cv_conclusion_history_path,
    evolution_report_path,
    first_json_artifact,
    fp_rules_path,
    get_html_report_base,
    get_temp_dir,
    json_artifact_dir,
    json_artifact_glob,
    read_evolution_section,
    zero_backlog_ledger_path,
)
from jwsgj.runtime_scope import normalize_skill_dir
from jwsgj.shared_cache import (
    carry_failure_detail,
    mem_bus_peek,
    mem_bus_take,
)
from jwsgj.treatment_state import get_treatment_state_path
from jwsgj.xv_intermediate_store import (
    cv_artifact_fresh,
    get_round_start_ts,
    load_intermediate,
    normalize_round_start_ts,
    read_stage_trace_entries,
    round_anchor_equiv_form,
)

logger = logging.getLogger(__name__)
__all__ = [
    'PIPELINE_FIELD_FLOW',
    'cv_out_view',
    'cv_phase_extra',
    'describe_pipeline_field_flow',
    'emit_cv_report',
    'finalize_completed_pipeline',
    'finalize_pipeline_reports',
    'generate_final_summary_htmls',
    'get_cv_report_path',
    'get_pipeline_round_trace',
    'get_pipeline_stage_traces',
    'load_cv_report_tolerant',
    'load_first_valid_report',
    'load_method_adjustments_tolerant',
    'load_plan_cv_report',
    'load_stage6_inputs',
    'load_stage_cv_report',
    'load_stages_from_files',
    'mem_cv_report_current',
    'plan_cv_report_candidates',
    'read_json_silent',
    'regression_out_view',
    'resolve_treatment_plan',
    'state_cv_report_path',
    'step_run_payload',
]
_READ_ENCODING = "utf-8-sig"
def _plan_candidates(sd: str) -> list[str]:
    return sorted(json_artifact_glob(sd, "treatment_plan_*.json"),
                  reverse=True)
def _load_plan_tolerant(sd: str, plan_path: str) -> dict:
    candidates = [plan_path] if plan_path else []
    candidates.extend(p for p in _plan_candidates(sd) if p != plan_path)
    if not candidates:
        return {"plan": {}, "status": "missing", "plan_path": ""}
    current = normalize_round_start_ts(get_round_start_ts(sd))
    if current:
        candidates = [
            path for path in candidates
            if _resume_plan_is_current(sd, path, current)]
    if not candidates:
        return {"plan": {}, "status": "load_failed", "plan_path": plan_path}
    plan, _hit = load_first_valid_report(candidates)
    if _hit:
        return {"plan": plan, "status": "loaded", "plan_path": _hit}
    return {"plan": {}, "status": "load_failed", "plan_path": plan_path}
def _get_plan_file(sd: str) -> str:
    p_state = load_pipeline_state(sd)
    artifacts = dict_or_empty(p_state.get("artifacts"))
    _p = str_or(artifacts.get("plan_path")) or str_or(
        p_state.get("plan_path"))
    if _p and os.path.isfile(_p):
        return _p
    _files = _plan_candidates(sd)
    return _files[0] if _files else ""
def resolve_treatment_plan(skill_dir: str) -> dict:
    plan_path = ""
    try:
        plan_path = _get_plan_file(skill_dir)
        return _load_plan_tolerant(skill_dir, plan_path)
    except Exception as exc:  # noqa: BLE001
        logger.warning("[TreatmentPlan] 计划候选发现或读取失败(降级空计划): %s", exc)
        return {"plan": {}, "status": "load_failed", "plan_path": plan_path}
def state_cv_report_path(p_state: dict, *, full_first: bool = False) -> str:
    if not isinstance(p_state, dict):
        logger.warning("[CVReport] 管线状态非映射(%s)，按无报告路径处理",
                       type(p_state).__name__)
        p_state = {}
    artifacts = p_state.get("artifacts", {})
    if not isinstance(artifacts, dict):
        artifacts = {}
    _levels = (
        (artifacts.get("full_report_path"), p_state.get("full_report_path"),
         artifacts.get("cv_report_path"), p_state.get("cv_report_path"))
        if full_first else
        (artifacts.get("cv_report_path"), p_state.get("cv_report_path"),
         artifacts.get("full_report_path"), p_state.get("full_report_path")))
    for _raw in _levels:
        if isinstance(_raw, str) and _raw:
            return _raw
    return ""
def _cv_report_candidates(sd: str) -> list[str]:
    _p = state_cv_report_path(load_pipeline_state(sd))
    candidates: list[str] = [_p] if _p else []
    for _f in sorted(json_artifact_glob(sd, "cv_final_report_*.json"),
                     reverse=True):
        if _f not in candidates:
            candidates.append(_f)
    return candidates
def get_cv_report_path(sd: str) -> str:
    for _p in _cv_report_candidates(sd):
        if os.path.isfile(_p):
            return _p
    return ""
def _is_error_report(data: Any) -> bool:
    return isinstance(data, dict) and data.get("_error") is True
def _report_belongs_to_round(data: dict, current_round: str) -> bool:
    if not current_round:
        return True
    anchor = entry_round_anchor(data)
    if not anchor:
        return False
    return (round_anchor_equiv_form(anchor)
            == round_anchor_equiv_form(current_round))
def load_first_valid_report(candidates: list[str], *,
                            current_round: str = "") -> tuple[dict, str]:
    candidates = _as_str_list(candidates)
    for _cand in candidates:
        if not isinstance(_cand, str) or not os.path.isfile(_cand):
            continue
        try:
            with open(_cand, encoding=_READ_ENCODING) as _cf:
                _data = json.load(_cf)
            if not isinstance(_data, dict):
                logger.warning(
                    "[CVReport] 候选报告顶层非 dict(跳过取更旧): %s", _cand)
                continue
            if not _data:
                logger.warning(
                    "[CVReport] 候选报告为空 dict(跳过取更旧): %s", _cand)
                continue
            if _is_error_report(_data):
                logger.warning(
                    "[CVReport] 候选报告含错误哨兵(跳过取更旧): %s", _cand)
                continue
            if not _report_belongs_to_round(_data, current_round):
                logger.warning("[CVReport] 候选报告非本轮(跳过): %s", _cand)
                continue
            return _data, _cand
        except (OSError, ValueError, RecursionError) as _le:
            logger.warning("[CVReport] 候选报告读取/解析失败(跳过取更旧): %s: %s",
                           _cand, _le)
    return {}, ""
def load_cv_report_tolerant(sd: str) -> tuple[dict, str]:
    try:
        _cur_anchor = coerce_round_anchor(
            load_pipeline_state(sd).get("round_start_ts"))
    except Exception as _se:  # noqa: BLE001
        logger.debug("[CVReport] 轮次锚读取失败(内存通道降级): %s", _se)
        _cur_anchor = ""
    _mem = mem_bus_peek("cv_report_slim", sd)
    if isinstance(_mem, dict) and _mem:
        if _is_error_report(_mem):
            logger.warning("[CVReport] 内存报告含错误哨兵(回退磁盘)")
        elif (not _cur_anchor
                or round_anchor_equiv_form(entry_round_anchor(_mem))
                == round_anchor_equiv_form(_cur_anchor)):
            return _mem, "mem_bus://cv_report_slim"
        else:
            logger.warning(
                "[CVReport] 内存报告轮次不匹配(回退磁盘): mem=%r cur=%r",
                entry_round_anchor(_mem), _cur_anchor)
    return load_first_valid_report(
        _cv_report_candidates(sd), current_round=_cur_anchor)
def plan_cv_report_candidates(sd: str) -> list[str]:
    _state_cv_path = state_cv_report_path(load_pipeline_state(sd),
                                           full_first=True)
    candidates: list[str] = [_state_cv_path] if _state_cv_path else []
    for _pat in ("cv_full_report_*.json", "cv_final_report_*.json"):
        for _f in sorted(json_artifact_glob(sd, _pat), reverse=True):
            if _f not in candidates:
                candidates.append(_f)
    return candidates
def mem_cv_report_current(payload: dict, sd: str) -> bool:
    current = normalize_round_start_ts(get_round_start_ts(sd))
    if not current:
        return True
    return _round_anchor_admitted(
        payload.get("round_start_ts"), current, tag="TreatmentPlanStep",
        source="CV内存载荷", missing="缺失", suffix="，丢弃",
        normalized_stale=True)
def load_plan_cv_report(cv_cands: list, sd: str) -> tuple[dict, str]:
    cv_cands = _as_str_list(cv_cands)
    _mem_full = mem_bus_take("cv_full_report", sd)
    if isinstance(_mem_full, dict) and _mem_full:
        if _is_error_report(_mem_full):
            logger.warning(
                "[TreatmentPlanStep] CV内存报告含错误哨兵(回退磁盘候选)")
        elif mem_cv_report_current(_mem_full, sd):
            logger.info("[TreatmentPlanStep] CV报告内存直通命中（零读盘）: %d 键",
                        len(_mem_full))
            return _mem_full, "mem_bus://cv_full_report"
    return load_first_valid_report(
        cv_cands,
        current_round=normalize_round_start_ts(get_round_start_ts(sd)))
def load_stage_cv_report(skill_dir: str, *,
                          plan_mode: bool = False) -> tuple[dict, str, bool]:
    if plan_mode:
        candidates = plan_cv_report_candidates(skill_dir)
        report, path = load_plan_cv_report(candidates, skill_dir)
        return report, path, any(os.path.isfile(_c) for _c in candidates)
    report, path = load_cv_report_tolerant(skill_dir)
    return report, path, bool(get_cv_report_path(skill_dir))
def _archive_artifact_path(state: Any) -> str | None:
    if not isinstance(state, dict):
        return None
    artifacts = state.get("artifacts")
    if not isinstance(artifacts, dict):
        return None
    path = artifacts.get("archive_feedback_loop")
    if isinstance(path, str) and os.path.isfile(path):
        return path
    return None
def _state_archive_candidate(ctx: PipelineContext) -> str | None:
    try:
        return _archive_artifact_path(load_pipeline_state(ctx.skill_dir))
    except Exception as e:  # noqa: BLE001
        logger.debug("[Stage6d] active-pipeline artifacts 读取失败(回退glob): %s", e)
    return None
def _read_stage6b_payload(path: str) -> tuple[dict, str | None] | None:
    try:
        with open(path, encoding=_READ_ENCODING) as f:
            payload = json.load(f)
    except (OSError, ValueError, RecursionError) as _ae:
        logger.warning("[Stage6d] feedback_loop 归档不可读(跳过取更旧): %s: %s",
                       path, _ae)
        return None
    if not isinstance(payload, dict):
        logger.warning("[Stage6d] feedback_loop 归档顶层非 dict(跳过取更旧): %s",
                       path)
        return None
    _round_ts = coerce_round_anchor_strict(payload.pop("round_start_ts", ""))
    for _meta in ("_step_name", "_archived_at", "_schema_version"):
        payload.pop(_meta, None)
    return payload, _round_ts
def _archive_glob_candidates(skill_dir: str) -> list[str]:
    arch_dir = os.path.join(get_temp_dir(skill_dir), ARCHIVE_DIRNAME)
    pattern = os.path.join(arch_dir, "feedback_loop_*.json")
    return sorted((p for p in glob.glob(pattern) if os.path.isfile(p)),
                  reverse=True)
def _stage6b_candidates(ctx: PipelineContext) -> list[str]:
    candidates: list[str] = []
    state_path = _state_archive_candidate(ctx)
    if state_path:
        candidates.append(state_path)
    for path in _archive_glob_candidates(ctx.skill_dir):
        if path not in candidates:
            candidates.append(path)
    return candidates
def _round_anchor_verdict(raw: Any, current: str) -> tuple[str, str, str]:
    anchor = coerce_round_anchor_strict(raw)
    if not current:
        return "current", anchor or "", ""
    if anchor is None:
        return "invalid", "", ""
    normalized = normalize_round_start_ts(anchor)
    if not normalized:
        return "unanchored", anchor, ""
    if normalized != round_anchor_equiv_form(current):
        return "stale", anchor, normalized
    return "current", anchor, normalized
def _round_anchor_admitted(raw: Any, current: str, *,
                           tag: str = "ReportChannel", source: str,
                           missing: str = "缺失", suffix: str = "，丢弃",
                           normalized_stale: bool = False) -> bool:
    verdict, anchor, normalized = _round_anchor_verdict(raw, current)
    if verdict == "current":
        return True
    if verdict == "invalid":
        logger.warning("[%s] %s轮次锚类型非法(不可归属)%s",
                       tag, source, suffix)
    elif verdict == "unanchored":
        logger.warning("[%s] %s%s轮次锚(不可归属)%s",
                       tag, source, missing, suffix)
    else:
        logger.info("[%s] %s非本轮(round=%s != %s)%s",
                    tag, source, normalized if normalized_stale else anchor,
                    current, suffix)
    return False
def _load_stage6b_archive(ctx: PipelineContext) -> dict | None:
    _cur_round = normalize_round_start_ts(get_round_start_ts(ctx.skill_dir))
    _mem = mem_bus_take("stage6b_feedback_loop", ctx.skill_dir)
    if (isinstance(_mem, dict) and _mem
            and _round_anchor_admitted(
                _mem.get("round_start_ts"), _cur_round, tag="Stage6d",
                source="feedback_loop 内存载荷", missing="无",
                suffix="，跳过内存副本", normalized_stale=True)):
        return dict(_mem)
    for _cand in _stage6b_candidates(ctx):
        _read = _read_stage6b_payload(_cand)
        if _read is None:
            continue
        payload, _raw_round_ts = _read
        if _round_anchor_admitted(
                _raw_round_ts, _cur_round, tag="Stage6d",
                source="feedback_loop 归档", missing="无",
                suffix=f"，跳过: {_cand}", normalized_stale=True):
            return payload
    return None
def load_method_adjustments_tolerant(skill_dir: str) -> dict:
    adj_path = "method_adjustments"
    try:
        data = read_evolution_section(skill_dir, "method_adjustments")
    except (OSError, ValueError, TypeError) as e:
        logger.warning("[Stage6d] method_adjustments 读取失败(降级空表): %s: %s",
                       adj_path, e)
        return {}
    if data is None:
        return {}
    if not isinstance(data, dict):
        logger.warning("[Stage6d] method_adjustments 形态非法(降级空表): %s: %s",
                       type(data).__name__, adj_path)
        return {}
    return data
def _method_id_for_recovery(detail: Any) -> str | None:
    if not isinstance(detail, dict):
        return None
    mid = detail.get("method_id", "")
    if not isinstance(mid, str) or not mid:
        return None
    if as_pure_count(detail.get("findings_count")) <= 0:
        return None
    return mid
def _recover_method_findings(intermediate_dir: str, mid: str,
                             freshness: str | None) -> list:
    try:
        data = load_intermediate(intermediate_dir, mid,
                                 freshness_cutoff=freshness)
    except Exception as e:  # noqa: BLE001
        logger.warning("[Stage6d] %s 中间结果回读失败(跳过): %s", mid, e)
        return []
    if not isinstance(data, dict):
        return []
    findings = data.get("findings_list")
    return findings if isinstance(findings, list) else []
def _recover_stage1_findings(ctx: PipelineContext, details: list) -> list:
    findings: list = []
    intermediate_dir = json_artifact_dir(ctx.skill_dir)
    freshness = get_round_start_ts(ctx.skill_dir)
    for detail in details:
        mid = _method_id_for_recovery(detail)
        if mid is None:
            continue
        findings.extend(_recover_method_findings(
            intermediate_dir, mid, freshness))
    return findings
def _method_status_counts(details: list) -> dict:
    buckets = {"completed": 0, "failed": 0, "skipped": 0}
    total_findings = 0
    for detail in details:
        if not isinstance(detail, dict):
            continue
        _status = _normalize_status_text(detail.get("status"))
        # 历史记录里的 fail 是「诊断结论未通过（P0）」，方法已完整执行，
        # 不得计入执行失败；执行健康与结论分别统计。
        if _status in ("fail", "failed"):
            _status = "warn"
        bucket = method_status_bucket(_status)
        if bucket is not None:
            buckets[bucket] += 1
        total_findings += as_pure_count(detail.get("findings_count"))
    return {
        "methods_passed": buckets["completed"],
        "methods_failed": buckets["failed"],
        "methods_skipped": buckets["skipped"],
        "total_findings": total_findings,
    }
def _stage1_payload(ctx: PipelineContext) -> dict:
    progress = query_methods_progress(ctx.skill_dir)
    if not isinstance(progress, dict):
        logger.warning("[Stage6d] 诊断进度视图非 dict(%s)，按空进度回填",
                       type(progress).__name__)
        progress = {}
    details = dict_items(progress.get("details"))
    counts = _method_status_counts(details)
    declared_executed = int_or(progress.get("completed"), 0)
    observed_executed = counts["methods_passed"] + counts["methods_failed"]
    executed = max(declared_executed, observed_executed)
    return {
        "status": "completed",
        FIELD_METHODS_EXECUTED: as_pure_count(executed),
        **counts,
        FIELD_INTERMEDIATE_REPORTS: details,
        "findings": _recover_stage1_findings(ctx, details),
    }
def _stage2b_payload(ctx: PipelineContext) -> dict | None:
    cv_report, _src = load_cv_report_tolerant(ctx.skill_dir)
    if not cv_report:
        return None
    _rules_triggered = cv_report.get(FIELD_RULES_TRIGGERED)
    if not is_pure_int(_rules_triggered):
        _rules_triggered = cv_report.get("rules_applied_count", 0)
    _rules_triggered = as_pure_count(_rules_triggered)
    return {
        "status": "completed",
        "report": dict(cv_report),
        FIELD_TOTAL_INPUT_FINDINGS: as_pure_count(
            cv_report.get(FIELD_TOTAL_INPUT_FINDINGS, 0)),
        FIELD_FINDINGS_SUPPRESSED: as_pure_count(
            cv_report.get(FIELD_FINDINGS_SUPPRESSED, 0)),
        FIELD_RULES_TRIGGERED: _rules_triggered,
    }
def _load_json_dict(path: str, label: str) -> dict:
    with open(path, encoding=_READ_ENCODING) as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise TypeError(f"{label} 格式非法: {type(data).__name__}")
    return data
def _stage4_payload(ctx: PipelineContext) -> dict | None:
    path = get_treatment_state_path(ctx.skill_dir)
    if not os.path.isfile(path):
        return None
    state = _load_json_dict(path, "_treatment_state.json")
    _exec_view = dict(treatment_exec_result(ctx.skill_dir))
    _exec_view.pop("details", None)
    _exec_view["status"] = (str_or(state.get("status"))
                             or str_or(_exec_view.get("status"))
                             or "completed")
    _exec_view["fixes_applied"] = (
        as_pure_count(state.get("succeeded", 0))
        + as_pure_count(state.get("ai_fixed", 0)))
    _exec_view["items"] = dict_items(state.get("items"))
    _exec_view["details"] = dict_items(state.get("item_details"))
    return _exec_view
def _stage5_payload(ctx: PipelineContext) -> dict | None:
    _cur_round = normalize_round_start_ts(get_round_start_ts(ctx.skill_dir))
    review = mem_bus_peek("review_result", ctx.skill_dir)
    if (isinstance(review, dict) and review
            and _round_anchor_admitted(
                review.get("round_start_ts"), _cur_round,
                source="复盘内存载荷 ")):
        return dict(review)
    path = first_json_artifact(ctx.skill_dir, "_review_result.json")
    if not path:
        return None
    payload = _load_json_dict(path, "_review_result.json")
    if not _round_anchor_admitted(
            payload.get("round_start_ts"), _cur_round, source="复盘磁盘副本 "):
        return None
    return payload
_STAGE_LOADERS = [
    ("stage1", _stage1_payload),
    ("stage2b", _stage2b_payload),
    ("stage4", _stage4_payload),
    ("stage5", _stage5_payload),
    ("stage6b", _load_stage6b_archive),
]
def _restore_stage(ctx: PipelineContext, key: str, loader) -> None:
    if key in ctx.stages:
        return
    try:
        payload = loader(ctx)
    except Exception as e:  # noqa: BLE001
        logger.warning("[Stage6d] %s 加载失败: %s", key, e)
        payload = None
    if payload:
        ctx.stages[key] = payload
    else:
        ctx.stages.setdefault(key, {})
def load_stages_from_files(ctx: PipelineContext):
    for key, loader in _STAGE_LOADERS:
        _restore_stage(ctx, key, loader)
def load_stage6_inputs(skill_dir: str, *,
                       with_fix_coverage: bool = False
                       ) -> tuple[dict | None, dict, dict]:
    review = load_review_evidence(skill_dir)
    cv_report, _cv_path = load_cv_report_tolerant(skill_dir)
    exec_result = treatment_exec_result(
        skill_dir, with_fix_coverage=with_fix_coverage)
    return review, cv_report, exec_result
_COORDINATOR_CONTENT_KEYS = ("frozen", "conflicts", "tracked_parameters",
                             "session_count")
_FEEDBACK_CONTENT_KEYS = ("fupan_quality_score", "fupan_memory_ops",
                          "diagnosis_feedbacks", "cv_feedbacks",
                          "fixer_feedbacks", "code_feedback_l1_applied")
def _load_cv_stats_channel(skill_dir: str) -> tuple[dict, dict]:
    _cv_stats: dict = {}
    _cvr: dict = {}
    try:
        _cvr, _ = load_cv_report_tolerant(skill_dir)
        if _cvr:
            for _k in ("confirmed", "likely", "uncertain",
                       "suppressed", "contradictions"):
                if _k in _cvr:
                    _cv_stats[_k] = normalize_count(_cvr.get(_k))
    except Exception:
        logger.debug("[FinalSummary] CV 报告读取失败（总报告降级空统计）",
                     exc_info=True)
    return _cv_stats, _cvr
def _aggregate_report_candidates(skill_dir: str) -> list[str]:
    _stamped = sorted(json_artifact_glob(skill_dir, "report_*.json"),
                      reverse=True)
    _cutoff = get_round_start_ts(skill_dir)
    if _cutoff:
        return [p for p in _stamped if cv_artifact_fresh(p, _cutoff)]
    _legacy = first_json_artifact(skill_dir, "report.json")
    return _stamped + ([_legacy] if _legacy else [])
def _load_aggregate_report_channel(skill_dir: str) -> tuple[list, int]:
    for _path in _aggregate_report_candidates(skill_dir):
        _agg = read_json_silent(_path)
        if not isinstance(_agg, dict) or not _agg:
            continue
        if _is_error_report(_agg):
            logger.warning(
                "[FinalSummary] 聚合报告含错误哨兵(跳过取更旧): %s", _path)
            continue
        return _aggregate_report_findings(_agg)
    return [], 0
def _findings_with_total(raw, total: int) -> tuple[list, int]:
    if not isinstance(raw, list):
        return [], total
    return list(raw), total or len(raw)
def _aggregate_report_findings(_agg: dict) -> tuple[list, int]:
    _st = _agg.get("summary") or {}
    _agg_findings_total = (normalize_count(_st.get("findings_total"))
                           if isinstance(_st, dict) else 0)
    _xv = _agg.get(CAT_CROSS_VALIDATION)
    _fs = (_finding_entries(_xv.get("findings"))
           if isinstance(_xv, dict) else [])
    if not _fs:
        _fs = _aggregate_layer3_findings(_agg)
    return _findings_with_total(_fs, _agg_findings_total)
def _aggregate_layer3_findings(_agg: dict):
    _layers = _agg.get("conclusion_layers") or {}
    if not isinstance(_layers, dict):
        return None
    _l3 = _layers.get("layer_3_evidence")
    if not isinstance(_l3, dict):
        return None
    return _finding_entries(_l3.get("top_findings"))
def _load_final_data_context(skill_dir: str) -> tuple[list, int, dict]:
    _cv_stats, _cvr = _load_cv_stats_channel(skill_dir)
    _agg_findings, _agg_findings_total = _load_aggregate_report_channel(skill_dir)
    if (not _agg_findings_total or not _agg_findings) and _cvr:
        _raw_findings = _finding_entries(_cvr.get("findings"))
        if not _raw_findings:
            _raw_findings = _finding_entries(_cvr.get("findings_index"))
        _cv_findings, _cv_total = _findings_with_total(
            _raw_findings,
            normalize_count(_cvr.get(FIELD_TOTAL_INPUT_FINDINGS)))
        if _cv_findings:
            _agg_findings = _cv_findings
            _agg_findings_total = max(_agg_findings_total, _cv_total)
    return _agg_findings, _agg_findings_total, _cv_stats
def _collect_trace_metrics(skill_dir: str) -> dict[str, dict]:
    metrics_by_phase: dict[str, dict] = {}
    try:
        traces = get_pipeline_stage_traces(skill_dir)
    except Exception as _te:  # noqa: BLE001
        logger.warning("[FinalSummary] 阶段轨迹读取失败(降级空指标): %s", _te)
        return metrics_by_phase
    for trace in as_entry_list(traces):
        if not isinstance(trace, dict):
            continue
        phase = trace.get("phase")
        metrics = trace.get("metrics")
        if isinstance(phase, str) and isinstance(metrics, dict):
            metrics_by_phase[phase] = metrics
    return metrics_by_phase
def _coordinator_status_report(skill_dir: str) -> dict:
    try:
        status = FeedbackCoordinator(skill_dir).get_status()
    except Exception:
        logger.debug("[FinalSummary] 协调器状态读取降级", exc_info=True)
        return {}
    if not isinstance(status, dict):
        return {}
    frozen = status.get("frozen_parameters")
    return {
        "frozen": len(frozen) if isinstance(frozen, list) else 0,
        "conflicts": normalize_count(status.get("total_conflicts", 0)),
        "tracked_parameters": normalize_count(
            status.get("total_parameters_tracked", 0)),
        "session_count": normalize_count(status.get("session_count", 0)),
    }
def _fanout_stage_payload(skill_dir: str) -> dict:
    latest = first_json_artifact(skill_dir, "fanout_report_latest.json")
    candidates = [latest] if latest else []
    for path in sorted(json_artifact_glob(
            skill_dir, "fanout_report_*.json"), reverse=True):
        if path not in candidates:
            candidates.append(path)
    current = normalize_round_start_ts(get_round_start_ts(skill_dir))
    data, path = load_first_valid_report(candidates, current_round=current)
    if not data:
        return {}
    return {
        "report_path": str_or(data.get("report_path")) or path,
        "stage_id": str_or(data.get("stage_id")) or "G",
        "stage_label": str_or(data.get("stage_label"))
                       or "阶段G: 扇出诊断与治疗",
        "summary": dict_or_empty(data.get("summary")),
        "gate": dict_or_empty(data.get("gate")),
    }
def _stage_health(report: dict, *,
                  required_keys: tuple[str, ...] = ()) -> str:
    _rep = dict_or_empty(report)
    if not _rep:
        return "missing"
    if not required_keys:
        return "ok"
    if all(_content_present(_rep.get(_key)) for _key in required_keys):
        return "ok"
    return "degraded"
def _treatment_plan_stage_payload(skill_dir: str) -> dict:
    try:
        _resolved = resolve_treatment_plan(skill_dir)
    except Exception as _tpe:  # noqa: BLE001
        log_swallowed(__name__, _tpe,
                      context='_treatment_plan_stage_payload:Exc')
        return {"plan_path": "", "load_status": "load_failed",
                "total_items": 0, "auto_safe_count": 0}
    _plan = dict_or_empty(_resolved.get("plan"))
    _items = dict_items(_plan.get("items"))
    _auto_safe = sum(
        1 for _item in _items
        if isinstance(_item, dict) and _item.get("auto_safe") is True)
    return {
        "plan_path": str_or(_resolved.get("plan_path")),
        "load_status": str_or(_resolved.get("status")),
        "total_items": len(_items),
        "auto_safe_count": _auto_safe,
    }
def _treatment_plan_stage_status(plan_report: dict) -> str:
    _rep = dict_or_empty(plan_report)
    if not _rep:
        return "missing"
    load_status = _normalize_status_text(_rep.get("load_status"))
    if load_status == "missing":
        return "missing"
    if load_status != "loaded" or not str_or(_rep.get("plan_path")):
        return "degraded"
    return _stage_health(_rep, required_keys=("plan_path", "total_items"))
def _content_present(value: Any) -> bool:
    if value is None:
        return False
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (list, tuple, set, frozenset, dict)):
        return bool(value)
    return True
def _has_positive_value(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return value > 0
    if isinstance(value, str):
        text = value.strip()
        if not text or not signal_bool(text):
            return False
        try:
            return float(text) > 0
        except (TypeError, ValueError):
            return True
    if isinstance(value, (list, tuple, set, frozenset, dict)):
        return bool(value)
    return value is not None
# 治疗项已处理的计数键：与复盘前置门保持同一口径，任一非零才算治疗真的推进过。
_TREATMENT_HANDLED_KEYS = (
    "executed", "succeeded", "fixed", "failed", "error", "rolled_back",
    "skipped", "fp_confirmed", "pending_confirm", "suggestion", "no_fixer",
    "ai_fixed",
)
# 最终报告的硬门阶段：治疗计划/执行未完成时，报告必然只剰空壳，
# 评分与结论全部失实——这类半成品报告比没有报告更有害。
_FINAL_REPORT_BLOCKING_STAGES = frozenset({
    "treatment_plan", "treatment_execution",
})
# 允许产出最终报告的最低相位：治疗项执行完成。
_FINAL_REPORT_MIN_PHASE = "treatment_done"
def _phase_reached_safe(current: str, milestone: str) -> bool:
    """相位到达判定（延迟导入避开与 pipeline_steps_phases 的循环依赖）。

    导入失败时返回 True（fail-open）：门禁自身故障不得阻断正常交付。
    """
    try:
        from jwsgj.pipeline_steps_phases import phase_reached
    except Exception as _import_exc:  # noqa: BLE001
        log_swallowed(__name__, _import_exc,
                      context='_phase_reached_safe:ImportError')
        return True
    return phase_reached(current, milestone)
def _treatment_execution_stage_status(skill_dir: str, report: dict) -> str:
    if not os.path.isfile(get_treatment_state_path(skill_dir)):
        return "missing"
    _rep = dict_or_empty(report)
    if not _rep:
        return "degraded"
    _state_status = _normalize_status_text(_rep.get("status"))
    if _state_status and _state_status not in ("completed", "no_plan"):
        return "degraded"
    _health = _stage_health(_rep, required_keys=("total", "executed"))
    if _health != "ok":
        return _health
    # 状态是「完成」但治疗项全部未处理：事实是「未开始」，不能当作 ok，
    # 否则最终报告会把「治疗未执行」写成「治疗完成」。
    _total = max(int_metric(_rep.get("total", 0)),
                 int_metric(_rep.get("total_items", 0)))
    _handled = sum(int_metric(_rep.get(key, 0))
                   for key in _TREATMENT_HANDLED_KEYS)
    if _total > 0 and _handled == 0:
        return "degraded"
    return "ok"
def _diagnosis_stage_status(report: dict) -> str:
    _rep = dict_or_empty(report)
    if not _rep:
        return "missing"
    if (_has_positive_value(_rep.get("methods_executed"))
            or _content_present(_rep.get("findings"))):
        return "ok"
    return "degraded"
def _feedback_stage_status(report: dict) -> str:
    _rep = dict_or_empty(report)
    if not _rep:
        return "missing"
    _coord = dict_or_empty(_rep.get("coordinator"))
    if any(_has_positive_value(_coord.get(_key))
           for _key in _COORDINATOR_CONTENT_KEYS):
        return "ok"
    if any(_has_positive_value(_rep.get(_key))
           for _key in _FEEDBACK_CONTENT_KEYS):
        return "ok"
    return "degraded"
def _build_final_stages(skill_dir: str, _agg_findings: list,
                        _cv_stats: dict, *,
                        progress: dict | None = None) -> dict:
    _raw_progress = (progress if isinstance(progress, dict)
                     else get_pipeline_progress(skill_dir))
    if not isinstance(_raw_progress, dict):
        logger.warning("[FinalSummary] 管线进度视图非 dict(%s)，按空视图装配",
                       type(_raw_progress).__name__)
    _progress = dict_or_empty(_raw_progress)
    _trace_metrics = _collect_trace_metrics(skill_dir)
    _rev_m = _trace_metrics.get("review_done", {})
    _fupan_m = _trace_metrics.get("fupan_done", {})
    _fb_m = _trace_metrics.get("feedback_done", {})
    _cfb_m = _trace_metrics.get("code_feedback_done", {})
    _coord_report = _coordinator_status_report(skill_dir)
    _diag_report = {
        "findings": _agg_findings,
        "methods_executed": normalize_count(_progress.get("completed")),
    }
    _fanout_report = _fanout_stage_payload(skill_dir)
    _plan_report = _treatment_plan_stage_payload(skill_dir)
    _treat_report = dict_or_empty(_progress.get("treatment"))
    _review_report = {
        "score": _rev_m.get("review_score", ""),
        "grade": _rev_m.get("review_grade", ""),
    }
    _feedback_report = {
        "coordinator": _coord_report,
        "fupan_quality_score": _fupan_m.get(
            "fupan_quality_score", ""),
        "fupan_memory_ops": _fupan_m.get("fupan_memory_ops", 0),
        "diagnosis_feedbacks": _fb_m.get("feedback_diag_count", 0),
        "cv_feedbacks": _fb_m.get("feedback_cv_count", 0),
        "fixer_feedbacks": _fb_m.get("feedback_fixer_count", 0),
        "code_feedback_l1_applied": _cfb_m.get("code_feedback_l1", 0),
    }
    return {
        "diagnosis": {
            "status": _diagnosis_stage_status(_diag_report),
            "report": _diag_report},
        "cross_validation": {
            "status": _stage_health(_cv_stats, required_keys=(
                "confirmed", "likely", "uncertain", "suppressed")),
            "report": _cv_stats},
        "fanout": {
            "status": _stage_health(_fanout_report,
                                    required_keys=("summary", "gate")),
            "report": _fanout_report},
        "treatment_plan": {
            "status": _treatment_plan_stage_status(_plan_report),
            "report": _plan_report},
        "treatment_execution": {
            "status": _treatment_execution_stage_status(
                skill_dir, _treat_report),
            "report": _treat_report},
        "review": {
            "status": _stage_health(_review_report,
                                    required_keys=("score", "grade")),
            "report": _review_report},
        "feedback": {
            "status": _feedback_stage_status(_feedback_report),
            "report": _feedback_report},
    }
def _trace_duration_ms_of(trace: dict) -> int:
    _dur = trace.get("phase_duration_ms")
    if isinstance(_dur, int) and not isinstance(_dur, bool) and _dur > 0:
        return _dur
    return 0
def _round_total_time_s(traces: list) -> float:
    _rows = ([t for t in traces if isinstance(t, dict)]
             if isinstance(traces, list) else [])
    if not _rows:
        return 0.0
    _anchor = ""
    for _t in reversed(_rows):
        _anchor = entry_round_anchor(_t)
        if _anchor:
            break
    _anchor_form = round_anchor_equiv_form(_anchor)
    # 末尾轨迹必须与轮次锚同轮：无锚/异轮的尾部轨迹（跨会话残留或状态丢失
    # 期间的留痕）不得充当本轮终点，否则总耗时会被抬高为跨轮时间差。
    _last = next(
        (_t for _t in reversed(_rows)
         if round_anchor_equiv_form(entry_round_anchor(_t)) == _anchor_form),
        _rows[-1])
    _t0ms = compact_ts_to_ms(normalize_round_start_ts(_anchor) or _anchor)
    _last_ts = str_or_empty(_last.get("timestamp"))
    _t1ms = compact_ts_to_ms(normalize_round_start_ts(_last_ts) or _last_ts)
    if _t0ms is not None and _t1ms is not None and _t1ms >= _t0ms:
        return round((_t1ms - _t0ms) / 1000.0, 3)
    _block: list = []
    for _t in reversed(_rows):
        _row_anchor_form = round_anchor_equiv_form(entry_round_anchor(_t))
        if not _row_anchor_form and _anchor_form and not _block:
            continue
        if _row_anchor_form != _anchor_form:
            break
        _block.append(_t)
    return round(sum(_trace_duration_ms_of(t) for t in _block) / 1000.0, 3)
def _merge_final_stages(built: dict, injected: dict | None) -> dict:
    if not isinstance(injected, dict) or not injected:
        return built
    merged = {_key: dict_or_empty(_value) for _key, _value in built.items()}
    for _key, _value in injected.items():
        if not isinstance(_value, dict):
            continue
        _base = dict(dict_or_empty(merged.get(_key)))
        _inj_report = _value.get("report")
        if isinstance(_inj_report, dict) and _inj_report:
            _base_report = dict(dict_or_empty(_base.get("report")))
            _base_report.update(_inj_report)
            _base["report"] = _base_report
        for _k, _v in _value.items():
            if _k == "report":
                continue
            _base[_k] = _v
        merged[_key] = _base
    return merged
def _final_report_gate(completeness: dict,
                       progress: dict | None = None) -> tuple[bool, str]:
    """最终报告前置门：治疗阶段未完成/相位未就结时拒绝产出。

    返回 ``(是否放行, 阻塞原因)``；放行时原因为空串。

    判据两道：
    1. 治疗计划/治疗执行两个硬门阶段必须为 ok；
    2. 管线相位（可读时）至少达到 treatment_done。
    相位不可读（独立调用无管线状态）时只靠第一道，不凭空阻断。
    """
    _progress_map = dict_or_empty(progress)
    # 状态文件读取/签名验证失败时 phase 已降级为初始占位值，此时任何相位
    # 判定都不可信（会把「状态丢失」误读成「诊断进行中」）。
    _state_error = str_or(_progress_map.get("state_load_error")).strip()
    if _state_error:
        return False, f"pipeline_state_unreadable:{_state_error[:120]}"
    _incomplete = set(as_entry_list(
        dict_or_empty(completeness).get("incomplete_stages")))
    _blocking = _incomplete & _FINAL_REPORT_BLOCKING_STAGES
    if _blocking:
        return False, "treatment_stage_incomplete:" + ",".join(
            sorted(_blocking))
    _phase = str_or(_progress_map.get("phase")).strip()
    if _phase and not _phase_reached_safe(_phase, _FINAL_REPORT_MIN_PHASE):
        return False, f"phase_not_settled:{_phase}"
    return True, ""
def _data_completeness(stages: dict,
                        resume_degraded: dict | None = None) -> dict:
    _detail = {}
    for _key, _value in dict_or_empty(stages).items():
        if not isinstance(_value, dict):
            continue
        _detail[_key] = (str_or(_value.get("status")).strip().lower()
                         or "unknown")
    _missing = sorted(k for k, v in _detail.items() if v != "ok")
    _resume = dict_or_empty(resume_degraded)
    if _resume:
        logger.warning(
            "[FinalSummary] 恢复降级相位 %d 个（历史产物缺失但降级继续）: %s",
            len(_resume), ", ".join(sorted(_resume)))
    return {"total_stages": len(_detail),
            "complete_stages": len(_detail) - len(_missing),
            "incomplete_stages": _missing,
            "resume_degraded": sorted(_resume),
            "detail": _detail}
def _finding_entries(value: Any) -> list[dict]:
    if isinstance(value, dict):
        return [value] if value else []
    return [item for item in as_entry_list(value)
            if isinstance(item, dict) and item]
def generate_final_summary_htmls(
    skill_dir: str,
    *,
    stages: dict | None = None,
    findings: list | None = None,
    cv_stats: dict | None = None,
    total_time: float | None = None,
    progress: dict | None = None,
) -> dict:
    out = {"pipeline_report": "", "coverage_report": "", "pipeline_summary": "",
           "final_report": "", "final_json": "", "findings_total": 0, "cv_stats": {},
           "report_dir": "", "data_completeness": {}}
    _agg_findings: list = []
    _agg_findings_total = 0
    _cv_stats: dict = {}
    try:
        if findings is None or cv_stats is None:
            (_disk_findings, _disk_findings_total,
             _disk_cv_stats) = _load_final_data_context(skill_dir)
            if findings is None:
                _agg_findings = _disk_findings
                _agg_findings_total = _disk_findings_total
            else:
                _agg_findings = _finding_entries(findings)
                _agg_findings_total = len(_agg_findings)
            _cv_stats = (_disk_cv_stats if cv_stats is None
                         else dict_or_empty(cv_stats))
        else:
            _agg_findings = _finding_entries(findings)
            _agg_findings_total = len(_agg_findings)
            _cv_stats = dict_or_empty(cv_stats)
        _report_dir = get_html_report_base()
        os.makedirs(_report_dir, exist_ok=True)
        out["report_dir"] = _report_dir
        _resolved_progress = (progress if isinstance(progress, dict)
                              else get_pipeline_progress(skill_dir))
        _stages = _merge_final_stages(
            _build_final_stages(skill_dir, _agg_findings, _cv_stats,
                                progress=_resolved_progress), stages)
        _completeness = _data_completeness(
            _stages, _resolved_progress.get("resume_degraded"))
        out["data_completeness"] = _completeness
        if _completeness["incomplete_stages"]:
            logger.warning(
                "[FinalSummary] 最终报告数据不完整（%d/%d 阶段）: %s",
                len(_completeness["incomplete_stages"]),
                _completeness["total_stages"],
                ", ".join(_completeness["incomplete_stages"]))
        # 治疗阶段未完成时拒绝产出最终报告：报告的事实基础是「治疗已执行」，
        # 治疗未开始时只能输出空壳阶段与失实评分，会在后续收口与门禁中
        # 被当成真实结论消费。
        _gate_ok, _gate_reason = _final_report_gate(
            _completeness, _resolved_progress)
        if not _gate_ok:
            logger.error(
                "[FinalSummary] 最终报告拒绝产出（%s）：%d/%d 阶段未完成（%s）；"
                "请先推进管线到治疗完成后再收口",
                _gate_reason, len(_completeness["incomplete_stages"]),
                _completeness["total_stages"],
                ", ".join(_completeness["incomplete_stages"]))
            out["blocked"] = True
            out["block_reason"] = _gate_reason
            # 拒绝产出也要带出已聚合的统计：调用方据此判断「数据有了但
            # 阶段未完成」，而不是被当成「完全没数据」。
            out["findings_total"] = _agg_findings_total
            out["cv_stats"] = _cv_stats
            return out
        _resolved_total = (max(safe_float(total_time, 0.0), 0.0)
                           if total_time is not None
                           else _round_total_time_s(
                               get_pipeline_stage_traces(skill_dir)))
        _block = emit_final_summary_block(skill_dir, {
            "stages": _stages,
            "total_time": _resolved_total,
            "progress": _resolved_progress,
            "findings_count": _agg_findings_total,
            "cv_stats": _cv_stats,
            "report_dir": _report_dir,
            "data_completeness": _completeness,
        })
        out["report_dir"] = str_or(_block.get("report_dir")) or out["report_dir"]
        if _block.get("produced_keys"):
            _bind_final_report_paths(out, _block)
    except Exception as _fbe:  # noqa: BLE001
        logger.warning("[FinalSummary] 最终报告组装失败(不阻断): %s", _fbe)
    out["findings_total"] = _agg_findings_total
    out["cv_stats"] = _cv_stats
    return out
def _bind_final_report_paths(out: dict, block: dict) -> None:
    _final_path = str_or(block.get("path"))
    for _k in as_entry_list(block.get("produced_keys")):
        if isinstance(_k, str) and _k:
            out[_k] = _final_path
    if _final_path:
        out["final_report"] = _final_path
    out["final_json"] = str_or(block.get("json_path"))
_STEP_RUN_PAYLOAD_KEYS = ("total_findings", FIELD_RULES_TRIGGERED,
                          "changed_files_count")
def step_run_payload(out: dict) -> dict:
    out = dict_or_empty(out)
    return {key: out[key] for key in _STEP_RUN_PAYLOAD_KEYS if key in out}
def regression_out_view(status: str, result: dict,
                        stage_start: float) -> dict:
    result = dict_or_empty(result)
    changed_files = _as_str_list(result.get("changed_files"))
    changed_count = (len(changed_files) if changed_files
                     else max(int_or(result.get("changed_files_count")), 0))
    raw_has_changes = result.get("has_changes")
    has_changes = bool(changed_files or changed_count) or signal_bool(
        raw_has_changes)
    out = {
        "status": str_or(status),
        "has_changes": has_changes,
        "changed_files_count": changed_count,
        "elapsed_s": elapsed_seconds(stage_start),
    }
    if changed_files:
        out["changed_files"] = changed_files
    if result.get("regression_ctx_path"):
        out["regression_ctx_path"] = result["regression_ctx_path"]
    regression_error = str_or(result.get("regression_error")).strip()
    if regression_error:
        out["regression_error"] = regression_error[:500]
    carry_failure_detail(out, result)
    return out
def cv_out_view(status: str, result: dict, stage_start: float) -> dict:
    result = dict_or_empty(result)
    out = {
        "status": str_or(status),
        "total_findings": max(int_or(result.get("total_findings")), 0),
        FIELD_FINDINGS_SUPPRESSED: max(
            int_or(result.get(FIELD_FINDINGS_SUPPRESSED)), 0),
        FIELD_RULES_TRIGGERED: max(
            int_or(result.get(FIELD_RULES_TRIGGERED)), 0),
        "participation_rate": max(
            safe_float(result.get("participation_rate"), 0.0), 0.0),
        "elapsed_s": elapsed_seconds(stage_start),
    }
    if result.get("report_path"):
        out["cv_report_path"] = result["report_path"]
    carry_failure_detail(out, result)
    return out
def cv_phase_extra(view: dict, result: dict) -> dict:
    view = dict_or_empty(view)
    result = dict_or_empty(result)
    return {
        "cv_total_findings": max(int_or(view.get("total_findings")), 0),
        "cv_suppressed": max(int_or(view.get(FIELD_FINDINGS_SUPPRESSED)), 0),
        "cv_rules_triggered": max(int_or(view.get(FIELD_RULES_TRIGGERED)), 0),
        "cv_report_path": str_or(view.get("cv_report_path")),
        "full_report_path": str_or(result.get("full_report_path")),
    }
def emit_cv_report(sd: str, output_html: str | None, result: dict) -> None:
    if output_html:
        logger.info(
            "[CVStep] 独立 HTML 输出已归并 CV 阶段报告"
            "（不另写无配套 JSON 文件）: %s", output_html)
    try:
        cv_html_gen = dict_or_empty(generate_html_report(result, sd, "cv"))
        cv_html_data = dict_or_empty(cv_html_gen.get("data"))
        if cv_html_data.get("path"):
            logger.info("[CVStep] HTML 报告已生成: %s", cv_html_data["path"])
        else:
            logger.warning("[CVStep] HTML 报告生成未落盘: %s",
                           cv_html_gen.get("message", "no path returned"))
    except Exception as _he:  # noqa: BLE001
        logger.warning("[CVStep] HTML 报告生成失败: %s", _he)
def finalize_pipeline_reports(skill_dir: str) -> dict | None:
    try:
        generate_final_summary_htmls(skill_dir)
    except Exception as _fhe:  # noqa: BLE001
        logger.warning("[PipelineNext] 全流程总报告重生成失败(不阻断): %s", _fhe)
    _attach_target: dict = {}
    attach_degradation_report(skill_dir, _attach_target)
    degradation_report = _attach_target.get("_degradation_report")
    if not isinstance(degradation_report, dict) or not degradation_report:
        logger.warning("[PipelineNext] 降级报告未生成（按未生成处置）")
        return None
    _html_path = str_or(_attach_target.get("degradation_report_html"))
    if _html_path:
        degradation_report["html_path"] = _html_path
    return degradation_report
def finalize_completed_pipeline(
    skill_dir: str,
    out: dict,
    *,
    advance_phase: bool = True,
    findings: list | None = None,
    stages: dict | None = None,
    cv_stats: dict | None = None,
) -> None:
    if not isinstance(out, dict):
        logger.warning(
            "[FinalSummary] 收口输出容器非 dict(%s)，本次只生成报告不写回调用方",
            type(out).__name__)
        out = {}
    if advance_phase:
        advance_pipeline_phase(skill_dir, "all_completed", {
            "completed_at": timestamp_human(),
            "auto_enhance_applied": dict_or_empty(
                out.get("auto_enhancements")).get("applied", 0),
        })
    else:
        logger.info(
            "[FinalSummary] 非管线入口收口：跳过 all_completed 相位推进，"
            "仅生成最终报告")
    _injected = {
        _key: _value for _key, _value in (
            ("stages", stages), ("findings", findings),
            ("cv_stats", cv_stats))
        if _value is not None
    }
    try:
        _final = generate_final_summary_htmls(skill_dir, **_injected)
        out["final_html_reports"] = _final
        logger.info("[AutoEnhanceStep] 全流程总报告已生成: %s",
                    _final.get("pipeline_summary", ""))
    except Exception as _fhe:  # noqa: BLE001
        logger.warning("[AutoEnhanceStep] 全流程总报告生成失败(不阻断): %s", _fhe)
    attach_degradation_report(skill_dir, out)
    logger.info("[AutoEnhanceStep] 完成: auto_enh=%s, memory_ops=%d, %.1fs",
                 dict_or_empty(out.get("auto_enhancements")).get("applied", 0),
                 len_safe(out.get("_memory_operations")),
                 safe_float(out.get("elapsed_s")))
PIPELINE_FIELD_FLOW: dict[str, dict[str, str]] = {
    "round_anchor": {
        "semantics": "管线轮次标识（17 位毫秒级 ts，全链 join 主键）",
        "finding": "（无独立键；经 finding_id 内嵌轮次外信息间接关联）",
        "review_item": "（无；审核面经 review_id 与裁决留痕衔接）",
        "verdict_trace": "round_start_ts",
        "stage_trace": "round_start_ts",
        "evolution": "round_start_ts（复盘报告/增强条目/反哺会话/CV结论历史/"
                     "归零台账三事件/销项记录(v3.190.0+)/成长快照(v3.190.0+)"
                     "全链产物统一起始键；写入侧经 peek_round_start_ts 公开 SSOT "
                     "注入原始值不归一；历史遗留条目缺省=归属不可考，读侧不得臆造回填）",
    },
    "target_file": {
        "semantics": "目标文件路径",
        "finding": "file（别名 path/file_path/filepath/location 经 normalize_finding 归一出口 file）",
        "review_item": "file_path",
        "verdict_trace": "file_path（相对/入库形态）+ file_path_abs（绝对路径定位锚，v3+）",
        "stage_trace": "（无；阶段级产物路径在 artifacts 容器）",
        "evolution": "enhancement：target（语义随 target_type）/target_id；复盘报告：skill_dir 技能根级归属",
    },
    "target_line": {
        "semantics": "目标行号（0=文件级或无行级定位）",
        "finding": "line（恒非负 int，脏形态归 0）",
        "review_item": "line",
        "verdict_trace": "line",
        "stage_trace": "（无）",
        "evolution": "（无行级定位；反哺条目为规则/参数级目标）",
    },
    "finding_identity": {
        "semantics": "finding 身份锚（一个 finding 的一生的 join 主键；与 "
                     "归零台账 zb- 前缀稳定去重键为双格式：CV 侧为定位型 "
                     "{mid}:{file}:{line}:{rule_id}，台账侧为哈希型，经台账 "
                     "finding_seen 事件的 file/line/locator/rule_id 键桥接对齐）",
        "finding": "finding_id（CV 收集期补齐生成，xv_findings_core）",
        "review_item": "finding_id（treatment 通道收集层从 diagnosis_evidence "
                       "提取置顶；无 finding 级定位通道为空串）",
        "verdict_trace": "finding_id（v5+ 顶层恒在键；v1-v4 历史条目读侧回填 "
                         "空串=归属不可考）",
        "stage_trace": "（无；阶段级不留 finding 粒度）",
        "evolution": "zero_backlog_ledger finding_seen/finding_resolved 事件的 "
                     "finding_id（zb- 前缀稳定去重键，跨轮幂等锚）",
    },
    "rule_identity": {
        "semantics": "命中规则/检测器标识（误报固化/历史 FP 率/修复经验关联键）",
        "finding": "rule_id（别名 id/rule/detector_id/rule_ref 归一出口）",
        "review_item": "rule_id（+ rule_id_canonical 跨轮稳定形态）",
        "verdict_trace": "rule_id（target 为同值或 locator，随 target_kind 阅读）",
        "stage_trace": "（无）",
        "evolution": "rule_id（enhancement）/ target_id（增强目标标识）",
    },
    "description_text": {
        "semantics": "问题/建议描述主文本",
        "finding": "message（别名 description/title 归一出口）",
        "review_item": "description",
        "verdict_trace": "assessment.verdict_rationale / execution_reason（裁决与执行理由）",
        "stage_trace": "（无；阶段级指标在 metrics 容器）",
        "evolution": "description（enhancement）/ summary（复盘报告）",
    },
    "severity": {
        "semantics": "严重度词系（P0-P3 主流；安全域兼容 CRITICAL/HIGH）",
        "finding": "severity",
        "review_item": "severity",
        "verdict_trace": "original_severity（通道原始值）+ assessment.severity_assessment（AI 复核）",
        "stage_trace": "（无）",
        "evolution": "（无；反哺建议以 priority/confidence 表达）",
    },
    "event_time": {
        "semantics": "事件时刻（统一消费键 timestamp；形态由各段规约自明，"
                     "跨段 join 经 round_start_ts 分组后组内以 timestamp 对齐）",
        "finding": "（无独立键；finding_id 不含时刻）",
        "review_item": "（无；以裁决时刻为准）",
        "verdict_trace": "timestamp（ISO，与 at 同源）+ at_ts（17 位毫秒戳，跨文件时序免双格式解析）",
        "stage_trace": "timestamp（17 位毫秒戳）+ phase_duration_ms（相位耗时差分视图；"
                        "首相位自 round_start_ts 起算，锚点缺失为 None）",
        "evolution": "timestamp（复盘报告/增强条目/反哺会话/snapshot=ISO 恒在；"
                     "v3.190.0 起 CV结论历史 timestamp=ts 同值写入、归零台账三事件 "
                     "timestamp=ISO 写入、销项记录 timestamp=resolved_at 同值写入；"
                     "旁路键 ts/at/resolved_at 保留写入向后兼容，补齐非替代；"
                     "enhancement 另含 modified_at 裁决回填时刻）",
    },
    "phase": {
        "semantics": "管线相位/阶段标识",
        "finding": "（无；domain/sources 标注来源引擎）",
        "review_item": "channel（七通道）+ phase（provenance 内来源相位）",
        "verdict_trace": "channel + phase（裁决发生相位，ai_fix_pending/evolution_pending 等）",
        "stage_trace": "phase（目标相位）+ from_phase（源相位）+ direction（advance/rewind_resume/self_heal/legacy）",
        "evolution": "phase + source（enhancement 来源相位与域标识）",
    },
    "ownership": {
        "semantics": "归属锚（目标技能根/绝对路径）",
        "finding": "（无；file 经技能根语境解释）",
        "review_item": "（无；skill_dir 为调用上下文）",
        "verdict_trace": "skill_dir（v4+ 技能根归属锚，无文件通道恒可归属）+ "
                         "file_path_abs（v3+ 目标文件绝对路径，跨会话脱离 cwd 仍定位）",
        "stage_trace": "skill_dir（v3+）",
        "evolution": "skill_dir（复盘报告顶层；v3.190.0 起成长快照/销项记录同词补齐）",
    },
}
_KEY_SPEC_GUIDE: dict[str, str] = {
    "finding": "describe_finding_keys()",
    "review_item": "describe_review_item_keys()",
    "verdict_trace": "describe_verdict_trace_keys()",
    "stage_trace": "describe_stage_metrics_keys()",
    "evolution": "describe_evolution_artifact_keys()",
}
def describe_pipeline_field_flow() -> dict:
    return {
        "field_flow": {k: dict(v) for k, v in PIPELINE_FIELD_FLOW.items()},
        "stage_key_specs": dict(_KEY_SPEC_GUIDE),
        "join_anchors": {
            "round_start_ts": "轮次主键：stage_trace/verdict_trace/cv_conclusion_history/"
                "zero_backlog_ledger 四事件流 + 复盘报告/增强条目/反哺会话/销项记录/"
                "成长快照（v3.190.0 起后两产物补齐）全链共有；"
                "写入侧统一经 peek_round_start_ts 公开 SSOT 注入（原始值不归一）；"
                "历史遗留条目缺省=归属不可考，读侧不得臆造回填",
            "timestamp": "同名时间统一消费键：stage_trace（17 位戳）/ verdict_trace "
                "（ISO+at_ts 双格式）/ evolution 全产物（ISO；v3.190.0 起 "
                "cv_conclusion_history/zero_backlog_ledger/log_finding_closure "
                "写入侧补齐，旁路键 ts/at/resolved_at 保留向后兼容，补齐非替代）"
                "——按 round_start_ts 分组后组内时序对齐",
            "ownership": "skill_dir（stage_trace v3+/verdict_trace v4+/复盘报告/"
                "成长快照/销项记录 v3.190.0+）+ file_path_abs（verdict_trace v3+ 文件级定位）",
        },
        "normalizers": {
            "finding": "normalize_finding(finding) — 读侧归一（补齐非替代，line 恒非负 int）",
            "verdict_trace": "get_ai_review_verdicts 出口恒 24 键（_normalize_verdict_trace_entry 归一；v4 起含 skill_dir，v5 起含 finding_id）",
            "stage_trace": "get_pipeline_stage_traces 出口恒 11 键（含 phase_duration_ms "
                "与 phase_in_spec 视图键；trace_version 原值保留）",
        },
        "round_trace": "get_pipeline_round_trace(skill_dir, round_start_ts) — "
            "单轮全链追溯聚合出口（阶段留痕+裁决留痕+复盘摘要+反哺分桶"
            "（当轮条目）+误报固化计数+归零台账+CV 结论历史+相位概览"
            "八段一键视图，trace_version 锚跨版本可辨）",
    }
def read_json_silent(path: str) -> object:
    try:
        if not path or not os.path.isfile(path):
            return None
        with open(path, encoding=_READ_ENCODING, errors="replace") as _f:
            return json.load(_f)
    except Exception as _e:  # noqa: BLE001
        logger.debug(
            '静默降级[read_json_silent:Exc]: %s: %s', type(_e).__name__, _e)
        return None
def _resolve_round_filter(sd: str, round_start_ts: str | None) -> str:
    rst = round_start_ts
    if rst is None:
        try:
            rst = load_pipeline_state(sd).get("round_start_ts", "")
        except Exception as _e:  # noqa: BLE001
            logger.debug(
                '静默降级[get_pipeline_round_trace:rst]: %s', _e)
            rst = ""
    _anchor = coerce_round_anchor(rst)
    return normalize_round_start_ts(_anchor) or _anchor
def _parse_jsonl_dict(line: str) -> dict | None:
    line = line.strip()
    if not line.startswith("{"):
        return None
    try:
        event = json.loads(line)
    except (ValueError, RecursionError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_parse_jsonl_dict:ValueError+')
        return None
    return event if isinstance(event, dict) else None
def _iter_jsonl_dicts(path: str, log_tag: str):
    try:
        if not path or not os.path.isfile(path):
            return
        with open(path, encoding=_READ_ENCODING, errors="replace") as handle:
            for line in handle:
                event = _parse_jsonl_dict(line)
                if event is not None:
                    yield event
    except OSError as _e:
        logger.debug(
            '静默降级[%s]: %s: %s', log_tag, type(_e).__name__, _e)
def _collect_retro_summary(jdir: str, rst: str = "") -> dict:
    retro = read_json_silent(os.path.join(jdir, "retrospective_report.json"))
    retro_summary: dict = {}
    if not isinstance(retro, dict):
        return retro_summary
    _retro_rst = entry_round_anchor(retro)
    if rst and round_anchor_equiv_form(_retro_rst) != round_anchor_equiv_form(rst):
        return retro_summary
    for _k in ("timestamp", "session_id", "round_start_ts", "scores",
               "issues_found", "enhancement_actions", "summary"):
        if _k in retro:
            retro_summary[_k] = retro[_k]
    return retro_summary
def _collect_enhancement_stats(sd: str, rst: str) -> tuple[dict, list, int]:
    enh_counts: dict = {}
    enh_round_entries: list = []
    enh_unanchored = 0
    try:
        enh = read_evolution_section(sd, "enhancement_log")
    except (OSError, ValueError, TypeError) as _enh_exc:
        logger.warning("[Stage6d] enhancement_log 读取失败(降级空表): %s",
                       _enh_exc)
        enh = None
    for _e in _iter_enh_entries(enh):
        _st = _normalize_status_text(_e.get("status")) or "unknown"
        _e_rst = entry_round_anchor(_e)
        if not _e_rst:
            enh_unanchored += 1
        view = _enh_entry_compact_view(_e, _st, _e_rst, rst)
        if view is None:
            continue
        enh_counts[_st] = enh_counts.get(_st, 0) + 1
        enh_round_entries.append(view)
    return enh_counts, enh_round_entries, enh_unanchored
def _iter_enh_entries(enh) -> list:
    if not isinstance(enh, dict):
        return []
    return dict_items(enh.get("entries"))
def _enh_entry_compact_view(_e: dict, _st: str, _e_rst: str,
                             rst: str) -> dict | None:
    if rst and round_anchor_equiv_form(_e_rst) != round_anchor_equiv_form(rst):
        return None
    return {
        "target_id": str_or_empty(_e.get("target_id")),
        "action_type": str_or_empty(_e.get("action_type")),
        "status": _st,
        "rule_id": str_or_empty(_e.get("rule_id")),
        "phase": str_or_empty(_e.get("phase")),
        "source": str_or_empty(_e.get("source")),
        "round_start_ts": _e_rst,
        "timestamp": str_or_empty(_e.get("timestamp")),
        "modified_at": str_or_empty(_e.get("modified_at")),
    }
def _count_fp_rules(sd: str) -> int:
    fp = read_json_silent(fp_rules_path(sd))
    rules = fp.get("rules") if isinstance(fp, dict) else None
    return (len(rules) if isinstance(rules, (list, tuple, set, frozenset, dict))
            else 0)
def _collect_zero_backlog_counts(sd: str, rst: str) -> dict:
    zero_backlog_counts: dict = {}
    _ledp = zero_backlog_ledger_path(sd)
    for _ev in _iter_jsonl_dicts(_ledp, "get_pipeline_round_trace:ledger"):
        if rst and (round_anchor_equiv_form(entry_round_anchor(_ev))
                    != round_anchor_equiv_form(rst)):
            continue
        _ek = _normalize_status_text(_ev.get("event")) or "unknown"
        zero_backlog_counts[_ek] = zero_backlog_counts.get(_ek, 0) + 1
    return zero_backlog_counts
def _collect_cv_conclusion_latest(sd: str, rst: str = "") -> dict:
    cv_conclusion_latest: dict = {}
    for _cv in _iter_jsonl_dicts(
            cv_conclusion_history_path(sd), "get_pipeline_round_trace:cv_hist"):
        if rst and (round_anchor_equiv_form(entry_round_anchor(_cv))
                    != round_anchor_equiv_form(rst)):
            continue
        cv_conclusion_latest = _cv_snapshot_of(_cv)
    return cv_conclusion_latest
def _cv_snapshot_of(_cv: dict) -> dict:
    _concl = _cv.get("conclusions")
    return {
        "timestamp": str_or_empty(_cv.get("timestamp")
                                       or _cv.get("ts", "")),
        "round_start_ts": entry_round_anchor(_cv),
        "conclusions_count": (
            len(_concl) if isinstance(_concl, dict) else 0),
    }
def _build_phase_overview(stage_traces: list) -> dict:
    if not stage_traces:
        return {}
    _ph_seq: list = []
    _dir_counts: dict = {}
    _rewind_phases: list = []
    for _st in stage_traces:
        _ph, _dir = _phase_dir_of(_st)
        _accumulate_phase(_ph_seq, _dir_counts, _rewind_phases, _ph, _dir)
    return {
        "phase_sequence": _ph_seq,
        "phase_count": len(_ph_seq),
        "direction_counts": _dir_counts,
        "rewind_phases": _rewind_phases,
        "has_rewind": bool(_rewind_phases),
    }
def _phase_dir_of(_st) -> tuple[str, str]:
    if not isinstance(_st, dict):
        return "", ""
    return (str(_st.get("phase", "") or ""),
            str(_st.get("direction", "") or "advance"))
def _accumulate_phase(ph_seq: list, dir_counts: dict, rewind_phases: list,
                      ph: str, direction: str) -> None:
    if ph:
        ph_seq.append(ph)
    if direction:
        dir_counts[direction] = dir_counts.get(direction, 0) + 1
    if direction in ("rewind_resume", "self_heal") and ph \
            and ph not in rewind_phases:
        rewind_phases.append(ph)
def _round_trace_dict_entries(raw: Any, channel: str) -> tuple[list[dict], bool]:
    if not isinstance(raw, (list, tuple)):
        logger.warning("[RoundTrace] %s非序列(%s)，按空视图处理",
                       channel, type(raw).__name__)
        return [], True
    entries = [item for item in raw if isinstance(item, dict)]
    dropped = len(raw) - len(entries)
    if dropped:
        logger.warning("[RoundTrace] %s含非映射条目 %d 个(已跳过，视图降级)",
                       channel, dropped)
    return entries, dropped > 0
def _require_skill_root(skill_dir: Any, entry: str) -> str:
    try:
        raw = os.fspath(skill_dir)
    except TypeError as exc:
        raise TypeError(f"{entry}: skill_dir 须为路径") from exc
    if isinstance(raw, bytes):
        raw = os.fsdecode(raw)
    if not isinstance(raw, str) or not raw.strip():
        raise ValueError(f"{entry}: skill_dir 不能为空")
    return raw
def get_pipeline_stage_traces(skill_dir: str,
                              round_start_ts: str | None = None,
                              phase: str | None = None) -> list[dict]:
    sd = normalize_skill_dir(
        _require_skill_root(skill_dir, "get_pipeline_stage_traces"))
    if round_start_ts is None:
        round_start_ts = _resolve_round_filter(sd, None)
    return read_stage_trace_entries(sd, round_start_ts, phase)
def get_pipeline_round_trace(skill_dir: str,
                             round_start_ts: str | None = None) -> dict:
    sd = normalize_skill_dir(
        _require_skill_root(skill_dir, "get_pipeline_round_trace"))
    rst = _resolve_round_filter(sd, round_start_ts)
    raw_traces = get_pipeline_stage_traces(sd, round_start_ts=rst)
    stage_traces, traces_degraded = _round_trace_dict_entries(
        raw_traces, "阶段轨迹")
    try:
        raw_verdicts = get_ai_review_verdicts(sd, round_start_ts=rst)
        verdicts, verdicts_degraded = _round_trace_dict_entries(
            raw_verdicts, "裁决留痕")
    except Exception as _ve:  # noqa: BLE001
        logger.warning("[RoundTrace] 裁决留痕读取失败(降级): %s", _ve)
        verdicts_degraded = True
        verdicts = []
    retro_summary = _collect_retro_summary(os.path.dirname(
        evolution_report_path(sd)), rst)
    enh_counts, enh_round_entries, enh_unanchored = (
        _collect_enhancement_stats(sd, rst))
    fp_rules_count = _count_fp_rules(sd)
    zero_backlog_counts = _collect_zero_backlog_counts(sd, rst)
    cv_conclusion_latest = _collect_cv_conclusion_latest(sd, rst)
    _phase_overview = _build_phase_overview(stage_traces)
    degraded = verdicts_degraded or traces_degraded
    return {
        "trace_version": 1,
        "status": "partial" if degraded else "ok",
        "round_start_ts": rst,
        "skill_dir": sd,
        "stage_traces": stage_traces,
        "verdicts": verdicts,
        "verdicts_degraded": verdicts_degraded,
        "retrospective_summary": retro_summary,
        "enhancement_counts": enh_counts,
        "enhancement_round_entries": enh_round_entries,
        "enhancement_unanchored_count": enh_unanchored,
        "fp_rules_count": fp_rules_count,
        "zero_backlog_counts": zero_backlog_counts,
        "cv_conclusion_latest": cv_conclusion_latest,
        "phase_overview": _phase_overview,
        "keys_guide": {
            "stage_metrics": _KEY_SPEC_GUIDE["stage_trace"],
            "verdict_trace": _KEY_SPEC_GUIDE["verdict_trace"],
            "review_item": _KEY_SPEC_GUIDE["review_item"],
            "finding": _KEY_SPEC_GUIDE["finding"],
            "evolution_artifact": _KEY_SPEC_GUIDE["evolution"],
            "field_flow": "describe_pipeline_field_flow()",
        },
    }

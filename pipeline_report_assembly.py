from __future__ import annotations

import json
import logging
import math
import os
import shutil
import subprocess
import time
import traceback
from datetime import datetime
from pathlib import Path
from typing import Any

from jwsgj.build_skill_lifecycle import (
    detect_duplicate_names,
    load_skill_reputation,
    reputation_key,
    score_skill_health,
)
from jwsgj.diag_health_scoring import (
    apply_health_report,
    build_quality_projection,
)
from jwsgj.diag_types_normalize import (
    as_number,
    dict_items,
    dict_or_empty,
    elapsed_seconds,
    int_metric,
    int_or,
    str_or,
    timestamp_human,
    timestamp_ms,
)
from jwsgj.diag_zero_backlog_ledger import register_cv_findings_snapshot
from jwsgj.html_render_pipeline import (
    emit_aggregate_report_html,
    generate_html_report,
)
from jwsgj.log_config import log_swallowed
from jwsgj.pipeline_round_trace import (
    PipelineContext,
    PipelineGuard,
    query_methods_progress,
    save_treatment_plan,
    treatment_exec_result,
)
from jwsgj.retrospective_enhancer import run_retrospective
from jwsgj.retrospective_evolution import get_fp_evolution_summary
from jwsgj.runtime_paths import (
    diag_intermediate_dir,
    evolution_report_path,
    json_artifact_dir,
)
from jwsgj.runtime_scope import normalize_skill_dir
from jwsgj.shared_cache import (
    DiagnosticContext,
    as_diag_ctx,
    peek_warmed_cache,
)
from jwsgj.treatment_plan import generate_treatment_plan
from jwsgj.treatment_state import load_treatment_state
from jwsgj.xv_context_derivation import (
    METHOD_REGISTRY,
    sub_result,
)
from jwsgj.xv_context_history import (
    load_stage2b_baseline,
    persist_stage2b_baseline,
)
from jwsgj.xv_cv_report_assemble import (
    ReportAggregator,
    build_f1_report,
    log_cv_extract_summary,
)
from jwsgj.xv_intermediate_store import (
    clear_regression_handoff,
    get_round_start_ts,
    load_intermediate_fused,
    normalize_regression_handoff,
    persist_cv_reports,
    save_regression_handoff,
    take_regression_handoff,
)

logger = logging.getLogger(__name__)
__all__ = [
    'RegressionCrossValidator',
    'aggregate_report',
    'attach_degradation_report',
    'build_review_quality_augmentation',
    'diag_skill',
    'generate_degradation_report',
    'print_summary',
    'register_backlog_soft',
    'run_antipattern_density_report',
    'run_health_diag',
    'run_stage2a_regression_cv',
    'run_stage2b_main_cv',
]
_QUICK_SKILL_LIMIT = 4
def _emit_diag_skill_html(result: dict[str, Any], skill_md: Path | None) -> None:
    try:
        payload = dict(result)
        payload["_step_name"] = "health_score"
        payload["_stage_hint"] = "diag:A"
        _sd = str(skill_md.parent) if skill_md is not None else ""
        generate_html_report(payload, _sd, "step")
        logger.info("[Quality] 健康评分 HTML 报告已生成: %s", result.get("skill_name"))
    except Exception as _dhe:  # noqa: BLE001
        logger.warning("[Quality] 健康评分 HTML 报告生成失败(不阻断): %s", _dhe)
def diag_skill(skill_name: str, rep: dict[str, Any] | None = None) -> dict[str, Any]:
    result, skill_md = score_skill_health(skill_name, rep)
    _emit_diag_skill_html(result, skill_md)
    return result
def _zombie_of(row: dict[str, Any]) -> str:
    for _key in ("zombie_status", "zombie"):
        _text = str_or(row.get(_key)).strip().lower()
        if _text:
            return _text
    return "active"
def _compute_distribution_stats(
        results: list[dict[str, Any]]) -> tuple[dict[str, int], dict[str, int], float]:
    grades: dict[str, int] = {}
    zombie_dist: dict[str, int] = {}
    total_score = 0.0
    counted = 0
    for r in results:
        if isinstance(r, dict):
            g = str_or(r.get("grade")).strip() or "F"
            grades[g] = grades.get(g, 0) + 1
            _score = r.get("overall_score")
            if (isinstance(_score, (int, float))
                    and not isinstance(_score, bool)
                    and math.isfinite(_score)):
                total_score += _score
                counted += 1
            zs = _zombie_of(r)
            zombie_dist[zs] = zombie_dist.get(zs, 0) + 1
    avg_score = round(total_score / counted, 1) if counted else 0.0
    return grades, zombie_dist, avg_score
def _build_health_report(results: list[dict[str, Any]],
                         grades: dict[str, int], zombie_dist: dict[str, int],
                         avg_score: float,
                         duplicates: list[tuple[str, str]]) -> dict[str, Any]:
    return {
        "date": datetime.now().isoformat(),
        "total_skills": len(results),
        "average_score": avg_score,
        "summary": {
            "total_skills": len(results),
            "average_score": avg_score,
            "grade_distribution": grades,
            "zombie_distribution": zombie_dist,
            "duplicates_found": len(duplicates),
            "duplicate_pairs": [list(p) for p in duplicates],
        },
        "skills": results,
        "results": results,
        "duplicates": [list(p) for p in duplicates],
    }
def _log_health_summary(report: dict[str, Any]) -> None:
    _rep = dict_or_empty(report)
    _s = dict_or_empty(_rep.get("summary"))
    _zombies = sum(int_metric(c) for st, c in dict_or_empty(
        _s.get("zombie_distribution")).items()
        if st in ("zombie", "sunset"))
    logger.info(
        "Health diag: %d skills, avg=%.1f, zombies=%d, duplicates=%d",
        int_metric(_rep.get("total_skills", 0)),
        as_number(_rep.get("average_score", 0), 0),
        _zombies,
        int_metric(_s.get("duplicates_found", 0)),
    )
def _summary_grade_lines(s: dict) -> list[str]:
    _grade_dist = {str_or(g).strip() or "F": count
                   for g, count in dict_or_empty(
                       s.get("grade_distribution")).items()}
    _known = ["A", "B", "C", "D", "F"]
    _extra = sorted(str(g) for g in _grade_dist if g not in _known)
    lines = []
    for grade in [*_known, *_extra]:
        count = int_metric(_grade_dist.get(grade, 0))
        if count <= 0 and grade in _extra:
            continue
        lines.append(f"    {grade}: {'#' * count} ({count})")
    return lines
def _summary_zombie_lines(s: dict) -> list[str]:
    _zombie_dist = dict_or_empty(s.get("zombie_distribution"))
    _known = ["active", "dormant", "zombie", "sunset"]
    _extra = sorted(str(status) for status in _zombie_dist
                    if status not in _known)
    lines = []
    for status in [*_known, *_extra]:
        count = int_metric(_zombie_dist.get(status, 0))
        if count > 0:
            lines.append(f"    {status}: {count}")
    return lines
def _summary_duplicate_lines(s: dict) -> list[str]:
    if int_metric(s.get("duplicates_found", 0)) <= 0:
        return []
    lines = ["", "重复命名:"]
    _pairs = s.get("duplicate_pairs") or []
    if not isinstance(_pairs, (list, tuple, set)):
        _pairs = []
    for pair in _pairs:
        if isinstance(pair, (list, tuple)) and len(pair) >= 2:
            lines.append(f"    {pair[0]} <-> {pair[1]}")
    return lines
def _summary_concern_lines(skills) -> list[str]:
    lines = []
    for skill in skills:
        if not isinstance(skill, dict):
            continue
        _score = as_number(skill.get("overall_score", 0), 0)
        _days = as_number(skill.get("days_since_active", 0), 0)
        _status = _zombie_of(skill)
        if _score < 50 or _status != "active":
            lines.append(
                "    [{}] {:25s} score={:.0f} status={} days_inactive={:.0f}d".format(
                    skill.get("grade", "F"), str(skill.get("skill_name", "")),
                    _score, _status, _days,
                )
            )
    return lines
def print_summary(report: dict[str, Any]) -> str:
    if not isinstance(report, dict) or not report:
        logger.info("[Quality] 无健康报告生成。")
        return ""
    s = dict_or_empty(report.get("summary"))
    lines = [
        "=" * 60,
        "技能健康诊断报告",
        "=" * 60,
        "  {} | 技能数: {} | 均分: {}".format(
            report.get("date", ""), s.get("total_skills", 0), s.get("average_score", 0)
        ),
        "",
        "等级分布:",
    ]
    lines.extend(_summary_grade_lines(s))
    lines.append("")
    lines.append("活跃状态:")
    lines.extend(_summary_zombie_lines(s))
    lines.extend(_summary_duplicate_lines(s))
    lines.append("")
    lines.append("需关注:")
    _skills = report.get("skills") or []
    if not isinstance(_skills, (list, tuple, set)):
        _skills = []
    lines.extend(_summary_concern_lines(_skills))
    lines.append("=" * 60)
    text = "\n".join(lines)
    for line in lines:
        logger.info("%s", line)
    return text
def _filter_active_skills(reputation: dict[str, Any],
                          skill_filter: Any) -> dict[str, Any]:
    if isinstance(skill_filter, str):
        if not skill_filter.strip():
            return reputation
        candidates: list[str] = [skill_filter]
    elif isinstance(skill_filter, (list, set, tuple)):
        candidates = [s.strip() for s in skill_filter
                      if isinstance(s, str) and s.strip()]
        if not candidates:
            return reputation
    else:
        return reputation
    selected: dict[str, Any] = {}
    for name in candidates:
        key = reputation_key(reputation, name)
        if key is not None:
            selected[key] = reputation[key]
    return selected
def _limit_quick_skills(reputation: dict[str, Any],
                        quick: bool) -> dict[str, Any]:
    if not quick:
        return reputation
    return dict(sorted(reputation.items(), key=lambda item: str(item[0]))
                [:_QUICK_SKILL_LIMIT])
def _diagnose_one_skill(
        skill_name: str, reputation: dict[str, Any]
) -> tuple[dict[str, Any] | None, dict[str, str] | None]:
    try:
        return diag_skill(skill_name, reputation.get(skill_name, {})), None
    except Exception as exc:
        logger.warning("[Quality] 技能健康诊断失败(跳过该技能): %s: %s",
                       skill_name, exc, exc_info=True)
        return None, {"skill_name": skill_name, "error": str(exc)[:300]}
def run_health_diag(quick: bool = False,
                    skill_filter: Any = None) -> dict[str, Any] | None:
    logger.info("run_health_diag: 触发健康诊断 (quick=%s, filter=%r)",
                quick, skill_filter)
    raw_reputation = load_skill_reputation()
    if not isinstance(raw_reputation, dict):
        logger.warning("[Quality] 技能声誉数据形态非法(%s)，放弃健康诊断",
                       type(raw_reputation).__name__)
        return None
    reputation = {key: value for key, value in raw_reputation.items()
                  if isinstance(key, str) and isinstance(value, dict)}
    if len(reputation) != len(raw_reputation):
        logger.warning("[Quality] 声誉台账剔除非法键/值条目 %d 个",
                       len(raw_reputation) - len(reputation))
    if not reputation:
        logger.warning("[Quality] 无技能声誉数据")
        return None
    active_skills = _filter_active_skills(reputation, skill_filter)
    active_skills = _limit_quick_skills(active_skills, quick)
    if not active_skills:
        return None
    results = []
    errors: list[dict[str, str]] = []
    for skill_name in active_skills:
        result, error = _diagnose_one_skill(skill_name, reputation)
        if result is not None:
            results.append(result)
        if error is not None:
            errors.append(error)
    grades, zombie_dist, avg_score = _compute_distribution_stats(results)
    duplicates = detect_duplicate_names(list(active_skills.keys()))
    report = _build_health_report(results, grades, zombie_dist, avg_score, duplicates)
    if errors:
        report["errors"] = errors
        summary = report.get("summary")
        if not isinstance(summary, dict):
            summary = {}
        summary["failed_skills"] = len(errors)
        report["summary"] = summary
    _log_health_summary(report)
    print_summary(report)
    return report
_B1_ENGINE_ID = "B1"
def aggregate_report(intermediate_dir: str, output_dir: str,
                    skill_dir: str | None = None) -> str:
    if not skill_dir:
        raise ValueError(
            "aggregate_report: 缺少 skill_dir（报告技能身份不能从 "
            f"output_dir={output_dir!r} 反推）")
    sd_norm = normalize_skill_dir(skill_dir, require_valid=True)
    _agg_guard = PipelineGuard(sd_norm, "aggregate")
    _agg_guard.enter()
    try:
        return _aggregate_report_locked(intermediate_dir, output_dir, sd_norm)
    finally:
        try:
            _agg_guard.exit()
        except Exception as _exit_err:
            logger.warning("[Aggregator] 守卫释放失败(降级): %s", _exit_err,
                           exc_info=True)
def register_backlog_soft(report: dict, skill_dir: str) -> None:
    try:
        _zb_reg = register_cv_findings_snapshot(skill_dir, report)
        logger.info("[Aggregator] 归零台账登记: %d 条新 finding（重复跳过 %d）",
                    _zb_reg.get("registered", 0), _zb_reg.get("skipped_dup", 0))
    except Exception as _zb_e:  # noqa: BLE001
        logger.warning("[Aggregator] 归零台账登记失败（不阻断）: %s", _zb_e)
def _resolve_diag_ctx(skill_dir: str):
    try:
        cache = peek_warmed_cache(skill_dir)
        if cache is not None and hasattr(cache, "slots"):
            return as_diag_ctx(cache)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context=f'_resolve_diag_ctx:bridge:'
                              f'{type(_e).__name__}')
    try:
        return DiagnosticContext(skill_dir)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context=f'_resolve_diag_ctx:fallback:'
                              f'{type(_e).__name__}')
        return None
def _inject_f1_sections(report: dict, intermediate_dir: str,
                        skill_dir: str) -> None:
    try:
        _f1_sections = build_f1_report(intermediate_dir, skill_dir)
        if isinstance(_f1_sections.get("call_chain"), dict):
            report.setdefault("call_chain", _f1_sections["call_chain"])
        if isinstance(_f1_sections.get("blindspots"), dict):
            report.setdefault("blindspots", _f1_sections["blindspots"])
    except Exception as _f1a_exc:  # noqa: BLE001
        logger.warning("[Aggregator] call_chain/blindspots section 注入失败（不阻断）: %s",
                       _f1a_exc)
def _dumps_report_summary(report: dict) -> str:
    try:
        return json.dumps(report.get("summary", {}),
                          ensure_ascii=False, default=str)
    except (TypeError, ValueError, RecursionError) as _sum_exc:
        log_swallowed(__name__, _sum_exc, context='_dumps_report_summary:TypeError+')
        return f"<summary 序列化失败: {_sum_exc}>"
def _cv_engine():
    import jwsgj.xv_confidence_review as engine  # lazy-by-design
    return engine
def _aggregate_report_locked(intermediate_dir: str, output_dir: str,
                             skill_dir: str) -> str:
    agg = ReportAggregator(
        intermediate_dir, output_dir, skill_dir=skill_dir,
        cv_runner=lambda: _cv_engine().CrossValidatorV2().validate(
            intermediate_dir, skill_dir=skill_dir))
    report = agg.build()
    if report.get("_error") is True:
        logger.error(
            "[Aggregator] 聚合构建失败（_error 哨兵），终止治疗/复盘/HTML 消费，不落盘空报告")
        return ""
    _inject_f1_sections(report, intermediate_dir, skill_dir)
    report = apply_health_report(report, skill_dir,
                                 ctx=_resolve_diag_ctx(skill_dir))
    path = agg.write(report)
    if not path:
        logger.error(
            "[Aggregator] 聚合报告落盘失败，终止治疗/复盘/HTML 消费，"
            "不以空路径伪装聚合完成")
        return ""
    logger.info("[Aggregator] 聚合完成: %s", path)
    logger.info("[Aggregator] 摘要: %s", _dumps_report_summary(report))
    log_cv_extract_summary(report)
    register_backlog_soft(report, skill_dir)
    treatment_plan, treatment_plan_path = _generate_treatment_plan_step(
        report, path, skill_dir)
    if treatment_plan is not None:
        _log_treatment_readiness(treatment_plan)
    # 复盘前置门在 _run_retro_step 内部判定：治疗未执行时跳过并告警。
    # 判定结果同时回写到报告 payload，读者能在报告里看到「复盘已推迟」
    # 的明确标注，不会把「治疗未开始」误读成「治疗无效」。
    _retro_outcome = _run_retro_step(skill_dir, path, treatment_plan_path)
    report["retro_outcome"] = dict_or_empty(_retro_outcome)
    emit_aggregate_report_html(report, skill_dir)
    return path
def _generate_treatment_plan_step(report: dict, path: str,
                                  skill_dir: str):
    try:
        treatment_plan = generate_treatment_plan(report, None, skill_dir)
        output_dir_tp = os.path.dirname(path)
        treatment_plan_path = save_treatment_plan(treatment_plan, output_dir_tp)
        _tp = treatment_plan.to_dict()
        _tp_sum = _tp.get("summary", "")
        logger.info("[Aggregator] 治疗方案: %s", _tp_sum)
        return treatment_plan, treatment_plan_path
    except Exception as _e:  # noqa: BLE001
        logger.warning("[Aggregator] 治疗方案生成失败（不阻塞后续步骤）: %s", _e)
        return None, None
def _log_treatment_readiness(treatment_plan) -> None:
    tp_items = treatment_plan.items if hasattr(treatment_plan, "items") else []
    auto_safe = sum(1 for i in tp_items if getattr(i, "auto_safe", False))
    total = len(tp_items)
    logger.info(
        "[Aggregator] 治疗方案就绪: %d 项（%d auto_safe），"
        "请通过独立步骤 API 逐项执行治疗："
        "   %s.run_treatment_step(skill_dir)",
        total, auto_safe, __name__.split(".", 1)[0]
    )
def _treatment_execution_view(skill_dir: str) -> dict | None:
    try:
        view = treatment_exec_result(skill_dir)
    except Exception as _tx_e:  # noqa: BLE001
        logger.warning("[Aggregator-v7] 治疗执行视图读取失败(降级为无执行证据): %s",
                       _tx_e)
        return None
    if not isinstance(view, dict) or not view:
        return None
    if not view.get("details") and not int_metric(view.get("total_items", 0)):
        return None
    return view
# 治疗结算态：只有结算完成才具备复盘的事实基础。未结算（in_progress/
# running/pending 等）或治疗项全部未处理时一律跳过——此时治疗审计只能拿到
# total_items/executed=0，评分函数会把「未开始」当成「无效」，输出
# 「治疗有效性 30%（严重不足）」这类失实结论。
_RETRO_TREATMENT_SETTLED_STATUSES = frozenset({
    "completed", "no_plan", "failed", "error", "skipped", "rolled_back",
})
# 治疗项已处理的计数键：任一非零表示治疗确实推进过，复盘才有事实支撑。
_RETRO_TREATMENT_HANDLED_KEYS = (
    "executed", "succeeded", "fixed", "failed", "error", "rolled_back",
    "skipped", "fp_confirmed", "pending_confirm", "suggestion", "no_fixer",
    "ai_fixed",
)
def _retro_treatment_gate(skill_dir: str) -> tuple[bool, str]:
    """复盘前置门：治疗未执行/未结算时禁止产出复盘报告。

    返回 ``(是否放行, 跳过原因)``；放行时原因为空串。
    """
    view = _treatment_execution_view(skill_dir)
    if view is None:
        return False, "treatment_not_started"
    status = str_or(view.get("status")).strip().lower()
    if status and status not in _RETRO_TREATMENT_SETTLED_STATUSES:
        return False, f"treatment_unsettled:{status}"
    total = int_metric(view.get("total_items", 0))
    handled = sum(int_metric(view.get(key, 0))
                  for key in _RETRO_TREATMENT_HANDLED_KEYS)
    if total > 0 and handled == 0:
        return False, "treatment_not_executed"
    return True, ""
def _run_retro_step(skill_dir: str, path: str,
                    treatment_plan_path: str | None) -> dict:
    """执行复盘反哺并返回结果视图（skipped 时调用方据此留痕）。"""
    _allowed, _skip_reason = _retro_treatment_gate(skill_dir)
    if not _allowed:
        logger.warning(
            "[Aggregator-v7] 复盘反哺跳过（%s）：治疗尚未执行，"
            "复盘报告改由治疗完成后的 fupan_done 阶段生成，"
            "避免把「治疗未开始」误判成「治疗无效」", _skip_reason)
        return {"status": "skipped", "reason": _skip_reason}
    try:
        _retro_report = run_retrospective(
            skill_dir=skill_dir,
            diagnosis_report_path=path,
            treatment_execution=_treatment_execution_view(skill_dir),
            treatment_plan_path=treatment_plan_path,
            output_dir=os.path.dirname(evolution_report_path(skill_dir)),
        )
        _rs = _retro_report.scores if hasattr(_retro_report, 'scores') else {}
        _overall = _rs.get("overall", 0) if isinstance(_rs, dict) else 0
        logger.info("[Aggregator-v7] 复盘反哺完成: 总分=%.1f, 问题=%d, 增强=%d",
                     _overall,
                     len(_retro_report.issues_found) if hasattr(_retro_report, 'issues_found') else 0,
                     len(_retro_report.enhancement_actions) if hasattr(_retro_report, 'enhancement_actions') else 0)
        return {"status": "completed", "overall_score": _overall}
    except Exception as _e:  # noqa: BLE001
        logger.warning("[Aggregator-v7] 复盘反哺执行失败（不阻塞后续步骤）: %s", _e)
        return {"status": "failed", "error": str(_e)[:300]}
def _soft_chain(label: str, fn, *args) -> None:
    try:
        fn(*args)
    except Exception as exc:  # noqa: BLE001
        logger.warning("[ReviewStep] %s失败: %s", label, exc)
def _resolve_intermediate_dir(skill_dir: str, cache=None) -> str | None:
    if cache is not None:
        out_dir = getattr(cache, "output_dir", None) or getattr(cache, "report_dir", None)
        if out_dir:
            cand = diag_intermediate_dir(out_dir)
            if os.path.isdir(cand):
                return cand
    cand = json_artifact_dir(skill_dir)
    if os.path.isdir(cand):
        return cand
    return None
def _sub_engine_result(b1_data: dict, sub_id: str = _B1_ENGINE_ID) -> dict:
    if not isinstance(b1_data, dict):
        return {}
    for host in (b1_data.get("payload"), b1_data):
        result = sub_result(host, sub_id)
        if result is not None:
            return result
    return {}
def _extract_a2_metadata(b1_data: dict | None) -> dict:
    if not isinstance(b1_data, dict):
        return {}
    meta = dict_or_empty(b1_data.get("a2_metadata"))
    if meta:
        return meta
    meta = dict_or_empty(dict_or_empty(b1_data.get("payload")).get("a2_metadata"))
    if meta:
        return meta
    return dict_or_empty(_sub_engine_result(b1_data).get("a2_metadata"))
def _read_b1_intermediate(intermediate_dir: str,
                          freshness_cutoff: str = "") -> dict | None:
    try:
        data = load_intermediate_fused(intermediate_dir, _B1_ENGINE_ID,
                                       strict_provenance=False,
                                       freshness_cutoff=freshness_cutoff)
        if not isinstance(data, dict) or not data or data.get("status") == "corrupted":
            return None
        return data
    except Exception as e:  # noqa: BLE001
        logger.debug("[AntiPatternDensity] 读取 B1 中间结果失败，回退实时执行: %s", e)
        return None
def _antipattern_skip_report(data_source: str, reason: str) -> dict[str, Any]:
    return {
        "status": "skip",
        "findings_count": 0,
        "score": 0.0,
        "total_violations": 0,
        "summary": reason,
        "issues": [],
        "density_hotspots": [],
        "data_source": data_source,
    }
def _acquire_b1_data(skill_dir: str, cache: Any, b1_data: dict | None,
                     run_b1_if_missing: bool,
                     b1_runner: Any = None) -> tuple[dict | None, str]:
    if b1_data is not None:
        return b1_data, "injected"
    inter_dir = _resolve_intermediate_dir(skill_dir, cache)
    if inter_dir:
        b1 = _read_b1_intermediate(inter_dir, get_round_start_ts(skill_dir))
        if b1 is not None:
            return b1, "intermediate"
    if run_b1_if_missing and b1_runner is not None:
        try:
            b1 = b1_runner(skill_dir, cache)
        except Exception as e:  # noqa: BLE001
            logger.warning("[AntiPatternDensity] 回退执行 B1 失败: %s", e)
            b1 = None
        if b1 is not None:
            return b1, "engine1"
    return None, "none"
def _normalize_antipattern_payload(meta: dict) -> tuple[list, list, int]:
    issues = dict_items(meta.get("issues"))
    hotspots = dict_items(meta.get("density_hotspots"))
    total = max(int_or(meta.get("total_violations"), 0), 0)
    return issues, hotspots, total or len(issues)
def run_antipattern_density_report(skill_dir: str,
                                    cache: Any = None,
                                    b1_data: dict | None = None,
                                    run_b1_if_missing: bool = False,
                                    b1_runner: Any = None) -> dict[str, Any]:
    try:
        raw_dir = os.fspath(skill_dir)
    except TypeError:
        return _antipattern_skip_report(
            "none", "反模式密度分析跳过(技能根须为路径)")
    if isinstance(raw_dir, bytes):
        raw_dir = os.fsdecode(raw_dir)
    if not raw_dir.strip():
        return _antipattern_skip_report(
            "none", "反模式密度分析跳过(技能根为空)")
    sd = normalize_skill_dir(raw_dir)
    if not os.path.isdir(sd):
        return _antipattern_skip_report(
            "none", f"反模式密度分析跳过(技能根不存在: {sd})")
    b1, data_source = _acquire_b1_data(
        sd, cache, b1_data, run_b1_if_missing, b1_runner)
    if b1 is None:
        return _antipattern_skip_report(
            data_source, "反模式密度分析跳过(依赖B1的a2_metadata未就绪)")
    meta = _extract_a2_metadata(b1)
    if not meta:
        return _antipattern_skip_report(
            data_source, "反模式密度分析跳过(B1无a2_metadata)")
    issues, density_hotspots, total_violations = _normalize_antipattern_payload(meta)
    score = max(0, 100 - total_violations * 2)
    summary_parts = [
        f"反模式密度分析: {total_violations} 项违规, {len(issues)} 项 findings"
    ]
    if density_hotspots:
        summary_parts.append(f"{len(density_hotspots)} 个密度热点文件")
    return {
        "status": "pass",
        "findings_count": len(issues),
        "score": score,
        "total_violations": total_violations,
        "summary": ", ".join(summary_parts),
        "issues": issues,
        "density_hotspots": density_hotspots,
        "data_source": data_source,
    }
def _apply_density_report(out: dict, skill_dir: str) -> None:
    density = run_antipattern_density_report(skill_dir)
    out["antipattern_density"] = {
        "status": density.get("status"),
        "score": density.get("score"),
        "total_violations": density.get("total_violations"),
        "summary": density.get("summary", ""),
    }
def build_review_quality_augmentation(skill_dir: str, details: object,
                                      confirmed_findings: object) -> dict:
    out: dict = {}
    _soft_chain(
        "质量三键投影",
        lambda: out.update(build_quality_projection(
            details, confirmed_findings)))
    _soft_chain("反模式密度报告", _apply_density_report, out, skill_dir)
    _soft_chain(
        "FP 进化摘要生成",
        lambda: out.update(
            fp_evolution=get_fp_evolution_summary(skill_dir)))
    return out
def _normalize_status_text(value: Any) -> str:
    return value.strip().lower() if isinstance(value, str) else ""
_DR_ITEM_RULES: dict[str, dict] = {
    "fixed": {"count": "fixed"},
    "ai_fixed": {"count": "ai_fixed"},
    "planned": {"count": "planned", "list": "degraded_items", "status": "planned",
                "reason": "已生成修复方案，待 AI 审核执行",
                "action": "通过 run_next_ai_review 逐项审核执行"},
    "failed": {"count": "failed", "list": "degraded_items", "status": "failed",
               "reason": "修复执行失败"},
    "rolled_back": {"count": "rolled_back", "list": "degraded_items",
                    "status": "rolled_back", "reason": "安全验证失败已回滚"},
    "fp_confirmed": {"count": "fp_confirmed", "list": "fp_confirmed_items",
                     "status": "fp_confirmed",
                     "reason": "判定为疑似误报（FP 确认），未进入修复流程",
                     "action": "已入队 AI 语义复核：run_next_ai_review → apply_cv_uncertain_verdict 执行裁决"},
    "pending_confirm": {"count": "pending_confirm", "list": "pending_confirm_items",
                        "status": "pending_confirm",
                        "reason": "非自动安全修复，待 AI 审核执行",
                        "action": "AI 审核并执行：run_ai_manual_fix_step / apply_ai_fix"},
    "suggestion": {"count": "suggestion", "list": "degraded_items",
                   "status": "suggestion", "reason": "已生成修复建议模板",
                   "action": "AI 审核并执行：get_ai_fix_candidates 生成 fixed_source 后 apply_ai_fix 应用"},
    "no_fixer": {"count": "no_fixer", "list": "degraded_items",
                 "status": "no_fixer", "reason": "无可用修复器",
                 "action": "需开发新修复器或手动修复"},
    "skipped": {"count": "skipped", "list": "degraded_items",
                "status": "skipped", "reason": "未知原因跳过"},
    "pending": {"count": "degraded", "list": "degraded_items",
                "status": "pending", "reason": "治疗项未执行（会话中断恢复）",
                "hard_reason": True},
}
_DR_ITEM_RULE_ALIASES: dict[str, str] = {
    "succeeded": "fixed",
    "error": "failed",
}
def _dr_treatment_rule(status: str) -> dict | None:
    return _DR_ITEM_RULES.get(_DR_ITEM_RULE_ALIASES.get(status, status))
def _dr_treatment_item(report: dict, item: dict) -> None:
    if not isinstance(item, dict):
        return
    _status = _normalize_status_text(item.get("status")) or "pending"
    rule = _dr_treatment_rule(_status)
    if rule is None:
        rule = {
            "count": "degraded", "list": "degraded_items",
            "status": _status,
            "reason": f"治疗项状态未知（{_status}），需核查并重跑",
            "hard_reason": True,
        }
    report["treatment"][rule["count"]] = \
        report["treatment"].get(rule["count"], 0) + 1
    list_key = rule.get("list")
    if not list_key:
        return
    detail = item.get("result")
    if not isinstance(detail, dict):
        detail = {}
    report[list_key].append(_dr_build_entry(item, rule, detail))
def _dr_build_entry(item: dict, rule: dict, detail: dict) -> dict:
    entry = {
        "stage": "treatment",
        "index": int_or(item.get("index"), -1),
        "rule_id": str_or(item.get("rule_id")),
        "file_path": str_or(item.get("file_path")),
        "line": max(int_or(item.get("line")), 0),
    }
    if rule.get("status") is not None:
        entry["status"] = rule["status"]
    entry["reason"] = _dr_item_reason(detail, rule)
    if rule.get("action"):
        entry["action"] = rule["action"]
    return entry
def _dr_item_reason(detail: dict, rule: dict) -> str:
    if rule.get("hard_reason"):
        return rule["reason"]
    return (str_or(detail.get("reason")) or str_or(detail.get("error"))
            or rule["reason"])
def _dr_diag_entry(d: dict, status: str, reason: str) -> dict:
    return {
        "stage": "diagnosis",
        "method_id": str_or(d.get("method_id")),
        "method_name": str_or(d.get("method_name")),
        "status": status,
        "reason": reason,
    }
_VERDICT_COUNTER_KEYS: tuple[str, ...] = ("pass", "warn", "fail", "unknown")
_LEGACY_FAIL_STATUSES: frozenset[str] = frozenset({"fail", "failed"})
_VERDICT_FAIL_REASON = (
    "诊断结论未通过：发现 P0 阻断项（方法本身已执行完成，不是执行失败）")
_LEGACY_VERDICT_FAIL_REASON = (
    "诊断结论未通过（历史记录：发现 P0 阻断项，方法本身已执行完成）")
def _empty_verdict_counters() -> dict:
    return {key: 0 for key in _VERDICT_COUNTER_KEYS}
def _dr_record_verdict(report: dict, d: dict, verdict: str,
                       verdict_reason: str, display: str) -> None:
    """记录诊断结论（verdict），与执行健康（status）分账。"""
    _verdict = _normalize_status_text(verdict)
    if _verdict not in _VERDICT_COUNTER_KEYS or _verdict == "unknown":
        return
    counters = report.setdefault("verdict", _empty_verdict_counters())
    counters[_verdict] = counters.get(_verdict, 0) + 1
    if _verdict != "fail":
        return
    report.setdefault("verdict_items", []).append({
        "stage": "diagnosis",
        "method_id": str_or(d.get("method_id")),
        "method_name": str_or(d.get("method_name")),
        "status": display,
        "verdict": "fail",
        "reason": (str_or(verdict_reason) or _VERDICT_FAIL_REASON),
    })
_DR_DIAG_STATUS_RULES: dict[str, tuple[str, str | None]] = {
    "pass": ("passed", None),
    "warn": ("passed", None),
    "ok": ("passed", None),
    # fail 是「诊断结论未通过」而不是「方法执行失败」：方法已产出完整结果，
    # 只是存在 P0 阻断项。执行维度计为 passed，结论单独进 verdict_items。
    "fail": ("passed", None),
    "failed": ("passed", None),
    "timeout": ("failed", "诊断方法执行超时: {status}"),
    "error": ("failed", "诊断方法执行失败: {status}"),
    "blocked": ("degraded", "诊断方法被并发锁阻断，未产出结果，需重跑"),
    "skip": ("skipped", "诊断方法被跳过，未产出结果，需核查依赖并重跑"),
    "pending": ("degraded", "诊断方法未完成（会话中断恢复）"),
    "missing": ("degraded", "诊断中间结果缺失（未产出或已清理），需重跑该方法"),
    "corrupted": ("degraded", "诊断中间结果损坏（不可解析或结构非法），需重跑该方法"),
}
_DR_DIAG_BUCKETS: tuple[str, ...] = ("passed", "failed", "degraded", "skipped")
def _empty_diagnosis_counters() -> dict:
    return {"total": 0,
            **{bucket: 0 for bucket in _DR_DIAG_BUCKETS}}
def _dr_classify_diag_item(d: dict, report: dict) -> None:
    if not isinstance(d, dict):
        return
    raw = d.get("status", "pending")
    display = raw.strip() if isinstance(raw, str) else ""
    if not display:
        display = "pending"
    status = display.lower()
    _verdict = _normalize_status_text(d.get("verdict"))
    _verdict_reason = str_or(d.get("verdict_reason"))
    if status in _LEGACY_FAIL_STATUSES:
        if _verdict not in _VERDICT_COUNTER_KEYS or _verdict == "unknown":
            _verdict = "fail"
        if not _verdict_reason:
            _verdict_reason = _LEGACY_VERDICT_FAIL_REASON
    rule = _DR_DIAG_STATUS_RULES.get(status)
    bucket, reason_tpl = rule or (
        "degraded", "诊断方法状态未知: {status}，需核查并重跑")
    counts = report["diagnosis"]
    counts[bucket] = counts.get(bucket, 0) + 1
    if reason_tpl is not None:
        report["degraded_items"].append(
            _dr_diag_entry(d, display, reason_tpl.format(status=display)))
    _dr_record_verdict(report, d, _verdict, _verdict_reason, display)
def _dr_record_collect_error(report: dict, stage: str, exc: Exception) -> None:
    errors = report.get("collection_errors")
    if not isinstance(errors, list):
        errors = []
        report["collection_errors"] = errors
    errors.append({"stage": stage, "error": str(exc)})
def _dr_mapping_items(report: dict, stage: str, raw: Any,
                      label: str) -> list[dict]:
    items = dict_items(raw)
    if not isinstance(raw, (list, tuple)):
        _dr_record_collect_error(
            report, stage,
            TypeError(f"{label}形态非法: {type(raw).__name__}"))
    elif isinstance(raw, (list, tuple)) and len(items) != len(raw):
        dropped = len(raw) - len(items)
        logger.warning("[DegradationReport] %s含非映射条目 %d 个(已跳过)",
                       label, dropped)
        _dr_record_collect_error(
            report, stage,
            ValueError(f"{label}含非映射条目 {dropped} 个，已跳过"))
    return items
def _dr_collect_diagnosis(sd: str, report: dict) -> None:
    try:
        raw_progress = query_methods_progress(sd)
        if not isinstance(raw_progress, dict):
            raise TypeError(
                f"诊断进度视图非映射: {type(raw_progress).__name__}")
        if not raw_progress:
            raise ValueError(
                "诊断进度视图为空（上游读取失败），无法确认诊断方法状态")
        details_raw = raw_progress.get("details")
        details = _dr_mapping_items(
            report, "diagnosis", details_raw, "诊断明细")
        declared = max(int_or(raw_progress.get("total"), 0), 0)
        treatment_count = 0
        classified = 0
        item_errors = 0
        for d in details:
            try:
                cfg = METHOD_REGISTRY.get(d.get("method_id"))
                if cfg is not None and cfg.domain == "treatment":
                    treatment_count += 1
                    continue
                _dr_classify_diag_item(d, report)
                classified += 1
            except Exception as item_err:  # noqa: BLE001
                item_errors += 1
                logger.warning("[DegradationReport] 诊断方法聚合失败(跳过该项): %s",
                               item_err)
        counted_total = (max(declared - treatment_count, 0)
                         if declared else 0)
        report["diagnosis"]["total"] = max(counted_total, classified)
        if declared and not details:
            _dr_record_collect_error(
                report, "diagnosis",
                ValueError(f"诊断进度声明 total={declared} 但 details 为空"))
        elif declared and counted_total != classified:
            _dr_record_collect_error(
                report, "diagnosis",
                ValueError("诊断明细与声明总数不一致: "
                           f"classified={classified}, declared={counted_total}"))
        if item_errors:
            _dr_record_collect_error(
                report, "diagnosis",
                ValueError(f"{item_errors} 个诊断方法条目聚合失败"))
    except Exception as e:  # noqa: BLE001
        logger.warning("[DegradationReport] 诊断维度失败: %s", e)
        _dr_record_collect_error(report, "diagnosis", e)
def _dr_collect_treatment(sd: str, report: dict) -> None:
    try:
        state = load_treatment_state(sd)
        if not isinstance(state, dict):
            raise TypeError(
                f"治疗状态非映射: {type(state).__name__}")
        raw_items = state.get("items")
        items = _dr_mapping_items(
            report, "treatment", raw_items, "治疗明细")
        declared = max(int_or(state.get("total"), 0), 0)
        report["treatment"]["total"] = max(declared, len(items))
        item_errors = 0
        for item in items:
            try:
                _dr_treatment_item(report, item)
            except Exception as item_err:  # noqa: BLE001
                item_errors += 1
                logger.warning("[DegradationReport] 治疗项聚合失败(跳过该项): %s",
                               item_err)
        if item_errors:
            _dr_record_collect_error(
                report, "treatment",
                ValueError(f"{item_errors} 个治疗条目聚合失败"))
        integrity_reason = str_or(state.get("_state_integrity_reason"))
        if (_normalize_status_text(state.get("status")) == "error"
                or state.get("_state_integrity") == "torn"):
            _dr_record_collect_error(
                report, "treatment",
                ValueError(integrity_reason or
                           "治疗状态为 error，无法确认治疗项终态"))
        if declared and not items:
            _dr_record_collect_error(
                report, "treatment",
                ValueError(f"治疗状态声明 total={declared} 但 items 为空"))
        elif declared and len(items) < declared:
            _dr_record_collect_error(
                report, "treatment",
                ValueError(f"治疗明细 {len(items)} 少于声明 total {declared}"))
            logger.warning("[DegradationReport] 治疗明细 %d 少于声明 total %d，"
                           "报告按声明总数展示", len(items), declared)
    except Exception as e:  # noqa: BLE001
        logger.warning("[DegradationReport] 治疗维度失败: %s", e)
        _dr_record_collect_error(report, "treatment", e)
def _dr_finalize(report: dict) -> int:
    total_degraded = sum(
        len(report[key]) for key in (
            "degraded_items", "pending_confirm_items"))
    verdict = dict_or_empty(report.get("verdict"))
    if verdict.get("fail", 0) > 0:
        report["verdict_status"] = "fail"
    elif verdict.get("warn", 0) > 0:
        report["verdict_status"] = "warn"
    else:
        report["verdict_status"] = "pass"
    if report["diagnosis"]["failed"] > 0 or report["treatment"]["failed"] > 0:
        report["overall_status"] = "failed"
    elif total_degraded > 0 or report.get("collection_errors"):
        report["overall_status"] = "degraded"
    report["recommendations"].extend(_dr_recommendations(report))
    return total_degraded
def _dr_recommendations(report: dict) -> list[str]:
    treatment = report["treatment"]
    recommendation_specs = (
        (len(report.get("pending_confirm_items") or []),
         "发现 {count} 个待 AI 审核执行的真实问题 (run_next_ai_review)"),
        (treatment.get("planned", 0),
         "治疗阶段 {count} 项已生成方案，建议通过 run_next_ai_review 审核执行"),
        (treatment.get("suggestion", 0),
         "治疗阶段 {count} 项仅有修复建议，需由 AI 生成并应用真实修复"),
        (treatment.get("skipped", 0),
         "治疗阶段 {count} 项被跳过，建议核查跳过原因并重跑"),
        (treatment.get("no_fixer", 0),
         "治疗阶段 {count} 项无可用修复器，需开发新修复器"),
        (report["diagnosis"]["failed"],
         "诊断阶段 {count} 个方法执行失败，建议检查依赖"),
        (dict_or_empty(report.get("verdict")).get("fail", 0),
         ("诊断结论未通过：{count} 个方法存在 P0 阻断项"
          "（方法本身已执行完成），需按台账销项后复检")),
        (report["diagnosis"]["skipped"],
         "诊断阶段 {count} 个方法被跳过，建议核查跳过原因并重跑"),
        (report["diagnosis"].get("degraded", 0),
         "诊断阶段 {count} 个方法降级（缺失/损坏/被阻断/未完成），建议按明细重跑该方法"),
        (treatment["failed"], "治疗阶段 {count} 项失败，建议复盘修复器"),
        (treatment["rolled_back"], "治疗阶段 {count} 项回滚，建议检查安全验证"),
        (treatment.get("degraded", 0),
         "治疗阶段 {count} 项未执行或状态未知，建议重跑治疗链路"),
    )
    messages = [message.format(count=count)
                for count, message in recommendation_specs if count > 0]
    failed_stages = sorted({str(e.get("stage")) for e in
                            (report.get("collection_errors") or [])
                            if isinstance(e, dict)})
    if failed_stages:
        messages.append(
            f"{'、'.join(failed_stages)} 维度采集失败，报告为部分视图，建议修复后重跑")
    return messages
def _empty_treatment_counters() -> dict:
    counters = {"total": 0}
    for rule in _DR_ITEM_RULES.values():
        counters.setdefault(rule["count"], 0)
    return counters
def generate_degradation_report(skill_dir: str) -> dict:
    report = {
        "generated_at": timestamp_human(),
        "overall_status": "completed",
        "verdict_status": "pass",
        "diagnosis": _empty_diagnosis_counters(),
        "verdict": _empty_verdict_counters(),
        "verdict_items": [],
        "treatment": _empty_treatment_counters(),
        "collection_errors": [],
        "degraded_items": [],
        "fp_confirmed_items": [],
        "pending_confirm_items": [],
        "recommendations": [],
    }
    _dr_collect_diagnosis(skill_dir, report)
    _dr_collect_treatment(skill_dir, report)
    total_degraded = _dr_finalize(report)
    logger.info("[DegradationReport] %s, degraded=%d, fp=%d",
                 report["overall_status"], total_degraded, len(report["fp_confirmed_items"]))
    return report
def _degradation_payload(report: dict) -> dict:
    def _copy_list(value: Any) -> list:
        if not isinstance(value, (list, tuple)):
            return []
        return [dict(item) if isinstance(item, dict) else item
                for item in value]
    return {
        "overall_status": report.get("overall_status"),
        "verdict_status": report.get("verdict_status"),
        "generated_at": report.get("generated_at"),
        "diagnosis": dict(dict_or_empty(report.get("diagnosis"))),
        "verdict": dict(dict_or_empty(report.get("verdict"))),
        "verdict_items": _copy_list(report.get("verdict_items")),
        "treatment": dict(dict_or_empty(report.get("treatment"))),
        "collection_errors": _copy_list(report.get("collection_errors")),
        "degraded_items": _copy_list(report.get("degraded_items")),
        "fp_confirmed_items": _copy_list(report.get("fp_confirmed_items")),
        "pending_confirm_items": _copy_list(report.get("pending_confirm_items")),
        "recommendations": _copy_list(report.get("recommendations")),
    }
def _emit_degradation_html(skill_dir: str, report: dict, out: dict) -> None:
    try:
        _deg_html = dict_or_empty(
            generate_html_report(report, skill_dir, "degradation"))
        _deg_path = str_or(
            dict_or_empty(_deg_html.get("data")).get("path"))
        if _deg_path:
            out["degradation_report_html"] = _deg_path
            logger.info("[AutoEnhanceStep] 降级报告 HTML 已生成: %s",
                        _deg_path)
    except Exception as _dhe:  # noqa: BLE001
        logger.warning("[AutoEnhanceStep] 降级报告 HTML 生成失败(不阻断): %s",
                       _dhe)
def attach_degradation_report(skill_dir: str, out: dict) -> None:
    if not isinstance(out, dict):
        logger.warning("[AutoEnhanceStep] 输出容器非 dict(%s)，降级报告不附加",
                       type(out).__name__)
        return
    try:
        report = generate_degradation_report(skill_dir)
        out["_degradation_report"] = _degradation_payload(report)
        _emit_degradation_html(skill_dir, report, out)
        logger.info("[AutoEnhanceStep] 降级报告已自动生成: %s",
                    report.get("overall_status"))
    except Exception as de:  # noqa: BLE001
        logger.warning("[AutoEnhanceStep] 降级报告生成失败: %s", de)
def _as_str_list(value: Any) -> list[str]:
    if isinstance(value, (str, bytes, os.PathLike)):
        text = os.fsdecode(os.fspath(value))
        return [text] if text else []
    if isinstance(value, (list, tuple, set, frozenset)):
        items: list[str] = []
        for item in value:
            if item is None:
                continue
            if isinstance(item, (str, bytes, os.PathLike)):
                text = os.fsdecode(os.fspath(item))
            else:
                text = str(item)
            if text:
                items.append(text)
        return items
    return []
_DEFAULT_BASELINE_COMMIT = "HEAD~1"
_BASELINE_MODE_COMMIT = "commit"
_BASELINE_MODE_EMPTY_TREE = "empty_tree"
class RegressionCrossValidator:
    def __init__(self, skill_dir: str,
                 baseline_commit: str = _DEFAULT_BASELINE_COMMIT):
        try:
            raw_dir = os.fspath(skill_dir)
        except TypeError as exc:
            raise TypeError(
                "RegressionCrossValidator: skill_dir 须为路径"
            ) from exc
        if isinstance(raw_dir, bytes):
            raw_dir = os.fsdecode(raw_dir)
        if not raw_dir.strip():
            raise ValueError("RegressionCrossValidator: skill_dir 不能为空")
        baseline = (baseline_commit.strip()
                    if isinstance(baseline_commit, str) else "")
        if baseline.startswith("-"):
            raise ValueError(
                "RegressionCrossValidator: baseline_commit 不得以 '-' 开头: "
                f"{baseline_commit!r}")
        self.skill_dir = os.path.abspath(raw_dir)
        self.baseline_commit = baseline or _DEFAULT_BASELINE_COMMIT
        self.baseline_ref = ''
        self.baseline_mode = ''
    def run(self) -> dict[str, Any]:
        if not self._is_git_repo():
            return self._empty_result(
                'not a git repository', degraded=True)
        baseline_ref = self._resolve_baseline_ref()
        if not baseline_ref:
            return self._empty_result('baseline resolve failed')
        changed_files = self._get_changed_files(baseline_ref)
        if changed_files is None:
            return self._empty_result('git diff failed')
        return {
            'changed_files': changed_files,
            'baseline_commit': self.baseline_commit,
            'baseline_ref': baseline_ref,
            'baseline_mode': self.baseline_mode,
            'error': None,
        }
    def _empty_result(self, reason: str, *,
                      degraded: bool = False) -> dict[str, Any]:
        """无法比对变更集时的结构化结果。

        ``error`` 保留 reason 供调用方留痕。只有明确的环境不适用（非 Git
        工作区）才设置 ``degraded=True``；基线解析和 Git 命令执行失败必须
        保持非降级错误，使 Stage2a 返回 failed，而不是零变更的 completed。
        """
        return {
            'changed_files': [],
            'baseline_commit': self.baseline_commit,
            'baseline_ref': '',
            'baseline_mode': '',
            'error': reason,
            'degraded': degraded,
            'degraded_reason': reason if degraded else '',
        }
    def _resolve_baseline_ref(self) -> str:
        if self.baseline_ref:
            return self.baseline_ref
        result = self._git('git rev-parse baseline',
                           ['rev-parse', '--verify', '--quiet',
                            f'{self.baseline_commit}^{{commit}}'], 5)
        if result is None:
            return ''
        resolved = result.stdout.strip() if result.returncode == 0 else ''
        if resolved:
            self.baseline_ref = resolved
            self.baseline_mode = _BASELINE_MODE_COMMIT
            return self.baseline_ref
        if self.baseline_commit != _DEFAULT_BASELINE_COMMIT:
            logger.warning(
                '[RegressionCV] 指定基线 %s 不是可达提交，回归基线解析失败',
                self.baseline_commit)
            return ''
        graph_probe = self._git(
            'git history probe', ['rev-list', '--parents', '-n', '1', '--all'], 5)
        if graph_probe is None or graph_probe.returncode != 0:
            detail = graph_probe.stderr.strip() if graph_probe is not None else 'probe failed'
            logger.warning(
                '[RegressionCV] 默认基线 %s 缺失且历史对象图不可读，'
                '拒绝按空树扩大回归范围: %s', self.baseline_commit, detail)
            return ''
        empty_tree_ref = self._resolve_empty_tree_ref()
        if not empty_tree_ref:
            return ''
        self.baseline_ref = empty_tree_ref
        self.baseline_mode = _BASELINE_MODE_EMPTY_TREE
        logger.info(
            '[RegressionCV] 基线 %s 不存在(首提交仓库/浅克隆)，'
            '按空树基线比较全部跟踪文件', self.baseline_commit)
        return self.baseline_ref
    def _resolve_empty_tree_ref(self) -> str:
        result = self._git(
            'git empty tree', ['hash-object', '-t', 'tree', '--stdin'],
            5, input_text='')
        if result is None or result.returncode != 0:
            detail = result.stderr.strip() if result is not None else 'probe failed'
            logger.warning('[RegressionCV] 空树基线对象解析失败: %s', detail)
            return ''
        return result.stdout.strip()
    def _git(self, label: str, args: list[str], timeout: int,
             *, input_text: str | None = None) -> subprocess.CompletedProcess[str] | None:
        git_exe = shutil.which('git')
        if git_exe is None:
            logger.debug('[RegressionCV] %s skipped: git not found on PATH', label)
            return None
        try:
            return subprocess.run([git_exe, *args], cwd=self.skill_dir, capture_output=True, text=True, input=input_text, encoding='utf-8', errors='replace', timeout=timeout, check=False)  # jwsgj:suppress SYM-TAINT
        except (subprocess.SubprocessError, FileNotFoundError, OSError) as e:
            logger.debug('[RegressionCV] %s error: %s', label, e)
            return None
    def _is_git_repo(self) -> bool:
        result = self._git('git repo check', ['rev-parse', '--is-inside-work-tree'], 5)
        return bool(result) and result.returncode == 0 and (result.stdout.strip() == 'true')
    @staticmethod
    def _is_python_source_file(path: str) -> bool:
        return path.lower().endswith('.py')
    def _is_existing_python_source_file(self, path: str) -> bool:
        return (self._is_python_source_file(path)
                and os.path.isfile(os.path.join(self.skill_dir, path)))
    def _get_changed_files(self, baseline_ref: str) -> list[str] | None:
        result = self._git('git diff', ['diff', '--relative', '--name-only', '-z',
                                        baseline_ref], 10)
        if result is None:
            return None
        if result.returncode != 0:
            logger.warning('git diff failed: %s', result.stderr.strip())
            return None
        changed = [f for f in result.stdout.split('\x00')
                   if self._is_python_source_file(f)]
        untracked = self._get_untracked_py_files()
        if untracked is None:
            return None
        return _reg_merge_untracked(changed, untracked)
    def _get_untracked_py_files(self) -> list[str] | None:
        result = self._git('git ls-files', ['ls-files', '--others', '--exclude-standard', '-z'], 10)
        if result is None:
            return None
        if result.returncode != 0:
            logger.warning('git ls-files failed: %s', result.stderr.strip())
            return None
        return [f for f in result.stdout.split('\x00')
                if self._is_existing_python_source_file(f)]
def _reg_merge_untracked(changed: list[str], untracked: list[str]) -> list[str]:
    if not untracked:
        return changed
    seen = set(changed)
    return changed + [f for f in untracked if f not in seen]
def _collect_regression_ctx(ctx: PipelineContext) -> tuple[dict | None, str]:
    try:
        raw = RegressionCrossValidator(skill_dir=ctx.skill_dir).run()
    except Exception as _reg_e:  # noqa: BLE001
        logger.warning('[Stage2a] 回归CV跳过: %s', _reg_e)
        return None, str(_reg_e)[:300]
    if not isinstance(raw, dict):
        return None, f"invalid regression result: {type(raw).__name__}"
    # degraded=True 是「环境不适用」而非「分析失败」：error 留痕但不升级为
    # step_failed，否则非 git 技能目录永远跑不完管线。
    _err = "" if raw.get("degraded") is True else str_or(raw.get("error"))
    regression_ctx = normalize_regression_handoff(raw, 'Stage2a')
    if regression_ctx is None and not _err:
        _err = "invalid regression result: changed_files must be a list"
    return regression_ctx, _err
def _fill_regression_result(result: dict, regression_ctx: dict | None, ctx_path: str) -> None:
    changed_files = _as_str_list((regression_ctx or {}).get('changed_files'))
    result['regression_ctx_path'] = ctx_path
    result['has_changes'] = bool(changed_files)
    result['changed_files_count'] = len(changed_files)
    result['changed_files'] = changed_files
def run_stage2a_regression_cv(ctx: PipelineContext) -> dict:
    stage_start = time.time()
    ts = timestamp_ms()
    logger.info('[Stage2a] 回归CV上下文生成开始: %s', timestamp_human())
    result = {'stage': 'regression_cv', 'timestamp': ts, 'status': 'running'}
    try:
        _regression_ctx, _reg_error = _collect_regression_ctx(ctx)
        if _regression_ctx is not None:
            logger.info('[Stage2a] 回归CV: %d changed files detected',
                        len(_as_str_list(_regression_ctx.get('changed_files'))))
        ctx_path = save_regression_handoff(
            ctx.skill_dir, ctx.json_artifact_dir, _regression_ctx)
        _fill_regression_result(result, _regression_ctx, ctx_path)
        _degraded_reason = str_or((_regression_ctx or {}).get('degraded_reason'))
        if _degraded_reason:
            result['regression_degraded'] = _degraded_reason
            logger.warning(
                '[Stage2a] 回归CV降级跳过（无变更集可比对）: %s', _degraded_reason)
        if _reg_error:
            result['regression_error'] = _reg_error
        result['status'] = 'failed' if _reg_error else 'completed'
        result['elapsed_s'] = elapsed_seconds(stage_start)
        if _reg_error:
            logger.warning(
                '[Stage2a] 回归CV未完成: %s, %.1fs',
                _reg_error, result['elapsed_s'])
        else:
            logger.info(
                '[Stage2a] 回归CV完成: has_changes=%s, %.1fs',
                result['has_changes'], result['elapsed_s'])
    except Exception as e:
        result['status'] = 'failed'
        result['error'] = str(e)[:500]
        result['elapsed_s'] = elapsed_seconds(stage_start)
        logger.exception('[Stage2a] 回归CV失败')
    ctx.stages['stage2a'] = result
    return result
def _record_cv_backlog_registration(skill_dir: str, cv_report: dict,
                                    result: dict) -> None:
    try:
        registration = register_cv_findings_snapshot(skill_dir, cv_report)
    except Exception as exc:
        logger.warning("[Stage2b] 归零台账登记异常: %s", exc, exc_info=True)
        registration = {"ok": False, "error": str(exc)[:300]}
    if not isinstance(registration, dict):
        logger.warning("[Stage2b] 归零台账登记返回非 dict(%s)",
                       type(registration).__name__)
        registration = {
            "ok": False,
            "error": f"invalid registration result: {type(registration).__name__}",
        }
    result["zero_backlog_registration"] = registration
    if not registration.get("ok"):
        detail = registration.get("error", "unknown")
        logger.warning("[Stage2b] 归零台账登记失败: %s", detail)
        raise RuntimeError(f"归零台账登记失败，Stage2b 不得提交: {detail}")
def run_stage2b_main_cv(ctx: PipelineContext) -> dict:
    stage_start = time.time()
    ts = timestamp_ms()
    logger.info("[Stage2b] 主交叉验证开始: %s", timestamp_human())
    result = {
        "timestamp": ts,
        "status": "running",
    }
    try:
        regression_ctx = take_regression_handoff(ctx.skill_dir,
                                                ctx.json_artifact_dir)
        result, cv_report = _cv_engine().run_stage2b_execute(ctx, regression_ctx)
        baseline_info = load_stage2b_baseline(ctx.skill_dir, result)
        # 归零台账登记是提交前置门：登记失败即「Stage2b 不得提交」，必须先于
        # CV 报告落盘与 mem_bus 直通执行；否则未登记的 CV 结果会被
        # load_cv_report_tolerant 等消费方当成本轮事实读取。登记只依赖内存中的
        # cv_report，不依赖落盘路径，顺序调整不改变成功路径行为。
        _record_cv_backlog_registration(ctx.skill_dir, cv_report, result)
        persist_cv_reports(ctx.skill_dir, ctx.json_artifact_dir,
                           cv_report, result, ts)
        persist_stage2b_baseline(ctx.skill_dir, cv_report, result,
                                 baseline_info,
                                 query_methods_progress(ctx.skill_dir))
        clear_regression_handoff(ctx.json_artifact_dir, ctx.skill_dir)
        result["status"] = "completed"
        result["elapsed_s"] = elapsed_seconds(stage_start)
        _total, _suppressed, _rules = _cv_engine().summarize_cv_result(result)
        logger.info("[Stage2b] 主交叉验证完成: %d findings, %d 抑制, %d 规则触发 (耗时 %.1fs)",
                     _total, _suppressed, _rules, result["elapsed_s"])
    except Exception as e:
        result["status"] = "failed"
        result["error"] = str(e)[:500]
        result["traceback"] = traceback.format_exc()[:1000]
        logger.exception("[Stage2b] 主交叉验证失败")
    ctx.stages["stage2b"] = result
    return result

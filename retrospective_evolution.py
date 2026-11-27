from __future__ import annotations  # noqa: I001
import json
import logging
import os
import re
import time
from collections import Counter, defaultdict
from collections.abc import Iterable
from dataclasses import dataclass
from typing import Any
from jwsgj.diag_guard_io import (
    atomic_write_text,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
)
from jwsgj.diag_shared_ast_views import register_cache_release
from jwsgj.diag_types_defs import severity_rank_of_text
from jwsgj.diag_types_normalize import (
    as_item_list,
    as_list,
    as_num,
    as_pure_count,
    as_str,
    dict_or_empty,
    finding_file_key,
    int_or,
    is_finite_num,
    is_placeholder_rule_id,
    is_real_number,
    norm_rule_id,
    normalize_confidence,
    now_iso,
    plan_index,
    require_dict,
    severity_literal_from_rank,
    signal_bool,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    FIELD_METHOD_THRESHOLDS,
    FIELD_REGRESSION_FAILED,
    FIELD_ROUTED_TO_FIXER,
    FIELD_SAFETY_VERIFIER_USED,
    FIELD_SIDE_EFFECTS_DETECTED,
    FIELD_SUGGESTED_VALUE,
    FIELD_TOTAL_INPUT_FINDINGS,
    SUMMARY_STATUS_BUCKETS,
    TX_FIXED_STATUSES,
    TX_ROLLED_BACK_STATUSES,
    register_review_provider,
)
from jwsgj.fix_guide_rule_identity import resolve_rule_alias
from jwsgj.fp_rules_judge import (
    finding_line_no,
    is_known_fp,
    load_fp_rules,
    load_fp_tracker_rates,
    load_historical_fp_rules,
    rules_of,
    suppression_min_severity,
)
from jwsgj.log_analysis import (
    load_bug_intercepts,
    load_defense_feedback_events,
)
from jwsgj.log_config import log_swallowed, write_defense_feedback
from jwsgj.retrospective_ledger import (
    _required_write_lock,
    append_enhancement_entry,
    dump_json_text,
    load_retrospective_summary,
    normalized_enhancement_entries,
    persist_review_enhancements,
    read_enhancement_log,
    save_enhancement_log,
)
from jwsgj.runtime_paths import (
    evolution_report_path,
    fp_tracker_path,
    fp_tracker_rules_path,
    read_evolution_section,
    write_evolution_section,
)
from jwsgj.treatment_state import (
    AUTO_FIXED_STATUSES,
    DEFAULT_COUNTED_STATUSES,
    FAILED_STATUSES,
    fp_item_identity,
    iter_unique_rule_observations,
    load_treatment_items,
    load_treatment_state,
    mark_item_fp_confirmed,
    normalize_item_severity,
    read_treatment_state_items,
    save_treatment_state,
)
from jwsgj.xv_cv_report_assemble import extract_cv_stats
from jwsgj.xv_intermediate_store import get_round_start_ts
from jwsgj.runtime_scope import canonical_path
__all__ = [
    "BUG_INTERCEPT_HIGH_FREQ_THRESHOLD",
    "HIGH_FP_THRESHOLD",
    "MIN_SAMPLE_SIZE",
    "VERY_HIGH_FP_THRESHOLD",
    "HistoricalLessonsInjector",
    "absorb_cv_feedback",
    "apply_cv_feedback",
    "apply_status_map_to_details",
    "batch_fp_marking",
    "batch_mark_fp_confirmed",
    "build_fix_route_report",
    "build_status_map_from_items",
    "clear_feedback_history",
    "collect_diagnostic_defense_signals",
    "collect_stage6a_improvements",
    "cv_stats_from_report",
    "derive_regression_status",
    "generate_fix_suggestions",
    "generate_fp_driven_enhancements",
    "get_fp_evolution_summary",
    "latest_status_rows",
    "merge_treatment_state_details",
    "persist_review_enhancements_step",
    "record_defense_feedback",
    "record_main_cv_defense_feedback",
    "record_regression_cv_defense_feedback",
    "run_defense_feedback_step",
    "run_feedback_loop_stage",
    "run_fp_evolution_step",
    "summarize_defense_feedback",
    "zero_batch_fp_result",
]
logger = logging.getLogger(__name__)
_DEFAULT_SKILL_DIR = ""
def _rec_get(record: Any, key: str, default: Any = None) -> Any:
    if isinstance(record, dict):
        return record.get(key, default)
    return getattr(record, key, default)
def _status_text(value: Any) -> str:
    return value.strip().lower() if isinstance(value, str) else ""
def _record_status(record: Any) -> str:
    return _status_text(_rec_get(record, "status", ""))
def _normalize_statuses(
    counted_statuses: tuple[str, ...] | None,
) -> tuple[str, ...]:
    if counted_statuses is None:
        return DEFAULT_COUNTED_STATUSES
    if isinstance(counted_statuses, str):
        text = _status_text(counted_statuses)
        return (text,) if text else ()
    if isinstance(counted_statuses, (list, set, frozenset, tuple)):
        return tuple(
            text for text in (_status_text(s) for s in counted_statuses) if text)
    return DEFAULT_COUNTED_STATUSES
_HOTSPOT_P1_COUNT = 5
def _hotspot_priority(count: int) -> str:
    return "P1" if count >= _HOTSPOT_P1_COUNT else "P2"
def _count_status_keys(results, counted_statuses, key_of) -> Counter:
    counted = _normalize_statuses(counted_statuses)
    keys = []
    for record in list(results or []):
        if _record_status(record) not in counted:
            continue
        key = key_of(record)
        if key:
            keys.append(key)
    return Counter(keys)
def _rule_key(record: Any) -> str:
    raw = _rec_get(record, "rule_id", "")
    return resolve_rule_alias(str(raw)) if raw else ""
def _file_key(record: Any) -> str:
    raw = (_rec_get(record, "file", None)
           or _rec_get(record, "file_path", "") or "")
    return finding_file_key(raw)
def _suggest_from_failures(
        failed: list[Any] | tuple[Any, ...]) -> list[dict[str, Any]]:
    if not failed:
        return []
    return [{"failure": str(f), "suggestion": "见日志详情"} for f in failed[:10]]
_HOTSPOT_TRIGGER_COUNT = 3
_HOTSPOT_TOP_N = 10
def _suggestions_from_counts(
    counts: Counter, *, category: str, key_name: str,
    message: str,
) -> list[dict[str, Any]]:
    ranked = sorted(
        counts.items(), key=lambda kv: (-kv[1], str(kv[0])))[:_HOTSPOT_TOP_N]
    return [
        {
            "priority": _hotspot_priority(count),
            "category": category,
            key_name: key,
            "count": count,
            "suggestion": message.format(key=key, count=count),
        }
        for key, count in ranked
        if count >= _HOTSPOT_TRIGGER_COUNT
    ]
def _suggest_from_quality(
        quality_result: dict[str, Any] | None) -> list[dict[str, Any]]:
    if not isinstance(quality_result, dict) or not quality_result:
        return []
    suggestions = _quality_gate_suggestions(quality_result)
    suggestions.extend(_weak_dimension_suggestions(
        quality_result.get("dimension_scores")))
    return suggestions
def _quality_gate_suggestions(quality_result: dict) -> list[dict[str, Any]]:
    if quality_result.get("gate") != "blocker":
        return []
    score = quality_result.get("score")
    has_score = is_finite_num(score)
    return [{
        "priority": "P0",
        "category": "quality_gate",
        "suggestion": "质量门控未通过,建议先修复所有P0再提交",
        "reason": f"当前评分{score}/100" if has_score else "当前评分未知",
    }]
_WEAK_DIM_SCORE = 70
_WEAK_DIM_TOP_N = 3
def _weak_dimension_suggestions(dim_scores: Any) -> list[dict[str, Any]]:
    if not isinstance(dim_scores, dict):
        return []
    weak_dims = [
        (dim, score) for dim, score in dim_scores.items()
        if is_finite_num(score) and score < _WEAK_DIM_SCORE
    ]
    return [{
        "priority": "P2",
        "category": "dimension_improvement",
        "suggestion": f"{dim}维度评分{score},建议针对性改进",
        "reason": f"低于{_WEAK_DIM_SCORE}分的维度存在系统性缺陷",
    } for dim, score in sorted(
        weak_dims, key=lambda x: (x[1], str(x[0])))[:_WEAK_DIM_TOP_N]]
def generate_fix_suggestions(
    results: Iterable[Any],
    quality_result: dict[str, Any] | None = None,
    counted_statuses: tuple[str, ...] = DEFAULT_COUNTED_STATUSES,
) -> list[dict[str, Any]]:
    results = as_item_list(results, log_tag="generate_fix_suggestions.results")
    failed = [r for r in results if _record_status(r) in FAILED_STATUSES]
    suggestions: list[dict[str, Any]] = []
    suggestions.extend(_suggest_from_failures(failed))
    suggestions.extend(_suggestions_from_counts(
        _count_status_keys(results, counted_statuses, _rule_key),
        category="rule_frequency", key_name="rule_id",
        message="规则 {key} 触发 {count} 次，建议系统性修复该类问题",
    ))
    suggestions.extend(_suggestions_from_counts(
        _count_status_keys(results, counted_statuses, _file_key),
        category="file_hotspot", key_name="file",
        message="文件 {key} 有 {count} 个修复项，建议重点重构",
    ))
    suggestions.extend(_suggest_from_quality(quality_result))
    return suggestions
def _build_fix_evolution_improvements(skill_dir: str) -> list:
    items = read_treatment_state_items(skill_dir)
    if not items:
        return []
    return generate_fix_suggestions(items)
def collect_stage6a_improvements(skill_dir: str, result: dict) -> list:
    try:
        _fx_suggestions = _build_fix_evolution_improvements(skill_dir)
    except Exception as _fx_err:  # noqa: BLE001
        logger.warning("[FixEvolution] 修复进化建议生成跳过: %s", _fx_err)
        _fx_suggestions = []
    result["fix_evolution_suggestions"] = _fx_suggestions
    _fx_improvements = [
        f"[修复进化][{s.get('category', 'misc')}] {s.get('suggestion', '')}（{s.get('priority', 'P2')}）"
        for s in _fx_suggestions if isinstance(s, dict)
    ]
    if _fx_suggestions:
        logger.info("[FixEvolution] 修复进化建议: %d 条（规则频率/文件热点等维度）",
                    len(_fx_suggestions))
    return _fx_improvements
_FEEDBACK_HISTORY: list[tuple[str, dict[str, Any]]] = []
_CATEGORY_SUGGESTIONS: dict[str, str] = {
    "circular": (
        "循环依赖矛盾: 建议复核导入图、动态导入证据与分层环判定是否一致"
    ),
    "dead_code": (
        "死代码矛盾: 建议复核消费者扫描、动态引用与依赖声明是否一致"
    ),
    "gate_miss": (
        "门禁漏判矛盾: 建议检查诊断发现是否完整进入审查与阻断链，并补充反例"
    ),
}
_REGRESSION_SUGGESTION = (
    "回归测试状态={status}: 建议核对安全验证是否覆盖导致回归的代码路径，"
    "并补充对应的定向回归测试"
)
_REGRESSION_FAILURE_STATUSES = frozenset({"fail", "failed", "error"})
_FIX_SAFETY_SUGGESTION = (
    "fix_safety矛盾: 建议检查修复器的副作用边界声明，"
    "确认 affected_callers 是否完整覆盖了受影响的调用方"
)
def _normalize_contradictions(payload: Any) -> list:
    if not payload:
        return []
    if not isinstance(payload, (list, tuple)):
        logger.warning("[DefenseFeedback] contradictions 载荷非法(%s)，降级为空清单",
                       type(payload).__name__)
        return []
    raw = list(payload)
    cleaned = [ct for ct in raw if isinstance(ct, dict)]
    skipped = len(raw) - len(cleaned)
    if skipped:
        logger.warning("[DefenseFeedback] 矛盾清单跳过 %d 条非字典条目", skipped)
    return cleaned
def _contradiction_blob(ct: dict) -> str:
    locator = str(ct.get("locator", ""))
    ctype = str(ct.get("contradiction_type", ""))
    families = ct.get("evidence_families")
    families = (list(families)
                if isinstance(families, (list, tuple, set, frozenset))
                else [])
    return (locator + " " + ctype + " " + " ".join(str(f) for f in families)).lower()
_CONTRADICTION_CATEGORY_HINTS = (
    ("fix_safety", ("fix_safety", "fixer", "fix_vs", "修复安全", "修复器")),
    ("circular", ("circular", "cycle", "循环依赖", "循环导入")),
    ("dead_code", ("dead_code", "deadcode", "dead_vs", "死代码")),
)
_GATE_MISS_RE = re.compile(r"\bgate\b|\bgate_|门禁")
_CLASSIFY_TOKEN_RE = re.compile(r"[^a-z0-9_\u3400-\u4dbf\u4e00-\u9fff]+")
def _classify_tokens(text: str) -> tuple[str, ...]:
    return tuple(t for t in _CLASSIFY_TOKEN_RE.split(text.lower()) if t)
def _classify_contradiction(ct: dict) -> str:
    blob = _contradiction_blob(ct or {})
    tokens = _classify_tokens(blob)
    for category, hints in _CONTRADICTION_CATEGORY_HINTS:
        if any(token.startswith(hint)
               for hint in hints for token in tokens):
            return category
    if _GATE_MISS_RE.search(blob):
        return "gate_miss"
    return "other"
def _build_defense_recommendations(
    by_category: dict[str, int],
    regression_status: str = "",
) -> list[str]:
    recommendations: list[str] = []
    fix_safety_count = by_category.get("fix_safety", 0)
    if fix_safety_count:
        recommendations.append(
            f"规则复核: fix_safety矛盾x{fix_safety_count}（修复后仍有高危发现），建议人工复核"
            "相关修复器的 auto_safe 风险标记、风险元数据与误报豁免规则是否匹配")
        recommendations.append(_FIX_SAFETY_SUGGESTION)
    if regression_status in _REGRESSION_FAILURE_STATUSES:
        recommendations.append(_REGRESSION_SUGGESTION.format(status=regression_status))
    for category, suggestion in _CATEGORY_SUGGESTIONS.items():
        if by_category.get(category) and suggestion not in recommendations:
            recommendations.append(suggestion)
    if by_category.get("other"):
        recommendations.append(
            f"其他类型矛盾x{by_category['other']}: 建议复核产生冲突结论的规则族"
            "及其统一注册、证据和判定口径"
        )
    return recommendations
def _categorize(contradictions: list) -> dict[str, int]:
    by_category: dict[str, int] = {}
    for ct in contradictions:
        if isinstance(ct, dict):
            category = _classify_contradiction(ct)
            by_category[category] = by_category.get(category, 0) + 1
    return by_category
def _feedback_scope_key(skill_dir: str) -> str:
    if not skill_dir:
        return ""
    try:
        return canonical_path(skill_dir)
    except (OSError, TypeError, ValueError) as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc,
                      context=f'_feedback_scope_key:{type(_swallowed_exc).__name__}')
        return ""
def record_defense_feedback(
    contradictions: list | None = None,
    regression_status: str = "",
    skill_dir: str = _DEFAULT_SKILL_DIR,
) -> dict[str, Any]:
    contradictions = _normalize_contradictions(contradictions)
    regression_status = _status_text(regression_status)
    by_category = _categorize(contradictions)
    recommendations = _build_defense_recommendations(
        by_category, regression_status
    )
    fix_safety_count = by_category.get("fix_safety", 0)
    entry = {
        "contradiction_count": len(contradictions),
        "fix_safety_count": fix_safety_count,
        "regression_status": regression_status,
        "recommendations": recommendations,
        "by_category": by_category,
    }
    _scope = _feedback_scope_key(skill_dir)
    _FEEDBACK_HISTORY.append((_scope, entry))
    summary = {
        "feedback_count": sum(
            1 for _entry_scope, _ in _FEEDBACK_HISTORY
            if _entry_scope == _scope),
        "recommendations": recommendations,
        "fix_safety_detected": fix_safety_count > 0,
        "by_category": by_category,
        "contradiction_count": entry["contradiction_count"],
        "regression_status": regression_status,
    }
    try:
        write_defense_feedback(**entry, skill_dir=skill_dir or "")
    except (OSError, TypeError, ValueError):
        logger.warning("defense_feedback 事件落盘失败（降级）", exc_info=True)
    if recommendations:
        logger.info(
            "[DefenseFeedback] 记录反馈: 矛盾 %d 条, 回归状态=%s, 生成 %d 条规则迭代建议",
            entry["contradiction_count"], regression_status or "n/a",
            len(recommendations),
        )
    return summary
def record_regression_cv_defense_feedback(sd: str, status: str) -> None:
    status = _status_text(status)
    try:
        record_defense_feedback(
            contradictions=None,
            regression_status=(
                "pass" if status == "completed"
                else "fail" if status in _REGRESSION_FAILURE_STATUSES
                else ""),
            skill_dir=sd,
        )
    except Exception as _fb_err:  # noqa: BLE001
        log_swallowed(__name__, _fb_err,
                      context=(f'record_regression_cv_defense_feedback:'
                               f'{type(_fb_err).__name__}'))
def record_main_cv_defense_feedback(sd: str, result: dict) -> None:
    try:
        _report = result.get("report") if isinstance(result, dict) else None
        record_defense_feedback(
            contradictions=_extract_contradiction_list(_report),
            regression_status="",
            skill_dir=sd,
        )
    except Exception as _fb_err:  # noqa: BLE001
        log_swallowed(__name__, _fb_err,
                      context=(f'record_main_cv_defense_feedback:'
                               f'{type(_fb_err).__name__}'))
def clear_feedback_history(skill_dir: str = _DEFAULT_SKILL_DIR) -> int:
    if not skill_dir:
        n = len(_FEEDBACK_HISTORY)
        _FEEDBACK_HISTORY.clear()
        return n
    scope = _feedback_scope_key(skill_dir)
    if not scope:
        logger.warning("防御反馈清理跳过：skill_dir 无法归一为项目作用域: %r",
                     skill_dir)
        return 0
    kept = [item for item in _FEEDBACK_HISTORY if item[0] != scope]
    removed = len(_FEEDBACK_HISTORY) - len(kept)
    _FEEDBACK_HISTORY[:] = kept
    return removed
BUG_INTERCEPT_HIGH_FREQ_THRESHOLD = 3
_CATEGORY_HIGH_FREQ_THRESHOLD = 3
_BUG_INTERCEPT_TOP_N = 20
def _event_payload(event: Any) -> dict:
    if not isinstance(event, dict):
        return {}
    payload = event.get("payload")
    return payload if isinstance(payload, dict) else {}
def _bug_intercept_counter(events: list) -> Counter:
    counter: Counter = Counter()
    for ev in events:
        check_id = _event_payload(ev).get("check_id")
        if not check_id and isinstance(ev, dict):
            check_id = ev.get("check_id")
        if check_id:
            counter[str(check_id)] += 1
    return counter
def _bug_intercept_events_in_scope(events: list, skill_dir: str) -> list:
    if not skill_dir:
        return events
    scope = _feedback_scope_key(skill_dir)
    if not scope:
        return []
    return [
        event for event in events
        if _feedback_scope_key(
            str(_event_payload(event).get("skill_dir") or "")) == scope
    ]
def _signal_bug_intercept(skill_dir: str = _DEFAULT_SKILL_DIR) -> dict[str, Any]:
    events = _bug_intercept_events_in_scope(load_bug_intercepts(), skill_dir)
    counter = _bug_intercept_counter(events)
    high_freq = [
        {"check_id": cid, "count": n}
        for cid, n in sorted(
            counter.items(), key=lambda kv: (-kv[1], kv[0]))
        if n >= BUG_INTERCEPT_HIGH_FREQ_THRESHOLD]
    return {
        "bug_intercept_total": len(events),
        "bug_intercept_high_freq": high_freq[:_BUG_INTERCEPT_TOP_N],
    }
def _signal_fp_rules(skill_dir: str) -> dict[str, Any]:
    rules = rules_of(load_fp_rules(skill_dir) if skill_dir else {})
    return {"fp_rule_ids": sorted(str(k) for k in rules)}
def _signal_defense_feedback(skill_dir: str) -> dict[str, Any]:
    summary = summarize_defense_feedback(skill_dir)
    recs = summary.get("recommendations") if isinstance(summary, dict) else None
    return {"defense_recommendations":
            [r for r in recs if r] if isinstance(recs, list) else []}
def _signal_lessons(skill_dir: str) -> dict[str, Any]:
    if not skill_dir:
        return {"lessons": []}
    return {"lessons": HistoricalLessonsInjector(skill_dir).inject() or []}
def collect_diagnostic_defense_signals(skill_dir: str) -> dict[str, Any]:
    signals: dict[str, Any] = {
        "bug_intercept_high_freq": [], "bug_intercept_total": 0, "fp_rule_ids": [],
        "defense_recommendations": [], "lessons": [], "channel_errors": {},
    }
    channel_producers = (
        ("bug_intercept", lambda: _signal_bug_intercept(skill_dir)),
        ("fp_rules", lambda: _signal_fp_rules(skill_dir)),
        ("defense_feedback", lambda: _signal_defense_feedback(skill_dir)),
        ("lessons", lambda: _signal_lessons(skill_dir)),
    )
    for channel_name, producer in channel_producers:
        try:
            signals.update(producer())
        except Exception as e:  # noqa: BLE001
            signals["channel_errors"][channel_name] = str(e)
            logger.warning("[defense_bridge] %s 通道失败: %s", channel_name, e)
    return signals
def _load_defense_feedback_history(
        skill_dir: str = _DEFAULT_SKILL_DIR) -> list[dict[str, Any]]:
    try:
        events = load_defense_feedback_events()
    except (OSError, TypeError, ValueError):
        logger.warning("defense_feedback 事件读取失败（降级空列表）", exc_info=True)
        return []
    if not skill_dir:
        return events
    scope = _feedback_scope_key(skill_dir)
    if not scope:
        logger.warning("防御反馈摘要跳过：skill_dir 无法归一为项目作用域: %r",
                       skill_dir)
        return []
    return [
        event for event in events
        if _feedback_scope_key(
            str(_event_payload(event).get("skill_dir") or "")) == scope
    ]
def _accumulate_recommendations(recommendations: list[str],
                                raw_recs) -> None:
    if not isinstance(raw_recs, list):
        return
    for rec in raw_recs:
        if isinstance(rec, str) and rec not in recommendations:
            recommendations.append(rec)
def _accumulate_by_category(by_category: dict[str, int], raw_by_cat) -> None:
    if not isinstance(raw_by_cat, dict):
        return
    for raw_cat, cnt in raw_by_cat.items():
        if (not isinstance(raw_cat, str) or isinstance(cnt, bool)
                or not isinstance(cnt, (int, float))):
            continue
        cat = _status_text(raw_cat)
        if not cat:
            continue
        try:
            delta = max(0, int(cnt))
        except (ValueError, OverflowError) as _e:
            log_swallowed(__name__, _e,
                          context=f'_accumulate_by_category:{type(_e).__name__}')
            continue
        by_category[cat] = by_category.get(cat, 0) + delta
def _aggregate_defense_events(events: list) -> dict:
    by_category: dict[str, int] = {}
    recommendations: list[str] = []
    contradiction_total = 0
    fix_safety_total = 0
    regression_failures = 0
    for ev in events:
        payload = _event_payload(ev)
        contradiction_total += max(0, int_or(payload.get("contradiction_count")))
        if _status_text(payload.get("regression_status")) in _REGRESSION_FAILURE_STATUSES:
            regression_failures += 1
        _accumulate_recommendations(recommendations,
                                    payload.get("recommendations"))
        event_by_category: dict[str, int] = {}
        _accumulate_by_category(event_by_category, payload.get("by_category"))
        explicit_fix_safety = max(0, int_or(payload.get("fix_safety_count")))
        event_fix_safety = max(
            explicit_fix_safety, event_by_category.get("fix_safety", 0))
        if event_fix_safety:
            event_by_category["fix_safety"] = event_fix_safety
        fix_safety_total += event_fix_safety
        for cat, count in event_by_category.items():
            by_category[cat] = by_category.get(cat, 0) + count
    return {
        "by_category": by_category, "recommendations": recommendations,
        "contradiction_total": contradiction_total, "fix_safety_total": fix_safety_total,
        "regression_failures": regression_failures,
    }
def _build_risk_signal(events_count: int, contradiction_total: int,
                       regression_failures: int, rec_count: int) -> str:
    if not (events_count and (contradiction_total or regression_failures)):
        return ""
    parts = [f"CV 矛盾结论 {contradiction_total} 条"]
    if regression_failures:
        parts.append(f"回归失败 {regression_failures} 次")
    return ("[防御反馈] 本轮闭环留痕: " + "、".join(parts) +
            f"，已生成 {rec_count} 条防御规则迭代建议待审核")
def summarize_defense_feedback(skill_dir: str = _DEFAULT_SKILL_DIR) -> dict[str, Any]:
    events = _load_defense_feedback_history(skill_dir)
    agg = _aggregate_defense_events(events)
    by_category = agg["by_category"]
    recommendations = agg["recommendations"]
    contradiction_total = agg["contradiction_total"]
    fix_safety_total = agg["fix_safety_total"]
    regression_failures = agg["regression_failures"]
    high_freq = [(cat, cnt) for cat, cnt in sorted(
        by_category.items(), key=lambda kv: (-kv[1], kv[0]))
        if cnt >= _CATEGORY_HIGH_FREQ_THRESHOLD]
    risk_signal = _build_risk_signal(
        len(events), contradiction_total, regression_failures,
        len(recommendations))
    return {
        "total": len(events), "contradiction_total": contradiction_total,
        "fix_safety_total": fix_safety_total, "regression_failures": regression_failures,
        "by_category": by_category, "high_freq": high_freq,
        "recommendations": recommendations, "risk_signal": risk_signal,
    }
def _nonnull(value: object, default: Any) -> Any:
    return default if value is None else value
def _is_nonempty_str(value: object) -> bool:
    return isinstance(value, str) and bool(value)
def _lesson(source: str, target: str, description: str,
            suggestion: Any, confidence: float, inject_as: str) -> dict:
    return {
        "source": source, "target": target, "description": description,
        FIELD_SUGGESTED_VALUE: suggestion, "confidence": confidence,
        "inject_as": inject_as,
    }
def _history_method_multiplier(entry: dict) -> float:
    direct = entry.get("confidence_multiplier")
    if is_finite_num(direct):
        return normalize_confidence(direct, 1.0)
    for record in reversed(as_list(entry.get("suggestions"))):
        if not isinstance(record, dict):
            continue
        suggested = record.get(FIELD_SUGGESTED_VALUE)
        if not isinstance(suggested, dict):
            continue
        value = suggested.get("confidence_multiplier")
        if is_finite_num(value):
            return normalize_confidence(value, 1.0)
    return 1.0
class HistoricalLessonsInjector:
    _ENHANCEMENT_REPORT_KEYS = (
        "enhancement_actions", "enhancements", "lessons", "improvements")
    _LESSON_DESC_KEYS = ("description", "reason", "message")
    _LESSON_CHANNELS = (
        ("_load_retrospective_lessons", "复盘经验"),
        ("_load_enhancement_log_lessons", "增强日志"),
        ("_load_feedback_history_lessons", "反馈历史"),
    )
    def __init__(self, skill_dir: str):
        self.skill_dir = skill_dir
    def _load_json(self, path: str) -> Any | None:
        if not path:
            return None
        data, kind, _err = read_json_artifact(path)
        return None if kind != "ok" else data
    def inject(self) -> list:
        lessons: list[dict] = []
        for loader_name, label in self._LESSON_CHANNELS:
            try:
                lessons.extend(getattr(self, loader_name)())
            except Exception as e:  # noqa: BLE001
                logger.warning("[LessonsInjector] %s加载失败: %s", label, e)
        if lessons:
            logger.info("[LessonsInjector] 注入 %d 条历史经验", len(lessons))
        return lessons
    def _load_retrospective_lessons(self) -> list[dict]:
        report = self._load_json(evolution_report_path(self.skill_dir))
        if not isinstance(report, dict):
            return []
        lessons: list[dict] = []
        lessons.extend(self._collect_good_practice_lessons(report))
        lessons.extend(self._collect_issue_lessons(report))
        lessons.extend(self._collect_enhancement_key_lessons(report))
        return lessons
    def _collect_good_practice_lessons(self, report: dict) -> list[dict]:
        lessons: list[dict] = []
        for gp in as_list(report.get("good_practices")):
            if not isinstance(gp, dict):
                continue
            desc = gp.get("description", "")
            if not _is_nonempty_str(desc):
                continue
            reusable = gp.get("reusable")
            if reusable is None or signal_bool(reusable):
                lessons.append(_lesson(
                    source="retrospective_good_practice",
                    target=_nonnull(gp.get("method_id"), ""),
                    description=f"[优质操作-{_nonnull(gp.get('phase'), '')}] {desc}",
                    suggestion="在代码中复现此模式", confidence=0.8,
                    inject_as="code_pattern"))
        return lessons
    def _collect_issue_lessons(self, report: dict) -> list[dict]:
        lessons: list[dict] = []
        for issue in as_list(report.get("issues_found")):
            if not isinstance(issue, dict):
                continue
            severity = _status_text(issue.get("severity"))
            if severity not in ("critical", "high"):
                continue
            desc = issue.get("description", "")
            remedy = issue.get("remedy", "")
            if not (_is_nonempty_str(desc) and _is_nonempty_str(remedy)):
                continue
            lessons.append(_lesson(
                source="retrospective_issue",
                target=_nonnull(issue.get("method_id"), ""),
                description=f"[避免-{severity}] {desc}",
                suggestion=remedy, confidence=0.75,
                inject_as="avoidance_pattern"))
        return lessons
    def _collect_enhancement_key_lessons(self, report: dict) -> list[dict]:
        lessons: list[dict] = []
        seen_descs: set[str] = set()
        for key in self._ENHANCEMENT_REPORT_KEYS:
            for it in as_list(report.get(key)):
                lesson = self._enhancement_lesson(it, seen_descs)
                if lesson is not None:
                    lessons.append(lesson)
        return lessons
    def _enhancement_lesson(self, item: object,
                            seen_descs: set[str]) -> dict | None:
        if not isinstance(item, dict):
            return None
        desc = next(
            (item[k] for k in self._LESSON_DESC_KEYS
             if _is_nonempty_str(item.get(k))), "")
        if not desc or desc in seen_descs:
            return None
        seen_descs.add(desc)
        return _lesson(
            source="retrospective",
            target=(_nonnull(item.get("target"), "")
                    or _nonnull(item.get("target_id"), "all")),
            description=desc, suggestion=_nonnull(item.get(FIELD_SUGGESTED_VALUE), ""),
            confidence=normalize_confidence(item.get("confidence")),
            inject_as="precheck",
        )
    def _load_enhancement_log_lessons(self) -> list[dict]:
        try:
            log = read_evolution_section(
                self.skill_dir, "enhancement_log")
        except (OSError, ValueError, TypeError) as _exc:
            logger.warning("[RetroEvolution] 增强日志 section 读取失败: %s", _exc)
            log = None
        entries = (as_list(log.get("entries")) if isinstance(log, dict)
                   else as_list(log))
        lessons: list[dict] = []
        for entry in entries:
            if (not isinstance(entry, dict)
                    or _status_text(entry.get("status")) != "pending"):
                continue
            confidence = normalize_confidence(entry.get("confidence"))
            if confidence < 0.6:
                continue
            desc = entry.get("description", "")
            if not _is_nonempty_str(desc):
                continue
            lessons.append(_lesson(
                source="enhancement_log", target=_nonnull(entry.get("target"), ""),
                description=desc, suggestion=_nonnull(entry.get(FIELD_SUGGESTED_VALUE), ""),
                confidence=confidence, inject_as="precheck"))
        return lessons
    _METHOD_MULTIPLIER_FLOOR = 0.9
    def _load_feedback_history_lessons(self) -> list[dict]:
        try:
            history = read_evolution_section(
                self.skill_dir, "feedback_history")
        except (OSError, ValueError, TypeError) as _exc:
            logger.warning("[RetroEvolution] 反馈历史 section 读取失败: %s", _exc)
            history = None
        if not isinstance(history, dict):
            return []
        lessons: list[dict] = []
        method_thresh = history.get(FIELD_METHOD_THRESHOLDS, {}) or {}
        if not isinstance(method_thresh, dict):
            return lessons
        for mid, thresh in method_thresh.items():
            if not isinstance(thresh, dict):
                continue
            mult = _history_method_multiplier(thresh)
            if mult < self._METHOD_MULTIPLIER_FLOOR:
                lessons.append(_lesson(
                    source="feedback_history",
                    target=mid,
                    description=f"历史经验：{mid} 存在误报倾向，新代码中应增加前置条件检查",
                    suggestion="增加输入验证和边界条件检查",
                    confidence=0.7,
                    inject_as="code_pattern",
                ))
        return lessons
def _read_json_object(path: str, label: str) -> tuple[dict | None, str]:
    try:
        data, kind, _err = read_json_artifact(path, propagate_io=True)
    except OSError as _e:
        log_swallowed(__name__, _e, context=f'{label}:OSError')
        return None, "io"
    if kind != "ok":
        return None, "missing" if kind == "missing" else "corrupt"
    if not isinstance(data, dict):
        return None, "non_dict"
    return data, "ok"
MIN_SAMPLE_SIZE = 5
HIGH_FP_THRESHOLD = 0.50
VERY_HIGH_FP_THRESHOLD = 0.80
def _evolution_result(patterns_analyzed: int, enhancements_generated: int = 0,
                      fp_tracker_written: int = 0,
                      top_rules: list[str] | None = None) -> dict:
    return {
        "patterns_analyzed": patterns_analyzed,
        "enhancements_generated": enhancements_generated,
        "fp_tracker_written": fp_tracker_written,
        "top_rules": list(top_rules or []),
    }
def _persist_detector_improvements(skill_dir: str, patterns: list[dict],
                                   eligible: list[dict],
                                   fp_tracker_written: int) -> tuple[int, list[str]]:
    _top_rules = [p["rule_id"] for p in eligible[:10]]
    retro_ctx = load_retrospective_summary(skill_dir)
    new_entries = [
        _generate_detector_improvement_entry(pattern, retro_ctx)
        for pattern in eligible
    ]
    appended = 0
    try:
        with _required_write_lock(skill_dir):
            data, readable = read_enhancement_log(skill_dir, label="FpEvolution")
            if not readable or data is None:
                return 0, _top_rules
            entries = normalized_enhancement_entries(data)
            previous_count = len(entries)
            for entry in new_entries:
                append_enhancement_entry(entries, entry)
            appended = len(entries) - previous_count
            if not appended:
                logger.info(
                    "[FpEvolution] 分析 %d 个FP模式，%d 条改进建议均已存在，本轮不重复写盘",
                    len(patterns), len(new_entries))
                return 0, _top_rules
            sessions = data.get("sessions", [])
            if not isinstance(sessions, list):
                sessions = []
            sessions.append(_fp_evolution_session(
                patterns, eligible, appended, fp_tracker_written, _top_rules))
            data["sessions"] = sessions
            save_enhancement_log(skill_dir, data)
    except (OSError, ValueError, TypeError, RecursionError) as exc:
        logger.warning(
            "[FpEvolution] 分析 %d 个FP模式，改进建议落盘失败(0/%d 条)，写入 %d 条FP率: %s",
            len(patterns), appended, fp_tracker_written, exc)
        return 0, _top_rules
    logger.info("[FpEvolution] 分析 %d 个FP模式, 生成 %d 条改进建议, 写入 %d 条FP率",
                len(patterns), appended, fp_tracker_written)
    return appended, _top_rules
def _fp_evolution_session(patterns: list, eligible: list,
                          enhancements_generated: int, fp_tracker_written: int,
                          top_rules: list) -> dict:
    return {
        "timestamp": now_iso(),
        "type": "fp_evolution_v2",
        "patterns_analyzed": len(patterns),
        "eligible_rules": len(eligible),
        "enhancements_generated": enhancements_generated,
        "fp_tracker_written": fp_tracker_written,
        "top_rules": list(top_rules),
    }
_FEEDBACK_FP_EVIDENCE_LIMIT = 200
def _normalize_feedback_evidence(evidence: dict) -> dict:
    """把反馈历史中的 fp_confirmed 证据归一成治疗项形态。

    `_analyze_fp_patterns` 依赖 `file_path`/`message` 两个字段采样；
    反馈历史里对应的是 `file`/`reason`，这里补齐别名而不改动原字典。
    """
    item = dict(evidence)
    if not as_str(item.get("file_path")):
        item["file_path"] = as_str(item.get("file"))
    if not as_str(item.get("message")):
        item["message"] = as_str(item.get("reason"))
    return item
def _items_from_feedback_history(skill_dir: str) -> list:
    """从反馈历史回灌 fp_confirmed 证据。

    治疗状态落在会话级 Temp 目录，跨会话即失效；而反馈历史
    （evolution_state.json 的 feedback_history section）是技能级持久的。
    反哺输入若只依赖治疗状态，跨会话后必然归零，已固化的抑制规则
    也永远无法被重新评估。这里把已留痕的 fp_confirmed 证据归一成
    治疗项形态，保证反哺链路跨会话可回溯。
    """
    try:
        history = read_evolution_section(skill_dir, "feedback_history")
    except (OSError, ValueError, TypeError) as exc:
        log_swallowed(
            __name__, exc,
            context='_items_from_feedback_history:read_evolution_section')
        return []
    if not isinstance(history, dict):
        return []
    items: list = []
    seen: set[tuple[str, str]] = set()
    for session in as_list(history.get("sessions")):
        if not isinstance(session, dict):
            continue
        summary = session.get("outcome_summary")
        if not isinstance(summary, dict):
            continue
        for issue in as_list(summary.get("issues_discovered")):
            if not isinstance(issue, dict):
                continue
            for evidence in as_list(issue.get("evidence")):
                if not isinstance(evidence, dict):
                    continue
                if _status_text(evidence.get("status")) != "fp_confirmed":
                    continue
                key = (norm_rule_id(evidence.get("rule_id")),
                       fp_item_identity(evidence))
                if key in seen:
                    continue
                seen.add(key)
                items.append(_normalize_feedback_evidence(evidence))
                if len(items) >= _FEEDBACK_FP_EVIDENCE_LIMIT:
                    return items
    return items
def _load_fp_evolution_source(skill_dir: str) -> tuple[list, str]:
    """当前 FP 证据优先；当前状态没有 FP 时回退到持久历史。"""
    items = load_treatment_items(skill_dir)
    has_current_fp = any(
        isinstance(item, dict)
        and _status_text(item.get("status")) == "fp_confirmed"
        for item in items)
    if not has_current_fp:
        historical = _items_from_feedback_history(skill_dir)
        if historical:
            return historical, "feedback_history"
    return items, "treatment_state" if items else "feedback_history"


def generate_fp_driven_enhancements(skill_dir: str) -> dict:
    items, source = _load_fp_evolution_source(skill_dir)
    if not items:
        logger.info(
            "[FpEvolution] 治疗状态与反馈历史均无fp_confirmed证据，跳过FP驱动进化")
        return _evolution_result(0)
    logger.info("[FpEvolution] FP证据来源=%s, 条目=%d", source, len(items))
    patterns = _analyze_fp_patterns(items)
    if not patterns:
        logger.info("[FpEvolution] 无fp_confirmed项，跳过FP驱动进化")
        return _evolution_result(0)
    fp_tracker_written = _write_fp_tracker_json(skill_dir, patterns)
    eligible = _eligible_fp_patterns(patterns)
    if not eligible:
        logger.info("[FpEvolution] %d 个FP模式但无满足阈值的规则(FP率>=%.0f%%, 样本>=%d)",
                     len(patterns), HIGH_FP_THRESHOLD * 100, MIN_SAMPLE_SIZE)
        return _evolution_result(len(patterns),
                                 fp_tracker_written=fp_tracker_written,
                                 top_rules=[p["rule_id"] for p in patterns[:10]])
    generated, top_rules = _persist_detector_improvements(
        skill_dir, patterns, eligible, fp_tracker_written)
    return _evolution_result(len(patterns), generated, fp_tracker_written,
                             top_rules)
def _has_min_sample_size(pattern: dict) -> bool:
    return int_or(pattern.get("total_count")) >= MIN_SAMPLE_SIZE
def _pattern_fp_rate(pattern: dict) -> float:
    fp_count = max(0, as_num(pattern.get("fp_count", 0)))
    total = max(fp_count, as_num(pattern.get("total_count", 0)))
    return fp_count / total if total > 0 else 0.0
OBSERVATION_MIN_SAMPLE_SIZE = 1
OBSERVATION_FP_THRESHOLD = 0.9
OBSERVATION_SEVERITY_RANK = 3
def _is_observation_pattern(pattern: dict) -> bool:
    """小样本高误报率 → 观察态抑制。

    标准门槛（≥5 样本）会把零散误报永久挡在治理之外，而真实误报
    恰恰多是零散分布（每条规则 1–2 次）。观察态允许小样本规则先
    降噪，但只抑制最低严重度（P3），P0–P2 不受影响；规则同时带
    `observation_mode` 标记，由 TTL 与救援率回收兜底。
    """
    if _has_min_sample_size(pattern):
        return False
    return (int_or(pattern.get("total_count")) >= OBSERVATION_MIN_SAMPLE_SIZE
            and _pattern_fp_rate(pattern) >= OBSERVATION_FP_THRESHOLD)
def _eligible_fp_patterns(patterns: list[dict]) -> list[dict]:
    return [p for p in patterns
            if (_has_min_sample_size(p)
                and _pattern_fp_rate(p) >= HIGH_FP_THRESHOLD)
            or _is_observation_pattern(p)]
def _accumulate_fp_counts(entry: dict, it: dict) -> None:
    entry["fp_count"] += 1
    entry["total_count"] += 1
    sev = normalize_item_severity(it.get("severity"))
    entry["severities"][sev] = entry["severities"].get(sev, 0) + 1
    if not finding_line_no(it):
        entry["line_zero_count"] += 1
def _append_limited_sample(samples: list[str], value: str, limit: int,
                           max_chars: int | None = None) -> None:
    if value and len(samples) < limit and value not in samples:
        samples.append(value[:max_chars])
def _accumulate_fp_samples(entry: dict, it: dict) -> None:
    fpath = as_str(it.get("file_path", "")) or as_str(it.get("file", ""))
    _append_limited_sample(entry["sample_files"], fpath, 10)
    res = it.get("result")
    msg = as_str(it.get("message", ""))
    if not msg and isinstance(res, dict):
        msg = as_str(res.get("reason", ""))
    _append_limited_sample(entry["sample_messages"], msg, 3, max_chars=200)
def _count_rule_denominators(by_rule: dict, items: list,
                             fp_identities: set[tuple[str, str]]) -> None:
    non_fp = [it for it in items
              if isinstance(it, dict)
              and _status_text(it.get("status")) != "fp_confirmed"]
    for rid, it in iter_unique_rule_observations(non_fp):
        if (rid, fp_item_identity(it)) in fp_identities:
            continue
        if rid in by_rule:
            by_rule[rid]["total_count"] += 1
def _build_pattern_entry(rid: str, e: dict) -> dict:
    total = max(e["total_count"], e["fp_count"])
    fp_rate = e["fp_count"] / total if total > 0 else 0
    line_zero_ratio = e["line_zero_count"] / e["fp_count"] if e["fp_count"] > 0 else 0
    return {
        "rule_id": rid,
        "fp_count": e["fp_count"],
        "total_count": total,
        "fp_rate": round(fp_rate, 3),
        "sample_files": e["sample_files"],
        "sample_messages": e["sample_messages"],
        "severities": e["severities"],
        "line_zero_ratio": round(line_zero_ratio, 3),
        "_line_zero_count": e["line_zero_count"],
    }
def _pattern_line_zero_ratio(pattern: dict) -> float:
    if "_line_zero_count" not in pattern:
        return max(0.0, as_num(pattern.get("line_zero_ratio", 0)))
    fp_count = max(0, as_num(pattern.get("fp_count", 0)))
    if fp_count <= 0:
        return 0.0
    line_zero_count = min(
        fp_count, max(0, as_num(pattern.get("_line_zero_count", 0))))
    return line_zero_count / fp_count
def _analyze_fp_patterns(items: list) -> list[dict]:
    fp_items = [it for it in items
                if isinstance(it, dict)
                and _status_text(it.get("status")) == "fp_confirmed"]
    if not fp_items:
        return []
    by_rule: dict = defaultdict(lambda: {
        "fp_count": 0, "total_count": 0,
        "sample_files": [], "sample_messages": [],
        "severities": {}, "line_zero_count": 0,
    })
    fp_identities: set[tuple[str, str]] = set()
    for rid, it in iter_unique_rule_observations(fp_items):
        if is_placeholder_rule_id(rid):
            continue
        fp_identities.add((rid, fp_item_identity(it)))
        entry = by_rule[rid]
        _accumulate_fp_counts(entry, it)
        _accumulate_fp_samples(entry, it)
    _count_rule_denominators(by_rule, items, fp_identities)
    patterns = []
    for rid, e in by_rule.items():
        patterns.append(_build_pattern_entry(rid, e))
    patterns.sort(key=lambda x: (-x["fp_count"], x["rule_id"]))
    return patterns
def _atomic_dump_json(path: str, obj, label: str = "FpEvolution") -> None:
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    atomic_write_text(path, dump_json_text(obj), tag=label)
def _write_fp_tracker_json(skill_dir: str, patterns: list[dict]) -> int:
    fp_path = fp_tracker_rules_path(skill_dir)
    existing, kind = _read_json_object(fp_path, "_write_fp_tracker_json")
    if kind == "missing":
        existing = {}
    if existing is None:
        logger.warning(
            "[FpEvolution] fp_tracker_rules.json 读取失败(%s)，保留原文件并跳过写入",
            kind)
        return 0
    updated = _merge_tracker_updates(existing, patterns)
    written = 0
    if updated > 0:
        try:
            _atomic_dump_json(fp_path, existing)
            written = updated
            logger.info("[FpEvolution] 写入 %d 条FP率到 fp_tracker_rules.json (规则号维度闭环)",
                        updated)
        except (OSError, ValueError, TypeError, RecursionError) as e:
            logger.warning("[FpEvolution] fp_tracker_rules.json 写入失败: %s", e)
    return written
def _merge_tracker_updates(existing: dict, patterns: list[dict]) -> int:
    updated = 0
    for p in patterns:
        rid = p["rule_id"]
        if not _has_min_sample_size(p) and not _is_observation_pattern(p):
            continue
        values = {
            "total": p["total_count"],
            "fp": p["fp_count"],
            "fp_rate": _pattern_fp_rate(p),
        }
        current = existing.get(rid)
        if (isinstance(current, dict)
                and all(current.get(key) == value for key, value in values.items())):
            continue
        existing[rid] = {**current, **values} if isinstance(current, dict) else values
        updated += 1
    return updated
def _fp_evolution_provenance(pattern: dict, action_desc: str,
                             retro_ctx: dict | None = None) -> dict:
    fp_count = pattern.get("fp_count", 0)
    fp_rate = _pattern_fp_rate(pattern)
    prov = {
        "phase": "treatment",
        "source": "fp_evolution",
        "diagnosis_context": {
            "rule_id": pattern.get("rule_id", ""),
            "severity": "",
            "description": f"规则误报率 {fp_rate:.0%}（{fp_count} 项），{action_desc}",
        },
        "treatment_context": {
            "fp_confirmed": fp_count,
            "fp_rate": fp_rate,
            "severities": pattern.get("severities", {}) or {},
            "sample_files": (pattern.get("sample_files") or [])[:5],
        },
    }
    if isinstance(retro_ctx, dict) and retro_ctx:
        prov["retrospective_context"] = dict(retro_ctx)
    return prov
_FP_LINE_ZERO_RATIO = 0.5
_FP_LARGE_COUNT = 100
_FP_NEAR_CERTAIN_RATE = 0.95
def _detector_improvement_suggestions(pattern: dict) -> list[str]:
    fp_rate = _pattern_fp_rate(pattern)
    fp_count = pattern["fp_count"]
    line_zero_ratio = _pattern_line_zero_ratio(pattern)
    sample_messages = pattern.get("sample_messages", [])
    improvements = []
    if line_zero_ratio > _FP_LINE_ZERO_RATIO:
        improvements.append(
            f"检测器产出的{line_zero_ratio:.0%}发现为line=0文件级，"
            f"建议增加AST节点行号定位(ast.NodeVisitor.visit时记录node.lineno)"
        )
    if fp_count > _FP_LARGE_COUNT:
        improvements.append(
            f"误报量极大({fp_count}项)，建议收窄检测条件："
            f"增加上下文检查(如排除内置函数/排除属性调用/排除设计模式)"
        )
    if fp_rate >= _FP_NEAR_CERTAIN_RATE:
        improvements.append(
            f"FP率{fp_rate:.0%}接近100%，检测规则可能存在根本性设计缺陷，"
            f"建议审查检测逻辑或降级为INFO级"
        )
    if sample_messages:
        improvements.append(
            f"典型误报样本: {sample_messages[0][:100]}"
        )
    return improvements
def _generate_detector_improvement_entry(pattern: dict,
                                         retro_ctx: dict | None = None) -> dict:
    rid = pattern["rule_id"]
    fp_rate = _pattern_fp_rate(pattern)
    fp_count = pattern["fp_count"]
    improvements = _detector_improvement_suggestions(pattern)
    suppression_rule = _suppression_rule_payload(pattern, improvements)
    return {
        "timestamp": now_iso(),
        "target": f"fp_suppression/{rid}",
        "target_type": "fp_suppression",
        "target_id": rid,
        "action_type": "fp_suppression",
        "description": f"规则 {rid} 产生 {fp_count} 项误报(FP率{fp_rate:.0%})，生成抑制规则",
        "suggested_value": json.dumps(suppression_rule, ensure_ascii=False),
        "expected_impact": f"应用抑制规则后预计减少 {fp_count} 项误报",
        "confidence": min(0.95, 0.5 + fp_count / 50),
        "status": "pending",
        "fp_pattern": True,
        "rule_id": rid,
        "fp_rate": fp_rate,
        "fp_count": fp_count,
        **_fp_evolution_provenance(pattern, "建议生成抑制规则", retro_ctx),
    }
_FILE_PATTERN_LIMIT = 5
def _derive_file_patterns(sample_files: list) -> list[str]:
    """从样本文件派生路径子串模式。

    `_patterns_hit` 做子串匹配，而 finding 的 file 可能是绝对路径，
    因此取 basename 才能稳定命中。样本缺文件时返回空列表，由
    `_suppression_rule_has_evidence` 失败关闭——无证据的抑制规则
    会退化为无差别掩盖，不得写入。
    """
    names: list[str] = []
    for raw in as_list(sample_files):
        path = as_str(raw).strip().replace("\\", "/")
        if not path:
            continue
        base = os.path.basename(path)
        if base and base not in names:
            names.append(base)
    return names[:_FILE_PATTERN_LIMIT]
def _suppression_rule_payload(pattern: dict,
                              improvements: list[str]) -> dict:
    sample_messages = pattern.get("sample_messages", [])
    rule = {
        "rule_id": pattern["rule_id"],
        "fp_count": pattern["fp_count"],
        "fp_rate": _pattern_fp_rate(pattern),
        "line_zero_ratio": _pattern_line_zero_ratio(pattern),
        "improvements": improvements,
        "sample_files": pattern.get("sample_files", [])[:5],
        "sample_messages": sample_messages[:3],
    }
    observation = _is_observation_pattern(pattern)
    rule["observation_mode"] = observation
    rule["min_severity_to_suppress"] = (
        severity_literal_from_rank(OBSERVATION_SEVERITY_RANK)
        if observation
        else suppression_min_severity(
            _pattern_fp_rate(pattern), pattern["fp_count"],
            pattern.get("severities")))
    if sample_messages:
        rule["message_patterns"] = [m[:60] for m in sample_messages[:2]]
    else:
        rule["message_patterns"] = []
    rule["file_patterns"] = _derive_file_patterns(rule["sample_files"])
    return rule
def get_fp_evolution_summary(skill_dir: str) -> dict:
    items, _source = _load_fp_evolution_source(skill_dir)
    fp_items = [it for it in items
                if isinstance(it, dict)
                and _status_text(it.get("status")) == "fp_confirmed"]
    patterns = _analyze_fp_patterns(items)
    return {
        "total_fp": len(fp_items),
        "total_patterns": len(patterns),
        "high_fp_rules": len([p for p in patterns
                              if _has_min_sample_size(p)
                              and _pattern_fp_rate(p) >= HIGH_FP_THRESHOLD]),
        "very_high_fp_rules": len([p for p in patterns
                                   if _has_min_sample_size(p)
                                   and _pattern_fp_rate(p) >= VERY_HIGH_FP_THRESHOLD]),
        "top_5_rules": [
            {"rule_id": p["rule_id"], "fp_count": p["fp_count"],
             "fp_rate": _pattern_fp_rate(p)}
            for p in patterns[:5]
        ],
    }
def _record_degraded_step(result: dict, step: str,
                          exc: BaseException) -> None:
    """反哺步骤降级必须留痕。

    静默 ``warning`` 会让“进化”看起来完成了：外层只看 ``status``，
    而反哺什么都没做也能拿到 ``completed``。降级项汇总后由
    ``run_stage6c_code_feedback`` 统一作失败判定。
    """
    degraded = result.get("degraded_steps")
    if not isinstance(degraded, list):
        degraded = []
        result["degraded_steps"] = degraded
    degraded.append({
        "step": step,
        "error": f"{type(exc).__name__}: {str(exc)[:300]}",
    })


def run_fp_evolution_step(skill_dir: str, result: dict) -> None:
    try:
        _evo_result = require_dict(
            generate_fp_driven_enhancements(skill_dir), "FP驱动进化结果")
        result["fp_evolution"] = _evo_result
        logger.info("[Stage6c] FP驱动进化: %d模式→%d改进建议+FP跟踪器%d条",
                    _evo_result.get("patterns_analyzed", 0),
                    _evo_result.get("enhancements_generated", 0),
                    _evo_result.get("fp_tracker_written", 0))
    except Exception as evo_e:  # noqa: BLE001
        _record_degraded_step(result, "fp_evolution", evo_e)
        logger.warning("[Stage6c] FP驱动进化降级: %s", evo_e)
def _extract_contradiction_list(cv_report: dict) -> list:
    if not isinstance(cv_report, dict):
        return []
    merged: list = []
    for key in ("contradiction_findings", "contradictions"):
        value = cv_report.get(key)
        if not isinstance(value, (list, tuple)):
            continue
        for item in value:
            if item not in merged:
                merged.append(item)
    return merged
def _is_applied_treatment_item(item: Any) -> bool:
    return (isinstance(item, dict)
            and _status_text(item.get("status")) in AUTO_FIXED_STATUSES)
_REGRESSION_TEXT_VERDICTS = {
    "1": True, "true": True, "yes": True, "verified": True,
    "pass": True, "passed": True, "completed": True,
    "0": False, "false": False, "no": False,
    "fail": False, "failed": False, "error": False,
}
def _regression_verification(item: dict) -> bool | None:
    detail = item.get("result")
    if detail is None:
        return None
    if not isinstance(detail, dict):
        return False
    raw = detail.get("regression_verified")
    if raw is None:
        return None
    if isinstance(raw, str):
        return _REGRESSION_TEXT_VERDICTS.get(_status_text(raw))
    if isinstance(raw, bool):
        return raw
    if is_finite_num(raw):
        return bool(raw) if raw in (0, 1) else None
    return None
def _applied_treatment_items(state: Any) -> list:
    raw_items = state.get("items") if isinstance(state, dict) else state
    items = as_item_list(raw_items, log_tag="_applied_treatment_items")
    return [it for it in items if _is_applied_treatment_item(it)]
def derive_regression_status(skill_dir: str) -> str:
    try:
        _applied_items = _applied_treatment_items(
            load_treatment_state(skill_dir))
        if not _applied_items:
            return ""
        verdicts = [_regression_verification(it) for it in _applied_items]
        if any(verdict is False for verdict in verdicts):
            return "fail"
        if all(verdict is True for verdict in verdicts):
            return "pass"
        logger.debug("[Stage6c] 已应用 %d 项但未全部获得回归通过证据，状态留空",
                     len(_applied_items))
    except Exception as e:  # noqa: BLE001
        logger.debug("回归状态提取失败，降级空状态: %s", e)
        return ""
    return ""
def _log_defense_feedback(defense_fb: dict, reg_status: str) -> None:
    if not defense_fb.get("recommendations"):
        return
    by_cat = defense_fb.get("by_category") or {}
    logger.info(
        "[Stage6c] 矛盾→防御规则反馈: %d条矛盾(修复安全%d), "
        "%d条防御建议, 回归状态=%s",
        sum(by_cat.values()),
        by_cat.get("fix_safety", 0),
        len(defense_fb["recommendations"]),
        reg_status or "未知",
    )
def run_defense_feedback_step(skill_dir: str, cv_report: dict,
                              result: dict) -> None:
    _fb_recorded = False
    try:
        _contra_list = _extract_contradiction_list(cv_report)
        _reg_status = derive_regression_status(skill_dir)
        _defense_fb = require_dict(
            record_defense_feedback(
                contradictions=_contra_list, regression_status=_reg_status,
                skill_dir=skill_dir),
            "防御反馈结果")
        result["feedback_defense"] = _defense_fb
        _fb_recorded = True
        _log_defense_feedback(_defense_fb, _reg_status)
    except Exception as _def_e:  # noqa: BLE001
        _record_degraded_step(result, "defense_feedback", _def_e)
        logger.warning("[Stage6c] 矛盾防御反馈降级: %s", _def_e)
    finally:
        if _fb_recorded:
            try:
                result["feedback_history_released"] = (
                    clear_feedback_history(skill_dir))
            except Exception as _rel_e:  # noqa: BLE001
                result["feedback_history_released"] = 0
                logger.warning("[Stage6c] 防御反馈历史释放失败(降级): %s", _rel_e)
def persist_review_enhancements_step(ctx, review_result: dict | None,
                                    result: dict | None = None) -> None:
    if not review_result:
        return
    try:
        persist_review_enhancements(ctx, review_result)
    except Exception as peh_err:  # noqa: BLE001
        logger.warning("[Stage6c] 复盘增强建议持久化降级: %s", peh_err)
        if isinstance(result, dict):
            _record_degraded_step(result, "review_enhancements", peh_err)
register_cache_release(
    "defense_feedback", clear_feedback_history, "防御反馈历史",
    scope="project", order=190)
register_review_provider("precreation_history_lessons", HistoricalLessonsInjector)
def _index_key(entry: dict) -> int | None:
    idx = plan_index(entry.get("index"))
    return idx if idx is not None and idx >= 0 else None
def _apply_status_to_entry(entry, status_by_index: dict) -> bool:
    if not isinstance(entry, dict):
        return False
    idx = _index_key(entry)
    if idx is None or idx not in status_by_index:
        return False
    new_status = _status_text(status_by_index[idx])
    if not new_status:
        return False
    if _status_text(entry.get("status")) == new_status:
        return False
    entry["status"] = new_status
    return True
def _latest_detail_positions(details: list) -> dict[int, int]:
    positions: dict[int, int] = {}
    for pos, entry in enumerate(details):
        idx = _index_key(entry) if isinstance(entry, dict) else None
        if idx is not None:
            positions[idx] = pos
    return positions
def apply_status_map_to_details(merged: list, status_by_index: dict) -> int:
    merged = as_item_list(merged, log_tag="apply_status_map_to_details")
    raw_status_by_index = dict_or_empty(status_by_index)
    status_by_index = {}
    for raw_idx, status in raw_status_by_index.items():
        idx = plan_index(raw_idx)
        if idx is not None:
            status_by_index[idx] = status
    positions = _latest_detail_positions(merged)
    return sum(
        1 for idx, pos in positions.items()
        if _apply_status_to_entry(merged[pos], status_by_index))
def _status_entry(item) -> tuple[int, str] | None:
    if not isinstance(item, dict):
        return None
    status = _status_text(item.get("status"))
    idx = _index_key(item)
    if not status or idx is None:
        return None
    return idx, status
def build_status_map_from_items(items: list) -> dict:
    pairs = [pair for pair in map(
        _status_entry, as_item_list(items, log_tag="build_status_map_from_items"))
        if pair is not None]
    return dict(pairs)
def merge_treatment_state_details(skill_dir: str, exec_result: dict | None) -> list:
    details = (exec_result.get("details")
               if isinstance(exec_result, dict) else None)
    has_details = isinstance(details, (list, tuple))
    merged = list(details) if has_details else []
    try:
        _ts_items = read_treatment_state_items(skill_dir)
    except OSError as exc:
        logger.warning(
            "[Stage6b] 治疗状态读取失败(%s)，沿用执行明细 %d 项: %s",
            type(exc).__name__, len(merged), exc)
        return merged
    if not _ts_items:
        return merged
    if not has_details:
        logger.info("[Stage6b] details 缺失，以 _treatment_state.json %d 项替代",
                    len(_ts_items))
        return list(_ts_items)
    _updated_count = apply_status_map_to_details(
        merged, build_status_map_from_items(_ts_items))
    if _updated_count > 0:
        logger.info("[Stage6b] 从_treatment_state.json更新 %d 项状态(含fp_confirmed)",
                    _updated_count)
    return merged
def latest_status_rows(details: list) -> list[dict]:
    rows: list[dict] = []
    details = as_item_list(details, log_tag="latest_status_rows")
    positions = _latest_detail_positions(details)
    for pos, entry in enumerate(details):
        if not isinstance(entry, dict):
            continue
        idx = _index_key(entry)
        if idx is None or positions.get(idx) == pos:
            rows.append(entry)
    return rows
def _count_status(rows: list, statuses: tuple) -> int:
    counted = {text for text in (_status_text(s) for s in statuses) if text}
    return sum(1 for d in rows if _status_text(d.get("status")) in counted)
_EXECUTED_STATUSES: tuple[str, ...] = tuple(
    status for _field in ("auto_fixed", "fix_rolled_back", "fix_failed")
    for status in SUMMARY_STATUS_BUCKETS.get(_field, ()))
def build_fix_route_report(exec_result: dict, details: list) -> dict:
    exec_result = exec_result if isinstance(exec_result, dict) else {}
    _details = as_item_list(details, log_tag="build_fix_route_report.details")
    rows = latest_status_rows(_details)
    return {
        "summary": {
            FIELD_ROUTED_TO_FIXER: _count_status(rows, _EXECUTED_STATUSES),
            **{field: _count_status(rows, statuses)
               for field, statuses in SUMMARY_STATUS_BUCKETS.items()},
            FIELD_SIDE_EFFECTS_DETECTED: as_pure_count(
                exec_result.get(FIELD_SIDE_EFFECTS_DETECTED)),
            FIELD_SAFETY_VERIFIER_USED: as_pure_count(
                exec_result.get(FIELD_SAFETY_VERIFIER_USED)),
            "regression_passed": as_pure_count(
                exec_result.get("regression_passed")),
            FIELD_REGRESSION_FAILED: as_pure_count(
                exec_result.get(FIELD_REGRESSION_FAILED)),
        },
        "details": _details,
        "fix_coverage": dict_or_empty(exec_result.get("fix_coverage")),
    }
_BATCH_REPROCESSABLE = {"pending", "suggestion", "pending_confirm"}
_BATCH_TRULY_TERMINAL = frozenset({
    *TX_FIXED_STATUSES, *TX_ROLLED_BACK_STATUSES, "skipped",})
@dataclass(frozen=True)
class _FpHistory:
    frozen_rules: dict
    tracker_rates: dict
def _sev_batch_eligible(item: dict) -> bool:
    _token, rank = severity_rank_of_text(item.get("severity"))
    return rank in (2, 3, 4)
def _unit_interval_or_zero(value: Any) -> float:
    number = as_num(value)
    return number if 0.0 <= number <= 1.0 else 0.0
def _frozen_rule_stats(frozen_rules: dict, rid: str) -> tuple[float, float, float]:
    raw_meta = frozen_rules.get(rid)
    meta = raw_meta if isinstance(raw_meta, dict) else {}
    return (as_num(meta.get("count", 0)),
            _unit_interval_or_zero(meta.get("confidence", 0)),
            _unit_interval_or_zero(meta.get("fp_rate", 0)))
_BATCH_MIN_HISTORY_COUNT = MIN_SAMPLE_SIZE
_BATCH_MIN_HISTORY_CONFIDENCE = 0.6
_BATCH_MIN_RATE_EVIDENCE_COUNT = 20
_BATCH_MIN_FP_RATE = VERY_HIGH_FP_THRESHOLD
_BATCH_MIN_FROZEN_CONFIDENCE = 0.80
def _treatment_no_fixer_fp(rid: str, frozen_rules: dict) -> tuple[bool, str, str]:
    hist_count, hist_confidence, _ = _frozen_rule_stats(frozen_rules, rid)
    if (hist_count >= _BATCH_MIN_HISTORY_COUNT
            and hist_confidence >= _BATCH_MIN_HISTORY_CONFIDENCE):
        return (True,
                f"无修复器且规则已历史固化为FP(count={hist_count}, conf={hist_confidence})",
                "treatment_outcome")
    return False, "", ""
def _detect_treatment_outcome(item: dict, status: str, rid: str,
                              history: _FpHistory) -> tuple[bool, str, str]:
    if (status == "no_fixer" and rid in history.frozen_rules
            and _sev_batch_eligible(item)):
        return _treatment_no_fixer_fp(rid, history.frozen_rules)
    return False, "", ""
def _rate_by_tracker(rid: str, tracker_rates: dict, sev: str) -> tuple[bool, str]:
    tracker_entry = tracker_rates.get(rid, {})
    if not isinstance(tracker_entry, dict):
        return False, ""
    tr_total = as_num(tracker_entry.get("total", 0))
    if "fp" in tracker_entry and tr_total > 0:
        tr_fp = as_num(tracker_entry.get("fp"))
        if not 0 <= tr_fp <= tr_total:
            return False, ""
        tr_fp_rate = tr_fp / tr_total
    else:
        tr_fp_rate = _unit_interval_or_zero(tracker_entry.get("fp_rate", 0))
    if (tr_fp_rate >= _BATCH_MIN_FP_RATE
            and tr_total >= _BATCH_MIN_RATE_EVIDENCE_COUNT):
        return (True,
                f"历史FP率驱动(fp_rate={tr_fp_rate:.0%}, total={tr_total}, {sev})")
    return False, ""
def _rate_by_frozen_rule(rid: str, frozen_rules: dict) -> tuple[bool, str]:
    if rid not in frozen_rules:
        return False, ""
    hist_count, hist_confidence, hist_fp_rate = _frozen_rule_stats(
        frozen_rules, rid)
    if (hist_count >= _BATCH_MIN_RATE_EVIDENCE_COUNT
            and hist_confidence >= _BATCH_MIN_FROZEN_CONFIDENCE
            and hist_fp_rate >= _BATCH_MIN_FP_RATE):
        return (True,
                (f"历史固化规则驱动(count={hist_count}, "
                 f"conf={hist_confidence}, fp_rate={hist_fp_rate:.0%})"))
    return False, ""
def _detect_historical_rate(item: dict, status: str, rid: str,
                            history: _FpHistory) -> tuple[bool, str, str]:
    if status not in _BATCH_REPROCESSABLE or not _sev_batch_eligible(item):
        return False, "", ""
    is_fp, reason = _rate_by_tracker(
        rid, history.tracker_rates,
        normalize_item_severity(item.get("severity")))
    if not is_fp:
        is_fp, reason = _rate_by_frozen_rule(rid, history.frozen_rules)
    if is_fp:
        return True, reason, "historical_fp_rate"
    return False, "", ""
def _detect_item_fp(item: dict, status: str, rid: str, skill_dir: str,
                    history: _FpHistory) -> tuple[bool, str, str]:
    if status in _BATCH_REPROCESSABLE:
        is_fp, fp_reason = is_known_fp(item, skill_dir)
        if is_fp:
            return True, fp_reason, "structural"
    if is_placeholder_rule_id(rid):
        return False, "", ""
    is_fp, fp_reason, strategy = _detect_treatment_outcome(
        item, status, rid, history)
    if is_fp:
        return True, fp_reason, strategy
    return _detect_historical_rate(item, status, rid, history)
def _treatment_items_sanitized(state: dict) -> list:
    if not isinstance(state, dict):
        logger.warning("[BatchFP] 治疗状态非映射(%s)，按空清单处理",
                       type(state).__name__)
        return []
    items = state.get("items") or []
    if isinstance(items, tuple):
        items = list(items)
        state["items"] = items
    elif not isinstance(items, list):
        logger.warning("[BatchFP] 治疗状态 items 键非 list 脏形态(%s)，归一空清单",
                       type(items).__name__)
        return []
    return items
_BATCH_STRATEGIES: tuple[str, ...] = (
    "structural", "treatment_outcome", "historical_fp_rate")
def _empty_strategy_counts() -> dict[str, int]:
    return dict.fromkeys(_BATCH_STRATEGIES, 0)
def _apply_batch_marks(state: dict, items: list, skill_dir: str,
                       history: _FpHistory) -> tuple[int, dict, dict, int]:
    total_marked = 0
    already_fp = 0
    by_rule: dict = {}
    by_strategy = _empty_strategy_counts()
    for position, item in enumerate(items):
        if not isinstance(item, dict):
            continue
        raw_status = item.get("status")
        if raw_status is None:
            status = "pending"
        elif isinstance(raw_status, str):
            status = _status_text(raw_status) or "pending"
        else:
            logger.warning("[BatchFP] 治疗项状态非文本(%s)，跳过判定: index=%r",
                           type(raw_status).__name__, item.get("index"))
            continue
        if status in _BATCH_TRULY_TERMINAL:
            continue
        rid = norm_rule_id(item.get("rule_id"))
        if status == "fp_confirmed":
            already_fp += 1
            continue
        is_fp, fp_reason, strategy = _detect_item_fp(
            item, status, rid, skill_dir, history)
        if not is_fp:
            continue
        if not mark_item_fp_confirmed(state, item, fp_reason, strategy, position):
            continue
        by_strategy[strategy] = by_strategy.get(strategy, 0) + 1
        total_marked += 1
        by_rule[rid] = by_rule.get(rid, 0) + 1
    return total_marked, by_rule, by_strategy, already_fp
def batch_mark_fp_confirmed(skill_dir: str) -> dict:
    state = load_treatment_state(skill_dir)
    items = _treatment_items_sanitized(state)
    history = _FpHistory(
        frozen_rules=load_historical_fp_rules(skill_dir),
        tracker_rates=load_fp_tracker_rates(skill_dir))
    total_marked, by_rule, by_strategy, already_fp = _apply_batch_marks(
        state, items, skill_dir, history)
    if total_marked > 0:
        save_treatment_state(skill_dir, state)
        logger.info("[BatchFP] 批量标记 %d 项为 fp_confirmed (共 %d 项, 策略: %s, 规则: %s)",
                     total_marked, len(items), by_strategy,
                     dict(sorted(by_rule.items(),
                                 key=lambda x: (-x[1], x[0]))[:10]))
    return {
        "total_marked": total_marked,
        "total_items": len(items),
        "already_fp": already_fp,
        "by_rule": by_rule,
        "by_strategy": by_strategy,
    }
def zero_batch_fp_result() -> dict:
    return {"total_marked": 0, "total_items": 0, "already_fp": 0,
            "by_rule": {}, "by_strategy": _empty_strategy_counts()}
def batch_fp_marking(skill_dir: str) -> dict:
    try:
        _batch_result = batch_mark_fp_confirmed(skill_dir)
        logger.info("[Stage6b] 批量FP标记(前置): %d/%d 项标记为fp_confirmed",
                    _batch_result.get("total_marked", 0),
                    _batch_result.get("total_items", 0))
        return _batch_result
    except Exception as batch_e:  # noqa: BLE001
        logger.warning("[Stage6b] 批量FP标记跳过: %s", batch_e)
        return zero_batch_fp_result()
def _merge_feedback_report(result: dict, feedback_dict: dict,
                          stage_start: float) -> None:
    feedback_values = dict(feedback_dict)
    _fb_ts = feedback_values.pop("timestamp", None)
    _has_reported_status = "status" in feedback_values
    _reported_status = feedback_values.pop("status", None)
    for key in ("stage", "round_start_ts"):
        value = feedback_values.pop(key, None)
        if value is not None:
            result[f"feedback_{key}"] = value
    result.update(feedback_values)
    if _fb_ts is not None:
        result["feedback_timestamp"] = _fb_ts
    result["status"] = (
        "completed" if not _has_reported_status
        else _status_text(_reported_status) or "failed")
    result["elapsed_s"] = round(time.time() - stage_start, 2)
_CV_SECTION_STAT_KEYS = ("confirmed", "suppressed", "investigated",
                         FIELD_TOTAL_INPUT_FINDINGS)
_CV_SUMMARY_STAT_KEYS = ("cv_confirmed", "cv_suppressed", "cv_investigated",
                         FIELD_TOTAL_INPUT_FINDINGS)
_CV_DEGRADED_STATUSES = frozenset({
    "degraded", "empty_degradation", "insufficient_coverage"})
_CV_INCOMPLETE_PHASE_STATUSES = frozenset({"critical", "degraded"})
def _has_cv_stats(payload: Any, keys: tuple[str, ...]) -> bool:
    return isinstance(payload, dict) and any(
        is_real_number(payload.get(key)) and payload.get(key) >= 0
        for key in keys)
def _cv_report_degraded(report: dict) -> bool:
    if signal_bool(report.get("_empty_report")):
        return True
    if signal_bool(report.get("coverage_gate_triggered")):
        return True
    phase_health = report.get("phase_health")
    if isinstance(phase_health, dict):
        phase_status = as_str(
            phase_health.get("overall_status")).strip().lower()
        if phase_status in _CV_INCOMPLETE_PHASE_STATUSES:
            return True
    return as_str(report.get("status")).strip().lower() in _CV_DEGRADED_STATUSES
def cv_stats_from_report(cv_report) -> tuple[dict, str]:
    if not isinstance(cv_report, dict) or not cv_report:
        return {}, "no_cv_stats"
    if _cv_report_degraded(cv_report):
        logger.info("[Stage6b] CV报告为降级态(%s)，本轮不写性能基线",
                    cv_report.get("status") or "degraded")
        return {}, "no_cv_stats"
    if (_has_cv_stats(cv_report.get(CAT_CROSS_VALIDATION), _CV_SECTION_STAT_KEYS)
            or _has_cv_stats(cv_report.get("summary"),
                             _CV_SUMMARY_STAT_KEYS)):
        stats = extract_cv_stats(cv_report)
    elif _has_cv_stats(cv_report, _CV_SECTION_STAT_KEYS):
        stats = extract_cv_stats({CAT_CROSS_VALIDATION: cv_report})
    else:
        return {}, "no_cv_stats"
    if stats.get("_error"):
        return stats, "extract_error"
    return stats, ""
def _feedback_report_dict(feedback_report: Any) -> dict:
    if hasattr(feedback_report, "to_dict"):
        data = feedback_report.to_dict()
    elif isinstance(feedback_report, dict):
        data = feedback_report
    else:
        data = None
    return require_dict(data, "反馈报告")
def _feedback_dict_lists(feedback_report: Any) -> tuple[list, list]:
    _fb_dict = _feedback_report_dict(feedback_report)
    return (as_list(_fb_dict.get("cv_feedbacks")),
            as_list(_fb_dict.get("diagnosis_feedbacks")))
def _read_json_dict(path: str, label: str) -> dict | None:
    data, kind = _read_json_object(path, label)
    if kind == "missing":
        return {}
    if kind != "ok":
        logger.warning(
            "[CV-Feedback] %s 读取失败(%s)，按不可读处理以保留历史",
            label, kind)
        return None
    return data
def _merge_fp_tracker(adjustments: dict, fp_tracker_data: dict) -> None:
    if not fp_tracker_data:
        return
    existing_fp = adjustments.get("rule_fp_tracker", {})
    if not isinstance(existing_fp, dict):
        existing_fp = {}
    merged_fp = dict(existing_fp)
    merged_fp.update(fp_tracker_data)
    adjustments["rule_fp_tracker"] = merged_fp
    logger.info("[CV-Feedback] rule_fp_tracker 同步: %d families",
                len(fp_tracker_data))
def _norm_stat(source: dict, key: str):
    v = source.get(key)
    return v if (is_real_number(v) and v >= 0) else 0
def _cv_performance_stats_entry(cv_stats: dict) -> dict:
    return {
        "confirmed": _norm_stat(cv_stats, "confirmed"),
        "suppressed": _norm_stat(cv_stats, "suppressed"),
        "investigated": _norm_stat(cv_stats, "investigated"),
        FIELD_TOTAL_INPUT_FINDINGS: _norm_stat(cv_stats, FIELD_TOTAL_INPUT_FINDINGS),
        "degraded": _norm_stat(cv_stats, "degraded"),
        "partial_degraded": _norm_stat(cv_stats, "partial_degraded"),
        "updated_at": now_iso(),
    }
def _persist_adjustments(skill_dir: str, adjustments: dict) -> bool:
    try:
        if not write_evolution_section(
                skill_dir, "method_adjustments", adjustments):
            logger.warning(
                "[CV-Feedback] method_adjustments section 落盘失败: %s",
                skill_dir)
            return False
        updated_keys = [
            key for key in ("rule_fp_tracker", "cv_performance_stats")
            if key in adjustments]
        logger.info("[CV-Feedback] method_adjustments.json 已更新 (%s)",
                    " + ".join(updated_keys) or "last_cv_feedback_sync")
        return True
    except (OSError, ValueError, TypeError, RecursionError) as e:
        logger.warning("[CV-Feedback] method_adjustments.json 写入失败: %s", e)
        return False
def apply_cv_feedback(skill_dir: str, cv_stats: dict, feedback_report: Any) -> bool:
    try:
        cv_feedbacks, diagnosis_feedbacks = _feedback_dict_lists(feedback_report)
        logger.info("[CV-Feedback] CV反馈已吸收 (%d cv + %d diagnosis feedbacks)",
                    len(cv_feedbacks), len(diagnosis_feedbacks))
        fp_tracker_data = _read_json_dict(fp_tracker_path(skill_dir), "FP tracker")
        adjustments = read_evolution_section(
            skill_dir, "method_adjustments", default={})
        if not isinstance(adjustments, dict):
            logger.warning(
                "[CV-Feedback] method_adjustments section 非映射(%s)，"
                "保留历史并跳过本轮写入", type(adjustments).__name__)
            return False
        sync_ok = True
        if fp_tracker_data is None:
            sync_ok = False
            logger.warning("[CV-Feedback] FP tracker 读取失败，本轮跳过 tracker 同步")
        else:
            _merge_fp_tracker(adjustments, fp_tracker_data)
        if isinstance(cv_stats, dict) and cv_stats.get("_error"):
            logger.warning(
                "[CV-Feedback] cv_stats 为失败态(%s)，跳过性能统计写入"
                "（避免把全 0 当有效基线覆盖历史）",
                cv_stats.get("_partial", True))
        elif isinstance(cv_stats, dict) and cv_stats:
            if _has_cv_stats(cv_stats, _CV_SECTION_STAT_KEYS):
                adjustments["cv_performance_stats"] = (
                    _cv_performance_stats_entry(cv_stats))
            else:
                logger.warning(
                    "[CV-Feedback] cv_stats 无有效统计键(%s)，跳过性能统计写入",
                    ",".join(sorted(str(k) for k in cv_stats))[:120])
        if not adjustments:
            return sync_ok
        adjustments["last_cv_feedback_sync"] = now_iso()
        write_ok = _persist_adjustments(skill_dir, adjustments)
        return write_ok and sync_ok
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e,
                      context=f'apply_cv_feedback:{type(e).__name__}')
        logger.error("[%s] 异常降级: %s", "apply_cv_feedback", e)
        return False
def absorb_cv_feedback(skill_dir: str, cv_report: dict, feedback, result: dict) -> None:
    try:
        _cv_stats, _stats_skip = cv_stats_from_report(cv_report)
        absorbed = apply_cv_feedback(skill_dir, _cv_stats, feedback)
        result["cv_feedback_absorbed"] = absorbed
        if _stats_skip:
            result["cv_feedback_stats_skipped"] = _stats_skip
            logger.info("[Stage6b] CV性能基线未写入(%s)，反馈吸收继续",
                        _stats_skip)
        if not absorbed:
            logger.warning("[Stage6b] CV引擎反馈吸收未完成，请检查状态读取或写盘日志")
        elif not _stats_skip:
            logger.info("[Stage6b] CV引擎反馈吸收完成 (confirmed=%s, suppressed=%s)",
                        _cv_stats.get("confirmed", 0),
                        _cv_stats.get("suppressed", 0))
    except Exception as _absorb_err:  # noqa: BLE001
        result["cv_feedback_absorbed"] = False
        logger.warning("[Stage6b] CV引擎反馈吸收失败（不阻塞）: %s", _absorb_err)
def _log_feedback_done(feedback_dict: dict, elapsed: float) -> None:
    logger.info("[Stage6b] feedback_loop完成: %d 诊断反馈, %d CV反馈, %d 修复器反馈 (耗时 %.1fs)",
                len(feedback_dict.get("diagnosis_feedbacks") or []),
                len(feedback_dict.get("cv_feedbacks") or []),
                len(feedback_dict.get("fixer_feedbacks") or []),
                elapsed)
def run_feedback_loop_stage(skill_dir: str, exec_result: dict, cv_report: dict,
                             *, feedback_runner, memory_context=None) -> dict:
    stage_start = time.time()
    result = {"stage": "feedback_loop", "timestamp": timestamp_ms(),
              "status": "running",
              "round_start_ts": get_round_start_ts(skill_dir)}
    result["batch_fp_marking"] = batch_fp_marking(skill_dir)
    try:
        _merged_details = merge_treatment_state_details(skill_dir, exec_result)
        feedback = feedback_runner(
            skill_dir=skill_dir,
            fix_route_report=build_fix_route_report(
                exec_result, _merged_details),
            diagnosis_report=cv_report,
            memory_context=memory_context,
        )
        feedback_dict = _feedback_report_dict(feedback)
        _merge_feedback_report(result, feedback_dict, stage_start)
        absorb_cv_feedback(skill_dir, cv_report, feedback, result)
        _log_feedback_done(feedback_dict, result["elapsed_s"])
    except Exception as e:
        result["status"] = "failed"
        result["error"] = str(e)[:500]
        result["elapsed_s"] = round(time.time() - stage_start, 2)
        logger.exception("[Stage6b] feedback_loop失败")
    return result

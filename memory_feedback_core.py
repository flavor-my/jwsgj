from __future__ import annotations

import logging
import math
import os
import re
import time
from collections.abc import Iterable
from dataclasses import dataclass, field, replace
from typing import Any, Protocol

from jwsgj.diag_types_normalize import (
    as_list,
    dict_or_empty,
    finding_file_path,
    is_finite_num,
    safe_float,
    signal_bool,
    unwrap_cv_results,
)
from jwsgj.diag_types_vocab import (
    CONF_CAP,
    CONF_FLOOR,
    DEFAULT_CONFIDENCE_FALLBACK,
    FIELD_CV_CONFIDENCE_THRESHOLDS,
    FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
    TX_ROLLED_BACK_STATUSES,
)
from jwsgj.hallucination_prewrite import get_constraints_for_task
from jwsgj.log_config import log_swallowed
from jwsgj.memory_bridge import (
    CATEGORY_CV_TUNING,
    CATEGORY_FIX_RESULT,
    CATEGORY_FIXER_PERF_SYNC,
    CATEGORY_FP_PATTERN,
    CATEGORY_OSCILLATION,
    CATEGORY_TP_PATTERN,
    FIX_RESULT_UPDATE_HEADING,
    JACCARD_THRESHOLD,
    TP_CONFIDENCE_MULTIPLIER,
    TP_THRESHOLD_ADJUSTMENT,
    WIKI_LESSONS_PREFIX,
    DiagnosticMemoryContext,
    DiagnosticMemoryOperation,
    TreatmentMemoryEnhancement,
    fix_failed,
    fix_succeeded,
    get_rule_severity_calibrations,
    iter_rule_findings,
    last_summary_dict,
    md_cell,
    memory_date_stamp,
    memory_text_tokens,
    normalize_rule_id,
    path_segment,
    pattern_rule_ids,
    pick_first,
    pick_text,
    rules_triggered_signal,
    safe_int,
    str_memory_paths,
    treatment_items,
    validate_memory_context,
)
from jwsgj.memory_op_generation import _existing_page_write_op
from jwsgj.pipeline_round_trace import PipelineContext
from jwsgj.runtime_paths import (
    diag_intermediate_dir,
    get_temp_base,
    read_evolution_section,
)
from jwsgj.testsuite_eval import build_test_bridge
from jwsgj.xv_threshold_learning import (
    apply_cv_tunings_to_config,
    fp_tuning_params,
    generate_cv_tunings,
    get_rule_threshold,
)


def generate_memory_cv_tunings(memory_context) -> list:
    if not memory_context:
        return []
    try:
        issues = validate_memory_context(memory_context)
        if issues:
            logger.info("[FullPipeline] 记忆上下文验证: %s", "; ".join(issues))
        return generate_cv_tunings(memory_context)
    except Exception as exc:  # noqa: BLE001
        logger.warning("[FullPipeline] 记忆驱动CV调优生成跳过: %s", exc)
        return []
def apply_memory_cv_tunings(adjustments: dict, tunings: list) -> dict:
    if not tunings:
        return adjustments
    adjusted = apply_cv_tunings_to_config(adjustments, tunings)
    logger.info("[FullPipeline] 记忆驱动CV调优: %d条规则调整", len(tunings))
    return adjusted
__all__ = [
    "FeedbackSyncResult",
    "apply_cv_memory_enhancements",
    "apply_memory_bridge",
    "apply_memory_cv_tunings",
    "build_pipeline_context",
    "compute_feedback_effectiveness",
    "detect_oscillation_params",
    "dict_records",
    "enhance_diagnosis_with_feedback",
    "enhance_feedback_with_memory",
    "enhance_treatment_feedback_with_memory",
    "export_feedback_to_memory_ops",
    "generate_fix_result_ops",
    "generate_fp_pattern_ops",
    "generate_memory_cv_tunings",
    "generate_tp_pattern_ops",
    "get_failed_fix_avoidance",
    "get_fix_pattern_suggestions",
    "get_fixer_success_rates",
    "import_memory_to_feedback",
    "load_feedback_adjustments",
    "memory_op_dedup_key",
    "memory_op_to_dict",
    "page_text",
    "recommend_fix_strategy",
    "str_items",
    "sync_feedback_bidirectional",
    "sync_fixer_performance_to_memory",
    "text_items",
]
logger = logging.getLogger(__name__)
logger.info("memory_feedback_core 已加载: %d 项导出", len(__all__))
_GENERIC_ROW_PATTERN = (
    r"(?m)^[ \t]*\|[ \t]*([^|\r\n]+?)[ \t]*\|"
    r"[ \t]*(\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)[ \t]*\|[ \t\r]*$"
)
_FEEDBACK_KEYS = ("diagnosis_feedbacks", "cv_feedbacks", "fixer_feedbacks")
_MIN_PATTERN_COUNT = 3
_FIXER_SKIP_RATE_THRESHOLD = 0.3
_WORSENING_TRENDS = frozenset({"worsening", "needs_attention"})
_RELATED_CONCEPT_LINE = 'related: ["wiki/concepts/CodeOps-代码操作规范"]'
_TP_SAMPLE_LIMIT = 3
_TP_MULTIPLIER_CEILING = 1.1
_OSCILLATION_CHANGE_THRESHOLD = 0.5
_SUMMARY_RATE_KEYS = ("fp_rate", "review_score", "fix_success_rate")
_SUMMARY_LIST_KEYS = ("cv_tunings", "enhancements")
_SUMMARY_COUNT_KEYS = ("failed_count", "executed_count", "total_findings")
_CONFIRMED_RE = re.compile(r"(?<![a-z])confirmed(?![a-z])")
_NEGATED_CONFIRMED_RE = re.compile(
    r"(?<![a-z])(?:(?:un|non|dis)[_\s-]*confirmed"
    r"|not[_\s-]+confirmed)(?![a-z])")
_CONF_FLOOR = 0.05
_CONF_CEIL = 0.99
_DOWNGRADE_CONF_FLOOR = 0.1
_CV_TUNING_ADOPTION_AVAILABLE = "available"
def _fix_trend(rate: float) -> str:
    if rate >= 0.6:
        return "improving"
    if rate < 0.3:
        return "needs_attention"
    return "stable"
def _parse_number_rows(scope: str, pattern: str) -> dict[str, float]:
    rows: dict[str, float] = {}
    for raw_key, raw in re.findall(pattern, scope):
        key = raw_key.strip()
        if not key:
            continue
        try:
            value = float(raw)
        except ValueError as e:
            logger.debug("格式解析失败（跳过条目）: %s: %s", raw, e)
            continue
        if not math.isfinite(value):
            logger.debug("数值非有限（跳过条目）: %s=%s", key, raw)
            continue
        rows[key] = value
    return rows
@dataclass
class FeedbackSyncResult:
    exported_ops: list[DiagnosticMemoryOperation] = field(default_factory=list)
    imported_adjustments: dict = field(default_factory=dict)
    sync_errors: list[str] = field(default_factory=list)
def _materialize_feedback_export_ops(
    ops: list[DiagnosticMemoryOperation],
    memory_search_results: list[dict],
) -> list[DiagnosticMemoryOperation]:
    if not ops or not memory_search_results:
        return ops
    records = dict_records(memory_search_results)
    existing_paths = [
        record.get("path") for record in records
        if isinstance(record.get("path"), str) and record.get("path")
    ]
    ctx = DiagnosticMemoryContext(
        raw_memory_paths=existing_paths,
        raw_search_results=records,
    )
    materialized = []
    for op in ops:
        write_op = _existing_page_write_op(op, ctx)
        if write_op is not None:
            materialized.append(write_op)
    return materialized
def sync_feedback_bidirectional(
    feedback_history: dict,
    method_adjustments: dict,
    memory_search_results: list[dict],
) -> FeedbackSyncResult:
    result = FeedbackSyncResult()
    try:
        export_ops = export_feedback_to_memory_ops(
            feedback_history, method_adjustments)
        result.exported_ops = _materialize_feedback_export_ops(
            export_ops, memory_search_results)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e,
                      context=f'sync_feedback_bidirectional:{type(e).__name__}')
        result.sync_errors.append(f"export_failed: {e}")
    try:
        result.imported_adjustments = import_memory_to_feedback(memory_search_results)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e,
                      context=f'sync_feedback_bidirectional:{type(e).__name__}')
        result.sync_errors.append(f"import_failed: {e}")
    if result.sync_errors:
        logger.warning("[MemoryBridge] 反馈双向同步部分失败: %s",
                       "; ".join(result.sync_errors))
    else:
        imported_count = sum(
            len(value) for value in result.imported_adjustments.values()
            if isinstance(value, dict))
        logger.info("[MemoryBridge] 反馈双向同步完成: 导出 %d 条操作, 导入 %d 项调整",
                    len(result.exported_ops), imported_count)
    return result
def _numeric_cell(value: Any) -> str:
    return str(value).replace("|", "_").replace("\r", " ").replace("\n", " ")
def _numeric_value(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    try:
        if isinstance(value, (int, float)):
            numeric = float(value)
        elif isinstance(value, str):
            numeric = float(value.strip())
        else:
            return None
    except (TypeError, ValueError, OverflowError):
        return None
    return numeric if math.isfinite(numeric) else None
def _numeric_rows(mapping: dict) -> list[tuple[str, float]]:
    rows: list[tuple[str, float]] = []
    for key, value in mapping.items():
        if not isinstance(key, str) or not key.strip():
            continue
        numeric = _numeric_value(value)
        if numeric is None:
            continue
        rows.append((key.strip(), numeric))
    return sorted(rows, key=lambda kv: kv[0])
def _numeric_table_rows(rows: list[tuple]) -> str:
    return "".join(
        f"| {_numeric_cell(k)} | {_numeric_cell(v)} |\n" for k, v in rows)
_METHOD_ADJUSTMENT_PAGE_TITLE = "方法反馈调整历史"
_METHOD_ADJUSTMENT_MEMORY_PATH = (
    f"{WIKI_LESSONS_PREFIX}/{_METHOD_ADJUSTMENT_PAGE_TITLE}")
def _method_adjustment_op(method_adjustments: dict) -> DiagnosticMemoryOperation | None:
    multipliers = dict_or_empty(
        method_adjustments.get("method_confidence_multipliers"))
    thresholds = dict_or_empty(
        method_adjustments.get("cv_confidence_thresholds"))
    multiplier_rows = _numeric_rows(multipliers)
    threshold_rows = _numeric_rows(thresholds)
    if not (multiplier_rows or threshold_rows):
        return None
    content = f"""---
title: {_METHOD_ADJUSTMENT_PAGE_TITLE}
summary: 诊断方法置信度乘数和CV阈值的历史调整记录,跨会话持久化
{_RELATED_CONCEPT_LINE}
---

## 方法置信度乘数

| 方法ID | 乘数 |
|--------|------|
"""
    content += _numeric_table_rows(multiplier_rows)
    content += "\n## CV置信度阈值\n\n| 规则ID | 阈值 |\n|--------|------|\n"
    content += _numeric_table_rows(threshold_rows)
    return DiagnosticMemoryOperation(
        operation="add",
        path=_METHOD_ADJUSTMENT_MEMORY_PATH,
        content=content,
        category=CATEGORY_CV_TUNING,
        quality_score=7.0,
        reason=f"反馈历史同步: {len(multiplier_rows)}个方法乘数, {len(threshold_rows)}个CV阈值",
        confidence=0.8,
        tags=["feedback_sync", "method_adjustments"],
    )
def _collect_feedbacks(feedback_history: dict) -> list:
    if not isinstance(feedback_history, dict):
        return []
    feedbacks: list = []
    seen: set[int] = set()
    for _fb_key in ("feedbacks",) + tuple(_FEEDBACK_KEYS):
        for item in as_list(feedback_history.get(_fb_key)):
            marker = id(item)
            if marker in seen:
                continue
            seen.add(marker)
            feedbacks.append(item)
    return feedbacks
def _fp_feedbacks(feedbacks: list) -> list[dict]:
    return [f for f in feedbacks
            if isinstance(f, dict)
            and f.get("feedback_type") == "false_positive"]
def _fp_summary_op(fp_feedbacks: list) -> DiagnosticMemoryOperation | None:
    if not fp_feedbacks:
        return None
    return DiagnosticMemoryOperation(
        operation="add",
        path=f"{WIKI_LESSONS_PREFIX}/历史误报模式汇总",
        content=_build_fp_summary_content(fp_feedbacks),
        category=CATEGORY_FP_PATTERN,
        quality_score=8.0,
        reason=f"误报模式汇总: {len(fp_feedbacks)}条",
        confidence=0.9,
        tags=["feedback_sync", "false_positive"],
    )
def _build_fp_rule_content(rid: str, feedbacks: list[dict]) -> str:
    reasons = []
    for fb in feedbacks:
        reason = fb.get("reason")
        if isinstance(reason, str) and reason.strip():
            reasons.append(md_cell(reason.strip()[:200]))
    reason_lines = "\n".join(f"- {r}" for r in reasons[:10]) or "- 无描述"
    first_reason = reasons[0] if reasons else ""
    _rid = md_cell(rid)
    return f"""---
title: FP反馈 - {_rid}
summary: 规则{_rid}历史误报反馈{len(feedbacks)}条, FP模式学习
{_RELATED_CONCEPT_LINE}
---

## 误报反馈

| 指标 | 值 |
|------|-----|
| 规则ID | {_rid} |
| 反馈条数 | {len(feedbacks)} |

## 误报原因

原因: {first_reason}

{reason_lines}
"""
def _fp_rule_op(rid: str, feedbacks: list[dict]) -> DiagnosticMemoryOperation:
    return DiagnosticMemoryOperation(
        operation="add",
        path=f"{WIKI_LESSONS_PREFIX}/误报反馈-{path_segment(rid)}",
        content=_build_fp_rule_content(rid, feedbacks),
        category=CATEGORY_FP_PATTERN,
        quality_score=7.5,
        reason=f"规则{rid}历史误报反馈: {len(feedbacks)}条",
        rule_id=rid,
        confidence=0.8,
        tags=["feedback_sync", "false_positive", rid],
    )
def _fp_rule_ops(feedbacks: list) -> list[DiagnosticMemoryOperation]:
    grouped: dict[str, list[dict]] = {}
    for fb in feedbacks:
        if not isinstance(fb, dict):
            continue
        rid = normalize_rule_id(fb.get("target_id"))
        if rid:
            grouped.setdefault(rid, []).append(fb)
    return [_fp_rule_op(rid, items) for rid, items in grouped.items()]
def _require_mapping(value: Any, field: str) -> dict:
    if value is None:
        return {}
    if not isinstance(value, dict):
        raise TypeError(f"{field} 须为 dict，实际为 {type(value).__name__}")
    return value
def export_feedback_to_memory_ops(
    feedback_history: dict,
    method_adjustments: dict,
) -> list[DiagnosticMemoryOperation]:
    ops: list[DiagnosticMemoryOperation] = []
    feedback_history = _require_mapping(feedback_history, "feedback_history")
    method_adjustments = _require_mapping(method_adjustments, "method_adjustments")
    adjustment_op = _method_adjustment_op(method_adjustments)
    if adjustment_op is not None:
        ops.append(adjustment_op)
    feedbacks = _collect_feedbacks(feedback_history)
    fp_feedbacks = _fp_feedbacks(feedbacks)
    fp_op = _fp_summary_op(fp_feedbacks)
    if fp_op is not None:
        ops.append(fp_op)
        ops.extend(_fp_rule_ops(fp_feedbacks))
    logger.info("[MemoryBridge] 反馈导出: %d条记忆操作", len(ops))
    return ops
def page_text(record: dict) -> str:
    if not isinstance(record, dict):
        return ""
    for key in ("content", "snippet", "summary"):
        candidate = record.get(key)
        if isinstance(candidate, str) and candidate.strip():
            return candidate
    return ""
def dict_records(value: Any) -> list[dict]:
    if value is None or isinstance(value, (str, bytes)):
        return []
    if isinstance(value, dict):
        return [value]
    if isinstance(value, Iterable):
        return [item for item in value if isinstance(item, dict)]
    raise TypeError(f"记录容器类型非法: {type(value).__name__}")
def text_items(value: Any) -> list[str]:
    if value is None or isinstance(value, (bytes, dict)):
        return []
    if isinstance(value, str):
        return [value]
    if isinstance(value, Iterable):
        return [str(item) for item in value if item is not None]
    raise TypeError(f"证据项类型非法: {type(value).__name__}")
def str_items(value: Any) -> list[str]:
    if value is None or isinstance(value, (bytes, dict)):
        return []
    if isinstance(value, str):
        return [value]
    if isinstance(value, Iterable):
        return [item for item in value if isinstance(item, str)]
    raise TypeError(f"字符串项类型非法: {type(value).__name__}")
def _split_feedback_sections(content: str) -> tuple[str, str]:
    if "## CV置信度阈值" in content:
        multiplier_scope, _, threshold_scope = content.partition("## CV置信度阈值")
        return multiplier_scope, threshold_scope
    return content, ""
def _markdown_level_two_section(content: str, title: str) -> str | None:
    heading = re.search(
        rf"(?m)^ {{0,3}}##[ \t]+{re.escape(title)}[ \t]*\r?$", content)
    if heading is None:
        return None
    section = content[heading.end():]
    next_heading = re.search(r"(?m)^ {0,3}##[ \t]+", section)
    if next_heading is not None:
        section = section[:next_heading.start()]
    return section
def _parse_method_multiplier_rows(content: str, legacy_scope: str) -> dict[str, float]:
    section = _markdown_level_two_section(content, "方法置信度乘数")
    if section is None:
        if re.search(r"(?m)^ {0,3}#{2,6}[ \t]+", content):
            if _parse_number_rows(legacy_scope, _GENERIC_ROW_PATTERN):
                logger.warning(
                    "[MemoryBridge] 方法页含未归属数值表，跳过乘数解析")
            return {}
        return _parse_number_rows(legacy_scope, _GENERIC_ROW_PATTERN)
    return _parse_number_rows(section, _GENERIC_ROW_PATTERN)
def _is_method_adjustment_record(record: dict) -> bool:
    if not isinstance(record, dict):
        return False
    path = record.get("path")
    if isinstance(path, str) and path:
        return path == _METHOD_ADJUSTMENT_MEMORY_PATH
    if path not in (None, ""):
        return False
    return any(
        isinstance(text, str) and (
            _METHOD_ADJUSTMENT_PAGE_TITLE in text
            or "## 方法置信度乘数" in text)
        for text in (record.get("content"), record.get("snippet"),
                     record.get("summary")))
def import_memory_to_feedback(
    memory_search_results: list[dict],
) -> dict:
    adjustments: dict = {
        "method_confidence_multipliers": {},
        "cv_confidence_thresholds": {},
        "_imported_from_memory": False,
    }
    for mem in dict_records(memory_search_results):
        if not _is_method_adjustment_record(mem):
            continue
        content = page_text(mem)
        if not content:
            continue
        multiplier_scope, threshold_scope = _split_feedback_sections(content)
        threshold_section = _markdown_level_two_section(content, "CV置信度阈值")
        if threshold_section is not None:
            threshold_scope = threshold_section
        adjustments["method_confidence_multipliers"].update(
            _parse_method_multiplier_rows(content, multiplier_scope))
        adjustments["cv_confidence_thresholds"].update(
            _parse_number_rows(threshold_scope, _GENERIC_ROW_PATTERN))
    logger.info("[MemoryBridge] 反馈导入: %d个方法乘数, %d个CV阈值",
               len(adjustments["method_confidence_multipliers"]),
               len(adjustments["cv_confidence_thresholds"]))
    if (adjustments["method_confidence_multipliers"]
            or adjustments["cv_confidence_thresholds"]):
        adjustments["_imported_from_memory"] = True
    return adjustments
def _build_fp_summary_content(fp_feedbacks: list[dict]) -> str:
    lines = ["| 规则ID | 误报类型 | 描述 |", "|--------|---------|------|"]
    for fb in fp_feedbacks:
        rid = md_cell(str(fb.get("target_id") or ""))
        ftype = md_cell(str(fb.get("feedback_type") or ""))
        desc = md_cell(str(fb.get("reason") or "")[:80])
        lines.append(f"| {rid} | {ftype} | {desc} |")
    return f"""---
title: 历史误报模式汇总
summary: {len(fp_feedbacks)}条误报模式记录, 跨会话FP模式学习
{_RELATED_CONCEPT_LINE}
---
## 误报模式列表
{chr(10).join(lines)}
"""
def memory_op_to_dict(op: object) -> dict:
    read = (op.get if isinstance(op, dict)
            else lambda key, default="": getattr(op, key, default))
    tags = read("tags", [])
    operation = read("operation", "")
    if not isinstance(operation, str) or not operation.strip():
        action = read("action", "")
        operation = action if isinstance(action, str) else ""
    operation = operation.strip()
    return {
        "operation": operation,
        "path": read("path", ""),
        "content": read("content", "") or "",
        "old_text": read("old_text", "") or "",
        "category": read("category", ""),
        "quality_score": read("quality_score", 0.0),
        "reason": read("reason", ""),
        "rule_id": read("rule_id", ""),
        "confidence": read("confidence", 0.0),
        "tags": (list(tags) if isinstance(tags, (list, tuple))
                 else sorted(tags, key=str)
                 if isinstance(tags, (set, frozenset)) else []),
    }
def _append_exported_feedback_ops(
    memory_ops: list[dict], feedbacks: list,
) -> None:
    export_ops = export_feedback_to_memory_ops(
        {"feedbacks": as_list(feedbacks)}, {})
    for op in export_ops:
        memory_ops.append(memory_op_to_dict(op))
def memory_op_dedup_key(op: dict) -> tuple[str, str] | None:
    if not isinstance(op, dict):
        return None
    operation = op.get("operation")
    if not isinstance(operation, str) or not operation.strip():
        operation = op.get("action")
    path = op.get("path")
    if not isinstance(operation, str) or not isinstance(path, str):
        return None
    operation, path = operation.strip(), path.strip()
    if not operation or not path:
        return None
    return (operation, path)
def _dedup_keys(ops: list[dict]) -> set[tuple[str, str]]:
    return {
        key for op in ops
        if (key := memory_op_dedup_key(op)) is not None
    }
def _memory_op_contract_valid(op: Any) -> bool:
    """记忆操作是否满足写入契约（与 ``validated_memory_operations`` 同源）。"""
    # lazy-by-design：契约校验位于上层 memory_bridge_ops，模块级反向导入会成环。
    from jwsgj.memory_bridge_ops import (  # noqa: PLC0415
        _memory_op_payload, memory_operation_issue)
    payload = (op if isinstance(op, dict) and op.get("action")
               else _memory_op_payload(op))
    return memory_operation_issue(payload, 0) is None
def _merge_preserved_memory_ops(memory_ops: list[dict],
                                feedback_result: dict) -> list[dict]:
    preserved = [
        (op if op.get("operation") else memory_op_to_dict(op))
        if isinstance(op, dict) else memory_op_to_dict(op)
        for op in as_list(feedback_result.get("_memory_operations"))
        if isinstance(op, dict) or hasattr(op, "operation")
    ]
    if not preserved:
        return memory_ops
    seen = _dedup_keys(preserved)
    merged = list(preserved)
    replaced_invalid = 0
    for op in memory_ops:
        key = memory_op_dedup_key(op)
        if key is None:
            merged.append(op)
            continue
        if key not in seen:
            seen.add(key)
            merged.append(op)
            continue
        # 同键冲突：保留项契约有效则保留项优先；保留项无效（下游校验必丢）时
        # 由契约有效的新操作顶替其位，否则有效操作会被无效旧项静默吞掉——
        # 与 extend_ops_deduped 的同键处理口径一致。
        if not _memory_op_contract_valid(op):
            continue
        same_key = [index for index, existing in enumerate(merged)
                    if memory_op_dedup_key(existing) == key]
        # 同键已有契约有效的保留项（无论位置）则保留项优先，不得再塞一份
        # 造成重复写入；仅当同键全部无效时才顶替第一条。
        if not same_key or any(
                _memory_op_contract_valid(merged[index])
                for index in same_key):
            continue
        merged[same_key[0]] = op
        replaced_invalid += 1
    if replaced_invalid:
        logger.info("[MemoryBridge] 以有效操作替换 %d 条同键无效保留操作",
                    replaced_invalid)
    return merged
def _append_tp_pattern_ops(memory_ops: list[dict], enhanced: dict,
                           ctx: DiagnosticMemoryContext) -> None:
    cv_results = enhanced.get("stage2_cross_validation")
    if not isinstance(cv_results, dict) or not cv_results:
        cv_results = enhanced.get("cv_report") or {}
    if not isinstance(cv_results, dict):
        cv_results = {}
    if not cv_results:
        return
    tp_ops = generate_tp_pattern_ops(cv_results, str_memory_paths(ctx))
    for op in tp_ops:
        memory_ops.append(memory_op_to_dict(op))
def _append_calibration_ops(memory_ops: list[dict],
                            ctx: DiagnosticMemoryContext) -> None:
    calibrations = get_rule_severity_calibrations(ctx)
    known_paths = str_memory_paths(ctx)
    for cal in calibrations:
        if not isinstance(cal, dict):
            continue
        rid = cal.get("rule_id", "")
        if not isinstance(rid, str) or not rid:
            continue
        _sev = cal.get("suggested_severity") or ""
        _cal_reason = cal.get("reason") or ""
        path = f"{WIKI_LESSONS_PREFIX}/严重性校准-{path_segment(rid)}"
        if path in known_paths:
            continue
        _rid_cell = md_cell(rid)
        _sev_cell = md_cell(str(_sev))
        _reason_cell = md_cell(str(_cal_reason))
        memory_ops.append({
            "operation": "add",
            "path": path,
            "content": f"""---
title: 严重性校准 - {_rid_cell}
summary: 规则{_rid_cell}建议严重性调整为{_sev_cell}
{_RELATED_CONCEPT_LINE}
---

## 校准建议

| 指标 | 值 |
|------|-----|
| 规则ID | {_rid_cell} |
| 建议严重性 | {_sev_cell} |
| 原因 | {_reason_cell} |
""",
            "category": CATEGORY_CV_TUNING,
            "quality_score": 7.0,
            "reason": _cal_reason,
            "rule_id": rid,
        })
        known_paths.add(path)
def _enhance_with_memory_ops(feedback_result: dict,
                             ctx: DiagnosticMemoryContext | None,
                             collect, domain: str) -> dict:
    if not isinstance(feedback_result, dict):
        feedback_result = {}
    if not ctx:
        return feedback_result
    enhanced = dict(feedback_result)
    memory_ops: list[dict] = []
    try:
        collect(memory_ops, enhanced, ctx)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] %s异常: %s", domain, e)
    enhanced["_memory_operations"] = _merge_preserved_memory_ops(
        memory_ops, feedback_result)
    return enhanced
def enhance_feedback_with_memory(
    feedback_result: dict,
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    return _enhance_with_memory_ops(
        feedback_result, ctx, _append_feedback_sections, domain="反哺记忆增强")
def _append_feedback_sections(memory_ops: list[dict], enhanced: dict,
                              ctx: DiagnosticMemoryContext) -> None:
    _append_tp_pattern_ops(memory_ops, enhanced, ctx)
    _append_calibration_ops(memory_ops, ctx)
    feedbacks = _collect_feedbacks(enhanced)
    if feedbacks:
        _append_exported_feedback_ops(memory_ops, feedbacks)
def _collect_cv_tuning(ctx: DiagnosticMemoryContext, report: dict) -> bool:
    tuning_count = sum(
        1 for item in as_list(ctx.cv_tuning_history)
        if isinstance(item, dict) and normalize_rule_id(item.get("rule_id")))
    if tuning_count <= 0:
        return False
    report["metrics"]["cv_tuning_count"] = tuning_count
    report["metrics"]["cv_tuning_adoption"] = _CV_TUNING_ADOPTION_AVAILABLE
    return True
def _collect_fp_trend(ctx: DiagnosticMemoryContext, report: dict) -> bool:
    patterns = as_list(ctx.known_fp_patterns)
    rule_freq = _pattern_rule_counts(patterns)
    valid_patterns = sum(rule_freq.values())
    if valid_patterns <= 0:
        return False
    persistent_fp = sum(
        1 for count in rule_freq.values() if count >= _MIN_PATTERN_COUNT)
    report["metrics"]["fp_patterns"] = valid_patterns
    report["metrics"]["persistent_fp_rules"] = persistent_fp
    report["metrics"]["fp_trend"] = _fp_trend_label(
        persistent_fp, len(rule_freq))
    return True
def _unique_pattern_dicts(patterns: Any) -> list[dict]:
    unique: list[dict] = []
    seen: set[int] = set()
    for item in as_list(patterns):
        if not isinstance(item, dict) or id(item) in seen:
            continue
        seen.add(id(item))
        unique.append(item)
    return unique
def _pattern_rule_counts(patterns: Any) -> dict[str, int]:
    counts: dict[str, int] = {}
    for item in _unique_pattern_dicts(patterns):
        rid = normalize_rule_id(item.get("rule_id"))
        if rid:
            counts[rid] = counts.get(rid, 0) + 1
    return counts
def _fp_trend_label(persistent_fp: int, legal_rule_count: int) -> str:
    if legal_rule_count <= 0:
        return "unknown"
    if persistent_fp < legal_rule_count * 0.3:
        return "improving"
    if persistent_fp < legal_rule_count * 0.6:
        return "stable"
    return "worsening"
def _fix_records(historical_fix_rates: dict) -> list[dict]:
    records: list[dict] = []
    seen: set[int] = set()
    for rates in historical_fix_rates.values():
        for record in as_list(rates):
            if not isinstance(record, dict) or id(record) in seen:
                continue
            seen.add(id(record))
            records.append(record)
    return records
def _collect_fix_rate_trend(ctx: DiagnosticMemoryContext, report: dict) -> bool:
    _hfr = dict_or_empty(ctx.historical_fix_rates)
    records = [record for record in _fix_records(_hfr)
               if _has_fix_verdict(record)]
    if not records:
        return False
    success_count = sum(1 for record in records if fix_succeeded(record))
    overall_rate = success_count / len(records)
    report["metrics"]["fix_success_rate"] = round(overall_rate, 3)
    report["metrics"]["fix_trend"] = _fix_trend(overall_rate)
    return True
def _explicit_number(diag_summary: dict, key: str) -> float | None:
    value = diag_summary.get(key)
    if value is None:
        return None
    parsed = safe_float(value, default=math.nan)
    return None if not math.isfinite(parsed) else parsed
def _write_fix_rate(metrics: dict, rate: float) -> None:
    clamped = min(1.0, max(0.0, rate))
    metrics["fix_success_rate"] = round(clamped, 3)
    metrics["fix_trend"] = _fix_trend(clamped)
def _apply_summary_fix_rate(metrics: dict, explicit_fix_rate: float | None,
                            executed_count: float,
                            failed_count: float) -> None:
    if explicit_fix_rate is not None and "fix_success_rate" not in metrics:
        _write_fix_rate(metrics, explicit_fix_rate)
    if executed_count > 0 and "fix_success_rate" not in metrics:
        _write_fix_rate(metrics, (executed_count - failed_count) / executed_count)
def _fp_trend_of(rate: float) -> str:
    return ("improving" if rate < 0.2
            else "stable" if rate < 0.4
            else "worsening")
def _write_fp_rate(metrics: dict, rate: float) -> None:
    clamped = min(1.0, max(0.0, rate))
    metrics["fp_rate"] = round(clamped, 3)
    metrics["fp_trend"] = _fp_trend_of(clamped)
def _apply_summary_fp_rate(metrics: dict, explicit_fp_rate: float | None) -> None:
    if explicit_fp_rate is not None and "fp_rate" not in metrics:
        _write_fp_rate(metrics, explicit_fp_rate)
def _summary_metric_inputs(diag_summary: dict) -> dict:
    return {
        "cv_tunings": as_list(diag_summary.get("cv_tunings")),
        "enhancements": as_list(diag_summary.get("enhancements")),
        "failed_count": safe_float(diag_summary.get("failed_count", 0)),
        "executed_count": safe_float(diag_summary.get("executed_count", 0)),
        "fix_success_rate": _explicit_number(diag_summary, "fix_success_rate"),
        "fp_rate": _explicit_number(diag_summary, "fp_rate"),
        "review_score": _explicit_number(diag_summary, "review_score"),
        "total_findings": safe_float(diag_summary.get("total_findings", 0)),
    }
def _summary_contributes(inputs: dict) -> bool:
    if any(inputs[key] is not None for key in _SUMMARY_RATE_KEYS):
        return True
    if any(inputs[key] for key in _SUMMARY_LIST_KEYS):
        return True
    return any(inputs[key] > 0 for key in _SUMMARY_COUNT_KEYS)
def _collect_summary_metrics(diag_summary: dict, report: dict) -> bool:
    inputs = _summary_metric_inputs(diag_summary)
    if not _summary_contributes(inputs):
        return False
    metrics = report["metrics"]
    before = len(metrics)
    if inputs["cv_tunings"] and "cv_tuning_count" not in metrics:
        metrics["cv_tuning_count"] = len(inputs["cv_tunings"])
        metrics["cv_tuning_adoption"] = _CV_TUNING_ADOPTION_AVAILABLE
    if inputs["enhancements"]:
        metrics["enhancement_count"] = len(inputs["enhancements"])
    for _key in ("executed_count", "failed_count", "total_findings"):
        if inputs[_key] > 0:
            metrics[_key] = int(inputs[_key])
    _apply_summary_fix_rate(metrics, inputs["fix_success_rate"],
                            inputs["executed_count"], inputs["failed_count"])
    _apply_summary_fp_rate(metrics, inputs["fp_rate"])
    if inputs["review_score"] is not None:
        metrics["review_score"] = round(
            min(100.0, max(0.0, inputs["review_score"])), 1)
    return len(metrics) > before
def _trend_counts(metrics: dict) -> tuple[int, int]:
    improving = worsening = 0
    for value in metrics.values():
        if not isinstance(value, str):
            continue
        if value == "improving":
            improving += 1
        elif value in _WORSENING_TRENDS:
            worsening += 1
    return improving, worsening
def _assess_overall_effectiveness(report: dict) -> None:
    improving, worsening = _trend_counts(report["metrics"])
    if improving > worsening:
        report["overall_effectiveness"] = "effective"
    elif worsening > improving:
        report["overall_effectiveness"] = "needs_improvement"
    else:
        report["overall_effectiveness"] = "moderate"
def _build_effectiveness_suggestions(report: dict) -> list[str]:
    suggestions: list[str] = []
    if report["metrics"].get("fp_trend") == "worsening":
        suggestions.append("FP趋势恶化: 建议提高高FP规则的CV阈值，或禁用持续误报的规则")
    if report["metrics"].get("fix_trend") == "needs_attention":
        suggestions.append("修复成功率低: 建议检查失败修复器，优先使用高成功率修复器")
    if report["metrics"].get("persistent_fp_rules", 0) > 5:
        suggestions.append(f"存在{report['metrics']['persistent_fp_rules']}个顽固FP规则: 建议分析根因并考虑规则重写或禁用")
    if not suggestions:
        improving, worsening = _trend_counts(report["metrics"])
        if improving and not worsening:
            suggestions.append(
                "当前反馈趋势向好，暂无需要干预的恶化项，建议持续观察")
        else:
            suggestions.append(
                "暂无可判定的改善/恶化趋势，建议继续积累数据以获得更精确的评估")
    return suggestions
def compute_feedback_effectiveness(
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    report: dict[str, Any] = {
        "overall_effectiveness": "unknown",
        "metrics": {},
        "suggestions": [],
        "has_data": False,
    }
    if not ctx:
        return report
    try:
        if _collect_effectiveness_metrics(ctx, report):
            report["has_data"] = True
            _assess_overall_effectiveness(report)
            report["suggestions"] = _build_effectiveness_suggestions(report)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 反馈效果评估异常: %s", e)
    return report
def _collect_effectiveness_metrics(ctx: DiagnosticMemoryContext,
                                   report: dict) -> bool:
    has_data = False
    for collector in (_collect_cv_tuning, _collect_fp_trend,
                      _collect_fix_rate_trend):
        if collector(ctx, report):
            has_data = True
    diag_summary = (ctx.last_diagnosis_summary
                    if isinstance(ctx.last_diagnosis_summary, dict) else {})
    if diag_summary and _collect_summary_metrics(diag_summary, report):
        has_data = True
    return has_data
def _group_rule_fixes(details: list) -> dict[str, list[dict]]:
    rule_fixes: dict[str, list[dict]] = {}
    for detail in details:
        if not isinstance(detail, dict):
            continue
        raw_rid = detail.get("rule_id", "")
        rid = normalize_rule_id(raw_rid)
        if rid is None:
            if raw_rid:
                logger.warning(
                    "[MemoryBridge] generate_fix_result_ops: 条目 "
                    "rule_id 非法（实际 %s），跳过该条",
                    type(raw_rid).__name__)
            continue
        rule_fixes.setdefault(rid, []).append(detail)
    return rule_fixes
def _success_count(fixes: list[dict]) -> int:
    return sum(1 for f in fixes if fix_succeeded(f))
def _failed_fix_verdict(fix_info: dict) -> bool:
    if not isinstance(fix_info, dict) or fix_succeeded(fix_info):
        return False
    return (fix_failed(fix_info)
            or fix_info.get("success") is False
            or fix_info.get("status") in TX_ROLLED_BACK_STATUSES)
def _fail_count(fixes: list[dict]) -> int:
    return sum(1 for f in fixes if _failed_fix_verdict(f))
def _decided_fix_counts(fixes: list[dict]) -> tuple[int, int, float]:
    success_count = _success_count(fixes)
    fail_count = _fail_count(fixes)
    decided = success_count + fail_count
    return success_count, fail_count, (success_count / decided if decided else 0)
def _fix_result_op(
    path: str, rid: str, fixes: list[dict],
    success_rate: float, quality: float, counts: tuple[int, int],
    *, exists: bool,
) -> DiagnosticMemoryOperation:
    success_count, fail_count = counts
    if exists:
        operation = "patch"
        content = _build_fix_result_patch(fixes, success_rate)
        reason = f"规则{rid}修复结果更新: {success_count}成功/{fail_count}失败"
        old_text = "<!-- 待更新 -->"
    else:
        operation = "add"
        content = _build_fix_result_content(rid, fixes, success_rate)
        reason = f"规则{rid}修复经验记录: {success_count}成功/{fail_count}失败"
        old_text = ""
    return DiagnosticMemoryOperation(
        operation=operation,
        path=path,
        content=content,
        old_text=old_text,
        category=CATEGORY_FIX_RESULT,
        quality_score=quality,
        reason=reason,
        rule_id=rid,
        confidence=success_rate,
        tags=["fix_result", rid],
    )
def _fix_result_op_for_rule(
    rid: str, fixes: list[dict], existing: set[str],
) -> DiagnosticMemoryOperation | None:
    success_count, fail_count, success_rate = _decided_fix_counts(fixes)
    if success_count == 0 and fail_count < 2:
        return None
    quality = 7.0 if success_rate > 0.5 else 8.0
    path = f"{WIKI_LESSONS_PREFIX}/修复经验-{path_segment(rid)}"
    return _fix_result_op(
        path, rid, fixes, success_rate, quality,
        (success_count, fail_count), exists=path in existing)
def _existing_path_set(existing_paths: set[str] | None) -> set[str]:
    return existing_paths or set()
def generate_fix_result_ops(
    treatment_results: dict,
    existing_paths: set[str] | None = None,
) -> list[DiagnosticMemoryOperation]:
    ops: list[DiagnosticMemoryOperation] = []
    existing = _existing_path_set(existing_paths)
    try:
        rule_fixes = _group_rule_fixes(treatment_items(treatment_results))
        for rid, fixes in rule_fixes.items():
            op = _fix_result_op_for_rule(rid, fixes, existing)
            if op is not None:
                ops.append(op)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 修复经验操作生成异常: %s", e)
    if ops:
        logger.info("[MemoryBridge] 修复经验沉淀: %d条记忆操作", len(ops))
    return ops
_SOURCE_FINDING_ID = "_memory_source_id"
def _with_entry_defaults(finding: dict, defaults: tuple) -> dict:
    flat = dict(finding)
    flat.setdefault(_SOURCE_FINDING_ID, id(finding))
    for _key, _value in defaults:
        flat.setdefault(_key, _value)
    return flat
def _entry_leaf_finding(entry: dict) -> dict | None:
    sample = entry.get("sample_finding")
    if isinstance(sample, dict) and sample:
        return sample
    if any(key in entry for key in ("rule_id", "type", "rule_family", "file")):
        return entry
    return None
def _normalized_rule_finding(finding: dict) -> dict | None:
    if not isinstance(finding, dict):
        return None
    rid = (normalize_rule_id(finding.get("rule_id"))
           or normalize_rule_id(finding.get("type"))
           or normalize_rule_id(finding.get("rule_family")))
    if not rid:
        return None
    if finding.get("rule_id") == rid:
        return finding
    normalized = dict(finding)
    normalized["rule_id"] = rid
    return normalized
def _flatten_index_entry(locator, entry: dict) -> list[dict]:
    _defaults = (("locator", locator),
                 ("rule_family", entry.get("rule_family")),
                 ("conclusion", entry.get("conclusion")),
                 ("status", entry.get("status")),
                 ("_degrade_status", entry.get("_degrade_status")),
                 ("_partial_degrade", entry.get("_partial_degrade")),
                 ("_is_degraded", entry.get("_is_degraded")),
                 ("degrade_status", entry.get("degrade_status")))
    inner = entry.get("findings")
    if isinstance(inner, list) and inner:
        usable = []
        for finding in inner:
            if not isinstance(finding, dict):
                continue
            normalized = _normalized_rule_finding(
                _with_entry_defaults(finding, _defaults))
            if normalized is not None:
                usable.append(normalized)
        if usable:
            return usable
    leaf = _entry_leaf_finding(entry)
    if leaf is None:
        return []
    normalized = _normalized_rule_finding(
        _with_entry_defaults(leaf, _defaults))
    return [normalized] if normalized is not None else []
def _flatten_index_list(index: list) -> list[dict]:
    flattened: list[dict] = []
    for entry in index:
        if not isinstance(entry, dict):
            continue
        locator = entry.get("locator")
        flattened.extend(_flatten_index_entry(
            locator if isinstance(locator, str) else "", entry))
    return flattened
def _flatten_cv_index_findings(cv_results: dict) -> list[dict]:
    if not isinstance(cv_results, dict):
        return []
    index = cv_results.get("findings_index")
    if isinstance(index, list):
        return _flatten_index_list(index)
    if not isinstance(index, dict):
        return []
    flattened: list[dict] = []
    for locator, entry in index.items():
        if isinstance(entry, dict):
            flattened.extend(_flatten_index_entry(locator, entry))
    return flattened
def _first_finding_list(*candidates, seen: set[int] | None = None) -> list:
    for candidate in candidates:
        if not isinstance(candidate, list):
            continue
        findings = []
        for finding in candidate:
            if not isinstance(finding, dict):
                continue
            marker = finding.get(_SOURCE_FINDING_ID, id(finding))
            if seen is not None and marker in seen:
                continue
            normalized = _normalized_rule_finding(finding)
            if normalized is not None:
                findings.append(normalized)
                if seen is not None:
                    seen.add(marker)
        if findings:
            return findings
    return []
def _confirmed_findings(entries) -> list:
    if not isinstance(entries, list):
        return []
    return [f for f in entries if _is_confirmed_finding(f)]
def _degraded_locator_key(finding: dict) -> tuple[str, str] | None:
    locator = finding.get("locator")
    if not isinstance(locator, str) or not locator.strip():
        return None
    # 派生 degraded_findings 只携带 rule_family；主记录优先使用同一身份，
    # 避免 rule_id 与 rule_family 不同时把同一条发现重复计入两个规则。
    rid = (normalize_rule_id(finding.get("rule_family"))
           or normalize_rule_id(finding.get("rule_id")))
    return (locator.strip(), rid) if rid else None
def _dedup_derived_degraded(findings: list, degraded: list) -> list:
    covered: dict[tuple[str, str], int] = {}
    for finding in findings:
        if "degrad" not in _fp_conclusion_text(finding):
            continue
        key = _degraded_locator_key(finding)
        if key is not None:
            covered[key] = covered.get(key, 0) + 1
    unique: list = []
    for finding in degraded:
        key = _degraded_locator_key(finding)
        remaining = covered.get(key, 0) if key is not None else 0
        if remaining:
            covered[key] = remaining - 1
        else:
            unique.append(finding)
    return unique
def _resolve_fp_findings(cv_results: dict) -> list:
    cv_results = unwrap_cv_results(cv_results)
    seen: set[int] = set()
    findings = _first_finding_list(cv_results.get("findings"), seen=seen)
    if not findings:
        findings = _first_finding_list(
            _flatten_cv_index_findings(cv_results),
            cv_results.get("confirmed_findings"), seen=seen)
    degraded = _first_finding_list(
        cv_results.get("degraded_findings"), seen=seen)
    return [*findings, *_dedup_derived_degraded(findings, degraded)]
_FP_CONCLUSION_FIELDS = ("conclusion", "status", "degrade_status")
_FP_REJECT_MARKERS = ("reject", "false", "suppress")
_DEGRADE_STATUS_VALUES = frozenset({"degraded", "partial_degraded"})
def _is_rejected_conclusion(conclusion_lower: str) -> bool:
    return ("degrad" in conclusion_lower
            or any(marker in conclusion_lower for marker in _FP_REJECT_MARKERS))
def _degrade_status_signal(finding: dict) -> str:
    status = finding.get("_degrade_status")
    if isinstance(status, str) and status in _DEGRADE_STATUS_VALUES:
        return status
    if signal_bool(finding.get("_partial_degrade")):
        return "partial_degraded"
    if signal_bool(finding.get("_is_degraded")):
        return "degraded"
    status = finding.get("degrade_status")
    if isinstance(status, str) and status in _DEGRADE_STATUS_VALUES:
        return status
    return ""
def _fp_conclusion_text(finding: dict) -> str:
    fallback = ""
    for key in _FP_CONCLUSION_FIELDS:
        text = pick_text(finding, (key,)).strip().lower()
        if not text:
            continue
        if not fallback:
            fallback = text
        if _is_confirmed_conclusion(text) or _is_rejected_conclusion(text):
            return text
    return _degrade_status_signal(finding) or fallback
def _bucket_fp_conclusion(stats: dict, conclusion_lower: str) -> None:
    if _is_confirmed_conclusion(conclusion_lower):
        stats["confirmed"] += 1
    elif "degrad" in conclusion_lower:
        stats["degraded"] += 1
    elif _is_rejected_conclusion(conclusion_lower):
        stats["rejected"] += 1
def _accumulate_fp_rule_stats(all_findings: list) -> dict[str, dict]:
    rule_stats: dict[str, dict] = {}
    for rid, finding in iter_rule_findings(all_findings):
        stats = rule_stats.setdefault(
            rid, {"total": 0, "confirmed": 0, "degraded": 0, "rejected": 0})
        stats["total"] += 1
        _bucket_fp_conclusion(stats, _fp_conclusion_text(finding))
    return rule_stats
def generate_fp_pattern_ops(
    cv_results: dict,
    existing_paths: set[str] | None = None,
) -> list[DiagnosticMemoryOperation]:
    ops: list[DiagnosticMemoryOperation] = []
    existing = _existing_path_set(existing_paths)
    all_findings = _resolve_fp_findings(cv_results)
    rule_stats = _accumulate_fp_rule_stats(all_findings)
    for rid, stats in rule_stats.items():
        if stats["total"] < 3:
            continue
        fp_count = _fp_flagged_count(stats)
        fp_rate = fp_count / stats["total"]
        if fp_rate < 0.5:
            continue
        path = _fp_pattern_path(rid)
        if path in existing:
            continue
        ops.append(_fp_pattern_op(rid, stats, fp_count, fp_rate))
    return ops
def _fp_flagged_count(stats: dict) -> int:
    return stats["degraded"] + stats["rejected"]
def _build_fp_pattern_content(rule_id: str, stats: dict, fp_rate: float) -> str:
    _rid = md_cell(rule_id)
    fp_count = _fp_flagged_count(stats)
    adjustment, multiplier = fp_tuning_params(fp_rate)
    return f"""---
title: FP模式 - {_rid}
summary: 规则{_rid}误报率{fp_rate:.0%}, 统计{stats['total']}次发现中{fp_count}次误报
{_RELATED_CONCEPT_LINE}
---

## 误报模式

| 指标 | 值 |
|------|-----|
| 规则ID | {_rid} |
| 总发现数 | {stats['total']} |
| 确认数 | {stats['confirmed']} |
| 降级数 | {stats['degraded']} |
| 拒绝数 | {stats['rejected']} |
| 误报率 | {fp_rate:.1%} |

## 调优建议

- CV阈值建议提高 {adjustment}
- 置信度乘数建议设为 {multiplier}
- 原因：该规则历史误报率过高，需要更严格的前置条件检查
"""
def _fp_pattern_path(rid: str) -> str:
    return f"{WIKI_LESSONS_PREFIX}/FP模式-{path_segment(rid)}"
def _fp_pattern_op(rid: str, stats: dict, fp_count: int,
                   fp_rate: float) -> DiagnosticMemoryOperation:
    return DiagnosticMemoryOperation(
        operation="add",
        path=_fp_pattern_path(rid),
        content=_build_fp_pattern_content(rid, stats, fp_rate),
        category=CATEGORY_FP_PATTERN,
        quality_score=min(10.0, 4.0 + fp_rate * 6),
        reason=f"规则{rid}误报率{fp_rate:.0%}({fp_count}/{stats['total']})",
        rule_id=rid,
        confidence=fp_rate,
        tags=["false_positive", rid],
    )
def detect_oscillation_params(
    cv_results: dict,
    ctx: DiagnosticMemoryContext | None,
) -> list[DiagnosticMemoryOperation]:
    ops: list[DiagnosticMemoryOperation] = []
    last_summary = last_summary_dict(ctx)
    if not last_summary:
        return ops
    cv_results = unwrap_cv_results(cv_results)
    current_rules = rules_triggered_signal(cv_results)
    if current_rules is None:
        return ops
    previous_rules = safe_int(
        pick_first(last_summary, ("cv_rules_triggered",), 0))
    if previous_rules <= 0:
        return ops
    change_ratio = abs(current_rules - previous_rules) / previous_rules
    if change_ratio > _OSCILLATION_CHANGE_THRESHOLD:
        ops.append(_oscillation_op(
            previous_rules, current_rules, change_ratio,
            memory_date_stamp()))
    return ops
def _oscillation_op(previous_rules: int, current_rules: int,
                    change_ratio: float, ts: str) -> DiagnosticMemoryOperation:
    return DiagnosticMemoryOperation(
        operation="add",
        path=f"{WIKI_LESSONS_PREFIX}/振荡参数-CV规则触发数-{ts}",
        content=_build_oscillation_content(
            previous_rules, current_rules, change_ratio, ts),
        category=CATEGORY_OSCILLATION,
        quality_score=6.0,
        reason=(f"CV规则触发数振荡: {previous_rules}→{current_rules}"
                f"({change_ratio:.0%})"),
        confidence=0.7,
        tags=["oscillation", "cv_rules"],
    )
def _build_oscillation_content(previous_rules: int, current_rules: int,
                               change_ratio: float, ts: str) -> str:
    return f"""---
title: 振荡参数 - CV规则触发数 ({ts})
summary: CV规则触发数{previous_rules}→{current_rules}波动{change_ratio:.0%}, 超出±{_OSCILLATION_CHANGE_THRESHOLD:.0%}稳定带
{_RELATED_CONCEPT_LINE}
---

## 振荡检测

| 指标 | 上次 | 本次 | 变化率 |
|------|------|------|--------|
| CV规则触发数 | {previous_rules} | {current_rules} | {change_ratio:.0%} |

## 档案

- 参数: CV规则触发数
- 安全值: {_OSCILLATION_CHANGE_THRESHOLD}
- 原因: 触发数{previous_rules}→{current_rules}波动{change_ratio:.0%}，超出±{_OSCILLATION_CHANGE_THRESHOLD:.0%}稳定带

## 波动归因

CV规则触发数大幅波动的常见来源：
1. 代码变更导致规则匹配模式变化
2. CV阈值调整过于激进
3. 增量分析模式下中间结果过期

## 建议

- 使用增量模式时确保中间结果时效性
- CV阈值调整幅度限制在±0.2以内（与单次最大调整步长一致）
- 关注触发数变化对应的代码变更区域
"""
def _is_confirmed_conclusion(conclusion_lower: str) -> bool:
    return (_CONFIRMED_RE.search(conclusion_lower) is not None
            and not _NEGATED_CONFIRMED_RE.search(conclusion_lower))
def _is_confirmed_finding(f) -> bool:
    if not isinstance(f, dict):
        return False
    for key in ("conclusion", "status"):
        text = pick_text(f, (key,)).strip().lower()
        if not text:
            continue
        if _is_confirmed_conclusion(text):
            return True
        if (_NEGATED_CONFIRMED_RE.search(text)
                or _is_rejected_conclusion(text)):
            return False
    return False
def _resolve_tp_findings(cv_results: dict) -> list:
    cv_results = unwrap_cv_results(cv_results)
    seen: set[int] = set()
    findings = _first_finding_list(
        cv_results.get("confirmed_findings"), seen=seen)
    if not findings:
        findings = _first_finding_list(
            _confirmed_findings(cv_results.get("findings")),
            _confirmed_findings(_flatten_cv_index_findings(cv_results)),
            seen=seen)
    return findings
def _accumulate_tp_rule_stats(findings: list) -> dict[str, dict]:
    rule_stats: dict[str, dict] = {}
    for rid, finding in iter_rule_findings(findings):
        stats = rule_stats.setdefault(rid, {"confirmed": 0, "samples": []})
        stats["confirmed"] += 1
        if len(stats["samples"]) < _TP_SAMPLE_LIMIT:
            stats["samples"].append({
                "file": (finding_file_path(finding)
                          or pick_text(finding, ("path",))),
                "line": pick_text(finding, ("line",)),
                "snippet": pick_text(finding, ("snippet", "message"))[:100],
            })
    return rule_stats
def _tp_confidence(confirmed: int) -> float:
    return min(0.95, 0.5 + confirmed * 0.1)
def _tp_pattern_content(rid: str, stats: dict) -> str:
    _rid = md_cell(rid)
    samples_text = "\n".join(
        f"  - `{md_cell(s['file'])}:{md_cell(s['line'])}` — {md_cell(s['snippet'])}"
        for s in stats["samples"]
    )
    return f"""---
title: TP模式 - {_rid}
summary: 规则{_rid}真阳性确认{stats['confirmed']}次, 置信度高, 可提升检测优先级
{_RELATED_CONCEPT_LINE}
---

## 真阳性模式

| 指标 | 值 |
|------|-----|
| 规则ID | {_rid} |
| 确认次数 | {stats['confirmed']} |
| 置信度 | {_tp_confidence(stats["confirmed"]):.1%} |

## 样本

{samples_text}

## 调优建议

- CV阈值可降低{abs(TP_THRESHOLD_ADJUSTMENT):.2f}（更宽松），提升召回率
- 置信度乘数可设为{TP_CONFIDENCE_MULTIPLIER:.2f}~{_TP_MULTIPLIER_CEILING:.2f}
"""
def _tp_pattern_path(rid: str) -> str:
    return f"{WIKI_LESSONS_PREFIX}/TP模式-{path_segment(rid)}"
def _tp_pattern_op(rid: str, stats: dict) -> DiagnosticMemoryOperation:
    confidence = _tp_confidence(stats["confirmed"])
    return DiagnosticMemoryOperation(
        operation="add",
        path=_tp_pattern_path(rid),
        content=_tp_pattern_content(rid, stats),
        category=CATEGORY_TP_PATTERN,
        quality_score=min(10.0, 4.0 + stats["confirmed"] * 1.5),
        reason=f"规则{rid}真阳性{stats['confirmed']}次",
        rule_id=rid,
        confidence=confidence,
        tags=["true_positive", rid],
    )
def generate_tp_pattern_ops(
    cv_results: dict,
    existing_paths: set[str] | None = None,
) -> list[DiagnosticMemoryOperation]:
    ops: list[DiagnosticMemoryOperation] = []
    existing = _existing_path_set(existing_paths)
    findings = _resolve_tp_findings(cv_results)
    rule_stats = _accumulate_tp_rule_stats(findings)
    for rid, stats in rule_stats.items():
        if stats["confirmed"] < 2:
            continue
        path = _tp_pattern_path(rid)
        if path in existing:
            continue
        ops.append(_tp_pattern_op(rid, stats))
    return ops
def _best_fixer_label(fixer_stats: dict[str, dict]) -> str:
    best_fixer: str | None = None
    best_rate = 0.0
    for fixer, stats in fixer_stats.items():
        total = safe_int(stats.get("total"))
        if total <= 0:
            continue
        rate = safe_int(stats.get("success")) / total
        if (rate > best_rate
                or (rate == best_rate and rate > 0
                    and (best_fixer is None or fixer < best_fixer))):
            best_fixer, best_rate = fixer, rate
    if best_fixer is None or best_rate <= 0:
        return "无成功修复记录"
    return f"最佳修复器{md_cell(best_fixer)}({best_rate:.0%})"
def _fixer_performance_rows(fixer_stats: dict[str, dict]) -> str:
    return "\n".join(
        f"| {md_cell(fixer)} | {s['success']}/{s['total']} | {s['success']/s['total']:.1%} |"
        for fixer, s in fixer_stats.items()
    )
def _build_fix_result_content(rule_id: str, fixes: list[dict], success_rate: float) -> str:
    success_count = _success_count(fixes)
    attempt_count = success_count + _fail_count(fixes)
    fixer_stats = _rule_fixer_stats(fixes)
    _rid_cell = md_cell(rule_id)
    return f"""---
title: 修复经验 - {_rid_cell}
summary: 规则{_rid_cell}修复成功率{success_rate:.0%}, {attempt_count}次尝试, {_best_fixer_label(fixer_stats)}
{_RELATED_CONCEPT_LINE}
---

## 修复结果统计

| 指标 | 值 |
|------|-----|
| 规则ID | {_rid_cell} |
| 总尝试次数 | {attempt_count} |
| 成功次数 | {success_count} |
| 成功率 | {success_rate:.1%} |

## 修复器性能

| 修复器 | 成功/总 | 成功率 |
|--------|---------|--------|
{_fixer_performance_rows(fixer_stats)}

<!-- 待更新 -->
"""
def _build_fix_result_patch(fixes: list[dict], success_rate: float) -> str:
    success_count = _success_count(fixes)
    fail_count = _fail_count(fixes)
    fixer_stats = _rule_fixer_stats(fixes)
    return (f"{FIX_RESULT_UPDATE_HEADING}\n\n"
            f"更新: {success_count}成功/{fail_count}失败, 成功率{success_rate:.0%}\n\n"
            "| 修复器 | 成功/总 | 成功率 |\n"
            "|--------|---------|--------|\n"
            f"{_fixer_performance_rows(fixer_stats)}\n\n"
            "<!-- 待更新 -->")
def _fixer_perf_slot(perf_data: dict[str, dict], fixer: str) -> dict:
    slot = perf_data.get(fixer)
    if slot is None:
        slot = {
            "total": 0, "fixed": 0, "failed": 0,
            "rolled_back": 0, "skipped": 0,
            "failure_reasons": {},
            "rule_ids": set(),
        }
        perf_data[fixer] = slot
    return slot
def _fixer_outcome(item: dict, status: Any) -> str:
    if fix_succeeded(item):
        return "fixed"
    if status in ("rolled_back", "skipped"):
        return status
    if _failed_fix_verdict(item):
        return "failed"
    return ""
def _accumulate_fixer_perf(perf_data: dict[str, dict], item: Any) -> None:
    if not isinstance(item, dict):
        return
    fixer = pick_text(item, ("fixer_name", "fixer"))
    if not fixer:
        return
    outcome = _fixer_outcome(item, item.get("status", ""))
    if not outcome:
        return
    slot = _fixer_perf_slot(perf_data, fixer)
    slot["total"] += 1
    rid = normalize_rule_id(item.get("rule_id"))
    if rid:
        slot["rule_ids"].add(rid)
    slot[outcome] += 1
    if outcome == "failed":
        reason = pick_text(item, ("failure_reason", "error"), "unknown")
        reasons = slot["failure_reasons"]
        reasons[reason] = reasons.get(reason, 0) + 1
def _perf_grade(success_rate: float) -> str:
    if success_rate >= 0.8:
        return "A(优秀)"
    if success_rate >= 0.6:
        return "B(良好)"
    if success_rate >= 0.4:
        return "C(一般)"
    return "D(需改进)"
def _grade_advice(grade: str) -> str:
    if grade.startswith("A"):
        return "优先使用此修复器"
    if grade.startswith("B"):
        return "谨慎使用，建议先dry_run"
    if grade.startswith("C"):
        return "建议降级或寻找替代修复器"
    return "建议禁用或重构此修复器"
def _build_fixer_perf_snapshot_op(
    fixer: str, data: dict, date_str: str,
) -> DiagnosticMemoryOperation | None:
    total = data["total"]
    attempted = max(0, total - data["skipped"])
    if attempted < 3 and data["failed"] == 0 and data["rolled_back"] == 0:
        return None
    success_rate = data["fixed"] / attempted if attempted else 0.0
    rollback_rate = data["rolled_back"] / attempted if attempted else 0.0
    grade = _perf_grade(success_rate)
    top_failures = sorted(data["failure_reasons"].items(), key=lambda x: -x[1])[:3]
    failure_lines = [f"  - {md_cell(r)}: {c}次" for r, c in top_failures]
    path = (f"{WIKI_LESSONS_PREFIX}/修复器性能-"
            f"{path_segment(fixer)}-{path_segment(date_str)}")
    _fx = md_cell(fixer)
    content = f"""---
title: 修复器{_fx}性能快照 ({date_str})
summary: {_fx}: 成功率{success_rate:.1%}({data['fixed']}/{attempted}), 回滚率{rollback_rate:.1%}, 等级{grade}
---

## 修复器性能

| 指标 | 值 |
|------|-----|
| 总调度次数 | {total} |
| 实际尝试 | {attempted} |
| 成功(fixed) | {data['fixed']} |
| 失败(failed) | {data['failed']} |
| 回滚(rolled_back) | {data['rolled_back']} |
| 跳过(skipped) | {data['skipped']} |
| 成功率 | {success_rate:.1%} |
| 回滚率 | {rollback_rate:.1%} |
| 性能等级 | {grade} |
| 覆盖规则数 | {len(data['rule_ids'])} |

## 失败原因分布

{chr(10).join(failure_lines) if failure_lines else "无失败记录"}

## 治疗建议

{_grade_advice(grade)}
"""
    return DiagnosticMemoryOperation(
        operation="add",
        path=path,
        content=content,
        category=CATEGORY_FIXER_PERF_SYNC,
        quality_score=7.0,
        reason=f"修复器性能同步: {fixer} 成功率{success_rate:.1%} 等级{grade}",
        confidence=0.95,
        tags=["fixer_performance", fixer],
    )
def _collect_fixer_perf(treatment_results: dict) -> dict[str, dict]:
    perf_data: dict[str, dict] = {}
    for item in treatment_items(treatment_results):
        _accumulate_fixer_perf(perf_data, item)
    return perf_data
def sync_fixer_performance_to_memory(
    treatment_results: dict,
) -> list[DiagnosticMemoryOperation]:
    ops: list[DiagnosticMemoryOperation] = []
    if not treatment_results:
        return ops
    try:
        perf_data = _collect_fixer_perf(treatment_results)
        date_str = memory_date_stamp()
        for fixer, data in perf_data.items():
            op = _build_fixer_perf_snapshot_op(fixer, data, date_str)
            if op is not None:
                ops.append(op)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 修复器性能同步异常: %s", e)
    if ops:
        logger.info("[MemoryBridge] 修复器性能同步: %d条快照", len(ops))
    return ops
def _resolved_fixer_rates(
    ctx: DiagnosticMemoryContext | None,
    fixer_rates: dict[str, TreatmentMemoryEnhancement] | None,
) -> dict[str, TreatmentMemoryEnhancement]:
    return get_fixer_success_rates(ctx) if fixer_rates is None else fixer_rates
def _grouped_fix_history(historical_rates: dict) -> dict[str, list]:
    grouped: dict[str, list] = {}
    seen: dict[str, set[int]] = {}
    for raw_rule_id, fix_list in historical_rates.items():
        rule_id = normalize_rule_id(raw_rule_id)
        if not rule_id:
            if raw_rule_id:
                logger.warning(
                    "[MemoryBridge] 历史修复记录规则键非法(%s)，跳过: %r",
                    type(raw_rule_id).__name__, raw_rule_id)
            continue
        if not isinstance(fix_list, list) or not fix_list:
            continue
        target = grouped.setdefault(rule_id, [])
        rule_seen = seen.setdefault(rule_id, set())
        for record in fix_list:
            marker = id(record)
            if marker in rule_seen:
                continue
            rule_seen.add(marker)
            target.append(record)
    return grouped
def get_fixer_success_rates(
    ctx: DiagnosticMemoryContext | None,
) -> dict[str, TreatmentMemoryEnhancement]:
    enhancements: dict[str, TreatmentMemoryEnhancement] = {}
    if ctx is None:
        return enhancements
    fixer_perf_snapshot = dict_or_empty(ctx.fixer_performance)
    historical_rates = _grouped_fix_history(
        dict_or_empty(ctx.historical_fix_rates))
    for rule_id, fix_list in historical_rates.items():
        enhancement = _build_rule_enhancement(rule_id, fix_list, fixer_perf_snapshot)
        if enhancement is not None:
            enhancements[rule_id] = enhancement
    logger.info("[MemoryBridge] 修复器成功率提取: %d条规则有历史数据", len(enhancements))
    return enhancements
def _has_fix_verdict(fix_info: dict) -> bool:
    return fix_succeeded(fix_info) or _failed_fix_verdict(fix_info)
def _merge_fixer_stat(fixer_stats: dict[str, dict], fixer: Any,
                      success: int, total: int) -> None:
    if not isinstance(fixer, str) or not fixer or total <= 0:
        return
    success = max(0, min(success, total))
    stats = fixer_stats.setdefault(fixer, {"success": 0, "total": 0})
    stats["success"] += success
    stats["total"] += total
def _rule_fixer_stats(fix_list: list) -> dict[str, dict]:
    fixer_stats: dict[str, dict] = {}
    for fix_info in fix_list:
        if not isinstance(fix_info, dict):
            continue
        table = fix_info.get("fixer_stats")
        if isinstance(table, dict) and table:
            for fixer, raw in table.items():
                if not isinstance(raw, dict):
                    continue
                _merge_fixer_stat(
                    fixer_stats, fixer,
                    safe_int(raw.get("success")), safe_int(raw.get("total")))
            continue
        if not _has_fix_verdict(fix_info):
            continue
        _merge_fixer_stat(
            fixer_stats,
            pick_text(fix_info, ("fixer_name", "fixer")),
            1 if fix_succeeded(fix_info) else 0, 1)
    return fixer_stats
def _fixer_ranking_view(
    fixer_stats: dict[str, dict],
) -> tuple[list, list, int, dict[str, float]]:
    skip_list = []
    total_attempts = 0
    fixer_rates: dict[str, float] = {}
    for fixer, stats in fixer_stats.items():
        rate = stats["success"] / stats["total"]
        fixer_rates[fixer] = rate
        total_attempts += stats["total"]
        if rate < _FIXER_SKIP_RATE_THRESHOLD and stats["total"] >= 2:
            skip_list.append(fixer)
    fixer_ranking = sorted(fixer_rates.items(), key=lambda kv: (-kv[1], kv[0]))
    return fixer_ranking, skip_list, total_attempts, fixer_rates
def _merge_perf_snapshot_rate(
    best_fixer: str | None, best_rate: float, fixer_perf_snapshot: dict,
) -> float:
    if best_fixer and best_fixer in fixer_perf_snapshot:
        perf = fixer_perf_snapshot[best_fixer]
        if isinstance(perf, dict) and "success_rate" in perf:
            perf_rate = perf.get("success_rate")
            if is_finite_num(perf_rate) and 0.0 <= perf_rate <= 1.0:
                return float(perf_rate)
    return best_rate
def _pick_best_fixer(fixer_rates: dict[str, float]) -> tuple[str | None, float]:
    positive_rates = [(f, r) for f, r in fixer_rates.items() if r > 0]
    if not positive_rates:
        return None, 0.0
    return min(positive_rates, key=lambda kv: (-kv[1], kv[0]))
def _build_rule_enhancement(
    rule_id: str,
    fix_list: list,
    fixer_perf_snapshot: dict,
) -> TreatmentMemoryEnhancement | None:
    fixer_stats = _rule_fixer_stats(fix_list)
    fixer_ranking, skip_list, total_attempts, fixer_rates = (
        _fixer_ranking_view(fixer_stats))
    best_fixer, best_rate = _pick_best_fixer(fixer_rates)
    if not (best_fixer or skip_list):
        return None
    best_rate = _merge_perf_snapshot_rate(best_fixer, best_rate, fixer_perf_snapshot)
    if best_fixer in skip_list and best_rate < _FIXER_SKIP_RATE_THRESHOLD:
        best_fixer, best_rate = _pick_best_fixer({
            fixer: rate for fixer, rate in fixer_rates.items()
            if fixer not in skip_list})
    return TreatmentMemoryEnhancement(
        rule_id=rule_id,
        preferred_fixer=best_fixer,
        skip_fixers=[fixer for fixer in skip_list if fixer != best_fixer],
        success_rate=best_rate,
        total_attempts=total_attempts,
        fixer_ranking=fixer_ranking,
    )
def _fix_suggestion_for_rule(
    rid: Any, fixer_rates: dict[str, TreatmentMemoryEnhancement],
) -> dict | None:
    rid = normalize_rule_id(rid)
    if not rid:
        logger.warning(
            "[MemoryBridge] get_fix_pattern_suggestions: rule_id 非法或为空，跳过该条")
        return None
    enh = fixer_rates.get(rid)
    if not enh or not enh.preferred_fixer or enh.success_rate <= 0:
        return None
    skip_fixers = _fixer_avoid_list(enh, enh.preferred_fixer)
    return {
        "suggested_fixer": enh.preferred_fixer,
        "confidence": enh.success_rate,
        "reason": f"基于{enh.total_attempts}次历史修复记录",
        "total_attempts": enh.total_attempts,
        "skip_fixers": skip_fixers,
    }
def get_fix_pattern_suggestions(
    ctx: DiagnosticMemoryContext | None,
    rule_ids: list[str] | None = None,
    *,
    fixer_rates: dict[str, TreatmentMemoryEnhancement] | None = None,
) -> dict[str, dict]:
    rates = _resolved_fixer_rates(ctx, fixer_rates)
    suggestions: dict[str, dict] = {}
    if rule_ids is not None and not isinstance(rule_ids, list):
        if isinstance(rule_ids, Iterable) and not isinstance(
                rule_ids, (str, bytes, dict)):
            rule_ids = list(rule_ids)
        else:
            rule_ids = [rule_ids]
    target_rules = rule_ids if rule_ids is not None else list(rates.keys())
    for raw_rid in target_rules:
        rid = normalize_rule_id(raw_rid)
        if not rid:
            continue
        entry = _fix_suggestion_for_rule(rid, rates)
        if entry is not None:
            suggestions[rid] = entry
    return suggestions
def get_failed_fix_avoidance(
    ctx: DiagnosticMemoryContext | None,
    *,
    fixer_rates: dict[str, TreatmentMemoryEnhancement] | None = None,
) -> dict[str, list[str]]:
    rates = _resolved_fixer_rates(ctx, fixer_rates)
    avoidance: dict[str, list[str]] = {}
    for rid, enh in rates.items():
        if not enh.skip_fixers:
            continue
        avoid = _fixer_avoid_list(enh, enh.preferred_fixer)
        if avoid:
            avoidance[rid] = avoid
    return avoidance
def _fixer_avoid_list(
    enh: TreatmentMemoryEnhancement | None, best_fixer: str | None,
) -> list[str]:
    if not enh:
        return []
    return [fixer for fixer in enh.skip_fixers if fixer != best_fixer]
def _fixer_alternatives(
    enh: TreatmentMemoryEnhancement | None,
    best_fixer: str | None,
    avoid_list: list[str],
) -> list[str]:
    if not enh:
        return []
    return [
        name
        for name, rate in enh.fixer_ranking
        if rate > 0 and name != best_fixer and name not in avoid_list
    ][:3]
def _select_fixer_candidates(
    enh: TreatmentMemoryEnhancement | None,
) -> tuple[str | None, float, list[str], list[str]]:
    best_fixer: str | None = None
    best_rate = 0.0
    if enh and enh.preferred_fixer:
        best_fixer = enh.preferred_fixer
        best_rate = enh.success_rate
    avoid_list = _fixer_avoid_list(enh, best_fixer)
    alternatives = _fixer_alternatives(enh, best_fixer, avoid_list)
    return best_fixer, best_rate, avoid_list, alternatives
def recommend_fix_strategy(
    finding: dict,
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    if not isinstance(finding, dict):
        finding = {}
    rid = normalize_rule_id(finding.get("rule_id")) or ""
    recommendation: dict[str, Any] = {
        "rule_id": rid,
        "recommended_fixer": None,
        "estimated_success_rate": 0.0,
        "risk_level": "unknown",
        "avoid_fixers": [],
        "alternative_fixers": [],
        "strategy_reason": "",
        "confidence": 0.0,
    }
    if not ctx or not finding:
        recommendation["strategy_reason"] = "无历史数据或finding为空"
        return recommendation
    try:
        if not rid:
            recommendation["strategy_reason"] = "finding缺少rule_id"
            return recommendation
        fixer_rates = get_fixer_success_rates(ctx)
        enh = fixer_rates.get(rid)
        best_fixer, best_rate, avoid_list, alternatives = \
            _select_fixer_candidates(enh)
        recommendation.update(_strategy_fields(
            rid, best_fixer, best_rate, avoid_list, alternatives))
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 修复策略推荐异常: %s", e)
        recommendation["strategy_reason"] = (
            f"推荐链异常降级: {type(e).__name__}: {str(e)[:120]}")
    return recommendation
def _strategy_fields(
    rule_id: str,
    fixer: str | None,
    rate: float,
    avoid: list[str],
    alternatives: list[str],
) -> dict:
    if rate >= 0.8:
        risk_level = "low"
    elif rate >= 0.5:
        risk_level = "medium"
    elif rate > 0:
        risk_level = "high"
    else:
        risk_level = "unknown"
        fixer = None
        rate = 0.0
    confidence = min(1.0, rate * 0.7 + 0.3) if rate > 0 else 0.1
    return {
        "recommended_fixer": fixer,
        "estimated_success_rate": round(rate, 3),
        "risk_level": risk_level,
        "avoid_fixers": avoid,
        "alternative_fixers": alternatives,
        "strategy_reason": _build_strategy_reason(
            rule_id, fixer, rate, avoid, risk_level,
            alternatives=alternatives,
        ),
        "confidence": round(confidence, 3),
    }
def _build_strategy_reason(
    rule_id: str,
    fixer: str | None,
    rate: float,
    avoid: list[str],
    risk: str,
    alternatives: list[str],
) -> str:
    parts: list[str] = []
    if fixer:
        parts.append(f"推荐修复器{fixer}(历史成功率{rate:.0%})")
    else:
        parts.append(f"无历史成功修复记录: {rule_id}")
    if alternatives:
        parts.append(f"替代修复器: {', '.join(alternatives)}")
    if avoid:
        parts.append(f"规避修复器: {', '.join(avoid)}")
    parts.append(f"风险等级: {risk}")
    return "; ".join(parts)
def _clamp_confidence(value: float, floor: float = _CONF_FLOOR) -> float:
    try:
        numeric = float(value)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_clamp_confidence:{type(_e).__name__}')
        numeric = floor
    if not math.isfinite(numeric):
        numeric = floor
    return round(max(floor, min(_CONF_CEIL, numeric)), 6)
_AGGREGATE_TARGETS = frozenset({"FIXER_REGISTRY_OVERALL", "AUTO_SAFE_REGISTRY"})
_RULE_THRESHOLD_KEY_PREFIX = "CV-CONFIDENCE-"
_RULE_THRESHOLD_KEY_ALIASES = (_RULE_THRESHOLD_KEY_PREFIX, "CONFIDENCE_")
_LOW_FIX_THRESHOLD_STEP = 0.2
_FP_THRESHOLD_STEP = 0.1
def _fixer_pattern_content(title: str, summary: str, detail: str) -> str:
    return (f"---\ntitle: {md_cell(title)}\nsummary: {md_cell(summary)}\n"
            f"{_RELATED_CONCEPT_LINE}\n---\n\n## 新模式证据\n\n"
            f"{md_cell(detail)}\n")
def _fixer_pattern_texts(ftype: str, rid: str,
                         reason: str) -> tuple[str, str] | None:
    if ftype == "safety_mislabel":
        if rid in _AGGREGATE_TARGETS:
            return (_fixer_pattern_content(
                        "修复器新模式 - auto_safe 系统误标",
                        "auto_safe 安全验证机制存在系统性误标",
                        f"auto_safe 安全验证机制存在系统性误标(新模式): {reason}"),
                    "auto_safe 标记的修复器实际修复失败/回滚，记忆中无此模式记录")
        return (_fixer_pattern_content(
                    f"修复器新模式 - auto_safe - {rid}",
                    f"修复器{rid}标记 auto_safe 但修复失败/回滚",
                    f"修复器 {rid} 标记 auto_safe 但修复结果失败/回滚(新模式): {reason}"),
                f"修复器{rid}的安全标签与实际修复结果不符，历史无失败记录")
    if ftype == "coverage_gap":
        if rid in _AGGREGATE_TARGETS:
            return (_fixer_pattern_content(
                        "修复器新模式 - 注册表覆盖缺口",
                        "修复器注册表存在整体覆盖缺口",
                        f"修复器注册表存在整体覆盖缺口(新模式): {reason}"),
                    "修复器注册表整体覆盖不足，记忆中无此模式记录")
        return (_fixer_pattern_content(
                    f"修复器新模式 - 覆盖缺口 - {rid}",
                    f"规则{rid}缺少修复器",
                    f"规则 {rid} 缺少修复器(覆盖缺口, 新模式): {reason}"),
                f"规则{rid}有confirmed finding但无修复器，历史无相关记录")
    return None
def _fixer_pattern_known(path: str, rid: str, known_paths: set[str],
                         hfr: dict, ftype: str) -> bool:
    if path in known_paths:
        return True
    if ftype != "safety_mislabel":
        return False
    rule_key = "" if rid in _AGGREGATE_TARGETS else rid
    historical = [
        hist
        for raw_rule_id, records in hfr.items()
        if rule_key and normalize_rule_id(raw_rule_id) == rule_key
        for hist in as_list(records)
    ]
    return any(
        isinstance(hist, dict)
        and (hist.get("success") is False or fix_failed(hist)
             or hist.get("status") == "rolled_back")
        for hist in historical)
def _fixer_feedback_fields(fb: Any) -> tuple[str, str, str] | None:
    if not isinstance(fb, dict):
        return None
    rid = normalize_rule_id(fb.get("target_id"))
    ftype = fb.get("feedback_type", "")
    if not rid or not isinstance(ftype, str) or not ftype:
        return None
    return rid, ftype, fb.get("reason") or ""
def _fixer_pattern_op(rid: str, ftype: str, reason: str,
                      known_paths: set[str], hfr: dict) -> dict | None:
    path = (f"{WIKI_LESSONS_PREFIX}/修复器新模式-"
            f"{path_segment(ftype)}-{path_segment(rid)}")
    if _fixer_pattern_known(path, rid, known_paths, hfr, ftype):
        return None
    texts = _fixer_pattern_texts(ftype, rid, reason)
    if texts is None:
        return None
    content, op_reason = texts
    return {
        "operation": "add",
        "path": path,
        "content": content,
        "category": CATEGORY_FIX_RESULT,
        "quality_score": 8.0,
        "reason": op_reason,
        "rule_id": "" if rid in _AGGREGATE_TARGETS else rid,
    }
def _collect_fixer_pattern_ops(memory_ops: list[dict],
                               feedbacks: list,
                               ctx: DiagnosticMemoryContext) -> None:
    if not feedbacks:
        return
    known_paths = str_memory_paths(ctx)
    hfr = dict_or_empty(ctx.historical_fix_rates)
    for feedback in feedbacks:
        fields = _fixer_feedback_fields(feedback)
        if fields is None:
            continue
        rid, ftype, reason = fields
        op = _fixer_pattern_op(rid, ftype, reason, known_paths, hfr)
        if op is not None:
            memory_ops.append(op)
            known_paths.add(op["path"])
def _append_treatment_feedback_sections(memory_ops: list[dict],
                                        enhanced: dict,
                                        ctx: DiagnosticMemoryContext) -> None:
    feedbacks = _collect_feedbacks(enhanced)
    _collect_fixer_pattern_ops(memory_ops, feedbacks, ctx)
    if feedbacks:
        _append_exported_feedback_ops(memory_ops, feedbacks)
def enhance_treatment_feedback_with_memory(
    feedback_result: dict,
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    return _enhance_with_memory_ops(
        feedback_result, ctx, _append_treatment_feedback_sections,
        domain="治疗反馈记忆增强")
def _threshold_rule_id(rid: str) -> str:
    if not isinstance(rid, str):
        return ""
    for prefix in _RULE_THRESHOLD_KEY_ALIASES:
        if rid.startswith(prefix):
            return rid[len(prefix):].strip()
    return rid.strip()
def _rule_threshold_keys(rid: str) -> tuple[str, ...]:
    bare = _threshold_rule_id(rid)
    keys = [f"{prefix}{bare}" for prefix in _RULE_THRESHOLD_KEY_ALIASES]
    keys.append(bare)
    return tuple(dict.fromkeys(keys))
def _read_rule_threshold(thresholds: dict, rid: str) -> float:
    for key in _rule_threshold_keys(rid):
        value = safe_float(thresholds.get(key), math.nan)
        if math.isfinite(value):
            return float(value)
    return safe_float(get_rule_threshold(_threshold_rule_id(rid)), CONF_FLOOR)
def _apply_rule_threshold_delta(
    enhanced: dict,
    rid: str,
    delta: float,
    adj_type: str,
    reason: str,
    adjustments: list[dict],
) -> None:
    bare = _threshold_rule_id(rid)
    if not bare or bare in _AGGREGATE_TARGETS:
        return
    thresholds = enhanced.get("cv_confidence_thresholds")
    current = dict(thresholds) if isinstance(thresholds, dict) else {}
    threshold_keys = _rule_threshold_keys(bare)
    old_value = _read_rule_threshold(current, bare)
    new_value = round(max(CONF_FLOOR, min(CONF_CAP, old_value + delta)), 2)
    if delta == 0 or new_value == old_value:
        return
    current[threshold_keys[0]] = new_value
    for alias in threshold_keys[1:]:
        current.pop(alias, None)
    enhanced["cv_confidence_thresholds"] = current
    adjustments.append({
        "type": adj_type,
        "rule_id": bare,
        "reason": reason,
        "old_value": old_value,
        "new_value": new_value,
    })
def _apply_lower_confidence_adjustments(
    enhanced: dict,
    ctx: DiagnosticMemoryContext,
    adjustments: list[dict],
) -> None:
    hfr = _grouped_fix_history(dict_or_empty(ctx.historical_fix_rates))
    if not hfr:
        return
    for rid, rates in hfr.items():
        _lower_confidence_for_rule(rid, rates, enhanced, adjustments)
def _lower_confidence_for_rule(rid: str, rates: list, enhanced: dict,
                               adjustments: list[dict]) -> None:
    decided = [r for r in rates
               if isinstance(r, dict) and _has_fix_verdict(r)]
    total = len(decided)
    if total < 3:
        return
    success_count = sum(1 for r in decided if fix_succeeded(r))
    success_rate = success_count / total
    if success_rate >= 0.2:
        return
    _apply_rule_threshold_delta(
        enhanced, rid, _LOW_FIX_THRESHOLD_STEP, "lower_confidence",
        (f"修复成功率仅{success_rate:.0%}({success_count}/{total})，"
         "提高CV确认阈值以降低该规则诊断置信度"),
        adjustments)
def _iter_frequent_rules(patterns: Any):
    for rid, count in _pattern_rule_counts(patterns).items():
        if count >= _MIN_PATTERN_COUNT:
            yield rid, count
def _apply_fp_threshold_adjustments(
    enhanced: dict,
    ctx: DiagnosticMemoryContext,
    adjustments: list[dict],
) -> None:
    for rid, count in _iter_frequent_rules(ctx.known_fp_patterns):
        _apply_rule_threshold_delta(
            enhanced, rid, _FP_THRESHOLD_STEP, "raise_threshold",
            f"FP出现{count}次，提高CV置信度阈值", adjustments)
def _apply_tp_confidence_adjustments(
    enhanced: dict,
    ctx: DiagnosticMemoryContext,
    adjustments: list[dict],
) -> None:
    fp_rule_ids = pattern_rule_ids(ctx.known_fp_patterns)
    for rid, count in _iter_frequent_rules(ctx.known_tp_patterns):
        if rid in fp_rule_ids:
            continue
        _apply_rule_threshold_delta(
            enhanced, rid, TP_THRESHOLD_ADJUSTMENT, "raise_confidence",
            f"TP出现{count}次，降低CV阈值以提升召回", adjustments)
def enhance_diagnosis_with_feedback(
    diagnosis_config: dict,
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    if not isinstance(diagnosis_config, dict):
        diagnosis_config = {}
    if not ctx:
        return diagnosis_config
    enhanced = dict(diagnosis_config)
    adjustments: list[dict] = []
    try:
        _apply_lower_confidence_adjustments(enhanced, ctx, adjustments)
        _apply_fp_threshold_adjustments(enhanced, ctx, adjustments)
        _apply_tp_confidence_adjustments(enhanced, ctx, adjustments)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 诊断反馈增强异常: %s", e)
        return diagnosis_config
    if adjustments:
        enhanced["_feedback_adjustments"] = adjustments
    return enhanced
class _FeedbackReportLike(Protocol):
    memory_operations: list
    def to_dict(self) -> dict: ...
_MEMORY_OP_TEXT_DEFAULTS = {
    "operation": "", "path": "", "content": "", "old_text": "",
    "category": "", "reason": "", "rule_id": "",
}
def _memory_op_report_face(op) -> dict | None:
    if not isinstance(op, dict):
        logger.warning(
            "[MemoryBridge] 记忆操作非 dict(%s)，报告投影跳过",
            type(op).__name__)
        return None
    face = {key: str(op.get(key, default) or default)
            for key, default in _MEMORY_OP_TEXT_DEFAULTS.items()}
    quality = op.get("quality_score", 0.0)
    face["quality_score"] = float(quality) if is_finite_num(quality) else 0.0
    confidence = op.get("confidence", 0.0)
    face["confidence"] = (
        float(confidence) if is_finite_num(confidence) else 0.0)
    tags = op.get("tags", [])
    face["tags"] = list(tags) if isinstance(tags, (list, tuple)) else []
    return face
def _enhance_report_with_memory(report: _FeedbackReportLike,
                                memory_context: DiagnosticMemoryContext) -> dict:
    report_dict = report.to_dict()
    existing_ops = report_dict.get("memory_operations")
    if (isinstance(existing_ops, list) and existing_ops
            and not report_dict.get("_memory_operations")):
        report_dict["_memory_operations"] = existing_ops
    enhanced = enhance_treatment_feedback_with_memory(report_dict, memory_context)
    mem_ops = enhanced.get("_memory_operations", [])
    if mem_ops:
        report.memory_operations = [
            face for face in map(_memory_op_report_face, mem_ops)
            if face is not None]
        logger.info("[MemoryBridge] 记忆增强: %d条记忆操作",
                    len(report.memory_operations))
    return report_dict
def _append_new_memory_ops(report: _FeedbackReportLike, export_ops, seen: set) -> int:
    appended = 0
    for op in export_ops:
        _d = _memory_op_report_face(memory_op_to_dict(op))
        if _d is None:
            continue
        _k = memory_op_dedup_key(_d)
        if _k is not None and _k in seen:
            continue
        if _k is not None:
            seen.add(_k)
        report.memory_operations.append(_d)
        appended += 1
    return appended
def _export_feedbacks_to_memory(report: _FeedbackReportLike, report_dict: dict,
                                adjustments: dict) -> None:
    all_feedbacks = _collect_feedbacks(report_dict)
    adj = dict_or_empty(adjustments)
    method_adjustments = {
        "method_confidence_multipliers": dict_or_empty(
            adj.get(FIELD_METHOD_CONFIDENCE_MULTIPLIERS)),
        "cv_confidence_thresholds": dict_or_empty(
            adj.get(FIELD_CV_CONFIDENCE_THRESHOLDS)),
    }
    export_ops = export_feedback_to_memory_ops(
        {"feedbacks": all_feedbacks}, method_adjustments)
    if not export_ops:
        return
    seen = {k for k in map(memory_op_dedup_key, report.memory_operations)
            if k is not None}
    appended = _append_new_memory_ops(report, export_ops, seen)
    if appended:
        logger.info("[MemoryBridge] 反馈与调整导出: %d条记忆操作", appended)
def apply_memory_bridge(report: _FeedbackReportLike,
                        adjustments: dict,
                        memory_context: DiagnosticMemoryContext | None) -> None:
    if not memory_context:
        return
    try:
        report_dict = _enhance_report_with_memory(report, memory_context)
        _export_feedbacks_to_memory(report, report_dict, adjustments)
    except Exception as mem_err:  # noqa: BLE001
        logger.warning("[MemoryBridge] 记忆桥接跳过: %s", mem_err)
_EXACT_MATCH_TP: tuple[str, float, str] = ("tp_match", 0.1, "历史TP模式匹配")
_EXACT_MATCH_FP: tuple[str, float, str] = ("fp_caution", -0.1, "历史FP模式警告")
_SIMILARITY_MATCH_TP: tuple[str, float, str] = (
    "tp_similarity_match", 0.08, "TP")
_SIMILARITY_MATCH_FP: tuple[str, float, str] = (
    "fp_similarity_caution", -0.08, "FP")
def apply_cv_memory_enhancements(memory_context: DiagnosticMemoryContext | None,
                                 cv_report: dict, result: dict) -> dict:
    cv_report = dict_or_empty(cv_report)
    if not memory_context:
        return cv_report
    cv_report = _enhance_cv_report_with_memory(memory_context, cv_report, result)
    _record_cv_fp_pattern_ops(memory_context, cv_report, result)
    _record_cv_severity_calibrations(memory_context, result)
    return cv_report
def _enhance_cv_report_with_memory(memory_context: DiagnosticMemoryContext | None,
                                  cv_report: dict, result: dict) -> dict:
    try:
        enhanced = _enhance_cv_with_memory(cv_report, memory_context)
        if not isinstance(enhanced, dict):
            logger.warning("[Stage2b] CV记忆增强返回非 dict(%s)，保留原报告",
                           type(enhanced).__name__)
            return cv_report
        cv_report = enhanced
        result["report"] = cv_report
        mem_enh = cv_report.get("_memory_enhancement", {})
        if not isinstance(mem_enh, dict):
            mem_enh = {}
        if any(mem_enh.values()):
            logger.info("[Stage2b] 记忆增强CV: TP放大=%d, FP降权=%d, 关联=%d",
                       mem_enh.get("tp_amplified", 0),
                       mem_enh.get("fp_downgraded", 0),
                       mem_enh.get("correlated", 0))
    except Exception as cv_mem_err:  # noqa: BLE001
        logger.warning("[Stage2b] CV记忆增强跳过: %s", cv_mem_err)
    return cv_report
def _record_cv_fp_pattern_ops(memory_context: DiagnosticMemoryContext | None,
                              cv_report: dict, result: dict) -> None:
    try:
        fp_ops = generate_fp_pattern_ops(
            cv_report, str_memory_paths(memory_context))
        if fp_ops:
            result["_memory_fp_ops"] = [memory_op_to_dict(op) for op in fp_ops]
            logger.info("[Stage2b] FP模式记忆: %d条操作", len(fp_ops))
    except Exception as fp_mem_err:  # noqa: BLE001
        logger.warning("[Stage2b] FP模式记忆跳过: %s", fp_mem_err)
def _record_cv_severity_calibrations(memory_context: DiagnosticMemoryContext | None,
                                     result: dict) -> None:
    try:
        calibs = get_rule_severity_calibrations(memory_context)
        if calibs:
            result["_memory_severity_calibrations"] = calibs
            logger.info("[Stage2b] 规则校准: %d条", len(calibs))
    except Exception as calib_err:  # noqa: BLE001
        logger.warning("[Stage2b] 规则校准跳过: %s", calib_err)
def _report_findings(report: dict) -> list:
    findings = report.get("confirmed_findings")
    if not isinstance(findings, list):
        findings = report.get("findings")
    return findings if isinstance(findings, list) else []
def _write_report_findings(report: dict, findings: list) -> None:
    confirmed = report.get("confirmed_findings")
    fallback = report.get("findings")
    if isinstance(confirmed, list):
        report["confirmed_findings"] = findings
        if "findings" in report and (
                not isinstance(fallback, list) or fallback is confirmed):
            report["findings"] = findings
        return
    report["findings"] = findings
    if "confirmed_findings" in report:
        report["confirmed_findings"] = findings
def _map_findings(report: dict, mapper) -> tuple[int, list]:
    findings = _report_findings(report)
    mapped = 0
    new_list = []
    for f in findings:
        if isinstance(f, dict):
            replacement = mapper(f)
            if replacement is not None:
                mapped += 1
                new_list.append(replacement)
                continue
        new_list.append(f)
    return mapped, new_list
def _apply_finding_map(report: dict, mapper, *,
                       count_key: str | None = None) -> int:
    count, mapped = _map_findings(report, mapper)
    if count or count_key is None:
        _write_report_findings(report, mapped)
    if count_key is not None:
        report[count_key] = count
    return count
def _conf_value(finding: dict,
                 default: float = DEFAULT_CONFIDENCE_FALLBACK) -> float:
    raw = finding.get("confidence")
    return raw if is_finite_num(raw) else default
def _amplify_tp_findings(
    cv_report: dict,
    ctx: DiagnosticMemoryContext | None,
) -> tuple[dict, int]:
    if not ctx or not ctx.known_tp_patterns:
        return cv_report, 0
    tp_rule_ids = pattern_rule_ids(ctx.known_tp_patterns)
    if not tp_rule_ids:
        return cv_report, 0
    fp_rule_ids = pattern_rule_ids(ctx.known_fp_patterns)
    report = dict(cv_report)
    def _amplify(f: dict):
        if f.get("_tp_amplified"):
            return None
        rid = normalize_rule_id(f.get("rule_id"))
        if rid not in tp_rule_ids or rid in fp_rule_ids:
            return None
        f_copy = dict(f)
        f_copy["confidence"] = _clamp_confidence(_conf_value(f_copy) + 0.15)
        f_copy["_tp_amplified"] = True
        return f_copy
    amplified = _apply_finding_map(report, _amplify)
    return report, amplified
def _jaccard_similarity(set_a: set, set_b: set) -> float:
    union = set_a | set_b
    return len(set_a & set_b) / len(union) if union else 0.0
def _best_jaccard_match(f_text: set, patterns: list) -> tuple[dict | None, float]:
    best = None
    best_score = 0.0
    for p in patterns:
        if not isinstance(p, dict):
            continue
        p_text = memory_text_tokens(str(
            p.get("pattern") or p.get("reason") or ""))
        score = _jaccard_similarity(f_text, p_text)
        if score > best_score:
            best = p
            best_score = score
    return best, best_score
def _unmatched_findings(findings: list,
                        matched_rules: set[str]) -> list[tuple[dict, str]]:
    return [(finding, rid)
            for rid, finding in iter_rule_findings(findings)
            if rid not in matched_rules]
def _correlation_entry(rid: str, corr_type: str, pattern: str,
                       boost: float, reason: str) -> dict:
    return {
        "rule_id": rid,
        "type": corr_type,
        "historical_pattern": pattern,
        "confidence_boost": boost,
        "reason": reason,
    }
def _exact_pattern_matches(patterns: list, current_rules: set[str],
                           spec: tuple[str, float, str]) -> list[dict]:
    corr_type, boost, label = spec
    return [
        _correlation_entry(
            rid, corr_type, str(item.get("pattern") or "")[:100], boost,
            f"{label}: {str(item.get('reason') or '')[:80]}")
        for rid, item in iter_rule_findings(patterns)
        if rid in current_rules
    ]
def _similarity_entry(rid: str, match: dict, score: float,
                      spec: tuple[str, float, str]) -> dict:
    corr_type, boost, label = spec
    return _correlation_entry(
        rid,
        corr_type,
        str(match.get("pattern") or "")[:100],
        boost,
        (f"Jaccard相似度{score:.2f}匹配历史{label}模式: "
         f"{str(match.get('reason') or '')[:60]}"),
    )
def _threshold_match(text: set, patterns: list) -> tuple[dict | None, float]:
    best, score = _best_jaccard_match(text, patterns)
    if best and score >= JACCARD_THRESHOLD:
        return best, score
    return None, score
def _similarity_matches(unmatched_findings: list, tp_patterns: list,
                        fp_patterns: list) -> list[dict]:
    out: list[dict] = []
    for f, rid in unmatched_findings:
        f_text = memory_text_tokens(str(
            f.get("description") or f.get("message") or f.get("snippet") or ""))
        if not f_text:
            continue
        best_tp, tp_score = _threshold_match(f_text, tp_patterns)
        best_fp, fp_score = _threshold_match(f_text, fp_patterns)
        if best_fp and (not best_tp or fp_score >= tp_score):
            out.append(_similarity_entry(rid, best_fp, fp_score,
                                         _SIMILARITY_MATCH_FP))
        elif best_tp:
            out.append(_similarity_entry(rid, best_tp, tp_score,
                                         _SIMILARITY_MATCH_TP))
    return out
def _correlate_with_history(
    cv_report: dict,
    ctx: DiagnosticMemoryContext | None,
) -> list[dict]:
    correlations: list[dict] = []
    if not ctx or (not ctx.known_fp_patterns and not ctx.known_tp_patterns):
        return correlations
    findings = _report_findings(cv_report)
    current_rules = pattern_rule_ids(findings)
    tp_patterns = _unique_pattern_dicts(ctx.known_tp_patterns)
    fp_patterns = _unique_pattern_dicts(ctx.known_fp_patterns)
    correlations.extend(_exact_pattern_matches(
        tp_patterns, current_rules, _EXACT_MATCH_TP))
    correlations.extend(_exact_pattern_matches(
        fp_patterns, current_rules, _EXACT_MATCH_FP))
    matched_findings = pattern_rule_ids(correlations)
    correlations.extend(_similarity_matches(
        _unmatched_findings(findings, matched_findings),
        tp_patterns, fp_patterns))
    return correlations
def _apply_fp_downgrade(enhanced: dict, ctx: DiagnosticMemoryContext) -> int:
    if not ctx.known_fp_patterns:
        return 0
    fp_rule_ids = pattern_rule_ids(ctx.known_fp_patterns)
    def _downgrade(f: dict):
        if f.get("_fp_downgraded"):
            return None
        if normalize_rule_id(f.get("rule_id")) in fp_rule_ids and not f.get("_tp_amplified"):
            f_copy = dict(f)
            base = _conf_value(f_copy)
            f_copy["confidence"] = min(
                base, _clamp_confidence(base - 0.1, _DOWNGRADE_CONF_FLOOR))
            f_copy["_fp_downgraded"] = True
            return f_copy
        return None
    return _apply_finding_map(enhanced, _downgrade)
def _strongest_boosts(correlations: list) -> dict[str, float]:
    boosts: dict[str, float] = {}
    for rid, corr in iter_rule_findings(correlations):
        boost = corr.get("confidence_boost", 0.0)
        previous = boosts.get(rid)
        if (previous is None or abs(boost) > abs(previous)
                or (abs(boost) == abs(previous) and boost < previous)):
            boosts[rid] = boost
    return boosts
def _apply_correlation_boost(enhanced: dict, correlations: list) -> int:
    corr_boost_map = _strongest_boosts(correlations)
    if not corr_boost_map:
        return 0
    def _boost(f: dict):
        rid = normalize_rule_id(f.get("rule_id"))
        if rid in corr_boost_map and not f.get("_correlation_adjusted") \
                and not f.get("_fp_downgraded") and not f.get("_tp_amplified"):
            f_copy = dict(f)
            base = _conf_value(f_copy)
            boost = corr_boost_map[rid]
            adjusted = _clamp_confidence(base + boost)
            if boost < 0:
                adjusted = min(base, adjusted)
            f_copy["confidence"] = adjusted
            f_copy["_correlation_adjusted"] = True
            return f_copy
        return None
    return _apply_finding_map(
        enhanced, _boost, count_key="_correlation_boost_applied")
def _apply_severity_calibrations(enhanced: dict,
                                 ctx: DiagnosticMemoryContext) -> None:
    calibrations = get_rule_severity_calibrations(ctx)
    if not calibrations:
        return
    cal_map = {}
    for _c in calibrations:
        if not isinstance(_c, dict):
            continue
        _rid = normalize_rule_id(_c.get("rule_id"))
        _sev = _c.get("suggested_severity")
        if _rid and isinstance(_sev, str) and _sev:
            cal_map[_rid] = _sev
    if not cal_map:
        return
    def _calibrate(f: dict):
        rid = normalize_rule_id(f.get("rule_id"))
        target = cal_map.get(rid)
        if target is None:
            return None
        if "_original_severity" in f and f.get("severity") == target:
            return None
        f_copy = dict(f)
        f_copy["_original_severity"] = (
            f["_original_severity"] if "_original_severity" in f
            else f.get("severity", ""))
        f_copy["severity"] = target
        return f_copy
    _apply_finding_map(
        enhanced, _calibrate, count_key="_severity_calibrations_applied")
def _enhance_cv_with_memory(
    cv_report: dict,
    ctx: DiagnosticMemoryContext | None,
) -> dict:
    if not ctx:
        return cv_report
    enhanced = dict(cv_report)
    tp_amplified = 0
    fp_downgraded = 0
    correlated = 0
    try:
        enhanced, tp_amplified = _amplify_tp_findings(enhanced, ctx)
        fp_downgraded = _apply_fp_downgrade(enhanced, ctx)
        correlations = _correlate_with_history(enhanced, ctx)
        correlated = len(correlations)
        if correlations:
            enhanced["_memory_correlations"] = correlations
            _apply_correlation_boost(enhanced, correlations)
        _apply_severity_calibrations(enhanced, ctx)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] CV记忆增强异常: %s", e)
    enhanced["_memory_enhancement"] = {
        "tp_amplified": tp_amplified,
        "fp_downgraded": fp_downgraded,
        "correlated": correlated,
    }
    return enhanced
def _init_context_paths(ctx: PipelineContext) -> None:
    if ctx.adapter is not None:
        ctx.temp_dir = ctx.adapter.get_temp_dir()
    else:
        ctx.temp_dir = get_temp_base(ctx.skill_dir)
    ctx.report_dir = get_temp_base(ctx.skill_dir)
    ctx.intermediate_dir = diag_intermediate_dir(ctx.report_dir)
    os.makedirs(ctx.intermediate_dir, exist_ok=True)
def _merge_section(adjustments: dict, section_key: str, incoming) -> None:
    if not incoming:
        return
    target = adjustments.setdefault(section_key, {})
    for rule_id, value in incoming.items():
        target[rule_id] = value
def _feedback_context_without_tuned_patterns(
    memory_context: DiagnosticMemoryContext,
    cv_tunings: list,
) -> DiagnosticMemoryContext:
    tuned_rule_ids = {
        rid for tuning in cv_tunings
        if (rid := normalize_rule_id(getattr(tuning, "rule_id", None)))
    }
    if not tuned_rule_ids:
        return memory_context
    def _remaining(patterns) -> list:
        return [
            pattern for pattern in as_list(patterns)
            if not isinstance(pattern, dict)
            or normalize_rule_id(pattern.get("rule_id")) not in tuned_rule_ids
        ]
    return replace(
        memory_context,
        known_fp_patterns=_remaining(memory_context.known_fp_patterns),
        known_tp_patterns=_remaining(memory_context.known_tp_patterns),
    )
def _merge_feedback_adjustments(
    ctx: PipelineContext, memory_context, cv_tunings: list,
) -> None:
    try:
        memory_context = _feedback_context_without_tuned_patterns(
            memory_context, cv_tunings)
        feedback_config = enhance_diagnosis_with_feedback(
            ctx.adjustments, memory_context)
        if not feedback_config.get("_feedback_adjustments"):
            return
        logger.info("[FullPipeline] v4反馈驱动诊断调整: %d项",
                    len(feedback_config["_feedback_adjustments"]))
        fb_cv_thresh = feedback_config.get(
            FIELD_CV_CONFIDENCE_THRESHOLDS, {})
        _merge_section(ctx.adjustments, FIELD_CV_CONFIDENCE_THRESHOLDS,
                       fb_cv_thresh)
        logger.info("[FullPipeline] v4反馈调整已合并: %d项阈值",
                    len(fb_cv_thresh))
    except Exception as fb_diag_err:  # noqa: BLE001
        logger.warning("[FullPipeline] v4反馈诊断调整跳过: %s", fb_diag_err)
def _load_hallucination_constraints(ctx: PipelineContext) -> None:
    try:
        ctx.hallucination_ledger = get_constraints_for_task(
            skill_dir=ctx.skill_dir)
        if ctx.hallucination_ledger:
            logger.info("[FullPipeline] 幻觉防控约束注入: %d条约束",
                        len(ctx.hallucination_ledger))
    except Exception as _hall_cons_err:  # noqa: BLE001
        ctx.hallucination_ledger = []
        logger.warning("[FullPipeline] 幻觉防控约束加载跳过: %s", _hall_cons_err)
def build_pipeline_context(
        skill_dir: str, dry_run: bool | None = None,
        timeout: int | None = None, adapter=None, llm_call_fn=None,
        incremental: bool = False,
        memory_context: DiagnosticMemoryContext | None = None) -> PipelineContext:
    ctx = PipelineContext.from_skill_dir(skill_dir)
    if dry_run is not None:
        ctx.dry_run = dry_run
    if timeout is not None:
        ctx.timeout = timeout
    ctx.llm_call_fn = llm_call_fn
    ctx.adapter = adapter
    ctx.incremental = incremental
    _init_context_paths(ctx)
    ctx.pipeline_id = time.strftime("%Y%m%d%H%M%S") + f"-{id(ctx)}"
    ctx.adjustments = load_feedback_adjustments(ctx.skill_dir)
    ctx.memory_context = memory_context
    cv_tunings = generate_memory_cv_tunings(memory_context)
    _merge_feedback_adjustments(ctx, memory_context, cv_tunings)
    ctx.adjustments = apply_memory_cv_tunings(ctx.adjustments, cv_tunings)
    _load_hallucination_constraints(ctx)
    ctx.test_bridge = build_test_bridge(
        ctx.skill_dir, ctx.temp_dir, ctx.adapter)
    return ctx
def _drop_dirty_adjustment_fields(adj: dict, adj_path: str) -> None:
    dirty = [
        key for key in (
            FIELD_METHOD_CONFIDENCE_MULTIPLIERS,
            FIELD_CV_CONFIDENCE_THRESHOLDS,
            "fixer_safety_overrides",
        ) if key in adj and not isinstance(adj[key], dict)
    ]
    for key in dirty:
        del adj[key]
    if dirty:
        logger.warning(
            "[FullPipeline] 反馈调整字段形态非法已剔除: %s: %s",
            ", ".join(dirty), adj_path)
def load_feedback_adjustments(skill_dir: str) -> dict:
    adj_path = "approved_adjustments"
    try:
        adj = read_evolution_section(skill_dir, "approved_adjustments")
        if adj is None:
            return {}
        if not isinstance(adj, dict):
            logger.warning(
                "[FullPipeline] 反馈调整文件形态非法(%s)，忽略: %s",
                type(adj).__name__, adj_path)
            return {}
        _drop_dirty_adjustment_fields(adj, adj_path)
        logger.info(
            "[FullPipeline] 加载 AI 审核采纳的反馈调整: %d 方法乘数, %d CV阈值, %d 修复器覆盖",
            len(adj.get(FIELD_METHOD_CONFIDENCE_MULTIPLIERS, {})),
            len(adj.get(FIELD_CV_CONFIDENCE_THRESHOLDS, {})),
            len(adj.get("fixer_safety_overrides", {})))
        return adj
    except (OSError, ValueError, RecursionError) as e:
        logger.warning("[FullPipeline] 加载反馈调整失败: %s", e)
        return {}

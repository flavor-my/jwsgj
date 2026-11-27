from __future__ import annotations

import hashlib
import logging
import math
import posixpath
import re
import time
from collections import Counter
from typing import TYPE_CHECKING, Any, NamedTuple

from jwsgj.diag_types_normalize import (
    as_list,
    as_number,
    coerce_text_list,
    dict_or_empty,
    has_finding_entries,
    safe_float,
    safe_str,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    DIAGNOSE_TO_P,
    FIELD_QUALITY_REASONS,
    FMT_DATETIME,
    MEMORY_WRITE_ACTIONS,
    P_SCALE_LEVELS,
    SEVERITY_RANK,
    diag_severity_to_p,
)
from jwsgj.memory_bridge import (
    CATEGORY_DIAGNOSTIC_SUMMARY,
    JACCARD_THRESHOLD,
    MIN_QUALITY_SCORE,
    TREATMENT_ITEM_KEYS,
    WIKI_CONCEPTS_PREFIX,
    WIKI_LESSONS_PREFIX,
    WIKI_PROJECTS_PREFIX,
    DiagnosticMemoryContext,
    DiagnosticMemoryOperation,
    baseline_count,
    compute_enhancement_impact,
    compute_information_density,
    detect_diagnostic_regression,
    enhance_fupan_with_memory,
    enhance_retrospective_with_memory,
    enhance_review_with_memory,
    format_memory_trend_score,
    get_rule_severity_calibrations,
    is_valid_memory_score,
    last_summary_dict,
    materialize_existing_memories,
    md_cell,
    memory_date_stamp,
    memory_raw_text,
    memory_text_tokens,
    normalize_mem_entry,
    pick_first,
    pipeline_stage_views,
    str_memory_paths,
    total_findings_signal,
    treatment_items,
)
from jwsgj.memory_feedback_core import (
    compute_feedback_effectiveness,
    detect_oscillation_params,
    dict_records,
    enhance_diagnosis_with_feedback,
    enhance_feedback_with_memory,
    enhance_treatment_feedback_with_memory,
    generate_fix_result_ops,
    generate_fp_pattern_ops,
    generate_memory_cv_tunings,
    generate_tp_pattern_ops,
    memory_op_dedup_key,
    memory_op_to_dict,
    recommend_fix_strategy,
    str_items,
    sync_feedback_bidirectional,
    sync_fixer_performance_to_memory,
    text_items,
)
from jwsgj.memory_op_generation import (
    _existing_page_write_op,
    fm_scalar,
    generate_cross_session_lessons_ops,
    generate_diagnostic_summary_op,
    generate_fix_pattern_learning_ops,
    generate_fupan_memory_ops,
    generate_pdca_tracking_ops,
    generate_retrospective_memory_ops,
    generate_rule_evolution_ops,
)

if TYPE_CHECKING:
    from jwsgj.retrospective_audit import RetrospectiveReport
logger = logging.getLogger(__name__)
__all__ = [
    "DEFAULT_QUALITY_THRESHOLD",
    "absorb_ops",
    "apply_fupan_memory_bridge",
    "apply_fupan_memory_enhancement",
    "apply_retrospective_memory_bridge",
    "apply_review_memory_enhancements",
    "build_memory_operations",
    "enhance_pipeline_with_memory",
    "enhance_stage6d_memory",
    "evaluate_memory_quality",
    "existing_improvement_memories",
    "extend_ops_deduped",
    "frontmatter_bounds",
    "fuse_stage6d_memory_pipeline",
    "generate_cross_session_quality_ops",
    "generate_diagnostic_memory_ops",
    "generate_memory_candidates",
    "integrate_fupan_capabilities",
    "memory_operation_issue",
    "normalize_candidates",
    "normalize_report_containers",
    "pdca_check_and_record",
    "quality_gate",
    "run_fupan_pdca",
    "serialize_ops",
    "sync_stage6d_feedback",
    "validated_memory_operations",
]
logger.info("memory_bridge_ops 已加载: %d 项导出", len(__all__))
_FRONTMATTER_OPEN_RE = re.compile(r"\A---(\r?\n)")
def frontmatter_bounds(content: Any) -> tuple[str, int] | None:
    if not isinstance(content, str):
        return None
    opening = _FRONTMATTER_OPEN_RE.match(content)
    if opening is None:
        return None
    nl = opening.group(1)
    end = content.find(f"{nl}---{nl}", opening.end() - len(nl))
    if end != -1:
        return nl, end
    closing = f"{nl}---"
    if content.endswith(closing):
        return nl, len(content) - len(closing)
    return None
def memory_operation_issue(op: Any, idx: int) -> dict | None:
    if not isinstance(op, dict):
        return {"index": idx, "path": "", "reason": "非字典操作项"}
    action = op.get("action", "")
    if not isinstance(action, str) or action not in MEMORY_WRITE_ACTIONS:
        return {"index": idx, "path": op.get("path", ""),
                "reason": f"非法 action: {action!r}"}
    path = op.get("path")
    if not path or (isinstance(path, str) and not path.strip()):
        return {"index": idx, "path": "", "reason": "path 为空"}
    if not isinstance(path, str):
        return {"index": idx, "path": path, "reason": "path 非字符串"}
    content = op.get("content", "")
    if not content or (isinstance(content, str) and not content.strip()):
        return {"index": idx, "path": path, "reason": "content 为空"}
    if not isinstance(content, str):
        return {"index": idx, "path": path, "reason": "content 非字符串"}
    if action == "add" and frontmatter_bounds(content) is None:
        return {"index": idx, "path": path,
                "reason": "缺少 frontmatter 头或未闭合"}
    if action == "patch":
        old_text = op.get("old_text")
        if not isinstance(old_text, str):
            reason = ("patch 缺少 old_text" if not old_text
                      else "patch old_text 非字符串")
            return {"index": idx, "path": path, "reason": reason}
        if not old_text.strip():
            return {"index": idx, "path": path, "reason": "patch 缺少 old_text"}
    return None
def generate_diagnostic_memory_ops(
    diagnosis_results: dict,
    cv_results: dict,
    treatment_results: dict,
    review_results: dict | None = None,
    ctx: DiagnosticMemoryContext | None = None,
) -> list[DiagnosticMemoryOperation]:
    ops: list[DiagnosticMemoryOperation] = []
    existing_paths = str_memory_paths(ctx)
    fp_ops = generate_fp_pattern_ops(cv_results, existing_paths)
    ops.extend(fp_ops)
    fix_ops = generate_fix_result_ops(treatment_results, existing_paths)
    ops.extend(fix_ops)
    summary_op = generate_diagnostic_summary_op(
        diagnosis_results, cv_results, treatment_results, review_results, ctx
    )
    if summary_op:
        ops.append(summary_op)
    osc_ops = detect_oscillation_params(cv_results, ctx)
    ops.extend(osc_ops)
    filtered = [op for op in ops if op.quality_score >= MIN_QUALITY_SCORE]
    logger.info("[MemoryBridge] 记忆操作生成: 总计%d, 质量过滤后%d",
               len(ops), len(filtered))
    return filtered
def _append_quality_trend_op(ops: list[DiagnosticMemoryOperation],
                            review: dict, prev_summary: dict | None,
                            diag: dict,
                            ctx: DiagnosticMemoryContext | None) -> None:
    if not prev_summary:
        return
    raw_prev_score = pick_first(prev_summary, ("review_score",))
    raw_curr_score = pick_first(review, ("overall_score", "score"))
    if not (is_valid_memory_score(raw_prev_score)
            and is_valid_memory_score(raw_curr_score)):
        return
    prev_score = safe_float(raw_prev_score)
    curr_score = safe_float(raw_curr_score)
    delta = curr_score - prev_score
    if abs(delta) < 5:
        return
    prev_total = baseline_count(
        prev_summary, ("total_findings",), ("findings",))
    curr_total = total_findings_signal(diag)
    prev_total_cell = str(prev_total) if prev_total is not None else "N/A"
    curr_total_cell = (str(curr_total)
                       if curr_total is not None else "N/A")
    total_delta_cell = (f"{curr_total - prev_total:+d}"
                       if prev_total is not None and curr_total is not None
                       else "—")
    date_str = memory_date_stamp()
    trend_path = f"{WIKI_PROJECTS_PREFIX}/质量趋势-{date_str}"
    trend_content = f"""---
title: 质量趋势 ({date_str})
summary: 复盘评分{prev_score:.1f}→{curr_score:.1f}({delta:+.1f}), {"改善" if delta > 0 else "下降"}
---

## 质量趋势

| 指标 | 上次 | 本次 | 变化 |
|------|------|------|------|
| 复盘评分 | {prev_score:.1f} | {curr_score:.1f} | {delta:+.1f} |
| 总发现 | {prev_total_cell} | {curr_total_cell} | {total_delta_cell} |
"""
    trend_op = _existing_page_write_op(DiagnosticMemoryOperation(
        operation="add",
        path=trend_path,
        content=trend_content,
        category=CATEGORY_DIAGNOSTIC_SUMMARY,
        quality_score=8.0,
        reason=f"质量趋势: {delta:+.1f}分变化",
        confidence=0.9,
        tags=["quality_trend"],
    ), ctx)
    if trend_op is not None:
        ops.append(trend_op)
def generate_cross_session_quality_ops(
    pipeline_result: dict,
    ctx: DiagnosticMemoryContext | None,
) -> list[DiagnosticMemoryOperation]:
    ops: list[DiagnosticMemoryOperation] = []
    if not pipeline_result:
        return ops
    try:
        diag, cv, tx, review = pipeline_stage_views(pipeline_result)
        summary_op = generate_diagnostic_summary_op(diag, cv, tx, review, ctx)
        if summary_op:
            ops.append(summary_op)
        tp_ops = generate_tp_pattern_ops(cv, str_memory_paths(ctx) or None)
        ops.extend(tp_ops)
        _append_quality_trend_op(
            ops, review, last_summary_dict(ctx), diag, ctx)
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 跨会话质量操作生成异常: %s", e)
    return ops
def _as_iterable_list(value: Any) -> list:
    if value is None or isinstance(value, (str, bytes, bytearray, dict)):
        return []
    try:
        return list(value)
    except TypeError:
        logger.debug("值不可迭代，按空列表处理: %s", type(value).__name__, exc_info=True)
        return []
def _read_ops_field(container: Any, key: str, source: str) -> list:
    if not isinstance(container, dict):
        logger.warning("[fupan] %s 容器非 dict(%s)，按空清单降级",
                       source, type(container).__name__)
        return []
    value = container.get(key)
    items = _as_iterable_list(value)
    if not items and isinstance(value, (str, bytes, bytearray, dict)):
        logger.warning("[fupan] %s 的 %s 不是操作序列(%s)，按空清单降级",
                       source, key, type(value).__name__)
    return items
def _ops_field(container: dict, prefer: str = "_memory_operations") -> str:
    other = ("memory_operations" if prefer == "_memory_operations"
             else "_memory_operations")
    if prefer in container:
        return prefer
    if other in container:
        return other
    return prefer
_PREFIX_RE = re.compile(r"^(?:\[([^\]]*)\]|【([^】]*)】)\s*")
_CJK_CHUNK_RE = re.compile(r"[\u4e00-\u9fff]+")
_UNICODE_WORD_RE = re.compile(r"[^\W\d_]{3,}", re.UNICODE)
def _strip_detail_prefix(detail: str) -> str:
    text = detail.strip()
    while True:
        match = _PREFIX_RE.match(text)
        if not match:
            return text
        text = text[match.end():].strip()
def _leading_prefix_tags(text: str) -> list[str]:
    tags: list[str] = []
    rest = text.strip()
    while True:
        match = _PREFIX_RE.match(rest)
        if not match:
            return tags
        tags.append((match.group(1) or match.group(2) or "").strip().lower())
        rest = rest[match.end():].strip()
_REJECT_PAYLOAD_PATTERNS = [re.compile(r'^\{"title"\s*:')]
_REJECT_MARKER_TAGS = frozenset({"defect", "缺陷"})
def _has_reject_marker(text: str) -> bool:
    return any(tag in _REJECT_MARKER_TAGS for tag in _leading_prefix_tags(text))
_MIN_DETAIL_LEN = 15
_MAX_DETAIL_LEN = 2000
_ACTIONABLE_KEYWORDS = ["必须", "应该", "建议", "检查", "验证", "使用", "避免", "增加",
                        "确保", "禁止", "推荐", "需要", "优先", "拆分", "提取", "统一"]
_ACTIONABLE_ASCII = (
    "must", "should", "ensure", "verify", "check", "avoid", "add",
    "prefer", "split", "extract", "unify", "replace", "remove",
    "refactor", "review", "confirm", "recommend", "require", "need",
    "fix",
)
_ACTIONABLE_ASCII_ALTERNATION = "|".join(
    sorted(_ACTIONABLE_ASCII, key=len, reverse=True))
_ACTIONABLE_ASCII_RE = re.compile(
    rf"(?<![A-Za-z0-9_])(?:{_ACTIONABLE_ASCII_ALTERNATION})(?![A-Za-z0-9_])",
    re.IGNORECASE)
def _actionable_hits(detail: str) -> int:
    hits = sum(1 for kw in _ACTIONABLE_KEYWORDS if kw in detail)
    hits += len({m.group(0).lower()
                 for m in _ACTIONABLE_ASCII_RE.finditer(detail)})
    return hits
_WORD_ASCII = r"[A-Za-z0-9_]"
_SPECIFIC_MARKER_SOURCES = (
    rf"Error(?!{_WORD_ASCII})", rf"\.py(?!{_WORD_ASCII})",
    rf"(?<!{_WORD_ASCII})import(?!{_WORD_ASCII})",
    rf"(?<!{_WORD_ASCII})def(?!{_WORD_ASCII})",
    "模块", "文件", "函数", "配置", "参数",
    "路径", "编码", "权限", "超时", "依赖",
)
_SPECIFIC_MARKERS: tuple[re.Pattern[str], ...] = tuple(
    re.compile(source) for source in _SPECIFIC_MARKER_SOURCES)
def _score_completeness(detail: str) -> tuple[int, list[str]]:
    if len(detail) >= 80:
        return 3, ["detail长度充足"]
    if len(detail) >= 30:
        return 2, ["detail长度适中"]
    if len(detail) >= _MIN_DETAIL_LEN:
        return 1, ["detail长度偏短"]
    return 0, []
def _score_actionability(detail: str) -> tuple[int, list[str]]:
    action_count = _actionable_hits(detail)
    if action_count >= 3:
        return 3, [f"可操作性强({action_count}个动作词)"]
    if action_count >= 1:
        return 2, ["包含可操作建议"]
    return 0, ["缺少可操作建议"]
def _score_density(detail: str) -> tuple[int, list[str]]:
    if not detail or not detail.strip():
        return 0, []
    density = safe_float(
        compute_information_density(detail).get("density"), 0.0)
    if density >= 0.6:
        return 2, ["信息密度高"]
    if density >= 0.4:
        return 1, ["信息密度适中"]
    return 0, []
def _score_specificity(detail: str) -> tuple[int, list[str]]:
    specific_count = sum(1 for pat in _SPECIFIC_MARKERS if pat.search(detail))
    if specific_count >= 3:
        return 2, ["包含具体技术细节"]
    if specific_count >= 1:
        return 1, ["包含部分技术细节"]
    return 0, []
def evaluate_memory_quality(item: dict[str, Any]) -> tuple[float, list[str]]:
    if not isinstance(item, dict):
        return 0.0, ["硬过滤: 非 dict 条目"]
    detail = _judgement_text(item)
    score = 0.0
    reasons: list[str] = []
    for scorer in (_score_completeness, _score_actionability,
                   _score_density, _score_specificity):
        score_part, reasons_part = scorer(detail)
        score += score_part
        reasons.extend(reasons_part)
    return round(score, 1), reasons
def _low_quality_reason(item: dict[str, Any]) -> str | None:
    raw_detail = _detail_text(item)
    detail = _strip_detail_prefix(raw_detail)
    if len(detail) < _MIN_DETAIL_LEN:
        return "硬过滤: 内容过短"
    if _has_reject_marker(raw_detail) or any(
            pat.search(detail) for pat in _REJECT_PAYLOAD_PATTERNS):
        return "硬过滤: 命中拒绝模式(JSON载荷/原始缺陷标记)"
    detail_head = re.split(r"详情[:：]", detail, maxsplit=1)
    if len(detail_head) > 1:
        first_line = detail_head[1].split("\n", 1)[0].strip()
        if len(first_line) < 5:
            return "硬过滤: 详情首行过短"
    if len(detail) > _MAX_DETAIL_LEN:
        return "硬过滤: 内容超长"
    return None
DEFAULT_QUALITY_THRESHOLD = MIN_QUALITY_SCORE
MAX_QUALITY_THRESHOLD = 10.0
_TYPE_AWARE_THRESHOLDS: dict[str, float] = {
    "security": 3.5,
    "bug_fix": 3.5,
    "process": DEFAULT_QUALITY_THRESHOLD,
    "style": 4.5,
}
_TYPE_AWARE_ALIASES: dict[str, tuple[str, ...]] = {
    "security": ("security", "安全"),
    "bug_fix": ("bug_fix", "bugfix", "修复", "缺陷"),
    "process": ("process", "流程"),
    "style": ("style", "风格"),
}
def _get_type_aware_threshold(
    item: dict[str, Any], default_threshold: float, *,
    explicit: bool = False,
) -> float:
    if explicit:
        return default_threshold
    category = safe_str(item.get("category") or "").lower()
    for type_key, aliases in _TYPE_AWARE_ALIASES.items():
        if any(alias in category for alias in aliases):
            return _TYPE_AWARE_THRESHOLDS[type_key]
    return default_threshold
def _jaccard_similarity(a: str, b: str) -> float:
    a_words = memory_text_tokens(a)
    b_words = memory_text_tokens(b)
    if not a_words or not b_words:
        return 0.0
    return len(a_words & b_words) / len(a_words | b_words)
_SIM_THRESHOLD = JACCARD_THRESHOLD
def _detail_text(item: dict[str, Any]) -> str:
    return safe_str(item.get("detail") or item.get("content") or "").strip()
def _judgement_text(item: dict[str, Any]) -> str:
    return _strip_detail_prefix(_detail_text(item))
def _normalized_text(text: str) -> str:
    return _strip_detail_prefix(text).strip().lower()
def _memory_texts(normalized: dict[str, Any]) -> list[str]:
    return [
        text for key in ("content", "snippet", "summary")
        if isinstance(normalized.get(key), str)
        and (text := _normalized_text(normalized[key]))
    ]
_CANDIDATE_TEXT_DEFAULTS = {"detail": "", "content": "", "category": "通用"}
def _coerce_candidate_fields(item: dict[str, Any]) -> None:
    for name, default in _CANDIDATE_TEXT_DEFAULTS.items():
        if not isinstance(item.get(name), str):
            item[name] = safe_str(item[name]) if item.get(name) else default
def _find_matching_memory_path(detail: str, existing_memories: list) -> str | None:
    detail_lower = _normalized_text(detail)
    for mem in existing_memories:
        normalized = normalize_mem_entry(mem)
        if normalized is None:
            continue
        if not any(
                _jaccard_similarity(detail_lower, existing_text) >= _SIM_THRESHOLD
                for existing_text in _memory_texts(normalized)):
            continue
        path = mem.get("path") if isinstance(mem, dict) else None
        if isinstance(path, str) and path:
            return path
    return None
def _is_duplicate(detail: str, existing_full: list) -> bool:
    detail_lower = detail.strip().lower()
    for existing_text in existing_full:
        sim = _jaccard_similarity(detail_lower, existing_text)
        if sim >= _SIM_THRESHOLD:
            return True
    return False
def _collect_existing_full_texts(existing_memories: list) -> list[str]:
    texts: list[str] = []
    for mem in existing_memories:
        normalized = normalize_mem_entry(mem)
        if normalized is None:
            continue
        texts.extend(_memory_texts(normalized))
    return texts
class _GateContext(NamedTuple):
    threshold: float
    explicit_threshold: bool
    existing_memories: list
    existing_full_texts: list
    passed: list
    rejected: list
    upgrades: list
    batch_full_texts: list
def _annotate_quality(item: dict[str, Any]) -> float:
    score, reasons = evaluate_memory_quality(item)
    item["quality_score"] = score
    item[FIELD_QUALITY_REASONS] = reasons
    return score
def _mark_batch_duplicate(item: dict[str, Any], rejected: list) -> None:
    _annotate_quality(item)
    item["quality_passed"] = False
    item[FIELD_QUALITY_REASONS].append(
        f"批内重复: 与本批次已接受候选内容重复(Jaccard>={_SIM_THRESHOLD})")
    rejected.append(item)
def _existing_content_for_path(existing_memories: list,
                               path: str) -> str:
    for mem in existing_memories:
        if not isinstance(mem, dict) or mem.get("path") != path:
            continue
        content = mem.get("content")
        if isinstance(content, str) and content.strip():
            return content
    return ""
def _route_cross_duplicate(item: dict[str, Any], detail: str,
                           ctx: _GateContext) -> None:
    score = _annotate_quality(item)
    matched_path = _find_matching_memory_path(detail, ctx.existing_memories or [])
    effective_threshold = _get_type_aware_threshold(
        item, ctx.threshold, explicit=ctx.explicit_threshold)
    if matched_path and score >= effective_threshold:
        anchor = _existing_content_for_path(
            ctx.existing_memories or [], matched_path)
        if not anchor:
            item["quality_passed"] = False
            item[FIELD_QUALITY_REASONS].append(
                "升级: 目标页缺少全文锚点，拒绝生成无法定位的patch")
            ctx.rejected.append(item)
            return
        item["quality_passed"] = True
        item["effective_threshold"] = effective_threshold
        item["upgrade_target"] = matched_path
        item["old_text"] = anchor
        item[FIELD_QUALITY_REASONS].append("升级: 与已有记忆重复但质量达标，生成patch操作")
        ctx.upgrades.append(item)
        ctx.batch_full_texts.append(detail.strip().lower())
    else:
        item["quality_passed"] = False
        item[FIELD_QUALITY_REASONS].append(
            f"去重: 与已有记忆内容重复(Jaccard>={_SIM_THRESHOLD})")
        ctx.rejected.append(item)
def _apply_soft_threshold(item: dict[str, Any], detail: str,
                          ctx: _GateContext) -> None:
    score = _annotate_quality(item)
    effective_threshold = _get_type_aware_threshold(
        item, ctx.threshold, explicit=ctx.explicit_threshold)
    if score >= effective_threshold:
        item["quality_passed"] = True
        item["effective_threshold"] = effective_threshold
        ctx.passed.append(item)
        ctx.batch_full_texts.append(detail.strip().lower())
    else:
        item["quality_passed"] = False
        ctx.rejected.append(item)
def _gate_candidate(item: Any, ctx: _GateContext) -> None:
    if not isinstance(item, dict):
        logger.warning("[fupan-质量门禁] 跳过非 dict 候选条目: %r", type(item).__name__)
        ctx.rejected.append({"quality_passed": False,
                             FIELD_QUALITY_REASONS: ["硬过滤: 非 dict 条目"],
                             "raw_item": safe_str(item)[:100]})
        return
    item = dict(item)
    _coerce_candidate_fields(item)
    hard_reason = _low_quality_reason(item)
    if hard_reason is not None:
        item["quality_score"] = 0.0
        item["quality_passed"] = False
        item[FIELD_QUALITY_REASONS] = [hard_reason]
        ctx.rejected.append(item)
        return
    detail = _judgement_text(item)
    if _is_duplicate(detail, ctx.batch_full_texts):
        _mark_batch_duplicate(item, ctx.rejected)
        return
    if _is_duplicate(detail, ctx.existing_full_texts):
        _route_cross_duplicate(item, detail, ctx)
        return
    _apply_soft_threshold(item, detail, ctx)
def _quality_threshold_state(value: Any) -> tuple[float, bool]:
    parsed = safe_float(value, None)
    if (parsed is not None and math.isfinite(parsed)
            and 0 < parsed <= MAX_QUALITY_THRESHOLD):
        return float(parsed), True
    if value is not None:
        logger.warning(
            "[fupan-质量门禁] 阈值 %r 超出 (0, %.1f] 值域或格式非法，回退默认 %.1f",
            value, MAX_QUALITY_THRESHOLD, DEFAULT_QUALITY_THRESHOLD)
    return DEFAULT_QUALITY_THRESHOLD, False
def quality_gate(
    candidates: list[dict[str, Any]],
    threshold: float | None = None,
    existing_memories: list[dict[str, Any]] | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    candidates = _as_iterable_list(candidates)
    existing_memories = materialize_existing_memories(existing_memories)
    normalized_threshold, explicit_threshold = _quality_threshold_state(threshold)
    ctx = _GateContext(
        threshold=normalized_threshold,
        explicit_threshold=explicit_threshold,
        existing_memories=existing_memories,
        existing_full_texts=_collect_existing_full_texts(existing_memories),
        passed=[],
        rejected=[],
        upgrades=[],
        batch_full_texts=[],
    )
    for item in candidates:
        _gate_candidate(item, ctx)
    if ctx.rejected:
        logger.info("[fupan-质量门禁] %d→%d (拒绝%d条)",
                  len(candidates), len(ctx.passed), len(ctx.rejected))
    return ctx.passed, ctx.rejected, ctx.upgrades
class _MemoryPageSpec(NamedTuple):
    title: str
    summary: str
    detail: str
    category: str
    priority: str
    source: str
    file_path: str = ""
_RISK_CATEGORY_TOKENS = (
    "风险", "避坑", "risk", "pitfall", "hazard", "vulnerab",
)
_IMPROVEMENT_CATEGORY_TOKENS = (
    "优化", "改进", "optimiz", "improv", "enhance", "refactor",
)
def _category_hits(category: str, tokens: tuple[str, ...]) -> bool:
    lowered = safe_str(category).lower()
    return any(token in lowered for token in tokens)
def _build_memory_content(spec: _MemoryPageSpec) -> str:
    frontmatter = (f"---\ntitle: {fm_scalar(spec.title)}\n"
                   f"summary: {fm_scalar(spec.summary)}\n---\n\n")
    if _category_hits(spec.category, _RISK_CATEGORY_TOKENS):
        actionable = ("## 可操作建议\n\n1. 确认该风险是否在当前代码库中存在\n"
                      "2. 检查相关模块的异常处理和防御性编程\n"
                      "3. 添加回归测试覆盖该风险场景\n\n")
    elif _category_hits(spec.category, _IMPROVEMENT_CATEGORY_TOKENS):
        actionable = ("## 可操作建议\n\n1. 评估该改进在当前项目中的适用性\n"
                      "2. 制定具体的实施计划和验证标准\n"
                      "3. 在小范围内试点后再推广\n\n")
    else:
        actionable = ("## 可操作建议\n\n1. 验证该经验在当前上下文中的适用性\n"
                      "2. 结合具体代码场景制定实施方案\n\n")
    file_line = (f"\n- 关联文件: {md_cell(spec.file_path)}"
                 if spec.file_path else "")
    return frontmatter + (
        f"## 详情\n\n{spec.detail}\n\n{actionable}"
        "## 适用场景\n\n适用于同类项目的代码与文档审计场景，可迁移到同类项目。\n\n"
        f"## 元信息\n\n- 类别: {spec.category}\n- 优先级: {spec.priority}"
        f"\n- 来源: {spec.source}{file_line}"
        f"\n- 时间: {time.strftime(FMT_DATETIME)}\n")
def _detail_digest(detail: str) -> str:
    return hashlib.md5(
        detail.encode("utf-8"), usedforsecurity=False).hexdigest()[:6]
def _unicode_alnum(text: str) -> str:
    return "".join(char for char in text if char.isalnum())
def _make_path(category: str, detail: str) -> str:
    clean = _unicode_alnum(detail[:20])
    if not clean:
        clean = "x"
    cat = _unicode_alnum(safe_str(category))
    if not cat:
        cat = "通用"
    detail_hash = _detail_digest(detail)
    return f"{WIKI_LESSONS_PREFIX}/复盘_{cat}_{clean[:10]}_{detail_hash}"
def _rebuild_candidate_content(item: dict[str, Any]) -> None:
    detail = _detail_text(item)
    category = safe_str(item.get("category") or "通用")
    priority = safe_str(item.get("priority") or "P2-通用")
    source = safe_str(item.get("source") or "自动复盘")
    title = detail[:40] if detail else "复盘经验"
    item["path"] = _make_path(category, detail)
    item["title"] = title
    item["summary"] = detail[:100] if detail else ""
    item["category"] = category
    item["priority"] = priority
    item["source"] = source
    item["content"] = _build_memory_content(_MemoryPageSpec(
        title=title, summary=item["summary"], detail=detail,
        category=category, priority=priority, source=source,
        file_path=_item_file_path(item)))
def normalize_candidates(candidates: list[dict[str, Any]]) -> list[dict[str, Any]]:
    normalized = []
    for item in _as_iterable_list(candidates):
        if not isinstance(item, dict):
            continue
        normalized_item = dict(item)
        _coerce_candidate_fields(normalized_item)
        path = normalized_item.get("path")
        content = normalized_item.get("content")
        if isinstance(content, str) and content.strip():
            if not isinstance(path, str) or not path.strip():
                path_seed = safe_str(
                    normalized_item.get("detail")
                    or normalized_item.get("summary")
                    or normalized_item.get("title") or content)
                normalized_item["path"] = _make_path(
                    normalized_item["category"], path_seed)
            normalized.append(normalized_item)
            continue
        _rebuild_candidate_content(normalized_item)
        normalized.append(normalized_item)
    return normalized
def _pm_text_fields(pm: dict) -> tuple[Any, str, str, str, str]:
    detail = pm.get("memory_detail") or pm.get("improvement") or ""
    cat = safe_str(pm.get("memory_category") or "").strip() or "避坑"
    risk_text = safe_str(pm.get("risk") or "")
    pattern_name = safe_str(pm.get("pattern_name") or "未知")
    priority = safe_str(pm.get("priority") or "P1-核心")
    return detail, cat, risk_text, pattern_name, priority
def _candidate_entry(spec: _MemoryPageSpec) -> dict[str, Any]:
    summary = spec.summary[:100]
    return {
        "path": _make_path(spec.category, spec.detail), "title": spec.title,
        "summary": summary,
        "content": _build_memory_content(spec._replace(summary=summary)),
        "detail": spec.detail, "category": spec.category,
        "source": spec.source, "priority": spec.priority,
    }
def _is_detail_duplicate(text: str, candidates: list) -> bool:
    for candidate in candidates:
        existing = safe_str(candidate.get("detail") or "")
        if existing and (text == existing or text.startswith(existing)
                         or existing.startswith(text)):
            return True
    return False
def _candidates_from_patterns(pattern_matches: list, candidates: list) -> None:
    added = 0
    for pm in pattern_matches:
        if not isinstance(pm, dict):
            continue
        detail, cat, risk_text, pattern_name, priority = _pm_text_fields(pm)
        if not isinstance(detail, str) or len(detail) < _MIN_DETAIL_LEN:
            continue
        if _is_detail_duplicate(detail, candidates):
            continue
        candidates.append(_candidate_entry(_MemoryPageSpec(
            title=f"复盘经验: {pattern_name}", summary=risk_text,
            detail=detail, category=cat, priority=priority,
            source="自动复盘-模式匹配", file_path=_item_file_path(pm))))
        added += 1
        if added >= 3:
            break
def _candidates_from_risks(risks: list[str], candidates: list) -> None:
    seen_risks = set()
    added = 0
    for risk in risks:
        if not isinstance(risk, str) or len(risk) < 10:
            continue
        risk_key = risk
        if risk_key in seen_risks:
            continue
        if _is_detail_duplicate(risk, candidates):
            continue
        seen_risks.add(risk_key)
        candidates.append(_candidate_entry(_MemoryPageSpec(
            title=f"复盘风险: {risk[:40]}", summary=risk[:100],
            detail=risk, category="避坑",
            priority="P1-核心", source="自动复盘-风险检测")))
        added += 1
        if added >= 5:
            break
def _detected_candidate_fields(dr, candidates) -> tuple[str, str] | None:
    if not isinstance(dr, dict):
        return None
    raw_suggestion = dr.get("suggestion")
    if not isinstance(raw_suggestion, str):
        return None
    suggestion = raw_suggestion.strip()
    if len(suggestion) < _MIN_DETAIL_LEN:
        return None
    if _is_detail_duplicate(suggestion, candidates):
        return None
    category = safe_str(dr.get("category") or "").strip() or "避坑"
    return suggestion, category
def _candidates_from_detected(detected_risks: list, candidates: list) -> None:
    added = 0
    for dr in detected_risks:
        fields = _detected_candidate_fields(dr, candidates)
        if fields is None:
            continue
        suggestion, category = fields
        candidates.append(_candidate_entry(_MemoryPageSpec(
            title=f"复盘风险: {category}-{suggestion[:36]}",
            summary=suggestion[:100], detail=suggestion, category=category,
            priority="P1-核心", source="自动复盘-风险检测",
            file_path=_item_file_path(dr))))
        added += 1
        if added >= 5:
            break
def _candidates_from_improvements(improvements: list[str], candidates: list) -> None:
    added = 0
    for imp in improvements:
        if not isinstance(imp, str) or len(imp) < _MIN_DETAIL_LEN:
            continue
        if _is_detail_duplicate(imp, candidates):
            continue
        candidates.append(_candidate_entry(_MemoryPageSpec(
            title=f"复盘改进: {imp[:40]}", summary=imp[:100],
            detail=imp, category="优化",
            priority="P2-通用", source="自动复盘-改进建议")))
        added += 1
        if added >= 3:
            break
def generate_memory_candidates(
    risks: list[str], improvements: list[str],
    detected_risks: list[dict[str, Any]],
    pattern_matches: list[dict[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    _candidates_from_patterns(_as_iterable_list(pattern_matches), candidates)
    _candidates_from_risks(_as_iterable_list(risks), candidates)
    _candidates_from_detected(_as_iterable_list(detected_risks), candidates)
    _candidates_from_improvements(
        _as_iterable_list(improvements), candidates)
    return candidates
def _op_target_path(item: dict[str, Any], key: str) -> str:
    value = item.get(key)
    return value.strip() if isinstance(value, str) else ""
def _op_text_payload(value: Any) -> str:
    return value if isinstance(value, str) else ""
def _make_ops_batch_id(clean_passed: list, clean_upgrades: list) -> str:
    paths_digest = "\n".join(
        safe_str(p.get("path", "")) for p in clean_passed)
    paths_digest += "\n--upgrades--\n" + "\n".join(
        safe_str(u.get("upgrade_target", "")) for u in clean_upgrades)
    return (f"batch-{int(time.time())}-"
            f"{hashlib.md5(paths_digest.encode(), usedforsecurity=False).hexdigest()[:8]}")
def _operation_record(action: str, path: str, content: str, reason: str,
                      quality_score: Any, batch_id: str,
                      **extra: Any) -> dict[str, Any]:
    record: dict[str, Any] = {
        "action": action,
        "path": path,
        "content": content,
        "reason": reason,
        "quality_score": as_number(quality_score),
        "batch_id": batch_id,
    }
    record.update(extra)
    return record
def _append_add_operations(clean_passed: list, batch_id: str,
                           operations: list) -> None:
    skipped_invalid_path = 0
    skipped_empty_content = 0
    for item in clean_passed:
        path = _op_target_path(item, "path")
        if not path:
            skipped_invalid_path += 1
            continue
        content = _op_text_payload(item.get("content"))
        if not content.strip():
            skipped_empty_content += 1
            continue
        operations.append(_operation_record(
            "add", path, content,
            f"新增记忆: {safe_str(item.get('title') or path)}",
            item.get("quality_score"), batch_id))
    if skipped_empty_content:
        logger.warning("[fupan-memory] build_memory_operations 跳过 %d 个空或非 str content 的 passed 条目"
                     "（空内容 add 会写入空页面，非 str 内容违反操作契约）",
                     skipped_empty_content)
    if skipped_invalid_path:
        logger.warning("[fupan-memory] build_memory_operations 跳过 %d 个空或非 str path 的 passed 条目"
                     "（add 操作须有合法目标路径，与 upgrade 通道同口径）",
                     skipped_invalid_path)
def _append_patch_operations(clean_upgrades: list, batch_id: str,
                             operations: list) -> None:
    skipped_invalid_target = 0
    skipped_missing_anchor = 0
    skipped_empty_content = 0
    for item in clean_upgrades:
        target_path = _op_target_path(item, "upgrade_target")
        if not target_path:
            skipped_invalid_target += 1
            continue
        old_text = _op_text_payload(item.get("old_text"))
        if not old_text.strip():
            skipped_missing_anchor += 1
            continue
        content = _op_text_payload(item.get("content"))
        if not content.strip():
            skipped_empty_content += 1
            continue
        operations.append(_operation_record(
            "patch", target_path, content,
            (f"升级记忆: {safe_str(item.get('title') or target_path)} "
             f"(与已有记忆重复但质量达标, Jaccard>={_SIM_THRESHOLD})"),
            item.get("quality_score"), batch_id, old_text=old_text))
    if skipped_invalid_target:
        logger.warning("[fupan-memory] build_memory_operations 跳过 %d 个空或非 str upgrade_target 的 upgrade 条目"
                     "（patch 操作须有合法目标路径，与 passed 通道同口径）",
                     skipped_invalid_target)
    if skipped_missing_anchor:
        logger.warning("[fupan-memory] build_memory_operations 跳过 %d 个缺少 str old_text 锚点的 upgrade 条目"
                     "（无锚点 patch 无法定位目标页，禁止伪造占位符或隐式转型）",
                     skipped_missing_anchor)
    if skipped_empty_content:
        logger.warning("[fupan-memory] build_memory_operations 跳过 %d 个空或非 str content 的 upgrade 条目"
                     "（空内容 patch 会把目标段落清空，非 str 内容违反操作契约）",
                     skipped_empty_content)
def _clean_dict_entries(items: list, channel: str) -> list:
    clean = [p for p in items if isinstance(p, dict)]
    if len(clean) != len(items):
        logger.warning("[fupan-memory] build_memory_operations 跳过 %d 个非 dict %s 条目",
                     len(items) - len(clean), channel)
    return clean
def build_memory_operations(
    passed: list[dict[str, Any]],
    upgrades: list[dict[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    clean_passed = _clean_dict_entries(_as_iterable_list(passed), "passed")
    clean_upgrades = _clean_dict_entries(_as_iterable_list(upgrades), "upgrade")
    batch_id = _make_ops_batch_id(clean_passed, clean_upgrades)
    operations: list[dict[str, Any]] = []
    _append_add_operations(clean_passed, batch_id, operations)
    _append_patch_operations(clean_upgrades, batch_id, operations)
    return validated_memory_operations(operations, "build_memory_operations")
def _memory_op_payload(op: object) -> dict:
    payload = memory_op_to_dict(op)
    payload["action"] = payload.pop("operation", "")
    return payload
def validated_memory_operations(entries: Any, source: str) -> list[dict]:
    raw = _as_iterable_list(entries)
    if not raw and entries:
        logger.warning("[fupan] %s 记忆操作容器不可归一为序列(%s)，按空清单降级",
                       source, type(entries).__name__)
    kept: list[dict] = []
    dropped_reasons: Counter = Counter()
    for idx, entry in enumerate(raw):
        payload = (entry if (isinstance(entry, dict)
                             and entry.get("action") in MEMORY_WRITE_ACTIONS)
                   else _memory_op_payload(entry))
        issue = memory_operation_issue(payload, idx)
        if issue is None:
            kept.append(payload)
        else:
            dropped_reasons[issue["reason"]] += 1
    if dropped_reasons:
        logger.warning("[fupan] %s 丢弃 %d 条非法记忆操作（原因: %s）",
                       source, sum(dropped_reasons.values()),
                       dict(dropped_reasons))
    return kept
_REPORT_LIST_FIELDS = (
    "issues_found",
    "good_practices",
    "enhancement_actions",
    "enhancement_log",
    "memory_operations",
)
def normalize_report_containers(report: RetrospectiveReport) -> None:
    for field in _REPORT_LIST_FIELDS:
        value = getattr(report, field, None)
        if isinstance(value, list):
            continue
        coerced = _as_iterable_list(value)
        if (value is not None
                and (isinstance(value, (str, bytes, bytearray, dict))
                     or not hasattr(value, "__iter__"))):
            logger.warning("[fupan] 复盘字段 %s 不是列表(%s)，按空列表降级",
                           field, type(value).__name__)
        setattr(report, field, coerced)
def _extend_memory_operations(report: RetrospectiveReport, ops: list) -> None:
    normalize_report_containers(report)
    report.memory_operations = list(report.memory_operations) + ops
def apply_retrospective_memory_bridge(report: RetrospectiveReport,
                        memory_context: DiagnosticMemoryContext) -> None:
    normalize_report_containers(report)
    try:
        retro_dict = _report_to_memory_payload(report)
        enhanced_dict = enhance_retrospective_with_memory(retro_dict, memory_context)
        trend = enhanced_dict.get('_memory_score_trend', {})
        if trend:
            logger.info("[Retrospective] 记忆增强: 评分趋势 %s (%s→%s)",
                        trend.get('direction', '?'),
                        format_memory_trend_score(trend.get('previous')),
                        format_memory_trend_score(trend.get('current')))
        persistent = enhanced_dict.get('_memory_persistent_improvements', [])
        if persistent:
            logger.info("[Retrospective] 记忆增强: %d 条改进建议命中历史FP规则",
                        len(persistent))
        mem_ops = generate_retrospective_memory_ops(
            enhanced_dict, memory_context)
        if mem_ops:
            _extend_memory_operations(
                report, [_memory_op_payload(op) for op in mem_ops])
            logger.info("[Retrospective] 记忆操作: %d条", len(mem_ops))
    except Exception as mem_err:  # noqa: BLE001
        logger.warning("[Retrospective] 记忆桥接跳过: %s", mem_err)
_PRIORITY_VALUES = frozenset(P_SCALE_LEVELS - {"P4"})
def _memory_candidates_from(
    items: list[dict],
    *,
    default_category: str,
    path_prefix: str,
    title_prefix: str,
    priority_field: str | None,
    default_priority: str,
    source: str,
) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for item in as_list(items):
        candidate = _memory_candidate_from_item(
            item,
            default_category=default_category,
            path_prefix=path_prefix,
            title_prefix=title_prefix,
            priority_field=priority_field,
            default_priority=default_priority,
            source=source,
        )
        if candidate is not None:
            out.append(candidate)
    return out
def _coerce_candidate_str(value, default: str) -> str:
    if not isinstance(value, str):
        return default
    normalized = value.strip()
    return normalized or default
def _resolve_priority(item: dict, priority_field: str | None,
                      default_priority: str) -> str:
    raw_priority = (item.get(priority_field) if priority_field else None)
    if not isinstance(raw_priority, str) or not raw_priority:
        return default_priority
    normalized = raw_priority.strip()
    key = normalized.upper()
    if key in _PRIORITY_VALUES:
        return key
    if key in SEVERITY_RANK or key in DIAGNOSE_TO_P:
        mapped = diag_severity_to_p(normalized)
        if mapped in _PRIORITY_VALUES:
            return mapped
    return default_priority
_CANDIDATE_MIN_DETAIL_LEN = 20
def _usable_memory_detail(item: dict) -> str:
    for field in ("detail", "description"):
        value = item.get(field)
        if isinstance(value, str) and len(value.strip()) >= _CANDIDATE_MIN_DETAIL_LEN:
            return value
    return ""
_PATH_SEGMENT_UNSAFE_RE = re.compile(
    r'[\x00-\x1f\x7f-\x9f\\/:*?"<>|]+')
def _safe_path_segment(text: str) -> str:
    cleaned = _PATH_SEGMENT_UNSAFE_RE.sub('_', text).strip('._')
    return cleaned or 'entry'
def _memory_candidate_from_item(
    item,
    *,
    default_category: str,
    path_prefix: str,
    title_prefix: str,
    priority_field: str | None,
    default_priority: str,
    source: str,
) -> dict[str, Any] | None:
    if not isinstance(item, dict):
        return None
    detail = _usable_memory_detail(item)
    if not detail:
        return None
    cat = _coerce_candidate_str(item.get("category"), default_category)
    method_id = _coerce_candidate_str(item.get("method_id", ""), "")
    entry_title = f"{method_id}_{detail[:40]}" if method_id else detail[:50]
    priority = _resolve_priority(item, priority_field, default_priority)
    title = f"{title_prefix}: {entry_title[:50]}"
    summary = detail[:100]
    path = (f"{path_prefix}/{_safe_path_segment(entry_title[:30])}"
            f"_{_detail_digest(detail)}")
    content = _build_memory_content(_MemoryPageSpec(
        title=title, summary=summary, detail=detail,
        category=cat, priority=priority, source=source,
        file_path=_item_file_path(item)))
    return {
        "path": path,
        "title": title,
        "summary": summary,
        "content": content,
        "detail": detail,
        "category": cat,
        "priority": priority,
        "source": source,
        "quality_score": evaluate_memory_quality({"detail": detail, "category": cat})[0],
    }
def integrate_fupan_capabilities(
    report: RetrospectiveReport,
    diagnosis_report: dict | None = None,
    memory_context: DiagnosticMemoryContext | None = None,
) -> None:
    normalize_report_containers(report)
    pdca_result = _run_pdca_track(report, diagnosis_report, memory_context)
    _merge_pdca_act_ops(report, pdca_result)
    candidates = _build_memory_candidates(report, pdca_result)
    if not candidates:
        logger.debug("[Retrospective] 无记忆候选生成")
        return
    passed_count = _apply_quality_gate(report, candidates, memory_context)
    logger.info("[Retrospective] fupan能力集成完成: 候选%d→通过%d→记忆操作%d",
                len(candidates), passed_count, len(report.memory_operations))
def _report_to_memory_payload(report: RetrospectiveReport) -> dict:
    retro_dict = report.to_dict()
    retro_dict["overall_score"] = dict_or_empty(report.scores).get("overall")
    retro_dict["improvements"] = [
        {"priority": a.get("priority", ""),
         "description": a.get("description", ""),
         "rule_id": a.get("target_id", "")}
        for a in report.enhancement_actions if isinstance(a, dict)
    ]
    return retro_dict
def _apply_quality_gate(report: RetrospectiveReport, candidates: list,
                        memory_context: DiagnosticMemoryContext | None = None) -> int:
    normalize_report_containers(report)
    candidates = normalize_candidates(candidates)
    existing_memories = (memory_context.raw_search_results
                         if memory_context else None)
    passed, rejected, upgrades = quality_gate(
        candidates, existing_memories=existing_memories)
    report.quality_gate_result = {
        "total_candidates": len(candidates),
        "passed": len(passed),
        "rejected": len(rejected),
        "upgrades": len(upgrades),
        "rejection_rate": round(len(rejected) / max(len(candidates), 1), 2),
    }
    fupan_ops = build_memory_operations(passed, upgrades)
    _extend_memory_operations(report, fupan_ops)
    return len(passed)
def _enhancement_action_texts(report: RetrospectiveReport) -> list[str]:
    texts: list[str] = []
    for action in report.enhancement_actions:
        if not isinstance(action, dict):
            continue
        description = action.get("description")
        if isinstance(description, str) and description.strip():
            texts.append(description.strip())
    return texts
def _run_pdca_track(
        report: RetrospectiveReport,
        diagnosis_report: dict | None,
        memory_context: DiagnosticMemoryContext | None = None) -> dict[str, Any]:
    improvement_texts = _enhancement_action_texts(report)
    try:
        pdca_ctx = {
            "errors": [],
            "tool_calls": [],
            "changed_files": _collect_changed_files(diagnosis_report),
        }
        existing = (existing_improvement_memories(
            memory_context.raw_search_results) if memory_context else [])
        if existing:
            pdca_result = pdca_check_and_record(
                improvement_texts, pdca_ctx, existing_improvements=existing)
        else:
            pdca_result = pdca_check_and_record(improvement_texts, pdca_ctx)
        if not isinstance(pdca_result, dict):
            pdca_result = {}
        report.pdca_tracking = pdca_result
        return pdca_result
    except Exception as pdca_err:  # noqa: BLE001
        logger.warning("[Retrospective] PDCA 追踪失败(不阻断): %s", pdca_err)
        return {}
def _resolve_findings_index(diagnosis_report: dict) -> list:
    fi = diagnosis_report.get("findings_index")
    if not has_finding_entries(fi):
        cv = diagnosis_report.get(CAT_CROSS_VALIDATION)
        fi = cv.get("findings_index") if isinstance(cv, dict) else None
    return fi if isinstance(fi, list) else []
def _item_file_path(item: dict) -> str:
    for key in ("file_path", "file"):
        value = item.get(key)
        if isinstance(value, str) and value:
            return value
    return ""
def _collect_changed_files(diagnosis_report: dict | None) -> list[str]:
    if not isinstance(diagnosis_report, dict):
        return []
    paths = [
        _item_file_path(item)
        for item in _resolve_findings_index(diagnosis_report)
        if isinstance(item, dict)
    ]
    return list(dict.fromkeys(fp for fp in paths if fp))
def _pdca_list(pdca_result: dict[str, Any], key: str) -> list:
    value = pdca_result.get(key, []) if isinstance(pdca_result, dict) else []
    return value if isinstance(value, list) else []
def _merge_pdca_act_ops(report: RetrospectiveReport,
                        pdca_result: dict[str, Any]) -> None:
    act_ops = validated_memory_operations(
        _pdca_list(pdca_result, "act_operations"), "PDCA Act回写")
    if act_ops:
        _extend_memory_operations(report, act_ops)
        logger.info("[Retrospective] PDCA Act 回写: %d 条 patch 操作", len(act_ops))
def _build_memory_candidates(report: RetrospectiveReport,
                             pdca_result: dict[str, Any]) -> list[dict[str, Any]]:
    normalize_report_containers(report)
    candidates: list[dict[str, Any]] = []
    candidates.extend(_memory_candidates_from(
        report.issues_found,
        default_category="lessons", path_prefix=WIKI_LESSONS_PREFIX,
        title_prefix="复盘教训", priority_field="severity",
        default_priority="P2", source="retrospective_engine-issues"))
    candidates.extend(_memory_candidates_from(
        report.good_practices,
        default_category="concepts", path_prefix=WIKI_CONCEPTS_PREFIX,
        title_prefix="复盘优质", priority_field=None,
        default_priority="P3", source="retrospective_engine-practices"))
    pdca_new = _pdca_list(pdca_result, "new_candidates")
    if pdca_new:
        candidates.extend(pdca_new)
        logger.info("[Retrospective] PDCA 新增 %d 条候选", len(pdca_new))
    return candidates
def _entry_count(value: Any) -> int:
    return len(value) if isinstance(value, (dict, list)) else 0
def _operation_contract_valid(op: dict) -> bool:
    payload = op if op.get("action") else _memory_op_payload(op)
    return memory_operation_issue(payload, 0) is None
def _replace_invalid_duplicate(target: list, key: tuple[str, str],
                               new_op: dict) -> bool:
    if not _operation_contract_valid(new_op):
        return False
    invalid_index = None
    for idx, existing in enumerate(target):
        if not isinstance(existing, dict) or memory_op_dedup_key(existing) != key:
            continue
        if _operation_contract_valid(existing):
            return False
        if invalid_index is None:
            invalid_index = idx
    if invalid_index is None:
        return False
    target[invalid_index] = new_op
    return True
def extend_ops_deduped(target: list, new_ops: list) -> None:
    if not isinstance(target, list):
        logger.warning("[fupan] extend_ops_deduped target 非 list(%s)，跳过合并",
                       type(target).__name__)
        return
    new_ops = _as_iterable_list(new_ops)
    seen = {
        key for op in target
        if isinstance(op, dict)
        and (key := memory_op_dedup_key(op)) is not None
    }
    skipped_invalid = 0
    replaced_invalid = 0
    for op in new_ops:
        if not isinstance(op, dict):
            continue
        key = memory_op_dedup_key(op)
        if key is None:
            skipped_invalid += 1
            continue
        if not _operation_contract_valid(op):
            skipped_invalid += 1
            continue
        if key not in seen:
            seen.add(key)
            target.append(op)
        elif _replace_invalid_duplicate(target, key, op):
            replaced_invalid += 1
    if replaced_invalid:
        logger.info("[fupan] extend_ops_deduped 以有效操作替换 %d 条同键无效旧项",
                    replaced_invalid)
    if skipped_invalid:
        logger.warning("[fupan] extend_ops_deduped 跳过 %d 条无效载荷操作"
                       "（缺少 operation/action 或 path，或未通过内容、锚点、frontmatter 契约）",
                       skipped_invalid)
def serialize_ops(ops: list) -> list[dict]:
    return [_normalized_op(op) for op in _as_iterable_list(ops)]
def memory_ops_list(container: dict, field: str | None = None) -> list:
    field = field or _ops_field(container)
    return [op if isinstance(op, dict) else memory_op_to_dict(op)
            for op in _read_ops_field(container, field, "memory_ops_list")
            if isinstance(op, dict) or hasattr(op, "operation")]
def enhance_dict_guarded(fn, payload: dict, memory_context: Any,
                         label: str) -> dict:
    try:
        enhanced = fn(payload, memory_context)
    except Exception as enhance_err:  # noqa: BLE001
        logger.warning("%s记忆增强失败(不阻断): %s", label, enhance_err)
        return payload
    if not isinstance(enhanced, dict):
        logger.warning("%s记忆增强返回非 dict(%s)，保留原结果",
                       label, type(enhanced).__name__)
        return payload
    return enhanced
def apply_review_memory_enhancements(result: dict, memory_context) -> dict:
    result = enhance_dict_guarded(
        enhance_retrospective_with_memory, result, memory_context,
        "[Stage5] retrospective")
    result = enhance_dict_guarded(
        enhance_review_with_memory, result, memory_context, "[Stage5] review")
    try:
        retro_mem_ops = generate_retrospective_memory_ops(
            result, memory_context)
        _merged_ops = memory_ops_list(result)
        if "_memory_operations" in result and "memory_operations" in result:
            extend_ops_deduped(
                _merged_ops, memory_ops_list(result, field="memory_operations"))
        if retro_mem_ops:
            extend_ops_deduped(
                _merged_ops, [_memory_op_payload(op) for op in retro_mem_ops])
            logger.info("[Stage5] retrospective记忆操作: %d条", len(retro_mem_ops))
        if _merged_ops:
            result["_memory_operations"] = _merged_ops
    except Exception as retro_ops_err:  # noqa: BLE001
        logger.warning("[Stage5] retrospective记忆操作跳过: %s", retro_ops_err)
    return result
def append_fupan_memory_ops(result: dict, memory_context: Any) -> None:
    try:
        fupan_mem_ops = generate_fupan_memory_ops(result, memory_context)
        if not fupan_mem_ops:
            return
        field = _ops_field(result, prefer="memory_operations")
        existing_ops = memory_ops_list(result, field=field)
        extend_ops_deduped(
            existing_ops, [_memory_op_payload(op) for op in fupan_mem_ops])
        result[field] = existing_ops
        logger.info("[Stage6a] fupan记忆操作: %d条", len(fupan_mem_ops))
    except Exception as fupan_ops_err:  # noqa: BLE001
        logger.warning("[Stage6a] fupan记忆操作跳过: %s", fupan_ops_err)
def apply_fupan_memory_enhancement(result: dict, memory_context) -> dict:
    if not memory_context:
        return result
    result = enhance_dict_guarded(
        enhance_fupan_with_memory, result, memory_context, "[Stage6a] fupan")
    append_fupan_memory_ops(result, memory_context)
    return result
def apply_fupan_memory_bridge(result: dict,
                              memory_context: DiagnosticMemoryContext | None) -> dict:
    if memory_context:
        try:
            enhanced = enhance_fupan_with_memory(result, memory_context)
            if not isinstance(enhanced, dict):
                raise TypeError(
                    f"记忆增强返回值非字典: {type(enhanced).__name__}")
            result = enhanced
            fupan_ops = validated_memory_operations(
                generate_fupan_memory_ops(result, memory_context), "记忆桥接")
            if fupan_ops:
                field = _ops_field(result, prefer="memory_operations")
                existing_ops = _read_ops_field(
                    result, field, "apply_fupan_memory_bridge")
                before = len(existing_ops)
                extend_ops_deduped(existing_ops, fupan_ops)
                result[field] = existing_ops
                logger.info("[fupan] 记忆增强: %d条新增记忆操作",
                            len(existing_ops) - before)
        except Exception as mem_err:  # noqa: BLE001
            logger.warning("[fupan] 记忆桥接跳过: %s", mem_err)
    return result
def run_fupan_pdca(improvements: list[str], auto_context: dict | None,
                   existing_memories: list[dict] | None,
                   memory_candidates: list[dict]) -> tuple[dict, list, bool]:
    pdca_result: dict[str, Any] = {}
    degraded = False
    candidates = (memory_candidates if isinstance(memory_candidates, list)
                  else _as_iterable_list(memory_candidates))
    try:
        pdca_ctx = dict_or_empty(auto_context)
        if auto_context is not None and not isinstance(auto_context, dict):
            logger.warning("[fupan] auto_context 非 dict(%s)，按空上下文继续",
                           type(auto_context).__name__)
        pdca_ctx["errors"] = coerce_text_list(pdca_ctx.get("errors"))
        pdca_ctx["changed_files"] = coerce_text_list(
            pdca_ctx.get("changed_files"))
        pdca_result = pdca_check_and_record(
            improvements, pdca_ctx,
            existing_improvements=existing_improvement_memories(
                existing_memories))
        if pdca_result.get("checked") is False:
            degraded = True
            pdca_result["pdca_available"] = False
            logger.warning("[fupan] PDCA追踪降级(未执行): %s",
                           pdca_result.get("error", "checked=False"))
        pdca_new = _pdca_list(pdca_result, "new_candidates")
        if pdca_new:
            candidates.extend(pdca_new)
            logger.info("[fupan] PDCA新增 %d 条候选", len(pdca_new))
    except Exception as e:  # noqa: BLE001
        logger.warning("[fupan] PDCA追踪失败: %s", e)
        pdca_result = {"pdca_available": False, "error": safe_str(e)[:200]}
        degraded = True
    return pdca_result, candidates, degraded
def _normalized_op(op: Any) -> dict:
    return op if isinstance(op, dict) else memory_op_to_dict(op)
def absorb_ops(container: dict, ops: Any) -> int:
    if not isinstance(container, dict):
        logger.warning("[fupan] absorb_ops 容器非 dict(%s)，跳过写入",
                       type(container).__name__)
        return 0
    items = _as_iterable_list(ops)
    if not items:
        return 0
    field = _ops_field(container)
    merged = _read_ops_field(container, field, "absorb_ops")
    before = len(merged)
    normalized = []
    dropped = 0
    dropped_types: dict[str, int] = {}
    for op in items:
        payload = (_memory_op_payload(op) if field == "memory_operations"
                   else _normalized_op(op))
        if memory_op_dedup_key(payload) is None:
            dropped += 1
            type_name = type(op).__name__
            dropped_types[type_name] = dropped_types.get(type_name, 0) + 1
            continue
        normalized.append(payload)
    if dropped:
        logger.warning("[fupan] absorb_ops 丢弃 %d 条缺 operation/action 或 path 的载荷(类型分布 %s)",
                       dropped, dropped_types)
    extend_ops_deduped(merged, normalized)
    container[field] = merged
    return len(merged) - before
def _apply_cv_tuning_hints(enhanced: dict, ctx: DiagnosticMemoryContext) -> list:
    cv_tunings = generate_memory_cv_tunings(ctx)
    if cv_tunings:
        enhanced["_cv_tuning_suggestions"] = [
            {
                "rule_id": t.rule_id,
                "threshold_adjustment": t.threshold_adjustment,
                "confidence_multiplier": t.confidence_multiplier,
                "reason": t.reason,
                "evidence_count": t.evidence_count,
            }
            for t in cv_tunings
        ]
    return cv_tunings
def _oscillation_warnings(params: dict) -> list[dict]:
    warnings: list[dict] = []
    for name, info in params.items():
        if not isinstance(info, dict):
            logger.warning(
                "[MemoryBridge] 振荡参数 %r 载荷撕裂(%s)，跳过告警项",
                name, type(info).__name__)
            continue
        warnings.append({
            "param": name,
            "safe_value": info.get("safe_value"),
            "reason": info.get("reason", ""),
        })
    return warnings
def _apply_context_snapshot_hints(enhanced: dict, ctx: DiagnosticMemoryContext) -> None:
    warnings = _oscillation_warnings(dict_or_empty(ctx.oscillation_params))
    if warnings:
        enhanced["_oscillation_warnings"] = warnings
    _prev_summary = last_summary_dict(ctx)
    if _prev_summary:
        enhanced["_previous_diagnosis"] = _prev_summary
def _apply_enhancement_impact(
    enhanced: dict, all_ops: list, v4_metrics: dict, ctx: DiagnosticMemoryContext
) -> None:
    impact = compute_enhancement_impact(enhanced, ctx)
    if impact["has_baseline"]:
        v4_metrics["enhancement_impact"] = impact["impact_metrics"]
        extend_ops_deduped(all_ops, serialize_ops(impact["memory_ops"]))
def _apply_regression_detection(
    enhanced: dict,
    all_ops: list,
    v4_metrics: dict,
    diag_results: dict,
    ctx: DiagnosticMemoryContext,
) -> None:
    current_findings = as_list(diag_results.get("findings"))
    regression = detect_diagnostic_regression(current_findings, ctx)
    if regression["has_history"]:
        v4_metrics["regressions"] = len(regression["regressions"])
        enhanced["_v4_regression"] = {
            "regressions": len(regression["regressions"]),
            "details": regression["regressions"],
        }
        extend_ops_deduped(all_ops, serialize_ops(regression["memory_ops"]))
def _apply_feedback_effectiveness(
    enhanced: dict, v4_metrics: dict, review_results: dict, ctx: DiagnosticMemoryContext
) -> None:
    feedback_effect = compute_feedback_effectiveness(ctx)
    if feedback_effect["has_data"]:
        v4_metrics["feedback_effectiveness"] = feedback_effect["overall_effectiveness"]
        v4_metrics["feedback_suggestions"] = len(feedback_effect.get("suggestions", []))
        if review_results:
            review_results = dict(review_results)
            review_results["_feedback_effectiveness"] = feedback_effect
            enhanced["stage5_review"] = review_results
def _apply_diagnosis_config_feedback(
    enhanced: dict, diag_results: dict, ctx: DiagnosticMemoryContext
) -> None:
    if diag_results:
        diag_config = diag_results.get("config", {})
        if isinstance(diag_config, dict) and diag_config:
            diag_results = dict(diag_results)
            diag_results["config"] = enhance_diagnosis_with_feedback(diag_config, ctx)
            enhanced["stage1_diagnosis"] = diag_results
def _with_fix_strategy(item: Any, ctx: DiagnosticMemoryContext) -> Any:
    if not isinstance(item, dict):
        return item
    item_copy = dict(item)
    strategy = recommend_fix_strategy(item_copy, ctx)
    if strategy.get("recommended_fixer"):
        item_copy["_fix_strategy"] = strategy
    return item_copy
def _with_treatment_items(tx_results: dict, items: list) -> dict:
    updated = dict(tx_results)
    for key in TREATMENT_ITEM_KEYS:
        carrier = updated.get(key)
        if isinstance(carrier, list) and carrier:
            updated[key] = items
            break
    return updated
def _apply_fix_strategy_hints(
    enhanced: dict, tx_results: dict, ctx: DiagnosticMemoryContext
) -> None:
    if not tx_results:
        return
    tx_items = treatment_items(tx_results)
    if not tx_items:
        return
    enhanced_items = [_with_fix_strategy(item, ctx) for item in tx_items]
    enhanced["stage4_treatment_execution"] = _with_treatment_items(
        tx_results, enhanced_items)
def _enhance_stage6_feedback(
    enhanced: dict, all_ops: list, ctx: DiagnosticMemoryContext
) -> None:
    _primary_fb = dict_or_empty(enhanced.get("stage6_feedback"))
    _fallback_fb = dict_or_empty(enhanced.get("feedback"))
    feedback = _primary_fb or _fallback_fb
    if feedback:
        enhanced_feedback = enhance_treatment_feedback_with_memory(feedback, ctx)
        enhanced["stage6_feedback"] = enhanced_feedback
        if not _primary_fb and _fallback_fb:
            enhanced["feedback"] = enhanced_feedback
        extend_ops_deduped(
            all_ops, serialize_ops(_as_iterable_list(
                enhanced_feedback.get("_memory_operations"))))
def _absorb_generated_op_families(
    all_ops: list, enhanced: dict, tx_results: dict,
    ctx: DiagnosticMemoryContext,
) -> None:
    extend_ops_deduped(
        all_ops, serialize_ops(generate_rule_evolution_ops(ctx)))
    if tx_results:
        extend_ops_deduped(
            all_ops, serialize_ops(generate_fix_pattern_learning_ops(tx_results, ctx)))
        extend_ops_deduped(
            all_ops, serialize_ops(sync_fixer_performance_to_memory(tx_results)))
    extend_ops_deduped(
        all_ops, serialize_ops(generate_pdca_tracking_ops(enhanced, ctx)))
    extend_ops_deduped(
        all_ops, serialize_ops(generate_cross_session_lessons_ops(enhanced, ctx)))
def _run_memory_enhancement_chain(
    enhanced: dict, ctx: DiagnosticMemoryContext, all_ops: list, v4_metrics: dict
) -> tuple[list, list, list]:
    cv_tunings = _apply_cv_tuning_hints(enhanced, ctx)
    diag_results = dict_or_empty(enhanced.get("stage1_diagnosis"))
    cv_results = dict_or_empty(enhanced.get("stage2_cross_validation"))
    tx_results = dict_or_empty(enhanced.get("stage4_treatment_execution"))
    review_results = dict_or_empty(enhanced.get("stage5_review"))
    extend_ops_deduped(all_ops, serialize_ops(generate_diagnostic_memory_ops(
        diag_results, cv_results, tx_results, review_results, ctx
    )))
    _apply_context_snapshot_hints(enhanced, ctx)
    cross_ops = generate_cross_session_quality_ops(enhanced, ctx)
    extend_ops_deduped(all_ops, serialize_ops(cross_ops))
    calibrations = get_rule_severity_calibrations(ctx)
    if calibrations:
        enhanced["_severity_calibrations"] = calibrations
    _apply_enhancement_impact(enhanced, all_ops, v4_metrics, ctx)
    _apply_regression_detection(enhanced, all_ops, v4_metrics, diag_results, ctx)
    _absorb_generated_op_families(all_ops, enhanced, tx_results, ctx)
    _apply_feedback_effectiveness(enhanced, v4_metrics, review_results, ctx)
    _apply_diagnosis_config_feedback(enhanced, diag_results, ctx)
    _apply_fix_strategy_hints(enhanced, tx_results, ctx)
    _enhance_stage6_feedback(enhanced, all_ops, ctx)
    return cv_tunings, cross_ops, calibrations
def _bridge_status_v4(
    ctx: DiagnosticMemoryContext,
    cv_tunings: list,
    cross_ops: list,
    calibrations: list,
    all_ops: list,
    v4_metrics: dict,
) -> dict:
    return {
        "status": "enhanced",
        "version": "v4",
        "fp_patterns_loaded": _entry_count(ctx.known_fp_patterns),
        "tp_patterns_loaded": _entry_count(ctx.known_tp_patterns),
        "fix_rates_loaded": _entry_count(ctx.historical_fix_rates),
        "oscillation_params_loaded": _entry_count(ctx.oscillation_params),
        "cv_tunings_generated": len(cv_tunings),
        "cross_session_ops": len(cross_ops),
        "severity_calibrations": len(calibrations),
        "memory_ops_generated": len(all_ops),
        "v4_metrics": v4_metrics,
        "v4_functions": [
            "enhancement_impact", "regression_detection", "rule_evolution",
            "fix_pattern_learning", "fixer_perf_sync", "pdca_tracking",
            "cross_session_lessons", "feedback_effectiveness",
            "diagnosis_feedback_enhancement", "fix_strategy_recommendation",
            "treatment_feedback_enhancement",
        ],
    }
def enhance_pipeline_with_memory(
    pipeline_result: dict,
    ctx: DiagnosticMemoryContext | None = None,
) -> dict:
    if not isinstance(pipeline_result, dict):
        pipeline_result = {}
    if not ctx:
        no_ctx: dict[str, Any] = dict(pipeline_result)
        no_ctx["_memory_bridge"] = {"status": "no_context", "version": "v4"}
        return no_ctx
    enhanced: dict[str, Any] = dict(pipeline_result)
    all_ops: list[dict] = []
    v4_metrics: dict[str, Any] = {}
    try:
        cv_tunings, cross_ops, calibrations = _run_memory_enhancement_chain(
            enhanced, ctx, all_ops, v4_metrics)
        absorb_ops(enhanced, all_ops)
        enhanced["_memory_bridge"] = _bridge_status_v4(
            ctx, cv_tunings, cross_ops, calibrations, all_ops, v4_metrics)
        logger.info(
            "[MemoryBridge] 管线增强完成: %d CV调优, %d 记忆操作",
            len(cv_tunings), len(all_ops),
        )
    except Exception as e:  # noqa: BLE001
        logger.warning("[MemoryBridge] 管线增强失败(不阻断): %s", e)
        absorb_ops(enhanced, all_ops)
        enhanced["_memory_bridge"] = {
            "status": "partial_error",
            "version": "v4",
            "error": str(e)[:200],
        }
    return enhanced
def _stage1_findings(stages: dict) -> list:
    s1 = dict_or_empty(stages.get("stage1", {}))
    findings = s1.get("findings")
    if isinstance(findings, list):
        return findings
    raw = s1.get("raw_findings")
    return raw if isinstance(raw, list) else []
def _merge_memory_enhancement(result: dict, enhanced: dict) -> None:
    absorb_ops(result, enhanced.get("_memory_operations"))
    result.update({key: value for key, value in enhanced.items()
                   if key != "_memory_operations"})
def _stage1_fusion_view(stages: dict) -> dict:
    view = dict_or_empty(stages.get("stage1", {}))
    if isinstance(view.get("findings"), list):
        return {**view}
    if "findings" in view:
        return {**view, "findings": _stage1_findings(stages)}
    raw = view.get("raw_findings")
    if isinstance(raw, list) and raw:
        return {**view, "findings": raw}
    return {**view}
def _fusion_pipeline_input(stages: dict) -> dict:
    _s2b = stages.get("stage2b")
    if not isinstance(_s2b, dict) or not _s2b:
        _s2b = stages.get("stage2", {})
    return {
        "stage1_diagnosis": _stage1_fusion_view(stages),
        "stage2_cross_validation": dict_or_empty(_s2b),
        "stage4_treatment_execution": dict_or_empty(stages.get("stage4", {})),
        "stage5_review": dict_or_empty(stages.get("stage5", {})),
        "stage6_feedback": dict_or_empty(stages.get("stage6b", {})),
    }
def _copy_named_keys(
    result: dict, enhanced: dict, keys: tuple[str, ...],
) -> None:
    for key in keys:
        if key in enhanced:
            result[key] = enhanced[key]
def _absorb_v4_metrics(result: dict, bridge: dict) -> None:
    v4_metrics = bridge.get("v4_metrics", {})
    if not v4_metrics:
        return
    result["_v4_metrics"] = v4_metrics
    if "enhancement_impact" in v4_metrics:
        result["_v4_enhancement_impact"] = v4_metrics["enhancement_impact"]
_FUSION_REWRITTEN_STAGE_KEYS = ("stage1_diagnosis", "stage4_treatment_execution")
def _copy_rewritten_stage_payloads(result: dict, enhanced: dict,
                                   baseline: dict | None) -> None:
    baseline = baseline if isinstance(baseline, dict) else {}
    for key in _FUSION_REWRITTEN_STAGE_KEYS:
        value = enhanced.get(key)
        if key in enhanced and value is not baseline.get(key):
            result[key] = value
def _merge_feedback_effectiveness(result: dict, enhanced: dict) -> None:
    enhanced_review = dict_or_empty(enhanced.get("stage5_review"))
    if "_feedback_effectiveness" not in enhanced_review:
        return
    feedback_effect = enhanced_review["_feedback_effectiveness"]
    result["_feedback_effectiveness"] = feedback_effect
    review_effect = result.get("stage5_review")
    if isinstance(review_effect, dict):
        review_effect = dict(review_effect)
        review_effect["_feedback_effectiveness"] = feedback_effect
        result["stage5_review"] = review_effect
    elif "stage5_review" not in result:
        result["stage5_review"] = enhanced_review
def _fusion_merge_outputs(result: dict, enhanced: dict,
                          baseline: dict | None = None) -> dict:
    absorb_ops(result, enhanced.get("_memory_operations"))
    _copy_named_keys(result, enhanced, (
        "_cv_tuning_suggestions", "_oscillation_warnings",
        "_previous_diagnosis", "_severity_calibrations"))
    _copy_rewritten_stage_payloads(result, enhanced, baseline)
    _bridge = enhanced.get("_memory_bridge", {})
    if not isinstance(_bridge, dict):
        _bridge = {}
    result["_memory_bridge"] = _bridge
    _absorb_v4_metrics(result, _bridge)
    if "_v4_regression" in enhanced:
        result["_v4_regression"] = enhanced["_v4_regression"]
    _merge_feedback_effectiveness(result, enhanced)
    return _bridge
def fuse_stage6d_memory_pipeline(stages: dict, result: dict,
                                 memory_context) -> None:
    if not memory_context:
        return
    try:
        _pipeline_input = _fusion_pipeline_input(stages)
        _enhanced = enhance_pipeline_with_memory(_pipeline_input, memory_context)
        _bridge = _fusion_merge_outputs(result, _enhanced, _pipeline_input)
        logger.info("[Stage6d] v1/v3/v4记忆增强(融合编排): ops=%d, cv_tunings=%d, bridge_ops=%d",
                    len(memory_ops_list(result)),
                    _bridge.get("cv_tunings_generated", 0),
                    _bridge.get("memory_ops_generated", 0))
    except Exception as _mem_fuse_err:
        logger.warning("[Stage6d] v1/v3/v4记忆增强跳过: %s", _mem_fuse_err, exc_info=True)
def enhance_stage6d_memory(stages: dict, result: dict,
                           memory_context) -> None:
    if memory_context:
        try:
            _merge_memory_enhancement(
                result,
                enhance_feedback_with_memory(result, memory_context))
        except Exception as fb_mem_err:  # noqa: BLE001
            logger.warning("[Stage6d] v3反哺记忆增强跳过: %s", fb_mem_err)
    fuse_stage6d_memory_pipeline(stages, result, memory_context)
def _record_imported_feedback(result: dict, imported: Any) -> None:
    if not isinstance(imported, dict):
        return
    if (imported.get("method_confidence_multipliers")
            or imported.get("cv_confidence_thresholds")):
        result["_memory_imported_feedback"] = imported
def _merge_exported_feedback(result: dict, export_ops: list) -> None:
    added = absorb_ops(result, export_ops)
    if added:
        logger.info("[Stage6d] 反馈导出记忆: %d条(去重后新增)", added)
def sync_stage6d_feedback(stages: dict, result: dict, memory_context,
                          method_adjustments: dict) -> None:
    if not memory_context:
        return
    try:
        sync_result = sync_feedback_bidirectional(
            dict_or_empty(stages.get("stage6b", {})),
            method_adjustments or {},
            getattr(memory_context, "raw_search_results", None) or [])
        _record_imported_feedback(result, sync_result.imported_adjustments)
        _merge_exported_feedback(result, sync_result.exported_ops)
        sync_errors = as_list(getattr(sync_result, "sync_errors", None))
        if sync_errors:
            result["_feedback_sync_errors"] = sync_errors
            logger.warning("[Stage6d] 反馈双向同步 %d 项失败: %s",
                           len(sync_errors), sync_errors[:3])
    except Exception as sync_err:  # noqa: BLE001
        error = f"{type(sync_err).__name__}: {sync_err}"[:500]
        result["_feedback_sync_errors"] = [
            *as_list(result.get("_feedback_sync_errors")), error]
        logger.warning("[Stage6d] 反馈双向同步失败，阶段将停留待重试: %s", sync_err)
def _append_unique(keywords: list[str], words) -> None:
    for w in words:
        if w not in keywords:
            keywords.append(w)
def _iter_cn_windows(chunk: str):
    for size in (2, 3):
        for i in range(len(chunk) - size + 1):
            yield chunk[i:i + size]
def _is_improvement_memory(memory: Any) -> bool:
    if not isinstance(memory, dict):
        return False
    return any(_category_hits(v, _IMPROVEMENT_CATEGORY_TOKENS)
               for v in (memory.get("summary"), memory.get("path"))
               if isinstance(v, str))
def existing_improvement_memories(
        existing_memories: list[dict] | None) -> list[dict]:
    return [m for m in dict_records(existing_memories)
            if _is_improvement_memory(m)]
def _extract_keywords(text: str) -> list[str]:
    if not text:
        return []
    keywords: list[str] = []
    non_cjk = _CJK_CHUNK_RE.sub(" ", text)
    _append_unique(keywords, (token.lower() for token
                              in _UNICODE_WORD_RE.findall(non_cjk)))
    for chunk in _CJK_CHUNK_RE.findall(text):
        _append_unique(keywords, _iter_cn_windows(chunk))
    return keywords[:10]
def _basename_lower(path: Any) -> str:
    return str(path).rsplit("/", 1)[-1].rsplit("\\", 1)[-1].lower()
def _normalized_source_path(path: Any) -> str:
    if not isinstance(path, str):
        return ""
    normalized = path.strip().strip('"').replace("\\", "/").lower()
    while normalized.startswith("./"):
        normalized = normalized[2:]
    normalized = posixpath.normpath(normalized)
    return "" if normalized == "." else normalized.rstrip("/")
def _same_source_file(left: Any, right: Any) -> bool:
    left_path = _normalized_source_path(left)
    right_path = _normalized_source_path(right)
    if not left_path or not right_path:
        return False
    if left_path == right_path:
        return True
    for candidate, other in ((left_path, right_path), (right_path, left_path)):
        if "/" not in candidate and candidate == _basename_lower(other):
            return True
        is_absolute = candidate.startswith("/") or re.match(
            r"^[a-z]:/", candidate) is not None
        if is_absolute and candidate.endswith(f"/{other}"):
            return True
    return False
_MEMORY_FILE_LINE_RE = re.compile(
    r"(?m)^\s*-\s*关联文件[:：]\s*(.+?)\s*$")
_MEMORY_DETAIL_SECTION_RE = re.compile(
    r"(?ms)^ {0,3}##[ \t]+详情[ \t]*\r?\n(.*?)"
    r"(?=^ {0,3}##[ \t]+|\Z)")
_PDCA_ACT_MARKER = "[PDCA-Act]"
def _memory_source_path(memory: dict[str, Any]) -> str:
    for key in ("file_path", "file"):
        value = memory.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    match = _MEMORY_FILE_LINE_RE.search(memory_raw_text(memory))
    return match.group(1).replace("\\|", "|").strip() if match else ""
def _improvement_signal_text(memory: dict[str, Any]) -> str:
    raw = memory_raw_text(memory)
    detail = _MEMORY_DETAIL_SECTION_RE.search(raw)
    if detail and detail.group(1).strip():
        return detail.group(1).strip()
    summary = memory.get("summary")
    if isinstance(summary, str) and summary.strip():
        return summary.strip()
    return raw
def _is_exact_recur(source_path: str, current_files: list[str],
                    imp_keywords: list[str], all_context_lower: str) -> bool:
    if not source_path or not imp_keywords:
        return False
    if not any(kw.lower() in all_context_lower for kw in imp_keywords):
        return False
    return any(_same_source_file(source_path, cf) for cf in current_files)
def _match_keyword_level(imp_keywords: list[str], all_context_lower: str) -> str:
    if not imp_keywords:
        return ""
    matched_count = sum(1 for kw in imp_keywords if kw.lower() in all_context_lower)
    if matched_count >= 3:
        return "family_recur"
    if matched_count >= 1:
        return "pattern_recur"
    return ""
def _match_core_words(imp_text_lower: str, all_context_lower: str) -> bool:
    if not imp_text_lower:
        return False
    core_words = [w for w in imp_text_lower.split() if len(w) > 3]
    return any(w in all_context_lower for w in core_words[:3])
def _match_improvement(
    imp_text: str,
    imp_keywords: list[str],
    all_context: str,
    imp_path: str = "",
    current_files: list[str] | None = None,
) -> str:
    current_files = current_files or []
    all_context_lower = all_context.lower()
    imp_text_lower = imp_text.lower() if imp_text else ""
    if _is_exact_recur(imp_path, current_files, imp_keywords, all_context_lower):
        return "exact_recur"
    level = _match_keyword_level(imp_keywords, all_context_lower)
    if level:
        return level
    if _match_core_words(imp_text_lower, all_context_lower):
        return "pattern_recur"
    return "unconfirmed"
def _build_evidence_context(current_context: dict[str, Any]) -> tuple[str, list]:
    current_context = dict_or_empty(current_context)
    errors = text_items(current_context.get("errors"))
    tool_calls = dict_records(current_context.get("tool_calls"))
    changed_files = text_items(current_context.get("changed_files"))
    tool_names = (str(tc.get("name") or "") for tc in tool_calls)
    evidence = " ".join((
        " ".join(errors),
        " ".join(tool_names),
    )).lower()
    return evidence, changed_files
def _classify_improvement(
    raw_imp: Any, evidence_text: str, changed_files: list,
) -> tuple[dict[str, Any] | None, str]:
    imp = normalize_mem_entry(raw_imp)
    if imp is None:
        return None, "skip"
    if isinstance(raw_imp, dict) and not isinstance(raw_imp.get("path", ""), str):
        imp["path"] = ""
    raw_text = memory_raw_text(imp)
    if _PDCA_ACT_MARKER in raw_text:
        imp["_status"] = "applied"
        return imp, "applied"
    signal_text = _improvement_signal_text(imp)
    imp_text = signal_text.lower()
    imp_keywords = _extract_keywords(signal_text)
    source_path = _memory_source_path(imp)
    result = _match_improvement(imp_text, imp_keywords, evidence_text,
                                source_path, changed_files)
    if result != "unconfirmed":
        imp["_recur_level"] = result
        return imp, "recurring"
    if source_path and any(
            _same_source_file(source_path, cf) for cf in changed_files):
        imp["_status"] = "applied"
        return imp, "applied"
    imp["_status"] = "unverified"
    return imp, "unverified"
def _entry_path(imp: dict) -> str:
    path = imp.get("path", "")
    return path if isinstance(path, str) else ""
def _memory_patch_anchor(memory: dict[str, Any]) -> str:
    content = memory.get("content")
    summary = memory.get("summary")
    if (isinstance(content, str) and content.strip()
            and content != summary):
        return content
    snippet = memory.get("snippet")
    if isinstance(snippet, str) and snippet.strip():
        return snippet
    return ""
def _summarize_check_result(applied: list, unverified: list,
                            recurring: list) -> dict[str, Any]:
    levels = Counter(r.get("_recur_level") for r in recurring)
    return {
        "applied": len(applied), "recurring_count": len(recurring),
        "recurring_exact": levels.get("exact_recur", 0),
        "recurring_family": levels.get("family_recur", 0),
        "recurring_pattern": levels.get("pattern_recur", 0),
        "unverified_count": len(unverified),
        "details": [
            {"text": memory_raw_text(imp)[:100],
             "anchor": _memory_patch_anchor(imp), "path": _entry_path(imp),
             "status": imp.get("_recur_level") or imp.get("_status", "unverified")}
            for imp in applied + unverified + recurring],
        "recurring_issues": [memory_raw_text(imp)[:100] for imp in recurring],
    }
def _check_improvements(
    existing_improvements: list[dict[str, Any]],
    current_context: dict[str, Any],
) -> dict[str, Any]:
    if not existing_improvements:
        return _summarize_check_result([], [], [])
    evidence_text, changed_files = _build_evidence_context(current_context)
    applied = []
    unverified = []
    recurring = []
    for raw_imp in existing_improvements:
        imp, bucket = _classify_improvement(raw_imp, evidence_text, changed_files)
        if imp is None:
            continue
        if bucket == "recurring":
            recurring.append(imp)
        elif bucket == "applied":
            applied.append(imp)
        else:
            unverified.append(imp)
    return _summarize_check_result(applied, unverified, recurring)
def _collect_existing_keyword_sets(existing_improvements: list) -> list[set]:
    existing_keyword_sets = []
    for raw_imp in existing_improvements:
        normalized = normalize_mem_entry(raw_imp)
        if normalized is None:
            continue
        kws = set(_extract_keywords(_improvement_signal_text(normalized)))
        if kws:
            existing_keyword_sets.append(kws)
    return existing_keyword_sets
def _is_keyword_duplicate(imp_kws: set, existing_keyword_sets: list[set]) -> bool:
    if not imp_kws:
        return False
    for existing_kws in existing_keyword_sets:
        overlap = len(imp_kws & existing_kws)
        if overlap >= max(2, len(imp_kws) // 2):
            return True
    return False
def _record_new_improvements(
    improvements: list[str],
    existing_improvements: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    existing_keyword_sets = _collect_existing_keyword_sets(existing_improvements)
    new_items = []
    skipped_short = 0
    for imp in improvements:
        if not isinstance(imp, str):
            continue
        if len(imp.strip()) < _MIN_DETAIL_LEN:
            skipped_short += 1
            continue
        imp_kws = set(_extract_keywords(imp))
        if _is_keyword_duplicate(imp_kws, existing_keyword_sets):
            continue
        new_items.append({
            "detail": f"[PDCA-Plan] {imp[:200]}",
            "category": "改进追踪",
            "source": "自动复盘-PDCA",
            "priority": "P2-通用",
        })
        existing_keyword_sets.append(imp_kws)
    if skipped_short:
        logger.warning("[PDCA] 跳过 %d 条过短改进项（低于记忆质量硬过滤下限 %d 字符）",
                       skipped_short, _MIN_DETAIL_LEN)
    return new_items
def _applied_act_details(check_result: dict[str, Any]) -> list[dict[str, Any]]:
    raw_details = check_result.get("details")
    act_details: list[dict[str, Any]] = []
    skipped_no_path = 0
    for det in raw_details if isinstance(raw_details, list) else []:
        if not isinstance(det, dict) or det.get("status") != "applied":
            continue
        path = det.get("path")
        if not isinstance(path, str) or not path.strip():
            skipped_no_path += 1
            continue
        act_details.append({**det, "path": path.strip()})
    if skipped_no_path:
        logger.warning("[PDCA] %d 个已落实项缺少记忆页路径，无法回写（applied 计数含这些项）",
                       skipped_no_path)
    return act_details
def _act_batch_id(act_details: list[dict[str, Any]]) -> str:
    digest = str([det["path"] for det in act_details])
    return (
        f"batch-pdca-act-{int(time.time())}-"
        f"{hashlib.md5(digest.encode('utf-8'), usedforsecurity=False).hexdigest()[:8]}")
def _act_patch_operation(det: dict[str, Any], anchor: str,
                         batch_id: str) -> dict[str, Any]:
    content = (
        f"{anchor}\n\n{_PDCA_ACT_MARKER} 该改进项已于 {time.strftime(FMT_DATETIME)} "
        "验证落实（关联路径本轮已被改动且无复发信号），"
        "后续复发检测应跳过该项。"
    )
    return _operation_record(
        "patch", det.get("path", ""), content,
        "PDCA Act 回写: 标记改进项已落实", 0.0, batch_id,
        old_text=anchor)
def _build_act_operations(check_result: dict[str, Any]) -> list[dict[str, Any]]:
    if not isinstance(check_result, dict):
        return []
    act_details = _applied_act_details(check_result)
    act_batch = _act_batch_id(act_details)
    act_ops: list[dict[str, Any]] = []
    skipped_no_anchor = 0
    for det in act_details:
        anchor = det.get("anchor", det.get("text", ""))
        if not isinstance(anchor, str) or not anchor.strip():
            skipped_no_anchor += 1
            continue
        if _PDCA_ACT_MARKER in anchor:
            continue
        act_ops.append(_act_patch_operation(det, anchor, act_batch))
    if skipped_no_anchor:
        logger.warning("[PDCA] 跳过 %d 个缺少正文锚点的 Act 回写", skipped_no_anchor)
    return act_ops
def _build_repair_actions(check_result: dict[str, Any]) -> list[str]:
    recurring_issues = check_result.get("recurring_issues", [])
    if not recurring_issues:
        return []
    level_actions = (
        ("recurring_exact", "PDCA精确复发(同文件): {n}项 — 需立即修复"),
        ("recurring_family", "PDCA规则族复发(跨文件): {n}项 — 需检查规则族覆盖范围"),
        ("recurring_pattern", "PDCA模式复发(相似模式): {n}项 — 需增强检测规则"),
    )
    actions: list[str] = []
    for _key, _tpl in level_actions:
        _n = check_result.get(_key, 0)
        if isinstance(_n, int) and not isinstance(_n, bool) and _n > 0:
            actions.append(_tpl.format(n=_n))
    logger.warning("[PDCA] 复发改进项: %d 项", len(recurring_issues))
    if not actions:
        actions.append(f"PDCA复发: {len(recurring_issues)}项 — 级别计数不可用，需人工复核")
    return actions
def pdca_check_and_record(
    improvements: list[str],
    auto_context: dict[str, Any],
    existing_improvements: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    pdca_result: dict[str, Any] = {
        "checked": False,
        "applied": 0,
        "recurring": 0,
        "new_items": 0,
        "new_candidates": [],
        "act_operations": [],
        "recurring_issues": [],
        "repair_actions": [],
        "unverified": 0,
    }
    try:
        existing = dict_records(existing_improvements)
        improvement_texts = str_items(improvements)
        current_context = dict_or_empty(auto_context)
        if auto_context is not None and not isinstance(auto_context, dict):
            logger.warning("[PDCA] auto_context 非 dict(%s)，按空上下文继续",
                           type(auto_context).__name__)
        check_result = _check_improvements(existing, current_context)
        pdca_result["applied"] = check_result.get("applied", 0)
        pdca_result["recurring"] = check_result.get("recurring_count", 0)
        pdca_result["recurring_issues"] = check_result.get("recurring_issues", [])
        pdca_result["unverified"] = check_result.get("unverified_count", 0)
        new_items = _record_new_improvements(improvement_texts, existing)
        pdca_result["act_operations"] = _build_act_operations(check_result)
        pdca_result["repair_actions"] = _build_repair_actions(check_result)
        pdca_result["new_items"] = len(new_items)
        pdca_result["new_candidates"] = new_items
        pdca_result["checked"] = True
        logger.info("[PDCA] 检查完成: 已落实=%d, 复发=%d, 新记录=%d",
                  pdca_result["applied"],
                  pdca_result["recurring"],
                  pdca_result["new_items"])
    except (KeyError, TypeError, ValueError, AttributeError) as e:
        logger.warning("[PDCA] 检查跳过: %s", e)
        pdca_result["error"] = str(e)[:100]
    return pdca_result

from __future__ import annotations

import math
import os
import re
from collections.abc import Mapping
from dataclasses import dataclass, field
from datetime import datetime
from typing import Any, TypeVar

from jwsgj.build_discover_sixdim_text import (
    _CLAUSE_SPLIT_RE,
    _DEFAULT_SKILL_TYPE,
    _DEFAULT_TRIGGER_COMMAND,
    _LABEL_EXAMPLES,
    _LEADING_TRIGGER_MARK,
    _RESPONSIBILITY_ACTION_WORDS,
    _SCENARIO_INDICATORS,
    _extract_negative_rules,
    _has_section_marker,
    _is_negation_clause,
    _keyword_dedup_key,
    _normalize_inputs,
    _normalize_slot_text,
    _positive_business_text,
    _positive_prefix_before_negation,
    _trigger_command_for,
    build_keyword_matrix,
    compose_golden_description,
    expand_keyword_matrix,
    extract_core_action,
    generate_negative_rules,
    strip_injected_sections,
    validate_description_generation,
)
from jwsgj.build_script_compliance import (
    describe_script_layout,
    generate_scripts_segment,
    optimize_script_invocation,
)
from jwsgj.build_text_document import (
    locate_section,
    match_source_eol,
    normalize_str,
    normalize_str_list,
    normalize_text,
    readable_skill_name,
    truncate_description,
)
from jwsgj.build_text_frontmatter import (
    DEFAULT_SKILL_VERSION,
    extract_description_lenient,
    read_frontmatter_skill_name,
    replace_frontmatter_description,
    split_frontmatter,
)
from jwsgj.build_text_scoring import (
    DESC_MAX_LENGTH,
    DESC_MIN_LENGTH,
    DESC_OPTIMAL_MIN,
    DOMAIN_HINT_TO_TYPE_KEY,
    DOMAIN_NEGATIVES,
    LOW_TRIGGER_SCORE,
    NEGATIVE_COMMANDS,
    QUALITY_WEIGHTS,
    RE_CHINESE_CHARS,
    SIX_DIM_SPECS,
    SIX_DIM_WEIGHTS,
    SPOKEN_PATTERNS,
    TRIGGER_COMMANDS,
    TRIGGER_EXAMPLE_TEMPLATES,
    TYPE_ACTION_WORDS,
    check_atomic_responsibility,
    check_description_length,
    detect_vague_words,
    evaluate_multilingual_coverage,
    generate_trigger_examples,
    keyword_matches,
    normalize_descriptions,
    normalize_keywords,
    stem_matches,
    text_token_count,
    word_tokens,
)
from jwsgj.diag_guard_io import (
    coerce_target_file,
    guarded_open,
    normalize_path_arg,
)
from jwsgj.diag_types_normalize import (
    dict_or_empty,
    meta_num,
    yaml_safe_desc_line,
    yaml_safe_quote,
)
from jwsgj.diag_types_vocab import (
    DESC_MAX,
    FIELD_CAPABILITY_COVERAGE,
    FIELD_DISCOVERABILITY_INDEX,
    FIELD_OPTIMIZED_DESCRIPTION,
    FIELD_OPTIMIZED_KEYWORDS,
    FIELD_RECOMMENDATIONS,
    FIELD_SYNONYM_COVERAGE,
    FIELD_TRIGGER_EXAMPLES,
    MD_TABLE_SEP_3COL,
)
from jwsgj.log_config import get_module_logger, log_swallowed
from jwsgj.skill_doc_render import build_unified_skill_md_body

__all__ = [
    'SIX_DIM_ROWS',
    'SIX_DIM_SECTION_TITLE',
    'DiscoverabilityReport',
    'apply_six_dim_enhancement',
    'average_optimization_score',
    'build_discoverability_section',
    'build_script_score_section',
    'canonical_skill_category',
    'check_atomicity',
    'check_vagueness',
    'clamp_description_to_hard_limit',
    'compose_optimization_score',
    'compute_trigger_score',
    'differentiate_from_existing',
    'enhance_content_six_dim',
    'enhance_proposal_file_six_dim',
    'enhance_skill_discoverability',
    'full_discoverability_enhance',
    'generate_discoverability_report',
    'generate_golden_description',
    'generate_six_dim_description',
    'generate_skill_md_template',
    'grade_from_score',
    'identify_issues',
    'render_six_dim_section',
    'score_description_quality',
    'score_six_dimensions',
    'score_to_grade',
    'six_dim_threshold',
    'tokenize_for_overlap',
]
logger = get_module_logger(__name__, __file__)
_T = TypeVar("_T")
SIX_DIM_SECTION_TITLE = "## 六维可发现性诊断"
def _ladder_pick(value: float, ladder: tuple[tuple[float, _T], ...],
                 default: _T) -> _T:
    for threshold, result in ladder:
        if value >= threshold:
            return result
    return default
def tokenize_for_overlap(text: str) -> set[str]:
    return word_tokens(normalize_text(text))
def differentiate_from_existing(new_desc: str,
                                 existing_descs: list[str]) -> dict:
    new_desc = normalize_text(new_desc)
    source_descriptions = (
        existing_descs if isinstance(existing_descs, (list, tuple))
        else normalize_descriptions(existing_descs)
    )
    new_words = tokenize_for_overlap(strip_injected_sections(new_desc))
    overlaps = []
    for i, raw_existing in enumerate(source_descriptions):
        normalized = normalize_descriptions(raw_existing)
        if not normalized:
            continue
        existing_words = tokenize_for_overlap(
            strip_injected_sections(normalized[0]))
        intersection = new_words & existing_words
        if not intersection:
            continue
        overlap_ratio = len(intersection) / max(len(new_words), 1)
        identical_tokens = bool(new_words) and new_words == existing_words
        if identical_tokens or (len(intersection) > 5 and overlap_ratio > 0.15):
            overlaps.append({
                "index": i,
                "overlap_ratio": round(overlap_ratio, 3),
                "shared_terms": sorted(intersection)[:10],
            })
    return {
        "overlaps": overlaps,
        "total_overlaps": len(overlaps),
        "max_overlap": max((o["overlap_ratio"] for o in overlaps), default=0.0),
    }
def _score_trigger_dim(desc_lower: str) -> tuple[float, str | None]:
    if any(keyword_matches(cmd, desc_lower) for cmd in TRIGGER_COMMANDS):
        return 1.0, None
    return 0.3, "缺少强制触发词（如 MUST USE），建议添加"
def _score_scenario_dim(desc_lower: str) -> tuple[float, str | None]:
    if any(stem_matches(ind, desc_lower) for ind in _SCENARIO_INDICATORS):
        return 1.0, None
    return 0.4, "缺少场景边界描述，建议添加适用场景"
def _score_keyword_dim(top_kws: list[str], desc_lower: str) -> tuple[float, str | None]:
    if not top_kws:
        return 0.0, "未提供关键词，无法评估关键词覆盖，建议补充核心触发词"
    kw_in_desc = sum(1 for kw in top_kws if keyword_matches(kw, desc_lower))
    score = min(kw_in_desc / max(len(top_kws), 1), 1.0)
    if kw_in_desc < min(3, len(top_kws)) or score < _SUGGESTION_SCORE_THRESHOLD:
        return score, "关键词在描述中覆盖率不足，建议内嵌更多触发词"
    return score, None
def _score_negative_dim(has_negative: bool) -> tuple[float, str | None]:
    if has_negative:
        return 1.0, None
    return 0.2, "缺少反向排除规则，建议添加 NOT FOR 声明"
def _score_example_dim(has_examples: bool) -> tuple[float, str | None]:
    if has_examples:
        return 1.0, None
    return 0.3, "缺少触发示例，建议添加 1-2 个用户提问样例"
def _collect_dimension_results(
        dimensions: tuple[tuple[str, tuple[float, str | None]], ...],
) -> tuple[dict[str, float], list[str]]:
    scores = {name: result[0] for name, result in dimensions}
    details = [result[1] for _, result in dimensions if result[1]]
    return scores, details
def _score_presence_dims(desc_lower: str, top_kws: list[str],
                          has_negative: bool,
                          has_examples: bool) -> tuple[dict[str, float], list[str]]:
    return _collect_dimension_results((
        ("has_trigger_command", _score_trigger_dim(desc_lower)),
        ("has_scenario_boundary", _score_scenario_dim(desc_lower)),
        ("has_keywords_coverage", _score_keyword_dim(top_kws, desc_lower)),
        ("has_negative_rule", _score_negative_dim(has_negative)),
        ("has_trigger_example", _score_example_dim(has_examples)),
    ))
def _score_length_dim(desc: str) -> tuple[float, str | None]:
    desc_len = len(desc)
    if desc_len > DESC_MAX:
        return 0.3, f"描述超出硬上限（>{DESC_MAX}字符），必须精简"
    if desc_len > DESC_MAX_LENGTH:
        return 0.5, f"描述过长（>{DESC_MAX_LENGTH}字符），建议精简"
    if desc_len >= DESC_OPTIMAL_MIN:
        return 1.0, None
    if desc_len >= DESC_MIN_LENGTH:
        return 0.7, None
    return 0.3, f"描述过短（<{DESC_MIN_LENGTH}字符），建议扩充到{DESC_OPTIMAL_MIN}字符以上"
def _score_specificity_dim(desc: str) -> tuple[float, str | None]:
    vagueness_count = len(detect_vague_words(desc))
    score = max(0.0, 1.0 - vagueness_count * 0.3)
    if vagueness_count > 0:
        return score, f"描述中包含 {vagueness_count} 个空泛词汇，建议替换为具体描述"
    return score, None
def _score_spoken_dim(desc_lower: str) -> tuple[float, str | None]:
    hit_patterns = {
        pattern
        for patterns in SPOKEN_PATTERNS.values()
        for pattern in patterns
        if stem_matches(pattern, desc_lower)
    }
    spoken_hits = len(hit_patterns)
    score = min(spoken_hits / 5.0, 1.0)
    if spoken_hits < 2:
        return score, "口语化触发词覆盖不足，建议补充日常用语变体"
    return score, None
def _normalize_ratio(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        ratio = float(value)
    except OverflowError as e:
        logger.debug("_normalize_ratio 数值溢出: %r (%s)", value, e)
        return None
    if not math.isfinite(ratio):
        return None
    return min(1.0, max(0.0, ratio))
_NEUTRAL_DIFFERENTIATION_SCORE = 0.7
def _score_metric_dims(desc: str, desc_lower: str,
                       differentiation: float | None) -> tuple[dict[str, float], list[str]]:
    differentiation_score = (_NEUTRAL_DIFFERENTIATION_SCORE
                             if differentiation is None else differentiation)
    return _collect_dimension_results((
        ("length_optimal", _score_length_dim(desc)),
        ("specificity", _score_specificity_dim(desc)),
        ("differentiation", (differentiation_score, None)),
        ("spoken_coverage", _score_spoken_dim(desc_lower)),
    ))
def score_description_quality(desc: str, keywords: list[str],
                              has_negative: bool = False,
                              has_examples: bool = False,
                              differentiation: float | None = None) -> dict:
    desc = normalize_text(desc)
    keywords = normalize_keywords(keywords)
    differentiation = _normalize_ratio(differentiation)
    desc_lower = desc.lower()
    top_kws = keywords[:10]
    scores: dict[str, float] = {}
    details: list[str] = []
    _p_scores, _p_details = _score_presence_dims(desc_lower, top_kws, has_negative, has_examples)
    scores.update(_p_scores)
    details.extend(_p_details)
    _m_scores, _m_details = _score_metric_dims(desc, desc_lower, differentiation)
    scores.update(_m_scores)
    details.extend(_m_details)
    total = sum(scores[dim] * QUALITY_WEIGHTS.get(dim, 0.1) for dim in scores)
    total = round(total * 100, 1)
    return {
        "total": total,
        "grade": grade_from_score(total),
        "dimensions": scores,
        "details": details,
    }
def _unique_dimension_items(value: Any) -> list[Any]:
    if not isinstance(value, (list, tuple, set)):
        return []
    unique: list[Any] = []
    seen: set[tuple[str, str]] = set()
    for item in value:
        if isinstance(item, str):
            item = normalize_text(item).strip()
            if not item:
                continue
            key = ("str", _keyword_dedup_key(item))
        else:
            key = (type(item).__name__, repr(item))
        if key in seen:
            continue
        seen.add(key)
        unique.append(item)
    return unique
def score_six_dimensions(desc: str, *,
                         trigger_examples: list[str],
                         role_info: dict,
                         coverage_info: dict,
                         anchor_info: dict,
                         synonyms: list[str]) -> dict[str, float]:
    desc = normalize_text(desc)
    trigger_examples = _unique_dimension_items(
        normalize_descriptions(trigger_examples))
    role_info = dict_or_empty(role_info)
    coverage_info = dict_or_empty(coverage_info)
    anchor_info = dict_or_empty(anchor_info)
    synonyms = _unique_dimension_items(normalize_descriptions(synonyms))
    scores = {}
    business_content = _LEADING_TRIGGER_MARK.sub("", desc, count=1)
    hit_langs = (int(bool(re.search(RE_CHINESE_CHARS, business_content)))
                 + int(bool(re.search(r'[a-zA-Z]', business_content))))
    scores["bilingual"] = _ladder_pick(hit_langs, ((2, 1.0), (1, 0.3)), default=0.0)
    spoken_hits = len(synonyms)
    scores[FIELD_SYNONYM_COVERAGE] = min(spoken_hits / 8.0, 1.0)
    scores["user_examples"] = (_ladder_pick(
        len(trigger_examples), ((20, 1.0), (10, 0.8), (5, 0.6), (3, 0.4)),
        default=0.2) if trigger_examples else 0.0)
    matched_roles = _unique_dimension_items(role_info.get("matched_roles"))
    scores["role_perspective"] = _ladder_pick(
        len(matched_roles), ((3, 1.0), (2, 0.8), (1, 0.5)), default=0.0)
    caps = _unique_dimension_items(coverage_info.get("capabilities"))
    scores[FIELD_CAPABILITY_COVERAGE] = _ladder_pick(
        len(caps), ((8, 1.0), (5, 0.8), (3, 0.6), (1, 0.4)), default=0.0)
    scores["skill_anchors"] = _score_anchor_dim(anchor_info)
    return scores
def _anchor_score_identity(item: Any) -> Any:
    if isinstance(item, Mapping):
        name = item.get("name")
        return name if isinstance(name, str) else ""
    return item if isinstance(item, str) else ""
def _score_anchor_dim(anchor_info: dict) -> float:
    anchor_info = dict_or_empty(anchor_info)
    anchors = _unique_dimension_items(
        [_anchor_score_identity(item) for item in
         _unique_dimension_items(anchor_info.get("matched_anchors"))])
    tags = _unique_dimension_items(anchor_info.get("tags"))
    anchor_count = len(anchors)
    tag_count = len(tags)
    if anchor_count >= 2 and tag_count >= 2:
        return 1.0
    if anchor_count >= 1 and tag_count >= 1:
        return 0.7
    if anchor_count >= 1 or tag_count >= 1:
        return 0.4
    return 0.0
_GRADE_LADDER: tuple[tuple[float, str], ...] = (
    (85, "A - 优秀（高触发概率）"),
    (70, "B - 良好（可稳定触发）"),
    (55, "C - 一般（存在漏触发风险）"),
    (40, "D - 较差（需大幅优化）"),
)
def grade_from_score(score: float) -> str:
    return _ladder_pick(score, _GRADE_LADDER, "F - 不合格（严重需要优化）")
@dataclass(frozen=True)
class _TriggerDimension:
    key: str
    weight: float
    issue_threshold: float
    issue: str
    suggestion: str
_TRIGGER_DIMENSIONS: tuple[_TriggerDimension, ...] = (
    _TriggerDimension(
        'has_trigger_command', 0.15, 0.5,
        '缺少强制触发词（MUST USE/CRITICAL TRIGGER）',
        "添加强制触发指令词（如 'MUST USE'/'PRIORITY LOAD'）"),
    _TriggerDimension(
        'has_scenario_boundary', 0.15, 0.5,
        '缺少明确的触发场景描述',
        "添加场景边界描述（如'当用户要求...时使用'）"),
    _TriggerDimension(
        'has_keywords_embedded', 0.10, 0.5,
        '关键词未充分内嵌在描述中',
        '将核心关键词内嵌到 description 中，提升语义命中率'),
    _TriggerDimension(
        'has_negative_rule', 0.15, 0.5,
        '缺少反向排除规则（NOT FOR/DO NOT USE FOR）',
        "添加反向排除规则（如'NOT FOR: 不相关的任务'）"),
    _TriggerDimension(
        'length_optimal', 0.05, 0.6,
        f'描述长度不在黄金区间（{DESC_OPTIMAL_MIN}-{DESC_MAX}字符为佳）',
        '调整描述长度至最优范围（当前过短或过长）'),
    _TriggerDimension(
        'specificity', 0.15, 0.5,
        '描述包含过多空泛词汇',
        "替换空泛词汇为具体描述（避免使用'处理'/'操作'等模糊词）"),
    _TriggerDimension(
        'differentiation', 0.10, 0.5,
        '与其他技能的区分度不足',
        '添加领域区分词，使技能与其他领域技能区分开'),
    _TriggerDimension(
        'spoken_coverage', 0.05, 0.5,
        '口语化触发词覆盖不足',
        "增加口语化触发词覆盖（如'做个'/'查查'/'看看'）"),
    _TriggerDimension(
        'multilingual_coverage', 0.05, 0.5,
        '中英文关键词覆盖不均衡',
        '增加中英双语关键词覆盖'),
)
_TRIGGER_SCORE_WEIGHTS: dict[str, float] = {
    dim.key: dim.weight for dim in _TRIGGER_DIMENSIONS
}
_SUGGESTION_SCORE_THRESHOLD = 0.5
_NEGATION_GAP_CHARS = set('的任务工作内容需求请求之类等项 \t')
def _neg_window_start(desc_lower: str, pos: int, neg_markers: list,
                      neg_marker_max: int) -> int:
    win_start = max(0, pos - 40)
    if win_start <= 0 or not neg_marker_max:
        return win_start
    cross = _crossing_marker_start(desc_lower, win_start, neg_markers)
    return cross if cross >= 0 else win_start
def _crossing_marker_start(desc_lower: str, win_start: int, neg_markers: list) -> int:
    cross = -1
    for marker in neg_markers:
        if len(marker) < 2:
            continue
        lo = max(0, win_start - len(marker) + 1)
        start = desc_lower.find(marker, lo, win_start + len(marker) - 1)
        if 0 <= start < win_start and (cross < 0 or start < cross):
            cross = start
    return cross
def _trailing_negation_hit(desc_lower: str, end: int, neg_markers: list,
                           neg_marker_max: int) -> bool:
    gap = desc_lower[end:end + 8]
    gi = 0
    while gi < len(gap) and gap[gi] in _NEGATION_GAP_CHARS:
        gi += 1
    return any(
        keyword_matches(nm, desc_lower[end + gi:end + gi + neg_marker_max])
        for nm in neg_markers if not nm.isascii())
def _in_negation_context(desc_lower: str, pos: int, word_len: int,
                         neg_markers: list, neg_marker_max: int) -> bool:
    window = desc_lower[
        _neg_window_start(desc_lower, pos, neg_markers, neg_marker_max):pos]
    if any(keyword_matches(marker, window) for marker in neg_markers):
        return True
    return _trailing_negation_hit(
        desc_lower, pos + word_len, neg_markers, neg_marker_max)
def _trigger_score_suggestions(scores: dict[str, float]) -> list[str]:
    return [dim.suggestion for dim in _TRIGGER_DIMENSIONS
            if scores.get(dim.key, 1.0) < _SUGGESTION_SCORE_THRESHOLD]
def _score_differentiation(
        description: str, existing_descs: list[str] | None = None) -> float:
    existing = normalize_descriptions(existing_descs)
    if not existing:
        return _NEUTRAL_DIFFERENTIATION_SCORE
    overlap = differentiate_from_existing(description, existing)["max_overlap"]
    return min(1.0, max(0.0, 1.0 - overlap))
def _has_negative_rule_signal(desc: str) -> bool:
    return bool(_extract_negative_rules(normalize_text(desc)))
def _score_text_presence_dims(desc_lower: str,
                              top_kws: list[str]) -> dict[str, float]:
    keyword_score, _keyword_detail = _score_keyword_dim(top_kws, desc_lower)
    return {
        'has_trigger_command': _score_trigger_dim(desc_lower)[0],
        'has_scenario_boundary': _score_scenario_dim(desc_lower)[0],
        'has_keywords_embedded': keyword_score,
        'has_negative_rule': _score_negative_dim(
            _has_negative_rule_signal(desc_lower))[0],
    }
def _score_coverage_dims(
        description: str, desc_lower: str, keywords: list[str],
        existing_descs: list[str] | None = None) -> dict[str, float]:
    ml = evaluate_multilingual_coverage(keywords)
    return {
        'length_optimal': _score_length_dim(description)[0],
        'specificity': _score_specificity_dim(description)[0],
        'differentiation': _score_differentiation(description, existing_descs),
        'spoken_coverage': _score_spoken_dim(desc_lower)[0],
        'multilingual_coverage': ml.get('coverage_score', 0.0),
    }
def _weighted_total(scores: dict[str, float],
                    weights: Mapping[str, float] | None = None) -> float:
    weight_table = _TRIGGER_SCORE_WEIGHTS if weights is None else weights
    weight_sum = sum(weight_table.get(k, 0.0) for k in scores)
    if weight_sum <= 0:
        return 0.0
    weighted = sum(scores[k] * weight_table.get(k, 0.0)
                   for k in scores)
    return weighted / weight_sum
def compute_trigger_score(
        description: str, keywords: list[str],
        existing_descs: list[str] | None = None) -> dict[str, Any]:
    keywords = normalize_keywords(keywords)
    description = normalize_text(description)
    desc_lower = description.lower()
    scores = _score_text_presence_dims(desc_lower, keywords[:10])
    scores.update(_score_coverage_dims(
        description, desc_lower, keywords, existing_descs))
    total = _weighted_total(scores)
    suggestions = _trigger_score_suggestions(scores)
    return {
        'total_score': round(total * 100, 2),
        'scores': scores,
        'breakdown': {k: round(v * 100, 2) for k, v in scores.items()},
        'suggestions': suggestions,
    }
def score_to_grade(score: float) -> str:
    if score >= 0.85:
        return 'A (优秀)'
    if score >= 0.7:
        return 'B (良好)'
    if score >= 0.55:
        return 'C (合格)'
    if score >= 0.4:
        return 'D (需改进)'
    return 'F (不合格)'
def identify_issues(scores: dict[str, float]) -> list[str]:
    return [dim.issue for dim in _TRIGGER_DIMENSIONS
            if scores.get(dim.key, 1.0) < dim.issue_threshold]
def check_vagueness(desc: str) -> dict:
    found = detect_vague_words(desc)
    vagueness_ratio = len(found) / max(text_token_count(desc), 1)
    return {
        "vagueness_ratio": round(vagueness_ratio, 3),
        "vague_words": found,
        "is_vague": vagueness_ratio > 0.15,
    }
def _without_negated_indicator(desc_lower: str, indicator: str,
                               neg_markers: list[str],
                               neg_marker_max: int) -> str:
    word = indicator.lower()
    if not word:
        return desc_lower
    masked: list[str] | None = None
    start = 0
    while (pos := desc_lower.find(word, start)) >= 0:
        if _in_negation_context(
                desc_lower, pos, len(word), neg_markers, neg_marker_max):
            if masked is None:
                masked = list(desc_lower)
            masked[pos:pos + len(word)] = " " * len(word)
        start = pos + 1
    return "".join(masked) if masked is not None else desc_lower
def _has_unnegated_stem(desc_lower: str, indicator: str,
                        neg_markers: list[str], neg_marker_max: int) -> bool:
    if not stem_matches(indicator, desc_lower):
        return False
    positive_text = _without_negated_indicator(
        desc_lower, indicator, neg_markers, neg_marker_max)
    return stem_matches(indicator, positive_text)
_RESPONSIBILITY_STOPWORDS: frozenset[str] = frozenset({
    "the", "a", "an", "this", "that", "current", "task", "tasks",
    "item", "items", "request", "requested", "skill", "tool", "tools",
    "for", "of", "to", "in", "on", "with", "by", "from", "into",
    "and", "or", "user", "users", "need", "needs", "when", "other",
    "not", "never", "etc", "must", "always", "load", "critical",
    "trigger", "priority", "be", "invoked",
})
_CN_RESPONSIBILITY_STOPWORDS: tuple[str, ...] = (
    "当前", "任务", "请求", "技能", "工具", "用户", "需要", "使用",
    "支持", "相关", "对象", "工作", "内容", "适用于", "用于", "的", "了",
    "和", "或", "与", "及", "以及", "等",
)
_CN_ACTION_WORD_ALT = "|".join(re.escape(word) for word in sorted(
    (word for word in _RESPONSIBILITY_ACTION_WORDS if not word.isascii()),
    key=len, reverse=True))
_RESPONSIBILITY_SPLIT_RE = re.compile(
    rf"[。；;！!？?，,\n、]+|(?<!\d)\.(?!\d)|"
    rf"\b(?:and|also|then|but|however)\b|但(?:是)?|不过|然而|"
    rf"同时|并且|此外|然后|以及|(?<!合)并(?={_CN_ACTION_WORD_ALT})",
    re.IGNORECASE)
def _is_action_token(token: str) -> bool:
    return any(stem_matches(action, token)
               for action in _RESPONSIBILITY_ACTION_WORDS if action.isascii())
def _domain_label_from_clause(clause: str) -> str:
    text = re.sub(
        r"[A-Za-z]+",
        lambda match: " " if _is_action_token(match.group(0)) else match.group(0),
        clause.lower())
    chinese_actions = sorted(
        (word for word in _RESPONSIBILITY_ACTION_WORDS if not word.isascii()),
        key=len, reverse=True)
    for action in (*chinese_actions, *NEGATIVE_COMMANDS):
        if not action.isascii():
            text = text.replace(action.lower(), " ")
    for word in _CN_RESPONSIBILITY_STOPWORDS:
        text = text.replace(word, " ")
    text = re.sub(r"[^a-z0-9\u4e00-\u9fff]+", " ", text)
    tokens = [token for token in text.split()
              if len(token) >= 2 and token not in _RESPONSIBILITY_STOPWORDS]
    return " ".join(tokens).strip()[:80]
def _labels_related(left: str, right: str) -> bool:
    left_parts = re.findall(r"[a-z0-9]+|[\u4e00-\u9fff]+", left)
    right_parts = re.findall(r"[a-z0-9]+|[\u4e00-\u9fff]+", right)
    for left_part in left_parts:
        for right_part in right_parts:
            if left_part == right_part:
                return True
            if left_part.isascii() and right_part.isascii():
                if (stem_matches(left_part, right_part)
                        or stem_matches(right_part, left_part)):
                    return True
            elif (not left_part.isascii() and not right_part.isascii()
                  and min(len(left_part), len(right_part)) >= 2
                  and (left_part in right_part or right_part in left_part)):
                return True
    return False
def check_atomicity(name: str, desc: str) -> dict:
    combined = (normalize_text(desc).strip()
                or normalize_text(name).strip()).lower()
    combined = _positive_business_text(combined).lower()
    neg_markers = [cmd.lower() for cmd in NEGATIVE_COMMANDS]
    neg_marker_max = max((len(marker) for marker in neg_markers), default=0)
    detected_domains: list[str] = []
    for clause in _RESPONSIBILITY_SPLIT_RE.split(combined):
        if _is_negation_clause(clause):
            continue
        label = _domain_label_from_clause(clause)
        if not label:
            continue
        scope = clause.strip()
        if stem_matches(label, scope):
            if not _has_unnegated_stem(
                    scope, label, neg_markers, neg_marker_max):
                continue
        else:
            parts = [part for part in label.split() if len(part) >= 2]
            if parts and not any(_has_unnegated_stem(
                    scope, part, neg_markers, neg_marker_max) for part in parts):
                continue
        if not any(_labels_related(label, existing)
                   for existing in detected_domains):
            detected_domains.append(label)
    domain_count = len(detected_domains)
    risk_level = ("unknown" if domain_count == 0
                  else "low" if domain_count == 1
                  else "medium" if domain_count == 2 else "high")
    return {
        "detected_domains": detected_domains,
        "domain_count": domain_count,
        "is_atomic": domain_count <= 1,
        "risk_level": risk_level,
    }
def _evaluate_quality(optimized_desc: str, keyword_list: list[str], golden: dict,
                      differentiation: dict,
                      has_existing_descs: bool) -> tuple[dict, dict, float, float, str]:
    diff_score = (max(0.0, 1.0 - differentiation.get("max_overlap", 0.0))
                  if has_existing_descs else None)
    has_examples = (bool(golden.get(FIELD_TRIGGER_EXAMPLES))
                    or _has_section_marker(optimized_desc, _LABEL_EXAMPLES))
    quality = score_description_quality(
        optimized_desc, keyword_list, _has_negative_rule_signal(optimized_desc),
        has_examples, differentiation=diff_score)
    six_dim_scores = score_six_dimensions(
        optimized_desc,
        trigger_examples=golden.get(FIELD_TRIGGER_EXAMPLES, []),
        role_info=golden.get("role_info", {}),
        coverage_info=golden.get("coverage_info", {}),
        anchor_info=golden.get("anchor_info", {}),
        synonyms=golden.get("synonyms", []))
    quality["six_dim_scores"] = six_dim_scores
    six_dim_total = round(
        _weighted_total(six_dim_scores, SIX_DIM_WEIGHTS) * 100, 1)
    quality["six_dim_total"] = six_dim_total
    score = round(quality.get("total", 0.0) * 0.5 + six_dim_total * 0.5, 1)
    return quality, six_dim_scores, six_dim_total, score, grade_from_score(score)
def _build_six_dimensions(keyword_list: list[str], golden: dict) -> dict[str, Any]:
    return {
        "bilingual": {
            "cn_keywords": [kw for kw in keyword_list if re.search(RE_CHINESE_CHARS, kw)],
            "en_keywords": [kw for kw in keyword_list if re.search(r'[a-zA-Z]', kw)],
        },
        FIELD_SYNONYM_COVERAGE: golden.get("synonyms", []),
        "user_examples_count": len(golden.get(FIELD_TRIGGER_EXAMPLES, [])),
        "user_examples": golden.get(FIELD_TRIGGER_EXAMPLES, [])[:25],
        "role_perspective": golden.get("role_info", {}),
        FIELD_CAPABILITY_COVERAGE: golden.get("coverage_info", {}),
        "skill_anchors": golden.get("anchor_info", {}),
    }
def enhance_skill_discoverability(
    skill_name: str,
    description: str,
    keywords: list[str] | None = None,
    skill_type: str = _DEFAULT_SKILL_TYPE,
    existing_descs: list[str] | None = None,
    anchors: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    skill_name, description, skill_type = _normalize_inputs(
        skill_name, description, skill_type)
    keywords = normalize_keywords(keywords)
    existing_descriptions = normalize_descriptions(existing_descs)
    business_core = strip_injected_sections(description)
    golden = compose_golden_description(
        skill_name, description, skill_type, anchors=anchors)
    optimized_desc = clamp_description_to_hard_limit(
        golden.get("description", description))
    must_trigger = golden.get("must_trigger", "")
    trigger_examples = golden.get(FIELD_TRIGGER_EXAMPLES, [])
    negative_rules = generate_negative_rules(business_core)
    expanded_keywords = build_keyword_matrix(
        skill_name, business_core, keywords)
    keyword_list = expanded_keywords["keywords"]
    differentiation = differentiate_from_existing(
        optimized_desc, existing_descriptions)
    (quality, six_dim_scores, six_dim_total,
     score, grade) = _evaluate_quality(
        optimized_desc, keyword_list, golden,
        differentiation, bool(existing_descriptions))
    vagueness = check_vagueness(optimized_desc)
    atomicity = check_atomicity(skill_name, business_core)
    return {
        "skill_name": skill_name,
        "original_description": description,
        FIELD_OPTIMIZED_DESCRIPTION: optimized_desc,
        "must_trigger": must_trigger,
        FIELD_TRIGGER_EXAMPLES: trigger_examples,
        "negative_rules": negative_rules,
        "keywords": keyword_list,
        "keyword_groups": expanded_keywords["groups"],
        "keyword_total": expanded_keywords["total_count"],
        "quality_score": score,
        "quality_grade": grade,
        "quality_details": quality,
        "vagueness": vagueness,
        "atomicity": atomicity,
        "differentiation": differentiation,
        "enhanced": score >= 60.0,
        FIELD_DISCOVERABILITY_INDEX: score,
        "six_dimensions": _build_six_dimensions(keyword_list, golden),
        "six_dim_scores": six_dim_scores,
        "six_dim_total": six_dim_total,
    }
def generate_six_dim_description(
    skill_name: str,
    description: str = "",
    keywords: list[str] | None = None,
    skill_type: str = _DEFAULT_SKILL_TYPE,
    anchors: Mapping[str, Any] | None = None,
) -> str:
    description = normalize_text(description)
    result = enhance_skill_discoverability(
        skill_name=skill_name,
        description=description,
        keywords=keywords,
        skill_type=skill_type,
        anchors=anchors,
    )
    return clamp_description_to_hard_limit(
        result.get(FIELD_OPTIMIZED_DESCRIPTION, description))
def clamp_description_to_hard_limit(description: str) -> str:
    description = normalize_text(description)
    if len(description) <= DESC_MAX:
        return description
    clamped = truncate_description(description, DESC_MAX, "。")
    logger.warning(
        "六维描述超出硬上限 %d 字符（实测 %d），已收敛至 %d 字符",
        DESC_MAX, len(description), len(clamped))
    return clamped
def _markdown_table_cell(text: str) -> str:
    return (text.replace("\\", "\\\\").replace("|", "\\|")
            .replace("\r\n", "<br>").replace("\r", "<br>")
            .replace("\n", "<br>"))
def _dim_row(dim_label: str, scores: dict, score_key: str,
             threshold: float, detail: str) -> str:
    mark = "✓" if _six_dim_score_of(scores, score_key) >= threshold else "✗"
    return (f"| {_markdown_table_cell(dim_label)} | {mark} | "
            f"{_markdown_table_cell(detail)} |")
_EXAMPLES_PER_ROW = 4
_UNSCENED_EXAMPLE_LABEL = "custom"
_TRIGGER_EXAMPLE_SECTION_TITLE = "## 典型用户指令示例"
def _chunked(items: list[str], size: int) -> list[list[str]]:
    return [items[i:i + size] for i in range(0, len(items), size)]
def _render_trigger_examples_table(trigger_examples: list[str]) -> list[str]:
    examples = list(dict.fromkeys(
        text.strip() for text in trigger_examples
        if isinstance(text, str) and text.strip()))
    if not examples:
        return []
    parts: list[str] = ["| 场景 | 指令示例 |", "|------|---------|"]
    rendered: set[str] = set()
    for scene_key, scene_examples in TRIGGER_EXAMPLE_TEMPLATES.items():
        matching = [e for e in scene_examples
                    if e in examples and e not in rendered]
        if not matching:
            continue
        rendered.update(matching)
        for chunk in _chunked(matching, _EXAMPLES_PER_ROW):
            parts.append(
                f"| {_markdown_table_cell(scene_key)} | "
                f"{_markdown_table_cell(' / '.join(chunk))} |")
    for chunk in _chunked([e for e in examples if e not in rendered],
                          _EXAMPLES_PER_ROW):
        parts.append(
            f"| {_markdown_table_cell(_UNSCENED_EXAMPLE_LABEL)} | "
            f"{_markdown_table_cell(' / '.join(chunk))} |")
    return parts
SIX_DIM_ROWS: tuple[tuple[str, str, float], ...] = tuple(
    (label, key, threshold) for key, label, threshold in SIX_DIM_SPECS)
def six_dim_threshold(score_key: str, default: float = 0.0) -> float:
    return next((_t for _label, _key, _t in SIX_DIM_ROWS if _key == score_key), default)
def _six_dim_details(six_dim_data: dict, trigger_examples: list[str]) -> dict[str, str]:
    coverage_info = dict_or_empty(six_dim_data.get(FIELD_CAPABILITY_COVERAGE))
    role_info = dict_or_empty(six_dim_data.get("role_perspective"))
    anchor_info = dict_or_empty(six_dim_data.get("skill_anchors"))
    synonym_info = normalize_descriptions(
        six_dim_data.get(FIELD_SYNONYM_COVERAGE))
    trigger_examples = normalize_descriptions(trigger_examples)
    capabilities = coverage_info.get("capabilities") or []
    if not isinstance(capabilities, (list, tuple, set)):
        capabilities = []
    anchor_names = [
        str(entry["name"])
        for entry in anchor_info.get("matched_anchors") or []
        if isinstance(entry, Mapping) and entry.get("name")
    ]
    roles = role_info.get("matched_roles") or []
    if not isinstance(roles, (list, tuple, set)):
        roles = []
    matched_roles = [role for role in roles
                     if isinstance(role, str) and role.strip()]
    return {
        "bilingual": "description 中英双语覆盖",
        FIELD_SYNONYM_COVERAGE: "、".join(synonym_info[:6]),
        "user_examples": f"{len(trigger_examples)} 条示例",
        "role_perspective": "、".join(matched_roles),
        FIELD_CAPABILITY_COVERAGE: f"{len(capabilities)} 项能力",
        "skill_anchors": "、".join(anchor_names),
    }
def _render_six_dim_table(six_dim_scores: dict, six_dim_data: dict,
                          trigger_examples: list[str]) -> list[str]:
    details = _six_dim_details(six_dim_data, trigger_examples)
    rows = [_dim_row(label, six_dim_scores, key, threshold, details.get(key, ""))
            for label, key, threshold in SIX_DIM_ROWS]
    return ["| 维度 | 状态 | 详情 |", MD_TABLE_SEP_3COL, *rows]
def render_six_dim_section(six_dim_result: dict) -> str:
    six_dim_result = dict_or_empty(six_dim_result)
    trigger_examples = normalize_descriptions(
        six_dim_result.get(FIELD_TRIGGER_EXAMPLES))
    example_rows = _render_trigger_examples_table(trigger_examples)
    parts = [""]
    if example_rows:
        parts.extend([
            _TRIGGER_EXAMPLE_SECTION_TITLE,
            "",
            "匹配以下任意说法即触发本技能：",
            "",
            *example_rows,
            "",
        ])
    parts.extend([SIX_DIM_SECTION_TITLE, ""])
    parts.extend(_render_six_dim_table(
        dict_or_empty(six_dim_result.get("six_dim_scores")),
        dict_or_empty(six_dim_result.get("six_dimensions")),
        trigger_examples))
    parts.append("")
    return "\n".join(parts)
def _read_utf8_text(path: str) -> str:
    with open(path, encoding="utf-8-sig", newline="") as fh:
        return fh.read()
def _normalize_cr_only(text: str) -> tuple[str, bool]:
    if "\r" in text and "\n" not in text:
        return text.replace("\r", "\n"), True
    return text, False
def _restore_cr_only(text: str, cr_only: bool) -> str:
    return text.replace("\n", "\r") if cr_only else text
def _apply_six_dim_to_content(current_content: str,
                              skill_name: str) -> tuple[str, dict[str, Any]]:
    current_content, cr_only = _normalize_cr_only(current_content)
    skill_name = read_frontmatter_skill_name(current_content, skill_name)
    current_desc = extract_description_lenient(current_content)
    enhance_result = enhance_skill_discoverability(
        skill_name=skill_name,
        description=current_desc,
        keywords=[],
        skill_type=_DEFAULT_SKILL_TYPE,
    )
    raw_optimized_desc = normalize_str(
        enhance_result.get(FIELD_OPTIMIZED_DESCRIPTION))
    _validate_six_dim_generation(current_desc, raw_optimized_desc or current_desc)
    optimized_desc = clamp_description_to_hard_limit(raw_optimized_desc)
    six_dim_data = dict_or_empty(enhance_result.get("six_dimensions"))
    six_dim_scores = dict_or_empty(enhance_result.get("six_dim_scores"))
    current_content, _note, _status = _apply_description_optimization(
        current_content, current_desc, optimized_desc)
    if _status in ("empty", "missing_key"):
        return (_restore_cr_only(current_content, cr_only),
                {"six_dim_enhanced": False, "six_dim_note": _note})
    refreshed = _refresh_or_append_six_dim_section(
        current_content, render_six_dim_section(enhance_result))
    result = {
        "six_dim_enhanced": _status == "applied" or refreshed != current_content,
        "six_dim_scores": six_dim_scores,
        "six_dim_examples_count": six_dim_data.get("user_examples_count", 0),
    }
    if _note is not None:
        result["six_dim_note"] = _note
    logger.info("六维增强完成: description已优化")
    return _restore_cr_only(refreshed, cr_only), result
def _validate_six_dim_generation(original_desc: str,
                                 generated_desc: str) -> None:
    try:
        v_report = validate_description_generation(
            original_desc=original_desc,
            generated_desc=generated_desc,
        )
        if not v_report.passed:
            logger.warning("refactor_skill_doc 六维验证未通过: %s", v_report.failures)
    except Exception:
        logger.warning("refactor_skill_doc: 六维生成后验证异常(已抑制)", exc_info=True)
def _apply_description_optimization(
    content: str, current_desc: str, optimized_desc: str,
) -> tuple[str, str | None, str]:
    if not optimized_desc:
        return content, "description 无需优化", "empty"
    if optimized_desc == current_desc:
        return content, "description 无需优化", "unchanged"
    _replaced = replace_frontmatter_description(
        content, yaml_safe_desc_line(optimized_desc))
    if _replaced == content:
        return content, "description 替换未生效（缺少锚点或替换结果未变化）", "missing_key"
    return _replaced, None, "applied"
def _six_dim_score_of(six_dim_scores: dict, key: str,
                      default: float = 0.0) -> float:
    value = six_dim_scores.get(key, default)
    if isinstance(value, bool):
        return default
    try:
        score = float(value)
    except (TypeError, ValueError, OverflowError) as e:
        logger.debug("_six_dim_score_of 分值不可解析(%s): %r (%s)", key, value, e)
        return default
    return score if math.isfinite(score) else default
def _refresh_or_append_six_dim_section(current_content: str,
                                       six_dim_body: str) -> str:
    current_content, cr_only = _normalize_cr_only(current_content)
    _eol, six_dim_body = match_source_eol(current_content, six_dim_body)
    section = six_dim_body.strip()
    current_content = _strip_legacy_example_sections(current_content)
    span = locate_section(current_content, SIX_DIM_SECTION_TITLE)
    if span is None:
        result = (current_content.rstrip("\r\n") + _eol + _eol
                  + six_dim_body.lstrip("\r\n"))
    else:
        start, end = span
        if end < len(current_content):
            result = (current_content[:start] + section + _eol + _eol
                      + current_content[end:])
        else:
            trailing = _eol if current_content.endswith(("\n", "\r")) else ""
            result = current_content[:start] + section + trailing
    return _restore_cr_only(result, cr_only)
def _strip_legacy_example_sections(content: str) -> str:
    while True:
        span = locate_section(content, _TRIGGER_EXAMPLE_SECTION_TITLE)
        if span is None:
            return content
        content = content[:span[0]] + content[span[1]:]
def _six_dim_degrade(detail: Any) -> dict[str, Any]:
    logger.warning("六维增强后处理失败: %s", detail)
    return {"six_dim_enhanced": False, "six_dim_note": f"增强失败: {detail}"}
def enhance_content_six_dim(new_content: str, skill_name: str,
                               enhance_six_dim: bool) -> tuple[str, dict[str, Any]]:
    new_content = normalize_text(new_content)
    if not enhance_six_dim:
        return new_content, {}
    try:
        return _apply_six_dim_to_content(new_content, skill_name)
    except Exception as _e:
        log_swallowed(__name__, _e,
                      context=f'enhance_content_six_dim:{type(_e).__name__}')
        return new_content, _six_dim_degrade(_e)
def enhance_proposal_file_six_dim(result: dict[str, Any],
                                    md_path: str) -> None:
    if not isinstance(result, dict):
        logger.warning("enhance_proposal_file_six_dim: result 非映射(%s)，跳过",
                       type(result).__name__)
        return
    _raw_path = result.get("output_path")
    final_path = normalize_path_arg(_raw_path)
    if not isinstance(final_path, str) or not final_path:
        result.update(_six_dim_degrade(
            "refactor_and_save 未返回 output_path（契约异常）: "
            f"{type(_raw_path).__name__}"))
        return
    try:
        current_content = _read_utf8_text(final_path)
        current_content, _six_dim = _apply_six_dim_to_content(
            current_content,
            os.path.basename(os.path.dirname(os.path.abspath(md_path))))
        if _six_dim.get("six_dim_enhanced"):
            with guarded_open(final_path, "w", encoding="utf-8",
                              newline="") as _f:
                _f.write(current_content)
        result.update(_six_dim)
    except Exception as _e:
        log_swallowed(__name__, _e,
                      context=f'enhance_proposal_file_six_dim:{type(_e).__name__}')
        result.update(_six_dim_degrade(_e))
def _warn_validation_gaps(raw_desc: str, enriched: object,
                          keywords: list[str]) -> None:
    try:
        v_report = validate_description_generation(
            original_desc=raw_desc, generated_desc=enriched,
            keywords=keywords)
    except Exception:
        logger.warning('generate_golden_description: 六维增强验证异常，保留增强产物', exc_info=True)
        return
    if not v_report.passed:
        logger.warning('六维增强验证未通过: %s', v_report.failures)
def _finalize_description(enriched: object, raw_desc: str) -> str:
    selected = enriched
    if not isinstance(selected, str) or not selected:
        logger.warning('generate_golden_description: 增强产物非可用 str（%s），回退 raw_desc',
                     type(enriched).__name__)
        selected = raw_desc
    return clamp_description_to_hard_limit(selected)
def _enhance_with_validation(raw_desc: str, skill_name: str,
                             keywords: list[str], skill_type: str) -> str:
    try:
        result = enhance_skill_discoverability(
            skill_name=skill_name, description=raw_desc,
            keywords=keywords, skill_type=skill_type)
        enriched = result.get(FIELD_OPTIMIZED_DESCRIPTION, raw_desc)
    except Exception as _e:
        logger.warning('generate_golden_description fallback to raw_desc: %s', _e, exc_info=True)
        enriched = raw_desc
    else:
        _warn_validation_gaps(raw_desc, enriched, keywords)
    return _finalize_description(enriched, raw_desc)
def _resolve_slot_parts(skill_name: str, action: str, scenario: str,
                        skill_type: str) -> tuple[str, str, str]:
    type_key = (skill_type if skill_type in TYPE_ACTION_WORDS
                else DOMAIN_HINT_TO_TYPE_KEY.get(skill_type, skill_type))
    subject = skill_name or "本技能"
    action_part = action or TYPE_ACTION_WORDS.get(
        type_key, f'处理 {subject} 相关任务')
    scenario_part = scenario or f'当用户需要执行 {subject} 相关操作时使用'
    return type_key, action_part, scenario_part
def _compose_raw_description(action_part: str, scenario_part: str, keywords: list[str],
                             skill_name: str, type_key: str,
                             negative_rules: list[str], trigger_cmd: str) -> str:
    kw_sample = (keywords[:8] if keywords
                 else [readable_skill_name(skill_name) or skill_name or "本技能"])
    kw_str = '、'.join(kw_sample)
    raw_desc = (f'[{trigger_cmd}] {action_part}. {scenario_part}. '
                f'核心能力: {kw_str}.')
    if negative_rules:
        raw_desc += f" NOT FOR: {'; '.join(negative_rules[:3])}."
    else:
        domain_neg = DOMAIN_NEGATIVES.get(type_key, DOMAIN_NEGATIVES['generic'])
        raw_desc += f" NOT FOR: {'; '.join(domain_neg[:3])}."
    return raw_desc
def generate_golden_description(skill_name: str, action: str = '', scenario: str = '',
                                keywords: list[str] | None = None,
                                skill_type: str = _DEFAULT_SKILL_TYPE,
                                negative_rules: list[str] | None = None) -> str:
    keywords = normalize_keywords(keywords)
    skill_name = normalize_text(skill_name)
    if not isinstance(skill_type, str):
        skill_type = _DEFAULT_SKILL_TYPE if not skill_type else str(skill_type)
    skill_type = canonical_skill_category(skill_type)
    action = normalize_text(action)
    scenario = normalize_text(scenario)
    negative_rules = normalize_keywords(negative_rules)
    action = _normalize_slot_text(action)
    if action and _action_slot_is_exclusion_only(action):
        negative_rules = normalize_keywords(
            [*negative_rules, *_extract_negative_rules(action)])
        action = ""
    scenario = _normalize_slot_text(scenario)
    type_key, action_part, scenario_part = _resolve_slot_parts(
        skill_name, action, scenario, skill_type)
    core_action = extract_core_action(skill_name, action)
    trigger_cmd = _trigger_command_for(core_action)
    raw_desc = _compose_raw_description(
        action_part, scenario_part, keywords, skill_name, type_key,
        negative_rules, trigger_cmd)
    return _enhance_with_validation(raw_desc, skill_name, keywords, skill_type)
def _action_slot_is_exclusion_only(action: str) -> bool:
    # 转折否定（handles A but not B）整体保留在同一子句后仍含正向前缀，
    # 不能只看「是否含否定谓词」，否则正向动作槽会被当成纯排除并清空。
    clauses = [clause for clause in _CLAUSE_SPLIT_RE.split(action)
               if clause.strip()]
    return bool(clauses) and all(
        _is_negation_clause(clause)
        and not _positive_prefix_before_negation(clause)
        for clause in clauses)
_CATEGORY_CANONICAL_ALIASES = {
    "skill": "skill-management",
    "skillops": "skill-management",
}
def canonical_skill_category(skill_type: object) -> str:
    category = (normalize_text(skill_type).strip().lower()
                or _DEFAULT_SKILL_TYPE)
    return _CATEGORY_CANONICAL_ALIASES.get(category, category)
_TRIGGER_POSITIVE_FLAGS: frozenset[str] = frozenset({'true', '1', 'yes'})
def _positive_trigger_queries(examples: list[dict[str, str]]) -> list[str]:
    queries = []
    for example in examples:
        if not isinstance(example, dict):
            continue
        should_trigger = str(example.get('should_trigger', '')).strip().lower()
        query = example.get('query')
        if should_trigger in _TRIGGER_POSITIVE_FLAGS and isinstance(query, str):
            query = query.strip()
            if query:
                queries.append(query)
    return queries
def _normalize_version(version: object) -> str:
    if version is None:
        return DEFAULT_SKILL_VERSION
    return normalize_text(version).strip() or DEFAULT_SKILL_VERSION
def _expand_template_keywords(
        keywords: list[str], readable: str, description: str) -> list[str]:
    seeds = [*keywords, readable, *readable.split()]
    matrix = build_keyword_matrix(readable, description, seeds)
    expanded = expand_keyword_matrix(matrix["keywords"])
    return expanded or [readable or 'skill']
def _ensure_trigger_and_exclusion(description: str) -> str:
    needs_trigger = _LEADING_TRIGGER_MARK.match(description) is None
    needs_exclusion = not _has_negative_rule_signal(description)
    prefix = f'[{_DEFAULT_TRIGGER_COMMAND}] '
    suffix = ' NOT FOR: 与此技能无关的通用任务。'
    reserve = ((len(prefix) if needs_trigger else 0)
                + (len(suffix) if needs_exclusion else 0))
    if reserve and len(description) + reserve > DESC_MAX:
        description = truncate_description(
            description, DESC_MAX - reserve, "。")
        if not needs_exclusion and not _has_negative_rule_signal(description):
            needs_exclusion = True
            reserve = (len(prefix) if needs_trigger else 0) + len(suffix)
            description = truncate_description(
                description, DESC_MAX - reserve, "。")
    if needs_trigger:
        description = prefix + description
    if needs_exclusion:
        description += suffix
    return description
def _build_frontmatter(skill_name: str, version: str, description: str,
                       keywords: list[str], skill_type: str) -> str:
    category_line = ''
    if skill_type and skill_type != _DEFAULT_SKILL_TYPE:
        category_line = f'category: {yaml_safe_quote(skill_type)}\n'
    frontmatter = (
        f'---\nname: {yaml_safe_quote(skill_name)}\nversion: {yaml_safe_quote(version)}\n'
        f'{category_line}{yaml_safe_desc_line(description)}\nkeywords:\n'
    )
    frontmatter += ''.join(f'  - {yaml_safe_quote(kw)}\n' for kw in keywords[:25])
    return frontmatter + '---\n\n'
def generate_skill_md_template(skill_name: str, description: str = '',
                               skill_type: str = _DEFAULT_SKILL_TYPE,
                               keywords: list[str] | None = None,
                               version: str = DEFAULT_SKILL_VERSION) -> str:
    keywords = normalize_keywords(keywords)
    skill_name = normalize_text(skill_name)
    description = normalize_text(description)
    skill_type = canonical_skill_category(skill_type)
    version = _normalize_version(version)
    display_name = skill_name or "unnamed-skill"
    readable = display_name.replace('-', ' ').replace('_', ' ')
    optimized_desc = (
        _enhance_with_validation(
            description, skill_name, keywords, skill_type)
        if description else generate_golden_description(
            skill_name, description, keywords=keywords, skill_type=skill_type)
    )
    optimized_desc = _ensure_trigger_and_exclusion(optimized_desc)
    expanded_kw = _expand_template_keywords(
        keywords, readable, description or optimized_desc)
    examples = generate_trigger_examples(skill_name, optimized_desc, expanded_kw)
    trigger_queries = _positive_trigger_queries(examples)
    body = build_unified_skill_md_body(
        skill_name=display_name, capabilities=[f'{readable} 相关操作'],
        exclusion_scopes=[f'与 {readable} 无关的任务'], trigger_examples=trigger_queries)
    return _build_frontmatter(
        display_name, version, optimized_desc, expanded_kw, skill_type) + body
_DESC_KEY_RE = re.compile(r"(?m)^description[ \t]*:")
def _has_description_field(content: str) -> bool:
    if not content:
        return False
    normalized = content.replace("\r\n", "\n").replace("\r", "\n")
    parts = split_frontmatter(normalized)
    return len(parts) >= 3 and bool(_DESC_KEY_RE.search(parts[1]))
def apply_six_dim_enhancement(skill_name: str, description: str,
                              skill_type: str,
                              result_content: str) -> tuple[bool, dict, str]:
    six_dim_enhanced = False
    six_dim_result: dict = {}
    result_content, cr_only = _normalize_cr_only(
        normalize_text(result_content))
    try:
        six_dim_result = enhance_skill_discoverability(
            skill_name=skill_name,
            description=description,
            keywords=[],
            skill_type=skill_type,
        )
        optimized_desc = six_dim_result.get(FIELD_OPTIMIZED_DESCRIPTION, "")
        clamped_desc = clamp_description_to_hard_limit(optimized_desc)
        if clamped_desc != optimized_desc:
            six_dim_result = {**six_dim_result,
                              FIELD_OPTIMIZED_DESCRIPTION: clamped_desc}
            optimized_desc = clamped_desc
        has_description_field = _has_description_field(result_content)
        description_status = "empty"
        if optimized_desc and has_description_field:
            current_description = extract_description_lenient(result_content)
            result_content, _note, description_status = (
                _apply_description_optimization(
                    result_content, current_description, optimized_desc))
            if description_status == "missing_key":
                logger.warning(
                    "preflight fixer: description 替换未生效（锚点漂移），"
                    "保留原描述并跳过六维区块注入")
        if description_status in ("applied", "unchanged"):
            result_content = _refresh_or_append_six_dim_section(
                result_content, render_six_dim_section(six_dim_result))
            six_dim_enhanced = True
            message = ("六维可发现性增强: description 已替换为优化描述"
                       if description_status == "applied" else
                       "六维可发现性增强: 诊断与示例区块已就绪")
            logger.info("preflight fixer: %s", message)
    except Exception as exc:
        logger.warning("Six-dim enhancement failed: %s", exc)
        six_dim_result = {"error": str(exc)}
    return six_dim_enhanced, six_dim_result, _restore_cr_only(
        result_content, cr_only)
def _negative_rules_text(value: Any) -> str:
    if isinstance(value, str):
        return value.strip()
    return "; ".join(normalize_str_list(value))
def build_discoverability_section(meta: dict[str, Any]) -> dict[str, Any]:
    meta = meta if isinstance(meta, dict) else {}
    disc_result = enhance_skill_discoverability(
        meta.get("name", ""), meta.get("description", ""),
        meta.get("keywords"),
    )
    if not isinstance(disc_result, dict):
        disc_result = {}
    details = disc_result.get("quality_details")
    if not isinstance(details, dict):
        details = {}
    index_raw = disc_result.get(FIELD_DISCOVERABILITY_INDEX)
    if index_raw is None:
        index_raw = disc_result.get("quality_score")
    optimized_desc = disc_result.get(FIELD_OPTIMIZED_DESCRIPTION)
    recommendations = disc_result.get(FIELD_RECOMMENDATIONS)
    if recommendations is None:
        recommendations = details.get("details")
    return {
        FIELD_OPTIMIZED_DESCRIPTION: (
            clamp_description_to_hard_limit(optimized_desc)
            if isinstance(optimized_desc, str) else ""
        ),
        FIELD_OPTIMIZED_KEYWORDS: (
            normalize_str_list(disc_result.get(FIELD_OPTIMIZED_KEYWORDS))
            or normalize_str_list(disc_result.get("keywords"))
        ),
        FIELD_DISCOVERABILITY_INDEX: meta_num(index_raw),
        "quality_grade": str(
            disc_result.get("quality_grade") or details.get("grade") or "?"
        ),
        FIELD_TRIGGER_EXAMPLES: normalize_str_list(
            disc_result.get(FIELD_TRIGGER_EXAMPLES)),
        "negative_rules": _negative_rules_text(disc_result.get("negative_rules")),
        FIELD_RECOMMENDATIONS: normalize_str_list(recommendations),
    }
def build_script_score_section(skill_dir: str) -> dict[str, Any]:
    script_results = optimize_script_invocation(skill_dir)
    script_list = script_results if isinstance(script_results, list) else []
    scores = [meta_num(item.get("original_score"))
              for item in script_list if isinstance(item, dict)]
    average = round(sum(scores) / len(scores), 1) if scores else 0
    return {
        "scripts_checked": len(script_list),
        "results": script_list,
        "average_score": average,
        "layout": describe_script_layout(skill_dir),
    }
def compose_optimization_score(disc_index: float,
                               script_section: dict[str, Any]) -> float:
    index = meta_num(disc_index)
    script_section = dict_or_empty(script_section)
    if not meta_num(script_section.get("scripts_checked")):
        return index
    average = meta_num(script_section.get("average_score"))
    return round(index * 0.6 + average * 0.4, 1)
def average_optimization_score(results: list[dict[str, Any]]) -> float:
    items = results if isinstance(results, (list, tuple)) else []
    scores = [meta_num(r.get("overall_score")) for r in items
              if isinstance(r, dict) and not r.get("error")]
    return round(sum(scores) / max(len(scores), 1), 1)
_LOW_SCRIPT_SCORE = 70
@dataclass
class DiscoverabilityReport:
    skill_name: str = ""
    overall_score: float = 0.0
    grade: str = "F"
    trigger_score: float = 0.0
    script_score: float = 0.0
    description_quality: dict[str, Any] = field(default_factory=dict)
    keyword_coverage: dict[str, Any] = field(default_factory=dict)
    recommendations: list[str] = field(default_factory=list)
    auto_fixes_applied: list[str] = field(default_factory=list)
def _report_suggestions(trigger_score: dict, vague: list[str],
                        atomic_check: dict, ml_check: dict) -> list[str]:
    suggestions: list[str] = []
    if trigger_score["total_score"] < LOW_TRIGGER_SCORE:
        suggestions.append(f"触发评分较低 ({trigger_score['total_score']})，建议优化 description")
    if vague:
        suggestions.append(f"存在 {len(vague)} 个空泛词: {vague}")
    if not atomic_check["is_atomic"]:
        suggestions.append(atomic_check["suggestion"])
    if ml_check["suggestion"]:
        suggestions.append(ml_check["suggestion"])
    return suggestions
def generate_discoverability_report(
    skill_name: str, description: str, keywords: list[str],
    existing_descriptions: list[str] | None = None,
) -> dict[str, Any]:
    keywords = normalize_keywords(keywords)
    trigger_score = compute_trigger_score(
        description, keywords, existing_descs=existing_descriptions)
    if not isinstance(trigger_score, dict):
        trigger_score = {"total_score": 0.0, "scores": {}}
    vague = detect_vague_words(description)
    length_check = check_description_length(description)
    atomic_check = check_atomic_responsibility(description)
    ml_check = evaluate_multilingual_coverage(keywords)
    report = {
        "skill_name": skill_name,
        "generated_at": datetime.now().isoformat(),
        "trigger_score": trigger_score,
        "description_quality": {
            "length": length_check,
            "vague_words": vague,
            "vague_count": len(vague),
        },
        "keyword_coverage": ml_check,
        "atomicity": atomic_check,
        FIELD_RECOMMENDATIONS: _report_suggestions(
            trigger_score, vague, atomic_check, ml_check),
    }
    issues = identify_issues(dict(trigger_score.get("scores", {})))
    if issues:
        report["identified_issues"] = issues
    return report
def _merge_unique_recommendations(
    report: DiscoverabilityReport, items: list[str]
) -> None:
    for item in items:
        if item not in report.recommendations:
            report.recommendations.append(item)
def _collect_overlap_recommendations(
    optimized_desc: str, existing_descriptions: list[str]
) -> list[str]:
    try:
        diff = differentiate_from_existing(optimized_desc, existing_descriptions)
    except Exception:
        logger.warning("full_discoverability_enhance: 触发词差异化分析异常，跳过重叠告警",
                     exc_info=True)
        return []
    overlaps = diff.get("overlaps", []) if isinstance(diff, dict) else []
    messages: list[str] = []
    for overlap in overlaps:
        if not isinstance(overlap, dict):
            continue
        ratio = overlap.get("overlap_ratio")
        if isinstance(ratio, bool) or not isinstance(ratio, (int, float)):
            continue
        messages.append(
            f"与已有技能 #{overlap.get('index', '?')} 存在触发词重叠 ({ratio:.0%})")
    return messages
def _collect_sixdim_overlay(
    skill_name: str,
    optimized_desc: str,
    expanded_kw: list[str],
    skill_type: str,
    existing_descriptions: list[str] | None,
) -> tuple[dict[str, Any], list[str]]:
    try:
        six_result = enhance_skill_discoverability(
            skill_name=skill_name,
            description=optimized_desc,
            keywords=expanded_kw,
            skill_type=skill_type,
            existing_descs=existing_descriptions or [],
        )
    except Exception:
        logger.warning("full_discoverability_enhance: 六维增强评分异常，跳过叠加", exc_info=True)
        return {}, []
    if not isinstance(six_result, dict):
        return {}, []
    raw_examples = six_result.get(FIELD_TRIGGER_EXAMPLES)
    trigger_examples = raw_examples if isinstance(raw_examples, list) else []
    quality_overlay = {
        "six_dim_scores": six_result.get("six_dim_scores", {}),
        "six_dim_total": six_result.get("six_dim_total", 0.0),
        "quality_grade": six_result.get("quality_grade", ""),
        FIELD_TRIGGER_EXAMPLES: trigger_examples[:10],
    }
    quality_details = six_result.get("quality_details")
    if not isinstance(quality_details, dict):
        return quality_overlay, []
    raw_details = quality_details.get("details")
    details = raw_details if isinstance(raw_details, list) else []
    return quality_overlay, details[:3]
def _optimize_description_and_keywords(
    skill_name: str, description: str, keywords: list[str], skill_type: str
) -> tuple[str, list[str], list[str]]:
    description = normalize_text(description)
    try:
        optimized_desc = (
            _enhance_with_validation(
                description, skill_name, keywords, skill_type)
            if description else generate_golden_description(
                skill_name, description, keywords=keywords, skill_type=skill_type)
        )
    except (RuntimeError, ValueError, TypeError, KeyError) as exc:
        logger.warning("full_discoverability_enhance: 描述优化失败，保留原描述: %s", exc)
        optimized_desc = description
    if not isinstance(optimized_desc, str) or not optimized_desc.strip():
        optimized_desc = description
    fixes: list[str] = []
    if optimized_desc != description:
        fixes.append("description: 已优化为六维黄金结构")
    keyword_matrix = build_keyword_matrix(skill_name, description, keywords)
    expanded_kw = expand_keyword_matrix(keyword_matrix["keywords"])
    if not isinstance(expanded_kw, list):
        expanded_kw = list(keywords)
    if len(expanded_kw) > len(keywords):
        fixes.append(f"keywords: 从 {len(keywords)} 扩展到 {len(expanded_kw)} 个")
    return optimized_desc, expanded_kw, fixes
def _overall_recommendations(
    trigger_score: float, script_score: float | None
) -> list[str]:
    messages: list[str] = []
    if trigger_score < LOW_TRIGGER_SCORE:
        messages.append(f"触发评分 {trigger_score} 偏低，建议增加 MUST USE 指令和触发示例")
    if script_score is not None and script_score < _LOW_SCRIPT_SCORE:
        messages.append(
            "脚本 Agent 友好度不足，建议补齐结构化输出、dry-run、"
            "参数校验与模块 docstring")
    return messages
def full_discoverability_enhance(
    skill_dir: str,
    skill_name: str = "",
    description: str = "",
    keywords: list[str] | None = None,
    skill_type: str = _DEFAULT_SKILL_TYPE,
    existing_descriptions: list[str] | None = None,
    auto_generate_scripts: bool = True,
) -> DiscoverabilityReport:
    dir_text = coerce_target_file(skill_dir)
    if not skill_name:
        skill_name = (os.path.basename(dir_text.rstrip("/\\"))
                      if dir_text else "")
    keywords = normalize_keywords(keywords)
    existing_descriptions = normalize_descriptions(existing_descriptions)
    report = DiscoverabilityReport(skill_name=skill_name)
    optimized_desc, expanded_kw, fixes = _optimize_description_and_keywords(
        skill_name, description, keywords, skill_type)
    if existing_descriptions:
        _merge_unique_recommendations(
            report,
            _collect_overlap_recommendations(optimized_desc, existing_descriptions),
        )
    trigger_result = compute_trigger_score(
        optimized_desc, expanded_kw, existing_descs=existing_descriptions)
    report.trigger_score = trigger_result["total_score"]
    report.description_quality = trigger_result
    report.script_score, script_fix, scripts_evaluated = generate_scripts_segment(
        dir_text, skill_name, optimized_desc, auto_generate_scripts)
    if script_fix:
        fixes.append(script_fix)
    detail_report = generate_discoverability_report(
        skill_name, optimized_desc, expanded_kw,
        existing_descriptions=existing_descriptions)
    _merge_unique_recommendations(
        report, detail_report.get("identified_issues", []))
    if scripts_evaluated:
        report.overall_score = round(
            report.trigger_score * 0.6 + report.script_score * 0.4, 1)
    else:
        report.overall_score = round(report.trigger_score, 1)
    report.grade = score_to_grade(report.overall_score / 100)
    report.keyword_coverage = evaluate_multilingual_coverage(expanded_kw)
    report.auto_fixes_applied = fixes
    _merge_unique_recommendations(
        report,
        _overall_recommendations(
            report.trigger_score,
            report.script_score if scripts_evaluated else None),
    )
    quality_overlay, six_details = _collect_sixdim_overlay(
        skill_name, optimized_desc, expanded_kw, skill_type,
        existing_descriptions,
    )
    report.description_quality.update(quality_overlay)
    _merge_unique_recommendations(report, six_details)
    return report

from __future__ import annotations

import logging
import os
import re
from collections.abc import MutableMapping
from dataclasses import dataclass, field, replace
from typing import Any

from jwsgj.build_skill_md_quality import (
    _DESC_MIN_LENGTH,
    _as_keyword_list,
    _normalize_skill_dir,
    _read_skill_md_metadata,
    check_frontmatter_compliance,
)
from jwsgj.build_text_document import (
    BLOCK_SCALAR_INDICATORS,
    _desc_length,
    _restore_line_endings,
    normalize_str_list,
    truncate_description,
    word_pattern,
)
from jwsgj.build_text_frontmatter import (
    _field_line_numbers,
    _merge_indented_desc_keywords,
    _write_back_description,
    insert_frontmatter_description,
    replace_frontmatter_desc_keywords,
    split_frontmatter,
    split_frontmatter_document,
)
from jwsgj.build_text_scoring import (
    GRADE_BANDS_RATIO,
    band_to_grade,
    keyword_matches,
    score_to_grade,
)
from jwsgj.build_trigger_evaluate import (
    TriggerOptimizationResult,
    TriggerOptimizer,
    TriggerTestSuite,
)
from jwsgj.diag_types_normalize import text_or_empty
from jwsgj.diag_types_vocab import DESC_MAX, FIELD_RECOMMENDATIONS
from jwsgj.log_config import observation_gate
from jwsgj.skill_profile import is_scan_py_name

_log = logging.getLogger(__name__)
__all__ = [
    'BLOCK_SCALAR_INDICATORS',
    'BestPracticesReport',
    'DescriptionOptimizer',
    'attach_best_practices',
    'batch_optimize_descriptions',
    'diagnose_best_practices',
    'enforce_best_practices',
    'evaluate_description',
    'expand_skill_keywords',
    'merge_frontmatter_desc_keywords',
    'optimize_description',
    'run_trigger_test_gate',
    'truncate_keep_negative',
]
_DEFAULT_SKILL_TYPE = "generic"
_CN_VERB_PATTERN_SOURCE = {
    '调试|排查|诊断|troubleshoot': 'debug',
    '部署|发布|上线|release|publish': 'deploy',
    '搜索|检索|查找|query|lookup': 'search',
    '创建|新建|生成|build|make': 'create',
    '编辑|修改|更新|change|alter': 'edit',
    '删除|移除|清理|remove|clean': 'delete',
    '转换|转化|迁移|migrate|transform': 'convert',
    '分析|统计|aggregate|analyze': 'analyze',
    '监控|观察|babysit|watch': 'monitor',
    '检查|审查|校验|diag|review|inspect': 'check',
    '合并|整合|merge|integrate': 'merge',
    '发送|提交|submit|push|dispatch': 'send',
    '提取|抓取|crawl|scrape|fetch': 'extract',
    '备份|存档|archive|backup': 'backup',
    '还原|恢复|restore|recover': 'restore',
}
def _ascii_aware_verb_pattern(pattern: str) -> str:
    alternatives = []
    for part in pattern.split("|"):
        rendered = part
        if part.isascii() and part.isalpha():
            rendered = rf"(?<![A-Za-z0-9_]){part}(?![A-Za-z0-9_])"
        alternatives.append(rendered)
    return "|".join(alternatives)
CN_VERB_PATTERNS = {
    _ascii_aware_verb_pattern(pattern): replacement
    for pattern, replacement in _CN_VERB_PATTERN_SOURCE.items()
}
EN_VERB_MAP = {
    '\\btroubleshoot\\b': 'debug',
    '\\bdebugging\\b': 'debug',
    '\\bdeploying?\\b': 'deploy',
    '\\breleasing?\\b': 'deploy',
    '\\bgenerating?\\b': 'create',
    '\\bmodifying?\\b': 'edit',
    '\\bupdating?\\b': 'edit',
    '\\bcreating?\\b': 'create',
    '\\bremoving?\\b': 'delete',
    '\\btransforming?\\b': 'convert',
    '\\banalyzing?\\b': 'analyze',
    '\\bmonitoring?\\b': 'monitor',
    '\\breviewing?\\b': 'check',
    '\\binspecting?\\b': 'check',
    '\\bintegrating?\\b': 'merge',
    '\\bsubmitting?\\b': 'send',
    '\\bextracting?\\b': 'extract',
    '\\bbacking up\\b': 'backup',
    '\\brestoring?\\b': 'restore',
}
@dataclass
class DescriptionScore:
    original: str = ''
    word_count: int = 0
    score: float = 5.0
    grade: str = 'fair'
    issues: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
    optimized: str | None = None
    keyword_coverage: float = 0.0
    has_load_when: bool = False
    has_negative: bool = False
    attention_score: float = 0.0
    negative_defense_score: float = 0.0
def _analyze_issues(word_count: int, keywords: list, description: str) -> list[str]:
    issues: list[str] = []
    if word_count < 5:
        issues.append('描述过短，建议至少5个词（目标10词以上）')
    if word_count > 80:
        issues.append('描述过长，建议精简到50词以内')
    if keywords and not any(keyword_matches(str(kw), description.lower())
                            for kw in keywords):
        issues.append('描述中未包含任何关键词')
    return issues
_TRIGGER_SCENE_RE = re.compile(
    r"when|当(?!前).{1,40}?时|trigger|触发", re.IGNORECASE)
_NEGATIVE_DEFENSE_RE = re.compile(
    r"(?<![A-Za-z0-9_])not\s+for(?![A-Za-z0-9_])|不要(?:用于|使用)|不适用|"
    r"(?:^|[.!?。！？…]\s*)exclude\b",
    re.IGNORECASE | re.MULTILINE,
)
_NEGATIVE_TAIL_RE = re.compile(
    r"(?:(?<![A-Za-z0-9_])not\s+for(?![A-Za-z0-9_])\s*[:：]?|"
    r"不要(?:用于|使用)|不适用(?:于)?|"
    r"(?:^|(?<=[.!?。！？…])\s*)exclude\b\s*[:：]?)"
    r"[^。.!！?？…]*[。.!！?？…]?",
    re.IGNORECASE | re.MULTILINE,
)
def _has_trigger_scene(description: str) -> bool:
    positive_text = _NEGATIVE_TAIL_RE.sub("", description)
    return bool(_TRIGGER_SCENE_RE.search(positive_text))
def _score_label(score: float) -> str:
    if score >= 8:
        return 'excellent'
    if score >= 6:
        return 'good'
    if score >= 4:
        return 'fair'
    return 'poor'
class DescriptionOptimizer:
    def __init__(self) -> None:
        self._trigger_optimizer = TriggerOptimizer()
    def analyze(self, description: str,
                keywords: list[str] | None = None) -> DescriptionScore:
        description = text_or_empty(description)
        keywords = _as_keyword_list(keywords)
        trigger_result = self._trigger_optimizer.analyze(description, keywords)
        word_count = _count_description_words(description)
        optimized = _generate_optimized_description(description, trigger_result)
        issues = _analyze_issues(word_count, keywords, description)
        suggestions = list(trigger_result.suggestions)
        has_load_when = _has_trigger_scene(description)
        has_negative = bool(_NEGATIVE_DEFENSE_RE.search(description))
        score = trigger_result.overall_score
        grade = _score_label(score)
        return DescriptionScore(
            original=description,
            word_count=word_count,
            score=score,
            grade=grade,
            issues=issues,
            suggestions=suggestions,
            optimized=optimized,
            keyword_coverage=trigger_result.keyword_coverage,
            has_load_when=has_load_when,
            has_negative=has_negative,
            attention_score=trigger_result.attention_score,
            negative_defense_score=trigger_result.negative_defense_score,
        )
    def suggest_keywords(self, description: str) -> list[str]:
        base = self._trigger_optimizer.analyze(description).recommended_keywords
        return expand_skill_keywords(base)
def _count_description_words(text: str) -> int:
    chinese_chars = len(re.findall('[\\u4e00-\\u9fff]', text))
    if chinese_chars > 0:
        en_words = len(re.sub('[\\u4e00-\\u9fff]+', ' ', text).split())
        return int(chinese_chars / 1.5) + en_words
    return len(text.split())
_REDUNDANT_PREFIX_REWRITES: tuple[tuple[str, str], ...] = (
    ('这个技能用于', 'Use this when '),
    ('本技能用于', 'Use this when '),
    ('本技能可以', ''),
    ('这个技能可以', ''),
    ('This skill is used to', 'Use this when '),
    ('This skill can', ''),
    ('You can use this skill to', 'Use this when '),
)
def _apply_verb_rewrites(text: str, rules: dict, flags: int = 0) -> str:
    for pattern, replacement in rules.items():
        text = re.sub(pattern, replacement, text, flags=flags)
    return text
def _generate_optimized_description(description: str,
                                    trigger_result: TriggerOptimizationResult) -> str:
    optimized_desc = trigger_result.optimized_description
    if optimized_desc and len(optimized_desc) > 10:
        return optimized_desc.strip()
    optimized = _apply_verb_rewrites(description, CN_VERB_PATTERNS)
    optimized = _apply_verb_rewrites(optimized, EN_VERB_MAP, re.IGNORECASE)
    for pattern, replacement in _REDUNDANT_PREFIX_REWRITES:
        optimized, replaced = re.subn(
            r"^\s*" + pattern, replacement, optimized,
            count=1, flags=re.IGNORECASE)
        if replaced:
            break
    return optimized.strip()
_RE_CN_RUN = re.compile(r'[\u4e00-\u9fff]+')
def _overlap_tokens(text: str) -> list[str]:
    tokens: list[str] = []
    for part in text.lower().split():
        pos = 0
        for m in _RE_CN_RUN.finditer(part):
            if m.start() > pos:
                tokens.append(part[pos:m.start()])
            run = m.group()
            if len(run) >= 2:
                tokens.extend(run[i:i + 2] for i in range(len(run) - 1))
            else:
                tokens.append(run)
            pos = m.end()
        if pos < len(part):
            tokens.append(part[pos:])
    return tokens
_VAGUE_WORDS: tuple[str, ...] = (
    "好的", "优秀的", "强大的", "全面的", "专业的", "高效",
    "nice", "good", "great", "powerful", "comprehensive",
)
def _vague_word_pattern(word: str) -> re.Pattern[str] | None:
    if not word.isascii():
        return None
    return re.compile(word_pattern(word), re.IGNORECASE)
def _contains_vague_word(word: str, text_lower: str) -> bool:
    pattern = _vague_word_pattern(word)
    return bool(pattern.search(text_lower)) if pattern else word in text_lower
def _vague_penalty(desc_lower: str, issues: list[str]) -> tuple[float, list[str]]:
    vague_found = [w for w in _VAGUE_WORDS if _contains_vague_word(w, desc_lower)]
    if vague_found:
        issues.append(f"包含空泛词: {vague_found}")
        return 15.0, vague_found
    return 0.0, []
def _resolve_existing_descs(existing_descs: Any) -> list[str]:
    return [d if isinstance(d, str) else str(d)
            for d in _as_keyword_list(existing_descs) if d]
def _is_heavy_overlap(desc_word_set: set[str], other: str) -> bool:
    if not desc_word_set:
        return False
    overlap = len(desc_word_set & set(_overlap_tokens(other)))
    return overlap > len(desc_word_set) * 0.7
def _overlap_penalty(description: str,
                     existing_descs: Any, issues: list[str]) -> float:
    candidates = _resolve_existing_descs(existing_descs)
    if not candidates:
        return 0.0
    desc_word_set = set(_overlap_tokens(description))
    for other in candidates:
        if _is_heavy_overlap(desc_word_set, other):
            issues.append("与其他技能 description 高度重叠")
            return 15.0
    return 0.0
def _length_penalty(description: str, issues: list[str]) -> float:
    penalty = 0.0
    length = _desc_length(description)
    if length < _DESC_MIN_LENGTH:
        issues.append(f"description 过短（<{_DESC_MIN_LENGTH}字符），无法有效触发")
        penalty += 40
    if length > DESC_MAX:
        issues.append(f"description 过长（>{DESC_MAX}字符），可能被截断")
        penalty += 10
    return penalty
def _has_skill_name_mention(description: str, skill_name: str) -> bool:
    if not skill_name:
        return False
    if skill_name.isascii():
        return keyword_matches(skill_name, description.lower())
    return skill_name.casefold() in description.casefold()
def evaluate_description(description: str, skill_name: str = "",
                         existing_descs: Any = None) -> dict[str, Any]:
    issues: list[str] = []
    score = 100.0
    description = text_or_empty(description)
    skill_name = text_or_empty(skill_name)
    score -= _length_penalty(description, issues)
    desc_lower = description.lower()
    _pen, vague_found = _vague_penalty(desc_lower, issues)
    score -= _pen
    if not _has_trigger_scene(description):
        issues.append("缺少触发场景描述（建议以'当用户...'开头）")
        score -= 10
    if (skill_name and
            not _has_skill_name_mention(description, skill_name)):
        issues.append(f"技能名 '{skill_name}' 未在 description 中出现")
        score -= 5
    score -= _overlap_penalty(description, existing_descs, issues)
    return {
        "score": max(0, score),
        "issues": issues,
        "suggestions": [f"修复: {issue}" for issue in issues],
        "length": _desc_length(description),
        "vague_words": vague_found,
    }
_CJK_TEXT_RE = re.compile(r"[\u4e00-\u9fff]")
_LATIN_LETTER_RE = re.compile(r"[A-Za-z]")
def _is_latin_text(text: str) -> bool:
    return bool(_LATIN_LETTER_RE.search(text)) and not _CJK_TEXT_RE.search(text)
def optimize_description(skill_name: str, description: str,
                         keywords: list[str] | None = None,
                         skill_type: str = _DEFAULT_SKILL_TYPE) -> str:
    description = text_or_empty(description)
    skill_name = text_or_empty(skill_name)
    keywords = _as_keyword_list(keywords)
    if not description:
        description = (
            f"Use this skill when the user needs {skill_name} capabilities."
            if _is_latin_text(skill_name)
            else f"当用户需要{skill_name}相关功能时使用本技能"
        )
    latin = _is_latin_text(description)
    description = _ensure_trigger_lead(_strip_vague(description), skill_name,
                                       latin=latin)
    base = description
    for _ in range(3):
        description = _ensure_skill_name_mention(base, skill_name, latin=latin)
        description = _weave_trigger_keywords(description, keywords, latin=latin)
        description = _append_exclusion(description, skill_type, latin=latin)
        if len(description) <= DESC_MAX:
            return description
        enrichment = max(0, len(description) - len(base))
        shortened = truncate_keep_negative(
            base, max(1, DESC_MAX - enrichment), ellipsis_cut=True)
        if shortened == base:
            break
        base = shortened
    return truncate_keep_negative(description, DESC_MAX,
                                   ellipsis_cut=True)
def _ensure_trigger_lead(description: str, skill_name: str,
                         *, latin: bool = False) -> str:
    if _has_trigger_scene(description):
        return description
    if latin:
        target = f" {skill_name}" if skill_name else " the declared"
        return (f"Use this skill when the user needs{target} capabilities. "
                f"{description}")
    return f"当用户需要{skill_name}功能时使用本技能。{description}"
def _ensure_skill_name_mention(description: str, skill_name: str,
                               *, latin: bool = False) -> str:
    if (skill_name and
            not _has_skill_name_mention(description, skill_name)):
        if latin:
            return f"{description} ({skill_name})"
        return f"{description}（{skill_name}）"
    return description
def _fit_with_ellipsis(text: str, limit: int) -> str:
    if limit <= 0:
        return ""
    if len(text) <= limit:
        return text
    if limit <= 3:
        return text[:limit]
    return text[:limit - 3] + "..."
def _truncate_for_language(text: str, limit: int) -> str:
    terminal = "." if _is_latin_text(text) else "。"
    return truncate_description(text, limit, terminal, clamp_within_limit=True)
_PUNCTUATION_ONLY_STRIP = "。！？….!?，、；： \t"
def _has_readable_content(text: str) -> bool:
    return bool(text.strip(_PUNCTUATION_ONLY_STRIP))
def _truncate_content(text: str, limit: int, ellipsis_cut: bool) -> str:
    truncated = (_fit_with_ellipsis(text, limit) if ellipsis_cut
                 else _truncate_for_language(text, limit))
    return truncated if _has_readable_content(truncated) else ""
def truncate_keep_negative(description: str, limit: int,
                            *, ellipsis_cut: bool = False) -> str:
    if limit <= 0:
        return ""
    if len(description) <= limit:
        return description
    matches = list(_NEGATIVE_TAIL_RE.finditer(description))
    if not matches:
        return _truncate_content(description, limit, ellipsis_cut)
    match = matches[-1]
    tail = match.group(0).strip()
    head = description[:match.start()].rstrip()
    if len(tail) >= limit:
        truncated_tail = _truncate_content(tail, limit, ellipsis_cut)
        if _has_readable_content(head):
            head = _truncate_content(
                head, max(1, limit // 2 - 2), ellipsis_cut)
            tail_budget = limit - len(head) - 2
            if _has_readable_content(head) and tail_budget > 0:
                shortened_tail = _truncate_content(
                    tail, tail_budget, ellipsis_cut)
                if _has_readable_content(shortened_tail):
                    return _append_sentence(
                        head, shortened_tail, latin=_is_latin_text(head))
        return truncated_tail
    head_budget = limit - len(tail) - 2
    head = (_truncate_content(head, head_budget, ellipsis_cut)
            if head and head_budget > 0 else "")
    if not _has_readable_content(head):
        return tail
    return _append_sentence(head, tail, latin=_is_latin_text(head))
_CN_LIST_SEPARATORS = "、，,"
_CN_ATTRIBUTIVE_PARTICLES = "的地得"
_DANGLING_SEPARATOR_RE = re.compile(r"[、，,]\s*(?=[、，,。；;])")
_LEADING_SEPARATOR_RE = re.compile(r"^[、，,。；;\s]+")
def _vague_word_regex(word: str) -> re.Pattern[str]:
    pattern = _vague_word_pattern(word)
    return pattern or re.compile(re.escape(word))
def _strip_vague(description: str) -> str:
    for word in _VAGUE_WORDS:
        pattern = _vague_word_regex(word)
        description = re.sub(
            rf"(?:{pattern.pattern})[{_CN_LIST_SEPARATORS}]*\s*"
            rf"[{_CN_ATTRIBUTIVE_PARTICLES}]?",
            "", description, flags=pattern.flags)
    description = _DANGLING_SEPARATOR_RE.sub("", description)
    description = _LEADING_SEPARATOR_RE.sub("", description)
    return re.sub(r" {2,}", " ", description).strip()
_CJK_SENTENCE_END_CHARS = ("。", "！", "？", "…")
_LATIN_SENTENCE_END_CHARS = (".", "!", "?")
def _append_sentence(description: str, sentence: str,
                     *, latin: bool = False) -> str:
    if description.endswith(_LATIN_SENTENCE_END_CHARS):
        return description + " " + sentence
    if description.endswith(_CJK_SENTENCE_END_CHARS):
        return description + sentence
    return description + (". " if latin else "。") + sentence
def _weave_trigger_keywords(description: str, keywords: list,
                            *, latin: bool = False) -> str:
    if keywords:
        _extra = [str(k) for k in keywords
                  if k and not keyword_matches(str(k), description.lower())][:3]
        if _extra:
            keywords_latin = latin and not any(
                _CJK_TEXT_RE.search(k) for k in _extra)
            label = "Trigger keywords" if keywords_latin else "触发关键词"
            sep = ", " if keywords_latin else "、"
            colon = ": " if keywords_latin else "："
            description = _append_sentence(
                description, f"{label}{colon}{sep.join(_extra)}",
                latin=latin)
    return description
def _append_exclusion(description: str, skill_type: str,
                      *, latin: bool = False) -> str:
    if not _NEGATIVE_DEFENSE_RE.search(description):
        if latin:
            scope = (f"tasks unrelated to {skill_type}"
                     if skill_type and skill_type != _DEFAULT_SKILL_TYPE
                     else "tasks unrelated to the declared capability scope")
            description = _append_sentence(
                description, f"Not for {scope}.", latin=True)
        elif skill_type and skill_type != _DEFAULT_SKILL_TYPE:
            description = _append_sentence(
                description, f"不适用于与{skill_type}无关的任务。")
        else:
            description = _append_sentence(
                description, "不适用于与声明的能力范围无关的任务。")
    return description
def _normalize_expand_input(base_keywords: list) -> list:
    return [k.strip() for k in _as_keyword_list(base_keywords)
            if isinstance(k, str) and k.strip()]
_KEYWORD_EN_MAP = {
    "创建": "create", "诊断": "diag", "重构": "refactor",
    "优化": "optimize", "清理": "cleanup", "进化": "evolve",
    "扫描": "scan", "检测": "detect", "修复": "fix",
}
_KEYWORD_COLLOQUIAL_MAP = {
    "诊断": "帮我审查", "重构": "帮我重构", "清理": "帮我清理",
    "优化": "帮我优化", "创建": "帮我创建",
    "create": "help me create", "diag": "help me diagnose",
    "diagnose": "help me diagnose", "refactor": "help me refactor",
    "cleanup": "help me clean up", "optimize": "help me optimize",
}
def expand_skill_keywords(base_keywords: list, skill_name: str = "") -> list:
    base_keywords = _normalize_expand_input(base_keywords)
    expanded = list(base_keywords)
    for kw in expanded[:]:
        if kw in _KEYWORD_EN_MAP:
            expanded.append(_KEYWORD_EN_MAP[kw])
        if kw in _KEYWORD_COLLOQUIAL_MAP:
            expanded.append(_KEYWORD_COLLOQUIAL_MAP[kw])
    if skill_name:
        expanded.append(str(skill_name))
    return list(dict.fromkeys(kw for kw in expanded if kw))
def batch_optimize_descriptions(skills: dict[str, str]) -> list[dict]:
    optimizer = DescriptionOptimizer()
    results = []
    if not isinstance(skills, dict):
        skills = {}
    for name, desc in skills.items():
        result = optimizer.analyze(desc)
        results.append({
            "name": name,
            "original": desc,
            "word_count": result.word_count,
            "score": result.score,
            "grade": result.grade,
            "optimized": result.optimized,
            "issues": result.issues,
            "suggestions": result.suggestions,
        })
    results.sort(key=lambda r: r["score"])
    return results
def _description_field_presence(text: str) -> bool | None:
    split = split_frontmatter_document(text)
    if split is None:
        return None
    parts = split_frontmatter(split[0])
    if len(parts) < 3:
        return None
    return bool(_field_line_numbers(parts[1].split("\n"), "description"))
def merge_frontmatter_desc_keywords(text: str, opt: Any,
                                     md_label: str = "") -> str | None:
    description = getattr(opt, "optimized_description", None)
    if not (isinstance(description, str) and description.strip()):
        description = None
    keywords = normalize_str_list(getattr(opt, "optimized_keywords", None))
    if description is None and not keywords:
        return None
    merged_indented, indented_seen = _merge_indented_desc_keywords(
        text, description, keywords, md_label)
    if indented_seen:
        return merged_indented
    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    status: dict[str, Any] = {}
    merged = replace_frontmatter_desc_keywords(
        normalized, description, keywords,
        md_label=md_label, status_out=status)
    if (description is not None and not status.get("desc_written")
            and _description_field_presence(normalized) is False):
        inserted = insert_frontmatter_description(merged, description)
        status["desc_written"] = inserted != merged
        merged = inserted
    if merged == normalized:
        return None
    if not (status.get("desc_written") or status.get("keywords_written")):
        return None
    return _restore_line_endings(text, merged)
@dataclass
class BestPracticesReport:
    skill_dir: str
    skill_name: str = ""
    description: str = ""
    overall_score: float = 0.0
    overall_grade: str = "F"
    description_quality: dict[str, Any] = field(default_factory=dict)
    frontmatter_compliance: dict[str, Any] = field(default_factory=dict)
    script_quality: list[dict[str, Any]] = field(default_factory=list)
    all_issues: list[str] = field(default_factory=list)
    auto_fixed: list[str] = field(default_factory=list)
    irreparable: list[str] = field(default_factory=list)
    recommendations: list[str] = field(default_factory=list)
@dataclass(frozen=True)
class _FrontmatterFields:
    skill_name: str
    description: str
    keywords: list[str] | None
    version: str
def _record_description_quality(report: BestPracticesReport,
                                desc_eval: dict[str, Any]) -> float:
    desc_score = desc_eval["score"]
    report.description_quality = {
        "score": desc_score, "grade": score_to_grade(desc_score),
        "length": desc_eval["length"],
        "vague_words": desc_eval["vague_words"],
        "issues": desc_eval["issues"],
    }
    return desc_score
def _enforce_description(report: BestPracticesReport, fm: _FrontmatterFields,
                         skill_dir: str,
                         auto_fix: bool) -> tuple[float, _FrontmatterFields]:
    description = fm.description
    desc_eval = evaluate_description(description, fm.skill_name)
    desc_score = _record_description_quality(report, desc_eval)
    desc_grade = score_to_grade(desc_score)
    low_quality = desc_grade in ("D", "F")
    length_invalid = not _DESC_MIN_LENGTH <= desc_eval["length"] <= DESC_MAX
    repair_reason = "质量低" if low_quality else "长度不合规"
    if low_quality or length_invalid:
        if auto_fix:
            optimized = optimize_description(fm.skill_name, description,
                                             fm.keywords)
            if skill_dir and _write_back_description(
                skill_dir, optimized):
                report.auto_fixed.append(
                    f"description: 已写回优化结果 (grade={desc_grade})")
                effective = _read_skill_md_metadata(skill_dir)["description"]
                description = effective or optimized
                desc_eval = evaluate_description(description, fm.skill_name)
                desc_score = _record_description_quality(report, desc_eval)
                desc_grade = score_to_grade(desc_score)
                if desc_grade in ("D", "F"):
                    report.irreparable.append(
                        f"description写回后质量仍低(grade={desc_grade})")
                elif not _DESC_MIN_LENGTH <= desc_eval["length"] <= DESC_MAX:
                    report.irreparable.append(
                        "description写回后长度仍不合规"
                        f"(length={desc_eval['length']})")
            else:
                recommendation_prefix = (
                    "description: " if low_quality
                    else "description: 长度不合规，"
                )
                report.recommendations.append(
                    f"{recommendation_prefix}优化结果未写回(grade={desc_grade})，"
                    f"建议替换为: {optimized[:100]}...")
                report.irreparable.append(
                    f"description{repair_reason}且优化结果未写回(grade={desc_grade})")
        else:
            unfixed_reason = "质量过低" if low_quality else repair_reason
            report.irreparable.append(
                f"description{unfixed_reason}(grade={desc_grade})")
    report.all_issues.extend(desc_eval["issues"])
    return desc_score, replace(fm, description=description)
def _enforce_frontmatter(report: BestPracticesReport, skill_dir: str,
                         fm: _FrontmatterFields) -> float:
    fm_report = check_frontmatter_compliance(
        skill_dir, fm.skill_name, fm.description, fm.keywords, fm.version
    )
    report.frontmatter_compliance = {
        "score": fm_report.total_score, "grade": fm_report.grade,
        "name_valid": fm_report.name_valid,
        "description_valid": fm_report.description_valid,
        "skill_md_lines": fm_report.skill_md_lines,
        "skill_md_ok": fm_report.skill_md_ok,
        "keywords_count": fm_report.keywords_count,
        "issues": fm_report.all_issues,
        FIELD_RECOMMENDATIONS: fm_report.recommendations,
    }
    blocking = fm_report.all_issues
    if blocking:
        if fm_report.recommendations:
            report.recommendations.append(
                f"frontmatter: 硬校验未通过(grade={fm_report.grade})，"
                f"建议按下列建议修复")
            report.recommendations.extend(fm_report.recommendations)
        report.irreparable.append(
            f"frontmatter合规性校验未通过(grade={fm_report.grade}): "
            + "；".join(str(issue) for issue in blocking[:3]))
    elif fm_report.advisories:
        report.recommendations.extend(
            f"建议: {advice}" for advice in fm_report.advisories)
    report.all_issues.extend(blocking)
    report.all_issues.extend(fm_report.advisories)
    return fm_report.total_score
def _check_one_script(sp: str, f: str,
                      report: BestPracticesReport) -> dict[str, Any] | None:
    from jwsgj.build_script_compliance import (  # lazy-by-design
        CLIBestPracticesEngine,
        read_script_text,
    )
    try:
        content = read_script_text(sp, lenient=True)
    except (OSError, ValueError) as e:
        _log.warning("[best_practices] 脚本读取失败: %s: %s", f, e)
        issue = f"脚本 {f} 读取失败: {e}"
        report.all_issues.append(issue)
        report.irreparable.append(issue)
        return None
    cli_r = CLIBestPracticesEngine.check_cli_compliance(sp, content=content)
    scr_r = CLIBestPracticesEngine.check_script_compliance(sp, content=content)
    report.all_issues.extend(cli_r.recommendations)
    report.all_issues.extend(scr_r.recommendations)
    if cli_r.grade in ("D", "F") or scr_r.grade in ("D", "F"):
        report.recommendations.append(
            f"脚本 {f}: 合规性低(cli={cli_r.grade}, "
            f"script={scr_r.grade})，建议修复")
        report.irreparable.append(
            f"脚本 {f} 合规性低(cli={cli_r.grade}, "
            f"script={scr_r.grade})")
    return {
        "file": f,
        "cli_score": cli_r.total_score, "cli_grade": cli_r.grade,
        "cli_passed": cli_r.passed, "cli_failed": cli_r.failed,
        "script_score": scr_r.total_score, "script_grade": scr_r.grade,
        "script_passed": scr_r.passed, "script_failed": scr_r.failed,
        FIELD_RECOMMENDATIONS: cli_r.recommendations + scr_r.recommendations,
    }
def _enforce_scripts(report: BestPracticesReport, skill_dir: str) -> None:
    if not skill_dir:
        _log.warning("[best_practices] skill_dir 空白，跳过 scripts 扫描（禁止落到进程工作目录）")
        return
    scripts_dir = os.path.join(skill_dir, "scripts")
    if not os.path.isdir(scripts_dir):
        return
    try:
        script_files = sorted(os.listdir(scripts_dir))
    except OSError as e:
        _log.warning("[best_practices] 列举 scripts 目录失败: %s", e)
        issue = f"scripts 目录列举失败: {e}"
        report.all_issues.append(issue)
        report.irreparable.append(issue)
        return
    for f in script_files:
        script_path = os.path.join(scripts_dir, f)
        if not is_scan_py_name(f) or not os.path.isfile(script_path):
            continue
        entry = _check_one_script(script_path, f, report)
        if entry is not None:
            report.script_quality.append(entry)
def _compute_overall_grade(report: BestPracticesReport, desc_score: float,
                          fm_score: float) -> None:
    scores = [desc_score / 100.0, fm_score / 100.0]
    if report.script_quality:
        avg_script = sum(
            s["cli_score"] + s["script_score"] for s in report.script_quality
        ) / (len(report.script_quality) * 2)
        scores.append(avg_script / 100.0)
    report.overall_score = round(sum(scores) / len(scores), 2)
    report.overall_grade = band_to_grade(report.overall_score, GRADE_BANDS_RATIO)
def _resolve_enforce_inputs(skill_dir: str, skill_name: str,
                            description: str, keywords: list[str] | None,
                            version: str) -> tuple[str, str, list[str] | None, str]:
    meta = _read_skill_md_metadata(skill_dir)
    if not skill_name:
        skill_name = meta["name"]
    if not description:
        description = meta["description"]
    if keywords is None and meta["keywords"]:
        keywords = meta["keywords"]
    if not version:
        version = meta["version"]
    return skill_name, description, keywords, version
def diagnose_best_practices(skill_dir: str) -> dict:
    bp_report, bp_passed = enforce_best_practices(skill_dir, auto_fix=False)
    return {
        "passed": bp_passed,
        "overall_score": bp_report.overall_score,
        "overall_grade": bp_report.overall_grade,
        "auto_fixed": bp_report.auto_fixed,
        "irreparable": bp_report.irreparable,
        FIELD_RECOMMENDATIONS: bp_report.recommendations,
    }
def attach_best_practices(result: dict, skill_dir: str) -> None:
    if not isinstance(result, MutableMapping):
        raise TypeError(
            "attach_best_practices 需要可变映射结果包，实际 "
            f"{type(result).__name__}")
    try:
        result["best_practices"] = diagnose_best_practices(skill_dir)
    except Exception as e:  # noqa: BLE001
        _log.warning("best_practices 检测失败: %s", e)
        result["best_practices"] = {"error": str(e)}
def _reject_invalid_skill_dir(skill_dir: object, skill_name: str,
                              reason: str = "") -> tuple[BestPracticesReport, bool]:
    issue = reason or ("技能目录参数非法或空白: " + repr(skill_dir)[:200])
    _log.warning("enforce_best_practices %s，拒绝读取文件系统", issue)
    report = BestPracticesReport(skill_dir="", skill_name=text_or_empty(skill_name))
    report.all_issues.append(issue)
    report.irreparable.append(issue)
    report.recommendations.append(f"修复: {issue}")
    return report, False
def enforce_best_practices(skill_dir: str, skill_name: str = "",
                           description: str = "",
                           keywords: list[str] | None = None,
                           version: str = "",
                           auto_fix: bool = True) -> tuple[BestPracticesReport, bool]:
    normalized_dir = _normalize_skill_dir(skill_dir)
    if not normalized_dir:
        return _reject_invalid_skill_dir(skill_dir, skill_name)
    if not os.path.isdir(normalized_dir):
        return _reject_invalid_skill_dir(
            skill_dir, skill_name,
            reason=f"技能目录不存在或不是目录: {normalized_dir}")
    skill_dir = normalized_dir
    skill_name, description, keywords, version = _resolve_enforce_inputs(
        skill_dir, skill_name, description, keywords, version)
    fm = _FrontmatterFields(skill_name=skill_name, description=description,
                            keywords=keywords, version=version)
    report = BestPracticesReport(skill_dir=str(skill_dir), skill_name=skill_name)
    desc_score, fm = _enforce_description(report, fm, skill_dir, auto_fix)
    report.description = fm.description or ""
    fm_score = _enforce_frontmatter(report, skill_dir, fm)
    _enforce_scripts(report, skill_dir)
    _compute_overall_grade(report, desc_score, fm_score)
    all_passed = len(report.irreparable) == 0
    if not all_passed:
        report.recommendations.append(
            f"存在 {len(report.irreparable)} 个不可修复的违规，操作被阻断"
        )
    _log.info("enforce_best_practices: %s 全部通过=%s",
              report.skill_name, all_passed)
    return report, all_passed
@observation_gate("trigger test")
def run_trigger_test_gate(name: str, description: str, keywords: list) -> None:
    tr = TriggerTestSuite().run(name, description, keywords)
    _log.info(
        "[init] 触发测试: accuracy=%.2f precision=%.2f recall=%.2f 建议%d条",
        tr.accuracy, tr.precision, tr.recall, len(tr.recommendations))

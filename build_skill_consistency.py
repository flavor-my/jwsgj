from __future__ import annotations

import logging
import math
import os
import re
from dataclasses import dataclass, field
from difflib import SequenceMatcher
from itertools import combinations
from pathlib import Path
from typing import Any, ClassVar

from jwsgj.build_skill_md_optimize import (
    merge_frontmatter_desc_keywords,
    truncate_keep_negative,
)
from jwsgj.build_skill_md_quality import validate_create_input
from jwsgj.build_text_document import (
    CORE_ACTION_VERBS,
    DESCRIPTION_MAX_LEN,
    SKILL_ACTION_VERBS,
    contains_term,
    find_first_sentence_period,
    has_cjk,
    jaccard,
    normalize_str,
    normalize_str_list,
    resolve_entry_document,
    tokenize_words,
    truncate_description,
    word_pattern,
    write_markdown_text,
)
from jwsgj.build_text_frontmatter import (
    DEFAULT_SKILL_VERSION,
    frontmatter_keywords,
    normalize_description_field,
    parse_frontmatter_dict,
)
from jwsgj.build_text_scoring import (
    CN_EXCLUSION_HEADS,
    NEGATION_PATTERNS,
    VERB_SYNONYM_EXPANSION,
    extract_negated_terms,
    keyword_matches,
    stem_matches,
)
from jwsgj.build_trigger_activation import (
    get_calibrator,
)
from jwsgj.build_trigger_evaluate import (
    DOMAIN_TRIGGER_PATTERNS,
    SemanticConsistencyReport,
    SemanticConsistencyValidator,
    TriggerOptimizer,
    TriggerTestSuite,
    TriggerTestSuiteResult,
    normalize_root_str,
    scan_skill_descriptions,
)
from jwsgj.skill_doc_render import generate_matching_description

_log = logging.getLogger(__name__)
__all__ = [
    'ATTENTION_DILUTERS',
    'ATTENTION_ESCAPE_PATTERNS',
    'ATTENTION_SEGMENT_WEIGHTS',
    'COLLOQUIAL_PREFIXES',
    'COLLOQUIAL_SUFFIXES',
    'NOUN_NORMALIZATION',
    'PICKING_CUES',
    'VERB_NORMALIZATION',
    'AttentionSegment',
    'AttentionSegmentOptimizer',
    'AttentionSegmentReport',
    'CrossSkillOverlapDetector',
    'CrossSkillOverlapResult',
    'MatchingConflictDetector',
    'MetadataOptimizationResult',
    'OverlapReport',
    'QueryRewriter',
    'RewriteResult',
    'SemanticMatchResult',
    'SemanticMatcher',
    'SkillFrontmatter',
    'SkillMetadataOptimizer',
    'SkillSemanticIndex',
    'apply_frontmatter_fix',
    'assess_description_generation',
    'build_creation_semantic_index',
    'detect_skill_overlaps',
    'generate_optimized_frontmatter',
    'get_conflict_detector',
    'get_rewriter',
    'quick_match_skills',
    'suggest_pair_resolution',
    'validate_creation_inputs',
    'validate_semantic_consistency',
]
_HIGH_RISK_OVERLAP_THRESHOLD = 0.6
_TRIGGER_OVERLAP_MIN = 0.3
_SEMANTIC_OVERLAP_MIN = 0.5
_FUNCTIONAL_OVERLAP_MIN = 0.4
_TRIGGER_VERBS: tuple[str, ...] = tuple(sorted(SKILL_ACTION_VERBS))
_GENERIC_USAGE_PREFIX = (
    "Use this skill when the user needs to perform the related task. ")
_MUST_CALL_CUE = (
    "MUST call this skill when matching the trigger conditions.")
_PRESENTATION_FRAME_RES: tuple[tuple[re.Pattern[str], str], ...] = (
    (re.compile(r"(?is)(?:trigger|use) this skill when the user "
                r"(?:asks|needs) to\s+(?:work with\s+)?(.+?)(?:[.。]|$)"), r"\1"),
    (re.compile(r"(?is)use this skill (?:to|for)\s+"), " "),
    (re.compile(r"(?is)trigger this skill when the user needs the "
                r"related task[.。]?"), " "),
    (re.compile(r"当用户要求(.+?)时触发此技能[。.]?"), r"\1 "),
    (re.compile(r"当用户需要相关任务时触发此技能[。.]?"), " "),
    (re.compile(r"当用户需要(.{1,80}?)时使用[本此]技能[。.]?"), r"\1 "),
    (re.compile(r"包括[：:]"), " "),
)
_GENERATED_DESC_TRIGGER_RE = re.compile(
    r"\[MUST USE\]\s*当用户需要(?:执行|处理).{0,80}?时使用本技能。")
_GENERATED_DESC_MARKERS: tuple[str, ...] = ("口语化表达：", "适用角色：")
_GENERATED_CAP_RE = re.compile(r"核心能力：(.+?)。")
_GENERATED_SCENE_RE = re.compile(r"适用于：(.+?)(?:等场景|类任务)?。")
_NEGATIVE_SCOPE_RE = re.compile(
    r"(?i)(?:\bNOT\s+for\b|\bDO\s+NOT\b|\bNEVER\b|不要用于|不适用于)"
    r"(?:(?![。!！?？；\r\n]|\.(?=\s|$)).)*")
_NEGATED_REQUIREMENT_RE = re.compile(
    r"(?i)\b(?:not|never)\s+(?:(?:always|necessarily)\s+)?"
    r"(?:must|always|required)\b")
_NEGATION_MASK_PATTERNS = (
    *NEGATION_PATTERNS,
    _NEGATIVE_SCOPE_RE.pattern,
    _NEGATED_REQUIREMENT_RE.pattern,
)
def _capability_text(text: str) -> str:
    content = normalize_str(text)
    if not content:
        return ""
    if (any(marker in content for marker in _GENERATED_DESC_MARKERS)
            and _GENERATED_DESC_TRIGGER_RE.search(content)):
        capability = (_GENERATED_CAP_RE.search(content)
                      or _GENERATED_SCENE_RE.search(content))
        content = capability.group(1).strip() if capability else ""
    else:
        content = content.replace(_GENERIC_USAGE_PREFIX, " ")
        content = content.replace(_MUST_CALL_CUE, " ")
        for pattern, replacement in _PRESENTATION_FRAME_RES:
            content = pattern.sub(replacement, content)
    content = _mask_negated_context(content)
    return re.sub(r"\s+", " ", content).strip(" .。;；,，")
_TRIGGER_NOISE: frozenset[str] = frozenset({
    "a", "an", "the", "this", "that", "these", "those",
    "it", "its", "is", "are", "be", "by", "for", "from",
    "in", "on", "of", "or", "and", "as", "at", "to",
    "with", "when", "if", "then", "than", "you", "your",
    "we", "our", "they", "their", "i", "me", "my",
    "please", "help", "use", "using", "used", "call",
    "calls", "called", "must", "always", "required",
    "trigger", "triggers", "triggered", "skill", "skills",
    "user", "users", "need", "needs", "ask", "asks",
    "task", "tasks", "related", "perform", "matching",
    "match", "condition", "conditions", "not", "never", "no",
    "此技能", "本技能", "技能", "用户", "任务", "相关任务",
    "相关", "触发", "使用", "调用", "加载", "当", "时",
    "场景", "情形", "情况",
    "当用户", "当用户需要", "当用户要求", "当用户需要执行",
    "当用户需要处理", "用户需要", "使用本技能",
    "需要", "要求", "不", "不要", "不要用于", "不适用于",
    "与", "声明", "范围", "无关",
})
_MUST_CUE_ALT: str = "|".join(
    word_pattern(w) for w in ("MUST", "ALWAYS", "REQUIRED", "TRIGGER"))
_CJK_SKILL_USE_VERB = r"(?:使用|调用|加载|激活|采用|应用)(?:此|本)技能"
_TRIGGER_PREFIX_PRESENT_RE = re.compile(
    r"^(?:(?:Trigger|Use|Using|Call|Activate|Invoke)\s+"
    r"(?:(?:this|the)\s+skill\b|this\s+(?:when|if|for|to)\b"
    r"|when\b|if\b|for\b|to\b)"
    r"|(?:MUST|ALWAYS)\b"
    r"|\[MUST USE\]"
    r"|This\s+skill\s+(?:should\s+be\s+used|is\s+used|must\s+be\s+used)\b"
    r"|When\s+the\s+user\b"
    r"|(?:必须|需要)?\s*" + _CJK_SKILL_USE_VERB +
    r"|当用户(?:要求|需要)[^。]{1,200}时[，,]?\s*(?:请)?"
    r"(?:触发此技能|" + _CJK_SKILL_USE_VERB + r"))",
    re.IGNORECASE,
)
@dataclass
class SkillFrontmatter:
    name: str
    description: str
    keywords: list[str]
    category: str = ""
    depends_on: list[str] = field(default_factory=list)
    def __post_init__(self) -> None:
        self.name = normalize_str(self.name).strip()
        self.description = normalize_str(self.description)
        self.keywords = normalize_str_list(self.keywords)
        self.category = normalize_str(self.category)
        self.depends_on = normalize_str_list(self.depends_on)
    @classmethod
    def from_metadata(cls, item: dict) -> SkillFrontmatter | None:
        if not isinstance(item, dict):
            return None
        name = normalize_str(item.get('name')).strip()
        if not name:
            return None
        return cls(
            name=name,
            description=normalize_str(item.get('description')),
            keywords=normalize_str_list(item.get('keywords')),
            category=normalize_str(item.get('category')),
            depends_on=normalize_str_list(item.get('depends_on')),
        )
@dataclass
class OverlapReport:
    pair: tuple[str, str] = ("", "")
    overlap_type: str = ""
    overlap_score: float = 0.0
    shared_triggers: list[str] = field(default_factory=list)
    conflict_description: str = ""
    resolution: str = ""
@dataclass
class CrossSkillOverlapResult:
    total_skills: int = 0
    overlapping_pairs: list[OverlapReport] = field(default_factory=list)
    isolated_skills: list[str] = field(default_factory=list)
    resolution_plan: list[str] = field(default_factory=list)
    summary: str = ""
def _normalize_sequence_input(value, label: str) -> list[Any] | None:
    if value is None:
        return None
    if isinstance(value, (str, bytes, bytearray)):
        _log.warning('%s 为字符串形态，不按序列拆分，已归空', label)
        return None
    if isinstance(value, dict):
        _log.warning('%s 为映射形态，键不得当作序列项，已归空', label)
        return None
    if isinstance(value, (set, frozenset)):
        items = sorted(value, key=lambda item: (type(item).__name__, str(item)))
        _log.info('%s 为无序集合，已按稳定键排序', label)
        return items
    try:
        return list(value)
    except TypeError:
        _log.warning('%s 类型 %s 非法，已归空', label, type(value).__name__)
        return None
def _skill_sequence(payload: object, label: str) -> list[SkillFrontmatter]:
    raw_items = _normalize_sequence_input(payload, label)
    if raw_items is None:
        return []
    valid_items = [item for item in raw_items if isinstance(item, SkillFrontmatter)]
    if len(valid_items) != len(raw_items):
        _log.warning('%s 跳过 %d 个非 SkillFrontmatter 载荷项',
                     label, len(raw_items) - len(valid_items))
    return valid_items
class CrossSkillOverlapDetector:
    def __init__(self) -> None:
        self._skills: list[SkillFrontmatter] = []
    def register_skill(self, skill: SkillFrontmatter) -> None:
        if not isinstance(skill, SkillFrontmatter):
            _log.warning('register_skill 拒绝非 SkillFrontmatter 入参: %r', skill)
            return
        if any(s.name == skill.name for s in self._skills):
            _log.warning('register_skill 跳过同名技能（保留先注册项）: %s',
                         skill.name)
            return
        self._skills.append(skill)
    def detect_overlap_with(self, new_skill: SkillFrontmatter,
                            existing_skills: list[SkillFrontmatter]) -> list[OverlapReport]:
        if not isinstance(new_skill, SkillFrontmatter):
            _log.warning('detect_overlap_with 拒绝非 SkillFrontmatter 入参: %r',
                         new_skill)
            return []
        if existing_skills is None:
            return []
        existing_items = self._dedupe_by_name(
            _skill_sequence(existing_skills, 'detect_overlap_with'))
        reports = []
        for existing in existing_items:
            reports.extend(self._detect_pair(new_skill, existing))
        return reports
    def _detect_pair(self, a: SkillFrontmatter, b: SkillFrontmatter) -> list[OverlapReport]:
        if a.name == b.name:
            _log.warning('跳过同名技能对，不与自身比较: %s', a.name)
            return []
        reports = []
        trigger_overlap = self._calc_trigger_overlap(a, b)
        if trigger_overlap["score"] > _TRIGGER_OVERLAP_MIN:
            reports.append(self._build_report(
                a, b, "trigger", trigger_overlap["score"],
                trigger_overlap["shared"], trigger_overlap["desc"],
                self._resolve_trigger_overlap(a, b, trigger_overlap)))
        semantic_score = self._calc_semantic_overlap(a, b)
        if semantic_score > _SEMANTIC_OVERLAP_MIN:
            reports.append(self._build_report(
                a, b, "semantic", semantic_score, [],
                f"技能描述语义相似度{semantic_score:.0%}，Agent可能混淆调用",
                self._resolve_semantic_overlap(semantic_score)))
        kw_overlap = self._calc_keyword_overlap(a, b)
        if kw_overlap["score"] > _FUNCTIONAL_OVERLAP_MIN:
            reports.append(self._build_report(
                a, b, "functional", kw_overlap["score"],
                kw_overlap["shared_keywords"],
                f"功能关键词重叠率{kw_overlap['score']:.0%}，可能功能冗余",
                self._resolve_functional_overlap(a, b, kw_overlap)))
        return reports
    def _build_report(self, a: SkillFrontmatter, b: SkillFrontmatter,
                      overlap_type: str, score: float, shared: list[str],
                      description: str, resolution: str) -> OverlapReport:
        return OverlapReport(
            pair=(a.name, b.name),
            overlap_type=overlap_type,
            overlap_score=score,
            shared_triggers=shared,
            conflict_description=description,
            resolution=resolution,
        )
    def _calc_trigger_overlap(self, a: SkillFrontmatter,
                               b: SkillFrontmatter) -> dict:
        a_triggers = self._trigger_set(a)
        b_triggers = self._trigger_set(b)
        shared = a_triggers & b_triggers
        score = jaccard(a_triggers, b_triggers)
        shared_sorted = sorted(shared)
        desc_parts = []
        if shared:
            desc_parts.append(f"共享触发词: {', '.join(shared_sorted[:8])}")
            desc_parts.append(
                f'触发词重叠率{score:.0%}，Agent可能在"{", ".join(shared_sorted[:3])}"场景下同时匹配两个技能'
            )
        return {
            "score": score,
            "shared": shared_sorted,
            "desc": "; ".join(desc_parts),
        }
    def _calc_semantic_overlap(self, a: SkillFrontmatter,
                                b: SkillFrontmatter) -> float:
        text_a = self._semantic_text(a)
        text_b = self._semantic_text(b)
        if not text_a or not text_b:
            return 0.0
        first, second = (text_a, text_b) if text_a <= text_b else (text_b, text_a)
        return SequenceMatcher(None, first, second).ratio()
    @staticmethod
    def _semantic_text(skill: SkillFrontmatter) -> str:
        description = _capability_text(skill.description)
        keywords = " ".join(normalize_str_list(skill.keywords))
        return f"{description} {keywords}".strip().lower()
    def _calc_keyword_overlap(self, a: SkillFrontmatter,
                               b: SkillFrontmatter) -> dict:
        a_kw = {k.lower() for k in normalize_str_list(a.keywords)}
        b_kw = {k.lower() for k in normalize_str_list(b.keywords)}
        shared = a_kw & b_kw
        a_only = a_kw - b_kw
        b_only = b_kw - a_kw
        score = jaccard(a_kw, b_kw)
        shared_sorted = sorted(shared)
        desc_parts = []
        if shared:
            desc_parts.append(f"共享关键词: {', '.join(shared_sorted[:8])}")
        desc_parts.append(f"关键词重叠率{score:.0%}")
        return {
            "score": score,
            "shared_keywords": shared_sorted,
            "a_only_keywords": sorted(a_only),
            "b_only_keywords": sorted(b_only),
            "desc": "; ".join(desc_parts),
        }
    def _trigger_set(self, skill: SkillFrontmatter) -> set[str]:
        triggers = (set(self._extract_triggers(_capability_text(skill.description)))
                    | {k.lower() for k in normalize_str_list(skill.keywords)})
        return {t for t in triggers if t not in _TRIGGER_NOISE}
    def _extract_triggers(self, text: str) -> list[str]:
        if not text:
            return []
        triggers: list[str] = []
        text_lower = text.lower()
        must_match = re.findall(
            rf"(?:{_MUST_CUE_ALT}|触发)\s*"
            r"([\w\u4e00-\u9fff-]+(?:[\s:：]+[\w\u4e00-\u9fff-]+){0,2})",
            text, re.IGNORECASE)
        triggers.extend(
            token.lower()
            for chunk in must_match
            for token in re.split(r"[\s:：]+", chunk)
            if token)
        for verb in _TRIGGER_VERBS:
            if re.search(word_pattern(verb), text_lower):
                triggers.append(verb)
        return list(dict.fromkeys(triggers))
    def _resolve_trigger_overlap(self, a: SkillFrontmatter, b: SkillFrontmatter,
                                   overlap: dict) -> str:
        strategies = []
        if overlap["shared"]:
            strategies.append(f"在{a.name}的NOT-for中添加'{b.name}相关场景'")
        shared = set(overlap["shared"])
        a_only = self._trigger_set(a) - shared
        b_only = self._trigger_set(b) - shared
        if a_only:
            strategies.append(f"{a.name}的触发词建议聚焦于: {', '.join(sorted(a_only)[:3])}")
        if b_only:
            strategies.append(f"{b.name}的触发词建议聚焦于: {', '.join(sorted(b_only)[:3])}")
        if overlap["score"] > 0.7:
            strategies.append(
                f"重叠严重（重叠度{overlap['score']:.0%}），建议合并为一个技能后分层路由")
        return "; ".join(strategies) if strategies else "添加负例声明，明确分工"
    def _resolve_semantic_overlap(self, score: float) -> str:
        if score > 0.7:
            return f"语义高度重叠({score:.0%})，建议合并为统一技能或将其中一个改为子模块"
        return "细化description的触发场景描述，突出各自差异化能力"
    def _resolve_functional_overlap(self, a: SkillFrontmatter, b: SkillFrontmatter,
                                      overlap: dict) -> str:
        shared = overlap.get("shared_keywords", [])
        a_only = overlap.get("a_only_keywords", [])
        b_only = overlap.get("b_only_keywords", [])
        strategies = []
        if shared:
            shared_sample = shared[:5]
            strategies.append(
                f"共享关键词({len(shared)}个)需重新分配：{', '.join(shared_sample)}"
                + ("..." if len(shared) > 5 else ""))
        if a_only:
            strategies.append(f"{a.name}独有关键词：{', '.join(a_only[:3])}")
        if b_only:
            strategies.append(f"{b.name}独有关键词：{', '.join(b_only[:3])}")
        if overlap.get("score", 0) > 0.5:
            strategies.append("建议添加负例声明明确功能边界")
        return "; ".join(strategies) if strategies else "无显著功能重叠"
    def _normalize_skill_items(self,
                               skills: dict | list | None) -> list[SkillFrontmatter]:
        if skills is None:
            raw_items: object = list(self._skills)
        elif isinstance(skills, dict):
            raw_items = list(skills.values())
        else:
            raw_items = skills
        skill_items = _skill_sequence(raw_items, 'detect_all')
        return self._dedupe_by_name(skill_items)
    @staticmethod
    def _dedupe_by_name(skill_items: list[SkillFrontmatter]) -> list[SkillFrontmatter]:
        seen_names: set[str] = set()
        deduped: list[SkillFrontmatter] = []
        for skill in skill_items:
            if skill.name in seen_names:
                continue
            seen_names.add(skill.name)
            deduped.append(skill)
        if len(deduped) != len(skill_items):
            _log.warning('跳过 %d 个同名重复技能项（保留首个）',
                         len(skill_items) - len(deduped))
        return deduped
    def detect_all(self, skills: dict | list | None = None) -> CrossSkillOverlapResult:
        skill_items = self._normalize_skill_items(skills)
        overlapping, isolated = self._overlap_outcome(
            skill_items, self._detect_overlaps(skill_items))
        result = CrossSkillOverlapResult(
            total_skills=len(skill_items),
            overlapping_pairs=overlapping,
            isolated_skills=isolated,
            resolution_plan=self._generate_resolution_plan(overlapping),
        )
        result.summary = self._generate_summary(result)
        _log.info("detect_all 完成: %d 技能, %d 重叠报告, %d 孤立技能",
                  result.total_skills, len(result.overlapping_pairs),
                  len(result.isolated_skills))
        return result
    def _detect_overlaps(self,
                         skill_items: list[SkillFrontmatter]) -> list[OverlapReport]:
        reports: list[OverlapReport] = []
        for skill_a, skill_b in combinations(skill_items, 2):
            reports.extend(self._detect_pair(skill_a, skill_b))
        return reports
    @staticmethod
    def _overlap_outcome(skill_items: list[SkillFrontmatter],
                         reports: list[OverlapReport]
                         ) -> tuple[list[OverlapReport], list[str]]:
        overlapping = list(reports)
        paired = {name for r in overlapping for name in r.pair if name}
        isolated = sorted(s.name for s in skill_items
                          if s.name and s.name not in paired)
        return overlapping, isolated
    def _generate_resolution_plan(self, reports: list[OverlapReport]) -> list[str]:
        plan = []
        seen_pairs = set()
        for rep in sorted(reports, key=lambda r: r.overlap_score, reverse=True):
            pair_key = tuple(sorted(rep.pair))
            if pair_key in seen_pairs:
                continue
            seen_pairs.add(pair_key)
            plan.append(
                f"[{rep.overlap_type.upper()}] {rep.pair[0]} ↔ {rep.pair[1]} "
                f"(重叠度{rep.overlap_score:.0%}): {rep.resolution}"
            )
        return plan
    def _generate_summary(self, result: CrossSkillOverlapResult) -> str:
        parts = []
        parts.append(f"检测{result.total_skills}个技能, "
                      f"发现{len(result.overlapping_pairs)}处重叠")
        high_risk = [r for r in result.overlapping_pairs
                     if r.overlap_score > _HIGH_RISK_OVERLAP_THRESHOLD]
        if high_risk:
            parts.append(f"高风险重叠{len(high_risk)}处需优先处理")
        if result.isolated_skills:
            parts.append(f"孤立技能{len(result.isolated_skills)}个(无重叠)")
        return "; ".join(parts)
def detect_skill_overlaps(skills_metadata: list[dict]) -> CrossSkillOverlapResult:
    metadata_items = _normalize_sequence_input(
        skills_metadata, "detect_skill_overlaps 入参") or []
    detector = CrossSkillOverlapDetector()
    for skill in metadata_items:
        frontmatter = SkillFrontmatter.from_metadata(skill)
        if frontmatter is not None:
            detector.register_skill(frontmatter)
    result = detector.detect_all()
    _log.info("detect_skill_overlaps 完成: %d 技能, %d 重叠对, %d 孤立",
              result.total_skills, len(result.overlapping_pairs),
              len(result.isolated_skills))
    return result
def suggest_pair_resolution(a: SkillFrontmatter, b: SkillFrontmatter) -> list[str]:
    detector = CrossSkillOverlapDetector()
    detector.register_skill(a)
    detector.register_skill(b)
    result = detector.detect_all()
    return result.resolution_plan
_TRAILING_PUNCT = ". 。　 "
_CONTROL_CHAR_RE = re.compile(r'[\x00-\x1f\x7f]')
_YAML_COMMON_CONTROL_ESCAPES = {
    '\n': '\\n',
    '\r': '\\r',
    '\t': '\\t',
}
_MAX_KEYWORDS = 15
_GENERIC_NAME_SEGMENTS: frozenset[str] = frozenset({
    "skill", "skills", "tool", "tools", "agent", "assistant", "plugin",
})
_CORE_ACTION_VERBS_LOWER: frozenset[str] = frozenset(
    verb.lower() for verb in CORE_ACTION_VERBS)
_CORE_ACTION_FALLBACKS: tuple[tuple[tuple[str, ...], str], ...] = (
    (("create", "build"), "create"),
    (("edit", "modify"), "edit"),
    (("analyze",), "analyze"),
    (("check", "diag"), "check"),
)
_DOMAIN_NEGATIVES: dict[str, str] = {
    "docx": "PDF creation; plain text editing without formatting",
    "xlsx": "database queries; raw CSV without formatting",
    "pptx": "single image creation; video production",
    "pdf": "Word document editing; Excel analysis",
    "browser": "local file operations; system commands",
    "code": "document editing; spreadsheet processing",
    "image": "video processing; document editing",
    "code_diag": "document editing; spreadsheet processing; web browsing",
    "memory": "document editing; file conversion; web scraping",
    "skill-management": "document editing; data analysis; web browsing",
}
_DESC_STOPWORDS: frozenset[str] = frozenset({
    "这个", "一个", "进行", "相关", "需要", "可以", "通过", "使用", "作为",
})
_DESC_PHRASE_SUFFIXES: tuple[str, ...] = (
    "系统", "引擎", "模块", "分析", "诊断", "修复", "检查", "测试",
    "优化", "工具", "流程", "策略", "质量", "安全", "代码", "数据",
    "文件", "文档", "体系", "平台", "框架", "库", "服务", "接口",
    "协议", "规范", "标准", "模型", "算法", "机制", "方案",
    "流水线", "工作流", "执行", "沉淀", "固化", "披露", "防御", "引导",
    "治理", "审计", "监控", "部署", "调度", "编排", "识别", "提取",
    "转换", "生成", "清洗", "校验", "验证", "追踪", "扫描", "检测",
    "定位", "排查", "度量", "评估", "规划", "重构", "退化", "味道",
)
_DESC_PHRASE_MAX_HEAD = 4
_DESC_PHRASE_BOUNDARY_CHARS: frozenset[str] = frozenset(
    "的得地之和与及或并而但把被将从向对于在是把给让帮为")
_DESC_PHRASE_STOP_WORDS: frozenset[str] = frozenset({
    "覆盖", "负责", "支持", "提供", "实现", "完成", "生成", "处理",
    "包括", "包含", "涉及", "适用", "帮助", "辅助", "面向", "针对",
    "基于", "属于", "具有", "拥有", "用于", "新建", "创建", "编辑",
    "整理", "导出", "改写", "要求", "确保", "保证", "避免", "禁止",
    "推荐", "建议", "允许", "专注", "致力",
})
def _is_desc_phrase_char(char: str) -> bool:
    return "\u4e00" <= char <= "\u9fff" and char not in _DESC_PHRASE_BOUNDARY_CHARS
def _is_desc_phrase_boundary(desc: str, cursor: int) -> bool:
    if desc[cursor] in _DESC_PHRASE_BOUNDARY_CHARS:
        return True
    if cursor >= 1:
        window = desc[cursor - 1:cursor + 1]
        return window in _DESC_STOPWORDS or window in _DESC_PHRASE_STOP_WORDS
    return False
_YAML_RESERVED_WORDS: frozenset[str] = frozenset({
    "true", "false", "yes", "no", "on", "off", "null", "~",
})
def _yaml_escape(value) -> str:
    s = value if isinstance(value, str) else str(value)
    s = s.replace("\\", "\\\\").replace('"', '\\"')
    if _CONTROL_CHAR_RE.search(s):
        s = _CONTROL_CHAR_RE.sub(
            lambda m: _YAML_COMMON_CONTROL_ESCAPES.get(
                m.group(), f'\\x{ord(m.group()):02x}'),
            s)
    return s
def _normalize_existing_frontmatters(existing_skills: list) -> list[SkillFrontmatter]:
    return [
        frontmatter for frontmatter in
        (SkillFrontmatter.from_metadata(item) for item in existing_skills)
        if frontmatter is not None
    ]
@dataclass
class RewriteResult:
    original: str = ""
    standardized: str = ""
    refined: str = ""
    candidates: list[str] = field(default_factory=list)
    extracted_verb: str = ""
    extracted_object: str = ""
    confidence: float = 0.0
    is_ambiguous: bool = False
    def all_forms(self) -> list[str]:
        return _dedup_ordered(normalize_str_list(
            [self.original, self.standardized, self.refined]
            + normalize_str_list(self.candidates)))
COLLOQUIAL_PREFIXES = [
    r"^(?:请问一下|请帮(?:忙|俺|我)?|帮我|帮忙|请问|请|能不能|可以|可不可以|麻烦|求助)\s*",
    r"^(?:看看|看一看|看下)\s*(?=怎么|如何)",
    r"(?i)^(?:how to|how do i|how can i|what is|what's|tell me about)\s*",
]
COLLOQUIAL_SUFFIXES = [
    r"\s*(?:呢|啊|呀|吗|吧|哦|哈)$",
    r"(?i)\s*(?:谢谢|感谢|thanks|thank you)$",
]
VERB_NORMALIZATION = {
    "create": ["create", "make", "build", "generate", "construct", "创建", "新建", "生成"],
    "delete": ["delete", "remove", "clear", "drop", "destroy", "删除", "清除"],
    "update": ["update", "modify", "change", "edit", "patch", "更新", "修改"],
    "get": ["get", "fetch", "retrieve", "read", "load", "obtain", "获取", "读取"],
    "process": ["process", "handle", "deal with", "处理"],
    "search": [
        "search", "find", "look", "query", "locate",
        "搜索", "查找", "查询", "查看", "看看", "看", "查",
    ],
    "run": ["run", "execute", "start", "launch", "invoke", "运行", "执行"],
    "stop": ["stop", "halt", "terminate", "kill", "abort", "停止", "终止"],
    "validate": ["validate", "check", "verify", "inspect", "diag", "校验", "验证", "检查"],
    "optimize": ["optimize", "improve", "enhance", "refine", "优化", "改进"],
    "convert": ["convert", "transform", "translate", "migrate", "转换", "迁移"],
    "analyze": ["analyze", "examine", "inspect", "evaluate", "分析", "评估"],
    "export": ["export", "save", "dump", "output", "导出", "保存"],
    "import": ["import", "load", "ingest", "read", "导入", "载入"],
}
_CANDIDATE_VERB_LIMIT = 3
_CANDIDATE_NOUN_LIMIT = 2
_KEYWORD_HIT_WEIGHT = 0.2
_FORM_HIT_WEIGHT = 0.3
_VERB_HIT_WEIGHT = 0.3
_OBJECT_HIT_WEIGHT = 0.2
_CONFIDENCE_VERB_WEIGHT = 0.4
_CONFIDENCE_OBJECT_WEIGHT = 0.3
_CONFIDENCE_LENGTH_WEIGHT = 0.2
_CONFIDENCE_PLAIN_WEIGHT = 0.1
_CONFIDENCE_MIN_LENGTH = 4
_MAX_STRIP_ROUNDS = 5
_FORM_TOKEN_RE = re.compile(r"[A-Za-z0-9_]+")
_FORM_STOP_WORDS = frozenset({
    "a", "an", "and", "are", "as", "at", "be", "by", "can", "could",
    "for", "from", "her", "his", "how", "i", "in", "is", "it", "its",
    "me", "my", "of", "on", "or", "our", "please", "should", "that",
    "the", "their", "these", "this", "those", "to", "what", "with",
    "would", "you", "your",
})
_VERB_OBJECT_FILLER_RE = re.compile(r"^(?:(?:一下|一哈)\s*)+")
def _dedup_ordered(items: list[str]) -> list[str]:
    return list(dict.fromkeys(items))
NOUN_NORMALIZATION = {
    "file": ["file", "document", "doc", "artifact", "文件", "文档"],
    "skill": ["skill", "module", "plugin", "extension", "技能", "模块"],
    "config": ["config", "configuration", "settings", "preference", "配置", "设置"],
    "report": ["report", "summary", "result", "output", "报告", "汇总"],
    "data": ["data", "content", "payload", "body", "数据", "内容"],
    "code": ["code", "script", "program", "source", "代码", "脚本"],
    "test": ["test", "spec", "case", "scenario", "测试", "用例"],
    "dependency": ["dependency", "dep", "requirement", "prerequisite", "依赖", "前置条件"],
    "error": ["error", "exception", "fault", "issue", "错误", "异常", "故障"],
    "log": ["log", "record", "entry", "trace", "日志", "记录"],
    "path": ["path", "route", "location", "directory", "路径", "目录"],
    "memory": ["memory", "cache", "buffer", "store", "内存", "缓存"],
}
class QueryRewriter:
    def __init__(self) -> None:
        self._verb_map = VERB_NORMALIZATION
        self._noun_map = NOUN_NORMALIZATION
        (self._canonical_verb_terms,
         self._synonym_verb_terms) = self._build_search_terms(self._verb_map)
        (self._canonical_noun_terms,
         self._synonym_noun_terms) = self._build_search_terms(self._noun_map)
    @staticmethod
    def _build_search_terms(
        mapping: dict[str, list[str]],
    ) -> tuple[list[tuple[str, str]], list[tuple[str, str]]]:
        return (
            QueryRewriter._canonical_search_terms(mapping),
            QueryRewriter._synonym_search_terms(mapping),
        )
    @staticmethod
    def _canonical_search_terms(mapping: dict[str, list[str]]) -> list[tuple[str, str]]:
        return [(key, key) for key in sorted(mapping.keys(), key=len, reverse=True)]
    @staticmethod
    def _synonym_search_terms(mapping: dict[str, list[str]]) -> list[tuple[str, str]]:
        syn_owner: dict[str, str] = {}
        for key, syn_list in mapping.items():
            for syn in syn_list:
                if syn != key:
                    syn_owner.setdefault(syn, key)
        return [
            (syn, owner) for syn, owner in sorted(
                syn_owner.items(), key=lambda kv: len(kv[0]), reverse=True)
        ]
    def rewrite(self, query: str) -> RewriteResult:
        query = normalize_str(query)
        result = RewriteResult(original=query)
        standardized = self._remove_colloquial(query)
        result.standardized = standardized
        verb, obj = self._extract_core(standardized)
        result.extracted_verb = verb
        result.extracted_object = obj
        refined = self._refine_intent(standardized, verb)
        result.refined = refined
        candidates = self._generate_candidates(verb, obj)
        result.candidates = candidates
        result.confidence = self._calc_confidence(standardized, verb, obj)
        result.is_ambiguous = not (verb and obj)
        return result
    @staticmethod
    def _contains_match_term(text: str, term: str) -> bool:
        if not text or not term:
            return False
        if term.isascii():
            return re.search(word_pattern(term), text, re.IGNORECASE) is not None
        return term in text
    @classmethod
    def _form_matches_description(cls, form_lower: str, desc_lower: str) -> bool:
        if cls._contains_match_term(desc_lower, form_lower):
            return True
        return any(
            len(word) > 1 and word not in _FORM_STOP_WORDS
            and cls._contains_match_term(desc_lower, word)
            for word in _FORM_TOKEN_RE.findall(form_lower)
        )
    @classmethod
    def _score_form_for_skill(cls, form_lower: str, verb: str, obj: str,
                              keywords_lower: list[str],
                              desc_lower: str) -> float:
        score = _KEYWORD_HIT_WEIGHT * sum(
            1 for kw in keywords_lower
            if cls._contains_match_term(form_lower, kw))
        if cls._form_matches_description(form_lower, desc_lower):
            score += _FORM_HIT_WEIGHT
        if cls._contains_match_term(desc_lower, verb):
            score += _VERB_HIT_WEIGHT
        if cls._contains_match_term(desc_lower, obj):
            score += _OBJECT_HIT_WEIGHT
        return score
    @staticmethod
    def _lowered_match_context(skill_keywords: list[str],
                               skill_description: str) -> tuple[list[str], str]:
        return (
            _dedup_ordered([k.lower() for k in skill_keywords]),
            skill_description.lower(),
        )
    def rewrite_for_skill_match(self, query: str, skill_keywords: list[str],
                                 skill_description: str) -> tuple[str, float]:
        skill_keywords = normalize_str_list(skill_keywords)
        skill_description = normalize_str(skill_description)
        result = self.rewrite(query)
        best_score = 0.0
        best_form = result.original
        keywords_lower, desc_lower = self._lowered_match_context(
            skill_keywords, skill_description)
        for form in result.all_forms():
            score = self._score_form_for_skill(
                form.lower(), result.extracted_verb, result.extracted_object,
                keywords_lower, desc_lower)
            if score > best_score:
                best_score = score
                best_form = form
        return best_form, min(best_score, 1.0)
    @staticmethod
    def _strip_to_fixpoint(s: str, patterns: list[str]) -> str:
        for _ in range(_MAX_STRIP_ROUNDS):
            prev = s
            for pat in patterns:
                s = re.sub(pat, "", s).strip()
            if s == prev:
                break
        return s
    def _remove_colloquial(self, query: str) -> str:
        s = self._strip_to_fixpoint(query.strip(), COLLOQUIAL_PREFIXES)
        return self._strip_to_fixpoint(s, COLLOQUIAL_SUFFIXES)
    def _extract_core(self, text: str) -> tuple[str, str]:
        verb, obj = self._find_verb(text)
        if verb:
            return verb, obj
        return self._find_noun_fallback(text)
    @staticmethod
    def _first_hit_in_layers(layers: tuple[list[tuple[str, str]], ...],
                             text: str) -> tuple[str, re.Match | None]:
        best: tuple[int, int, int, str, re.Match] | None = None
        for layer_index, terms in enumerate(layers):
            for term, canonical in terms:
                m = re.search(word_pattern(term), text, re.IGNORECASE)
                if m is None:
                    continue
                rank = (m.start(), layer_index, -len(term))
                if best is None or rank < best[:3]:
                    best = (rank[0], rank[1], rank[2], canonical, m)
        if best is not None:
            return best[3], best[4]
        return "", None
    def _find_verb(self, text: str) -> tuple[str, str]:
        verb, match = self._first_hit_in_layers(
            (self._canonical_verb_terms, self._synonym_verb_terms), text)
        if match is None:
            return "", ""
        obj = _VERB_OBJECT_FILLER_RE.sub("", text[match.end():])
        obj = obj.lstrip(" \t\r\n：:").strip(" \t\r\n。.！!？?；;，,")
        if not obj:
            prefix = text[:match.start()].strip(" \t\r\n。.！!？?；;，,：:")
            _, noun_match = self._first_hit_in_layers(
                (self._canonical_noun_terms, self._synonym_noun_terms), prefix)
            if noun_match is not None and noun_match.span() == (0, len(prefix)):
                obj = prefix
        return verb, obj
    def _find_noun_fallback(self, text: str) -> tuple[str, str]:
        obj, match = self._first_hit_in_layers(
            (self._canonical_noun_terms, self._synonym_noun_terms), text)
        if match is None:
            return "", ""
        return "", obj
    def _refine_intent(self, text: str, verb: str) -> str:
        synonyms = self._verb_map.get(verb)
        if not synonyms:
            return text
        terms = [(verb, verb)] + [
            (syn, verb) for syn in synonyms if syn != verb
        ]
        _, match = self._first_hit_in_layers((terms,), text)
        if match is None or match.group().lower() == verb.lower():
            return text
        return text[:match.start()] + verb + text[match.end():]
    def _generate_candidates(self, verb: str, obj: str) -> list[str]:
        if not (verb and obj):
            return []
        verb_forms = self._verb_map.get(verb, [verb])[:_CANDIDATE_VERB_LIMIT]
        noun_key = obj
        noun, noun_match = self._first_hit_in_layers(
            (self._canonical_noun_terms, self._synonym_noun_terms), obj)
        if noun_match is not None and noun_match.span() == (0, len(obj)):
            noun_key = noun
        noun_forms = self._noun_map.get(noun_key, [obj])[:_CANDIDATE_NOUN_LIMIT]
        return _dedup_ordered(
            # jwsgj:suppress large_list_alloc
            [f"{sv} {sn}" for sv in verb_forms for sn in noun_forms])
    def _calc_confidence(self, text: str, verb: str, obj: str) -> float:
        if not text:
            return 0.0
        rules = (
            (verb in self._verb_map, _CONFIDENCE_VERB_WEIGHT),
            (bool(obj), _CONFIDENCE_OBJECT_WEIGHT),
            (len(text) >= _CONFIDENCE_MIN_LENGTH, _CONFIDENCE_LENGTH_WEIGHT),
            (not re.search(r"[?？]", text), _CONFIDENCE_PLAIN_WEIGHT),
        )
        return min(sum(weight for hit, weight in rules if hit), 1.0)
_global_rewriter: QueryRewriter = QueryRewriter()
def get_rewriter() -> QueryRewriter:
    return _global_rewriter
def _generation_violation_issues(report: Any) -> list[str]:
    issues: list[str] = []
    critical_detailed = 0
    for violation in report.violations:
        if violation.severity == "critical":
            critical_detailed += 1
        if violation.severity not in ("critical", "high"):
            continue
        issues.append(
            f"[GEN-{violation.rule_id}] {violation.description[:80]}")
    if report.critical_count > critical_detailed:
        issues.insert(
            0, f"生成的 description严重违规({report.critical_count}项)")
    return issues
def _normalize_matching_score(value: Any) -> float | None:
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, (int, float)):
        try:
            score = float(value)
        except OverflowError:
            _log.warning("matching_score 数值超出浮点范围: %r，按未提供处理", value)
            return None
    elif isinstance(value, str):
        try:
            score = float(value.strip())
        except ValueError:
            _log.warning("matching_score 非数值字符串: %r，按未提供处理", value)
            return None
    else:
        _log.warning("matching_score 类型 %s 非法，按未提供处理",
                     type(value).__name__)
        return None
    if not math.isfinite(score):
        _log.warning("matching_score 非有限数值: %r，按未提供处理", value)
        return None
    return score
def assess_description_generation(
        skill_name: str, keywords: list[str],
        matching_score: float | None = None) -> dict[str, Any]:
    matching_score = _normalize_matching_score(matching_score)
    generation = generate_matching_description(
        skill_name=normalize_str(skill_name),
        keywords=normalize_str_list(keywords))
    score = generation["diag"].overall_score
    optimizations: list[str] = []
    if score >= 80 and (matching_score is None or score > matching_score):
        optimizations.append("建议参考生成的 description 以提升匹配质量")
    return {
        "generation": generation,
        "score": score,
        "issues": _generation_violation_issues(generation["diag"]),
        "optimizations": optimizations,
    }
@dataclass
class MetadataOptimizationResult:
    skill_name: str = ""
    optimized_description: str = ""
    optimized_keywords: list[str] = field(default_factory=list)
    category: str = ""
    domain_hint: str = ""
    frontmatter: str = ""
    trigger_score: float = 0.0
    issues: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
class SkillMetadataOptimizer:
    _EXTRA_DOMAIN_PATTERNS: ClassVar[dict[str, list[str]]] = {
        "code_diag": ["diag", "诊断", "修复", "fix", "安全", "security", "漏洞", "vulnerability", "代码质量", "重构", "refactor"],
    }
    def __init__(self) -> None:
        self._trigger_optimizer = TriggerOptimizer()
        self._verb_map = VERB_SYNONYM_EXPANSION
        self._domain_patterns = {
            **DOMAIN_TRIGGER_PATTERNS, **self._EXTRA_DOMAIN_PATTERNS}
        self._query_rewriter = QueryRewriter()
        self._trigger_tester = TriggerTestSuite()
    def optimize(self, skill_name: str, description: str = "",
                 skill_type: str = "", user_keywords: list[str] | None = None) -> MetadataOptimizationResult:
        raw_name = normalize_str(skill_name).strip()
        skill_name = raw_name or "unnamed-skill"
        if not raw_name:
            _log.warning("optimize: skill_name 为空，使用默认名称 'unnamed-skill'")
        description = normalize_str(description)
        skill_type = normalize_str(skill_type)
        result = MetadataOptimizationResult(skill_name=skill_name)
        domain = self._infer_domain(raw_name, skill_type)
        category = skill_type or domain or "generic"
        result.domain_hint = normalize_str(domain)
        result.category = category
        opt_desc = self._optimize_description(skill_name, description, domain)
        result.optimized_description = opt_desc
        keywords = self._infer_keywords(raw_name, opt_desc, domain, user_keywords)
        result.optimized_keywords = keywords
        result.frontmatter = self._generate_frontmatter(
            skill_name, opt_desc, keywords, category
        )
        trigger_result = self._trigger_optimizer.analyze(opt_desc, keywords, skill_name, domain)
        result.trigger_score = trigger_result.overall_score
        result.issues = trigger_result.suggestions
        if len(opt_desc) < 20:
            result.warnings.append("description过短，建议补充触发场景")
        if len(keywords) < 5:
            result.warnings.append("keywords数量不足，建议至少5个")
        return result
    def _infer_domain(self, name: str, skill_type: str) -> str | None:
        normalized_type = skill_type.strip().lower()
        if normalized_type in self._domain_patterns:
            return normalized_type
        combined = (normalize_str(name) + " " + normalize_str(skill_type)).lower()
        for domain, indicators in self._domain_patterns.items():
            if any(keyword_matches(ind, combined) for ind in indicators):
                return domain
        return None
    def _optimize_description(self, name: str, desc: str, domain: str | None) -> str:
        if not desc.strip() or desc.strip().startswith("[TODO"):
            desc = self._auto_generate_description(name)
        desc = desc.strip()
        desc = self._ensure_trigger_prefix(name, desc)
        desc = self._append_negative_defense(desc, domain)
        return truncate_keep_negative(desc, DESCRIPTION_MAX_LEN)
    def _ensure_trigger_prefix(self, name: str, desc: str) -> str:
        desc = _reorder_leading_negative(desc)
        positive_desc = _positive_trigger_subject(
            _mask_negated_context(desc).lstrip(" \t\r\n.。!！?？；;"))
        if _TRIGGER_PREFIX_PRESENT_RE.search(positive_desc):
            return desc
        if not positive_desc:
            return _trigger_prefix_for(desc, "") + desc
        prefix = _trigger_prefix_for(
            positive_desc, self._extract_core_action(name, positive_desc))
        return prefix + desc
    def _append_negative_defense(self, desc: str, domain: str | None) -> str:
        if _has_negative_scope(desc):
            return desc
        if len(desc) >= 240 or not domain:
            return desc
        negatives = self._generate_negatives(domain)
        if not negatives:
            return desc
        return desc.rstrip(_TRAILING_PUNCT) + f". NOT for: {negatives}."
    def _auto_generate_description(self, name: str) -> str:
        name = normalize_str(name)
        action = self._extract_core_action(name, "")
        noun = name.replace("skill-", "").replace("-", " ").replace("_", " ").strip()
        if action:
            action_terms = [action]
            for hints, fallback_action in _CORE_ACTION_FALLBACKS:
                if fallback_action == action:
                    action_terms.extend(hints)
            action_pattern = "|".join(
                word_pattern(term)
                for term in sorted(set(action_terms), key=len, reverse=True))
            noun = re.sub(
                rf"(?:{action_pattern})\s*", "", noun,
                count=1, flags=re.IGNORECASE)
            noun = re.sub(r"\s+", " ", noun).strip()
        if not noun:
            noun = "the requested task"
        if action:
            return f"Trigger this skill when the user asks to {action} {noun}."
        return f"Use this skill when the user needs to work with {noun}."
    def _extract_core_action(self, name: str, desc: str) -> str | None:
        combined = (normalize_str(name) + " " + normalize_str(desc)).lower()
        best_rank: tuple[int, int, int] | None = None
        best_action: str | None = None
        order = 0
        def consider(action: str, term: str, source: int, *, stem: bool) -> None:
            nonlocal best_rank, best_action, order
            if term.isascii():
                pattern = rf"(?<![A-Za-z0-9_]){re.escape(term)}"
                if not stem:
                    pattern += r"(?![A-Za-z0-9_])"
            else:
                pattern = re.escape(term)
            match = re.search(pattern, combined)
            if match is not None:
                rank = (match.start(), source, order)
                if best_rank is None or rank < best_rank:
                    best_rank = rank
                    best_action = action
            order += 1
        for verb in self._verb_map:
            consider(verb, verb, 0, stem=True)
        for action_verb in CORE_ACTION_VERBS:
            consider(action_verb, action_verb, 1, stem=False)
        for hints, action in _CORE_ACTION_FALLBACKS:
            for hint in hints:
                consider(action, hint, 2, stem=True)
        return best_action
    def _infer_keywords(self, name: str, desc: str, domain: str | None,
                        user_keywords: list[str] | None) -> list[str]:
        user_keywords = normalize_str_list(user_keywords)
        name = normalize_str(name)
        desc = _capability_text(desc)
        keywords_set: set[str] = {kw.lower() for kw in user_keywords}
        name_parts = re.split(r"[-_]", name.lower())
        keywords_set.update(
            part for part in name_parts
            if len(part) > 1 and part not in _GENERIC_NAME_SEGMENTS)
        keywords_set |= self._collect_desc_keywords(desc)
        self._add_verb_synonyms(desc.lower(), keywords_set)
        if domain:
            for term in self._domain_patterns.get(domain, []):
                keywords_set.add(term.lower())
        user_ordered: list[str] = []
        seen_user: set[str] = set()
        for kw in user_keywords:
            lowered = kw.lower()
            if lowered not in seen_user:
                seen_user.add(lowered)
                user_ordered.append(kw)
        return (user_ordered + sorted(keywords_set - seen_user))[:_MAX_KEYWORDS]
    @staticmethod
    def _collect_desc_keywords(desc: str) -> set[str]:
        phrases: set[str] = set()
        for suffix in _DESC_PHRASE_SUFFIXES:
            start = 0
            while True:
                index = desc.find(suffix, start)
                if index < 0:
                    break
                head: list[str] = []
                cursor = index - 1
                while cursor >= 0 and len(head) < _DESC_PHRASE_MAX_HEAD:
                    if (not _is_desc_phrase_char(desc[cursor])
                            or _is_desc_phrase_boundary(desc, cursor)):
                        break
                    head.append(desc[cursor])
                    cursor -= 1
                truncated = (
                    len(head) == _DESC_PHRASE_MAX_HEAD
                    and cursor >= 0
                    and _is_desc_phrase_char(desc[cursor])
                    and not _is_desc_phrase_boundary(desc, cursor)
                )
                if len(head) >= 2 and not truncated:
                    phrases.add("".join(reversed(head)) + suffix)
                start = index + len(suffix)
        return {
            word for word in phrases
            if word not in _DESC_STOPWORDS and word in desc
        }
    def _add_verb_synonyms(self, desc_lower: str, keywords_set: set[str]) -> None:
        for verb, synonyms in self._verb_map.items():
            if stem_matches(verb, desc_lower):
                keywords_set.add(verb)
                for syn in synonyms[:2]:
                    if syn.lower() not in keywords_set:
                        keywords_set.add(syn.lower())
    @staticmethod
    def _generate_negatives(domain: str) -> str:
        if not isinstance(domain, str):
            return ""
        return _DOMAIN_NEGATIVES.get(domain, "")
    @staticmethod
    def _yaml_safe_name(name: str) -> str:
        value = normalize_str(name).strip() or "unnamed-skill"
        if (value.lower() not in _YAML_RESERVED_WORDS
                and re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", value)):
            return value
        return f'"{_yaml_escape(value)}"'
    def _generate_frontmatter(self, name: str, desc: str, keywords: list[str],
                              category: str) -> str:
        safe_name = self._yaml_safe_name(name)
        safe_desc = desc.strip()
        if len(safe_desc) > DESCRIPTION_MAX_LEN:
            safe_desc = truncate_description(
                safe_desc, DESCRIPTION_MAX_LEN, "。", clamp_within_limit=True)
        safe_desc = _yaml_escape(safe_desc)
        kw_str = ", ".join(
            f'"{_yaml_escape(kw)}"' for kw in keywords[:_MAX_KEYWORDS])
        safe_category = _yaml_escape(category)
        lines = [
            "---",
            f'name: {safe_name}',
            f'description: "{safe_desc}"',
            f'version: "{DEFAULT_SKILL_VERSION}"',
            f'category: "{safe_category}"',
            f'keywords: [{kw_str}]',
            "depends_on: []",
            "---",
        ]
        return "\n".join(lines)
    def run_validation(self, skill_name: str, skill_type: str,
                       keywords: list, description: str, base: MetadataOptimizationResult,
                       existing_skills: list | None = None) -> dict:
        skill_name = normalize_str(skill_name)
        skill_type = normalize_str(skill_type)
        description = normalize_str(description)
        keywords = normalize_str_list(keywords)
        suite_result = self._trigger_tester.run(skill_name, description, keywords)
        self._run_confidence_calibration(skill_name, suite_result)
        trigger_test = {
            "skill_name": skill_name,
            "accuracy": suite_result.accuracy,
            "precision": suite_result.precision,
            "recall": suite_result.recall,
            "total": suite_result.total,
            "passed": suite_result.passed,
            "suggestions": list(suite_result.recommendations),
        }
        return {
            "query_rewriting": self._build_query_rewriting_result(
                skill_name, skill_type, keywords, description),
            "overlap_detection": self._build_overlap_detection_result(
                skill_name, base, existing_skills),
            "trigger_test": trigger_test,
        }
    def _build_query_rewriting_result(self, skill_name: str, skill_type: str,
                                       keywords: list[str], description: str) -> dict:
        name_words = skill_name.replace('-', ' ').replace('_', ' ')
        type_words = skill_type or 'process'
        test_queries = [
            f'help me {name_words}',
            f'i want to {type_words} {name_words}',
            f'can you {name_words}',
        ]
        rewrite_results: list[dict[str, Any]] = []
        for q in test_queries:
            best_form, match_score = self._query_rewriter.rewrite_for_skill_match(
                q, keywords, description
            )
            rewrite_results.append({
                'original': q,
                'best_form': best_form,
                'match_score': match_score,
            })
        return {
            'rewrite_results': rewrite_results,
            'average_match_score': round(
                sum(r['match_score'] for r in rewrite_results) / max(len(rewrite_results), 1), 3),
            'test_query_count': len(test_queries),
        }
    def _build_overlap_detection_result(self, skill_name: str,
                                        base: MetadataOptimizationResult,
                                        existing_skills: list | None) -> dict:
        if existing_skills is not None and not isinstance(
                existing_skills, (list, tuple)):
            _log.warning(
                '_build_overlap_detection_result existing_skills 非列表形态: %s，'
                '按空处理', type(existing_skills).__name__)
            existing_skills = []
        if not existing_skills:
            return {'overlap_count': 0, 'overlaps': []}
        if not isinstance(base, MetadataOptimizationResult):
            _log.warning(
                '_build_overlap_detection_result base 非 MetadataOptimizationResult: %s，'
                '按空优化结果处理', type(base).__name__)
            base = MetadataOptimizationResult()
        new_skill_md = SkillFrontmatter(
            name=skill_name,
            description=base.optimized_description,
            keywords=base.optimized_keywords,
            category=base.category,
        )
        existing_frontmatters = _normalize_existing_frontmatters(
            existing_skills)
        overlaps = CrossSkillOverlapDetector().detect_overlap_with(
            new_skill_md, existing_frontmatters
        )
        return {
            'overlap_count': len(overlaps),
            'overlaps': overlaps,
        }
    def _run_confidence_calibration(self, skill_name: str,
                                     test_result: TriggerTestSuiteResult) -> None:
        records = [
            (detail.test_case.query, detail.match_score, detail.triggered)
            for detail in test_result.details
            if detail.test_case is not None
        ]
        if records:
            get_calibrator().record_from_test(skill_name, records)
def _skill_field_str(skill: dict[str, Any], key: str) -> str:
    value = skill.get(key)
    if isinstance(value, str):
        return value
    if value is not None:
        _log.warning(
            "技能字段 %s 非 str 类型（%s），已归空", key, type(value).__name__
        )
    return ""
def _filter_items_by_type(items: list[Any], item_type: type,
                          label: str, noun: str) -> list[Any]:
    valid = [item for item in items if isinstance(item, item_type)]
    dropped = len(items) - len(valid)
    if dropped:
        _log.warning(
            "%s含 %d 个%s（类型：%s），已跳过",
            label, dropped, noun,
            ", ".join(
                sorted({
                    type(item).__name__ for item in items
                    if not isinstance(item, item_type)
                })
            ),
        )
    return valid
def _normalize_skill_records(skills) -> list[dict[str, Any]]:
    records = _normalize_sequence_input(skills, "detect 入参 skills")
    if records is None:
        return []
    valid_skills = _filter_items_by_type(records, dict, "detect 入参", "非 dict 项")
    normalized: list[dict[str, Any]] = []
    seen_names: set[str] = set()
    unnamed = 0
    duplicate_names = 0
    for skill in valid_skills:
        name = _skill_field_str(skill, "name").strip()
        if not name:
            unnamed += 1
            continue
        if name in seen_names:
            duplicate_names += 1
            continue
        seen_names.add(name)
        normalized.append(dict(
            skill,
            name=name,
            description=_skill_field_str(skill, "description"),
        ))
    if unnamed:
        _log.warning("detect 入参跳过 %d 个缺少有效 name 的技能记录", unnamed)
    if duplicate_names:
        _log.warning(
            "detect 入参跳过 %d 个同名重复技能记录（保留首个）", duplicate_names)
    return normalized
_FILE_CONFLICT_EXTENSIONS: frozenset[str] = frozenset({
    "docx", "xlsx", "xlsm", "xls", "csv", "tsv", "pptx", "pdf",
    "dbt", "ksheet", "otl",
    "py", "pyi", "js", "jsx", "ts", "tsx", "java", "go", "rs",
    "c", "h", "cpp", "hpp", "cs", "rb", "php", "sh", "bash", "ps1",
    "sql", "ipynb",
    "json", "jsonl", "yaml", "yml", "toml", "ini", "cfg", "xml",
    "md", "txt", "html", "css", "log",
    "dwg", "dxf",
})
_FILE_CONFLICT_EXTENSION_RE = re.compile(
    r"\.(" + "|".join(sorted(
        _FILE_CONFLICT_EXTENSIONS, key=len, reverse=True))
    + r")(?![A-Za-z0-9_])",
    re.IGNORECASE,
)
_GENERIC_SKILL_FILENAMES: tuple[str, ...] = (
    "SKILL.md", "README.md", "AGENTS.md", "CLAUDE.md", "RULES.md",
)
_GENERIC_SKILL_FILENAME_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])(?:"
    + "|".join(re.escape(name) for name in _GENERIC_SKILL_FILENAMES)
    + r")(?![A-Za-z0-9_.-])",
    re.IGNORECASE,
)
def _mask_negated_context(text: str) -> str:
    chars = list(text)
    for pattern in _NEGATION_MASK_PATTERNS:
        for match in re.finditer(pattern, text, re.IGNORECASE):
            start, end = match.start(), match.end()
            chars[start:end] = " " * (end - start)
    return "".join(chars)
def _positive_trigger_subject(text: str) -> str:
    positive = text.strip()
    return re.sub(r"^(?:这个|本|此)?\s*技能\s*[。!！?？；;:：,，、\s]+", "", positive).strip()
def _reorder_leading_negative(text: str) -> str:
    stripped = text.strip()
    match = re.match(r"^(.+?[。.!！?？])\s*(.*)$", stripped, re.DOTALL)
    if match is None:
        return stripped
    first, remainder = match.group(1), match.group(2).strip()
    if not remainder or not _has_negative_scope(first):
        return stripped
    return f"{remainder} {first}"
class MatchingConflictDetector:
    def detect(self, skills: list[dict[str, Any]]) -> dict[str, Any]:
        skills = _normalize_skill_records(skills)
        overlaps = self._detect_overlaps(skills)
        contradictions = self._detect_contradictions(skills)
        file_conflicts = self._detect_file_conflicts(skills)
        return {
            "total_skills": len(skills),
            "overlap_count": len(overlaps),
            "contradiction_count": len(contradictions),
            "file_conflict_count": len(file_conflicts),
            "overlaps": overlaps,
            "contradictions": contradictions,
            "file_conflicts": file_conflicts,
        }
    def _detect_overlaps(
        self, skills: list[dict[str, Any]]
    ) -> list[dict[str, Any]]:
        overlaps = []
        pre = [
            (
                tokenize_words(_capability_text(
                    _skill_field_str(s, "description"))),
                _skill_field_str(s, "name"),
            )
            for s in skills
        ]
        for (words_a, name_a), (words_b, name_b) in combinations(pre, 2):
            entry = self._overlap_entry(words_a, name_a, words_b, name_b)
            if entry is not None:
                overlaps.append(entry)
        return overlaps
    @staticmethod
    def _overlap_entry(words_a: set[str], name_a: str,
                       words_b: set[str], name_b: str) -> dict[str, Any] | None:
        if not words_a or not words_b:
            return None
        shared = words_a & words_b
        score = jaccard(words_a, words_b)
        if score <= _FUNCTIONAL_OVERLAP_MIN:
            return None
        return {
            "skill_a": name_a,
            "skill_b": name_b,
            "overlap_score": round(score, 3),
            "shared_words": sorted(shared)[:10],
            "severity": ("high" if score > _HIGH_RISK_OVERLAP_THRESHOLD
                         else "medium"),
            "suggestion": (
                f"'{name_a}' 和 '{name_b}' 的 description "
                f"重叠度 {score:.0%}，建议在各自的 description 中明确互斥条件"
            ),
        }
    def _detect_contradictions(
        self, skills: list[dict[str, Any]]
    ) -> list[dict[str, Any]]:
        contradictions = []
        pre = []
        for s in skills:
            raw_desc = _skill_field_str(s, "description")
            pre.append(
                (
                    extract_negated_terms(raw_desc, NEGATION_PATTERNS),
                    tokenize_words(_mask_negated_context(
                        _capability_text(raw_desc))),
                    _skill_field_str(s, "name"),
                )
            )
        for (neg_a, words_a, name_a), (neg_b, words_b, name_b) in combinations(pre, 2):
            contradictions.extend(
                self._contradiction_entries(neg_a, name_a, name_b, words_b))
            contradictions.extend(
                self._contradiction_entries(neg_b, name_b, name_a, words_a))
        return contradictions
    @staticmethod
    def _contradiction_entries(negatives: list[str], own_name: str,
                               other_name: str,
                               other_words: set[str]) -> list[dict[str, Any]]:
        entries: list[dict[str, Any]] = []
        for neg in negatives:
            overlap = tokenize_words(neg) & other_words
            if len(overlap) >= 2:
                entries.append({
                    "skill_a": own_name,
                    "skill_b": other_name,
                    "negated_in_a": neg,
                    "matched_in_b": sorted(overlap),
                    "suggestion": (
                        f"'{own_name}' 排除 '{neg}'，但 "
                        f"'{other_name}' 的核心能力中包含相关内容，确认是否矛盾"
                    ),
                })
        return entries
    def _detect_file_conflicts(
        self, skills: list[dict[str, Any]]
    ) -> list[dict[str, Any]]:
        ext_map = self._collect_extension_owners(skills)
        return [
            self._file_conflict_entry(ext, skill_names)
            for ext, skill_names in ext_map.items()
            if len(skill_names) > 1
        ]
    @staticmethod
    def _collect_extension_owners(skills: list[dict[str, Any]]) -> dict[str, list[str]]:
        ext_map: dict[str, list[str]] = {}
        for skill in skills:
            desc = _mask_negated_context(_skill_field_str(skill, "description"))
            desc = _GENERIC_SKILL_FILENAME_RE.sub(" ", desc)
            skill_name = _skill_field_str(skill, "name")
            for raw_ext in _FILE_CONFLICT_EXTENSION_RE.findall(desc):
                ext = raw_ext.lower().strip(". ")
                if not ext:
                    continue
                bucket = ext_map.setdefault(ext, [])
                if skill_name not in bucket:
                    bucket.append(skill_name)
        return ext_map
    @staticmethod
    def _file_conflict_entry(ext: str, skill_names: list[str]) -> dict[str, Any]:
        return {
            "extension": ext,
            "competing_skills": skill_names,
            "severity": "high" if len(skill_names) > 2 else "medium",
            "suggestion": (
                f"多个技能（{', '.join(skill_names)}）都声明处理 .{ext} 文件，"
                "建议在各自的 description 中明确分工条件"
            ),
        }
_conflict_detector_instance = MatchingConflictDetector()
def get_conflict_detector() -> MatchingConflictDetector:
    return _conflict_detector_instance
def _attach_conflicts(
    report: SemanticConsistencyReport, skills: dict[str, str]
) -> None:
    try:
        _conflict_skills = [
            {"name": _n, "description": _d} for _n, _d in skills.items()
        ]
        _mc = get_conflict_detector().detect(_conflict_skills)
        report.matching_conflicts = _mc
        for _o in _mc.get("overlaps", []):
            report.issues.append(
                f"[匹配冲突] {_o['skill_a']} 与 {_o['skill_b']} description 重叠 "
                f"{_o['overlap_score']:.0%}: {_o['suggestion']}"
            )
        for _c in _mc.get("contradictions", []):
            report.issues.append(
                f"[匹配矛盾] {_c['skill_a']} 排除的内容与 {_c['skill_b']} 核心能力重叠: {_c['suggestion']}"
            )
        for _fc in _mc.get("file_conflicts", []):
            report.issues.append(
                f"[文件冲突] 多个技能声明处理 .{_fc['extension']}: "
                f"{_fc['suggestion']}"
            )
    except Exception as _e:  # noqa: BLE001
        _log.warning(
            "[semantic] 匹配冲突检测失败(不影响主流程): %s: %s",
            type(_e).__name__, _e, exc_info=True,
        )
def _build_consistency_issues(report: SemanticConsistencyReport) -> list[str]:
    issues = []
    if report.consistency_score < 70:
        issues.append(
            f"语义一致性评分仅 {report.consistency_score:.1f}，存在大量跨技能语义断层"
        )
    if len(report.high_severity_gaps) > 2:
        issues.append(
            f"发现 {len(report.high_severity_gaps)} 个严重语义断层，Workflow 组合时风险极高"
        )
    return issues
def _build_consistency_suggestions() -> list[str]:
    return [
        "[概念定义] 在 SKILL.md 中为每个核心概念添加明确的语义范围说明",
        "[语义对齐] 建立跨技能的'概念词典'，统一常见概念的语义定义",
        "[接口契约] 使用 JSON Schema 的 description 字段精确描述每个字段的语义范围",
        "[文档规范] 在函数 docstring 的 Args 段落中，不仅说明类型，还要说明语义范围",
    ]
def _root_problem(skills_root: str) -> str:
    if not skills_root.strip():
        return "技能根路径为空，语义一致性未度量"
    try:
        is_dir = Path(skills_root).is_dir()
    except (OSError, ValueError) as exc:
        _log.warning(
            "validate_semantic_consistency 根路径不可用 %r: %s: %s",
            skills_root, type(exc).__name__, exc)
        return f"技能根路径不可用：{skills_root}，语义一致性未度量"
    if not is_dir:
        return f"技能根目录不存在或不是目录：{skills_root}，语义一致性未度量"
    return ""
def validate_semantic_consistency(skills_root: str | os.PathLike) -> SemanticConsistencyReport:
    skills_root = normalize_root_str(skills_root)
    validator = SemanticConsistencyValidator()
    problem = _root_problem(skills_root)
    skills: dict[str, str] = {}
    if not problem:
        try:
            skills = scan_skill_descriptions(skills_root)
        except (OSError, RuntimeError, TypeError, ValueError) as exc:
            _log.warning(
                "validate_semantic_consistency 扫描失败 %r: %s: %s",
                skills_root, type(exc).__name__, exc)
            problem = f"技能根扫描失败：{skills_root}，语义一致性未度量"
    gaps = validator.validate(skills)
    if not problem and not skills:
        problem = f"技能根下未发现可用 SKILL.md：{skills_root}，语义一致性未度量"
    report = SemanticConsistencyReport(
        skills_root=skills_root,
        total_skills=len(skills),
        semantic_gaps=gaps,
        high_severity_gaps=[g for g in gaps if g.severity in ("high", "critical")],
        consistency_score=(
            0.0 if problem else max(0.0, 100.0 - len(gaps) * 5)),
    )
    if problem:
        _log.warning("validate_semantic_consistency: %s", problem)
        report.issues = [problem]
    else:
        report.issues = _build_consistency_issues(report)
    report.suggestions = _build_consistency_suggestions()
    _attach_conflicts(report, skills)
    return report
def _keyword_coverage(keywords: list[str], query_lower: str) -> float:
    kw_set = {k.lower() for k in keywords if k}
    hits = sum(1 for k in kw_set if contains_term(k, query_lower))
    return hits / len(kw_set) if kw_set else 0.0
def _extract_keywords(text: str) -> list[str]:
    return [
        w
        for w in sorted(tokenize_words(text))
        if len(w) > 2 or (len(w) == 2 and has_cjk(w))
    ]
_DEFAULT_TOPK = 5
@dataclass
class SemanticMatchResult:
    skill_name: str = ""
    query: str = ""
    score: float = 0.0
    matched_keywords: list[str] = field(default_factory=list)
    reason: str = ""
@dataclass
class SkillSemanticIndex:
    skill_name: str = ""
    keywords: list[str] = field(default_factory=list)
class SemanticMatcher:
    def __init__(self) -> None:
        self._index: dict[str, SkillSemanticIndex] = {}
        self._descriptions: dict[str, str] = {}
    def build_index(self, skills_root: str | os.PathLike) -> None:
        descriptions = scan_skill_descriptions(skills_root)
        self._index.clear()
        self._descriptions = {}
        for name, desc in descriptions.items():
            self.register_skill(name, desc)
    def match(self, query: str, candidates: list[str]) -> list[tuple[str, float]]:
        query, candidates = self._normalize_match_inputs(query, candidates)
        if not query.strip() or not candidates:
            return []
        query_lower = query.lower()
        results: list[tuple[str, float]] = []
        for c in candidates:
            results.append((c, self._score_candidate(c, query, query_lower)))
        results.sort(key=lambda x: x[1], reverse=True)
        return results
    def rank_descriptions(
        self, query: str, topk: int = _DEFAULT_TOPK
    ) -> list[SemanticMatchResult]:
        query = query if isinstance(query, str) else ""
        topk = _normalize_topk(topk, "rank_descriptions topk")
        if not query.strip():
            return []
        query_lower = query.lower()
        scored = []
        for name, desc in self._descriptions.items():
            info = self._index.get(name)
            keyword_pool = (info.keywords if info is not None and info.keywords
                            else _extract_keywords(desc))
            scored.append((
                name,
                self._score_candidate(name, query, query_lower),
                [kw for kw in keyword_pool
                 if contains_term(kw, query_lower)],
            ))
        scored.sort(key=lambda item: item[1], reverse=True)
        return [
            SemanticMatchResult(
                skill_name=name,
                query=query,
                score=score,
                matched_keywords=matched_keywords,
                reason="语义相似度与关键词覆盖匹配",
            )
            for name, score, matched_keywords in scored[: max(0, topk)]
        ]
    def _score_candidate(
        self, name: str, query: str, query_lower: str,
    ) -> float:
        candidate_text = self._descriptions.get(name) or name
        score = jaccard(
            tokenize_words(query), tokenize_words(candidate_text))
        info = self._index.get(name)
        if info is not None and info.keywords:
            score = 0.5 * score + 0.5 * _keyword_coverage(
                info.keywords, query_lower)
        return score
    def _normalize_match_inputs(
        self, query, candidates
    ) -> tuple[str, list[str]]:
        query = query if isinstance(query, str) else ""
        candidate_list = _normalize_sequence_input(
            candidates, "match 入参 candidates"
        )
        if candidate_list is None:
            return query, []
        valid_candidates = _filter_items_by_type(
            candidate_list, str, "match 入参", "非 str 候选")
        return query, valid_candidates
    def register_skill(
        self, skill_name: str, description: str, keywords: list[str] | None = None
    ) -> None:
        skill_name = normalize_str(skill_name).strip()
        description = normalize_str(description)
        if not skill_name:
            _log.warning("SemanticMatcher.register_skill 拒绝空技能名")
            return
        kw = normalize_str_list(keywords) or _extract_keywords(description)
        self._descriptions[skill_name] = description
        self._index[skill_name] = SkillSemanticIndex(
            skill_name=skill_name,
            keywords=kw,
        )
def _normalize_topk(topk, label: str = "topk") -> int:
    if isinstance(topk, int) and not isinstance(topk, bool):
        return topk
    _log.warning(
        "%s 类型 %s 非法（应为 int），按默认 %d 处理",
        label, type(topk).__name__, _DEFAULT_TOPK,
    )
    return _DEFAULT_TOPK
def quick_match_skills(
    skills_root: str | os.PathLike, query: str = "", topk: int = _DEFAULT_TOPK
) -> list[SemanticMatchResult]:
    query = query if isinstance(query, str) else ""
    if not query:
        return []
    matcher = SemanticMatcher()
    matcher.build_index(skills_root)
    return matcher.rank_descriptions(query, topk)
_FIX_SCORE_THRESHOLD = 60.0
def apply_frontmatter_fix(skill_dir: str, overall_score: float) -> str:
    if not isinstance(skill_dir, (str, os.PathLike)):
        _log.warning("apply_frontmatter_fix 拒绝非路径入参: %r", skill_dir)
        return ""
    if isinstance(skill_dir, str) and not skill_dir.strip():
        _log.warning("apply_frontmatter_fix 拒绝空路径入参")
        return ""
    md_file = resolve_entry_document(skill_dir)
    if md_file is None:
        _log.warning("apply_frontmatter_fix 未找到入口文档: %s", skill_dir)
        return ""
    score = _normalize_matching_score(overall_score)
    if score is None or score >= _FIX_SCORE_THRESHOLD:
        _log.info(
            "apply_frontmatter_fix 跳过 %s：评分 %r 不在修复区间(<%.0f)",
            md_file, overall_score, _FIX_SCORE_THRESHOLD)
        return ""
    try:
        raw = md_file.read_bytes()
        text = raw.decode("utf-8-sig")
        had_bom = raw.startswith(b"\xef\xbb\xbf")
        frontmatter = parse_frontmatter_dict(text)
        if not frontmatter:
            _log.info("apply_frontmatter_fix 跳过 %s：未解析到 frontmatter", md_file)
            return ""
        name = (normalize_str(frontmatter.get("name")).strip()
                or Path(skill_dir).name)
        description = normalize_description_field(frontmatter.get("description"))
        keywords = frontmatter_keywords(frontmatter.get("keywords"))
        category = normalize_str(frontmatter.get("category"))
        opt_result = SkillMetadataOptimizer().optimize(
            skill_name=name,
            description=description,
            skill_type=category,
            user_keywords=keywords,
        )
        new_text = merge_frontmatter_desc_keywords(text, opt_result, str(md_file))
        if new_text is None:
            return ""
        write_markdown_text(md_file, new_text, had_bom, newline="")
        return (f"frontmatter优化(评分{score:.0f}→触发分"
                f"{opt_result.trigger_score:.0f})")
    except Exception as exc:  # noqa: BLE001
        _log.warning(
            "apply_frontmatter_fix 降级跳过 %s: %s: %s",
            md_file, type(exc).__name__, exc, exc_info=True)
        return ""
def validate_creation_inputs(skill_name: str, description: str
                             ) -> tuple[str, str, dict | None]:
    skill_name = normalize_str(skill_name)
    description = normalize_str(description)
    pre_issues = validate_create_input(skill_name, description)
    if pre_issues:
        _log.warning("[SkillCreation] 源头预检失败，创建流程拦截: skill=%s, issues=%s",
                     skill_name, pre_issues)
        return skill_name, description, {
            "ok": False, "error": "源头预检失败", "issues": pre_issues,
        }
    return skill_name, description, None
def build_creation_semantic_index(skill_name: str,
                                  opt_result: MetadataOptimizationResult) -> dict:
    skill_name = normalize_str(skill_name).strip()
    if not skill_name:
        _log.warning("build_creation_semantic_index 拒绝空技能名")
        return {"skill_name": "", "registered": False, "match_results": []}
    if not isinstance(opt_result, MetadataOptimizationResult):
        _log.warning(
            "build_creation_semantic_index 拒绝非 MetadataOptimizationResult: %s，"
            "按未注册处理", type(opt_result).__name__)
        return {
            "skill_name": skill_name,
            "registered": False,
            "match_results": [],
        }
    matcher = SemanticMatcher()
    matcher.register_skill(
        skill_name=skill_name,
        description=opt_result.optimized_description,
        keywords=opt_result.optimized_keywords,
    )
    match_results = matcher.match(
        opt_result.optimized_description, [skill_name])
    return {
        "skill_name": skill_name,
        "registered": True,
        "match_results": match_results,
    }
def generate_optimized_frontmatter(
        name: str,
        display_name: str,
        description: str,
        skill_type: str) -> tuple[str, list[str]]:
    name = normalize_str(name).strip()
    display_name = normalize_str(display_name).strip()
    description = normalize_str(description).strip()
    if not description:
        subject = display_name or name
        description = f"{subject} 技能" if subject else "通用技能"
    metadata_opt = SkillMetadataOptimizer()
    opt_result = metadata_opt.optimize(
        skill_name=name,
        description=description,
        skill_type=skill_type,
    )
    optimized_description = opt_result.optimized_description
    optimized_keywords = opt_result.optimized_keywords
    optimized_description = AttentionSegmentOptimizer().optimize(
        optimized_description, optimized_keywords
    )
    return optimized_description, optimized_keywords
def _safe_lower(text: str) -> str:
    lowered = text.lower()
    if len(lowered) == len(text):
        return lowered
    return "".join(ch.lower() if len(ch.lower()) == 1 else ch for ch in text)
_CJK_CHAR_RE = re.compile(r"[\u3400-\u4dbf\u4e00-\u9fff]")
_ASCII_ALPHA_CHAR_RE = re.compile(r"[A-Za-z]")
def _is_cjk_dominant(text: str) -> bool:
    cjk = len(_CJK_CHAR_RE.findall(text))
    if cjk == 0:
        return False
    return cjk >= len(_ASCII_ALPHA_CHAR_RE.findall(text))
_TRIGGER_PREFIX_CJK_TEMPLATE = "当用户要求{action}时触发此技能。"
_TRIGGER_PREFIX_CJK_GENERIC = "当用户需要相关任务时触发此技能。"
_TRIGGER_PREFIX_EN_TEMPLATE = "Trigger this skill when the user asks to {action}. "
_TRIGGER_PREFIX_EN_GENERIC = "Trigger this skill when the user needs the related task. "
def _trigger_prefix_for(description: str, core_action: str) -> str:
    action = normalize_str(core_action).strip()
    if action and not action.isascii():
        return _TRIGGER_PREFIX_CJK_TEMPLATE.format(action=action)
    if action:
        return _TRIGGER_PREFIX_EN_TEMPLATE.format(action=action)
    if _is_cjk_dominant(description):
        return _TRIGGER_PREFIX_CJK_GENERIC
    return _TRIGGER_PREFIX_EN_GENERIC
ATTENTION_DILUTERS = [
    "basically", "actually", "simply", "essentially", "generally",
    "基本上", "实际上", "简单来说", "本质上", "一般来说",
    "various", "multiple", "several",
    "各种", "多种", "若干", "一些",
    "etc", "and so on", "and more",
    "等等", "以及其他", "等诸如此类",
]
_MUST_CUES: tuple[str, ...] = (
    "MUST", "ALWAYS", "REQUIRED", "必须", "务必", "强制", "一定",
)
_MUST_CUE_RE = re.compile(
    "|".join(
        rf"(?<!不){cue}" if not cue.isascii() else word_pattern(cue)
        for cue in _MUST_CUES
    ),
    re.IGNORECASE,
)
_NEGATIVE_CUES_ASCII: tuple[str, ...] = (
    "NOT for", "DO NOT", "NEVER", "ONLY for", "Exclusively", "Strictly",
)
_NEGATIVE_CUES_CJK: tuple[str, ...] = CN_EXCLUSION_HEADS
_NEGATIVE_CUE_ASCII_ALT = "|".join(c.replace(" ", r"\s+") for c in _NEGATIVE_CUES_ASCII)
_NEGATIVE_CUE_CJK_ALT = "|".join(_NEGATIVE_CUES_CJK)
_NEGATIVE_CUE_SEARCH_RE = re.compile(
    rf"\b(?:{_NEGATIVE_CUE_ASCII_ALT})\b|{_NEGATIVE_CUE_CJK_ALT}",
    re.IGNORECASE,
)
def _has_negative_scope(text: str) -> bool:
    if not isinstance(text, str) or not text.strip():
        return False
    text = _NEGATED_REQUIREMENT_RE.sub(" ", text)
    if _NEGATIVE_CUE_SEARCH_RE.search(text):
        return True
    return bool(extract_negated_terms(text, NEGATION_PATTERNS))
PICKING_CUES = [
    *_MUST_CUES, *_NEGATIVE_CUES_ASCII, *_NEGATIVE_CUES_CJK,
]
_TRIGGER_RES: tuple[re.Pattern[str], ...] = (
    re.compile(r"\b(trigger|activate|use|call|invoke)\s+"
               r"(?:this\s+skill(?![A-Za-z0-9_-])[\s,，]*(?:when|if|for|to)?"
               r"|this\s+(?:when|if|for|to)"
               r"|(?:when|if|for|to))(?![A-Za-z0-9_])"),
    re.compile(r"(加载|激活|使用|调用)\s*"
               r"(?:this\s+skill(?![A-Za-z0-9_-])|此技能|本技能)\s*(?:当|如果|以)?"),
)
_NEGATIVE_DEFENSE_RES: tuple[re.Pattern[str], ...] = (
    re.compile(rf"\b({_NEGATIVE_CUE_ASCII_ALT})\b[\s\w,:：；;，.]+",
               re.IGNORECASE),
    re.compile(rf"({_NEGATIVE_CUE_CJK_ALT})[\s\w,:：；;，.]+",
               re.IGNORECASE),
)
_USER_PHRASE_RES: tuple[re.Pattern[str], ...] = tuple(
    re.compile(p) for p in (
        r"帮我", r"能不能", r"如何", r"给我", r"我想",
        r"how\s+do\s+i", r"can\s+you\s+help", r"please\s+help",
    )
)
_DILUTER_RES: tuple[re.Pattern[str], ...] = tuple(
    re.compile(word_pattern(diluter), re.IGNORECASE)
    for diluter in ATTENTION_DILUTERS
)
ATTENTION_ESCAPE_PATTERNS = [
    r".{80,}",
    r"\([^)]{50,}\)",
    r"\[[^\]]{50,}\]",
    r"\{[^}]{50,}\}",
]
_ESCAPE_RES = tuple(re.compile(p) for p in ATTENTION_ESCAPE_PATTERNS)
_ATTENTION_GOLDEN_WINDOW_CHARS = 200
ATTENTION_SEGMENT_WEIGHTS = {
    "trigger_when": 3.0,
    "must_always": 5.0,
    "action_verb": 2.5,
    "negative_defense": 4.0,
    "user_phrase": 1.5,
    "vague_filler": -2.0,
    "overlong_clause": -3.0,
}
@dataclass
class AttentionSegment:
    text: str = ""
    start_pos: int = 0
    end_pos: int = 0
    segment_type: str = ""
    weight: float = 0.0
    is_picking_cue: bool = False
@dataclass
class AttentionSegmentReport:
    skill_name: str = ""
    description: str = ""
    overall_attention_score: float = 0.0
    picking_conversion_rate: float = 0.0
    dilution_score: float = 0.0
    golden_window_score: float = 0.0
    segments: list[AttentionSegment] = field(default_factory=list)
    issues: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
    optimized_description: str = ""
class AttentionSegmentOptimizer:
    @staticmethod
    def _compute_attention_score(segments: list[AttentionSegment]) -> float:
        positive_weight = sum(s.weight for s in segments if s.weight > 0)
        return min(100.0, positive_weight * 8)
    @staticmethod
    def _compute_picking_conversion(segments: list[AttentionSegment]) -> float:
        if not segments:
            return 0.0
        picking = sum(1 for s in segments if s.is_picking_cue)
        return min(100.0, picking * 25)
    @staticmethod
    def _compute_dilution_score(segments: list[AttentionSegment]) -> float:
        hits = sum(1 for s in segments if s.segment_type in
                   ("vague_filler", "overlong_clause"))
        return min(100.0, hits * 15)
    @classmethod
    def _compute_golden_window(cls, description: str) -> float:
        golden = description[:_ATTENTION_GOLDEN_WINDOW_CHARS]
        golden_segments = cls._extract_segments(golden)
        golden_picking = sum(1 for s in golden_segments if s.is_picking_cue)
        golden_attention = sum(s.weight for s in golden_segments if s.weight > 0)
        return min(100.0, golden_attention * 10 + golden_picking * 15)
    def analyze(self, skill_name: str, description: str,
                keywords: list[str] | None = None) -> AttentionSegmentReport:
        skill_name = normalize_str(skill_name)
        description = normalize_str(description)
        report = AttentionSegmentReport(
            skill_name=skill_name,
            description=description,
        )
        keywords = normalize_str_list(keywords)
        segments = self._extract_segments(description)
        report.segments = segments
        report.overall_attention_score = self._compute_attention_score(segments)
        report.picking_conversion_rate = self._compute_picking_conversion(segments)
        report.dilution_score = self._compute_dilution_score(segments)
        report.golden_window_score = self._compute_golden_window(description)
        report.issues = self._generate_issues(report)
        report.suggestions = self._generate_suggestions(report, description)
        report.optimized_description = self.optimize(description, keywords)
        return report
    @staticmethod
    def _collect_segments(text: str, matches, segment_type: str, *,
                          is_picking_cue: bool = False,
                          tail_chars: int = 0) -> list[AttentionSegment]:
        weight = ATTENTION_SEGMENT_WEIGHTS[segment_type]
        segments: list[AttentionSegment] = []
        for m in matches:
            end = min(m.end() + tail_chars, len(text))
            segments.append(AttentionSegment(
                text=text[m.start():end], start_pos=m.start(), end_pos=end,
                segment_type=segment_type, weight=weight,
                is_picking_cue=is_picking_cue))
        return segments
    @classmethod
    def _pattern_segments(cls, text: str, patterns, segment_type: str, *,
                          search_text: str | None = None,
                          **kwargs) -> list[AttentionSegment]:
        haystack = text if search_text is None else search_text
        matches = (m for pattern in patterns for m in pattern.finditer(haystack))
        return cls._collect_segments(text, matches, segment_type, **kwargs)
    @classmethod
    def _extract_action_verb_segments(cls, text: str,
                                      text_lower: str) -> list[AttentionSegment]:
        matches = (m for verb in CORE_ACTION_VERBS
                   for m in re.finditer(word_pattern(verb), text_lower))
        return cls._collect_segments(text, matches, "action_verb")
    @staticmethod
    def _deduplicate_segments(segments: list[AttentionSegment]) -> list[AttentionSegment]:
        seen = set()
        unique = []
        for seg in sorted(segments, key=lambda s: s.start_pos):
            key = (seg.start_pos, seg.segment_type)
            if key not in seen:
                seen.add(key)
                unique.append(seg)
        return unique
    @classmethod
    def _extract_segments(cls, description: str) -> list[AttentionSegment]:
        text_lower = _safe_lower(description)
        positive_text = _mask_negated_context(description)
        positive_lower = _safe_lower(positive_text)
        segments: list[AttentionSegment] = []
        segments.extend(cls._pattern_segments(
            description, _TRIGGER_RES, "trigger_when", search_text=positive_lower))
        segments.extend(cls._collect_segments(
            description, _MUST_CUE_RE.finditer(positive_text), "must_always",
            is_picking_cue=True))
        segments.extend(cls._extract_action_verb_segments(description, positive_lower))
        segments.extend(cls._pattern_segments(
            description, _NEGATIVE_DEFENSE_RES, "negative_defense",
            search_text=text_lower, is_picking_cue=True, tail_chars=30))
        segments.extend(cls._pattern_segments(
            description, _USER_PHRASE_RES, "user_phrase", search_text=text_lower))
        segments.extend(cls._pattern_segments(
            description, _DILUTER_RES, "vague_filler", search_text=text_lower))
        segments.extend(cls._pattern_segments(
            description, _ESCAPE_RES, "overlong_clause"))
        return cls._deduplicate_segments(segments)
    @staticmethod
    def _generate_issues(report: AttentionSegmentReport) -> list[str]:
        has_picking_in_golden = any(
            s.is_picking_cue and s.start_pos < _ATTENTION_GOLDEN_WINDOW_CHARS
            for s in report.segments)
        conditions = (
            (report.golden_window_score < 50,
             (f"黄金窗口（前{_ATTENTION_GOLDEN_WINDOW_CHARS}字符）缺乏足够的选择引导，"
              "Agent可能在快速浏览时跳过此技能")),
            (report.picking_conversion_rate < 30,
             "注意力→选择转化率低：描述吸引了注意力但缺少明确的选择信号（picking cues）"),
            (report.dilution_score > 40,
             "注意力稀释严重：描述中包含模糊填充词或过长从句，分散了核心选择信号"),
            (not has_picking_in_golden,
             (f"黄金窗口（前{_ATTENTION_GOLDEN_WINDOW_CHARS}字符）内缺少选择引导词"
              "（如MUST/ALWAYS/ONLY），Agent难以在浏览时确认此技能")),
        )
        return [message for failed, message in conditions if failed]
    @staticmethod
    def _generate_suggestions(report: AttentionSegmentReport, description: str) -> list[str]:
        conditions = (
            (report.golden_window_score < 60,
             "[注意力段] 在description前30字符内嵌入'Trigger when + MUST call'的选择引导"),
            (report.picking_conversion_rate < 40,
             "[选择转化] 添加1-2个明确的选择引导词（如'Use this skill ONLY for...'/'必须调用此技能以...'）"),
            (report.dilution_score > 30,
             "[稀释消除] 删除'相关/各种/等等'等模糊填充词，每个句子只传递一个核心选择信号"),
            (len(description) > _ATTENTION_GOLDEN_WINDOW_CHARS,
             (f"[长度控制] 将description压缩到{_ATTENTION_GOLDEN_WINDOW_CHARS}字符以内，"
              "确保核心选择信号在注意力窗口内")),
            (not any(s.segment_type == "negative_defense" for s in report.segments),
             "[对比度增强] 添加NOT for/不要用于声明，通过高对比度阻断错误选择路径"),
        )
        suggestions = [message for needed, message in conditions if needed]
        return suggestions + [
            "[注意力段理论] 遵循'每段一个信号'原则：将多个功能点拆分为独立的注意力段，避免信息过载"
        ]
    def optimize(self, description: str,
                 keywords: list[str] | None = None) -> str:
        desc = normalize_str(description).strip()
        if not desc:
            return desc
        keywords = normalize_str_list(keywords)
        desc = self._ensure_trigger_prefix(desc)
        desc = self._insert_must_cue(desc)
        desc = self._strip_diluters(desc)
        desc = truncate_keep_negative(desc, DESCRIPTION_MAX_LEN)
        desc = self._append_negative_defense(desc, keywords)
        return desc.strip()
    @staticmethod
    def _ensure_trigger_prefix(desc: str) -> str:
        desc = _reorder_leading_negative(desc)
        positive_desc = _positive_trigger_subject(
            _mask_negated_context(desc).lstrip(" \t\r\n.。!！?？；;"))
        if _TRIGGER_PREFIX_PRESENT_RE.search(positive_desc):
            return desc
        if not positive_desc:
            return _trigger_prefix_for(desc, "") + desc
        core_action = AttentionSegmentOptimizer._extract_core_action(positive_desc)
        return _trigger_prefix_for(positive_desc, core_action) + desc
    @staticmethod
    def _insert_must_cue(desc: str) -> str:
        if _MUST_CUE_RE.search(_mask_negated_context(desc)):
            return desc
        first_period = find_first_sentence_period(desc)
        if first_period < 0:
            stripped = desc.rstrip()
            if not stripped:
                return desc
            separator = (" " if stripped.endswith(("!", "?", "！", "？"))
                         else ". ")
            return stripped + separator + _MUST_CALL_CUE
        insertion = " " + _MUST_CALL_CUE
        head, tail = desc[:first_period + 1], desc[first_period + 1:]
        if tail and not tail[0].isspace():
            tail = " " + tail
        return head + insertion + tail
    @staticmethod
    def _strip_diluters(desc: str) -> str:
        for pattern in _DILUTER_RES:
            desc = pattern.sub("", desc, count=0)
        desc = re.sub(r"([.。!！?？])\s*[、,，:：;；]+\s*", r"\1 ", desc)
        desc = re.sub(r"([、,，:：;；])\s*[、,，:：;；]+\s*", r"\1 ", desc)
        desc = re.sub(r"[、,，:：;；]+\s*(?=[.。!！?？])", "", desc)
        desc = re.sub(r"[、,，]\s*$", "", desc)
        desc = re.sub(
            r"(?<![。!！?？])([。!！?？])\s*[。!！?？](?![。!！?？])", r"\1", desc)
        desc = re.sub(r"  +", " ", desc)
        desc = re.sub(
            r" +([、,，:：;；.。!！?？])(?![、,，:：;；.。!！?？])", r"\1", desc)
        desc = re.sub(r"^[、,，:：;；.。!！?？]+\s*", "", desc)
        return desc.strip()
    @staticmethod
    def _append_negative_defense(desc: str, keywords: list[str]) -> str:
        if _has_negative_scope(desc):
            return desc
        negatives = AttentionSegmentOptimizer._generate_negatives(desc, keywords)
        if not negatives:
            return desc
        candidate = re.sub(
            r"[.。!！?？~～;；:：,，、 ]+$", "", desc
        ) + f". NOT for: {negatives}."
        return truncate_keep_negative(candidate, DESCRIPTION_MAX_LEN)
    @staticmethod
    def _extract_core_action(desc: str) -> str:
        best_verb = ""
        best_pos = len(desc) + 1
        for v in CORE_ACTION_VERBS:
            m = re.search(word_pattern(v), desc, flags=re.IGNORECASE)
            if m is not None and m.start() < best_pos:
                best_pos = m.start()
                best_verb = v
        return best_verb
    @staticmethod
    def _generate_negatives(description: str, keywords: list[str]) -> str:
        explicit = extract_negated_terms(description, NEGATION_PATTERNS)
        if explicit:
            return "; ".join(explicit[:3])
        terms = [
            kw for kw in normalize_str_list(keywords)
            if kw and kw.lower() not in _CORE_ACTION_VERBS_LOWER
        ]
        if not terms:
            return ""
        sample = terms[:3]
        # 语言判定必须剔除 _insert_must_cue 注入的英文提示：该提示固定为英文，
        # 会把中文描述的拉丁字母占比抬高，导致 NOT-for 尾句语言与描述不一致。
        language_probe = description.replace(_MUST_CALL_CUE, " ")
        if _is_cjk_dominant(language_probe):
            return "、".join(f"{term}之外的任务" for term in sample)
        return "; ".join(f"tasks other than {term}" for term in sample)

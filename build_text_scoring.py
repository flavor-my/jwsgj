from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import re
import unicodedata
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field
from functools import cache, lru_cache
from pathlib import Path
from typing import Any, Self

from jwsgj.build_text_document import (
    DOMAIN_KEYWORDS,
    SKILL_ACTION_VERBS,
    SLOT_NOISE_CHARS,
    detect_text_language,
    find_first_sentence_period,
    has_cjk,
    jaccard,
    match_domain,
    readable_skill_name,
    safe_text,
    word_pattern,
)
from jwsgj.build_text_frontmatter import (
    UPLOAD_ALLOWED_FIELDS,
    UPLOAD_DESC_MAX_CHARS,
    parse_frontmatter_dict,
    parse_skill_md_text,
    read_skill_md,
)
from jwsgj.diag_guard_io import (
    guarded_open,
    normalize_out_path,
)
from jwsgj.diag_guard_state import (
    serialize_json,
)
from jwsgj.diag_types_defs import (
    DocQualityIssue,
    SubDimensionScore,
    make_matching_issue,
)
from jwsgj.diag_types_normalize import (
    normalize_entry_inputs,
    yaml_safe_desc_line,
    yaml_safe_quote,
)
from jwsgj.diag_types_vocab import (
    CAT_CROSS_VALIDATION,
    CAT_DISCOVERABILITY,
    DESC_MAX,
    FIELD_CAPABILITY_COVERAGE,
    FIELD_SYNONYM_COVERAGE,
    FIELD_TRIGGER_EXAMPLES,
    MANDATORY_PIPELINE_TRIGGER_KEYWORDS,
    MAX_SKILL_NAME_LENGTH,
    SKILL_MD_LINE_LIMIT,
    SKILL_NAME_MIN_LEN,
)
from jwsgj.log_config import (
    log_swallowed,
)
from jwsgj.runtime_paths import (
    sanitize_skill_name,
    trigger_keywords_path,
)
from jwsgj.runtime_scope import (
    normalize_text,
)

KEYWORD_NOISE = frozenset({
    "the", "and", "for", "get", "set", "run", "new", "all", "any",
    "not", "工具", "辅助", "通用", "相关", "其他",
})
_DERIVED_CACHE_MAX_ENTRIES = 256
__all__ = [
    'ANCHOR_RELATION_MARKERS',
    'CN_EXCLUSION_HEADS',
    'COLLOQUIAL_TRIGGER_WORDS',
    'CONTENT_QUALITY_RULES',
    'DEFAULT_NUM_NEGATIVE',
    'DEFAULT_NUM_POSITIVE',
    'DESC_MAX_LENGTH',
    'DESC_MIN_LENGTH',
    'DESC_OPTIMAL_MIN',
    'DOMAIN_HINT_TO_TYPE_KEY',
    'DOMAIN_NEGATIVES',
    'EXTENSION_ALTERNATION',
    'FILE_EXTENSION_PATTERN',
    'GENERIC_EXTENSION_ALTERNATION',
    'GRADE_BANDS_RATIO',
    'KEYWORD_NOISE',
    'LOW_TRIGGER_SCORE',
    'MANDATORY_PIPELINE_TRIGGER_KEYWORDS',
    'NEGATION_PATTERNS',
    'NEGATIVE_COMMANDS',
    'PIPELINE_TRIGGER_KEYWORDS',
    'QUALITY_WEIGHTS',
    'RE_CHINESE_CHARS',
    'ROLE_PERSPECTIVES',
    'SIX_DIM_SPECS',
    'SIX_DIM_WEIGHTS',
    'SPOKEN_PATTERNS',
    'STANDARD_SECTIONS',
    'TRIGGER_COMMANDS',
    'TRIGGER_CONTEXT_TOKENS',
    'TRIGGER_EXAMPLE_TEMPLATES',
    'TRIGGER_FUZZY_MIN_LEN',
    'TRIGGER_FUZZY_MIN_SCORE',
    'TRIGGER_FUZZY_SEEDS',
    'TRIGGER_NEGATIVE_CONTEXTS',
    'TRIGGER_WEAK_TOKENS',
    'TYPE_ACTION_WORDS',
    'TYPE_KEYWORDS',
    'UPLOAD_COMPLIANCE_RULES',
    'VAGUE_WORDS',
    'VERB_SYNONYM_EXPANSION',
    '_GENERIC_USAGE_RE',
    'DeduplicationReport',
    'OverlapPair',
    'SkillDeduplicationEngine',
    'SkillFingerprint',
    'TriggerVocabulary',
    'anchor_entries',
    'anchor_section_cut',
    'band_to_grade',
    'best_keyword_match',
    'build_skill_frontmatter',
    'check_atomic_responsibility',
    'check_description_length',
    'count_keyword_hits',
    'declared_extensions',
    'derive_skill_anchors',
    'detect_vague_words',
    'evaluate_multilingual_coverage',
    'export_merge_plan',
    'extract_boundary_scopes',
    'extract_negated_terms',
    'extract_skill_fingerprint',
    'fix_upload_violation_descs',
    'generate_trigger_examples',
    'get_content_quality_rules',
    'get_standard_sections',
    'get_upload_compliance_rules',
    'infer_skill_type',
    'keyword_matches',
    'load_custom_trigger_keywords',
    'load_skill_trigger_vocabulary',
    'match_pipeline_trigger',
    'matching_dimensions',
    'md_escape_cell',
    'negative_query_for_boundary',
    'normalize_bool_flag',
    'normalize_descriptions',
    'normalize_keywords',
    'normalize_nonnegative_count',
    'normalize_suggestion_text',
    'normalize_trigger_text',
    'probe_pipeline_trigger',
    'resolve_domain_key',
    'run_deduplication',
    'sanitize_upload_description',
    'scan_skill_deduplication',
    'score_to_grade',
    'seed_token_pairs',
    'stem_matches',
    'text_token_count',
    'trigger_tokens',
    'validate_pipeline_trigger_contract',
    'word_tokens',
]
_log = logging.getLogger(__name__)
_SKILLOPS_ACTION_WORD = "创建、诊断、进化、重构和优化 Agent Skills"
TYPE_ACTION_WORDS: dict[str, str] = {
    "docx": "创建或编辑 Word (.docx) 文档",
    "xlsx": "创建、编辑或分析 Excel (.xlsx) 电子表格",
    "pptx": "创建或编辑 PowerPoint (.pptx) 演示文稿",
    "pdf": "读取、创建、编辑或转换 PDF 文件",
    "browser": "通过浏览器进行网页交互、信息检索、表单填写",
    "code_diag": "对 Python 代码进行全量深度诊断、质量评分和反模式检测",
    "memory": "管理跨会话的经验记忆、行为约束和交付检查",
    "skill": _SKILLOPS_ACTION_WORD,
    "skillops": _SKILLOPS_ACTION_WORD,
    "generic": "执行特定领域的专业任务",
}
RE_CHINESE_CHARS = r"[\u4e00-\u9fff]"
_ASCII_WORD_RE = re.compile(r"[A-Za-z]")
TRIGGER_COMMANDS = [
    "MUST USE",
    "MUST BE INVOKED",
    "ALWAYS LOAD",
    "CRITICAL TRIGGER",
    "PRIORITY LOAD",
]
_TRIGGER_COMMAND_PREFIX_RE = re.compile(
    r"^\s*(?:\[\s*)?(?:"
    + "|".join(re.escape(command) for command in TRIGGER_COMMANDS)
    + r")(?:\s*\])?(?:\s*[:：.。,，;；]+)?\s*",
    re.IGNORECASE,
)
DOMAIN_NEGATIVES = {
    "docx": ["PDF creation", "image editing", "video processing", "database queries"],
    "xlsx": ["PDF creation", "image editing", "document formatting", "presentation design"],
    "pptx": ["image editing alone", "database queries", "plain text documentation"],
    "pdf": ["Word document editing", "Excel analysis", "image editing", "presentation design"],
    "browser": ["local file operations", "system administration", "code editing"],
    "code_diag": ["document editing", "spreadsheet processing", "web browsing", "image editing"],
    "memory": ["document formatting", "file conversion", "web scraping", "image generation"],
    "skillops": ["document editing", "data analysis", "web browsing", "image generation"],
    "generic": ["tasks outside the explicitly stated scope"],
}
QUALITY_WEIGHTS = {
    "has_trigger_command": 0.15,
    "has_scenario_boundary": 0.15,
    "has_keywords_coverage": 0.10,
    "has_negative_rule": 0.15,
    "has_trigger_example": 0.10,
    "length_optimal": 0.05,
    "specificity": 0.15,
    "differentiation": 0.10,
    "spoken_coverage": 0.05,
}
LOW_TRIGGER_SCORE = 70
DESC_MIN_LENGTH = 80
DESC_MAX_LENGTH = 400
DESC_OPTIMAL_MIN = 150
VAGUE_WORDS: tuple[str, ...] = (
    "powerful", "flexible", "useful", "helpful", "comprehensive",
    "强大的", "灵活的", "好用的", "全面的", "综合的", "完善的",
    "various", "multiple", "many", "things", "stuff",
    "各种", "多种", "很多", "一些", "相关",
)
TRIGGER_EXAMPLE_TEMPLATES = {
    "code_review": [
        "帮我看看这段代码有啥问题",
        "检查一下这个项目的代码质量",
        "做个code review",
        "review一下最近提交的代码",
        "帮我审审这段逻辑有没有坑",
        "code review一下",
    ],
    "dead_code": [
        "扫描一下有没有死代码",
        "找找没用的代码和文件",
        "清理一下冗余的代码",
        "dead code detection帮我跑一下",
        "哪些代码从来没被调用过",
    ],
    "antipattern": [
        "检测一下反模式",
        "看看代码有没有坏味道",
        "code smell检测",
        "antipattern scan跑一下",
    ],
    "security": [
        "做个安全审计",
        "扫描敏感信息泄露",
        "检查有没有路径穿越漏洞",
        "security audit一下",
        "检查密钥有没有泄露",
    ],
    "auto_fix": [
        "自动修复这个问题",
        "帮我改改这个bug",
        "auto fix一下",
        "生成修复方案",
        "自动修好",
    ],
    "skill_ops": [
        "创建一个新技能",
        "帮我写个skill",
        "新建一个技能",
        "skill creation",
        "重构这个技能",
        "优化skill文档",
        "给这个技能做个体检",
        "提升技能质量",
    ],
    "testing": [
        "测试覆盖率怎么样",
        "跑一下测试",
        "做回归验证",
        "test coverage check",
    ],
    "scoring": [
        "评估代码复杂度",
        "算算代码评分",
        "代码质量打分",
        "code quality score",
        "这个项目健康度怎么样",
        "代码体检",
    ],
    "full_diag": [
        "做一次全面诊断",
        "full diagnostic",
        "给项目做个体检",
        "全面扫描一下",
    ],
    CAT_CROSS_VALIDATION: [
        "交叉验证一下",
        "多源验证",
        "cross validation",
        "结果仲裁一下",
    ],
    "generic": [
        "帮我处理一下",
        "我需要用这个技能",
        "请帮我完成这项任务",
        "怎么做这个",
        "帮我看一下",
        "帮我做这个",
    ],
}
ANCHOR_RELATION_MARKERS: tuple[str, ...] = (
    "配合使用", "前后衔接", "工具链", "协同使用",
    "works with", "works alongside", "paired with",
)
_ANCHOR_NAME_PATTERN = r"[A-Za-z][A-Za-z0-9_.-]{1,63}|[\u4e00-\u9fff]{2,20}"
_ANCHOR_SENTENCE_SPLIT_RE = re.compile(r"[。；;！!？?\n]")
_ANCHOR_TAG_RE = re.compile(r"#[A-Za-z0-9_\-\u4e00-\u9fff]+")
_ANCHOR_SECTION_COLON_RE = re.compile(r"\s*[:：]")
_ANCHOR_NAME_STOPWORDS = frozenset({
    "本技能", "该技能", "此技能", "其他技能", "技能", "用户",
    "this skill", "the skill",
})
@cache
def _anchor_relation_patterns() -> tuple[tuple[str, re.Pattern[str]], ...]:
    patterns: list[tuple[str, re.Pattern[str]]] = []
    for marker in ANCHOR_RELATION_MARKERS:
        if marker.isascii():
            patterns.append((marker, re.compile(
                re.escape(marker) + r"\s+(" + _ANCHOR_NAME_PATTERN + r")",
                re.IGNORECASE)))
        else:
            patterns.append((marker, re.compile(
                r"与\s*(" + _ANCHOR_NAME_PATTERN + r")\s*" + re.escape(marker),
                re.IGNORECASE)))
    return tuple(patterns)
def derive_skill_anchors(text: Any) -> dict[str, dict[str, Any]]:
    normalized = normalize_text(text)
    if not normalized:
        return {}
    anchors: dict[str, dict[str, Any]] = {}
    for marker, pattern in _anchor_relation_patterns():
        for match in pattern.finditer(normalized):
            name = match.group(1).strip()
            if not name or name.casefold() in _ANCHOR_NAME_STOPWORDS:
                continue
            key = name.casefold()
            if key in anchors:
                continue
            sentence = next(
                (chunk.strip()
                 for chunk in _ANCHOR_SENTENCE_SPLIT_RE.split(normalized)
                 if match.group(0) in chunk),
                normalized)
            anchors[key] = {
                "name": name,
                "relation": marker,
                "scenario": sentence,
                "tags": sorted(set(_ANCHOR_TAG_RE.findall(sentence))),
            }
    return anchors
def anchor_entries(anchors: Any) -> list[dict]:
    catalog = {} if anchors is None else anchors
    if not isinstance(catalog, Mapping):
        _log.warning("锚点词表需为映射，收到 %s，按空词表处理",
                     type(catalog).__name__)
        return []
    entries: list[dict] = []
    for entry in catalog.values():
        if not isinstance(entry, Mapping):
            continue
        anchor_name = entry.get("name")
        if not isinstance(anchor_name, str) or not anchor_name.strip():
            continue
        anchor_name = anchor_name.strip()
        tags = entry.get("tags", [])
        if isinstance(tags, str):
            tags = [tags]
        elif isinstance(tags, (set, frozenset)):
            tags = sorted(tags, key=repr)
        elif not isinstance(tags, (list, tuple)):
            tags = []
        entries.append(dict(entry, name=anchor_name, tags=[
            tag.strip() for tag in tags
            if isinstance(tag, str) and tag.strip()]))
    return entries
def anchor_section_cut(text: Any) -> int:
    normalized = normalize_text(text)
    if not normalized:
        return -1
    cut = -1
    for _marker, pattern in _anchor_relation_patterns():
        for match in pattern.finditer(normalized):
            if not _ANCHOR_SECTION_COLON_RE.match(normalized, match.end()):
                continue
            if cut < 0 or match.start() < cut:
                cut = match.start()
    return cut
SIX_DIM_WEIGHTS: dict[str, float] = {
    "bilingual": 0.15, FIELD_SYNONYM_COVERAGE: 0.10, "user_examples": 0.20,
    "role_perspective": 0.15, FIELD_CAPABILITY_COVERAGE: 0.25, "skill_anchors": 0.15,
}
SIX_DIM_SPECS: tuple[tuple[str, str, float], ...] = (
    ("bilingual", "① 中英文双语", 0.6),
    (FIELD_SYNONYM_COVERAGE, "② 口语化近义词", 0.6),
    ("user_examples", "③ 用户指令覆盖", 0.6),
    ("role_perspective", "④ 角色视角分层", 0.5),
    (FIELD_CAPABILITY_COVERAGE, "⑤ 业务功能覆盖", 0.6),
    ("skill_anchors", "⑥ 关联锚点+标签", 0.4),
)
NEGATIVE_COMMANDS = ['NOT FOR', 'DO NOT USE FOR', 'NEVER INVOKE FOR', '严禁用于', '不适用于', '不处理']
CN_EXCLUSION_HEADS: tuple[str, ...] = (
    "仅限于", "不适用于", "不适用", "不支持", "不负责", "不涉及",
    "不包含", "不包括", "不允许", "不接受", "不要", "禁止", "请勿",
)
_CN_NEGATION_HEADS: tuple[str, ...] = tuple(sorted(
    {*CN_EXCLUSION_HEADS, "不是", "不属于", "不处理", "不覆盖", "不做", "不用于", "不应"},
    key=len, reverse=True,
))
_CN_ACTION_WORDS = frozenset(
    word for word in SKILL_ACTION_VERBS if not word.isascii()
).union({
    "修复", "修理", "读取", "打开", "操作", "输出", "新建", "导出",
    "发布", "清理", "扫描", "检测", "审查", "审核", "校验", "评估",
    "使用", "调用", "加载", "提供", "覆盖", "适用", "负责", "涉及",
    "包含", "包括", "兼容", "允许", "接受", "支持",
})
_CN_ACTION_VERB_ALT = "|".join(re.escape(word) for word in sorted(
    _CN_ACTION_WORDS, key=len, reverse=True))
_CN_BARE_NOT_ACTION_VERB_ALT = "|".join(re.escape(word) for word in sorted(
    _CN_ACTION_WORDS - {"处理", "支持", "负责", "涉及", "包含", "包括", "允许", "接受", "用于"},
    key=len, reverse=True))
_EN_NEGATION_VERB_SKIP = (
    r"(?:use|handle|process|support|trigger|call|invoke|provide|cover|include"
    r"|deal\s+with|work\s+with|be\s+used)"
)
_EN_MODAL_NEG_HEAD = (
    r"(?:do|does|did|can|could|will|would|should|must|shall)\s+not"
    r"|don't|doesn't|didn't|can't|cannot|won't|couldn't|wouldn't"
    r"|shouldn't|mustn't|shan't"
)
NEGATION_PATTERNS: tuple[str, ...] = (
    "(?:" + "|".join(_CN_NEGATION_HEADS) + r")\s*(.+?)(?=[。，\r\n]|$)",
    r"(?:未|尚未|暂未|无法|不能|不会|无需|无须|不需|不必|不应)(?=(?:"
    + _CN_ACTION_VERB_ALT + r"))(.+?)(?=[。，\r\n]|$)",
    r"不(?=(?:" + _CN_BARE_NOT_ACTION_VERB_ALT
    + r"))(.+?)(?=[。，\r\n]|$)",
    r"(?:NOT\s+for|DO\s+NOT|NEVER)\s*[:：]?(?:\s+"
    + _EN_NEGATION_VERB_SKIP + r"(?:\s+for)?)?\s+(.+?)(?=[.。\r\n]|$)",
    r"\b(?:" + _EN_MODAL_NEG_HEAD + r")\b\s*(?:"
    + _EN_NEGATION_VERB_SKIP + r"\s+(?:for\s+)?)?(.+?)(?=[.。\r\n]|$)",
    r"not\s+(?:intended|designed)\s+for\s+(.+?)(?=[.。\r\n]|$)",
    r"not\s+responsible\s+for\s+(.+?)(?=[.。，,\r\n]|$)",
    r"not\s+allowed\s*[:：]?\s*(?:to\s+)?(.+?)(?=[.。，,\r\n]|$)",
    (r"([^.。，,\r\n]+?)\s+(?:is|are|was|were)\s+not\s+applicable\s+to\s+"
     r"(?:this|the)\s+skill\b(?=[.。\r\n]|$)"),
    (r"\b(?:this|the)\s+skill\s+(?:is|are|was|were)\s+not\s+applicable\s+to\s+"
     r"(.+?)(?=[.。\r\n]|$)"),
    r"(?:^|(?<=[.。，,\r\n]))\s*not\s+applicable\s+to\s+(.+?)(?=[.。\r\n]|$)",
    r"(?:若|如果)(?:主要|核心)?(?:产出|交付物)\s*(?:为|是)\s*(.+?)(?=[。，\r\n]|$)",
)
def extract_negated_terms(text: str,
                         patterns: tuple[str, ...] | list[str]) -> list[str]:
    pattern_list = list(patterns)
    use_boundary_parser = all(
        pattern in pattern_list for pattern in NEGATION_PATTERNS)
    negatives = extract_boundary_scopes(text) if use_boundary_parser else []
    for pattern in pattern_list:
        if use_boundary_parser and pattern in NEGATION_PATTERNS:
            continue
        for match in re.finditer(pattern, text, re.IGNORECASE):
            for neg_text in _negated_term_parts(match.group(1)):
                if neg_text not in negatives:
                    negatives.append(neg_text)
    return negatives
_RESPONSIBILITY_CLUSTERS: dict[str, list[str]] = {
    'create': ['创建', '生成', '新建', 'build', 'create', 'generate', 'make',
               'builds', 'creates', 'generates', 'makes',
               'building', 'creating', 'generating', 'making', 'creation', 'generation'],
    'edit': ['编辑', '修改', '更新', 'edit', 'update', 'modify', 'change',
             'edits', 'updates', 'modifies', 'changes',
             'editing', 'updating', 'modifying', 'changing', 'modification'],
    'analyze': ['分析', '诊断', '检查', 'analyze', 'diag', 'inspect', 'review',
                'analyzes', 'diagnoses', 'inspects', 'reviews',
                'analyzing', 'diagnosing', 'inspecting', 'reviewing', 'analysis', 'diagnosis'],
    'convert': ['转换', '导出', '转成', 'convert', 'export', 'transform',
                'converts', 'exports', 'transforms',
                'converting', 'exporting', 'transforming', 'conversion', 'transformation'],
    'delete': ['删除', '移除', '清除', 'delete', 'remove', 'clear',
               'deletes', 'removes', 'clears',
               'deleting', 'removing', 'clearing', 'deletion', 'removal'],
    'search': ['搜索', '查找', '查询', 'search', 'find', 'query',
               'searches', 'finds', 'queries', 'searching', 'finding', 'querying'],
    'deploy': ['部署', '发布', '上线', 'deploy', 'release', 'publish',
               'deploys', 'releases', 'publishes',
               'deploying', 'releasing', 'publishing', 'deployment'],
    'monitor': ['监控', '监测', '跟踪', 'monitor', 'track', 'watch',
                'monitors', 'tracks', 'watches', 'monitoring', 'tracking', 'watching'],
}
_TYPE_KEY_TO_DOMAIN_HINT: dict[str, str] = {
    "code_diag": "code",
    "skill": "skill-management",
    "skillops": "skill-management",
}
DOMAIN_HINT_TO_TYPE_KEY: dict[str, str] = {
    "code": "code_diag",
    "skill-management": "skillops",
}
def resolve_domain_key(hint: str | None, table: dict) -> str | None:
    if hint in table:
        return hint
    return _TYPE_KEY_TO_DOMAIN_HINT.get(hint, hint)
EXTENSION_ALTERNATION = "docx|xlsx|xlsm|xls|csv|tsv|pptx|pdf|dbt|ksheet|otl"
GENERIC_EXTENSION_ALTERNATION = (
    EXTENSION_ALTERNATION + "|"
    "txt|md|markdown|rst|tex|json|jsonl|ya?ml|toml|ini|cfg|conf|log|xml|"
    "html?|css|scss|less|js|jsx|ts|tsx|vue|svelte|py|ipynb|java|kt|"
    "c|h|cc|cpp|hpp|cs|go|rs|rb|php|swift|scala|sh|bash|zsh|ps1|bat|cmd|"
    "sql|db|sqlite|parquet|avro|proto|"
    "zip|tar|gz|tgz|bz2|xz|rar|7z|"
    "png|jpe?g|gif|svg|webp|bmp|tiff?|ico|"
    "mp3|wav|flac|aac|ogg|m4a|mp4|mov|avi|mkv|webm"
)
FILE_EXTENSION_PATTERN: re.Pattern = re.compile(
    r"(?:\.[ \t]*|(?<![a-zA-Z]))(?:" + EXTENSION_ALTERNATION + r")(?![a-zA-Z])",
    re.IGNORECASE,
)
@lru_cache(maxsize=_DERIVED_CACHE_MAX_ENTRIES)
def _declared_ext_re(extension_alternation: str) -> re.Pattern[str]:
    return re.compile(
        r"\.(" + extension_alternation + r")(?![A-Za-z0-9])", re.IGNORECASE
    )
_EXT_CLAUSE_RESET_RE = re.compile(
    r"[。；;！!？?，,\n]|\.(?=\s|$)|\bbut\b|\bhowever\b|\band\b|但|不过|然而|以及",
    re.IGNORECASE)
_EXT_CN_VERBS: tuple[str, ...] = (
    "处理", "读取", "编辑", "打开", "操作", "转换", "生成", "使用",
    "支持", "提供", "包含", "包括", "涉及", "负责", "覆盖", "适用",
    "兼容", "用于",
)
_EXT_EN_VERBS = (
    r"supports?|supported|handles?|handled|reads?|edits?|opens?"
    r"|operates?|converts?|generates?|uses?|provides?|includes?|covers?"
    r"|offers?|gives?|has|have"
)
_EXT_EN_CAPABILITY_MARKERS = (
    _EXT_EN_VERBS + r"|compatible|works?\s+with"
)
_EXT_EN_NEG_VERB_SUFFIX = (
    r"(?:\s+(?:" + _EXT_EN_CAPABILITY_MARKERS + r")"
    r"(?:\s+support)?(?:\s+for)?)?"
)
_EXT_EN_NEGATION_HEADS = (
    r"(?:\bnot\b(?!\s+only\b)|\bnever\b|\bwithout\b"
    r"|\b(?:" + _EN_MODAL_NEG_HEAD + r")\b)"
)
_EXT_EN_NEGATION_PATTERN = _EXT_EN_NEGATION_HEADS + _EXT_EN_NEG_VERB_SUFFIX
_EXT_POSTFIX_NO_SUPPORT_PATTERN = (
    r"(?:has|have|had)\s+no\s+support\b(?!\s+for\b)")
_EXT_CN_VERB_ALT = "|".join(_EXT_CN_VERBS)
_EXT_NEG_MARKER_RE = re.compile(
    r"(?:不|未|尚未|暂未|无法|不能|不会|无需|无须|不需|不必)"
    r"(?:" + _EXT_CN_VERB_ALT + r")"
    r"|(?:不可|未能|禁止|请勿|勿|切勿|不要|不需要|不承诺)"
    r"|别(?:" + _EXT_CN_VERB_ALT + r"|碰|动)"
    r"|" + _EXT_EN_NEGATION_PATTERN
    + r"|\b" + _EXT_POSTFIX_NO_SUPPORT_PATTERN
    + r"|support\s+is\s+(?:unavailable|not\s+available)"
    + r"|\bunsupported\b|\bunavailable\b|\bno\s+support\b|\bno\b"
    + r"|(?:不|未)(?:再)?(?:受|被)支持",
    re.IGNORECASE,
)
_EXT_POS_MARKER_RE = re.compile(
    r"(?:" + _EXT_CN_VERB_ALT + r"|可以|能够|可(?:以|能)?|仅|只"
    r"|\b(?:" + _EXT_EN_CAPABILITY_MARKERS + r"|only)\b)",
    re.IGNORECASE,
)
_EXT_POLARITY_RE = re.compile(
    r"(?P<neg>" + _EXT_NEG_MARKER_RE.pattern + r")"
    r"|(?P<pos>" + _EXT_POS_MARKER_RE.pattern + r")",
    re.IGNORECASE,
)
_EXT_SOFT_RESET_MARKERS = frozenset(("，", ",", "and", "以及"))
_EXT_POSTFIX_COPULA_RE = re.compile(r"\b(?:is|are|was|were)\s*$", re.IGNORECASE)
_EXT_POSTFIX_NEG_RE = re.compile(
    r"(?:(?:不|未)(?:再)?(?:受|被)支持|support\s+is\s+(?:unavailable|not\s+available)|"
    + _EXT_POSTFIX_NO_SUPPORT_PATTERN + r")",
    re.IGNORECASE,
)
_EXT_PREFIX_ONLY_NEG_RE = re.compile(r"(?:without|no|not|never)", re.IGNORECASE)
_EXT_POSTFIX_PAST_PARTICIPLE = frozenset({
    "supported", "handled", "opened", "converted", "generated",
    "provided", "included", "covered", "offered", "compatible",
})
_EXT_POSTFIX_COMMA_BOUNDARY_RE = re.compile(r",|，")
_EXT_POSTFIX_SUBJECT_BOUNDARY_RE = re.compile(
    r",|，|\band\b|\bor\b|\bwhile\b|以及", re.IGNORECASE)
def declared_extensions(
    text: str, extension_alternation: str | None = None
) -> set[str]:
    text = normalize_text(text)
    pattern = _declared_ext_re(
        EXTENSION_ALTERNATION if extension_alternation is None
        else extension_alternation)
    declared: set[str] = set()
    state: bool | None = None
    cursor = 0
    for reset in _EXT_CLAUSE_RESET_RE.finditer(text):
        if reset.group(0).casefold() in _EXT_SOFT_RESET_MARKERS:
            continue
        state = _consume_extension_segment(
            text[cursor:reset.start()], state, declared, pattern)
        state = None
        cursor = reset.end()
    _consume_extension_segment(text[cursor:], state, declared, pattern)
    return declared
def _collect_extension_segment(
    chunk: str,
    state: bool | None,
    declared: set[str],
    pattern: re.Pattern[str],
) -> bool | None:
    if not chunk:
        return state
    if state is None:
        state = True
    extensions = {
        match.group(1).lower() for match in pattern.finditer(chunk)
    }
    if state:
        declared.update(extensions)
    else:
        declared.difference_update(extensions)
    return state
def _postfix_subject_start(
    prefix: str, pattern: re.Pattern[str], has_prior_marker: bool
) -> int:
    if not has_prior_marker:
        return 0
    subject_start = 0
    for boundary in _EXT_POSTFIX_SUBJECT_BOUNDARY_RE.finditer(prefix):
        if (pattern.search(prefix, 0, boundary.start())
                and pattern.search(prefix, boundary.end())):
            subject_start = boundary.end()
    if subject_start:
        return subject_start
    extensions = list(pattern.finditer(prefix))
    return extensions[-1].start() if len(extensions) > 1 else 0
def _postfix_marker_owns_subject(
    segment: str,
    prefix: str,
    marker: re.Match[str],
    pattern: re.Pattern[str],
) -> bool:
    if _EXT_PREFIX_ONLY_NEG_RE.fullmatch(marker.group(0)):
        return False
    boundaries = list(_EXT_POSTFIX_SUBJECT_BOUNDARY_RE.finditer(prefix))
    subject_offset = boundaries[-1].end() if boundaries else 0
    if pattern.search(prefix, subject_offset) is None:
        return False
    if (boundaries
            or _EXT_POSTFIX_COPULA_RE.search(prefix)
            or _EXT_POSTFIX_NEG_RE.fullmatch(marker.group(0))):
        return True
    next_boundary = _EXT_POSTFIX_SUBJECT_BOUNDARY_RE.search(
        segment, marker.end())
    next_extension = pattern.search(segment, marker.end())
    return next_extension is None or (
        next_boundary is not None
        and next_boundary.start() < next_extension.start())
def _consume_extension_segment(
    segment: str,
    state: bool | None,
    declared: set[str],
    pattern: re.Pattern[str],
) -> bool | None:
    cursor = 0
    after_prefix_neg = False
    for marker in _EXT_POLARITY_RE.finditer(segment):
        prefix = segment[cursor:marker.start()]
        next_state = marker.group("neg") is None
        # “without/no/not .docx support”中的 support 是宾语名词的一部分，
        # 不得把它当作拥有 .docx 主语的后缀标记，否则会回收前缀否定的范围；
        # 但 “without .docx, .xlsx supported” 中逗号后的过去分词是新分句
        # 谓语，必须允许它回指 .xlsx，否则会把显式肯定误判为否定。
        postfix_allowed = (
            not after_prefix_neg
            or _EXT_POSTFIX_COPULA_RE.search(prefix) is not None
            or (marker.group(0).casefold() in _EXT_POSTFIX_PAST_PARTICIPLE
                and _EXT_POSTFIX_COMMA_BOUNDARY_RE.search(prefix) is not None)
        )
        if postfix_allowed and _postfix_marker_owns_subject(
                segment, prefix, marker, pattern):
            subject_start = _postfix_subject_start(
                prefix, pattern, has_prior_marker=cursor > 0)
            state = _collect_extension_segment(
                prefix[:subject_start], state, declared, pattern)
            state = _collect_extension_segment(
                prefix[subject_start:], next_state, declared, pattern)
        else:
            state = _collect_extension_segment(
                prefix, state, declared, pattern)
        state = next_state
        cursor = marker.end()
        after_prefix_neg = _EXT_PREFIX_ONLY_NEG_RE.fullmatch(
            marker.group(0)) is not None
    return _collect_extension_segment(
        segment[cursor:], state, declared, pattern)
_GRADE_BANDS_SCALE: tuple[tuple[float, str], ...] = (
    (0.9, "A"), (0.75, "B"), (0.6, "C"), (0.4, "D"),
)
GRADE_BANDS_RATIO: tuple[tuple[float, str], ...] = (
    (0.9, "A"), (0.7, "B"), (0.5, "C"), (0.3, "D"),
)
def band_to_grade(ratio: float,
                  bands: tuple[tuple[float, str], ...]) -> str:
    for threshold, grade in bands:
        if ratio >= threshold:
            return grade
    return "F"
def score_to_grade(score: float, scale: float = 100.0) -> str:
    return band_to_grade(score / scale if scale > 0 else 0,
                         _GRADE_BANDS_SCALE)
def _keyword_text(item: Any) -> str | None:
    if item is None or isinstance(item, (Mapping, list, tuple, set, frozenset)):
        return None
    if isinstance(item, (bytes, bytearray)):
        return item.decode('utf-8', errors='replace')
    return item if isinstance(item, str) else str(item)
def _as_text_items(value: object, context: str) -> list[object]:
    if isinstance(value, (str, bytes, bytearray)):
        return [value]
    if isinstance(value, Mapping):
        return []
    if not value:
        return []
    if isinstance(value, (set, frozenset)):
        return sorted(value, key=repr)
    try:
        return list(iter(value))
    except TypeError as _e:
        log_swallowed(__name__, _e, context=context)
        return []
def _filter_text_items(items: list[object]) -> list[str]:
    normalized: list[str] = []
    for item in items:
        text = _keyword_text(item)
        if text is not None and text.strip():
            normalized.append(text)
    return normalized
def _normalize_text_container(value: object, context: str) -> list[str]:
    return _filter_text_items(_as_text_items(value, context))
def normalize_keywords(keywords: list[str] | None) -> list[str]:
    normalized = _normalize_text_container(
        keywords, 'normalize_keywords:TypeError')
    return [kw.strip() for kw in normalized if kw.strip()]
def normalize_descriptions(value: object) -> list[str]:
    return _normalize_text_container(value, 'normalize_descriptions:TypeError')
def md_escape_cell(text: str) -> str:
    if not isinstance(text, str):
        text = "" if text is None else str(text)
    return (text.replace("\\", "\\\\")
            .replace("|", "\\|")
            .replace("\r", " ").replace("\n", " "))
def _ascii_boundary_pattern(kw: str, *, suffix_boundary: bool,
                            word_chars: str = "A-Za-z0-9_") -> str:
    pattern = re.escape(kw)
    if kw[0].isalnum() or kw[0] == "_":
        pattern = rf"(?<![{word_chars}])" + pattern
    if suffix_boundary and (kw[-1].isalnum() or kw[-1] == "_"):
        pattern = pattern + rf"(?![{word_chars}])"
    return pattern
def _match_keyword(keyword: str, text_lower: str, *, suffix_boundary: bool) -> bool:
    kw = normalize_text(keyword).lower()
    if not kw or not isinstance(text_lower, str):
        return False
    if not kw.isascii():
        return kw in text_lower
    return re.search(
        _ascii_boundary_pattern(kw, suffix_boundary=suffix_boundary),
        text_lower,
    ) is not None
def keyword_matches(keyword: str, text_lower: str) -> bool:
    return _match_keyword(keyword, text_lower, suffix_boundary=True)
def stem_matches(keyword: str, text_lower: str) -> bool:
    return _match_keyword(keyword, text_lower, suffix_boundary=False)
def text_token_count(text: str) -> int:
    text = normalize_text(text)
    en_words = len(text.split())
    cn_chars = len(re.findall(RE_CHINESE_CHARS, text))
    return max(en_words, cn_chars)
def detect_vague_words(text: str) -> list[str]:
    text = normalize_text(text)
    text_lower = text.lower()
    return [w for w in VAGUE_WORDS if keyword_matches(w, text_lower)]
def check_description_length(description: str) -> dict[str, Any]:
    description = normalize_text(description)
    length = len(description)
    result = {
        'length': length,
        'is_valid': DESC_MIN_LENGTH <= length <= DESC_MAX,
        'is_optimal': DESC_OPTIMAL_MIN <= length <= DESC_MAX_LENGTH,
    }
    if length < DESC_MIN_LENGTH:
        result['status'] = 'too_short'
        result['suggestion'] = f'描述过短（{length}字符），建议扩充到至少{DESC_MIN_LENGTH}字符'
    elif length > DESC_MAX:
        result['status'] = 'too_long'
        result['suggestion'] = f'描述过长（{length}字符），建议精简核心场景'
    elif length < DESC_OPTIMAL_MIN:
        result['status'] = 'acceptable'
        result['suggestion'] = f'建议扩充到{DESC_OPTIMAL_MIN}字符以上'
    elif length > DESC_MAX_LENGTH:
        result['status'] = 'acceptable'
        result['suggestion'] = (
            f'描述偏长（{length}字符），建议精简到{DESC_MAX_LENGTH}字符以内')
    else:
        result['status'] = 'optimal'
        result['suggestion'] = ''
    return result
def check_atomic_responsibility(description: str) -> dict[str, Any]:
    description = _positive_responsibility_text(description)
    text_lower = description.lower()
    matched = [c for c, kws in _RESPONSIBILITY_CLUSTERS.items()
               if any(keyword_matches(kw, text_lower) for kw in kws)]
    is_atomic = len(matched) <= 2
    suggestion = ''
    if not is_atomic:
        suggestion = f'描述包含 {len(matched)} 个职责簇 {matched}，建议拆分为独立技能'
    return {'is_atomic': is_atomic, 'matched_clusters': matched, 'suggestion': suggestion}
def _coverage_score(has_zh: bool, has_en: bool) -> float:
    if has_zh and has_en:
        return 1.0
    return 0.5 if has_zh or has_en else 0.0
def _coverage_suggestion(has_zh: bool, has_en: bool) -> str:
    if has_zh and has_en:
        return ''
    if not has_zh and not has_en:
        return '建议同时添加中文与英文关键词以提高双语环境触发率'
    if not has_zh:
        return '建议添加中文关键词以提高中文环境触发率'
    return '建议添加英文关键词以提高英文环境触发率'
def evaluate_multilingual_coverage(keywords: list[str]) -> dict[str, Any]:
    keywords = normalize_keywords(keywords)
    if not keywords:
        return {'coverage_score': 0.0, 'zh_count': 0, 'en_count': 0,
                'suggestion': '关键词列表为空'}
    zh_count = sum(1 for kw in keywords if re.search(RE_CHINESE_CHARS, kw))
    en_count = sum(1 for kw in keywords if _ASCII_WORD_RE.search(kw))
    has_zh, has_en = zh_count > 0, en_count > 0
    return {
        'coverage_score': _coverage_score(has_zh, has_en),
        'zh_count': zh_count,
        'en_count': en_count,
        'suggestion': _coverage_suggestion(has_zh, has_en),
    }
PIPELINE_TRIGGER_KEYWORDS: tuple[str, ...] = (
    "审计", "bug", "缺陷", "修复", "治疗", "诊断",
    "审一下", "审查", "查查", "检查下", "检查一下", "排查",
    "扫描漏洞", "扫描安全漏洞", "安全漏洞", "漏洞扫描", "找问题",
    "修一下", "治一下", "确诊", "体检", "优化代码", "优化下代码", "分析下", "污染追踪", "权限审计",
    "纠错", "纠正", "订正", "消缺", "补漏", "堵漏", "打补丁",
    "查错", "找错", "筛查", "巡检", "把脉", "问诊", "会诊", "复诊",
    "检视", "查验", "剖析", "摸底", "清查", "稽核", "复核", "核查", "盘点",
    "漏洞", "隐患", "毛病", "异味", "坏味道", "反模式", "报错", "故障", "崩溃",
    "治理", "疗愈", "救治", "抢救", "根除", "剔除",
    "污点追踪", "密钥泄露", "路径穿越", "越权", "供应链扫描",
    "審計", "審查", "修復", "治療", "診斷", "檢查", "掃描",
    "audit", "defect", "fix", "treat", "diagnose", "diagnosis",
    "debug", "check my skill", "code review",
    "repair", "patch", "troubleshoot", "vulnerability", "vulnerabilities",
    "bugfix", "lint", "hotfix", "hot fix", "quick fix",
    "扇出", "测试", "验证", "分析", "检查", "优化", "死代码", "清理",
)
TRIGGER_WEAK_TOKENS: tuple[str, ...] = (
    "修", "查", "看", "审", "扫", "测", "补", "清", "治", "改",
    "优化", "处理", "解决", "搞定", "搞好", "弄下", "搞下",
)
TRIGGER_CONTEXT_TOKENS: tuple[str, ...] = (
    "代码", "code", "技能", "skill", "模块", "函数", "文件", "脚本", "项目",
    "工程", "源码", "源文件", "程序", "插件", "组件", "接口", "api", "依赖",
    "测试", "用例", "质量", "bug", "报错", "异常", "错误", "漏洞", "缺陷",
    "注释", "编译", "部署", "运行", "仓库", "版本", "提交", "逻辑", "数据结构",
)
TRIGGER_NEGATIVE_CONTEXTS: tuple[str, ...] = (
    "装修", "修图", "修车", "修水管", "修眉", "修甲", "维修", "保修", "修文",
    "修辞", "修脚", "查快递", "查天气", "查话费", "查机票", "查路线", "查酒店",
    "查股价", "查分", "审稿", "审片", "年审", "政审", "治疗感冒", "挂号", "洗牙",
)
TRIGGER_FUZZY_MIN_SCORE = 0.60
TRIGGER_FUZZY_MIN_LEN = 4
VERB_SYNONYM_EXPANSION: dict[str, list[str]] = {
    "create": ["build", "make", "generate", "produce", "draft",
               "新建", "生成", "创建", "制作", "起草", "编制", "拟定"],
    "edit": ["modify", "update", "change", "revise", "alter",
             "修改", "更新", "调整", "改动", "修订", "变更"],
    "delete": ["remove", "clear", "clean", "erase", "drop",
               "删除", "移除", "清理", "清除", "清空", "废弃"],
    "search": ["find", "look up", "query", "lookup",
               "检索", "查找", "寻找", "查询", "搜索", "定位", "匹配"],
    "analyze": ["examine", "inspect", "study", "assess", "evaluate",
                "分析", "检查", "审查", "评估", "诊断", "解析"],
    "convert": ["transform", "translate", "change to", "turn into",
                "转换", "转化", "变成", "转为", "改写", "转译"],
    "merge": ["combine", "join", "integrate", "unify",
              "合并", "整合", "联合", "汇总", "融合", "聚合"],
    "check": ["review", "diag", "inspect", "verify",
              "检查", "审查", "校验", "验证", "核对", "诊断", "排查"],
    "extract": ["pull out", "fetch", "retrieve", "scrape",
                "提取", "抓取", "获取", "摘取", "抽取", "导出"],
    "send": ["submit", "dispatch", "push", "deliver",
             "发送", "提交", "推送", "递交", "上报", "投递"],
    "monitor": ["watch", "track", "observe", "babysit",
                "监控", "监视", "跟踪", "观察", "追踪", "值守"],
    "deploy": ["release", "publish", "ship",
               "上线", "发布", "部署", "投产", "启用", "交付"],
    "backup": ["archive", "save copy", "snapshot",
               "备份", "存档", "保留副本", "镜像", "留存"],
    "restore": ["recover", "rollback", "revert",
                "还原", "恢复", "回滚", "回退", "重建"],
    "optimize": ["improve", "enhance", "refine", "tune",
                 "优化", "改进", "提升", "调优", "完善", "改良"],
    "format": ["style", "layout", "beautify",
               "格式化", "排版", "美化", "整理", "规范", "对齐"],
    "calculate": ["compute", "sum", "count", "reckon",
                  "计算", "统计", "求和", "汇总", "核算", "测算"],
    "compare": ["contrast", "diff", "versus",
                "对比", "比较", "对照", "差异", "delta"],
}
TRIGGER_FUZZY_SEEDS: tuple[str, ...] = (
    "帮我诊断下代码质量", "把代码检查一下", "帮我跑全面诊断", "帮我修代码问题",
    "修一下这个BUG", "治疗这些问题项", "帮我审计技能", "审查skill",
    "检查这个技能的安全性", "清理技能文档", "整理skill目录", "删掉过时内容",
    "帮我创建新skill", "写一个技能", "帮我重构技能文档", "改进这个skill",
    "扫描安全漏洞", "污点追踪", "权限审计", "查密钥泄露",
    "找出死代码并清理", "跑一下回归测试", "补齐测试覆盖率", "确认这些发现是不是误报",
    "帮我看看这段代码", "这段代码有点问题", "代码质量怎么样", "帮我修复这个模块",
    "帮我排查一下问题", "这个功能崩溃了", "帮我治理一下技术债", "帮我体检一下代码",
    "帮我瞅瞅这个文件", "修复缺陷", "修复漏洞", "看看这段逻辑对不对",
    "帮我分析下这个函数", "帮我查查这个脚本", "检查一下我的技能", "审计一下这个技能",
    "帮我把这些bug修了", "代码体检", "代码诊断", "帮我把问题处理一下",
    "这代码有毛病", "帮我看看哪里有问题", "排查一下故障", "帮我看下报错",
    "帮我搞定代码问题", "帮我把这个模块搞定", "代码跑不通", "帮我看下这个函数",
)
def _vocab_tuple(value: object) -> tuple[str, ...]:
    if isinstance(value, str):
        cleaned = value.strip()
        return (cleaned,) if cleaned else ()
    if isinstance(value, (list, tuple)):
        items: object = value
    elif isinstance(value, (set, frozenset)):
        items = sorted(value, key=str)
    else:
        return ()
    return tuple(text for item in items
                 if isinstance(item, str) and (text := item.strip()))
@dataclass(frozen=True)
class TriggerVocabulary:
    keywords: tuple[str, ...] = PIPELINE_TRIGGER_KEYWORDS
    negative_contexts: tuple[str, ...] = TRIGGER_NEGATIVE_CONTEXTS
    weak_tokens: tuple[str, ...] = TRIGGER_WEAK_TOKENS
    context_tokens: tuple[str, ...] = TRIGGER_CONTEXT_TOKENS
    fuzzy_seeds: tuple[str, ...] = TRIGGER_FUZZY_SEEDS
    def __post_init__(self) -> None:
        for field_name in ("keywords", "negative_contexts", "weak_tokens",
                           "context_tokens", "fuzzy_seeds"):
            object.__setattr__(self, field_name,
                               _vocab_tuple(getattr(self, field_name)))
DEFAULT_TRIGGER_VOCABULARY = TriggerVocabulary()
_VOCAB_FIELDS: tuple[str, ...] = (
    "keywords", "negative_contexts", "weak_tokens", "context_tokens",
    "fuzzy_seeds",
)
def _as_vocabulary(value: object) -> TriggerVocabulary | None:
    if value is None or isinstance(value, TriggerVocabulary):
        return value
    if isinstance(value, Mapping):
        return TriggerVocabulary(**{
            name: value[name] for name in _VOCAB_FIELDS if name in value
        })
    _log.warning("触发词表形态非法: %s，回退默认词表", type(value).__name__)
    return None
_NEVER_MATCH_PATTERN = r"(?!)"
def _compile_trigger_pattern(keywords: tuple[str, ...]) -> re.Pattern:
    cleaned = [item.strip() for item in keywords if isinstance(item, str)]
    parts = [
        _ascii_boundary_pattern(kw, suffix_boundary=True)
        if re.search(r"[A-Za-z]", kw) else re.escape(kw)
        for kw in cleaned if kw
    ]
    return re.compile("|".join(parts) or _NEVER_MATCH_PATTERN, re.IGNORECASE)
_cached_trigger_pattern = lru_cache(
    maxsize=_DERIVED_CACHE_MAX_ENTRIES)(_compile_trigger_pattern)
_TRIGGER_PATTERN = _cached_trigger_pattern(PIPELINE_TRIGGER_KEYWORDS)
def match_pipeline_trigger(
        text: str,
        vocabulary: TriggerVocabulary | None = None) -> list[str]:
    if not text or not isinstance(text, str):
        return []
    vocabulary = _as_vocabulary(vocabulary)
    if vocabulary is not None and not vocabulary.keywords:
        return []
    pattern = (_TRIGGER_PATTERN if vocabulary is None
               else _cached_trigger_pattern(tuple(vocabulary.keywords)))
    try:
        seen: list[str] = []
        for m in pattern.finditer(text):
            kw = m.group(0).lower()
            if kw not in seen:
                seen.append(kw)
        return seen
    except Exception as e:
        _log.warning("[Trigger] 关键词匹配异常: %s", e)
        return []
def validate_pipeline_trigger_contract(
        vocabulary: TriggerVocabulary | None = None) -> dict:
    vocab = _as_vocabulary(vocabulary) or DEFAULT_TRIGGER_VOCABULARY
    registered = {
        kw.lower() for kw in vocab.keywords
        if isinstance(kw, str) and kw.strip()
    }
    missing = [kw for kw in MANDATORY_PIPELINE_TRIGGER_KEYWORDS
               if kw.lower() not in registered]
    unmatched: list[str] = []
    for kw in MANDATORY_PIPELINE_TRIGGER_KEYWORDS:
        if kw in missing:
            continue
        try:
            hits = [hit.lower() for hit in match_pipeline_trigger(kw, vocab)]
        except Exception as exc:
            _log.warning("[Trigger] 强制词 %r 契约校验异常: %s", kw, exc)
            unmatched.append(kw)
            continue
        if kw.lower() not in hits:
            unmatched.append(kw)
    enforced = [kw for kw in MANDATORY_PIPELINE_TRIGGER_KEYWORDS
                if kw not in missing and kw not in unmatched]
    return {
        "schema": "pipeline-trigger-contract/1",
        "passed": not missing and not unmatched,
        "mandatory_keywords": list(MANDATORY_PIPELINE_TRIGGER_KEYWORDS),
        "registered_count": len(registered),
        "enforced_keywords": enforced,
        "missing": missing,
        "unmatched": unmatched,
    }
_TAIL_NOISE = re.compile(r"[吧呗啦呀啊哈呢哦嘛吗么~！!。，,、？?；;：:…\s]+$")
_LEAD_POLITE_WORDS = (
    "请", "帮我", "帮忙", "麻烦", "劳驾", "能不能", "可以", "可否",
)
def _strip_lead_polite(t: str) -> str:
    while True:
        t = t.lstrip()
        for w in _LEAD_POLITE_WORDS:
            if t.startswith(w):
                t = t[len(w):]
                break
        else:
            return t
def normalize_trigger_text(text: str) -> str:
    t = unicodedata.normalize("NFKC", normalize_text(text)).lower()
    t = re.sub(r"\s+", " ", t).strip()
    t = _strip_lead_polite(t)
    t = _TAIL_NOISE.sub("", t)
    return t.strip()
_CJK_RUN = re.compile(r"[\u4e00-\u9fff]+|[a-z0-9]+")
def trigger_tokens(text: str) -> frozenset[str]:
    tokens: set[str] = set()
    for seg in _CJK_RUN.findall(normalize_text(text).lower()):
        if seg[0].isascii():
            if len(seg) >= 2:
                tokens.add(seg)
        elif len(seg) == 1:
            tokens.add(seg)
        else:
            for i in range(len(seg) - 1):
                tokens.add(seg[i:i + 2])
    return frozenset(tokens)
_WORD_TOKEN_RE = re.compile(r'[A-Za-z0-9_]+|[\u4e00-\u9fff]+')
def word_tokens(text: str) -> set[str]:
    tokens: set[str] = set()
    for m in _WORD_TOKEN_RE.finditer(normalize_text(text).lower()):
        seg = m.group(0)
        if seg.isascii() or len(seg) == 1:
            tokens.add(seg)
        else:
            tokens.update(seg[i:i + 2] for i in range(len(seg) - 1))
    return tokens
@dataclass
class SkillFingerprint:
    skill_name: str = ''
    description: str = ''
    keywords: list[str] = field(default_factory=list)
    category: str = ''
    action_verbs: set[str] = field(default_factory=set)
    domain_nouns: set[str] = field(default_factory=set)
    has_scripts: bool = False
    has_tests: bool = False
    skill_dir: str = ''
def _skill_identity(skill_name: str, skill_dir: str = '') -> tuple[str, str]:
    if skill_dir:
        return ('path', os.path.normcase(
            os.path.realpath(os.path.abspath(skill_dir))))
    return ('name', skill_name)
def _dir_nonempty(path: Path) -> bool:
    try:
        return path.is_dir() and any(path.iterdir())
    except OSError as exc:
        _log.warning('枚举 %s 失败，按空目录降级: %s', path, exc)
        return False
def extract_skill_fingerprint(skill_dir: Path | str) -> SkillFingerprint | None:
    if not isinstance(skill_dir, (str, os.PathLike)):
        _log.warning('extract_skill_fingerprint 入参非路径: %r，跳过', skill_dir)
        return None
    skill_dir = Path(os.fsdecode(skill_dir))
    md_file = skill_dir / 'SKILL.md'
    if not md_file.exists():
        return None
    try:
        text = md_file.read_text(encoding='utf-8-sig')
    except (OSError, UnicodeDecodeError) as exc:
        _log.warning('读取 SKILL.md 失败，跳过指纹提取 %s: %s', skill_dir, exc)
        return None
    fp = SkillFingerprint(
        skill_name=skill_dir.name, skill_dir=os.path.abspath(skill_dir))
    meta = parse_skill_md_text(text, default_name=skill_dir.name)
    fp.description = meta["description"]
    fp.keywords = list(meta["keywords"])
    fp.category = normalize_text(
        parse_frontmatter_dict(text).get("category", "")).strip()
    combined = (fp.skill_name + ' ' + fp.description + ' ' + ' '.join(fp.keywords)).lower()
    fp.action_verbs = {v for v in SKILL_ACTION_VERBS if re.search(word_pattern(v), combined)}
    fp.domain_nouns = {d for d in DOMAIN_KEYWORDS if match_domain(combined, d)}
    fp.has_scripts = _dir_nonempty(skill_dir / 'scripts')
    fp.has_tests = _dir_nonempty(skill_dir / 'tests')
    return fp
_DEFAULT_OVERLAP_THRESHOLD = 0.6
_MERGE_FULL_THRESHOLD = 0.85
_MERGE_CONSOLIDATE_THRESHOLD = 0.75
@dataclass
class OverlapPair:
    skill_a: str = ''
    skill_b: str = ''
    semantic_similarity: float = 0.0
    keyword_overlap: float = 0.0
    action_overlap: float = 0.0
    domain_overlap: float = 0.0
    overall_overlap: float = 0.0
    merge_strategy: str = ''
    recommendation: str = ''
    skill_a_dir: str = ''
    skill_b_dir: str = ''
@dataclass
class DeduplicationReport:
    skills_root: str = ''
    total_skills: int = 0
    overlap_pairs: list[OverlapPair] = field(default_factory=list)
    high_risk_pairs: list[OverlapPair] = field(default_factory=list)
    redundancy_score: float = 0.0
    merge_plan: list[dict] = field(default_factory=list)
    issues: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
class SkillDeduplicationEngine:
    def deduplicate(self: Self, skill_dirs: list) -> dict:
        dirs = self._normalize_input_dirs(skill_dirs)
        fingerprints = self._dedupe_fingerprints(
            self._extract_fingerprints(dirs))
        pairs = self._build_pairs(fingerprints)
        merge_plan = self._generate_merge_plan(pairs)
        _log.info("deduplicate 完成: %d 指纹, %d 重叠对, %d 归并计划项",
                  len(fingerprints), len(pairs), len(merge_plan))
        return {'fingerprints': fingerprints, 'pairs': pairs, 'merge_plan': merge_plan}
    @staticmethod
    def _normalize_input_dirs(skill_dirs: list) -> list:
        if skill_dirs is not None and not isinstance(skill_dirs, (list, tuple)):
            _log.warning('deduplicate 入参非列表形态: %r，按空载荷处理',
                          skill_dirs)
            return []
        dirs: list[str] = []
        for skill_dir in skill_dirs or []:
            normalized = normalize_out_path(skill_dir)
            if normalized is None:
                _log.warning('deduplicate 跳过非法技能目录项: %r', skill_dir)
                continue
            dirs.append(normalized)
        return dirs
    def _extract_fingerprints(self: Self, dirs: list) -> list[SkillFingerprint]:
        fingerprints = []
        for skill_dir in dirs:
            fp = extract_skill_fingerprint(Path(skill_dir))
            if fp:
                fingerprints.append(fp)
        return fingerprints
    @staticmethod
    def _dedupe_fingerprints(
            fingerprints: list[SkillFingerprint]) -> list[SkillFingerprint]:
        seen: set[tuple[str, str]] = set()
        deduped: list[SkillFingerprint] = []
        for fp in fingerprints:
            identity = _skill_identity(fp.skill_name, fp.skill_dir)
            if identity in seen:
                _log.warning('deduplicate 跳过重复技能指纹（保留首个）: %s',
                             fp.skill_dir or fp.skill_name)
                continue
            seen.add(identity)
            deduped.append(fp)
        return deduped
    def _build_pairs(self: Self, fingerprints: list[SkillFingerprint]) -> list[OverlapPair]:
        pairs = []
        ordered = sorted(
            fingerprints,
            key=lambda fp: _skill_identity(fp.skill_name, fp.skill_dir))
        for i, a in enumerate(ordered):
            for b in ordered[i + 1:]:
                pairs.append(self._compare_pair(a, b))
        return pairs
    def scan(self: Self, skills_root: str,
             threshold: float = _DEFAULT_OVERLAP_THRESHOLD) -> DeduplicationReport:
        threshold = self._normalize_scan_threshold(threshold)
        normalized_root = normalize_out_path(skills_root)
        if normalized_root is None:
            _log.warning('scan skills_root 非法或空白: %r，返回空去重报告',
                         skills_root)
            return self._empty_scan_report(
                skills_root,
                '技能根目录参数非法或空白: ' + repr(skills_root)[:200])[1]
        skill_dirs, error_report = self._collect_skill_dirs(normalized_root)
        if error_report is not None:
            return error_report
        return self._build_scan_report(normalized_root, skill_dirs, threshold)
    @staticmethod
    def _normalize_scan_threshold(threshold: float) -> float:
        if not isinstance(threshold, (int, float)) or isinstance(threshold, bool):
            _log.warning('scan threshold 非数字或布尔: %r，回退默认 %s',
                         threshold, _DEFAULT_OVERLAP_THRESHOLD)
            return _DEFAULT_OVERLAP_THRESHOLD
        if isinstance(threshold, float) and not math.isfinite(threshold):
            _log.warning('scan threshold 非有限值: %r，回退默认 %s',
                         threshold, _DEFAULT_OVERLAP_THRESHOLD)
            return _DEFAULT_OVERLAP_THRESHOLD
        if threshold < 0 or threshold > 1:
            _log.warning('scan threshold 超出 [0, 1]: %r，回退默认 %s',
                         threshold, _DEFAULT_OVERLAP_THRESHOLD)
            return _DEFAULT_OVERLAP_THRESHOLD
        return threshold
    @staticmethod
    def _empty_scan_report(skills_root,
                           issue: str) -> tuple[list[Path], DeduplicationReport]:
        report = DeduplicationReport(skills_root=str(skills_root))
        report.issues = [issue]
        return [], report
    @staticmethod
    def _collect_skill_dirs(skills_root: str
                            ) -> tuple[list[Path], DeduplicationReport | None]:
        root = Path(skills_root)
        if not root.is_dir():
            _log.warning('skills_root 不存在或非目录，返回空去重报告: %s', skills_root)
            return SkillDeduplicationEngine._empty_scan_report(
                skills_root, '技能根目录不存在或不可读')
        try:
            skill_dirs = [d for d in root.iterdir()
                          if d.is_dir() and (d / 'SKILL.md').exists()]
        except OSError as exc:
            _log.warning('技能根目录不可读，返回空去重报告 %s: %s', skills_root, exc)
            return SkillDeduplicationEngine._empty_scan_report(
                skills_root, '技能根目录不可读: ' + str(exc))
        return skill_dirs, None
    def _build_scan_report(self: Self, skills_root: str, skill_dirs: list[Path],
                           threshold: float) -> DeduplicationReport:
        dedup_result = self.deduplicate([str(d) for d in skill_dirs])
        pairs = dedup_result.get('pairs', [])
        merge_plan = dedup_result.get('merge_plan', [])
        high_risk = [p for p in pairs if p.overall_overlap >= threshold]
        redundancy_score = (round(len(high_risk) / max(len(pairs), 1) * 100, 1)
                           if pairs else 0.0)
        report = DeduplicationReport(
            skills_root=skills_root, total_skills=len(skill_dirs),
            overlap_pairs=pairs, high_risk_pairs=high_risk,
            redundancy_score=redundancy_score, merge_plan=merge_plan)
        report.issues = self._generate_issues(report)
        report.suggestions = self._generate_suggestions(report)
        _log.info("scan 完成: %d 技能, %d 重叠对, %d 高风险, 冗余度 %.1f%%",
                  len(skill_dirs), len(pairs), len(high_risk),
                  redundancy_score)
        return report
    def _compare_pair(self: Self, a: SkillFingerprint, b: SkillFingerprint) -> OverlapPair:
        pair = OverlapPair(
            skill_a=a.skill_name, skill_b=b.skill_name,
            skill_a_dir=a.skill_dir, skill_b_dir=b.skill_dir)
        pair.semantic_similarity = jaccard(
            word_tokens(a.description), word_tokens(b.description))
        pair.keyword_overlap = jaccard(
            {k.lower() for k in a.keywords}, {k.lower() for k in b.keywords})
        pair.action_overlap = jaccard(a.action_verbs, b.action_verbs)
        pair.domain_overlap = jaccard(a.domain_nouns, b.domain_nouns)
        pair.overall_overlap = round(
            pair.semantic_similarity * 0.35
            + pair.keyword_overlap * 0.25
            + pair.action_overlap * 0.2
            + pair.domain_overlap * 0.2,
            2,
        )
        pair.merge_strategy = self._determine_merge_strategy(pair.overall_overlap)
        pair.recommendation = self._generate_recommendation(a, b, pair)
        return pair
    def _determine_merge_strategy(self: Self, overlap: float) -> str:
        if overlap >= _MERGE_FULL_THRESHOLD:
            return '完全合并: 保留脚本和测试更完整的技能作为主干，删除另一个'
        if overlap >= _MERGE_CONSOLIDATE_THRESHOLD:
            return '功能归并: 将B作为A的子模块或扩展功能，保留单一入口'
        if overlap >= _DEFAULT_OVERLAP_THRESHOLD:
            return '差异化重构: 明确划分两者的使用边界，通过负例防御消除重叠'
        return '无需合并'
    def _generate_recommendation(self: Self, a: SkillFingerprint, b: SkillFingerprint, pair: OverlapPair) -> str:
        label_a, label_b = a.skill_name, b.skill_name
        if (a.skill_name == b.skill_name
                and _skill_identity(a.skill_name, a.skill_dir)
                != _skill_identity(b.skill_name, b.skill_dir)):
            label_a, label_b = a.skill_dir, b.skill_dir
        if pair.overall_overlap >= _MERGE_FULL_THRESHOLD:
            score_a = int(a.has_scripts) + int(a.has_tests)
            score_b = int(b.has_scripts) + int(b.has_tests)
            winner = label_a if score_a >= score_b else label_b
            return f"建议保留 '{winner}'（脚本/测试更完整），将另一个的功能迁移后归档"
        if pair.overall_overlap >= _MERGE_CONSOLIDATE_THRESHOLD:
            return f"建议将 '{label_b}' 的核心能力作为扩展函数整合进 '{label_a}'"
        return '建议通过强化负例防御和差异化描述降低重叠'
    def _generate_merge_plan(self: Self, pairs: list[OverlapPair]) -> list[dict]:
        plan = []
        handled = set()
        for pair in pairs:
            if pair.overall_overlap < _MERGE_CONSOLIDATE_THRESHOLD:
                continue
            identity_a = _skill_identity(pair.skill_a, pair.skill_a_dir)
            identity_b = _skill_identity(pair.skill_b, pair.skill_b_dir)
            if identity_a == identity_b:
                continue
            key = tuple(sorted([identity_a, identity_b]))
            if key in handled:
                continue
            handled.add(key)
            plan.append({
                'action': ('MERGE' if pair.overall_overlap >= _MERGE_FULL_THRESHOLD
                           else 'CONSOLIDATE'),
                'skill_a': pair.skill_a,
                'skill_b': pair.skill_b,
                'skill_a_dir': pair.skill_a_dir,
                'skill_b_dir': pair.skill_b_dir,
                'overlap': pair.overall_overlap,
                'strategy': pair.merge_strategy,
                'recommendation': pair.recommendation,
            })
        return plan
    def _generate_issues(self: Self, report: DeduplicationReport) -> list[str]:
        issues = []
        if report.redundancy_score > 30:
            issues.append(f'技能目录冗余度高达 {report.redundancy_score:.1f}%，存在严重的可发现性危机')
        if len(report.high_risk_pairs) > 3:
            issues.append(f'发现 {len(report.high_risk_pairs)} 对高风险重叠技能，Agent 容易混淆')
        return issues
    def _generate_suggestions(self: Self, report: DeduplicationReport) -> list[str]:
        suggestions = []
        if report.redundancy_score > 20:
            suggestions.append('[数量治理] 优先合并重叠度>=0.85的技能对，将技能总数控制在合理范围')
        suggestions.append('[差异化] 对重叠度0.6-0.75的技能对，强化负例防御和差异化描述')
        suggestions.append('[归并策略] 保留脚本/测试最完整的技能作为主干，将其他技能的功能迁移后归档')
        suggestions.append('[领域拆分] 如果同一领域技能过多，考虑按子领域或子任务进一步拆分')
        return suggestions
def export_merge_plan(report: DeduplicationReport, output_path: str | None=None) -> str:
    if not isinstance(report, DeduplicationReport):
        _log.warning('export_merge_plan 入参非 DeduplicationReport: %r，降级空报告', report)
        report = DeduplicationReport()
    data = {'skills_root': report.skills_root, 'total_skills': report.total_skills, 'redundancy_score': report.redundancy_score, 'high_risk_count': len(report.high_risk_pairs), 'merge_plan': report.merge_plan}
    json_str = serialize_json(data, indent=2)
    out_path = normalize_out_path(output_path)
    if out_path is None:
        if output_path is not None:
            _log.warning('export_merge_plan output_path 非法: %r，跳过落盘', output_path)
        return json_str
    with guarded_open(out_path, 'w', encoding='utf-8', newline='\n') as f:
        f.write(json_str)
    _log.info("export_merge_plan 落盘: %s（%d 计划项）",
              out_path, len(report.merge_plan))
    return json_str
_DEDUPLICATION_ENGINE = SkillDeduplicationEngine()
run_deduplication = _DEDUPLICATION_ENGINE.deduplicate
scan_skill_deduplication = _DEDUPLICATION_ENGINE.scan
def _overlap(a: frozenset, b: frozenset) -> float:
    if not a or not b:
        return 0.0
    return len(a & b) / min(len(a), len(b))
_SEED_TOKEN_CACHE: dict[
    tuple[str, ...], tuple[tuple[str, frozenset], ...]
] | None = {}
def _bounded_cache_put(cache: dict, key: Any, value: Any) -> None:
    if key not in cache and len(cache) >= _DERIVED_CACHE_MAX_ENTRIES:
        cache.pop(next(iter(cache)))
    cache[key] = value
def seed_token_pairs(
        seeds: tuple[str, ...] | None = None
) -> tuple[tuple[str, frozenset], ...]:
    global _SEED_TOKEN_CACHE
    if _SEED_TOKEN_CACHE is None:
        _SEED_TOKEN_CACHE = {}
    key = TRIGGER_FUZZY_SEEDS if seeds is None else _vocab_tuple(seeds)
    cached = _SEED_TOKEN_CACHE.get(key)
    if cached is None:
        cached = tuple(
            (text, trigger_tokens(normalize_trigger_text(text)))
            for text in (normalize_text(s) for s in key) if text)
        _bounded_cache_put(_SEED_TOKEN_CACHE, key, cached)
    return cached
_CUSTOM_KEYWORDS_CACHE: dict[
    str, tuple[bytes, tuple[str, ...]]
] = {}
def _clean_custom_keywords(raw: object) -> tuple[str, ...]:
    if not isinstance(raw, list):
        return ()
    return tuple(k.strip() for k in raw
                 if isinstance(k, str) and k.strip())
def load_custom_trigger_keywords(skill_dir: str | None) -> list[str]:
    if not skill_dir:
        return []
    try:
        path = trigger_keywords_path(skill_dir)
        with open(path, "rb") as f:
            payload = f.read()
        content_key = hashlib.sha256(payload).digest()
        cached = _CUSTOM_KEYWORDS_CACHE.get(path)
        if cached is not None and cached[0] == content_key:
            return list(cached[1])
        data = json.loads(payload)
        raw = data.get("keywords") if isinstance(data, dict) else data
        kws = _clean_custom_keywords(raw)
        _bounded_cache_put(
            _CUSTOM_KEYWORDS_CACHE, path, (content_key, kws))
        return list(kws)
    except Exception as e:
        _log.debug("自定义触发词加载跳过: %s", e)
        return []
def load_skill_trigger_vocabulary(
        skill_dir: str | Path) -> TriggerVocabulary:
    try:
        meta = read_skill_md(skill_dir)
    except (OSError, UnicodeDecodeError) as e:
        _log.warning("[Trigger] 读取技能触发词失败 %s: %s", skill_dir, e)
        return TriggerVocabulary(keywords=(), negative_contexts=(),
                                 weak_tokens=(), context_tokens=(),
                                 fuzzy_seeds=())
    raw_keywords = meta.get("keywords", [])
    if isinstance(raw_keywords, str):
        raw_keywords = [raw_keywords]
    elif not isinstance(raw_keywords, (list, tuple)):
        raw_keywords = []
    keywords = tuple(dict.fromkeys(
        keyword.strip() for keyword in raw_keywords
        if isinstance(keyword, str) and keyword.strip()))
    return TriggerVocabulary(
        keywords=keywords, negative_contexts=(), weak_tokens=(),
        context_tokens=(), fuzzy_seeds=())
def _weak_ctx_hits(
        norm: str,
        vocabulary: TriggerVocabulary | None = None
) -> tuple[list[str], list[str]]:
    vocab = _as_vocabulary(vocabulary) or DEFAULT_TRIGGER_VOCABULARY
    weak = [w for w in vocab.weak_tokens
            if keyword_matches(w, norm)]
    ctx = [c for c in vocab.context_tokens
           if keyword_matches(c, norm)]
    return weak, ctx
def _fuzzy_seed_match(
        norm: str,
        vocabulary: TriggerVocabulary | None = None
) -> tuple[str, float]:
    vocab = _as_vocabulary(vocabulary) or DEFAULT_TRIGGER_VOCABULARY
    query_tokens = trigger_tokens(norm)
    best_seed, best_score = "", 0.0
    for seed, seed_tokens in seed_token_pairs(vocab.fuzzy_seeds):
        score = max(jaccard(query_tokens, seed_tokens),
                    _overlap(query_tokens, seed_tokens))
        if score > best_score:
            best_seed, best_score = seed, score
    return best_seed, best_score
def _custom_trigger_hits(norm: str, skill_dir: str | None) -> list[str]:
    return [k for k in load_custom_trigger_keywords(skill_dir)
            if keyword_matches(k, norm)]
def _soft_verdict(
        norm: str, ev: dict,
        vocabulary: TriggerVocabulary | None = None
) -> tuple[str, str] | None:
    weak, ctx = _weak_ctx_hits(norm, vocabulary)
    if weak and ctx:
        ev["weak_tokens"], ev["context_tokens"] = weak, ctx
        return "soft", "weak_ctx"
    if len(norm) >= TRIGGER_FUZZY_MIN_LEN:
        best_seed, best_score = _fuzzy_seed_match(norm, vocabulary)
        ev["fuzzy"] = {"seed": best_seed, "score": round(best_score, 3)}
        if best_score >= TRIGGER_FUZZY_MIN_SCORE:
            return "soft", "fuzzy"
    return None
_STRONG_HIT_CONTAINERS = (list, tuple, set, frozenset)
def _strong_hits_of(strong_hits: list[str] | None) -> list[str]:
    return [
        hit for hit in (strong_hits or [])
        if isinstance(hit, str) and hit
    ]
def _negatives_in(
        norm: str,
        vocabulary: TriggerVocabulary | None = None
) -> list[str]:
    vocab = _as_vocabulary(vocabulary) or DEFAULT_TRIGGER_VOCABULARY
    return [n for n in vocab.negative_contexts
            if keyword_matches(n, norm)]
def probe_pipeline_trigger(
        text: str,
        strong_hits: list[str] | None = None,
        skill_dir: str | None = None,
        vocabulary: TriggerVocabulary | None = None) -> dict:
    out: dict = {
        "decision": "miss",
        "confidence": "none",
        "evidence": {"strong_hits": [], "custom_hits": [],
                     "mandatory_hits": [], "weak_tokens": [],
                     "context_tokens": [], "fuzzy": None,
                     "negatives_blocked": []},
    }
    out["decision"], out["confidence"] = _probe_decision(
        text, strong_hits, skill_dir, out["evidence"], vocabulary)
    return _finalize_probe(out)
def _probe_decision(text: str, strong_hits: list[str] | None,
                    skill_dir: str | None, ev: dict,
                    vocabulary: TriggerVocabulary | None = None
                    ) -> tuple[str, str]:
    if not text or not isinstance(text, str):
        return "miss", "none"
    if strong_hits is not None and not isinstance(
            strong_hits, _STRONG_HIT_CONTAINERS):
        _log.warning(
            "probe_pipeline_trigger strong_hits 须为字符串序列，"
            "收到 %s；改从文本重新检测",
            type(strong_hits).__name__)
        strong_hits = None
    norm = normalize_trigger_text(text)
    strong = (_strong_hits_of(strong_hits) if strong_hits is not None
              else match_pipeline_trigger(norm, vocabulary))
    ev["strong_hits"] = strong
    mandatory_hits = [kw for kw in MANDATORY_PIPELINE_TRIGGER_KEYWORDS
                      if keyword_matches(kw, norm)]
    ev["mandatory_hits"] = mandatory_hits
    negatives = _negatives_in(norm, vocabulary)
    if negatives:
        ev["negatives_blocked"] = negatives
    if negatives and not mandatory_hits:
        return "miss", "none"
    if negatives and mandatory_hits:
        ev["mandatory_bypass"] = True
    custom = _custom_trigger_hits(norm, skill_dir)
    ev["custom_hits"] = custom
    if mandatory_hits or strong or custom:
        return "hit", "strong"
    soft = _soft_verdict(norm, ev, vocabulary)
    return soft if soft else ("miss", "none")
def _finalize_probe(out: dict) -> dict:
    out["recommendation"] = {"hit": "execute", "soft": "confirm",
                             "miss": "none"}[out["decision"]]
    return out
SPOKEN_PATTERNS: dict[str, list[str]] = {
    "create": ["做个", "建个", "弄个", "整一个", "搞一个",
               "whip up", "put together", "spin up", "throw together"],
    "build": ["搭个", "建个", "弄个", "整一个",
              "set up", "build out"],
    "check": ["看看", "查查", "检查下", "查一下", "看下",
              "take a look", "have a look", "check out", "look over"],
    "diag": ["诊断下", "审一下", "查查",
             "look into", "dig into", "figure out what's wrong"],
    "optimize": ["优化下", "改改进", "调一下", "优化优化",
                 "speed up", "tune up", "clean up"],
    "analyze": ["分析下", "分析分析", "看看怎么样",
                "go over", "run through", "break down"],
    "fix": ["修一下", "修修", "改改", "修好",
            "sort out", "patch up", "fix up"],
    "convert": ["转一下", "换成", "转成", "变一下"],
    "generate": ["生成个", "做个", "出个", "弄个"],
    "extract": ["提取下", "抽出来", "拿出去"],
    "merge": ["合并下", "合一下", "拼一起"],
    "split": ["拆开", "分开", "拆一下"],
}
COLLOQUIAL_TRIGGER_WORDS: tuple[str, ...] = (
    "做个", "建个", "弄个", "生成个", "出个", "搭个",
    "诊断下", "审一下", "查查", "看看", "检查下", "优化下",
    "whip up", "put together", "spin up", "set up",
    "take a look", "have a look", "check out", "look into",
    "run through", "go over", "sort out", "clean up",
)
ROLE_PERSPECTIVES: dict[str, dict[str, Any]] = {
    "developer": {
        "label": "开发工程师", "prefix": "[开发]",
        "patterns": ["开发", "编程", "编码", "implement", "write code", "coding", "build", "代码"],
    },
    "tester": {
        "label": "测试工程师", "prefix": "[测试]",
        "patterns": ["测试", "验证", "regression", "coverage", "质量保障", "验收"],
    },
    "security": {
        "label": "安全工程师", "prefix": "[安全]",
        "patterns": ["安全", "审计", "vulnerability", "权限", "保密", "加密", "隐私"],
    },
    "architect": {
        "label": "架构师", "prefix": "[架构]",
        "patterns": ["架构", "设计", "模式", "设计评审", "技术选型", "design pattern"],
    },
    "manager": {
        "label": "管理者", "prefix": "[管理]",
        "patterns": ["管理", "跟进", "追踪", "报告", "review", "评估", "计划", "规划", "组织"],
    },
}
STANDARD_SECTIONS: list[dict[str, Any]] = [
    {
        "key": "description_block",
        "title": "",
        "required": True,
        "description": "description 区块（frontmatter 之后的首段）",
    },
    {
        "key": "capability_boundary",
        "title": "技能能力边界",
        "required": True,
        "description": "能做/不能做（In Scope / Out of Scope）",
        "aliases": ("Capability Boundary", "Scope and Limitations"),
    },
    {
        "key": "agent_guidance",
        "title": "Agent 决策指引",
        "required": True,
        "description": "何时加载本技能、加载后操作步骤",
        "aliases": ("Agent Guidance", "Agent Decision Guide"),
    },
    {
        "key": "trigger_conditions",
        "title": "触发条件",
        "required": True,
        "description": "应当触发 / 不应触发的条件列表",
        "aliases": ("Trigger Conditions", "When to Use"),
    },
    {
        "key": FIELD_TRIGGER_EXAMPLES,
        "title": "触发示例",
        "required": False,
        "description": "用户可说的场景化原话",
        "aliases": ("Trigger Examples",),
    },
    {
        "key": "quick_start",
        "title": "快速入门",
        "required": True,
        "description": "最小的可执行代码示例或调用方式",
        "aliases": ("Quick Start", "Getting Started"),
    },
    {
        "key": "domain_overview",
        "title": "域总览",
        "required": True,
        "description": "模块能力全景表（域 | 模块数 | 入口函数）",
        "aliases": ("Domain Overview", "Module Overview"),
    },
    {
        "key": "file_structure",
        "title": "文件结构",
        "required": False,
        "description": "目录树，展示 .py 文件组织",
        "aliases": ("File Structure", "Project Structure"),
    },
    {
        "key": "use_cases",
        "title": "典型应用场景",
        "required": False,
        "description": "场景 | 入口 | 说明 映射表",
        "aliases": ("Use Cases", "Usage Scenarios"),
    },
    {
        "key": "script_inventory",
        "title": "脚本清单",
        "required": False,
        "description": "脚本名称、用途和调用方式",
        "aliases": ("Script Inventory",),
    },
    {
        "key": "script_vs_api",
        "title": "脚本 vs API 决策指引",
        "required": False,
        "description": "何时用 CLI、何时用 API",
        "aliases": ("Script vs API",),
    },
    {
        "key": "key_constraints",
        "title": "关键约束",
        "required": False,
        "description": "核心约束和限制",
        "aliases": ("Key Constraints", "Constraints"),
    },
    {
        "key": "design_principles",
        "title": "设计原则",
        "required": False,
        "description": "核心设计理念和行为铁律",
        "aliases": ("Design Principles",),
    },
    {
        "key": "gotchas",
        "title": "Gotchas",
        "required": False,
        "description": "踩坑记录与已知陷阱",
        "aliases": ("Known Issues", "Pitfalls"),
    },
    {
        "key": "six_dim_diagnosis",
        "title": "六维可发现性诊断",
        "required": False,
        "description": "六维可发现性评分表",
        "aliases": ("Discoverability Diagnosis", "Six-Dimension Diagnosis"),
    },
]
CONTENT_QUALITY_RULES: list[dict[str, Any]] = [
    {
        "key": "description_completeness",
        "title": "描述完整性",
        "description": "description 区块应包含技能用途、触发条件和边界说明",
    },
    {
        "key": "capability_boundary",
        "title": "能力边界清晰",
        "description": "能做/不能做列表应覆盖且不重叠",
    },
    {
        "key": "trigger_saturation",
        "title": "触发词饱和覆盖",
        "description": "触发条件应覆盖口语化、正式、中英文多维度表达",
    },
    {
        "key": "examples_coverage",
        "title": "示例覆盖度",
        "description": "触发示例应 >= 5 条，覆盖核心场景",
    },
    {
        "key": "structure_compliance",
        "title": "结构合规",
        "description": "应包含技能能力边界、Agent 决策指引、触发条件等标准章节",
    },
    {
        "key": CAT_DISCOVERABILITY,
        "title": "可发现性",
        "description": "六维可发现性检查应全部通过",
    },
]
_EXTRA_FRONTMATTER_ALLOWED = UPLOAD_ALLOWED_FIELDS - {"name", "description"}
_FLOW_SEQUENCE_SPECIALS = frozenset(",[]{}")
def _flow_list_item(item: Any) -> str:
    if item is None:
        return "null"
    text = safe_text(item)
    quoted = yaml_safe_quote(text)
    if quoted != text:
        return quoted
    if _FLOW_SEQUENCE_SPECIALS & set(text):
        return serialize_json(text)
    return quoted
def _safe_frontmatter_mapping(value: dict) -> str:
    try:
        return serialize_json(value)
    except (TypeError, ValueError, RecursionError) as e:
        log_swallowed(__name__, e,
                      context='_safe_frontmatter_mapping:dict')
        return yaml_safe_quote(safe_text(value))
def _format_extra_frontmatter_line(key: str, value: Any) -> str:
    if isinstance(value, list):
        items_str = ", ".join(_flow_list_item(item) for item in value)
        return f"{key}: [{items_str}]"
    if isinstance(value, dict):
        return f"{key}: {_safe_frontmatter_mapping(value)}"
    return f"{key}: {yaml_safe_quote(safe_text(value))}"
def _extra_frontmatter_lines(extra_frontmatter: dict | None) -> list[str]:
    extra = extra_frontmatter if isinstance(extra_frontmatter, dict) else {}
    return [
        _format_extra_frontmatter_line(key, value)
        for key, value in extra.items()
        if key in _EXTRA_FRONTMATTER_ALLOWED and value is not None
    ]
def sanitize_upload_description(description: Any) -> str:
    text = safe_text(description or "")
    text, _ = _uv_rewrite_brackets(text)
    text, _ = _uv_rewrite_truncate(text)
    return text
def build_skill_frontmatter(skill_name: str, description: str,
                            extra_frontmatter: dict | None = None) -> str:
    safe_desc = sanitize_upload_description(description)
    safe_name = sanitize_skill_name(safe_text(skill_name or ''))
    lines = ["---", f"name: {yaml_safe_quote(safe_name)}"]
    lines.append(yaml_safe_desc_line(safe_desc))
    lines.extend(_extra_frontmatter_lines(extra_frontmatter))
    lines.append("---")
    _log.info("SKILL.md frontmatter 生成: %s (desc %d 字符)",
              safe_name, len(safe_desc))
    return "\n".join(lines)
UPLOAD_COMPLIANCE_RULES: list[dict[str, Any]] = [
    {"id": "UV-001", "severity": "critical", "desc": "frontmatter YAML 可解析"},
    {"id": "UV-002", "severity": "medium", "desc": "frontmatter 字段白名单"},
    {"id": "UV-003", "severity": "critical",
     "desc": f"name 必填、为字符串且长度达标（≥{SKILL_NAME_MIN_LEN} 字符）"},
    {"id": "UV-004", "severity": "high", "desc": "name kebab-case 格式"},
    {"id": "UV-005", "severity": "high", "desc": f"SKILL.md 行数限制（≤{SKILL_MD_LINE_LIMIT} 行）"},
    {"id": "UV-006", "severity": "high", "desc": f"name 长度限制（≤{MAX_SKILL_NAME_LENGTH} 字符）"},
    {"id": "UV-007", "severity": "high", "desc": "目录名与 name 一致"},
    {"id": "UV-008", "severity": "critical", "desc": "description 必填、为字符串且长度达标（下限见 skill_doc_diagnoser 上传域检查器）"},
    {"id": "UV-009", "severity": "medium", "desc": "description 无尖括号"},
    {"id": "UV-010", "severity": "high", "desc": f"description 长度限制（≤{UPLOAD_DESC_MAX_CHARS} 字符）"},
    {"id": "UV-011", "severity": "high", "desc": "name 无连字符边界问题"},
    {"id": "UV-012", "severity": "high", "desc": "description 无控制字符"},
]
def get_standard_sections() -> list[dict[str, Any]]:
    return [dict(s) for s in STANDARD_SECTIONS]
def get_content_quality_rules() -> list[dict[str, Any]]:
    return [dict(r) for r in CONTENT_QUALITY_RULES]
def get_upload_compliance_rules() -> list[dict[str, Any]]:
    return [dict(r) for r in UPLOAD_COMPLIANCE_RULES]
def _uv_rewrite_brackets(description: str) -> tuple[str, str | None]:
    if "<" not in description and ">" not in description:
        return description, None
    return (description.replace("<", "（").replace(">", "）"),
            "[UV-009] 已把 description 中的尖括号替换为全角括号")
def _uv_rewrite_truncate(description: str) -> tuple[str, str | None]:
    if len(description) <= UPLOAD_DESC_MAX_CHARS:
        return description, None
    return (description[:UPLOAD_DESC_MAX_CHARS - 3] + "...",
            f"[UV-010] description 已截断至 {UPLOAD_DESC_MAX_CHARS} 字符以内")
_UV_DESC_REWRITERS = {
    "UV-009": _uv_rewrite_brackets,
    "UV-010": _uv_rewrite_truncate,
}
_UV_STATIC_ADVICE = {
    "UV-001": "frontmatter YAML 语法错误，重构时已使用安全引号修复",
    "UV-002": "移除 frontmatter 中不允许的字段（需手动确认）",
}
_UV_SUGGESTION_RULES = frozenset({
    "UV-003", "UV-005", "UV-006", "UV-007", "UV-008", "UV-011", "UV-012",
})
def normalize_suggestion_text(issue: DocQualityIssue, limit: int) -> str:
    suggestion = issue.suggestion
    if suggestion is None:
        return ""
    return str(suggestion)[:limit]
def _issue_entries(issues: Any, context: str) -> list[DocQualityIssue]:
    if not isinstance(issues, (list, tuple)):
        if issues is not None:
            log_swallowed(
                __name__, TypeError(f"issues 载体非法: {type(issues).__name__}"),
                context=f"{context}:issues-container")
        return []
    kept = [issue for issue in issues if isinstance(issue, DocQualityIssue)]
    dropped = len(issues) - len(kept)
    if dropped:
        log_swallowed(
            __name__, TypeError(f"issues 含 {dropped} 个非 DocQualityIssue 条目"),
            context=f"{context}:issue-shape")
    return kept
def _uv_advice_message(rid: str, issue: DocQualityIssue,
                       skill_name: str) -> str | None:
    static = _UV_STATIC_ADVICE.get(rid)
    if static is not None:
        return f"[{rid}] {static}"
    if rid == "UV-004":
        safe_name = sanitize_skill_name(skill_name)
        return f"[UV-004] name 应为 kebab-case 格式，已消毒为: '{safe_name}'"
    if rid in _UV_SUGGESTION_RULES:
        return f"[{rid}] {normalize_suggestion_text(issue, 100)}"
    return None
def fix_upload_violation_descs(skill_name: str,
                                description: str,
                                issues: list[DocQualityIssue]) -> dict[str, Any]:
    improvements: list[str] = []
    new_desc = normalize_text(description)
    for issue in _issue_entries(issues, 'fix_upload_violation_descs'):
        rewrite = _UV_DESC_REWRITERS.get(issue.rule_id)
        if rewrite is not None:
            new_desc, message = rewrite(new_desc)
            if message is not None:
                improvements.append(message)
            continue
        advice = _uv_advice_message(issue.rule_id, issue, skill_name)
        if advice is not None:
            improvements.append(advice)
    return {"description": new_desc, "improvements": improvements}
TYPE_KEYWORDS = {
    "xlsx": ["excel", "spreadsheet", "xlsx", "表格", "sheet", "workbook"],
    "docx": ["word", "document", "docx", "文档", "文字"],
    "pptx": ["powerpoint", "presentation", "pptx", "演示", "幻灯片", "ppt"],
    "pdf": ["pdf", "portable document"],
    "skill": ["skill", "oracle", "技能", "builder", "构建"],
}
@lru_cache(maxsize=_DERIVED_CACHE_MAX_ENTRIES)
def _keyword_probe(keyword: str) -> re.Pattern[str] | None:
    if keyword.isascii() and keyword.isalpha():
        return re.compile(
            _ascii_boundary_pattern(keyword, suffix_boundary=False))
    return None
def _keyword_hit(body_lower: str, keyword: Any) -> bool:
    if not isinstance(keyword, str) or not keyword:
        return False
    keyword = keyword.lower()
    probe = _keyword_probe(keyword)
    if probe is not None:
        return bool(probe.search(body_lower))
    return keyword in body_lower
def count_keyword_hits(body: Any, keywords: Any) -> int:
    if not isinstance(body, str):
        return 0
    corpus = body.lower()
    keywords = (keywords,) if isinstance(keywords, str) else keywords
    if isinstance(keywords, Mapping):
        _log.debug("count_keyword_hits: keywords 为 Mapping，键不计入关键词")
        return 0
    try:
        items = iter(keywords)
    except TypeError:
        _log.debug("count_keyword_hits: keywords 不可迭代，零计数: %s",
                     type(keywords).__name__)
        return 0
    return sum(1 for kw in items if _keyword_hit(corpus, kw))
def best_keyword_match(text: str, keyword_map: dict, default: str) -> str:
    scores = {}
    for key, keywords in keyword_map.items():
        score = count_keyword_hits(text, keywords)
        if score > 0:
            scores[key] = score
    if scores:
        return max(scores, key=scores.get)
    return default
def infer_skill_type(name: str, description: str = "") -> str:
    text = (normalize_text(name) + " " + normalize_text(description)).lower()
    return best_keyword_match(text, TYPE_KEYWORDS, "generic")
_M1_DEDUCTIONS = {"critical": 40.0, "high": 15.0}
_M3_MIN_HITS = 5
_M4_MIN_HITS = 2
@dataclass(frozen=True)
class _PatternDimSpec:
    dim_id: str
    dim_name: str
    rule_id: str
    min_hits: int
    per_hit: float
    weight: float
    issue_text: str
    suggestion: str
    detail_text: str
_M3_DIM_SPEC = _PatternDimSpec(
    dim_id="M3", dim_name="口语化近义词密度", rule_id="SD-M3",
    min_hits=_M3_MIN_HITS, per_hit=15.0, weight=0.25,
    issue_text="口语化近义词仅{hits}个，建议>={min_hits}个",
    suggestion="添加'帮我看'/'查一下'/'检查下'/'修一下'等口语表达",
    detail_text="命中{hits}个口语化表达",
)
_M4_DIM_SPEC = _PatternDimSpec(
    dim_id="M4", dim_name="角色视角分层", rule_id="SD-M4",
    min_hits=_M4_MIN_HITS, per_hit=20.0, weight=0.25,
    issue_text="角色视角关键词仅{hits}个，建议覆盖开发/测试/安全等角色",
    suggestion="添加面向不同角色的用语",
    detail_text="命中{hits}个角色视角关键词",
)
def _pattern_dimension(desc_lower: str, all_issues: list,
                       spec: _PatternDimSpec,
                       patterns: Iterable[str],
                       doc_profile: str) -> SubDimensionScore:
    hits = sum(1 for pattern in dict.fromkeys(patterns)
               if count_keyword_hits(desc_lower, pattern))
    dim_issues: list[DocQualityIssue] = []
    if hits < spec.min_hits and doc_profile == "template":
        dim_issues.append(make_matching_issue(
            spec.rule_id, "medium",
            spec.issue_text.format(hits=hits, min_hits=spec.min_hits),
            spec.suggestion))
    all_issues.extend(dim_issues)
    if not desc_lower:
        return SubDimensionScore(
            dim_id=spec.dim_id, dim_name=spec.dim_name,
            category="matching", score=65.0, weight=spec.weight,
            issues=dim_issues,
            detail=f"{spec.detail_text.format(hits=hits)}（描述为空，未评估基线）",
        )
    return SubDimensionScore(
        dim_id=spec.dim_id, dim_name=spec.dim_name, category="matching",
        score=min(100.0, hits * spec.per_hit), weight=spec.weight,
        issues=dim_issues,
        detail=spec.detail_text.format(hits=hits),
    )
def _m1_description_sufficiency(
        description: str, matching_issues: list) -> SubDimensionScore:
    m1_issues = [i for i in matching_issues if i.rule_id in ("DR-001", "DR-004")]
    if not description:
        m1_score = 0.0
    elif len(description) < 30:
        m1_score = 30.0
    elif len(description) < 80:
        m1_score = 60.0
    else:
        penalty = sum(_M1_DEDUCTIONS.get(i.severity, 0.0) for i in m1_issues)
        m1_score = max(0.0, 100.0 - penalty)
    return SubDimensionScore(
        dim_id="M1", dim_name="description充分性", category="matching",
        score=m1_score, weight=0.30,
        issues=m1_issues,
        detail=f"长度={len(description)}字符" + (f", {len(m1_issues)}项问题" if m1_issues else ""),
    )
def _m2_bilingual_coverage(description: str, all_issues: list) -> SubDimensionScore:
    content = _TRIGGER_COMMAND_PREFIX_RE.sub("", description, count=1)
    has_cn = bool(re.search(RE_CHINESE_CHARS, content))
    has_en = bool(_ASCII_WORD_RE.search(content))
    m2_issues: list[DocQualityIssue] = []
    m2_score = 100.0
    if not has_cn:
        m2_score = 30.0
        m2_issues.append(make_matching_issue(
            "SD-M2-CN", "high", "description 缺少中文内容", "添加中文关键词"))
    if not has_en:
        m2_score = 0.0 if not has_cn else 40.0
        m2_issues.append(make_matching_issue(
            "SD-M2-EN", "high", "description 缺少英文内容", "添加英文关键词"))
    all_issues.extend(m2_issues)
    return SubDimensionScore(
        dim_id="M2", dim_name="中英文双语覆盖", category="matching",
        score=m2_score, weight=0.20,
        issues=m2_issues,
        detail=f"中文={'有' if has_cn else '无'}, 英文={'有' if has_en else '无'}",
    )
def matching_dimensions(description, all_issues,
                        doc_profile: str) -> list[SubDimensionScore]:
    description, all_issues = normalize_entry_inputs(
        description, all_issues, text=True)
    if isinstance(all_issues, list):
        kept = _issue_entries(all_issues, 'matching_dimensions')
        if len(kept) != len(all_issues):
            all_issues[:] = kept
    else:
        all_issues = list(_issue_entries(
            tuple(all_issues) if isinstance(all_issues, (tuple, set, frozenset))
            else None,
            'matching_dimensions'))
    matching_issues = [i for i in all_issues if i.category == "matching"]
    desc_lower = description.lower()
    return [
        _m1_description_sufficiency(description, matching_issues),
        _m2_bilingual_coverage(description, all_issues),
        _pattern_dimension(
            desc_lower, all_issues, _M3_DIM_SPEC,
            (p for patterns in SPOKEN_PATTERNS.values() for p in patterns),
            doc_profile),
        _pattern_dimension(
            desc_lower, all_issues, _M4_DIM_SPEC,
            (p for rp in ROLE_PERSPECTIVES.values()
             for p in rp.get("patterns", [])),
            doc_profile),
    ]
_POSITIVE_EXAMPLE_TEMPLATES: dict[str, tuple[str, ...]] = {
    "zh": (
        '帮我{phrase}',
        '我需要{phrase}',
        '请{phrase}一下',
    ),
    "en": (
        'Help me {phrase}',
        'I need to {phrase}',
        'Please {phrase}',
    ),
}
_NEGATIVE_EXAMPLE_QUERIES: dict[str, tuple[str, ...]] = {
    "zh": (
        '今天天气怎么样',
        '帮我播放音乐',
        '设置一个闹钟',
        '推荐一部电影',
        '翻译这段文字',
    ),
    "en": (
        "What's the weather like today?",
        'Play some music for me',
        'Set an alarm for 7am',
        'Recommend a good movie',
        'Translate this paragraph',
    ),
}
_NEGATIVE_QUERY_TABLE: tuple[tuple[tuple[str, ...], str, str], ...] = (
    (("skill", "技能"), "请帮我创建一个新技能",
     "Please create a new skill"),
    (("日常", "daily", "routine"), "请帮我安排明天的会议日程",
     "Please schedule tomorrow's meeting"),
    (("创意", "设计", "creative", "design"), "请帮我设计一个公司logo",
     "Please design a company logo"),
    (("数据查询", "data query", "data lookup"), "请帮我查询明天的天气预报",
     "Please check tomorrow's weather forecast"),
)
_DEFAULT_NEGATIVE_QUERY: dict[str, str] = {
    "zh": "请帮我推荐一本好书",
    "en": "Please recommend a good book",
}
_TASK_NOUN_SUFFIXES: tuple[str, ...] = ("任务", "task", "tasks")
def negative_query_for_boundary(boundary: str, language: str | None = None) -> str:
    scope = normalize_text(boundary).strip(SLOT_NOISE_CHARS)
    lang = (language if language in _DEFAULT_NEGATIVE_QUERY
            else detect_text_language(scope))
    if not scope:
        return _DEFAULT_NEGATIVE_QUERY.get(lang, _DEFAULT_NEGATIVE_QUERY["en"])
    scope_lower = scope.lower()
    if not scope_lower.startswith(("非", "not ")):
        for needles, zh_query, en_query in _NEGATIVE_QUERY_TABLE:
            if any(needle in scope_lower for needle in needles):
                return zh_query if lang == "zh" else en_query
    is_task = scope.casefold().endswith(_TASK_NOUN_SUFFIXES)
    if lang == "zh":
        return f"请帮我处理{scope}" if is_task else f"请帮我处理{scope}相关任务"
    return (f"Please help me with {scope}" if is_task
            else f"Please help me with a task related to {scope}")
DEFAULT_NUM_POSITIVE = 3
DEFAULT_NUM_NEGATIVE = 2
def normalize_nonnegative_count(value: object, default: int, label: str) -> int:
    if value is None:
        return default
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        _log.warning("%s: 数量形参 %r 不是非负整数，回退默认值 %s",
                     label, value, default)
        return default
    return value
def normalize_bool_flag(value: object, default: bool, label: str) -> bool:
    if value is None:
        return default
    if not isinstance(value, bool):
        _log.warning("%s: 布尔形参 %r 非 bool，回退默认值 %s",
                     label, value, default)
        return default
    return value
_BOUNDARY_SCOPE_MAX_CHARS = 80
_BOUNDARY_CN_VERB_ALT = (
    "适用于?|" + _EXT_CN_VERB_ALT + "|" + _CN_ACTION_VERB_ALT)
_BOUNDARY_CN_CAPABILITY_VERB_ALT = (
    r"适用于?|用于|处理|支持|负责|涉及|包含|包括|允许|接受")
_BOUNDARY_EN_VERBS = _EN_NEGATION_VERB_SKIP
_BOUNDARY_EN_MODAL_NEG_HEAD = (
    r"(?:" + _EN_MODAL_NEG_HEAD + r")(?!\s+(?:ONLY|JUST)\b)"
)
_BOUNDARY_PASSIVE_NEG_HEAD = (
    r"(?:IS|ARE|WAS|WERE)\s+NOT(?!\s+(?:ONLY|JUST)\b)"
    r"(?:\s+(?:SUPPORTED|HANDLED|COVERED|PROCESSED|INCLUDED|AVAILABLE|APPLICABLE|ALLOWED|RESPONSIBLE))?"
)
_BOUNDARY_NEG_HEADS = (
    r"(?:"
    r"不(?:适用于?|用于)|不是(?:用于)?|不做|不要(?:用于)?|请勿|禁止|勿|切勿"
    r"|(?:不|未)(?:受|被)支持"
    r"|不(?:" + _BOUNDARY_CN_CAPABILITY_VERB_ALT + r"|是|属于)"
    r"|不(?=(?:" + _BOUNDARY_CN_VERB_ALT + r"))"
    r"|不应(?:触发|使用|调用|加载)?"
    r"|(?:未|尚未|暂未)(?=(?:" + _BOUNDARY_CN_VERB_ALT + r"))"
    r"|(?:无法|不能|不会|无需|无须|不需|不必)(?=(?:"
    + _BOUNDARY_CN_VERB_ALT + r"))"
    r"|NOT\s+FOR"
    r"|NEVER(?:\s+(?:" + _BOUNDARY_EN_VERBS + r"))?(?:\s+FOR)?"
    r"|NOT\s+(?:INTENDED|DESIGNED)\s+FOR|NOT\s+APPLICABLE(?:\s+TO)?"
    r"|NOT\s+RESPONSIBLE\s+FOR|NOT\s+ALLOWED"
    r"|(?:" + _BOUNDARY_EN_MODAL_NEG_HEAD + r")"
    r"(?:\s+(?:" + _BOUNDARY_EN_VERBS + r"))?(?:\s+FOR)?"
    r"|" + _BOUNDARY_PASSIVE_NEG_HEAD + r"(?:\s+FOR)?"
    r"|\bNOT\b(?!\s+(?:ONLY|JUST)\b)"
    r")"
)
_BOUNDARY_NEG_HEAD_RE = re.compile(_BOUNDARY_NEG_HEADS, re.IGNORECASE)
_BOUNDARY_PREFIX_SCOPED_NEG_HEAD_RE = re.compile(
    _BOUNDARY_PASSIVE_NEG_HEAD + r"(?:\s+FOR)?", re.IGNORECASE,
)
_BOUNDARY_SCOPE_PREFIX_RE = re.compile(
    r'^(?:若|如果|when|if)\s*(?:(?:the|a|an)\s+)?(?:(?:主要|核心|main|primary)\s*)?'
    r'(?:产出|交付物|output|deliverable)\s*(?:为|是|is)?\s*',
    re.IGNORECASE)
_BOUNDARY_SCOPE_CONNECTOR_RE = re.compile(
    r'^(?:(?:also|and|but|plus|or)\s+|(?:此外|另外|同时|并且|也|还|但|不过|然而|则|并|而是)\s*)',
    re.IGNORECASE)
_BOUNDARY_SCOPE_TRAILING_CONNECTOR_RE = re.compile(
    r'(?:\s+(?:also|and|but|plus|or)|(?:此外|另外|同时|也|还|但|不过|然而|和|与|及))\s*$',
    re.IGNORECASE)
_BOUNDARY_SCOPE_INLINE_CONNECTOR_RE = re.compile(
    r"\s+(?:also|and|but|plus|or)\s+|(?:此外|另外|同时|但|不过|然而)",
    re.IGNORECASE)
_BOUNDARY_SCOPE_MIXED_POLARITY_CONNECTOR_RE = re.compile(
    _BOUNDARY_SCOPE_INLINE_CONNECTOR_RE.pattern + r"|并且|而且|以及|和|与",
    re.IGNORECASE)
_BOUNDARY_SCOPE_LEAD_NOISE_RE = re.compile(r'^[\s:：]+')
_BOUNDARY_SCOPE_LEAD_PREPOSITION_RE = re.compile(
    r'^(?:to|for)\b\s*', re.IGNORECASE)
_BOUNDARY_SCOPE_TAIL_PARTICLE_RE = re.compile(
    r'(?:则|就|then|otherwise)\s*$', re.IGNORECASE)
_BOUNDARY_SCOPE_SPLIT_RE = re.compile(r'[、;；]')
_BOUNDARY_SCOPE_UNIT_SPLIT_RE = re.compile(r'([，,;；])')
_BOUNDARY_SCOPE_ACTION_WORDS = frozenset(SKILL_ACTION_VERBS).union(
    word for words in _RESPONSIBILITY_CLUSTERS.values() for word in words)
_BOUNDARY_SCOPE_ACTION_WORD_RE = "|".join(
    re.escape(word) + (r"(?![A-Za-z])" if word.isascii() else "")
    for word in sorted(_BOUNDARY_SCOPE_ACTION_WORDS, key=len, reverse=True))
_BOUNDARY_SCOPE_ACTION_WORD_END_RE = re.compile(
    r"(?:" + _BOUNDARY_SCOPE_ACTION_WORD_RE + r")\s*$", re.IGNORECASE)
_BOUNDARY_SCOPE_NONFINITE_START_RE = re.compile(
    r"^[A-Za-z]+(?:ing|ed)\b", re.IGNORECASE)
_BOUNDARY_SUBJECT_PATTERN = (
    r"(?:本技能|该技能|此技能|这个技能|本工具|该工具|此工具|本系统"
    r"|该系统|此系统|本产品|该产品|此产品|本模块|该模块|此模块|本组件"
    r"|该组件|此组件|(?:the\s+skill|this\s+skill|the\s+tool"
    r"|this\s+tool|the\s+system|this\s+system|the\s+product"
    r"|this\s+product|it)(?![A-Za-z0-9_]))"
)
_BOUNDARY_SCOPE_SUBJECT_PREFIX_RE = re.compile(
    r"^(?:" + _BOUNDARY_SUBJECT_PATTERN + r"\s*)",
    re.IGNORECASE)
_BOUNDARY_SCOPE_POSITIVE_START_RE = re.compile(
    r'(?:(?:please|then)\s+|请|然后|仅|只|主要)*'
    r'(?:' + _EXT_CN_VERB_ALT + r'|创建|新建|生成|分析|输出|导出|修复|修理|可以|能够'
    r'|supports?|handles?|reads?|edits?|creates?|generates?|analy[sz]es?|exports?'
    r'|fix(?:es|ed|ing)?|repair(?:s|ed|ing)?|'
    + _BOUNDARY_SCOPE_ACTION_WORD_RE + r')',
    re.IGNORECASE)
_BOUNDARY_SCOPE_POSITIVE_AFFIRMATIVE_RE = re.compile(
    r'\b(?:is|are|was|were)\s+(?:supported|covered|handled|processed|included|available|allowed)\b'
    r'|(?<![不未再])(?:受|被)支持\s*$',
    re.IGNORECASE)
def _is_positive_business_fragment(text: str) -> bool:
    probe = _BOUNDARY_SCOPE_SUBJECT_PREFIX_RE.sub("", text, count=1)
    return bool(_BOUNDARY_SCOPE_POSITIVE_START_RE.match(probe)
                or _BOUNDARY_SCOPE_POSITIVE_AFFIRMATIVE_RE.search(probe))
def _negated_term_parts(text: str) -> list[str]:
    parts: list[str] = []
    for index, raw_part in enumerate(re.split(r"[;；,，]", text)):
        part = raw_part.strip()
        if not part:
            continue
        if index and _is_positive_business_fragment(part):
            break
        parts.append(part)
    return parts
_BOUNDARY_CONDITIONAL_SUBJECT_RE = re.compile(
    r'(?:(?:则|就|then|otherwise)\s*)?'
    + _BOUNDARY_SUBJECT_PATTERN + r'\s*$',
    re.IGNORECASE)
_SENTENCE_TERMINATORS_RE = re.compile(r'[。！？!?\n]')
_BOUNDARY_COORDINATED_CLAUSE_RE = re.compile(
    r"并且|而且|同时|\s+(?:and|or)\s+", re.IGNORECASE)
def _split_coordinated_positive_clauses(text: str) -> list[str]:
    clauses: list[str] = []
    cursor = 0
    for match in _BOUNDARY_COORDINATED_CLAUSE_RE.finditer(text):
        prefix = text[cursor:match.start()]
        if not _BOUNDARY_NEG_HEAD_RE.search(prefix):
            continue
        tail = text[match.end():]
        if not _is_positive_business_fragment(tail):
            continue
        if match.group(0).isascii():
            if (not _BOUNDARY_SCOPE_SUBJECT_PREFIX_RE.match(tail)
                    and (_BOUNDARY_SCOPE_ACTION_WORD_END_RE.search(prefix)
                         or _BOUNDARY_SCOPE_NONFINITE_START_RE.match(tail))):
                continue
        elif (not _BOUNDARY_SCOPE_SUBJECT_PREFIX_RE.match(tail)
                and _BOUNDARY_NEG_HEAD_RE.search(tail)):
            continue
        clauses.append(text[cursor:match.start()])
        cursor = match.end()
    if not cursor:
        return [text]
    clauses.append(text[cursor:])
    return clauses
def _split_sentence_clauses(text: str) -> list[str]:
    clauses: list[str] = []
    for chunk in _SENTENCE_TERMINATORS_RE.split(text):
        pending = chunk
        while pending:
            pos = find_first_sentence_period(pending)
            if pos < 0:
                clauses.extend(_split_coordinated_positive_clauses(pending))
                break
            clauses.extend(_split_coordinated_positive_clauses(pending[:pos]))
            pending = pending[pos + 1:]
    return clauses
def _boundary_scope_units(clause: str) -> list[str]:
    clause = clause.strip()
    if (_BOUNDARY_SCOPE_PREFIX_RE.match(clause)
            and _BOUNDARY_NEG_HEAD_RE.search(clause)):
        return [clause]
    pieces = _BOUNDARY_SCOPE_UNIT_SPLIT_RE.split(clause)
    units: list[str] = []
    pending_sep = ""
    for index, piece in enumerate(pieces):
        if index % 2:
            pending_sep = piece
            continue
        raw_piece = piece
        piece = piece.strip()
        if not piece:
            pending_sep = ""
            continue
        if units and not (
            _BOUNDARY_NEG_HEAD_RE.search(piece)
            or _BOUNDARY_SCOPE_CONNECTOR_RE.match(piece)
            or _is_positive_business_fragment(piece)
        ):
            units[-1] = f"{units[-1]}{pending_sep}{raw_piece}"
        else:
            units.append(piece)
        pending_sep = ""
    return units
def _split_positive_passive_fragment(fragment: str) -> tuple[str, str]:
    connectors = list(
        _BOUNDARY_SCOPE_MIXED_POLARITY_CONNECTOR_RE.finditer(fragment))
    for connector in reversed(connectors):
        positive = fragment[:connector.start()].strip()
        scope = fragment[connector.end():].strip()
        if not connector.group(0).isascii():
            positive_probe = _BOUNDARY_SCOPE_SUBJECT_PREFIX_RE.sub(
                "", positive, count=1).strip().casefold()
            if (any(positive_probe == word.casefold()
                    for word in _BOUNDARY_SCOPE_ACTION_WORDS)
                    or _is_positive_business_fragment(scope)):
                continue
        if ((positive.isascii() and len(positive.split()) < 2) or not scope
                or not _is_positive_business_fragment(positive)):
            continue
        return positive, scope
    return "", fragment
def _head_is_prefix_scoped(
        unit: str, head: re.Match[str], end: int) -> bool:
    if _BOUNDARY_PREFIX_SCOPED_NEG_HEAD_RE.fullmatch(head.group(0)):
        return True
    return (not head.group(0).isascii()
            and not unit[head.end():end].strip(" \t,，、;；:："))
def _negated_scope_fragments(unit: str) -> list[str]:
    heads = list(_BOUNDARY_NEG_HEAD_RE.finditer(unit))
    head_ends = [head.start() for head in heads[1:]] + [len(unit)]
    prefix_scoped_flags = [
        _head_is_prefix_scoped(unit, head, end)
        for head, end in zip(heads, head_ends, strict=True)
    ]
    fragments: list[str] = []
    for index, head in enumerate(heads):
        previous = heads[index - 1] if index else None
        following = heads[index + 1] if index + 1 < len(heads) else None
        prefix_scoped = prefix_scoped_flags[index]
        previous_is_active = bool(
            previous is not None and not prefix_scoped_flags[index - 1])
        following_is_passive = bool(
            following is not None and prefix_scoped_flags[index + 1])
        if prefix_scoped:
            start = previous.end() if previous is not None else 0
            fragment = unit[start:head.start()]
            if previous_is_active:
                connectors = list(
                    _BOUNDARY_SCOPE_INLINE_CONNECTOR_RE.finditer(fragment))
                if connectors:
                    fragment = fragment[connectors[-1].end():]
            elif previous is None:
                _positive, fragment = _split_positive_passive_fragment(fragment)
            fragment = _BOUNDARY_CONDITIONAL_SUBJECT_RE.sub(
                '', fragment).strip()
            if not fragment:
                end = following.start() if following is not None else len(unit)
                fragment = unit[head.end():end]
        else:
            end = following.start() if following is not None else len(unit)
            fragment = unit[head.end():end]
            if following_is_passive:
                connectors = list(
                    _BOUNDARY_SCOPE_INLINE_CONNECTOR_RE.finditer(fragment))
                if connectors:
                    fragment = fragment[:connectors[-1].start()]
        fragments.append(fragment)
    return fragments
def extract_boundary_scopes(description: str) -> list[str]:
    scopes: list[str] = []
    for sentence in _split_sentence_clauses(normalize_text(description)):
        for clause in _RESPONSIBILITY_CONTRAST_RE.split(sentence):
            for unit in _boundary_scope_units(clause):
                unit = _BOUNDARY_SCOPE_CONNECTOR_RE.sub('', unit).strip()
                if not unit or not _BOUNDARY_NEG_HEAD_RE.search(unit):
                    continue
                prefix = _BOUNDARY_SCOPE_PREFIX_RE.match(unit)
                if prefix is not None:
                    conditional_fragment = _BOUNDARY_NEG_HEAD_RE.split(
                        unit[prefix.end():], maxsplit=1)[0]
                    fragments = [_BOUNDARY_CONDITIONAL_SUBJECT_RE.sub(
                        '', conditional_fragment)]
                else:
                    fragments = _negated_scope_fragments(unit)
                for fragment in fragments:
                    fragment = _BOUNDARY_SCOPE_LEAD_NOISE_RE.sub('', fragment).strip()
                    fragment = _BOUNDARY_SCOPE_LEAD_PREPOSITION_RE.sub('', fragment).strip()
                    fragment = _BOUNDARY_SCOPE_CONNECTOR_RE.sub('', fragment).strip()
                    fragment = _BOUNDARY_SCOPE_TRAILING_CONNECTOR_RE.sub('', fragment).strip()
                    for part in _BOUNDARY_SCOPE_SPLIT_RE.split(fragment):
                        part = _BOUNDARY_SCOPE_TAIL_PARTICLE_RE.sub('', part.strip())
                        part = part.strip(SLOT_NOISE_CHARS)
                        if part and len(part) <= _BOUNDARY_SCOPE_MAX_CHARS:
                            scopes.append(part)
    return list(dict.fromkeys(scopes))
_RESPONSIBILITY_CONTRAST_RE = re.compile(
    r"\bbut\b|\bhowever\b|但|不过|然而", re.IGNORECASE)
def _positive_responsibility_text(description: str) -> str:
    positive: list[str] = []
    for sentence in _split_sentence_clauses(normalize_text(description)):
        for clause in _RESPONSIBILITY_CONTRAST_RE.split(sentence):
            for raw_unit in _boundary_scope_units(clause):
                unit = _BOUNDARY_SCOPE_CONNECTOR_RE.sub('', raw_unit).strip()
                if not unit:
                    continue
                head = _BOUNDARY_NEG_HEAD_RE.search(unit)
                if head is None:
                    positive.append(unit)
                    continue
                if _BOUNDARY_SCOPE_PREFIX_RE.match(unit):
                    continue
                if _head_is_prefix_scoped(unit, head, len(unit)):
                    prefix, _scope = _split_positive_passive_fragment(
                        unit[:head.start()])
                    if prefix:
                        positive.append(prefix)
                    continue
                prefix = unit[:head.start()].strip()
                prefix = _BOUNDARY_CONDITIONAL_SUBJECT_RE.sub('', prefix).strip()
                prefix = _BOUNDARY_SCOPE_TRAILING_CONNECTOR_RE.sub('', prefix).strip()
                if prefix:
                    positive.append(prefix)
    return " ".join(positive)
def _needs_phrase_separator(left: str, right: str) -> bool:
    if not left or not right:
        return False
    return ((left[-1].isascii() and left[-1].isalnum())
            or (right[0].isascii() and right[0].isalnum()))
def _action_in_readable(action: str, readable: str) -> bool:
    probe = action.casefold()
    if not probe:
        return True
    target = readable.casefold()
    if has_cjk(probe):
        return probe in target
    return keyword_matches(probe, target)
def _action_phrase(action: str, readable: str) -> str:
    if not readable:
        return action
    if _action_in_readable(action, readable):
        return readable
    separator = " " if _needs_phrase_separator(action, readable) else ""
    return f"{action}{separator}{readable}"
_DEFAULT_EXAMPLE_LANGUAGE = "zh"
def _example_template(
        index: int, language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> str:
    templates = (_POSITIVE_EXAMPLE_TEMPLATES.get(language)
                 or _POSITIVE_EXAMPLE_TEMPLATES["en"])
    return templates[index % len(templates)]
def _select_positive_actions(
        keywords: list[str], num_positive: int,
        language: str = _DEFAULT_EXAMPLE_LANGUAGE) -> list[str]:
    unique: list[str] = []
    seen: set[str] = set()
    for keyword in keywords:
        key = keyword.casefold()
        if key not in seen:
            seen.add(key)
            unique.append(keyword)
    quota = min(num_positive, len(unique))
    if language == "en":
        verbs = [kw for kw in unique if kw.casefold() in SKILL_ACTION_VERBS]
        rest = [kw for kw in unique if kw not in set(verbs)]
        return (verbs + rest)[:quota]
    picked = [kw for kw in unique if len(kw) <= 4][:quota]
    used = set(picked)
    for kw in unique:
        if len(picked) >= quota:
            break
        if kw not in used:
            picked.append(kw)
            used.add(kw)
    return picked
def generate_trigger_examples(skill_name: str, description: str, keywords: list[str],
                              num_positive: int = DEFAULT_NUM_POSITIVE,
                              num_negative: int = DEFAULT_NUM_NEGATIVE) -> list[dict[str, str]]:
    examples: list[dict[str, str]] = []
    keywords = normalize_keywords(keywords)
    num_positive = normalize_nonnegative_count(
        num_positive, DEFAULT_NUM_POSITIVE, "generate_trigger_examples")
    num_negative = normalize_nonnegative_count(
        num_negative, DEFAULT_NUM_NEGATIVE, "generate_trigger_examples")
    skill_name = normalize_text(skill_name)
    description = normalize_text(description)
    language = detect_text_language(description, skill_name,
                                    " ".join(keywords))
    readable = readable_skill_name(skill_name)
    action_words = _select_positive_actions(
        keywords, num_positive, language)
    for i, action in enumerate(action_words):
        template = _example_template(i, language)
        phrase = _action_phrase(action, readable)
        reason = (f"包含触发关键词 '{action}'" if language == "zh"
                  else f"contains trigger keyword '{action}'")
        examples.append({'query': template.format(phrase=phrase),
                         'should_trigger': 'true', 'reason': reason})
    seen_negative_queries: set[str] = set()
    for scope in extract_boundary_scopes(description):
        if len(seen_negative_queries) >= num_negative:
            break
        query = negative_query_for_boundary(scope, language=language)
        if query in seen_negative_queries:
            continue
        seen_negative_queries.add(query)
        examples.append({
            'query': query,
            'should_trigger': 'false',
            'reason': (f"命中显式排除范围: {scope}" if language == "zh"
                       else f"matches explicit exclusion: {scope}"),
        })
    generic_negatives = (_NEGATIVE_EXAMPLE_QUERIES.get(language)
                         or _NEGATIVE_EXAMPLE_QUERIES["en"])
    for negative_query in generic_negatives:
        if len(seen_negative_queries) >= num_negative:
            break
        if any(keyword_matches(kw, negative_query.lower())
               for kw in keywords):
            continue
        if negative_query in seen_negative_queries:
            continue
        seen_negative_queries.add(negative_query)
        reason = (f"与 {skill_name or '本技能'} 无关的通用请求"
                  if language == "zh"
                  else f"general request unrelated to {skill_name or 'this skill'}")
        examples.append({'query': negative_query,
                         'should_trigger': 'false', 'reason': reason})
    return examples
_GENERIC_USAGE_RE = re.compile(
    r'快速入门|快速开始|快速上手|使用方法|使用说明|命令速查|调用方式|'
    r'工作流|workflow|usage|quick\s*start|getting\s*started|'
    r'示例|examples?', re.IGNORECASE)

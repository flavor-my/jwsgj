from __future__ import annotations

import re
from collections.abc import Iterator, Mapping
from dataclasses import dataclass, field
from functools import cache
from itertools import chain
from typing import Any

from jwsgj.build_text_document import (
    SLOT_NOISE_CHARS,
    normalize_text,
)
from jwsgj.build_text_scoring import (
    CN_EXCLUSION_HEADS,
    DOMAIN_NEGATIVES,
    NEGATIVE_COMMANDS,
    RE_CHINESE_CHARS,
    ROLE_PERSPECTIVES,
    SPOKEN_PATTERNS,
    TRIGGER_COMMANDS,
    anchor_entries,
    anchor_section_cut,
    derive_skill_anchors,
    keyword_matches,
    normalize_bool_flag,
    normalize_keywords,
    normalize_nonnegative_count,
    stem_matches,
)
from jwsgj.diag_types_vocab import FIELD_TRIGGER_EXAMPLES

__all__ = [
    'ValidationReport',
    'append_unique_keyword',
    'build_keyword_matrix',
    'build_trigger_example_pool',
    'compose_golden_description',
    'expand_keyword_matrix',
    'expand_long_tail',
    'expand_spoken_and_cn',
    'extract_base_keywords',
    'extract_core_action',
    'extract_noun',
    'generate_business_coverage',
    'generate_negative_rules',
    'generate_role_perspective',
    'generate_skill_anchors',
    'merge_and_pad_keywords',
    'strip_injected_sections',
    'validate_description_generation',
]
_DEFAULT_SKILL_TYPE = "generic"
_ROLE_PERSPECTIVE_TEXTS = {
    role: f"{role_info['prefix']} {' / '.join(role_info['patterns'][:3])}"
    for role, role_info in ROLE_PERSPECTIVES.items()
}
def _is_meaningful_token(text: str) -> bool:
    return len(text) > 1 or (text.isascii() and text.isalnum())
_SCENARIO_INDICATORS: tuple[str, ...] = (
    "when the user", "当用户", "when user", "适用于",
    "use when", "trigger", "触发", "调用",
)
_LABEL_SPOKEN = "口语化表达"
_LABEL_CAPABILITY = "业务能力"
_LABEL_EXAMPLES = "触发示例"
INJECTED_SECTION_LABELS: tuple[str, ...] = (
    _LABEL_SPOKEN,
    _LABEL_CAPABILITY,
    _LABEL_EXAMPLES,
)
_SECTION_MARKER_PREFIX = r"(?:^|(?<=[\s。；;，,、：:]))"
@cache
def _section_marker_pattern(label: str) -> re.Pattern[str]:
    return re.compile(_SECTION_MARKER_PREFIX + re.escape(label) + r"\s*[:：]")
_INJECTED_SECTION_PATTERNS: tuple[re.Pattern[str], ...] = tuple(
    _section_marker_pattern(label) for label in INJECTED_SECTION_LABELS
)
_LEADING_TRIGGER_MARK = re.compile(
    r'(?:\s*\[[ \t]*)?(?<![A-Za-z])(?P<trigger>'
    + '|'.join(re.escape(_c) for _c in TRIGGER_COMMANDS)
    + r')(?![A-Za-z])(?:[ \t]*\])?(?:[ \t]*[:：.。,，;；]+)?\s*',
    re.IGNORECASE)
def _normalize_slot_text(text: str) -> str:
    text = text.strip().lstrip(SLOT_NOISE_CHARS)
    _hit = _LEADING_TRIGGER_MARK.match(text)
    while text and _hit:
        text = text[_hit.end():].lstrip(SLOT_NOISE_CHARS)
        _hit = _LEADING_TRIGGER_MARK.match(text)
    return text.rstrip(SLOT_NOISE_CHARS)
def _normalize_inputs(name: str, desc: str,
                      skill_type: str) -> tuple[str, str, str]:
    return (normalize_text(name), normalize_text(desc),
            normalize_text(skill_type).strip().lower() or _DEFAULT_SKILL_TYPE)
def _match_haystack(name: str, desc: str, skill_type: str,
                    limit: int | None = None) -> str:
    body = _positive_business_text(strip_injected_sections(desc))
    body = body[:limit] if limit is not None else body
    return (name + " " + body + " " + skill_type).lower()
def strip_injected_sections(text: str) -> str:
    text = normalize_text(text)
    if not text:
        return text
    cut = len(text)
    for pattern in _INJECTED_SECTION_PATTERNS:
        match = pattern.search(text)
        if match is not None and match.start() < cut:
            cut = match.start()
    anchor_cut = anchor_section_cut(text)
    if 0 <= anchor_cut < cut:
        cut = anchor_cut
    for role_text in _ROLE_PERSPECTIVE_TEXTS.values():
        role_cut = text.find(role_text)
        if 0 <= role_cut < cut:
            cut = role_cut
    return text[:cut]
def generate_role_perspective(name: str, desc: str,
                              skill_type: str) -> dict:
    name, desc, skill_type = _normalize_inputs(name, desc, skill_type)
    desc_lower = _match_haystack(name, desc, skill_type)
    matched_roles = []
    role_texts = []
    for role, rp in ROLE_PERSPECTIVES.items():
        if any(stem_matches(kw, desc_lower) for kw in rp["patterns"]):
            matched_roles.append(role)
            role_texts.append(_ROLE_PERSPECTIVE_TEXTS[role])
    return {
        "matched_roles": matched_roles,
        "role_text": " | ".join(role_texts),
        "role_keywords": [list(ROLE_PERSPECTIVES[r]["patterns"])
                          for r in matched_roles],
    }
_BUSINESS_DOMAIN_KEYWORDS: dict[str, list[str]] = {
    "code_diag": ["diagnos", "antipattern", "反模式", "dead code", "死代码", "代码质量诊断", "缺陷检测", "代码质量", "code quality"],
    "security": ["security audit", "安全审计", "vulnerability scan", "漏洞扫描", "secret leak", "密钥泄露", "path traversal", "路径穿越", "安全审查", "security review", "安全漏洞"],
    "testing": ["test coverage", "测试覆盖", "regression test", "回归测试", "mutation test", "变异测试", "执行测试", "run test"],
    "fix_repair": ["auto fix", "自动修复", "修复缺陷", "修复方案", "bug fix", "缺陷修复", "修复代码"],
    "skill_mgmt": ["skill creation", "技能创建", "skill audit", "技能审计", "doc refactor", "文档重构", "trigger optimize", "触发词优化", "discoverability enhance", "可发现性增强", "preflight check", "预检", "技能文档", "构建管理技能"],
    "cross_verify": ["cross validation", "交叉验证", "multi-source", "多源仲裁", "baseline compare", "基线对比", "conflict resolution", "冲突解决"],
}
# 转折词引导的否定（but not / 但不是 / 而不是 / 而非）必须在同一子句内
# 交给 _NEGATIVE_SCOPE_AFTER_PREDICATES 解析，否则 "but" 会把否定短语拆成
# 独立片段而被当成正向能力。
_NEGATION_TRANSITION_GUARD = r"(?!(?:\s*是)?\s*(?:不|非|没|未))"
_CLAUSE_SPLIT_RE = re.compile(
    r"[。；;！!？?，,、\n]+|(?<!\d)\.(?!\d)|"
    r"\b(?:but|however)\b"
    r"(?!\s*(?:not|never|cannot|can't|no longer|without|"
    r"is\s+not|are\s+not|was\s+not|were\s+not))|"
    r"但是" + _NEGATION_TRANSITION_GUARD + r"|"
    r"但" + _NEGATION_TRANSITION_GUARD + r"|"
    r"不过" + _NEGATION_TRANSITION_GUARD + r"|"
    r"然而" + _NEGATION_TRANSITION_GUARD,
    re.IGNORECASE)
def generate_business_coverage(name: str, desc: str,
                               skill_type: str) -> dict:
    name, desc, skill_type = _normalize_inputs(name, desc, skill_type)
    desc_lower = _match_haystack(name, desc, skill_type, limit=200)
    matched_caps = []
    for domain, keywords in _BUSINESS_DOMAIN_KEYWORDS.items():
        if any(stem_matches(kw, desc_lower) for kw in keywords):
            matched_caps.append(domain)
    business_core = strip_injected_sections(desc)
    capabilities = list(dict.fromkeys(
        clause for clause in _positive_business_clauses(business_core)
        if len(clause) >= 2
    ))
    return {
        "matched_domains": matched_caps,
        "capabilities": capabilities,
        "coverage_text": "，".join(capabilities),
    }
def _resolve_anchor_catalog(desc: str,
                           anchors: Mapping[str, Any] | None) -> Mapping[str, Any]:
    return derive_skill_anchors(desc) if anchors is None else anchors
def generate_skill_anchors(name: str, desc: str,
                           skill_type: str,
                           anchors: Mapping[str, Any] | None = None) -> dict:
    name, desc, skill_type = _normalize_inputs(name, desc, skill_type)
    desc_lower = _match_haystack(name, desc, skill_type)
    matched_anchors = []
    all_tags = []
    anchor_texts = []
    source_sections = [section.strip() for section in re.split(
        r"(?<=[。；;\n])", _positive_business_text(desc)) if section.strip()]
    catalog = _resolve_anchor_catalog(desc, anchors)
    for anchor in anchor_entries(catalog):
        anchor_name = anchor["name"].lower()
        if not keyword_matches(anchor_name, desc_lower):
            continue
        matched_anchors.append(anchor)
        all_tags.extend(
            tag for tag in anchor["tags"]
            if keyword_matches(tag.lower(), desc_lower))
        anchor_texts.extend(
            section for section in source_sections
            if keyword_matches(anchor_name, section.lower()))
    anchor_texts = list(dict.fromkeys(anchor_texts))
    return {
        "matched_anchors": matched_anchors,
        "tags": sorted(set(all_tags)),
        "anchor_texts": anchor_texts,
        "anchor_summary": "；".join(anchor_texts),
    }
_SHORT_DESC_TEMPLATE_RE = re.compile(
    r'^(?:\s*\[[^\]]+\]|\s*(?:MUST USE|MUST BE INVOKED|ALWAYS LOAD|'
    r'CRITICAL TRIGGER|PRIORITY LOAD))?\s*'
    r'(?P<sentence>when the user needs to [^.。]+\.)\s*', re.IGNORECASE)
def _is_generated_fallback_sentence(sentence: str, name: str) -> bool:
    readable_name = name.replace("-", " ").replace("_", " ").strip()
    objects = (readable_name,) if readable_name else ("the requested task",)
    default_verb = "work with" if readable_name else "perform"
    head = "when the user needs to "
    lowered = sentence.strip().rstrip(".").lower()
    if not lowered.startswith(head):
        return False
    return any(
        lowered == head + f"{verb} {obj}".lower()
        for verb in (default_verb, *_ACTION_PRIORITY)
        for obj in objects)
def _strip_generated_fallback_prefix(text: str, name: str = "") -> str:
    match = _SHORT_DESC_TEMPLATE_RE.match(text)
    if match is None or not _is_generated_fallback_sentence(
            match.group("sentence"), name):
        return text
    return text[match.end():]
def _build_short_desc_fallback(name: str, desc: str,
                               action: str | None) -> str:
    readable_name = name.replace("-", " ").replace("_", " ").strip()
    if readable_name:
        generated_base = (
            f"when the user needs to {action or 'work with'} {readable_name}."
        )
    else:
        generated_base = (
            f"when the user needs to {action or 'perform'} the requested task."
        )
    short_desc = _normalize_slot_text(desc).strip() if desc else ""
    if short_desc:
        return f"{generated_base} {short_desc}"
    return generated_base
_CN_VERB_TO_EN: dict[str, str] = {
    "创建": "create", "生成": "generate", "构建": "build",
    "诊断": "diag", "检查": "check", "审查": "check", "检测": "check",
    "优化": "optimize", "改进": "optimize",
    "分析": "analyze",
    "修复": "fix", "修理": "fix",
    "转换": "convert", "转化": "convert",
    "提取": "extract",
    "合并": "merge",
    "拆分": "split", "分割": "split",
}
# 英文动作词只认原形及其屈折形态（含 e 音省与 y→i），不把 checkout / fixture /
# user 这类同前缀异义词当成动作信号；中文动作词按子串匹配。
# -er/-or 施事者形态（editor / worker）仅用于技能名动作提取，判断否定前缀是否为
# 正向职责时必须排除，否则 "The editor does not handle..." 的主语会被当成动作。
_EN_ACTION_SUFFIXES_AFTER_STEM: tuple[str, ...] = (
    "ing", "ion", "ions", "ation", "ations",
)
_EN_ACTION_SUFFIXES_AFTER_WORD: tuple[str, ...] = (
    "s", "es", "ed", "d", "er", "ers", "or", "ors",
    "ment", "ments",
)
_AGENT_NOUN_SUFFIXES: frozenset[str] = frozenset({"er", "ers", "or", "ors"})
@cache
def _action_word_pattern(word: str,
                          *, allow_derived: bool = True) -> re.Pattern[str]:
    stem = word.removesuffix("e")
    forms = {word}
    forms.update(
        word + suffix for suffix in _EN_ACTION_SUFFIXES_AFTER_WORD
        if allow_derived or suffix not in _AGENT_NOUN_SUFFIXES)
    forms.update(stem + suffix for suffix in _EN_ACTION_SUFFIXES_AFTER_STEM)
    if word.endswith("y"):
        forms.update((word[:-1] + "ied", word[:-1] + "ies"))
    alt = "|".join(re.escape(form) for form in sorted(forms, key=len, reverse=True))
    return re.compile(
        r"(?<![A-Za-z0-9_])(?:" + alt + r")(?![A-Za-z0-9_])", re.IGNORECASE)
def _action_word_matches(word: str, text_lower: str,
                         *, allow_derived: bool = True) -> bool:
    if not word.isascii():
        return word in text_lower
    return _action_word_pattern(
        word, allow_derived=allow_derived).search(text_lower) is not None
def _iter_matched_spoken(text_lower: str) -> Iterator[tuple[str, list[str]]]:
    for verb, patterns in SPOKEN_PATTERNS.items():
        if _action_word_matches(verb, text_lower):
            yield verb, patterns
def _append_synonym_patterns(patterns: list[str], synonyms: list[str],
                            seen: set[str], limit: int = 3) -> None:
    for pattern in patterns[:limit]:
        append_unique_keyword(synonyms, seen, pattern)
def _collect_synonyms(matching_base: str) -> list[str]:
    synonyms: list[str] = []
    seen_syn_pool: set[str] = set()
    desc_lower = matching_base.lower()
    matched_verbs: set[str] = set()
    for verb, patterns in _iter_matched_spoken(desc_lower):
        matched_verbs.add(verb)
        _append_synonym_patterns(patterns, synonyms, seen_syn_pool)
    for cn_word, en_verb in _CN_VERB_TO_EN.items():
        if stem_matches(cn_word, desc_lower) and en_verb not in matched_verbs:
            matched_verbs.add(en_verb)
            _append_synonym_patterns(
                SPOKEN_PATTERNS.get(en_verb, []), synonyms, seen_syn_pool)
    return synonyms
def _embed_section(enriched: str, items: list[str], header: str,
                   separator: str, limit: int | None = None) -> str:
    if not items:
        return enriched
    unique: list[str] = []
    seen: set[str] = set()
    for item in items:
        text = item.strip()
        if text and text not in seen and text not in enriched:
            seen.add(text)
            unique.append(text)
    if unique and not _has_section_marker(enriched, header):
        enriched += f" {header}：{separator.join(unique[:limit])}"
    return enriched
def _has_section_marker(text: str, label: str) -> bool:
    return bool(_section_marker_pattern(label).search(normalize_text(text)))
def _embed_role_perspective(enriched: str, role_info: dict) -> str:
    role_text = normalize_text(role_info.get("role_text"))
    if not role_text:
        return enriched
    segments = [segment.strip() for segment in role_text.split(" | ")
                if segment.strip()]
    matched_roles = role_info.get("matched_roles") or []
    for index, role in enumerate(matched_roles):
        if index >= len(segments):
            break
        segment = segments[index]
        prefix = ROLE_PERSPECTIVES.get(role, {}).get("prefix", "")
        if prefix and prefix in enriched:
            continue
        if segment not in enriched:
            enriched += f" {segment}"
    return enriched
def _collect_sixdim_artifacts(name: str, matching_base: str,
                              skill_type: str, action: str,
                              anchors: Mapping[str, Any] | None = None) -> dict:
    role_info = generate_role_perspective(name, matching_base, skill_type)
    coverage_info = generate_business_coverage(name, matching_base, skill_type)
    anchor_info = generate_skill_anchors(
        name, matching_base, skill_type, anchors=anchors)
    return {
        "role_info": role_info,
        "coverage_info": coverage_info,
        "anchor_info": anchor_info,
        "examples": build_trigger_example_pool(action),
        "synonyms": _collect_synonyms(matching_base),
    }
_ANY_TRIGGER_MARK_RE = re.compile(
    r'(?<![A-Za-z])(?P<trigger>'
    + '|'.join(re.escape(_c) for _c in TRIGGER_COMMANDS)
    + r')(?![A-Za-z])', re.IGNORECASE)
def _apply_must_prefix(enriched: str, must_prefix: str) -> tuple[str, str]:
    mark = _LEADING_TRIGGER_MARK.match(enriched)
    if mark is None:
        mark = _ANY_TRIGGER_MARK_RE.search(enriched)
    if mark is None:
        return must_prefix + enriched, must_prefix.strip()
    return enriched, f"[{mark.group('trigger').upper()}]"
def _embed_trigger_examples(enriched: str, examples: list[str]) -> str:
    if not examples:
        return enriched
    example_str = " | ".join(examples[:5])
    if example_str in enriched or _has_section_marker(enriched, _LABEL_EXAMPLES):
        return enriched
    return enriched + f" {_LABEL_EXAMPLES}：{example_str}"
def _embed_anchors(enriched: str, anchor_texts: list[str],
                   tags: list[str]) -> str:
    for anchor_text in anchor_texts:
        if anchor_text and anchor_text not in enriched:
            enriched += f" {anchor_text}"
    for tag in tags:
        if tag not in enriched:
            enriched += f" {tag}"
    return enriched
def _compose_sixdim_description(clean_base: str, must_prefix: str,
                                art: dict) -> tuple[str, str]:
    role_info, coverage_info, anchor_info = (
        art["role_info"], art["coverage_info"], art["anchor_info"])
    enriched, must_trigger = _apply_must_prefix(clean_base.strip(), must_prefix)
    enriched = _embed_section(enriched, art["synonyms"], _LABEL_SPOKEN, " / ", 12)
    enriched = _embed_role_perspective(enriched, role_info)
    enriched = _embed_section(
        enriched, coverage_info["capabilities"], _LABEL_CAPABILITY, "，")
    enriched = _embed_trigger_examples(enriched, art["examples"])
    enriched = _embed_anchors(
        enriched, anchor_info["anchor_texts"], anchor_info["tags"])
    return enriched, must_trigger
def compose_golden_description(name: str, desc: str,
                                skill_type: str,
                                anchors: Mapping[str, Any] | None = None) -> dict:
    name, desc, skill_type = _normalize_inputs(name, desc, skill_type)
    result = {
        "description": desc,
        "must_trigger": "",
        FIELD_TRIGGER_EXAMPLES: [],
    }
    clean_base = desc
    business_core = _strip_generated_fallback_prefix(
        _normalize_slot_text(strip_injected_sections(desc)), name)
    matching_base = _truncate_positive_core(
        _positive_business_text(business_core), _MATCHING_BASE_LIMIT)
    action = extract_core_action(name, business_core)
    must_prefix = f"[{_trigger_command_for(action)}] "
    if not desc or len(desc.strip()) < 20:
        clean_base = _build_short_desc_fallback(name, desc, action)
    art = _collect_sixdim_artifacts(
        name, matching_base, skill_type, action, anchors=anchors)
    result[FIELD_TRIGGER_EXAMPLES] = art["examples"]
    enriched, must_trigger = _compose_sixdim_description(
        clean_base, must_prefix, art)
    result["must_trigger"] = must_trigger
    result["description"] = enriched
    result["role_info"] = art["role_info"]
    result["coverage_info"] = art["coverage_info"]
    result["anchor_info"] = art["anchor_info"]
    result["synonyms"] = art["synonyms"]
    return result
_NAME_STRUCTURAL_TOKENS: frozenset[str] = frozenset({"skill", "skills"})
_ACTION_PRIORITY: tuple[str, ...] = (
    "fix", "repair", "restore", "recover",
    "create", "build", "generate", "make",
    "edit", "modify", "update", "change",
    "analyze", "diag", "review", "check", "inspect",
    "delete", "remove", "clean",
    "convert", "export", "transform",
    "deploy", "publish", "release",
    "optimize", "improve", "enhance",
    "search", "find", "query",
)
_PRIORITY_LOAD_ACTIONS: frozenset[str] = frozenset(
    {"fix", "repair", "restore", "recover"})
_DEFAULT_TRIGGER_COMMAND = "MUST USE"
_PRIORITY_TRIGGER_COMMAND = "PRIORITY LOAD"
def _trigger_command_for(action: str | None) -> str:
    return (_PRIORITY_TRIGGER_COMMAND
            if action in _PRIORITY_LOAD_ACTIONS
            else _DEFAULT_TRIGGER_COMMAND)
_RESPONSIBILITY_ACTION_WORDS: frozenset[str] = frozenset({
    *_ACTION_PRIORITY, *_CN_VERB_TO_EN,
    "process", "manage", "handle", "execute", "support", "use", "work",
    "处理", "执行", "管理", "使用", "支持", "规划", "预订", "整理",
    "归档", "保存", "读取", "写入", "发送", "接收", "翻译", "播放",
    "绘制", "设计", "审查", "搜索", "分析", "部署", "编辑", "导出",
    "转换", "监控", "备份", "发布", "上传", "下载", "测试", "评估",
    "审核", "校验", "审计", "重构", "清理", "治疗", "复盘", "反哺",
    "进化", "扫描", "评审", "校核", "定位", "追踪", "治理", "排查",
    "收敛", "固化", "沉淀",
    # 与 build_text_scoring._CN_ACTION_WORDS 对齐的职责动词：缺失它们会让
    # 「适用于B」这类正向句在否定延续窗口内被误判为排除对象。
    "适用", "提供", "覆盖", "兼容", "负责", "涉及", "包含", "包括",
    "允许", "接受",
})
def _iter_matched_actions(text_lower: str) -> Iterator[str]:
    for action in _ACTION_PRIORITY:
        if _action_word_matches(action, text_lower) or any(
                en_action == action and stem_matches(cn_word, text_lower)
                for cn_word, en_action in _CN_VERB_TO_EN.items()):
            yield action
def extract_core_action(name: str, desc: str) -> str | None:
    combined = (normalize_text(name) + " " + _positive_business_text(
        strip_injected_sections(desc))).lower()
    return next(_iter_matched_actions(combined), None)
def extract_noun(name: str) -> str:
    clean = normalize_text(name)
    clean = clean.removeprefix("skill-").removesuffix("-skill")
    clean = clean.replace("-", " ").replace("_", " ")
    return clean.strip()
_GENERIC_TRIGGER_EXAMPLE_TEMPLATES: tuple[str, ...] = (
    "请{action}当前任务", "帮我{action}这个任务", "我想{action}当前任务",
    "能不能{action}这个任务", "使用本技能{action}当前任务",
    "调用此技能{action}当前任务", "需要{action}当前任务",
    "如何{action}当前任务", "麻烦{action}当前任务", "请立即{action}当前任务",
    "Please {action} the current task", "Help me {action} this task",
    "I need to {action} the current task", "Can you {action} this task",
    "Use this skill to {action} the current task",
    "Invoke this skill to {action} this task",
    "How do I {action} the current task",
    "Trigger this skill to {action} the task", "I want to {action} this task",
    "Please help me {action} the task", "请{action}当前任务 please",
    "Help me {action}当前任务", "能不能{action}这个任务 for me",
    "Use this skill to {action}当前任务", "Please {action}当前任务",
)
def build_trigger_example_pool(action: str | None) -> list[str]:
    effective_action = normalize_text(action) or "process"
    return list(dict.fromkeys(
        template.format(action=effective_action)
        for template in _GENERIC_TRIGGER_EXAMPLE_TEMPLATES
    ))[:25]
_GENERIC_NEGATIVE_RULE = DOMAIN_NEGATIVES["generic"][0]
_NEGATIVE_SCOPE_AFTER_PREDICATES: tuple[str, ...] = tuple(dict.fromkeys((
    *NEGATIVE_COMMANDS,
    "does not handle", "does not cover", "does not process",
    "does not support", "does not deal with", "does not touch",
    "doesn't handle", "doesn't cover", "doesn't process",
    "doesn't support", "doesn't deal with", "doesn't touch",
    "do not handle", "do not cover", "do not process",
    "do not support", "do not deal with", "do not touch",
    "don't handle", "don't cover", "don't process",
    "don't support", "don't deal with", "don't touch",
    "can not handle", "cannot handle", "is not responsible for",
    "not responsible for",
    # 转折否定：对象位于谓词之后（handles A but not B → B 是排除对象）。
    "but not", "however not", "但不是", "而不是", "而非",
    # 系动词否定转折（handles A but/however is not B → B 是排除对象）。
    "but is not", "but are not", "but was not", "but were not",
    "however is not", "however are not", "however was not",
    "however were not",
    # 英文排他词同样是后置范围标记（handles A except B → B 是排除对象）。
    "except for", "except", "excluding",
)))
_NEGATIVE_SCOPE_BEFORE_PREDICATES: tuple[str, ...] = (
    "not covered", "not handled", "not supported", "not processed",
    "not included", "not available", "not applicable", "not allowed",
    "不被支持", "不被处理", "不被覆盖", "不被包含", "不被允许",
)
# 「仅限于 X」限定的是正向职责范围（只有 X 在范围内），X 不是排除对象；
# 它与「不包含 X」方向相反，不能共用否定范围解析，否则 X 会被写成 NOT FOR。
_POSITIVE_SCOPE_RESTRICTION_HEADS: frozenset[str] = frozenset({"仅限于"})
_CN_EXCLUSION_PREDICATES: tuple[str, ...] = tuple(dict.fromkeys((
    *(head for head in CN_EXCLUSION_HEADS
      if head not in _POSITIVE_SCOPE_RESTRICTION_HEADS),
    "不负责处理", "不予处理", "不做处理", "不做",
)))
_NEGATIVE_SCOPE_PREDICATES: tuple[str, ...] = tuple(dict.fromkeys((
    *_NEGATIVE_SCOPE_AFTER_PREDICATES,
    *_NEGATIVE_SCOPE_BEFORE_PREDICATES,
    *_CN_EXCLUSION_PREDICATES,
)))
_NEGATIVE_SCOPE_LEADING_VERBS: tuple[str, ...] = (
    "使用", "用于", "用来", "进行",
)
_NEGATIVE_SCOPE_AUXILIARY_HEADS: frozenset[str] = frozenset({
    "禁止", "请勿", "不要", "不允许", "不接受",
})
def _predicate_pattern(predicate: str) -> re.Pattern[str]:
    pattern = re.escape(predicate)
    if predicate[:1].isascii() and predicate[:1].isalpha():
        pattern = r"(?<![A-Za-z])" + pattern
    if predicate[-1:].isascii() and predicate[-1:].isalpha():
        pattern += r"(?![A-Za-z])"
    return re.compile(pattern, re.IGNORECASE)
_CN_ACTION_NEGATION_PREFIXES: tuple[str, ...] = (
    "不允许", "不接受", "不负责", "不予", "不做", "请勿", "禁止", "不要",
    "不能", "不可", "无需", "无须", "不", "勿",
)
_CN_ACTION_NEGATION_VERBS = "|".join(re.escape(word) for word in sorted(
    (word for word in _RESPONSIBILITY_ACTION_WORDS if not word.isascii()),
    key=len, reverse=True))
_CN_ACTION_NEGATION_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = tuple(
    (prefix, re.compile(
        re.escape(prefix) + rf"(?=(?:{_CN_ACTION_NEGATION_VERBS}))",
        re.IGNORECASE))
    for prefix in _CN_ACTION_NEGATION_PREFIXES)
_EN_ACTION_NEGATION_PREFIXES: tuple[str, ...] = (
    "do not", "don't", "does not", "doesn't", "did not", "didn't",
    "can not", "cannot", "can't", "could not", "couldn't",
    "must not", "mustn't", "should not", "shouldn't",
    "will not", "won't", "never",
)
_EN_ACTION_NEGATION_VERBS = "|".join(re.escape(word) for word in sorted(
    (word for word in _RESPONSIBILITY_ACTION_WORDS if word.isascii()),
    key=len, reverse=True))
_EN_ACTION_NEGATION_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = tuple(
    (prefix, re.compile(
        rf"(?<![A-Za-z]){re.escape(prefix)}"
        rf"(?=\s+(?:{_EN_ACTION_NEGATION_VERBS})(?![A-Za-z]))",
        re.IGNORECASE))
    for prefix in _EN_ACTION_NEGATION_PREFIXES)
_NEGATIVE_SCOPE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    *tuple((predicate, _predicate_pattern(predicate))
           for predicate in _NEGATIVE_SCOPE_PREDICATES),
    *_EN_ACTION_NEGATION_PATTERNS,
    *_CN_ACTION_NEGATION_PATTERNS,
)
_NEGATIVE_SCOPE_SUBJECTS: tuple[str, ...] = (
    "本技能", "该技能", "此技能", "这个技能", "本工具", "该工具", "此工具",
    "本系统", "该系统", "此系统", "本产品", "该产品", "此产品",
    "本模块", "该模块", "此模块", "本组件", "该组件", "此组件",
    "the skill", "this skill", "the tool", "this tool",
    "the system", "this system", "the product", "this product", "it",
)
_CN_POSITIVE_CLAUSE_HEAD = (
    r"(?:(?:"
    + "|".join(re.escape(subject) for subject in _NEGATIVE_SCOPE_SUBJECTS
               if not subject.isascii())
    + r"|请|然后))*(?:"
    + "|".join(re.escape(word) for word in sorted(
        (word for word in _RESPONSIBILITY_ACTION_WORDS if not word.isascii()),
        key=len, reverse=True))
    + r")"
)
_COORDINATED_CLAUSE_SPLIT_RE = re.compile(
    r"(?:并且|而且|同时|然后|(?<!合)并)(?=" + _CN_POSITIVE_CLAUSE_HEAD + r")"
    r"|\s+(?:and|or)\s+(?=(?:"
    + "|".join(re.escape(subject) for subject in _NEGATIVE_SCOPE_SUBJECTS
               if subject.isascii())
    + r")\b)",
    re.IGNORECASE)
_CLAUSE_SEGMENT_SPLIT_RE = re.compile(
    rf"(?:{_CLAUSE_SPLIT_RE.pattern})|(?:{_COORDINATED_CLAUSE_SPLIT_RE.pattern})",
    re.IGNORECASE)
_NEGATIVE_SCOPE_TRAILING_CN: tuple[str, ...] = (
    "以及", "同时", "然后", "并且", "而且", "也",
)
_NEGATIVE_SCOPE_TRAILING_EN_RE = re.compile(
    r"(?:^|\s+)(?:and|or|are|is|was|were|be|been)$", re.IGNORECASE)
_NEGATIVE_SCOPE_LEADING_PREPOSITION_RE = re.compile(
    r"^\s*(?:to|for)\b\s*", re.IGNORECASE)
_NEGATIVE_SCOPE_TRAILING_NOUNS: tuple[str, ...] = (
    "相关任务", "的任务", "任务",
)
_NEGATIVE_SCOPE_NOISE = frozenset({
    *_NEGATIVE_SCOPE_SUBJECTS, "任务", "相关任务", "的技能",
})
_NEGATIVE_CONTINUATION_LEADING_RE = re.compile(
    r"^(?:\s*(?:and|or|also)\s+|\s*(?:以及|同时|并且|而且|也|并))+",
    re.IGNORECASE)
def _strip_leading_scope_verb(scope: str, enabled: bool) -> str:
    if not enabled:
        return scope
    for verb in _NEGATIVE_SCOPE_LEADING_VERBS:
        if not scope.startswith(verb) or len(scope) == len(verb):
            continue
        remainder = scope[len(verb):].lstrip(" \t\r\n")
        if remainder:
            return remainder
    return scope
def _clean_negative_scope(text: str, *,
                          strip_leading_verb: bool = False) -> str:
    scope = _NEGATIVE_CONTINUATION_LEADING_RE.sub("", text).strip(
        " \t\r\n,，、;；:：。.")
    while scope:
        previous = scope
        scope = _strip_leading_scope_verb(scope, strip_leading_verb)
        lowered = scope.lower()
        for subject in _NEGATIVE_SCOPE_SUBJECTS:
            if not lowered.startswith(subject):
                continue
            remainder = scope[len(subject):]
            if subject.isascii() and remainder[:1].isalnum():
                continue
            scope = remainder.lstrip(" \t\r\n,，、;；:：")
            break
        for suffix in _NEGATIVE_SCOPE_TRAILING_CN:
            if len(scope) > len(suffix) and scope.endswith(suffix):
                scope = scope[:-len(suffix)].rstrip(" \t\r\n,，、;；:：")
                break
        scope = _NEGATIVE_SCOPE_TRAILING_EN_RE.sub("", scope).rstrip(
            " \t\r\n,，、;；:：")
        for suffix in _NEGATIVE_SCOPE_TRAILING_NOUNS:
            if len(scope) > len(suffix) and scope.endswith(suffix):
                scope = scope[:-len(suffix)].rstrip(" \t\r\n,，、;；:：的")
                break
        if scope == previous:
            break
    scope = _strip_leading_scope_verb(
        scope.strip(" \t\r\n,，、;；:：.。"), strip_leading_verb)
    if not _is_meaningful_token(scope) or scope.casefold() in _NEGATIVE_SCOPE_NOISE:
        return ""
    return scope
def _iter_predicate_matches(clause: str) -> list[tuple[int, int, str]]:
    lowered = clause.lower()
    matches: list[tuple[int, int, str]] = []
    for predicate, pattern in _NEGATIVE_SCOPE_PATTERNS:
        for match in pattern.finditer(lowered):
            matches.append((match.start(), match.end(), predicate))
    matches.sort(key=lambda item: (item[0], -(item[1] - item[0])))
    filtered: list[tuple[int, int, str]] = []
    for start, end, predicate in matches:
        if any(start >= kept_start and end <= kept_end
               for kept_start, kept_end, _ in filtered):
            continue
        filtered.append((start, end, predicate))
    return filtered
_NEGATIVE_CONTINUATION_CHARS = frozenset(";；,，、")
_POSITIVE_PREFIX_TRAILING_RE = re.compile(
    r"(?:\s+(?:and|or|also|then)|同时|并且|而且|以及|也|并|和|与|"
    r"但(?:是)?|不过|然而)$",
    re.IGNORECASE)
def _iter_clause_segments(text: str) -> Iterator[tuple[str, str]]:
    cursor = 0
    for match in _CLAUSE_SEGMENT_SPLIT_RE.finditer(text):
        yield text[cursor:match.start()], match.group(0)
        cursor = match.end()
    yield text[cursor:], ""
def _is_negative_continuation_separator(separator: str) -> bool:
    return (bool(separator)
            and all(char in _NEGATIVE_CONTINUATION_CHARS for char in separator))
def _positive_action_probe(text: str) -> str:
    return re.sub(r"^\s*\[[^\]\r\n]+\]\s*", "", text).strip()
def _has_positive_business_action(text: str) -> bool:
    probe = _positive_action_probe(text).lower()
    return bool(probe) and any(
        _action_word_matches(action, probe, allow_derived=False)
        for action in _RESPONSIBILITY_ACTION_WORDS)
_POSITIVE_CLAUSE_LEADING_RE = re.compile(
    r"^(?:(?:please|then)\s+|请|然后)+", re.IGNORECASE)
_POSITIVE_CLAUSE_MODAL_RE = re.compile(
    r"^(?:(?:can|could|will)\s+|可以|能够|可|能)", re.IGNORECASE)
_POSITIVE_AFFIRMATIVE_COPULA_RE = re.compile(
    r"\b(?:is|are|was|were)\s+(?:supported|covered|handled|processed|included|available|allowed)\b",
    re.IGNORECASE)
# 「仅/只 + 范围限定谓词」限定的是正向职责边界（仅包括 B = 只做 B），
# 不是排除对象；否则否定续接窗口会把它误写成 NOT FOR 规则。
_POSITIVE_SCOPE_RESTRICTION_RE = re.compile(
    r"^(?:仅|只)(?:限于|用于|用来|包括|包含|支持|负责|处理|覆盖|适用|提供|接受|允许)"
)
def _starts_positive_business_clause(clause: str) -> bool:
    probe = _NEGATIVE_CONTINUATION_LEADING_RE.sub(
        "", _positive_action_probe(clause)).lstrip().lower()
    probe = _POSITIVE_CLAUSE_LEADING_RE.sub("", probe).lstrip()
    for subject in _NEGATIVE_SCOPE_SUBJECTS:
        if not probe.startswith(subject):
            continue
        remainder = probe[len(subject):]
        if subject.isascii() and remainder[:1].isalnum():
            continue
        probe = remainder.lstrip(" \t\r\n,，、;；:：")
        break
    probe = _POSITIVE_CLAUSE_MODAL_RE.sub("", probe, count=1).lstrip()
    if _POSITIVE_SCOPE_RESTRICTION_RE.match(probe):
        return True
    if _POSITIVE_AFFIRMATIVE_COPULA_RE.search(probe):
        return True
    ascii_head = re.match(r"[A-Za-z]+", probe)
    if ascii_head is not None:
        token = ascii_head.group(0)
        return any(_action_word_matches(action, token)
                   for action in _RESPONSIBILITY_ACTION_WORDS)
    return any(not action.isascii() and probe.startswith(action)
               for action in _RESPONSIBILITY_ACTION_WORDS)
_COORDINATED_NEGATION_SPLIT_RE = re.compile(
    r"\b(?:and|or)\b|并且|而且|同时|以及", re.IGNORECASE)
def _split_coordinated_negation_prefix(prefix: str) -> tuple[str, str]:
    for coordinator in reversed(list(
            _COORDINATED_NEGATION_SPLIT_RE.finditer(prefix))):
        positive = prefix[:coordinator.start()].strip(" \t,，、;；:：")
        negative = prefix[coordinator.end():].strip(" \t,，、;；:：")
        if positive and negative and _starts_positive_business_clause(positive):
            return positive, negative
    return "", prefix
def _positive_prefix_before_negation(clause: str) -> str:
    matches = _iter_predicate_matches(clause)
    if not matches:
        return ""
    start, end, predicate = matches[0]
    prefix = clause[:start].strip(" \t,，、;；:：")
    after_text = clause[end:].strip(" \t,，、;；:：。")
    before_predicate = predicate.casefold() in _NEGATIVE_SCOPE_BEFORE_PREDICATES
    if (before_predicate and after_text
            and _NEGATIVE_CONTINUATION_LEADING_RE.match(after_text)):
        return ""
    if before_predicate:
        positive_prefix, _negative_prefix = _split_coordinated_negation_prefix(
            prefix)
        if positive_prefix:
            return positive_prefix
        # 「X is not supported [by this tool]」：前置谓词前无并列正职责时，
        # 整段前缀都是排除对象，不能当作正向能力泄漏（如「Image editing is」）；
        # 仅悬垂连接词（「docs and not supported pdf」）按后置语义走通用路径。
        if not (after_text and _ends_with_dangling_coordinator(prefix)):
            return ""
    if not after_text:
        return ""
    prefix = _POSITIVE_PREFIX_TRAILING_RE.sub("", prefix).strip(
        " \t,，、;；:：")
    return prefix if _has_positive_business_action(prefix) else ""
def _ends_with_dangling_coordinator(text: str) -> bool:
    return bool(_POSITIVE_PREFIX_TRAILING_RE.search(
        text.strip(" \t,，、;；:：")))
def _append_negative_rule(rules: list[str], seen: set[str], scope: str) -> None:
    key = scope.casefold()
    if scope and key not in seen:
        seen.add(key)
        rules.append(scope)
def _extract_negative_rules(desc: str) -> list[str]:
    text = normalize_text(desc)
    rules: list[str] = []
    seen: set[str] = set()
    negative_open = False
    for raw_clause, separator in _iter_clause_segments(text):
        clause = raw_clause.strip()
        if not clause:
            if negative_open and not _is_negative_continuation_separator(separator):
                negative_open = False
            continue
        matches = _iter_predicate_matches(clause)
        if (negative_open and not matches
                and not _starts_positive_business_clause(clause)):
            _append_negative_rule(rules, seen, _clean_negative_scope(clause))
            negative_open = _is_negative_continuation_separator(separator)
            continue
        for index, (start, end, predicate) in enumerate(matches):
            next_start = (matches[index + 1][0]
                          if index + 1 < len(matches) else len(clause))
            previous_end = matches[index - 1][1] if index else 0
            auxiliary = predicate.casefold() in _NEGATIVE_SCOPE_AUXILIARY_HEADS
            after_text = clause[end:next_start]
            if predicate.casefold() in _NEGATIVE_SCOPE_BEFORE_PREDICATES:
                after_text = _NEGATIVE_SCOPE_LEADING_PREPOSITION_RE.sub(
                    "", after_text, count=1)
            after = _clean_negative_scope(
                after_text, strip_leading_verb=auxiliary)
            before_text = clause[previous_end:start]
            before_predicate = (
                predicate.casefold() in _NEGATIVE_SCOPE_BEFORE_PREDICATES)
            dangling_coordinator = _ends_with_dangling_coordinator(before_text)
            if before_predicate:
                positive_prefix, coordinated_scope = (
                    _split_coordinated_negation_prefix(before_text))
                if positive_prefix:
                    before_text = coordinated_scope
                elif index:
                    coordinator = _COORDINATED_NEGATION_SPLIT_RE.search(
                        before_text)
                    if coordinator is not None:
                        before_text = before_text[coordinator.end():]
            before = _clean_negative_scope(
                before_text, strip_leading_verb=auxiliary)
            # 「A and not supported B」：前置谓词后仍带范围且谓词前是悬垂
            # 连接词时，谓词按后置语义生效，B 才是排除对象；A 是正职责，
            # 不能被写成 NOT FOR。
            prefer_before = (before_predicate and bool(before)
                             and not (after and dangling_coordinator))
            scope = before if prefer_before else (after or before)
            _append_negative_rule(rules, seen, scope)
        negative_open = (bool(matches)
                         and _is_negative_continuation_separator(separator))
    return rules
def generate_negative_rules(desc: str) -> str:
    rules = _extract_negative_rules(normalize_text(desc))
    return "; ".join(rules[:4]) if rules else _GENERIC_NEGATIVE_RULE
def _is_negation_clause(clause: str) -> bool:
    lowered = clause.lower()
    return any(pattern.search(lowered)
               for _predicate, pattern in _NEGATIVE_SCOPE_PATTERNS)
def _positive_business_clauses(text: str) -> list[str]:
    clauses: list[str] = []
    negative_open = False
    for raw_clause, separator in _iter_clause_segments(normalize_text(text)):
        clause = raw_clause.strip(" \t,，、")
        if not clause:
            if negative_open and not _is_negative_continuation_separator(separator):
                negative_open = False
            continue
        matches = _iter_predicate_matches(clause)
        if (negative_open and not matches
                and not _starts_positive_business_clause(clause)):
            negative_open = _is_negative_continuation_separator(separator)
            continue
        if matches:
            prefix = _positive_prefix_before_negation(clause)
            if prefix:
                clauses.append(prefix)
            negative_open = _is_negative_continuation_separator(separator)
            continue
        clauses.append(clause)
        negative_open = False
    return clauses
def _positive_business_text(text: str) -> str:
    return "。".join(_positive_business_clauses(text))
_MATCHING_BASE_LIMIT = 200
def _truncate_positive_core(text: str, limit: int) -> str:
    # 截断只落在句号边界：能力清单与锚点句直接消费该文本，半句会原样
    # 注入描述（如「支持多人协同审阅并汇总批」），故宁取整句。
    if len(text) <= limit:
        return text
    cut = text.rfind("。", 0, limit)
    if cut < 0:
        cut = text.find("。", limit)
    return text[:cut + 1] if cut >= 0 else text
def extract_base_keywords(name: str, existing_keywords: list[str]
                          ) -> tuple[set[str], dict]:
    name = normalize_text(name)
    existing_keywords = normalize_keywords(existing_keywords)
    keywords_set: set[str] = set()
    groups = {"core": [], "expanded": [], "long_tail": []}
    name_parts = re.split(r"[-_]", name.lower())
    for p in name_parts:
        if _is_meaningful_token(p) and p not in _NAME_STRUCTURAL_TOKENS:
            keywords_set.add(p)
            groups["core"].append(p)
    for kw in existing_keywords:
        if _is_meaningful_token(kw) and kw.lower() not in keywords_set:
            keywords_set.add(kw.lower())
            groups["core"].append(kw)
    return keywords_set, groups
def expand_spoken_and_cn(desc: str, desc_lower: str,
                         keywords_set: set[str], groups: dict) -> None:
    for _verb, patterns in _iter_matched_spoken(desc_lower):
        for pattern in patterns[:4]:
            normalized = pattern.lower()
            if normalized in keywords_set:
                continue
            keywords_set.add(normalized)
            groups["expanded"].append(pattern)
    cn_phrases = re.findall(
        RE_CHINESE_CHARS + r'{2,6}(?:技能|系统|引擎|模块|分析|诊断|检查|测试|优化|工具|'
        r'流程|策略|质量|安全|代码|数据|文件|文档|管理|平台|检测|评分|修复|重构|'
        r'生成|创建|编辑|转换|搜索|匹配|扫描|注册|上传|部署|监控|备份)',
        desc,
    )
    for phrase in cn_phrases:
        if phrase not in keywords_set:
            groups["expanded"].append(phrase)
            keywords_set.add(phrase)
_LONG_TAIL_TEMPLATES: tuple[str, ...] = (
    "如何{spoke}", "请{spoke}",
    "{spoke} please", "help me {spoke}",
)
def _join_action_noun(action: str, noun: str) -> str:
    # 动作词恒为英文；ASCII 名词须留空格分隔，中文名词保持紧邻。
    if noun[:1].isascii() and noun[:1].isalnum():
        return f"{action} {noun}"
    return f"{action}{noun}"
def expand_long_tail(desc_lower: str, groups: dict,
                     noun: str) -> None:
    if not noun:
        return
    for action in _iter_matched_actions(_positive_business_text(desc_lower)):
        groups["long_tail"].extend(
            template.format(spoke=_join_action_noun(action, noun))
            for template in _LONG_TAIL_TEMPLATES
        )
def _keyword_dedup_key(keyword: str) -> str:
    return normalize_text(keyword).strip().casefold()
def _merge_keyword_groups(groups: dict) -> list[str]:
    all_keywords: list[str] = []
    seen: set[str] = set()
    candidates = chain.from_iterable(
        groups[name] for name in ("core", "expanded", "long_tail"))
    for kw in candidates:
        key = _keyword_dedup_key(kw)
        if key in seen:
            continue
        seen.add(key)
        all_keywords.append(kw)
    return all_keywords
def _pad_core_to_five(groups: dict) -> None:
    core: list[str] = []
    seen: set[str] = set()
    for kw in groups["core"]:
        key = _keyword_dedup_key(kw)
        if key in seen:
            continue
        seen.add(key)
        core.append(kw)
    groups["core"] = core
    for bucket in ("expanded", "long_tail"):
        unique: list[str] = []
        for kw in groups[bucket]:
            key = _keyword_dedup_key(kw)
            if key in seen:
                continue
            seen.add(key)
            unique.append(kw)
        groups[bucket] = unique
    needed = 5 - len(core)
    for bucket in ("expanded", "long_tail"):
        if needed <= 0:
            break
        moved = groups[bucket][:needed]
        core.extend(moved)
        groups[bucket] = groups[bucket][len(moved):]
        needed -= len(moved)
def merge_and_pad_keywords(groups: dict) -> tuple[list[str], dict]:
    all_keywords = _merge_keyword_groups(groups)
    _pad_core_to_five(groups)
    return all_keywords, groups
def build_keyword_matrix(name: str, desc: str,
                          existing_keywords: list[str]) -> dict:
    name = normalize_text(name)
    desc = _positive_business_text(
        _strip_generated_fallback_prefix(strip_injected_sections(desc), name))
    existing_keywords = normalize_keywords(existing_keywords)
    keywords_set, groups = extract_base_keywords(name, existing_keywords)
    desc_lower = desc.lower()
    expand_spoken_and_cn(desc, desc_lower, keywords_set, groups)
    expand_long_tail(desc_lower, groups, extract_noun(name))
    all_keywords, groups = merge_and_pad_keywords(groups)
    return {
        "keywords": all_keywords,
        "groups": groups,
        "total_count": len(all_keywords),
    }
_DEFAULT_INCLUDE_SPOKEN = True
_DEFAULT_INCLUDE_BILINGUAL = True
_DEFAULT_MAX_KEYWORDS = 50
def append_unique_keyword(result: list[str], seen: set[str],
                          kw: object) -> None:
    if kw is None:
        return
    keyword = normalize_text(kw if isinstance(kw, str) else str(kw)).strip()
    key = _keyword_dedup_key(keyword)
    if not key or any(_keyword_dedup_key(existing) == key
                      for existing in seen):
        return
    seen.add(keyword)
    result.append(keyword)
def _find_spoken_match(kw: str,
                        patterns_dict: dict[str, list[str]]) -> list[str]:
    kw_lower = str(kw).lower()
    for patterns in patterns_dict.values():
        if any(keyword_matches(pattern.lower(), kw_lower)
               for pattern in patterns):
            return patterns
    return []
def _first_matching_action(kw: str,
                            patterns_dict: dict[str, list[str]]) -> str | None:
    probe = str(kw).lower()
    for action, patterns in patterns_dict.items():
        if any(probe == candidate.lower()
               for candidate in (action, *patterns)):
            return action
    return None
def _find_bilingual_matches(kw: str,
                             patterns_dict: dict[str, list[str]]) -> list[str]:
    probe = str(kw)
    action = _first_matching_action(probe, patterns_dict)
    if action is None:
        return []
    if re.search(RE_CHINESE_CHARS, probe):
        return [action]
    return [p for p in patterns_dict[action] if re.search(RE_CHINESE_CHARS, p)]
def _seed_keyword_matrix(base_keywords: list[str]) -> tuple[list[str], set[str]]:
    result: list[str] = []
    seen: set[str] = set()
    for kw in base_keywords:
        append_unique_keyword(result, seen, kw)
    return result, seen
def _extend_with_spoken(result: list[str], seen: set[str],
                        base_keywords: list[str]) -> None:
    for kw in base_keywords:
        for variant in _find_spoken_match(kw, SPOKEN_PATTERNS)[:6]:
            append_unique_keyword(result, seen, variant)
def _extend_with_bilingual(result: list[str], seen: set[str]) -> None:
    for kw in list(result):
        for addition in _find_bilingual_matches(kw, SPOKEN_PATTERNS):
            append_unique_keyword(result, seen, addition)
def expand_keyword_matrix(base_keywords: list[str],
                          include_spoken: bool = _DEFAULT_INCLUDE_SPOKEN,
                          include_bilingual: bool = _DEFAULT_INCLUDE_BILINGUAL,
                          max_keywords: int = _DEFAULT_MAX_KEYWORDS) -> list[str]:
    base_keywords = normalize_keywords(base_keywords)
    include_spoken = normalize_bool_flag(
        include_spoken, _DEFAULT_INCLUDE_SPOKEN,
        "expand_keyword_matrix.include_spoken")
    include_bilingual = normalize_bool_flag(
        include_bilingual, _DEFAULT_INCLUDE_BILINGUAL,
        "expand_keyword_matrix.include_bilingual")
    max_keywords = normalize_nonnegative_count(
        max_keywords, _DEFAULT_MAX_KEYWORDS, "expand_keyword_matrix")
    result, seen = _seed_keyword_matrix(base_keywords)
    if include_spoken:
        _extend_with_spoken(result, seen, base_keywords)
    if include_bilingual:
        _extend_with_bilingual(result, seen)
    return result[:max_keywords]
@dataclass
class ValidationReport:
    passed: bool = True
    checks: dict[str, bool] = field(default_factory=dict)
    failures: list[str] = field(default_factory=list)
_SENTENCE_TERMINAL_TRANS = str.maketrans({
    "！": "。", "!": "。", "？": "。", "?": "。",
    "；": "。", ";": "。",
})
def _normalize_sentence_terminals(text: str) -> str:
    return re.sub(r"[。.]+", "。", normalize_text(text).translate(
        _SENTENCE_TERMINAL_TRANS)).strip()
def _check_non_regression(original_desc: str,
                          generated_desc: str) -> tuple[bool, str | None]:
    original_core = re.search(
        r'((?:(?:包括|核心能力)\s*[:：]|(?:including|core capabilities)\s*:).*?)'
        r'(?:口语化表达[：:]|业务能力[：:]|触发示例[：:]|NOT FOR\b|\Z)',
        original_desc, re.DOTALL | re.IGNORECASE)
    if not original_core:
        return True, None
    core_content = original_core.group(1).strip()
    normalized_core = _normalize_sentence_terminals(core_content).rstrip("。")
    if normalized_core in _normalize_sentence_terminals(generated_desc):
        return True, None
    return False, f"原始业务能力信息丢失: {core_content[:80]}..."
def _check_no_duplication(original_desc: str, generated_desc: str,
                          markers: tuple[str, ...]) -> tuple[bool, str | None]:
    for marker in markers:
        count = generated_desc.count(marker)
        if count <= 1 or count <= original_desc.count(marker):
            continue
        return False, f"标记 '{marker}' 重复出现 {count} 次"
    return True, None
def _check_trigger_unique(generated_desc: str) -> tuple[bool, str | None]:
    command_pattern = "|".join(re.escape(cmd) for cmd in TRIGGER_COMMANDS)
    commands = re.findall(
        rf"(?<![A-Za-z])({command_pattern})(?![A-Za-z])",
        generated_desc, flags=re.IGNORECASE)
    if len(commands) > 1:
        return False, "触发指令重复注入: " + ", ".join(commands)
    return True, None
def _check_content_growth(original_desc: str,
                          generated_desc: str) -> tuple[bool, str | None]:
    if len(generated_desc) >= len(original_desc):
        return True, None
    return False, f"内容缩减: {len(original_desc)}→{len(generated_desc)} 字符"
def _has_bilingual_signal(desc: str) -> bool:
    content = _LEADING_TRIGGER_MARK.sub("", normalize_text(desc), count=1)
    return (bool(re.search(RE_CHINESE_CHARS, content))
            and bool(re.search(r"[a-zA-Z]", content)))
def _has_anchor_signal(
        desc: str,
        anchors: Mapping[str, Any] | None = None) -> bool:
    desc_lower = normalize_text(desc).lower()
    catalog = _resolve_anchor_catalog(desc, anchors)
    return any(
        keyword_matches(anchor["name"].lower(), desc_lower)
        or any(keyword_matches(tag.lower(), desc_lower)
               for tag in anchor["tags"])
        for anchor in anchor_entries(catalog))
def _check_dimension_count(
        generated_desc: str,
        section_labels: tuple[str, ...],
        role_prefixes: tuple[str, ...],
        anchors: Mapping[str, Any] | None = None) -> tuple[bool, str | None]:
    dim_count = sum(
        1 for label in section_labels
        if _has_section_marker(generated_desc, label))
    if any(m in generated_desc for m in role_prefixes):
        dim_count += 1
    if _has_bilingual_signal(generated_desc):
        dim_count += 1
    if _has_anchor_signal(generated_desc, anchors):
        dim_count += 1
    if dim_count >= 3:
        return True, None
    return False, f"六维维度覆盖不足: 仅 {dim_count} 个维度"
def _check_keyword_preserved(generated_desc: str,
                             keywords: list[str]) -> tuple[bool, str | None]:
    if not keywords:
        return True, None
    sample = keywords[:10]
    desc_lower = generated_desc.lower()
    present = sum(1 for kw in sample if keyword_matches(kw, desc_lower))
    threshold = min(3, len(sample))
    if present >= threshold:
        return True, None
    return False, f"核心关键词仅保留 {present}/{len(sample)}（阈值 {threshold}）"
def _record_check(report: ValidationReport, name: str,
                  result: tuple[bool, str | None]) -> None:
    passed, failure = result
    report.checks[name] = passed
    if not passed:
        report.failures.append(failure or "")
        report.passed = False
def validate_description_generation(
    original_desc: str,
    generated_desc: str,
    keywords: list[str] | None = None,
    anchors: Mapping[str, Any] | None = None,
) -> ValidationReport:
    keywords = normalize_keywords(keywords)
    original_desc = normalize_text(original_desc)
    generated_desc = normalize_text(generated_desc)
    role_prefixes = tuple(rp["prefix"] for rp in ROLE_PERSPECTIVES.values())
    injection_markers = (*INJECTED_SECTION_LABELS, *role_prefixes)
    report = ValidationReport()
    _record_check(report, "non_regression",
                  _check_non_regression(original_desc, generated_desc))
    _record_check(report, "no_duplication",
                  _check_no_duplication(original_desc, generated_desc,
                                        injection_markers))
    _record_check(report, "trigger_unique",
                  _check_trigger_unique(generated_desc))
    _record_check(report, "content_growth",
                  _check_content_growth(original_desc, generated_desc))
    _record_check(report, "dimension_count",
                  _check_dimension_count(
                      generated_desc, INJECTED_SECTION_LABELS, role_prefixes,
                      anchors))
    _record_check(report, "keyword_preserved",
                  _check_keyword_preserved(generated_desc, keywords))
    return report

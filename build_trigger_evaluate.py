from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import random
import re
import sys
from collections import Counter
from collections.abc import Iterable, Iterator
from dataclasses import dataclass, field
from itertools import combinations
from pathlib import Path
from typing import Any, ClassVar, Self

if __package__ in (None, ""):
    _pkg_parent = os.path.dirname(
        os.path.dirname(os.path.abspath(__file__)))
    if _pkg_parent not in sys.path:
        sys.path.insert(0, _pkg_parent)
from jwsgj.build_discover_sixdim import compute_trigger_score
from jwsgj.build_text_document import (
    iter_matching_files,
    jaccard,
    normalize_str,
    normalize_str_list,
    normalize_text,
    read_skill_text,
    tokenize_words,
)
from jwsgj.build_text_frontmatter import (
    extract_description,
    read_frontmatter_skill_name,
)
from jwsgj.build_text_scoring import (
    NEGATIVE_COMMANDS,
    VERB_SYNONYM_EXPANSION,
    keyword_matches,
    normalize_keywords,
    resolve_domain_key,
)
from jwsgj.diag_guard_io import (
    guarded_open,
    normalize_out_path,
    normalize_path_arg,
)
from jwsgj.diag_types_vocab import (
    CAT_DISCOVERABILITY,
)
from jwsgj.log_config import log_swallowed

logger = logging.getLogger(__name__)
__all__ = [
    'ATTENTION_WEIGHT_KEYWORDS',
    'CN_ATTENTION_WORDS',
    'DOMAIN_TRIGGER_PATTERNS',
    'NEGATIVE_INDICATORS',
    'ConceptDefinition',
    'SemanticConsistencyReport',
    'SemanticConsistencyValidator',
    'SemanticGap',
    'TestCase',
    'TestDataset',
    'TestDatasetGenerator',
    'TestPrompt',
    'TestPromptManager',
    'TriggerOptimizationResult',
    'TriggerOptimizer',
    'TriggerTestCase',
    'TriggerTestResult',
    'TriggerTestSuite',
    'TriggerTestSuiteResult',
    'batch_analyze_triggers',
    'export_semantic_gaps',
    'export_test_dataset_to_json',
    'export_test_dataset_to_jsonl',
    'generate_trigger_report',
    'load_test_prompts',
    'normalize_root_str',
    'scan_skill_descriptions',
]
logger.info("build_trigger_evaluate 已加载：%d 项导出", len(__all__))
@dataclass
class TestCase:
    input_text: str = ""
    case_type: str = ""
    expected_skill: str = ""
    expected_confidence: float = 0.0
    description: str = ""
    tags: list[str] = field(default_factory=list)
@dataclass
class TestDataset:
    skill_name: str = ""
    description: str = ""
    keywords: list[str] = field(default_factory=list)
    positive_cases: list[TestCase] = field(default_factory=list)
    negative_cases: list[TestCase] = field(default_factory=list)
    boundary_cases: list[TestCase] = field(default_factory=list)
    chain_cases: list[TestCase] = field(default_factory=list)
    summary: dict[str, Any] = field(default_factory=dict)
    def __post_init__(self: Self) -> None:
        if not self.summary:
            self.summary = _build_dataset_summary(self)
def _optional_finite_float(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        number = float(value)
    except (OverflowError, TypeError, ValueError):
        return None
    return number if math.isfinite(number) else None
def _finite_float(value: Any) -> float:
    number = _optional_finite_float(value)
    return 0.0 if number is None else number
def _case_type_counts(entries: list[tuple[str, TestCase]]) -> dict[str, int]:
    counts = Counter(case_type for case_type, _ in entries)
    known_types = ("positive", "negative", "boundary", "chain")
    other_count = sum(
        count for case_type, count in counts.items()
        if case_type not in known_types)
    return {
        "total_cases": len(entries),
        "positive_count": counts["positive"],
        "negative_count": counts["negative"],
        "boundary_count": counts["boundary"],
        "chain_count": counts["chain"],
        "other_count": other_count,
    }
def _build_dataset_summary(
    dataset: TestDataset, extra: dict | None = None
) -> dict[str, Any]:
    entries = _iter_dataset_case_entries(dataset, warn=False)
    summary: dict[str, Any] = {
        "skill_name": dataset.skill_name,
        **_case_type_counts(entries),
    }
    if extra:
        summary.update(extra)
    return summary
def _iter_dataset_case_entries(
    dataset: TestDataset, *, warn: bool
) -> list[tuple[str, TestCase]]:
    valid: list[tuple[str, TestCase]] = []
    for group_name in ('positive_cases', 'negative_cases',
                       'boundary_cases', 'chain_cases'):
        group = getattr(dataset, group_name)
        if group is None:
            continue
        if not isinstance(group, (list, tuple)):
            if warn:
                logger.warning("跳过非列表用例组 %s: %r", group_name, group)
            continue
        case_type = group_name.removesuffix("_cases")
        for case in group:
            if isinstance(case, TestCase):
                effective = (case.case_type
                             if isinstance(case.case_type, str)
                             and case.case_type else case_type)
                valid.append((effective, case))
            elif warn:
                logger.warning("跳过非 TestCase 用例项: %r", case)
    return valid
def _case_to_dict(case: TestCase, default_type: str) -> dict:
    case_type = case.case_type if isinstance(case.case_type, str) else ""
    return {
        "input_text": case.input_text,
        "case_type": case_type or default_type,
        "expected_skill": case.expected_skill,
        "expected_confidence": _finite_float(case.expected_confidence),
        "description": case.description,
        "tags": normalize_str_list(case.tags),
    }
def _build_dataset_payload(dataset: TestDataset) -> dict:
    entries = _iter_dataset_case_entries(dataset, warn=True)
    if isinstance(dataset.summary, dict):
        summary = dict(dataset.summary)
    else:
        logger.warning("导出 summary 非 dict: %r，归空并重建计数", dataset.summary)
        summary = {}
    summary.update({
        "skill_name": normalize_str(dataset.skill_name),
        **_case_type_counts(entries),
    })
    return {
        "skill_name": normalize_str(dataset.skill_name),
        "description": normalize_str(dataset.description),
        "keywords": normalize_str_list(dataset.keywords),
        "summary": summary,
        "cases": [_case_to_dict(case, group) for group, case in entries],
    }
def _prepare_output_path(output_path: Any, entry: str) -> str | None:
    if output_path is None:
        return None
    out_path = normalize_out_path(output_path)
    if out_path is None:
        logger.warning("%s output_path 非法: %r，跳过落盘", entry, output_path)
        return None
    if os.path.isdir(out_path):
        logger.warning("%s output_path 指向目录，跳过落盘: %s", entry, out_path)
        return None
    return out_path
def _prepare_export(dataset: TestDataset, output_path: Any,
                    entry: str) -> tuple[TestDataset, str | None]:
    if not isinstance(dataset, TestDataset):
        logger.warning("%s 入参非 TestDataset: %s，降级空数据集",
                       entry, type(dataset).__name__)
        dataset = TestDataset()
    return dataset, _prepare_output_path(output_path, entry)
def export_test_dataset_to_json(dataset: TestDataset, output_path: str) -> str:
    dataset, out_path = _prepare_export(
        dataset, output_path, "export_test_dataset_to_json")
    if out_path is None:
        return ""
    data = _build_dataset_payload(dataset)
    with guarded_open(out_path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(data, f, ensure_ascii=False, indent=2, default=str)
    return os.path.abspath(out_path)
def export_test_dataset_to_jsonl(dataset: TestDataset, output_path: str) -> str:
    dataset, out_path = _prepare_export(
        dataset, output_path, "export_test_dataset_to_jsonl")
    if out_path is None:
        return ""
    with guarded_open(out_path, "w", encoding="utf-8", newline="\n") as f:
        for case_type, case in _iter_dataset_case_entries(dataset, warn=True):
            f.write(json.dumps(
                _case_to_dict(case, case_type), ensure_ascii=False,
                default=str) + "\n")
    return os.path.abspath(out_path)
_DEFAULT_POSITIVE_COUNT = 12
_DEFAULT_NEGATIVE_COUNT = 8
_DEFAULT_BOUNDARY_COUNT = 6
_DEFAULT_CHAIN_COUNT = 4
def _coerce_count(value: Any, default: int) -> int:
    if value is None:
        return default
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        logger.warning("计数值载荷非数字: %r，回退默认 %d", value, default)
        return default
    if isinstance(value, float) and not math.isfinite(value):
        logger.warning("计数值载荷非有限值: %r，回退默认 %d", value, default)
        return default
    return max(0, int(value))
def _normalize_counts(positive_count: Any, negative_count: Any,
                      boundary_count: Any, chain_count: Any
                      ) -> tuple[int, int, int, int]:
    return (
        _coerce_count(positive_count, _DEFAULT_POSITIVE_COUNT),
        _coerce_count(negative_count, _DEFAULT_NEGATIVE_COUNT),
        _coerce_count(boundary_count, _DEFAULT_BOUNDARY_COUNT),
        _coerce_count(chain_count, _DEFAULT_CHAIN_COUNT),
    )
_POSITIVE_TEMPLATES: dict[str, list[str]] = {
    "direct": [
        "帮我{action}{target}", "请{action}一个{target}", "能不能{action}{target}",
        "我想{action}{target}", "给我{action}一个{target}",
        "如何使用此技能{action}{target}", "需要{action}{target}",
    ],
    "polite": [
        "请问可以帮我{action}{target}吗", "麻烦帮我{action}一下{target}", "能否请你{action}{target}",
    ],
    "casual": [
        "{action}个{target}吧", "把{target}{action}一下", "{action}{target}，谢谢", "来{action}个{target}",
    ],
    "professional": [
        "执行{action}操作，对象为{target}", "对{target}进行{action}处理",
        "调用技能完成{target}的{action}", "使用本技能{action}{target}",
    ],
    "english": [
        "Please help me {action} {target}", "I need to {action} {target}",
        "Can you {action} {target} for me", "How do I {action} {target}",
        "Trigger skill to {action} {target}", "Use this skill to {action} {target}",
    ],
    "mixed": [
        "帮我{action}一下这个{target} please", "能不能{action} {target} for me",
        "I want to {action} {target}", "请{action} {target}, thanks",
    ],
}
_EXPLICIT_EXCLUSION_TEMPLATES_CN: tuple[str, ...] = (
    "请不要使用{skill}处理这个请求",
    "不要调用{skill}，我想自己处理",
    "无需触发{skill}，保持当前状态",
    "请避免使用{skill}完成这项任务",
    "不用加载{skill}，我只需要人工答复",
    "别启用{skill}，这次不要自动处理",
)
_EXPLICIT_EXCLUSION_TEMPLATES_EN: tuple[str, ...] = (
    "Do not use {skill} for this request",
    "Don't call {skill}; I will handle it myself",
    "Never trigger {skill} for this task",
    "Avoid invoking {skill} this time",
    "Do not load {skill}; provide a manual answer",
    "Never activate {skill} for this request",
)
_EXPLICIT_EXCLUSION_TEMPLATES = (
    _EXPLICIT_EXCLUSION_TEMPLATES_CN + _EXPLICIT_EXCLUSION_TEMPLATES_EN)
def _explicit_exclusion_text(skill_name: str, index: int,
                             latin: bool | None = None) -> str:
    index = max(0, int(index))
    templates = (_EXPLICIT_EXCLUSION_TEMPLATES if latin is None else
                 _EXPLICIT_EXCLUSION_TEMPLATES_EN if latin else
                 _EXPLICIT_EXCLUSION_TEMPLATES_CN)
    template = templates[index % len(templates)]
    template_latin = latin if latin is not None else not _CJK_SCOPE_RE.search(template)
    skill = normalize_str(skill_name).strip() or (
        "current skill" if template_latin else "当前技能")
    text = template.format(skill=skill)
    cycle = index // len(templates)
    if cycle:
        text += _round_suffix(cycle + 1, template_latin)
    return text
_POSITIVE_TEMPLATE_FLAT: tuple[str, ...] = tuple(
    template for templates in _POSITIVE_TEMPLATES.values()
    for template in templates)
_CHAIN_TEMPLATES: list[str] = [
    "先{action1}{target1}，再{action2}{target2}",
    "帮我{action1}{target1}，然后{action2}{target2}",
    "第一步{action1}{target1}，第二步{action2}{target2}",
    "{action1}{target1}之后{action2}{target2}",
]
_CHAIN_TEMPLATES_EN: list[str] = [
    "First {action1} {target1}, then {action2} {target2}",
    "Help me {action1} {target1} and then {action2} {target2}",
    "Step 1: {action1} {target1}. Step 2: {action2} {target2}",
    "After {action1} {target1}, {action2} {target2}",
]
_CJK_SCOPE_RE = re.compile(r"[\u3400-\u4dbf\u4e00-\u9fff]")
def _is_latin_skill(*texts: Any) -> bool:
    joined = " ".join(
        item for text in texts
        for item in ([str(part) for part in text]
                     if isinstance(text, (list, tuple, set))
                     else [text if isinstance(text, str) else ""]))
    if _CJK_SCOPE_RE.search(joined):
        return False
    return bool(re.search(r"[A-Za-z]", joined))
_DEFAULT_ACTION = "处理"
_DEFAULT_ACTION_EN = "process"
_DEFAULT_LATIN = False
_ACTION_CN_LABELS: dict[str, str] = {
    "create": "创建",
    "edit": "编辑",
    "delete": "删除",
    "search": "搜索",
    "analyze": "分析",
    "convert": "转换",
    "merge": "合并",
    "check": "检查",
    "extract": "提取",
    "send": "发送",
    "monitor": "监控",
    "deploy": "部署",
    "backup": "备份",
    "restore": "恢复",
    "optimize": "优化",
    "format": "格式化",
    "calculate": "计算",
    "compare": "对比",
}
_ACTION_VERBS: dict[str, list[str]] = {
    label: list(dict.fromkeys(
        [verb, *VERB_SYNONYM_EXPANSION[verb], label]))
    for verb, label in _ACTION_CN_LABELS.items()
    if verb in VERB_SYNONYM_EXPANSION
}
def _action_en_form(action: str) -> str:
    key = normalize_str(action).strip()
    if not key:
        return key
    for synonym in _ACTION_VERBS.get(key, ()):
        if synonym.isascii():
            return synonym
    return _DEFAULT_ACTION_EN if key == _DEFAULT_ACTION else key
def _render_template(template: str, action: str, target: str) -> str:
    form = action if _CJK_SCOPE_RE.search(template) else _action_en_form(action)
    return template.format(action=form, target=target)
def _round_suffix(cycle: int, latin: bool) -> str:
    return f" (round {cycle})" if latin else f"（第{cycle}轮）"
_MIN_TERM_LEN = 2
_TARGET_STOPWORDS: frozenset[str] = frozenset({
    "skill", "skills", "help", "me", "the", "a", "an",
    "tool", "tools", "util", "utils", "helper", "agent", "service", "manager",
})
_ACTION_WORD_FORMS: frozenset[str] = frozenset(
    form.lower() for synonyms in _ACTION_VERBS.values()
    for form in synonyms)
def _target_like_keywords(keywords: list[str], action: str) -> list[str]:
    action_forms = _ACTION_WORD_FORMS
    return [kw for kw in keywords
            if kw.lower() != action and kw.lower() not in action_forms]
def _pick_target_keyword(keywords: list[str], action: str) -> str | None:
    for kw in _target_like_keywords(keywords, action):
        low = kw.lower()
        if len(low) < _MIN_TERM_LEN or low in _TARGET_STOPWORDS:
            continue
        return kw
    return None
def _synonyms_for(action: str, *, latin: bool = _DEFAULT_LATIN) -> list[str]:
    key = normalize_str(action).strip()
    if not key:
        return []
    forms = _ACTION_VERBS.get(key)
    if forms is None:
        cn_label = _ACTION_CN_LABELS.get(key.lower())
        forms = _ACTION_VERBS.get(cn_label) if cn_label else None
    if not forms:
        return []
    return [form for form in forms
            if form != key and (form.isascii() if latin else not form.isascii())]
_EN_INFLECTION_SUFFIX = r"(?:es|ed|ing|s)?"
_VOWEL_CHARS = frozenset("aeiou")
_NO_DOUBLE_CHARS = frozenset("aeiouwxy")
def _en_inflection_patterns(form: str) -> list[str]:
    escaped = re.escape(form)
    patterns = [rf"{escaped}{_EN_INFLECTION_SUFFIX}"]
    if (form.endswith("e")
            and (len(form) > 3
                 or (len(form) == 3 and form[-2] not in _VOWEL_CHARS))):
        patterns.append(rf"{re.escape(form[:-1])}(?:ing|ed)")
    if (len(form) > 2 and form.endswith("y")
            and form[-2] not in _VOWEL_CHARS):
        patterns.append(rf"{re.escape(form[:-1])}(?:ies|ied)")
    if (len(form) >= 3 and form[-1].isalpha()
            and form[-1] not in _NO_DOUBLE_CHARS
            and form[-2] in _VOWEL_CHARS
            and form[-3].isalpha() and form[-3] not in _VOWEL_CHARS):
        patterns.append(rf"{re.escape(form + form[-1])}(?:ing|ed)")
    return patterns
def _matched_en_form(form: str, text_lower: str) -> str | None:
    if not form:
        return None
    for pattern in _en_inflection_patterns(form):
        found = re.search(
            rf"(?<![A-Za-z0-9_]){pattern}(?![A-Za-z0-9_])", text_lower)
        if found:
            return found.group(0)
    return None
def _matched_form(form: str, text_lower: str) -> str | None:
    if not form:
        return None
    if not form.isascii():
        return form if form in text_lower else None
    return _matched_en_form(form, text_lower)
def _form_hits(form: str, text_lower: str) -> bool:
    return _matched_form(form, text_lower) is not None
class TestDatasetGenerator:
    def generate(self: Self, skill_name: str, description: str = "",
                 keywords: list[str] | None = None,
                 depends_on: list[str] | None = None,
                 positive_count: int | None = None,
                 negative_count: int | None = None,
                 boundary_count: int | None = None,
                 chain_count: int | None = None) -> TestDataset:
        positive_count, negative_count, boundary_count, chain_count = (
            _normalize_counts(positive_count, negative_count,
                              boundary_count, chain_count)
        )
        skill_name = normalize_str(skill_name)
        description = normalize_str(description)
        keywords = normalize_str_list(keywords)
        depends_on = list(dict.fromkeys(normalize_str_list(depends_on)))
        dataset = TestDataset(skill_name=skill_name, description=description, keywords=keywords)
        action, target = self._extract_action_target(skill_name, description, keywords)
        latin = _is_latin_skill(skill_name, description, keywords)
        dataset.positive_cases = self._generate_positive(
            skill_name, action, target, keywords, positive_count, latin=latin)
        dataset.negative_cases = self._generate_negative(
            negative_count, skill_name, latin=latin)
        dataset.boundary_cases = self._generate_boundary(
            skill_name, action, target, boundary_count, latin=latin)
        dataset.chain_cases = self._generate_chain(
            skill_name, action, target, depends_on, chain_count, latin=latin)
        dataset.summary = _build_dataset_summary(
            dataset, {"action": action, "target": target})
        return dataset
    def _extract_action_target(self: Self, skill_name: str, description: str,
                               keywords: list[str]) -> tuple[str, str]:
        combined = (skill_name + " " + description + " " + " ".join(keywords)).lower()
        primary = _NOT_FOR_RE.sub(" ", combined)
        action = _DEFAULT_ACTION
        for act, synonyms in _ACTION_VERBS.items():
            if any(_form_hits(s.lower(), primary) for s in synonyms):
                action = act
                break
        target = re.sub(
            r"\s+", " ",
            re.sub(r"[-_]+", " ", skill_name.removeprefix("skill-")),
        ).strip()
        picked = _pick_target_keyword(keywords, action)
        if picked:
            target = picked
        return action, target
    @staticmethod
    def _positive_templates(keywords: list[str], action: str,
                            target: str, latin: bool = _DEFAULT_LATIN) -> list[str]:
        rendered = [
            _render_template(template, action, target)
            for template in _POSITIVE_TEMPLATE_FLAT
            if not latin or not _CJK_SCOPE_RE.search(template)
        ]
        keyword_templates = (
            "帮我{action}{target}",
            "请{action}一个{target}",
            "能不能{action}{target}",
            "Please {action} the {target}",
            "I need to {action} {target}",
        )
        for kw in _target_like_keywords(keywords, action)[:3]:
            if latin and _CJK_SCOPE_RE.search(kw):
                continue
            rendered.extend(
                _render_template(template, action, kw)
                for template in keyword_templates
                if not latin or not _CJK_SCOPE_RE.search(template)
            )
        return list(dict.fromkeys(rendered))
    def _generate_positive(self: Self, skill_name: str, action: str, target: str,
                           keywords: list[str], count: int,
                           latin: bool = _DEFAULT_LATIN) -> list[TestCase]:
        templates = self._positive_templates(
            keywords, action, target, latin=latin)
        if not templates:
            return []
        rng = random.Random(hashlib.sha256(
            (skill_name + action + target).encode("utf-8")).digest())  # nosec B311
        rendered_texts = rng.sample(
            templates, min(count, len(templates)))  # nosec B311
        for i in range(len(rendered_texts), count):
            cycle = i // len(templates)
            rendered_texts.append(
                f"{templates[i % len(templates)]}{_round_suffix(cycle + 1, latin)}")
        cases: list[TestCase] = []
        for text in rendered_texts:
            cases.append(TestCase(
                input_text=text, case_type="positive", expected_skill=skill_name,
                expected_confidence=0.8 + rng.random() * 0.2,  # nosec B311
                description=f"正例: {text[:30]}...",
                tags=["positive", "direct_trigger" if "帮我" in text else "indirect_trigger"],
            ))
        return cases
    def _generate_negative(self: Self, count: int,
                           skill_name: str = "",
                           latin: bool | None = None) -> list[TestCase]:
        if count <= 0:
            return []
        return [TestCase(
            input_text=_explicit_exclusion_text(skill_name, i, latin=latin),
            case_type="negative", expected_skill="", expected_confidence=0.0,
            description="负例: 请求明确排除当前技能",
            tags=["negative", "explicit_exclusion"],
        ) for i in range(count)]
    def _generate_boundary(self: Self, skill_name: str, action: str, target: str,
                           count: int, latin: bool = _DEFAULT_LATIN) -> list[TestCase]:
        if count <= 0:
            return []
        action_form = _action_en_form(action) if latin else action
        vague = (f"Can you handle this {target} somehow?" if latin
                 else f"帮我{_DEFAULT_ACTION}一下这个{target}")
        multi = (f"Please {action_form} {target}, and also check the weather"
                 if latin else f"帮我{action}{target}，顺便查一下天气")
        cases: list[TestCase] = []
        cases.append(TestCase(input_text=action_form, case_type="boundary",
            expected_skill=skill_name, expected_confidence=0.3,
            description="边界: 只有动词，无目标", tags=["boundary", "incomplete_input"]))
        cases.append(TestCase(input_text=target, case_type="boundary",
            expected_skill=skill_name, expected_confidence=0.4,
            description="边界: 只有目标，无动作", tags=["boundary", "incomplete_input"]))
        cases.append(TestCase(input_text=vague, case_type="boundary",
            expected_skill=skill_name, expected_confidence=0.5,
            description="边界: 模糊动词'处理'", tags=["boundary", "vague_verb"]))
        cases.append(TestCase(input_text=multi, case_type="boundary",
            expected_skill=skill_name, expected_confidence=0.5,
            description="边界: 多意图混合", tags=["boundary", "multi_intent"]))
        exclusion_target = normalize_str(skill_name).strip() or (
            "current skill" if latin else "当前技能")
        exclusion_text = (
            f"Do not use {exclusion_target} to {action_form} {target}" if latin
            else f"不要使用{exclusion_target}{action}{target}")
        cases.append(TestCase(
            input_text=exclusion_text,
            case_type="boundary", expected_skill="", expected_confidence=0.0,
            description="边界: 显式排除当前技能",
            tags=["boundary", "negation", "explicit_exclusion"]))
        cases.append(TestCase(input_text="", case_type="boundary",
            expected_skill="", expected_confidence=0.0,
            description="边界: 空输入", tags=["boundary", "empty_input"]))
        synonyms = _synonyms_for(action, latin=latin)
        if synonyms:
            for syn in synonyms[:2]:
                text = f"Please {syn} {target}" if latin else f"帮我{syn}{target}"
                cases.append(TestCase(input_text=text, case_type="boundary",
                    expected_skill=skill_name, expected_confidence=0.6,
                    description=f"边界: 同义动词 '{syn}'", tags=["boundary", "synonym"]))
        if count <= len(cases):
            return cases[:count]
        filled = list(cases)
        for i in range(len(cases), count):
            base = cases[i % len(cases)]
            cycle = i // len(cases)
            filled.append(TestCase(
                input_text=f"{base.input_text}{_round_suffix(cycle + 1, latin)}",
                case_type=base.case_type,
                expected_skill=base.expected_skill,
                expected_confidence=base.expected_confidence,
                description=base.description,
                tags=list(base.tags)))
        return filled
    def _generate_chain(self: Self, skill_name: str, action: str, target: str,
                        depends_on: list[str] | None, count: int,
                        latin: bool = _DEFAULT_LATIN) -> list[TestCase]:
        cases: list[TestCase] = []
        dep_skills = depends_on[: min(2, max(0, count))] if depends_on else []
        if latin:
            templates = _CHAIN_TEMPLATES_EN
            chain_actions = [_action_en_form(action),
                             "check", "save", "export"]
            chain_targets = [target, "result", "report", "file"]
        else:
            templates = _CHAIN_TEMPLATES
            chain_actions = [action, "检查", "保存", "导出"]
            chain_targets = [target, "结果", "报告", "文件"]
        generic_count = max(0, count - len(dep_skills))
        for i in range(generic_count):
            template = templates[i % len(templates)]
            cycle = i // len(templates)
            a1 = chain_actions[i % len(chain_actions)]
            t1 = chain_targets[i % len(chain_targets)]
            a2 = chain_actions[(i + 1) % len(chain_actions)]
            t2 = chain_targets[(i + 1) % len(chain_targets)]
            text = template.format(action1=a1, target1=t1, action2=a2, target2=t2)
            if cycle:
                text += _round_suffix(cycle + 1, latin)
            cases.append(TestCase(input_text=text, case_type="chain",
                expected_skill=skill_name, expected_confidence=0.7,
                description=f"链式: {a1}->{a2}", tags=["chain", "multi_step"]))
        for dep_skill in dep_skills:
            text = (f"First use {dep_skill}, then use {skill_name} to "
                    f"{_action_en_form(action)} {target}" if latin
                    else f"先用{dep_skill}{_DEFAULT_ACTION}，再用"
                         f"{skill_name}{action}{target}")
            cases.append(TestCase(
                input_text=text,
                case_type="chain", expected_skill=skill_name, expected_confidence=0.6,
                description=f"链式: 依赖 {dep_skill}",
                tags=["chain", "cross_skill", f"depends_on:{dep_skill}"]))
        return cases
_DEFAULT_PROMPT_CATEGORY = "general"
_DEFAULT_PROMPT_DIFFICULTY = "beginner"
@dataclass
class TestPrompt:
    name: str = ""
    prompt: str = ""
    expected_keywords: list[str] = field(default_factory=list)
    category: str = _DEFAULT_PROMPT_CATEGORY
    difficulty: str = _DEFAULT_PROMPT_DIFFICULTY
    metadata: dict[str, Any] = field(default_factory=dict)
@dataclass
class TestPromptManager:
    prompts: list[TestPrompt] = field(default_factory=list)
    def __post_init__(self: Self) -> None:
        if isinstance(self.prompts, (list, tuple)):
            self.prompts = list(self.prompts)
        else:
            logger.warning("TestPromptManager prompts 非列表形态: %r，归空",
                           self.prompts)
            self.prompts = []
    def add_prompt(self, prompt: TestPrompt) -> None:
        if not isinstance(prompt, TestPrompt):
            logger.warning("add_prompt 拒绝非 TestPrompt 入参: %r", prompt)
            return
        self.prompts.append(prompt)
    def to_dict(self) -> dict:
        prompts_out: list[dict] = []
        for p in self.prompts:
            if not isinstance(p, TestPrompt):
                logger.warning("to_dict 跳过非 TestPrompt 项: %r", p)
                continue
            prompts_out.append(_prompt_to_dict(p))
        return {"prompts": prompts_out}
_PROMPT_FIELDS: tuple[str, ...] = (
    "name", "prompt", "expected_keywords", "category", "difficulty", "metadata")
def _prompt_to_dict(prompt: TestPrompt) -> dict:
    keywords = prompt.expected_keywords
    metadata = prompt.metadata
    return {
        "name": prompt.name if isinstance(prompt.name, str) else "",
        "prompt": prompt.prompt if isinstance(prompt.prompt, str) else "",
        "expected_keywords": normalize_str_list(keywords),
        "category": (prompt.category if isinstance(prompt.category, str)
                     else _DEFAULT_PROMPT_CATEGORY),
        "difficulty": (prompt.difficulty if isinstance(prompt.difficulty, str)
                       else _DEFAULT_PROMPT_DIFFICULTY),
        "metadata": dict(metadata) if isinstance(metadata, dict) else {},
    }
def _build_prompt(p_data: dict) -> TestPrompt:
    unknown = sorted(str(key) for key in p_data if key not in _PROMPT_FIELDS)
    if unknown:
        logger.warning("测试提示条目含未知字段 %s，已忽略这些字段", unknown)
    return TestPrompt(**_prompt_payload(p_data))
def _prompt_payload(p_data: dict) -> dict:
    name = p_data.get("name", "")
    prompt = p_data.get("prompt", "")
    category = p_data.get("category", _DEFAULT_PROMPT_CATEGORY)
    difficulty = p_data.get("difficulty", _DEFAULT_PROMPT_DIFFICULTY)
    metadata = p_data.get("metadata")
    return {
        "name": name if isinstance(name, str) else "",
        "prompt": prompt if isinstance(prompt, str) else "",
        "expected_keywords": normalize_str_list(
            p_data.get("expected_keywords")),
        "category": (category if isinstance(category, str)
                     else _DEFAULT_PROMPT_CATEGORY),
        "difficulty": (difficulty if isinstance(difficulty, str)
                       else _DEFAULT_PROMPT_DIFFICULTY),
        "metadata": dict(metadata) if isinstance(metadata, dict) else {},
    }
def _load_prompt_items(manager: TestPromptManager, prompts_raw: list) -> None:
    for p_data in prompts_raw:
        if not isinstance(p_data, dict):
            logger.warning("跳过非对象测试提示条目: %r", p_data)
            continue
        manager.add_prompt(_build_prompt(p_data))
def _read_prompt_payload(norm_path: str) -> list:
    try:
        with open(norm_path, encoding="utf-8-sig") as f:
            data = json.load(f)
    except (OSError, ValueError, TypeError, RecursionError) as exc:
        logger.warning("加载测试提示失败: %s", exc)
        return []
    if not isinstance(data, dict):
        logger.warning("测试提示文件顶层非对象，跳过加载: %s", norm_path)
        return []
    prompts_raw = data.get("prompts", [])
    if not isinstance(prompts_raw, list):
        logger.warning("测试提示 prompts 非列表，跳过加载: %s", norm_path)
        return []
    return prompts_raw
def load_test_prompts(path: str | os.PathLike | None = None) -> TestPromptManager:
    manager = TestPromptManager()
    norm_path = normalize_out_path(path)
    if not norm_path:
        return manager
    if not os.path.isfile(norm_path):
        logger.warning("测试提示路径不存在或不是文件，按空提示集处理: %s",
                       norm_path)
        return manager
    _load_prompt_items(manager, _read_prompt_payload(norm_path))
    return manager
@dataclass
class TriggerTestCase:
    query: str
    expected_trigger: bool
    priority: str = "normal"
    tags: list[str] = field(default_factory=list)
    expected_reason: str = ""
@dataclass
class TriggerTestResult:
    test_case: TriggerTestCase | None = None
    triggered: bool = False
    match_score: float = 0.0
    matched_keywords: list[str] = field(default_factory=list)
    passed: bool = False
    detail: str = ""
@dataclass(frozen=True)
class _ScoreEvidence:
    matched_kw: list[str]
    kw_lower: list[str]
    overlap: set[str]
    query_words: set[str]
    score: float
    neg_score: float
@dataclass
class TriggerTestSuiteResult:
    skill_name: str = ""
    total: int = 0
    passed: int = 0
    failed: int = 0
    false_positive: int = 0
    false_negative: int = 0
    accuracy: float = 0.0
    precision: float = 0.0
    recall: float = 0.0
    details: list[TriggerTestResult] = field(default_factory=list)
    recommendations: list[str] = field(default_factory=list)
def _confusion_counts(details: list[TriggerTestResult]) -> tuple[int, int, int]:
    outcomes = Counter(
        (bool(detail.test_case.expected_trigger), bool(detail.triggered))
        for detail in details if detail.test_case is not None
    )
    return outcomes[True, True], outcomes[False, True], outcomes[True, False]
def _normalize_keywords(keywords) -> list[str]:
    normalized = [kw.lower() for kw in normalize_str_list(keywords)]
    return [kw for kw in dict.fromkeys(normalized)
            if len(kw) >= _MIN_TERM_LEN]
def _negation_command_pattern(command: str) -> str:
    # 英文命令必须带词边界：否则 "not formatted" / "not use format" 会被
    # "NOT FOR" 前缀命中，把 "matted ..." 当成排除范围。
    pattern = r"\s+".join(re.escape(part) for part in command.split())
    if command[:1].isascii() and command[:1].isalpha():
        pattern = r"(?<![A-Za-z])" + pattern
    if command[-1:].isascii() and command[-1:].isalpha():
        pattern += r"(?![A-Za-z])"
    return pattern
_NOT_FOR_MARKERS: tuple[str, ...] = tuple(
    _negation_command_pattern(command) for command in NEGATIVE_COMMANDS
) + tuple(
    _negation_command_pattern(marker) for marker in (
        "NOT intended for", "NOT designed for", "NOT applicable to",
        "不要用于", "不用于", "禁止用于", "禁止使用", "不适用",
        "不负责", "不支持", "不涉及",
    )
)
# 强正向职责动词：用于在负向范围中识别「PDF，支持Word」这类正向转折。
# 只收强职责动词，避免把 "NOT FOR A, search results" 的名词短语误判为转折。
_POSITIVE_SCOPE_HEADS_CN: tuple[str, ...] = (
    "支持", "适用", "提供", "兼容", "负责", "涉及", "包含", "包括",
    "允许", "接受", "处理", "生成", "创建", "编辑", "分析", "转换",
    "合并", "检查", "诊断", "优化", "修复", "导出", "读取", "写入",
    "部署", "构建",
)
_POSITIVE_SCOPE_HEADS_EN: tuple[str, ...] = (
    "support", "handle", "provide", "cover", "offer", "include",
    "accept", "allow", "process", "generate", "create", "edit",
    "analyze", "convert", "merge", "check", "diagnose", "optimize",
    "fix", "export", "read", "write", "deploy", "build",
)
_POSITIVE_SCOPE_HEAD_ALT = "|".join((
    *(re.escape(word) for word in _POSITIVE_SCOPE_HEADS_CN),
    *(rf"(?<![A-Za-z]){re.escape(word)}(?:s|es|ed|ing)?(?![A-Za-z])"
      for word in _POSITIVE_SCOPE_HEADS_EN),
))
_NOT_FOR_CONTRAST = (
    r"(?:但(?:是)?|而是|\b(?:but|however|instead|rather)\b|"
    rf"[,，;；]\s*(?:(?:并|且|同时|以及|然后|再|还|也)\s*)*"
    rf"(?:{_POSITIVE_SCOPE_HEAD_ALT}))"
)
_NOT_FOR_PATTERN = (
    rf"(?:{'|'.join(_NOT_FOR_MARKERS)})\s*[:：]?\s*"
    rf"((?:(?!\.(?:\s|$)|[。！？!?\n]|{_NOT_FOR_CONTRAST}).)*)"
)
_NOT_FOR_RE = re.compile(_NOT_FOR_PATTERN, re.IGNORECASE)
# 查询侧对 NOT FOR 词的否定（not Word editing / 不要Word编辑）表示该词
# 不是本次需求，不能再按描述负例扣分，否则会把「I need PDF, not Word
# editing」误判为不触发。
_QUERY_TERM_NEGATION_RE = re.compile(
    r"(?:\b(?:not|never|no|without|avoid|don't|donot|dont|doesn't|didn't|"
    r"cannot|can't|won't|wouldn't|shouldn't|mustn't)\b[^.!?;；\n]{0,40}"
    r"|(?:不要|不用|无需|别|禁止|请勿|不能|不可|不想|不愿|不会|"
    r"而非|而不是|但不是)[^。！？；\n]{0,20})$",
    re.IGNORECASE,
)
def _term_negated_in_query(term: str, query_lower: str) -> bool:
    if not term or not query_lower:
        return False
    for match in re.finditer(re.escape(term), query_lower):
        prefix = query_lower[max(0, match.start() - 60):match.start()]
        if _QUERY_TERM_NEGATION_RE.search(prefix):
            return True
    return False
_NEG_TERM_SPLIT_RE = re.compile(r"[,，、/|&;；]+|\b(?:and|or)\b", re.IGNORECASE)
_CN_CONJUNCTION_CHARS = frozenset("和与及")
def _is_leading_conjunction(clause: str, index: int, seg_start: int) -> bool:
    if index != seg_start:
        return True
    if index == 0:
        return True
    return clause[index - 1] != clause[index]
def _split_cn_conjunctions(clause: str) -> list[str]:
    parts: list[str] = []
    seg_start = 0
    word_initial = False
    for i, ch in enumerate(clause):
        if ch not in _CN_CONJUNCTION_CHARS:
            continue
        left = clause[seg_start:i].strip()
        right = clause[i + 1:].strip()
        if not right:
            continue
        if len(left) >= 2 and len(right) >= 2:
            parts.append(left)
            seg_start = i + 1
            word_initial = False
        elif not left and _is_leading_conjunction(clause, i, seg_start):
            seg_start = i + 1
            word_initial = False
        elif not left:
            word_initial = True
    tail = clause[seg_start:].strip()
    if (parts and len(tail) >= 2
            and (word_initial or tail[0] not in _CN_CONJUNCTION_CHARS)):
        parts.append(tail)
    return parts
def _neg_terms(clause: str, *, include_whole: bool = True) -> list[str]:
    terms: list[str] = []
    for raw_part in _NEG_TERM_SPLIT_RE.split(clause):
        part = raw_part.strip()
        if not part:
            continue
        if include_whole:
            terms.append(part)
        split_parts = _split_cn_conjunctions(part)
        if split_parts:
            terms.extend(split_parts)
        elif not include_whole:
            terms.append(part)
    return list(dict.fromkeys(terms))
_NO_POSITIVE_CASE_HINT = (
    "测试集缺少正例：描述中未提取到可识别的核心名词，"
    "建议补充具体能力描述与核心关键词")
_KEYWORD_MATCH_MAX = 0.4
_TRIGGER_THRESHOLD = 0.3
_COLLOQUIAL_FLOOR = 0.35
_DESC_OVERLAP_MAX = 0.4
_RECOMMENDATION_THRESHOLD = 0.8
_COLLOQUIAL_CN_MARKERS: tuple[str, ...] = (
    "帮我", "给我", "我要", "我想", "能不能", "麻烦")
_STOPWORDS: frozenset[str] = frozenset({
    "a", "an", "and", "any", "are", "as", "at", "be", "been", "by",
    "can", "could", "did", "do", "does", "for", "from", "help", "how",
    "i", "in", "is", "it", "its", "me", "my", "of", "on", "or",
    "our", "please", "should", "some", "that", "the", "these", "this",
    "those", "to", "us", "was", "we", "were", "will", "with", "would",
    "you", "your",
    "一下", "一个", "与", "且", "什么", "以及", "但", "何", "你",
    "使用", "可以", "和", "哪个", "哪些", "怎么", "或", "我", "所有",
    "把", "并且", "并", "这个", "这些", "这样", "那个", "那些", "需要",
    "请", "进行", "还是", "还有", "这", "那", "的", "了", "及",
})
def _content_words(words: set[str]) -> set[str]:
    return {word for word in words if word not in _STOPWORDS}
def _word_forms_match(left: str, right: str) -> bool:
    if left == right:
        return True
    if not left.isascii() or not right.isascii():
        return False
    return (_matched_en_form(left, right) is not None
            or _matched_en_form(right, left) is not None)
def _description_content_overlap(query_words: set[str],
                                 desc_words: set[str]) -> set[str]:
    desc_content = _content_words(set(desc_words))
    exact = query_words & desc_content
    inflected = {
        word for word in query_words - exact
        if any(_word_forms_match(word, candidate) for candidate in desc_content)
    }
    return exact | inflected
_VERB_CANDIDATES: tuple[str, ...] = (
    "create", "edit", "analyze", "convert", "merge", "search",
    "generate", "process", "diag", "refactor", "build", "deploy",
    "read", "write", "extract", "transform", "validate",
    "创建", "编辑", "分析", "转换", "合并", "搜索", "生成",
    "处理", "诊断", "重构", "构建", "部署", "读取", "写入",
    "提取", "验证",
)
_NOUN_CANDIDATES: tuple[str, ...] = (
    "document", "docx", "xlsx", "pptx", "pdf", "data",
    "code", "script", "file", "image", "report",
    "文档", "表格", "幻灯片", "图片", "代码", "数据", "文件", "报告",
)
_REQUEST_SUPPLEMENT_ACTIONS = ("use", "handle", "save", "export")
_REQUEST_ACTION_FORMS = frozenset(
    form.lower()
    for form in (*_ACTION_WORD_FORMS, *_VERB_CANDIDATES,
                 *_REQUEST_SUPPLEMENT_ACTIONS)
)
_REQUEST_CN_ACTION_FORMS = tuple(sorted(
    (form for form in _REQUEST_ACTION_FORMS if not form.isascii()),
    key=len, reverse=True,
))
_REQUEST_EN_ACTION_FORMS = tuple(sorted(
    (form for form in _REQUEST_ACTION_FORMS if form.isascii()),
    key=len, reverse=True,
))
_REQUEST_CN_ACTION_ADVERB = r"(?:直接|立即|现在|马上|立刻|急着|再|先|继续)\s*"
_REQUEST_EN_ACTION_ADVERB = r"(?:now|immediately|directly)\s+"
# 否定体里的情态动词（不能处理 / 不想处理 / 不要会处理）不是动作本身，
# 需与「帮我/please」同层剥离，否则否定动作识别不到、仍参与正向计分。
_REQUEST_CN_ACTION_MODAL = r"(?:能|能够|可以|会|要|想|愿意|肯)\s*"
_REQUEST_ACTION_PREFIX_RE = re.compile(
    rf"^(?:(?:帮我|给我|替我|让我)\s*|{_REQUEST_CN_ACTION_MODAL}|"
    rf"(?:please|help\s+me(?:\s+to)?|(?:let|have)\s+me)\s+|"
    rf"{_REQUEST_CN_ACTION_ADVERB}|{_REQUEST_EN_ACTION_ADVERB})+",
    re.IGNORECASE,
)
# 裸「不」排除正反问式请求「能不能/会不会/可不可以/行不行」（两侧同字），
# 它们是口语请求而非否定；「不能处理」等真否定（后接动作）仍按否定处理。
_REQUEST_CN_BARE_NEGATION = (
    r"(?<!得)(?<!何)(?<!不能)(?<!并非)(?<!不是)"
    r"(?:(?<![能会可行])不|不(?![能会可行]))"
)
_REQUEST_CN_NEGATION_MARKERS = (
    r"(?:不需要|不要|请勿|禁止|无需|不用|别|避免|" + _REQUEST_CN_BARE_NEGATION + r")"
)
_REQUEST_CN_RHETORICAL_GUARD = r"(?<!为什么)(?<!为何)(?<!怎么)(?<!怎样)"
_REQUEST_NEGATION_CN_RE = re.compile(
    rf"{_REQUEST_CN_RHETORICAL_GUARD}{_REQUEST_CN_NEGATION_MARKERS}\s*"
    r"(?P<body>.*?)(?=改为|而是|但是|但|[。！？!?；;\n，,]|$)"
)
_REQUEST_EN_NEGATION_MARKERS = (
    r"(?:do\s+not|don't|doesn't|didn't|never|avoid|can't|cannot|won't|"
    r"couldn't|wouldn't|shouldn't|mustn't|(?<!why\s)(?<!not\s)not)"
)
_REQUEST_NEGATION_EN_RE = re.compile(
    rf"\b{_REQUEST_EN_NEGATION_MARKERS}\s+"
    r"(?P<body>.*?)(?=\b(?:instead|rather|but)\b|\.(?:\s|$)|[!?；;\n,，]|$)",
    re.IGNORECASE,
)
def _request_action_at_start(
    text: str, extra_forms: tuple[str, ...] = ()
) -> bool:
    stripped = _REQUEST_ACTION_PREFIX_RE.sub("", text.lstrip())
    cn_forms = _REQUEST_CN_ACTION_FORMS + tuple(
        form for form in extra_forms if form and not form.isascii())
    if any(stripped.startswith(form) for form in cn_forms):
        return True
    en_forms = _REQUEST_EN_ACTION_FORMS + tuple(
        form for form in extra_forms if form and form.isascii())
    return any(
        re.match(rf"{pattern}(?![A-Za-z0-9_])", stripped) is not None
        for form in en_forms
        for pattern in _en_inflection_patterns(form)
    )
def _mask_negated_action_match(
    match: re.Match[str], extra_forms: tuple[str, ...] = ()
) -> str:
    if _request_action_at_start(match.group("body"), extra_forms):
        return " "
    return match.group(0)
def _positive_request_text(
    query_lower: str, match_terms: Iterable[str] = ()
) -> str:
    extra_forms = tuple(dict.fromkeys(
        term.strip().lower() for term in match_terms
        if isinstance(term, str) and term.strip()))
    masked = _REQUEST_NEGATION_EN_RE.sub(
        lambda match: _mask_negated_action_match(match, extra_forms),
        query_lower,
    )
    return _REQUEST_NEGATION_CN_RE.sub(
        lambda match: _mask_negated_action_match(match, extra_forms), masked)
def _keyword_nouns(keywords: set[str]) -> list[str]:
    action_forms = _ACTION_WORD_FORMS
    picked: list[str] = []
    for kw in sorted(keywords):
        low = kw.lower()
        if (len(low) < _MIN_TERM_LEN or low in _TARGET_STOPWORDS
                or low in action_forms):
            continue
        picked.append(kw)
        if len(picked) >= 3:
            break
    return picked
def _extract_candidates(candidates: tuple[str, ...], desc: str,
                        keywords: set[str]) -> list[str]:
    picked: list[str] = []
    for item in candidates:
        if _matched_form(item, desc) is None and item not in keywords:
            continue
        if item not in picked:
            picked.append(item)
        if len(picked) >= 5:
            break
    return picked
def _normalize_custom_cases(custom_cases) -> list[TriggerTestCase] | None:
    if custom_cases is None:
        return None
    if not isinstance(custom_cases, (list, tuple)):
        logger.warning(
            "_run_setup custom_cases 非列表/元组类型（%s），已忽略改走自动生成",
            type(custom_cases).__name__)
        return None
    valid_cases = [c for c in custom_cases if isinstance(c, TriggerTestCase)]
    dropped = len(custom_cases) - len(valid_cases)
    if dropped:
        logger.warning(
            "_run_setup custom_cases 含 %d 个非 TriggerTestCase 项，已滤除",
            dropped)
    if valid_cases or not custom_cases:
        return valid_cases
    logger.warning(
        "_run_setup custom_cases 全部非法，按空测试集处理")
    return []
def _has_explicit_skill_exclusion(query_lower: str,
                                  skill_name: str = "") -> bool:
    name = normalize_str(skill_name).lower()
    cn_targets = [
        r"(?:(?:当前|本|此|这个|该|这)\s*)?"
        r"(?:技能|工具|系统|模块|组件|功能)",
    ]
    en_targets = [
        r"(?:(?:this|the)\s+)?(?:current\s+)?"
        r"(?:skill|tool|system|module|component|function)\b",
        r"当前\s*(?:技能|工具)",
    ]
    if name:
        escaped = re.escape(name)
        left = r"(?<![A-Za-z0-9_-])"
        boundary = r"(?![A-Za-z0-9_-])"
        cn_targets.insert(0, rf"{left}{escaped}(?:\s*技能)?{boundary}")
        en_targets.insert(
            0,
            rf"(?:(?:this|the|current)\s+)?{left}{escaped}"
            rf"(?:\s+(?:skill|tool))?{boundary}",
        )
    cn_pattern = (
        rf"{_REQUEST_CN_RHETORICAL_GUARD}{_REQUEST_CN_NEGATION_MARKERS}\s*"
        rf"(?:{_REQUEST_CN_ACTION_ADVERB})*"
        r"(?:使用|调用|触发|加载|启用|激活|用)?\s*"
        rf"(?:{'|'.join(cn_targets)})"
    )
    en_pattern = (
        rf"\b{_REQUEST_EN_NEGATION_MARKERS}\s+"
        rf"(?:{_REQUEST_EN_ACTION_ADVERB})*"
        r"(?:use|using|call|calling|trigger|triggering|invoke|invoking|"
        r"load|loading|activate|activating)\s+"
        rf"(?:{'|'.join(en_targets)})"
    )
    return (re.search(cn_pattern, query_lower, re.IGNORECASE) is not None
            or re.search(en_pattern, query_lower, re.IGNORECASE) is not None)
class TriggerTestSuite:
    _COLLOQUIAL_MARKERS: tuple[str, ...] = _COLLOQUIAL_CN_MARKERS + (
        "please help me", "i want to", "i need to", "i would like to",
        "can you",
    )
    def __init__(self: Self) -> None:
        self._test_cases: list[TriggerTestCase] = []
    @property
    def cases(self: Self) -> list[TriggerTestCase]:
        return list(self._test_cases)
    def _generate_positive_cases(self: Self, core_verbs: list[str],
                                  core_nouns: list[str], *,
                                  latin: bool) -> list[TriggerTestCase]:
        cases = []
        for verb in core_verbs[:3]:
            for noun in core_nouns[:3]:
                query = f"{verb} {noun}"
                cases.append(TriggerTestCase(
                    query=query,
                    expected_trigger=True,
                    priority="normal",
                    tags=["auto-positive"],
                    expected_reason=f"核心动词'{verb}' + 核心名词'{noun}'应触发技能",
                ))
        if not core_nouns:
            return cases
        default_verb = _DEFAULT_ACTION_EN if latin else _DEFAULT_ACTION
        verb0 = core_verbs[0] if core_verbs else default_verb
        verb1 = core_verbs[1] if len(core_verbs) > 1 else verb0
        verb2 = core_verbs[2] if len(core_verbs) > 2 else verb0
        noun0 = core_nouns[0]
        noun1 = core_nouns[1] if len(core_nouns) > 1 else noun0
        noun2 = core_nouns[2] if len(core_nouns) > 2 else noun0
        if latin:
            colloquial_templates = [
                f"Please help me {verb0} {noun0}",
                f"I want to {verb1} {noun1}",
                f"Can you {verb2} {noun2}",
            ]
        else:
            colloquial_templates = [
                f"帮我{verb0}一下{noun0}",
                f"我想{verb1}一下{noun1}",
                f"能不能{verb2}个{noun2}",
            ]
        for q in colloquial_templates:
            cases.append(TriggerTestCase(
                query=q,
                expected_trigger=True,
                priority="critical",
                tags=["auto-positive", "colloquial"],
                expected_reason="口语化表达应被查询改写后匹配",
            ))
        return cases
    def _generate_negative_from_description(self: Self, description: str) -> list[TriggerTestCase]:
        cases = []
        for part in _NOT_FOR_RE.findall(description):
            for term in _neg_terms(part, include_whole=False):
                if len(term) < _MIN_TERM_LEN:
                    continue
                cases.append(TriggerTestCase(
                    query=term,
                    expected_trigger=False,
                    priority="critical",
                    tags=["auto-negative"],
                    expected_reason=f"明确声明不适用场景'{term}'不应触发",
                ))
        return cases
    def _generate_exclusion_cases(self: Self, name: str) -> list[TriggerTestCase]:
        cases = []
        for i in range(len(_EXPLICIT_EXCLUSION_TEMPLATES)):
            query = _explicit_exclusion_text(name, i)
            cases.append(TriggerTestCase(
                query=query,
                expected_trigger=False,
                priority="edge",
                tags=["auto-negative", "explicit_exclusion"],
                expected_reason="请求明确排除当前技能，不应触发",
            ))
        return cases
    def generate_cases_from_skill(self: Self, name: str, description: str | None,
                                    keywords: list[str] | None) -> list[TriggerTestCase]:
        description = normalize_str(description)
        keywords = normalize_str_list(keywords)
        desc_lower = _NOT_FOR_RE.sub(" ", description.lower())
        keywords_lower = {k.lower() for k in keywords}
        core_verbs = _extract_candidates(
            _VERB_CANDIDATES, desc_lower, keywords_lower)
        core_nouns = _extract_candidates(
            _NOUN_CANDIDATES, desc_lower, keywords_lower)
        if not core_nouns:
            core_nouns = _keyword_nouns(keywords_lower)
        cases = []
        cases.extend(self._generate_positive_cases(
            core_verbs, core_nouns, latin=_is_latin_skill(
                name, description, keywords)))
        cases.extend(self._generate_negative_from_description(description))
        cases.extend(self._generate_exclusion_cases(name))
        return cases
    def _run_setup(self: Self, name: str, description: str | None,
                   keywords: list[str] | None,
                   custom_cases: list[TriggerTestCase] | None = None
                   ) -> tuple[list[TriggerTestCase], TriggerTestSuiteResult,
                              str, list[str], set[str]]:
        custom_cases = _normalize_custom_cases(custom_cases)
        desc_lower = normalize_str(description).lower()
        kw_lower = _normalize_keywords(keywords)
        test_cases = custom_cases if custom_cases is not None else (
            self.generate_cases_from_skill(name, description, kw_lower)
        )
        self._test_cases = list(test_cases)
        result = TriggerTestSuiteResult(
            skill_name=normalize_str(name),
            total=len(test_cases),
        )
        desc_words = tokenize_words(
            _NOT_FOR_RE.sub(" ", desc_lower))
        return test_cases, result, desc_lower, kw_lower, desc_words
    def _run_execute(self: Self, test_cases: list[TriggerTestCase], desc_lower: str,
                     kw_lower: list[str], desc_words: set[str],
                     result: TriggerTestSuiteResult) -> TriggerTestSuiteResult:
        for case in test_cases:
            test_result = self._run_single(
                case, desc_lower, kw_lower, desc_words, result.skill_name)
            result.details.append(test_result)
            if test_result.passed:
                result.passed += 1
            else:
                result.failed += 1
        return result
    def _run_report(self: Self, test_cases: list[TriggerTestCase],
                    result: TriggerTestSuiteResult) -> TriggerTestSuiteResult:
        total = len(test_cases)
        if total == 0:
            result.recommendations = [
                "测试集为空：未生成任何测试用例，请检查技能元数据或提供 custom_cases"
            ]
            return result
        result.accuracy = result.passed / total
        tp, fp, fn = _confusion_counts(result.details)
        result.false_positive = fp
        result.false_negative = fn
        if tp + fp > 0:
            result.precision = tp / (tp + fp)
        if tp + fn > 0:
            result.recall = tp / (tp + fn)
        result.recommendations = self._generate_recommendations(result, tp, fp, fn)
        if not any(d.test_case is not None and d.test_case.expected_trigger
                   for d in result.details):
            result.recommendations.insert(0, _NO_POSITIVE_CASE_HINT)
        return result
    def run(self: Self, name: str, description: str | None,
            keywords: list[str] | None,
            custom_cases: list[TriggerTestCase] | None = None) -> TriggerTestSuiteResult:
        test_cases, result, desc_lower, kw_lower, desc_words = self._run_setup(
            name, description, keywords, custom_cases
        )
        result = self._run_execute(test_cases, desc_lower, kw_lower, desc_words, result)
        return self._run_report(test_cases, result)
    def run_batch(self: Self, skills: list[dict] | None) -> dict[str, TriggerTestSuiteResult]:
        results: dict[str, TriggerTestSuiteResult] = {}
        for s in _normalize_skills_data(skills):
            if not isinstance(s, dict):
                logger.warning("run_batch: 跳过非 dict 项: %r", s)
                continue
            name = normalize_str(s.get("name"))
            outcome = self.run(
                name,
                s.get("description"),
                s.get("keywords"),
            )
            key = name
            if key in results:
                serial = 2
                while f"{name}#{serial}" in results:
                    serial += 1
                key = f"{name}#{serial}"
                logger.warning(
                    "run_batch: 技能名 %r 重复，结果保留于唯一键 %r", name, key)
            results[key] = outcome
        return results
    def _score_keyword_match(self: Self, query_lower: str,
                             kw_lower: list[str]) -> tuple[float, list[str]]:
        matched = []
        score = 0.0
        for kw in kw_lower:
            if self._term_hits_query(kw, query_lower):
                matched.append(kw)
                score += _KEYWORD_MATCH_MAX
        return min(score, _KEYWORD_MATCH_MAX), matched
    def _score_description_overlap(self: Self, query_lower: str,
                                   desc_words: set) -> tuple[float, set[str]]:
        query_words = _content_words(tokenize_words(query_lower))
        if not query_words:
            return 0.0, set()
        overlap = _description_content_overlap(query_words, set(desc_words))
        return (min(len(overlap) / len(query_words) * _DESC_OVERLAP_MAX,
                    _DESC_OVERLAP_MAX), overlap)
    @staticmethod
    def _term_hits_query(term: str, query_lower: str) -> bool:
        if not term:
            return False
        if term.isascii():
            return _matched_en_form(term, query_lower) is not None
        if term in query_lower:
            return True
        term_words = _content_words(tokenize_words(term))
        query_words = _content_words(tokenize_words(query_lower))
        return bool(term_words) and term_words <= query_words
    def _score_negative_match(self: Self, query_lower: str, desc_lower: str) -> float:
        not_clauses = _NOT_FOR_RE.findall(desc_lower)
        for clause in not_clauses:
            for raw_term in _neg_terms(clause):
                term = raw_term.lower()
                if (len(term) >= _MIN_TERM_LEN
                        and self._term_hits_query(term, query_lower)
                        and not _term_negated_in_query(term, query_lower)):
                    return -0.5
        return 0.0
    def _run_single(self: Self, case: TriggerTestCase, desc_lower: str,
                     kw_lower: list[str], desc_words: set[str],
                     skill_name: str = "") -> TriggerTestResult:
        query_lower = normalize_str(case.query).lower()
        positive_query = _positive_request_text(
            query_lower, (*kw_lower, *desc_words))
        kw_score, matched_kw = self._score_keyword_match(positive_query, kw_lower)
        desc_score, overlap = self._score_description_overlap(
            positive_query, desc_words)
        neg_score = self._score_negative_match(positive_query, desc_lower)
        score = round(self._apply_colloquial_compensation(
            kw_score + desc_score + neg_score, kw_score, desc_score,
            neg_score, positive_query), 6)
        excluded = _has_explicit_skill_exclusion(query_lower, skill_name)
        if excluded:
            score = 0.0
        triggered = not excluded and score > _TRIGGER_THRESHOLD
        detail = self._build_detail(
            _ScoreEvidence(
                matched_kw=matched_kw,
                kw_lower=kw_lower,
                overlap=overlap,
                query_words=_content_words(tokenize_words(positive_query)),
                score=score,
                neg_score=neg_score,
            )
        )
        if positive_query != query_lower:
            detail += " | 否定动作子句不参与正向计分"
        if excluded:
            detail += " | 请求显式排除当前技能: 不触发"
        return TriggerTestResult(
            test_case=case,
            triggered=triggered,
            match_score=score,
            matched_keywords=matched_kw,
            passed=(case.expected_trigger == triggered),
            detail=detail,
        )
    def _apply_colloquial_compensation(self: Self, score: float, kw_score: float,
                                        desc_score: float, neg_score: float,
                                        query_lower: str) -> float:
        if (any(m in query_lower for m in self._COLLOQUIAL_MARKERS)
                and (kw_score > 0 or desc_score > 0)
                and neg_score >= 0):
            return max(score, _COLLOQUIAL_FLOOR)
        return score
    @staticmethod
    def _build_detail(evidence: _ScoreEvidence) -> str:
        detail_parts = [
            (f"关键词匹配: {len(evidence.matched_kw)}/{len(evidence.kw_lower)} "
             f"({', '.join(evidence.matched_kw[:5])})"),
            f"描述覆盖查询词: {len(evidence.overlap)}/{len(evidence.query_words)}词",
            f"总得分: {evidence.score:.2f} (阈值>{_TRIGGER_THRESHOLD}触发)",
        ]
        if evidence.neg_score < 0:
            detail_parts.append(f"负例扣分: {evidence.neg_score:.1f}")
        return " | ".join(detail_parts)
    def _generate_recommendations(self: Self, result: TriggerTestSuiteResult,
                                   tp: int, fp: int, fn: int) -> list[str]:
        rules = (
            (result.accuracy < _RECOMMENDATION_THRESHOLD,
             f"触发准确率{result.accuracy:.0%}偏低，建议优化description和keywords"),
            (result.false_positive > 0,
             f"存在{result.false_positive}个误触发场景，建议补充NOT-for负例声明"),
            (result.false_negative > 0,
             f"存在{result.false_negative}个漏触发场景，建议在keywords中添加遗漏的触发词"),
            (result.precision < _RECOMMENDATION_THRESHOLD and tp + fp > 0,
             "精确率偏低，建议缩小触发范围，减少模糊匹配"),
            (result.recall < _RECOMMENDATION_THRESHOLD and tp + fn > 0,
             "召回率偏低，建议扩展同义词覆盖，特别是口语化表达"),
        )
        return [message for hit, message in rules if hit]
_DOMAIN_NEGATIVE_RECOMMENDATIONS = {
    "docx": ["纯文本编辑(无格式需求)", "PDF转换", "代码文件"],
    "xlsx": ["纯数据查询(无表格操作)", "图表绘制", "数据库操作"],
    "pptx": ["单页图片", "文档排版", "视频制作"],
    "pdf": ["Word编辑", "Excel分析", "图片处理"],
    "browser": ["本地文件操作", "系统命令", "代码编写"],
    "code": ["文档编辑", "表格处理", "网页浏览"],
    "image": ["视频处理", "音频处理", "文档编辑"],
}
@dataclass
class TriggerOptimizationResult:
    original_description: str = ""
    optimized_description: str | None = None
    attention_score: float = 0.0
    keyword_coverage: float = 0.0
    negative_defense_score: float = 0.0
    synonym_richness: float = 0.0
    user_language_match: float = 0.0
    overall_score: float = 0.0
    suggestions: list[str] = field(default_factory=list)
    recommended_keywords: list[str] = field(default_factory=list)
    recommended_negatives: list[str] = field(default_factory=list)
    trigger_command_score: float = 0.0
    scenario_boundary_score: float = 0.0
    specificity_score: float = 0.0
    multilingual_score: float = 0.0
ATTENTION_WEIGHT_KEYWORDS: set[str] = {
    "MUST", "ALWAYS", "REQUIRED", "Trigger when", "Activate if",
    "Use this when", "Call this if", "Invoke when", "加载当", "激活当",
    "必须使用", "必须调用", "在满足以下条件时",
    "Use this skill to", "Call this skill when", "This skill handles",
    "Invoke this skill for", "Apply this skill when",
    "触发此技能当", "调用此技能以", "使用此技能处理",
    "Tool for", "Function to", "Capability to", "Ability to",
    "Only for", "Exclusively for", "Strictly for", "仅限于", "专用于",
}
CN_ATTENTION_WORDS: set[str] = {
    "必须", "一定", "务必", "强制", "仅在", "仅限于", "只有",
    "当且仅当", "在满足", "以下条件", "触发条件", "激活条件",
    "当用户", "当用户要", "当用户想", "当用户需要", "如需",
}
NEGATIVE_INDICATORS: set[str] = {
    "NOT FOR", "DO NOT", "NEVER", "AVOID", "UNLESS", "EXCEPT",
    "不要", "禁止", "除非", "除外", "不属于", "不适用",
    "仅限于", "仅用于", "不负责", "不处理", "不要用于",
}
DOMAIN_TRIGGER_PATTERNS: dict[str, list[str]] = {
    "docx": ["word", "文档", "docx", "doc", "报告", "合同", "正文", "段落",
             "页眉", "页脚", "排版", "格式", "修订", "批注", "目录"],
    "xlsx": ["excel", "表格", "xlsx", "xls", "csv", "sheet", "单元格", "列", "行",
             "公式", "透视表", "图表", "数据", "筛选", "排序"],
    "pptx": ["ppt", "幻灯片", "演示", "presentation", "slide", "放映", "模板",
             "母版", "动画", "演讲", "汇报"],
    "pdf": ["pdf", "扫描件", "ocr", "签名", "合并pdf", "拆分pdf", "水印",
            "提取文字", "转pdf", "pdf编辑"],
    "browser": ["网页", "网站", "浏览器", "打开网页", "访问", "抓取",
                "截图", "滚动", "点击", "爬取", "导航", "url"],
    "code": ["代码", "编程", "python", "脚本", "函数", "调试", "重构",
             "review", "pull request", "commit", "语法", "lint"],
    "data": ["数据", "清洗", "etl", "聚合", "统计", "分析", "可视化",
             "图表", "plot", "dataframe", "sql", "数据库"],
    "image": ["图片", "图像", "photo", "resize", "裁剪", "压缩", "格式转换",
              "水印", "滤镜", "调色", "分辨率"],
    "skill-management": ["skill", "技能", "创建技能", "优化技能", CAT_DISCOVERABILITY,
                         "可发现性", "元数据", "frontmatter"],
    "memory": ["记忆", "经验", "memory", "沉淀", "复盘", "固化",
               "持久化", "trace"],
    "security": ["安全", "security", "漏洞", "vulnerability", "诊断", "扫描",
                 "加密", "解密", "密钥", "凭证"],
    "contract": ["合同", "contract", "条款", "协议", "agreement", "报价",
                 "预算", "结算", "清单"],
}
def _keyword_presence(desc: str, keywords: list[str]) -> tuple[list[str], list[str]]:
    text = desc.lower()
    present: list[str] = []
    missing: list[str] = []
    seen: set[str] = set()
    for kw in keywords:
        normalized = normalize_text(kw).lower()
        if normalized in seen:
            continue
        seen.add(normalized)
        bucket = present if _form_hits(normalized, text) else missing
        bucket.append(kw)
    return present, missing
def _score_keyword_coverage(desc: str, keywords: list[str]) -> float:
    if not keywords:
        return 0.0
    present, missing = _keyword_presence(desc, keywords)
    total = len(present) + len(missing)
    return min(1.0, len(present) / total) if total else 0.0
def _score_user_language(desc: str) -> float:
    score = 0.0
    text = desc.lower()
    casual_patterns = [re.escape(marker) for marker in _COLLOQUIAL_CN_MARKERS]
    casual_patterns.extend([
        r"如何", r"how\s+(?:do|can|to)", r"i\s+(?:want|need)\s+to\b",
        r"i\s+would\s+like\b", r"help\s+me", r"can\s+you", r"please",
    ])
    hits = sum(1 for p in casual_patterns if re.search(p, text, re.IGNORECASE))
    score += min(hits * 0.5, 2.0)
    if re.search(r'[?？]', desc):
        score += 0.5
    if re.match(r'^(?:请|帮我|给我|创建|编辑|删除|检查|分析)', desc.strip()):
        score += 1.0
    return min(5.0, score) / 5.0
def _calc_overall(attention: float, negative: float,
                  coverage: float, synonym: float, user_lang: float) -> float:
    score = (
        attention / 10.0 * 0.30 +
        negative / 10.0 * 0.25 +
        coverage * 0.15 +
        synonym * 0.20 +
        user_lang * 0.10
    )
    return round(score * 10.0, 2)
_STRONG_TRIGGER_PATTERNS: tuple[str, ...] = (
    r"\b(?:trigger|activate|use|call|invoke|apply)\s+(?:when|if)\b",
    (r"\b(?:trigger|activate|use|call|invoke|apply)\s+this\s+"
     r"(?:(?:skill|tool|function)\s+)?(?:when|if|for|to)\b"),
    r"\bmust\s+use\b", r"\balways\s+use\b",
    r"必须调用", r"必须使用", r"激活当", r"加载当",
    r"(?:使用|调用|加载|激活|触发)\s*(?:本|此)\s*技能",
    r"在满足.*条件时", r"当且仅当",
)
def _has_strong_trigger(text: str) -> bool:
    return any(re.search(pattern, text, re.IGNORECASE) is not None
               for pattern in _STRONG_TRIGGER_PATTERNS)
def _score_attention(desc: str) -> float:
    score = 3.0
    text = desc.lower()
    score += 2.0 * _has_strong_trigger(text)
    counted = {kw for kw in ATTENTION_WEIGHT_KEYWORDS
               if keyword_matches(kw, text)}
    attention_hits = len(counted)
    attention_hits += sum(1 for kw in CN_ATTENTION_WORDS
                          if kw not in counted and kw in desc)
    score += min(attention_hits * 0.8, 3.0)
    counted_lower = {keyword.lower() for keyword in counted}
    uppercase_words = [
        word for word in re.findall(r'\b[A-Z]{3,}\b', desc)
        if word.lower() not in counted_lower
    ]
    score += min(len(uppercase_words) * 0.3, 1.5)
    return min(10.0, score)
def _score_negative_defense(desc: str) -> float:
    score = 2.0
    text = desc.lower()
    neg_hits = sum(1 for kw in NEGATIVE_INDICATORS if keyword_matches(kw, text))
    score += min(neg_hits * 1.5, 5.0)
    explicit_neg = [
        r"\bnot\s+(?:for|when|if|to)\b",
        r"(?:不要|禁止|请勿|不可|不能|不负责|不处理|不适用于)",
        r"\bdo\s+not\s+(?:use|call|trigger|invoke)\b",
        r"\bnever\s+(?:use|call|trigger)\b",
    ]
    for pattern in explicit_neg:
        if re.search(pattern, text, re.IGNORECASE):
            score += 2.0
            break
    return min(10.0, score)
def _synonym_group_forms(verb: str, synonyms: list[str]) -> list[str]:
    label = _ACTION_CN_LABELS.get(verb)
    if label is not None:
        return _ACTION_VERBS[label]
    return list(dict.fromkeys([verb, *synonyms]))
def _synonym_group_hits(
        combined: str) -> Iterator[tuple[str, list[str], list[str]]]:
    for verb, synonyms in VERB_SYNONYM_EXPANSION.items():
        forms = _synonym_group_forms(verb, synonyms)
        hits = [form for form in forms if _form_hits(form, combined)]
        if hits:
            yield verb, synonyms, hits
def _score_synonym_richness(desc: str, keywords: list[str]) -> float:
    combined = desc.lower() + " " + " ".join(keywords).lower()
    group_scores = [
        len(hits) / len(_synonym_group_forms(verb, synonyms))
        for verb, synonyms, hits in _synonym_group_hits(combined)
    ]
    if not group_scores:
        return 0.0
    return sum(group_scores) / len(group_scores)
_ATTENTION_ACTION_THRESHOLD = 5.0
_NEGATIVE_ACTION_THRESHOLD = 4.0
_SUGGESTION_RULES: tuple[tuple[str, float, str | None], ...] = (
    ("attention_score", _ATTENTION_ACTION_THRESHOLD,
     ("[注意力] 建议在description开头添加明确的触发引导，"
     "如 'Trigger this skill when...' 或 '当用户需要...时必须调用此技能'")),
    ("negative_defense_score", _NEGATIVE_ACTION_THRESHOLD,
     ("[负例防御] 建议添加'不适用于...'或'不要用于...'等声明，"
     "明确技能边界，减少误触发")),
    ("keyword_coverage", 0.5, None),
    ("synonym_richness", 0.3,
     ("[同义词] 建议扩展触发词覆盖，包含同一动作的多种口语表达，"
     "如'创建/新建/生成'、'检查/审查/校验'")),
    ("user_language_match", 0.3,
     ("[用户语言] 建议使用用户可能的原话作为触发关键词，"
     "如'帮我...'、'能不能...'、'how do I...'")),
)
def _generate_suggestions(result: TriggerOptimizationResult,
                          desc: str, keywords: list[str]) -> list[str]:
    keywords = normalize_keywords(keywords)
    suggestions: list[str] = []
    for score_field, threshold, message in _SUGGESTION_RULES:
        if getattr(result, score_field) >= threshold:
            continue
        text = message if message is not None else _keyword_gap_suggestion(
            desc, keywords)
        if text:
            suggestions.append(text)
    length_hint = _length_suggestion(desc)
    if length_hint:
        suggestions.append(length_hint)
    return suggestions
def _keyword_gap_suggestion(desc: str, keywords: list[str]) -> str | None:
    if not keywords:
        return ("[关键词] 未提供 keywords，关键词覆盖率无法评估，"
                "建议补充 1-3 个中英核心触发词")
    _present, missing = _keyword_presence(desc, keywords)
    if not missing:
        return None
    return (
        f"[关键词] 以下keywords未在description中体现: {missing[:5]}。"
        f"建议将核心关键词自然融入触发描述"
    )
def _length_suggestion(desc: str) -> str | None:
    word_count = len(desc.split())
    cn_chars = len(_CJK_SCOPE_RE.findall(desc))
    if word_count + cn_chars >= 20:
        return None
    return "[长度] description过短，建议至少20个有效字符以包含充分触发信息"
def _collect_domain_keyword_terms(domain_hint: str | None, combined: str) -> list[str]:
    resolved = resolve_domain_key(domain_hint, DOMAIN_TRIGGER_PATTERNS)
    if not resolved or resolved not in DOMAIN_TRIGGER_PATTERNS:
        return []
    return [term for term in DOMAIN_TRIGGER_PATTERNS[resolved]
            if not keyword_matches(term, combined)]
def _collect_synonym_terms(combined: str) -> list[str]:
    recommendations: list[str] = []
    for _verb, synonyms, _hits in _synonym_group_hits(combined):
        for syn in synonyms:
            if _form_hits(syn, combined) or syn in recommendations:
                continue
            recommendations.append(syn)
    return recommendations
def _infer_domain_hint(combined: str) -> str | None:
    # 单字指标（如 xlsx 的「行」「列」）会命中「进行」「列队」等无关文本，
    # 不能参与领域推断；多领域同时命中时按有效指标数取最高者，避免
    # 「进行安全诊断」被排在前面的 xlsx 抢走。
    best_domain: str | None = None
    best_hits = 0
    for domain, indicators in DOMAIN_TRIGGER_PATTERNS.items():
        hits = sum(
            1 for indicator in indicators
            if len(indicator) >= 2 and keyword_matches(indicator, combined))
        if hits > best_hits:
            best_domain, best_hits = domain, hits
    return best_domain
def _recommend_keywords(desc: str, skill_name: str,
                        domain_hint: str | None) -> list[str]:
    combined = (normalize_text(skill_name) + " " + normalize_text(desc)).lower()
    recommendations = _collect_domain_keyword_terms(
        domain_hint or _infer_domain_hint(combined), combined)
    for term in _collect_synonym_terms(combined):
        if term not in recommendations:
            recommendations.append(term)
    return recommendations[:15]
def _domain_negative_terms(combined: str, domain_hint: str | None) -> list[str]:
    hint = resolve_domain_key(domain_hint, _DOMAIN_NEGATIVE_RECOMMENDATIONS)
    if not hint or hint not in _DOMAIN_NEGATIVE_RECOMMENDATIONS:
        return []
    return [neg for neg in _DOMAIN_NEGATIVE_RECOMMENDATIONS[hint]
            if neg.lower() not in combined]
def _mutual_exclusion_terms(combined: str) -> list[str]:
    terms: list[str] = []
    has_edit = any(
        _form_hits(form, combined)
        for form in ("编辑", "修改", "edit", "modify", "revise", "update")
    )
    has_create = any(
        _form_hits(form, combined)
        for form in ("创建", "生成", "create", "generate", "build", "make")
    )
    if has_edit and not has_create:
        terms.append("创建新文件(应使用创建类技能)")
    if has_create and not has_edit:
        terms.append("编辑已有文件(应使用编辑类技能)")
    return terms
def _recommend_negatives(desc: str, skill_name: str,
                         domain_hint: str | None) -> list[str]:
    combined = (normalize_text(skill_name) + " " + normalize_text(desc)).lower()
    negatives = _domain_negative_terms(
        combined, domain_hint or _infer_domain_hint(combined))
    negatives.extend(_mutual_exclusion_terms(combined))
    return negatives[:8]
def _generate_optimized(desc: str, keywords: list[str],
                        result: TriggerOptimizationResult) -> str:
    optimized = desc.strip()
    if (result.attention_score < _ATTENTION_ACTION_THRESHOLD
            and not _has_strong_trigger(optimized)):
        core_action = _extract_core_action(keywords, optimized)
        if core_action:
            prefix = f"Trigger this skill when the user asks to {core_action}. "
        else:
            prefix = "Use this skill when the user needs to perform the related task. "
        optimized = prefix + optimized
    if result.negative_defense_score < _NEGATIVE_ACTION_THRESHOLD:
        negatives = result.recommended_negatives
        if negatives:
            neg_text = "NOT for: " + "; ".join(negatives[:3])
            head = optimized.rstrip(". 。")
            optimized = f"{head}. {neg_text}." if head else f"{neg_text}."
    return optimized.strip()
_EXTENDED_SCORE_FIELDS: tuple[tuple[str, str], ...] = (
    ("trigger_command_score", "has_trigger_command"),
    ("scenario_boundary_score", "has_scenario_boundary"),
    ("specificity_score", "specificity"),
    ("multilingual_score", "multilingual_coverage"),
)
def _extended_scores(description: str, keywords: list[str]) -> dict[str, float]:
    try:
        raw = compute_trigger_score(description, keywords)
        if not isinstance(raw, dict):
            logger.warning("trigger score 载荷非 dict: %r，按无扩展分处理",
                           type(raw).__name__)
            return {}
        scores = raw.get("scores", {})
        if not isinstance(scores, dict):
            logger.warning("trigger score 维度载荷非 dict: %r，按无扩展分处理",
                           type(scores).__name__)
            return {}
        extended: dict[str, float] = {}
        for output_name, source_name in _EXTENDED_SCORE_FIELDS:
            value = _optional_finite_float(scores.get(source_name))
            if value is not None:
                extended[output_name] = value
        return extended
    except Exception as _e:
        logger.warning("trigger score computation failed: %s", _e, exc_info=True)
        return {}
def _fuse_overall(base_score: float, extended: dict[str, float]) -> float:
    if not extended:
        return round(base_score, 2)
    extended_total = sum(extended.values()) * 10.0
    return round((base_score * 5 + extended_total) / (5 + len(extended)), 2)
def _extract_core_action(keywords: list[str], desc: str) -> str | None:
    keywords_text = " ".join(keywords or ()).lower()
    desc_lower = desc.lower()
    for verb, synonyms in VERB_SYNONYM_EXPANSION.items():
        forms = _synonym_group_forms(verb, synonyms)
        if (any(_form_hits(form, keywords_text) for form in forms)
                or any(_form_hits(form, desc_lower) for form in forms)):
            return verb
    return None
class TriggerOptimizer:
    def analyze(self: Self, description: str,
                keywords: list[str] | None = None,
                skill_name: str = "",
                domain_hint: str | None = None) -> TriggerOptimizationResult:
        description = normalize_text(description)
        skill_name = normalize_text(skill_name)
        if not isinstance(domain_hint, str):
            domain_hint = None
        keywords = normalize_keywords(keywords)
        result = TriggerOptimizationResult(original_description=description)
        result.attention_score = _score_attention(description)
        result.negative_defense_score = _score_negative_defense(description)
        result.keyword_coverage = _score_keyword_coverage(description, keywords)
        result.synonym_richness = _score_synonym_richness(description, keywords)
        result.user_language_match = _score_user_language(description)
        extended = _extended_scores(description, keywords)
        result.trigger_command_score = extended.get("trigger_command_score", 0.0)
        result.scenario_boundary_score = extended.get("scenario_boundary_score", 0.0)
        result.specificity_score = extended.get("specificity_score", 0.0)
        result.multilingual_score = extended.get("multilingual_score", 0.0)
        base_score = _calc_overall(
            result.attention_score, result.negative_defense_score,
            result.keyword_coverage, result.synonym_richness, result.user_language_match,
        )
        result.overall_score = _fuse_overall(base_score, extended)
        result.suggestions = _generate_suggestions(result, description, keywords)
        result.recommended_keywords = _recommend_keywords(description, skill_name, domain_hint)
        result.recommended_negatives = _recommend_negatives(description, skill_name, domain_hint)
        result.optimized_description = _generate_optimized(description, keywords, result)
        return result
def _mapping_skill_entries(mapping: dict) -> list[dict]:
    entries: list[dict] = []
    for name, meta in mapping.items():
        entry = dict(meta) if isinstance(meta, dict) else {}
        entry["name"] = name
        entries.append(entry)
    return entries
def _normalize_skills_data(skills_data: Any) -> list:
    if skills_data is None:
        return []
    if isinstance(skills_data, (list, tuple)):
        return list(skills_data)
    if isinstance(skills_data, dict):
        return [skills_data] if "name" in skills_data else _mapping_skill_entries(
            skills_data)
    if isinstance(skills_data, (str, bytes)):
        logger.warning("_normalize_skills_data: 形态 %r 非清单，归空处理",
                     type(skills_data).__name__)
        return []
    try:
        return list(skills_data)
    except TypeError:
        logger.warning("_normalize_skills_data: 不可迭代（%s），归空处理",
                     type(skills_data).__name__)
        return []
def batch_analyze_triggers(skills_data: list) -> list:
    skills_data = _normalize_skills_data(skills_data)
    optimizer = TriggerOptimizer()
    results = []
    for item in skills_data:
        if not isinstance(item, dict):
            logger.warning("batch_analyze_triggers: 跳过非 dict 项 %r", type(item).__name__)
            continue
        result = optimizer.analyze(
            description=item.get("description", ""),
            keywords=item.get("keywords", []),
            skill_name=item.get("name", ""),
            domain_hint=item.get("domain"),
        )
        results.append(result)
    return results
_LOW_SCORE_THRESHOLD = 5.0
def _build_low_score_rows(results: list, items: list) -> list[dict]:
    indexed_items = [
        (i, item) for i, item in enumerate(items) if isinstance(item, dict)]
    return [
        {
            "name": (normalize_str(item.get("name")) or f"skill_{i}"),
            "score": r.overall_score,
            "top_issue": r.suggestions[0] if r.suggestions else "无",
        }
        for r, (i, item) in zip(results, indexed_items, strict=True)
        if r.overall_score < _LOW_SCORE_THRESHOLD
    ]
def _collect_issue_counts(results: list) -> dict[str, int]:
    issue_counts: dict[str, int] = {}
    for r in results:
        for s in r.suggestions:
            key = s.split("]")[0] + "]" if "]" in s else s[:20]
            issue_counts[key] = issue_counts.get(key, 0) + 1
    return issue_counts
def _build_top_recommendations(issue_counts: dict) -> list[dict]:
    top_issues = sorted(
        issue_counts.items(), key=lambda x: (-x[1], str(x[0])))[:5]
    return [{"issue": k, "affected_count": v} for k, v in top_issues]
def generate_trigger_report(skills_data: list) -> dict:
    skills_data = _normalize_skills_data(skills_data)
    results = batch_analyze_triggers(skills_data)
    total = len(results)
    if total == 0:
        return {
            "total_skills": 0,
            "average_score": 0.0,
            "low_score_count": 0,
            "low_score_skills": [],
            "top_recommendations": [],
        }
    avg_score = sum(r.overall_score for r in results) / total
    low_rows = _build_low_score_rows(results, skills_data)
    return {
        "total_skills": total,
        "average_score": round(avg_score, 2),
        "low_score_count": len(low_rows),
        "low_score_skills": low_rows,
        "top_recommendations": _build_top_recommendations(_collect_issue_counts(results)),
    }
def _normalize_root_input(skills_root, fallback_hint: str) -> str | None:
    candidate = normalize_path_arg(skills_root)
    if isinstance(candidate, str):
        return candidate.strip()
    if skills_root is not None:
        logger.warning(
            "skills_root 类型 %s 非法（应为 str/PathLike），%s",
            type(skills_root).__name__, fallback_hint,
        )
    return None
def _resolve_skills_root(skills_root) -> Path | None:
    normalized = _normalize_root_input(skills_root, "按空扫描处理")
    if normalized is None or not normalized.strip():
        return None
    root = Path(normalized)
    try:
        _root_ok = root.is_dir()
    except (OSError, ValueError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'_resolve_skills_root:{type(_e).__name__}')
        _root_ok = False
    return root if _root_ok else None
def _collect_skill_md_files(root: Path) -> list[Path]:
    skill_md_list: list[Path] = []
    try:
        for skill_md in iter_matching_files(str(root), "SKILL.md"):
            skill_md_list.append(Path(skill_md))
    except OSError as e:
        logger.warning("目录遍历中断（保留已扫描部分）: %s: %s", root, e)
    return sorted(skill_md_list)
def _load_skill_entry(skill_md: Path) -> tuple[str, str] | None:
    try:
        content = read_skill_text(skill_md)
    except (OSError, UnicodeDecodeError) as e:
        logger.debug("文件读取失败（跳过）: %s: %s", skill_md, e)
        return None
    if "\ufffd" in content:
        logger.warning(
            "SKILL.md 解码含替换字符（非 UTF-8 且无编码声明），描述可能失真: %s",
            skill_md)
    name = read_frontmatter_skill_name(content, skill_md.parent.name)
    description = extract_description(content)
    if name and description:
        return name, description
    return None
def scan_skill_descriptions(skills_root: str | os.PathLike) -> dict[str, str]:
    root = _resolve_skills_root(skills_root)
    if root is None:
        return {}
    skills: dict[str, str] = {}
    for skill_md in _collect_skill_md_files(root):
        entry = _load_skill_entry(skill_md)
        if entry is None:
            continue
        name, description = entry
        if name in skills and skills[name] != description:
            logger.warning(
                "技能名 %r 在多个目录重复出现，忽略后扫描到的描述（%s）",
                name, skill_md,
            )
            continue
        skills[name] = description
    return skills
def normalize_root_str(skills_root) -> str:
    normalized = _normalize_root_input(skills_root, "按空路径处理")
    return "" if normalized is None else normalized
_GAP_CRITICAL_THRESHOLD = 0.8
_GAP_HIGH_THRESHOLD = 0.5
_GAP_MEDIUM_THRESHOLD = 0.3
_UNDEFINED_SCOPE = "未明确"
_SEVERITY_ORDER: dict[str, int] = {
    "critical": 0, "high": 1, "medium": 2, "low": 3}
def _normalized_gap_severity(gap: SemanticGap) -> str:
    return (gap.severity.strip().lower()
            if isinstance(gap.severity, str) else "")
def _gap_sort_key(gap: SemanticGap) -> tuple:
    severity = _normalized_gap_severity(gap)
    score = _finite_float(gap.gap_score)
    concept = gap.concept_name if isinstance(gap.concept_name, str) else ""
    return (_SEVERITY_ORDER.get(severity, len(_SEVERITY_ORDER)),
            -score, concept, str(gap.skill_a), str(gap.skill_b))
@dataclass
class ConceptDefinition:
    concept_name: str = ""
    skill_name: str = ""
    context: str = ""
    definition_hint: str = ""
    scope_keywords: set[str] = field(default_factory=set)
@dataclass
class SemanticGap:
    concept_name: str = ""
    skill_a: str = ""
    skill_b: str = ""
    definition_a: str = ""
    definition_b: str = ""
    gap_score: float = 0.0
    severity: str = "low"
    recommendation: str = ""
@dataclass
class SemanticConsistencyReport:
    skills_root: str = ""
    total_skills: int = 0
    semantic_gaps: list[SemanticGap] = field(default_factory=list)
    high_severity_gaps: list[SemanticGap] = field(default_factory=list)
    consistency_score: float = 0.0
    issues: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
    matching_conflicts: dict[str, Any] = field(default_factory=dict)
def _bounded_phrase(phrase: str) -> str:
    escaped = re.escape(phrase)
    if not phrase.isascii():
        return escaped
    return rf"(?<![a-z0-9_]){escaped}(?![a-z0-9_])"
_CONCEPT_CONTEXT_WINDOW = 80
_CONCEPT_CONTEXT_DELIMITER_RE = re.compile(
    r"[。！？!?；;，,\n]|(?<!\d)\.(?!\d)")
def _concept_context(text: str, match_start: int, match_end: int) -> str:
    window_start = max(0, match_start - _CONCEPT_CONTEXT_WINDOW)
    window_end = min(len(text), match_end + _CONCEPT_CONTEXT_WINDOW)
    prefix = text[window_start:match_start]
    suffix = text[match_end:window_end]
    previous = -1
    for boundary in _CONCEPT_CONTEXT_DELIMITER_RE.finditer(prefix):
        previous = boundary.start()
    following = _CONCEPT_CONTEXT_DELIMITER_RE.search(suffix)
    context_start = window_start + previous + 1
    context_end = match_end + following.start() if following else window_end
    return text[context_start:context_end]
class SemanticConsistencyValidator:
    AMBIGUOUS_CONCEPTS: ClassVar[dict[str, list[str]]] = {
        "code_context": ["代码上下文", "code context", "上下文", "完整代码", "源码"],
        "file_path": ["文件路径", "filepath", "path", "目录", "folder"],
        "document": ["文档", "document", "文件", "文本", "正文"],
        "data_range": ["数据范围", "range", "区间", "scope", "筛选条件"],
        "config": ["配置", "config", "设置", "参数", "选项", "options"],
        "result": ["结果", "result", "返回值", "输出", "output"],
        "input_text": ["输入", "input", "文本", "内容", "content"],
        "template": ["模板", "template", "模版", "样例", "示例"],
        "batch": ["批量", "batch", "批次", "批量处理", "列表"],
        "filter": ["过滤", "filter", "筛选", "条件", "criteria"],
    }
    SCOPE_INDICATORS: ClassVar[dict[str, list[str]]] = {
        "full": ["完整", "全部", "整体", "full", "entire", "whole", "complete", "所有"],
        "partial": ["部分", "局部", "片段", "partial", "segment", "snippet", "节选"],
        "summary": ["摘要", "概要", "总结", "summary", "overview", "brief"],
        "structured": ["结构化", "JSON", "字典", "对象", "schema", "structured", "dict"],
        "raw": ["原始", "raw", "原生", "未处理", "plain", "unformatted"],
    }
    def __init__(self: Self) -> None:
        self._ambiguous_concepts = self.AMBIGUOUS_CONCEPTS
        self._scope_indicators = self.SCOPE_INDICATORS
        self._ambiguous_lower: dict[str, tuple[str, ...]] = {
            key: tuple(alias.lower() for alias in aliases)
            for key, aliases in self._ambiguous_concepts.items()
        }
        self._scope_lower: dict[str, tuple[str, ...]] = {
            key: tuple(word.lower() for word in words)
            for key, words in self._scope_indicators.items()
        }
        self._alias_res: dict[str, tuple[tuple[str, re.Pattern[str]], ...]] = {
            key: tuple((alias, re.compile(_bounded_phrase(alias)))
                for alias in aliases)
            for key, aliases in self._ambiguous_lower.items()
        }
        self._scope_res: dict[str, tuple[re.Pattern[str], ...]] = {
            key: tuple(re.compile(_bounded_phrase(word))
                       for word in words)
            for key, words in self._scope_lower.items()
        }
    def validate(self: Self, skills: dict[str, str]) -> list[SemanticGap]:
        skills = self._normalize_skills(skills)
        all_concepts = self._collect_concepts(skills)
        return self._dedupe_max_gaps(all_concepts)
    def _normalize_skills(self: Self, skills) -> dict[str, str]:
        if skills is None:
            skills = {}
        elif not isinstance(skills, dict):
            logger.warning(
                "validate 入参 skills 类型 %s 非法，按空字典处理",
                type(skills).__name__,
            )
            skills = {}
        clean: dict[str, str] = {}
        for skill_name, text in skills.items():
            if not isinstance(skill_name, str):
                logger.warning(
                    "validate 入参含非 str 技能名（%s），已跳过该条",
                    type(skill_name).__name__,
                )
                continue
            if not isinstance(text, str):
                if text is not None:
                    logger.warning(
                        "技能 %s 的描述非 str 类型（%s），已跳过该条",
                        skill_name,
                        type(text).__name__,
                    )
                continue
            clean[skill_name] = text
        return clean
    def _collect_concepts(
        self: Self, skills: dict[str, str]
    ) -> dict[str, list[ConceptDefinition]]:
        all_concepts: dict[str, list[ConceptDefinition]] = {}
        for skill_name, text in skills.items():
            concepts = self._extract_concepts(skill_name, text)
            for concept_key, defs in concepts.items():
                all_concepts.setdefault(concept_key, []).extend(defs)
        return all_concepts
    def _dedupe_max_gaps(
        self: Self, all_concepts: dict[str, list[ConceptDefinition]]
    ) -> list[SemanticGap]:
        seen: dict[tuple[str, str, str], SemanticGap] = {}
        for concept, defs in all_concepts.items():
            self._compare_concept_pairs(concept, defs, seen)
        return sorted(seen.values(), key=_gap_sort_key)
    def _compare_concept_pairs(
        self: Self,
        concept: str,
        defs: list[ConceptDefinition],
        seen: dict[tuple[str, str, str], SemanticGap],
    ) -> None:
        for a, b in combinations(defs, 2):
            if a.skill_name == b.skill_name:
                continue
            gap = self._compare_definitions(concept, a, b)
            if gap.gap_score <= 0:
                continue
            key = (concept, gap.skill_a, gap.skill_b)
            prev = seen.get(key)
            if prev is None or gap.gap_score > prev.gap_score:
                seen[key] = gap
    def _extract_concepts(
        self: Self, skill_name: str, text: str
    ) -> dict[str, list[ConceptDefinition]]:
        definitions: dict[str, list[ConceptDefinition]] = {}
        text_lower = text.lower()
        for concept_key, alias_res in self._alias_res.items():
            starts: set[int] = set()
            for _alias, pattern in alias_res:
                for m in pattern.finditer(text_lower):
                    if m.start() in starts:
                        continue
                    starts.add(m.start())
                    context = _concept_context(text_lower, m.start(), m.end())
                    scope = self._infer_scope(context)
                    definition_hint = ("; ".join(scope) if scope
                                       else _UNDEFINED_SCOPE)
                    defs = definitions.setdefault(concept_key, [])
                    defs.append(
                        ConceptDefinition(
                            concept_name=concept_key,
                            skill_name=skill_name,
                            context=context,
                            definition_hint=definition_hint,
                            scope_keywords=set(scope),
                        )
                    )
        return definitions
    def _infer_scope(self: Self, context: str) -> list[str]:
        scopes = []
        context_lower = context.lower()
        for scope_type, patterns in self._scope_res.items():
            if any(pattern.search(context_lower) for pattern in patterns):
                scopes.append(scope_type)
        return scopes
    def _compare_definitions(
        self: Self, concept: str, a: ConceptDefinition, b: ConceptDefinition
    ) -> SemanticGap:
        gap = SemanticGap(
            concept_name=concept,
            skill_a=a.skill_name,
            skill_b=b.skill_name,
            definition_a=a.definition_hint,
            definition_b=b.definition_hint,
        )
        gap.gap_score = _scope_gap_score(a, b)
        gap.severity = _gap_severity(gap.gap_score)
        gap.recommendation = self._generate_gap_recommendation(
            concept, a, b, gap.gap_score
        )
        return gap
    def _generate_gap_recommendation(
        self: Self,
        concept: str,
        a: ConceptDefinition,
        b: ConceptDefinition,
        score: float,
    ) -> str:
        if score >= _GAP_CRITICAL_THRESHOLD:
            return f"严重语义断层: '{concept}' 在 '{a.skill_name}' 和 '{b.skill_name}' 中的定义几乎完全不同，Workflow 组合时必定出错"
        if score >= _GAP_HIGH_THRESHOLD:
            hints = [hint for hint in (a.definition_hint, b.definition_hint)
                     if hint and hint != _UNDEFINED_SCOPE]
            if len(hints) == 2:
                return (f"语义差异: '{concept}' 在两者中的范围定义不一致，"
                        f"建议统一为 '{hints[0]}' 或 '{hints[1]}'")
            if hints:
                return (f"语义差异: '{concept}' 仅在一侧声明了 "
                        f"'{hints[0]}'，建议另一侧补齐同类范围说明")
            return (f"语义差异: '{concept}' 两侧都未声明语义范围，"
                    f"建议补充完整/部分、原始/结构化等范围标注")
        return f"轻微差异: '{concept}' 的语义范围有细微差别，建议在 SKILL.md 中明确标注语义边界"
def _scope_set(definition: ConceptDefinition) -> set[str]:
    scope = definition.scope_keywords
    if isinstance(scope, (set, frozenset)):
        return set(scope)
    if isinstance(scope, (list, tuple)):
        return {item for item in scope if isinstance(item, str)}
    return set()
def _scope_gap_score(a: ConceptDefinition, b: ConceptDefinition) -> float:
    a_scope = _scope_set(a)
    b_scope = _scope_set(b)
    if a_scope and b_scope:
        return 1.0 - jaccard(a_scope, b_scope)
    if a_scope or b_scope:
        return 0.5
    return 0.0
def _gap_severity(score: float) -> str:
    if score >= _GAP_CRITICAL_THRESHOLD:
        return "critical"
    if score >= _GAP_HIGH_THRESHOLD:
        return "high"
    if score >= _GAP_MEDIUM_THRESHOLD:
        return "medium"
    return "low"
_EXPORT_GAP_LIMIT = 10
def export_semantic_gaps(
    report: SemanticConsistencyReport | None, output_path: str | None = None
) -> str:
    if not isinstance(report, SemanticConsistencyReport):
        if report is not None:
            logger.warning(
                "export_semantic_gaps 入参非 SemanticConsistencyReport: %r，"
                "降级空报告", report,
            )
        report = SemanticConsistencyReport(consistency_score=0)
    raw_gaps = report.semantic_gaps
    if not isinstance(raw_gaps, (list, tuple)):
        logger.warning(
            "export_semantic_gaps semantic_gaps 非列表（%s），按空处理",
            type(raw_gaps).__name__)
        raw_gaps = []
    valid_gaps = [gap for gap in raw_gaps if isinstance(gap, SemanticGap)]
    dropped = len(raw_gaps) - len(valid_gaps)
    if dropped:
        logger.warning(
            "export_semantic_gaps 跳过 %d 个非 SemanticGap 条目", dropped)
    gaps = sorted(valid_gaps, key=_gap_sort_key)
    data = {
        "skills_root": report.skills_root,
        "consistency_score": _finite_float(report.consistency_score),
        "high_severity_count": sum(
            1 for gap in gaps
            if _normalized_gap_severity(gap) in ("high", "critical")),
        "gaps_total": len(gaps),
        "gaps_truncated": len(gaps) > _EXPORT_GAP_LIMIT,
        "gaps": [
            {
                "concept": (g.concept_name
                            if isinstance(g.concept_name, str) else ""),
                "skill_a": str(g.skill_a),
                "skill_b": str(g.skill_b),
                "gap_score": _finite_float(g.gap_score),
                "severity": (g.severity if isinstance(g.severity, str)
                             else ""),
                "recommendation": (g.recommendation
                                   if isinstance(g.recommendation, str) else ""),
            }
            for g in gaps[: _EXPORT_GAP_LIMIT]
        ],
    }
    json_str = json.dumps(data, ensure_ascii=False, indent=2, default=str)
    out_path = _prepare_output_path(output_path, "export_semantic_gaps")
    if out_path is None:
        return json_str
    with guarded_open(out_path, "w", encoding="utf-8", newline="\n") as f:
        f.write(json_str)
    return json_str

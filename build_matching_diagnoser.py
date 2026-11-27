from __future__ import annotations  # noqa: I001
import copy
import logging
import os
import re
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from typing import Any
from jwsgj.build_skill_md_quality import NAME_REGEX
from jwsgj.build_text_frontmatter import (
    frontmatter_keywords,
    is_frontmatter_fence,
    locate_frontmatter_body_start,
    normalize_description_field,
    parse_frontmatter_fields,
    parse_skill_md_text,
)
from jwsgj.build_text_scoring import (
    EXTENSION_ALTERNATION,
    FILE_EXTENSION_PATTERN,
    GENERIC_EXTENSION_ALTERNATION,
    declared_extensions,
    score_to_grade,
)
from jwsgj.build_text_signals import (
    CODE_TOOL_INDICATORS,
    COLLOQUIAL_INTENT_PATTERNS,
    COLLOQUIAL_PATTERNS,
    FILE_FORMAT_SKILL_INDICATORS,
    FILE_SKILL_INDICATORS,
    NATURAL_BOUNDARY_PATTERNS,
    NEGATIVE_BOUNDARY_PATTERNS,
    STRUCTURE_ACTION_PATTERNS,
    STRUCTURE_TARGET_PATTERNS,
    STRUCTURE_TRIGGER_PATTERNS,
    TRIGGER_PATTERNS,
    VAGUE_WORDS_CN_ORDERED,
    VAGUE_WORDS_EN_ORDERED,
    compile_patterns,
    description_is_cjk_dominant,
    extract_capabilities,
    fenced_block_spans,
    find_missing_keywords,
    first_paragraph_issue,
    first_sentence,
    has_explicit_trigger_clause,
    has_name_explanation,
    mask_exclusion_context,
    matches_any,
    missing_action_target_signals,
    normalize_matching_keywords,
    normalize_name_field,
    opens_with_action_verb,
    opens_with_trigger_phrase,
    refs_without_condition,
    resource_dirs_for,
    resource_path_pattern,
    resource_reference_matches,
    unreferenced_redundant_docs,
    vague_word_spans,
)
from jwsgj.log_config import log_swallowed
_log = logging.getLogger(__name__)
__all__ = [
    'CAPTURE_RULES',
    'DESCRIPTION_HARD_RULES',
    'DESCRIPTION_MAX_LENGTH',
    'DESCRIPTION_MIN_LENGTH',
    'MATCHING_KNOWN_CHECKS',
    'CaptureDiagnoseReport',
    'CaptureRuleDiagnoser',
    'CaptureRuleViolation',
    'MatchingDiagnoseReport',
    'MatchingRuleDiagnoser',
    'MatchingRuleViolation',
    'RuleViolation',
    'SkillFullDiagnoseResult',
    'batch_diag_matching_rules',
    'diag_matching_rules_from_md',
    'diag_skill_full_pipeline',
    'get_capture_diagnoser',
    'get_diagnoser',
    'get_matching_hard_rules',
    'run_rule_checks',
    'shared_compute_score_and_grade',
]
DESCRIPTION_MIN_LENGTH = 30
DESCRIPTION_MAX_LENGTH = 3000
DESCRIPTION_HARD_RULES: list[dict] = [
    {
        "id": "DR-001",
        "name": "触发场景必须明确",
        "rule": "description 必须包含明确的触发条件从句（如 '当用户...' / 'Use this skill when...'），"
        "或以操作动词开头（如 '创建或编辑...'）",
        "severity": "critical",
        "check": "has_trigger_scenario",
    },
    {
        "id": "DR-002",
        "name": "核心能力必须枚举",
        "rule": "description 必须列出 10 个以上的具体能力（动词+对象格式）",
        "severity": "high",
        "check": "min_capabilities",
        "min_capabilities": 10,
    },
    {
        "id": "DR-003",
        "name": "排除范围必须声明",
        "rule": "description 应包含排除边界声明，告知 AI 什么情况下不应触发本技能。"
        "支持多种表达格式：'不适用于'/'NOT for'/'则不应触发'/'则不应使用本技能'/'则不属于本技能'/'If the main output is...' 等。",
        "severity": "medium",
        "check": "has_negative_boundary",
    },
    {
        "id": "DR-004",
        "name": "长度不宜过长",
        "rule": "description 长度建议在 30-3000 字符之间。"
        "过短的 description 无法提供足够的触发信息，"
        "过长的 description 会占用系统提示 token 且关键信息容易被淹没。"
        "多核心域技能（如代码工具集、全生命周期质量管控框架）合理长度可达 2000+ 字符。"
        "建议将核心触发条件放在前 200 字符内。",
        "severity": "low",
        "check": "length_range",
        "min_length": DESCRIPTION_MIN_LENGTH,
        "max_length": DESCRIPTION_MAX_LENGTH,
    },
    {
        "id": "DR-005",
        "name": "避免模糊词汇",
        "rule": "description 不应包含 'powerful'、'灵活的'、'各种' 等无信息量词汇",
        "severity": "medium",
        "check": "no_vague_words",
    },
    {
        "id": "DR-006",
        "name": "description 必须自足",
        "rule": "description 必须独立包含匹配所需的全部语义信息（操作动词+目标对象+触发条件）。"
        "keywords 列表不参与匹配阶段的选择决策（系统提示不注入 keywords），"
        "因此匹配信息绝不能依赖 keywords，必须在 description 中直接体现。",
        "severity": "critical",
        "check": "description_self_sufficient",
    },
    {
        "id": "DR-007",
        "name": "文件类型信号必须明确",
        "rule": "涉及特定文件格式的技能，description 中必须包含文件扩展名（如 .docx、.xlsx）",
        "severity": "critical",
        "check": "has_file_extension_signal",
    },
    {
        "id": "DR-008",
        "name": "用户口语表达建议覆盖",
        "rule": "description 应包含用户可能使用的口语化表达或意图描述（如 '帮我、我要、能不能'，"
        "或 '用户需要/用户要求…' 等），便于 Agent 在口语化请求下命中。",
        "severity": "low",
        "check": "has_colloquial_coverage",
    },
    {
        "id": "DR-009",
        "name": "name 应便于语义匹配",
        "rule": "技能名称应简短且具有强语义信号。文件操作类建议用扩展名（如 xlsx、docx），"
        "功能类建议用 2-4 词英文组合（如 data-pipeline、web-builder）。"
        "避免使用抽象缩写（如 abc-tool）或特殊命名，若必须使用则 description 需额外补偿。",
        "severity": "medium",
        "check": "name_matchability",
    },
    {
        "id": "DR-010",
        "name": "description 结构完整性",
        "rule": "description 应包含以下结构要素：操作动词（创建/编辑/分析/处理等）+ 目标对象"
        "（文件类型/功能领域）+ 触发条件。三要素齐全时可获得最高匹配率。",
        "severity": "high",
        "check": "description_structure",
    },
    {
        "id": "DR-011",
        "name": "排除边界的多种表达",
        "rule": "排除声明应使用自然语言，支持但不限于：'不适用于'/'NOT FOR'/'则不应触发'/'"
        "则不应使用本技能'/'若...则...' / 'Does not apply to' / 'not for non-' 等。",
        "severity": "low",
        "check": "negative_boundary_natural_language",
    },
]
_GENERIC_FILE_EXTENSION_RE = re.compile(
    r"\.[ \t]*(?:" + GENERIC_EXTENSION_ALTERNATION + r")(?![A-Za-z0-9])",
    re.IGNORECASE,
)
def get_matching_hard_rules() -> list[dict[str, Any]]:
    return copy.deepcopy(DESCRIPTION_HARD_RULES)
def _frontmatter_unclosed(content: str) -> bool:
    lines = content.split("\n")
    first = 0
    while first < len(lines) and not lines[first].strip():
        first += 1
    if first >= len(lines) or not is_frontmatter_fence(
            lines[first].lstrip("\ufeff").rstrip("\r")):
        return False
    return locate_frontmatter_body_start(lines) == 0
def _normalize_md_path(path: Any) -> str:
    if not isinstance(path, (str, bytes, os.PathLike)):
        return ""
    return os.fsdecode(os.fspath(path))
def _keyword_gap_violation(
    rule: dict[str, Any], description: str, keywords: list[str],
) -> MatchingRuleViolation | None:
    cjk_dominant = description_is_cjk_dominant(description)
    meaningful_kws = [
        kw for kw in keywords
        if len(kw) >= 2 and kw.isascii() != cjk_dominant
    ]
    if not meaningful_kws:
        return None
    missing_core = find_missing_keywords(description, meaningful_kws)
    if len(missing_core) <= len(meaningful_kws) / 2:
        return None
    return _violation(
        rule,
        f"keywords 中有 {len(missing_core)}/{len(meaningful_kws)} 个核心信号词"
        f"（{', '.join(missing_core[:5])}）未在 description 中体现。"
        " 匹配阶段 Agent 无法感知 keywords，这些语义信息必须在 description 中覆盖。",
        ", ".join(missing_core[:5]),
    )
def shared_compute_score_and_grade(
    passed: int,
    total: int,
    violations: list[Any],
    critical_weight: float = 25.0,
    high_weight: float = 10.0,
    medium_weight: float = 4.0,
) -> tuple[float, str]:
    if total == 0:
        return 0.0, "F"
    base = (passed / total) * 100.0
    weights = {
        "critical": critical_weight,
        "high": high_weight,
        "medium": medium_weight,
    }
    deductions = sum(
        weights.get(
            v.get("severity", "") if isinstance(v, dict)
            else getattr(v, "severity", ""),
            0.0,
        )
        for v in violations
    )
    score = max(0.0, min(100.0, base - deductions))
    return score, score_to_grade(score)
_SEVERITY_COUNT_FIELD: dict[str, str] = {
    "critical": "critical_count",
    "high": "high_count",
    "medium": "medium_count",
    "low": "low_count",
}
@dataclass
class RuleViolation:
    rule_id: str = ""
    rule_name: str = ""
    severity: str = ""
    description: str = ""
    suggestion: str = ""
    matched_text: str = ""
    def to_dict(self) -> dict[str, str]:
        return {
            "rule_id": self.rule_id,
            "rule_name": self.rule_name,
            "severity": self.severity,
            "description": self.description,
            "suggestion": self.suggestion,
            "matched_text": self.matched_text,
        }
@dataclass
class CaptureRuleViolation(RuleViolation):
    pass
def _rule_config_violation(
    rule: dict[str, Any], reason: str,
) -> RuleViolation:
    data = rule if isinstance(rule, dict) else {}
    return RuleViolation(
        rule_id=str(data.get("id") or ""),
        rule_name=str(data.get("name") or ""),
        severity="critical",
        description=reason,
        suggestion=("补齐规则分发表登记或修正 check 名后重跑诊断；"
                    "未登记检查按 critical 失败关闭处理。"),
        matched_text=str(data.get("check") or ""),
    )
def _fail_rule(report: Any, rule: dict[str, Any], reason: str) -> None:
    _log.warning("%s", reason)
    _record_rule_result(report, _rule_config_violation(rule, reason))
def _record_rule_result(report: Any, violation: RuleViolation | None) -> None:
    if violation is None:
        report.passed_rules += 1
        return
    report.violations.append(violation)
    report.failed_rules += 1
    count_field = _SEVERITY_COUNT_FIELD.get(violation.severity, "low_count")
    setattr(report, count_field, getattr(report, count_field) + 1)
def _resolve_check_spec(
    dispatch: Mapping[str, tuple[Any, tuple[str, ...]]],
    rule: dict[str, Any],
    label: str,
    hint: str,
) -> tuple[Any, tuple[str, ...]]:
    check_fn = rule.get("check")
    spec = dispatch.get(check_fn) if isinstance(check_fn, str) else None
    if spec is None:
        raise LookupError(
            f"未知的{label}检查函数 {check_fn!r} (rule={rule.get('id')})：{hint}"
        )
    return spec
def run_rule_checks(
    report: Any,
    rules: Any,
    known_checks: frozenset[str],
    check: Callable[[dict[str, Any]], RuleViolation | None],
    rule_label: str,
) -> None:
    for rule in rules:
        check_name = rule.get("check") if isinstance(rule, dict) else None
        if not isinstance(check_name, str) or check_name not in known_checks:
            rule_id = rule.get("id") if isinstance(rule, dict) else None
            _fail_rule(report, rule, (
                f"未知的{rule_label}检查函数 {check_name!r} "
                f"(rule={rule_id})，按 critical 失败关闭"))
            continue
        try:
            violation = check(rule)
        except LookupError as exc:
            log_swallowed(__name__, exc, context=f'{rule_label}:LookupError')
            _fail_rule(report, rule, (
                f"{rule_label}检查函数 {check_name!r} 执行期查找失败: {exc}"))
            continue
        except OSError as exc:
            _fail_rule(report, rule, (
                f"{rule_label}检查函数 {check_name!r} 执行期 I/O 失败: {exc}"))
            continue
        _record_rule_result(report, violation)
CAPTURE_RULES: list[dict[str, Any]] = [
    {
        "id": "CR-001",
        "name": "frontmatter 建议精简",
        "rule": "SKILL.md 的 YAML frontmatter 推荐只保留 name 和 description 字段。"
        "其他字段（keywords、version 等）不参与匹配阶段的选择决策，"
        "但开发者可根据需要添加。并非强制要求。",
        "severity": "low",
        "check": "frontmatter_fields_only",
        "allowed_fields": ["name", "description"],
        "exempt_fields": ["keywords", "tags", "version", "dependencies"],
    },
    {
        "id": "CR-002",
        "name": "name 命名规范",
        "rule": "技能名称应遵循以下规范："
        "(1) 只使用小写字母、数字和连字符；"
        "(2) 长度不超过 64 个字符；"
        "(3) 不含空格、大写字母或特殊字符；"
        "(4) 文件操作类建议用扩展名（如 xlsx、json）；"
        "(5) 功能类建议用连字符组合（如 data-pipeline、web-builder）。",
        "severity": "high",
        "check": "name_naming_convention",
        "max_length": 64,
    },
    {
        "id": "CR-003",
        "name": "正文行数参考",
        "rule": "SKILL.md 正文（frontmatter 之后的部分）行数不限，"
        "但超过 3500 行时应考虑在正文开头提供目录或分段指引，"
        "帮助 AI 快速定位所需内容。",
        "severity": "low",
        "check": "body_line_limit",
        "max_lines": 3500,
    },
    {
        "id": "CR-004",
        "name": "正文首段提供核心工作流",
        "rule": "SKILL.md 正文的第一段（frontmatter 结束后的首个段落）应快速提供核心工作流或执行方向。"
        "AI 读取正文后需要立即知道如何执行任务，而非先阅读大量背景介绍。"
        "首段应包含操作动词（步骤1、首先、使用...等），"
        "或以可执行代码块直接给出工具用法。",
        "severity": "medium",
        "check": "body_first_paragraph_workflow",
    },
    {
        "id": "CR-005",
        "name": "资源引用有加载条件说明",
        "rule": "正文中的资源引用（scripts/、references/、assets/ 文件）应附带加载条件说明。"
        "例如：'高级功能详见 references/advanced.md' 或 '需要OCR时使用 scripts/ocr.sh'。"
        "不应仅列出文件名而不说明何时使用。",
        "severity": "medium",
        "check": "resource_reference_conditions",
    },
    {
        "id": "CR-006",
        "name": "无冗余文档",
        "rule": "技能目录中不应包含冗余的辅助文档，如 README.md、CHANGELOG.md、"
        "QUICK_REFERENCE.md、INSTALLATION_GUIDE.md 等。"
        "技能应只保留 AI 执行任务所需的核心文件。",
        "severity": "low",
        "check": "no_redundant_docs",
        "redundant_patterns": [
            "README",
            "CHANGELOG",
            "CHANGES",
            "HISTORY",
            "QUICK_REFERENCE",
            "INSTALLATION",
            "SETUP",
            "UPGRADE",
            "MIGRATION",
            "CONTRIBUTING",
        ],
    },
    {
        "id": "CR-007",
        "name": "description 与正文一致性",
        "rule": "正文内容应与 description 中的声明保持一致。"
        "例如 description 中声明支持某种格式，但正文只处理另一种格式，"
        "则构成不一致。匹配阶段基于 description 选中技能后，"
        "正文无法交付承诺的能力会导致执行失败。",
        "severity": "high",
        "check": "description_body_consistency",
    },
]
@dataclass
class CaptureDiagnoseReport:
    skill_name: str = ""
    skill_path: str = ""
    total_rules: int = 0
    violations: list[CaptureRuleViolation] = field(default_factory=list)
    passed_rules: int = 0
    failed_rules: int = 0
    critical_count: int = 0
    high_count: int = 0
    medium_count: int = 0
    low_count: int = 0
    overall_score: float = 0.0
    grade: str = ""
    body_lines: int = 0
    frontmatter_keys: list[str] = field(default_factory=list)
    def to_dict(self) -> dict[str, Any]:
        return {
            "skill_name": self.skill_name,
            "skill_path": self.skill_path,
            "total_rules": self.total_rules,
            "passed_rules": self.passed_rules,
            "failed_rules": self.failed_rules,
            "critical_count": self.critical_count,
            "high_count": self.high_count,
            "medium_count": self.medium_count,
            "low_count": self.low_count,
            "overall_score": self.overall_score,
            "grade": self.grade,
            "body_lines": self.body_lines,
            "frontmatter_keys": list(self.frontmatter_keys),
            "violations": [v.to_dict() for v in self.violations],
        }
def _capture_violation(
    rule: dict[str, Any], suggestion: str, matched_text: str
) -> CaptureRuleViolation:
    return CaptureRuleViolation(
        rule_id=rule["id"],
        rule_name=rule["name"],
        severity=rule["severity"],
        description=rule["rule"],
        suggestion=suggestion,
        matched_text=matched_text,
    )
@dataclass(frozen=True)
class _CaptureDocContext:
    fm_keys: list[str]
    name: str
    body_text: str
    body_lines: int
    skill_md_path: str
    description: str
    doc_root: str
def _name_length_issue(name: str, max_len: int) -> str:
    return f"名称长度 {len(name)} 超过上限 {max_len}" if len(name) > max_len else ""
def _name_uppercase_issue(name: str) -> str:
    return "包含大写字母" if re.search(r"[A-Z]", name) else ""
def _name_space_issue(name: str) -> str:
    return "包含空格" if re.search(r"[\s]", name) else ""
def _name_special_char_issue(name: str) -> str:
    bad_chars = dict.fromkeys(re.findall(r"[^a-zA-Z0-9\-\s]", name))
    if not bad_chars:
        return ""
    return f"包含特殊字符: {', '.join(bad_chars)}"
_PLAIN_NAME_READABLE_MAX = 12
_GENERIC_MATCHING_NAME_SEGMENTS = frozenset({
    "abc", "agent", "assistant", "plugin", "skill", "tool", "tools",
})
def _semantic_hyphenated_name(name: str) -> bool:
    if not re.fullmatch(
            r"[a-z0-9]+(?:-[a-z0-9]+){1,3}", name, re.IGNORECASE):
        return False
    return any(
        len(part) > 1 and part not in _GENERIC_MATCHING_NAME_SEGMENTS
        for part in name.casefold().split("-")
    )
def _name_readability_issue(name: str) -> str:
    if (re.search(r"[\-]", name) or re.match(r"^[a-z]{2,6}$", name)
            or len(name) <= _PLAIN_NAME_READABLE_MAX):
        return ""
    return "名称较长且无连字符分隔，语义可读性差"
_NAME_ISSUE_CHECKS = (
    _name_uppercase_issue,
    _name_space_issue,
    _name_special_char_issue,
    _name_readability_issue,
)
_BARE_EXTENSION_RE = re.compile(
    r"(?<![A-Za-z0-9.])(?:" + EXTENSION_ALTERNATION + r")(?![A-Za-z0-9])",
    re.IGNORECASE,
)
def _normalize_bare_extensions(text: str) -> str:
    return _BARE_EXTENSION_RE.sub(lambda m: "." + m.group(0), text)
class CaptureRuleDiagnoser:
    def __init__(self) -> None:
        self._default_resource_pattern = resource_path_pattern(
            resource_dirs_for(""))
        self._resource_pattern_cache: dict[tuple[str, ...], re.Pattern[str]] = {}
    def diag(
        self, skill_md_path: str, description: str | None = None
    ) -> CaptureDiagnoseReport:
        report = CaptureDiagnoseReport(
            skill_name="",
            skill_path=str(skill_md_path),
            total_rules=len(CAPTURE_RULES),
        )
        try:
            skill_md_path = _normalize_diag_path(skill_md_path)
            report.skill_path = skill_md_path
            with open(skill_md_path, encoding="utf-8-sig") as f:
                content = f.read()
        except (OSError, TypeError, ValueError) as e:
            log_swallowed(
                __name__, e,
                context=f'CaptureRuleDiagnoser.diag:{type(e).__name__}')
            return _finalize_parse_error_report(report, e)
        return self._diag_content(
            content, skill_md_path, description, report=report)
    def _diag_content(
        self,
        content: str,
        skill_md_path: str | bytes | os.PathLike,
        description: str | None = None,
        report: CaptureDiagnoseReport | None = None,
    ) -> CaptureDiagnoseReport:
        if report is None:
            report = CaptureDiagnoseReport(
                skill_name="", skill_path=str(skill_md_path),
                total_rules=len(CAPTURE_RULES))
        try:
            skill_md_path = _normalize_diag_path(skill_md_path)
            report.skill_path = skill_md_path
        except (OSError, TypeError, ValueError) as e:
            log_swallowed(
                __name__, e,
                context=f'CaptureRuleDiagnoser._diag_content:{type(e).__name__}')
            return _finalize_parse_error_report(report, e)
        if _frontmatter_unclosed(content):
            exc = ValueError("frontmatter 未闭合（缺少结束标记 '---'）")
            log_swallowed(
                __name__, exc,
                context='CaptureRuleDiagnoser.diag:UnclosedFrontmatter')
            return _finalize_parse_error_report(report, exc)
        fm_keys, name, fm_description, body_text, body_lines = (
            self._parse_skill_md_full(content)
        )
        description = _normalize_diag_description(description, fm_description)
        report.skill_name = name
        report.frontmatter_keys = fm_keys
        report.body_lines = body_lines
        ctx = _CaptureDocContext(
            fm_keys=fm_keys, name=name, body_text=body_text,
            body_lines=body_lines, skill_md_path=skill_md_path,
            description=description,
            doc_root=_doc_root_of(skill_md_path),
        )
        self._run_all_checks(report, ctx)
        report.overall_score, report.grade = shared_compute_score_and_grade(
            report.passed_rules,
            report.total_rules,
            report.violations,
        )
        return report
    def _run_all_checks(
        self, report: CaptureDiagnoseReport, ctx: _CaptureDocContext
    ) -> None:
        def _check(rule: dict[str, Any]) -> CaptureRuleViolation | None:
            check, fields = _resolve_check_spec(
                _CAPTURE_DISPATCH, rule, "捕捉规则",
                "_CAPTURE_DISPATCH 与 _CAPTURE_KNOWN_CHECKS 失同步")
            return check(self, rule, *(getattr(ctx, field) for field in fields))
        run_rule_checks(
            report, CAPTURE_RULES, _CAPTURE_KNOWN_CHECKS, _check, "捕捉规则",
        )
    def _check_frontmatter_fields(
        self, rule: dict[str, Any], fm_keys: list[str]
    ) -> CaptureRuleViolation | None:
        allowed = set(rule["allowed_fields"])
        exempt = set(rule.get("exempt_fields") or ())
        extra_keys = sorted(set(fm_keys) - allowed - exempt)
        if not extra_keys:
            return None
        return _capture_violation(
            rule,
            f"frontmatter 包含额外字段: {', '.join(extra_keys)}。"
            " 这些字段不参与匹配阶段的选择决策（系统提示不注入 keywords），"
            " 但开发者可根据需要保留。并非强制要求精简。",
            ", ".join(extra_keys),
        )
    def _check_name_convention(
        self, rule: dict[str, Any], name: str
    ) -> CaptureRuleViolation | None:
        if not name:
            return _capture_violation(rule, "frontmatter 中缺少 name 字段", "(空)")
        max_len = rule["max_length"]
        issues = [msg for check in _NAME_ISSUE_CHECKS if (msg := check(name))]
        if not issues and not NAME_REGEX.match(name):
            issues.append(
                "名称必须由小写字母/数字段组成，连字符只能分隔非空语段"
            )
        length_issue = _name_length_issue(name, max_len)
        if length_issue:
            issues.insert(0, length_issue)
        if not issues:
            return None
        return _capture_violation(
            rule,
            f"技能名称 '{name}' 存在以下问题: {'; '.join(issues)}。"
            " 建议使用小写+连字符格式（如 data-processor），"
            " 文件操作类用格式名（如 json、xlsx）。",
            f"{name} ({len(name)}字符)",
        )
    def _check_body_line_limit(
        self, rule: dict[str, Any], body_lines: int
    ) -> CaptureRuleViolation | None:
        max_lines = rule["max_lines"]
        if body_lines <= max_lines:
            return None
        return _capture_violation(
            rule,
            f"正文 {body_lines} 行（参考线 {max_lines} 行）。"
            " 行数较多时建议在正文开头添加目录或分段指引，"
            " 帮助 AI 快速定位所需内容。正文行数本身不是限制条件。",
            f"{body_lines} 行",
        )
    def _check_first_paragraph(
        self, rule: dict[str, Any], body_text: str
    ) -> CaptureRuleViolation | None:
        issue = first_paragraph_issue(body_text)
        if issue is None:
            return None
        message, matched_text = issue
        return _capture_violation(rule, message, matched_text)
    def _resource_pattern_for(
        self, rule: dict[str, Any], doc_root: str,
    ) -> re.Pattern[str]:
        declared = tuple(
            item.strip() for item in (rule.get("resource_dirs") or ())
            if isinstance(item, str) and item.strip())
        names = declared or resource_dirs_for(doc_root)
        if not names:
            return self._default_resource_pattern
        pattern = self._resource_pattern_cache.get(names)
        if pattern is None:
            pattern = resource_path_pattern(names)
            self._resource_pattern_cache[names] = pattern
        return pattern
    def _check_resource_references(
        self, rule: dict[str, Any], body_text: str, doc_root: str,
    ) -> CaptureRuleViolation | None:
        block_spans = fenced_block_spans(body_text)
        matches = resource_reference_matches(
            body_text, block_spans, self._resource_pattern_for(rule, doc_root))
        if not matches:
            return None
        refs_without_context = refs_without_condition(
            body_text, matches, block_spans)
        if not refs_without_context:
            return None
        shown = ", ".join(refs_without_context[:5])
        return _capture_violation(
            rule,
            f"以下资源引用缺少加载条件说明: {shown}。"
            " 建议在引用处说明何时应读取该文件，例如："
            "'需要高级功能时，详见 references/advanced.md'。",
            shown,
        )
    def _check_redundant_docs(
        self, rule: dict[str, Any], skill_md_path: str, body_text: str,
    ) -> CaptureRuleViolation | None:
        skill_dir = _doc_root_of(skill_md_path)
        if not os.path.isdir(skill_dir):
            return None
        patterns = list(
            compile_patterns(tuple(rule.get("redundant_patterns") or []), True)
        )
        redundant = unreferenced_redundant_docs(
            skill_dir, os.path.basename(skill_md_path), body_text, patterns)
        if not redundant:
            return None
        return _capture_violation(
            rule,
            f"技能目录中存在未引用的辅助文档: {', '.join(redundant)}。"
            " 请确认这些文件未被其他入口引用且并非项目必需后，"
            "再决定是否移除，避免删除实际加载资源。",
            ", ".join(redundant),
        )
    def _check_desc_body_consistency(
        self, rule: dict[str, Any], description: str, body_text: str
    ) -> CaptureRuleViolation | None:
        if not description:
            return None
        desc_exts = declared_extensions(
            _normalize_bare_extensions(description),
            GENERIC_EXTENSION_ALTERNATION)
        body_exts = declared_extensions(
            _normalize_bare_extensions(body_text),
            GENERIC_EXTENSION_ALTERNATION)
        if not desc_exts:
            return None
        missing_in_body = sorted(desc_exts - body_exts)
        if not missing_in_body:
            return None
        return _capture_violation(
            rule,
            f"description 中声明处理 {', '.join(missing_in_body)} 文件，"
            " 但正文中未涉及这些格式的操作指导。"
            " 匹配阶段基于 description 选中技能后，"
            " 正文无法交付承诺的能力会导致执行失败。"
            " 建议在 description 中移除未实际支持的扩展名，"
            " 或在正文中补充对应格式的操作指导。",
            ", ".join(missing_in_body),
        )
    def _parse_skill_md_full(
        self, content: str
    ) -> tuple[list[str], str, str, str, int]:
        lines = content.split("\n")
        body_start = locate_frontmatter_body_start(lines)
        fm_keys: list[str] = []
        name = ""
        description = ""
        if body_start:
            first = 0
            while first < len(lines) and not lines[first].strip():
                first += 1
            fm_keys, name, description = parse_frontmatter_fields(
                lines[first + 1:body_start - 1])
        body_text = "\n".join(lines[body_start:])
        body_lines = len(body_text.splitlines())
        return fm_keys, name, description, body_text, body_lines
_CaptureCheck = Callable[..., "CaptureRuleViolation | None"]
_CAPTURE_DISPATCH: dict[str, tuple[_CaptureCheck, tuple[str, ...]]] = {
    "frontmatter_fields_only": (
        CaptureRuleDiagnoser._check_frontmatter_fields, ("fm_keys",)),
    "name_naming_convention": (
        CaptureRuleDiagnoser._check_name_convention, ("name",)),
    "body_line_limit": (
        CaptureRuleDiagnoser._check_body_line_limit, ("body_lines",)),
    "body_first_paragraph_workflow": (
        CaptureRuleDiagnoser._check_first_paragraph, ("body_text",)),
    "resource_reference_conditions": (
        CaptureRuleDiagnoser._check_resource_references,
        ("body_text", "doc_root")),
    "no_redundant_docs": (
        CaptureRuleDiagnoser._check_redundant_docs,
        ("skill_md_path", "body_text")),
    "description_body_consistency": (
        CaptureRuleDiagnoser._check_desc_body_consistency,
        ("description", "body_text")),
}
_CAPTURE_KNOWN_CHECKS = frozenset(_CAPTURE_DISPATCH)
_capture_diagnoser_instance = CaptureRuleDiagnoser()
def get_capture_diagnoser() -> CaptureRuleDiagnoser:
    return _capture_diagnoser_instance
def _normalize_diag_path(path: Any) -> str:
    normalized = _normalize_md_path(path)
    if not normalized:
        raise TypeError(f"无效的 SKILL.md 路径: {path!r}")
    return normalized
def _doc_root_of(skill_md_path: str) -> str:
    return os.path.dirname(skill_md_path) or os.curdir
def _normalize_diag_description(description: str | None, fm_description: str) -> str:
    if description is None:
        return fm_description
    if not isinstance(description, str):
        return str(description) if description else ""
    return description
def _finalize_parse_error_report(
    report: CaptureDiagnoseReport, e: Exception
) -> CaptureDiagnoseReport:
    report.violations.append(_parse_error_violation(e))
    report.total_rules = 1
    report.failed_rules = 1
    report.critical_count = 1
    report.overall_score, report.grade = shared_compute_score_and_grade(
        report.passed_rules, report.total_rules, report.violations,
    )
    return report
def _parse_error_violation(e: Exception) -> CaptureRuleViolation:
    return CaptureRuleViolation(
        rule_id="PARSE-ERROR",
        rule_name="文件读取失败",
        severity="critical",
        description=f"SKILL.md 解析失败: {str(e)[:100]}",
        suggestion="检查文件路径、读取权限、编码（UTF-8）与 frontmatter "
                   "结束标记后重新诊断",
        matched_text="",
    )
_MatchingCheck = Callable[..., "MatchingRuleViolation | None"]
_MATCHING_DISPATCH: dict[str, tuple[_MatchingCheck, tuple[str, ...]]] = {}
@dataclass
class MatchingRuleViolation(RuleViolation):
    pass
def _violation(
    rule: dict[str, Any], suggestion: str, matched_text: str,
) -> MatchingRuleViolation:
    return MatchingRuleViolation(
        rule_id=rule["id"],
        rule_name=rule["name"],
        severity=rule["severity"],
        description=rule["rule"],
        suggestion=suggestion,
        matched_text=matched_text,
    )
@dataclass
class MatchingDiagnoseReport:
    skill_name: str = ""
    description: str = ""
    keywords: list[str] = field(default_factory=list)
    total_rules: int = 0
    violations: list[MatchingRuleViolation] = field(default_factory=list)
    passed_rules: int = 0
    failed_rules: int = 0
    critical_count: int = 0
    high_count: int = 0
    medium_count: int = 0
    low_count: int = 0
    overall_score: float = 0.0
    grade: str = ""
    suggestions: list[str] = field(default_factory=list)
    def to_dict(self) -> dict[str, Any]:
        return {
            "skill_name": self.skill_name,
            "description": self.description,
            "keywords": list(self.keywords),
            "total_rules": self.total_rules,
            "passed_rules": self.passed_rules,
            "failed_rules": self.failed_rules,
            "critical_count": self.critical_count,
            "high_count": self.high_count,
            "medium_count": self.medium_count,
            "low_count": self.low_count,
            "overall_score": self.overall_score,
            "grade": self.grade,
            "violations": [v.to_dict() for v in self.violations],
            "suggestions": list(self.suggestions),
        }
_SkillMdFields = tuple[str, str, list[str]]
def _read_skill_md_text(path: str | bytes | os.PathLike) -> str:
    with open(_normalize_md_path(path), encoding="utf-8-sig") as f:
        return f.read()
def _skill_md_fields_from_text(
    content: str, path: str | bytes | os.PathLike,
) -> _SkillMdFields:
    if not content:
        return "", "", []
    if _frontmatter_unclosed(content):
        _log.warning(
            "frontmatter 未闭合（缺少结束标记 '---'），按空 frontmatter 处理: %s",
            path,
        )
        return "", "", []
    meta = parse_skill_md_text(content)
    raw_name = meta.get("name")
    return (
        raw_name if isinstance(raw_name, str) else "",
        normalize_description_field(meta.get("description")),
        frontmatter_keywords(meta.get("keywords")),
    )
class MatchingRuleDiagnoser:
    def __init__(self) -> None:
        self._trigger_patterns = list(compile_patterns(tuple(TRIGGER_PATTERNS), True))
        self._negative_patterns = list(
            compile_patterns(tuple(NEGATIVE_BOUNDARY_PATTERNS), True)
        )
        self._colloquial_patterns = list(
            compile_patterns(tuple(COLLOQUIAL_PATTERNS), True)
        )
    def diag(
        self, skill_name: str, description: str, keywords: list[str] | None = None
    ) -> MatchingDiagnoseReport:
        keywords = normalize_matching_keywords(keywords)
        skill_name = normalize_name_field(skill_name)
        description = normalize_description_field(description)
        report = MatchingDiagnoseReport(
            skill_name=skill_name,
            description=description,
            keywords=keywords,
            total_rules=len(DESCRIPTION_HARD_RULES),
        )
        self._run_all_checks(report, description, keywords, skill_name)
        report.overall_score, report.grade = shared_compute_score_and_grade(
            report.passed_rules,
            report.total_rules,
            report.violations,
        )
        report.suggestions = _build_suggestions(report)
        return report
    def _run_all_checks(
        self, report: MatchingDiagnoseReport,
        description: str, keywords: list[str], skill_name: str,
    ) -> None:
        _context = {
            "description": description,
            "keywords": keywords,
            "skill_name": skill_name,
        }
        def _check(rule: dict[str, Any]) -> MatchingRuleViolation | None:
            check, fields = _resolve_check_spec(
                _MATCHING_DISPATCH, rule, "规则", "未在 _MATCHING_DISPATCH 登记")
            return check(self, rule, *(_context[field] for field in fields))
        run_rule_checks(
            report, DESCRIPTION_HARD_RULES, MATCHING_KNOWN_CHECKS,
            _check, "规则",
        )
    def parse_skill_md(self, path: str) -> tuple[str, str, list[str]]:
        try:
            content = _read_skill_md_text(path)
        except (OSError, UnicodeError, TypeError, ValueError) as e:
            _log.warning(
                "SKILL.md 读取/解析失败，frontmatter 按空处理: %s (%s: %s)",
                path, type(e).__name__, e,
            )
            return "", "", []
        return _skill_md_fields_from_text(content, path)
    def _check_trigger_scenario(
        self, rule: dict[str, Any], description: str
    ) -> MatchingRuleViolation | None:
        capability_text = mask_exclusion_context(description)
        if matches_any(self._trigger_patterns, capability_text):
            return None
        if has_explicit_trigger_clause(capability_text):
            return None
        if opens_with_action_verb(capability_text):
            return None
        return _violation(
            rule,
            "在 description 开头添加明确的触发场景，例如："
            "'当用户需要<操作><目标对象>时，使用本技能。'"
            " 或 'Use this skill when the user asks to <action> <target>.'",
            "",
        )
    def _check_min_capabilities(
        self, rule: dict[str, Any], description: str
    ) -> MatchingRuleViolation | None:
        capabilities = extract_capabilities(description)
        min_cap = rule["min_capabilities"]
        if len(capabilities) >= min_cap:
            return None
        return _violation(
            rule,
            f"当前仅列出 {len(capabilities)} 项能力（最低要求 {min_cap} 项）。"
            " 建议用 '动词+对象' 格式枚举更多具体能力，例如："
            "'包括：读取、编辑、转换目标文件，从零创建新对象，以及格式间的转换。'",
            ", ".join(capabilities) if capabilities else "(空)",
        )
    def _check_negative_boundary(
        self, rule: dict[str, Any], description: str
    ) -> MatchingRuleViolation | None:
        if matches_any(self._negative_patterns, description):
            return None
        return _violation(
            rule,
            "在 description 末尾添加排除声明，例如："
            "'不适用于与本技能无关的任务' 或 'Does not apply to unrelated tasks.'",
            "",
        )
    def _check_length_range(
        self, rule: dict[str, Any], description: str
    ) -> MatchingRuleViolation | None:
        length = len(description)
        min_len = rule["min_length"]
        max_len = rule["max_length"]
        if min_len <= length <= max_len:
            return None
        if length < min_len:
            return _violation(
                rule,
                f"description 长度 {length} 字符，低于最低 {min_len} 字符。匹配阶段信息不足会导致 AI 漏选。",
                f"length={length}",
            )
        return _violation(
            rule,
            f"description 长度 {length} 字符，超过最高 {max_len} 字符。过长会导致 Agent 注意力衰减，关键触发信息被淹没。",
            f"length={length}",
        )
    def _check_vague_words(
        self, rule: dict[str, Any], description: str
    ) -> MatchingRuleViolation | None:
        found = []
        for word in VAGUE_WORDS_EN_ORDERED:
            if vague_word_spans(word, description):
                found.append(word)
        for word in VAGUE_WORDS_CN_ORDERED:
            if vague_word_spans(word, description):
                found.append(word)
        if not found:
            return None
        return _violation(
            rule,
            f"发现模糊词汇: {', '.join(found[:5])}。"
            " 用具体的动词和对象替代，例如 '创建、编辑目标对象' 而非 '灵活的目标工具'。",
            ", ".join(found[:5]),
        )
    def _check_description_self_sufficient(
        self, rule: dict[str, Any], description: str, keywords: list[str]
    ) -> MatchingRuleViolation | None:
        gap = _keyword_gap_violation(rule, description, keywords)
        if gap is not None:
            return gap
        missing = missing_action_target_signals(description)
        if not missing:
            return None
        return _violation(
            rule,
            "description 缺少" + "、".join(missing) +
            "。必须同时包含操作动词（如 '创建、编辑、分析'）和目标对象"
            "（如 '文档、表格、代码'），匹配阶段 Agent 才能判断技能用途。",
            ", ".join(missing),
        )
    def _check_file_extension(
        self, rule: dict[str, Any], description: str
    ) -> MatchingRuleViolation | None:
        capability_text = mask_exclusion_context(description)
        has_document_target = matches_any(
            FILE_FORMAT_SKILL_INDICATORS, capability_text)
        is_file_skill = has_document_target or matches_any(
            FILE_SKILL_INDICATORS, capability_text)
        if not is_file_skill:
            return None
        if has_document_target:
            has_extension = FILE_EXTENSION_PATTERN.search(capability_text)
        else:
            if matches_any(CODE_TOOL_INDICATORS, capability_text):
                return None
            has_extension = (
                FILE_EXTENSION_PATTERN.search(capability_text)
                or _GENERIC_FILE_EXTENSION_RE.search(capability_text))
        if has_extension:
            return None
        return _violation(
            rule,
            "description 中未检测到明确的文件扩展名（如 .docx、.json）。"
            " 文件扩展名是 Agent 匹配阶段最强的硬信号，缺失会导致匹配率大幅下降。",
            "",
        )
    def _check_colloquial_coverage(
        self, rule: dict[str, Any], description: str
    ) -> MatchingRuleViolation | None:
        if matches_any(self._colloquial_patterns, description):
            return None
        if matches_any(COLLOQUIAL_INTENT_PATTERNS, description):
            return None
        return _violation(
            rule,
            "description 中未包含用户可能使用的口语化表达或对应的意图描述。"
            " 建议添加如 '用户要求生成、处理、下载' 或 '帮用户把代码检查一下' 等贴近用户的描述。"
            " 对于代码工具类技能，可以描述为'当用户需要检查、诊断、重构代码时'。",
            "",
        )
    def _check_name_matchability(
        self, rule: dict[str, Any], description: str, skill_name: str
    ) -> MatchingRuleViolation | None:
        sn = (skill_name or "").strip()
        if sn and (
            FILE_EXTENSION_PATTERN.fullmatch(sn)
            or re.fullmatch(GENERIC_EXTENSION_ALTERNATION, sn, re.IGNORECASE)
            or _semantic_hyphenated_name(sn)
        ):
            return None
        first_line = first_sentence(description)
        if opens_with_trigger_phrase(description) or opens_with_action_verb(description):
            return None
        if has_name_explanation(description):
            return None
        return _violation(
            rule,
            "技能名称若为抽象缩写，description 首句应以触发条件或操作动词开头，"
            "明确解释技能功能。例如：'当用户需要...时使用本技能'。"
            " 文件操作类技能建议直接用格式名命名（如 xlsx、json）。",
            first_line[:60] if first_line else "(空)",
        )
    def _check_description_structure(
        self, rule: dict[str, Any], description: str
    ) -> MatchingRuleViolation | None:
        capability_text = mask_exclusion_context(description)
        has_action = matches_any(STRUCTURE_ACTION_PATTERNS, capability_text)
        has_target = matches_any(STRUCTURE_TARGET_PATTERNS, capability_text)
        has_trigger = (
            matches_any(STRUCTURE_TRIGGER_PATTERNS, capability_text)
            or has_explicit_trigger_clause(capability_text)
        )
        missing: list[str] = []
        if not has_action:
            missing.append("操作动词")
        if not has_target:
            missing.append("目标对象")
        if not has_trigger:
            missing.append("触发条件")
        if not missing:
            return None
        return _violation(
            rule,
            f"description 缺少以下结构要素：{', '.join(missing)}。"
            " 建议采用三段式结构："
            "1) 触发条件（'当用户...' / 'Use this skill when...'）；"
            "2) 操作动词+目标对象（'创建、编辑目标对象'）；"
            "3) 排除边界（'不适用于...'）。",
            f"缺少: {', '.join(missing)}",
        )
    def _check_negative_boundary_natural_language(
        self, rule: dict[str, Any], description: str
    ) -> MatchingRuleViolation | None:
        has_natural_boundary = matches_any(
            (*NATURAL_BOUNDARY_PATTERNS, *NEGATIVE_BOUNDARY_PATTERNS), description)
        if has_natural_boundary:
            return None
        return _violation(
            rule,
            "排除声明建议使用自然语言而非技术性表达。推荐格式："
            "'不适用于...' / '若主要产出为...则不应触发本技能' / "
            "'Does not apply to...' / 'If the main output is...'",
            "",
        )
    def diag_from_skill_md(self, skill_md_path: str) -> MatchingDiagnoseReport:
        name, description, keywords = self.parse_skill_md(skill_md_path)
        return self.diag(name, description, keywords)
    def batch_diag(self, skills: list) -> list:
        results = []
        for skill in skills:
            if not isinstance(skill, dict):
                _log.warning("batch_diag: 跳过非 dict 项 %r",
                             type(skill).__name__)
                continue
            results.append(
                self.diag(
                    skill_name=skill.get("name", ""),
                    description=skill.get("description", ""),
                    keywords=skill.get("keywords", []),
                )
            )
        return results
_MATCHING_DISPATCH.update({
    "has_trigger_scenario": (
        MatchingRuleDiagnoser._check_trigger_scenario, ("description",)),
    "min_capabilities": (
        MatchingRuleDiagnoser._check_min_capabilities, ("description",)),
    "has_negative_boundary": (
        MatchingRuleDiagnoser._check_negative_boundary, ("description",)),
    "length_range": (
        MatchingRuleDiagnoser._check_length_range, ("description",)),
    "no_vague_words": (
        MatchingRuleDiagnoser._check_vague_words, ("description",)),
    "description_self_sufficient": (
        MatchingRuleDiagnoser._check_description_self_sufficient,
        ("description", "keywords")),
    "has_file_extension_signal": (
        MatchingRuleDiagnoser._check_file_extension, ("description",)),
    "has_colloquial_coverage": (
        MatchingRuleDiagnoser._check_colloquial_coverage, ("description",)),
    "name_matchability": (
        MatchingRuleDiagnoser._check_name_matchability,
        ("description", "skill_name")),
    "description_structure": (
        MatchingRuleDiagnoser._check_description_structure, ("description",)),
    "negative_boundary_natural_language": (
        MatchingRuleDiagnoser._check_negative_boundary_natural_language,
        ("description",)),
})
MATCHING_KNOWN_CHECKS: frozenset[str] = frozenset(_MATCHING_DISPATCH)
def _build_suggestions(report: MatchingDiagnoseReport) -> list[str]:
    suggestions: list[str] = []
    if report.critical_count > 0:
        suggestions.append(
            f"[紧急] 存在 {report.critical_count} 项严重违规，技能可能无法被 Agent 正确匹配"
        )
    if report.grade in ("D", "F"):
        suggestions.append(
            "description 质量不达标，建议参考同类高质量技能的 description 结构重写"
        )
    if report.high_count > 2:
        suggestions.append(
            "[通用] 建议 description 遵循三段式结构："
            "1) 触发场景（'当用户...'）；"
            "2) 能力枚举（'包括：...'）；"
            "3) 排除边界（'不适用于...'）"
        )
    return suggestions
_diagnoser_instance = MatchingRuleDiagnoser()
def get_diagnoser() -> MatchingRuleDiagnoser:
    return _diagnoser_instance
def diag_matching_rules_from_md(
    skill_md_path: str | bytes | os.PathLike
) -> MatchingDiagnoseReport:
    md_path = _normalize_md_path(skill_md_path)
    if not md_path or not os.path.isfile(md_path):
        _log.warning("diag_matching_rules_from_md: 文件不存在, path=%s", md_path)
        raise FileNotFoundError(f"文件不存在: {md_path}")
    try:
        return get_diagnoser().diag_from_skill_md(md_path)
    except Exception as e:
        _log.error("diag_matching_rules_from_md: 诊断异常, %s: %s",
                   type(e).__name__, str(e)[:120])
        raise
def batch_diag_matching_rules(skills: list) -> list:
    if not skills or not isinstance(skills, (list, tuple)):
        _log.warning("batch_diag_matching_rules: skills为空或类型无效")
        return []
    try:
        return get_diagnoser().batch_diag(skills)
    except Exception as e:
        _log.error("batch_diag_matching_rules: 批量诊断异常, %s: %s",
                   type(e).__name__, str(e)[:120])
        raise
@dataclass
class SkillFullDiagnoseResult:
    skill_name: str = ""
    matching_report: MatchingDiagnoseReport | None = None
    capture_report: CaptureDiagnoseReport | None = None
    overall_score: float = 0.0
    overall_grade: str = ""
    phase_scores: dict[str, float] = field(default_factory=dict)
    suggestions: list[str] = field(default_factory=list)
    def to_dict(self) -> dict[str, Any]:
        return {
            "skill_name": self.skill_name,
            "overall_score": self.overall_score,
            "overall_grade": self.overall_grade,
            "phase_scores": dict(self.phase_scores),
            "matching": self.matching_report.to_dict() if self.matching_report else None,
            "capture": self.capture_report.to_dict() if self.capture_report else None,
            "suggestions": list(self.suggestions),
        }
def _pipeline_suggestions(
    matching_report: MatchingDiagnoseReport,
    capture_report: CaptureDiagnoseReport,
) -> list[str]:
    suggestions: list[str] = []
    if matching_report.critical_count > 0:
        suggestions.append(
            f"[匹配-紧急] {matching_report.critical_count} 项 critical 违规，"
            "技能可能无法被 Agent 正确匹配"
        )
    if capture_report.critical_count > 0:
        suggestions.append(
            f"[捕捉-紧急] {capture_report.critical_count} 项 critical 违规，"
            "匹配后 Agent 可能无法正确执行"
        )
    if matching_report.grade in ("D", "F") and capture_report.grade in ("D", "F"):
        suggestions.append(
            "[全链路-警告] 匹配和捕捉阶段均不达标，建议完全重构 SKILL.md"
        )
    return suggestions
_MATCHING_PHASE_WEIGHT = 0.6
_CAPTURE_PHASE_WEIGHT = 0.4
def diag_skill_full_pipeline(
    skill_md_path: str | bytes | os.PathLike
) -> SkillFullDiagnoseResult:
    md_path = _normalize_md_path(skill_md_path)
    if not md_path or not os.path.isfile(md_path):
        raise FileNotFoundError(f"文件不存在: {md_path}")
    try:
        content = _read_skill_md_text(md_path)
    except (OSError, UnicodeError, TypeError, ValueError) as e:
        _log.warning(
            "SKILL.md 读取/解析失败，frontmatter 按空处理: %s (%s: %s)",
            md_path, type(e).__name__, e,
        )
        name, description, keywords = "", "", []
        log_swallowed(
            __name__, e,
            context=f'diag_skill_full_pipeline:{type(e).__name__}')
        capture_report = _finalize_parse_error_report(
            CaptureDiagnoseReport(
                skill_path=md_path, total_rules=len(CAPTURE_RULES)), e)
    else:
        name, description, keywords = _skill_md_fields_from_text(content, md_path)
        capture_report = get_capture_diagnoser()._diag_content(
            content, md_path, description)
    diagnoser = get_diagnoser()
    matching_report = diagnoser.diag(name, description, keywords)
    matching_score = matching_report.overall_score
    capture_score = capture_report.overall_score
    overall_score = (matching_score * _MATCHING_PHASE_WEIGHT
                     + capture_score * _CAPTURE_PHASE_WEIGHT)
    result = SkillFullDiagnoseResult(
        skill_name=name or os.path.basename(
            os.path.dirname(os.path.abspath(md_path))),
        matching_report=matching_report,
        capture_report=capture_report,
        overall_score=overall_score,
        overall_grade=score_to_grade(overall_score),
        phase_scores={
            "matching": matching_score,
            "capture": capture_score,
        },
    )
    result.suggestions = _pipeline_suggestions(matching_report, capture_report)
    return result

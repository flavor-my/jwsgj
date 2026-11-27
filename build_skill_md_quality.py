from __future__ import annotations

import ast
import io
import logging
import os
import re
import textwrap
import tokenize
import unicodedata
from collections import Counter
from collections.abc import Iterable, Iterator, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, ClassVar

from jwsgj.build_text_document import (
    _GENERIC_BOUNDARY_RE,
    _desc_length,
    iter_fence_lines,
    resolve_entry_document,
    strip_fenced_blocks,
)
from jwsgj.build_text_frontmatter import (
    UPLOAD_ALLOWED_FIELDS,
    UPLOAD_DESC_MAX_CHARS,
    detect_doc_profile_text,
    is_field_key_line,
    is_frontmatter_fence,
    load_frontmatter,
    locate_frontmatter,
    split_frontmatter_document,
)
from jwsgj.build_text_scoring import (
    _GENERIC_USAGE_RE,
    COLLOQUIAL_TRIGGER_WORDS,
    count_keyword_hits,
    score_to_grade,
)
from jwsgj.diag_guard_io import guarded_write, normalize_out_path
from jwsgj.diag_shared_source_core import count_lines
from jwsgj.diag_types_defs import (
    DocQualityIssue,
    PreCheckItem,
    PreinterventionResult,
    SubDimensionScore,
    finish_check,
    make_detail,
    normalize_text_param,
)
from jwsgj.diag_types_normalize import normalize_input, text_or_empty
from jwsgj.diag_types_vocab import (
    CAT_DISCOVERABILITY,
    DESC_MAX,
    MAX_SKILL_NAME_LENGTH,
    SEVERITY_BLOCKING,
    SEVERITY_INFO,
    SEVERITY_WARNING,
    SKILL_MD_LINE_LIMIT,
    SKILL_NAME_MIN_LEN,
    register_check_provider,
    register_review_provider,
)
from jwsgj.log_config import log_swallowed, safe_write_audit
from jwsgj.runtime_scope import normalize_skill_dir, normalize_text, skill_root_of

_log = logging.getLogger(__name__)
__all__ = [
    'GENERIC_WORKFLOW_RULES',
    'NAME_REGEX',
    'PROJECT_WORKFLOW_RULES',
    'SKILL_MD_MAX_LINES',
    'SkillDocPrecheck',
    'check_doc_skeleton',
    'check_frontmatter_compliance',
    'diag_upload',
    'diag_upload_u1u2',
    'enforce_workflow_doc',
    'skill_name_issues',
    'validate_create_input',
    'validate_workflow_doc',
]
NAME_MAX_LENGTH = MAX_SKILL_NAME_LENGTH
NAME_MIN_LENGTH = SKILL_NAME_MIN_LEN
NAME_REGEX = re.compile(r'^[a-z0-9](?:[a-z0-9]|-(?=[a-z0-9]))*\Z')
_DESC_MIN_LENGTH = 10
SKILL_MD_MAX_LINES = 500
VERSION_REGEX = re.compile(
    r"^\d+\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?"
    r"(?:\+[0-9A-Za-z.-]+)?\Z")
def skill_name_issues(skill_name: str) -> list[str]:
    issues: list[str] = []
    if len(skill_name) < SKILL_NAME_MIN_LEN:
        issues.append(f"技能名过短: {len(skill_name)} < {SKILL_NAME_MIN_LEN}")
    if len(skill_name) > MAX_SKILL_NAME_LENGTH:
        issues.append(
            f"技能名过长: {len(skill_name)} > {MAX_SKILL_NAME_LENGTH}")
    if not NAME_REGEX.match(skill_name):
        issues.append(f"技能名不符合 kebab-case 规范: '{skill_name}'")
    return issues
def validate_create_input(name: str, description: str) -> list:
    name = normalize_text(name)
    description = normalize_text(description)
    issues: list[str] = []
    if not name:
        issues.append("技能名不能为空")
    else:
        issues.extend(skill_name_issues(name))
    if not description.strip():
        issues.append("技能描述不能为空")
    return issues
@dataclass
class FrontmatterComplianceReport:
    skill_path: str
    name: str = ""
    name_valid: bool = False
    name_issues: list[str] = field(default_factory=list)
    description: str = ""
    description_valid: bool = False
    description_length: int = 0
    description_issues: list[str] = field(default_factory=list)
    directory_match: bool = False
    skill_md_lines: int = 0
    skill_md_ok: bool = True
    has_scripts_dir: bool = False
    has_references_dir: bool = False
    has_assets_dir: bool = False
    keywords_count: int = 0
    keywords_issues: list[str] = field(default_factory=list)
    version_valid: bool = True
    version_issues: list[str] = field(default_factory=list)
    total_score: float = 0.0
    grade: str = "F"
    all_issues: list[str] = field(default_factory=list)
    advisories: list[str] = field(default_factory=list)
    recommendations: list[str] = field(default_factory=list)
def _kebab_case_issues(name: str) -> list[str]:
    specific = (
        (" " in name, "name 不能包含空格"),
        ("_" in name, "name 不能包含下划线，请使用连字符"),
        (any(c.isupper() for c in name), "name 不能包含大写字母"),
    )
    issues = [message for failed, message in specific if failed]
    if issues:
        return issues
    if not NAME_REGEX.match(name):
        return [f"name '{name}' 不符合 kebab-case 格式（仅小写字母+数字+连字符）"]
    return []
def check_skill_name(name: str,
                     directory_name: str = "") -> tuple[bool, list[str], bool]:
    issues = []
    name = text_or_empty(name)
    if not name:
        issues.append("name 字段不能为空")
        return False, issues, False
    too_short = len(name) < NAME_MIN_LENGTH
    if too_short:
        issues.append(f"name 长度({len(name)})低于最小值({NAME_MIN_LENGTH})")
    if len(name) > NAME_MAX_LENGTH:
        issues.append(f"name 长度({len(name)})超过最大值({NAME_MAX_LENGTH})")
    kebab_issues = _kebab_case_issues(name)
    issues.extend(kebab_issues)
    valid = not too_short and len(name) <= NAME_MAX_LENGTH and not kebab_issues
    dir_match = False
    if directory_name:
        dir_match = (name == directory_name)
        if not dir_match:
            issues.append(f"name '{name}' 与目录名 '{directory_name}' 不一致")
    return valid, issues, dir_match
def _first_content_line_index(lines: list[str]) -> int:
    """首个非空行下标（兼容前导空行与 BOM），与 frontmatter 模块
    _FRONTMATTER_DOC_PREFIX 允许 "\\A\\ufeff?(?:[ \\t]*\\r?\\n)*" 的口径一致。"""
    for index, line in enumerate(lines):
        if index == 0:
            line = line.removeprefix("\ufeff")
        if line.strip():
            return index
    return len(lines)
def _frontmatter_has_field(lines: list[str], field_name: str) -> bool:
    start = _first_content_line_index(lines)
    if start >= len(lines) or not is_frontmatter_fence(lines[start]):
        return False
    for line in lines[start + 1:]:
        if is_frontmatter_fence(line):
            break
        if is_field_key_line(line, field_name):
            return True
    return False
def _description_length_issues(description: str) -> list[str]:
    length = _desc_length(description)
    if not length:
        return ["description 不能为空"]
    if length < _DESC_MIN_LENGTH:
        return [(f"description 过短({length}字符)，"
                 f"低于最低要求{_DESC_MIN_LENGTH}字符")]
    if length > DESC_MAX:
        return [f"description 过长({length}字符)，超过{DESC_MAX}上限"]
    return []
def _read_skill_doc_text(md_path: Any) -> tuple[str | None, BaseException | None]:
    try:
        raw = Path(md_path).read_bytes()
    except (OSError, TypeError, ValueError) as exc:
        return None, exc
    try:
        text = raw.decode("utf-8-sig")
    except UnicodeDecodeError as exc:
        return None, exc
    return text.replace("\r\n", "\n").replace("\r", "\n"), None
def _empty_frontmatter_meta() -> dict[str, Any]:
    return {"name": "", "description": "", "keywords": [], "version": ""}
def _read_skill_md_metadata(skill_dir: str) -> dict[str, Any]:
    md_path = resolve_entry_document(skill_dir)
    if md_path is None:
        return _empty_frontmatter_meta()
    content, read_exc = _read_skill_doc_text(md_path)
    if content is None:
        _log.warning("[best_practices] 读取 SKILL.md 元数据失败: %s", read_exc)
        return _empty_frontmatter_meta()
    fm_text, _body_start = locate_frontmatter(content)
    fm, reason, detail = load_frontmatter(fm_text)
    if fm is None:
        if reason != "missing":
            _log.warning("[best_practices] 解析 SKILL.md 元数据失败: %s %s",
                         reason, detail)
        return _empty_frontmatter_meta()
    name = fm.get("name", "")
    description = fm.get("description", "")
    raw_version = fm.get("version", "")
    version = (raw_version if isinstance(raw_version, str)
               else "" if raw_version is None else repr(raw_version))
    keywords = fm.get("keywords")
    if ("keywords" not in fm or keywords is None) and "tags" in fm:
        keywords = fm["tags"]
    return {
        "name": name if isinstance(name, str) else "",
        "description": description if isinstance(description, str) else "",
        "keywords": [] if keywords is None else keywords,
        "version": version,
    }
def _check_skill_md_file(skill_path: Path,
                         report: FrontmatterComplianceReport) -> None:
    skill_md_path = skill_path / "SKILL.md"
    if not skill_md_path.exists():
        report.skill_md_ok = False
        report.all_issues.append("SKILL.md 不存在")
        return
    content, read_exc = _read_skill_doc_text(skill_md_path)
    if content is None:
        _log.warning("[check_frontmatter_compliance] 读取SKILL.md失败: %s", read_exc)
        report.skill_md_ok = False
        report.all_issues.append(f"SKILL.md 读取失败: {read_exc}")
        return
    lines = content.splitlines()
    line_count = count_lines(content)
    report.skill_md_lines = line_count
    report.skill_md_ok = line_count <= SKILL_MD_MAX_LINES
    if not report.skill_md_ok:
        line_issue = _skill_md_line_issue(line_count)
        if line_count > SKILL_MD_LINE_LIMIT:
            report.all_issues.append(line_issue)
        else:
            report.advisories.append(line_issue)
    if not _frontmatter_has_field(lines, "name"):
        report.name_issues.append("SKILL.md frontmatter 缺少 name 字段")
        report.name_valid = False
    if not _frontmatter_has_field(lines, "description"):
        report.description_issues.append(
            "SKILL.md frontmatter 缺少 description 字段")
        report.description_valid = False
def _skill_md_line_issue(line_count: int) -> str:
    over_hard = line_count > SKILL_MD_LINE_LIMIT
    scope = (f"超过硬上限({SKILL_MD_LINE_LIMIT}行)" if over_hard
             else f"超过推荐线({SKILL_MD_MAX_LINES}行)")
    advice = ("必须提取同模块私有实现或把参考资料移出 SKILL.md" if over_hard
              else "建议渐进披露拆分或把参考资料移出 SKILL.md")
    return f"SKILL.md 行数({line_count}){scope}，{advice}"
def _check_version_format(version: str,
                          report: FrontmatterComplianceReport) -> None:
    if version and not VERSION_REGEX.match(version.strip()):
        report.version_valid = False
        report.version_issues.append(
            f"version '{version}' 不符合语义化版本格式（如 1.0.0）")
def _stripped_keywords(keywords: list) -> tuple[list[str], bool]:
    stripped = [k.strip() for k in keywords if isinstance(k, str)]
    has_blank = len(stripped) != len(keywords) or any(not k for k in stripped)
    return stripped, has_blank
def _duplicate_keywords(stripped: list[str]) -> list[str]:
    counts = Counter(k for k in stripped if k)
    return sorted(k for k, n in counts.items() if n > 1)
def _check_keywords_items(keywords: list,
                          report: FrontmatterComplianceReport) -> None:
    if not keywords:
        return
    stripped_kws, has_blank = _stripped_keywords(keywords)
    if has_blank:
        report.keywords_issues.append("keywords 存在空白项")
    dup_kws = _duplicate_keywords(stripped_kws)
    if dup_kws:
        report.keywords_issues.append(
            f"keywords 存在重复项: {', '.join(dup_kws[:5])}")
def _as_keyword_list(keywords: Any) -> list:
    if keywords is None:
        return []
    if isinstance(keywords, str):
        return [keywords]
    if isinstance(keywords, Mapping):
        return [keywords]
    if isinstance(keywords, Iterable) and not isinstance(
            keywords, (bytes, bytearray)):
        return list(keywords)
    return [keywords]
_INVALID_SKILL_DIR = "<invalid-skill-dir>"
def _normalize_skill_dir(skill_dir: object) -> str:
    normalized = normalize_out_path(skill_dir)
    return normalize_skill_dir(normalized) if normalized else ""
def _resolve_skill_path(skill_dir: str) -> tuple[Path, str]:
    path_text = _normalize_skill_dir(skill_dir)
    if not path_text:
        return Path(_INVALID_SKILL_DIR), ""
    skill_path = Path(path_text)
    return skill_path, skill_path.name
def _fill_structure_flags(report: FrontmatterComplianceReport,
                          skill_path: Path) -> None:
    report.has_scripts_dir = (skill_path / "scripts").is_dir()
    report.has_references_dir = (skill_path / "references").is_dir()
    report.has_assets_dir = (skill_path / "assets").is_dir()
def _finalize_compliance_report(report: FrontmatterComplianceReport) -> None:
    checks = (
        report.name_valid and not report.name_issues,
        report.description_valid,
        report.skill_md_ok,
        report.version_valid,
        not report.keywords_issues,
    )
    report.total_score = (sum(checks) / len(checks)) * 100
    report.grade = score_to_grade(report.total_score)
    if report.all_issues:
        report.recommendations = [f"修复: {issue}" for issue in report.all_issues]
    if report.advisories:
        report.recommendations.extend(
            f"建议: {advice}" for advice in report.advisories)
def check_frontmatter_compliance(skill_dir: str, name: str = "",
                                  description: str = "",
                                  keywords: list[str] | None = None,
                                  version: str = "") -> FrontmatterComplianceReport:
    name = text_or_empty(name)
    description = text_or_empty(description)
    version = text_or_empty(version)
    keywords_omitted = keywords is None
    skill_path, directory_name = _resolve_skill_path(skill_dir)
    if (skill_path != Path(_INVALID_SKILL_DIR)
            and (not name.strip() or not description.strip()
                 or keywords_omitted or not version.strip())):
        metadata = _read_skill_md_metadata(str(skill_path))
        if not name.strip():
            name = metadata["name"]
        if not description.strip():
            description = metadata["description"]
        if keywords_omitted:
            keywords = metadata["keywords"]
        if not version.strip():
            version = metadata["version"]
    keywords = _as_keyword_list(keywords)
    report = FrontmatterComplianceReport(
        skill_path=str(skill_path),
        name=name,
        description=description,
        description_length=_desc_length(description),
        keywords_count=len(keywords),
    )
    name_valid, name_issues, dir_match = check_skill_name(name, directory_name)
    report.name_valid = name_valid
    report.name_issues = name_issues
    report.directory_match = dir_match
    report.description_issues = _description_length_issues(description)
    report.description_valid = not report.description_issues
    _check_skill_md_file(skill_path, report)
    _fill_structure_flags(report, skill_path)
    _check_version_format(version, report)
    _check_keywords_items(keywords, report)
    report.all_issues.extend(name_issues)
    report.all_issues.extend(report.description_issues)
    report.all_issues.extend(report.version_issues)
    report.all_issues.extend(report.keywords_issues)
    _finalize_compliance_report(report)
    return report
_RESTRICTIVE_CONTEXT_KEYWORDS = (
    "禁止", "严禁", "禁用", "不得", "不可", "不能", "不要", "勿",
    "不支持", "非批量", "限制", "仅保留",
    "not for", "do not", "don't", "must not", "prohibit", "forbid",
    "not supported", "unsupported", "not applicable", "restrict",
    "non-batch", "no batch", "keep only",
)
_HTML_COMMENT_BLOCK_RE = re.compile(r"<!--[\s\S]*?(?:-->|\Z)")
def _declaration_scan_text(md: str) -> str:
    return strip_fenced_blocks(_HTML_COMMENT_BLOCK_RE.sub("", md))
def _declares_fragments(md: str,
                        groups: tuple[tuple[str, ...], ...]) -> bool:
    return any(group and all(fragment in md for fragment in group)
               for group in groups)
def _declares_step_guard(md: str, anchor: str,
                         groups: tuple[tuple[str, ...], ...]) -> bool:
    visible_md = _declaration_scan_text(md)
    return anchor in visible_md and _declares_fragments(visible_md, groups)
def _declares_entry(md: str, entry: str,
                    markers: tuple[str, ...]) -> bool:
    visible_md = _declaration_scan_text(md)
    return (entry in visible_md
            and any(marker in visible_md for marker in markers))
_COMMAND_WRAPPING_PREFIX_RE = re.compile(
    r"(?i)(?:\b(?:python[0-9.]*|py(?:\s+-[0-9][0-9A-Za-z.-]*)?)\s+-m\s+"
    r"|\b(?:uvx|uv\s+run|pipx\s+run|poetry\s+run|pdm\s+run)\s+)\Z")
_MARKDOWN_COMMAND_PREFIX_RE = re.compile(
    r"\A[ \t]*(?:[$>][ \t]*)?(?:(?:[-*+]|[0-9]+[.)])[ \t]+)?\Z")
def _is_command_start(before: str) -> bool:
    stripped = before.rstrip()
    if not stripped or stripped.endswith(("&&", "||", ";", "|", "`")):
        return True
    if _COMMAND_WRAPPING_PREFIX_RE.search(stripped + " "):
        return True
    return _MARKDOWN_COMMAND_PREFIX_RE.match(before) is not None
def _requires_command_flag(md: str, command: str, flag: str) -> bool:
    md = _declaration_scan_text(md)
    command_re = re.compile(
        rf"(?<![\w.-]){re.escape(command)}(?![\w.-])")
    flag_re = re.compile(rf"(?<![\w-]){re.escape(flag)}(?![\w-])")
    logical_line = ""
    declared = False
    for physical_line in [*md.splitlines(), ""]:
        current = physical_line.rstrip()
        continued = current.endswith("\\")
        if continued:
            current = current[:-1]
        logical_line = (f"{logical_line} {current}" if logical_line
                        else current)
        if continued:
            continue
        code_line = _code_seg_before_inline_comment(logical_line)
        if code_line.strip():
            logical_line = code_line
        matches = list(command_re.finditer(logical_line))
        for index, match in enumerate(matches):
            before = logical_line[:match.start()]
            tail = logical_line[match.end():
                      matches[index + 1].start()
                      if index + 1 < len(matches) else len(logical_line)]
            invocation = re.split(r"&&|\|\||[;|]", tail, maxsplit=1)[0]
            if _is_command_start(before):
                if before.rstrip().endswith("`"):
                    code_end = tail.find("`")
                    invocation = tail[:code_end] if code_end >= 0 else tail
                    if not invocation.strip():
                        continue
                if not flag_re.search(invocation):
                    return False
                declared = True
            elif flag_re.search(invocation):
                # 非命令上下文（如强制规则声明行）中命令与 flag 同现即视为已声明
                declared = True
        logical_line = ""
    return declared
_PROJECT_STEP_GUARD_POLICY = {
    "id": "D1",
    "anchor": "P0",
    "groups": (
        ("一个方法一个命令轮次",),
        ("一次bash调用仅执行一项独立任务",),
        ("逐步管线一次进程只推进一步", "批处理入口"),
    ),
    "declaration": (
        "> **P0 强制规则：逐步管线一次进程只推进一步；"
        "单进程连续推进只能使用批处理入口，禁止手工连续调用多个守卫步骤**"),
}
_PROJECT_RUFF_COMMAND = "ruff"
_PROJECT_RUFF_FLAG = "--no-cache"
_PROJECT_RUFF_DECLARATION = (
    "> **P0 强制规则：手动/旁路执行 ruff 时必须加 "
    "`--no-cache`（禁止在技能目录内产生 `.ruff_cache`）。**")
_PROJECT_STEP_ENTRY = "run_next_pipeline_step"
_PROJECT_STEP_ENTRY_MARKERS = ("统一入口", "逐项推进")
_PROJECT_ENTRY_DECLARATION = (
    "> **统一入口**：`run_next_pipeline_step`（每调用推进一项任务）。")
_PROJECT_LOOP_CALL = "run_single_method"
PROJECT_WORKFLOW_RULES = [
    {
        "id": "D1",
        "name": "P0强制规则声明",
        "description": "SKILL.md 必须声明 P0 逐步推进与批处理边界",
        "check": lambda md: _declares_step_guard(
            md, _PROJECT_STEP_GUARD_POLICY["anchor"],
            _PROJECT_STEP_GUARD_POLICY["groups"]),
        "fix": lambda md: _fix_p0_declaration(
            md, _PROJECT_STEP_GUARD_POLICY["declaration"],
            _PROJECT_STEP_GUARD_POLICY["anchor"],
            _PROJECT_STEP_GUARD_POLICY["groups"]),
        "fix_hint": "在顶部强制规则处添加 P0 强制规则声明",
    },
    {
        "id": "D2",
        "name": "命令缓存开关声明",
        "description": "手动/旁路执行 ruff 须加 --no-cache（防缓存污染）",
        "check": lambda md: _requires_command_flag(
            md, _PROJECT_RUFF_COMMAND, _PROJECT_RUFF_FLAG),
        "fix": lambda md: _fix_command_flag_declaration(
            md, _PROJECT_RUFF_COMMAND, _PROJECT_RUFF_FLAG,
            _PROJECT_RUFF_DECLARATION),
        "fix_hint": "在顶部强制规则处添加 ruff --no-cache 声明",
    },
    {
        "id": "R2",
        "name": "禁止循环调用",
        "description": "代码示例中禁止出现 for/while 循环调用指定入口函数",
        "check": lambda md: not _has_loop_pattern(md, _PROJECT_LOOP_CALL),
        "fix": lambda md: _fix_loop_patterns(md, _PROJECT_LOOP_CALL),
        "fix_hint": "删除代码示例中的 for/while 循环，改为逐行独立调用",
    },
    {
        "id": "R4",
        "name": "禁止批量模式章节",
        "description": "不得包含'批量执行'或'模式二'等批量模式章节",
        "check": lambda md: _no_batch_mode_section(md),
        "fix": lambda md: _fix_batch_mode_section(md),
        "fix_hint": "删除批量执行模式章节",
    },
    {
        "id": "R5",
        "name": "统一入口声明",
        "description": "声明的统一入口须标注为统一/逐项推进入口",
        "check": lambda md: _declares_entry(
            md, _PROJECT_STEP_ENTRY, _PROJECT_STEP_ENTRY_MARKERS),
        "fix": lambda md: _fix_entry_declaration(
            md, _PROJECT_STEP_ENTRY, _PROJECT_STEP_ENTRY_MARKERS,
            _PROJECT_ENTRY_DECLARATION),
        "fix_hint": "将统一入口标注为每次调用推进一项",
    },
]
def _has_closed_frontmatter(md: str) -> bool:
    lines = md.lstrip("\ufeff").splitlines()
    start = _first_content_line_index(lines)
    if start >= len(lines) or not is_frontmatter_fence(lines[start]):
        return True
    return any(is_frontmatter_fence(ln) for ln in lines[start + 1:])
def _has_balanced_fences(md: str) -> bool:
    in_fence = False
    for _line, state in iter_fence_lines(md.splitlines()):
        in_fence = state
    return not in_fence
GENERIC_WORKFLOW_RULES = [
    {
        "id": "G1",
        "name": "frontmatter 闭合",
        "description": "若文档以 --- 开头，必须有闭合的 --- 分隔行",
        "check": _has_closed_frontmatter,
        "fix_hint": "补全 frontmatter 的闭合 ---",
    },
    {
        "id": "G2",
        "name": "代码围栏闭合",
        "description": "Markdown 代码围栏数量必须成对",
        "check": _has_balanced_fences,
        "fix_hint": "补全未闭合的 ``` 代码围栏",
    },
]
_BATCH_MODE_KEYWORDS = (
    "模式二", "批量执行", "批量模式",
    "mode two", "mode 2", "batch execution", "batch mode",
)
_ATX_HEADING_RE = re.compile(r"^ {0,3}#{1,6}[ \t]+(.+?)\s*#*\s*$")
_SETEXT_HEADING_UNDERLINE_RE = re.compile(r"^ {0,3}(=+|-+)[ \t]*$")
_THEMATIC_BREAK_RE = re.compile(
    r"^ {0,3}(?:(?:\*[ \t]*){3,}|(?:-[ \t]*){3,}|(?:_[ \t]*){3,})$")
_SETEXT_NON_PARAGRAPH_RE = re.compile(
    r"^ {0,3}(?:#{1,6}[ \t]+|>|(?:[-+*]|\d+[.)])[ \t]+)")
def _heading_scan_states(lines: list[str]) -> list[bool]:
    states = [state for _, state in iter_fence_lines(lines)]
    start = _first_content_line_index(lines)
    if start < len(lines) and is_frontmatter_fence(lines[start]):
        for index in range(start, len(lines)):
            states[index] = True
            if index > start and is_frontmatter_fence(lines[index]):
                break
    return states
def _is_setext_text_line(lines: list[str], index: int,
                         fence_states: list[bool]) -> bool:
    if index < 0 or index >= len(lines) or fence_states[index]:
        return False
    line = lines[index]
    return bool(
        line.strip()
        and len(line) - len(line.lstrip(" ")) <= 3
        and _ATX_HEADING_RE.match(line) is None
        and _SETEXT_HEADING_UNDERLINE_RE.match(line) is None
        and _THEMATIC_BREAK_RE.match(line) is None
        and _SETEXT_NON_PARAGRAPH_RE.match(line) is None
    )
def _heading_map(lines: list[str],
                 fence_states: list[bool]) -> dict[int, tuple[int, str, int]]:
    headings: dict[int, tuple[int, str, int]] = {}
    for index, line in enumerate(lines):
        if fence_states[index]:
            continue
        atx = _ATX_HEADING_RE.match(line)
        if atx is not None:
            stripped = line.strip()
            level = len(stripped) - len(stripped.lstrip("#"))
            headings[index] = (level, atx.group(1).strip(), 1)
            continue
        underline = _SETEXT_HEADING_UNDERLINE_RE.match(line)
        if underline is None or not _is_setext_text_line(
                lines, index - 1, fence_states):
            continue
        start = index - 1
        while _is_setext_text_line(lines, start - 1, fence_states):
            start -= 1
        level = 1 if underline.group(1).startswith("=") else 2
        title = "\n".join(lines[start:index]).strip()
        headings[start] = (level, title, index - start + 1)
    return headings
def _is_batch_mode_title(title: str) -> bool:
    folded = title.strip().casefold()
    return (any(kw in folded for kw in _BATCH_MODE_KEYWORDS)
            and not any(kw in folded for kw in _RESTRICTIVE_CONTEXT_KEYWORDS))
def _no_batch_mode_section(md: str) -> bool:
    lines = md.split("\n")
    fence_states = _heading_scan_states(lines)
    return not any(_is_batch_mode_title(heading[1])
                   for heading in _heading_map(lines, fence_states).values())
def _scan_code_chars(code: str):
    in_quote = None
    idx = 0
    n = len(code)
    while idx < n:
        ch = code[idx]
        if in_quote:
            yield idx, ch, True
            if ch == "\\":
                if idx + 1 < n:
                    yield idx + 1, code[idx + 1], True
                idx += 2
                continue
            if ch == in_quote:
                in_quote = None
            idx += 1
            continue
        yield idx, ch, False
        if ch in ("'", '"'):
            in_quote = ch
        idx += 1
def _code_seg_before_inline_comment(seg: str) -> str:
    for idx, ch, in_string in _scan_code_chars(seg):
        if not in_string and ch == "#":
            return seg[:idx]
    return seg
_CALL_PATTERN_CACHE: dict[str, re.Pattern[str]] = {}
def _call_pattern(func_name: str) -> re.Pattern[str]:
    pattern = _CALL_PATTERN_CACHE.get(func_name)
    if pattern is None:
        pattern = re.compile(rf"\b{re.escape(func_name)}\s*\(")
        _CALL_PATTERN_CACHE[func_name] = pattern
    return pattern
def _calls_function(code: str, func_name: str) -> bool:
    pattern = _call_pattern(func_name)
    return any(not in_string and pattern.match(code, idx)
               for idx, _ch, in_string in _scan_code_chars(code))
def _structural_colon_index(code: str) -> int:
    depth = 0
    for idx, ch, in_string in _scan_code_chars(code):
        if in_string:
            continue
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif ch == ":" and depth == 0:
            return idx
    return -1
def _loop_body_indices(lines: list[str], loop_idx: int,
                       header_end: int | None = None):
    header = lines[loop_idx]
    indent = len(header) - len(header.lstrip())
    body_start = loop_idx + 1 if header_end is None else header_end + 1
    for j in range(body_start, len(lines)):
        stripped = lines[j].strip()
        if not stripped or stripped.startswith("#"):
            yield j
            continue
        if len(lines[j]) - len(lines[j].lstrip()) <= indent:
            break
        yield j
def _loop_else_indices(lines: list[str], loop_idx: int,
                       header_end: int, body_indices: list[int]) -> list[int]:
    next_index = body_indices[-1] + 1 if body_indices else header_end + 1
    if next_index >= len(lines):
        return []
    else_line = lines[next_index]
    indent = len(lines[loop_idx]) - len(lines[loop_idx].lstrip())
    else_indent = len(else_line) - len(else_line.lstrip())
    if (else_indent == indent
            and re.match(r"else\s*:", else_line.lstrip())):
        return [next_index, *_loop_body_indices(lines, next_index)]
    return []
class _LoopExecutionCallVisitor(ast.NodeVisitor):
    def __init__(self, func_name: str) -> None:
        self.func_name = func_name
        self.found = False
    def visit_Call(self, node: ast.Call) -> None:
        if ((isinstance(node.func, ast.Name) and node.func.id == self.func_name)
                or (isinstance(node.func, ast.Attribute)
                    and node.func.attr == self.func_name)):
            self.found = True
        self.generic_visit(node)
    def _visit_function_definition(self, node) -> None:
        for expression in node.decorator_list:
            self.visit(expression)
        arguments = node.args
        for expression in [*arguments.defaults, *arguments.kw_defaults]:
            if expression is not None:
                self.visit(expression)
        all_args = [
            *arguments.posonlyargs, *arguments.args, *arguments.kwonlyargs,
            *(arg for arg in (arguments.vararg, arguments.kwarg)
              if arg is not None),
        ]
        for arg in all_args:
            if arg.annotation is not None:
                self.visit(arg.annotation)
        if node.returns is not None:
            self.visit(node.returns)
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._visit_function_definition(node)
    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._visit_function_definition(node)
    def visit_Lambda(self, node: ast.Lambda) -> None:
        for expression in [*node.args.defaults, *node.args.kw_defaults]:
            if expression is not None:
                self.visit(expression)
def _window_calls_function(lines: list[str], loop_idx: int,
                           func_name: str) -> bool:
    header_end = _loop_header_end(lines, loop_idx)
    if header_end is None:
        return False
    header_lines = lines[loop_idx:header_end + 1]
    body_indices = list(_loop_body_indices(lines, loop_idx, header_end))
    else_indices = _loop_else_indices(
        lines, loop_idx, header_end, body_indices)
    region_indices = [*body_indices, *else_indices]
    source = textwrap.dedent("\n".join(
        [*header_lines, *(lines[j] for j in region_indices)]))
    async_wrapper = re.match(r"\s*async\s+(?:for|while)\b", source) is not None
    if async_wrapper:
        source = "async def _jwsgj_loop_example():\n" + textwrap.indent(
            source, "    ")
    try:
        tree = ast.parse(source)
    except (SyntaxError, ValueError):
        pass
    else:
        visitor = _LoopExecutionCallVisitor(func_name)
        root_statements = tree.body[0].body if async_wrapper else tree.body
        for statement in root_statements:
            visitor.visit(statement)
        return visitor.found
    code = _code_seg_before_inline_comment(header_lines[-1])
    colon = _structural_colon_index(code)
    if colon >= 0 and _calls_function(code[colon + 1:], func_name):
        return True
    return any(
        _calls_function(_code_seg_before_inline_comment(lines[j]), func_name)
        for j in region_indices
    )
def _is_loop_header(line: str) -> bool:
    stripped = line.strip()
    return ":" in stripped and re.match(r"(?:async\s+)?(?:for|while)\b", stripped) is not None
def _loop_header_end(lines: list[str], loop_idx: int) -> int | None:
    if _is_loop_header(lines[loop_idx]):
        return loop_idx
    stripped = lines[loop_idx].strip()
    if re.match(r"(?:async\s+)?(?:for|while)\b", stripped) is None:
        return None
    source = "\n".join(lines[loop_idx:]) + "\n"
    depth = 0
    try:
        tokens = tokenize.generate_tokens(io.StringIO(source).readline)
        for token in tokens:
            if token.type == tokenize.OP:
                if token.string in "([{":
                    depth += 1
                elif token.string in ")]}":
                    depth = max(0, depth - 1)
                elif token.string == ":" and depth == 0:
                    return loop_idx + token.start[0] - 1
            elif token.type == tokenize.NEWLINE and depth == 0:
                return None
    except (tokenize.TokenError, SyntaxError, ValueError):
        return None
    return None
def _has_loop_pattern(md: str, func_name: str) -> bool:
    lines = md.split("\n")
    return any(_loop_header_end(lines, i) is not None
               and _window_calls_function(lines, i, func_name)
               for i, line in enumerate(lines))
def _default_skill_md_path(start_dir: str | None = None) -> str:
    root = skill_root_of(start_dir or os.getcwd())
    return os.path.join(root, "SKILL.md") if root else ""
def _fix_loop_patterns(md: str, func_name: str) -> str:
    lines = md.split("\n")
    result = []
    i = 0
    while i < len(lines):
        if (_loop_header_end(lines, i) is not None
                and _window_calls_function(lines, i, func_name)):
            i = _comment_loop_block(lines, i, result, func_name)
            continue
        result.append(lines[i])
        i += 1
    return "\n".join(result)
def _comment_loop_block(lines: list[str], start: int,
                        result: list[str], func_name: str) -> int:
    indent = len(lines[start]) - len(lines[start].lstrip())
    result.append(" " * indent
                  + f"# [auto-fixed] 禁止循环调用 {func_name}，改为逐行独立调用：")
    result.append(" " * indent + "# " + lines[start].lstrip())
    header_end = _loop_header_end(lines, start)
    if header_end is None:
        header_end = start
    header_tail = list(range(start + 1, header_end + 1))
    body_indices = list(_loop_body_indices(lines, start, header_end))
    body = header_tail + body_indices
    body.extend(_loop_else_indices(lines, start, header_end, body_indices))
    for j in body:
        stripped = lines[j].strip()
        if stripped and not stripped.startswith("#"):
            result.append(" " * indent + "# " + stripped)
        else:
            result.append(lines[j])
    return body[-1] + 1 if body else start + 1
def _mask_batch_keywords(text: str) -> str:
    return (text.replace("模式二", "模式-二")
                .replace("批量执行", "批量-执行")
                .replace("批量模式", "批量-模式"))
def _html_comment(text: str) -> str:
    return "<!-- " + text.replace("-->", "-- >") + " -->"
def _comment_out_batch_body(
    lines: list[str], index: int, section_level: int,
) -> tuple[list[str], int]:
    commented: list[str] = []
    fence_states = _heading_scan_states(lines)
    headings = _heading_map(lines, fence_states)
    if index and fence_states[index - 1]:
        return commented, index
    while index < len(lines):
        body = lines[index]
        stripped = body.strip()
        heading = headings.get(index)
        if heading is not None and heading[0] <= section_level:
            break
        if stripped:
            indent = len(body) - len(body.lstrip())
            commented.append(
                " " * indent + _html_comment(_mask_batch_keywords(stripped)))
        else:
            commented.append(body)
        index += 1
    return commented, index
def _fix_batch_mode_section(md: str) -> str:
    lines = md.split("\n")
    fence_states = _heading_scan_states(lines)
    headings = _heading_map(lines, fence_states)
    result: list[str] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        heading = headings.get(i)
        if heading is None or not _is_batch_mode_title(heading[1]):
            result.append(line)
            i += 1
            continue
        section_level, title, heading_span = heading
        reason = ("禁止批量模式章节(标题)" if "模式二" in title
                  else "禁止批量模式章节(批量执行/批量模式)")
        indent = len(line) - len(line.lstrip())
        result.append(" " * indent + _html_comment(
            f"[auto-fixed] {reason}，改为逐方法独立执行："))
        for heading_line in lines[i:i + heading_span]:
            result.append(" " * indent + _html_comment(
                _mask_batch_keywords(heading_line.strip())))
        i += heading_span
        body, i = _comment_out_batch_body(lines, i, section_level)
        result.extend(body)
    return "\n".join(result)
def _find_safe_insert_index(lines: list[str]) -> int:
    search_start = 0
    fm_start = _first_content_line_index(lines)
    if fm_start < len(lines) and is_frontmatter_fence(lines[fm_start]):
        closed = False
        for i in range(fm_start + 1, len(lines)):
            if is_frontmatter_fence(lines[i]):
                search_start = i + 1
                closed = True
                break
        if not closed:
            return len(lines)
    for i, (line, in_fence) in enumerate(
            iter_fence_lines(lines[search_start:]), start=search_start):
        if not in_fence and line.startswith("## "):
            return i
    return search_start
def _insert_declaration(md: str, declaration: str) -> str:
    lines = md.split("\n")
    insert_idx = _find_safe_insert_index(lines)
    lines.insert(insert_idx, "")
    lines.insert(insert_idx, declaration)
    return "\n".join(lines)
def _fix_p0_declaration(md: str, declaration: str, anchor: str,
                        groups: tuple[tuple[str, ...], ...]) -> str:
    visible_md = _declaration_scan_text(md)
    if anchor in visible_md and (not groups or _declares_fragments(
            visible_md, groups)):
        return md
    return _insert_declaration(md, declaration)
def _fix_command_flag_declaration(md: str, command: str, flag: str,
                                  declaration: str) -> str:
    if _requires_command_flag(md, command, flag):
        return md
    # 声明只起提示作用：已在位仍违规说明命令行本身缺 flag，重复插入无法修复。
    if declaration in md:
        return md
    return _insert_declaration(md, declaration)
def _fix_entry_declaration(md: str, entry: str, markers: tuple[str, ...],
                           declaration: str) -> str:
    if _declares_entry(md, entry, markers):
        return md
    return _insert_declaration(md, declaration)
def _invalid_rule_violation(rule: Any, reason: str) -> dict:
    rule_id = ""
    if isinstance(rule, Mapping):
        raw_id = rule.get("id")
        rule_id = raw_id.strip() if isinstance(raw_id, str) else ""
    return {
        "rule_id": rule_id or "<invalid-rule>",
        "name": "非法工作流规则",
        "description": reason,
        "fix_hint": "传入含非空 id 与可调用 check 的规则映射",
        "error": reason,
    }
def _normalize_workflow_rules(rules: Any) -> tuple[list[dict], list[dict]]:
    if rules is None:
        return list(GENERIC_WORKFLOW_RULES), []
    if isinstance(rules, Mapping):
        candidates: list[Any] = [rules]
    elif isinstance(rules, (str, bytes, bytearray)):
        return [], [_invalid_rule_violation(
            rules, f"规则集不能是 {type(rules).__name__}")]
    else:
        try:
            candidates = list(rules)
        except TypeError:
            return [], [_invalid_rule_violation(
                rules, f"规则集不可迭代: {type(rules).__name__}")]
    normalized: list[dict] = []
    invalid: list[dict] = []
    for candidate in candidates:
        if not isinstance(candidate, Mapping):
            invalid.append(_invalid_rule_violation(
                candidate,
                f"规则条目必须是映射，实际 {type(candidate).__name__}"))
            continue
        rule = dict(candidate)
        rule_id = rule.get("id")
        if not isinstance(rule_id, str) or not rule_id.strip():
            invalid.append(_invalid_rule_violation(
                candidate, "规则缺少非空 str 的 id"))
            continue
        if not callable(rule.get("check")):
            invalid.append(_invalid_rule_violation(
                candidate, f"规则 {rule_id.strip()} 的 check 不可调用"))
            continue
        rule["id"] = rule_id.strip()
        for field_name in ("name", "description", "fix_hint"):
            value = rule.get(field_name)
            rule[field_name] = value.strip() if isinstance(value, str) else ""
        normalized.append(rule)
    rule_counts = Counter(rule["id"] for rule in normalized)
    if any(count > 1 for count in rule_counts.values()):
        unique_rules: list[dict] = []
        for rule in normalized:
            rule_id = rule["id"]
            if rule_counts[rule_id] > 1:
                invalid.append(_invalid_rule_violation(
                    rule, f"规则 id 重复: {rule_id}"))
                continue
            unique_rules.append(rule)
        normalized = unique_rules
    return normalized, invalid
def _invalid_report(skill_md_path: str, error: str) -> dict:
    return {
        "valid": False,
        "error": error,
        "checked_rules": 0,
        "passed": 0,
        "violations": [],
        "skill_md_path": skill_md_path,
    }
def _enforce_report(skill_md_path: str, before: dict, after: dict | None,
                    fixed: list[str], error: str | None = None) -> dict:
    tail = before if after is None else after
    report = {
        "valid_before": before["valid"],
        "valid_after": tail["valid"],
        "fixed": fixed,
        "violations_before": before["violations"],
        "violations_after": tail["violations"],
        "skill_md_path": skill_md_path,
    }
    if error is not None:
        report["error"] = error
    elif tail.get("error"):
        report["error"] = tail["error"]
    return report
def validate_workflow_doc(skill_md_path: str | None = None,
                          rules=None) -> dict:
    if skill_md_path is None:
        skill_md_path = _default_skill_md_path()
    if not skill_md_path:
        _log.warning("[WorkflowDoc] 未找到当前项目的 SKILL.md")
        return _invalid_report("", "未找到当前项目的 SKILL.md")
    if not os.path.exists(skill_md_path):
        _log.warning("[WorkflowDoc] SKILL.md 不存在: %s", skill_md_path)
        return _invalid_report(skill_md_path, f"SKILL.md 不存在: {skill_md_path}")
    md, read_exc = _read_skill_doc_text(skill_md_path)
    if md is None:
        _log.warning("[WorkflowDoc] SKILL.md 读取失败: %s (%s: %s)",
                     skill_md_path, type(read_exc).__name__, read_exc)
        return _invalid_report(
            skill_md_path,
            f"SKILL.md 读取失败: {skill_md_path} "
            f"({type(read_exc).__name__}: {read_exc})")
    active_rules, invalid_rules = _normalize_workflow_rules(rules)
    violations = list(invalid_rules)
    passed = 0
    for rule in active_rules:
        violation = _evaluate_workflow_rule(rule, md)
        if violation is None:
            passed += 1
        else:
            violations.append(violation)
    checked_rules = len(active_rules) + len(invalid_rules)
    if not checked_rules:
        _log.warning("[WorkflowDoc] 未提供可执行的工作流校验规则: %s",
                     skill_md_path)
        return _invalid_report(skill_md_path, "未提供可执行的工作流校验规则")
    _log.info(
        "[WorkflowDoc] 校验完成: valid=%s, passed=%d/%d, violations=[%s], file=%s",
        not violations, passed, checked_rules,
        ",".join(v["rule_id"] for v in violations) or "-", skill_md_path)
    return {
        "valid": not violations,
        "checked_rules": checked_rules,
        "passed": passed,
        "violations": violations,
        "skill_md_path": skill_md_path,
    }
def _evaluate_workflow_rule(rule: dict, md: str) -> dict | None:
    entry = {
        "rule_id": text_or_empty(rule.get("id")),
        "name": text_or_empty(rule.get("name")),
        "description": text_or_empty(rule.get("description")),
        "fix_hint": text_or_empty(rule.get("fix_hint")),
    }
    check = rule.get("check")
    if not callable(check):
        entry["error"] = "规则缺少可调用的 check"
        return entry
    try:
        if check(md):
            return None
    except Exception as e:  # noqa: BLE001
        _log.warning("工作流规则检查异常 [%s]: %s",
                     entry["rule_id"] or "?", e)
        entry["error"] = f"检查异常: {e}"
    return entry
def _apply_rule_fixes(md: str, violations: list[dict],
                      rules: list[dict]) -> tuple[str, list[str]]:
    fixed: list[str] = []
    rule_index = {rule["id"]: rule for rule in rules
                  if isinstance(rule, dict)
                  and isinstance(rule.get("id"), str)}
    for violation in violations:
        rule_id = (violation.get("rule_id")
                   if isinstance(violation, dict) else None)
        rule = rule_index.get(rule_id)
        if rule is None:
            continue
        fixer = rule.get("fix")
        if not callable(fixer):
            continue
        try:
            new_md = fixer(md)
        except Exception as e:  # noqa: BLE001
            _log.warning("工作流规则修复异常 [%s]: %s: %s",
                         rule_id, type(e).__name__, e)
            continue
        if new_md != md:
            md = new_md
            fixed.append(rule_id)
    return md, fixed
def _write_fixed_workflow_doc(md: str, skill_md_path: str,
                              fixed: list[str]) -> str | None:
    try:
        guarded_write(md, skill_md_path, preserve_form=True)
    except Exception as e:  # noqa: BLE001
        safe_write_audit("self_check_doc_fix_failed", file=skill_md_path,
                         fixed_rules=",".join(fixed),
                         reason=f"{type(e).__name__}: {e}")
        _log.warning(
            "[SelfCheck] SKILL.md 写入失败(临时文件已由守卫清理): %s (%s)",
            skill_md_path, e,
        )
        return f"SKILL.md 写入失败: {type(e).__name__}: {e}"
    safe_write_audit("self_check_doc_enforced", file=skill_md_path,
                     fixed_rules=",".join(fixed))
    _log.info("[WorkflowDoc] 自动修复已写盘: rules=[%s], file=%s",
                ",".join(fixed), skill_md_path)
    return None
def enforce_workflow_doc(skill_md_path: str | None = None,
                         auto_fix: bool = True, rules=None) -> dict:
    if isinstance(rules, Iterator) and not isinstance(rules, Mapping):
        rules = list(rules)
    if skill_md_path is None:
        skill_md_path = _default_skill_md_path()
    result_before = validate_workflow_doc(skill_md_path, rules=rules)
    if not skill_md_path:
        return _enforce_report(
            skill_md_path, result_before, None, [],
            error="未找到当前项目的 SKILL.md")
    if result_before["valid"] or not auto_fix:
        return _enforce_report(skill_md_path, result_before, None, [])
    active_rules, _invalid_rules = _normalize_workflow_rules(rules)
    if not active_rules:
        return _enforce_report(
            skill_md_path, result_before, None, [],
            error="未提供可执行的工作流校验规则")
    md, read_exc = _read_skill_doc_text(skill_md_path)
    if md is None:
        read_exc = read_exc or RuntimeError("SKILL.md 读取失败")
        log_swallowed(__name__, read_exc,
                      context=f'enforce_workflow_doc:{type(read_exc).__name__}')
        return _enforce_report(
            skill_md_path, result_before, None, [],
            error=f"SKILL.md 读取失败: {skill_md_path} "
                  f"({type(read_exc).__name__}: {read_exc})")
    md, fixed = _apply_rule_fixes(
        md, result_before["violations"], active_rules)
    if fixed:
        error = _write_fixed_workflow_doc(md, skill_md_path, fixed)
        if error is not None:
            return _enforce_report(
                skill_md_path, result_before, None, [], error=error)
    after = validate_workflow_doc(skill_md_path, rules=rules)
    return _enforce_report(skill_md_path, result_before, after, fixed)
_UPLOAD_DESC_MIN_CHARS = 20
def diag_upload(content: str, md_path: str,
                skill_dir: str = "") -> list[DocQualityIssue]:
    if not isinstance(content, str):
        content = ""
    issues: list[DocQualityIssue] = []
    issues.extend(_uv005_issues(count_lines(content)))
    fm, fm_issues = _parse_frontmatter(content)
    issues.extend(fm_issues)
    if fm is None:
        return issues
    description = fm.get("description")
    issues.extend(_check_upload_extra_fields(fm))
    issues.extend(_check_upload_name(fm.get("name"), md_path, skill_dir))
    issues.extend(_check_upload_desc_required(description))
    issues.extend(_check_upload_desc_format(description))
    return issues
def _upload_issue(rule_id: str, severity: str, description: str,
                  suggestion: str, location: str) -> DocQualityIssue:
    return DocQualityIssue(
        category="upload", rule_id=rule_id, severity=severity,
        description=description, suggestion=suggestion, location=location,
    )
def _parse_frontmatter(content):
    fm_text, _body_start = locate_frontmatter(content)
    fm, reason, detail = load_frontmatter(fm_text)
    if reason == "missing":
        return None, [_upload_issue("UV-001", "critical",
            "未找到有效的 YAML frontmatter",
            "添加 --- 包裹的 YAML frontmatter", "文件开头")]
    if reason == "no_yaml":
        _log.warning("[SkillDoc] PyYAML 未安装，frontmatter 合规检查降级为 UV-001 上报")
        return None, [_upload_issue("UV-001", "critical",
            "PyYAML 未安装，frontmatter 合规检查不可用",
            "安装 PyYAML（pip install pyyaml）后重新诊断",
            "frontmatter")]
    if reason == "parse_error":
        _log.warning("[SkillDoc] frontmatter YAML 解析失败（降级为 UV-001 上报）: %s", detail)
        return None, [_upload_issue("UV-001", "critical",
            f"YAML 解析失败: {detail[:80]}",
            "检查 description 中的特殊字符是否已正确转义，使用双引号包裹",
            "frontmatter")]
    if reason == "not_dict":
        return None, [_upload_issue("UV-001", "critical",
            "frontmatter 解析结果不是字典", "确认 YAML 格式正确", "frontmatter")]
    return fm, []
def _check_upload_extra_fields(fm: dict) -> list:
    issues: list[DocQualityIssue] = []
    extra = set(fm.keys()) - UPLOAD_ALLOWED_FIELDS
    if extra:
        issues.append(_upload_issue(
            "UV-002", "medium",
            f"frontmatter 含非标字段: "
            f"{', '.join(sorted(str(k) for k in extra))}",
            f"仅保留 {', '.join(sorted(UPLOAD_ALLOWED_FIELDS))} 字段",
            "frontmatter",
        ))
    return issues
def _uv005_issues(line_count: int) -> list:
    if line_count <= SKILL_MD_LINE_LIMIT:
        return []
    return [_upload_issue(
        "UV-005", "high",
        f"SKILL.md 行数 {line_count} 超过 {SKILL_MD_LINE_LIMIT} 行限制",
        "将详细内容拆分到 references/ 目录",
        "全文",
    )]
def _uv003_issues(raw_name) -> list:
    if raw_name is None:
        return [_upload_issue("UV-003", "critical",
            "frontmatter 缺少必填字段 'name'",
            "在 frontmatter 中添加 name: your-skill-name", "frontmatter")]
    if not isinstance(raw_name, str):
        return [_upload_issue("UV-003", "critical",
            f"name 字段类型错误（{type(raw_name).__name__}），应为字符串",
            "将 name 改为字符串类型", "frontmatter → name")]
    name = raw_name.strip()
    if not name:
        return [_upload_issue("UV-003", "critical",
            "name 字段为空字符串",
            "将 name 设置为 kebab-case 技能名，如: my-skill-name",
            "frontmatter → name")]
    if len(name) < SKILL_NAME_MIN_LEN:
        return [_upload_issue("UV-003", "critical",
            f"name 过短（{len(name)} 字符），至少 {SKILL_NAME_MIN_LEN} 字符",
            f"name 至少 {SKILL_NAME_MIN_LEN} 字符，如: my-skill",
            "frontmatter → name")]
    return []
_HYPHEN_BOUNDARY_RE = re.compile(r"-{2,}")
def _strip_hyphen_boundaries(name: str) -> str:
    return _HYPHEN_BOUNDARY_RE.sub("-", name).strip("-")
def _uv004_issues(raw_name: str) -> list:
    if NAME_REGEX.match(raw_name):
        return []
    if NAME_REGEX.match(_strip_hyphen_boundaries(raw_name)):
        return []
    return [_upload_issue(
        "UV-004", "high",
        f"name '{raw_name}' 不符合 kebab-case 格式",
        "使用小写字母和连字符，如: my-skill-name",
        "frontmatter → name",
    )]
def _skill_dir_name(md_path) -> str:
    if not isinstance(md_path, (str, os.PathLike)) or not md_path:
        return ""
    raw_path = os.fspath(md_path)
    if not isinstance(raw_path, str) or not raw_path.strip():
        return ""
    abs_path = os.path.normpath(os.path.abspath(raw_path))
    if os.path.isdir(abs_path):
        return os.path.basename(abs_path)
    return os.path.basename(os.path.dirname(abs_path))
def _uv007_issues(raw_name: str, md_path) -> list:
    dir_name = _skill_dir_name(md_path)
    if not dir_name or raw_name == dir_name:
        return []
    return [_upload_issue(
        "UV-007", "high",
        f"目录名 '{dir_name}' 与 name '{raw_name}' 不一致",
        f"将目录名改为 '{raw_name}' 或将 name 改为 '{dir_name}'",
        "frontmatter → name",
    )]
def _uv006_issues(raw_name: str) -> list:
    if len(raw_name) <= MAX_SKILL_NAME_LENGTH:
        return []
    return [_upload_issue(
        "UV-006", "high",
        f"name 过长（{len(raw_name)} 字符）。最大长度为 {MAX_SKILL_NAME_LENGTH} 字符",
        f"缩短 name 至 {MAX_SKILL_NAME_LENGTH} 字符以内",
        "frontmatter → name",
    )]
def _uv011_issues(name_stripped: str) -> list:
    if ("--" not in name_stripped
            and not name_stripped.startswith("-")
            and not name_stripped.endswith("-")):
        return []
    return [_upload_issue(
        "UV-011", "high",
        "name 存在连字符边界问题（连续连字符或首尾连字符）",
        "移除连续连字符及首尾连字符",
        "frontmatter → name",
    )]
def _upload_identity_path(md_path, skill_dir) -> Any:
    if isinstance(skill_dir, (str, os.PathLike)):
        skill_dir_text = os.fspath(skill_dir)
        if isinstance(skill_dir_text, str) and skill_dir_text.strip():
            return os.path.join(skill_dir_text, "SKILL.md")
    return md_path
def _check_upload_name(raw_name, md_path, skill_dir) -> list:
    issues: list[DocQualityIssue] = _uv003_issues(raw_name)
    if not (isinstance(raw_name, str) and raw_name.strip()):
        return issues
    identity_path = _upload_identity_path(md_path, skill_dir)
    name_value = raw_name.strip()
    issues.extend(_uv004_issues(raw_name))
    issues.extend(_uv007_issues(name_value, identity_path))
    issues.extend(_uv006_issues(name_value))
    issues.extend(_uv011_issues(name_value))
    return issues
def _check_upload_desc_required(description) -> list:
    issues: list[DocQualityIssue] = []
    if description is None:
        issues.append(_upload_issue(
            "UV-008", "critical",
            "frontmatter 缺少必填字段 'description'",
            "在 frontmatter 中添加 description 字段",
            "frontmatter",
        ))
    elif not isinstance(description, str):
        issues.append(_upload_issue(
            "UV-008", "critical",
            f"description 字段类型错误（{type(description).__name__}），应为字符串",
            "将 description 改为字符串类型",
            "frontmatter → description",
        ))
    elif _desc_length(description) < _UPLOAD_DESC_MIN_CHARS:
        issues.append(_upload_issue(
            "UV-008", "critical",
            f"description 过短（{_desc_length(description)} 字符）",
            f"description 至少 {_UPLOAD_DESC_MIN_CHARS} 字符，须包含触发条件和能力描述",
            "frontmatter → description",
        ))
    return issues
def _uv012_issues(description: str) -> list:
    for i, ch in enumerate(description):
        if unicodedata.category(ch) == "Cc" and ch not in ("\n", "\r", "\t"):
            return [_upload_issue(
                "UV-012", "high",
                f"description 含控制字符 U+{ord(ch):04X}",
                "移除或转义该控制字符",
                f"description 位置 {i}",
            )]
    return []
def _uv009_issues(description: str) -> list:
    if "<" not in description and ">" not in description:
        return []
    return [_upload_issue(
        "UV-009", "medium",
        "description 含尖括号（可能触发 HTML 注入检测）",
        "将 < > 替换为全角字符 ＜ ＞",
        "frontmatter → description",
    )]
def _uv010_issues(description: str) -> list:
    length = _desc_length(description)
    if length <= UPLOAD_DESC_MAX_CHARS:
        return []
    return [_upload_issue(
        "UV-010", "high",
        f"description 长度 {length} 超过 {UPLOAD_DESC_MAX_CHARS} 字符限制",
        f"精简至 {UPLOAD_DESC_MAX_CHARS} 字符以内",
        "frontmatter → description",
    )]
def _check_upload_desc_format(description) -> list:
    if not isinstance(description, str) or not description:
        return []
    return [*_uv012_issues(description),
            *_uv009_issues(description),
            *_uv010_issues(description)]
_UPLOAD_SUBDIMENSIONS = (
    (
        "U1", "YAML合规性", 0.40,
        frozenset({"UV-001", "UV-002", "UV-008", "UV-009", "UV-012"}),
        {"critical": 50.0, "high": 25.0, "medium": 10.0},
        "YAML问题", "YAML合规",
    ),
    (
        "U2", "内容限制合规", 0.60,
        frozenset({"UV-003", "UV-004", "UV-005", "UV-006", "UV-007", "UV-010", "UV-011"}),
        {"critical": 40.0, "high": 20.0, "medium": 10.0},
        "内容限制问题", "内容限制合规",
    ),
)
def diag_upload_u1u2(all_issues: list[DocQualityIssue]) -> list[SubDimensionScore]:
    if all_issues is None:
        raw_items = []
    elif isinstance(all_issues, Iterable) and not isinstance(
            all_issues, (str, bytes, bytearray, Mapping)):
        raw_items = list(all_issues)
    else:
        raw_items = [all_issues]
    upload_issues: list = []
    skipped = 0
    for item in raw_items:
        if not all(isinstance(getattr(item, field_name, None), str)
                   for field_name in ("category", "rule_id", "severity")):
            skipped += 1
            continue
        if item.category == "upload":
            upload_issues.append(item)
    results: list[SubDimensionScore] = []
    for dim_id, dim_name, weight, rule_ids, deductions, problem_label, ok_label in _UPLOAD_SUBDIMENSIONS:
        dim_issues = [i for i in upload_issues if i.rule_id in rule_ids]
        unknown_severities = sum(
            i.severity not in deductions for i in dim_issues)
        unknown_deduction = max(deductions.values(), default=0.0)
        invalid_deduction = skipped * unknown_deduction
        score = max(0.0, 100.0 - invalid_deduction - sum(
            deductions.get(i.severity, unknown_deduction) for i in dim_issues))
        detail = (f"{len(dim_issues)}项{problem_label}" if dim_issues
                  else ok_label)
        if unknown_severities:
            detail += f"（{unknown_severities}条未知严重度按最高档扣分）"
        if skipped:
            detail += f"（{skipped} 条非法条目按最高档扣分）"
        results.append(SubDimensionScore(
            dim_id=dim_id, dim_name=dim_name, category="upload",
            score=score, weight=weight,
            issues=dim_issues,
            detail=detail,
        ))
    return results
_DOC_CORE_SECTIONS = [
    ("frontmatter", r"^---\s*$"),
    ("name_field", r"^name[ \t]*:"),
    ("description_field", r"^description[ \t]*:"),
]
_DOC_CORE_SECTION_NAMES = frozenset(name for name, _ in _DOC_CORE_SECTIONS)
_DOC_TEMPLATE_SECTIONS = [
    ("scope_boundary", r"能做|In Scope|不能做|Out of Scope|不支持|不适用|仅支持"),
    ("agent_guidance", r"Agent 决策指引|决策指引"),
    ("trigger_conditions", r"触发条件|触发示例|Trigger"),
    ("quick_start", r"快速入门|Quick Start"),
    ("module_overview", r"模块总览|域.*总览"),
    ("use_cases", r"典型应用场景|应用场景"),
    ("constraints", r"关键约束|约束"),
    (CAT_DISCOVERABILITY, r"六维可发现性|可发现性"),
]
_DOC_GENERAL_SECTIONS = [
    ("usage_entry", (r"快速入门|快速开始|快速上手|使用方法|使用说明|"
                     r"命令速查|调用方式|工作流|workflow|usage|quick\s*start|"
                     r"getting\s*started|示例|examples?")),
    ("scope_boundary", (r"不支持|不适用|不覆盖|不处理|能做|In Scope|"
                        r"不能做|Out of Scope|仅支持|只支持|能力边界|限制|"
                        r"limitations?")),
]
_DOC_ROUTER_SECTIONS = [
    ("local_md_ref", r'(?<![\w./-])(?:[\w.-]+/)*[\w.-]+\.md\b'),
]
def _doc_required_for_profile(md_content: str) -> list:
    profile = detect_doc_profile_text(md_content)
    if profile == "template":
        return _DOC_CORE_SECTIONS + _DOC_TEMPLATE_SECTIONS
    if profile == "router":
        return _DOC_CORE_SECTIONS + _DOC_ROUTER_SECTIONS
    return _DOC_CORE_SECTIONS + _DOC_GENERAL_SECTIONS
def _doc_file_phase(md_path: str, details: list[dict],
                    suggestions: list[str]) -> bool:
    md_content, read_exc = _read_skill_doc_text(md_path)
    if md_content is None:
        log_swallowed(
            __name__, read_exc,
            context=f'_doc_file_phase:{type(read_exc).__name__}')
        details.append(make_detail(
            "invalid_skill_md", "DOC-01", md_path, confidence=1.0,
            message=f"SKILL.md 读取失败: {read_exc}",
        ))
        suggestions.append("SKILL.md 必须是可读取的 UTF-8 普通文件")
        return True
    violated = False
    frontmatter_parts = split_frontmatter_document(md_content)
    frontmatter = frontmatter_parts[0] if frontmatter_parts else ""
    body = frontmatter_parts[1] if frontmatter_parts else md_content
    section_content = strip_fenced_blocks(body)
    frontmatter_lines = frontmatter.splitlines()
    fm_start = _first_content_line_index(frontmatter_lines)
    core_presence = {
        "frontmatter": fm_start < len(frontmatter_lines)
        and is_frontmatter_fence(frontmatter_lines[fm_start]),
        "name_field": _frontmatter_has_field(frontmatter_lines, "name"),
        "description_field": _frontmatter_has_field(
            frontmatter_lines, "description"),
    }
    for section_name, pattern in _doc_required_for_profile(md_content):
        if section_name in _DOC_CORE_SECTION_NAMES:
            present = core_presence.get(section_name, False)
        else:
            present = re.search(
                pattern, section_content, re.MULTILINE | re.IGNORECASE,
            ) is not None
        if not present:
            violated = True
            details.append(make_detail(
                "missing_section", "DOC-01", md_path, confidence=0.9,
                section=section_name,
                pattern=pattern,
            ))
            suggestions.append(f"SKILL.md 缺少章节: {section_name}")
    return violated
def _doc_description_phase(description: str, details: list[dict],
                           suggestions: list[str]) -> bool:
    description = description.strip()
    violated = False
    if not description:
        violated = True
        details.append(make_detail(
            "no_description", "DOC-02", "<SKILL.md>", confidence=0.95,
            message="缺少技能描述",
        ))
        suggestions.append("提供技能描述（description），用于生成 SKILL.md frontmatter")
    if description and not re.search(r'[a-zA-Z]', description):
        suggestions.append("可选建议：按目标用户语言补充英文或双语触发词以提高可发现性")
    if description and not any(w in description for w in COLLOQUIAL_TRIGGER_WORDS):
        suggestions.append(
            f"可选建议：按目标用户习惯添加口语化触发词: {COLLOQUIAL_TRIGGER_WORDS}")
    return violated
def check_doc_skeleton(skill_dir: str | os.PathLike = "",
                       description: str = "") -> PreinterventionResult:
    skill_dir = normalize_input(skill_dir, "check_doc_skeleton 参数 skill_dir",
                                 allow_path=True)
    description = normalize_input(description, "check_doc_skeleton 参数 description")
    details: list[dict] = []
    suggestions: list[str] = []
    md_path = os.path.join(skill_dir, "SKILL.md") if skill_dir else ""
    md_exists = bool(md_path) and os.path.isfile(md_path)
    if md_exists:
        violated = _doc_file_phase(md_path, details, suggestions)
    elif not skill_dir:
        violated = _doc_description_phase(description, details, suggestions)
    elif not os.path.isdir(skill_dir):
        violated = True
        details.append(make_detail(
            "invalid_skill_dir", "DOC-01", skill_dir, confidence=1.0,
            message=f"技能目录不存在: {skill_dir}",
        ))
        suggestions.append("传入真实存在的技能目录（含 SKILL.md）后重跑骨架检查")
    elif os.path.exists(md_path):
        violated = True
        details.append(make_detail(
            "invalid_skill_md", "DOC-01", md_path, confidence=1.0,
            message="SKILL.md 不是普通文件",
        ))
        suggestions.append("SKILL.md 必须是可读取的普通文件")
    else:
        violated = True
        details.append(make_detail(
            "missing_skill_md", "DOC-01", md_path, confidence=1.0,
            message="技能目录缺少 SKILL.md",
        ))
        suggestions.append("在技能目录中创建 SKILL.md 后重跑骨架检查")
    return finish_check("doc_skeleton_check", "文档骨架检查", not violated, "warning",
                   details, suggestions)
def _doc_check_provider() -> dict:
    return {"doc_skeleton_check": check_doc_skeleton}
register_check_provider(_doc_check_provider)
_SECTION_TITLE_SEPARATORS = ("（", "(", "：", ":", "-", "—", "/", "、")
class SkillDocPrecheck:
    REQUIRED_SECTIONS: ClassVar[list] = [
        "技能能力边界", "Agent 决策指引", "触发条件",
        "快速入门", "域总览",
        "关键约束",
    ]
    SECTION_ALIASES: ClassVar[dict[str, tuple[str, ...]]] = {
        "技能能力边界": (
            "Capability Boundary", "Capabilities and Boundaries",
            "Boundaries", "Scope", "Limitations", "What This Does Not Do",
        ),
        "Agent 决策指引": (
            "Decision Guide", "Decision Tree", "How to Choose",
            "Choosing the Right Mode", "Which Mode",
        ),
        "触发条件": (
            "Trigger Conditions", "Triggers", "When to Use",
            "When to Use This Skill", "Activation",
        ),
        "快速入门": (
            "Quick Start", "Quickstart", "Getting Started",
            "Usage", "Basic Usage",
        ),
        "域总览": (
            "Overview", "Domain Overview", "Architecture", "Introduction",
        ),
        "关键约束": (
            "Key Constraints", "Constraints", "Important Notes",
            "Rules", "Guardrails", "Requirements",
        ),
    }
    _KEYWORD_DIMENSIONS: ClassVar[list[dict]] = [
        {
            "keywords": COLLOQUIAL_TRIGGER_WORDS,
            "severity": SEVERITY_INFO,
            "missing": "描述缺少口语化近义词",
            "fix": "dynamic_sample",
        },
        {
            "keywords": ("怎么做", "帮我", "how do i", "how to",
                         "help me", "can you", "i need to", "i want to"),
            "severity": SEVERITY_INFO,
            "missing": "描述缺少用户指令示例",
            "fix": "添加触发示例，如: '帮我处理一下' / 'how do I merge two PDFs'",
        },
        {
            "keywords": ("开发者", "架构师", "测试", "运维", "安全",
                         "developer", "architect", "tester", "devops", "security"),
            "severity": SEVERITY_INFO,
            "missing": "描述缺少角色视角分层",
            "fix": "添加角色视角关键词，如: 开发者/架构师/测试工程师/运维/安全工程师",
        },
        {
            "keywords": ("创建", "诊断", "修复", "审计", "优化", "重构",
                         "create", "diagnose", "fix", "audit", "optimize",
                         "refactor", "extract", "merge", "split", "convert",
                         "generate", "analyze", "inspect", "review"),
            "severity": SEVERITY_WARNING,
            "missing": "描述缺少业务功能关键词",
            "fix": "添加业务功能关键词，如: 创建/诊断/修复/审计/优化/重构",
        },
        {
            "keywords": ("场景", "标签", "tag", "场景标签", "关联",
                         "scenario", "scenarios", "label", "related",
                         "use case", "use cases", "see also"),
            "severity": SEVERITY_INFO,
            "missing": "描述缺少关联锚点或场景标签",
            "fix": "添加场景标签或关联锚点，如: 场景标签/关联技能/tag",
        },
    ]
    def check(self, skill_name: str = "",
              skill_desc: str = "",
              skill_md_content: str = "") -> list[PreCheckItem]:
        items = []
        skill_name, name_error = normalize_text_param(
            skill_name, "skill_name 期望 str",
            suggestion="传入 str 后再继续", applicable_to="SKILL.md header")
        skill_desc, desc_error = normalize_text_param(
            skill_desc, "skill_desc 期望 str",
            suggestion="传入 str 后再继续", applicable_to="SKILL.md description")
        skill_md_content, md_error = normalize_text_param(
            skill_md_content, "skill_md_content 期望 str",
            suggestion="传入 str 文档内容后再继续", applicable_to="SKILL.md body")
        for error in (name_error, desc_error, md_error):
            if error is not None:
                items.append(error)
        skill_desc = skill_desc or ""
        self._append_identity_issues(skill_name, skill_desc, items)
        items.extend(self._check_six_dimensions(skill_desc))
        if skill_md_content:
            self._check_required_sections(skill_md_content, items)
        return items
    @classmethod
    def _has_required_section(cls, content: str, canonical: str) -> bool:
        targets = (canonical, *cls.SECTION_ALIASES.get(canonical, ()))
        folded_targets = frozenset(target.casefold() for target in targets)
        lines = content.splitlines()
        fence_states = _heading_scan_states(lines)
        for heading in _heading_map(lines, fence_states).values():
            folded = heading[1].strip().casefold()
            if folded in folded_targets:
                return True
            if any(re.match(rf"{re.escape(target)}\s*{re.escape(sep)}", folded)
                   for target in folded_targets
                   for sep in _SECTION_TITLE_SEPARATORS):
                return True
        return False
    @staticmethod
    def _doc_issue(severity: str, description: str, suggestion: str,
                   applicable_to: str, *, source: str = "rule") -> PreCheckItem:
        return PreCheckItem(
            category="documentation", severity=severity,
            description=description, suggestion=suggestion,
            source=source, applicable_to=applicable_to,
        )
    @staticmethod
    def _append_identity_issues(skill_name: str, skill_desc: str,
                                items: list[PreCheckItem]) -> None:
        if not skill_name.strip():
            items.append(SkillDocPrecheck._doc_issue(
                SEVERITY_BLOCKING, "技能名称为空",
                "提供一个简洁明确的技能名称", "SKILL.md header"))
        if not skill_desc.strip():
            items.append(SkillDocPrecheck._doc_issue(
                SEVERITY_BLOCKING, "技能描述为空",
                "提供中英双语描述，包含触发关键词和口语化表达",
                "SKILL.md description"))
        elif _desc_length(skill_desc) < 50:
            items.append(SkillDocPrecheck._doc_issue(
                SEVERITY_WARNING, "技能描述过短",
                "描述应包含：能力概述 + 触发关键词 + 口语化表达",
                "SKILL.md description"))
    def _check_required_sections(self, skill_md_content: str,
                                 items: list[PreCheckItem]) -> None:
        content = skill_md_content if isinstance(skill_md_content, str) else ""
        profile = detect_doc_profile_text(content)
        if profile == "router":
            return
        frontmatter_parts = split_frontmatter_document(content)
        body = frontmatter_parts[1] if frontmatter_parts else content
        if profile == "template":
            for section in self.REQUIRED_SECTIONS:
                if self._has_required_section(body, section):
                    continue
                items.append(self._doc_issue(
                    SEVERITY_WARNING, f"SKILL.md 缺少必需章节: {section}",
                    f"添加 '{section}' 章节，确保 Agent 能完整理解技能能力",
                    "SKILL.md body"))
            return
        section_content = strip_fenced_blocks(body)
        if not _GENERIC_USAGE_RE.search(section_content):
            items.append(self._doc_issue(
                SEVERITY_WARNING, "SKILL.md 缺少必需章节: 使用入口/操作说明",
                "补充快速开始、使用方法或命令速查章节",
                "SKILL.md body"))
        if not _GENERIC_BOUNDARY_RE.search(section_content):
            items.append(self._doc_issue(
                SEVERITY_WARNING, "SKILL.md 缺少必需章节: 能力边界",
                "补充不支持/不适用/仅支持等边界说明",
                "SKILL.md body"))
    @staticmethod
    def _missing_language(desc: str) -> str:
        has_chinese = any('\u4e00' <= c <= '\u9fff' for c in desc)
        has_english = any('a' <= c <= 'z' for c in desc)
        if has_chinese and has_english:
            return ""
        if has_chinese:
            return "英文"
        if has_english:
            return "中文"
        return "中英双语"
    def _check_six_dimensions(self, desc: str) -> list[PreCheckItem]:
        items = []
        desc = desc.lower()
        missing_language = self._missing_language(desc)
        if missing_language:
            suffix = "（建议中英双语）" if missing_language != "中英双语" else ""
            items.append(self._doc_issue(
                SEVERITY_WARNING, f"描述缺少{missing_language}关键词{suffix}",
                f"description 补充{missing_language}关键词以提高跨语言触发覆盖",
                "description", source="six_dimensions"))
        for dim in self._KEYWORD_DIMENSIONS:
            if count_keyword_hits(desc, dim["keywords"]):
                continue
            suggestion = dim["fix"]
            if suggestion == "dynamic_sample":
                suggestion = f"添加口语化触发词，如: {', '.join(dim['keywords'][:5])}"
            items.append(self._doc_issue(
                dim["severity"], dim["missing"], suggestion, "description",
                source="six_dimensions"))
        return items
register_review_provider(
    "precreation_doc_precheck", SkillDocPrecheck)

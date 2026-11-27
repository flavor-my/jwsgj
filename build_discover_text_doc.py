from __future__ import annotations

import hashlib
import logging
import os
import re
from bisect import bisect_right
from collections import defaultdict
from collections.abc import Iterator
from dataclasses import dataclass, field
from datetime import UTC, datetime
from itertools import groupby
from pathlib import Path
from typing import Any, NamedTuple, Self

from jwsgj.build_text_document import (
    _FENCE_LINE_RE,
    _MD_BLANK_LINE_RE,
    _MD_LINK_DEST_RE,
    _MD_LINK_RE,
    ENTRY_DOC_NAME,
    SETEXT_UNDERLINE_RE,
    _iter_local_links,
    iter_doc_entry_candidates,
    iter_fence_state,
    jaccard,
    resolve_entry_document,
    scan_fence_state,
)
from jwsgj.build_text_frontmatter import locate_frontmatter_body_start
from jwsgj.diag_shared_source_core import count_lines

__all__ = [
    'DocCleaner',
    'DocCleanupItem',
    'DocCleanupReport',
    'DocEntropyMetrics',
    'body_opens_with_code_block',
    'code_block_mask',
    'inline_code_spans',
    'referenced_local_paths',
]
_log = logging.getLogger(__name__)
_DEFAULT_METRIC_VALUE = 0.0
_NO_EXTRA_PROTECTED_SECTIONS: tuple[str, ...] = ()
@dataclass
class DocCleanupItem:
    line_start: int = 0
    line_end: int = 0
    section: str = ""
    category: str = ""
    severity: str = "info"
    description: str = ""
    snippet: str = ""
    suggestion: str = ""
    metric_value: float = _DEFAULT_METRIC_VALUE
@dataclass
class DocEntropyMetrics:
    structure_entropy: float = 0.0
    semantic_redundancy: float = 0.0
    freshness_score: float = 100.0
    heading_depth_variance: float = 0.0
    duplicate_heading_count: int = 0
    blank_line_clusters: int = 0
    stale_date_count: int = 0
    total_score: float = 100.0
@dataclass
class DocCleanupReport:
    skill_dir: str = ""
    doc_path: str = ""
    total_lines: int = 0
    items: list[DocCleanupItem] = field(default_factory=list)
    entropy: DocEntropyMetrics | None = None
    errors: list[str] = field(default_factory=list)
_CHANGELOG_SECTION_PATTERNS = [
    r"^#+\s*(?:变更日志|更新日志|版本历史|发布说明|Changelog|Change\s*Log|Release\s*Notes|History|变更记录|修订记录|更新记录)",
    r"^#+\s*(?:What'?s\s+New|Breaking\s+Changes|Migration\s+Guide|Upgrade\s+Notes)",
    r"^#+\s*(?:版本\s*\d+\.\d+|v\d+\.\d+\.\d+)",
]
_NESTED_CHANGELOG_PATTERNS = [
    r".*(?:v\d+\.\d+\.\d+|v\d+\.\d+)\s*(?:新增|修复|移除|重构|优化|升级|迁移).*",
    r".*自\s*v?\d+\.\d+.*(?:起|开始|之后).*",
    r".*(?:since|from)\s+v?\d+\.\d+\.\d+.*",
]
_KEEP_A_CHANGELOG_PATTERN = re.compile(
    r"^###?\s*(Added|Changed|Deprecated|Removed|Fixed|Security|"
    r"新增|变更|弃用|移除|修复|安全)\s*$",
    re.IGNORECASE
)
_HISTORICAL_PATTERNS = [
    (r"已废弃.*(?:API|方法|函数|模块|接口|类|属性|参数|功能)", "已废弃的 API 说明"),
    (r"(?:不再支持|已移除|已删除|已下线).*(?:功能|特性|模块|接口|API|方法)", "已移除的功能说明"),
    (r"(?:旧版|老版本|legacy|outdated|obsolete).*(?:支持|处理|方式|用法)", "旧版说明"),
    (r"自\s*(?:v?\d+\.\d+|版本\s*\d+).*起(?:已|不再|废弃|移除|删除)", "版本废弃声明"),
    (r"(?:deprecated|obsolete|removed)\s*(?:since|in|from|at)\s+v?\d+\.\d+", "英文废弃声明"),
    (r"\(已(?:废弃|删除|移除|过时|淘汰)\)", "括号内废弃标记"),
    (r"~~.*~~", "删除线标记（暗示已废弃内容）"),
    (r"此(?:功能|方法|API|接口).*(?:已不再|已被|已经).*(?:使用|推荐|替代)", "功能替代说明"),
    (r"(?:请改用|请迁移到|请迁移至|迁移到|迁移至)[^\n]{0,60}(?:替代|代替|替换|取代)", "迁移引导（暗示旧功能已废弃）"),
]
_REDUNDANT_PATTERNS = [
    (r"^>{3,}\s*$", "长分隔线（冗余装饰）"),
    (r"^-{5,}\s*$", "水平分隔线"),
    (r"^={5,}\s*$", "等号分隔线"),
    (r"^\*{5,}\s*$", "星号分隔线"),
    (r"^(?:备注|注意|提示|说明|警告|重要)\s*[：:]\s*$", "空备注标题"),
    (r"^\*\*(?:备注|注意|提示|说明|警告|重要)\*\*\s*[：:]\s*$", "空加粗标记"),
    (r"^(?:TODO|FIXME|HACK|XXX|NOTE)\s*[：:]\s*$", "空待办标记"),
]
_INVALID_PATTERNS = [
    (r"^\|(?:\s*\|)+$", "空表格行"),
    (r"(?<!!)\[[^\]]*\]\s*\(\s*\)", "空链接"),
    (r"!\[[^\]]*\]\s*\(\s*\)", "空图片标记"),
]
_PARAGRAPH_BREAK_RE = re.compile(
    r"^\s*$|^[ ]{0,3}#{1,6}(?:[ \t]+|$)")
_LIST_MARKER_RE = re.compile(r"^(\s*)([-*+])\s+")
_LIST_ITEM_LEAD_RE = re.compile(r"^[ ]{0,3}(?:[-*+]|\d+[.)])[ \t]+")
_BLOCKQUOTE_LEAD_RE = re.compile(r"^[ ]{0,3}>")
_BLOCKQUOTE_PREFIX_RE = re.compile(r"^[ ]{0,3}>[ \t]?")
_CONTAINER_PREFIX_RE = re.compile(
    r"^[ ]{0,3}(?:>[ \t]?|(?:[-*+]|\d{1,9}[.)])[ \t]+)")
_LIST_CONTAINER_RE = re.compile(
    r"^( *)([-*+]|\d{1,9}[.)])(?:( +)(.*))?$")
_TABLE_ROW_LEAD_RE = re.compile(r"^[ ]{0,3}\|")
_THEMATIC_BREAK_RE = re.compile(
    r"^[ ]{0,3}(?:(?:\*[ \t]*){3,}|(?:-[ \t]*){3,}|(?:_[ \t]*){3,})$")
_HEADING_RE = re.compile(r"^[ ]{0,3}(#{1,6})(?:[ \t]+|$)")
_HEADING_TEXT_RE = re.compile(
    r"^[ ]{0,3}(#{1,6})(?:[ \t]+(.*))?[ \t]*$")
_NON_PARAGRAPH_LEAD_RE = re.compile(r"^(?:[-*+]\s|\d+[.)]\s|\||>|`{3,}|~{3,})")
_PROTECTED_SECTIONS = {
    "设计原则", "快速导航", "适用场景", "不适用场景",
    "Python API", "CLI 入口", "子包架构", "架构", "结构",
    "API", "Usage", "Installation", "Quick Start",
    "快速开始", "安装", "使用方式", "调用方式",
    "Agent 使用方式", "核心 API", "配置", "Configuration",
    "Overview", "概览", "简介", "Introduction",
    "核心能力", "能力矩阵",
    "兼容性", "性能", "依赖", "Dependencies", "Requirements",
    "测试", "Testing", "贡献指南", "Contributing",
    "许可证", "License", "安全", "Security",
    "常见问题", "FAQ", "故障排除", "Troubleshooting",
    "参考", "References", "致谢", "Acknowledgments",
    "Cleanup", "Clean",
}
_MIN_PARAGRAPH_CHARS = 20
_STALE_DATE_THRESHOLD_DAYS = 365
_DATE_PATTERNS = [
    re.compile(r"(\d{4})[-/](\d{2})[-/](\d{2})"),
    re.compile(r"(\d{4})年(\d{1,2})月(\d{1,2})日"),
]
def _normalize_text(text: str) -> str:
    return re.sub(r"\s+", " ", text.lower()).strip()
def _char_ngrams(text: str, n: int = 3) -> set[str]:
    s = _normalize_text(text)
    if len(s) < n:
        return {s}
    return {s[i:i + n] for i in range(len(s) - n + 1)}
def _section_is_protected(
        section: str,
        extra: tuple[str, ...] = _NO_EXTRA_PROTECTED_SECTIONS) -> bool:
    folded = section.casefold()
    for protected in (*_PROTECTED_SECTIONS, *extra):
        needle = protected.casefold()
        if not needle.isascii():
            if needle in folded:
                return True
            continue
        if re.search(rf"(?<![a-z0-9_]){re.escape(needle)}(?![a-z0-9_])",
                     folded):
            return True
    return False
def _normalize_protected_sections(values: Any) -> tuple[str, ...]:
    if values is None:
        return ()
    if isinstance(values, str):
        values = (values,)
    if not isinstance(values, (list, tuple, set, frozenset)):
        return ()
    ordered: list[str] = []
    for value in values:
        text = value.strip() if isinstance(value, str) else ""
        if text and text not in ordered:
            ordered.append(text)
    return tuple(ordered)
class _SectionMap(dict[int, str]):
    __slots__ = ("extra", "protected_lines")
    def __init__(
            self, extra: tuple[str, ...] = _NO_EXTRA_PROTECTED_SECTIONS,
            ) -> None:
        super().__init__()
        self.extra = extra
        self.protected_lines: set[int] = set()
    def is_protected(self, section: str, line_no: int) -> bool:
        return (line_no in self.protected_lines
                or _section_is_protected(section, self.extra))
def _line_in_changelog(idx: int, sections: list[tuple[int, int]]) -> bool:
    return any(cs <= idx < ce for cs, ce in sections)
def _line_exempt(idx: int, exempt_mask: set[int],
                 changelog_sections: list[tuple[int, int]]) -> bool:
    return idx in exempt_mask or _line_in_changelog(idx, changelog_sections)
def _setext_underline_lines(lines: list[str],
                            exempt_mask: set[int]) -> set[int]:
    underlines: set[int] = set()
    for i in range(1, len(lines)):
        if i in exempt_mask or (i - 1) in exempt_mask:
            continue
        # 缩进 >= 4 的下划线属于缩进代码（或段落的懒惰续行），
        # 按 CommonMark 不能打断段落成为 setext 标题。
        expanded = lines[i].expandtabs(4)
        if len(expanded) - len(expanded.lstrip(" ")) > 3:
            continue
        if not SETEXT_UNDERLINE_RE.match(lines[i].strip()):
            continue
        prev = lines[i - 1].strip()
        if (not prev or SETEXT_UNDERLINE_RE.match(prev)
                or _HEADING_RE.match(prev)
                or _NON_PARAGRAPH_LEAD_RE.match(prev)
                or _THEMATIC_BREAK_RE.match(prev)):
            continue
        underlines.add(i)
    return underlines
def _setext_heading_blocks(
        lines: list[str], exempt_mask: set[int],
        ) -> list[tuple[int, int, int]]:
    blocks: list[tuple[int, int, int]] = []
    for underline in sorted(_setext_underline_lines(lines, exempt_mask)):
        start = underline - 1
        while start > 0:
            previous = start - 1
            if previous in exempt_mask:
                break
            text = lines[previous].strip()
            if (not text or SETEXT_UNDERLINE_RE.match(text)
                    or _HEADING_RE.match(text)
                    or _NON_PARAGRAPH_LEAD_RE.match(text)
                    or _THEMATIC_BREAK_RE.match(text)):
                break
            start = previous
        level = 1 if lines[underline].strip()[0] == "=" else 2
        blocks.append((start, underline, level))
    return blocks
def _dead_link_item(line_no: int, line: str, target: str,
                    section: str) -> DocCleanupItem:
    return DocCleanupItem(
        line_start=line_no, line_end=line_no,
        section=section,
        category="invalid", severity="warning",
        description=f"死链接：目标文件 '{target}' 不存在",
        snippet=line.strip()[:100],
        suggestion=f"更新或移除此链接: {target}",
    )
def _default_document_path(project_root: Path) -> Path:
    resolved = resolve_entry_document(project_root)
    return project_root / ENTRY_DOC_NAME if resolved is None else resolved
def _resolve_document_path(project_root: Path, doc_path) -> Path:
    if doc_path is None:
        return _default_document_path(project_root)
    if not isinstance(doc_path, (str, os.PathLike)) or not os.fspath(doc_path):
        raise ValueError(f"无效的文档路径: {doc_path!r}")
    candidate = Path(doc_path)
    if not candidate.is_absolute():
        candidate = project_root / candidate
    resolved = candidate.resolve()
    if not resolved.is_relative_to(project_root.resolve()):
        raise ValueError(f"文档路径必须位于项目目录内: {doc_path}")
    return resolved
def _entry_candidate_hint(project_root: Path) -> str:
    names: list[str] = []
    for candidate in iter_doc_entry_candidates(project_root):
        try:
            name = candidate.relative_to(project_root).as_posix()
        except ValueError:
            name = candidate.name
        if name not in names:
            names.append(name)
        if len(names) >= 6:
            break
    return "、".join(names)
def _entry_missing_error(project_root: Path, doc_path: Path) -> str:
    if doc_path.name != ENTRY_DOC_NAME:
        return f"{doc_path.name} 不存在"
    return (f"未找到入口文档（{doc_path.name} / README / docs 入口）: "
            f"已查找 {_entry_candidate_hint(project_root)}")
class DocCleaner:
    def __init__(self: Self, skill_dir: str,
                 doc_path: str | os.PathLike | None = None,
                 *, protected_sections: tuple[str, ...] | list[str] | None = None,
                 ) -> None:
        if (not isinstance(skill_dir, (str, os.PathLike))
                or not os.fspath(skill_dir)):
            raise ValueError(
                f"无效的技能目录: {skill_dir!r}（须为非空字符串或路径对象）")
        self._skill_dir = Path(skill_dir)
        if not self._skill_dir.is_dir():
            raise ValueError(f"无效的技能目录: {skill_dir}")
        self._doc_path = _resolve_document_path(self._skill_dir, doc_path)
        self._protected_sections = _normalize_protected_sections(
            protected_sections)
    def analyze(self: Self) -> DocCleanupReport:
        report = DocCleanupReport(
            skill_dir=str(self._skill_dir),
            doc_path=str(self._doc_path),
        )
        if not self._doc_path.exists():
            report.errors.append(
                _entry_missing_error(self._skill_dir, self._doc_path))
            return report
        try:
            content = self._doc_path.read_text(encoding="utf-8-sig")
        except (OSError, UnicodeDecodeError) as e:
            report.errors.append(f"读取 {self._doc_path.name} 失败: {e}")
            _log.error("analyze failed: %s", e, exc_info=True)
            return report
        lines = content.split("\n")
        if content.endswith("\n"):
            lines.pop()
        report.total_lines = count_lines(content)
        inline_masked_lines = _mask_inline_code_lines(lines)
        exempt_mask = _body_exempt_mask(lines)
        paragraphs = _extract_paragraphs(lines, exempt_mask)
        changelog_sections = _find_changelog_sections(lines, exempt_mask)
        eligible_paragraphs = _eligible_paragraphs(
            paragraphs, changelog_sections)
        heading_texts = {
            i: text for i, _depth, text in _iter_heading_texts(lines, exempt_mask)
        }
        _report_changelog_sections(
            lines, changelog_sections, report, heading_texts)
        section_map = _build_section_map(
            lines, exempt_mask, self._protected_sections)
        _scan_lines_pass(
            lines, exempt_mask, changelog_sections, report, heading_texts,
            section_map, inline_masked_lines)
        exact_duplicate_items = _detect_duplicate_paragraphs(
            lines, section_map, eligible_paragraphs)
        exact_duplicate_ranges = {
            (item.line_start, item.line_end) for item in exact_duplicate_items
        }
        report.items.extend(
            item for item in _detect_similar_paragraphs(
                lines, section_map, eligible_paragraphs)
            if (item.line_start, item.line_end) not in exact_duplicate_ranges)
        report.items.extend(exact_duplicate_items)
        report.items.extend(_detect_markdown_lint(
            lines, section_map, exempt_mask, changelog_sections))
        report.items.extend(_detect_dead_links(
            lines, exempt_mask, changelog_sections, self._skill_dir,
            section_map, link_base=self._doc_path.parent,
            masked_lines=inline_masked_lines))
        report.entropy = _compute_entropy_metrics(
            lines, report, exempt_mask, changelog_sections, section_map,
            paragraph_total=sum(
                1 for start, _end, _content in eligible_paragraphs
                if not section_map.is_protected(
                    section_map.get(start, ""), start)))
        return report
def _detect_dead_links(lines: list[str],
                       exempt_mask: set[int],
                       changelog_sections: list[tuple[int, int]],
                       skill_dir: Path,
                       section_map: _SectionMap,
                       link_base: Path,
                       *, masked_lines: list[str],
                       ) -> list[DocCleanupItem]:
    items: list[DocCleanupItem] = []
    for i, line in enumerate(lines):
        if _line_exempt(i, exempt_mask, changelog_sections):
            continue
        section = section_map.get(i + 1, "")
        for target, target_path in _iter_local_link_targets(
                masked_lines[i], skill_dir, link_base):
            if target_path is None or not target_path.exists():
                items.append(_dead_link_item(i + 1, line, target, section))
    return items
def _iter_local_link_targets(line: str, skill_dir: Path,
                             base_dir: Path | None = None,
                             ) -> Iterator[tuple[str, Path | None]]:
    root = Path(skill_dir).resolve()
    link_base = Path(
        skill_dir if base_dir is None else base_dir).resolve()
    searchable = _mask_inline_code(line)
    for _label, target, decoded_target in _iter_local_links(searchable):
        if "\x00" in decoded_target:
            yield target, None
            continue
        if os.path.isabs(decoded_target):
            absolute = Path(os.path.normpath(decoded_target)).resolve()
            if absolute.is_relative_to(root):
                yield target, absolute
            continue
        target_path = Path(os.path.normpath(
            os.path.join(str(link_base), decoded_target))).resolve()
        if target_path.is_relative_to(root):
            yield target, target_path
def referenced_local_paths(body_text: str, skill_dir: Path,
                           base_dir: Path | None = None) -> set[Path]:
    referenced: set[Path] = set()
    if not isinstance(body_text, str):
        return referenced
    lines = body_text.split("\n")
    masked_lines = _mask_inline_code_lines(lines)
    code_mask = code_block_mask(lines)
    for i, _line in enumerate(lines):
        if i in code_mask:
            continue
        for _target, target_path in _iter_local_link_targets(
                masked_lines[i], skill_dir, base_dir):
            if target_path is not None:
                referenced.add(target_path.resolve())
    return referenced
class _LineScanRule(NamedTuple):
    patterns: list
    category: str
    default_description: str
    suggestion: str
    strip_line: bool
    ignore_case: bool
    anchor: bool
_LINE_SCAN_RULES: tuple[_LineScanRule, ...] = (
    _LineScanRule(_NESTED_CHANGELOG_PATTERNS, "changelog", "嵌套版本变更记录",
                  "移除此版本变更记录行", False, True, False),
    _LineScanRule(_HISTORICAL_PATTERNS, "historical", "历史遗留说明",
                  "移除此行历史遗留说明", False, True, False),
    _LineScanRule(_REDUNDANT_PATTERNS, "redundant", "冗余信息", "移除此行",
                  True, False, True),
    _LineScanRule(_INVALID_PATTERNS, "invalid", "无效标记", "移除此无效标记",
                  True, False, False),
)
def _line_matches(rule: _LineScanRule, text: str, pattern: str) -> bool:
    flags = re.IGNORECASE if rule.ignore_case else 0
    matcher = re.match if rule.anchor else re.search
    return matcher(pattern, text, flags) is not None
def _scan_line_patterns(i: int, line: str, prose: str,
                         current_section: str,
                         report: DocCleanupReport,
                         *, skip_redundant: bool
                         ) -> None:
    stripped = line.strip()
    for rule in _LINE_SCAN_RULES:
        if skip_redundant and rule.category == "redundant":
            continue
        text = prose.strip() if rule.strip_line else prose
        for entry in rule.patterns:
            pattern, desc = (entry if isinstance(entry, tuple)
                             else (entry, rule.default_description))
            if not _line_matches(rule, text, pattern):
                continue
            report.items.append(DocCleanupItem(
                line_start=i + 1, line_end=i + 1,
                section=current_section,
                category=rule.category, severity="info",
                description=desc,
                snippet=stripped,
                suggestion=rule.suggestion,
            ))
            return
def _report_changelog_sections(lines: list[str],
                                changelog_sections: list[tuple[int, int]],
                                report: DocCleanupReport,
                                heading_texts: dict[int, str]) -> None:
    for start, end in changelog_sections:
        section_name = (heading_texts[start] if start in heading_texts
                        else _heading_text(lines[start]))
        if end <= start:
            continue
        snippet = "\n".join(lines[start:min(start + 3, end)])
        report.items.append(DocCleanupItem(
            line_start=start + 1, line_end=end,
            section=section_name,
            category="changelog", severity="warning",
            description=f"变更日志章节: '{section_name}'（{end - start} 行）",
            snippet=snippet,
            suggestion="移除此变更日志章节，版本历史由版本控制系统管理",
        ))
def _scan_lines_pass(lines: list[str],
                     exempt_mask: set[int],
                     changelog_sections: list[tuple[int, int]],
                     report: DocCleanupReport,
                     heading_texts: dict[int, str],
                     section_map: _SectionMap,
                     masked_lines: list[str]) -> None:
    current_section = ""
    policy = section_map
    setext_lines = _setext_underline_lines(lines, exempt_mask)
    for i, line in enumerate(lines):
        if i in exempt_mask:
            continue
        if i in heading_texts:
            current_section = heading_texts[i]
        if (policy.is_protected(current_section, i + 1)
                or _line_in_changelog(i, changelog_sections)):
            continue
        prose = masked_lines[i]
        if _KEEP_A_CHANGELOG_PATTERN.match(prose.strip()):
            report.items.append(DocCleanupItem(
                line_start=i + 1, line_end=i + 1,
                section=current_section,
                category="changelog", severity="info",
                description="Keep a Changelog 标准分类行",
                snippet=line.strip(),
                suggestion="移除此变更日志分类行",
            ))
            continue
        _scan_line_patterns(i, line, prose, current_section, report,
                            skip_redundant=i in setext_lines)
        date_item = _check_stale_date(
            line, i, current_section, search_text=prose)
        if date_item:
            report.items.append(date_item)
def _detect_similar_paragraphs(lines: list[str],
                               section_map: _SectionMap,
                               paragraphs: list[tuple[int, int, str]],
                               ) -> list[DocCleanupItem]:
    if len(paragraphs) < 2:
        return []
    best_by_target = _best_similarity_pairs(paragraphs, section_map)
    return _similar_items_from_pairs(lines, section_map, best_by_target)
def _detect_markdown_lint(lines: list[str],
                          section_map: _SectionMap,
                          exempt_mask: set[int],
                          changelog_sections: list[tuple[int, int]],
                          ) -> list[DocCleanupItem]:
    items: list[DocCleanupItem] = []
    heading_texts, heading_depths = _collect_lint_headings(
        lines, exempt_mask, changelog_sections)
    items.extend(_lint_duplicate_headings(lines, section_map, heading_texts))
    items.extend(_lint_heading_jumps(lines, section_map, heading_depths))
    items.extend(_lint_blank_runs(
        lines, section_map, exempt_mask, changelog_sections))
    items.extend(_lint_list_markers(
        lines, section_map, exempt_mask, changelog_sections))
    return items
def _check_stale_date(line: str, line_idx: int,
                      section: str, *,
                      search_text: str | None = None) -> DocCleanupItem | None:
    stalest: DocCleanupItem | None = None
    if search_text is None:
        search_text = _mask_inline_code(line)
    for pattern in _DATE_PATTERNS:
        for m in pattern.finditer(search_text):
            parsed = _parse_stale_age_days(m)
            if parsed is None:
                continue
            age_days, date_obj = parsed
            if age_days <= _STALE_DATE_THRESHOLD_DAYS:
                continue
            item = DocCleanupItem(
                line_start=line_idx + 1, line_end=line_idx + 1,
                section=section,
                category="stale_date", severity="info",
                description=f"过期日期: {date_obj.strftime('%Y-%m-%d')}（距今 {age_days} 天）",
                snippet=line.strip()[:100],
                suggestion="更新日期或移除此行",
                metric_value=age_days,
            )
            if stalest is None or item.metric_value > stalest.metric_value:
                stalest = item
    return stalest
def _compute_entropy_metrics(lines: list[str],
                             report: DocCleanupReport,
                             exempt_mask: set[int],
                             changelog_sections: list[tuple[int, int]],
                             section_map: _SectionMap, *,
                             paragraph_total: int,
                             ) -> DocEntropyMetrics:
    metrics = DocEntropyMetrics()
    _entropy_structure_metrics(
        lines, exempt_mask, changelog_sections, metrics,
        section_map=section_map)
    metrics.semantic_redundancy = _semantic_redundancy_score(
        report, paragraph_total)
    metrics.blank_line_clusters = _count_blank_line_clusters(
        lines, exempt_mask, changelog_sections, section_map=section_map)
    _stale_freshness_score(report, metrics)
    metrics.total_score = _total_health_score(metrics)
    return metrics
def _find_changelog_sections(lines: list[str],
                             exempt_mask: set[int]) -> list[tuple[int, int]]:
    heading_lines = _collect_heading_lines(lines, exempt_mask)
    all_section_lines = [(i, level) for i, level, _ in heading_lines]
    section_starts = [
        (i, level) for i, level, text in heading_lines
        if any(re.search(p, text.lstrip(), re.IGNORECASE)
               for p in _CHANGELOG_SECTION_PATTERNS)
    ]
    sections: list[tuple[int, int]] = []
    covered_until = -1
    for start, level in section_starts:
        if start < covered_until:
            continue
        end = _changelog_section_end(
            all_section_lines, start, level, len(lines))
        sections.append((start, end))
        covered_until = end
    return sections
def _heading_text(line: str) -> str:
    match = _HEADING_TEXT_RE.match(line)
    if match is None:
        return ""
    text = (match.group(2) or "").strip()
    closed = text.rstrip("#")
    if closed != text and (not closed or closed[-1].isspace()):
        text = closed.strip()
    return text
def _collect_heading_lines(
        lines: list[str], exempt_mask: set[int]) -> list[tuple[int, int, str]]:
    headings: list[tuple[int, int, str]] = [
        (i, len(match.group(1)), line)
        for i, line in enumerate(lines)
        if i not in exempt_mask and (match := _HEADING_RE.match(line))
    ]
    for start, underline, level in _setext_heading_blocks(lines, exempt_mask):
        heading_text = " ".join(
            line.strip() for line in lines[start:underline])
        headings.append((start, level, "#" * level + " " + heading_text))
    headings.sort(key=lambda heading: heading[0])
    return headings
def _build_section_map(lines: list[str],
                       exempt_mask: set[int],
                       extra: tuple[str, ...]) -> _SectionMap:
    headings = {
        i: (level, _heading_text(line))
        for i, level, line in _collect_heading_lines(lines, exempt_mask)
    }
    section_map = _SectionMap(extra)
    ancestors: list[tuple[int, bool]] = []
    current_section = ""
    for i in range(len(lines)):
        if i in headings:
            level, current_section = headings[i]
            while ancestors and ancestors[-1][0] >= level:
                ancestors.pop()
            inherited = ancestors[-1][1] if ancestors else False
            protected = inherited or _section_is_protected(
                current_section, extra)
            ancestors.append((level, protected))
        if ancestors and ancestors[-1][1]:
            section_map.protected_lines.add(i + 1)
        section_map[i + 1] = current_section
    return section_map
def _fence_syntax_line(line: str) -> str:
    if not isinstance(line, str):
        return ""
    cursor = 0
    while match := _CONTAINER_PREFIX_RE.match(line[cursor:]):
        cursor += match.end()
    return line[cursor:]
def _container_quote_depth(line: str) -> int:
    cursor = 0
    depth = 0
    while match := _CONTAINER_PREFIX_RE.match(line[cursor:]):
        if match.group(0).lstrip().startswith(">"):
            depth += 1
        cursor += match.end()
    return depth
def _update_list_context(
        stack: list[tuple[int, int]], match: re.Match,
        ) -> None:
    indent = len(match.group(1))
    marker = match.group(2)
    padding = match.group(3)
    content = match.group(4) or ""
    padding_width = (
        len(padding) if padding and len(padding) <= 4 and content else 1)
    content_indent = indent + len(marker) + padding_width
    while stack and indent < stack[-1][0]:
        stack.pop()
    if stack and indent == stack[-1][0]:
        stack[-1] = (indent, content_indent)
    else:
        stack.append((indent, content_indent))
def _line_opens_paragraph(line: str) -> bool:
    expanded = line.expandtabs(4).removesuffix("\r")
    if not expanded.strip():
        return False
    match = _LIST_CONTAINER_RE.match(expanded)
    if match:
        content = (match.group(4) or "").strip()
        if not content or len(match.group(3) or "") > 4:
            return False
    else:
        content = expanded.strip()
    return not (
        _HEADING_RE.match(content)
        or SETEXT_UNDERLINE_RE.match(content)
        or _THEMATIC_BREAK_RE.match(content))
def _line_interrupts_paragraph(line: str) -> bool:
    expanded = line.expandtabs(4).removesuffix("\r")
    if (_HEADING_RE.match(expanded)
            or _THEMATIC_BREAK_RE.match(expanded)
            or _FENCE_LINE_RE.match(expanded)):
        return True
    list_match = _LIST_CONTAINER_RE.match(expanded)
    if list_match is None:
        return False
    content = (list_match.group(4) or "").strip()
    padding = list_match.group(3) or ""
    if not content or len(padding) > 4:
        return False
    marker = list_match.group(2)
    return not marker[0].isdigit() or int(marker[:-1]) == 1


def _indented_code_mask(lines: list[str], fence_mask: set[int]) -> set[int]:
    mask: set[int] = set()
    quote_index = 0
    while quote_index < len(lines):
        if (not isinstance(lines[quote_index], str)
                or not _BLOCKQUOTE_PREFIX_RE.match(lines[quote_index])):
            quote_index += 1
            continue
        start = quote_index
        stripped_lines: list[str] = []
        while quote_index < len(lines):
            if not isinstance(lines[quote_index], str):
                break
            match = _BLOCKQUOTE_PREFIX_RE.match(lines[quote_index])
            if match:
                stripped_lines.append(lines[quote_index][match.end():])
                quote_index += 1
                continue
            probe = quote_index
            interrupted = False
            while (probe < len(lines) and isinstance(lines[probe], str)
                   and lines[probe].strip()
                   and not _BLOCKQUOTE_PREFIX_RE.match(lines[probe])):
                if _line_interrupts_paragraph(lines[probe]):
                    interrupted = True
                    break
                probe += 1
            if interrupted:
                stripped_lines.extend(lines[quote_index:probe])
                quote_index = probe
                break
            if (probe >= len(lines)
                    or not isinstance(lines[probe], str)
                    or not _BLOCKQUOTE_PREFIX_RE.match(lines[probe])):
                break
            stripped_lines.extend(lines[quote_index:probe])
            quote_index = probe
        local_fence_mask = {
            i - start for i in fence_mask if start <= i < quote_index}
        mask.update(
            start + i for i in _indented_code_mask(
                stripped_lines, local_fence_mask))
    list_stack: list[tuple[int, int]] = []
    paragraph_open = False
    in_code = False
    pending_blanks: list[int] = []
    for i, raw_line in enumerate(lines):
        if not isinstance(raw_line, str):
            paragraph_open = False
            in_code = False
            pending_blanks.clear()
            continue
        if quote_match := _BLOCKQUOTE_PREFIX_RE.match(raw_line):
            quote_line = raw_line.expandtabs(4).removesuffix("\r")
            quote_indent = len(quote_line) - len(quote_line.lstrip(" "))
            while list_stack and quote_indent < list_stack[-1][1]:
                list_stack.pop()
            quote_content = raw_line[quote_match.end():]
            paragraph_open = (
                i not in mask and i not in fence_mask
                and _line_opens_paragraph(quote_content))
            in_code = False
            pending_blanks.clear()
            continue
        if i in fence_mask:
            fence_line = raw_line.expandtabs(4).removesuffix("\r")
            fence_indent = len(fence_line) - len(fence_line.lstrip(" "))
            while list_stack and fence_indent < list_stack[-1][1]:
                list_stack.pop()
            paragraph_open = False
            in_code = False
            pending_blanks.clear()
            continue
        line = raw_line.expandtabs(4).removesuffix("\r")
        if not line.strip():
            paragraph_open = False
            if in_code:
                pending_blanks.append(i)
            continue
        indent = len(line) - len(line.lstrip(" "))
        base_indent = list_stack[-1][1] if list_stack else 0
        if in_code and indent >= base_indent + 4:
            mask.update(pending_blanks)
            pending_blanks.clear()
            mask.add(i)
            continue
        in_code = False
        pending_blanks.clear()
        if not paragraph_open:
            base_indent = list_stack[-1][1] if list_stack else 0
            if indent >= base_indent + 4:
                mask.add(i)
                in_code = True
                continue
        list_match = _LIST_CONTAINER_RE.match(line)
        is_heading = _HEADING_RE.match(line) is not None
        is_setext = SETEXT_UNDERLINE_RE.match(line.strip()) is not None
        is_break = _THEMATIC_BREAK_RE.match(line) is not None
        if list_match:
            _update_list_context(list_stack, list_match)
            paragraph_open = _line_opens_paragraph(line)
            continue
        if is_heading or is_setext or is_break:
            while list_stack and indent < list_stack[-1][1]:
                list_stack.pop()
            paragraph_open = False
            continue
        if paragraph_open:
            continue
        while list_stack and indent < list_stack[-1][1]:
            list_stack.pop()
        base_indent = list_stack[-1][1] if list_stack else 0
        if indent >= base_indent + 4:
            mask.add(i)
            in_code = True
        else:
            paragraph_open = True
    for i, raw_line in enumerate(lines):
        if i not in mask or not isinstance(raw_line, str):
            continue
        quote_match = _BLOCKQUOTE_PREFIX_RE.match(raw_line)
        if (quote_match is None
                or raw_line[quote_match.end():].strip()):
            continue
        probe = i + 1
        while probe < len(lines) and isinstance(lines[probe], str):
            candidate = lines[probe]
            candidate_quote = _BLOCKQUOTE_PREFIX_RE.match(candidate)
            candidate_content = (candidate[candidate_quote.end():]
                                 if candidate_quote else candidate)
            if candidate_content.strip():
                break
            probe += 1
        if (probe >= len(lines) or not isinstance(lines[probe], str)
                or not _BLOCKQUOTE_PREFIX_RE.match(lines[probe])):
            mask.discard(i)
    return mask
def code_block_mask(lines: list[str]) -> set[int]:
    if not isinstance(lines, (list, tuple)):
        return set()
    mask: set[int] = set()
    in_fence = False
    fence_char = ""
    fence_len = 0
    fence_list_indent: int | None = None
    fence_quote_depth = 0
    list_stack: list[tuple[int, int]] = []
    paragraph_open = False
    fence_lines = [_fence_syntax_line(line) for line in lines]
    for i, line in enumerate(fence_lines):
        source_line = lines[i]
        expanded = (source_line.expandtabs(4).removesuffix("\r")
                    if isinstance(source_line, str) else "")
        indent = len(expanded) - len(expanded.lstrip(" "))
        list_match = _LIST_CONTAINER_RE.match(expanded)
        empty_list_item = (
            list_match is not None
            and not (list_match.group(4) or "").strip())
        list_opens_container = list_match is not None and not (
            empty_list_item and paragraph_open)
        is_interrupt = (
            list_opens_container
            or _FENCE_LINE_RE.match(line) is not None
            or _HEADING_RE.match(expanded) is not None
            or SETEXT_UNDERLINE_RE.match(expanded.strip()) is not None
            or _THEMATIC_BREAK_RE.match(expanded) is not None
            or _BLOCKQUOTE_PREFIX_RE.match(expanded) is not None)
        if (in_fence and fence_quote_depth
                and _container_quote_depth(expanded) < fence_quote_depth):
            in_fence, fence_char, fence_len = False, "", 0
            fence_list_indent = None
            fence_quote_depth = 0
            paragraph_open = False
        if (in_fence and fence_list_indent is not None and expanded.strip()
                and indent < fence_list_indent and is_interrupt):
            in_fence, fence_char, fence_len = False, "", 0
            fence_list_indent = None
            paragraph_open = False
        if not in_fence:
            if not expanded.strip():
                paragraph_open = False
            elif list_opens_container:
                _update_list_context(list_stack, list_match)
                paragraph_open = _line_opens_paragraph(expanded)
            elif is_interrupt:
                while list_stack and indent < list_stack[-1][1]:
                    list_stack.pop()
                paragraph_open = False
            elif not paragraph_open:
                while list_stack and indent < list_stack[-1][1]:
                    list_stack.pop()
                paragraph_open = True
        was_in_fence = in_fence
        in_fence, fence_char, fence_len, line_kind = scan_fence_state(
            in_fence, fence_char, fence_len, line)
        if not was_in_fence and in_fence:
            fence_list_indent = list_stack[-1][1] if list_stack else None
            fence_quote_depth = _container_quote_depth(expanded)
            paragraph_open = False
        if in_fence or line_kind == "close":
            mask.add(i)
        if line_kind == "close":
            fence_list_indent = None
            fence_quote_depth = 0
    mask.update(_indented_code_mask(lines, mask))
    return mask
def _frontmatter_mask(lines: list[str]) -> set[int]:
    body_start = locate_frontmatter_body_start(lines)
    return set(range(min(body_start, len(lines))))
def _body_exempt_mask(lines: list[str]) -> set[int]:
    frontmatter = _frontmatter_mask(lines)
    body_start = len(frontmatter)
    body_code = {
        i + body_start for i in code_block_mask(lines[body_start:])
    }
    return frontmatter | body_code
def _inline_code_block_ranges(lines: list[str]) -> list[tuple[int, int]]:
    exempt = _body_exempt_mask(lines)
    setext_blocks = {
        start: underline + 1
        for start, underline, _level in _setext_heading_blocks(lines, exempt)
    }
    setext_lines = {
        i for start, end in setext_blocks.items() for i in range(start, end)
    }
    ranges: list[tuple[int, int]] = []
    start: int | None = None
    kind = ""
    list_content_indent: int | None = None
    list_stack: list[tuple[int, int]] = []
    def flush(end: int) -> None:
        nonlocal start
        if start is not None and start < end:
            ranges.append((start, end))
        start = None
    for i, line in enumerate(lines):
        if i in exempt or not line.strip():
            flush(i)
            kind = ""
            list_content_indent = None
            continue
        partial_container_setext = (
            start is not None and start < i
            and kind in {"list", "quote", "quote-list"})
        if i in setext_blocks and not partial_container_setext:
            flush(i)
            ranges.append((i, setext_blocks[i]))
            kind = ""
            list_content_indent = None
            continue
        if i in setext_lines and not partial_container_setext:
            continue
        syntax_line = line.removesuffix("\r")
        container_body = syntax_line.expandtabs(4)
        while quote_match := _BLOCKQUOTE_PREFIX_RE.match(container_body):
            container_body = container_body[quote_match.end():]
        content_line = _fence_syntax_line(syntax_line)
        is_quote = _BLOCKQUOTE_LEAD_RE.match(syntax_line) is not None
        empty_container = _LIST_CONTAINER_RE.match(content_line)
        empty_list_item = (empty_container is not None
                           and not (empty_container.group(4) or "").strip())
        if (not content_line.strip()
                or empty_list_item and kind != "paragraph"):
            flush(i)
            kind = ""
            list_content_indent = None
            continue
        if (_HEADING_RE.match(content_line)
                or _THEMATIC_BREAK_RE.match(content_line)
                or _TABLE_ROW_LEAD_RE.match(content_line)):
            flush(i)
            ranges.append((i, i + 1))
            kind = ""
            list_content_indent = None
            continue
        container_indent = (
            len(container_body) - len(container_body.lstrip(" ")))
        nested_setext = (
            start is not None
            and SETEXT_UNDERLINE_RE.match(container_body.strip()) is not None
            and (kind == "quote" and is_quote
                 or kind in {"list", "quote-list"}
                 and list_content_indent is not None
                 and container_indent >= list_content_indent))
        if nested_setext:
            flush(i + 1)
            kind = ""
            list_content_indent = None
            continue
        list_container = _LIST_CONTAINER_RE.match(container_body)
        if (_LIST_ITEM_LEAD_RE.match(container_body)
                and not (empty_list_item and kind == "paragraph")):
            flush(i)
            start = i
            kind = "quote-list" if is_quote else "list"
            list_stack.clear()
            if list_container is not None:
                _update_list_context(list_stack, list_container)
                list_content_indent = list_stack[-1][1]
            else:
                list_content_indent = None
            continue
        if is_quote and kind not in {"quote", "quote-list"}:
            flush(i)
            start = i
            kind = "quote"
            list_content_indent = None
            continue
        if start is None:
            start = i
            kind = "quote" if is_quote else "paragraph"
            list_content_indent = None
    flush(len(lines))
    return ranges
def _inline_code_spans_in_block(text: str) -> list[tuple[int, int]]:
    def collect_spans(scan_text: str) -> list[tuple[int, int]]:
        runs: list[tuple[int, int]] = []
        cursor = 0
        while cursor < len(scan_text):
            if scan_text[cursor] != "`":
                cursor += 1
                continue
            start = cursor
            while cursor < len(scan_text) and scan_text[cursor] == "`":
                cursor += 1
            runs.append((start, cursor))
        run_indices_by_length: dict[int, list[int]] = defaultdict(list)
        for index, (start, end) in enumerate(runs):
            run_indices_by_length[end - start].append(index)
        spans: list[tuple[int, int]] = []
        index = 0
        while index < len(runs):
            start, end = runs[index]
            backslashes = 0
            cursor = start - 1
            while cursor >= 0 and scan_text[cursor] == "\\":
                backslashes += 1
                cursor -= 1
            opening_start = start
            opening_length = end - start
            if backslashes % 2:
                opening_start += 1
                opening_length -= 1
            if opening_length:
                candidates = run_indices_by_length[opening_length]
                candidate_pos = bisect_right(candidates, index)
                if candidate_pos < len(candidates):
                    closing_index = candidates[candidate_pos]
                    spans.append((opening_start, runs[closing_index][1]))
                    index = closing_index + 1
                    continue
            index += 1
        return spans
    spans = collect_spans(text)
    masked = list(text)
    masked_destination = False
    for match in _MD_LINK_RE.finditer(text):
        label = match.group(1)
        trailing_backslashes = len(label) - len(label.rstrip("\\"))
        if (trailing_backslashes % 2
                or _MD_BLANK_LINE_RE.search(match.group(0))
                or _MD_LINK_DEST_RE.fullmatch(match.group(2)) is None):
            continue
        if any(start <= match.start() < end for start, end in spans):
            continue
        start, end = match.span(2)
        if any(span_start < start < span_end for span_start, span_end in spans):
            continue
        masked[start:end] = " " * (end - start)
        masked_destination = True
    return collect_spans("".join(masked)) if masked_destination else spans
def inline_code_spans(text: str) -> list[tuple[int, int]]:
    if not isinstance(text, str):
        return []
    lines = text.split("\n")
    offsets: list[int] = []
    offset = 0
    for line in lines:
        offsets.append(offset)
        offset += len(line) + 1
    spans: list[tuple[int, int]] = []
    for start, end in _inline_code_block_ranges(lines):
        block = "\n".join(lines[start:end])
        spans.extend(
            (offsets[start] + span_start, offsets[start] + span_end)
            for span_start, span_end in _inline_code_spans_in_block(block))
    return spans
def _unwrap_inline_code(line: str) -> str:
    spans = inline_code_spans(line)
    if not spans:
        return line
    parts: list[str] = []
    cursor = 0
    for start, end in spans:
        opening_end = start
        while line[opening_end] == "`":
            opening_end += 1
        delimiter_length = opening_end - start
        parts.append(line[cursor:start])
        parts.append(line[opening_end:end - delimiter_length])
        cursor = end
    parts.append(line[cursor:])
    return "".join(parts)
def _mask_inline_code(line: str) -> str:
    spans = inline_code_spans(line)
    if not spans:
        return line
    chars = list(line)
    for start, end in spans:
        chars[start:end] = [
            char if char in "\r\n" else " "
            for char in chars[start:end]
        ]
    return "".join(chars)
def _mask_inline_code_lines(lines: list[str]) -> list[str]:
    return _mask_inline_code("\n".join(lines)).split("\n")
def body_opens_with_code_block(body_text: str) -> bool:
    if not isinstance(body_text, str):
        return False
    normalized = body_text.replace("\r\n", "\n").replace("\r", "\n")
    lines = normalized.split("\n")
    setext_headings = {
        i for start, underline, _level in _setext_heading_blocks(lines, set())
        for i in range(start, underline + 1)
    }
    for i, line in enumerate(lines):
        stripped = line.strip()
        if (not stripped or _HEADING_RE.match(stripped)
                or i in setext_headings):
            continue
        return next(iter_fence_state([stripped]))[1]
    return False
def _flush_paragraph(
        paragraphs: list[tuple[int, int, str]], para_lines: list[str],
        para_start: int | None, end_idx: int) -> None:
    if para_start is not None and para_lines:
        paragraphs.append((para_start, end_idx, " ".join(para_lines)))
    para_lines.clear()
def _extract_paragraphs(lines: list[str],
                        exempt_mask: set[int]) -> list[tuple[int, int, str]]:
    paragraphs: list[tuple[int, int, str]] = []
    para_start: int | None = None
    para_lines: list[str] = []
    setext_marks = {
        i for start, underline, _level in _setext_heading_blocks(
            lines, exempt_mask)
        for i in range(start, underline + 1)
    }
    for i, line in enumerate(lines):
        if i in exempt_mask or i in setext_marks:
            _flush_paragraph(paragraphs, para_lines, para_start, i)
            para_start = None
            continue
        stripped = line.strip()
        if (_PARAGRAPH_BREAK_RE.match(line)
                or _NON_PARAGRAPH_LEAD_RE.match(stripped)
                or _THEMATIC_BREAK_RE.match(line.expandtabs(4))):
            _flush_paragraph(paragraphs, para_lines, para_start, i)
            para_start = None
        else:
            cleaned = _unwrap_inline_code(stripped).strip()
            if cleaned:
                para_start = para_start or i + 1
                para_lines.append(cleaned)
    _flush_paragraph(paragraphs, para_lines, para_start, len(lines))
    return paragraphs
def _paragraph_is_eligible(start: int, content: str,
                           changelog_sections: list[tuple[int, int]]) -> bool:
    return (len(content) >= _MIN_PARAGRAPH_CHARS
            and not _line_in_changelog(start - 1, changelog_sections))
def _eligible_paragraphs(
        paragraphs: list[tuple[int, int, str]],
        changelog_sections: list[tuple[int, int]],
        ) -> list[tuple[int, int, str]]:
    return [
        (start, end, content) for start, end, content in paragraphs
        if _paragraph_is_eligible(start, content, changelog_sections)
    ]
def _paragraph_hash_groups(
        paragraphs: list[tuple[int, int, str]],
        ) -> dict[str, list[tuple[int, int]]]:
    groups: dict[str, list[tuple[int, int]]] = defaultdict(list)
    for start, end, content in paragraphs:
        h = hashlib.md5(
            _normalize_text(content).encode(), usedforsecurity=False).hexdigest()
        groups[h].append((start, end))
    return groups
def _paragraph_snippet(lines: list[str], start: int, end: int) -> str:
    return "\n".join(lines[start - 1:min(start + 1, end)])
def _duplicate_item(line_start: int, line_end: int, section: str,
                    snippet: str, description: str,
                    metric_value: float = _DEFAULT_METRIC_VALUE,
                    ) -> DocCleanupItem:
    return DocCleanupItem(
        line_start=line_start, line_end=line_end,
        section=section,
        category="duplicate", severity="warning",
        description=description,
        snippet=snippet,
        suggestion="移除重复段落或合并为单一描述",
        metric_value=metric_value,
    )
def _duplicate_paragraph_items(
        lines: list[str],
        section_map: _SectionMap,
        occurrences: list[tuple[int, int]],
        ) -> list[DocCleanupItem]:
    if len(occurrences) < 2:
        return []
    first_start, first_end = occurrences[0]
    items: list[DocCleanupItem] = []
    for start, end in occurrences[1:]:
        section = section_map.get(start, "")
        if section_map.is_protected(section, start):
            continue
        items.append(_duplicate_item(
            start, end, section,
            _paragraph_snippet(lines, start, end),
            f"精确重复段落（与第 {first_start}-{first_end} 行内容相同）",
        ))
    return items
def _detect_duplicate_paragraphs(lines: list[str],
                                 section_map: _SectionMap,
                                 paragraphs: list[tuple[int, int, str]],
                                 ) -> list[DocCleanupItem]:
    items: list[DocCleanupItem] = []
    groups = _paragraph_hash_groups(paragraphs)
    for occurrences in groups.values():
        if len(occurrences) > 1:
            items.extend(_duplicate_paragraph_items(
                lines, section_map, occurrences))
    return items
@dataclass
class _SimilarityState:
    paras: list[tuple[int, int, str]]
    ngram_sets: list[set[str]]
    normalized_paras: list[str]
    section_map: _SectionMap
    best_by_target: dict[tuple[int, int], tuple[float, int, int]] = field(
        default_factory=dict)
def _best_similarity_pairs(
        paras: list[tuple[int, int, str]],
        section_map: _SectionMap,
        ) -> dict[tuple[int, int], tuple[float, int, int]]:
    state = _SimilarityState(
        paras=paras,
        ngram_sets=[_char_ngrams(c) for _, _, c in paras],
        normalized_paras=[_normalize_text(c) for _, _, c in paras],
        section_map=section_map,
    )
    for i in range(len(paras)):
        for j in range(i + 1, len(paras)):
            _update_best_pair(state, i, j)
    return state.best_by_target
def _update_best_pair(state: _SimilarityState, i: int, j: int) -> None:
    if state.normalized_paras[i] == state.normalized_paras[j]:
        return
    sim = jaccard(state.ngram_sets[i], state.ngram_sets[j])
    if sim < 0.80:
        return
    start, end = state.paras[j][0], state.paras[j][1]
    if state.section_map.is_protected(
            state.section_map.get(start, ""), start):
        return
    key = (start, end)
    if (key not in state.best_by_target
            or sim > state.best_by_target[key][0]):
        state.best_by_target[key] = (
            sim, state.paras[i][0], state.paras[i][1])
def _similar_items_from_pairs(
        lines: list[str],
        section_map: _SectionMap,
        best_by_target: dict[tuple[int, int], tuple[float, int, int]],
        ) -> list[DocCleanupItem]:
    items: list[DocCleanupItem] = []
    for (s_start, s_end), (sim, f_start, f_end) in best_by_target.items():
        items.append(_duplicate_item(
            s_start, s_end, section_map.get(s_start, ""),
            _paragraph_snippet(lines, s_start, s_end),
            f"疑似重复段落（与第 {f_start}-{f_end} 行 Jaccard 相似度 {sim:.0%}）",
            metric_value=sim,
        ))
    return items
def _iter_heading_texts(lines: list[str], exempt_mask: set[int]):
    for i, depth, heading_line in _collect_heading_lines(lines, exempt_mask):
        yield i, depth, _heading_text(heading_line)
def _collect_lint_headings(lines: list[str], exempt_mask: set[int],
                           changelog_sections: list[tuple[int, int]],
                           ) -> tuple[dict[str, list[int]], list[tuple[int, int]]]:
    heading_texts: dict[str, list[int]] = defaultdict(list)
    heading_depths: list[tuple[int, int]] = []
    for i, depth, text in _iter_heading_texts(lines, exempt_mask):
        if _line_in_changelog(i, changelog_sections):
            continue
        heading_texts[_normalize_text(text)].append(i + 1)
        heading_depths.append((depth, i + 1))
    return heading_texts, heading_depths
def _unprotected_duplicate_heading_occurrences(
        heading_texts: dict[str, list[int]],
        section_map: _SectionMap,
        ) -> list[tuple[str, int, int]]:
    occurrences_out: list[tuple[str, int, int]] = []
    for text, occurrences in heading_texts.items():
        if not text:
            continue
        for line_no in occurrences[1:]:
            if section_map.is_protected(
                    section_map.get(line_no, ""), line_no):
                continue
            occurrences_out.append((text, line_no, occurrences[0]))
    return occurrences_out
def _lint_duplicate_headings(lines: list[str],
                             section_map: _SectionMap,
                             heading_texts: dict[str, list[int]],
                             ) -> list[DocCleanupItem]:
    items: list[DocCleanupItem] = []
    for text, line_no, first_line in _unprotected_duplicate_heading_occurrences(
            heading_texts, section_map):
        items.append(DocCleanupItem(
            line_start=line_no, line_end=line_no,
            section=section_map.get(line_no, ""),
            category="lint", severity="info",
            description=f"重复标题 '{text[:50]}'（首次出现在第 {first_line} 行）",
            snippet=lines[line_no - 1].strip(),
            suggestion="合并重复标题下的内容，或使用不同标题",
        ))
    return items
def _lint_heading_jumps(lines: list[str],
                        section_map: _SectionMap,
                        heading_depths: list[tuple[int, int]],
                        ) -> list[DocCleanupItem]:
    items: list[DocCleanupItem] = []
    for idx in range(len(heading_depths) - 1):
        d1, l1 = heading_depths[idx]
        d2, l2 = heading_depths[idx + 1]
        if d2 > d1 + 1:
            section = section_map.get(l2, "")
            if section_map.is_protected(section, l2):
                continue
            items.append(DocCleanupItem(
                line_start=l2, line_end=l2,
                section=section,
                category="lint", severity="info",
                description=f"标题层级跳跃：h{d1} → h{d2}（缺少 h{d1 + 1}）",
                snippet=lines[l2 - 1].strip(),
                suggestion=f"在第 {l1} 行和第 {l2} 行之间添加 h{d1 + 1} 级标题",
            ))
    return items
def _iter_blank_runs(lines: list[str], skip_line) -> list[tuple[int, int]]:
    def _is_body_blank(pair: tuple[int, str]) -> bool:
        index, line = pair
        return not skip_line(index) and not line.strip()
    runs: list[tuple[int, int]] = []
    for is_blank, group in groupby(enumerate(lines), key=_is_body_blank):
        if not is_blank:
            continue
        members = list(group)
        if len(members) >= 3:
            runs.append((members[0][0] + 1, len(members)))
    return runs
def _lint_blank_runs(lines: list[str],
                     section_map: _SectionMap,
                     exempt_mask: set[int],
                     changelog_sections: list[tuple[int, int]],
                     ) -> list[DocCleanupItem]:
    items: list[DocCleanupItem] = []
    for blank_start, blank_run in _iter_blank_runs(
            lines, lambda i: _line_exempt(
                i, exempt_mask, changelog_sections)):
        section = section_map.get(blank_start, "")
        if section_map.is_protected(section, blank_start):
            continue
        items.append(DocCleanupItem(
            line_start=blank_start, line_end=blank_start + blank_run - 1,
            section=section,
            category="lint", severity="info",
            description=f"连续 {blank_run} 行空白（建议最多 1 行）",
            snippet="(空行区域)",
            suggestion="保留最多 1 个空行，删除多余空行",
        ))
    return items
def _list_marker_item(line: str, line_no: int, bullet: str,
                      prev_bullet: str, section: str) -> DocCleanupItem:
    return DocCleanupItem(
        line_start=line_no, line_end=line_no,
        section=section,
        category="lint", severity="info",
        description=f"列表标记不一致：使用 '{bullet}' 而前一项使用 '{prev_bullet}'",
        snippet=line.strip(),
        suggestion="统一使用同一种列表标记（推荐 '-'）",
    )
def _marker_break_item(
        line: str, index: int, prev_bullet: tuple[int, str] | None,
        indent: int, bullet: str, section_map: _SectionMap,
        ) -> DocCleanupItem | None:
    if (prev_bullet is None or indent != prev_bullet[0]
            or bullet == prev_bullet[1]):
        return None
    section = section_map.get(index + 1, "")
    if section_map.is_protected(section, index + 1):
        return None
    return _list_marker_item(line, index + 1, bullet, prev_bullet[1], section)
def _lint_list_markers(lines: list[str],
                       section_map: _SectionMap,
                       exempt_mask: set[int],
                       changelog_sections: list[tuple[int, int]],
                       ) -> list[DocCleanupItem]:
    items: list[DocCleanupItem] = []
    prev_bullet: tuple[int, str] | None = None
    for i, line in enumerate(lines):
        if _line_exempt(i, exempt_mask, changelog_sections):
            prev_bullet = None
            continue
        if _THEMATIC_BREAK_RE.match(line):
            prev_bullet = None
            continue
        m = _LIST_MARKER_RE.match(line)
        if not m:
            continuation_indent = len(line) - len(line.lstrip(" \t"))
            if (prev_bullet is not None and line.strip()
                    and continuation_indent > prev_bullet[0]):
                continue
            prev_bullet = None
            continue
        indent, bullet = len(m.group(1)), m.group(2)
        item = _marker_break_item(
            line, i, prev_bullet, indent, bullet, section_map)
        if item is not None:
            items.append(item)
        prev_bullet = (indent, bullet)
    return items
def _entropy_structure_metrics(lines: list[str], exempt_mask: set[int],
                               changelog_sections: list[tuple[int, int]],
                               metrics: DocEntropyMetrics, *,
                               section_map: _SectionMap,
                               ) -> None:
    heading_texts, heading_depths = _collect_lint_headings(
        lines, exempt_mask, changelog_sections)
    if not heading_depths:
        return
    depths = [depth for depth, _line_no in heading_depths]
    mean_depth = sum(depths) / len(depths)
    variance = sum((depth - mean_depth) ** 2 for depth in depths) / len(depths)
    metrics.heading_depth_variance = variance
    metrics.structure_entropy = min(1.0, variance / 4.0)
    metrics.duplicate_heading_count = len(
        _unprotected_duplicate_heading_occurrences(
            heading_texts, section_map))
def _semantic_redundancy_score(report: DocCleanupReport,
                               paragraph_total: int) -> float:
    if paragraph_total <= 0:
        return 0.0
    dup_count = sum(1 for i in report.items if i.category == "duplicate")
    return min(1.0, dup_count / paragraph_total)
def _count_blank_line_clusters(lines: list[str], exempt_mask: set[int],
                               changelog_sections: list[tuple[int, int]], *,
                               section_map: _SectionMap,
                               ) -> int:
    return sum(
        1 for start, _run in _iter_blank_runs(
            lines, lambda i: _line_exempt(i, exempt_mask, changelog_sections))
        if not section_map.is_protected(section_map.get(start, ""), start))
def _stale_freshness_score(report: DocCleanupReport,
                           metrics: DocEntropyMetrics) -> None:
    stale_items = [i for i in report.items if i.category == "stale_date"]
    metrics.stale_date_count = len(stale_items)
    if stale_items:
        total_age = sum(i.metric_value for i in stale_items)
        avg_age = total_age / len(stale_items)
        metrics.freshness_score = max(0, 100 - avg_age / 10)
    else:
        metrics.freshness_score = 100.0
def _total_health_score(metrics: DocEntropyMetrics) -> float:
    return (
        0.25 * (100 - metrics.structure_entropy * 100) +
        0.25 * (100 - metrics.semantic_redundancy * 100) +
        0.25 * metrics.freshness_score +
        0.25 * max(0, 100 - metrics.blank_line_clusters * 5 -
                   metrics.duplicate_heading_count * 10)
    )
def _parse_stale_age_days(m: re.Match) -> tuple[int, datetime] | None:
    try:
        y, mo, d = int(m.group(1)), int(m.group(2)), int(m.group(3))
        date_obj = datetime(y, mo, d, tzinfo=UTC)
        return (datetime.now(UTC) - date_obj).days, date_obj
    except ValueError:
        _log.debug("[DocCleaner] 非法日期 %r 跳过过期检测", m.group(0))
        return None
def _changelog_section_end(all_section_lines: list[tuple[int, int]],
                           start: int, level: int,
                           last_line_no: int) -> int:
    for sec_line, sec_level in all_section_lines:
        if sec_line > start and sec_level <= level:
            return sec_line
    return last_line_no

from __future__ import annotations

import ast
import hashlib
import logging
import os
import re
import time
from collections.abc import Callable, Iterator

from jwsgj.build_skill_api_contract import (
    collect_api_names,
    collect_skill_py_basenames,
    extract_param_names,
    extract_py_refs,
    get_scan_files,
    has_code_surface,
    has_scan_files,
    is_script_only_skill,
    iter_scan_function_entries,
    strip_url_tokens,
)
from jwsgj.build_text_document import (
    _DEFAULT_DOC_PROFILE,
    _GENERIC_BOUNDARY_RE,
    _RESOURCE_DIR_ALT,
    _body_h2_titles,
    _local_md_refs,
    _normalize_sections_found,
    _ref_escapes_skill_dir,
    identifier_pattern,
    iter_atx_headings,
    iter_fenced_blocks,
    strip_fenced_blocks,
)
from jwsgj.build_text_scoring import (
    _GENERIC_USAGE_RE,
    get_standard_sections,
)
from jwsgj.diag_shared_ast_nodes import iter_module_scope_nodes
from jwsgj.diag_shared_source_core import (
    _l5_markdown_cells,
    _markdown_table_cells,
)
from jwsgj.diag_types_defs import (
    DocQualityIssue,
    SubDimensionScore,
    make_noscan_issue,
    record_dimension,
)
from jwsgj.diag_types_normalize import normalize_entry_inputs
from jwsgj.diag_types_vocab import (
    NO_CODE_DETAIL,
    NO_CODE_SCORE,
)
from jwsgj.log_config import write_module_run
from jwsgj.runtime_scope import (
    is_test_source_basename,
    py_stem,
    read_diagnostic_source_strict,
)

__all__ = [
    'RECOMMENDED_SECTIONS',
    'REQUIRED_SECTIONS',
    'check_c9_c6_c7',
    'diag_capture_c1c3',
    'diag_capture_c4c5',
    'diag_capture_fallback',
    'diag_loading_l1l2',
    'diag_loading_l3l4',
    'diag_loading_l5',
]
_log = logging.getLogger(__name__)
_LOADING_NOSCAN_SCORE = 50.0
_SECTION_REGISTRY = get_standard_sections()
_RECOMMENDED_SECTION_KEYS = (
    "file_structure", "use_cases", "key_constraints", "design_principles",
)
REQUIRED_SECTIONS: list[str] = [
    s["title"] for s in _SECTION_REGISTRY
    if s.get("required") and s.get("key") != "description_block" and s.get("title")
]
RECOMMENDED_SECTIONS: list[str] = [
    s["title"] for s in _SECTION_REGISTRY
    if s.get("key") in _RECOMMENDED_SECTION_KEYS and s.get("title")
]
_SECTION_TITLE_ALIASES = {
    "capability_boundary": (
        "技能能力边界", "能力边界", "capability boundary",
        "scope and limitations", "in scope", "out of scope"),
    "agent_guidance": (
        "Agent 决策指引", "agent decision guide", "agent guidance",
        "decision guide"),
    "trigger_conditions": (
        "触发条件", "何时使用", "trigger conditions",
        "when to use", "when not to use"),
    "trigger_examples": (
        "触发示例", "用户示例", "trigger examples", "user examples"),
    "quick_start": (
        "快速入门", "快速开始", "quick start", "quickstart",
        "getting started"),
    "domain_overview": (
        "域总览", "模块总览", "模块概览", "架构总览", "模块索引",
        "能力总览", "架构", "概述", "总览", "domain overview",
        "module overview", "architecture overview", "module index",
        "capability overview", "overview", "architecture"),
    "file_structure": (
        "文件结构", "目录结构", "file structure", "project structure",
        "directory structure", "file tree"),
    "use_cases": (
        "典型应用场景", "应用场景", "使用场景", "use cases",
        "usage scenarios", "examples"),
    "script_inventory": (
        "脚本清单", "script inventory", "script catalog", "scripts"),
    "script_vs_api": (
        "脚本 vs API 决策指引", "脚本 vs api", "script vs api",
        "scripts vs api", "cli vs api"),
    "key_constraints": (
        "关键约束", "核心约束", "key constraints", "constraints"),
    "design_principles": (
        "设计原则", "核心原则", "design principles"),
    "gotchas": ("Gotchas", "常见陷阱", "known issues", "pitfalls"),
    "six_dim_diagnosis": (
        "六维可发现性诊断", "six-dimension discoverability",
        "six dim diagnosis"),
    "module_details": (
        "各模块详解", "模块能力详解", "模块详解", "模块", "详解",
        "api 参考", "api 文档", "module details", "module reference",
        "api reference", "module", "detail"),
}
_C4_KEY_SECTION_KEYS = frozenset({
    "capability_boundary", "quick_start", "domain_overview", "use_cases"})
def _split_h2_sections(body_text: str) -> list[tuple[str, str]]:
    headings = [(start, title, end)
                for start, end, _level, title
                in iter_atx_headings(body_text, level=2)]
    sections: list[tuple[str, str]] = []
    for i, (_start, title, head_end) in enumerate(headings):
        if i + 1 < len(headings):
            raw = body_text[head_end:headings[i + 1][0]]
            content = raw.removesuffix('\n')
        else:
            content = body_text[head_end:]
        sections.append((title, content))
    return sections
def _resolve_sections_found(body_text, sections_found):
    sections = _normalize_sections_found(sections_found)
    return sections or _split_h2_sections(body_text or "")
def _section_key(title) -> str:
    normalized = str(title or "").casefold()
    best_key = ""
    best_len = 0
    for key, aliases in _SECTION_TITLE_ALIASES.items():
        for alias in aliases:
            candidate = alias.casefold()
            if (candidate and candidate in normalized
                    and len(candidate) > best_len):
                best_key, best_len = key, len(candidate)
    return best_key
def _section_keys(title) -> set[str]:
    """全部命中键: 合并标题(如“域总览与文件结构”)同时满足多个章节。"""
    normalized = str(title or "").casefold()
    return {
        key for key, aliases in _SECTION_TITLE_ALIASES.items()
        if any(alias.casefold() in normalized for alias in aliases if alias)
    }
def _rule_suffix(label, limit: int) -> str:
    text = str(label or "").strip()
    if len(text) <= limit:
        return text
    digest = hashlib.sha1(text.encode("utf-8")).hexdigest()[:6]
    return f"{text[:limit]}-{digest}"
def _registry_section_key(title: str) -> str:
    return next((str(section.get("key") or "")
                 for section in _SECTION_REGISTRY
                 if section.get("title") == title), "")
def _standard_section_keys(titles) -> frozenset[str]:
    return frozenset(key for key in map(_registry_section_key, titles) if key)
def _c1_router(body_text: str):
    links = len(_local_md_refs(body_text or ""))
    if links >= 1:
        return 100.0, []
    return 60.0, [DocQualityIssue(
        category="capture", rule_id="SD-C1-ROUTER", severity="medium",
        description="路由型文档未包含任何本地 Markdown 引用",
        suggestion="在正文中链接具体操作指南（如 create-docx.md）",
        location="正文",
    )]
def _c1_general(body_text: str, sections_found) -> tuple:
    prose = strip_fenced_blocks(body_text or "")
    titles = [str(t) for t, _c in (sections_found or [])]
    if not titles:
        titles = _body_h2_titles(prose)
    has_usage = (any(_GENERIC_USAGE_RE.search(t) for t in titles)
                 or bool(_GENERIC_USAGE_RE.search(prose)))
    has_boundary = bool(_GENERIC_BOUNDARY_RE.search(prose))
    has_structure = len(titles) >= 2
    score = 100.0
    issues: list[DocQualityIssue] = []
    if not has_usage:
        score -= 30
        issues.append(DocQualityIssue(
            category="capture", rule_id="SD-C1-USAGE", severity="medium",
            description="缺少使用入口/操作说明章节",
            suggestion="补充快速开始、使用方法或命令速查章节",
            location="正文"))
    if not has_boundary:
        score -= 20
        issues.append(DocQualityIssue(
            category="capture", rule_id="SD-C1-BOUNDARY", severity="low",
            description="正文未声明能力边界",
            suggestion="补充不支持/不适用/仅支持等边界说明",
            location="正文"))
    if not has_structure:
        score -= 20
        issues.append(DocQualityIssue(
            category="capture", rule_id="SD-C1-STRUCT", severity="medium",
            description="正文缺少二级章节结构",
            suggestion="用 ## 二级标题组织操作说明",
            location="正文"))
    return max(0.0, score), issues
_SUMMARY_MODULE_COUNT_RE = re.compile(
    r'扫描统计|(?:\*\*)?\s*(?:共|总计|合计)?\s*(?:\*\*)?'
    r'\d[\d,，]*(?:\*\*)?\s*个\s*(?:可导入\s*)?模块'
    r'(?=$|[ \t|，。；、,;:：)）\]】」》*])',
    re.MULTILINE)
_SUMMARY_MODULE_COUNT_EN_RE = re.compile(
    r'\b\d[\d,]*\s+(?:importable\s+)?modules?\b'
    r'|\bmodules?\s*(?:count|total)?\s*[:=]\s*\d[\d,]*\b',
    re.IGNORECASE)
_SUMMARY_FILE_COUNT_RE = re.compile(
    r'\d[\d,，]*\s*个\s*(?:可导入\s*)?(?:\.py\s*)?文件'
    r'|\b\d[\d,]*\s+(?:importable\s+)?files?\b'
    r'|\bfiles?\s*(?:count|total)?\s*[:=]\s*\d[\d,]*\b',
    re.IGNORECASE)
def _has_scan_summary(text) -> bool:
    if not isinstance(text, str):
        return False
    return bool(_SUMMARY_MODULE_COUNT_RE.search(text)
                or _SUMMARY_MODULE_COUNT_EN_RE.search(text)
                or _SUMMARY_FILE_COUNT_RE.search(text))
def _scan_summary_counts(text) -> set[int]:
    if not isinstance(text, str):
        return set()
    counts: set[int] = set()
    for pattern in (_SUMMARY_MODULE_COUNT_RE, _SUMMARY_MODULE_COUNT_EN_RE,
                    _SUMMARY_FILE_COUNT_RE):
        for match in pattern.finditer(text):
            number = re.search(r'\d[\d,，]*', match.group(0))
            if number is None:
                continue
            digits = re.sub(r'[,，]', '', number.group(0))
            if len(digits) <= 15:
                counts.add(int(digits))
    return counts
def _missing_section_issues(missing: list[str], kind: str, rule_prefix: str,
                            severity: str, suggestion: str) -> list[DocQualityIssue]:
    return [DocQualityIssue(
        category="capture", rule_id=f"{rule_prefix}-{sec}", severity=severity,
        description=f"缺少{kind}章节: {sec}",
        suggestion=suggestion.format(sec=sec),
        location="正文",
    ) for sec in missing]
_PLACEHOLDER_SECTION_RE = re.compile(
    r'^(?:(?:[（(]?\s*(?:待|to\s*be)\s*(?:从|自|由)?.{0,30}'
    r'(?:填充|补充|生成|填写|完善)\s*[）)]?)|(?:todo|tbd))[.。!！]?$',
    re.IGNORECASE)
def _is_placeholder_section(content) -> bool:
    return bool(isinstance(content, str) and content.strip()
                and _PLACEHOLDER_SECTION_RE.fullmatch(content.strip()))
def _found_section_keys(sections_found) -> set[str]:
    found: set[str] = set()
    for title, content in sections_found:
        if not (isinstance(content, str) and content.strip()
                and not _is_placeholder_section(content)):
            continue
        # 合并标题(域总览与文件结构)需同时计入其覆盖的每个章节键
        found |= _section_keys(title)
    return found
def _c1_missing_sections(body_text, sections_found=None) -> tuple:
    c1_prose = strip_fenced_blocks(body_text)
    sections = (sections_found if sections_found
                else _split_h2_sections(body_text))
    found_keys = _found_section_keys(sections)
    c1_missing_required = [s for s in REQUIRED_SECTIONS
                           if _registry_section_key(s) not in found_keys]
    c1_missing_recommended = [s for s in RECOMMENDED_SECTIONS
                              if _registry_section_key(s) not in found_keys]
    return c1_prose, c1_missing_required, c1_missing_recommended
def diag_capture_c1c3(body_text, all_issues, api_scan, sections_found=None,
                      *, doc_profile: str = _DEFAULT_DOC_PROFILE
                      ) -> list[SubDimensionScore]:
    sections_found, all_issues = normalize_entry_inputs(sections_found, all_issues)
    sections_found = _resolve_sections_found(body_text, sections_found)
    results: list[SubDimensionScore] = []
    c1_prose, c1_missing_required, c1_missing_recommended = (
        _c1_missing_sections(body_text, sections_found))
    if doc_profile == "template":
        c1_score = max(0.0, 100.0 - len(c1_missing_required) * 20.0
                       - len(c1_missing_recommended) * 5.0)
        c1_issues = _missing_section_issues(
            c1_missing_required, "必需", "SD-C1-REQ", "high",
            "添加 '## {sec}' 章节")
        c1_issues += _missing_section_issues(
            c1_missing_recommended, "推荐", "SD-C1-REC", "low",
            "建议添加 '## {sec}' 章节提升文档完整性")
        c1_detail = (f"必需章节缺{len(c1_missing_required)}/{len(REQUIRED_SECTIONS)}, "
                     f"推荐章节缺{len(c1_missing_recommended)}/{len(RECOMMENDED_SECTIONS)}")
    elif doc_profile == "router":
        c1_score, c1_issues = _c1_router(body_text)
        c1_detail = "路由型文档：按本地引用指南校验"
    else:
        c1_score, c1_issues = _c1_general(body_text, sections_found)
        c1_detail = "通用文档：校验使用入口/能力边界/章节结构"
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id="C1", dim_name="标准章节完整性", category="capture",
        score=c1_score, weight=0.25,
        issues=c1_issues,
        detail=c1_detail,
    ))
    record_dimension(results, all_issues, _check_section_depth(
        REQUIRED_SECTIONS, RECOMMENDED_SECTIONS, sections_found,
        doc_profile=doc_profile))
    if doc_profile == "router":
        c3_score, counts = 80.0, (0, 0, 0)
        c3_issues: list[DocQualityIssue] = []
        c3_detail = "路由型文档：结构化内容下沉到引用指南"
    else:
        c3_score, counts = _compute_c3_score(c1_prose, body_text, api_scan)
        c3_issues = _c3_issues(counts[0], counts[1])
        c3_detail = (f"表格={counts[0]}, 代码块={counts[1]}, "
                     f"列表项={counts[2]}")
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id="C3", dim_name="结构化元素使用", category="capture",
        score=c3_score, weight=0.15,
        issues=c3_issues,
        detail=c3_detail,
    ))
    _log.info("[SkillDoc][Capture] C1/C2/C3 完成: %s",
              ", ".join(f"{r.dim_id}={r.score:.1f}" for r in results))
    return results
def diag_capture_c4c5(body_text, all_issues, api_scan, sections_found=None,
                      *, doc_profile: str = _DEFAULT_DOC_PROFILE,
                      expanded_body=None) -> list[SubDimensionScore]:
    sections_found, all_issues = normalize_entry_inputs(sections_found, all_issues)
    sections_found = _resolve_sections_found(body_text, sections_found)
    results: list[SubDimensionScore] = []
    c4_score, c4_detail, c4_issues = _compute_c4_section_richness(
        sections_found, doc_profile)
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id="C4", dim_name="章节内容丰富度", category="capture",
        score=c4_score, weight=0.15,
        issues=c4_issues,
        detail=c4_detail,
    ))
    c5_score, c5_detail, c5_issues = _compute_c5_module_coverage(
        expanded_body if isinstance(expanded_body, str) else body_text,
        api_scan, doc_profile=doc_profile)
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id="C5", dim_name="模块详解覆盖度", category="capture",
        score=c5_score, weight=0.15,
        issues=c5_issues,
        detail=c5_detail,
    ))
    _log.info("[SkillDoc][Capture] C4/C5 完成: %s",
              ", ".join(f"{r.dim_id}={r.score:.1f}" for r in results))
    return results
def check_c9_c6_c7(sections_found: list | None = None,
                   api_scan: dict | None = None,
                   all_issues: list | None = None,
                   skill_dir: str = "",
                   *, doc_profile: str = _DEFAULT_DOC_PROFILE
                   ) -> list[SubDimensionScore]:
    sections_found, all_issues = normalize_entry_inputs(sections_found, all_issues)
    sections_found = _normalize_sections_found(sections_found)
    results = []
    api_files = get_scan_files(api_scan)
    no_code = has_code_surface(api_scan) is False and doc_profile != "router"
    if no_code:
        c9_score, c9_detail, c9_issues = NO_CODE_SCORE, NO_CODE_DETAIL, []
    elif doc_profile == "router":
        c9_score, c9_detail, c9_issues = 70.0, "路由型文档：代码文档下沉到引用指南", []
    else:
        c9_score, c9_detail, c9_issues = _compute_c9_semantic_depth(api_files)
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id="C9", dim_name="模块语义文档化深度", category="capture",
        score=c9_score, weight=0.10,
        issues=c9_issues,
        detail=c9_detail,
    ))
    if no_code:
        c6_score, c6_detail, c6_issues = NO_CODE_SCORE, NO_CODE_DETAIL, []
    elif doc_profile == "router":
        c6_score, c6_detail, c6_issues = 70.0, "路由型文档：参数文档下沉到引用指南", []
    else:
        c6_score, c6_detail, c6_issues = _compute_c6_param_coverage(api_scan, sections_found)
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id="C6", dim_name="参数文档完整性", category="capture",
        score=c6_score, weight=0.05,
        issues=c6_issues,
        detail=c6_detail,
    ))
    if no_code:
        c7_score, c7_detail, c7_issues = NO_CODE_SCORE, NO_CODE_DETAIL, []
    else:
        c7_score, c7_detail, c7_issues = _compute_c7_cross_coverage(
            sections_found, api_files, skill_dir, doc_profile=doc_profile)
    record_dimension(results, all_issues, SubDimensionScore(
        dim_id="C7", dim_name="章节间交叉覆盖度", category="capture",
        score=c7_score, weight=0.10,
        issues=c7_issues,
        detail=c7_detail,
    ))
    _log.info("[SkillDoc][Capture] C9/C6/C7 完成: %s",
              ", ".join(f"{r.dim_id}={r.score:.1f}" for r in results))
    return results
def diag_capture_fallback(body_text: str) -> list[DocQualityIssue]:
    body_text, _ = normalize_entry_inputs(body_text, [], text=True)
    issues: list[DocQualityIssue] = []
    if not body_text or len(body_text.strip()) < 50:
        _log.warning("[SkillDoc][Capture] CR-001 命中: 正文过短或缺失（len=%d）",
                     len(body_text) if body_text else 0)
        issues.append(DocQualityIssue(
            category="capture", rule_id="CR-001", severity="critical",
            description="正文过短或缺失", suggestion="补充技能使用说明和工作流",
            location="正文",
        ))
    return issues
def _scan_rel_path(value) -> str:
    return value.replace("\\", "/") if isinstance(value, str) else ""
_MD_TABLE_SEPARATOR_CELL_RE = re.compile(r':?-+:?')
def _iter_markdown_tables(text: str) -> Iterator[list[str]]:
    lines = text.splitlines()
    index = 0
    while index + 1 < len(lines):
        header = _markdown_table_cells(lines[index])
        separator = _markdown_table_cells(lines[index + 1])
        if (len(header) < 2 or len(header) != len(separator)
                or not all(_MD_TABLE_SEPARATOR_CELL_RE.fullmatch(cell)
                           for cell in separator)):
            index += 1
            continue
        rows = [lines[index], lines[index + 1]]
        index += 2
        while index < len(lines):
            cells = _markdown_table_cells(lines[index])
            if len(cells) != len(header):
                break
            rows.append(lines[index])
            index += 1
        yield rows
def _compute_c3_score(c1_prose: str, body_text: str,
                      api_scan) -> tuple[float, tuple[int, int, int]]:
    tables = list(_iter_markdown_tables(c1_prose))
    table_count = len(tables)
    code_block_count = len(iter_fenced_blocks(body_text))
    list_count = len(re.findall(r'^\s*[-*]\s', c1_prose, re.MULTILINE))
    c3_score = (
        min(30.0, table_count * 6.0)
        + min(25.0, code_block_count * 5.0)
        + min(20.0, list_count * 2.0)
    )
    api_files = get_scan_files(api_scan)
    if api_files:
        actual_names = collect_api_names(api_scan, include_module_names=True)
        api_related_tables = 0
        table_rows = [row for rows in tables for row in rows]
        for row in table_rows:
            if any(identifier_pattern(name).search(row)
                   for name in actual_names):
                api_related_tables += 1
        c3_score += min(25.0, api_related_tables * 3.0)
    else:
        c3_score += 10.0
    return c3_score, (table_count, code_block_count, list_count)
def _c3_issues(table_count: int, code_block_count: int) -> list[DocQualityIssue]:
    issues = []
    if table_count == 0:
        issues.append(DocQualityIssue(
            category="capture", rule_id="SD-C3-TBL", severity="medium",
            description="正文中无表格，结构化信息展示不足",
            suggestion="使用表格展示模块清单、场景映射等结构化数据",
            location="正文",
        ))
    if code_block_count == 0:
        issues.append(DocQualityIssue(
            category="capture", rule_id="SD-C3-CODE", severity="medium",
            description="正文中无代码示例",
            suggestion="添加Python/bash代码块展示调用方式",
            location="正文",
        ))
    return issues
def _c4_prose_lines(sec_prose: str) -> list[str]:
    return [
        ln for ln in sec_prose.split('\n')
        if ln.strip()
        and not ln.strip().startswith('|')
        and not ln.strip().startswith('#')
        and not ln.strip().startswith('```')
    ]
_C4_DESC_FACTOR_RE = re.compile(
    r'[^\s\-*+][^\n]*?[—\-:：]\s*(?![|:\-\s])[^`\n]{10,}')
def _c4_section_factors(sec_content: str) -> float:
    factors = 0.0
    sec_prose = strip_fenced_blocks(sec_content)
    prose_lines = _c4_prose_lines(sec_prose)
    if next(_iter_markdown_tables(sec_prose), None) is not None:
        factors += 25.0
    if iter_fenced_blocks(sec_content):
        factors += 25.0
    if _C4_DESC_FACTOR_RE.search("\n".join(prose_lines)):
        factors += 20.0
    if re.search(r'^\s*[-*]\s', sec_prose, re.MULTILINE):
        factors += 15.0
    if sum(len(ln) for ln in prose_lines) > 50:
        factors += 15.0
    return factors
def _c4_issue_for(sec_title_stripped: str, score: float) -> DocQualityIssue | None:
    if score >= 40.0:
        return None
    return DocQualityIssue(
        category="capture", rule_id=f"SD-C4-{_rule_suffix(sec_title_stripped, 10)}",
        severity="medium",
        description=f"章节 '{sec_title_stripped}' 内容丰富度不足（{score:.0f}/100）",
        suggestion="补充表格、代码示例、函数签名或列表项以提升内容密度",
        location=f"正文: ## {sec_title_stripped}",
    )
def _compute_c4_section_richness(sections_found, doc_profile: str):
    if doc_profile == "router":
        return 80.0, "路由型文档：章节内容丰富度下沉到引用指南", []
    key_sections = _c4_key_section_scores(sections_found, doc_profile)
    c4_issues = [
        issue for title, score in key_sections
        if (issue := _c4_issue_for(title, score)) is not None
    ]
    c4_score = (round(sum(s for _t, s in key_sections) / len(key_sections), 1)
                if key_sections else 80.0)
    detail = (f"检查{len(key_sections)}个关键章节, 均分={c4_score:.0f}"
              if key_sections else "无章节可检查")
    return c4_score, detail, c4_issues
def _c4_key_section_scores(sections_found,
                           doc_profile: str) -> list[tuple[str, float]]:
    if doc_profile != "template":
        rows = [(str(title).strip(), _c4_section_factors(content))
                for title, content in sections_found
                if str(title).strip() and not _is_placeholder_section(content)]
        return rows[:8]
    richness_keys = _standard_section_keys(
        REQUIRED_SECTIONS + RECOMMENDED_SECTIONS)
    rows: list[tuple[str, float]] = []
    for sec_title, sec_content in sections_found:
        title = sec_title.strip()
        section_keys = _section_keys(title)
        if (not (section_keys & richness_keys)
                or not (section_keys & _C4_KEY_SECTION_KEYS)):
            continue
        if not _is_placeholder_section(sec_content):
            rows.append((title, _c4_section_factors(sec_content)))
    return rows
def _module_mentioned(fname: str, mod_path: str, base_name: str,
                      prose_text: str, py_refs: set[str]) -> bool:
    if fname.lower() in py_refs:
        return True
    return bool(identifier_pattern(mod_path).search(prose_text)
                or identifier_pattern(base_name).search(prose_text))
def _entry_items(f_info, key: str) -> list:
    if not isinstance(f_info, dict):
        return []
    items = f_info.get(key)
    return items if isinstance(items, (list, tuple)) else []
def _c5_scan_entry(f_info, package_root: str = ""
                   ) -> tuple[str, str, str, str] | None:
    if not isinstance(f_info, dict):
        return None
    f_path = _scan_rel_path(f_info.get("file"))
    if not f_path:
        return None
    if not (_entry_items(f_info, "functions")
            or _entry_items(f_info, "classes")):
        return None
    fname = f_path.rsplit("/", 1)[-1]
    if fname.lower() == "__init__.py":
        # 包的公开 API 以包名被引用(import pkg / from pkg import x), 而不是 __init__
        package_dir = f_path[:-len(fname)].strip("/").removeprefix("./")
        package = package_dir.replace("/", ".") or (
            package_root.strip() if isinstance(package_root, str) else "")
        if package:
            return f_path, fname, package, package.rsplit(".", 1)[-1]
    mod_path = py_stem(f_path.replace("/", "."))
    return f_path, fname, mod_path, py_stem(fname)
def _c5_module_mention_stats(api_files, prose_text,
                             package_root: str = "") -> tuple:
    all_mentioned = extract_py_refs(prose_text)
    total = 0
    unmentioned: list[tuple[str, str]] = []
    for f_info in api_files:
        entry = _c5_scan_entry(f_info, package_root)
        if entry is None:
            continue
        f_path, fname, mod_path, base_name = entry
        total += 1
        if not _module_mentioned(
                fname, mod_path, base_name, prose_text, all_mentioned):
            unmentioned.append((f_path, base_name))
    return total, unmentioned
def _c5_unmentioned_issues(unmentioned: list) -> list[DocQualityIssue]:
    return [DocQualityIssue(
        category="capture", rule_id=f"SD-C5-{_rule_suffix(base_name, 15)}",
        severity="medium",
        description=f"关键模块 {f_path}（含公开API）未在文档中说明",
        suggestion=f"在'域总览'中补充 {base_name} 的能力说明",
        location="正文",
    ) for f_path, base_name in unmentioned[:50]]
def _compute_c5_module_coverage(body_text, api_scan,
                                *, doc_profile: str):
    if doc_profile == "router":
        return 80.0, "路由型文档：模块说明下沉到引用指南", []
    if has_code_surface(api_scan) is False:
        return NO_CODE_SCORE, NO_CODE_DETAIL, []
    api_files = get_scan_files(api_scan)
    if not api_files:
        _log.warning("[SkillDoc][C5] 无法扫描技能目录，模块覆盖度未验证")
        return _LOADING_NOSCAN_SCORE, "无法扫描", [make_noscan_issue(
            "capture", "SD-C5-NOSCAN", "模块覆盖度")]
    body_prose = strip_fenced_blocks(body_text)
    skill_dir = api_scan.get("skill_dir") if isinstance(api_scan, dict) else ""
    package_root = (os.path.basename(os.path.normpath(skill_dir))
                    if isinstance(skill_dir, str) and skill_dir else "")
    c5_total, unmentioned = _c5_module_mention_stats(
        api_files, body_prose, package_root)
    if not c5_total:
        return 70.0, "无含公开API的关键模块，按基线70计分", []
    c5_missing = len(unmentioned)
    c5_has_summary = _has_scan_summary(body_prose)
    c5_score = max(0.0, round(100.0 - (c5_missing / c5_total) * 80.0, 1))
    if doc_profile != "template":
        c5_score = max(40.0, c5_score)
    detail = (f"{c5_total - c5_missing}/{c5_total}关键模块已文档化"
              f"{'（有摘要行）' if c5_has_summary else ''}")
    return c5_score, detail, _c5_unmentioned_issues(unmentioned)
_C9_SIGNATURE_DOC_RE = re.compile(
    r'^(?:(?:async\s+)?def\s+)?[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*\s*\([^()]*\)'
    r'\s*(?:->\s*[^\n]+)?:?$')
def _c9_doc_is_signature_dump(doc: str) -> bool:
    text = doc.strip().strip('`').strip()
    return bool(text) and bool(_C9_SIGNATURE_DOC_RE.fullmatch(text))
def _c9_signature_key(text: str) -> str:
    text = re.sub(r"^(?:async\s+)?def\s+", "", text.strip().strip('`').strip())
    return re.sub(r"\s+", "", text).rstrip(":")
def _doc_is_signature_dump(doc: str, signature: str) -> bool:
    return _c9_doc_is_signature_dump(doc) or (
        bool(signature)
        and _c9_signature_key(doc) == _c9_signature_key(signature))
def _c9_func_entry_stats(func) -> tuple:
    if not isinstance(func, dict):
        return False, False, False
    doc = func.get("doc", "")
    if not isinstance(doc, str):
        doc = ""
    full_doc = func.get("full_doc")
    if isinstance(full_doc, str) and full_doc.strip():
        # doc 只是首行摘要；语义判定要看全文, 否则 Args 段落会被截断
        doc = full_doc
    sig = func.get("signature", "")
    if not isinstance(sig, str):
        sig = ""
    text = doc.strip()
    signature_dump = bool(text) and _doc_is_signature_dump(doc, sig)
    semantic = bool(text) and len(text) >= 10 and not signature_dump
    # 无 docstring 时扫描侧只有签名可读, 沿用既有口径计为原始签名
    raw_signature = bool(sig and (not text or signature_dump))
    return True, semantic, raw_signature
def _c9_desc_stats(api_files):
    total_descs = 0
    semantic_descs = 0
    raw_signatures = 0
    for _f_path, func in iter_scan_function_entries(api_files):
        _counted, _semantic, _raw = _c9_func_entry_stats(func)
        if _counted:
            total_descs += 1
            semantic_descs += int(_semantic)
            raw_signatures += int(_raw)
    return total_descs, semantic_descs, raw_signatures
def _compute_c9_semantic_depth(api_files):
    c9_issues = []
    c9_score = 100.0
    if api_files:
        total_descs, semantic_descs, raw_signatures = _c9_desc_stats(api_files)
        if total_descs > 0:
            ratio = semantic_descs / total_descs
            c9_score = round(ratio * 100, 1)
            sig_penalty = min(20, (raw_signatures // 10) * 5)
            c9_score = max(0.0, c9_score - sig_penalty)
            c9_detail = f"语义描述率{ratio * 100:.0f}%"
            if sig_penalty:
                c9_detail += f"（签名惩罚-{sig_penalty}）"
            if ratio < 0.5:
                c9_issues.append(DocQualityIssue(
                    category="capture", rule_id="SD-C9-SEMANTIC", severity="medium",
                    description=f"仅 {semantic_descs}/{total_descs} 个函数有语义描述",
                    suggestion="为函数添加有意义的 docstring，而非纯签名转储",
                    location="正文",
                ))
        else:
            c9_score = 70.0
            c9_detail = "无可测函数，按基线70计分"
    else:
        c9_score = 70.0
        c9_detail = "无法扫描，按基线70计分"
        _log.warning("[SkillDoc][C9] 无法扫描技能目录，模块语义文档化深度未验证")
        c9_issues.append(make_noscan_issue(
            "capture", "SD-C9-NOSCAN", "模块语义文档化深度"))
    return c9_score, c9_detail, c9_issues
def _c7_scan_file_names(api_files, skill_dir: str) -> set:
    names = set()
    for info in api_files:
        if not isinstance(info, dict):
            continue
        rel_path = _scan_rel_path(info.get("file"))
        if rel_path:
            names.add(rel_path.rsplit("/", 1)[-1].lower())
    if skill_dir and os.path.isdir(skill_dir):
        names |= collect_skill_py_basenames(skill_dir)
    return names
def _c7_no_domain_issue() -> DocQualityIssue:
    return DocQualityIssue(
        category="capture", rule_id="SD-C7-NODOMAIN", severity="high",
        description="缺少域总览章节或章节内容为空，无法验证章节间一致性",
        suggestion="添加'## 域总览'章节并补充域总览内容",
        location="正文",
    )
def _c7_stale_issues(stale) -> list:
    return [DocQualityIssue(
        category="capture", rule_id=f"SD-C7-STALE-{py_stem(fname)}",
        severity="medium",
        description=f"域总览提及的模块 {fname} 在代码扫描中不存在",
        suggestion=f"更新域总览中 {fname} 的陈旧引用",
        location="正文: 域总览",
    ) for fname in stale[:5]]
_C7_STALE_PENALTY_PER_ITEM = 15.0
_C7_STALE_PENALTY_MAX_ITEMS = 5
def _is_c7_test_ref(fname: str) -> bool:
    base = fname.rsplit("/", 1)[-1].lower()
    return base == "conftest.py" or is_test_source_basename(base)
def _c7_detail(c7_issues, stale_total: int = 0) -> str:
    if stale_total:
        return f"域总览陈旧引用{stale_total}个"
    return c7_issues[0].description if c7_issues else "章节间覆盖一致"
def _find_domain_overview_prose(sections_found) -> str:
    for sec_title, sec_content in sections_found:
        if "domain_overview" in _section_keys(sec_title):
            return strip_fenced_blocks(sec_content)
    return ""
def _compute_c7_cross_coverage(sections_found, api_files, skill_dir: str,
                               *, doc_profile: str):
    if doc_profile == "router":
        return 80.0, "路由型文档：不校验总览交叉覆盖", []
    overview_prose = _find_domain_overview_prose(sections_found)
    if not (overview_prose and overview_prose.strip()):
        if doc_profile != "template":
            return 70.0, "无总览章节：交叉覆盖不适用", []
        _log.warning("[SkillDoc][C7] 缺少域总览章节或章节内容为空，无法验证章节间一致性")
        issue = _c7_no_domain_issue()
        return 50.0, _c7_detail([issue]), [issue]
    scan_files = _c7_scan_file_names(api_files, skill_dir)
    if not scan_files:
        _log.warning("[SkillDoc][C7] 无法扫描技能目录，章节间交叉覆盖度未验证")
        issue = make_noscan_issue(
            "capture", "SD-C7-NOSCAN", "章节间交叉覆盖度")
        return 70.0, _c7_detail([issue]), [issue]
    overview_files = extract_py_refs(
        overview_prose, include_scripts=is_script_only_skill(skill_dir))
    # 测试文件不在 API 扫描集内, 但存在即非“陈旧模块引用”
    stale = sorted(f for f in overview_files
                   if f not in scan_files and not _is_c7_test_ref(f))
    if not stale:
        return 100.0, _c7_detail([]), []
    stale_total = len(stale)
    c7_score = max(0.0, 100.0
                   - min(stale_total, _C7_STALE_PENALTY_MAX_ITEMS)
                   * _C7_STALE_PENALTY_PER_ITEM)
    c7_issues = _c7_stale_issues(stale)
    return c7_score, _c7_detail(c7_issues, stale_total), c7_issues
def _compute_c6_param_coverage(api_scan, sections_found=None):
    c6_issues: list = []
    if sections_found is None:
        sections_found = []
    scan_files = get_scan_files(api_scan)
    if not scan_files:
        _log.warning("[SkillDoc][C6] 无法扫描技能目录，参数文档完整性未验证")
        c6_issues.append(make_noscan_issue(
            "capture", "SD-C6-NOSCAN", "参数文档完整性"))
        return 70.0, "无法扫描", c6_issues
    c6_total, c6_docced = _count_c6_docced_params(scan_files)
    if c6_total <= 0:
        c6_detail = ("压缩格式已文档化" if _is_c6_compressed_format(sections_found)
                     else "无可检查的带参函数")
        return 100.0, c6_detail, c6_issues
    c6_score = round(c6_docced / c6_total * 100, 1)
    c6_detail = f"{c6_docced}/{c6_total}参数已文档化"
    if c6_score < 50:
        c6_issues.append(DocQualityIssue(
            category="capture", rule_id="SD-C6-PARAMS", severity="low",
            description=f"仅 {c6_docced}/{c6_total} 个参数已文档化",
            suggestion="在函数 docstring 中补充参数说明",
            location="正文",
        ))
    return c6_score, c6_detail, c6_issues
def _is_c6_compressed_format(sections_found) -> bool:
    for sec_title, sec_content in sections_found:
        if _section_key(sec_title) != "module_details":
            continue
        c6_prose = strip_fenced_blocks(sec_content)
        if re.search(r'\w+\(\)', c6_prose):
            return True
    return False
def _c6_doc_without_signatures(doc: str, signature: str) -> str:
    if signature:
        doc = doc.replace(signature, " ")
    return "\n".join(
        " " if _c9_doc_is_signature_dump(line) else line
        for line in doc.splitlines())
def _c6_func_param_stats(func) -> tuple:
    if not isinstance(func, dict):
        return 0, 0
    sig = func.get("signature", "")
    if not isinstance(sig, str):
        sig = ""
    params = extract_param_names(sig)
    if not params:
        return 0, 0
    full_doc = func.get("full_doc")
    doc = (full_doc if isinstance(full_doc, str) and full_doc
           else func.get("doc", ""))
    if not isinstance(doc, str) or _doc_is_signature_dump(doc, sig):
        doc = ""
    else:
        doc = _c6_doc_without_signatures(doc, sig)
    docced = 0
    for p in params:
        if identifier_pattern(p).search(doc):
            docced += 1
    return len(params), docced
def _count_c6_docced_params(scan_files: list):
    c6_total = 0
    c6_docced = 0
    for _f_path, func in iter_scan_function_entries(scan_files):
        _total, _docced = _c6_func_param_stats(func)
        c6_total += _total
        c6_docced += _docced
    return c6_total, c6_docced
def _penalty_quick_start(sec_content: str, _sec_prose: str, reasons: list[str]) -> float:
    if not iter_fenced_blocks(sec_content):
        reasons.append("缺少代码示例")
        return 30.0
    return 0.0
def _penalty_scenarios(_sec_content: str, sec_prose: str, reasons: list[str]) -> float:
    table_rows = sum(len(rows) for rows in _iter_markdown_tables(sec_prose))
    if table_rows < 3:
        reasons.append(f"场景表仅{table_rows}行")
        return 20.0
    return 0.0
def _penalty_domain_overview(_sec_content: str, sec_prose: str, reasons: list[str]) -> float:
    if next(_iter_markdown_tables(sec_prose), None) is None:
        reasons.append("缺少域总览表格")
        return 25.0
    return 0.0
_TRIGGER_CLASSIFICATION_RE = re.compile(
    r"应当触发|不应触发|适用|不适用|"
    r"\bshould(?:\s+not)?\s+trigger\b|"
    r"\bshould\s+use\b|\bdo\s+not\s+use\b|\bdon['’]t\s+use\b|"
    r"\b(?:not\s+)?applicable\b|\bin\s+scope\b|\bout\s+of\s+scope\b",
    re.IGNORECASE)
def _penalty_trigger_conditions(_sec_content: str, sec_prose: str, reasons: list[str]) -> float:
    if not _TRIGGER_CLASSIFICATION_RE.search(sec_prose):
        reasons.append("缺少触发/不触发分类")
        return 20.0
    return 0.0
_SECTION_PENALTY_CHECKS: tuple[tuple[tuple[str, ...], Callable[[str, str, list[str]], float]], ...] = (
    (("quick_start",), _penalty_quick_start),
    (("use_cases",), _penalty_scenarios),
    (("domain_overview",), _penalty_domain_overview),
    (("trigger_conditions",), _penalty_trigger_conditions),
)
def _section_specific_penalty(sec_title_stripped: str, sec_content: str,
                              reasons: list[str]) -> float:
    section_key = _section_key(sec_title_stripped)
    for section_keys, check in _SECTION_PENALTY_CHECKS:
        if section_key in section_keys:
            return check(sec_content, strip_fenced_blocks(sec_content), reasons)
    return 0.0
def _depth_line_count_penalty(line_count: int) -> tuple[float, str | None]:
    if line_count < 3:
        return 50.0, f"仅{line_count}行非空行"
    if line_count < 6:
        return 25.0, f"仅{line_count}行非空行"
    if line_count < 10:
        return 10.0, f"{line_count}行非空行"
    return 0.0, None
def _depth_density_penalty(density: float) -> tuple[float, str | None]:
    if density < 0.3:
        return 20.0, f"内容密度低({density:.0%})"
    if density < 0.5:
        return 10.0, f"内容密度偏低({density:.0%})"
    return 0.0, None
def _score_section_depth(sec_title_stripped: str, sec_content: str):
    prose = sec_content.strip()
    sec_lines = prose.split('\n')
    non_empty_lines = [ln for ln in sec_lines if ln.strip()]
    line_count = len(non_empty_lines)
    depth_score = 100.0
    reasons: list[str] = []
    _line_penalty, _line_reason = _depth_line_count_penalty(line_count)
    depth_score -= _line_penalty
    if _line_reason:
        reasons.append(_line_reason)
    total_chars = len(prose)
    non_empty_chars = sum(len(ln.strip()) for ln in non_empty_lines)
    if total_chars > 0:
        density = non_empty_chars / total_chars
        _density_penalty, _density_reason = _depth_density_penalty(density)
        depth_score -= _density_penalty
        if _density_reason:
            reasons.append(_density_reason)
    depth_score -= _section_specific_penalty(sec_title_stripped, sec_content, reasons)
    return line_count, max(0.0, depth_score), reasons
def _c2_depth_penalty(shallow_sections) -> float:
    penalty = 0.0
    for _title, _lines, depth, _reasons in shallow_sections:
        if depth < 50:
            penalty += 25.0
        elif depth < 70:
            penalty += 18.0
        else:
            penalty += 10.0
    return penalty
def _c2_shallow_issues(shallow_sections) -> list:
    return [DocQualityIssue(
        category="capture", rule_id=f"SD-C2-{_rule_suffix(sec_title, 10)}",
        severity="medium",
        description=(f"章节 '{sec_title}' 内容深度不足"
                     f"（{d_score:.0f}/100）: {', '.join(reasons[:3])}"),
        suggestion="补充更多细节：表格、代码示例、使用说明、子章节等",
        location=f"正文: ## {sec_title}",
    ) for sec_title, _line_count, d_score, reasons in shallow_sections]
def _check_section_depth(required_sections, recommended_sections, sections_found,
                         *, doc_profile: str):
    if doc_profile == "router":
        return SubDimensionScore(
            dim_id="C2", dim_name="章节内容深度", category="capture",
            score=80.0, weight=0.20, issues=[],
            detail="路由型文档：章节深度下沉到引用指南",
        )
    shallow_sections = []
    standard_keys = _standard_section_keys(
        required_sections + recommended_sections)
    for sec_title, sec_content in sections_found:
        sec_title_stripped = sec_title.strip()
        if (doc_profile != "general"
                and _section_key(sec_title_stripped) not in standard_keys):
            continue
        if _is_placeholder_section(sec_content):
            continue
        line_count, depth_score, reasons = _score_section_depth(sec_title_stripped, sec_content)
        if depth_score < 80.0:
            shallow_sections.append((sec_title_stripped, line_count, depth_score, reasons))
    c2_score = max(0.0, 100.0 - _c2_depth_penalty(shallow_sections))
    c2_issues = _c2_shallow_issues(shallow_sections)
    return SubDimensionScore(
        dim_id="C2", dim_name="章节内容深度", category="capture",
        score=c2_score, weight=0.20,
        issues=c2_issues,
        detail=f"浅层章节{len(shallow_sections)}个" + (f": {', '.join(s[0] for s in shallow_sections[:3])}" if shallow_sections else ""),
    )
def _normalize_platform_issues(platform_loading_issues) -> list:
    if platform_loading_issues is None:
        return []
    if not isinstance(platform_loading_issues, list):
        _log.warning("[SkillDoc][L1] platform_loading_issues 形态异常(%s)，"
                     "按空快照处理", type(platform_loading_issues).__name__)
        return []
    valid = [i for i in platform_loading_issues
             if isinstance(i, DocQualityIssue)]
    if len(valid) != len(platform_loading_issues):
        _log.warning("[SkillDoc][L1] platform_loading_issues 跳过 %d 个非 "
                     "issue 条目", len(platform_loading_issues) - len(valid))
    if len(valid) == len(platform_loading_issues):
        return platform_loading_issues
    return valid
_RESOURCE_REF_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_+\-./])(?:" + _RESOURCE_DIR_ALT + r")/[\w\-./]+",
    re.IGNORECASE,
)
def diag_loading_l1l2(body_text, skill_dir, all_issues, platform_loading_issues,
                      sections_found=None) -> list[SubDimensionScore]:
    _t0 = time.monotonic()
    body_text, all_issues = normalize_entry_inputs(body_text, all_issues, text=True)
    platform_loading_issues = _normalize_platform_issues(platform_loading_issues)
    sections_found = _resolve_sections_found(body_text, sections_found)
    skill_dir_usable = (isinstance(skill_dir, (str, os.PathLike)) and bool(skill_dir)
                        and os.path.isdir(skill_dir))
    if not skill_dir_usable:
        _log.warning("[SkillDoc][L1/L2] skill_dir 缺失或不可用，"
                     "跳过资源/文件结构存在性检查: %r", skill_dir)
    l1_result, l1_new_issues = _diag_loading_l1(
        body_text, skill_dir, skill_dir_usable, platform_loading_issues)
    all_issues.extend(l1_new_issues)
    l2_result = _diag_loading_l2(body_text, skill_dir, skill_dir_usable, sections_found)
    all_issues.extend(l2_result.issues)
    results: list[SubDimensionScore] = [l1_result, l2_result]
    write_module_run(
        "skill_doc_structure", "diag_loading_l1l2",
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        l1_score=l1_result.score, l2_score=l2_result.score,
        l1_issues=len(l1_result.issues), l2_issues=len(l2_result.issues))
    return results
def _esc_ref_issue(rule_id: str, ref: str) -> DocQualityIssue:
    return DocQualityIssue(
        category="loading", rule_id=rule_id, severity="medium",
        description=f"文档引用的文件路径越出技能目录: {ref}",
        suggestion="技能文档须自包含，修正为技能目录内相对路径",
        location=f"正文: {ref}",
        matched_text=ref,
    )
def _ref_trim_trailing_slash(raw_ref: str) -> str:
    ref = raw_ref
    while ref.endswith("/"):
        ref = ref[:-1]
    ref = ref.removesuffix("/.")
    return re.sub(r'(?<=[\w-])\.+$', '', ref)
def _check_l1_resource_existence(all_refs, skill_dir) -> list:
    detected: list[DocQualityIssue] = []
    for raw_ref in sorted(all_refs):
        ref = _ref_trim_trailing_slash(raw_ref)
        if _ref_escapes_skill_dir(ref):
            detected.append(_esc_ref_issue("SD-L1-ESC", ref))
            continue
        _ref_path = os.path.join(skill_dir, ref)
        if not (os.path.isfile(_ref_path) or os.path.isdir(_ref_path)):
            detected.append(DocQualityIssue(
                category="loading", rule_id=f"SD-L1-{_rule_suffix(ref, 30)}",
                severity="medium",
                description=f"正文引用的资源 {ref} 在技能目录中不存在",
                suggestion="创建该文件或从正文中移除引用",
                location=f"正文: {ref}",
            ))
    return detected
def _check_l1_nested_refs(all_refs) -> list:
    detected: list[DocQualityIssue] = []
    nested_refs = [r for r in all_refs if r.rstrip("./").count("/") > 1]
    for ref in sorted(nested_refs):
        detected.append(DocQualityIssue(
            category="loading", rule_id="LR-001", severity="medium",
            description=f"存在嵌套资源引用: {ref}",
            suggestion="所有引用应从 SKILL.md 直接链接，避免 A→B→C 的嵌套引用",
            location=f"正文: {ref}",
            matched_text=ref,
        ))
    return detected
_LONG_REF_MAX_LINES = 100
_LONG_REF_TOC_PATTERN = re.compile(
    r"(?:#\s*目录|#\s*目錄|#\s*Table of Contents|#\s*TOC|-\s+\[)",
    re.IGNORECASE)
def _l1_ref_needs_toc(fpath: str) -> bool:
    try:
        ref_content = read_diagnostic_source_strict(fpath)
    except (OSError, UnicodeDecodeError, LookupError) as e:
        _log.debug("参考文档读取/解码失败（跳过 LR-002）: %s: %s", fpath, e)
        return False
    if len(ref_content.splitlines()) <= _LONG_REF_MAX_LINES:
        return False
    return not bool(_LONG_REF_TOC_PATTERN.search(ref_content))
def _check_l1_long_ref_toc(skill_dir) -> list:
    detected: list[DocQualityIssue] = []
    ref_dir = os.path.join(skill_dir, "references")
    if not os.path.isdir(ref_dir):
        return detected
    try:
        entries = sorted(os.listdir(ref_dir))
    except OSError as e:
        _log.warning("references 目录不可读，跳过 LR-002 检查: %s: %s",
                     ref_dir, e)
        return detected
    for fname in entries:
        fpath = os.path.join(ref_dir, fname)
        if not (os.path.isfile(fpath)
                and fname.lower().endswith((".md", ".rst"))):
            continue
        if not _l1_ref_needs_toc(fpath):
            continue
        detected.append(DocQualityIssue(
            category="loading", rule_id="LR-002", severity="low",
            description=(f"references/{fname} 超过 "
                         f"{_LONG_REF_MAX_LINES} 行但无目录"),
            suggestion="在文件顶部添加目录，方便 AI 预览时快速理解内容范围",
            location=f"references/{fname}",
        ))
    return detected
_L1_SEVERITY_PENALTY: dict[str, float] = {
    "critical": 40.0, "high": 25.0, "medium": 12.0, "low": 5.0,
}
def _l1_penalty(issues) -> float:
    return sum(_L1_SEVERITY_PENALTY.get(i.severity, 0.0) for i in issues)
def _diag_loading_l1(body_text, skill_dir, skill_dir_usable, platform_loading_issues):
    all_refs = set(_RESOURCE_REF_PATTERN.findall(body_text))
    noscan_issues = ([] if skill_dir_usable else [make_noscan_issue(
        "loading", "SD-L1-NOSCAN", "资源引用有效性")])
    sd_l1_detected = (_check_l1_resource_existence(all_refs, skill_dir)
                      if skill_dir_usable else [])
    lr001_detected = _check_l1_nested_refs(all_refs)
    lr002_detected = (_check_l1_long_ref_toc(skill_dir) if skill_dir_usable else [])
    l1_new_issues = [
        *noscan_issues, *sd_l1_detected, *lr001_detected, *lr002_detected]
    l1_issues = [*platform_loading_issues, *l1_new_issues]
    base_score = 100.0 if skill_dir_usable else _LOADING_NOSCAN_SCORE
    scored_issues = [issue for issue in l1_issues
                     if issue.rule_id != "SD-L1-NOSCAN"]
    l1_score = max(0.0, base_score - _l1_penalty(scored_issues))
    if skill_dir_usable:
        l1_detail = f'{len(l1_issues)}项引用问题' if l1_issues else '无引用问题'
    else:
        other_issue_count = len(l1_issues) - len(noscan_issues)
        l1_detail = "无法扫描（skill_dir 不可用）"
        if other_issue_count:
            l1_detail += f"；另发现{other_issue_count}项引用问题"
    l1_dim = SubDimensionScore(
        dim_id='L1',
        dim_name='资源引用有效性',
        category='loading',
        weight=0.3,
        score=l1_score,
        issues=l1_issues,
        detail=l1_detail,
    )
    return l1_dim, l1_new_issues
def _l2_missing_file_issue(fname: str) -> DocQualityIssue:
    return DocQualityIssue(
        category="loading", rule_id=f"SD-L2-{fname}", severity="medium",
        description=f"文档中提到的文件 {fname} 在技能目录中不存在",
        suggestion="创建该文件或从文档中移除引用",
        location=f"正文: {fname}",
    )
def _l2_missing_dir_issue(dname: str) -> DocQualityIssue:
    return DocQualityIssue(
        category="loading", rule_id=f"SD-L2-DIR-{dname}", severity="low",
        description=f"文件结构树中提到的目录 {dname}/ 不存在",
        suggestion="创建目录或更新文件结构树",
        location=f"文件结构: {dname}/",
    )
def _l2_check_mentioned_files(mentioned_files, skill_dir):
    issues = []
    penalty = 0.0
    basenames = None
    for fname in sorted(set(mentioned_files)):
        if _ref_escapes_skill_dir(fname):
            issues.append(_esc_ref_issue("SD-L2-ESC", fname))
            penalty += 10
            continue
        if os.path.isfile(os.path.join(skill_dir, fname)):
            continue
        if "/" not in fname:
            if basenames is None:
                basenames = collect_skill_py_basenames(skill_dir)
            if fname.lower() in basenames:
                continue
        issues.append(_l2_missing_file_issue(fname))
        penalty += 10
    return issues, penalty
def _find_fs_section(sections_found) -> str | None:
    for sec_title, sec_content in _normalize_sections_found(sections_found):
        if _section_key(sec_title) == "file_structure":
            return sec_content
    return None
_L2_TREE_ROOT_RE = re.compile(r'([^\s/]+)/?\s*(?:#.*)?$')
def _l2_tree_root(tree_block: str):
    for line in tree_block.splitlines():
        text = line.strip()
        if not text:
            continue
        head = text.split('#', 1)[0].strip()
        if len(head) >= 2 and head.startswith('`') and head.endswith('`'):
            head = head[1:-1].strip()
        if not head or head[0] in '├└│`|+':
            return None
        if head == '/':
            return ''
        if _ref_escapes_skill_dir(head.rstrip('/')):
            return ''
        match = _L2_TREE_ROOT_RE.fullmatch(head)
        return match.group(1) if match else None
    return None
def _l2_tree_describes_skill(tree_block: str, skill_dir: str) -> bool:
    root = _l2_tree_root(tree_block)
    if root is None:
        return True
    if not root:
        return False
    if root in (".", "./"):
        return True
    normalized = root.rstrip("/").strip("./")
    if not normalized:
        return False
    skill_name = os.path.basename(os.path.normpath(skill_dir))
    return normalized.lower() == skill_name.lower()
def _l2_tree_blocks(body_text, sections_found, skill_dir) -> list[str]:
    fs_content = _find_fs_section(sections_found)
    source = fs_content if fs_content is not None else body_text
    return [block for block in iter_fenced_blocks(source)
            if _l2_tree_describes_skill(block, skill_dir)]
_L2_TREE_BRANCH_RE = re.compile(r'[├└|+](?:─|-){1,2}\s*`?([^\s/`]+)/`?')
def _l2_mentioned_dirs(tree_blocks) -> set:
    mentioned_dirs = set()
    for tree_block in tree_blocks:
        stack: list[tuple[int, str]] = []
        for line in tree_block.splitlines():
            m = _L2_TREE_BRANCH_RE.search(line)
            if not m:
                continue
            col = m.start()
            while stack and stack[-1][0] >= col:
                stack.pop()
            stack.append((col, m.group(1)))
            mentioned_dirs.add("/".join(name for _c, name in stack))
    return mentioned_dirs
def _l2_check_mentioned_dirs(mentioned_dirs, skill_dir):
    issues = []
    penalty = 0.0
    for dname in sorted(mentioned_dirs):
        if _ref_escapes_skill_dir(dname):
            issues.append(_esc_ref_issue("SD-L2-ESC", dname))
            penalty += 10
            continue
        dpath = os.path.join(skill_dir, *dname.split("/"))
        if not os.path.isdir(dpath):
            issues.append(_l2_missing_dir_issue(dname))
            penalty += 5
    return issues, penalty
def _diag_loading_l2(body_text, skill_dir, skill_dir_usable, sections_found) -> SubDimensionScore:
    l2_issues = []
    l2_score = 100.0
    mentioned_files = re.findall(r'`([\w\-./]+\.py)`', body_text, re.IGNORECASE)
    if skill_dir_usable:
        mentioned_dirs = _l2_mentioned_dirs(
            _l2_tree_blocks(body_text, sections_found, skill_dir))
        file_issues, file_penalty = _l2_check_mentioned_files(
            mentioned_files, skill_dir)
        dir_issues, dir_penalty = _l2_check_mentioned_dirs(
            mentioned_dirs, skill_dir)
        l2_issues.extend(file_issues)
        l2_issues.extend(dir_issues)
        l2_score -= file_penalty + dir_penalty
        l2_score = max(0.0, l2_score)
        l2_detail = (f'{len(l2_issues)}项不一致' if l2_issues
                     else '文档与目录一致')
    else:
        _log.warning("[SkillDoc][L2] skill_dir 不可用，文件结构准确性未度量")
        l2_score = _LOADING_NOSCAN_SCORE
        l2_issues.append(make_noscan_issue(
            "loading", "SD-L2-NOSCAN", "文件结构准确性"))
        l2_detail = '无法扫描（skill_dir 不可用）'
    return SubDimensionScore(
        dim_id='L2',
        dim_name='文件结构准确性',
        category='loading',
        weight=0.2,
        score=l2_score,
        issues=l2_issues,
        detail=l2_detail
    )
def _iter_scan_function_names(api_scan) -> Iterator[tuple[str, str]]:
    for f_path, func in iter_scan_function_entries(get_scan_files(api_scan)):
        func_name = func.get("name")
        if isinstance(func_name, str) and func_name:
            yield f_path, func_name
def _reexport_aliases(f_info, api_scan) -> dict[str, str]:
    skill_dir = api_scan.get("skill_dir") if isinstance(api_scan, dict) else ""
    f_path = _scan_rel_path(f_info.get("file"))
    if not isinstance(skill_dir, str) or not skill_dir or not f_path:
        return {}
    source_path = os.path.join(skill_dir, *f_path.split("/"))
    try:
        source = read_diagnostic_source_strict(source_path)
        tree = ast.parse(source)
    except (OSError, UnicodeDecodeError, LookupError, SyntaxError) as exc:
        _log.warning("[SkillDoc][L3] 入口别名解析失败，保留原名匹配: %s: %s",
                     f_path, exc)
        return {}
    return {
        alias.asname: alias.name
        for node in iter_module_scope_nodes(tree, descend_classes=False)
        if isinstance(node, ast.ImportFrom)
        for alias in node.names
        if alias.asname and alias.name != "*"
    }
def _iter_entry_functions(api_scan) -> Iterator[str]:
    seen: set[str] = set()
    files = get_scan_files(api_scan)
    all_function_names = {
        func_name for _f_path, func_name in _iter_scan_function_names(api_scan)}
    for f_info in files:
        if not isinstance(f_info, dict):
            continue
        f_path = _scan_rel_path(f_info.get("file"))
        if f_path.rsplit("/", 1)[-1].lower() != "__init__.py":
            continue
        direct_names = [
            func.get("name") for func in _entry_items(f_info, "functions")
            if isinstance(func, dict)]
        exported_names = [
            name for name in _entry_items(f_info, "public_api_names")
            if isinstance(name, str)]
        aliases: dict[str, str] | None = None
        for func_name in [*direct_names, *exported_names]:
            if (not isinstance(func_name, str) or func_name.startswith("_")
                    or func_name in seen):
                continue
            if func_name not in all_function_names:
                if aliases is None:
                    aliases = _reexport_aliases(f_info, api_scan)
                if aliases.get(func_name) not in all_function_names:
                    continue
            seen.add(func_name)
            yield func_name
def _diag_loading_l3(body_text, api_scan) -> SubDimensionScore:
    if has_code_surface(api_scan) is False:
        return SubDimensionScore(
            dim_id='L3',
            dim_name='API函数覆盖率',
            category='loading',
            weight=0.3,
            score=NO_CODE_SCORE,
            issues=[],
            detail=NO_CODE_DETAIL
        )
    l3_issues: list[DocQualityIssue] = []
    l3_total = 0
    l3_undoc = 0
    has_scan = has_scan_files(api_scan)
    if has_scan:
        for func_name in _iter_entry_functions(api_scan):
            l3_total += 1
            if not identifier_pattern(func_name).search(body_text):
                l3_undoc += 1
                if len(l3_issues) < 50:
                    l3_issues.append(DocQualityIssue(
                        category="loading",
                        rule_id=f"SD-L3-{_rule_suffix(func_name, 15)}",
                        severity="low",
                        description=f"入口函数 {func_name}() 未在文档中提及",
                        suggestion=f"在'快速入门'或'典型应用场景'中补充 {func_name}() 的说明",
                        location="正文",
                    ))
        if l3_total > 0:
            coverage = (l3_total - l3_undoc) / l3_total
            l3_score = round(coverage * 100, 1)
            l3_detail = f'{l3_total - l3_undoc}/{l3_total}入口函数已文档化'
        else:
            l3_score = 90.0
            l3_detail = '无可测入口函数，按基线90计分'
    else:
        l3_score = _LOADING_NOSCAN_SCORE
        l3_detail = '无法扫描'
        l3_issues.append(make_noscan_issue(
            "loading", "SD-L3-NOSCAN", "API函数覆盖率"))
    return SubDimensionScore(
        dim_id='L3',
        dim_name='API函数覆盖率',
        category='loading',
        weight=0.3,
        score=l3_score,
        issues=l3_issues,
        detail=l3_detail
    )
_L4_TREE_ENTRY_RE = re.compile(
    r'[├└|+](?:─|-){1,2}\s*`?([^\s/`]+?)(/?)`?\s*(?:#.*)?$')
def _extract_l4_tree_paths(fs_content: str, skill_dir="") -> set[str]:
    tree_files: set[str] = set()
    for tree_block in iter_fenced_blocks(fs_content):
        if skill_dir and not _l2_tree_describes_skill(tree_block, skill_dir):
            continue
        root = _l2_tree_root(tree_block)
        if root == '':
            continue
        stack: list[tuple[int, str]] = []
        def register(raw_path: str, *, tree_root: str | None = root) -> None:
            path = raw_path.replace('\\', '/').lower()
            while path.startswith('./'):
                path = path[2:]
            if tree_root and path.startswith(tree_root.lower() + '/'):
                path = path[len(tree_root) + 1:]
            if path.endswith('.py'):
                tree_files.add(path)
        for line in tree_block.splitlines():
            match = _L4_TREE_ENTRY_RE.search(line)
            if match is None:
                for raw_path in re.findall(
                        r'[\w\-./]+\.py', line, re.IGNORECASE):
                    register(raw_path)
                continue
            col = match.start()
            while stack and stack[-1][0] >= col:
                stack.pop()
            name, directory_marker = match.groups()
            if directory_marker:
                stack.append((col, name))
            else:
                register('/'.join([*(item for _c, item in stack), name]))
    return tree_files
def _l4_scan_stats(scan_files: list) -> set[str]:
    actual_py_files = set()
    for f in scan_files:
        if not isinstance(f, dict):
            continue
        rel_path = _scan_rel_path(f.get("file"))
        if rel_path:
            actual_py_files.add(rel_path.lower())
    return actual_py_files
_L4_SUMMARY_SCORE = 80.0
_L4_TREE_SCORE = 60.0
_L4_NO_TREE_SCORE = 30.0
def _l4_base_score(l4_has_summary: bool, tree_files: set):
    if l4_has_summary:
        return _L4_SUMMARY_SCORE, None
    if tree_files:
        return _L4_TREE_SCORE, None
    return _L4_NO_TREE_SCORE, DocQualityIssue(
        category="loading", rule_id="SD-L4-NOTREE",
        severity="medium",
        description="文件结构章节缺少文件树或统计摘要",
        suggestion="添加统计摘要行或精简的文件树",
        location="正文: 文件结构",
    )
def _l4_summary_mismatch_issue(counts: set[int], total_count: int) -> DocQualityIssue:
    description = (f"统计摘要模块数{sorted(counts)}与代码扫描{total_count}个不一致"
                   if counts else "统计摘要未提供可核验的模块数")
    return DocQualityIssue(
        category="loading", rule_id="SD-L4-SUMMARY", severity="medium",
        description=description,
        suggestion=f"将统计摘要更新为实际扫描结果: {total_count}个模块",
        location="正文: 文件结构",
    )
def _l4_scan_verdict(body_text, fs_content, api_scan):
    actual_py_files = _l4_scan_stats(get_scan_files(api_scan))
    total_count = len(actual_py_files)
    body_prose = strip_fenced_blocks(body_text)
    has_summary = _has_scan_summary(body_prose)
    summary_counts = _scan_summary_counts(body_prose)
    summary_valid = total_count in summary_counts
    skill_dir = api_scan.get("skill_dir", "") if isinstance(api_scan, dict) else ""
    tree_files = _extract_l4_tree_paths(fs_content, skill_dir)
    score, base_issue = _l4_base_score(summary_valid, tree_files)
    issues: list[DocQualityIssue] = [base_issue] if base_issue is not None else []
    if has_summary and not summary_valid:
        issues.append(_l4_summary_mismatch_issue(summary_counts, total_count))
    exhaust_penalty, exhaust_issue = _l4_exhaust_penalty(
        tree_files, total_count)
    if exhaust_penalty:
        score = max(0.0, score - exhaust_penalty)
        issues.append(exhaust_issue)
    tree_coverage, missing_issue = _l4_tree_completeness(
        tree_files, actual_py_files, summary_valid,
        _l4_on_disk_tree_files(tree_files, actual_py_files, skill_dir))
    if missing_issue is not None:
        score = min(score, round(_L4_TREE_SCORE * tree_coverage, 1))
        issues.append(missing_issue)
    return score, issues, total_count, has_summary
def _diag_loading_l4(body_text, sections_found, api_scan,
                     *, doc_profile: str) -> SubDimensionScore:
    scan_ok = has_scan_files(api_scan)
    fs_content = _find_fs_section(sections_found) or ""
    if doc_profile == "router":
        return SubDimensionScore(
            dim_id='L4',
            dim_name='文件树完整性',
            category='loading',
            weight=0.2,
            score=80.0,
            issues=[],
            detail='路由型文档：文件结构不适用'
        )
    if not scan_ok and has_code_surface(api_scan) is False:
        return SubDimensionScore(
            dim_id='L4',
            dim_name='文件树完整性',
            category='loading',
            weight=0.2,
            score=NO_CODE_SCORE,
            issues=[],
            detail=NO_CODE_DETAIL
        )
    if doc_profile != "template" and scan_ok and not fs_content:
        return SubDimensionScore(
            dim_id='L4',
            dim_name='文件树完整性',
            category='loading',
            weight=0.2,
            score=70.0,
            issues=[],
            detail='未提供文件结构章节：不适用'
        )
    if scan_ok:
        l4_score, l4_issues, l4_total_count, l4_has_summary = _l4_scan_verdict(
            body_text, fs_content, api_scan)
    else:
        l4_score, l4_total_count, l4_has_summary = _LOADING_NOSCAN_SCORE, 0, False
        l4_issues = [make_noscan_issue(
            "loading", "SD-L4-NOSCAN", "文件树完整性")]
    return SubDimensionScore(
        dim_id='L4',
        dim_name='文件树完整性',
        category='loading',
        weight=0.2,
        score=l4_score,
        issues=l4_issues,
        detail=f"共{l4_total_count}个文件, 摘要={('有' if l4_has_summary else '无')}" if scan_ok else '无法扫描'
    )
def diag_loading_l3l4(body_text, all_issues, api_scan, sections_found=None,
                      *, doc_profile: str = _DEFAULT_DOC_PROFILE,
                      expanded_body=None) -> list[SubDimensionScore]:
    _t0 = time.monotonic()
    body_text, all_issues = normalize_entry_inputs(body_text, all_issues, text=True)
    sections_found = _resolve_sections_found(body_text, sections_found)
    if doc_profile == "router":
        l3 = SubDimensionScore(
            dim_id='L3',
            dim_name='API函数覆盖率',
            category='loading',
            weight=0.3,
            score=80.0,
            issues=[],
            detail='路由型文档：API 说明下沉到引用指南'
        )
    else:
        l3 = _diag_loading_l3(
            expanded_body if isinstance(expanded_body, str) else body_text,
            api_scan)
    l4 = _diag_loading_l4(body_text, sections_found, api_scan,
                          doc_profile=doc_profile)
    all_issues.extend(l3.issues)
    all_issues.extend(l4.issues)
    write_module_run(
        "skill_doc_structure", "diag_loading_l3l4",
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        l3_score=l3.score, l4_score=l4.score,
        issues=len(l3.issues) + len(l4.issues))
    return [l3, l4]
def _l4_exhaust_penalty(tree_files: set, l4_total_count: int):
    if tree_files and len(tree_files) > l4_total_count * 0.8 and l4_total_count > 30:
        return 20.0, DocQualityIssue(
            category="loading", rule_id="SD-L4-EXHAUST",
            severity="low",
            description=f"文件树列出了 {len(tree_files)}/{l4_total_count} 个文件（穷举式），建议压缩为摘要",
            suggestion="将完整文件树替换为统计摘要+关键模块列表",
            location="正文: 文件结构",
        )
    return 0.0, None
def _l4_on_disk_tree_files(tree_files: set, actual_py_files: set,
                           skill_dir) -> set[str]:
    """扫描集之外但磁盘上真实存在的树内 .py 文件, 如 tests 与脚本目录"""
    normalized_actual = {
        path.replace('\\', '/').lower() for path in actual_py_files}
    if not isinstance(skill_dir, str) or not skill_dir:
        return set()
    on_disk: set[str] = set()
    for path in tree_files - normalized_actual:
        if _ref_escapes_skill_dir(path):
            continue
        if os.path.isfile(os.path.join(skill_dir, *path.split("/"))):
            on_disk.add(path)
    return on_disk
def _l4_tree_completeness(tree_files: set, actual_py_files: set,
                          l4_has_summary: bool,
                          on_disk_files: set | None = None
                          ) -> tuple[float, DocQualityIssue | None]:
    if not tree_files or not actual_py_files or l4_has_summary:
        return 1.0, None
    normalized_actual = {
        path.replace('\\', '/').lower() for path in actual_py_files}
    # 存在性口径 = 扫描集 并上 磁盘上真实存在的树内文件; 缺失率仍以扫描集为分母
    existing_files = normalized_actual | set(on_disk_files or ())
    missing_in_tree = sorted(normalized_actual - tree_files)
    stale_in_tree = sorted(tree_files - existing_files)
    missing_ratio = len(missing_in_tree) / len(normalized_actual)
    if missing_ratio <= 0.2 and not stale_in_tree:
        return 1.0, None
    descriptions: list[str] = []
    suggestions: list[str] = []
    if missing_ratio > 0.2:
        descriptions.append(
            f"缺失 {len(missing_in_tree)}/{len(normalized_actual)} 个 .py 文件")
        suggestions.append(f"补充缺失的文件: {', '.join(missing_in_tree[:5])}")
    if stale_in_tree:
        descriptions.append(f"包含 {len(stale_in_tree)} 个不存在的 .py 文件")
        suggestions.append(f"移除或更新: {', '.join(stale_in_tree[:5])}")
    issue = DocQualityIssue(
        category="loading", rule_id="SD-L4-TREE",
        severity="medium",
        description=f"文件结构树{'；'.join(descriptions)}",
        suggestion="；".join(suggestions),
        location="正文: 文件结构",
    )
    matched_count = len(existing_files & tree_files)
    recall = 1.0 if missing_ratio <= 0.2 else 1.0 - missing_ratio
    precision = matched_count / len(tree_files)
    return min(recall, precision), issue
def _strip_leading_signature(after: str) -> str:
    if not after.startswith('('):
        return after
    depth = 0
    for i, ch in enumerate(after):
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                return after[i + 1:]
    return ''
_L5_DESC_SEP = r'(?:[—:：]|-(?![A-Za-z0-9_-]))'
_L5_DESC_RE = re.compile(_L5_DESC_SEP + r'\s*(.{5,})')
_L5_BACKTICK_DESC_RE = re.compile(
    r'`[^`]*`\s*' + _L5_DESC_SEP + r'\s*(.{5,})')
_L5_TAIL_MIN_CHARS = 5
_L5_TAIL_WORD_RE = re.compile(r"[\u4e00-\u9fff]|[A-Za-z]{3,}")
_L5_TAIL_CONNECTOR_RE = re.compile(r"^(?:and|or|vs\.?|with)\b", re.IGNORECASE)
_L5_TAIL_STOP_CHARS = frozenset(
    "()（）[]【】<>《》=|/\\、,，;；:：。.?!！？…—~*`'\"“”‘’的和等在与及或")
def _l5_desc_tail(after: str) -> str:
    return _strip_leading_signature(after.lstrip()).lstrip("`").lstrip()
def _l5_tail_description(tail: str) -> bool:
    text = tail.split("\n", 1)[0].strip()
    if not text or text[0] in _L5_TAIL_STOP_CHARS:
        return False
    if len(text) < _L5_TAIL_MIN_CHARS or _L5_TAIL_CONNECTOR_RE.match(text):
        return False
    return bool(_L5_TAIL_WORD_RE.search(text))
_CELL_DECOR_RE = re.compile(r'[`*\[\]]')
_CELL_DECOR_AND_PAREN_RE = re.compile(r'[`*\[\]()]')
_L5_NON_PROSE_CELL_RE = re.compile(r"(?:\.{1,2}/)*[A-Za-z_][\w./\\-]*")
def _l5_cell_has_description(cell: str, api_names: set) -> bool:
    if _l5_cell_is_api_name(_CELL_DECOR_RE.sub('', cell).strip(), api_names):
        return False
    plain = _CELL_DECOR_AND_PAREN_RE.sub('', cell).strip()
    if (not plain or len(plain) < _L5_TAIL_MIN_CHARS
            or re.fullmatch(r':?-{3,}:?', plain)
            or _L5_NON_PROSE_CELL_RE.fullmatch(plain)):
        return False
    return bool(_L5_TAIL_WORD_RE.search(plain))
def _l5_next_api_offset(after: str, func_name: str, api_names) -> int:
    offsets = []
    for other_name in api_names:
        if other_name == func_name:
            continue
        other = identifier_pattern(other_name).search(after)
        if other is not None:
            offsets.append(other.start())
    return min(offsets) if offsets else -1
def _l5_cell_is_api_name(cell: str, api_names: set) -> bool:
    key = cell
    if cell.endswith(')') and '(' in cell:
        key = cell.split('(', 1)[0].strip()
    return key.rsplit(".", 1)[-1] in api_names
def _l5_table_description_present(body_text: str, occ, func_name: str,
                                  api_names: set) -> bool | None:
    line_start = body_text.rfind('\n', 0, occ.start()) + 1
    line_end = body_text.find('\n', occ.end())
    if line_end < 0:
        line_end = len(body_text)
    line = body_text[line_start:line_end]
    cells = _l5_markdown_cells(line)
    if len(cells) < 2:
        return None
    offset = occ.start() - line_start
    current = next((index for index, (start, end, _) in enumerate(cells)
                    if start <= offset < end), -1)
    if current < 0:
        return False
    if any(_l5_cell_has_description(raw_cell, api_names)
           for index, (_start, _end, raw_cell) in enumerate(cells)
           if index != current):
        return True
    cell_start, _cell_end, cell = cells[current]
    # 与内联路径共用同一套描述判定, 避免“`foo()`：说明”只在表格中被漏判
    return _l5_inline_desc_present(
        _l5_desc_tail(cell[occ.end() - line_start - cell_start:]),
        func_name, api_names)
def _desc_precedes_next_api(match, next_api: int) -> bool:
    return (match is not None
            and (next_api < 0 or match.start(1) < next_api))
def _l5_inline_desc_present(after: str, func_name: str,
                            api_names: set) -> bool:
    next_api = _l5_next_api_offset(after, func_name, api_names)
    desc_match = _L5_DESC_RE.search(after)
    if (_desc_precedes_next_api(desc_match, next_api)
            and not desc_match.group(1).startswith('(')):
        return True
    if _desc_precedes_next_api(_L5_BACKTICK_DESC_RE.search(after), next_api):
        return True
    tail_region = after if next_api < 0 else after[:next_api]
    return _l5_tail_description(tail_region)
def _l5_func_description_present(body_text: str, occurrences: list,
                                 func_name: str, api_names: set) -> bool:
    for occ in occurrences:
        table_description = _l5_table_description_present(
            body_text, occ, func_name, api_names)
        if table_description is True:
            return True
        if table_description is False:
            continue
        after = _l5_desc_tail(
            strip_url_tokens(body_text[occ.end():occ.end() + 80]))
        if _l5_inline_desc_present(after, func_name, api_names):
            return True
    return False
def _l5_func_audit(body_text: str, func_name: str, api_names: set):
    occurrences = list(identifier_pattern(func_name).finditer(body_text))
    if not occurrences:
        return False, False
    return True, _l5_func_description_present(
        body_text, occurrences, func_name, api_names)
def _l5_no_desc_issue(func_name: str) -> DocQualityIssue:
    return DocQualityIssue(
        category="loading", rule_id=f"SD-L5-{_rule_suffix(func_name, 15)}",
        severity="low",
        description=f"函数 {func_name}() 在文档中被提及但缺少功能描述",
        suggestion=f"为 {func_name}() 添加简短的功能说明",
        location="正文",
    )
def _l5_nomention_issue() -> DocQualityIssue:
    return DocQualityIssue(
        category="loading", rule_id="SD-L5-NOMENTION", severity="medium",
        description="扫描到公开函数但文档未提及任何函数，函数描述质量无从评估",
        suggestion="在'快速入门'或'域总览'中提及并描述核心函数",
        location="正文",
    )
def _l5_audit_functions(body_text: str, api_scan):
    func_names = list(dict.fromkeys(
        func_name for _f_path, func_name
        in _iter_scan_function_names(api_scan)))
    api_names = set(func_names)
    issues: list[DocQualityIssue] = []
    with_desc = mentioned = 0
    for func_name in func_names:
        is_mentioned, has_desc = _l5_func_audit(
            body_text, func_name, api_names)
        if not is_mentioned:
            continue
        mentioned += 1
        if has_desc:
            with_desc += 1
        elif len(issues) < 50:
            issues.append(_l5_no_desc_issue(func_name))
    return issues, with_desc, mentioned, len(func_names)
def _l5_assess(l5_total: int, l5_mentioned: int, l5_with_desc: int,
               *, doc_profile: str):
    if l5_total == 0:
        neutral = 70.0 if doc_profile != "template" else 50.0
        return neutral, f"无可测函数，按基线{neutral:.0f}计分", None
    if l5_mentioned > 0:
        return (round(l5_with_desc / l5_mentioned * 100, 1),
                f"{l5_with_desc}/{l5_mentioned}函数有描述", None)
    if doc_profile != "template":
        return 50.0, "文档未直接提及Python函数（参考型文档不强制）", None
    return (0.0, f"文档未提及任何函数（可测{l5_total}个），按0分计",
            _l5_nomention_issue())
def diag_loading_l5(body_text, all_issues, api_scan,
                    *, doc_profile: str = _DEFAULT_DOC_PROFILE,
                    expanded_body=None
                    ) -> list[SubDimensionScore]:
    _t0 = time.monotonic()
    body_text, all_issues = normalize_entry_inputs(body_text, all_issues, text=True)
    results: list[SubDimensionScore] = []
    l5_issues: list[DocQualityIssue] = []
    l5_with_desc = 0
    l5_mentioned = 0
    l5_total = 0
    if doc_profile == "router":
        l5_score = 70.0
        l5_detail = "路由型文档：函数描述下沉到引用指南"
    elif has_code_surface(api_scan) is False:
        l5_score = NO_CODE_SCORE
        l5_detail = NO_CODE_DETAIL
    elif has_scan_files(api_scan):
        l5_issues, l5_with_desc, l5_mentioned, l5_total = _l5_audit_functions(
            expanded_body if isinstance(expanded_body, str) else body_text,
            api_scan)
        l5_score, l5_detail, l5_tail_issue = _l5_assess(
            l5_total, l5_mentioned, l5_with_desc, doc_profile=doc_profile)
        if l5_tail_issue is not None:
            l5_issues.append(l5_tail_issue)
    else:
        l5_score = _LOADING_NOSCAN_SCORE
        l5_detail = "无法扫描"
        l5_issues.append(make_noscan_issue(
            "loading", "SD-L5-NOSCAN", "函数描述质量"))
    all_issues.extend(l5_issues)
    results.append(SubDimensionScore(
        dim_id='L5',
        dim_name='函数描述质量',
        category='loading',
        weight=0.2,
        score=l5_score,
        issues=l5_issues,
        detail=l5_detail
    ))
    write_module_run(
        "skill_doc_structure", "diag_loading_l5",
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        l5_score=l5_score, issues=len(l5_issues),
        mentioned=l5_mentioned, total=l5_total)
    return results

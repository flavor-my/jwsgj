from __future__ import annotations

import logging
import math
import os
import re
from collections.abc import Callable, Iterable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

try:
    import yaml
except ImportError as _yaml_err:
    logging.getLogger(__name__).debug("PyYAML 未安装，frontmatter 解析降级为空 dict: %s", _yaml_err)
    yaml = None
from jwsgj.build_matching_diagnoser import diag_skill_full_pipeline
from jwsgj.build_skill_api_contract import scan_skill_api
from jwsgj.build_skill_md_quality import diag_upload, diag_upload_u1u2
from jwsgj.build_text_document import (
    detect_doc_profile,
    iter_matching_files,
    normalize_str,
    normalize_text,
    strip_fenced_blocks,
)
from jwsgj.build_text_frontmatter import (
    extract_frontmatter_fields,
    load_frontmatter,
    parse_frontmatter,
)
from jwsgj.build_text_scoring import (
    count_keyword_hits,
    matching_dimensions,
)
from jwsgj.diag_guard_io import (
    normalize_path_arg,
    resolve_skill_dir,
)
from jwsgj.diag_types_defs import (
    DocQualityIssue,
    DocQualityReport,
    SubDimensionScore,
    make_matching_issue,
)
from jwsgj.html_render_pipeline import generate_html_report
from jwsgj.shared_cache import ensure_entry_warmed
from jwsgj.skill_doc_structure import (
    _split_h2_sections,
    check_c9_c6_c7,
    diag_capture_c1c3,
    diag_capture_c4c5,
    diag_capture_fallback,
    diag_loading_l1l2,
    diag_loading_l3l4,
    diag_loading_l5,
)
from jwsgj.skill_doc_subdim_content import (
    check_q9_q10_q11,
    diag_content,
    diag_content_q1q4,
    diag_content_q5q6,
    diag_content_q7q8,
    expand_linked_docs,
)

__all__ = [
    'PATTERNS',
    'PATTERN_HINTS',
    'PATTERN_KEYWORDS',
    'PatternMatchSpec',
    'SkillAnalysis',
    'SkillDocDiagnoser',
    'batch_diag_skill_docs',
    'detect_patterns',
    'diag_skill_doc',
    'diag_skill_doc_to_markdown',
    'get',
    'get_doc_diagnoser',
    'get_pattern_hint',
    'infer_design_pattern',
    'list_all_patterns',
    'platform_pipeline_issues',
    'recommend_pattern',
    'validate_refactor_content',
]
_log = logging.getLogger(__name__)
_PACKAGE_NAME = (__package__
                 or os.path.basename(os.path.dirname(os.path.abspath(__file__))))
def _normalize_md_text(content: str) -> str:
    return (content.removeprefix("\ufeff")
            .replace("\r\n", "\n").replace("\r", "\n"))
def _skill_dir_of(md_path: Any) -> str:
    normalized = normalize_path_arg(md_path)
    if not isinstance(normalized, str) or not normalized.strip():
        return ""
    return (resolve_skill_dir(normalized)
            or os.path.dirname(os.path.abspath(normalized)))
def _uv000_report(md_path: str, description: str,
                  suggestion: str) -> DocQualityReport:
    path_text = md_path if isinstance(md_path, str) else ""
    return DocQualityReport(
        skill_name="(未知)", skill_path=path_text,
        total_issues=1,
        issues=[DocQualityIssue(
            category="upload", rule_id="UV-000", severity="critical",
            description=str(description)[:120], suggestion=suggestion,
            location=path_text[:200],
        )],
    )
def _read_md_text(md_path: str) -> tuple[str, DocQualityReport | None]:
    try:
        with open(md_path, "r", encoding="utf-8-sig") as f:
            content = f.read()
    except FileNotFoundError:
        return "", _uv000_report(md_path, "文件不存在",
                                 "确认 SKILL.md 路径正确")
    except (OSError, UnicodeDecodeError) as e:
        _log.warning("[SkillDoc] SKILL.md 读取失败: %s", e)
        return "", _uv000_report(
            md_path,
            f"SKILL.md 读取失败: {type(e).__name__}: {str(e)[:120]}",
            "确认文件编码为 UTF-8 且文件可读")
    return _normalize_md_text(content), None
def _matching_fallback(description: str) -> list[DocQualityIssue]:
    issues: list[DocQualityIssue] = []
    if not description:
        issues.append(make_matching_issue(
            "DR-001", "critical", "description 为空",
            "添加包含触发条件和能力描述的 description",
            location="frontmatter"))
    return issues
def _convert_violations_to_issues(report, category: str,
                                  default_location: str) -> list[DocQualityIssue]:
    issues: list[DocQualityIssue] = []
    for v in getattr(report, "violations", None) or []:
        _rid = normalize_str(getattr(v, "rule_id", ""))
        _cat = "loading" if _rid.startswith("LR-") else category
        issues.append(DocQualityIssue(
            category=_cat,
            rule_id=_rid,
            severity=normalize_str(getattr(v, "severity", "")) or "low",
            description=normalize_str(getattr(v, "description", "")),
            suggestion=normalize_str(getattr(v, "suggestion", "")),
            location=(normalize_str(getattr(v, "location", ""))
                      or default_location),
            matched_text=normalize_str(getattr(v, "matched_text", "")),
        ))
    return issues
def platform_pipeline_issues(md_path: str, description: str,
                             body_text: str) -> list[DocQualityIssue]:
    try:
        full_result = diag_skill_full_pipeline(md_path)
        return (_convert_violations_to_issues(
                    full_result.matching_report, "matching",
                    "frontmatter → description")
                + _convert_violations_to_issues(
                    full_result.capture_report, "capture", "正文"))
    except Exception as e:  # noqa: BLE001
        _log.warning("全链路管道失败，降级: %s", e)
        return _matching_fallback(description) + diag_capture_fallback(body_text)
_TRIGGER_KEYWORD_RE = re.compile(
    r'典型用户指令|trigger examples|触发示例|用户示例', re.IGNORECASE)
_ATX_HEADING_RE = re.compile(r'^[ ]{0,3}(#{1,6})[ \t]+')
_LIST_ITEM_RE = re.compile(r'^\s*(?:[-*+]|\d+[.)])\s+\S')
_TABLE_ROW_RE = re.compile(r'^[ \t]*\|')
_TABLE_SEP_RE = re.compile(r'^[ \t]*\|?[ \t:|-]*-[ \t:|-]*\|?[ \t]*$')
_ANCHOR_REF_RE = re.compile(
    r'(与\s*\S+\s*(配合|衔接|联动)|配合使用|前后衔接|工具链'
    r'|\b(?:works?|integrates?|pairs?|combines?)\s+with\b'
    r'|\bused?\s+(?:together\s+)?with\b|\btoolchains?\b)', re.IGNORECASE)
_SCENE_TAG_RE = re.compile(
    r'(?<![\w/(])#(?!define\b|include\b|pragma\b|ifn?def\b|endif\b|elif\b'
    r'|undef\b|error\b|line\b|region\b|endregion\b|todo\b|fixme\b)'
    r'[A-Za-z][A-Za-z0-9_\-]*\b(?![!/?])')
def _issue_list(condition: bool, factory) -> list[DocQualityIssue]:
    return [factory()] if condition else []
def _pipe_segment_count(stripped: str) -> int:
    segments = [part.strip() for part in stripped.split('|') if part.strip()]
    return len(segments) if len(segments) >= 2 else 0
def _is_example_block_start(line: str) -> bool:
    return bool(_LIST_ITEM_RE.match(line)
                or _TABLE_ROW_RE.match(line)
                or _pipe_segment_count(line.strip())
                or _quote_example_count([line]) > 0)
_TRIGGER_LABEL_RESIDUE_RE = re.compile(
    r'(?:[\s:：\-—>|*_`~，,。.；;]+'
    r'|以下是|以下为|如下所示|如下|列表|清单|below|following|list'
    r'|[（(【\[][^（）()【】\[\]]{0,24}[）)】\]])*',
    re.IGNORECASE)
def _is_trigger_label_line(line: str) -> bool:
    return bool(_TRIGGER_LABEL_RESIDUE_RE.fullmatch(
        _TRIGGER_KEYWORD_RE.sub("", line)))
def _inline_trigger_end(lines: list[str], start: int) -> int:
    j = start + 1
    start_is_label = _is_trigger_label_line(lines[start])
    while j < len(lines):
        line = lines[j]
        if _ATX_HEADING_RE.match(line):
            return j
        if line.strip():
            j += 1
            continue
        if not start_is_label:
            return j
        nxt = next((ln for ln in lines[j + 1:] if ln.strip()), "")
        if not nxt or not _is_example_block_start(nxt):
            return j
        j += 1
    return j
def _atx_heading_level(line: str) -> int:
    match = _ATX_HEADING_RE.match(line)
    return len(match.group(1)) if match else 0
def _heading_section_end(lines: list[str], start: int) -> int:
    level = _atx_heading_level(lines[start])
    j = start + 1
    while j < len(lines):
        next_level = _atx_heading_level(lines[j])
        if next_level and next_level <= level:
            break
        j += 1
    return j
def _iter_trigger_sections(text: str) -> Iterable[list[str]]:
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        if not _TRIGGER_KEYWORD_RE.search(lines[i]):
            i += 1
            continue
        if _ATX_HEADING_RE.match(lines[i]):
            j = _heading_section_end(lines, i)
            yield lines[i + 1:j]
            i = j
            continue
        end = _inline_trigger_end(lines, i)
        yield lines[i:end]
        i = end
_TABLE_EXAMPLE_HEADER_RE = re.compile(
    r"示例|例子|指令|话术|用户请求|用户输入|提问|"
    r"example|prompt|request|utterance|command", re.IGNORECASE)
def _table_cells(line: str) -> list[str]:
    return [cell.strip() for cell in line.strip().strip('|').split('|')]
def _table_example_columns(header_line: str, cell_count: int) -> tuple[int, ...]:
    columns = tuple(idx for idx, cell in enumerate(_table_cells(header_line))
                    if _TABLE_EXAMPLE_HEADER_RE.search(cell))
    if columns:
        return columns
    return tuple(range(1, cell_count)) if cell_count > 1 else (0,)
def _table_row_example_count(line: str,
                             columns: tuple[int, ...]) -> int:
    cells = _table_cells(line)
    return sum(
        len([part for part in cells[idx].split(' / ') if part.strip()])
        for idx in columns if idx < len(cells))
def _next_nonempty_line(section_lines: list[str], start: int) -> str:
    return next((ln.strip() for ln in section_lines[start:] if ln.strip()), "")
def _is_table_row(line: str, next_nonempty: str,
                  table_columns: tuple[int, ...] | None) -> bool:
    if _TABLE_ROW_RE.match(line):
        return True
    return "|" in line and (
        table_columns is not None or bool(_TABLE_SEP_RE.match(next_nonempty)))
_QUOTE_EXAMPLE_PAIR_RE = re.compile(
    r"(?<![A-Za-z0-9])'[^'\n]{1,200}'(?![A-Za-z0-9])"
    r'|"[^"\n]{1,200}"'
    r"|‘[^’]*’|“[^”]*”")
def _quote_example_count(quote_lines: list[str]) -> int:
    quote_text = "\n".join(quote_lines)
    return sum(
        1 for match in _QUOTE_EXAMPLE_PAIR_RE.finditer(quote_text)
        if match.group(0)[1:-1].strip())
def _count_section_examples(section_lines: list[str]) -> int:
    list_count = 0
    table_count = 0
    pipe_count = 0
    quote_lines: list[str] = []
    table_columns: tuple[int, ...] | None = None
    for idx, line in enumerate(section_lines):
        stripped = line.strip()
        if not stripped:
            continue
        if _LIST_ITEM_RE.match(line):
            table_columns = None
            list_count += 1
            continue
        next_nonempty = (_next_nonempty_line(section_lines, idx + 1)
                         if "|" in stripped else "")
        if _is_table_row(line, next_nonempty, table_columns):
            if _TABLE_SEP_RE.match(stripped):
                continue
            if _TABLE_SEP_RE.match(next_nonempty):
                table_columns = _table_example_columns(
                    stripped, len(_table_cells(stripped)))
                continue
            cells = _table_cells(stripped)
            if table_columns is None:
                columns = (tuple(range(1, len(cells)))
                           if len(cells) > 1 else (0,))
            else:
                columns = table_columns
            table_count += _table_row_example_count(stripped, columns)
            continue
        table_columns = None
        pipe_hit = _pipe_segment_count(stripped)
        if pipe_hit:
            pipe_count += pipe_hit
            continue
        quote_lines.append(line)
    return (list_count + table_count + pipe_count
            + _quote_example_count(quote_lines))
def _count_trigger_examples(description: str, prose_body: str) -> int:
    return sum(
        _count_section_examples(section)
        for section in _iter_trigger_sections(
            description + "\n\n" + prose_body))
_SIX03_MIN_EXAMPLES = 20
_SIX03_HIGH_SEVERITY_BELOW = 10
_SIX05_MIN_PROSE_CHARS = 100
def _six03_issue(example_count: int) -> DocQualityIssue:
    return make_matching_issue(
        "DR-SIX-03",
        ("high" if example_count < _SIX03_HIGH_SEVERITY_BELOW
         else "medium"),
        (f"典型用户指令不足（当前约 {max(example_count, 0)} 条），"
         f"建议饱和覆盖至 {_SIX03_MIN_EXAMPLES}+ 条"),
        (f"添加 {_SIX03_MIN_EXAMPLES}+ 条用户可能说出的完整句子，"
         "覆盖中文口语、英文术语、不同角色视角"),
        location="frontmatter: description / 正文")
def _six03_issues(example_count: int) -> list[DocQualityIssue]:
    return _issue_list(example_count < _SIX03_MIN_EXAMPLES,
                       lambda: _six03_issue(example_count))
def _six05_issue() -> DocQualityIssue:
    return make_matching_issue(
        "DR-SIX-05", "medium",
        "正文内容过短，无法覆盖技能全量业务功能",
        "在正文中详细列出每个具体能力点，而非仅概括性描述",
        location="body")
def _six05_issues(prose_body: str) -> list[DocQualityIssue]:
    return _issue_list(
        not prose_body
        or len(prose_body.strip()) < _SIX05_MIN_PROSE_CHARS,
        _six05_issue)
def _six06_missing_facets(prose_scan_text: str) -> list[str]:
    has_anchor_ref = bool(_ANCHOR_REF_RE.search(prose_scan_text))
    has_tags = bool(_SCENE_TAG_RE.search(prose_scan_text))
    missing: list[str] = []
    if not has_anchor_ref:
        missing.append("关联技能锚点")
    if not has_tags:
        missing.append("场景标签（#tag）")
    return missing
def _six06_issue(missing: list[str]) -> DocQualityIssue:
    return make_matching_issue(
        "DR-SIX-06", "low",
        f"缺少{'和'.join(missing)}，降低技能在上下文推理中的匹配率",
        "添加与实际业务相关的关联技能声明和场景标签（#标签）",
        location="frontmatter: description / 正文头部")
def _six06_issues(prose_scan_text: str) -> list[DocQualityIssue]:
    missing = _six06_missing_facets(prose_scan_text)
    return _issue_list(bool(missing), lambda: _six06_issue(missing))
def _six_dimension_issues(description: str,
                        body_text: str) -> list[DocQualityIssue]:
    issues: list[DocQualityIssue] = []
    description = normalize_str(description)
    body_text = normalize_str(body_text)
    prose_body = strip_fenced_blocks(body_text)
    issues.extend(_six03_issues(_count_trigger_examples(description, prose_body)))
    issues.extend(_six05_issues(prose_body))
    issues.extend(_six06_issues(description + "\n" + prose_body))
    return issues
@dataclass(frozen=True)
class _PhaseSpec:
    key: str
    label: str
    weight: float
    suggestion: str
_PHASES: tuple[_PhaseSpec, ...] = (
    _PhaseSpec(
        "matching", "匹配阶段（description 质量）", 0.20,
        ("[匹配阶段] description 质量不足，建议使用 "
         "MatchingDescriptionGenerator 生成改进版 description")),
    _PhaseSpec(
        "capture", "捕捉阶段（正文结构）", 0.15,
        ("[捕捉阶段] 正文结构存在问题，建议遵循三段式结构"
         "（触发场景 → 能力枚举 → 工作流程）重构正文")),
    _PhaseSpec(
        "loading", "深度加载（资源引用）", 0.15,
        ("[加载阶段] 资源引用或 API 覆盖存在问题，建议修复断链"
         "引用并补充入口函数说明")),
    _PhaseSpec(
        "content", "内容质量（文档完整性）", 0.30,
        ("[内容质量] 文档完整性不足，建议补充代码示例、"
         "能力边界声明等核心内容")),
    _PhaseSpec(
        "upload", "上传合规（打包校验）", 0.20,
        ("[上传合规] 存在上传校验违规，技能无法通过打包校验。"
         "建议优先修复 UV-001~UV-012 中的 critical 问题")),
)
_CAT_SCORE_WEIGHTS: dict[str, float] = {p.key: p.weight for p in _PHASES}
_PHASE_SECTIONS: tuple[tuple[str, str], ...] = tuple(
    (p.key, p.label) for p in _PHASES)
_SUGGESTION_THRESHOLDS: tuple[tuple[str, str], ...] = tuple(
    (p.key, p.suggestion) for p in _PHASES)
_GRADE_BANDS: tuple[tuple[float, str], ...] = (
    (90.0, "A"), (75.0, "B"), (60.0, "C"), (40.0, "D"),
)
_SUGGESTION_SCORE_THRESHOLD = {
    grade: band for band, grade in _GRADE_BANDS}["C"]
_MAX_CATEGORY_SCORE = 100.0
_EMPTY_CATEGORY_SCORE = _MAX_CATEGORY_SCORE
_LOW_DIM_THRESHOLD = 30.0
_LOW_DIM_PENALTY = 10.0
def _normalized_dim_score(value: Any) -> float:
    try:
        score = float(value)
    except (TypeError, ValueError, OverflowError):
        return 0.0
    if not math.isfinite(score):
        return 0.0
    return min(_MAX_CATEGORY_SCORE, max(0.0, score))
def _unweighted_average(scores: list[float]) -> float:
    return round(math.fsum(scores) / len(scores), 1)
def _valid_dim_weights(
    cat_dims: list[SubDimensionScore],
) -> list[float] | None:
    try:
        weights = [float(d.weight) for d in cat_dims]
    except (TypeError, ValueError, OverflowError):
        return None
    if (any(not math.isfinite(weight) or weight < 0 for weight in weights)
            or not weights or max(weights) <= 0):
        return None
    return weights
def _weighted_category_average(cat_dims: list[SubDimensionScore]) -> float:
    if not cat_dims:
        return _EMPTY_CATEGORY_SCORE
    scores = [_normalized_dim_score(d.score) for d in cat_dims]
    weights = _valid_dim_weights(cat_dims)
    if weights is None:
        return _unweighted_average(scores)
    weight_scale = max(weights)
    scaled_weights = [weight / weight_scale for weight in weights]
    weighted_sum = math.fsum(
        score * weight
        for score, weight in zip(scores, scaled_weights, strict=True))
    return round(weighted_sum / math.fsum(scaled_weights), 1)
def _category_score(cat_dims: list[SubDimensionScore]) -> float:
    if not cat_dims:
        return _EMPTY_CATEGORY_SCORE
    base = _weighted_category_average(cat_dims)
    weights = _valid_dim_weights(cat_dims)
    low_count = sum(
        1 for index, dim in enumerate(cat_dims)
        if _normalized_dim_score(dim.score) < _LOW_DIM_THRESHOLD
        and (weights is None or weights[index] > 0))
    return round(max(0.0, base - _LOW_DIM_PENALTY * low_count), 1)
def _grade_of(overall: float) -> str:
    return next((g for band, g in _GRADE_BANDS if overall >= band), "F")
def _count_issues_by_category(all_issues) -> dict[str, int]:
    counts: dict[str, int] = {}
    for issue in all_issues:
        cat = getattr(issue, "category", "")
        if isinstance(cat, str) and cat:
            counts[cat] = counts.get(cat, 0) + 1
    return counts
def _phase_summary(cat_dims_map: dict[str, list[SubDimensionScore]],
                   scores: dict[str, float],
                   all_issues: list[DocQualityIssue]) -> dict[str, str]:
    issue_counts = _count_issues_by_category(all_issues)
    summary: dict[str, str] = {}
    for cat, cat_dims in cat_dims_map.items():
        issue_count = issue_counts.get(cat, 0)
        dim_details = ", ".join(f"{d.dim_id}={d.score:.0f}" for d in cat_dims)
        summary[cat] = (f"{scores.get(cat, 0):.1f} ({issue_count} 项问题)"
                        f" [{dim_details}]")
    return summary
def _severity_suggestion_lines(all_issues) -> list[str]:
    lines: list[str] = []
    criticals = [i for i in all_issues if i.severity == "critical"]
    highs = [i for i in all_issues if i.severity == "high"]
    if criticals:
        lines.append(f"[紧急] 存在 {len(criticals)} 项严重问题，建议优先修复")
    if highs:
        lines.append(f"[重要] 存在 {len(highs)} 项高级别问题，建议尽快处理")
    return lines
def _threshold_suggestion_lines(scores: dict[str, Any]) -> list[str]:
    lines: list[str] = []
    for _key, _message in _SUGGESTION_THRESHOLDS:
        if scores.get(_key, 0.0) < _SUGGESTION_SCORE_THRESHOLD:
            lines.append(_message)
    if scores.get("grade", "F") in ("D", "F"):
        lines.append(
            "[全链路] 综合评分过低，建议使用 SkillDocCreator 完全重建 SKILL.md")
    return lines
def _merge_issue_suggestions(suggestions: list[str],
                             all_issues: list[DocQualityIssue]) -> list[str]:
    seen = set(suggestions)
    for i in all_issues:
        if i.suggestion and i.suggestion not in seen:
            suggestions.append(i.suggestion)
            seen.add(i.suggestion)
    return suggestions
class SkillDocDiagnoser:
    def diag(self, md_path: str, skill_dir: str | None = None) -> DocQualityReport:
        md_path = normalize_path_arg(md_path)
        if not isinstance(md_path, str) or not md_path.strip():
            return _uv000_report(
                md_path, "md_path 必须为非空字符串",
                "传入 SKILL.md 的绝对路径或相对路径")
        content, degraded_report = _read_md_text(md_path)
        if degraded_report is not None:
            return degraded_report
        name, description, _keywords, body_text, _parsed_skill_dir = self.parse_document(content, md_path)
        _norm_dir = normalize_path_arg(skill_dir)
        skill_dir = (_norm_dir
                     if isinstance(_norm_dir, str) and _norm_dir.strip()
                     else _parsed_skill_dir)
        all_issues: list[DocQualityIssue] = platform_pipeline_issues(
            md_path, description, body_text)
        all_issues.extend(diag_upload(content, md_path, skill_dir))
        all_issues.extend(diag_content(body_text, skill_dir))
        all_issues.extend(_six_dimension_issues(description, body_text))
        sub_dims = self._run_sub_dimension_diagnosis(
            body_text, description, skill_dir, all_issues, md_path,
        )
        scores = self._compute_scores_from_sub_dims(sub_dims, all_issues)
        return self._build_report(
            name, md_path, skill_dir, all_issues, sub_dims, scores)
    def _build_report(
        self, name: str, md_path: str, skill_dir: str,
        all_issues: list[DocQualityIssue],
        sub_dims: list[SubDimensionScore], scores: dict[str, Any],
    ) -> DocQualityReport:
        dir_name = os.path.basename(os.path.normpath(skill_dir)) if skill_dir else ""
        return DocQualityReport(
            skill_name=name or dir_name,
            skill_path=md_path,
            total_issues=len(all_issues),
            issues=all_issues,
            matching_score=scores["matching"],
            capture_score=scores["capture"],
            loading_score=scores["loading"],
            content_score=scores["content"],
            upload_score=scores["upload"],
            overall_score=scores["overall"],
            overall_grade=scores["grade"],
            phase_summary=scores["summary"],
            suggestions=self._generate_suggestions(scores, all_issues),
            sub_dimensions=sub_dims,
        )
    def parse_document(self, content: str, md_path: str):
        content = _normalize_md_text(content)
        name, description, keywords, body_start = (
            extract_frontmatter_fields(content))
        body_text = content if body_start is None else content[body_start:].strip()
        skill_dir = _skill_dir_of(md_path)
        return name, description, keywords, body_text, skill_dir
    def _run_sub_dimension_diagnosis(
        self, body_text: str, description: str, skill_dir: str,
        all_issues: list[DocQualityIssue], md_path: str,
    ) -> list[SubDimensionScore]:
        dims: list[SubDimensionScore] = []
        api_scan = scan_skill_api(skill_dir)
        platform_loading_issues = [i for i in all_issues if i.category == "loading"]
        sections_found = _split_h2_sections(body_text)
        doc_profile = detect_doc_profile(sections_found, body_text)
        expanded_body = expand_linked_docs(md_path, body_text, skill_dir)
        dims.extend(matching_dimensions(description, all_issues, doc_profile))
        dims.extend(diag_capture_c1c3(
            body_text, all_issues, api_scan, sections_found,
            doc_profile=doc_profile))
        dims.extend(diag_capture_c4c5(
            body_text, all_issues, api_scan, sections_found,
            doc_profile=doc_profile, expanded_body=expanded_body))
        dims.extend(check_c9_c6_c7(
            sections_found, api_scan, all_issues, skill_dir,
            doc_profile=doc_profile))
        dims.extend(diag_loading_l1l2(body_text, skill_dir, all_issues, platform_loading_issues, sections_found))
        dims.extend(diag_loading_l3l4(
            body_text, all_issues, api_scan, sections_found,
            doc_profile=doc_profile, expanded_body=expanded_body))
        dims.extend(diag_loading_l5(
            body_text, all_issues, api_scan, doc_profile=doc_profile,
            expanded_body=expanded_body))
        dims.extend(diag_content_q1q4(
            body_text, description, all_issues, api_scan, skill_dir,
            doc_profile=doc_profile, expanded_body=expanded_body))
        dims.extend(diag_content_q5q6(
            body_text, all_issues, api_scan,
            doc_profile=doc_profile, expanded_body=expanded_body))
        dims.extend(diag_content_q7q8(
            body_text, all_issues, sections_found, doc_profile=doc_profile))
        dims.extend(check_q9_q10_q11(
            sections_found, api_scan, all_issues,
            doc_profile=doc_profile, expanded_body=expanded_body))
        dims.extend(diag_upload_u1u2(all_issues))
        return dims
    def _generate_suggestions(self,
                              scores: dict[str, Any],
                              all_issues: list[DocQualityIssue] | None = None,
                              ) -> list[str]:
        if all_issues is None:
            all_issues = []
        suggestions = _severity_suggestion_lines(all_issues)
        suggestions.extend(_threshold_suggestion_lines(scores))
        return _merge_issue_suggestions(suggestions, all_issues)
    def _compute_scores_from_sub_dims(
        self, sub_dims: list[SubDimensionScore],
        all_issues: list[DocQualityIssue],
    ) -> dict[str, Any]:
        categories = list(_CAT_SCORE_WEIGHTS)
        cat_dims_map = {cat: [d for d in sub_dims if d.category == cat]
                        for cat in categories}
        scores = {cat: _category_score(cat_dims_map[cat]) for cat in categories}
        overall = round(
            sum(scores.get(k, 0) * w for k, w in _CAT_SCORE_WEIGHTS.items()), 1)
        return {
            **scores,
            "overall": overall,
            "grade": _grade_of(overall),
            "summary": _phase_summary(cat_dims_map, scores, all_issues),
        }
_diagnoser_instance = SkillDocDiagnoser()
def get_doc_diagnoser() -> SkillDocDiagnoser:
    return _diagnoser_instance
def _emit_doc_diag_html(md_path: str, report: DocQualityReport) -> None:
    try:
        payload = report.to_dict() if hasattr(report, "to_dict") else {}
        payload["_step_name"] = "doc_diag"
        _sd = _skill_dir_of(md_path)
        generate_html_report(payload, _sd, "step")
    except Exception as _de:  # noqa: BLE001
        _log.warning("doc_diag HTML 报告生成失败(不阻断): %s", _de)
def _diag_input_error_report(md_path: str, message: str) -> DocQualityReport:
    _err_report = _uv000_report(
        md_path, message, "确认 SKILL.md 路径正确且 YAML frontmatter 有效")
    _emit_doc_diag_html(md_path, _err_report)
    return _err_report
def _ensure_diag_ready(md_path: Any, entry_tag: str) -> tuple[str, str]:
    md_path = normalize_path_arg(md_path)
    if not isinstance(md_path, str) or not md_path.strip():
        _log.warning("%s: md_path 为空或类型无效, got=%r", entry_tag, md_path)
        return md_path, "md_path 必须为非空字符串"
    try:
        is_file = os.path.isfile(md_path)
    except OSError as e:
        _log.warning("%s: 路径查询失败, path=%s, error=%s",
                     entry_tag, md_path, e)
        return md_path, f"SKILL.md 路径不可访问: {type(e).__name__}"
    if not is_file:
        _log.warning("%s: 文件不存在, path=%s", entry_tag, md_path)
        return md_path, f"SKILL.md 不存在: {md_path}"
    try:
        ensure_entry_warmed(_skill_dir_of(md_path),
                            None, f"文档诊断 {entry_tag}")
    except Exception as e:  # noqa: BLE001
        _log.warning("%s: 缓存预热失败，降级为无缓存诊断: %s", entry_tag, e)
    return md_path, ""
def diag_skill_doc(md_path: str) -> DocQualityReport:
    md_path, _err = _ensure_diag_ready(md_path, "diag_skill_doc")
    if _err:
        return _diag_input_error_report(md_path, _err)
    try:
        _log.info("diag_skill_doc: 开始诊断, path=%s", md_path)
        _doc_report = get_doc_diagnoser().diag(md_path)
        _emit_doc_diag_html(md_path, _doc_report)
        return _doc_report
    except Exception as e:  # noqa: BLE001
        _log.error("diag_skill_doc 异常: %s", e, exc_info=True)
        return _diag_input_error_report(md_path, f"诊断执行异常: {e}")
_SEVERITY_LABELS: dict[str, str] = {
    "critical": "严重", "high": "高", "medium": "中", "low": "低"}
def _md_table_cell(value: Any) -> str:
    text = value if isinstance(value, str) else str(value)
    return (text.replace("\\", "\\\\").replace("|", "\\|")
            .replace("\r\n", "<br>").replace("\r", "<br>")
            .replace("\n", "<br>"))
def _md_phase_rows(report: DocQualityReport) -> list[str]:
    rows = []
    for phase_key, phase_name in _PHASE_SECTIONS:
        score = getattr(report, f"{phase_key}_score", 0.0)
        summary = report.phase_summary.get(phase_key, "")
        rows.append(
            f"| {_md_table_cell(phase_name)} | {score:.1f} | "
            f"{_md_table_cell(summary)} |")
    return rows
def _md_subdim_rows(report: DocQualityReport) -> list[str]:
    return [
        f"| {_md_table_cell(f'{sd.dim_id} {sd.dim_name}')} | "
        f"{_md_table_cell(sd.category)} | {sd.score:.1f} | "
        f"{sd.weight:.1f} | {_md_table_cell(sd.detail)} |"
        for sd in report.sub_dimensions
    ]
def _severity_key_of(issue: DocQualityIssue) -> str:
    sev = issue.severity
    return sev if isinstance(sev, str) and sev else "unknown"
def _severity_order(by_severity: dict[str, list[DocQualityIssue]]) -> list[str]:
    ordered = [sev for sev in ("critical", "high", "medium", "low")
               if sev in by_severity]
    ordered.extend(sev for sev in by_severity if sev not in ordered)
    return ordered
def _md_issue_entry_lines(index: int, issue: DocQualityIssue) -> list[str]:
    lines = [
        f"**{index}. [{issue.category}] {issue.description}**",
        f"    - 位置: {issue.location}",
        f"    - 建议: {issue.suggestion}",
    ]
    if issue.matched_text:
        lines.append(f"    - 触发文本: `{issue.matched_text[:100]}`")
    lines.append("")
    return lines
def _md_issues_block(report: DocQualityReport) -> list[str]:
    if not report.issues:
        return ["无违规项。"]
    lines: list[str] = []
    by_severity: dict[str, list[DocQualityIssue]] = {}
    for issue in report.issues:
        by_severity.setdefault(_severity_key_of(issue), []).append(issue)
    for sev in _severity_order(by_severity):
        sev_label = _SEVERITY_LABELS.get(sev, sev)
        items = by_severity[sev]
        lines.append(f"### [{sev_label}] {sev.upper()} — {len(items)} 项")
        lines.append("")
        for i, issue in enumerate(items, 1):
            lines.extend(_md_issue_entry_lines(i, issue))
    return lines
def _render_report_markdown(report: DocQualityReport) -> str:
    lines = [
        f"# 技能文档诊断报告：{report.skill_name}",
        "",
        f"**文件路径**: {report.skill_path}",
        f"**综合评分**: {report.overall_score:.1f}/100 — **等级：{report.overall_grade}**",
        "",
        "## 阶段评分",
        "",
        "| 阶段 | 评分 | 说明 |",
        "|------|------|------|",
    ]
    lines.extend(_md_phase_rows(report))
    if report.sub_dimensions:
        lines.extend([
            "",
            "## 子维度评分明细",
            "",
            "| 子维度 | 所属大类 | 评分 | 权重 | 说明 |",
            "|--------|----------|------|------|------|",
        ])
        lines.extend(_md_subdim_rows(report))
    lines.extend([
        "",
        f"## 发现的问题（共 {report.total_issues} 项）",
        "",
    ])
    lines.extend(_md_issues_block(report))
    if report.suggestions:
        lines.extend(["## 改进建议", ""])
        lines.extend(f"- {s}" for s in report.suggestions)
    return "\n".join(lines)
def diag_skill_doc_to_markdown(md_path: str) -> str:
    md_path, _err = _ensure_diag_ready(md_path, "diag_skill_doc_to_markdown")
    if _err:
        return f"错误: {_err}"
    _log.info("diag_skill_doc_to_markdown: 开始诊断并生成Markdown报告, path=%s", md_path)
    try:
        report = get_doc_diagnoser().diag(md_path)
        return _render_report_markdown(report)
    except Exception as e:  # noqa: BLE001
        _log.error("diag_skill_doc_to_markdown 异常: %s", e, exc_info=True)
        return f"错误: 诊断执行异常: {str(e)[:200]}"
@dataclass
class PatternMatchSpec:
    pattern: str
    confidence: float
    evidence: list[str] = field(default_factory=list)
    recommendation: str = ""
@dataclass
class SkillAnalysis:
    skill_name: str
    skill_path: str
    detected_patterns: list[PatternMatchSpec] = field(default_factory=list)
    recommended_pattern: str | None = None
    warnings: list[str] = field(default_factory=list)
_TOOL_LIKE_NAME_KEYWORDS = ("tool", "api", "client", "browser",
                            "工具", "接口", "客户端", "浏览器")
_OUTPUT_FORMAT_KEYWORDS = ("output", "format", "输出", "格式")
_DETECT_MIN_CONFIDENCE = 0.3
_KW_MIN_HITS = 2
class _Scorer:
    __slots__ = ("_signals", "evidence", "score")
    def __init__(self, signals: dict[str, float]):
        self._signals = signals
        self.score: float = 0.0
        self.evidence: list[str] = []
    def hit(self, key: str, message: str, scale: float = 1.0) -> None:
        self.evidence.append(message)
        self.score += self._signals.get(key, 0.0) * scale
    def keywords(self, body: str, keywords: Any, key: str, label: str,
                 per_hit: float) -> int:
        hits = count_keyword_hits(body, keywords)
        if hits >= _KW_MIN_HITS:
            self.hit(key, f"含 {hits} 个{label}", min(hits / per_hit, 1.0))
        return hits
def _match_tool_wrapper(pattern_def: dict, body: str, frontmatter: dict,
                        has_references: bool, skill_name: str) -> tuple[float, list[str]]:
    scorer = _Scorer(pattern_def["signals"])
    if has_references:
        scorer.hit("has_references", "有 references/ 目录")
    scorer.keywords(body, pattern_def["keywords"], "api_keywords", " API 关键词", 4)
    _deps = (frontmatter.get("dependencies")
             or frontmatter.get("requires")
             or frontmatter.get("requirements"))
    if _deps:
        scorer.hit("external_dependency", "声明外部依赖")
    _name = skill_name.lower() if isinstance(skill_name, str) else ""
    if count_keyword_hits(_name, _TOOL_LIKE_NAME_KEYWORDS):
        scorer.hit("tool_like_name", "名称含工具类关键词")
    return scorer.score, scorer.evidence
def _match_generator(pattern_def: dict, body: str, has_references: bool,
                     has_assets: bool) -> tuple[float, list[str]]:
    scorer = _Scorer(pattern_def["signals"])
    if has_assets:
        scorer.hit("has_assets", "有 assets/ 目录")
    if has_references:
        scorer.hit("has_references", "有 references/ 目录")
    scorer.keywords(body, pattern_def["keywords"], "generate_keywords", "生成关键词", 4)
    if count_keyword_hits(body, _OUTPUT_FORMAT_KEYWORDS):
        scorer.hit("output_format_specified", "指定输出格式")
    return scorer.score, scorer.evidence
def _match_reviewer(pattern_def: dict, body: str, has_checklist: bool,
                    has_severity_levels: bool,
                    has_scoring_mechanism: bool) -> tuple[float, list[str]]:
    scorer = _Scorer(pattern_def["signals"])
    if has_checklist:
        scorer.hit("has_checklist", "有检查清单文件")
    scorer.keywords(body, pattern_def["keywords"], "review_keywords", "审查关键词", 4)
    if has_severity_levels:
        scorer.hit("severity_levels", "定义严重级别")
    if has_scoring_mechanism:
        scorer.hit("scoring_mechanism", "有评分机制")
    return scorer.score, scorer.evidence
def _match_inversion(pattern_def: dict, body: str,
                     has_gate: bool) -> tuple[float, list[str]]:
    scorer = _Scorer(pattern_def["signals"])
    english_prompt = (
        re.search(r"\bask(?:s|ed|ing)?\b", body)
        and re.search(r"\bquestions?\b", body))
    if english_prompt or "提问" in body:
        scorer.hit("multi_turn", "多轮交互模式")
    phase_count = len(set(re.findall(r"(?:phase|阶段)\s*(\d+)", body)))
    if phase_count >= 2:
        scorer.hit("question_phases", "分阶段提问")
    if has_gate:
        scorer.hit("gate_mechanism", "有门禁机制")
    scorer.keywords(body, pattern_def["keywords"], "planning_keywords", "规划关键词", 3)
    return scorer.score, scorer.evidence
def _match_pipeline(pattern_def: dict, body: str, step_pattern: list[str],
                    has_gate: bool) -> tuple[float, list[str]]:
    scorer = _Scorer(pattern_def["signals"])
    if len(step_pattern) >= 2:
        scorer.hit("sequential_steps", f"有 {len(step_pattern)} 个顺序步骤")
    if has_gate:
        scorer.hit("gate_per_step", "有门禁机制")
    if "验证" in body or re.search(r"(?:\b|(?<=_))(?:verif(?:y|ies|ied|ic)|check)", body):
        scorer.hit("verification_points", "有验证点")
    scorer.keywords(body, pattern_def["keywords"], "pipeline_keywords", "流水线关键词", 3)
    return scorer.score, scorer.evidence
def _match_adapter(pattern_def: dict, body: str) -> tuple[float, list[str]]:
    scorer = _Scorer(pattern_def["signals"])
    fmt_count = len(re.findall(
        r'(?:(?:\b|(?<=_))(?:format|convert)|格式|转换)', body))
    if fmt_count >= 2:
        scorer.hit("multi_format", f"涉及 {fmt_count} 种格式/转换信号")
    scorer.keywords(body, pattern_def["keywords"], "convert_keywords", "转换关键词", 4)
    if re.search(r'(?:(?:\b|(?<=_))input|输入).{0,20}(?:(?:\b|(?<=_))output|输出)', body):
        scorer.hit("input_output_mismatch", "存在输入/输出形态差异描述")
    fmt_kw = count_keyword_hits(
        body, ("pdf", "docx", "xlsx", "pptx", "csv", "json", "html", "md"))
    if fmt_kw >= _KW_MIN_HITS:
        scorer.hit("format_keywords", f"覆盖 {fmt_kw} 种文件格式")
    return scorer.score, scorer.evidence
def _match_strategy(pattern_def: dict, body: str,
                    has_references: bool) -> tuple[float, list[str]]:
    scorer = _Scorer(pattern_def["signals"])
    if re.search(r'(?:(?:\b|(?<=_))strateg(?:y|ies)|策略|算法|(?:\b|(?<=_))algorithm).{0,30}(?:(?:\b|(?<=_))(?:switch|select)|选择|切换|根据)', body):
        scorer.hit("conditional_dispatch", "存在按条件选择策略的描述")
    strat_count = len(re.findall(r'(?:(?:\b|(?<=_))strateg(?:y|ies)|策略|算法)', body))
    if strat_count >= 2:
        scorer.hit("multiple_strategies", f"提及 {strat_count} 处策略/算法")
    if has_references or "plugin" in body or "插件" in body:
        scorer.hit("plugin_like", "插件式扩展（references/ 或 plugin 信号）")
    scorer.keywords(body, pattern_def["keywords"], "strategy_keywords", "策略关键词", 4)
    return scorer.score, scorer.evidence
def _match_router(pattern_def: dict, body: str) -> tuple[float, list[str]]:
    scorer = _Scorer(pattern_def["signals"])
    entry_count = len(re.findall(r'(?:入口|(?:\b|(?<=_))entr(?:y|ies))', body))
    if entry_count >= 2 or re.search(r'(?:统一入口|快捷入口)', body):
        scorer.hit("multi_entry", "多个入口/统一入口描述")
    if re.search(r'(?:意图|(?:\b|(?<=_))intent|语义匹配|路由表)', body):
        scorer.hit("intent_matching", "意图/语义匹配描述")
    if re.search(r'(?:(?:\b|(?<=_))(?:dispatch|route)|分发|路由)', body):
        scorer.hit("dispatch_table", "分发/路由机制描述")
    scorer.keywords(body, pattern_def["keywords"], "router_keywords", "路由关键词", 4)
    return scorer.score, scorer.evidence
def _match_command(pattern_def: dict, body: str) -> tuple[float, list[str]]:
    scorer = _Scorer(pattern_def["signals"])
    if re.search(r'(?:(?:\b|(?<=_))(?:undo|rollback)|撤销|回滚|撤回)', body):
        scorer.hit("undo_support", "支持撤销/回滚")
    if re.search(r'(?:(?:\b|(?<=_))queue|队列|排队)', body):
        scorer.hit("queue_mechanism", "队列化机制")
    if re.search(r'(?:日志|(?:\b|(?<=_))log(?:s|ged|ging)?\b|审计记录|\baudit trail)', body):
        scorer.hit("action_logging", "操作日志记录")
    scorer.keywords(body, pattern_def["keywords"], "command_keywords", "命令关键词", 4)
    return scorer.score, scorer.evidence
def _match_facade(pattern_def: dict, body: str) -> tuple[float, list[str]]:
    scorer = _Scorer(pattern_def["signals"])
    if re.search(r'(?:统一入口|一站式|one-stop|快捷入口)', body):
        scorer.hit("single_entry", "单一统一入口")
    if re.search(r'(?:简化|封装|(?:\b|(?<=_))(?:facade|hide|hidden)|隐藏)', body):
        scorer.hit("simplified_api", "简化接口描述")
    if len(re.findall(r'模块', body)) >= 3 or len(re.findall(r'subsystem|子系统', body)) >= 1:
        scorer.hit("multi_subsystem", "聚合多个子模块")
    scorer.keywords(body, pattern_def["keywords"], "facade_keywords", "门面关键词", 4)
    return scorer.score, scorer.evidence
_MATCHER_SPECS: dict[str, tuple[Callable[..., Any], tuple[str, ...]]] = {
    "Tool Wrapper": (_match_tool_wrapper, ("frontmatter", "has_references", "skill_name")),
    "Generator": (_match_generator, ("has_references", "has_assets")),
    "Reviewer": (_match_reviewer, ("has_checklist", "has_severity_levels", "has_scoring_mechanism")),
    "Inversion": (_match_inversion, ("has_gate",)),
    "Pipeline": (_match_pipeline, ("step_pattern", "has_gate")),
    "Adapter": (_match_adapter, ()),
    "Strategy": (_match_strategy, ("has_references",)),
    "Router": (_match_router, ()),
    "Command": (_match_command, ()),
    "Facade": (_match_facade, ()),
}
_REQUIRED_FRONTMATTER_FIELDS = (
    ("name", "方案 frontmatter 缺少 name 字段"),
    ("description", "方案 frontmatter 缺少 description 字段"),
)
def _find_frontmatter_end(lines: list[str]) -> int | None:
    return next(
        (i for i, ln in enumerate(lines[1:], 1)
         if ln.strip() == "---" and not ln[:1].isspace()),
        None)
def validate_refactor_content(new_content: str) -> str | None:
    if not isinstance(new_content, str):
        return "方案内容必须为文本"
    lines = _normalize_md_text(new_content).split("\n")
    if not lines or lines[0].rstrip() != "---":
        return "方案内容缺少 frontmatter 起始分隔符 ---"
    fm_end = _find_frontmatter_end(lines)
    if fm_end is None:
        return "方案内容 frontmatter 块不完整（缺少闭合 ---）"
    fm_lines = lines[1:fm_end]
    meta, reason, detail = load_frontmatter("\n".join(fm_lines))
    if reason == "no_yaml":
        return "方案 frontmatter 无法校验：PyYAML 未安装"
    if reason:
        detail_text = "解析结果不是字典" if reason == "not_dict" else detail
        return f"方案 frontmatter YAML 无效：{detail_text[:160]}"
    if not isinstance(meta, dict):
        return "方案 frontmatter YAML 无效：解析结果不是字典"
    for field_name, missing_message in _REQUIRED_FRONTMATTER_FIELDS:
        value = meta.get(field_name)
        if value is None or (isinstance(value, str) and not value.strip()):
            return missing_message
        if not isinstance(value, str):
            return (f"方案 frontmatter 字段 {field_name} 类型错误"
                    f"（{type(value).__name__}），应为字符串")
    return None
def _parse_skill_frontmatter(content: str) -> dict:
    fm_text, _body = parse_frontmatter(content)
    if fm_text is None:
        return {}
    meta, reason, detail = load_frontmatter(fm_text)
    if reason == "no_yaml":
        _log.warning("[SkillDoc] PyYAML 未安装，frontmatter 字段按空处理")
        return {}
    if reason:
        _log.warning("[SkillDoc] frontmatter 不可用于模式识别（%s），字段按空处理: %s",
                     reason, detail)
        return {}
    return meta if isinstance(meta, dict) else {}
def _snapshot_skill_dir(skill_dir: Path) -> dict:
    has_references = (skill_dir / "references").is_dir()
    assets_dir = skill_dir / "assets"
    has_assets = assets_dir.is_dir()
    has_checklist = False
    has_templates = False
    if has_references:
        try:
            has_checklist = any(
                f.is_file()
                and ("checklist" in f.name.lower() or "review" in f.name.lower())
                for f in (skill_dir / "references").iterdir()
            )
        except OSError as e:
            _log.warning("references/ 目录扫描失败: %s", e)
    if has_assets:
        try:
            has_templates = any(path.is_file() for path in assets_dir.rglob("*"))
        except OSError as e:
            _log.warning("assets/ 目录扫描失败: %s", e)
    return {
        "has_references": has_references,
        "has_assets": has_assets,
        "has_checklist": has_checklist,
        "has_templates": has_templates,
    }
def _resolve_matcher(
        pattern_name: str, pattern_def: Any,
) -> tuple[Callable[..., Any], tuple[str, ...]] | None:
    spec = _MATCHER_SPECS.get(pattern_name)
    if spec is None and isinstance(pattern_name, str):
        spec = _MATCHER_SPECS_BY_KEY.get(_pattern_key(pattern_name))
    if spec is None:
        _log.debug("模式 %r 匹配器未接线，跳过评分（可用: %s）",
                     pattern_name, sorted(_MATCHER_SPECS))
        return None
    if not (isinstance(pattern_def, dict)
            and isinstance(pattern_def.get("signals"), dict)
            and isinstance(pattern_def.get("keywords"), list)):
        _log.debug("模式 %r 定义形态异常（缺 signals/keywords），跳过评分", pattern_name)
        return None
    return spec
def _build_matcher_args(pattern_name: str, pattern_def: dict, body: str,
                        ctx: dict) -> tuple[float, list[str]] | None:
    spec = _resolve_matcher(pattern_name, pattern_def)
    if spec is None:
        return None
    matcher, params = spec
    return matcher(pattern_def, body, *(ctx[k] for k in params))
_GATE_SIGNAL_RE = re.compile(
    r"(?:\bgates?\b|门禁|阻断|\bblock(?:ed|ing)\b|must\s+pass"
    r"|[未不]通过|(?:满足|符合)[^。\n]{0,12}条件)", re.IGNORECASE)
_GATE_CN_QUALIFIER = r"(?:显式|明确|有效|任何|实际|真正|真实|必要)(?:的)?"
_GATE_EN_QUALIFIER = (
    r"(?:a|an|any|the|explicit|real|actual|formal|proper|valid|working)"
)
_GATE_ABSENCE_PREFIX_RE = re.compile(
    rf"(?:(?:缺少|没有(?:设置|配置|建立)?|无|不含|无需|不需要|尚未|"
    rf"未(?:设置|配置|建立|提供)|不(?:具备|具有|提供|支持))"
    rf"(?:{_GATE_CN_QUALIFIER})?"
    rf"|(?<![A-Za-z0-9_])(?:without|no)"
    rf"(?:\s+{_GATE_EN_QUALIFIER}){{0,3}})\s*$",
    re.IGNORECASE)
_GATE_NEGATED_OPERATION_PREFIX_RE = re.compile(
    rf"(?:不(?:是|算|等于)?(?:{_GATE_CN_QUALIFIER})?"
    r"|(?<![A-Za-z0-9_])(?:not|without|cannot|[a-z]+n't)"
    r"(?:\s+(?!only\b|just\b)[a-z][a-z'-]*){0,3})\s*$",
    re.IGNORECASE)
def _has_gate_mechanism(body: str) -> bool:
    for match in _GATE_SIGNAL_RE.finditer(body):
        prefix = body[max(0, match.start() - 24):match.start()]
        if (_GATE_ABSENCE_PREFIX_RE.search(prefix)
                or _GATE_NEGATED_OPERATION_PREFIX_RE.search(prefix)):
            continue
        return True
    return False
def _build_match_context(body: str, frontmatter: dict, snap: dict,
                         skill_name: str) -> dict:
    step_pattern = list(dict.fromkeys(
        re.findall(r"(?:step|步骤|phase|阶段)\s*(\d+)", body)))
    has_gate = _has_gate_mechanism(body)
    has_severity_levels = bool(re.search(r"(?:(?:\b|(?<=_))severity|严重)", body))
    has_scoring_mechanism = bool(re.search(
        r"(?:\bscor(?:e|es|ed|ing|ings)\b|\brat(?:e|es|ed|ing|ings)\b|评分|评级)", body))
    return {
        "frontmatter": frontmatter,
        "skill_name": skill_name,
        "step_pattern": step_pattern,
        "has_gate": has_gate,
        "has_severity_levels": has_severity_levels,
        "has_scoring_mechanism": has_scoring_mechanism,
        **snap,
    }
def _score_patterns(body: str, frontmatter: dict, snap: dict, skill_name: str) -> list[PatternMatchSpec]:
    ctx = _build_match_context(body, frontmatter, snap, skill_name)
    matches = []
    for pattern_name, pattern_def in _pattern_table().items():
        result = _build_matcher_args(pattern_name, pattern_def, body, ctx)
        if result is None:
            continue
        score, evidence = result
        if score >= _DETECT_MIN_CONFIDENCE:
            matches.append(PatternMatchSpec(
                pattern=pattern_name, confidence=min(score, 1.0),
                evidence=evidence,
                recommendation=pattern_def.get("template") or "",
            ))
    matches.sort(key=lambda m: (-m.confidence, m.pattern))
    return matches
def _antipattern_excluded(ap: str, has_refs: bool, has_assets: bool,
                          has_templates: bool, has_gate: bool) -> bool:
    if ap.startswith("硬编码"):
        return has_refs
    if not ap.startswith("缺少"):
        return False
    requirements = [
        satisfied
        for mentioned, satisfied in (
            ("references/" in ap, has_refs),
            ("assets/" in ap, has_assets),
            ("模板" in ap, has_templates),
            ("门禁机制" in ap, has_gate),
        )
        if mentioned
    ]
    return bool(requirements) and all(requirements)
def _build_antipattern_warnings(matches: list[PatternMatchSpec], snap: dict) -> list[str]:
    warnings = []
    if not matches:
        return warnings
    top = matches[0]
    pattern_def = _pattern_table().get(top.pattern)
    if not isinstance(pattern_def, dict):
        return warnings
    _has_refs = snap.get("has_references", False)
    _has_assets = snap.get("has_assets", False)
    _has_templates = snap.get("has_templates", False)
    _has_gate = snap.get("has_gate", False)
    antipatterns = pattern_def.get("antipatterns")
    if not isinstance(antipatterns, (list, tuple)):
        return warnings
    for ap in antipatterns:
        if not isinstance(ap, str):
            continue
        if _antipattern_excluded(
                ap, _has_refs, _has_assets, _has_templates, _has_gate):
            continue
        warnings.append(f"[{top.pattern}] 潜在反模式: {ap}")
    return warnings
def _missing_skill_analysis(skill_md_path: str, skill_dir: Path,
                           skill_name: str) -> SkillAnalysis:
    _log.warning("SKILL.md 不存在: %s", skill_md_path)
    return SkillAnalysis(
        skill_name=skill_name,
        skill_path=str(skill_dir),
        warnings=[f"SKILL.md 文件不存在: {skill_md_path}"],
    )
def detect_patterns(skill_md_path: str) -> SkillAnalysis:
    normalized = normalize_path_arg(skill_md_path)
    if not isinstance(normalized, str) or not normalized:
        _log.warning("detect_patterns: 路径为空或类型无效, got=%r", skill_md_path)
        return SkillAnalysis(
            skill_name="unknown",
            skill_path="",
            warnings=[f"SKILL.md 路径无效: {skill_md_path!r}"],
        )
    path = Path(normalized)
    skill_dir = path.parent
    skill_name = skill_dir.name or "unknown"
    if not path.is_file():
        return _missing_skill_analysis(normalized, skill_dir, skill_name)
    try:
        content = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        _log.exception("读取 SKILL.md 失败: %s", normalized)
        raise
    content = _normalize_md_text(content)
    frontmatter = _parse_skill_frontmatter(content)
    declared_name, description, keywords, body_start = (
        extract_frontmatter_fields(content))
    skill_name = declared_name or skill_name
    body_text = content if body_start is None else content[body_start:]
    semantic_text = "\n".join([description, *keywords, body_text])
    body = strip_fenced_blocks(semantic_text).lower()
    snap = _snapshot_skill_dir(skill_dir)
    matches = _score_patterns(body, frontmatter, snap, skill_name)
    has_gate = _build_match_context(
        body, frontmatter, snap, skill_name)["has_gate"]
    warnings = _build_antipattern_warnings(
        matches, {**snap, "has_gate": has_gate})
    recommended = matches[0].pattern if matches else None
    return SkillAnalysis(
        skill_name=skill_name,
        skill_path=str(skill_dir),
        detected_patterns=matches,
        recommended_pattern=recommended,
        warnings=warnings,
    )
_REQUIRED_KEYS = frozenset({'signals', 'keywords', 'antipatterns', 'template'})
_MIN_PATTERN_COUNT = 3
_FALLBACK_CONFIDENCE = 0.1
_DEFAULT_PATTERN_KEY = "pipeline"
def _is_numeric_signal_map(signals: Any) -> bool:
    if not isinstance(signals, dict):
        return False
    for weight in signals.values():
        if isinstance(weight, bool) or not isinstance(weight, (int, float)):
            return False
        try:
            numeric = float(weight)
        except (OverflowError, ValueError):
            return False
        if not math.isfinite(numeric) or numeric < 0:
            return False
    return True
def _is_str_list(value: Any) -> bool:
    return isinstance(value, list) and all(isinstance(x, str) for x in value)
def _well_formed(v: Any) -> bool:
    if not (isinstance(v, dict) and set(v) >= _REQUIRED_KEYS):
        return False
    return (
        _is_numeric_signal_map(v.get("signals"))
        and _is_str_list(v.get("keywords"))
        and _is_str_list(v.get("antipatterns"))
        and isinstance(v.get("template"), str)
    )
def _validate_pattern_data(data: Any) -> dict | None:
    if not isinstance(data, dict):
        _log.warning(
            "patterns.yaml 加载结果非 dict 形态（实际 %s），回退内置默认模式",
            type(data).__name__,
        )
        return None
    if len(data) < _MIN_PATTERN_COUNT:
        _log.warning(
            "patterns.yaml 仅含 %d 个模式（需 >=%d 个），回退内置默认模式",
            len(data), _MIN_PATTERN_COUNT,
        )
        return None
    bad_keys = [k for k in data if not isinstance(k, str) or not k.strip()]
    if bad_keys:
        _log.warning(
            "patterns.yaml 模式名非法（需非空字符串）: %r，回退内置默认模式",
            bad_keys,
        )
        return None
    bad = [k for k, v in data.items() if not _well_formed(v)]
    if bad:
        _log.warning(
            "patterns.yaml 结构校验失败（模式 %s 缺少必需键或类型不符），回退内置默认模式",
            bad,
        )
        return None
    return data
def _load_patterns() -> Any:
    config_path = Path(__file__).resolve().parent / 'references' / 'patterns.yaml'
    if yaml is None:
        _log.warning(
            "PyYAML 未安装，patterns.yaml 加载跳过，回退内置默认模式"
            "（补装：python -m %s deps --install）", _PACKAGE_NAME)
        return _DEFAULT_PATTERNS
    if not config_path.exists():
        return _DEFAULT_PATTERNS
    try:
        with open(config_path, encoding='utf-8') as f:
            data = yaml.safe_load(f)
    except (OSError, UnicodeDecodeError, yaml.YAMLError, RecursionError):
        _log.warning("patterns.yaml 加载失败，回退内置默认模式", exc_info=True)
        return _DEFAULT_PATTERNS
    validated = _validate_pattern_data(data)
    return validated if validated is not None else _DEFAULT_PATTERNS
_DEFAULT_PATTERNS = {
    "Tool Wrapper": {
        "description": "封装外部工具/API,提供标准化接口。动态加载 references/ 中的规范文档。",
        "keywords": ["api", "tool", "wrapper", "封装", "接口", "调用", "sdk", "client", "browser", "http", "request"],
        "signals": {
            "has_references": 0.3,
            "api_keywords": 0.25,
            "external_dependency": 0.25,
            "tool_like_name": 0.2,
        },
        "antipatterns": ["硬编码 API 规范在 SKILL.md 中", "缺少 references/ 目录"],
        "template": "references/conventions.md 存放规范文档,SKILL.md 中 Load 'references/...' 按需加载",
        "example": "browser, wps-docs, kdocs, stock-analysis",
    },
    "Generator": {
        "description": "根据参数自动生成产出物。基于 assets/ 模板 + references/ 风格指南强制统一输出。",
        "keywords": ["生成", "创建", "产出", "generate", "create", "build", "模板", "template", "输出", "output", "format"],
        "signals": {
            "has_assets": 0.3,
            "has_references": 0.2,
            "generate_keywords": 0.3,
            "output_format_specified": 0.2,
        },
        "antipatterns": ["输出格式不统一", "缺少模板文件", "风格指南与模板分离不清晰"],
        "template": "assets/ 存放输出模板,references/ 存放风格指南,SKILL.md 中 Step 1-5 填空式生成",
        "example": "docx, pptx, xlsx, pdf, paper-writer",
    },
    "Reviewer": {
        "description": "对内容进行质量检查/合规审查。what(检查清单)与 how(审查逻辑)分离。",
        "keywords": ["审查", "检查", "诊断", "review", "diag", "check", "lint", "质量", "quality", "规范", "合规"],
        "signals": {
            "has_checklist": 0.35,
            "review_keywords": 0.3,
            "severity_levels": 0.2,
            "scoring_mechanism": 0.15,
        },
        "antipatterns": ["检查规则硬编码在 system prompt 中", "what 和 how 未分离"],
        "template": "references/review-checklist.md 存放检查清单,SKILL.md 中逐项加载评分,输出 Summary→Findings→Score→Top 3",
        "example": "CIE 反模式扫描, build_preflight, code-reviewer",
    },
    "Inversion": {
        "description": "Agent 主动向用户提问收集需求,而非立即生成。门禁机制防止过早构建。",
        "keywords": ["提问", "收集", "需求", "规划", "设计", "question", "ask", "interview", "requirement", "plan", "discovery"],
        "signals": {
            "multi_turn": 0.3,
            "question_phases": 0.3,
            "gate_mechanism": 0.25,
            "planning_keywords": 0.15,
        },
        "antipatterns": ["Agent 立即开始生成而非先收集需求", "缺少门禁机制", "一次性问太多问题"],
        "template": "分阶段提问(Problem Discovery→Technical Constraints→Synthesis),每阶段有门禁,一次只问一个问题",
        "example": "project-planner, timer_task(定时触发类)",
    },
    "Pipeline": {
        "description": "严格按顺序执行工作流。每步有门禁条件,防止跳步或忽略中间验证。",
        "keywords": ["流水线", "步骤", "阶段", "pipeline", "step", "stage", "顺序", "sequence", "workflow", "流程"],
        "signals": {
            "sequential_steps": 0.35,
            "gate_per_step": 0.3,
            "verification_points": 0.2,
            "pipeline_keywords": 0.15,
        },
        "antipatterns": ["步骤间无验证", "Agent 跳步或忽略中间步骤", "门禁条件不明确"],
        "template": "每步独立验证函数 + 步骤间显式确认点 + 失败阻断后续步骤",
        "example": "pipeline_steps_phases(16 相位管线), run_pipeline_batch(批量推进)",
    },
    "Adapter": {
        "description": "在不同格式/协议间转换。适配输入输出差异，使不兼容接口协同工作。",
        "keywords": ["转换", "适配", "adapter", "convert", "transform", "格式", "format", "迁移", "migrate", "协议", "protocol"],
        "signals": {
            "multi_format": 0.3,
            "convert_keywords": 0.3,
            "input_output_mismatch": 0.2,
            "format_keywords": 0.2,
        },
        "antipatterns": ["硬编码格式转换逻辑", "缺少格式验证"],
        "template": "输入格式检测→适配器选择→格式转换→输出验证",
        "example": "pdf(格式转换), 文件格式适配器",
    },
    "Strategy": {
        "description": "根据条件选择不同算法/策略执行。策略可插拔，运行时动态选择。",
        "keywords": ["策略", "选择", "strategy", "algorithm", "算法", "条件", "分支", "switch", "dispatch", "路由"],
        "signals": {
            "multiple_strategies": 0.3,
            "strategy_keywords": 0.3,
            "conditional_dispatch": 0.2,
            "plugin_like": 0.2,
        },
        "antipatterns": ["策略硬编码在条件语句中", "缺少策略注册机制"],
        "template": "策略注册表 + 条件匹配 + 策略执行 + 结果聚合",
        "example": "treatment_plan(治疗策略), build_preflight(技能类型推断)",
    },
    "Router": {
        "description": "将请求路由到不同处理器。基于意图/关键词/语义匹配分发到目标模块。",
        "keywords": ["路由", "分发", "router", "route", "dispatch", "匹配", "match", "触发", "trigger", "入口", "entry"],
        "signals": {
            "multi_entry": 0.3,
            "router_keywords": 0.3,
            "intent_matching": 0.2,
            "dispatch_table": 0.2,
        },
        "antipatterns": ["路由规则硬编码", "缺少回退路由"],
        "template": "意图检测→路由表匹配→分发到处理器→结果聚合",
        "example": "pipeline_trigger_route(文本触发路由), diag_method_invoke(方法级分派)",
    },
    "Command": {
        "description": "将操作封装为命令对象。支持撤销、重做、队列化和日志记录。",
        "keywords": ["命令", "操作", "command", "action", "执行", "execute", "撤销", "undo", "队列", "queue", "任务", "task"],
        "signals": {
            "command_keywords": 0.3,
            "undo_support": 0.25,
            "queue_mechanism": 0.25,
            "action_logging": 0.2,
        },
        "antipatterns": ["操作不可撤销", "缺少操作日志"],
        "template": "命令封装→队列管理→执行→日志记录→可选撤销",
        "example": "timer_task(定时任务), treatment_plan(治疗计划)",
    },
    "Facade": {
        "description": "为复杂子系统提供简化接口。隐藏内部复杂性，暴露统一入口。",
        "keywords": ["简化", "统一", "facade", "入口", "一站式", "封装", "简化接口", "hide", "complex", "子系统"],
        "signals": {
            "simplified_api": 0.3,
            "facade_keywords": 0.25,
            "multi_subsystem": 0.25,
            "single_entry": 0.2,
        },
        "antipatterns": ["Facade 过于庞大", "泄露子系统细节"],
        "template": "统一入口函数→内部委托给子系统→结果聚合返回",
        "example": "run_full_analysis(全量分析), quick_cleanup(一键清理)",
    },
}
PATTERNS: dict[str, dict[str, Any]] = _load_patterns()
def _pattern_table() -> dict:
    return PATTERNS if isinstance(PATTERNS, dict) else {}
def _copy_definition(definition: dict) -> dict:
    copied = dict(definition)
    for key in ('signals', 'keywords', 'antipatterns'):
        value = copied.get(key)
        if isinstance(value, dict):
            copied[key] = dict(value)
        elif isinstance(value, list):
            copied[key] = list(value)
    return copied
def _keyword_confidence(pattern_def: dict, body: str) -> float:
    keywords = pattern_def.get('keywords') or []
    if isinstance(keywords, str):
        items = [keywords]
    elif isinstance(keywords, Iterable):
        items = list(keywords)
    else:
        items = []
    return min(count_keyword_hits(body, items) / max(len(items), 1), 1.0)
def _fallback_recommendation(pattern_table: dict) -> list[tuple[str, float]]:
    for name in pattern_table:
        if isinstance(name, str) and _pattern_key(name) == _DEFAULT_PATTERN_KEY:
            return [(name, _FALLBACK_CONFIDENCE)]
    fallback = next(iter(pattern_table), None)
    return [(fallback, _FALLBACK_CONFIDENCE)] if fallback is not None else []
def recommend_pattern(description: str, skill_name: str = "") -> list[tuple[str, float]]:
    body = (normalize_str(description) + " " + normalize_str(skill_name)).lower()
    pattern_table = _pattern_table()
    results = _keyword_ranked(pattern_table, body)
    return results or _fallback_recommendation(pattern_table)
def _keyword_ranked(pattern_table: dict, body: str) -> list[tuple[str, float]]:
    results = []
    for pattern_name, pattern_def in pattern_table.items():
        if not isinstance(pattern_def, dict):
            continue
        confidence = _keyword_confidence(pattern_def, body)
        if confidence > 0:
            results.append((pattern_name, round(confidence, 2)))
    results.sort(key=lambda x: (-x[1], x[0]))
    return results
def get(pattern_name: str) -> dict | None:
    if not isinstance(pattern_name, str):
        _log.warning('get 非字符串模式名: %r，返回 None', pattern_name)
        return None
    definition = _pattern_table().get(pattern_name)
    if not isinstance(definition, dict):
        definition = _pattern_definition(pattern_name)
    return (_copy_definition(definition)
            if isinstance(definition, dict) else None)
def list_all_patterns() -> list[dict]:
    return [{**_copy_definition(v), 'name': k}
            for k, v in _pattern_table().items() if isinstance(v, dict)]
def _pattern_key(pattern_title: str) -> str:
    return pattern_title.strip().lower().replace(" ", "_").replace("-", "_")
_MATCHER_SPECS_BY_KEY = {_pattern_key(name): spec
                         for name, spec in _MATCHER_SPECS.items()}
def _pattern_keyword_map(pattern_table: dict) -> dict[str, list[str]]:
    return {
        _pattern_key(title): list(definition.get("keywords") or ())
        for title, definition in pattern_table.items()
        if isinstance(title, str) and isinstance(definition, dict)
    }
PATTERN_KEYWORDS = _pattern_keyword_map(PATTERNS)
PATTERN_HINTS = {
    "generator": "适合按模板生成结构化产出物",
    "inversion": "适合需要多轮确认的交互式任务",
    "tool_wrapper": "适合为现有工具添加文档规范",
    "reviewer": "适合检查和诊断已有产出物",
    "pipeline": "适合多步骤顺序执行的工作流",
    "adapter": "适合在多种格式/系统间转换适配",
    "strategy": "适合按条件切换多种算法或策略",
    "router": "适合按意图分发到不同处理模块",
    "command": "适合需要撤销/队列化/日志记录的操作封装",
    "facade": "适合为复杂子系统提供统一简化入口",
}
_PATTERN_HINT_FALLBACK = "按模式自身定义执行"
def _pattern_definition(pattern: str) -> dict | None:
    wanted = _pattern_key(pattern)
    for title, definition in _pattern_table().items():
        if isinstance(title, str) and (_pattern_key(title) == wanted
                                       or title.strip() == pattern.strip()):
            return definition if isinstance(definition, dict) else None
    return None
def get_pattern_hint(pattern: str) -> str:
    if not isinstance(pattern, str) or not pattern.strip():
        if not isinstance(pattern, str):
            _log.warning("get_pattern_hint 非字符串模式名: %r，使用中性提示", pattern)
        return _PATTERN_HINT_FALLBACK
    key = pattern if pattern in PATTERN_HINTS else _pattern_key(pattern)
    hint = PATTERN_HINTS.get(key)
    if hint:
        return hint
    definition = _pattern_definition(pattern)
    description = (definition or {}).get("description")
    if isinstance(description, str) and description.strip():
        return description.strip()
    return _PATTERN_HINT_FALLBACK
def _pattern_has_keyword_evidence(pattern_title: str, body: str) -> bool:
    definition = _pattern_table().get(pattern_title)
    keywords = definition.get("keywords") if isinstance(definition, dict) else None
    return count_keyword_hits(body, keywords or ()) > 0
def _recommended_pattern(body: str) -> str | None:
    for pattern_title, _confidence in recommend_pattern(body):
        mapped = _pattern_key(pattern_title)
        if not _pattern_has_keyword_evidence(pattern_title, body):
            continue
        return mapped
    return None
def infer_design_pattern(name: str, description: str = "",
                         content: str = "") -> str:
    text = (normalize_text(name) + " " + normalize_text(description) + " "
            + normalize_text(content)).lower()
    mapped = _recommended_pattern(text)
    if mapped:
        return mapped
    fallback = _fallback_recommendation(_pattern_table())
    return (_pattern_key(fallback[0][0]) if fallback
            else _DEFAULT_PATTERN_KEY)
def _is_searchable_dir(dir_path) -> bool:
    return isinstance(dir_path, str) and bool(dir_path) and os.path.isdir(dir_path)
def _unique_skill_key(results: dict[str, DocQualityReport], name: str) -> str:
    if name not in results:
        return name
    idx = 2
    while f"{name}#{idx}" in results:
        idx += 1
    key = f"{name}#{idx}"
    _log.warning("batch_diag_skill_docs: 技能名重复 %s, 保留为 %s 避免静默覆盖",
                   name, key)
    return key
def _diag_one_file(diagnoser, md_path: str) -> DocQualityReport | None:
    try:
        ensure_entry_warmed(
            _skill_dir_of(md_path),
            None, "批量文档诊断 batch_diag_skill_docs")
    except Exception as e:  # noqa: BLE001
        _log.warning("缓存预热失败 %s: %s", md_path, str(e)[:80])
    try:
        return diagnoser.diag(md_path)
    except Exception as e:  # noqa: BLE001
        _log.warning("诊断失败 %s: %s", md_path, str(e)[:80])
        return _uv000_report(
            md_path,
            f"诊断执行异常: {type(e).__name__}: {str(e)[:120]}",
            "排查该文件或诊断环境后重试")
_DEFAULT_BATCH_PATTERN = "SKILL.md"
def batch_diag_skill_docs(
        dir_path: str, pattern: str = _DEFAULT_BATCH_PATTERN,
) -> dict[str, DocQualityReport]:
    dir_path = normalize_path_arg(dir_path)
    pattern = (pattern.strip() if isinstance(pattern, str) and pattern.strip()
               else _DEFAULT_BATCH_PATTERN)
    if not _is_searchable_dir(dir_path):
        _log.warning("batch_diag_skill_docs: dir_path 为空、类型无效或不存在, got=%r",
                       dir_path)
        return {}
    results: dict[str, DocQualityReport] = {}
    diagnoser = get_doc_diagnoser()
    for md_path in iter_matching_files(dir_path, pattern):
        report = _diag_one_file(diagnoser, md_path)
        if report is not None:
            results[_unique_skill_key(results, report.skill_name)] = report
    return results

from __future__ import annotations

import ast
import hashlib
import io
import logging
import os
import re
import tokenize
from collections.abc import Callable, Iterator
from dataclasses import dataclass, field
from datetime import UTC, datetime
from itertools import combinations
from pathlib import Path
from typing import Any, Self

from jwsgj.build_module_topology import loading_chain_diag
from jwsgj.build_text_document import (
    count_words_cn_aware,
    read_skill_text,
)
from jwsgj.build_text_frontmatter import (
    extract_description,
    is_field_key_line,
    load_frontmatter,
    locate_frontmatter_body_start,
    parse_frontmatter,
)
from jwsgj.diag_shared_source_core import (
    iter_file_trees,
    read_source,
)
from jwsgj.diag_shared_source_scan import (
    split_lines_lf,
    string_token_row_spans,
)
from jwsgj.diag_testing_test_index import (
    iter_collectable_test_functions,
)
from jwsgj.diag_types_normalize import (
    finite_float_or_none,
)
from jwsgj.diag_types_vocab import (
    DESC_MAX,
)
from jwsgj.log_config import (
    log_swallowed,
)
from jwsgj.runtime_scope import (
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    SCAN_COLLECT_PRUNE_DIRS_LOWER,
    TEST_DIR_CANDIDATES,
    is_backup_like_dir,
    is_pruned_scan_dir,
    is_scan_py_name,
    is_temp_artifact_dir,
    is_test_file_path,
    rglob_paths_tolerant,
)
from jwsgj.skill_audit_rules import (
    DOC_ROLE_MANIFEST,
    DOC_ROLE_NONE,
    DOC_ROLE_README,
    DOC_ROLE_SKILL,
    TargetDocument,
    count_dangerous_call_risks,
    iter_markdown_lines,
    resolve_target_document,
)

__all__ = [
    'DESC_CRITICAL',
    'DESC_WARN',
    'UNUSED_DAYS_THRESHOLD',
    'DuplicateGroup',
    'FiveDimensionHealth',
    'SkillAttribution',
    'TodoDiagnoseReport',
    'TodoItem',
    'TokenBudget',
    'detect_duplicates',
    'detect_unused_skills',
    'determine_budget_status',
    'diag_todos',
    'diag_token_budget',
    'find_token_budget',
    'format_five_dimension_report',
    'is_skipped_dir_name',
    'matching_duplicate_groups',
    'matching_unused_skill',
    'normalize_skill_path',
    'resolve_skill_attribution',
    'run_five_dimension_health',
    'run_five_dimension_health_batch',
    'skill_md_desc_line',
    'walk_skill_mds',
]
_log = logging.getLogger(__name__)
_DEFAULT_TOKEN_BUDGET: int = 5000
_DEFAULT_SIMILARITY_THRESHOLD: float = 0.6
UNUSED_DAYS_THRESHOLD: float = 90.0
_HEALTHY_MIN_SCORE: float = 80.0
_WARNING_MIN_SCORE: float = 60.0
_DIAGNOSTIC_ERROR_SCORE: float = 0.0
_HIGH_COMPLEXITY_THRESHOLD: int = 15
_STMT_DESCEND_NODES: tuple = (ast.stmt, ast.ExceptHandler, ast.match_case)
_TRY_STAR_NODE = getattr(ast, "TryStar", None)
_BRANCH_NODES: tuple = tuple(
    node for node in (ast.If, ast.For, ast.AsyncFor, ast.While, ast.Try,
                      _TRY_STAR_NODE, ast.With, ast.AsyncWith,
                      ast.match_case)
    if node is not None)
_DESC_WORD_TIERS: tuple[tuple[int, str, str], ...] = (
    (90, "critical", "描述过长（>90词），严重影响触发精准度，建议精简到40词以内"),
    (60, "warn", "描述较长（>60词），建议精简到40词以内提高触发率"),
    (40, "info", "描述略长（>40词），可选精简"),
)
_RECOMMENDATION_RULES: tuple[tuple[str, str, str, str, int], ...] = (
    ("security_score", "security_issues", "安全", "建议立即修复安全风险", 3),
    ("architecture_score", "architecture_issues", "架构", "建议重构模块结构", 3),
    ("code_quality_score", "code_quality_issues", "代码", "建议改善代码质量", 3),
    ("test_quality_score", "test_quality_issues", "测试", "建议补充测试用例", 3),
    ("documentation_score", "documentation_issues", "文档", "建议完善文档", 3),
    ("token_budget_score", "token_budget_issues", "Token预算", "", 2),
    ("loading_chain_score", "loading_chain_issues", "加载链路", "", 2),
    ("duplicate_score", "duplicate_issues", "重复", "建议处理同名或高相似技能", 3),
    ("idle_score", "idle_issues", "闲置", "建议确认技能是否仍在维护", 3),
    ("description_score", "description_issues", "描述", "", 3),
)
_DIMENSION_PREFIXES: tuple[str, ...] = (
    "code_quality", "test_quality", "architecture", "security",
    "documentation", "token_budget", "duplicate", "idle",
    "loading_chain", "description",
)
_PRIMARY_SCORE_FIELDS: tuple[str, ...] = tuple(
    f"{prefix}_score" for prefix in _DIMENSION_PREFIXES[:5])
_DOC_REQUIRED_SECTIONS: dict[str, tuple[str, ...]] = {
    "description": ("description", "描述"),
    "triggers": ("trigger", "触发", "使用场景"),
    "instructions": ("instruction", "步骤", "使用方式", "快速入门", "用法"),
    "gotchas": ("gotcha", "注意", "陷阱", "警告"),
}
_GENERIC_HEALTH_SKIP_DIRS = GENERIC_SCAN_IGNORE_DIRS_LOWER | {"baselines"}
_SKILL_SCAN_SKIP_DIRS = SCAN_COLLECT_PRUNE_DIRS_LOWER | {"baselines"}
def _health_scan_skip_dirs(root_dir: Any) -> frozenset[str]:
    try:
        has_skill_md = os.path.isfile(
            os.path.join(os.fspath(root_dir), "SKILL.md"))
    except (TypeError, ValueError, OSError):
        has_skill_md = False
    return _SKILL_SCAN_SKIP_DIRS if has_skill_md else _GENERIC_HEALTH_SKIP_DIRS
@dataclass
class FiveDimensionHealth:
    skill_name: str
    skill_path: str
    timestamp: str = field(default_factory=lambda: datetime.now(UTC).isoformat())
    token_budget_score: float = 100.0
    token_budget_detail: dict[str, Any] = field(default_factory=dict)
    token_budget_issues: list[str] = field(default_factory=list)
    duplicate_score: float = 100.0
    duplicate_detail: dict[str, Any] = field(default_factory=dict)
    duplicate_issues: list[str] = field(default_factory=list)
    idle_score: float = 100.0
    idle_detail: dict[str, Any] = field(default_factory=dict)
    idle_issues: list[str] = field(default_factory=list)
    loading_chain_score: float = 100.0
    loading_chain_detail: dict[str, Any] = field(default_factory=dict)
    loading_chain_issues: list[str] = field(default_factory=list)
    description_score: float = 100.0
    description_detail: dict[str, Any] = field(default_factory=dict)
    description_issues: list[str] = field(default_factory=list)
    code_quality_score: float = 100.0
    code_quality_detail: dict[str, Any] = field(default_factory=dict)
    code_quality_issues: list[str] = field(default_factory=list)
    test_quality_score: float = 100.0
    test_quality_detail: dict[str, Any] = field(default_factory=dict)
    test_quality_issues: list[str] = field(default_factory=list)
    architecture_score: float = 100.0
    architecture_detail: dict[str, Any] = field(default_factory=dict)
    architecture_issues: list[str] = field(default_factory=list)
    security_score: float = 100.0
    security_detail: dict[str, Any] = field(default_factory=dict)
    security_issues: list[str] = field(default_factory=list)
    documentation_score: float = 100.0
    documentation_detail: dict[str, Any] = field(default_factory=dict)
    documentation_issues: list[str] = field(default_factory=list)
    overall_score: float = 0.0
    health_status: str = "healthy"
    recommendations: list[str] = field(default_factory=list)
    def compute_overall(self: Self) -> None:
        primary_scores = [getattr(self, name) for name in _PRIMARY_SCORE_FIELDS]
        if not primary_scores:
            self.overall_score = 0.0
            self.health_status = "critical"
            return
        self.overall_score = round(sum(primary_scores) / len(primary_scores), 1)
        if self.overall_score >= _HEALTHY_MIN_SCORE:
            self.health_status = "healthy"
        elif self.overall_score >= _WARNING_MIN_SCORE:
            self.health_status = "warning"
        else:
            self.health_status = "critical"
        if self.health_status == "healthy":
            incomplete = any(
                getattr(self, f"{score_field[:-6]}_detail").get("status")
                in {"partial", "error"}
                for score_field in _PRIMARY_SCORE_FIELDS
            )
            weak_primary = any(
                score < _HEALTHY_MIN_SCORE for score in primary_scores)
            if incomplete or weak_primary:
                self.health_status = "warning"
def _apply_dimension(health: FiveDimensionHealth, prefix: str,
                     result: tuple[float, dict[str, Any], list[str]]) -> dict[str, Any]:
    score, detail, issues = result
    setattr(health, f"{prefix}_score", score)
    setattr(health, f"{prefix}_detail", detail)
    setattr(health, f"{prefix}_issues", issues)
    return detail
def _five_dim_description_diag(skill_dir: str) -> dict[str, Any]:
    doc = resolve_target_document(skill_dir)
    result = {"exists": doc.path is not None, "description": "", "word_count": 0,
              "char_count": 0, "status": "ok", "suggestion": "",
              "doc_path": str(doc.path) if doc.path is not None else "",
              "doc_role": doc.doc_role, "target_kind": doc.kind}
    if doc.doc_role == DOC_ROLE_NONE:
        result["status"] = "critical"
        result["suggestion"] = ("SKILL.md 不存在，且未找到 README/pyproject "
                                "等项目说明，无法读取 description；"
                                "技能无法被触发词匹配发现，普通项目也无法被理解")
        return result
    if doc.read_failed:
        _log.warning("[Health] description_diag 读取失败: %s", doc.path)
        result["status"] = "warn"
        result["suggestion"] = f"{doc.path.name} 读取失败，描述精简诊断降级"
        return result
    try:
        description = doc.description
    except Exception as e:  # noqa: BLE001
        _log.debug("[Health] 描述提取失败，降级空描述: %s", e, exc_info=True)
        description = ""
    if not description:
        result["status"] = "critical"
        if doc.doc_role == DOC_ROLE_SKILL:
            result["suggestion"] = ("SKILL.md 描述为空（frontmatter 缺少 "
                                    "description 键或值为空），技能无法被触发"
                                    "词匹配发现，必须补齐 description")
        else:
            result["suggestion"] = (f"{doc.path.name if doc.path else '项目文档'}"
                                    " 未声明 description（项目清单 name/"
                                    "description 与 README 首段均为空），"
                                    "无法判断目标用途")
        return result
    result["description"] = description
    result["char_count"] = len(description)
    _wc = count_words_cn_aware(description)
    result["word_count"] = _wc
    result["status"], result["suggestion"] = _desc_word_tier(_wc)
    return result
def _desc_word_tier(word_count: int) -> tuple[str, str]:
    for limit, status, suggestion in _DESC_WORD_TIERS:
        if word_count > limit:
            return status, suggestion
    return "ok", "描述长度合理"
def _has_docstring(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    first = node.body[0] if node.body else None
    return (isinstance(first, ast.Expr)
            and isinstance(first.value, ast.Constant)
            and isinstance(first.value.value, str))
class _CodeQualityScanner:
    def __init__(self) -> None:
        self.total_functions = 0
        self.bare_except_count = 0
        self.no_docstring_count = 0
        self.high_complexity_count = 0
        self.issues: list[str] = []
        self._comp_stack: list[int | None] = []
    def scan_tree(self, node, fpath: str) -> None:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            self._visit_function(node, fpath)
            return
        if isinstance(node, ast.ClassDef):
            self._comp_stack.append(None)
            self._descend(node, fpath)
            self._comp_stack.pop()
            return
        if isinstance(node, ast.ExceptHandler) and node.type is None:
            self.bare_except_count += 1
        elif (isinstance(node, _BRANCH_NODES) and self._comp_stack
              and self._comp_stack[-1] is not None):
            self._comp_stack[-1] += 1
        self._descend(node, fpath)
    def _descend(self, node, fpath: str) -> None:
        for child in ast.iter_child_nodes(node):
            if isinstance(child, _STMT_DESCEND_NODES):
                self.scan_tree(child, fpath)
    def _visit_function(self, node, fpath: str) -> None:
        self.total_functions += 1
        if not _has_docstring(node):
            self.no_docstring_count += 1
        self._comp_stack.append(0)
        self._descend(node, fpath)
        comp = self._comp_stack.pop()
        if comp > _HIGH_COMPLEXITY_THRESHOLD:
            self.high_complexity_count += 1
            self.issues.append(
                f"高复杂度函数: {node.name} @ {os.path.basename(fpath)}"
                f" (复杂度={comp})")
def _is_test_file_under(path: str, scan_root: str) -> bool:
    # 测试归属必须相对扫描根判定：is_test_file_path 会检查路径的每一段，
    # 若技能根本身位于 tests/fixtures/*_tests 等祖先目录之下，绝对路径会让
    # 全部生产源码被误判为测试文件（代码质量/安全维度扫描 0 文件却得满分）。
    try:
        relative = os.path.relpath(path, scan_root)
    except ValueError:  # Windows 跨盘符等无法相对化时回退绝对路径口径
        return is_test_file_path(path)
    return is_test_file_path(relative)
def _iter_project_py_files(skill_dir: str, *, include_tests: bool) -> Iterator[str]:
    if not str(skill_dir or "").strip():
        return
    skip_dirs = _health_scan_skip_dirs(skill_dir)
    for root, dirs, files in os.walk(skill_dir):
        dirs[:] = sorted(
            name for name in dirs
            if not is_pruned_scan_dir(name, skip_dirs))
        for fname in sorted(files):
            if not is_scan_py_name(fname):
                continue
            path = os.path.join(root, fname)
            if not include_tests and _is_test_file_under(path, skill_dir):
                continue
            yield path
def _record_parse_coverage(detail: dict[str, Any], total: int,
                           parsed: int) -> None:
    unparsed = max(0, total - parsed)
    detail["unparsed_files"] = unparsed
    detail["scan_coverage"] = round(parsed / total, 4) if total else 1.0
    detail["status"] = (
        "error" if total and not parsed
        else "partial" if unparsed
        else "ok"
    )
def _coverage_adjusted_score(score: float, total: int, parsed: int) -> float:
    if not total:
        return score
    return round(score * (parsed / total), 1)
def _check_code_quality(skill_dir: str, ctx=None) -> tuple[float, dict[str, Any], list[str]]:
    py_files = list(_iter_project_py_files(skill_dir, include_tests=False))
    detail: dict[str, Any] = {"files_scanned": len(py_files),
                              "total_functions": 0, "issues_found": 0}
    scanner = _CodeQualityScanner()
    parsed = 0
    for fpath, tree in iter_file_trees(py_files, ctx):
        parsed += 1
        scanner.scan_tree(tree, fpath)
    detail["parsed_files"] = parsed
    _record_parse_coverage(detail, len(py_files), parsed)
    detail["total_functions"] = scanner.total_functions
    detail["bare_except_count"] = scanner.bare_except_count
    detail["no_docstring_count"] = scanner.no_docstring_count
    detail["high_complexity_count"] = scanner.high_complexity_count
    detail["issues_found"] = (scanner.bare_except_count + scanner.no_docstring_count
                             + scanner.high_complexity_count)
    issues = scanner.issues
    unparsed = len(py_files) - parsed
    if unparsed > 0:
        issues.append(f"{unparsed} 个 .py 文件无法读取或解析，"
                      f"代码质量结论仅覆盖 {parsed}/{len(py_files)} 个文件")
    if scanner.bare_except_count > 0:
        issues.append(f"发现 {scanner.bare_except_count} 处 bare except")
    if scanner.no_docstring_count > 0 and scanner.total_functions > 0:
        ratio = scanner.no_docstring_count / max(scanner.total_functions, 1)
        if ratio > 0.5:
            issues.append(f"{scanner.no_docstring_count}/{scanner.total_functions} "
                          f"个函数缺少 docstring ({ratio:.0%})")
    _n = max(scanner.total_functions, 1)
    score = max(0.0, 100.0 - scanner.bare_except_count * 5
                - min(40.0, (scanner.high_complexity_count / _n) * 200.0)
                - min(40.0, (scanner.no_docstring_count / _n) * 100.0))
    return _coverage_adjusted_score(score, len(py_files), parsed), detail, issues
def _check_test_quality(skill_dir: str, ctx=None) -> tuple[float, dict[str, Any], list[str]]:
    issues: list[str] = []
    detail: dict[str, Any] = {"test_files": 0, "test_functions": 0,
                              "has_tests_dir": False}
    test_files = _iter_test_py_files(skill_dir)
    detail["has_tests_dir"] = _has_test_directory(skill_dir)
    detail["test_files"] = len(test_files)
    parsed = 0
    test_functions = 0
    for _fpath, tree in iter_file_trees(test_files, ctx):
        parsed += 1
        test_functions += sum(
            1 for _node in iter_collectable_test_functions(tree))
    detail["parsed_test_files"] = parsed
    detail["test_functions"] = test_functions
    _record_parse_coverage(detail, len(test_files), parsed)
    unparsed = len(test_files) - parsed
    if unparsed:
        issues.append(f"{unparsed} 个测试文件无法读取或解析，"
                      f"测试质量仅覆盖 {parsed}/{len(test_files)} 个文件")
    if not test_files:
        score = 20.0
        issues.append("未找到测试文件")
    elif not parsed:
        score = _DIAGNOSTIC_ERROR_SCORE
    else:
        if test_functions == 0:
            score = 40.0
            issues.append("可解析测试文件存在但无测试函数")
        else:
            score = min(100.0, 40.0 + parsed * 10 + test_functions * 2)
        score = _coverage_adjusted_score(score, len(test_files), parsed)
        if score < _HEALTHY_MIN_SCORE:
            issues.append(f"测试覆盖不足: {parsed}/{len(test_files)} 个可解析测试文件/"
                           f"{test_functions} 个测试函数")
    return score, detail, issues
def _iter_test_py_files(skill_dir: str) -> list[str]:
    return [path for path in _iter_project_py_files(
        skill_dir, include_tests=True) if _is_test_file_under(path, skill_dir)]
def _has_test_directory(skill_dir: str) -> bool:
    return any(
        os.path.isdir(os.path.join(skill_dir, dir_name))
        for dir_name in TEST_DIR_CANDIDATES)
def _loading_chain_result(skill_dir: str, ctx=None) -> dict[str, Any]:
    try:
        return loading_chain_diag(skill_dir, ctx)
    except Exception as exc:  # noqa: BLE001
        _log.warning("[Health] 加载链诊断维度失败: %s", exc)
        return {"has_circular": None, "has_dead_import": None,
                "details": [], "status": "error"}
def _check_architecture(skill_dir: str, ctx=None,
                         chain_result: dict[str, Any] | None = None) -> tuple[float, dict[str, Any], list[str]]:
    issues: list[str] = []
    detail: dict[str, Any] = {"total_py_files": 0, "has_references": False,
                              "has_scripts": False, "circular_deps": False}
    has_references = os.path.isdir(os.path.join(skill_dir, "references"))
    has_scripts = os.path.isdir(os.path.join(skill_dir, "scripts"))
    py_count = len(list(_iter_project_py_files(
        skill_dir, include_tests=False)))
    detail["total_py_files"] = py_count
    detail["test_py_files"] = len(_iter_test_py_files(skill_dir))
    detail["has_references"] = has_references
    detail["has_scripts"] = has_scripts
    if chain_result is None:
        chain_result = _loading_chain_result(skill_dir, ctx)
    chain_error = chain_result.get("status") == "error"
    detail["status"] = "error" if chain_error else "ok"
    detail["circular_deps"] = chain_result.get("has_circular")
    detail["dead_imports"] = chain_result.get("has_dead_import")
    if chain_error:
        issues.append("加载链诊断失败，架构依赖状态未知")
        return _DIAGNOSTIC_ERROR_SCORE, detail, issues
    penalties = (
        (chain_result.get("has_circular"), 40.0, "检测到循环依赖"),
        (chain_result.get("has_dead_import"), 15.0, "存在死导入"),
    )
    score = 100.0
    for triggered, penalty, issue in penalties:
        if not triggered:
            continue
        score -= penalty
        issues.append(issue)
    return max(0.0, score), detail, issues
def _check_security(skill_dir: str, ctx=None) -> tuple[float, dict[str, Any], list[str]]:
    issues: list[str] = []
    detail: dict[str, Any] = {"files_scanned": 0, "eval_count": 0, "exec_count": 0,
                              "shell_true_count": 0, "total_risks": 0}
    py_files = list(_iter_project_py_files(skill_dir, include_tests=False))
    detail["files_scanned"] = len(py_files)
    total_risks = 0
    parsed = 0
    for fpath, tree in iter_file_trees(py_files, ctx):
        parsed += 1
        file_eval, file_exec, file_shell = count_dangerous_call_risks(tree)
        if file_eval or file_exec or file_shell:
            detail["eval_count"] += file_eval
            detail["exec_count"] += file_exec
            detail["shell_true_count"] += file_shell
            _n = file_eval + file_exec + file_shell
            total_risks += _n
            issues.append(
                f"{os.path.basename(fpath)}: 发现 {_n} 处危险调用"
                f"(eval={file_eval}, exec={file_exec}, shell={file_shell})")
    detail["total_risks"] = total_risks
    detail["parsed_files"] = parsed
    _record_parse_coverage(detail, len(py_files), parsed)
    unparsed = len(py_files) - parsed
    if unparsed > 0:
        issues.append(f"{unparsed} 个 .py 文件无法读取或解析，"
                      f"安全评估仅覆盖 {parsed}/{len(py_files)} 个文件")
    score = max(0.0, 100.0 - total_risks * 10)
    return _coverage_adjusted_score(score, len(py_files), parsed), detail, issues
def _doc_frontmatter_complete(content: str) -> bool:
    fm_text, _ = parse_frontmatter(content)
    frontmatter, reason, detail = load_frontmatter(fm_text)
    if reason == "parse_error":
        _log.debug("[Health] frontmatter YAML 解析失败，按不完整处理: %s", detail)
    if not isinstance(frontmatter, dict):
        return False
    return all(isinstance(frontmatter.get(key), str) and frontmatter[key].strip()
               for key in ("name", "description"))
def _markdown_heading_texts(content: str) -> list[str]:
    _frontmatter, body = parse_frontmatter(content)
    return [value.lower() for kind, value in iter_markdown_lines(body)
            if kind == "heading"]
def _doc_section_presence(content: str) -> dict[str, bool]:
    headings = _markdown_heading_texts(content)
    presence = {section: any(kw.lower() in heading
                             for heading in headings for kw in keywords)
                for section, keywords in _DOC_REQUIRED_SECTIONS.items()}
    if extract_description(content).strip():
        presence["description"] = True
    return presence
def _manifest_documentation(
        doc: TargetDocument, detail: dict[str, Any],
        issues: list[str]) -> tuple[float, dict[str, Any], list[str]]:
    complete = bool(doc.name) and bool(doc.description)
    detail["frontmatter_complete"] = complete
    if not complete:
        missing = [label for label, value in (
            ("name", doc.name), ("description", doc.description)) if not value]
        issues.append("项目清单缺少 " + "/".join(missing))
        return 70.0, detail, issues
    return 100.0, detail, issues
def _readme_documentation(
        doc: TargetDocument, detail: dict[str, Any],
        issues: list[str]) -> tuple[float, dict[str, Any], list[str]]:
    detail["frontmatter_complete"] = bool(doc.description)
    if not doc.text.strip():
        issues.append(f"{doc.path.name} 内容为空")
        return 0.0, detail, issues
    if not _markdown_heading_texts(doc.text):
        issues.append(f"{doc.path.name} 缺少 Markdown 标题")
        return 70.0, detail, issues
    if not doc.description:
        issues.append(f"{doc.path.name} 缺少可读摘要")
        return 80.0, detail, issues
    return 100.0, detail, issues
def _check_documentation(skill_dir: str) -> tuple[float, dict[str, Any], list[str]]:
    issues: list[str] = []
    detail: dict[str, Any] = {"skill_md_exists": False, "required_sections": {},
                              "frontmatter_complete": False,
                              "doc_role": DOC_ROLE_NONE, "doc_path": ""}
    doc = resolve_target_document(skill_dir)
    detail["doc_role"] = doc.doc_role
    if doc.path is None:
        return 0.0, detail, ["SKILL.md 不存在",
                             "未找到 README/pyproject 等替代项目说明"]
    detail["doc_path"] = str(doc.path)
    detail["skill_md_exists"] = doc.doc_role == DOC_ROLE_SKILL
    if doc.read_failed:
        return 0.0, detail, [f"{doc.path.name} 读取失败"]
    if doc.doc_role == DOC_ROLE_MANIFEST:
        return _manifest_documentation(doc, detail, issues)
    if doc.doc_role == DOC_ROLE_README:
        return _readme_documentation(doc, detail, issues)
    content = doc.text
    frontmatter_complete = _doc_frontmatter_complete(content)
    detail["frontmatter_complete"] = frontmatter_complete
    found_sections = _doc_section_presence(content)
    detail["required_sections"] = found_sections
    missing_sections = [section for section, found in found_sections.items()
                        if not found]
    issues.extend(f"缺少 {section} 章节" for section in missing_sections)
    if not frontmatter_complete:
        issues.append("frontmatter 不完整")
    score = (100.0 - len(missing_sections) * 15.0
             - (0.0 if frontmatter_complete else 30.0))
    return max(0.0, score), detail, issues
def normalize_skill_path(value: Any) -> str:
    try:
        raw = (os.fspath(value)
               if isinstance(value, (os.PathLike, bytes)) else str(value or ""))
        if isinstance(raw, bytes):
            raw = os.fsdecode(raw)
    except TypeError:
        return ""
    if not raw.strip():
        return ""
    try:
        return os.path.normcase(os.path.realpath(os.path.abspath(raw)))
    except (OSError, ValueError):
        return os.path.normcase(os.path.abspath(raw))
def _skill_leaf_name(skill_dir: Any) -> str:
    return Path(normalize_skill_path(skill_dir)).name
def _same_skill_name(left: Any, right: Any) -> bool:
    return os.path.normcase(str(left or "")) == os.path.normcase(
        str(right or ""))
def _shared_scan_or_compute(shared_scans: dict[str, Any] | None, key: str,
                           compute: Callable[[], Any]) -> Any:
    cached = (shared_scans or {}).get(key)
    return compute() if cached is None else cached
def _normalized_budget_limit(value: Any) -> int:
    if isinstance(value, bool):
        return _DEFAULT_TOKEN_BUDGET
    try:
        limit = int(value)
    except (TypeError, ValueError, OverflowError):
        return _DEFAULT_TOKEN_BUDGET
    return limit if limit > 0 else _DEFAULT_TOKEN_BUDGET
def _check_token_budget(sp: Path, skills_root: str | None, budget_limit: int,
                         shared_scans: dict[str, Any] | None) -> tuple[float, dict[str, Any], list[str]]:
    budget_limit = _normalized_budget_limit(budget_limit)
    score = 100.0
    issues: list[str] = []
    detail: dict[str, Any] = {"status": "skipped"}
    try:
        if skills_root:
            table_result = _token_budget_from_table(
                sp, skills_root, shared_scans, budget_limit)
            if table_result is not None:
                score, detail, table_issues = table_result
                issues.extend(table_issues)
    except Exception as _e:  # noqa: BLE001
        _log.warning("[Health] token 预算维度失败: %s", _e)
    if detail.get("status") in (None, "skipped"):
        score, detail, fallback_issues = _token_budget_fallback(sp, budget_limit)
        issues.extend(fallback_issues)
    return score, detail, issues
def _apply_token_budget_limit(
        score: float, detail: dict[str, Any], issues: list[str],
        estimated_tokens: int, budget_limit: int,
) -> tuple[float, dict[str, Any], list[str]]:
    if estimated_tokens <= budget_limit:
        return score, detail, issues
    if detail.get("status") == "ok":
        detail["status"] = "warn"
    issues.append(
        f"Token 估算超标: ~{estimated_tokens} tokens > 预算 {budget_limit}")
    return min(score, 50.0), detail, issues
def find_token_budget(skills_root: str, skill_dir: Any, *,
                      shared_scans: dict[str, Any] | None = None,
                      ) -> TokenBudget | None:
    if not str(skill_dir or "").strip():
        return None
    target = normalize_skill_path(Path(skill_dir) / "SKILL.md")
    budgets = _shared_scan_or_compute(
        shared_scans, "budgets", lambda: diag_token_budget(skills_root))
    matches = [budget for budget in budgets
               if normalize_skill_path(
                   getattr(budget, "skill_path", "")) == target]
    return matches[0] if len(matches) == 1 else None
def _token_budget_from_table(sp: Path, skills_root: str,
                             shared_scans: dict[str, Any] | None,
                             budget_limit: int,
                             ) -> tuple[float, dict[str, Any], list[str]] | None:
    budget = find_token_budget(skills_root, sp, shared_scans=shared_scans)
    if budget is None:
        return None
    detail = {
        "total_chars": budget.total_chars,
        "estimated_tokens": budget.estimated_tokens,
        "description_chars": budget.description_chars,
        "description_status": budget.status,
        "budget_percent": budget.budget_percent,
        "status": "ok",
    }
    return _apply_token_budget_limit(
        100.0, detail, [], budget.estimated_tokens, budget_limit)
def _estimate_token_count(text: str) -> int:
    return max(1, len(text) // 4) if text else 0
def _token_budget_fallback(sp: Path, budget_limit: int) -> tuple[float, dict[str, Any], list[str]]:
    doc = resolve_target_document(sp)
    if doc.path is None:
        return 0.0, {"status": "missing"}, [
            "SKILL.md 不存在", "未找到 README/pyproject 等替代项目说明"]
    if doc.read_failed:
        _log.warning("[Health] %s 读取失败，Token 回退估算降级", doc.path)
        return 0.0, {"status": "error"}, [
            f"{doc.path.name} 读取失败，Token 估算不可用"]
    chars = doc.text
    est = _estimate_token_count(chars)
    return _apply_token_budget_limit(
        100.0,
        {"total_chars": len(chars), "estimated_tokens": est, "status": "ok",
         "doc_role": doc.doc_role},
        [], est, budget_limit)
def _duplicate_issue_text(dup, target: str) -> str:
    other = ", ".join(s for s in dup.skills
                      if not _same_skill_name(s, target))
    if other:
        return f"与 {other} 相似度 {dup.similarity:.2f}"
    return (f"与其他目录下同名技能 {target} 完全同名"
            f"（相似度 {dup.similarity:.2f}）")
@dataclass(frozen=True)
class SkillAttribution:
    in_root: bool
    name_ambiguous: bool
    reason: str = ""
    @property
    def attributable(self) -> bool:
        return self.in_root and not self.name_ambiguous
def resolve_skill_attribution(skills_dir: Any, skill_dir: Any) -> SkillAttribution:
    entries = list(walk_skill_mds(skills_dir))
    target = normalize_skill_path(skill_dir)
    in_root = any(normalize_skill_path(md.parent) == target
                  for _name, md in entries)
    if not in_root:
        return SkillAttribution(in_root=False, name_ambiguous=False,
                                reason="目标不在 skills_root 下")
    leaf = _skill_leaf_name(skill_dir)
    if sum(1 for name, _md in entries
           if _same_skill_name(name, leaf)) > 1:
        return SkillAttribution(in_root=True, name_ambiguous=True,
                                reason="同名嵌套技能无法仅凭叶名归属")
    return SkillAttribution(in_root=True, name_ambiguous=False)
def matching_duplicate_groups(skills_root: str, skill_dir: Any, *,
                              shared_scans: dict[str, Any] | None = None,
                              ) -> list[DuplicateGroup]:
    leaf = _skill_leaf_name(skill_dir)
    groups = _shared_scan_or_compute(
        shared_scans, "duplicates", lambda: detect_duplicates(skills_root))
    return [group for group in groups
            if any(_same_skill_name(leaf, name)
                   for name in getattr(group, "skills", ()))]
def matching_unused_skill(skills_root: str, skill_dir: Any, *,
                          shared_scans: dict[str, Any] | None = None,
                          ) -> str | None:
    leaf = _skill_leaf_name(skill_dir)
    unused = _shared_scan_or_compute(
        shared_scans, "unused", lambda: detect_unused_skills(skills_root))
    return next((name for name in unused
                 if _same_skill_name(name, leaf)), None)
def _duplicate_detail(status: str, total: int = 0,
                      reason: str = "") -> dict[str, Any]:
    detail: dict[str, Any] = {"status": status, "total_duplicates": total}
    if reason:
        detail["reason"] = reason
    return detail
def _check_duplicates(skills_root: str | None, sp: Path,
                      shared_scans: dict[str, Any] | None) -> tuple[float, dict[str, Any], list[str]]:
    score = 100.0
    issues: list[str] = []
    if not skills_root:
        return score, _duplicate_detail("skipped", reason="未提供 skills_root"), issues
    try:
        attribution = resolve_skill_attribution(skills_root, sp)
        if not attribution.attributable:
            return score, _duplicate_detail(
                "skipped", reason=attribution.reason), issues
        skill_dups = matching_duplicate_groups(
            skills_root, sp, shared_scans=shared_scans)
        if skill_dups:
            score = max(40.0, 100 - len(skill_dups) * 20)
            issues.extend(_duplicate_issue_text(dup, _skill_leaf_name(sp))
                           for dup in skill_dups)
        detail = _duplicate_detail("ok", total=len(skill_dups))
    except Exception as _e:  # noqa: BLE001
        _log.warning("[Health] 重复检测维度失败: %s", _e)
        return _DIAGNOSTIC_ERROR_SCORE, _duplicate_detail("error"), [
            "重复检测失败，无法确认相似技能"]
    return score, detail, issues
def _idle_from_root(skills_root: str, sp: Path,
                    shared_scans: dict[str, Any] | None
                    ) -> tuple[float, dict[str, Any], list[str]]:
    try:
        if not resolve_skill_attribution(skills_root, sp).attributable:
            return _idle_from_mtime(sp)
        if matching_unused_skill(
                skills_root, sp, shared_scans=shared_scans) is not None:
            return 50.0, {"status": "idle"}, [
                f"技能超过 {UNUSED_DAYS_THRESHOLD:g} 天未修改（闲置）"]
        return 100.0, {"status": "active"}, []
    except Exception as _e:  # noqa: BLE001
        _log.warning("[Health] 闲置检测维度失败: %s", _e)
        return _DIAGNOSTIC_ERROR_SCORE, {"status": "error"}, [
            "闲置检测失败，无法确认技能活跃状态"]
def _iter_activity_files(sp: Path) -> Iterator[Path]:
    skip_dirs = _health_scan_skip_dirs(sp)
    for root, dirs, files in os.walk(sp):
        dirs[:] = sorted(
            name for name in dirs
            if not is_pruned_scan_dir(name, skip_dirs))
        for file_name in sorted(files):
            stem = os.path.splitext(file_name)[0]
            if (file_name.startswith(".")
                    or is_backup_like_dir(stem)
                    or is_temp_artifact_dir(stem)):
                continue
            yield Path(root) / file_name
def _newest_source_mtime(sp: Path) -> tuple[datetime | None, str]:
    newest: tuple[float, str] | None = None
    try:
        candidates = list(_iter_activity_files(sp))
    except OSError as exc:
        _log.debug("[Health] 闲置检测交付文件枚举失败 %s: %s", sp, exc)
        return None, ""
    for entry in candidates:
        try:
            stamp = entry.stat().st_mtime
        except (OSError, ValueError):
            continue
        if newest is None or stamp > newest[0]:
            newest = (stamp, str(entry))
    if newest is None:
        return None, ""
    try:
        return datetime.fromtimestamp(newest[0], tz=UTC), newest[1]
    except (OSError, OverflowError, ValueError) as exc:
        _log.debug("[Health] 源码 mtime 转换失败 %s: %s", newest[1], exc)
        return None, ""
def _newest_skill_mtime(
        sp: Path, doc_path: Path | None) -> tuple[datetime | None, str]:
    mtime, source = _newest_source_mtime(sp)
    if doc_path is None:
        return mtime, source
    try:
        doc_mtime = datetime.fromtimestamp(doc_path.stat().st_mtime, tz=UTC)
    except (OSError, OverflowError, ValueError) as exc:
        _log.warning("[Health] %s stat 失败，回退其他交付文件 mtime: %s",
                     doc_path.name, exc)
        return mtime, source
    if mtime is None or doc_mtime > mtime:
        return doc_mtime, str(doc_path)
    return mtime, source
def _idle_from_mtime(sp: Path) -> tuple[float, dict[str, Any], list[str]]:
    doc = resolve_target_document(sp)
    mtime, source = _newest_skill_mtime(sp, doc.path)
    if mtime is None:
        if doc.path is not None:
            return _DIAGNOSTIC_ERROR_SCORE, {"status": "error"}, [
                f"{doc.path.name} 与其他交付文件 mtime 均不可读，闲置状态未知"]
        return 100.0, {"status": "missing"}, []
    days_since, is_idle = _mtime_age(mtime, UNUSED_DAYS_THRESHOLD)
    detail = {"status": "active", "days_since_modified": days_since,
              "evidence": os.path.basename(source)}
    if is_idle:
        detail["status"] = "idle"
        return 50.0, detail, [f"目标 {days_since} 天未修改"]
    return 100.0, detail, []
def _check_loading_chain(skill_dir: str, ctx=None) -> tuple[float, dict[str, Any], list[str]]:
    score = 100.0
    issues: list[str] = []
    chain_result = _loading_chain_result(skill_dir, ctx)
    if chain_result.get("status") == "error":
        return _DIAGNOSTIC_ERROR_SCORE, chain_result, [
            "加载链诊断失败，无法确认循环依赖与死导入"]
    if chain_result.get("has_circular"):
        score = 20.0
        issues.append("检测到循环依赖")
    elif chain_result.get("has_dead_import"):
        score = 70.0
        issues.append("存在死导入")
    return score, chain_result, issues
def _check_description(skill_dir: str) -> tuple[float, dict[str, Any], list[str]]:
    score = 100.0
    issues: list[str] = []
    desc_diag = _five_dim_description_diag(skill_dir)
    if desc_diag["status"] == "critical":
        score = 40.0
    elif desc_diag["status"] == "warn":
        score = 70.0
    if desc_diag["status"] != "ok" and desc_diag.get("suggestion"):
        issues.append(desc_diag["suggestion"])
    return score, desc_diag, issues
def _dim_recommendation(tag: str, score: float, issues: list[str],
                        advice: str = "", top: int = 3) -> str:
    _ev = "; ".join(list(issues)[:top]) or "无具体问题清单(见维度明细)"
    _text = f"[{tag}] 评分 {score:.0f}: {_ev}"
    if advice:
        _text += f" — {advice}"
    return _text
def _five_dim_recommendations(health: FiveDimensionHealth) -> list[str]:
    interventions: list[str] = []
    for score_field, issues_field, tag, advice, top in _RECOMMENDATION_RULES:
        score = getattr(health, score_field)
        if score >= _HEALTHY_MIN_SCORE:
            continue
        interventions.append(_dim_recommendation(
            tag, score, getattr(health, issues_field), advice, top=top))
    return interventions
def _dedupe_preserving_order(items: list[str]) -> list[str]:
    seen: set[str] = set()
    unique: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        unique.append(item)
    return unique
def run_five_dimension_health(skill_dir: str, skills_root: str | None = None,
                              budget_limit: int = _DEFAULT_TOKEN_BUDGET,
                              ctx: Any | None = None, *,
                              _shared_scans: dict[str, Any] | None = None) -> FiveDimensionHealth:
    if not str(skill_dir or "").strip():
        issue = "技能目录为空，无法执行五维体检"
        health = FiveDimensionHealth(skill_name="", skill_path="")
        for prefix in _DIMENSION_PREFIXES:
            setattr(health, f"{prefix}_score", _DIAGNOSTIC_ERROR_SCORE)
            getattr(health, f"{prefix}_detail").update(
                status="error", reason=issue)
        health.compute_overall()
        health.recommendations.append(issue)
        return health
    sp = Path(skill_dir)
    health = FiveDimensionHealth(
        skill_name=_skill_leaf_name(sp), skill_path=str(sp))
    _apply_dimension(health, "token_budget", _check_token_budget(
        sp, skills_root, budget_limit, _shared_scans))
    _apply_dimension(health, "duplicate", _check_duplicates(
        skills_root, sp, _shared_scans))
    _apply_dimension(health, "idle", (
        _idle_from_root(skills_root, sp, _shared_scans)
        if skills_root else _idle_from_mtime(sp)))
    _apply_dimension(health, "loading_chain", _check_loading_chain(
        skill_dir, ctx))
    _apply_dimension(health, "description", _check_description(skill_dir))
    _apply_dimension(health, "code_quality", _check_code_quality(skill_dir, ctx))
    _apply_dimension(health, "test_quality", _check_test_quality(skill_dir, ctx))
    _apply_dimension(health, "architecture", _check_architecture(
        skill_dir, ctx, chain_result=health.loading_chain_detail))
    _apply_dimension(health, "security", _check_security(skill_dir, ctx))
    _apply_dimension(health, "documentation", _check_documentation(skill_dir))
    health.compute_overall()
    health.recommendations.extend(_five_dim_recommendations(health))
    if health.overall_score < _HEALTHY_MIN_SCORE:
        health.recommendations = _dedupe_preserving_order([
            *health.recommendations,
            *(issue for prefix in _DIMENSION_PREFIXES
              for issue in getattr(health, f"{prefix}_issues")),
        ])
    _log.info(
        "[Health] 五维体检完成: %s 总分 %.1f 状态 %s",
        health.skill_name, health.overall_score, health.health_status,
        extra={"event": "five_dim_health_done"})
    return health
def _prescan_global_scans(skills_root: str) -> dict[str, Any]:
    shared_scans: dict[str, Any] = {}
    if not Path(skills_root).is_dir():
        return shared_scans
    scans = (
        ("budgets", lambda: diag_token_budget(skills_root)),
        ("duplicates", lambda: detect_duplicates(skills_root)),
        ("unused", lambda: detect_unused_skills(
            skills_root)),
    )
    for key, scan in scans:
        try:
            shared_scans[key] = scan()
        except Exception as _e:  # noqa: BLE001
            _log.warning("[Health] 批量预扫描 %s 失败，回退单技能现场计算: %s",
                         key, _e)
    return shared_scans
def _assess_one_skill(skill_md: Path, skills_root: str, budget_limit: int,
                      shared_scans: dict[str, Any],
                      ctx: Any | None = None) -> FiveDimensionHealth:
    try:
        return run_five_dimension_health(
            str(skill_md.parent), skills_root=skills_root,
            budget_limit=budget_limit, ctx=ctx,
            _shared_scans=shared_scans or None)
    except Exception as _e:  # noqa: BLE001
        _log.warning("[Health] 批量体检单技能失败: %s (%s)", skill_md.parent, _e)
        health = FiveDimensionHealth(
            skill_name=skill_md.parent.name, skill_path=str(skill_md.parent))
        health.overall_score = 0.0
        health.health_status = "error"
        reason = f"五维体检执行失败: {_e}"
        for prefix in _DIMENSION_PREFIXES:
            setattr(health, f"{prefix}_score", _DIAGNOSTIC_ERROR_SCORE)
            getattr(health, f"{prefix}_detail").update(
                status="error", reason=reason)
        health.recommendations.append(reason)
        return health
def run_five_dimension_health_batch(skills_root: str,
                                    budget_limit: int = _DEFAULT_TOKEN_BUDGET,
                                    ctx: Any | None = None
                                    ) -> list[FiveDimensionHealth]:
    if not str(skills_root or "").strip():
        return []
    shared_scans = _prescan_global_scans(skills_root)
    results: list[FiveDimensionHealth] = []
    for _name, skill_md in list(walk_skill_mds(skills_root)):
        results.append(_assess_one_skill(
            skill_md, skills_root, budget_limit, shared_scans, ctx))
    return results
def format_five_dimension_report(health: FiveDimensionHealth) -> str:
    lines = [
        "=" * 60, f"五维体检报告: {health.skill_name}", "=" * 60,
        f"综合评分: {health.overall_score:.1f}/100",
        f"健康状态: {health.health_status.upper()}",
        f"时间: {health.timestamp}", "",
        "主维度评分 (代码/测试/架构/安全/文档):",
        f"  1. 代码质量:   {health.code_quality_score:.1f}",
        f"  2. 测试质量:   {health.test_quality_score:.1f}",
        f"  3. 架构评估:   {health.architecture_score:.1f}",
        f"  4. 安全评估:   {health.security_score:.1f}",
        f"  5. 文档评估:   {health.documentation_score:.1f}",
        "",
        "补充维度评分:",
        f"  Token预算:     {health.token_budget_score:.1f}",
        f"  重复检测:      {health.duplicate_score:.1f}",
        f"  闲置检测:      {health.idle_score:.1f}",
        f"  加载链路:      {health.loading_chain_score:.1f}",
        f"  描述精简:      {health.description_score:.1f}",
    ]
    if health.recommendations:
        lines.append("")
        lines.append("改进建议:")
        for rec in health.recommendations[:8]:
            lines.append(f"  - {rec}")
    lines.append("")
    lines.append("=" * 60)
    return "\n".join(lines)
@dataclass
class TokenBudget:
    skill_name: str
    total_chars: int
    estimated_tokens: int
    description_chars: int
    body_chars: int
    frontmatter_chars: int
    skill_path: str = ""
    budget_percent: float = 0.0
    status: str = "ok"
@dataclass
class DuplicateGroup:
    skills: list[str]
    similarity: float
    reason: str
def walk_skill_mds(skills_dir: Any) -> Iterator[tuple[str, Path]]:
    if not str(skills_dir or "").strip():
        return
    skills_path = Path(skills_dir)
    if not skills_path.is_dir():
        return
    skill_mds, partial = rglob_paths_tolerant(skills_path, "SKILL.md")
    if partial:
        _log.warning(
            "[Health] 技能目录枚举不完整（部分目录不可读），本次结果可能缺失: %s",
            skills_path)
    yield from _collect_skill_md_entries(skills_path, skill_mds)
def is_skipped_dir_name(name: str) -> bool:
    return is_pruned_scan_dir(name, _SKILL_SCAN_SKIP_DIRS)
def _collect_skill_md_entries(skills_path: Path,
                              skill_mds: list[Path]) -> list[tuple[str, Path]]:
    entries: list[tuple[str, Path]] = []
    for skill_md in sorted(skill_mds, key=str):
        try:
            rel_parts = skill_md.relative_to(skills_path).parts
        except ValueError as _e:
            log_swallowed(__name__, _e, context='walk_skill_mds:ValueError')
            continue
        if not skill_md.is_file():
            continue
        if any(is_skipped_dir_name(part) for part in rel_parts[:-1]):
            continue
        skill_name = skill_md.parent.name or _skill_leaf_name(skill_md.parent)
        entries.append((skill_name, skill_md))
    return entries
def skill_md_desc_line(skill_dir: str) -> int:
    if not str(skill_dir or "").strip():
        return 0
    try:
        content = read_skill_text(Path(skill_dir) / "SKILL.md")
    except OSError as _e:
        log_swallowed(__name__, _e, context='skill_md_desc_line:OSError')
        return 0
    lines = content.splitlines()
    body_start = locate_frontmatter_body_start(lines)
    if not body_start:
        return 0
    for index in range(body_start - 2, -1, -1):
        if is_field_key_line(lines[index], "description"):
            return index + 1
    return 0
DESC_WARN = DESC_MAX
DESC_CRITICAL = DESC_MAX * 2
def determine_budget_status(desc_chars: int) -> str:
    if desc_chars > DESC_CRITICAL:
        return "critical"
    if desc_chars > DESC_WARN:
        return "warn"
    return "ok"
def diag_token_budget(skills_dir: str) -> list[TokenBudget]:
    budgets = []
    total_chars = 0
    for skill_name, skill_md in list(walk_skill_mds(skills_dir)):
        try:
            content = read_skill_text(skill_md)
        except (OSError, UnicodeDecodeError) as e:
            _log.warning("[Quality] 扫描失败,跳过 %s: %s", skill_md, e)
            continue
        fm, body = parse_frontmatter(content)
        frontmatter_chars = len(fm) if fm else 0
        body_chars = len(body)
        content_chars = len(content)
        total_chars += content_chars
        desc_chars = len(extract_description(content))
        budgets.append(TokenBudget(
            skill_name=skill_name, total_chars=content_chars,
            estimated_tokens=_estimate_token_count(content),
            description_chars=desc_chars,
            body_chars=body_chars, frontmatter_chars=frontmatter_chars,
            skill_path=str(skill_md),
            budget_percent=0.0, status=determine_budget_status(desc_chars),
        ))
    if total_chars > 0:
        for b in budgets:
            b.budget_percent = round(b.total_chars / total_chars * 100, 1)
    budgets.sort(key=lambda b: b.total_chars, reverse=True)
    return budgets
def _as_keyword_set(keywords: Any) -> frozenset[str] | None:
    if isinstance(keywords, (set, frozenset, list, tuple)):
        try:
            normalized = frozenset(keywords)
        except TypeError as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='_as_keyword_set:TypeError')
            return None
        return normalized if normalized else None
    return None
def _as_similarity_threshold(threshold: Any) -> float:
    value = finite_float_or_none(threshold)
    if value is None or value <= 0:
        return _DEFAULT_SIMILARITY_THRESHOLD
    return min(value, 1.0)
def _normalized_days_threshold(value: Any) -> float:
    number = finite_float_or_none(value)
    return number if number is not None and number > 0 else UNUSED_DAYS_THRESHOLD
def _mtime_age(mtime: datetime, threshold_days: float, *,
               now: datetime | None = None) -> tuple[int, bool]:
    current = datetime.now(UTC) if now is None else now
    elapsed_seconds = max(0.0, (current - mtime).total_seconds())
    age_days = int(elapsed_seconds // 86400)
    return age_days, elapsed_seconds > threshold_days * 86400
def _compare_skill_pair(a: Any, b: Any, name_a: Any, name_b: Any,
                       similarity_threshold: Any) -> DuplicateGroup | None:
    if _same_skill_name(name_a, name_b):
        return DuplicateGroup(skills=[name_a, name_b], similarity=1.0, reason="完全同名")
    if a.get("content_hash") and a.get("content_hash") == b.get("content_hash"):
        return DuplicateGroup(
            skills=[name_a, name_b], similarity=1.0,
            reason="内容完全一致(SKILL.md hash相同)")
    keywords_a = _as_keyword_set(a.get("keywords"))
    keywords_b = _as_keyword_set(b.get("keywords"))
    if not (keywords_a and keywords_b):
        return None
    intersection = len(keywords_a & keywords_b)
    union = len(keywords_a | keywords_b)
    jaccard = intersection / union
    if jaccard < similarity_threshold:
        return None
    return DuplicateGroup(
        skills=[name_a, name_b],
        similarity=round(jaccard, 3),
        reason=f"关键词重叠 {intersection}/{union}",
    )
def _description_keywords(description: str) -> set[str]:
    keywords: set[str] = set()
    for _m in re.finditer(r"[a-zA-Z0-9]+|([\u4e00-\u9fff]+)",
                          description.lower()):
        seg = _m.group(0)
        if _m.group(1):
            if len(seg) == 1:
                keywords.add(seg)
            else:
                keywords.update(seg[i:i + 2] for i in range(len(seg) - 1))
        else:
            keywords.add(seg)
    return keywords
def detect_duplicates(
        skills_dir: str,
        similarity_threshold: float = _DEFAULT_SIMILARITY_THRESHOLD
) -> list[DuplicateGroup]:
    threshold = _as_similarity_threshold(similarity_threshold)
    skill_data: list[dict] = []
    for skill_name, skill_md in list(walk_skill_mds(skills_dir)):
        try:
            content = read_skill_text(skill_md)
            desc = extract_description(content)
            skill_data.append({
                "name": skill_name, "description": desc,
                "content_hash": hashlib.sha256(content.encode()).hexdigest(),
                "keywords": _description_keywords(desc),
            })
        except (OSError, UnicodeDecodeError) as e:
            _log.warning("[Quality] 扫描失败,跳过 %s: %s", skill_md, e)
            continue
    duplicates = []
    for a, b in combinations(skill_data, 2):
        result = _compare_skill_pair(
            a, b, a["name"], b["name"], threshold,
        )
        if result is not None:
            duplicates.append(result)
    return duplicates
def detect_unused_skills(
        skills_dir: str,
        days_threshold: float = UNUSED_DAYS_THRESHOLD) -> list[str]:
    threshold = _normalized_days_threshold(days_threshold)
    unused = []
    for skill_name, skill_md in list(walk_skill_mds(skills_dir)):
        mtime, _source = _newest_skill_mtime(skill_md.parent, skill_md)
        if mtime is None:
            _log.warning("[Quality] 修改时间证据不可用，跳过 %s", skill_md)
            continue
        if _mtime_age(mtime, threshold)[1]:
            unused.append(skill_name)
    return unused
@dataclass
class TodoItem:
    file: str = ""
    line: int = 0
    marker: str = ""
    description: str = ""
    is_valid: bool = True
    validation_note: str = ""
    actual_code: str = ""
    file_mtime: datetime | None = None
    age_days: int = 0
    is_stale: bool = False
@dataclass
class TodoDiagnoseReport:
    skill_path: str = ""
    total_files: int = 0
    total_lines: int = 0
    items: list[TodoItem] = field(default_factory=list)
    stale_items: list[TodoItem] = field(default_factory=list)
    stale_count: int = 0
    stale_threshold_days: float = UNUSED_DAYS_THRESHOLD
    partial: bool = False
_TODO_MARKER_ALIASES: dict[str, str] = {
    "TODO": "TODO",
    "FIXME": "FIXME",
    "HACK": "HACK",
    "XXX": "XXX",
    "WARN": "WARN(?:ING)?",
}
def _todo_marker_pattern(alias: str) -> re.Pattern[str]:
    return re.compile(
        rf"#\s*{alias}(?=[\s:：(（/,，]|$)\s*"
        rf"(?:\(([^)]*)\)|（([^）]*)）)?\s*[:：]?\s*(.*)",
        re.IGNORECASE)
_PATTERN_RULES: dict[str, re.Pattern] = {
    marker: _todo_marker_pattern(alias)
    for marker, alias in _TODO_MARKER_ALIASES.items()
}
_DANGER_SIGNALS: list[str] = [
    "临时", "暂时", "先这样", "后续", "以后", "待定",
    "不知道", "不确定", "可能", "大概",
    "绕过", "跳过", "忽略",
    "temporarily", "remove later", "稍后删除", "稍后移除",
    "not implemented", "未实现", "尚未实现",
    "placeholder", "占位",
    "stub", "桩",
    "broken", "已损坏",
    "deprecated", "已废弃",
    "dangerous", "危险",
    "hack", "workaround",
]
def _inside_string_literal(line: str, pos: int) -> bool:
    in_str = False
    quote = ""
    i = 0
    while i < pos:
        if in_str:
            i, in_str = _advance_in_string(line, i, quote)
            quote = quote if in_str else ""
            continue
        ch = line[i]
        if ch == "#":
            return False
        if ch not in ("'", '"'):
            i += 1
            continue
        if line[i:i + 3] != ch * 3:
            in_str = True
            quote = ch
            i += 1
            continue
        in_triple, after_close = _triple_quote_verdict(line, i, pos)
        if in_triple:
            return True
        i = after_close
    return in_str
def _triple_quote_verdict(line: str, start: int, pos: int) -> tuple[bool, int]:
    quote = line[start:start + 3]
    close = line.find(quote, start + 3)
    if close == -1 or close + 3 > pos:
        return True, -1
    return False, close + 3
def _advance_in_string(line: str, i: int, quote: str) -> tuple[int, bool]:
    if line[i] == "\\":
        return i + 2, True
    return i + 1, line[i] != quote
def _parse_todo_line(file_path: str, line_no: int, line: str,
                     string_spans: list[tuple[int, int]] | None = None) -> TodoItem | None:
    best_marker = ""
    best_match: re.Match[str] | None = None
    for marker, pattern in _PATTERN_RULES.items():
        match = _first_code_match(pattern, line, string_spans)
        if match is None:
            continue
        if best_match is None or match.start() < best_match.start():
            best_marker, best_match = marker, match
    if best_match is None:
        return None
    match = best_match
    owner = match.group(1) if match.group(1) is not None else match.group(2)
    description_text = _LEADING_MARKER_ENUM_PAT.sub(
        "", match.group(3), count=1)
    description = " ".join(
        p for p in (owner, description_text) if p
    ).strip()
    return TodoItem(
        file=file_path,
        line=line_no,
        marker=best_marker,
        description=description,
        actual_code=line.strip(),
    )
def _pos_in_string_literal(line: str, pos: int,
                           string_spans: list[tuple[int, int]] | None) -> bool:
    if string_spans is None:
        return _inside_string_literal(line, pos)
    return any(s <= pos < e for s, e in string_spans)
def _first_code_match(pattern: re.Pattern, line: str,
                      string_spans: list[tuple[int, int]] | None):
    pos = 0
    while True:
        match = pattern.search(line, pos)
        if match is None:
            return None
        if not _pos_in_string_literal(line, match.start(), string_spans):
            return match
        pos = match.start() + 1
_MARKER_ENUM_WORD = r"(?:TODO|FIXME|HACK|XXX|WARN|WARNING)"
_MARKER_ENUM_PAT = re.compile(  # jwsgj:suppress SE-30
    rf"\b{_MARKER_ENUM_WORD}(?:\s*[/,，]\s*{_MARKER_ENUM_WORD})+",
    re.IGNORECASE)
_LEADING_MARKER_ENUM_PAT = re.compile(
    rf"^(?:\s*[/,，]\s*{_MARKER_ENUM_WORD})+\s*[:：]?\s*",
    re.IGNORECASE)
_DANGER_SIGNAL_SUFFIXES = {
    "stub": r"(?:s|bed|bing)?",
    "hack": r"(?:s|ed|ing)?",
    "placeholder": r"s?",
    "workaround": r"s?",
    "dangerous": r"(?:ly)?",
}
def _has_danger_signal(description: str, signal: str) -> bool:
    if not signal.isascii():
        return signal in description
    suffix = _DANGER_SIGNAL_SUFFIXES.get(signal, "")
    return re.search(
        rf"(?<![a-z0-9_]){re.escape(signal)}{suffix}(?![a-z0-9_])",
        description) is not None
def _check_danger_signals(todo: TodoItem) -> None:
    desc_lower = _MARKER_ENUM_PAT.sub(" ", todo.description).lower()
    for signal in _DANGER_SIGNALS:
        if _has_danger_signal(desc_lower, signal):
            todo.is_valid = False
            todo.validation_note = "Danger signal: " + repr(signal)
            return
def _tokenized_comment_columns(
        content: str, fpath: Path) -> tuple[dict[int, list[int]], bool]:
    columns: dict[int, list[int]] = {}
    tokens = tokenize.generate_tokens(io.StringIO(content).readline)
    while True:
        try:
            token = next(tokens)
        except StopIteration:
            return columns, True
        except (tokenize.TokenError, SyntaxError, ValueError) as exc:
            _log.warning(
                "[Debt] TODO 台账词法分析不完整，仅保留已确认注释 %s: %s",
                fpath, exc)
            return columns, False
        if token.type == tokenize.COMMENT:
            columns.setdefault(token.start[0], []).append(token.start[1])
def _scan_file_for_todos(fpath: Path, report: TodoDiagnoseReport,
                         cache=None) -> None:
    content = read_source(str(fpath), cache)
    if content is None:
        report.partial = True
        _log.warning("[Debt] TODO 台账源文件读取失败，结果标记为不完整: %s", fpath)
        return
    file_mtime = _todo_file_mtime(fpath)
    lines = split_lines_lf(content)
    age_days, is_stale = (
        (0, False) if file_mtime is None
        else _mtime_age(file_mtime, report.stale_threshold_days)
    )
    report.total_lines += len(lines)
    row_spans = string_token_row_spans(content)
    comment_columns: dict[int, list[int]] | None = None
    if row_spans is None:
        comment_columns, complete = _tokenized_comment_columns(content, fpath)
        if not complete:
            report.partial = True
    for i, line in enumerate(lines, 1):
        if comment_columns is None:
            spans = row_spans.get(i, []) if row_spans is not None else None
            candidates = [
                _parse_todo_line(str(fpath), i, line, string_spans=spans)]
        else:
            candidates = [
                _parse_todo_line(
                    str(fpath), i, line[column:], string_spans=[])
                for column in comment_columns.get(i, [])
            ]
        for todo in candidates:
            if todo is None:
                continue
            if comment_columns is not None:
                todo.actual_code = line.strip()
            if file_mtime is None:
                report.partial = True
            _check_danger_signals(todo)
            todo.file_mtime = file_mtime
            todo.age_days = age_days
            todo.is_stale = is_stale
            report.items.append(todo)
def _todo_file_mtime(fpath: Path) -> datetime | None:
    try:
        return datetime.fromtimestamp(fpath.stat().st_mtime, tz=UTC)
    except (OSError, OverflowError, ValueError) as exc:
        _log.warning("[Debt] Todo scan mtime 降级: %s: %s", fpath, exc)
        return None
def _todo_scan_excluded(fpath: Path, sp: Path,
                        skip_dirs: frozenset[str]) -> bool:
    rel_parts = fpath.relative_to(sp).parts
    dir_parts, file_name = rel_parts[:-1], rel_parts[-1]
    if not is_scan_py_name(file_name):
        return True
    if any(is_pruned_scan_dir(p, skip_dirs) for p in dir_parts):
        return True
    stem = os.path.splitext(file_name)[0]
    return (file_name.startswith(".")
            or is_backup_like_dir(stem)
            or is_temp_artifact_dir(stem))
def diag_todos(skill_path: str,
                stale_threshold_days: float = UNUSED_DAYS_THRESHOLD,
                cache: Any = None) -> TodoDiagnoseReport:
    threshold = _normalized_days_threshold(stale_threshold_days)
    report = TodoDiagnoseReport(
        skill_path=skill_path, stale_threshold_days=threshold,
    )
    if not str(skill_path or "").strip():
        return report
    sp = Path(skill_path)
    if not sp.is_dir():
        report.partial = True
        _log.warning("[Debt] TODO 台账目标不存在或不是目录，结果标记为不完整: %s", sp)
        return report
    py_paths, partial = rglob_paths_tolerant(sp, "*")
    if partial:
        report.partial = True
        _log.warning(
            "[Debt] TODO 台账目录枚举不完整（部分目录不可读），"
            "标记统计可能缺失: %s", sp)
    skip_dirs = _health_scan_skip_dirs(sp)
    for fpath in py_paths:
        if fpath.is_dir() or _todo_scan_excluded(fpath, sp, skip_dirs):
            continue
        report.total_files += 1
        _scan_file_for_todos(fpath, report, cache=cache)
    report.stale_items = [item for item in report.items if item.is_stale]
    report.stale_count = len(report.stale_items)
    return report

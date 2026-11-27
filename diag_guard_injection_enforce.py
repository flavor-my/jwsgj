from __future__ import annotations

import ast
import hashlib
import logging
import math
import os
import time
from collections.abc import Callable, Iterator, Mapping
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from enum import Enum
from threading import RLock
from typing import Any, NamedTuple

from jwsgj.diag_debt_engine import (
    CodeQualityScorer,
    FixGate,
    get_debt_engine,
)
from jwsgj.diag_guard_injection_scan import (
    CodeRuleScanner,
    RefactoringEngineV3,
    _finding,
    _safe_str,
    scan_source,
)
from jwsgj.diag_shared_ast_nodes import (
    calc_nesting,
    count_params,
    definition_start_line,
    iter_own_scope,
    own_scope_line_span,
)
from jwsgj.diag_shared_source_core import (
    coerce_source_text,
    count_lines,
    read_source,
    read_source_strict,
)
from jwsgj.diag_shared_source_core import parse_cached as parse_cached_source
from jwsgj.diag_smell_detector import (
    WHOLE_FILE_ONLY_SMELL_RULES,
    ComprehensiveDiagnoser,
    SmellDetectorV3,
)
from jwsgj.diag_types_defs import SizeViolation
from jwsgj.diag_types_normalize import (
    is_real_number,
    normalize_list_field,
)
from jwsgj.diag_types_vocab import (
    DEFAULT_SESSION_QUOTA,
    DEFAULT_TASK_TYPE,
    FIELD_RECOMMENDATIONS,
    HARD_MAX_NESTING,
    HARD_MAX_PARAMS,
    MSG_SYNTAX_ERROR_SKIP,
    NEAR_BUDGET_RATIO,
    ROLE_HARD_THRESHOLDS,
    RULE_TOO_MANY_PARAMS,
    TASK_BUDGET_FACTOR,
    TASK_BUDGETS,
    FileRole,
    SizeGateStatus,
    classify_file_role,
    coerce_task_type,
    get_role_thresholds,
    normalize_filepath,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    collect_py_files,
    is_test_file_path,
)

_log = logging.getLogger(__name__)
__all__ = [
    'BudgetDecision',
    'BudgetReport',
    'CodeInjectionEngine',
    'EntityBudget',
    'SessionQuota',
    'SizeGuard',
    'SizeReport',
    'SourceBudgetGuard',
    'VerifyResult',
    'get_session_budget_state',
    'get_size_guard',
    'record_session_write',
    'run_cie_batch_verify',
    'run_cie_incremental_check',
    'size_gate_issues',
    'supplement_cie_sections',
]
_log.info("diag_guard_injection_enforce 已加载：%d 项导出", len(__all__))
def _severity_text(severity: Any) -> str:
    value = getattr(severity, "value", severity)
    if isinstance(value, str) and value:
        return value
    return "MEDIUM"
_FIX_GATE_BLOCK_PREFIXES: tuple[str, ...] = (
    "C4", "SEC-", "CS-9", "RL-01", "SZ-01", "WRITE-BLOCK",
    "SYNTAX", "EMPTY",
)
_FIX_GATE_WARN_PREFIXES: tuple[str, ...] = (
    "C6", "C13", "CS-92", "CS-95", "DB-", "R3", "C11",
    "RB-", "ST-", "EX-01",
)
_FIX_GATE = FixGate(
    block_prefixes=_FIX_GATE_BLOCK_PREFIXES,
    warn_prefixes=_FIX_GATE_WARN_PREFIXES,
)
@dataclass
class VerifyResult:
    passed: bool = True
    errors: list | None = None
    warnings: list | None = None
    score: float = 0.0
    details: dict | None = None
    violations: list | None = None
    suggestions: list | None = None
    def __post_init__(self):
        if self.errors is None:
            self.errors = self.violations if self.violations is not None else []
        if self.warnings is None:
            self.warnings = []
        if self.details is None:
            self.details = {}
        if self.violations is None:
            self.violations = self.errors
        if self.suggestions is None:
            self.suggestions = []
    @property
    def ok(self) -> bool:
        return self.passed and len(self.errors) == 0
def _safe_stage(label: str, stage: Callable[[], Any], fallback: Any,
                errors: list[dict] | None = None) -> Any:
    try:
        return stage()
    except Exception as e:  # noqa: BLE001
        _log.warning("%s failed: %s", label, e)
        if errors is not None:
            errors.append(_finding(
                "CIE-VERIFY-ERROR",
                f"{label} 验证阶段失败({type(e).__name__})，无法证明代码安全",
                0, rule_type="verification_error"))
        return fallback
def _warning_identity(item: Any) -> tuple[str, int, str]:
    if not isinstance(item, Mapping):
        text = _safe_str(item)
        return text, 0, text
    rule = item.get("rule_id") or item.get("type") or item.get("rule") or ""
    line = item.get("line")
    message = item.get("message") or item.get("msg") or ""
    return (_safe_str(rule), line if isinstance(line, int) else 0,
            _safe_str(message))
def _debt_gate_level(debt_report: Any) -> str:
    if getattr(debt_report, "blocked", False):
        return "BLOCK"
    level = getattr(debt_report, "level", None)
    level = getattr(level, "value", level)
    if level == "BLOCK":
        return "BLOCK"
    return "WARN" if level == "WARN" else "PASS"
def _size_gate_entry(rule_id: str, entry_type: str, prefix: str,
                     severity: str, size_gate: dict) -> dict:
    return {
        "type": entry_type,
        "rule_id": rule_id,
        "message": prefix + ": " + _safe_str(size_gate.get("summary", "")),
        "severity": severity,
        "line": 0,
        "details": size_gate.get("violations", []),
    }
class CodeInjectionEngine(CodeRuleScanner):
    def post_verify(self, code: str,
                    task_type: str = DEFAULT_TASK_TYPE,
                    file_path: str = "") -> VerifyResult:
        t0 = time.time()
        blocked = self._pv_reject_unverifiable_payload(code, t0)
        if blocked is not None:
            return blocked
        violations: list[dict] = []
        warnings: list[dict] = []
        suggestions: list[str] = []
        stage_errors: list[dict] = []
        ast_violations, ast_warnings = self._ast_scan(code)
        violations.extend(ast_violations)
        warnings.extend(ast_warnings)
        score = 100.0 if not violations else max(0, 100 - len(violations) * 10)
        gate_decisions = {}
        quality_score = None
        size_gate = None
        score, suggestions, gate_decisions = _safe_stage(
            "pv_assess_and_gate",
            lambda: self._pv_assess_and_gate(violations, warnings),
            (score, suggestions, gate_decisions), errors=stage_errors)
        quality_score, size_gate, violations, warnings, score = _safe_stage(
            "pv_quality_size_gate",
            lambda: self._pv_quality_size_gate(
                code, violations, warnings, score, task_type, file_path),
            (quality_score, size_gate, violations, warnings, score),
            errors=stage_errors)
        warnings, suggestions, smell_findings = _safe_stage(
            "pv_detect_smells",
            lambda: self._pv_detect_smells(code, warnings, suggestions),
            (warnings, suggestions, None), errors=stage_errors)
        warnings, suggestions, quality_score = _safe_stage(
            "pv_comprehensive_diag",
            lambda: self._pv_comprehensive_diag(
                code, warnings, suggestions, quality_score,
                smell_findings=smell_findings),
            (warnings, suggestions, quality_score), errors=stage_errors)
        if stage_errors:
            violations.extend(stage_errors)
            score = 0.0
        elapsed_ms = (time.time() - t0) * 1000
        suggestions = list(dict.fromkeys(suggestions))
        vr = VerifyResult(
            passed=not violations,
            errors=violations,
            warnings=warnings,
            score=score,
            suggestions=suggestions,
            details={
                "quality_score": quality_score,
                "size_gate": size_gate,
                "gate_decisions": gate_decisions,
                "scan_time_ms": elapsed_ms,
            },
        )
        _log.info(
            "post_verify 完成: passed=%s, violations=%d, warnings=%d, "
            "score=%s, %.1fms",
            vr.passed, len(violations), len(warnings), score, elapsed_ms,
        )
        return vr
    def _pv_reject_unverifiable_payload(self, code: Any,
                                          t0: float) -> VerifyResult | None:
        if isinstance(code, str) and code.strip():
            return None
        if isinstance(code, str):
            violation = _finding(
                "EMPTY", "空白源码载荷，无有效代码产物", 0,
                rule_type="empty_payload")
            suggestion = "检查上游生成链路，产出非空代码后重新验证"
            _log.warning("[CIE] post_verify 空白源码载荷，降级为阻断结果")
        else:
            violation = _finding(
                "SYNTAX",
                "非字符串源码输入(" + type(code).__name__ + ")，物理上不可解析",
                0, rule_type="syntax_error")
            suggestion = "提供字符串源码（str）后重新验证"
            _log.warning(
                "[CIE] post_verify 非字符串源码输入: %s，降级为阻断结果",
                type(code).__name__)
        return self._blocked_verify_result(
            t0, [violation], [], [suggestion])
    @staticmethod
    def _blocked_verify_result(t0: float, violations: list[dict],
                               warnings: list[dict],
                               suggestions: list[str]) -> VerifyResult:
        elapsed_ms = (time.time() - t0) * 1000
        return VerifyResult(
            passed=False,
            errors=violations,
            warnings=warnings,
            score=0.0,
            suggestions=suggestions,
            details={
                "quality_score": None,
                "size_gate": None,
                "gate_decisions": {},
                "scan_time_ms": elapsed_ms,
            },
        )
    def _pv_assess_and_gate(self, violations: Any, warnings: Any) -> Any:
        suggestions = self._generate_suggestions(violations, warnings)
        score = self._calculate_score(violations, warnings)
        gate_decisions = {}
        for v in violations:
            rule_id = v.get("rule_id", "")
            gate_decisions[rule_id] = _FIX_GATE.check(
                rule_id, v.get("severity", ""))
        return score, suggestions, gate_decisions
    def _pv_quality_size_gate(
        self, code: Any, violations: Any, warnings: Any, score: Any,
        task_type: str, file_path: str,
    ) -> Any:
        _qs = CodeQualityScorer()
        quality_score = _qs.score(code) or {}
        size_report = get_size_guard().check(
            code, file_path=file_path, task_type=task_type)
        size_gate = size_report.to_dict()
        if size_report.gate is SizeGateStatus.BLOCK:
            if not any(v.get("type") == "syntax_error" for v in violations):
                violations.append(_size_gate_entry(
                    "SZ-01", "size_gate_blocked", "代码体积超标",
                    "CRITICAL", size_gate))
                score = max(0, score - 20)
        elif size_report.gate is SizeGateStatus.WARN:
            warnings.append(_size_gate_entry(
                "SZ-02", "size_gate_warning", "代码体积偏高",
                "WARNING", size_gate))
        return quality_score, size_gate, violations, warnings, score
    def _pv_detect_smells(self, code: Any, warnings: Any, suggestions: Any) -> Any:
        sd = SmellDetectorV3()
        findings = sd.detect_all(code)
        for f in findings:
            warnings.append({
                "type": "smell_v3",
                "rule_id": f.rule_id,
                "message": f.message,
                "severity": _severity_text(f.severity),
                "line": f.line,
            })
        if findings:
            re_v3 = RefactoringEngineV3()
            smell_dicts = [
                {
                    "smell": f.rule_id.replace("SMELL-", "").replace("-", " ").title(),
                    "location": str(f.line),
                }
                for f in findings
            ]
            seen_advice = {s for s in suggestions if isinstance(s, str)}
            for r in re_v3.recommend_refactorings(smell_dicts):
                msg = r.get("refactoring", str(r)) if isinstance(r, dict) else str(r)
                advice = f"[重构建议] {msg}"
                if advice in seen_advice:
                    continue
                seen_advice.add(advice)
                suggestions.append(advice)
        return warnings, suggestions, findings
    def _pv_comprehensive_diag(self, code: Any, warnings: Any, suggestions: Any,
                                quality_score: Any,
                                smell_findings: list | None = None) -> Any:
        ca = ComprehensiveDiagnoser()
        diag = ca.diag_code(code, smell_findings=smell_findings)
        if diag.get("smells"):
            seen = {_warning_identity(w) for w in warnings}
            for smell in diag["smells"][:5]:
                entry = {
                    "type": "comprehensive_smell",
                    "rule_id": smell.get("rule_id", ""),
                    "message": smell.get("message", ""),
                    "severity": smell.get("severity", "MEDIUM"),
                    "line": smell.get("line", 0),
                }
                identity = _warning_identity(entry)
                if identity in seen:
                    continue
                seen.add(identity)
                warnings.append(entry)
        if diag.get(FIELD_RECOMMENDATIONS):
            for rec in diag[FIELD_RECOMMENDATIONS][:5]:
                suggestions.append(f"[综合诊断] {rec}")
        if quality_score is None:
            quality_score = {}
        quality_score["comprehensive_overall_score"] = diag.get("overall_score", 0)
        quality_score["comprehensive_maintainability_index"] = diag.get(
            "maintainability_index", 0
        )
        return warnings, suggestions, quality_score
    def verify_with_debt_gate(
        self, code: str, task_type: str = DEFAULT_TASK_TYPE,
        file_path: str = "",
    ) -> dict[str, Any]:
        t0 = time.time()
        vr = self.post_verify(code, task_type, file_path)
        debt_report = None
        debt_gate = "PASS"
        try:
            de = get_debt_engine()
            debt_report = de.evaluate(
                code, vr.violations, vr.warnings,
                history_key=file_path or None)
            debt_gate = _debt_gate_level(debt_report)
        except Exception as e:  # noqa: BLE001
            _log.warning("[debt-gate] 债务评分不可用，阻断验证: %s", e)
            debt_gate = "BLOCK"
            vr.passed = False
            vr.score = 0.0
            vr.violations.append(_finding(
                "CIE-DEBT-GATE-ERROR",
                f"债务门禁执行失败({type(e).__name__})，无法完成验证",
                0, rule_type="debt_gate_error"))
        try:
            debt_payload = (
                debt_report.to_dict() if debt_report is not None else None)
        except Exception as e:  # noqa: BLE001
            _log.warning("[debt-gate] 债务报告序列化失败,降级为 None: %s", e)
            debt_payload = None
        elapsed_ms = (time.time() - t0) * 1000
        _log.info(
            "verify_with_debt_gate 完成: passed=%s, debt_gate=%s, "
            "score=%s, violations=%d, warnings=%d, %.1fms",
            vr.passed and debt_gate != "BLOCK",
            debt_gate, vr.score,
            len(vr.violations), len(vr.warnings),
            elapsed_ms,
        )
        return {
            "passed": vr.passed and debt_gate != "BLOCK",
            "gate": debt_gate,
            "score": vr.score,
            "violations": vr.violations,
            "warnings": vr.warnings,
            "suggestions": vr.suggestions,
            "debt_report": debt_payload,
            "scan_time_ms": round(elapsed_ms, 2),
        }
_INCR_CHUNK_LINES = 80
_INCR_MAX_FILES = 5
_IC_SIZE_WARN_LINES = 200
def _normalize_batch_payload(file_paths: Any) -> list | None:
    if isinstance(file_paths, (str, bytes)):
        return [file_paths]
    if file_paths is None:
        return None
    if isinstance(file_paths, Mapping):
        return [file_paths] if file_paths else None
    if isinstance(file_paths, (list, tuple)):
        return list(file_paths) or None
    try:
        normalized = list(file_paths)
    except TypeError as _e:
        log_swallowed(__name__, _e, context='_batch_verify:TypeError')
        normalized = [file_paths]
    return normalized or None
def _normalize_batch_workers(max_workers: Any, n_files: int) -> int:
    default_workers = min(8, max(1, n_files))
    if max_workers is None:
        return default_workers
    try:
        max_workers = int(max_workers)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context='_normalize_batch_workers:TypeError')
        return default_workers
    return max(1, max_workers)
def _error_vr(err_type: str, rule_id: str, message: str) -> VerifyResult:
    return VerifyResult(
        passed=False,
        errors=[{
            "type": err_type, "rule_id": rule_id,
            "message": message, "severity": "HIGH",
        }],
    )
def _read_source_for_verify(fp: str) -> tuple[str | None, VerifyResult | None]:
    if not os.path.isfile(fp):
        return None, _error_vr(
            "file_not_found", "BATCH-404", "文件不存在: " + fp)
    try:
        return read_source_strict(fp), None
    except OSError as e:
        _log.warning("[batch_verify] 文件读取失败，降级错误结果: %s: %s", fp, e)
        return None, _error_vr(
            "file_read_error", "BATCH-403",
            f"文件读取失败({e.__class__.__name__}): {fp}")
def _normalize_issue_id(value: Any) -> str:
    return value if isinstance(value, str) and value else "UNKNOWN"
def _count_issue_ids(items: Any, issue_counts: dict[str, int]) -> None:
    for item in items:
        rid = (_normalize_issue_id(item.get("rule_id"))
               if isinstance(item, Mapping) else "UNKNOWN")
        issue_counts[rid] = issue_counts.get(rid, 0) + 1
class _StatFields(NamedTuple):
    violations: list
    warnings: list
    score: Any
    scan_ms: Any
def _first_list_payload(*values: Any) -> list:
    for value in values:
        if isinstance(value, (list, tuple)):
            return value
    return []
def _stat_number_or_none(value: Any) -> Any:
    return value if is_real_number(value) else None
def _stat_fields_of(r: Any) -> _StatFields:
    details = getattr(r, "details", None)
    if not isinstance(details, dict):
        details = {}
    return _StatFields(
        violations=_first_list_payload(
            getattr(r, "violations", None), getattr(r, "errors", None)),
        warnings=_first_list_payload(getattr(r, "warnings", None)),
        score=_stat_number_or_none(getattr(r, "score", None)),
        scan_ms=_stat_number_or_none(details.get("scan_time_ms", 0)),
    )
def _parse_chunk(source: str, failure_hint: str) -> Any | None:
    try:
        tree = ast.parse(source)
        compile(tree, "<incremental_chunk>", "exec")
        return tree
    except (SyntaxError, ValueError, RecursionError, MemoryError) as _e:
        _log.debug("[incremental] %s: %s", failure_hint, _e)
        return None
def _size_gate_value(size_report: Any) -> str:
    gate = getattr(size_report, "gate", None)
    value = getattr(gate, "value", gate)
    return value if isinstance(value, str) else ""
def _size_report_payload(size_report: Any, gate_value: str) -> dict:
    return {
        "total_lines": getattr(size_report, "total_lines", 0),
        "gate": gate_value,
        "violations": [
            {"type": getattr(v, "type", ""), "msg": getattr(v, "message", "")}
            for v in (getattr(size_report, "violations", None) or [])[:3]
        ],
    }
def _ic_adj_line(raw: int, line_offset: int) -> int:
    return max(0, raw - line_offset)
def _batch_verify(engine: Any, file_paths: Any,
                  max_workers: int | None = None) -> dict:
    normalized = _normalize_batch_payload(file_paths)
    if normalized is None:
        return {}
    max_workers = _normalize_batch_workers(max_workers, len(normalized))
    results: dict = {}
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(_verify_one_file, engine, fp): fp
                   for fp in normalized}
        for future in as_completed(futures):
            fp, result = future.result()
            results[fp] = result
    passed_n = sum(1 for r in results.values() if getattr(r, "passed", False))
    _log.info(
        "batch_verify 完成: files=%d, passed=%d, failed=%d",
        len(results), passed_n, len(results) - passed_n,
    )
    return results
def _verify_one_file(engine: Any, fp: Any) -> tuple[str, VerifyResult]:
    try:
        key = fp if isinstance(fp, str) else repr(fp)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='_verify_one_file:repr:Exc')
        key = "<unreprable path>"
    if not isinstance(fp, str):
        return key, _error_vr(
            "invalid_path", "BATCH-400",
            f"路径载荷非法(非 str: {type(fp).__name__}): {key}")
    try:
        code, read_error = _read_source_for_verify(fp)
    except Exception as e:  # noqa: BLE001
        _log.warning("[batch_verify] 单文件读取未预期异常，降级错误结果: %s: %s",
                     key, e)
        return key, _error_vr(
            "invalid_path", "BATCH-400",
            f"路径载荷非法或未预期异常({e.__class__.__name__}): {key}")
    if read_error is not None:
        return key, read_error
    try:
        return key, engine.post_verify(code, file_path=key)
    except Exception as e:  # noqa: BLE001
        _log.warning("[batch_verify] post_verify 未预期异常: %s: %s",
                     key, e, exc_info=True)
        return key, _error_vr(
            "verify_internal_error", "BATCH-500",
            f"验证内部异常({e.__class__.__name__}): {e}")
def _batch_stats(batch_results: Any) -> dict[str, Any]:
    if not isinstance(batch_results, dict):
        batch_results = {}
    total_batched = len(batch_results)
    total_violations = 0
    total_warnings = 0
    scores: list[float] = []
    total_scan_time = 0.0
    issue_counts: dict[str, int] = {}
    for r in batch_results.values():
        violations, warnings, score, scan_ms = _stat_fields_of(r)
        total_violations += len(violations)
        total_warnings += len(warnings)
        if score is not None:
            scores.append(score)
        if scan_ms is not None:
            total_scan_time += scan_ms
        _count_issue_ids(violations, issue_counts)
        _count_issue_ids(warnings, issue_counts)
    avg_score = sum(scores) / len(scores) if scores else 0
    top_issues = sorted(
        issue_counts.items(), key=lambda item: (-item[1], item[0]))[:10]
    return {
        "total_batched": total_batched,
        "total_violations": total_violations,
        "total_warnings": total_warnings,
        "total_issues": sum(issue_counts.values()),
        "avg_score": round(avg_score, 2),
        "total_scan_time_ms": round(total_scan_time, 2),
        "top_issues": top_issues,
        "issue_counts": issue_counts,
    }
def _ic_scan_payload(code_chunk: Any,
                     allow_indented_wrap: bool) -> tuple[Any, int, str]:
    if not isinstance(code_chunk, str):
        return None, 0, ""
    tree = _parse_chunk(code_chunk, "直接解析失败")
    if tree is not None:
        return tree, 0, code_chunk
    if not allow_indented_wrap:
        return None, 0, ""
    first_code_line = next((
        line for line in code_chunk.splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ), "")
    if not first_code_line[:1].isspace():
        return None, 0, ""
    indented = "\n".join(
        "    " + line for line in code_chunk.split("\n")
    )
    # 缩进块可能截断自 async 函数体（await/async with/async for）；同步包装
    # 对这些片段必然 SyntaxError，需再试 async 包装，否则整段按不可解析跳过，
    # 块内安全/坏味道发现全部漏报。
    for wrapper in ("def _chk():\n", "async def _chk():\n"):
        wrapped = wrapper + indented
        tree = _parse_chunk(wrapped, "包装解析仍失败,跳过该段")
        if tree is not None:
            return tree, 1, wrapped
    return None, 0, ""
def _ic_finding_entry(item: dict, line_offset: int,
                      source_line_offset: int) -> dict:
    _rid = str(item.get("rule_id") or "")
    return {
        "rule": _rid, "rule_id": _rid,
        "line": (_ic_adj_line(item.get("line") or 0, line_offset)
                 + source_line_offset),
        "msg": item.get("message") or "",
        "severity": item.get("severity") or "",
    }
def _ic_ast_security_scan(tree: Any, result: dict,
                          line_offset: int,
                          source: str,
                          source_line_offset: int) -> None:
    violations, warnings = scan_source(source, tree)
    for item in violations:
        result["violations"].append(
            _ic_finding_entry(item, line_offset, source_line_offset))
    for item in warnings:
        result["warnings"].append(
            _ic_finding_entry(item, line_offset, source_line_offset))
def _ic_size_quality_check(full_code_accumulated: str, result: dict,
                           file_path: str) -> None:
    if not isinstance(full_code_accumulated, str) or not full_code_accumulated:
        return
    if count_lines(full_code_accumulated) < _IC_SIZE_WARN_LINES:
        return
    _ic_size_gate_warn(full_code_accumulated, result, file_path)
    _ic_quality_sample(full_code_accumulated, result)
def _ic_size_gate_warn(full_code_accumulated: str, result: dict,
                       file_path: str) -> None:
    try:
        sg = get_size_guard()
        size_report = sg.check(
            full_code_accumulated, file_path=file_path,
            task_type=DEFAULT_TASK_TYPE)
    except Exception as _e:  # noqa: BLE001
        _log.debug("[incremental] 体积检查失败(不阻断): %s", _e)
        return
    if size_report is None:
        return
    gate_value = _size_gate_value(size_report)
    if gate_value in ("WARN", "BLOCK"):
        sr_total = getattr(size_report, "total_lines", 0)
        result["warnings"].append({
            "rule": "SZ-INCR", "rule_id": "SZ-INCR",
            "line": 0,
            "msg": f"累计代码量已达 {sr_total} 行: "
                   f"{getattr(size_report, 'summary', '')}",
            "severity": ("CRITICAL" if gate_value == "BLOCK"
                         else "HIGH"),
        })
        result["size_report"] = _size_report_payload(size_report, gate_value)
def _ic_quality_sample(full_code_accumulated: str, result: dict) -> None:
    try:
        qs = CodeQualityScorer()
        qs_stats = qs.score(full_code_accumulated)
        if qs_stats:
            result["quality"] = qs_stats
    except Exception as _e:  # noqa: BLE001
        _log.debug("[incremental] 累计质量评分失败(不阻断): %s", _e)
def _ic_smell_detect(code_chunk: str, result: dict, tree: ast.AST,
                     line_offset: int, source_line_offset: int) -> None:
    try:
        sd = SmellDetectorV3()
        findings = sd.detect_all(code_chunk, tree=tree)
        for f in findings:
            if f.rule_id in WHOLE_FILE_ONLY_SMELL_RULES:
                continue
            raw_line = getattr(f, "line", 0) or 0
            if raw_line <= line_offset:
                continue
            result["warnings"].append({
                "rule": f.rule_id, "rule_id": f.rule_id,
                "line": _ic_adj_line(raw_line, line_offset) + source_line_offset,
                "msg": f.message,
                "severity": _severity_text(getattr(f, "severity", None)),
            })
    except Exception as _e:  # noqa: BLE001
        _log.warning("[incremental] 坏味道检测失败: %s", _e)
def _incremental_check(code_chunk: str, chunk_index: int = 0,
                       full_code_accumulated: str = "",
                       file_path: str = "",
                       source_line_offset: int = 0,
                       allow_indented_wrap: bool = True,
                       file_parseable: bool = True) -> dict:
    t0 = time.time()
    result: dict = {
        "ok": True, "parseable": True, "violations": [], "warnings": [],
        "quality": None, "size_report": None, "chunk_index": chunk_index,
    }
    tree, line_offset, scanned_source = _ic_scan_payload(
        code_chunk, allow_indented_wrap=allow_indented_wrap)
    if not file_parseable:
        result["parseable"] = False
    _ic_size_quality_check(full_code_accumulated, result, file_path)
    if tree is None:
        result["time_ms"] = round((time.time() - t0) * 1000, 2)
        result["parseable"] = False
        result["ok"] = False
        return result
    try:
        _ic_ast_security_scan(
            tree, result, line_offset, source=scanned_source,
            source_line_offset=source_line_offset)
    except Exception as _e:  # noqa: BLE001
        _log.warning("[incremental] 安全扫描失败，当前块按阻断处理: %s", _e)
        result["violations"].append({
            "rule": "CIE-INCR-SCAN-ERROR",
            "rule_id": "CIE-INCR-SCAN-ERROR",
            "line": 0,
            "msg": f"安全扫描失败({type(_e).__name__})，无法证明本块安全",
            "severity": "CRITICAL",
        })
    _ic_smell_detect(
        scanned_source, result, tree, line_offset, source_line_offset)
    result["ok"] = result["parseable"] and not result["violations"]
    result["time_ms"] = round((time.time() - t0) * 1000, 2)
    if result["violations"] or result["warnings"]:
        _log.info(
            "incremental_check: chunk=%d 发现问题: violations=%d, "
            "warnings=%d, ok=%s, %.1fms",
            chunk_index, len(result["violations"]),
            len(result["warnings"]), result["ok"], result["time_ms"],
        )
    else:
        _log.debug(
            "incremental_check: chunk=%d 干净, %.1fms",
            chunk_index, result["time_ms"],
        )
    return result
def _cie_target_files(skill_dir: str, ctx=None) -> list[str]:
    return [
        os.path.join(skill_dir, rel)
        for rel in collect_py_files(skill_dir, ctx)
        if not is_test_file_path(rel)
    ]
def run_cie_batch_verify(skill_dir: str, ctx=None) -> dict | None:
    targets = _cie_target_files(skill_dir, ctx)
    if not targets:
        return None
    engine = CodeInjectionEngine()
    batch = _batch_verify(engine, targets)
    return {
        **_batch_stats(batch),
        "files": {
            os.path.relpath(fp, skill_dir).replace("\\", "/"): {
                "passed": vr.passed,
                "score": vr.score,
                "violations": len(vr.violations),
                "warnings": len(vr.warnings),
            }
            for fp, vr in batch.items()
        },
    }
def _physical_lines(file_src: str) -> list[str]:
    lines = file_src.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines
def _logical_chunk_ranges(file_lines: list[str],
                          chunk_lines: int,
                          tree: ast.AST | None = None) -> list[tuple[int, int]]:
    if chunk_lines <= 0:
        raise ValueError("chunk_lines 必须为正整数")
    total_lines = len(file_lines)
    if tree is None:
        tree = _parse_chunk(
            "\n".join(file_lines), "文件级分块解析失败，回退物理分块")
    if tree is None:
        return [
            (offset + 1, min(offset + chunk_lines, total_lines))
            for offset in range(0, total_lines, chunk_lines)
        ]
    ranges: list[tuple[int, int]] = []
    start = 1
    current_end: int | None = None
    for node in tree.body:
        end = int(getattr(node, "end_lineno", None)
                  or getattr(node, "lineno", 0) or 0)
        if end < start:
            continue
        if current_end is not None and end - start + 1 > chunk_lines:
            ranges.append((start, current_end))
            start = current_end + 1
            current_end = None
        current_end = end
        if end - start + 1 >= chunk_lines:
            ranges.append((start, end))
            start = end + 1
            current_end = None
    if current_end is not None:
        if total_lines - start + 1 <= chunk_lines:
            ranges.append((start, total_lines))
            start = total_lines + 1
        else:
            ranges.append((start, current_end))
            start = current_end + 1
    for offset in range(start - 1, total_lines, chunk_lines):
        ranges.append((offset + 1, min(offset + chunk_lines, total_lines)))
    return ranges
def _scan_file_chunks(file_src: str, chunk_lines: int,
                      rule_counts: dict, file_path: str = "") -> dict:
    file_lines = _physical_lines(file_src)
    file_tree = _parse_chunk(
        file_src, "文件级分块解析失败，回退物理分块")
    stats = {
        "lines": len(file_lines),
        "chunks": 0,
        "chunks_unparseable": 0,
        "chunks_flagged": 0,
        "violations": 0,
        "warnings": 0,
        "size_report": None,
        "quality": None,
    }
    for start_line, end_line in _logical_chunk_ranges(
            file_lines, chunk_lines, tree=file_tree):
        source_line_offset = start_line - 1
        chunk = "\n".join(file_lines[source_line_offset:end_line])
        is_last_chunk = end_line >= len(file_lines)
        is_whole_file_chunk = start_line == 1 and is_last_chunk
        res = _incremental_check(
            chunk,
            chunk_index=stats["chunks"],
            full_code_accumulated=file_src if is_last_chunk else "",
            file_path=file_path,
            source_line_offset=source_line_offset,
            allow_indented_wrap=not is_whole_file_chunk,
            file_parseable=file_tree is not None,
        )
        stats["chunks"] += 1
        if not res.get("parseable", True):
            stats["chunks_unparseable"] += 1
        vs = res.get("violations") or []
        ws = res.get("warnings") or []
        if vs or ws:
            stats["chunks_flagged"] += 1
        stats["violations"] += len(vs)
        stats["warnings"] += len(ws)
        if res.get("size_report") is not None:
            stats["size_report"] = res["size_report"]
        if res.get("quality") is not None:
            stats["quality"] = res["quality"]
        for item in vs + ws:
            rid = (_normalize_issue_id(
                item.get("rule_id") or item.get("rule"))
                if isinstance(item, Mapping) else "UNKNOWN")
            rule_counts[rid] = rule_counts.get(rid, 0) + 1
    return stats
def run_cie_incremental_check(skill_dir: str, ctx=None) -> dict | None:
    sized = []
    for fp in _cie_target_files(skill_dir, ctx):
        src = read_source(fp, ctx)
        if src:
            sized.append((fp, src))
    if not sized:
        return None
    sized.sort(key=lambda kv: -len(kv[1].split("\n")))
    incr = {
        "files_checked": 0,
        "chunks_total": 0,
        "chunks_unparseable": 0,
        "chunks_flagged": 0,
        "violations": 0,
        "warnings": 0,
        "files": {},
    }
    rule_counts: dict = {}
    for fp, file_src in sized[:_INCR_MAX_FILES]:
        stats = _scan_file_chunks(
            file_src, _INCR_CHUNK_LINES, rule_counts, file_path=fp)
        incr["files_checked"] += 1
        incr["chunks_total"] += stats["chunks"]
        incr["chunks_unparseable"] += stats["chunks_unparseable"]
        incr["chunks_flagged"] += stats["chunks_flagged"]
        incr["violations"] += stats["violations"]
        incr["warnings"] += stats["warnings"]
        incr["files"][os.path.relpath(fp, skill_dir).replace("\\", "/")] = {
            "lines": stats["lines"],
            "chunks": stats["chunks"],
            "chunks_unparseable": stats["chunks_unparseable"],
            "chunks_flagged": stats["chunks_flagged"],
            "violations": stats["violations"],
            "warnings": stats["warnings"],
            "size_report": stats["size_report"],
            "quality": stats["quality"],
        }
    incr["rule_counts"] = rule_counts
    incr["top_rules"] = sorted(
        rule_counts.items(), key=lambda item: (-item[1], item[0]))[:10]
    return incr
def _record_cie_degradation(report: dict, step: str, label: str,
                            err: BaseException) -> None:
    _log.warning("%s: %s", label, err)
    report["errors"] = normalize_list_field(report.get("errors"))
    report["errors"].append({"step": step, "error": str(err)})
def _apply_cie_section(report: dict, step: str, label: str, key: str,
                       producer: Callable[[], Any],
                       keep: Callable[[Any], bool] | None = None) -> None:
    try:
        result = producer()
    except Exception as err:  # noqa: BLE001
        log_swallowed(__name__, err, context=step)
        _record_cie_degradation(report, step, label, err)
        return
    if keep is not None and not keep(result):
        return
    report[key] = result
def supplement_cie_sections(report: dict, skill_dir: str, ctx=None) -> None:
    _apply_cie_section(
        report, "cie_batch_verify", "[Step10] CIE 批量验证失败",
        "cie_batch_verify", lambda: run_cie_batch_verify(skill_dir, ctx),
        keep=lambda result: result is not None)
    _apply_cie_section(
        report, "cie_incremental_check", "[Step11] CIE 增量流式检查失败",
        "cie_incremental_check",
        lambda: run_cie_incremental_check(skill_dir, ctx),
        keep=lambda result: isinstance(result, dict)
        and bool(result.get("files_checked")))
_STRONG_FILE_CAP = min(t[0] for t in ROLE_HARD_THRESHOLDS.values())
_STRONG_FUNC_CAP = min(t[1] for t in ROLE_HARD_THRESHOLDS.values())
_STRONG_CLASS_CAPS = sorted({t[2] for t in ROLE_HARD_THRESHOLDS.values()})
_STRONG_CLASS_CAP = (
    f"{_STRONG_CLASS_CAPS[0]}~{_STRONG_CLASS_CAPS[-1]}"
    f"（按角色分级，最严 {_STRONG_CLASS_CAPS[0]}）"
    if len(_STRONG_CLASS_CAPS) > 1 else f"{_STRONG_CLASS_CAPS[0]}")
_STRONG_CONSTRAINT_TEMPLATE = """## 代码体积强制约束（违反将导致代码被拒绝）

你即将编写的代码必须遵守以下硬性限制，这不是建议，是必须遵守的规则：

| 规则 | 硬限制 | 说明 |
|------|--------|------|
| 文件行数 | ≤ {file_cap} 行 | 超出时收敛职责：简化逻辑、消除重复、迁出无关块 |
| 函数行数 | ≤ {func_cap} 行 | 超过此值的函数必须提取子函数 |
| 类方法行数 | ≤ {func_cap} 行 | 类方法必须短小精悍 |
| 类行数 | ≤ {class_cap} 行 | 大类须收敛职责或提取同模块私有实现 |
| 嵌套深度 | ≤ {nesting} 层 | 必须用卫语句或提取函数扁平化 |
| 参数数量 | ≤ {params} 个 | 必须封装为数据类或参数对象 |

本次任务预算：{advice}

如果预估代码量会超出限制：
1. 在开始编写前给出规模收敛方案（简化逻辑/消除重复/迁出无关职责）
2. 把无关职责迁到既有职责模块，避免为了压行数而制造新的转发层
3. 用清晰的职责描述组织代码，规模控制在预算范围内

违反规则的代码将在生成后被体积守卫拒绝，需要重新编写。{policy}"""
def _definition_span(node: Any) -> int:
    end = getattr(node, "end_lineno", None) or getattr(node, "lineno", 0) or 0
    return max(0, int(end) - definition_start_line(node) + 1)
def _function_size_violations(node: ast.AST, hard_func: int, location: str,
                              kind: str) -> list[SizeViolation]:
    label = "方法" if kind == "method" else "函数"
    violations: list[SizeViolation] = []
    span = own_scope_line_span(node)
    if span > hard_func:
        violations.append(SizeViolation(
            type=f"{kind}_too_long", severity="HIGH", location=location,
            value=span, threshold=hard_func,
            message=f"{label} '{location}' {span} 行,超过限制 {hard_func} 行",
            suggestion=(f"提取 '{node.name}' 中的子逻辑为私有辅助方法"
                        if kind == "method"
                        else f"拆分 '{node.name}' 为多个子函数"),
        ))
    depth = calc_nesting(node)
    if depth > HARD_MAX_NESTING:
        violations.append(SizeViolation(
            type="too_deep_nesting", severity="HIGH", location=location,
            value=depth, threshold=HARD_MAX_NESTING,
            message=f"{label} '{location}' 嵌套深度 {depth},超过限制 {HARD_MAX_NESTING} 层",
            suggestion="使用卫语句(early return/continue)减少嵌套",
        ))
    params = count_params(node, is_method=(kind == "method"))
    if params > HARD_MAX_PARAMS:
        violations.append(SizeViolation(
            type=RULE_TOO_MANY_PARAMS, severity="MEDIUM", location=location,
            value=params, threshold=HARD_MAX_PARAMS,
            message=f"{label} '{location}' 有 {params} 个参数,超过限制 {HARD_MAX_PARAMS}",
            suggestion="封装参数为 dataclass 或参数对象",
        ))
    return violations
@dataclass
class SizeReport:
    passed: bool
    gate: SizeGateStatus
    total_lines: int
    func_count: int
    class_count: int
    violations: list[SizeViolation] = field(default_factory=list)
    budget_advice: str = ""
    summary: str = ""
    def to_dict(self) -> dict[str, Any]:
        return {
            "passed": self.passed,
            "gate": self.gate.value,
            "total_lines": self.total_lines,
            "func_count": self.func_count,
            "class_count": self.class_count,
            "violations": [v.to_dict() for v in self.violations],
            "budget_advice": self.budget_advice,
            "summary": self.summary,
        }
class SizeGuard:
    def __init__(self, strict: bool = True, policy: str = "") -> None:
        self.strict = strict
        self.policy = policy.strip()
    def _policy_block(self, policy: str | None = None) -> str:
        text = self.policy if policy is None else str(policy).strip()
        return f"\n\n项目治理约束：{text}" if text else ""
    def format_strong_constraint(self, task_type: str = DEFAULT_TASK_TYPE,
                                 policy: str | None = None) -> str:
        budget = self.get_budget(task_type)
        return _STRONG_CONSTRAINT_TEMPLATE.format(
            file_cap=_STRONG_FILE_CAP,
            func_cap=_STRONG_FUNC_CAP,
            class_cap=_STRONG_CLASS_CAP,
            nesting=HARD_MAX_NESTING,
            params=HARD_MAX_PARAMS,
            advice=budget["advice"],
            policy=self._policy_block(policy),
        )
    def check(self, code: str, file_path: str = "", task_type: str = DEFAULT_TASK_TYPE, file_role: FileRole | None = None, tree=None) -> SizeReport:
        file_path = normalize_filepath(file_path)
        code = coerce_source_text(code)
        if code is None:
            return self._blocked_report(0)
        if file_role is None:
            file_role = classify_file_role(file_path)
        hard_file, hard_func, hard_class = get_role_thresholds(file_role)
        total_lines = count_lines(code)
        violations = self._check_file_length(total_lines, file_path, hard_file)
        try:
            if not isinstance(tree, ast.AST):
                tree = parse_cached_source(code)
            compile(tree, file_path or "<size-guard>", "exec")
        except (SyntaxError, ValueError, TypeError, RecursionError, MemoryError):
            _log.warning(MSG_SYNTAX_ERROR_SKIP)
            return self._blocked_report(total_lines, violations)
        cls_v, class_count = self._checkast_classes(tree, hard_class)
        violations.extend(cls_v)
        fn_v, func_count = self._checkast_functions(tree, hard_func)
        violations.extend(fn_v)
        gate = self._decide_gate(violations)
        return self._build_size_report(violations, total_lines, func_count, class_count, gate, task_type)
    def _blocked_report(
        self, total_lines: int,
        violations: list[SizeViolation] | None = None,
    ) -> SizeReport:
        return SizeReport(
            passed=False,
            gate=(SizeGateStatus.BLOCK if self.strict
                  else SizeGateStatus.WARN),
            total_lines=total_lines,
            func_count=0,
            class_count=0,
            violations=list(violations or ()),
            summary="语法错误，无法分析",
        )
    def _check_file_length(self, total_lines: int, file_path: str, hard_file: int) -> list[SizeViolation]:
        if total_lines <= hard_file:
            return []
        return [SizeViolation(
            type="file_too_long", severity="CRITICAL",
            location=file_path or "(代码片段)",
            value=total_lines, threshold=hard_file,
            message=f"文件 {total_lines} 行,超过硬限制 {hard_file} 行",
            suggestion=("简化逻辑/消除重复/迁出无关块，"
                         f"规模收敛到 ≤ {hard_file} 行")
        )]
    @staticmethod
    def _iter_own_methods(cls_node: ast.ClassDef) -> Iterator[ast.FunctionDef | ast.AsyncFunctionDef]:
        return (
            item for item in iter_own_scope(
                cls_node, skip_lambda=True, include_self=False)
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
        )
    def _checkast_classes(self, tree: ast.AST, hard_class: int) -> tuple[list[SizeViolation], int]:
        violations = []
        class_count = 0
        for node in walk_nodes(tree):
            if not isinstance(node, ast.ClassDef):
                continue
            class_count += 1
            cls_lines = _definition_span(node)
            if cls_lines <= hard_class:
                continue
            violations.append(SizeViolation(
                type="class_too_long", severity="HIGH",
                location=node.name, value=cls_lines,
                threshold=hard_class,
                message=f"类 '{node.name}' {cls_lines} 行,超过限制 {hard_class} 行",
                suggestion=(f"收敛类 '{node.name}' 职责：提取同模块"
                            f"私有实现或迁出无关方法")
            ))
        return violations, class_count
    @classmethod
    def _method_class_names(cls, tree: ast.AST) -> dict[int, str]:
        names: dict[int, str] = {}
        for node in walk_nodes(tree):
            if not isinstance(node, ast.ClassDef):
                continue
            for method in cls._iter_own_methods(node):
                names[id(method)] = node.name
        return names
    def _checkast_functions(self, tree: ast.AST,
                            hard_func: int) -> tuple[list[SizeViolation], int]:
        violations = []
        func_count = 0
        method_classes = self._method_class_names(tree)
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            func_count += 1
            class_name = method_classes.get(id(node))
            if class_name:
                violations.extend(_function_size_violations(
                    node, hard_func, f"{class_name}.{node.name}", "method"))
            else:
                violations.extend(_function_size_violations(
                    node, hard_func, node.name, "function"))
        return violations, func_count
    def _decide_gate(self, violations: list[SizeViolation]) -> SizeGateStatus:
        if not violations:
            return SizeGateStatus.PASS
        if self.strict and any(
                v.severity in ("CRITICAL", "HIGH") for v in violations):
            return SizeGateStatus.BLOCK
        return SizeGateStatus.WARN
    def _build_size_report(self, violations: list[SizeViolation], total_lines: int, func_count: int, class_count: int, gate: SizeGateStatus, task_type: str) -> SizeReport:
        return SizeReport(
            passed=(gate == SizeGateStatus.PASS),
            gate=gate,
            total_lines=total_lines,
            func_count=func_count,
            class_count=class_count,
            violations=violations,
            budget_advice=self.get_budget(task_type).get("advice", ""),
            summary=f"{total_lines} lines, {func_count} funcs, {class_count} classes",
        )
    def get_budget(self, task_type: str = DEFAULT_TASK_TYPE) -> dict[str, Any]:
        key = coerce_task_type(task_type, DEFAULT_TASK_TYPE)
        return dict(TASK_BUDGETS.get(key) or TASK_BUDGETS[DEFAULT_TASK_TYPE])
_instance = SizeGuard()
def get_size_guard() -> SizeGuard:
    return _instance
def _size_violation_text(violation: Any) -> str:
    if isinstance(violation, str):
        return violation
    if isinstance(violation, dict):
        return str(violation.get("message") or violation.get("description")
                   or violation)
    return str(getattr(violation, "message", "") or violation)
def size_gate_issues(code: Any, tree: Any = None,
                     exclude_rules: Any = None, filepath: str = "") -> list:
    if exclude_rules and "SZ-01" in exclude_rules:
        return []
    sz_report = get_size_guard().check(code, file_path=filepath, tree=tree)
    if not (hasattr(sz_report, "violations") and sz_report.violations):
        return []
    return [
        {
            "rule_id": "SZ-01",
            "file": filepath or "",
            "line": 0,
            "message": _size_violation_text(v),
            "severity": "P3",
            "category": "size",
        }
        for v in sz_report.violations
    ]
def _coerce_quota_max(value: Any) -> int:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return DEFAULT_SESSION_QUOTA["max_total_lines"]
    if isinstance(value, float) and not math.isfinite(value):
        return DEFAULT_SESSION_QUOTA["max_total_lines"]
    return max(0, int(value))
class BudgetDecision(Enum):
    WITHIN_BUDGET = "within_budget"
    NEAR_BUDGET = "near_budget"
    OVER_BUDGET = "over_budget"
    SESSION_QUOTA_EXCEEDED = "session_quota_exceeded"
    INVALID_SOURCE = "invalid_source"
@dataclass
class EntityBudget:
    entity_type: str = ""
    entity_name: str = ""
    start_line: int = 0
    end_line: int = 0
    total_lines: int = 0
    budget_lines: int = 0
    usage_pct: float = 0.0
    over_budget: bool = False
    near_budget: bool = False
@dataclass
class SessionQuota:
    session_id: str = ""
    max_total_lines: int = DEFAULT_SESSION_QUOTA["max_total_lines"]
    total_lines_written: int = 0
    files_written: dict[str, int] | None = None
    def __post_init__(self) -> None:
        self.max_total_lines = _coerce_quota_max(self.max_total_lines)
        if not isinstance(self.files_written, Mapping):
            if self.files_written is not None:
                _log.debug("SessionQuota.files_written 非映射（%s），重置为空表",
                           type(self.files_written).__name__)
            self.files_written = {}
        else:
            self.files_written = dict(self.files_written)
    @property
    def exceeded(self) -> bool:
        return self.total_lines_written > self.max_total_lines
@dataclass
class BudgetReport:
    passed: bool = True
    decision: BudgetDecision = BudgetDecision.WITHIN_BUDGET
    filepath: str = ""
    file_role: FileRole | None = None
    total_lines: int = 0
    budget_file_lines: int = 0
    budget_factor: float = 1.0
    file_usage_pct: float = 0.0
    entities: list[EntityBudget] | None = None
    violations: list[EntityBudget] | None = None
    near_limit: list[EntityBudget] | None = None
    split_suggestions: list[dict] | None = None
    session_quota_used: int = 0
    session_quota_max: int = 0
    check_time_ms: float = 0.0
    summary: str = ""
    def __post_init__(self) -> None:
        for _name in ("entities", "violations", "near_limit", "split_suggestions"):
            _value = getattr(self, _name)
            if _value is None:
                setattr(self, _name, [])
            elif not isinstance(_value, list):
                _log.debug("BudgetReport.%s 非序列（%s），归一为空表",
                           _name, type(_value).__name__)
                setattr(self, _name,
                        list(_value)
                        if isinstance(_value, (tuple, set, frozenset)) else [])
    def format_summary(self) -> str:
        return (
            f"decision={self.decision.value} "
            f"lines={self.total_lines}/{self.budget_file_lines} "
            f"violations={len(self.violations)} "
            f"time={self.check_time_ms:.1f}ms"
        )
def _extract_functions(tree: ast.Module) -> list[EntityBudget]:
    entities: list[EntityBudget] = []
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            kind = "function"
        elif isinstance(node, ast.ClassDef):
            kind = "class"
        else:
            continue
        start_line = definition_start_line(node)
        end_line = int(getattr(node, "end_lineno", None) or start_line)
        total_lines = (own_scope_line_span(node) if kind == "function"
                       else _definition_span(node))
        entities.append(EntityBudget(
            entity_type=kind, entity_name=node.name,
            start_line=start_line, end_line=end_line,
            total_lines=total_lines,
        ))
    return entities
def _generate_split_suggestions(violations: list[EntityBudget]) -> list[dict]:
    suggestions = []
    for v in violations:
        action = ("extract_private_impl" if v.entity_type in ("function", "class")
                  else "migrate_code")
        suggestions.append({
            "entity": v.entity_name,
            "entity_type": v.entity_type,
            "lines": v.total_lines,
            "budget": v.budget_lines,
            "action": action,
        })
    return suggestions
def _paren_delta(code_part: str) -> int:
    return (code_part.count("(") + code_part.count("[")
            - code_part.count(")") - code_part.count("]"))
def _detect_imports_end_line(code: str) -> int:
    try:
        tree = parse_cached_source(code)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as _e:
        log_swallowed(__name__, _e, context='_detect_imports_end_line:SyntaxError')
        return _detect_imports_end_line_scan(code)
    end = 0
    for node in _module_body_after_docstring(tree):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            break
        end = int(node.end_lineno or 0)
    return end
def _module_body_after_docstring(tree: ast.Module) -> list[ast.stmt]:
    body = tree.body
    if not body:
        return body
    first = body[0]
    is_doc = (isinstance(first, ast.Expr)
              and isinstance(first.value, ast.Constant)
              and isinstance(first.value.value, str))
    return body[1:] if is_doc else body
def _detect_imports_end_line_scan(code: str) -> int:
    lines = code.split("\n")
    last_import_line = 0
    paren_depth = 0
    continued = False
    for i, line in enumerate(lines, 1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            if paren_depth > 0 or continued:
                last_import_line = i
            continue
        code_part = stripped.split("#", 1)[0].rstrip()
        if paren_depth > 0 or continued:
            last_import_line = i
            paren_depth += _paren_delta(code_part)
            continued = code_part.endswith("\\")
            continue
        if not stripped.startswith(("import ", "from ")):
            break
        last_import_line = i
        paren_depth += _paren_delta(code_part)
        continued = code_part.endswith("\\")
    return max(0, last_import_line)
def _top_level_spans(report: BudgetReport, lines: list[str],
                     imports_end: int) -> list[tuple[int, int]]:
    try:
        tree = parse_cached_source("\n".join(lines))
        return sorted({
            (definition_start_line(n), n.end_lineno)
            for n in tree.body
            if (n.end_lineno or n.lineno) > imports_end
        })
    except (SyntaxError, ValueError, RecursionError, MemoryError) as _e:
        log_swallowed(__name__, _e, context='_top_level_spans:SyntaxError')
        return sorted({
            (ent.start_line, ent.end_line) for ent in report.entities
            if ent.end_line > imports_end
        })
@dataclass
class _CheckFacts:
    t0: float
    filepath: str
    role: FileRole
    total_lines: int
    file_budget: int
    budget_factor: float
    decision: BudgetDecision
    passed: bool
    file_usage_pct: float = 0.0
    entities: list[EntityBudget] = field(default_factory=list)
    violations: list[EntityBudget] = field(default_factory=list)
    near_limit: list[EntityBudget] = field(default_factory=list)
def _auto_split_payload(action: str, report: BudgetReport, *,
                        strategy: str, filepath: str,
                        total_lines: int = 0, import_block: str = "",
                        split_plan: list[dict] | None = None) -> dict[str, Any]:
    return {
        "action": action,
        "report": report,
        "strategy": strategy,
        "filepath": filepath,
        "total_lines": total_lines,
        "import_block": import_block,
        "split_plan": list(split_plan or ()),
    }
class SourceBudgetGuard:
    def __init__(self, strict: bool = True, task_type: str = DEFAULT_TASK_TYPE,
                 session_quota_max: int | None = None) -> None:
        self.strict = strict
        self.task_type = coerce_task_type(task_type, DEFAULT_TASK_TYPE)
        self.budget_factor = TASK_BUDGET_FACTOR.get(self.task_type, 1.0)
        self._session_quota = self._new_session_quota(session_quota_max)
        self._check_count = 0
        self._block_count = 0
        self._lock = RLock()
    @staticmethod
    def _new_session_quota(max_total_lines: int | None) -> SessionQuota:
        return SessionQuota(
            session_id=hashlib.md5(str(time.time()).encode(), usedforsecurity=False).hexdigest()[:8],
            max_total_lines=max_total_lines,
        )
    def check(self, code: str, filepath: str = "",
              context: dict[str, Any] | None = None) -> BudgetReport:
        t0 = time.perf_counter()
        filepath = normalize_filepath(filepath)
        role, file_budget, func_budget, class_budget, factor = self._resolve_budget(filepath, context)
        tree, entities, total_lines = self._extract_entities(code)
        violations, near_limit = (
            self._evaluate_entities(entities, func_budget, class_budget)
            if tree is not None else ([], [])
        )
        file_usage_pct, file_over_budget = self._check_file_budget(total_lines, file_budget)
        if file_over_budget:
            violations.append(self._make_file_entity(filepath, total_lines, file_budget, file_usage_pct))
        elif file_usage_pct >= NEAR_BUDGET_RATIO:
            near_limit.append(self._make_file_entity(
                filepath, total_lines, file_budget, file_usage_pct, over_budget=False))
        if tree is None:
            decision, passed = BudgetDecision.INVALID_SOURCE, False
        else:
            decision, passed = self._make_decision(violations, near_limit)
        return self._build_budget_report(_CheckFacts(
            t0=t0, filepath=filepath, role=role, total_lines=total_lines,
            file_budget=file_budget, budget_factor=factor,
            file_usage_pct=file_usage_pct, entities=entities,
            violations=violations, near_limit=near_limit,
            decision=decision, passed=passed,
        ), summary="" if tree is not None else "syntax error, skipped")
    def _effective_task_type(self, context: dict[str, Any] | None) -> str:
        raw_task_type = (context.get("task_type", self.task_type)
                         if isinstance(context, dict) else self.task_type)
        return coerce_task_type(raw_task_type, self.task_type)
    def _resolve_budget(self, filepath: str, context: dict[str, Any] | None) -> tuple[FileRole, int, int, int, float]:
        factor = TASK_BUDGET_FACTOR.get(self._effective_task_type(context), 1.0)
        role = classify_file_role(filepath)
        file_b, func_b, class_b = get_role_thresholds(role)
        return (role, round(file_b * factor), round(func_b * factor),
                round(class_b * factor), factor)
    def _extract_entities(self, code: str) -> tuple[ast.Module | None, list[EntityBudget], int]:
        code = coerce_source_text(code)
        if code is None:
            return None, [], 0
        try:
            tree = parse_cached_source(code)
        except (SyntaxError, ValueError, RecursionError, MemoryError):
            _log.warning(MSG_SYNTAX_ERROR_SKIP)
            return None, [], count_lines(code)
        entities = _extract_functions(tree)
        return tree, entities, count_lines(code)
    def _evaluate_entities(self, entities: list[EntityBudget], func_budget: int, class_budget: int) -> tuple[list[EntityBudget], list[EntityBudget]]:
        violations: list[EntityBudget] = []
        near_limit: list[EntityBudget] = []
        for entity in entities:
            entity.budget_lines = (
                class_budget if entity.entity_type == "class" else func_budget)
            if entity.budget_lines > 0:
                entity.usage_pct = entity.total_lines / entity.budget_lines
            entity.over_budget = entity.total_lines > entity.budget_lines
            entity.near_budget = not entity.over_budget and entity.usage_pct >= NEAR_BUDGET_RATIO
            if entity.over_budget:
                violations.append(entity)
            elif entity.near_budget:
                near_limit.append(entity)
        return violations, near_limit
    def _check_file_budget(self, total_lines: int, file_budget: int) -> tuple[float, bool]:
        usage = total_lines / file_budget if file_budget > 0 else 0.0
        return usage, total_lines > file_budget
    def _make_file_entity(self, filepath: str, total_lines: int,
                          file_budget: int, usage_pct: float,
                          over_budget: bool = True) -> EntityBudget:
        return EntityBudget(
            entity_type="file", entity_name=filepath or "<code>",
            start_line=0, end_line=total_lines, total_lines=total_lines,
            budget_lines=file_budget, usage_pct=usage_pct, over_budget=over_budget,
            near_budget=not over_budget,
        )
    def _make_decision(self, violations: list[EntityBudget],
                       near_limit: list[EntityBudget]) -> tuple[BudgetDecision, bool]:
        if self._session_quota.exceeded:
            return BudgetDecision.SESSION_QUOTA_EXCEEDED, False
        if violations:
            return BudgetDecision.OVER_BUDGET, not self.strict
        if near_limit:
            return BudgetDecision.NEAR_BUDGET, True
        return BudgetDecision.WITHIN_BUDGET, True
    def _account_check(self, passed: bool) -> None:
        self._check_count += 1
        if not passed:
            self._block_count += 1
    def _build_budget_report(self, facts: _CheckFacts,
                             summary: str = "") -> BudgetReport:
        split_suggestions: list[dict] = []
        if facts.violations:
            split_suggestions = _generate_split_suggestions(facts.violations)
        report = BudgetReport(
            passed=facts.passed, decision=facts.decision, filepath=facts.filepath,
            file_role=facts.role, total_lines=facts.total_lines,
            budget_file_lines=facts.file_budget,
            budget_factor=facts.budget_factor,
            file_usage_pct=facts.file_usage_pct, entities=facts.entities,
            violations=facts.violations, near_limit=facts.near_limit,
            split_suggestions=split_suggestions,
            session_quota_used=self._session_quota.total_lines_written,
            session_quota_max=self._session_quota.max_total_lines,
            check_time_ms=(time.perf_counter() - facts.t0) * 1000, summary="",
        )
        report.summary = summary or report.format_summary()
        self._account_check(facts.passed)
        _log.info(
            "[BudgetGuard] %s role=%s decision=%s lines=%d/%d violations=%d time=%.1fms",
            facts.filepath or "<code>", facts.role.value, facts.decision.value,
            facts.total_lines, facts.file_budget, len(facts.violations),
            report.check_time_ms,
        )
        return report
    def record_write(self, filepath: str, lines: int) -> None:
        if isinstance(lines, bool) or not isinstance(lines, int):
            raise TypeError("lines 必须为非负整数")
        if lines < 0:
            raise ValueError("lines 必须为非负整数")
        filepath = normalize_filepath(filepath)
        with self._lock:
            self._session_quota.total_lines_written += lines
            self._session_quota.files_written[filepath] = (
                self._session_quota.files_written.get(filepath, 0) + lines
            )
    def get_session_quota(self) -> SessionQuota:
        return self._session_quota
    def reset_session_quota(self, new_max: int | None = None) -> None:
        with self._lock:
            self._session_quota = self._new_session_quota(new_max)
    def trigger_auto_split(self, code: str, filepath: str, strategy: str = "auto",
                           context: dict[str, Any] | None = None) -> dict[str, Any]:
        coerced = coerce_source_text(code)
        if coerced is None:
            return _auto_split_payload(
                "no_split_needed", self.check(code, filepath, context=context),
                strategy=strategy, filepath=normalize_filepath(filepath))
        code = coerced
        filepath = normalize_filepath(filepath)
        report = self.check(code, filepath, context=context)
        if not report.violations:
            return _auto_split_payload(
                "no_split_needed", report, strategy=strategy,
                filepath=filepath, total_lines=report.total_lines)
        lines = code.split("\n")
        total_lines = count_lines(code)
        imports_end = _detect_imports_end_line(code)
        import_block = "\n".join(lines[:imports_end])
        split_plan = self._build_split_plan(
            report, lines, filepath, imports_end, total_lines)
        action = "split_planned" if split_plan else "no_split_needed"
        return _auto_split_payload(
            action, report, strategy=strategy, filepath=filepath,
            total_lines=total_lines, import_block=import_block,
            split_plan=split_plan)
    def _build_split_plan(self, report: BudgetReport, lines: list[str], filepath: str,
                          imports_end: int, total_lines: int) -> list[dict]:
        split_plan: list[dict] = []
        top_spans = _top_level_spans(report, lines, imports_end)
        current_start = imports_end + 1
        if top_spans and top_spans[0][0] < current_start:
            current_start = top_spans[0][0]
        file_budget = report.budget_file_lines
        content_budget = file_budget - imports_end
        if content_budget <= 0 or total_lines <= file_budget:
            return []
        try:
            tree = parse_cached_source("\n".join(lines))
        except (SyntaxError, ValueError, RecursionError, MemoryError):
            return []
        if any(
                not isinstance(node, (ast.Import, ast.ImportFrom))
                and int(getattr(node, "lineno", 0) or 0) <= imports_end
                for node in _module_body_after_docstring(tree)):
            return []
        emit_chunk = _make_chunk_emitter(split_plan, filepath, report)
        if not top_spans:
            for _slice_start, _slice_end in _iter_budget_slices(
                    current_start, total_lines, content_budget):
                emit_chunk(_slice_start, _slice_end)
            return split_plan
        segs = _split_segments(top_spans, current_start, total_lines)
        if not _pack_segments_to_chunks(
                segs, total_lines, content_budget, emit_chunk):
            return []
        return split_plan
    def format_strong_constraint(self, filepath: str = "",
                                 context: dict[str, Any] | None = None) -> str:
        role, file_budget, func_budget, class_budget, factor = self._resolve_budget(filepath, context)
        lines = [
            f"[预算约束] 文件角色: {role.value}",
            f"  文件行数上限: {file_budget} 行（硬阻断）",
            f"  函数行数上限: {func_budget} 行（硬阻断）",
            f"  类行数上限: {class_budget} 行（硬阻断）",
        ]
        if factor < 1.0:
            lines.append(f"  任务类型收紧系数: {factor:.0%} ({self._effective_task_type(context)})")
        if self._session_quota.total_lines_written > 0:
            lines.append(f"  会话已使用: {self._session_quota.total_lines_written}/{self._session_quota.max_total_lines} 行")
        return "\n".join(lines)
    @property
    def stats(self) -> dict[str, Any]:
        return {"checks": self._check_count, "blocked": self._block_count}
def _split_segments(top_spans: list[tuple[int, int]], start: int,
                    total_lines: int) -> list[tuple[bool, int, int]]:
    segs: list[tuple[bool, int, int]] = []
    _prev = start
    for _s, _e in top_spans:
        if _s > _prev:
            segs.append((False, _prev, _s - 1))
        segs.append((True, _s, _e))
        _prev = _e + 1
    if _prev <= total_lines:
        segs.append((False, _prev, total_lines))
    return segs
def _iter_budget_slices(start: int, end: int, file_budget: int,
                        keep_tail: bool = True) -> Iterator[tuple[int, int]]:
    if file_budget <= 0:
        raise ValueError(f"file_budget 必须为正数（否则切片游标不前进）：{file_budget!r}")
    cursor = start
    while end - cursor + 1 > file_budget:
        yield cursor, cursor + file_budget - 1
        cursor += file_budget
    if keep_tail and cursor <= end:
        yield cursor, end
def _make_chunk_emitter(split_plan: list[dict], filepath: str,
                        report: BudgetReport) -> Any:
    chunk_index = 1
    _stem, _ext = os.path.splitext(str(filepath))
    def _emit_chunk(start: int, end: int) -> None:
        nonlocal chunk_index
        split_plan.append({
            "target_file": f"{_stem}_{chunk_index}{_ext or '.py'}",
            "start_line": start,
            "end_line": end,
            "estimated_lines": end - start + 1,
            "entities": [e.entity_name for e in report.entities
                         if start <= e.start_line <= end],
        })
        chunk_index += 1
    return _emit_chunk
def _pack_segments_to_chunks(segs: list[tuple[bool, int, int]],
                             total_lines: int, file_budget: int,
                             emit_chunk) -> bool:
    current_start = segs[0][1]
    for _is_entity, _s, _e in segs:
        if _is_entity and _e - _s + 1 > file_budget:
            return False
        if _e - current_start + 1 <= file_budget:
            continue
        if current_start < _s:
            emit_chunk(current_start, _s - 1)
            current_start = _s
        if _is_entity:
            continue
        for _slice_start, _slice_end in _iter_budget_slices(
                current_start, _e, file_budget, keep_tail=False):
            emit_chunk(_slice_start, _slice_end)
            current_start = _slice_end + 1
    if total_lines - current_start + 1 > file_budget:
        return False
    emit_chunk(current_start, total_lines)
    return True
_SESSION_BUDGET_GUARD = SourceBudgetGuard(strict=True)
def record_session_write(filepath: str, code: str) -> BudgetReport:
    guard = _SESSION_BUDGET_GUARD
    with guard._lock:
        report = guard.check(code, filepath=filepath)
        passed_before_write = report.passed
        quota = guard.get_session_quota()
        projected_total = quota.total_lines_written + report.total_lines
        if projected_total > quota.max_total_lines:
            report.decision = BudgetDecision.SESSION_QUOTA_EXCEEDED
            report.passed = False
        elif report.passed:
            guard.record_write(filepath, report.total_lines)
        report.session_quota_used = quota.total_lines_written
        if passed_before_write and not report.passed:
            guard._block_count += 1
        report.summary = report.format_summary()
        return report
def get_session_budget_state() -> dict[str, Any]:
    guard = _SESSION_BUDGET_GUARD
    with guard._lock:
        quota = guard.get_session_quota()
        return {
            "session_id": quota.session_id,
            "used_lines": quota.total_lines_written,
            "max_total_lines": quota.max_total_lines,
            "exceeded": quota.exceeded,
            "files_written": dict(quota.files_written or {}),
        }

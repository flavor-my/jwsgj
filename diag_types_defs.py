from __future__ import annotations

import ast
import math
import os
import time
from collections.abc import Iterable
from dataclasses import asdict, dataclass, field, is_dataclass
from typing import Any, Self

from jwsgj.diag_types_normalize import (
    coerce_line_number,
    normalize_files_list,
    normalize_input,
    normalize_passed,
    normalize_target_path,
    safe_int,
    severity_literal_from_rank,
    severity_text_value,
    signal_bool,
    str_or,
    text_or_empty,
)
from jwsgj.diag_types_vocab import (
    DEFAULT_FINDING_CONFIDENCE,
    DIAGNOSE_TO_P,
    FIELD_CV_RULE_WEIGHTS,
    FIELD_METHOD_THRESHOLDS,
    FIELD_SUGGESTED_VALUE,
    FINDING_KEY_ALIASES,
    METHOD_DEGRADE_EXC,
    MSG_CONFIRM_SKILL_DIR,
    PARSE_DEGRADE_EXC,
    RESULT_STATUS_BUCKETS,
    SEVERITY_BLOCKING,
    SEVERITY_INFO,
    SEVERITY_RANK,
    DiagnoseSeverity,
    EntryDecision,
    GuardLevel,
    OperationType,
    Severity,
    VulnerabilityCategory,
    diag_severity_to_p,
    normalize_filepath,
)
from jwsgj.log_config import (
    get_module_logger,
    log_swallowed,
    safe_write_audit,
    write_audit,
)
from jwsgj.runtime_scope import is_test_file_path

logger = get_module_logger(__name__)
_FALSE_FLAG_TEXT = frozenset({"off", "n", "否"})
def _flag_bool(value: Any) -> bool:
    if isinstance(value, str) and value.strip().lower() in _FALSE_FLAG_TEXT:
        return False
    return signal_bool(value)
class ContractViolationError(Exception):
    def __init__(self, message: str = "") -> None:
        super().__init__(message)
        try:
            write_audit("contract_violation", message=message[:500])
        except Exception as _e:  # noqa: BLE001 — 审计写失败降级，不击穿契约异常
            log_swallowed(__name__, _e, context='ContractViolationError.write_audit')
class ConcurrentExecutionError(Exception):
    pass
@dataclass
class EntryResult:
    ok: bool
    decision: EntryDecision
    filepath: str
    code: str = ""
    gen_issues: list[dict] = field(default_factory=list)
    needs_split: bool = False
    split_plan: list[dict] = field(default_factory=list)
    diag_issues: list[dict] = field(default_factory=list)
    total_issues: int = 0
    block_count: int = 0
    warn_count: int = 0
    message: str = ""
    warnings: list[str] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    @classmethod
    def begin(cls, code: str, filepath: Any) -> Self:
        return cls(ok=True, decision=EntryDecision.ALLOW,
                   filepath=normalize_filepath(filepath), code=code)
    def record_blocked(self, msg: str, count: int = 1) -> None:
        self.errors.append(msg)
        self.block_count += count
    def degrade_gate(self, tag: str, label: str, engine: str,
                     exc: BaseException) -> None:
        subject = f"{engine} " if engine else f"{label}门禁"
        logger.warning("[GenEntryGuard] %s %s执行异常, 降级跳过: %s",
                       tag, subject, exc)
        self.warnings.append(f"[{tag}] {label}门禁执行异常已降级跳过: {exc}")
def diag_line(prefix: str, name: str, detail: str, line_num: int = 0) -> str:
    loc = f" (行{line_num})" if line_num else ""
    return f"{prefix} {name}: {detail}{loc}"
def diag_issue_entry(check_id: str, message: str, severity: str, line: int,
                     suggestion: str,
                     fix_example: str | None = None) -> dict:
    entry = {
        "check_id": check_id, "message": message,
        "severity": severity, "line": line,
        "suggestion": suggestion,
    }
    if fix_example is not None:
        entry["fix_example"] = fix_example
    return entry
DEFAULT_REGISTRY_BLOCK_SEVERITY = "P0"
DEFAULT_LOGIC_BLOCK_SEVERITY = "P1"
_SEVERITY_WORD_TO_P: dict[str, str] = {
    **{word: severity_literal_from_rank(rank)
       for word, rank in SEVERITY_RANK.items()},
    **DIAGNOSE_TO_P,
    SEVERITY_BLOCKING.upper(): "P0",
}
BLOCK_SEVERITY_CHOICES = frozenset(_SEVERITY_WORD_TO_P.values())
_DEFAULT_STRICT = True
_DEFAULT_ENABLE_REGISTRY_GATE = True
_DEFAULT_SKILL_DIR = ""
_DEFAULT_REGISTRY_EXCLUDE_IDS: set[str] | None = None
def severity_rank_of_text(value: Any) -> tuple[str, int | None]:
    token = severity_text_value(value) or ""
    if not token:
        return "", None
    p_level = _SEVERITY_WORD_TO_P.get(token)
    if p_level is None:
        return token, None
    return token, SEVERITY_RANK[p_level]
def _normalize_block_severity(value: Any, fallback: str,
                             param_name: str) -> str:
    _token, rank = severity_rank_of_text(value)
    if rank is not None:
        return severity_literal_from_rank(rank)
    _fb_token, fb_rank = severity_rank_of_text(fallback)
    sev = (severity_literal_from_rank(fb_rank) if fb_rank is not None
           else DEFAULT_LOGIC_BLOCK_SEVERITY)
    logger.warning(
        "[GenEntryGuard] %s=%r 非法（支持 P0-P4、CRITICAL/HIGH/MEDIUM/LOW/"
        "INFO/ERROR/WARN/BLOCK 与 blocking），回退默认 %s",
        param_name, value, sev,
    )
    return sev
def _normalize_exclude_ids(value: Any) -> set[str] | None:
    if value is None:
        return None
    if isinstance(value, str):
        return {value} if value else None
    try:
        return set(value)
    except TypeError:
        logger.warning(
            "[GenEntryGuard] registry_exclude_ids 不可迭代（%s），按不排除降级",
            type(value).__name__,
        )
        return None
def _normalize_skill_dir(skill_dir: Any) -> str:
    if not skill_dir:
        return ""
    path = normalize_filepath(skill_dir)
    if path.strip():
        return path
    label = ("空白路径" if isinstance(skill_dir, str)
             else "路径协议异常"
             if isinstance(skill_dir, (bytes, bytearray, os.PathLike))
             else "非 str/bytes/PathLike")
    logger.warning("[GenEntryGuard] skill_dir %s（%s），按空目录降级",
                   label, type(skill_dir).__name__)
    return ""
@dataclass(frozen=True)
class EntryGateConfig:
    strict: bool = _DEFAULT_STRICT
    enable_registry_gate: bool = _DEFAULT_ENABLE_REGISTRY_GATE
    skill_dir: str = _DEFAULT_SKILL_DIR
    registry_exclude_ids: set[str] | None = _DEFAULT_REGISTRY_EXCLUDE_IDS
    registry_block_severity: str = DEFAULT_REGISTRY_BLOCK_SEVERITY
    logic_block_severity: str = DEFAULT_LOGIC_BLOCK_SEVERITY
    @classmethod
    def build(cls, *, strict: Any = _DEFAULT_STRICT,
              enable_registry_gate: Any = _DEFAULT_ENABLE_REGISTRY_GATE,
              skill_dir: Any = _DEFAULT_SKILL_DIR,
              registry_exclude_ids: Any = _DEFAULT_REGISTRY_EXCLUDE_IDS,
              registry_block_severity: Any = DEFAULT_REGISTRY_BLOCK_SEVERITY,
              logic_block_severity: Any = DEFAULT_LOGIC_BLOCK_SEVERITY,
              ) -> EntryGateConfig:
        return cls(
            strict=_flag_bool(strict),
            enable_registry_gate=_flag_bool(enable_registry_gate),
            skill_dir=_normalize_skill_dir(skill_dir),
            registry_exclude_ids=_normalize_exclude_ids(registry_exclude_ids),
            registry_block_severity=_normalize_block_severity(
                registry_block_severity, DEFAULT_REGISTRY_BLOCK_SEVERITY,
                "registry_block_severity"),
            logic_block_severity=_normalize_block_severity(
                logic_block_severity, DEFAULT_LOGIC_BLOCK_SEVERITY,
                "logic_block_severity"),
        )
def _public_fields(obj: Any) -> dict[str, Any]:
    return {k: v for k, v in obj.__dict__.items() if not k.startswith("_")}
@dataclass
class Finding:
    rule_id: str
    severity: Severity
    location: str = ""
    line: int = 0
    message: str = ""
    suggestion: str = ""
    metrics: dict[str, Any] = field(default_factory=dict)
    references: list[str] = field(default_factory=list)
    def to_dict(self) -> dict[str, Any]:
        out = _public_fields(self)
        out["severity"] = (self.severity.value
                           if isinstance(self.severity, Severity)
                           else self.severity)
        return out
class DiagnoseFinding:
    __slots__ = (
        "code_snippet",
        "col_offset",
        "description",
        "dimension",
        "file",
        "id",
        "line",
        "message",
        "rule_ref",
        "severity",
        "suggestion",
        "title",
    )
    _INT_SLOTS = frozenset(("line", "col_offset"))
    def __init__(self, **kwargs: Any) -> None:
        for slot in self.__slots__:
            value = kwargs.get(slot, 0 if slot in self._INT_SLOTS else "")
            if slot == "line":
                value = coerce_line_number(value)
            elif slot == "col_offset":
                value = max(0, safe_int(value))
            setattr(self, slot, value)
    def to_dict(self) -> dict:
        return {s: getattr(self, s) for s in self.__slots__}
@dataclass
class PatternFinding:
    detector_id: str
    pattern_name: str
    severity: str
    filepath: str
    line: int = 0
    column: int = 0
    snippet: str = ""
    message: str = ""
    suggestion: str = ""
    def to_dict(self) -> dict[str, Any]:
        return _public_fields(self)
_DEDUPE_KEY_FIELDS = ("detector_id", "pattern_name", "filepath",
                      "line", "column", "message")
def _finding_field(finding: Any, name: str) -> Any:
    value = getattr(finding, name, None)
    if value is not None:
        return value
    if hasattr(finding, "get"):
        return finding.get(name)
    return None
def dedupe_findings(findings: list[PatternFinding]) -> list[PatternFinding]:
    seen = set()
    unique = []
    for finding in findings:
        key = tuple(_finding_field(finding, name)
                    for name in _DEDUPE_KEY_FIELDS)
        try:
            duplicated = key in seen
            if not duplicated:
                seen.add(key)
        except TypeError:
            unique.append(finding)
            continue
        if not duplicated:
            unique.append(finding)
    return unique
@dataclass
class FindingRecord:
    id: str = ""
    severity: str = ""
    dimension: str = ""
    file: str = ""
    line: int = 0
    rule: str = ""
    title: str = ""
    description: str = ""
    suggestion: str = ""
    code_snippet: str = ""
    rule_ref: str = ""
    def to_dict(self) -> dict[str, Any]:
        return _public_fields(self)
def finding_scan_exempt(filepath: Any) -> bool:
    return is_test_file_path(str(filepath or ""))
def _alias_value_missing(value: Any) -> bool:
    return (value is None
            or (isinstance(value, str) and not value.strip())
            or (isinstance(value, (bool, int, float)) and not value))
def _first_alias_value(record: dict, aliases: tuple[str, ...]):
    for alias in aliases:
        value = record.get(alias)
        if not _alias_value_missing(value):
            return value
    return None
def normalize_finding(finding: Any) -> dict:
    if not isinstance(finding, dict):
        return {}
    out = dict(finding)
    for canonical, aliases in FINDING_KEY_ALIASES.items():
        if not _alias_value_missing(out.get(canonical)):
            continue
        value = _first_alias_value(out, aliases)
        if value is not None:
            out[canonical] = value
    out["line"] = coerce_line_number(out.get("line"))
    return out
def issue_to_finding(issue: DiagnoseIssue | dict, filepath: str = "") -> dict:
    if isinstance(issue, dict):
        check_id = text_or_empty(
            issue.get("check_id") or issue.get("rule_id") or "")
        severity = issue.get("severity", "")
        line = issue.get("line")
        message = text_or_empty(issue.get("message"))
        suggestion = text_or_empty(issue.get("suggestion"))
    else:
        check_id = text_or_empty(getattr(issue, "check_id", "")
                                 or getattr(issue, "rule_id", ""))
        severity = getattr(issue, "severity", "")
        line = getattr(issue, "line", None)
        message = text_or_empty(getattr(issue, "message", ""))
        suggestion = text_or_empty(getattr(issue, "suggestion", ""))
        if not check_id:
            logger.warning("[diag_types_defs] issue_to_finding 条目缺少 "
                           "check_id(%s)，按空规则归档",
                           type(issue).__name__)
    return {
        "rule_id": check_id,
        "severity": diag_severity_to_p(severity),
        "dimension": "general",
        "file": filepath,
        "line": coerce_line_number(line),
        "title": message,
        "description": message,
        "suggestion": suggestion,
        "code_snippet": "",
        "rule_ref": check_id,
    }
@dataclass
class ProjectContext:
    project_type: str = "unknown"
    frameworks: list[str] = field(default_factory=list)
    python_version: str = ""
    has_type_checking: bool = False
    has_tests: bool = False
    has_ci: bool = False
    package_manager: str = "pip"
    file_stats: dict[str, int] = field(default_factory=dict)
@dataclass
class FunctionReport:
    name: str
    score: int
    lines: int = 0
    params: int = 0
    cyclomatic_complexity: int = 0
    cognitive_complexity: int = 0
    nesting_depth: int = 0
    has_docstring: bool = False
    has_type_annotations: bool = False
    violates_srp: bool = False
    slap_violations: list[str] = field(default_factory=list)
    findings: list[Finding] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
    extract_candidates: list[dict] = field(default_factory=list)
    summary: str = ""
    def to_dict(self) -> dict:
        out = _public_fields(self)
        out["findings"] = [f.to_dict() if hasattr(f, "to_dict") else f
                           for f in self.findings]
        return out
@dataclass
class DirFileStats:
    dir_path: str
    total_py_files: int
    total_lines: int
    small_files: list[str] = field(default_factory=list)
    large_files: list[str] = field(default_factory=list)
    massive_files: list[str] = field(default_factory=list)
    file_sizes: dict[str, int] = field(default_factory=dict)
@dataclass
class MergePlan:
    target_module: str
    source_files: list[str]
    rationale: str
    total_lines: int
    strategy: str
@dataclass
class DirFileResult:
    ok: bool
    dir_path: str
    stats: DirFileStats
    merge_plans: list[MergePlan] = field(default_factory=list)
    strangler_plans: list[dict] = field(default_factory=list)
    arch_violations: list[dict] = field(default_factory=list)
    issues: list[dict] = field(default_factory=list)
    message: str = ""
@dataclass
class SizeViolation:
    rule_id: str = ""
    type: str = ""
    severity: str = ""
    location: str = ""
    value: int = 0
    threshold: int = 0
    message: str = ""
    suggestion: str = ""
    def to_dict(self) -> dict:
        return dict(self.__dict__)
def _try_dict_method(obj: Any, method_name: str) -> dict | None:
    method = getattr(obj, method_name, None)
    if not callable(method):
        return None
    try:
        d = method()
        if isinstance(d, dict):
            return d
    except Exception as _e:  # noqa: BLE001 — 序列化降级，记录日志不阻断
        logger.warning("result_to_dict %s() fallback: %s", method_name, _e)
    return None
def result_to_dict(obj: Any) -> dict:
    if isinstance(obj, dict):
        return obj
    d = _try_dict_method(obj, "_asdict")
    if d is not None:
        return d
    d = _try_dict_method(obj, "to_dict")
    if d is not None:
        return d
    try:
        if is_dataclass(obj) and not isinstance(obj, type):
            return asdict(obj)
    except Exception as _e:  # noqa: BLE001 — 序列化降级，记录日志不阻断
        logger.warning("result_to_dict dataclass fallback: %s", _e)
    instance_dict = getattr(obj, "__dict__", None)
    if isinstance(instance_dict, dict):
        return dict(instance_dict)
    return {"raw": str(obj)[:500]}
def default_feedback_history() -> dict:
    return {
        "version": "1.0",
        FIELD_METHOD_THRESHOLDS: {},
        FIELD_CV_RULE_WEIGHTS: {},
        "fixer_needs": {},
        "session_count": 0,
        "sessions": [],
    }
def summary_dict(outcome_summary) -> dict:
    if isinstance(outcome_summary, TreatmentOutcomeSummary):
        return outcome_summary.to_dict()
    if isinstance(outcome_summary, dict):
        return dict(outcome_summary)
    if outcome_summary:
        logger.warning(
            "[diag_types_defs] outcome_summary 非法形态(%s)，归空处理",
            type(outcome_summary).__name__)
    return {}
@dataclass
class TreatmentOutcome:
    rule_id: str
    file: str
    line: int
    status: str
    severity: str
    auto_safe: bool = False
    fixer_type: str = ""
    reason: str = ""
    timestamp: str = ""
    side_effects: list[dict] = field(default_factory=list)
    def to_dict(self) -> dict:
        return _public_fields(self)
@dataclass
class TreatmentOutcomeSummary:
    total_attempted: int = 0
    total_fixed: int = 0
    total_rolled_back: int = 0
    total_failed: int = 0
    total_skipped: int = 0
    total_no_fixer: int = 0
    total_file_not_found: int = 0
    total_fp_confirmed: int = 0
    success_rate: float = 0.0
    rollback_rate: float = 0.0
    fp_rate: float = 0.0
    failure_patterns: list[dict] = field(default_factory=list)
    issues_discovered: list[dict] = field(default_factory=list)
    side_effects_summary: dict[str, Any] = field(default_factory=dict)
    def to_dict(self) -> dict:
        return _public_fields(self)
@dataclass
class DiagnosisFeedback:
    target_type: str
    target_id: str
    feedback_type: str
    current_value: Any = None
    suggested_value: Any = None
    reason: str = ""
    confidence: float = 0.0
    evidence: list[str] = field(default_factory=list)
    def to_dict(self) -> dict:
        out = _public_fields(self)
        out["current_value"] = text_or_empty(self.current_value)
        out[FIELD_SUGGESTED_VALUE] = text_or_empty(self.suggested_value)
        return out
@dataclass
class FeedbackReport:
    timestamp: str = ""
    treatment_summary: dict = field(default_factory=dict)
    diagnosis_feedbacks: list[dict] = field(default_factory=list)
    cv_feedbacks: list[dict] = field(default_factory=list)
    fixer_feedbacks: list[dict] = field(default_factory=list)
    applied_count: int = 0
    pending_count: int = 0
    memory_operations: list[dict] = field(default_factory=list)
    def to_dict(self) -> dict:
        return _public_fields(self)
def _implicit_severity_to_p(value: Any) -> str:
    token, rank = severity_rank_of_text(value)
    if not token:
        logger.debug("[diag_types_defs] 隐式流 severity 缺失，按 P3 归档")
        return "P3"
    if rank is None:
        logger.warning("[diag_types_defs] 隐式流 severity 非法(%r)，按 P3 归档",
                       value)
        return "P3"
    return severity_literal_from_rank(rank)
@dataclass
class ImplicitFlowFinding:
    category: str
    severity: str
    file: str
    line: int
    variable: str
    sink: str
    code_snippet: str = ""
    confidence: float = 1.0
    suggestion: str = ""
    cwe_id: str = ""
    def to_dict(self) -> dict[str, Any]:
        category = str_or(self.category, "").strip()
        rule_id = (f"IMPLICIT-{category.split('_')[0].upper()}"
                   if category else "IMPLICIT-FLOW")
        cwe_suffix = f" (CWE: {self.cwe_id})" if self.cwe_id else ""
        return {
            "rule_id": rule_id,
            "severity": _implicit_severity_to_p(self.severity),
            "file": self.file,
            "line": self.line,
            "message": (f"{rule_id}: 敏感变量 '{self.variable}' 影响 "
                        f"{self.sink} 的可观测输出{cwe_suffix}"),
            "category": "implicit_flow",
            "confidence": self.confidence,
            "suggestion": self.suggestion,
            "cwe_id": self.cwe_id,
            "variable": self.variable,
            "sink": self.sink,
            "code_snippet": self.code_snippet,
        }
@dataclass
class VulnerabilityFinding:
    category: VulnerabilityCategory
    severity: str
    file: str
    line: int
    source: str
    sink: str
    code_snippet: str = ""
    taint_origin: str = ""
    confidence: float = 1.0
    is_false_positive: bool = False
    suggestion: str = ""
    cwe_id: str = ""
    def __post_init__(self) -> None:
        if isinstance(self.category, VulnerabilityCategory):
            return
        try:
            self.category = VulnerabilityCategory(self.category)
        except (TypeError, ValueError) as _cat_exc:
            logger.warning(
                "VulnerabilityFinding.category 非法（%r），保留原值: %s",
                self.category, _cat_exc)
    def to_dict(self) -> dict[str, Any]:
        out = _public_fields(self)
        out["category"] = (
            self.category.value
            if isinstance(self.category, VulnerabilityCategory)
            else self.category
        )
        return out
@dataclass
class TaintTrace:
    variable: str
    source_file: str
    source_line: int
    source_expr: str
    propagation_chain: list[dict] = field(default_factory=list)
    sink_file: str = ""
    sink_line: int = 0
    sink_expr: str = ""
    crossed_modules: list[str] = field(default_factory=list)
    crossed_functions: list[str] = field(default_factory=list)
@dataclass
class ExecutionPath:
    path_id: int
    constraints: list[str] = field(default_factory=list)
    is_feasible: bool = True
    reaches_sink: bool = False
    sink_name: str = ''
    sink_line: int = 0
    trigger_input: dict[str, Any] = field(default_factory=dict)
@dataclass
class DiagnoseIssue:
    check_id: str
    severity: DiagnoseSeverity
    message: str
    line: int = 0
    col: int = 0
    suggestion: str = ''
    auto_fixable: bool = False
    details: dict = field(default_factory=dict)
@dataclass
class CrossFileSymbolicPath:
    path_id: str = ''
    entry_file: str = ''
    entry_function: str = ''
    nodes: list[str] = field(default_factory=list)
    constraints: list[str] = field(default_factory=list)
    taint_sources: list[str] = field(default_factory=list)
    taint_sinks: list[str] = field(default_factory=list)
    states: list[Any] = field(default_factory=list)
    is_feasible: bool = True
    feasibility_proof: str = ''
    exploit_inputs: dict[str, Any] = field(default_factory=dict)
@dataclass
class CrossFileSymbolicState:
    state_id: str = ''
    current_file: str = ''
    current_function: str = ''
    current_line: int = 0
    symbolic_vars: dict[str, Any] = field(default_factory=dict)
    cross_file_symbol_map: dict[str, Any] = field(default_factory=dict)
    path_constraints: list[str] = field(default_factory=list)
    cross_file_taint_flows: list[Any] = field(default_factory=list)
@dataclass
class UnifiedExploitResult:
    vulnerability_id: str = ''
    severity: str = ''
    cwe_id: str = ''
    exploit_id: str = ''
    payload: str = ''
    success: bool = False
    cross_file_steps: list[dict[str, Any]] = field(default_factory=list)
    constraints: list[str] = field(default_factory=list)
    exploitable_inputs: dict[str, Any] = field(default_factory=dict)
    constraint_solution: dict[str, Any] = field(default_factory=dict)
    fix_suggestions: list[str] = field(default_factory=list)
    runtime_context: dict[str, Any] = field(default_factory=dict)
    details: dict[str, Any] = field(default_factory=dict)
@dataclass
class CrossFileSymbolicReport:
    root_dir: str = ''
    files_scanned: int = 0
    files_failed: int = 0
    cross_file_paths: int = 0
    symbolic_states_explored: int = 0
    exploitable_vulnerabilities: int = 0
    scan_time_ms: float = 0.0
    backend_used: str = ''
    results: list[UnifiedExploitResult] = field(default_factory=list)
    findings: list[dict[str, Any]] = field(default_factory=list)
    score: float = 0.0
    errors: list[str] = field(default_factory=list)
def _trunc_str(value: Any, limit: int) -> str:
    return value[:limit] if isinstance(value, str) else ""
@dataclass
class FeedbackModification:
    modification_id: str = ""
    level: str = ""
    target_file: str = ""
    target_name: str = ""
    action_type: str = ""
    original_value: str = ""
    new_value: str = ""
    diff_preview: str = ""
    syntax_valid: bool | None = None
    regression_passed: bool | None = None
    backup_path: str = ""
    applied: bool = False
    timestamp: str = ""
    confidence: float = 0.0
    source_enhancement_id: str = ""
    error_message: str = ""
    def to_dict(self) -> dict:
        out = _public_fields(self)
        out.update(
            original_value=_trunc_str(self.original_value, 200),
            new_value=_trunc_str(self.new_value, 200),
            diff_preview=_trunc_str(self.diff_preview, 500),
        )
        return out
def str_field(entry: dict, key: str, default: str = "") -> str:
    if not hasattr(entry, "get"):
        logger.debug("[diag_types_defs] str_field 载荷非映射(%s)，取默认值 %r",
                     type(entry).__name__, default)
        return default
    return str_or(entry.get(key, default), default)
def build_failed_modification(modification_id: str, level: str,
                             target_name: str, action_type: str,
                             error_message: str,
                             confidence: float) -> FeedbackModification:
    return FeedbackModification(
        modification_id=modification_id, level=level,
        target_name=target_name, action_type=action_type,
        applied=False, confidence=confidence,
        error_message=error_message)
@dataclass
class FeedbackBatchResult:
    batch_id: str = ""
    timestamp: str = ""
    total_pending: int = 0
    total_processed: int = 0
    l1_applied: int = 0
    l2_applied: int = 0
    l3_applied: int = 0
    l4_applied: int = 0
    skipped: int = 0
    failed: int = 0
    modifications: list = field(default_factory=list)
    summary: str = ""
    def to_dict(self) -> dict:
        out = _public_fields(self)
        out["modifications"] = [
            m.to_dict() if hasattr(m, "to_dict")
            else (m if isinstance(m, dict)
                  else m.__dict__ if hasattr(m, "__dict__") else str(m))
            for m in self.modifications
        ]
        return out
@dataclass
class TestMethodResult:
    __test__ = False
    method_name: str
    method_id: str
    status: str = "pass"
    score: int = 100
    findings: list[dict] = field(default_factory=list)
    metrics: dict = field(default_factory=dict)
    summary: str = ""
    error: str | None = None
    elapsed_ms: float = 0.0
    def finish(self, start: float, precision: int | None = None) -> TestMethodResult:
        elapsed_ms = (time.perf_counter() - start) * 1000
        self.elapsed_ms = (elapsed_ms if precision is None
                           else round(elapsed_ms, precision))
        return self
    @classmethod
    def invalid_input(cls, raw_dir, method_name: str, method_id: str,
                      subject: str, start: float) -> TestMethodResult:
        result = cls(method_name=method_name, method_id=method_id)
        result.status = "error"
        result.score = 0
        result.error = f"目录不存在: {raw_dir!r}"
        result.summary = f"{subject}目录无效: {raw_dir!r}"
        return result.finish(start)
    @classmethod
    def skipped(cls, method_id: str, method_name: str, error: str,
                summary: str) -> TestMethodResult:
        return cls(method_name=method_name, method_id=method_id,
                   status="skip", score=0, error=error, summary=summary)
    @classmethod
    def from_execution_error(cls, exc: BaseException, method_id: str,
                             method_name: str) -> TestMethodResult:
        summary = f"执行异常: {type(exc).__name__}: {str(exc)[:200]}"
        if isinstance(exc, METHOD_DEGRADE_EXC):
            return cls.skipped(method_id, method_name, str(exc), summary)
        return cls(
            method_name=method_name, method_id=method_id,
            status="error", score=0, error=str(exc),
            summary=f"未预期异常: {type(exc).__name__}: {str(exc)[:200]}",
        )
    def to_dict(self) -> dict:
        out = _public_fields(self)
        out["elapsed_ms"] = round(self.elapsed_ms, 2)
        return out
def result_status_bucket(status: Any) -> str:
    if not isinstance(status, str):
        return 'error'
    token = status.strip().lower()
    return token if token in RESULT_STATUS_BUCKETS else 'error'
def _severity_tally_bucket(value: Any) -> str:
    _token, rank = severity_rank_of_text(value)
    if rank is None:
        logger.warning("[diag_types_defs] severity 缺失或非法(%r)，"
                       "聚合按 low 归档", value)
        return "low"
    if rank <= 1:
        return "high"
    return "medium" if rank == 2 else "low"
def severity_tally(findings: list[dict]) -> dict[str, int]:
    counts = {"high": 0, "medium": 0, "low": 0}
    for finding in dict_findings(findings):
        bucket = _severity_tally_bucket(finding.get("severity"))
        if bucket:
            counts[bucket] += 1
    return counts
def _coerce_count(value: Any) -> int:
    if isinstance(value, bool):
        return 0
    if isinstance(value, int):
        return max(value, 0)
    if isinstance(value, float):
        if math.isfinite(value) and value.is_integer():
            return max(int(value), 0)
        return 0
    if isinstance(value, str):
        try:
            return max(int(value.strip()), 0)
        except ValueError:
            return 0
    return 0
def graded_status_score(counts: dict, total: int,
                        low_penalty: int) -> tuple[str, int]:
    high = _coerce_count(
        counts.get('high', 0) if hasattr(counts, 'get') else 0)
    medium = _coerce_count(
        counts.get('medium', 0) if hasattr(counts, 'get') else 0)
    low = _coerce_count(
        counts.get('low', 0) if hasattr(counts, 'get') else 0)
    total_count = _coerce_count(total)
    penalty = _coerce_count(low_penalty)
    effective_total = max(total_count, high + medium + low)
    if effective_total == 0:
        return 'pass', 100
    if high > 0:
        return 'warn', max(30, 80 - high * 10)
    return 'pass', max(65, 90 - effective_total * penalty)
def finalize_test_result(result: TestMethodResult, cache,
                         start: float) -> TestMethodResult:
    entries = getattr(cache, "entries", None)
    try:
        total_files = len(entries)
    except TypeError:
        logger.warning("[diag_types_defs] 缓存条目不可计数(%s)，"
                       "扫描文件数按 0 归档", type(entries).__name__)
        total_files = 0
    result.metrics["total_files_scanned"] = total_files
    return result.finish(start, precision=1)
def scan_issue(rel_path: str, line: int, typ: str, severity: str,
                message: str, **extra) -> dict:
    return {"file": rel_path, "line": line, "type": typ,
            "severity": severity, "message": message, **extra}
def norm_result_line(item: dict) -> int:
    if not hasattr(item, "get"):
        return 0
    return coerce_line_number(item.get("line", 0))
def _coerce_guard_level(
        value: Any, fallback: GuardLevel = GuardLevel.INFO) -> GuardLevel:
    if isinstance(value, GuardLevel):
        return value
    text = severity_text_value(value)
    if text:
        token = text.upper()
        for member in GuardLevel:
            if token in (member.value.upper(), member.name.upper()):
                return member
    return fallback
@dataclass
class GuardResult:
    guard_name: str
    passed: bool
    level: GuardLevel | str | None = None
    message: str = ""
    details: list[str] = field(default_factory=list)
    fix_suggestion: str = ""
    def __post_init__(self) -> None:
        self.passed = (False if self.passed is None
                       else normalize_passed(self.passed))
        if not isinstance(self.message, str):
            self.message = "" if self.message is None else str(self.message)
        if not isinstance(self.level, GuardLevel):
            fallback = GuardLevel.INFO if self.passed else GuardLevel.BLOCK
            self.level = _coerce_guard_level(self.level, fallback)
DEFAULT_OPERATION_TARGET_PATH = ""
DEFAULT_OPERATION_AFFECTED_FILES: list[str] | None = None
DEFAULT_OPERATION_METADATA: dict[str, Any] | None = None
DEFAULT_OPERATION_DRY_RUN = False
def common_parent_of(paths: Iterable[str]) -> str:
    files = normalize_files_list(paths)
    if not files:
        return ""
    try:
        parents = [os.path.dirname(os.path.abspath(path)) for path in files]
        return os.path.commonpath(parents)
    except (OSError, ValueError) as _e:
        log_swallowed(
            __name__, _e,
            context=f'common_parent_of:{type(_e).__name__}')
        return ""
@dataclass
class OperationContext:
    operation: OperationType
    target_path: str = DEFAULT_OPERATION_TARGET_PATH
    dry_run: bool = DEFAULT_OPERATION_DRY_RUN
    metadata: dict | None = DEFAULT_OPERATION_METADATA
    affected_files: list[str] | None = DEFAULT_OPERATION_AFFECTED_FILES
    def __post_init__(self) -> None:
        self.metadata = _metadata_dict(self.metadata)
        self.operation = normalize_operation_kind(self.operation)
        self.affected_files = normalize_files_list(self.affected_files)
        self.target_path = normalize_target_path(self.target_path)
        self._target_path_inferred = False
        if not self.target_path:
            self.target_path = common_parent_of(self.affected_files)
            self._target_path_inferred = bool(self.target_path)
        self.dry_run = _flag_bool(self.dry_run)
def _metadata_dict(metadata: Any) -> dict:
    if isinstance(metadata, dict):
        return dict(metadata)
    if metadata is not None and hasattr(metadata, "get") and hasattr(metadata, "items"):
        try:
            return dict(metadata)
        except (TypeError, ValueError) as exc:
            logger.warning("操作上下文 metadata 的 Mapping 形态转 dict 失败 %r，"
                           "已归一空 dict: %s", metadata, exc)
            return {}
    if metadata is not None:
        logger.warning("操作上下文 metadata 类型非法 %r，已归一空 dict", metadata)
    return {}
def normalize_operation_kind(raw: Any) -> Any:
    if isinstance(raw, OperationType):
        return raw
    if isinstance(raw, str):
        try:
            return OperationType(raw)
        except ValueError:
            logger.debug("operation 值非枚举成员，按原样保留: %r", raw, exc_info=True)
            return raw
    return raw
def is_read_only_audit(ctx: OperationContext) -> bool:
    metadata = getattr(ctx, "metadata", None)
    if not hasattr(metadata, "get"):
        return False
    value = metadata.get("read_only_audit", False)
    return False if value is None else normalize_passed(value)
def target_path_str(ctx: OperationContext) -> str:
    tp = getattr(ctx, "target_path", "")
    return tp if isinstance(tp, str) else ""
def _ctx_metadata(ctx: Any) -> dict:
    metadata = getattr(ctx, "metadata", None)
    return metadata if hasattr(metadata, "get") else {}
def metadata_path_str(ctx: OperationContext, key: str) -> str:
    return normalize_target_path(_ctx_metadata(ctx).get(key, ""))
def code_to_write_str(ctx: OperationContext) -> str:
    code = _ctx_metadata(ctx).get("code_to_write", "")
    if isinstance(code, str):
        return code
    if isinstance(code, (bytes, bytearray)):
        try:
            return bytes(code).decode("utf-8")
        except UnicodeDecodeError as exc:
            logger.warning("code_to_write 非 UTF-8 字节，守卫按空串处理: %s", exc)
            return ""
    if isinstance(code, (list, tuple)):
        if all(isinstance(line, str) for line in code):
            return "\n".join(code)
        logger.warning("code_to_write 条目非字符串，守卫按空串处理")
        return ""
    if code is not None:
        logger.warning("code_to_write 形态非法(%s)，守卫按空串处理",
                       type(code).__name__)
    return ""
def issues_guard_result(guard_name: str, label: str, unit: str,
                        issues: list[str], fix_suggestion: str,
                        pass_message: str, *,
                        level: GuardLevel = GuardLevel.BLOCK) -> GuardResult:
    if not issues:
        return GuardResult(guard_name=guard_name, passed=True,
                           message=pass_message)
    return GuardResult(guard_name=guard_name, passed=False, level=level,
                       message=f"{label}发现 {len(issues)} 个{unit}",
                       details=issues, fix_suggestion=fix_suggestion)
@dataclass
class DocSection:
    title: str = ""
    content: str = ""
    required: bool = False
    order: int = 0
@dataclass
class DocQualityIssue:
    category: str = ""
    rule_id: str = ""
    severity: str = ""
    description: str = ""
    suggestion: str = ""
    location: str = ""
    matched_text: str = ""
@dataclass
class SubDimensionScore:
    dim_id: str = ""
    dim_name: str = ""
    category: str = ""
    score: float = 0.0
    weight: float = 1.0
    issues: list[DocQualityIssue] = field(default_factory=list)
    detail: str = ""
@dataclass
class DocQualityReport:
    skill_name: str = ""
    skill_path: str = ""
    total_issues: int = 0
    issues: list[DocQualityIssue] = field(default_factory=list)
    matching_score: float = 0.0
    capture_score: float = 0.0
    loading_score: float = 0.0
    content_score: float = 0.0
    upload_score: float = 0.0
    overall_score: float = 0.0
    overall_grade: str = "F"
    phase_summary: dict[str, Any] = field(default_factory=dict)
    suggestions: list[str] = field(default_factory=list)
    sub_dimensions: list[SubDimensionScore] = field(default_factory=list)
    def to_dict(self: Self) -> dict[str, Any]:
        return {
            "skill_name": self.skill_name,
            "skill_path": self.skill_path,
            "total_issues": self.total_issues,
            "overall_score": self.overall_score,
            "overall_grade": self.overall_grade,
            "phase_scores": {
                "matching": self.matching_score,
                "capture": self.capture_score,
                "loading": self.loading_score,
                "content": self.content_score,
                "upload": self.upload_score,
            },
            "phase_summary": self.phase_summary,
            "issues": [
                {
                    "category": i.category,
                    "rule_id": i.rule_id,
                    "severity": i.severity,
                    "description": i.description,
                    "suggestion": i.suggestion,
                    "location": i.location,
                    "matched_text": i.matched_text,
                }
                for i in self.issues
            ],
            "suggestions": self.suggestions,
            "sub_dimensions": [
                {
                    "dim_id": s.dim_id,
                    "dim_name": s.dim_name,
                    "category": s.category,
                    "score": s.score,
                    "weight": s.weight,
                    "detail": s.detail,
                    "issue_count": len(s.issues),
                }
                for s in self.sub_dimensions
            ],
        }
@dataclass
class DocRefactorPlan:
    skill_name: str = ""
    original_path: str = ""
    issues: list[DocQualityIssue] = field(default_factory=list)
    improvements: list[str] = field(default_factory=list)
    new_frontmatter: str = ""
    new_body_sections: list[DocSection] = field(default_factory=list)
    estimated_score_after: float = 0.0
    def to_dict(self: Self) -> dict[str, Any]:
        return {
            "skill_name": self.skill_name,
            "original_path": self.original_path,
            "issue_count": len(self.issues),
            "improvements": self.improvements,
            "estimated_score_after": self.estimated_score_after,
            "new_frontmatter": self.new_frontmatter,
            "new_body_sections": [
                {"title": s.title, "content": s.content[:200], "order": s.order}
                for s in self.new_body_sections
            ],
        }
_DEFAULT_SCAN_TARGET_LABEL = "技能目录"
def make_noscan_issue(category: str, rule_id: str, what: str, *,
                      target_label: str = _DEFAULT_SCAN_TARGET_LABEL
                      ) -> DocQualityIssue:
    label = str_or(target_label).strip() or _DEFAULT_SCAN_TARGET_LABEL
    suggestion = (MSG_CONFIRM_SKILL_DIR if label == _DEFAULT_SCAN_TARGET_LABEL
                  else f"确认{label}可访问，重新运行诊断")
    return DocQualityIssue(
        category=category, rule_id=rule_id, severity="medium",
        description=f"无法扫描{label}，{what}未验证",
        suggestion=suggestion,
        location=label,
    )
def make_matching_issue(rule_id: str, severity: str, description: str,
                        suggestion: str,
                        location: str = "frontmatter: description",
                        matched_text: str = "") -> DocQualityIssue:
    return DocQualityIssue(
        category="matching", rule_id=rule_id, severity=severity,
        description=description, suggestion=suggestion,
        location=location, matched_text=matched_text,
    )
def record_dimension(results: list[SubDimensionScore],
                     all_issues: list[DocQualityIssue],
                     dim: SubDimensionScore) -> None:
    all_issues.extend(dim.issues)
    results.append(dim)
def collect_findings(
        entries: Iterable[tuple[str, str, str, str | None, bool]],
) -> tuple[list[dict], list[str], bool]:
    details: list[dict] = []
    suggestions: list[str] = []
    has_blocking = False
    for raw_entry in (entries if entries is not None else ()):
        if not isinstance(raw_entry, (tuple, list)) or len(raw_entry) != 5:
            logger.warning("[diag_types_defs] collect_findings 跳过形态非法条目"
                           "(%s)，期望 5 元组", type(raw_entry).__name__)
            continue
        issue, rule_id, locator, suggestion, blocking = raw_entry
        details.append(make_detail(issue=issue, rule_id=rule_id,
                                   locator=locator, confidence=1.0))
        has_blocking = has_blocking or _flag_bool(blocking)
        if suggestion and suggestion not in suggestions:
            suggestions.append(suggestion)
    return details, suggestions, has_blocking
_DETAIL_CONFIDENCE_DEFAULT = 0.85
_DETAIL_CONFIDENCE_FALLBACK = DEFAULT_FINDING_CONFIDENCE
def _detail_confidence(detail: object) -> float:
    value = detail.get("confidence") if isinstance(detail, dict) else None
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return _DETAIL_CONFIDENCE_FALLBACK
    try:
        number = float(value)
    except OverflowError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_detail_confidence:OverflowError')
        return _DETAIL_CONFIDENCE_FALLBACK
    if not math.isfinite(number):
        return _DETAIL_CONFIDENCE_FALLBACK
    return min(max(number, 0.0), 1.0)
def _detail_dicts(details: list) -> list[dict]:
    return [d for d in details if isinstance(d, dict)]
def _detail_texts(details: list[dict], key: str) -> list[str]:
    return [value for detail in details
            if isinstance((value := detail.get(key)), str) and value]
def _compute_confidence(details: list) -> float:
    valid = _detail_dicts(details)
    if not valid:
        return 0.0
    total = sum(_detail_confidence(d) for d in valid)
    return round(total / len(valid), 3)
def make_detail(issue: str, rule_id: str, locator: str,
                confidence: float = _DETAIL_CONFIDENCE_DEFAULT, **extra) -> dict:
    detail = {
        "issue": issue,
        "rule_id": rule_id,
        "locator": locator,
        "confidence": confidence,
    }
    detail.update(extra)
    return detail
def prepare_tree(
        content: str, check_name: str,
) -> tuple[ast.AST | None, PreinterventionResult | None]:
    if not content:
        return None, PreinterventionResult(
            check_name=check_name, passed=True, severity="info",
            message="无内容可检查")
    try:
        return ast.parse(content), None
    except PARSE_DEGRADE_EXC as e:
        logger.debug("suppressed parse error: %s", e)
        return None, PreinterventionResult(
            check_name=check_name, passed=False, severity="blocking",
            message=f"语法错误: {e}")
def finish_check(check_name: str, title: str, passed: bool, fail_severity: str,
                 details: list, suggestions: list) -> PreinterventionResult:
    return PreinterventionResult(
        check_name=check_name,
        passed=passed,
        severity=fail_severity if not passed else SEVERITY_INFO,
        message=title + ("" if passed else "（发现问题）"),
        details=details,
        suggestions=suggestions,
    )
@dataclass
class PreinterventionResult:
    check_name: str
    passed: bool
    severity: str
    message: str
    details: list[dict[str, Any]] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
    def to_dict(self) -> dict:
        detail_dicts = _detail_dicts(self.details)
        rule_ids = sorted(set(_detail_texts(detail_dicts, "rule_id")))
        locators = _detail_texts(detail_dicts, "locator")
        return {
            "check_name": self.check_name,
            "passed": self.passed,
            "severity": self.severity,
            "message": self.message,
            "details": self.details,
            "suggestions": self.suggestions,
            "rule_ids": rule_ids,
            "locators": locators,
            "evidence_type": "static_text",
            "confidence": _compute_confidence(self.details),
        }
@dataclass
class PreCheckItem:
    category: str = ""
    severity: str = ""
    description: str = ""
    suggestion: str = ""
    source: str = ""
    applicable_to: str = ""
    rule_id: str = ""
    locator: str = ""
    confidence: float = 0.0
    evidence_type: str = ""
    def to_dict(self) -> dict:
        return asdict(self)
@dataclass
class ArchitectureSuggestion:
    aspect: str = ""
    description: str = ""
    reasoning: str = ""
    pattern: str = ""
    example: str = ""
    def to_dict(self) -> dict:
        return asdict(self)
def type_error_precheck(actual_value, field_desc: str,
                         source: str, applicable_to: str,
                         suggestion: str = "传入 str 源码后再继续") -> PreCheckItem:
    return PreCheckItem(
        category="code_quality",
        severity=SEVERITY_BLOCKING,
        description=(
            f"输入类型错误: {field_desc}，实际 "
            f"{type(actual_value).__name__}"),
        suggestion=suggestion,
        source=source,
        applicable_to=applicable_to,
    )
def normalize_text_param(
    value: object,
    field_desc: str,
    *,
    suggestion: str,
    applicable_to: str,
    allow_pathlike: bool = False,
    prechecks: list[dict] | None = None,
) -> tuple[str, PreCheckItem | None]:
    if (isinstance(value, str) or value is None
            or (allow_pathlike and isinstance(value, os.PathLike))):
        return normalize_input(
            value, field_desc, allow_path=allow_pathlike), None
    error = type_error_precheck(
        value, field_desc, "type_guard", applicable_to, suggestion=suggestion)
    if prechecks is not None:
        prechecks.append(error.to_dict())
    return "", error
def dict_findings(findings) -> list:
    try:
        return [f for f in findings if isinstance(f, dict)]
    except TypeError as _e:
        log_swallowed(__name__, _e, context='dict_findings:TypeError')
        return []
def severity_breakdown_of(findings) -> dict[str, int]:
    sev_count: dict[str, int] = {}
    for ff in dict_findings(findings):
        s = ff.get("severity")
        if not isinstance(s, str):
            s = "unknown"
        else:
            s = s.strip().upper() or "unknown"
        sev_count[s] = sev_count.get(s, 0) + 1
    return sev_count
def make_a2_finding(rule_id: str, severity: str, file: str, line: int,
                    message: str, **extra: object) -> dict:
    finding: dict = {
        "rule_id": rule_id, "severity": severity,
        "file": file, "line": line, "message": message, "source": "A2",
    }
    finding.update(extra)
    return finding
def aaf_reject(ctx: Any, status: str, reason: str, *, event: str,
               audit_reason: str = "", **extra: Any) -> dict[str, Any]:
    index = getattr(ctx, "index", None)
    file_path = normalize_filepath(getattr(ctx, "file_path", ""))
    if ctx is None or not hasattr(ctx, "index"):
        logger.warning("[diag_types_defs] aaf_reject 上下文缺少 index/file_path"
                       "(%s)，审计按缺省字段记录", type(ctx).__name__)
    safe_write_audit(event, index=index, file=file_path,
                     reason=audit_reason or reason)
    payload: dict[str, Any] = {
        **extra,
        "status": status,
        "reason": reason,
        "regression_verified": False,
    }
    if getattr(ctx, "side_effects", None):
        payload["side_effects"] = ctx.side_effects
    return payload
__all__ = [
    'DEFAULT_LOGIC_BLOCK_SEVERITY',
    'DEFAULT_OPERATION_AFFECTED_FILES',
    'DEFAULT_OPERATION_DRY_RUN',
    'DEFAULT_OPERATION_METADATA',
    'DEFAULT_OPERATION_TARGET_PATH',
    'DEFAULT_REGISTRY_BLOCK_SEVERITY',
    'ArchitectureSuggestion',
    'ConcurrentExecutionError',
    'ContractViolationError',
    'CrossFileSymbolicPath',
    'CrossFileSymbolicReport',
    'CrossFileSymbolicState',
    'DiagnoseFinding',
    'DiagnoseIssue',
    'DiagnoseSeverity',
    'DiagnosisFeedback',
    'DirFileResult',
    'DirFileStats',
    'DocQualityIssue',
    'DocQualityReport',
    'DocRefactorPlan',
    'DocSection',
    'EntryGateConfig',
    'EntryResult',
    'ExecutionPath',
    'FeedbackBatchResult',
    'FeedbackModification',
    'FeedbackReport',
    'Finding',
    'FindingRecord',
    'FunctionReport',
    'GuardResult',
    'ImplicitFlowFinding',
    'MergePlan',
    'OperationContext',
    'PatternFinding',
    'PreCheckItem',
    'PreinterventionResult',
    'ProjectContext',
    'SizeViolation',
    'SubDimensionScore',
    'TaintTrace',
    'TestMethodResult',
    'TreatmentOutcome',
    'TreatmentOutcomeSummary',
    'UnifiedExploitResult',
    'VulnerabilityFinding',
    'aaf_reject',
    'build_failed_modification',
    'code_to_write_str',
    'collect_findings',
    'common_parent_of',
    'dedupe_findings',
    'default_feedback_history',
    'diag_issue_entry',
    'diag_line',
    'dict_findings',
    'finalize_test_result',
    'finding_scan_exempt',
    'finish_check',
    'graded_status_score',
    'is_read_only_audit',
    'issue_to_finding',
    'issues_guard_result',
    'make_a2_finding',
    'make_detail',
    'make_matching_issue',
    'make_noscan_issue',
    'metadata_path_str',
    'norm_result_line',
    'normalize_finding',
    'normalize_operation_kind',
    'normalize_text_param',
    'prepare_tree',
    'record_dimension',
    'result_status_bucket',
    'result_to_dict',
    'scan_issue',
    'severity_breakdown_of',
    'severity_rank_of_text',
    'severity_tally',
    'str_field',
    'summary_dict',
    'target_path_str',
    'type_error_precheck',
]

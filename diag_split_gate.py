from __future__ import annotations

import ast
import hashlib
import io
import logging
import math
import re
import threading
import tokenize
from dataclasses import dataclass, field
from enum import Enum
from typing import Any

from jwsgj.diag_detector_assembly import DiagnoseGate, gate_issue_severity
from jwsgj.diag_detectors_registry import preflight_diagnostic_check
from jwsgj.diag_guard_injection_enforce import (
    CodeInjectionEngine,
    SourceBudgetGuard,
)
from jwsgj.diag_guard_injection_scan import (
    CIE_WRITE_SAME_ROOT_RULE_IDS,
    is_always_block_finding,
    scan_write_redlines,
)
from jwsgj.diag_shared_ast_nodes import (
    calc_nesting,
    count_params,
    definition_start_line,
    iter_own_scope,
    own_scope_line_span,
)
from jwsgj.diag_shared_source_core import (
    check_comment_docstring_sync,
    coerce_source_text,
    count_lines,
    decode_source,
    read_py_source_with_error,
)
from jwsgj.diag_split_plan import (
    _PATCH_FORMS,
    _added_patch_form_lines,
    _parse_module_with_semantics,
)
from jwsgj.diag_split_plan import (
    GenerationGuard as _GenerationGuard,
)
from jwsgj.diag_split_plan import (
    new_patch_fix_issues as _new_patch_fix_issues,
)
from jwsgj.diag_split_plan import (
    normalize_code as _normalize_code,
)
from jwsgj.diag_types_defs import (
    EntryGateConfig,
    EntryResult,
    aaf_reject,
    diag_issue_entry,
    diag_line,
    severity_rank_of_text,
)
from jwsgj.diag_types_normalize import int_or, severity_text_value, strip_bom
from jwsgj.diag_types_vocab import (
    HARD_MAX_CLASS_LINES,
    HARD_MAX_FILE_LINES,
    HARD_MAX_FUNC_LINES,
    HARD_MAX_METHOD_LINES,
    HARD_MAX_NESTING,
    HARD_MAX_PARAMS,
    PARSE_DEGRADE_EXC,
    SEVERITY_RANK,
    EntryDecision,
    normalize_filepath,
)
from jwsgj.fp_rules_judge import is_known_fp
from jwsgj.log_config import log_swallowed, write_bug_intercept
from jwsgj.prevention_refs_main import (
    attach_issue_examples,
    run_write_preflight_gate,
)
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
__all__ = [
    "GATE5_LOGIC_RID_RE",
    "BlockedError",
    "DiagnosePhase",
    "GenEntryGuard",
    "GuardDecision",
    "GuardedCode",
    "SizeCheckEngine",
    "WriteBlockedError",
    "WriteGuard",
    "aaf_verify_patch_precheck",
    "check_fixed_source_syntax",
    "comment_docstring_sync_error",
    "commit_blocked",
    "downgrade_known_fp",
    "get_entry_guard",
    "load_quick_guard_source",
    "query_known_fp",
    "quick_guard",
    "run_registry_gate",
]
def load_quick_guard_source(filepath: str) -> tuple[str | None, dict | None]:
    filepath = normalize_filepath(filepath)
    if not filepath:
        return None, {"ok": False, "error": "filepath 和 code 不能同时为空"}
    try:
        code, error = read_py_source_with_error(filepath)
    except ValueError as e:
        log_swallowed(__name__, e, context='load_quick_guard_source:ValueError')
        error = e
        code = None
    if error is None:
        return code, None
    if isinstance(error, FileNotFoundError):
        log_swallowed(__name__, error, context='load_quick_guard_source:FileNotFoundError')
        return None, {"ok": False, "error": f"文件不存在: {filepath}"}
    logger.debug("[quick_guard] 文件读取失败: %s (%s)", filepath, error)
    return None, {"ok": False, "error": f"文件读取失败: {filepath} ({error})"}
def comment_docstring_sync_error(
    original_source: str, fixed_source: str, filepath: str
) -> str | None:
    comment_issues = check_comment_docstring_sync(
        original_source, fixed_source, filepath)
    if not comment_issues:
        return None
    return (
        "修复未同步受影响的注释/docstring（fix_scope.comments"
        "写盘门禁）："
        + "；".join(
            f"[{i['kind']}] {i['detail']}"
            for i in comment_issues[:3])
        + "。修复改变行为/语义/契约时必须同步更新相关 docstring"
        "与注释，禁止留下与新实现矛盾的旧注释；请同步修订后重新"
        "提交修复源码全文"
    )
def check_fixed_source_syntax(fixed_source: str, filepath: str) -> str | None:
    try:
        tokenize.detect_encoding(io.BytesIO(
            fixed_source.encode("utf-8", errors="surrogatepass")).readline)
        source = strip_bom(fixed_source)
        compile(source, filepath, "exec")
    except (LookupError, *PARSE_DEGRADE_EXC) as e:  # jwsgj:silent-ok
        return f"修复后代码语法错误: {e}"
    return None
def aaf_verify_patch_precheck(ctx: Any) -> dict | None:
    try:
        _added = _added_patch_form_lines(
            ctx.original_source, ctx.fixed_source)
    except Exception as exc:
        reason = (f"写前补丁预检执行失败({type(exc).__name__}): "
                  f"{str(exc)[:200]}，未获得验证通过结论，已拒绝写入")
        logger.warning("[AIManualFix] %s", reason, exc_info=True)
        return aaf_reject(
            ctx, "failed", reason, event="ai_fix_failed",
            audit_reason=reason, patch_precheck="error")
    if _added is None:
        reason = ("写前补丁预检源码不可解析，补丁形态差集无法归因，"
                  "未获得验证通过结论，已拒绝写入")
        logger.warning("[AIManualFix] %s", reason)
        return aaf_reject(
            ctx, "failed", reason, event="ai_fix_failed",
            audit_reason=reason, patch_precheck="error")
    if not _added:
        return None
    _labels = {key: label for key, _matched, label, _suffix in _PATCH_FORMS}
    _detail = "；".join(
        f"{_labels.get(key, key)} x{len(lines)}"
        f"（行 {', '.join(str(n) for n in sorted(set(lines))[:8])}）"
        for key, lines in _added.items())
    _reason = (f"写前补丁式修复预检拦截: 修复新引入 "
               f"{sum(len(lines) for lines in _added.values())} 处补丁形态"
               f" —— {_detail}——禁止补丁方式修复（B35），请定位根因并以"
               f"根因消除方式重修，不得以吞异常遮蔽症状")
    logger.warning("[AIManualFix] %s", _reason)
    return aaf_reject(
        ctx, "rejected", _reason, event="ai_fix_rejected",
        patch_precheck="blocked_patch_form")
def _safe_text_md5(text: str) -> str:
    try:
        raw = text.encode("utf-8")
    except UnicodeEncodeError as _e:
        log_swallowed(__name__, _e, context='_safe_text_md5:UnicodeEncodeError')
        raw = text.encode("utf-8", "surrogatepass")
    return hashlib.md5(raw, usedforsecurity=False).hexdigest()
class GuardDecision(Enum):
    ALLOW = "allow"
    BLOCK = "block"
    WARN = "warn"
    DEGRADED = "degraded"
@dataclass
class SizeScan:
    total_lines: int = 0
    func_count: int = 0
    class_count: int = 0
    blocking: list[dict] = field(default_factory=list)
    warning: list[dict] = field(default_factory=list)
@dataclass(frozen=True)
class _EntityLineRule:
    max_lines: int
    rule_id: str
_METHOD_LINE_RULE = _EntityLineRule(HARD_MAX_METHOD_LINES, "SIZE-METHOD-001")
_FUNC_LINE_RULE = _EntityLineRule(HARD_MAX_FUNC_LINES, "SIZE-FUNC-001")
def _size_violation(rule_id: str, severity: str, location: str,
                    message: str, value: int, threshold: int,
                    suggestion: str) -> dict:
    return {"rule_id": rule_id, "message": message, "severity": severity,
            "location": location, "value": value, "threshold": threshold,
            "suggestion": suggestion}
class SizeCheckEngine:
    def check(self, tree: ast.AST, code: str, filepath: str) -> SizeScan:
        code = coerce_source_text(code) or ""
        filepath = normalize_filepath(filepath)
        scan = SizeScan(total_lines=count_lines(code))
        self._check_file_length(scan, filepath)
        if not isinstance(tree, ast.AST):
            logger.debug(
                "[SizeCheckEngine] tree 非 AST（%s），仅做文件行数判定",
                type(tree).__name__)
            self._scan_budget(scan, code, filepath)
            return scan
        self._scan_entities(tree, scan)
        self._scan_budget(scan, code, filepath)
        return scan
    def _check_file_length(self, scan: SizeScan, filepath: str) -> None:
        total_lines = scan.total_lines
        if total_lines > HARD_MAX_FILE_LINES:
            msg = (
                f"文件 {total_lines} 行,超过硬限制 {HARD_MAX_FILE_LINES} 行."
                f"必须按 GOV-01 治理（简化/去重/收敛/迁移），"
                f"把规模收敛到 ≤{HARD_MAX_FILE_LINES} 行"
            )
            scan.blocking.append(_size_violation(
                "SIZE-FILE-001", "CRITICAL", filepath or "(代码片段)", msg,
                total_lines, HARD_MAX_FILE_LINES,
                "简化逻辑/消除重复/收敛依赖/迁移无关块到"
                "既有职责模块（GOV-01 禁止直接拆分）"))
        elif total_lines > HARD_MAX_FILE_LINES * 0.6:
            msg = (
                f"文件 {total_lines} 行,接近硬限制 {HARD_MAX_FILE_LINES} 行"
                f"（{total_lines * 100 // HARD_MAX_FILE_LINES}%）,治理候选"
                "（GOV-01 禁止直接拆分）"
            )
            scan.warning.append(_size_violation(
                "SIZE-FILE-002", "HIGH", filepath or "(代码片段)", msg,
                total_lines, int(HARD_MAX_FILE_LINES * 0.6),
                "优先简化逻辑或迁移无关块到既有职责模块"))
    def _scan_entities(self, tree: ast.AST, scan: SizeScan) -> None:
        method_nodes: set[int] = set()
        method_classes: dict[int, str] = {}
        func_count = 0
        class_count = 0
        for node in walk_nodes(tree):
            if isinstance(node, ast.ClassDef):
                class_count += 1
                self._check_class_node(node, scan)
                self._collect_method_nodes(node, method_nodes, method_classes)
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                func_count += 1
                self._check_func_node(node, id(node) in method_nodes,
                                      method_classes, scan)
        scan.func_count = func_count
        scan.class_count = class_count
    @staticmethod
    def _collect_method_nodes(node: ast.ClassDef, method_nodes: set,
                              method_classes: dict[int, str]) -> None:
        for child in iter_own_scope(node, skip_lambda=True, include_self=False):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                method_nodes.add(id(child))
                method_classes[id(child)] = node.name
    def _check_class_node(self, node: ast.ClassDef,
                          scan: SizeScan) -> None:
        cls_lines = (node.end_lineno or node.lineno) - definition_start_line(
            node) + 1
        if cls_lines > HARD_MAX_CLASS_LINES:
            scan.blocking.append(_size_violation(
                "SIZE-CLASS-001", "HIGH", node.name,
                f"类 '{node.name}' {cls_lines} 行,超过限制 {HARD_MAX_CLASS_LINES} 行",
                cls_lines, HARD_MAX_CLASS_LINES,
                (f"收敛类 '{node.name}' 职责：提取同模块私有实现或"
                 f"迁出无关方法（GOV-01 禁止拆分）")))
    def _check_func_node(self, node: ast.AST, is_method: bool,
                         method_classes: dict[int, str],
                         scan: SizeScan) -> None:
        display_name, kind = self._entity_identity(
            node, is_method, method_classes)
        self._check_entity_lines(
            node, scan, _METHOD_LINE_RULE if is_method else _FUNC_LINE_RULE,
            display_name, kind)
        self._check_func_nesting(node, scan, display_name, kind)
        self._check_func_params(node, scan, display_name, kind, is_method)
    @staticmethod
    def _entity_identity(node, is_method: bool,
                         method_classes: dict[int, str]) -> tuple[str, str]:
        class_name = method_classes.get(id(node)) or ""
        if not is_method or not class_name:
            return node.name, "函数"
        return f"{class_name}.{node.name}", "方法"
    def _check_entity_lines(self, node, scan: SizeScan,
                            rule: _EntityLineRule, display_name: str,
                            kind: str) -> None:
        func_lines = own_scope_line_span(node)
        if func_lines > rule.max_lines:
            scan.blocking.append(_size_violation(
                rule.rule_id, "HIGH", display_name,
                f"{kind} '{display_name}' {func_lines} 行,"
                f"超过限制 {rule.max_lines} 行",
                func_lines, rule.max_lines,
                (f"按执行阶段提取 '{display_name}' 的同模块私有子函数或"
                 f"迁移无关块，把自身规模收敛到 ≤{rule.max_lines} 行"
                 "（GOV-01 禁止直接拆分）")))
    def _check_func_nesting(self, node, scan: SizeScan,
                            display_name: str, kind: str) -> None:
        depth = calc_nesting(node)
        if depth > HARD_MAX_NESTING:
            scan.blocking.append(_size_violation(
                "SIZE-NEST-001", "HIGH", display_name,
                f"{kind} '{display_name}' 嵌套深度 {depth},"
                f"超过限制 {HARD_MAX_NESTING} 层",
                depth, HARD_MAX_NESTING,
                "使用卫语句(early return/continue)减少嵌套"))
    def _check_func_params(self, node, scan: SizeScan,
                           display_name: str, kind: str,
                           is_method: bool) -> None:
        params = count_params(node, is_method)
        if params > HARD_MAX_PARAMS:
            scan.warning.append(_size_violation(
                "SIZE-PARAM-001", "MEDIUM", display_name,
                f"{kind} '{display_name}' 有 {params} 个参数,"
                f"超过限制 {HARD_MAX_PARAMS}",
                params, HARD_MAX_PARAMS,
                "封装参数为 dataclass 或参数对象"))
    def _scan_budget(self, scan: SizeScan, code: str,
                     filepath: str) -> None:
        try:
            budget = SourceBudgetGuard(strict=False).check(
                code, filepath=filepath)
            location = filepath or "(代码片段)"
            for item in budget.violations:
                total_lines = int_or(getattr(item, "total_lines", 0), 0)
                budget_lines = int_or(getattr(item, "budget_lines", 0), 0)
                scan.warning.append(_size_violation(
                    "BUDGET-001", "MEDIUM", location,
                    (f"实体预算超标: {item.entity_type} "
                     f"'{item.entity_name}' {total_lines} 行"
                     f"（预算 {budget_lines} 行）"),
                    total_lines, budget_lines,
                    "按执行阶段提取同模块私有子函数或收敛实体职责"))
        except Exception:
            logger.warning("[SizeCheckEngine] 预算扫描降级（不影响体积检查）",
                           exc_info=True)
@dataclass
class GuardedCode:
    code: str
    original_hash: str
    diag_trail: list[dict]
    decision: GuardDecision
    violations_blocked: int
    violations_warned: int
    pre_score: float = 0.0
    total_lines: int = 0
    func_count: int = 0
    class_count: int = 0
    size_violations: int = 0
    @property
    def is_clean(self) -> bool:
        return self.decision == GuardDecision.ALLOW and self.violations_blocked == 0
    def summary(self) -> dict[str, Any]:
        return {
            "decision": self.decision.value,
            "blocked": self.violations_blocked,
            "warned": self.violations_warned,
            "pre_score": self.pre_score,
            "total_lines": self.total_lines,
            "func_count": self.func_count,
            "class_count": self.class_count,
            "size_violations": self.size_violations,
            "is_clean": self.is_clean,
        }
class DiagnosePhase(Enum):
    PRE_WRITE = "pre_write"
_BLOCKING_SEVERITY_CEILING = SEVERITY_RANK["ERROR"]
def _is_blocking_severity(severity: Any) -> bool:
    rank = SEVERITY_RANK.get(severity_text_value(severity) or "")
    if rank is None:
        return True
    return rank <= _BLOCKING_SEVERITY_CEILING
@dataclass
class _PhaseState:
    diag_trail: list[dict] = field(default_factory=list)
    blocked: list[dict] = field(default_factory=list)
    warned: list[dict] = field(default_factory=list)
    size_stats: dict[str, Any] = field(default_factory=lambda: {
        "total_lines": 0, "func_count": 0, "class_count": 0,
        "size_violations": 0,
    })
    def record_block(self, violation: dict) -> None:
        self._record(violation, "block", self.blocked)
    def record_warn(self, violation: dict) -> None:
        self._record(violation, "warn", self.warned)
    def _record(self, violation: dict, decision: str,
                bucket: list[dict]) -> None:
        bucket.append(violation)
        self.diag_trail.append({**violation,
                                "phase": DiagnosePhase.PRE_WRITE.value,
                                "decision": decision})
    def record_violation(self, violation: dict,
                         shadowed_by: str | None = None) -> None:
        if shadowed_by:
            self.record_shadowed(violation, shadowed_by)
        elif _is_blocking_severity(violation.get('severity')):
            self.record_block(violation)
        else:
            self.record_warn(violation)
    def record_size_block(self, violation: dict) -> None:
        self.record_block(violation)
        self.size_stats["size_violations"] += 1
    def record_size_warn(self, violation: dict) -> None:
        self.record_warn(violation)
        self.size_stats["size_violations"] += 1
    def record_degraded(self, entry: dict) -> None:
        self.diag_trail.append({**entry,
                                 "phase": DiagnosePhase.PRE_WRITE.value,
                                 "decision": "degraded"})
    def record_shadowed(self, violation: dict, shadowed_by: str) -> None:
        self.diag_trail.append({**violation,
                                 "phase": DiagnosePhase.PRE_WRITE.value,
                                 "decision": "shadowed",
                                 "shadowed_by": shadowed_by})
def _cie_same_root_shadowed(v: dict, state: _PhaseState) -> str | None:
    root_ids = CIE_WRITE_SAME_ROOT_RULE_IDS.get(str(v.get("rule_id")))
    line = v.get("line")
    if (not root_ids or not isinstance(line, int)
            or isinstance(line, bool) or line <= 0):
        return None
    for prior in (*state.blocked, *state.warned):
        if (prior.get("line") == line
                and str(prior.get("rule_id")) in root_ids):
            return str(prior.get("rule_id"))
    return None
def _coerce_cie_score(value: Any) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return 100.0
    if isinstance(value, float) and not math.isfinite(value):
        return 100.0
    return float(value)
def _syntax_block_entry(message: str) -> dict:
    return {"rule_id": "SYNTAX-ERROR", "message": message,
            "severity": "CRITICAL"}
def _syntax_block_reason(exc: BaseException) -> str:
    if isinstance(exc, RecursionError):
        return f"解析递归超限（嵌套过深）: {exc}"
    if isinstance(exc, MemoryError):
        return f"解析器栈溢出（源码过于复杂）: {exc}"
    return f"语法错误: {exc}"
def _dict_findings(findings: Any, channel: str) -> list[dict]:
    if findings is None:
        return []
    if not isinstance(findings, (list, tuple)):
        raise TypeError(
            f"{channel} 须为 list/tuple，得到 {type(findings).__name__}")
    for index, finding in enumerate(findings):
        if not isinstance(finding, dict):
            raise TypeError(
                f"{channel}[{index}] 须为 dict，得到 "
                f"{type(finding).__name__}")
    return list(findings)
def _build_guard_result(
    code: str, code_hash: str, decision: GuardDecision,
    diag_score: float, filepath: str, state: _PhaseState
) -> GuardedCode:
    stats = state.size_stats
    logger.info(
        "[WriteGuard] %s: decision=%s, blocked=%d, warned=%d, pre_score=%.1f, "
        "lines=%d, funcs=%d, classes=%d, size_violations=%d",
        filepath or "<code>",
        decision.value,
        len(state.blocked),
        len(state.warned),
        diag_score,
        stats.get("total_lines", 0),
        stats.get("func_count", 0),
        stats.get("class_count", 0),
        stats.get("size_violations", 0),
    )
    return GuardedCode(
        code=code,
        original_hash=code_hash,
        diag_trail=state.diag_trail,
        decision=decision,
        violations_blocked=len(state.blocked),
        violations_warned=len(state.warned),
        pre_score=diag_score,
        total_lines=stats.get("total_lines", 0),
        func_count=stats.get("func_count", 0),
        class_count=stats.get("class_count", 0),
        size_violations=stats.get("size_violations", 0),
    )
def _block_physical_code(code_text: str, reason: str,
                         filepath: str) -> GuardedCode:
    state = _PhaseState()
    state.record_block(_syntax_block_entry(reason))
    return _build_guard_result(code_text, _safe_text_md5(code_text),
                               GuardDecision.BLOCK, 0.0, filepath, state)
def _block_non_str_code(code: Any, filepath: str) -> GuardedCode:
    reason = f"非字符串源码输入({type(code).__name__})，物理上不可写盘"
    try:
        text = str(code)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='_block_non_str_code:Exc')
        text = f"<unstringifiable {type(code).__name__} input>"
    return _block_physical_code(text, reason, filepath)
def _block_unencodable_code(code: str, filepath: str,
                            exc: UnicodeEncodeError) -> GuardedCode:
    reason = (
        f"UTF-8 不可编码源码（{exc.reason}，位置 {exc.start}），"
        "物理上不可写盘（代理孤点/病态编码形态）")
    return _block_physical_code(code, reason, filepath)
def _bom_cookie_conflict_error(
        code: str | bytes | bytearray) -> str | None:
    if isinstance(code, str):
        if not code.startswith("\ufeff"):
            return None
        raw = code.encode("utf-8", errors="surrogatepass")
    else:
        raw = bytes(code)
        if not raw.startswith(b"\xef\xbb\xbf"):
            return None
    try:
        tokenize.detect_encoding(io.BytesIO(raw).readline)
    except (LookupError, SyntaxError) as exc:
        return f"源码编码声明非法，无法安全写盘: {exc}"
    return None
def _utf8_write_roundtrip_error(code: str, raw: bytes) -> str | None:
    try:
        encoding = tokenize.detect_encoding(io.BytesIO(raw).readline)[0]
    except (LookupError, SyntaxError) as exc:
        return f"源码编码声明非法，无法安全写盘: {exc}"
    try:
        decoded = raw.decode(encoding)
    except UnicodeDecodeError as exc:
        return (
            f"源码编码声明 {encoding!r} 与 UTF-8 写盘不兼容: {exc}；"
            "请更正 coding 声明或改用 UTF-8 源码")
    if decoded != code:
        return (
            f"源码编码声明 {encoding!r} 与 UTF-8 写盘不兼容，"
            "按声明回读会改变源码内容；请更正 coding 声明或改用 UTF-8 源码")
    return None
class WriteGuard:
    def __init__(self, strict: bool = True, enable_size_guard: bool = True):
        self.strict = strict
        self.enable_size_guard = enable_size_guard
        self._cie_engine = CodeInjectionEngine()
        self._size_engine = SizeCheckEngine()
    def guard(
        self,
        code: str,
        filepath: str = _DEFAULT_FILEPATH,
    ) -> GuardedCode:
        filepath = normalize_filepath(filepath)
        if not isinstance(code, str):
            return _block_non_str_code(code, filepath)
        bom_error = _bom_cookie_conflict_error(code)
        if bom_error is not None:
            return _block_physical_code(code, bom_error, filepath)
        code = strip_bom(code)
        try:
            raw_code = code.encode("utf-8")
        except UnicodeEncodeError as exc:
            log_swallowed(__name__, exc, context='WriteGuard.guard:UnicodeEncodeError')
            return _block_unencodable_code(code, filepath, exc)
        encoding_error = _utf8_write_roundtrip_error(code, raw_code)
        if encoding_error is not None:
            return _block_physical_code(code, encoding_error, filepath)
        code_hash = _safe_text_md5(code)
        state = _PhaseState()
        tree = self._pre_write_syntax_check(code, filepath, state)
        if tree is None:
            decision = self._pre_write_decide(state)
            return _build_guard_result(code, code_hash, decision, 0.0, filepath, state)
        self._pre_write_ast_security(tree, code, state)
        self._record_patch_fix_blocks(code, filepath, state)
        if self.enable_size_guard:
            self._pre_write_size_check(tree, code, filepath, state)
        diag_score, cie_degraded = self._pre_write_cie_diag(
            code, filepath, state)
        decision = self._pre_write_decide(state, cie_degraded)
        return _build_guard_result(code, code_hash, decision, diag_score, filepath, state)
    def _pre_write_syntax_check(
        self, code: str, filepath: str, state: _PhaseState
    ) -> ast.AST | None:
        tree, parse_err = _parse_module_with_semantics(
            code, filepath or "<write-guard>")
        if tree is not None:
            return tree
        if parse_err is not None:
            logger.warning("[WriteGuard] 语法解析失败转硬阻断: %s", parse_err)
            state.record_block(
                _syntax_block_entry(_syntax_block_reason(parse_err)))
        return None
    def _pre_write_ast_security(
        self, tree: ast.AST, code: str, state: _PhaseState,
    ) -> None:
        for violation in scan_write_redlines(tree, code):
            state.record_violation(violation)
    def _record_patch_fix_blocks(self, code: str, filepath: str,
                                 state: _PhaseState) -> None:
        for issue in _new_patch_fix_issues(code, filepath):
            state.record_block({
                "rule_id": "NO-PATCH-FIX",
                "message": issue.message,
                "severity": "CRITICAL",
            })
    def _pre_write_size_check(self, tree: ast.AST, code: str,
                              filepath: str, state: _PhaseState) -> None:
        scan = self._size_engine.check(tree, code, filepath)
        state.size_stats["total_lines"] = scan.total_lines
        state.size_stats["func_count"] = scan.func_count
        state.size_stats["class_count"] = scan.class_count
        for violation in scan.blocking:
            state.record_size_block(violation)
        for violation in scan.warning:
            state.record_size_warn(violation)
    def _pre_write_cie_diag(
        self, code: str, filepath: str, state: _PhaseState
    ) -> tuple[float, bool]:
        diag_score = 100.0
        degraded = False
        try:
            vr = self._cie_engine.verify_with_debt_gate(
                code, "code_write", filepath)
            if not isinstance(vr, dict):
                raise TypeError(f"CIE 引擎返回非 dict 结果: {type(vr).__name__}")
            diag_score = _coerce_cie_score(vr.get('score'))
            seen: set[tuple[str, str, str]] = set()
            blocked_before = len(state.blocked)
            self._record_cie_findings(
                _dict_findings(vr.get('violations'), 'CIE violations'),
                state, seen)
            self._record_cie_findings(
                _dict_findings(vr.get('warnings'), 'CIE warnings'),
                state, seen, warning_only=True)
            self._record_debt_gate(
                vr, state,
                findings_blocked=len(state.blocked) > blocked_before)
        except Exception as e:  # noqa: BLE001
            logger.debug("[WriteGuard] CIE 引擎不可用: %s,降级为 AST 扫描器", e)
            state.record_degraded({
                "rule_id": "CIE-DEGRADED",
                "message": f"CIE 引擎不可用,降级为 AST 扫描器: {e}",
                "severity": "INFO",
            })
            degraded = True
        return diag_score, degraded
    def _record_cie_findings(self, findings, state: _PhaseState,
                             seen: set[tuple[str, str, str]],
                             warning_only: bool = False) -> None:
        if not isinstance(findings, (list, tuple)):
            findings = []
        for finding in findings:
            if not isinstance(finding, dict):
                continue
            severity = (severity_text_value(finding.get('severity'))
                        or ('MEDIUM' if warning_only else 'CRITICAL'))
            entry = {
                "rule_id": finding.get('rule_id', 'UNKNOWN'),
                "message": finding.get('message', ''),
                "severity": severity,
                "line": finding.get('line'),
            }
            identity = (str(entry["rule_id"]), str(entry["line"]),
                        str(entry["message"]))
            if identity in seen:
                continue
            seen.add(identity)
            shadowed_by = _cie_same_root_shadowed(finding, state)
            if shadowed_by:
                state.record_shadowed(entry, shadowed_by)
            elif warning_only:
                state.record_warn(entry)
            else:
                state.record_violation(entry)
    def _record_debt_gate(self, vr: dict, state: _PhaseState, *,
                          findings_blocked: bool) -> None:
        debt_gate = str(vr.get('gate') or 'PASS').strip().upper()
        if debt_gate not in ('BLOCK', 'WARN'):
            return
        debt_dict = vr.get('debt_report')
        if not isinstance(debt_dict, dict):
            debt_dict = {}
        if debt_gate == 'BLOCK' and findings_blocked:
            return
        debt_msg = "技术债务超限: score={}, issues={}".format(
            debt_dict.get('total_score', '?'),
            self._debt_issue_count(debt_dict),
        )
        record = state.record_block if debt_gate == 'BLOCK' else state.record_warn
        record({
            "rule_id": "DEBT-GATE",
            "message": debt_msg,
            "severity": "HIGH" if debt_gate == 'BLOCK' else "MEDIUM",
        })
    @staticmethod
    def _debt_issue_count(debt_dict: dict) -> int:
        issues = debt_dict.get('issues')
        return len(issues) if isinstance(issues, (list, tuple)) else 0
    def _pre_write_decide(self, state: _PhaseState,
                          cie_degraded: bool = False) -> GuardDecision:
        if state.blocked:
            if self.strict or any(is_always_block_finding(b)
                                  for b in state.blocked):
                return GuardDecision.BLOCK
            return GuardDecision.WARN
        if state.warned:
            return GuardDecision.WARN
        if cie_degraded:
            return GuardDecision.DEGRADED
        return GuardDecision.ALLOW
class WriteBlockedError(Exception):
    def __init__(self, guarded: GuardedCode):
        self.guarded = guarded
        blocks = [t for t in guarded.diag_trail if t.get("decision") == "block"]
        msg = f"WriteGuard 阻断: {len(blocks)} 个违规"
        if blocks:
            msg += f" — {blocks[0].get('rule_id')}: {blocks[0].get('message')}"
        super().__init__(msg)
class GenEntryGuard:
    def __init__(
            self, thresholds: dict | None = None,
            strict: bool = EntryGateConfig.strict,
            skill_dir: str = EntryGateConfig.skill_dir,
            enable_registry_gate: bool = EntryGateConfig.enable_registry_gate,
            registry_exclude_ids: set[str] | None = (
                EntryGateConfig.registry_exclude_ids),
            registry_block_severity: str = (
                EntryGateConfig.registry_block_severity),
            logic_block_severity: str = (
                EntryGateConfig.logic_block_severity)) -> None:
        if not isinstance(thresholds, dict):
            if thresholds:
                logger.warning(
                    "[GenEntryGuard] thresholds 非 dict（%s），按空覆盖降级",
                    type(thresholds).__name__,
                )
            thresholds = {}
        config = EntryGateConfig.build(
            strict=strict,
            enable_registry_gate=enable_registry_gate,
            skill_dir=skill_dir,
            registry_exclude_ids=registry_exclude_ids,
            registry_block_severity=registry_block_severity,
            logic_block_severity=logic_block_severity,
        )
        self.strict = config.strict
        self.enable_registry_gate = config.enable_registry_gate
        self.skill_dir = config.skill_dir
        self.registry_exclude_ids = config.registry_exclude_ids
        self.registry_block_severity = config.registry_block_severity
        self.logic_block_severity = config.logic_block_severity
        self.gen_guard = _GenerationGuard(thresholds=thresholds)
        self.thresholds = self.gen_guard.thresholds
        self.write_guard = WriteGuard(strict=self.strict)
        self.diag_gate = DiagnoseGate(strict=self.strict)
        self._guard_count = 0
        self._block_count = 0
        self._session_p0_count = 0
        self._runner = _GateRunner(self)
    def get_stats(self) -> dict:
        return {
            "guard_count": self._guard_count,
            "block_count": self._block_count,
            "block_rate": self._block_count / max(self._guard_count, 1),
        }
    def before_write(self, code: str, filepath: str) -> EntryResult:
        self._guard_count += 1
        if not isinstance(code, (str, bytes, bytearray)):
            result = EntryResult.begin("", filepath)
            result.record_blocked(
                f"输入契约违约: code 参数须为 str，得到 "
                f"{type(code).__name__}，无源码可写盘")
            return self._finalize_decision(result, result.filepath)
        bom_error = _bom_cookie_conflict_error(code)
        if bom_error is not None:
            result = EntryResult.begin("", filepath)
            result.record_blocked(bom_error)
            return self._finalize_decision(result, result.filepath)
        if isinstance(code, (bytes, bytearray)):
            decoded_code = decode_source(bytes(code))
            if decoded_code is None:
                result = EntryResult.begin("", filepath)
                result.record_blocked(
                    "输入契约违约: bytes 源码无法按 PEP 263 编码声明严格解码"
                    "（无效字节或非法编码声明），已阻断写入")
                return self._finalize_decision(result, result.filepath)
            code = decoded_code
        code = _normalize_code(code)
        result = EntryResult.begin(code, filepath)
        code, filepath = result.code, result.filepath
        self._runner._gate1_structure(code, filepath, result)
        self._runner._gate2_security(code, filepath, result)
        self._runner._gate3_antipattern(code, filepath, result)
        self._runner._gate_norms_preflight(code, filepath, result)
        run_registry_gate(
            code, filepath, result,
            enable=self.enable_registry_gate,
            exclude_ids=self.registry_exclude_ids,
            block_severity=self.registry_block_severity,
            logic_block_severity=self.logic_block_severity,
            skill_dir=self.skill_dir,
        )
        attach_issue_examples(list(result.gen_issues) + list(result.diag_issues))
        return self._finalize_decision(result, filepath)
    def _finalize_decision(self, result: EntryResult, filepath: str) -> EntryResult:
        result.total_issues = len(result.errors) + len(result.warnings)
        result.warn_count = len(result.warnings)
        if result.errors:
            result.decision = EntryDecision.BLOCK
            self._block_count += 1
            result.ok = False
            logger.warning("[GenEntryGuard] before_write BLOCK: %d errors, %d warnings | %s",
                         len(result.errors), len(result.warnings), filepath)
            return result
        result.ok = True
        if result.needs_split:
            result.decision = EntryDecision.SPLIT_REQUIRED
            logger.info("[GenEntryGuard] before_write SPLIT_REQUIRED: %d warnings | %s",
                      len(result.warnings), filepath)
        elif result.warnings and self.strict:
            result.decision = EntryDecision.WARN
            logger.info("[GenEntryGuard] before_write WARN: %d warnings | %s",
                      len(result.warnings), filepath)
        else:
            result.decision = EntryDecision.ALLOW
        return result
def _degrade_gate_blocked(result: EntryResult, tag: str, label: str,
                          engine: str, exc: BaseException) -> None:
    result.degrade_gate(tag, label, engine, exc)
    result.record_blocked(
        f"[{tag}] {label}门禁未完成，无有效扫描结果，阻断写入: {exc}")
_GATE2_DETAIL_LIMIT = 5
_GATE2_DETAIL_TEXT_LIMIT = 120
def _gate2_blocked_trails(wg_result: GuardedCode) -> list[dict]:
    # WriteGuard 的阻断明细（规则号/文案/行号）只存在于 diag_trail；
    # 仅转发计数会让调用方拿到「N 个阻断级问题」却无从定位修复项。
    return [trail for trail in wg_result.diag_trail
            if isinstance(trail, dict) and trail.get("decision") == "block"]
def _gate2_trail_line(trail: dict) -> int:
    line = trail.get("line")
    if isinstance(line, bool) or not isinstance(line, int) or line <= 0:
        return 0
    return line
def _gate2_block_detail(blocks: list[dict]) -> str:
    if not blocks:
        return ""
    parts: list[str] = []
    for trail in blocks[:_GATE2_DETAIL_LIMIT]:
        line = trail.get("line")
        message = str(trail.get('message') or '')
        location = (f" (行{line})"
                    if isinstance(line, int) and not isinstance(line, bool)
                    and line > 0 and f"行{line}" not in message else "")
        parts.append(
            f"[{trail.get('rule_id')}] "
            f"{message[:_GATE2_DETAIL_TEXT_LIMIT]}{location}")
    suffix = " …" if len(blocks) > _GATE2_DETAIL_LIMIT else ""
    return f"——{'；'.join(parts)}{suffix}"


class _GateRunner:
    def __init__(self, host: GenEntryGuard) -> None:
        self._host = host
    def _gate1_structure(self, code: str, filepath: str, result: EntryResult) -> None:
        try:
            gen_result = self._host.gen_guard.before_write(code, filepath)
            for issue in gen_result.issues:
                sev = gate_issue_severity(issue)
                msg = f"[结构质量] {issue.code}: {issue.message}"
                result.gen_issues.append({
                    "code": issue.code, "message": issue.message,
                    "severity": sev, "line": issue.line,
                    "suggestion": issue.suggestion,
                })
                if sev in ("BLOCK", "ERROR"):
                    result.record_blocked(msg)
                elif sev == "WARN":
                    result.warnings.append(msg)
            result.needs_split = gen_result.needs_split
            if gen_result.split_plan:
                result.split_plan = [
                    {
                        "target_module": item.target_module,
                        "symbols": item.symbols,
                        "strategy": getattr(item.strategy, 'value', str(item.strategy)),
                        "rationale": item.rationale,
                        "estimated_lines": item.estimated_lines,
                    }
                    for item in gen_result.split_plan
                ]
        except Exception as e:  # noqa: BLE001
            log_swallowed(__name__, e, context='_GateRunner._gate1_structure:Exc')
            _degrade_gate_blocked(
                result, "Gate1", "结构质量", "GenerationGuard", e)
    def _gate2_security(self, code: str, filepath: str, result: EntryResult) -> None:
        try:
            wg_result = self._host.write_guard.guard(code, filepath)
            _blocks = _gate2_blocked_trails(wg_result)
            _detail = _gate2_block_detail(_blocks)
            if wg_result.decision == GuardDecision.BLOCK:
                for _trail in _blocks:
                    result.diag_issues.append(diag_issue_entry(
                        str(_trail.get("rule_id") or "WRITE-BLOCK"),
                        str(_trail.get("message") or ""),
                        str(_trail.get("severity") or "BLOCK"),
                        _gate2_trail_line(_trail),
                        str(_trail.get("fix_suggestion") or "")))
                result.record_blocked(
                    f"安全扫描阻断: {wg_result.violations_blocked} 个阻断级问题"
                    f"{_detail}",
                    wg_result.violations_blocked,
                )
            else:
                if wg_result.violations_blocked:
                    result.warnings.append(
                        f"安全扫描警告: {wg_result.violations_blocked} 个阻断级问题已降级（宽松模式）"
                        f"{_detail}")
                if wg_result.violations_warned:
                    result.warnings.append(f"安全扫描警告: {wg_result.violations_warned} 个警告级问题")
                if wg_result.decision == GuardDecision.DEGRADED:
                    result.warnings.append(
                        "[Gate2] CIE 诊断引擎降级: 诊断面收缩为 AST 基础扫描")
        except Exception as e:  # noqa: BLE001
            log_swallowed(__name__, e, context='_GateRunner._gate2_security:Exc')
            result.record_blocked(
                f"[Gate2] 安全合规门禁执行异常，无有效扫描结果，阻断写入: {e}")
    def _record_bug_intercept(self, check_id: str, sev: str, filepath: str,
                              line_num: int | None = None,
                              suggestion: str | None = None) -> None:
        try:
            write_bug_intercept(check_id, sev, filepath, line_num or 0,
                                suggestion=suggestion or "",
                                skill_dir=self._host.skill_dir)
        except Exception as exc:  # noqa: BLE001
            log_swallowed(
                __name__, exc, context=f"write_bug_intercept:{check_id}")
    def _gate3_antipattern(self, code: str, filepath: str, result: EntryResult) -> None:
        try:
            dg_result = self._host.diag_gate.check(code, filepath)
            for issue in dg_result.issues:
                self._process_gate3_issue(issue, filepath, result)
        except Exception as e:  # noqa: BLE001
            log_swallowed(__name__, e, context='_GateRunner._gate3_antipattern:Exc')
            _degrade_gate_blocked(
                result, "Gate3", "反模式", "DiagnoseGate", e)
    def _process_gate3_issue(self, issue: Any, filepath: str,
                             result: EntryResult) -> None:
        sev = gate_issue_severity(issue)
        check_id = str(issue.check_id or "")
        msg = diag_line("[反模式]", check_id, issue.message, issue.line or 0)
        result.diag_issues.append(diag_issue_entry(
            check_id, issue.message, sev, issue.line, issue.suggestion))
        if sev == "WARN":
            result.warnings.append(msg)
            return
        if sev not in ("BLOCK", "ERROR"):
            return
        if not commit_blocked(
                check_id, issue.line, filepath, result, msg,
                block_exempt=True, skill_dir=self._host.skill_dir):
            return
        if check_id.startswith('B'):
            self._record_bug_intercept(
                check_id, sev, filepath, issue.line, issue.suggestion)
    def _gate_norms_preflight(self, code: str, filepath: str,
                             result: EntryResult) -> None:
        self._host._session_p0_count = run_write_preflight_gate(
            code, filepath, result,
            project_dir=self._host.skill_dir or "",
            session_p0_count=self._host._session_p0_count)
def _entry_result_payload(result: EntryResult, guard: GenEntryGuard) -> dict:
    return {
        "ok": result.ok,
        "filepath": result.filepath,
        "decision": result.decision.value if result.decision else "UNKNOWN",
        "warnings": result.warnings,
        "errors": result.errors,
        "needs_split": result.needs_split,
        "diag_issues": result.diag_issues,
        "stats": guard.get_stats(),
        "gen_issues": result.gen_issues,
        "split_plan": result.split_plan,
        "block_count": result.block_count,
        "total_issues": result.total_issues,
    }
def quick_guard(filepath: str = _DEFAULT_FILEPATH,
                code: str | None = None,
                skill_dir: str = EntryGateConfig.skill_dir,
                enable_registry_gate: bool = (
                    EntryGateConfig.enable_registry_gate),
                registry_exclude_ids: set[str] | None = (
                    EntryGateConfig.registry_exclude_ids)) -> dict:
    if code is None:
        code, load_error = load_quick_guard_source(filepath)
        if load_error is not None:
            return load_error
    guard = GenEntryGuard(
        skill_dir=skill_dir, enable_registry_gate=enable_registry_gate,
        registry_exclude_ids=registry_exclude_ids,
    )
    result = guard.before_write(code, filepath or "<string>")
    return _entry_result_payload(result, guard)
class BlockedError(Exception):
    def __init__(self, result: EntryResult) -> None:
        self.result = result
        super().__init__(
            f"GenEntryGuard 阻断写入 {result.filepath}: "
            f"{result.block_count} 个阻断级问题"
        )
_entry_guard: GenEntryGuard | None = None
_entry_guard_lock = threading.Lock()
def get_entry_guard() -> GenEntryGuard:
    global _entry_guard
    if _entry_guard is None:
        with _entry_guard_lock:
            if _entry_guard is None:
                _entry_guard = GenEntryGuard()
    return _entry_guard
GATE5_LOGIC_RID_RE = re.compile(r'^LV\d+$')
def query_known_fp(rule_id: str, line_num: int,
                   filepath: str = _DEFAULT_FILEPATH,
                   skill_dir: str = "", message: str = "") -> tuple[bool, str]:
    try:
        return is_known_fp(
            {
                "rule_id": rule_id,
                "line": line_num,
                "file": filepath or "(code_snippet)",
                "message": message,
            },
            skill_dir,
        )
    except Exception:
        logger.debug(
            "[GenEntryGuard] 误报库查询异常（按未命中降级）: "
            "rule=%s", rule_id, exc_info=True)
        return False, ""
def downgrade_known_fp(rule_id: str, line_num: int, filepath: str,
                       result: EntryResult, msg: str,
                       block_exempt: bool = False, *,
                       skill_dir: str = "") -> bool:
    entry = next((
        item for item in reversed(result.diag_issues)
        if isinstance(item, dict)
        and item.get("check_id") == rule_id
        and (item.get("line") or 0) == (line_num or 0)
    ), None)
    if entry is None:
        logger.debug(
            "[GenEntryGuard] 误报降级缺匹配条目（rule=%s, line=%s），"
            "按不降级处理", rule_id, line_num)
        return False
    fp_hit, fp_reason = query_known_fp(
        rule_id, line_num, filepath, skill_dir,
        message=str(entry.get("message") or ""),
    )
    if not fp_hit:
        return False
    if block_exempt and (
            severity_text_value(entry.get("severity")) or "") == "BLOCK":
        return False
    entry["severity"] = "WARN"
    entry["fp_downgraded"] = True
    result.warnings.append(f"{msg}（已知误报降级: {fp_reason}）")
    return True
def commit_blocked(rule_id: str, line_num: int, filepath: str,
                   result: EntryResult, msg: str,
                   block_exempt: bool = False, *,
                   skill_dir: str = "") -> bool:
    if downgrade_known_fp(
            rule_id, line_num, filepath, result, msg,
            block_exempt, skill_dir=skill_dir):
        return False
    result.record_blocked(msg)
    return True
def _gate5_severity_rank(sev_text: str | None,
                         rid: str) -> tuple[str, int]:
    token, rank = severity_rank_of_text(sev_text)
    if rank is not None:
        return token, rank
    logger.warning(
        "[GenEntryGuard] Gate5 未知严重度 %r（rule=%s），按最严档处置",
        sev_text, rid)
    return "CRITICAL", SEVERITY_RANK["CRITICAL"]
def _process_gate5_finding(item: dict, filepath: str, result: EntryResult,
                           blk_rank: int, logic_blk_rank: int, *,
                           skill_dir: str = "") -> None:
    rid = str(item.get("rule_id") or "")
    sev, sev_rank = _gate5_severity_rank(
        severity_text_value(item.get("severity")), rid)
    line_num = item.get("line") or 0
    detail = item.get("message") or ""
    msg = diag_line("[诊断预检]", rid, detail, line_num)
    result.diag_issues.append(diag_issue_entry(
        rid, detail, sev, line_num,
        item.get("suggestion") or "",
        fix_example=item.get("fix_example") or ""))
    _rule_blk_rank = (
        logic_blk_rank
        if GATE5_LOGIC_RID_RE.match(rid.replace('-', '').upper())
        else blk_rank)
    if sev_rank <= _rule_blk_rank:
        commit_blocked(rid, line_num, filepath, result, msg,
                       skill_dir=skill_dir)
    else:
        result.warnings.append(msg)
def run_registry_gate(code: str, filepath: str, result: EntryResult, *,
                      enable: bool = EntryGateConfig.enable_registry_gate,
                      exclude_ids: set[str] | None = (
                          EntryGateConfig.registry_exclude_ids),
                      block_severity: str = (
                          EntryGateConfig.registry_block_severity),
                      logic_block_severity: str = (
                          EntryGateConfig.logic_block_severity),
                      skill_dir: str = EntryGateConfig.skill_dir) -> None:
    try:
        config = EntryGateConfig.build(
            enable_registry_gate=enable,
            registry_exclude_ids=exclude_ids,
            registry_block_severity=block_severity,
            logic_block_severity=logic_block_severity,
            skill_dir=skill_dir,
        )
        if not config.enable_registry_gate:
            return
        pf = preflight_diagnostic_check(
            code, filepath, exclude_ids=config.registry_exclude_ids,
            min_severity="P3",
        )
        if pf.get("degraded"):
            reason = str(pf.get('degraded_reason') or '未完成扫描')
            result.warnings.append(f"[Gate5] 诊断注册表降级: {reason}")
            result.record_blocked(
                f"[Gate5] 诊断注册表未完成扫描，无有效全量结果，阻断写入: {reason}")
        _blk_rank = SEVERITY_RANK[config.registry_block_severity]
        _logic_blk_rank = SEVERITY_RANK[config.logic_block_severity]
        for item in _dict_findings(pf.get("findings"), "Gate5 findings"):
            _process_gate5_finding(
                item, filepath, result, _blk_rank, _logic_blk_rank,
                skill_dir=config.skill_dir)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context='run_registry_gate:Exc')
        _degrade_gate_blocked(result, "Gate5", "诊断注册表", "", e)

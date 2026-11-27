from __future__ import annotations

import ast
import os
import re
import time
from collections.abc import Callable
from dataclasses import asdict, dataclass, field
from functools import partial
from typing import Any, NamedTuple

import jwsgj.html_render_pipeline as _html_report_renderers
from jwsgj.diag_guard_io import (
    guarded_open,
)
from jwsgj.diag_guard_state import (
    JsonSerializableMixin,
)
from jwsgj.diag_shared_ast_nodes import (
    count_params,
    cyclomatic_complexity,
    is_main_check,
    is_placeholder_stmt,
    iter_own_scope,
    split_identifier,
)
from jwsgj.diag_shared_ast_views import collect_api_function_nodes, tree_nodes
from jwsgj.diag_types_defs import (
    ContractViolationError,
    PreCheckItem,
    PreinterventionResult,
    finish_check,
    make_detail,
    normalize_text_param,
    prepare_tree,
)
from jwsgj.diag_types_normalize import (
    format_compact_ts,
    normalize_input,
    safe_confidence,
)
from jwsgj.diag_types_vocab import (
    FIELD_SUGGESTED_VALUE,
    FMT_DATETIME,
    KEY_SEVERITIES,
    MAX_FUNCTION_COMPLEXITY,
    MAX_FUNCTION_LINES,
    MAX_PARAMETERS,
    PREINTERVENTION_VERSION,
    RULE_HIGH_COMPLEXITY,
    RULE_MISSING_DOCSTRING,
    SEVERITY_BLOCKING,
    SEVERITY_INFO,
    SEVERITY_WARNING,
    register_check_provider,
    registered_check_providers,
    registered_review_providers,
)
from jwsgj.log_config import get_module_logger, log_swallowed

__all__ = [
    "PREINTERVENTION_VERSION",
    "PreCreationReviewReport",
    "PreCreationReviewer",
    "PreinterventionReport",
    "check_api_design",
    "check_error_handling",
    "check_logging_standard",
    "check_quality_baseline",
    "run_pre_creation_review",
    "run_preintervention",
    "run_preintervention_with_lessons",
]
logger = get_module_logger(__name__, __file__)
logger.info("build_preintervention 已加载（维度契约 + 报告/执行/审查 + 样式维度）")
_LOG_METHOD_NAMES = frozenset({
    "warning", "warn", "error", "info", "debug", "exception",
    "critical", "fatal",
})
_LOGGER_SEGMENTS = frozenset({"log", "logs", "logger", "logging"})
_OUTPUT_FUNCTION_SEGMENTS = frozenset({"print", "pprint"})
def _identifier_segments(name: object) -> set[str]:
    return set(split_identifier(str(name)))
class _DimensionSpec(NamedTuple):
    check_name: str
    title: str
    severity: str
    scan: Callable[[ast.AST, str, list, list], bool]
    @property
    def public_name(self) -> str:
        return "check_" + self.check_name.removesuffix("_check")
def _run_dimension(spec: _DimensionSpec, content: str) -> PreinterventionResult:
    if content is not None and not isinstance(content, str):
        normalize_input(content, f"{spec.public_name} 参数 content")
        return _log_check_result(PreinterventionResult(
            check_name=spec.check_name,
            passed=False,
            severity=SEVERITY_BLOCKING,
            message=f"{spec.title}输入类型非法",
            details=[make_detail(
                "invalid_entry_type", _ENTRY_TYPE_RULE_ID,
                f"{spec.public_name}.content", confidence=1.0,
                expected="str", actual=type(content).__name__,
            )],
            suggestions=["传入 str 源码后重跑该维度检查"],
        ))
    content = normalize_input(content, f"{spec.public_name} 参数 content")
    tree, early = prepare_tree(content, spec.check_name)
    if early is not None:
        logger.debug("[preintervention] %s 前置终止: %s",
                     spec.check_name, early.message)
        return early
    details: list[dict] = []
    suggestions: list[str] = []
    passed = spec.scan(tree, content, details, suggestions)
    return _log_check_result(finish_check(
        spec.check_name, spec.title, passed, spec.severity, details, suggestions))
def _dimension_entry(spec: _DimensionSpec) -> Callable[[str], PreinterventionResult]:
    def check_dimension(content: str = "") -> PreinterventionResult:
        return _run_dimension(spec, content)
    check_dimension.__name__ = spec.public_name
    check_dimension.__qualname__ = spec.public_name
    check_dimension.__doc__ = (
        f"{spec.title}（{spec.check_name}）。\n\n"
        "Args:\n    content: 待检查源码。\n\n"
        "Returns:\n    PreinterventionResult: 该维度的检查结果。")
    return check_dimension
def _scan_api_design(tree: ast.AST, _content: str, details: list, suggestions: list) -> bool:
    passed = True
    for node, is_method in collect_api_function_nodes(tree):
        if _inspect_api_function(node, details, suggestions, is_method):
            passed = False
    return passed
_API_DESIGN = _DimensionSpec("api_design_check", "API 设计检查", SEVERITY_BLOCKING, _scan_api_design)
check_api_design = _dimension_entry(_API_DESIGN)
def _inspect_api_function(node: ast.FunctionDef | ast.AsyncFunctionDef,
                          details: list, suggestions: list,
                          is_method: bool) -> bool:
    found = False
    for rule in (_api_return_annotation_rule,
                 _api_naming_rule, _api_docstring_rule):
        if rule(node, details, suggestions):
            found = True
    if _api_parameter_count_rule(node, details, suggestions, is_method):
        found = True
    return found
def _api_return_annotation_rule(node: ast.FunctionDef | ast.AsyncFunctionDef,
                                details: list, suggestions: list) -> bool:
    if node.returns is not None or node.name.startswith("_"):
        return False
    details.append(make_detail(
        "missing_return_annotation", "API-03", "<function>", confidence=0.85,
        function=node.name,
        line=node.lineno,
    ))
    suggestions.append(f"函数 {node.name} 缺少返回值注解")
    return True
def _api_parameter_count_rule(node: ast.FunctionDef | ast.AsyncFunctionDef,
                              details: list, suggestions: list,
                              is_method: bool) -> bool:
    param_count = count_params(node, is_method=is_method)
    if node.name.startswith("_") or param_count <= MAX_PARAMETERS:
        return False
    details.append(make_detail(
        "too_many_parameters", "API-04", "<function>", confidence=0.9,
        function=node.name,
        line=node.lineno,
        params=param_count,
        threshold=MAX_PARAMETERS,
    ))
    suggestions.append(
        f"函数 {node.name} 参数数 {param_count} 过多，考虑使用参数对象")
    return True
def _api_naming_rule(node: ast.FunctionDef | ast.AsyncFunctionDef,
                     details: list, suggestions: list) -> bool:
    if node.name.startswith("_") or re.match(r'^[a-z_][a-z0-9_]*$', node.name):
        return False
    details.append(make_detail(
        "naming_violation", "API-05", "<function>", confidence=0.8,
        function=node.name,
        line=node.lineno,
        expected="snake_case",
    ))
    suggestions.append(f"函数 {node.name} 命名不符合 snake_case 规范")
    return True
def _api_docstring_rule(node: ast.FunctionDef | ast.AsyncFunctionDef,
                        details: list, suggestions: list) -> bool:
    if node.name.startswith("_") or ast.get_docstring(node) is not None:
        return False
    details.append(make_detail(
        RULE_MISSING_DOCSTRING, "API-06", "<function>", confidence=0.85,
        function=node.name,
        line=node.lineno,
    ))
    suggestions.append(f"函数 {node.name} 缺少 docstring")
    return True
def _scan_quality_baseline(tree: ast.AST, _content: str, details: list, suggestions: list) -> bool:
    passed = True
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if _check_function_length_phase(node, details, suggestions):
            passed = False
        if _check_function_complexity_phase(node, details, suggestions):
            passed = False
    return passed
_QUALITY_BASELINE = _DimensionSpec("quality_baseline_check", "质量基线检查", SEVERITY_BLOCKING, _scan_quality_baseline)
check_quality_baseline = _dimension_entry(_QUALITY_BASELINE)
def _check_function_length_phase(node: ast.FunctionDef | ast.AsyncFunctionDef,
                                 details: list[dict],
                                 suggestions: list[str]) -> bool:
    func_lines = node.end_lineno - node.lineno + 1
    if func_lines <= MAX_FUNCTION_LINES:
        return False
    details.append(make_detail(
        "function_too_long", "QUAL-01", "<function>", confidence=0.9,
        function=node.name,
        line=node.lineno,
        lines=func_lines,
        threshold=MAX_FUNCTION_LINES,
    ))
    suggestions.append(f"函数 {node.name} 有 {func_lines} 行，超过 {MAX_FUNCTION_LINES} 行阈值")
    return True
def _own_scope_complexity(node: ast.AST) -> int:
    return cyclomatic_complexity(
        node, partial(iter_own_scope, skip_lambda=True, include_self=True))
def _check_function_complexity_phase(node: ast.FunctionDef | ast.AsyncFunctionDef,
                                     details: list[dict],
                                     suggestions: list[str]) -> bool:
    complexity = _own_scope_complexity(node)
    if complexity <= MAX_FUNCTION_COMPLEXITY:
        return False
    details.append(make_detail(
        RULE_HIGH_COMPLEXITY, "QUAL-02", "<function>", confidence=0.85,
        function=node.name,
        line=node.lineno,
        complexity=complexity,
        threshold=MAX_FUNCTION_COMPLEXITY,
    ))
    suggestions.append(
        f"函数 {node.name} 圈复杂度 {complexity} 超过 {MAX_FUNCTION_COMPLEXITY}，"
        "考虑拆分条件分支"
    )
    return True
def _except_block_has_logging(node: ast.ExceptHandler) -> bool:
    return any(
        _call_is_log_or_print(child)
        for child in iter_own_scope(node, skip_lambda=True, include_self=True)
        if isinstance(child, ast.Call))
def _is_logger_name(name: str) -> bool:
    return bool(_identifier_segments(name) & _LOGGER_SEGMENTS)
def _is_logging_symbol(name: str) -> bool:
    return (_is_logger_name(name)
            or bool(_identifier_segments(name) & _OUTPUT_FUNCTION_SEGMENTS))
def _is_logger_receiver(value: ast.AST) -> bool:
    if isinstance(value, ast.Name):
        return _is_logger_name(value.id)
    if isinstance(value, ast.Attribute):
        return (_is_logger_name(value.attr)
                or _is_logger_receiver(value.value))
    if isinstance(value, ast.Call):
        func = value.func
        if isinstance(func, ast.Name):
            return _is_logger_name(func.id)
        if isinstance(func, ast.Attribute):
            return (_is_logger_name(func.attr)
                    or _is_logger_receiver(func.value))
    return False
def _call_is_log_or_print(call: ast.Call) -> bool:
    if _is_getlogger_call(call):
        return False
    func = call.func
    if isinstance(func, ast.Attribute):
        if func.attr.lower() in _LOG_METHOD_NAMES:
            return _is_logger_receiver(func.value)
        return _is_logging_symbol(func.attr)
    return (isinstance(func, ast.Name)
            and _is_logging_symbol(func.id))
_BROAD_EXCEPTION_NAMES = frozenset({"Exception", "BaseException"})
def _is_broad_exception_catch(type_node: ast.AST | None) -> bool:
    if isinstance(type_node, ast.Name):
        return type_node.id in _BROAD_EXCEPTION_NAMES
    if (isinstance(type_node, ast.Attribute)
            and isinstance(type_node.value, ast.Name)
            and type_node.value.id == "builtins"):
        return type_node.attr in _BROAD_EXCEPTION_NAMES
    if isinstance(type_node, ast.Tuple):
        return any(_is_broad_exception_catch(e) for e in type_node.elts)
    return False
def _analyze_except_handler(node: ast.ExceptHandler, details: list,
                            suggestions: list) -> bool:
    found = False
    if node.type is None:
        found = True
        details.append(make_detail(
            "bare_except", "ERR-01", "<unknown>", confidence=0.9,
            line=node.lineno,
        ))
        suggestions.append(f"L{node.lineno}: 避免使用 bare except，指定具体异常类型")
    body = node.body
    if len(body) == 1 and is_placeholder_stmt(body[0]):
        found = True
        details.append(make_detail(
            "swallowed_exception", "ERR-02", "<unknown>", confidence=0.85,
            line=node.lineno,
        ))
        suggestions.append(f"L{node.lineno}: 不要吞异常，至少记录日志")
    propagates = any(isinstance(stmt, ast.Raise) for stmt in body)
    if (node.type and _is_broad_exception_catch(node.type)
            and not propagates
            and not _except_block_has_logging(node)):
        found = True
        details.append(make_detail(
            "exception_without_logging", "ERR-03", "<unknown>", confidence=0.8,
            line=node.lineno,
        ))
        suggestions.append(f"L{node.lineno}: except Exception/BaseException 块中应记录日志")
    return found
def _scan_error_handling(tree: ast.AST, _content: str, details: list, suggestions: list) -> bool:
    passed = True
    for node in tree_nodes(tree):
        if isinstance(node, ast.ExceptHandler) and _analyze_except_handler(
                node, details, suggestions):
            passed = False
    return passed
_ERROR_HANDLING = _DimensionSpec("error_handling_check", "错误处理检查", SEVERITY_WARNING, _scan_error_handling)
check_error_handling = _dimension_entry(_ERROR_HANDLING)
def _is_print_call(node: ast.AST) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    if isinstance(func, ast.Name):
        return func.id in _OUTPUT_FUNCTION_SEGMENTS
    return (isinstance(func, ast.Attribute)
            and func.attr in _OUTPUT_FUNCTION_SEGMENTS)
def _walk_loop_scope(loop_node: ast.AST, *, skip_orelse: bool = False,
                     annotations_evaluated: bool = True):
    stack = [loop_node]
    while stack:
        cur = stack.pop()
        yield cur
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            if not isinstance(cur, ast.Lambda):
                stack.extend(cur.decorator_list)
                if annotations_evaluated:
                    parameters = (*cur.args.posonlyargs, *cur.args.args,
                                  *cur.args.kwonlyargs)
                    if cur.args.vararg is not None:
                        parameters += (cur.args.vararg,)
                    if cur.args.kwarg is not None:
                        parameters += (cur.args.kwarg,)
                    stack.extend(arg.annotation for arg in parameters
                                 if arg.annotation is not None)
                    if cur.returns is not None:
                        stack.append(cur.returns)
            stack.extend(cur.args.defaults)
            stack.extend(default for default in cur.args.kw_defaults
                         if default is not None)
            continue
        children = list(ast.iter_child_nodes(cur))
        if skip_orelse and cur is loop_node and isinstance(
                cur, (ast.For, ast.AsyncFor, ast.While)):
            orelse_ids = {id(stmt) for stmt in cur.orelse}
            children = [child for child in children
                        if id(child) not in orelse_ids]
        stack.extend(children)
def _collect_main_guard_prints(tree: ast.Module) -> set:
    return {
        id(sub)
        for node in tree_nodes(tree)
        if isinstance(node, ast.If) and is_main_check(node.test)
        for stmt in node.body
        for sub in _walk_loop_scope(stmt)
        if _is_print_call(sub)
    }
def _check_print_as_logging(tree: ast.Module, details: list, suggestions: list) -> int:
    main_block_prints = _collect_main_guard_prints(tree)
    found = 0
    for node in tree_nodes(tree):
        if _is_print_call(node):
            if id(node) in main_block_prints:
                continue
            found += 1
            details.append(make_detail(
                "print_as_logging", "LOG-01",
                f"line:{node.lineno}", confidence=0.55,
            ))
            suggestions.append(f"L{node.lineno}: 建议使用logging替代print")
    return found
def _is_getlogger_call(value: ast.AST) -> bool:
    if not isinstance(value, ast.Call):
        return False
    func = value.func
    if isinstance(func, ast.Attribute):
        return func.attr in {"getLogger", "get_logger"}
    return (isinstance(func, ast.Name)
            and func.id in {"getLogger", "get_logger"})
def _is_logger_getlogger_assign(target: ast.AST, value: ast.AST) -> bool:
    return (isinstance(target, ast.Name) and _is_logger_name(target.id)
            and _is_getlogger_call(value))
def _mentions_dunder_name(node: ast.AST) -> bool:
    return any(isinstance(sub, ast.Name) and sub.id == "__name__"
               for sub in tree_nodes(node))
def _getlogger_uses_dunder_name(call: ast.Call) -> bool:
    args = call.args
    if args and _mentions_dunder_name(args[0]):
        return True
    return any(kw.arg == "name" and _mentions_dunder_name(kw.value)
               for kw in call.keywords)
def _check_logger_naming(tree: ast.Module, details: list, suggestions: list) -> int:
    found = 0
    for node in tree_nodes(tree):
        if isinstance(node, ast.Assign):
            targets = node.targets
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
        else:
            continue
        for target in targets:
            if (_is_logger_getlogger_assign(target, node.value)
                    and not _getlogger_uses_dunder_name(node.value)):
                found += 1
                details.append(make_detail(
                    "logger_naming", "LOG-02",
                    f"line:{node.lineno}", confidence=0.60,
                ))
                suggestions.append(f"L{node.lineno}: 建议使用 logging.getLogger(__name__)")
    return found
def _scan_logging_standard(tree: ast.AST, _content: str, details: list, suggestions: list) -> bool:
    found = _check_print_as_logging(tree, details, suggestions)
    found += _check_logger_naming(tree, details, suggestions)
    return not found
_LOGGING_STANDARD = _DimensionSpec("logging_standard_check", "日志规范检查", SEVERITY_WARNING, _scan_logging_standard)
check_logging_standard = _dimension_entry(_LOGGING_STANDARD)
def _style_check_provider() -> dict:
    return {
        "api_design_check": check_api_design,
        "error_handling_check": check_error_handling,
        "logging_standard_check": check_logging_standard,
        "quality_baseline_check": check_quality_baseline,
    }
register_check_provider(_style_check_provider)
def _log_check_result(result: PreinterventionResult) -> PreinterventionResult:
    if result.passed:
        logger.debug("[preintervention] %s 通过（%d 项明细）",
                     result.check_name, len(result.details))
    else:
        logger.info("[preintervention] %s 未通过 severity=%s 明细 %d 项",
                    result.check_name, result.severity, len(result.details))
    return result
def _persist_json(output_path: str, payload: str) -> None:
    try:
        with guarded_open(output_path, "w", encoding="utf-8") as handle:
            handle.write(payload)
    except (OSError, ValueError, ContractViolationError) as e:
        logger.warning("to_json 写盘失败（%s）: %s", output_path, e)
@dataclass
class PreinterventionReport(JsonSerializableMixin):
    version: str = PREINTERVENTION_VERSION
    timestamp: str = ""
    skill_name: str = ""
    results: list[PreinterventionResult] = field(default_factory=list)
    _enhanced: bool = False
    _lessons: list = field(default_factory=list)
    _lessons_count: int = 0
    _crosscheck: Any = None
    _memory_warnings: list = field(default_factory=list)
    _memory_suggestions: list = field(default_factory=list)
    _memory_known_patterns: dict = field(default_factory=dict)
    def _failed_at(self, severity: str) -> list[PreinterventionResult]:
        return [r for r in self.results if not r.passed and r.severity == severity]
    @property
    def blocking_issues(self) -> list[PreinterventionResult]:
        return self._failed_at(SEVERITY_BLOCKING)
    @property
    def warning_issues(self) -> list[PreinterventionResult]:
        return self._failed_at(SEVERITY_WARNING)
    @property
    def info_issues(self) -> list[PreinterventionResult]:
        return self._failed_at(SEVERITY_INFO)
    def has_blocking(self) -> bool:
        return bool(self.blocking_issues)
    def has_warning(self) -> bool:
        return bool(self.warning_issues)
    def _severity_counts(self) -> dict:
        return {
            "blocking_count": len(self.blocking_issues),
            "warning_count": len(self.warning_issues),
            "info_count": len(self.info_issues),
        }
    def _enhanced_fields(self) -> dict:
        fields = {
            "enhanced": True,
            "lessons": self._lessons,
            "lessons_count": self._lessons_count,
            "crosscheck": self._crosscheck,
        }
        if self._memory_warnings or self._memory_suggestions:
            fields["memory_warnings"] = self._memory_warnings
            fields["memory_suggestions"] = self._memory_suggestions
        if self._memory_known_patterns:
            fields["memory_known_patterns"] = self._memory_known_patterns
        return fields
    def to_dict(self) -> dict:
        data = {
            "version": self.version,
            "timestamp": self.timestamp,
            "skill_name": self.skill_name,
            "total_checks": len(self.results),
            "passed_checks": sum(1 for r in self.results if r.passed),
        }
        data.update(self._severity_counts())
        data["results"] = [r.to_dict() for r in self.results]
        if self._enhanced:
            data.update(self._enhanced_fields())
        return data
    def to_json(self, indent: int = 2, *, output_path: str = "") -> str:
        if indent is not None and (isinstance(indent, bool)
                                   or not isinstance(indent, int)):
            raise TypeError(
                "to_json() 的 indent 必须是 int 或 None；"
                "写盘请使用 output_path= 关键字参数")
        data = super().to_json(indent=indent)
        if output_path:
            _persist_json(output_path, data)
        return data
def _build_degraded_result(check_name: str, detail_kind: str, detail_code: str,
                           subject: str, message: str, error: Exception,
                           suggestion: str, *,
                           severity: str = SEVERITY_WARNING) -> PreinterventionResult:
    err_text = f"{type(error).__name__}: {error}"
    return PreinterventionResult(
        check_name=check_name,
        passed=False,
        severity=severity,
        message=message,
        details=[make_detail(
            detail_kind, detail_code, subject, confidence=1.0, error=err_text,
        )],
        suggestions=[suggestion],
    )
def _run_check(check, *args) -> PreinterventionResult:
    try:
        return check(*args)
    except Exception as e:
        fname = getattr(check, "__name__", "unknown_check")
        logger.exception("[run_preintervention] 单项检查异常降级: %s", fname)
        return _build_degraded_result(
            f"{fname}_degraded", "check_degraded", "PRE-DEG-001", "<check>",
            f"检查执行异常已降级: {type(e).__name__}: {e}", e,
            "该维度检查实现或输入异常，修复后重跑预介入检查",
        )
def _degraded_preintervention_report(skill_name: str,
                                      error: Exception) -> PreinterventionReport:
    logger.error("[run_preintervention] 报告构造异常降级: %s", error)
    report = PreinterventionReport(
        version="error", timestamp="", skill_name=skill_name)
    report.results.append(_build_degraded_result(
        "run_preintervention_degraded", "report_degraded", "PRE-DEG-002",
        "<report>", f"预介入检查整体降级: {type(error).__name__}: {error}", error,
        "预介入报告构造异常，修复后重跑 run_preintervention",
        severity=SEVERITY_BLOCKING,
    ))
    return report
_ENTRY_FIELD_SPECS: tuple[tuple[str, bool, str], ...] = (
    ("skill_name", False, "str"),
    ("description", False, "str"),
    ("skill_dir", True, "str 或 os.PathLike"),
    ("content", False, "str"),
    ("filename", True, "str 或 os.PathLike"),
)
_ENTRY_TYPE_RULE_ID = "PRE-INPUT-001"
def _collect_entry_type_errors(entry: str,
                               raw_values: dict[str, object]) -> list[dict]:
    errors: list[dict] = []
    for field_name, allow_path, expected in _ENTRY_FIELD_SPECS:
        raw = raw_values.get(field_name)
        if raw is None or isinstance(raw, str):
            continue
        if allow_path and isinstance(raw, os.PathLike):
            continue
        errors.append(make_detail(
            "invalid_entry_type", _ENTRY_TYPE_RULE_ID,
            f"{entry}.{field_name}", confidence=1.0,
            expected=expected, actual=type(raw).__name__))
    return errors
def _normalize_entry_inputs(skill_name: object, description: object,
                            skill_dir: object, content: object,
                            filename: object, entry: str
                            ) -> tuple[tuple[str, str, str, str, str], list[dict]]:
    raw_values = dict(zip((spec[0] for spec in _ENTRY_FIELD_SPECS),
                          (skill_name, description, skill_dir, content,
                           filename), strict=True))
    normalized = tuple(
        normalize_input(raw_values[name], f"{entry} 参数 {name}",
                        allow_path=allow_path)
        for name, allow_path, _expected in _ENTRY_FIELD_SPECS)
    return normalized, _collect_entry_type_errors(entry, raw_values)
def _input_contract_result(errors: list[dict]) -> PreinterventionResult:
    return PreinterventionResult(
        check_name="input_contract_check",
        passed=False,
        severity=SEVERITY_BLOCKING,
        message="入口参数类型非法（已归一后继续检查）",
        details=errors,
        suggestions=["按期望类型传参（路径型参数可传 str 或 PathLike）后重跑预介入检查"],
    )
def _new_report(skill_name: str) -> PreinterventionReport:
    return PreinterventionReport(
        timestamp=format_compact_ts(int(time.time() * 1000)),
        skill_name=skill_name,
    )
_STATUS_COMPLETED = "completed"
_STATUS_DEGRADED = "degraded"
def _emit_preintervention_html(report: PreinterventionReport, skill_dir: str,
                               status: str = _STATUS_COMPLETED) -> None:
    try:
        payload = report.to_dict()
        payload["status"] = status
        payload["summary"] = (
            f"{payload.get('passed_checks', 0)}/{payload.get('total_checks', 0)} 项检查通过，"
            f"blocking {payload.get('blocking_count', 0)} / warning {payload.get('warning_count', 0)}")
        _html_report_renderers.emit_step_html("preintervention", skill_dir, payload)
    except Exception as _phe:  
        logger.warning("[preintervention] HTML 报告生成失败(不阻断): %s", _phe)
_DIMENSIONS = (
    ("architecture_check", "skill_dir", "content"),
    ("api_design_check", "content"),
    ("doc_skeleton_check", "skill_dir", "description"),
    ("import_structure_check", "content", "skill_dir", "filename"),
    ("quality_baseline_check", "content"),
    ("error_handling_check", "content"),
    ("security_design_check", "content"),
    ("performance_baseline_check", "content"),
    ("test_skeleton_check", "skill_dir", "content", "filename"),
    ("concurrency_safety_check", "content"),
    ("logging_standard_check", "content"),
    ("dependency_management_check", "skill_dir", "content", "filename"),
    ("all_declaration_check", "content"),
    ("guard_injection_check", "content"),
    ("bug_antipatterns_check", "content"),
    ("over_engineering_check", "content"),
    ("stub_portal_check", "content", "skill_dir", "filename"),
)
def _run_all_checks(report: PreinterventionReport, skill_dir: str,
                    content: str, description: str, filename: str) -> None:
    ctx = {"skill_dir": skill_dir, "content": content,
           "description": description, "filename": filename}
    impls: dict = {}
    for provider in registered_check_providers():
        impls.update(provider())
    missing = [spec[0] for spec in _DIMENSIONS if spec[0] not in impls]
    if missing:
        raise RuntimeError(f"预介入维度未装配（检查域未导入）: {missing}")
    for spec in _DIMENSIONS:
        report.results.append(
            _run_check(impls[spec[0]], *(ctx[key] for key in spec[1:])))
def _execute_preintervention(
    raw_inputs: tuple[object, object, object, object, object],
) -> tuple[PreinterventionReport, str, tuple[str, str, str, str, str]]:
    entry_values = ("", "", "", "", "")
    input_errors: list[dict] = []
    skill_name = ""
    try:
        entry_values, input_errors = _normalize_entry_inputs(
            *raw_inputs, entry="run_preintervention")
        skill_name, description, skill_dir, content, filename = entry_values
        report = _new_report(skill_name)
        if input_errors:
            report.results.append(_input_contract_result(input_errors))
        _run_all_checks(report, skill_dir, content, description, filename)
        degraded = any(
            detail.get("issue") == "check_degraded"
            for result in report.results
            for detail in result.details
            if isinstance(detail, dict)
        )
        status = _STATUS_DEGRADED if degraded else _STATUS_COMPLETED
        return report, status, entry_values
    except Exception as e:  
        log_swallowed(__name__, e, context='run_preintervention:Exc')
        report = _degraded_preintervention_report(skill_name, e)
        return report, _STATUS_DEGRADED, entry_values
_DEFAULT_ENABLE_LESSONS = True
_DEFAULT_ENABLE_CROSSCHECK = True
@dataclass(frozen=True)
class _EntryEnhancement:
    enable_lessons: bool = _DEFAULT_ENABLE_LESSONS
    enable_crosscheck: bool = _DEFAULT_ENABLE_CROSSCHECK
    memory_context: Any | None = None
def _execute_and_emit(
    raw_inputs: tuple[object, object, object, object, object],
    enhancement: _EntryEnhancement | None = None,
) -> PreinterventionReport:
    report, status, entry_values = _execute_preintervention(raw_inputs)
    skill_name, description, skill_dir, content, filename = entry_values
    if enhancement is not None:
        lessons = (_inject_history_lessons(skill_dir)
                   if enhancement.enable_lessons else [])
        crosscheck = (_run_precreation_crosscheck(
            skill_dir, content, filename, skill_name, description)
            if enhancement.enable_crosscheck else None)
        if enhancement.enable_crosscheck and crosscheck is None:
            status = _STATUS_DEGRADED
        if enhancement.memory_context:
            _apply_memory_enhancement(
                report, description, content, enhancement.memory_context)
        report._enhanced = True
        report._lessons = lessons
        report._crosscheck = crosscheck
        report._lessons_count = len(lessons)
    _emit_preintervention_html(report, skill_dir, status=status)
    return report
def run_preintervention(
    skill_name: str = "",
    description: str = "",
    skill_dir: str | os.PathLike = "",
    content: str = "",
    filename: str = "",
) -> PreinterventionReport:
    return _execute_and_emit(
        (skill_name, description, skill_dir, content, filename))
_REVIEW_COLLABORATORS: tuple[tuple[str, str], ...] = (
    ("precreation_history_lessons", "历史经验注入器工厂（入参：skill_dir）"),
    ("precreation_review_gate", "严格门禁实例工厂"),
    ("precreation_code_precheck", "代码质量预检工厂（入参：门禁实例）"),
    ("precreation_doc_precheck", "SKILL.md 六维与必需章节预检工厂"),
    ("precreation_arch_advisor", "架构建议器工厂"),
    ("precreation_api_prechecks", "API 幻觉预检（入参：源码 + 文件名）"),
    ("precreation_constraint_lessons", "编写前约束转注入经验"),
)
def _resolve_review_collaborators() -> dict:
    impls = registered_review_providers()
    missing = [f"{name}({usage})" for name, usage in _REVIEW_COLLABORATORS
               if name not in impls]
    if missing:
        raise RuntimeError(f"预创建审查协作者未装配（领域未导入）: {missing}")
    return impls
_DEFAULT_REVIEW_MODE = "both"
_VALID_REVIEW_MODES = ("code_writing", "skill_creation", _DEFAULT_REVIEW_MODE)
def _normalize_review_params(
    filename: object,
    code_content: object,
    skill_name: object,
    skill_desc: object,
    module_type: object,
    prechecks: list[dict],
) -> tuple[str, str, str, str, str]:
    filename, _ = normalize_text_param(
        filename, "filename 期望 str",
        suggestion="传入 str 或 PathLike 文件名后再继续",
        applicable_to="review() 参数", allow_pathlike=True, prechecks=prechecks)
    code_content, _ = normalize_text_param(
        code_content, "code_content 期望 str",
        suggestion="传入 str 源码后再继续",
        applicable_to=filename or "code", prechecks=prechecks)
    skill_name, _ = normalize_text_param(
        skill_name, "skill_name 期望 str",
        suggestion="传入 str 技能名后再继续",
        applicable_to="review() 参数", prechecks=prechecks)
    skill_desc, _ = normalize_text_param(
        skill_desc, "skill_desc 期望 str",
        suggestion="传入 str 技能描述后再继续",
        applicable_to="review() 参数", prechecks=prechecks)
    module_type, _ = normalize_text_param(
        module_type, "module_type 期望 str",
        suggestion="传入 str 模块类型（diagnostic/validator/fixer/builder）后再继续",
        applicable_to="review() 参数", prechecks=prechecks)
    return filename, code_content, skill_name, skill_desc, module_type
@dataclass
class PreCreationReviewReport:
    timestamp: str = ""
    skill_dir: str = ""
    mode: str = ""
    prechecks: list[dict] = field(default_factory=list)
    blocking_count: int = 0
    warning_count: int = 0
    info_count: int = 0
    architecture_suggestions: list[dict] = field(default_factory=list)
    injected_lessons: list[dict] = field(default_factory=list)
    summary: str = ""
    can_proceed: bool = True
    def to_dict(self) -> dict:
        return asdict(self)
class PreCreationReviewer:
    def __init__(self, skill_dir: str | os.PathLike):
        raw_skill_dir = skill_dir
        skill_dir, dir_error = normalize_text_param(
            skill_dir, "skill_dir 期望 str",
            suggestion="传入 str 路径后再继续",
            applicable_to="PreCreationReviewer(skill_dir)",
            allow_pathlike=True)
        if dir_error is not None:
            logger.warning(
                "[PreCreationReview] skill_dir 类型非法 %r，已归一空串",
                raw_skill_dir)
        self.skill_dir = skill_dir
        self._input_prechecks = [] if dir_error is None else [dir_error]
        collaborators = _resolve_review_collaborators()
        self.code_checker = collaborators["precreation_code_precheck"](
            collaborators["precreation_review_gate"]())
        self.doc_checker = collaborators["precreation_doc_precheck"]()
        self.arch_advisor = collaborators["precreation_arch_advisor"]()
        self.lessons_injector = collaborators["precreation_history_lessons"](skill_dir)
        self._api_prechecks = collaborators["precreation_api_prechecks"]
        self._constraint_lessons = collaborators["precreation_constraint_lessons"]
    def review(self,
               mode: str = _DEFAULT_REVIEW_MODE,
               code_content: str = "",
               filename: str = "",
               skill_name: str = "",
               skill_desc: str = "",
               module_type: str = "") -> PreCreationReviewReport:
        mode = self._normalize_mode(mode)
        report = PreCreationReviewReport(
            timestamp=time.strftime(FMT_DATETIME),
            skill_dir=self.skill_dir,
            mode=mode,
        )
        report.prechecks.extend(
            item.to_dict() for item in self._input_prechecks)
        filename, code_content, skill_name, skill_desc, module_type = (
            _normalize_review_params(
                filename, code_content, skill_name, skill_desc,
                module_type, report.prechecks))
        code_review_requested = mode in ("code_writing", "both")
        run_code_checks = code_review_requested and bool(code_content.strip())
        if code_review_requested and not run_code_checks:
            report.prechecks.append(PreCheckItem(
                category="input_contract",
                severity=SEVERITY_BLOCKING,
                description="代码审查已启用，但 code_content 为空",
                suggestion="传入待审查源码，或改用 skill_creation 模式",
                source="build_preintervention",
                applicable_to=filename or "code",
                evidence_type="input_contract",
            ).to_dict())
        self._run_code_prechecks(report, code_content, filename, run_code_checks)
        self._run_doc_prechecks(report, skill_name, skill_desc, mode)
        report.architecture_suggestions = self._collect_architecture_suggestions(
            module_type, filename, skill_name, code_content)
        self._inject_lessons(report)
        self._finalize_report(report, code_content, filename, run_code_checks)
        return report
    def _finalize_report(self, report: PreCreationReviewReport,
                         code_content: str, filename: str,
                         run_code_checks: bool) -> None:
        if run_code_checks:
            report.prechecks.extend(
                item.to_dict()
                for item in self._api_prechecks(code_content, filename))
        report.injected_lessons.extend(self._constraint_lessons())
        self._count_severities(report)
        report.can_proceed = report.blocking_count == 0
        report.summary = self._compose_summary(report)
        logger.info("[PreCreationReview] 预检完成: blocking=%d, warning=%d, "
                     "info=%d, lessons=%d, can_proceed=%s",
                     report.blocking_count, report.warning_count,
                     report.info_count, len(report.injected_lessons),
                     report.can_proceed)
    @staticmethod
    def _normalize_mode(mode: object) -> str:
        if mode in _VALID_REVIEW_MODES:
            return mode
        logger.warning(
            "[PreCreationReview] 无效 mode=%r（合法值 %s），"
            "已归一为 %s 执行全量预检",
            mode, "/".join(_VALID_REVIEW_MODES), _DEFAULT_REVIEW_MODE)
        return _DEFAULT_REVIEW_MODE
    def _run_code_prechecks(self, report: PreCreationReviewReport,
                            code_content: str, filename: str,
                            enabled: bool) -> None:
        if not enabled:
            return
        code_items = self.code_checker.check(code_content, filename)
        report.prechecks.extend(i.to_dict() for i in code_items)
    def _run_doc_prechecks(self, report: PreCreationReviewReport,
                           skill_name: str, skill_desc: str, mode: str) -> None:
        if mode not in ("skill_creation", "both"):
            return
        doc_items = self.doc_checker.check(
            skill_name, skill_desc, self._read_skill_md())
        report.prechecks.extend(i.to_dict() for i in doc_items)
    def _collect_architecture_suggestions(self, module_type: str,
                                          filename: str, skill_name: str,
                                          code_content: str) -> list[dict]:
        suggestions = self.arch_advisor.advise(
            module_type, filename or skill_name, code_content)
        return [s.to_dict() for s in suggestions]
    def _inject_lessons(self, report: PreCreationReviewReport) -> None:
        lessons = self.lessons_injector.inject()
        report.injected_lessons = list(lessons)
        self._inject_lesson_prechecks(report, lessons)
    def _read_skill_md(self) -> str:
        if not self.skill_dir:
            return ""
        md_path = os.path.join(self.skill_dir, "SKILL.md")
        if not os.path.isfile(md_path):
            return ""
        try:
            with open(md_path, encoding="utf-8", errors="replace") as f:
                return f.read()
        except OSError as e:
            logger.warning("[PreCreationReview] 读取 SKILL.md 失败: %s", e)
            return ""
    def _inject_lesson_prechecks(self, report: PreCreationReviewReport,
                                 lessons: list) -> None:
        for lesson in lessons:
            if not isinstance(lesson, dict):
                continue
            lesson_severity = (
                SEVERITY_WARNING
                if lesson.get("inject_as") == "avoidance_pattern"
                else SEVERITY_INFO)
            lesson_confidence = safe_confidence(
                lesson.get("confidence", 0.0), 0.0)
            report.prechecks.append(PreCheckItem(
                category="lesson",
                severity=lesson_severity,
                description=f"[历史经验] {lesson.get('description', '')}",
                suggestion=lesson.get(FIELD_SUGGESTED_VALUE, ""),
                source=lesson.get("source", "historical"),
                applicable_to=lesson.get("target", ""),
                confidence=lesson_confidence,
                evidence_type="historical",
            ).to_dict())
    def _count_severities(self, report: PreCreationReviewReport) -> None:
        unknown = 0
        for item in report.prechecks:
            sev = item.get("severity", "")
            if sev == SEVERITY_BLOCKING:
                report.blocking_count += 1
            elif sev == SEVERITY_WARNING:
                report.warning_count += 1
            elif sev == SEVERITY_INFO:
                report.info_count += 1
            else:
                unknown += 1
                report.blocking_count += 1
        if unknown:
            logger.warning(
                "[PreCreationReview] %d 条预检项 severity 非法，已按 blocking 计入",
                unknown)
    def _compose_summary(self, report: PreCreationReviewReport) -> str:
        lines = []
        lines.append("## 预创建审查总结")
        lines.append("")
        if report.can_proceed:
            lines.append("**可以继续创建** (无阻断项)")
        else:
            lines.append(f"**存在 {report.blocking_count} 项阻断问题，必须先解决**")
        lines.append(f"- 阻断: {report.blocking_count}, 警告: {report.warning_count}, 提示: {report.info_count}")
        lines.append(f"- 注入经验/约束: {len(report.injected_lessons)} 条")
        lines.append(f"- 架构建议: {len(report.architecture_suggestions)} 条")
        if report.prechecks:
            lines.append("")
            lines.append("### 关键检查项")
            for item in report.prechecks:
                if item.get("severity") in KEY_SEVERITIES:
                    lines.append(f"- [{item.get('severity', '')}] "
                                 f"{item.get('description', '')}")
        return "\n".join(lines)
def run_pre_creation_review(
    skill_dir: str | os.PathLike,
    mode: str = _DEFAULT_REVIEW_MODE,
    code_content: str = "",
    filename: str = "",
    skill_name: str = "",
    skill_desc: str = "",
    module_type: str = "",
) -> PreCreationReviewReport:
    reviewer = PreCreationReviewer(skill_dir)
    return reviewer.review(
        mode=mode,
        code_content=code_content,
        filename=filename,
        skill_name=skill_name,
        skill_desc=skill_desc,
        module_type=module_type,
    )
def _normalize_crosscheck(crosscheck) -> dict | None:
    if crosscheck is None:
        return None
    if hasattr(crosscheck, "to_dict"):
        return crosscheck.to_dict()
    if isinstance(crosscheck, dict):
        return crosscheck
    return {"status": "completed", "raw": str(crosscheck)}
def _enhancement(name: str):
    provider = registered_review_providers().get(name)
    if provider is None:
        raise RuntimeError(f"预介入增强融合点未装配（领域未导入）: {name}")
    return provider
def _inject_history_lessons(skill_dir: str) -> list:
    try:
        injector = _enhancement("precreation_history_lessons")(skill_dir)
        lessons = injector.inject()
        logger.info("[preintervention] 注入 %d 条历史经验", len(lessons))
        return lessons
    except Exception as e:  
        logger.warning("[preintervention] 经验注入失败: %s", e)
        return []
def _run_precreation_crosscheck(skill_dir: str, content: str, filename: str,
                                skill_name: str,
                                description: str) -> dict | None:
    try:
        crosscheck = run_pre_creation_review(
            skill_dir=skill_dir,
            code_content=content,
            filename=filename,
            skill_name=skill_name,
            skill_desc=description,
        )
        return _normalize_crosscheck(crosscheck)
    except Exception as e:
        logger.warning("[preintervention] 交叉验证失败: %s", e, exc_info=True)
        return None
def _apply_memory_enhancement(report: PreinterventionReport, description: str,
                              content: str, memory_context: Any) -> None:
    try:
        mem_result = _enhancement("precreation_memory_enhance")(
            description, content, memory_context)
        warnings = mem_result.get("warnings", [])
        report._memory_warnings = warnings
        report._memory_suggestions = mem_result.get("suggestions", [])
        report._memory_known_patterns = mem_result.get("known_patterns", {})
        if warnings:
            logger.info("[preintervention] 记忆增强: %d条警告, %d条建议",
                        len(warnings), len(mem_result.get("suggestions", [])))
    except Exception as mem_err:  
        logger.warning("[preintervention] 记忆增强跳过: %s", mem_err)
def run_preintervention_with_lessons(
    skill_dir: str | os.PathLike,
    skill_name: str = "",
    description: str = "",
    content: str = "",
    enable_lessons: bool = _DEFAULT_ENABLE_LESSONS,
    filename: str = "",
    enable_pre_creation_crosscheck: bool = _DEFAULT_ENABLE_CROSSCHECK,
    memory_context: Any | None = None,
) -> PreinterventionReport:
    return _execute_and_emit(
        (skill_name, description, skill_dir, content, filename),
        _EntryEnhancement(
            enable_lessons=enable_lessons,
            enable_crosscheck=enable_pre_creation_crosscheck,
            memory_context=memory_context,
        ),
    )

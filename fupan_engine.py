from __future__ import annotations

import ast
import json
import logging
import math
import os
import re
import symtable
import time
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, NamedTuple

from jwsgj.diag_testing_import_audit import (
    _binding_event_position,
    _call_in_bound_scope,
    _collect_scope_binding_ranges,
)
from jwsgj.diag_testing_source import (
    collect_scope_binding_names,
)
from jwsgj.diag_types_normalize import (
    as_declared,
    coerce_text_list,
    count_tasks,
    dict_items,
    dict_or_empty,
    grade_from_score,
    len_safe,
    safe_float,
    safe_str,
    str_or,
    text_or_empty,
    timestamp_human,
    timestamp_ms,
)
from jwsgj.diag_types_vocab import (
    CAT_MAINTAINABILITY,
    FIELD_METHODS_EXECUTED,
    MEMORY_WRITE_ACTIONS,
    TX_FAILED_STATUSES,
)
from jwsgj.diag_zero_backlog_ledger import (
    load_ai_review_summary,
)
from jwsgj.fupan_analyzer import (
    analyze_session,
    as_bool,
    as_float,
    as_int,
    build_trigger_signals,
    collect_tools_used,
    ensure_list,
    ensure_str_list,
    normalize_scalar,
    to_fupan_params,
)
from jwsgj.html_render_pipeline import emit_fupan_report_html
from jwsgj.log_analysis import load_detector_liveness_events
from jwsgj.log_config import log_swallowed
from jwsgj.log_driven_evolution import (
    load_audit_summary,
    load_bug_intercept_summary,
    load_growth_summary,
    load_log_quality_summary,
    load_perf_summary,
    load_swallowed_summary,
    register_rule_candidates,
    run_log_driven_evolution,
)
from jwsgj.memory_bridge import (
    DiagnosticMemoryContext as _FupanMemCtx,
)
from jwsgj.memory_bridge import (
    compute_information_density,
    evaluate_memory_density,
    fix_succeeded,
    is_valid_memory_score,
    materialize_existing_memories,
    treatment_counts,
)
from jwsgj.memory_bridge_ops import (
    apply_fupan_memory_bridge,
    apply_fupan_memory_enhancement,
    build_memory_operations,
    frontmatter_bounds,
    generate_memory_candidates,
    memory_operation_issue,
    normalize_candidates,
    quality_gate,
    run_fupan_pdca,
    validated_memory_operations,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.retrospective_evolution import (
    collect_stage6a_improvements,
)
from jwsgj.retrospective_evolution import (
    summarize_defense_feedback as _summarize_defense_feedback,
)
from jwsgj.runtime_paths import (
    read_evolution_section,
)
from jwsgj.testsuite_eval import attach_test_health_metrics

__all__ = [
    "DimensionScore",
    "QualityDimension",
    "QualityReport",
    "build_stage5_fupan_context",
    "build_stage6a_fupan_inputs",
    "detect_risks",
    "fp_consume_event_risks",
    "fp_consume_log_growth",
    "inject_log_findings_into_review",
    "project_stage6a_fupan_report",
    "quick_analyze",
    "run_fupan",
    "run_stage6a_fupan",
    "score_dimensions",
    "score_log_quality",
    "verify_consumption_chain",
    "verify_fupan_writes",
]
_log = logging.getLogger(__name__)
class QualityDimension(Enum):
    COMPLETENESS = "completeness"
    ACCURACY = "accuracy"
    SECURITY = "security"
    EFFICIENCY = "efficiency"
    MAINTAINABILITY = CAT_MAINTAINABILITY
    INNOVATION = "innovation"
    CONSISTENCY = "consistency"
    USER_SATISFACTION = "user_satisfaction"
    LOG_QUALITY = "log_quality"
@dataclass
class DimensionScore:
    dimension: QualityDimension
    score: float = 0.0
    weight: float = 1.0
    evidence: list[str] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
@dataclass
class QualityReport:
    dimensions: list[DimensionScore] = field(default_factory=list)
    overall_score: float = 0.0
    grade: str = "F"
    strengths: list[str] = field(default_factory=list)
    weaknesses: list[str] = field(default_factory=list)
    risk_level: str = "low"
RISK_PATTERNS: list[dict[str, Any]] = [
    {"id": "R01", "category": "数据安全",
     "pattern": ["密码", "token", "api_key", "secret", "密钥", "凭证", "私钥"],
     "severity": "critical",
     "suggestion": "检测到敏感信息泄露风险,请确保凭证类数据未被记录或硬编码"},
    {"id": "R02", "category": "文件操作",
     "pattern": ["删除", "rm ", "unlink", "覆盖", "overwrite", "清空"],
     "severity": "high",
     "suggestion": "检测到不可逆文件操作,请确认已备份或用户已授权"},
    {"id": "R03", "category": "依赖缺失",
     "pattern": ["ModuleNotFoundError", "ImportError", "No module named", "找不到模块"],
     "severity": "high",
     "suggestion": "检测到模块导入失败,请检查依赖是否完整安装"},
    {"id": "R04", "category": "循环依赖",
     "pattern": ["circular import", "循环导入", "cannot import name"],
     "severity": "high",
     "suggestion": "检测到循环依赖风险,建议提取公共模块或使用延迟导入"},
    {"id": "R05", "category": "性能退化",
     "pattern": ["timeout", "超时", "slow", "慢", "耗时", "卡顿"],
     "severity": "medium",
     "suggestion": "检测到性能问题,建议优化算法或增加缓存"},
    {"id": "R06", "category": "状态不一致",
     "pattern": ["不一致", "inconsistent", "冲突", "conflict", "版本不匹配"],
     "severity": "medium",
     "suggestion": "检测到状态不一致风险,建议检查同步机制"},
    {"id": "R07", "category": "硬编码配置",
     "pattern": ["hardcode", "硬编码", "写死", "magic number"],
     "severity": "low",
     "suggestion": "检测到硬编码配置,建议提取为配置文件或环境变量"},
    {"id": "R08", "category": "异常处理缺失",
     "pattern": ["未处理异常", "unhandled exception", "裸 except", "bare except"],
     "severity": "medium",
     "suggestion": "检测到异常处理缺失,建议添加 try/except 并记录日志"},
    {"id": "R09", "category": "资源泄漏",
     "pattern": ["未关闭", "not closed", "leak", "泄漏", "未释放"],
     "severity": "medium",
     "suggestion": "检测到资源泄漏风险,建议使用 with 语句或确保资源释放"},
    {"id": "R10", "category": "代码重复",
     "pattern": ["重复代码", "duplicate", "copy-paste", "复制粘贴"],
     "severity": "low",
     "suggestion": "检测到代码重复,建议提取公共函数或模块"},
    {"id": "R11", "category": "测试缺失",
     "pattern": ["无测试", "no test", "未测试", "untested"],
     "severity": "low",
     "suggestion": "检测到测试覆盖不足,建议补充单元测试"},
    {"id": "R12", "category": "文档缺失",
     "pattern": ["无文档", "no doc", "未注释", "undocumented"],
     "severity": "low",
     "suggestion": "检测到文档覆盖不足,建议补充 docstring 和 README"},
    {"id": "R13", "category": "动态导入",
     "pattern": ["__import__", "importlib.import_module"],
     "severity": "high",
     "suggestion": "检测到运行时动态导入,建议使用静态 import 并添加可用性检查"},
    {"id": "R14", "category": "代码注入",
     "pattern": ["eval(", "exec(", "compile("],
     "severity": "critical",
     "suggestion": "检测到代码注入风险,建议使用 ast.literal_eval 或沙箱隔离"},
]
_KW_RE_CACHE: dict[str, re.Pattern[str]] = {
    kw: re.compile(re.escape(kw), re.IGNORECASE)
    for _pattern_def in RISK_PATTERNS
    for kw in _pattern_def["pattern"]
}
def _lex_consume_short_string(text: str, i: int, quote: str,
                              pos: int) -> tuple[bool, int]:
    content_start = i + 1
    while True:
        line_end = text.find("\n", content_start)
        scan_stop = pos if line_end == -1 else min(line_end, pos)
        j = _short_string_end(text, content_start, quote, scan_stop)
        if j < scan_stop:
            return False, j + 1
        if scan_stop == pos:
            return True, i
        if not _short_string_line_is_escaped(text, content_start, line_end):
            return False, line_end + 1
        content_start = line_end + 1
def _short_string_line_is_escaped(text: str, start: int, line_end: int) -> bool:
    cursor = line_end - 1
    if cursor >= start and text[cursor] == "\r":
        cursor -= 1
    backslashes = 0
    while cursor >= start and text[cursor] == "\\":
        backslashes += 1
        cursor -= 1
    return backslashes % 2 == 1
def _lex_construct_at(text: str, pos: int) -> str:
    active = ""
    i = 0
    pos = min(pos, len(text))
    while i < pos:
        if active:
            active, i = _consume_active_triple(text, i, active)
            continue
        ch = text[i]
        if ch == "#":
            nl_next = _comment_next_line(text, i, pos)
            if nl_next < 0:
                return "comment"
            i = nl_next
            continue
        if ch in ("'", '"'):
            if text.startswith(ch * 3, i):
                active = ch * 3
                i += 3
                continue
            in_short, i = _lex_consume_short_string(text, i, ch, pos)
            if in_short:
                return "short"
            continue
        i += 1
    return "triple" if active else ""
def _consume_active_triple(text: str, i: int, active: str) -> tuple[str, int]:
    if text[i] == "\\":
        return active, i + 2
    if text.startswith(active, i):
        return "", i + 3
    return active, i + 1
def _comment_next_line(text: str, i: int, pos: int) -> int:
    nl = text.find("\n", i)
    if nl == -1 or nl >= pos:
        return -1
    return nl + 1
def _short_string_end(text: str, content_start: int, ch: str,
                      scan_stop: int) -> int:
    j = content_start
    while j < scan_stop:
        if text[j] == "\\":
            j = min(j + 2, scan_stop)
            continue
        if text[j] == ch:
            break
        j += 1
    return j
def _classify_keyword_context(text: str, pos: int) -> str:
    construct = _lex_construct_at(text, pos)
    if construct in ("triple", "short"):
        return "string"
    if construct == "comment":
        return "comment"
    return "code"
_SEVERITY_ORDER: dict[str, int] = {"critical": 0, "high": 1, "medium": 2, "low": 3}
def _normalize_risk_severity(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    return value.strip().lower()
def _severity_rank(risk: dict[str, Any]) -> int:
    return _SEVERITY_ORDER.get(_normalize_risk_severity(risk.get("severity")), 99)
_MAX_KW_HITS = 5
_IMPORT_STMT_HEAD_RE = re.compile(
    r"\A(?:import[ \t]+[\w.]+|from[ \t]+[\w.]+[ \t]+import\b)")
def _is_ascii_word_char(ch: str) -> bool:
    return ch.isascii() and (ch.isalnum() or ch == "_")
def _kw_edge_is_ascii_letter(kw_lower: str, *, head: bool) -> bool:
    ch = kw_lower[:1] if head else kw_lower[-1:]
    return ch.isascii() and ch.isalpha()
def _is_word_interior_hit(text: str, idx: int, kw_lower: str) -> bool:
    if (idx > 0 and _kw_edge_is_ascii_letter(kw_lower, head=True)
            and _is_ascii_word_char(text[idx - 1])):
        return True
    end = idx + len(kw_lower)
    return (end < len(text)
            and _kw_edge_is_ascii_letter(kw_lower, head=False)
            and _is_ascii_word_char(text[end]))
def _is_attr_call_hit(text: str, idx: int, kw_lower: str) -> bool:
    if not kw_lower.endswith("(") or idx == 0 or text[idx - 1] != ".":
        return False
    for module_name in _BUILTIN_MODULE_NAMES:
        prefix = f"{module_name}."
        start = idx - len(prefix)
        if start < 0 or not text[:idx].endswith(prefix):
            continue
        if (start == 0 or (not _is_ascii_word_char(text[start - 1])
                           and text[start - 1] != ".")):
            return False
    return True
_CONTEXT_CONFIDENCE: dict[str, float] = {
    "code": 0.9, "string": 0.6, "comment": 0.3}
_TEXT_HIT_CONFIDENCE = 0.7
def _kw_hit_evidence(text: str, pos: int,
                     is_code: bool) -> tuple[str, float]:
    if not is_code:
        return "text", _TEXT_HIT_CONFIDENCE
    context = _classify_keyword_context(text, pos)
    return context, _CONTEXT_CONFIDENCE.get(context, _TEXT_HIT_CONFIDENCE)
_CODE_TEXT_MARKERS = ("\ndef ", "\nclass ", "\nimport ", "\nfrom ", "\n    ")
def _is_code_text(text: str) -> bool:
    lines = text.splitlines()
    comment_only = bool(lines) and all(
        not line.strip() or line.lstrip().startswith("#") for line in lines)
    return bool(
        comment_only
        or any(marker in text for marker in _CODE_TEXT_MARKERS)
        or text.startswith(("def ", "class "))
        or _IMPORT_STMT_HEAD_RE.match(text) is not None
    )
def _scan_keyword_hits(text: str, pattern_def: dict[str, Any], kw: str,
                       is_code: bool, detected: list[dict[str, Any]]) -> None:
    kw_re = _KW_RE_CACHE[kw]
    kw_lower = kw.lower()
    hits = 0
    for m in kw_re.finditer(text):
        if hits >= _MAX_KW_HITS:
            break
        idx = m.start()
        if _is_word_interior_hit(text, idx, kw_lower):
            continue
        if _is_attr_call_hit(text, idx, kw_lower):
            continue
        context, confidence = _kw_hit_evidence(text, idx, is_code)
        detected.append({
            "risk_id": pattern_def["id"],
            "category": pattern_def["category"],
            "severity": pattern_def["severity"],
            "matched_keyword": kw,
            "suggestion": pattern_def["suggestion"],
            "method": "keyword",
            "confidence": confidence,
            "context": context,
            "lineno": text.count("\n", 0, idx) + 1,
            "col_offset": idx - text.rfind("\n", 0, idx) - 1,
        })
        hits += 1
def _detect_risks(text: str) -> list[dict[str, Any]]:
    detected = []
    is_code = _is_code_text(text)
    for pattern_def in RISK_PATTERNS:
        for kw in pattern_def["pattern"]:
            _scan_keyword_hits(text, pattern_def, kw, is_code, detected)
    detected.sort(key=_severity_rank)
    return detected
class _AstCallSpec(NamedTuple):
    risk_id: str
    category: str
    severity: str
    matched_keyword: str
    suggestion: str
_RISK_DEFS_BY_ID: dict[str, dict[str, Any]] = {d["id"]: d for d in RISK_PATTERNS}
def _ast_spec(risk_id: str, matched_keyword: str,
              suggestion: str | None = None) -> _AstCallSpec:
    definition = _RISK_DEFS_BY_ID[risk_id]
    return _AstCallSpec(definition["id"], definition["category"],
                        definition["severity"], matched_keyword,
                        suggestion or definition["suggestion"])
_BARE_EXCEPT_SPEC = _ast_spec(
    "R08", "except:", "检测到裸 except,建议捕获具体异常类型并记录日志")
_BUILTIN_MODULE_NAMES = frozenset({"builtins", "__builtins__"})
_AST_CALL_RISK_TABLE: dict[str, _AstCallSpec] = {
    "__import__": _ast_spec("R13", "__import__"),
    "eval": _ast_spec("R14", "eval()"),
    "exec": _ast_spec("R14", "exec()"),
    "compile": _ast_spec("R14", "compile()"),
}
def _ast_risk_record(
    spec: _AstCallSpec, lineno: int, col_offset: int,
) -> dict[str, Any]:
    return {
        "risk_id": spec.risk_id,
        "category": spec.category,
        "severity": spec.severity,
        "matched_keyword": spec.matched_keyword,
        "suggestion": spec.suggestion,
        "method": "ast",
        "confidence": 0.95,
        "context": "code",
        "lineno": lineno,
        "col_offset": col_offset,
    }
def _builtin_call_name(
    func: ast.AST,
    shadowed_names: frozenset[str],
    builtin_aliases: dict[str, str],
) -> str | None:
    if isinstance(func, ast.Name):
        if func.id in shadowed_names:
            return None
        return builtin_aliases.get(func.id, func.id)
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        module_name = builtin_aliases.get(func.value.id)
        if module_name is None:
            if (func.value.id != "__builtins__"
                    or func.value.id in shadowed_names):
                return None
            module_name = func.value.id
        if (module_name in _BUILTIN_MODULE_NAMES
                and func.value.id not in shadowed_names):
            return func.attr
    return None
def _iter_unconditional_statements(
    body: list[ast.stmt],
) -> list[ast.stmt]:
    statements: list[ast.stmt] = []
    for stmt in body:
        if isinstance(stmt, ast.If) and isinstance(stmt.test, ast.Constant):
            selected = stmt.body if bool(stmt.test.value) else stmt.orelse
            statements.extend(_iter_unconditional_statements(selected))
        else:
            statements.append(stmt)
    return statements
def _canonical_builtin_imports(body: list[ast.stmt]) -> dict[str, str]:
    names: dict[str, str] = {}
    for stmt in _iter_unconditional_statements(body):
        if isinstance(stmt, ast.Import):
            for alias in stmt.names:
                bound = alias.asname or alias.name.split(".")[0]
                names[bound] = (
                    alias.name if alias.name in _BUILTIN_MODULE_NAMES else "")
        elif isinstance(stmt, ast.ImportFrom):
            for alias in stmt.names:
                bound = alias.asname or alias.name
                canonical = (stmt.level == 0 and stmt.module == "builtins"
                             and alias.name in _AST_CALL_RISK_TABLE)
                names[bound] = alias.name if canonical else ""
    return {name: target for name, target in names.items() if target}
def _collect_complex_scope_bindings(
    stmt: ast.stmt, bound_names: set[str], declared_outer: set[str],
    possible_builtin_names: set[str] | None = None,
) -> None:
    def _visit(node: ast.AST) -> None:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            bound_names.add(node.name)
            signature = [*node.decorator_list]
            if isinstance(node, ast.ClassDef):
                signature.extend([*node.bases, *[kw.value for kw in node.keywords]])
            else:
                signature.append(node.args)
                if node.returns is not None:
                    signature.append(node.returns)
            signature.extend(getattr(node, "type_params", ()))
            for part in signature:
                _visit(part)
            return
        if isinstance(node, ast.Lambda):
            _visit(node.args)
            return
        if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp,
                             ast.GeneratorExp)):
            for generator in node.generators:
                _visit(generator.iter)
                for condition in generator.ifs:
                    _visit(condition)
            if isinstance(node, ast.DictComp):
                _visit(node.key)
                _visit(node.value)
            else:
                _visit(node.elt)
            return
        if isinstance(node, ast.Import):
            bound_names.update(
                alias.asname or alias.name.split(".")[0] for alias in node.names)
            if possible_builtin_names is not None:
                possible_builtin_names.update(_canonical_builtin_imports([node]))
            return
        if isinstance(node, ast.ImportFrom):
            bound_names.update(
                alias.asname or alias.name for alias in node.names
                if alias.name != "*")
            if possible_builtin_names is not None:
                possible_builtin_names.update(_canonical_builtin_imports([node]))
            return
        if isinstance(node, ast.Delete):
            bound_names.update(
                target.id for item in node.targets for target in walk_nodes(item)
                if isinstance(target, ast.Name) and isinstance(target.ctx, ast.Del))
        collect_scope_binding_names(node, bound_names, declared_outer)
        for child in ast.iter_child_nodes(node):
            _visit(child)
    _visit(stmt)
def _symbol_is_local(table: symtable.SymbolTable, name: str) -> bool:
    for symbol in table.get_symbols():
        if symbol.get_name() != name:
            continue
        return (symbol.is_assigned() or symbol.is_parameter()
                or symbol.is_imported() or symbol.is_namespace())
    return False
def _annotation_only_unbound_names(body: list[ast.stmt]) -> set[str]:
    annotated: set[str] = set()
    bound: set[str] = set()
    def _visit(node: ast.AST) -> None:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            bound.add(node.name)
            for part in [*node.decorator_list, node.args,
                         *getattr(node, "type_params", ())]:
                _visit(part)
            if node.returns is not None:
                _visit(node.returns)
            return
        if isinstance(node, ast.ClassDef):
            bound.add(node.name)
            for part in [*node.decorator_list, *node.bases,
                         *[kw.value for kw in node.keywords],
                         *getattr(node, "type_params", ())]:
                _visit(part)
            return
        if isinstance(node, ast.Lambda):
            _visit(node.args)
            return
        if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp,
                             ast.GeneratorExp)):
            for generator in node.generators:
                _visit(generator.iter)
                for condition in generator.ifs:
                    _visit(condition)
            if isinstance(node, ast.DictComp):
                _visit(node.key)
                _visit(node.value)
            else:
                _visit(node.elt)
            return
        if isinstance(node, ast.AnnAssign) and node.value is None:
            if isinstance(node.target, ast.Name):
                annotated.add(node.target.id)
            _visit(node.annotation)
            return
        if isinstance(node, ast.Name) and isinstance(
                node.ctx, (ast.Store, ast.Del)):
            bound.add(node.id)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                bound.add(alias.asname or alias.name.split(".")[0])
        elif (isinstance(node, (ast.ExceptHandler, ast.MatchAs, ast.MatchStar))
              and node.name):
            bound.add(node.name)
        elif isinstance(node, ast.MatchMapping) and node.rest:
            bound.add(node.rest)
        for child in ast.iter_child_nodes(node):
            _visit(child)
    for stmt in body:
        _visit(stmt)
    return annotated - bound
class _ScopeNames(NamedTuple):
    shadowed: frozenset[str]
    builtin_aliases: dict[str, str]
    declared_outer_aliases: dict[str, str]
    inline_shadowed: frozenset[str] = frozenset()
def _scope_names(
    table: symtable.SymbolTable,
    body: list[ast.stmt],
    inherited: _ScopeNames,
    global_scope: _ScopeNames | None,
) -> _ScopeNames:
    symbols = list(table.get_symbols())
    local = {
        symbol.get_name() for symbol in symbols
        if (symbol.is_assigned() or symbol.is_parameter()
            or symbol.is_imported() or symbol.is_namespace())
    }
    if table.get_type() in {"module", "class"}:
        local.difference_update(_annotation_only_unbound_names(body))
    pure_imports = {
        symbol.get_name() for symbol in symbols
        if (symbol.is_imported() and not symbol.is_assigned()
            and not symbol.is_parameter() and not symbol.is_namespace())
    }
    canonical = _canonical_builtin_imports(body)
    active_aliases = {
        name: target for name, target in canonical.items() if name in pure_imports
    }
    global_only = {
        symbol.get_name() for symbol in symbols
        if (global_scope is not None and symbol.is_global()
            and symbol.get_name() not in local)
    }
    aliases = {
        name: target for name, target in inherited.builtin_aliases.items()
        if name not in local and name not in global_only
    }
    if global_scope is not None:
        aliases.update({
            name: target
            for name, target in global_scope.builtin_aliases.items()
            if name in global_only
        })
    aliases.update(active_aliases)
    shadowed_names = (
        (set(inherited.shadowed) | local)
        - set(active_aliases) - global_only)
    if global_scope is not None:
        shadowed_names.update(set(global_scope.shadowed) & global_only)
    declared_outer_aliases: dict[str, str] = {}
    for symbol in symbols:
        name = symbol.get_name()
        if name not in local:
            continue
        if symbol.is_nonlocal():
            outer = inherited
        elif global_scope is not None and symbol.is_global():
            outer = global_scope
        else:
            continue
        target = outer.builtin_aliases.get(name, "")
        if (not target and symbol.is_global()
                and name in _AST_CALL_RISK_TABLE
                and name not in outer.shadowed):
            target = name
        if target:
            declared_outer_aliases[name] = target
    return _ScopeNames(
        frozenset(shadowed_names), aliases, declared_outer_aliases)
_COMPREHENSION_SCOPE_NAMES = {
    ast.ListComp: "listcomp",
    ast.SetComp: "setcomp",
    ast.DictComp: "dictcomp",
    ast.GeneratorExp: "genexpr",
}
_TYPE_PARAMETER_SCOPE = "type parameter"
def _shadow_type_params(names: _ScopeNames,
                        type_params: frozenset[str]) -> _ScopeNames:
    """PEP 695 类型参数在函数体/类体（含方法体）内运行期可见并遮蔽同名内建。"""
    if not type_params:
        return names
    return names._replace(
        shadowed=names.shadowed | type_params,
        builtin_aliases={name: target for name, target
                         in names.builtin_aliases.items()
                         if name not in type_params},
        declared_outer_aliases={name: target for name, target
                                in names.declared_outer_aliases.items()
                                if name not in type_params},
    )
_SEQUENTIAL_SCOPE_TYPES = frozenset({"module", "class"})
_SEQUENTIAL_BINDING_NODES = (
    ast.Import, ast.ImportFrom, ast.Assign, ast.AnnAssign, ast.AugAssign,
    ast.Delete, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
)
class _AstRiskResults(list):
    def __init__(self, risks=(), shadowed_calls=frozenset()):
        super().__init__(risks)
        self.shadowed_calls = frozenset(shadowed_calls)
class _AstRiskScanner:
    def __init__(self, table: symtable.SymbolTable, source: str):
        self._root = table
        self._source_lines = source.splitlines()
        self._binding_ranges: dict[str, list] = {}
        self._children: dict[int, list[symtable.SymbolTable]] = {}
        self._table_parents: dict[int, symtable.SymbolTable] = {}
        self._type_params: dict[int, frozenset[str]] = {}
        self._scope_bodies: dict[int, list[ast.stmt]] = {}
        self._names_by_table: dict[int, _ScopeNames] = {}
        self._sequential_cache: dict[int, tuple[dict, frozenset]] = {}
        self._register(table)
        self.risks: list[dict[str, Any]] = []
        self.shadowed_calls: set[tuple[str, int, int]] = set()
    def _char_col(self, lineno: int, byte_col: int) -> int:
        line = self._source_lines[lineno - 1]
        return len(line.encode("utf-8")[:byte_col].decode("utf-8"))
    def _definition_name_col(
        self, node: ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef,
    ) -> int:
        char_col = self._char_col(node.lineno, node.col_offset)
        line = self._source_lines[node.lineno - 1]
        matched = re.match(
            r"(?:async\s+)?(?:def|class)\s+", line[char_col:])
        if matched:
            return char_col + matched.end()
        prefix_len = (10 if isinstance(node, ast.AsyncFunctionDef)
                      else 6 if isinstance(node, ast.ClassDef) else 4)
        return char_col + prefix_len
    def _raw_call_name_position(
        self, func: ast.Name | ast.Attribute,
    ) -> tuple[int, int]:
        if isinstance(func, ast.Attribute):
            return (func.end_lineno,
                    func.end_col_offset - len(func.attr.encode("utf-8")))
        return func.lineno, func.col_offset
    def _call_name_position(
        self, func: ast.Name | ast.Attribute,
    ) -> tuple[int, int]:
        lineno, byte_col = self._raw_call_name_position(func)
        return lineno, self._char_col(lineno, byte_col)
    def _suppress_annotation_calls(self, annotation: ast.AST) -> None:
        for node in walk_nodes(annotation):
            if not isinstance(node, ast.Call):
                continue
            func = node.func
            if isinstance(func, ast.Name):
                name = func.id
            elif isinstance(func, ast.Attribute):
                name = func.attr
            else:
                continue
            if name not in _AST_CALL_RISK_TABLE:
                continue
            lineno, col_offset = self._call_name_position(func)
            self.shadowed_calls.add((name, lineno, col_offset))
    def _sequential_bindings(
        self, table: symtable.SymbolTable,
    ) -> tuple[dict, frozenset, frozenset]:
        cached = self._sequential_cache.get(id(table))
        if cached is not None:
            return cached
        events: dict[str, list[tuple[tuple[int, int], str | None]]] = {}
        complex_names: set[str] = set()
        possible_builtin_names: set[str] = set()
        for stmt in _iter_unconditional_statements(
                self._scope_bodies.get(id(table), [])):
            if isinstance(stmt, (ast.Global, ast.Nonlocal)):
                continue
            bound_names: set[str] = set()
            declared_outer: set[str] = set()
            if not isinstance(stmt, _SEQUENTIAL_BINDING_NODES):
                _collect_complex_scope_bindings(
                    stmt, bound_names, declared_outer, possible_builtin_names)
                complex_names.update(bound_names | declared_outer)
                continue
            collect_scope_binding_names(stmt, bound_names, declared_outer)
            if isinstance(stmt, ast.Import):
                bound_names.update(
                    alias.asname or alias.name.split(".")[0]
                    for alias in stmt.names)
            elif isinstance(stmt, ast.ImportFrom):
                bound_names.update(
                    alias.asname or alias.name for alias in stmt.names
                    if alias.name != "*")
            elif isinstance(stmt, ast.Delete):
                bound_names.update(
                    node.id for target in stmt.targets
                    for node in walk_nodes(target)
                    if isinstance(node, ast.Name)
                    and isinstance(node.ctx, ast.Del))
            if isinstance(stmt, ast.AnnAssign) and stmt.value is None:
                continue
            named_exprs = [node for node in walk_nodes(stmt)
                           if isinstance(node, ast.NamedExpr)]
            bound_names.update(
                node.target.id for node in named_exprs
                if isinstance(node.target, ast.Name))
            simple = not named_exprs
            names = bound_names | declared_outer
            if not simple:
                complex_names.update(names)
                continue
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef)):
                position = (stmt.end_lineno, stmt.end_col_offset)
            else:
                position = _binding_event_position(stmt)
            canonical = (_canonical_builtin_imports([stmt])
                         if isinstance(stmt, (ast.Import, ast.ImportFrom)) else {})
            for name in names:
                target = (None if isinstance(stmt, ast.Delete)
                          else canonical.get(name, ""))
                events.setdefault(name, []).append((position, target))
        for name in complex_names:
            events.pop(name, None)
        result = (events, frozenset(complex_names),
                  frozenset(possible_builtin_names))
        self._sequential_cache[id(table)] = result
        return result
    def _sequential_alias(self, table: symtable.SymbolTable, name: str,
                          lineno: int, byte_col: int) -> tuple[bool, str]:
        if name in self._type_params.get(id(table), frozenset()):
            return True, ""
        sequential_scope = table.get_type() in _SEQUENTIAL_SCOPE_TYPES
        if not sequential_scope and not _symbol_is_local(table, name):
            return False, ""
        events, complex_names, _ = self._sequential_bindings(table)
        if name in complex_names:
            return False, ""
        position = (lineno, byte_col)
        visible = [event for event in events.get(name, ())
                   if event[0] <= position]
        if visible:
            target = visible[-1][1]
            if target is not None:
                return True, target
            is_global = any(
                symbol.get_name() == name and symbol.is_global()
                for symbol in table.get_symbols())
            prior_binding = (len(visible) > 1
                             and visible[-2][1] is not None)
            outer = self._global_names
            module_binding = (name in outer.shadowed
                              or name in outer.builtin_aliases)
            if is_global and (prior_binding or module_binding):
                # global 删除成功后移除模块绑定，内建同名对象重新可见；
                # nonlocal 删除只会让自由变量进入未绑定状态。
                return (True, name) if name in _AST_CALL_RISK_TABLE else (True, "")
        if not sequential_scope:
            return True, ""
        parent = self._table_parents.get(id(table))
        if parent is None:
            if name in _AST_CALL_RISK_TABLE or name == "__builtins__":
                return True, name
            if name in events:
                return True, ""
            return False, ""
        resolved, target = self._sequential_alias(
            parent, name, lineno, byte_col)
        if resolved:
            return True, target
        outer = self._names_by_table.get(id(parent))
        if outer is not None:
            if name in outer.shadowed:
                return True, ""
            if name in outer.builtin_aliases:
                return True, outer.builtin_aliases[name]
            if name in _AST_CALL_RISK_TABLE or name == "__builtins__":
                return True, name
        return False, ""
    def _uncertain_complex_binding(
        self, table: symtable.SymbolTable, current: _ScopeNames, name: str,
    ) -> bool:
        bindings = self._sequential_bindings(table)
        if name not in bindings[1]:
            return False
        return (table.get_type() in _SEQUENTIAL_SCOPE_TYPES
                or name in bindings[2]
                or bool(current.declared_outer_aliases.get(name)))
    def _resolve_call_name(self, func: ast.Name | ast.Attribute,
                           current: _ScopeNames,
                           table: symtable.SymbolTable) -> str | None:
        # _visit 对任意 ast.Call 都传入 node.func；当 func 是 Call/Lambda/
        # IfExp/Tuple 等表达式时没有可静态解析的根名称（如 f()()、
        # (lambda: ...)()），与 _suppress_annotation_calls 的 else 分支保持
        # 一致：不解析、不告警，而不是访问不存在的 .value 抛 AttributeError 穿透
        # 到 run_fupan 兜底导致整轮复盘 ok=False。
        if not isinstance(func, (ast.Name, ast.Attribute)):
            return None
        root = (func.id if isinstance(func, ast.Name)
                else func.value.id if isinstance(func.value, ast.Name) else "")
        if root in current.inline_shadowed:
            return None
        lineno, byte_col = self._raw_call_name_position(func)
        declared = current.declared_outer_aliases.get(root, "")
        if (declared and not _call_in_bound_scope(
                self._binding_ranges, root, lineno, byte_col)):
            if isinstance(func, ast.Name):
                return declared
            if declared in _BUILTIN_MODULE_NAMES:
                return func.attr
        if (root and _symbol_is_local(table, root)
                and root in self._sequential_bindings(table)[1]):
            return None
        if root:
            resolved, target = self._sequential_alias(
                table, root, lineno, byte_col)
            if resolved:
                if isinstance(func, ast.Name):
                    return target or None
                return func.attr if target in _BUILTIN_MODULE_NAMES else None
        return _builtin_call_name(
            func, current.shadowed, current.builtin_aliases)
    def _register(self, table: symtable.SymbolTable) -> None:
        children = list(table.get_children())
        self._children[id(table)] = children
        for child in children:
            self._table_parents[id(child)] = table
            self._register(child)
            if child.get_type() != _TYPE_PARAMETER_SCOPE:
                continue
            # PEP 695 泛型函数/类的真实作用域挂在同名同行的 ``type parameter``
            # 合成表之下。合成表对作用域链透明（真实作用域的父表直接挂到
            # 当前表），其类型参数名登记到真实作用域：运行期它们在函数体、
            # 类体与方法体内均可见并遮蔽同名内建。
            type_params = frozenset(
                symbol.get_name() for symbol in child.get_symbols()
                if symbol.is_assigned()
                and not symbol.get_name().startswith("."))
            for grandchild in self._children[id(child)]:
                self._table_parents[id(grandchild)] = table
                self._type_params[id(grandchild)] = type_params
    def _take_child(self, table: symtable.SymbolTable,
                    name: str, lineno: int) -> symtable.SymbolTable | None:
        child = self._pop_child(table, name, lineno)
        if (child is not None
                and child.get_type() == _TYPE_PARAMETER_SCOPE):
            # 不穿透合成表会把真实作用域顶替掉：嵌套作用域取不到子表而抛
            # ValueError，使整段文本的 AST 检测降级为空。
            child = self._pop_child(child, name, lineno)
        return child
    def _pop_child(self, table: symtable.SymbolTable,
                   name: str, lineno: int) -> symtable.SymbolTable | None:
        children = self._children[id(table)]
        index = next((i for i, child in enumerate(children)
                      if child.get_name() == name
                      and child.get_lineno() == lineno), None)
        if index is None:
            return None
        return children.pop(index)
    def scan(self, tree: ast.Module) -> list[dict[str, Any]]:
        self._postponed_annotations = any(
            isinstance(stmt, ast.ImportFrom) and stmt.level == 0
            and stmt.module == "__future__"
            and any(alias.name == "annotations" for alias in stmt.names)
            for stmt in tree.body)
        self._binding_ranges = _collect_scope_binding_ranges(tree)
        self._scope_bodies[id(self._root)] = tree.body
        names = _scope_names(
            self._root, tree.body, _ScopeNames(frozenset(), {}, {}), None)
        self._global_names = names
        self._visit_body(tree.body, self._root, names, names)
        self.risks.sort(key=_severity_rank)
        return self.risks
    def _visit_body(self, body: list[ast.stmt], table: symtable.SymbolTable,
                    current: _ScopeNames, closure: _ScopeNames) -> None:
        self._names_by_table[id(table)] = current
        for node in body:
            self._visit(node, table, current, closure)
    def _visit_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef,
                        table: symtable.SymbolTable,
                        current: _ScopeNames,
                        closure: _ScopeNames) -> None:
        if node.name in _AST_CALL_RISK_TABLE:
            self.shadowed_calls.add((
                node.name, node.lineno, self._definition_name_col(node)))
        signature = [*node.decorator_list]
        if self._postponed_annotations:
            signature.extend(node.args.defaults)
            signature.extend(default for default in node.args.kw_defaults
                             if default is not None)
            for arg in (*node.args.posonlyargs, *node.args.args,
                        *node.args.kwonlyargs, node.args.vararg,
                        node.args.kwarg):
                if arg is not None and arg.annotation is not None:
                    self._suppress_annotation_calls(arg.annotation)
        else:
            signature.append(node.args)
        signature.extend(getattr(node, "type_params", ()))
        if node.returns is not None:
            if self._postponed_annotations:
                self._suppress_annotation_calls(node.returns)
            else:
                signature.append(node.returns)
        for part in signature:
            self._visit(part, table, current, closure)
        child = self._take_child(table, node.name, node.lineno)
        if child is None:
            raise ValueError(f"AST/符号表函数作用域不一致: {node.name}")
        self._scope_bodies[id(child)] = node.body
        outer = _shadow_type_params(
            closure, self._type_params.get(id(child), frozenset()))
        local = _scope_names(
            child, node.body, outer, self._global_names)
        self._visit_body(node.body, child, local, local)
    def _visit_lambda(self, node: ast.Lambda, table: symtable.SymbolTable,
                      current: _ScopeNames, closure: _ScopeNames) -> None:
        self._visit(node.args, table, current, closure)
        child = self._take_child(table, "lambda", node.lineno)
        if child is None:
            raise ValueError("AST/符号表 lambda 作用域不一致")
        local = _scope_names(child, [], closure, self._global_names)
        self._visit(node.body, child, local, local)
    def _visit_class(self, node: ast.ClassDef, table: symtable.SymbolTable,
                     current: _ScopeNames, closure: _ScopeNames) -> None:
        if node.name in _AST_CALL_RISK_TABLE:
            self.shadowed_calls.add((
                node.name, node.lineno, self._definition_name_col(node)))
        for part in [*node.decorator_list, *node.bases,
                     *[kw.value for kw in node.keywords],
                     *getattr(node, "type_params", ())]:
            self._visit(part, table, current, closure)
        child = self._take_child(table, node.name, node.lineno)
        if child is None:
            raise ValueError(f"AST/符号表类作用域不一致: {node.name}")
        self._scope_bodies[id(child)] = node.body
        outer = _shadow_type_params(
            closure, self._type_params.get(id(child), frozenset()))
        local = _scope_names(
            child, node.body, outer, self._global_names)
        self._visit_body(node.body, child, local, outer)
    def _nearest_non_class_scope(
        self, table: symtable.SymbolTable,
    ) -> symtable.SymbolTable:
        while table.get_type() == "class":
            parent = self._table_parents.get(id(table))
            if parent is None:
                break
            table = parent
        return table
    def _visit_comprehension(self, node: ast.AST,
                             table: symtable.SymbolTable,
                             current: _ScopeNames,
                             closure: _ScopeNames) -> bool:
        scope_name = _COMPREHENSION_SCOPE_NAMES[type(node)]
        child = self._take_child(table, scope_name, node.lineno)
        generators = node.generators
        self._visit(generators[0].iter, table, current, closure)
        if child is not None:
            local = _scope_names(child, [], closure, self._global_names)
            scope_table = child
        else:
            inline_targets: set[str] = set()
            for generator in generators:
                collect_scope_binding_names(
                    generator, inline_targets, set())
            base = current
            scope_table = table
            if table.get_type() == "class":
                base = closure
                scope_table = self._nearest_non_class_scope(table)
            local = _ScopeNames(
                base.shadowed | frozenset(inline_targets),
                {name: target for name, target in base.builtin_aliases.items()
                 if name not in inline_targets},
                base.declared_outer_aliases,
                base.inline_shadowed | frozenset(inline_targets),
            )
        for index, generator in enumerate(generators):
            if index:
                self._visit(generator.iter, scope_table, local, local)
            self._visit(generator.target, scope_table, local, local)
            for condition in generator.ifs:
                self._visit(condition, scope_table, local, local)
        if isinstance(node, ast.DictComp):
            self._visit(node.key, scope_table, local, local)
            self._visit(node.value, scope_table, local, local)
        else:
            self._visit(node.elt, scope_table, local, local)
        return True
    def _visit(self, node: ast.AST, table: symtable.SymbolTable,
               current: _ScopeNames, closure: _ScopeNames) -> None:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            self._visit_function(node, table, current, closure)
            return
        if isinstance(node, ast.Lambda):
            self._visit_lambda(node, table, current, closure)
            return
        if isinstance(node, ast.ClassDef):
            self._visit_class(node, table, current, closure)
            return
        if (type(node) in _COMPREHENSION_SCOPE_NAMES
                and self._visit_comprehension(node, table, current, closure)):
            return
        if (isinstance(node, ast.AnnAssign)
                and (self._postponed_annotations
                     or table.get_type() == "function")):
            self._suppress_annotation_calls(node.annotation)
            self._visit(node.target, table, current, closure)
            if node.value is not None:
                self._visit(node.value, table, current, closure)
            return
        if isinstance(node, ast.ExceptHandler) and node.type is None:
            self.risks.append(_ast_risk_record(
                _BARE_EXCEPT_SPEC, node.lineno,
                self._char_col(node.lineno, node.col_offset)))
        elif isinstance(node, ast.Call):
            call_name = self._resolve_call_name(node.func, current, table)
            if call_name in _AST_CALL_RISK_TABLE:
                lineno, col_offset = self._call_name_position(node.func)
                self.risks.append(_ast_risk_record(
                    _AST_CALL_RISK_TABLE[call_name], lineno, col_offset))
            elif isinstance(node.func, ast.Name):
                name = node.func.id
                if name in _AST_CALL_RISK_TABLE:
                    local_binding = _symbol_is_local(table, name)
                    uncertain_sequential = self._uncertain_complex_binding(
                        table, current, name)
                    if ((name in current.shadowed or local_binding)
                            and not uncertain_sequential):
                        self.shadowed_calls.add((
                            name, node.func.lineno,
                            self._char_col(node.func.lineno, node.func.col_offset)))
            elif (isinstance(node.func, ast.Attribute)
                  and isinstance(node.func.value, ast.Name)
                  and node.func.attr in _AST_CALL_RISK_TABLE):
                root = node.func.value.id
                uncertain_sequential = self._uncertain_complex_binding(
                    table, current, root)
                unbound_builtins = (
                    root == "builtins"
                    and root not in current.builtin_aliases)
                if ((root in current.shadowed
                     or root in current.inline_shadowed
                     or _symbol_is_local(table, root)
                     or unbound_builtins)
                        and not uncertain_sequential):
                    lineno, col_offset = self._call_name_position(node.func)
                    self.shadowed_calls.add((
                        node.func.attr, lineno, col_offset))
        for child in ast.iter_child_nodes(node):
            self._visit(child, table, current, closure)
def _detect_risks_ast(code: str) -> list[dict[str, Any]]:
    if not code or not code.strip():
        return []
    try:
        tree = ast.parse(code)
        table = symtable.symtable(code, "<fupan_risks>", "exec")
        scanner = _AstRiskScanner(table, code)
        return _AstRiskResults(scanner.scan(tree), scanner.shadowed_calls)
    except SyntaxError as _e:
        # 降级为空结果必须留可感知痕迹，否则“无风险”与“解析失败”不可区分。
        log_swallowed(__name__, _e, context='_detect_risks_ast:SyntaxError')
        if _is_code_text(code):
            _log.warning(
                "detect_risks: 代码文本 AST 解析失败，风险检测降级为空结果: %s",
                _e)
        return []
    except (ValueError, RecursionError, MemoryError) as _e:
        log_swallowed(__name__, _e, context='_detect_risks_ast:ValueError')
        _log.warning("detect_risks: 复盘文本 AST 解析失败，风险检测降级为空结果: %s", _e)
        return []
def _is_shadowed_keyword_call(
    risk: dict[str, Any], shadowed_calls: frozenset[tuple[str, int, int]],
) -> bool:
    if risk.get("risk_id") not in {"R13", "R14"}:
        return False
    keyword = risk.get("matched_keyword", "")
    name = keyword.removesuffix("(")
    location = (name, risk.get("lineno"), risk.get("col_offset"))
    return location in shadowed_calls
def _risk_occurrence(
    risk: dict[str, Any],
) -> tuple[str | None, int | None, int | None]:
    return (risk.get("risk_id"), risk.get("lineno"),
            risk.get("col_offset"))
def detect_risks(text: str) -> list[dict[str, Any]]:
    if not isinstance(text, str):
        text = safe_str(text) if text else ""
    risks = _detect_risks(text)
    ast_risks = _detect_risks_ast(text)
    shadowed_calls = getattr(ast_risks, "shadowed_calls", frozenset())
    if shadowed_calls:
        risks = [r for r in risks
                 if not _is_shadowed_keyword_call(r, shadowed_calls)]
    if ast_risks:
        ast_occurrences = {_risk_occurrence(r) for r in ast_risks}
        risks = [r for r in risks
                 if _risk_occurrence(r) not in ast_occurrences] + ast_risks
        risks.sort(key=_severity_rank)
    return risks
def _sd_score_completeness(task_success: bool) -> DimensionScore:
    d = DimensionScore(dimension=QualityDimension.COMPLETENESS,
                       score=90.0 if task_success else 30.0)
    d.evidence.append("任务成功完成" if task_success else "任务未完全成功")
    if not task_success:
        d.suggestions.append("建议复盘失败原因并制定补救方案")
    return d
_PRECISION_SESSION_LIMIT = 5
_PRECISION_FP_RATE_FLOOR = 0.3
_NO_SAMPLE_ACCURACY_CEILING = 70.0
def _precision_rate(value: Any) -> float | None:
    """归一化误报率（兼容 0–1 小数与 0–100 百分比两种口径）。"""
    rate = as_float(value, None)
    if rate is None or not math.isfinite(rate):
        return None
    return min(1.0, max(0.0, rate if rate <= 1.0 else rate / 100.0))
def _feedback_fp_rate(value: Any) -> float | None:
    """feedback_history 的 fp_rate 恒为 0–100 百分比口径。

    唯一写入方 treatment_feedback._rate_pct 已乘 100：0.5 表示 0.5%，
    若交给 _precision_rate 做双口径猜测会被当成 50%。
    """
    rate = as_float(value, None)
    if rate is None or not math.isfinite(rate):
        return None
    return min(1.0, max(0.0, rate / 100.0))
def _load_precision_metrics(skill_dir: str | None) -> dict[str, float] | None:
    """从反馈历史与漏报探针汇总诊断精度指标。

    ACCURACY 维度原本只依据执行错误数，与“诊断准不准”完全脱钩，复盘质量分
    因此对误报治理零约束。这里同时接入两条正交轴：治疗阶段的 ``fp_rate``
    （误报）与探针的 ``fn_rate``（漏报）。任一轴可用即参与计分，两轴都无
    样本时才返回 None（调用方按未验证封顶，不再给满分）。
    """
    if not skill_dir:
        return None
    rates: list[float] = []
    try:
        history = read_evolution_section(skill_dir, "feedback_history")
    except (OSError, ValueError, TypeError):
        history = None
    sessions = history.get("sessions") if isinstance(history, dict) else None
    if isinstance(sessions, list):
        for session in sessions[-_PRECISION_SESSION_LIMIT:]:
            if not isinstance(session, dict):
                continue
            summary = session.get("outcome_summary")
            if not isinstance(summary, dict):
                continue
            if as_int(summary.get("total_attempted")) <= 0:
                continue
            rate = _feedback_fp_rate(summary.get("fp_rate"))
            if rate is not None:
                rates.append(rate)
    metrics: dict[str, float] = {}
    if rates:
        metrics["fp_rate"] = sum(rates) / len(rates)
    fn_rate = _load_fn_rate(skill_dir)
    if fn_rate is not None:
        metrics["fn_rate"] = fn_rate
    return metrics or None
def _load_fn_rate(skill_dir: str | None) -> float | None:
    """读取漏报探针最近一轮的漏报率。

    漏报与误报是诊断精度的两条正交轴：`fp_rate` 只覆盖“产出后被判错”，
    而漏报（真实缺陷根本没 finding）必须由注入探针独立度量。只接误报时，
    accuracy 维度对“什么都没检出”完全免疫——空跑也能拿 100 分。
    """
    if not skill_dir:
        return None
    try:
        history = read_evolution_section(skill_dir, "fn_probe_history")
    except (OSError, ValueError, TypeError):
        return None
    rounds = history.get("rounds") if isinstance(history, dict) else None
    if not isinstance(rounds, list) or not rounds:
        return None
    latest = rounds[-1] if isinstance(rounds[-1], dict) else None
    if latest is None:
        return None
    survived = latest.get("survived")
    if not isinstance(survived, (list, tuple)):
        return None
    evaluated = as_int(latest.get("killed")) + len(survived)
    if evaluated <= 0:
        return None
    return len(survived) / evaluated
def _sd_score_accuracy(error_count: int,
                       precision_metrics: dict | None = None,
                       ) -> DimensionScore:
    d = DimensionScore(dimension=QualityDimension.ACCURACY)
    fp_rate = _precision_rate((precision_metrics or {}).get("fp_rate"))
    fn_rate = _precision_rate((precision_metrics or {}).get("fn_rate"))
    if fp_rate is None and fn_rate is None:
        # 无精度样本时不得给满分：findings 为空时下游门禁全部“通过”，
        # 漏报因此最隐蔽。按未验证封顶，逼出“补样本”而不是“零样本放行”。
        d.score = min(_NO_SAMPLE_ACCURACY_CEILING,
                      100.0 - min(80.0, error_count * 15.0))
        d.evidence.append("无精度/漏报样本，accuracy 按未验证封顶计分")
        d.suggestions.append(
            "补充漏报探针基线与治疗阶段误报样本后重算 accuracy")
        if error_count > 0:
            d.evidence.append(f"发生 {error_count} 个错误")
            d.suggestions.append("建议分析错误根因并添加防护")
        return d
    worst_rate = max(
        rate for rate in (fp_rate, fn_rate) if rate is not None)
    d.score = max(10.0, 100.0 * (1.0 - worst_rate))
    if fp_rate is not None:
        d.evidence.append(
            f"诊断误报率 {fp_rate:.0%}（近{_PRECISION_SESSION_LIMIT}轮）")
    if fn_rate is not None:
        d.evidence.append(f"漏报探针漏报率 {fn_rate:.0%}")
    if worst_rate >= _PRECISION_FP_RATE_FLOOR:
        d.suggestions.append(
            f"精度缺口达 {worst_rate:.0%}，优先收敛高频误报规则并补漏报 checker")
    return d
_SEVERE_RISK_MIN_CONFIDENCE = 0.5
def _is_severe_risk(risk: dict[str, Any]) -> bool:
    return _normalize_risk_severity(risk.get("severity")) in ("critical", "high")
def _passes_severe_risk_gate(risk: dict[str, Any]) -> bool:
    return (_is_severe_risk(risk)
            and as_float(risk.get("confidence"),
                         _SEVERE_RISK_MIN_CONFIDENCE)
            >= _SEVERE_RISK_MIN_CONFIDENCE)
_SECURITY_BASE_SCORE = 85.0
_SECURITY_RISK_PENALTY = 20.0
_SECURITY_FLOOR_SCORE = 10.0
def _sd_score_security(all_text: str, risks: list[dict[str, Any]] | None = None) -> DimensionScore:
    d = DimensionScore(dimension=QualityDimension.SECURITY,
                       score=_SECURITY_BASE_SCORE)
    if risks is None:
        risks = detect_risks(all_text)
    security_risks = [r for r in risks if _passes_severe_risk_gate(r)]
    if security_risks:
        d.score = max(
            _SECURITY_FLOOR_SCORE,
            _SECURITY_BASE_SCORE - len(security_risks) * _SECURITY_RISK_PENALTY)
        d.evidence.append(f"检测到 {len(security_risks)} 个安全风险")
        for risk in security_risks[:3]:
            _suggestion = safe_str(risk.get("suggestion") or "").strip()
            if _suggestion:
                d.suggestions.append(_suggestion)
    else:
        d.evidence.append("未检测到明显安全风险")
    return d
def _sd_score_efficiency(duration: int) -> DimensionScore:
    duration = max(0, duration)
    if duration > 600:
        score, evidence = 40.0, f"耗时 {duration}s (超过 10 分钟)"
    elif duration > 300:
        score, evidence = 60.0, f"耗时 {duration}s (超过 5 分钟)"
    elif duration > 120:
        score, evidence = 80.0, f"耗时 {duration}s (2-5 分钟)"
    else:
        score, evidence = 100.0, f"耗时 {duration}s (高效)"
    d = DimensionScore(dimension=QualityDimension.EFFICIENCY,
                       score=score, evidence=[evidence])
    if score < 70:
        d.suggestions.append("建议优化执行流程或拆分任务以减少耗时")
    return d
def _sd_score_maintainability(code_modified: bool, changed_files: list[str]) -> DimensionScore:
    d = DimensionScore(dimension=QualityDimension.MAINTAINABILITY, score=80.0)
    if code_modified:
        n = len(changed_files)
        if n == 0:
            d.evidence = ["代码已修改但未提供变更文件明细"]
        elif n > 10:
            d.score, d.evidence = 50.0, [f"修改了 {n} 个文件 (变更范围大)"]
            d.suggestions.append("建议将大范围变更拆分为多个小提交")
        elif n > 5:
            d.score, d.evidence = 70.0, [f"修改了 {n} 个文件"]
        else:
            d.evidence = [f"修改了 {n} 个文件 (范围可控)"]
    else:
        d.evidence.append("无代码变更")
    return d
def _sd_score_satisfaction(task_success: bool, error_count: int) -> DimensionScore:
    return DimensionScore(
        dimension=QualityDimension.USER_SATISFACTION,
        score=85.0 if task_success and error_count == 0 else 60.0,
        evidence=["基于任务成功率和错误数的估算"])
_LOG_QUALITY_WEIGHT = 0.5
_LOG_QUALITY_UNKNOWN_SCORE = 80.0
_LOG_QUALITY_UNMEASURED_EVIDENCE = "日志质量不可度量（采集通道未产出有效评分）"
def _log_quality_neutral(evidence_text: str) -> DimensionScore:
    return DimensionScore(
        dimension=QualityDimension.LOG_QUALITY,
        weight=_LOG_QUALITY_WEIGHT,
        score=_LOG_QUALITY_UNKNOWN_SCORE,
        evidence=[evidence_text],
    )
def score_log_quality(
    log_quality_summary: dict[str, Any] | None = None,
) -> DimensionScore:
    if not isinstance(log_quality_summary, dict) or not log_quality_summary:
        return _log_quality_neutral(
            f"无日志数据，默认 {_LOG_QUALITY_UNKNOWN_SCORE:.0f} 分")
    quality_score = safe_float(log_quality_summary.get("quality_score"), None)
    field_completeness = safe_float(
        log_quality_summary.get("field_completeness"), None)
    if (not as_bool(log_quality_summary.get("metrics_available"),
                    default=True)
            or quality_score is None or quality_score < 0
            or (field_completeness is not None and field_completeness < 0)):
        return _log_quality_neutral(_LOG_QUALITY_UNMEASURED_EVIDENCE)
    normalized_score = max(0.0, min(100.0, quality_score))
    evidence = _log_quality_evidence(
        normalized_score, as_int(log_quality_summary.get("total_entries")),
        field_completeness,
        as_int(log_quality_summary.get("parse_error_count")),
        as_int(log_quality_summary.get("chain_break_count")),
        ensure_list(log_quality_summary.get("issues")))
    return DimensionScore(
        dimension=QualityDimension.LOG_QUALITY,
        weight=_LOG_QUALITY_WEIGHT,
        score=normalized_score,
        evidence=evidence,
    )
def _log_quality_evidence(
    quality_score: float,
    total_entries: int,
    field_completeness: float | None,
    parse_errors: int,
    chain_breaks: int,
    issues: list,
) -> list[str]:
    completeness_text = (
        "不可度量" if field_completeness is None
        else f"{min(1.0, max(0.0, field_completeness)):.2%}")
    evidence = [
        f"日志质量评分: {quality_score:.1f}/100",
        f"日志条目数: {total_entries}",
        f"字段完整性: {completeness_text}",
    ]
    if parse_errors > 0:
        evidence.append(f"JSON 解析错误: {parse_errors} 条")
    if chain_breaks > 0:
        evidence.append(f"日志链断裂: {chain_breaks} 处")
    for issue in issues[:5]:
        if not isinstance(issue, dict):
            continue
        issue_type = safe_str(issue.get("type") or "").strip()
        detail = safe_str(issue.get("detail") or "").strip()
        if not (issue_type or detail):
            continue
        evidence.append(": ".join(
            part for part in (issue_type, detail[:60]) if part))
    return evidence
_RISK_LEVEL_BY_RANK: dict[int, str] = {
    rank: level for level, rank in _SEVERITY_ORDER.items()}
def _sd_calc_risk_level(all_text: str, risks: list[dict[str, Any]] | None = None) -> str:
    if risks is None:
        risks = detect_risks(all_text)
    scored = [r for r in risks
              if not _is_severe_risk(r) or _passes_severe_risk_gate(r)]
    if not scored:
        return "low"
    max_risk = min(scored, key=_severity_rank)
    return _RISK_LEVEL_BY_RANK.get(_severity_rank(max_risk), "low")
_INNOVATION_KEYWORDS = (
    "新增", "重写", "重构", "升级", "自动化", "闭环", "反馈", "验证",
    "修复", "优化", "迁移", "适配", "集成", "拆分", "统一",
    "new", "rewrite", "refactor", "upgrade", "automation", "automated",
    "closed loop", "feedback", "validation", "verify", "fix", "fixed",
    "fixes", "optimize", "optimization", "migration",
    "migrate", "adapter", "integration", "integrate",
    "split", "unify", "unified", "enhance",
    "improve",
)
_CONSISTENCY_KEYWORDS = (
    "修复", "优化", "升级", "增强", "重构",
    "fix", "fixed", "fixes", "optimize", "optimized", "upgrade",
    "upgraded", "enhance", "enhanced", "refactor", "refactored",
    "improve", "improved",
)
def _keyword_present(text: str, keyword: str) -> bool:
    folded = text.casefold()
    key = keyword.casefold()
    if key.isascii() and any(ch.isalpha() for ch in key):
        suffix = (r"(?:s|es|ed|d|ing)?" if len(key) >= 5 else "")
        return re.search(
            rf"(?<![a-z0-9_]){re.escape(key)}{suffix}(?![a-z0-9_])", folded
        ) is not None
    return key in folded
def _join_spaced(*parts) -> str:
    chunks: list[str] = []
    for part in parts:
        if isinstance(part, str):
            chunks.append(part)
        elif part is None:
            continue
        else:
            chunks.extend(safe_str(x) for x in part)
    return " ".join(chunks)
def _evaluate_innovation(summary: str, changed_files: list[str],
                         improvements: list[str]) -> tuple[float, list[str], list[str]]:
    score = 60.0
    evidence: list[str] = []
    suggestions: list[str] = []
    combined = _join_spaced(summary, changed_files, improvements)
    innovation_hits = [kw for kw in _INNOVATION_KEYWORDS
                       if _keyword_present(combined, kw)]
    if len(innovation_hits) >= 5:
        score += 25
        evidence.append(f"改进建议包含 {len(innovation_hits)} 个创新关键词")
    elif len(innovation_hits) >= 2:
        score += 12
        evidence.append("改进建议包含创新要素")
    else:
        evidence.append("改进建议创新性不足")
    if changed_files:
        evidence.append(f"修改了 {len(changed_files)} 个文件")
    else:
        evidence.append("无文件变更")
    if score < 70:
        suggestions.append("建议尝试更创新的方案或工具组合")
    return score, evidence, suggestions
def _evaluate_consistency(summary: str, error_count: int,
                          code_modified: bool) -> tuple[float, list[str], list[str]]:
    score = 80.0
    evidence: list[str] = []
    if error_count == 0:
        score += 5
        evidence.append("本次会话无错误")
    else:
        evidence.append(f"本次会话 {error_count} 个错误")
    if code_modified:
        if any(_keyword_present(summary, kw)
               for kw in _CONSISTENCY_KEYWORDS):
            score += 5
            evidence.append("变更方向与历史优化路线一致")
    else:
        evidence.append("无代码变更,行为稳定")
    return score, evidence, []
DEFAULT_WEIGHT_TEMPLATE = "default"
_WEIGHT_TEMPLATES: dict[str, dict[str, float]] = {
    DEFAULT_WEIGHT_TEMPLATE: {
        "completeness": 1.5, "accuracy": 1.5, "security": 1.5,
        "efficiency": 1.0, CAT_MAINTAINABILITY: 1.0, "innovation": 0.5,
        "consistency": 1.0, "user_satisfaction": 1.0,
    },
    "code_review": {
        "completeness": 1.0, "accuracy": 2.0, "security": 1.5,
        "efficiency": 0.5, CAT_MAINTAINABILITY: 2.0, "innovation": 0.5,
        "consistency": 1.5, "user_satisfaction": 0.5,
    },
    "bug_fix": {
        "completeness": 2.0, "accuracy": 2.0, "security": 1.0,
        "efficiency": 0.5, CAT_MAINTAINABILITY: 1.0, "innovation": 0.0,
        "consistency": 1.5, "user_satisfaction": 1.5,
    },
}
def _sanitize_weight(value: Any, default: float) -> float:
    num = as_float(value, default)
    return num if num >= 0 else default
def _normalize_detected_risks(detected_risks):
    if detected_risks is None:
        return None
    if isinstance(detected_risks, (tuple, set, frozenset)):
        detected_risks = list(detected_risks)
    if not isinstance(detected_risks, list):
        return None
    if not detected_risks:
        return detected_risks
    filtered = [risk for risk in detected_risks if isinstance(risk, dict)]
    return filtered or None
def _resolve_weights(custom_weights, weight_template: str) -> dict[str, float]:
    if custom_weights is not None and not isinstance(custom_weights, dict):
        custom_weights = None
    if not isinstance(weight_template, str):
        weight_template = DEFAULT_WEIGHT_TEMPLATE
    weights = dict(_WEIGHT_TEMPLATES.get(
        weight_template, _WEIGHT_TEMPLATES[DEFAULT_WEIGHT_TEMPLATE]))
    if custom_weights:
        custom_weights = dict(custom_weights)
        if "satisfaction" in custom_weights:
            custom_weights.setdefault(
                QualityDimension.USER_SATISFACTION.value,
                custom_weights["satisfaction"])
            del custom_weights["satisfaction"]
        template_weights = dict(weights)
        weights = {**template_weights, **custom_weights}
        for key in list(weights):
            weights[key] = _sanitize_weight(
                weights[key], float(template_weights.get(key, 1.0)))
    return weights
def _weighted_dimension(score: DimensionScore, weights: dict[str, float],
                        weight_key: str) -> DimensionScore:
    score.weight = weights[weight_key]
    return score
def _dimension_from_evaluation(
    dimension: QualityDimension, weight: float,
    evaluation: tuple[float, list[str], list[str]],
) -> DimensionScore:
    score, evidence, suggestions = evaluation
    return DimensionScore(dimension=dimension, weight=weight, score=score,
                          evidence=evidence, suggestions=suggestions)
def _apply_report_totals(report: QualityReport) -> None:
    total_weight = 0
    weighted_score = 0
    strengths: list[str] = []
    weaknesses: list[str] = []
    for dimension in report.dimensions:
        total_weight += dimension.weight
        weighted_score += dimension.score * dimension.weight
        if dimension.score >= 80:
            strengths.append(dimension.dimension.value)
        elif dimension.score < 60:
            weaknesses.append(dimension.dimension.value)
    if total_weight > 0:
        if math.isfinite(total_weight) and math.isfinite(weighted_score):
            overall_score = weighted_score / total_weight
        else:
            max_weight = max(d.weight for d in report.dimensions)
            scaled_total = math.fsum(
                d.weight / max_weight for d in report.dimensions)
            scaled_score = math.fsum(
                d.score * (d.weight / max_weight) for d in report.dimensions)
            overall_score = scaled_score / scaled_total
        report.overall_score = round(overall_score, 1)
    report.grade = grade_from_score(report.overall_score)
    report.strengths = strengths
    report.weaknesses = weaknesses
def _compose_report(dims: list[DimensionScore], all_text: str,
                    detected_risks: list[dict[str, Any]]) -> QualityReport:
    report = QualityReport(dimensions=dims)
    _apply_report_totals(report)
    report.risk_level = _sd_calc_risk_level(all_text, risks=detected_risks)
    return report
def score_dimensions(
    task_success: bool, error_count: int, duration: int,
    code_modified: bool, changed_files: list[str],
    summary: str, risks: list[str], improvements: list[str],
    custom_weights: dict[str, float] | None = None,
    weight_template: str = DEFAULT_WEIGHT_TEMPLATE,
    detected_risks: list[dict[str, Any]] | None = None,
    precision_metrics: dict | None = None,
) -> QualityReport:
    duration = max(0, as_int(duration))
    error_count = max(0, as_int(error_count))
    task_success = as_bool(task_success, default=True)
    code_modified = as_bool(code_modified, default=False)
    summary = summary if isinstance(summary, str) else safe_str(summary or "")
    risks = ensure_str_list(risks)
    improvements = ensure_str_list(improvements)
    changed_files = ensure_str_list(changed_files)
    detected_risks = _normalize_detected_risks(detected_risks)
    weights = _resolve_weights(custom_weights, weight_template)
    dims: list[DimensionScore] = [
        _weighted_dimension(_sd_score_completeness(task_success),
                            weights, "completeness"),
        _weighted_dimension(_sd_score_accuracy(error_count, precision_metrics),
                            weights, "accuracy"),
    ]
    all_text = _join_spaced(summary, risks, improvements)
    if detected_risks is None:
        detected_risks = detect_risks(all_text)
    dims.extend([
        _weighted_dimension(
            _sd_score_security(all_text, risks=detected_risks),
            weights, "security"),
        _weighted_dimension(_sd_score_efficiency(duration),
                            weights, "efficiency"),
        _weighted_dimension(
            _sd_score_maintainability(code_modified, changed_files),
            weights, CAT_MAINTAINABILITY),
        _dimension_from_evaluation(
            QualityDimension.INNOVATION, weights["innovation"],
            _evaluate_innovation(summary, changed_files, improvements)),
        _dimension_from_evaluation(
            QualityDimension.CONSISTENCY, weights["consistency"],
            _evaluate_consistency(summary, error_count, code_modified)),
        _weighted_dimension(
            _sd_score_satisfaction(task_success, error_count), weights,
            QualityDimension.USER_SATISFACTION.value),
    ])
    return _compose_report(dims, all_text, detected_risks)
def _merge_auto_key(item: str, prefix: str) -> str:
    text = safe_str(item).strip()
    marker = f"{prefix} "
    if prefix and text.startswith(marker):
        text = text[len(marker):].strip()
    return text
def _merge_auto_list(current: list[str], incoming: list[str],
                     prefix: str) -> list[str]:
    merged = list(coerce_text_list(current))
    seen = {_merge_auto_key(item, prefix) for item in merged}
    for item in coerce_text_list(incoming):
        key = _merge_auto_key(item, prefix)
        if not key or key in seen:
            continue
        merged.append(f"{prefix} {key}" if prefix else key)
        seen.add(key)
    return merged
def _merge_auto_params(
    summary: str, risks: list[str], improvements: list[str],
    auto_params: dict[str, Any],
) -> tuple[str, list[str], list[str]]:
    if not summary and auto_params.get("summary"):
        summary = auto_params["summary"]
    risks = _merge_auto_list(risks, auto_params.get("risks", []), "[自动]")
    improvements = _merge_auto_list(improvements, auto_params.get("improvements", []), "[自动]")
    return summary, risks, improvements
def _build_quality_report_dict(qr: QualityReport) -> dict:
    return {
        "overall_score": qr.overall_score, "grade": qr.grade,
        "strengths": qr.strengths, "weaknesses": qr.weaknesses,
        "risk_level": qr.risk_level,
        "dimensions": [
            {"dimension": d.dimension.value, "score": d.score, "weight": d.weight,
             "evidence": d.evidence, "suggestions": d.suggestions}
            for d in qr.dimensions]}
class _ContextFacts(NamedTuple):
    duration: int
    task_success: bool
    code_modified: bool
    error_count: int
def _ctx_facts(auto_context: dict | None) -> _ContextFacts:
    auto_ctx = auto_context or {}
    return _ContextFacts(
        duration=normalize_scalar(auto_ctx.get("duration"), 0, want_int=True),
        task_success=as_bool(auto_ctx.get("task_success"), default=True),
        code_modified=as_bool(auto_ctx.get("code_modified"), default=False),
        error_count=len(ensure_str_list(auto_ctx.get("errors"))),
    )
def _run_auto_analysis(auto_context, summary, risks, improvements, memory_candidates):
    auto_analyzed = False
    pattern_matches = []
    auto_ctx = auto_context or {}
    try:
        facts = _ctx_facts(auto_ctx)
        analysis = analyze_session(
            user_messages=auto_ctx.get("user_messages", []),
            tool_calls=auto_ctx.get("tool_calls", []),
            errors=auto_ctx.get("errors", []),
            code_modified=facts.code_modified,
            changed_files=auto_ctx.get("changed_files", []),
            duration=facts.duration,
            task_success=facts.task_success,
            session_summary_hint=summary,
        )
        auto_params = to_fupan_params(analysis)
        pattern_matches = analysis.pattern_matches
        summary, risks, improvements = _merge_auto_params(
            summary, risks, improvements, auto_params)
        if not memory_candidates:
            memory_candidates = analysis.memory_candidates
        auto_analyzed = True
    except Exception as e:
        _log.warning("[fupan] 自动分析跳过: %s", e)
    return {
        "auto_analyzed": auto_analyzed,
        "pattern_matches": pattern_matches,
        "summary": summary,
        "risks": risks,
        "improvements": improvements,
        "memory_candidates": memory_candidates,
    }
def _has_related_key(text: str) -> bool:
    return any(line.startswith("related:") for line in text.split("\n"))
def _inject_related_line(content: str, related_yaml: str) -> str | None:
    bounds = frontmatter_bounds(content)
    if bounds is None:
        return None
    nl, end = bounds
    head = content[:end + len(nl)]
    return None if _has_related_key(head) else f"{head}{related_yaml}{nl}{content[end + len(nl):]}"
def _is_write_action(action: Any) -> bool:
    return isinstance(action, str) and action in MEMORY_WRITE_ACTIONS
def _collect_related_paths(memory_operations) -> list[str]:
    paths = [op["path"] for op in memory_operations
             if isinstance(op, dict)
             and _is_write_action(op.get("action"))
             and isinstance(op.get("path"), str)]
    return [p for p in dict.fromkeys(paths) if p]
def _inject_op_related(op: dict, related_paths: list[str]) -> None:
    others = [p for p in related_paths if p != op.get("path", "")][:5]
    if not others:
        return
    related_yaml = json.dumps(others, ensure_ascii=False)
    new_content = _inject_related_line(
        op.get("content", ""), f"related: {related_yaml}")
    if new_content is not None:
        op["content"] = new_content
    else:
        _log.debug("[fupan] related 注入跳过（无规范 frontmatter 或已有 related）: %s",
                   op.get("path", ""))
def _apply_related_links(memory_operations):
    related_paths = _collect_related_paths(memory_operations)
    if len(related_paths) <= 1:
        return
    for op in memory_operations:
        if not isinstance(op, dict) or op.get("action") != "add":
            continue
        _inject_op_related(op, related_paths)
def _ensure_patch_old_text(memory_operations: list) -> None:
    for op in memory_operations:
        if not isinstance(op, dict) or op.get("action") != "patch":
            continue
        _ot = op.get("old_text")
        if not isinstance(_ot, str) or not _ot.strip():
            _log.warning(
                "[fupan] patch 缺少 old_text 锚点(写前置校验将拒绝): %s",
                op.get("path", ""))
def _fp_trigger_info(auto_context: dict | None, summary: str) -> dict[str, object]:
    trigger_info: dict[str, Any] = {}
    try:
        auto_ctx = auto_context or {}
        user_msgs = coerce_text_list(auto_ctx.get("user_messages"))
        if not user_msgs and auto_ctx.get("user_msg"):
            user_msgs = [str(auto_ctx["user_msg"])]
        facts = _ctx_facts(auto_ctx)
        trigger_info = build_trigger_signals(
            tools_used=collect_tools_used(auto_ctx),
            user_messages=user_msgs,
            outcome_detail=auto_ctx.get("outcome_detail", ""),
            summary=summary,
            duration=facts.duration,
            task_success=facts.task_success,
            error_count=facts.error_count,
            code_modified=facts.code_modified,
        )
        trigger_info["information_density"] = compute_information_density(
            summary or "")
        trigger_info["available"] = True
    except Exception as trig_err:
        _log.warning("[fupan] 触发判定/密度评估跳过: %s", trig_err)
        trigger_info = {"available": False, "error": safe_str(trig_err)[:100]}
    return trigger_info
def _int_score(score: float) -> int:
    return math.floor(score + 0.5)
def _fp_recalc_totals(qr: QualityReport) -> int:
    _apply_report_totals(qr)
    return _int_score(qr.overall_score)
def _inject_log_quality_dimension(qr: QualityReport,
                                  log_quality_summary: dict) -> int:
    log_dim = score_log_quality(log_quality_summary)
    qr.dimensions.append(log_dim)
    quality_score = _fp_recalc_totals(qr)
    _log.info("[fupan] 日志质量维度注入: score=%.1f, overall=%.1f",
              log_dim.score, qr.overall_score)
    return quality_score
def _fp_quality(auto_context: dict | None, summary: str,
                 risks: list[str], improvements: list[str],
                 log_quality_summary: dict,
                 detected_risks: list[dict[str, Any]] | None = None,
                 precision_metrics: dict | None = None,
                 ) -> tuple[QualityReport, int]:
    auto_ctx = auto_context or {}
    facts = _ctx_facts(auto_ctx)
    qr = score_dimensions(
        task_success=facts.task_success,
        error_count=facts.error_count,
        duration=facts.duration,
        code_modified=facts.code_modified,
        changed_files=coerce_text_list(auto_ctx.get("changed_files")),
        summary=summary, risks=risks, improvements=improvements,
        detected_risks=detected_risks,
        precision_metrics=precision_metrics)
    quality_score = _inject_log_quality_dimension(qr, log_quality_summary)
    return qr, quality_score
def _fp_detail_key(cand: dict) -> str:
    if not isinstance(cand, dict):
        return ""
    detail = cand.get("detail")
    if not isinstance(detail, str):
        detail = safe_str(detail) if detail else ""
    return detail
def _fp_merge_candidates(memory_candidates: list[dict], risks: list[str],
                         improvements: list[str], detected_risks: list[dict],
                         pattern_matches: list[dict]) -> list[dict]:
    structured_candidates = generate_memory_candidates(
        risks, improvements, detected_risks, pattern_matches)
    if not memory_candidates:
        memory_candidates = structured_candidates
    else:
        existing_keys = {_fp_detail_key(c) for c in memory_candidates
                         if isinstance(c, dict)}
        for cand in structured_candidates:
            key = _fp_detail_key(cand)
            if key not in existing_keys:
                memory_candidates.append(cand)
                existing_keys.add(key)
    return memory_candidates
def _pdca_deduct_consistency(qr: QualityReport, quality_score: int) -> int:
    for dim in getattr(qr, "dimensions", None) or ():
        if dim.dimension != QualityDimension.CONSISTENCY:
            continue
        dim.score = max(0, dim.score - 5)
        if isinstance(dim.evidence, list):
            dim.evidence.append("PDCA追踪不可用,一致性扣5分")
        return _fp_recalc_totals(qr)
    return quality_score
def _fp_run_pdca(improvements: list[str], auto_context: dict | None,
                 existing_memories: list[dict] | None,
                 memory_candidates: list[dict], qr: QualityReport,
                 quality_score: int) -> tuple[dict, list[dict], QualityReport, int]:
    pdca_result, memory_candidates, degraded = run_fupan_pdca(
        improvements, auto_context, existing_memories, memory_candidates)
    if degraded:
        try:
            quality_score = _pdca_deduct_consistency(qr, quality_score)
        except Exception as _deduct_err:
            _log.warning("[fupan] PDCA降级扣分跳过: %s", _deduct_err)
    return pdca_result, memory_candidates, qr, quality_score
def _fupan_message(result: dict[str, Any]) -> str:
    ops = result.get("memory_operations")
    rejected = result.get("memory_rejected")
    op_count = len(ops) if isinstance(ops, list) else 0
    rejected_count = len(rejected) if isinstance(rejected, list) else 0
    return (f"复盘完成: {op_count}条记忆操作待执行, "
            f"{rejected_count}条被拒绝")
_FUPAN_SEQ = 0
def _next_result_id() -> str:
    global _FUPAN_SEQ
    _FUPAN_SEQ += 1
    return f"fupan-{int(time.time() * 1000)}-{_FUPAN_SEQ}"
def _result_skeleton(ok: bool, summary: str = "") -> dict[str, Any]:
    return {
        "ok": ok,
        "result_id": _next_result_id(),
        "summary": summary or "会话复盘",
        "memory_operations": [],
        "memory_rejected": [],
        "quality_report": {},
        "quality_score": 0,
        "detected_risks": [],
        "risks_count": 0,
        "improvements_count": 0,
        "auto_analyzed": False,
        "audit_summary": {},
        "swallowed_summary": {},
        "ai_review_summary": {},
        "log_quality_summary": {},
        "pdca": {},
        "trigger_info": {},
        "memory_density": {},
        "message": "",
    }
def _append_unique(seq: list[str], item: str) -> None:
    if item not in seq:
        seq.append(item)
def _append_str_items(seq: list[str], items: Any, prefix: str = "") -> None:
    for item in ensure_list(items):
        if isinstance(item, str) and item:
            _append_unique(seq, f"{prefix}{item}")
def _fp_consume_defense(risks: list[str], improvements: list[str],
                        skill_dir: str = "") -> None:
    _raw_defense = _summarize_defense_feedback(skill_dir)
    defense_summary = _raw_defense if isinstance(_raw_defense, dict) else {}
    _df_risk = defense_summary.get("risk_signal")
    if isinstance(_df_risk, str) and _df_risk:
        _append_unique(risks, _df_risk)
    _df_recs = ensure_list(defense_summary.get("recommendations"))
    _append_str_items(improvements, _df_recs[:10], "[防御反馈] ")
    _df_total = as_int(defense_summary.get("total"))
    if _df_total:
        _log.info("[fupan] 防御反馈消费: %d 条事件, 矛盾 %d 条, 回归失败 %d 次, 建议 %d 条",
                  _df_total,
                  as_int(defense_summary.get("contradiction_total")),
                  as_int(defense_summary.get("regression_failures")),
                  len(_df_recs))
def _fp_consume_ai_review_risks(risks: list[str], improvements: list[str],
                                skill_dir: str | None = None) -> dict:
    _summary = load_ai_review_summary(skill_dir)
    if _summary["total"] <= 0:
        return _summary
    _fp_ratio = _summary["fp_ratio"]
    if _fp_ratio >= 0.3:
        _fp_risk = (f"[AI审核] 误报判定占比 {_fp_ratio:.0%}"
                    f"（{_summary['fp_count']}/{_summary['total']}），"
                    f"相关规则疑似过宽，建议校准规则阈值并补充反例")
        _append_unique(risks, _fp_risk)
        _fp_imp = ("[AI审核] 对误报率高的规则族逐一复核（触发条件/阈值/"
                   "上下文证据），用阳性对照与反例重新校准")
        _append_unique(improvements, _fp_imp)
    _fail_count = (as_int(_summary.get("exec_failed_count"))
                   or len(ensure_list(_summary.get("exec_failed"))))
    if _fail_count:
        _fail_risk = (f"[AI审核] {_fail_count} 条批准治疗"
                      f"执行未成功，治疗链路存在断裂，需排查失败根因")
        _append_unique(risks, _fail_risk)
        _fail_imp = ("[AI审核] 对执行失败的治疗逐条回溯"
                     "（审核→计划→执行→结果），修复治疗执行链路")
        _append_unique(improvements, _fail_imp)
    if _summary["top_rules"]:
        _top_txt = "、".join(f"{r}({n}次)"
                             for r, n in _summary["top_rules"])
        _rule_risk = (f"[AI审核] 高频被审规则: {_top_txt}，"
                      f"建议优先复核这些规则的质量与阈值")
        _append_unique(risks, _rule_risk)
    _log.info("[fupan] AI审核裁决消费: %d 条裁决, 误报 %d (%.0f%%), "
              "执行失败 %d", _summary["total"], _summary["fp_count"],
              _fp_ratio * 100, _fail_count)
    return _summary
def _fp_consume_audit_channel(risks: list[str]) -> dict:
    audit_summary = load_audit_summary()
    _high_risk_count = as_int(audit_summary.get("high_risk_count"))
    if not _high_risk_count:
        _high_risk_count = len(ensure_list(audit_summary.get("high_risk_events")))
    if _high_risk_count > 0:
        audit_risk = (f"[审计留痕] 检测到 {_high_risk_count} 条高危操作记录"
                      f"（回滚 {audit_summary['rollback_count']} 次）")
        _append_unique(risks, audit_risk)
        _log.info("[fupan] 审计事件消费: %d 条高危 / %d 条审计记录, 回滚 %d 次",
                  _high_risk_count, audit_summary["total"],
                  audit_summary["rollback_count"])
    return audit_summary
def _fp_consume_perf_channel(risks: list[str]) -> dict:
    perf_summary = load_perf_summary()
    if perf_summary["total"] > 0:
        if perf_summary["degraded"]:
            _append_str_items(risks, perf_summary["signals"], "[性能退化] ")
        _log.info("[fupan] 性能趋势消费: %d 条打点, %d 阶段, 退化信号 %d 个",
                  perf_summary["total"], len(perf_summary["per_phase"]),
                  len(perf_summary["signals"]))
    return perf_summary
def _fp_consume_swallowed_channel(risks: list[str]) -> dict:
    swallowed_summary = load_swallowed_summary()
    if swallowed_summary["total"] > 0:
        swallow_risk = (f"[静默异常] 检测到 {swallowed_summary['total']} 条被吞没的异常"
                        f"（高频模块: {', '.join(m for m, _ in swallowed_summary['high_freq_modules'][:3]) or '无'}）")
        _append_unique(risks, swallow_risk)
        _log.info("[fupan] 静默异常消费: %d 条记录, %d 个模块",
                  swallowed_summary["total"], len(swallowed_summary["by_module"]))
    return swallowed_summary
def _fp_consume_bug_intercept_channel(risks: list[str]) -> dict:
    bug_summary = load_bug_intercept_summary()
    if bug_summary["total"] > 0:
        top_bugs = "、".join(f"{c}({n}次)" for c, n in bug_summary["high_freq"][:3]) or "无"
        bug_risk = (f"[BUG拦截] 本次编写前/编写时门禁拦截 {bug_summary['total']} 个 BUG"
                    f"（高频类型: {top_bugs}）")
        _append_unique(risks, bug_risk)
        _log.info("[fupan] BUG拦截消费: %d 条记录, %d 类检测器",
                  bug_summary["total"], len(bug_summary["by_check"]))
    return bug_summary
def _fp_consume_detector_liveness(risks: list[str], improvements: list[str]) -> None:
    try:
        _lv_events = load_detector_liveness_events()
        if _lv_events:
            _evt = _lv_events[-1]
            _payload = _evt.get("payload") if isinstance(_evt, dict) else None
            _latest = _payload if isinstance(_payload, dict) else {}
            _dead = ensure_list(_latest.get("dead_rules"))
            if _dead:
                _lv_risk = (f"[检测器活性] 阳性对照探针发现 {len(_dead)} 个失效检测器: "
                            f"{', '.join(str(r) for r in _dead[:8])}；"
                            f"对应规则的真实问题可能不可见，需修复检测器注册/规则链")
                _append_unique(risks, _lv_risk)
                _lv_imp = ("[检测器活性] 对失效检测器逐个溯源（规则删除/注册表断裂/"
                           "异常被吞），修复后用预防库反例重验活性")
                _append_unique(improvements, _lv_imp)
            _log.info("[fupan] 检测器活性消费: 最新探针 %d/%d 失效",
                      len(_dead), as_int(_latest.get("probed")))
    except Exception as _lv_e:
        _log.warning("[fupan] 检测器活性消费跳过: %s", _lv_e, exc_info=True)
def fp_consume_event_risks(risks: list[str], improvements: list[str],
                           skill_dir: str | None = None) -> tuple[dict, dict, dict]:
    audit_summary = _fp_consume_audit_channel(risks)
    _fp_consume_perf_channel(risks)
    swallowed_summary = _fp_consume_swallowed_channel(risks)
    _fp_consume_defense(risks, improvements, skill_dir or "")
    _fp_consume_bug_intercept_channel(risks)
    ai_review_summary = _fp_consume_ai_review_risks(risks, improvements, skill_dir)
    _fp_consume_detector_liveness(risks, improvements)
    return audit_summary, swallowed_summary, ai_review_summary
def _ensure_list_key(ctx: dict[str, Any], key: str) -> list:
    val = ctx.get(key)
    if isinstance(val, list):
        return val
    if isinstance(val, (tuple, set, frozenset)):
        val = list(val)
    elif isinstance(val, str):
        val = [val] if val else []
    else:
        val = []
    ctx[key] = val
    return val
def inject_log_findings_into_review(
    review_context: dict[str, Any],
    log_findings: list[Any],
) -> dict[str, Any]:
    ctx = review_context if isinstance(review_context, dict) else {}
    log_findings = ensure_list(log_findings)
    if not log_findings:
        return ctx
    risks = _ensure_list_key(ctx, "risks")
    improvements = _ensure_list_key(ctx, "improvements")
    archived = _ensure_list_key(ctx, "log_driven_findings")
    for f in log_findings:
        _inject_one_log_finding(f, risks, improvements, archived)
    return ctx
def _inject_one_log_finding(
    finding: Any,
    risks: list[str],
    improvements: list[str],
    archived: list[Any],
) -> None:
    title, description, action, payload = _log_finding_fields(finding)
    if not (title or description or action):
        return
    if title or description:
        detail = ": ".join(part for part in (title, description) if part)
        _append_unique(risks, f"[日志驱动] {detail}")
    if action:
        _append_unique(improvements, f"[日志驱动] {action}")
    archived.append(payload)
def _log_finding_fields(f) -> tuple[str, str, str, Any]:
    title = _finding_field(f, "title")
    description = _finding_field(f, "description")
    action = _finding_field(f, "suggested_action")
    if isinstance(f, dict):
        return title, description, action, f
    to_dict = getattr(f, "to_dict", None)
    payload = (to_dict() if callable(to_dict)
               else {"title": title, "description": description,
                     "suggested_action": action})
    return title, description, action, payload
def _finding_field(finding: Any, key: str) -> str:
    if isinstance(finding, dict):
        return text_or_empty(finding.get(key))
    return text_or_empty(getattr(finding, key, None))
def _fp_consume_log_evolution(risks: list[str], improvements: list[str]) -> tuple[list[str], list[str]]:
    try:
        _lde_raw = run_log_driven_evolution(close_resolved=True)
        _lde_result = _lde_raw if isinstance(_lde_raw, dict) else {}
        _open_findings = as_int(_lde_result.get("open_findings"))
        if _lde_result.get("status") == "error":
            _append_unique(
                risks,
                f"[日志驱动] {_lde_result.get('message') or '日志驱动分析失败'}")
        if _lde_result.get("status") == "ok" and _open_findings > 0:
            _review_ctx = inject_log_findings_into_review(
                {"risks": risks, "improvements": improvements},
                _lde_result.get("findings"),
            )
            risks = _review_ctx["risks"]
            improvements = _review_ctx["improvements"]
            _log.info("[fupan] 日志驱动自进化增强: %d 条发现 (%d 待处理)",
                      as_int(_lde_result.get("total_findings")), _open_findings)
        risks = _fp_consume_closure_stats(risks, _lde_result)
    except Exception as _lde_err:
        _log.warning("[fupan] 日志驱动自进化增强跳过: %s", _lde_err, exc_info=True)
    return risks, improvements
def _fp_consume_closure_stats(risks: list[str], lde_result: dict) -> list[str]:
    _raw_stats = lde_result.get("closure_stats")
    _closure_stats = _raw_stats if isinstance(_raw_stats, dict) else {}
    _active_open = as_int(_closure_stats.get("active_open"))
    _recurrence_rate = as_float(_closure_stats.get("recurrence_rate"), 0.0)
    _total_closed = as_int(_closure_stats.get("total_closed"))
    if _active_open > 5:
        _closure_risk = (f"[销项管理] 未销项活跃发现 {_active_open} 条，"
                         f"处理速度可能跟不上发现问题速度")
        _append_unique(risks, _closure_risk)
    if _recurrence_rate > 0.3:
        _recur_risk = (f"[销项管理] 销项后复发率 {_recurrence_rate:.1%}，"
                       f"修复不彻底需加强治疗安全网")
        _append_unique(risks, _recur_risk)
    _log.info("[fupan] 销项统计消费: 已销项 %d, 活跃 %d, 复发率 %.2f%%",
              _total_closed, _active_open, _recurrence_rate * 100)
    return risks
def _fp_register_log_rule_candidates() -> None:
    try:
        _rc_raw = register_rule_candidates()
        _rc_result = _rc_raw if isinstance(_rc_raw, dict) else {}
        _log.info("[fupan] 规则候选注册固化: registered=%d, skipped=%d, "
                  "failed=%d, verified=%d",
                  as_int(_rc_result.get("registered")),
                  as_int(_rc_result.get("skipped")),
                  as_int(_rc_result.get("failed")),
                  as_int(_rc_result.get("verified")))
    except Exception as _rc_err:
        _log.warning("[fupan] 规则候选注册固化跳过: %s", _rc_err, exc_info=True)
def _fp_consume_log_quality_channel(risks: list[str],
                                     improvements: list[str]) -> dict:
    log_quality_summary = load_log_quality_summary()
    if log_quality_summary["log_quality_risk"]:
        lq_risk = log_quality_summary["log_quality_risk"]
        _append_unique(risks, lq_risk)
        _log.info("[fupan] 日志质量消费: 质量评分 %.1f, 发现 %d 条",
                  log_quality_summary["quality_score"],
                  len(log_quality_summary["log_findings"]))
    _append_str_items(improvements,
                      log_quality_summary.get("log_improvements"))
    return log_quality_summary
def _fp_consume_growth_channel(risks: list[str],
                               skill_dir: str | None = None) -> dict:
    if not skill_dir:
        return {
            "ok": False, "unavailable": True,
            "reason": "project_root_required", "snapshot": {},
            "degraded": False, "signals": [], "history_count": 0,
        }
    growth_summary = load_growth_summary(project_root=skill_dir)
    if growth_summary.get("ok"):
        if growth_summary.get("degraded"):
            _append_str_items(risks, growth_summary.get("signals"),
                              "[规模退化] ")
        _log.info("[fupan] 规模趋势消费: %d 文件/%d 行, 历史 %d 次快照, 退化信号 %d 个",
                  growth_summary["snapshot"].get("py_files", 0),
                  growth_summary["snapshot"].get("total_lines", 0),
                  growth_summary["history_count"],
                  len(growth_summary["signals"]))
    return growth_summary
def fp_consume_log_growth(risks: list[str], improvements: list[str],
                          skill_dir: str | None = None) -> tuple[list[str], list[str], dict]:
    log_quality_summary = _fp_consume_log_quality_channel(risks, improvements)
    _fp_consume_growth_channel(risks, skill_dir)
    risks, improvements = _fp_consume_log_evolution(risks, improvements)
    _fp_register_log_rule_candidates()
    return risks, improvements, log_quality_summary
def _fp_normalize_inputs(risks, improvements, summary,
                         memory_quality_threshold, memory_candidates):
    risks = ensure_str_list(risks)
    improvements = ensure_str_list(improvements)
    summary = summary if isinstance(summary, str) else safe_str(summary or "")
    if isinstance(memory_candidates, (list, tuple)):
        memory_candidates = list(memory_candidates)
    else:
        memory_candidates = ([] if memory_candidates is None
                             else [memory_candidates])
    return risks, improvements, summary, memory_quality_threshold, memory_candidates
def _fp_consume_and_detect(summary, risks, improvements, auto_context):
    detect_parts: list[Any] = [summary, risks, improvements]
    if auto_context:
        detect_parts.append(coerce_text_list(auto_context.get("errors")))
    detected_risks = detect_risks(_join_spaced(*detect_parts))
    for dr in detected_risks:
        _append_unique(
            risks, f"[自动检测] {dr['category']}: {dr['suggestion']}")
    return detected_risks
def _fp_density_governance(memory_candidates, improvements):
    density_eval = evaluate_memory_density(memory_candidates)
    if density_eval.get("low_count", 0) > 0:
        for rec in density_eval.get("recommendations", []):
            _append_unique(improvements, rec)
    return density_eval
class _IngestBundle(NamedTuple):
    audit: dict[str, Any]
    swallowed: dict[str, Any]
    ai_review: dict[str, Any]
    log_quality: dict[str, Any]
    auto_analyzed: bool
class _OperationBundle(NamedTuple):
    operations: list[dict[str, Any]]
    rejected: list[dict[str, Any]]
    density: dict[str, Any]
    quality_report: QualityReport
    quality_score: int
    pdca: dict[str, Any]
class _ProduceRequest(NamedTuple):
    memory_candidates: list[dict[str, Any]]
    risks: list[str]
    improvements: list[str]
    detected_risks: list[dict[str, Any]]
    pattern_matches: list[dict[str, Any]]
    auto_context: dict[str, Any] | None
    existing_memories: list[dict[str, Any]] | None
    memory_quality_threshold: float | None
    quality_report: QualityReport
    quality_score: int
def _fp_produce_operations(req: _ProduceRequest) -> _OperationBundle:
    existing_memories = materialize_existing_memories(req.existing_memories)
    memory_candidates = _fp_merge_candidates(
        req.memory_candidates, req.risks, req.improvements,
        req.detected_risks, req.pattern_matches)
    pdca_result, memory_candidates, qr, quality_score = _fp_run_pdca(
        req.improvements, req.auto_context, existing_memories,
        memory_candidates, req.quality_report, req.quality_score)
    memory_candidates = normalize_candidates(memory_candidates)
    density_eval = _fp_density_governance(memory_candidates, req.improvements)
    memory_passed, memory_rejected, memory_upgrades = quality_gate(
        memory_candidates, threshold=req.memory_quality_threshold,
        existing_memories=existing_memories)
    memory_operations = build_memory_operations(
        memory_passed, memory_upgrades)
    act_ops = validated_memory_operations(
        pdca_result.get("act_operations", []), "PDCA Act回写")
    if act_ops:
        memory_operations.extend(act_ops)
        _log.info("[fupan] PDCA Act回写: %d 条 patch 操作", len(act_ops))
    return _OperationBundle(memory_operations, memory_rejected, density_eval,
                            qr, quality_score, pdca_result)
def _fp_build_result(summary: str, bundle: _OperationBundle,
                     detected_risks: list[dict[str, Any]],
                     risks_count: int, improvements_count: int,
                     sources: _IngestBundle,
                     trigger_info: dict[str, object]) -> dict[str, Any]:
    result = _result_skeleton(ok=True, summary=summary)
    result.update({
        "memory_operations": bundle.operations,
        "memory_rejected": bundle.rejected,
        "quality_report": _build_quality_report_dict(bundle.quality_report),
        "quality_score": bundle.quality_score,
        "detected_risks": detected_risks,
        "risks_count": risks_count,
        "improvements_count": improvements_count,
        "auto_analyzed": sources.auto_analyzed,
        "audit_summary": sources.audit,
        "swallowed_summary": sources.swallowed,
        "ai_review_summary": sources.ai_review,
        "log_quality_summary": sources.log_quality,
        "pdca": bundle.pdca,
        "trigger_info": trigger_info,
        "memory_density": bundle.density,
    })
    result["message"] = _fupan_message(result)
    return result
def _fp_finalize_result(result: dict[str, Any],
                        memory_context: _FupanMemCtx | None,
                        output_html: str | None,
                        skill_dir: str | None) -> dict[str, Any]:
    result = apply_fupan_memory_bridge(result, memory_context)
    _apply_related_links(result["memory_operations"])
    result["message"] = _fupan_message(result)
    _ensure_patch_old_text(result["memory_operations"])
    emit_fupan_report_html(result, output_html, skill_dir)
    return result
def _fp_error_fallback(e, summary, output_html, skill_dir):
    fallback = _result_skeleton(ok=False)
    fallback["message"] = f"复盘异常终止: {safe_str(e)[:100]}"
    fallback["summary"] = (summary if isinstance(summary, str)
                           and summary else "会话复盘")
    try:
        emit_fupan_report_html(fallback, output_html, skill_dir)
    except Exception as html_err:
        _log.warning("[fupan] 失败降级 HTML 发射失败(不覆盖原始异常): %s",
                     html_err, exc_info=True)
    return fallback
def run_fupan(
    output_html: str | None = None,
    summary: str = "",
    risks: list[str] | None = None,
    improvements: list[str] | None = None,
    memory_candidates: list[dict[str, Any]] | None = None,
    auto_analyze: bool = True,
    auto_context: dict[str, Any] | None = None,
    memory_quality_threshold: float | None = None,
    existing_memories: list[dict[str, Any]] | None = None,
    memory_context: _FupanMemCtx | None = None,
    skill_dir: str | None = None,
) -> dict[str, Any]:
    auto_context = auto_context if isinstance(auto_context, dict) else None
    try:
        (risks, improvements, summary,
         memory_quality_threshold, memory_candidates) = _fp_normalize_inputs(
            risks, improvements, summary,
            memory_quality_threshold, memory_candidates)
        auto_analyzed = False
        pattern_matches: list[dict[str, Any]] = []
        audit_summary, swallowed_summary, ai_review_summary = fp_consume_event_risks(
            risks, improvements, skill_dir=skill_dir)
        risks, improvements, log_quality_summary = fp_consume_log_growth(
            risks, improvements, skill_dir=skill_dir)
        if auto_analyze and auto_context:
            auto_result = _run_auto_analysis(auto_context, summary, risks, improvements, memory_candidates)
            auto_analyzed = auto_result["auto_analyzed"]
            pattern_matches = auto_result["pattern_matches"]
            summary = auto_result["summary"]
            risks = auto_result["risks"]
            improvements = auto_result["improvements"]
            memory_candidates = auto_result["memory_candidates"]
        detected_risks = _fp_consume_and_detect(
            summary, risks, improvements, auto_context)
        trigger_info = _fp_trigger_info(auto_context, summary)
        qr, quality_score = _fp_quality(
            auto_context=auto_context, summary=summary, risks=risks,
            improvements=improvements, log_quality_summary=log_quality_summary,
            detected_risks=detected_risks,
            precision_metrics=_load_precision_metrics(skill_dir))
        bundle = _fp_produce_operations(_ProduceRequest(
            memory_candidates=memory_candidates, risks=risks,
            improvements=improvements, detected_risks=detected_risks,
            pattern_matches=pattern_matches, auto_context=auto_context,
            existing_memories=existing_memories,
            memory_quality_threshold=memory_quality_threshold,
            quality_report=qr, quality_score=quality_score))
        result = _fp_build_result(
            summary=summary, bundle=bundle, detected_risks=detected_risks,
            risks_count=len(risks), improvements_count=len(improvements),
            sources=_IngestBundle(
                audit=audit_summary, swallowed=swallowed_summary,
                ai_review=ai_review_summary, log_quality=log_quality_summary,
                auto_analyzed=auto_analyzed),
            trigger_info=trigger_info)
        return _fp_finalize_result(result=result, memory_context=memory_context,
                                   output_html=output_html, skill_dir=skill_dir)
    except Exception as e:
        _log.error("[fupan] run_fupan 异常: %s", e, exc_info=True)
        return _fp_error_fallback(e, summary, output_html, skill_dir)
_FUPAN_REPORT_FIELDS = (
    ("fupan_quality_score", "quality_score", int),
    ("memory_operations", "memory_operations", list),
    ("fupan_detected_risks", "detected_risks", list),
    ("pdca", "pdca", dict),
    ("quality_report", "quality_report", dict),
    ("detected_risks", "detected_risks", list),
    ("summary", "summary", str),
)
_FUPAN_NON_SUCCESS_STATUSES = frozenset(TX_FAILED_STATUSES) | frozenset({
    "in_progress", "running", "blocked", "skipped", "pending",
})
_FUPAN_NON_SUCCESS_COUNT_KEYS = (
    "failed", "rolled_back", "skipped", "pending_confirm",
    "suggestion", "no_fixer",
)
def _execution_count(value: Any) -> int | None:
    if value is None:
        return 0
    if isinstance(value, (list, tuple, set, frozenset, dict)):
        return len(value)
    number = safe_float(value, None)
    if number is None or not number.is_integer():
        return None
    return count_tasks(value, clamp_negative=False)
def _count_value(value: Any) -> int:
    parsed = _execution_count(value)
    return 0 if parsed is None else parsed
def _ctx_count(source: dict, key: str) -> int:
    return _count_value(source.get(key)) if isinstance(source, dict) else 0
def _score_value(value: Any) -> float:
    parsed = safe_float(value, None)
    return parsed if is_valid_memory_score(parsed) else 0.0
def _fupan_user_messages(fupan_context: dict) -> list[str]:
    return [
        f'诊断方法: {_ctx_count(fupan_context, "diag_methods")}执行/{_ctx_count(fupan_context, "diag_passed")}通过',
        f'CV发现: {_ctx_count(fupan_context, "cv_findings")}个, 规则触发: {_ctx_count(fupan_context, "cv_rules")}',
        f'治疗执行: {_ctx_count(fupan_context, "tx_executed")}项, 成功: {_ctx_count(fupan_context, "tx_succeeded")}, 失败: {_ctx_count(fupan_context, "tx_failed")}, 回滚: {_ctx_count(fupan_context, "tx_rolled_back")}',
        f'复盘评分: {safe_float(fupan_context.get("retro_score", 0), 0)}',
    ]
def _fupan_summary_hint(fupan_context: dict) -> str:
    return (f'管线复盘: CV={_ctx_count(fupan_context, "cv_findings")}发现/'
            f'{_ctx_count(fupan_context, "cv_rules")}规则, '
            f'治疗={_ctx_count(fupan_context, "tx_succeeded")}/'
            f'{_ctx_count(fupan_context, "tx_executed")}成功, '
            f'失败={_ctx_count(fupan_context, "tx_failed")}, '
            f'六环评分={safe_float(fupan_context.get("retro_score", 0), 0)}')
def _fupan_changed_files(exec_result: dict) -> list[str]:
    files: set[str] = set()
    seen: set[int] = set()
    containers = (dict_items(exec_result.get("details"))
                  + dict_items(exec_result.get("items")))
    for entry in containers:
        if (("status" in entry or "success" in entry)
                and not fix_succeeded(entry)):
            continue
        _collect_file_refs(entry, files, seen)
    return sorted(files)
def _collect_file_refs(record, out: set[str], seen: set[int],
                       depth: int = 0) -> None:
    if not isinstance(record, dict) or depth > 4 or id(record) in seen:
        return
    seen.add(id(record))
    for key in ("file", "file_path"):
        token = _changed_file_token(record.get(key))
        if token:
            out.add(token)
    for value in ensure_list(record.get("files")):
        token = _changed_file_token(value)
        if token:
            out.add(token)
    for key in ("plan", "result", "detail"):
        nested = record.get(key)
        if isinstance(nested, dict):
            _collect_file_refs(nested, out, seen, depth + 1)
def _changed_file_token(value) -> str:
    if isinstance(value, bool):
        return ""
    if isinstance(value, str):
        return value.strip()
    if isinstance(value, int):
        return str(value)
    if isinstance(value, os.PathLike):
        return os.fsdecode(os.fspath(value))
    return ""
def _collect_raw_memory_paths(memory_context: Any) -> list:
    raw_paths = getattr(memory_context, "raw_memory_paths", None)
    if isinstance(raw_paths, (set, frozenset)):
        return sorted(
            raw_paths,
            key=lambda p: safe_str(
                os.fspath(p) if isinstance(p, os.PathLike) else p),
        )
    return list(raw_paths) if isinstance(raw_paths, (list, tuple)) else []
def _fupan_existing_memories(raw_mem_paths: list) -> list[dict]:
    return [{
        "path": (os.fsdecode(os.fspath(p))
                 if isinstance(p, os.PathLike) else p),
        "summary": "",
    } for p in raw_mem_paths if isinstance(p, (str, os.PathLike))]
def _fupan_task_success(exec_result: dict) -> bool:
    if not isinstance(exec_result, dict):
        return False
    status = str_or(exec_result.get("status")).strip().lower()
    if (status in _FUPAN_NON_SUCCESS_STATUSES
            or not as_bool(status, default=False)):
        return False
    counts = [_execution_count(exec_result.get(key))
              for key in _FUPAN_NON_SUCCESS_COUNT_KEYS]
    if any(count is None for count in counts):
        return False
    return all(count == 0 for count in counts)
def _fupan_failure_errors(exec_result: dict) -> list[str]:
    failed = _ctx_count(exec_result, "failed")
    rolled_back = _ctx_count(exec_result, "rolled_back")
    status = str_or(exec_result.get("status")).strip().lower()
    if status in TX_FAILED_STATUSES:
        failed = max(1, failed)
    detail = str_or(exec_result.get("error")).strip()
    suffix = f": {detail}" if detail else ""
    errors = [
        f"治疗执行失败 {index}/{failed}{suffix}"
        for index in range(1, failed + 1)
    ]
    errors.extend(
        f"治疗回滚 {index}/{rolled_back}{suffix}"
        for index in range(1, rolled_back + 1))
    return errors
def _fupan_task_duration(review_result: dict | None) -> int:
    duration = count_tasks(dict_or_empty(review_result).get("elapsed_s"))
    return 0 if duration is None else duration
def build_stage6a_fupan_inputs(review_result: dict | None, exec_result: dict,
                               fupan_context: dict, improvements: list,
                               *, skill_dir: str,
                               memory_context: Any = None) -> dict:
    review_view = dict_or_empty(review_result)
    exec_view = dict_or_empty(exec_result)
    ctx_view = dict_or_empty(fupan_context)
    return {
        "summary": _fupan_summary_hint(ctx_view),
        "improvements": improvements or None,
        "auto_analyze": True,
        "auto_context": {
            "user_messages": _fupan_user_messages(ctx_view),
            "tool_calls": [],
            "errors": _fupan_failure_errors(exec_view),
            "code_modified": _ctx_count(ctx_view, "tx_succeeded") > 0,
            "changed_files": _fupan_changed_files(exec_view),
            "duration": _fupan_task_duration(review_view),
            "task_success": _fupan_task_success(exec_view),
        },
        "existing_memories": _fupan_existing_memories(
            _collect_raw_memory_paths(memory_context)),
        "memory_context": memory_context,
        "skill_dir": skill_dir,
    }
def project_stage6a_fupan_report(result: dict, fupan_result: dict, *,
                                 test_bridge: Any = None) -> None:
    fupan_result = dict_or_empty(fupan_result)
    for result_key, source_key, expected in _FUPAN_REPORT_FIELDS:
        result[result_key] = as_declared(
            fupan_result.get(source_key), expected)
    attach_test_health_metrics(test_bridge, result)
def run_stage6a_fupan(ctx: Any, review_result: dict | None,
                      exec_result: dict) -> dict:
    stage_start = time.time()
    _log.info("[Stage6a] fupan_engine 开始: %s", timestamp_human())
    result = {"stage": "fupan", "timestamp": timestamp_ms(),
              "status": "running"}
    review_view = dict_or_empty(review_result)
    exec_view = dict_or_empty(exec_result)
    fupan_context = dict_or_empty(review_view.get("_review_context_for_fupan"))
    try:
        _fx_improvements = collect_stage6a_improvements(
            ctx.skill_dir, result)
        fupan_result = run_fupan(**build_stage6a_fupan_inputs(
            review_view, exec_view, fupan_context, _fx_improvements,
            skill_dir=ctx.skill_dir,
            memory_context=getattr(ctx, "memory_context", None)))
        if not isinstance(fupan_result, dict):
            raise TypeError(
                "fupan_engine 返回非 dict: "
                f"{type(fupan_result).__name__}")
        if fupan_result.get("ok") is False:
            raise RuntimeError(str(fupan_result.get("message")
                                 or "fupan_engine 返回失败(ok=False)"))
        project_stage6a_fupan_report(
            result, fupan_result, test_bridge=getattr(ctx, "test_bridge", None))
        result["status"] = "completed"
        result["elapsed_s"] = round(time.time() - stage_start, 2)
        _log.info("[Stage6a] fupan_engine完成: quality_score=%s, "
                  "memory_ops=%d, risks=%d",
                  result["fupan_quality_score"],
                  len_safe(result["memory_operations"]),
                  len_safe(result["detected_risks"]))
        result = apply_fupan_memory_enhancement(
            result, getattr(ctx, "memory_context", None))
        _record_stage6a_memory_injection(ctx, result)
    except Exception as fupan_err:
        _log.warning("[Stage6a] fupan_engine失败(不阻断): %s", fupan_err)
        result["status"] = "failed"
        result["fupan_error"] = str(fupan_err)[:200]
        result["elapsed_s"] = round(time.time() - stage_start, 2)
    ctx.stages["stage6a"] = result
    return result
def _record_stage6a_memory_injection(ctx: Any, result: dict) -> None:
    try:
        from jwsgj.diag_delivery_integrity_gate import (
            record_memory_injection,
        )
        report = record_memory_injection(
            ctx.skill_dir,
            result.get("memory_operations"),
            round_start_ts=_stage6a_round_anchor(ctx),
            source="stage6a_fupan",
            quality_score=float(result.get("fupan_quality_score") or 0.0),
        )
        result["memory_injection_receipt"] = report
    except Exception as inject_err:
        _log.warning("[Stage6a] 记忆注入回执写入失败(交付门禁将阻断): %s",
                     inject_err)
def _stage6a_round_anchor(ctx: Any) -> str:
    try:
        from jwsgj.diag_types_normalize import (
            coerce_round_anchor as _coerce,
        )
        from jwsgj.pipeline_round_trace import (
            load_pipeline_state as _load_state,
        )
        state = _load_state(ctx.skill_dir)
        return str(_coerce(str(state.get("round_start_ts") or "")) or "")
    except Exception as _anchor_exc:
        _log.debug(
            "Stage6a 轮次锚点不可用时退化返回空锚"
            "（回执落空锚，交付门禁按「轮次锚缺失」保守阻断）: %s",
            _anchor_exc)
        return ""
def build_stage5_fupan_context(diag_result: dict, exec_result: dict,
                               cv_findings: int, cv_rules: int,
                               retro_score: float) -> dict:
    return {
        "diag_methods": _ctx_count(
            diag_result, FIELD_METHODS_EXECUTED),
        "diag_passed": _ctx_count(diag_result, "methods_passed"),
        "cv_findings": _count_value(cv_findings),
        "cv_rules": _count_value(cv_rules),
        "tx_executed": _ctx_count(exec_result, "executed"),
        "tx_succeeded": treatment_counts(exec_result)["fixed"],
        "tx_rolled_back": _ctx_count(exec_result, "rolled_back"),
        "tx_failed": _ctx_count(exec_result, "failed"),
        "retro_score": _score_value(retro_score),
    }
def _quick_analyze_empty() -> dict[str, Any]:
    return {"summary": "", "risks": [], "improvements": [],
            "memory_candidates": [], "pattern_matches": [],
            "complexity_score": 0, "extraction_confidence": 0.0}
def quick_analyze(
    user_messages: list[str] | None = None,
    tool_calls: list[dict[str, Any]] | None = None,
    errors: list[str] | None = None,
    **kwargs: Any,
) -> dict[str, Any]:
    try:
        analysis = analyze_session(
            user_messages=user_messages, tool_calls=tool_calls,
            errors=errors,
            enable_reflexion=kwargs.pop("enable_reflexion", False),
            enable_root_cause=kwargs.pop("enable_root_cause", False),
            enable_pattern_match=kwargs.pop("enable_pattern_match", False),
            **kwargs)
        params = to_fupan_params(analysis)
        params["pattern_matches"] = analysis.pattern_matches
        params["complexity_score"] = analysis.complexity_score
        params["extraction_confidence"] = analysis.extraction_confidence
        return {"ok": True, **params}
    except Exception as e:
        _log.warning("[fupan] quick_analyze 分析降级: %s", e)
        return {"ok": False, "error": safe_str(e)[:100],
                **_quick_analyze_empty()}
def _memory_ops_view(fupan_result: Any) -> tuple[list, str]:
    if not isinstance(fupan_result, dict):
        return [], f"复盘结果非字典: {type(fupan_result).__name__}"
    ops = fupan_result.get("memory_operations", [])
    if not isinstance(ops, list):
        return [], "memory_operations 非列表"
    if fupan_result.get("ok") is False:
        return ops, safe_str(
            fupan_result.get("message") or "复盘结果标记为失败")
    return ops, ""
def verify_fupan_writes(fupan_result: dict[str, Any]) -> dict[str, Any]:
    ops, extraction_error = _memory_ops_view(fupan_result)
    if extraction_error:
        return {"ok": False, "total": len(ops), "valid": 0,
                "invalid": [{"index": -1, "path": "",
                             "reason": extraction_error}]}
    invalid: list[dict[str, Any]] = []
    for idx, op in enumerate(ops):
        issue = memory_operation_issue(op, idx)
        if issue:
            issue["path"] = text_or_empty(issue.get("path"))
            invalid.append(issue)
    return {"ok": not invalid, "total": len(ops),
            "valid": len(ops) - len(invalid), "invalid": invalid}
def _expected_op_paths(ops: list) -> list[str]:
    paths: list[str] = []
    for op in ops:
        if not isinstance(op, dict):
            continue
        if not _is_write_action(op.get("action")):
            continue
        path = op.get("path")
        if isinstance(path, str) and path.strip():
            paths.append(path)
    return list(dict.fromkeys(paths))
def _written_path_set(written_paths: list[str] | None) -> set[str]:
    return {p for p in coerce_text_list(written_paths) if p}
def _chain_gaps(
    expected: list[str], written: set[str],
) -> tuple[list[str], list[str]]:
    missing = [p for p in expected if p not in written]
    unrelated = sorted(p for p in written if p not in expected)
    return missing, unrelated
def verify_consumption_chain(
    fupan_result: dict[str, Any],
    written_paths: list[str] | None = None,
) -> dict[str, Any]:
    ops, extraction_error = _memory_ops_view(fupan_result)
    write_check = verify_fupan_writes(fupan_result)
    expected_paths = _expected_op_paths(ops)
    written = _written_path_set(written_paths)
    missing, unrelated = _chain_gaps(expected_paths, written)
    result = {
        "ok": write_check["ok"] and not missing,
        "expected": len(expected_paths),
        "written": len(expected_paths) - len(missing),
        "missing": missing,
        "unrelated": unrelated,
    }
    if extraction_error:
        result["error"] = extraction_error
    return result

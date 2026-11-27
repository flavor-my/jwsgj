from __future__ import annotations

import ast
import hashlib
import io
import logging
import math
import os
import re
import threading
import tokenize
from collections.abc import Iterable
from copy import copy as _shallow_copy
from copy import deepcopy
from dataclasses import dataclass, field, fields, replace
from enum import Enum
from typing import Any, ClassVar

from jwsgj.diag_shared_ast_nodes import (
    ASTPreciseParser,
    build_parent_map,
    is_static_literal_expr,
    parse_ast_safely,
)
from jwsgj.diag_shared_ast_views import (
    register_cache_release,
    tree_nodes,
    tree_unparse_cache,
    unparse_cached,
)
from jwsgj.diag_shared_source_core import join_source_lines
from jwsgj.diag_taint_interproc import CrossModuleTaintTracker, clear_taint_scope_memos
from jwsgj.diag_taint_model import BUILTIN_SOURCES
from jwsgj.diag_taint_scanners import PreciseVulnDetector as _PreciseVulnDetector
from jwsgj.diag_taint_scanners import release_scanner_caches as _release_scanner_caches
from jwsgj.diag_taint_symbolic import SeedGenerator, SymbolicExecutor
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    ExecutionPath,
    TaintTrace,
    VulnerabilityFinding,
    finding_scan_exempt,
)
from jwsgj.diag_types_vocab import (
    TAINT_LOCAL_TRUSTED_CATEGORIES,
    TAINT_SOURCE_CATEGORY_BY_NAME,
    VULN_RENDER_TEMPLATE_STRING,
    VulnerabilityCategory,
    normalize_filepath,
)
from jwsgj.log_config import write_module_run

_log = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
def _str_field(finding: dict, key: str) -> str:
    value = finding.get(key)
    return value if isinstance(value, str) else ""
def _category_label(category: Any) -> str:
    value = getattr(category, "value", None)
    return value if isinstance(value, str) else str(category)
def _confidence_multiplier(finding: _Finding) -> float:
    confidence = getattr(finding, "confidence", None)
    if isinstance(confidence, bool) or not isinstance(confidence, (int, float)):
        return 1.0
    try:
        value = float(confidence)
    except (OverflowError, ValueError):  # jwsgj:silent-ok 不可表示即视为非有限值
        return 0.0
    return value if math.isfinite(value) else 0.0
def _source_category_of(name: str) -> str:
    if not name:
        return ""
    category = TAINT_SOURCE_CATEGORY_BY_NAME.get(name, "")
    if category:
        return category
    return next((src.category for src in BUILTIN_SOURCES if src.name == name), "")
def _taint_origin_fields(finding: dict) -> tuple[str, str]:
    src_cat = _str_field(finding, "source_category")
    src_name = _str_field(finding, "source_name")
    if not src_cat and src_name:
        src_cat = _source_category_of(src_name)
    return src_cat, src_name
def taint_traversal_exemption(finding: dict) -> bool | None:
    if not isinstance(finding, dict):
        return None
    if finding.get("trusted_origin") is True:
        return True
    src_cat, src_name = _taint_origin_fields(finding)
    if not (src_cat or src_name):
        return None
    return src_cat in TAINT_LOCAL_TRUSTED_CATEGORIES
__all__ = [
    'CustomRuleRegistry',
    'CustomSecurityRule',
    'DiagOptions',
    'EnhancedSecurityDiagnoser',
    'ExploitPathReport',
    'ExploitReportGenerator',
    'FrameworkAwareAnalyzer',
    'FrameworkContext',
    'FrameworkType',
    'check_SE38',
    'check_SE39',
    'check_SE40',
    'clear_security_scan_cache',
    'get_diagnoser',
    'release_diagnoser_caches',
    'run_enhanced_security_scan',
    'security_scan_cache_key',
    'security_scan_cache_lookup',
    'security_scan_cache_store',
    'taint_traversal_exemption',
    'wiring_declarations',
]
_Category = VulnerabilityCategory
_Finding = VulnerabilityFinding
_log.info("diag_security_diagnoser 已加载: %d 项导出", len(__all__))
_FRAMEWORK_CTX_CACHE: dict[str, tuple[ast.Module | None, FrameworkContext]] = {}
_FRAMEWORK_CTX_CACHE_LOCK = threading.Lock()
_FRAMEWORK_CTX_CACHE_CAP = 512
_RESULT_CACHE_MAX = 256
_DIAG_RESULT_CACHE: dict[str, tuple[str, dict]] = {}
_DIAG_RESULT_LOCK = threading.Lock()
def _cache_put(cache: dict, key: Any, value: Any, max_size: int) -> None:
    if len(cache) >= max_size:
        cache.clear()
    cache[key] = value
_EXTRA_RESULT_DEFAULTS: dict[str, Any] = {
    "cfg_blocks": {},
    "du_chains": {},
    "taint_traces": [],
    "symbolic_paths": [],
    "custom_findings": [],
    "knowledge_findings": [],
    "exploit_reports": [],
}
_EXTRA_RESULT_KEYS: tuple[str, ...] = tuple(_EXTRA_RESULT_DEFAULTS)
_CACHE_SERVE_FULL = "full"
_CACHE_SERVE_SUBSET = "subset"
def _empty_extras() -> dict:
    return {key: (dict(value) if isinstance(value, dict) else list(value))
            for key, value in _EXTRA_RESULT_DEFAULTS.items()}
def _diag_tree_text(tree: Any) -> str:
    return (ast.dump(tree, include_attributes=True)
            if isinstance(tree, ast.Module) else "")
def _diag_cache_key(code: str, custom_rules: list[_Rule],
                    knowledge_rules: list[dict], tree: Any = None) -> str:
    semantic_state = repr((custom_rules, knowledge_rules))
    tree_text = _diag_tree_text(tree)
    payload = (f"{len(code)}:{code}{len(semantic_state)}:{semantic_state}"
               f"{len(tree_text)}:{tree_text}")
    return hashlib.sha1(
        payload.encode("utf-8", "surrogatepass"),
        usedforsecurity=False).hexdigest()
def _diag_source_digest(code: str) -> str:
    _norm = code.replace("\r\n", "\n").replace("\r", "\n").rstrip("\n")
    return hashlib.sha256(
        _norm.encode("utf-8", "surrogatepass")).hexdigest()
def _retarget_finding_file(finding: Any, filepath: str) -> Any:
    if isinstance(finding, _Finding):
        return finding if finding.file == filepath else replace(
            finding, file=filepath)
    if isinstance(finding, dict):
        return (finding if finding.get("file") == filepath
                else {**finding, "file": filepath})
    return finding
def _subset_diag_result(full: dict, filepath: str | None = None) -> dict:
    _raw_findings = full.get("findings")
    findings = deepcopy(list(_raw_findings)
                        if isinstance(_raw_findings, (list, tuple)) else [])
    if filepath is not None:
        findings = [_retarget_finding_file(f, filepath) for f in findings]
    result = {
        "ok": full.get("ok", True),
        "framework": full.get("framework", "unknown"),
        "findings": findings,
    }
    result.update(_empty_extras())
    return result
def _check_result_cache(ckey: str | None, filepath: str, full_req: bool) -> dict | None:
    if ckey is None:
        return None
    with _DIAG_RESULT_LOCK:
        hit = _DIAG_RESULT_CACHE.get(ckey)
    if hit is None:
        return None
    stored_path, stored = hit
    if full_req:
        return deepcopy(stored) if stored_path == filepath else None
    return _subset_diag_result(stored, filepath=filepath)
def _store_result_cache(ckey: str | None, filepath: str, full_req: bool, result: dict) -> None:
    if not full_req or ckey is None:
        return
    with _DIAG_RESULT_LOCK:
        existing = _DIAG_RESULT_CACHE.get(ckey)
        if existing is None or existing[0] == filepath:
            _cache_put(_DIAG_RESULT_CACHE, ckey,
                       (filepath, deepcopy(result)), _RESULT_CACHE_MAX)
@dataclass(frozen=True)
class DiagOptions:
    enable_symbolic: bool = True
    enable_vuln_scan: bool = True
    enable_cfg_du: bool = True
    include_extras: bool = True
_DEFAULT_DIAG_OPTIONS = DiagOptions()
_DIAG_OPTION_FLAGS: tuple[str, ...] = tuple(
    option_field.name for option_field in fields(DiagOptions))
def _coerce_diag_options(options: Any) -> DiagOptions:
    if isinstance(options, DiagOptions):
        return options
    if isinstance(options, dict):
        return DiagOptions(**{
            name: (options[name] if isinstance(options.get(name), bool)
                   else getattr(_DEFAULT_DIAG_OPTIONS, name))
            for name in _DIAG_OPTION_FLAGS
        })
    return _DEFAULT_DIAG_OPTIONS
class FrameworkType(Enum):
    DJANGO = "django"
    FLASK = "flask"
    FASTAPI = "fastapi"
    UNKNOWN = "unknown"
@dataclass
class FrameworkContext:
    framework: FrameworkType
    auto_escape: bool = True
    orm_parameterized: bool = True
    csrf_enabled: bool = True
    pydantic_validation: bool = False
    risk_modifiers: dict[str, float] = field(default_factory=dict)
class FrameworkAwareAnalyzer:
    DJANGO_IMPORTS: ClassVar[set[str]] = {'django', 'django.http',
        'django.db', 'django.views'}
    FLASK_IMPORTS: ClassVar[set[str]] = {'flask', 'flask.request',
        'flask.render_template'}
    FASTAPI_IMPORTS: ClassVar[set[str]] = {'fastapi', 'fastapi.params'}
    DJANGO_HIGH_RISK: ClassVar[dict[str, float]] = {
        'raw': 2.0, 'mark_safe': 2.0, 'safe': 1.5, 'extra': 1.5}
    FLASK_HIGH_RISK: ClassVar[dict[str, float]] = {
        VULN_RENDER_TEMPLATE_STRING: 2.0, 'Markup': 2.0,
        'make_response': 1.2}
    FASTAPI_HIGH_RISK: ClassVar[dict[str, float]] = {
        'WebSocket': 1.5, 'Depends': 0.5}
    @staticmethod
    def _collect_imports(tree: ast.Module) -> set[str]:
        imports: set[str] = set()
        for node in tree_nodes(tree):
            if isinstance(node, ast.Import):
                names = (alias.name for alias in node.names)
            elif (isinstance(node, ast.ImportFrom) and node.module
                  and not node.level):
                names = (node.module,)
            else:
                continue
            for name in names:
                imports.update((name, name.split('.')[0]))
        return imports
    def detect(self, tree: ast.Module, *,
               source_key: str = "") -> FrameworkContext:
        _ck = f"src:{source_key}" if source_key else f"tree:{id(tree)}"
        with _FRAMEWORK_CTX_CACHE_LOCK:
            _hit = _FRAMEWORK_CTX_CACHE.get(_ck)
            if _hit is not None and (_hit[0] is tree or source_key):
                return deepcopy(_hit[1])
        imports = self._collect_imports(tree)
        if imports & self.DJANGO_IMPORTS:
            ctx = FrameworkContext(
                framework=FrameworkType.DJANGO,
                risk_modifiers=dict(self.DJANGO_HIGH_RISK))
        elif imports & self.FASTAPI_IMPORTS:
            ctx = FrameworkContext(
                framework=FrameworkType.FASTAPI, pydantic_validation=True,
                risk_modifiers=dict(self.FASTAPI_HIGH_RISK))
        elif imports & self.FLASK_IMPORTS:
            ctx = FrameworkContext(
                framework=FrameworkType.FLASK,
                auto_escape=True, orm_parameterized=False,
                risk_modifiers=dict(self.FLASK_HIGH_RISK),
            )
        else:
            ctx = FrameworkContext(framework=FrameworkType.UNKNOWN)
        write_module_run("diag_security_diagnoser", "detect", "ok",
                         framework=ctx.framework.value)
        with _FRAMEWORK_CTX_CACHE_LOCK:
            if len(_FRAMEWORK_CTX_CACHE) >= _FRAMEWORK_CTX_CACHE_CAP:
                _FRAMEWORK_CTX_CACHE.clear()
            _FRAMEWORK_CTX_CACHE[_ck] = (None if source_key else tree, ctx)
        return deepcopy(ctx)
    @staticmethod
    def _risk_modifier_for(sink: Any, modifiers: dict) -> float:
        if not isinstance(sink, str) or not sink:
            return 1.0
        if sink in modifiers:
            return modifiers[sink]
        return modifiers.get(sink.rsplit('.', 1)[-1], 1.0)
    def adjust_risk(self, finding: _Finding, context: FrameworkContext) -> _Finding:
        confidence = _confidence_multiplier(finding)
        suggestion = (finding.suggestion
                      if isinstance(finding.suggestion, str) else "")
        modifier = self._risk_modifier_for(finding.sink, context.risk_modifiers)
        if modifier > 1.5:
            if confidence > 0:
                finding.severity = "CRITICAL"
                finding.confidence = min(1.0, confidence * modifier)
                finding.suggestion = suggestion + (
                    f" [{context.framework.value} 框架: 此调用绕过内置防护]"
                )
        elif modifier > 1.0:
            finding.confidence = min(1.0, confidence * modifier)
            finding.suggestion = suggestion + (
                f" [{context.framework.value} 框架: 此调用弱化内置防护]"
            )
        elif modifier < 1.0:
            finding.confidence = confidence * modifier
            finding.suggestion = suggestion + (
                f" [{context.framework.value} 框架: 内置防护可能降低风险]"
            )
        return finding
@dataclass
class ExploitPathReport:
    vulnerability: _Finding
    source_info: dict = field(default_factory=dict)
    propagation_steps: list[dict] = field(default_factory=list)
    sink_info: dict = field(default_factory=dict)
    trigger_input: dict[str, Any] = field(default_factory=dict)
    fix_suggestion: str = ""
    severity_score: float = 0.0
class ExploitReportGenerator:
    _SEVERITY_BASE_SCORES: ClassVar[dict[str, float]] = {
        "CRITICAL": 9.0, "HIGH": 7.0, "MEDIUM": 5.0,
        "LOW": 3.0, "INFO": 1.0}
    def generate(self, finding: _Finding,
                 taint_trace: TaintTrace | None = None,
                 exec_paths: list[ExecutionPath] | None = None) -> ExploitPathReport:
        report = ExploitPathReport(
            vulnerability=finding,
            source_info={
                "type": finding.source,
                "file": finding.file,
                "line": finding.line,
            },
            propagation_steps=[],
            sink_info={
                "function": finding.sink,
                "file": finding.file,
                "line": finding.line,
            },
            fix_suggestion=finding.suggestion,
            severity_score=self._calculate_severity(finding),
        )
        if taint_trace is not None:
            report.source_info.update({
                "type": taint_trace.source_expr or finding.source,
                "file": taint_trace.source_file or finding.file,
                "line": taint_trace.source_line or finding.line,
            })
            report.sink_info.update({
                "function": taint_trace.sink_expr or finding.sink,
                "file": taint_trace.sink_file or finding.file,
                "line": taint_trace.sink_line or finding.line,
            })
            self._append_taint_steps(report, taint_trace)
        if exec_paths:
            self._append_symbolic_step(report, exec_paths)
        write_module_run("diag_security_diagnoser", "generate", "ok",
                         severity=report.vulnerability.severity,
                         propagation_steps=len(report.propagation_steps))
        return report
    @staticmethod
    def _append_taint_steps(report: ExploitPathReport, taint_trace: TaintTrace) -> None:
        for step in taint_trace.propagation_chain:
            report.propagation_steps.append({
                "step": len(report.propagation_steps) + 1,
                "type": step.get("type", "unknown"),
                "variable": step.get("from_var", ""),
                "function": step.get("to_func", ""),
                "file": step.get("file", ""),
                "line": step.get("line", 0),
            })
    @staticmethod
    def _append_symbolic_step(report: ExploitPathReport, exec_paths: list[ExecutionPath]) -> None:
        exploitable = [p for p in exec_paths if p.reaches_sink and p.is_feasible]
        if not exploitable:
            return
        path = exploitable[0]
        report.trigger_input = dict(path.trigger_input)
        report.propagation_steps.append({
            "step": len(report.propagation_steps) + 1,
            "type": "symbolic_path",
            "constraints": list(path.constraints),
            "trigger": dict(path.trigger_input),
        })
    def _calculate_severity(self, finding: _Finding) -> float:
        score = self._SEVERITY_BASE_SCORES.get(finding.severity, 5.0)
        score *= _confidence_multiplier(finding)
        return round(max(0.0, min(10.0, score)), 1)
    def format_report(self, report: ExploitPathReport) -> str:
        lines = [
            "=" * 60,
            "漏洞利用路径报告",
            "=" * 60,
            (f"严重性: {report.vulnerability.severity} "
             f"(评分: {report.severity_score}/10.0)"),
            f"CWE: {report.vulnerability.cwe_id}",
            f"类型: {_category_label(report.vulnerability.category)}",
            "",
            f"[Source] {report.source_info.get('type')}",
            f"  文件: {report.source_info.get('file')}",
            f"  行号: {report.source_info.get('line')}",
            "",
            "[传播链]",
        ]
        for step in report.propagation_steps:
            lines.append(
                f"  Step {step.get('step', '?')}: {step.get('type', '?')} "
                f"→ {step.get('function', '')} "
                f"(行 {step.get('line', '?')})"
            )
        lines.extend([
            "",
            f"[Sink] {report.sink_info.get('function')}",
            f"  文件: {report.sink_info.get('file')}",
            f"  行号: {report.sink_info.get('line')}",
            "",
        ])
        if report.trigger_input:
            lines.append(f"[触发输入] {report.trigger_input}")
            lines.append("")
        lines.extend([
            f"[修复建议] {report.fix_suggestion}",
            "=" * 60,
        ])
        return '\n'.join(lines)
@dataclass
class CustomSecurityRule:
    rule_id: str
    name: str
    description: str
    severity: str
    sources: list[str] = field(default_factory=list)
    sinks: list[str] = field(default_factory=list)
    sanitizers: list[str] = field(default_factory=list)
    cwe_id: str = ""
    enabled: bool = True
_Rule = CustomSecurityRule
def _builtin_rules() -> list[_Rule]:
    specs = (
        ("CUSTOM-001", "Hardcoded JWT Secret", "检测硬编码的 JWT 密钥",
         "HIGH", ["JWT_SECRET", "SECRET_KEY", "jwt_secret"], [], [], "CWE-798"),
        ("CUSTOM-002", "Insecure Random", "检测使用不安全的随机数生成器",
         "MEDIUM", [], ["random.random", "random.randint"],
         ["secrets.token_bytes", "os.urandom"], "CWE-330"),
        ("CUSTOM-003", "Debug Mode Enabled", "检测生产环境开启 DEBUG 模式",
         "HIGH", [], ["DEBUG = True", "DEBUG=True"], [], "CWE-489"),
        ("CUSTOM-004", "Insecure SSL", "检测不安全的 SSL 配置（verify=False）",
         "MEDIUM", [], ["verify=False", "verify = False"], [], "CWE-295"),
    )
    return [_Rule(*spec) for spec in specs]
def _release_cache_slots(owner: Any, slots: Iterable[str]) -> int:
    released = 0
    for slot in slots:
        if getattr(owner, slot, None) is not None:
            setattr(owner, slot, None)
            released += 1
    return released
def _rule_pattern(pattern: str) -> re.Pattern:
    left = r"(?<!\w)" if pattern[0].isalnum() or pattern[0] == "_" else ""
    right = r"(?!\w)" if pattern[-1].isalnum() or pattern[-1] == "_" else ""
    return re.compile(left + re.escape(pattern) + right)
class CustomRuleRegistry:
    _RULE_CATEGORY_MAP: ClassVar[dict] = {
        "CUSTOM-001": _Category.HARDCODED_SECRET,
        "CUSTOM-002": _Category.WEAK_CRYPTO,
        "CUSTOM-003": _Category.INSECURE_CONFIG,
        "CUSTOM-004": _Category.WEAK_CRYPTO,
    }
    _TREE_CACHE_SLOTS: ClassVar[tuple[str, ...]] = (
        "_node_srcs_cache",
        "_parent_map_cache",
    )
    def __init__(self) -> None:
        self._node_srcs_cache: tuple[ast.Module, list] | None = None
        self._parent_map_cache: tuple[ast.Module, dict] | None = None
        self._rules: dict[str, _Rule] = {}
        self._load_builtin_rules()
    def node_sources(self, tree: ast.Module) -> list[tuple[ast.AST, str]]:
        cached = self._node_srcs_cache
        if cached is None or cached[0] is not tree:
            up_cache = tree_unparse_cache(tree)
            cached = (tree, [
                (node, unparse_cached(tree, node, up_cache))
                for node in tree_nodes(tree)
                if isinstance(node, (ast.Assign, ast.AnnAssign, ast.Call))
            ])
            self._node_srcs_cache = cached
        return cached[1]
    def _parent_map(self, tree: ast.Module) -> dict[int, ast.AST]:
        cached = self._parent_map_cache
        if cached is None or cached[0] is not tree:
            cached = (tree, build_parent_map(tree))
            self._parent_map_cache = cached
        return cached[1]
    def release_tree_caches(self) -> int:
        return _release_cache_slots(self, self._TREE_CACHE_SLOTS)
    @staticmethod
    def _drop_subsumed_hits(matched: list[tuple[ast.AST, str]],
                            parent_map: dict[int, ast.AST]
                            ) -> list[tuple[ast.AST, str]]:
        if len(matched) < 2:
            return matched
        return [(node, sink) for node, sink in matched
                if not CustomRuleRegistry._has_descendant_hit(
                    node, sink, matched, parent_map)]
    @staticmethod
    def _has_descendant_hit(node: ast.AST, sink: str,
                            matched: list[tuple[ast.AST, str]],
                            parent_map: dict[int, ast.AST]) -> bool:
        return any(
            other is not node and other_sink == sink
            and CustomRuleRegistry._is_ancestor(node, other, parent_map)
            for other, other_sink in matched)
    @staticmethod
    def _is_ancestor(anc: ast.AST, desc: ast.AST, parent_map: dict[int, ast.AST]) -> bool:
        cur = parent_map.get(id(desc))
        while cur is not None:
            if cur is anc:
                return True
            cur = parent_map.get(id(cur))
        return False
    def _load_builtin_rules(self) -> None:
        for rule in _builtin_rules():
            self._rules[rule.rule_id] = rule
    def register(self, rule: _Rule) -> bool:
        if not isinstance(rule, _Rule):
            _log.warning("[Security] register 拒绝非规则对象: %r", rule)
            return False
        self._rules[rule.rule_id] = rule
        return True
    def get_all(self) -> list[_Rule]:
        return list(self._rules.values())
    def get_enabled(self) -> list[_Rule]:
        return [r for r in self._rules.values() if r.enabled]
    def unregister(self, rule_id: str) -> bool:
        return self._rules.pop(rule_id, None) is not None
    def apply_rules(self, code: str, filepath: str = _DEFAULT_FILEPATH,
                    tree: ast.Module | None = None) -> list[_Finding]:
        findings = []
        if not isinstance(code, str):
            _log.warning("[Security] 非字符串源码输入,跳过规则匹配")
            write_module_run("diag_security_diagnoser", "apply_rules",
                             "degraded", reason="non_str_source")
            return findings
        if tree is None:
            tree = ASTPreciseParser.parse(code, filepath)
        emitted: set[tuple[str, int, str]] = set()
        code_only = _code_only_text(code) if tree is None else ""
        for rule in self.get_enabled():
            if not (rule.sinks or rule.sources):
                continue
            if tree is not None:
                findings.extend(self._apply_rule_ast_channel(
                    rule, tree, filepath, emitted))
            else:
                findings.extend(self._emit_findings(
                    rule, filepath, self._text_hits(rule, code_only), emitted))
        write_module_run("diag_security_diagnoser", "apply_rules", "ok",
                         findings=len(findings))
        return findings
    @staticmethod
    def _make_finding(rule: _Rule, rule_category: _Category, filepath: str, line: int, sink: str) -> _Finding:
        return _Finding(
            category=rule_category,
            severity=rule.severity,
            file=filepath,
            line=line,
            source=rule.name,
            sink=sink,
            suggestion=rule.description,
            cwe_id=rule.cwe_id,
        )
    def _apply_rule_ast_channel(self, rule: _Rule,
                                tree: ast.Module, filepath: str,
                                emitted: set) -> list[_Finding]:
        matched = self._collect_pattern_hits(rule, tree)
        kept = (self._drop_subsumed_hits(matched, self._parent_map(tree))
                if len(matched) > 1 else matched)
        return self._emit_findings(
            rule, filepath, ((node.lineno, sink) for node, sink in kept), emitted)
    def _emit_findings(self, rule: _Rule, filepath: str,
                       hits: Iterable[tuple[int, str]],
                       emitted: set) -> list[_Finding]:
        rule_category = self._RULE_CATEGORY_MAP.get(
            rule.rule_id, _Category.INSECURE_CONFIG)
        out: list[_Finding] = []
        for line, sink in hits:
            key = (rule.rule_id, line, sink)
            if key in emitted:
                continue
            emitted.add(key)
            out.append(self._make_finding(
                rule, rule_category, filepath, line, sink))
        return out
    def _collect_pattern_hits(self, rule: _Rule, tree: ast.Module) -> list[tuple[ast.AST, str]]:
        sink_patterns = [p for p in rule.sinks if isinstance(p, str) and p]
        source_patterns = [p for p in rule.sources if isinstance(p, str) and p]
        static_patterns = sink_patterns + source_patterns
        up_cache = tree_unparse_cache(tree)
        matched: list[tuple[ast.AST, str]] = []
        for node, src in self.node_sources(tree):
            static = (isinstance(node, (ast.Assign, ast.AnnAssign))
                      and node.value is not None
                      and is_static_literal_expr(node.value))
            if static and isinstance(node.value, ast.Constant):
                literal = node.value.value
                static = not (
                    literal is None
                    or (isinstance(literal, (str, bytes)) and not literal)
                )
            texts = [src]
            if isinstance(node, ast.AnnAssign) and node.value is not None:
                texts.append(f"{unparse_cached(tree, node.target, up_cache)}"
                             f" = {unparse_cached(tree, node.value, up_cache)}")
            texts = [_STR_LITERAL_RE.sub("''", text) for text in texts]
            patterns = static_patterns if static else sink_patterns
            for sink in patterns:
                matcher = _rule_pattern(sink)
                if any(matcher.search(text) for text in texts):
                    matched.append((node, sink))
        return matched
    @staticmethod
    def _text_hits(rule: _Rule, code_only: str) -> list[tuple[int, str]]:
        return [(line, sink)
                for sink in [p for p in (*rule.sinks, *rule.sources)
                             if isinstance(p, str) and p]
                for line in CustomRuleRegistry._find_lines(code_only, sink)]
    @staticmethod
    def _find_lines(code: str, pattern: str) -> list[int]:
        matcher = _rule_pattern(pattern)
        if '\n' not in pattern:
            return [i for i, line in enumerate(code.split('\n'), 1)
                    if matcher.search(line)]
        return [code.count('\n', 0, match.start()) + 1
                for match in matcher.finditer(code)]
_STR_LITERAL_RE = re.compile(r"'(?:[^'\\]|\\.)*'|\"(?:[^\"\\]|\\.)*\"")
_FSTRING_TEXT_TOKENS = frozenset(
    getattr(tokenize, name) for name in
    ("FSTRING_START", "FSTRING_MIDDLE", "FSTRING_END")
    if hasattr(tokenize, name))
def _code_only_text(code: str) -> str:
    masked = [char if char in "\r\n" else " " for char in code]
    offsets = [0]
    for line in io.StringIO(code).readlines():
        offsets.append(offsets[-1] + len(line))
    ignored = {tokenize.COMMENT, tokenize.STRING} | _FSTRING_TEXT_TOKENS
    try:
        tokens = tokenize.generate_tokens(io.StringIO(code).readline)
        for token in tokens:
            if token.type in ignored or not token.string:
                continue
            start = offsets[token.start[0] - 1] + token.start[1]
            end = offsets[token.end[0] - 1] + token.end[1]
            masked[start:end] = code[start:end]
    except (tokenize.TokenError, SyntaxError) as exc:
        _log.debug("[Security] 文本扫描词法重建提前结束: %s", exc)
    return "".join(masked)
class EnhancedSecurityDiagnoser:
    def __init__(self) -> None:
        self.vuln_detector = _PreciseVulnDetector()
        self.taint_tracker = CrossModuleTaintTracker()
        self.framework_analyzer = FrameworkAwareAnalyzer()
        self.symbolic_executor = SymbolicExecutor()
        self.concolic_seeds = SeedGenerator.from_symbolic_executor(
            self.symbolic_executor)
        self.custom_rules = CustomRuleRegistry()
        self.knowledge = self.vuln_detector.knowledge
        self.report_generator = ExploitReportGenerator()
    def diag(self, code: str, filepath: str = _DEFAULT_FILEPATH,
             tree: ast.Module | None = None,
             options: DiagOptions | None = None) -> dict:
        opts = _coerce_diag_options(options)
        filepath = normalize_filepath(filepath)
        if not isinstance(code, str):
            _log.warning("[Security] diag 非字符串源码输入: %s",
                         filepath or "<code>")
            write_module_run("diag_security_diagnoser", "diag", "degraded",
                             reason="non_str_source")
            return {"ok": False, "error": "非字符串源码"}
        _serve = self._cache_service_mode(opts)
        _full_req = _serve == _CACHE_SERVE_FULL
        knowledge_rules = (
            self._load_knowledge_rules()
            if _serve is not None else None)
        _ckey = (_diag_cache_key(
            code, self.custom_rules.get_all(), knowledge_rules or [], tree=tree)
            if _serve is not None else None)
        _early = _check_result_cache(_ckey, filepath, _full_req)
        if _early is not None:
            if _full_req:
                _early = self._refresh_cached_taint(
                    _early, tree, code, filepath, opts)
                _store_result_cache(_ckey, filepath, True, _early)
            return _early
        tree = self._parse_tree(code, filepath, tree)
        if tree is None:
            return {"ok": False, "error": "语法错误"}
        result = self._diagnose_tree(
            tree, code, filepath, opts, knowledge_rules=knowledge_rules)
        _store_result_cache(_ckey, filepath, _full_req, result)
        return result
    @staticmethod
    def _is_full_request(opts: DiagOptions) -> bool:
        return (opts.enable_vuln_scan and opts.include_extras
                and opts.enable_symbolic and opts.enable_cfg_du)
    @staticmethod
    def _cache_service_mode(opts: DiagOptions) -> str | None:
        if EnhancedSecurityDiagnoser._is_full_request(opts):
            return _CACHE_SERVE_FULL
        if opts.enable_vuln_scan and not opts.include_extras:
            return _CACHE_SERVE_SUBSET
        return None
    @staticmethod
    def _parse_tree(code: str, filepath: str, tree: ast.Module | None) -> ast.Module | None:
        if tree is not None:
            return tree
        parsed = ASTPreciseParser.parse(code, filepath)
        if parsed is None:
            _log.warning("[Security] diag 语法错误早退: %s",
                         filepath or "<code>")
        return parsed
    def _refresh_cached_taint(self, result: dict, tree: ast.Module | None,
                              code: str, filepath: str,
                              opts: DiagOptions) -> dict:
        traces = self._collect_taint_traces(filepath, code, tree, opts)
        result["taint_traces"] = traces
        trace_by_sink = self._index_traces_by_sink(traces, filepath)
        result["exploit_reports"] = self._build_exploit_reports(
            result.get("findings") or [], trace_by_sink,
            result.get("symbolic_paths") or [], opts)
        return result

    def _diagnose_tree(self, tree: ast.Module, code: str, filepath: str,
                       opts: DiagOptions,
                       knowledge_rules: list[dict] | None) -> dict:
        findings, framework_ctx = self._scan_findings(tree, code, filepath, opts)
        taint_traces = self._collect_taint_traces(filepath, code, tree, opts)
        trace_by_sink = self._index_traces_by_sink(taint_traces, filepath)
        cfg_results, du_results = self._build_cfg_du_maps(tree, opts)
        symbolic_paths = self._collect_symbolic_paths(tree, opts)
        custom_findings, knowledge_findings = self._collect_custom_findings(
            code, filepath, tree, opts, knowledge_rules=knowledge_rules)
        reports = self._build_exploit_reports(
            findings, trace_by_sink, symbolic_paths, opts)
        result = {
            "ok": True,
            "framework": framework_ctx.framework.value,
            "findings": findings,
        }
        extras = {
            "cfg_blocks": cfg_results,
            "du_chains": du_results,
            "taint_traces": taint_traces,
            "symbolic_paths": symbolic_paths,
            "custom_findings": custom_findings,
            "knowledge_findings": knowledge_findings,
            "exploit_reports": reports,
        }
        result.update({key: extras[key] for key in _EXTRA_RESULT_KEYS})
        return result
    def _scan_findings(self, tree: ast.Module, code: str, filepath: str,
                       opts: DiagOptions) -> tuple[list, Any]:
        findings = (self.vuln_detector.scan(tree, code, filepath)
                    if opts.enable_vuln_scan else [])
        framework_ctx = self.framework_analyzer.detect(
            tree, source_key=_diag_source_digest(code))
        findings = [self.framework_analyzer.adjust_risk(f, framework_ctx)
                    for f in findings]
        return findings, framework_ctx
    def _collect_taint_traces(self, filepath: str, code: str, tree: ast.Module, opts: DiagOptions) -> list:
        if not opts.include_extras:
            return []
        return self.taint_tracker.track_file(filepath, code, tree=tree)
    def _collect_symbolic_paths(self, tree: ast.Module, opts: DiagOptions) -> list:
        if not (opts.enable_symbolic and opts.include_extras):
            return []
        return self._run_symbolic_pass(tree)
    def _collect_custom_findings(self, code: str, filepath: str,
                                 tree: ast.Module, opts: DiagOptions,
                                 knowledge_rules: list[dict] | None
                                 ) -> tuple[list, list]:
        if not opts.include_extras:
            return [], []
        custom = self.custom_rules.apply_rules(code, filepath, tree=tree)
        knowledge = self._apply_knowledge_patterns(
            code, filepath, tree=tree, rules=knowledge_rules)
        return custom, knowledge
    def _build_exploit_reports(self, findings: list,
                               trace_by_sink: dict,
                               symbolic_paths: list,
                               opts: DiagOptions) -> list:
        if not opts.include_extras:
            return []
        reports = []
        for finding in findings:
            traces = trace_by_sink.get((finding.file, finding.line), [])
            reports.append(self.report_generator.generate(
                finding,
                taint_trace=self._match_trace_for_finding(
                    traces, finding.sink),
                exec_paths=self._match_paths_for_finding(
                    symbolic_paths, finding.line, finding.sink),
            ))
        return reports
    @staticmethod
    def _index_traces_by_sink(taint_traces: list,
                              filepath: str) -> dict[tuple[str, int], list[TaintTrace]]:
        trace_by_sink: dict[tuple[str, int], list[TaintTrace]] = {}
        for trace in taint_traces:
            sink_line = getattr(trace, "sink_line", 0)
            if not sink_line:
                continue
            sink_file = _sink_record_file(
                getattr(trace, "sink_file", ""), filepath)
            trace_by_sink.setdefault((sink_file, sink_line), []).append(trace)
        return trace_by_sink
    @staticmethod
    def _sink_names_match(actual: Any, expected: Any) -> bool:
        if not isinstance(actual, str) or not isinstance(expected, str):
            return False
        actual = actual.strip()
        expected = expected.strip()
        if not actual or not expected:
            return False
        if actual == expected:
            return True
        actual_tail = actual.rsplit('.', 1)[-1]
        expected_tail = expected.rsplit('.', 1)[-1]
        return (('.' not in actual and actual == expected_tail)
                or ('.' not in expected and actual_tail == expected))
    @classmethod
    def _match_trace_for_finding(cls, traces: list[TaintTrace],
                                 sink_name: str) -> TaintTrace | None:
        if not traces:
            return None
        if not sink_name:
            return traces[0]
        return next((trace for trace in traces
                     if cls._sink_names_match(
                         getattr(trace, 'sink_expr', ''), sink_name)), None)
    def _build_cfg_du_maps(self, tree: ast.Module, opts: DiagOptions) -> tuple[dict, dict]:
        if not (opts.enable_cfg_du and opts.include_extras):
            return {}, {}
        return self.vuln_detector.cfg_du_report(tree)
    def _run_symbolic_pass(self, tree: ast.Module) -> list:
        symbolic_paths = []
        for node in tree_nodes(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                paths = self.symbolic_executor.execute(node, import_tree=tree)
                self._backfill_trigger_input(paths, node)
                symbolic_paths.extend(paths)
        return symbolic_paths
    def _backfill_trigger_input(self, paths: list, node: Any) -> None:
        for p in paths:
            if (p.reaches_sink and p.is_feasible
                    and not p.trigger_input):
                seeds = self.concolic_seeds.generate(
                    node, base_constraints=p.constraints,
                    allow_negation=False)
                if seeds:
                    p.trigger_input = seeds[0]
    @staticmethod
    def _match_paths_for_finding(paths: list, line: int,
                                 sink_name: str = "") -> list:
        if not isinstance(line, int) or isinstance(line, bool) or line <= 0:
            return []
        matched = [p for p in paths if getattr(p, "sink_line", None) == line]
        if not sink_name:
            return matched
        return [p for p in matched
                if EnhancedSecurityDiagnoser._sink_names_match(
                    getattr(p, 'sink_name', ''), sink_name)]
    def _load_knowledge_rules(self) -> list[dict]:
        try:
            return self.knowledge.export_as_detection_rules()
        except Exception as e:  # noqa: BLE001
            _log.warning("[Security] 知识学习器导出失败: %s", e)
            return []
    def _apply_knowledge_patterns(self, code: str, filepath: str,
                                  tree: ast.Module | None = None,
                                  rules: list[dict] | None = None
                                  ) -> list[_Finding]:
        if not isinstance(code, str):
            _log.warning("[Security] 非字符串源码输入,跳过知识模式匹配")
            return []
        if rules is None:
            rules = self._load_knowledge_rules()
        if not rules:
            return []
        if tree is None:
            tree, err = parse_ast_safely(code)
            if err is not None:
                _log.warning("[Security] 知识模式检测跳过(源码解析失败): %s", err)
                return []
        node_srcs = [(node, _STR_LITERAL_RE.sub("''", src))
                     for node, src in self.custom_rules.node_sources(tree)]
        return self.vuln_detector.match_knowledge_patterns(
            rules, node_srcs, filepath)
def get_diagnoser() -> EnhancedSecurityDiagnoser:
    return _diagnoser
def release_diagnoser_caches() -> int:
    n = 0
    with _DIAG_RESULT_LOCK:
        if _DIAG_RESULT_CACHE:
            _DIAG_RESULT_CACHE.clear()
            n += 1
    with _FRAMEWORK_CTX_CACHE_LOCK:
        if _FRAMEWORK_CTX_CACHE:
            _FRAMEWORK_CTX_CACHE.clear()
            n += 1
    with _SECURITY_SCAN_CACHE_LOCK:
        if _SECURITY_SCAN_CACHE:
            _SECURITY_SCAN_CACHE.clear()
            n += 1
    tracker = getattr(_diagnoser, "taint_tracker", None)
    if tracker is not None and getattr(tracker, "traces", None):
        tracker.traces = []
        n += 1
    executor = getattr(_diagnoser, "symbolic_executor", None)
    reset_state = getattr(executor, "reset_state", None)
    if callable(reset_state):
        n += reset_state()
    n += clear_taint_scope_memos()
    n += _diagnoser.custom_rules.release_tree_caches()
    n += _release_scanner_caches()
    return n
_diagnoser = EnhancedSecurityDiagnoser()
_SECURITY_SCAN_CACHE: dict = {}
_SECURITY_SCAN_CACHE_LOCK = threading.Lock()
# 单条“上次完整结果”备忘：SE38/SE39/SE40 三个场景检查对同一文件连续各调
# 一次 ``run_enhanced_security_scan``，每次都会重跑跨文件污点追踪（实测占
# 单文件耗时的大头）。只保留最近一条即可把三次压成一次，且不同文件天然互斥，
# 不存在跨文件陈旧风险。
_SECURITY_SCAN_LAST: dict = {}
def _remember_scan_result(key: str, findings: list) -> None:
    _SECURITY_SCAN_LAST.clear()
    _SECURITY_SCAN_LAST[key] = list(findings)
def clear_security_scan_cache() -> None:
    with _SECURITY_SCAN_CACHE_LOCK:
        _SECURITY_SCAN_CACHE.clear()
        _SECURITY_SCAN_LAST.clear()
def _security_scan_rule_state() -> tuple[list[_Rule], list[dict]]:
    diagnoser = get_diagnoser()
    return diagnoser.custom_rules.get_all(), diagnoser._load_knowledge_rules()
def security_scan_cache_key(source_text: str, filepath: str, tree: Any) -> str:
    filepath = normalize_filepath(filepath)
    source_text = source_text if isinstance(source_text, str) else ""
    tree_text = _diag_tree_text(tree)
    semantic_state = repr(_security_scan_rule_state())
    payload = (f"{len(filepath)}:{filepath}{len(source_text)}:"
               f"{source_text}{len(tree_text)}:{tree_text}"
               f"{len(semantic_state)}:{semantic_state}")
    return hashlib.sha256(
        payload.encode("utf-8", "surrogatepass")).hexdigest()
def security_scan_cache_lookup(key: str) -> list | None:
    if not isinstance(key, str):
        return None
    with _SECURITY_SCAN_CACHE_LOCK:
        cached = _SECURITY_SCAN_CACHE.get(key)
    if cached is None:
        return None
    return [_copy_diagnose_finding(f) for f in cached]
def security_scan_cache_store(key: str, findings: list) -> None:
    if not isinstance(key, str) or not isinstance(findings, (list, tuple)):
        return
    copied = [_copy_diagnose_finding(f) for f in findings]
    with _SECURITY_SCAN_CACHE_LOCK:
        _cache_put(_SECURITY_SCAN_CACHE, key, copied, _RESULT_CACHE_MAX)
def _copy_diagnose_finding(f: Any) -> Any:
    to_dict = getattr(f, "to_dict", None)
    if callable(to_dict):
        try:
            return type(f)(**to_dict())
        except (TypeError, ValueError) as _copy_err:
            _log.debug("[Security] finding to_dict 重建失败，降级浅拷贝: %s",
                       _copy_err)
    return _shallow_copy(f)
register_cache_release(
    "e1_diagnoser_caches", release_diagnoser_caches, "E1 诊断器缓存", order=110)
_SE_RULE_SCENARIO = "SE-38"
_SE_RULE_CUSTOM = "SE-39"
_SE_RULE_SYMBOLIC = "SE-40"
_TAINT_FINDING_PREFIX = "[EnhancedSecurity] 跨文件污点传播:"
_CATEGORY_TO_SE_RULE: dict[str, str] = {
    "sql_injection": "SE-05",
    "command_injection": "SE-02",
    "deserialization": "SE-04",
    "path_traversal": "SE-06",
    "xss": "SE-16",
    "xxe": "SE-19",
    "weak_crypto": "SE-10",
    "hardcoded_secret": "SE-03",
}
_SEVERITY_TO_DIAG: dict[str, str] = {
    "CRITICAL": "P0", "HIGH": "P0", "MEDIUM": "P1", "LOW": "P2", "INFO": "P3",
}
_DIAG_P_LEVELS = frozenset(_SEVERITY_TO_DIAG.values())
_SUGGESTION_VULN = (
    '根因: 安全扫描器检测到潜在漏洞,具体类别和详情见description字段。\n'
    '修复策略(按优先级):\n1. 根据CWE编号查阅OWASP修复指南\n'
    '2. 使用安全编码模式替代不安全模式\n3. 添加输入验证和输出编码\n'
    '4. 启用安全防护中间件\n'
    '参考标准: OWASP Top 10 / CWE数据库 / Bandit规则集'
)
_SUGGESTION_TAINT = (
    '根因: 用户输入或外部数据通过函数调用链传播到危险汇聚点'
    '(exec/eval/SQL执行)未经过净化,攻击者可构造恶意输入实现'
    '代码注入/SQL注入/命令注入。\n修复策略(按优先级):\n'
    '1. 在汇聚点使用参数化查询替代字符串拼接(SQL参数化)\n'
    '2. 在数据入口处添加输入净化(白名单过滤/类型校验)\n'
    '3. 使用安全API替代危险函数(shlex.quote替代os.system)\n'
    '4. 添加输出编码防止XSS(html.escape)\n代码示例:\n'
    '  # 修复前: query = f"SELECT * FROM users WHERE name=\'{user_input}\'"\n'
    '  # 修复后: cursor.execute("SELECT * FROM users WHERE name=%s", (user_input,))\n'
    '参考标准: OWASP A03:2021-Injection / CWE-89(SQL注入) / '
    'CWE-78(命令注入) / Bandit B608'
)
_SUGGESTION_FRAMEWORK = (
    '根因: 代码使用了框架特定的不安全API或反模式,如Django的raw()'
    'SQL执行、Flask的render_template_string(XSS风险)、FastAPI的'
    '未验证重定向,绕过了框架内置的安全防护机制。\n'
    '修复策略(按优先级):\n1. 替换为框架推荐的安全API'
    '(Django ORM替代raw()/Jinja2自动转义替代render_template_string)\n'
    '2. 启用框架安全中间件(Django SecurityMiddleware/Flask-Talisman)\n'
    '3. 配置CSP(内容安全策略)头限制脚本来源\n'
    '4. 使用框架内置的CSRF保护机制\n代码示例:\n'
    '  # Django: 修复前 - User.objects.raw(f"SELECT * WHERE name=\'{name}\'")\n'
    '  # Django: 修复后 - User.objects.filter(name=name)\n'
    '参考标准: OWASP A04:2021-Insecure Design / CWE-1004(框架安全配置) / '
    'Bandit B703'
)
_SUGGESTION_SYMBOLIC = (
    '根因: 通过符号执行验证发现特定输入组合下存在可达的安全约束违反路径,'
    '程序缺少输入边界检查或约束验证,在极端输入条件下可能触发未处理的'
    '安全漏洞(缓冲区溢出/整数溢出/空指针解引用)。\n修复策略(按优先级):\n'
    '1. 在函数入口添加输入边界检查(范围/类型/长度校验)\n'
    '2. 添加前置条件断言(assert 0 <= value < MAX_SIZE)\n'
    '3. 使用类型注解+运行时验证(pydantic/typing.cast)\n'
    '4. 对关键路径添加不变量检查(invariant check)\n代码示例:\n'
    '  # 修复前: def process(data): return buffer[data[\'offset\']]\n'
    '  # 修复后: def process(data):\n'
    '  #     offset = data[\'offset\']\n'
    '  #     if not isinstance(offset, int) or offset < 0 '
    'or offset >= len(buffer):\n'
    '  #         raise ValueError(f"Invalid offset: {offset}")\n'
    '  #     return buffer[offset]\n'
    '参考标准: SAST-Symbolic Execution / CWE-20(输入验证不当) / '
    'CWE-125(越界读取)'
)
def _normalize_finding_line(line_num: Any) -> int:
    if isinstance(line_num, bool) or line_num is None:
        return 0
    if isinstance(line_num, int):
        return max(0, line_num)
    if isinstance(line_num, float):
        if not (math.isfinite(line_num) and line_num.is_integer()):
            return 0
        return max(0, int(line_num))
    if isinstance(line_num, str):
        text = line_num.strip()
        if text.isascii() and text.isdigit():
            return int(text)
    return 0
def _build_security_finding(rule_id: str, severity: str, filepath: str,
                            line_num: Any, description: str,
                            suggestion: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id=rule_id,
        severity=severity,
        dimension="security",
        file=filepath,
        line=_normalize_finding_line(line_num),
        description=description,
        suggestion=suggestion,
    )
def _confidence_suffix(value: Any) -> str:
    if value is None or isinstance(value, bool):
        return ""
    try:
        confidence = float(value)
    except (TypeError, ValueError, OverflowError):  # jwsgj:silent-ok 非数值置信度省略展示
        return ""
    if not math.isfinite(confidence):
        return ""
    return f" confidence={confidence:.0%}"
def _severity_to_diag(value: Any, default: str = "P1") -> str:
    text = getattr(value, "value", value)
    if not isinstance(text, str) or not text.strip():
        return default
    upper = text.strip().upper()
    if upper in _DIAG_P_LEVELS:
        return upper
    return _SEVERITY_TO_DIAG.get(upper, default)
def _convert_vuln_finding_to_result(finding, filepath: str) -> DiagnoseFinding:
    cat_value = _category_label(_record_field(finding, "category", ""))
    rule_id = _CATEGORY_TO_SE_RULE.get(cat_value, _SE_RULE_SCENARIO)
    severity = _severity_to_diag(_record_field(finding, "severity", ""))
    source = _record_field(finding, "source", "")
    sink = _record_field(finding, "sink", "")
    cwe_id = _record_field(finding, "cwe_id", "")
    description = (
        f"[EnhancedSecurity] {cat_value}: {source} -> {sink}"
        + (f" (CWE: {cwe_id})" if cwe_id else "")
        + _confidence_suffix(_record_field(finding, "confidence"))
    )
    suggestion = _record_field(finding, "suggestion", "")
    return _build_security_finding(
        rule_id, severity, filepath, _record_field(finding, "line", 0),
        description, suggestion or _SUGGESTION_VULN)
_TAINT_SOURCE_FIELDS = ('source_expr', 'variable', 'source')
_TAINT_SINK_FIELDS = ('sink_expr', 'sink')
_TAINT_RECORD_FIELDS = _TAINT_SOURCE_FIELDS + _TAINT_SINK_FIELDS
_FIELD_MISSING = object()
def _record_field(record: Any, name: str, default: Any = None) -> Any:
    if isinstance(record, dict):
        return record.get(name, default)
    return getattr(record, name, default)
def _first_record_field(record: Any, fields: tuple[str, ...], default: Any) -> Any:
    for fname in fields:
        value = _record_field(record, fname)
        if value:
            return value
    return default
def _sink_record_file(sink_file: Any, filepath: str) -> str:
    sink = normalize_filepath(sink_file)
    if not sink or sink == filepath:
        return filepath
    if not filepath or os.path.isabs(sink) == os.path.isabs(filepath):
        return sink
    try:
        if os.path.isabs(sink):
            return os.path.relpath(sink)
        return os.path.abspath(sink)
    except ValueError:
        return sink
def _taint_record(trace):
    if not any(_record_field(trace, field, _FIELD_MISSING) is not _FIELD_MISSING
               for field in _TAINT_RECORD_FIELDS):
        return None
    if not any(_record_field(trace, field) for field in _TAINT_SINK_FIELDS):
        return None
    source_name = _first_record_field(trace, _TAINT_SOURCE_FIELDS, 'unknown')
    sink_name = _first_record_field(trace, _TAINT_SINK_FIELDS, 'unknown')
    line_num = _record_field(trace, 'sink_line')
    if not line_num:
        line_num = _record_field(trace, 'source_line')
    if not line_num:
        line_num = _record_field(trace, 'line') or 0
    return source_name, sink_name, line_num, _record_field(trace, 'sink_file', '')
def _supplement_record(cf):
    if not isinstance(cf, dict) and not hasattr(cf, 'line'):
        return None
    desc = (_record_field(cf, 'description', '')
            or f"{_record_field(cf, 'source', '') or 'unknown'}: "
               f"{_record_field(cf, 'sink', '')}")
    return (_record_field(cf, 'line', 0), desc,
            _record_field(cf, 'suggestion') or None,
            _record_field(cf, 'severity', ''))
_TRUE_FLAG_TEXT = frozenset({"1", "true", "yes", "on"})
_FALSE_FLAG_TEXT = frozenset({"0", "false", "no", "off", ""})
def _flag_value(value: Any, default: bool) -> bool:
    if value is None or value is _FIELD_MISSING:
        return default
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value != 0
    if isinstance(value, float):
        return math.isfinite(value) and value != 0.0
    if isinstance(value, str):
        normalized = value.strip().lower()
        if normalized in _TRUE_FLAG_TEXT:
            return True
        if normalized in _FALSE_FLAG_TEXT:
            return False
    return False
def _crossed_modules_flag(value: Any) -> bool:
    if isinstance(value, (list, tuple, set, frozenset)):
        return bool(value)
    return _flag_value(value, False)
def _symbolic_record(sp):
    vulnerable = _record_field(sp, 'reaches_sink', _FIELD_MISSING)
    if vulnerable is _FIELD_MISSING or vulnerable is None:
        vulnerable = _record_field(sp, 'vulnerable', False)
    feasible = _flag_value(_record_field(sp, 'is_feasible', True), True)
    sink_line = _record_field(sp, 'sink_line')
    if sink_line is None:
        sink_line = _record_field(sp, 'line', 0)
    return (_flag_value(vulnerable, False), feasible,
            _record_field(sp, 'path_id', '?'), sink_line)
def _is_cross_file_taint_finding(finding: Any) -> bool:
    return (_record_field(finding, "id") == _SE_RULE_SCENARIO
            and str(_record_field(finding, "description", "")).startswith(
                _TAINT_FINDING_PREFIX))


def run_enhanced_security_scan(tree: Any, source_lines: Any, filepath: str) -> list:
    filepath = normalize_filepath(filepath)
    source_text = join_source_lines(source_lines)
    if not source_text.strip():
        return []
    findings = []
    _scan_failed = False
    _cache_key = ""
    try:
        _cache_key = security_scan_cache_key(source_text, filepath, tree)
        _recent = _SECURITY_SCAN_LAST.get(_cache_key)
        if _recent is not None:
            return list(_recent)
        _cached = security_scan_cache_lookup(_cache_key)
        diagnoser = get_diagnoser()
        if _cached is not None:
            findings = [f for f in _cached
                        if not _is_cross_file_taint_finding(f)]
            traces = diagnoser._collect_taint_traces(
                filepath, source_text,
                tree if isinstance(tree, ast.Module) else None,
                _DEFAULT_DIAG_OPTIONS)
            findings.extend(_convert_taint_findings(
                {"taint_traces": traces}, filepath))
            security_scan_cache_store(_cache_key, findings)
            _remember_scan_result(_cache_key, findings)
            return findings
        result = diagnoser.diag(source_text, filepath=filepath,
                                tree=tree if isinstance(tree, ast.Module) else None)
        if not result.get("ok"):
            _log.debug("run_enhanced_security_scan: EnhancedSecurityDiagnoser returned error: %s",
                       result.get("error", "unknown"))
            return []
        for convert in _ENHANCED_FINDING_CONVERTERS:
            findings.extend(convert(result, filepath))
    except Exception as e:  # noqa: BLE001 —— 诊断链路软失败降级不阻断调用方（CFG/DU-Chain/符号执行深链路异常面广）
        _scan_failed = True
        _log.warning("run_enhanced_security_scan: EnhancedSecurityDiagnoser failed for %s: %s", filepath, e)
    if not _scan_failed and _cache_key:
        security_scan_cache_store(_cache_key, findings)
        _remember_scan_result(_cache_key, findings)
    return list(findings)
def _convert_vuln_findings(result: Any, filepath: str) -> list:
    findings: list = []
    for vf in result.get("findings") or []:
        if _flag_value(_record_field(vf, 'is_false_positive', False), False):
            continue
        try:
            findings.append(_convert_vuln_finding_to_result(vf, filepath))
        except (AttributeError, TypeError, ValueError) as e:
            _log.debug("run_enhanced_security_scan: 单条 finding 转换失败，跳过: %s", e)
    return findings
def _convert_taint_findings(result: Any, filepath: str) -> list:
    findings: list = []
    for trace in result.get("taint_traces") or []:
        record = _taint_record(trace)
        if record is None:
            continue
        source_name, sink_name, line_num, sink_file = record
        source_path = _sink_record_file(
            _record_field(trace, 'source_file', ''), filepath)
        sink_path = _sink_record_file(sink_file, filepath)
        if (not _crossed_modules_flag(
                _record_field(trace, 'crossed_modules', False))
                and os.path.normcase(os.path.abspath(source_path or filepath))
                == os.path.normcase(os.path.abspath(sink_path or filepath))):
            continue
        findings.append(_build_security_finding(
            _SE_RULE_SCENARIO, "P1", sink_path, line_num,
            f"{_TAINT_FINDING_PREFIX} {source_name} -> {sink_name}",
            _SUGGESTION_TAINT,
        ))
    return findings
def _convert_supplement_findings(result: Any, filepath: str) -> list:
    findings: list = []
    framework = result.get("framework") or "unknown"
    context_label = (f"框架({framework})安全风险" if framework != "unknown"
                     else "自定义规则安全风险")
    for field_name in ("custom_findings", "knowledge_findings"):
        for cf in result.get(field_name) or []:
            record = _supplement_record(cf)
            if record is None:
                continue
            line_num, desc, suggestion, severity = record
            findings.append(_build_security_finding(
                _SE_RULE_CUSTOM, _severity_to_diag(severity, "P2"),
                filepath, line_num,
                f"[EnhancedSecurity] {context_label}: {desc}",
                suggestion or _SUGGESTION_FRAMEWORK,
            ))
    return findings
def _convert_symbolic_findings(result: Any, filepath: str) -> list:
    findings: list = []
    for sp in result.get("symbolic_paths") or []:
        vulnerable, feasible, sp_path_id, sp_line = _symbolic_record(sp)
        trigger_input = _record_field(sp, 'trigger_input')
        if not (vulnerable and feasible and isinstance(trigger_input, dict)):
            continue
        findings.append(_build_security_finding(
            _SE_RULE_SYMBOLIC, "P2", filepath, sp_line,
            f"[EnhancedSecurity] 符号执行验证: 路径 {sp_path_id} 存在安全约束违反",
            _SUGGESTION_SYMBOLIC,
        ))
    return findings
_ENHANCED_FINDING_CONVERTERS = (
    _convert_vuln_findings,
    _convert_taint_findings,
    _convert_supplement_findings,
    _convert_symbolic_findings,
)
def _make_se_check(name: str, *, keep: tuple[str, ...] = (),
                   drop: tuple[str, ...] = ()) -> Any:
    def _check(tree: Any, source_lines: Any, filepath: Any,
               index: list | None = None) -> list:
        if finding_scan_exempt(filepath):
            return []
        if index is not None and not index:
            return []
        findings = run_enhanced_security_scan(tree, source_lines, filepath)
        if keep:
            return [f for f in findings if getattr(f, 'id', None) in keep]
        if drop:
            return [f for f in findings if getattr(f, 'id', None) not in drop]
        return findings
    _check.__name__ = name
    _check.__qualname__ = name
    _check.__doc__ = (
        f"SE 场景级检查器 {name}：保留 {keep or '全部'}，"
        f"剔除 {drop or '无'}。")
    return _check
check_SE38 = _make_se_check(
    "check_SE38", drop=(_SE_RULE_CUSTOM, _SE_RULE_SYMBOLIC))
check_SE39 = _make_se_check("check_SE39", keep=(_SE_RULE_CUSTOM,))
check_SE40 = _make_se_check("check_SE40", keep=(_SE_RULE_SYMBOLIC,))
def wiring_declarations() -> dict:
    return {
        "catalogs": {"se_checks": {
            'SE38': check_SE38, 'SE39': check_SE39, 'SE40': check_SE40,
        }},
        "rebuild_hooks": {"security_scan_cache": clear_security_scan_cache},
    }

from __future__ import annotations

import inspect
import logging
import os
import time
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from typing import Any, NamedTuple, Protocol

from jwsgj.diag_antipattern_flow_detect import collect_top_scan_files
from jwsgj.diag_antipattern_flow_govern import real_antipattern_scan
from jwsgj.diag_blindspot_file import DEFAULT_PROJECT_ROOT
from jwsgj.diag_blindspot_refs import (
    is_exported_from_init,
    is_facade_module,
    is_library_project,
)
from jwsgj.diag_blindspot_symbol import (
    DEFAULT_INCLUDE_CODE_BLINDSPOTS,
    run_layer14_parallel,
    run_layers_5_to_76,
)
from jwsgj.diag_callgraph_builder import CallGraphBuilder
from jwsgj.diag_callgraph_channels import (
    merge_bindings_into_callgraph,
    scan_runtime_bindings,
)
from jwsgj.diag_guard_state import (
    serialize_json,
    write_json_artifact,
)
from jwsgj.diag_health_profile import analyze_call_depth
from jwsgj.diag_shared_ast_views import structural_fingerprint
from jwsgj.diag_ten_dim_scorer import quick_score
from jwsgj.diag_types_normalize import (
    as_entry_list,
    as_list,
    as_number,
    dict_or_empty,
    finite_float_or_none,
    float_metric,
    is_number,
    normalize_line_no,
    numeric_or,
    safe_text,
    severity_key,
    severity_penalty_weight,
    severity_text_value,
    timestamp_human,
)
from jwsgj.diag_types_vocab import (
    AST_VISITOR_PREFIXES,
    CAT_CROSS_VALIDATION,
    CLI_CMD_PREFIXES,
    FIELD_POTENTIAL_FP,
    FIELD_TOTAL_BLINDSPOTS,
    FIELD_TOTAL_FUNCTIONS,
    FMT_DATETIME,
    FUNCTION_ORPHAN_BLINDSPOT_TYPES,
    LAYER_DEGRADE_EXC,
    MESSAGE_TRUNCATE_LEN,
    POLYMORPHIC_METHODS,
    RULE_UNREACHABLE_CODE,
    SEVERITY_RANK,
    UNTESTED_COVERAGE_BLINDSPOT_TYPES,
    Thresholds,
)
from jwsgj.log_config import log_swallowed, timed_log
from jwsgj.runtime_scope import is_diagnosis_out_of_scope, validate_source_paths
from jwsgj.shared_cache import as_diag_ctx, ensure_entry_warmed, validated_warmed_root
from jwsgj.shared_cache_store import (
    callgraph_share_fingerprint,
    persist_call_graph_share,
)

DEFAULT_TOP_FILES = 8
__all__ = [
    "DEFAULT_TOP_FILES",
    "HIGH_SEVERITY_NONE_TYPES",
    "BlindspotHub",
    "BlindspotSummary",
    "CallGraphAnalyzer",
    "UnifiedBlindspotEntry",
    "UnifiedBlindspotReport",
    "apply_blindspot_summary",
    "cluster_by_structural_similarity",
    "collect_blindspot_entries",
    "compute_reliability_weighted_penalty",
    "confirm_dead_code_with_evidence",
    "detect_pattern_collapse",
    "detect_proximity_clustering",
    "ensure_call_graph",
    "load_ignore_decorators",
    "load_whitelist",
    "polymorphic_reason",
    "resolve_numeric_severity",
    "run_call_graph_analysis",
    "run_callgraph_channel",
    "run_lightweight_diagnosis",
    "scan_blindspots",
]
logger = logging.getLogger(__name__)
_LAYER14_REPORT_SPECS = (
    (
        "script",
        "脚本: {total_scripts}个, CLI入口={cli_scripts}, "
        "独立={standalone_scripts}, 盲区={" + FIELD_TOTAL_BLINDSPOTS + "}",
    ),
    (
        "module",
        "模块: {total_modules}个, 导入边={import_edges}, 盲区={"
        + FIELD_TOTAL_BLINDSPOTS + "}",
    ),
    (
        "func",
        "函数: {" + FIELD_TOTAL_FUNCTIONS + "}个, 公开={public_functions}, "
        "盲区={" + FIELD_TOTAL_BLINDSPOTS + "}",
    ),
    (
        "class",
        "类: {total_classes}个, 实例化={total_instantiations}次, 盲区={"
        + FIELD_TOTAL_BLINDSPOTS + "}",
    ),
)
_DEFENSIVE_TYPES = frozenset({
    "except", "try_body", "with", "decorator", "finally", "try_else",
})
_BOUNDARY_TYPES = frozenset({
    "branch", "comprehension", "generator", "loop",
    "else_block", "loop_else", "match_case",
})
_KNOWN_CONF_KEYS = {
    "confirmed": "confirmed_pct",
    "confirmed_untested": "confirmed_untested_pct",
    FIELD_POTENTIAL_FP: "potential_false_positive_pct",
    "external_api": "external_api_pct",
}
_KNOWN_CONF = tuple(_KNOWN_CONF_KEYS)
CATEGORY_DEFENSIVE = "defensive"
CATEGORY_BOUNDARY = "boundary"
CATEGORY_CORE = "core"
_CATEGORY_ORDER = (CATEGORY_DEFENSIVE, CATEGORY_BOUNDARY, CATEGORY_CORE)
_FUNCTION_ORPHAN_TYPES = FUNCTION_ORPHAN_BLINDSPOT_TYPES
_CONFIDENCE_BY_TYPE: dict[str, tuple[int, int]] = {
    "orphan_module": (85, 70),
    "dead_module": (80, 65),
    "unused_import": (90, 90),
}
_DEAD_CODE_CONFIDENCE: tuple[tuple[str, int], ...] = (("critical", 95),)
_DEAD_CODE_DEFAULT_CONFIDENCE = 80
_CONFIRMED_MIN_CONFIDENCE = 90
_POTENTIAL_FP_MIN_CONFIDENCE = 70
_EXTERNAL_API_MIN_CONFIDENCE = 60
_FUNCTION_ORPHAN_LIBRARY_CONFIDENCE = _EXTERNAL_API_MIN_CONFIDENCE
_FUNCTION_ORPHAN_CONFIDENCE = _POTENTIAL_FP_MIN_CONFIDENCE
_FALLBACK_CONFIDENCE = _POTENTIAL_FP_MIN_CONFIDENCE
_CONFIRMED_ENTRY_CONFIDENCE = _CONFIRMED_MIN_CONFIDENCE
_NUMERIC_CONF_FLOOR = _EXTERNAL_API_MIN_CONFIDENCE
_POTENTIAL_FP_CONFIDENCE = 75
_RELIABILITY_CONFIRMED_MIN = 0.70
_RELIABILITY_POTENTIAL_FP_MIN = 0.55
@dataclass
class UnifiedBlindspotEntry:
    level: str
    blindspot_type: str
    severity: str
    filepath: str
    line: int = 0
    end_line: int = 0
    name: str = ""
    message: str = ""
    suggestion: str = ""
    details: dict[str, Any] = field(default_factory=dict)
    confidence: str = "unknown"
    confidence_reason: str = ""
    numeric_confidence: float | None = None
    reliability_score: float | None = None
    def to_dict(self) -> dict:
        return {
            "rule_id": self.blindspot_type,
            "method_id": "D1",
            "level": self.level,
            "blindspot_type": self.blindspot_type,
            "severity": self.severity,
            "filepath": self.filepath,
            "line": self.line,
            "end_line": self.end_line,
            "name": self.name,
            "message": self.message,
            "suggestion": self.suggestion,
            "details": self.details,
            "confidence": self.confidence,
            "confidence_reason": self.confidence_reason,
            "numeric_confidence": self.numeric_confidence,
            "reliability_score": self.reliability_score,
        }
class _EntryPosition(NamedTuple):
    level: str
    name: str
    line: int = 0
    end_line: int = 0
_SEVERITY_BY_RANK = ("critical", "high", "medium", "low", "info")
_SEVERITY_LEVELS = tuple(reversed(_SEVERITY_BY_RANK))
def _merge_metric_value(old, new):
    if is_number(old) and is_number(new):
        return old + new
    if isinstance(old, dict) and isinstance(new, dict):
        return _merge_layer_metrics(old, new)
    return new
def _merge_layer_metrics(existing, new):
    if not isinstance(new, dict):
        return dict(existing) if isinstance(existing, dict) else {}
    if not isinstance(existing, dict) or not existing:
        return dict(new)
    merged = dict(existing)
    for key, value in new.items():
        merged[key] = (_merge_metric_value(merged[key], value)
                       if key in merged else value)
    return merged
def _hashable_key(value, fallback: str = "unknown"):
    try:
        hash(value)
    except TypeError as _e:
        log_swallowed(__name__, _e, context='_hashable_key:TypeError')
        return fallback
    return value
HIGH_SEVERITY_NONE_TYPES = frozenset({
    RULE_UNREACHABLE_CODE,
    "empty_function", "stub_function", "pass_stub", "dead_stub", "empty_shell",
})
_CANONICAL_SEVERITIES = frozenset(_SEVERITY_LEVELS)
_SEVERITY_NAME_BY_RANK = dict(enumerate(_SEVERITY_BY_RANK))
_PENALTY_SEVERITY_BY_NAME = {
    name: f"P{rank}" for rank, name in _SEVERITY_NAME_BY_RANK.items()
}
def _downgrade_severity(severity: str) -> str:
    if not isinstance(severity, str):
        return severity
    canonical = resolve_numeric_severity("", severity)
    if canonical not in _CANONICAL_SEVERITIES:
        return severity
    idx = _SEVERITY_LEVELS.index(canonical)
    return _SEVERITY_LEVELS[max(idx - 1, 0)]
def resolve_numeric_severity(blindspot_type: str, severity) -> str:
    if severity is None:
        return "high" if blindspot_type in HIGH_SEVERITY_NONE_TYPES else "medium"
    text = str(getattr(severity, "value", severity)).strip().lower()
    if text in _CANONICAL_SEVERITIES:
        return text
    rank = SEVERITY_RANK.get(text.upper())
    if rank is None:
        return text
    return _SEVERITY_NAME_BY_RANK.get(rank, "low")
def _compute_numeric_confidence(level: str, blindspot_type: str, severity: str,
                                 is_library: bool, is_dead_code: bool = False) -> int:
    if blindspot_type in HIGH_SEVERITY_NONE_TYPES:
        return 100
    fixed_score = _CONFIDENCE_BY_TYPE.get(blindspot_type)
    if fixed_score is not None:
        general_score, library_score = fixed_score
        return library_score if is_library else general_score
    if blindspot_type == "dead_code_block" or is_dead_code:
        return _dead_code_confidence(severity)
    if level == "function" and blindspot_type in _FUNCTION_ORPHAN_TYPES:
        return (_FUNCTION_ORPHAN_LIBRARY_CONFIDENCE if is_library
                else _FUNCTION_ORPHAN_CONFIDENCE)
    return _FALLBACK_CONFIDENCE
def _dead_code_confidence(severity: str) -> int:
    for label, score in _DEAD_CODE_CONFIDENCE:
        if severity == label:
            return score
    return _DEAD_CODE_DEFAULT_CONFIDENCE
def _confidence_to_category(confidence: float) -> str:
    if confidence >= _CONFIRMED_MIN_CONFIDENCE:
        return "confirmed"
    if confidence >= _POTENTIAL_FP_MIN_CONFIDENCE:
        return FIELD_POTENTIAL_FP
    if confidence >= _EXTERNAL_API_MIN_CONFIDENCE:
        return "external_api"
    return "unknown"
def _classify_generic_confidence(is_lib: bool, level: str, filepath: str, blindspot_type: str,
                                 severity: str | None = None,
                                 is_dead_code: bool = False) -> tuple:
    severity = resolve_numeric_severity(blindspot_type, severity)
    numeric_conf = _compute_numeric_confidence(
        level=level, blindspot_type=blindspot_type, severity=severity,
        is_library=is_lib, is_dead_code=is_dead_code
    )
    if level == "module" and os.path.basename(filepath) == "__init__.py":
        return ("external_api",
                f"__init__.py orchestrator (confidence: {numeric_conf}%)")
    category = _confidence_to_category(numeric_conf)
    if level == "script" and is_lib:
        return (FIELD_POTENTIAL_FP, f"library skill script (confidence: {numeric_conf}%)")
    return (category, f"numeric confidence {numeric_conf}% | type={blindspot_type}")
def _classify_public_orphan(function_name: str, is_lib: bool) -> tuple:
    if is_lib:
        return ("external_api",
                "library skill public API, designed for external consumption")
    _simple = function_name.rsplit('.', 1)[-1] if function_name else ''
    shape_reason = polymorphic_reason(_simple)
    if shape_reason:
        return (FIELD_POTENTIAL_FP, shape_reason)
    return ("confirmed", "internal dead code")
def _classify_confidence(blindspot, *, is_lib: bool, is_facade) -> tuple:
    fp = getattr(blindspot, "filepath", "")
    fn = getattr(blindspot, "function_name", "")
    bt = getattr(blindspot, "blindspot_type", "")
    is_public = getattr(blindspot, "is_public", False)
    basename = os.path.basename(fp)
    if basename == "__init__.py":
        return ("external_api", "__init__.py public API")
    if is_facade(fp):
        return ("external_api", "structural facade re-export")
    if bt in UNTESTED_COVERAGE_BLINDSPOT_TYPES:
        return ("confirmed_untested",
                "live function with callers; uncovered lines are a test gap, not dead code")
    if is_public and bt in _FUNCTION_ORPHAN_TYPES:
        return _classify_public_orphan(fn, is_lib)
    if not is_public and bt == "orphan" and is_lib:
        return (FIELD_POTENTIAL_FP,
                "library-style skill private helper; public-API reachability unverified")
    return ("confirmed", "internal dead code")
def _classify_class_confidence(project_root: str, blindspot, *,
                                is_lib: bool) -> tuple:
    if not is_lib:
        return ("confirmed", "class never instantiated within project")
    class_name = getattr(blindspot, "class_name", "")
    filepath = getattr(blindspot, "filepath", "")
    if is_exported_from_init(project_root, class_name, filepath):
        return ("external_api",
                "library skill class exported from __init__.py, designed for external instantiation")
    return ("confirmed", "internal class not exported from __init__.py")
def polymorphic_reason(function_name: str) -> str | None:
    if function_name in POLYMORPHIC_METHODS:
        return "polymorphic method"
    if function_name.startswith(AST_VISITOR_PREFIXES):
        return "AST visitor callback"
    if function_name.startswith(CLI_CMD_PREFIXES):
        return "CLI dispatch"
    if function_name.startswith('__') and function_name.endswith('__'):
        return "magic method"
    return None
class _LayerReport(Protocol):
    blindspots: list
    def summary(self) -> dict: ...
@dataclass
class UnifiedBlindspotReport:
    project_root: str
    timestamp: str = field(default_factory=lambda: time.strftime(FMT_DATETIME))
    entries: list[UnifiedBlindspotEntry] = field(default_factory=list)
    metrics: dict[str, Any] = field(default_factory=dict)
    business_flow: Any = None
    _is_lib: bool | None = field(default=None, init=False, repr=False, compare=False)
    _facade_cache: dict[str, bool] = field(
        default_factory=dict, init=False, repr=False, compare=False)
    def is_library(self) -> bool:
        if self._is_lib is None:
            self._is_lib = is_library_project(self.project_root)
        return self._is_lib
    def _is_facade(self, filepath: str) -> bool:
        if filepath not in self._facade_cache:
            self._facade_cache[filepath] = is_facade_module(
                self.project_root, filepath)
        return self._facade_cache[filepath]
    def _emit_entry(self, position: _EntryPosition, *, blindspot_type: str,
                    severity: str, filepath: str, message: str,
                    suggestion: str, details: dict, confidence: str,
                    reason: str, is_lib: bool,
                    is_dead_code: bool) -> UnifiedBlindspotEntry:
        entry = UnifiedBlindspotEntry(
            level=position.level,
            blindspot_type=blindspot_type,
            severity=severity,
            filepath=filepath,
            line=position.line,
            end_line=position.end_line,
            name=position.name,
            message=message,
            suggestion=suggestion,
            details=details,
            confidence=confidence,
            confidence_reason=reason,
        )
        entry.numeric_confidence = _compute_numeric_confidence(
            level=position.level, blindspot_type=blindspot_type,
            severity=severity, is_library=is_lib,
            is_dead_code=is_dead_code)
        self.entries.append(entry)
        return entry
    def _add_layer_entries(self, level: str, report, position_of,
                           classify) -> None:
        self.metrics[level] = _merge_layer_metrics(
            self.metrics.get(level), report.summary())
        is_lib = self.is_library()
        for b in report.blindspots:
            sev_norm = resolve_numeric_severity(b.blindspot_type, b.severity)
            confidence, reason = classify(b)
            self._emit_entry(
                position_of(b),
                blindspot_type=b.blindspot_type,
                severity=sev_norm,
                filepath=b.filepath,
                message=b.message,
                suggestion=b.suggestion,
                details=b.to_dict(),
                confidence=confidence,
                reason=reason,
                is_lib=is_lib,
                is_dead_code=False,
            )
    def _add_layer_blindspots(self, level: str, report) -> None:
        self._add_layer_entries(
            level, report,
            position_of=lambda b: _EntryPosition(
                level, os.path.basename(b.filepath)),
            classify=lambda b: _classify_generic_confidence(
                self.is_library(), level=level, filepath=b.filepath,
                blindspot_type=b.blindspot_type, severity=b.severity))
    def add_function_blindspots(self, report: _LayerReport) -> None:
        self._add_layer_entries(
            "function", report,
            position_of=lambda b: _EntryPosition(
                "function", b.function_name, b.start_line,
                getattr(b, "end_line", 0)),
            classify=lambda b: _classify_confidence(
                b, is_lib=self.is_library(), is_facade=self._is_facade))
    def add_code_blindspots(self, reports) -> None:
        if isinstance(reports, (str, bytes)) or not hasattr(reports, "__iter__"):
            report_list = [reports]
        else:
            report_list = list(reports)
        is_lib = self.is_library()
        files_with_blindspots = 0
        total_blocks = 0
        dead_blocks = 0
        total_uncovered = 0
        total_executable = 0
        fp_count = 0
        for report in report_list:
            blocks = as_entry_list(getattr(report, "blocks", None))
            total_uncovered += numeric_or(
                getattr(report, "total_uncovered_lines", 0), 0)
            total_executable += numeric_or(
                getattr(report, "total_executable_lines", 0), 0)
            if not blocks:
                continue
            filepath = getattr(report, "filepath", "") or ""
            files_with_blindspots += 1
            total_blocks += len(blocks)
            dead_blocks += sum(1 for b in blocks if getattr(b, "is_dead_code", False))
            fp_count += self._emit_code_layer_entries(blocks, filepath, is_lib)
        self.metrics["code"] = _merge_layer_metrics(self.metrics.get("code"), {
            "total_files_with_blindspots": files_with_blindspots,
            "total_blocks": total_blocks,
            "dead_code_blocks": dead_blocks,
            "total_uncovered_lines": total_uncovered,
            "total_executable_lines": total_executable,
            "potential_false_positives": fp_count,
        })
    def _emit_code_layer_entries(self, blocks, filepath: str, is_lib: bool) -> int:
        fp_count = 0
        for b in blocks:
            entry = self._emit_code_block_entry(b, filepath, is_lib)
            if entry.confidence == FIELD_POTENTIAL_FP:
                fp_count += 1
        return fp_count
    def _emit_code_block_entry(self, block, filepath: str,
                               is_lib: bool) -> UnifiedBlindspotEntry:
        _b_dead = bool(getattr(block, "is_dead_code", False))
        _b_type = getattr(block, "block_type", "unknown")
        _b_name = getattr(block, "name", "")
        _b_sev = getattr(block, "severity", None)
        _b_start = getattr(block, "start_line", 0) or 0
        _b_end = getattr(block, "end_line", 0) or 0
        _b_uncovered = as_entry_list(getattr(block, "uncovered_lines", None))
        _b_triggers = as_entry_list(getattr(block, "trigger_conditions", None))
        _b_sibling = bool(getattr(block, "sibling_covered", False))
        _b_inputs = as_entry_list(getattr(block, "suggested_inputs", None))
        confidence, reason = _classify_generic_confidence(
            is_lib, level="code", filepath=filepath,
            blindspot_type=_b_type, severity=_b_sev, is_dead_code=_b_dead,
        )
        sev_norm = resolve_numeric_severity(_b_type, _b_sev)
        return self._emit_entry(
            _EntryPosition("code", _b_name, _b_start, _b_end),
            blindspot_type=_b_type,
            severity=sev_norm,
            filepath=filepath,
            message=f"{_b_name}（{_b_type}）有 {len(_b_uncovered)} 行未覆盖",
            suggestion=(_b_triggers[0] if _b_triggers else ""),
            details={
                "start_line": _b_start,
                "end_line": _b_end,
                "uncovered_lines": _b_uncovered,
                "is_dead_code": _b_dead,
                "sibling_covered": _b_sibling,
                "trigger_conditions": _b_triggers,
                "suggested_inputs": _b_inputs,
            },
            confidence=confidence,
            reason=reason,
            is_lib=is_lib,
            is_dead_code=_b_dead,
        )
    def add_class_blindspots(self, report: _LayerReport) -> None:
        self._add_layer_entries(
            "class", report,
            position_of=lambda b: _EntryPosition(
                "class", b.class_name, b.start_line,
                getattr(b, "end_line", 0)),
            classify=lambda b: _classify_class_confidence(
                self.project_root, b, is_lib=self.is_library()))
    def add_confirmed_entry(self, source: dict, *, blindspot_type: str,
                            confidence_reason: str) -> UnifiedBlindspotEntry:
        entry = UnifiedBlindspotEntry(
            level="code",
            blindspot_type=blindspot_type,
            severity=resolve_numeric_severity(
                blindspot_type, source.get("severity")),
            filepath=source.get("filepath", ""),
            line=source.get("line", 0),
            name=source.get("name", ""),
            message=source.get("message", ""),
            suggestion=source.get("suggestion", ""),
            confidence="confirmed",
            confidence_reason=confidence_reason,
            numeric_confidence=_CONFIRMED_ENTRY_CONFIDENCE,
        )
        self.entries.append(entry)
        return entry
    def collect_layer_reports(self, layer_results: dict) -> None:
        for layer, log_template in _LAYER14_REPORT_SPECS:
            layer_report = layer_results.get(layer)
            if not layer_report:
                continue
            try:
                if layer == "func":
                    self.add_function_blindspots(layer_report)
                elif layer == "class":
                    self.add_class_blindspots(layer_report)
                else:
                    self._add_layer_blindspots(layer, layer_report)
            except LAYER_DEGRADE_EXC as exc:
                logger.warning("%s 层报告汇聚失败(该层降级): %s", layer, exc)
                continue
            try:
                summary = layer_report.summary()
                log_line = "       " + log_template.format(**summary)
            except LAYER_DEGRADE_EXC as exc:
                logger.warning("%s 层日志摘要失败(条目已汇聚): %s", layer, exc)
                continue
            logger.info("%s", log_line)
    def log_summary(self, project_root: str, syn_errors) -> None:
        s = self.summary()
        logger.info("\n%s", "=" * 60)
        logger.info("[盲区] 五层盲区扫描报告")
        logger.info("%s", "=" * 60)
        logger.info("  项目: %s", project_root)
        logger.info("  总盲区数: %s", s.get(FIELD_TOTAL_BLINDSPOTS))
        if s.get("by_confidence"):
            fp = (s.get("by_confidence") or {}).get(FIELD_POTENTIAL_FP, 0)
            if fp > 0:
                logger.info("  疑似误报: %d (%d%%)", fp,
                            fp * 100 // max(s.get(FIELD_TOTAL_BLINDSPOTS, 1), 1))
        for sev in ["critical", "high", "medium", "low", "info"]:
            count = (s.get("by_severity") or {}).get(sev, 0)
            if count:
                logger.info("    %s: %d", sev.upper(), count)
        logger.info("  层级: %s", s.get("by_level", {}))
        if syn_errors:
            logger.info("  语法错误: %d 个文件", len(syn_errors))
    def filter_by_whitelist(self, whitelist) -> int:
        if not whitelist:
            return 0
        return _filter_report_entries(
            self, lambda e: _is_whitelisted(_entry_name(e), whitelist),
            "Whitelist", "白名单")
    def filter_by_ignore_decorators(self, ignored_decorators,
                                    call_graph=None) -> int:
        if not ignored_decorators:
            return 0
        norm = {d.lstrip("@") for d in ignored_decorators
                if isinstance(d, str) and d}
        if not norm:
            return 0
        norm_simple = {n.rsplit(".", 1)[-1] for n in norm}
        funcs = (getattr(call_graph, "functions", {})
                 if call_graph is not None else {})
        if not isinstance(funcs, dict):
            funcs = {}
        by_simple = _unambiguous_simple_node_map(funcs)
        return _filter_report_entries(
            self,
            lambda e: _entry_has_ignored_decorator(
                e, funcs, by_simple, norm, norm_simple),
            "IgnoreDecorators", "忽略装饰器")
    def apply_clustering(self, call_graph, diag_ctx=None) -> None:
        try:
            if self.entries and call_graph is not None:
                logger.info("[盲区] 7.6/7 条目聚类降噪...")
                _entries = self.entries
                _, _collapse = detect_pattern_collapse(_entries)
                _, _prox = detect_proximity_clustering(_entries)
                _, _struct = cluster_by_structural_similarity(
                    _entries, diag_ctx=diag_ctx, project_root=self.project_root)
                self.metrics["clustering"] = {
                    "pattern_collapse": _collapse,
                    "proximity_clustering": _prox,
                    "structural_clustering": _struct,
                }
                logger.info(
                    "       聚类: 模式崩溃组=%d(影响%d条), 邻近聚类=%d组, 结构聚类=%d组",
                    _collapse.get("collapsed_groups", 0),
                    _collapse.get("affected_entries", 0),
                    _prox.get("clusters", 0),
                    _struct.get("clusters", 0),
                )
            else:
                logger.info("[盲区] 7.6/7 条目聚类降噪... 跳过（需调用图与条目）")
        except LAYER_DEGRADE_EXC as exc:
            logger.debug("聚类降噪跳过: %s", exc)
    def summary(self) -> dict:
        result = _summary_core_counters(self)
        _summary_attach_business_flows(self, result)
        conf_count = _summary_confidence_distribution(self, result)
        _summary_attach_fp_adjusted_severity(self, result)
        _summary_attach_effective_total(self, result, conf_count)
        _summary_attach_clustering_pass(self, result)
        _summary_attach_reliability_weighted(self, result)
        return result
    def to_json(self, filepath: str | None = None) -> str:
        data = {
            "summary": self.summary(),
            "entries": [e.to_dict() for e in self.entries],
        }
        json_str = serialize_json(data, indent=2)
        if filepath:
            write_json_artifact(filepath, data, indent=2)
        return json_str
    def to_report_data(self) -> dict:
        entries_dicts = [
            e.to_dict() if hasattr(e, "to_dict")
            else (vars(e) if hasattr(e, "__dict__") else {})
            for e in self.entries
        ]
        summary_data = self.summary()
        report_data = {
            "summary": summary_data,
            "entries": entries_dicts,
            "metrics": self.metrics,
            "project_root": self.project_root,
            "timestamp": self.timestamp,
        }
        business_flows = summary_data.get("business_flows")
        if business_flows:
            report_data["business_flows"] = business_flows
        return report_data
def _entry_category(blindspot_type: str) -> str:
    if blindspot_type in _DEFENSIVE_TYPES:
        return CATEGORY_DEFENSIVE
    if blindspot_type in _BOUNDARY_TYPES:
        return CATEGORY_BOUNDARY
    return CATEGORY_CORE
def _summary_core_counters(report) -> dict:
    sev_count = Counter()
    level_count = Counter()
    type_count = Counter()
    category_count = Counter()
    cat_sev = {cat: Counter() for cat in _CATEGORY_ORDER}
    for e in report.entries:
        _btype = _hashable_key(e.blindspot_type)
        _sev = _hashable_key(resolve_numeric_severity(
            _btype if isinstance(_btype, str) else "", e.severity))
        sev_count[_sev] += 1
        level_count[_hashable_key(e.level)] += 1
        type_count[_btype] += 1
        cat = _entry_category(_btype)
        category_count[cat] += 1
        cat_sev[cat][_sev] += 1
    by_category_severity = {
        cat: dict(ctr.most_common()) for cat, ctr in cat_sev.items() if ctr
    }
    return {
        "project": report.project_root,
        "timestamp": report.timestamp,
        FIELD_TOTAL_BLINDSPOTS: len(report.entries),
        "by_severity": dict(sev_count.most_common()),
        "by_level": dict(level_count.most_common()),
        "by_type": dict(type_count.most_common()),
        "by_category": dict(category_count.most_common()),
        "by_category_severity": by_category_severity,
        "metrics": report.metrics,
    }
def _summary_attach_business_flows(report, result: dict) -> None:
    if report.business_flow is not None:
        try:
            _bf_summary = report.business_flow.summary()
            if isinstance(_bf_summary, dict):
                result["business_flows"] = _bf_summary
        except Exception as exc:  # noqa: BLE001
            logger.debug("business_flow summary 提取失败: %s", exc)
def _summary_confidence_distribution(report, result: dict) -> Counter:
    conf_count = Counter()
    for e in report.entries:
        _conf = _hashable_key(e.confidence)
        if _conf != "unknown":
            conf_count[_conf] += 1
    if conf_count:
        result["by_confidence"] = dict(conf_count.most_common())
        total_conf = sum(conf_count.get(_k, 0) for _k in _KNOWN_CONF) or 1
        result["precision_estimate"] = {
            pct_key: round(conf_count.get(label, 0) / total_conf * 100, 1)
            for label, pct_key in _KNOWN_CONF_KEYS.items()
        }
    return conf_count
def _summary_attach_fp_adjusted_severity(report, result: dict) -> None:
    fp_severity_raw: Counter = Counter()
    adjusted: Counter = Counter()
    for e in report.entries:
        if e.confidence == "external_api":
            continue
        _btype = _hashable_key(getattr(e, "blindspot_type", ""))
        _sev = _hashable_key(resolve_numeric_severity(
            _btype if isinstance(_btype, str) else "",
            getattr(e, "severity", None)))
        if e.confidence == FIELD_POTENTIAL_FP:
            fp_severity_raw[_sev] += 1
        else:
            adjusted[_sev] += 1
    for sev, cnt in fp_severity_raw.items():
        adjusted[_downgrade_severity(sev)] += cnt
    result["by_severity_adjusted"] = dict(adjusted.most_common())
    if fp_severity_raw:
        result["fp_severity_raw"] = dict(fp_severity_raw.most_common())
def _summary_attach_effective_total(report, result: dict, conf_count: Counter) -> None:
    unknown_cnt = len(report.entries) - sum(
        conf_count.get(_k, 0) for _k in _KNOWN_CONF)
    result["effective_total"] = (
        conf_count.get("confirmed", 0)
        + conf_count.get("confirmed_untested", 0)
        + unknown_cnt
        + round(conf_count.get(FIELD_POTENTIAL_FP, 0) / 2)
    )
def _summary_attach_clustering_pass(report, result: dict) -> None:
    _clustering = report.metrics.get("clustering")
    if isinstance(_clustering, dict):
        for _ck in ("pattern_collapse", "proximity_clustering", "structural_clustering"):
            _cv = _clustering.get(_ck)
            if isinstance(_cv, dict) and _cv:
                result[_ck] = _cv
def _summary_attach_reliability_weighted(report, result: dict) -> None:
    if any(getattr(e, "reliability_score", None) is not None
           for e in report.entries):
        try:
            _is_lib = report.is_library()
            result["reliability_weighted"] = compute_reliability_weighted_penalty(
                report.entries,
                _is_lib,
                report.metrics.get(CAT_CROSS_VALIDATION),
            )
        except Exception as _rw_exc:  # noqa: BLE001
            logger.debug("reliability_weighted 预估失败: %s", _rw_exc)
_CONFIDENCE_PENALTY_WEIGHTS = {
    "confirmed": 1.0,
    "confirmed_untested": 1.0,
    FIELD_POTENTIAL_FP: 0.5,
    "external_api": 0.0,
    "unknown": 1.0,
}
def _confidence_penalty_weight(conf: str, skip_external_api: bool) -> tuple[float, bool]:
    if conf == "unknown" and skip_external_api:
        return 0.2, True
    return _CONFIDENCE_PENALTY_WEIGHTS.get(conf, 1.0), False
def _resolve_penalty_exemption(cv_pm: dict | None, is_library: bool) -> bool:
    if not isinstance(cv_pm, dict):
        return False
    cv_dead = as_number(cv_pm.get("confirmed_dead"), 0)
    cv_ext_api = as_number(cv_pm.get("external_api_excluded"), 0)
    return bool(is_library and (cv_dead == 0 or cv_ext_api > 0))
def _entry_penalty(entry, skip_external_api: bool) -> tuple[float, bool, bool] | None:
    conf = getattr(entry, "confidence", "unknown")
    if skip_external_api and conf == "external_api":
        return None
    sev = resolve_numeric_severity(getattr(entry, "blindspot_type", ""),
                                   getattr(entry, "severity", "low"))
    rel = finite_float_or_none(getattr(entry, "reliability_score", 0.5))
    rel = 0.5 if rel is None else min(1.0, max(0.0, rel))
    weight, unknown_retained = _confidence_penalty_weight(
        conf, skip_external_api)
    details = getattr(entry, "details", None)
    cc = numeric_or(
        details.get("cyclomatic_complexity", 0)
        if isinstance(details, dict) else 0, 0)
    high_cc = cc > Thresholds.CYCLOMATIC_RECOMMEND
    penalty_severity = _PENALTY_SEVERITY_BY_NAME.get(sev, sev)
    return (severity_penalty_weight(penalty_severity, default=1) * rel * weight,
            unknown_retained, high_cc)
def compute_reliability_weighted_penalty(entries: list | None, is_library: bool, cv_pm: dict | None) -> dict:
    skip_external_api = _resolve_penalty_exemption(cv_pm, is_library)
    weighted_penalty = 0.0
    reliability_entries = 0
    skipped_external_api = 0
    unknown_retained = 0
    high_complexity_count = 0
    for e in entries or []:
        contribution = _entry_penalty(e, skip_external_api)
        if contribution is None:
            skipped_external_api += 1
            continue
        penalty, retained, high_cc = contribution
        weighted_penalty += penalty
        reliability_entries += 1
        if retained:
            unknown_retained += 1
        if high_cc:
            high_complexity_count += 1
    return {
        "weighted_penalty": round(weighted_penalty, 2),
        "reliability_entries": reliability_entries,
        "skipped_external_api": skipped_external_api,
        "unknown_retained": unknown_retained,
        "high_complexity_count": high_complexity_count,
        "external_api_exempt": skip_external_api,
    }
_PATTERN_COLLAPSE_THRESHOLD = 3
_CONFIRMED_CONFIDENCES = ('confirmed', 'confirmed_untested')
_PROXIMITY_LINE_THRESHOLD = 15
_MAJORITY_VOTE_RATIO = 0.6
_COLLAPSE_RESTORE_RATIO = 0.5
_DETAIL_SAMPLE_LIMIT = 20
_CLUSTER_SOURCE_MARKS: dict[str, tuple[str, str]] = {
    "structural": ('_structural_downgraded', '_structural_restored'),
    "proximity": ('_proximity_downgraded', '_proximity_restored'),
    "collapse": ('_pattern_collapse', '_pattern_collapse_restored'),
}
def _read_confidence(entry) -> str:
    return safe_text(getattr(entry, 'confidence', 'unknown'))
def _assign_confidence(entry, confidence: str) -> None:
    entry.confidence = confidence
    if confidence == FIELD_POTENTIAL_FP:
        entry.numeric_confidence = _POTENTIAL_FP_CONFIDENCE
def _entry_filepath(entry) -> str:
    raw = getattr(entry, 'filepath', '') or getattr(entry, 'file', '')
    return safe_text(raw)
def _entry_blindspot_type(entry) -> str:
    raw = getattr(entry, 'blindspot_type', '') or getattr(entry, 'type', '')
    return safe_text(raw)
def _entry_line(entry) -> int:
    line = normalize_line_no(getattr(entry, 'line', 0))
    return line or normalize_line_no(getattr(entry, 'lineno', 0))
def _is_confirmed(entry) -> bool:
    return _read_confidence(entry) in _CONFIRMED_CONFIDENCES
def _count_confirmed(entries, *, include_untested: bool = False) -> int:
    if include_untested:
        return sum(1 for e in entries if _is_confirmed(e))
    return sum(1 for e in entries if _read_confidence(e) == 'confirmed')
def _count_downgraded(entries) -> int:
    return sum(1 for e in entries if _read_confidence(e) == FIELD_POTENTIAL_FP)
def _cluster_detail(members, **extra) -> dict:
    return {
        **extra,
        "cluster_size": len(members),
        "confirmed": _count_confirmed(members),
        "downgraded": _count_downgraded(members),
    }
def _collapse_target_confidence(old_conf):
    if old_conf == 'confirmed':
        return 'confirmed_untested'
    if old_conf == 'unknown':
        return FIELD_POTENTIAL_FP
    return old_conf
def _group_entries(entries, keyfunc):
    groups = defaultdict(list)
    for entry in entries:
        groups[keyfunc(entry)].append(entry)
    return groups
def _collapse_group_key(entry):
    return (_entry_filepath(entry), _entry_blindspot_type(entry))
def _collapse_eligible_groups(groups):
    return [(key, entries) for key, entries in groups.items()
            if len(entries) >= _PATTERN_COLLAPSE_THRESHOLD and all(key)]
def _pattern_collapse_downgrade(groups) -> int:
    collapsed = 0
    for _key, entries in _collapse_eligible_groups(groups):
        group_affected = 0
        for e in entries:
            old_conf = _read_confidence(e)
            new_conf = _collapse_target_confidence(old_conf)
            if new_conf != old_conf:
                e._pre_collapse_confidence = old_conf
                e._pre_collapse_numeric_confidence = getattr(
                    e, 'numeric_confidence', None)
                _assign_confidence(e, new_conf)
                e._pattern_collapse = True
                group_affected += 1
        if group_affected:
            collapsed += 1
    return collapsed
def _restore_majority_confirmed_group(entries):
    confirmed_in_group = _count_confirmed(entries, include_untested=True)
    collapsed_in_group = sum(
        1 for e in entries if getattr(e, '_pattern_collapse', False))
    if (not collapsed_in_group
            or confirmed_in_group <= len(entries) * _COLLAPSE_RESTORE_RATIO):
        return 0
    restored = 0
    for e in entries:
        if not getattr(e, '_pattern_collapse', False):
            continue
        e.confidence = getattr(e, '_pre_collapse_confidence',
                               _read_confidence(e))
        e.numeric_confidence = getattr(
            e, '_pre_collapse_numeric_confidence',
            getattr(e, 'numeric_confidence', None))
        e._pattern_collapse_restored = True
        restored += 1
    return restored
def _pattern_collapse_restore(groups):
    restored = 0
    for _key, entries in _collapse_eligible_groups(groups):
        restored += _restore_majority_confirmed_group(entries)
    return restored
def _collapse_group_detail(fpath, btype, entries) -> dict:
    before_counts = Counter()
    after_counts = Counter()
    affected_count = 0
    restored_count = 0
    for e in entries:
        _pre = getattr(e, '_pre_collapse_confidence', None)
        before_counts[_pre if _pre is not None else _read_confidence(e)] += 1
        after_counts[_read_confidence(e)] += 1
        if getattr(e, '_pattern_collapse', False):
            affected_count += 1
        if getattr(e, '_pattern_collapse_restored', False):
            restored_count += 1
    return {
        "file": fpath,
        "type": btype,
        "count": len(entries),
        "affected": affected_count,
        "confidence_before": dict(before_counts),
        "confidence_after": dict(after_counts),
        "restored": restored_count,
    }
def _pattern_collapse_details(groups):
    return [_collapse_group_detail(fpath, btype, entries)
            for (fpath, btype), entries in _collapse_eligible_groups(groups)
            if any(getattr(e, '_pattern_collapse', False) for e in entries)]
_COLLAPSE_RUN_MARKS = (
    "_pattern_collapse", "_pattern_collapse_restored",
    "_pre_collapse_confidence", "_pre_collapse_numeric_confidence",
)
def _reset_collapse_run_marks(entries) -> None:
    for entry in entries:
        if (getattr(entry, "_pattern_collapse", False)
                and not getattr(entry, "_pattern_collapse_restored", False)):
            entry.confidence = getattr(
                entry, "_pre_collapse_confidence", _read_confidence(entry))
            if hasattr(entry, "_pre_collapse_numeric_confidence"):
                entry.numeric_confidence = entry._pre_collapse_numeric_confidence
        for mark in _COLLAPSE_RUN_MARKS:
            if hasattr(entry, mark):
                delattr(entry, mark)
def _reset_cluster_run_marks(entries, source: str) -> None:
    downgraded_mark, restored_mark = _CLUSTER_SOURCE_MARKS[source]
    for entry in entries:
        if (getattr(entry, downgraded_mark, False)
                and not getattr(entry, restored_mark, False)
                and _read_confidence(entry) == FIELD_POTENTIAL_FP):
            original = getattr(entry, "_pre_clustering_confidence", None)
            if original is not None:
                entry.confidence = original
            if hasattr(entry, "_pre_clustering_numeric_confidence"):
                entry.numeric_confidence = entry._pre_clustering_numeric_confidence
        for mark in (downgraded_mark, restored_mark):
            if hasattr(entry, mark):
                delattr(entry, mark)
        other_channel_active = any(
            other_source != source
            and other_source != "collapse"
            and getattr(entry, marks[0], False)
            for other_source, marks in _CLUSTER_SOURCE_MARKS.items())
        if not other_channel_active:
            if hasattr(entry, "_pre_clustering_confidence"):
                delattr(entry, "_pre_clustering_confidence")
            if hasattr(entry, "_pre_clustering_numeric_confidence"):
                delattr(entry, "_pre_clustering_numeric_confidence")
def detect_pattern_collapse(bs_entries: list) -> tuple[list, dict]:
    if not bs_entries:
        return bs_entries, {"collapsed_groups": 0, "affected_entries": 0,
                            "restored_entries": 0, "details": []}
    _reset_collapse_run_marks(bs_entries)
    groups = _group_entries(bs_entries, _collapse_group_key)
    _pattern_collapse_downgrade(groups)
    restored = _pattern_collapse_restore(groups)
    details = _pattern_collapse_details(groups)
    net_details = [d for d in details if d["affected"] > d["restored"]]
    net_affected = sum(d["affected"] - d["restored"] for d in net_details)
    return bs_entries, {
        "collapsed_groups": len(net_details),
        "affected_entries": net_affected,
        "restored_entries": restored,
        "threshold": _PATTERN_COLLAPSE_THRESHOLD,
        "details": details[:_DETAIL_SAMPLE_LIMIT],
    }
def _downgraded_source(e) -> tuple[str, str] | None:
    for marks in _CLUSTER_SOURCE_MARKS.values():
        if getattr(e, marks[0], False):
            return marks
    return None
def _restore_cluster_entry(e) -> bool:
    if _read_confidence(e) != FIELD_POTENTIAL_FP:
        return False
    marks = _downgraded_source(e)
    if marks is None:
        return False
    original = getattr(e, '_pre_clustering_confidence', None)
    if original is None:
        original = getattr(e, '_pre_collapse_confidence', 'unknown')
    if hasattr(e, '_pre_clustering_numeric_confidence'):
        original_numeric = e._pre_clustering_numeric_confidence
    else:
        original_numeric = getattr(
            e, '_pre_collapse_numeric_confidence',
            getattr(e, 'numeric_confidence', None))
    e.confidence = original
    e.numeric_confidence = original_numeric
    setattr(e, marks[1], True)
    return True
def _downgrade_confirmed_members(members, source: str) -> int:
    marker = _CLUSTER_SOURCE_MARKS[source][0]
    downgraded = 0
    for e in members:
        if _read_confidence(e) != 'confirmed':
            continue
        e._pre_clustering_confidence = 'confirmed'
        e._pre_clustering_numeric_confidence = getattr(
            e, 'numeric_confidence', None)
        _assign_confidence(e, FIELD_POTENTIAL_FP)
        setattr(e, marker, True)
        downgraded += 1
    return downgraded
def _majority_vote_adjust(members: list, source: str = "proximity") -> int:
    confirmed_count = _count_confirmed(members)
    downgraded_count = _count_downgraded(members)
    total = len(members)
    if downgraded_count > total * _MAJORITY_VOTE_RATIO and confirmed_count > 0:
        return _downgrade_confirmed_members(members, source)
    if confirmed_count > total * _MAJORITY_VOTE_RATIO and downgraded_count > 0:
        return sum(1 for e in members if _restore_cluster_entry(e))
    return 0
def _greedy_proximity_clusters(entries):
    if not entries:
        return []
    sorted_entries = sorted(entries, key=_entry_line)
    clusters = []
    current_cluster = [sorted_entries[0]]
    current_max_line = _entry_line(sorted_entries[0])
    for e in sorted_entries[1:]:
        e_line = _entry_line(e)
        if e_line - current_max_line <= _PROXIMITY_LINE_THRESHOLD:
            current_cluster.append(e)
            current_max_line = max(current_max_line, e_line)
        else:
            if len(current_cluster) >= 2:
                clusters.append(current_cluster)
            current_cluster = [e]
            current_max_line = e_line
    if len(current_cluster) >= 2:
        clusters.append(current_cluster)
    return clusters
def _process_proximity_file(fpath, entries):
    known = [e for e in entries if _entry_line(e) > 0]
    if len(known) < 2:
        return 0, 0, []
    clusters = _greedy_proximity_clusters(known)
    cluster_count = 0
    adjusted = 0
    file_details = []
    for cluster in clusters:
        cluster_count += 1
        adjusted += _majority_vote_adjust(cluster)
        file_details.append(_cluster_detail(
            cluster,
            file=fpath,
            line_range=f"{_entry_line(cluster[0])}-{_entry_line(cluster[-1])}",
        ))
    return cluster_count, adjusted, file_details
def detect_proximity_clustering(bs_entries: list) -> tuple[list, dict]:
    if not bs_entries:
        return bs_entries, {"clusters": 0, "adjusted_entries": 0, "details": []}
    _reset_cluster_run_marks(bs_entries, "proximity")
    file_groups = _group_entries(bs_entries, _entry_filepath)
    total_clusters = 0
    total_adjusted = 0
    details = []
    for fpath, entries in file_groups.items():
        if not fpath or len(entries) < 2:
            continue
        file_clusters, file_adjusted, file_details = _process_proximity_file(
            fpath, entries)
        total_clusters += file_clusters
        total_adjusted += file_adjusted
        details.extend(file_details)
    return bs_entries, {
        "clusters": total_clusters,
        "adjusted_entries": total_adjusted,
        "proximity_threshold": _PROXIMITY_LINE_THRESHOLD,
        "details": details[:_DETAIL_SAMPLE_LIMIT],
    }
def _compute_fingerprints_and_group(bs_entries, tree_cache, profiles_cache, diag_ctx=None,
                                     project_root=None):
    fp_groups = {}
    for e in bs_entries:
        fp = structural_fingerprint(
            _entry_filepath(e), _entry_line(e), _entry_blindspot_type(e),
            tree_cache, profiles_cache, diag_ctx, project_root)
        if fp:
            fp_groups.setdefault(fp, []).append(e)
    return fp_groups
def _apply_majority_voting(fp_groups):
    total_clusters = 0
    total_adjusted = 0
    details = []
    for fp, members in fp_groups.items():
        if len(members) < 2:
            continue
        total_clusters += 1
        total_adjusted += _majority_vote_adjust(members, source="structural")
        details.append(_cluster_detail(members, fingerprint=fp))
    return total_clusters, total_adjusted, details
def cluster_by_structural_similarity(bs_entries: list, diag_ctx=None, project_root=None) -> tuple[list, dict]:
    if not bs_entries:
        return bs_entries, {"clusters": 0, "adjusted_entries": 0, "details": []}
    _reset_cluster_run_marks(bs_entries, "structural")
    tree_cache = {}
    profiles_cache = {}
    fp_groups = _compute_fingerprints_and_group(
        bs_entries, tree_cache, profiles_cache, diag_ctx, project_root)
    total_clusters, total_adjusted, details = _apply_majority_voting(fp_groups)
    return bs_entries, {
        "clusters": total_clusters,
        "adjusted_entries": total_adjusted,
        "details": details[:_DETAIL_SAMPLE_LIMIT],
    }
def _path_text(value) -> str | None:
    try:
        return os.fsdecode(os.fspath(value))
    except TypeError:  # jwsgj:silent-ok
        return None
def _required_project_root(project_root) -> str:
    path = _path_text(project_root)
    if path is None or not path.strip():
        raise ValueError(f"Invalid project_root: {project_root!r}")
    return path
def _as_path_list(value) -> list:
    if not value:
        return []
    if isinstance(value, (str, bytes, os.PathLike)):
        return [value]
    try:
        return list(value)
    except TypeError:  # jwsgj:silent-ok
        return []
def load_whitelist(whitelist_files: list[str] | str | None=None) -> set[str]:
    whitelist = set()
    for wf in _as_path_list(whitelist_files):
        path = _path_text(wf)
        if path is None:
            logger.debug("load_whitelist: 跳过非路径项: %r", wf)
            continue
        if os.path.isfile(path):
            whitelist |= _read_whitelist_file(path)
    return whitelist
def _read_whitelist_file(path: str) -> set[str]:
    names = set()
    try:
        with open(path, encoding="utf-8-sig") as f:
            for raw_line in f:
                line = raw_line.strip()
                if line and not line.startswith("#"):
                    names.add(line.split()[0])
    except (OSError, ValueError) as e:
        logger.debug("load_whitelist: suppressed error: %s", e, exc_info=True)
    return names
def load_ignore_decorators(ignore_decorators: list[str] | str | None=None) -> set[str]:
    if not ignore_decorators:
        return set()
    if isinstance(ignore_decorators, str):
        raw_items = [ignore_decorators]
    else:
        try:
            raw_items = list(ignore_decorators)
        except TypeError:  # jwsgj:silent-ok
            logger.debug(
                "load_ignore_decorators: 入参不可迭代，按空集合处理: %r",
                ignore_decorators)
            return set()
    normalized = (_normalize_decorator_name(raw) for raw in raw_items)
    return {name for name in normalized if name is not None}
def _normalize_decorator_name(raw: object) -> str | None:
    if not isinstance(raw, str):
        return None
    name = raw.strip()
    if not name:
        return None
    return name if name.startswith("@") else "@" + name
def _is_whitelisted(name: str, whitelist: set[str]) -> bool:
    if not whitelist or not name:
        return False
    if name in whitelist:
        return True
    parts = name.split(".")
    return any(".".join(parts[i:]) in whitelist for i in range(1, len(parts)))
def _entry_name(entry: object) -> str:
    name = getattr(entry, "name", "")
    return name if isinstance(name, str) else ""
def _filter_report_entries(report, should_drop, tag: str, label: str) -> int:
    entries = getattr(report, "entries", None)
    if not entries:
        return 0
    kept = [e for e in entries if not should_drop(e)]
    filtered = len(entries) - len(kept)
    if filtered:
        report.entries = kept
        logger.info("  [%s] 过滤 %d 个%s盲区", tag, filtered, label)
    return filtered
def _resolve_entry_decorators(entry, fnode) -> list[str]:
    decs = _decorator_list(getattr(fnode, "decorators", None))
    if not decs:
        details = getattr(entry, "details", None)
        raw = details.get("decorators") if isinstance(details, dict) else None
        decs = _decorator_list(raw)
    return decs
def _decorator_list(raw) -> list[str]:
    if isinstance(raw, str):
        raw = [raw]
    if not isinstance(raw, (list, tuple)):
        return []
    normalized = (_normalize_decorator_name(item) for item in raw)
    return [name[1:] for name in normalized if name is not None]
def _unambiguous_simple_node_map(funcs: dict) -> dict:
    simple_holders: dict[str, list] = {}
    for fk, fn in funcs.items():
        if not isinstance(fk, str):
            continue
        simple_holders.setdefault(fk.split(".")[-1], []).append(fn)
    return {
        s: holders[0]
        for s, holders in simple_holders.items() if len(holders) == 1
    }
def _entry_has_ignored_decorator(e, funcs: dict, by_simple: dict,
                                 norm: set, norm_simple: set) -> bool:
    e_name = _entry_name(e)
    fnode = (funcs.get(e_name)
             or by_simple.get(e_name.split(".")[-1] if e_name else ""))
    decs = _resolve_entry_decorators(e, fnode)
    return any(d in norm or d.rsplit(".", 1)[-1] in norm_simple for d in decs)
@dataclass
class BlindspotSummary:
    raw: dict
    bs_count: int
    code_level_aggr: dict
    confirmed_entries: list
    confirmed_total: int
def _code_metrics_numeric(raw: dict) -> tuple[dict, float, float]:
    _raw_metrics = raw.get("metrics")
    _cov_metrics = (_raw_metrics.get("code")
                    if isinstance(_raw_metrics, dict) else None)
    if not isinstance(_cov_metrics, dict):
        _cov_metrics = {}
    _exec_lines = as_number(_cov_metrics.get("total_executable_lines", 0), 0)
    _uncov_lines = as_number(_cov_metrics.get("total_uncovered_lines", 0), 0)
    return _cov_metrics, _exec_lines, _uncov_lines
def _compute_coverage_pct(raw: dict) -> float:
    _, _exec_lines, _uncov_lines = _code_metrics_numeric(raw)
    if _exec_lines > 0:
        return round(min(_exec_lines,
                         max(0.0, _exec_lines - _uncov_lines))
                     / _exec_lines * 100, 1)
    return as_number(raw.get("coverage_pct", 0), 0)
def _extract_clustering_audit(raw: dict) -> dict:
    _clustering = dict_or_empty(
        dict_or_empty(raw.get("metrics")).get("clustering"))
    if not _clustering:
        return {}
    _cl_summary: dict = {}
    for _cl_key in ("pattern_collapse", "proximity_clustering",
                    "structural_clustering"):
        _cl_val = dict_or_empty(_clustering.get(_cl_key))
        if _cl_val:
            _cl_summary[_cl_key] = _primitive_only(_cl_val)
    return _cl_summary
def _primitive_only(values: dict) -> dict:
    return {key: value for key, value in values.items()
            if isinstance(value, (int, float, str, bool))}
def _coerce_blindspot_entry(bf):
    _to_dict_fn = getattr(bf, "to_dict", None)
    if not callable(_to_dict_fn):
        return False, None
    try:
        return True, _to_dict_fn()
    except Exception as _td_e:  # noqa: BLE001
        logger.warning("[CGA] 盲点条目序列化失败（丢弃1条）: %s", _td_e)
        return False, None
def _bump_code_aggregate(bf: dict, aggr: dict) -> None:
    _key = tuple(
        "" if _v is None else str(_v)
        for _v in (bf.get("blindspot_type"),
                   bf.get("severity"),
                   bf.get("confidence")))
    aggr[_key] = aggr.get(_key, 0) + 1
def _append_confirmed_entry(bf: dict, entries: list) -> None:
    if len(entries) >= 50:
        return
    entries.append({
        "type": str(bf.get("blindspot_type") or ""),
        "severity": str(bf.get("severity") or ""),
        "file": str(bf.get("filepath") or ""),
        "line": as_number(bf.get("line"), 0),
        "name": str(bf.get("name") or "")[:80],
        "message": str(bf.get("message") or "")[:120],
    })
def _collect_code_blindspot(bf: dict, aggr: dict, entries: list,
                            all_findings: list) -> int:
    _bump_code_aggregate(bf, aggr)
    if bf.get("confidence") != "confirmed":
        return 0
    _append_confirmed_entry(bf, entries)
    canonical_severity = resolve_numeric_severity(
        str(bf.get("blindspot_type") or ""), bf.get("severity"))
    if canonical_severity in ("high", "critical"):
        _hi = dict(bf)
        _hi["source"] = "CGA"
        all_findings.append(_hi)
    return 1
def collect_blindspot_entries(
    bs_findings, all_findings: list,
) -> tuple[dict, list, int, int]:
    _code_level_aggr: dict[tuple, int] = {}
    _dropped_unserializable = 0
    _confirmed_entries: list[dict] = []
    _confirmed_total = 0
    for raw_bf in bs_findings:
        bf = raw_bf
        if not isinstance(bf, (dict, str)):
            _converted, bf = _coerce_blindspot_entry(bf)
            if not _converted or not isinstance(bf, (dict, str)):
                _dropped_unserializable += 1
                continue
        if isinstance(bf, dict):
            if bf.get("level") != "code":
                all_findings.append({**bf, "source": "CGA"})
                continue
            _confirmed_total += _collect_code_blindspot(
                bf, _code_level_aggr, _confirmed_entries, all_findings)
            continue
        if isinstance(bf, str):
            all_findings.append({
                "rule_id": "BLINDSPOT",
                "message": bf,
                "source": "CGA",
            })
    return (_code_level_aggr, _confirmed_entries,
            _confirmed_total, _dropped_unserializable)
def apply_blindspot_summary(graph_summary: dict,
                            summary: BlindspotSummary) -> None:
    graph_summary["blindspots"] = summary.bs_count
    graph_summary["coverage_pct"] = _compute_coverage_pct(summary.raw)
    if summary.confirmed_total:
        graph_summary["blindspot_confirmed_entries"] = {
            "total": summary.confirmed_total,
            "truncated": (summary.confirmed_total
                          > len(summary.confirmed_entries)),
            "entries": summary.confirmed_entries,
        }
    if summary.code_level_aggr:
        graph_summary["blindspot_code_level_aggregated"] = {
            "|".join(k): v
            for k, v in sorted(summary.code_level_aggr.items())
        }
    _cl_summary = _extract_clustering_audit(summary.raw)
    if _cl_summary:
        graph_summary["blindspot_clustering"] = _cl_summary
_EVIDENCE_WEIGHTS = {"static": 0.85, "dynamic": 0.25, "baseline": 0.10}
def _compute_reliability_score(numeric_confidence: float,
                               evidence_sources: set | None = None) -> float:
    if not evidence_sources:
        evidence_sources = {"static"}
    base = _EVIDENCE_WEIGHTS["static"] if "static" in evidence_sources else 0.0
    for src in evidence_sources - {"static"}:
        base += _EVIDENCE_WEIGHTS.get(src, 0)
    sufficiency = min(1.0, base)
    return round((numeric_confidence / 100.0) * sufficiency, 4)
def _confidence_to_reliability_category(reliability: float) -> str:
    if reliability >= _RELIABILITY_CONFIRMED_MIN:
        return "confirmed"
    if reliability >= _RELIABILITY_POTENTIAL_FP_MIN:
        return FIELD_POTENTIAL_FP
    return "unknown"
def _path_parts(path: str) -> list[str]:
    text = os.path.normcase(path).replace('\\', '/')
    return [part for part in text.split('/') if part]
def _coverage_paths_match(e_filepath: str, fpath: str,
                          project_root: str | None = None) -> bool:
    if (not isinstance(e_filepath, str) or not isinstance(fpath, str)
            or not e_filepath or not fpath):
        return False
    if project_root:
        root = os.path.realpath(os.path.abspath(project_root))
        e_absolute = (e_filepath if os.path.isabs(e_filepath)
                      else os.path.join(root, e_filepath))
        f_absolute = (fpath if os.path.isabs(fpath)
                      else os.path.join(root, fpath))
        return (os.path.normcase(os.path.realpath(e_absolute))
                == os.path.normcase(os.path.realpath(f_absolute)))
    e_parts = _path_parts(e_filepath)
    f_parts = _path_parts(fpath)
    if not e_parts or not f_parts:
        return False
    if len(e_parts) <= len(f_parts):
        return f_parts[-len(e_parts):] == e_parts
    return e_parts[-len(f_parts):] == f_parts
def _entry_attr_number(entry, names: tuple[str, ...], default: Any) -> Any:
    for name in names:
        value = numeric_or(getattr(entry, name, 0), 0)
        if value:
            return value
    return default
def _entry_attr_text(entry, names: tuple[str, ...]) -> str:
    for name in names:
        value = getattr(entry, name, "")
        if isinstance(value, str) and value:
            return value
    return ""
def _entry_func_span(entry):
    e_line = _entry_attr_number(entry, ("line", "lineno"), 0)
    if e_line <= 0:
        return None
    e_end = _entry_attr_number(entry, ("end_line", "end_lineno"), 0)
    if e_end <= 0:
        return None
    return e_line, max(e_end, e_line)
def _executed_lines_hit_span(fdata: dict, e_line, e_end) -> bool:
    executed_lines = fdata.get('executed_lines', [])
    if not (isinstance(executed_lines, (list, tuple, set)) and executed_lines):
        return False
    return any(e_line <= ln <= e_end
               for ln in executed_lines
               if isinstance(ln, int) and not isinstance(ln, bool))
def _coverage_file_hit(files_data: dict, e_filepath: str, span: tuple,
                       project_root: str | None = None) -> bool:
    e_line, e_end = span
    if e_end < e_line:
        return False
    matches = [
        (fpath, fdata) for fpath, fdata in files_data.items()
        if isinstance(fdata, dict) and _coverage_paths_match(
            e_filepath, fpath, project_root)
    ]
    if not matches:
        return False
    if project_root:
        return any(_executed_lines_hit_span(fdata, e_line, e_end)
                   for _fpath, fdata in matches)
    entry_parts = _path_parts(e_filepath)
    exact = [fdata for fpath, fdata in matches
             if _path_parts(fpath) == entry_parts]
    if not exact and len(matches) > 1:
        return False
    candidates = exact or [fdata for _fpath, fdata in matches]
    return any(_executed_lines_hit_span(fdata, e_line, e_end)
               for fdata in candidates)
def _entry_body_start(entry, start: int, end: int) -> int | None:
    details = getattr(entry, 'details', None)
    if isinstance(details, dict) and 'body_first_line' in details:
        finite = finite_float_or_none(details.get('body_first_line'))
        if finite is not None:
            body_start = int(finite)
            if body_start == 0:
                return start + 1 if end > start else start
            if start <= body_start <= end:
                return body_start
        return None
    return start + 1 if end > start else start
def _entry_body_lines(entry) -> int | None:
    details = getattr(entry, 'details', None)
    if not isinstance(details, dict):
        return None
    finite = finite_float_or_none(details.get('body_lines'))
    if finite is None or finite < 0:
        return None
    return int(finite)
def _coverage_line_evidence(entry, cov, project_root: str | None = None) -> bool:
    if not (isinstance(cov, dict) and cov):
        return False
    files_data = cov.get('files', {})
    e_filepath = _entry_attr_text(entry, ('filepath', 'file'))
    if not (e_filepath and isinstance(files_data, dict)):
        return False
    span = _entry_func_span(entry)
    if span is None:
        return False
    start, end = span
    if _entry_body_lines(entry) == 0:
        return False
    body_start = _entry_body_start(entry, start, end)
    if body_start is None or body_start > end:
        return False
    return _coverage_file_hit(
        files_data, e_filepath, (body_start, end), project_root)
def _fuzzy_detail_matches(detail: dict, e_name: str) -> bool:
    d_func = detail.get('function', '')
    if not isinstance(d_func, str) or not d_func:
        return False
    if detail.get('status', '') != 'resolved':
        return False
    return e_name == d_func
def _fuzzy_execution_evidence(sim_report, e_name: str) -> bool:
    fuzzy_exec = getattr(sim_report, 'fuzzy_execution', None)
    if not isinstance(fuzzy_exec, dict):
        return False
    details = fuzzy_exec.get('details', [])
    if not isinstance(details, list):
        return False
    return any(_fuzzy_detail_matches(detail, e_name)
               for detail in details if isinstance(detail, dict))
def _count_evidence_sources(entry, sim_report=None) -> set:
    sources = {"static"}
    e_name = _entry_attr_text(entry, ('name',))
    if sim_report is not None and getattr(entry, 'level', None) == 'function':
        cov = getattr(sim_report, 'coverage_data', None)
        if _coverage_line_evidence(
                entry, cov, getattr(sim_report, 'project_root', None)):
            sources.add("dynamic")
        if "dynamic" not in sources and _fuzzy_execution_evidence(
                sim_report, e_name):
            sources.add("dynamic")
    return sources
def _resolve_entry_confidence(entry) -> tuple[str, float]:
    raw_conf = getattr(entry, 'confidence', 'unknown')
    numeric_conf = _NUMERIC_CONF_FLOOR
    _safe_conf = finite_float_or_none(getattr(entry, 'numeric_confidence', None))
    if _safe_conf is not None:
        numeric_conf = min(100.0, max(float(_NUMERIC_CONF_FLOOR), _safe_conf))
    elif raw_conf in ('confirmed', 'confirmed_untested'):
        numeric_conf = _CONFIRMED_ENTRY_CONFIDENCE
    elif raw_conf == FIELD_POTENTIAL_FP:
        numeric_conf = _POTENTIAL_FP_CONFIDENCE
    return raw_conf, numeric_conf
def _phase2_dynamic_reject(entry, evidence: set) -> bool:
    if "dynamic" not in evidence:
        return False
    entry.reliability_score = 0.0
    _assign_confidence(entry, FIELD_POTENTIAL_FP)
    entry.confidence_reason = (
        "dynamic evidence covered (phase2 rejected by simulation)")
    return True
def _phase3_reclassify(entry, raw_conf: str, numeric_conf: float,
                       evidence: set) -> tuple[str, float | None]:
    if raw_conf == 'external_api':
        entry.reliability_score = 0.5
        return "external_api", None
    reliability = _compute_reliability_score(numeric_conf, evidence)
    if raw_conf != 'confirmed_untested':
        entry.confidence = _confidence_to_reliability_category(reliability)
    entry.reliability_score = reliability
    if entry.confidence == 'confirmed':
        bucket = "confirmed"
    elif entry.confidence == 'confirmed_untested':
        bucket = "confirmed_untested"
    else:
        bucket = "phase3_rejected"
    return bucket, reliability
def _classify_entry(entry, sim_report: Any | None, phase_counts: dict,
                    reliability_scores: list) -> bool:
    if getattr(entry, 'level', None) == 'code':
        return True
    phase_counts["phase1"] += 1
    raw_conf, numeric_conf = _resolve_entry_confidence(entry)
    evidence = _count_evidence_sources(entry, sim_report)
    if (raw_conf not in ('confirmed_untested', 'external_api')
            and _phase2_dynamic_reject(entry, evidence)):
        phase_counts["phase2_rejected"] += 1
        return False
    bucket, reliability = _phase3_reclassify(
        entry, raw_conf, numeric_conf, evidence)
    if reliability is not None:
        reliability_scores.append(reliability)
    phase_counts[bucket] += 1
    return True
def confirm_dead_code_with_evidence(entries: list | None,
                                    sim_report: Any | None = None) -> dict:
    phase_counts = {"phase1": 0, "phase2_rejected": 0, "phase3_rejected": 0,
                    "confirmed": 0, "confirmed_untested": 0,
                    "external_api": 0}
    reliability_scores: list[float] = []
    adjusted_entries = []
    for e in entries or []:
        if _classify_entry(e, sim_report, phase_counts, reliability_scores):
            adjusted_entries.append(e)
    return {
        "phase_counts": phase_counts,
        "reliability_stats": {
            "avg_reliability": round(sum(reliability_scores) / max(len(reliability_scores), 1), 4)
            if reliability_scores else 0,
            "entries_with_reliability": len(reliability_scores),
            "phase2_rejected": phase_counts["phase2_rejected"],
            "phase3_rejected": phase_counts["phase3_rejected"],
        },
        "entries": adjusted_entries,
    }
class BlindspotHub:
    def __init__(self, project_root: str, ctx=None) -> None:
        self.project_root = os.path.abspath(_required_project_root(project_root))
        self.report = UnifiedBlindspotReport(project_root=self.project_root)
        self._ctx = ctx
        self.exception_analysis = None
    @timed_log()
    def scan_all(
        self,
        source_paths: list[str] | None = None,
        coverage_hook=None,
        call_graph=None,
        include_code_blindspots: bool = DEFAULT_INCLUDE_CODE_BLINDSPOTS,
        lazy_modules: set | None = None,
        whitelist: set[str] | None = None,
        ignored_decorators: set[str] | None = None,
    ) -> UnifiedBlindspotReport:
        self.report = UnifiedBlindspotReport(project_root=self.project_root)
        self.exception_analysis = None
        validate_source_paths(source_paths)
        source_paths = _filter_in_scope_paths(self.project_root, source_paths)
        _layer_results = run_layer14_parallel(
            self.project_root, self._ctx, source_paths, coverage_hook,
            call_graph, lazy_modules)
        self.report.collect_layer_reports(_layer_results)
        def _filter_noise() -> None:
            self.report.filter_by_whitelist(whitelist)
            self.report.filter_by_ignore_decorators(
                ignored_decorators, call_graph)
        _filter_noise()
        self.exception_analysis = run_layers_5_to_76(
            self.report, self.project_root, self._ctx, source_paths,
            coverage_hook, call_graph, include_code_blindspots,
            before_clustering=_filter_noise, after_code_scan=_filter_noise)
        self._attach_syntax_errors(call_graph)
        return self.report
    def _attach_syntax_errors(self, call_graph) -> None:
        syntax_errors = as_entry_list(getattr(call_graph, "syntax_errors", None))
        if syntax_errors:
            self.report.metrics["syntax_errors"] = syntax_errors
def _filter_in_scope_paths(project_root: str, source_paths):
    if not source_paths:
        return source_paths
    filtered = [p for p in source_paths
                if not is_diagnosis_out_of_scope(p, root_dir=project_root)]
    if len(filtered) != len(source_paths):
        logger.info(
            "[盲区] 诊断范围过滤: %d → %d 个路径（排除 tests/归口目录/Temp）",
            len(source_paths), len(filtered))
    return filtered
def scan_blindspots(project_root: str=DEFAULT_PROJECT_ROOT, source_paths: list[str] | None=None, include_code: bool=DEFAULT_INCLUDE_CODE_BLINDSPOTS, output_json: str | None=None, call_graph: Any=None, ctx: Any=None, whitelist_files: list[str] | str | None=None, ignore_decorators: list[str] | str | None=None, coverage_hook: Any=None) -> UnifiedBlindspotReport:
    project_root = validated_warmed_root(project_root)
    validate_source_paths(source_paths)
    source_paths = _filter_in_scope_paths(project_root, source_paths)
    call_graph = _prepare_call_graph(project_root, source_paths, call_graph, ctx)
    whitelist, ignored_decorators = _load_noise_reduction(whitelist_files, ignore_decorators)
    hub = BlindspotHub(project_root, ctx=ctx)
    code_layer_enabled = include_code and coverage_hook is not None
    report = hub.scan_all(
        source_paths=source_paths,
        coverage_hook=coverage_hook,
        call_graph=call_graph,
        include_code_blindspots=code_layer_enabled,
        whitelist=whitelist,
        ignored_decorators=ignored_decorators,
    )
    if include_code and not code_layer_enabled:
        report.metrics["code"] = {
            "skipped_reason": "runtime_coverage_not_provided",
            "coverage_available": False,
        }
    report.filter_by_whitelist(whitelist)
    report.filter_by_ignore_decorators(ignored_decorators, call_graph)
    _syn_errors = as_entry_list(report.metrics.get("syntax_errors"))
    report.log_summary(project_root, _syn_errors)
    if output_json:
        report.to_json(output_json)
        logger.info("\n[JSON -> %s]", output_json)
    return report
def _prepare_call_graph(project_root: str, source_paths: list[str] | None,
                        call_graph: Any, ctx: Any) -> Any:
    if call_graph is not None:
        return call_graph
    logger.info("[盲区] 构建调用图...")
    return CallGraphBuilder(
        project_root, ctx=ctx, include_tests=False).build(source_paths)
def _load_noise_reduction(whitelist_files, ignore_decorators) -> tuple[set, set]:
    whitelist_files = _as_path_list(whitelist_files)
    whitelist = load_whitelist(whitelist_files)
    ignored_decorators = load_ignore_decorators(ignore_decorators)
    if whitelist_files:
        logger.info("  [Whitelist] 加载白名单: %d 个标识符（来自 %d 个文件）",
                    len(whitelist), len(whitelist_files))
    if ignored_decorators:
        logger.info("  [IgnoreDecorators] 忽略装饰器: %s", sorted(ignored_decorators))
    return whitelist, ignored_decorators
class CallGraphAnalyzer:
    def __init__(self, skill_dir: str):
        self.skill_dir = _required_project_root(skill_dir)
    def analyze(self, cache=None) -> dict:
        build_fingerprint = callgraph_share_fingerprint(self.skill_dir)
        ctx = (as_diag_ctx(cache)
               if cache is not None and hasattr(cache, "slots") else None)
        def _ctor(cls, *args):
            if ctx is None or not _ctor_accepts_ctx(cls):
                return cls(*args)
            return cls(*args, ctx=ctx)
        graph, graph_summary, all_findings = \
            self._build_static_graph(_ctor, cache)
        self._scan_runtime_bindings(graph, graph_summary)
        graph_summary["break_points"] = len(
            graph.analyses.breakpoints.get_break_points() or [])
        func_count, edge_count, orphan_count = _graph_counts(graph)
        graph_summary.update(zip(
            ("functions", "edges", "orphans"),
            (func_count, edge_count, orphan_count)))
        self._serialize_graph_indexes(graph, graph_summary)
        _bs_scan_error = self._scan_blindspots(
            _ctor, cache, graph, all_findings, graph_summary)
        _empty_graph = func_count <= 0
        if _empty_graph:
            logger.warning("[CGA] 调用图函数数为 0，通道状态降级")
        self._persist_graph_outputs(
            cache, graph_summary, func_count,
            expected_fingerprint=build_fingerprint)
        summary_parts = [f"调用图: {func_count}函数, {edge_count}边"]
        if orphan_count:
            summary_parts.append(f"{orphan_count}孤立")
        if all_findings:
            summary_parts.append(f"{len(all_findings)}个发现")
        return {
            "status": ("warn" if _bs_scan_error is not None or _empty_graph
                        else "pass"),
            "findings_count": len(all_findings),
            "findings": all_findings,
            "summary": ", ".join(summary_parts),
            "payload": {
                "call_graph": graph_summary,
                "functions": func_count,
                "edges": edge_count,
                "orphans": orphan_count,
            },
        }
    def _build_static_graph(self, ctor, cache):
        builder = ctor(CallGraphBuilder, self.skill_dir)
        graph = builder.build()
        func_count, edge_count, orphan_count = _graph_counts(graph)
        if cache is not None and hasattr(cache, 'slots'):
            _call_slot_setter(
                cache.slots, "set_call_graph", graph,
                label="调用图槽位回写")
        all_findings = []
        _bp_count = len(
            graph.analyses.breakpoints.get_break_points() or [])
        _syn_errs = getattr(graph, "syntax_errors", None) or []
        graph_summary = {
            "functions": func_count,
            "edges": edge_count,
            "orphans": orphan_count,
            "break_points": _bp_count,
            "syntax_errors": len(_syn_errs),
        }
        return graph, graph_summary, all_findings
    def _scan_runtime_bindings(self, graph, graph_summary):
        try:
            observed, binding_report = scan_runtime_bindings(
                graph, self.skill_dir)
            graph_summary["binding_observed"] = observed
            self._merge_binding_report(graph, binding_report, graph_summary)
        except (ImportError, AttributeError) as e:
            logger.debug("[CGA] 运行时绑定扫描不可用: %s", e)
        except Exception as e:
            logger.warning("[CGA] 运行时绑定扫描异常: %s", e, exc_info=True)
    @staticmethod
    def _merge_binding_report(graph, report, graph_summary) -> None:
        try:
            binding_merge = merge_bindings_into_callgraph(graph, report)
            graph_summary["binding_merge"] = binding_merge
            if binding_merge.get("new_edges"):
                logger.info(
                    "[CGA] 绑定合并: +%s 边, 解析 %s, 未解析 %s",
                    binding_merge["new_edges"], binding_merge["resolved"],
                    binding_merge["unresolved"],)
        except (AttributeError, KeyError, TypeError, ValueError) as _bm_e:
            logger.debug("[CGA] 绑定合并失败: %s", _bm_e)
    def _serialize_graph_indexes(self, graph, graph_summary):
        try:
            graph_summary["functions_index"] = {
                fname: {
                    "filepath": getattr(fnode, "filepath", ""),
                    "start_line": getattr(fnode, "start_line", 0),
                    "end_line": getattr(fnode, "end_line", 0),
                }
                for fname, fnode in (getattr(graph, "functions", None) or {}).items()
            }
        except Exception as e:
            logger.warning("[CGA] functions_index 序列化失败: %s", e, exc_info=True)
        try:
            graph_summary["callers_index"] = {
                callee: sorted(callers)
                for callee, callers in (getattr(graph, "callers", None) or {}).items()
                if callers
            }
        except Exception as e:
            logger.warning("[CGA] callers_index 序列化失败: %s", e, exc_info=True)
    def _scan_blindspots(self, ctor, cache, graph, all_findings, graph_summary):
        _bs_scan_error: str | None = None
        logger.info(
            "[CGA] 代码层盲区扫描跳过：C1 无运行时覆盖率数据")
        try:
            hub = ctor(BlindspotHub, self.skill_dir)
            _src_paths = (getattr(cache, "py_files", None)
                          if cache is not None else None)
            bs_result = hub.scan_all(
                source_paths=_src_paths,
                call_graph=graph,
                include_code_blindspots=False,
            )
            _degrade = self._apply_blindspot_result(
                cache, hub, bs_result, all_findings, graph_summary)
            if _degrade is not None:
                _bs_scan_error = safe_text(_degrade, MESSAGE_TRUNCATE_LEN)
        except (ImportError, AttributeError) as e:
            logger.debug("[CGA] 盲点扫描不可用: %s", e)
            _bs_scan_error = safe_text(f"{type(e).__name__}: {e}", MESSAGE_TRUNCATE_LEN)
        except Exception as e:
            logger.warning("[CGA] 盲点扫描异常: %s", e, exc_info=True)
            _bs_scan_error = safe_text(f"{type(e).__name__}: {e}", MESSAGE_TRUNCATE_LEN)
        if _bs_scan_error is not None:
            graph_summary["blindspot_scan_error"] = _bs_scan_error
        return _bs_scan_error
    def _apply_blindspot_result(self, cache, hub, bs_result,
                                all_findings, graph_summary) -> str | None:
        _degrade = self._cache_bs_artifacts(cache, hub, bs_result)
        raw = self._result_to_dict(bs_result)
        bs_findings = _normalize_bs_entries(raw)
        (code_level_aggr, confirmed_entries, confirmed_total,
         dropped_unserializable) = collect_blindspot_entries(
            bs_findings, all_findings)
        if dropped_unserializable:
            logger.warning(
                "[CGA] %s 条盲点条目不可消费（既非 dict/str 也无 to_dict，"
                "或 to_dict 返回非 dict/str），已跳过",
                dropped_unserializable)
        apply_blindspot_summary(graph_summary, BlindspotSummary(
            raw=raw, bs_count=len(bs_findings),
            code_level_aggr=code_level_aggr,
            confirmed_entries=confirmed_entries,
            confirmed_total=confirmed_total))
        return _degrade
    def _cache_bs_artifacts(self, cache, hub, bs_result) -> str | None:
        slots = getattr(cache, "slots", None) if cache is not None else None
        if slots is None:
            if cache is not None and (
                    hasattr(cache, "set_blindspot_report")
                    or hasattr(cache, "set_exception_result")):
                return "AttributeError: cache 声明槽位 setter 但缺 slots 总线"
            return None
        errors = (
            self._write_blindspot_slot(slots, bs_result),
            self._write_exception_slot(slots, hub),
        )
        return "; ".join(error for error in errors if error) or None
    def _write_blindspot_slot(self, slots, bs_result) -> str | None:
        _report_setter = getattr(slots, "set_blindspot_report", None)
        if not callable(_report_setter):
            return "AttributeError: slots 缺 set_blindspot_report"
        try:
            _report_setter(bs_result)
        except Exception as _bs_e:  # noqa: BLE001
            logger.debug("[CGA] 盲点报告槽位回写失败: %s", _bs_e)
            return safe_text(
                f"{type(_bs_e).__name__}: {_bs_e}", MESSAGE_TRUNCATE_LEN)
        return None
    def _write_exception_slot(self, slots, hub) -> str | None:
        try:
            _exc_full = getattr(hub, "exception_analysis", None)
        except Exception as _exc_get_e:  # noqa: BLE001
            logger.debug("[CGA] 异常传播成果探测失败: %s", _exc_get_e)
            return safe_text(
                f"{type(_exc_get_e).__name__}: {_exc_get_e}", MESSAGE_TRUNCATE_LEN)
        if not _exc_full:
            return None
        _exc_setter = getattr(slots, "set_exception_result", None)
        if not callable(_exc_setter):
            return "AttributeError: slots 缺 set_exception_result"
        try:
            _exc_setter(_exc_full)
        except Exception as _exc_e:  # noqa: BLE001
            logger.debug("[CGA] 异常传播槽位回写失败: %s", _exc_e)
            return safe_text(
                f"{type(_exc_e).__name__}: {_exc_e}", MESSAGE_TRUNCATE_LEN)
        return None
    def _persist_graph_outputs(self, cache, graph_summary, func_count,
                               expected_fingerprint: str | None = None):
        try:
            _fc = int(func_count)
        except (TypeError, ValueError, OverflowError) as _e:
            log_swallowed(__name__, _e, context='CallGraphAnalyzer._persist_graph_outputs:numeric')
            _fc = 0
        self._persist_to_cache_slots(cache, graph_summary, _fc)
        try:
            persist_call_graph_share(
                self.skill_dir, graph_summary, _fc,
                expected_fingerprint=expected_fingerprint)
        except Exception as _share_e:  # noqa: BLE001
            logger.debug("[CGA] 调用图共享回写失败: %s", _share_e)
    @staticmethod
    def _persist_to_cache_slots(cache, graph_summary, func_count: int) -> None:
        if cache is None or not hasattr(cache, "slots"):
            return
        slots = cache.slots
        _call_slot_setter(
            slots, "set_call_graph_summary", graph_summary,
            label="调用图缓存槽位回写")
        _mark_graph_health(slots, func_count)
    @staticmethod
    def _result_to_dict(result) -> dict:
        payload = _safe_to_dict(result)
        if payload is not None:
            return payload
        if isinstance(result, dict):
            return result
        if hasattr(result, '__dict__'):
            return {k: v for k, v in result.__dict__.items() if not k.startswith('_')}
        return {"raw": str(result)}
def _ctor_accepts_ctx(cls) -> bool:
    try:
        if cls.__init__ is object.__init__:
            return False
    except (AttributeError, TypeError) as _e:
        log_swallowed(__name__, _e, context='_ctor_accepts_ctx:AttributeError')
        return False
    try:
        sig = inspect.signature(cls.__init__)
    except (TypeError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_ctor_accepts_ctx:TypeError')
        return False
    params = sig.parameters.values()
    if any(p.kind == inspect.Parameter.VAR_KEYWORD for p in params):
        return True
    return any(p.name == "ctx" for p in params)
def _normalize_bs_entries(raw: dict) -> list:
    bs_findings = raw.get("entries")
    if bs_findings is None:
        bs_findings = raw.get("blocks")
    if isinstance(bs_findings, (list, tuple)):
        return list(bs_findings)
    return []
def _graph_collection_count(graph, collection_name: str,
                            count_name: str) -> int:
    collection = getattr(graph, collection_name, None)
    if collection is not None:
        try:
            return len(collection)
        except TypeError:
            logger.debug("[CGA] %s 非可计数集合，回退 %s",
                         collection_name, count_name)
    value = getattr(graph, count_name, 0)
    return value if isinstance(value, int) and not isinstance(value, bool) else 0
def _graph_counts(graph) -> tuple:
    return (
        _graph_collection_count(graph, "functions", "function_count"),
        _graph_collection_count(graph, "calls", "edge_count"),
        _graph_collection_count(graph, "orphans", "orphan_count"),
    )
def _safe_to_dict(result) -> dict | None:
    to_dict = getattr(result, "to_dict", None)
    if not callable(to_dict):
        return None
    try:
        payload = to_dict()
    except Exception as _td_err:  # noqa: BLE001
        logger.warning(
            "[CGA] to_dict() 抛异常，降级 __dict__/dict/raw 分支: %s",
            _td_err)
        return None
    if isinstance(payload, dict):
        return payload
    logger.warning(
        "[CGA] to_dict() 返回非 dict（%s），降级 __dict__/dict/raw 分支",
        type(payload).__name__)
    return None
def run_call_graph_analysis(skill_dir: str, cache: Any = None) -> dict:
    try:
        skill_dir = _required_project_root(skill_dir)
        cache = ensure_entry_warmed(
            skill_dir, cache, who="run_call_graph_analysis")
        analyzer = CallGraphAnalyzer(skill_dir)
        return analyzer.analyze(cache=cache)
    except Exception as e:
        logger.warning("[CGA] 调用关系分析异常: %s", e, exc_info=True)
        return {
            "status": "error",
            "findings_count": 0,
            "summary": f"调用关系分析错误: {e}",
            "error": safe_text(f"{type(e).__name__}: {e}", MESSAGE_TRUNCATE_LEN),
            "findings": [],
        }
def _optional_key(key: str, value) -> dict:
    return {key: value} if value else {}
def _callgraph_payload_part(d1_result: dict, d1_status: str,
                            d1_findings: list, cg: dict) -> dict:
    _d1_error = (safe_text(d1_result["error"], MESSAGE_TRUNCATE_LEN)
                 if d1_status == "error" and d1_result.get("error") else "")
    return {
        "status": d1_status,
        "functions": as_number(cg.get("functions", 0), 0),
        "edges": as_number(cg.get("edges", 0), 0),
        "orphans": as_number(cg.get("orphans", 0), 0),
        "break_points": as_number(cg.get("break_points", 0), 0),
        "syntax_errors": as_number(cg.get("syntax_errors", 0), 0),
        "blindspots": as_number(cg.get("blindspots", 0), 0),
        "coverage_pct": as_number(cg.get("coverage_pct", 0), 0),
        "findings_count": len(d1_findings),
        "binding_observed": cg.get("binding_observed"),
        "binding_merge": cg.get("binding_merge"),
        "blindspot_code_level_aggregated": cg.get(
            "blindspot_code_level_aggregated"),
        **_optional_key("blindspot_clustering", cg.get("blindspot_clustering")),
        **_optional_key("blindspot_confirmed_entries",
                        cg.get("blindspot_confirmed_entries")),
        "functions_index": cg.get("functions_index"),
        "callers_index": cg.get("callers_index"),
        **_optional_key("error", _d1_error),
        **_optional_key("blindspot_scan_error",
                        safe_text(cg.get("blindspot_scan_error") or "",
                                   MESSAGE_TRUNCATE_LEN)),
    }
def run_callgraph_channel(skill_dir: str, cache=None) -> tuple:
    try:
        d1_result = run_call_graph_analysis(skill_dir, cache=cache)
        _st = d1_result.get("status")
        d1_status = _st if _st in ("pass", "warn", "error") else "error"
        d1_findings = as_list(d1_result.get("findings"))
        _cg_raw = dict_or_empty(d1_result.get("payload")).get("call_graph")
        _cg = _cg_raw if isinstance(_cg_raw, dict) else {}
        return (_callgraph_payload_part(d1_result, d1_status, d1_findings, _cg),
                d1_findings, d1_status in ("error", "warn"))
    except Exception as e:  # noqa: BLE001
        logger.warning("[D1] 调用关系分析失败: %s", e)
        return ({"status": "error", "findings_count": 0,
                 "error": safe_text(e, MESSAGE_TRUNCATE_LEN)}, [], True)
_GRAPH_HEALTH_DEFAULTS = {
    "CALL_GRAPH_HEALTHY": "healthy",
    "CALL_GRAPH_DEGRADED": "degraded",
    "CALL_GRAPH_MISSING": "missing",
}
def _call_slot_setter(slots, setter_name: str, *args, label: str) -> bool:
    if slots is None:
        return False
    try:
        setter = getattr(slots, setter_name, None)
        if not callable(setter):
            return False
        setter(*args)
    except Exception as exc:  # noqa: BLE001
        logger.debug("[CGA] %s失败: %s", label, exc)
        return False
    return True
def _set_graph_health(slots, code_attr: str, detail: str) -> None:
    if slots is None:
        return
    code = getattr(slots, code_attr, _GRAPH_HEALTH_DEFAULTS[code_attr])
    _call_slot_setter(
        slots, "set_call_graph_health", code, detail,
        label="调用图健康标记回写")
def _mark_summary_health(slots, summary) -> None:
    func_count = (int(as_number(summary.get("functions", 0), 0))
                  if isinstance(summary, dict) else 0)
    _mark_graph_health(slots, func_count)
def ensure_call_graph(skill_dir: str, cache: Any) -> dict | None:
    slots = getattr(cache, "slots", None)
    try:
        skill_dir = _required_project_root(skill_dir)
    except (TypeError, ValueError) as exc:
        logger.warning("[CGA] 调用图根路径无效: %s", exc)
        _mark_graph_health(slots, None, missing_detail=safe_text(
            f"{type(exc).__name__}: {exc}", MESSAGE_TRUNCATE_LEN))
        return None
    if slots is not None:
        try:
            if slots.has_call_graph_summary():
                summary = slots.get_call_graph_summary()
                if isinstance(summary, dict) and summary:
                    _mark_summary_health(slots, summary)
                    return summary
                logger.warning(
                    "[CGA] 内存调用图摘要为空或非 dict，回退共享层/重建")
            shared = slots.load_call_graph_share(skill_dir)
        except Exception as e:  # noqa: BLE001
            logger.warning("[CGA] 调用图缓存槽位读取失败，回退重建: %s", e)
            shared = None
        if isinstance(shared, dict) and shared:
            logger.info("[CGA] ensure_call_graph 命中磁盘共享层（免重建）")
            _call_slot_setter(
                slots, "set_call_graph_summary", shared,
                label="调用图摘要回填")
            _mark_summary_health(slots, shared)
            return shared
    try:
        result = run_call_graph_analysis(skill_dir, cache=cache)
        if not isinstance(result, dict) or result.get("status") == "error":
            detail = (safe_text(result.get("error", "构建失败"), MESSAGE_TRUNCATE_LEN)
                      if isinstance(result, dict) else "")
            _mark_graph_health(slots, None, missing_detail=detail)
            return None
        return _graph_from_build(result, slots)
    except Exception as e:  # noqa: BLE001
        logger.warning("[CGA] ensure_call_graph 构建异常: %s", e)
        _mark_graph_health(
            slots, None,
            missing_detail=safe_text(
                f"{type(e).__name__}: {e}", MESSAGE_TRUNCATE_LEN))
        return None
def _mark_graph_health(slots, func_count: int | None,
                      missing_detail: str = "") -> None:
    if func_count is None:
        _set_graph_health(slots, "CALL_GRAPH_MISSING", missing_detail)
        return
    healthy = func_count > 0
    _set_graph_health(
        slots, "CALL_GRAPH_HEALTHY" if healthy else "CALL_GRAPH_DEGRADED",
        "" if healthy else "函数数为 0（空图）")
def _graph_from_build(result: dict, slots) -> dict | None:
    payload = result.get("payload") or {}
    graph = payload.get("call_graph")
    if graph is None:
        _set_graph_health(slots, "CALL_GRAPH_DEGRADED", "payload 缺 call_graph")
        return None
    _call_slot_setter(
        slots, "set_call_graph_summary", graph,
        label="调用图摘要回填")
    func_count = payload.get("functions", 0) or 0
    try:
        _fc = int(func_count)
    except (TypeError, ValueError, OverflowError):  # jwsgj:silent-ok
        _fc = 0
    _mark_graph_health(slots, _fc)
    return graph
_LIGHTDIAG_ERROR_STEPS = 3
_LIGHTDIAG_BP_HIGH_RISK = 10
_LIGHTDIAG_SCORE_HIGH_RISK = 60
_LIGHTDIAG_SCORE_WARNING = 80
_LIGHTDIAG_WEAK_TOP_N = 3
def _resolve_status(errors: list[dict]) -> str:
    if len(errors) >= _LIGHTDIAG_ERROR_STEPS:
        return "error"
    return "partial" if errors else "ok"
def _merge_call_chain_judgments(report: dict, cg_judgments) -> None:
    if isinstance(cg_judgments, dict) and cg_judgments:
        report.setdefault("judgments", []).extend(
            j for j in cg_judgments.values() if isinstance(j, dict))
def _split_info_break_points(report: dict) -> None:
    details = report["call_chain"].get("break_point_details", []) or []
    info_bps: list = []
    real_bps: list = []
    for item in details:
        sev = severity_text_value(item.get("severity")) if isinstance(item, dict) else None
        info = sev == "INFO"
        (info_bps if info else real_bps).append(item)
    if not info_bps:
        report.pop("api_inventory", None)
        report["call_chain"].pop("api_inventory_count", None)
        return
    report["api_inventory"] = {
        "total": len(info_bps),
        "description": "公开 API 清单（无内部调用者，库型技能正常现象）",
        "functions": [
            {"name": bp.get("function", bp.get("name", "?")),
             "message": bp.get("message", "")}
            for bp in info_bps if isinstance(bp, dict)],
    }
    report["call_chain"]["break_point_details"] = real_bps
    report["call_chain"]["break_points"] = len(real_bps)
    report["call_chain"]["api_inventory_count"] = len(info_bps)
def _record_step_error(errors: list[dict], step: str,
                       exc: BaseException, label: str) -> None:
    errors.append({"step": step, "error": str(exc)[:200]})
    logger.warning("[LightDiag] %s失败: %s", label, exc)
def _report_call_chain(report: dict, skill_dir: str, errors: list[dict]) -> None:
    try:
        graph = CallGraphBuilder(
            project_root=skill_dir, include_tests=False).build()
        s = graph.analyses.summary.summary()
        report["call_chain"] = {
            "total_functions": s.get("total_functions", 0),
            "public_functions": s.get("public_functions", 0),
            "total_calls": s.get("total_calls", 0),
            "cross_file_calls": s.get("cross_file_calls", 0),
            "orphans": s.get("orphans", 0),
            "break_point_details": graph.analyses.breakpoints.get_break_points(),
            "break_points": s.get("break_points", 0),
            "external_deps": s.get("external_deps", 0),
            "external_deps_total": s.get("external_deps_total", 0),
            "syntax_errors": s.get("syntax_errors", 0),
            "exemption_classification": s.get("exemption_classification", {}),
            "judgments": s.get("judgments", {}),
        }
        _merge_call_chain_judgments(report, s.get("judgments", {}))
        _split_info_break_points(report)
        report["call_depth"] = analyze_call_depth(graph)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context='_report_call_chain:Exc')
        _record_step_error(errors, "call_chain", e, "调用链诊断")
def _report_antipatterns(report: dict, skill_dir: str, top_files: int,
                         errors: list[dict]) -> None:
    try:
        files = collect_top_scan_files(skill_dir, top_files)
        issues = real_antipattern_scan(files)
        by_severity: dict[str, int] = {}
        by_type: dict[str, int] = {}
        accepted = 0
        for item in issues:
            if not isinstance(item, dict):
                continue
            accepted += 1
            sev = severity_key(severity_text_value(item.get("severity"))) or "UNKNOWN"
            by_severity[sev] = by_severity.get(sev, 0) + 1
            typ = str(item.get("type") or item.get("rule_id") or "unknown")
            by_type[typ] = by_type.get(typ, 0) + 1
        report["antipatterns"] = {
            "scanned_files": len(files),
            "total": accepted,
            "by_severity": by_severity,
            "top_types": dict(sorted(
                by_type.items(), key=lambda kv: kv[1], reverse=True)[:10]),
        }
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context='_report_antipatterns:Exc')
        _record_step_error(errors, "antipatterns", e, "反模式扫描")
def _report_quality(report: dict, skill_dir: str, errors: list[dict]) -> None:
    try:
        ten_dim = quick_score(skill_dir)
        if hasattr(ten_dim, "to_dict"):
            data = ten_dim.to_dict()
        else:
            data = dict(ten_dim) if isinstance(ten_dim, dict) else {"raw": str(ten_dim)}
        dims = data.get("dimensions", [])
        weak = sorted(
            ({"name": d.get("name"),
              "score": float_metric(d.get("score", 0))}
             for d in dims
             if isinstance(d, dict) and d.get("grade") != "N/A"),
            key=lambda d: d["score"],
        )[:_LIGHTDIAG_WEAK_TOP_N]
        report["quality"] = {
            "overall_score": data.get("overall_score", 0),
            "overall_grade": data.get("overall_grade", "N/A"),
            "weakest_dimensions": weak,
        }
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context='_report_quality:Exc')
        _record_step_error(errors, "quality", e, "十维评分")
def _light_verdict_signals(report: dict) -> tuple[int, int, int, float | None]:
    bp = report.get("call_chain", {}).get("break_points", 0)
    anti = report.get("antipatterns", {})
    by_severity = anti.get("by_severity", {})
    anti_high = by_severity.get("P0", 0) + by_severity.get("P1", 0)
    anti_total = anti.get("total", 0)
    raw_score = report.get("quality", {}).get("overall_score")
    return bp, anti_high, anti_total, float_metric(raw_score, None)
def _light_verdict_decide(bp: int, anti_high: int, anti_total: int,
                          score: float | None, has_output: bool) -> str:
    if (anti_high > 0 or bp >= _LIGHTDIAG_BP_HIGH_RISK
            or (score is not None and score < _LIGHTDIAG_SCORE_HIGH_RISK)):
        return "needs_attention"
    if (anti_total > 0 or bp > 0
            or (score is not None and score < _LIGHTDIAG_SCORE_WARNING)):
        return "acceptable"
    return "healthy" if has_output else "unknown"
def _compute_light_verdict(report: dict, errors: list[dict]) -> str:
    verdict = "unknown"
    try:
        bp, anti_high, anti_total, score = _light_verdict_signals(report)
        verdict = _light_verdict_decide(
            bp, anti_high, anti_total, score,
            bool(report.get("call_chain") or report.get("quality")))
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context='_compute_light_verdict:Exc')
        _record_step_error(errors, "verdict", e, "综合判定")
    return verdict
def _persist_light_report(report: dict, output_json: str,
                          errors: list[dict]) -> None:
    try:
        out_dir = os.path.dirname(output_json)
        if out_dir:
            os.makedirs(out_dir, exist_ok=True)
        report["report_path"] = output_json
        write_json_artifact(output_json, report, indent=2)
        logger.info("轻量诊断完成, 报告: %s", output_json)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e, context='_persist_light_report:Exc')
        _record_step_error(errors, "save_report", e, "报告落盘")
        report.pop("report_path", None)
        report["status"] = _resolve_status(errors)
def run_lightweight_diagnosis(
    skill_dir: str = "",
    top_files: int = DEFAULT_TOP_FILES,
    output_json: str | None = None,
) -> dict:
    _dir = validated_warmed_root(skill_dir or os.getcwd())
    report: dict = {
        "skill_dir": _dir,
        "diagnosed_at": timestamp_human(),
    }
    errors: list[dict] = []
    _report_call_chain(report, _dir, errors)
    _report_antipatterns(report, _dir, top_files, errors)
    _report_quality(report, _dir, errors)
    report["verdict"] = _compute_light_verdict(report, errors)
    report["errors"] = errors
    report["status"] = _resolve_status(errors)
    if output_json:
        _persist_light_report(report, output_json, errors)
    return report

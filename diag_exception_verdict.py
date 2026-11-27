from __future__ import annotations

import ast
import hashlib
import logging
import os
import re
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Any

from jwsgj.diag_detector_findings import (
    is_retired_rule,
    map_external_severity,
)
from jwsgj.diag_detectors_registry import run_bounded_channel
from jwsgj.diag_exception_detection import (
    ExceptionPropagationAnalyzer,
    _canonical_exc_name,
    _class_exc_bases,
    collect_exception_scan_files,
    detect_resource_leaks_inline,
    exception_type_lineage,
    is_protocol_exc_site,
    load_source_and_tree,
    log_swallowed_entries,
    run_exception_miner_detector,
    run_tryceratops_detector,
    summarize_type_flow,
)
from jwsgj.diag_shared_ast_nodes import (
    TRY_STAR,
    definition_time_exprs,
    is_class_shaped_exc_name,
)
from jwsgj.diag_shared_source_core import (
    CONTEXT_ACCESS_ERRORS,
    read_source_with_fingerprint,
)
from jwsgj.diag_shared_source_core import (
    parse_py_file as _parse_py_file,
)
from jwsgj.diag_shared_source_scan import (
    is_suppressed,
    parse_suppressions,
)
from jwsgj.diag_types_normalize import (
    as_entry_list,
    coerce_line,
    dict_or_empty,
    signal_bool,
    text_or_empty,
)
from jwsgj.diag_types_vocab import (
    METHOD_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    is_backup_path,
    is_scan_py_name,
    is_test_file_path,
    prune_scan_dirnames,
    safe_relpath,
    scan_exclude_dirs,
)

logger = logging.getLogger(__name__)
__all__ = [
    "BY_DESIGN_SIGNAL_EXCEPTIONS",
    "EM_KNOWN_FP_PATTERNS",
    "EXEMPTION_AUDIT_REASONS",
    "EXEMPTION_CAUGHT",
    "EXEMPTION_CONTROL_FLOW",
    "EXEMPTION_DESIGN_SIGNAL",
    "EXEMPTION_TEST_PATH",
    "EXEMPTION_UNRESOLVED_TYPE",
    "assemble_exception_result",
    "caught_specific_types",
    "classify_static_exemption",
    "classify_swallowed_exemption",
    "d4_tc_entry",
    "is_by_design_signal_exception",
    "is_intentional_guard",
    "is_unresolved_exc_type_name",
    "run_exception_detector",
    "run_exception_layer",
    "safe_analyze_exceptions",
]
_BY_DESIGN_SIGNAL_EXCEPTION_TYPES = frozenset({
    "NotImplementedError", "AssertionError", "UnpicklingError",
    "ArgumentTypeError",
    "SystemExit",
})
_RE_RAISE_LABELS = frozenset({"bare re-raise", "re-raise variable"})
BY_DESIGN_SIGNAL_EXCEPTIONS = frozenset(
    _BY_DESIGN_SIGNAL_EXCEPTION_TYPES | _RE_RAISE_LABELS)
_GUARD_MSG_RE = re.compile(
    r"无效|不能为空|仅支持|不支持|被错误|已阻断|必须是|须为|需要|"
    r"收到|非法|不一致|非目录|未知|无法|未找到|无交集|退化|超出|失败|拒绝|"
    r"缺少|不存在|不可用|"
    r"[Ii]nvalid|[Nn]ot a directory|expects|must be|does not support|"
    r"closed file|exceeded max depth|unknown|cannot|could not|not found|"
    r"missing|degenerate|out of range|failed|unavailable"
)
_GUARD_VALUE_ERROR_TYPES = frozenset({
    "ValueError", "TypeError", "RuntimeError",
    "OSError", "FileExistsError", "IsADirectoryError",
    "NotADirectoryError", "PermissionError", "BlockingIOError",
    "InterruptedError", "ProcessLookupError", "TimeoutError",
    "ConnectionError", "ConnectionAbortedError", "ConnectionRefusedError",
    "ConnectionResetError", "BrokenPipeError",
})
_DESIGN_SIGNAL_NAME_STEMS = frozenset({
    "contract", "precondition", "postcondition", "invariant", "violation",
    "guard", "tamper", "provenance", "concurrent", "notwarmed", "notready",
    "invalid", "unsupported", "unavailable", "argument", "path",
})
_DEFAULT_FINDING_SEVERITY = "P2"
_RESOURCE_LEAK_RULE_ID = "RL-LEAK"
_CROSS_FILE_RULE_ID = "EX-CF-01"
_TRY_MALFORMED_RULE_ID = "TRY-UNKNOWN"
_TRY_CATEGORY = "exception_pattern"
_CROSS_FILE_CONFIDENCE = 0.70
_UNCAUGHT_CONFIDENCE = 0.75
_SWALLOWED_CONFIDENCE = 0.70
_RESOURCE_LEAK_CONFIDENCE = 0.65
_CROSS_FILE_EXTERNAL_SEVERITY = "medium"
_SWALLOWED_EXTERNAL_SEVERITY = "low"
def _confidence_or_default(value: Any, default: float) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return default
    return value if 0.0 <= value <= 1.0 else default
def _signal_type_tail(exc_type: Any) -> str:
    if not isinstance(exc_type, str):
        return ""
    return exc_type.strip().rsplit(".", 1)[-1]
def _is_design_signal_tail(tail: str) -> bool:
    if not tail:
        return False
    if tail in _BY_DESIGN_SIGNAL_EXCEPTION_TYPES:
        return True
    lowered = tail.lower()
    if not lowered.endswith(("error", "exception")):
        return False
    return any(stem in lowered for stem in _DESIGN_SIGNAL_NAME_STEMS)
def is_by_design_signal_exception(exc_type: Any) -> bool:
    tail = _signal_type_tail(exc_type)
    if tail in _RE_RAISE_LABELS:
        return True
    return _is_design_signal_tail(tail)
def is_intentional_guard(exc_type: str, message: str,
                          reraise_source: str = "") -> bool:
    tail = _signal_type_tail(exc_type)
    if _is_design_signal_tail(tail):
        return True
    if tail == "bare re-raise" and reraise_source:
        parts = [p.strip() for p in reraise_source.split("|") if p.strip()]
        return bool(parts) and all(
            _is_design_signal_tail(_signal_type_tail(p)) for p in parts)
    if tail in _GUARD_VALUE_ERROR_TYPES:
        return bool(_GUARD_MSG_RE.search(message or ""))
    return False
def is_unresolved_exc_type_name(raise_type) -> bool:
    if not isinstance(raise_type, str):
        return False
    name = raise_type.strip()
    if not name or name == "bare re-raise":
        return False
    if not all(part.isidentifier() for part in name.split(".")):
        return False
    return not is_class_shaped_exc_name(name)
EXEMPTION_TEST_PATH = "test_path"
EXEMPTION_DESIGN_SIGNAL = "design_signal"
EXEMPTION_CONTROL_FLOW = "control_flow"
EXEMPTION_UNRESOLVED_TYPE = "unresolved_type"
EXEMPTION_CAUGHT = "caught"
_SWALLOWED_EXEMPTION_BUCKETS = (
    EXEMPTION_TEST_PATH, EXEMPTION_DESIGN_SIGNAL, EXEMPTION_CONTROL_FLOW)
_CROSS_FILE_EXEMPTION_BUCKETS = (
    EXEMPTION_TEST_PATH, EXEMPTION_DESIGN_SIGNAL,
    EXEMPTION_UNRESOLVED_TYPE, EXEMPTION_CAUGHT)
EXEMPTION_AUDIT_REASONS = {
    EXEMPTION_TEST_PATH: "test",
    EXEMPTION_DESIGN_SIGNAL: "by_design",
    EXEMPTION_CONTROL_FLOW: "control_flow",
    EXEMPTION_UNRESOLVED_TYPE: "unresolved_type",
    EXEMPTION_CAUGHT: "caught",
}
def classify_static_exemption(filepath, exc_type) -> str | None:
    if is_test_file_path(filepath if isinstance(filepath, str) else ""):
        return EXEMPTION_TEST_PATH
    if is_by_design_signal_exception(exc_type):
        return EXEMPTION_DESIGN_SIGNAL
    return None
def classify_swallowed_exemption(entry) -> str | None:
    if not isinstance(entry, dict):
        return None
    bucket = classify_static_exemption(
        entry.get("filepath", ""), entry.get("raise_type", ""))
    if bucket is not None:
        return bucket
    return (EXEMPTION_CONTROL_FLOW
            if entry.get("swallow_kind") == "control_flow" else None)
def safe_analyze_exceptions(skill_dir: str, ctx=None, graph=None, source_paths=None) -> dict:
    try:
        return _analyze_all_exception_patterns(
            skill_dir, ctx=ctx, graph=graph, source_paths=source_paths)
    except Exception as e:
        logger.warning("safe_analyze_exceptions failed: %s", e, exc_info=True)
        return {}
@dataclass
class _ExceptionScanBundle:
    type_flow_entries: list = field(default_factory=list)
    tryceratops_findings: list = field(default_factory=list)
    em_findings: list = field(default_factory=list)
    leaks: list = field(default_factory=list)
    counters: dict = field(default_factory=dict)
    cross_file_findings: list = field(default_factory=list)
    exception_bases: dict = field(default_factory=dict)
def _exception_miner_summary(findings, exempt_test: int) -> dict:
    entries = as_entry_list(findings)
    by_pattern = defaultdict(int)
    for finding in entries:
        if not isinstance(finding, dict):
            continue
        by_pattern[str(finding.get('pattern') or 'unknown')] += 1
    return {
        'total': len(entries),
        'by_pattern': dict(by_pattern),
        'details': entries[:30],
        'exempt_test': exempt_test,
    }
def _resource_leak_summary(leaks, counters: dict) -> dict:
    return {
        "total": len(leaks),
        **{counter_key: counters.get(counter_key, 0)
           for counter_key in _LEAK_RESULT_TO_COUNTER.values()},
        "leaks": leaks,
        "score_penalty": min(len(leaks) * 2, 10),
    }
def _build_exception_summaries(bundle: _ExceptionScanBundle) -> dict:
    counters = bundle.counters
    log_swallowed_entries(bundle.type_flow_entries)
    return {
        "type_flow": summarize_type_flow(bundle.type_flow_entries),
        "tryceratops": bundle.tryceratops_findings,
        "tryceratops_exempt_test": counters.get("tc_exempt_test", 0),
        "tryceratops_exempt_protocol": counters.get("tc_exempt_protocol", 0),
        "tryceratops_exempt_selective": counters.get("tc_exempt_selective", 0),
        "exception_miner": _exception_miner_summary(
            bundle.em_findings, counters.get("em_exempt_test", 0)),
        "resource_leaks": _resource_leak_summary(bundle.leaks, counters),
        "cross_file": bundle.cross_file_findings or [],
    }
def _resolve_exception_scan_files(skill_dir: str, ctx=None,
                                  source_paths=None) -> list:
    if source_paths is not None:
        return collect_exception_scan_files(source_paths)
    ctx_files = getattr(ctx, "py_files", None) if ctx is not None else None
    if ctx_files is not None:
        return [fp for fp in ctx_files if not is_backup_path(fp)]
    return collect_exception_scan_files([skill_dir])
_LEAK_RESULT_TO_COUNTER = {
    "safe_with": "safe_with",
    "open_calls": "total_open_calls",
    "exempt_inline": "exempt_inline",
    "exempt_test": "exempt_test",
    "exempt_fd_closed": "exempt_fd_closed",
}
_EXEMPT_COUNTER_KEYS = (
    *_LEAK_RESULT_TO_COUNTER.values(),
    "tc_exempt_test", "em_exempt_test",
    "tc_exempt_protocol", "tc_exempt_selective",
)
def _scan_resource_leaks(tree, rel: str, counters: dict) -> list:
    result = detect_resource_leaks_inline(tree, rel)
    for result_key, counter_key in _LEAK_RESULT_TO_COUNTER.items():
        counters[counter_key] = result.get(result_key, 0)
    return result.get("leaks", [])
def _scan_one_file_domains(filepath, skill_dir, ctx, analyzer) -> dict | None:
    _source, tree = load_source_and_tree(filepath, ctx)
    if tree is None:
        return None
    rel = safe_relpath(filepath, skill_dir)
    _is_test_file = is_test_file_path(rel)
    type_flow_new = analyzer.analyze_file_preparsed(filepath, tree)
    tryceratops_new, tc_et, tc_p, tc_s = run_tryceratops_detector(
        tree, filepath, rel, _is_test_file)
    em_new, em_et = run_exception_miner_detector(
        tree, filepath, rel, _is_test_file)
    counters = dict.fromkeys(_EXEMPT_COUNTER_KEYS, 0)
    counters["tc_exempt_test"] = tc_et
    counters["tc_exempt_protocol"] = tc_p
    counters["tc_exempt_selective"] = tc_s
    counters["em_exempt_test"] = em_et
    leaks_new = _scan_resource_leaks(tree, rel, counters)
    return {"type_flow": type_flow_new, "tryceratops": tryceratops_new,
            "em": em_new, "leaks": leaks_new, "counters": counters,
            "exception_bases": _class_exc_bases(tree)}
def _analyze_all_exception_patterns(skill_dir: str, ctx=None, graph=None,
                                   source_paths=None) -> dict:
    py_files = _resolve_exception_scan_files(skill_dir, ctx, source_paths)
    analyzer = ExceptionPropagationAnalyzer(skill_dir)
    bundle = _ExceptionScanBundle(
        counters=dict.fromkeys(_EXEMPT_COUNTER_KEYS, 0))
    for filepath in py_files:
        chunk = _scan_one_file_domains(filepath, skill_dir, ctx, analyzer)
        if chunk is None:
            continue
        bundle.type_flow_entries.extend(chunk["type_flow"])
        bundle.tryceratops_findings.extend(chunk["tryceratops"])
        bundle.em_findings.extend(chunk["em"])
        bundle.leaks.extend(chunk["leaks"])
        for _k, _v in chunk["counters"].items():
            bundle.counters[_k] += _v
        bundle.exception_bases.update(chunk["exception_bases"])
    if graph is not None:
        bundle.cross_file_findings = _collect_cf_findings(
            bundle.type_flow_entries,
            _CrossFileIndex(graph, bundle.exception_bases))
    return _build_exception_summaries(bundle)
@dataclass(frozen=True)
class _RaiseSite:
    func: str
    file: str
    basename: str
    line: int
    exc_type: str
@dataclass
class _EscapeFrame:
    func: str
    memo_key: tuple[str, str, str]
    entry_stack: frozenset
    callers: Any
    polluted: bool = False
class _EscapeGraph:
    __slots__ = ("_callers", "_exc_bases", "_memo", "_proj_root",
                 "_span", "_try_map")
    def __init__(self, callers: dict, span: dict, try_map: dict,
                 proj_root: str, exc_bases: dict | None = None) -> None:
        self._memo: dict[tuple[str, str, str], bool] = {}
        self._callers = callers
        self._span = span
        self._try_map = try_map
        self._proj_root = proj_root
        self._exc_bases = exc_bases or {}
    def _has_try(self, caller: str, via_callee: str,
                 exc_type: str = "") -> bool:
        span = self._span.get(caller)
        if not span:
            return False
        fullpath, start, _end = span
        coverage = _load_file_try_map(
            fullpath, self._proj_root, self._try_map).get(start, {})
        callee_tail = via_callee.rsplit(".", 1)[-1]
        sites = coverage.get(callee_tail, ())
        if not exc_type:
            return bool(sites) and all(bool(site) for site in sites)
        return bool(sites) and all(
            _call_site_catches(exc_type, caught, self._exc_bases)
            for caught in sites)
    def escapes(self, func: str, entry_stack: frozenset,
                via_callee: str = "", exc_type: str = ""):
        memo = self._memo
        pending = [(func, via_callee, entry_stack)]
        frames: list[_EscapeFrame] = []
        returned = None
        while pending or frames:
            if pending:
                current, current_via, current_stack = pending.pop()
                memo_key = (current, current_via, exc_type)
                if memo_key in memo:
                    returned = memo[memo_key], False
                    continue
                if current in current_stack:
                    returned = False, True
                    continue
                if self._has_try(current, current_via, exc_type):
                    memo[memo_key] = False
                    returned = False, False
                    continue
                up_callers = self._callers.get(current, set())
                if not up_callers:
                    memo[memo_key] = True
                    returned = True, False
                    continue
                frames.append(_EscapeFrame(
                    current, memo_key, current_stack | {current},
                    iter(up_callers),
                ))
                returned = None
            if not frames:
                continue
            frame = frames[-1]
            if returned is not None:
                child_escapes, child_polluted = returned
                frame.polluted = frame.polluted or child_polluted
                if child_escapes:
                    memo[frame.memo_key] = True
                    frames.pop()
                    returned = True, frame.polluted
                    continue
                returned = None
            try:
                caller = next(frame.callers)
            except StopIteration:
                frames.pop()
                if not frame.polluted:
                    memo[frame.memo_key] = False
                returned = False, frame.polluted
                continue
            pending.append((caller, frame.func, frame.entry_stack))
        if returned is None:
            raise RuntimeError("异常逃逸图遍历未产生裁决")
        return returned
class _CrossFileIndex:
    def __init__(self, graph, exc_bases: dict | None = None) -> None:
        self.proj_root = str(getattr(graph, "project_root", "") or "")
        (self.func_to_file, self.func_to_span, self.spans_by_file,
         self.paths_by_basename) = _build_func_index(graph)
        self.callee_to_callers = _collect_callee_callers(graph)
        self.file_try_map: dict[
            str, dict[int, dict[str, list[frozenset[str]]]]] = {}
        self.escape = _EscapeGraph(
            self.callee_to_callers, self.func_to_span, self.file_try_map,
            self.proj_root, exc_bases)
        self._simple_index: dict[str, set] | None = None
        self.seen_pairs: set[tuple] = set()
    def simple_callers(self, simple_name: str) -> set:
        if self._simple_index is None:
            self._simple_index = {
                callee: set(caller_set)
                for callee, caller_set in self.callee_to_callers.items()
                if "." not in callee
            }
        return self._simple_index.get(simple_name, set())
    def raise_func_callers(self, raise_func: str) -> set:
        callers = set(self.callee_to_callers.get(raise_func, set()))
        simple_name = raise_func.rsplit(".", maxsplit=1)[-1]
        _dunder = simple_name.startswith("__") and simple_name.endswith("__")
        if simple_name != raise_func and not _dunder:
            callers |= self.simple_callers(simple_name)
        return callers
def _norm_path_key(fp: str) -> str:
    raw = str(fp or "")
    if not raw:
        return ""
    return os.path.normcase(os.path.normpath(raw)).replace(os.sep, "/")
def _paths_same_file(p1: str, p2: str) -> bool:
    n1 = _norm_path_key(p1)
    n2 = _norm_path_key(p2)
    if not n1 or not n2:
        return False
    if n1 == n2:
        return True
    return n1.endswith("/" + n2) or n2.endswith("/" + n1)
def _is_catching_try(node) -> bool:
    return (isinstance(node, (ast.Try, TRY_STAR))
            and bool(getattr(node, "handlers", ())))
def _call_target_tail(node: ast.Call) -> str:
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    return ""
_CATCH_ALL = "*"
def _exact_except_type_names(exc_node, *, unknown_as_catch_all=False) -> list[str]:
    nodes = exc_node.elts if isinstance(exc_node, ast.Tuple) else (exc_node,)
    names: list[str] = []
    for node in nodes:
        if isinstance(node, ast.Name):
            names.append(node.id)
        elif isinstance(node, ast.Attribute):
            names.append(node.attr)
        elif unknown_as_catch_all:
            names.append(_CATCH_ALL)
    return names
def _body_call_coverage(func_node, *, with_exception_types=False) -> dict:
    protected_calls: dict[str, list[frozenset[str]]] = {}
    stack = [(stmt, frozenset()) for stmt in reversed(func_node.body)]
    deferred = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
    while stack:
        current, protected = stack.pop()
        if isinstance(current, deferred):
            for site in reversed(definition_time_exprs(current)):
                stack.append((site, protected))
            continue
        if isinstance(current, ast.GeneratorExp):
            # 仅最外层迭代式在创建生成器时立即求值；主体、筛选条件和
            # 后续迭代式均延迟到迭代时执行，不能继承创建点的 try 保护。
            children = [(current.elt, frozenset())]
            for index, comprehension in enumerate(current.generators):
                children.append((
                    comprehension.iter,
                    protected if index == 0 else frozenset()))
                children.extend(
                    (condition, frozenset())
                    for condition in comprehension.ifs)
            for child, child_protected in reversed(children):
                stack.append((child, child_protected))
            continue
        if isinstance(current, ast.Call):
            tail = _call_target_tail(current)
            if tail:
                protected_calls.setdefault(tail, []).append(protected)
        if _is_catching_try(current):
            caught = set(protected)
            for handler in current.handlers:
                if handler.type is None:
                    caught.add(_CATCH_ALL)
                else:
                    caught.update(_exact_except_type_names(
                        handler.type, unknown_as_catch_all=True))
            for child in reversed(current.body):
                stack.append((child, frozenset(caught)))
            for group in (current.handlers, current.orelse, current.finalbody):
                for child in reversed(group):
                    stack.append((child, protected))
            continue
        for child in reversed(list(ast.iter_child_nodes(current))):
            stack.append((child, protected))
    if with_exception_types:
        return protected_calls
    return {
        name: all(bool(site) for site in sites)
        for name, sites in protected_calls.items()
    }
def _call_site_catches(exc_type: str, caught: frozenset[str],
                       exc_bases: dict | None = None) -> bool:
    if not caught:
        return False
    if _CATCH_ALL in caught or "BaseException" in caught:
        return True
    lineage = exception_type_lineage(
        _signal_type_tail(exc_type), exc_bases)
    canonical_caught = {_canonical_exc_name(name) for name in caught}
    if lineage & canonical_caught:
        return True
    # 谱系未触达 BaseException 时无法证明它不是 Exception 子类（基类可能来自
    # 标准库/第三方，不在内建基类表里）；``except Exception`` 按 Python 惯例
    # 视为捕获，与 diag_exception_detection._lineage_catches 同口径。按
    # ``len(lineage) == 1`` 判定会把 DbError(sqlite3.Error) 这类多级自定义
    # 异常误判为未被 except Exception 捕获，进而伪报跨文件逃逸。
    return "Exception" in canonical_caught and "BaseException" not in lineage
def _build_func_index(graph):
    func_to_file: dict[str, str] = {}
    func_to_span: dict[str, tuple[str, int, int]] = {}
    spans_by_file: dict[str, list[tuple[str, int, int]]] = {}
    paths_by_basename: dict[str, list[str]] = {}
    if hasattr(graph, "functions"):
        for func_name, fnode in graph.functions.items():
            filepath = getattr(fnode, "filepath", "") or getattr(fnode, "file", "")
            if not filepath or is_backup_path(filepath):
                continue
            fullpath = _norm_path_key(filepath)
            func_to_file[func_name] = fullpath
            _bucket = paths_by_basename.setdefault(
                os.path.basename(fullpath), [])
            if fullpath not in _bucket:
                _bucket.append(fullpath)
            start = getattr(fnode, "start_line", 0) or 0
            end = getattr(fnode, "end_line", 0) or 0
            func_to_span[func_name] = (fullpath, start, end)
            if start > 0:
                spans_by_file.setdefault(fullpath, []).append((func_name, start, end))
    return func_to_file, func_to_span, spans_by_file, paths_by_basename
def _collect_callee_callers(graph) -> dict:
    callee_to_callers: dict[str, set[str]] = {}
    _index = getattr(graph, "callers", None)
    if isinstance(_index, dict):
        for callee, callers in _index.items():
            try:
                callee_to_callers[callee] = set(callers) if callers else set()
            except TypeError as te:
                logger.debug("callers 非可迭代，跳过 %s: %s", callee, te)
                continue
    for edge in getattr(graph, "calls", None) or ():
        caller = getattr(edge, "caller_func", "")
        callee = getattr(edge, "callee_func", "")
        if caller and callee:
            callee_to_callers.setdefault(callee, set()).add(caller)
    return callee_to_callers
def _resolve_try_map_source(fullpath: str, proj_root: str) -> str:
    if not fullpath or os.path.isabs(fullpath):
        return fullpath
    if proj_root:
        anchored = os.path.join(proj_root, fullpath)
        if os.path.isfile(anchored):
            return anchored
    return fullpath
def _load_file_try_map(fullpath: str, proj_root: str,
                       file_try_map: dict) -> dict:
    if fullpath in file_try_map:
        return file_try_map[fullpath]
    result: dict[int, dict[str, bool]] = {}
    file_try_map[fullpath] = result
    _src = _resolve_try_map_source(fullpath, proj_root)
    if not _src or not os.path.isfile(_src):
        return result
    _tree = _parse_py_file(_src, quiet=True)[1]
    if _tree is None:
        return result
    for node in walk_nodes(_tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            result[node.lineno] = _body_call_coverage(
                node, with_exception_types=True)
    return result
def _span_covers_line(span: tuple[str, int, int], line: int) -> bool:
    _fname, start, end = span
    return start > 0 and start <= line and (end == 0 or line <= end)
def _span_width(span: tuple[str, int, int]) -> float:
    _fname, start, end = span
    return end - start if end >= start > 0 else float("inf")
def _resolve_enclosing(entry_path: str, line: int,
                       paths_by_basename: dict, spans_by_file: dict) -> str:
    candidates = paths_by_basename.get(
        os.path.basename(_norm_path_key(entry_path)), [])
    matched = [p for p in candidates if _paths_same_file(p, entry_path)]
    if not matched:
        return ""
    entry_key = _norm_path_key(entry_path)
    exact = [p for p in matched if _norm_path_key(p) == entry_key]
    pool = exact or matched
    if len(pool) != 1:
        return ""
    best = ""
    best_span = None
    for span_entry in spans_by_file.get(pool[0], ()):
        if not _span_covers_line(span_entry, line):
            continue
        width = _span_width(span_entry)
        if best_span is None or width < best_span:
            best, best_span = span_entry[0], width
    return best
def _build_cf_finding(site: _RaiseSite, caller: str, caller_full: str,
                      call_chain: tuple[str, ...] = ()) -> dict:
    caller_display = os.path.basename(caller_full)
    propagation_path = (
        " -> ".join(call_chain) if call_chain else f"{site.func} -> {caller}")
    return {
        "rule_id": _CROSS_FILE_RULE_ID,
        "severity": _CROSS_FILE_EXTERNAL_SEVERITY,
        "confidence": _CROSS_FILE_CONFIDENCE,
        "message": (
            f"异常 {site.exc_type} 从 {site.basename}:{site.func} "
            f"跨文件传播到 {caller_display}:{caller} "
            f"(沿调用链无处理器，可逃逸至顶层入口)"
        ),
        "file": site.file,
        "line": site.line,
        "source": "exception_cross_file",
        "propagation_path": propagation_path,
        "raise_file": site.basename,
        "caller_file": caller_full,
        "exc_type": site.exc_type,
    }
def _iter_cf_caller_findings(site: _RaiseSite, caller_set,
                             idx: _CrossFileIndex) -> list:
    out: list[dict] = []
    pending = [(site.func, caller, (site.func,))
               for caller in sorted(caller_set)]
    visited_edges: set[tuple[str, str]] = set()
    for current, caller, call_chain in pending:
        edge = (current, caller)
        if edge in visited_edges:
            continue
        visited_edges.add(edge)
        caller_full = idx.func_to_file.get(caller, "")
        if not caller_full or is_test_file_path(caller_full):
            continue
        if _paths_same_file(caller_full, site.file):
            if idx.escape._has_try(caller, current, site.exc_type):
                continue
            pending.extend(
                (caller, upstream, (*call_chain, caller))
                for upstream in sorted(idx.raise_func_callers(caller))
            )
            continue
        _escapes, _ = idx.escape.escapes(
            caller, frozenset(), current, site.exc_type)
        if not _escapes:
            continue
        dedup_key = (site.func, caller, site.file,
                     site.line, site.exc_type)
        if dedup_key in idx.seen_pairs:
            continue
        idx.seen_pairs.add(dedup_key)
        out.append(_build_cf_finding(
            site, caller, caller_full, (*call_chain, caller)))
    return out
def _process_cf_entry(entry, idx: _CrossFileIndex) -> list:
    raise_file = getattr(entry, "filepath", "") or ""
    if not raise_file or is_test_file_path(raise_file):
        return []
    raise_line = coerce_line(getattr(entry, "raise_line", 0))
    exc_type = getattr(entry, "raise_type", "") or "?"
    if getattr(entry, "raise_transparent", False):
        return []
    if exc_type in _RE_RAISE_LABELS:
        return []
    if is_unresolved_exc_type_name(exc_type):
        return []
    raise_func = _resolve_enclosing(raise_file, raise_line,
                                    idx.paths_by_basename, idx.spans_by_file)
    if not raise_func:
        return []
    if is_protocol_exc_site(raise_func, exc_type):
        return []
    if is_intentional_guard(exc_type, getattr(entry, "message", "") or "",
                              getattr(entry, "except_type", "") or ""):
        return []
    site = _RaiseSite(raise_func, raise_file, os.path.basename(raise_file),
                      raise_line, exc_type)
    return _iter_cf_caller_findings(
        site, idx.raise_func_callers(raise_func), idx)
def _collect_cf_findings(type_flow_entries, idx: _CrossFileIndex) -> list:
    findings: list[dict] = []
    for entry in type_flow_entries:
        if coerce_line(getattr(entry, "except_line", 0)) > 0:
            continue
        findings.extend(_process_cf_entry(entry, idx))
    return findings
_TC_KNOWN_FP_PATTERNS = frozenset({"try003_raise_vanilla_args"})
EM_KNOWN_FP_PATTERNS = frozenset({
    "em001_nested_try_in_except",
    "em004_exception_control_flow",
})
_TC_RETIRED_CAP = 200
_D4_EX_SEV_MAP = {"high": "P1", "medium": "P2", "low": "P3"}
_D4_TRY_SEV_MAP = {"high": "P2", "medium": "P3", "low": "P3"}
_D1_DATA_CHANNEL_SHAPES = {
    "resource_leaks": dict,
    "type_flow": dict,
    "tryceratops": list,
    "cross_file": list,
}
_D1_DATA_CHANNEL_KEYS = tuple(_D1_DATA_CHANNEL_SHAPES)
_AUDIT_RULES = ("EX-UNCAUGHT", "EX-SWALLOWED", "EX-CF-01", "TRY-*")
_AUDIT_SAMPLE_CAP = 20
_AUDIT_REASONS = (
    EXEMPTION_AUDIT_REASONS[EXEMPTION_TEST_PATH],
    EXEMPTION_AUDIT_REASONS[EXEMPTION_DESIGN_SIGNAL],
    EXEMPTION_AUDIT_REASONS[EXEMPTION_CAUGHT],
    EXEMPTION_AUDIT_REASONS[EXEMPTION_CONTROL_FLOW],
    EXEMPTION_AUDIT_REASONS[EXEMPTION_UNRESOLVED_TYPE],
)
def _make_filter_auditor(filter_audit: dict, sample_cap: int):
    def _audit(rule: str, reason: str, sample: dict) -> None:
        a = filter_audit.get(rule)
        if a is None or reason not in _AUDIT_REASONS:
            return
        a[reason] += 1
        samples = a["samples"].get(reason)
        if samples is not None and len(samples) < sample_cap:
            samples.append(sample)
    return _audit
def _d1_metrics_payload(result: dict, filter_audit: dict,
                        tc_retired: list) -> dict:
    return {
        **result,
        "filter_audit": filter_audit,
        "tryceratops_retired": tc_retired[:_TC_RETIRED_CAP] + (
            [{"truncated": True, "total": len(tc_retired)}]
            if len(tc_retired) > _TC_RETIRED_CAP else []),
    }
def _new_audit() -> dict:
    return {**dict.fromkeys(_AUDIT_REASONS, 0),
            "samples": {r: [] for r in _AUDIT_REASONS}}
def _degraded_result(summary: str, **extra) -> tuple:
    return "degraded", {"status": "warn", "summary": summary,
                        "findings": [], **extra}
def _d4_guard_verdict(result) -> tuple:
    if not result:
        return _degraded_result(
            "D4 异常/资源泄漏分析未产出结构化结果（分析失败降级，非无发现）")
    if not isinstance(result, dict):
        return _degraded_result(
            "D4 异常/资源泄漏分析结果不可识别（顶层非结构化形态，降级，非无发现）",
            metrics={"raw_input": result})
    if result.get("status") is not None and result.get("findings") is not None:
        return "original", result
    if not any(k in result for k in _D1_DATA_CHANNEL_KEYS):
        return _degraded_result(
            "D4 异常/资源泄漏分析结果不可识别（零数据通道键，降级，非无发现）",
            metrics=dict(result))
    malformed = [
        key for key, shape in _D1_DATA_CHANNEL_SHAPES.items()
        if key in result and not isinstance(result[key], shape)
    ]
    if malformed:
        return _degraded_result(
            "D4 异常/资源泄漏分析通道形态异常（降级，非无发现）: "
            + ", ".join(malformed),
            metrics=dict(result))
    return None, None
def _rl_suppressed(leak: dict, cache: dict, skill_dir: str = "") -> bool:
    filepath = leak.get("file")
    line = leak.get("line")
    if not isinstance(filepath, str) or not filepath:
        return False
    if not os.path.isabs(filepath) and skill_dir:
        filepath = os.path.join(skill_dir, filepath)
    if not (isinstance(line, int) and not isinstance(line, bool) and line > 0):
        return False
    sp = cache.get(filepath)
    if sp is None:
        source, _fingerprint = read_source_with_fingerprint(filepath)
        sp = parse_suppressions(source) if source is not None else {}
        cache[filepath] = sp
    if not sp:
        return False
    return is_suppressed(sp, line, leak.get("rule_id") or _RESOURCE_LEAK_RULE_ID)
def _d4_rl_findings(rl: dict, skill_dir: str = "") -> list:
    out: list = []
    _supp_cache: dict = {}
    for leak in as_entry_list(rl.get("leaks")):
        if not isinstance(leak, dict):
            continue
        if _rl_suppressed(leak, _supp_cache, skill_dir):
            continue
        f = dict(leak)
        f["rule_id"] = text_or_empty(f.get("rule_id")) or _RESOURCE_LEAK_RULE_ID
        f["severity"] = map_external_severity(
            f.get("severity"), _D4_EX_SEV_MAP,
            fallback=_DEFAULT_FINDING_SEVERITY)
        f["confidence"] = _confidence_or_default(
            f.get("confidence"), _RESOURCE_LEAK_CONFIDENCE)
        f["message"] = text_or_empty(f.get("message")) or (
            "资源泄漏: open() @ " + str(leak.get("file", "?"))
            + ":" + str(leak.get("line", "?")))
        out.append(f)
    return out
def _caught_type_hit(exc_type, caught: frozenset) -> bool:
    tail = _signal_type_tail(exc_type)
    if not tail or not caught:
        return False
    canonical_caught = {_canonical_exc_name(name) for name in caught}
    return bool(exception_type_lineage(tail) & canonical_caught)
def _tf_sample(e: dict, raise_type: str) -> dict:
    return {"exc": raise_type, "file": e.get("filepath", ""),
            "line": coerce_line(e.get("raise_line"))}
def _tf_exempt_reason(e: dict, rule: str, audit) -> tuple[str, str | None]:
    _rt = text_or_empty(e.get("raise_type"))
    _bucket = classify_static_exemption(e.get("filepath", ""), _rt)
    if _bucket is None:
        return _rt, None
    audit(rule, EXEMPTION_AUDIT_REASONS[_bucket], _tf_sample(e, _rt))
    return _rt, _bucket
def _ex_finding(rule_id: str, label: str, raise_type: str, e: dict,
                confidence: float, *, line_key: str = "raise_line") -> dict:
    _file = e.get("filepath", "")
    _line = coerce_line(e.get(line_key))
    return {
        "rule_id": rule_id,
        "severity": map_external_severity(
            e.get("severity"), _D4_EX_SEV_MAP,
            fallback=_DEFAULT_FINDING_SEVERITY),
        "confidence": confidence,
        "message": f"{label}: {raise_type or '?'}",
        "file": _file,
        "line": _line,
    }
def _tf_uncaught_entry(e: dict, audit, ensure_caught) -> dict | None:
    _rt, _exempt = _tf_exempt_reason(e, "EX-UNCAUGHT", audit)
    if _exempt:
        return None
    _samp = _tf_sample(e, _rt)
    if signal_bool(e.get("raise_transparent")):
        audit("EX-UNCAUGHT", EXEMPTION_AUDIT_REASONS[EXEMPTION_DESIGN_SIGNAL], _samp)
        return None
    if is_intentional_guard(_rt, text_or_empty(e.get("raise_msg"))):
        audit("EX-UNCAUGHT", EXEMPTION_AUDIT_REASONS[EXEMPTION_DESIGN_SIGNAL], _samp)
        return None
    if is_unresolved_exc_type_name(_rt):
        audit("EX-UNCAUGHT", EXEMPTION_AUDIT_REASONS[EXEMPTION_UNRESOLVED_TYPE],
              _samp)
        return None
    if _caught_type_hit(_rt, ensure_caught()):
        audit("EX-UNCAUGHT", EXEMPTION_AUDIT_REASONS[EXEMPTION_CAUGHT], _samp)
        return None
    return _ex_finding(
        "EX-UNCAUGHT", "未捕获异常", _rt, e, _UNCAUGHT_CONFIDENCE)
def _tf_swallowed_entry(e: dict, audit) -> dict | None:
    _rt = text_or_empty(e.get("raise_type"))
    _bucket = classify_swallowed_exemption(e)
    if _bucket is not None:
        audit("EX-SWALLOWED", EXEMPTION_AUDIT_REASONS[_bucket],
              _tf_sample(e, _rt))
        return None
    return _ex_finding(
        "EX-SWALLOWED", "异常被吞没", _rt, e, _SWALLOWED_CONFIDENCE,
        line_key="except_line")
def _d4_tf_findings(tf: dict, audit, ensure_caught) -> list:
    out: list = []
    for e in as_entry_list(tf.get("entries")):
        if not isinstance(e, dict):
            continue
        if signal_bool(e.get("is_swallowed")):
            _entry = _tf_swallowed_entry(e, audit)
        elif coerce_line(e.get("except_line")) == 0:
            _entry = _tf_uncaught_entry(e, audit, ensure_caught)
        else:
            continue
        if _entry is not None:
            out.append(_entry)
    return out
def _tc_retired_entry(f: dict, rid: str, pat: str, **mark) -> dict:
    rec = {"rule_id": rid, "pattern": pat,
           "file": f.get("file"), "line": f.get("line"),
           "severity": f.get("severity"),
           "reason": f.get("reason")}
    rec.update(mark)
    return rec
def _d4_tc_channel(f_list, skill_dir: str, audit) -> tuple:
    tc_retired: list[dict] = []
    out: list = []
    suppression_cache: dict = {}
    for f in as_entry_list(f_list):
        if not isinstance(f, dict):
            continue
        _kind, _entry = d4_tc_entry(
            f, skill_dir, audit, suppression_cache=suppression_cache)
        if _kind == "keep":
            out.append(_entry)
        elif _kind == "retired":
            tc_retired.append(_entry)
    return out, tc_retired
def _entry_file(entry: dict) -> str:
    return str(entry.get("file", "") or entry.get("filepath", "") or "")
_TRY_CONFIDENCE = 0.70
def _tryceratops_rule_id(f: dict) -> str:
    raw = f.get("rule_id")
    rid = raw.strip() if isinstance(raw, str) else ""
    if rid:
        return rid
    pattern = str(f.get("pattern") or "").strip()
    return f"TRY-{pattern}" if pattern else ""
def _prepare_tryceratops_entry(f: dict, rule_id: str) -> dict:
    entry = dict(f)
    entry["rule_id"] = rule_id
    entry["message"] = (
        text_or_empty(entry.get("message"))
        or text_or_empty(entry.get("reason"))
    )
    entry["severity"] = map_external_severity(
        entry.get("severity"), _D4_TRY_SEV_MAP,
        fallback=_DEFAULT_FINDING_SEVERITY)
    entry["confidence"] = _confidence_or_default(
        entry.get("confidence"), _TRY_CONFIDENCE)
    entry["category"] = text_or_empty(entry.get("category")) or _TRY_CATEGORY
    return entry
def _tc_known_fp(f: dict, pattern: str, rule_id: str, skill_dir: str,
                 suppression_cache: dict | None = None) -> bool:
    if pattern in _TC_KNOWN_FP_PATTERNS:
        return True
    probe = dict(f)
    identifiers = [rule_id]
    if pattern and pattern not in identifiers:
        identifiers.append(pattern)
    cache = suppression_cache if suppression_cache is not None else {}
    for identifier in identifiers:
        probe["rule_id"] = identifier
        if _rl_suppressed(probe, cache, skill_dir):
            return True
    return False
def d4_tc_entry(f: dict, skill_dir: str, audit, *,
                suppression_cache: dict | None = None) -> tuple:
    _pat = str(f.get("pattern") or "").strip()
    _rid = _tryceratops_rule_id(f)
    if not _rid:
        return "retired", _tc_retired_entry(
            f, _TRY_MALFORMED_RULE_ID, _pat, malformed=True)
    if _tc_known_fp(f, _pat, _rid, skill_dir, suppression_cache):
        return "retired", _tc_retired_entry(f, _rid, _pat)
    if is_retired_rule(_rid):
        return "retired", _tc_retired_entry(f, _rid, _pat, retired_rule=True)
    f_entry = _prepare_tryceratops_entry(f, _rid)
    _tc_file = _entry_file(f_entry)
    if is_test_file_path(_tc_file):
        audit("TRY-*", EXEMPTION_AUDIT_REASONS[EXEMPTION_TEST_PATH],
              {"rule": _rid, "file": _tc_file,
               "line": f_entry.get("line", 0)})
        return "skip", None
    return "keep", f_entry
def _cross_file_exemption(f: dict, ensure_caught) -> tuple[str, str] | None:
    exc_type = text_or_empty(f.get("exc_type"))
    for path_key in ("file", "caller_file"):
        if is_test_file_path(f.get(path_key, "")):
            return EXEMPTION_TEST_PATH, exc_type
    if is_by_design_signal_exception(exc_type):
        return EXEMPTION_DESIGN_SIGNAL, exc_type
    if is_unresolved_exc_type_name(exc_type):
        return EXEMPTION_UNRESOLVED_TYPE, exc_type
    if _caught_type_hit(exc_type, ensure_caught()):
        return EXEMPTION_CAUGHT, exc_type
    return None
def _d4_cf_findings(cf_raw, audit, ensure_caught) -> list:
    out: list = []
    for f in as_entry_list(cf_raw):
        if not (isinstance(f, dict) and f.get("rule_id")):
            continue
        _exempt = _cross_file_exemption(f, ensure_caught)
        if _exempt is not None:
            _bucket, _exc = _exempt
            audit(_CROSS_FILE_RULE_ID, EXEMPTION_AUDIT_REASONS[_bucket],
                  {"exc": _exc,
                   "path": f"{f.get('file', '')} -> "
                           f"{f.get('caller_file', '')}"})
            continue
        f_entry = dict(f)
        f_entry["line"] = coerce_line(f_entry.get("line"))
        f_entry["severity"] = map_external_severity(
            f_entry.get("severity"), _D4_EX_SEV_MAP,
            fallback=_DEFAULT_FINDING_SEVERITY)
        f_entry["confidence"] = _confidence_or_default(
            f_entry.get("confidence"), _CROSS_FILE_CONFIDENCE)
        out.append(f_entry)
    return out
_STATUS_ORDER = {"pass": 0, "warn": 1, "fail": 2, "error": 3}
_CAUGHT_TYPES_CACHE_MAX = 32
_caught_types_cache: dict[str, tuple[tuple, frozenset]] = {}
def _prune_caught_scan_dirs(dirs: list, skill_dir: str) -> None:
    skip = {str(n).lower() for n in scan_exclude_dirs(skill_dir)}
    prune_scan_dirnames(dirs, skip)
def _iter_caught_scan_py_files(skill_dir: str):
    for root, dirs, files in os.walk(skill_dir):
        _prune_caught_scan_dirs(dirs, skill_dir)
        for fn in files:
            if not is_scan_py_name(fn):
                continue
            path = os.path.join(root, fn)
            rel = os.path.relpath(path, skill_dir)
            if not is_test_file_path(rel):
                yield path
def _dir_py_content_token(skill_dir: str) -> tuple:
    token: list = []
    for p in _iter_caught_scan_py_files(skill_dir):
        digest = hashlib.sha256()
        try:
            with open(p, "rb") as source_file:
                for chunk in iter(lambda: source_file.read(1024 * 1024), b""):
                    digest.update(chunk)
        except OSError as e:
            logger.debug("文件内容探测失败（跳过）: %s: %s", p, e)
            continue
        token.append((os.path.relpath(p, skill_dir), digest.digest()))
    return tuple(sorted(token))
def _load_caught_tree(path: str, cache=None):
    if cache is not None and hasattr(cache, "get_ast"):
        try:
            tree = cache.get_ast(path)
        except CONTEXT_ACCESS_ERRORS as _e:
            log_swallowed(__name__, _e, context='caught_specific_types:_CTX_ACCESS_ERRORS')
            return None
        if tree is not None:
            return tree
    return _parse_py_file(path, quiet=True)[1]
_BROAD_EXC_NAMES = frozenset({"Exception", "BaseException"})
def _collect_exact_except_types(tree, caught: set) -> None:
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ExceptHandler) or node.type is None:
            continue
        caught.update(
            name for name in _exact_except_type_names(node.type)
            if name not in _BROAD_EXC_NAMES)
def caught_specific_types(skill_dir: str, cache=None) -> frozenset:
    key = os.path.normcase(os.path.abspath(skill_dir))
    token = _dir_py_content_token(skill_dir)
    cached = _caught_types_cache.get(key)
    if cached is not None and cached[0] == token:
        return cached[1]
    caught: set[str] = set()
    exception_bases: dict[str, tuple[str, ...]] = {}
    for path in _iter_caught_scan_py_files(skill_dir):
        tree = _load_caught_tree(path, cache)
        if tree is None:
            continue
        _collect_exact_except_types(tree, caught)
        exception_bases.update(_class_exc_bases(tree))
    canonical_caught = {_canonical_exc_name(name) for name in caught}
    covered_custom_types = {
        name for name in exception_bases
        if exception_type_lineage(name, exception_bases) & canonical_caught
    }
    caught.update(covered_custom_types)
    result = frozenset(caught)
    if len(_caught_types_cache) >= _CAUGHT_TYPES_CACHE_MAX:
        _caught_types_cache.clear()
    _caught_types_cache[key] = (token, result)
    return result
def _caught_provider(skill_dir: str, cache=None):
    _caught_set: frozenset | None = None
    def _ensure_caught_set() -> frozenset:
        nonlocal _caught_set
        if _caught_set is None:
            _caught_set = caught_specific_types(skill_dir, cache)
        return _caught_set
    return _ensure_caught_set
def assemble_exception_result(result: dict | None, skill_dir: str,
                              cache=None) -> dict:
    _verdict, _payload = _d4_guard_verdict(result)
    if _verdict is not None:
        return _payload
    filter_audit = {rule: _new_audit() for rule in _AUDIT_RULES}
    _audit = _make_filter_auditor(filter_audit, _AUDIT_SAMPLE_CAP)
    ensure_caught = _caught_provider(skill_dir, cache)
    findings: list[dict] = []
    rl = dict_or_empty(result.get("resource_leaks"))
    findings.extend(_d4_rl_findings(rl, skill_dir))
    tf = dict_or_empty(result.get("type_flow"))
    findings.extend(_d4_tf_findings(tf, _audit, ensure_caught))
    _tc_new, tc_retired = _d4_tc_channel(
        result.get("tryceratops"), skill_dir, _audit)
    findings.extend(_tc_new)
    findings.extend(_d4_cf_findings(
        result.get("cross_file"), _audit, ensure_caught))
    total_leaks = rl.get("total", 0)
    uncaught = tf.get("total_uncaught", 0)
    status = "warn" if findings else "pass"
    _upstream = result.get("status")
    if (isinstance(_upstream, str) and _upstream in _STATUS_ORDER
            and _STATUS_ORDER[_upstream] > _STATUS_ORDER[status]):
        status = _upstream
    score = max(30, 100 - len(findings))
    summary = (f"异常/资源泄漏分析: {len(findings)}项发现, "
               f"资源泄漏{total_leaks}, 未捕获异常(原始){uncaught}")
    return {
        "status": status,
        "score": score,
        "summary": summary,
        "findings": findings,
        "metrics": _d1_metrics_payload(result, filter_audit, tc_retired),
    }
def _inject_swallowed_exception_entries(report, type_flow: dict) -> dict:
    _sw_exempt = dict.fromkeys(_SWALLOWED_EXEMPTION_BUCKETS, 0)
    if not isinstance(type_flow, dict):
        return _sw_exempt
    for entry in as_entry_list(type_flow.get("entries")):
        if not isinstance(entry, dict):
            continue
        if signal_bool(entry.get("is_swallowed")):
            _bucket = classify_swallowed_exemption(entry)
            if _bucket is not None:
                _sw_exempt[_bucket] += 1
                continue
            report.add_confirmed_entry(
                {
                    "severity": entry.get(
                        "severity", _SWALLOWED_EXTERNAL_SEVERITY),
                    "filepath": entry.get("filepath", ""),
                    "line": coerce_line(entry.get("except_line")),
                    "name": entry.get("raise_type", ""),
                    "message": entry.get("message", ""),
                    "suggestion": entry.get("suggestion", ""),
                },
                blindspot_type="exception_swallow",
                confidence_reason="exception swallowing detected",
            )
    return _sw_exempt
def _log_injection_exemptions(sw_exempt: dict, cf_exempt: dict) -> None:
    if any(sw_exempt.values()):
        logger.info(
            "[盲区] 吞没注入豁免（D4 同口径）: 测试路径=%d 设计信号=%d 控制流=%d",
            sw_exempt["test_path"], sw_exempt["design_signal"],
            sw_exempt["control_flow"])
    if any(cf_exempt.values()):
        logger.info(
            "[盲区] 跨文件异常注入豁免（D4 同口径）: "
            "测试路径=%d 设计信号=%d 未解析类型=%d 项目捕获=%d",
            cf_exempt[EXEMPTION_TEST_PATH],
            cf_exempt[EXEMPTION_DESIGN_SIGNAL],
            cf_exempt[EXEMPTION_UNRESOLVED_TYPE], cf_exempt[EXEMPTION_CAUGHT])
def _inject_cross_file_exception_entries(report, project_root, ctx,
                                         exc_result: dict) -> dict:
    _cf_exempt = dict.fromkeys(_CROSS_FILE_EXEMPTION_BUCKETS, 0)
    if not isinstance(exc_result, dict):
        return _cf_exempt
    _caught_exc_types = None
    def _ensure_caught() -> frozenset:
        nonlocal _caught_exc_types
        if _caught_exc_types is None:
            _caught_exc_types = caught_specific_types(project_root, ctx)
        return _caught_exc_types
    for cf in as_entry_list(exc_result.get("cross_file")):
        if not isinstance(cf, dict):
            continue
        _exempt = _cross_file_exemption(cf, _ensure_caught)
        if _exempt is not None:
            _cf_exempt[_exempt[0]] += 1
            continue
        report.add_confirmed_entry(
            {
                "severity": cf.get(
                    "severity", _CROSS_FILE_EXTERNAL_SEVERITY),
                "filepath": cf.get("file", ""),
                "line": coerce_line(cf.get("line")),
                "name": cf.get("propagation_path", ""),
                "message": cf.get("message", ""),
                "suggestion": "确保调用方对跨文件传播的异常有适当处理",
            },
            blindspot_type="exception_cross_file",
            confidence_reason="cross-file exception propagation detected via call graph",
        )
    return _cf_exempt
def run_exception_layer(report, project_root, call_graph, source_paths, ctx):
    try:
        exc_result = safe_analyze_exceptions(
            project_root, ctx=ctx, graph=call_graph, source_paths=source_paths,
        )
        if not isinstance(exc_result, dict) or not exc_result:
            logger.warning(
                "[盲区] 异常传播分析失败(该层发现不可用): 空结果哨兵，不计入零发现")
            logger.info("       异常传播: 分析失败（降级，该层发现不可用，非零发现）")
            return None
        type_flow = exc_result.get("type_flow") or {}
        if not isinstance(type_flow, dict):
            logger.warning(
                "[盲区] type_flow 契约外形态（%s），降级空表",
                type(type_flow).__name__)
            type_flow = {}
        exc_sum = {
            "total_raises": type_flow.get("total_raises", 0),
            "total_caught": type_flow.get("total_caught", 0),
            "total_uncaught": type_flow.get("total_uncaught", 0),
            "total_swallowed": type_flow.get("swallowed_exceptions", 0),
        }
        report.metrics["exception_propagation"] = exc_sum
        _sw_exempt = _inject_swallowed_exception_entries(report, type_flow)
        _cf_exempt = _inject_cross_file_exception_entries(
            report, project_root, ctx, exc_result)
        _log_injection_exemptions(_sw_exempt, _cf_exempt)
        logger.info(
            f"       异常: {exc_sum['total_raises']}个raise, "
            f"已捕获={exc_sum['total_caught']}, "
            f"未捕获={exc_sum['total_uncaught']}, "
            f"吞没={exc_sum['total_swallowed']}, "
            f"跨文件传播={len(exc_result.get('cross_file') or [])}")
        return exc_result
    except METHOD_DEGRADE_EXC as e:
        logger.warning(
            "异常传播分析跳过(该层发现不可用，非零发现): %s", e, exc_info=True)
        logger.info(f"       跳过（该层发现不可用）: {e}")
        return None
def _normalize_tryceratops_finding(
        f: dict, out: list, skill_dir: str, audit,
        suppression_cache: dict,
) -> None:
    kind, entry = d4_tc_entry(
        f, skill_dir, audit, suppression_cache=suppression_cache)
    if kind == "keep":
        out.append(entry)
        return
    if kind != "retired" or not entry.get("malformed"):
        return
    normalized = _prepare_tryceratops_entry(f, _TRY_MALFORMED_RULE_ID)
    normalized["malformed"] = True
    out.append(normalized)
def _normalize_tryceratops_findings(findings: list, skill_dir: str) -> list:
    out: list = []
    audit = _make_filter_auditor({"TRY-*": _new_audit()}, 0)
    suppression_cache: dict = {}
    for f in findings:
        if isinstance(f, dict):
            _normalize_tryceratops_finding(
                f, out, skill_dir, audit, suppression_cache)
        else:
            out.append({
                "rule_id": _TRY_MALFORMED_RULE_ID,
                "severity": _DEFAULT_FINDING_SEVERITY,
                "confidence": 0.0,
                "category": _TRY_CATEGORY,
                "message": f"Tryceratops 发现条目形态异常: {type(f).__name__}",
                "malformed": True,
            })
    return out
def run_exception_detector(skill_dir: str, ctx: Any = None) -> list[dict]:
    def _produce() -> list:
        result = safe_analyze_exceptions(skill_dir, ctx=ctx)
        if not isinstance(result, dict) or not result:
            raise RuntimeError(
                "异常传播分析未产出结构化结果（空结果哨兵，非零发现）")
        findings = result.get("tryceratops", [])
        if not isinstance(findings, list):
            raise RuntimeError(
                "tryceratops 通道形态异常（"
                f"{type(findings).__name__}），降级非零发现")
        return _normalize_tryceratops_findings(findings, skill_dir)
    return run_bounded_channel(
        "diag_exception_verdict", "run_exception_detector", _produce,
        label="D5 tryceratops", propagate_errors=True)

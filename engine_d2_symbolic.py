from __future__ import annotations

import ast
import hashlib
import importlib.metadata
import logging
import os
import platform
import re
import threading
import time
from collections import deque
from collections.abc import Iterable, Iterator
from concurrent.futures import ThreadPoolExecutor
from copy import deepcopy
from dataclasses import dataclass, field
from itertools import combinations
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    call_arg_values,
    call_tail_name,
    collect_param_names,
    comp_target_names,
    definition_time_exprs,
    is_static_method,
    iter_pattern_capture_names,
    iter_unpack_target_names,
    resolve_call_name,
)
from jwsgj.diag_types_defs import (
    CrossFileSymbolicPath,
    CrossFileSymbolicReport,
    CrossFileSymbolicState,
    UnifiedExploitResult,
)
from jwsgj.diag_types_normalize import (
    as_entry_list,
    is_pure_int,
)
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC, VULN_RENDER_TEMPLATE
from jwsgj.engine_d2_flow import (
    CrossFileTaintEngine,
    function_param_names,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    adaptive_workers,
    safe_relpath,
)

_log = logging.getLogger("jwsgj.engine_d2_symbolic")
__all__ = [
    "CallContext",
    "CrossFileSymbolicBridge",
    "FunctionTaintSummary",
    "InterproceduralTaintEngine",
    "InterproceduralTaintFlow",
    "TaintSeverity",
    "flow_id_or_unknown",
    "infer_sink_cwe",
    "inject_runtime_context",
    "normalize_e2_finding_fields",
    "sink_fix_suggestions",
    "solve_symbolic_paths",
]
class _SinkRoute(NamedTuple):
    cwe: str
    cwe_keywords: tuple[str, ...]
    fix_keywords: tuple[str, ...]
    fixes: tuple[str, ...]
    fix_pattern: str | None = None
_SINK_ROUTE_TABLE: dict[str, _SinkRoute] = {
    "sql": _SinkRoute(
        "CWE-89", ("sql", "execute", "raw"), ("sql", "execute"),
        ("使用参数化查询替代字符串拼接 SQL",
         "考虑使用 ORM 的安全查询方法（如 Django .filter()）")),
    "system": _SinkRoute(
        "CWE-78", ("system", "popen", "subprocess"),
        ("system", "popen", "subprocess"),
        ("使用 shlex.quote() 或参数列表方式传递命令参数",
         "避免将用户输入直接拼接到命令字符串")),
    "eval": _SinkRoute(
        "CWE-95", ("eval", "exec"), ("eval", "exec"),
        ("禁止使用 eval/exec 处理不可信输入",
         "如需动态执行，使用 ast.literal_eval() 或沙箱环境")),
    "requests": _SinkRoute(
        "CWE-918", ("requests.get", "urlopen"),
        ("requests.get", "urlopen"),
        ("对请求 URL 做协议/域名白名单校验，禁止内网地址",
         "设置合理超时并限制重定向次数")),
    "path": _SinkRoute(
        "CWE-22", ("path", "open", "file"), ("path", "file"),
        ("使用 os.path.realpath() 规范化路径后验证",
         "使用白名单限制可访问的目录范围"),
        r"\bopen\b"),
    "deserialize": _SinkRoute(
        "CWE-502", ("pickle", "yaml.load"), ("pickle", "yaml"),
        ("使用 pickle 时限制反序列化的类型（Unpickler.find_class）",
         "使用 yaml.safe_load() 替代 yaml.load()")),
    "template": _SinkRoute(
        "CWE-79", ("mark_safe", VULN_RENDER_TEMPLATE),
        ("mark_safe", VULN_RENDER_TEMPLATE),
        ("使用模板引擎的自动转义功能",
         "避免对用户可控内容使用 mark_safe()")),
}
_CWE_ROUTE_ORDER: tuple[str, ...] = (
    "sql", "system", "eval", "requests", "path", "deserialize", "template")
_FIX_ROUTE_ORDER: tuple[str, ...] = (
    "sql", "system", "requests", "path", "eval", "deserialize", "template")
_TAINT_LABEL_LIMIT = 100
def _path_labels(sp: Any, attr: str) -> list[str]:
    raw = getattr(sp, attr, None)
    if isinstance(raw, str):
        return [raw]
    if raw is None:
        return []
    try:
        return [item for item in raw if isinstance(item, str)]
    except TypeError as _e:
        _log.debug("[E2] %s 载体不可迭代（忽略）: %s", attr, _e)
        return []
def _sink_keyword_domain(sp: CrossFileSymbolicPath) -> str:
    return ' '.join(
        (s.split('@', 1)[0] if '@' in s else s)
        for s in _path_labels(sp, "taint_sinks")).lower()
def _keywords_hit(keywords: Iterable[str], text: str) -> bool:
    return any(
        re.search(rf"(?<![^\W_]){re.escape(kw)}(?![^\W_])", text)
        is not None for kw in keywords)
def _suggestion_group_matches(
    keywords: Iterable[str], pattern: str | None, sinks_str: str,
) -> bool:
    return _keywords_hit(keywords, sinks_str) or (
        pattern is not None and re.search(pattern, sinks_str) is not None)
def infer_sink_cwe(sp: CrossFileSymbolicPath) -> str:
    sinks_str = _sink_keyword_domain(sp)
    for key in _CWE_ROUTE_ORDER:
        route = _SINK_ROUTE_TABLE[key]
        if _keywords_hit(route.cwe_keywords, sinks_str):
            return route.cwe
    return 'CWE-20'
def sink_fix_suggestions(sp: CrossFileSymbolicPath) -> list[str]:
    suggestions = []
    sinks_str = _sink_keyword_domain(sp)
    sources_str = ' '.join(_path_labels(sp, "taint_sources")).lower()
    if sources_str:
        suggestions.append(
            "Review taint sources for proper input validation: "
            f"{sources_str[:_TAINT_LABEL_LIMIT]}")
    sink_matched = False
    for key in _FIX_ROUTE_ORDER:
        route = _SINK_ROUTE_TABLE[key]
        if _suggestion_group_matches(
                route.fix_keywords, route.fix_pattern, sinks_str):
            suggestions.extend(route.fixes)
            sink_matched = True
    if not sink_matched:
        if sinks_str:
            suggestions.append(
                f"对 {sinks_str[:_TAINT_LABEL_LIMIT]} 的入参做"
                "类型/范围白名单校验，拒绝外部可控原始值")
        suggestions.append("对来自外部源的输入进行严格的输入验证和净化")
        suggestions.append("遵循最小权限原则，限制危险函数的可访问性")
    return suggestions
@dataclass
class FunctionTaintSummary:
    function_name: str = ""
    tainted_return: bool = False
    module_path: str = ""
    source_hash: str = ""
    registry_version: int = 0
    param_taint_map: dict = field(default_factory=dict)
    return_taint: dict = field(default_factory=dict)
    return_sources: set = field(default_factory=set)
    param_sink_hits: dict = field(default_factory=dict)
    source_sink_hits: set = field(default_factory=set)
    call_arg_taint: dict[str, dict[int, set[int]]] = field(default_factory=dict)
    has_exception_paths: bool = False
    class_name: str = ""
class TaintSeverity:
    LOW = "LOW"
    MEDIUM = "MEDIUM"
    HIGH = "HIGH"
    CRITICAL = "CRITICAL"
@dataclass
class InterproceduralTaintFlow:
    source: str = ''
    sink: str = ''
    path: list = field(default_factory=list)
    severity: str = TaintSeverity.MEDIUM
    source_location: str = ''
    sink_location: str = ''
    def to_dict(self) -> dict:
        return {"source": self.source, "sink": self.sink, "path": self.path,
                "severity": self.severity,
                "source_location": self.source_location,
                "sink_location": self.sink_location}
@dataclass
class CallContext:
    call_site_id: str = ""
    caller_func: str = ""
    caller_module: str = ""
    callee_func: str = ""
    callee_module: str = ""
    arg_taint_map: dict = field(default_factory=dict)
    context_string: str = ""
    source_location: str = ""
    sink_location: str = ""
def _source_hash(source: str) -> str:
    return hashlib.sha1(
        source.encode("utf-8", "surrogatepass"),
        usedforsecurity=False).hexdigest()
def _normalize_tags(tags) -> list:
    if isinstance(tags, str):
        return [tags]
    if tags is None:
        return []
    try:
        items = list(tags)
    except TypeError as _e:
        _log.debug("[Interproc] tags 不可迭代降级为空集: %s: %s", type(_e).__name__, _e)
        return []
    return [item for item in items if isinstance(item, str)]
def _summary_key(module_path: str, fn_node) -> str:
    return f"{module_path}:{fn_node.name}@{fn_node.lineno}:{fn_node.col_offset}"
_MAX_SUMMARY_PASSES = 32
_MAX_LOOP_PASSES = 32
def _summary_state(summary: FunctionTaintSummary) -> tuple:
    return (
        bool(summary.tainted_return),
        tuple(sorted((idx, tuple(names))
                     for idx, names in summary.return_taint.items())),
        tuple(sorted(summary.return_sources)),
        tuple(sorted((idx, tuple(sorted(sinks)))
                     for idx, sinks in summary.param_sink_hits.items())),
        tuple(sorted(summary.source_sink_hits)),
        tuple(sorted(
            (callee, tuple(sorted(
                (caller_idx, tuple(sorted(callee_idxs)))
                for caller_idx, callee_idxs in mapping.items())))
            for callee, mapping in summary.call_arg_taint.items())),
        bool(summary.has_exception_paths),
    )
def _merge_summary(
    old: FunctionTaintSummary, new: FunctionTaintSummary,
) -> FunctionTaintSummary:
    new.tainted_return = new.tainted_return or old.tainted_return
    for idx, names in old.return_taint.items():
        target = new.return_taint.setdefault(idx, [])
        for name in names:
            if name not in target:
                target.append(name)
    new.return_sources.update(old.return_sources)
    for idx, sinks in old.param_sink_hits.items():
        new.param_sink_hits.setdefault(idx, set()).update(sinks)
    new.source_sink_hits.update(old.source_sink_hits)
    for callee, mapping in old.call_arg_taint.items():
        target = new.call_arg_taint.setdefault(callee, {})
        for caller_idx, callee_idxs in mapping.items():
            target.setdefault(caller_idx, set()).update(callee_idxs)
    new.has_exception_paths = new.has_exception_paths or old.has_exception_paths
    new.param_taint_map.update(old.param_taint_map)
    return new
def _parse_analyzable(code: str, filepath: str):
    try:
        return ast.parse(code, filename=filepath or "<string>")
    except PARSE_DEGRADE_EXC as _e:
        _log.warning(
            "[Interproc] analyze 不可解析输入降级 ok=False"
            "（%s）: %s: %s",
            filepath or "<string>", type(_e).__name__, _e)
        return None
def _unpack_batch_item(item):
    if len(item) in (2, 3):
        node, module_path, *source = item
        return node, module_path, source[0] if source else None
    _log.warning(
        "[Interproc] compute_summary_batch 跳过非法条目"
        "（长度 %d，应为 (node, module_path[, source])）",
        len(item))
    return None
def _edge_names_of_call(child: ast.Call) -> list:
    callee = resolve_call_name(child)
    names = [callee] if callee else []
    if (isinstance(child.func, ast.Attribute)
            and child.func.attr not in names):
        names.append(child.func.attr)
    return names
def _resolved_registered_name(node: ast.Call, registry) -> str:
    callee = resolve_call_name(node)
    if callee and callee in registry:
        return callee
    tail = call_tail_name(node)
    return tail if tail and tail in registry else ""
def _iter_direct_calls(fn_node: ast.AST) -> Iterator[ast.Call]:
    queue = deque(fn_node.body)
    while queue:
        child = queue.popleft()
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            queue.extend(definition_time_exprs(child))
            continue
        if isinstance(child, ast.ClassDef):
            queue.extend(child.decorator_list)
            queue.extend(child.bases)
            queue.extend(keyword.value for keyword in child.keywords)
            queue.extend(child.body)
            continue
        if isinstance(child, ast.Call):
            yield child
        queue.extend(ast.iter_child_nodes(child))
def _class_receiver_name(call: ast.Call, class_names,
                         current_class: str = "") -> str:
    if not isinstance(call.func, ast.Attribute):
        return ""
    receiver = call.func.value
    if isinstance(receiver, ast.Name):
        if receiver.id in {"self", "cls"} and current_class:
            return current_class
        return receiver.id if receiver.id in class_names else ""
    if isinstance(receiver, ast.Call) and isinstance(receiver.func, ast.Name):
        return receiver.func.id if receiver.func.id in class_names else ""
    return ""
def _receiver_offset(call: ast.Call, callee_params, class_names=(),
                     *, is_static: bool = False) -> int:
    if is_static:
        return 0
    if (isinstance(call.func, ast.Attribute)
            and callee_params and callee_params[0] == "self"
            and isinstance(call.func.value, ast.Name)
            and call.func.value.id in class_names):
        return 0
    return int(
        isinstance(call.func, ast.Attribute)
        and bool(callee_params)
        and callee_params[0] in {"self", "cls"}
    )
def _arguments_for_param(call: ast.Call, callee_params, callee_idx: int,
                         receiver_offset: int, callee_args) -> list[ast.expr]:
    if (not (0 <= callee_idx < len(callee_params))
            or not isinstance(callee_args, ast.arguments)):
        return []
    if callee_idx < receiver_offset:
        return []
    posonly = list(callee_args.posonlyargs)
    positional = [*posonly, *callee_args.args]
    kwonly = list(callee_args.kwonlyargs)
    regular_end = len(positional)
    vararg_end = regular_end + int(callee_args.vararg is not None)
    kwonly_end = vararg_end + len(kwonly)
    starred_positions = [index for index, arg in enumerate(call.args)
                         if isinstance(arg, ast.Starred)]
    starred = [call.args[index].value for index in starred_positions]
    if callee_idx < regular_end:
        param = positional[callee_idx]
        position = callee_idx - receiver_offset
        values = []
        has_position = 0 <= position < len(call.args)
        if has_position:
            argument = call.args[position]
            values.append(
                argument.value if isinstance(argument, ast.Starred)
                else argument)
            if starred_positions and starred_positions[0] <= position:
                values.extend(
                    arg for index, arg in enumerate(call.args)
                    if index > starred_positions[0]
                    and index != position
                    and not isinstance(arg, ast.Starred))
        values.extend(
            call.args[index].value for index in starred_positions
            if index <= position)
        if ((not has_position or starred)
                and callee_idx >= len(posonly)):
            values.extend(
                keyword.value for keyword in call.keywords
                if keyword.arg is None or keyword.arg == param.arg)
        return values
    if callee_args.vararg is not None and callee_idx == regular_end:
        start = max(0, regular_end - receiver_offset)
        values = [
            arg.value if isinstance(arg, ast.Starred) else arg
            for arg in call.args[start:]
        ]
        values.extend(starred)
        return values
    if vararg_end <= callee_idx < kwonly_end:
        param = kwonly[callee_idx - vararg_end]
        return [
            keyword.value for keyword in call.keywords
            if keyword.arg is None or keyword.arg == param.arg
        ]
    if callee_args.kwarg is not None and callee_idx == kwonly_end:
        keyword_bound = {
            param.arg for param in [*positional[len(posonly):], *kwonly]
        }
        return [
            keyword.value for keyword in call.keywords
            if keyword.arg is None or keyword.arg not in keyword_bound
        ]
    return []
@dataclass
class _PropagationState:
    visited: set = field(default_factory=set)
    flows: list = field(default_factory=list)
class InterproceduralTaintEngine:
    def __init__(self, max_depth: int = 10) -> None:
        self.max_depth = max_depth
        self.sources: dict[str, list] = {}
        self.sinks: dict[str, list] = {}
        self.sanitizers: dict[str, list] = {}
        self.summary_cache: dict[str, FunctionTaintSummary] = {}
        self.call_graph: dict[str, list] = {}
        self._function_params: dict[str, list[str]] = {}
        self._function_args: dict[str, ast.arguments] = {}
        self._class_names: set[str] = set()
        self._function_class_names: dict[int, str] = {}
        self._known_methods: set[str] = set()
        self._static_method_names: set[str] = set()
        self._active_module: str | None = None
        self._registry_version = 0
        self.stats = {
            "functions_analyzed": 0,
            "summaries_computed": 0,
            "flows_found": 0,
            "flows_blocked": 0,
            "cache_hits": 0,
        }
    def _register(self, registry: dict[str, list], name: str, tags) -> None:
        normalized = _normalize_tags(tags)
        if registry.get(name) == normalized:
            return
        registry[name] = normalized
        self._registry_version += 1
    def register_source(self, name: str, tags: list) -> None:
        self._register(self.sources, name, tags)
    def register_sink(self, name: str, tags: list) -> None:
        self._register(self.sinks, name, tags)
    def register_sanitizer(self, name: str, tags: list) -> None:
        self._register(self.sanitizers, name, tags)
    def compute_function_summary(self, fn_node, module_path: str,
                                 source: str | None = None) -> FunctionTaintSummary:
        key = _summary_key(module_path, fn_node)
        cacheable = isinstance(source, str)
        source_hash = _source_hash(source) if cacheable else ""
        cached = self.summary_cache.get(key) if cacheable else None
        if (cached is not None and cached.source_hash == source_hash
                and cached.registry_version == self._registry_version):
            self._count_summary(cached=True)
            return cached
        summary = self._build_summary(fn_node, module_path, source)
        if cacheable:
            self.summary_cache[key] = summary
        self._count_summary(cached=False)
        return summary
    def _new_summary(self, fn_node, module_path: str,
                     source: str | None) -> FunctionTaintSummary:
        return FunctionTaintSummary(
            function_name=fn_node.name,
            module_path=module_path,
            source_hash=(_source_hash(source)
                         if isinstance(source, str) else ""),
            registry_version=self._registry_version,
            class_name=self._function_class_names.get(id(fn_node), ""),
        )
    def _build_summary(self, fn_node, module_path: str,
                       source: str | None) -> FunctionTaintSummary:
        summary = self._new_summary(fn_node, module_path, source)
        params = function_param_names(fn_node)
        visitor = _InterproceduralTaintVisitor(
            params, summary, self, module_path)
        visitor.visit(fn_node)
        summary.has_exception_paths = visitor.found_exception_paths
        for idx in summary.return_taint:
            if idx < len(params):
                summary.param_taint_map[idx] = params[idx]
        return summary
    def _count_summary(self, cached: bool) -> None:
        self.stats["functions_analyzed"] += 1
        self.stats["cache_hits" if cached else "summaries_computed"] += 1
    def compute_summary_batch(self, funcs: list) -> int:
        processed = 0
        entries: list[tuple] = []
        for item in funcs:
            try:
                unpacked = _unpack_batch_item(item)
                if unpacked is None:
                    continue
                node, module_path, source = unpacked
                self.compute_function_summary(node, module_path, source)
                entries.append((node, module_path, source))
                processed += 1
            except RecursionError as _e:
                _log.warning("[Interproc] compute_summary_batch 扫描深度"
                             "降级: %r (%s)", item, _e)
                continue
            except (TypeError, ValueError, LookupError,
                    AttributeError) as _e:
                _log.warning("[Interproc] compute_summary_batch 跳过"
                             "非法条目: %r (%s)", item, _e)
                continue
        self._stabilize_summaries(entries)
        return processed
    def _stabilize_summaries(self, entries: list[tuple]) -> None:
        entries = [entry for entry in entries
                   if isinstance(entry[2], str)]
        if len(entries) < 2:
            return
        for node, module_path, source in entries:
            key = _summary_key(module_path, node)
            self.summary_cache[key] = self._new_summary(
                node, module_path, source)
        max_passes = min(len(entries) + 1, _MAX_SUMMARY_PASSES)
        for _pass in range(max_passes):
            changed = False
            for node, module_path, source in entries:
                key = _summary_key(module_path, node)
                old = self.summary_cache.get(key)
                fresh = self._build_summary(node, module_path, source)
                if old is None:
                    self.summary_cache[key] = fresh
                    changed = True
                    continue
                merged = _merge_summary(old, fresh)
                if _summary_state(merged) != _summary_state(old):
                    changed = True
                self.summary_cache[key] = merged
            if not changed:
                return
        _log.warning("[Interproc] 摘要固定点未完全收敛（上限 %d 轮）",
                     max_passes)
    def analyze(self, code: str, filepath: str = "") -> dict:
        before = dict(self.stats)
        tree = _parse_analyzable(code, filepath)
        if tree is None:
            return {"ok": False, "flows": [],
                    "stats": self._stats_delta(before),
                    "functions_analyzed": 0}
        _mp = filepath or "<string>"
        self._active_module = _mp
        funcs, live_keys = self._rebuild_call_graph_entries(tree, code, _mp)
        self._evict_stale_summaries(_mp, live_keys)
        self.compute_summary_batch(funcs)
        flows = self.propagate_taint()
        return {"ok": True, "flows": flows,
                "stats": self._stats_delta(before),
                "functions_analyzed": len(funcs)}
    def _stats_delta(self, before: dict[str, int]) -> dict[str, int]:
        return {key: value - before.get(key, 0)
                for key, value in self.stats.items()}
    def _evict_stale_summaries(self, module_path: str,
                               live_keys: set) -> None:
        prefix = f"{module_path}:"
        for stale_key in [k for k in self.summary_cache
                          if k.startswith(prefix) and k not in live_keys]:
            del self.summary_cache[stale_key]
    def _rebuild_call_graph_entries(self, tree, code: str,
                                    module_path: str) -> tuple[list, set]:
        self.call_graph = {}
        self._function_params = {}
        self._function_args = {}
        self._function_class_names = {}
        self._known_methods = set()
        self._static_method_names = set()
        funcs = []
        live_keys = set()
        self._class_names = set()
        nodes = list(walk_nodes(tree))
        for node in nodes:
            if not isinstance(node, ast.ClassDef):
                continue
            self._class_names.add(node.name)
            for child in node.body:
                if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    self._function_class_names[id(child)] = node.name
                    self._known_methods.add(f"{node.name}.{child.name}")
                    if is_static_method(child):
                        self._static_method_names.add(child.name)
                        self._static_method_names.add(
                            f"{node.name}.{child.name}")
        for node in nodes:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                funcs.append((node, module_path, code))
                live_keys.add(_summary_key(module_path, node))
                self.call_graph.setdefault(node.name, [])
                lookup_names = [node.name]
                class_name = self._function_class_names.get(id(node), "")
                if class_name:
                    lookup_names.append(f"{class_name}.{node.name}")
                for lookup_name in lookup_names:
                    self._function_params.setdefault(
                        lookup_name, function_param_names(node))
                    self._function_args.setdefault(lookup_name, node.args)
        for node, _module_path, _source in funcs:
            self._register_function_calls(node)
        return funcs, live_keys
    def _register_function_calls(self, fn_node) -> None:
        current_class = self._function_class_names.get(id(fn_node), "")
        current_name = (f"{current_class}.{fn_node.name}"
                        if current_class else fn_node.name)
        for child in _iter_direct_calls(fn_node):
            for name in self._call_edge_names(child, current_class):
                if (name not in {fn_node.name, current_name}
                        and name not in self.call_graph[fn_node.name]):
                    self.call_graph[fn_node.name].append(name)
    def _call_edge_names(self, call: ast.Call,
                         current_class: str = "") -> list:
        names = _edge_names_of_call(call)
        class_name = _class_receiver_name(
            call, self._class_names, current_class)
        if class_name:
            qualified = f"{class_name}.{call.func.attr}"
            if qualified in self._known_methods:
                return [qualified]
        return names
    @staticmethod
    def _tainted_param_indexes(summary: FunctionTaintSummary) -> list[int]:
        call_indexes = {
            param_idx
            for calls in summary.call_arg_taint.values()
            for param_idx in calls
        }
        return sorted(
            set(summary.return_taint) | set(summary.param_sink_hits)
            | call_indexes)
    def propagate_taint(self) -> list:
        state = _PropagationState()
        for func in self.call_graph:
            for summary in self._lookup_summaries(func):
                for param_idx in self._tainted_param_indexes(summary):
                    self._propagate_from(
                        state, func, param_idx, 0, summary=summary,
                        origin=(func, param_idx))
        state.flows.extend(self._direct_source_flows())
        self.stats["flows_found"] += len(state.flows)
        if state.flows:
            _log.info("[Interproc] 污点传播: %d 条流（净化阻断累计 %d）",
                      len(state.flows), self.stats["flows_blocked"])
        return state.flows
    def _param_sink_flow(self, func: str, param_idx: int,
                         sink_name: str) -> InterproceduralTaintFlow:
        return InterproceduralTaintFlow(
            source=func, sink=sink_name,
            severity=self._classify_severity(self.sinks[sink_name]),
            source_location=f"{func}:param{param_idx}",
            sink_location=sink_name)
    def _active_summaries(self) -> list:
        _module = self._active_module
        if _module is None:
            return list(self.summary_cache.values())
        return [s for s in self.summary_cache.values()
                if s.module_path == _module]
    def _direct_source_flows(self) -> list:
        flows: list = []
        for summary in self._active_summaries():
            for origin, sink_name in sorted(summary.source_sink_hits):
                if sink_name not in self.sinks:
                    continue
                severity = self._classify_severity(self.sinks[sink_name])
                flows.append(InterproceduralTaintFlow(
                    source=origin, sink=sink_name, severity=severity,
                    source_location=summary.function_name,
                    sink_location=sink_name))
        return flows
    def _propagate_from(self, state, func, param_idx, depth,
                        summary, origin) -> None:
        if depth >= self.max_depth:
            return
        self._emit_registered_sink_flows(
            state, func, param_idx, summary, origin)
        self._propagate_along_call_edges(
            state, func, param_idx, depth, summary, origin)
    def _emit_registered_sink_flows(self, state, func, param_idx,
                                    summary, origin) -> None:
        if summary is None:
            return
        source_func, source_param = origin
        for sink_name in sorted(
                summary.param_sink_hits.get(param_idx) or ()):
            if sink_name not in self.sinks:
                continue
            key = ("sink", source_func, source_param,
                   func, param_idx, sink_name)
            if key in state.visited:
                continue
            state.visited.add(key)
            state.flows.append(
                self._param_sink_flow(source_func, source_param, sink_name))
    def _propagate_along_call_edges(self, state, func, param_idx, depth,
                                    summary, origin) -> None:
        for callee in self.call_graph.get(func, []):
            key = ("edge", *origin, func, param_idx, callee, depth)
            if key in state.visited:
                continue
            state.visited.add(key)
            if callee in self.sinks:
                continue
            if callee in self.sanitizers:
                if (summary is not None
                        and summary.call_arg_taint.get(callee, {})
                        .get(param_idx)):
                    self.stats["flows_blocked"] += 1
            else:
                self._recurse_into_callee(
                    state, callee, depth, summary, param_idx, origin)
    def _recurse_into_callee(self, state, callee, depth, caller_summary,
                             caller_param_idx, origin) -> None:
        call_map = (getattr(caller_summary, "call_arg_taint", {})
                    if caller_summary is not None else {})
        callee_indexes = call_map.get(callee, {}).get(caller_param_idx, set())
        if not callee_indexes:
            return
        for callee_summary in self._lookup_summaries(callee):
            tainted_indexes = set(self._tainted_param_indexes(callee_summary))
            for callee_idx in sorted(callee_indexes & tainted_indexes):
                self._propagate_from(
                    state, callee, callee_idx, depth + 1,
                    summary=callee_summary, origin=origin)
    def get_stats(self) -> dict:
        return dict(self.stats)
    def _lookup_summaries(self, func_name: str) -> list:
        summaries = self._active_summaries()
        if func_name in self._known_methods:
            class_name, _, simple_name = func_name.rpartition(".")
            return [s for s in summaries
                    if s.function_name == simple_name
                    and s.class_name == class_name]
        return [s for s in summaries if s.function_name == func_name]
    def _signature_for_summary(self, summary: FunctionTaintSummary) -> tuple:
        lookup_name = (f"{summary.class_name}.{summary.function_name}"
                       if summary.class_name else summary.function_name)
        return (self._function_params.get(lookup_name, ()),
                self._function_args.get(lookup_name))
    def _is_static_call_target(self, callee: str, summary=None) -> bool:
        if summary is not None and summary.class_name:
            qualified = f"{summary.class_name}.{summary.function_name}"
            return qualified in self._static_method_names
        return callee in self._static_method_names
    @staticmethod
    def _classify_severity(tags: list):
        for tag in tags:
            if isinstance(tag, str) and ("code_execution" in tag
                                         or "command_injection" in tag):
                return TaintSeverity.CRITICAL
        return TaintSeverity.HIGH
_DEFINITION_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_MAX_VISIT_DEPTH = 100
def _definition_scan_frames(node: ast.AST, stack: tuple) -> list:
    frames = [(expr, stack) for expr in definition_time_exprs(node)]
    inner_stack = (*stack, collect_param_names(node))
    if isinstance(node, ast.Lambda):
        frames.append((node.body, inner_stack))
    else:
        frames.extend((stmt, inner_stack) for stmt in node.body)
    return frames
def _comprehension_results(node) -> tuple:
    return (node.key, node.value) if isinstance(node, ast.DictComp) else (node.elt,)
def _comprehension_scan_frames(node: ast.AST, stack: tuple) -> list:
    generators = node.generators
    inner_stack = (*stack, frozenset(comp_target_names(node)))
    frames = [(generators[0].iter, stack)]
    frames.extend((gen.iter, inner_stack) for gen in generators[1:])
    frames.extend((gen.target, inner_stack) for gen in generators)
    for gen in generators:
        frames.extend((cond, inner_stack) for cond in gen.ifs)
    frames.extend((expr, inner_stack) for expr in _comprehension_results(node))
    return frames
def _scan_shadow(n: ast.AST, param_stack: tuple,
                 shadowed: set) -> None:
    pending: list[tuple[ast.AST, tuple]] = [(n, param_stack)]
    while pending:
        node, stack = pending.pop()
        if isinstance(node, _DEFINITION_NODES):
            pending.extend(_definition_scan_frames(node, stack))
            continue
        if isinstance(node, COMP_SCOPE_NODES):
            pending.extend(_comprehension_scan_frames(node, stack))
            continue
        if (isinstance(node, ast.Name) and stack
                and any(node.id in pset for pset in reversed(stack))):
            shadowed.add(id(node))
            continue
        pending.extend((child, stack)
                       for child in ast.iter_child_nodes(node))
def _collect_param_shadow_ids(root: ast.expr) -> set:
    shadowed: set[int] = set()
    _scan_shadow(root, (), shadowed)
    return shadowed
class _TaintFrame:
    __slots__ = ("class_scope", "comprehension_scope", "locals",
                 "origins", "sources", "tainted")
    def __init__(self, bound_names=None, class_scope=False,
                 comprehension_scope=False):
        self.locals = set(bound_names or ())
        self.tainted = set()
        self.sources = {}
        self.origins = {}
        self.class_scope = class_scope
        self.comprehension_scope = comprehension_scope
    def clone(self):
        frame = _TaintFrame(
            self.locals, self.class_scope, self.comprehension_scope)
        frame.tainted = set(self.tainted)
        frame.sources = {name: set(values)
                         for name, values in self.sources.items()}
        frame.origins = {name: set(values)
                         for name, values in self.origins.items()}
        return frame
class _TaintFrameStack:
    def __init__(self, param_set: set[str]) -> None:
        self.param_set = param_set
        root = _TaintFrame(param_set)
        root.tainted = set(param_set)
        root.sources = {name: {name} for name in param_set}
        self.frames: list[_TaintFrame] = [root]
    def push(self, bound_names=None, class_scope=False,
             comprehension_scope=False):
        self.frames.append(_TaintFrame(
            bound_names, class_scope, comprehension_scope))
    def pop(self) -> None:
        self.frames.pop()
    def snapshot(self) -> list[_TaintFrame]:
        return [frame.clone() for frame in self.frames]
    def restore(self, snapshot: list[_TaintFrame]) -> None:
        self.frames = [frame.clone() for frame in snapshot]
    def absorb(self, frame: _TaintFrame) -> None:
        target = self.frames[-1]
        target.locals.update(frame.locals)
        for name in frame.locals:
            if name not in frame.tainted:
                target.tainted.discard(name)
                target.sources.pop(name, None)
                target.origins.pop(name, None)
                continue
            target.tainted.add(name)
            target.sources[name] = set(frame.sources.get(name, set()))
            target.origins[name] = set(frame.origins.get(name, set()))
    def merge(self, states: list[list[_TaintFrame]]) -> None:
        if not states or any(len(state) != len(self.frames) for state in states):
            raise RuntimeError("污点分支状态栈不平衡")
        merged_frames = []
        for frames in zip(*states, strict=True):
            base = frames[0]
            merged = _TaintFrame(
                class_scope=base.class_scope,
                comprehension_scope=base.comprehension_scope)
            merged.locals = set().union(*(frame.locals for frame in frames))
            merged.tainted = set().union(*(frame.tainted for frame in frames))
            for channel in ("sources", "origins"):
                values = {}
                for frame in frames:
                    for name, entries in getattr(frame, channel).items():
                        if name in merged.tainted:
                            values.setdefault(name, set()).update(entries)
                setattr(merged, channel, values)
            merged_frames.append(merged)
        self.frames = merged_frames
    def binding_frame_of(self, name):
        current = self.frames[-1]
        for frame in reversed(self.frames):
            if frame.class_scope and frame is not current:
                continue
            if name in frame.locals:
                return frame
        return None
    def is_tainted(self, name: str) -> bool:
        frame = self.binding_frame_of(name)
        return frame is not None and name in frame.tainted
    def _bound_channel(self, name: str, channel: str) -> set | None:
        frame = self.binding_frame_of(name)
        if frame is None:
            return None
        return getattr(frame, channel).get(name, set())
    def sources_of(self, name: str) -> set:
        return self._bound_channel(name, "sources") or set()
    def origins_of(self, name: str) -> set:
        return self._bound_channel(name, "origins") or set()
    def register_binding(self, target_id: str, tainted_sources: set,
                         source_origins: set,
                         existing: set | None,
                         comprehension_walrus: bool = False) -> None:
        frame = self.frames[-1]
        previous_sources = self.sources_of(target_id)
        previous_origins = self.origins_of(target_id)
        if comprehension_walrus:
            frame = next(
                (candidate for candidate in reversed(self.frames)
                 if not candidate.comprehension_scope),
                frame,
            )
        if existing is None:
            self._clear_binding(frame, target_id)
        if not tainted_sources and not source_origins:
            self._register_clean(frame, target_id, existing)
            return
        origins = set(source_origins)
        merged: set[str] = set(existing or ())
        if tainted_sources:
            frame.tainted.add(target_id)
            merged.update(self.param_set.intersection(tainted_sources))
            for src in tainted_sources:
                if src == target_id:
                    merged.update(previous_sources)
                    origins.update(previous_origins)
                else:
                    merged.update(self.sources_of(src))
                    origins.update(self.origins_of(src))
        if origins:
            frame.tainted.add(target_id)
            frame.origins.setdefault(target_id, set()).update(origins)
        if merged:
            frame.sources[target_id] = merged
        frame.locals.add(target_id)
    @staticmethod
    def _clear_binding(frame: _TaintFrame, target_id: str) -> None:
        frame.tainted.discard(target_id)
        frame.sources.pop(target_id, None)
        frame.origins.pop(target_id, None)
    def _register_clean(self, frame, target_id: str,
                        existing: set | None) -> None:
        if existing:
            frame.sources[target_id] = set(existing)
            frame.tainted.add(target_id)
        frame.locals.add(target_id)
def _taint_frames_key(frames: list[_TaintFrame]) -> tuple:
    return tuple(
        (
            frame.class_scope,
            frame.comprehension_scope,
            frozenset(frame.locals),
            frozenset(frame.tainted),
            frozenset(
                (name, frozenset(values))
                for name, values in frame.sources.items()),
            frozenset(
                (name, frozenset(values))
                for name, values in frame.origins.items()),
        )
        for frame in frames
    )
class _InterproceduralTaintVisitor(ast.NodeVisitor):
    def __init__(self, params, summary, engine, module_path) -> None:
        self.params = params
        self.param_set = set(params)
        self.summary = summary
        self.engine = engine
        self.module_path = module_path
        self.found_exception_paths = False
        self._stack = _TaintFrameStack(self.param_set)
        self._fn_depth = 0
        self._nested_summary_scope = 0
        self._visit_depth = 0
        self._depth_truncated = False
    def visit(self, node):
        if self._visit_depth >= _MAX_VISIT_DEPTH:
            if not self._depth_truncated:
                self._depth_truncated = True
                _log.warning(
                    "[Interproc] 扫描深度超过 %d 层，截断深层子树: %s",
                    _MAX_VISIT_DEPTH, self.module_path)
            return None
        self._visit_depth += 1
        try:
            return super().visit(node)
        finally:
            self._visit_depth -= 1
    def visit_Return(self, node: ast.Return) -> None:
        if node.value is None:
            return
        if self._fn_depth <= 1:
            tainted_in_return, origin_in_return = self._extract_flow(node.value)
            if tainted_in_return or origin_in_return:
                self.summary.tainted_return = True
                self.summary.return_sources.update(origin_in_return)
                for name in tainted_in_return:
                    self.summary.return_sources.update(
                        self._stack.origins_of(name))
                    for cand in self._param_outflow_candidates(name):
                        self._register_param_outflow(cand)
        self.generic_visit(node)
    def _register_taint_binding(self, target_id: str, value: ast.expr,
                                 existing: set | None = None,
                                 comprehension_walrus: bool = False) -> None:
        tainted_sources, source_origins = self._extract_flow(value)
        self._stack.register_binding(
            target_id, tainted_sources, source_origins, existing,
            comprehension_walrus=comprehension_walrus)
    def visit_Assign(self, node: ast.Assign) -> None:
        for target in node.targets:
            self._bind_destructure_target(target, node.value, positional=True)
        self.generic_visit(node)
    def visit_NamedExpr(self, node: ast.NamedExpr) -> None:
        if isinstance(node.target, ast.Name):
            self._register_taint_binding(
                node.target.id, node.value, comprehension_walrus=True)
        self.generic_visit(node)
    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.value is not None and isinstance(node.target, ast.Name):
            self._register_taint_binding(node.target.id, node.value)
        self.generic_visit(node)
    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        target = node.target
        if isinstance(target, ast.Name):
            self._register_taint_binding(
                target.id, node.value,
                existing=self._stack.sources_of(target.id))
        self.generic_visit(node)
    def _bind_destructure_target(self, target: ast.expr, value: ast.expr,
                                 *, positional: bool = False) -> None:
        if positional:
            plan = _positional_unpack_plan(target, value)
            if plan is not None:
                # 赋值语义：先整体求值右侧再逐个绑定，否则 ``a, b = b, a``
                # 这种交换会在绑定 a 时先把 a 的旧污点清掉，导致 b 丢污点
                extracted = [(leaf, *self._snapshot_binding_flow(sub_value))
                             for leaf, sub_value in plan]
                for leaf, tainted_sources, source_origins in extracted:
                    for target_id in iter_unpack_target_names(leaf):
                        self._stack.register_binding(
                            target_id, tainted_sources, source_origins, None)
                return
        for target_id in iter_unpack_target_names(target):
            self._register_taint_binding(target_id, value)
    def _snapshot_binding_flow(self, value: ast.expr) -> tuple[set, set]:
        """绑定前把右侧表达式解析成参数级污点源与来源标签。

        ``register_binding`` 对传入的名字是**延迟**解析（注册时再查
        ``sources_of``），多目标赋值逐个注册会互相覆盖；这里在任何绑定
        发生前一次性解析完成，与 ``a, b = b, a`` 的「右侧先整体求值」
        语义一致。
        """
        tainted_names, origins = self._extract_flow(value)
        sources: set = set()
        for name in tainted_names:
            sources |= self._stack.sources_of(name)
            origins |= self._stack.origins_of(name)
        return sources, origins
    def _visit_comprehension(self, node) -> None:
        generators = node.generators
        self.visit(generators[0].iter)
        self._stack.push(comprehension_scope=True)
        try:
            for idx, gen in enumerate(generators):
                if idx:
                    self.visit(gen.iter)
                self._bind_destructure_target(gen.target, gen.iter)
                for cond in gen.ifs:
                    self.visit(cond)
            for result in _comprehension_results(node):
                self.visit(result)
        finally:
            self._stack.pop()
    def visit_ListComp(self, node: ast.ListComp) -> None:
        self._visit_comprehension(node)
    visit_SetComp = visit_ListComp
    visit_DictComp = visit_ListComp
    visit_GeneratorExp = visit_ListComp
    def visit_For(self, node: ast.For) -> None:
        self._visit_loop(node)
    visit_AsyncFor = visit_For
    def visit_While(self, node: ast.While) -> None:
        self._visit_loop(node)
    def visit_With(self, node: ast.With) -> None:
        for item in node.items:
            if item.optional_vars is not None:
                self._bind_destructure_target(
                    item.optional_vars, item.context_expr)
        self.generic_visit(node)
    visit_AsyncWith = visit_With
    def _visit_function_frame(self, node) -> None:
        self._fn_depth += 1
        if self._fn_depth > 1:
            self._nested_summary_scope += 1
        try:
            if self._fn_depth == 1:
                self._visit_nodes(node.body)
            else:
                self._scan_definition_body(node, node.body)
        finally:
            if self._fn_depth > 1:
                self._nested_summary_scope -= 1
            self._fn_depth -= 1
    def _visit_nodes(self, nodes) -> None:
        for node in nodes:
            self.visit(node)
    def _scan_definition_body(self, node, statements) -> None:
        previous_scope = self._nested_summary_scope
        if previous_scope:
            self._nested_summary_scope -= 1
        try:
            for expr in definition_time_exprs(node):
                self.visit(expr)
        finally:
            self._nested_summary_scope = previous_scope
        self._stack.push(collect_param_names(node))
        try:
            self._visit_nodes(statements)
        finally:
            self._stack.pop()
    def _visit_alternatives(self, branches) -> None:
        entry = self._stack.snapshot()
        outcomes = []
        for branch in branches:
            self._stack.restore(entry)
            self._visit_nodes(branch)
            outcomes.append(self._stack.snapshot())
        self._stack.merge(outcomes)
    def visit_If(self, node: ast.If) -> None:
        self.visit(node.test)
        self._visit_alternatives((node.body, node.orelse))
    def visit_IfExp(self, node: ast.IfExp) -> None:
        self.visit(node.test)
        self._visit_alternatives(((node.body,), (node.orelse,)))
    def _visit_loop(self, node) -> None:
        is_for = isinstance(node, (ast.For, ast.AsyncFor))
        self.visit(node.iter if is_for else node.test)
        entry = self._stack.snapshot()
        current = entry
        for _pass in range(_MAX_LOOP_PASSES):
            self._stack.restore(current)
            if is_for:
                self._bind_destructure_target(node.target, node.iter)
                self.visit(node.target)
            else:
                self.visit(node.test)
            self._visit_nodes(node.body)
            iterated = self._stack.snapshot()
            self._stack.merge([entry, iterated])
            if _taint_frames_key(self._stack.frames) == _taint_frames_key(current):
                break
            current = self._stack.snapshot()
        else:
            _log.warning(
                "[Interproc] 循环污点状态未完全收敛（上限 %d 轮）: %s",
                _MAX_LOOP_PASSES, self.module_path)
        self._visit_nodes(node.orelse)
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._visit_function_frame(node)
    visit_AsyncFunctionDef = visit_FunctionDef
    def visit_Lambda(self, node: ast.Lambda) -> None:
        self._fn_depth += 1
        try:
            if self._fn_depth == 1:
                self.visit(node.body)
            else:
                self._scan_definition_body(node, (node.body,))
        finally:
            self._fn_depth -= 1
    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        for dec in node.decorator_list:
            self.visit(dec)
        for base in node.bases:
            self.visit(base)
        for kw in node.keywords:
            self.visit(kw.value)
        self._stack.push(class_scope=True)
        try:
            for stmt in node.body:
                self.visit(stmt)
        finally:
            self._stack.pop()
    def visit_Try(self, node) -> None:
        entry = self._stack.snapshot()
        exception_states = [entry]
        for statement in node.body:
            self.visit(statement)
            exception_states.append(self._stack.snapshot())
        self._visit_nodes(node.orelse)
        outcomes = [self._stack.snapshot()]
        for handler in node.handlers:
            self._stack.restore(entry)
            self._stack.merge(exception_states)
            self.visit(handler)
            outcomes.append(self._stack.snapshot())
        self._stack.merge(outcomes)
        self._visit_nodes(node.finalbody)
    visit_TryStar = visit_Try
    def visit_ExceptHandler(self, node: ast.ExceptHandler) -> None:
        if self._fn_depth <= 1:
            self.found_exception_paths = True
        if node.type is not None:
            self.visit(node.type)
        self._stack.push({node.name} if node.name else frozenset())
        handler_frame = None
        try:
            for stmt in node.body:
                self.visit(stmt)
            handler_frame = self._stack.frames[-1].clone()
        finally:
            self._stack.pop()
        if handler_frame is not None:
            self._stack.absorb(handler_frame)
    def visit_Match(self, node) -> None:
        self.visit(node.subject)
        subject_names, subject_origins = self._extract_flow(node.subject)
        subject_sources = set()
        for name in subject_names:
            subject_sources.update(self._stack.sources_of(name))
            subject_origins.update(self._stack.origins_of(name))
        entry = self._stack.snapshot()
        outcomes = []
        for case in node.cases:
            self._stack.restore(entry)
            names = iter_pattern_capture_names(case.pattern)
            self._stack.push(names)
            case_frame = None
            try:
                for name in names:
                    self._stack.register_binding(
                        name, subject_sources, subject_origins, existing=None)
                if case.guard is not None:
                    self.visit(case.guard)
                self._visit_nodes(case.body)
                case_frame = self._stack.frames[-1].clone()
            finally:
                self._stack.pop()
            if case_frame is not None:
                self._stack.absorb(case_frame)
            outcomes.append(self._stack.snapshot())
        if outcomes:
            if not any(case.guard is None
                       and _match_pattern_is_irrefutable(case.pattern)
                       for case in node.cases):
                outcomes.append(entry)
            self._stack.merge(outcomes)
    def visit_Call(self, node: ast.Call) -> None:
        sink_name = _resolved_registered_name(node, self.engine.sinks)
        if sink_name:
            for arg in call_arg_values(node):
                self._register_sink_arg(arg, sink_name)
        self._record_call_argument_flows(node)
        self.generic_visit(node)
    def _record_call_argument_flows(self, node: ast.Call) -> None:
        if self._nested_summary_scope:
            return
        for callee in dict.fromkeys(
                self.engine._call_edge_names(node, self.summary.class_name)):
            if (callee not in self.engine.call_graph
                    and callee not in self.engine._function_params):
                continue
            summaries = self.engine._lookup_summaries(callee)
            signatures = (
                [(summary, *self.engine._signature_for_summary(summary))
                 for summary in summaries]
                if summaries else
                [(None, self.engine._function_params.get(callee, ()),
                  self.engine._function_args.get(callee))]
            )
            for summary, callee_params, callee_args in signatures:
                receiver_offset = _receiver_offset(
                    node, callee_params, self.engine._class_names,
                    is_static=self.engine._is_static_call_target(
                        callee, summary))
                for callee_idx in range(len(callee_params)):
                    arguments = _arguments_for_param(
                        node, callee_params, callee_idx, receiver_offset,
                        callee_args)
                    for argument in arguments:
                        self._record_call_argument_flow(
                            callee, callee_idx, argument)
    def _record_call_argument_flow(self, callee: str, callee_idx: int,
                                   value: ast.expr) -> None:
        tainted_names, _origins = self._extract_flow(value)
        for name in tainted_names:
            for param_name in self._param_outflow_candidates(name):
                caller_idx = self.params.index(param_name)
                self.summary.call_arg_taint.setdefault(callee, {}).setdefault(
                    caller_idx, set()).add(callee_idx)
    def _call_return_taint(self, call: ast.Call,
                           depth: int) -> tuple[set, set, bool]:
        names: set[str] = set()
        origins: set[str] = set()
        modeled = False
        for callee in dict.fromkeys(
                self.engine._call_edge_names(call, self.summary.class_name)):
            for summary in self.engine._lookup_summaries(callee):
                if (summary.module_path
                        and summary.module_path != self.module_path):
                    continue
                modeled = True
                if not summary.tainted_return:
                    continue
                origins.update(summary.return_sources)
                callee_params, callee_args = (
                    self.engine._signature_for_summary(summary))
                receiver_offset = _receiver_offset(
                    call, callee_params, self.engine._class_names,
                    is_static=self.engine._is_static_call_target(
                        callee, summary))
                for callee_idx in summary.return_taint:
                    arguments = _arguments_for_param(
                        call, callee_params, callee_idx, receiver_offset,
                        callee_args)
                    for argument in arguments:
                        arg_names, arg_origins = self._extract_flow(
                            argument, _depth=depth + 1)
                        names.update(arg_names)
                        origins.update(arg_origins)
        return names, origins, modeled
    def _register_sink_arg(self, arg: ast.expr, callee: str) -> None:
        tainted_names, origins = self._extract_flow(arg)
        _own_scope = self._nested_summary_scope == 0
        for tname in tainted_names:
            for cand in self._param_outflow_candidates(tname):
                self._register_param_outflow(cand, sink=callee)
            if not _own_scope:
                continue
            for origin in self._stack.origins_of(tname):
                self.summary.source_sink_hits.add((origin, callee))
        if not _own_scope:
            return
        for origin in origins:
            self.summary.source_sink_hits.add((origin, callee))
    def _param_outflow_candidates(self, name: str) -> list:
        candidates: list[str] = []
        for src in self._stack.sources_of(name):
            if src in self.param_set and src not in candidates:
                candidates.append(src)
        return candidates
    def _register_param_outflow(self, param_name: str,
                                sink: str | None = None) -> None:
        param_idx = self.params.index(param_name)
        if sink is not None:
            self.summary.param_sink_hits.setdefault(param_idx, set()).add(sink)
            return
        existing = self.summary.return_taint.setdefault(param_idx, [])
        if param_name not in existing:
            existing.append(param_name)
        self.summary.param_sink_hits.setdefault(param_idx, set())
    def _scan_call_facts(self, node: ast.Call, origins: set) -> bool:
        source = _resolved_registered_name(node, self.engine.sources)
        if source:
            origins.add(source)
        return bool(_resolved_registered_name(node, self.engine.sanitizers))
    def _extract_flow(self, node: ast.expr,
                      _depth: int = 0) -> tuple[set, set]:
        shadowed = _collect_param_shadow_ids(node)
        names: set[str] = set()
        origins: set[str] = set()
        if _depth > 12:
            return names, origins
        pending: list[ast.AST] = [node]
        while pending:
            cur = pending.pop()
            if isinstance(cur, ast.Lambda):
                continue
            if isinstance(cur, ast.Name):
                if (id(cur) not in shadowed
                        and self._stack.is_tainted(cur.id)):
                    names.add(cur.id)
                continue
            if isinstance(cur, ast.NamedExpr):
                pending.append(cur.value)
                continue
            if isinstance(cur, ast.Call):
                if isinstance(cur.func, ast.Lambda):
                    pending.append(cur.func.body)
                    pending.extend(ast.iter_child_nodes(cur))
                    continue
                if self._scan_call_facts(cur, origins):
                    continue
                return_names, return_origins, modeled = (
                    self._call_return_taint(cur, _depth))
                names.update(return_names)
                origins.update(return_origins)
                if modeled:
                    continue
            pending.extend(ast.iter_child_nodes(cur))
        return names, origins
def _positional_unpack_plan(
    target: ast.expr, value: ast.expr,
) -> list[tuple[ast.expr, ast.expr]] | None:
    """赋值解包的位置配对计划：返回 ``(叶子目标, 对应右侧子表达式)`` 列表。

    顶层两侧均为无 Starred 且等长的元组/列表字面量时按位置逐层展开：
    ``a, b = p, 1`` 只有 ``a`` 承接 ``p`` 的污点，``b`` 必须保持干净，
    否则干净元素被整体污点化，产生误报。子层不可位置配对（如
    ``(a, b) = (p, get(q))`` 的第二个元素）则把该子目标整体作为叶子，
    承接子表达式全部污点。

    ``for``/推导式目标是逐元素迭代、``with ... as`` 承接 ``__enter__``
    返回值，都不满足「整体赋值」语义，调用方不得对它们启用位置配对。
    顶层任一条件不满足返回 None，由调用方回退到「整体 RHS 污点赋给
    全部目标」的保守语义。
    """
    if not isinstance(target, (ast.Tuple, ast.List)):
        return None
    if not isinstance(value, (ast.Tuple, ast.List)):
        return None
    if len(target.elts) != len(value.elts):
        return None
    if any(isinstance(item, ast.Starred) for item in target.elts):
        return None
    if any(isinstance(item, ast.Starred) for item in value.elts):
        return None
    plan: list[tuple[ast.expr, ast.expr]] = []
    for sub_target, sub_value in zip(target.elts, value.elts, strict=True):
        sub_plan = _positional_unpack_plan(sub_target, sub_value)
        if sub_plan is None:
            plan.append((sub_target, sub_value))
        else:
            plan.extend(sub_plan)
    return plan
def _match_pattern_is_irrefutable(pattern: ast.AST) -> bool:
    if isinstance(pattern, ast.MatchAs):
        return (pattern.pattern is None
                or _match_pattern_is_irrefutable(pattern.pattern))
    if isinstance(pattern, ast.MatchOr):
        return any(_match_pattern_is_irrefutable(item)
                   for item in pattern.patterns)
    return False
def _dual_get(obj: Any, key: str, default: Any = "") -> Any:
    if isinstance(obj, dict):
        return obj.get(key, default)
    return getattr(obj, key, default)
def _flow_steps(flow: Any) -> list:
    steps = as_entry_list(_dual_get(flow, "steps", []))
    if steps:
        return steps
    return [{
        "file_path": _dual_get(flow, "source_file", ""),
        "line": _dual_get(flow, "line", 0),
        "variable": "",
        "constraint": "",
    }]
def _display_path(raw: Any, root_dir: str) -> str:
    if not isinstance(raw, str) or not raw:
        return ""
    if not root_dir or not os.path.isabs(raw):
        return raw
    return safe_relpath(raw, root_dir, normalize=False)
def _flow_identity(flow: Any, root_dir: str = "") -> tuple[str, str, str]:
    raw_id = _dual_get(flow, "flow_id")
    if isinstance(raw_id, str) and raw_id:
        path_id = raw_id
    elif raw_id not in (None, ""):
        path_id = str(raw_id)
    else:
        path_id = _fallback_flow_id(flow)
    return (path_id,
            _display_path(_dual_get(flow, "source_file"), root_dir),
            _dual_get(flow, "source_name") or "")
def _fallback_flow_id(flow: Any) -> str:
    parts = (str(_dual_get(flow, "source_file") or ""),
             str(_dual_get(flow, "line") or ""),
             str(_dual_get(flow, "sink") or ""),
             str(_dual_get(flow, "sink_file") or ""),
             str(_dual_get(flow, "source_name") or ""),
             str(_dual_get(flow, "reaches_param")))
    digest = hashlib.sha1(
        "\0".join(parts).encode("utf-8", "surrogatepass"),
        usedforsecurity=False).hexdigest()[:12]
    return f"cfsp_{digest}"
def _step_file(step: Any) -> str:
    raw = _dual_get(step, "file_path")
    return raw if isinstance(raw, str) else ""
def _flow_source_label(flow: Any, entry_func: str, entry_file: str,
                       steps: list, root_dir: str = "") -> str:
    _name = entry_func or str(_dual_get(flow, "source", "") or "")
    _file = _display_path(_step_file(steps[0]), root_dir) if steps else ""
    _file = _file or entry_file
    if not _name:
        return _file or "unknown"
    return f"{_name}@{_file}" if _file else _name
def _flow_sink_label(flow: Any, steps: list, root_dir: str = "") -> str:
    sink_name = _dual_get(flow, 'sink_name') or _dual_get(flow, 'sink') or ''
    if not isinstance(sink_name, str) or not sink_name:
        sink_name = 'taint_flow'
    sink_file = _dual_get(flow, 'sink_file')
    if not sink_file and steps:
        sink_file = _step_file(steps[-1])
    if not sink_file:
        sink_file = _dual_get(flow, 'source_file')
    sink_file = _display_path(sink_file, root_dir)
    return f"{sink_name}@{sink_file}" if sink_file else sink_name
def _flow_to_symbolic_path(
    flow: Any, root_dir: str = "",
) -> CrossFileSymbolicPath:
    steps = _flow_steps(flow)
    path_id, entry_file, entry_func = _flow_identity(flow, root_dir)
    symbolic_path = CrossFileSymbolicPath(
        path_id=path_id,
        entry_file=entry_file,
        entry_function=entry_func,
    )
    _build_states_for_flow(flow, symbolic_path, path_id, steps)
    symbolic_path.taint_sources.append(
        _flow_source_label(flow, entry_func, entry_file, steps, root_dir))
    symbolic_path.taint_sinks.append(
        _flow_sink_label(flow, steps, root_dir))
    return symbolic_path
def _normalize_step_line(raw: Any) -> int:
    return raw if is_pure_int(raw) and raw >= 0 else 0
def _normalize_step_file(raw: Any) -> str:
    return raw if isinstance(raw, str) else ''
def _state_from_step(
    step: Any, state_id: str, seen_vars: dict,
) -> CrossFileSymbolicState:
    file_path = _normalize_step_file(_dual_get(step, "file_path"))
    line = _normalize_step_line(_dual_get(step, "line"))
    state = CrossFileSymbolicState(
        state_id=state_id,
        current_file=file_path,
        current_function="",
        current_line=line,
    )
    var_name = _dual_get(step, "variable", "")
    if isinstance(var_name, str) and var_name:
        symbolic_var = _symbolize_variable(
            var_name, file_path or "<unknown>", line, seen_vars)
        state.symbolic_vars[var_name] = symbolic_var
        if file_path:
            state.cross_file_symbol_map[var_name] = (
                file_path, line, str(symbolic_var)
            )
    return state
def _build_states_for_flow(
    flow: Any, symbolic_path: Any, path_id: Any, steps: list,
) -> None:
    seen_vars = {}
    for i, step in enumerate(steps):
        state = _state_from_step(step, f"{path_id}_s{i}", seen_vars)
        constraint = _dual_get(step, "constraint", "")
        if constraint:
            state.path_constraints.append(constraint)
            symbolic_path.constraints.append(constraint)
        state.cross_file_taint_flows = [flow]
        symbolic_path.states.append(state)
def _symbolize_variable(var_name: str, file_path: str, line: int,
                        seen_vars: dict) -> str:
    key = f"{file_path}:{line}:{var_name}"
    cached = seen_vars.get(key)
    if isinstance(cached, str):
        return cached
    symbol = f"SYM_{var_name}_{line}" if line > 0 else f"SYM_{var_name}"
    if symbol in seen_vars.values():
        digest = hashlib.sha1(
            file_path.encode("utf-8", "surrogatepass"),
            usedforsecurity=False).hexdigest()[:12]
        symbol = f"{symbol}_{digest}"
    seen_vars[key] = symbol
    return symbol
def flow_id_or_unknown(flow) -> str:
    try:
        value = _dual_get(flow, 'flow_id', '')
    except Exception as _e:
        log_swallowed(__name__, _e,
                      context=f'flow_id_or_unknown:{type(_e).__name__}')
        return '?'
    return str(value) if value not in (None, '') else '?'
def _eq_sides(constraint: Any) -> tuple[str, str] | None:
    if not isinstance(constraint, str):
        return None
    parts = constraint.split('==')
    if len(parts) != 2:
        return None
    return parts[0].strip(), parts[1].strip()
def _constraint_literals_differ(lhs: str, rhs: str) -> bool:
    try:
        return ast.literal_eval(lhs) != ast.literal_eval(rhs)
    except (ValueError, TypeError, SyntaxError, RecursionError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=(f'_constraint_literals_differ:'
                     f'{type(_swallowed_exc).__name__}'))
        return False
def _is_contradiction_pair(c1: Any, c2: Any) -> bool:
    sides1 = _eq_sides(c1)
    sides2 = _eq_sides(c2)
    if sides1 is None or sides2 is None:
        return False
    return (
        (sides1[0] == sides2[0]
         and _constraint_literals_differ(sides1[1], sides2[1]))
        or (sides1[0] == sides2[1]
            and _constraint_literals_differ(sides1[1], sides2[0]))
        or (sides1[1] == sides2[0]
            and _constraint_literals_differ(sides1[0], sides2[1]))
        or (sides1[1] == sides2[1]
            and _constraint_literals_differ(sides1[0], sides2[0]))
    )
def _path_is_feasible(path: CrossFileSymbolicPath) -> bool:
    for constraint in path.constraints:
        sides = _eq_sides(constraint)
        if sides is not None and _constraint_literals_differ(*sides):
            return False
    return not any(
        _is_contradiction_pair(c1, c2)
        for c1, c2 in combinations(path.constraints, 2)
    )
def _mark_path_feasible(path: CrossFileSymbolicPath) -> None:
    path.is_feasible = _path_is_feasible(path)
    path.feasibility_proof = "Heuristic (solver unavailable)"
def solve_symbolic_paths(
    symbolic_paths: list[CrossFileSymbolicPath],
) -> list[CrossFileSymbolicPath]:
    if (isinstance(symbolic_paths, (str, bytes, dict))
            or not isinstance(symbolic_paths, Iterable)):
        _log.warning("solve_symbolic_paths 收到非法载体（%s），按空表处理",
                     type(symbolic_paths).__name__)
        symbolic_paths = []
    else:
        symbolic_paths = list(symbolic_paths)
    paths_to_solve = [p for p in symbolic_paths if p.constraints]
    if len(paths_to_solve) > 1:
        max_workers = adaptive_workers(len(paths_to_solve))
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            list(executor.map(_mark_path_feasible, paths_to_solve))
    elif paths_to_solve:
        _mark_path_feasible(paths_to_solve[0])
    feasible = [p for p in symbolic_paths if p.is_feasible]
    _log.info("约束求解: %d/%d 条路径可行",
              len(feasible), len(symbolic_paths))
    return symbolic_paths
def _build_symbolic_states(
    taint_flows: list, root_dir: str = "",
) -> list[CrossFileSymbolicPath]:
    paths = []
    for flow in taint_flows:
        try:
            paths.append(_flow_to_symbolic_path(flow, root_dir))
        except (AttributeError, KeyError, TypeError, ValueError, RuntimeError) as e:
            _log.warning("污点流 %s 符号化失败(跳过): %s",
                         flow_id_or_unknown(flow), e)
    _log.info("从 %d 条污点流构建 %d 条跨文件符号路径",
              len(taint_flows), len(paths))
    return paths
def _py_file_count(py_files) -> int | None:
    if isinstance(py_files, (list, tuple, set, frozenset)):
        return len(py_files)
    return None
def _apply_scan_summary(
    report: CrossFileSymbolicReport, summary: dict | None,
    py_files: list | None,
) -> None:
    _summary = dict(summary or {})
    _taint_scanned = _summary.get('files_scanned')
    _scan_error = _summary.get('scan_error')
    if _scan_error:
        report.files_scanned = 0
        report.files_failed = 0
        report.errors.append(
            _scan_error if isinstance(_scan_error, str)
            else f'污点扫描未执行（scan_error 类型: {type(_scan_error).__name__}）')
        return
    if is_pure_int(_taint_scanned) and _taint_scanned >= 0:
        report.files_scanned = _taint_scanned
    else:
        _counted = _py_file_count(py_files)
        if _counted is None:
            report.errors.append(
                '污点扫描未返回 files_scanned，py_files 无法计数：扫描覆盖未度量')
        else:
            report.files_scanned = _counted
            report.errors.append(
                '扫描器未报告 files_scanned，files_scanned 取 py_files 计数（近似口径）')
    _taint_failed = _summary.get('files_failed')
    if is_pure_int(_taint_failed) and _taint_failed >= 0:
        report.files_failed = _taint_failed
    else:
        report.files_failed = 0
        report.errors.append(
            '污点扫描未返回有效 files_failed，失败文件覆盖未度量')
    _walk_errors = _summary.get('walk_error_count')
    if is_pure_int(_walk_errors) and _walk_errors > 0:
        report.errors.append(
            f'{_walk_errors} 个子目录不可读，扫描覆盖不完整')
def _analyze_taint_flows(
    report: CrossFileSymbolicReport, taint_flows: list,
    max_paths: int | None, root_dir: str,
) -> None:
    if not is_pure_int(max_paths):
        max_paths = len(taint_flows)
    max_paths = max(0, max_paths)
    if len(taint_flows) > max_paths:
        _log.warning(
            "[CrossFileSymbolic] 污点流超出上限: %d > %d，仅分析前 %d 条",
            len(taint_flows), max_paths, max_paths,
        )
    symbolic_paths = _build_symbolic_states(taint_flows[:max_paths], root_dir)
    report.symbolic_states_explored = sum(
        len(p.states) for p in symbolic_paths
    )
    symbolic_paths = solve_symbolic_paths(symbolic_paths)
    feasible = [p for p in symbolic_paths if p.is_feasible]
    for sp in feasible:
        report.results.append(_build_unified_result(sp, root_dir))
    report.results = inject_runtime_context(report.results)
    report.exploitable_vulnerabilities = len(report.results)
def _build_unified_result(
    sp: CrossFileSymbolicPath, root_dir: str,
) -> UnifiedExploitResult:
    result = UnifiedExploitResult(
        vulnerability_id=sp.path_id,
        severity="P0" if sp.exploit_inputs else "P1",
        cwe_id=infer_sink_cwe(sp),
    )
    for state in sp.states:
        _rel = _display_path(state.current_file, root_dir)
        result.cross_file_steps.append({
            'file': _rel,
            'line': state.current_line,
            'constraints': state.path_constraints,
            'symbolic_vars': {
                k: str(v) for k, v in state.symbolic_vars.items()
            },
        })
    result.constraints = sp.constraints
    result.exploitable_inputs = sp.exploit_inputs
    if sp.exploit_inputs:
        result.constraint_solution = sp.exploit_inputs
    result.fix_suggestions = sink_fix_suggestions(sp)
    result.details.update(_source_flow_details(sp))
    return result
def _source_flow_details(sp: CrossFileSymbolicPath) -> dict[str, Any]:
    states = as_entry_list(getattr(sp, 'states', None))
    if not states:
        return {}
    flows = as_entry_list(getattr(states[0], 'cross_file_taint_flows', None))
    flow = flows[0] if flows else None
    if flow is None:
        return {}
    return {"reaches_param": _dual_get(flow, "reaches_param", None),
            "sink": _dual_get(flow, "sink", "")}
class _E2FindingFields(NamedTuple):
    vuln_id: str
    severity: str
    constraints: list | tuple
    steps: list | tuple
    file_name: str
    line_num: int
    sink: str
def _e2_sink_label(vuln: Any, vuln_id: str) -> str:
    details = getattr(vuln, 'details', None)
    if isinstance(details, dict):
        for key in ('sink', 'sink_name'):
            value = details.get(key)
            if isinstance(value, str) and value:
                return value
    for attr in ('sink', 'sink_name'):
        value = getattr(vuln, attr, None)
        if isinstance(value, str) and value:
            return value
    return vuln_id.rsplit(':', 1)[-1] if ':' in vuln_id else ''
def _e2_sink_step_loc(steps: list) -> tuple[str, int]:
    _loc_step = steps[-1] if steps else None
    if not isinstance(_loc_step, dict):
        return '', 0
    _file = _loc_step.get('file')
    _line = _loc_step.get('line')
    return (_file if isinstance(_file, str) else '',
            _normalize_step_line(_line))
def normalize_e2_finding_fields(vuln: Any) -> _E2FindingFields:
    vuln_id = getattr(vuln, 'vulnerability_id', '')
    if not isinstance(vuln_id, str):
        vuln_id = '' if vuln_id is None else str(vuln_id)
    _raw_severity = getattr(vuln, 'severity', '')
    severity = (_raw_severity
                if isinstance(_raw_severity, str) and _raw_severity
                else 'P1')
    constraints = as_entry_list(getattr(vuln, 'constraints', []))
    steps = as_entry_list(getattr(vuln, 'cross_file_steps', []))
    file_name, line_num = _e2_sink_step_loc(steps)
    sink = _e2_sink_label(vuln, vuln_id)
    return _E2FindingFields(
        vuln_id, severity, constraints, steps, file_name, line_num, sink)
class CrossFileSymbolicBridge:
    def __init__(self, root_dir: str | None = None) -> None:
        self.root_dir = root_dir or os.getcwd()
        self._cross_file_taint_engine = CrossFileTaintEngine()
        self.last_taint_scan_summary: dict[str, Any] = {}
    def identify_cross_file_taint_flows(
        self, root_dir: str | None = None, cache=None,
        restrict_files: list[str] | None = None,
    ) -> list:
        if root_dir is None:
            root_dir = self.root_dir
        report = self._cross_file_taint_engine.analyze_project(
            root_dir, cache=cache, restrict_files=restrict_files)
        flows = list(as_entry_list(getattr(report, 'flows', None)))
        _summary = getattr(report, 'summary', None)
        if isinstance(_summary, dict):
            self.last_taint_scan_summary = dict(_summary)
        else:
            if _summary:
                _log.warning("污点扫描 summary 非 dict 形态（忽略）: %r", _summary)
            self.last_taint_scan_summary = {}
        _log.info("识别到 %d 条跨文件污点流", len(flows))
        return flows
    def analyze(
        self, root_dir: str | None = None, max_paths: int | None = 50,
        py_files: list | None = None, cache=None,
        restrict_files: list[str] | None = None,
    ) -> CrossFileSymbolicReport:
        root_dir = root_dir or self.root_dir
        t_start = time.time()
        report = CrossFileSymbolicReport(root_dir=root_dir)
        taint_flows = self.identify_cross_file_taint_flows(
            root_dir, cache=cache, restrict_files=restrict_files)
        _apply_scan_summary(
            report, self.last_taint_scan_summary, py_files)
        report.cross_file_paths = len(taint_flows)
        if taint_flows:
            _analyze_taint_flows(
                report, taint_flows, max_paths, root_dir)
        else:
            _log.info("未发现跨文件污点流")
        report.scan_time_ms = (time.time() - t_start) * 1000
        report.backend_used = 'heuristic'
        if report.errors:
            _log.warning("[CrossFileSymbolic] 扫描覆盖不完整: %s",
                         "; ".join(report.errors[:3]))
        _log.info(
            "跨文件符号分析完成: %d 个文件, %d 条污点流, "
            "%d 个符号状态, %d 条可利用 (%d ms)",
            report.files_scanned, report.cross_file_paths,
            report.symbolic_states_explored, report.exploitable_vulnerabilities,
            int(report.scan_time_ms)
        )
        return report
    def quick_scan(self, target_file: str) -> Any:
        _abs_target = os.path.abspath(target_file)
        report = self.analyze(
            os.path.dirname(_abs_target), max_paths=10, restrict_files=[_abs_target]
        )
        if report.results:
            return report.results[0]
        return UnifiedExploitResult(vulnerability_id="none")
    def get_status(self) -> dict[str, Any]:
        return {k: str(v)[:100] for k, v in vars(self).items() if not k.startswith('_')}
_STABLE_ENV_MEMO: dict[str, Any] | None = None
_STABLE_ENV_MEMO_LOCK = threading.Lock()
def _stable_runtime_env() -> dict[str, Any]:
    global _STABLE_ENV_MEMO
    with _STABLE_ENV_MEMO_LOCK:
        if _STABLE_ENV_MEMO is not None:
            return _STABLE_ENV_MEMO
    env: dict[str, Any] = {
        'python_version': platform.python_version(),
        'platform': platform.platform(),
        'os': os.name,
    }
    env['installed_packages'] = _installed_package_names()
    with _STABLE_ENV_MEMO_LOCK:
        if _STABLE_ENV_MEMO is None:
            _STABLE_ENV_MEMO = env
    return _STABLE_ENV_MEMO
def _installed_package_names(limit: int | None = 20) -> list[str]:
    try:
        distributions = list(importlib.metadata.distributions())
    except (OSError, ValueError, AttributeError, KeyError, TypeError) as exc:
        _log.debug("installed_packages 枚举失败(忽略): %s", exc)
        return []
    names: set[str] = set()
    skipped = 0
    for dist in distributions:
        try:
            name = dist.metadata.get('Name')
        except (OSError, ValueError, AttributeError, KeyError, TypeError):
            skipped += 1
            continue
        if isinstance(name, str) and name:
            names.add(name)
        else:
            skipped += 1
    if skipped:
        _log.debug("installed_packages 跳过 %d 条无名字/脏元数据条目", skipped)
    packages = sorted(names)
    if is_pure_int(limit) and limit < 0:
        _log.debug("installed_packages 上限非法(%d)，按不截断处理", limit)
        return packages
    if is_pure_int(limit) and len(packages) > limit:
        _log.debug("installed_packages 截断 %d -> %d 条（环境快照展示上限）",
                   len(packages), limit)
        return packages[:limit]
    return packages
def _collect_runtime_context() -> dict[str, Any]:
    context: dict[str, Any] = dict(_stable_runtime_env())
    context['cwd'] = os.getcwd()
    context['environment'] = 'ci' if os.environ.get('CI') else 'local'
    return context
def inject_runtime_context(
    results: list[UnifiedExploitResult],
) -> list[UnifiedExploitResult]:
    if not results:
        return results
    try:
        context = _collect_runtime_context()
    except (OSError, AttributeError, KeyError, TypeError, ValueError,
            RuntimeError) as exc:
        _log.warning("运行时上下文注入失败: %s", exc)
        return results
    for result in results:
        _inject_runtime_context_one(result, context)
    return results
def _inject_runtime_context_one(
    result: UnifiedExploitResult, context: dict[str, Any],
) -> None:
    try:
        result.runtime_context = deepcopy(context)
        if result.exploitable_inputs:
            _adjust_inputs_for_runtime(result, context)
    except (OSError, AttributeError, KeyError, TypeError, ValueError,
            RuntimeError) as exc:
        _log.warning("运行时上下文注入失败(仅损失该条): %s", exc)
_URI_AUTHORITY_RE = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*://")
_PATH_INPUT_KEY_PARTS = frozenset({"path", "file", "dir", "directory", "folder"})
_PATH_INPUT_KEY_NAMES = frozenset({"filename", "filepath", "foldername"})
def _is_path_input_key(key: Any) -> bool:
    if not isinstance(key, str):
        return False
    normalized = key.casefold().replace("-", "_")
    return (normalized in _PATH_INPUT_KEY_NAMES
            or not _PATH_INPUT_KEY_PARTS.isdisjoint(normalized.split("_")))
def _windows_path_value(value: Any) -> Any:
    if (isinstance(value, str) and '/' in value
            and _URI_AUTHORITY_RE.match(value) is None):
        return value.replace('/', '\\')
    return value
def _adjust_inputs_for_runtime(result: UnifiedExploitResult, context: dict) -> None:
    if 'Windows' not in str(context.get('platform', '')):
        return
    for key, value in result.exploitable_inputs.items():
        if _is_path_input_key(key):
            result.exploitable_inputs[key] = _windows_path_value(value)

from __future__ import annotations  # noqa: I001
import ast
import logging
import os
import sys
from collections.abc import Iterator, Mapping
from typing import Any
from jwsgj.diag_callgraph_builder import _is_constant_false_test
from jwsgj.diag_callgraph_collect import relative_import_module
from jwsgj.diag_callgraph_facts import (
    CallEdge,
    FunctionNode,
    _qualify_module_member,
)
from jwsgj.diag_callgraph_resolve import (
    _MODULE_SCOPE_NAME,
    SELF_CLS_NAMES,
    _iter_definition_annotations,
)
from jwsgj.diag_callgraph_source import (
    _collect_class_spans,
    _iter_registered_defs,
    _iter_scope_nodes_preorder,
    _parse_source_file,
    _path_key,
    _qualify,
    _real_path_key,
    _resolve_source_filepath,
    _str_file,
    _str_name,
)
from jwsgj.diag_callgraph_verdicts import find_orphans
from jwsgj.diag_implicit_calls import RuntimeBindingScanner
from jwsgj.diag_shared_ast_nodes import (
    innermost_span,
    module_postpones_annotations,
    path_to_dotted_module,
    type_checking_body_node_ids,
)
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_scope import canonical_path, iter_py_files_under
from jwsgj.prevention_scope_facts import walk_nodes
logger = logging.getLogger(__name__)
__all__ = [
    "FallbackCallGraph",
    "build_fallback_call_graph",
    "fallback_resolve_function_name",
    "merge_bindings_into_callgraph",
    "merge_trace_edges",
    "merge_trace_into_callgraph",
    "scan_runtime_bindings",
]
_EVENT_ENTRY_FIELDS = ("bus_instance", "callback", "callback_file", "callback_line")
_REGISTRY_ENTRY_FIELDS = ("registry_instance", "handler", "handler_file", "handler_line")
_COUNT_ONLY_CHANNELS = (
    ("decorator_registrations", "wrapped_func", "装饰器注册通道"),
    ("init_subclass_registrations", "subclass", "__init_subclass__ 注册通道"),
)
def _int_line(value: Any) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        return 0
    return value
def _entry_field(entry: Any, key: str, default: Any = "") -> Any:
    if not isinstance(entry, Mapping):
        return default
    return entry.get(key, default)
def _iter_entries(items: Any, *, channel: str) -> Iterator[Mapping]:
    if isinstance(items, (str, bytes)) or not isinstance(
            items, (list, tuple, set, frozenset)):
        if items:
            logger.warning(
                "[CallGraph] %s 非清单形状,跳过整段: %r",
                channel, type(items).__name__)
        return
    for entry in items:
        if isinstance(entry, Mapping):
            yield entry
        else:
            logger.warning(
                "[CallGraph] %s 含非映射条目,跳过: %r", channel, entry)
def _graph_views(call_graph: Any) -> tuple[dict | None, list | None]:
    funcs = getattr(call_graph, "functions", None)
    calls = getattr(call_graph, "calls", None)
    if funcs is not None and not isinstance(funcs, dict):
        logger.warning("[CallGraph] functions 非映射形态,跳过: %r",
                       type(funcs).__name__)
        funcs = None
    if calls is not None and not isinstance(calls, list):
        logger.warning("[CallGraph] calls 非列表形态,跳过: %r",
                       type(calls).__name__)
        calls = None
    return funcs, calls
def _paths_consistent(a: str, b: str) -> bool:
    na, nb = _path_key(a), _path_key(b)
    if not na or not nb:
        return False
    if na == nb:
        return True
    if na.endswith(os.sep + nb) or nb.endswith(os.sep + na):
        return True
    real_a, real_b = _real_path_key(a), _real_path_key(b)
    return bool(real_a and real_b and real_a == real_b)
def _register_caller(callers_idx, callee_key: str, caller_key: str) -> None:
    if not isinstance(callers_idx, dict):
        return
    entry = callers_idx.get(callee_key)
    if not isinstance(entry, (set, list)):
        callers_idx[callee_key] = {caller_key}
    elif isinstance(entry, set):
        entry.add(caller_key)
    elif caller_key not in entry:
        entry.append(caller_key)
def _function_confidence_snapshot(call_graph) -> dict:
    return {
        id(node): getattr(node, "confidence", "unknown")
        for node in (getattr(call_graph, "functions", None) or {}).values()
    }
def _refresh_orphans_after_edges(call_graph, previous_confidence: dict,
                                 new_edges: int) -> None:
    if not new_edges:
        return
    find_orphans(call_graph)
    for node in getattr(call_graph, "orphans", None) or []:
        previous = previous_confidence.get(id(node))
        if previous is not None:
            node.confidence = previous
class _MergeCtx:
    def __init__(self, call_graph: Any) -> None:
        self.call_graph = call_graph
        self.new_edges = 0
        self.edges_in_graph = 0
        self._funcs_map, self._calls_list = _graph_views(call_graph)
        self._named_funcs = {
            key: node for key, node in (self._funcs_map or {}).items()
            if isinstance(key, str)}
        self._existing_funcs: set[str] = set(self._named_funcs)
        self._segment_index: dict[str, tuple[str, ...]] = self._build_segment_index()
        self._exact_index, self._span_index = self._build_span_indexes()
        self._merged_edge_keys: set[tuple[str, str]] = self._existing_edge_keys()
    def _build_segment_index(self) -> dict[str, tuple[str, ...]]:
        index: dict[str, list[str]] = {}
        for fqn in sorted(self._existing_funcs):
            index.setdefault(fqn.rsplit(".", 1)[-1], []).append(fqn)
        return {seg: tuple(fqns) for seg, fqns in index.items()}
    def _existing_edge_keys(self) -> set[tuple[str, str]]:
        return {
            (getattr(e, "caller_func", ""), getattr(e, "callee_func", ""))
            for e in (self._calls_list or [])
        }
    @staticmethod
    def _index_span(exact_index: dict, span_index: dict, fqn: str,
                    file_path: str, norm: str, line: int) -> None:
        exact_index.setdefault((norm, line), []).append(fqn)
        span_index.setdefault(
            (os.path.basename(file_path), line), []).append((fqn, norm))
    def _index_function(self, exact_index: dict, span_index: dict,
                        fqn: str, fnode: Any) -> None:
        fp = _str_file(getattr(fnode, "filepath", ""))
        sl = _int_line(getattr(fnode, "start_line", 0))
        if not (fp and sl):
            return
        norm = _path_key(fp)
        self._index_span(exact_index, span_index, fqn, fp, norm, sl)
        dl = _int_line(getattr(fnode, "decor_line", 0))
        if dl and dl != sl:
            self._index_span(exact_index, span_index, fqn, fp, norm, dl)
    def _build_span_indexes(self) -> tuple[dict, dict]:
        exact_index: dict = {}
        span_index: dict = {}
        for fqn, fnode in self._named_funcs.items():
            self._index_function(exact_index, span_index, fqn, fnode)
        return exact_index, span_index
    def exists_in_graph(self, name: str) -> bool:
        name = _str_name(name)
        if not name:
            return False
        if name in self._existing_funcs:
            return True
        return name.rsplit(".", 1)[-1] in self._segment_index
    def resolve_in_graph_fqns(self, name: str, file: str, line: int) -> list:
        name = _str_name(name)
        if not name:
            return []
        if name in self._existing_funcs:
            return [name]
        r_file = _str_file(file)
        r_line = _int_line(line)
        if r_file and r_line:
            span_hit = self._resolve_by_span(r_file, r_line)
            if span_hit:
                return span_hit
        return list(self._segment_index.get(name.rsplit(".", 1)[-1], ()))
    def _resolve_by_span(self, r_file: str, r_line: int):
        exact = self._exact_index.get((_path_key(r_file), r_line))
        if exact:
            return list(exact)
        hit = self._span_index.get((os.path.basename(r_file), r_line))
        if hit:
            consistent = [fqn for fqn, fp in hit
                          if _paths_consistent(r_file, fp)]
            if consistent:
                return consistent
        return None
    def _register_edge(self, caller_key: str, callee_key: str,
                       edge: CallEdge) -> None:
        self._calls_list.append(edge)
        _register_caller(
            getattr(self.call_graph, "callers", None), callee_key, caller_key)
        self.new_edges += 1
    def _add_edge(self, caller_key: str, callee_key: str, target_file: str,
                  target_line: int, callee_file: str) -> bool:
        if self._calls_list is None:
            return False
        edge_key = (caller_key, callee_key)
        if edge_key in self._merged_edge_keys:
            return False
        self._merged_edge_keys.add(edge_key)
        self._register_edge(caller_key, callee_key, CallEdge(
            caller_file=target_file,
            caller_func=caller_key,
            callee_func=callee_key,
            callee_file=callee_file,
            line=target_line,
            is_external=False,
        ))
        return True
    def add_in_graph_edge(self, prefix: str, owner: str, target_fqn: str,
                          target_file: str, target_line: int) -> None:
        fnode = (self._funcs_map.get(target_fqn)
                 if self._funcs_map is not None else None)
        created = self._add_edge(
            f"{prefix}:{owner}", target_fqn, target_file, target_line,
            callee_file=(getattr(fnode, "filepath", "") or target_file))
        if created:
            self.edges_in_graph += 1
    def add_synth_edge(self, prefix: str, owner: str, target_name: str,
                       target_file: str, target_line: int) -> None:
        if target_name == "<unknown>":
            return
        if self._calls_list is None:
            return
        synth_key = f"{prefix}:{target_name}"
        if self._funcs_map is None:
            callee_file = target_file
        else:
            synth_key, callee_file, _created = _ensure_synthetic_node(
                self._funcs_map, synth_key, target_file, target_line)
        self._add_edge(
            f"{prefix}:{owner}", synth_key, target_file, target_line,
            callee_file=callee_file)
    def merge_callback_entries(self, items: Any, prefix: str,
                               fields: tuple[str, str, str, str]) -> None:
        owner_field, cb_field, file_field, line_field = fields
        for it in _iter_entries(items, channel=f"{prefix} 订阅/注册通道"):
            cb_name = _str_name(_entry_field(it, cb_field))
            if not cb_name:
                logger.warning(
                    "[CallGraph] %s 条目缺回调名,跳过: %r", prefix, it)
                continue
            cb_file = _str_file(_entry_field(it, file_field))
            cb_line = _int_line(_entry_field(it, line_field, 0))
            owner = _str_name(_entry_field(it, owner_field))
            if not owner:
                logger.warning(
                    "[CallGraph] %s 条目缺归属实例,跳过: %r", prefix, it)
                continue
            fqns = self.resolve_in_graph_fqns(cb_name, cb_file, cb_line)
            if fqns:
                for fqn in fqns:
                    self.add_in_graph_edge(
                        prefix, owner, fqn, cb_file, cb_line)
            else:
                self.add_synth_edge(
                    prefix, owner, cb_name, cb_file, cb_line)
    def count_graph_resolvable(self, names: Any) -> int:
        total = 0
        for name in names:
            name_s = _str_name(name)
            if name_s and self.exists_in_graph(name_s):
                total += 1
        return total
def _count_resolvable_registrations(ctx: _MergeCtx,
                                    binding_report: Any) -> int:
    names = [
        _entry_field(entry, field)
        for attr, field, channel in _COUNT_ONLY_CHANNELS
        for entry in _iter_entries(
            getattr(binding_report, attr, None), channel=channel)
    ]
    return ctx.count_graph_resolvable(names)
def merge_bindings_into_callgraph(
    call_graph: Any,
    binding_report: Any,
) -> dict:
    previous_confidence = _function_confidence_snapshot(call_graph)
    ctx = _MergeCtx(call_graph)
    ctx.merge_callback_entries(
        getattr(binding_report, "event_subscriptions", None),
        "<event>", _EVENT_ENTRY_FIELDS)
    ctx.merge_callback_entries(
        getattr(binding_report, "registry_entries", None),
        "<registry>", _REGISTRY_ENTRY_FIELDS)
    bindings_resolved = _count_resolvable_registrations(ctx, binding_report)
    unresolved = max(0, ctx.new_edges - ctx.edges_in_graph)
    _refresh_orphans_after_edges(
        call_graph, previous_confidence, ctx.new_edges)
    invalidate = getattr(call_graph, "invalidate_analysis_caches", None)
    if callable(invalidate):
        invalidate()
    return {
        "bindings_total": _int_line(
            getattr(binding_report, "total_bindings", 0)),
        "new_edges": ctx.new_edges,
        "edges_resolved": ctx.edges_in_graph,
        "bindings_resolved": bindings_resolved,
        "resolved": ctx.edges_in_graph + bindings_resolved,
        "unresolved": unresolved,
    }
def _project_module_namespace(skill_dir: str) -> dict:
    _abs_root = os.path.normpath(os.path.abspath(skill_dir))
    _skill_root = os.path.normcase(_abs_root)
    return {k: v for k, v in list(sys.modules.items())
            if _ns_mod_match(k, v, _skill_root)}
def scan_runtime_bindings(graph, skill_dir) -> tuple[dict, Any]:
    skill_dir = _str_file(skill_dir)
    if not skill_dir.strip():
        raise ValueError("skill_dir 必须是非空路径")
    report = RuntimeBindingScanner().scan(
        namespace=_project_module_namespace(skill_dir),
        call_graph=graph, project_root=skill_dir)
    return _binding_observed_counts(report), report
def _observed_entries_count(entries) -> int:
    if entries is None:
        return 0
    if isinstance(entries, (list, tuple, set, frozenset)):
        return len(entries)
    logger.warning("[CallGraph] 绑定条目形态非法,按 0 计: %r", type(entries))
    return 0
def _binding_observed_counts(report) -> dict:
    return {
        binding_type: _observed_entries_count(entries)
        for binding_type, entries in (
            ("registry", getattr(report, 'registry_entries', [])),
            ("event_sub", getattr(report, 'event_subscriptions', [])),
            ("dynamic_attr", getattr(report, 'dynamic_attributes', [])),
            ("decorator", getattr(report, 'decorator_registrations', [])),
            ("init_subclass", getattr(report, 'init_subclass_registrations', [])),
        )
    }
def _safe_module_attr(module, name: str, default, context: str):
    try:
        return getattr(module, name, default)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context=f"{context}:{type(_e).__name__}")
        return default
def _ns_paths_within_root(paths, skill_root: str) -> bool:
    try:
        return any(isinstance(path, str) and path
                   and _file_within_root(path, skill_root) for path in paths)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context=(
            f'diag_callgraph_channels._ns_mod_match:PathIter:{type(_e).__name__}'))
        return False
def _ns_mod_match(_k: str, _v, _skill_root: str) -> bool:
    _f = _safe_module_attr(_v, "__file__", "",
                           'diag_callgraph_channels._ns_mod_match.File')
    if isinstance(_f, str) and _f:
        return _file_within_root(_f, _skill_root)
    _paths = _safe_module_attr(_v, "__path__", (),
                               'diag_callgraph_channels._ns_mod_match.Path')
    if _paths is None or isinstance(_paths, (str, bytes)):
        return False
    return _ns_paths_within_root(_paths, _skill_root)
def _file_within_root(file_path: str, root: str) -> bool:
    try:
        normalized = canonical_path(file_path)
        normalized_root = canonical_path(root)
        return os.path.commonpath(
            [normalized, normalized_root]) == normalized_root
    except (OSError, TypeError, ValueError) as _e:
        log_swallowed(__name__, _e, context=(
            f'diag_callgraph_channels._file_within_root:{type(_e).__name__}'))
        return False
def _normalize_trace_edges(trace_edges) -> list:
    if trace_edges is None:
        return []
    if not isinstance(trace_edges, (list, tuple)):
        logger.warning(
            "merge_trace_into_callgraph trace_edges 非列表形态: %r，按空载荷处理",
            trace_edges)
        return []
    return list(trace_edges)
def merge_trace_into_callgraph(call_graph: Any, trace_edges: list[tuple[str, str, str, str, int]]) -> dict:
    trace_edges = _normalize_trace_edges(trace_edges)
    _funcs, _calls = _graph_views(call_graph)
    if _funcs is None or _calls is None:
        return {"trace_total": len(trace_edges), "new_edges": 0,
                "new_functions": 0, "resolved_dynamic": 0, "unresolved": 0}
    previous_confidence = _function_confidence_snapshot(call_graph)
    ast_edge_index = _build_trace_dedup_index(call_graph)
    func_simple_to_files = _index_functions_by_simple_name(call_graph)
    new_edges = 0
    new_functions = 0
    resolved_dynamic = 0
    for trace_edge in trace_edges:
        _ne, _nf, _rd = _merge_single_trace_edge(
            call_graph, ast_edge_index, func_simple_to_files, trace_edge)
        new_edges += _ne
        new_functions += _nf
        resolved_dynamic += _rd
    if new_edges:
        _refresh_orphans_after_edges(
            call_graph, previous_confidence, new_edges)
        _invalidate = getattr(call_graph, "invalidate_analysis_caches", None)
        if callable(_invalidate):
            _invalidate()
    return {
        "trace_total": len(trace_edges),
        "new_edges": new_edges,
        "new_functions": new_functions,
        "resolved_dynamic": resolved_dynamic,
        "unresolved": new_edges - resolved_dynamic,
    }
def _trace_paths_consistent(left, right) -> bool:
    left = _str_name(left)
    right = _str_name(right)
    if not left or not right:
        return left == right
    return _paths_consistent(left, right)
def _register_trace_dedup(index, caller, callee, caller_file, callee_file) -> None:
    record = (caller, callee, _str_name(caller_file),
              _str_name(callee_file))
    index.setdefault((caller, callee), []).append(record)
def _observed_trace_identity(edge) -> tuple[str, str, str, str]:
    return (
        _str_name(edge.caller_func),
        _str_name(edge.callee_func),
        _str_name(getattr(edge, "caller_file", "")),
        _str_name(getattr(edge, "callee_file", "")),
    )
def _build_trace_dedup_index(call_graph) -> dict:
    index = {}
    for edge in call_graph.calls:
        _register_trace_dedup(index, *_observed_trace_identity(edge))
    return index
def _trace_edge_duplicate(index, caller, callee, caller_file, callee_file) -> bool:
    candidates = index.get((caller, callee), ())
    return any(
        caller == old_caller
        and callee == old_callee
        and _trace_paths_consistent(caller_file, old_caller_file)
        and _trace_paths_consistent(callee_file, old_callee_file)
        for old_caller, old_callee, old_caller_file, old_callee_file
        in candidates)
def _index_functions_by_simple_name(call_graph) -> dict:
    func_simple_to_files: dict[str, list[str]] = {}
    for key in call_graph.functions:
        if not isinstance(key, str):
            continue
        simple = key.split('.')[-1]
        if simple not in func_simple_to_files:
            func_simple_to_files[simple] = []
        func_simple_to_files[simple].append(key)
    return func_simple_to_files
def _fnode_filepath(call_graph, key: str) -> str:
    return _str_file(getattr(call_graph.functions.get(key), "filepath", ""))
def _trace_name_candidates(call_graph, func_simple_to_files: dict,
                           name: str) -> list[str]:
    def bare_candidates(simple: str) -> list[str]:
        return [
            key for key in func_simple_to_files.get(simple, [])
            if not getattr(call_graph.functions[key], "is_method", False)
            and not getattr(call_graph.functions[key], "class_name", None)
        ]
    if "." not in name:
        return bare_candidates(name)
    parts = [part for part in name.split(".") if part and part != "<locals>"]
    suffixes = {
        ".".join(parts[start:]) for start in range(max(0, len(parts) - 1))
    }
    candidates = [
        key for key in call_graph.functions if isinstance(key, str)
        and any(key.endswith("." + suffix) for suffix in suffixes)
    ]
    return candidates
def _resolve_simple_name_target(call_graph, func_simple_to_files: dict,
                                callee: str, callee_file) -> tuple[str, str] | None:
    candidates = _trace_name_candidates(
        call_graph, func_simple_to_files, callee)
    if not candidates:
        return None
    same_file = [c for c in candidates
                 if _trace_paths_consistent(
                     callee_file, _fnode_filepath(call_graph, c))]
    if (not same_file and callee_file
            and any(_fnode_filepath(call_graph, c) for c in candidates)):
        return None
    pool = same_file or candidates
    if len(pool) != 1:
        return None
    resolved_callee = pool[0]
    resolved_file = _fnode_filepath(call_graph, resolved_callee) or callee_file
    return resolved_callee, resolved_file
def _ensure_synthetic_node(functions: dict, base_key: str, callee_file: str,
                           line: int) -> tuple[str, str, bool]:
    candidates = [key for key in functions
                  if key == base_key or (
                      key.startswith(base_key + "#")
                      and key[len(base_key) + 1:].isdigit())]
    candidates.sort(key=lambda key: (
        0 if key == base_key else int(key[len(base_key) + 1:])))
    for synth_key in candidates:
        existing = functions[synth_key]
        existing_file = _str_file(getattr(existing, "filepath", ""))
        if (existing_file and callee_file
                and not _trace_paths_consistent(existing_file, callee_file)):
            continue
        if not existing_file and callee_file:
            existing.filepath = callee_file
            existing_file = callee_file
        return synth_key, existing_file, False
    used_numbers = [int(key[len(base_key) + 1:])
                    for key in candidates if key != base_key]
    synth_key = (base_key if base_key not in functions
                 else f"{base_key}#{max(used_numbers, default=1) + 1}")
    functions[synth_key] = FunctionNode(
        name=synth_key,
        filepath=callee_file,
        start_line=line,
        end_line=line,
        is_public=False,
        is_synthetic=True,
    )
    return synth_key, callee_file, True
def _resolve_trace_target(call_graph, func_simple_to_files: dict,
                          callee: str, callee_file, line):
    if callee in call_graph.functions:
        static_file = _fnode_filepath(call_graph, callee)
        if not (static_file and callee_file
                and not _trace_paths_consistent(static_file, callee_file)):
            return callee, static_file or callee_file, False
    resolved = _resolve_simple_name_target(
        call_graph, func_simple_to_files, callee, callee_file)
    if resolved is not None:
        resolved_callee, resolved_file = resolved
        return resolved_callee, resolved_file, False
    return _ensure_synthetic_node(
        call_graph.functions, f"<dynamic>:{callee}", callee_file, line)
def _trace_module_scope_key(call_graph, caller_file: str) -> str:
    file_text = _str_file(caller_file)
    root = _str_file(getattr(call_graph, "project_root", ""))
    if not file_text or not root:
        return _MODULE_SCOPE_NAME
    try:
        resolved = _resolve_source_filepath(file_text, call_graph)
        abs_file = os.path.realpath(resolved)
        abs_root = os.path.realpath(root)
        if (os.path.commonpath([
                os.path.normcase(abs_file), os.path.normcase(abs_root)])
                != os.path.normcase(abs_root)):
            return _MODULE_SCOPE_NAME
        rel_path = os.path.relpath(abs_file, abs_root)
    except (OSError, ValueError):
        return _MODULE_SCOPE_NAME
    module = path_to_dotted_module(rel_path.replace("\\", "/"))
    return _qualify_module_member(module, _MODULE_SCOPE_NAME)
def _resolve_trace_caller_name(call_graph, func_simple_to_files: dict,
                               caller: str, caller_file: str) -> str:
    if caller == _MODULE_SCOPE_NAME:
        return _trace_module_scope_key(call_graph, caller_file)
    if caller in call_graph.functions:
        static_file = _fnode_filepath(call_graph, caller)
        if (static_file and caller_file
                and not _trace_paths_consistent(static_file, caller_file)):
            return f"<dynamic>:{caller}"
        return caller
    resolved = _resolve_simple_name_target(
        call_graph, func_simple_to_files, caller, caller_file)
    return resolved[0] if resolved is not None else caller
def _merge_single_trace_edge(call_graph, ast_edge_index: dict,
                             func_simple_to_files: dict, trace_edge) -> tuple[int, int, int]:
    if not isinstance(trace_edge, (tuple, list)) or len(trace_edge) != 5:
        logger.warning("trace 边形态非法（期望 5 元组），跳过: %r", trace_edge)
        return 0, 0, 0
    caller, callee, caller_file, callee_file, line = trace_edge
    caller = _str_name(caller)
    callee = _str_name(callee)
    if not caller or not callee:
        logger.warning("trace 边缺函数名，跳过: %r", trace_edge)
        return 0, 0, 0
    caller_file = _str_name(caller_file)
    callee_file = _str_name(callee_file)
    line = _int_line(line)
    if _trace_edge_duplicate(
            ast_edge_index, caller, callee, caller_file, callee_file):
        return 0, 0, 0
    caller = _resolve_trace_caller_name(
        call_graph, func_simple_to_files, caller, caller_file)
    resolved_caller_file = _fnode_filepath(call_graph, caller) or caller_file
    resolved_callee, resolved_file, created = _resolve_trace_target(
        call_graph, func_simple_to_files, callee, callee_file, line)
    if _trace_edge_duplicate(
            ast_edge_index, caller, resolved_callee,
            resolved_caller_file, resolved_file):
        return 0, 0, 0
    edge = CallEdge(
        caller_file=resolved_caller_file or resolved_file,
        caller_func=caller,
        callee_func=resolved_callee,
        callee_file=resolved_file,
        line=line,
        is_external=False,
    )
    edge._trace_observation = (caller, callee, caller_file, callee_file)
    call_graph.calls.append(edge)
    _register_trace_dedup(
        ast_edge_index, caller, resolved_callee,
        resolved_caller_file, resolved_file)
    _register_caller(
        getattr(call_graph, "callers", None), resolved_callee, caller)
    return 1, (1 if created else 0), (0 if resolved_callee.startswith('<dynamic>') else 1)
def merge_trace_edges(call_graph, trace_edges, sim_report) -> None:
    if not trace_edges or call_graph is None:
        return
    merge_result = merge_trace_into_callgraph(call_graph, trace_edges)
    sim_report.trace_merge = merge_result
    logger.info(f"  [Trace] 合并: +{merge_result['new_edges']} 边, "
                f"解析 {merge_result['resolved_dynamic']}/"
                f"{merge_result['trace_total']}")
class FallbackCallGraph:
    def __init__(self, forward_graph: dict[str, set[str]],
                 callers: dict[str, set[str]]) -> None:
        self.functions: dict[str, Any] = dict.fromkeys(forward_graph)
        self.callers = callers
def _strip_root_pkg_prefix(name: str, root_pkg: str) -> str:
    if root_pkg and name.startswith(root_pkg + "."):
        return name[len(root_pkg) + 1:]
    return name
_UNBOUND = object()


def _call_position(call: ast.Call) -> tuple[int, int]:
    fallback = getattr(call, "func", None)
    line = (_int_line(getattr(call, "lineno", 0))
            or _int_line(getattr(fallback, "lineno", 0)))
    column = _int_line(getattr(call, "col_offset", 0))
    if not getattr(call, "lineno", 0):
        column = _int_line(getattr(fallback, "col_offset", 0))
    return line, column


def _binding_event_visible(event: tuple, line: int, column: int) -> bool:
    event_line, event_column, _sequence, _value, executable, definition = event
    if not executable:
        return False
    if definition and event_line >= line:
        return False
    return (event_line, event_column) <= (line, column)


class _OrderedBindings(dict[str, str]):
    def __init__(self) -> None:
        super().__init__()
        self._events: dict[str, list[tuple]] = {}
        self._sequence = 0

    def bind(self, name: str, value: str, node: ast.AST, *,
             executable: bool = True, definition: bool = False) -> None:
        self._sequence += 1
        event = (
            _int_line(getattr(node, "lineno", 0)),
            _int_line(getattr(node, "col_offset", 0)),
            self._sequence, value, executable, definition,
        )
        self._events.setdefault(name, []).append(event)
        if executable:
            self[name] = value

    def has_events(self, name: str) -> bool:
        return name in self._events

    def resolve_at(self, name: str, call: ast.Call):
        events = self._events.get(name)
        if not events:
            return None
        line, column = _call_position(call)
        if not line:
            return self.get(name, _UNBOUND)
        visible = [event for event in events
                   if _binding_event_visible(event, line, column)]
        if not visible:
            return _UNBOUND
        return max(visible, key=lambda event: event[2])[3]


class _ScopedBindings:
    def __init__(self, parent: dict[str, str]) -> None:
        self.parent = parent
        self.local = _OrderedBindings()

    def bind(self, name: str, value: str, node: ast.AST, *,
             executable: bool = True, definition: bool = False) -> None:
        self.local.bind(
            name, value, node, executable=executable, definition=definition)

    def get(self, name: str, default=None):
        if self.local.has_events(name):
            return self.local.get(name, default)
        return self.parent.get(name, default)

    def resolve_at(self, name: str, call: ast.Call):
        if self.local.has_events(name):
            return self.local.resolve_at(name, call)
        return self.parent.get(name)


def _binding_value(bindings: dict[str, str], name: str, call: ast.Call):
    resolver = getattr(bindings, "resolve_at", None)
    return resolver(name, call) if callable(resolver) else bindings.get(name)


def _store_binding(bindings: dict[str, str], name: str, value: str,
                   node: ast.AST, *, executable: bool = True,
                   definition: bool = False) -> None:
    binder = getattr(bindings, "bind", None)
    if callable(binder):
        binder(name, value, node, executable=executable, definition=definition)
    elif executable:
        bindings[name] = value


def _bind_from_import(node: ast.ImportFrom, module_prefix: str, fpath: str,
                      bindings: dict[str, str], *,
                      executable: bool = True) -> None:
    rel_mod = relative_import_module(node, module_prefix, fpath)
    for alias in node.names:
        if alias.name == "*":
            continue
        local = alias.asname or alias.name
        _store_binding(bindings, local, _qualify(rel_mod, alias.name), node,
                       executable=executable)


def _bind_plain_import(node: ast.Import, bindings: dict[str, str], *,
                       executable: bool = True) -> None:
    for alias in node.names:
        if alias.asname:
            _store_binding(bindings, alias.asname, alias.name, node,
                           executable=executable)
        else:
            top = alias.name.split(".")[0]
            _store_binding(bindings, top, top, node, executable=executable)


def _iter_scope_imports(statements: list[ast.stmt]) -> Iterator[ast.AST]:
    module = ast.Module(body=list(statements), type_ignores=[])
    for node in _iter_scope_nodes_preorder(module):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            yield node


def _bind_import_nodes(nodes: Iterator[ast.AST], module_prefix: str,
                       fpath: str, bindings: dict[str, str], *,
                       unexecuted_body_ids=frozenset()) -> None:
    for node in nodes:
        executable = id(node) not in unexecuted_body_ids
        if isinstance(node, ast.ImportFrom):
            _bind_from_import(
                node, module_prefix, fpath, bindings, executable=executable)
        else:
            _bind_plain_import(node, bindings, executable=executable)


def _collect_scope_bindings(tree: ast.AST, module_prefix: str, fpath: str,
                            *, include_definitions: bool) -> _OrderedBindings:
    bindings = _OrderedBindings()
    unexecuted_body_ids = _unexecuted_body_node_ids(tree)
    module = ast.Module(body=list(tree.body), type_ignores=[])
    for node in _iter_scope_nodes_preorder(module):
        executable = id(node) not in unexecuted_body_ids
        if isinstance(node, ast.ImportFrom):
            _bind_from_import(
                node, module_prefix, fpath, bindings, executable=executable)
        elif isinstance(node, ast.Import):
            _bind_plain_import(node, bindings, executable=executable)
        elif (include_definitions and executable
              and isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                    ast.ClassDef))):
            _store_binding(
                bindings, node.name, _qualify(module_prefix, node.name), node,
                definition=True)
    return bindings



def _class_reference_in_scope(
        name: str, class_scope_name: str,
        class_names: frozenset[str],
        class_qualnames: frozenset[str]) -> str:
    if class_scope_name:
        nested = f"{class_scope_name}.{name}"
        if nested in class_qualnames:
            return nested
    return name if name in class_names else ""
def _callee_for_name_call(call: ast.Call, module_prefix: str,
                          bindings: dict[str, str], root_pkg: str,
                          module_prefixes: set[str],
                          local_defs: frozenset[str],
                          class_names: frozenset[str],
                          class_qualnames: frozenset[str],
                          class_scope_name: str) -> str:
    name = call.func.id
    mapped = _binding_value(bindings, name, call)
    if mapped is _UNBOUND:
        return name
    if mapped is not None:
        return _resolve_mapped_callee(
            mapped, root_pkg, module_prefixes)
    class_ref = _class_reference_in_scope(
        name, class_scope_name, class_names, class_qualnames)
    if class_ref:
        return _qualify(module_prefix, class_ref)
    if name in local_defs:
        return _qualify(module_prefix, name)
    return name
def _definition_prefix_split(
    chain: str, module_prefixes: set[str],
) -> tuple[str, list[str]] | None:
    segs = chain.split(".")
    for cut in range(len(segs) - 1, 0, -1):
        prefix = ".".join(segs[:cut])
        remainder = segs[cut:]
        if prefix in module_prefixes:
            return prefix, remainder
        nested = [m for m in module_prefixes if m.endswith("." + prefix)]
        if len(nested) == 1:
            return nested[0], remainder
    return None
def _resolve_mapped_callee(chain: str, root_pkg: str,
                           module_prefixes: set[str]) -> str:
    stripped = _strip_root_pkg_prefix(chain, root_pkg)
    for candidate in dict.fromkeys((stripped, chain)):
        split = _definition_prefix_split(candidate, module_prefixes)
        if split is None:
            continue
        prefix, remainder = split
        return ".".join([prefix, *remainder]) if remainder else prefix
    return stripped
def _callee_for_attr_call(call: ast.Call, module_prefix: str,
                          bindings: dict[str, str], root_pkg: str,
                          module_prefixes: set[str],
                          class_name: str,
                          class_names: frozenset[str],
                          class_qualnames: frozenset[str],
                          class_scope_name: str) -> str | None:
    parts = [call.func.attr]
    cur = call.func.value
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if not isinstance(cur, ast.Name):
        return None
    parts.append(cur.id)
    parts.reverse()
    base = parts[0]
    tail = ".".join(parts[1:])
    if base in SELF_CLS_NAMES and class_name:
        return (_qualify(module_prefix, f"{class_name}.{tail}")
                if len(parts) == 2 else ".".join(parts))
    mapped = _binding_value(bindings, base, call)
    if mapped is _UNBOUND:
        return ".".join(parts)
    if mapped:
        return _resolve_mapped_callee(
            f"{mapped}.{tail}" if tail else mapped,
            root_pkg, module_prefixes)
    class_ref = _class_reference_in_scope(
        base, class_scope_name, class_names, class_qualnames)
    if class_ref and len(parts) == 2:
        return _qualify(module_prefix, f"{class_ref}.{tail}")
    if tail:
        return ".".join(parts)
    return _qualify(module_prefix, base)
def _callee_key_for_call(call: ast.Call, module_prefix: str,
                         bindings: dict[str, str], root_pkg: str,
                         module_prefixes: set[str],
                         class_name: str,
                         local_defs: frozenset[str],
                         class_names: frozenset[str],
                         class_qualnames: frozenset[str],
                         class_scope_name: str
                         ) -> str | None:
    if isinstance(call.func, ast.Name):
        return _callee_for_name_call(
            call, module_prefix, bindings, root_pkg, module_prefixes,
            local_defs, class_names, class_qualnames, class_scope_name)
    if isinstance(call.func, ast.Attribute):
        return _callee_for_attr_call(
            call, module_prefix, bindings, root_pkg, module_prefixes,
            class_name, class_names, class_qualnames, class_scope_name)
    return None
def _unexecuted_body_node_ids(tree: ast.AST) -> set[int]:
    skipped = type_checking_body_node_ids(tree)
    for node in walk_nodes(tree):
        if (isinstance(node, (ast.If, ast.While))
                and _is_constant_false_test(node.test)):
            for stmt in node.body:
                skipped.update(id(sub) for sub in walk_nodes(stmt))
    return skipped


def _iter_function_calls(
        func_node: ast.AST, postponed_annotations: bool = False,
        unexecuted_body_ids: frozenset[int] = frozenset(),
) -> Iterator[ast.Call]:
    def walk(node: ast.AST, in_class_body: bool = False):
        if id(node) in unexecuted_body_ids:
            return
        if isinstance(node, ast.Call):
            yield node
        if isinstance(node, ast.Lambda):
            defaults = (
                *node.args.defaults,
                *(value for value in node.args.kw_defaults if value is not None),
            )
            for default in defaults:
                yield from walk(default, in_class_body)
            # 函数体内的 lambda 体在被调用时执行，调用边归属于当前函数；
            # 旧实现只特判了 ``(lambda: ...)()`` 立即调用，赋值/传参场景
            # （``cb = lambda: h()``、``f(lambda: h())``）的调用边全部丢失。
            yield from walk(node.body, in_class_body)
            return
        if isinstance(node, ast.AnnAssign):
            children = [node.target]
            if node.value is not None:
                children.append(node.value)
            if in_class_body and not postponed_annotations:
                children.append(node.annotation)
            for child in children:
                yield from walk(child, in_class_body)
            return
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            expressions = [
                *node.decorator_list, *node.args.defaults,
                *(value for value in node.args.kw_defaults if value is not None),
            ]
            if not postponed_annotations:
                expressions.extend(_iter_definition_annotations(node))
            for expression in expressions:
                yield from walk(expression, in_class_body)
            return
        if isinstance(node, ast.ClassDef):
            for expression in [
                    *node.decorator_list, *node.bases,
                    *(keyword.value for keyword in node.keywords)]:
                yield from walk(expression, in_class_body)
            for stmt in node.body:
                yield from walk(stmt, True)
            return
        for child in ast.iter_child_nodes(node):
            yield from walk(child, in_class_body)
    for stmt in list(getattr(func_node, "body", ()) or ()):
        yield from walk(stmt)
def _calls_in_expressions(expressions) -> Iterator[ast.Call]:
    def walk(node):
        if isinstance(node, ast.Lambda):
            defaults = (
                *node.args.defaults,
                *(value for value in node.args.kw_defaults if value is not None),
            )
            for default in defaults:
                yield from walk(default)
            return
        if isinstance(node, ast.Call):
            yield node
            if isinstance(node.func, ast.Lambda):
                yield from walk(node.func.body)
        for child in ast.iter_child_nodes(node):
            yield from walk(child)
    for expression in expressions:
        yield from walk(expression)
def _calls_in_decorator_expressions(expressions) -> Iterator[ast.Call]:
    for expression in expressions:
        invocation = (expression if isinstance(expression, ast.Call) else
                      ast.Call(func=expression, args=[], keywords=[]))
        yield from _calls_in_expressions([invocation])
def _iter_module_execution_calls(
        tree: ast.AST) -> Iterator[tuple[ast.Call, str]]:
    postponed_annotations = module_postpones_annotations(tree)
    unexecuted_body_ids = _unexecuted_body_node_ids(tree)
    def definition_expressions(node) -> list:
        expressions = [
            *node.args.defaults,
            *(value for value in node.args.kw_defaults if value is not None),
        ]
        if not postponed_annotations:
            expressions.extend(_iter_definition_annotations(node))
        return expressions
    def scoped_calls(expressions, class_scope_name: str, decorator: bool = False):
        collector = (_calls_in_decorator_expressions if decorator
                     else _calls_in_expressions)
        for call in collector(expressions):
            yield call, class_scope_name
    def walk_body(body: list[ast.stmt], class_scope_name: str):
        for stmt in body:
            if id(stmt) in unexecuted_body_ids:
                continue
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                yield from scoped_calls(
                    stmt.decorator_list, class_scope_name, decorator=True)
                yield from scoped_calls(
                    definition_expressions(stmt), class_scope_name)
            elif isinstance(stmt, ast.ClassDef):
                yield from scoped_calls(
                    stmt.decorator_list, class_scope_name, decorator=True)
                yield from scoped_calls([
                    *stmt.bases,
                    *(keyword.value for keyword in stmt.keywords),
                ], class_scope_name)
                nested = (f"{class_scope_name}.{stmt.name}"
                          if class_scope_name else stmt.name)
                yield from walk_body(stmt.body, nested)
            elif isinstance(stmt, ast.AnnAssign) and postponed_annotations:
                expressions = [stmt.target]
                if stmt.value is not None:
                    expressions.append(stmt.value)
                yield from scoped_calls(expressions, class_scope_name)
            else:
                yield from walk_control_flow(stmt, class_scope_name)
    def walk_control_flow(node: ast.AST, class_scope_name: str):
        if id(node) in unexecuted_body_ids:
            return
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.stmt):
                yield from walk_body([child], class_scope_name)
            elif isinstance(child, ast.expr):
                yield from scoped_calls([child], class_scope_name)
            else:
                yield from walk_control_flow(child, class_scope_name)
    yield from walk_body(list(getattr(tree, "body", ()) or ()), "")
def _collect_call_edges(
    tree: ast.AST, module_prefix: str, bindings: dict[str, str],
    root_pkg: str, fallback_graph: dict[str, set[str]],
    module_prefixes: set[str], filepath: str,
    local_defs: frozenset[str],
    class_names: frozenset[str],
    class_qualnames: frozenset[str],
) -> None:
    module_callees = set()
    for child, class_scope_name in _iter_module_execution_calls(tree):
        callee = _callee_key_for_call(
            child, module_prefix, bindings, root_pkg, module_prefixes,
            "", local_defs, class_names, class_qualnames, class_scope_name)
        if callee is not None:
            module_callees.add(callee)
    if module_callees:
        module_key = _qualify_module_member(
            module_prefix, _MODULE_SCOPE_NAME)
        fallback_graph.setdefault(module_key, set()).update(module_callees)
    postponed_annotations = module_postpones_annotations(tree)
    unexecuted_body_ids = frozenset(_unexecuted_body_node_ids(tree))
    for registered in _iter_registered_defs(tree):
        func_name = _qualify(module_prefix, registered.qualname)
        callees = fallback_graph.setdefault(func_name, set())
        local_bindings = _ScopedBindings(bindings)
        _bind_import_nodes(
            _iter_scope_imports(registered.node.body), module_prefix, filepath,
            local_bindings, unexecuted_body_ids=unexecuted_body_ids)
        for child in _iter_function_calls(
                registered.node, postponed_annotations, unexecuted_body_ids):
            callee = _callee_key_for_call(
                child, module_prefix, local_bindings, root_pkg,
                module_prefixes, registered.class_name, local_defs,
                class_names, class_qualnames, "")
            if callee is not None:
                callees.add(callee)
def _collect_module_prefixes(py_files: list[str],
                             skill_dir: str) -> set[str]:
    prefixes: set[str] = set()
    for fpath in py_files:
        mp = _module_prefix_of(fpath, skill_dir)
        if mp:
            prefixes.add(mp)
    return prefixes
def _module_scope_names(
        tree: ast.AST,
) -> tuple[frozenset[str], frozenset[str], frozenset[str]]:
    local_defs = {
        registered.qualname
        for registered in _iter_registered_defs(tree)
        if "." not in registered.qualname
    }
    class_qualnames = frozenset(
        path for path, _start, _end in _collect_class_spans(tree))
    class_names = frozenset(
        path for path in class_qualnames if "." not in path)
    return (frozenset(local_defs | class_names),
            class_names, class_qualnames)
def _resolve_reexport_callee(callee: str, module_bindings: dict,
                             root_pkg: str, module_prefixes: set[str],
                             fallback_graph: dict[str, set[str]]) -> str:
    resolved = callee
    visited = set()
    while resolved not in visited:
        visited.add(resolved)
        root_bindings = module_bindings.get("")
        extra_tail: list[str] = []
        if root_bindings and resolved in root_bindings:
            prefix, remainder = "", [resolved]
        else:
            # 根包（根 ``__init__.py``，模块前缀为空）再导出的属性尾段：
            # ``from .mod import C`` + ``C.run()`` 的首段 ``C`` 只在根绑定中，
            # ``_definition_prefix_split`` 找不到模块前缀。旧逻辑只在整名
            # 精确命中根绑定时才解析，``C.run`` 因此永不映射到 ``mod.C.run``。
            root_head, _, root_tail = resolved.partition(".")
            if (root_bindings and root_tail and root_head in root_bindings
                    and root_head not in module_prefixes):
                prefix, remainder = "", [root_head]
                extra_tail = [root_tail]
            else:
                split = _definition_prefix_split(resolved, module_prefixes)
                if split is None:
                    break
                prefix, remainder = split
        symbol, *attribute_tail = remainder
        attribute_tail.extend(extra_tail)
        mapped = module_bindings.get(prefix, {}).get(symbol)
        if mapped is None:
            break
        next_resolved = _resolve_mapped_callee(
            mapped, root_pkg, module_prefixes)
        if attribute_tail:
            next_resolved = ".".join([next_resolved, *attribute_tail])
        if next_resolved == resolved:
            break
        resolved = next_resolved
    return resolved if resolved in fallback_graph else callee
def _resolve_fallback_reexports(fallback_graph: dict[str, set[str]],
                                module_bindings: dict, root_pkg: str,
                                module_prefixes: set[str]) -> None:
    for caller, callees in fallback_graph.items():
        fallback_graph[caller] = {
            _resolve_reexport_callee(
                callee, module_bindings, root_pkg, module_prefixes,
                fallback_graph)
            for callee in callees
        }
def build_fallback_call_graph(skill_dir: str) -> dict[str, set[str]]:
    fallback_graph: dict[str, set[str]] = {}
    if not skill_dir or not os.path.isdir(skill_dir):
        return fallback_graph
    root_pkg = os.path.basename(os.path.normpath(skill_dir))
    py_files = sorted(iter_py_files_under(skill_dir), key=_path_key)
    module_prefixes = _collect_module_prefixes(py_files, skill_dir)
    module_bindings = {}
    for fpath in py_files:
        tree = _parse_source_file(fpath, "信号源")
        if tree is None:
            continue
        module_prefix = _module_prefix_of(fpath, skill_dir)
        bindings = _collect_scope_bindings(
            tree, module_prefix, fpath, include_definitions=True)
        module_bindings[module_prefix] = bindings
        local_defs, class_names, class_qualnames = _module_scope_names(tree)
        _collect_call_edges(
            tree, module_prefix, bindings, root_pkg, fallback_graph,
            module_prefixes, fpath, local_defs, class_names, class_qualnames)
    _resolve_fallback_reexports(
        fallback_graph, module_bindings, root_pkg, module_prefixes)
    return fallback_graph
def _ast_function_spans(tree: ast.AST) -> list[tuple[int, int, str]]:
    return [
        (registered.node.lineno, registered.node.end_lineno,
         registered.qualname)
        for registered in _iter_registered_defs(tree)
        if registered.node.lineno is not None
        and registered.node.end_lineno is not None
    ]
def fallback_resolve_function_name(filepath: str, line: int, skill_dir: str) -> str:
    if not isinstance(filepath, str) or not filepath or not os.path.exists(filepath):
        return ""
    if not isinstance(line, int) or isinstance(line, bool):
        return ""
    if skill_dir and not _file_within_root(filepath, skill_dir):
        return ""
    tree = _parse_source_file(filepath, "函数定位")
    if tree is None:
        return ""
    innermost = innermost_span(_ast_function_spans(tree), line)
    if not innermost:
        return ""
    module_prefix = _module_prefix_of(filepath, skill_dir)
    return f"{module_prefix}.{innermost}" if module_prefix else innermost
def _module_prefix_of(filepath: str, skill_dir: str) -> str:
    if not skill_dir:
        return ""
    try:
        _abs_fp = os.path.realpath(filepath)
        _abs_sd = os.path.realpath(skill_dir)
        if (os.path.commonpath([os.path.normcase(_abs_fp),
                                os.path.normcase(_abs_sd)])
                != os.path.normcase(_abs_sd)):
            return ""
        prefix = os.path.relpath(_abs_fp, _abs_sd)
    except (OSError, ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_module_prefix_of:{type(_e).__name__}')
        return ""
    return path_to_dotted_module(prefix)
logger.info("%s 已加载: %d 项导出", __name__, len(__all__))

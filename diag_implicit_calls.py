from __future__ import annotations

import ast
import functools
import logging
import os
import sys
import threading
import time
import types
from collections import defaultdict, deque
from collections.abc import Callable, Iterator, Mapping
from typing import Any

from jwsgj.diag_callgraph_facts import (
    FunctionNode,
    class_tail_index,
    method_to_classes_index,
)
from jwsgj.diag_callgraph_verdicts import (
    CallGraph,
    CallGraphBuilderProtocol,
    append_synthetic_edge,
)
from jwsgj.diag_shared_ast_nodes import (
    is_dunder_name,
    normalize_torn_name,
    path_to_dotted_module,
    pkg_root_name,
)
from jwsgj.diag_shared_source_core import read_cached
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_scope import (
    is_test_caller_name,
    is_test_file_path,
    prune_ignore_dirs,
)

logger = logging.getLogger(__name__)
__all__ = [
    "DynamicCallTracer",
    "RuntimeBindingReport",
    "RuntimeBindingScanner",
    "filter_suspicious_files",
    "generate_dataclass_methods",
    "link_implicit_calls",
    "link_init_subclass",
    "link_mixin_methods",
    "link_singledispatch",
]
def _existing_call_pairs(graph: CallGraph) -> set[tuple[str, str]]:
    return {(e.caller_func, e.callee_func) for e in graph.calls}
def _emit_synthetic_edge(graph: CallGraph, caller_func: str, callee_func: str,
                         *, caller_file: str,
                         existing_pairs: set[tuple[str, str]],
                         line: int | None = None,
                         args_count: int | None = None,
                         all_callers: dict[str, set[str]] | None = None
                         ) -> bool:
    pair = (caller_func, callee_func)
    if pair in existing_pairs:
        return False
    kwargs: dict[str, int] = {}
    if line is not None:
        kwargs["line"] = line
    if args_count is not None:
        kwargs["args_count"] = args_count
    append_synthetic_edge(
        graph, caller_func=caller_func, caller_file=caller_file,
        callee_fqn=callee_func, missing_ok=False, **kwargs)
    existing_pairs.add(pair)
    if all_callers is not None:
        all_callers[callee_func].add(caller_func)
    return True
def _name_seq(value: Any) -> tuple:
    if isinstance(value, str):
        return (value,) if value else ()
    if isinstance(value, (list, tuple, set, frozenset)):
        return tuple(value)
    return ()
def _split_ref(value) -> tuple[str, str] | None:
    parts = normalize_torn_name(value).rsplit(".", 1)
    return (parts[0], parts[1]) if len(parts) == 2 else None
def _ref_module(value) -> str:
    return normalize_torn_name(value).rsplit(".", 1)[0]
def _ref_basename(value) -> str:
    return normalize_torn_name(value).rsplit(".", 1)[-1]
def _method_key(cls_fqn: str, method_name: str) -> str:
    return f"{cls_fqn}.{method_name}"
def _caller_file_of(graph, caller_func: str, fallback: str) -> str:
    fnode = graph.functions.get(caller_func)
    return (fnode.filepath if fnode is not None and fnode.filepath
            else fallback)
def generate_dataclass_methods(graph: CallGraph) -> None:
    synthetic_methods = ("__init__", "__eq__", "__repr__")
    changed = False
    options_map = getattr(graph, "dataclass_options", None)
    if not isinstance(options_map, Mapping):
        options_map = {}
    classes = sorted(
        _name_seq(getattr(graph, "dataclass_classes", ())), key=str)
    for full_class in classes:
        normalized_class = normalize_torn_name(full_class)
        split = _split_ref(normalized_class)
        module, cls_name = split if split is not None else ("", normalized_class)
        if not cls_name:
            continue
        filepath = _resolve_dataclass_filepath(graph, full_class, module, cls_name)
        if not filepath:
            continue
        options = options_map.get(full_class)
        if not isinstance(options, Mapping):
            options = {}
        class_path = _dataclass_class_path(
            graph, full_class, cls_name, filepath)
        for method in synthetic_methods:
            if options.get(method[2:-2]) is False:
                continue
            changed = _synthesize_dataclass_method(
                graph, full_class, class_path, filepath, method) or changed
    if changed:
        graph.invalidate_analysis_caches()
def _resolve_dataclass_filepath(graph, full_class: str,
                                module: str, cls_name: str):
    filepath = graph.class_files.get(full_class)
    if not filepath:
        class_prefix = f"{module}.{cls_name}" if module else cls_name
        for fname, fnode in graph.functions.items():
            if normalize_torn_name(fname).startswith(f"{class_prefix}."):
                filepath = fnode.filepath
                break
    return filepath
def _dataclass_class_path(graph, full_class: str, cls_name: str,
                          filepath: str) -> str:
    module_name = _caller_module_name(graph, filepath)
    prefix = f"{module_name}." if module_name else ""
    normalized = normalize_torn_name(full_class)
    if prefix and normalized.startswith(prefix):
        class_path = normalized[len(prefix):]
        if class_path:
            return class_path
    elif not module_name and normalized:
        # 根包（根 ``__init__.py``）的类键本身就是类路径，没有模块前缀可剥；
        # 旧逻辑退回简单类名，会把嵌套类 ``Outer.Inner`` 的合成方法误归到 ``Inner``。
        return normalized
    return cls_name
def _synthesize_dataclass_method(graph, full_class: str, class_path: str,
                                 filepath: str, method: str) -> bool:
    key = f"{full_class}.{method}"
    if key in graph.functions:
        return False
    fnode = FunctionNode(
        name=f"{class_path}.{method}",
        filepath=filepath,
        start_line=0, end_line=0,
        is_public=True, is_async=False,
        is_method=True, class_name=class_path,
        is_synthetic=True,
    )
    fnode._project_root = graph.project_root
    graph.functions[key] = fnode
    graph.class_methods[class_path].add(method)
    return True
def link_init_subclass(graph: CallGraph) -> None:
    existing_pairs = _existing_call_pairs(graph)
    init_subclass_by_simple = _build_init_subclass_simple_index(graph)
    for sub_cls, base_names in graph.class_inheritance.items():
        sub_key = normalize_torn_name(sub_cls)
        mro_targets = _init_subclass_mro_targets(graph, sub_key)
        if mro_targets is not None:
            for full_key in mro_targets:
                _emit_init_subclass_edge(
                    graph, sub_cls, sub_key, full_key, existing_pairs)
            continue
        for base_name in _name_seq(base_names):
            for full_key in _resolve_init_subclass_targets(
                    graph, sub_key, base_name, init_subclass_by_simple):
                _emit_init_subclass_edge(
                    graph, sub_cls, sub_key, full_key, existing_pairs)
def _build_init_subclass_simple_index(graph) -> dict:
    init_subclass_by_simple: dict[str, list[str]] = defaultdict(list)
    for fq in graph.functions:
        if normalize_torn_name(fq).endswith(".__init_subclass__"):
            cls_key = fq[: -len(".__init_subclass__")]
            init_subclass_by_simple[_ref_basename(cls_key)].append(fq)
    return init_subclass_by_simple
def _emit_init_subclass_edge(graph, sub_cls, sub_key: str, full_key: str,
                             existing_pairs: set) -> None:
    fnode = graph.functions[full_key]
    init_fnode = graph.functions.get(_method_key(sub_key, "__init__"))
    if init_fnode and init_fnode.filepath:
        caller_file = init_fnode.filepath
    else:
        caller_file = (graph.class_files.get(sub_cls)
                       or fnode.filepath)
    _emit_synthetic_edge(graph, sub_key, full_key,
                         caller_file=caller_file,
                         existing_pairs=existing_pairs)
def _resolve_init_subclass_targets(graph, sub_key: str, base_name: str,
                                   by_simple: dict[str, list[str]]) -> list[str]:
    init_subclass_key = f"{base_name}.__init_subclass__"
    if init_subclass_key in graph.functions:
        return [init_subclass_key]
    split = _split_ref(sub_key)
    if split is not None:
        candidate = f"{split[0]}.{base_name}.__init_subclass__"
        if candidate in graph.functions:
            return [candidate]
    inherited = _inherited_init_subclass_target(graph, sub_key, base_name)
    if inherited is not None:
        return [inherited]
    hits = (by_simple.get(_ref_basename(base_name), [])
            if "." not in normalize_torn_name(base_name) else [])
    return hits if len(hits) == 1 else []
def _init_subclass_class_key(graph, owner_key: str, class_name: str) -> str:
    normalized = normalize_torn_name(class_name)
    if "." in normalized:
        return normalized
    split = _split_ref(owner_key)
    candidate = f"{split[0]}.{normalized}" if split else normalized
    if (candidate in graph.class_inheritance
            or f"{candidate}.__init_subclass__" in graph.functions):
        return candidate
    hits = [
        key for key in graph.class_inheritance
        if _ref_basename(key) == normalized
    ]
    return hits[0] if len(hits) == 1 else candidate
def _inherited_init_subclass_target(graph, sub_key: str,
                                    base_name: str) -> str | None:
    start = _init_subclass_class_key(graph, sub_key, base_name)
    queue = deque([start])
    visited: set[str] = set()
    while queue:
        cls_key = queue.popleft()
        if cls_key in visited:
            continue
        visited.add(cls_key)
        method_key = _method_key(cls_key, "__init_subclass__")
        if method_key in graph.functions:
            return method_key
        for parent in _name_seq(graph.class_inheritance.get(cls_key)):
            queue.append(_init_subclass_class_key(graph, cls_key, parent))
    return None
def _init_subclass_mro_targets(graph, sub_key: str) -> list[str] | None:
    mro = _static_class_mro(graph, sub_key, {}, set())
    if mro is None:
        return None
    for cls_key in mro[1:]:
        method_key = _method_key(cls_key, "__init_subclass__")
        if method_key in graph.functions:
            return [method_key]
    return []

def _static_class_mro(graph, cls_key: str, memo: dict, active: set) -> list[str] | None:
    cls_key = normalize_torn_name(cls_key)
    if cls_key in memo:
        return memo[cls_key]
    if cls_key in active:
        return None
    active.add(cls_key)
    try:
        parents = [
            _init_subclass_class_key(graph, cls_key, parent)
            for parent in _name_seq(graph.class_inheritance.get(cls_key))
        ]
        parent_mros = []
        for parent in parents:
            parent_mro = _static_class_mro(graph, parent, memo, active)
            if parent_mro is None:
                return None
            parent_mros.append(parent_mro)
        merged = _merge_static_mro(parent_mros + [parents])
        if merged is None:
            return None
        mro = [cls_key] + merged
        memo[cls_key] = mro
        return mro
    finally:
        active.remove(cls_key)

def _merge_static_mro(sequences: list[list[str]]) -> list[str] | None:
    sequences = [list(seq) for seq in sequences if seq]
    merged: list[str] = []
    while sequences:
        candidate = next(
            (seq[0] for seq in sequences
             if not any(seq[0] in other[1:] for other in sequences)),
            None,
        )
        if candidate is None:
            return None
        merged.append(candidate)
        sequences = [
            seq[1:] if seq[0] == candidate else seq
            for seq in sequences
        ]
        sequences = [seq for seq in sequences if seq]
    return merged

def link_singledispatch(graph: CallGraph) -> None:
    existing_pairs = _existing_call_pairs(graph)
    _pkg_root = pkg_root_name(graph.project_root)
    for raw_base_key, registered_keys in graph.singledispatch_register.items():
        base_key, base_fnode = _resolve_singledispatch_base(
            graph, raw_base_key, _pkg_root)
        if not base_fnode:
            continue
        for reg_key in _name_seq(registered_keys):
            if reg_key not in graph.functions:
                continue
            _emit_synthetic_edge(
                graph, base_key, reg_key,
                caller_file=base_fnode.filepath,
                line=base_fnode.start_line,
                existing_pairs=existing_pairs)
def _resolve_singledispatch_base(graph, base_key, pkg_root: str):
    base_key = normalize_torn_name(base_key)
    base_fnode = graph.functions.get(base_key)
    if base_fnode is not None and base_key in graph.singledispatch_funcs:
        return base_key, base_fnode
    if pkg_root and base_key.startswith(pkg_root + "."):
        _stripped = base_key[len(pkg_root) + 1:]
        _stripped_fnode = graph.functions.get(_stripped)
        if (_stripped_fnode is not None
                and _stripped in graph.singledispatch_funcs):
            return _stripped, _stripped_fnode
    return base_key, None
def link_implicit_calls(builder: CallGraphBuilderProtocol) -> None:
    graph = builder.graph
    logger.debug("链接隐式调用: %d 个节点", len(graph.functions))
    class_methods = _build_class_method_index(graph)
    all_callers = _build_all_callers(graph)
    existing_pairs = _existing_call_pairs(graph)
    method_to_classes = method_to_classes_index(class_methods)
    _link_visitor_pattern(graph, class_methods, existing_pairs,
                          builder._import_aliases)
    _link_test_entry_points(graph, all_callers, existing_pairs)
    _resolve_instance_methods(graph, class_methods, existing_pairs,
                              method_to_classes, builder._import_aliases)
    caller_callee_index = _link_decorator_semantics(
        graph, existing_pairs, builder._import_aliases)
    _analyze_cross_function_dataflow(
        graph, class_methods, method_to_classes, existing_pairs,
        caller_callee_index, builder._import_aliases)
def _iter_class_methods(graph) -> Iterator[tuple[str, str, str]]:
    for fqname, fnode in graph.functions.items():
        if not fnode.class_name:
            continue
        yield (fqname, normalize_torn_name(fnode.class_name),
               _ref_basename(fnode.name))
def _build_class_method_index(graph) -> dict[str, list[str]]:
    class_methods: dict[str, list[str]] = defaultdict(list)
    for fqname, _cls_name, pure_name in _iter_class_methods(graph):
        class_methods[_ref_module(fqname)].append(pure_name)
    return class_methods
def _build_all_callers(graph) -> dict[str, set[str]]:
    all_callers: dict[str, set[str]] = defaultdict(set)
    for edge in graph.calls:
        all_callers[edge.callee_func].add(edge.caller_func)
    for func, callers in graph.callers.items():
        all_callers[func].update(callers)
    return all_callers
def _resolve_base_fqn(graph, sub_cls: str, base_name: str, visitor_classes: set,
                      _simple_index: dict[str, list[str]]):
    if base_name in graph.class_inheritance or base_name in visitor_classes:
        return base_name
    same_module = _same_module_base(sub_cls, base_name, visitor_classes)
    if same_module is not None:
        return same_module
    hits = _simple_name_hits(graph, base_name, _simple_index)
    return hits[0] if len(hits) == 1 else None
def _same_module_base(sub_cls: str, base_name: str, visitor_classes: set):
    split = _split_ref(sub_cls)
    if split is None:
        return None
    candidate = f"{split[0]}.{base_name}"
    return candidate if candidate in visitor_classes else None
def _simple_name_hits(graph, base_name: str,
                      _simple_index: dict[str, list[str]] | None) -> list[str]:
    normalized = _ref_basename(base_name)
    if _simple_index is not None:
        return _simple_index.get(normalized, [])
    suffix = "." + normalized
    return [_k for _k in graph.class_inheritance
            if normalize_torn_name(_k).endswith(suffix)]
def _link_visitor_pattern(graph, class_methods: dict[str, list[str]],
                          existing_pairs: set, import_aliases):
    visitor_classes = _propagate_visitor_subclasses(
        graph, _direct_visitor_hits(graph, import_aliases))
    for vc_fqn in sorted(visitor_classes):
        _link_visitor_class(graph, class_methods, vc_fqn, existing_pairs)
def _link_visitor_class(graph, class_methods, vc_fqn: str,
                        existing_pairs: set) -> None:
    methods = class_methods.get(vc_fqn, [])
    visit_methods = [m for m in methods if m.startswith("visit_")]
    if not visit_methods:
        return
    caller_key = _select_visitor_caller(graph, vc_fqn, methods)
    if caller_key is None:
        return
    for method_name in visit_methods:
        key = _method_key(vc_fqn, method_name)
        if key not in graph.functions:
            continue
        _emit_synthetic_edge(
            graph, caller_key, key,
            caller_file=_caller_file_of(
                graph, caller_key, graph.functions[key].filepath),
            existing_pairs=existing_pairs)
_VISITOR_BASES = {"NodeVisitor", "ast.NodeVisitor", "NodeTransformer", "ast.NodeTransformer"}
def _class_import_aliases(graph, cls_fqn: str, import_aliases) -> dict:
    if not import_aliases:
        return {}
    filepath = graph.class_files.get(cls_fqn, "")
    return import_aliases.get(filepath) or {}
def _qualified_base_name(base: str, aliases: dict) -> str:
    base = normalize_torn_name(base)
    if not aliases:
        return base
    head, _, tail = base.partition(".")
    resolved_head = aliases.get(head)
    if not resolved_head:
        return base
    return f"{resolved_head}.{tail}" if tail else resolved_head
def _is_visitor_base(base: str, aliases: dict) -> bool:
    if base in _VISITOR_BASES:
        return True
    return _qualified_base_name(base, aliases) in _VISITOR_BASES
def _direct_visitor_hits(graph, import_aliases) -> set:
    hits = set()
    for sub_cls, base_names in graph.class_inheritance.items():
        aliases = _class_import_aliases(graph, sub_cls, import_aliases)
        for base in _name_seq(base_names):
            if _is_visitor_base(base, aliases):
                hits.add(sub_cls)
                break
    return hits
def _build_visitor_simple_index(graph) -> dict[str, list[str]]:
    simple_index: dict[str, list[str]] = defaultdict(list)
    for cls_key in graph.class_inheritance:
        simple_index[_ref_basename(cls_key)].append(cls_key)
    return simple_index
def _propagate_visitor_subclasses(graph, visitor_classes: set) -> set:
    simple_key_index = _build_visitor_simple_index(graph)
    changed = True
    while changed:
        changed = False
        for sub_cls, base_names in graph.class_inheritance.items():
            if sub_cls in visitor_classes:
                continue
            if _visitor_base_reachable(graph, sub_cls, base_names,
                                       visitor_classes, simple_key_index):
                visitor_classes.add(sub_cls)
                changed = True
    return visitor_classes
def _visitor_base_reachable(graph, sub_cls, base_names,
                            visitor_classes, simple_key_index) -> bool:
    for base_name in _name_seq(base_names):
        resolved = _resolve_base_fqn(
            graph, sub_cls, base_name, visitor_classes, simple_key_index)
        if resolved in visitor_classes:
            return True
    return False
def _select_visitor_caller(graph, vc_fqn: str, methods: list[str]):
    init_key = _method_key(vc_fqn, "__init__")
    if init_key in graph.functions:
        return init_key
    for m in methods:
        if m.startswith("visit_"):
            continue
        candidate = _method_key(vc_fqn, m)
        if candidate in graph.functions:
            return candidate
    return f"<visitor:{vc_fqn}>"
def _link_test_entry_points(graph, all_callers: dict[str, set[str]],
                            existing_pairs: set) -> None:
    for fqname, fnode in graph.functions.items():
        if not is_test_file_path(fnode.filepath):
            continue
        if not is_test_caller_name(fqname, graph.functions):
            continue
        if all_callers.get(fqname):
            continue
        _emit_synthetic_edge(
            graph, "<test_runner>", fqname,
            caller_file=fnode.filepath,
            existing_pairs=existing_pairs, all_callers=all_callers)
def _resolve_edge_target_class(candidate_classes: list[str], caller_func: str,
                               caller_instantiates: dict[str, set[str]]) -> str | None:
    if len(candidate_classes) == 1:
        return candidate_classes[0]
    inst_classes = caller_instantiates.get(caller_func, set())
    matching = [c for c in candidate_classes if c in inst_classes]
    if len(matching) == 1:
        return matching[0]
    return None
def _defined_method_target(graph, class_fqn: str, method_name: str) -> str | None:
    target_fqname = _method_key(class_fqn, method_name)
    return target_fqname if target_fqname in graph.functions else None
def _method_candidates(callee: str, method_to_classes) -> tuple[str, list[str]]:
    method_name = _ref_basename(callee)
    return method_name, method_to_classes.get(method_name, [])
def _emit_resolved_channel(graph, existing_pairs: set, resolver) -> None:
    for edge in list(graph.calls):
        target_fqname = resolver(edge)
        if target_fqname is None:
            continue
        _emit_synthetic_edge(
            graph, edge.caller_func, target_fqname,
            caller_file=edge.caller_file, line=edge.line,
            args_count=edge.args_count, existing_pairs=existing_pairs)
def _is_import_qualified(callee: str, caller_file,
                         import_aliases) -> bool:
    if not import_aliases:
        return False
    aliases = import_aliases.get(caller_file)
    if not aliases:
        return False
    head = callee.split(".", 1)[0]
    return head in aliases
def _resolve_instance_methods(graph, class_methods: dict[str, list[str]],
                              existing_pairs: set,
                              method_to_classes: dict[str, list[str]],
                              import_aliases):
    ref_name_to_classes = {cls_fqn: {cls_fqn} for cls_fqn in class_methods}
    caller_instantiates = _build_caller_instantiates(
        graph, ref_name_to_classes, import_aliases)
    _emit_resolved_channel(
        graph, existing_pairs,
        lambda edge: _instance_method_target(
            graph, edge, method_to_classes, caller_instantiates,
            import_aliases))
def _dotted_callee_is_inference_eligible(graph, edge,
                                         import_aliases) -> bool:
    if edge.type_resolution_blocked:
        return False
    callee = normalize_torn_name(edge.callee_func)
    if (callee in graph.functions or "." not in callee
            or callee.startswith(".")):
        return False
    return not _is_import_qualified(callee, edge.caller_file, import_aliases)
def _reject_name_coincidence(target: str | None, edge) -> str | None:
    if target is not None and target == normalize_torn_name(edge.caller_func):
        return None
    return target
def _instance_method_target(graph, edge, method_to_classes,
                            caller_instantiates, import_aliases) -> str | None:
    if not _dotted_callee_is_inference_eligible(graph, edge, import_aliases):
        return None
    callee = normalize_torn_name(edge.callee_func)
    method_name, candidate_classes = _method_candidates(
        callee, method_to_classes)
    if not candidate_classes:
        return None
    target_cls = _resolve_edge_target_class(
        candidate_classes, edge.caller_func, caller_instantiates)
    if target_cls is None:
        return None
    return _reject_name_coincidence(
        _defined_method_target(graph, target_cls, method_name), edge)
def _caller_module_name(graph, caller_file: str) -> str:
    path = caller_file if isinstance(caller_file, str) else ""
    root = getattr(graph, "project_root", "") or ""
    if root and os.path.isabs(path):
        try:
            path = os.path.relpath(path, root)
        except ValueError:  # jwsgj:silent-ok 跨盘路径无法相对化时返回空映射
            return ""
        if path == os.pardir or path.startswith(os.pardir + os.sep):
            return ""
    return path_to_dotted_module(path.replace("\\", "/"))
def _instantiates_classes(callee: str, caller_file: str, graph,
                          ref_name_to_classes: dict[str, set[str]],
                          import_aliases) -> set[str]:
    direct = ref_name_to_classes.get(callee)
    if direct:
        return direct
    aliases = (import_aliases or {}).get(caller_file) or {}
    resolved = _qualified_base_name(callee, aliases)
    if resolved != callee:
        return ref_name_to_classes.get(resolved, set())
    if "." in callee:
        return set()
    module_name = _caller_module_name(graph, caller_file)
    if not module_name:
        return set()
    return ref_name_to_classes.get(f"{module_name}.{callee}", set())
def _build_caller_instantiates(
    graph, ref_name_to_classes: dict[str, set[str]],
    import_aliases) -> dict[str, set[str]]:
    caller_instantiates: dict[str, set[str]] = defaultdict(set)
    for edge in graph.calls:
        if edge.caller_func not in graph.functions:
            continue
        callee = normalize_torn_name(edge.callee_func)
        caller_instantiates[edge.caller_func] |= _instantiates_classes(
            callee, edge.caller_file, graph, ref_name_to_classes,
            import_aliases)
        if callee.endswith(".__init__"):
            cls_part = callee[:-len(".__init__")]
            caller_instantiates[edge.caller_func] |= _instantiates_classes(
                cls_part, edge.caller_file, graph, ref_name_to_classes,
                import_aliases)
    return caller_instantiates
def _resolve_wraps_candidate(graph, fqname: str, wrapped_name: str,
                             module_name: str,
                             before_line: int | None = None) -> str | None:
    fqname = normalize_torn_name(fqname)
    owner_prefix = _ref_module(fqname) if "." in fqname else ""
    candidates = []
    owner_candidate = (
        f"{owner_prefix}.{wrapped_name}"
        if owner_prefix and owner_prefix != module_name else ""
    )
    if owner_candidate:
        candidates.append(owner_candidate)
    if module_name:
        candidates.append(f"{module_name}.{wrapped_name}")
    candidates.append(wrapped_name)
    for cand in candidates:
        if cand not in graph.functions or cand == fqname:
            continue
        if cand == owner_candidate and before_line is not None:
            candidate_node = graph.functions[cand]
            if candidate_node.start_line > before_line:
                continue
        return cand
    return None
def _link_wraps_semantics(graph, existing_pairs: set,
                          import_aliases) -> None:
    for fqname, fnode in graph.functions.items():
        aliases = (import_aliases or {}).get(fnode.filepath) or {}
        for wrapped_name in _iter_wraps_targets(fnode):
            resolved_name = _qualified_base_name(wrapped_name, aliases)
            _link_wrapped_target(graph, fqname, fnode, resolved_name,
                                 existing_pairs)
def _iter_wraps_targets(fnode):
    decorator_args = fnode.decorator_args
    if not isinstance(decorator_args, Mapping):
        return
    for dec_name, dec_args in decorator_args.items():
        if _ref_basename(dec_name) != "wraps":
            continue
        yield from _name_seq(dec_args)
def _link_wrapped_target(graph, fqname: str, fnode, wrapped_name,
                         existing_pairs) -> None:
    cand = _resolve_wraps_candidate(
        graph, fqname, wrapped_name,
        _caller_module_name(graph, fnode.filepath),
        before_line=fnode.start_line)
    if cand is None:
        return
    _emit_synthetic_edge(
        graph, fqname, cand,
        caller_file=fnode.filepath, line=fnode.start_line,
        existing_pairs=existing_pairs)
def _link_decorator_semantics(
    graph, existing_pairs: set, import_aliases) -> dict[str, list[str]]:
    logger.debug("分析装饰器语义")
    _link_wraps_semantics(graph, existing_pairs, import_aliases)
    caller_callee_index: dict[str, list[str]] = defaultdict(list)
    for _e in graph.calls:
        caller_callee_index[_e.caller_func].append(_e.callee_func)
    return caller_callee_index
_FACTORY_NAME_PREFIXES = ("create_", "build_", "make_", "new_", "get_")
def _build_factory_return_types(
    graph, class_methods: dict[str, list[str]]) -> dict[str, str]:
    return_type_cache: dict[str, str] = {}
    class_modules = {
        cls_fqn: _caller_module_name(graph, filepath)
        for cls_fqn, filepath in graph.class_files.items()
        if isinstance(filepath, str) and filepath
    }
    for fqname, fnode in graph.functions.items():
        simple = _ref_basename(fqname)
        if simple.startswith(_FACTORY_NAME_PREFIXES):
            module_name = _caller_module_name(graph, fnode.filepath)
            inferred = _infer_factory_return_class(
                simple, class_methods, module_name, class_modules)
            if inferred is not None:
                return_type_cache[fqname] = inferred
    return return_type_cache
def _analyze_cross_function_dataflow(graph, class_methods: dict[str, list[str]],
                                     method_to_classes: dict[str, list[str]],
                                     existing_pairs: set,
                                     caller_callee_index: dict[str, list[str]],
                                     import_aliases):
    logger.debug("分析跨函数数据流: %d 个类", len(class_methods))
    _return_type_cache = _build_factory_return_types(graph, class_methods)
    _emit_resolved_channel(
        graph, existing_pairs,
        lambda edge: _dataflow_target_fqname(
            graph, edge, method_to_classes, _return_type_cache,
            caller_callee_index, import_aliases))
def _dataflow_target_fqname(graph, edge, method_to_classes, return_type_cache,
                            caller_callee_index, import_aliases) -> str | None:
    if not _dotted_callee_is_inference_eligible(graph, edge, import_aliases):
        return None
    callee = normalize_torn_name(edge.callee_func)
    method_name, candidate_classes = _method_candidates(
        callee, method_to_classes)
    if len(candidate_classes) <= 1:
        return None
    target_cls = _dataflow_target_class(
        graph, edge, callee, candidate_classes,
        return_type_cache, caller_callee_index)
    if target_cls is None:
        return None
    return _reject_name_coincidence(
        _defined_method_target(graph, target_cls, method_name), edge)
def _dataflow_target_class(graph, edge, callee, candidate_classes,
                           return_type_cache, caller_callee_index) -> str | None:
    if not graph.functions.get(edge.caller_func):
        return None
    return _resolve_dataflow_target(
        caller_callee_index.get(edge.caller_func, []),
        return_type_cache, callee, candidate_classes)
def _infer_factory_return_class(
    simple: str, class_methods: dict[str, list[str]],
    module_name: str, class_modules: Mapping[str, str],
) -> str | None:
    suffix = simple.split("_", 1)[1]
    suffix_flat = suffix.replace("_", "").lower()
    candidates = []
    for cls_fqn in class_methods:
        cls_simple = _ref_basename(cls_fqn)
        cls_low = cls_simple.lower()
        if any((cls_low == suffix.lower(), cls_low == suffix_flat)):
            candidates.append(cls_fqn)
    same_module = []
    for cls_fqn in candidates:
        cls_module = class_modules.get(cls_fqn)
        if cls_module is None:
            cls_module = _ref_module(cls_fqn) if "." in cls_fqn else ""
        if cls_module == module_name:
            same_module.append(cls_fqn)
    if len(same_module) == 1:
        return same_module[0]
    if same_module:
        return None
    return candidates[0] if len(candidates) == 1 else None
def _resolve_dataflow_target(caller_callees, _return_type_cache: dict[str, str],
                             callee: str, candidate_classes: list[str]) -> str | None:
    matches = {
        ret_type
        for prev_callee in caller_callees
        if prev_callee != callee
        for ret_type in (_return_type_cache.get(prev_callee),)
        if ret_type and ret_type in candidate_classes
    }
    return next(iter(matches)) if len(matches) == 1 else None
def _resolve_hop_targets(graph, base_key: str, base_written) -> tuple[list[str], bool]:
    simple = _ref_basename(base_written)
    if base_key in graph.class_inheritance or base_key in graph.class_files:
        return [base_key], False
    if "." in normalize_torn_name(base_written):
        return [], True
    # 原实现每次调都先构造两个 set 的并集、再全量遍历并逐键做
    # ``normalize_torn_name``——在 1404 个类 × 数万次 mixin 解析下退化为 O(n²)。
    # 尾段索引与 ``_ref_basename(cand) == simple`` 口径完全一致。
    hop_targets = sorted(
        class_tail_index(graph, "class_inheritance", "class_files").get(
            simple, ()))
    if len(hop_targets) != 1:
        return [], True
    return hop_targets, False
def _enqueue_hop_targets(queue, visited: set, hop_targets: list[str],
                         mixin_cls_key: str, mixin_simple: str,
                         allow_simple: bool) -> bool:
    for target in hop_targets:
        if _is_mixin_hit(target, mixin_cls_key, mixin_simple, allow_simple):
            return True
        if target in visited:
            continue
        visited.add(target)
        queue.append(target)
    return False
def _mixin_inheritance_confirmed(graph, sub_cls_key: str, mixin_cls_key: str):
    if not graph.class_inheritance:
        return None
    sub_cls_key = normalize_torn_name(sub_cls_key)
    mixin_cls_key = normalize_torn_name(mixin_cls_key)
    if sub_cls_key == mixin_cls_key:
        return True
    if sub_cls_key not in graph.class_inheritance:
        return False
    reached, broken = _bfs_mixin_reachability(graph, sub_cls_key, mixin_cls_key)
    if reached:
        return True
    return None if broken else False
def _bfs_mixin_reachability(graph, sub_cls_key: str, mixin_cls_key: str):
    mixin_simple = _ref_basename(mixin_cls_key)
    visited = {sub_cls_key}
    queue = deque([sub_cls_key])
    broken = False
    while queue:
        cls_key = normalize_torn_name(queue.popleft())
        reached, hop_broken = _expand_mixin_bases(
            graph, queue, visited, cls_key, mixin_cls_key, mixin_simple)
        broken = broken or hop_broken
        if reached:
            return True, broken
    return False, broken
def _expand_mixin_bases(graph, queue, visited: set, cls_key: str,
                        mixin_cls_key: str, mixin_simple: str):
    broken = False
    for base_written in _name_seq(graph.class_inheritance.get(cls_key)):
        allow_simple = "." not in normalize_torn_name(base_written)
        base_key = _resolve_base_edge_key(cls_key, base_written)
        allow_simple = allow_simple and not (
            base_key in graph.class_inheritance or base_key in graph.class_files)
        hop_targets, hop_broken = _resolve_hop_targets(graph, base_key, base_written)
        broken = broken or hop_broken
        if base_key == mixin_cls_key:
            return True, broken
        if _enqueue_hop_targets(queue, visited, hop_targets,
                                mixin_cls_key, mixin_simple, allow_simple):
            return True, broken
    return False, broken
def _resolve_base_edge_key(cls_key: str, base_written) -> str:
    base_written_norm = normalize_torn_name(base_written)
    if "." in base_written_norm:
        return base_written_norm
    if "." not in cls_key:
        return base_written_norm
    return f"{_ref_module(cls_key)}.{base_written_norm}"
def _is_mixin_hit(candidate_key: str, mixin_cls_key: str,
                  mixin_simple: str, allow_simple: bool) -> bool:
    return (candidate_key == mixin_cls_key
            or (allow_simple
                and _ref_basename(candidate_key) == mixin_simple))
def _collect_mixin_classes(graph) -> dict[str, set[str]]:
    mixin_classes: dict[str, set[str]] = {}
    for _fqname, cls_name, method_name in _iter_class_methods(graph):
        if "Mixin" in cls_name or cls_name.startswith("_"):
            mixin_classes.setdefault(cls_name, set()).add(method_name)
    return mixin_classes
def _build_cls_method_fqn_index(graph) -> dict[tuple[str, str], list[str]]:
    index = defaultdict(list)
    for fqn, cls_name, method_name in _iter_class_methods(graph):
        index[(cls_name, method_name)].append(fqn)
    return index
def _has_direct_super_call(node: ast.AST, method_name: str) -> bool:
    stack = list(getattr(node, "body", ()))
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda, ast.ClassDef, ast.GeneratorExp)):
            continue
        if isinstance(current, ast.Call) and isinstance(
                current.func, ast.Attribute) and current.func.attr == method_name:
            receiver = current.func.value
            if (isinstance(receiver, ast.Call)
                    and isinstance(receiver.func, ast.Name)
                    and receiver.func.id == "super"):
                return True
        stack.extend(ast.iter_child_nodes(current))
    return False


def _graph_source_path(graph: CallGraph, filepath: str) -> str:
    # ``FunctionNode.filepath`` 由 builder 写入的是**项目根相对路径**；
    # 直接交给 ``read_cached`` 会按进程 cwd 解析，cwd ≠ 项目根时整段源码
    # 证据静默丢失（mixin super() 通道零边）。这里按 ``project_root`` 还原。
    if not filepath or os.path.isabs(filepath):
        return filepath
    root = getattr(graph, "project_root", "") or ""
    return os.path.join(root, filepath) if root else filepath


def _source_super_callers(graph: CallGraph, candidates: set[str]) -> set[str]:
    by_file: dict[str, list[str]] = defaultdict(list)
    for fqn in candidates:
        filepath = _graph_source_path(
            graph, graph.functions[fqn].filepath)
        if filepath:
            by_file[filepath].append(fqn)
    confirmed: set[str] = set()
    for filepath, fqns in by_file.items():
        source = read_cached(filepath)
        if source is None:
            continue
        try:
            tree = ast.parse(source)
        except (SyntaxError, ValueError, TypeError, RecursionError) as exc:
            log_swallowed(__name__, exc, context="mixin_super_evidence")
            continue
        definitions = {
            (node.name, node.lineno, node.end_lineno): node
            for node in ast.walk(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        }
        for fqn in fqns:
            fnode = graph.functions[fqn]
            method_name = _ref_basename(fnode.name)
            node = definitions.get(
                (method_name, fnode.start_line, fnode.end_line))
            if node is not None and _has_direct_super_call(node, method_name):
                confirmed.add(fqn)
    return confirmed


def link_mixin_methods(graph: CallGraph) -> None:
    mixin_classes = _collect_mixin_classes(graph)
    if not mixin_classes:
        return
    _cls_method_fqn = _build_cls_method_fqn_index(graph)
    existing_pairs = _existing_call_pairs(graph)
    mixin_method_names = set().union(*mixin_classes.values())
    candidates = {
        fqn for fqn, fnode in graph.functions.items()
        if fnode.class_name and _ref_basename(fnode.name) in mixin_method_names
    }
    super_callers = _source_super_callers(graph, candidates)
    for fqn, fnode in graph.functions.items():
        if fqn not in super_callers:
            continue
        _link_mixin_consumers(graph, fqn, fnode, mixin_classes,
                              _cls_method_fqn, existing_pairs)
def _link_mixin_consumers(graph, fqn: str, fnode, mixin_classes,
                          cls_method_fqn, existing_pairs: set) -> None:
    if not fnode.class_name:
        return
    method_name = _ref_basename(fnode.name)
    for mixin_cls, mixin_methods in mixin_classes.items():
        for mixin_fqn in _confirmed_mixin_fqns(
                graph, fqn, method_name, mixin_cls, mixin_methods,
                cls_method_fqn):
            _emit_synthetic_edge(
                graph, fqn, mixin_fqn,
                caller_file=fnode.filepath or "",
                line=fnode.start_line,
                existing_pairs=existing_pairs)
def _confirmed_mixin_fqns(graph, fqn: str, method_name: str, mixin_cls: str,
                          mixin_methods: set, cls_method_fqn):
    if method_name not in mixin_methods:
        return
    for mixin_fqn in cls_method_fqn.get((mixin_cls, method_name), ()):
        if mixin_fqn == fqn:
            continue
        confirmed = _mixin_inheritance_confirmed(
            graph,
            _ref_module(fqn),
            _ref_module(mixin_fqn))
        if confirmed is True:
            yield mixin_fqn
_EVENT_BUS_ATTRS = frozenset({
    '_subscriptions', '_listeners', '_handlers', '_callbacks',
    '_events', '_event_map', '_subscribers', '_watchers',
    '_hooks', '_observers', '_signal_handlers',
})
_REGISTRY_ATTRS = frozenset({
    '_checkers', '_registry', '_discovered', '_registered',
    '_entries', '_handlers', '_plugins', '_extensions',
    '_modules', '_providers', '_factories', '_rules',
    '_fixers', '_scanners', '_analyzers', '_detectors',
})
_OVERLAP_ATTRS = _EVENT_BUS_ATTRS & _REGISTRY_ATTRS
_SCALAR_TYPES: tuple[type, ...] = (str, int, float, bool, bytes, bytearray)
def _is_multi_callback_tuple(value: Any) -> bool:
    return (isinstance(value, tuple) and bool(value)
            and all(callable(item) for item in value))
def _stable_obj_key(obj: Any) -> tuple:
    code = getattr(obj, "__code__", None)
    return (
        type(obj).__name__,
        _qualname(obj, ""),
        getattr(code, "co_filename", "") if code is not None else "",
        getattr(code, "co_firstlineno", 0) if code is not None else 0,
        id(obj),
    )
def _stable_items(items: Any) -> list:
    if isinstance(items, (set, frozenset)):
        return sorted(items, key=_stable_obj_key)
    return list(items)
def _iter_nested_callables(items: Any, depth: int = 0):
    if depth >= 4:
        if callable(items):
            yield items
        return
    for item in _stable_items(items):
        if isinstance(item, (list, tuple, set, frozenset)):
            yield from _iter_nested_callables(item, depth + 1)
        elif callable(item):
            yield item
def _as_code(value: Any) -> types.CodeType | None:
    return value if isinstance(value, types.CodeType) else None
def _callable_target(obj: Any) -> Any:
    target = obj.func if isinstance(obj, functools.partial) else obj
    if (isinstance(target, type)
            or _as_code(getattr(target, "__code__", None)) is not None):
        return target
    if not callable(target):
        return target
    call_target = target.__call__
    return (call_target
            if _as_code(getattr(call_target, "__code__", None)) is not None
            else target)
def _qualname(obj: Any, default: str = "?") -> str:
    for attr in ("__qualname__", "__name__"):
        try:
            value = getattr(obj, attr, "")
        except Exception as exc:  # noqa: BLE001 — 降级：不阻断主链
            logger.debug("限定名属性探测失败 %s: %s", attr, exc)
            continue
        if isinstance(value, str) and value:
            return value
    return default
def _binding_key(obj: Any, slot: Any, identity: Any) -> tuple:
    identity_key = ((id(identity.__self__), id(identity.__func__))
                    if isinstance(identity, types.MethodType) else id(identity))
    try:
        hash(slot)
    except Exception:  # noqa: BLE001 — 自定义 slot 的哈希失败不阻断绑定扫描
        slot_key = (type(slot).__name__, repr(slot))
    else:
        slot_key = (type(slot), slot)
    return (type(obj).__name__, id(obj), slot_key, identity_key)
def _claim_unique(seen: set[tuple], key: tuple) -> bool:
    if key in seen:
        return False
    seen.add(key)
    return True
_BINDING_CHANNELS = (
    "event_subscriptions", "registry_entries", "decorator_registrations",
    "dynamic_attributes", "init_subclass_registrations",
)
def _method_qualname_fallback(frame) -> str:
    code = frame.f_code
    for local_name in ("self", "cls"):
        value = frame.f_locals.get(local_name)
        owner = value if isinstance(value, type) else type(value)
        for base in getattr(owner, "__mro__", ()):
            candidate = vars(base).get(code.co_name)
            if isinstance(candidate, (staticmethod, classmethod)):
                candidate = candidate.__func__
            if getattr(candidate, "__code__", None) is code:
                return f"{base.__qualname__}.{code.co_name}"
    return code.co_name
def _frame_qualname(frame) -> str:
    code = frame.f_code
    qualified = getattr(code, "co_qualname", None)
    return qualified or _method_qualname_fallback(frame)
class DynamicCallTracer:
    def __init__(self, project_root: str,
                 engine_files: tuple[str, ...] = ()) -> None:
        self.project_root = _root_abs_path(project_root)
        self._root_norm = (
            (_resolved_path(self.project_root) or _root_boundary(self.project_root))
            if self.project_root else ""
        )
        self._engine_files = {
            os.path.realpath(path) for path in engine_files
            if isinstance(path, str) and path}
        self._engine_files.add(os.path.realpath(__file__))
        self._edges: list[tuple[str, str, str, str, int]] = []
        self._original_profile: Callable | None = None
        self._original_profiles: dict[int, Callable | None] = {}
        self._trace_thread_id: int = 0
        self._active = False
        self._stopped = False
        self._depth = 0
        self._max_depth = 50
        self._start_time: float = 0
        self._stop_time: float = 0
        self._call_counts: dict[tuple[str, str, str, str], int] = {}
        self._tracked_frames: set[int] = set()
        self._depth_lock = threading.Lock()
    def start(self) -> None:
        if self._active:
            return
        self._active = True
        self._stopped = False
        self._edges.clear()
        self._call_counts.clear()
        self._tracked_frames.clear()
        self._original_profiles.clear()
        self._depth = 0
        self._start_time = time.time()
        self._stop_time = 0
        self._trace_thread_id = threading.get_ident()
        self._original_profile = sys.getprofile()
        sys.setprofile(self._trace_callback)
    def stop(self) -> list[tuple[str, str, str, str, int]]:
        if not self.is_active:
            return list(self._edges)
        sys.setprofile(self._original_profile)
        self._stop_time = time.time()
        self._active = False
        self._stopped = True
        with self._depth_lock:
            self._tracked_frames.clear()
        return list(self._edges)
    def install_for_current_thread(self) -> Callable | None:
        previous = sys.getprofile()
        thread_id = threading.get_ident()
        self._original_profiles[thread_id] = previous
        self._trace_thread_id = thread_id
        sys.setprofile(self._trace_callback)
        return previous
    def restore_current_thread(self, previous: Callable | None) -> None:
        sys.setprofile(previous)
        self._original_profiles.pop(threading.get_ident(), None)
    @property
    def is_active(self) -> bool:
        return self._active
    @property
    def edge_count(self) -> int:
        return len(self._edges)
    @property
    def unique_callers(self) -> int:
        return len({e[0] for e in self._edges})
    @property
    def unique_callees(self) -> int:
        return len({e[1] for e in self._edges})
    def summary(self) -> dict:
        return {
            "total_edges": self.edge_count,
            "unique_callers": self.unique_callers,
            "unique_callees": self.unique_callees,
            "duration_ms": (round(((self._stop_time or time.time()) - self._start_time) * 1000, 1)
                            if self._start_time else 0.0),
            "max_depth": self._max_depth,
        }
    def _forward_to_original_profile(self, frame, event, arg) -> None:
        original = self._original_profiles.get(
            threading.get_ident(), self._original_profile)
        if original is None:
            return
        try:
            original(frame, event, arg)
        except Exception as exc:  # noqa: BLE001 — 降级：转发失败不阻断主链
            logger.debug("转发事件给在位 profiler 失败: %s", exc)
    def _trace_callback(self, frame, event, arg):
        if threading.get_ident() != self._trace_thread_id:
            return None
        if self._stopped:
            return None
        if event == 'return':
            self._handle_return_event(frame, event, arg)
            return self._trace_callback
        if event != 'call':
            self._forward_to_original_profile(frame, event, arg)
            return self._trace_callback
        if not self._enter_traced_depth(frame, event, arg):
            return None
        try:
            keep_self = self._collect_call_edge(frame, event, arg)
        except (KeyError, TypeError, AttributeError, ValueError) as exc:
            logger.debug("trace callback 异常: %s", exc)
            return self._trace_callback
        return self._trace_callback if keep_self else None
    def _revert_traced_depth(self, frame) -> None:
        self._tracked_frames.discard(id(frame))
        self._depth = max(0, self._depth - 1)
    def _handle_return_event(self, frame, event, arg) -> None:
        with self._depth_lock:
            if id(frame) in self._tracked_frames:
                self._revert_traced_depth(frame)
        self._forward_to_original_profile(frame, event, arg)
    def _enter_traced_depth(self, frame, event, arg) -> bool:
        with self._depth_lock:
            if self._depth < self._max_depth:
                self._depth += 1
                self._tracked_frames.add(id(frame))
                return True
        self._forward_to_original_profile(frame, event, arg)
        return False
    def _skip_non_project_frame(self, frame, event, arg) -> None:
        with self._depth_lock:
            self._revert_traced_depth(frame)
        self._forward_to_original_profile(frame, event, arg)
    def _collect_call_edge(self, frame, event, arg) -> bool:
        code = frame.f_code
        filepath = code.co_filename
        callee_name = _frame_qualname(frame)
        if not self._is_project_file(filepath):
            self._skip_non_project_frame(frame, event, arg)
            return False
        self._forward_to_original_profile(frame, event, arg)
        if os.path.realpath(filepath) in self._engine_files:
            return True
        self._record_edge(frame, callee_name, filepath)
        return True
    def _record_edge(self, frame, callee_name: str, filepath: str) -> None:
        caller_frame = frame.f_back
        if not (caller_frame and caller_frame.f_code):
            return
        caller_file = caller_frame.f_code.co_filename
        caller_name = _frame_qualname(caller_frame)
        if not (self._is_project_file(caller_file) or caller_name == '<module>'):
            return
        if not caller_name:
            caller_name = '<module>'
        edge_key = (caller_file, caller_name, callee_name, filepath)
        if edge_key not in self._call_counts:
            self._call_counts[edge_key] = 0
            self._edges.append((
                caller_name,
                callee_name,
                caller_file,
                filepath,
                caller_frame.f_lineno,
            ))
        self._call_counts[edge_key] += 1
    def _is_project_file(self, filepath: str) -> bool:
        if not isinstance(filepath, str) or not filepath or filepath.startswith('<'):
            return False
        return _is_within_root(
            _resolved_project_path(filepath, self.project_root), self._root_norm)
def _root_boundary(project_root: str) -> str:
    return os.path.normcase(os.path.normpath(os.path.abspath(project_root)))
def _root_abs_path(project_root: Any) -> str:
    if not isinstance(project_root, (str, os.PathLike)):
        return ""
    try:
        text = os.fspath(project_root)
    except TypeError as _e:
        log_swallowed(
            __name__, _e,
            context=f"_root_abs_path:{type(_e).__name__}")
        return ""
    if isinstance(text, bytes):
        text = os.fsdecode(text)
    text = text.strip()
    return os.path.abspath(text) if text else ""
@functools.lru_cache(maxsize=4096)
def _resolved_path_cached(norm_input: str) -> str | None:
    """路径身份解析（带边界缓存）。

    ``os.path.realpath`` 在 Windows 上是逐段 syscall，而诊断轮次里同一批
    文件会被各检测器反复请求：实测单轮 17,358 次调用仅对应 146 个不同路径
    （去重率 99.16%，且 Top 参数是 enum.py/re/_parser.py/inspect.py 这类
    第三方模块路径）。路径解析是纯函数，按规范化输入缓存即可消除全部重复
    系统调用，语义与逐次解析等价。
    """
    try:
        return os.path.normcase(os.path.normpath(os.path.realpath(norm_input)))
    except (TypeError, ValueError) as _e:
        log_swallowed(
            __name__, _e,
            context=f"_resolved_path:{type(_e).__name__}")
        return None


def _resolved_path(filepath) -> str | None:
    if isinstance(filepath, bytes):
        return None
    try:
        hash(filepath)
    except TypeError:
        # 不可哈希输入（如自定义 PathLike 实现）退回无缓存路径
        return _resolved_path_cached.__wrapped__(filepath)  # type: ignore[attr-defined]
    return _resolved_path_cached(filepath)
def _resolved_project_path(filepath: Any, project_root: Any) -> str | None:
    if not isinstance(filepath, str) or not filepath or filepath.startswith('<'):
        return None
    path = filepath
    if not os.path.isabs(path):
        root = _root_abs_path(project_root)
        if not root:
            return None
        path = os.path.join(root, path)
    return _resolved_path(path)
def _is_within_root(norm_path: str | None, root_norm: str) -> bool:
    if not norm_path or not root_norm:
        return False
    root_prefix = root_norm if root_norm.endswith(os.sep) else root_norm + os.sep
    return norm_path == root_norm or norm_path.startswith(root_prefix)
def filter_suspicious_files(project_root: str, call_graph: Any = None,
                            blindspot_report: Any = None) -> list[str]:
    root = _root_abs_path(project_root)
    if not root:
        logger.warning(
            "filter_suspicious_files project_root 非法或空白: %r，返回空范围",
            project_root)
        return []
    suspicious_files = _collect_graph_suspicious_files(call_graph)
    suspicious_files |= _collect_blindspot_files(blindspot_report)
    if not suspicious_files:
        return [root]
    resolved = _admit_suspicious_files(root, suspicious_files)
    if not resolved:
        return [root]
    _admit_package_init(root, resolved)
    total_py = _count_project_py_files(root)
    if len(resolved) > total_py * 0.8:
        return [root]
    return sorted(resolved.values(), key=os.path.normcase)
def _entry_file(item, fields) -> str:
    for name in fields:
        value = (item.get(name) if isinstance(item, dict)
                 else getattr(item, name, None))
        if value:
            return value
    return ""
def _entry_files(items, fields) -> set:
    return {fp for fp in (_entry_file(item, fields) for item in items) if fp}
def _collect_graph_suspicious_files(call_graph) -> set:
    if call_graph is None:
        return set()
    suspicious_files = _entry_files(
        getattr(call_graph, 'orphans', None) or [], ('filepath',))
    _bp_list = call_graph.analyses.breakpoints.get_break_points()
    suspicious_files |= _entry_files(_bp_list or [], ('file',))
    return suspicious_files
def _collect_blindspot_files(blindspot_report) -> set:
    if blindspot_report is None:
        return set()
    return _entry_files(getattr(blindspot_report, 'entries', None) or [],
                        ('filepath', 'file'))
def _admit_python_file(project_root: str, fp: Any,
                       root_norm: str | None = None) -> str | None:
    if not isinstance(fp, (str, os.PathLike)):
        return None
    try:
        path_text = os.fsdecode(os.fspath(fp))
    except (TypeError, ValueError, OSError):
        return None
    if not path_text.lower().endswith('.py'):
        return None
    _abs = path_text if os.path.isabs(path_text) else os.path.join(
        project_root, path_text)
    _abs = os.path.normpath(os.path.abspath(_abs))
    if not os.path.isfile(_abs):
        return None
    _resolved = _resolved_path(_abs)
    _root_norm = (root_norm or _resolved_path(project_root)
                  or _root_boundary(project_root))
    if not _is_within_root(_resolved, _root_norm):
        return None
    return _abs
def _admit_suspicious_files(project_root: str, suspicious_files: set) -> dict:
    _root_norm = _resolved_path(project_root) or _root_boundary(project_root)
    resolved: dict[str, str] = {}
    for fp in suspicious_files:
        _admitted = _admit_python_file(project_root, fp, _root_norm)
        if _admitted:
            resolved.setdefault(os.path.normcase(_admitted), _admitted)
    return resolved
def _admit_package_init(project_root: str, resolved: dict[str, str]) -> None:
    init_file = _admit_python_file(
        project_root, os.path.join(project_root, '__init__.py'))
    if init_file:
        resolved.setdefault(os.path.normcase(init_file), init_file)
def _count_project_py_files(project_root: str) -> int:
    total_py = 0
    for root, dirs, files in os.walk(project_root):
        prune_ignore_dirs(dirs, root_dir=project_root)
        for name in files:
            if not name.lower().endswith('.py'):
                continue
            rel_path = os.path.relpath(os.path.join(root, name), project_root)
            if is_test_file_path(rel_path):
                continue
            total_py += 1
    return total_py
class RuntimeBindingReport:
    def __init__(self):
        self.event_subscriptions: list[dict] = []
        self.registry_entries: list[dict] = []
        self.decorator_registrations: list[dict] = []
        self.dynamic_attributes: list[dict] = []
        self.init_subclass_registrations: list[dict] = []
    @property
    def total_bindings(self) -> int:
        return sum(len(getattr(self, name)) for name in _BINDING_CHANNELS)
    def summary(self) -> dict:
        counts = {name: len(getattr(self, name)) for name in _BINDING_CHANNELS}
        counts["total"] = self.total_bindings
        return counts
    def to_dict(self) -> dict:
        payload = {
            name: [dict(entry) for entry in getattr(self, name)]
            for name in _BINDING_CHANNELS
        }
        payload["summary"] = self.summary()
        return payload
class _CallableResolver:
    def __init__(self) -> None:
        self._last_seg_cache: tuple[Any, frozenset[str]] | None = None
    def reset_cache(self) -> None:
        self._last_seg_cache = None
    def resolve(self, obj: Any, call_graph: Any) -> dict:
        if callable(obj):
            return self._resolve_callable(obj, call_graph)
        if isinstance(obj, (tuple, list)):
            return self._resolve_container(obj, call_graph)
        if isinstance(obj, (set, frozenset)):
            return self._inert_result(self.resolve_set_names(obj))
        return self._inert_result(str(obj)[:80])
    @staticmethod
    def _inert_result(name: str) -> dict:
        return {"name": name, "file": "", "line": 0, "in_graph": False}
    def _resolve_callable(self, obj: Any, call_graph: Any) -> dict:
        target = _callable_target(obj)
        name = _qualname(target, "<unknown>")
        code = _as_code(getattr(target, '__code__', None))
        return {
            "name": name,
            "file": code.co_filename if code else '',
            "line": code.co_firstlineno if code else 0,
            "in_graph": self.name_in_graph(name, call_graph),
        }
    def _resolve_container(self, obj: Any, call_graph: Any) -> dict:
        for item in obj:
            if callable(item):
                return self.resolve(item, call_graph)
        return self._inert_result(str(obj)[:80])
    @staticmethod
    def resolve_set_names(obj: Any) -> str:
        names = [_qualname(item) for item in obj if callable(item)]
        return ", ".join(sorted(names)) if names else "<set>"
    def name_in_graph(self, name: str, call_graph: Any) -> bool:
        _funcs = getattr(call_graph, 'functions', None)
        if not isinstance(_funcs, dict) or not isinstance(name, str) or not name:
            return False
        if name in _funcs:
            return True
        cache = self._last_seg_cache
        if cache is None or cache[0] is not call_graph:
            segs = frozenset(
                f.rsplit(".", 1)[-1] for f in _funcs if isinstance(f, str))
            cache = (call_graph, segs)
            self._last_seg_cache = cache
        return name.rsplit(".", 1)[-1] in cache[1]
    def is_project_file(self, filepath: str, project_root: str) -> bool:
        if not isinstance(filepath, str):
            return False
        if not filepath or filepath.startswith('<'):
            return False
        root = _root_abs_path(project_root)
        if not root:
            return False
        norm_root = _resolved_path(root)
        if norm_root is None:
            return False
        return _is_within_root(
            _resolved_project_path(filepath, root), norm_root)
    def is_interesting_object(self, obj: Any) -> bool:
        if isinstance(obj, _SCALAR_TYPES):
            return False
        if isinstance(obj, (list, tuple, set, frozenset, dict)):
            return False
        if isinstance(obj, types.ModuleType):
            return False
        return not (isinstance(obj, type) and obj.__module__ in ('builtins', 'abc'))
    @staticmethod
    def is_callable_or_container(obj: Any) -> bool:
        if callable(obj):
            return True
        if isinstance(obj, (tuple, list, set, frozenset)):
            return any(True for _item in _iter_nested_callables(obj))
        return False
class _EventBusDetector:
    def __init__(self, resolver: _CallableResolver) -> None:
        self._kv = resolver
        self._seen_entries: set[tuple] = set()
    def reset(self) -> None:
        self._seen_entries.clear()
    def _iter_callbacks(self, attr: str, callbacks: Any):
        if isinstance(callbacks, (list, set, frozenset)):
            yield from _iter_nested_callables(callbacks)
        elif isinstance(callbacks, tuple):
            if attr in _OVERLAP_ATTRS:
                if _is_multi_callback_tuple(callbacks):
                    yield from callbacks
            else:
                yield from _iter_nested_callables(callbacks)
        elif attr not in _OVERLAP_ATTRS:
            yield callbacks
    def _iter_bus_callbacks(self, obj: Any):
        for attr in sorted(_EVENT_BUS_ATTRS):
            if not hasattr(obj, attr):
                continue
            subs = getattr(obj, attr)
            if not isinstance(subs, dict):
                continue
            for event_name, callbacks in subs.items():
                for cb in self._iter_callbacks(attr, callbacks):
                    yield event_name, cb
    def _emit_subscription(self, name: str, obj: Any, event_name: Any,
                           cb_info: dict,
                           report: RuntimeBindingReport) -> None:
        report.event_subscriptions.append({
            "bus_instance": name,
            "bus_type": type(obj).__name__,
            "event": str(event_name),
            "callback": cb_info["name"],
            "callback_file": cb_info["file"],
            "callback_line": cb_info["line"],
            "in_call_graph": cb_info["in_graph"],
        })
    def detect(
        self, name: str, obj: Any,
        report: RuntimeBindingReport, call_graph: Any,
    ):
        for event_name, cb in self._iter_bus_callbacks(obj):
            if not self._kv.is_callable_or_container(cb):
                continue
            cb_info = self._kv.resolve(cb, call_graph)
            if cb_info["name"] == "<unknown>":
                continue
            if not _claim_unique(self._seen_entries,
                                 _binding_key(obj, event_name, cb)):
                continue
            self._emit_subscription(
                name, obj, event_name, cb_info, report)
class _RegistryDetector:
    def __init__(self, resolver: _CallableResolver) -> None:
        self._kv = resolver
        self._seen_entries: set[tuple] = set()
        self._lazy_trigger: bool
    def reset(self, lazy_trigger: bool) -> None:
        self._seen_entries.clear()
        self._lazy_trigger = lazy_trigger
    def trigger_lazy(self, obj: Any):
        if not self._lazy_trigger:
            return
        if hasattr(obj, '_ensure_discovered') and callable(obj._ensure_discovered):
            try:
                if not getattr(obj, '_discovered', True):
                    obj._ensure_discovered()
            except Exception as exc:  # noqa: BLE001 — 降级：不阻断主链
                logger.warning("触发懒加载失败: %s", exc)
    def detect(
        self, name: str, obj: Any,
        report: RuntimeBindingReport, call_graph: Any,
    ):
        self.trigger_lazy(obj)
        for attr in sorted(_REGISTRY_ATTRS):
            if not hasattr(obj, attr):
                continue
            entries = getattr(obj, attr)
            if isinstance(entries, dict):
                self._register_dict_entries(
                    name, obj,
                    self._iter_dict_entries(attr, entries),
                    report, call_graph)
            elif isinstance(entries, (tuple, list, set, frozenset)):
                self._register_iterable_entries(
                    name, obj, entries, report, call_graph)
    def _emit_entry(self, name: str, obj: Any, entry_name: Any,
                    h_info: dict,
                    report: RuntimeBindingReport) -> None:
        report.registry_entries.append({
            "registry_instance": name,
            "registry_type": type(obj).__name__,
            "entry_name": str(entry_name),
            "handler": h_info["name"],
            "handler_file": h_info["file"],
            "handler_line": h_info["line"],
            "in_call_graph": h_info["in_graph"],
        })
    def _iter_dict_entries(self, attr: str, entries: dict):
        _overlap = attr in _OVERLAP_ATTRS
        for entry_name, handler in entries.items():
            if not self._kv.is_callable_or_container(handler):
                continue
            if _overlap and (
                    isinstance(handler, (list, set, frozenset))
                    or _is_multi_callback_tuple(handler)):
                continue
            yield entry_name, handler
    def _register_resolved(self, name: str, obj: Any, entry_name: Any,
                           handler: Any, h_info: dict,
                           report: RuntimeBindingReport) -> None:
        if h_info["name"] == "<unknown>":
            return
        if not _claim_unique(self._seen_entries,
                             _binding_key(obj, entry_name, handler)):
            return
        self._emit_entry(name, obj, entry_name, h_info, report)
    @staticmethod
    def _callable_handlers(value: Any):
        if isinstance(value, (list, tuple, set, frozenset)):
            yield from _iter_nested_callables(value)
            return
        if callable(value):
            yield value
    def _register_dict_entries(self, name: str, obj: Any,
                               entries_iter, report: RuntimeBindingReport,
                               call_graph: Any) -> None:
        for entry_name, handler in entries_iter:
            for item in self._callable_handlers(handler):
                self._register_resolved(
                    name, obj, entry_name, item,
                    self._kv.resolve(item, call_graph), report)
    def _register_iterable_entries(self, name: str, obj: Any,
                                   entries: Any, report: RuntimeBindingReport,
                                   call_graph: Any) -> None:
        for item in _stable_items(entries):
            for handler in self._callable_handlers(item):
                h_info = self._kv.resolve(handler, call_graph)
                self._register_resolved(
                    name, obj, h_info["name"], handler, h_info, report)
class _DecoratorDetector:
    def __init__(self, resolver: _CallableResolver) -> None:
        self._kv = resolver
    def detect(
        self, name: str, obj: Any,
        report: RuntimeBindingReport, call_graph: Any,
        project_root: str,
    ):
        self._walk_wrapped_chain(name, obj, report, call_graph, project_root)
        self._register_decorator_list(name, obj, report, call_graph)
    def _append_entry(self, report: RuntimeBindingReport, name: str,
                      wrapped_name: str, code: Any, depth: int,
                      call_graph: Any, decorator: str | None = None) -> None:
        entry = {
            "decorated_name": name,
            "wrapped_func": wrapped_name,
            "wrapped_file": "",
            "wrapped_line": 0,
            "decorator_depth": depth,
            "in_call_graph": self._kv.name_in_graph(wrapped_name, call_graph),
        }
        if code is not None:
            entry["wrapped_file"] = code.co_filename
            entry["wrapped_line"] = code.co_firstlineno
        if decorator is not None:
            entry["decorator"] = decorator
        report.decorator_registrations.append(entry)
    def _walk_wrapped_chain(self, name: str, obj: Any,
                            report: RuntimeBindingReport, call_graph: Any,
                            project_root: str) -> None:
        seen = {id(obj)}
        current = obj
        depth = 0
        while hasattr(current, '__wrapped__') and depth < 10:
            wrapped = current.__wrapped__
            wrapped_id = id(wrapped)
            if wrapped_id in seen:
                break
            seen.add(wrapped_id)
            depth += 1
            code = _as_code(getattr(wrapped, '__code__', None))
            if code is not None and self._kv.is_project_file(
                    code.co_filename, project_root):
                self._append_entry(
                    report, name, _qualname(wrapped), code, depth,
                    call_graph)
            current = wrapped
    def _register_decorator_list(self, name: str, obj: Any,
                                 report: RuntimeBindingReport,
                                 call_graph: Any) -> None:
        dec_list = getattr(obj, '_decorators', None)
        if not isinstance(dec_list, list):
            return
        _dec_code = _as_code(getattr(obj, '__code__', None))
        for dec in _iter_nested_callables(dec_list):
            dec_name = getattr(dec, '__name__', str(dec))
            self._append_entry(
                report, name, name, _dec_code, 0, call_graph,
                decorator=dec_name)
def _class_scope_prefix(obj: Any) -> str:
    if not isinstance(obj, type):
        return ''
    _qual = getattr(obj, '__qualname__', '')
    return f'{_qual}.' if isinstance(_qual, str) and _qual else ''
def _defined_in_class_scope(value: Any, class_prefix: str) -> bool:
    _qual = getattr(value, '__qualname__', '')
    if not (class_prefix and isinstance(_qual, str)
            and _qual.startswith(class_prefix)):
        return False
    relative_qual = _qual[len(class_prefix):]
    return '.<locals>.' not in relative_qual
class _DynamicAttrDetector:
    def __init__(self) -> None:
        self._seen_init: set[tuple] = set()
    def reset(self) -> None:
        self._seen_init.clear()
    def detect_attributes(
        self, name: str, obj: Any, report: RuntimeBindingReport,
    ):
        obj_vars = self._safe_vars(obj)
        if obj_vars is None:
            return
        _class_prefix = _class_scope_prefix(obj)
        for attr_name, attr_value in obj_vars.items():
            if not self.is_dynamic_callable_attr(attr_name, attr_value):
                continue
            call_target = _callable_target(attr_value)
            if (_defined_in_class_scope(attr_value, _class_prefix)
                    or _defined_in_class_scope(call_target, _class_prefix)):
                continue
            code = _as_code(getattr(call_target, '__code__', None))
            if code is None:
                continue
            report.dynamic_attributes.append({
                "owner": name,
                "attr_name": attr_name,
                "func_name": _qualname(call_target, attr_name),
                "func_file": code.co_filename,
                "func_line": getattr(code, 'co_firstlineno', 0),
            })
    @staticmethod
    def _safe_vars(obj: Any) -> Any:
        try:
            if not hasattr(obj, '__dict__'):
                return None
            obj_vars = vars(obj)
        except (TypeError, AttributeError) as e:
            logger.debug("属性获取失败: %s", e)
            return None
        return obj_vars if hasattr(obj_vars, "items") else None
    @staticmethod
    def is_dynamic_callable_attr(attr_name: str, attr_value: Any) -> bool:
        if attr_name.startswith('_'):
            return False
        return callable(attr_value) and not isinstance(attr_value, type)
    def detect_init_subclass(
        self, name: str, cls: type, report: RuntimeBindingReport,
    ):
        if not isinstance(cls, type):
            return
        if not any(base is not object and '__init_subclass__' in vars(base)
                   for base in cls.__mro__):
            return
        try:
            subclasses = cls.__subclasses__()
        except (TypeError, RuntimeError) as exc:
            logger.debug("获取 %s 子类失败: %s", cls.__name__, exc)
            subclasses = []
        for sub in subclasses:
            if not _claim_unique(self._seen_init, (id(cls), id(sub))):
                continue
            sub_module = getattr(sub, '__module__', '?')
            sub_name = _qualname(sub)
            report.init_subclass_registrations.append({
                "base_class": name,
                "subclass": sub_name,
                "subclass_module": sub_module,
                "registration_method": "__init_subclass__",
            })
class RuntimeBindingScanner:
    def __init__(self) -> None:
        self._scanned: set[int] = set()
        self._kv = _CallableResolver()
        self._event = _EventBusDetector(self._kv)
        self._registry = _RegistryDetector(self._kv)
        self._decorator = _DecoratorDetector(self._kv)
        self._dynamic = _DynamicAttrDetector()
    def scan(
        self,
        namespace: dict,
        call_graph: Any,
        project_root: str,
        lazy_trigger: bool = True,
    ) -> RuntimeBindingReport:
        report = RuntimeBindingReport()
        if not isinstance(namespace, Mapping):
            logger.warning(
                "namespace 非映射载荷,跳过扫描: %r", type(namespace).__name__)
            return report
        self._scanned.clear()
        self._event.reset()
        self._registry.reset(lazy_trigger)
        self._dynamic.reset()
        self._kv.reset_cache()
        try:
            namespace_items = list(namespace.items())
        except Exception as exc:  # noqa: BLE001 — 降级：自定义映射枚举失败
            logger.warning("namespace 枚举失败，跳过扫描: %s", exc)
            return report
        all_modules = all(
            isinstance(value, types.ModuleType)
            for _name, value in namespace_items)
        if all_modules:
            self._scan_sys_modules_mode(
                namespace_items, report, call_graph, project_root)
        else:
            self._scan_exec_globals_mode(
                namespace_items, report, call_graph, project_root)
        return report
    def _scan_sys_modules_mode(
        self, namespace_items: list[tuple[Any, Any]],
        report: RuntimeBindingReport, call_graph: Any, project_root: str,
    ):
        for mod_name, mod in namespace_items:
            if not isinstance(mod, types.ModuleType):
                continue
            try:
                self._scan_module_attrs(
                    mod_name, mod, report, call_graph, project_root)
            except Exception as exc:  # noqa: BLE001 — 降级：不阻断主链
                logger.debug("扫描模块 %s 失败: %s", mod_name, exc)
    def _scan_exec_globals_mode(
        self, namespace_items: list[tuple[Any, Any]],
        report: RuntimeBindingReport, call_graph: Any, project_root: str,
    ):
        self._scan_namespace_objects(
            namespace_items, report, call_graph, project_root)
        self._scan_namespace_modules(
            namespace_items, report, call_graph, project_root)
    def _scan_namespace_objects(
        self, namespace_items: list[tuple[Any, Any]],
        report: RuntimeBindingReport, call_graph: Any, project_root: str,
    ) -> None:
        for name, obj in namespace_items:
            if not isinstance(name, str) or is_dunder_name(name):
                continue
            self._run_channel(
                "扫描命名空间对象", name, self._scan_object,
                name, obj, report, call_graph, project_root)
    def _scan_namespace_modules(
        self, namespace_items: list[tuple[Any, Any]],
        report: RuntimeBindingReport, call_graph: Any, project_root: str,
    ) -> None:
        for name, obj in namespace_items:
            if not isinstance(obj, types.ModuleType):
                continue
            self._run_channel(
                "扫描模块", name, self._scan_module_attrs,
                name, obj, report, call_graph, project_root)
    def _scan_module_attrs(
        self,
        mod_name: str,
        mod: types.ModuleType,
        report: RuntimeBindingReport,
        call_graph: Any,
        project_root: str,
    ):
        mod_file = getattr(mod, '__file__', '')
        if not mod_file or not self._kv.is_project_file(mod_file, project_root):
            return
        for attr_name, attr_val in list(vars(mod).items()):
            if is_dunder_name(attr_name):
                continue
            label = f"{mod_name}.{attr_name}"
            self._run_channel(
                "扫描模块属性", label, self._scan_object,
                label, attr_val, report, call_graph, project_root)
    def _scan_object(
        self,
        name: str,
        obj: Any,
        report: RuntimeBindingReport,
        call_graph: Any,
        project_root: str,
    ):
        if obj is None or isinstance(obj, _SCALAR_TYPES):
            return
        obj_id = id(obj)
        if obj_id in self._scanned:
            return
        self._scanned.add(obj_id)
        if not self._is_interesting(name, obj):
            return
        for channel, func, args in self._channel_calls(
                name, obj, report, call_graph, project_root):
            self._run_channel(channel, name, func, *args)
    def _is_interesting(self, name: str, obj: Any) -> bool:
        try:
            return self._kv.is_interesting_object(obj)
        except Exception as exc:  # noqa: BLE001 — 降级：不阻断主链
            logger.debug("对象兴趣判定失败 %s: %s", name, exc)
            return False
    def _channel_calls(
        self, name: str, obj: Any, report: RuntimeBindingReport,
        call_graph: Any, project_root: str,
    ) -> tuple[tuple[str, Any, tuple[Any, ...]], ...]:
        return (
            ("事件总线", self._event.detect,
             (name, obj, report, call_graph)),
            ("注册表", self._registry.detect,
             (name, obj, report, call_graph)),
            ("装饰器", self._decorator.detect,
             (name, obj, report, call_graph, project_root)),
            ("动态属性", self._dynamic.detect_attributes,
             (name, obj, report)),
            ("子类注册", self._dynamic.detect_init_subclass,
             (name, obj, report)),
        )
    def _run_channel(self, channel: str, name: str, func: Any,
                     *args: Any) -> None:
        try:
            func(*args)
        except Exception as exc:  # noqa: BLE001 — 降级：不阻断主链
            logger.debug("%s通道扫描失败 %s: %s", channel, name, exc)

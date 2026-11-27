from __future__ import annotations

import ast
import logging
from dataclasses import dataclass
from functools import cache
from typing import NamedTuple

from jwsgj.diag_callgraph_facts import (
    CallEdge,
    _funcs_revision,
    _qualify_module_member,
    class_method_names,
    functions_by_attr_name,
    functions_ending_with,
    property_maps,
    resolve_callee_file,
)
from jwsgj.diag_shared_ast_nodes import (
    BUILTIN_CALLABLES,
    build_node_dispatch,
    iter_arg_nodes,
    normalize_torn_name,
    path_to_dotted_module,
    pkg_root_name,
    strip_pkg_root,
    torn_list,
)
from jwsgj.log_config import log_swallowed

__all__ = [
    'SELF_CLS_NAMES',
    'CalleeFileContext',
    'CalleeResolver',
    'class_key_by_simple',
    'class_or_bases_define_method',
    'dotted_name_of',
    'extract_type_name',
    'is_cls_bound_factory',
    'is_project_class',
    'is_self_attr_target',
    'lookup_func_return_type',
    'lookup_method_return_type',
    'prescan_module_globals',
    'resolve_base_key',
    'resolve_inherited_method',
    'static_import_module_arg',
    'symbol_owner_lookup',
    'walk_visitors_once',
]
SELF_CLS_NAMES = frozenset({"self", "cls"})
logger = logging.getLogger(__name__)
logger.info("diag_callgraph_resolve 已加载：%d 项导出", len(__all__))
def static_import_module_arg(
        call_node: ast.Call,
        file_aliases: dict[str, str] | None = None,
) -> str | None:
    if not _is_import_module_callee(call_node.func, file_aliases):
        return None
    return _constant_str_arg(call_node)
def _constant_str_arg(call_node: ast.Call) -> str | None:
    arg0 = _import_module_name_arg(call_node)
    if not (isinstance(arg0, ast.Constant) and isinstance(arg0.value, str)):
        return None
    return arg0.value.strip() or None
def _is_import_module_callee(
        func, file_aliases: dict[str, str] | None,
) -> bool:
    if isinstance(func, ast.Attribute):
        if not (isinstance(func.value, ast.Name)
                and func.attr == "import_module"):
            return False
        module_name = func.value.id
        if file_aliases is not None:
            module_name = file_aliases.get(module_name, module_name)
        return module_name == "importlib"
    if isinstance(func, ast.Name):
        if file_aliases is None:
            return func.id == "import_module"
        return file_aliases.get(func.id) == "importlib.import_module"
    return False
def extract_type_name(annotation: ast.AST) -> str | None:
    simple = _simple_annotation_name(annotation)
    if simple is not None:
        return simple
    return _composite_annotation_name(annotation)
def _simple_annotation_name(annotation: ast.AST) -> str | None:
    if isinstance(annotation, ast.Name):
        return annotation.id
    if isinstance(annotation, ast.Attribute):
        return _dotted_annotation_name(annotation)
    if isinstance(annotation, ast.Constant):
        return (_string_annotation_name(annotation.value)
                if isinstance(annotation.value, str) else None)
    return None
def _string_annotation_name(annotation: str) -> str | None:
    text = annotation.strip()
    if not text:
        return None
    try:
        parsed = ast.parse(text, mode="eval").body
    except (SyntaxError, ValueError):
        return text
    if isinstance(parsed, ast.Constant) and parsed.value == annotation:
        return text
    return extract_type_name(parsed)
def _dotted_annotation_name(annotation: ast.Attribute) -> str:
    parts: list[str] = []
    cur: ast.AST = annotation
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if not isinstance(cur, ast.Name):
        return annotation.attr
    parts.append(cur.id)
    parts.reverse()
    return ".".join(parts)
def _composite_annotation_name(annotation: ast.AST) -> str | None:
    if isinstance(annotation, ast.Subscript):
        return _subscript_annotation_name(annotation)
    if isinstance(annotation, ast.BinOp) and isinstance(annotation.op, ast.BitOr):
        return _unambiguous_type_name(_union_annotation_types(annotation))
    return None
def _subscript_annotation_name(annotation: ast.Subscript) -> str | None:
    container = extract_type_name(annotation.value)
    simple = container.rsplit(".", 1)[-1] if container else ""
    elements = (list(annotation.slice.elts)
                if isinstance(annotation.slice, ast.Tuple)
                else [annotation.slice])
    if simple == "Annotated":
        return extract_type_name(elements[0]) if elements else None
    if simple == "Optional":
        return extract_type_name(annotation.slice)
    if simple == "Union":
        return _unambiguous_type_name(
            extract_type_name(element) for element in elements)
    return container
def _unambiguous_type_name(type_names) -> str | None:
    candidates = {
        name for name in type_names if name and name != "None"
    }
    return candidates.pop() if len(candidates) == 1 else None
def _union_annotation_types(annotation: ast.AST):
    if isinstance(annotation, ast.BinOp) and isinstance(annotation.op, ast.BitOr):
        yield from _union_annotation_types(annotation.left)
        yield from _union_annotation_types(annotation.right)
        return
    type_name = extract_type_name(annotation)
    if type_name and type_name != "None":
        yield type_name
def prescan_module_globals(module_node: ast.Module,
                            module_globals: dict[str, str]) -> None:
    stack = [module_node]
    while stack:
        stmt = stack.pop()
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            continue
        merged = {**_constructor_global_type(stmt),
                  **_annotation_global_type(stmt)}
        for name, type_name in merged.items():
            module_globals.setdefault(name, type_name)
        stack.extend(ast.iter_child_nodes(stmt))
def _constructor_global_type(stmt) -> dict[str, str]:
    if not _is_simple_construction(stmt):
        return {}
    ctor = stmt.value.func.id
    if _is_non_constructor_name(ctor):
        return {}
    return {t.id: ctor for t in stmt.targets if isinstance(t, ast.Name)}
def _is_simple_construction(stmt) -> bool:
    return (isinstance(stmt, ast.Assign)
            and isinstance(stmt.value, ast.Call)
            and isinstance(stmt.value.func, ast.Name))
def _is_non_constructor_name(name: str) -> bool:
    return name in BUILTIN_CALLABLES or name in SELF_CLS_NAMES
def _annotation_global_type(stmt) -> dict[str, str]:
    if not (isinstance(stmt, ast.AnnAssign)
            and isinstance(stmt.target, ast.Name)
            and stmt.value is not None):
        return {}
    ann_type = extract_type_name(stmt.annotation)
    return {stmt.target.id: ann_type} if ann_type else {}
# 后缀段索引：``最后一段 -> 候选键列表``。
#
# ``_lookup_return_type`` / ``lookup_method_return_type`` 的语义是
# 「``k.endswith(suffix)`` 且唯一命中」，原实现在**每个调用点**上全量扫描
# ``store``，于是 O(调用点 × store 大小)。由于 ``suffix`` 总以它的最后
# 一段结尾（``k.endswith(suffix)`` ⇒ ``k`` 也以该段结尾），可以先用最后
# 一段把候选集缩到个位数，再逐个验证——**候选集是原匹配集的超集，
# 故逐字等价**。
_SUFFIX_INDEX_CACHE: dict[int, tuple] = {}
_SUFFIX_INDEX_CACHE_MAX = 64
def _suffix_segment(suffix: str) -> str:
    return suffix.rsplit(".", 1)[-1] if suffix else ""
def _suffix_index(store) -> dict[str, list[str]]:
    """按最后一段建倒排索引（按 store 身份 + 键快照缓存）。"""
    cache_key = id(store)
    keys = tuple(store)
    cached = _SUFFIX_INDEX_CACHE.get(cache_key)
    if (cached is not None and cached[0] is store
            and cached[1] == keys):
        return cached[2]
    index: dict[str, list[str]] = {}
    for candidate in store:
        if isinstance(candidate, str):
            index.setdefault(
                candidate.rsplit(".", 1)[-1], []).append(candidate)
    _SUFFIX_INDEX_CACHE[cache_key] = (store, keys, index)
    while len(_SUFFIX_INDEX_CACHE) > _SUFFIX_INDEX_CACHE_MAX:
        _SUFFIX_INDEX_CACHE.pop(next(iter(_SUFFIX_INDEX_CACHE)), None)
    return index
def _unique_suffix_hit(store, suffix: str) -> str | None:
    """返回 ``endswith(suffix)`` 的唯一命中键；无或多于一个时返回 None。"""
    found: str | None = None
    for candidate in _suffix_index(store).get(_suffix_segment(suffix), ()):
        if not candidate.endswith(suffix):
            continue
        if found is not None:
            return None
        found = candidate
    return found
def _lookup_return_type(store: dict[str, str | None], key: str,
                        suffix: str) -> str | None:
    """按后缀唯一命中查找返回类型。"""
    if key in store:
        return store[key]
    found = _unique_suffix_hit(store, suffix)
    return store[found] if found is not None else None
def lookup_method_return_type(store: dict[str, str | None], obj_type: str,
                               method_name: str) -> str | None:
    key = f"{obj_type}.{method_name}"
    if key in store:
        return store[key]
    suffix = f".{key}"
    found = _unique_suffix_hit(store, suffix)
    if found is not None:
        return store[found]
    simple = obj_type.rsplit(".", 1)[-1]
    if simple == obj_type:
        return None
    simple_key = f"{simple}.{method_name}"
    return store.get(simple_key)
def lookup_func_return_type(store: dict[str, str | None], func_id: str,
                             file_aliases: dict[str, str],
                             module_name: str, pkg_root: str = "") -> str | None:
    normalized = _qualify_type_name(
        func_id, file_aliases, pkg_root) or func_id
    if "." in normalized:
        qualified = normalized
        suffix = f".{normalized}"
    else:
        qualified = _qualify_module_member(module_name, normalized)
        suffix = f".{func_id}"
    return _lookup_return_type(store, qualified, suffix)
def symbol_owner_lookup(symbol: str, symbol_owner, file_symbols):
    if symbol_owner is not None:
        return symbol_owner.get(symbol)
    matches = [fpath for fpath, syms in file_symbols.items()
               if symbol in syms]
    return matches[0] if len(matches) == 1 else None
def is_project_class(graph, module_name: str, callee_name: str) -> bool:
    qualified_names = (
        (callee_name, _qualify_module_member(module_name, callee_name))
        if "." in callee_name
        else (_qualify_module_member(module_name, callee_name),)
    )
    _class_files = getattr(graph, "class_files", None) or {}
    if any(
            name in graph.class_inheritance
            or name in graph.dataclass_classes
            or name in _class_files
            for name in qualified_names):
        return True
    return ("." not in callee_name
            and bool(class_method_names(graph, callee_name)))
def _methods_at_class_key(graph, class_key: str) -> set[str]:
    """类 key 对应的方法名集合（含 ``类.`` 前缀的直属函数）。

    本函数对**每个调用点**都要跑一次，而函数体内部有两次全量扫描：

    1. ``graph.class_methods`` 的键（每键一次 ``normalize_torn_name``）
    2. ``graph.functions`` 的键（每键一次 ``startswith`` + 切片）

    于是整体退化为 O(调用点 × (类数 + 函数数))。现在按
    ``normalized`` 做结果缓存。版本覆盖类方法的键与方法集，以及函数表的
    身份及其修订号或键快照，因此等长替换和原方法集内增删也会使缓存失效。

    注：不能直接复用 ``_class_method_index``，因为它用 ``_as_name_tuple``
    而本函数用 ``torn_list``，二者对 ``str`` 类型的 methods 语义不同
    （前者视为单元组、后者视为空），替换会改变检测结论。
    """
    normalized = normalize_torn_name(class_key)
    methods_version = tuple(
        (key, frozenset(torn_list(methods)))
        for key, methods in graph.class_methods.items()
    )
    functions_version = _funcs_revision(graph.functions)
    if functions_version is None:
        functions_version = tuple(graph.functions)
    functions_version = (id(graph.functions), functions_version)
    _sig = (id(graph), methods_version, functions_version)
    _cache = getattr(graph, "_methods_at_class_key_cache", None)
    if _cache is not None and _cache[0] == _sig:
        _hit = _cache[1].get(normalized)
        if _hit is not None:
            return set(_hit)
    else:
        _cache = (_sig, {})
        graph._methods_at_class_key_cache = _cache
    exact_keys = [
        key for key in graph.class_methods
        if isinstance(key, str) and normalize_torn_name(key) == normalized
    ]
    methods = {
        method for key in exact_keys
        for method in torn_list(graph.class_methods[key])
    }
    prefix = f"{normalized}."
    methods.update(
        full_key[len(prefix):] for full_key in graph.functions
        if isinstance(full_key, str) and full_key.startswith(prefix)
        and "." not in full_key[len(prefix):]
    )
    if exact_keys or methods:
        _cache[1][normalized] = frozenset(methods)
        return methods
    if "." in normalized:
        _cache[1][normalized] = frozenset()
        return set()
    _fallback = class_method_names(graph, normalized)
    _cache[1][normalized] = frozenset(_fallback)
    return _fallback
def class_or_bases_define_method(graph, class_name: str, method: str) -> bool:
    class_key = class_key_by_simple(
        graph, normalize_torn_name(class_name)) or normalize_torn_name(class_name)
    if method in _methods_at_class_key(graph, class_key):
        return True
    seen: set[str] = set()
    frontier = [class_key]
    while frontier:
        class_key = frontier.pop(0)
        if class_key in seen:
            continue
        seen.add(class_key)
        for base_key, _simple in _parent_entries(graph, class_key):
            if method in _methods_at_class_key(graph, base_key):
                return True
            frontier.append(base_key)
    return False
# 类名归一化索引：``exact: 归一化名 -> [keys]`` 与 ``tail: 最后一段 -> [keys]``。
#
# 原实现对**每个调用点**都做三件昂贵的事：
#   1. ``set(class_files)`` / ``set(class_inheritance) | set(class_methods)``
#      —— 每次新建 3 个 set 副本；
#   2. 对每个键调 **2 次** ``normalize_torn_name``（字符串拆分/拼接）；
#   3. 全量扫描。
# 于是整体为 O(调用点 × (类文件数 + 继承数 + 类方法数))。
# 索引命中后只需 O(候选数)，键快照验证与键数相关；``tail`` 索引利用「``k.endswith(suffix)`` ⇒
# k 以 suffix 最后一段结尾」把候选集缩到个位数，**匹配集是原集合的超集、
# 再逐个验证，故语义逐字等价**。
_CLASS_KEY_INDEX_CACHE: dict[int, tuple] = {}
_CLASS_KEY_INDEX_CACHE_MAX = 32
def _build_name_index(keys) -> tuple[dict, dict]:
    """构建 ``(exact_index, tail_index)`` 两组倒排表。"""
    exact: dict[str, list[str]] = {}
    tail: dict[str, list[str]] = {}
    for candidate in keys:
        if not isinstance(candidate, str):
            continue
        normalized = normalize_torn_name(candidate)
        exact.setdefault(normalized, []).append(candidate)
        tail.setdefault(normalized.rsplit(".", 1)[-1], []).append(candidate)
    return exact, tail
def _class_key_indexes(graph) -> tuple:
    """返回两组索引（按 graph 身份 + 三个容器的键快照缓存）。"""
    class_files = getattr(graph, "class_files", None) or {}
    inheritance = graph.class_inheritance
    methods = graph.class_methods
    signature = (tuple(class_files), tuple(inheritance), tuple(methods))
    cached = _CLASS_KEY_INDEX_CACHE.get(id(graph))
    if (cached is not None and cached[0] is graph
            and cached[1] == signature):
        return cached[2]
    groups = (
        _build_name_index(class_files),
        _build_name_index(set(inheritance) | set(methods)),
    )
    _CLASS_KEY_INDEX_CACHE[id(graph)] = (graph, signature, groups)
    while len(_CLASS_KEY_INDEX_CACHE) > _CLASS_KEY_INDEX_CACHE_MAX:
        _CLASS_KEY_INDEX_CACHE.pop(next(iter(_CLASS_KEY_INDEX_CACHE)), None)
    return groups
def _group_simple_matches(group: tuple, target: str) -> set[str]:
    """单组内的「精确或后缀」匹配集（与原列表推导逐字等价）。"""
    exact_index, tail_index = group
    found: set[str] = set(exact_index.get(target, ()))
    for candidate in tail_index.get(target.rsplit(".", 1)[-1], ()):
        normalized = normalize_torn_name(candidate)
        if normalized == target or normalized.endswith(f".{target}"):
            found.add(candidate)
    return found
def class_key_by_simple(graph, simple: str) -> str | None:
    target = normalize_torn_name(simple)
    for group in _class_key_indexes(graph):
        matches = _group_simple_matches(group, target)
        if matches:
            return next(iter(matches)) if len(matches) == 1 else None
    return None
def _resolve_class_key(graph, module_name: str,
                       class_name: str) -> str | None:
    if class_name in graph.class_inheritance:
        return class_name
    direct = _qualify_module_member(module_name, class_name)
    if direct in graph.class_inheritance:
        return direct
    if "." in class_name:
        return None
    return class_key_by_simple(graph, class_name)
def _super_method_key(graph, module_name: str, base_key: str, simple: str,
                      method: str) -> str | None:
    key = f"{base_key}.{method}"
    if key in graph.functions:
        return key
    hits = functions_ending_with(
        graph.functions, f"{simple}.{method}")
    if len(hits) == 1:
        return hits[0]
    if len(hits) > 1:
        same_mod = _qualify_module_member(module_name, f"{simple}.{method}")
        if same_mod in hits:
            return same_mod
    return None
def resolve_inherited_method(graph, module_name: str, method: str,
                              start_class: str | None = None) -> str | None:
    cls = start_class
    if not cls:
        return None
    start = _resolve_class_key(graph, module_name, cls)
    if start is None:
        return None
    queue = [start]
    visited = {start}
    while queue:
        cls_key = queue.pop(0)
        for base_key, simple in _unvisited_parents(graph, cls_key, visited):
            if method in _methods_at_class_key(graph, base_key):
                resolved = _super_method_key(
                    graph, module_name, base_key, simple, method)
                if resolved is not None:
                    return resolved
            queue.append(base_key)
    return None
def _unvisited_parents(graph, cls_key: str, visited: set[str]):
    for base_key, simple in _parent_entries(graph, cls_key):
        if base_key in visited:
            continue
        visited.add(base_key)
        yield base_key, simple
def _parent_entries(graph, cls_key: str):
    for base_written in torn_list(graph.class_inheritance.get(cls_key)):
        written = normalize_torn_name(base_written)
        yield (resolve_base_key(graph, cls_key, written),
               written.rsplit(".", 1)[-1])
def resolve_base_key(graph, cls_key: str, base_written: str) -> str:
    class_files = getattr(graph, "class_files", None) or {}
    class_file = class_files.get(cls_key)
    module_name = (
        path_to_dotted_module(class_file) if class_file is not None
        else cls_key.rsplit(".", 1)[0] if "." in cls_key else ""
    )
    scope = cls_key.rsplit(".", 1)[0] if "." in cls_key else ""
    candidates = []
    while scope and scope != module_name:
        candidates.append(_qualify_module_member(scope, base_written))
        scope = scope.rsplit(".", 1)[0] if "." in scope else ""
    candidates.append(_qualify_module_member(module_name, base_written))
    for candidate in dict.fromkeys(candidates):
        if candidate in graph.class_inheritance or candidate in class_files:
            return candidate
    if "." in base_written:
        return base_written
    return class_key_by_simple(graph, base_written) or candidates[-1]
def dotted_name_of(node) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return ast.unparse(node)
    return None
def is_cls_bound_factory(types_state, func_name: str, current_class) -> bool:
    return (func_name == "cls" and bool(current_class)
            and types_state.cls_bound_to_class)
def is_self_attr_target(target: ast.AST, current_class) -> bool:
    return (bool(current_class)
            and isinstance(target, ast.Attribute)
            and isinstance(target.value, ast.Name)
            and target.value.id == 'self')
def _destructured_elements(target) -> tuple:
    return (target.value,) if isinstance(target, ast.Starred) else target.elts
@cache
def _get_walk_dispatch(visitor_cls: type) -> dict:
    return build_node_dispatch(visitor_cls)
def _walk_dfs(node, pairs):
    cls = node.__class__
    for v, _tget in pairs:
        method = _tget(cls)
        if method is not None:
            method(v, node)
    for _field in node._fields:
        try:
            value = getattr(node, _field)
        except AttributeError:
            logger.debug("单趟遍历字段访问失败(跳过): %s.%s",
                         type(node).__name__, _field)
            continue
        _walk_child_value(value, pairs)
def _walk_child_value(value, pairs):
    if isinstance(value, list):
        for item in value:
            if isinstance(item, ast.AST):
                _walk_dfs(item, pairs)
    elif isinstance(value, ast.AST):
        _walk_dfs(value, pairs)
def walk_visitors_once(tree: ast.AST, visitors) -> None:
    visitors = list(visitors)
    pairs = [(v, _get_walk_dispatch(type(v)).get) for v in visitors]
    saved = {
        id(v): (v, v.__dict__.get('generic_visit'),
                'generic_visit' in v.__dict__)
        for v in visitors
    }
    try:
        for v in visitors:
            v.generic_visit = lambda _node: None
        _walk_dfs(tree, pairs)
    finally:
        for v, orig, had_own in saved.values():
            if had_own:
                v.generic_visit = orig
            else:
                v.__dict__.pop('generic_visit', None)
_MODULE_SCOPE_NAME = "<module>"
_NEUTRAL_BASE_CLASSES = frozenset({
    "object", "Generic", "Protocol", "ABC", "ABCMeta",
    "NamedTuple", "TypedDict",
})
_MODULE_SCOPE_SUFFIX = "." + _MODULE_SCOPE_NAME
def _register_edge(graph, edge: CallEdge) -> None:
    graph.calls.append(edge)
    graph.callers[edge.callee_func].add(edge.caller_func)
def _add_call_edge(graph, filepath: str, node: ast.Call, caller: str,
                   callee_name: str, callee_file: str | None,
                   is_external: bool, is_self: bool,
                   type_resolution_blocked: bool = False) -> None:
    edge = CallEdge(
        caller_file=filepath,
        caller_func=caller,
        callee_func=callee_name,
        callee_file=callee_file,
        line=node.lineno,
        is_external=is_external,
        is_self_call=is_self,
        args_count=len(node.args) + len(node.keywords),
        type_resolution_blocked=type_resolution_blocked,
    )
    _register_edge(graph, edge)
def _add_constructor_init_edge(graph, filepath: str, module_name: str,
                               callee_name: str, caller: str,
                               node: ast.Call) -> None:
    init_key = f"{callee_name}.__init__"
    if init_key not in graph.functions and "." not in callee_name:
        _qualified_init = _qualify_module_member(
            module_name, f"{callee_name}.__init__")
        if _qualified_init in graph.functions:
            init_key = _qualified_init
    if init_key not in graph.functions:
        if not is_project_class(graph, module_name, callee_name):
            return
        init_key = _constructor_init_key_by_simple(graph, callee_name)
    if init_key not in graph.functions:
        return
    _add_call_edge(graph, filepath, node, caller, init_key,
                   graph.functions[init_key].filepath, False, False)
def _constructor_init_key_by_simple(graph, callee_name: str) -> str:
    simple = callee_name.rsplit(".", 1)[-1]
    candidates = [
        f"{cls_key}.__init__"
        for cls_key in (getattr(graph, "class_files", None) or {})
        if isinstance(cls_key, str)
        and cls_key.rsplit(".", 1)[-1] == simple
        and f"{cls_key}.__init__" in graph.functions
    ]
    return candidates[0] if len(candidates) == 1 else ""
def _iter_definition_annotations(node: ast.FunctionDef | ast.AsyncFunctionDef):
    for arg in iter_arg_nodes(node.args):
        if arg.annotation is not None:
            yield arg.annotation
    if node.returns is not None:
        yield node.returns
def _own_module_hit(hits, module_name: str, suffix: str) -> str | None:
    own = [hit for hit in hits if hit[: -len(suffix) - 1] == module_name]
    return own[0] if len(own) == 1 else None
def _unique_method_hit(hits, module_name: str,
                        suffix: str) -> str | None:
    if len(hits) == 1:
        return hits[0]
    return _own_module_hit(hits, module_name, suffix)
def _string_ref_attr_name(node: ast.Call) -> str | None:
    if len(node.args) < 2:
        return None
    attr_arg = node.args[1]
    if isinstance(attr_arg, ast.Constant) and isinstance(attr_arg.value, str):
        return attr_arg.value
    return None
@dataclass(frozen=True)
class _RefEdgeFlags:
    args_count: int = 0
    is_self: bool = False
class _RefEdgeBuilder:
    def __init__(self, graph, filepath, module_name,
                 file_aliases: dict[str, str] | None = None) -> None:
        self._graph = graph
        self._filepath = filepath
        self._module_name = module_name
        self._file_aliases = file_aliases or {}
        self._pkg_root = _graph_pkg_root(graph)
        _property_map, self._prop_by_attr = property_maps(graph.functions)
        self._fallback_prop_edges: set[tuple[str, str]] = set()
        self._string_ref_edges: set[tuple[str, str]] = set()
        self._dyn_resolved_sites: set[tuple[str, int]] = set()
    def mark_dyn_resolved(self, callee_name: str, lineno: int) -> None:
        self._dyn_resolved_sites.add((callee_name, lineno))
    def handle_string_ref(self, node: ast.Call, caller: str, func_name: str,
                          receiver_type: str | None) -> None:
        attr_name = _string_ref_attr_name(node)
        if attr_name is None:
            return
        if func_name == "getattr":
            self._handle_getattr_ref(node, caller, attr_name, receiver_type)
        elif func_name == "setattr":
            self._handle_setattr_ref(
                node, caller, attr_name, receiver_type)
        elif func_name == "hasattr":
            self._handle_hasattr_ref(caller, attr_name, receiver_type)
    def _attr_candidates(self, attr_name: str, *, include_synthetic: bool = False,
                         property_only: bool = False) -> list[str]:
        return [
            full_key
            for full_key, is_syn, is_prop in functions_by_attr_name(
                self._graph.functions, attr_name)
            if (include_synthetic or not is_syn)
            and (not property_only or is_prop
                 or self._is_property_accessor(full_key))
        ]
    def _is_property_accessor(self, full_key: str) -> bool:
        fnode = self._graph.functions.get(full_key)
        if fnode is None:
            return False
        if getattr(fnode, "is_property", False):
            return True
        return any(
            str(dec).rsplit(".", 1)[-1] in ("setter", "deleter")
            for dec in (getattr(fnode, "decorators", None) or ()))
    def _link_once(self, node: ast.AST, caller: str, full_key: str, registry,
                   flags: _RefEdgeFlags | None = None) -> None:
        edge_key = (caller, full_key)
        if edge_key in registry:
            return
        self._append_ref_edge(node, caller, full_key, flags)
        registry.add(edge_key)
    def _typed_attr_targets(
            self, receiver_type: str | None, attr_name: str, *,
            require_property: bool) -> tuple[list[str], bool]:
        if not receiver_type:
            return [], False
        suffix = f"{receiver_type}.{attr_name}"
        hits = list(functions_ending_with(self._graph.functions, suffix))
        if not hits:
            inherited = resolve_inherited_method(
                self._graph, self._module_name, attr_name,
                start_class=receiver_type)
            if inherited is None:
                return [], True
            hits = [inherited]
        if require_property:
            hits = [h for h in hits if self._is_property_accessor(h)]
        if not hits:
            return [], True
        target = _unique_method_hit(hits, self._module_name, suffix)
        return ([target] if target else []), True
    def _getattr_targets(
            self, receiver_type: str | None,
            attr_name: str) -> tuple[list[str], bool]:
        targets, settled = self._typed_attr_targets(
            receiver_type, attr_name, require_property=False)
        if settled:
            return targets, True
        return self._attr_candidates(attr_name), False
    def _handle_getattr_ref(self, node: ast.Call, caller: str,
                            attr_name: str, receiver_type: str | None) -> None:
        targets, settled = self._getattr_targets(receiver_type, attr_name)
        if settled:
            if targets and (targets[0], node.lineno) not in self._dyn_resolved_sites:
                self._append_ref_edge(node, caller, targets[0])
            return
        for full_key in targets:
            if (full_key, node.lineno) in self._dyn_resolved_sites:
                continue
            self._link_once(node, caller, full_key, self._string_ref_edges)
    def _handle_setattr_ref(self, node: ast.Call, caller: str,
                            attr_name: str,
                            receiver_type: str | None) -> None:
        targets, settled = self._typed_attr_targets(
            receiver_type, attr_name, require_property=True)
        if settled:
            for full_key in targets:
                self._link_once(node, caller, full_key,
                                self._string_ref_edges,
                                _RefEdgeFlags(args_count=1))
            return
        for full_key in self._attr_candidates(
                attr_name, include_synthetic=True, property_only=True):
            self._link_once(node, caller, full_key, self._string_ref_edges,
                            _RefEdgeFlags(args_count=1))
    def _handle_hasattr_ref(self, caller: str, attr_name: str,
                            receiver_type: str | None) -> None:
        targets, settled = self._typed_attr_targets(
            receiver_type, attr_name, require_property=False)
        if settled:
            for full_key in targets:
                self._graph.callers[full_key].add(caller)
            return
        for full_key in self._attr_candidates(
                attr_name, include_synthetic=True):
            self._graph.callers[full_key].add(caller)
    def handle_attribute_read(self, node: ast.Attribute, caller: str,
                              class_name: str | None,
                              is_self: bool) -> None:
        if class_name:
            self._emit_typed_property_edge(node, caller, class_name, is_self)
        else:
            self._emit_fallback_prop_edges(node, caller)
    def _emit_typed_property_edge(self, node: ast.Attribute, caller: str,
                                  class_name: str, is_self: bool) -> None:
        class_name = (_qualify_type_name(
            class_name, self._file_aliases, self._pkg_root) or class_name)
        targets, settled = self._typed_attr_targets(
            class_name, node.attr, require_property=True)
        if settled:
            if not targets:
                return
            full_key = targets[0]
        else:
            full_key = resolve_inherited_method(
                self._graph, self._module_name, node.attr,
                start_class=class_name)
            if (full_key is None
                    or not self._is_property_accessor(full_key)):
                return
        self._append_ref_edge(
            node, caller, full_key, _RefEdgeFlags(is_self=is_self))
    def _emit_fallback_prop_edges(self, node: ast.Attribute,
                                  caller: str) -> None:
        for full_key in self._prop_by_attr.get(node.attr, []):
            if full_key not in self._graph.functions:
                continue
            self._link_once(node, caller, full_key, self._fallback_prop_edges)
    def link_super_call(self, node: ast.Call, caller: str,
                        start_class: str | None) -> None:
        callee = resolve_inherited_method(
            self._graph, self._module_name, node.func.attr,
            start_class=start_class)
        if callee is None:
            return
        self._append_ref_edge(
            node, caller, callee,
            _RefEdgeFlags(args_count=len(node.args) + len(node.keywords)))
    def _append_ref_edge(self, node: ast.AST, caller: str, full_key: str,
                         flags: _RefEdgeFlags | None = None) -> None:
        _flags = flags or _RefEdgeFlags()
        fnode = self._graph.functions[full_key]
        edge = CallEdge(
            caller_file=self._filepath, caller_func=caller,
            callee_func=full_key, callee_file=fnode.filepath,
            line=node.lineno, is_external=False, is_self_call=_flags.is_self,
            args_count=_flags.args_count,
        )
        _register_edge(self._graph, edge)
class _DictFuncEdgeBuilder:
    def __init__(self, graph, filepath, file_symbols, module_name,
                 file_aliases, pkg_root, symbol_index) -> None:
        self.graph = graph
        self.filepath = filepath
        self.file_symbols = file_symbols
        self._file_aliases = file_aliases
        self._pkg_root = pkg_root
        self._symbol_index = symbol_index
        self._module_name = module_name
        self.edges_created: set[tuple[str, str]] = set()
    def add_edge(self, callee_name: str, caller: str, lineno: int) -> None:
        callee_name = self._resolve_alias(callee_name)
        callee_name, callee_file = resolve_callee_file(
            self.graph, self.filepath, self.file_symbols, self._pkg_root,
            self._module_name, self._symbol_index, callee_name)
        if callee_file is None:
            return
        self._emit_edge(caller, callee_name, callee_file, lineno)
    def _resolve_alias(self, callee_name: str) -> str:
        head, dot, rest = callee_name.partition(".")
        target = self._file_aliases.get(head)
        if target is None:
            return callee_name
        return f"{target}.{rest}" if dot and rest else target
    def _emit_edge(self, caller: str, callee_name: str,
                   callee_file: str, lineno: int) -> None:
        edge_key = (caller, callee_name)
        if edge_key in self.edges_created:
            return
        self.edges_created.add(edge_key)
        if caller in self.graph.callers.get(callee_name, ()):
            return
        _register_edge(self.graph, CallEdge(
            caller_file=self.filepath,
            caller_func=caller,
            callee_func=callee_name,
            callee_file=callee_file,
            line=lineno,
        ))
class CalleeFileContext:
    def __init__(self, filepath, import_aliases, file_symbols,
                 symbol_index=None) -> None:
        self.filepath = filepath
        self.import_aliases = import_aliases
        self.file_symbols = file_symbols
        self.symbol_index = symbol_index
class CalleeResolver:
    def __init__(self, graph, file_ctx, symbol_owner, return_types,
                 types, dispatch) -> None:
        self.graph = graph
        self.filepath = file_ctx.filepath
        self.file_symbols = file_ctx.file_symbols
        self._symbol_index = file_ctx.symbol_index
        self._file_aliases = _file_alias_map(
            file_ctx.import_aliases, file_ctx.filepath)
        self._pkg_root = _graph_pkg_root(graph)
        self._symbol_owner = symbol_owner
        self._module_name = path_to_dotted_module(file_ctx.filepath)
        self._return_types = return_types
        self._types = types
        self._dispatch = dispatch
        self._shadowed_names: set[str] = set()
        self._alias_target_names: frozenset[str] = frozenset(
            self._file_aliases.values())
        self._graph_alias_target_names: frozenset[str] = frozenset(
            strip_pkg_root(name, self._pkg_root)
            for name in self._alias_target_names)
        self._dict_edges = _DictFuncEdgeBuilder(
            graph, file_ctx.filepath, file_ctx.file_symbols,
            self._module_name, self._file_aliases, self._pkg_root,
            symbol_index=self._symbol_index)
    def _resolve_receiver_type(self, base_node: ast.AST,
                                current_class: str | None) -> str | None:
        if isinstance(base_node, ast.Call):
            return self._resolve_call_receiver_type(base_node, current_class)
        if not isinstance(base_node, ast.Name):
            return None
        return self._name_receiver_type(base_node.id, current_class)
    def _aliases_for_name(self, name: str) -> dict[str, str]:
        if self._types.has_callable_binding(name):
            target = self._types.callable_alias(name)
            if target is not None:
                return {**self._file_aliases, name: target}
        return self._file_aliases
    def _visible_callable_name(self, name: str) -> str | None:
        if not self._types.has_callable_binding(name):
            return name
        target = self._types.callable_alias(name)
        if target is None:
            return None
        if target == name:
            return name
        return self._file_aliases.get(target, target)
    def _is_builtin_name_call(self, func_node, name: str) -> bool:
        if not (isinstance(func_node, ast.Name) and func_node.id == name):
            return False
        if name in self._shadowed_names:
            return False
        return self._visible_callable_name(name) in (
            name, f"builtins.{name}")
    def _name_receiver_type(self, name: str,
                            current_class: str | None) -> str | None:
        if name in SELF_CLS_NAMES:
            return current_class
        var_type = self._types.var_type(name)
        if var_type is not None:
            return _qualify_type_name(
                var_type, self._file_aliases, self._pkg_root)
        visible = self._visible_callable_name(name)
        if visible is None:
            return None
        qualified = _qualify_type_name(
            visible, self._aliases_for_name(name), self._pkg_root)
        return self._canonical_project_class(qualified)
    def _canonical_project_class(self, qualified: str | None) -> str | None:
        if not qualified or not is_project_class(
                self.graph, self._module_name, qualified):
            return None
        class_files = getattr(self.graph, "class_files", None) or {}
        own = _qualify_module_member(self._module_name, qualified)
        for candidate in (qualified, own):
            if candidate in class_files:
                return candidate
        suffix = f".{qualified}"
        found = _unique_suffix_hit(class_files, suffix)
        return found if found is not None else qualified
    def _static_import_module_arg(self, call_node: ast.Call) -> str | None:
        func = call_node.func
        bound_name = (
            func.id if isinstance(func, ast.Name)
            else func.value.id
            if (isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Name))
            else None
        )
        if bound_name is None:
            return None
        if (bound_name in self._shadowed_names
                or (self._types.has_callable_binding(bound_name)
                    and self._types.callable_alias(bound_name) is None)
                or self._types.var_type(bound_name) is not None):
            return None
        return static_import_module_arg(
            call_node, self._aliases_for_name(bound_name))
    def _resolve_call_receiver_type(self, call_node: ast.Call,
                                     current_class: str | None) -> str | None:
        func = call_node.func
        if isinstance(func, ast.Name):
            if is_cls_bound_factory(self._types, func.id, current_class):
                return current_class
            if self._is_builtin_name_call(func, "getattr"):
                attr_type = self._resolve_getattr_value_type(
                    call_node, current_class)
                if attr_type:
                    return _qualify_type_name(
                        attr_type, self._file_aliases, self._pkg_root)
        self_attr_type = self._resolve_self_attr_receiver_type(
            func, current_class)
        if self_attr_type is not None:
            return self_attr_type
        module_name = self._static_import_module_arg(call_node)
        if module_name is not None:
            return _qualify_type_name(
                module_name, self._file_aliases, self._pkg_root)
        if isinstance(func, ast.Attribute):
            obj_type = self._resolve_receiver_type(
                func.value, current_class)
            if obj_type:
                ret_type = lookup_method_return_type(
                    self._return_types, obj_type, func.attr)
                if ret_type:
                    return _qualify_type_name(
                        ret_type, self._file_aliases, self._pkg_root)
        return self._resolve_bare_name_receiver_type(func)
    def _resolve_self_attr_receiver_type(self, func, current_class):
        if not (isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Name)
                and func.value.id in SELF_CLS_NAMES
                and current_class):
            return None
        qualified = _qualify_type_name(
            func.attr, self._file_aliases, self._pkg_root)
        method_defined = class_or_bases_define_method(
            self.graph, current_class, func.attr)
        if (not method_defined
                and is_project_class(self.graph, self._module_name, qualified)):
            return qualified
        return _qualify_type_name(
            lookup_method_return_type(
                self._return_types, current_class, func.attr),
            self._file_aliases, self._pkg_root)
    def _resolve_bare_name_receiver_type(self, func):
        name = dotted_name_of(func)
        if not name:
            return None
        aliases = self._file_aliases
        if isinstance(func, ast.Name):
            aliases = self._aliases_for_name(name)
            name = self._visible_callable_name(name)
            if name is None:
                return None
        ret_type = lookup_func_return_type(
            self._return_types, name, aliases, self._module_name,
            self._pkg_root)
        if ret_type:
            return _qualify_type_name(
                ret_type, self._file_aliases, self._pkg_root)
        qualified = _qualify_type_name(
            name, aliases, self._pkg_root)
        return self._canonical_project_class(qualified)
    def _resolve_getattr_value_type(self, call: ast.Call,
                                    current_class: str | None) -> str | None:
        if len(call.args) != 2:
            return None
        attr_name = _const_str(call.args[1])
        if attr_name is None:
            return None
        obj_type = self._resolve_receiver_type(call.args[0], current_class)
        if not obj_type:
            return None
        return_type = lookup_method_return_type(
            self._return_types, obj_type, attr_name)
        if return_type:
            return return_type
        return self._types.instance_attr_type(obj_type, attr_name)
    def resolve_declared_class(self, recv, current_class: str | None):
        if isinstance(recv, ast.Name):
            return self._name_receiver_type(recv.id, current_class)
        if (isinstance(recv, ast.Attribute)
                and isinstance(recv.value, ast.Name)):
            return self._declared_class_of_attr(
                recv.value.id, recv.attr, current_class)
        return None
    def _declared_class_of_attr(self, base: str, attr: str,
                                current_class: str | None):
        if base in SELF_CLS_NAMES and current_class:
            return self._types.instance_attr_type(current_class, attr)
        owner_type = self._types.var_type(base)
        if owner_type is not None:
            owner_type = _qualify_type_name(
                owner_type, self._file_aliases, self._pkg_root)
            return self._types.instance_attr_type(owner_type, attr)
        return None
    def _resolve_dataflow_callee(
            self, callee_name: str, current_class: str | None,
            receiver_node: ast.AST | None = None) -> str:
        callee_name = _strip_pkg_root_nonempty(callee_name, self._pkg_root)
        if callee_name in self.graph.functions:
            return callee_name
        if self._is_alias_target(callee_name):
            return callee_name
        parts = callee_name.split(".")
        is_class_attr_receiver = (
            current_class is not None
            and isinstance(receiver_node, ast.Attribute)
            and isinstance(receiver_node.value, ast.Name)
            and receiver_node.value.id in SELF_CLS_NAMES)
        class_name = self._resolve_var_class_name(
            parts[0], current_class,
            use_instance_attr=len(parts) >= 2 and is_class_attr_receiver)
        if not class_name:
            return callee_name
        class_name = _qualify_type_name(
            class_name, self._file_aliases, self._pkg_root)
        method_name = ".".join(parts[1:])
        resolved = self._typed_method_hit(class_name, method_name)
        if resolved is None:
            resolved = resolve_inherited_method(
                self.graph, self._module_name, method_name,
                start_class=class_name)
        if resolved is None and "." in method_name:
            return callee_name
        return resolved or f"{class_name}.{method_name}"
    def _is_alias_target(self, callee_name: str) -> bool:
        return any(callee_name == qual or callee_name.startswith(qual + ".")
                   for qual in self._graph_alias_target_names)
    def _resolve_var_class_name(self, var_name: str,
                                current_class: str | None,
                                use_instance_attr: bool) -> str | None:
        if current_class and use_instance_attr:
            return self._types.instance_attr_type(current_class, var_name)
        return self._types.var_type(var_name)
    def _resolve_call_target(self, callee_name: str, is_self: bool,
                             current_class: str | None
                             ) -> tuple[str, str | None, bool]:
        callee_name = _strip_pkg_root_nonempty(callee_name, self._pkg_root)
        if is_self and current_class:
            return self._resolve_self_target(callee_name, current_class)
        if callee_name in self.graph.functions:
            return self._graph_target(callee_name)
        if "." not in callee_name:
            return self._resolve_bare_name_target(callee_name)
        return self._resolve_qualified_target(callee_name)
    def _graph_target(self, key: str) -> tuple[str, str | None, bool]:
        return key, self.graph.functions[key].filepath, False
    def _resolve_self_target(self, callee_name: str,
                             current_class: str) -> tuple[str, str | None, bool]:
        resolved = _qualify_module_member(
            self._module_name, f"{current_class}.{callee_name}")
        if resolved in self.graph.functions:
            return self._graph_target(resolved)
        inherited = resolve_inherited_method(
            self.graph, self._module_name, callee_name,
            start_class=current_class)
        if inherited is not None:
            return self._graph_target(inherited)
        if self._class_chain_has_external_base(current_class):
            return callee_name, None, True
        return None, None, False
    def _class_chain_has_external_base(self, current_class: str) -> bool:
        start = self._class_key_of(current_class)
        if start is None:
            return False
        stack = [start]
        seen: set[str] = set()
        while stack:
            cls_key = stack.pop()
            if cls_key in seen:
                continue
            seen.add(cls_key)
            for base_written in torn_list(
                    self.graph.class_inheritance.get(cls_key)):
                base_key = resolve_base_key(
                    self.graph, cls_key, base_written)
                if base_key in self.graph.class_inheritance:
                    stack.append(base_key)
                    continue
                if is_project_class(
                        self.graph, self._module_name, base_key):
                    continue
                if base_key.rsplit(".", 1)[-1] in _NEUTRAL_BASE_CLASSES:
                    continue
                return True
        return False
    def _class_key_of(self, current_class: str) -> str | None:
        direct = _qualify_module_member(self._module_name, current_class)
        if direct in self.graph.class_inheritance:
            return direct
        return class_key_by_simple(self.graph, current_class)
    def _resolve_bare_name_target(self, callee_name: str
                                  ) -> tuple[str, str | None, bool]:
        if (self._types.has_callable_binding(callee_name)
                and self._types.callable_alias(callee_name) is None):
            return callee_name, None, True
        simple_full = _qualify_module_member(
            self._module_name, callee_name)
        if simple_full in self.graph.functions:
            return self._graph_target(simple_full)
        owned_full = self._owned_module_key(callee_name)
        if owned_full is not None:
            return self._graph_target(owned_full)
        return callee_name, None, True
    def _owned_module_key(self, callee_name: str) -> str | None:
        fpath = symbol_owner_lookup(callee_name, self._symbol_owner,
                                     self.file_symbols)
        if fpath is None:
            return None
        key = _qualify_module_member(
            path_to_dotted_module(fpath), callee_name)
        return key if key in self.graph.functions else None
    def _resolve_qualified_target(self, callee_name: str
                                  ) -> tuple[str, str | None, bool]:
        confirmed = functions_ending_with(
            self.graph.functions, f".{callee_name}", dot_or_equal=False)
        if len(confirmed) == 1:
            return self._graph_target(confirmed[0])
        if confirmed:
            own = _qualify_module_member(self._module_name, callee_name)
            if own in confirmed:
                return self._graph_target(own)
        return callee_name, None, True
    def _typed_method_hit(self, type_name: str, method_name: str) -> str | None:
        suffix = f"{type_name}.{method_name}"
        hits = functions_ending_with(self.graph.functions, suffix)
        return _unique_method_hit(hits, self._module_name, suffix)
    def _lookup_typed_method(self, base_node: ast.AST, attr_name: str,
                             current_class: str | None) -> str | None:
        type_name = self._resolve_receiver_type(base_node, current_class)
        if not type_name:
            return None
        suffix = f"{type_name}.{attr_name}"
        hits = list(functions_ending_with(self.graph.functions, suffix))
        if hits:
            return _unique_method_hit(hits, self._module_name, suffix)
        return resolve_inherited_method(
            self.graph, self._module_name, attr_name, start_class=type_name)
    def _resolve_callee(self, func_node: ast.AST,
                        current_class: str | None,
                        current_func: str | None) -> tuple[str | None, bool]:
        if isinstance(func_node, ast.Name):
            return self._resolve_name_callee(func_node)
        if isinstance(func_node, ast.Attribute):
            return self._resolve_attribute_callee(
                func_node, current_class, current_func)
        if isinstance(func_node, ast.Subscript):
            return self._resolve_subscript_callee(
                func_node, current_class, current_func)
        if isinstance(func_node, ast.Call):
            return self._resolve_dynamic_call_callee(
                func_node, current_class, current_func) or (None, False)
        return None, False
    def shadow_name(self, name: str) -> None:
        self._shadowed_names.add(name)
    def _resolve_name_callee(self, func_node: ast.Name) -> tuple[str, bool]:
        name = func_node.id
        if self._types.has_callable_binding(name):
            target = self._types.callable_alias(name)
            if target is None:
                return name, False
            if target == name:
                return name, False
            return self._file_aliases.get(target, target), False
        if name in self._shadowed_names:
            return name, False
        return self._file_aliases.get(name, name), False
    def _resolve_attribute_callee(self, func_node, current_class: str | None,
                                  current_func: str | None
                                  ) -> tuple[str | None, bool]:
        typed = self._typed_attribute_target(func_node, current_class)
        if typed is not None:
            return typed, False
        base_name = self._resolve_callee(
            func_node.value, current_class, current_func)[0]
        if base_name in SELF_CLS_NAMES:
            if base_name == "cls":
                bound = self._types.cls_bound_to_class and bool(current_class)
            else:
                bound = current_class is not None
            if not bound:
                return None, False
            return func_node.attr, True
        if (isinstance(func_node.value, ast.Name)
                and self._visible_callable_name(func_node.value.id) is None):
            return None, False
        if base_name:
            return f"{base_name}.{func_node.attr}", False
        return None, False
    def _typed_attribute_target(self, func_node: ast.Attribute,
                                current_class: str | None) -> str | None:
        value = func_node.value
        if isinstance(value, ast.Name) and value.id in SELF_CLS_NAMES:
            return None
        if isinstance(value, (ast.Name, ast.Call)):
            return self._lookup_typed_method(
                value, func_node.attr, current_class)
        return None
    def _resolve_subscript_callee(self, func_node,
                                  current_class: str | None,
                                  current_func: str | None) -> tuple[str | None, bool]:
        container = self._subscript_container_name(func_node.value)
        if container is None:
            return self._resolve_callee(
                func_node.value, current_class, current_func)
        key_map = self._dispatch.merged_map(container, current_class)
        if key_map is None:
            return None, False
        key_str = _dispatch_key(func_node.slice)
        if key_str is not None and key_str in key_map:
            return self._table_ref_target(key_map[key_str], current_class)
        if (isinstance(key_str, str)
                or (isinstance(key_str, _DispatchKey)
                    and key_str.kind == "constant")):
            return None, False
        if not key_map:
            return None, False
        primary = _first_dispatch_value(key_map)
        self._emit_subscript_fallback_edges(
            key_map, current_func, func_node, current_class, skip=primary)
        return self._table_ref_target(primary, current_class)
    @staticmethod
    def _subscript_container_name(value) -> str | None:
        if isinstance(value, ast.Name):
            return value.id
        if (isinstance(value, ast.Attribute)
                and isinstance(value.value, ast.Name)
                and value.value.id in SELF_CLS_NAMES):
            return f"{value.value.id}.{value.attr}"
        return None
    def _table_ref_target(self, value: str,
                          current_class: str | None) -> tuple[str, bool]:
        head, _dot, rest = value.partition(".")
        if rest and head in SELF_CLS_NAMES and current_class:
            return rest, True
        return value, False
    def _emit_subscript_fallback_edges(self, key_map, current_func,
                                       func_node, current_class, *,
                                       skip: str | None) -> None:
        caller = current_func or _qualify_module_member(
            self._module_name, _MODULE_SCOPE_NAME)
        for val in key_map.values():
            if val == skip:
                continue
            target, is_self = self._table_ref_target(val, current_class)
            if is_self and current_class:
                target, _target_file, is_external = self._resolve_call_target(
                    target, True, current_class)
                if is_external or target not in self.graph.functions:
                    continue
                val = target
            self._dict_edges.add_edge(
                val, caller, getattr(func_node, "lineno", 0))
    def _resolve_getattr_callee(self, func_node, current_class: str | None) -> str | None:
        if not self._is_builtin_name_call(func_node.func, "getattr"):
            return None
        if len(func_node.args) < 2:
            return None
        attr_name = _const_str(func_node.args[1])
        if attr_name is None:
            return None
        return self._lookup_typed_method(
            func_node.args[0], attr_name, current_class)
    def _resolve_import_module_callee(self, func_node) -> tuple[str, bool] | None:
        module_name = self._static_import_module_arg(func_node)
        if module_name is None:
            return None
        return _strip_pkg_root_nonempty(module_name, self._pkg_root), False
    def _resolve_dynamic_call_callee(self, func_node, current_class: str | None,
                                     current_func: str | None) -> tuple[str, bool] | None:
        if not isinstance(func_node, ast.Call):
            return None
        typed = self._resolve_getattr_callee(func_node, current_class)
        if typed is not None:
            return typed, False
        if self._is_partial_call(func_node) and func_node.args:
            return self._resolve_callee(func_node.args[0], current_class, current_func)
        return self._resolve_import_module_callee(func_node)
    def _is_partial_call(self, func_node: ast.Call) -> bool:
        callee_ref = func_node.func
        bound_name = (
            callee_ref.id if isinstance(callee_ref, ast.Name)
            else callee_ref.value.id
            if (isinstance(callee_ref, ast.Attribute)
                and isinstance(callee_ref.value, ast.Name))
            else None
        )
        if bound_name is None:
            return False
        if (bound_name in self._shadowed_names
                or (self._types.has_callable_binding(bound_name)
                    and self._types.callable_alias(bound_name) is None)
                or self._types.var_type(bound_name) is not None):
            return False
        dotted = dotted_name_of(callee_ref)
        return _qualify_type_name(
            dotted, self._aliases_for_name(bound_name)) == "functools.partial"
    def _receiver_has_project_method(self, func_node: ast.Attribute,
                                     current_class: str | None) -> bool:
        class_name = _qualify_type_name(
            self.resolve_declared_class(
                func_node.value, current_class),
            self._file_aliases, self._pkg_root)
        return bool(class_name) and class_or_bases_define_method(
            self.graph, class_name, func_node.attr)
    def _is_tracked_local_callable(self, callee_name: str) -> bool:
        if "." in callee_name:
            return False
        if (callee_name in SELF_CLS_NAMES
                and callee_name not in self._alias_target_names):
            return True
        return (self._types.is_tracked_callable(callee_name)
                or self._types.has_callable_binding(callee_name))
    def _track_dict_value_calls(self, value_node, caller: str,
                                current_class: str | None) -> None:
        if not isinstance(value_node, ast.Dict):
            return
        for _k, value in zip(value_node.keys, value_node.values, strict=True):
            self._walk_dict_value(value, caller, current_class, depth=0)
    def _walk_dict_value(self, value: ast.AST, caller: str,
                         current_class: str | None, depth: int) -> None:
        if depth > _MAX_DICT_VALUE_DEPTH:
            return
        nested = self._nested_dict_values(value)
        if nested is not None:
            for child in nested:
                self._walk_dict_value(child, caller, current_class, depth + 1)
            return
        callee_name = self._resolve_dict_value(value, current_class, caller)
        if callee_name is None:
            return
        self._dict_edges.add_edge(
            callee_name, caller, getattr(value, "lineno", 0))
    @staticmethod
    def _nested_dict_values(value: ast.AST) -> list[ast.AST] | None:
        if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
            return list(value.elts)
        return list(value.values) if isinstance(value, ast.Dict) else None
    def _resolve_dict_value(self, value_node: ast.AST,
                            current_class: str | None,
                            caller: str) -> str | None:
        if not isinstance(value_node, (ast.Name, ast.Attribute)):
            return None
        callee_name, is_self = self._resolve_callee(
            value_node, current_class, caller)
        if callee_name is None:
            return None
        if (isinstance(value_node, ast.Name)
                and self._is_tracked_local_callable(callee_name)):
            return None
        if is_self and current_class:
            target, _target_file, is_external = self._resolve_call_target(
                callee_name, True, current_class)
            if is_external or target not in self.graph.functions:
                return None
            return target
        return callee_name
_MAX_DICT_VALUE_DEPTH = 5
class _DispatchKey(NamedTuple):
    kind: str
    value: object
_DispatchKeyT = str | _DispatchKey
def _dispatch_key(node) -> _DispatchKeyT | None:
    if isinstance(node, ast.Name):
        return _DispatchKey("name", node.id)
    if not isinstance(node, ast.Constant) or node.value is ...:
        return None
    if isinstance(node.value, str):
        return node.value
    try:
        hash(node.value)
    except TypeError:
        return None
    return _DispatchKey("constant", node.value)
def _const_str(node) -> str | None:
    if not (isinstance(node, ast.Constant) and isinstance(node.value, str)):
        return None
    return node.value or None
def _first_dispatch_value(key_map: dict) -> str:
    first_key = min(key_map, key=lambda k: (type(k).__name__, repr(k)))
    return key_map[first_key]
def _qualify_type_name(type_name: str | None,
                       file_aliases: dict[str, str],
                       pkg_root: str = "") -> str | None:
    if not type_name:
        return type_name
    head, dot, rest = type_name.partition(".")
    mapped = (file_aliases.get(head, head) if file_aliases else head)
    if dot:
        mapped = f"{mapped}.{rest}"
    return strip_pkg_root(mapped, pkg_root) if pkg_root else mapped
def _graph_pkg_root(graph) -> str:
    return pkg_root_name(getattr(graph, 'project_root', '') or '')
def _strip_pkg_root_nonempty(name: str, pkg_root: str) -> str:
    stripped = strip_pkg_root(name, pkg_root)
    return stripped or name
def _file_alias_map(import_aliases: dict[str, dict[str, str]],
                    filepath: str) -> dict[str, str]:
    return import_aliases.get(filepath) or {}
def _graph_type_store(graph, attr: str) -> dict[str, str]:
    store = getattr(graph, attr, None)
    if isinstance(store, dict):
        return store
    store = {}
    try:
        setattr(graph, attr, store)
    except (AttributeError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f"_graph_type_store:{type(_e).__name__}")
    return store
def _import_module_name_arg(node: ast.Call):
    if node.args:
        return node.args[0]
    return next(
        (kw.value for kw in node.keywords if kw.arg == "name"), None)

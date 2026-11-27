from __future__ import annotations

import ast
import hashlib
import logging
import os
import threading
import weakref
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    TRY_NODE_TYPES,
    TYPE_ALIAS_NODES,
    definition_start_line,
    definition_time_exprs,
    iter_arg_nodes,
    iter_pattern_capture_names,
    iter_target_bindings,
    module_level_binding_names,
)
from jwsgj.diag_shared_source_core import (
    FRAME_BOUNDARY_NODES,
    SOURCE_READ_PARSE_ERRORS,
    bound_shared_cache,
    clear_guard_ast_cache,
    clear_shared_ast_cache,
    clear_shared_parse_cache,
    clear_source_parse_cache,
    coerce_ctx_tree,
    coerce_source_text,
    lru_get,
    lru_put,
    parse_cached,
    parse_py_file,
    read_source_with_fingerprint,
)
from jwsgj.diag_shared_source_scan import (
    clear_shared_tokenize_cache,
    release_scan_base_caches,
    release_tokenize_caches,
)
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC, CodeRegion
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
_TREE_NODES_INDEX: weakref.WeakKeyDictionary[ast.AST, bool] = (
    weakref.WeakKeyDictionary())
_TREE_NODES_LOCK = threading.Lock()
_TREE_NODES_ATTR = "_jwsgj_tree_nodes"
_TREE_NODES_INDEX_MAX = 1024
_SUBTREE_NODES_INDEX: weakref.WeakKeyDictionary[ast.AST, bool] = (
    weakref.WeakKeyDictionary())
_SUBTREE_NODES_ATTR = "_jwsgj_subtree_nodes"
_SUBTREE_NODES_INDEX_MAX = 8192
_SCOPE_BFS_INDEX: weakref.WeakKeyDictionary[ast.AST, bool] = (
    weakref.WeakKeyDictionary())
_SCOPE_BFS_ATTR = "_jwsgj_same_scope_bfs"
_SCOPE_BFS_INDEX_MAX = 8192
_SCOPE_DFS_INDEX: weakref.WeakKeyDictionary[ast.AST, bool] = (
    weakref.WeakKeyDictionary())
_SCOPE_DFS_ATTR = "_jwsgj_same_scope_dfs"
_SCOPE_DFS_INDEX_MAX = 8192
_PARENT_MAP_INDEX: weakref.WeakKeyDictionary[ast.AST, bool] = (
    weakref.WeakKeyDictionary())
_PARENT_MAP_ATTR = "_jwsgj_parent_map"
_PARENT_MAP_INDEX_MAX = 2048
_SCOPE_IMPORTS_INDEX: weakref.WeakKeyDictionary[ast.AST, bool] = (
    weakref.WeakKeyDictionary())
_SCOPE_IMPORTS_ATTR = "_jwsgj_scope_imports"
_SCOPE_IMPORTS_INDEX_MAX = 2048
_FILE_BOUND_NAMES_INDEX: weakref.WeakKeyDictionary[ast.AST, bool] = (
    weakref.WeakKeyDictionary())
_FILE_BOUND_NAMES_ATTR = "_jwsgj_file_bound_names"
_FILE_BOUND_NAMES_INDEX_MAX = 2048
_CONTAINERS_ATTR = "_jwsgj_region_containers"
_REGION_CONTAINERS_INDEX: weakref.WeakKeyDictionary[ast.AST, bool] = (
    weakref.WeakKeyDictionary())
_REGION_CONTAINERS_INDEX_MAX = 2048
def _iter_fast_children(node: ast.AST) -> Iterator[ast.AST]:
    try:
        _d = node.__dict__
    except AttributeError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_iter_fast_children:AttributeError')
        yield from _iter_reflective_children(node)
        return
    for _f in getattr(node, "_fields", ()):
        _v = _d.get(_f)
        if _v is None:
            continue
        yield from _iter_ast_values(_v)
def _iter_reflective_children(node: ast.AST) -> Iterator[ast.AST]:
    if not hasattr(node, "_fields"):
        logger.debug("_iter_fast_children 遇异构节点(无 __dict__/_fields，视无子): %s",
                   type(node).__name__)
        return
    logger.debug("_iter_fast_children 遇异构节点(降级反射遍历): %s", type(node).__name__)
    yield from ast.iter_child_nodes(node)
def _iter_ast_values(value) -> Iterator[ast.AST]:
    if isinstance(value, list):
        for _item in value:
            if isinstance(_item, ast.AST):
                yield _item
        return
    if isinstance(value, ast.AST):
        yield value
def _fast_bfs_list(root: ast.AST) -> list:
    out: list[ast.AST] = [root]
    head = 0
    while head < len(out):
        out.extend(_iter_fast_children(out[head]))
        head += 1
    return out
_TREE_NODES_CAP_MARGIN = 128
_TREE_NODES_INDEX_HARD_MAX = 8192
_TREE_NODES_INDEX_DEFAULT = _TREE_NODES_INDEX_MAX
def _tree_nodes_index_cap() -> int:
    if _TREE_NODES_INDEX_MAX != _TREE_NODES_INDEX_DEFAULT:
        return _TREE_NODES_INDEX_MAX
    _bc = bound_shared_cache()
    if _bc is None:
        return _TREE_NODES_INDEX_MAX
    try:
        _fc = getattr(_bc, "file_count", None)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='_tree_nodes_index_cap:file_count')
        return _TREE_NODES_INDEX_MAX
    if not isinstance(_fc, int) or _fc <= 0:
        return _TREE_NODES_INDEX_MAX
    return min(max(_TREE_NODES_INDEX_MAX, _fc + _TREE_NODES_CAP_MARGIN),
               _TREE_NODES_INDEX_HARD_MAX)
def tree_nodes(tree: ast.AST) -> list:
    return _cached_materialize(
        tree, _TREE_NODES_ATTR, _TREE_NODES_INDEX, _tree_nodes_index_cap,
        lambda: _fast_bfs_list(tree))
_MATERIALIZE_FAMILIES: tuple[tuple[weakref.WeakKeyDictionary, str], ...] = (
    (_TREE_NODES_INDEX, _TREE_NODES_ATTR),
    (_SUBTREE_NODES_INDEX, _SUBTREE_NODES_ATTR),
    (_SCOPE_BFS_INDEX, _SCOPE_BFS_ATTR),
    (_SCOPE_DFS_INDEX, _SCOPE_DFS_ATTR),
    (_PARENT_MAP_INDEX, _PARENT_MAP_ATTR),
    (_SCOPE_IMPORTS_INDEX, _SCOPE_IMPORTS_ATTR),
    (_FILE_BOUND_NAMES_INDEX, _FILE_BOUND_NAMES_ATTR),
    (_REGION_CONTAINERS_INDEX, _CONTAINERS_ATTR),
)
def release_tree_nodes_index() -> int:
    with _TREE_NODES_LOCK:
        return _release_tree_nodes_index_locked()
def _release_family_index_locked(index: weakref.WeakKeyDictionary,
                                 attr: str) -> int:
    n = len(index)
    for _nd in list(index.keys()):
        try:
            delattr(_nd, attr)
        except (AttributeError, TypeError) as _e:
            log_swallowed(__name__, _e,
                          context=f'_release_family_index_locked:{type(_e).__name__}')
    index.clear()
    return n
def _release_tree_nodes_index_locked() -> int:
    return sum(_release_family_index_locked(_idx, _attr)
               for _idx, _attr in _MATERIALIZE_FAMILIES)
_TREE_VIEW_LOCK = threading.Lock()
def cached_tree_view(cache, tree: ast.AST, builder):
    try:
        with _TREE_VIEW_LOCK:
            hit = cache.get(tree)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='cached_tree_view:read')
        hit = None
    if hit is not None:
        return hit
    built = builder(tree)
    try:
        with _TREE_VIEW_LOCK:
            cache[tree] = built
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='cached_tree_view:write')
    return built
def _cached_materialize(node: ast.AST, attr: str,
                        index: weakref.WeakKeyDictionary[ast.AST, bool],
                        index_max: int | Callable[[], int], build) -> list | dict:
    cached = getattr(node, attr, None)
    if cached is not None:
        return cached
    materialized = build()
    try:
        setattr(node, attr, materialized)
    except (AttributeError, TypeError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_cached_materialize:{type(_e).__name__}')
        return materialized
    max_entries = index_max() if callable(index_max) else index_max
    with _TREE_NODES_LOCK:
        if len(index) >= max_entries:
            _release_family_index_locked(index, attr)
        index[node] = True
    return materialized
def subtree_nodes(node: ast.AST) -> list:
    return _cached_materialize(node, _SUBTREE_NODES_ATTR, _SUBTREE_NODES_INDEX,
                               _SUBTREE_NODES_INDEX_MAX,
                               lambda: _fast_bfs_list(node))
def same_scope_bfs_nodes(node: ast.AST) -> list:
    def _build() -> list:
        out: list[ast.AST] = []
        queue = list(_iter_fast_children(node))
        i = 0
        while i < len(queue):
            child = queue[i]
            i += 1
            out.append(child)
            if isinstance(child, FRAME_BOUNDARY_NODES):
                continue
            queue.extend(_iter_fast_children(child))
        return out
    return _cached_materialize(node, _SCOPE_BFS_ATTR, _SCOPE_BFS_INDEX,
                               _SCOPE_BFS_INDEX_MAX, _build)
def same_scope_dfs_nodes(node: ast.AST) -> list:
    def _build() -> list:
        out: list[ast.AST] = []
        stack = list(_iter_fast_children(node))[::-1]
        while stack:
            cur = stack.pop()
            out.append(cur)
            if isinstance(cur, FRAME_BOUNDARY_NODES):
                continue
            stack.extend(reversed(list(_iter_fast_children(cur))))
        return out
    return _cached_materialize(node, _SCOPE_DFS_ATTR, _SCOPE_DFS_INDEX,
                               _SCOPE_DFS_INDEX_MAX, _build)
def iter_skip_nested_class(node: ast.AST):
    stack: list[ast.AST] = list(_iter_fast_children(node))[::-1]
    while stack:
        n = stack.pop()
        if isinstance(n, ast.ClassDef):
            continue
        yield n
        stack.extend(list(_iter_fast_children(n))[::-1])
def parent_map(tree: ast.AST) -> dict:
    def _build() -> dict:
        pm: dict[ast.AST, ast.AST] = {}
        _conflict: set[int] = set()
        for p in tree_nodes(tree):
            for c in _iter_fast_children(p):
                if id(c) in _conflict:
                    continue
                _prev = pm.get(c)
                if _prev is None:
                    pm[c] = p
                elif _prev is not p:
                    del pm[c]
                    _conflict.add(id(c))
        return pm
    return _cached_materialize(tree, _PARENT_MAP_ATTR, _PARENT_MAP_INDEX,
                               _PARENT_MAP_INDEX_MAX, _build)
def scope_import_tables(tree: ast.Module) -> dict:
    return _cached_materialize(tree, _SCOPE_IMPORTS_ATTR, _SCOPE_IMPORTS_INDEX,
                               _SCOPE_IMPORTS_INDEX_MAX,
                               lambda: _build_scope_import_tables(tree))
def _import_statement_bound_name(node: ast.Import | ast.ImportFrom,
                                 alias: ast.alias) -> str:
    if isinstance(node, ast.Import):
        return alias.asname or alias.name.split(".", 1)[0]
    if alias.name == "*":
        return ""
    return alias.asname or alias.name
def _import_binding_record(node: ast.Import | ast.ImportFrom,
                           alias: ast.alias) -> tuple[str, tuple | None]:
    bound = _import_statement_bound_name(node, alias)
    if not bound:
        return bound, None
    if isinstance(node, ast.Import):
        module_ref = alias.name if alias.asname else alias.name.split('.')[0]
        return bound, ('import', module_ref)
    src = "" if node.level else (node.module or "")
    return bound, ('from', src, alias.name)
def _outer_write_scope(scope: ast.AST,
                       parents: dict[ast.AST, ast.AST]) -> ast.AST | None:
    target = parents.get(scope)
    while isinstance(target, (ast.ClassDef, ast.ExceptHandler)):
        target = parents.get(target)
    return target

def _nonlocal_write_scope(
        scope: ast.AST, name: str, parents: dict[ast.AST, ast.AST],
        redirected: Callable[[ast.AST, str], bool]) -> ast.AST:
    target = _outer_write_scope(scope, parents)
    while target is not None and redirected(target, name):
        target = _outer_write_scope(target, parents)
    return target if target is not None else scope

def _declared_import_scope(scope: ast.AST, name: str,
                           parents: dict[ast.AST, ast.AST],
                           declarations: dict) -> ast.AST:
    kind = declarations.get(scope, {}).get(name)
    if kind is None:
        return scope
    if kind == "global":
        while scope in parents:
            scope = parents[scope]
        return scope
    return _nonlocal_write_scope(
        scope, name, parents,
        lambda candidate, symbol: symbol in declarations.get(candidate, {}))
def _build_scope_import_tables(tree: ast.Module) -> dict:
    tables: dict[ast.AST, dict[str, tuple]] = {}
    parents: dict[ast.AST, ast.AST] = {}
    declarations: dict[ast.AST, dict[str, str]] = {}
    imports: list[tuple[ast.Import | ast.ImportFrom, ast.alias, ast.AST]] = []
    stack: list[tuple[ast.AST, ast.AST]] = [
        (child, tree) for child in list(_iter_fast_children(tree))[::-1]]
    while stack:
        node, scope = stack.pop()
        child_scope = scope
        if isinstance(node, FRAME_BOUNDARY_NODES):
            child_scope = node
            parents[node] = scope
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            imports.extend((node, alias, scope) for alias in node.names)
            continue
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            kind = "global" if isinstance(node, ast.Global) else "nonlocal"
            declared = declarations.setdefault(scope, {})
            for name in node.names:
                declared[name] = kind
        for child in reversed(list(_iter_fast_children(node))):
            stack.append((child, child_scope))
    for node, alias, scope in imports:
        bound, record = _import_binding_record(node, alias)
        if record is None:
            continue
        target = _declared_import_scope(scope, bound, parents, declarations)
        tables.setdefault(target, {})[bound] = record
    return tables
_BINDING_INDEX: weakref.WeakKeyDictionary[ast.AST, tuple] = (
    weakref.WeakKeyDictionary())
_BINDING_INDEX_LOCK = threading.Lock()
def materialized_index(index: list | None) -> list | None:
    return list(index) if index is not None else None
def iter_nodes(tree: ast.AST | None, index: list | None) -> Iterator[ast.AST]:
    if index is not None:
        return iter(index)
    if tree is None:
        return iter(())
    return walk_nodes(tree)
def clear_module_binding_index() -> int:
    with _BINDING_INDEX_LOCK:
        n = len(_BINDING_INDEX)
        _BINDING_INDEX.clear()
        return n
def _register_import_alias(node: ast.Import, alias: ast.alias,
                           alias_map: dict) -> None:
    bound = _import_statement_bound_name(node, alias)
    if bound:
        alias_map.setdefault(alias.name, set()).add(bound)
def _collect_from_imports(node: ast.ImportFrom, from_imports: list) -> None:
    if node.level or not node.module:
        return
    for alias in node.names:
        bound = _import_statement_bound_name(node, alias)
        if bound:
            from_imports.append((node.module, alias.name, bound))
def _build_binding_index(tree: ast.AST) -> tuple[dict, list]:
    alias_map: dict = {}
    from_imports: list = []
    for node in tree_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                _register_import_alias(node, alias, alias_map)
        elif isinstance(node, ast.ImportFrom):
            _collect_from_imports(node, from_imports)
    return alias_map, from_imports
def _binding_index_of(tree: ast.AST) -> tuple[dict, list]:
    try:
        with _BINDING_INDEX_LOCK:
            _idx = _BINDING_INDEX.get(tree)
        if _idx is None:
            _idx = _build_binding_index(tree)
            with _BINDING_INDEX_LOCK:
                _BINDING_INDEX[tree] = _idx
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context='_binding_index_of:cache_rebuild')
        _idx = _build_binding_index(tree)
    return _idx
def _module_matches(imported: str, module: str) -> bool:
    return imported == module or imported.split('.', maxsplit=1)[0] == module
def collect_module_bindings_detailed(tree: ast.AST | None, module: str,
                                      members: tuple[str, ...]
                                      ) -> tuple[set, dict]:
    aliases = {module}
    from_origins: dict[str, str] = {}
    if tree is None:
        return aliases, from_origins
    _alias_map, _from_imports = _binding_index_of(tree)
    aliases.update(_alias_map.get(module, ()))
    aliases.update({
        _bound for _mod, _orig, _bound in _from_imports
        if f"{_mod}.{_orig}" == module})
    from_origins.update({
        _bound: _orig for _mod, _orig, _bound in _from_imports
        if _module_matches(_mod, module) and _orig in members})
    return aliases, from_origins
def collect_module_bindings(tree: ast.AST | None, module: str,
                             members: tuple[str, ...]) -> tuple[set, set]:
    aliases, from_origins = collect_module_bindings_detailed(
        tree, module, members)
    return aliases, set(from_origins)
def qualified_and_bare_call_targets_detailed(
        tree: ast.AST | None, module: str, members: tuple[str, ...]
) -> tuple[set, dict]:
    aliases, origins = collect_module_bindings_detailed(
        tree, module, members)
    targets = {f'{a}.{m}' for a in aliases for m in members} | set(origins)
    return targets, origins
def qualified_and_bare_call_targets(tree: ast.AST | None, module: str,
                                     members: tuple[str, ...]) -> set:
    return qualified_and_bare_call_targets_detailed(
        tree, module, members)[0]
def file_bound_names(tree: ast.Module) -> set:
    return _cached_materialize(tree, _FILE_BOUND_NAMES_ATTR, _FILE_BOUND_NAMES_INDEX,
                               _FILE_BOUND_NAMES_INDEX_MAX,
                               lambda: _build_file_bound_names(tree))
def _collect_target_names(targets) -> set:
    names: set = set()
    for tgt in targets:
        assign_target_names(tgt, names)
    return names
def _single_target_name(node: ast.AST) -> set:
    target = node.target
    return {target.id} if isinstance(target, ast.Name) else set()
def _annassign_bound_name(node: ast.AnnAssign) -> set:
    return _single_target_name(node) if node.value is not None else set()
def _declared_bound_name(node: ast.AST) -> set:
    name = getattr(node, 'name', getattr(node, 'arg', None))
    return {name} if isinstance(name, str) and name else set()
def _imported_bound_names(node: ast.Import | ast.ImportFrom) -> set:
    return {bound for alias in node.names
            if (bound := _import_statement_bound_name(node, alias))}
def _targets_bound_names(node: ast.AST) -> set:
    targets = getattr(node, 'targets', None)
    if targets is None:
        targets = [node.target]
    return _collect_target_names(targets)
def _optional_vars_bound_names(node: ast.withitem) -> set:
    return (_collect_target_names([node.optional_vars])
            if node.optional_vars is not None else set())
def _match_mapping_rest_bound_name(node: ast.MatchMapping) -> set:
    return {node.rest} if isinstance(node.rest, str) and node.rest else set()
def _comprehension_bound_names(node: ast.comprehension) -> set:
    return _collect_target_names([node.target])
def _type_alias_bound_name(node: ast.AST) -> set:
    target = getattr(node, "name", None)
    return {target.id} if isinstance(target, ast.Name) else set()
_TYPE_PARAM_NODE_TYPES = tuple(
    _t for _t in (getattr(ast, "TypeVar", None),
                  getattr(ast, "ParamSpec", None),
                  getattr(ast, "TypeVarTuple", None))
    if _t is not None)
_NODE_BOUND_NAME_HANDLERS = (
    ((ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.arg),
     _declared_bound_name),
    # ``del name`` 在 Python 作用域规则中是绑定操作（使名字在整个作用域视为
    # 局部绑定）：缺少该处理器时 scope_node_bound_names(Delete) 返回空集，
    # ``from os import getcwd; def f(): del getcwd; return getcwd`` 被误判为
    # 仍引用模块导入（diag_dependency_analyzer 不得不自行特判 Delete）。
    ((ast.Assign, ast.For, ast.AsyncFor, ast.Delete), _targets_bound_names),
    ((ast.AnnAssign,), _annassign_bound_name),
    ((ast.AugAssign, ast.NamedExpr), _single_target_name),
    ((ast.Import, ast.ImportFrom), _imported_bound_names),
    ((ast.withitem,), _optional_vars_bound_names),
    ((ast.ExceptHandler, ast.MatchAs, ast.MatchStar), _declared_bound_name),
    ((ast.MatchMapping,), _match_mapping_rest_bound_name),
    ((ast.comprehension,), _comprehension_bound_names),
    (TYPE_ALIAS_NODES, _type_alias_bound_name),
    (_TYPE_PARAM_NODE_TYPES, _declared_bound_name),
)
def scope_node_bound_names(node: ast.AST) -> set[str]:
    for node_types, handler in _NODE_BOUND_NAME_HANDLERS:
        if isinstance(node, node_types):
            return handler(node)
    return set()
def _build_file_bound_names(tree: ast.Module) -> set:
    bound: set = set()
    for node in tree_nodes(tree):
        if isinstance(node, ast.comprehension):
            continue
        bound |= scope_node_bound_names(node)
    return bound
_ORIG_AST_WALK = ast.walk
_MODULE_WALK_CACHE: weakref.WeakKeyDictionary[ast.AST, list] = (
    weakref.WeakKeyDictionary())
_MODULE_WALK_LOCK = threading.Lock()
_MEMO_WALK_SCOPE_LOCK = threading.RLock()
_MEMO_WALK_ROOT_TYPES = (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)
def _memoized_module_walk(node: ast.AST):
    if not isinstance(node, _MEMO_WALK_ROOT_TYPES):
        return _ORIG_AST_WALK(node)
    with _MODULE_WALK_LOCK:
        cached = _MODULE_WALK_CACHE.get(node)
    if cached is None:
        cached = tree_nodes(node)
        with _MODULE_WALK_LOCK:
            _MODULE_WALK_CACHE[node] = cached
    return iter(cached)
@contextmanager
def memoized_module_walk_scope() -> Iterator[None]:
    with _MEMO_WALK_SCOPE_LOCK:
        previous = ast.walk
        if previous is _memoized_module_walk:
            yield
            return
        ast.walk = _memoized_module_walk
        try:
            yield
        finally:
            ast.walk = previous
            with _MODULE_WALK_LOCK:
                _MODULE_WALK_CACHE.clear()
_SHARED_WALK_ROOTS = _MEMO_WALK_ROOT_TYPES
_SHARED_WALK_MEMO: dict[int, tuple] = {}
_SHARED_WALK_MEMO_MAX = 8192
def shared_walk(node: ast.AST) -> list[ast.AST] | Iterator[ast.AST]:
    if not isinstance(node, _SHARED_WALK_ROOTS):
        return walk_nodes(node)
    key = id(node)
    got = _SHARED_WALK_MEMO.get(key)
    if got is not None and got[0] is node:
        return got[1]
    nodes = _fast_bfs_list(node)
    if len(_SHARED_WALK_MEMO) >= _SHARED_WALK_MEMO_MAX:
        _SHARED_WALK_MEMO.clear()
    _SHARED_WALK_MEMO[key] = (node, nodes)
    return nodes
def clear_shared_walk() -> int:
    n = len(_SHARED_WALK_MEMO)
    _SHARED_WALK_MEMO.clear()
    return n
def clear_lexical_scope_memo() -> int:
    n = len(_LEXICAL_SCOPE_MEMO)
    _LEXICAL_SCOPE_MEMO.clear()
    return n
class WalkIndex:
    __slots__ = ("_memo", "_parent_memo")
    def __init__(self) -> None:
        self._memo: dict[int, tuple] = {}
        self._parent_memo: dict[int, tuple] = {}
    def walk(self, node: ast.AST) -> list[ast.AST]:
        if isinstance(node, _SHARED_WALK_ROOTS):
            return shared_walk(node)
        _key = id(node)
        _got = self._memo.get(_key)
        if _got is None or _got[0] is not node:
            _got = (node, list(walk_nodes(node)))
            self._memo[_key] = _got
        return _got[1]
    def parent_index(self, loop: ast.AST) -> dict[int, ast.AST]:
        _key = id(loop)
        _got = self._parent_memo.get(_key)
        if _got is None or _got[0] is not loop:
            _got = (loop, _parent_map(self.walk(loop)))
            self._parent_memo[_key] = _got
        return _got[1]
def _parent_map(nodes) -> dict[int, ast.AST]:
    parents: dict[int, ast.AST] = {}
    for n in nodes:
        for c in ast.iter_child_nodes(n):
            parents[id(c)] = n
    return parents
_CONTAINER_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
def _container_nodes(tree: ast.AST) -> list:
    return _cached_materialize(
        tree, _CONTAINERS_ATTR, _REGION_CONTAINERS_INDEX,
        _REGION_CONTAINERS_INDEX_MAX,
        lambda: [n for n in tree_nodes(tree)
                 if isinstance(n, _CONTAINER_TYPES) and hasattr(n, "lineno")])
def _node_span(node: Any) -> int:
    return ((getattr(node, "end_lineno", None) or node.lineno)
            - definition_start_line(node))
def _node_covers_line(node: Any, line: int) -> bool:
    return definition_start_line(node) <= line <= (
        getattr(node, "end_lineno", None) or node.lineno)
def _smallest_container_at(containers: list, line: int) -> Any:
    return min(
        (n for n in containers if _node_covers_line(n, line)),
        key=_node_span,
        default=None,
    )
def _single_line_region(filepath: str, line: int, node_type: str = "") -> CodeRegion:
    return CodeRegion(file=filepath, start_line=line, end_line=line,
                      node_type=node_type)
def _resolve_region_source(filepath: str, source: str | None,
                           source_cache: dict[str, Any] | None = None) -> str | None:
    if source is not None:
        return source
    if source_cache is not None and filepath in source_cache:
        return source_cache[filepath]
    try:
        resolved = None
        if os.path.isfile(filepath):
            resolved, _fingerprint = read_source_with_fingerprint(
                filepath, strict=True)
    except SOURCE_READ_PARSE_ERRORS:
        if source_cache is not None:
            source_cache[filepath] = None
        raise
    if source_cache is not None:
        source_cache[filepath] = resolved
    return resolved
def compute_code_region(filepath: str, line: int,
                        source: str | None = None, *,
                        source_cache: dict[str, Any] | None = None) -> CodeRegion:
    if not filepath or line <= 0:
        return _single_line_region(filepath or "", line)
    try:
        resolved = _resolve_region_source(filepath, source, source_cache)
        if resolved is None:
            return _single_line_region(filepath, line)
        tree = parse_cached(resolved, filepath)
        best_node = _smallest_container_at(_container_nodes(tree), line)
    except SOURCE_READ_PARSE_ERRORS as e:
        logger.warning("[Cache] 源文件解析失败，降级单行区域: %s (%s)",
                       filepath, e)
        return _single_line_region(filepath, line)
    if best_node is None:
        return _single_line_region(filepath, line, "Module")
    return CodeRegion(
        file=filepath,
        start_line=definition_start_line(best_node),
        end_line=best_node.end_lineno or best_node.lineno,
        node_type=type(best_node).__name__,
        node_name=best_node.name,
    )
def assign_target_names(target: ast.AST, out: set) -> None:
    for name, _line, _col in iter_target_bindings(target):
        out.add(name)
_NODE_KEY_RULES = (
    (TRY_NODE_TYPES, "try"),
    (ast.If, "if"),
    ((ast.For, ast.AsyncFor), "for"),
    (ast.While, "while"),
    ((ast.With, ast.AsyncWith), "with"),
    (ast.Call, "call"),
    (ast.ExceptHandler, "except"),
)
_PROFILE_KEYS = tuple(key for _types, key in _NODE_KEY_RULES)
_CALL_COUNT_CAP = 20
def _tree_from_ctx(filepath, get_ast):
    try:
        tree = get_ast(filepath)
    except (OSError, SyntaxError, ValueError, RuntimeError, KeyError,
            TypeError, AttributeError, MemoryError) as e:
        logger.warning("[WarnQ] ctx.get_ast 失败，AST 置空: %s (%s)", filepath, e)
        return None
    return coerce_ctx_tree(filepath, tree)
def _tree_from_disk(filepath, project_root):
    resolved = filepath
    if project_root and not os.path.isabs(filepath):
        resolved = os.path.join(project_root, filepath)
    return parse_py_file(resolved)[1]
def _get_structural_tree(filepath, tree_cache, diag_ctx=None, project_root=None):
    if filepath in tree_cache:
        return tree_cache[filepath]
    _ctx_get_ast = getattr(diag_ctx, "get_ast", None) if diag_ctx is not None else None
    if callable(_ctx_get_ast):
        tree = _tree_from_ctx(filepath, _ctx_get_ast)
    else:
        tree = _tree_from_disk(filepath, project_root)
    tree_cache[filepath] = tree
    return tree
def _stmt_profile_key(node):
    for types, key in _NODE_KEY_RULES:
        if isinstance(node, types):
            return key
    return None
def _build_file_func_profiles(tree):
    profiles = []
    _queue = [(tree, ())]
    _head = 0
    while _head < len(_queue):
        node, chain = _queue[_head]
        _head += 1
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            func_start = definition_start_line(node)
            func_end = getattr(node, 'end_lineno', None) or (func_start + 100)
            counts = dict.fromkeys(_PROFILE_KEYS, 0)
            profiles.append((node.name, func_start, func_end, counts))
            chain = chain + (counts,)
        _key = _stmt_profile_key(node)
        if _key is not None:
            for _c in chain:
                _c[_key] += 1
        for _child in ast.iter_child_nodes(node):
            _queue.append((_child, chain))
    return profiles
def _get_file_func_profiles(fpath, tree, profiles_cache):
    profiles = profiles_cache.get(fpath)
    if profiles is None:
        profiles = _build_file_func_profiles(tree)
        profiles_cache[fpath] = profiles
    return profiles
def _profile_signature(counts: dict) -> str:
    parts = []
    for key in _PROFILE_KEYS:
        value = counts[key]
        parts.append(f"{key}:{min(value, _CALL_COUNT_CAP) if key == 'call' else value}")
    return "|".join(parts)
def structural_fingerprint(fpath: str, line: int, btype: str,
                           tree_cache: dict, profiles_cache: dict,
                           diag_ctx=None, project_root=None):
    if not fpath:
        return None
    tree = _get_structural_tree(fpath, tree_cache, diag_ctx, project_root)
    if tree is None:
        return None
    best = None
    for profile in _get_file_func_profiles(fpath, tree, profiles_cache):
        func_start, func_end = profile[1], profile[2]
        if not (func_start <= line <= func_end):
            continue
        if best is None or func_start > best[1]:
            best = profile
    if best is None:
        context_parts = [f"file:{fpath}", f"type:{btype}"]
    else:
        context_parts = [f"file:{fpath}", best[0],
                         _profile_signature(best[3]), f"type:{btype}"]
    fp_str = "|".join(context_parts)
    return hashlib.md5(fp_str.encode('utf-8'), usedforsecurity=False).hexdigest()[:12]
_LEXICAL_SCOPE_TYPES = (ast.ExceptHandler, *COMP_SCOPE_NODES)
class LexicalScopeTable(NamedTuple):
    bound: dict[ast.AST, set[str]]
    parent: dict[ast.AST, ast.AST]
    open_calls: list[tuple[ast.Call, ast.AST]]
    shadow_bound: dict[ast.AST, set[str]]
    calls: list[tuple[ast.Call, ast.AST]]
    tree: ast.AST | None = None
def _absorb_scope_declarations(
        tree: ast.Module, bound: dict[ast.AST, set[str]],
        shadow_bound: dict[ast.AST, set[str]],
        parent: dict[ast.AST, ast.AST],
        declarations: dict[tuple[ast.AST, bool], set[str]]) -> None:
    for (scope, is_global), names in declarations.items():
        if scope is tree:
            continue
        local = bound.setdefault(scope, set())
        shadow_local = shadow_bound.setdefault(scope, set())
        for name in names:
            target = (tree if is_global else _nonlocal_write_scope(
                scope, name, parent,
                lambda candidate, symbol: (
                    symbol in declarations.get((candidate, False), ())
                    or symbol in declarations.get((candidate, True), ()))))
            if name in local:
                bound[target].add(name)
            if name in shadow_local:
                shadow_bound[target].add(name)
        local -= names
        shadow_local -= names
def definition_time_expressions(
        node: ast.AST, *, annotations_evaluated: bool = True) -> list[ast.AST]:
    exprs = definition_time_exprs(node)
    exprs.extend(getattr(node, "bases", ()) or ())
    exprs.extend(keyword.value for keyword in (getattr(node, "keywords", ()) or ()))
    for type_param in getattr(node, "type_params", None) or ():
        bound = getattr(type_param, "bound", None)
        if bound is not None:
            exprs.append(bound)
        default = getattr(type_param, "default_value", None)
        if default is None:
            default = getattr(type_param, "default", None)
        if default is not None:
            exprs.append(default)
    if annotations_evaluated:
        args = getattr(node, "args", None)
        if isinstance(args, ast.arguments):
            exprs.extend(
                arg.annotation for arg in iter_arg_nodes(args)
                if arg.annotation is not None)
        returns = getattr(node, "returns", None)
        if returns is not None:
            exprs.append(returns)
    return exprs
def _definition_header_nodes(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, ast.ClassDef):
        return [*node.decorator_list, *node.bases, *node.keywords,
                *getattr(node, "type_params", [])]
    params = iter_arg_nodes(node.args)
    returns = getattr(node, "returns", None)
    return [*getattr(node, "decorator_list", []),
            *(a.annotation for a in params if a.annotation is not None),
            *node.args.defaults,
            *(d for d in node.args.kw_defaults if d is not None),
            *([returns] if returns is not None else []),
            *getattr(node, "type_params", [])]
def _ordinary_binding_scope(scope: ast.AST, parent: dict[ast.AST, ast.AST],
                            named_expr: bool = False) -> ast.AST:
    while ((named_expr and isinstance(scope, COMP_SCOPE_NODES))
           or isinstance(scope, ast.ExceptHandler)):
        scope = parent[scope]
    return scope
def _push_def_scope(node: ast.AST, scope: ast.AST, maps: tuple[dict, dict, dict],
                    stack: list[tuple[ast.AST, ast.AST]]) -> None:
    bound, shadow_bound, parent = maps
    parent[node] = scope
    bound.setdefault(node, set())
    shadow_bound.setdefault(node, set())
    if not isinstance(node, ast.Lambda):
        enclosing = _ordinary_binding_scope(scope, parent)
        bound[enclosing].add(node.name)
        shadow_bound[enclosing].add(node.name)
    if not isinstance(node, ast.ClassDef):
        params = {a.arg for a in iter_arg_nodes(node.args)}
        bound[node].update(params)
        shadow_bound[node].update(params)
    type_params = list(getattr(node, "type_params", None) or [])
    stack.extend(
        (child, scope) for child in _definition_header_nodes(node)
        if not any(child is tp for tp in type_params))
    stack.extend((child, node) for child in type_params)
    body = node.body if isinstance(node.body, list) else [node.body]
    stack.extend((child, node) for child in body)
_LEXICAL_SCOPE_MEMO: dict[int, tuple] = {}
# 上限必须大于「同时活跃的 tree 数」，否则退化为抖动。
# 历史缺陷：上限 32 而全库 307 个模块，每次写入都触发**整体清空**，
# 于是每个模块都要重建一次词法作用域表（O(树节点数)），
# 这是 C 方法调用图构建的主要耗时源之一。
# 现在改真 LRU（淘汰最久未用项），工作集能常驻。
_LEXICAL_SCOPE_MEMO_MAX = 512
def collect_lexical_scope_table(tree: ast.Module) -> LexicalScopeTable:
    _key = id(tree)
    _got = lru_get(_LEXICAL_SCOPE_MEMO, _key)
    if _got is not None and _got[0] is tree:
        return _got[1]
    table = _build_lexical_scope_table(tree)
    lru_put(_LEXICAL_SCOPE_MEMO, _key, (tree, table),
            _LEXICAL_SCOPE_MEMO_MAX)
    return table
def _build_lexical_scope_table(tree: ast.Module) -> LexicalScopeTable:
    bound: dict[ast.AST, set[str]] = {tree: set()}
    shadow_bound: dict[ast.AST, set[str]] = {tree: set()}
    parent: dict[ast.AST, ast.AST] = {}
    open_calls: list[tuple[ast.Call, ast.AST]] = []
    calls: list[tuple[ast.Call, ast.AST]] = []
    declarations: dict[tuple[ast.AST, bool], set[str]] = {}
    outer_eval_scopes: dict[ast.AST, ast.AST] = {}
    maps = (bound, shadow_bound, parent)
    stack: list[tuple[ast.AST, ast.AST]] = [
        (child, tree) for child in ast.iter_child_nodes(tree)]
    while stack:
        node, scope = stack.pop()
        if isinstance(node, FRAME_BOUNDARY_NODES):
            _push_def_scope(node, scope, maps, stack)
            continue
        if isinstance(node, _LEXICAL_SCOPE_TYPES):
            parent[node] = scope
            bound.setdefault(node, set())
            shadow_bound.setdefault(node, set())
            if isinstance(node, ast.ExceptHandler) and isinstance(node.name, str):
                bound[node].add(node.name)
                shadow_bound[node].add(node.name)
            child_scope = node
        else:
            child_scope = scope
            binding_scope = _ordinary_binding_scope(
                scope, parent, isinstance(node, ast.NamedExpr))
            names = scope_node_bound_names(node)
            if (isinstance(node, ast.AnnAssign) and node.value is None
                    and isinstance(binding_scope, (
                        ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))):
                names |= _single_target_name(node)
            bound[binding_scope] |= names
            if not isinstance(node, (ast.Import, ast.ImportFrom)):
                shadow_bound[binding_scope] |= names
        if isinstance(node, (ast.Global, ast.Nonlocal)):
            declaration_scope = _ordinary_binding_scope(scope, parent)
            declarations.setdefault(
                (declaration_scope, isinstance(node, ast.Global)),
                set()).update(node.names)
        if isinstance(node, ast.Call):
            calls.append((node, scope))
            if isinstance(node.func, ast.Name) and node.func.id == "open":
                open_calls.append((node, scope))
        if isinstance(node, COMP_SCOPE_NODES) and node.generators:
            outer_eval_scopes[node.generators[0].iter] = scope
        if isinstance(node, ast.ExceptHandler) and node.type is not None:
            outer_eval_scopes[node.type] = scope
        stack.extend((child, outer_eval_scopes.get(child, child_scope))
                     for child in ast.iter_child_nodes(node))
    _absorb_scope_declarations(tree, bound, shadow_bound, parent, declarations)
    return LexicalScopeTable(
        bound, parent, open_calls, shadow_bound, calls, tree)
def scope_shadows_name(table: LexicalScopeTable, scope: ast.AST,
                        name: str) -> bool:
    direct = scope
    while scope is not None:
        if (not (isinstance(scope, ast.ClassDef) and scope is not direct)
                and name in table.bound.get(scope, frozenset())):
            return True
        scope = table.parent.get(scope)
    return False
def scope_shadows_import(table: LexicalScopeTable, scope: ast.AST,
                          name: str) -> bool:
    direct = scope
    while scope is not None:
        if (not (isinstance(scope, ast.ClassDef) and scope is not direct)
                and name in table.shadow_bound.get(scope, frozenset())):
            return True
        scope = table.parent.get(scope)
    return False
def call_scope_map(table: LexicalScopeTable) -> dict[int, ast.AST]:
    return {id(call): scope for call, scope in table.calls}
def call_head_is_shadowed(node: ast.Call, table: LexicalScopeTable,
                           scopes: dict[int, ast.AST]) -> bool:
    func = node.func
    if isinstance(func, ast.Name):
        name = func.id
    elif isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        name = func.value.id
    else:
        return False
    scope = scopes.get(id(node))
    return bool(scope is not None and scope_shadows_import(table, scope, name))
_OPEN_BINDING_AMBIGUOUS = object()
_OPEN_BINDING_DELETED = object()
_OPEN_LOCAL_FRAME_TYPES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ExceptHandler)
def _open_statement_binding_kind(node: ast.AST) -> str | None:
    if isinstance(node, ast.Import):
        for alias in node.names:
            if _import_statement_bound_name(node, alias) == "open":
                return "custom"
        return None
    if isinstance(node, ast.ImportFrom):
        for alias in node.names:
            if _import_statement_bound_name(node, alias) != "open":
                continue
            return ("family"
                    if not node.level and _open_family_module(node.module)
                    else "custom")
        return None
    if isinstance(node, ast.Delete):
        for target in node.targets:
            for child in walk_nodes(target):
                if (isinstance(child, ast.Name)
                        and isinstance(child.ctx, ast.Del)
                        and child.id == "open"):
                    return "custom"
        return None
    return "custom" if "open" in scope_node_bound_names(node) else None
def _open_statement_binding_parts(node: ast.AST) -> tuple[str | None, bool]:
    direct = _open_statement_binding_kind(node)
    nested = False
    for child in walk_nodes(node):
        if child is not node and _open_statement_binding_kind(child) is not None:
            nested = True
            break
    return direct, nested
def _scope_initial_open_binding(scope: ast.AST) -> str | None:
    args = getattr(scope, "args", None)
    if isinstance(args, ast.arguments):
        for parameter in iter_arg_nodes(args):
            if parameter.arg == "open":
                return "custom"
    if isinstance(scope, ast.ExceptHandler) and scope.name == "open":
        return "custom"
    for type_parameter in getattr(scope, "type_params", ()) or ():
        if (isinstance(type_parameter, _TYPE_PARAM_NODE_TYPES)
                and getattr(type_parameter, "name", None) == "open"):
            return "custom"
    return None
def _build_open_binding_prefixes(
        scope: ast.AST, delete_falls_through: bool = False) -> list | None:
    if not isinstance(scope, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef, ast.ExceptHandler)):
        return None
    body = getattr(scope, "body", None)
    if not isinstance(body, list):
        return None
    state = _scope_initial_open_binding(scope)
    prefixes: list[tuple[int, object, bool]] = []
    for statement in body:
        direct, nested = _open_statement_binding_parts(statement)
        prefixes.append((id(statement), state, direct is not None or nested))
        if nested:
            state = _OPEN_BINDING_AMBIGUOUS
        elif (isinstance(statement, ast.Delete)
              and (isinstance(scope, (ast.Module, ast.ClassDef))
                   or delete_falls_through)
              and direct == "custom"):
            state = _OPEN_BINDING_DELETED
        elif direct is not None:
            state = direct
    return prefixes
def _direct_statement_for_call(parents: dict, call: ast.AST,
                               scope: ast.AST) -> ast.AST | None:
    current = call
    while True:
        parent = parents.get(current)
        if parent is scope:
            return current
        if parent is None:
            return None
        current = parent
def _child_below_ancestor(
        node: ast.AST, ancestor: ast.AST, parents: dict) -> ast.AST | None:
    current = node
    while True:
        parent = parents.get(current)
        if parent is ancestor:
            return current
        if parent is None:
            return None
        current = parent
def _open_call_precedes_named_expr(
        call: ast.Call, binding: ast.NamedExpr, parents: dict) -> bool:
    if any(node is binding for node in walk_nodes(call)):
        return False
    if any(node is call for node in walk_nodes(binding.value)):
        return True
    binding_chain: set[ast.AST] = set()
    current: ast.AST | None = binding
    while current is not None:
        binding_chain.add(current)
        current = parents.get(current)
    current = call
    while current is not None:
        parent = parents.get(current)
        if parent is None:
            break
        if parent in binding_chain:
            after_child = _child_below_ancestor(binding, parent, parents)
            before_child = current
            if isinstance(parent, ast.IfExp):
                branches = (parent.body, parent.orelse)
                return bool(
                    (before_child is parent.test and after_child in branches)
                    or (before_child in branches and after_child in branches
                        and before_child is not after_child))
            if isinstance(parent, COMP_SCOPE_NODES):
                generators = parent.generators
                before_region = next(
                    (index for index, generator in enumerate(generators)
                     if before_child is generator), len(generators))
                after_region = next(
                    (index for index, generator in enumerate(generators)
                     if after_child is generator), len(generators))
                if before_region != after_region:
                    return before_region < after_region
            return (call.lineno, call.col_offset) < (
                binding.lineno, binding.col_offset)
        current = parent
    return False
def _open_call_precedes_statement_binding(
        call: ast.Call, statement: ast.AST, parents: dict) -> bool:
    if isinstance(statement, (ast.Expr, ast.Assign, ast.AnnAssign,
                              ast.AugAssign, ast.NamedExpr)):
        roots = [statement.value]
    elif isinstance(statement, (ast.For, ast.AsyncFor)):
        roots = [statement.iter]
    elif isinstance(statement, (ast.With, ast.AsyncWith)):
        roots = []
        for item in statement.items:
            direct, nested = _open_statement_binding_parts(item)
            if nested:
                break
            roots.append(item.context_expr)
            if direct is not None:
                break
    elif isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef)):
        roots = _definition_header_nodes(statement)
    else:
        return False
    bindings = [
        node for root in roots for node in walk_nodes(root)
        if (isinstance(node, ast.NamedExpr)
            and isinstance(node.target, ast.Name)
            and node.target.id == 'open')]
    if bindings:
        return all(_open_call_precedes_named_expr(call, binding, parents)
                   for binding in bindings)
    if isinstance(statement, ast.Expr):
        return False
    current = call
    while current is not None:
        if any(current is root for root in roots):
            return True
        current = parents.get(current)
    return False
def _open_scope_declares_global(table: LexicalScopeTable,
                                scope: ast.AST) -> bool:
    owner = _ordinary_binding_scope(scope, table.parent, named_expr=True)
    return any(isinstance(node, ast.Global) and 'open' in node.names
               for node in same_scope_bfs_nodes(owner))
def _ordered_open_shadowing(table: LexicalScopeTable, call: ast.Call,
                            scope: ast.AST, prefix_cache: dict,
                            at_statement_start: bool = False) -> bool | None:
    if table.tree is None or not isinstance(scope, (ast.Module, ast.FunctionDef,
                                                    ast.AsyncFunctionDef,
                                                    ast.ClassDef,
                                                    ast.ExceptHandler)):
        return None
    cached = prefix_cache.get(scope)
    if cached is None:
        global_open = _open_scope_declares_global(table, scope)
        prefixes = _build_open_binding_prefixes(scope, global_open)
        prefix_cache[scope] = (prefixes, global_open)
    else:
        prefixes, global_open = cached
    if prefixes is None:
        return None
    parents = parent_map(table.tree)
    statement = _direct_statement_for_call(parents, call, scope)
    if statement is None:
        return None
    for node_id, state, ambiguous in prefixes:
        if node_id != id(statement):
            continue
        if state is _OPEN_BINDING_AMBIGUOUS:
            return None
        if (not at_statement_start and ambiguous
                and not _open_call_precedes_statement_binding(
                    call, statement, parents)):
            return None
        if (isinstance(scope, ast.ClassDef)
                and (state is None
                     or (state is _OPEN_BINDING_DELETED and not global_open))):
            outer = table.parent.get(scope)
            if outer is not None:
                return _ordered_open_shadowing(
                    table, scope, outer, prefix_cache,
                    at_statement_start=True)
            return None
        if state is _OPEN_BINDING_DELETED:
            return False
        if state is not None:
            return state == "custom"
        if isinstance(scope, _OPEN_LOCAL_FRAME_TYPES):
            if "open" in table.bound.get(scope, set()):
                return True
            return None
        return False
    return None
def shadowed_open_call_ids(table: LexicalScopeTable) -> frozenset[int]:
    imports = scope_import_tables(table.tree) if table.tree is not None else {}
    prefix_cache: dict = {}
    shadowed: set[int] = set()
    for call, scope in table.open_calls:
        ordered = _ordered_open_shadowing(table, call, scope, prefix_cache)
        if ordered is not None:
            if ordered:
                shadowed.add(id(call))
            continue
        family_imported = _open_family_import_at_scope(table, imports, scope)
        if scope_shadows_import(table, scope, "open") or (
                not family_imported
                and scope_shadows_name(table, scope, "open")):
            shadowed.add(id(call))
    return frozenset(shadowed)
OPEN_FAMILY_MODULES = frozenset({
    "builtins", "bz2", "codecs", "gzip", "io", "lzma", "os", "tarfile",
    "tokenize", "zipfile",
})
def _open_family_module(dotted: str | None) -> str | None:
    if not dotted:
        return None
    top = dotted.split(".", maxsplit=1)[0]
    return top if top in OPEN_FAMILY_MODULES else None
def open_family_aliases(tree: ast.AST | None) -> dict[str, str]:
    if tree is None:
        return {}
    resolved: dict[str, tuple[int, int, str]] = {}
    for node in tree_nodes(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        module = _open_family_module(node.module)
        if node.level or module is None:
            continue
        position = (getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
        for alias in node.names:
            if alias.name != "open":
                continue
            bound = _import_statement_bound_name(node, alias)
            if not bound:
                continue
            previous = resolved.get(bound)
            if previous is None or position >= previous[:2]:
                resolved[bound] = (*position, module)
    return {name: module for name, (_line, _col, module) in resolved.items()}
def _open_family_import_at_scope(table: LexicalScopeTable,
                                 imports: dict, scope: ast.AST) -> bool:
    direct = scope
    while scope is not None:
        if not (isinstance(scope, ast.ClassDef) and scope is not direct):
            binding = imports.get(scope, {}).get("open")
            if binding is not None:
                return (binding[0] == "from"
                        and binding[1] in OPEN_FAMILY_MODULES)
        scope = table.parent.get(scope)
    return False
def non_builtin_open_call_ids(tree: ast.Module) -> frozenset[int]:
    return shadowed_open_call_ids(collect_lexical_scope_table(tree))
def collect_api_function_nodes(
        tree: ast.Module) -> list[tuple[ast.FunctionDef | ast.AsyncFunctionDef, bool]]:
    entries: list[tuple[ast.FunctionDef | ast.AsyncFunctionDef, bool]] = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            entries.append((node, False))
        elif isinstance(node, ast.ClassDef):
            entries.extend(
                (m, True) for m in ast.iter_child_nodes(node)
                if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))
            )
    return entries
def drain_frame_stack(root: ast.AST, step: Callable[..., None]) -> list:
    out: list = []
    stack: list[ast.AST] = [root]
    while stack:
        step(stack.pop(), stack, out)
    return out
_DEFAULT_RELEASE_KIND = "count"
_DEFAULT_RELEASE_SCOPE = "all"
_DEFAULT_RELEASE_ORDER = 100
class CacheReleaseHook(NamedTuple):
    key: str
    release_fn: Callable[..., Any]
    label: str
    kind: str = _DEFAULT_RELEASE_KIND
    scope: str = _DEFAULT_RELEASE_SCOPE
    order: int = _DEFAULT_RELEASE_ORDER
_CACHE_RELEASE_HOOKS: dict[str, CacheReleaseHook] = {}
def _release_hook_owner(release_fn: Callable[..., Any]) -> str:
    return getattr(release_fn, "__module__", "") or "<unknown>"
def register_cache_release(key: str, release_fn: Callable[..., Any], label: str,
                           *, kind: str = _DEFAULT_RELEASE_KIND,
                           scope: str = _DEFAULT_RELEASE_SCOPE,
                           order: int = _DEFAULT_RELEASE_ORDER) -> None:
    if kind not in ("count", "flag"):
        raise ValueError(f"未知释放回填口径: {kind!r}（只允许 count/flag）")
    if scope not in ("all", "project", "process"):
        raise ValueError(
            f"未知释放作用域: {scope!r}（只允许 all/project/process）")
    existing = _CACHE_RELEASE_HOOKS.get(key)
    if existing is not None:
        owner = _release_hook_owner(release_fn)
        previous_owner = _release_hook_owner(existing.release_fn)
        if owner != previous_owner:
            raise ValueError(
                f"释放钩子键冲突: {key!r} 已由 {previous_owner}（{existing.label}）"
                f"登记，{owner} 不得重复占用同一缓存域")
    _CACHE_RELEASE_HOOKS[key] = CacheReleaseHook(
        key=key, release_fn=release_fn, label=label,
        kind=kind, scope=scope, order=order)
def registered_cache_releases() -> tuple[CacheReleaseHook, ...]:
    return tuple(sorted(_CACHE_RELEASE_HOOKS.values(),
                        key=lambda _hook: (_hook.order, _hook.key)))
register_cache_release(
    "shared_ast", clear_shared_ast_cache, "盲点共享AST缓存",
    kind="flag", order=10)
register_cache_release(
    "shared_parse", clear_shared_parse_cache, "检测器共享解析缓存",
    kind="flag", order=20)
register_cache_release(
    "source_parse", clear_source_parse_cache, "sha1 键源码解析缓存", order=30)
register_cache_release(
    "guard_ast", clear_guard_ast_cache, "DirFileGuard 共享 AST 缓存", order=40)
register_cache_release(
    "e1_scan_base_caches", release_scan_base_caches, "E1 扫描底座行缓存",
    order=70)
register_cache_release(
    "sec_tree_nodes_index", release_tree_nodes_index, "共享节点表索引",
    order=120)
register_cache_release(
    "sec_tokenize_caches", release_tokenize_caches,
    "安全域 tokenize 投影缓存", order=130)
register_cache_release(
    "module_binding_index", clear_module_binding_index, "SE 导入绑定索引",
    order=140)
register_cache_release(
    "shared_walk_memo", clear_shared_walk, "共享遍历注册表", order=150)
register_cache_release(
    "lexical_scope_memo", clear_lexical_scope_memo, "词法作用域表 memo",
    order=155)
register_cache_release(
    "shared_tokenize_cache", clear_shared_tokenize_cache, "共享 tokenize 缓存",
    kind="flag", order=160)
class ImportFacts(NamedTuple):
    modules: dict[str, tuple[str, ...]]
    members: dict[str, tuple[str, ...]]
    shadowed: set[str]
def _record_import_facts(modules: dict[str, list[str]],
                         node: ast.Import) -> None:
    for alias in node.names:
        if alias.asname:
            modules.setdefault(alias.asname, []).append(alias.name)
            continue
        top = alias.name.split(".", 1)[0]
        paths = modules.setdefault(top, [])
        paths.append(top)
        if alias.name != top:
            paths.append(alias.name)
def _record_import_from_facts(modules: dict[str, list[str]],
                              members: dict[str, list[str]],
                              node: ast.ImportFrom,
                              module_roots: frozenset[str] | set[str]) -> None:
    if node.level or not node.module:
        return
    for alias in node.names:
        if alias.name == "*":
            continue
        local = alias.asname or alias.name
        canonical = f"{node.module}.{alias.name}"
        members.setdefault(local, []).append(canonical)
        if canonical in module_roots:
            modules.setdefault(local, []).append(canonical)
def import_facts(tree: ast.AST, *,
                 module_roots: frozenset[str] | set[str] = frozenset()) -> ImportFacts:
    modules: dict[str, list[str]] = {}
    members: dict[str, list[str]] = {}
    for node in tree_nodes(tree):
        if isinstance(node, ast.Import):
            _record_import_facts(modules, node)
        elif isinstance(node, ast.ImportFrom):
            _record_import_from_facts(modules, members, node, module_roots)
    shadowed = (module_level_binding_names(tree)
                if isinstance(tree, ast.Module) else set())
    return ImportFacts(
        modules=dict(zip(modules, map(tuple, modules.values()), strict=True)),
        members=dict(zip(members, map(tuple, members.values()), strict=True)),
        shadowed=shadowed,
    )
_MATCH_TYPE: Any = getattr(ast, "Match", None)
_LOOP_OR_IF_STMTS: tuple = (ast.If, ast.For, ast.AsyncFor, ast.While)
_BLOCK_STMTS: tuple = (_LOOP_OR_IF_STMTS + (ast.With, ast.AsyncWith)
                       + tuple(TRY_NODE_TYPES))
_DEF_STMTS: tuple = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_STMT_SCAN_RULES: tuple = (
    (_DEF_STMTS, "_scan_def_like"),
    ((ast.Assign, ast.AnnAssign, ast.AugAssign), "_scan_assign_like"),
    ((ast.For, ast.AsyncFor), "_scan_for_like"),
    ((ast.With, ast.AsyncWith), "_scan_with_like"),
    ((ast.If, ast.While), "_scan_if_while"),
    (TRY_NODE_TYPES, "_scan_try_like"),
    ((ast.Import, ast.ImportFrom), "_scan_import_like"),
    ((ast.Delete,), "_scan_delete_like"),
)
if _MATCH_TYPE is not None:
    _STMT_SCAN_RULES += ((_MATCH_TYPE, "_scan_match_like"),)
class _CPGNode:
    __slots__ = ('ast_node', 'id', 'lineno', 'type')
    def __init__(self, node_id, ast_node):
        self.id = node_id
        self.type = type(ast_node).__name__
        self.ast_node = ast_node
        self.lineno = getattr(ast_node, 'lineno', 0)
class _CPGEdge:
    __slots__ = ('edge_type', 'source_id', 'target_id')
    def __init__(self, source_id, target_id, edge_type):
        self.source_id = source_id
        self.target_id = target_id
        self.edge_type = edge_type
class _SimpleCPG:
    def __init__(self, filepath: str = _DEFAULT_FILEPATH):
        self.nodes = {}
        self.edges = []
        self.filepath = filepath
        self._next_id = 0
    def add_node(self, ast_node):
        nid = self._next_id
        self._next_id += 1
        node = _CPGNode(nid, ast_node)
        self.nodes[nid] = node
        return nid
    def add_edge(self, src_id: int, tgt_id: int, edge_type: str) -> None:
        self.edges.append(_CPGEdge(src_id, tgt_id, edge_type))
class _CPGBuilder:
    def __init__(self, node_limit: int, filepath: str = _DEFAULT_FILEPATH) -> None:
        self.node_limit = node_limit
        self.cpg = _SimpleCPG(filepath)
        self.node_ids: dict = {}
        self.exceeded = False
    def _nid(self, node):
        if self.exceeded:
            return None
        nid = self.node_ids.get(id(node))
        if nid is None:
            nid = self.cpg.add_node(node)
            self.node_ids[id(node)] = nid
            if len(self.cpg.nodes) > self.node_limit:
                self.exceeded = True
                return None
        return nid
    def _walk(self, node):
        if self.exceeded:
            return
        pid = self._nid(node)
        if pid is None:
            return
        for child in ast.iter_child_nodes(node):
            cid = self._nid(child)
            if cid is not None:
                self.cpg.add_edge(pid, cid, "AST_PARENT")
            self._walk(child)
    def _link(self, stmts):
        prev = None
        for stmt in stmts:
            cur = self._nid(stmt)
            if cur is None:
                return
            if prev is not None:
                self.cpg.add_edge(prev, cur, "CONTROL_FLOW")
            prev = cur
            self._flow_stmt(stmt)
    def _flow_match(self, stmt) -> None:
        for case in stmt.cases:
            self._link(case.body)
    def _flow_try(self, stmt) -> None:
        self._link(stmt.orelse)
        for handler in stmt.handlers:
            self._link(handler.body)
        self._link(stmt.finalbody)
    def _flow_stmt(self, stmt):
        if isinstance(stmt, _DEF_STMTS):
            self._link(stmt.body)
            return
        if _MATCH_TYPE is not None and isinstance(stmt, _MATCH_TYPE):
            self._flow_match(stmt)
            return
        if not isinstance(stmt, _BLOCK_STMTS):
            return
        self._link(stmt.body)
        if isinstance(stmt, _LOOP_OR_IF_STMTS):
            self._link(stmt.orelse)
            return
        if isinstance(stmt, TRY_NODE_TYPES):
            self._flow_try(stmt)
    @staticmethod
    def _definition_ids(value: Any) -> tuple[int, ...]:
        if value is None:
            return ()
        if isinstance(value, frozenset):
            return tuple(sorted(item for item in value if item is not None))
        return (value,)
    def _link_data_dep(self, name_node: Any, defined: dict) -> None:
        sources = self._definition_ids(defined.get(name_node.id))
        if not sources:
            return
        tgt = self._nid(name_node)
        if tgt is None:
            return
        for src in sources:
            if src != tgt:
                self.cpg.add_edge(src, tgt, "DATA_DEP")
    def _scan_uses(self, stmt, defined: dict,
                   named_expr_target: dict | None = None) -> None:
        for node in self._iter_own_nodes(stmt):
            if isinstance(node, COMP_SCOPE_NODES):
                self._scan_comprehension(
                    node, defined,
                    named_expr_target if named_expr_target is not None else defined)
                continue
            if isinstance(node, ast.NamedExpr):
                self._scan_uses(node.value, defined, named_expr_target)
                sid = self._nid(node)
                if sid is None:
                    continue
                for name in self._collect_stores(node.target):
                    defined[name] = sid
                    if (named_expr_target is not None
                            and named_expr_target is not defined):
                        named_expr_target[name] = sid
                continue
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
                self._link_data_dep(node, defined)
    def _scan_comprehension(self, node, defined: dict,
                            named_expr_target: dict) -> None:
        local = dict(defined)
        sid = self._nid(node)
        for generator in node.generators:
            self._scan_uses(generator.iter, local, named_expr_target)
            self._scan_uses(generator.target, local, named_expr_target)
            for name in self._collect_stores(generator.target):
                local[name] = sid
            for condition in generator.ifs:
                self._scan_uses(condition, local, named_expr_target)
        result_exprs = ((node.key, node.value)
                        if isinstance(node, ast.DictComp) else (node.elt,))
        for expr in result_exprs:
            self._scan_uses(expr, local, named_expr_target)
    @staticmethod
    def _bind_name(name: Any, defined: dict, sid) -> None:
        if name:
            defined[name] = sid
    def _bind_pattern_names(self, pattern, defined: dict, sid) -> None:
        if pattern is None:
            return
        for name in iter_pattern_capture_names(pattern):
            self._bind_name(name, defined, sid)
    def _scan_assign_like(self, stmt, defined: dict) -> None:
        sid = self._nid(stmt)
        if isinstance(stmt, ast.AugAssign) and isinstance(stmt.target, ast.Name):
            previous = self._definition_ids(defined.get(stmt.target.id))
            if sid is not None:
                for prev in previous:
                    if prev != sid:
                        self.cpg.add_edge(prev, sid, "DATA_DEP")
        if (isinstance(stmt, (ast.Assign, ast.AnnAssign))
                and stmt.value is not None):
            self._scan_uses(stmt.value, defined)
            targets = (stmt.targets if isinstance(stmt, ast.Assign)
                       else [stmt.target, stmt.annotation])
            for target in targets:
                self._scan_uses(target, defined)
        else:
            self._scan_uses(stmt, defined)
        for name in self._assign_targets(stmt):
            defined[name] = sid
    def _scan_for_like(self, stmt, defined: dict) -> None:
        sid = self._nid(stmt)
        for expr in self._head_exprs(stmt):
            self._scan_uses(expr, defined)
        base = dict(defined)
        body_defined = dict(base)
        self._scan_uses(stmt.target, body_defined)
        for name in self._collect_stores(stmt.target):
            body_defined[name] = sid
        self._scan_bodies(stmt.body, body_defined)
        self._merge_branch_definitions(defined, base, [base, body_defined])
        self._scan_bodies(stmt.orelse, defined)
    def _scan_with_like(self, stmt, defined: dict) -> None:
        sid = self._nid(stmt)
        for item in stmt.items:
            self._scan_uses(item.context_expr, defined)
            if item.optional_vars is not None:
                self._scan_uses(item.optional_vars, defined)
                for name in self._collect_stores(item.optional_vars):
                    defined[name] = sid
        self._scan_bodies(stmt.body, defined)
    @staticmethod
    def _merge_possible_definitions(defined: dict,
                                    endpoints: list[dict]) -> None:
        names = set().union(*(branch.keys() for branch in endpoints))
        merged = {
            name: frozenset(
                source
                for branch in endpoints
                for source in _CPGBuilder._definition_ids(branch.get(name)))
            for name in sorted(names)
        }
        defined.clear()
        defined.update(merged)
    @staticmethod
    def _merge_branch_definitions(defined: dict, base: dict,
                                  branches: list[dict]) -> None:
        if not branches:
            defined.clear()
            defined.update(base)
            return
        _CPGBuilder._merge_possible_definitions(defined, branches)
    def _scan_if_while(self, stmt, defined: dict) -> None:
        for expr in self._head_exprs(stmt):
            self._scan_uses(expr, defined)
        if isinstance(stmt, ast.While):
            base = dict(defined)
            body_defined = dict(base)
            self._scan_bodies(stmt.body, body_defined)
            self._merge_branch_definitions(defined, base, [base, body_defined])
            self._scan_bodies(stmt.orelse, defined)
            return
        base = dict(defined)
        body_defined = dict(base)
        self._scan_bodies(stmt.body, body_defined)
        else_defined = dict(base)
        self._scan_bodies(stmt.orelse, else_defined)
        self._merge_branch_definitions(
            defined, base, [body_defined, else_defined])
    def _scan_try_like(self, stmt, defined: dict) -> None:
        sid = self._nid(stmt)
        base = dict(defined)
        body_defined = dict(base)
        self._scan_bodies(stmt.body, body_defined)
        normal_defined = dict(body_defined)
        self._scan_bodies(stmt.orelse, normal_defined)
        if stmt.handlers:
            handler_base = dict(base)
            self._merge_possible_definitions(
                handler_base, [base, body_defined])
            branches = [normal_defined]
            for handler in stmt.handlers:
                branch = dict(handler_base)
                if handler.type is not None:
                    self._scan_uses(handler.type, branch)
                if handler.name:
                    branch[handler.name] = sid
                self._scan_bodies(handler.body, branch)
                if handler.name:
                    branch.pop(handler.name, None)
                branches.append(branch)
            self._merge_branch_definitions(defined, base, branches)
        else:
            defined.clear()
            defined.update(normal_defined)
        self._scan_bodies(stmt.finalbody, defined)
    def _scan_def_like(self, stmt, defined: dict) -> None:
        sid = self._nid(stmt)
        self._scan_uses(stmt, defined)
        self._bind_name(stmt.name, defined, sid)
    def _scan_import_like(self, stmt, defined: dict) -> None:
        sid = self._nid(stmt)
        for alias in stmt.names:
            bound = _import_statement_bound_name(stmt, alias)
            if bound:
                defined[bound] = sid
    def _scan_delete_like(self, stmt, defined: dict) -> None:
        self._scan_uses(stmt, defined)
        for target in stmt.targets:
            for n in walk_nodes(target):
                if (isinstance(n, ast.Name)
                        and isinstance(n.ctx, ast.Del)):
                    defined.pop(n.id, None)
    @staticmethod
    def _pattern_always_matches(pattern: ast.AST) -> bool:
        if isinstance(pattern, ast.MatchAs):
            return (pattern.pattern is None or
                    _CPGBuilder._pattern_always_matches(pattern.pattern))
        if isinstance(pattern, ast.MatchOr):
            return any(_CPGBuilder._pattern_always_matches(sub)
                       for sub in pattern.patterns)
        return False
    def _scan_match_like(self, stmt, defined: dict) -> None:
        sid = self._nid(stmt)
        self._scan_uses(stmt.subject, defined)
        base = dict(defined)
        branches: list[dict] = []
        for case in stmt.cases:
            branch = dict(base)
            self._scan_uses(case.pattern, branch)
            self._bind_pattern_names(case.pattern, branch, sid)
            if case.guard is not None:
                self._scan_uses(case.guard, branch)
            self._scan_bodies(case.body, branch)
            branches.append(branch)
        has_fallthrough = not any(
            case.guard is None and self._pattern_always_matches(case.pattern)
            for case in stmt.cases)
        if has_fallthrough:
            branches.append(dict(base))
        self._merge_branch_definitions(defined, base, branches)
    def _scan_stmt(self, stmt, defined: dict) -> None:
        if self.exceeded:
            return
        for _types, _handler in _STMT_SCAN_RULES:
            if isinstance(stmt, _types):
                getattr(self, _handler)(stmt, defined)
                return
        self._scan_uses(stmt, defined)
    def _scan_bodies(self, stmts, defined: dict) -> None:
        for sub in stmts:
            self._scan_stmt(sub, defined)
    def _scan_block(self, stmts, defined: dict | None = None):
        if defined is None:
            defined = {}
        for stmt in stmts:
            self._scan_stmt(stmt, defined)
    def _parameter_definitions(self, node) -> dict:
        # 形参是函数体作用域内的定义：以各自 ast.arg 节点为定义源，否则
        # ``def f(a, b): return a + b`` 中 a/b 的使用没有任何数据依赖边。
        args = getattr(node, "args", None)
        if args is None:
            return {}
        defined: dict = {}
        for arg in iter_arg_nodes(args):
            arg_id = self._nid(arg)
            if arg_id is not None:
                defined[arg.arg] = arg_id
        return defined
    def _build_phases(self, tree):
        self._walk(tree)
        self._link(tree.body)
        self._scan_block(tree.body)
        for node in walk_nodes(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef)):
                self._scan_block(node.body, self._parameter_definitions(node))
            elif isinstance(node, ast.Lambda):
                self._scan_block([node.body], self._parameter_definitions(node))
    @staticmethod
    def _collect_stores(target):
        names: set = set()
        assign_target_names(target, names)
        return list(names)
    @staticmethod
    def _assign_targets(stmt):
        if isinstance(stmt, ast.Assign):
            return [n for t in stmt.targets for n in _CPGBuilder._collect_stores(t)]
        if isinstance(stmt, ast.AnnAssign) and stmt.value is None:
            return []
        return _CPGBuilder._collect_stores(stmt.target)
    @staticmethod
    def _iter_own_nodes(root):
        _stack = [root]
        while _stack:
            _cur = _stack.pop()
            if isinstance(_cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef, ast.Lambda)):
                _stack.extend(reversed(definition_time_expressions(_cur)))
                continue
            if isinstance(_cur, (COMP_SCOPE_NODES, ast.NamedExpr)):
                yield _cur
                continue
            yield _cur
            _stack.extend(reversed(list(ast.iter_child_nodes(_cur))))
    @staticmethod
    def _head_exprs(stmt):
        if isinstance(stmt, (ast.For, ast.AsyncFor)):
            return [stmt.iter]
        if isinstance(stmt, (ast.If, ast.While)):
            return [stmt.test]
        return []
    def build(self, tree) -> Any:
        try:
            self._build_phases(tree)
        except RecursionError:
            logger.warning("CPGEngine.build_cpg: 建图递归超限（源码嵌套过深），放弃建图", exc_info=True)
            return None
        if self.exceeded:
            logger.warning("CPGEngine.build_cpg: 节点数超过 %d，放弃建图", self.node_limit)
            return None
        return self.cpg
class CPGEngine:
    NODE_LIMIT: ClassVar[int] = 50000
    def build_cpg(self, code: Any, filepath: str = _DEFAULT_FILEPATH) -> Any:
        try:
            tree = ast.parse(coerce_source_text(code))
        except PARSE_DEGRADE_EXC as exc:
            logger.debug("CPGEngine.build_cpg: 源码解析失败，放弃建图: %s", exc)
            return None
        return _CPGBuilder(self.NODE_LIMIT, filepath).build(tree)
def tree_unparse_cache(tree: ast.AST) -> dict[int, str]:
    cache = getattr(tree, "_jwsgj_unparse_cache", None)
    if cache is None:
        cache = {}
        try:
            tree._jwsgj_unparse_cache = cache
        except (AttributeError, TypeError) as e:
            logger.debug("[ASTViews] 缓存挂载失败: %s", e)
    return cache
def unparse_cached(tree: ast.AST, node: ast.AST, cache: dict[int, str] | None = None) -> str:
    if cache is None:
        cache = tree_unparse_cache(tree)
    key = id(node)
    if key in cache:
        return cache[key]
    try:
        src = ast.unparse(node)
    except Exception as e:  # noqa: BLE001
        logger.warning("[ASTViews] 节点反解析失败，降级为空源码: %s", e)
        src = ''
    cache[key] = src
    return src
def unparse_or_type_name(node: ast.AST) -> str:
    if isinstance(node, ast.Constant):
        return repr(node.value)
    try:
        return ast.unparse(node)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context='unparse_or_type_name:ast.unparse')
        return type(node).__name__
__all__ = [
    "OPEN_FAMILY_MODULES",
    "CPGEngine",
    "CacheReleaseHook",
    "ImportFacts",
    "LexicalScopeTable",
    "WalkIndex",
    "assign_target_names",
    "cached_tree_view",
    "call_head_is_shadowed",
    "call_scope_map",
    "clear_lexical_scope_memo",
    "clear_module_binding_index",
    "clear_shared_walk",
    "collect_api_function_nodes",
    "collect_lexical_scope_table",
    "collect_module_bindings",
    "collect_module_bindings_detailed",
    "compute_code_region",
    "definition_time_expressions",
    "drain_frame_stack",
    "file_bound_names",
    "import_facts",
    "iter_nodes",
    "iter_skip_nested_class",
    "iter_target_bindings",
    "materialized_index",
    "memoized_module_walk_scope",
    "non_builtin_open_call_ids",
    "open_family_aliases",
    "parent_map",
    "qualified_and_bare_call_targets",
    "qualified_and_bare_call_targets_detailed",
    "register_cache_release",
    "registered_cache_releases",
    "release_tree_nodes_index",
    "same_scope_bfs_nodes",
    "same_scope_dfs_nodes",
    "scope_import_tables",
    "scope_node_bound_names",
    "scope_shadows_import",
    "scope_shadows_name",
    "shadowed_open_call_ids",
    "shared_walk",
    "structural_fingerprint",
    "subtree_nodes",
    "tree_nodes",
    "tree_unparse_cache",
    "unparse_cached",
    "unparse_or_type_name",
]
logger.info(
    "diag_shared_ast_views L0 AST 派生视图域（索引物化/绑定表/代码区间/作用域账本/包形态/结构指纹）已加载: %d 项导出",
    len(__all__))

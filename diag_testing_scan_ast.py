from __future__ import annotations

import ast
import io
import logging
import os
import re
import time
import tokenize
from bisect import bisect_right
from collections import defaultdict
from collections.abc import Callable
from dataclasses import dataclass, field, replace

from jwsgj.diag_se_data import (
    CREDENTIAL_KEYWORDS,
    _se03_pairs_for_target,
    is_placeholder_secret,
)
from jwsgj.diag_shared_ast_nodes import (
    assign_targets_value,
    ast_name,
    collect_param_names,
    is_none_literal,
    iter_own_scope,
    iter_unpack_target_names,
    loop_body_has_break,
    main_guard_branch,
    main_guard_node_ids,
)
from jwsgj.diag_shared_ast_views import (
    definition_time_expressions,
    shared_walk,
)
from jwsgj.diag_shared_source_core import (
    is_regex_pattern_text,
    is_rule_name_constant,
)
from jwsgj.diag_shared_source_scan import (
    has_inline_suppression,
    is_suppressed,
    line_has_applicable_nosec,
    parse_suppressions,
)
from jwsgj.diag_testing_source import (
    collect_scope_binding_names,
    entry_nodes,
    import_binding_names,
    iter_direct_scope_nodes,
    nodes_where,
    resolve_file_cache,
)
from jwsgj.diag_types_defs import (
    TestMethodResult,
    finalize_test_result,
    graded_status_score,
    severity_tally,
)
from jwsgj.diag_types_vocab import YAML_SAFE_LOADERS
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import is_test_file_path

__all__ = [
    "ImportBinds",
    "ScopeIndex",
    "match_hardcoded_secret",
    "run_fuzz_tests",
    "run_security_tests",
]
_log = logging.getLogger(__name__)
_log.addHandler(logging.NullHandler())
_log.info("diag_testing_scan_ast 已加载：%d 项导出", len(__all__))
def _module_alias_names_from_nodes(nodes, *module_names: str) -> list[set]:
    if not module_names:
        raise ValueError(
            "_module_alias_names requires at least one module name")
    names = [set() for _ in module_names]
    slot = {m: i for i, m in enumerate(module_names)}
    for node in nodes:
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            idx = slot.get(alias.name)
            if idx is not None:
                names[idx].add(alias.asname or alias.name)
                continue
            for _idx, _module in enumerate(module_names):
                if alias.name.startswith(f"{_module}."):
                    if not alias.asname:
                        names[_idx].add(_module)
                    break
    return names
def _from_import_symbol_binds_from_nodes(nodes) -> dict[str, tuple[str, str]]:
    binds: dict[str, tuple[str, str]] = {}
    for _imp in nodes:
        if isinstance(_imp, ast.ImportFrom) and _imp.module and not _imp.level:
            for _alias in _imp.names:
                if _alias.name == '*':
                    for _sym in _STAR_IMPORT_SYMBOLS.get(_imp.module, ()):
                        binds[_sym] = (_imp.module, _sym)
                else:
                    binds[_alias.asname or _alias.name] = (_imp.module, _alias.name)
    return binds
def _from_import_bind_syms_from_nodes(nodes, module: str,
                                     symbols) -> dict[str, str]:
    return {_n: _sym
            for _n, (_mod, _sym)
            in _from_import_symbol_binds_from_nodes(nodes).items()
            if _mod == module and _sym in symbols}
def _os_path_names_from_nodes(nodes) -> set[str]:
    names: set[str] = set()
    for node in nodes:
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == 'os.path' and alias.asname:
                    names.add(alias.asname)
        elif (isinstance(node, ast.ImportFrom) and not node.level
              and node.module == 'os'):
            for alias in node.names:
                if alias.name == 'path':
                    names.add(alias.asname or alias.name)
    return names
def _filter_overridden_imports(nodes) -> list[ast.AST]:
    node_list = list(nodes)
    latest: dict[str, tuple[int, int]] = {}
    for node_index, node in enumerate(node_list):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        for alias_index, alias in enumerate(node.names):
            if isinstance(node, ast.ImportFrom) and alias.name == '*':
                continue
            bound_name = (alias.asname or alias.name.split('.')[0]
                          if isinstance(node, ast.Import)
                          else alias.asname or alias.name)
            latest[bound_name] = (node_index, alias_index)
    visible: list[ast.AST] = []
    for node_index, node in enumerate(node_list):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            visible.append(node)
            continue
        kept = []
        for alias_index, alias in enumerate(node.names):
            if isinstance(node, ast.ImportFrom) and alias.name == '*':
                kept.append(alias)
                continue
            bound_name = (alias.asname or alias.name.split('.')[0]
                          if isinstance(node, ast.Import)
                          else alias.asname or alias.name)
            if latest[bound_name] == (node_index, alias_index):
                kept.append(alias)
        if len(kept) == len(node.names):
            visible.append(node)
        elif kept:
            replacement = (ast.Import(names=kept)
                           if isinstance(node, ast.Import)
                           else ast.ImportFrom(module=node.module, names=kept,
                                               level=node.level))
            visible.append(ast.copy_location(replacement, node))
    return visible
@dataclass(frozen=True)
class ImportBinds:
    os_names: set[str]
    sp_names: set[str]
    sys_names: set[str]
    pickle_names: set[str]
    marshal_names: set[str]
    yaml_names: set[str]
    ctypes_names: set[str]
    ssl_names: set[str]
    builtins_names: set[str]
    from_binds: dict[str, tuple[str, str]]
    os_path_names: set[str] = field(default_factory=set)
    yaml_loader_names: set[str] = field(default_factory=set)
    @classmethod
    def from_nodes(cls, nodes) -> ImportBinds:
        nodes = list(nodes)
        (os_n, sp_n, sys_n, pickle_n, marshal_n, yaml_n, ctypes_n, ssl_n,
         builtins_n, builtin_n) = _module_alias_names_from_nodes(
            nodes, 'os', 'subprocess', 'sys', 'pickle', 'marshal', 'yaml',
            'ctypes', 'ssl', 'builtins', '__builtin__')
        yaml_loader_n = _module_alias_names_from_nodes(
            nodes, 'yaml.loader')[0]
        return cls(os_names=os_n, sp_names=sp_n, sys_names=sys_n,
                   pickle_names=pickle_n, marshal_names=marshal_n,
                   yaml_names=yaml_n,
                   ctypes_names=ctypes_n, ssl_names=ssl_n,
                   builtins_names=builtins_n | builtin_n,
                   from_binds=_from_import_symbol_binds_from_nodes(nodes),
                   os_path_names=_os_path_names_from_nodes(nodes),
                   yaml_loader_names=yaml_loader_n)
_OUTER_EVAL_SCOPE_TYPES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
)
_COMP_SCOPE_TYPES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
_LEXICAL_SCOPE_TYPES = _OUTER_EVAL_SCOPE_TYPES + _COMP_SCOPE_TYPES
_ORDERED_BINDING_SCOPE_TYPES = (
    ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef,
)
def _parent_map(nodes) -> dict[ast.AST, ast.AST]:
    parents: dict[ast.AST, ast.AST] = {}
    for parent in nodes:
        for child in ast.iter_child_nodes(parent):
            parents[child] = parent
    return parents
def _scope_body(scope: ast.AST) -> tuple[ast.AST, ...]:
    body = getattr(scope, 'body', None)
    if body is None:
        return ()
    if isinstance(body, list):
        return tuple(body)
    return (body,)
def _outer_comprehension_iter(scope, child, below) -> bool:
    return bool(isinstance(child, ast.comprehension)
                and scope.generators and child is scope.generators[0]
                and below is child.iter)
def _nearest_scope(node: ast.AST, parents: dict, scopes: set, tree: ast.AST):
    current = node
    child = None
    below = None
    while current is not None:
        if current in scopes:
            outer_evaluation = (
                isinstance(current, _OUTER_EVAL_SCOPE_TYPES)
                and child not in _scope_body(current))
            outer_comp_iter = (
                isinstance(current, _COMP_SCOPE_TYPES)
                and _outer_comprehension_iter(current, child, below))
            if not outer_evaluation and not outer_comp_iter:
                return current
        below = child
        child, current = current, parents.get(current)
    return tree
def _in_deferred_body(node: ast.AST, scope: ast.AST,
                      parents: dict[ast.AST, ast.AST]) -> bool:
    current = node
    child = None
    while current is not None and current is not scope:
        if (isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda))
                and child in _scope_body(current)):
            return True
        child, current = current, parents.get(current)
    return False
def _scope_order_position(scope: ast.AST, node: ast.AST | None,
                          parents: dict[ast.AST, ast.AST]
                          ) -> tuple[int, int] | None:
    if not isinstance(scope, _ORDERED_BINDING_SCOPE_TYPES) or node is None:
        return None
    if _in_deferred_body(node, scope, parents):
        return None
    lineno = getattr(node, 'lineno', None)
    if not isinstance(lineno, int) or lineno <= 0:
        return None
    return lineno, getattr(node, 'col_offset', 0)
def _node_order_position(node: ast.AST, *, end: bool = False
                         ) -> tuple[int, int] | None:
    prefix = 'end_' if end else ''
    lineno = getattr(node, f'{prefix}lineno', None)
    if not isinstance(lineno, int) or lineno <= 0:
        return None
    return lineno, getattr(node, f'{prefix}col_offset', 0)
def _binding_order_position(node: ast.AST) -> tuple[int, int] | None:
    if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                         ast.NamedExpr, ast.Import, ast.ImportFrom,
                         ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
                         ast.Global, ast.Nonlocal)):
        return _node_order_position(node, end=True)
    if isinstance(node, (ast.For, ast.AsyncFor, ast.ExceptHandler)):
        return (_node_order_position(node.body[0]) if node.body
                else _node_order_position(node, end=True))
    if isinstance(node, ast.withitem) and node.optional_vars is not None:
        return _node_order_position(node.optional_vars, end=True)
    if isinstance(node, ast.match_case):
        return _node_order_position(node.pattern, end=True)
    return _node_order_position(node)
def _is_binding_site(node: ast.AST) -> bool:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
                         ast.Assign, ast.AugAssign, ast.For, ast.AsyncFor,
                         ast.Import, ast.ImportFrom, ast.Global, ast.Nonlocal,
                         ast.NamedExpr, ast.match_case)):
        return True
    if isinstance(node, ast.AnnAssign):
        return node.value is not None
    if isinstance(node, ast.withitem):
        return node.optional_vars is not None
    return isinstance(node, ast.ExceptHandler) and bool(node.name)
def _scope_binding_events(scope: ast.AST) -> tuple[tuple[tuple[int, int], ast.AST], ...]:
    events = [
        (position, node) for node in iter_direct_scope_nodes(scope)
        if _is_binding_site(node)
        for position in [_binding_order_position(node)] if position is not None]
    events.extend(
        (position, node) for node in _comprehension_namedexpr_nodes(scope)
        for position in [_binding_order_position(node)] if position is not None)
    return tuple(sorted(events, key=lambda event: event[0]))
def _binding_event_maps(scopes: set) -> tuple[dict, dict]:
    positions: dict = {}
    events_by_scope: dict = {}
    for scope in scopes:
        if not isinstance(scope, _ORDERED_BINDING_SCOPE_TYPES):
            continue
        events = _scope_binding_events(scope)
        positions[scope] = tuple(sorted({position for position, _node in events}))
        events_by_scope[scope] = events
    return positions, events_by_scope
def _ordered_shadow_position(
        scope: ast.AST, node: ast.AST | None,
        parents: dict[ast.AST, ast.AST], binding_positions: dict
        ) -> tuple[int, int] | None:
    immediate = _scope_order_position(scope, node, parents)
    if immediate is None:
        return None
    positions = binding_positions.get(scope, ())
    index = bisect_right(positions, immediate)
    return positions[index - 1] if index else (0, 0)
def _ordered_shadow_names(scope: ast.AST, shadow_imports: bool,
                          before: tuple[int, int], events: tuple,
                          states: dict) -> set[str]:
    key = (id(scope), shadow_imports)
    state = states.get(key)
    if state is None or before < state[0]:
        names: set[str] = collect_param_names(scope)
        declared_outer: set[str] = set()
        event_index = 0
    else:
        _previous, names, declared_outer, event_index = state
    while event_index < len(events) and events[event_index][0] <= before:
        _position, event_node = events[event_index]
        collect_scope_binding_names(event_node, names, declared_outer)
        if isinstance(event_node, (ast.Import, ast.ImportFrom)):
            imported, star = import_binding_names(event_node)
            if (star and isinstance(event_node, ast.ImportFrom)
                    and not event_node.level):
                imported.update(_STAR_IMPORT_SYMBOLS.get(
                    event_node.module or '', ()))
            if shadow_imports:
                names.update(imported)
            else:
                names.difference_update(imported)
            if star and not (
                    isinstance(event_node, ast.ImportFrom)
                    and not event_node.level
                    and event_node.module in _STAR_IMPORT_SYMBOLS):
                names.add('*')
        # global/nonlocal 声明本身不建立本地绑定，但声明后的写入会改变
        # 当前名称解析到的外层对象，必须保留为同名导入的遮蔽屏障。
        event_index += 1
    states[key] = (before, names, declared_outer, event_index)
    return names
def _enclosing_scope(scope: ast.AST, parents: dict, scopes: set):
    current = parents.get(scope)
    skip_class = isinstance(scope, _LEXICAL_SCOPE_TYPES)
    while current is not None:
        if (current in scopes
                and not (skip_class and isinstance(current, ast.ClassDef))):
            return current
        current = parents.get(current)
    return None
class ScopeIndex:
    def __init__(self, tree: ast.AST):
        self._tree = tree
        self._module_nodes: list[ast.AST] = []
        self._local_nodes: dict[int, list[ast.AST]] = defaultdict(list)
        self._class_nodes: dict[int, list[ast.AST]] = defaultdict(list)
        self._parent_func: dict[int, ast.AST | None] = {}
        self._parents: dict[ast.AST, ast.AST] = {}
        self._binding_positions: dict[ast.AST, tuple] = {}
        self._binding_events: dict[ast.AST, tuple] = {}
        self._ordered_shadow_states: dict = {}
        self._import_scopes: dict[int, ast.AST] = {}
        self._binds_cache: dict[tuple[int, int], ImportBinds] = {}
        self._call_binds_cache: dict[tuple, ImportBinds] = {}
        self._visible_cache: dict[tuple[int, int], list[ast.AST]] = {}
        self._call_visible_cache: dict[tuple, list[ast.AST]] = {}
        self._module_alias_cache: dict[tuple, set[str]] = {}
        self._bound_symbols_cache: dict[tuple, dict[str, str]] = {}
        self._call_scope: dict[int, ast.AST | None] = {}
        self._call_class_scope: dict[int, ast.ClassDef | None] = {}
        self._shadow_cache: dict[tuple, set[str]] = {}
        self._index()
    def _index(self) -> None:
        nodes = shared_walk(self._tree)
        parents = _parent_map(nodes)
        self._parents = parents
        scopes = {self._tree} | {
            node for node in nodes if isinstance(node, _LEXICAL_SCOPE_TYPES)}
        self._binding_positions, self._binding_events = (
            _binding_event_maps(scopes))
        for scope in scopes:
            if scope is self._tree or isinstance(scope, ast.ClassDef):
                continue
            parent = _enclosing_scope(scope, parents, scopes)
            self._parent_func[id(scope)] = (
                None if parent is None or parent is self._tree else parent)
        for node in nodes:
            scope = _nearest_scope(node, parents, scopes, self._tree)
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                self._import_scopes[id(node)] = scope
                if isinstance(scope, ast.ClassDef):
                    self._class_nodes[id(scope)].append(node)
                elif scope is self._tree:
                    self._module_nodes.append(node)
                else:
                    self._local_nodes[id(scope)].append(node)
            if not isinstance(node, ast.Call):
                continue
            class_scope = scope if isinstance(scope, ast.ClassDef) else None
            func_scope = (_enclosing_scope(scope, parents, scopes)
                          if class_scope is not None else scope)
            self._call_scope[id(node)] = (
                None if func_scope is None or func_scope is self._tree
                else func_scope)
            self._call_class_scope[id(node)] = class_scope
    def _ancestors_of(self, func: ast.AST) -> tuple[ast.AST, ...]:
        chain: list[ast.AST] = []
        seen: set[int] = set()
        cur = self._parent_func.get(id(func))
        while cur is not None and id(cur) not in seen:
            seen.add(id(cur))
            chain.append(cur)
            cur = self._parent_func.get(id(cur))
        return tuple(reversed(chain))
    @staticmethod
    def _scope_key(func: ast.AST | None,
                   class_body: ast.ClassDef | None) -> tuple[int, int]:
        return (0 if func is None else id(func),
                0 if class_body is None else id(class_body))
    def _visible_nodes(self, func: ast.AST | None,
                       class_body: ast.ClassDef | None = None) -> list[ast.AST]:
        key = self._scope_key(func, class_body)
        cached = self._visible_cache.get(key)
        if cached is None:
            cached = self._collect_visible_nodes(func, class_body)
            self._visible_cache[key] = cached
        return cached
    def _collect_visible_nodes(
            self, func: ast.AST | None,
            class_body: ast.ClassDef | None) -> list[ast.AST]:
        nodes = list(self._module_nodes)
        if func is not None:
            for ancestor in self._ancestors_of(func):
                nodes.extend(self._local_nodes.get(id(ancestor), ()))
            nodes.extend(self._local_nodes.get(id(func), ()))
        if class_body is not None:
            nodes.extend(self._class_nodes.get(id(class_body), ()))
        seen: set[int] = set()
        unique: list[ast.AST] = []
        for node in nodes:
            if id(node) in seen:
                continue
            seen.add(id(node))
            unique.append(node)
        return unique
    def _binds_for_scope(self, func: ast.AST | None,
                         class_body: ast.ClassDef | None) -> ImportBinds:
        key = self._scope_key(func, class_body)
        cached = self._binds_cache.get(key)
        if cached is None:
            cached = ImportBinds.from_nodes(
                self._visible_nodes(func, class_body))
            self._binds_cache[key] = cached
        return cached
    def _visible_nodes_for_call(self, call: ast.Call) -> tuple[tuple, list]:
        scope = self.scope_of_call(call)
        class_scope = self._call_class_scope.get(id(call))
        ordered_scopes = [self._tree, class_scope, scope]
        if scope is not None:
            ordered_scopes.extend(self._ancestors_of(scope))
        ordered_scopes = list(dict.fromkeys(
            candidate for candidate in ordered_scopes if candidate is not None))
        ordered_positions = tuple(
            _ordered_shadow_position(
                candidate, call, self._parents, self._binding_positions)
            for candidate in ordered_scopes)
        key = (*self._scope_key(scope, class_scope), *ordered_positions)
        cached = self._call_visible_cache.get(key)
        if cached is not None:
            return key, cached
        nodes = self._visible_nodes(scope, class_scope)
        if any(position is not None for position in ordered_positions):
            visible = []
            for node in nodes:
                owner = self._import_scopes.get(id(node))
                if isinstance(owner, _ORDERED_BINDING_SCOPE_TYPES):
                    before = _ordered_shadow_position(
                        owner, call, self._parents, self._binding_positions)
                    position = _binding_order_position(node)
                    if (before is not None
                            and (position is None or position > before)):
                        continue
                visible.append(node)
            nodes = visible
        scope_order: dict[ast.AST, int] = {}
        for node in nodes:
            owner = self._import_scopes.get(id(node))
            if owner not in scope_order:
                scope_order[owner] = len(scope_order)
        nodes = sorted(
            nodes,
            key=lambda node: (
                scope_order.get(self._import_scopes.get(id(node)), -1),
                _binding_order_position(node) or (10**12, 10**12),
            ),
        )
        nodes = _filter_overridden_imports(nodes)
        self._call_visible_cache[key] = nodes
        return key, nodes
    def binds_for(self, func: ast.AST | None) -> ImportBinds:
        return self._binds_for_scope(func, None)
    def scope_of_call(self, call: ast.Call) -> ast.AST | None:
        return self._call_scope.get(id(call))
    def binds_for_call(self, call: ast.Call) -> ImportBinds:
        key, nodes = self._visible_nodes_for_call(call)
        cached = self._call_binds_cache.get(key)
        if cached is None:
            cached = ImportBinds.from_nodes(nodes)
            self._call_binds_cache[key] = cached
        return cached
    def module_aliases_for_call(self, call: ast.Call, module: str) -> set[str]:
        visibility_key, nodes = self._visible_nodes_for_call(call)
        key = (*visibility_key, module)
        cached = self._module_alias_cache.get(key)
        if cached is None:
            cached = _module_alias_names_from_nodes(nodes, module)[0]
            self._module_alias_cache[key] = cached
        return cached
    def bound_symbols_for_call(self, call: ast.Call, module: str,
                               symbols) -> dict[str, str]:
        visibility_key, nodes = self._visible_nodes_for_call(call)
        key = (*visibility_key, module, tuple(symbols))
        cached = self._bound_symbols_cache.get(key)
        if cached is None:
            cached = _from_import_bind_syms_from_nodes(nodes, module, symbols)
            self._bound_symbols_cache[key] = cached
        return cached
    def _scope_shadow_names(self, scope: ast.AST,
                            shadow_imports: bool = False,
                            node: ast.AST | None = None) -> set[str]:
        before_position = _ordered_shadow_position(
            scope, node, self._parents, self._binding_positions)
        if (before_position is None
                and isinstance(scope, _ORDERED_BINDING_SCOPE_TYPES)):
            events = self._binding_events[scope]
            before_position = events[-1][0] if events else (0, 0)
        if before_position is not None:
            return _ordered_shadow_names(
                scope, shadow_imports, before_position,
                self._binding_events[scope], self._ordered_shadow_states)
        key = (id(scope), shadow_imports)
        cached = self._shadow_cache.get(key)
        if cached is None:
            cached = _scope_shadow_names(scope, shadow_imports)
            self._shadow_cache[key] = cached
        return cached
    def _name_is_shadowed(self, call: ast.Call, name: str,
                          include_star: bool) -> bool:
        scopes = []
        class_scope = self._call_class_scope.get(id(call))
        if class_scope is not None:
            scopes.append(class_scope)
        scope = self.scope_of_call(call)
        while scope is not None:
            scopes.append(scope)
            scope = self._parent_func.get(id(scope))
        scopes.append(self._tree)
        for scope in scopes:
            non_imports = self._scope_shadow_names(scope, node=call)
            if _shadowed_name(non_imports, name, include_star):
                return True
            imports = (self._scope_shadow_names(scope, True, call)
                       - non_imports)
            if name in imports:
                return False
        return False
    def name_is_shadowed(self, call: ast.Call, name: str) -> bool:
        return self._name_is_shadowed(call, name, True)
def _call_name_is_shadowed(call: ast.Call, index: ScopeIndex) -> bool:
    func = call.func
    if isinstance(func, ast.Name):
        return index._name_is_shadowed(call, func.id, False)
    if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        return index._name_is_shadowed(call, func.value.id, False)
    return False
SHELL_CALL_ATTRS = frozenset(
    {"call", "run", "Popen", "check_output", "check_call"})
_CMD_OWNER_MODULES = frozenset({"os", "subprocess"})
_CTYPES_FFI_ATTRS = frozenset(
    {"windll", "WinDLL", "CDLL", "oledll", "PyDLL"})
_YAML_LOAD_FUNCS = frozenset({'load', 'load_all'})
YAML_UNSAFE_LOAD_FUNCS = frozenset({'unsafe_load', 'unsafe_load_all'})
YAML_LOAD_FAMILY = _YAML_LOAD_FUNCS | YAML_UNSAFE_LOAD_FUNCS
_YAML_DISPATCH_SYMBOLS = YAML_LOAD_FAMILY | frozenset({'loads'})
_CREDENTIAL_BASE_NAME_PATTERN = '|'.join(
    kw.replace('_', '[_-]?') for kw in CREDENTIAL_KEYWORDS
    if kw not in {'token', 'auth_token'})
_NON_CREDENTIAL_TOKEN_PREFIXES = ('page', 'next', 'pagination', 'csrf', 'paid')
_CREDENTIAL_TOKEN_NAME_PATTERN = (
    rf'(?!(?:{"|".join(_NON_CREDENTIAL_TOKEN_PREFIXES)})[_-]?token'
    r'(?![A-Za-z0-9_]))'
    r'(?:[A-Za-z_]\w*[_-])?token(?![A-Za-z0-9_])'
)
_CREDENTIAL_NAME_PATTERN = (
    rf'(?:{_CREDENTIAL_BASE_NAME_PATTERN}|{_CREDENTIAL_TOKEN_NAME_PATTERN})')
_CREDENTIAL_NAME_RE = re.compile(
    rf'^(?:.*(?:{_CREDENTIAL_BASE_NAME_PATTERN}).*'
    rf'|{_CREDENTIAL_TOKEN_NAME_PATTERN})$', re.IGNORECASE)
_HARDCODED_CREDENTIAL_PATTERNS = [re.compile(
    rf'(?:{_CREDENTIAL_BASE_NAME_PATTERN}'
    rf'|(?<![A-Za-z0-9_]){_CREDENTIAL_TOKEN_NAME_PATTERN})'
    + r'(?:["\']\s*\])?\s*(?::\s*[^=:\n]+)?[:=]\s*["\']([^"\']{4,})["\']',
    re.IGNORECASE
)]
@dataclass(frozen=True)
class _TokenSpans:
    strings: dict[int, list[tuple[int, int | None, str]]]
    string_clear_lines: set[int]
    string_end_anchors: dict[int, int]
    comments: dict[int, list[tuple[int, int | None]]]
def _collect_token_spans(tokens) -> _TokenSpans:
    strings: dict[int, list[tuple[int, int | None, str]]] = {}
    clear_lines: set[int] = set()
    end_anchors: dict[int, int] = {}
    comments: dict[int, list[tuple[int, int | None]]] = {}
    _fstring_middle = getattr(tokenize, "FSTRING_MIDDLE", None)
    for tok in tokens:
        if tok.type == tokenize.STRING:
            _repl = '""'
        elif _fstring_middle is not None and tok.type == _fstring_middle:
            _repl = ''
        elif tok.type == tokenize.COMMENT:
            comments.setdefault(tok.start[0], []).append(
                (tok.start[1],
                 tok.end[1] if tok.start[0] == tok.end[0] else None))
            continue
        else:
            continue
        start_line, start_col = tok.start
        end_line, end_col = tok.end
        if _repl == '' and tok.string and tok.string[-1] in '{}':
            end_col += 1
        if start_line == end_line:
            strings.setdefault(start_line, []).append(
                (start_col, end_col, _repl))
        else:
            strings.setdefault(start_line, []).append((start_col, None, _repl))
            for mid in range(start_line + 1, end_line):
                clear_lines.add(mid)
            strings.setdefault(end_line, []).append((0, end_col, _repl))
            if _repl:
                end_anchors[end_line] = start_line
    return _TokenSpans(strings, clear_lines, end_anchors, comments)
def _token_spans(source: str) -> _TokenSpans | None:
    try:
        return _collect_token_spans(
            tokenize.generate_tokens(io.StringIO(source).readline))
    except Exception as e:  # noqa: BLE001 —— 分词失败形态不可枚举，回退原文避免误报
        _log.warning("源码分词失败，返回原始内容: %s", e, exc_info=True)
        return None
def _anchor_indent(lines: list, end_anchors: dict | None, line_no: int) -> str:
    if not end_anchors:
        return ''
    start_line = end_anchors.get(line_no)
    if start_line is None or not 0 < start_line <= len(lines):
        return ''
    head = lines[start_line - 1]
    return head[:len(head) - len(head.lstrip())]
def _apply_string_mask_spans(lines: list, per_line: dict, clear_lines: set,
                             end_anchors: dict | None) -> None:
    for ln in clear_lines:
        if 0 < ln <= len(lines):
            lines[ln - 1] = ''
    for ln, spans in per_line.items():
        if not 0 < ln <= len(lines):
            continue
        line = lines[ln - 1]
        _indent = _anchor_indent(lines, end_anchors, ln)
        for start_col, end_col, _repl in sorted(spans, key=lambda s: -s[0]):
            if end_col is None:
                line = line[:start_col] + _repl
            else:
                _lead = _indent if start_col == 0 else ''
                line = line[:start_col] + _lead + _repl + line[end_col:]
        lines[ln - 1] = line
def _apply_comment_strip_spans(lines: list, per_line: dict) -> None:
    for ln, spans in per_line.items():
        if not 0 < ln <= len(lines):
            continue
        line = lines[ln - 1]
        for start_col, end_col in sorted(spans, key=lambda s: -s[0]):
            line = (line[:start_col] if end_col is None
                    else line[:start_col] + line[end_col:])
        lines[ln - 1] = line
def _scan_text(source: str, *, mask_strings: bool) -> str:
    spans = _token_spans(source)
    if spans is None:
        return source
    lines = source.split('\n')
    _apply_comment_strip_spans(lines, spans.comments)
    if mask_strings:
        _apply_string_mask_spans(
            lines, spans.strings, spans.string_clear_lines,
            spans.string_end_anchors)
    return '\n'.join(lines)
def _rule_family(*codes: str) -> tuple[str, ...]:
    family: list[str] = []
    for code in codes:
        family.append(code)
        if code[:1] in ("S", "B"):
            family.append(("B" if code[0] == "S" else "S") + code[1:])
    return tuple(dict.fromkeys(family))
_INLINE_SUPPRESSION_RULES: dict[str, tuple[str, tuple[str, ...]]] = {
    "hardcoded_secret": ("hardcoded_secret",
                         ("E1-HARDCODED-CRED", *_rule_family("S105", "S106"))),
    "eval_exec": ("code_injection", _rule_family("S102", "S307")),
    "pickle_load": ("deserialization", _rule_family("S301")),
    "shell_true": ("command_injection", _rule_family("S602", "S604", "S605")),
    "import_pickle": ("deserialization",
                      _rule_family("S403", "S301")),
    "import_marshal": ("deserialization", _rule_family("S301")),
    "import_shelve": ("deserialization", _rule_family("S301")),
    "os.system": ("command_injection", _rule_family("S605")),
    "subprocess.shell": ("command_injection",
                         _rule_family("S602", "S604", "S605")),
    "command_injection": ("command_injection",
                          _rule_family("S602", "S604", "S605")),
    "cmd_injection_var": ("command_injection", _rule_family("S605")),
    "cmd_injection_shell": ("command_injection",
                            _rule_family("S602", "S604", "S605")),
    "eval": ("code_injection", _rule_family("S307", "S102")),
    "exec": ("code_injection", _rule_family("S102")),
    "pickle": ("deserialization", _rule_family("S301")),
    "marshal": ("deserialization", _rule_family("S301")),
    "marshal_load": ("deserialization", _rule_family("S301")),
    "shelve": ("deserialization", _rule_family("S301")),
    "yaml.load": ("deserialization", _rule_family("S506")),
    "yaml_unsafe": ("deserialization", _rule_family("S506")),
    "sql_injection": ("sql_injection", _rule_family("S608")),
    "sql_injection_fstring": ("sql_injection", _rule_family("S608")),
    "sql_injection_concat": ("sql_injection", _rule_family("S608")),
    "hardcoded_credential": ("hardcoded_secret", _rule_family("S105", "S106")),
    "insecure_tempfile": ("", _rule_family("S306")),
    "weak_hash": ("", _rule_family("S324")),
    "ssl._create_unverified_context": ("", _rule_family("S323")),
    "xxe": ("", _rule_family("S313", "S314")),
    "insecure_xml": ("", _rule_family("S313", "S314")),
    "insecure_deserialization": ("deserialization", ()),
    "path_traversal": ("", ()),
    "path_traversal_join": ("", ()),
    "ssrf": ("", ()),
    "ctypes": ("", ()),
    "debug_mode": ("", ()),
    "hardcoded_address": ("", ()),
}
def _suppression_spec(kind: str | None) -> tuple[str, tuple[str, ...]]:
    spec = _INLINE_SUPPRESSION_RULES.get(kind or "")
    if spec is not None:
        return spec
    if kind and kind.isupper():
        return "", (kind,)
    return "", ()
def line_suppressed_at(lineno, source_lines,
                       rule: str | None = None) -> bool:
    if isinstance(lineno, bool) or not isinstance(lineno, int):
        return False
    if not 0 < lineno <= len(source_lines):
        return False
    if not _line_mentions_suppression(str(source_lines[lineno - 1])):
        return False
    category, rule_ids = _suppression_spec(rule)
    source = "\n".join(str(line) for line in source_lines)
    if line_has_applicable_nosec(source, lineno, category,
                                 frozenset(rule_ids)):
        return True
    if not (category or rule_ids):
        return False
    suppressions = parse_suppressions(source)
    if not suppressions:
        return False
    return any(is_suppressed(suppressions, lineno, token)
               for token in (category, *rule_ids) if token)
def _line_mentions_suppression(line_text: str) -> bool:
    low = line_text.lower()
    return "nosec" in low or "noqa" in low or "suppress" in low
def _yaml_loader_arg(call_node: ast.Call) -> ast.expr | None:
    for kw in call_node.keywords:
        if kw.arg == 'Loader':
            return kw.value
    if len(call_node.args) >= 2:
        return call_node.args[1]
    return None
def _safe_loader_binding(loader: ast.expr, binds: ImportBinds) -> bool:
    if isinstance(loader, ast.Name):
        binding = binds.from_binds.get(loader.id)
        return (binding is not None
                and binding[0] in ('yaml', 'yaml.loader')
                and binding[1] in YAML_SAFE_LOADERS)
    if not (isinstance(loader, ast.Attribute)
            and loader.attr in YAML_SAFE_LOADERS):
        return False
    if isinstance(loader.value, ast.Name):
        owner = loader.value.id
        if owner in binds.yaml_names or owner in binds.yaml_loader_names:
            return True
        return binds.from_binds.get(owner) == ('yaml', 'loader')
    return (isinstance(loader.value, ast.Attribute)
            and loader.value.attr == 'loader'
            and isinstance(loader.value.value, ast.Name)
            and loader.value.value.id in binds.yaml_names)
def has_safe_loader(call_node: ast.Call, binds: ImportBinds,
                    index: ScopeIndex) -> bool:
    loader = _yaml_loader_arg(call_node)
    if loader is None or is_none_literal(loader):
        return False
    bound = loader
    while isinstance(bound, ast.Attribute):
        bound = bound.value
    bound_name = bound.id if isinstance(bound, ast.Name) else None
    if (bound_name is not None
            and index._name_is_shadowed(call_node, bound_name, False)):
        return False
    return _safe_loader_binding(loader, binds)
def has_shell_true_kw(call_node: ast.Call) -> bool:
    for kw in call_node.keywords:
        if kw.arg != 'shell' or not isinstance(kw.value, ast.Constant):
            continue
        value = kw.value.value
        if value is None or value is Ellipsis:
            return False
        return bool(value)
    return False
_DESER_LOAD_ATTRS = frozenset({"load", "loads"})
_EVAL_EXEC_NAMES = ('eval', 'exec')
_BUILTIN_RISK_NAMES = ('input', *_EVAL_EXEC_NAMES)
_BUILTINS_MODULE_NAMES = ('builtins', '__builtin__')
_TAINT_SOURCE_PATTERNS = [
    re.compile(r'\bsys\.argv\b'),
    re.compile(r'\bos\.environ\b'),
    re.compile(r'\bgetenv\s*\('),
    re.compile(r'(?<![\w.])input\s*\('),
    re.compile(r'\bsys\.stdin\b'),
    re.compile(r'\.recv(?:from)?\s*\('),
    re.compile(r'\brequest\s*\.'),
    re.compile(r'\baskopenfilename\s*\('),
    re.compile(r'(?<![\w.])(?:argv|environ|stdin)\b'),
]
_TAINT_NAME_HINTS = frozenset({'argv', 'environ', 'stdin'})
def _matches_taint_source(scan_view: str) -> bool:
    return any(p.search(scan_view) for p in _TAINT_SOURCE_PATTERNS)
_TAINT_CALL_NAMES = {'input', 'getenv', 'recv', 'recvfrom', 'urlopen'}
_TAINT_ATTR_HINTS = {'argv', 'environ', 'stdin', 'form', 'cookies', 'headers'}
def _fn_tainted_names(func_node) -> set:
    tainted: set = set()
    while True:
        grew = False
        for n in iter_own_scope(func_node, skip_lambda=True):
            if isinstance(n, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                              ast.NamedExpr)):
                grew = _propagate_assign_taint(n, tainted) or grew
        if not grew:
            return tainted
def _assignment_targets_value(node: ast.AST):
    if isinstance(node, (ast.AugAssign, ast.NamedExpr)):
        return [node.target], node.value
    return assign_targets_value(node)
def _propagate_assign_taint(n, tainted: set) -> bool:
    pair = _assignment_targets_value(n)
    if pair is None:
        return False
    targets, value = pair
    if not _node_taint_hit(value, tainted):
        return False
    _new = {name for target in targets
            for name in iter_unpack_target_names(target)
            if name not in tainted}
    tainted |= _new
    return bool(_new)
def _node_taint_hit(node: ast.AST, tainted_names: set) -> bool:
    for n in walk_nodes(node):
        if isinstance(n, ast.Call) and ast_name(n.func) in _TAINT_CALL_NAMES:
            return True
        if isinstance(n, ast.Attribute) and n.attr in _TAINT_ATTR_HINTS:
            return True
        if (isinstance(n, ast.Name)
                and (n.id in tainted_names or n.id in _TAINT_NAME_HINTS)):
            return True
    return False
def _line_join_has_taint(func_node, line_num: int) -> bool:
    tainted_names = _fn_tainted_names(func_node)
    for n in iter_own_scope(func_node, skip_lambda=True):
        if getattr(n, 'lineno', None) != line_num:
            continue
        if (isinstance(n, ast.BinOp) and isinstance(n.op, ast.Add)
                and (_node_taint_hit(n.left, tainted_names)
                     or _node_taint_hit(n.right, tainted_names))):
            return True
    return False
def entry_source_lines(entry) -> list:
    src = getattr(entry, 'source', '') or ''
    return src.split('\n')
def yaml_call_is_unsafe(symbol: str, call: ast.Call,
                        binds: ImportBinds, index: ScopeIndex) -> bool:
    return (symbol in YAML_LOAD_FAMILY
            and (symbol in YAML_UNSAFE_LOAD_FUNCS
                 or not has_safe_loader(call, binds, index)))
_EXIT_CALL_NAMES = ('exit', 'quit')
_STAR_IMPORT_SYMBOLS = {
    'os': ('system', '_exit'),
    'os.path': ('join',),
    'subprocess': tuple(SHELL_CALL_ATTRS),
    'sys': ('exit',),
    'pickle': tuple(_DESER_LOAD_ATTRS),
    'marshal': tuple(_DESER_LOAD_ATTRS),
    'yaml': (*YAML_LOAD_FAMILY, *YAML_SAFE_LOADERS),
    **{
        module: (*_BUILTIN_RISK_NAMES, *_EXIT_CALL_NAMES)
        for module in _BUILTINS_MODULE_NAMES
    },
}
_FindingAdder = Callable[[str, str, str, int], None]
_CLI_ENTRY_FILES = {'__main__.py', 'cli.py'}
_CLI_ENTRY_NAMES = frozenset({'main'})
def _is_cli_entry_file(base: str) -> bool:
    if base in _CLI_ENTRY_FILES:
        return True
    stem = base.removesuffix('.py')
    return 'cli' in re.split(r'[^a-z0-9]+', stem.lower())
def _is_main_guard(node: ast.AST) -> bool:
    if not isinstance(node, ast.If) or not isinstance(node.test, ast.Compare):
        return False
    return main_guard_branch(node.test) is True
def _main_guard_called_names(tree: ast.Module) -> set[str]:
    names: set[str] = set()
    for node in getattr(tree, 'body', ()):
        if not _is_main_guard(node):
            continue
        stack = list(node.body)
        while stack:
            cur = stack.pop()
            if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda, ast.ClassDef)):
                continue
            if isinstance(cur, ast.Call) and isinstance(cur.func, ast.Name):
                names.add(cur.func.id)
            stack.extend(ast.iter_child_nodes(cur))
    return names
def _exit_call_leaves_process(call: ast.Call, ctx: _FuzzContext) -> bool:
    if _call_name_is_shadowed(call, ctx.index):
        return False
    binds = ctx.index.binds_for_call(call)
    func = call.func
    if isinstance(func, ast.Name):
        binding = binds.from_binds.get(func.id)
        if binding is not None:
            module, symbol = binding
            return ((module == 'sys' and symbol == 'exit')
                    or (module == 'os' and symbol == '_exit')
                    or (module in _BUILTINS_MODULE_NAMES
                        and symbol in _EXIT_CALL_NAMES))
        return func.id in _EXIT_CALL_NAMES
    if (isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)):
        owner = func.value.id
        return ((owner in binds.sys_names and func.attr == 'exit')
                or (owner in binds.os_names and func.attr == '_exit')
                or (owner in binds.builtins_names
                    and func.attr in _EXIT_CALL_NAMES))
    return False
def _loop_has_function_exit(loop_node: ast.AST,
                            ctx: _FuzzContext | None = None) -> bool:
    stack = list(loop_node.body)
    while stack:
        n = stack.pop()
        if isinstance(n, (ast.Return, ast.Raise)):
            return True
        if ctx is not None and isinstance(n, ast.Call) and (
                _exit_call_leaves_process(n, ctx)):
            return True
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        stack.extend(ast.iter_child_nodes(n))
    return False
@dataclass(frozen=True)
class _FuzzContext:
    func_node: ast.AST
    is_cli_entry: bool
    binds: ImportBinds
    index: ScopeIndex
    add: _FindingAdder
    # if __name__ == "__main__": 守卫体内的全部节点 id：守卫体就是进程
    # 边界的 CLI 交接段，其中的 sys.exit 是退出码契约，不是「模块级提前
    # 终止进程」的缺陷。
    cli_guard_ids: frozenset = frozenset()
    @property
    def in_cli_context(self) -> bool:
        return (self.is_cli_entry
                or getattr(self.func_node, 'name', '').startswith('cmd_'))
def _scan_child_danger(child: ast.AST, ctx: _FuzzContext) -> None:
    if not isinstance(child, (ast.While, ast.Call)):
        return
    _line = getattr(child, "lineno", None)
    if _line is None:
        return
    if isinstance(child, ast.While):
        _check_while_danger(child, ctx, _line)
        return
    fnode = child.func
    if isinstance(fnode, ast.Name):
        _check_call_name_danger(child, ctx, _line)
    elif isinstance(fnode, ast.Attribute):
        _check_call_attr_danger(child, ctx, _line)
def _check_while_danger(child: ast.While, ctx: _FuzzContext, _line: int) -> None:
    if (isinstance(child.test, ast.Constant) and bool(child.test.value)
            and not ctx.in_cli_context
            and id(child) not in ctx.cli_guard_ids
            and not loop_body_has_break(child.body)
            and not _loop_has_function_exit(child, ctx)):
        ctx.add("danger_pattern", "while_true", "medium", _line)
def _check_call_name_danger(child: ast.Call, ctx: _FuzzContext,
                            _line: int) -> None:
    fnode = child.func
    if _call_name_is_shadowed(child, ctx.index):
        return
    binding = ctx.binds.from_binds.get(fnode.id)
    if binding is None:
        if fnode.id in _BUILTIN_RISK_NAMES:
            _check_builtin_name_danger(child, ctx, _line)
        return
    _mod, _sym = binding
    if _mod in _BUILTINS_MODULE_NAMES:
        _check_builtin_name_danger(child, ctx, _line, _sym)
    else:
        _check_bound_name_danger(_mod, _sym, child, ctx, _line)
def _check_builtin_name_danger(child: ast.Call, ctx: _FuzzContext,
                               _line: int, name: str | None = None) -> None:
    _name = name or child.func.id
    if _name == 'input':
        if not ctx.in_cli_context:
            ctx.add("danger_pattern", "input", "medium", _line)
    elif _name in _EVAL_EXEC_NAMES:
        ctx.add("security_pattern", "eval_exec", "high", _line)
def _check_bound_name_danger(_mod: str, _sym: str, child: ast.Call,
                             ctx: _FuzzContext, _line: int) -> None:
    if _mod in _CMD_OWNER_MODULES:
        _check_bound_exec_name_danger(_mod, _sym, child, ctx, _line)
    elif _mod in ('pickle', 'marshal', 'yaml'):
        _check_bound_deser_name_danger(_mod, _sym, child, ctx, _line)
    elif _mod == 'sys' and _sym == 'exit':
        if not ctx.in_cli_context and id(child) not in ctx.cli_guard_ids:
            ctx.add("danger_pattern", "sys_exit", "medium", _line)
    elif (_mod == 'os.path' and _sym == 'join'
          and _path_join_tainted(child, ctx.func_node, ctx)):
        ctx.add("security_pattern", "path_traversal_join", "medium", _line)
def _check_bound_exec_name_danger(_mod: str, _sym: str, child: ast.Call,
                                  ctx: _FuzzContext, _line: int) -> None:
    if _mod == 'os' and _sym == 'system':
        ctx.add("security_pattern", "cmd_injection_var", "high", _line)
    elif (_mod == 'subprocess' and _sym in SHELL_CALL_ATTRS
            and has_shell_true_kw(child)):
        ctx.add("security_pattern", "cmd_injection_shell", "high", _line)
def _check_bound_deser_name_danger(_mod: str, _sym: str, child: ast.Call,
                                  ctx: _FuzzContext, _line: int) -> None:
    if _mod in ('pickle', 'marshal') and _sym in _DESER_LOAD_ATTRS:
        ctx.add("security_pattern", f"{_mod}_load", "medium", _line)
    elif _mod == 'yaml' and yaml_call_is_unsafe(
            _sym, child, ctx.binds, ctx.index):
        ctx.add("security_pattern", "yaml_unsafe", "medium", _line)
def _is_static_sql_expression(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return True
    if isinstance(node, ast.JoinedStr):
        return all(isinstance(value, ast.Constant) for value in node.values)
    return (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)
            and _is_static_sql_expression(node.left)
            and _is_static_sql_expression(node.right))
def _sql_arg_injection_kind(child: ast.Call) -> str | None:
    if not child.args:
        return None
    a0 = child.args[0]
    if isinstance(a0, ast.JoinedStr):
        return (None if _is_static_sql_expression(a0)
                else "sql_injection_fstring")
    if isinstance(a0, ast.BinOp) and isinstance(a0.op, ast.Add):
        return (None if _is_static_sql_expression(a0)
                else "sql_injection_concat")
    return None
def _path_join_owner_name(child: ast.Call, ctx) -> str | None:
    func = child.func
    if isinstance(func, ast.Name):
        return (func.id if ctx.binds.from_binds.get(func.id)
                == ('os.path', 'join') else None)
    if not isinstance(func, ast.Attribute) or func.attr != 'join':
        return None
    owner = func.value
    if (isinstance(owner, ast.Name)
            and owner.id in ctx.binds.os_path_names):
        return owner.id
    if (isinstance(owner, ast.Attribute) and owner.attr == 'path'
            and isinstance(owner.value, ast.Name)
            and owner.value.id in ctx.binds.os_names):
        return owner.value.id
    return None
def _path_join_tainted(child: ast.Call, func_node: ast.AST, ctx) -> bool:
    owner_name = _path_join_owner_name(child, ctx)
    if (owner_name is None
            or ctx.index._name_is_shadowed(child, owner_name, False)):
        return False
    tainted_names = _fn_tainted_names(func_node)
    return any(_node_taint_hit(arg, tainted_names) for arg in child.args)
_RECEIVER_AGNOSTIC_ATTRS = frozenset({
    'execute', 'executemany', 'join', 'parse_args'})
def _check_receiver_agnostic_attr(attr: str, child: ast.Call,
                                  ctx: _FuzzContext, _line: int) -> None:
    if attr == 'parse_args':
        if not ctx.in_cli_context:
            ctx.add("danger_pattern", "argparse_parse", "medium", _line)
        return
    _check_attr_injection_danger(attr, child, ctx, _line)
def _check_call_attr_danger(child: ast.Call, ctx: _FuzzContext,
                            _line: int) -> None:
    fnode = child.func
    _owner_node = fnode.value
    owner_is = _owner_node.id if isinstance(_owner_node, ast.Name) else None
    attr = fnode.attr
    if attr in _RECEIVER_AGNOSTIC_ATTRS:
        _check_receiver_agnostic_attr(attr, child, ctx, _line)
        return
    if _call_name_is_shadowed(child, ctx.index):
        return
    if (attr in _BUILTIN_RISK_NAMES
            and owner_is in ctx.binds.builtins_names):
        _check_builtin_name_danger(child, ctx, _line, attr)
    elif (attr == 'exit' and owner_is in ctx.binds.sys_names
            and not ctx.in_cli_context
            and id(child) not in ctx.cli_guard_ids):
        ctx.add("danger_pattern", "sys_exit", "medium", _line)
    elif attr in _YAML_DISPATCH_SYMBOLS:
        _check_attr_deser_danger(attr, owner_is, child, ctx, _line)
    elif attr == 'system' or attr in SHELL_CALL_ATTRS:
        _check_attr_exec_danger(attr, owner_is, child, ctx, _line)
def _check_attr_deser_danger(attr: str, owner_is: str | None, child: ast.Call,
                             ctx: _FuzzContext, _line: int) -> None:
    if attr in _DESER_LOAD_ATTRS:
        if owner_is in ctx.binds.pickle_names:
            ctx.add("security_pattern", "pickle_load", "medium", _line)
        elif owner_is in ctx.binds.marshal_names:
            ctx.add("security_pattern", "marshal_load", "medium", _line)
    if (owner_is in ctx.binds.yaml_names
            and yaml_call_is_unsafe(attr, child, ctx.binds, ctx.index)):
        ctx.add("security_pattern", "yaml_unsafe", "medium", _line)
def _check_attr_exec_danger(attr: str, owner_is: str | None, child: ast.Call,
                            ctx: _FuzzContext, _line: int) -> None:
    if attr == 'system' and owner_is in ctx.binds.os_names:
        ctx.add("security_pattern", "cmd_injection_var", "high", _line)
    elif (attr in SHELL_CALL_ATTRS and owner_is in ctx.binds.sp_names
            and has_shell_true_kw(child)):
        ctx.add("security_pattern", "cmd_injection_shell", "high", _line)
def _check_attr_injection_danger(attr: str, child: ast.Call,
                                 ctx: _FuzzContext, _line: int) -> None:
    if attr in ('execute', 'executemany'):
        _sql_kind = _sql_arg_injection_kind(child)
        if _sql_kind:
            ctx.add("security_pattern", _sql_kind, "high", _line)
    elif attr == 'join' and _path_join_tainted(child, ctx.func_node, ctx):
        ctx.add("security_pattern", "path_traversal_join", "medium", _line)
def _fuzz_scope_nodes(node):
    stack = list(reversed(getattr(node, 'body', None) or ()))
    while stack:
        cur = stack.pop()
        yield cur
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            stack.extend(reversed(definition_time_expressions(cur)))
            continue
        if isinstance(cur, ast.ClassDef):
            stack.extend(reversed(
                [*definition_time_expressions(cur), *cur.body]))
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))
def _fuzz_scan_entry(entry, risk_findings: list) -> int:
    if is_test_file_path(entry.rel_path or ''):
        return 0
    rel_path = entry.rel_path
    _base = os.path.basename(entry.path)
    is_cli_file = _is_cli_entry_file(_base)
    cli_entry_names = _main_guard_called_names(entry.tree) | set(
        _CLI_ENTRY_NAMES)
    scope_index = ScopeIndex(entry.tree)
    _lines = entry_source_lines(entry)
    cli_guard_ids = main_guard_node_ids(entry.tree)
    tested = 0
    _reported_node_ids: set[int] = set()
    for func_node in entry_nodes(entry):
        if not isinstance(func_node, (ast.Module, ast.FunctionDef,
                                      ast.AsyncFunctionDef)):
            continue
        is_module = isinstance(func_node, ast.Module)
        if not is_module:
            tested += 1
        ctx = _FuzzContext(
            func_node=func_node,
            is_cli_entry=(is_cli_file or getattr(func_node, 'name', '')
                          in cli_entry_names),
            binds=scope_index.binds_for(None if is_module else func_node),
            index=scope_index,
            add=_make_finding_adder(
                func_node, rel_path, risk_findings, _lines),
            cli_guard_ids=cli_guard_ids,
        )
        for child in _fuzz_scope_nodes(func_node):
            if isinstance(child, (ast.Call, ast.While)):
                if id(child) in _reported_node_ids:
                    continue
                _reported_node_ids.add(id(child))
            child_ctx = (replace(
                ctx, binds=scope_index.binds_for_call(child))
                         if isinstance(child, ast.Call) else ctx)
            _scan_child_danger(child, child_ctx)
    return tested
def _make_finding_adder(func_node: ast.AST, rel_path: str,
                        risk_findings: list,
                        source_lines: list | None = None) -> _FindingAdder:
    seen: set = set()
    _lines = source_lines or []
    scope_name = getattr(func_node, 'name', '<module>')
    def _add(kind, pattern_name, severity, line):
        if line_suppressed_at(line, _lines, pattern_name):
            return
        key = (scope_name, pattern_name, line)
        if key in seen:
            return
        seen.add(key)
        risk_findings.append({
            "file": rel_path,
            "function": scope_name,
            "type": kind,
            "pattern": pattern_name,
            "line": line,
            "severity": severity,
            "message": (f"函数 {scope_name} 包含危险模式: {pattern_name}"
                        if kind == "danger_pattern"
                        else f"函数 {scope_name} 潜在安全漏洞: {pattern_name}"),
        })
    return _add
def _invalid_ast_entries(cache, *, include_tests: bool = False) -> list:
    entries = list(getattr(cache, 'entries', ()) or ())
    if include_tests:
        entries.extend(getattr(cache, 'test_dir_entries', ()) or ())
    return [entry for entry in entries
            if getattr(entry, 'parse_error', None)
            or getattr(entry, 'tree', None) is None]
def _invalid_ast_result(result: TestMethodResult, invalid_entries: list,
                        start: float) -> TestMethodResult:
    invalid_files = [
        {
            'file': (getattr(entry, 'rel_path', '')
                     or getattr(entry, 'path', '')),
            'error': str(getattr(entry, 'parse_error', None)
                         or '缺少可遍历的 AST'),
        }
        for entry in invalid_entries
    ]
    result.status = 'error'
    result.score = 0
    result.error = '; '.join(
        f"{item['file']}: {item['error']}" for item in invalid_files)
    result.metrics = {'invalid_files': invalid_files}
    result.summary = f'AST安全分析未完成: {len(invalid_files)} 个文件无法解析'
    return result.finish(start)
def run_fuzz_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name="模糊测试",
        method_id="fuzz_test",
    )
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        return TestMethodResult.invalid_input(
            skill_dir, "模糊测试", "fuzz_test", "扫描", start)
    invalid_entries = _invalid_ast_entries(cache)
    if invalid_entries:
        return _invalid_ast_result(result, invalid_entries, start)
    functions_tested = 0
    risk_findings = []
    for entry in cache.valid_entries:
        functions_tested += _fuzz_scan_entry(entry, risk_findings)
    result.findings = risk_findings
    result.metrics = {
        "functions_analyzed": functions_tested,
        "danger_patterns_found": len(risk_findings),
        "mode": "ast_safety_analysis",
    }
    result.status = "pass" if not risk_findings else "warn"
    result.score = max(60, 100 - len(risk_findings) * 5)
    result.summary = f"AST安全分析: {functions_tested} 函数, {len(risk_findings)} 危险模式"
    result.finish(start)
    return result
def _pickle_import_bindings(node: ast.Import, module_names: set[str]) -> None:
    for alias in node.names:
        if alias.asname:
            if alias.name == "pickle":
                module_names.add(alias.asname)
        elif (alias.name == "pickle"
                or alias.name.startswith("pickle.")):
            module_names.add("pickle")
def _pickle_fromimport_bindings(node: ast.ImportFrom, bare_names: set[str]) -> None:
    if node.module != "pickle" or node.level:
        return
    for alias in node.names:
        if alias.name == "*":
            bare_names.update(("load", "loads"))
        elif alias.name in ("load", "loads"):
            bare_names.add(alias.asname or alias.name)
def _collect_pickle_bindings(
        tree: ast.AST | None) -> tuple[set[str], set[str]]:
    module_names: set[str] = set()
    bare_names: set[str] = set()
    if tree is None:
        return module_names, bare_names
    for node in iter_direct_scope_nodes(tree):
        if isinstance(node, ast.Import):
            _pickle_import_bindings(node, module_names)
        elif isinstance(node, ast.ImportFrom):
            _pickle_fromimport_bindings(node, bare_names)
    return module_names, bare_names
def _collect_builtin_eval_bindings(
        scope: ast.AST | None) -> tuple[set[str], set[str]]:
    module_names: set[str] = set()
    bare_names: set[str] = set()
    if scope is None:
        return module_names, bare_names
    for node in iter_direct_scope_nodes(scope):
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name in _BUILTINS_MODULE_NAMES:
                    module_names.add(alias.asname or alias.name)
        elif (isinstance(node, ast.ImportFrom) and not node.level
              and node.module in _BUILTINS_MODULE_NAMES):
            for alias in node.names:
                if alias.name == '*':
                    bare_names.update(_EVAL_EXEC_NAMES)
                elif alias.name in _EVAL_EXEC_NAMES:
                    bare_names.add(alias.asname or alias.name)
    return module_names, bare_names
def _match_pickle_load(node: ast.AST, pickle_mods: set[str],
                       pickle_bares: set[str]) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    if isinstance(func, ast.Attribute):
        return (func.attr in _DESER_LOAD_ATTRS
                and isinstance(func.value, ast.Name)
                and func.value.id in pickle_mods)
    return isinstance(func, ast.Name) and func.id in pickle_bares
def _collect_shell_bare_bindings(tree: ast.AST | None) -> set[str]:
    names: set[str] = set()
    if tree is None:
        return names
    for node in iter_direct_scope_nodes(tree):
        if not (isinstance(node, ast.ImportFrom)
                and node.module == 'subprocess' and not node.level):
            continue
        for alias in node.names:
            if alias.name == '*':
                names.update(SHELL_CALL_ATTRS)
            elif alias.name in SHELL_CALL_ATTRS:
                names.add(alias.asname or alias.name)
    return names
def _collect_subprocess_module_bindings(tree: ast.AST | None) -> set[str]:
    names: set[str] = set()
    if tree is None:
        return names
    for node in iter_direct_scope_nodes(tree):
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            if alias.name == 'subprocess':
                names.add(alias.asname or 'subprocess')
            elif not alias.asname and alias.name.startswith('subprocess.'):
                names.add('subprocess')
    return names
def _match_shell_true(node: ast.AST, bare_names: set[str],
                      module_names: set[str]) -> bool:
    if not (isinstance(node, ast.Call) and has_shell_true_kw(node)):
        return False
    func = node.func
    if isinstance(func, ast.Attribute):
        return (func.attr in SHELL_CALL_ATTRS
                and isinstance(func.value, ast.Name)
                and func.value.id in module_names)
    return isinstance(func, ast.Name) and func.id in bare_names
_SECURITY_BINDING_KEYS = (
    'pickle_mods', 'pickle_bares', 'shell_mods', 'shell_bares',
    'builtins_mods', 'eval_bares',
)
def _empty_security_bindings() -> dict[str, set[str]]:
    return {key: set() for key in _SECURITY_BINDING_KEYS}
def _collect_scope_security_imports(scope: ast.AST) -> dict[str, set[str]]:
    bindings = _empty_security_bindings()
    bindings['pickle_mods'], bindings['pickle_bares'] = (
        _collect_pickle_bindings(scope))
    bindings['shell_mods'] = _collect_subprocess_module_bindings(scope)
    bindings['shell_bares'] = _collect_shell_bare_bindings(scope)
    bindings['builtins_mods'], bindings['eval_bares'] = (
        _collect_builtin_eval_bindings(scope))
    return bindings
def _security_import_event_bindings(node: ast.AST) -> dict[str, set[str]]:
    visible_nodes = _filter_overridden_imports([node])
    if not visible_nodes:
        return _empty_security_bindings()
    wrapper = ast.Module(body=visible_nodes, type_ignores=[])
    return _collect_scope_security_imports(wrapper)
def _security_event_index(scopes: set, binding_events: dict) -> tuple[dict, dict]:
    event_imports: dict = {}
    name_events: dict = {}
    for scope in scopes:
        per_name: dict[str, list] = defaultdict(list)
        for position, node in binding_events.get(scope, ()):
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                imported = _security_import_event_bindings(node)
                event_imports[id(node)] = imported
                names, _star = import_binding_names(node)
                for bound_names in imported.values():
                    names.update(bound_names)
            else:
                names = set()
                declared_outer = set()
                collect_scope_binding_names(node, names, declared_outer)
                names.update(declared_outer)
            for name in names:
                per_name[name].append((position, node))
        name_events[scope] = {
            name: (tuple(position for position, _node in events),
                   tuple(node for _position, node in events))
            for name, events in per_name.items()
        }
    return event_imports, name_events
def _shadowed_name(names: set[str], name: str,
                   include_star: bool) -> bool:
    return name in names or (include_star and '*' in names)
def _comprehension_namedexpr_nodes(scope: ast.AST):
    if isinstance(scope, _COMP_SCOPE_TYPES):
        return
    stack = list(_scope_body(scope))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            continue
        if isinstance(node, _COMP_SCOPE_TYPES):
            comp_stack = [node]
            while comp_stack:
                cur = comp_stack.pop()
                if isinstance(cur, ast.Lambda):
                    continue
                if (isinstance(cur, ast.NamedExpr)
                        and isinstance(cur.target, ast.Name)):
                    yield cur
                comp_stack.extend(ast.iter_child_nodes(cur))
            continue
        stack.extend(ast.iter_child_nodes(node))
def _comprehension_namedexpr_names(scope: ast.AST) -> set[str]:
    return {node.target.id for node in _comprehension_namedexpr_nodes(scope)}
def _scope_shadow_names(scope: ast.AST,
                        shadow_imports: bool) -> set[str]:
    names: set[str] = set()
    imported: set[str] = set()
    declared_outer: set[str] = set()
    star_import = False
    is_comp_scope = isinstance(scope, _COMP_SCOPE_TYPES)
    for node in iter_direct_scope_nodes(scope):
        if is_comp_scope and isinstance(node, ast.NamedExpr):
            continue
        collect_scope_binding_names(node, names, declared_outer)
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            _bound, _star = import_binding_names(node)
            imported.update(_bound)
            star_import = star_import or _star
    names |= collect_param_names(scope)
    names |= _comprehension_namedexpr_names(scope)
    if shadow_imports:
        names |= imported
    if star_import:
        names.add('*')
    return names - declared_outer
def _security_scope_index(tree: ast.Module | None) -> dict:
    if tree is None:
        return {'tree': None, 'parents': {}, 'scopes': set(),
                'imports': {}, 'shadows': {}, 'non_import_shadows': {},
                'binding_positions': {}, 'binding_events': {},
                'event_imports': {}, 'name_events': {}, 'visible_imports': {},
                'ordered_shadows': {}, 'bindings': {}, 'shadowed': {}}
    nodes = shared_walk(tree)
    parents = _parent_map(nodes)
    scopes = {tree} | {node for node in nodes
                       if isinstance(node, _LEXICAL_SCOPE_TYPES)}
    binding_positions, binding_events = _binding_event_maps(scopes)
    event_imports, name_events = _security_event_index(scopes, binding_events)
    return {
        'tree': tree,
        'parents': parents,
        'scopes': scopes,
        'imports': {scope: _collect_scope_security_imports(scope)
                    for scope in scopes},
        'shadows': {scope: _scope_shadow_names(scope, True)
                    for scope in scopes},
        'non_import_shadows': {scope: _scope_shadow_names(scope, False)
                               for scope in scopes},
        'binding_positions': binding_positions,
        'binding_events': binding_events,
        'event_imports': event_imports,
        'name_events': name_events,
        'visible_imports': {},
        'ordered_shadows': {},
        'bindings': {},
        'shadowed': {},
    }
def _security_scope_before_position(scope: ast.AST, node: ast.AST,
                                    index: dict) -> tuple[int, int]:
    before_position = _ordered_shadow_position(
        scope, node, index['parents'], index['binding_positions'])
    if before_position is None:
        events = index['binding_events'][scope]
        return events[-1][0] if events else (0, 0)
    return before_position
def _security_scope_shadow_names(scope: ast.AST, shadow_imports: bool,
                                 node: ast.AST, index: dict) -> set[str]:
    if not isinstance(scope, _ORDERED_BINDING_SCOPE_TYPES):
        key = 'shadows' if shadow_imports else 'non_import_shadows'
        return index[key][scope]
    before_position = _security_scope_before_position(scope, node, index)
    return _ordered_shadow_names(
        scope, shadow_imports, before_position,
        index['binding_events'][scope], index['ordered_shadows'])
def _security_scope_imports(scope: ast.AST, node: ast.AST,
                            index: dict) -> dict[str, set[str]]:
    if not isinstance(scope, _ORDERED_BINDING_SCOPE_TYPES):
        return index['imports'][scope]
    before = _security_scope_before_position(scope, node, index)
    cache_key = (id(scope), before)
    cached = index['visible_imports'].get(cache_key)
    if cached is not None:
        return cached
    visible = _empty_security_bindings()
    for key, candidates in index['imports'][scope].items():
        for name in candidates:
            positions, nodes = index['name_events'][scope].get(name, ((), ()))
            event_index = bisect_right(positions, before)
            if not event_index:
                continue
            latest_node = nodes[event_index - 1]
            imported = index['event_imports'].get(id(latest_node))
            if imported is not None and name in imported[key]:
                visible[key].add(name)
    index['visible_imports'][cache_key] = visible
    return visible
def _scoped_security_bindings(node: ast.AST, index: dict) -> dict[str, set[str]]:
    memo = index['bindings']
    node_key = id(node)
    cached = memo.get(node_key)
    if cached is not None:
        return cached
    visible = _empty_security_bindings()
    blocked = _empty_security_bindings()
    scope = _nearest_scope(node, index['parents'], index['scopes'], index['tree'])
    while scope is not None:
        imports = _security_scope_imports(scope, node, index)
        shadows = _security_scope_shadow_names(scope, True, node, index)
        non_import_shadows = _security_scope_shadow_names(
            scope, False, node, index)
        for key in _SECURITY_BINDING_KEYS:
            hidden = non_import_shadows | (shadows - imports[key])
            visible_imports = imports[key]
            if isinstance(scope, _ORDERED_BINDING_SCOPE_TYPES):
                visible_imports = visible_imports & shadows
            visible[key].update(visible_imports - blocked[key] - hidden)
            blocked[key].update(hidden)
        scope = _enclosing_scope(scope, index['parents'], index['scopes'])
    memo[node_key] = visible
    return visible
def _security_name_shadowed(name: str, node: ast.AST, index: dict) -> bool:
    memo = index['shadowed']
    key = (id(node), name)
    cached = memo.get(key)
    if cached is not None:
        return cached
    scope = _nearest_scope(node, index['parents'], index['scopes'], index['tree'])
    while scope is not None:
        shadows = _security_scope_shadow_names(scope, True, node, index)
        if name in shadows or '*' in shadows:
            memo[key] = True
            return True
        scope = _enclosing_scope(scope, index['parents'], index['scopes'])
    memo[key] = False
    return False
def _match_scoped_eval_exec(node: ast.AST, index: dict) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    bindings = _scoped_security_bindings(node, index)
    if isinstance(func, ast.Name):
        if func.id in bindings['eval_bares']:
            return True
        return (func.id in _EVAL_EXEC_NAMES
                and not _security_name_shadowed(func.id, node, index))
    return (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id in bindings['builtins_mods']
            and func.attr in _EVAL_EXEC_NAMES)
def _match_scoped_pickle_load(node: ast.AST, index: dict) -> bool:
    bindings = _scoped_security_bindings(node, index)
    return _match_pickle_load(
        node, bindings['pickle_mods'], bindings['pickle_bares'])
def _match_scoped_shell_true(node: ast.AST, index: dict) -> bool:
    bindings = _scoped_security_bindings(node, index)
    return _match_shell_true(
        node, bindings['shell_bares'], bindings['shell_mods'])
_CRED_VALUE_MIN_LEN = 4
def match_hardcoded_secret(node: ast.AST) -> bool:
    parts = _assignment_targets_value(node)
    if parts is None:
        return False
    targets, value = parts
    lineno = getattr(node, "lineno", 0)
    for target in targets:
        # 与 SE-03 共用标准配对：支持元组/列表/星号解包，按位置对齐目标名与值，
        # 否则 `user, password = "root", "..."` 的 password 目标会被整体跳过。
        for name, pair_value, _pair_lineno in _se03_pairs_for_target(
                target, value, lineno):
            if not (isinstance(pair_value, ast.Constant)
                    and isinstance(pair_value.value, str)
                    and len(pair_value.value) >= _CRED_VALUE_MIN_LEN):
                continue
            if not _CREDENTIAL_NAME_RE.search(name):
                continue
            # 与 SE-03 共用同一非凭据排除：占位值/模板串（changeme、${VAR}、
            # xxxxxxxx）、正则模式常量（如 *_TAIL = r"\s*\(.*?password"）、规则名
            # 常量——目标名带凭据词但值不是硬编码凭据。
            if (is_placeholder_secret(pair_value.value)
                    or is_regex_pattern_text(pair_value.value)
                    or is_rule_name_constant(pair_value.value, [name])):
                continue
            return True
    return False
def _security_patterns(tree: ast.Module | None) -> dict:
    scope_index = _security_scope_index(tree)
    return {
        "hardcoded_secret": {
            "check": match_hardcoded_secret,
            "severity": "high",
            "message": "硬编码密钥/凭证检测",
        },
        "eval_exec": {
            "check": lambda node: _match_scoped_eval_exec(node, scope_index),
            "severity": "high",
            "message": "危险函数 eval/exec 调用",
        },
        "pickle_load": {
            "check": lambda node: _match_scoped_pickle_load(node, scope_index),
            "severity": "high",
            "message": "不安全的 pickle 反序列化",
        },
        "shell_true": {
            "check": lambda node: _match_scoped_shell_true(node, scope_index),
            "severity": "medium",
            "message": "subprocess shell=True 存在命令注入风险",
        },
    }
def _security_inline_suppressed(entry, pattern_name: str, lineno: int) -> bool:
    rule_ids = _suppression_spec(pattern_name)[1]
    filepath = getattr(entry, 'path', '') or ''
    if not rule_ids or not filepath:
        return False
    return any(has_inline_suppression(filepath, lineno, rule_id)
               for rule_id in rule_ids)
def _scan_entry_security(entry, patterns: dict
                         ) -> tuple[list[dict], list[tuple[str, int]]]:
    rel_path = entry.rel_path
    in_tests = is_test_file_path(rel_path)
    source_lines = entry_source_lines(entry)
    entry_findings: list[dict] = []
    fixture_hits: list[tuple[str, int]] = []
    for node in nodes_where(
            entry, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                    ast.NamedExpr, ast.Call)):
        for pattern_name, pattern_info in patterns.items():
            kind, payload = _security_pattern_outcome(
                node, pattern_name, pattern_info, rel_path,
                entry, source_lines, in_tests)
            if kind == "finding":
                entry_findings.append(payload)
            elif kind == "fixture":
                fixture_hits.append(payload)
    return entry_findings, fixture_hits
def _security_pattern_outcome(node, pattern_name: str, pattern_info: dict,
                              rel_path: str, entry, source_lines,
                              in_tests: bool):
    if not pattern_info["check"](node):
        return "skip", None
    lineno = getattr(node, "lineno", 0)
    if line_suppressed_at(lineno, source_lines, pattern_name):
        return "skip", None
    if _security_inline_suppressed(entry, pattern_name, lineno):
        return "skip", None
    if in_tests:
        return "fixture", (f"SEC-{pattern_name}", lineno)
    return "finding", {
        "type": f"SEC-{pattern_name}",
        "severity": pattern_info["severity"],
        "file": rel_path,
        "line": lineno,
        "message": pattern_info["message"],
    }
def run_security_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name="安全测试",
        method_id="security_test",
    )
    cache = resolve_file_cache(skill_dir, kwargs)
    if cache is None:
        return TestMethodResult.invalid_input(
            skill_dir, "安全测试", "security_test", "安全检查", start)
    invalid_entries = _invalid_ast_entries(cache, include_tests=True)
    if invalid_entries:
        return _invalid_ast_result(result, invalid_entries, start)
    try:
        findings, fixture_hits_all = _collect_security_findings(cache)
    except Exception as exc:  # noqa: BLE001 - 扫描异常必须转换为失败结果
        _log.warning("安全测试模式检查中断: %s", exc, exc_info=True)
        result.status = "error"
        result.score = 0
        result.error = f"{type(exc).__name__}: {exc}"
        result.summary = "安全测试未完成: AST 安全模式检查异常"
        return result.finish(start)
    _apply_security_verdict(result, findings, fixture_hits_all)
    return finalize_test_result(result, cache, start)
def _collect_security_findings(cache
                               ) -> tuple[list[dict], dict[str, list[tuple[str, int]]]]:
    findings: list[dict] = []
    fixture_hits_all: dict[str, list[tuple[str, int]]] = {}
    entries = [*cache.entries, *(cache.test_dir_entries or ())]
    for entry in entries:
        if entry.parse_error or not entry.tree:
            continue
        entry_findings, fixture_hits = _scan_entry_security(
            entry, _security_patterns(entry.tree))
        findings.extend(entry_findings)
        if fixture_hits:
            fixture_hits_all.setdefault(entry.rel_path, []).extend(fixture_hits)
    return findings, fixture_hits_all
def _apply_security_verdict(result: TestMethodResult, findings: list[dict],
                            fixture_hits_all: dict[str, list[tuple[str, int]]]) -> None:
    if fixture_hits_all:
        _log.info("[T-SEC] 测试夹具样本命中 %d 处（tests/ 正/负样本，不入 findings，"
                  "人工复核详见 metrics.test_fixture_hits）",
                  sum(len(v) for v in fixture_hits_all.values()))
    counts = severity_tally(findings)
    result.findings = findings
    result.metrics = {
        "test_fixture_hits": fixture_hits_all,
        "total_findings": len(findings),
        "high_severity": counts["high"],
        "medium_severity": counts["medium"],
        "low_severity": counts["low"],
    }
    status, score = graded_status_score(counts, len(findings), low_penalty=2)
    result.status = status
    result.score = score
    if not findings:
        result.summary = "未检测到 AST 级安全风险"
    elif counts["high"] > 0:
        result.summary = f"检测到 {len(findings)} 个安全问题（{counts['high']} 个高危）"
    else:
        result.summary = f"检测到 {len(findings)} 个中危安全问题"

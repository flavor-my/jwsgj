from __future__ import annotations

import ast
import logging
from collections import deque
from collections.abc import Iterator
from typing import NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    SHADOW_SCOPE_STOP,
    TRY_NODE_TYPES,
    collect_param_names,
    definition_time_exprs,
    dotted_name,
    in_subtree,
    iter_arg_nodes,
    iter_own_nodes,
    iter_pattern_capture_names,
    iter_scope_nodes,
    iter_unpack_target_names,
    module_postpones_annotations,
    node_position,
)
from jwsgj.diag_shared_ast_views import (
    collect_module_bindings,
    scope_import_tables,
    scope_node_bound_names,
    tree_nodes,
)
from jwsgj.diag_shared_ast_views import (
    parent_map as _shared_parent_map,
)
from jwsgj.diag_types_defs import DiagnoseFinding, finding_scan_exempt
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger(__name__)
__all__ = [
    "check_CL01", "check_DT01", "check_TH01",
]
_DEFAULT_FILEPATH = ""
def _scope_definition_guard(scope: ast.AST, node: ast.AST) -> bool:
    if isinstance(scope, ast.ClassDef):
        bases = [*scope.bases, *(kw.value for kw in scope.keywords)]
        head = [*scope.decorator_list, *bases]
        return any(in_subtree(node, expr) for expr in head)
    if isinstance(scope, (*_FUNCTION_NODES, ast.Lambda)):
        if in_subtree(node, scope.args):
            return True
        decorators = getattr(scope, "decorator_list", ())
        if any(in_subtree(node, dec) for dec in decorators):
            return True
        returns = getattr(scope, "returns", None)
        return returns is not None and in_subtree(node, returns)
    return False
_FUNCTION_NODES = (ast.FunctionDef, ast.AsyncFunctionDef)
_SCOPE_NODES = (*_FUNCTION_NODES, ast.Lambda, ast.ClassDef)
def _scope_with_binding_targets(stmt: ast.AST):
    for item in stmt.items:
        if item.optional_vars is not None:
            yield item.optional_vars
class _ScopeModel:
    _SCOPE_TYPES = (*_SCOPE_NODES, *COMP_SCOPE_NODES)
    def __init__(self, tree: ast.AST) -> None:
        self.tree = tree
        self._parent_map: dict[ast.AST, ast.AST] = {}
        self._assigned: dict[ast.AST, set[str]] = {}
        self._shadow_bound: dict[ast.AST, set[str]] = {}
        self._global_decl: dict[ast.AST, set[str]] = {}
        self._nonlocal_decl: dict[ast.AST, set[str]] = {}
        self.seq_names: dict[
            tuple[ast.AST, str],
            list[tuple[_DT01Binding, frozenset[str], ast.AST]],
        ] = {}
    def build(self) -> None:
        self._parent_map = _shared_parent_map(self.tree)
        self.build_scope_bindings()
        self.build_seq_names()
    def enclosing_scope(self, node: ast.AST) -> ast.AST:
        cur = self._parent_map.get(node)
        while cur is not None and not isinstance(cur, self._SCOPE_TYPES):
            cur = self._parent_map.get(cur)
        return cur if cur is not None else self.tree
    def execution_scope(self, node: ast.AST) -> ast.AST:
        cur: ast.AST | None = node
        while cur is not None:
            if isinstance(cur, (*_SCOPE_NODES, ast.Module)):
                return cur
            cur = self._parent_map.get(cur)
        return self.tree
    def eval_scope(self, node: ast.AST) -> ast.AST:
        cur = node
        parent = self._parent_map.get(cur)
        while parent is not None:
            if isinstance(parent, self._SCOPE_TYPES):
                generators = getattr(parent, "generators", None)
                if generators and in_subtree(node, generators[0].iter):
                    cur = parent
                    parent = self._parent_map.get(parent)
                    continue
                if _scope_definition_guard(parent, node):
                    cur = parent
                    parent = self._parent_map.get(parent)
                    continue
                return parent
            if isinstance(parent, ast.Module):
                return parent
            cur = parent
            parent = self._parent_map.get(parent)
        return self.tree
    def owner_scope(self, node: ast.AST) -> ast.AST:
        cur: ast.AST | None = node
        while cur is not None:
            if isinstance(cur, (ast.ClassDef, ast.Module)):
                return cur
            cur = self._parent_map.get(cur)
        return self.tree
    def parent_scope(self, scope: ast.AST) -> ast.AST | None:
        if scope is self.tree:
            return None
        cur = self._parent_map.get(scope)
        while cur is not None:
            if isinstance(cur, (*_SCOPE_NODES, *COMP_SCOPE_NODES, ast.Module)):
                return cur
            cur = self._parent_map.get(cur)
        return None
    def shadow_bindings(self, scope: ast.AST) -> frozenset[str]:
        return frozenset(self._shadow_bound.get(scope, ()))
    def build_scope_bindings(self) -> None:
        _all_scopes: list[ast.AST] = [self.tree]
        for _p in tree_nodes(self.tree):
            if isinstance(_p, self._SCOPE_TYPES):
                _all_scopes.append(_p)
        for _scope in _all_scopes:
            if isinstance(_scope, COMP_SCOPE_NODES):
                _bound = self.comprehension_bindings(_scope)
                self._assigned[_scope] = _bound
                self._shadow_bound[_scope] = set(_bound)
                continue
            _names: set[str] = collect_param_names(_scope)
            _shadowed: set[str] = set(_names)
            for _stmt in iter_scope_nodes(_scope):
                if isinstance(_stmt, ast.Global):
                    self._global_decl.setdefault(
                        _scope, set()).update(_stmt.names)
                    continue
                if isinstance(_stmt, ast.Nonlocal):
                    self._nonlocal_decl.setdefault(
                        _scope, set()).update(_stmt.names)
                    continue
                _bound = scope_node_bound_names(_stmt)
                _names |= _bound
                if not isinstance(_stmt, (ast.Import, ast.ImportFrom)):
                    _shadowed |= _bound
            self._assigned[_scope] = _names
            self._shadow_bound[_scope] = _shadowed
        self.migrate_declared_bindings()
    @staticmethod
    def comprehension_bindings(scope: ast.AST) -> set[str]:
        _names: set[str] = set()
        for generator in scope.generators:
            _names.update(iter_unpack_target_names(generator.target))
        return _names
    def migrate_declared_bindings(self) -> None:
        for _scope, _gd in self._global_decl.items():
            if _scope is self.tree:
                continue
            self._assigned.setdefault(self.tree, set()).update(
                _gd & self._assigned.get(_scope, set()))
            self._shadow_bound.setdefault(self.tree, set()).update(
                _gd & self._shadow_bound.get(_scope, set()))
            self._assigned[_scope] -= _gd
            self._shadow_bound[_scope] -= _gd
        for _scope, _nl in self._nonlocal_decl.items():
            self._assigned[_scope] -= _nl
            self._shadow_bound[_scope] -= _nl
    def binding_scope(self, name: str, scope: ast.AST) -> ast.AST | None:
        cur: ast.AST | None = scope
        while cur is not None:
            is_outer_class = isinstance(cur, ast.ClassDef) and cur is not scope
            if not is_outer_class and name in self._assigned.get(cur, ()):
                return cur
            cur = self.parent_scope(cur)
        return None
    @staticmethod
    def is_all_name_seq(node: ast.AST) -> bool:
        return (isinstance(node, (ast.Tuple, ast.List))
                and all(isinstance(e, ast.Name) for e in node.elts))
    def _all_name_seq_target(self, node: ast.AST) -> ast.Name | None:
        if isinstance(node, ast.AnnAssign):
            target, value = node.target, node.value
        elif isinstance(node, ast.Assign) and len(node.targets) == 1:
            target, value = node.targets[0], node.value
        else:
            return None
        if value is not None and isinstance(target, ast.Name) \
                and self.is_all_name_seq(value):
            return target
        return None
    def build_seq_names(self) -> None:
        for _p in tree_nodes(self.tree):
            _target = self._all_name_seq_target(_p)
            if _target is None:
                continue
            _b = self.binding_scope(_target.id, self.enclosing_scope(_p))
            if _b is not None:
                event_scope = self.execution_scope(_p)
                binding = _DT01Binding(
                    "", node_position(_p), _p,
                    _dt01_branch_path(_p, self._parent_map, event_scope))
                self.seq_names.setdefault((_b, _target.id), []).append((
                    binding, frozenset(e.id for e in _p.value.elts),
                    event_scope,
                ))
    def src_elem_names(self, src: ast.AST, at: ast.AST) -> set[str] | None:
        if isinstance(src, ast.Name):
            _b = self.binding_scope(src.id, self.enclosing_scope(at))
            if _b is None:
                return None
            records = self.seq_names.get((_b, src.id))
            if records is None:
                return None
            operation_scope = self.execution_scope(at)
            operation_path = _dt01_branch_path(
                at, self._parent_map, operation_scope)
            elements: set[str] = set()
            for index, (candidate, names, event_scope) in enumerate(records):
                if event_scope is not operation_scope:
                    elements.update(names)
                    continue
                later = [event[0] for event in records[index + 1:]
                         if event[2] is operation_scope]
                if _dt01_reaching_worlds(
                        candidate, later, at, operation_path,
                        self._parent_map, operation_scope):
                    elements.update(names)
            return elements
        if self.is_all_name_seq(src):
            return {e.id for e in src.elts}
        return None
    def loop_source_elems(self, name: str, call: ast.Call) -> set[str] | None:
        cur = self._parent_map.get(call)
        while cur is not None:
            _elems = self.loop_target_elems(cur, name)
            if _elems is not None:
                return _elems
            cur = self._parent_map.get(cur)
        return None
    @staticmethod
    def comprehension_target_iter(
            comp: ast.AST, name: str) -> ast.AST | None:
        for gen in comp.generators:
            if isinstance(gen.target, ast.Name) and gen.target.id == name:
                return gen.iter
        return None
    def loop_target_elems(self, cur: ast.AST, name: str) -> set[str] | None:
        if (isinstance(cur, (ast.For, ast.AsyncFor))
                and isinstance(cur.target, ast.Name)
                and cur.target.id == name):
            return self.src_elem_names(cur.iter, cur)
        if isinstance(cur, COMP_SCOPE_NODES):
            _iter = self.comprehension_target_iter(cur, name)
            return self.src_elem_names(_iter, cur) if _iter is not None else None
        return None
    def binding_key(self, name_id: str, anchor: ast.AST) -> tuple[ast.AST, str] | None:
        _b = self.binding_scope(name_id, self.enclosing_scope(anchor))
        return (_b, name_id) if _b is not None else None
_TH01_DAEMON_SETTERS = frozenset({"setDaemon", "set_daemon"})
def _th01_truthy_flag(value: ast.AST) -> bool:
    if isinstance(value, ast.Constant):
        return bool(value.value)
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return bool(value.elts)
    if isinstance(value, ast.Dict):
        return bool(value.keys)
    return True
def _th01_collect_import_scopes(tree: ast.AST) -> set[tuple[ast.AST, str]]:
    return {
        (owner, name)
        for owner, table in scope_import_tables(tree).items()
        for name, binding in table.items()
        if binding[1] == "threading"
    }
def _th01_import_binding_target(node: ast.AST, name: str) -> str:
    if isinstance(node, ast.Import):
        for alias in node.names:
            bound = alias.asname or alias.name.split(".")[0]
            if bound == name:
                return "module" if alias.name == "threading" else ""
    elif isinstance(node, ast.ImportFrom):
        for alias in node.names:
            bound = alias.asname or alias.name
            if bound == name:
                return ("member" if not node.level
                        and node.module == "threading"
                        and alias.name == "Thread" else "")
    return ""
def _th01_ctor_daemon_kw(call: ast.Call) -> bool:
    return any(
        kw.arg == "daemon" and _th01_truthy_flag(kw.value)
        for kw in call.keywords)
def _th01_is_bindable_expr(expr: ast.AST) -> bool:
    return isinstance(expr, ast.Name) or (
        isinstance(expr, ast.Attribute) and bool(dotted_name(expr)))
def _th01_iter_binding_exprs(target: ast.AST) -> Iterator[ast.AST]:
    if _th01_is_bindable_expr(target):
        yield target
        return
    if isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            yield from _th01_iter_binding_exprs(element)
    elif isinstance(target, ast.Starred):
        yield from _th01_iter_binding_exprs(target.value)
def _th01_iter_assignment_pairs(
        target: ast.AST, value: ast.AST) -> Iterator[tuple[ast.AST, ast.AST]]:
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(element, ast.Starred)
                        for element in (*target.elts, *value.elts))):
        for target_element, value_element in zip(
                target.elts, value.elts, strict=True):
            yield from _th01_iter_assignment_pairs(
                target_element, value_element)
        return
    yield target, value
def _th01_bucket_add(bucket: dict, key: tuple[ast.AST, str] | None,
                     anchor: ast.Call) -> None:
    if key is not None:
        bucket.setdefault(key, []).append(anchor)
def _th01_event_constructor_index(
        constructors: list, event: ast.AST,
        reassigned: list[tuple[tuple[int, int], ast.AST]],
        scope: _ScopeModel) -> int | None:
    event_scope = scope.execution_scope(event)
    if _dt01_binding_blocks_reach(
            event, event, scope._parent_map, event_scope):
        return None
    event_pos = node_position(event)
    candidates = []
    for index, ctor in enumerate(constructors):
        if event_pos < ctor[0]:
            continue
        if (in_subtree(event, ctor[3])
                and scope.eval_scope(event) is scope.eval_scope(ctor[3])):
            continue
        candidates.append(index)
    if not candidates:
        return None
    index = max(candidates, key=lambda i: constructors[i][0])
    ctor_pos = constructors[index][0]
    if any(ctor_pos < pos < event_pos for pos, _node in reassigned):
        return None
    return index
def _th01_event_constructor_worlds(
        constructors: list, index: int, event: ast.AST,
        reassigned: list[tuple[tuple[int, int], ast.AST]],
        scope: _ScopeModel) -> list[_DT01Path]:
    event_scope = scope.execution_scope(event)
    ctor = constructors[index]
    if scope.execution_scope(ctor[3]) is not event_scope:
        legacy = _th01_event_constructor_index(
            constructors, event, reassigned, scope)
        return [frozenset()] if legacy == index else []
    if _dt01_binding_blocks_reach(
            event, event, scope._parent_map, event_scope):
        return []
    event_pos = node_position(event)
    if event_pos < ctor[0] or in_subtree(event, ctor[3]):
        return []
    parents = scope._parent_map
    candidate = _DT01Binding(
        "", ctor[0], ctor[3],
        _dt01_branch_path(ctor[3], parents, event_scope))
    killers: list[_DT01Binding] = []
    for other in constructors[index + 1:]:
        if ctor[0] < other[0] < event_pos:
            killers.append(_DT01Binding(
                "", other[0], other[3],
                _dt01_branch_path(other[3], parents, event_scope)))
    for position, node in reassigned:
        if ctor[0] < position < event_pos:
            killers.append(_DT01Binding(
                "", position, node,
                _dt01_branch_path(node, parents, event_scope)))
    killers.sort(key=lambda binding: binding.position)
    return _dt01_reaching_worlds(
        candidate, killers, event,
        _dt01_branch_path(event, parents, event_scope), parents, event_scope)
def _th01_apply_lifecycle_events(
        constructors: list, states: list[dict], events: list[ast.AST],
        field: str,
        reassigned: list[tuple[tuple[int, int], ast.AST]],
        scope: _ScopeModel) -> None:
    for event in events:
        for index in range(len(constructors)):
            if _th01_event_constructor_worlds(
                    constructors, index, event, reassigned, scope):
                states[index][field].append(event)
def _th01_event_precedes(scope: _ScopeModel, earlier: ast.AST,
                         later: ast.AST) -> bool:
    earlier_scope = scope.execution_scope(earlier)
    later_scope = scope.execution_scope(later)
    if earlier_scope is not later_scope:
        return True
    if node_position(earlier) >= node_position(later):
        return False
    parents = scope._parent_map
    earlier_path = _dt01_branch_path(earlier, parents, earlier_scope)
    later_path = _dt01_branch_path(later, parents, later_scope)
    return _dt01_paths_compatible(earlier_path, later_path)
def _th01_paths_cover(
        base_worlds: list[_DT01Path],
        cleanup_worlds: list[_DT01Path]) -> bool:
    if not base_worlds:
        return False
    paths = [*base_worlds, *cleanup_worlds]
    decisions = sorted({
        decision for path in paths for decision, _value in path})
    arity = _dt01_decision_arity(paths)
    world_count = 1
    for decision in decisions:
        world_count *= max(arity.get(decision, 2), 2)
    for base in base_worlds:
        if world_count <= 1024:
            uncovered = any(
                not any(_dt01_paths_compatible(world, cleanup)
                        for cleanup in cleanup_worlds)
                for world in _dt01_path_worlds(base, decisions, arity))
        else:
            blockers = [
                _DT01Binding("", (-1, -1), ast.Pass(), path)
                for path in cleanup_worlds
            ]
            uncovered = bool(_dt01_fallback_reaching_world(
                base, blockers, arity))
        if uncovered:
            return False
    return True
def _th01_daemon_candidate_worlds(
        scope: _ScopeModel, candidate: ast.AST, start: ast.AST,
        events: list[ast.AST], values: dict[ast.AST, bool],
        start_scope: ast.AST) -> list[_DT01Path]:
    parents = scope._parent_map
    def binding(node: ast.AST) -> _DT01Binding:
        return _DT01Binding(
            "", node_position(node), node,
            _dt01_branch_path(node, parents, start_scope))
    killers = [binding(event) for event in events if not values[event]]
    return _dt01_reaching_worlds(
        binding(candidate), killers, start,
        _dt01_branch_path(start, parents, start_scope), parents, start_scope)
class _TH01Checker:
    def __init__(self, tree: ast.AST, filepath: str) -> None:
        self.tree = tree
        self.filepath = filepath
        self.issues: list[DiagnoseFinding] = []
        _thread_mods, _thread_bare = collect_module_bindings(
            tree, 'threading', ('Thread',))
        self._thread_mods = _thread_mods
        self._thread_bare_names = _thread_bare
        self.constructors: dict[
            tuple[ast.AST, str],
            list[tuple[tuple[int, int], int, bool, ast.Call]],
        ] = {}
        self.started: dict[tuple[ast.AST, str], list[ast.Call]] = {}
        self.joined: dict[tuple[ast.AST, str], list[ast.Call]] = {}
        self.daemon_assigned: dict[tuple[ast.AST, str], list[ast.AST]] = {}
        self._daemon_event_values: dict[ast.AST, bool] = {}
        self.reassigned: dict[
            tuple[ast.AST, str],
            list[tuple[tuple[int, int], ast.AST]],
        ] = {}
        self._scope = _ScopeModel(tree)
        self._import_scopes: set[tuple[ast.AST, str]] = set()
        self._thread_aliases: dict[ast.AST, _DT01Aliases] = {}
    def _build_thread_aliases(self) -> None:
        tracked = self._thread_mods | set(self._thread_bare_names)
        grouped: dict[
            ast.AST, dict[str, list[_DT01AliasEvent]]] = {}
        parents = self._scope._parent_map
        for node in tree_nodes(self.tree):
            names = set(scope_node_bound_names(node))
            if isinstance(node, ast.Delete):
                names.update(
                    name for target in node.targets
                    for name in iter_unpack_target_names(target))
            for name in names & tracked:
                scope = self._scope.binding_scope(
                    name, self._scope.enclosing_scope(node))
                if scope is None:
                    continue
                position_node = node if hasattr(node, "lineno") else node.target
                grouped.setdefault(scope, {}).setdefault(name, []).append(
                    _DT01AliasEvent(
                        node_position(position_node),
                        _th01_import_binding_target(node, name), node,
                        _dt01_branch_path(node, parents, scope)))
        for scope, events_by_name in grouped.items():
            aliases = _DT01Aliases(scope, parents)
            for name, events in events_by_name.items():
                aliases[name] = sorted(
                    events, key=lambda event: event.position)
            self._thread_aliases[scope] = aliases
    def _thread_name_shadowed(
            self, name: str, call: ast.Call, expected: str) -> bool:
        scope = self._scope.binding_scope(name, self._scope.eval_scope(call))
        if scope is None:
            return False
        aliases = self._thread_aliases.get(scope)
        if aliases is not None and name in aliases:
            return _dt01_alias_at(aliases[name], call, aliases) != expected
        if name in self._scope.shadow_bindings(scope):
            return True
        return (scope, name) not in self._import_scopes
    def _is_thread_ctor(self, call: ast.Call) -> bool:
        func = call.func
        if isinstance(func, ast.Name):
            return (func.id in self._thread_bare_names
                    and not self._thread_name_shadowed(
                        func.id, call, "member"))
        return (isinstance(func, ast.Attribute) and func.attr == "Thread"
                and isinstance(func.value, ast.Name)
                and func.value.id in self._thread_mods
                and not self._thread_name_shadowed(
                    func.value.id, call, "module"))
    def _expr_binding_key(
        self, expr: ast.AST, anchor: ast.AST
    ) -> tuple[ast.AST, str] | None:
        if isinstance(expr, ast.Name):
            return self._scope.binding_key(expr.id, anchor)
        if isinstance(expr, ast.Attribute):
            _dotted = dotted_name(expr)
            if _dotted:
                return (self._scope.owner_scope(anchor), _dotted)
        return None
    def _is_ctor_binding(self, tgt: ast.AST, value: ast.AST) -> bool:
        return (_th01_is_bindable_expr(tgt) and isinstance(value, ast.Call)
                and self._is_thread_ctor(value))
    def _is_daemon_binding(self, tgt: ast.AST, value: ast.AST) -> bool:
        return (isinstance(tgt, ast.Attribute) and tgt.attr == "daemon"
                and _th01_is_bindable_expr(tgt.value))
    def _record_ctor_event(self, target: ast.AST, ctor_call: ast.Call,
                           anchor: ast.AST) -> None:
        _key = self._expr_binding_key(target, anchor)
        if _key is None:
            return
        self.constructors.setdefault(_key, []).append((
            node_position(ctor_call), ctor_call.lineno,
            _th01_ctor_daemon_kw(ctor_call), ctor_call,
        ))
    def _record_reassignment(self, target: ast.AST, anchor: ast.AST) -> None:
        key = self._expr_binding_key(target, anchor)
        self._record_reassignment_key(key, anchor)
    def _record_import_reassignment(
            self, node: ast.Import | ast.ImportFrom) -> None:
        for name in scope_node_bound_names(node):
            key = self._scope.binding_key(name, node)
            self._record_reassignment_key(key, node)
    def _record_reassignment_key(
            self, key: tuple[ast.AST, str] | None, anchor: ast.AST) -> None:
        if key is None:
            return
        end_pos = (
            anchor.end_lineno if anchor.end_lineno is not None else anchor.lineno,
            anchor.end_col_offset if anchor.end_col_offset is not None
            else anchor.col_offset,
        )
        self.reassigned.setdefault(key, []).append((end_pos, anchor))
    def _record_daemon_event(
            self, recv: ast.AST, anchor: ast.AST, enabled: bool) -> None:
        _key = self._expr_binding_key(recv, anchor)
        if _key is not None:
            self.daemon_assigned.setdefault(_key, []).append(anchor)
            self._daemon_event_values[anchor] = enabled
    def _record_assign_events(self, node: ast.Assign) -> None:
        for tgt in node.targets:
            for target, value in _th01_iter_assignment_pairs(tgt, node.value):
                if self._is_ctor_binding(target, value):
                    self._record_ctor_event(target, value, node)
                else:
                    for expression in _th01_iter_binding_exprs(target):
                        self._record_reassignment(expression, node)
                if self._is_daemon_binding(target, value):
                    self._record_daemon_event(
                        target.value, node, _th01_truthy_flag(value))
    def _record_annassign_events(self, node: ast.AnnAssign) -> None:
        if node.value is None:
            return
        if self._is_ctor_binding(node.target, node.value):
            self._record_ctor_event(node.target, node.value, node)
        elif _th01_is_bindable_expr(node.target):
            self._record_reassignment(node.target, node)
        if self._is_daemon_binding(node.target, node.value):
            self._record_daemon_event(
                node.target.value, node, _th01_truthy_flag(node.value))
    def _record_walrus_event(self, node: ast.NamedExpr) -> None:
        if self._is_ctor_binding(node.target, node.value):
            self._record_ctor_event(node.target, node.value, node)
        elif _th01_is_bindable_expr(node.target):
            self._record_reassignment(node.target, node)
    def _record_daemon_call_event(self, node: ast.Call) -> None:
        func = node.func
        if not (isinstance(func, ast.Attribute)
                and func.attr in _TH01_DAEMON_SETTERS
                and _th01_is_bindable_expr(func.value)
                and node.args):
            return
        self._record_daemon_event(
            func.value, node, _th01_truthy_flag(node.args[0]))
    def _start_join_event_keys(self, recv: ast.AST, node: ast.Call) -> list:
        if isinstance(recv, ast.Name):
            _elems = self._scope.loop_source_elems(recv.id, node)
            if _elems is not None:
                return [self._scope.binding_key(_e, node) for _e in _elems]
            return [self._scope.binding_key(recv.id, node)]
        if isinstance(recv, ast.Attribute):
            _key = self._expr_binding_key(recv, node)
            return [_key] if _key is not None else []
        if (isinstance(recv, ast.NamedExpr)
                and isinstance(recv.target, ast.Name)):
            return [self._scope.binding_key(recv.target.id, node)]
        return []
    def _record_start_join_events(self, node: ast.Call) -> None:
        if not (isinstance(node.func, ast.Attribute)
                and node.func.attr in ("start", "join")):
            return
        _bucket = self.started if node.func.attr == "start" else self.joined
        for _key in self._start_join_event_keys(node.func.value, node):
            _th01_bucket_add(_bucket, _key, node)
    def _record_target_reassignment(self, target: ast.AST) -> None:
        for expression in _th01_iter_binding_exprs(target):
            self._record_reassignment(expression, expression)
    def _collect_events(self) -> None:
        for node in tree_nodes(self.tree):
            if isinstance(node, ast.Assign):
                self._record_assign_events(node)
            elif isinstance(node, ast.AnnAssign):
                self._record_annassign_events(node)
            elif isinstance(node, ast.NamedExpr):
                self._record_walrus_event(node)
            elif (isinstance(node, ast.AugAssign)
                    and _th01_is_bindable_expr(node.target)):
                self._record_reassignment(node.target, node)
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                self._record_import_reassignment(node)
            if isinstance(node, (ast.For, ast.AsyncFor)):
                self._record_target_reassignment(node.target)
            elif isinstance(node, (ast.With, ast.AsyncWith)):
                for item in node.items:
                    if item.optional_vars is not None:
                        self._record_target_reassignment(item.optional_vars)
            if isinstance(node, ast.Call):
                self._record_start_join_events(node)
                self._record_daemon_call_event(node)
    def _daemon_coverage(
            self, constructor: tuple, events: list[ast.AST],
            start: ast.AST) -> list[_DT01Path]:
        start_scope = self._scope.execution_scope(start)
        local_events = [
            event for event in events
            if self._scope.execution_scope(event) is start_scope
        ]
        coverage: list[_DT01Path] = []
        if any(self._daemon_event_values[event]
               and self._scope.execution_scope(event) is not start_scope
               for event in events):
            coverage.append(frozenset())
        candidates = [
            event for event in local_events
            if self._daemon_event_values[event]
        ]
        if constructor[2]:
            candidates.append(constructor[3])
        for candidate in candidates:
            coverage.extend(_th01_daemon_candidate_worlds(
                self._scope, candidate, start, local_events,
                self._daemon_event_values, start_scope))
        return coverage
    def _report_lifecycle(self) -> None:
        pending: list[tuple[int, str]] = []
        for (_bscope, name), constructors in self.constructors.items():
            ordered = sorted(constructors, key=lambda ctor: ctor[0])
            states = [
                {"started": [], "joined": [], "daemon": []}
                for _ctor in ordered
            ]
            reassigned = self.reassigned.get((_bscope, name), [])
            _th01_apply_lifecycle_events(
                ordered, states, self.started.get((_bscope, name), []),
                "started", reassigned, self._scope)
            _th01_apply_lifecycle_events(
                ordered, states, self.joined.get((_bscope, name), []),
                "joined", reassigned, self._scope)
            _th01_apply_lifecycle_events(
                ordered, states, self.daemon_assigned.get((_bscope, name), []),
                "daemon", reassigned, self._scope)
            for index, (ctor, state) in enumerate(
                    zip(ordered, states, strict=True)):
                for start in state["started"]:
                    start_worlds = _th01_event_constructor_worlds(
                        ordered, index, start, reassigned, self._scope)
                    cleanup_worlds = self._daemon_coverage(
                        ctor, state["daemon"], start)
                    for join in state["joined"]:
                        if _th01_event_precedes(self._scope, start, join):
                            cleanup_worlds.extend(
                                _th01_event_constructor_worlds(
                                    ordered, index, join, reassigned,
                                    self._scope))
                    if not _th01_paths_cover(start_worlds, cleanup_worlds):
                        pending.append((ctor[1], name))
                        break
        for line, name in sorted(pending):
            self.issues.append(DiagnoseFinding(
                id="TH-01", severity="P2", dimension="concurrency",
                file=self.filepath, line=line,
                description=f"线程 {name} 启动后未 join 也未设置 daemon（解释器退出前会等待其结束，可能阻塞退出）",
                suggestion=_th01_suggestion(
                    "非 daemon 线程未 join 时，解释器退出前会等待其结束，可能阻塞进程退出；主流程也无法确认任务已完成。",
                    f"结束前调用 {name}.join()；后台任务显式设置 daemon=True"),
            ))
    def _report_fire_and_forget(self) -> None:
        for node in tree_nodes(self.tree):
            if not isinstance(node, ast.Expr):
                continue
            finding = self._fire_and_forget_finding(node)
            if finding is not None:
                self.issues.append(finding)
    def _fire_and_forget_finding(self, node: ast.Expr) -> DiagnoseFinding | None:
        call = node.value
        if not (isinstance(call, ast.Call)
                and isinstance(call.func, ast.Attribute)
                and call.func.attr == "start"):
            return None
        ctor = call.func.value
        if not (isinstance(ctor, ast.Call) and self._is_thread_ctor(ctor)):
            return None
        call_scope = self._scope.execution_scope(call)
        if _dt01_binding_blocks_reach(
                call, call, self._scope._parent_map, call_scope):
            return None
        if _th01_ctor_daemon_kw(ctor):
            return None
        return DiagnoseFinding(
            id="TH-01", severity="P2", dimension="concurrency",
            file=self.filepath, line=call.lineno,
            description=("threading.Thread(...) 构造后直接链式 .start()"
                         "（未保存线程引用，未 join 也未设置 daemon，"
                         "解释器退出前仍会等待其结束，可能阻塞退出）"),
            suggestion=_th01_suggestion(
                "构造即链式启动且未保存线程引用，非 daemon 线程未 join 时主线程"
                "退出行为未定义，任务可能被中途截断。",
                "t = threading.Thread(...) 保存引用后 t.start()，结束前调用 "
                "t.join()；后台任务显式设置 daemon=True"),
        )
    def run(self) -> list[DiagnoseFinding]:
        self._scope.build()
        self._import_scopes = _th01_collect_import_scopes(self.tree)
        self._build_thread_aliases()
        self._collect_events()
        self._report_lifecycle()
        self._report_fire_and_forget()
        return self.issues
def check_TH01(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if tree is None or finding_scan_exempt(filepath):
        return []
    return _TH01Checker(tree, filepath).run()
def _th01_suggestion(root_cause: str, fix_hint: str) -> str:
    return (f"根因: {root_cause}该问题属于并发安全类别。\n"
            f"修复策略: {fix_hint}\n"
            "参考标准: threading 文档")
def _cl01_is_staticmethod(node: ast.AST) -> bool:
    return any(
        dotted_name(decorator).rsplit(".", 1)[-1] == "staticmethod"
        for decorator in node.decorator_list
    )
def _cl01_owned_by_nested_staticmethod(child: ast.AST, node: ast.AST,
                                        scope_model: _ScopeModel) -> bool:
    owner = scope_model.execution_scope(child)
    if owner is node or not isinstance(owner, _FUNCTION_NODES):
        return False
    return _cl01_is_staticmethod(owner)
def _cl01_postponed_annotation_ids(tree: ast.AST) -> set[int]:
    """收集 ``from __future__ import annotations`` 下不会求值的注解节点。

    延迟注解模式下注解是字符串，不会在定义时求值；把其中的 ``self``
    当作运行期引用会产生 CL-01 误报（合法的静态方法前置引用）。
    """
    ids: set[int] = set()
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            args = getattr(node, "args", None)
            if args is not None:
                for arg_node in iter_arg_nodes(args):
                    if arg_node.annotation is not None:
                        ids.update(id(sub) for sub in walk_nodes(arg_node.annotation))
            returns = getattr(node, "returns", None)
            if returns is not None:
                ids.update(id(sub) for sub in walk_nodes(returns))
        if isinstance(node, ast.AnnAssign) and node.annotation is not None:
            ids.update(id(sub) for sub in walk_nodes(node.annotation))
    return ids
def _cl01_function_issues(node: ast.AST, filepath: str,
                          scope_model: _ScopeModel,
                          annotation_ids: frozenset[int] = frozenset(),
                          ) -> list[DiagnoseFinding]:
    for child in walk_nodes(node):
        if id(child) in annotation_ids:
            continue
        if not (isinstance(child, ast.Name) and child.id == "self"
                and isinstance(child.ctx, ast.Load)):
            continue
        if _cl01_owned_by_nested_staticmethod(child, node, scope_model):
            continue
        if scope_model.binding_scope(
                "self", scope_model.eval_scope(child)) is not None:
            continue
        return [DiagnoseFinding(
            id="CL-01", severity="P1", dimension="general",
            file=filepath, line=node.lineno,
            description=f"@staticmethod {node.name}() 函数体引用了 self（静态方法无实例绑定）",
            suggestion=("根因: 静态方法不接收实例参数，函数体内的 self 未定义，调用即 NameError。该问题属于闭包/绑定类别。\n"
                        "修复策略: 移除 @staticmethod（改为实例方法）或改用普通参数名\n"
                        "参考标准: Pylint E0210 / Ruff PLW0211"),
        )]
    return []
def check_CL01(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None or finding_scan_exempt(filepath):
        return issues
    model: _ScopeModel | None = None
    annotation_ids = (
        frozenset(_cl01_postponed_annotation_ids(tree))
        if module_postpones_annotations(tree) else frozenset())
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if not _cl01_is_staticmethod(node) \
                or "self" in collect_param_names(node):
            continue
        if model is None:
            model = _ScopeModel(tree)
            model.build()
        issues.extend(_cl01_function_issues(
            node, filepath, model, annotation_ids))
    return issues
_DT01_SCOPE_DEFS = (*SHADOW_SCOPE_STOP, ast.Lambda, *COMP_SCOPE_NODES)
_DT01_STACK_EXHAUSTED = object()
def _dt01_scope_body_children(scope: ast.AST) -> list[ast.AST]:
    if isinstance(scope, ast.Lambda):
        return [scope.body]
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                          ast.ClassDef, ast.Module)):
        return list(scope.body)
    return list(ast.iter_child_nodes(scope))
def _dt01_definition_children(scope: ast.AST) -> list[ast.AST]:
    if isinstance(scope, ast.ClassDef):
        children = list(scope.decorator_list)
        children.extend(scope.bases)
        children.extend(kw.value for kw in scope.keywords)
        return children
    return definition_time_exprs(scope)
def _dt01_iter_nodes(roots, skip: ast.AST | None):
    stack: list[Iterator[ast.AST]] = [iter(roots)]
    while stack:
        node = next(stack[-1], _DT01_STACK_EXHAUSTED)
        if node is _DT01_STACK_EXHAUSTED:
            stack.pop()
            continue
        if node is skip:
            continue
        yield node
        if isinstance(node, _DT01_SCOPE_DEFS):
            definition_children = _dt01_definition_children(node)
            if definition_children:
                stack.append(iter(definition_children))
            continue
        stack.append(iter(ast.iter_child_nodes(node)))
def _dt01_iter_scope_nodes(scope: ast.AST, skip: ast.AST | None = None):
    yield from _dt01_iter_nodes(_dt01_scope_body_children(scope), skip)
def _dt01_expression_nodes(expr: ast.AST):
    yield from _dt01_iter_nodes((expr,), None)
_DT01_NOW_TZ_DOTTED = ("datetime.now", "datetime.datetime.now")
_DT01_FROMTIMESTAMP_TZ_DOTTED = (
    "datetime.fromtimestamp", "datetime.datetime.fromtimestamp",
)
_DT01_NAIVE_ONLY_DOTTED = (
    "datetime.today", "datetime.datetime.today",
    "datetime.utcnow", "datetime.datetime.utcnow",
    "datetime.utcfromtimestamp", "datetime.datetime.utcfromtimestamp",
)
_DT01_NOW_DOTTED = (
    _DT01_NOW_TZ_DOTTED + _DT01_FROMTIMESTAMP_TZ_DOTTED
    + _DT01_NAIVE_ONLY_DOTTED
)
class _DT01AliasEvent(NamedTuple):
    position: tuple[int, int]
    target: str
    node: ast.AST
    path: frozenset[tuple[int, int]]
_DT01AliasValue = str | list[_DT01AliasEvent]
class _DT01Aliases(dict[str, _DT01AliasValue]):
    def __init__(self, scope: ast.AST,
                 parents: dict[ast.AST, ast.AST]) -> None:
        super().__init__()
        self.scope = scope
        self.parents = parents
def _dt01_alias_terminal(value: _DT01AliasValue) -> str:
    if isinstance(value, str):
        return value
    for event in reversed(value):
        if event.target or not event.path:
            return event.target
    return ""
def _dt01_alias_event_in_assignment_rhs(
        event: _DT01AliasEvent, use: ast.AST) -> bool:
    node = event.node
    if isinstance(node, ast.Assign):
        return in_subtree(use, node.value)
    if isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
        return node.value is not None and in_subtree(use, node.value)
    return False
def _dt01_alias_at(
        value: _DT01AliasValue, use: ast.AST,
        aliases: _DT01Aliases | None) -> str:
    if isinstance(value, str):
        return value
    position = node_position(use)
    parents = getattr(aliases, "parents", None)
    scope = getattr(aliases, "scope", None)
    use_path = (_dt01_branch_path(use, parents, scope)
                if parents is not None and scope is not None else frozenset())
    reachable = [
        event for event in value
        if event.position <= position
        and not _dt01_alias_event_in_assignment_rhs(event, use)
        and (event.target or not event.path or event.path <= use_path)
    ]
    return reachable[-1].target if reachable else ""
def _dt01_now_dotted(func: ast.AST,
                     aliases: _DT01Aliases | None) -> str:
    dotted = dotted_name(func)
    if aliases:
        parts = dotted.split(".")
        if len(parts) > 1 and parts[0] in aliases:
            base = _dt01_alias_at(aliases[parts[0]], func, aliases)
            if not base:
                return ""
            dotted = f"{base}." + ".".join(parts[1:])
    return dotted
def _dt01_tz_operand_kind(value: ast.AST) -> str:
    return "naive" if (isinstance(value, ast.Constant)
                       and value.value is None) else "aware"
def _dt01_now_tz_kind(node: ast.Call, dotted: str = "") -> str:
    if dotted in _DT01_NAIVE_ONLY_DOTTED:
        return "naive"
    tz_index = 1 if dotted in _DT01_FROMTIMESTAMP_TZ_DOTTED else 0
    if any(isinstance(arg, ast.Starred)
           for arg in node.args[:tz_index + 1]):
        return ""
    if len(node.args) > tz_index:
        return _dt01_tz_operand_kind(node.args[tz_index])
    for kw in node.keywords:
        if kw.arg == "tz":
            return _dt01_tz_operand_kind(kw.value)
    if any(kw.arg is None for kw in node.keywords):
        return ""
    return "naive"
def _dt01_now_info(node: ast.AST,
                   aliases: _DT01Aliases | None) -> str:
    if not isinstance(node, ast.Call):
        return ""
    dotted = _dt01_now_dotted(node.func, aliases)
    if dotted not in _DT01_NOW_DOTTED:
        return ""
    return _dt01_now_tz_kind(node, dotted)
def _dt01_replace_tzinfo_kind(node: ast.Call) -> str | None:
    for kw in node.keywords:
        if kw.arg == "tzinfo":
            return _dt01_tz_operand_kind(kw.value)
    if (any(kw.arg is None for kw in node.keywords)
            or any(isinstance(arg, ast.Starred) for arg in node.args)):
        return ""
    if len(node.args) >= 8:
        return _dt01_tz_operand_kind(node.args[7])
    return None
def _dt01_value_kind(val: ast.AST,
                     aliases: _DT01Aliases | None) -> str:
    if isinstance(val, ast.NamedExpr):
        return _dt01_value_kind(val.value, aliases)
    kind = _dt01_now_info(val, aliases)
    if kind:
        return kind
    if isinstance(val, ast.Call) and isinstance(val.func, ast.Attribute):
        if val.func.attr == "astimezone":
            return "aware"
        if val.func.attr == "replace":
            explicit = _dt01_replace_tzinfo_kind(val)
            return (_dt01_value_kind(val.func.value, aliases)
                    if explicit is None else explicit)
    return ""
def _dt01_assign_target_kinds(target: ast.AST, value: ast.AST,
                               aliases: _DT01Aliases | None) -> dict[str, str]:
    if isinstance(target, ast.Name):
        return {target.id: _dt01_value_kind(value, aliases)}
    if isinstance(target, (ast.Tuple, ast.List)):
        return _dt01_unpack_target_kinds(target, value, aliases)
    return {}
def _dt01_unpack_target_kinds(target: ast.AST, value: ast.AST,
                              aliases: _DT01Aliases | None) -> dict[str, str]:
    if not (isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(e, ast.Starred) for e in target.elts)):
        return dict.fromkeys(iter_unpack_target_names(target), "")
    kinds: dict[str, str] = {}
    for t_elt, v_elt in zip(target.elts, value.elts, strict=False):
        kinds.update(_dt01_assign_target_kinds(t_elt, v_elt, aliases))
    return kinds
def _dt01_scope_aliases(scope: ast.AST,
                        inherited: _DT01Aliases | None) -> _DT01Aliases:
    parents = _shared_parent_map(scope)
    aliases = _DT01Aliases(scope, parents)
    for name, value in (inherited or {}).items():
        inherited_value = (
            _dt01_alias_at(value, scope, inherited)
            if isinstance(scope, ast.ClassDef) and not isinstance(value, str)
            else _dt01_alias_terminal(value)
        )
        aliases[name] = inherited_value
    events: dict[str, list[_DT01AliasEvent]] = {}
    imported_names: set[str] = set()
    def add_event(name: str, node: ast.AST, target: str,
                  position: tuple[int, int] | None = None) -> None:
        events.setdefault(name, []).append(
            _DT01AliasEvent(
                node_position(node) if position is None else position,
                target, node, _dt01_branch_path(node, parents, scope)))
    for node in _dt01_iter_scope_nodes(scope):
        datetime_names: set[str] = set()
        for name, target, import_node in _dt01_iter_alias_entries(node):
            imported_names.add(name)
            datetime_names.add(name)
            add_event(name, import_node, target)
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            overwrite_names = scope_node_bound_names(node) - datetime_names
            position = None
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            overwrite_names = {node.name}
            position = node_position(node.body[0])
        elif isinstance(node, ast.ClassDef):
            overwrite_names = {node.name}
            position = (
                node.end_lineno if node.end_lineno is not None else node.lineno,
                node.end_col_offset if node.end_col_offset is not None
                else node.col_offset,
            )
        elif isinstance(node, ast.Delete):
            for target in node.targets:
                for name_node in _dt01_iter_target_name_nodes(target):
                    name = name_node.id
                    if (name == "datetime" or name in aliases
                            or name in imported_names):
                        restored = (aliases.get(name, "")
                                    if isinstance(scope, ast.ClassDef) else "")
                        add_event(name, node, restored)
            continue
        else:
            continue
        for name in overwrite_names:
            if name == "datetime" or name in aliases or name in imported_names:
                add_event(name, node, "", position)
    for name, _kind, _lineno, node in _dt01_binding_events_with_nodes(
            scope, None):
        if _dt01_binding_blocks_reach(node, node, parents, scope):
            continue
        if name == "datetime" or name in aliases or name in imported_names:
            add_event(name, node, "")
    for name in collect_param_names(scope):
        if name == "datetime" or name in aliases:
            add_event(name, scope, "")
    if isinstance(scope, COMP_SCOPE_NODES):
        for generator in scope.generators:
            for name in iter_unpack_target_names(generator.target):
                if name == "datetime" or name in aliases:
                    add_event(name, generator.target, "")
    for name, records in events.items():
        inherited_value = aliases.get(name, "")
        prior = ([
            _DT01AliasEvent(
                (-1, -1), inherited_value, scope, frozenset())
        ] if name in aliases else [])
        aliases[name] = sorted(
            [*prior, *records], key=lambda event: event.position)
    return aliases
def _dt01_is_datetime_import(node: ast.AST) -> bool:
    return isinstance(node, ast.Import) or (
        isinstance(node, ast.ImportFrom)
        and node.module == "datetime" and not node.level)
def _dt01_iter_alias_entries(node: ast.AST):
    if not _dt01_is_datetime_import(node):
        return
    for alias in node.names:
        if alias.name not in ("datetime", "datetime.datetime"):
            continue
        if isinstance(node, ast.Import):
            bound_name = alias.asname or alias.name.split(".")[0]
            target = alias.name if alias.asname else "datetime"
        else:
            bound_name = alias.asname or alias.name
            target = alias.name
        yield bound_name, target, node
_DT01_MATCH = getattr(ast, "Match", None)
def _dt01_promoted_walrus_targets(comp: ast.AST):
    queue = deque(ast.iter_child_nodes(comp))
    while queue:
        cur = queue.popleft()
        if isinstance(cur, _SCOPE_NODES):
            continue
        if isinstance(cur, ast.NamedExpr) and isinstance(cur.target, ast.Name):
            yield cur
        queue.extend(ast.iter_child_nodes(cur))
def _dt01_bind_assign(node: ast.Assign,
                      aliases: _DT01Aliases | None):
    for tgt in node.targets:
        for name, kind in _dt01_assign_target_kinds(
                tgt, node.value, aliases).items():
            yield name, kind, node.lineno
def _dt01_bind_annassign(node: ast.AnnAssign,
                         aliases: _DT01Aliases | None):
    if node.value is not None and isinstance(node.target, ast.Name):
        yield (node.target.id, _dt01_value_kind(node.value, aliases),
               node.lineno)
def _dt01_bind_namedexpr(node: ast.NamedExpr,
                         aliases: _DT01Aliases | None):
    if isinstance(node.target, ast.Name):
        yield (node.target.id, _dt01_value_kind(node.value, aliases),
               node.lineno)
def _dt01_bind_for(node: ast.For | ast.AsyncFor):
    for name in iter_unpack_target_names(node.target):
        yield name, "", node.target.lineno, node.target
def _dt01_iter_target_name_nodes(target: ast.AST):
    if isinstance(target, ast.Name):
        yield target
    elif isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            yield from _dt01_iter_target_name_nodes(element)
    elif isinstance(target, ast.Starred):
        yield from _dt01_iter_target_name_nodes(target.value)
def _dt01_bind_with(node: ast.With | ast.AsyncWith):
    for target in _scope_with_binding_targets(node):
        for name_node in _dt01_iter_target_name_nodes(target):
            yield name_node.id, "", name_node.lineno, name_node
def _dt01_bind_except(node: ast.ExceptHandler):
    if node.name:
        yield node.name, "", node.lineno
def _dt01_bind_match(node: ast.Match):
    for case in node.cases:
        for name in iter_pattern_capture_names(case.pattern):
            yield name, "", case.pattern.lineno, case.pattern
def _dt01_bind_promoted(node: ast.AST, aliases: _DT01Aliases | None):
    targets = sorted(
        _dt01_promoted_walrus_targets(node), key=node_position)
    for sub in targets:
        yield (sub.target.id, _dt01_value_kind(sub.value, aliases),
               sub.lineno, sub)
def _dt01_binding_events_with_nodes(scope: ast.AST,
                                    aliases: _DT01Aliases | None):
    in_comp = isinstance(scope, COMP_SCOPE_NODES)
    dispatch = [
        (ast.Assign, lambda n: _dt01_bind_assign(n, aliases)),
        (ast.AnnAssign, lambda n: _dt01_bind_annassign(n, aliases)),
        (ast.NamedExpr,
         lambda n: () if in_comp else _dt01_bind_namedexpr(n, aliases)),
        ((ast.For, ast.AsyncFor), _dt01_bind_for),
        ((ast.With, ast.AsyncWith), _dt01_bind_with),
        (ast.ExceptHandler, _dt01_bind_except),
        (COMP_SCOPE_NODES, lambda n: _dt01_bind_promoted(n, aliases)),
    ]
    if _DT01_MATCH is not None:
        dispatch.append((_DT01_MATCH, _dt01_bind_match))
    for node in _dt01_iter_scope_nodes(scope):
        for _types, _handler in dispatch:
            if isinstance(node, _types):
                for event in _handler(node):
                    if len(event) == 4:
                        yield event
                    else:
                        name, kind, lineno = event
                        yield name, kind, lineno, node
                break
class _DT01ScopeState(NamedTuple):
    terminal: dict[str, tuple[str, int]]
    rebound: set[str]
def _dt01_scope_bindings(
        scope: ast.AST,
        aliases: _DT01Aliases | None) -> _DT01ScopeState:
    terminal: dict[str, tuple[str, int]] = {}
    rebound = set(collect_param_names(scope))
    parents = _shared_parent_map(scope)
    for name, kind, lineno, node in _dt01_binding_events_with_nodes(
            scope, aliases):
        rebound.add(name)
        if _dt01_binding_blocks_reach(node, node, parents, scope):
            continue
        terminal[name] = (kind, lineno)
    if isinstance(scope, COMP_SCOPE_NODES):
        for gen in scope.generators:
            rebound |= set(iter_unpack_target_names(gen.target))
    return _DT01ScopeState(terminal, rebound)
def _dt01_cross_scope_rebind_kinds(
        scope: ast.AST,
        aliases: _DT01Aliases | None = None) -> dict[str, set[str]]:
    rebind_kinds: dict[str, set[str]] = {}
    owners: dict[str, ast.AST] = {}
    if isinstance(scope, _FUNCTION_NODES):
        owners = dict.fromkeys(_dt01_local_binding_names(scope), scope)
    _dt01_collect_descendant_rebinds(
        scope, scope, aliases, owners, rebind_kinds)
    return rebind_kinds
# 作用域级纯函数结果缓存。
#
# ``_dt01_cross_scope_rebind_kinds`` 从每个作用域向下递归全部后代会作用域，
# 过程中反复询问「本作用域的 global/nonlocal 声明」与「本地绑定名」。
# 这两个值只依赖 AST 结构，却在 307 模块规模下被放大成
# O(作用域数 × 后代数)：单文件实测 337 个作用域产生 2197 次声明遍历与
# 62342 次递归下降，独占 DT01 一半以上耗时。
# 缓存以 ``id(scope)`` 为键，由 ``check_DT01`` 入口按文件清空。
_DT01_SCOPE_DECL_CACHE: dict[int, tuple[set[str], set[str]]] = {}
_DT01_LOCAL_NAMES_CACHE: dict[int, set[str]] = {}
def _dt01_reset_scope_caches() -> None:
    """每文件入口清空作用域缓存（AST 生命周期与时序绑定）。"""
    _DT01_SCOPE_DECL_CACHE.clear()
    _DT01_LOCAL_NAMES_CACHE.clear()
def _dt01_local_binding_names(scope: ast.AST) -> set[str]:
    key = id(scope)
    cached = _DT01_LOCAL_NAMES_CACHE.get(key)
    if cached is not None:
        return cached
    globals_, nonlocals_ = _dt01_scope_declarations(scope)
    result = _dt01_scope_bindings(scope, None).rebound - globals_ - nonlocals_
    _DT01_LOCAL_NAMES_CACHE[key] = result
    return result
def _dt01_scope_declarations(scope: ast.AST) -> tuple[set[str], set[str]]:
    key = id(scope)
    cached = _DT01_SCOPE_DECL_CACHE.get(key)
    if cached is not None:
        return cached
    globals_: set[str] = set()
    nonlocals_: set[str] = set()
    for node in iter_own_nodes(scope):
        if isinstance(node, ast.Global):
            globals_ |= set(node.names)
        elif isinstance(node, ast.Nonlocal):
            nonlocals_ |= set(node.names)
    result = (globals_, nonlocals_)
    _DT01_SCOPE_DECL_CACHE[key] = result
    return result
def _dt01_collect_descendant_rebinds(
        node: ast.AST, root: ast.AST,
        aliases: _DT01Aliases | None,
        owners: dict[str, ast.AST],
        rebind_kinds: dict[str, set[str]]) -> None:
    for child in ast.iter_child_nodes(node):
        if not isinstance(child, _DT01_SCOPE_DEFS):
            _dt01_collect_descendant_rebinds(
                child, root, aliases, owners, rebind_kinds)
            continue
        _dt01_register_scope_rebinds(
            child, root, aliases, owners, rebind_kinds)
        child_owners = owners
        if isinstance(child, _FUNCTION_NODES):
            child_owners = dict(owners)
            for name in _dt01_local_binding_names(child):
                child_owners[name] = child
            globals_, _nonlocals = _dt01_scope_declarations(child)
            for name in globals_:
                child_owners.pop(name, None)
        _dt01_collect_descendant_rebinds(
            child, root, aliases, child_owners, rebind_kinds)
def _dt01_register_scope_rebinds(
        scope: ast.AST, root: ast.AST,
        aliases: _DT01Aliases | None,
        owners: dict[str, ast.AST],
        rebind_kinds: dict[str, set[str]]) -> None:
    globals_, nonlocals_ = _dt01_scope_declarations(scope)
    if not (globals_ or nonlocals_):
        return
    for name, (kind, _lineno) in _dt01_scope_bindings(
            scope, aliases).terminal.items():
        if name in globals_:
            if isinstance(root, ast.Module):
                rebind_kinds.setdefault(name, set()).add(kind)
        elif name in nonlocals_ and owners.get(name) is root:
            rebind_kinds.setdefault(name, set()).add(kind)
def _dt01_operand_kind(operand: ast.AST, var_kinds: dict[str, str],
                      aliases: _DT01Aliases | None) -> str:
    if isinstance(operand, ast.Name):
        return var_kinds.get(operand.id, "")
    return _dt01_value_kind(operand, aliases)
_DT01Decision = tuple[int, int]
_DT01Path = frozenset[_DT01Decision]
class _DT01Binding(NamedTuple):
    kind: str
    position: tuple[int, int]
    node: ast.AST
    path: _DT01Path
class _DT01BindingTimeline(NamedTuple):
    records: dict[str, list[_DT01Binding]]
    parents: dict[ast.AST, ast.AST]
    scope: ast.AST
def _dt01_try_decision(parent: ast.AST, current: ast.AST) -> list[_DT01Decision]:
    if any(stmt is current for stmt in parent.body):
        return []
    if any(stmt is current for stmt in parent.orelse):
        return [(id(parent), 0)]
    for index, handler in enumerate(parent.handlers, start=1):
        if handler is current:
            return [(id(parent), index)]
    return []
def _dt01_match_decision(parent: ast.AST, current: ast.AST) -> list[_DT01Decision]:
    for index, case in enumerate(parent.cases):
        if (case is current or case.guard is current
                or any(stmt is current for stmt in case.body)):
            return [(id(parent), index)]
    return []
def _dt01_comp_result_nodes(comp: ast.AST) -> tuple[ast.AST, ...]:
    if isinstance(comp, ast.DictComp):
        return comp.key, comp.value
    return comp.elt,
def _dt01_if_decisions(parent: ast.AST, current: ast.AST) -> set[_DT01Decision]:
    body = parent.body
    orelse = parent.orelse
    in_body = current is body if isinstance(body, ast.AST) else current in body
    in_else = current is orelse if isinstance(orelse, ast.AST) else current in orelse
    if in_body:
        return {(id(parent), 1)}
    if in_else:
        return {(id(parent), 0)}
    return set()
def _dt01_static_truth(node: ast.AST) -> bool | None:
    try:
        return bool(ast.literal_eval(node))
    except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):
        return None
def _dt01_loop_iter_non_empty(parent: ast.AST) -> bool:
    # ``for`` 的可迭代对象静态非空（字面量序列/非空 str、bytes/range 常量界）或
    # ``while`` 条件恒真时，循环体必然至少执行一次；把它再标成"可能不进入"
    # 分支会让体内必执行的赋值/清活在"未进入"世界被判未覆盖
    # （TH-01 误报 for t in [a, b]: t.join() / while True: t.join()），
    # 也会让循环体内必执行的时区归一被当作条件分支保留旧值（DT-01 误报）。
    if isinstance(parent, ast.While):
        return _dt01_static_truth(parent.test) is True
    if not isinstance(parent, (ast.For, ast.AsyncFor)):
        return False
    iter_node = parent.iter
    if isinstance(iter_node, (ast.Tuple, ast.List, ast.Set)):
        return bool(iter_node.elts)
    if isinstance(iter_node, ast.Dict):
        return bool(iter_node.keys)
    if isinstance(iter_node, ast.Constant) \
            and isinstance(iter_node.value, (str, bytes)):
        return bool(iter_node.value)
    if (isinstance(iter_node, ast.Call) and isinstance(iter_node.func, ast.Name)
            and iter_node.func.id == "range" and not iter_node.keywords
            and not any(isinstance(arg, ast.Starred) for arg in iter_node.args)
            and len(iter_node.args) in (1, 2)
            and all(isinstance(arg, ast.Constant) and type(arg.value) is int
                    for arg in iter_node.args)):
        bounds = [arg.value for arg in iter_node.args]
        return bounds[-1] > (bounds[0] if len(bounds) == 2 else 0)
    return False
def _dt01_loop_body_reachable(parent: ast.AST) -> bool:
    """循环体是否可能执行；静态可判定为空序列/恒假条件时返回 False。"""
    if isinstance(parent, ast.While):
        return _dt01_static_truth(parent.test) is not False
    if not isinstance(parent, (ast.For, ast.AsyncFor)):
        return True
    iter_node = parent.iter
    if isinstance(iter_node, (ast.Tuple, ast.List, ast.Set)):
        return bool(iter_node.elts)
    if isinstance(iter_node, ast.Dict):
        return bool(iter_node.keys)
    if isinstance(iter_node, ast.Constant) \
            and isinstance(iter_node.value, (str, bytes)):
        return bool(iter_node.value)
    if (isinstance(iter_node, ast.Call) and isinstance(iter_node.func, ast.Name)
            and iter_node.func.id == "range" and not iter_node.keywords
            and not any(isinstance(arg, ast.Starred) for arg in iter_node.args)
            and len(iter_node.args) in (1, 2)
            and all(isinstance(arg, ast.Constant) and type(arg.value) is int
                    for arg in iter_node.args)):
        bounds = [arg.value for arg in iter_node.args]
        return bounds[-1] > (bounds[0] if len(bounds) == 2 else 0)
    return True
def _dt01_loop_decisions(parent: ast.AST,
                         current: ast.AST) -> set[_DT01Decision]:
    enters_body = (current is getattr(parent, "target", None)
                   or current in parent.body)
    if not enters_body:
        return set()
    if _dt01_loop_iter_non_empty(parent):
        return set()
    if not _dt01_loop_body_reachable(parent):
        # 静态不可达：用负值标记，路径兼容性判定会将其视为永不执行。
        return {(id(parent), -1)}
    return {(id(parent), 1)}
def _dt01_bool_decisions(parent: ast.BoolOp,
                         current: ast.AST) -> set[_DT01Decision]:
    decisions: set[_DT01Decision] = set()
    for value in parent.values[1:]:
        decisions.add((id(value), 1))
        if value is current:
            return decisions
    return set()
def _dt01_filter_decisions(parent: ast.comprehension,
                           current: ast.AST) -> set[_DT01Decision]:
    decisions: set[_DT01Decision] = set()
    for expr in parent.ifs:
        decisions.add((id(expr), 1))
        if expr is current:
            return decisions
    return set()
def _dt01_comp_result_decisions(parent: ast.AST,
                                current: ast.AST) -> set[_DT01Decision]:
    if not any(in_subtree(current, result_node)
               for result_node in _dt01_comp_result_nodes(parent)):
        return set()
    return {
        (id(expr), 1)
        for gen in parent.generators for expr in gen.ifs
    }
def _dt01_assert_decisions(parent: ast.Assert,
                           current: ast.AST) -> set[_DT01Decision]:
    return {(id(parent), 1)} if parent.msg is current else set()
_DT01_BRANCH_DECISION_HANDLERS = [
    ((ast.If, ast.IfExp), _dt01_if_decisions),
    ((ast.For, ast.AsyncFor, ast.While), _dt01_loop_decisions),
    (TRY_NODE_TYPES, _dt01_try_decision),
    ((ast.BoolOp,), _dt01_bool_decisions),
]
if _DT01_MATCH is not None:
    _DT01_BRANCH_DECISION_HANDLERS.append((_DT01_MATCH, _dt01_match_decision))
_DT01_BRANCH_DECISION_HANDLERS.extend([
    ((ast.comprehension,), _dt01_filter_decisions),
    (COMP_SCOPE_NODES, _dt01_comp_result_decisions),
    ((ast.Assert,), _dt01_assert_decisions),
])
def _dt01_parent_branch_decisions(parent: ast.AST, current: ast.AST):
    for node_types, handler in _DT01_BRANCH_DECISION_HANDLERS:
        if isinstance(parent, node_types):
            return handler(parent, current)
    return set()
def _dt01_branch_path(node: ast.AST, parents: dict[ast.AST, ast.AST],
                      scope: ast.AST) -> _DT01Path:
    decisions: set[_DT01Decision] = set()
    current = node
    while current is not scope:
        parent = parents.get(current)
        if parent is None:
            break
        decisions.update(_dt01_parent_branch_decisions(parent, current))
        current = parent
    return frozenset(decisions)
def _dt01_binding_timeline(
        scope: ast.AST, aliases: _DT01Aliases | None,
        closure_options: dict[str, set[str]] | None = None,
        global_options: dict[str, set[str]] | None = None,
        free_options: dict[str, set[str]] | None = None,
) -> _DT01BindingTimeline:
    records: dict[str, list[_DT01Binding]] = {}
    parents = _shared_parent_map(scope)
    for name, kind, lineno, node in _dt01_binding_events_with_nodes(scope, aliases):
        record = _DT01Binding(
            kind, (lineno, node.col_offset), node,
            _dt01_branch_path(node, parents, scope))
        records.setdefault(name, []).append(record)
    globals_, nonlocals_ = (
        _dt01_scope_declarations(scope)
        if not isinstance(scope, ast.Module) else (set(), set()))
    inherited_anchor = ast.Pass()
    for declared_names, options in (
            (globals_, global_options), (nonlocals_, closure_options)):
        for name in declared_names:
            for kind in sorted((options or {}).get(name, ())):
                records.setdefault(name, []).append(_DT01Binding(
                    kind, (-1, -1), inherited_anchor, frozenset()))
    for name, kinds in (free_options or {}).items():
        for kind in sorted(kinds):
            records.setdefault(name, []).append(_DT01Binding(
                kind, (-1, -1), inherited_anchor, frozenset()))
    for events in records.values():
        events.sort(key=lambda event: event.position)
    return _DT01BindingTimeline(records, parents, scope)
def _dt01_paths_compatible(first: _DT01Path, second: _DT01Path) -> bool:
    if (any(value < 0 for _decision, value in first)
            or any(value < 0 for _decision, value in second)):
        return False
    decisions = dict(first)
    return all(decision not in decisions or decisions[decision] == value
               for decision, value in second)
def _dt01_decision_arity(paths) -> dict[int, int]:
    arity: dict[int, int] = {}
    for path in paths:
        for decision, value in path:
            arity[decision] = max(arity.get(decision, 0), int(value) + 1)
    return arity
def _dt01_path_worlds(base: _DT01Path, decisions: list[int],
                      arity: dict[int, int]) -> Iterator[_DT01Path]:
    worlds = [base]
    for decision in decisions:
        extended: list[_DT01Path] = []
        for world in worlds:
            existing = dict(world).get(decision)
            if existing is not None:
                extended.append(world)
                continue
            for value in range(max(arity.get(decision, 2), 2)):
                extended.append(world | {(decision, value)})
        worlds = extended
    yield from worlds
def _dt01_mentions_operation(node: ast.AST, operation: ast.AST) -> bool:
    return any(operation is sub for sub in walk_nodes(node))
def _dt01_binding_contains_prior_value_operation(
        binding: _DT01Binding, operation: ast.AST) -> bool:
    node = binding.node
    if isinstance(node, ast.ExceptHandler):
        return node.type is not None and in_subtree(operation, node.type)
    return _dt01_mentions_operation(node, operation)
def _dt01_reaching_killers(candidate: _DT01Binding,
                           later: list[_DT01Binding], operation: ast.AST,
                           operation_pos: tuple[int, int]
                           ) -> list[_DT01Binding]:
    return [
        record for record in later
        if candidate.position < record.position < operation_pos
        and not _dt01_binding_contains_prior_value_operation(record, operation)
    ]
_DT01_BLOCK_TERMINATORS = (ast.Raise, ast.Return, ast.Break, ast.Continue)
def _dt01_binding_blocks_reach(
        binding_node: ast.AST, operation: ast.AST,
        parents: dict[ast.AST, ast.AST], scope: ast.AST) -> bool:
    current = binding_node
    while current is not scope:
        parent = parents.get(current)
        if parent is None:
            break
        if isinstance(parent, ast.Assert) and current is parent.msg:
            return not in_subtree(operation, parent.msg)
        for _field, siblings in ast.iter_fields(parent):
            if not isinstance(siblings, list):
                continue
            for index, sibling in enumerate(siblings):
                if sibling is not current:
                    continue
                if any(isinstance(previous, _DT01_BLOCK_TERMINATORS)
                       for previous in siblings[:index]):
                    return True
                break
        current = parent
    return False
def _dt01_world_passes(world: _DT01Path,
                       killers: list[_DT01Binding]) -> bool:
    return not any(_dt01_paths_compatible(world, record.path)
                   for record in killers)
def _dt01_fallback_reaching_world(
        base: _DT01Path, killers: list[_DT01Binding], arity: dict[int, int],
) -> list[_DT01Path]:
    pending = [base]
    budget = 1024
    while pending and budget:
        budget -= 1
        world = pending.pop()
        killer = next((record for record in killers
                       if _dt01_paths_compatible(world, record.path)), None)
        if killer is None:
            return [world]
        decisions = dict(world)
        choices = [(decision, value) for decision, value in killer.path
                   if decision not in decisions]
        if not choices:
            continue
        for decision, killer_value in choices:
            for value in range(max(arity.get(decision, 2), 2)):
                if value != killer_value:
                    pending.append(world | {(decision, value)})
    return [base] if pending else []
def _dt01_reaching_worlds(
        candidate: _DT01Binding, later: list[_DT01Binding],
        operation: ast.AST, operation_path: _DT01Path,
        parents: dict[ast.AST, ast.AST], scope: ast.AST) -> list[_DT01Path]:
    operation_pos = (operation.lineno, operation.col_offset)
    if candidate.position >= operation_pos:
        return []
    if _dt01_mentions_operation(candidate.node, operation):
        return []
    if _dt01_binding_blocks_reach(
            candidate.node, operation, parents, scope):
        return []
    if not _dt01_paths_compatible(candidate.path, operation_path):
        return []
    base = candidate.path | operation_path
    killers = [
        record for record in _dt01_reaching_killers(
            candidate, later, operation, operation_pos)
        if not _dt01_binding_blocks_reach(
            record.node, operation, parents, scope)
    ]
    paths = (base, *(record.path for record in killers))
    decisions = sorted({
        decision for path in paths for decision, _value in path})
    arity = _dt01_decision_arity(paths)
    world_count = 1
    for decision in decisions:
        world_count *= max(arity.get(decision, 2), 2)
    if len(decisions) > 10 or world_count > 1024:
        return _dt01_fallback_reaching_world(base, killers, arity)
    return [world for world in _dt01_path_worlds(base, decisions, arity)
            if _dt01_world_passes(world, killers)]
def _dt01_unpack_binding_value(target: ast.AST, value: ast.AST,
                                name: str) -> ast.AST | None:
    if isinstance(target, ast.Name):
        return value if target.id == name else None
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(elt, ast.Starred) for elt in target.elts)):
        return None
    for target_elt, value_elt in zip(target.elts, value.elts, strict=True):
        bound_value = _dt01_unpack_binding_value(target_elt, value_elt, name)
        if bound_value is not None:
            return bound_value
    return None
def _dt01_binding_value(binding: _DT01Binding,
                        name: str) -> ast.AST | None:
    node = binding.node
    if isinstance(node, ast.NamedExpr):
        return node.value if node.target.id == name else None
    if isinstance(node, ast.AnnAssign):
        return _dt01_unpack_binding_value(node.target, node.value, name) \
            if node.value is not None else None
    if isinstance(node, ast.Assign):
        for target in node.targets:
            bound_value = _dt01_unpack_binding_value(target, node.value, name)
            if bound_value is not None:
                return bound_value
    return None
def _dt01_inherited_replace_receiver(value: ast.AST | None) -> ast.AST | None:
    if not (isinstance(value, ast.Call)
            and isinstance(value.func, ast.Attribute)
            and value.func.attr == "replace"):
        return None
    if _dt01_replace_tzinfo_kind(value) is not None:
        return None
    return value.func.value
def _dt01_local_name_options_at(
        name: str, node: ast.AST, var_kinds: dict[str, str],
        timeline: _DT01BindingTimeline,
        local_names: frozenset[str], inherited_world: _DT01Path,
        active_copies: frozenset[tuple[str, ast.AST]],
        ) -> list[tuple[str, _DT01Path]]:
    operation_path = _dt01_branch_path(node, timeline.parents, timeline.scope)
    records = timeline.records.get(name, [])
    options: list[tuple[str, _DT01Path]] = []
    for index, candidate in enumerate(records):
        later = records[index + 1:]
        copy_key = (name, candidate.node)
        bound_value = _dt01_binding_value(candidate, name)
        receiver = _dt01_inherited_replace_receiver(bound_value)
        copy_source = receiver if isinstance(receiver, ast.Name) else bound_value
        for world in _dt01_reaching_worlds(
                candidate, later, node, operation_path,
                timeline.parents, timeline.scope):
            if not _dt01_paths_compatible(inherited_world, world):
                continue
            combined_world = inherited_world | world
            if candidate.kind:
                options.append((candidate.kind, combined_world))
                continue
            if isinstance(copy_source, ast.Name):
                source_name = copy_source.id
                if source_name not in local_names:
                    options.append((var_kinds.get(source_name, ""),
                                    combined_world))
                elif copy_key in active_copies:
                    options.append(("", combined_world))
                else:
                    options.extend(_dt01_local_name_options_at(
                        source_name, candidate.node, var_kinds, timeline,
                        local_names, combined_world,
                        active_copies | {copy_key}))
            else:
                options.append(("", combined_world))
    return list(dict.fromkeys(options))
def _dt01_operand_kind_options_at(
        operand: ast.AST, node: ast.AST, var_kinds: dict[str, str],
        aliases: _DT01Aliases | None, timeline: _DT01BindingTimeline,
        local_names: frozenset[str]) -> list[tuple[str, _DT01Path]]:
    receiver = _dt01_inherited_replace_receiver(operand)
    if receiver is not None:
        return _dt01_operand_kind_options_at(
            receiver, node, var_kinds, aliases, timeline, local_names)
    if not isinstance(operand, ast.Name) or operand.id not in local_names:
        return [(_dt01_operand_kind(operand, var_kinds, aliases), frozenset())]
    options = _dt01_local_name_options_at(
        operand.id, node, var_kinds, timeline, local_names,
        frozenset(), frozenset())
    return list(dict.fromkeys(options)) or [("", frozenset())]
def _dt01_operand_desc(operand: ast.AST, kind: str) -> str:
    if isinstance(operand, ast.Name):
        return (f"aware 时间源变量 {operand.id}" if kind == "aware"
                else f"naive 时间源变量 {operand.id}")
    if isinstance(operand, ast.NamedExpr):
        return _dt01_operand_desc(operand.value, kind)
    if isinstance(operand, ast.Call):
        func = operand.func
        if isinstance(func, ast.Attribute) and func.attr == "astimezone":
            return "astimezone() 结果"
        dotted = dotted_name(func)
        if dotted:
            if kind == "aware" and dotted.endswith(".now"):
                return "datetime.now(tz...)"
            return f"{dotted}()"
    return "datetime.now(tz...)" if kind == "aware" else "datetime.now()"
def _dt01_merge_scope_state(
        scope: ast.AST, inherited: dict[str, str],
        aliases: _DT01Aliases | None,
        rebind_kinds: dict[str, set[str]]) -> tuple[
            dict[str, str], set[str], dict[str, set[str]]]:
    state = _dt01_scope_bindings(scope, aliases)
    terminal, rebound = state.terminal, state.rebound
    merged: dict[str, str] = dict(inherited)
    merged.update({name: kind for name, (kind, _ln) in terminal.items()})
    for name in rebound - terminal.keys():
        merged.pop(name, None)
    kind_options = {
        name: {kind} for name, kind in merged.items() if kind}
    for name, kinds in rebind_kinds.items():
        known = {kind for kind in kinds if kind}
        if known:
            kind_options.setdefault(name, set()).update(known)
    _dt01_apply_rebind_arbitration(merged, rebind_kinds)
    return merged, rebound, kind_options
def _dt01_apply_rebind_arbitration(merged: dict[str, str],
                                   rebind_kinds: dict[str, set[str]]) -> None:
    for name, rebind in rebind_kinds.items():
        current = merged.get(name, "")
        if not (current and rebind and all(k == current for k in rebind)):
            merged[name] = ""
_DT01_ORDER_CMP = (ast.Lt, ast.LtE, ast.Gt, ast.GtE)
_DT01_OP_ERRORS = {
    "相减": "can't subtract offset-naive and offset-aware datetimes",
    "比较": "can't compare offset-naive and offset-aware datetimes",
}
def _dt01_operand_pairs(
        node: ast.AST) -> list[tuple[tuple[ast.AST, ast.AST], str]]:
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Sub):
        return [((node.left, node.right), "相减")]
    if isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Sub):
        return [((node.target, node.value), "相减")]
    if isinstance(node, ast.Compare):
        bounds = [node.left, *node.comparators]
        return [((bounds[i], bounds[i + 1]), "比较")
                for i, op in enumerate(node.ops)
                if isinstance(op, _DT01_ORDER_CMP)]
    return []
def _dt01_pair_findings(node: ast.AST, merged: dict[str, str],
                        aliases: _DT01Aliases | None,
                        filepath: str,
                        timeline: _DT01BindingTimeline | None,
                        local_names: frozenset[str]
                        ) -> list[DiagnoseFinding]:
    if timeline is not None and _dt01_binding_blocks_reach(
            node, node, timeline.parents, timeline.scope):
        return []
    findings: list[DiagnoseFinding] = []
    for pair, op_label in _dt01_operand_pairs(node):
        mixed = _dt01_mixed_kinds(
            pair, merged, aliases, node, timeline, local_names)
        if mixed is None:
            continue
        findings.append(_dt01_mixed_finding(
            pair, mixed, node.lineno, filepath, op_label))
    return findings
def _dt01_mixed_finding(operands: tuple[ast.AST, ast.AST],
                        kinds: tuple[str, str], lineno: int,
                        filepath: str, op_label: str) -> DiagnoseFinding:
    left, right = operands
    left_kind, right_kind = kinds
    hit = (f"{_dt01_operand_desc(left, left_kind)} 与 "
           f"{_dt01_operand_desc(right, right_kind)} {op_label}")
    return DiagnoseFinding(
        id="DT-01", severity="P2", dimension="type",
        file=filepath, line=lineno,
        description=f"{hit}（naive-aware {op_label}必抛 TypeError）",
        suggestion=("根因: naive（无时区）与 aware（带时区）datetime "
                    f"{op_label}抛 TypeError: {_DT01_OP_ERRORS[op_label]}。\n"
                    "修复策略: 统一时区口径——全用 datetime.now(timezone.utc)"
                    "（aware）或全用 naive，跨口径用 .astimezone(timezone.utc)"
                    ".replace(tzinfo=None) 归一后再运算\n"
                    "参考标准: datetime 文档 naive/aware 对象章节"),
    )
def _dt01_scan_nodes(
        nodes: Iterator[ast.AST], merged: dict[str, str],
        sub_inherited: dict[str, str], filepath: str,
        aliases: _DT01Aliases | None,
        timeline: _DT01BindingTimeline | None,
        local_names: frozenset[str]) -> tuple[
        list[DiagnoseFinding],
        list[tuple[ast.AST, dict[str, str], dict[str, str]]]]:
    issues: list[DiagnoseFinding] = []
    sub_scopes: list[tuple[ast.AST, dict[str, str], dict[str, str]]] = []
    for node in nodes:
        if isinstance(node, _DT01_SCOPE_DEFS):
            sub_scopes.append((node, sub_inherited, merged))
            continue
        issues.extend(_dt01_pair_findings(
            node, merged, aliases, filepath, timeline, local_names))
    return issues, sub_scopes
def _dt01_is_mixed_pair(left_kind: str, right_kind: str) -> bool:
    return ((left_kind == "naive" and right_kind == "aware")
            or (left_kind == "aware" and right_kind == "naive"))
def _dt01_options_mixed(
        left_options: list[tuple[str, _DT01Path]],
        right_options: list[tuple[str, _DT01Path]],
) -> tuple[str, str] | None:
    for left_kind, left_path in left_options:
        for right_kind, right_path in right_options:
            if not _dt01_paths_compatible(left_path, right_path):
                continue
            if _dt01_is_mixed_pair(left_kind, right_kind):
                return left_kind, right_kind
    return None
def _dt01_mixed_kinds(pair: tuple[ast.AST, ast.AST],
                      merged: dict[str, str],
                      aliases: _DT01Aliases | None,
                      node: ast.AST,
                      timeline: _DT01BindingTimeline | None,
                      local_names: frozenset[str]
                      ) -> tuple[str, str] | None:
    left, right = pair
    if timeline is not None:
        return _dt01_options_mixed(
            _dt01_operand_kind_options_at(
                left, node, merged, aliases, timeline, local_names),
            _dt01_operand_kind_options_at(
                right, node, merged, aliases, timeline, local_names))
    left_kind = _dt01_operand_kind(left, merged, aliases)
    right_kind = _dt01_operand_kind(right, merged, aliases)
    if _dt01_is_mixed_pair(left_kind, right_kind):
        return left_kind, right_kind
    return None
def _dt01_scan_scope(
        scope: ast.AST, inherited: dict[str, str], filepath: str,
        aliases: _DT01Aliases | None,
        first_iter_kinds: dict[str, str] | None = None,
        first_iter_aliases: _DT01Aliases | None = None,
        closure_options: dict[str, set[str]] | None = None,
        global_options: dict[str, set[str]] | None = None,
) -> list[DiagnoseFinding]:
    inherited_aliases = aliases or {}
    aliases = _dt01_scope_aliases(scope, inherited_aliases)
    rebind_kinds = _dt01_cross_scope_rebind_kinds(scope, aliases)
    merged, rebound, kind_options = _dt01_merge_scope_state(
        scope, inherited, aliases, rebind_kinds)
    if global_options is None:
        global_options = kind_options if isinstance(scope, ast.Module) else {}
    globals_, nonlocals_ = (
        _dt01_scope_declarations(scope)
        if not isinstance(scope, ast.Module) else (set(), set()))
    free_options: dict[str, set[str]] = {}
    for name in set(merged) - rebound - globals_ - nonlocals_:
        kinds = {
            kind for kind in (closure_options or {}).get(name, ()) if kind}
        if kinds:
            free_options[name] = kinds
    issues: list[DiagnoseFinding] = []
    expr_scopes: list[tuple[ast.AST, dict[str, str], dict[str, str]]] = []
    eval_aliases = aliases
    skip = None
    if isinstance(scope, COMP_SCOPE_NODES) and scope.generators:
        skip = scope.generators[0].iter
        eval_kinds = merged if first_iter_kinds is None else first_iter_kinds
        if first_iter_aliases is not None:
            eval_aliases = first_iter_aliases
        expr_issues, expr_scopes = _dt01_scan_nodes(
            _dt01_expression_nodes(skip), eval_kinds, eval_kinds, filepath,
            eval_aliases, None, frozenset())
        issues.extend(expr_issues)
    sub_inherited = inherited if isinstance(scope, ast.ClassDef) else merged
    timeline = _dt01_binding_timeline(
        scope, aliases, closure_options, global_options, free_options)
    arbitrated = frozenset(rebind_kinds)
    declared = frozenset(globals_ | nonlocals_)
    local_names = ((frozenset(rebound) - arbitrated) | declared
                   | frozenset(free_options))
    pass_issues, pass_scopes = _dt01_scan_nodes(
        _dt01_iter_scope_nodes(scope, skip), merged, sub_inherited, filepath,
        aliases, timeline, local_names)
    issues.extend(pass_issues)
    sub_aliases = (inherited_aliases if isinstance(scope, ast.ClassDef)
                   else aliases)
    expr_sub_aliases = (inherited_aliases if isinstance(scope, ast.ClassDef)
                        else eval_aliases)
    child_closure_options = (
        closure_options if isinstance(scope, ast.ClassDef) else kind_options)
    for sub, body_inherited, eval_kinds in expr_scopes:
        issues.extend(_dt01_scan_scope(
            sub, body_inherited, filepath, expr_sub_aliases, eval_kinds,
            eval_aliases, child_closure_options, global_options))
    for sub, body_inherited, eval_kinds in pass_scopes:
        issues.extend(_dt01_scan_scope(
            sub, body_inherited, filepath, sub_aliases, eval_kinds, aliases,
            child_closure_options, global_options))
    return issues
def check_DT01(tree: ast.AST | None, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    _log.debug("规则入口 check_DT01 执行")
    if tree is None or finding_scan_exempt(filepath):
        return []
    # 作用域缓存按文件重生，避免跨文件 id() 重用导致串账
    _dt01_reset_scope_caches()
    return _dt01_scan_scope(tree, {}, filepath, None)
def wiring_declarations() -> dict:
    return {"catalogs": {
        "aicoder_direct": {'DT-01': check_DT01},
        "recovered_bindings": {
            'CL01': check_CL01, 'TH01': check_TH01,
        },
        "traps_bindings": {'DT01': check_DT01},
    }}

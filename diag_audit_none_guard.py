from __future__ import annotations

import ast
import logging
import re
from dataclasses import dataclass
from itertools import pairwise
from typing import ClassVar

from jwsgj.diag_shared_ast_bindings import expr_binds
from jwsgj.diag_shared_ast_nodes import (
    collect_param_names,
    split_identifier,
)
from jwsgj.diag_shared_ast_nodes import (
    is_none_literal as is_none_constant,
)
from jwsgj.diag_shared_ast_views import (
    assign_target_names,
)
from jwsgj.diag_shared_ast_views import (
    parent_map as shared_parent_map,
)
from jwsgj.diag_shared_source_core import (
    TRY_TYPES,
    parse_py_file,
    safe_source_line,
    suggest,
)
from jwsgj.diag_types_defs import (
    PatternFinding,
)
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    "FallbackReturnsNoneDetector",
    "NoneFallbackCallableDetector",
]
logger = logging.getLogger(__name__)
logger.info("diag_audit_none_guard 已加载：%d 项导出", len(__all__))
_QUALITY_ROOT_CAUSE = '代码实现中存在代码质量方面的问题, 需要规范化处理。'
_COMPREHENSION_NODES = (ast.ListComp, ast.SetComp, ast.DictComp,
                        ast.GeneratorExp)
def _collect_none_stmt(stmt: ast.AST, none_names: dict) -> None:
    if isinstance(stmt, ast.Assign):
        _states = _assign_binding_states(stmt)
    elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
        _states = _target_binding_states(stmt.target, stmt.value)
    else:
        return
    for name, state in _states.items():
        if state is False:
            none_names[name] = stmt.lineno
def _scan_try_chain(stmts, none_names: dict, *,
                    within_try: bool = False) -> None:
    for stmt in stmts:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            continue
        if isinstance(stmt, TRY_TYPES):
            for handler in stmt.handlers:
                _scan_try_chain(handler.body, none_names, within_try=True)
            _scan_try_chain(stmt.body, none_names, within_try=True)
            _scan_try_chain(stmt.orelse, none_names, within_try=True)
            _scan_try_chain(stmt.finalbody, none_names, within_try=True)
        elif isinstance(stmt, (ast.With, ast.AsyncWith)):
            _scan_try_chain(stmt.body, none_names, within_try=within_try)
        elif (within_try and isinstance(
                stmt, (ast.If, ast.For, ast.AsyncFor, ast.While))):
            _scan_try_chain(stmt.body, none_names, within_try=True)
            _scan_try_chain(stmt.orelse, none_names, within_try=True)
        else:
            _collect_none_stmt(stmt, none_names)
def _collect_none_assigns(tree: ast.AST) -> dict:
    none_names: dict = {}
    _scan_try_chain(ast.iter_child_nodes(tree), none_names)
    return none_names
def _import_bound_aliases(stmt: ast.Import | ast.ImportFrom) -> tuple[str, ...]:
    if isinstance(stmt, ast.Import):
        return tuple(alias.asname or alias.name.split('.')[0]
                     for alias in stmt.names)
    return tuple(alias.asname or alias.name for alias in stmt.names
                 if alias.name != '*')
def _collect_defined_names(tree: ast.AST) -> set:
    defined: set = set()
    for node in ast.iter_child_nodes(tree):
        names, none_names, _recover_names = _stmt_binding_faces(node)
        defined.difference_update(none_names)
        defined.update(names - none_names)
    return defined
def _unpack_binding_names(target: ast.AST) -> dict[str, None]:
    names: set[str] = set()
    assign_target_names(target, names)
    return dict.fromkeys(names)
def _is_pairable_unpack(target: ast.AST, value: ast.AST) -> bool:
    return (isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(e, ast.Starred) for e in target.elts))
def _value_may_be_none(value: ast.AST) -> bool:
    if not isinstance(value, ast.IfExp):
        return False
    return any(is_none_constant(branch)
               for branch in (value.body, value.orelse))
def _binding_faces_from_states(states: dict) -> tuple[set, set, set]:
    return (set(states),
            {name for name, state in states.items() if state is not True},
            {name for name, state in states.items() if state is True})
def _update_expression_states(states: dict, updates: dict, *,
                              optional: bool = False) -> None:
    for name, state in updates.items():
        if optional and name not in states and state is True:
            continue
        if optional and (state is None or name not in states
                         or states[name] != state):
            states[name] = None
        else:
            states[name] = state
def _expression_sequence_states(expressions, states: dict | None = None) -> dict:
    states = {} if states is None else states
    for expression in expressions:
        _update_expression_states(
            states, _expression_binding_states(expression))
    return states
def _constant_truthiness(node: ast.AST) -> bool | None:
    return bool(node.value) if isinstance(node, ast.Constant) else None
def _ifexp_binding_states(node: ast.IfExp) -> dict:
    prefix = _expression_binding_states(node.test)
    truthiness = _constant_truthiness(node.test)
    if truthiness is not None:
        branch = node.body if truthiness else node.orelse
        return _expression_sequence_states([branch], prefix)
    body = _expression_sequence_states([node.body], dict(prefix))
    orelse = _expression_sequence_states([node.orelse], dict(prefix))
    states: dict = {}
    for name in body.keys() | orelse.keys():
        if name in body and name in orelse:
            states[name] = (body[name] if body[name] == orelse[name]
                            else None)
        else:
            branch_state = body.get(name, orelse.get(name))
            if branch_state is not True:
                states[name] = None
    return states
def _comp_iter_length(node: ast.AST) -> int | None:
    if (isinstance(node, (ast.List, ast.Tuple, ast.Set))
            and not any(isinstance(e, ast.Starred) for e in node.elts)):
        return len(node.elts)
    return None
def _comprehension_binding_states(node: ast.AST) -> dict:
    generators = node.generators
    if not generators:
        return {}
    states = _expression_binding_states(generators[0].iter)
    if isinstance(node, ast.GeneratorExp) or _comp_iter_length(
            generators[0].iter) == 0:
        return states
    deferred = [*generators[0].ifs]
    for generator in generators[1:]:
        deferred.append(generator.iter)
        deferred.extend(generator.ifs)
    if isinstance(node, ast.DictComp):
        deferred.extend((node.key, node.value))
    else:
        deferred.append(node.elt)
    certain_iteration = all(
        not generator.ifs and (_comp_iter_length(generator.iter) or 0) > 0
        for generator in generators)
    for expression in deferred:
        _update_expression_states(
            states, _expression_binding_states(expression),
            optional=not certain_iteration)
    return states
def _expression_binding_states(node: ast.AST) -> dict:
    if isinstance(node, ast.NamedExpr):
        states = _expression_binding_states(node.value)
        _update_expression_states(
            states, _target_binding_states(node.target, node.value))
        return states
    if isinstance(node, ast.Lambda):
        return _expression_sequence_states([
            *node.args.defaults,
            *(default for default in node.args.kw_defaults
              if default is not None),
        ])
    if isinstance(node, _COMPREHENSION_NODES):
        return _comprehension_binding_states(node)
    if isinstance(node, ast.IfExp):
        return _ifexp_binding_states(node)
    if isinstance(node, ast.BoolOp):
        states: dict = {}
        certain = True
        for value in node.values:
            _update_expression_states(
                states, _expression_binding_states(value), optional=not certain)
            truthiness = _constant_truthiness(value)
            short_circuits = (
                isinstance(node.op, ast.And) and truthiness is False
                or isinstance(node.op, ast.Or) and truthiness is True)
            if short_circuits:
                break
            if truthiness is None:
                certain = False
        return states
    if isinstance(node, ast.Call):
        arguments = sorted((*node.args, *node.keywords), key=_source_order)
        return _expression_sequence_states([
            node.func,
            *(argument.value if isinstance(argument, ast.keyword)
              else argument for argument in arguments),
        ])
    if isinstance(node, ast.Dict):
        children = []
        for key, value in zip(node.keys, node.values, strict=True):
            if key is not None:
                children.append(key)
            children.append(value)
        return _expression_sequence_states(children)
    if isinstance(node, ast.Compare):
        states = _expression_sequence_states([node.left])
        if node.comparators:
            _update_expression_states(
                states, _expression_binding_states(node.comparators[0]))
        for comparator in node.comparators[1:]:
            _update_expression_states(
                states, _expression_binding_states(comparator), optional=True)
        return states
    return _expression_sequence_states(
        child for child in ast.iter_child_nodes(node)
        if isinstance(child, ast.expr))
def _target_binding_states(target: ast.AST, value: ast.AST | None, *,
                           unpacked: bool = False) -> dict[str, bool | None]:
    if value is None:
        return {}
    while isinstance(value, ast.NamedExpr):
        value = value.value
    if isinstance(target, ast.Name):
        if is_none_constant(value):
            return {target.id: False}
        if _value_may_be_none(value):
            return {target.id: None}
        if unpacked and not isinstance(value, ast.Constant):
            return {target.id: None}
        return {target.id: True}
    if isinstance(target, (ast.Tuple, ast.List)):
        if not _is_pairable_unpack(target, value):
            return _unpack_binding_names(target)
        _states: dict[str, bool | None] = {}
        for element, element_value in zip(
                target.elts, value.elts, strict=True):
            _states.update(_target_binding_states(
                element, element_value, unpacked=True))
        return _states
    if isinstance(target, ast.Starred):
        return _unpack_binding_names(target.value)
    return {}
def _assign_binding_states(stmt: ast.Assign) -> dict[str, bool | None]:
    _states = _expression_binding_states(stmt.value)
    if is_none_constant(stmt.value):
        for target in stmt.targets:
            _names: set = set()
            assign_target_names(target, _names)
            _states.update(dict.fromkeys(_names, False))
        return _states
    for target in stmt.targets:
        _states.update(_target_binding_states(target, stmt.value))
    return _states
def _assign_stmt_faces(stmt: ast.Assign) -> tuple[set, set, set]:
    return _binding_faces_from_states(_assign_binding_states(stmt))
def _annassign_binding_faces(stmt: ast.AnnAssign) -> tuple[set, set, set]:
    if stmt.value is None:
        return _no_binding_faces(stmt)
    _states = _expression_binding_states(stmt.value)
    _update_expression_states(
        _states, _target_binding_states(stmt.target, stmt.value))
    return _binding_faces_from_states(_states)
def _with_binding_faces(stmt: ast.With | ast.AsyncWith) -> tuple[set, set, set]:
    _states = _expression_sequence_states(
        item.context_expr for item in stmt.items)
    _names: set = set()
    for item in stmt.items:
        if item.optional_vars is not None:
            assign_target_names(item.optional_vars, _names)
    _states.update(dict.fromkeys(_names, None))
    return _binding_faces_from_states(_states)
def _import_binding_faces(stmt: ast.Import | ast.ImportFrom) -> tuple[set, set, set]:
    names = set(_import_bound_aliases(stmt))
    return names, set(), names
def _def_name_faces(stmt: ast.AST) -> tuple[set, set, set]:
    expressions = list(stmt.decorator_list)
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
        expressions.extend(stmt.args.defaults)
        expressions.extend(default for default in stmt.args.kw_defaults
                           if default is not None)
    elif isinstance(stmt, ast.ClassDef):
        expressions.extend(stmt.bases)
        expressions.extend(keyword.value for keyword in stmt.keywords)
    _states = _expression_sequence_states(expressions)
    _states[stmt.name] = True
    return _binding_faces_from_states(_states)
def _no_binding_faces(_stmt: ast.AST) -> tuple[set, set, set]:
    return set(), set(), set()
def _expr_binding_faces(stmt: ast.Expr) -> tuple[set, set, set]:
    return _binding_faces_from_states(_expression_binding_states(stmt.value))
def _test_binding_faces(stmt: ast.AST) -> tuple[set, set, set]:
    return _binding_faces_from_states(_expression_binding_states(stmt.test))
def _iter_binding_faces(stmt: ast.AST) -> tuple[set, set, set]:
    return _binding_faces_from_states(_expression_binding_states(stmt.iter))
_STATEMENT_BINDING_FACES = {
    ast.Assign: _assign_stmt_faces,
    ast.AnnAssign: _annassign_binding_faces,
    ast.FunctionDef: _def_name_faces,
    ast.AsyncFunctionDef: _def_name_faces,
    ast.ClassDef: _def_name_faces,
    ast.For: _iter_binding_faces,
    ast.AsyncFor: _iter_binding_faces,
    ast.If: _test_binding_faces,
    ast.While: _test_binding_faces,
    ast.Assert: _test_binding_faces,
    ast.With: _with_binding_faces,
    ast.AsyncWith: _with_binding_faces,
    ast.Expr: _expr_binding_faces,
    ast.Import: _import_binding_faces,
    ast.ImportFrom: _import_binding_faces,
}
def _stmt_binding_faces(stmt: ast.AST) -> tuple[set, set, set]:
    _faces = _STATEMENT_BINDING_FACES.get(type(stmt), _no_binding_faces)
    return _faces(stmt)
def _record_binding_faces(stmt, names: list, none_names: list,
                          recover_names: list, none_events: dict,
                          none_final: set, top_bind_lineno: dict,
                          *, record_all_recoveries: bool = False) -> None:
    for name in names:
        top_bind_lineno.setdefault(name, stmt.lineno)
    for name in none_names:
        none_events.setdefault(name, []).append((stmt.lineno, True))
    for name in recover_names:
        if record_all_recoveries:
            none_events.setdefault(name, []).append((stmt.lineno, False))
        elif name in none_events:
            none_events[name].append((stmt.lineno, False))
    if none_names:
        none_final.update(none_names)
    if recover_names:
        none_final.difference_update(recover_names)
def _iter_definite_binding_stmts(body: list):
    for stmt in body:
        yield stmt
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            yield from _iter_definite_binding_stmts(stmt.body)
        elif isinstance(stmt, TRY_TYPES):
            yield from _iter_definite_binding_stmts(stmt.finalbody)
def _scan_top_level_bindings(body: list, *,
                             terminal_only: bool = True) -> tuple[dict, dict]:
    none_events: dict[str, list[tuple[int, bool]]] = {}
    none_final: set = set()
    top_bind_lineno: dict[str, int] = {}
    for stmt in _iter_definite_binding_stmts(body):
        names, none_names, recover_names = _stmt_binding_faces(stmt)
        if not names:
            continue
        _record_binding_faces(
            stmt, names, none_names, recover_names, none_events, none_final,
            top_bind_lineno, record_all_recoveries=not terminal_only)
    return ({name: events for name, events in none_events.items()
             if not terminal_only or name in none_final}, top_bind_lineno)
def _assign_stmt_targets(n: ast.AST) -> tuple:
    return tuple(n.targets)
def _annassign_target_of(n: ast.AST) -> tuple:
    return (n.target,) if n.value is not None else ()
def _single_target_of(n: ast.AST) -> tuple:
    return (n.target,)
def _with_optional_vars(n: ast.AST) -> tuple:
    return tuple(item.optional_vars for item in n.items
                 if item.optional_vars is not None)
_TARGET_BINDING_EXTRACTORS = {
    ast.Assign: _assign_stmt_targets,
    ast.AnnAssign: _annassign_target_of,
    ast.AugAssign: _single_target_of,
    ast.NamedExpr: _single_target_of,
    ast.For: _single_target_of,
    ast.AsyncFor: _single_target_of,
    ast.With: _with_optional_vars,
    ast.AsyncWith: _with_optional_vars,
}
def _apply_target_binding_node(n: ast.AST, binds: set) -> bool:
    _extract = _TARGET_BINDING_EXTRACTORS.get(type(n))
    if _extract is None:
        return False
    for _target in _extract(n):
        assign_target_names(_target, binds)
    return True
def _optional_capture_name(n: ast.AST) -> tuple:
    return (n.name,) if n.name else ()
def _mapping_rest_name(n: ast.AST) -> tuple:
    return (n.rest,) if n.rest else ()
_CAPTURE_BINDING_EXTRACTORS = {
    ast.ExceptHandler: _optional_capture_name,
    ast.MatchAs: _optional_capture_name,
    ast.MatchStar: _optional_capture_name,
    ast.MatchMapping: _mapping_rest_name,
    ast.Import: _import_bound_aliases,
    ast.ImportFrom: _import_bound_aliases,
}
def _apply_capture_decl_node(n: ast.AST, binds: set,
                             globals_: set, nonlocals_: set) -> bool:
    _extract = _CAPTURE_BINDING_EXTRACTORS.get(type(n))
    if _extract is not None:
        binds.update(_extract(n))
        return True
    if isinstance(n, ast.Global):
        globals_.update(n.names)
        return True
    if isinstance(n, ast.Nonlocal):
        nonlocals_.update(n.names)
        return True
    return False
def _apply_scope_bind_node(n: ast.AST, binds: set,
                           globals_: set, nonlocals_: set) -> None:
    if _apply_target_binding_node(n, binds):
        return
    _apply_capture_decl_node(n, binds, globals_, nonlocals_)
def _scope_binding_names(container: ast.AST) -> tuple:
    binds = collect_param_names(container)
    globals_: set = set()
    nonlocals_: set = set()
    if isinstance(container, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)):
        stack = list(container.body)
    elif isinstance(container, ast.Lambda):
        stack = [container.body]
    else:
        stack = []
    while stack:
        n = stack.pop()
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            binds.add(n.name)
            continue
        if isinstance(n, ast.Lambda):
            continue
        if isinstance(n, _COMPREHENSION_NODES):
            binds.update(expr_binds(n))
            continue
        _apply_scope_bind_node(n, binds, globals_, nonlocals_)
        stack.extend(ast.iter_child_nodes(n))
    binds -= globals_ | nonlocals_
    if isinstance(container, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)):
        none_bind_lineno, top_bind_lineno = _scan_top_level_bindings(
            container.body, terminal_only=False)
        for name, h_events in _try_handler_binding_events(
                container.body).items():
            none_bind_lineno.setdefault(name, []).extend(h_events)
    else:
        none_bind_lineno, top_bind_lineno = {}, {}
    for name, events in _default_none_parameter_events(container).items():
        none_bind_lineno.setdefault(name, []).extend(events)
    none_bind_lineno = {n: ln for n, ln in none_bind_lineno.items()
                        if n in binds}
    top_bind_lineno = {n: ln for n, ln in top_bind_lineno.items()
                       if n in binds}
    return (binds, globals_, nonlocals_,
            none_bind_lineno, top_bind_lineno)
def _default_none_parameter_events(container: ast.AST) -> dict:
    if not isinstance(container, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.Lambda)):
        return {}
    parameters = container.args
    positional = [*parameters.posonlyargs, *parameters.args]
    default_offset = len(positional) - len(parameters.defaults)
    pairs = list(zip(positional[default_offset:], parameters.defaults,
                     strict=True))
    pairs.extend(zip(parameters.kwonlyargs, parameters.kw_defaults,
                     strict=True))
    lineno = getattr(container, 'lineno', 0)
    return {
        parameter.arg: [(lineno, True)]
        for parameter, default in pairs
        if default is not None and is_none_constant(default)
    }
@dataclass(frozen=True)
class _ShadowQuery:
    node: ast.AST
    name: str
    node_lineno: int
    parent_map: dict
    scope_cache: dict
def _scope_bind_verdict(anc: ast.AST, name: str, node_lineno: int,
                        scope_cache: dict, *,
                        dynamic_lookup: bool) -> bool | None:
    _key = id(anc)
    if _key not in scope_cache:
        scope_cache[_key] = _scope_binding_names(anc)
    binds, globals_, _nonlocals, none_binds, top_binds = scope_cache[_key]
    if name in globals_:
        return False
    if name not in binds:
        return None
    if dynamic_lookup and (name not in top_binds
                           or node_lineno <= top_binds[name]):
        return None
    return _terminal_state_exempt(none_binds.get(name), node_lineno)
def _terminal_state_exempt(events: list[tuple[int, bool]] | None,
                           node_lineno: int) -> bool:
    if not events:
        return True
    return _latest_none_state(events, node_lineno) is not True
def _comp_target_index(anc: ast.AST, name: str) -> int | None:
    for _i, _comp in enumerate(anc.generators):
        _targets: set = set()
        assign_target_names(_comp.target, _targets)
        if name in _targets:
            return _i
    return None
def _comp_generator_index(anc: ast.AST, child: ast.AST) -> int:
    for _i, _gen in enumerate(anc.generators):
        if _gen is child:
            return _i
    return -1
def _path_via_iter(node: ast.AST, child: ast.AST,
                   parent_map: dict) -> bool:
    iterator = getattr(child, 'iter', None)
    cur = node
    while cur is not None and cur is not child:
        if cur is iterator:
            return True
        cur = parent_map.get(cur)
    return False
def _generator_defers_node(node: ast.AST, generator: ast.GeneratorExp,
                           parent_map: dict) -> bool:
    return not (generator.generators and _path_via_iter(
        node, generator.generators[0], parent_map))
def _in_deferred_generator_context(node: ast.AST, parent_map: dict) -> bool:
    current = node
    while current in parent_map:
        parent = parent_map[current]
        if (isinstance(parent, ast.GeneratorExp)
                and _generator_defers_node(node, parent, parent_map)):
            return True
        current = parent
    return False
def _comp_scope_verdict(anc: ast.AST, child: ast.AST,
                        query: _ShadowQuery) -> bool | None:
    _bound_idx = _comp_target_index(anc, query.name)
    if _bound_idx is None:
        return None
    if not isinstance(child, ast.comprehension):
        return True
    _k = _comp_generator_index(anc, child)
    if _k > _bound_idx:
        return True
    if _k == _bound_idx and not _path_via_iter(
            query.node, child, query.parent_map):
        return True
    return None
def _is_def_time_context(anc: ast.AST, child: ast.AST) -> bool:
    if isinstance(anc, ast.Lambda):
        return child is not anc.body
    if isinstance(anc, (ast.FunctionDef, ast.AsyncFunctionDef,
                        ast.ClassDef)):
        return child not in anc.body
    return False
def _container_shadow_verdict(anc: ast.AST, child: ast.AST,
                              query: _ShadowQuery,
                              crossed_scope: bool) -> tuple[bool | None, bool]:
    if isinstance(anc, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return (_scope_bind_verdict(
            anc, query.name, query.node_lineno, query.scope_cache,
            dynamic_lookup=False), True)
    if isinstance(anc, ast.Lambda):
        return (_scope_bind_verdict(
            anc, query.name, query.node_lineno, query.scope_cache,
            dynamic_lookup=False), True)
    if isinstance(anc, ast.ClassDef):
        if crossed_scope:
            return None, crossed_scope
        return (_scope_bind_verdict(
            anc, query.name, query.node_lineno, query.scope_cache,
            dynamic_lookup=True), crossed_scope)
    return _comp_scope_verdict(anc, child, query), True
def _is_scope_shadowed(node: ast.AST, name: str, parent_map: dict,
                       scope_cache: dict) -> bool:
    query = _ShadowQuery(
        node=node,
        name=name,
        node_lineno=getattr(node, 'lineno', 0),
        parent_map=parent_map,
        scope_cache=scope_cache,
    )
    crossed_scope = False
    child = node
    anc = parent_map.get(node)
    while anc is not None:
        if _is_def_time_context(anc, child):
            child, anc = anc, parent_map.get(anc)
            continue
        if isinstance(anc, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda, ast.ClassDef,
                            *_COMPREHENSION_NODES)):
            verdict, crossed_scope = _container_shadow_verdict(
                anc, child, query, crossed_scope)
            if verdict is not None:
                return verdict
        child, anc = anc, parent_map.get(anc)
    return False
def _body_early_exits(stmts: list) -> bool:
    if not stmts:
        return False
    return isinstance(
        stmts[-1], (ast.Return, ast.Raise, ast.Break, ast.Continue))
def _statements_after(parent_map: dict, node: ast.AST) -> list:
    parent = parent_map.get(node)
    if parent is None:
        return []
    for _attr in ("body", "orelse", "finalbody"):
        _lst = getattr(parent, _attr, None)
        if not isinstance(_lst, list):
            continue
        for _idx, _stmt in enumerate(_lst):
            if _stmt is node:
                return _lst[_idx + 1:]
    return []
def in_protected_region(node: ast.AST, protected_ids: set,
                        parent_map: dict, *,
                        stop_at_deferred: bool = False) -> bool:
    _anc = node
    while _anc is not None:
        if id(_anc) in protected_ids:
            return True
        parent = parent_map.get(_anc)
        if (stop_at_deferred and isinstance(parent, ast.GeneratorExp)
                and _generator_defers_node(node, parent, parent_map)):
            return False
        if (isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef))
                and _anc in parent.body):
            return False
        if isinstance(parent, ast.Lambda) and _anc is parent.body:
            return False
        _anc = parent
    return False
def _break_binds_loop(brk: ast.Break, loop: ast.AST, parent_map: dict) -> bool:
    cur: ast.AST = brk
    while cur in parent_map:
        parent = parent_map[cur]
        if isinstance(parent, (ast.For, ast.AsyncFor, ast.While)):
            if cur in parent.orelse:
                cur = parent
                continue
            if cur in parent.body:
                return parent is loop
            cur = parent
            continue
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.Lambda)):
            return False
        cur = parent
    return False
def _has_bound_break(loop: ast.While, parent_map: dict) -> bool:
    return any(_break_binds_loop(brk, loop, parent_map)
               for brk in walk_nodes(loop) if isinstance(brk, ast.Break))
def _name_recovered_before_statement(node: ast.AST, boundary: ast.AST,
                                     name: str, parent_map: dict) -> bool:
    prior_blocks: list[list] = []
    child = node
    parent = parent_map.get(child)
    while parent is not None:
        if (isinstance(parent, TRY_TYPES)
                and (isinstance(child, ast.ExceptHandler)
                     or child in parent.finalbody)):
            return False
        prior = _prior_statement_block(parent, child)
        if prior:
            prior_blocks.append(prior)
        if parent is boundary:
            break
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.ClassDef, ast.Lambda)):
            return False
        child, parent = parent, parent_map.get(parent)
    if parent is not boundary:
        return False
    guarded = False
    for prior in reversed(prior_blocks):
        _stmts, guarded = _guarded_block_state(
            prior, name, guarded=guarded)
    return guarded
def _while_breaks_preserve_name(loop: ast.While, name: str,
                                parent_map: dict) -> bool:
    return all(
        _name_recovered_before_statement(brk, loop, name, parent_map)
        for brk in walk_nodes(loop)
        if isinstance(brk, ast.Break)
        and _break_binds_loop(brk, loop, parent_map))
def _positive_guard_names(test: ast.AST) -> set:
    names: set = set()
    if isinstance(test, ast.NamedExpr) and isinstance(test.target, ast.Name):
        names.add(test.target.id)
    is_not_none_name = _projected_name(test, 'not_none')
    if is_not_none_name:
        names.add(is_not_none_name)
    guard_call_name = _guard_call_first_name(test)
    if guard_call_name:
        names.add(guard_call_name)
    if isinstance(test, ast.Name):
        names.add(test.id)
    return names
def _guard_invalidating_walrus_names(test: ast.AST) -> set[str]:
    names: set[str] = set()
    stack = [test]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Lambda):
            stack.extend(node.args.defaults)
            stack.extend(default for default in node.args.kw_defaults
                         if default is not None)
            continue
        if isinstance(node, ast.GeneratorExp):
            if node.generators:
                stack.append(node.generators[0].iter)
            continue
        if isinstance(node, ast.NamedExpr):
            states = _target_binding_states(node.target, node.value)
            names.update(name for name, state in states.items()
                         if state is not True)
        stack.extend(ast.iter_child_nodes(node))
    return names
def _positive_guard_hits(test: ast.AST) -> set:
    if not (isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And)):
        return _positive_guard_names(test)
    guarded: set[str] = set()
    for value in test.values:
        guarded.difference_update(_guard_invalidating_walrus_names(value))
        guarded.update(_positive_guard_hits(value))
    return guarded
def _successors_allowed(node: ast.AST, parent_map: dict) -> bool:
    return not (isinstance(node, ast.While)
                and _has_bound_break(node, parent_map))
def _single_compare(test: ast.AST, ops: tuple):
    if not isinstance(test, ast.Compare):
        return None
    if len(test.ops) != 1 or len(test.comparators) != 1:
        return None
    if not isinstance(test.ops[0], ops):
        return None
    return test.left, test.ops[0], test.comparators[0]
def _compared_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.NamedExpr) and isinstance(node.target, ast.Name):
        return node.target.id
    return None
_NONE_IS_OPS = (ast.Is, ast.Eq)
_NONE_ISNOT_OPS = (ast.IsNot, ast.NotEq)
def _none_compare_projection(test: ast.AST) -> tuple[str, str] | None:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        inner = _none_compare_projection(test.operand)
        if inner is None:
            return None
        name, polarity = inner
        return name, ('is_none' if polarity == 'not_none' else 'not_none')
    parsed = _single_compare(test, _NONE_IS_OPS + _NONE_ISNOT_OPS)
    if parsed is None:
        return None
    left, op, comparator = parsed
    polarity = ('is_none' if isinstance(op, _NONE_IS_OPS) else 'not_none')
    name = _compared_name(left)
    if name is not None:
        if not is_none_constant(comparator):
            return None
        return name, polarity
    name = _compared_name(comparator)
    if name is None or not is_none_constant(left):
        return None
    return name, polarity
def _targets_mention(targets, name: str) -> bool:
    _names: set = set()
    for _t in targets:
        assign_target_names(_t, _names)
    return name in _names
def _block_loses_guard(body: list, name: str) -> bool:
    _stmts, final_state = _guarded_block_state(body, name, guarded=True)
    return not final_state
def _guarded_name_final_state(stmt: ast.AST, name: str) -> bool | None:
    names, none_names, recover_names = _stmt_binding_faces(stmt)
    if name in none_names:
        return False
    if name in recover_names:
        return True
    if name in names:
        return False
    if isinstance(stmt, ast.Delete):
        return False if _targets_mention(stmt.targets, name) else None
    if isinstance(stmt, TRY_TYPES):
        final_state = _path_final_none_state(
            stmt.finalbody, name, stmt.end_lineno or stmt.lineno)
        if final_state is not None:
            return not final_state
        if _block_loses_guard(stmt.finalbody, name):
            return False
        if (not _body_early_exits(stmt.body)
                and _block_loses_guard(stmt.body + stmt.orelse, name)):
            return False
        if any(not _body_early_exits(handler.body)
               and _block_loses_guard(handler.body, name)
               for handler in stmt.handlers):
            return False
        if _try_all_paths_recover(stmt, name):
            return True
        if _try_any_fallthrough_none(stmt, name):
            return False
    if (isinstance(stmt, (ast.For, ast.AsyncFor))
            and _targets_mention((stmt.target,), name)):
        return False
    if isinstance(stmt, (ast.With, ast.AsyncWith, ast.For, ast.AsyncFor,
                         ast.While)):
        if _block_loses_guard(stmt.body, name):
            return False
        if _block_loses_guard(getattr(stmt, 'orelse', []), name):
            return False
    return None
def _projected_name(test: ast.AST, polarity: str) -> str | None:
    projection = _none_compare_projection(test)
    if projection is None or projection[1] != polarity:
        return None
    return projection[0]
def _guard_call_first_name(test: ast.AST) -> str | None:
    if (isinstance(test, ast.Call)
            and isinstance(test.func, ast.Name)
            and test.func.id == 'callable'
            and test.args
            and isinstance(test.args[0], ast.Name)):
        return test.args[0].id
    return None
def _statement_evaluation_expressions(stmt: ast.AST) -> list[ast.expr]:
    if isinstance(stmt, ast.Assign):
        return [stmt.value, *stmt.targets]
    if isinstance(stmt, ast.AnnAssign):
        return ([stmt.value, stmt.target] if stmt.value is not None
                else [stmt.target])
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return [item.context_expr for item in stmt.items]
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        return [stmt.iter, stmt.target]
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return [*stmt.decorator_list, *stmt.args.defaults,
                *(default for default in stmt.args.kw_defaults
                  if default is not None)]
    if isinstance(stmt, ast.ClassDef):
        return [*stmt.decorator_list, *stmt.bases,
                *(keyword.value for keyword in stmt.keywords)]
    return [child for child in ast.iter_child_nodes(stmt)
            if isinstance(child, ast.expr)]
def _guarded_expression_nodes(node: ast.AST, name: str) -> list[ast.AST]:
    regions: dict = {}
    _protect_expression_before_none_rebind(regions, name, node)
    return list(regions.get(name, ()))
def _guarded_container_stmts(stmt: ast.AST, name: str) -> list[ast.AST]:
    stmts: list[ast.AST] = []
    entry_guarded = True
    for expression in _statement_evaluation_expressions(stmt):
        if entry_guarded:
            stmts.extend(_guarded_expression_nodes(expression, name))
        states = _expression_binding_states(expression)
        if name in states:
            entry_guarded = states[name] is True
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        if _targets_mention((stmt.target,), name):
            entry_guarded = False
    elif isinstance(stmt, (ast.With, ast.AsyncWith)):
        for item in stmt.items:
            if (item.optional_vars is not None
                    and _targets_mention((item.optional_vars,), name)):
                entry_guarded = False
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        body_stmts, _body_state = _guarded_block_state(
            stmt.body, name, guarded=entry_guarded)
        stmts.extend(body_stmts)
        return stmts
    if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
        body_stmts, body_state = _guarded_block_state(
            stmt.body, name, guarded=entry_guarded)
        stmts.extend(body_stmts)
        else_stmts, _else_state = _guarded_block_state(
            stmt.orelse, name, guarded=entry_guarded and body_state)
        stmts.extend(else_stmts)
        return stmts
    body_stmts, body_state = _guarded_block_state(
        stmt.body, name, guarded=entry_guarded)
    stmts.extend(body_stmts)
    else_stmts, else_state = _guarded_block_state(
        stmt.orelse, name, guarded=body_state)
    stmts.extend(else_stmts)
    body_may_rebind = any(
        name in _possible_binding_names(statement) for statement in stmt.body)
    handler_start = entry_guarded and not body_may_rebind
    # finalbody 在每条离开 try 的路径上都会执行：正常路径取 orelse 之后的终态
    # （body 早退时 orelse 不执行，取 body 终态）；每个 handler 的终态都参与合流，
    # 早退的 handler 同样会先经过 finalbody，不能被跳过。
    final_guarded = (
        body_state if _body_early_exits(stmt.body) else else_state)
    for handler in stmt.handlers:
        if handler_start and handler.type is not None:
            stmts.extend(_guarded_expression_nodes(handler.type, name))
        handler_stmts, handler_state = _guarded_block_state(
            handler.body, name, guarded=handler_start)
        stmts.extend(handler_stmts)
        final_guarded = final_guarded and handler_state
    final_stmts, _final_state = _guarded_block_state(
        stmt.finalbody, name, guarded=final_guarded)
    stmts.extend(final_stmts)
    return stmts
def _guarded_statement_stmts(stmt: ast.AST, name: str) -> list[ast.AST]:
    if isinstance(stmt, (ast.With, ast.AsyncWith, ast.For, ast.AsyncFor,
                         ast.While, *TRY_TYPES)):
        return _guarded_container_stmts(stmt, name)
    expressions = _statement_evaluation_expressions(stmt)
    if not any(name in _guard_invalidating_walrus_names(expression)
               for expression in expressions):
        return [stmt]
    stmts: list[ast.AST] = []
    for expression in expressions:
        stmts.extend(_guarded_expression_nodes(expression, name))
        if name in _guard_invalidating_walrus_names(expression):
            break
    return stmts
def _guarded_if_stmts(node: ast.If, name: str, guarded: bool
                      ) -> tuple[list[ast.AST], bool]:
    stmts: list[ast.AST] = (
        _guarded_expression_nodes(node.test, name) if guarded else [])
    test_states = _expression_binding_states(node.test)
    if name in test_states:
        guarded = test_states[name] is True
    body_stmts, body_state = _guarded_block_state(
        node.body, name, guarded=guarded)
    else_stmts, else_state = _guarded_block_state(
        node.orelse, name, guarded=guarded)
    stmts.extend(body_stmts)
    stmts.extend(else_stmts)
    if _body_early_exits(node.body):
        return stmts, else_state
    if _body_early_exits(node.orelse):
        return stmts, body_state
    return stmts, body_state and else_state
def _guarded_block_state(body: list, name: str, *, guarded: bool
                         ) -> tuple[list[ast.AST], bool]:
    stmts: list[ast.AST] = []
    for stmt in body:
        if isinstance(stmt, ast.If):
            nested_stmts, guarded = _guarded_if_stmts(stmt, name, guarded)
            stmts.extend(nested_stmts)
            continue
        if guarded:
            stmts.extend(_guarded_statement_stmts(stmt, name))
        state = _guarded_name_final_state(stmt, name)
        if state is not None:
            guarded = state
    return stmts, guarded
def _guarded_stmts(body: list, name: str, *, guarded_start: bool) -> list:
    stmts, _final_state = _guarded_block_state(
        body, name, guarded=guarded_start)
    return stmts
def _if_fallthrough_guarded(node: ast.If, name: str, *,
                            body_guarded: bool, else_guarded: bool) -> bool:
    _body_stmts, body_state = _guarded_block_state(
        node.body, name, guarded=body_guarded)
    _else_stmts, else_state = _guarded_block_state(
        node.orelse, name, guarded=else_guarded)
    if _body_early_exits(node.body):
        return else_state
    if _body_early_exits(node.orelse):
        return body_state
    return body_state and else_state
def _or_members(test: ast.AST):
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.Or):
        for value in test.values:
            yield from _or_members(value)
        return
    yield test
def _collect_is_none_names(test: ast.AST) -> set:
    names = {_projected_name(member, 'is_none')
             for member in _or_members(test)}
    names.discard(None)
    return names
def _collect_not_names(test: ast.AST, within: set | None = None) -> set:
    names = {_not_name(member, within) for member in _or_members(test)}
    names.discard(None)
    return names
def _not_name(test: ast.AST, within: set | None) -> str | None:
    if not (isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)):
        return None
    operand = test.operand
    if isinstance(operand, ast.Name):
        name = operand.id
    elif within is not None:
        return None
    elif (isinstance(operand, ast.NamedExpr)
          and isinstance(operand.target, ast.Name)):
        name = operand.target.id
    else:
        name = _guard_call_first_name(operand)
    if name is None or within is not None and name not in within:
        return None
    return name
def _repair_assigned_names(stmts: list) -> set:
    names: set = set()
    for stmt in stmts:
        for name in _assigned_names(stmt):
            state = _guarded_name_final_state(stmt, name)
            if state is True:
                names.add(name)
            elif state is False:
                names.discard(name)
    return names
def _assigned_names(stmt: ast.stmt) -> set:
    if isinstance(stmt, ast.Assign):
        touched: set = set()
        for target in stmt.targets:
            assign_target_names(target, touched)
        return touched
    if (isinstance(stmt, ast.AnnAssign)
            and isinstance(stmt.target, ast.Name)
            and stmt.value is not None):
        return {stmt.target.id}
    if isinstance(stmt, ast.Delete):
        touched = set()
        for target in stmt.targets:
            assign_target_names(target, touched)
        return touched
    return set()
def _protect_ids(regions: dict, name: str, stmts: list) -> None:
    regions.setdefault(name, set()).update(id(s) for s in stmts)
def _negative_guard_names(test: ast.AST) -> set:
    names = _collect_is_none_names(test) | _collect_not_names(test)
    names.difference_update(_guard_invalidating_walrus_names(test))
    return names
def _protect_orelse(regions: dict, names: set, node: ast.AST) -> None:
    for name in names:
        _protect_ids(regions, name, _guarded_stmts(
            node.orelse, name, guarded_start=True))
def _protect_successors(regions: dict, names: set, node: ast.AST,
                        parent_map: dict) -> None:
    stmts = _statements_after(parent_map, node)
    for name in names:
        _protect_ids(regions, name, _guarded_stmts(
            stmts, name, guarded_start=True))
def _conditional_guard_regions(regions: dict, node: ast.AST,
                               parent_map: dict) -> None:
    test = node.test
    for name in _positive_guard_hits(test):
        _protect_ids(regions, name, _guarded_stmts(
            node.body, name, guarded_start=True))
    neg_names = _negative_guard_names(test)
    successors_ok = _successors_allowed(node, parent_map)
    if successors_ok:
        _protect_orelse(regions, neg_names, node)
    elif isinstance(node, ast.While):
        for name in neg_names:
            if _while_breaks_preserve_name(node, name, parent_map):
                _protect_orelse(regions, {name}, node)
    if neg_names and _body_early_exits(node.body) and successors_ok:
        for name in neg_names:
            if _if_fallthrough_guarded(
                    node, name, body_guarded=False, else_guarded=True):
                _protect_successors(regions, {name}, node, parent_map)
    _repair_guard_channel(regions, node, parent_map, successors_ok)
def _protect_expression_before_none_rebind(
        regions: dict, name: str, node: ast.AST) -> None:
    if name not in _guard_invalidating_walrus_names(node):
        _protect_ids(regions, name, [node])
        return
    if isinstance(node, ast.NamedExpr):
        children = [node.value]
    elif isinstance(node, ast.Call):
        children = [node.func]
        arguments = sorted((*node.args, *node.keywords), key=_source_order)
        for argument in arguments:
            children.append(argument.value if isinstance(argument, ast.keyword)
                            else argument)
    elif isinstance(node, ast.Dict):
        children = []
        for key, value in zip(node.keys, node.values, strict=True):
            if key is not None:
                children.append(key)
            children.append(value)
    elif isinstance(node, ast.Lambda):
        children = [*node.args.defaults,
                    *(default for default in node.args.kw_defaults
                      if default is not None)]
    elif isinstance(node, ast.GeneratorExp):
        children = ([node.generators[0].iter]
                    if node.generators else [])
    elif isinstance(node, _COMPREHENSION_NODES):
        children = []
        for generator in node.generators:
            children.append(generator.iter)
            children.extend(generator.ifs)
        if isinstance(node, ast.DictComp):
            children.extend((node.key, node.value))
        else:
            children.append(node.elt)
    elif isinstance(node, ast.IfExp):
        _protect_expression_before_none_rebind(regions, name, node.test)
        if name in _guard_invalidating_walrus_names(node.test):
            return
        for branch in (node.body, node.orelse):
            _protect_expression_before_none_rebind(regions, name, branch)
        return
    else:
        children = [child for child in ast.iter_child_nodes(node)
                    if isinstance(child, ast.expr)]
    for child in children:
        _protect_expression_before_none_rebind(regions, name, child)
        if name in _guard_invalidating_walrus_names(child):
            break
def _ifexp_guard_regions(regions: dict, node: ast.IfExp) -> None:
    test = node.test
    for name in _positive_guard_hits(test):
        _protect_expression_before_none_rebind(regions, name, node.body)
    for name in _negative_guard_names(test):
        _protect_expression_before_none_rebind(regions, name, node.orelse)
def _repair_guard_channel(regions: dict, node: ast.AST,
                          parent_map: dict, successors_ok: bool) -> None:
    if not _collect_is_none_names(node.test):
        return
    repair_names = (_collect_is_none_names(node.test)
                    & _repair_assigned_names(node.body))
    if successors_ok:
        _protect_orelse(regions, repair_names, node)
        for name in repair_names:
            if _if_fallthrough_guarded(
                    node, name, body_guarded=False, else_guarded=True):
                _protect_successors(regions, {name}, node, parent_map)
    for name in repair_names:
        _protect_ids(regions, name, _guarded_stmts(
            node.body, name, guarded_start=False))
def _boolop_guard_regions(regions: dict, node: ast.BoolOp) -> None:
    if not isinstance(node.op, (ast.And, ast.Or)):
        return
    guard_hits = (_positive_guard_hits if isinstance(node.op, ast.And)
                  else _negative_guard_names)
    guarded: set[str] = set()
    for value in node.values:
        for name in guarded:
            _protect_expression_before_none_rebind(regions, name, value)
        guarded.difference_update(_guard_invalidating_walrus_names(value))
        guarded.update(guard_hits(value))
def _assert_guard_regions(regions: dict, node: ast.Assert,
                          parent_map: dict) -> None:
    for name in _positive_guard_hits(node.test):
        _protect_ids(regions, name, _guarded_stmts(
            _statements_after(parent_map, node), name, guarded_start=True))
def collect_guarded_regions(tree: ast.AST, parent_map: dict) -> dict:
    regions: dict[str, set[int]] = {}
    for node in walk_nodes(tree):
        if isinstance(node, (ast.If, ast.While)):
            _conditional_guard_regions(regions, node, parent_map)
        elif isinstance(node, ast.Assert):
            _assert_guard_regions(regions, node, parent_map)
        elif isinstance(node, ast.IfExp):
            _ifexp_guard_regions(regions, node)
        elif isinstance(node, ast.BoolOp):
            _boolop_guard_regions(regions, node)
    return regions
def _iter_module_level_trys(tree: ast.AST):
    # 遍历口径与 _scan_try_chain（None 赋值采集）保持一致：with 体与 try 内的
    # 条件/循环块都是确定可达的执行单元，嵌套其中的 try 同样参与旗标关联；
    # 模块顶层 if/for/while 体是条件执行，不纳入。
    stack: list = [(child, False) for child in ast.iter_child_nodes(tree)]
    while stack:
        node, within_try = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            continue
        if isinstance(node, TRY_TYPES):
            yield node
            for child in (*node.body, *node.orelse, *node.finalbody,
                          *(handler.body for handler in node.handlers)):
                stack.append((child, True))
            continue
        if isinstance(node, (ast.With, ast.AsyncWith)):
            stack.extend((child, within_try) for child in node.body)
        elif (within_try and isinstance(
                node, (ast.If, ast.For, ast.AsyncFor, ast.While))):
            stack.extend((child, True) for child in (*node.body, *node.orelse))
def _try_true_flag_names(try_node) -> set:
    flag_names: set = set()
    for stmt in try_node.body:
        assigned = _const_assign(stmt)
        if assigned is None:
            continue
        target_names, value = assigned
        if value is True:
            flag_names |= target_names
    return flag_names
def _const_assign(stmt: ast.stmt) -> tuple[set, object] | None:
    if isinstance(stmt, ast.Assign):
        targets, value = stmt.targets, stmt.value
    elif isinstance(stmt, ast.AnnAssign):
        if stmt.value is None:
            return None
        targets, value = (stmt.target,), stmt.value
    else:
        return None
    if not isinstance(value, ast.Constant):
        return None
    target_names = {t.id for t in targets if isinstance(t, ast.Name)}
    return target_names, value.value
def _possible_binding_names(stmt: ast.AST) -> set[str]:
    names: set[str] = set()
    globals_: set[str] = set()
    nonlocals_: set[str] = set()
    stack = [stmt]
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            names.add(node.name)
            continue
        if isinstance(node, ast.Lambda):
            continue
        if isinstance(node, _COMPREHENSION_NODES):
            names.update(expr_binds(node))
            continue
        _apply_scope_bind_node(node, names, globals_, nonlocals_)
        if isinstance(node, ast.Delete):
            for target in node.targets:
                assign_target_names(target, names)
        stack.extend(ast.iter_child_nodes(node))
    return names - globals_ - nonlocals_
def _statements_preserve_false(stmts: list, name: str) -> bool:
    return all(_statement_preserves_false(stmt, name) for stmt in stmts)
def _statement_preserves_false(stmt: ast.AST, name: str) -> bool:
    assigned = _const_assign(stmt)
    if assigned is not None:
        target_names, value = assigned
        return name not in target_names or value is False
    if isinstance(stmt, ast.If):
        body_safe = _statements_preserve_false(stmt.body, name)
        else_safe = _statements_preserve_false(stmt.orelse, name)
        if _body_early_exits(stmt.body):
            return else_safe
        if _body_early_exits(stmt.orelse):
            return body_safe
        return body_safe and else_safe
    return name not in _possible_binding_names(stmt)
def _path_none_false(stmts: list, none_names: set | None = None,
                       false_flags: set | None = None) -> tuple[set, set]:
    none_names = set() if none_names is None else set(none_names)
    false_flags = set() if false_flags is None else set(false_flags)
    for stmt in stmts:
        assigned = _const_assign(stmt)
        if assigned is None:
            false_flags = {name for name in false_flags
                           if _statement_preserves_false(stmt, name)}
            continue
        target_names, value = assigned
        if value is None:
            none_names |= target_names
        for name in target_names:
            if value is False:
                false_flags.add(name)
            else:
                false_flags.discard(name)
    return none_names, false_flags
def _top_level_try_false_flags(tree: ast.AST) -> dict[int, set[str]]:
    initial_flags: dict[int, set[str]] = {}
    false_flags: set[str] = set()
    for stmt in ast.iter_child_nodes(tree):
        if isinstance(stmt, TRY_TYPES):
            initial_flags[id(stmt)] = set(false_flags)
        _none_names, false_flags = _path_none_false(
            [stmt], false_flags=false_flags)
    return initial_flags
def _try_inherited_false_flags(try_node, flag_names_in_try: set,
                               initial_false_flags: set) -> set:
    if not try_node.body:
        return set()
    assigned = _const_assign(try_node.body[-1])
    if assigned is None or assigned[1] is not True:
        return set()
    terminal_true_names, _value = assigned
    candidates = (flag_names_in_try & initial_false_flags
                  & terminal_true_names)
    prefix = try_node.body[:-1]
    return {name for name in candidates
            if _statements_preserve_false(prefix, name)}
def _flag_correlation_for(try_node, per_handler: list,
                          flag_names_in_try: set, name: str,
                          initial_false_flags: set | None = None) -> set:
    end_line = try_node.end_lineno or try_node.lineno
    inherited_false = _try_inherited_false_flags(
        try_node, flag_names_in_try, initial_false_flags or set())
    correlated = set(flag_names_in_try)
    normal_stmts = try_node.body + try_node.orelse
    _normal_none, normal_false = _path_none_false(normal_stmts)
    if try_node.finalbody:
        _normal_none, normal_false = _path_none_false(
            try_node.finalbody, _normal_none, normal_false)
        normal_stmts = normal_stmts + try_node.finalbody
    if not _body_early_exits(try_node.body):
        safe_normal = set()
        if _path_final_none_state(normal_stmts, name, end_line) is False:
            safe_normal = set(flag_names_in_try)
        else:
            safe_normal = flag_names_in_try & normal_false
        correlated &= safe_normal
    for handler, (none_set, false_set) in zip(
            try_node.handlers, per_handler, strict=True):
        if _body_early_exits(handler.body):
            continue
        false_set = false_set | inherited_false
        handler_stmts = handler.body
        if try_node.finalbody:
            _final_none, false_set = _path_none_false(
                try_node.finalbody, none_set, false_set)
            handler_stmts = handler_stmts + try_node.finalbody
        safe_here = flag_names_in_try & false_set
        if _path_final_none_state(
                handler_stmts, name, end_line) is False:
            safe_here |= flag_names_in_try
        correlated &= safe_here
    return correlated
def _flag_none_correlations(tree: ast.AST) -> dict:
    correlations: dict[str, list[tuple[tuple[int, int], set[str]]]] = {}
    initial_false_flags = _top_level_try_false_flags(tree)
    for node in _iter_module_level_trys(tree):
        flag_names_in_try = _try_true_flag_names(node)
        per_handler = [_path_none_false(h.body) for h in node.handlers]
        all_none_names = {name for none_set, _false_set in per_handler
                          for name in none_set}
        try_end = (node.end_lineno or node.lineno,
                   getattr(node, 'end_col_offset', 0) or 0)
        for name in all_none_names:
            correlated = _flag_correlation_for(
                node, per_handler, flag_names_in_try, name,
                initial_false_flags.get(id(node)))
            correlations.setdefault(name, []).append(
                (try_end, set(correlated)))
    return correlations
def _pos_flag_hits(test: ast.AST, all_flag_names: set) -> set:
    pos: set = set()
    name = _flag_name(test, all_flag_names)
    if name is not None:
        pos.add(name)
        return pos
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
        for value in test.values:
            name = _flag_name(value, all_flag_names)
            if name is not None:
                pos.add(name)
    return pos
def _flag_name(node: ast.AST, all_flag_names: set) -> str | None:
    if isinstance(node, ast.Name) and node.id in all_flag_names:
        return node.id
    return None
def _flag_matched_names(hit_flags: set, none_to_flags: dict,
                        test: ast.AST) -> list:
    invalidated = _guard_invalidating_walrus_names(test)
    return [name for name, flags in none_to_flags.items()
            if flags & hit_flags and name not in invalidated]
def _flag_guard_ifexp(regions: dict, node: ast.IfExp,
                      all_flag_names: set, none_to_flags: dict) -> None:
    for name in _flag_matched_names(
            _pos_flag_hits(node.test, all_flag_names), none_to_flags, node.test):
        _protect_expression_before_none_rebind(regions, name, node.body)
    for name in _flag_matched_names(
            _collect_not_names(node.test, all_flag_names),
            none_to_flags, node.test):
        _protect_expression_before_none_rebind(regions, name, node.orelse)
def _flag_guard_if(regions: dict, node: ast.If, parent_map: dict,
                   all_flag_names: set, none_to_flags: dict) -> None:
    test = node.test
    for name in _flag_matched_names(
            _pos_flag_hits(test, all_flag_names), none_to_flags, test):
        _protect_ids(regions, name, _guarded_stmts(
            node.body, name, guarded_start=True))
    neg_flags = _collect_not_names(test, all_flag_names)
    for name in _flag_matched_names(neg_flags, none_to_flags, test):
        _protect_ids(regions, name, _guarded_stmts(
            node.orelse, name, guarded_start=True))
        if (_body_early_exits(node.body)
                and _if_fallthrough_guarded(
                    node, name, body_guarded=False, else_guarded=True)):
            _protect_ids(regions, name, _guarded_stmts(
                _statements_after(parent_map, node), name,
                guarded_start=True))
def _flag_guard_while(regions: dict, node: ast.While,
                      all_flag_names: set, none_to_flags: dict) -> None:
    for name in _flag_matched_names(
            _pos_flag_hits(node.test, all_flag_names), none_to_flags, node.test):
        _protect_ids(regions, name, _guarded_stmts(
            node.body, name, guarded_start=True))
def _is_module_scope_guard(node: ast.AST, parent_map: dict) -> bool:
    current = node
    while current in parent_map:
        current = parent_map[current]
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            return False
    return True
def _module_flag_bindings(tree: ast.AST, parent_map: dict) -> dict:
    bindings = _scope_all_bindings(tree)
    for node in walk_nodes(tree):
        if not _is_module_scope_guard(node, parent_map):
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            names = {node.name}
        elif isinstance(node, ast.Delete):
            names = set()
            for target in node.targets:
                assign_target_names(target, names)
        else:
            continue
        for name in names:
            bindings.setdefault(name, []).append(_BindingRecord(
                value=None, order=_source_order(node), may_be_none=True))
    return bindings

def _current_flag_correlations(correlations: dict, bindings: dict,
                               guard: ast.AST) -> dict:
    guard_order = _source_order(guard)
    current: dict[str, set[str]] = {}
    for name, events in correlations.items():
        prior = [(end, flags) for end, flags in events if end < guard_order]
        if not prior:
            continue
        latest_end = max(end for end, _flags in prior)
        flags = set(prior[0][1])
        for _end, event_flags in prior[1:]:
            flags &= event_flags
        for flag in tuple(flags):
            if any(latest_end < record.order < guard_order
                   for record in bindings.get(flag, ())):
                flags.discard(flag)
        if flags:
            current[name] = flags
    return current

def collect_flag_guarded_regions(tree: ast.AST, parent_map: dict) -> dict:
    regions: dict[str, set[int]] = {}
    correlations = _flag_none_correlations(tree)
    if not correlations:
        return regions
    bindings = _module_flag_bindings(tree, parent_map)
    for node in walk_nodes(tree):
        if not _is_module_scope_guard(node, parent_map):
            continue
        none_to_flags = _current_flag_correlations(
            correlations, bindings, node)
        all_flag_names = {flag for flags in none_to_flags.values()
                          for flag in flags}
        if not all_flag_names:
            continue
        if isinstance(node, ast.IfExp):
            _flag_guard_ifexp(regions, node, all_flag_names, none_to_flags)
        elif isinstance(node, ast.If):
            _flag_guard_if(regions, node, parent_map,
                           all_flag_names, none_to_flags)
        elif isinstance(node, ast.While):
            _flag_guard_while(regions, node, all_flag_names, none_to_flags)
    return regions
_SCOPE_BOUNDARIES = (ast.FunctionDef, ast.AsyncFunctionDef,
                     ast.ClassDef, ast.Lambda, ast.Module)
_PLATFORM_LOCKED_MODULES = {
    'msvcrt': 'win32', 'winreg': 'win32', 'winsound': 'win32',
    '_winapi': 'win32', 'nt': 'win32',
    'fcntl': 'posix', 'termios': 'posix', 'tty': 'posix', 'pty': 'posix',
    'grp': 'posix', 'pwd': 'posix', 'spwd': 'posix', 'crypt': 'posix',
    'syslog': 'posix', 'resource': 'posix', 'ossaudiodev': 'posix',
}
def collect_platform_aliases(tree: ast.AST) -> dict:
    aliases: dict = {}
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                cat = _PLATFORM_LOCKED_MODULES.get(alias.name.split('.')[0])
                if cat:
                    aliases[alias.asname or alias.name.split('.')[0]] = cat
            continue
        if not isinstance(node, ast.ImportFrom) or node.level:
            continue
        cat = _PLATFORM_LOCKED_MODULES.get((node.module or '').split('.')[0])
        if not cat:
            continue
        for alias in node.names:
            if alias.name != '*':
                aliases[alias.asname or alias.name] = cat
    return aliases
_SYS_ALIASES_DEFAULT: frozenset[str] = frozenset({"sys"})
def collect_sys_aliases(tree: ast.AST) -> frozenset[str]:
    aliases = set(_SYS_ALIASES_DEFAULT)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            if alias.name.split('.')[0] == 'sys':
                aliases.add(alias.asname or 'sys')
    return frozenset(aliases)
def _is_sys_platform(node: ast.AST, attr: str,
                     sys_aliases: frozenset[str]) -> bool:
    return (isinstance(node, ast.Attribute)
            and node.attr == attr
            and isinstance(node.value, ast.Name)
            and node.value.id in sys_aliases)
def _compare_const_str(test: ast.AST, ops: tuple):
    parsed = _single_compare(test, ops)
    if parsed is None:
        return None
    left, op, comparator = parsed
    if isinstance(comparator, ast.Constant) and isinstance(comparator.value, str):
        return left, op, comparator.value
    if isinstance(left, ast.Constant) and isinstance(left.value, str):
        return comparator, op, left.value
    return None
def _platform_startswith_effect(
        test: ast.AST, sys_aliases: frozenset[str]):
    if not (isinstance(test, ast.Call)
            and isinstance(test.func, ast.Attribute)
            and test.func.attr == 'startswith'
            and _is_sys_platform(test.func.value, 'platform', sys_aliases)
            and len(test.args) == 1
            and isinstance(test.args[0], ast.Constant)
            and isinstance(test.args[0].value, str)):
        return None
    return (1, test.args[0].value)
def _platform_test_effect(test: ast.AST,
                          sys_aliases: frozenset[str]):
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        effect = _platform_test_effect(test.operand, sys_aliases)
        if effect is not None:
            return -effect[0], effect[1]
        return None
    eq_shape = _compare_const_str(test, (ast.Eq, ast.NotEq))
    if (eq_shape is not None
            and _is_sys_platform(eq_shape[0], 'platform', sys_aliases)):
        pol = 1 if isinstance(eq_shape[1], ast.Eq) else -1
        return (pol, eq_shape[2])
    return _platform_startswith_effect(test, sys_aliases)
def _if_branch_sign(parent: ast.If, cur: ast.AST) -> int | None:
    if cur in parent.body:
        return 1
    if cur in parent.orelse:
        return -1
    return None
def _platform_else_verdict(cat: str, negs: list) -> bool:
    return cat == 'posix' and bool(negs) and all(
        p.startswith('win') for p in negs)
def platform_dispatched(node: ast.AST, called_name: str,
                         parent_map: dict, platform_aliases: dict,
                         sys_aliases: frozenset[str], *,
                         stop_at_deferred: bool = False) -> bool:
    cat = platform_aliases.get(called_name)
    if not cat:
        return False
    return _platform_branch_verdict(
        node, parent_map, cat, sys_aliases,
        stop_at_deferred=stop_at_deferred)
def _platform_if_constraint(parent: ast.If, cur: ast.AST,
                            sys_aliases: frozenset[str]):
    branch_sign = _if_branch_sign(parent, cur)
    if branch_sign is None:
        return None
    effect = _platform_test_effect(parent.test, sys_aliases)
    if effect is None:
        return None
    return effect[0] * branch_sign, effect[1]
def _platform_pos_verdict(cat: str, plat: str) -> bool:
    want_win = plat.startswith('win')
    return want_win if cat == 'win32' else not want_win
def _is_elif_continuation(parent: ast.If, cur: ast.AST) -> bool:
    return (len(parent.orelse) == 1 and parent.orelse[0] is cur
            and isinstance(cur, ast.If))
def _platform_branch_verdict(node: ast.AST, parent_map: dict, cat: str,
                             sys_aliases: frozenset[str], *,
                             stop_at_deferred: bool = False) -> bool:
    negs: list = []
    cur = node
    while cur in parent_map:
        parent = parent_map[cur]
        if (stop_at_deferred and isinstance(parent, ast.GeneratorExp)
                and _generator_defers_node(node, parent, parent_map)):
            return False
        if isinstance(parent, _SCOPE_BOUNDARIES):
            return False
        if not isinstance(parent, ast.If):
            cur = parent
            continue
        constraint = _platform_if_constraint(parent, cur, sys_aliases)
        if constraint is None:
            cur = parent
            continue
        sign, plat = constraint
        if sign > 0:
            return _platform_pos_verdict(cat, plat)
        negs.append(plat)
        if not _is_elif_continuation(parent, cur):
            return _platform_else_verdict(cat, negs)
        cur = parent
    return False
def _source_order(node: ast.AST) -> tuple[int, int]:
    return (getattr(node, 'lineno', 0), getattr(node, 'col_offset', 0))
@dataclass(frozen=True)
class _BindingRecord:
    value: ast.AST | None
    order: tuple[int, int]
    may_be_none: bool
@dataclass(frozen=True)
class _DerivedNoneFlag:
    called_name: str
    polarity: str
    dependency_orders: tuple[tuple[int, int], ...]
    binding_count: int
    order: tuple[int, int]
    def is_current(self, node: ast.AST) -> bool:
        order = _source_order(node)
        if order < self.order:
            return False
        current_count = sum(
            candidate <= order for candidate in self.dependency_orders)
        return current_count == self.binding_count
def _scope_all_bindings(scope: ast.AST) -> dict:
    binds: dict = {}
    todo = list(ast.iter_child_nodes(scope))
    while todo:
        cur = todo.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef, ast.Lambda)):
            continue
        todo.extend(ast.iter_child_nodes(cur))
        _record_binding(binds, cur)
    return binds
def _record_binding_target(binds: dict, target: ast.AST,
                           value: ast.AST | None, owner: ast.AST, *,
                           unpacked: bool = False) -> None:
    if isinstance(target, ast.Name):
        if value is None:
            state = None
        else:
            state = _target_binding_states(
                target, value, unpacked=unpacked).get(target.id)
        record = _BindingRecord(
            value=value,
            order=_source_order(owner),
            may_be_none=state is not True,
        )
        binds.setdefault(target.id, []).append(record)
        return
    if isinstance(target, (ast.Tuple, ast.List)):
        values = (list(value.elts) if _is_pairable_unpack(target, value)
                  else [None] * len(target.elts))
        for element, element_value in zip(target.elts, values, strict=True):
            _record_binding_target(
                binds, element, element_value, owner, unpacked=True)
        return
    if isinstance(target, ast.Starred):
        _record_binding_target(binds, target.value, None, owner, unpacked=True)
def _record_binding(binds: dict, cur: ast.AST) -> None:
    if isinstance(cur, ast.Assign):
        for target in cur.targets:
            _record_binding_target(binds, target, cur.value, cur)
        return
    if isinstance(cur, ast.AnnAssign):
        if cur.value is not None:
            _record_binding_target(binds, cur.target, cur.value, cur)
        return
    if isinstance(cur, ast.AugAssign):
        _record_binding_target(binds, cur.target, None, cur)
        return
    if isinstance(cur, ast.NamedExpr):
        _record_binding_target(binds, cur.target, cur.value, cur)
        return
    extract_targets = _TARGET_BINDING_EXTRACTORS.get(type(cur))
    if extract_targets is not None:
        for target in extract_targets(cur):
            _record_binding_target(binds, target, None, cur)
        return
    extract_captures = _CAPTURE_BINDING_EXTRACTORS.get(type(cur))
    if extract_captures is not None:
        for name in extract_captures(cur):
            record = _BindingRecord(
                value=None,
                order=_source_order(cur),
                may_be_none=not isinstance(cur, (
                    ast.Import, ast.ImportFrom, ast.ExceptHandler,
                    ast.MatchMapping, ast.MatchStar)),
            )
            binds.setdefault(name, []).append(record)
def _derived_scope_flags(binds: dict) -> dict:
    scope_flags: dict = {}
    for flag, records in binds.items():
        if len(records) != 1:
            continue
        flag_record = records[0]
        projection = _none_compare_projection(flag_record.value)
        if projection is None:
            continue
        called_name, polarity = projection
        dependency_orders = tuple(sorted(
            record.order for record in binds.get(called_name, ())))
        binding_count = sum(
            order <= flag_record.order for order in dependency_orders)
        scope_flags[flag] = _DerivedNoneFlag(
            called_name=called_name,
            polarity=polarity,
            dependency_orders=dependency_orders,
            binding_count=binding_count,
            order=flag_record.order,
        )
    return scope_flags
def collect_derived_none_flags(tree: ast.AST) -> dict:
    return {id(scope): _derived_scope_flags(_scope_all_bindings(scope))
            for scope in _scope_containers(tree)}
def _scope_containers(tree: ast.AST) -> list:
    return [tree, *[n for n in walk_nodes(tree)
                    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                                      ast.ClassDef))]]
def _shunt_test_branch(parent: ast.AST, cur: ast.AST):
    if isinstance(parent, ast.IfExp):
        return parent.test, (1 if cur is parent.body else -1)
    if isinstance(parent, ast.If):
        return parent.test, _if_branch_sign(parent, cur)
    return None, None
def _name_test_polarity(test: ast.AST):
    if isinstance(test, ast.Name):
        return test.id, 1
    if (isinstance(test, ast.UnaryOp)
            and isinstance(test.op, ast.Not)
            and isinstance(test.operand, ast.Name)):
        return test.operand.id, -1
    return None, 0
def _nearest_scope_container(node: ast.AST, tree: ast.AST,
                             parent_map: dict) -> ast.AST:
    scope = node
    while scope in parent_map and not isinstance(
            scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                    ast.ClassDef)):
        scope = parent_map[scope]
    return scope if isinstance(
        scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                ast.ClassDef)) else tree
def _shunt_flag_need(parent: ast.AST, cur: ast.AST):
    test, branch = _shunt_test_branch(parent, cur)
    if test is None or branch is None:
        return None, None
    flag_name, test_polarity = _name_test_polarity(test)
    if not (flag_name and test_polarity):
        return None, None
    return flag_name, branch * test_polarity
def _derived_flag_verdict(entry: _DerivedNoneFlag | None,
                          called_name: str, need_sign: int,
                          node: ast.AST) -> bool | None:
    if entry is None or entry.called_name != called_name:
        return None
    if not entry.is_current(node):
        return False
    need = 'not_none' if need_sign > 0 else 'is_none'
    return entry.polarity == need
def _derived_early_exit_verdict(
        parent: ast.AST, child: ast.AST, node: ast.AST, called_name: str,
        tree: ast.AST, parent_map: dict, derived_flags: dict) -> bool | None:
    prior = _prior_statement_block(parent, child) or []
    for statement in prior:
        if not (isinstance(statement, ast.If)
                and _body_early_exits(statement.body)):
            continue
        flag_name, test_polarity = _name_test_polarity(statement.test)
        if not (flag_name and test_polarity):
            continue
        scope = _nearest_scope_container(statement, tree, parent_map)
        entry = derived_flags.get(id(scope), {}).get(flag_name)
        verdict = _derived_flag_verdict(
            entry, called_name, -test_polarity, node)
        if verdict is not None:
            return verdict
    return None
def derived_flag_exempt(node: ast.AST, called_name: str,
                         tree: ast.AST, parent_map: dict,
                         derived_flags: dict, *,
                         stop_at_deferred: bool = False) -> bool:
    cur = node
    while cur in parent_map:
        parent = parent_map[cur]
        if (stop_at_deferred and isinstance(parent, ast.GeneratorExp)
                and _generator_defers_node(node, parent, parent_map)):
            return False
        flag_name, need_sign = _shunt_flag_need(parent, cur)
        if flag_name is None:
            verdict = _derived_early_exit_verdict(
                parent, cur, node, called_name, tree, parent_map,
                derived_flags)
            if verdict is not None:
                return verdict
            if isinstance(parent, _SCOPE_BOUNDARIES):
                return False
            cur = parent
            continue
        scope = _nearest_scope_container(parent, tree, parent_map)
        entry = derived_flags.get(id(scope), {}).get(flag_name)
        verdict = _derived_flag_verdict(
            entry, called_name, need_sign, node)
        if verdict is not None:
            return verdict
        cur = parent
    return False
def iter_enclosing_trys(target_node: ast.AST, tree: ast.AST,
                         parent_map: dict | None = None):
    if parent_map is None:
        parent_map = shared_parent_map(tree)
    node = target_node
    while node in parent_map:
        parent = parent_map[node]
        if (isinstance(parent, ast.GeneratorExp)
                and _generator_defers_node(target_node, parent, parent_map)):
            return
        action, step = _enclosing_try_step(parent, node)
        if action == 'stop':
            return
        if action == 'try':
            yield step
        node = step
def _enclosing_try_step(parent: ast.AST, node: ast.AST):
    if isinstance(parent, ast.ExceptHandler):
        return 'skip', parent
    if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return ('stop', None) if node in parent.body else ('skip', parent)
    if isinstance(parent, ast.Lambda):
        return ('stop', None) if node is parent.body else ('skip', parent)
    if isinstance(parent, TRY_TYPES):
        return ('try', parent) if node in parent.body else ('skip', parent)
    return 'skip', parent
def called_exc_name(func: ast.expr) -> str:
    if isinstance(func, ast.Attribute):
        return "AttributeError"
    return "TypeError"
def _handler_type_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id
    if (isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id == 'builtins'):
        return node.attr
    return None
def _handler_type_names(handler: ast.ExceptHandler) -> set[str] | None:
    if handler.type is None:
        return None
    if isinstance(handler.type, ast.Tuple):
        return {name for element in handler.type.elts
                if (name := _handler_type_name(element)) is not None}
    name = _handler_type_name(handler.type)
    return {name} if name is not None else set()
def try_catches_exception(try_node: ast.Try | ast.TryStar,
                           exc_name: str) -> bool:
    caught = {exc_name, 'Exception', 'BaseException'}
    for handler in try_node.handlers:
        names = _handler_type_names(handler)
        if names is None or names & caught:
            return True
    return False
def _parse_source(filepath: str, detector_id: str
                  ) -> tuple[str, ast.AST] | None:
    source, tree = parse_py_file(filepath, quiet=True)
    if tree is None:
        logger.warning("[AuditPatterns] %s 源文件解析失败，检测跳过: %s",
                       detector_id, filepath)
        return None
    return source, tree
def _log_detected(detector_id: str, pattern_name: str, count: int,
                  filepath: str) -> None:
    logger.info("[AuditPatterns] %s 检出 %d 处 %s: %s",
                detector_id, count, pattern_name, filepath)
def _resolve_called_root_name(func: ast.expr) -> str | None:
    _root = func
    while isinstance(_root, (ast.Attribute, ast.Subscript)):
        _root = _root.value
    return _root.id if isinstance(_root, ast.Name) else None
@dataclass(frozen=True)
class _D52ScanContext:
    tree: ast.AST
    parent_map: dict
    protected_regions: dict[str, set[int]]
    flag_regions: dict[str, set[int]]
    scope_cache: dict
    platform_aliases: dict
    sys_aliases: frozenset[str]
    derived_flags: dict
    scope_bindings: dict[int, dict]
    none_assigns: dict[str, int]
    vulnerable_names: dict[str, int]
    module_events: dict[str, list[tuple[int, bool]]]
    lines: list[str]
    filepath: str
@dataclass(frozen=True)
class _D52CallSite:
    node: ast.Call
    name: str
    exc_name: str
    enclosing_trys: tuple
def _d52_call_site(node: ast.Call, ctx: _D52ScanContext) -> _D52CallSite | None:
    called_name = _resolve_called_root_name(node.func)
    if (called_name not in ctx.vulnerable_names
            and not _historical_none_eager_call(node, called_name, ctx)):
        return None
    return _D52CallSite(
        node=node,
        name=called_name,
        exc_name=called_exc_name(node.func),
        enclosing_trys=tuple(iter_enclosing_trys(
            node, ctx.tree, ctx.parent_map)),
    )
def _is_module_eager_context(node: ast.AST, parent_map: dict) -> bool:
    child = node
    anc = parent_map.get(node)
    while anc is not None:
        if (isinstance(anc, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
                and not _is_def_time_context(anc, child)):
            return False
        if (isinstance(anc, ast.GeneratorExp)
                and not (anc.generators and child is anc.generators[0]
                         and _path_via_iter(node, child, parent_map))):
            return False
        child, anc = anc, parent_map.get(anc)
    return True
def _top_level_statement(node: ast.AST, tree: ast.AST,
                         parent_map: dict) -> ast.AST | None:
    current = node
    while current in parent_map:
        parent = parent_map[current]
        if parent is tree:
            return current
        current = parent
    return None
def _module_none_state_before_call(node: ast.AST, name: str,
                                   ctx: _D52ScanContext) -> bool | None:
    if not _is_module_eager_context(node, ctx.parent_map):
        return None
    local_verdict = _local_rebind_verdict(node, name, ctx)
    if local_verdict is not None:
        return not local_verdict
    statement = _top_level_statement(node, ctx.tree, ctx.parent_map)
    if statement is None:
        return None
    cutoff = getattr(statement, 'lineno', node.lineno) - 1
    return _latest_none_state(ctx.module_events.get(name), cutoff)
def _historical_none_eager_call(node: ast.AST, name: str,
                                ctx: _D52ScanContext) -> bool:
    if name not in ctx.none_assigns:
        return False
    return _module_none_state_before_call(node, name, ctx) is True
def _module_rebinding_exempt(node: ast.AST, name: str,
                             ctx: _D52ScanContext) -> bool:
    if not ctx.module_events.get(name):
        return False
    return _module_none_state_before_call(node, name, ctx) is False
def _record_definite_faces(stmts: list, events: dict) -> None:
    for stmt in _iter_definite_binding_stmts(stmts):
        _record_binding_faces(
            stmt, *_stmt_binding_faces(stmt), events, set(), {},
            record_all_recoveries=True)
def _try_handler_binding_events(stmts: list) -> dict[str, list[tuple[int, bool]]]:
    events: dict[str, list[tuple[int, bool]]] = {}
    stack = list(stmts)
    while stack:
        stmt = stack.pop()
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(stmt, TRY_TYPES):
            path_events: dict[str, list[tuple[int, bool]]] = {}
            _record_definite_faces(stmt.body + stmt.orelse, path_events)
            for handler in stmt.handlers:
                _record_definite_faces(handler.body, path_events)
            end_line = stmt.end_lineno or stmt.lineno
            # 候选集除 body/orelse/handler 的确定绑定外，还需覆盖仅在 finalbody
            # （或其条件分支）里绑定、try 体内不出现的名字。
            candidates = path_events.keys() | _scope_all_bindings(stmt).keys()
            for name in candidates:
                is_none = _try_terminal_none_state(stmt, name)
                if is_none is None:
                    continue
                events.setdefault(name, []).append((end_line, is_none))
        stack.extend(ast.iter_child_nodes(stmt))
    return events
def _latest_none_state(events: list[tuple[int, bool]] | None,
                       node_lineno: int) -> bool | None:
    if not events:
        return None
    latest_line = -1
    latest_is_none: bool | None = None
    for _line, _is_none in events:
        if latest_line <= _line <= node_lineno:
            latest_line = _line
            latest_is_none = _is_none
    return latest_is_none
def _prior_statement_block(parent: ast.AST, child: ast.AST) -> list | None:
    for field_name in parent._fields:
        group = getattr(parent, field_name, None)
        if not isinstance(group, list):
            continue
        for index, stmt in enumerate(group):
            if stmt is child:
                return group[:index]
    return None
def _path_final_none_state(stmts: list, name: str,
                           lineno: int) -> bool | None:
    events: dict[str, list[tuple[int, bool]]] = {}
    _record_definite_faces(stmts, events)
    return _latest_none_state(events.get(name), lineno)
def _try_any_fallthrough_none(try_node, name: str) -> bool:
    end_line = try_node.end_lineno or try_node.lineno
    if (not _body_early_exits(try_node.body)
            and _path_final_none_state(
                try_node.body + try_node.orelse, name, end_line) is True):
        return True
    return any(
        not _body_early_exits(handler.body)
        and _path_final_none_state(handler.body, name, end_line) is True
        for handler in try_node.handlers
    )
def _try_all_paths_recover(try_node, name: str) -> bool:
    end_line = try_node.end_lineno or try_node.lineno
    if not try_node.handlers:
        return _path_final_none_state(
            try_node.body + try_node.orelse, name, end_line) is False
    if (not _body_early_exits(try_node.body)
            and _path_final_none_state(
                try_node.body + try_node.orelse, name, end_line) is not False):
        return False
    for handler in try_node.handlers:
        if _body_early_exits(handler.body):
            continue
        if _path_final_none_state(
                handler.body, name, end_line) is not False:
            return False
    return True
def _none_literal_bound(node: ast.AST, name: str) -> bool:
    """node 子树（不进入嵌套作用域）内是否存在把 name 赋为 None 字面量的语句。"""
    stack = [node]
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(cur, (ast.Assign, ast.AnnAssign)) and (
                _statement_none_state(cur, name) is True):
            return True
        stack.extend(ast.iter_child_nodes(cur))
    return False
def _try_terminal_none_state(try_node, name: str) -> bool | None:
    """try 语句结束时 name 的终态：False=各离开路径均确定非 None，
    True=至少一条路径为（或可能为）None，None=try 内对 name 无值绑定。

    与 _try_all_paths_recover/_try_any_fallthrough_none 的区别：finalbody 在
    每条离开路径上都会执行，必须优先合流；handler/finalbody 内条件分支中的
    赋值不是确定语句，但会使 name 的终态不确定，须按"可能为 None"保守处理。
    """
    def _path_state(stmts: list) -> bool | None:
        state = _fallthrough_none_state(stmts, name, None)
        if state is not None:
            return state
        if any(_none_literal_bound(stmt, name) for stmt in stmts):
            return True
        return None
    final_state = _path_state(try_node.finalbody)
    if final_state is not None:
        return final_state
    if not try_node.handlers:
        return _path_state(try_node.body + try_node.orelse)
    path_states: list[bool | None] = []
    if not _body_early_exits(try_node.body):
        path_states.append(_path_state(try_node.body + try_node.orelse))
    path_states.extend(
        _path_state(handler.body) for handler in try_node.handlers
        if not _body_early_exits(handler.body))
    if not path_states or all(state is None for state in path_states):
        return None
    if any(state is True for state in path_states):
        return True
    if any(state is None for state in path_states):
        # 存在未触碰 name 的离开路径：异常可能发生在 body 绑定之前，该路径的
        # 终态等于进入 try 前的状态（本函数不可知）。其余路径的 False 不能
        # 代表“确定非 None”（进入前为 None 时漏报），也不能升级为 True
        # （进入前非 None 时误报）；返回 None 让调用方沿用 try 之前的最近
        # 确切状态。
        return None
    return False
_NONE_STATE_UNSET = object()
def _statement_none_state(stmt: ast.AST, name: str):
    if isinstance(stmt, ast.Assign):
        state = _assign_binding_states(stmt).get(name, _NONE_STATE_UNSET)
    elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
        states = _expression_binding_states(stmt.value)
        _update_expression_states(
            states, _target_binding_states(stmt.target, stmt.value))
        state = states.get(name, _NONE_STATE_UNSET)
    else:
        state = _NONE_STATE_UNSET
    if state is not _NONE_STATE_UNSET:
        return None if state is None else not state
    _names, none_names, recover_names = _stmt_binding_faces(stmt)
    if name in recover_names:
        return False
    if name in none_names:
        return None
    if isinstance(stmt, ast.Delete) and _targets_mention(stmt.targets, name):
        return None
    return _NONE_STATE_UNSET
def _fallthrough_none_state(stmts: list, name: str, entry_state):
    state = entry_state
    for stmt in stmts:
        if isinstance(stmt, ast.If):
            stmt_state = _if_fallthrough_none_state(stmt, name, state)
        else:
            stmt_state = _statement_none_state(stmt, name)
        if stmt_state is not _NONE_STATE_UNSET:
            state = stmt_state
    return state
def _if_fallthrough_none_state(node: ast.If, name: str, entry_state):
    body_state = _fallthrough_none_state(node.body, name, entry_state)
    else_state = _fallthrough_none_state(node.orelse, name, entry_state)
    if _body_early_exits(node.body):
        return else_state
    if _body_early_exits(node.orelse):
        return body_state
    if body_state == else_state:
        return body_state
    if body_state is True or else_state is True:
        return True
    return None
def _local_rebind_verdict(node: ast.AST, name: str,
                          ctx: _D52ScanContext) -> bool | None:
    child = node
    parent = ctx.parent_map.get(child)
    while parent is not None:
        prior = _prior_statement_block(parent, child)
        if prior is not None:
            events: dict = {}
            _record_definite_faces(prior, events)
            for stmt in prior:
                if isinstance(stmt, TRY_TYPES):
                    # try 终态必须完整记录（True=为/可能为 None，False=确定非 None）。
                    # 此前只记录 False，使 try 之前 x = int 的 False 残留，把
                    # try 内 x = None、handler 不恢复的调用误判为 local_rebound。
                    # 行号用结束行：终态在 try 全部语句之后才成立。
                    terminal = _try_terminal_none_state(stmt, name)
                    if terminal is not None:
                        events.setdefault(name, []).append(
                            (stmt.end_lineno or stmt.lineno, terminal))
                elif isinstance(stmt, ast.If):
                    entry_state = _latest_none_state(
                        events.get(name), stmt.lineno - 1)
                    state = _if_fallthrough_none_state(
                        stmt, name, entry_state)
                    if state is not None:
                        events.setdefault(name, []).append((
                            stmt.end_lineno or stmt.lineno, state))
            state = _latest_none_state(events.get(name), node.lineno)
            if state is not None:
                return not state
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.Lambda, ast.ClassDef)):
            break
        child, parent = parent, ctx.parent_map.get(parent)
    return None
def _has_later_none_rebind(node: ast.AST, name: str,
                           ctx: _D52ScanContext) -> bool:
    scope = _nearest_scope_container(node, ctx.tree, ctx.parent_map)
    order = _source_order(node)
    for record in ctx.scope_bindings.get(id(scope), {}).get(name, ()):
        if record.order > order and record.may_be_none:
            return True
    return False
def _d52_call_exemption(site: _D52CallSite,
                        ctx: _D52ScanContext) -> str | None:
    node = site.node
    called_name = site.name
    deferred_rebound = (_in_deferred_generator_context(node, ctx.parent_map)
                        and _has_later_none_rebind(node, called_name, ctx))
    local_verdict = _local_rebind_verdict(node, called_name, ctx)
    if local_verdict is True and not deferred_rebound:
        return "local_rebound"
    _region_ids = ctx.protected_regions.get(called_name)
    if _region_ids and in_protected_region(
            node, _region_ids, ctx.parent_map,
            stop_at_deferred=deferred_rebound):
        return "guarded_region"
    _flag_ids = ctx.flag_regions.get(called_name)
    if (local_verdict is not False and _flag_ids
            and in_protected_region(
                node, _flag_ids, ctx.parent_map,
                stop_at_deferred=deferred_rebound)):
        return "flag_guarded_region"
    if local_verdict is None:
        if _is_scope_shadowed(
                node, called_name, ctx.parent_map, ctx.scope_cache):
            return "scope_shadowed"
        if _module_rebinding_exempt(node, called_name, ctx):
            return "module_rebound"
    if (local_verdict is not False and platform_dispatched(
            node, called_name, ctx.parent_map, ctx.platform_aliases,
            ctx.sys_aliases, stop_at_deferred=deferred_rebound)):
        return "platform_dispatched"
    if derived_flag_exempt(
            node, called_name, ctx.tree, ctx.parent_map, ctx.derived_flags,
            stop_at_deferred=deferred_rebound):
        return "derived_flag"
    return ("enclosing_try"
            if any(try_catches_exception(t, site.exc_name)
                   for t in site.enclosing_trys) else None)
def _iter_d52_sites(ctx: _D52ScanContext):
    for node in walk_nodes(ctx.tree):
        if not isinstance(node, ast.Call):
            continue
        site = _d52_call_site(node, ctx)
        if site is None or _d52_call_exemption(site, ctx):
            continue
        yield site
def _build_d52_scan_context(tree: ast.AST, source: str,
                            filepath: str) -> _D52ScanContext | None:
    none_assigns = _collect_none_assigns(tree)
    if not none_assigns:
        return None
    defined_names = _collect_defined_names(tree)
    vulnerable_names = {
        name: line for name, line in none_assigns.items()
        if name not in defined_names
    }
    parent_map = shared_parent_map(tree)
    protected_regions = collect_guarded_regions(tree, parent_map)
    flag_regions = collect_flag_guarded_regions(tree, parent_map)
    module_events, _ = _scan_top_level_bindings(
        list(ast.iter_child_nodes(tree)), terminal_only=False)
    for name, h_events in _try_handler_binding_events(
            list(ast.iter_child_nodes(tree))).items():
        module_events.setdefault(name, []).extend(h_events)
    for name, line in none_assigns.items():
        events = module_events.setdefault(name, [])
        if not any(event_line == line and is_none
                   for event_line, is_none in events):
            events.append((line, True))
        events.sort(key=lambda event: event[0])
    scope_bindings = {id(scope): _scope_all_bindings(scope)
                      for scope in _scope_containers(tree)}
    derived_flags = {scope_id: _derived_scope_flags(bindings)
                     for scope_id, bindings in scope_bindings.items()}
    return _D52ScanContext(
        tree=tree,
        parent_map=parent_map,
        protected_regions=protected_regions,
        flag_regions=flag_regions,
        scope_cache={},
        platform_aliases=collect_platform_aliases(tree),
        sys_aliases=collect_sys_aliases(tree),
        derived_flags=derived_flags,
        scope_bindings=scope_bindings,
        none_assigns=none_assigns,
        vulnerable_names=vulnerable_names,
        module_events=module_events,
        lines=source.split("\n"),
        filepath=filepath,
    )
class NoneFallbackCallableDetector:
    DETECTOR_ID = "D52"
    PATTERN_NAME = "None-fallback name used as callable"
    def _make_d52_finding(self, site: _D52CallSite,
                          ctx: _D52ScanContext) -> PatternFinding:
        where = (f"{site.name} = None "
                 f"(L{ctx.none_assigns[site.name]}) ")
        if not site.enclosing_trys:
            severity = "ERROR"
            message = (where + f"called without guard, {site.exc_name} "
                       "when dependency unavailable")
        else:
            severity = "WARN"
            message = (where + "called in try blocks whose except clauses "
                       f"don't catch {site.exc_name} at any enclosing "
                       f"level, {site.exc_name} escapes")
        source_line = safe_source_line(ctx.lines, site.node.lineno)
        return PatternFinding(
            detector_id=self.DETECTOR_ID,
            pattern_name=self.PATTERN_NAME,
            severity=severity,
            filepath=ctx.filepath,
            line=site.node.lineno,
            snippet=source_line[:120],
            message=message,
            suggestion=suggest(_QUALITY_ROOT_CAUSE,
                f"Provide a callable fallback class for {site.name}, "
                f"or add `if {site.name} is not None:` guard, "
                f"or extend except to catch {site.exc_name}"),
        )
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        parsed = _parse_source(filepath, self.DETECTOR_ID)
        if parsed is None:
            return []
        source, tree = parsed
        ctx = _build_d52_scan_context(tree, source, filepath)
        if ctx is None:
            return []
        findings = [self._make_d52_finding(site, ctx)
                    for site in _iter_d52_sites(ctx)]
        if findings:
            _log_detected(self.DETECTOR_ID, self.PATTERN_NAME,
                          len(findings), filepath)
        return findings
class FallbackReturnsNoneDetector:
    DETECTOR_ID = "D55"
    PATTERN_NAME = "空壳降级方法返回 None"
    _FALLBACK_NAME_SEGMENTS = frozenset({
        'fallback', 'stub', 'placeholder', 'dummy', 'mock', 'fake', 'empty',
        'noop',
    })
    _FALLBACK_DOC_RE = re.compile(
        r"\b(?:fallback|stub|no[_ -]?op|placeholder|dummy|mock|fake|empty)\b",
        re.IGNORECASE)
    _FALLBACK_DOC_NEGATION_RE = re.compile(
        r"\b(?:not|no|never|non)[\s-]+(?:an?\s+|the\s+)?(?:real\s+)?"
        r"(?:fallback|stub|placeholder|dummy|mock|fake|empty|no[_ -]?op)"
        r"(?:\s*(?:\bor\b|\bnor\b)\s*(?:an?\s+|the\s+)?(?:real\s+)?"
        r"(?:fallback|stub|placeholder|dummy|mock|fake|empty|no[_ -]?op))*\b",
        re.IGNORECASE)
    _SKIP_METHODS = frozenset({
        '__init__', '__repr__', '__str__', '__del__', '__enter__',
        '__exit__', '__aenter__', '__aexit__', '__post_init__',
        '__setattr__', '__delattr__', '__setitem__', '__delitem__',
        '__set__', '__delete__', '__set_name__', '__setstate__',
        '__init_subclass__',
        '__getattr__',
    })
    _IMPORTANT_METHOD_HINTS = frozenset({
        'check', 'get', 'build', 'create', 'parse', 'analyze',
        'detect', 'validate', 'compute', 'solve', 'evaluate',
        'run', 'execute',
    })
    _NOOP_BODY_STMTS = (ast.Return, ast.Pass) + (
        (ast.TypeAlias,) if hasattr(ast, "TypeAlias") else ())
    _NOOP_EXPR_CONSTANT_TYPES = (str, type(...))
    @classmethod
    def _has_important_hint(cls, method_base: str) -> bool:
        _tokens = {tok for tok in method_base.split('_') if tok}
        return bool(_tokens & cls._IMPORTANT_METHOD_HINTS)
    _SIGNATURE_ONLY_SOURCES: ClassVar[dict[str, frozenset[str]]] = {
        'overload': frozenset({'typing', 'typing_extensions'}),
        'abstractmethod': frozenset({'abc'}),
    }
    @classmethod
    def _signature_only_names(cls, tree: ast.AST) -> frozenset[str]:
        names: set[str] = set()
        for node in walk_nodes(tree):
            if isinstance(node, ast.ImportFrom):
                if node.level:
                    continue
                for alias in node.names:
                    sources = cls._SIGNATURE_ONLY_SOURCES.get(alias.name, ())
                    if node.module not in sources:
                        continue
                    names.add(alias.asname or alias.name)
                if any(node.module in sources
                       for sources in cls._SIGNATURE_ONLY_SOURCES.values()):
                    for alias in node.names:
                        if alias.name == '*':
                            names.update(
                                name for name, sources
                                in cls._SIGNATURE_ONLY_SOURCES.items()
                                if node.module in sources)
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    local_name = alias.asname or alias.name.split('.')[0]
                    for name, sources in cls._SIGNATURE_ONLY_SOURCES.items():
                        if alias.name in sources:
                            names.add(f'{local_name}.{name}')
        return frozenset(names)
    @staticmethod
    def _is_signature_only(
            method_node: ast.FunctionDef | ast.AsyncFunctionDef,
            signature_only_names: frozenset[str]) -> bool:
        return any(
            (isinstance(decorator, ast.Name)
             and decorator.id in signature_only_names)
            or (isinstance(decorator, ast.Attribute)
                and isinstance(decorator.value, ast.Name)
                and f'{decorator.value.id}.{decorator.attr}'
                in signature_only_names)
            for decorator in method_node.decorator_list)
    def _skip_method(self, method_node: ast.FunctionDef | ast.AsyncFunctionDef,
                     signature_only_names: frozenset[str]) -> bool:
        if (method_node.name in self._SKIP_METHODS
                or self._is_signature_only(method_node, signature_only_names)):
            return True
        if (method_node.name.startswith('_')
                and not method_node.name.startswith('__')):
            method_base = method_node.name.lstrip('_').lower()
            return not self._has_important_hint(method_base)
        return False
    def _name_hits_fallback(self, name: str) -> bool:
        segments = split_identifier(name.lstrip('_'))
        if set(segments) & self._FALLBACK_NAME_SEGMENTS:
            return True
        return any(prev == 'no' and cur == 'op'
                   for prev, cur in pairwise(segments))
    def _is_fallback_class(self, node: ast.ClassDef) -> bool:
        if self._name_hits_fallback(node.name):
            return True
        doc = self._FALLBACK_DOC_NEGATION_RE.sub(
            " ", ast.get_docstring(node) or "")
        return bool(self._FALLBACK_DOC_RE.search(doc))
    def _is_placeholder_expr(self, stmt: ast.stmt) -> bool:
        return (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant)
                and isinstance(stmt.value.value, self._NOOP_EXPR_CONSTANT_TYPES))
    def _implicit_none_is_shell(self, body: list[ast.stmt]) -> bool:
        has_pass = any(isinstance(s, ast.Pass) for s in body)
        has_placeholder = any(self._is_placeholder_expr(s) for s in body)
        return has_pass or has_placeholder
    def _is_shell_stmt(self, stmt: ast.stmt) -> bool:
        return (isinstance(stmt, self._NOOP_BODY_STMTS)
                or self._is_placeholder_expr(stmt))
    def _returns_none_only(self, func_node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
        for stmt in func_node.body:
            if not self._is_shell_stmt(stmt):
                return False
        returns = [s for s in func_node.body if isinstance(s, ast.Return)]
        if not returns:
            return self._implicit_none_is_shell(func_node.body)
        return all(self._is_none_return(ret) for ret in returns)
    @staticmethod
    def _is_none_return(ret: ast.Return) -> bool:
        if ret.value is None:
            return True
        return (isinstance(ret.value, ast.Constant)
                and ret.value.value is None)
    def detect_file(self, filepath: str) -> list[PatternFinding]:
        parsed = _parse_source(filepath, self.DETECTOR_ID)
        if parsed is None:
            return []
        source, tree = parsed
        source_lines = source.split("\n")
        signature_only_names = self._signature_only_names(tree)
        findings: list[PatternFinding] = []
        for node in walk_nodes(tree):
            if isinstance(node, ast.ClassDef):
                findings.extend(
                    self._class_findings(
                        node, source_lines, filepath, signature_only_names))
        if findings:
            _log_detected(self.DETECTOR_ID, self.PATTERN_NAME,
                          len(findings), filepath)
        return findings
    def _class_findings(self, node: ast.ClassDef, source_lines: list[str],
                        filepath: str,
                        signature_only_names: frozenset[str]) -> list[PatternFinding]:
        if not self._is_fallback_class(node):
            return []
        findings: list[PatternFinding] = []
        for child in ast.iter_child_nodes(node):
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            if (self._skip_method(child, signature_only_names)
                    or not self._returns_none_only(child)):
                continue
            snippet = safe_source_line(source_lines, child.lineno)[:120]
            findings.append(PatternFinding(
                detector_id=self.DETECTOR_ID,
                pattern_name=self.PATTERN_NAME,
                severity="WARN",
                filepath=filepath,
                line=child.lineno,
                snippet=snippet,
                message=f"Fallback 类 '{node.name}' 的方法 '{child.name}()' 返回 None, 调用方访问属性将触发 AttributeError",
                suggestion=suggest(_QUALITY_ROOT_CAUSE,
                    "返回与真实实现接口一致的结果对象或安全默认值，而非 None")
            ))
        return findings
def wiring_declarations() -> dict:
    return {"catalogs": {
        "audit_detector_classes": {
            'D52': NoneFallbackCallableDetector,
            'D55': FallbackReturnsNoneDetector,
        },
    }}

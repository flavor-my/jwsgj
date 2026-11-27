from __future__ import annotations

import ast
import logging
from collections.abc import Iterator
from dataclasses import dataclass
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    iter_module_stmt_blocks,
    iter_unpack_target_names,
)
from jwsgj.prevention_container_mutation import _binding_dominates_use
from jwsgj.prevention_scope_facts import (
    FUNC_SCOPE_NODES,
    MATCH_MAPPING_TYPE,
    PATTERN_BIND_NODES,
    TRY_NODES,
    assigned_names,
    block_exits,
    block_never_falls_through,
    break_binding_loop,
    capture_binding_names,
    construct_shadows_name,
    int_literal,
    is_constant_true_while,
    is_statically_unreachable,
    iter_nodes_outside,
    loop_has_binding,
    make_issue,
    nearest_scope,
    param_names,
    parent_map_of,
    preceding_statements,
    prior_statements,
    range_len_source,
    scan_body_no_funcs,
    scope_chain,
    scope_definition_names,
    scope_function_defs,
    scope_local_bindings,
    snippet_of,
    source_lines,
    subtree_contains,
    target_binding_names,
    walk_ast_nodes,
    walk_nodes,
)

__all__ = [
    'check_LV06',
    'check_LV07',
    'check_LV11',
    'check_LV30',
    'check_LV31',
]
_log = logging.getLogger(__name__)
_log.info(
    "prevention_flow_loop_checks 循环迭代域"
    "（循环终止/下标边界/迭代空转）已加载：%d 项导出", len(__all__))
_FINDING_DIMENSION = 'logic_correctness'
_TYPE_ALIAS_T = getattr(ast, 'TypeAlias', None)
_Lv07DefEntry = tuple[ast.AST, set[str], set[str]]
_Lv07DefTable = dict[str, tuple[_Lv07DefEntry, ...]]
_LV07_DECL_NODES = {'global': ast.Global, 'nonlocal': ast.Nonlocal}
_LV07_PURE_BUILTINS = frozenset({
    'len', 'bool', 'repr', 'abs', 'any', 'all', 'min', 'max', 'sum',
    'str', 'int', 'float', 'complex', 'tuple', 'list', 'dict', 'set',
    'frozenset', 'sorted', 'reversed', 'enumerate', 'zip', 'map',
    'filter', 'isinstance', 'issubclass', 'hasattr', 'print', 'id',
    'type', 'dir', 'vars', 'format', 'round', 'divmod', 'pow',
})
_LV07_EAGER_KEY_BUILTINS = frozenset({'min', 'max', 'sorted'})
_LV07_LAZY_CALLBACK_BUILTINS = frozenset({'filter', 'map'})
_LV07_EAGER_ITERATOR_CONSUMERS = frozenset({
    'all', 'any', 'dict', 'frozenset', 'list', 'max', 'min', 'set',
    'sorted', 'sum', 'tuple',
})
_LV07_CALLBACK_BUILTINS = (
    _LV07_EAGER_KEY_BUILTINS | _LV07_LAZY_CALLBACK_BUILTINS
    | _LV07_EAGER_ITERATOR_CONSUMERS)
# 构造调用 C() 会执行的入口方法；按类名匹配（不是属性调用）。
_LV07_CTOR_NAMES = frozenset({'__init__', '__new__'})
_LV06_COMPARE_FLIP: dict[type, type] = {
    ast.Lt: ast.Gt, ast.Gt: ast.Lt,
    ast.LtE: ast.GtE, ast.GtE: ast.LtE,
}
_LV06_COMPARE_NEGATE: dict[type, type] = {
    ast.Lt: ast.GtE, ast.GtE: ast.Lt,
    ast.LtE: ast.Gt, ast.Gt: ast.LtE,
}
_LV06_BRANCH_GUARD_NODES = (ast.If, ast.While)
_LV06_BUILTIN_NAMES = frozenset({'range', 'len'})
_LV06_LENGTH_REDUCING_METHODS = frozenset({
    'clear', 'pop', 'popitem', 'remove',
})
def _lv07_mutation_bases(node: ast.AST | None, out: set[str]) -> None:
    if node is None:
        return
    for n in walk_nodes(node):
        if (isinstance(n, (ast.Attribute, ast.Subscript))
                and isinstance(n.ctx, (ast.Store, ast.Del))):
            base = n.value
            while isinstance(base, (ast.Attribute, ast.Subscript)):
                base = base.value
            if isinstance(base, ast.Name):
                out.add(base.id)
def _lv07_is_pure_annotation(stmt: ast.AST) -> bool:
    return isinstance(stmt, ast.AnnAssign) and stmt.value is None
def _lv07_is_pattern_bind_node(node: ast.AST) -> bool:
    return (isinstance(node, PATTERN_BIND_NODES)
            or (MATCH_MAPPING_TYPE is not None
                and isinstance(node, MATCH_MAPPING_TYPE)))
def _lv07_assign_targets(sub: ast.AST) -> list[ast.AST]:
    if _lv07_is_pure_annotation(sub):
        return []
    if isinstance(sub, ast.Assign):
        return list(sub.targets)
    return [sub.target]
def _lv07_target_list(node: ast.AST) -> list[ast.AST] | None:
    if isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
        return _lv07_assign_targets(node)
    if isinstance(node, (ast.NamedExpr, ast.For, ast.AsyncFor)):
        return [node.target]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [item.optional_vars for item in node.items
                if item.optional_vars is not None]
    if isinstance(node, ast.Delete):
        return list(node.targets)
    if _TYPE_ALIAS_T is not None and isinstance(node, _TYPE_ALIAS_T):
        return [node.name]
    return None
def _lv07_is_pure_builtin_call(
        node: ast.AST, pure_builtins: frozenset[str]) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in pure_builtins)
def _lv07_prune_pure_args(
        call_node: ast.Call, pure_builtins: frozenset[str]):
    operands = [*call_node.args, *(kw.value for kw in call_node.keywords)]
    for arg in operands:
        inner = arg.value if isinstance(arg, ast.Starred) else arg
        if isinstance(inner, (ast.Name, ast.Constant)):
            continue
        if _lv07_is_pure_builtin_call(inner, pure_builtins):
            yield from _lv07_prune_pure_args(inner, pure_builtins)
            continue
        yield from _lv07_pure_arg_call_signals(arg, pure_builtins)
def _lv07_walk_pruned(
        node: ast.AST, pure_builtins: frozenset[str]):
    for child in ast.iter_child_nodes(node):
        if (isinstance(node, ast.Call) and child is node.func
                and isinstance(child, ast.Name)):
            continue
        if _lv07_is_pure_builtin_call(child, pure_builtins):
            yield from _lv07_prune_pure_args(child, pure_builtins)
            continue
        yield child
        yield from _lv07_walk_pruned(child, pure_builtins)
def _lv07_pure_arg_call_signals(
        node: ast.AST, pure_builtins: frozenset[str]):
    if _lv07_is_pure_builtin_call(node, pure_builtins):
        yield from _lv07_prune_pure_args(node, pure_builtins)
        return
    if isinstance(node, ast.Call):
        yield from _lv07_walk_pruned(node, pure_builtins)
        return
    for child in ast.iter_child_nodes(node):
        yield from _lv07_pure_arg_call_signals(child, pure_builtins)
def _lv07_call_operand_nodes(
        call_node: ast.Call, pure_builtins: frozenset[str]):
    if not isinstance(call_node.func, ast.Name):
        yield from _lv07_walk_pruned(call_node.func, pure_builtins)
    operands = [*call_node.args, *(kw.value for kw in call_node.keywords)]
    for arg in operands:
        if isinstance(arg, ast.Name):
            yield arg
        elif _lv07_is_pure_builtin_call(arg, pure_builtins):
            yield from _lv07_prune_pure_args(arg, pure_builtins)
        else:
            yield from _lv07_walk_pruned(arg, pure_builtins)
def _lv07_extend_children(
        stack: list[ast.AST], node: ast.AST, while_node: ast.While,
        called: set[str] | frozenset[str], *,
        cross_function_scopes: bool) -> None:
    if node is while_node:
        stack.append(node.test)
        stack.extend(node.body)
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        stack.extend(_lv07_func_eval_surfaces(node))
        if cross_function_scopes and node.name in called:
            stack.extend(node.body)
    elif isinstance(node, ast.Lambda):
        stack.append(node.args)
    elif (cross_function_scopes and isinstance(node, ast.Call)
          and isinstance(node.func, ast.Lambda)):
        stack.extend(ast.iter_child_nodes(node))
        stack.append(node.func.body)
    elif (cross_function_scopes
          and isinstance(node, (ast.Assign, ast.AnnAssign))
          and isinstance(node.value, ast.Lambda)):
        stack.extend(ast.iter_child_nodes(node))
        targets = (node.targets if isinstance(node, ast.Assign)
                   else [node.target])
        names = {target.id for target in targets
                 if isinstance(target, ast.Name)}
        if names & called:
            stack.append(node.value.body)
    else:
        stack.extend(ast.iter_child_nodes(node))
def _lv07_generator_definitely_idle(
        node: ast.GeneratorExp, parents: dict[int, ast.AST],
        while_node: ast.While) -> bool:
    parent = parents.get(id(node))
    if isinstance(parent, ast.Expr) and parent.value is node:
        return True
    if isinstance(parent, ast.Assign) and parent.value is node:
        targets = parent.targets
    elif (isinstance(parent, (ast.AnnAssign, ast.NamedExpr))
          and parent.value is node):
        targets = [parent.target]
    else:
        return False
    if not targets or not all(isinstance(target, ast.Name) for target in targets):
        return False
    names = {target.id for target in targets}
    return not any(
        isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
        and sub.id in names
        for sub in walk_nodes(while_node))
def _lv07_loop_subtree(
        while_node: ast.While, called: set[str] | frozenset[str],
        parents: dict[int, ast.AST]):
    stack: list[ast.AST] = [while_node]
    while stack:
        cur = stack.pop()
        if (cur is not while_node
                and is_statically_unreachable(cur, parents, while_node)):
            continue
        yield cur
        if (isinstance(cur, ast.GeneratorExp)
                and _lv07_generator_definitely_idle(cur, parents, while_node)):
            if cur.generators:
                stack.append(cur.generators[0].iter)
            continue
        _lv07_extend_children(
            stack, cur, while_node, called,
            cross_function_scopes=True)
def _lv07_raise_can_escape_loop(
        raise_node: ast.Raise, parents: dict[int, ast.AST],
        while_node: ast.While) -> bool:
    cur: ast.AST = raise_node
    parent = parents.get(id(cur))
    while parent is not None and parent is not while_node:
        if (isinstance(parent, (ast.With, ast.AsyncWith))
                and any(stmt is cur for stmt in parent.body)):
            return False
        if (isinstance(parent, TRY_NODES) and parent.handlers
                and any(stmt is cur for stmt in parent.body)):
            return False
        cur, parent = parent, parents.get(id(parent))
    return True
def _lv07_loop_has_function_exit(
        while_node: ast.While, parents: dict[int, ast.AST]) -> bool:
    for node in scan_body_no_funcs(while_node.body):
        if not isinstance(node, (ast.Return, ast.Raise)):
            continue
        if is_statically_unreachable(node, parents, while_node):
            continue
        if (isinstance(node, ast.Return)
                or _lv07_raise_can_escape_loop(node, parents, while_node)):
            return True
    return False
def _lv07_chain_bindings(chain: list[ast.AST],
                         cache: dict[int, set[str]]) -> dict[int, set[str]]:
    for scope in chain:
        key = id(scope)
        if key in cache:
            continue
        if isinstance(scope, ast.Lambda):
            names = scope_local_bindings(scope)
        else:
            names = set(assigned_names(getattr(scope, 'body', [])))
            if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
                names |= param_names(scope)
        cache[key] = names
    return cache
def _lv07_scope_declarations(
        scope: ast.AST,
        cache: dict[int, tuple[set[str], set[str]]],
) -> tuple[set[str], set[str]]:
    key = id(scope)
    cached = cache.get(key)
    if cached is None:
        cached = (_lv07_scope_declared(scope, 'global'),
                  _lv07_scope_declared(scope, 'nonlocal'))
        cache[key] = cached
    return cached
def _lv07_binding_map(
        cond_vars: set[str], chain: list[ast.AST],
        bindings: dict[int, set[str]],
        declarations: dict[int, tuple[set[str], set[str]]],
) -> dict[str, ast.AST | None]:
    out: dict[str, ast.AST | None] = {}
    module_scope = next(
        (scope for scope in chain if isinstance(scope, ast.Module)), None)
    for v in cond_vars:
        out[v] = None
        for scope in chain:
            global_names, nonlocal_names = _lv07_scope_declarations(
                scope, declarations)
            if v in global_names:
                out[v] = module_scope
                break
            if v in nonlocal_names:
                continue
            if v in bindings[id(scope)]:
                out[v] = scope
                break
    return out
def _lv07_nonlocal_target(parents: dict[int, ast.AST], fn: ast.AST,
                          name: str,
                          bindings: dict[int, set[str]]) -> ast.AST | None:
    cur = nearest_scope(parents, fn)
    while cur is not None:
        if (isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef))
                and name in bindings.get(id(cur), set())):
            return cur
        cur = nearest_scope(parents, cur)
    return None
def _lv07_alias_assign_pairs(sub: ast.stmt) -> list[tuple[ast.AST, ast.AST]]:
    if isinstance(sub, ast.Assign):
        return [(t, sub.value) for t in sub.targets]
    if isinstance(sub, ast.AnnAssign) and sub.value is not None:
        return [(sub.target, sub.value)]
    return []
def _lv07_method_alias_target(tgt: ast.AST, val: ast.AST) -> str | None:
    if (isinstance(tgt, ast.Name) and isinstance(val, ast.Attribute)
            and isinstance(val.value, ast.Name)):
        return val.value.id
    return None
def _lv07_scope_statements(fn: ast.AST) -> list[ast.AST]:
    body = getattr(fn, 'body', [])
    return scan_body_no_funcs(body if isinstance(body, list) else [body])
def _lv07_declared_subtree(fn: ast.AST, kind: str) -> set[str]:
    want = _LV07_DECL_NODES.get(kind)
    if want is None:
        return set()
    return {name for node in walk_nodes(fn)
            if isinstance(node, want) for name in node.names}
def _lv07_scope_declared(fn: ast.AST, kind: str) -> set[str]:
    want = _LV07_DECL_NODES.get(kind)
    if want is None:
        return set()
    return {name for node in _lv07_scope_statements(fn)
            if isinstance(node, want) for name in node.names}
def _lv07_reachable_scope_statements(fn: ast.AST) -> list[ast.AST]:
    parents = parent_map_of(fn)
    return [node for node in _lv07_scope_statements(fn)
            if not is_statically_unreachable(node, parents, fn)]
def _lv07_scope_rebinds(fn: ast.AST, declared: set[str],
                        kind: str) -> set[str]:
    bound: set[str] = set()
    scoped = _lv07_scope_declared(fn, kind) & declared
    statements = _lv07_reachable_scope_statements(fn)
    if scoped:
        for sub in statements:
            if _lv07_is_pattern_bind_node(sub):
                bound |= capture_binding_names(sub) & scoped
                continue
            for target in _lv07_target_list(sub) or ():
                bound |= set(target_binding_names(target)) & scoped
    parents = parent_map_of(fn)
    direct_defs = [nested for nested in scope_function_defs(fn)
                   if not is_statically_unreachable(nested, parents, fn)]
    reference_nodes = list(statements)
    for nested in direct_defs:
        for surface in _lv07_func_eval_surfaces(nested):
            reference_nodes.extend(walk_nodes(surface))
    referenced = {
        node.id for node in reference_nodes
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)}
    referenced_attrs = {
        node.attr for node in reference_nodes if isinstance(node, ast.Attribute)}
    called_names = {
        node.func.id for node in reference_nodes
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)}
    for nested in direct_defs:
        if nested.name in referenced:
            bound |= _lv07_scope_rebinds(nested, declared, kind)
    for method in _scope_class_method_defs(fn):
        owner = nearest_scope(parents, method)
        constructor_called = (
            method.name in _LV07_CTOR_NAMES
            and isinstance(owner, ast.ClassDef) and owner.name in called_names)
        if method.name in referenced_attrs or constructor_called:
            bound |= _lv07_scope_rebinds(method, declared, kind)
    return bound
def _lv07_declared_rebinds(fn: ast.AST, declared: set[str]) -> set[str]:
    bound: set[str] = set()
    for kind in _LV07_DECL_NODES:
        bound |= _lv07_scope_rebinds(fn, declared, kind)
    return bound
def _lv07_target_signal_names(targets) -> set[str]:
    names: set[str] = set()
    for t in targets:
        names.update(iter_unpack_target_names(t))
        _lv07_mutation_bases(t, names)
    return names
def _lv07_signal_target_names(node: ast.AST) -> set[str] | None:
    if _lv07_is_pattern_bind_node(node):
        return capture_binding_names(node)
    targets = _lv07_target_list(node)
    if targets is None or _lv07_is_pure_annotation(node):
        return None
    return _lv07_target_signal_names(targets)
def _lv07_global_binds_condition(v: str, declared_global: set[str],
                                 bind_map: dict[str, ast.AST | None]) -> bool:
    if v not in declared_global:
        return False
    bv = bind_map.get(v)
    return bv is None or isinstance(bv, ast.Module)
def _lv07_nonlocal_binds_condition(v: str, declared_nonlocal: set[str],
                                   bind_map: dict[str, ast.AST | None]) -> bool:
    return v in declared_nonlocal and isinstance(
        bind_map.get(v), (ast.FunctionDef, ast.AsyncFunctionDef))
def _lv07_declared_candidates(fn_node: ast.AST, cond_vars: set[str],
                              bind_map: dict[str, ast.AST | None]) -> set[str]:
    declared_global = _lv07_declared_subtree(fn_node, 'global')
    declared_nonlocal = _lv07_declared_subtree(fn_node, 'nonlocal')
    candidates: set[str] = set()
    for v in cond_vars:
        if (_lv07_global_binds_condition(v, declared_global, bind_map)
                or _lv07_nonlocal_binds_condition(
                    v, declared_nonlocal, bind_map)):
            candidates.add(v)
    return candidates
def _lv07_func_eval_surfaces(fn_node) -> list[ast.AST]:
    surfaces = list(fn_node.decorator_list)
    surfaces.extend(getattr(fn_node, 'type_params', ()))
    surfaces.append(fn_node.args)
    if fn_node.returns is not None:
        surfaces.append(fn_node.returns)
    return surfaces
def _lv07_class_eval_surfaces(cls_node: ast.ClassDef) -> list[ast.AST]:
    surfaces = list(cls_node.decorator_list)
    surfaces.extend(getattr(cls_node, 'type_params', ()))
    surfaces.extend(cls_node.bases)
    surfaces.extend(kw.value for kw in cls_node.keywords)
    return surfaces
def _lv07_handle_scope_def_node(cur: ast.AST, stack: list[ast.AST],
                                cond_vars: set[str],
                                bind_map: dict[str, ast.AST | None],
                                updated: set[str],
                                called: set[str]) -> bool:
    if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
        candidates = _lv07_declared_candidates(cur, cond_vars, bind_map)
        if candidates and cur.name in called:
            updated.update(_lv07_declared_rebinds(cur, candidates))
        stack.extend(_lv07_func_eval_surfaces(cur))
        return True
    if isinstance(cur, ast.Lambda):
        stack.append(cur.args)
        return True
    if isinstance(cur, ast.ClassDef):
        if cur.name in called:
            for method in scope_function_defs(cur):
                if method.name not in _LV07_CTOR_NAMES:
                    continue
                candidates = _lv07_declared_candidates(
                    method, cond_vars, bind_map)
                if candidates:
                    updated.update(
                        _lv07_declared_rebinds(method, candidates))
        stack.extend(_lv07_class_eval_surfaces(cur))
        return True
    return False
def _lv07_scope_sensitive_signals(while_node: ast.While,
                                  cond_vars: set[str],
                                  parents: dict[int, ast.AST],
                                  bind_map: dict[str, ast.AST | None]) -> tuple[set[str], bool]:
    updated: set[str] = set()
    has_break = False
    called = _lv07_loop_called_names(while_node, parents)
    stack: list[ast.AST] = [while_node]
    while stack:
        cur = stack.pop()
        if (cur is not while_node
                and is_statically_unreachable(cur, parents, while_node)):
            continue
        if isinstance(cur, ast.Break):
            has_break |= break_binding_loop(parents, cur) is while_node
            _lv07_extend_children(
                stack, cur, while_node, called,
                cross_function_scopes=False)
            continue
        if _lv07_handle_scope_def_node(cur, stack, cond_vars, bind_map,
                                        updated, called):
            continue
        names = _lv07_signal_target_names(cur)
        if names is not None:
            updated |= names & cond_vars
        _lv07_extend_children(
            stack, cur, while_node, called,
            cross_function_scopes=False)
    return updated, has_break
def _lv07_def_entry(fn: ast.AST) -> _Lv07DefEntry:
    return (fn, _lv07_declared_subtree(fn, 'global'),
            _lv07_declared_subtree(fn, 'nonlocal'))
def _lv07_def_index(defs: list[ast.AST]) -> _Lv07DefTable:
    grouped: dict[str, list[_Lv07DefEntry]] = {}
    for stmt in defs:
        grouped.setdefault(stmt.name, []).append(_lv07_def_entry(stmt))
    return {name: tuple(entries) for name, entries in grouped.items()}
def _lv07_chain_ctor_methods(
        chain: list[ast.AST]) -> list[tuple[ast.ClassDef, ast.AST]]:
    """链上非 ClassDef 作用域内各类的构造器 (owner, method)。

    构造调用 ``C()`` 的 func 是 Name，既不在仅含 FunctionDef 的
    defs 表里，也不进 attribute_calls；须按类名单独匹配。
    """
    found: list[tuple[ast.ClassDef, ast.AST]] = []
    for scope in chain:
        if isinstance(scope, ast.ClassDef):
            continue
        for owner, method in _scope_class_methods(scope):
            if method.name in _LV07_CTOR_NAMES:
                found.append((owner, method))
    return found
def _lv07_chain_callable_defs(
        chain: list[ast.AST],
        cache: dict[int, _Lv07DefTable],
) -> _Lv07DefTable:
    defs: dict[str, list[_Lv07DefEntry]] = {}
    for scope in reversed(chain):
        if isinstance(scope, ast.ClassDef):
            continue
        key = id(scope)
        if key not in cache:
            cache[key] = _lv07_def_index(scope_function_defs(scope))
        for name, entries in cache[key].items():
            defs.setdefault(name, []).extend(entries)
    return {name: tuple(entries) for name, entries in defs.items()}
def _lv07_loop_called_names(
        while_node: ast.While, parents: dict[int, ast.AST]) -> set[str]:
    called: set[str] = set()
    while True:
        expanded = called | {
            sub.func.id
            for sub in _lv07_loop_subtree(while_node, called, parents)
            if isinstance(sub, ast.Call) and isinstance(sub.func, ast.Name)
        }
        if expanded == called:
            return called
        called = expanded
def _lv07_eager_callback_arg(
        call: ast.Call, parents: dict[int, ast.AST],
        active_builtins: set[str] | frozenset[str]) -> ast.AST | None:
    if not isinstance(call.func, ast.Name):
        return None
    name = call.func.id
    if name in _LV07_EAGER_KEY_BUILTINS and name in active_builtins:
        return next((kw.value for kw in call.keywords if kw.arg == 'key'), None)
    if (name not in _LV07_LAZY_CALLBACK_BUILTINS
            or name not in active_builtins or not call.args):
        return None
    parent = parents.get(id(call))
    if not (isinstance(parent, ast.Call)
            and isinstance(parent.func, ast.Name)
            and parent.func.id in _LV07_EAGER_ITERATOR_CONSUMERS
            and parent.func.id in active_builtins
            and any(arg is call for arg in parent.args)):
        return None
    return call.args[0]
def _lv07_eager_callbacks(
        while_node: ast.While, called: set[str],
        parents: dict[int, ast.AST],
        active_builtins: set[str] | frozenset[str]) -> list[ast.AST]:
    callbacks: list[ast.AST] = []
    for node in _lv07_loop_subtree(while_node, called, parents):
        if not isinstance(node, ast.Call):
            continue
        callback = _lv07_eager_callback_arg(node, parents, active_builtins)
        if callback is not None:
            callbacks.append(callback)
    return callbacks
@dataclass(frozen=True)
class _Lv07AnchorCtx:
    parents: dict[int, ast.AST]
    bind_map: dict[str, ast.AST | None]
    bindings: dict[int, set[str]]
def _lv07_anchor_declared_candidates(
        fn: ast.AST, cond_vars: set[str],
        declared_global: set[str], declared_nonlocal: set[str],
        ctx: _Lv07AnchorCtx) -> set[str]:
    candidates: set[str] = set()
    for v in cond_vars:
        if _lv07_global_binds_condition(v, declared_global, ctx.bind_map):
            candidates.add(v)
            continue
        if (_lv07_nonlocal_binds_condition(v, declared_nonlocal, ctx.bind_map)
                and _lv07_nonlocal_target(
                    ctx.parents, fn, v, ctx.bindings) is ctx.bind_map.get(v)):
            candidates.add(v)
    return candidates
def _scope_class_methods(
        scope: ast.AST) -> list[tuple[ast.ClassDef, ast.AST]]:
    """作用域体内（不进函数/lambda）各类及其直接方法 (owner, method)。"""
    pairs: list[tuple[ast.ClassDef, ast.AST]] = []
    stack: list[ast.AST] = list(reversed(
        list(getattr(scope, 'body', []))))
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                           ast.Lambda)):
            continue
        if isinstance(cur, ast.ClassDef):
            pairs.extend(
                (cur, method) for method in scope_function_defs(cur))
            stack.extend(reversed(list(ast.iter_child_nodes(cur))))
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))
    return pairs
def _scope_class_method_defs(scope: ast.AST) -> list[ast.AST]:
    return [method for _owner, method in _scope_class_methods(scope)]
def _lv07_chain_method_defs(
        chain: list[ast.AST], cache: dict[int, _Lv07DefTable],
) -> _Lv07DefTable:
    defs: dict[str, list[_Lv07DefEntry]] = {}
    for scope in chain:
        key = id(scope)
        if key not in cache:
            cache[key] = _lv07_def_index(_scope_class_method_defs(scope))
        for name, entries in cache[key].items():
            defs.setdefault(name, []).extend(entries)
    return {name: tuple(entries) for name, entries in defs.items()}
def _lv07_attribute_call_names(
        while_node: ast.While, called: set[str] | frozenset[str],
        parents: dict[int, ast.AST]) -> set[str]:
    return {sub.func.attr
            for sub in _lv07_loop_subtree(while_node, called, parents)
            if isinstance(sub, ast.Call)
            and isinstance(sub.func, ast.Attribute)}
def _lv07_rebind_of(
        entry: tuple[ast.AST, set[str], set[str]], cond_vars: set[str],
        ctx: _Lv07AnchorCtx) -> set[str]:
    fn, declared_global, declared_nonlocal = entry
    candidates = _lv07_anchor_declared_candidates(
        fn, cond_vars, declared_global, declared_nonlocal, ctx)
    if not candidates:
        return set()
    return _lv07_declared_rebinds(fn, candidates)
def _lv07_scope_callable_rebinds(
        while_node: ast.While, cond_vars: set[str],
        cache: dict[int, _Lv07DefTable],
        method_cache: dict[int, _Lv07DefTable],
        ctx: _Lv07AnchorCtx) -> set[str]:
    chain = scope_chain(ctx.parents, while_node)
    if not chain:
        return set()
    called = _lv07_loop_called_names(while_node, ctx.parents)
    active_builtins = _LV07_CALLBACK_BUILTINS - _builtin_shadowed_names(
        while_node, ctx.parents, ctx.bindings, _LV07_CALLBACK_BUILTINS)
    callbacks = _lv07_eager_callbacks(
        while_node, called, ctx.parents, active_builtins)
    called |= {node.id for node in callbacks if isinstance(node, ast.Name)}
    updated: set[str] = set()
    defs = _lv07_chain_callable_defs(chain, cache)
    for fname in called & defs.keys():
        for entry in defs[fname]:
            updated |= _lv07_rebind_of(entry, cond_vars, ctx)
    methods = _lv07_chain_method_defs(chain, method_cache)
    attribute_calls = _lv07_attribute_call_names(
        while_node, called, ctx.parents)
    attribute_calls |= {
        node.attr for node in callbacks if isinstance(node, ast.Attribute)}
    for fname in attribute_calls & methods.keys():
        for entry in methods[fname]:
            updated |= _lv07_rebind_of(entry, cond_vars, ctx)
    for owner, method in _lv07_chain_ctor_methods(chain):
        if owner.name in called:
            updated |= _lv07_rebind_of(
                _lv07_def_entry(method), cond_vars, ctx)
    return updated
def _lv07_cond_vars(node: ast.While) -> set[str]:
    called = {sub.func.id for sub in walk_nodes(node.test)
              if isinstance(sub, ast.Call)
              and isinstance(sub.func, ast.Name)}
    return {n.id for n in walk_nodes(node.test)
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)
            and n.id not in called}
def _lv07_cond_load_names(nodes, cond_vars: set[str]):
    for node in nodes:
        if (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
                and node.id in cond_vars):
            yield node.id
def _lv07_call_signal_names(
        node: ast.While, cond_vars: set[str], called: set[str],
        parents: dict[int, ast.AST],
        pure_builtins: frozenset[str]) -> set[str]:
    updated: set[str] = set()
    for sub in _lv07_loop_subtree(node, called, parents):
        if not isinstance(sub, ast.Call):
            continue
        if _lv07_is_pure_builtin_call(sub, pure_builtins):
            call_stream = _lv07_prune_pure_args(sub, pure_builtins)
        else:
            call_stream = _lv07_call_operand_nodes(sub, pure_builtins)
        updated.update(_lv07_cond_load_names(call_stream, cond_vars))
    return updated
class _Lv07ScanState(NamedTuple):
    parents: dict[int, ast.AST]
    callables: dict[int, _Lv07DefTable]
    bindings: dict[int, set[str]]
    methods: dict[int, _Lv07DefTable]
    declarations: dict[int, tuple[set[str], set[str]]]
def _lv07_reaching_values(node: ast.AST, name: str, scope: ast.AST,
                          parents: dict[int, ast.AST]) -> list[ast.expr]:
    position = (node.lineno, node.col_offset)
    candidates: list[tuple[ast.stmt, ast.expr]] = []
    for sub in scan_body_no_funcs(getattr(scope, 'body', [])):
        if not isinstance(sub, (ast.Assign, ast.AnnAssign)):
            continue
        if ((sub.lineno, sub.col_offset) >= position
                or is_statically_unreachable(sub, parents, scope)):
            continue
        for target, value in _lv07_alias_assign_pairs(sub):
            if isinstance(target, ast.Name) and target.id == name:
                candidates.append((sub, value))
                break
    reaching: list[ast.expr] = []
    for candidate, value in candidates:
        candidate_pos = (candidate.lineno, candidate.col_offset)
        if any((other.lineno, other.col_offset) > candidate_pos
               and _binding_dominates_use(other, node, parents)
               for other, _value in candidates):
            continue
        reaching.append(value)
    return reaching
def _lv07_alias_signal_names(node: ast.While, parents: dict[int, ast.AST],
                             cond_vars: set[str]) -> set[str]:
    scope = nearest_scope(parents, node)
    if scope is None:
        return set()
    called = _lv07_loop_called_names(node, parents)
    updated: set[str] = set()
    for sub in _lv07_loop_subtree(node, called, parents):
        if (not isinstance(sub, ast.Call)
                or not isinstance(sub.func, ast.Name)
                or nearest_scope(parents, sub) is not scope):
            continue
        for value in _lv07_reaching_values(
                sub, sub.func.id, scope, parents):
            receiver = _lv07_method_alias_target(sub.func, value)
            if receiver in cond_vars:
                updated.add(receiver)
    return updated
def _lv07_issue(node: ast.While, cond_vars: set[str], filepath,
                src_lines) -> dict[str, Any]:
    stuck = sorted(cond_vars)
    return make_issue(
        'LV-07', 'P1', 'logic_correctness', filepath, node.lineno,
        f"while 条件变量 {'/'.join(stuck)} 循环体内无更新路径（死循环）",
        (
            f'while 条件引用的变量 {stuck} 在循环体内没有任何更新'
            f'（无赋值/重绑定，也未作为调用实参传入可能修改它的函数）'
            f'——条件值恒定不变，初始为真即永久循环（CPU 空转、无'
            f'异常信号）。体内也无 break/return/raise 出口。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：循环条件变量与循环体脱节（重试计数漏递增、队列'
            '漏弹出、标志漏置位）。\n'
            '修复策略：循环体内更新条件变量（``retries += 1`` / '
            '``item = queue.pop()`` / ``done = True``）；确需阻塞轮询'
            '时加超时计数与 break 出口。\n'
            '参考标准：条件不变式死循环缺陷模式（循环条件与循环体状态脱节）'
        ),
        'while-no-update-deadloop',
    )
def _lv07_alias_receiver_signals(node: ast.While, cond_vars: set[str],
                                 parents: dict) -> set[str]:
    scope = nearest_scope(parents, node)
    if scope is None:
        return set()
    called = _lv07_loop_called_names(node, parents)
    updated: set[str] = set()
    for sub in _lv07_loop_subtree(node, called, parents):
        if (not isinstance(sub, ast.Call)
                or not isinstance(sub.func, ast.Attribute)
                or not isinstance(sub.func.value, ast.Name)
                or nearest_scope(parents, sub) is not scope):
            continue
        receiver = sub.func.value.id
        for value in _lv07_reaching_values(sub, receiver, scope, parents):
            refs = {n.id for n in walk_nodes(value) if isinstance(n, ast.Name)}
            updated |= refs & cond_vars
        for cond_var in cond_vars:
            for value in _lv07_reaching_values(
                    sub, cond_var, scope, parents):
                refs = {n.id for n in walk_nodes(value)
                        if isinstance(n, ast.Name)}
                if receiver in refs:
                    updated.add(cond_var)
    return updated
def _lv07_update_signals(node: ast.While, cond_vars: set[str],
                         bind_map: dict[str, ast.AST | None],
                         state: _Lv07ScanState,
                         ) -> tuple[set[str], bool]:
    updated, has_break = _lv07_scope_sensitive_signals(
        node, cond_vars, state.parents, bind_map)
    updated |= _lv07_scope_callable_rebinds(
        node, cond_vars, state.callables, state.methods,
        _Lv07AnchorCtx(state.parents, bind_map, state.bindings))
    called = _lv07_loop_called_names(node, state.parents)
    shadowed = _builtin_shadowed_names(
        node, state.parents, state.bindings, _LV07_PURE_BUILTINS)
    updated |= _lv07_call_signal_names(
        node, cond_vars, called, state.parents,
        _LV07_PURE_BUILTINS - shadowed)
    if not updated:
        updated |= _lv07_alias_signal_names(
            node, state.parents, cond_vars)
    if not updated:
        updated |= _lv07_alias_receiver_signals(
            node, cond_vars, state.parents)
    return updated, has_break
def _lv07_scan_while(node: ast.While, state: _Lv07ScanState,
                     filepath: Any, src_lines: list[str]) -> dict[str, Any] | None:
    if isinstance(node.test, ast.Constant):
        return None
    cond_vars = _lv07_cond_vars(node)
    if not cond_vars:
        return None
    chain = scope_chain(state.parents, node)
    _lv07_chain_bindings(chain, state.bindings)
    bind_map = _lv07_binding_map(
        cond_vars, chain, state.bindings, state.declarations)
    updated, has_break = _lv07_update_signals(
        node, cond_vars, bind_map, state)
    if (updated or has_break
            or _lv07_loop_has_function_exit(node, state.parents)):
        return None
    if block_never_falls_through(node.body, state.parents):
        return None
    return _lv07_issue(node, cond_vars, filepath, src_lines)
def check_LV07(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if not isinstance(tree, ast.AST):
        return issues
    src_lines = source_lines(source)
    state = _Lv07ScanState(parent_map_of(tree), {}, {}, {}, {})
    for node in walk_nodes(tree):
        if (not isinstance(node, ast.While)
                or is_statically_unreachable(node, state.parents, tree)):
            continue
        issue = _lv07_scan_while(node, state, filepath, src_lines)
        if issue is not None:
            issues.append(issue)
    return issues
def _lv30_stmt_lists(tree: ast.AST) -> list[list[ast.stmt]]:
    lists: list[list[ast.stmt]] = []
    stack: list[ast.AST] = [tree]
    while stack:
        node = stack.pop()
        child_lists = [block for block in iter_module_stmt_blocks(node) if block]
        lists.extend(child_lists)
        for stmts in reversed(child_lists):
            stack.extend(reversed(stmts))
    return lists
def _lv30_issue(stmt: ast.While, filepath: Any,
                src_lines: list[str],
                body_exits: bool) -> dict[str, Any]:
    if body_exits:
        return make_issue(
            'LV-30', 'P1', 'logic_correctness', filepath, stmt.lineno,
            'while True 后续语句永不可达：循环仅经 return/raise 退出',
            (
                '``while True`` 体内不存在绑定本循环的 ``break``，但存在'
                '必然 return/raise 的退出路径——循环本身不会挂死，'
                '其后同块语句仍被跳过：控制流只能经 return/raise '
                '离开函数，永远到达不了后续语句；既有的汇总/清理/'
                '返回值逻辑静态确证为死代码。'
            ),
            snippet_of(src_lines, stmt.lineno),
            (
                '根因：把 return/raise 写进 while True 后仍在其后追加'
                '语句，误以为循环会落穿继续执行。\n'
                '修复策略：把后续语句移入 return/raise 之前的可达'
                '路径，或改用 ``while 条件:`` + 循环后收尾；确需'
                '循环后逻辑时用 ``break`` 显式落穿。\n'
                '参考标准：不可达语句缺陷模式（Python 语言参考 '
                'return/raise 控制流语义）'
            ),
            'while-true-no-exit-unreachable',
        )
    return make_issue(
        'LV-30', 'P1', 'logic_correctness', filepath, stmt.lineno,
        'while True 无 break 出口：循环不可终止，后续语句永不可达',
        (
            '``while True`` 体内不存在绑定本循环的 ``break``'
            '——循环永不正常结束，其后同块语句只能经 break '
            '落穿到达，静态确证永不可达（return/raise 走函数'
            '退出路径、异常传播跳过后续语句）。写作时通常'
            '伴随「预期循环可结束」的后续逻辑（return/汇总/'
            '清理），出口缺失使循环进入即挂死：CPU 空转、'
            '线程永不归还。'
        ),
        snippet_of(src_lines, stmt.lineno),
        (
            '根因：循环退出条件缺失——只写了持续执行的轮询/'
            '处理体，漏写终止判定与 break 出口。\n'
            '修复策略：补退出条件（``while True: ... if '
            'done: break`` 或 ``while not done:`` 直接以状态'
            '为条件）；重试/轮询场景加计数上限与超时双出口；'
            '确需常驻时把后续语句移入循环体或移除。\n'
            '参考标准：不可终止循环缺陷模式（Python 语言 '
            'break 编译期绑定语义）'
        ),
        'while-true-no-exit-unreachable',
    )
def check_LV30(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if not isinstance(tree, ast.AST):
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    for stmts in _lv30_stmt_lists(tree):
        for idx, stmt in enumerate(stmts):
            if (not is_constant_true_while(stmt)
                    or is_statically_unreachable(stmt, parents, tree)):
                continue
            if loop_has_binding(parents, stmt, ast.Break):
                continue
            if idx >= len(stmts) - 1:
                continue
            issues.append(_lv30_issue(
                stmt, filepath, src_lines,
                block_never_falls_through(stmt.body)))
    return issues
def _lv31_loop_hit(
        node, parents: dict[int, ast.AST], root: ast.AST) -> bool:
    return any(
        not is_statically_unreachable(stmt, parents, root)
        and block_never_falls_through([stmt])
        for stmt in node.body)
def _lv31_issue(node, filepath, src_lines) -> dict[str, Any]:
    return make_issue(
        'LV-31', 'P2', 'logic_correctness', filepath, node.lineno,
        '循环体首轮迭代即无条件返回：后续元素永不处理',
        (
            '循环体内存在每轮必达的 return/raise（直系终止或'
            'if/else 全分支终止）——循环至多执行一轮，第二'
            '个及之后的元素永不处理。「遍历处理全部元素」的'
            '累加/过滤/查找意图静默落空（结果只反映首元素），'
            '无异常信号，属静默逻辑失效。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：兜底 return 写进了循环体内——「没找到」的'
            '默认返回本应放在循环之后，缩进层级错误使它每轮'
            '执行。\n'
            '修复策略：把兜底 return/raise 移出循环体（与 for '
            '对齐）；循环内只在命中时 return；find-first 惯用'
            '形态用 ``for ...: if match: return x`` + 循环外 '
            '``return None`` 或 ``next((x for x in items if '
            'cond), None)``。\n'
            '参考标准：循环首轮终止缺陷模式（缩进层级与'
            '循环语义）'
        ),
        'loop-first-iteration-return',
    )
def check_LV31(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if not isinstance(tree, ast.AST):
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            continue
        if is_constant_true_while(node):
            continue
        if not node.body:
            continue
        if loop_has_binding(parents, node, ast.Continue):
            continue
        if not _lv31_loop_hit(node, parents, tree):
            continue
        issues.append(_lv31_issue(node, filepath, src_lines))
    return issues
def _lv06_is_positive_int_offset(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant) and isinstance(node.value, int)
            and not isinstance(node.value, bool) and node.value >= 1)
def _lv06_iplus_parts(slice_node: ast.AST,
                      index_var: str) -> tuple[ast.Name, int] | None:
    if not (isinstance(slice_node, ast.BinOp)
            and isinstance(slice_node.op, ast.Add)):
        return None
    for left, right in ((slice_node.left, slice_node.right),
                        (slice_node.right, slice_node.left)):
        if (isinstance(left, ast.Name) and left.id == index_var
                and _lv06_is_positive_int_offset(right)):
            return left, right.value
    return None
def _lv06_index_offset(expr: ast.AST, index_var: str) -> int | None:
    if isinstance(expr, ast.Name):
        return 0 if expr.id == index_var else None
    parts = _lv06_iplus_parts(expr, index_var)
    return parts[1] if parts is not None else None
def _lv06_len_offset(expr: ast.AST, seq_var: str) -> int | None:
    if (isinstance(expr, ast.Call) and isinstance(expr.func, ast.Name)
            and expr.func.id == 'len' and not expr.keywords
            and len(expr.args) == 1
            and isinstance(expr.args[0], ast.Name)
            and expr.args[0].id == seq_var):
        return 0
    if isinstance(expr, ast.BinOp) and isinstance(expr.op, (ast.Add, ast.Sub)):
        base = _lv06_len_offset(expr.left, seq_var)
        const = int_literal(expr.right)
        if base is not None and const is not None:
            return base + const if isinstance(expr.op, ast.Add) else base - const
        if isinstance(expr.op, ast.Add):
            base = _lv06_len_offset(expr.right, seq_var)
            const = int_literal(expr.left)
            if base is not None and const is not None:
                return base + const
    return None
def _lv06_bound_compare(expr: ast.AST, index_var: str,
                        seq_var: str) -> tuple[type, int, int] | None:
    if not isinstance(expr, ast.Compare) or not expr.ops:
        return None
    left = expr.left
    for op, right in zip(expr.ops, expr.comparators, strict=False):
        offset = _lv06_index_offset(left, index_var)
        bound = _lv06_len_offset(right, seq_var)
        if offset is not None and bound is not None:
            return type(op), offset, bound
        offset = _lv06_index_offset(right, index_var)
        bound = _lv06_len_offset(left, seq_var)
        flipped = _LV06_COMPARE_FLIP.get(type(op))
        if offset is not None and bound is not None and flipped is not None:
            return flipped, offset, bound
        left = right
    return None
def _lv06_guard_min_offset(test: ast.AST, index_var: str,
                           seq_var: str) -> int | None:
    best: int | None = None
    conjuncts = (list(test.values) if isinstance(test, ast.BoolOp)
                 and isinstance(test.op, ast.And) else [test])
    for expr in conjuncts:
        bound = _lv06_bound_compare(expr, index_var, seq_var)
        if bound is None:
            continue
        op, offset, const = bound
        if op is ast.Lt:
            cand = offset - const
        elif op is ast.LtE:
            cand = offset - const - 1
        else:
            continue
        best = cand if best is None else max(best, cand)
    return best
def _lv06_exit_guard_covers(stmt: ast.AST, index_var: str, seq_var: str,
                            offset: int) -> bool:
    if isinstance(stmt, ast.Assert):
        return _lv06_guard_holds(
            stmt.test, offset, index_var, seq_var, positive=True)
    if not isinstance(stmt, ast.If):
        return False
    if block_exits(stmt.body):
        return _lv06_guard_holds(
            stmt.test, offset, index_var, seq_var, positive=False)
    if stmt.orelse and block_exits(stmt.orelse):
        return _lv06_guard_holds(
            stmt.test, offset, index_var, seq_var, positive=True)
    return False
def _lv06_negated_test(test: ast.AST) -> ast.AST | None:
    if not isinstance(test, ast.Compare) or len(test.ops) != 1:
        return None
    negate = _LV06_COMPARE_NEGATE.get(type(test.ops[0]))
    if negate is None:
        return None
    return ast.Compare(left=test.left, ops=[negate()],
                       comparators=[test.comparators[0]])
def _lv06_guard_holds(test: ast.AST, offset: int, index_var: str,
                      seq_var: str, *, positive: bool) -> bool:
    if _lv06_expression_rebinds_guard_inputs(test, index_var, seq_var):
        return False
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _lv06_guard_holds(test.operand, offset, index_var, seq_var,
                                 positive=not positive)
    if not positive and isinstance(test, ast.BoolOp) and isinstance(test.op, ast.Or):
        return any(_lv06_guard_holds(value, offset, index_var, seq_var,
                                     positive=False)
                   for value in test.values)
    if positive:
        min_offset = _lv06_guard_min_offset(test, index_var, seq_var)
    else:
        negated = _lv06_negated_test(test)
        if negated is None:
            return False
        min_offset = _lv06_guard_min_offset(negated, index_var, seq_var)
    return min_offset is not None and offset <= min_offset
def _lv06_rebinds_guard_inputs(stmts: list, index_var: str,
                               seq_var: str) -> bool:
    inputs = {index_var, seq_var}
    return any(inputs.intersection(assigned_names([stmt])) for stmt in stmts)
def _lv06_iter_guard_nodes(
        stmts: list, *, include_called_lambda_bodies: bool,
) -> Iterator[ast.AST]:
    stack = list(stmts)
    immediate_lambdas: set[int] = set()
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                           ast.ClassDef)):
            continue
        if isinstance(cur, ast.Lambda):
            stack.append(cur.args)
            if include_called_lambda_bodies and id(cur) in immediate_lambdas:
                stack.append(cur.body)
            continue
        if isinstance(cur, ast.Call) and isinstance(cur.func, ast.Lambda):
            immediate_lambdas.add(id(cur.func))
        yield cur
        stack.extend(ast.iter_child_nodes(cur))
def _lv06_sequence_length_changes(stmts: list, seq_var: str) -> bool:
    for node in _lv06_iter_guard_nodes(
            stmts, include_called_lambda_bodies=True):
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id == seq_var
                and node.func.attr in _LV06_LENGTH_REDUCING_METHODS):
            return True
        if (isinstance(node, ast.Subscript)
                and isinstance(node.ctx, ast.Store)
                and isinstance(node.slice, ast.Slice)
                and isinstance(node.value, ast.Name)
                and node.value.id == seq_var
                and (node.slice.step is None
                     or (isinstance(node.slice.step, ast.Constant)
                         and node.slice.step.value is None))):
            # 扩展切片要求等长替换，不会使既有的长度边界守卫失效。
            return True
        if isinstance(node, ast.Delete) and any(
                isinstance(target, ast.Subscript)
                and isinstance(target.value, ast.Name)
                and target.value.id == seq_var
                for target in node.targets):
            return True
    return False
def _lv06_guard_inputs_invalidated(stmts: list, index_var: str,
                                   seq_var: str) -> bool:
    return (_lv06_rebinds_guard_inputs(stmts, index_var, seq_var)
            or _lv06_sequence_length_changes(stmts, seq_var))
def _lv06_expression_rebinds_guard_inputs(
        expression: ast.AST, index_var: str, seq_var: str,
) -> bool:
    rebound = {
        name
        for node in _lv06_iter_guard_nodes(
            [expression], include_called_lambda_bodies=False)
        if isinstance(node, ast.NamedExpr)
        for name in target_binding_names(node.target)
    }
    if {index_var, seq_var} & rebound:
        return True
    return _lv06_sequence_length_changes([expression], seq_var)
def _lv06_evaluated_before(node: ast.AST, child: ast.AST) -> list[ast.AST]:
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        siblings = list(node.elts)
    elif isinstance(node, ast.BoolOp):
        siblings = list(node.values)
    elif isinstance(node, ast.BinOp):
        siblings = [node.left, node.right]
    elif isinstance(node, ast.Compare):
        siblings = [node.left, *node.comparators]
    elif isinstance(node, ast.Call):
        siblings = [node.func, *node.args, *node.keywords]
    elif isinstance(node, ast.IfExp):
        return [node.test] if child in (node.body, node.orelse) else []
    elif isinstance(node, ast.Subscript):
        siblings = [node.value, node.slice]
    elif isinstance(node, ast.Dict):
        siblings = []
        for key, value in zip(node.keys, node.values, strict=True):
            if key is not None:
                siblings.append(key)
            siblings.append(value)
    elif isinstance(node, ast.Slice):
        siblings = [node.lower, node.upper, node.step]
    else:
        return []
    preceding: list[ast.AST] = []
    for sibling in siblings:
        if sibling is child:
            return preceding
        if sibling is not None:
            preceding.append(sibling)
    return []
def _lv06_expression_prefix_invalidates_guard(
        root: ast.AST, hit: ast.AST, index_var: str, seq_var: str,
) -> bool:
    if root is hit:
        return False
    for child in ast.iter_child_nodes(root):
        if child is not hit and not subtree_contains(child, hit):
            continue
        if any(_lv06_expression_rebinds_guard_inputs(
                previous, index_var, seq_var)
               for previous in _lv06_evaluated_before(root, child)):
            return True
        return _lv06_expression_prefix_invalidates_guard(
            child, hit, index_var, seq_var)
    return False
def _lv06_statement_rebinds_before_hit(
        stmt: ast.AST, hit: ast.AST, index_var: str, seq_var: str,
) -> bool:
    if not isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        if (subtree_contains(stmt, hit)
                and _lv06_expression_prefix_invalidates_guard(
                    stmt, hit, index_var, seq_var)):
            return True
        return _lv06_rebinds_guard_inputs([stmt], index_var, seq_var)
    value = stmt.value
    if value is not None and subtree_contains(value, hit):
        return _lv06_expression_rebinds_guard_inputs(
            value, index_var, seq_var)
    targets = (stmt.targets if isinstance(stmt, ast.Assign)
               else [stmt.target])
    inputs = {index_var, seq_var}
    for index, target in enumerate(targets):
        if not subtree_contains(target, hit):
            continue
        if (not isinstance(stmt, ast.AugAssign) and value is not None
                and _lv06_expression_rebinds_guard_inputs(
                    value, index_var, seq_var)):
            return True
        if inputs & _lv07_target_signal_names(targets[:index]):
            return True
        return _lv06_expression_rebinds_guard_inputs(
            target, index_var, seq_var)
    return _lv06_rebinds_guard_inputs([stmt], index_var, seq_var)
def _lv06_branch_guard_covers(
        node: ast.AST, cur: ast.AST, hit: ast.AST,
        index_var: str, seq_var: str, offset: int,
) -> bool:
    body_hit = any(stmt is cur for stmt in node.body)
    if not body_hit and not any(stmt is cur for stmt in node.orelse):
        return False
    stmts = node.body if body_hit else node.orelse
    if (_lv06_guard_inputs_invalidated(
            prior_statements(stmts, cur), index_var, seq_var)
            or _lv06_statement_rebinds_before_hit(
                cur, hit, index_var, seq_var)):
        return False
    return _lv06_guard_holds(node.test, offset, index_var, seq_var,
                             positive=body_hit)
def _lv06_expr_guard_covers(hit: ast.AST, offset: int, index_var: str,
                            seq_var: str, parents: dict[int, ast.AST]) -> bool:
    cur = hit
    parent = parents.get(id(cur))
    while parent is not None and isinstance(parent, ast.expr):
        if isinstance(parent, FUNC_SCOPE_NODES):
            return False
        if isinstance(parent, ast.BoolOp):
            position = next((idx for idx, value in enumerate(parent.values)
                             if value is cur), 0)
            if position:
                if _lv06_expression_prefix_invalidates_guard(
                        cur, hit, index_var, seq_var):
                    return False
                positive = isinstance(parent.op, ast.And)
                for guard_index, test in enumerate(parent.values[:position]):
                    if not _lv06_guard_holds(
                            test, offset, index_var, seq_var,
                            positive=positive):
                        continue
                    if any(_lv06_expression_rebinds_guard_inputs(
                            intermediate, index_var, seq_var)
                           for intermediate in
                           parent.values[guard_index + 1:position]):
                        continue
                    return True
        elif (isinstance(parent, ast.IfExp) and parent.test is not cur
              and _lv06_guard_holds(
                  parent.test, offset, index_var, seq_var,
                  positive=parent.body is cur)
              and not _lv06_expression_prefix_invalidates_guard(
                  cur, hit, index_var, seq_var)):
            return True
        cur, parent = parent, parents.get(id(parent))
    return False
def _lv06_guarded(sub: ast.Subscript, offset: int, node: ast.For,
                  seq_var: str, index_var: str,
                  parents: dict[int, ast.AST]) -> bool:
    cur: ast.AST = sub
    parent = parents.get(id(cur))
    nested_loop = False
    if _lv06_expr_guard_covers(sub, offset, index_var, seq_var, parents):
        return True
    while parent is not None:
        allow_preceding = not nested_loop
        if parent is not node:
            if isinstance(parent, ast.Lambda):
                return False
            if isinstance(parent, (ast.For, ast.AsyncFor, ast.While)):
                nested_loop = True
                if _lv06_guard_inputs_invalidated(
                        [parent], index_var, seq_var):
                    return False
            if (isinstance(parent, _LV06_BRANCH_GUARD_NODES)
                    and _lv06_branch_guard_covers(
                        parent, cur, sub, index_var, seq_var, offset)):
                return True
        if allow_preceding:
            preceding = preceding_statements(parent, cur)
            for idx, prev in enumerate(preceding):
                if not _lv06_exit_guard_covers(
                        prev, index_var, seq_var, offset):
                    continue
                if (_lv06_guard_inputs_invalidated(
                        preceding[idx + 1:], index_var, seq_var)
                        or _lv06_statement_rebinds_before_hit(
                            cur, sub, index_var, seq_var)):
                    continue
                return True
        if parent is node:
            break
        cur, parent = parent, parents.get(id(parent))
    return False
def _lv06_shadowed(name_node: ast.Name, for_node: ast.For,
                   name: str, parents: dict[int, ast.AST]) -> bool:
    cur = parents.get(id(name_node))
    while cur is not None and cur is not for_node:
        if construct_shadows_name(cur, name, name_node):
            return True
        cur = parents.get(id(cur))
    return False
def _lv06_deferred_by_lambda(
        node: ast.AST, for_node: ast.For,
        parents: dict[int, ast.AST]) -> bool:
    cur = node
    parent = parents.get(id(cur))
    while parent is not None and parent is not for_node:
        if isinstance(parent, ast.Lambda) and cur is parent.body:
            call = parents.get(id(parent))
            if not (isinstance(call, ast.Call) and call.func is parent):
                return True
        cur, parent = parent, parents.get(id(parent))
    return False
def _lv06_rebinding_dominates_hit(
        node: ast.For, hit: ast.Subscript, seq_var: str, index_var: str,
        parents: dict[int, ast.AST],
) -> bool:
    position = (hit.lineno, hit.col_offset)
    inputs = {seq_var, index_var}
    for stmt in scan_body_no_funcs(node.body):
        if subtree_contains(stmt, hit):
            continue
        if _lv07_is_pattern_bind_node(stmt):
            bound = capture_binding_names(stmt)
        else:
            targets = _lv07_target_list(stmt)
            if targets is None:
                continue
            bound = {name for target in targets
                     for name in iter_unpack_target_names(target)}
        if not inputs & bound or (stmt.lineno, stmt.col_offset) >= position:
            continue
        if _binding_dominates_use(stmt, hit, parents):
            return True
    return False
def _lv06_index_hits(
        node: ast.For, seq_var: str, index_var: str,
        parents: dict[int, ast.AST], root: ast.AST,
) -> list[tuple[ast.Subscript, int]]:
    if seq_var in target_binding_names(node.target):
        return []
    hits: list[tuple[ast.Subscript, int]] = []
    for sub in iter_nodes_outside(
            node, stop_nodes=(ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)):
        if not (isinstance(sub, ast.Subscript)
                and isinstance(sub.value, ast.Name)
                and sub.value.id == seq_var):
            continue
        if (is_statically_unreachable(sub, parents, root)
                or _lv06_deferred_by_lambda(sub, node, parents)):
            continue
        parts = _lv06_iplus_parts(sub.slice, index_var)
        if parts is None:
            continue
        index_name, offset = parts
        if (_lv06_shadowed(sub.value, node, seq_var, parents)
                or _lv06_shadowed(index_name, node, index_var, parents)):
            continue
        if _lv06_rebinding_dominates_hit(
                node, sub, seq_var, index_var, parents):
            continue
        if _lv06_guarded(sub, offset, node, seq_var, index_var, parents):
            continue
        hits.append((sub, offset))
    return hits
def _lv06_loop_pair(node: ast.AST) -> tuple[str, str] | None:
    if not isinstance(node, ast.For) or not isinstance(node.target, ast.Name):
        return None
    seq_var = range_len_source(node.iter)
    if seq_var is None:
        return None
    return seq_var, node.target.id
def _execution_scope_definition_lines(
        scope: ast.AST, parents: dict[int, ast.AST],
        builtin_names: frozenset[str]) -> dict[str, int]:
    lines: dict[str, int] = {}
    for sub in walk_nodes(scope):
        if not isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.ClassDef)):
            continue
        if sub.name not in builtin_names or nearest_scope(parents, sub) is not scope:
            continue
        previous = lines.get(sub.name)
        if previous is None or sub.lineno < previous:
            lines[sub.name] = sub.lineno
    return lines
def _preceding_builtin_bindings(
        node: ast.AST, scope: ast.AST, parents: dict[int, ast.AST],
        builtin_names: frozenset[str]) -> set[str]:
    binding_lines = assigned_names(scope.body)
    for name, line in _execution_scope_definition_lines(
            scope, parents, builtin_names).items():
        previous = binding_lines.get(name)
        if previous is None or line < previous:
            binding_lines[name] = line
    return {name for name in builtin_names
            if binding_lines.get(name, node.lineno + 1) <= node.lineno}
def _builtin_shadowed_names(
        node: ast.AST, parents: dict[int, ast.AST],
        cache: dict[int, set[str]],
        builtin_names: frozenset[str]) -> set[str]:
    shadowed: set[str] = set()
    chain = scope_chain(parents, node)
    bindings = _lv07_chain_bindings(chain, cache)
    execution_order_scope = True
    for scope in chain:
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            execution_order_scope = False
        if (execution_order_scope
                and isinstance(scope, (ast.Module, ast.ClassDef))):
            shadowed.update(_preceding_builtin_bindings(
                node, scope, parents, builtin_names))
            continue
        shadowed.update(bindings[id(scope)] & builtin_names)
        body = getattr(scope, 'body', ())
        if isinstance(body, list):
            shadowed.update(scope_definition_names(body) & builtin_names)
    return shadowed
def check_LV06(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    shadow_cache: dict[int, set[str]] = {}
    for node in roots:
        pair = _lv06_loop_pair(node)
        if pair is None:
            continue
        if _builtin_shadowed_names(
                node, parents, shadow_cache, _LV06_BUILTIN_NAMES):
            continue
        seq_var, index_var = pair
        issues.extend(
            _lv06_issue(
                seq_var, index_var, offset, sub.lineno, filepath, src_lines)
            for sub, offset in _lv06_index_hits(
                node, seq_var, index_var, parents, tree))
    return issues
def _lv06_issue(seq_var: str, index_var: str, offset: int, lineno: int,
                filepath: Any, src_lines: list[str]) -> dict[str, Any]:
    return make_issue(
        'LV-06', 'P1', 'index_safety', filepath, lineno,
        f'range(len({seq_var})) 循环内 '
        f'{seq_var}[{index_var}+{offset}] 越界',
        (
            f'循环 ``for {index_var} in range(len({seq_var}))`` 的'
            f'最后一轮 {index_var} = len({seq_var})-1，'
            f'``{seq_var}[{index_var}+{offset}]`` 下标达到 '
            f'len({seq_var})+{offset - 1}，触发 IndexError。'
        ),
        snippet_of(src_lines, lineno),
        (
            f'根因：邻居遍历边界少算 {offset} 次'
            f'（{index_var}+{offset} 超出 range 上界）。\n'
            f'修复策略：``for {index_var} in '
            f'range(len({seq_var}) - {offset})``；或用 '
            f'``zip({seq_var}, {seq_var}[{offset}:])`` 配对遍历'
            '（零越界且语义清晰）。\n'
            '参考标准：邻居越界缺陷模式（行为级阳性对照实验）'
        ),
        'range-len-neighbor-overflow',
    )
def _lv11_range_call_args(node: ast.AST) -> list[ast.expr] | None:
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'range'):
        return None
    if node.keywords:
        return None
    if len(node.args) == 2:
        return node.args
    if len(node.args) == 3 and int_literal(node.args[2]) is not None:
        return node.args
    return None
def _lv11_range_step(args: list[ast.expr]) -> int | None:
    return 1 if len(args) == 2 else int_literal(args[2])
def _lv11_empty_range_args(node: ast.AST) -> tuple[int, int] | None:
    args = _lv11_range_call_args(node)
    if args is None:
        return None
    sv = int_literal(args[0])
    ev = int_literal(args[1])
    step = _lv11_range_step(args)
    if sv is None or ev is None or not step or sv == ev:
        return None
    if (sv > ev and step > 0) or (sv < ev and step < 0):
        return sv, ev
    return None
def _lv11_issue(node: ast.AST, sv: int, ev: int, filepath: Any,
                src_lines: list[str]) -> dict[str, Any]:
    args = getattr(node, 'args', ())
    step_val = int_literal(args[2]) if len(args) == 3 else None
    stepped = step_val is not None
    call_text = (f'range({sv}, {ev}, {step_val})' if stepped
                 else f'range({sv}, {ev})')
    if not stepped:
        step_desc = '省略步长即 +1'
    elif step_val > 0:
        step_desc = f'显式步长 +{step_val}'
    else:
        step_desc = f'显式步长 {step_val}'
    return make_issue(
        'LV-11', 'P1', 'logic_correctness', filepath, node.lineno,
        f'{call_text} 起止方向与步长推进方向相反：迭代恒空、循环体永不执行',
        (
            f'``{call_text}`` 中起始值 {sv} 与终止值 {ev} 的跨越方向'
            f'与{step_desc}相反——区间恒为空，循环体一次都不执行，'
            f'循环内逻辑全部静默失效（统计归零/任务跳过），'
            f'无任何异常信号提示。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            f'根因：倒序遍历忘写步长（``range({sv}, {ev}, -1)``）、正向遍历\n'
            f'误写负步长（``range(lo, hi, -1)``），或起止边界写反。\n'
            '修复策略：方向必须自洽——倒序 ``range(hi, lo, -1)``、升序\n'
            '``range(lo, hi)``（含头不含尾）；步长方向与边界同向时区间不为空。\n'
            '参考标准：range 迭代空区间契约（正步长需 start < stop，负步长需 start > stop）'
        ),
        'empty-range-loop',
    )
def check_LV11(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    shadow_cache: dict[int, set[str]] = {}
    range_name = frozenset({'range'})
    for node in roots:
        bounds = _lv11_empty_range_args(node)
        if (bounds is None
                or is_statically_unreachable(node, parents, tree)
                or _builtin_shadowed_names(
                    node, parents, shadow_cache, range_name)):
            continue
        sv, ev = bounds
        issues.append(_lv11_issue(node, sv, ev, filepath, src_lines))
    return issues

from __future__ import annotations

import ast
import logging
from typing import Any

from jwsgj.prevention_container_mutation import (
    _CONTAINER_COMP_NODES,
    _EMPTY_VISITS,
    _SHRINK_METHODS,
    _actual_arg,
    _aligned_assignment_pairs,
    _assignment_candidates,
    _binding_dominates_scope,
    _binding_scope,
    _child_under,
    _comp_prior_guards,
    _enclosing_function,
    _expression_condition_guarded,
    _expression_guard_invalidated,
    _guarded_on_path,
    _latest_assignment,
    _len_arg_expr,
    _len_const_compare,
    _loop_guarantees_once,
    _lv09_ancestor_chain,
    _lv09_comp_is_output_position,
    _lv09_comp_shadowed_names,
    _lv09_static_dict_len,
    _lv09_static_set_len,
    _matching_calls,
    _mutates_name,
    _nonempty_holds,
    _nonempty_literal,
    _pattern_irrefutable,
    _private_callable,
    _range_length,
    _range_nonempty,
    _resolved_int,
    _scope_chain,
)
from jwsgj.prevention_container_mutation import (
    _binding_invalidated_since as _binding_invalidated_since_base,
)
from jwsgj.prevention_scope_facts import (
    FUNC_SCOPE_NODES,
    TRY_NODES,
    binding_entries_index,
    block_exits,
    branch_truth,
    capture_binding_names,
    int_literal,
    iter_binding_entries,
    make_issue,
    nearest_scope,
    param_names,
    parent_map_of,
    scan_body_no_funcs,
    scope_local_bindings,
    shadowed_binding_at,
    snippet_of,
    source_lines,
    target_store_names,
    walk_ast_nodes,
    walk_nodes,
)

__all__ = [
    'check_LV25',
    'check_LV27',
]
_log = logging.getLogger(__name__)
_log.info(
    "prevention_container_length 容器长度 / 非空不变量"
    "两族检测器已加载：%d 项导出", len(__all__))
_LV25_ALIAS_ROUNDS = 3
_LV25_COLLECTOR_ROUNDS = 2
_LV25_CONTAINER_CTORS = frozenset({'list', 'tuple', 'set', 'frozenset', 'dict'})
_LV25_ITER_CALLS = _LV25_CONTAINER_CTORS | frozenset({
    'iter', 'reversed', 'enumerate', 'sorted', 'zip',
})
#: 必然让容器多出元素的成员方法。``append``/``insert``/``add`` 无论实参如何都
#: 增加一个元素；``setdefault`` 对不存在的键总是写入，命中已存在的键时容器
#: 本就非空；``extend``/``update`` 可能收到空容器，实参必须已知非空。
_LV25_GROWTH_METHODS = frozenset({
    'append', 'insert', 'add', 'setdefault', 'extend', 'update',
})
_LV25_GROWTH_METHODS_NEEDING_NONEMPTY_ARG = frozenset({'extend', 'update'})
def _lv25_assign_shape(node: ast.AST) -> tuple[ast.expr, ast.expr] | None:
    if isinstance(node, ast.Assign):
        if len(node.targets) != 1:
            return None
        return node.targets[0], node.value
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return node.target, node.value
    return None
def _lv25_div_operands(node: ast.AST) -> tuple[ast.operator, ast.expr] | None:
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, (ast.Div, ast.FloorDiv)):
            return node.op, node.right
        return None
    if isinstance(node, ast.AugAssign) and isinstance(
            node.op, (ast.Div, ast.FloorDiv)):
        return node.op, node.value
    return None
def _lv25_guarded_names(
        tree: ast.AST,
        parent: dict[int, ast.AST]) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        shape = _lv25_assign_shape(node)
        if (shape is not None and isinstance(shape[0], ast.Name)
                and _nonempty_literal(shape[1])):
            names.add(shape[0].id)
    names |= _lv25_ctor_targets(tree, parent)
    _lv25_derive_aliases_fixpoint(tree, names, parent)
    _propagate_collector_safety(tree, names, parent)
    return names
def _lv25_iter_subject(
        iter_node: ast.AST, parent: dict[int, ast.AST],
        forward: bool = False) -> ast.AST:
    if (isinstance(iter_node, ast.Call)
            and isinstance(iter_node.func, ast.Attribute)
            and not iter_node.keywords):
        method = iter_node.func.attr
        if (method in ('values', 'keys', 'items', 'copy')
                and not iter_node.args):
            return iter_node.func.value
        if (forward and method in ('split', 'rsplit')
                and 1 <= len(iter_node.args) <= 2
                and all(not isinstance(arg, ast.Starred)
                        for arg in iter_node.args)):
            separator = iter_node.args[0]
            if (isinstance(separator, ast.Constant)
                    and separator.value is not None):
                return iter_node.func.value
    if not (isinstance(iter_node, ast.Call)
            and isinstance(iter_node.func, ast.Name)
            and not iter_node.keywords):
        return iter_node
    name = iter_node.func.id
    if (name == 'range' and len(iter_node.args) == 1
            and not shadowed_binding_at(iter_node, 'range', parent, {})):
        arg = iter_node.args[0]
        if (isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name)
                and arg.func.id == 'len' and len(arg.args) == 1
                and not arg.keywords
                and not isinstance(arg.args[0], ast.Starred)
                and not shadowed_binding_at(arg, 'len', parent, {})):
            return arg.args[0]
    if (name in _LV25_ITER_CALLS and len(iter_node.args) == 1
            and not isinstance(iter_node.args[0], ast.Starred)
            and not shadowed_binding_at(iter_node, name, parent, {})):
        return iter_node.args[0]
    return iter_node
def _lv25_iter_source_name(
        iter_node: ast.AST, parent: dict[int, ast.AST],
        forward: bool = False) -> str | None:
    subject = _lv25_iter_subject(iter_node, parent, forward)
    return subject.id if isinstance(subject, ast.Name) else None
def _kv_value_evidence(
        node: ast.AST, name: str, kv_collectors: set[str],
        parent: dict[int, ast.AST]) -> ast.AST | None:
    scope = nearest_scope(parent, node)
    if scope is None:
        return None
    limit = (node.lineno, node.col_offset)
    for for_node in walk_nodes(scope):
        if not isinstance(for_node, ast.For):
            continue
        if (for_node.lineno, for_node.col_offset) >= limit:
            continue
        if nearest_scope(parent, for_node) is not scope:
            continue
        if not _lv25_node_in_loop_body(node, for_node, parent):
            continue
        if (isinstance(for_node.target, ast.Name)
                and for_node.target.id == name
                and _kv_items_iter_name(for_node.iter, kv_collectors)):
            return for_node
        iter_node = for_node.iter
        receiver = (iter_node.func.value.id
                    if isinstance(iter_node, ast.Call)
                    and isinstance(iter_node.func, ast.Attribute)
                    and isinstance(iter_node.func.value, ast.Name) else None)
        if (name in _kv_iter_value_targets(for_node)
                and receiver in kv_collectors
                and _kv_value_scope_ok(for_node, receiver, parent)
                and _kv_collector_values_safe(scope, receiver, parent)):
            return for_node
    return None
def _kv_value_scope_ok(for_node: ast.For, collector: str,
                       parent: dict[int, ast.AST]) -> bool:
    scope = nearest_scope(parent, for_node)
    if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False
    if collector in param_names(scope):
        return False
    return _binding_scope(for_node, collector, parent) is scope
_KV_VALUE_UNSAFE_METHODS = frozenset({'update', 'clear', 'pop', 'popitem'})
def _kv_iter_value_targets(for_node: ast.For) -> set[str]:
    iter_node = for_node.iter
    if not (isinstance(iter_node, ast.Call)
            and isinstance(iter_node.func, ast.Attribute)):
        return set()
    target = for_node.target
    if iter_node.func.attr == 'values' and isinstance(target, ast.Name):
        return {target.id}
    if (iter_node.func.attr == 'items'
            and isinstance(target, (ast.Tuple, ast.List))
            and target.elts and isinstance(target.elts[-1], ast.Name)):
        return {target.elts[-1].id}
    return set()
def _kv_value_mutator_call(node: ast.AST, collector: str) -> bool:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _SHRINK_METHODS):
        return False
    return any(
        isinstance(sub, ast.Name) and sub.id == collector
        and isinstance(sub.ctx, ast.Load)
        for sub in walk_nodes(node.func.value))
def _kv_value_aliases(
        scope: ast.AST, collector: str,
        parent: dict[int, ast.AST]) -> set[str]:
    aliases: set[str] = set()
    for candidate in walk_nodes(scope):
        if (not isinstance(candidate, (ast.For, ast.AsyncFor))
                or nearest_scope(parent, candidate) is not scope):
            continue
        iter_node = candidate.iter
        if not (isinstance(iter_node, ast.Call)
                and isinstance(iter_node.func, ast.Attribute)
                and iter_node.func.attr in ('values', 'items')
                and not iter_node.args and not iter_node.keywords
                and isinstance(iter_node.func.value, ast.Name)
                and iter_node.func.value.id == collector):
            continue
        aliases.update(_kv_iter_value_targets(candidate))
    while True:
        grew = False
        for candidate in walk_nodes(scope):
            if nearest_scope(parent, candidate) is not scope:
                continue
            bindings = _lv25_alias_binding(candidate)
            if bindings is None:
                continue
            for targets, value in bindings:
                if isinstance(value, ast.Name) and value.id in aliases:
                    before = len(aliases)
                    aliases.update(targets)
                    grew = grew or len(aliases) != before
        if not grew:
            return aliases
def _kv_collector_values_safe(scope: ast.AST, collector: str,
                              parent: dict[int, ast.AST]) -> bool:
    def _binds(target: ast.AST) -> bool:
        return any(bound == collector
                   for bound, _line in target_store_names(target, 0))
    def _subscript_of(target: ast.AST) -> bool:
        if not isinstance(target, ast.Subscript):
            return False
        cur = target
        while isinstance(cur, ast.Subscript):
            cur = cur.value
        return isinstance(cur, ast.Name) and cur.id == collector
    def _deletes(target: ast.AST) -> bool:
        return any(
            isinstance(sub, ast.Name) and sub.id == collector
            and isinstance(sub.ctx, ast.Del)
            for sub in walk_nodes(target))
    value_aliases = _kv_value_aliases(scope, collector, parent)
    for node in walk_nodes(scope):
        if (value_aliases and not isinstance(
                node, (ast.For, ast.AsyncFor, ast.Name))):
            bindings = _lv25_alias_binding(node)
            pure_alias = bool(bindings) and all(
                isinstance(value, ast.Name) and value.id in value_aliases
                for _targets, value in bindings)
            if (not pure_alias and any(
                    _mutates_name(node, alias) for alias in value_aliases)):
                return False
        if (node is not scope
                and isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                      ast.Lambda, ast.ClassDef))):
            if getattr(node, 'name', None) == collector:
                return False
            if collector in param_names(node):
                return False
            if any(isinstance(sub, ast.Name) and sub.id == collector
                   for sub in walk_nodes(node)):
                return False
            continue
        if collector in capture_binding_names(node):
            return False
        if isinstance(node, ast.Assign):
            targets = node.targets
        elif isinstance(node, ast.AnnAssign):
            if node.value is None:
                continue
            targets = [node.target]
        elif isinstance(node, ast.AugAssign):
            targets = [node.target]
        else:
            targets = []
        if targets:
            bound = any(_binds(tgt) for tgt in targets)
            if bound:
                simple_reset = (
                    _kv_empty_dict_literal(node.value)
                    and ((isinstance(node, ast.Assign)
                          and all(isinstance(tgt, ast.Name)
                                  for tgt in targets))
                         or (isinstance(node, ast.AnnAssign)
                             and isinstance(node.target, ast.Name))))
                if not simple_reset:
                    return False
            if any(_subscript_of(tgt) for tgt in targets):
                return False
            value = getattr(node, 'value', None)
            if value is not None and any(
                    isinstance(sub, ast.Name) and sub.id == collector
                    and isinstance(sub.ctx, ast.Load)
                    for sub in walk_nodes(value)):
                return False
        if isinstance(node, ast.NamedExpr):
            if _binds(node.target) and not _kv_empty_dict_literal(node.value):
                return False
            if any(
                    isinstance(sub, ast.Name) and sub.id == collector
                    and isinstance(sub.ctx, ast.Load)
                    for sub in walk_nodes(node.value)):
                return False
        elif isinstance(node, ast.Delete):
            if (any(_binds(tgt) or _deletes(tgt) for tgt in node.targets)
                    or any(_subscript_of(tgt) for tgt in node.targets)):
                return False
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            if _binds(node.target):
                return False
        elif isinstance(node, (ast.With, ast.AsyncWith)):
            if any(item.optional_vars is not None
                   and _binds(item.optional_vars)
                   for item in node.items):
                return False
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            if any((alias.asname or alias.name.split('.')[0]) == collector
                   for alias in node.names):
                return False
        elif isinstance(node, ast.Call):
            if _kv_value_mutator_call(node, collector):
                return False
            if any(any(isinstance(sub, ast.Name) and sub.id == collector
                       and isinstance(sub.ctx, ast.Load)
                       for sub in walk_nodes(arg))
                   for arg in node.args):
                return False
            if any(any(isinstance(sub, ast.Name) and sub.id == collector
                       and isinstance(sub.ctx, ast.Load)
                       for sub in walk_nodes(kw.value))
                   for kw in node.keywords):
                return False
            func = node.func
            if (isinstance(func, ast.Attribute)
                    and isinstance(func.value, ast.Name)
                    and func.value.id == collector):
                if func.attr in _KV_VALUE_UNSAFE_METHODS:
                    return False
                if func.attr == 'setdefault':
                    holder = parent.get(id(node))
                    if not (isinstance(holder, ast.Attribute)
                            and holder.attr == 'append'
                            and holder.value is node):
                        return False
                    append_call = parent.get(id(holder))
                    if not (isinstance(append_call, ast.Call)
                            and append_call.func is holder):
                        return False
    return True
def _kv_empty_dict_literal(value: ast.AST | None) -> bool:
    if isinstance(value, ast.Dict):
        return not value.keys
    return (isinstance(value, ast.Call)
            and isinstance(value.func, ast.Name)
            and value.func.id == 'dict'
            and not value.args and not value.keywords)
def _lv25_if_branch_at(
        guard: ast.If, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool | None:
    child = node
    cur = parent.get(id(child))
    while cur is not None and cur is not guard:
        child = cur
        cur = parent.get(id(child))
    return branch_truth(guard, child) if cur is guard else None
def _lv25_sequential_siblings(
        owner: ast.AST, child: ast.AST) -> list | None:
    for field in ('body', 'orelse', 'finalbody'):
        value = getattr(owner, field, None)
        if isinstance(value, list) and any(stmt is child for stmt in value):
            return value
    return None
def _lv25_prior_exit_before(
        node: ast.AST, scope: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    cur: ast.AST | None = node
    while cur is not None and cur is not scope:
        owner = parent.get(id(cur))
        if owner is None:
            return False
        siblings = _lv25_sequential_siblings(owner, cur)
        if siblings is not None:
            index = next((i for i, stmt in enumerate(siblings)
                          if stmt is cur), -1)
            if any(_lv25_may_skip_following(stmt)
                   for stmt in siblings[:index]):
                return True
        cur = owner
    return False
def _lv25_same_path_append_evidence(
        node: ast.AST, call: ast.Call, parent: dict[int, ast.AST],
        names: set[str]) -> ast.AST | None:
    scope = nearest_scope(parent, call)
    if scope is None or nearest_scope(parent, node) is not scope:
        return None
    if _lv25_prior_exit_before(call, scope, parent):
        return None
    loops: list[ast.For | ast.AsyncFor] = []
    child: ast.AST = call
    cur = parent.get(id(call))
    while cur is not None and cur is not scope:
        if isinstance(cur, (ast.For, ast.AsyncFor)):
            if not any(stmt is child for stmt in cur.body):
                return None
            loops.append(cur)
        elif isinstance(cur, ast.If):
            append_truth = branch_truth(cur, child)
            node_truth = _lv25_if_branch_at(cur, node, parent)
            if append_truth is None or node_truth != append_truth:
                return None
        elif not isinstance(cur, ast.Expr):
            return None
        child = cur
        cur = parent.get(id(cur))
    if cur is not scope:
        return None
    for loop in loops:
        if (_lv25_iterable_nonempty(loop, loop.iter, names, parent)
                or _lv25_node_in_loop_body(node, loop, parent)):
            continue
        source = _lv25_iter_source_name(
            loop.iter, parent, forward=True)
        if source is None or not _lv25_condition_guarded(node, source, parent):
            return None
    return loops[0] if loops else call
def _lv25_next_binding_scope(
        scope: ast.AST, parent: dict[int, ast.AST]) -> ast.AST | None:
    cur = parent.get(id(scope))
    while cur is not None:
        if isinstance(cur, (*FUNC_SCOPE_NODES, ast.Module)):
            return cur
        cur = parent.get(id(cur))
    return None
_LV25_DECLARATION_MEMO: dict[int, tuple[ast.AST, dict[str, str]]] = {}
_LV25_DECLARATION_MEMO_MAX = 8192
def _lv25_declaration_kinds(scope: ast.AST) -> dict[str, str]:
    """返回 scope 自身 body（不含嵌套函数）声明的名字 -> 声明类型。

    原实现每个 ``(节点, 名字)`` 组合都调一次 ``scan_body_no_funcs`` 重扫
    整个 scope 体，而结果**只取决于 scope 本身**：实测单文件 202,356 次
    调用只对应 213 个唯一 scope，即同一 scope 被重复扫描近千次。

    这是 LV25/LV27 慢的全部原因——外层遍历每个 AST 节点、内层再沿作用域
    链逐层重扫，总代价 O(节点 x 作用域深度 x 体量)。按 scope 身份缓存后
    每次查询降为 O(1)，整体降为 O(总体量)。

    缓存键用 ``id(scope)`` 并带身份校验（``hit[0] is scope``），避免
    ``id`` 被回收后复用时命中错误条目。
    """
    key = id(scope)
    hit = _LV25_DECLARATION_MEMO.get(key)
    if hit is not None and hit[0] is scope:
        return hit[1]
    kinds: dict[str, str] = {}
    body = getattr(scope, 'body', None)
    if isinstance(body, list):
        # 保持原实现的「首次出现优先」语义：后出现的同名声明不覆盖。
        for node in scan_body_no_funcs(body):
            if isinstance(node, ast.Global):
                for bound in node.names:
                    kinds.setdefault(bound, 'global')
            elif isinstance(node, ast.Nonlocal):
                for bound in node.names:
                    kinds.setdefault(bound, 'nonlocal')
    if len(_LV25_DECLARATION_MEMO) >= _LV25_DECLARATION_MEMO_MAX:
        _LV25_DECLARATION_MEMO.clear()
    _LV25_DECLARATION_MEMO[key] = (scope, kinds)
    return kinds
def _lv25_declaration_kind(scope: ast.AST, name: str) -> str | None:
    return _lv25_declaration_kinds(scope).get(name)
def _lv25_nonlocal_owner(
        scope: ast.AST, name: str,
        parent: dict[int, ast.AST]) -> ast.AST | None:
    cur = _lv25_next_binding_scope(scope, parent)
    while cur is not None and not isinstance(cur, ast.Module):
        if (not isinstance(cur, ast.ClassDef)
                and name in scope_local_bindings(cur)):
            return cur
        cur = _lv25_next_binding_scope(cur, parent)
    return None
def _lv25_next_name_resolution_scope(
        scope: ast.AST, parent: dict[int, ast.AST]) -> ast.AST | None:
    cur = _lv25_next_binding_scope(scope, parent)
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        while isinstance(cur, ast.ClassDef):
            cur = _lv25_next_binding_scope(cur, parent)
    return cur
def _lv25_visible_binding_owner(
        node: ast.AST, name: str,
        parent: dict[int, ast.AST]) -> ast.AST | None:
    scope = nearest_scope(parent, node)
    while scope is not None:
        declaration = _lv25_declaration_kind(scope, name)
        if declaration == 'nonlocal':
            return _lv25_nonlocal_owner(scope, name, parent)
        if declaration == 'global':
            cur = scope
            while cur is not None and not isinstance(cur, ast.Module):
                cur = _lv25_next_binding_scope(cur, parent)
            return cur
        if name in scope_local_bindings(scope):
            return scope
        scope = _lv25_next_name_resolution_scope(scope, parent)
    return None
def _lv25_inside_definition_body(
        node: ast.AST, definition: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    body = getattr(definition, 'body', None)
    statements = body if isinstance(body, list) else (
        [body] if body is not None else [])
    return any(_lv25_in_subtree(node, stmt, parent) for stmt in statements)
def _lv25_scope_mutates_outer(
        nested: ast.AST, scope: ast.AST, name: str,
        parent: dict[int, ast.AST], *, body: bool | None = None) -> bool:
    for sub in walk_nodes(nested):
        if sub is nested:
            continue
        if (body is not None
                and isinstance(nested, (ast.FunctionDef, ast.AsyncFunctionDef,
                                        ast.Lambda))
                and _lv25_inside_definition_body(sub, nested, parent) != body):
            continue
        if _lv25_visible_binding_owner(sub, name, parent) is not scope:
            continue
        if _mutates_name(sub, name):
            return True
    return False
def _lv25_deferred_scope_may_mutate(
        scope: ast.AST, name: str,
        parent: dict[int, ast.AST]) -> bool:
    for nested in walk_nodes(scope):
        if nested is scope or not isinstance(nested, FUNC_SCOPE_NODES):
            continue
        if _lv25_scope_mutates_outer(nested, scope, name, parent):
            return True
    return False
def _lv25_local_callable_bindings(
        scope: ast.AST) -> list[tuple[ast.AST, str, ast.AST | None]]:
    body = getattr(scope, 'body', None)
    if not isinstance(body, list):
        return []
    bindings = list(iter_binding_entries(body))
    bindings.extend(
        (node, node.name, None)
        for node, _value in _lv25_definition_bindings(body)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)))
    return bindings
def _lv25_resolve_local_callables(
        name: str, position: tuple[int, int] | None,
        bindings: list[tuple[ast.AST, str, ast.AST | None]],
        visiting: frozenset[tuple[str, int, int]], scope: ast.AST | None,
        parent: dict[int, ast.AST] | None) -> tuple[ast.AST, ...]:
    key = (name, *(position if position is not None else (-1, -1)))
    if key in visiting:
        return ()
    candidates = sorted(
        ((binding, bound, value)
         for binding, bound, value in bindings
         if bound == name and (
             position is None
             or (binding.lineno, binding.col_offset) < position)),
        key=lambda item: (item[0].lineno, item[0].col_offset),
        reverse=True)
    resolved: list[ast.AST] = []
    for binding, _bound, value in candidates:
        current: tuple[ast.AST, ...] = ()
        if isinstance(binding, (ast.FunctionDef, ast.AsyncFunctionDef)):
            current = (binding,)
        elif isinstance(value, ast.Lambda):
            current = (value,)
        elif isinstance(value, ast.Name):
            current = _lv25_resolve_local_callables(
                value.id, (binding.lineno, binding.col_offset), bindings,
                visiting | {key}, scope, parent)
        for callee in current:
            if callee not in resolved:
                resolved.append(callee)
        if (parent is None
                or _binding_dominates_scope(binding, scope, parent)):
            break
    return tuple(resolved)
def _lv25_invoked_local_callable(
        call: ast.Call,
        bindings: list[tuple[ast.AST, str, ast.AST | None]],
        parent: dict[int, ast.AST] | None = None) -> tuple[ast.AST, ...]:
    if isinstance(call.func, ast.Lambda):
        return (call.func,)
    if not isinstance(call.func, ast.Name):
        return ()
    scope = nearest_scope(parent, call) if parent is not None else None
    if parent is not None:
        owner = _lv25_visible_binding_owner(call, call.func.id, parent)
        if owner is None:
            return ()
        scope = owner
        bindings = _lv25_local_callable_bindings(owner)
        if owner is not nearest_scope(parent, call):
            return _lv25_resolve_local_callables(
                call.func.id, None, bindings, frozenset(), scope, parent)
    return _lv25_resolve_local_callables(
        call.func.id, (call.lineno, call.col_offset),
        bindings, frozenset(), scope, parent)
def _lv25_executed_deferred_mutator_between(
        start: ast.AST, name: str, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    scope = nearest_scope(parent, node)
    if scope is None:
        return False
    start_pos = (start.lineno, start.col_offset)
    end_pos = (node.lineno, node.col_offset)
    for nested in walk_nodes(scope):
        if nested is scope or not isinstance(nested, FUNC_SCOPE_NODES):
            continue
        definition_pos = (nested.lineno, nested.col_offset)
        defined_between = start_pos < definition_pos < end_pos
        if isinstance(nested, ast.ClassDef):
            if (defined_between and _lv25_scope_mutates_outer(
                    nested, scope, name, parent)):
                return True
            continue
        if not isinstance(nested, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.Lambda)):
            continue
        if (defined_between and _lv25_scope_mutates_outer(
                nested, scope, name, parent, body=False)):
            return True
    bindings = _lv25_local_callable_bindings(scope)
    for call in walk_nodes(scope):
        if not isinstance(call, ast.Call):
            continue
        call_pos = (call.lineno, call.col_offset)
        if (not start_pos < call_pos < end_pos
                or nearest_scope(parent, call) is not scope):
            continue
        callees = _lv25_invoked_local_callable(call, bindings, parent)
        if any(_lv25_scope_mutates_outer(
                callee, scope, name, parent, body=True)
               for callee in callees):
            return True
    return False
def _lv25_growth_stmt_kind(stmt: ast.AST, name: str) -> str | None:
    """``stmt`` 对 ``name`` 的增长形态：``'append'``（必然增长）、``'grow'``
    （需再证明实参 / 右值非空）或 ``None``。只做廉价判定，不含递归求值。

    ``append`` 保留原有的下标 / ``setdefault`` 接收者形态；其余增长方法只认
    直接作用于 ``name`` 的调用。
    """
    if isinstance(stmt, ast.AugAssign):
        if (isinstance(stmt.op, ast.Add)
                and isinstance(stmt.target, ast.Name)
                and stmt.target.id == name):
            return 'grow'
        return None
    if not (isinstance(stmt, ast.Call)
            and isinstance(stmt.func, ast.Attribute)):
        return None
    if stmt.func.attr == 'append':
        info = _collector_target(stmt)
        return 'append' if info is not None and info[0] == name else None
    if (stmt.func.attr in _LV25_GROWTH_METHODS
            and isinstance(stmt.func.value, ast.Name)
            and stmt.func.value.id == name):
        return 'grow'
    return None
def _lv25_growth_proven(
        stmt: ast.AST, name: str, guarded: set[str],
        parent: dict[int, ast.AST], kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]]) -> bool:
    """``'grow'`` 形态是否必然让容器非空。

    ``append``/``insert``/``add``/``setdefault`` 无论实参如何都多出一个元素
    （``setdefault`` 命中已存在的键时容器本就非空）；``extend``/``update`` 与
    ``x += value`` 可能收到空容器，要求每个实参 / 右值都已知非空。
    """
    if isinstance(stmt, ast.AugAssign):
        return _lv25_value_known_nonempty(
            stmt, stmt.value, guarded, parent, kv_collectors, visiting)
    attr = stmt.func.attr
    if attr not in _LV25_GROWTH_METHODS_NEEDING_NONEMPTY_ARG:
        return True
    values = [*stmt.args, *(kw.value for kw in stmt.keywords)]
    if not values or any(isinstance(arg, ast.Starred) for arg in stmt.args):
        return False
    return all(
        _lv25_value_known_nonempty(
            stmt, value, guarded, parent, kv_collectors, visiting)
        for value in values)
def _lv25_collector_evidence(
        node: ast.AST, name: str, guarded: set[str],
        parent: dict[int, ast.AST], kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]] = _EMPTY_VISITS) -> ast.AST | None:
    scope = nearest_scope(parent, node)
    if scope is None or _lv25_deferred_scope_may_mutate(
            scope, name, parent):
        return None
    limit = (node.lineno, node.col_offset)
    for stmt in walk_nodes(scope):
        kind = _lv25_growth_stmt_kind(stmt, name)
        if kind is None:
            continue
        call = stmt
        # 位置 / 作用域过滤必须先于实参求值：实参可能引用使用点之后的增长语句，
        # 先求值会沿同一条 (节点, 名字) 链无限递归。
        if (call.lineno, call.col_offset) >= limit:
            continue
        if nearest_scope(parent, call) is not scope:
            continue
        if (kind == 'grow' and not _lv25_growth_proven(
                call, name, guarded, parent, kv_collectors, visiting)):
            continue
        for_node = _enclosing_for_node(call, parent)
        evidence: ast.AST | None = None
        if for_node is None:
            if _lv25_straight_line_append(call, name, scope, parent):
                evidence = call
            else:
                evidence = _lv25_same_path_append_evidence(
                    node, call, parent, guarded)
        else:
            if (for_node.lineno, for_node.col_offset) >= limit:
                continue
            if nearest_scope(parent, for_node) is not scope:
                continue
            if _lv25_append_execution_guaranteed(
                    call, name, guarded, parent):
                evidence = for_node
            else:
                evidence = _lv25_same_path_append_evidence(
                    node, call, parent, guarded)
        if (evidence is not None
                and not _binding_invalidated_since(
                    evidence, name, node, parent)):
            return evidence
    return None
def _lv25_in_subtree(
        node: ast.AST, container: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    cur: ast.AST | None = node
    while cur is not None:
        if cur is container:
            return True
        cur = parent.get(id(cur))
    return False
def _lv25_callee_mutates_content(callee: ast.AST, param: str) -> bool:
    body = getattr(callee, 'body', None)
    if isinstance(callee, ast.Lambda):
        body = [body]
    if not isinstance(body, list):
        return False
    for candidate in scan_body_no_funcs(body):
        if not _mutates_name(candidate, param):
            continue
        if isinstance(candidate, (ast.Call, ast.AugAssign)):
            return True
        if isinstance(candidate, ast.Assign) and any(
                isinstance(target, ast.Subscript)
                for target in candidate.targets):
            return True
        if isinstance(candidate, ast.Delete) and any(
                isinstance(target, ast.Subscript)
                for target in candidate.targets):
            return True
    return False
def _lv25_local_mutator_call_between(
        start: ast.AST, name: str, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    scope = nearest_scope(parent, node)
    body = getattr(scope, 'body', None)
    if scope is None or not isinstance(body, list):
        return False
    bindings = _lv25_local_callable_bindings(scope)
    start_pos = (start.lineno, start.col_offset)
    end_pos = (node.lineno, node.col_offset)
    for call in walk_nodes(scope):
        if not isinstance(call, ast.Call):
            continue
        position = (call.lineno, call.col_offset)
        if not start_pos < position < end_pos:
            continue
        if nearest_scope(parent, call) is not scope:
            continue
        if (_lv25_in_subtree(call, start, parent)
                or _lv25_in_subtree(call, node, parent)):
            continue
        callees = _lv25_invoked_local_callable(call, bindings, parent)
        for callee in callees:
            for param in param_names(callee):
                actual = _actual_arg(call, callee, param, 0)
                if (isinstance(actual, ast.Name) and actual.id == name
                        and _lv25_callee_mutates_content(callee, param)):
                    return True
    return False
def _lv25_aligned_name_values(
        target: ast.AST, value: ast.AST) -> list[tuple[str, ast.AST]]:
    if isinstance(target, ast.Name):
        return [(target.id, value)]
    pairs = _aligned_assignment_pairs(target, value)
    if pairs is None:
        return []
    return [pair
            for subtarget, subvalue in pairs
            for pair in _lv25_aligned_name_values(subtarget, subvalue)]
def _lv25_alias_binding(
        node: ast.AST) -> list[tuple[list[str], ast.AST]] | None:
    if isinstance(node, ast.Assign):
        targets = node.targets
        value = node.value
    elif ((isinstance(node, ast.AnnAssign) and node.value is not None)
          or isinstance(node, ast.NamedExpr)):
        targets = [node.target]
        value = node.value
    else:
        return None
    pairs = [pair
             for target in targets
             for pair in _lv25_aligned_name_values(target, value)]
    return [([name], item) for name, item in pairs] if pairs else None
def _lv25_loop_alias_names(
        loop: ast.For | ast.AsyncFor, aliases: set[str]) -> set[str]:
    if (not isinstance(loop.iter, (ast.List, ast.Tuple))
            or any(isinstance(elt, ast.Starred) for elt in loop.iter.elts)):
        return set()
    return {target
            for elt in loop.iter.elts
            for target, value in _lv25_aligned_name_values(loop.target, elt)
            if isinstance(value, ast.Name) and value.id in aliases}
def _lv25_alias_mutator_between(
        start: ast.AST, name: str, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    scope = nearest_scope(parent, node)
    body = getattr(scope, 'body', None)
    if (scope is None or nearest_scope(parent, start) is not scope
            or not isinstance(body, list)):
        return False
    start_pos = (start.lineno, start.col_offset)
    end_pos = (node.lineno, node.col_offset)
    bindings = None
    mutated = False
    def _update(aliases: set[str], binding: tuple[list[str], ast.AST]) -> set[str]:
        targets, value = binding
        source_alias = isinstance(value, ast.Name) and value.id in aliases
        updated = set(aliases)
        if name in targets and not source_alias:
            updated = {name, *targets}
            if isinstance(value, ast.Name):
                updated.add(value.id)
        else:
            updated.difference_update(
                target for target in targets if target != name)
            if source_alias:
                updated.update(targets)
        return updated
    def _merge(*states: set[str] | None) -> set[str] | None:
        live = [state for state in states if state is not None]
        if not live:
            return None
        merged: set[str] = set()
        for state in live:
            merged.update(state)
        return merged
    def _quiet_alias_value(value: ast.AST, aliases: set[str]) -> bool:
        if isinstance(value, ast.Name):
            return value.id in aliases
        try:
            ast.literal_eval(value)
        except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):
            pass
        else:
            return True
        return (isinstance(value, (ast.List, ast.Tuple))
                and all(not isinstance(elt, ast.Starred)
                        and _quiet_alias_value(elt, aliases)
                        for elt in value.elts))
    def _quiet_alias_statement(stmt: ast.stmt, aliases: set[str]) -> bool:
        binding = _lv25_alias_binding(stmt)
        return bool(binding) and all(
            _quiet_alias_value(value, aliases)
            for _targets, value in binding)
    def _events(root: ast.AST, aliases: set[str]) -> set[str]:
        nonlocal bindings, mutated
        candidates = sorted(
            walk_nodes(root),
            key=lambda candidate: (
                getattr(candidate, 'lineno', -1),
                getattr(candidate, 'col_offset', -1)))
        for candidate in candidates:
            position = (getattr(candidate, 'lineno', -1),
                        getattr(candidate, 'col_offset', -1))
            if (position >= end_pos
                    or nearest_scope(parent, candidate) is not scope):
                continue
            if isinstance(candidate, ast.NamedExpr):
                binding = _lv25_alias_binding(candidate)
                if binding is not None:
                    for item in binding:
                        aliases = _update(aliases, item)
                    continue
            if not start_pos < position:
                continue
            if any(_mutates_name(candidate, alias)
                   for alias in aliases if alias != name):
                mutated = True
                return aliases
            if len(aliases) == 1 or not isinstance(candidate, ast.Call):
                continue
            if bindings is None:
                bindings = _lv25_local_callable_bindings(scope)
            callees = _lv25_invoked_local_callable(
                candidate, bindings, parent)
            for callee in callees:
                if any(alias != name and _lv25_scope_mutates_outer(
                        callee, scope, alias, parent, body=True)
                       for alias in aliases):
                    mutated = True
                    return aliases
                for param in param_names(callee):
                    actual = _actual_arg(candidate, callee, param, 0)
                    if (isinstance(actual, ast.Name) and actual.id != name
                            and actual.id in aliases
                            and _lv25_callee_mutates_content(callee, param)):
                        mutated = True
                        return aliases
        return aliases
    def _block(stmts: list[ast.stmt], aliases: set[str],
               exception_aliases: set[str] | None = None) -> set[str] | None:
        for stmt in stmts:
            if (stmt.lineno, stmt.col_offset) >= end_pos or mutated:
                break
            if (exception_aliases is not None
                    and not _quiet_alias_statement(stmt, aliases)):
                exception_aliases.update(aliases)
            limited = _lv25_in_subtree(node, stmt, parent)
            aliases = _statement(stmt, aliases, limited, exception_aliases)
            if aliases is None or limited:
                return aliases
        return aliases
    def _statement(
            stmt: ast.stmt, aliases: set[str], limited: bool,
            exception_aliases: set[str] | None = None) -> set[str] | None:
        if isinstance(stmt, ast.If):
            aliases = _events(stmt.test, aliases)
            branches = (stmt.body, stmt.orelse)
            if limited:
                if _lv25_in_subtree(node, stmt.test, parent):
                    return aliases
                for branch in branches:
                    if any(_lv25_in_subtree(node, child, parent)
                           for child in branch):
                        return _block(branch, aliases, exception_aliases)
                return aliases
            body_state = _block(stmt.body, set(aliases), exception_aliases)
            else_state = (_block(stmt.orelse, set(aliases), exception_aliases)
                          if stmt.orelse else set(aliases))
            return _merge(body_state, else_state)
        if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            source = stmt.test if isinstance(stmt, ast.While) else stmt.iter
            aliases = _events(source, aliases)
            if isinstance(stmt, (ast.For, ast.AsyncFor)):
                aliases.update(_lv25_loop_alias_names(stmt, aliases))
            if limited:
                if _lv25_in_subtree(node, source, parent):
                    return aliases
                for branch in (stmt.body, stmt.orelse):
                    if any(_lv25_in_subtree(node, child, parent)
                           for child in branch):
                        return _block(branch, aliases, exception_aliases)
                return aliases
            body_state = _block(stmt.body, set(aliases), exception_aliases)
            else_state = _block(stmt.orelse, set(aliases), exception_aliases)
            return _merge(set(aliases), body_state, else_state)
        if isinstance(stmt, TRY_NODES):
            handler_aliases = set(aliases)
            normal = _block(stmt.body, set(aliases), handler_aliases)
            if exception_aliases is not None:
                exception_aliases.update(handler_aliases)
            if normal is not None and stmt.orelse:
                normal = _block(stmt.orelse, normal, exception_aliases)
            handlers = [_block(handler.body, set(handler_aliases),
                               exception_aliases)
                        for handler in stmt.handlers]
            merged = _merge(normal, *handlers)
            if merged is not None and stmt.finalbody:
                merged = _block(stmt.finalbody, merged, exception_aliases)
            return merged
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            for item in stmt.items:
                aliases = _events(item.context_expr, aliases)
            return _block(stmt.body, aliases, exception_aliases)
        if isinstance(stmt, ast.Match):
            aliases = _events(stmt.subject, aliases)
            states = [_block(case.body, set(aliases), exception_aliases)
                      for case in stmt.cases]
            if not any(case.guard is None and _pattern_irrefutable(case.pattern)
                       for case in stmt.cases):
                states.append(set(aliases))
            return _merge(*states)
        binding = _lv25_alias_binding(stmt)
        if binding is not None:
            aliases = _events(stmt.value, aliases)
            for item in binding:
                aliases = _update(aliases, item)
            return aliases
        aliases = _events(stmt, aliases)
        if isinstance(stmt, (ast.Return, ast.Raise)):
            return None
        return aliases
    _block(body, {name})
    return mutated
def _binding_invalidated_since(
        start: ast.AST, name: str, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    return (
        _binding_invalidated_since_base(start, name, node, parent)
        or _lv25_executed_deferred_mutator_between(
            start, name, node, parent)
        or _lv25_local_mutator_call_between(start, name, node, parent)
        or _lv25_alias_mutator_between(start, name, node, parent)
    )
def _lv25_loop_control_skips_node(
        control: ast.AST, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    if not isinstance(control, (ast.Break, ast.Continue)):
        return False
    loop = parent.get(id(control))
    while loop is not None and not isinstance(
            loop, (ast.For, ast.AsyncFor, ast.While)):
        if isinstance(loop, (*FUNC_SCOPE_NODES, ast.Module)):
            return False
        loop = parent.get(id(loop))
    if loop is None:
        return False
    child = _child_under(loop, node, parent)
    if (isinstance(control, ast.Break)
            and any(child is stmt for stmt in loop.orelse)):
        return True
    return (_lv25_node_in_loop_body(node, loop, parent)
            and (control.lineno, control.col_offset)
            < (node.lineno, node.col_offset))
def _lv25_control_reaches_node_in_finally(
        control: ast.AST, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    cur = control
    while cur is not None:
        owner = parent.get(id(cur))
        if owner is None:
            return False
        if isinstance(owner, TRY_NODES):
            control_child = _child_under(owner, control, parent)
            node_child = _child_under(owner, node, parent)
            node_in_final = any(
                node_child is stmt for stmt in owner.finalbody)
            control_in_final = any(
                control_child is stmt for stmt in owner.finalbody)
            if node_in_final and not control_in_final:
                return True
        cur = owner
    return False
def _lv25_block_has_nonempty_assignment(
        stmts: list[ast.stmt], name: str,
        parent: dict[int, ast.AST], guarded: set[str], kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]], use_node: ast.AST,
        initial: bool = False) -> bool:
    nonempty = initial
    for stmt in stmts:
        if isinstance(stmt, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
            if _lv25_control_reaches_node_in_finally(
                    stmt, use_node, parent):
                return nonempty
            if (isinstance(stmt, (ast.Return, ast.Raise))
                    or _lv25_loop_control_skips_node(stmt, use_node, parent)):
                return True
            return nonempty
        shape = _lv25_assign_shape(stmt)
        if shape is not None and isinstance(shape[0], ast.Name) and shape[0].id == name:
            nonempty = _lv25_value_known_nonempty(
                stmt, shape[1], guarded, parent, kv_collectors, visiting)
            continue
        if (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Call)
                and isinstance(stmt.value.func, ast.Attribute)
                and stmt.value.func.attr == 'append'
                and isinstance(stmt.value.func.value, ast.Name)
                and stmt.value.func.value.id == name):
            nonempty = True
            continue
        if isinstance(stmt, ast.If):
            body_safe = _lv25_block_has_nonempty_assignment(
                stmt.body, name, parent, guarded, kv_collectors,
                visiting, use_node, initial=nonempty)
            else_safe = _lv25_block_has_nonempty_assignment(
                stmt.orelse, name, parent, guarded, kv_collectors,
                visiting, use_node, initial=nonempty)
            nonempty = body_safe and else_safe
            continue
        if isinstance(stmt, ast.Match):
            cases_safe = all(
                _lv25_block_has_nonempty_assignment(
                    case.body, name, parent, guarded, kv_collectors,
                    visiting, use_node, initial=nonempty)
                for case in stmt.cases)
            exhaustive = any(
                case.guard is None and _pattern_irrefutable(case.pattern)
                for case in stmt.cases)
            nonempty = cases_safe and (nonempty or exhaustive)
            continue
        if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While,
                             ast.Try, ast.With, ast.AsyncWith)):
            if not nonempty or any(
                    _mutates_name(sub, name) for sub in walk_nodes(stmt)):
                return False
            continue
        if any(_mutates_name(sub, name) for sub in walk_nodes(stmt)):
            nonempty = False
    return nonempty
def _lv25_try_all_paths_nonempty(
        try_node: ast.AST, name: str, parent: dict[int, ast.AST],
        guarded: set[str], kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]], use_node: ast.AST) -> bool:
    def _safe(block: list[ast.stmt]) -> bool:
        return _lv25_block_has_nonempty_assignment(
            block, name, parent, guarded, kv_collectors,
            visiting, use_node)
    body = getattr(try_node, 'body', [])
    orelse = getattr(try_node, 'orelse', [])
    handlers = getattr(try_node, 'handlers', [])
    normal_path = _safe(body) or (bool(orelse) and _safe(orelse))
    return normal_path and all(_safe(handler.body) for handler in handlers)
def _lv25_match_all_paths_nonempty(
        match: ast.Match, name: str, parent: dict[int, ast.AST],
        guarded: set[str], kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]], use_node: ast.AST) -> bool:
    cases = match.cases
    if not cases or not any(
            case.guard is None and _pattern_irrefutable(case.pattern)
            for case in cases):
        return False
    return all(
        _lv25_block_has_nonempty_assignment(
            case.body, name, parent, guarded, kv_collectors,
            visiting, use_node)
        for case in cases)
def _lv25_assignment_dominates(
        assignment: ast.AST, name: str, node: ast.AST,
        parent: dict[int, ast.AST], guarded: set[str], kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]]) -> bool:
    chain = _scope_chain(node, parent)
    scope = _binding_scope(node, name, parent)
    if (scope is None or not chain
            or _binding_scope(assignment, name, parent) is not scope):
        return False
    if (scope is not chain[0]
            and not (isinstance(chain[0], ast.ClassDef)
                     and isinstance(scope, ast.Module))):
        return False
    target_name = name
    cur: ast.AST = assignment
    while cur is not scope:
        owner = parent.get(id(cur))
        if owner is None:
            return False
        if owner is scope:
            return True
        if isinstance(owner, ast.If):
            truth = branch_truth(owner, cur)
            child = _child_under(owner, node, parent)
            if truth is None:
                return False
            if child is None:
                if not (_lv25_block_has_nonempty_assignment(
                        owner.body, target_name, parent, guarded,
                        kv_collectors, visiting, node)
                        and _lv25_block_has_nonempty_assignment(
                            owner.orelse, target_name, parent, guarded,
                            kv_collectors, visiting, node)):
                    return False
            elif branch_truth(owner, child) != truth:
                return False
        elif isinstance(owner, (ast.For, ast.AsyncFor, ast.While)):
            child = _child_under(owner, node, parent)
            if child is None:
                if (not _loop_guarantees_once(owner, parent)
                        or not owner.body or owner.body[0] is not cur):
                    return False
            elif not any(child is stmt for stmt in owner.body):
                return False
        elif isinstance(owner, (ast.With, ast.AsyncWith)):
            child = _child_under(owner, node, parent)
            if child is None or not any(child is stmt for stmt in owner.body):
                return False
        elif isinstance(owner, TRY_NODES):
            child = _child_under(owner, node, parent)
            in_final = any(cur is stmt for stmt in owner.finalbody)
            if in_final:
                if child is not None and not any(
                        child is stmt for stmt in owner.finalbody):
                    return False
                cur = owner
                continue
            if child is None:
                if any(cur is stmt for stmt in owner.body):
                    if not owner.handlers:
                        return True
                    return all(
                        _lv25_block_has_nonempty_assignment(
                            handler.body, target_name, parent, guarded,
                            kv_collectors, visiting, node)
                        for handler in owner.handlers)
                if any(cur is stmt for stmt in owner.orelse):
                    return bool(owner.handlers) and all(
                        _lv25_block_has_nonempty_assignment(
                            handler.body, target_name, parent, guarded,
                            kv_collectors, visiting, node)
                        for handler in owner.handlers)
                return False
            if (any(cur is stmt for stmt in owner.body)
                    and (any(child is stmt for stmt in owner.body)
                         or any(child is stmt for stmt in owner.orelse))):
                cur = owner
                continue
            if (any(cur is stmt for stmt in owner.orelse)
                    and any(child is stmt for stmt in owner.orelse)):
                cur = owner
                continue
            if cur is child:
                cur = owner
                continue
            return False
        elif isinstance(owner, ast.ExceptHandler):
            if _lv25_in_subtree(node, owner, parent):
                cur = owner
                continue
            try_owner = parent.get(id(owner))
            if (isinstance(try_owner, TRY_NODES)
                    and not _lv25_in_subtree(node, try_owner, parent)):
                return _lv25_try_all_paths_nonempty(
                    try_owner, target_name, parent, guarded,
                    kv_collectors, visiting, node)
            return False
        elif isinstance(owner, ast.Match):
            child = _child_under(owner, node, parent)
            if (child is None or child is not cur) and not (
                    _lv25_match_all_paths_nonempty(
                        owner, target_name, parent, guarded,
                        kv_collectors, visiting, node)):
                return False
            cur = owner
            continue
        elif isinstance(owner, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            return False
        cur = owner
    return True
def _lv25_comprehension_guard(
        node: ast.AST, name: str,
        parent: dict[int, ast.AST]) -> bool | None:
    cur: ast.AST | None = node
    prev: ast.AST = node
    gen_child: dict[int, ast.AST] = {}
    while cur is not None:
        if isinstance(cur, ast.comprehension):
            gen_child[id(cur)] = prev
        elif isinstance(cur, _CONTAINER_COMP_NODES):
            guards = _comp_prior_guards(cur, prev, gen_child)
            if any(
                    _nonempty_holds(guard, name, True, parent)
                    and not _binding_invalidated_since(
                        guard, name, node, parent)
                    for guard in guards):
                return True
            if name in _lv09_comp_shadowed_names(cur, prev, gen_child):
                return False
        prev = cur
        cur = parent.get(id(cur))
    return None
def _lv25_guarded_at(
        node: ast.AST, name: str, guarded: set[str],
        parent: dict[int, ast.AST], kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]] = _EMPTY_VISITS) -> bool:
    key = (id(node), name)
    if key in visiting:
        return False
    return _lv25_guarded_at_impl(
        node, name, guarded, parent, kv_collectors,
        visiting | {key})
def _lv25_guarded_at_impl(
        node: ast.AST, name: str, guarded: set[str],
        parent: dict[int, ast.AST], kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]]) -> bool:
    comprehension = _lv25_comprehension_guard(node, name, parent)
    if comprehension is not None:
        return comprehension
    # 最近一次赋值若在 try 体 / 条件分支 / 不保证执行的循环体里，它并不支配使用点
    # （``x = [9]; try: x = [1] except Exception: pass; len(x)``），此时更早的
    # 非空初始化仍然有效；按位置从近到远逐个尝试，每个候选独立校验
    # 「已知非空 + 支配使用点 + 其间无收缩性变更」。
    for latest in _assignment_candidates(node, name, parent):
        value = latest.value
        if not (_lv25_value_known_nonempty(
                latest, value, guarded, parent, kv_collectors,
                visiting)
                and _lv25_assignment_dominates(
                    latest, name, node, parent, guarded, kv_collectors,
                    visiting)
                and not _binding_invalidated_since(
                    latest, name, node, parent)):
            continue
        if isinstance(value, ast.Name) and value.id != name:
            return (_lv25_guarded_at(
                        latest, value.id, guarded, parent,
                        kv_collectors, visiting)
                    or _lv25_condition_guarded(
                        latest, value.id, parent))
        return True
    evidence = (_lv25_collector_evidence(
                    node, name, guarded, parent, kv_collectors, visiting)
                or _kv_value_evidence(node, name, kv_collectors, parent))
    return (evidence is not None
            and not _binding_invalidated_since(evidence, name, node, parent))
def _lv25_deferred_scope_body(scope: ast.AST, child: ast.AST) -> bool:
    if isinstance(scope, ast.Lambda):
        return child is scope.body
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return any(child is stmt for stmt in scope.body)
    return False
def _lv25_comp_source_nonempty(
        comp: ast.AST, path_child: ast.AST,
        gen_child: dict[int, ast.AST], name: str,
        parent: dict[int, ast.AST]) -> bool:
    gens = list(getattr(comp, 'generators', []))
    if not gens:
        return False
    if _lv09_comp_is_output_position(comp, path_child):
        indices = range(len(gens))
    elif isinstance(path_child, ast.comprehension):
        index = next((i for i, gen in enumerate(gens)
                      if gen is path_child), -1)
        if index < 0:
            return False
        if gen_child.get(id(path_child)) is path_child.iter:
            indices = range(index)
        else:
            indices = range(index + 1)
    else:
        return False
    return any(
        _lv25_iter_source_name(gens[i].iter, parent) == name
        for i in indices)
def _lv25_in_loop_source_body(node: ast.AST, name: str,
                              parent: dict) -> bool:
    child = node
    cur = parent.get(id(child))
    gen_child: dict[int, ast.AST] = {}
    while cur is not None:
        if _lv25_deferred_scope_body(cur, child):
            return False
        if isinstance(cur, ast.comprehension):
            gen_child[id(cur)] = child
        if isinstance(cur, _CONTAINER_COMP_NODES):
            if name in _lv09_comp_shadowed_names(cur, child, gen_child):
                return False
            if _lv25_comp_source_nonempty(
                    cur, child, gen_child, name, parent):
                return True
        if isinstance(cur, (ast.For, ast.AsyncFor)):
            in_body = any(id(child) == id(stmt) for stmt in cur.body)
            if in_body and _lv25_iter_source_name(cur.iter, parent) == name:
                if any(bound == name
                       for bound, _lineno in target_store_names(
                           cur.target, 0)):
                    return False
                latest = _latest_assignment(node, name, parent)
                loop_pos = (cur.lineno, cur.col_offset)
                if (latest is not None
                        and (latest.lineno, latest.col_offset) > loop_pos
                        and not (_nonempty_literal(latest.value)
                                 or _range_nonempty(
                                     latest, latest.value, parent))):
                    return False
                return not _binding_invalidated_since(
                    cur, name, node, parent)
        child = cur
        cur = parent.get(id(child))
    return False
def _lv25_condition_guarded(node: ast.AST, name: str,
                            parents: dict[int, ast.AST]) -> bool:
    comprehension = _lv25_comprehension_guard(node, name, parents)
    if comprehension is not None:
        return comprehension
    return _guarded_on_path(
        node, parents,
        lambda test, truth: _nonempty_holds(test, name, truth, parents),
        lambda guard: _binding_invalidated_since(guard, name, node, parents))
def _lv25_private_param_guarded(
        tree: ast.AST, fn: ast.AST, param: str,
        guarded: set[str], parent: dict[int, ast.AST],
        kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]]) -> bool:
    callable_info = _private_callable(fn, parent)
    if callable_info is None:
        return False
    key = (id(fn), param)
    if key in visiting:
        return False
    name, drop, kind = callable_info
    if _length_callable_reference_escapes(tree, name, kind, parent):
        return False
    calls = _matching_calls(tree, name, kind)
    if not calls:
        return False
    nested = visiting | {key}
    for call in calls:
        actual = _actual_arg(call, fn, param, drop)
        if actual is None:
            return False
        if _lv25_value_known_nonempty(
                call, actual, guarded, parent, kv_collectors):
            continue
        if not isinstance(actual, ast.Name):
            return False
        caller = _enclosing_function(call, parent)
        if (caller is None or actual.id not in param_names(caller)
                or not _lv25_private_param_guarded(
                    tree, caller, actual.id, guarded, parent,
                    kv_collectors, nested)):
            return False
    return True
def _lv25_interproc_guarded(
        tree: ast.AST, node: ast.AST, name: str, guarded: set[str],
        parent: dict[int, ast.AST],
        kv_collectors: set[str]) -> bool:
    fn = _enclosing_function(node, parent)
    if fn is None or name not in param_names(fn):
        return False
    _chain, lambda_shadowed, comp_shadowed, _class_hidden = (
        _lv09_ancestor_chain(node, parent))
    if name in lambda_shadowed | comp_shadowed:
        return False
    return _lv25_private_param_guarded(
        tree, fn, name, guarded, parent, kv_collectors, _EMPTY_VISITS)
def _length_callable_reference_escapes(
        tree: ast.AST, name: str, kind: str,
        parent: dict[int, ast.AST]) -> bool:
    for ref in walk_nodes(tree):
        is_name = (kind in {'function', 'constructor'}
                   and isinstance(ref, ast.Name) and ref.id == name)
        is_attribute = (kind in {'method', 'constructor'}
                        and isinstance(ref, ast.Attribute)
                        and ref.attr == name)
        if not (is_name or is_attribute):
            continue
        holder = parent.get(id(ref))
        if isinstance(holder, ast.Call) and holder.func is ref:
            continue
        return True
    return False
def _lv25_len_operand_arg(call: ast.AST) -> ast.expr | None:
    arg = _len_arg_expr(call)
    if arg is not None:
        return arg
    if (isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
            and call.func.id == 'len' and len(call.args) == 1
            and not call.keywords
            and not isinstance(call.args[0], ast.Starred)
            and isinstance(call.args[0], (ast.BinOp, ast.Call))):
        return call.args[0]
    return None
def _lv25_violates(node: ast.AST, guarded: set[str],
                   parent: dict, tree: ast.AST,
                   kv_collectors: set[str],
                   shadow_cache: dict[tuple[int, frozenset[int]], set[str]]
                   ) -> str | None:
    operands = _lv25_div_operands(node)
    if operands is None:
        return None
    arg = _lv25_len_operand_arg(operands[1])
    if arg is None:
        return None
    if shadowed_binding_at(node, 'len', parent, shadow_cache):
        return None
    if not isinstance(arg, ast.Name):
        return _lv25_unnamed_len_violation(
            node, arg, guarded, parent, kv_collectors)
    arg_name = arg.id
    if _lv25_guarded_at(
            node, arg_name, guarded, parent, kv_collectors):
        return None
    if _lv25_in_loop_source_body(node, arg_name, parent):
        return None
    if _lv25_condition_guarded(node, arg_name, parent):
        return None
    if _lv25_interproc_guarded(
            tree, node, arg_name, guarded, parent, kv_collectors):
        return None
    return arg_name
def _lv25_unnamed_len_violation(
        node: ast.AST, arg: ast.expr, guarded: set[str],
        parent: dict[int, ast.AST],
        kv_collectors: set[str]) -> str | None:
    if isinstance(arg, ast.Subscript):
        invalidated = lambda guard: _expression_guard_invalidated(
            guard, arg, node, parent)
        if (_lv25_slice_nonempty(
                node, arg, guarded, parent, kv_collectors)
                or _expression_condition_guarded(
                    node, arg, parent, invalidated)):
            return None
        return ast.unparse(arg)
    length = _lv25_known_length(node, arg, parent)
    if length is None:
        dynamic_ctor = (
            isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name)
            and arg.func.id in _LV25_CONTAINER_CTORS
            and len(arg.args) == 1 and not arg.keywords
            and not isinstance(arg.args[0], ast.Starred))
        if not dynamic_ctor or _lv25_value_known_nonempty(
                node, arg, guarded, parent, kv_collectors):
            return None
    elif length > 0:
        return None
    return ast.unparse(arg)
def _lv25_len_lower_bound(
        compare: ast.Compare, name: str, truth: bool,
        parent: dict[int, ast.AST] | None = None) -> int | None:
    parsed = _len_const_compare(compare, name, parent)
    if parsed is None:
        return None
    op, n = parsed
    if isinstance(op, ast.Eq):
        if truth:
            return n
        return 1 if n == 0 else None
    if isinstance(op, ast.NotEq):
        if not truth:
            return n
        return 1 if n == 0 else None
    if isinstance(op, ast.Gt):
        return n + 1 if truth else None
    if isinstance(op, ast.GtE):
        return n if truth else None
    if isinstance(op, ast.Lt):
        return None if truth else n
    if isinstance(op, ast.LtE):
        return None if truth else n + 1
    return None
def _lv25_len_at_least_holds(
        test: ast.AST, name: str, truth: bool, minimum: int,
        parent: dict[int, ast.AST] | None = None) -> bool:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _lv25_len_at_least_holds(
            test.operand, name, not truth, minimum, parent)
    if isinstance(test, ast.Compare):
        bound = _lv25_len_lower_bound(test, name, truth, parent)
        return bound is not None and bound >= minimum
    if isinstance(test, ast.BoolOp):
        if isinstance(test.op, ast.And) and truth:
            return any(_lv25_len_at_least_holds(v, name, True, minimum, parent)
                       for v in test.values)
        if isinstance(test.op, ast.Or) and not truth:
            return any(_lv25_len_at_least_holds(v, name, False, minimum, parent)
                       for v in test.values)
    return False
def _lv25_len_at_least_guarded(
        node: ast.AST, name: str, minimum: int,
        parents: dict[int, ast.AST]) -> bool:
    return _guarded_on_path(
        node, parents,
        lambda test, truth: _lv25_len_at_least_holds(
            test, name, truth, minimum, parents),
        lambda guard: _binding_invalidated_since(
            guard, name, node, parents))
def _lv25_split_index_bounds(
        node: ast.AST, name: str, source: str,
        parent: dict[int, ast.AST], names: set[str],
        kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]]) -> tuple[int, int] | None:
    assignment = _latest_assignment(node, name, parent)
    if assignment is None or not _lv25_assignment_dominates(
            assignment, name, node, parent, names, kv_collectors,
            visiting):
        return None
    value = assignment.value
    if (not isinstance(value, ast.Call) or not isinstance(value.func, ast.Name)
            or value.func.id != 'max'
            or shadowed_binding_at(node, 'max', parent, {})
            or len(value.args) != 2 or value.keywords):
        return None
    constant = _resolved_int(node, value.args[0], parent)
    dynamic = value.args[1]
    if (constant is None or not isinstance(dynamic, ast.BinOp)
            or not isinstance(dynamic.op, ast.Sub)):
        return None
    left = dynamic.left
    if (not isinstance(left, ast.Call) or not isinstance(left.func, ast.Name)
            or left.func.id != 'len' or len(left.args) != 1
            or not isinstance(left.args[0], ast.Name)
            or left.args[0].id != source):
        return None
    subtract = _resolved_int(node, dynamic.right, parent)
    if subtract is None or subtract < 1:
        return None
    return constant, subtract
def _lv25_comprehension_nonempty(
        node: ast.AST, value: ast.AST, names: set[str],
        parent: dict[int, ast.AST],
        kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]] = _EMPTY_VISITS) -> bool:
    if not isinstance(value, (ast.ListComp, ast.SetComp, ast.DictComp)):
        return False
    if not value.generators or any(gen.ifs for gen in value.generators):
        return False
    for gen in value.generators:
        if (_nonempty_literal(gen.iter)
                or _range_nonempty(node, gen.iter, parent)):
            continue
        source = _lv25_iter_source_name(
            gen.iter, parent, forward=True)
        if source is None:
            return False
        shadowed = _lv09_comp_shadowed_names(
            value, gen, {id(gen): gen.iter})
        if source in shadowed:
            return False
        if (_lv25_guarded_at(
                node, source, names, parent, kv_collectors, visiting)
                or _lv25_condition_guarded(node, source, parent)):
            continue
        return False
    return True
def _lv25_slice_has_items(
        lower: int | None, upper: int | None,
        step: int, source_length: int) -> bool:
    start, stop, stride = slice(lower, upper, step).indices(source_length)
    return len(range(start, stop, stride)) > 0
def _lv25_slice_required_len(
        lower: int | None, upper: int | None,
        step: int) -> int | None:
    span = max(64, abs(lower or 0) + abs(upper or 0) + abs(step) + 2)
    if span > 10000:
        return None
    first: int | None = None
    for length in range(1, span + 2):
        nonempty = _lv25_slice_has_items(lower, upper, step, length)
        if nonempty and first is None:
            first = length
        elif first is not None and not nonempty:
            return None
    return first
def _lv25_known_len_at_least(
        node: ast.AST, name: str, minimum: int,
        parent: dict[int, ast.AST], names: set[str],
        kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]]) -> bool:
    assignment = _latest_assignment(node, name, parent)
    if assignment is None or not _lv25_assignment_dominates(
            assignment, name, node, parent, names, kv_collectors,
            visiting):
        return False
    if _binding_invalidated_since(assignment, name, node, parent):
        return False
    length = _lv25_known_length(node, assignment.value, parent)
    return length is not None and length >= minimum
def _lv25_slice_nonempty(
        node: ast.AST, value: ast.AST, names: set[str],
        parent: dict[int, ast.AST],
        kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]] = _EMPTY_VISITS) -> bool:
    if (not isinstance(value, ast.Subscript)
            or not isinstance(value.slice, ast.Slice)):
        return False
    step_node = value.slice.step
    step = 1 if step_node is None else _resolved_int(node, step_node, parent)
    if step is None or step == 0:
        return False
    lower, upper = value.slice.lower, value.slice.upper
    lower_value = (None if lower is None
                   else _resolved_int(node, lower, parent))
    upper_value = (None if upper is None
                   else _resolved_int(node, upper, parent))
    source_node = value.value
    if isinstance(source_node, (ast.List, ast.Tuple, ast.Set,
                                ast.Constant)):
        if ((lower is not None and lower_value is None)
                or (upper is not None and upper_value is None)):
            return False
        source_len = _lv25_known_length(node, source_node, parent)
        return (source_len is not None
                and _lv25_slice_has_items(
                    lower_value, upper_value, step, source_len))
    if not isinstance(source_node, ast.Name):
        return False
    source = source_node.id
    if not (_lv25_guarded_at(
                node, source, names, parent, kv_collectors, visiting)
            or _lv25_condition_guarded(node, source, parent)):
        return False
    if lower is not None and lower_value is None:
        if upper is not None or step != 1 or not isinstance(lower, ast.Name):
            return False
        bounds = _lv25_split_index_bounds(
            node, lower.id, source, parent, names, kv_collectors,
            visiting)
        if bounds is None:
            return False
        constant, _subtract = bounds
        minimum = max(1, constant + 1)
        return _lv25_len_at_least_guarded(node, source, minimum, parent)
    if upper is not None and upper_value is None:
        if lower is not None or step != 1 or not isinstance(upper, ast.Name):
            return False
        bounds = _lv25_split_index_bounds(
            node, upper.id, source, parent, names, kv_collectors,
            visiting)
        if bounds is None or bounds[0] < 1:
            return False
        return _lv25_len_at_least_guarded(node, source, 1, parent)
    required = _lv25_slice_required_len(lower_value, upper_value, step)
    if required is None:
        return False
    return (_lv25_len_at_least_guarded(node, source, required, parent)
            or _lv25_known_len_at_least(
                node, source, required, parent, names,
                kv_collectors, visiting))
def _lv25_nonempty_builtin_ctor(
        node: ast.AST, value: ast.AST,
        parent: dict[int, ast.AST], names: set[str],
        kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]] = _EMPTY_VISITS) -> bool:
    if not (isinstance(value, ast.Call)
            and isinstance(value.func, ast.Name)
            and value.func.id in _LV25_CONTAINER_CTORS
            and len(value.args) == 1 and not value.keywords):
        return False
    arg = value.args[0]
    if (value.func.id == 'dict'
            and not isinstance(arg, (ast.Dict, ast.Name))):
        return False
    source_nonempty = (
        _nonempty_literal(arg) or _range_nonempty(node, arg, parent))
    if not source_nonempty and isinstance(arg, ast.Name):
        source_nonempty = (
            _lv25_guarded_at(
                node, arg.id, names, parent, kv_collectors, visiting)
            or _lv25_condition_guarded(node, arg.id, parent))
    return (source_nonempty
            and not shadowed_binding_at(node, value.func.id, parent, {}))
def _lv25_value_known_nonempty(
        node: ast.AST, value: ast.AST, names: set[str],
        parent: dict[int, ast.AST],
        kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]] = _EMPTY_VISITS) -> bool:
    if (_nonempty_literal(value) or _lv25_nonempty_fallback(value)
            or _range_nonempty(node, value, parent)
            or _lv25_nonempty_builtin_ctor(
                node, value, parent, names, kv_collectors, visiting)
            or _lv25_repeated_nonempty(value)
            or _lv25_concat_nonempty(value)):
        return True
    if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
            and _lv25_ctor_visible(
                node, value.func.id, parent)):
        return True
    if (_lv25_comprehension_nonempty(
            node, value, names, parent, kv_collectors, visiting)
            or _lv25_slice_nonempty(
                node, value, names, parent, kv_collectors,
                visiting)):
        return True
    return (isinstance(value, ast.Name)
            and (_lv25_guarded_at(
                    node, value.id, names, parent, kv_collectors,
                    visiting)
                 or _lv25_condition_guarded(node, value.id, parent)))
def _lv25_derive_aliases_fixpoint(tree: ast.AST, names: set[str],
                                  parent: dict[int, ast.AST]) -> None:
    for _ in range(_LV25_ALIAS_ROUNDS):
        grew = False
        for node in walk_nodes(tree):
            shape = _lv25_assign_shape(node)
            if shape is None or not isinstance(shape[0], ast.Name):
                continue
            target = shape[0].id
            if target in names:
                continue
            if _lv25_value_known_nonempty(
                    node, shape[1], names, parent, set()):
                names.add(target)
                grew = True
        if not grew:
            break
_COLLECTOR_NAME = 'name'
_COLLECTOR_SUBSCRIPT = 'subscript'
_COLLECTOR_SETDEFAULT = 'setdefault'
def _collector_target(call: ast.AST) -> tuple[str, str] | None:
    if not (isinstance(call, ast.Call)
            and isinstance(call.func, ast.Attribute)):
        return None
    recv = call.func.value
    if isinstance(recv, ast.Name):
        return recv.id, _COLLECTOR_NAME
    if isinstance(recv, ast.Subscript) and isinstance(recv.value, ast.Name):
        return recv.value.id, _COLLECTOR_SUBSCRIPT
    if (isinstance(recv, ast.Call)
            and isinstance(recv.func, ast.Attribute)
            and recv.func.attr == 'setdefault'
            and isinstance(recv.func.value, ast.Name)):
        return recv.func.value.id, _COLLECTOR_SETDEFAULT
    return None
def _lv25_straight_line_append(call: ast.Call, name: str, scope: ast.AST,
                               parent: dict[int, ast.AST]) -> bool:
    info = _collector_target(call)
    if info is None or info[0] != name:
        return False
    cur = parent.get(id(call))
    while cur is not None and cur is not scope:
        if not isinstance(cur, ast.Expr):
            return False
        cur = parent.get(id(cur))
    return cur is scope
def _lv25_returns_or_raises(node: ast.AST) -> bool:
    if isinstance(node, (ast.Return, ast.Raise)):
        return True
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.Lambda, ast.ClassDef)):
        return False
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        return (
            any(_lv25_returns_or_raises(stmt) for stmt in node.body)
            or any(_lv25_may_skip_following(stmt) for stmt in node.orelse))
    return any(_lv25_returns_or_raises(sub)
               for sub in ast.iter_child_nodes(node))
def _lv25_may_skip_following(node: ast.AST) -> bool:
    if isinstance(node, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
        return True
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.Lambda, ast.ClassDef)):
        return False
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        return _lv25_returns_or_raises(node)
    return any(_lv25_may_skip_following(sub)
               for sub in ast.iter_child_nodes(node))
def _lv25_node_in_loop_body(
        node: ast.AST, loop: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    child = _child_under(loop, node, parent)
    return (child is not None
            and any(child is stmt for stmt in getattr(loop, 'body', ())))
def _lv25_iterable_nonempty(
        node: ast.AST, iter_node: ast.AST, names: set[str],
        parent: dict[int, ast.AST]) -> bool:
    if (_nonempty_literal(iter_node)
            or _range_nonempty(node, iter_node, parent)
            or _lv25_nonempty_builtin_ctor(
                node, iter_node, parent, names, set())):
        return True
    if (isinstance(iter_node, ast.Call)
            and isinstance(iter_node.func, ast.Name)
            and _lv25_ctor_visible(
                node, iter_node.func.id, parent)):
        return True
    source = _lv25_iter_source_name(
        iter_node, parent, forward=True)
    if source is None:
        return False
    if _lv25_condition_guarded(node, source, parent):
        return True
    return _lv25_guarded_at(
        node, source, names, parent, set())
def _lv25_append_execution_guaranteed(
        call: ast.Call, name: str, names: set[str],
        parent: dict[int, ast.AST]) -> bool:
    scope = nearest_scope(parent, call)
    if scope is None:
        return False
    if _lv25_prior_exit_before(call, scope, parent):
        return False
    child: ast.AST = call
    cur = parent.get(id(call))
    saw_loop = False
    while cur is not None and cur is not scope:
        if isinstance(cur, (ast.For, ast.AsyncFor)):
            position = next((index for index, stmt in enumerate(cur.body)
                             if stmt is child), -1)
            if position < 0:
                return False
            if any(_lv25_may_skip_following(stmt)
                   for stmt in cur.body[:position]):
                return False
            if not _lv25_iterable_nonempty(
                    cur, cur.iter, names, parent):
                return False
            saw_loop = True
        elif not isinstance(cur, ast.Expr):
            return False
        child = cur
        cur = parent.get(id(cur))
    if cur is not scope:
        return False
    return saw_loop or _lv25_straight_line_append(call, name, scope, parent)
def _collect_append_sets(tree: ast.AST, parent: dict,
                         names: set[str]) -> tuple[set[str], set[str], set[str]]:
    kv_collectors: set[str] = set()
    guaranteed_kv: set[str] = set()
    direct_collectors: set[str] = set()
    for node in walk_nodes(tree):
        if (not isinstance(node, ast.Call)
                or not isinstance(node.func, ast.Attribute)
                or node.func.attr != 'append'):
            continue
        info = _collector_target(node)
        if info is None:
            continue
        cname, form = info
        is_kv = form != _COLLECTOR_NAME
        guaranteed = _lv25_append_execution_guaranteed(node, cname, names, parent)
        if is_kv:
            kv_collectors.add(cname)
            if guaranteed:
                guaranteed_kv.add(cname)
        elif guaranteed:
            direct_collectors.add(cname)
    return direct_collectors, kv_collectors, guaranteed_kv
def _enclosing_for_node(node: ast.AST, parent: dict) -> ast.For | None:
    cur: ast.AST | None = node
    while cur is not None:
        cur = parent.get(id(cur))
        if isinstance(cur, ast.For):
            return cur
    return None
def _kv_items_iter_name(iter_node: ast.AST,
                        kv_collectors: set[str]) -> str | None:
    if not (isinstance(iter_node, ast.Call)
            and isinstance(iter_node.func, ast.Attribute)
            and iter_node.func.attr == 'items'
            and not iter_node.args and not iter_node.keywords
            and isinstance(iter_node.func.value, ast.Name)):
        return None
    return (iter_node.func.value.id
            if iter_node.func.value.id in kv_collectors else None)
def _propagate_collector_safety(tree: ast.AST, names: set[str],
                               parent: dict[int, ast.AST]) -> None:
    for _ in range(_LV25_COLLECTOR_ROUNDS):
        grew = False
        direct_collectors, _kv_collectors, guaranteed_kv = (
            _collect_append_sets(tree, parent, names))
        for cname in direct_collectors | guaranteed_kv:
            if cname not in names:
                names.add(cname)
                grew = True
        if not grew:
            break
def _lv25_nonempty_fallback(value: ast.AST) -> bool:
    return (isinstance(value, ast.BoolOp) and isinstance(value.op, ast.Or)
            and any(_nonempty_literal(v) for v in value.values))
def _lv25_static_sequence(node: ast.AST) -> bool:
    return (isinstance(node, (ast.List, ast.Tuple))
            or (isinstance(node, ast.Constant)
                and isinstance(node.value, (str, bytes))))
def _lv25_repeated_nonempty(value: ast.AST) -> bool:
    if not (isinstance(value, ast.BinOp)
            and isinstance(value.op, ast.Mult)):
        return False
    for seq, count_node in ((value.left, value.right),
                            (value.right, value.left)):
        count = int_literal(count_node, allow_bool=True)
        if (count is not None and count >= 1
                and _nonempty_literal(seq)):
            return True
    return False
def _lv25_concat_nonempty(value: ast.AST) -> bool:
    if not (isinstance(value, ast.BinOp) and isinstance(value.op, ast.Add)):
        return False
    sides = (value.left, value.right)
    return (all(_lv25_static_sequence(side) for side in sides)
            and any(_nonempty_literal(side) for side in sides))
def _lv25_alias_length_stable(
        assignment: ast.AST, name_node: ast.Name, use_node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    name = name_node.id
    scope = nearest_scope(parent, assignment)
    if scope is None or nearest_scope(parent, use_node) is not scope:
        return False
    if not _binding_dominates_scope(assignment, scope, parent):
        return False
    start = (assignment.lineno, assignment.col_offset)
    end = (use_node.lineno, use_node.col_offset)
    for candidate in walk_nodes(scope):
        if not isinstance(candidate, ast.Name) or candidate.id != name:
            continue
        position = (candidate.lineno, candidate.col_offset)
        if not start < position < end:
            continue
        if candidate is name_node or _lv25_in_subtree(
                candidate, use_node, parent):
            continue
        return False
    return True
def _lv25_static_sequence_kind(value: ast.AST) -> type | None:
    if isinstance(value, ast.List):
        return list
    if isinstance(value, ast.Tuple):
        return tuple
    if (isinstance(value, ast.Constant)
            and isinstance(value.value, (str, bytes))):
        return type(value.value)
    return None
def _lv25_known_length(
        node: ast.AST, value: ast.AST,
        parent: dict[int, ast.AST],
        visiting: frozenset[int] = _EMPTY_VISITS,
        use_node: ast.AST | None = None) -> int | None:
    if use_node is None:
        use_node = node
    if isinstance(value, ast.Constant) and isinstance(value.value, (str, bytes)):
        return len(value.value)
    if isinstance(value, (ast.List, ast.Tuple)):
        if any(isinstance(elt, ast.Starred) for elt in value.elts):
            return None
        return len(value.elts)
    if isinstance(value, ast.Set):
        return _lv09_static_set_len(value)
    if isinstance(value, ast.Dict):
        return _lv09_static_dict_len(value)
    ranged = _range_length(node, value, parent)
    if ranged is not None:
        return ranged
    if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
            and value.func.id in _LV25_CONTAINER_CTORS and not value.keywords
            and not shadowed_binding_at(node, value.func.id, parent, {})):
        if not value.args:
            return 0
        if len(value.args) == 1 and not isinstance(value.args[0], ast.Starred):
            ctor_name = value.func.id
            arg = value.args[0]
            source_length = _lv25_known_length(
                node, arg, parent, visiting, use_node)
            if source_length == 0:
                return 0
            if ctor_name in {'list', 'tuple'}:
                return source_length
            if ctor_name in {'set', 'frozenset'}:
                if isinstance(arg, (ast.List, ast.Tuple)):
                    if any(isinstance(elt, ast.Starred) for elt in arg.elts):
                        return None
                    return _lv09_static_set_len(ast.Set(elts=list(arg.elts)))
                if (isinstance(arg, ast.Constant)
                        and isinstance(arg.value, (str, bytes))):
                    return len(set(arg.value))
                if (isinstance(arg, (ast.Set, ast.Dict))
                        or _range_length(node, arg, parent) is not None):
                    return source_length
                return None
            if ctor_name == 'dict':
                return source_length if isinstance(arg, ast.Dict) else None
    if isinstance(value, ast.BinOp):
        if isinstance(value.op, ast.Mult):
            for sequence, count_node in (
                    (value.left, value.right), (value.right, value.left)):
                if _lv25_static_sequence_kind(sequence) is None:
                    continue
                sequence_len = _lv25_known_length(
                    node, sequence, parent, visiting, use_node)
                count = int_literal(count_node, allow_bool=True)
                if sequence_len is not None and count is not None:
                    return sequence_len * count if count > 0 else 0
        if (isinstance(value.op, ast.Add)
                and _lv25_static_sequence_kind(value.left) is not None
                and _lv25_static_sequence_kind(value.left)
                is _lv25_static_sequence_kind(value.right)):
            left_len = _lv25_known_length(
                node, value.left, parent, visiting, use_node)
            right_len = _lv25_known_length(
                node, value.right, parent, visiting, use_node)
            if left_len is not None and right_len is not None:
                return left_len + right_len
    if isinstance(value, ast.Name):
        if id(value) in visiting:
            return None
        assignment = _latest_assignment(node, value.id, parent)
        if (assignment is not None
                and _lv25_alias_length_stable(
                    assignment, value, use_node, parent)):
            return _lv25_known_length(
                assignment, assignment.value, parent,
                visiting | {id(value)}, use_node)
    return None
def _lv25_is_nonempty_ctor(node: ast.FunctionDef) -> bool:
    if node.decorator_list:
        return False
    body = scan_body_no_funcs(node.body)
    if any(isinstance(n, (ast.Yield, ast.YieldFrom)) for n in body):
        return False
    if not block_exits(node.body):
        return False
    returns = [n for n in body if isinstance(n, ast.Return)]
    return bool(returns) and all(
        r.value is not None and _nonempty_literal(r.value)
        for r in returns)
def _lv25_definition_bindings(
        body: list[ast.stmt]) -> list[tuple[ast.AST, None]]:
    bindings: list[tuple[ast.AST, None]] = []
    stack: list[ast.AST] = list(body)
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Lambda):
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            bindings.append((node, None))
            continue
        stack.extend(ast.iter_child_nodes(node))
    return bindings
def _lv25_ctor_visible(
        node: ast.AST, name: str, parent: dict[int, ast.AST],
        visiting: frozenset[tuple[int, str]] = _EMPTY_VISITS) -> bool:
    key = (id(node), name)
    if key in visiting:
        return False
    nested = visiting | {key}
    position = (node.lineno, node.col_offset)
    for scope in _scope_chain(node, parent):
        if (isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda))
                and name in param_names(scope)):
            return False
        body = getattr(scope, 'body', None)
        if not isinstance(body, list):
            continue
        binding_rows = [
            (binding, value)
            for binding, value in binding_entries_index(body).get(name, ())
        ]
        binding_rows.extend(
            (binding, value)
            for binding, value in _lv25_definition_bindings(body)
            if getattr(binding, 'name', None) == name
        )
        if (scope is not nearest_scope(parent, node)
                and any((getattr(binding, 'lineno', 0),
                         getattr(binding, 'col_offset', 0)) >= position
                        for binding, _value in binding_rows)):
            return False
        bindings = [
            (binding, value)
            for binding, value in binding_rows
            if (getattr(binding, 'lineno', 0),
                getattr(binding, 'col_offset', 0)) < position
        ]
        if not bindings:
            if name in scope_local_bindings(scope):
                return False
            continue
        latest, value = max(
            bindings,
            key=lambda item: (getattr(item[0], 'lineno', 0),
                              getattr(item[0], 'col_offset', 0)))
        if not _binding_dominates_scope(latest, scope, parent):
            return False
        if isinstance(latest, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return _lv25_is_nonempty_ctor(latest)
        if (isinstance(latest, (ast.Assign, ast.AnnAssign,
                                ast.NamedExpr))
                and isinstance(value, ast.Name)):
            return _lv25_ctor_visible(
                node, value.id, parent, nested)
        return False
    return False
def _lv25_ctor_targets(
        tree: ast.AST,
        parent: dict[int, ast.AST]) -> set[str]:
    targets: set[str] = set()
    for node in walk_nodes(tree):
        if not (isinstance(node, (ast.Assign, ast.AnnAssign))
                and isinstance(node.value, ast.Call)
                and isinstance(node.value.func, ast.Name)
                and _lv25_ctor_visible(
                    node, node.value.func.id, parent)):
            continue
        nodes = node.targets if isinstance(node, ast.Assign) else [node.target]
        targets.update(t.id for t in nodes if isinstance(t, ast.Name))
    return targets
def _lv25_issue(filepath: Any, src_lines: list[str],
                node: ast.BinOp | ast.AugAssign,
                arg_name: str) -> dict[str, Any]:
    op_name = '/' if isinstance(node.op, ast.Div) else '//'
    return make_issue(
        'LV-25', 'P2', 'logic_correctness', filepath, node.lineno,
        f'除数 {op_name} len(...) 动态归零：{arg_name} 为空容器即 '
        f'ZeroDivisionError',
        (
            f'除数是 ``len({arg_name})``——{arg_name} 为空序列/空'
            f'映射时 len() 归 0，除法瞬间 ZeroDivisionError。'
            f'文件内未发现对 {arg_name} 的空状态守卫（``if '
            f'{arg_name}:`` / ``if len({arg_name}) == 0:``）。'
            f'平均值/占比类计算（``sum(x) / len(x)``）在空数据集上'
            f'是最高频的运行时崩溃形态。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：len() 可为 0 是容器常态，除法未做零值防御。\n'
            '修复策略：先判空再算（``if items: avg = total / '
            'len(items) else: avg = 0`` 或条件表达式 ``total / '
            'len(items) if items else 0``）；已知非空的数据集'
            '在守卫分支内计算。\n'
            '参考标准：Python len() 零值与除法 ZeroDivisionError 契约'
        ),
        'div-by-len-zero',
    )
def check_LV25(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    parent = parent_map_of(tree)
    guarded = _lv25_guarded_names(tree, parent)
    shadow_cache: dict[tuple[int, frozenset[int]], set[str]] = {}
    _, kv_collectors, _ = _collect_append_sets(tree, parent, set())
    for node in roots:
        arg_name = _lv25_violates(
            node, guarded, parent, tree, kv_collectors, shadow_cache)
        if arg_name is None:
            continue
        issues.append(_lv25_issue(filepath, src_lines, node, arg_name))
    return issues
_LV27_AGG_NAMES = frozenset({'max', 'min'})
def _lv27_gate_blocked(
        node: ast.AST, parents: dict[int, ast.AST],
        cache: dict[tuple, set[str]]) -> bool:
    if (not isinstance(node, ast.Call)
            or not isinstance(node.func, ast.Name)
            or node.func.id not in _LV27_AGG_NAMES):
        return True
    if shadowed_binding_at(node, node.func.id, parents, cache):
        return True
    if len(node.args) != 1:
        return True
    if len(node.keywords) > 1 or any(
            kw.arg is None or kw.arg != 'key' for kw in node.keywords):
        return True
    return not isinstance(node.args[0], _CONTAINER_COMP_NODES)
def _lv27_condition_guarded(
        node: ast.Call, iter_node: ast.AST,
        parents: dict[int, ast.AST]) -> bool:
    subject = _lv25_iter_subject(iter_node, parents, forward=True)
    if isinstance(subject, ast.Name):
        name = subject.id
        return _guarded_on_path(
            iter_node, parents,
            lambda test, truth: _nonempty_holds(test, name, truth, parents),
            lambda guard: _binding_invalidated_since(
                guard, name, iter_node, parents),
            frozenset({name}))
    return _expression_condition_guarded(
        iter_node, subject, parents,
        lambda guard: _expression_guard_invalidated(
            guard, subject, iter_node, parents))
def _lv27_subject_param(
        subject: ast.AST, fn: ast.AST) -> tuple[str, str | None] | None:
    params = param_names(fn)
    if isinstance(subject, ast.Name) and subject.id in params:
        return subject.id, None
    if (isinstance(subject, ast.Attribute)
            and isinstance(subject.value, ast.Name)
            and subject.value.id in params):
        return subject.value.id, subject.attr
    return None
def _lv27_map_subject(
        subject: ast.AST, actual: ast.AST, fn: ast.AST) -> ast.AST | None:
    binding = _lv27_subject_param(subject, fn)
    if binding is None:
        return None
    _param, attr = binding
    if attr is None:
        return actual
    return ast.Attribute(value=actual, attr=attr, ctx=ast.Load())
def _lv27_subject_safe_at_call(
        call: ast.Call, subject: ast.AST, parent: dict[int, ast.AST],
        guarded: set[str], kv_collectors: set[str]) -> bool:
    return (_lv25_value_known_nonempty(
                call, subject, guarded, parent, kv_collectors)
            or _lv27_condition_guarded(call, subject, parent))
def _lv27_private_subject_guarded(
        tree: ast.AST, fn: ast.AST, subject: ast.AST,
        parent: dict[int, ast.AST], guarded: set[str],
        kv_collectors: set[str],
        visiting: frozenset[tuple[int, str]] = _EMPTY_VISITS) -> bool:
    callable_info = _private_callable(fn, parent)
    binding = _lv27_subject_param(subject, fn)
    if callable_info is None or binding is None:
        return False
    key = (id(fn), ast.dump(subject, include_attributes=False))
    if key in visiting:
        return False
    name, drop, kind = callable_info
    if _length_callable_reference_escapes(tree, name, kind, parent):
        return False
    calls = _matching_calls(tree, name, kind)
    if not calls:
        return False
    nested = visiting | {key}
    for call in calls:
        actual = _actual_arg(call, fn, binding[0], drop)
        if actual is None:
            return False
        mapped = _lv27_map_subject(subject, actual, fn)
        if mapped is None:
            return False
        if _lv27_subject_safe_at_call(
                call, mapped, parent, guarded, kv_collectors):
            continue
        if not isinstance(mapped, ast.Name):
            return False
        caller = _enclosing_function(call, parent)
        if (caller is None or mapped.id not in param_names(caller)
                or not _lv27_private_subject_guarded(
                    tree, caller, ast.Name(id=mapped.id, ctx=ast.Load()),
                    parent, guarded, kv_collectors, nested)):
            return False
    return True
def _lv27_interproc_source_guarded(
        tree: ast.AST, value: ast.AST, index: int, node: ast.Call,
        parent: dict[int, ast.AST], guarded: set[str],
        kv_collectors: set[str]) -> bool:
    fn = _enclosing_function(node, parent)
    if fn is None:
        return False
    gen = value.generators[index]
    subject = _lv25_iter_subject(gen.iter, parent)
    root = subject.value if isinstance(subject, ast.Attribute) else subject
    if isinstance(root, ast.Name):
        shadowed = _lv09_comp_shadowed_names(
            value, gen, {id(gen): gen.iter})
        if root.id in shadowed:
            return False
    return _lv27_private_subject_guarded(
        tree, fn, subject, parent, guarded, kv_collectors)
def _lv27_setdefault_collectors(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == 'append'):
            continue
        info = _collector_target(node)
        if info is not None and info[1] == _COLLECTOR_SETDEFAULT:
            names.add(info[0])
    return names
def _lv27_kv_value_nonempty(
        iter_node: ast.AST, node: ast.Call, collectors: set[str],
        parent: dict[int, ast.AST]) -> bool:
    if not isinstance(iter_node, ast.Name):
        return False
    evidence = _kv_value_evidence(
        node, iter_node.id, collectors, parent)
    return (evidence is not None
            and not _binding_invalidated_since(
                evidence, iter_node.id, node, parent))
def _lv27_comp_target_nonempty(
        value: ast.AST, index: int, name: str) -> bool:
    for gen in reversed(value.generators[:index]):
        target = gen.target
        bound_names = {
            bound for bound, _line in target_store_names(target, 0)}
        if name not in bound_names:
            continue
        if not isinstance(target, ast.Name):
            return False
        iter_node = gen.iter
        if (not isinstance(iter_node, (ast.List, ast.Tuple))
                or not iter_node.elts
                or any(isinstance(elt, ast.Starred)
                       for elt in iter_node.elts)):
            return False
        return all(_nonempty_literal(elt)
                   for elt in iter_node.elts)
    return False
def _lv27_source_cleared(
        value: ast.AST, parent: dict[int, ast.AST], node: ast.Call,
        tree: ast.AST, collectors: set[str], guarded: set[str], kv_collectors: set[str]) -> bool:
    if not isinstance(value, _CONTAINER_COMP_NODES):
        return False
    if not value.generators or any(gen.ifs for gen in value.generators):
        return False
    for index, gen in enumerate(value.generators):
        iter_node = gen.iter
        if (_nonempty_literal(iter_node)
                or _range_nonempty(node, iter_node, parent)):
            continue
        subject = _lv25_iter_subject(iter_node, parent, forward=True)
        if (isinstance(subject, ast.Name)
                and (_lv25_guarded_at(
                        iter_node, subject.id, guarded, parent,
                        kv_collectors)
                     or _lv25_in_loop_source_body(
                         node, subject.id, parent)
                     or _lv27_comp_target_nonempty(
                         value, index, subject.id))):
            continue
        if _lv27_condition_guarded(node, iter_node, parent):
            continue
        if _lv27_kv_value_nonempty(iter_node, node, collectors, parent):
            continue
        if _lv27_interproc_source_guarded(
                tree, value, index, node, parent, guarded, kv_collectors):
            continue
        return False
    return True
def _lv27_issue(filepath: Any, src_lines: list[str], node: ast.Call) -> dict[str, Any]:
    agg = node.func.id
    return make_issue(
        'LV-27', 'P2', 'logic_correctness', filepath, node.lineno,
        f'{agg}() 空序列无 default：空输入/全过滤即 '
        f'ValueError',
        (
            f'``{agg}(推导式/生成器表达式)`` 未提供 default '
            f'——单实参推导式在源为空时即产出空序列（过滤推导式'
            f'还会在全过滤时空），此时抛 '
            f'``ValueError: {agg}() arg is an empty '
            f'sequence``，取极值入口当步崩溃。空数据集是运行常态'
            f'（无记录/全不合格），不是异常路径。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：max/min 对空序列抛 ValueError 是契约行为，调用\n'
            '处未给空态语义。\n'
            '修复策略：补 ``default=`` 关键字（``max(vals, default=0)``，\n'
            '生成器实参须加括号 ``max((v for v in xs), default=0)``）；\n'
            '或先判空走独立分支。\n'
            '参考标准：Python max/min 空序列与 default 参数契约'
        ),
        'empty-seq-max-min',
    )
def check_LV27(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    shadow_cache: dict[tuple, set[str]] = {}
    collectors = _lv27_setdefault_collectors(tree)
    guarded = _lv25_guarded_names(tree, parents)
    _, kv_collectors, _ = _collect_append_sets(tree, parents, set())
    for node in roots:
        if _lv27_gate_blocked(node, parents, shadow_cache):
            continue
        if _lv27_source_cleared(
                node.args[0], parents, node, tree, collectors,
                guarded, kv_collectors):
            continue
        issues.append(_lv27_issue(filepath, src_lines, node))
    return issues

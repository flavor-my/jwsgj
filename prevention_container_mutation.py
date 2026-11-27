from __future__ import annotations

import ast
import logging
from collections.abc import Callable
from typing import Any

from jwsgj.prevention_scope_facts import (
    INPLACE_MUTATOR_METHODS,
    SCOPE_CONTAINERS,
    TRY_NODES,
    aligned_unpack_pairs,
    bare_single_arg_call,
    block_exits,
    branch_truth,
    capture_binding_names,
    definition_outer_node_ids,
    int_literal,
    iter_nodes_outside,
    make_issue,
    nearest_scope,
    param_names,
    parent_map_of,
    same_expr,
    scope_body_stmts,
    scope_local_bindings,
    shadowed_binding_at,
    snippet_of,
    source_lines,
    stmt_siblings,
    target_store_names,
    walk_ast_nodes,
    walk_nodes,
)

__all__ = [
    'check_LV02',
    'check_LV09',
    'check_LV19',
    'check_LV22',
    'check_LV45',
]
_log = logging.getLogger(__name__)
_log.info(
    "prevention_container_mutation 容器变更 / 迭代形态"
    "五族检测器已加载：%d 项导出", len(__all__))
_LV09_MARKER_NODES = (ast.expr_context, ast.operator, ast.boolop,
                      ast.unaryop, ast.cmpop)
_CONTAINER_COMP_NODES = (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)
_LenValue = int | frozenset[int]
_LenRecord = tuple[int, int, int | None, ast.AST | None]
_Binds = dict[str, list[_LenRecord]]
_EMPTY_VISITS: frozenset[Any] = frozenset()
def _lv09_range_len(
        arg: ast.AST, node: ast.AST,
        parents: dict[int, ast.AST]) -> int | None:
    if (not isinstance(arg, ast.Call)
            or not isinstance(arg.func, ast.Name)
            or arg.func.id != 'range'
            or arg.keywords
            or not 1 <= len(arg.args) <= 3
            or any(isinstance(item, ast.Starred) for item in arg.args)
            or shadowed_binding_at(node, 'range', parents, {})):
        return None
    bounds = [int_literal(item) for item in arg.args]
    if any(bound is None for bound in bounds):
        return None
    try:
        return len(range(*bounds))
    except (TypeError, ValueError, OverflowError):
        return None
def _lv09_comprehension_len(
        comp: ast.ListComp | ast.GeneratorExp,
        bindings: dict[str, _LenValue], node: ast.AST,
        parents: dict[int, ast.AST]) -> _LenValue | None:
    if len(comp.generators) != 1:
        return None
    gen = comp.generators[0]
    if gen.ifs or gen.is_async:
        return None
    return _lv09_literal_len(gen.iter, bindings, node, parents)
def _lv09_static_comp_len(value: ast.AST) -> int | None:
    """单生成器、无 ifs/async、iter 为字面量的 ListComp/GeneratorExp 的静态长度。

    与调用点的 ``_lv09_comprehension_len`` 同口径，但只看字面量（赋值记录阶段
    没有名字解析上下文）；用于让 ``a = [x for x in [1, 2]]; zip(a, [1, 2, 3])
    这类先赋值再比对的 zip 长度错配也能被检出。
    """
    if not isinstance(value, (ast.ListComp, ast.GeneratorExp)):
        return None
    if len(value.generators) != 1:
        return None
    gen = value.generators[0]
    if gen.ifs or gen.is_async:
        return None
    it = gen.iter
    if isinstance(it, (ast.List, ast.Tuple)):
        if any(isinstance(e, ast.Starred) for e in it.elts):
            return None
        return len(it.elts)
    if isinstance(it, ast.Set):
        return _lv09_static_set_len(it)
    if isinstance(it, ast.Dict):
        return _lv09_static_dict_len(it)
    if isinstance(it, ast.Constant) and isinstance(it.value, (str, bytes)):
        return len(it.value)
    if isinstance(it, (ast.ListComp, ast.GeneratorExp)):
        return _lv09_static_comp_len(it)
    return None
def _lv09_static_value_len(value: ast.AST) -> int | None:
    """赋值右值的静态长度：无星号的 List/Tuple 字面量或静态推导式。"""
    if isinstance(value, (ast.List, ast.Tuple)):
        if any(isinstance(e, ast.Starred) for e in value.elts):
            return None
        return len(value.elts)
    return _lv09_static_comp_len(value)
def _lv09_static_set_len(node: ast.Set) -> int | None:
    values = []
    for elt in node.elts:
        if not isinstance(elt, ast.Constant):
            return None
        values.append(elt.value)
    try:
        return len(set(values))
    except TypeError:
        return None
def _lv09_static_dict_len(node: ast.Dict) -> int | None:
    keys = []
    for key in node.keys:
        if not isinstance(key, ast.Constant):
            return None
        keys.append(key.value)
    try:
        return len(set(keys))
    except TypeError:
        return None
def _lv09_literal_len(
        arg: ast.AST, bindings: dict[str, _LenValue], node: ast.AST,
        parents: dict[int, ast.AST]) -> _LenValue | None:
    if isinstance(arg, (ast.List, ast.Tuple)):
        if any(isinstance(e, ast.Starred) for e in arg.elts):
            return None
        return len(arg.elts)
    if isinstance(arg, ast.Set):
        return _lv09_static_set_len(arg)
    if isinstance(arg, ast.Dict):
        return _lv09_static_dict_len(arg)
    if isinstance(arg, ast.Constant) and isinstance(arg.value, (str, bytes)):
        return len(arg.value)
    if isinstance(arg, ast.NamedExpr):
        return _lv09_literal_len(
            arg.value, bindings, node, parents)
    if isinstance(arg, (ast.ListComp, ast.GeneratorExp)):
        return _lv09_comprehension_len(arg, bindings, node, parents)
    ranged = _lv09_range_len(arg, node, parents)
    if ranged is not None:
        return ranged
    if isinstance(arg, ast.Name):
        return bindings.get(arg.id)
    return None
_LV09_LEN_MUTATORS = frozenset({
    'append', 'extend', 'insert', 'remove', 'clear', 'pop',
    'add', 'discard', 'update', 'difference_update',
    'intersection_update', 'symmetric_difference_update',
    'popitem', 'setdefault',
})
def _lv09_record(
        binds: _Binds,
        name: str, record: tuple[int, int, int | None],
        origin: ast.AST | None = None) -> None:
    binds.setdefault(name, []).append((*record, origin))
def _lv09_pos(n: ast.AST,
              anchor: tuple[int, int] | None) -> tuple[int, int]:
    return anchor if anchor is not None else (n.lineno, n.col_offset)
def _lv09_assignment_bind_pos(
        stmt: ast.Assign | ast.AnnAssign) -> tuple[int, int]:
    value = stmt.value
    return (value.end_lineno or stmt.lineno,
            value.end_col_offset or stmt.col_offset)
def _lv09_push_comp_children(
        cur: ast.AST,
        stack: list[tuple[ast.AST, tuple[int, int] | None]],
        comp_anchor: tuple[int, int] | None) -> bool:
    if isinstance(cur, ast.comprehension):
        stack.extend((child, comp_anchor)
                     for child in ast.iter_child_nodes(cur)
                     if child is not cur.target)
        return True
    if isinstance(cur, _CONTAINER_COMP_NODES):
        comp_pos = (cur.lineno, cur.col_offset)
        stack.extend((child, comp_pos)
                     for child in ast.iter_child_nodes(cur))
        return True
    return False
def _lv09_rebound_names(cur: ast.AST) -> tuple[str, ...]:
    names = set(capture_binding_names(cur))
    if isinstance(cur, ast.ExceptHandler) and cur.name:
        names.add(cur.name)
    if isinstance(cur, ast.Name) and isinstance(
            cur.ctx, (ast.Store, ast.Del)):
        names.add(cur.id)
    return tuple(sorted(names))
def _lv09_subscript_base(cur: ast.AST) -> str:
    if (isinstance(cur, ast.Subscript)
            and isinstance(cur.ctx, (ast.Store, ast.Del))
            and isinstance(cur.value, ast.Name)):
        return cur.value.id
    return ''
def _lv09_mutator_receiver(cur: ast.AST) -> str:
    if (isinstance(cur, ast.Call) and isinstance(cur.func, ast.Attribute)
            and cur.func.attr in _LV09_LEN_MUTATORS
            and isinstance(cur.func.value, ast.Name)):
        return cur.func.value.id
    return ''
def _lv09_container_mutation_target(cur: ast.AST) -> str | None:
    return _lv09_subscript_base(cur) or _lv09_mutator_receiver(cur) or None
def _lv09_record_name_rebinds(
        cur: ast.AST,
        binds: _Binds,
        anchor: tuple[int, int] | None) -> None:
    for name in _lv09_rebound_names(cur):
        _lv09_record(binds, name, (*_lv09_pos(cur, anchor), None))
def _lv09_record_container_muts(
        cur: ast.AST,
        binds: _Binds,
        anchor: tuple[int, int] | None) -> None:
    target = _lv09_container_mutation_target(cur)
    if target is not None:
        _lv09_record(binds, target, (*_lv09_pos(cur, anchor), None))
def _lv09_record_import_bindings(cur: ast.AST, binds: _Binds) -> None:
    for alias in cur.names:
        _lv09_record(binds, alias.asname or alias.name.split('.')[0],
                     (cur.lineno, cur.col_offset, None))
def _lv09_enter_nested_scope(cur: ast.AST, binds: _Binds) -> None:
    if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        _lv09_record(binds, cur.name, (cur.lineno, cur.col_offset, None))
    _lv09_invalidate_scope_body(cur, (cur.lineno, cur.col_offset), binds)
def _lv09_invalidate_scope_body(
        definition: ast.AST, anchor: tuple[int, int],
        binds: _Binds) -> None:
    scope_parents = parent_map_of(definition)
    owner_facts: dict[int, tuple[set[int], set[str]]] = {}
    for sub in walk_nodes(definition):
        if isinstance(sub, (ast.Nonlocal, ast.Global)):
            for nm in sub.names:
                _lv09_record(binds, nm, (*anchor, None))
            continue
        target = _lv09_container_mutation_target(sub)
        if target is None:
            continue
        owner = nearest_scope(scope_parents, sub)
        if isinstance(owner, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            facts = owner_facts.get(id(owner))
            if facts is None:
                facts = (definition_outer_node_ids(owner),
                         scope_local_bindings(owner))
                owner_facts[id(owner)] = facts
            if id(sub) not in facts[0] and target in facts[1]:
                continue
        _lv09_record(binds, target, (*anchor, None))
def _lv09_invalidate_stores(
        stmt: ast.AST, binds: _Binds,
        anc: ast.AST | None = None) -> None:
    stack: list[tuple[ast.AST, tuple[int, int] | None]] = [(stmt, None)]
    while stack:
        cur, comp_anchor = stack.pop()
        if isinstance(cur, _LV09_MARKER_NODES):
            continue
        if (isinstance(cur, ast.Assign)
                and _lv09_static_value_len(cur.value) is not None):
            _lv09_record_assign_stmt(cur, binds)
            continue
        if (isinstance(cur, ast.AnnAssign)
                and isinstance(cur.target, ast.Name)
                and _lv09_static_value_len(cur.value) is not None
                and anc is not None):
            _lv09_record_annassign_stmt(cur, anc, binds)
            continue
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef, ast.Lambda)):
            _lv09_enter_nested_scope(cur, binds)
            continue
        if isinstance(cur, (ast.Import, ast.ImportFrom)):
            _lv09_record_import_bindings(cur, binds)
            continue
        if _lv09_push_comp_children(cur, stack, comp_anchor):
            continue
        _lv09_record_name_rebinds(cur, binds, comp_anchor)
        _lv09_record_container_muts(cur, binds, comp_anchor)
        stack.extend((child, comp_anchor)
                     for child in ast.iter_child_nodes(cur))
def _lv09_lambda_walrus_targets(lam: ast.Lambda) -> set[str]:
    out: set[str] = set()
    stack: list[ast.AST] = [lam.body]
    while stack:
        cur = stack.pop()
        if (isinstance(cur, ast.NamedExpr)
                and isinstance(cur.target, ast.Name)):
            out.add(cur.target.id)
            stack.extend(reversed(list(ast.iter_child_nodes(cur))))
            continue
        if isinstance(cur, ast.Lambda):
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))
    return out
def _lv09_collect_comp_targets(gens: list[ast.AST]) -> set[str]:
    targets: set[str] = set()
    for gen in gens:
        targets.update(name for name, _lineno
                       in target_store_names(gen.target, 0))
    return targets
def _lv09_comp_path_is_outer_iter(
        comp: ast.AST, path_child: ast.AST,
        gen_child: dict[int, ast.AST]) -> bool:
    if not isinstance(path_child, ast.comprehension):
        return False
    gens = list(getattr(comp, 'generators', []))
    for j, gen in enumerate(gens):
        if gen is path_child:
            return j == 0 and gen_child.get(id(gen)) is gen.iter
    return False
def _lv09_comp_is_output_position(comp: ast.AST, path_child: ast.AST) -> bool:
    if path_child is getattr(comp, 'elt', None):
        return True
    return (isinstance(comp, ast.DictComp)
            and path_child in (comp.key, comp.value))
def _lv09_comp_shadowed_names(comp: ast.AST, path_child: ast.AST,
                               gen_child: dict[int, ast.AST]) -> set[str]:
    gens = list(getattr(comp, 'generators', []))
    if not gens or path_child is None:
        return set()
    all_targets = _lv09_collect_comp_targets(gens)
    if _lv09_comp_is_output_position(comp, path_child):
        return all_targets
    if isinstance(path_child, ast.comprehension):
        for index, gen in enumerate(gens):
            if gen is not path_child:
                continue
            child = gen_child.get(id(gen))
            if child is gen.iter:
                return _lv09_collect_comp_targets(gens[:index])
            if child in gen.ifs:
                return _lv09_collect_comp_targets(gens[:index + 1])
        return all_targets
    return all_targets
def _lv09_comp_escapes_class_scope(comp: ast.AST, path_child: ast.AST,
                                    gen_child: dict[int, ast.AST]) -> bool:
    if _lv09_comp_is_output_position(comp, path_child):
        return True
    if isinstance(path_child, ast.comprehension):
        return not _lv09_comp_path_is_outer_iter(comp, path_child, gen_child)
    return True
def _lv09_record_assign_stmt(
        stmt: ast.Assign,
        binds: _Binds) -> None:
    length = _lv09_static_value_len(stmt.value)
    if length is not None:
        for target in stmt.targets:
            if isinstance(target, ast.Name):
                _lv09_record(
                    binds, target.id,
                    (*_lv09_assignment_bind_pos(stmt),
                     length), origin=stmt)
            else:
                _lv09_invalidate_stores(target, binds)
        _lv09_invalidate_stores(stmt.value, binds)
    else:
        _lv09_invalidate_stores(stmt, binds)
def _lv09_record_annassign_stmt(
        stmt: ast.AnnAssign, anc: ast.AST,
        binds: _Binds) -> None:
    if stmt.value is None:
        if (isinstance(anc, (ast.FunctionDef, ast.AsyncFunctionDef))
                and stmt.target.id not in binds):
            # 裸注解不重绑已有值；仅在尚无本地记录时遮蔽外层同名绑定。
            _lv09_record(
                binds, stmt.target.id,
                (stmt.lineno, stmt.col_offset, None))
        return
    length = _lv09_static_value_len(stmt.value)
    if length is not None:
        _lv09_record(
            binds, stmt.target.id,
            (*_lv09_assignment_bind_pos(stmt),
             length), origin=stmt)
        _lv09_invalidate_stores(stmt.value, binds)
    else:
        _lv09_invalidate_stores(stmt, binds)
def _lv09_record_scope_stmt(
        stmt: ast.stmt, anc: ast.AST, binds: _Binds) -> None:
    if isinstance(stmt, ast.Assign):
        _lv09_record_assign_stmt(stmt, binds)
    elif (isinstance(stmt, ast.AnnAssign)
            and isinstance(stmt.target, ast.Name)):
        _lv09_record_annassign_stmt(stmt, anc, binds)
    else:
        _lv09_invalidate_stores(stmt, binds, anc)
def _lv09_collect_scope_binds(
        tree: ast.AST) -> dict[int, _Binds]:
    scope_binds: dict[int, _Binds] = {}
    for anc in walk_nodes(tree):
        if not isinstance(anc, SCOPE_CONTAINERS):
            continue
        binds = scope_binds.setdefault(id(anc), {})
        for stmt in scope_body_stmts(anc):
            _lv09_record_scope_stmt(stmt, anc, binds)
    return scope_binds
def _lv09_scope_body_child(scope: ast.AST, child: ast.AST) -> bool:
    body = getattr(scope, 'body', None)
    return isinstance(body, list) and any(stmt is child for stmt in body)
def _lv09_ancestor_chain(
        node: ast.Call,
        parents: dict[int, ast.AST],
) -> tuple[list[ast.AST], set[str], set[str], bool]:
    lambda_shadowed: set[str] = set()
    comp_shadowed: set[str] = set()
    class_ns_hidden = False
    chain: list[ast.AST] = []
    gen_child: dict[int, ast.AST] = {}
    cur: ast.AST | None = node
    prev: ast.AST = node
    while cur is not None:
        if isinstance(cur, ast.Lambda) and prev is cur.body:
            lambda_shadowed |= param_names(cur)
            lambda_shadowed |= _lv09_lambda_walrus_targets(cur)
            class_ns_hidden = True
        if isinstance(cur, ast.comprehension):
            gen_child[id(cur)] = prev
        if isinstance(cur, _CONTAINER_COMP_NODES):
            comp_shadowed |= _lv09_comp_shadowed_names(cur, prev, gen_child)
            if not class_ns_hidden and _lv09_comp_escapes_class_scope(
                    cur, prev, gen_child):
                class_ns_hidden = True
        if (isinstance(cur, SCOPE_CONTAINERS)
                and (isinstance(cur, ast.Module)
                     or _lv09_scope_body_child(cur, prev))):
            chain.append(cur)
        prev = cur
        cur = parents.get(id(cur))
    return chain, lambda_shadowed, comp_shadowed, class_ns_hidden
def _lv09_lengths_before(
        records: list[_LenRecord], scope: ast.AST,
        znode: ast.Call, parents: dict[int, ast.AST],
) -> tuple[bool, _LenValue | None]:
    zpos = (znode.lineno, znode.col_offset)
    before = sorted(
        (record for record in records if record[:2] < zpos),
        key=lambda record: record[:2])
    if not before:
        return False, None
    dominating = [
        index for index, record in enumerate(before)
        if record[3] is not None
        and (
            _binding_dominates_use(record[3], znode, parents)
            or (
                nearest_scope(parents, record[3])
                is not nearest_scope(parents, znode)
                and _binding_dominates_scope(record[3], scope, parents)
            )
        )
    ]
    reachable = (before[dominating[-1]:] if dominating else before)
    values = {record[2] for record in reachable}
    if None in values:
        return True, None
    lengths = frozenset(value for value in values if value is not None)
    if len(lengths) == 1:
        return True, next(iter(lengths))
    return True, lengths
def _lv09_resolve_scope_binds(
        scope: ast.AST,
        resolved: dict[str, _LenValue | None],
        scope_binds: dict[int, _Binds],
        znode: ast.Call, parents: dict[int, ast.AST]) -> None:
    for nm, records in scope_binds.get(id(scope), {}).items():
        if nm in resolved:
            continue
        found, lengths = _lv09_lengths_before(
            records, scope, znode, parents)
        if found:
            resolved[nm] = lengths
        elif isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            resolved[nm] = None
def _lv09_apply_param_shadows(
        scope: ast.AST, resolved: dict[str, _LenValue | None]) -> None:
    for param in param_names(scope):
        if param not in resolved:
            resolved[param] = None
def _lv09_resolve_scope_lengths(
        chain: list[ast.AST],
        shadowed: set[str],
        class_ns_hidden: bool,
        scope_binds: dict[int, _Binds],
        znode: ast.Call, parents: dict[int, ast.AST],
) -> dict[str, _LenValue | None]:
    resolved: dict[str, _LenValue | None] = dict.fromkeys(shadowed)
    for scope in chain:
        if isinstance(scope, ast.ClassDef) and (
                scope is not chain[0] or class_ns_hidden):
            continue
        _lv09_resolve_scope_binds(
            scope, resolved, scope_binds, znode, parents)
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _lv09_apply_param_shadows(scope, resolved)
    return resolved
def _lv09_is_builtin_zip_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == 'zip'
            and len(node.args) >= 2)
def _immediate_expr_nodes(root: ast.AST) -> list[ast.AST]:
    nodes: list[ast.AST] = []
    stack: list[ast.AST] = [root]
    while stack:
        cur = stack.pop()
        nodes.append(cur)
        if isinstance(cur, ast.Lambda):
            args = cur.args
            children = [*args.defaults,
                        *(item for item in args.kw_defaults if item is not None)]
        elif isinstance(cur, ast.GeneratorExp):
            children = ([cur.generators[0].iter] if cur.generators else [])
        else:
            children = list(ast.iter_child_nodes(cur))
        stack.extend(reversed(children))
    return nodes
def _lv09_apply_namedexpr_side_effects(
        arg: ast.AST, value: _LenValue,
        bindings: dict[str, _LenValue]) -> None:
    for sub in _immediate_expr_nodes(arg):
        if (isinstance(sub, ast.NamedExpr) and sub is not arg
                and isinstance(sub.target, ast.Name)):
            bindings.pop(sub.target.id, None)
    if isinstance(arg, ast.NamedExpr) and isinstance(arg.target, ast.Name):
        bindings[arg.target.id] = value
def _lv09_static_arg_lens(
        args: list[ast.AST], resolved: dict[str, _LenValue | None],
        node: ast.AST, parents: dict[int, ast.AST],
) -> list[frozenset[int]] | None:
    bindings: dict[str, _LenValue] = {
        nm: length for nm, length in resolved.items()
        if length is not None}
    values: list[_LenValue] = []
    for arg in args:
        value = _lv09_literal_len(arg, bindings, node, parents)
        if value is None:
            return None
        values.append(value)
        _lv09_apply_namedexpr_side_effects(arg, value, bindings)
    return [frozenset({value}) if isinstance(value, int) else value
            for value in values]
def _lv09_static_args_or_none(
        node: ast.Call, resolved: dict[str, _LenValue | None],
        parents: dict[int, ast.AST]) -> list[int] | None:
    if node.keywords:
        return None
    possible = _lv09_static_arg_lens(node.args, resolved, node, parents)
    if possible is None:
        return None
    multi = [index for index, values in enumerate(possible) if len(values) > 1]
    if not multi:
        lens = [next(iter(values)) for values in possible]
        return None if len(set(lens)) <= 1 else lens
    if len(multi) != 1:
        repeated_args = [node.args[index] for index in multi]
        if (not all(isinstance(arg, ast.Name) for arg in repeated_args)
                or len({arg.id for arg in repeated_args}) != 1):
            return None
        shared = set(possible[multi[0]])
        for index in multi[1:]:
            shared.intersection_update(possible[index])
        witness = [next(iter(values)) for values in possible]
        for length in sorted(shared):
            for index in multi:
                witness[index] = length
            if len(set(witness)) > 1:
                return list(witness)
        return None
    witness = [next(iter(values)) for values in possible]
    variable = multi[0]
    for length in sorted(possible[variable]):
        witness[variable] = length
        if len(set(witness)) > 1:
            return list(witness)
    return None
def _lv09_issue(node: ast.AST, lens: list[int], filepath: Any,
                src_lines: list[str]) -> dict[str, Any]:
    return make_issue(
        'LV-09', 'P2', 'data_integrity', filepath, node.lineno,
        f'zip 实参列表长度不等（{lens}）：按最短静默截断',
        (
            f'zip 的字面量实参长度为 {lens}，不齐——zip 默认丢弃'
            f'较长列表尾部数据，配对结果静默缩水且无任何告警。'
            f'应显式声明意图：等长配对用 strict=True（不齐时 '
            f'ValueError 响亮失败），有意截断写 strict=False '
            f'并加注释说明。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：配对数据源长度不齐，zip 默认静默截断。\n'
            '修复策略：``zip(a, b, strict=True)``（等长契约，不齐'
            '响亮报错）；数据本身允许缺失时先对齐/补齐再 zip。\n'
            '参考标准：Python zip 默认按最短输入截断及 strict 参数契约'
        ),
        'zip-unequal-literal-truncation',
    )
def check_LV09(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    if not isinstance(tree, ast.AST):
        return issues
    src_lines = source_lines(source)
    scope_binds = _lv09_collect_scope_binds(tree)
    parents = parent_map_of(tree)
    for node in walk_nodes(tree):
        if not _lv09_is_builtin_zip_call(node):
            continue
        chain, lambda_shadowed, comp_shadowed, class_ns_hidden = (
            _lv09_ancestor_chain(node, parents))
        resolved = _lv09_resolve_scope_lengths(
            chain, lambda_shadowed | comp_shadowed,
            class_ns_hidden, scope_binds, node, parents)
        if 'zip' in resolved:
            continue
        lens = _lv09_static_args_or_none(node, resolved, parents)
        if lens is None:
            continue
        issues.append(_lv09_issue(node, lens, filepath, src_lines))
    return issues
def _len_arg_name(call_node: ast.AST) -> str | None:
    arg = _len_arg_expr(call_node)
    return arg.id if isinstance(arg, ast.Name) else None
def _len_arg_expr(call_node: ast.AST) -> ast.expr | None:
    if not isinstance(call_node, ast.Call) or call_node.keywords:
        return None
    arg = bare_single_arg_call(call_node, 'len')
    if not isinstance(arg, (ast.Name, ast.Subscript, ast.List, ast.Tuple,
                            ast.Set, ast.Dict, ast.Constant)):
        return None
    return arg
_SHRINK_METHODS = frozenset({
    'clear', 'pop', 'popitem', 'remove', 'discard',
    'difference_update', 'intersection_update',
    'symmetric_difference_update',
})
def _aligned_assignment_pairs(
        target: ast.AST, value: ast.AST,
) -> list[tuple[ast.AST, ast.AST]] | None:
    pairs = aligned_unpack_pairs(target, value)
    if pairs is not None:
        return pairs
    pack_nodes = (ast.Tuple, ast.List)
    if (not isinstance(target, pack_nodes)
            or not isinstance(value, pack_nodes)
            or any(isinstance(item, ast.Starred) for item in value.elts)):
        return None
    star_indexes = [index for index, item in enumerate(target.elts)
                    if isinstance(item, ast.Starred)]
    if len(star_indexes) != 1:
        return None
    star_index = star_indexes[0]
    trailing = len(target.elts) - star_index - 1
    if len(value.elts) < len(target.elts) - 1:
        return None
    return [
        *zip(target.elts[:star_index], value.elts[:star_index], strict=True),
        *((target.elts[len(target.elts) - trailing + offset],
           value.elts[len(value.elts) - trailing + offset])
          for offset in range(trailing)),
    ]
def _bound_values_for_name(
        target: ast.AST, value: ast.AST, name: str) -> list[ast.AST]:
    if isinstance(target, ast.Name):
        return [value] if target.id == name else []
    pairs = _aligned_assignment_pairs(target, value)
    if pairs is None:
        return []
    return [bound for subtarget, subvalue in pairs
            for bound in _bound_values_for_name(subtarget, subvalue, name)]
def _mutates_name(candidate: ast.AST, name: str) -> bool:
    def _binds(target: ast.AST) -> bool:
        return any(bound == name
                   for bound, _line in target_store_names(target, 0))
    if name in capture_binding_names(candidate):
        return True
    if isinstance(candidate, ast.NamedExpr):
        return (_binds(candidate.target)
                and not _nonempty_literal(candidate.value))
    if isinstance(candidate, (ast.Import, ast.ImportFrom)):
        return any((alias.asname or alias.name.split('.')[0]) == name
                   for alias in candidate.names)
    if isinstance(candidate, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)):
        return candidate.name == name
    if isinstance(candidate, ast.Assign):
        for target in candidate.targets:
            if _binds(target):
                values = _bound_values_for_name(
                    target, candidate.value, name)
                if not values or not _nonempty_literal(values[-1]):
                    return True
            elif (isinstance(target, ast.Subscript)
                  and isinstance(target.value, ast.Name)
                  and target.value.id == name
                  and isinstance(target.slice, ast.Slice)):
                return not _nonempty_literal(candidate.value)
        return False
    if isinstance(candidate, ast.AnnAssign):
        if candidate.value is not None and _binds(candidate.target):
            values = _bound_values_for_name(
                candidate.target, candidate.value, name)
            return not values or not _nonempty_literal(values[-1])
        return (candidate.value is not None
                and isinstance(candidate.target, ast.Subscript)
                and isinstance(candidate.target.value, ast.Name)
                and candidate.target.value.id == name
                and isinstance(candidate.target.slice, ast.Slice)
                and not _nonempty_literal(candidate.value))
    if isinstance(candidate, ast.AugAssign):
        if _binds(candidate.target):
            return not isinstance(candidate.op, ast.Add)
        return (isinstance(candidate.target, ast.Subscript)
                and isinstance(candidate.target.value, ast.Name)
                and candidate.target.value.id == name
                and isinstance(candidate.target.slice, ast.Slice)
                and not isinstance(candidate.op, ast.Add))
    if isinstance(candidate, ast.Delete):
        return any(
            (isinstance(target, ast.Name) and target.id == name)
            or (isinstance(target, ast.Subscript)
                and isinstance(target.value, ast.Name)
                and target.value.id == name)
            for target in candidate.targets)
    if isinstance(candidate, (ast.For, ast.AsyncFor)):
        return _binds(candidate.target)
    if isinstance(candidate, (ast.With, ast.AsyncWith)):
        return any(
            item.optional_vars is not None and _binds(item.optional_vars)
            for item in candidate.items)
    return bool(
        isinstance(candidate, ast.Call)
        and isinstance(candidate.func, ast.Attribute)
        and candidate.func.attr in _SHRINK_METHODS
        and isinstance(candidate.func.value, ast.Name)
        and candidate.func.value.id == name)
def _class_body_side_effect_in_scope(
        candidate: ast.AST, name: str, scope: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    candidate_scope = _effective_scope(candidate, parent)
    if not isinstance(candidate_scope, ast.ClassDef) or isinstance(
            scope, ast.ClassDef):
        return False
    outer_declared = any(
        isinstance(node, (ast.Global, ast.Nonlocal)) and name in node.names
        for stmt in candidate_scope.body
        for node in iter_nodes_outside(stmt))
    if not outer_declared and name in scope_local_bindings(candidate_scope):
        return False
    owner = nearest_scope(parent, candidate_scope)
    while owner is not None and owner is not scope:
        if isinstance(owner, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            return False
        owner = nearest_scope(parent, owner)
    return owner is scope
def _binding_invalidated_since(
        start: ast.AST, name: str, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    scope = _effective_scope(node, parent)
    if scope is None:
        return False
    root = _tree_root(node, parent)
    start_pos = (start.lineno, start.col_offset)
    end_pos = (node.lineno, node.col_offset)
    for candidate in walk_nodes(root):
        if candidate is start or candidate is node:
            continue
        pos = (getattr(candidate, 'lineno', 0),
               getattr(candidate, 'col_offset', 0))
        if not (start_pos < pos < end_pos):
            continue
        candidate_scope = _effective_scope(candidate, parent)
        if (candidate_scope is not scope
                and not _class_body_side_effect_in_scope(
                    candidate, name, scope, parent)):
            continue
        if _mutates_name(candidate, name):
            return True
    return False
def _child_under(
        ancestor: ast.AST, node: ast.AST,
        parent: dict[int, ast.AST]) -> ast.AST | None:
    cur: ast.AST | None = node
    while cur is not None:
        owner = parent.get(id(cur))
        if owner is ancestor:
            return cur
        cur = owner
    return None
def _pattern_irrefutable(pattern: ast.pattern) -> bool:
    if isinstance(pattern, ast.MatchAs):
        return (pattern.pattern is None
                or _pattern_irrefutable(pattern.pattern))
    if isinstance(pattern, ast.MatchOr):
        return any(_pattern_irrefutable(sub)
                   for sub in pattern.patterns)
    return False
def _loop_guarantees_once(loop: ast.AST,
                               parent: dict[int, ast.AST]) -> bool:
    if isinstance(loop, (ast.For, ast.AsyncFor)):
        return (_nonempty_literal(loop.iter)
                or _range_nonempty(loop, loop.iter, parent))
    test = getattr(loop, 'test', None)
    return (isinstance(test, ast.Constant) and bool(test.value)
            and not isinstance(test.value, (str, bytes)))
_LEN_MIRROR_OPS = {ast.Gt: ast.Lt, ast.GtE: ast.LtE,
                    ast.Lt: ast.Gt, ast.LtE: ast.GtE}
def _unwrap_walrus(node: ast.AST) -> ast.AST:
    # ``(n := expr)`` 表达式的真值即 ``expr`` 的真值：守卫判定须穿透海象外壳。
    while isinstance(node, ast.NamedExpr):
        node = node.value
    return node
def _len_const_compare(
        compare: ast.Compare, name: str,
        parent: dict[int, ast.AST] | None = None,
) -> tuple[ast.cmpop, int] | None:
    if len(compare.ops) != 1:
        return None
    left = _unwrap_walrus(compare.left)
    right = _unwrap_walrus(compare.comparators[0])
    op = compare.ops[0]
    if _len_arg_name(left) == name:
        if (parent is not None
                and shadowed_binding_at(left, 'len', parent, {})):
            return None
        number = int_literal(right)
        return None if number is None else (op, number)
    if _len_arg_name(right) == name:
        if (parent is not None
                and shadowed_binding_at(right, 'len', parent, {})):
            return None
        number = int_literal(left)
        mirrored = _LEN_MIRROR_OPS.get(type(op), type(op))()
        return None if number is None else (mirrored, number)
    return None
def _len_compare_holds(
        compare: ast.Compare, name: str, truth: bool,
        parent: dict[int, ast.AST] | None = None) -> bool:
    parsed = _len_const_compare(compare, name, parent)
    if parsed is None:
        return False
    op, n = parsed
    if isinstance(op, ast.Eq):
        return (truth and n >= 1) or (not truth and n == 0)
    if isinstance(op, ast.NotEq):
        return (truth and n == 0) or (not truth and n >= 1)
    if isinstance(op, ast.Gt):
        return truth and n >= 0
    if isinstance(op, ast.GtE):
        return truth and n >= 1
    if isinstance(op, ast.Lt):
        return (not truth) and n >= 1
    if isinstance(op, ast.LtE):
        return (not truth) and n >= 0
    return False
def _nonempty_holds(
        test: ast.AST, name: str, truth: bool,
        parents: dict[int, ast.AST]) -> bool:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _nonempty_holds(test.operand, name, not truth, parents)
    if isinstance(test, ast.NamedExpr):
        return (_nonempty_holds(test.target, name, truth, parents)
                or _nonempty_holds(test.value, name, truth, parents))
    if isinstance(test, ast.Name):
        return truth and test.id == name
    if isinstance(test, ast.Call):
        if not truth or test.keywords:
            return False
        return (isinstance(test.func, ast.Name)
                and test.func.id in ('len', 'bool')
                and len(test.args) == 1
                and isinstance(test.args[0], ast.Name)
                and test.args[0].id == name
                and not shadowed_binding_at(
                    test, test.func.id, parents, {}))
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        return _len_compare_holds(test, name, truth, parents)
    if isinstance(test, ast.BoolOp):
        if isinstance(test.op, ast.And) and truth:
            return any(_nonempty_holds(v, name, True, parents)
                       for v in test.values)
        if isinstance(test.op, ast.Or) and not truth:
            return any(_nonempty_holds(v, name, False, parents)
                       for v in test.values)
    if (truth and isinstance(test, (ast.ListComp, ast.SetComp,
                                    ast.DictComp))):
        return (bool(test.generators)
                and isinstance(test.generators[0].iter, ast.Name)
                and test.generators[0].iter.id == name)
    return False
def _post_if_truth(stmt: ast.If) -> bool | None:
    body_exit = block_exits(stmt.body)
    orelse_exit = bool(stmt.orelse) and block_exits(stmt.orelse)
    if body_exit and orelse_exit:
        return None
    if body_exit:
        return False
    if orelse_exit:
        return True
    return None
def _loop_body_breaks(body: list[ast.stmt]) -> bool:
    stack: list[ast.AST] = list(body)
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Break):
            return True
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda, ast.ClassDef)):
            continue
        if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            continue
        stack.extend(ast.iter_child_nodes(node))
    return False
def _prior_guard_truth(stmt: ast.AST) -> bool | None:
    if isinstance(stmt, ast.If):
        return _post_if_truth(stmt)
    if isinstance(stmt, ast.Assert):
        return True
    if isinstance(stmt, ast.While) and not _loop_body_breaks(stmt.body):
        return False
    return None
def _comp_prior_guards(
        comp: ast.AST, path_child: ast.AST,
        gen_child: dict[int, ast.AST]) -> list[ast.AST]:
    gens = list(getattr(comp, 'generators', []))
    if not gens or path_child is None:
        return []
    if _lv09_comp_is_output_position(comp, path_child):
        return [guard for gen in gens for guard in gen.ifs]
    if not isinstance(path_child, ast.comprehension):
        return []
    for index, gen in enumerate(gens):
        if gen is not path_child:
            continue
        previous = [guard for prev in gens[:index] for guard in prev.ifs]
        child = gen_child.get(id(gen))
        if child is gen.iter or child is gen.target:
            return previous
        if child is not None:
            for stop, guard in enumerate(gen.ifs):
                if guard is child:
                    return previous + list(gen.ifs[:stop])
        return previous
    return []
def _guarded_on_path(
        node: ast.AST, parents: dict[int, ast.AST],
        holds: Callable[[ast.AST, bool], bool],
        invalidated: Callable[[ast.AST], bool] | None = None,
        shadowed_names: frozenset[str] = _EMPTY_VISITS,
) -> bool:
    cur: ast.AST = node
    prev: ast.AST = node
    gen_child: dict[int, ast.AST] = {}
    while True:
        parent = parents.get(id(cur))
        if parent is None:
            return False
        if isinstance(cur, ast.comprehension):
            gen_child[id(cur)] = prev
        if isinstance(cur, _CONTAINER_COMP_NODES):
            for guard in _comp_prior_guards(cur, prev, gen_child):
                if (holds(guard, True)
                        and not (invalidated is not None
                                 and invalidated(guard))):
                    return True
            if shadowed_names.intersection(
                    _lv09_comp_shadowed_names(cur, prev, gen_child)):
                return False
        if isinstance(parent, ast.BoolOp):
            index = next((i for i, value in enumerate(parent.values)
                          if value is cur), -1)
            if index > 0:
                guard_truth = isinstance(parent.op, ast.And)
                for guard in parent.values[:index]:
                    if (holds(guard, guard_truth)
                            and not (invalidated is not None
                                     and invalidated(guard))):
                        return True
        truth = branch_truth(parent, cur)
        if (truth is not None and holds(parent.test, truth)
                and not (invalidated is not None and invalidated(parent))):
            return True
        siblings = stmt_siblings(parent, cur)
        if siblings is not None:
            cur_idx = next((i for i, stmt in enumerate(siblings)
                            if stmt is cur), -1)
            for guard in siblings[:cur_idx]:
                guard_truth = _prior_guard_truth(guard)
                if (guard_truth is not None
                        and holds(guard.test, guard_truth)
                        and not (invalidated is not None
                                 and invalidated(guard))):
                    return True
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if _lv09_scope_body_child(parent, cur):
                return False
        elif isinstance(parent, ast.Lambda):
            if parent.body is cur:
                return False
        elif isinstance(parent, ast.Module):
            return False
        prev = cur
        cur = parent
def _enclosing_function(
        node: ast.AST, parent: dict[int, ast.AST]) -> ast.AST | None:
    cur = parent.get(id(node))
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return cur
        cur = parent.get(id(cur))
    return None
def _private_callable(
        fn: ast.AST, parent: dict[int, ast.AST]) -> tuple[str, int, str] | None:
    if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return None
    owner = nearest_scope(parent, fn)
    is_method = isinstance(owner, ast.ClassDef)
    if fn.name == '__init__':
        if not is_method or not owner.name.startswith('_'):
            return None
        return owner.name, 1, 'constructor'
    if not fn.name.startswith('_'):
        return None
    is_static = any(
        (isinstance(dec, ast.Name) and dec.id == 'staticmethod')
        or (isinstance(dec, ast.Attribute) and dec.attr == 'staticmethod')
        for dec in fn.decorator_list)
    kind = 'method' if is_method else 'function'
    return fn.name, int(is_method and not is_static), kind
def _matching_calls(tree: ast.AST, name: str, kind: str) -> list[ast.Call]:
    calls: list[ast.Call] = []
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        is_name = isinstance(node.func, ast.Name) and node.func.id == name
        is_attribute = (isinstance(node.func, ast.Attribute)
                        and node.func.attr == name)
        if ((kind == 'function' and is_name)
                or (kind == 'method' and is_attribute)
                or (kind == 'constructor' and (is_name or is_attribute))):
            calls.append(node)
    return calls
def _actual_arg(
        call: ast.Call, fn: ast.AST, param: str, drop: int) -> ast.AST | None:
    args = fn.args
    positional = args.posonlyargs + args.args
    pos = next((i for i, arg in enumerate(positional) if arg.arg == param), None)
    if pos is not None:
        actual_pos = pos - drop
        if (actual_pos >= 0 and actual_pos < len(call.args)
                and not any(isinstance(arg, ast.Starred) for arg in call.args)):
            return call.args[actual_pos]
    elif not any(arg.arg == param for arg in args.kwonlyargs):
        return None
    if any(kw.arg is None for kw in call.keywords):
        return None
    return next((kw.value for kw in call.keywords if kw.arg == param), None)
def _expression_root_names(expr: ast.AST) -> set[str]:
    return {sub.id for sub in iter_nodes_outside(expr)
            if isinstance(sub, ast.Name)
            and isinstance(sub.ctx, ast.Load)}
def _expression_guard_invalidated(
        guard: ast.AST, subject: ast.AST, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    return any(_binding_invalidated_since(guard, name, node, parent)
               for name in _expression_root_names(subject))
def _expression_nonempty_holds(
        test: ast.AST, subject: ast.AST, truth: bool) -> bool:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _expression_nonempty_holds(test.operand, subject, not truth)
    if isinstance(test, ast.NamedExpr):
        return _expression_nonempty_holds(test.value, subject, truth)
    if same_expr(test, subject):
        return truth
    if isinstance(test, ast.BoolOp):
        if isinstance(test.op, ast.And) and truth:
            return any(_expression_nonempty_holds(value, subject, True)
                       for value in test.values)
        if isinstance(test.op, ast.Or) and not truth:
            return any(_expression_nonempty_holds(value, subject, False)
                       for value in test.values)
    return False
def _expression_condition_guarded(
        node: ast.AST, subject: ast.AST, parents: dict[int, ast.AST],
        invalidated: Callable[[ast.AST], bool] | None = None) -> bool:
    return _guarded_on_path(
        node, parents,
        lambda test, truth: _expression_nonempty_holds(
            test, subject, truth),
        invalidated, frozenset(_expression_root_names(subject)))
def _tree_root(node: ast.AST, parent: dict[int, ast.AST]) -> ast.AST:
    root = node
    while parent.get(id(root)) is not None:
        root = parent[id(root)]
    return root
def _scope_chain(
        node: ast.AST, parent: dict[int, ast.AST]) -> list[ast.AST]:
    raw: list[ast.AST] = []
    scope = nearest_scope(parent, node)
    while scope is not None:
        raw.append(scope)
        scope = nearest_scope(parent, scope)
    chain: list[ast.AST] = []
    for scope in raw:
        if isinstance(scope, ast.Lambda):
            if _child_under(scope, node, parent) is not scope.body:
                continue
        elif isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef)):
            child = _child_under(scope, node, parent)
            body = getattr(scope, 'body', None)
            if (child is not None and isinstance(body, list)
                    and not any(child is stmt for stmt in body)):
                continue
        if (isinstance(scope, ast.ClassDef)
                and any(isinstance(item, (ast.FunctionDef,
                                          ast.AsyncFunctionDef,
                                          ast.Lambda))
                        for item in chain)):
            continue
        chain.append(scope)
    return chain
def _effective_scope(
        node: ast.AST, parent: dict[int, ast.AST]) -> ast.AST | None:
    chain = _scope_chain(node, parent)
    return chain[0] if chain else None
def _binding_scope(
        node: ast.AST, name: str, parent: dict[int, ast.AST]) -> ast.AST | None:
    for scope in _scope_chain(node, parent):
        if name in scope_local_bindings(scope):
            return scope
    return None
def _latest_assignment(
        node: ast.AST, name: str, parent: dict[int, ast.AST]) -> ast.AST | None:
    candidates = _assignment_candidates(node, name, parent)
    return candidates[0] if candidates else None
def _assignment_candidates(
        node: ast.AST, name: str, parent: dict[int, ast.AST]) -> list[ast.AST]:
    """``node`` 之前对 ``name`` 的全部赋值，按源码位置从近到远排序。

    与 ``_latest_assignment`` 同一判定口径（单一 Name 目标的 Assign / 带值
    AnnAssign / NamedExpr，且与使用点同作用域）。最近一次赋值不支配使用点时
    （try 体、条件分支、不保证执行的循环体），调用方可回退到更早的赋值。
    """
    scope = _binding_scope(node, name, parent)
    if scope is None:
        return []
    root = _tree_root(node, parent)
    position = (node.lineno, node.col_offset)
    candidates = []
    for candidate in walk_nodes(root):
        if isinstance(candidate, ast.Assign):
            targets = candidate.targets
        elif (isinstance(candidate, ast.NamedExpr)
              or (isinstance(candidate, ast.AnnAssign)
                  and candidate.value is not None)):
            targets = [candidate.target]
        else:
            continue
        if (len(targets) != 1
                or not isinstance(targets[0], ast.Name)
                or targets[0].id != name
                or (candidate.lineno, candidate.col_offset) >= position):
            continue
        if nearest_scope(parent, candidate) is not scope:
            continue
        candidates.append(candidate)
    candidates.sort(key=lambda item: (item.lineno, item.col_offset),
                    reverse=True)
    return candidates
def _same_statement_block(
        owner: ast.AST, binding_child: ast.AST, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    use_child = _child_under(owner, node, parent)
    if use_child is None:
        return False
    for _field_name, field_value in ast.iter_fields(owner):
        if not isinstance(field_value, list):
            continue
        if (any(item is binding_child for item in field_value)
                and any(item is use_child for item in field_value)):
            return True
    return False
def _binding_dominates_use(
        binding: ast.AST, node: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    scope = nearest_scope(parent, binding)
    if scope is None or nearest_scope(parent, node) is not scope:
        return False
    conditional_ancestors = (
        ast.If, ast.IfExp, ast.BoolOp,
        ast.For, ast.AsyncFor, ast.While,
        ast.Match, ast.ExceptHandler, ast.With, ast.AsyncWith,
        *_CONTAINER_COMP_NODES,
        *TRY_NODES,
    )
    cur = binding
    while cur is not scope:
        owner = parent.get(id(cur))
        if owner is None:
            return False
        if owner is scope:
            return True
        if (isinstance(owner, conditional_ancestors)
                and not _same_statement_block(owner, cur, node, parent)):
            return False
        cur = owner
    return False
def _resolved_int(
        node: ast.AST, value: ast.AST,
        parent: dict[int, ast.AST]) -> int | None:
    sign = 1
    seen: set[int] = set()
    while True:
        literal = int_literal(value)
        if literal is not None:
            return sign * literal
        if (isinstance(value, ast.UnaryOp)
                and isinstance(value.op, (ast.USub, ast.UAdd))):
            if isinstance(value.op, ast.USub):
                sign = -sign
            node, value = value, value.operand
            continue
        if not isinstance(value, ast.Name):
            return None
        assignment = _latest_assignment(node, value.id, parent)
        if (assignment is None or assignment is value
                or not _binding_dominates_use(assignment, node, parent)):
            return None
        marker = id(assignment)
        if marker in seen:
            return None
        seen.add(marker)
        node, value = assignment, assignment.value
def _range_length(
        node: ast.AST, value: ast.AST,
        parent: dict[int, ast.AST]) -> int | None:
    if (not isinstance(value, ast.Call)
            or not isinstance(value.func, ast.Name)
            or value.func.id != 'range'
            or value.keywords
            or not 1 <= len(value.args) <= 3
            or any(isinstance(arg, ast.Starred) for arg in value.args)
            or shadowed_binding_at(node, 'range', parent, {})):
        return None
    bounds = [_resolved_int(node, arg, parent) for arg in value.args]
    if any(bound is None for bound in bounds):
        return None
    try:
        return len(range(*bounds))
    except (TypeError, ValueError, OverflowError):
        return None
def _positive_int_holds(
        test: ast.AST, subject: ast.AST, truth: bool) -> bool:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _positive_int_holds(test.operand, subject, not truth)
    if isinstance(test, ast.NamedExpr):
        return _positive_int_holds(test.value, subject, truth)
    if isinstance(test, ast.BoolOp):
        if isinstance(test.op, ast.And) and truth:
            return any(_positive_int_holds(v, subject, True)
                       for v in test.values)
        if isinstance(test.op, ast.Or) and not truth:
            return any(_positive_int_holds(v, subject, False)
                       for v in test.values)
        return False
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1):
        return False
    left, right = test.left, test.comparators[0]
    op = test.ops[0]
    number = int_literal(right)
    if not same_expr(left, subject):
        number = int_literal(left)
        if not same_expr(right, subject) or number is None:
            return False
        left, right = right, left
        op = _LEN_MIRROR_OPS.get(type(op), type(op))()
    if number is None:
        return False
    if isinstance(op, ast.Gt):
        return truth and number >= 0
    if isinstance(op, ast.GtE):
        return truth and number >= 1
    if isinstance(op, ast.Lt):
        return (not truth) and number >= 1
    if isinstance(op, ast.LtE):
        return (not truth) and number >= 0
    if isinstance(op, ast.Eq):
        return truth and number >= 1
    if isinstance(op, ast.NotEq):
        return (not truth) and number >= 1
    return False
def _range_nonempty(
        node: ast.AST, value: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    length = _range_length(node, value, parent)
    if length is not None:
        return length > 0
    if (not isinstance(value, ast.Call)
            or not isinstance(value.func, ast.Name)
            or value.func.id != 'range'
            or value.keywords
            or any(isinstance(arg, ast.Starred) for arg in value.args)
            or not 1 <= len(value.args) <= 3
            or shadowed_binding_at(node, 'range', parent, {})):
        return False
    if len(value.args) == 1:
        return _guarded_on_path(
            node, parent,
            lambda test, truth: _positive_int_holds(
                test, value.args[0], truth))
    if len(value.args) == 3:
        step = _resolved_int(node, value.args[2], parent)
        if step is None or step <= 0:
            return False
    start = _resolved_int(node, value.args[0], parent)
    return (start == 0 and _guarded_on_path(
        node, parent,
        lambda test, truth: _positive_int_holds(
            test, value.args[1], truth)))
def _nonempty_container(node: ast.AST) -> bool:
    if isinstance(node, ast.Dict):
        return bool(node.keys) and all(k is not None for k in node.keys)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        for elt in node.elts:
            if not isinstance(elt, ast.Starred):
                return True
            if _nonempty_literal(elt.value):
                return True
        return False
    return False
def _binding_dominates_scope(
        binding: ast.AST, scope: ast.AST,
        parent: dict[int, ast.AST]) -> bool:
    conditional_ancestors = (
        ast.If, ast.IfExp, ast.BoolOp,
        ast.For, ast.AsyncFor, ast.While,
        ast.Match, ast.ExceptHandler, ast.With, ast.AsyncWith,
        *_CONTAINER_COMP_NODES,
        *TRY_NODES,
    )
    cur = binding
    while cur is not scope:
        owner = parent.get(id(cur))
        if owner is None:
            return False
        if owner is scope:
            return True
        if isinstance(owner, conditional_ancestors):
            return False
        cur = owner
    return False
def _nonempty_literal(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant) and isinstance(node.value, (str, bytes)):
        return bool(node.value)
    return _nonempty_container(node)
def _lv02_target_text(target: ast.AST) -> str:
    if not isinstance(target, (ast.Name, ast.Attribute, ast.Subscript,
                              ast.Tuple, ast.List)):
        return ''
    if not isinstance(target.ctx, ast.Store):
        return ''
    return ast.unparse(target)
def _lv02_target_value_pairs(
        target: ast.AST, value: ast.AST) -> list[tuple[str, ast.expr, bool]]:
    pack_nodes = (ast.Tuple, ast.List)
    if isinstance(target, pack_nodes) and isinstance(value, pack_nodes):
        aligned = _aligned_assignment_pairs(target, value)
        if aligned is None:
            return []
        pairs: list[tuple[str, ast.expr, bool]] = []
        for subtarget, subvalue in aligned:
            pairs.extend(_lv02_target_value_pairs(subtarget, subvalue))
        return pairs
    text = _lv02_target_text(target)
    if not text:
        return []
    return [(text, value, isinstance(target, pack_nodes))]
def _lv02_assignment_values(
        node: ast.AST) -> list[tuple[str, ast.expr, bool]]:
    if isinstance(node, ast.Assign):
        targets = node.targets
        value = node.value
    elif isinstance(node, ast.AnnAssign):
        if node.value is None:
            return []
        targets = [node.target]
        value = node.value
    elif isinstance(node, ast.NamedExpr):
        targets = [node.target]
        value = node.value
    else:
        return []
    pairs: list[tuple[str, ast.expr, bool]] = []
    for target in targets:
        pairs.extend(_lv02_target_value_pairs(target, value))
    return pairs
def _inplace_chain_receiver(value: ast.AST) -> bool:
    return (isinstance(value, ast.Call)
            and isinstance(value.func, ast.Attribute)
            and value.func.attr in INPLACE_MUTATOR_METHODS)
def _lv02_inplace_call_targets(
        node: ast.AST) -> list[tuple[str, str, bool]]:
    hits: list[tuple[str, str, bool]] = []
    for target, original_value, unpacked in _lv02_assignment_values(node):
        value = original_value
        while isinstance(value, ast.NamedExpr):
            value = value.value
        if not _inplace_chain_receiver(value):
            continue
        if _inplace_chain_receiver(value.func.value):
            continue
        hits.append((target, value.func.attr, unpacked))
    return hits
def _lv02_issue(node: ast.AST, target: str, method: str, filepath: Any,
                src_lines: list[str], *, unpacked: bool = False
                ) -> dict[str, Any]:
    if unpacked:
        return make_issue(
            'LV-02', 'P1', 'logic_correctness', filepath, node.lineno,
            f"就地方法 {method}() 返回 None：解包 {target} 即 TypeError",
            (
                f'``{method}()`` 是就地变更方法（原地修改、返回 None），'
                f'``{target} = {method}(...)`` 的解包形态先把右侧求值为 '
                'None，解包即抛 ``TypeError: cannot unpack non-iterable '
                'NoneType object``——赋值从未完成，后续消费全部落空。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：fluent API 思维误用于 Python 就地变更方法，'
                '解包语法放大了「None 不可迭代」的失败面。\n'
                f'修复策略：拆为独立语句（直接 ``items.{method}()`` '
                '后消费 items）；确需多个新对象时改用函数式等价物\n'
                '逐个构造。\n'
                '参考标准：CPython list/dict 就地变更方法返回 None 的契约'
            ),
            'inplace-method-none-assign',
        )
    return make_issue(
        'LV-02', 'P1', 'logic_correctness', filepath, node.lineno,
        f"就地方法 {method}() 返回 None：变量 {target} 将是 None 而非变更后对象",
        (
            f'``{method}()`` 是就地变更方法（原地修改、返回 None），'
            f'赋值所得 {target} 恒为 None——后续任何下标访问/算术/迭代'
            f'消费触发 TypeError。该写法几乎必为笔误：要么意图取变更'
            f'后对象（应直接消费原对象），要么意图取返回值（应改用'
            f'有返回值的 API，如 sorted()/reversed()）。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：fluent API 思维误用于 Python 就地变更方法。\n'
            f'修复策略：直接消费原对象（``items.{method}()`` 后用 '
            f'items）；需要返回值时改用函数式等价物——sort→sorted、'
            'reverse→reversed(list)；append/extend/update 无返回值等价'
            '物，赋值形态本身就是错误。\n'
            '参考标准：CPython list/dict 就地变更方法返回 None 的契约'
        ),
        'inplace-method-none-assign',
    )
def check_LV02(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    for node in walk_ast_nodes(tree):
        for target, method, unpacked in _lv02_inplace_call_targets(node):
            issues.append(_lv02_issue(
                node, target, method, filepath, src_lines,
                unpacked=unpacked))
    return issues
def _lv19_mutable_element(elt: ast.AST) -> bool:
    if isinstance(elt, (ast.List, ast.Dict, ast.Set,
                        ast.ListComp, ast.DictComp, ast.SetComp)):
        return True
    if isinstance(elt, ast.Tuple):
        return any(_lv19_mutable_element(sub) for sub in elt.elts)
    if isinstance(elt, ast.Starred):
        inner = elt.value
        if isinstance(inner, (ast.List, ast.Tuple, ast.Set)):
            return any(_lv19_mutable_element(sub) for sub in inner.elts)
        if isinstance(inner, ast.Dict):
            return False
        return _lv19_mutable_element(inner)
    return (isinstance(elt, ast.BinOp) and isinstance(elt.op, ast.Mult)
            and (isinstance(elt.left, ast.List)
                 or isinstance(elt.right, ast.List)))
def _lv19_shared_mult_side(node: ast.BinOp) -> tuple[ast.List, int | None] | None:
    for lst, cnt in ((node.left, node.right), (node.right, node.left)):
        if not isinstance(lst, ast.List):
            continue
        if not any(_lv19_mutable_element(elt) for elt in lst.elts):
            continue
        count = int_literal(cnt, allow_bool=True)
        if count is None:
            try:
                literal_count = ast.literal_eval(cnt)
            except (ValueError, TypeError, SyntaxError,
                    MemoryError, RecursionError):
                pass
            else:
                if isinstance(literal_count, (int, bool)):
                    count = int(literal_count)
                else:
                    continue
        if count is not None and count < 2:
            continue
        return (lst, count)
    return None
def _lv19_issue(node: ast.BinOp, count: int | None, filepath: Any,
                src_lines: list[str]) -> dict[str, Any]:
    count_desc = str(count) if count is not None else 'n'
    return make_issue(
        'LV-19', 'P1', 'logic_correctness', filepath, node.lineno,
        f'列表乘法复制共享引用：{count_desc} 个位置引用同一可变对象',
        (
            f'``[可变字面量] * {count_desc}`` 产生的 {count_desc} 个'
            f'元素是**同一个可变对象的引用**——任一位置变更'
            f'（append/下标赋值）会同步出现在全部位置：矩阵行共享'
            f'（改一行全变）、桶列表混入（数据静默污染），无任何'
            f'异常信号，是初始化二维结构/桶数组时的高频'
            f'静默 BUG。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：序列乘法复制的是元素引用，可变元素被全部'
            '位置共享。\n'
            '修复策略：改用推导式逐位独立构造 ``[[] for _ in '
            'range(n)]`` / ``[[0] * cols for _ in '
            'range(rows)]``（每轮新建独立对象，标量行 ``[0] '
            '* cols`` 可乘——int 不可变）；嵌套维度的每一层都'
            '必须独立构造，不可用乘法展开可变元素。\n'
            '参考标准：序列乘法复制元素引用（浅拷贝语义）'
        ),
        'mutable-mult-shared-ref',
    )
def check_LV19(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    for node in walk_ast_nodes(tree):
        if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult)):
            continue
        side = _lv19_shared_mult_side(node)
        if side is None:
            continue
        issues.append(_lv19_issue(node, side[1], filepath, src_lines))
    return issues
_LV45_NONE_ATTRIBUTES = frozenset(dir(None))
def check_LV45(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    for node in roots:
        if not isinstance(node, ast.Attribute):
            continue
        inner = node.value
        if not _inplace_chain_receiver(inner):
            continue
        if (isinstance(node.ctx, ast.Load)
                and node.attr in _LV45_NONE_ATTRIBUTES):
            continue
        method = inner.func.attr
        issues.append(make_issue(
            'LV-45', 'P1', 'logic_correctness', filepath, node.lineno,
            f'就地方法 {method}() 链式续接：返回 None，取属性必 AttributeError',
            (
                f'``{method}()`` 是就地变更方法（原地修改、返回 '
                f'None）——``...{method}(...).{node.attr}`` 续接在 None '
                '上取属性，一执行即 ``AttributeError: NoneType has no '
                'attribute``。fluent 链式思维（JS 链/Guava 风格）不适用'
                'Python 内建容器的就地变更方法。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：fluent API 思维误用于返回 None 的就地方法\n'
                '（与 LV-02 赋值形态同一成因链，消费形态不同）。\n'
                '修复策略：拆为独立语句逐个调用'
                f'（``items.{method}(a)`` 换行 ``items.{method}(b)``）；\n'
                '需要链式结果对象时改用函数式等价物（sort→sorted、\n'
                'reverse→reversed，返回新对象可链）。\n'
                '参考标准：CPython list/set/dict 变更方法契约'
                '（mutator 返回 None，NoneType 属性访问即 AttributeError）'
            ),
            'inplace-method-chained-continuation',
        ))
    return issues
_LV22_MUTATORS = INPLACE_MUTATOR_METHODS | frozenset({
    'pop', 'popitem', 'setdefault',
})
def _lv22_target_binds_name(target: ast.AST, name: str) -> bool:
    return any(
        bound == name for bound, _lineno in target_store_names(target, 0))
def _lv22_subscript_nodes(tgt: ast.AST, src_name: str) -> list[ast.Subscript]:
    if isinstance(tgt, (ast.Tuple, ast.List)):
        return [found for sub in tgt.elts
                for found in _lv22_subscript_nodes(sub, src_name)]
    if isinstance(tgt, ast.Starred):
        return _lv22_subscript_nodes(tgt.value, src_name)
    if (isinstance(tgt, ast.Subscript)
            and isinstance(tgt.value, ast.Name)
            and tgt.value.id == src_name):
        return [tgt]
    return []
def _lv22_is_subscript_of(tgt: ast.AST, src_name: str) -> bool:
    return bool(_lv22_subscript_nodes(tgt, src_name))
def _lv22_dominating_literal_value(
        node: ast.AST, name: str,
        parent: dict[int, ast.AST]) -> ast.AST | None:
    assignment = _latest_assignment(node, name, parent)
    if (assignment is None
            or not _binding_dominates_use(assignment, node, parent)):
        return None
    value = assignment.value
    if (isinstance(value, (ast.List, ast.Tuple))
            or (isinstance(value, ast.Constant)
                and isinstance(value.value, (str, bytes)))):
        return value
    return None
def _lv22_rebinds_immutable_literal(
        node: ast.AST, name: str,
        parent: dict[int, ast.AST] | None) -> bool:
    if parent is None or not isinstance(node, ast.AugAssign):
        return False
    value = _lv22_dominating_literal_value(node, name, parent)
    return isinstance(value, ast.Tuple) or (
        isinstance(value, ast.Constant)
        and isinstance(value.value, (str, bytes)))
def _lv22_non_resizing_subscript(sub: ast.Subscript) -> bool:
    if not isinstance(sub.slice, ast.Slice):
        return True
    step = sub.slice.step
    return (step is not None
            and not (isinstance(step, ast.Constant) and step.value is None))
def _lv22_neutral_list_element_writes(
        targets: list[ast.AST], name: str, node: ast.AST,
        parent: dict[int, ast.AST] | None) -> bool:
    if parent is None:
        return False
    subscripts = [found for target in targets
                  for found in _lv22_subscript_nodes(target, name)]
    value = _lv22_dominating_literal_value(node, name, parent)
    # 单元素写入与扩展切片等长替换均不改变被迭代列表的长度。
    return (bool(subscripts) and isinstance(value, ast.List)
            and all(_lv22_non_resizing_subscript(sub) for sub in subscripts))
def _lv22_mutator_func(sub: ast.AST, src_name: str) -> ast.Attribute | None:
    if (isinstance(sub, ast.Call) and isinstance(sub.func, ast.Attribute)
            and sub.func.attr in _LV22_MUTATORS
            and isinstance(sub.func.value, ast.Name)
            and sub.func.value.id == src_name):
        return sub.func
    return None
def _lv22_hit_kind(
        sub: ast.AST, src_name: str,
        parent: dict[int, ast.AST] | None = None) -> tuple[str, int] | None:
    if isinstance(sub, ast.Delete):
        if any(_lv22_is_subscript_of(tgt, src_name) for tgt in sub.targets):
            return 'del 语句', sub.lineno
        return None
    if isinstance(sub, (ast.Assign, ast.AnnAssign)):
        if isinstance(sub, ast.AnnAssign) and sub.value is None:
            return None
        targets = (sub.targets if isinstance(sub, ast.Assign)
                   else [sub.target])
        if any(_lv22_is_subscript_of(tgt, src_name) for tgt in targets):
            if _lv22_neutral_list_element_writes(
                    targets, src_name, sub, parent):
                return None
            return '下标/切片赋值', sub.lineno
        return None
    if isinstance(sub, ast.AugAssign):
        if (isinstance(sub.target, ast.Name)
                and sub.target.id == src_name):
            if _lv22_rebinds_immutable_literal(sub, src_name, parent):
                return None
            return f'{type(sub.op).__name__} 原地更新', sub.lineno
        if _lv22_is_subscript_of(sub.target, src_name):
            if _lv22_neutral_list_element_writes(
                    [sub.target], src_name, sub, parent):
                return None
            return '下标/切片原地更新', sub.lineno
        return None
    func = _lv22_mutator_func(sub, src_name)
    if func is None:
        return None
    return f'{func.attr}() 调用', sub.lineno
def _lv22_issue(src_name: str, hit_kind: str, hit_line: int,
                filepath: Any, src_lines: list) -> dict[str, Any]:
    return make_issue(
        'LV-22', 'P1', 'logic_correctness', filepath, hit_line,
        f'迭代源 {src_name} 在循环体内被修改（{hit_kind}）',
        (
            f'``for ... in {src_name}:`` 的循环体内通过'
            f'{hit_kind}变更迭代源本身——dict/set 迭代中改尺寸'
            f'直接 ``RuntimeError: dictionary changed size '
            f'during iteration``（一执行即崩）；list 迭代中'
            f'pop/remove 使后续轮次位移跳过元素、过滤逻辑'
            f'静默漏删，append/extend 则让迭代器持续看到新元素、'
            f'循环不终止。这是遍历删键/清洗列表/边遍历边收集场景的'
            f'最高频崩溃与静默 BUG 模式。'
        ),
        snippet_of(src_lines, hit_line),
        (
            '根因：直接在迭代源上做增删，破坏了迭代协议的'
            '尺寸不变式。\n'
            f'修复策略：迭代副本、修改原件——'
            f'``for k in list({src_name}): {src_name}.pop(k)``'
            f'（dict）/ ``for x in list({src_name}): '
            f'{src_name}.remove(x)``（list）；或推导式重建'
            f'``{src_name} = [x for x in {src_name} if keep(x)]``'
            '（零原地修改）；dict 键集快照'
            f'``for k in list({src_name}.keys())`` 同口径；'
            '边遍历边收集改为先写入临时容器、循环结束后统一 extend。\n'
            '参考标准：Python 迭代协议尺寸不变式'
            '（B07/B32 编写前注入条目的实时拦截升级）'
        ),
        'mutate-iter-source',
    )
_LV22_VIEW_METHODS = frozenset({'keys', 'items', 'values'})
def _lv22_view_receiver(node: ast.AST) -> str | None:
    if not (isinstance(node, ast.Call) and not node.args
            and not node.keywords
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _LV22_VIEW_METHODS
            and isinstance(node.func.value, ast.Name)):
        return None
    return node.func.value.id
def _lv22_iter_source(node: ast.AST) -> str | None:
    if not isinstance(node, (ast.For, ast.AsyncFor)) or not node.body:
        return None
    if isinstance(node.iter, ast.Name):
        return node.iter.id
    return _lv22_view_receiver(node.iter)
def check_LV22(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    seen: set[tuple[str, int]] = set()
    for node in roots:
        src_name = _lv22_iter_source(node)
        if src_name is None:
            continue
        for hit_kind, hit_line in _lv22_loop_hits(node, src_name, parents):
            key = (src_name, hit_line)
            if key in seen:
                continue
            seen.add(key)
            issues.append(_lv22_issue(src_name, hit_kind, hit_line,
                                       filepath, src_lines))
    return issues
def _lv22_literal_truth(expr: ast.AST) -> bool | None:
    value = expr.value if isinstance(expr, ast.NamedExpr) else expr
    try:
        literal = ast.literal_eval(value)
    except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):
        return None
    return bool(literal)
def _lv22_preserves_original(expr: ast.AST, name: str) -> bool:
    if isinstance(expr, ast.NamedExpr):
        return _lv22_preserves_original(expr.value, name)
    if isinstance(expr, ast.IfExp):
        truth = _lv22_literal_truth(expr.test)
        if truth is not None:
            selected = expr.body if truth else expr.orelse
            return _lv22_preserves_original(selected, name)
        return (_lv22_preserves_original(expr.body, name)
                or _lv22_preserves_original(expr.orelse, name))
    if isinstance(expr, ast.BoolOp):
        if isinstance(expr.op, ast.Or):
            for value in expr.values:
                if _lv22_preserves_original(value, name):
                    return True
                if _lv22_literal_truth(value) is True:
                    return False
            return False
        for value in expr.values[:-1]:
            if _lv22_literal_truth(value) is False:
                return False
        return _lv22_preserves_original(expr.values[-1], name)
    return isinstance(expr, ast.Name) and expr.id == name
def _lv22_expr_always_binds(expr: ast.AST, name: str) -> bool:
    if isinstance(expr, ast.NamedExpr):
        if (_lv22_target_binds_name(expr.target, name)
                and not _lv22_preserves_original(expr.value, name)):
            return True
        return _lv22_expr_always_binds(expr.value, name)
    if isinstance(expr, ast.Lambda):
        return any(_lv22_expr_always_binds(default, name)
                   for default in _lv22_lambda_outer_exprs(expr))
    if isinstance(expr, ast.BoolOp):
        short_circuit_truth = isinstance(expr.op, ast.Or)
        for value in expr.values:
            if _lv22_expr_always_binds(value, name):
                return True
            truth = _lv22_literal_truth(value)
            if truth is None or truth is short_circuit_truth:
                return False
        return False
    if isinstance(expr, ast.IfExp):
        if _lv22_expr_always_binds(expr.test, name):
            return True
        truth = _lv22_literal_truth(expr.test)
        if truth is not None:
            selected = expr.body if truth else expr.orelse
            return _lv22_expr_always_binds(selected, name)
        return (_lv22_expr_always_binds(expr.body, name)
                and _lv22_expr_always_binds(expr.orelse, name))
    if isinstance(expr, _CONTAINER_COMP_NODES):
        return (bool(expr.generators)
                and _lv22_expr_always_binds(expr.generators[0].iter, name))
    if isinstance(expr, ast.Compare) and len(expr.ops) > 1:
        return (_lv22_expr_always_binds(expr.left, name)
                or _lv22_expr_always_binds(expr.comparators[0], name))
    return any(_lv22_expr_always_binds(child, name)
               for child in ast.iter_child_nodes(expr)
               if isinstance(child, ast.expr))
def _lv22_expr_branch_binds(expr: ast.AST, name: str, truth: bool) -> bool:
    if _lv22_expr_always_binds(expr, name):
        return True
    if not isinstance(expr, ast.BoolOp):
        return False
    if isinstance(expr.op, ast.And) and truth:
        return any(_lv22_expr_branch_binds(value, name, True)
                   for value in expr.values)
    if isinstance(expr.op, ast.Or) and not truth:
        return any(_lv22_expr_branch_binds(value, name, False)
                   for value in expr.values)
    return False
def _lv22_case_binds(case: ast.AST, name: str) -> bool:
    return any(name in capture_binding_names(node)
               for node in iter_nodes_outside(case.pattern))
def _lv22_pattern_captures_whole_subject(
        pattern: ast.AST, name: str) -> bool:
    if isinstance(pattern, ast.MatchAs):
        return (pattern.name == name
                or (pattern.pattern is not None
                    and _lv22_pattern_captures_whole_subject(
                        pattern.pattern, name)))
    if isinstance(pattern, ast.MatchOr):
        return any(_lv22_pattern_captures_whole_subject(sub, name)
                   for sub in pattern.patterns)
    return False
def _lv22_case_rebinds_away(
        case: ast.AST, subject: ast.AST, name: str) -> bool:
    whole_alias = (_lv22_preserves_original(subject, name)
                   and _lv22_pattern_captures_whole_subject(
                       case.pattern, name))
    return _lv22_case_binds(case, name) and not whole_alias
def _lv22_annotation_is_evaluated(
        stmt: ast.AnnAssign, parent: dict[int, ast.AST]) -> bool:
    scope = _effective_scope(stmt, parent)
    return (isinstance(scope, (ast.Module, ast.ClassDef))
            and not _lv22_annotations_deferred(_tree_root(stmt, parent)))
def _lv22_assignment_preserves_original(
        targets: list[ast.AST], value: ast.AST, name: str) -> bool:
    values = [bound for target in targets
              for bound in _bound_values_for_name(target, value, name)]
    return bool(values) and _lv22_preserves_original(values[-1], name)
def _lv22_block_definitely_rebinds(
        stmts: list[ast.stmt], name: str,
        parent: dict[int, ast.AST] | None = None) -> bool:
    for stmt in stmts:
        if (_lv22_stmt_definitely_rebinds(stmt, name, parent)
                or block_exits([stmt])):
            return True
    return False
def _lv22_stmt_definitely_rebinds(
        stmt: ast.AST, name: str,
        parent: dict[int, ast.AST] | None = None) -> bool:
    if isinstance(stmt, ast.Expr):
        return _lv22_expr_always_binds(stmt.value, name)
    if isinstance(stmt, (ast.Assign, ast.AnnAssign)):
        if (isinstance(stmt, ast.AnnAssign) and parent is not None
                and _lv22_annotation_is_evaluated(stmt, parent)
                and _lv22_expr_always_binds(stmt.annotation, name)):
            return True
        if isinstance(stmt, ast.AnnAssign) and stmt.value is None:
            return False
        targets = (stmt.targets if isinstance(stmt, ast.Assign)
                   else [stmt.target])
        if any(_lv22_target_binds_name(tgt, name) for tgt in targets):
            return (_lv22_expr_always_binds(stmt.value, name)
                    or not _lv22_assignment_preserves_original(
                        targets, stmt.value, name))
        return _lv22_expr_always_binds(stmt.value, name)
    if isinstance(stmt, ast.AugAssign):
        return (isinstance(stmt.target, ast.Name)
                and _lv22_rebinds_immutable_literal(
                    stmt, stmt.target.id, parent))
    if isinstance(stmt, ast.Delete):
        return any(isinstance(tgt, ast.Name) and tgt.id == name
                   for tgt in stmt.targets)
    if isinstance(stmt, (ast.Import, ast.ImportFrom)):
        return any((alias.asname or alias.name.split('.')[0]) == name
                   for alias in stmt.names)
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        if stmt.name == name:
            return True
        if parent is None:
            return False
        if any(_lv22_expr_always_binds(expr, name)
               for expr in _lv22_definition_outer_exprs(stmt, parent)):
            return True
        return (isinstance(stmt, ast.ClassDef)
                and _lv22_class_rebinds_outer(stmt, name, parent))
    if isinstance(stmt, ast.If):
        body_rebound = (
            _lv22_expr_branch_binds(stmt.test, name, True)
            or _lv22_block_definitely_rebinds(stmt.body, name, parent))
        else_rebound = (
            _lv22_expr_branch_binds(stmt.test, name, False)
            or _lv22_block_definitely_rebinds(stmt.orelse, name, parent))
        return body_rebound and else_rebound
    if isinstance(stmt, ast.While):
        if _lv22_expr_always_binds(stmt.test, name):
            return True
        return (not _loop_body_breaks(stmt.body)
                and _lv22_expr_branch_binds(stmt.test, name, False))
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        if _lv22_expr_always_binds(stmt.iter, name):
            return True
        return (_lv22_target_binds_name(stmt.target, name)
                and _lv22_safe_rebind_value(stmt.iter)
                and _loop_guarantees_once(
                    stmt, parent if parent is not None else {}))
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        if any((item.optional_vars is not None
                and _lv22_target_binds_name(item.optional_vars, name))
               or _lv22_expr_always_binds(item.context_expr, name)
               for item in stmt.items):
            return True
        return _lv22_leading_safe_rebind(stmt.body, name)
    if isinstance(stmt, TRY_NODES):
        if _lv22_block_definitely_rebinds(stmt.finalbody, name, parent):
            return True
        normal_path = (
            _lv22_block_definitely_rebinds(stmt.body, name, parent)
            or _lv22_block_definitely_rebinds(stmt.orelse, name, parent))
        return normal_path and all(
            _lv22_block_definitely_rebinds(handler.body, name, parent)
            or block_exits(handler.body)
            for handler in stmt.handlers)
    if isinstance(stmt, ast.Match):
        if _lv22_expr_always_binds(stmt.subject, name):
            return True
        if not any(case.guard is None
                   and _pattern_irrefutable(case.pattern)
                   for case in stmt.cases):
            return False
        return all(
            block_exits(case.body)
            or _lv22_block_definitely_rebinds(case.body, name, parent)
            or _lv22_case_rebinds_away(case, stmt.subject, name)
            for case in stmt.cases)
    return False
def _lv22_lambda_outer_exprs(lam: ast.Lambda) -> list[ast.AST]:
    args = lam.args
    return [*args.defaults,
            *(item for item in args.kw_defaults if item is not None)]
_LV22_EAGER_GENERATOR_CONSUMERS = frozenset({
    'all', 'any', 'dict', 'frozenset', 'list', 'max', 'min', 'set',
    'sorted', 'sum', 'tuple',
})
def _lv22_immediate_lambda_body(node: ast.AST) -> ast.AST | None:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Lambda)
            and not node.args and not node.keywords):
        return None
    args = node.func.args
    positional = args.posonlyargs + args.args
    if (len(positional) > len(args.defaults)
            or any(default is None for default in args.kw_defaults)):
        return None
    return node.func.body
def _lv22_generator_matches_consumer(
        gen: ast.GeneratorExp, *, asynchronous: bool,
) -> bool:
    return any(comp.is_async for comp in gen.generators) == asynchronous
def _lv22_eager_generator_arg(
        node: ast.AST, parent: dict[int, ast.AST] | None,
) -> ast.GeneratorExp | None:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in _LV22_EAGER_GENERATOR_CONSUMERS
            and len(node.args) == 1 and not node.keywords
            and isinstance(node.args[0], ast.GeneratorExp)
            and _lv22_generator_matches_consumer(
                node.args[0], asynchronous=False)
            and parent is not None
            and not shadowed_binding_at(node, node.func.id, parent, {})):
        return None
    return node.args[0]
def _lv22_scan_generator_body(
        gen: ast.GeneratorExp, name: str, hits: list[tuple[str, int]],
        parent: dict[int, ast.AST] | None,
) -> None:
    _lv22_scan_expr(gen.elt, name, hits, parent)
    for comp in gen.generators:
        for guard in comp.ifs:
            _lv22_scan_expr(guard, name, hits, parent)
    for comp in gen.generators[1:]:
        _lv22_scan_expr(comp.iter, name, hits, parent)
def _lv22_scan_expr(
        expr: ast.AST, name: str, hits: list[tuple[str, int]],
        parent: dict[int, ast.AST] | None = None,
) -> None:
    for sub in _immediate_expr_nodes(expr):
        hit = _lv22_hit_kind(sub, name, parent)
        if hit is not None:
            hits.append(hit)
        lambda_body = _lv22_immediate_lambda_body(sub)
        if lambda_body is not None:
            _lv22_scan_expr(lambda_body, name, hits, parent)
        generator = _lv22_eager_generator_arg(sub, parent)
        if generator is not None:
            _lv22_scan_generator_body(generator, name, hits, parent)
def _lv22_scan_exprs(
        stmt: ast.AST, name: str, hits: list[tuple[str, int]],
        parent: dict[int, ast.AST] | None = None,
) -> None:
    for child in ast.iter_child_nodes(stmt):
        if isinstance(child, ast.expr):
            _lv22_scan_expr(child, name, hits, parent)
def _lv22_safe_rebind_value(value: ast.AST) -> bool:
    try:
        ast.literal_eval(value)
    except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):
        return False
    return True
def _lv22_leading_safe_rebind(stmts: list[ast.stmt], name: str) -> bool:
    if not stmts:
        return False
    first = stmts[0]
    if isinstance(first, ast.Assign):
        if not all(isinstance(tgt, ast.Name) for tgt in first.targets):
            return False
        return (_lv22_safe_rebind_value(first.value)
                and any(_lv22_target_binds_name(tgt, name)
                        for tgt in first.targets))
    if isinstance(first, ast.AnnAssign):
        return (isinstance(first.target, ast.Name)
                and first.target.id == name
                and first.value is not None
                and _lv22_safe_rebind_value(first.value))
    return False
def _lv22_block_rebinds_before_exit(
        stmts: list[ast.stmt], name: str,
        parent: dict[int, ast.AST] | None = None) -> bool:
    simple_rebind_stmts = (
        ast.Expr, ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Delete,
        ast.Import, ast.ImportFrom,
        ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
    )
    for stmt in stmts:
        rebound = False
        if isinstance(stmt, ast.If):
            rebound = (
                _lv22_block_rebinds_before_exit(stmt.body, name, parent)
                and _lv22_block_rebinds_before_exit(
                    stmt.orelse, name, parent))
        elif isinstance(stmt, simple_rebind_stmts):
            rebound = _lv22_stmt_definitely_rebinds(stmt, name, parent)
        if rebound:
            return True
        if block_exits([stmt]):
            return False
    return False
def _lv22_try_rebinds_before_finally(
        stmt: ast.AST, name: str,
        parent: dict[int, ast.AST] | None = None) -> bool:
    if not stmt.handlers:
        return False
    handlers_rebind = all(
        handler.name == name or _lv22_leading_safe_rebind(
            handler.body, name)
        for handler in stmt.handlers)
    return (handlers_rebind
            and _lv22_block_rebinds_before_exit(
                stmt.body, name, parent))
def _lv22_scan_try(stmt: ast.AST, name: str,
                   hits: list[tuple[str, int]],
                   parent: dict[int, ast.AST]) -> None:
    body_rebound = _lv22_block_definitely_rebinds(
        stmt.body, name, parent)
    leading_safe = _lv22_leading_safe_rebind(stmt.body, name)
    finally_rebound = leading_safe or _lv22_try_rebinds_before_finally(
        stmt, name, parent)
    _lv22_scan_block(stmt.body, name, hits, True, parent)
    for handler in stmt.handlers:
        if handler.type is not None and not leading_safe:
            _lv22_scan_expr(handler.type, name, hits, parent)
        _lv22_scan_block(handler.body, name, hits,
                         not (leading_safe or handler.name == name), parent)
    _lv22_scan_block(stmt.orelse, name, hits, not body_rebound, parent)
    _lv22_scan_block(stmt.finalbody, name, hits, not finally_rebound, parent)
def _lv22_scan_match(stmt: ast.Match, name: str,
                     hits: list[tuple[str, int]],
                     parent: dict[int, ast.AST]) -> None:
    _lv22_scan_expr(stmt.subject, name, hits, parent)
    subject_rebound = _lv22_expr_always_binds(stmt.subject, name)
    for case in stmt.cases:
        original_bound = not (
            subject_rebound
            or _lv22_case_rebinds_away(case, stmt.subject, name))
        if case.guard is not None and original_bound:
            _lv22_scan_expr(case.guard, name, hits, parent)
        guard_rebound = (
            case.guard is not None
            and _lv22_expr_branch_binds(case.guard, name, True))
        _lv22_scan_block(
            case.body, name, hits, original_bound and not guard_rebound,
            parent)
def _lv22_scan_expr_sequence(
        exprs: list[ast.AST], name: str,
        hits: list[tuple[str, int]], bound: bool,
        parent: dict[int, ast.AST] | None = None) -> bool:
    for expr in exprs:
        if bound:
            _lv22_scan_expr(expr, name, hits, parent)
        if _lv22_expr_always_binds(expr, name):
            bound = False
    return bound
def _lv22_scan_assignment(
        stmt: ast.Assign | ast.AnnAssign, name: str,
        hits: list[tuple[str, int]],
        parent: dict[int, ast.AST] | None = None) -> bool:
    value = stmt.value
    if value is None:
        _lv22_scan_expr(stmt.target, name, hits, parent)
        return True
    targets = stmt.targets if isinstance(stmt, ast.Assign) else [stmt.target]
    _lv22_scan_expr(value, name, hits, parent)
    bound = not _lv22_expr_always_binds(value, name)
    for target in targets:
        if bound:
            if (_lv22_is_subscript_of(target, name)
                    and not _lv22_neutral_list_element_writes(
                        [target], name, stmt, parent)):
                hits.append(('下标/切片赋值', stmt.lineno))
            _lv22_scan_expr(target, name, hits, parent)
        if (_lv22_target_binds_name(target, name)
                and not _lv22_assignment_preserves_original(
                    [target], value, name)):
            bound = False
    return bound
def _lv22_scan_stmt(stmt: ast.AST, name: str,
                    hits: list[tuple[str, int]],
                    parent: dict[int, ast.AST]) -> None:
    if isinstance(stmt, (ast.If, ast.While)):
        _lv22_scan_expr(stmt.test, name, hits, parent)
        body_bound = not _lv22_expr_branch_binds(stmt.test, name, True)
        else_bound = not _lv22_expr_branch_binds(stmt.test, name, False)
        _lv22_scan_block(stmt.body, name, hits, body_bound, parent)
        _lv22_scan_block(stmt.orelse, name, hits, else_bound, parent)
        return
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        _lv22_scan_expr(stmt.iter, name, hits, parent)
        if (isinstance(stmt.iter, ast.GeneratorExp)
                and _lv22_generator_matches_consumer(
                    stmt.iter, asynchronous=isinstance(stmt, ast.AsyncFor))):
            _lv22_scan_generator_body(stmt.iter, name, hits, parent)
        iter_binds = _lv22_expr_always_binds(stmt.iter, name)
        if (not iter_binds and _lv22_is_subscript_of(stmt.target, name)
                and not _lv22_neutral_list_element_writes(
                    [stmt.target], name, stmt, parent)):
            hits.append(('循环目标下标赋值', stmt.lineno))
        target_binds = _lv22_target_binds_name(stmt.target, name)
        _lv22_scan_block(
            stmt.body, name, hits, not (target_binds or iter_binds), parent)
        target_guaranteed = (
            target_binds and _loop_guarantees_once(stmt, parent))
        _lv22_scan_block(
            stmt.orelse, name, hits,
            not (iter_binds or target_guaranteed), parent)
        return
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        original_bound = True
        for item in stmt.items:
            if original_bound:
                _lv22_scan_expr(item.context_expr, name, hits, parent)
            if _lv22_expr_always_binds(item.context_expr, name):
                original_bound = False
            if (original_bound and item.optional_vars is not None
                    and _lv22_is_subscript_of(item.optional_vars, name)
                    and not _lv22_neutral_list_element_writes(
                        [item.optional_vars], name, stmt, parent)):
                hits.append(('with 目标下标赋值', stmt.lineno))
            if (item.optional_vars is not None
                    and _lv22_target_binds_name(item.optional_vars, name)):
                original_bound = False
        _lv22_scan_block(stmt.body, name, hits, original_bound, parent)
        return
    if isinstance(stmt, TRY_NODES):
        _lv22_scan_try(stmt, name, hits, parent)
        return
    if isinstance(stmt, ast.Match):
        _lv22_scan_match(stmt, name, hits, parent)
        return
    if isinstance(stmt, ast.Delete):
        hit = _lv22_hit_kind(stmt, name, parent)
        if hit is not None:
            hits.append(hit)
        return
    if isinstance(stmt, ast.AugAssign):
        hit = _lv22_hit_kind(stmt, name, parent)
        if hit is not None:
            hits.append(hit)
        _lv22_scan_expr(stmt.value, name, hits, parent)
        return
    if isinstance(stmt, ast.Assign):
        _lv22_scan_assignment(stmt, name, hits, parent)
        return
    if isinstance(stmt, ast.AnnAssign):
        bound = _lv22_scan_assignment(stmt, name, hits, parent)
        if bound and _lv22_annotation_is_evaluated(stmt, parent):
            _lv22_scan_expr(stmt.annotation, name, hits, parent)
        return
    _lv22_scan_exprs(stmt, name, hits, parent)
def _lv22_annotations_deferred(tree: ast.AST) -> bool:
    return any(
        isinstance(stmt, ast.ImportFrom) and stmt.module == '__future__'
        and any(alias.name == 'annotations' for alias in stmt.names)
        for stmt in getattr(tree, 'body', ()))
def _lv22_definition_outer_exprs(
        node: ast.AST, parent: dict[int, ast.AST]) -> list[ast.AST]:
    exprs: list[ast.AST] = list(getattr(node, 'decorator_list', ()))
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        args = node.args
        exprs.extend(args.defaults)
        exprs.extend(item for item in args.kw_defaults if item is not None)
        if not _lv22_annotations_deferred(_tree_root(node, parent)):
            for arg in (args.posonlyargs + args.args + args.kwonlyargs):
                if arg.annotation is not None:
                    exprs.append(arg.annotation)
            for extra in (args.vararg, args.kwarg):
                if extra is not None and extra.annotation is not None:
                    exprs.append(extra.annotation)
            if node.returns is not None:
                exprs.append(node.returns)
    elif isinstance(node, ast.ClassDef):
        exprs.extend(node.bases)
        exprs.extend(kw.value for kw in node.keywords)
    exprs.extend(getattr(node, 'type_params', ()))
    return exprs
def _lv22_declaration_nodes(scope: ast.AST) -> list[ast.AST]:
    return [
        node for stmt in getattr(scope, 'body', ())
        for node in iter_nodes_outside(stmt)
        if isinstance(node, (ast.Global, ast.Nonlocal))
    ]
def _lv22_class_rebinds_outer(
        stmt: ast.ClassDef, name: str,
        parent: dict[int, ast.AST]) -> bool:
    declarations = [
        node for node in _lv22_declaration_nodes(stmt) if name in node.names]
    if (not declarations
            or not _lv22_block_definitely_rebinds(
                stmt.body, name, parent)):
        return False
    owner = nearest_scope(parent, stmt)
    if isinstance(owner, ast.Module):
        return any(isinstance(node, ast.Global) for node in declarations)
    if not isinstance(owner, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False
    if any(isinstance(node, ast.Nonlocal) for node in declarations):
        return True
    if not any(isinstance(node, ast.Global) for node in declarations):
        return False
    owner_globals = {
        nm for node in _lv22_declaration_nodes(owner)
        if isinstance(node, ast.Global) for nm in node.names}
    return name in owner_globals or name not in scope_local_bindings(owner)
def _lv22_scan_block(stmts: list, name: str,
                     hits: list[tuple[str, int]], bound: bool,
                     parent: dict[int, ast.AST]) -> None:
    for stmt in stmts:
        if isinstance(stmt, ast.ClassDef):
            bound = _lv22_scan_expr_sequence(
                _lv22_definition_outer_exprs(stmt, parent), name, hits, bound, parent)
            _lv22_scan_block(stmt.body, name, hits, bound, parent)
            bound = (bound and stmt.name != name
                     and not _lv22_class_rebinds_outer(stmt, name, parent))
            continue
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            bound = _lv22_scan_expr_sequence(
                _lv22_definition_outer_exprs(stmt, parent), name, hits, bound, parent)
            bound = bound and stmt.name != name
            continue
        if isinstance(stmt, ast.Lambda):
            continue
        if bound:
            _lv22_scan_stmt(stmt, name, hits, parent)
        if _lv22_stmt_definitely_rebinds(stmt, name, parent):
            bound = False
def _lv22_loop_hits(
        node: ast.AST, src_name: str,
        parent: dict[int, ast.AST]) -> list[tuple[str, int]]:
    hits: list[tuple[str, int]] = []
    if (_lv22_is_subscript_of(node.target, src_name)
            and not _lv22_neutral_list_element_writes(
                [node.target], src_name, node, parent)):
        hits.append(('循环目标下标赋值', node.lineno))
    bound = not _lv22_target_binds_name(node.target, src_name)
    _lv22_scan_block(node.body, src_name, hits, bound, parent)
    hits.sort(key=lambda hit: hit[1])
    unique: list[tuple[str, int]] = []
    seen_lines: set[int] = set()
    for hit in hits:
        if hit[1] in seen_lines:
            continue
        seen_lines.add(hit[1])
        unique.append(hit)
    return unique

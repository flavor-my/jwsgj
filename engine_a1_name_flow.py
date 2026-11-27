from __future__ import annotations

import ast
import builtins
import logging
from bisect import bisect_right
from collections.abc import Callable, Iterable
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    block_may_fall_through,
    build_parent_map,
    flatten_unpack_targets,
    iter_arg_nodes,
    iter_unpack_target_names,
    module_postpones_annotations,
)
from jwsgj.engine_a1_structure import (
    ALL_MUTATOR_METHODS,
    DefectType,
    FileDefect,
    binds_all_name,
    is_all_delete,
    is_all_name_target,
    is_all_walrus_stmt,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    is_test_file_path,
)

logger = logging.getLogger(__name__)
__all__ = [
    'check_all_overwrite',
    'check_undefined_names',
    'exception_matches',
]
logger.info("engine_a1_name_flow 名字流缺陷分析域已加载: %d 项导出", len(__all__))
def _exception_type_name(exc_type: ast.expr) -> str | None:
    if isinstance(exc_type, ast.Name):
        return exc_type.id
    if (isinstance(exc_type, ast.Attribute)
            and isinstance(exc_type.value, ast.Name)
            and exc_type.value.id == "builtins"):
        return exc_type.attr
    return None
def exception_matches(exc_type: ast.expr, names) -> bool:
    if isinstance(exc_type, ast.Tuple):
        return any(exception_matches(elt, names) for elt in exc_type.elts)
    return _exception_type_name(exc_type) in names
_EAGER_GENEXP_CALL_ARITIES = {
    'list': (1,), 'tuple': (1,), 'set': (1,), 'frozenset': (1,),
    'dict': (1,), 'sorted': (1,), 'any': (1,), 'all': (1,),
    'min': (1,), 'max': (1,), 'sum': (1, 2), 'next': (1, 2),
}
_EAGER_GENEXP_ANY_EXPLICIT_KEYWORDS = frozenset({'dict', 'sorted'})
_EAGER_GENEXP_ALLOWED_KEYWORDS = {
    'min': frozenset({'key', 'default'}),
    'max': frozenset({'key', 'default'}),
    'sum': frozenset({'start'}),
}
def _eager_genexp_keywords_consumed(name: str, keywords: list) -> bool:
    if any(keyword.arg is None for keyword in keywords):
        return False
    if name in _EAGER_GENEXP_ANY_EXPLICIT_KEYWORDS:
        return True
    allowed = _EAGER_GENEXP_ALLOWED_KEYWORDS.get(name, frozenset())
    return all(keyword.arg in allowed for keyword in keywords)
def _is_zero_arg_lambda_call(node: ast.Call) -> bool:
    if not isinstance(node.func, ast.Lambda) or node.args or node.keywords:
        return False
    args = node.func.args
    positional = [*args.posonlyargs, *args.args]
    required_positional = max(len(positional) - len(args.defaults), 0)
    return (required_positional == 0
            and all(default is not None for default in args.kw_defaults))
def _is_async_generator_exp(node: ast.AST) -> bool:
    return (isinstance(node, ast.GeneratorExp)
            and any(gen.is_async for gen in node.generators))
def _consumed_genexp(node: ast.AST, *, is_async: bool) -> ast.GeneratorExp | None:
    if not isinstance(node, ast.GeneratorExp):
        return None
    return node if _is_async_generator_exp(node) == is_async else None
def _lambda_local_bindings(node: ast.Lambda) -> frozenset[str]:
    names = {arg.arg for arg in iter_arg_nodes(node.args)}
    stack: list[ast.AST] = [node.body]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.Lambda):
            stack.extend(cur.args.defaults)
            stack.extend(item for item in cur.args.kw_defaults
                         if item is not None)
            continue
        if (isinstance(cur, ast.NamedExpr)
                and isinstance(cur.target, ast.Name)):
            names.add(cur.target.id)
        stack.extend(ast.iter_child_nodes(cur))
    return frozenset(names)
def _reads_all_before_binding(
        value: ast.expr, shadowed_eager_calls: frozenset[int]) -> bool:
    stack: list[tuple[ast.AST, frozenset[str], bool]] = [
        (value, frozenset(), False)]
    while stack:
        cur, shadowed, consumed = stack.pop()
        if isinstance(cur, ast.Name):
            if (cur.id == "__all__" and "__all__" not in shadowed
                    and isinstance(cur.ctx, ast.Load)):
                return True
            continue
        if isinstance(cur, ast.Lambda):
            stack.extend((item, shadowed, False)
                         for item in cur.args.defaults)
            stack.extend((item, shadowed, False)
                         for item in cur.args.kw_defaults if item is not None)
            if consumed:
                local_shadow = shadowed | _lambda_local_bindings(cur)
                stack.append((cur.body, local_shadow, False))
            continue
        if isinstance(cur, (ast.ListComp, ast.SetComp, ast.DictComp,
                            ast.GeneratorExp)):
            generators = cur.generators
            if isinstance(cur, ast.GeneratorExp) and not consumed:
                if generators:
                    stack.append((generators[0].iter, shadowed, False))
                continue
            inner = set(shadowed)
            tasks: list[tuple[ast.AST, frozenset[str], bool]] = []
            for generator in generators:
                genexp = _consumed_genexp(
                    generator.iter, is_async=bool(generator.is_async))
                tasks.append((generator.iter, frozenset(inner),
                              genexp is not None))
                inner.update(iter_unpack_target_names(generator.target))
                tasks.extend((condition, frozenset(inner), False)
                             for condition in generator.ifs)
            final_shadow = frozenset(inner)
            if isinstance(cur, ast.DictComp):
                tasks.extend(((cur.key, final_shadow, False),
                              (cur.value, final_shadow, False)))
            else:
                tasks.append((cur.elt, final_shadow, False))
            stack.extend(reversed(tasks))
            continue
        children = list(ast.iter_child_nodes(cur))
        eager: set[int] = set()
        if isinstance(cur, ast.Call):
            if _is_zero_arg_lambda_call(cur):
                eager.add(id(cur.func))
            elif isinstance(cur.func, ast.Name):
                arities = _EAGER_GENEXP_CALL_ARITIES.get(cur.func.id)
                genexp = (_consumed_genexp(cur.args[0], is_async=False)
                          if cur.args else None)
                if (arities and genexp is not None
                        and id(cur) not in shadowed_eager_calls
                        and _eager_genexp_keywords_consumed(
                            cur.func.id, cur.keywords)
                        and len(cur.args) in arities):
                    eager.add(id(genexp))
        elif isinstance(cur, (ast.Starred, ast.YieldFrom)):
            genexp = _consumed_genexp(cur.value, is_async=False)
            if genexp is not None:
                eager.add(id(genexp))
        stack.extend((child, shadowed, id(child) in eager)
                     for child in children)
    return False
def _is_all_mutator_call(call: ast.Call) -> bool:
    _f = call.func
    return (isinstance(_f, ast.Attribute)
            and _f.attr in ALL_MUTATOR_METHODS
            and isinstance(_f.value, ast.Name)
            and _f.value.id == "__all__")
def _is_all_annassign_rebind(node: ast.AnnAssign,
                             shadowed_eager_calls: frozenset[int]) -> bool:
    return (is_all_name_target(node.target)
            and node.value is not None
            and _reads_all_before_binding(node.value, shadowed_eager_calls))
def _is_all_assign_rebind(node: ast.Assign,
                          shadowed_eager_calls: frozenset[int]) -> bool:
    return (binds_all_name(node)
            and _reads_all_before_binding(node.value, shadowed_eager_calls))
def _is_all_increment_stmt(node: ast.stmt,
                           shadowed_eager_calls: frozenset[int]) -> bool:
    if isinstance(node, ast.Call):
        return _is_all_mutator_call(node)
    if isinstance(node, ast.AugAssign):
        return is_all_name_target(node.target)
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
        return _is_all_mutator_call(node.value)
    if isinstance(node, ast.AnnAssign):
        return _is_all_annassign_rebind(node, shadowed_eager_calls)
    if isinstance(node, ast.Assign):
        return _is_all_assign_rebind(node, shadowed_eager_calls)
    if is_all_walrus_stmt(node):
        return _reads_all_before_binding(node.value, shadowed_eager_calls)
    return False
def _is_complete_all_binding(stmt: ast.stmt,
                             shadowed_eager_calls: frozenset[int]) -> bool:
    if not binds_all_name(stmt):
        return False
    value = getattr(stmt, "value", None)
    return (value is None or not _reads_all_before_binding(
        value, shadowed_eager_calls))
def _is_bare_all_annotation(stmt: ast.stmt) -> bool:
    return (isinstance(stmt, ast.AnnAssign)
            and is_all_name_target(stmt.target)
            and stmt.value is None)
def _is_complete_all_assign(node: ast.AST,
                            shadowed_eager_calls: frozenset[int]) -> bool:
    if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.Expr)):
        return False
    return (getattr(node, "value", None) is not None
            and _is_complete_all_binding(node, shadowed_eager_calls))
def _global_names(block: ast.AST, include_class_bodies: bool) -> set[str]:
    if isinstance(block, ast.Lambda):
        return set()
    _prune: tuple[type, ...] = (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda)
    if not include_class_bodies:
        _prune = _prune + (ast.ClassDef,)
    names: set[str] = set()
    stack: list[ast.AST] = list(getattr(block, "body", []))
    while stack:
        stmt = stack.pop()
        if isinstance(stmt, ast.Global):
            names.update(stmt.names)
        elif isinstance(stmt, _prune):
            continue
        else:
            stack.extend(ast.iter_child_nodes(stmt))
    return names
def _has_nonlocal_all_declaration(func_node: ast.AST) -> bool:
    if isinstance(func_node, ast.Lambda):
        return False
    stack: list[ast.AST] = list(getattr(func_node, "body", []))
    while stack:
        stmt = stack.pop()
        if (isinstance(stmt, ast.Nonlocal)
                and "__all__" in stmt.names):
            return True
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            continue
        stack.extend(ast.iter_child_nodes(stmt))
    return False
def _all_increment_bucket(stmt: ast.stmt,
                          shadowed_eager_calls: frozenset[int]) -> str | None:
    if isinstance(stmt, ast.AugAssign):
        return "aug" if is_all_name_target(stmt.target) else None
    if ((isinstance(stmt, (ast.Assign, ast.AnnAssign))
         or is_all_walrus_stmt(stmt))
            and _is_all_increment_stmt(stmt, shadowed_eager_calls)):
        return "rebind"
    if is_all_delete(stmt):
        return "delete"
    return ("direct" if _is_all_increment_stmt(stmt, shadowed_eager_calls)
            else None)
_IncItem = tuple[ast.AST, tuple[int, int]]
class _FuncLocalAllScan:
    __slots__ = ("augs", "class_incs", "delete_nodes", "direct_incs",
                 "first_init", "has_local", "init_nodes", "init_pos",
                 "nonlocal_all", "parent", "root")
    def __init__(self, *, nonlocal_all: bool = False) -> None:
        self.augs: list[_IncItem] = []
        self.direct_incs: list[_IncItem] = []
        self.class_incs: list[_IncItem] = []
        self.delete_nodes: list[_IncItem] = []
        self.init_nodes: list[_IncItem] = []
        self.init_pos: list[tuple[int, int]] = []
        self.first_init: tuple[int, int] | None = None
        self.has_local = False
        self.nonlocal_all = nonlocal_all
        self.root: ast.AST | None = None
        self.parent: dict[int, ast.AST] = {}
    def reads_without_live_base(self, items: list[_IncItem]) -> list[_IncItem]:
        if not self.has_local:
            return []
        if not self.parent and self.root is not None:
            self.parent = build_parent_map(self.root)
        base_guards = {
            pos: _conditional_branch_chain(node, self.parent)
            for node, pos in self.init_nodes}
        hits: list[_IncItem] = []
        for item in items:
            read_guards = _conditional_branch_chain(item[0], self.parent)
            prior_bases = [init for init in self.init_pos if init < item[1]]
            live_bases = _covering_base_positions(
                prior_bases, base_guards, read_guards)
            has_live_base = False
            for init in live_bases:
                if any(
                        init < delete_pos < item[1]
                        and not _AllScanState._branches_disjoint(
                            _conditional_branch_chain(delete, self.parent),
                            read_guards)
                        for delete, delete_pos in self.delete_nodes):
                    continue
                has_live_base = True
                break
            if not has_live_base:
                hits.append(item)
        return hits
def _local_all_note_init(scan: _FuncLocalAllScan, node: ast.AST,
                         pos: tuple[int, int]) -> None:
    if scan.first_init is None or pos < scan.first_init:
        scan.first_init = pos
    scan.init_nodes.append((node, pos))
    scan.init_pos.append(pos)
    scan.has_local = True
def _local_all_note_binding(scan: _FuncLocalAllScan, stmt: ast.stmt,
                             pos: tuple[int, int],
                             shadowed_eager_calls: frozenset[int]) -> None:
    if scan.nonlocal_all:
        return
    complete = _is_complete_all_binding(stmt, shadowed_eager_calls)
    if complete or _is_bare_all_annotation(stmt):
        scan.has_local = True
    if complete:
        _local_all_note_init(scan, stmt, pos)
def _local_all_note_increment(scan: _FuncLocalAllScan, stmt: ast.stmt,
                              pos: tuple[int, int],
                              shadowed_eager_calls: frozenset[int]) -> None:
    bucket = _all_increment_bucket(stmt, shadowed_eager_calls)
    if bucket is None:
        return
    if scan.nonlocal_all:
        scan.direct_incs.append((stmt, pos))
        return
    if bucket == "delete":
        scan.delete_nodes.append((stmt, pos))
    sink = scan.direct_incs if bucket == "direct" else scan.augs
    sink.append((stmt, pos))
    if bucket != "direct":
        scan.has_local = True
def _local_all_visit(scan: _FuncLocalAllScan, stmt: ast.AST,
                     shadowed_eager_calls: frozenset[int]) -> bool:
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        return True
    if isinstance(stmt, ast.ClassDef):
        scan.class_incs.extend(_analyze_class_body_all(
            stmt, shadowed_eager_calls))
        return True
    if isinstance(stmt, ast.Call):
        if _is_all_mutator_call(stmt):
            scan.direct_incs.append(
                (stmt, (stmt.lineno, stmt.col_offset)))
        return False
    if not isinstance(stmt, ast.stmt):
        return False
    pos = (stmt.lineno, stmt.col_offset)
    _local_all_note_binding(scan, stmt, pos, shadowed_eager_calls)
    if not (isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Call)
            and _is_all_mutator_call(stmt.value)):
        _local_all_note_increment(scan, stmt, pos, shadowed_eager_calls)
    return False
def _init_all_param_binding(func_node: ast.AST,
                               scan: _FuncLocalAllScan) -> None:
    if any(arg.arg == '__all__' for arg in iter_arg_nodes(func_node.args)):
        _local_all_note_init(
            scan, func_node, (func_node.lineno, func_node.col_offset))
def _analyze_lambda_local_all(
        func_node: ast.Lambda,
        shadowed_eager_calls: frozenset[int]) -> _FuncLocalAllScan:
    scan = _FuncLocalAllScan()
    scan.root = func_node
    _init_all_param_binding(func_node, scan)
    stack: list[ast.AST] = [func_node.body]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Lambda):
            continue
        if (isinstance(node, ast.NamedExpr)
                and is_all_name_target(node.target)):
            pos = (node.lineno, node.col_offset)
            if _reads_all_before_binding(node.value, shadowed_eager_calls):
                scan.augs.append((node, pos))
                scan.has_local = True
            else:
                _local_all_note_init(scan, node, pos)
        elif isinstance(node, ast.Call) and _is_all_mutator_call(node):
            scan.direct_incs.append(
                (node, (node.lineno, node.col_offset)))
        stack.extend(ast.iter_child_nodes(node))
    return scan
def _analyze_func_local_all(
        func_node: ast.AST,
        shadowed_eager_calls: frozenset[int]) -> _FuncLocalAllScan:
    if isinstance(func_node, ast.Lambda):
        return _analyze_lambda_local_all(func_node, shadowed_eager_calls)
    scan = _FuncLocalAllScan(
        nonlocal_all=_has_nonlocal_all_declaration(func_node))
    scan.root = func_node
    _init_all_param_binding(func_node, scan)
    stack: list[ast.AST] = list(getattr(func_node, "body", []))
    while stack:
        stmt = stack.pop()
        if not _local_all_visit(scan, stmt, shadowed_eager_calls):
            stack.extend(ast.iter_child_nodes(stmt))
    return scan
def _non_global_class_inc_ids(
        block: ast.AST, shadowed_eager_calls: frozenset[int]) -> set[int]:
    ids: set[int] = set()
    if isinstance(block, ast.ClassDef):
        _outer, _class_local, _nested, _outer_deletes = (
            _scan_class_body_scope(block, shadowed_eager_calls))
        if "__all__" not in _global_names(block,
                                          include_class_bodies=False):
            ids.update(id(_s) for _s, _ in _outer)
        for _nc in _nested:
            ids |= _non_global_class_inc_ids(_nc, shadowed_eager_calls)
        return ids
    stack: list[ast.AST] = list(getattr(block, "body", []))
    while stack:
        stmt = stack.pop()
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            continue
        if isinstance(stmt, ast.ClassDef):
            ids |= _non_global_class_inc_ids(stmt, shadowed_eager_calls)
            continue
        stack.extend(ast.iter_child_nodes(stmt))
    return ids
def _partition_by_stmt_ids(
        items: list[_IncItem], stmt_ids: set[int] | frozenset[int],
) -> tuple[list[_IncItem], list[_IncItem]]:
    kept: list[_IncItem] = []
    hit: list[_IncItem] = []
    for _it in items:
        (hit if id(_it[0]) in stmt_ids else kept).append(_it)
    return kept, hit
def _move_func_local_augs(func_node: ast.AST,
                          scope_inc: list[_IncItem],
                          func_local_aug: list[_IncItem],
                          scope_mark: int,
                          shadowed_eager_calls: frozenset[int]) -> None:
    _scan = _analyze_func_local_all(func_node, shadowed_eager_calls)
    if not _scan.has_local:
        return
    _aug_hit = {id(_s) for _s, _ in _scan.reads_without_live_base(_scan.augs)}
    _direct_hit = {id(_s) for _s, _ in
                   _scan.reads_without_live_base(_scan.direct_incs)}
    _non_global = _non_global_class_inc_ids(
        func_node, shadowed_eager_calls)
    _class_hit = {id(_s) for _s, _ in
                  _scan.reads_without_live_base(_scan.class_incs)}
    _class_hit &= _non_global
    _moved_ids = _aug_hit | _direct_hit | _class_hit
    _drop_ids = {id(_s) for _s, _ in _scan.augs} - _aug_hit
    _drop_ids |= {id(_s) for _s, _ in _scan.direct_incs} - _direct_hit
    _drop_ids |= (({id(_s) for _s, _ in _scan.class_incs} & _non_global)
                  - _class_hit)
    if _moved_ids:
        scope_inc[scope_mark:], _moved = _partition_by_stmt_ids(
            scope_inc[scope_mark:], _moved_ids)
        func_local_aug.extend(_moved)
    if _drop_ids:
        scope_inc[scope_mark:], _ = _partition_by_stmt_ids(
            scope_inc[scope_mark:], _drop_ids)
def _scan_class_body_scope(
        class_node: ast.ClassDef,
        shadowed_eager_calls: frozenset[int],
) -> tuple[list[_IncItem], list[_IncItem], list[ast.ClassDef],
           list[_IncItem]]:
    base_nodes: list[_IncItem] = []
    delete_nodes: list[_IncItem] = []
    own_incs: list[_IncItem] = []
    nested_classes: list[ast.ClassDef] = []
    stack: list[ast.AST] = list(getattr(class_node, "body", []))
    while stack:
        stmt = stack.pop()
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            continue
        if isinstance(stmt, ast.ClassDef):
            nested_classes.append(stmt)
            continue
        if _is_complete_all_binding(stmt, shadowed_eager_calls):
            base_nodes.append((stmt, (stmt.lineno, stmt.col_offset)))
        if is_all_delete(stmt):
            delete_nodes.append((stmt, (stmt.lineno, stmt.col_offset)))
        if _is_all_increment_stmt(stmt, shadowed_eager_calls):
            own_incs.append((stmt, (stmt.lineno, stmt.col_offset)))
        stack.extend(ast.iter_child_nodes(stmt))
    parents = build_parent_map(class_node)
    base_guards = {
        pos: _conditional_branch_chain(node, parents)
        for node, pos in base_nodes}
    delete_guards = [
        (pos, _conditional_branch_chain(node, parents))
        for node, pos in delete_nodes]
    def has_covering_base(node: ast.AST, pos: tuple[int, int]) -> bool:
        read_guards = _conditional_branch_chain(node, parents)
        prior_bases = [base_pos for base_pos in base_guards
                       if base_pos < pos]
        covered_bases = _covering_base_positions(
            prior_bases, base_guards, read_guards)
        return any(
            not any(
                base_pos < delete_pos < pos
                and _AllScanState._base_branch_covers(
                    deleted_guards, read_guards)
                for delete_pos, deleted_guards in delete_guards)
            for base_pos in covered_bases)
    outer_incs: list[_IncItem] = []
    class_local_incs: list[_IncItem] = []
    for item in own_incs:
        node, pos = item
        (class_local_incs if has_covering_base(node, pos)
         else outer_incs).append(item)
    outer_deletes = [
        item for item in delete_nodes
        if len(_all_delete_targets(item[0])) > 1
        or not has_covering_base(item[0], item[1])]
    return outer_incs, class_local_incs, nested_classes, outer_deletes
def _analyze_class_body_all(
        class_node: ast.ClassDef,
        shadowed_eager_calls: frozenset[int]) -> list[_IncItem]:
    outer_incs, _class_local, nested_classes, _outer_deletes = (
        _scan_class_body_scope(class_node, shadowed_eager_calls))
    nested_incs: list[_IncItem] = []
    for _nc in nested_classes:
        nested_incs.extend(_analyze_class_body_all(
            _nc, shadowed_eager_calls))
    return nested_incs + outer_incs
def _covering_base_positions(
        bases: list[tuple[int, int]],
        base_guards: dict[tuple[int, int], tuple],
        read_guards: tuple) -> list[tuple[int, int]]:
    covered = {base for base in bases
               if _AllScanState._base_branch_covers(
                   base_guards.get(base, ()), read_guards)}
    alternatives: dict[tuple, dict[str, list[tuple[int, int]]]] = {}
    for base in bases:
        guards = base_guards.get(base, ())
        if not guards or guards[0][1] not in {'if_body', 'if_orelse'}:
            continue
        environment = guards[1:]
        if (environment
                and read_guards[-len(environment):] != environment):
            continue
        key = (guards[0][0], environment)
        alternatives.setdefault(key, {}).setdefault(
            guards[0][1], []).append(base)
    for branches in alternatives.values():
        if not {'if_body', 'if_orelse'} <= branches.keys():
            continue
        for positions in branches.values():
            covered.update(positions)
    return [base for base in bases if base in covered]


class _AllScanState:
    def __init__(self) -> None:
        self.base_pos: list[tuple[int, int]] = []
        self.base_nodes: list[_IncItem] = []
        self.delete_pos: list[tuple[int, int]] = []
        self.delete_nodes: list[_IncItem] = []
        self.unreachable_ids: set[int] = set()
        self.mod_block_inc: list[_IncItem] = []
        self.scope_inc: list[_IncItem] = []
        self.func_local_aug: list[_IncItem] = []
        self.func_base_pos: list[tuple[int, int]] = []
        self.func_base_nodes: list[_IncItem] = []
        self.func_base_names: set[str] = set()
        self.func_base_name_by_pos: dict[tuple[int, int], str] = {}
        self.direct_calls: list[tuple[tuple[int, int], str]] = []
        self.conditional_calls: set[tuple[int, int]] = set()
        self.direct_call_nodes: dict[tuple[int, int], ast.AST] = {}
        self.call_edges: set[tuple[str | None, str]] = set()
        self.include_annotations = True
        self.shadowed_eager_calls: frozenset[int] = frozenset()
        self.immediate_execution_ids: frozenset[int] = frozenset()
        self.parent: dict[int, ast.AST] = {}
        self.base_guards: dict[tuple[int, int], tuple] = {}
        self.delete_guards: dict[tuple[int, int], tuple] = {}
        self.top_increment_ids: set[int] = set()
        self.mod_block_delete: list[_IncItem] = []
        self.class_deletes: list[_IncItem] = []
    def live_bases(self, pos: tuple[int, int] | None = None,
                   node: ast.AST | None = None,
                   guarantee: bool = False) -> list[tuple[int, int]]:
        bases = (self.base_pos if pos is None
                 else [item for item in self.base_pos if item <= pos])
        guards = (_conditional_branch_chain(node, self.parent)
                  if node is not None else ())
        deletes = (self.delete_pos if pos is None
                   else [item for item in self.delete_pos if item < pos])
        if node is not None:
            deletes = [delete for delete in deletes
                       if not self._branches_disjoint(
                           self.delete_guards.get(delete, ()), guards)]
        if deletes:
            last_delete = max(deletes)
            bases = [item for item in bases if item > last_delete]
        if guarantee or node is not None:
            bases = _covering_base_positions(
                bases, self.base_guards, guards)
        return bases
    @staticmethod
    def _branches_disjoint(left: tuple, right: tuple) -> bool:
        for left_guard in left:
            for right_guard in right:
                if left_guard[0] != right_guard[0]:
                    continue
                labels = {left_guard[1], right_guard[1]}
                if labels == {'if_body', 'if_orelse'}:
                    return True
                if (left_guard[1] == right_guard[1] == 'match'
                        and left_guard[2] != right_guard[2]):
                    return True
        return False
    @staticmethod
    def _base_branch_covers(base_guards: tuple, read_guards: tuple) -> bool:
        return (not base_guards
                or base_guards == read_guards[-len(base_guards):])
def _dispatch_function_node(func_node: ast.AST, state: _AllScanState,
                            dispatch_nested: bool,
                            exec_order: bool = False) -> None:
    _globals = _global_names(func_node, include_class_bodies=True)
    if "__all__" not in _globals:
        _scan = _analyze_func_local_all(
            func_node, state.shadowed_eager_calls)
        if _scan.has_local:
            state.func_local_aug.extend(
                _scan.reads_without_live_base(_scan.augs))
            state.func_local_aug.extend(
                _scan.reads_without_live_base(_scan.direct_incs))
            state.func_local_aug.extend(
                _scan.reads_without_live_base(_scan.class_incs))
        else:
            sink = (state.mod_block_inc
                    if exec_order and id(func_node) in state.immediate_execution_ids
                    else state.scope_inc)
            sink.extend(_scan.direct_incs)
            sink.extend(_scan.class_incs)
        if dispatch_nested:
            for _nf in _collect_nested_funcs(func_node):
                _dispatch_function_node(_nf, state, False)
    else:
        _own_globals = _global_names(func_node, include_class_bodies=False)
        _scope_mark = len(state.scope_inc)
        _walk_all_stmts(func_node, state, _own_globals, False, False,
                        func_node.name, not dispatch_nested)
        if "__all__" not in _own_globals:
            _move_func_local_augs(func_node, state.scope_inc,
                                  state.func_local_aug, _scope_mark,
                                  state.shadowed_eager_calls)
_WalkFrame = tuple[ast.AST, set[str] | None, bool, bool, str | None,
                   bool]
class _ClassPostTask:
    __slots__ = ("cls_globals", "cls_node", "mark", "sink")
    def __init__(self, cls_node: ast.ClassDef,
                 cls_globals: set[str],
                 sink: list[_IncItem],
                 mark: int) -> None:
        self.cls_node = cls_node
        self.cls_globals = cls_globals
        self.sink = sink
        self.mark = mark
def _apply_class_post_filter(task: _ClassPostTask,
                             state: _AllScanState) -> None:
    if ("__all__" not in task.cls_globals
            and len(task.sink) > task.mark):
        _outer, class_local_incs, _nested, _outer_deletes = (
            _scan_class_body_scope(
                task.cls_node, state.shadowed_eager_calls))
        if class_local_incs:
            _drop = {id(_s) for _s, _ in class_local_incs}
            task.sink[task.mark:] = [
                _it for _it in task.sink[task.mark:]
                if id(_it[0]) not in _drop]
def _push_class_frames(stack: list, child: ast.ClassDef,
                       state: _AllScanState, frame: _WalkFrame) -> None:
    _, _, _, exec_order, cur_func, skip_nested_funcs = frame
    _cls_globals = _global_names(child, include_class_bodies=False)
    _sink = state.mod_block_inc if exec_order else state.scope_inc
    _mark = len(_sink)
    if exec_order:
        _record_bare_decorator_calls(child.decorator_list,
                                      state)
    stack.append(_ClassPostTask(child, _cls_globals, _sink,
                                _mark))
    stack.append((child, _cls_globals, False, exec_order,
                  cur_func, skip_nested_funcs))
def _binds_effective_base(child: ast.AST,
                          func_globals: set[str] | None,
                          shadowed_eager_calls: frozenset[int]) -> bool:
    if not binds_all_name(child):
        return False
    value = getattr(child, "value", None)
    if value is not None and _reads_all_before_binding(
            value, shadowed_eager_calls):
        return False
    return func_globals is None or "__all__" in func_globals
def _record_base_position(child: ast.AST, state: _AllScanState,
                          exec_order: bool,
                          cur_func: str | None) -> None:
    pos = (child.lineno, child.col_offset)
    if exec_order:
        state.base_pos.append(pos)
        state.base_nodes.append((child, pos))
        return
    state.func_base_pos.append(pos)
    state.func_base_nodes.append((child, pos))
    if cur_func is not None:
        state.func_base_names.add(cur_func)
        state.func_base_name_by_pos[pos] = cur_func
def _record_increment_position(child: ast.AST, state: _AllScanState,
                               exec_order: bool) -> None:
    pos = (child.lineno, child.col_offset)
    if exec_order:
        state.mod_block_inc.append((child, pos))
    else:
        state.scope_inc.append((child, pos))
def _record_direct_call(state: _AllScanState, node: ast.AST,
                        name: str) -> None:
    pos = (node.lineno, node.col_offset)
    state.direct_calls.append((pos, name))
    state.direct_call_nodes[pos] = node
def _record_child_facts(child: ast.AST, state: _AllScanState,
                        frame: _WalkFrame) -> None:
    _, func_globals, top_level, exec_order, cur_func, _ = frame
    if _binds_effective_base(
            child, func_globals, state.shadowed_eager_calls):
        _record_base_position(child, state, exec_order, cur_func)
        return
    is_expr_mutator = (isinstance(child, ast.Expr)
                       and isinstance(child.value, ast.Call)
                       and _is_all_mutator_call(child.value))
    if (_is_all_increment_stmt(child, state.shadowed_eager_calls)
            and not top_level and not is_expr_mutator):
        _record_increment_position(child, state, exec_order)
        return
    if (is_all_delete(child)
            and (func_globals is None or '__all__' in func_globals)):
        pos = (child.lineno, child.col_offset)
        if exec_order:
            state.delete_pos.append(pos)
            state.delete_nodes.append((child, pos))
            if not top_level:
                state.mod_block_delete.append((child, pos))
        else:
            state.scope_inc.append((child, pos))
        return
    if (exec_order and isinstance(child, ast.Call)
            and isinstance(child.func, ast.Name)):
        _record_direct_call(state, child, child.func.id)
def _handle_function_child(child: ast.AST, state: _AllScanState,
                           exec_order: bool) -> None:
    if exec_order:
        _collect_def_site_calls(child, state)
    _dispatch_function_node(child, state, True, exec_order=exec_order)
def _walk_all_stmts(node: ast.AST, state: _AllScanState,
                    func_globals: set[str] | None,
                    top_level: bool, exec_order: bool = True,
                    cur_func: str | None = None,
                    skip_nested_funcs: bool = False) -> None:
    stack: list[_WalkFrame | _ClassPostTask] = [
        (node, func_globals, top_level, exec_order, cur_func,
         skip_nested_funcs)]
    while stack:
        frame = stack.pop()
        if isinstance(frame, _ClassPostTask):
            _apply_class_post_filter(frame, state)
            continue
        for child in ast.iter_child_nodes(frame[0]):
            _dispatch_walk_child(child, stack, state, frame)
def _dispatch_walk_child(child: ast.AST, stack: list, state: _AllScanState,
                         frame: _WalkFrame) -> None:
    (_, func_globals, _top_level, exec_order, cur_func,
     skip_nested_funcs) = frame
    if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
        if skip_nested_funcs:
            return
        _handle_function_child(child, state, exec_order)
        return
    if isinstance(child, ast.ClassDef):
        _push_class_frames(stack, child, state, frame)
        return
    if isinstance(child, ast.Lambda):
        if exec_order:
            _collect_def_site_calls(child, state)
        _dispatch_function_node(child, state, True, exec_order=exec_order)
        return
    if isinstance(child, _TYPE_PARAM_NODES):
        return
    _record_child_facts(child, state, frame)
    stack.append((child, func_globals, False, exec_order,
                  cur_func, skip_nested_funcs))
def _record_bare_decorator_calls(decorator_list: list[ast.AST],
                                 state: _AllScanState) -> None:
    for _d in decorator_list:
        if isinstance(_d, ast.Name):
            _record_direct_call(state, _d, _d.id)
def _def_site_exprs(func_node: ast.AST,
                    include_annotations: bool) -> list:
    return [*getattr(func_node, "decorator_list", []),
            *_signature_exprs(func_node, include_annotations)]
def _arg_annotation_exprs(args: ast.arguments | None) -> list[ast.AST]:
    if args is None:
        return []
    nodes = (*args.posonlyargs, *args.args, *args.kwonlyargs,
             args.vararg, args.kwarg)
    return [_a.annotation for _a in nodes
            if _a is not None and _a.annotation is not None]
def _signature_exprs(func_node: ast.AST,
                     include_annotations: bool = True) -> list[ast.AST]:
    exprs: list[ast.AST] = []
    args = getattr(func_node, "args", None)
    if args is not None:
        exprs.extend(args.defaults)
        exprs.extend(_d for _d in args.kw_defaults if _d is not None)
    if include_annotations:
        exprs.extend(_arg_annotation_exprs(args))
        returns = getattr(func_node, "returns", None)
        if returns is not None:
            exprs.append(returns)
    return exprs
def _collect_def_site_calls(func_node: ast.AST,
                            state: _AllScanState) -> None:
    _record_bare_decorator_calls(
        list(getattr(func_node, "decorator_list", [])), state)
    stack: list[ast.AST] = _def_site_exprs(
        func_node, state.include_annotations)
    while stack:
        n = stack.pop()
        if isinstance(n, ast.Lambda):
            stack.extend(n.args.defaults)
            stack.extend(_d for _d in n.args.kw_defaults
                         if _d is not None)
            continue
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name):
            _record_direct_call(state, n, n.func.id)
        stack.extend(ast.iter_child_nodes(n))
def _collect_nested_funcs(func_node: ast.AST) -> list[ast.AST]:
    result: list[ast.AST] = []
    stack: list[ast.AST] = list(ast.iter_child_nodes(func_node))
    while stack:
        n = stack.pop()
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            result.append(n)
        stack.extend(ast.iter_child_nodes(n))
    return result
_TYPE_PARAM_NODES: tuple = tuple(
    _tp for _tp in (
        getattr(ast, "TypeVar", None),
        getattr(ast, "ParamSpec", None),
        getattr(ast, "TypeVarTuple", None),
    ) if _tp is not None)
def _call_edge_child(ch: ast.AST, cur_func: str | None
                     ) -> tuple[ast.AST, str | None, str | None] | None:
    if isinstance(ch, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return ch, ch.name, None
    if isinstance(ch, ast.Lambda):
        return ch, cur_func, None
    if isinstance(ch, _TYPE_PARAM_NODES):
        return None
    if isinstance(ch, ast.Call) and isinstance(ch.func, ast.Name):
        return ch, cur_func, ch.func.id
    return ch, cur_func, None
def _collect_call_edges(tree: ast.AST) -> set[tuple[str | None, str]]:
    edges: set[tuple[str | None, str]] = set()
    stack: list[tuple[ast.AST, str | None]] = [(tree, None)]
    while stack:
        node, cur_func = stack.pop()
        for ch in ast.iter_child_nodes(node):
            stepped = _call_edge_child(ch, cur_func)
            if stepped is None:
                continue
            child, frame, callee = stepped
            if callee is not None:
                edges.add((cur_func, callee))
            stack.append((child, frame))
    return edges
def _direct_call_node_matches(node: ast.AST, name: str) -> bool:
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        return node.func.id == name
    if isinstance(node, ast.Name):
        return node.id == name
    return isinstance(node, ast.Attribute) and node.attr == name
_CONDITIONAL_COMPREHENSION_SCOPES: tuple[type, ...] = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
def _loop_body_guaranteed(loop: ast.AST) -> bool:
    """循环体是否静态保证至少执行一次。

    ``while True`` 与非空字面量可迭代对象的 ``for`` 循环，其循环体/target
    绑定必然执行；继续标成条件分支会让 ``check_all_overwrite`` 把这些基值
    当成"可能未执行"，对合法代码报 ALL_NO_BASE。
    """
    if isinstance(loop, (ast.For, ast.AsyncFor)):
        iter_node = loop.iter
        if isinstance(iter_node, (ast.Tuple, ast.List, ast.Set)):
            return bool(iter_node.elts)
        if isinstance(iter_node, ast.Dict):
            return bool(iter_node.keys)
        if isinstance(iter_node, ast.Constant) and isinstance(
                iter_node.value, (str, bytes)):
            return bool(iter_node.value)
        if (isinstance(iter_node, ast.Call)
                and isinstance(iter_node.func, ast.Name)
                and iter_node.func.id == "range" and not iter_node.keywords
                and not any(isinstance(arg, ast.Starred)
                            for arg in iter_node.args)
                and len(iter_node.args) in (1, 2)
                and all(isinstance(arg, ast.Constant)
                        and type(arg.value) is int
                        for arg in iter_node.args)):
            bounds = [arg.value for arg in iter_node.args]
            return bounds[-1] > (bounds[0] if len(bounds) == 2 else 0)
        return False
    test = getattr(loop, "test", None)
    return test is not None and _literal_truth(test) is True
def _conditional_branch_key(p: ast.AST, cur: ast.AST) -> tuple | None:
    if isinstance(p, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        body = p.body
        in_body = cur in body if isinstance(body, list) else cur is body
        return (id(p), 'body') if in_body else None
    if isinstance(p, ast.If):
        truth = _literal_truth(p.test)
        if cur in p.body:
            return None if truth is True else (id(p), 'if_body')
        if cur in p.orelse:
            return None if truth is False else (id(p), 'if_orelse')
        return None
    if isinstance(p, (ast.For, ast.AsyncFor, ast.While)):
        if ((isinstance(p, (ast.For, ast.AsyncFor)) and cur is p.target)
                or cur in p.body):
            if _loop_body_guaranteed(p):
                return None
            return id(p), 'body'
        if cur in p.orelse:
            return id(p), 'orelse'
        return None
    if isinstance(p, ast.Match):
        return (id(p), 'match', id(cur)) if cur in p.cases else None
    if isinstance(p, TRY_NODE_TYPES):
        if (cur in p.body
                and any(block_may_fall_through(handler.body)
                        for handler in p.handlers)):
            return id(p), 'body'
        if cur in p.handlers:
            return id(p), 'handler', id(cur)
        if cur in p.orelse:
            return id(p), 'orelse'
        return None
    if isinstance(p, ast.match_case):
        return id(p), 'case'
    if isinstance(p, ast.comprehension):
        if cur in p.ifs:
            return id(p), 'if', p.ifs.index(cur)
        return None
    if isinstance(p, _CONDITIONAL_COMPREHENSION_SCOPES):
        if p.generators and cur is p.generators[0]:
            return None
        return id(p), 'comprehension', id(cur)
    if isinstance(p, ast.BoolOp):
        return ((id(p), 'value', p.values.index(cur))
                if cur is not p.values[0] else None)
    if isinstance(p, ast.IfExp):
        return ((id(p), 'body' if cur is p.body else 'orelse')
                if cur is not p.test else None)
    return None
# 历史缺陷（DC-03 / PY-05）：本模块曾在此处先定义过一份「只看最后一条语句」的
# ``_block_terminates``，文件后部又基于 ``_block_completion_modes`` 定义了同名实现——
# 后者在模块导入时静默覆盖前者，前一份逻辑完全失效却仍留在源码里被引用与审阅。
# 已删除死定义与仅服务于它的 ``_TERMINATING_STATEMENTS`` 常量，
# 唯一实现在 ``_block_completion_modes`` 之后。

def _terminating_branch_guards(tree: ast.AST) -> dict[int, str]:
    """收集「另一分支必然终止」的 If 守卫。

    形如 ``if cond: x = ...\nelse: continue`` 的分支中，存活分支一旦执行
    就必然赋好值；它的绑定不是条件绑定。若不剥离该守卫，死分支会把存活
    分支的赋值当成「可能未执行」，产生「引用未定义的名称」误报。

    返回值映射 ``id(if_node) -> 应视作无条件的守卫标签``。
    """
    guards: dict[int, str] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.If):
            continue
        body_terminates = _block_terminates(node.body)
        else_terminates = _block_terminates(node.orelse)
        if body_terminates == else_terminates:
            # 两支都终止时后续代码不可达（另有 unreachable 通道处理），
            # 都未终止时守卫是真条件守卫，均不参与豁免。
            continue
        guards[id(node)] = 'if_orelse' if body_terminates else 'if_body'
    return guards


def _conditional_branch_chain(node: ast.AST,
                              parent: dict[int, ast.AST]) -> tuple:
    branches: list[tuple] = []
    cur = node
    while True:
        p = parent.get(id(cur))
        if p is None:
            return tuple(branches)
        branch = _conditional_branch_key(p, cur)
        if branch is not None:
            branches.append(branch)
        cur = p
def _has_conditional_execution_path(node: ast.AST,
                                    parent: dict[int, ast.AST]) -> bool:
    cur = node
    while True:
        p = parent.get(id(cur))
        if p is None:
            return False
        if _conditional_branch_key(p, cur) is not None:
            return True
        cur = p
def _is_plain_class_body_node(node: ast.AST, parent: dict[int, ast.AST],
                              top: ast.AST) -> bool:
    cur = node
    in_definition_head = False
    while cur is not top:
        p = parent.get(id(cur))
        if p is None:
            return False
        if isinstance(p, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            body = p.body
            in_body = cur in body if isinstance(body, list) else cur is body
            if not in_body:
                in_definition_head = True
        if isinstance(p, ast.ClassDef) and cur in p.body:
            return not in_definition_head
        cur = p
    return False
def _top_level_mutator_calls(
        tree: ast.Module, parent: dict[int, ast.AST],
        unreachable_ids: set[int]) -> list[ast.Call]:
    calls: list[ast.Call] = []
    for top in tree.body:
        for node in walk_nodes(top):
            if not (isinstance(node, ast.Call) and _is_all_mutator_call(node)):
                continue
            if id(node) in unreachable_ids:
                continue
            if _has_conditional_execution_path(node, parent):
                continue
            if _is_plain_class_body_node(node, parent, top):
                continue
            calls.append(node)
    return sorted(calls, key=lambda node: (node.lineno, node.col_offset))
def _literal_truth(node: ast.AST) -> bool | None:
    try:
        return bool(ast.literal_eval(node))
    except (ValueError, TypeError, SyntaxError):
        return None
def _has_unreachable_execution_path(node: ast.AST,
                                    parent: dict[int, ast.AST]) -> bool:
    cur = node
    while True:
        p = parent.get(id(cur))
        if p is None:
            return False
        if isinstance(p, ast.If):
            truth = _literal_truth(p.test)
            if truth is not None:
                if cur in p.body and not truth:
                    return True
                if cur in p.orelse and truth:
                    return True
        elif isinstance(p, ast.While):
            truth = _literal_truth(p.test)
            if cur in p.body and truth is False:
                return True
            if cur in p.orelse and truth is True:
                return True
        elif isinstance(p, (ast.For, ast.AsyncFor)):
            truth = _literal_truth(p.iter)
            if ((cur is p.target or cur in p.body) and truth is False):
                return True
        cur = p
def _unreachable_node_ids(tree: ast.Module,
                          parent: dict[int, ast.AST]) -> set[int]:
    return {id(node) for node in walk_nodes(tree)
            if _has_unreachable_execution_path(node, parent)}
def _reachable_positions(items: list[_IncItem],
                         unreachable_ids: set[int]) -> list[tuple[int, int]]:
    return [pos for node, pos in items if id(node) not in unreachable_ids]
def _conditional_call_sites(
        tree: ast.Module, direct_calls: list[tuple[tuple[int, int], str]],
        parent: dict[int, ast.AST]) -> set[tuple[int, int]]:
    by_pos: dict[tuple[int, int], list[ast.AST]] = {}
    for node in walk_nodes(tree):
        lineno = getattr(node, "lineno", None)
        col = getattr(node, "col_offset", None)
        if lineno is not None and col is not None:
            by_pos.setdefault((lineno, col), []).append(node)
    conditional: set[tuple[int, int]] = set()
    for pos, name in direct_calls:
        for node in by_pos.get(pos, []):
            if (_direct_call_node_matches(node, name)
                    and _has_conditional_execution_path(node, parent)):
                conditional.add(pos)
                break
    return conditional
def _has_prior_call(state: _AllScanState,
                    pos: tuple[int, int]) -> bool:
    seeds = {cname for cpos, cname in state.direct_calls
             if cpos <= pos and cpos not in state.conditional_calls}
    if seeds & state.func_base_names:
        return True
    if not state.call_edges:
        return False
    reach = set(seeds)
    pending = list(seeds)
    while pending:
        caller = pending.pop()
        for source, callee in state.call_edges:
            if source == caller and callee not in reach:
                reach.add(callee)
                pending.append(callee)
    return bool(reach & state.func_base_names)
_NAME_ERROR_GUARD: tuple[str, ...] = (
    "NameError", "Exception", "BaseException")
def _handler_catches(exc_type: ast.expr | None) -> bool:
    return exc_type is None or exception_matches(
        exc_type, _NAME_ERROR_GUARD)
def _try_guarded(stmt: ast.AST, parent: dict[int, ast.AST]) -> bool:
    _F_EDGE = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
    cur: ast.AST = stmt
    p = parent.get(id(cur))
    while p is not None:
        if isinstance(p, _F_EDGE):
            return False
        if (isinstance(p, TRY_NODE_TYPES) and cur in p.body
                and any(_handler_catches(_h.type) for _h in p.handlers)):
            return True
        cur = p
        p = parent.get(id(cur))
    return False
def _report_all_overwrite(defects: list[FileDefect],
                          all_nodes: list[ast.AST], rel_path: str) -> None:
    if len(all_nodes) <= 1:
        return
    lines = [n.lineno for n in all_nodes]
    defects.append(FileDefect(
        defect_type=DefectType.ALL_OVERWRITE,
        severity="P0",
        filepath=rel_path,
        lineno=lines[0],
        end_lineno=lines[-1],
        message=f"__all__ 被多次赋值覆盖，位置: {lines}",
        suggestion="删除多余的 __all__ 赋值，仅保留最后一个有效定义",
        confidence=0.95,
        detail={"all_assignments": lines},
    ))
def check_all_overwrite(tree: ast.Module, rel_path: str) -> list[FileDefect]:
    defects: list[FileDefect] = []
    state = _AllScanState()
    scope_index = _UndefinedScopeIndex(tree)
    state.shadowed_eager_calls = _shadowed_eager_call_ids(tree, scope_index)
    state.immediate_execution_ids = _immediate_execution_scope_ids(
        tree, state.shadowed_eager_calls)
    state.include_annotations = not module_postpones_annotations(tree)
    state.call_edges = _collect_call_edges(tree)
    _walk_all_stmts(tree, state, None, True)
    _parent = build_parent_map(tree)
    state.parent = _parent
    state.base_guards = {
        pos: _conditional_branch_chain(node, _parent)
        for node, pos in state.base_nodes}
    state.delete_guards = {
        pos: _conditional_branch_chain(node, _parent)
        for node, pos in state.delete_nodes}
    state.unreachable_ids = _unreachable_node_ids(tree, _parent)
    state.func_base_nodes = [
        item for item in state.func_base_nodes
        if id(item[0]) not in state.unreachable_ids]
    state.func_base_pos = [pos for _node, pos in state.func_base_nodes]
    state.func_base_names = {
        state.func_base_name_by_pos[pos]
        for pos in state.func_base_pos
        if pos in state.func_base_name_by_pos}
    state.class_deletes = [
        item for class_node in walk_nodes(tree)
        if isinstance(class_node, ast.ClassDef)
        and '__all__' not in _global_names(
            class_node, include_class_bodies=False)
        and not _has_nonlocal_all_declaration(class_node)
        for item in _scan_class_body_scope(
            class_node, state.shadowed_eager_calls)[3]]
    state.base_pos = _reachable_positions(
        state.base_nodes, state.unreachable_ids)
    state.delete_pos = _reachable_positions(
        state.delete_nodes, state.unreachable_ids)
    state.conditional_calls = _conditional_call_sites(
        tree, state.direct_calls, _parent)
    top_calls = _top_level_mutator_calls(
        tree, _parent, state.unreachable_ids)
    state.top_increment_ids = {id(node) for node in top_calls}
    all_nodes: list[ast.AST] = []
    operations: list[tuple[tuple[int, int], str, ast.AST]] = []
    for node in ast.iter_child_nodes(tree):
        if _is_complete_all_assign(node, state.shadowed_eager_calls):
            all_nodes.append(node)
        is_expr_mutator = (isinstance(node, ast.Expr)
                           and isinstance(node.value, ast.Call)
                           and _is_all_mutator_call(node.value))
        if (_is_all_increment_stmt(node, state.shadowed_eager_calls)
                and not is_expr_mutator):
            operations.append(
                ((node.lineno, node.col_offset), 'increment', node))
        if is_all_delete(node):
            operations.append(
                ((node.lineno, node.col_offset), 'delete', node))
    operations.extend(
        ((node.lineno, node.col_offset), 'increment', node)
        for node in top_calls)
    for _pos, kind, node in sorted(operations, key=lambda item: item[0]):
        reporter = (_report_top_increment_no_base if kind == 'increment'
                    else _report_top_delete_no_base)
        reporter(defects, node, rel_path, state)
    _report_all_overwrite(defects, all_nodes, rel_path)
    _report_func_local_channel(defects, rel_path, state, _parent)
    _report_mod_block_channel(defects, rel_path, state, _parent)
    _report_mod_block_delete_channel(defects, rel_path, state, _parent)
    _report_class_delete_channel(defects, rel_path, state, _parent)
    _report_scope_channel(defects, rel_path, state, _parent, tree,
                          scope_index)
    if defects:
        logger.debug("A1 __all__ 结构缺陷检出: file=%s defects=%d kinds=%s",
                     rel_path, len(defects),
                     sorted({d.defect_type for d in defects}))
    return defects
def _all_delete_targets(node: ast.AST) -> list[ast.expr]:
    return [leaf for target in getattr(node, 'targets', ())
            for leaf in flatten_unpack_targets(target)
            if is_all_name_target(leaf)]
def _delete_no_base_target(node: ast.AST,
                           state: _AllScanState) -> ast.expr | None:
    targets = _all_delete_targets(node)
    statement_pos = (node.lineno, node.col_offset)
    for index, target in enumerate(targets):
        if index:
            return target
        if (not state.live_bases(statement_pos, node=target)
                and not _has_prior_call(state, statement_pos)):
            return target
    return None
def _report_top_delete_no_base(defects: list[FileDefect], node: ast.AST,
                               rel_path: str,
                               state: _AllScanState) -> None:
    target = _delete_no_base_target(node, state)
    if target is None:
        return
    defects.append(FileDefect(
        defect_type=DefectType.ALL_NO_BASE,
        severity="P0",
        filepath=rel_path,
        lineno=target.lineno,
        message=(f"__all__ 删除操作（第 {target.lineno} 行）无前置基值赋值，"
                 f"import 时将 NameError"),
        suggestion="在删除前完成基值赋值，或删除该语句",
        confidence=0.92,
        detail={"delete_lineno": target.lineno,
                "kind": "top_delete_no_base"},
    ))
def _report_top_increment_no_base(defects: list[FileDefect], node: ast.AST,
                                  rel_path: str,
                                  state: _AllScanState) -> None:
    if not (_is_all_increment_stmt(node, state.shadowed_eager_calls)
            and not state.live_bases(
                (node.lineno, node.col_offset), node=node)
            and not _has_prior_call(
                state, (node.lineno, node.col_offset))):
        return
    defects.append(FileDefect(
        defect_type=DefectType.ALL_NO_BASE,
        severity="P0",
        filepath=rel_path,
        lineno=node.lineno,
        message=(f"__all__ 增量操作（第 {node.lineno} 行）无前置基值赋值，"
                 f"import 时将 NameError/AttributeError"),
        suggestion=("在增量操作前添加完整基值赋值 __all__ = [...]，"
                    "或合并为单次完整赋值"),
        confidence=0.92,
        detail={"increment_lineno": node.lineno,
                "base_lines": sorted(
                    {ln for ln, _c in state.live_bases(
                        (node.lineno, node.col_offset), node=node)})},
    ))
def _enclosing_function_nodes(node: ast.AST,
                              parent: dict[int, ast.AST]) -> list[ast.AST]:
    nodes: list[ast.AST] = []
    cur = node
    p = parent.get(id(cur))
    while p is not None:
        if isinstance(p, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            nodes.append(p)
        cur = p
        p = parent.get(id(cur))
    return nodes
def _function_binds_all_value(
        func_node: ast.AST,
        shadowed_eager_calls: frozenset[int]) -> bool:
    return (_analyze_func_local_all(
        func_node, shadowed_eager_calls).first_init is not None)
def _functions_with_local_base(tree: ast.Module,
                               state: _AllScanState) -> set[int]:
    if not state.func_base_pos:
        return set()
    spans = sorted(
        ((n.end_lineno or n.lineno) - n.lineno, n.lineno,
         n.end_lineno or n.lineno, id(n))
        for n in walk_nodes(tree)
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)))
    owners: set[int] = set()
    for pos in state.func_base_pos:
        line = pos[0]
        for _size, start, end, fid in spans:
            if start <= line <= end:
                owners.add(fid)
                break
    return owners
def _local_base_execution_status(
        item: _IncItem, parent: dict[int, ast.AST], base_owners: set[int],
        shadowed_eager_calls: frozenset[int],
        scope_index: _UndefinedScopeIndex) -> tuple[bool, bool]:
    read_nodes = [node for node in walk_nodes(item[0])
                  if isinstance(node, ast.Name) and node.id == '__all__']
    early = False
    for func in _enclosing_function_nodes(item[0], parent):
        if not (id(func) in base_owners
                or _function_binds_all_value(func, shadowed_eager_calls)):
            continue
        if any(scope_index.is_early_closure_read(node, func, '__all__')
               for node in read_nodes):
            early = True
            continue
        return True, False
    return False, early
def _append_increment_defect(defects: list[FileDefect], rel_path: str, *,
                             line: tuple[int, int], message: str,
                             suggestion: str, confidence: float,
                             increment_lines: set[int], kind: str,
                             base_lines: list[int] | None = None) -> None:
    detail: dict[str, Any] = {
        "increment_lines": sorted(increment_lines), "kind": kind}
    if base_lines is not None:
        detail["base_lines"] = base_lines
    defects.append(FileDefect(
        defect_type=DefectType.ALL_NO_BASE,
        severity="P1",
        filepath=rel_path,
        lineno=line[0],
        message=message,
        suggestion=suggestion,
        confidence=confidence,
        detail=detail,
    ))
def _func_local_increment_form(stmt: ast.AST) -> str:
    if isinstance(stmt, ast.Delete):
        return "del __all__ 操作"
    if isinstance(stmt, ast.AugAssign):
        return "__all__ += 操作"
    if (isinstance(stmt, ast.Call)
            or (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Call))):
        return "__all__.append/extend/insert 增量操作"
    return "__all__ 自引用重绑定（= __all__ + ...）"
def _report_func_local_channel(
    defects: list[FileDefect],
    rel_path: str,
    state: _AllScanState,
    parent: dict[int, ast.AST],
) -> None:
    _func_hit = [item for item in state.func_local_aug
                 if id(item[0]) not in state.unreachable_ids
                 and not _try_guarded(item[0], parent)]
    if not _func_hit:
        return
    _first_item = min(_func_hit, key=lambda _it: _it[1])
    _first = _first_item[1]
    _form = _func_local_increment_form(_first_item[0])
    _append_increment_defect(
        defects, rel_path, line=_first,
        message=(f"{_form}（第 {_first[0]} 行，函数体内且未声明"
                 f" global）执行时 __all__ 尚无函数内有效绑定，"
                 f"访问未初始化的局部变量，被调用时必 UnboundLocalError"
                 f"（与模块级基值无关）"),
        suggestion=("在函数内添加 global __all__ 声明，"
                    "或在所有读取前完成基值赋值"),
        confidence=0.85,
        increment_lines={item[1][0] for item in _func_hit},
        kind="func_local_unbound")
def _report_mod_block_channel(
    defects: list[FileDefect],
    rel_path: str,
    state: _AllScanState,
    parent: dict[int, ast.AST],
) -> None:
    _mod_hit = [item for item in state.mod_block_inc
                if id(item[0]) not in state.unreachable_ids
                and id(item[0]) not in state.top_increment_ids
                and not state.live_bases(item[1], node=item[0])
                and not _has_prior_call(state, item[1])
                and not _try_guarded(item[0], parent)]
    if not _mod_hit:
        return
    _first = min(item[1] for item in _mod_hit)
    _append_increment_defect(
        defects, rel_path, line=_first,
        message=(f"__all__ 增量操作（第 {_first[0]} 行，模块级嵌套块内）"
                 f"先于全部基值赋值（执行序保证届时未绑定），"
                 f"条件成立时将 NameError"),
        suggestion=("将基值赋值移至增量之前，"
                    "或合并为单次完整赋值"),
        confidence=0.85,
        increment_lines={item[1][0] for item in _mod_hit},
        kind="mod_block_no_prior_base")
def _report_mod_block_delete_channel(
    defects: list[FileDefect],
    rel_path: str,
    state: _AllScanState,
    parent: dict[int, ast.AST],
) -> None:
    hits: list[tuple[_IncItem, ast.expr]] = []
    for item in state.mod_block_delete:
        node = item[0]
        if (id(node) in state.unreachable_ids
                or _try_guarded(node, parent)):
            continue
        target = _delete_no_base_target(node, state)
        if target is not None:
            hits.append((item, target))
    if not hits:
        return
    first_item, first_target = min(hits, key=lambda hit: hit[0][1])
    first_pos = first_item[1]
    defects.append(FileDefect(
        defect_type=DefectType.ALL_NO_BASE,
        severity="P1",
        filepath=rel_path,
        lineno=first_target.lineno,
        message=(f"__all__ 删除操作（第 {first_target.lineno} 行，"
                 f"模块级嵌套块内）无有效前置基值，条件成立时将 NameError"),
        suggestion="在删除前完成基值赋值，或删除该语句",
        confidence=0.85,
        detail={"delete_lines": sorted({target.lineno for _item, target in hits}),
                "kind": "mod_block_delete_no_base",
                "base_lines": sorted(
                    ln for ln, _col in state.live_bases(
                        first_pos, node=first_target))},
    ))
def _report_class_delete_channel(
    defects: list[FileDefect],
    rel_path: str,
    state: _AllScanState,
    parent: dict[int, ast.AST],
) -> None:
    hits: list[tuple[_IncItem, ast.expr]] = []
    for item in state.class_deletes:
        node = item[0]
        if (id(node) in state.unreachable_ids
                or _try_guarded(node, parent)):
            continue
        targets = _all_delete_targets(node)
        if not targets:
            continue
        target = targets[1] if len(targets) > 1 else targets[0]
        hits.append((item, target))
    if not hits:
        return
    _first_item, first_target = min(hits, key=lambda hit: hit[0][1])
    defects.append(FileDefect(
        defect_type=DefectType.ALL_NO_BASE,
        severity="P1",
        filepath=rel_path,
        lineno=first_target.lineno,
        message=(f"__all__ 删除操作（第 {first_target.lineno} 行，类体内且未声明"
                 f" global/nonlocal）无有效类局部基值，执行类体时将 NameError"
                 f"（模块或外层函数基值不参与类局部删除）"),
        suggestion=("在类体内删除前完成 __all__ 基值赋值；若目标是外部绑定，"
                    "先声明 global/nonlocal 并确保外部基值有效"),
        confidence=0.85,
        detail={"delete_lines": sorted({target.lineno for _item, target in hits}),
                "kind": "class_local_delete_no_base"},
    ))
def _direct_calls_without_live_base(state: _AllScanState) -> set[str]:
    return {name for pos, name in state.direct_calls
            if pos not in state.conditional_calls
            and not state.live_bases(
                pos, node=state.direct_call_nodes.get(pos))}
def _report_scope_channel(
    defects: list[FileDefect],
    rel_path: str,
    state: _AllScanState,
    parent: dict[int, ast.AST],
    tree: ast.Module,
    scope_index: _UndefinedScopeIndex,
) -> None:
    _base_owners = _functions_with_local_base(tree, state)
    _unguarded = []
    _early_closure_ids: set[int] = set()
    for item in state.scope_inc:
        if (id(item[0]) in state.unreachable_ids
                or _try_guarded(item[0], parent)):
            continue
        covered, early_closure = _local_base_execution_status(
            item, parent, _base_owners, state.shadowed_eager_calls,
            scope_index)
        if covered:
            continue
        _unguarded.append(item)
        if early_closure:
            _early_closure_ids.add(id(item[0]))
    if not _unguarded:
        return
    _final_bases = state.live_bases(guarantee=True)
    _early_call = bool(_final_bases)
    if _early_call:
        _called_without_base = _direct_calls_without_live_base(state)
        _unguarded = [
            item for item in _unguarded
            if id(item[0]) in _early_closure_ids
            or any(getattr(func, "name", None) in _called_without_base
                   for func in _enclosing_function_nodes(item[0], parent))]
    if not _unguarded:
        return
    _first_item = min(_unguarded, key=lambda item: item[1])
    _first = _first_item[1]
    _early_closure = id(_first_item[0]) in _early_closure_ids
    _kind = ("closure_inc_called_before_local_base" if _early_closure else
             "scope_inc_called_before_base" if _early_call
             else "scope_inc_no_base")
    _message = (
        f"__all__ 增量操作（第 {_first[0]} 行，闭包内）在外层局部基值"
        f"建立前经嵌套直接调用执行，调用时将 NameError" if _early_closure else
        f"__all__ 增量操作（第 {_first[0]} 行，非顶层）在模块基值建立前"
        f"经顶层直接调用执行，调用时将 NameError" if _early_call else
        f"__all__ 增量操作（第 {_first[0]} 行，非顶层）所在文件"
        f"无任何有效基值赋值，条件成立/被调用时将 NameError")
    _append_increment_defect(
        defects, rel_path, line=_first,
        message=_message,
        suggestion="添加模块级基值赋值 __all__ = [...]，或移除非公开模块中的增量操作",
        confidence=0.85 if _early_call else 0.8,
        increment_lines={item[1][0] for item in _unguarded},
        kind=_kind,
        base_lines=sorted(ln for ln, _col in _final_bases))
_MODULE_DUNDER_NAMES = frozenset({
    "__name__", "__file__", "__doc__", "__builtins__",
    "__path__", "__package__", "__spec__", "__loader__", "__cached__",
})
_BUILTIN_NAMES = frozenset(dir(builtins)) | _MODULE_DUNDER_NAMES
def _immediate_execution_scope_ids(
        tree: ast.Module,
        shadowed_eager_calls: frozenset[int]) -> frozenset[int]:
    parents = build_parent_map(tree)
    immediate: set[int] = set()
    while True:
        changed = False
        for node in walk_nodes(tree):
            if id(node) in immediate:
                continue
            parent = parents.get(id(node))
            if isinstance(node, ast.Lambda):
                found = (isinstance(parent, ast.Call)
                         and parent.func is node
                         and _is_zero_arg_lambda_call(parent))
            elif isinstance(node, ast.GeneratorExp):
                found = False
                if isinstance(parent, ast.Call) and parent.args:
                    name = (parent.func.id
                            if isinstance(parent.func, ast.Name) else '')
                    arities = _EAGER_GENEXP_CALL_ARITIES.get(name)
                    found = bool(
                        _consumed_genexp(parent.args[0], is_async=False) is node
                        and arities and len(parent.args) in arities
                        and id(parent) not in shadowed_eager_calls
                        and _eager_genexp_keywords_consumed(
                            name, parent.keywords))
                elif isinstance(parent, (ast.Starred, ast.YieldFrom)):
                    found = (parent.value is node
                             and not _is_async_generator_exp(node))
                elif isinstance(parent, (ast.For, ast.AsyncFor)):
                    found = (parent.iter is node
                             and _is_async_generator_exp(node)
                             == isinstance(parent, ast.AsyncFor))
                elif isinstance(parent, ast.comprehension):
                    owner = parents.get(id(parent))
                    protocol_matches = (
                        bool(parent.is_async) == _is_async_generator_exp(node))
                    found = (parent.iter is node and protocol_matches
                             and (isinstance(
                                  owner, (ast.ListComp, ast.SetComp,
                                          ast.DictComp))
                                  or (isinstance(owner, ast.GeneratorExp)
                                      and id(owner) in immediate)))
            else:
                continue
            if found:
                immediate.add(id(node))
                changed = True
        if not changed:
            return frozenset(immediate)
def _shadowed_eager_call_ids(
        tree: ast.Module, scope_index: _UndefinedScopeIndex) -> frozenset[int]:
    shadowed: set[int] = set()
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id in _EAGER_GENEXP_CALL_ARITIES):
            continue
        if node.func.id in scope_index.visible_names(node.func):
            shadowed.add(id(node))
    return frozenset(shadowed)
_MAX_UNDEFINED_FINDINGS = 20
_MAX_DETAIL_LINES = 50
_UNDEFINED_SEVERITY = "P1"
_UNDEFINED_CONFIDENCE = 0.6
class _BindScan:
    __slots__ = ("annotation_ids", "called_names", "defined",
                 "name_nodes", "read_target_ids")
    def __init__(self, name_nodes: list[ast.Name] | None,
                 annotation_ids: set[int] | None,
                 called_names: set[str] | None,
                 read_target_ids: set[int] | None) -> None:
        self.defined: set[str] = {"__name__", "__file__", "__doc__"}
        self.name_nodes = name_nodes
        self.annotation_ids = annotation_ids
        self.called_names = called_names
        self.read_target_ids = read_target_ids
_STATE_IN_FUNCTION = 1
_STATE_EXEMPT = 2
_STATE_CLASS_BODY = 4
_UNCALLED_FUNC_KINDS = (ast.FunctionDef, ast.AsyncFunctionDef)
def _called_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
        return node.func.id
    return None
def _has_star_import(nodes: Iterable[ast.AST]) -> bool:
    return any(isinstance(n, ast.ImportFrom)
               and any(a.name == "*" for a in n.names)
               for n in nodes)
def _is_skippable_undefined_ref(node: ast.Name, defined_names: set[str],
                                annotation_name_ids: set[int],
                                exempt_ids: set[int]) -> bool:
    name = node.id
    return (name in defined_names
            or id(node) in annotation_name_ids
            or id(node) in exempt_ids)
def _specialized_all_reference_ids(
        tree: ast.Module, shadowed_eager_calls: frozenset[int]) -> set[int]:
    exempt: set[int] = set()
    for node in walk_nodes(tree):
        specialized = (
            (isinstance(node, ast.stmt)
             and (_is_all_increment_stmt(node, shadowed_eager_calls)
                  or is_all_delete(node)))
            or (isinstance(node, ast.Call) and _is_all_mutator_call(node))
            or (isinstance(node, ast.NamedExpr)
                and is_all_name_target(node.target)
                and _reads_all_before_binding(
                    node.value, shadowed_eager_calls)))
        if not specialized:
            continue
        exempt.update(id(sub) for sub in walk_nodes(node)
                      if isinstance(sub, ast.Name) and sub.id == "__all__")
    return exempt
def check_undefined_names(tree: ast.Module, rel_path: str,
                           nodes: list[ast.AST] | None = None) -> list[FileDefect]:
    if nodes is None:
        nodes = list(walk_nodes(tree))
    scope_index = _UndefinedScopeIndex(tree)
    shadowed_eager_calls = _shadowed_eager_call_ids(tree, scope_index)
    immediate_execution_ids = _immediate_execution_scope_ids(
        tree, shadowed_eager_calls)
    if immediate_execution_ids:
        scope_index = _UndefinedScopeIndex(tree, immediate_execution_ids)
        shadowed_eager_calls = _shadowed_eager_call_ids(tree, scope_index)
    unreachable_ids = _unreachable_node_ids(tree, scope_index.ast_parents)
    nodes = [node for node in nodes if id(node) not in unreachable_ids]
    if _has_star_import(nodes):
        return [_nonlocal_binding_defect(rel_path, lineno, name)
                for lineno, name in scope_index.nonlocal_missing]
    name_nodes: list[ast.Name] = []
    annotation_name_ids = _function_local_annotation_name_ids(tree)
    is_test = is_test_file_path(rel_path)
    called_names: set[str] | None = set() if is_test else None
    read_target_ids: set[int] = set()
    scan = _BindScan(
        name_nodes,
        annotation_name_ids if module_postpones_annotations(tree) else None,
        called_names, read_target_ids)
    _scan_bindings(nodes, scan)
    exempt_ids = _specialized_all_reference_ids(tree, shadowed_eager_calls)
    if is_test:
        exempt_ids.update(_collect_uncalled_nested_bodies(tree, called_names))
    hits: dict[str, tuple[FileDefect, list[int]]] = {}
    for node in name_nodes:
        if _is_skippable_undefined_ref(
                node, scope_index.visible_names(node),
                annotation_name_ids, exempt_ids):
            continue
        defect = _undefined_name_defect(
            node, rel_path, read_reference=id(node) in read_target_ids)
        if defect is not None:
            hits.setdefault(node.id, (defect, []))[1].append(node.lineno)
    defects = _aggregate_undefined_findings(hits)
    defects.extend(_nonlocal_binding_defect(rel_path, lineno, name)
                   for lineno, name in scope_index.nonlocal_missing)
    return defects
def _nonlocal_binding_defect(rel_path: str, lineno: int,
                             name: str) -> FileDefect:
    return FileDefect(
        defect_type=DefectType.UNDEFINED_NAME,
        severity=_UNDEFINED_SEVERITY,
        filepath=rel_path,
        lineno=lineno,
        message=f"nonlocal 声明找不到外层函数绑定: '{name}'（编译期 SyntaxError）",
        suggestion=(f"在外层函数中为 '{name}' 赋值，"
                    "或改用 global 声明 / 局部变量"),
        confidence=0.9,
        detail={"name": name, "kind": "nonlocal"},
    )
def _aggregate_undefined_findings(
        hits: dict[str, tuple[FileDefect, list[int]]]) -> list[FileDefect]:
    defects = []
    for defect, name_lines in hits.values():
        lines = sorted(set(name_lines))
        if len(lines) > 1:
            defect.detail["lines"] = lines[:_MAX_DETAIL_LINES]
            defect.detail["ref_count"] = len(lines)
        defects.append(defect)
    return defects[:_MAX_UNDEFINED_FINDINGS]
def _collect_ann_names(expr: ast.expr | None,
                       annotation_name_ids: set[int]) -> None:
    if expr is None:
        return
    for sub in walk_nodes(expr):
        if isinstance(sub, ast.Name):
            annotation_name_ids.add(id(sub))
def _function_local_annotation_name_ids(tree: ast.Module) -> set[int]:
    parents = build_parent_map(tree)
    name_ids: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.AnnAssign):
            continue
        owner = parents.get(id(node))
        while owner is not None:
            if isinstance(owner, ast.ClassDef):
                break
            if isinstance(owner, (ast.FunctionDef, ast.AsyncFunctionDef)):
                _collect_ann_names(node.annotation, name_ids)
                break
            owner = parents.get(id(owner))
    return name_ids
def _bind_func_def(node: ast.AST, scan: _BindScan) -> None:
    scan.defined.add(node.name)
    _add_arg_names(node.args, scan.defined)
    if scan.annotation_ids is None:
        return
    _collect_ann_names(node.returns, scan.annotation_ids)
    for arg_node in iter_arg_nodes(node.args):
        _collect_ann_names(arg_node.annotation, scan.annotation_ids)
def _bind_ann_assign(node: ast.AST, scan: _BindScan) -> None:
    if isinstance(node.target, ast.Name) and node.value is not None:
        scan.defined.add(node.target.id)
    if scan.annotation_ids is not None:
        _collect_ann_names(node.annotation, scan.annotation_ids)
def _bind_with(node: ast.AST, scan: _BindScan) -> None:
    for item in node.items:
        if item.optional_vars is not None:
            scan.defined.update(iter_unpack_target_names(item.optional_vars))
def _bind_import(node: ast.AST, scan: _BindScan) -> None:
    for alias in node.names:
        scan.defined.add(alias.asname or alias.name.split(".", 1)[0])
def _bind_assign(node: ast.AST, scan: _BindScan) -> None:
    for target in node.targets:
        scan.defined.update(iter_unpack_target_names(target))
def _bind_loop_target(node: ast.AST, scan: _BindScan) -> None:
    scan.defined.update(iter_unpack_target_names(node.target))
def _bind_comprehension(node: ast.AST, scan: _BindScan) -> None:
    for generator in node.generators:
        scan.defined.update(iter_unpack_target_names(generator.target))
def _bind_named_definition(node: ast.AST, scan: _BindScan) -> None:
    scan.defined.add(node.name)
def _bind_named_expr(node: ast.AST, scan: _BindScan) -> None:
    if isinstance(node.target, ast.Name):
        scan.defined.add(node.target.id)
def _bind_except(node: ast.AST, scan: _BindScan) -> None:
    if node.name:
        scan.defined.add(node.name)
_NORMAL_COMPLETION = "normal"
_CONTROL_COMPLETION = "control"
_RAISE_COMPLETION = "raise"
def _block_completion_modes(stmts) -> set[str]:
    modes = {_NORMAL_COMPLETION}
    for stmt in stmts:
        successors = (_statement_completion_modes(stmt)
                      if _NORMAL_COMPLETION in modes else set())
        modes = (modes - {_NORMAL_COMPLETION}) | successors
    return modes
def _statement_completion_modes(stmt: ast.AST) -> set[str]:
    if isinstance(stmt, (ast.Return, ast.Break, ast.Continue)):
        return {_CONTROL_COMPLETION}
    if isinstance(stmt, ast.Raise):
        return {_RAISE_COMPLETION}
    if isinstance(stmt, ast.If):
        return (_block_completion_modes(stmt.body)
                | _block_completion_modes(stmt.orelse))
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        modes = set()
        for mode in _block_completion_modes(stmt.body):
            if mode == _RAISE_COMPLETION:
                # __exit__ may suppress the exception and resume after the with.
                modes.update((_NORMAL_COMPLETION, _RAISE_COMPLETION))
            else:
                modes.add(mode)
        return modes
    try_star = getattr(ast, "TryStar", None)
    if isinstance(stmt, ast.Try) or (try_star is not None
                                     and isinstance(stmt, try_star)):
        body_modes = _block_completion_modes(stmt.body)
        modes = body_modes - {_NORMAL_COMPLETION, _RAISE_COMPLETION}
        if _NORMAL_COMPLETION in body_modes:
            modes |= _block_completion_modes(stmt.orelse)
        if stmt.handlers:
            for handler in stmt.handlers:
                modes |= _block_completion_modes(handler.body)
        elif _RAISE_COMPLETION in body_modes:
            modes.add(_RAISE_COMPLETION)
        if stmt.finalbody:
            final_modes = _block_completion_modes(stmt.finalbody)
            if _NORMAL_COMPLETION not in final_modes:
                modes = set()
            modes |= final_modes - {_NORMAL_COMPLETION}
        return modes
    return {_NORMAL_COMPLETION}
def _block_terminates(stmts) -> bool:
    """语句序列是否不可能正常落到后续语句（保守分析显式控制流）。"""
    return bool(stmts) and _NORMAL_COMPLETION not in _block_completion_modes(stmts)
def _bind_delete(node: ast.AST, scan: _BindScan) -> None:
    if scan.read_target_ids is None:
        return
    for target in node.targets:
        scan.read_target_ids.update(
            id(sub) for sub in walk_nodes(target) if isinstance(sub, ast.Name))
def _bind_global_declaration(node: ast.AST, scan: _BindScan) -> None:
    scan.defined.update(node.names)
def _bind_type_alias(node: ast.AST, scan: _BindScan) -> None:
    scan.defined.add(node.name.id)
def _bind_lambda(node: ast.AST, scan: _BindScan) -> None:
    _add_arg_names(node.args, scan.defined)
def _bind_call(node: ast.AST, scan: _BindScan) -> None:
    name = _called_name(node)
    if name is not None and scan.called_names is not None:
        scan.called_names.add(name)
def _bind_augassign(node: ast.AST, scan: _BindScan) -> None:
    scan.defined.update(iter_unpack_target_names(node.target))
    if scan.read_target_ids is not None:
        scan.read_target_ids.update(
            id(sub) for sub in walk_nodes(node.target)
            if isinstance(sub, ast.Name))
def _bind_match(node: ast.AST, scan: _BindScan) -> None:
    _nm = node.rest if type(node) is ast.MatchMapping else node.name
    if _nm:
        scan.defined.add(_nm)
_BIND_HANDLERS: dict[type, Callable[[ast.AST, _BindScan], None]] = {
    ast.FunctionDef: _bind_func_def, ast.AsyncFunctionDef: _bind_func_def,
    ast.ClassDef: _bind_named_definition,
    ast.Assign: _bind_assign, ast.AnnAssign: _bind_ann_assign,
    ast.For: _bind_loop_target, ast.AsyncFor: _bind_loop_target,
    ast.With: _bind_with, ast.AsyncWith: _bind_with,
    ast.Import: _bind_import, ast.ImportFrom: _bind_import,
    ast.NamedExpr: _bind_named_expr, ast.ExceptHandler: _bind_except,
    ast.Lambda: _bind_lambda,
    ast.ListComp: _bind_comprehension, ast.SetComp: _bind_comprehension,
    ast.DictComp: _bind_comprehension, ast.GeneratorExp: _bind_comprehension,
    ast.Call: _bind_call, ast.AugAssign: _bind_augassign,
    ast.MatchAs: _bind_match, ast.MatchStar: _bind_match,
    ast.MatchMapping: _bind_match,
    ast.Global: _bind_global_declaration,
    ast.Delete: _bind_delete,
}
if hasattr(ast, "TypeAlias"):
    _BIND_HANDLERS[ast.TypeAlias] = _bind_type_alias
for _tp_name in ("TypeVar", "ParamSpec", "TypeVarTuple"):
    _tp_node = getattr(ast, _tp_name, None)
    if _tp_node is not None:
        _BIND_HANDLERS[_tp_node] = _bind_named_definition
def _scan_bindings(nodes: list[ast.AST], scan: _BindScan) -> None:
    for node in nodes:
        if type(node) is ast.Name:
            if scan.name_nodes is not None:
                scan.name_nodes.append(node)
            continue
        handler = _BIND_HANDLERS.get(type(node))
        if handler is not None:
            handler(node, scan)
def _add_arg_names(args: ast.arguments, defined_names: set[str]) -> None:
    for arg_node in iter_arg_nodes(args):
        defined_names.add(arg_node.arg)
def _undefined_name_defect(node: ast.Name, rel_path: str,
                           read_reference: bool) -> FileDefect | None:
    if not (isinstance(node.ctx, ast.Load) or read_reference):
        return None
    name = node.id
    if name in _BUILTIN_NAMES:
        return None
    return FileDefect(
        defect_type=DefectType.UNDEFINED_NAME,
        severity=_UNDEFINED_SEVERITY,
        filepath=rel_path,
        lineno=node.lineno,
        message=f"引用未定义的名称 '{name}'",
        suggestion=f"检查 '{name}' 是否已导入或定义，或添加对应的 import",
        confidence=_UNDEFINED_CONFIDENCE,
        detail={"name": name},
    )
def _collect_uncalled_nested_bodies(tree: ast.Module,
                                    called_names: set[str]) -> set[int]:
    exempt_ids: set[int] = set()
    stack: list[tuple[ast.AST, int]] = [(tree, 0)]
    while stack:
        container, state = stack.pop()
        for child in ast.iter_child_nodes(container):
            if state & _STATE_EXEMPT and isinstance(child, ast.Name):
                exempt_ids.add(id(child))
            _push_walk_child(stack, child, state, called_names)
    return exempt_ids
def _push_walk_child(stack: list, child: ast.AST, state: int,
                     called_names: set[str]) -> None:
    if isinstance(child, _UNCALLED_FUNC_KINDS):
        _push_uncalled_func_frame(stack, child, state, called_names)
        return
    if isinstance(child, ast.ClassDef):
        stack.append((child, _STATE_CLASS_BODY | (state & _STATE_EXEMPT)))
        return
    stack.append((child, state))
def _push_uncalled_func_frame(stack: list, child: ast.AST, state: int,
                              called_names: set[str]) -> None:
    inherited = _STATE_IN_FUNCTION | (state & _STATE_EXEMPT)
    if state & _STATE_CLASS_BODY:
        stack.append((child, inherited))
    elif not (state & _STATE_EXEMPT) and (state & _STATE_IN_FUNCTION) \
            and child.name not in called_names:
        stack.append((child, _STATE_IN_FUNCTION | _STATE_EXEMPT))
    else:
        stack.append((child, inherited))
class _TrackedBindings(set):
    """记录「本次写入过哪些名字」的绑定集合。

    ``_capture_bindings`` 过去用「集合差分」判断新增绑定，于是**重绑定同名
    名称**（循环目标、循环后再赋值、with/except 复用同名）不会补记绑定事件，
    读取点只能回退到更早的条件分支事件，再被 ``conditional_loop_write``
    滤掉，产生「引用未定义的名称」误报。写入追踪集合让重绑定也能被看见，
    从而按分支路径补记事件。

    ``clear`` 不属于写入（调用方用于回滚快照），故不记录。
    """

    __slots__ = ("written",)

    def __init__(self, *args) -> None:
        super().__init__(*args)
        self.written: set[str] = set()

    def add(self, name: str) -> None:
        self.written.add(name)
        super().add(name)

    def update(self, *iterables) -> None:
        # 逐个物化：``iterables`` 可能是生成器（如 ``iter_unpack_target_names``），
        # 先记录再交给 ``super().update`` 会把它消耗成空序列。
        for iterable in iterables:
            materialized = tuple(iterable)
            self.written.update(materialized)
            super().update(materialized)

    def discard(self, name: str) -> None:
        self.written.add(name)
        super().discard(name)

    def remove(self, name: str) -> None:
        self.written.add(name)
        super().remove(name)


class _UndefinedScope:
    def __init__(self, kind: str, parent: _UndefinedScope | None = None,
                 *, deferred: bool = False) -> None:
        self.kind = kind
        self.parent = parent
        self.deferred = deferred
        self.localize_walrus = False
        self.bindings: set[str] = _TrackedBindings()
        self.binding_events: dict[str, list[tuple[int, bool]]] = {}
        self.binding_event_paths: dict[str, dict[int, tuple]] = {}
        self.remote_binding_events: dict[str, list[tuple[int, bool]]] = {}
        self.remote_binding_event_paths: dict[str, dict[int, tuple]] = {}
        self.nonlocal_names: set[str] = set()
        self.global_names: set[str] = set()
        self.call_sites: list[tuple[int, str, ast.AST]] = []
        self.scan = _BindScan(None, None, None, None)
        self.scan.defined = self.bindings
def _target_binding_names(targets) -> frozenset[str]:
    return frozenset(iter_unpack_target_names(targets))
class _UndefinedScopeIndex:
    def __init__(self, tree: ast.Module,
                 immediate_execution_ids: frozenset[int] = frozenset()) -> None:
        self.root = _UndefinedScope("module")
        self.immediate_execution_ids = immediate_execution_ids
        self.ast_parents = build_parent_map(tree)
        self._loop_entry_guaranteed = {
            id(node): _literal_truth(
                node.iter if isinstance(node, (ast.For, ast.AsyncFor))
                else node.test) is True
            for node in walk_nodes(tree)
            if isinstance(node, (ast.For, ast.AsyncFor, ast.While))
        }
        self.function_scopes: dict[int, _UndefinedScope] = {}
        self.scope_nodes: dict[int, ast.AST] = {}
        self.name_scopes: dict[int, _UndefinedScope] = {}
        self.name_blocks: dict[int, tuple[tuple[_UndefinedScope,
                                                frozenset[str]], ...]] = {}
        self.name_orders: dict[int, int] = {}
        self.local_only_delete_ids: set[int] = set()
        # 记忆化缓存：``_conditional_branch_chain`` 是「节点 → 纯值」的函数，
        # 但 ``_visible_at`` 会按作用域里每个绑定名重复求同一个节点的分支链
        # （实测单文件 2578 行触发 117 万次重算、33s）。索引与 AST 同生命周期，
        # ``id()`` 在扫描期间稳定，故按 id 缓存不改变可见性语义。
        self._read_path_cache: dict[int, tuple] = {}
        self._unconditional_branch_guards = _terminating_branch_guards(tree)
        self._pending_nonlocals: list[tuple[ast.Nonlocal, _UndefinedScope]] = []
        self._deferred_global_bindings: set[str] = set()
        self._deferred_global_writers: dict[str, set[int]] = {}
        self._unreferenced_function_ids = self._find_unreferenced_functions(tree)
        self._unreferenced_generator_ids = self._find_unreferenced_generators(
            tree, immediate_execution_ids)
        self._order = 0
        self._walk(tree, self.root)
        self.root.bindings.update(self._deferred_global_bindings)
        self.nonlocal_missing = self._collect_missing_nonlocals()
    def _collect_missing_nonlocals(self) -> list[tuple[int, str]]:
        return [
            (node.lineno, name)
            for node, scope in self._pending_nonlocals
            for name in node.names
            if self._enclosing_function_scope(scope, name) is None
        ]
    @staticmethod
    def _find_unreferenced_functions(tree: ast.Module) -> frozenset[int]:
        loaded_names = {
            node.id for node in walk_nodes(tree)
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
        }
        attribute_names = {
            node.attr for node in walk_nodes(tree) if isinstance(node, ast.Attribute)
        }
        string_references = {
            node.value for node in walk_nodes(tree)
            if isinstance(node, ast.Constant) and isinstance(node.value, str)
        }
        return frozenset(
            id(node) for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and not node.decorator_list
            and node.name not in loaded_names
            and node.name not in attribute_names
            and node.name not in string_references
        )
    def _find_unreferenced_generators(
            self, tree: ast.Module,
            immediate_execution_ids: frozenset[int]) -> frozenset[int]:
        loaded_names = {
            node.id for node in walk_nodes(tree)
            if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
        }
        result = set()
        for node in walk_nodes(tree):
            if not isinstance(node, ast.GeneratorExp):
                continue
            if id(node) in immediate_execution_ids:
                continue
            parent = self.ast_parents.get(id(node))
            if isinstance(parent, ast.Expr) and parent.value is node:
                result.add(id(node))
                continue
            if not (isinstance(parent, (ast.Assign, ast.AnnAssign, ast.NamedExpr))
                    and parent.value is node):
                continue
            targets = parent.targets if isinstance(parent, ast.Assign) else (parent.target,)
            target_names = _target_binding_names(targets)
            if target_names and target_names.isdisjoint(loaded_names):
                result.add(id(node))
        return frozenset(result)
    def _node_is_immediate_read(self, node: ast.Name) -> bool:
        scope = self.name_scopes.get(id(node), self.root)
        while scope is not None:
            if scope.deferred:
                return False
            scope = scope.parent
        return True
    def _only_unexecuted_global_binding(self, name: str, order: int) -> bool:
        writers = self._deferred_global_writers.get(name, set())
        if not writers or not writers <= self._unreferenced_function_ids:
            return False
        events = self.root.binding_events.get(name, ())
        index = bisect_right(events, (order, True))
        return not (index and events[index - 1][1])
    @staticmethod
    def _block(scope: _UndefinedScope, names: frozenset[str],
               blocked: tuple) -> tuple:
        pending = frozenset(n for n in names if n not in scope.bindings)
        return (*blocked, (scope, pending)) if pending else blocked
    def _capture_bindings(self, scope: _UndefinedScope, binder,
                          *args, event_node: ast.AST | None = None) -> None:
        if event_node is None:
            event_node = next(
                (arg for arg in args if isinstance(arg, ast.AST)), None)
        event_path = (self._read_path(event_node)
                      if event_node is not None else ())
        bindings = scope.bindings
        before = set(bindings)
        tracked = bindings.written if isinstance(bindings, _TrackedBindings) else None
        if tracked is not None:
            tracked.clear()
        binder(*args)
        written = set(tracked) if tracked is not None else set()
        if tracked is not None:
            tracked.clear()
        bound = bindings - before
        declared = scope.nonlocal_names | scope.global_names
        if declared:
            scope.bindings -= declared
        remote = bound & declared if scope.kind != 'module' else set()
        if remote:
            global_remote = remote & scope.global_names
            if scope.kind == 'function':
                self._deferred_global_bindings.update(global_remote)
                owner = self.scope_nodes.get(id(scope))
                for name in global_remote:
                    self._deferred_global_writers.setdefault(name, set()).add(
                        id(owner))
            else:
                self.root.bindings.update(global_remote)
            if scope.kind == 'class' and global_remote:
                self._order += 1
                for name in global_remote:
                    self.root.binding_events.setdefault(name, []).append(
                        (self._order, True))
                    self.root.binding_event_paths.setdefault(
                        name, {})[self._order] = event_path
            if scope.kind == 'class':
                for name in sorted(remote & scope.nonlocal_names):
                    owner = self._enclosing_function_scope(scope, name)
                    if owner is None:
                        continue
                    owner.bindings.add(name)
                    self._order += 1
                    owner.binding_events.setdefault(name, []).append(
                        (self._order, True))
                    owner.binding_event_paths.setdefault(
                        name, {})[self._order] = event_path
            if scope.kind == 'function':
                self._order += 1
                for name in remote:
                    scope.remote_binding_events.setdefault(name, []).append(
                        (self._order, True))
                    scope.remote_binding_event_paths.setdefault(
                        name, {})[self._order] = event_path
        added = bindings - before
        if written:
            # 重绑定同名名称不改变集合内容，但绑定位置不同：补记事件，
            # 否则读取点会回退到更早的条件分支事件而误判未定义。
            added |= {
                name for name in written
                if name in bindings and name not in added
                and self._last_event_path(scope, name) != event_path}
        if not added:
            return
        self._order += 1
        for name in added:
            scope.binding_events.setdefault(name, []).append(
                (self._order, True))
            scope.binding_event_paths.setdefault(
                name, {})[self._order] = event_path
    @staticmethod
    def _last_event_path(scope: _UndefinedScope,
                         name: str) -> tuple | None:
        """取名称最近一次绑定事件的路径（无事件时返回 None）。"""
        events = scope.binding_events.get(name)
        if not events:
            return None
        return scope.binding_event_paths.get(name, {}).get(events[-1][0])

    def _bind_names(self, scope: _UndefinedScope, names,
                    event_node: ast.AST | None = None) -> None:
        self._capture_bindings(
            scope, scope.bindings.update, names, event_node=event_node)
    def _record_name(self, node: ast.Name, scope: _UndefinedScope,
                     blocked: tuple) -> None:
        self._order += 1
        self.name_orders[id(node)] = self._order
        self.name_scopes[id(node)] = scope
        if blocked:
            self.name_blocks[id(node)] = blocked
    def _walk(self, node: ast.AST, scope: _UndefinedScope,
              blocked: tuple = ()) -> None:
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            scope.call_sites.append((self._order, node.func.id, node))
        if isinstance(node, ast.Name):
            self._record_name(node, scope, blocked)
            return
        handler = _UNDEFINED_WALK_HANDLERS.get(type(node))
        if handler is not None:
            handler(self, node, scope, blocked)
            return
        bind = _BIND_HANDLERS.get(type(node))
        if bind is not None:
            self._capture_bindings(scope, bind, node, scope.scan)
        for child in ast.iter_child_nodes(node):
            self._walk(child, scope, blocked)
    def _walk_augassign(self, node: ast.AugAssign, scope: _UndefinedScope,
                        blocked: tuple) -> None:
        block = self._block(
            scope, _target_binding_names((node.target,)), blocked)
        self._walk(node.target, scope, block)
        self._walk(node.value, scope, block)
        self._capture_bindings(scope, _bind_augassign, node, scope.scan)
    def _walk_assignment_targets(self, targets, scope: _UndefinedScope,
                                 blocked: tuple) -> None:
        names = _target_binding_names(targets)
        for leaf in flatten_unpack_targets(targets):
            block = self._block(scope, names, blocked)
            self._walk(leaf, scope, block)
            self._capture_bindings(
                scope, scope.bindings.update, _target_binding_names((leaf,)),
                event_node=leaf)
    def _walk_assign(self, node: ast.Assign, scope: _UndefinedScope,
                     blocked: tuple) -> None:
        block = self._block(scope, _target_binding_names(node.targets), blocked)
        self._walk(node.value, scope, block)
        self._walk_assignment_targets(node.targets, scope, blocked)
    def _declare_unbound_locals(self, scope: _UndefinedScope,
                                names: frozenset[str],
                                event_node: ast.AST | None = None) -> None:
        if scope.kind != "function":
            return
        event_path = (self._read_path(event_node)
                      if event_node is not None else ())
        for name in names:
            if (name in scope.bindings or name in scope.binding_events
                    or name in scope.global_names
                    or name in scope.nonlocal_names):
                continue
            self._order += 1
            scope.binding_events.setdefault(name, []).append(
                (self._order, False))
            scope.binding_event_paths.setdefault(
                name, {})[self._order] = event_path
    def _walk_ann_assign(self, node: ast.AnnAssign, scope: _UndefinedScope,
                         blocked: tuple) -> None:
        names = (_target_binding_names((node.target,))
                 if node.value is not None else frozenset())
        block = self._block(scope, names, blocked)
        if scope.kind != "function":
            self._walk(node.annotation, scope, block)
        if node.value is not None:
            self._walk(node.value, scope, block)
        self._walk(node.target, scope, block)
        if node.value is not None:
            self._capture_bindings(
                scope, _bind_ann_assign, node, scope.scan)
        else:
            self._declare_unbound_locals(
                scope, _target_binding_names((node.target,)), node)
    def _walk_if(self, node: ast.If, scope: _UndefinedScope,
                 blocked: tuple) -> None:
        self._walk(node.test, scope, blocked)
        truth = _literal_truth(node.test)
        if truth is not None:
            for stmt in (node.body if truth else node.orelse):
                self._walk(stmt, scope, blocked)
            return
        incoming = set(scope.bindings)
        for stmt in node.body:
            self._walk(stmt, scope, blocked)
        body_bindings = set(scope.bindings)
        scope.bindings.clear()
        scope.bindings.update(incoming)
        for stmt in node.orelse:
            self._walk(stmt, scope, blocked)
        else_bindings = set(scope.bindings)
        body_terminates = _block_terminates(node.body)
        else_terminates = _block_terminates(node.orelse)
        if else_terminates and not body_terminates:
            # else 必然退出：if 之后只能从真分支到达，真分支的绑定是无条件的。
            # 只有「死分支独有」的绑定才需要销项事件。
            merged = body_bindings
            dead = else_bindings - body_bindings
        elif body_terminates and not else_terminates:
            # 真分支必然退出：if 之后只能从 else 到达。
            merged = else_bindings
            dead = body_bindings - else_bindings
        else:
            merged = body_bindings & else_bindings
            dead = body_bindings ^ else_bindings
        for name in sorted(dead):
            self._order += 1
            scope.binding_events.setdefault(name, []).append(
                (self._order, False))
            scope.binding_event_paths.setdefault(
                name, {})[self._order] = ()
        scope.bindings.clear()
        scope.bindings.update(merged)
    def _walk_while(self, node: ast.While, scope: _UndefinedScope,
                    blocked: tuple) -> None:
        self._walk(node.test, scope, blocked)
        truth = _literal_truth(node.test)
        incoming = set(scope.bindings)
        if truth is not False:
            for stmt in node.body:
                self._walk(stmt, scope, blocked)
        body_bindings = set(scope.bindings)
        if truth is not True:
            scope.bindings.clear()
            scope.bindings.update(incoming)
            for stmt in node.orelse:
                self._walk(stmt, scope, blocked)
            scope.bindings.update(body_bindings)
    def _walk_for(self, node: ast.AST, scope: _UndefinedScope,
                  blocked: tuple) -> None:
        block = self._block(scope, _target_binding_names((node.target,)),
                            blocked)
        self._walk(node.iter, scope, block)
        incoming = set(scope.bindings)
        if _literal_truth(node.iter) is not False:
            self._walk_assignment_targets(node.target, scope, blocked)
            for stmt in node.body:
                self._walk(stmt, scope, blocked)
        body_bindings = set(scope.bindings)
        scope.bindings.clear()
        scope.bindings.update(incoming)
        for stmt in node.orelse:
            self._walk(stmt, scope, blocked)
        scope.bindings.update(body_bindings)
    def _walk_with(self, node: ast.AST, scope: _UndefinedScope,
                   blocked: tuple) -> None:
        for item in node.items:
            names = (_target_binding_names((item.optional_vars,))
                     if item.optional_vars is not None else frozenset())
            block = self._block(scope, names, blocked)
            self._walk(item.context_expr, scope, block)
            if item.optional_vars is not None:
                self._walk_assignment_targets(
                    item.optional_vars, scope, blocked)
        for stmt in node.body:
            self._walk(stmt, scope, blocked)
    def _walk_named_expr(self, node: ast.NamedExpr, scope: _UndefinedScope,
                         blocked: tuple) -> None:
        target_scope = scope
        if scope.kind == "comprehension":
            while (target_scope.parent is not None
                   and target_scope.kind == "comprehension"
                   and not target_scope.localize_walrus):
                target_scope = target_scope.parent
        names = _target_binding_names((node.target,))
        block = self._block(target_scope, names, blocked)
        self._walk(node.value, scope, block)
        self._capture_bindings(
            target_scope, _bind_named_expr, node, target_scope.scan)
    def _discard_binding(self, scope: _UndefinedScope, name: str,
                         event_node: ast.AST | None = None) -> None:
        if name not in scope.bindings:
            return
        scope.bindings.discard(name)
        self._order += 1
        scope.binding_events.setdefault(name, []).append((self._order, False))
        event_path = (self._read_path(event_node)
                      if event_node is not None else ())
        scope.binding_event_paths.setdefault(
            name, {})[self._order] = event_path
    def _walk_delete(self, node: ast.Delete, scope: _UndefinedScope,
                     blocked: tuple) -> None:
        if scope.kind == "class":
            self.local_only_delete_ids.update(
                id(sub) for target in node.targets for sub in walk_nodes(target)
                if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Del)
                and sub.id not in scope.global_names
                and sub.id not in scope.nonlocal_names)
        for target in node.targets:
            for leaf in flatten_unpack_targets(target):
                self._walk(leaf, scope, blocked)
                for name in _target_binding_names((leaf,)):
                    owner = self._delete_target_scope(scope, name)
                    if owner is None:
                        continue
                    if (owner is scope and scope.kind == "function"
                            and name not in scope.global_names
                            and name not in scope.nonlocal_names):
                        self._bind_names(scope, (name,), leaf)
                    if owner is not scope and scope.deferred:
                        self._order += 1
                        scope.remote_binding_events.setdefault(
                            name, []).append((self._order, False))
                        scope.remote_binding_event_paths.setdefault(
                            name, {})[self._order] = self._read_path(leaf)
                    else:
                        self._discard_binding(owner, name, leaf)
    def _delete_target_scope(self, scope: _UndefinedScope,
                             name: str) -> _UndefinedScope | None:
        if scope.kind in {"function", "class"}:
            if name in scope.global_names:
                return self.root
            if name in scope.nonlocal_names:
                return self._enclosing_function_scope(scope, name)
            return scope
        if name in scope.bindings:
            return scope
        current = scope.parent
        while current is not None and current.kind != "module":
            if current.kind == "class":
                current = current.parent
                continue
            if name in current.bindings:
                return current
            current = current.parent
        return self.root
    @staticmethod
    def _enclosing_function_scope(scope: _UndefinedScope,
                                  name: str) -> _UndefinedScope | None:
        current = scope.parent
        while current is not None and current.kind != "module":
            if (current.kind in {"function", "comprehension"}
                    and (name in current.bindings
                         or name in current.binding_events)):
                return current
            current = current.parent
        return None
    def _walk_except(self, node: ast.ExceptHandler,
                     scope: _UndefinedScope, blocked: tuple) -> None:
        names = frozenset((node.name,)) if node.name else frozenset()
        block = self._block(scope, names, blocked)
        if node.type is not None:
            self._walk(node.type, scope, block)
        if node.name:
            self._bind_names(scope, (node.name,), node)
        for stmt in node.body:
            self._walk(stmt, scope, blocked)
        # ``except ... as name`` 的隐式 ``del name`` 只在处理器能落到后续语句时
        # 生效。处理器整体 return/raise 时后续语句不可达，此时丢弃绑定会把
        # try 体内由元组解包定义的同名变量一并抹掉，产生假的未定义名称。
        if node.name and not _block_terminates(node.body):
            self._discard_binding(scope, node.name, node)
    def _type_param_scope(self, node: ast.AST, scope: _UndefinedScope,
                          blocked: tuple) -> _UndefinedScope:
        type_params = getattr(node, "type_params", ())
        if not type_params:
            return scope
        type_scope = _UndefinedScope("type_params", scope, deferred=True)
        self._bind_names(type_scope, [
            type_param.name for type_param in type_params
            if isinstance(getattr(type_param, "name", None), str)])
        for type_param in type_params:
            self._walk(type_param, type_scope, blocked)
        return type_scope
    def _walk_global(self, node: ast.Global, scope: _UndefinedScope,
                     _blocked: tuple) -> None:
        if scope is not self.root:
            scope.global_names.update(node.names)
            scope.bindings -= set(node.names)
        for name in node.names:
            scope.nonlocal_names.discard(name)
    def _walk_nonlocal(self, node: ast.Nonlocal, scope: _UndefinedScope,
                       _blocked: tuple) -> None:
        for name in node.names:
            scope.nonlocal_names.add(name)
            self._discard_binding(scope, name, node)
        self._pending_nonlocals.append((node, scope))
    def _walk_type_alias(self, node: ast.AST, scope: _UndefinedScope,
                         blocked: tuple) -> None:
        type_scope = self._type_param_scope(node, scope, blocked)
        if type_scope is scope:
            type_scope = _UndefinedScope("type_params", scope, deferred=True)
        value = getattr(node, "value", None)
        if value is not None:
            self._walk(value, type_scope, blocked)
        self._capture_bindings(scope, _bind_type_alias, node, scope.scan)
    def _walk_function(self, node: ast.AST, scope: _UndefinedScope,
                       blocked: tuple) -> None:
        block = self._block(scope, frozenset((node.name,)), blocked)
        for expr in node.decorator_list:
            self._walk(expr, scope, block)
        type_scope = self._type_param_scope(node, scope, blocked)
        for expr in _signature_exprs(node):
            self._walk(expr, type_scope, block)
        self._capture_bindings(
            scope, _bind_named_definition, node, scope.scan)
        local = _UndefinedScope("function", type_scope, deferred=True)
        self.function_scopes[id(node)] = local
        self.scope_nodes[id(local)] = node
        self._capture_bindings(local, _add_arg_names, node.args, local.bindings)
        if scope.kind == "class":
            self._bind_names(local, ("__class__",))
        for stmt in node.body:
            self._walk(stmt, local)
    def _walk_class(self, node: ast.ClassDef, scope: _UndefinedScope,
                    blocked: tuple) -> None:
        block = self._block(scope, frozenset((node.name,)), blocked)
        for expr in node.decorator_list:
            self._walk(expr, scope, block)
        type_scope = self._type_param_scope(node, scope, blocked)
        for expr in (*node.bases, *node.keywords):
            self._walk(expr, type_scope, block)
        self._capture_bindings(
            scope, _bind_named_definition, node, scope.scan)
        local = _UndefinedScope("class", type_scope)
        self._bind_names(local, ("__module__", "__qualname__"))
        for stmt in node.body:
            self._walk(stmt, local, block)
    def _walk_lambda(self, node: ast.Lambda, scope: _UndefinedScope,
                     blocked: tuple) -> None:
        for expr in (*node.args.defaults,
                     *(d for d in node.args.kw_defaults if d is not None)):
            self._walk(expr, scope, blocked)
        local = _UndefinedScope(
            "function", scope, deferred=id(node) not in self.immediate_execution_ids)
        self.function_scopes[id(node)] = local
        self.scope_nodes[id(local)] = node
        self._capture_bindings(local, _add_arg_names, node.args, local.bindings)
        if scope.kind == "class":
            self._bind_names(local, ("__class__",))
        self._walk(node.body, local)
    def _walk_comprehension(self, node: ast.AST, scope: _UndefinedScope,
                            blocked: tuple) -> None:
        deferred = (isinstance(node, ast.GeneratorExp)
                    and id(node) not in self.immediate_execution_ids)
        local = _UndefinedScope("comprehension", scope, deferred=deferred)
        local.localize_walrus = id(node) in self._unreferenced_generator_ids
        eager = not deferred
        incoming = blocked if eager else ()
        for index, generator in enumerate(node.generators):
            names = _target_binding_names((generator.target,))
            block = self._block(local, names, ())
            if index == 0:
                self._walk(generator.iter, scope, blocked)
            else:
                self._walk(generator.iter, local, (*incoming, *block))
            self._walk(generator.target, local, (*incoming, *block))
            self._capture_bindings(
                local, local.bindings.update,
                iter_unpack_target_names(generator.target))
            for condition in generator.ifs:
                self._walk(condition, local, incoming)
        for field in ("elt", "key", "value"):
            expr = getattr(node, field, None)
            if expr is not None:
                self._walk(expr, local, incoming)
    def _closure_descendant_scope(self, node: ast.Name,
                                  ancestor: _UndefinedScope
                                  ) -> _UndefinedScope | None:
        scope = self.name_scopes.get(id(node))
        descendant = None
        while scope is not None and scope is not ancestor:
            if scope.kind == "function":
                descendant = scope
            scope = scope.parent
        return descendant if scope is ancestor else None
    def _early_closure_read_at(self, node: ast.Name,
                               ancestor: _UndefinedScope, name: str) -> bool:
        descendant = self._closure_descendant_scope(node, ancestor)
        if descendant is None:
            return False
        owner = self.scope_nodes.get(id(descendant))
        call_name = getattr(owner, "name", None)
        if not isinstance(call_name, str):
            return False
        for order, callee, call in ancestor.call_sites:
            if callee != call_name:
                continue
            if call_name not in self._visible_at(ancestor, order, call):
                continue
            if (name not in self._visible_at(ancestor, order, call)
                    and not _has_unreachable_execution_path(
                        call, self.ast_parents)):
                return True
        return False
    def is_early_closure_read(self, node: ast.Name,
                              function_node: ast.AST, name: str) -> bool:
        scope = self.function_scopes.get(id(function_node))
        return (scope is not None
                and self._early_closure_read_at(node, scope, name))
    def _read_path(self, node: ast.AST | None) -> tuple:
        """取节点的条件分支链（按节点 id 记忆化）。

        同一节点会被 ``_visible_at`` 针对每个绑定名反复查询，而分支链只依赖
        节点自身与其父链，属纯计算结果，缓存后不改变可见性语义。
        """
        if node is None:
            return ()
        key = id(node)
        cached = self._read_path_cache.get(key)
        if cached is None:
            chain = _conditional_branch_chain(node, self.ast_parents)
            exempt = self._unconditional_branch_guards
            if exempt:
                chain = tuple(
                    guard for guard in chain
                    if not (len(guard) >= 2
                            and exempt.get(guard[0]) == guard[1]))
            self._read_path_cache[key] = chain
            cached = chain
        return cached

    def _events_at(self, scope: _UndefinedScope, name: str,
                   order: int, node: ast.AST | None,
                   *, remote: bool = False) -> list[tuple[int, bool]]:
        events = (scope.remote_binding_events if remote
                  else scope.binding_events).get(name, ())
        if node is None:
            return list(events)
        paths = (scope.remote_binding_event_paths if remote
                 else scope.binding_event_paths).get(name, {})
        read_path = self._read_path(node)
        visible_events = []
        for event in events:
            event_path = paths.get(event[0], ())
            if _AllScanState._branches_disjoint(event_path, read_path):
                continue
            conditional_loop_write = any(
                guard[1] == 'body'
                and not self._loop_entry_guaranteed.get(guard[0], True)
                and guard not in read_path
                for guard in event_path)
            if not conditional_loop_write:
                visible_events.append(event)
        return visible_events
    def _visible_at(self, scope: _UndefinedScope, order: int,
                    node: ast.AST | None = None) -> set[str]:
        visible = scope.bindings - scope.binding_events.keys()
        for name in scope.binding_events:
            events = self._events_at(scope, name, order, node)
            index = bisect_right(events, (order, True))
            if index and events[index - 1][1]:
                visible.add(name)
        return visible
    def visible_names(self, node: ast.Name) -> set[str]:
        blocks = self.name_blocks.get(id(node), ())
        blocked_by_scope: dict[int, set[str]] = {}
        for blocked_scope, blocked_names in blocks:
            blocked_by_scope.setdefault(id(blocked_scope), set()).update(
                blocked_names)
        names: set[str] = set()
        resolved: set[str] = set()
        order = self.name_orders.get(id(node), self._order)
        scope = self.name_scopes.get(id(node), self.root)
        local_only_delete = id(node) in self.local_only_delete_ids
        remote_deleted: set[str] = set()
        temporal = True
        immediate_read = self._node_is_immediate_read(node)
        while scope is not None:
            pending = blocked_by_scope.get(id(scope), frozenset())
            if temporal:
                visible = self._visible_at(scope, order, node)
                known = set(scope.binding_events) | scope.bindings
            else:
                visible = set(scope.bindings)
                visible.update(self._visible_at(scope, order, node))
                known = set(scope.binding_events) | scope.bindings
            if scope.kind == 'function':
                for name in scope.global_names:
                    events = self._events_at(
                        scope, name, order, node, remote=True)
                    if not events:
                        continue
                    index = bisect_right(events, (order, True))
                    if index and events[index - 1][1]:
                        continue
                    if any(enabled for _order, enabled
                           in self.root.binding_events.get(name, ())):
                        continue
                    remote_deleted.add(name)
            candidates = (visible - resolved) - pending - remote_deleted
            if scope is self.root and candidates and immediate_read:
                candidates = {
                    name for name in candidates
                    if not self._only_unexecuted_global_binding(name, order)
                }
            if not temporal and scope.kind == 'function' and candidates:
                candidates = {
                    name for name in candidates
                    if not self._early_closure_read_at(node, scope, name)}
            names.update(candidates)
            if scope.kind == 'function':
                for name in scope.remote_binding_events:
                    events = self._events_at(
                        scope, name, order, node, remote=True)
                    index = bisect_right(events, (order, True))
                    if not index:
                        continue
                    if events[index - 1][1]:
                        remote_deleted.discard(name)
                    else:
                        remote_deleted.add(name)
            if local_only_delete:
                break
            if scope.kind in {"function", "comprehension", "type_params"}:
                resolved.update(known - resolved)
            parent = scope.parent
            if parent is not None and parent.kind == "class":
                parent = parent.parent
            if scope.deferred:
                temporal = False
            scope = parent
        return names
_UNDEFINED_WALK_HANDLERS: dict[type, Callable] = {
    ast.Global: _UndefinedScopeIndex._walk_global,
    ast.Nonlocal: _UndefinedScopeIndex._walk_nonlocal,
    ast.FunctionDef: _UndefinedScopeIndex._walk_function,
    ast.AsyncFunctionDef: _UndefinedScopeIndex._walk_function,
    ast.ClassDef: _UndefinedScopeIndex._walk_class,
    ast.Lambda: _UndefinedScopeIndex._walk_lambda,
    ast.If: _UndefinedScopeIndex._walk_if,
    ast.While: _UndefinedScopeIndex._walk_while,
    ast.ListComp: _UndefinedScopeIndex._walk_comprehension,
    ast.SetComp: _UndefinedScopeIndex._walk_comprehension,
    ast.DictComp: _UndefinedScopeIndex._walk_comprehension,
    ast.GeneratorExp: _UndefinedScopeIndex._walk_comprehension,
    ast.Assign: _UndefinedScopeIndex._walk_assign,
    ast.AnnAssign: _UndefinedScopeIndex._walk_ann_assign,
    ast.For: _UndefinedScopeIndex._walk_for,
    ast.AsyncFor: _UndefinedScopeIndex._walk_for,
    ast.With: _UndefinedScopeIndex._walk_with,
    ast.AsyncWith: _UndefinedScopeIndex._walk_with,
    ast.NamedExpr: _UndefinedScopeIndex._walk_named_expr,
    ast.Delete: _UndefinedScopeIndex._walk_delete,
    ast.AugAssign: _UndefinedScopeIndex._walk_augassign,
    ast.ExceptHandler: _UndefinedScopeIndex._walk_except,
}
if hasattr(ast, "TypeAlias"):
    _UNDEFINED_WALK_HANDLERS[ast.TypeAlias] = (
        _UndefinedScopeIndex._walk_type_alias)

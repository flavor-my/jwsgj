from __future__ import annotations

import ast
import json
import logging
from collections.abc import Callable, Container
from functools import partial
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    TRY_NODE_TYPES,
    block_may_fall_through,
    build_parent_map,
    collect_param_names,
    comp_element_roots,
    comp_target_names,
    dotted_name,
    expr_target_name,
    in_subtree,
    iter_pattern_capture_names,
    iter_scope_nodes,
    iter_unpack_target_names,
    kw_arg,
    loop_body_has_break,
    scope_chain,
    scope_roots,
    subscript_base_name,
)
from jwsgj.diag_shared_ast_views import (
    call_scope_map,
    collect_lexical_scope_table,
    definition_time_expressions,
    scope_import_tables,
    scope_shadows_import,
)
from jwsgj.diag_shared_source_core import (
    FRAME_BOUNDARY_NODES,
    build_ast_issue,
    iter_frame_nodes,
    join_source_lines,
)
from jwsgj.diag_shared_source_scan import (
    is_suppressed,
    parse_suppressions,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    finding_scan_exempt,
)
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    "check_FS01",
    "check_JS01",
    "check_JS03",
    "check_TP07",
]
_log = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
_log.info("diag_traps_guard 空值守卫覆盖语义域已加载: %d 项导出", len(__all__))
class _ModuleCallResolver:
    __slots__ = ("_imports", "_scopes", "_shadow")
    def __init__(self, tree: ast.AST) -> None:
        self._imports = scope_import_tables(tree)
        self._shadow = collect_lexical_scope_table(tree)
        self._scopes = call_scope_map(self._shadow)
    def _visible_import(self, node: ast.Call, name: str):
        scope = self._scopes.get(id(node))
        direct = scope
        while scope is not None:
            if not (isinstance(scope, ast.ClassDef) and scope is not direct):
                binding = self._imports.get(scope, {}).get(name)
                if binding is not None:
                    return binding
            scope = self._shadow.parent.get(scope)
        return None
    def canonical_name(self, node: ast.AST, module: str) -> str:
        if not isinstance(node, ast.Call):
            return ""
        if isinstance(node.func, ast.Name):
            return self._canonical_bare_name(node, module)
        qualified = dotted_name(node.func)
        if not qualified:
            return ""
        return self._canonical_qualified_name(node, qualified, module)
    def _canonical_bare_name(self, node: ast.Call, module: str) -> str:
        name = node.func.id
        scope = self._scopes.get(id(node))
        if (scope is not None and scope_shadows_import(
                self._shadow, scope, name)):
            return ""
        binding = self._visible_import(node, name)
        if (binding is not None and binding[0] == "from"
                and binding[1] == module):
            return f"{module}.{binding[2]}"
        return ""
    def _canonical_qualified_name(self, node: ast.Call, qualified: str,
                                  module: str) -> str:
        head, *members = qualified.split(".")
        scope = self._scopes.get(id(node))
        if (scope is not None and scope_shadows_import(
                self._shadow, scope, head)):
            return ""
        binding = self._visible_import(node, head)
        if binding is None:
            base = module if head == module else ""
        elif binding[0] == "import" and binding[1] == module:
            base = module
        elif binding[0] == "from" and binding[1] == module:
            base = f"{module}.{binding[2]}"
        else:
            base = ""
        return ".".join([base, *members]) if base else ""
    def builtin_name(self, node: ast.Call, name: str) -> bool:
        scope = self._scopes.get(id(node))
        if (scope is None or scope_shadows_import(
                self._shadow, scope, name)):
            return False
        binding = self._visible_import(node, name)
        if binding is None:
            return True
        return (binding[0] == "from" and binding[1] == "builtins"
                and binding[2] == name)
class _JS01FlowContext:
    __slots__ = ("call_ids", "resolver")
    def __init__(self, call_ids: frozenset[int],
                 resolver: _ModuleCallResolver) -> None:
        self.call_ids = call_ids
        self.resolver = resolver
    def __contains__(self, node_id: int) -> bool:
        return node_id in self.call_ids
_JS01Calls = frozenset[int] | _JS01FlowContext
_GUARD_BODY = "body"
_GUARD_ORELSE = "orelse"
def _sem_statement_block(stmt: ast.stmt, parents: dict) -> list[ast.stmt] | None:
    parent = parents.get(id(stmt))
    if parent is None:
        return None
    for field in ("body", "orelse", "finalbody"):
        block = getattr(parent, field, None)
        if isinstance(block, list) and stmt in block:
            return block
    return None
def _match_case_is_default(case: ast.match_case) -> bool:
    return (case.guard is None and isinstance(case.pattern, ast.MatchAs)
            and case.pattern.pattern is None)
def _sem_block_terminates(stmts: list[ast.stmt]) -> bool:
    return not block_may_fall_through(stmts)
def _sem_reachable_prefix(stmts: list[ast.stmt]) -> list[ast.stmt]:
    reachable = []
    for stmt in stmts:
        reachable.append(stmt)
        if _sem_block_terminates([stmt]):
            break
    return reachable
def _sem_loop_body_has_back_edge(stmts: list[ast.stmt]) -> bool:
    stmts = _sem_reachable_prefix(stmts)
    if not stmts:
        return True
    last = stmts[-1]
    if isinstance(last, (ast.Return, ast.Raise, ast.Break)):
        return False
    if isinstance(last, ast.If):
        return (_sem_loop_body_has_back_edge(last.body)
                or _sem_loop_body_has_back_edge(last.orelse))
    return True
def _sem_after_in_block(guard: ast.AST, node: ast.AST, parents: dict) -> bool:
    if not isinstance(guard, ast.stmt):
        return False
    block = _sem_statement_block(guard, parents)
    if block is None:
        return False
    return any(in_subtree(node, stmt)
               for stmt in block[block.index(guard) + 1:])
def _in_definition_time_face(scope: ast.AST, node: ast.AST) -> bool:
    return any(
        in_subtree(node, expr)
        for expr in definition_time_expressions(
            scope, annotations_evaluated=False))
def _branch_repairs_param(stmts: list[ast.AST], param_name: str,
                          value_ok: Callable[[ast.AST], bool]) -> bool:
    repaired = False
    for stmt in stmts:
        if isinstance(stmt, ast.Assign):
            targets = [t.id for t in stmt.targets if isinstance(t, ast.Name)]
            value = stmt.value
        elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
            targets = ([stmt.target.id]
                       if isinstance(stmt.target, ast.Name) else [])
            value = stmt.value
        else:
            continue
        if param_name in targets:
            repaired = value_ok(value)
    return repaired
def _sem_branch_nodes(guard: ast.AST, field: str) -> list[ast.AST]:
    value = getattr(guard, field, None)
    if isinstance(value, ast.AST):
        return [value]
    if isinstance(value, list):
        return [item for item in value if isinstance(item, ast.AST)]
    return []
def _fold_guard_branches(test: ast.AST, name: str,
                         atom: Callable[[ast.AST, str], str | None]) -> str | None:
    if not isinstance(test, ast.BoolOp):
        return atom(test, name)
    branches = {_fold_guard_branches(value, name, atom) for value in test.values}
    if isinstance(test.op, ast.And) and _GUARD_BODY in branches:
        return _GUARD_BODY
    if isinstance(test.op, ast.Or) and _GUARD_ORELSE in branches:
        return _GUARD_ORELSE
    return None
def _sem_path_product(path_groups: list) -> list:
    paths = [[]]
    for group in path_groups:
        paths = [prefix + list(path)
                 for prefix in paths for path in group]
    return paths
def _sem_fixed_outcome_paths(items: list) -> list:
    return _sem_path_product([
        _sem_outcome_paths(test, outcome) for test, outcome in items])
def _sem_outcome_paths(test: ast.AST, outcome: bool) -> list:
    if not isinstance(test, ast.BoolOp):
        return [[(test, outcome)]]
    is_and = isinstance(test.op, ast.And)
    if outcome == is_and:
        return _sem_fixed_outcome_paths(
            [(value, outcome) for value in test.values])
    paths = []
    for index, value in enumerate(test.values):
        items = [(previous, is_and)
                 for previous in test.values[:index]]
        items.append((value, outcome))
        paths.extend(_sem_fixed_outcome_paths(items))
    return paths
def _sem_expr_may_raise(node: ast.AST) -> bool:
    if (isinstance(node, ast.NamedExpr)
            and isinstance(node.target, ast.Name)):
        return _sem_expr_may_raise(node.value)
    try:
        ast.literal_eval(node)
    except (ValueError, TypeError, SyntaxError, RecursionError):
        return True
    return False
def _sem_target_may_raise(target: ast.AST) -> bool:
    if isinstance(target, ast.Name):
        return False
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_sem_target_may_raise(item) for item in target.elts)
    if isinstance(target, ast.Starred):
        return _sem_target_may_raise(target.value)
    return True
def _sem_statement_may_raise(stmt: ast.stmt) -> bool:
    if isinstance(stmt, ast.Assign):
        return (_sem_expr_may_raise(stmt.value)
                or any(_sem_target_may_raise(target)
                       for target in stmt.targets))
    if isinstance(stmt, ast.AnnAssign):
        return (stmt.value is None or _sem_expr_may_raise(stmt.value)
                or _sem_target_may_raise(stmt.target))
    if isinstance(stmt, ast.Expr):
        return _sem_expr_may_raise(stmt.value)
    if isinstance(stmt, (ast.Pass, ast.Break, ast.Continue)):
        return False
    if isinstance(stmt, ast.Return):
        return stmt.value is not None and _sem_expr_may_raise(stmt.value)
    return True
def _sem_try_handler_entry(stmts: list[ast.stmt], initial: Any, *,
                           copy_flow: Callable, step_flow: Callable,
                           merge_flows: Callable) -> tuple[Any, bool]:
    current = copy_flow(initial)
    exceptional = []
    bound_names: set[str] = set()
    simple_stmts = (ast.Assign, ast.AnnAssign, ast.AugAssign,
                    ast.Expr, ast.Delete)
    for stmt in _sem_reachable_prefix(stmts):
        before = copy_flow(current)
        after = step_flow(stmt, copy_flow(current))
        may_raise = _sem_statement_may_raise(stmt)
        if (isinstance(stmt, ast.Return)
                and isinstance(stmt.value, ast.Name)
                and stmt.value.id in bound_names):
            may_raise = False
        if may_raise:
            exceptional.append(before)
            if not isinstance(stmt, simple_stmts):
                exceptional.append(copy_flow(after))
        if isinstance(stmt, ast.Assign):
            bound_names.update(iter_unpack_target_names(stmt.targets))
        elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
            bound_names.update(iter_unpack_target_names(stmt.target))
        elif isinstance(stmt, ast.Delete):
            for name in iter_unpack_target_names(stmt.targets):
                bound_names.discard(name)
        current = after
    # 第二项标记 handler 是否可达；不可达 handler 不得污染 try 出口。
    return ((merge_flows(exceptional), True) if exceptional
            else (current, False))
def _sem_try_has_catch_all(stmt: ast.AST) -> bool:
    for handler in stmt.handlers:
        if handler.type is None or dotted_name(handler.type) in (
                "BaseException", "builtins.BaseException"):
            return True
    return False
def _guard_protects(guard: ast.AST, use: ast.AST, name: str, parents: dict,
                    safe_branch_of: Callable[[ast.AST, str], str | None],
                    *, repair_ok: Callable[[ast.AST], bool] | None = None
                    ) -> bool:
    safe_branch = safe_branch_of(guard.test, name)
    if safe_branch is None:
        return False
    safe_nodes = _sem_branch_nodes(guard, safe_branch)
    if any(in_subtree(use, stmt) for stmt in safe_nodes):
        return True
    if isinstance(guard, ast.Assert):
        return safe_branch == _GUARD_BODY and _sem_after_in_block(guard, use, parents)
    if isinstance(guard, ast.While):
        return (safe_branch == _GUARD_ORELSE
                and not loop_body_has_break(guard.body)
                and _sem_after_in_block(guard, use, parents))
    if not isinstance(guard, ast.If):
        return False
    unsafe_nodes = _sem_branch_nodes(
        guard, _GUARD_ORELSE if safe_branch == _GUARD_BODY else _GUARD_BODY)
    repaired = (repair_ok is not None
                and _branch_repairs_param(unsafe_nodes, name, repair_ok))
    return ((_sem_block_terminates(unsafe_nodes) or repaired)
            and _sem_after_in_block(guard, use, parents))
_TP07_MUTATING_ATTRS = frozenset({
    "append", "extend", "insert", "remove", "pop", "clear", "update",
    "sort", "reverse", "add", "discard", "setdefault", "popitem",
})
_TP07_SCOPE_STOP = FRAME_BOUNDARY_NODES + COMP_SCOPE_NODES
def _tp07_collect_walrus_targets(comp: ast.AST, into: set[str]) -> None:
    _wstack: list[ast.AST] = [comp]
    while _wstack:
        cur = _wstack.pop()
        if isinstance(cur, FRAME_BOUNDARY_NODES):
            continue
        if isinstance(cur, ast.NamedExpr) \
                and isinstance(cur.target, ast.Name):
            into.add(cur.target.id)
        _wstack.extend(ast.iter_child_nodes(cur))
def _tp07_collect_candidates(tree: ast.AST) -> dict[str, int]:
    candidates: dict[str, int] = {}
    for node in iter_scope_nodes(tree):
        _tp07_register_candidate(node, candidates)
    return candidates
def _tp07_register_candidate(node: ast.AST,
                             candidates: dict[str, int]) -> None:
    if isinstance(node, ast.Assign):
        if not isinstance(node.value, (ast.List, ast.Dict, ast.Set)):
            return
        for target in node.targets:
            if isinstance(target, ast.Name) \
                    and not target.id.startswith("_"):
                candidates.setdefault(target.id, node.lineno)
        return
    if (isinstance(node, ast.AnnAssign)
            and isinstance(node.value, (ast.List, ast.Dict, ast.Set))
            and isinstance(node.target, ast.Name)
            and not node.target.id.startswith("_")):
        candidates.setdefault(node.target.id, node.lineno)
def _tp07_collect_boundary_rebinds(node: ast.AST, cur: ast.AST,
                                   names: set[str]) -> None:
    if isinstance(cur, FRAME_BOUNDARY_NODES):
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef)):
            names.add(cur.name)
        for face in _tp07_split_boundary_faces(cur)[0]:
            _tp07_collect_walrus_targets(face, names)
    if (isinstance(cur, COMP_SCOPE_NODES)
            and not isinstance(node, ast.ClassDef)):
        _tp07_collect_walrus_targets(cur, names)
def _tp07_scope_rebinds(node: ast.AST) -> tuple[set[str], set[str]]:
    names: set[str] = set()
    global_names: set[str] = set()
    nonlocal_names: set[str] = set()
    _body = node.body if isinstance(node.body, list) else [node.body]
    stack = list(_body)
    while stack:
        cur = stack.pop()
        if isinstance(cur, _TP07_SCOPE_STOP):
            _tp07_collect_boundary_rebinds(node, cur, names)
            continue
        if isinstance(cur, ast.Global):
            global_names.update(cur.names)
            continue
        if isinstance(cur, ast.Nonlocal):
            nonlocal_names.update(cur.names)
            continue
        plain = _plain_rebind_names(cur)
        if plain:
            names.update(plain)
        if isinstance(cur, ast.Name) and isinstance(cur.ctx, ast.Store):
            names.add(cur.id)
        stack.extend(ast.iter_child_nodes(cur))
    names -= global_names
    names -= nonlocal_names
    if not isinstance(node, ast.ClassDef):
        names.update(collect_param_names(node))
    return names, global_names
def _tp07_collect_rebinds(
        tree: ast.AST) -> tuple[dict[int, set[str]], dict[int, set[str]]]:
    func_rebinds: dict[int, set[str]] = {}
    func_globals: dict[int, set[str]] = {}
    for node in walk_nodes(tree):
        if isinstance(node, COMP_SCOPE_NODES):
            func_rebinds[id(node)] = comp_target_names(node)
            func_globals[id(node)] = set()
            continue
        if not isinstance(node, FRAME_BOUNDARY_NODES):
            continue
        func_rebinds[id(node)], func_globals[id(node)] = \
            _tp07_scope_rebinds(node)
    return func_rebinds, func_globals
def _tp07_subscript_targets(targets) -> list[str]:
    bases: list[str] = []
    pending = list(targets)
    while pending:
        target = pending.pop()
        if isinstance(target, ast.Subscript):
            base = subscript_base_name(target)
            if base:
                bases.append(base)
        elif isinstance(target, (ast.Tuple, ast.List)):
            pending.extend(target.elts)
        elif isinstance(target, ast.Starred):
            pending.append(target.value)
    return bases
def _tp07_mutation_bases(child: ast.AST) -> list[str]:
    if isinstance(child, ast.Assign):
        return _tp07_subscript_targets(child.targets)
    if isinstance(child, ast.AugAssign):
        if isinstance(child.target, ast.Name):
            return [child.target.id]
        base = subscript_base_name(child.target)
        return [base] if base else []
    if isinstance(child, (ast.For, ast.AsyncFor)):
        return _tp07_subscript_targets([child.target])
    if isinstance(child, (ast.With, ast.AsyncWith)):
        return _tp07_subscript_targets([
            item.optional_vars for item in child.items
            if item.optional_vars is not None])
    if isinstance(child, ast.Delete):
        return _tp07_subscript_targets(child.targets)
    if (isinstance(child, ast.Call)
            and isinstance(child.func, ast.Attribute)
            and child.func.attr in _TP07_MUTATING_ATTRS):
        base = subscript_base_name(child.func.value)
        return [base] if base else []
    return []
def _tp07_chain_without_classes(chain: tuple, add: ast.AST) -> tuple:
    return tuple(o for o in chain if not isinstance(o, ast.ClassDef)) + (add,)
def _tp07_record_comp_mutations(comp: ast.AST, chain: tuple,
                                record) -> None:
    comp_chain = _tp07_chain_without_classes(chain, comp)
    for face in comp_element_roots(comp):
        for name in _tp07_mutation_bases(face):
            record(name, comp_chain, face)
    for gi, gen in enumerate(comp.generators):
        for name in _tp07_mutation_bases(gen.iter):
            record(name, chain if gi == 0 else comp_chain, gen.iter)
        for cond in gen.ifs:
            for name in _tp07_mutation_bases(cond):
                record(name, comp_chain, cond)
def _tp07_record_level_mutations(children, chain: tuple, record) -> None:
    for child in children:
        if isinstance(child, FRAME_BOUNDARY_NODES):
            continue
        if isinstance(child, COMP_SCOPE_NODES):
            _tp07_record_comp_mutations(child, chain, record)
            continue
        for name in _tp07_mutation_bases(child):
            record(name, chain, child)
def _tp07_child_nodes(value) -> list[ast.AST]:
    if isinstance(value, ast.AST):
        return [value]
    if isinstance(value, list):
        return [item for item in value if isinstance(item, ast.AST)]
    return []
def _tp07_split_boundary_faces(
        node: ast.AST) -> tuple[list[ast.AST], list[ast.AST]]:
    outer: list[ast.AST] = []
    body: list[ast.AST] = []
    for field, value in ast.iter_fields(node):
        target = body if field == "body" else outer
        target.extend(_tp07_child_nodes(value))
    return outer, body
def _tp07_push_comp_faces(work, comp: ast.AST, chain: tuple) -> None:
    comp_chain = _tp07_chain_without_classes(chain, comp)
    for gi, gen in reversed(list(enumerate(comp.generators))):
        for cond in reversed(gen.ifs):
            _tp07_push_node(work, cond, comp_chain)
        _tp07_push_node(work, gen.iter, chain if gi == 0 else comp_chain)
        _tp07_push_node(work, gen.target, comp_chain)
    for face in reversed(comp_element_roots(comp)):
        _tp07_push_node(work, face, comp_chain)
def _tp07_push_node(work, node: ast.AST, chain: tuple) -> None:
    if isinstance(node, FRAME_BOUNDARY_NODES):
        work.append((node, _tp07_chain_without_classes(chain, node), chain))
        return
    work.append((node, chain, None))
def _tp07_visit_boundary(node: ast.AST, chain: tuple, outer_chain: tuple,
                         work, record) -> None:
    outer_faces, body = _tp07_split_boundary_faces(node)
    _tp07_record_level_mutations(outer_faces, outer_chain, record)
    _tp07_push_children(work, outer_faces, outer_chain)
    _tp07_record_level_mutations(body, chain, record)
    _tp07_push_children(work, body, chain)
def _tp07_push_children(_work, children, chain: tuple) -> None:
    for child in reversed(children):
        if isinstance(child, COMP_SCOPE_NODES):
            _tp07_push_comp_faces(_work, child, chain)
            continue
        _tp07_push_node(_work, child, chain)
def _tp07_visit(root: ast.AST, root_chain: tuple, record) -> None:
    _work: list[tuple[ast.AST, tuple, tuple | None]] = []
    _tp07_push_node(_work, root, root_chain)
    while _work:
        node, chain, outer_chain = _work.pop()
        if outer_chain is not None:
            _tp07_visit_boundary(node, chain, outer_chain, _work, record)
            continue
        if isinstance(node, COMP_SCOPE_NODES):
            _tp07_record_comp_mutations(node, chain, record)
            _tp07_push_comp_faces(_work, node, chain)
            continue
        children = list(ast.iter_child_nodes(node))
        _tp07_record_level_mutations(children, chain, record)
        _tp07_push_children(_work, children, chain)
def _tp07_simple_class_binding(stmt: ast.stmt, name: str) -> bool | None:
    if isinstance(stmt, ast.Assign):
        return True if name in set(iter_unpack_target_names(
            stmt.targets)) else None
    if isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
        return (True if isinstance(stmt.target, ast.Name)
                and stmt.target.id == name else None)
    if isinstance(stmt, ast.AugAssign):
        return (True if isinstance(stmt.target, ast.Name)
                and stmt.target.id == name else None)
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return True if stmt.name == name else None
    if isinstance(stmt, (ast.Import, ast.ImportFrom)):
        return True if name in _import_bound_names(stmt) else None
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        targets = {target for item in stmt.items
                   if item.optional_vars is not None
                   for target in iter_unpack_target_names(item.optional_vars)}
        return True if name in targets else None
    if (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.NamedExpr)
            and isinstance(stmt.value.target, ast.Name)):
        return True if stmt.value.target.id == name else None
    if isinstance(stmt, ast.Delete):
        targets = {target for item in stmt.targets
                   for target in iter_unpack_target_names(item)}
        return False if name in targets else None
    return None
def _tp07_class_block_states(
        stmts: list[ast.stmt], name: str, states: frozenset[bool],
        use: ast.AST | None = None) -> frozenset[bool]:
    for stmt in _sem_reachable_prefix(stmts):
        if use is not None and in_subtree(use, stmt):
            return _tp07_class_statement_states(stmt, name, states, use)
        states = _tp07_class_statement_states(stmt, name, states)
    return states
def _tp07_definitely_nonempty_iterable(iterable: ast.AST) -> bool:
    if isinstance(iterable, (ast.List, ast.Tuple, ast.Set)):
        return any(not isinstance(element, ast.Starred)
                   for element in iterable.elts)
    if isinstance(iterable, ast.Dict):
        return any(key is not None for key in iterable.keys)
    return (isinstance(iterable, ast.Constant)
            and isinstance(iterable.value, (str, bytes))
            and bool(iterable.value))

def _tp07_class_statement_states(
        stmt: ast.stmt, name: str, states: frozenset[bool],
        use: ast.AST | None = None) -> frozenset[bool]:
    if isinstance(stmt, ast.If):
        if use is not None and in_subtree(use, stmt.test):
            return states
        if use is not None and any(in_subtree(use, node) for node in stmt.body):
            return _tp07_class_block_states(stmt.body, name, states, use)
        if use is not None and any(in_subtree(use, node) for node in stmt.orelse):
            return _tp07_class_block_states(stmt.orelse, name, states, use)
        outcomes = []
        if not _sem_block_terminates(stmt.body):
            outcomes.append(_tp07_class_block_states(
                stmt.body, name, states))
        if not _sem_block_terminates(stmt.orelse):
            outcomes.append(_tp07_class_block_states(
                stmt.orelse, name, states))
        return (frozenset().union(*outcomes)
                if outcomes else frozenset())
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        targets = {target for item in stmt.items
                   if item.optional_vars is not None
                   for target in iter_unpack_target_names(item.optional_vars)}
        body_states = frozenset({True}) if name in targets else states
        if use is not None and not any(
                in_subtree(use, node) for node in stmt.body):
            return states
        return _tp07_class_block_states(stmt.body, name, body_states, use)
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        if use is not None and in_subtree(use, stmt.iter):
            return states
        bound = name in iter_unpack_target_names(stmt.target)
        body_states = frozenset({True}) if bound else states
        if use is not None and any(in_subtree(use, node) for node in stmt.body):
            return _tp07_class_block_states(stmt.body, name, body_states, use)
        if use is not None and any(in_subtree(use, node) for node in stmt.orelse):
            entry_states = states
            if (not loop_body_has_break(stmt.body)
                    and _tp07_definitely_nonempty_iterable(stmt.iter)):
                entry_states = _tp07_class_block_states(
                    stmt.body, name, body_states)
            return _tp07_class_block_states(
                stmt.orelse, name, entry_states, use)
        body = _tp07_class_block_states(stmt.body, name, body_states)
        states = _tp07_class_block_states(stmt.orelse, name, states | body)
        return states
    if isinstance(stmt, ast.While):
        if use is not None and in_subtree(use, stmt.test):
            return states
        if use is not None and any(in_subtree(use, node) for node in stmt.body):
            return _tp07_class_block_states(stmt.body, name, states, use)
        if use is not None and any(in_subtree(use, node) for node in stmt.orelse):
            return _tp07_class_block_states(stmt.orelse, name, states, use)
        body = _tp07_class_block_states(stmt.body, name, states)
        return _tp07_class_block_states(stmt.orelse, name, states | body)
    if isinstance(stmt, TRY_NODE_TYPES):
        if use is not None:
            if any(in_subtree(use, node) for node in stmt.body):
                return _tp07_class_block_states(stmt.body, name, states, use)
            body = _tp07_class_block_states(stmt.body, name, states)
            if any(in_subtree(use, node) for node in stmt.orelse):
                return _tp07_class_block_states(stmt.orelse, name, body, use)
            handler_entry, handler_reachable = _tp07_try_handler_entry(
                stmt, name, states)
            for handler in stmt.handlers:
                if any(in_subtree(use, node) for node in handler.body):
                    return _tp07_class_block_states(
                        handler.body, name, handler_entry, use)
            if any(in_subtree(use, node) for node in stmt.finalbody):
                outcomes = _tp07_try_outcome_states(
                    stmt, name, states, include_terminated=True)
                if (not _sem_try_has_catch_all(stmt)
                        and handler_reachable):
                    outcomes.append(handler_entry)
                merged = frozenset().union(*outcomes)
                return _tp07_class_block_states(
                    stmt.finalbody, name, merged, use)
            return states
        outcomes = _tp07_try_outcome_states(stmt, name, states)
        merged = frozenset().union(*outcomes)
        return _tp07_class_block_states(stmt.finalbody, name, merged)
    if isinstance(stmt, ast.Match):
        if use is not None and in_subtree(use, stmt.subject):
            return states
        for case in stmt.cases:
            captured = name in iter_pattern_capture_names(case.pattern)
            case_states = frozenset({True}) if captured else states
            if use is not None and case.guard is not None \
                    and in_subtree(use, case.guard):
                return case_states
            if use is not None and any(
                    in_subtree(use, node) for node in case.body):
                return _tp07_class_block_states(
                    case.body, name, case_states, use)
        if use is not None:
            return states
        outcomes = []
        for case in stmt.cases:
            case_states = (frozenset({True})
                           if name in iter_pattern_capture_names(case.pattern)
                           else states)
            if not _sem_block_terminates(case.body):
                outcomes.append(_tp07_class_block_states(
                    case.body, name, case_states))
        if not any(_match_case_is_default(case) for case in stmt.cases):
            outcomes.append(states)
        return (frozenset().union(*outcomes)
                if outcomes else frozenset())
    if use is not None:
        return states
    binding = _tp07_simple_class_binding(stmt, name)
    if binding is not None:
        return frozenset({binding})
    return states
def _tp07_try_handler_entry(
        stmt: ast.AST, name: str, states: frozenset[bool],
) -> tuple[frozenset[bool], bool]:
    return _sem_try_handler_entry(
        stmt.body, states, copy_flow=lambda flow: flow,
        step_flow=lambda node, flow: _tp07_class_statement_states(
            node, name, flow),
        merge_flows=lambda flows: frozenset().union(*flows))
def _tp07_try_outcome_states(stmt: ast.AST, name: str,
                             states: frozenset[bool], *,
                             include_terminated: bool = False
                             ) -> list[frozenset[bool]]:
    body = _tp07_class_block_states(stmt.body, name, states)
    normal = _tp07_class_block_states(stmt.orelse, name, body)
    normal_terminated = (_sem_block_terminates(stmt.body)
                         or _sem_block_terminates(stmt.orelse))
    outcomes = ([] if normal_terminated and not include_terminated
                else [normal])
    handler_entry, handler_reachable = _tp07_try_handler_entry(
        stmt, name, states)
    for handler in stmt.handlers:
        if (handler_reachable
                and (include_terminated
                     or not _sem_block_terminates(handler.body))):
            outcomes.append(_tp07_class_block_states(
                handler.body, name, handler_entry))
    return outcomes
def _tp07_class_local_at_use(scope: ast.ClassDef, name: str,
                             use: ast.AST) -> bool:
    states = _tp07_class_block_states(
        scope.body, name, frozenset({False}), use)
    return states == frozenset({True})
def _tp07_record_pollution(candidates: dict, func_rebinds: dict,
                           func_globals: dict, mutated: set, name: str,
                           chain: tuple, use: ast.AST) -> None:
    if name not in candidates:
        return
    for owner in reversed(chain):
        if name in func_globals.get(id(owner), ()):
            break
        if name not in func_rebinds.get(id(owner), ()):
            continue
        if isinstance(owner, ast.ClassDef):
            if _tp07_class_local_at_use(owner, name, use):
                return
            continue
        return
    mutated.add(name)
def _tp07_finding(name: str, line: int, filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="TP-07", severity="P1", dimension="trap",
        file=filepath, line=line,
        description=f"模块级可变全局 {name} 被原地修改（跨模块共享状态）",
        suggestion=("根因: 模块级 list/dict/set 是进程内全局共享状态，"
                    "原地修改对所有导入方立即可见，多线程/多入口并发时"
                    "产生竞态与状态残留。该问题属于全局状态陷阱类别。\n"
                    "修复策略: 改为函数内局部构建返回；确需共享则用 "
                    "immutable tuple/frozenset + 显式重建，或加锁封装访问器\n"
                    "参考标准: Python 类属性共享语义 / Google Python 风格指南"),
    )
def check_TP07(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    candidates = _tp07_collect_candidates(tree)
    if not candidates:
        return issues
    func_rebinds, func_globals = _tp07_collect_rebinds(tree)
    mutated: set[str] = set()
    def _record(name: str, chain: tuple, use: ast.AST) -> None:
        _tp07_record_pollution(candidates, func_rebinds, func_globals,
                               mutated, name, chain, use)
    _tp07_visit(tree, (), _record)
    suppress_map = parse_suppressions(join_source_lines(source_lines))
    for name in sorted(mutated):
        if is_suppressed(suppress_map, candidates[name], "TP-07"):
            continue
        issues.append(_tp07_finding(name, candidates[name], filepath))
    return issues
def _fs01_definitely_not_none(node: ast.AST | None) -> bool:
    if isinstance(node, ast.Constant):
        return node.value is not None
    if isinstance(node, (ast.JoinedStr, ast.List, ast.Tuple, ast.Set, ast.Dict,
                          ast.ListComp, ast.SetComp, ast.DictComp,
                          ast.GeneratorExp, ast.Compare)):
        return True
    return isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not)
def _fs01_default_is_none(node: ast.Call, kw_default: ast.keyword | None) -> bool:
    return (
        (kw_default is not None
         and isinstance(kw_default.value, ast.Constant)
         and kw_default.value.value is None)
        or (len(node.args) >= 2
            and isinstance(node.args[1], ast.Constant)
            and node.args[1].value is None))
def _fs01_has_no_default(node: ast.Call, kw_default: ast.keyword | None) -> bool:
    if kw_default is not None or len(node.args) >= 2:
        return False
    return len(node.args) == 1 or any(kw.arg == "key" for kw in node.keywords)
def _fs01_getenv_risk(node: ast.Call) -> bool:
    if (any(isinstance(a, ast.Starred) for a in node.args)
            or any(kw.arg is None for kw in node.keywords)):
        return False
    kw_default = kw_arg(node, "default")
    return (_fs01_has_no_default(node, kw_default)
            or _fs01_default_is_none(node, kw_default))
_FS01_ENV_ACCESSORS = frozenset({"os.getenv", "os.environ.get"})
def _fs01_env_accessor(node: ast.Call,
                       resolver: _ModuleCallResolver) -> str:
    accessor = resolver.canonical_name(node, "os")
    return accessor if accessor in _FS01_ENV_ACCESSORS else ""
_FS01_TEST_CONTAINERS = (ast.If, ast.While, ast.IfExp, ast.Assert)
_FS01_ORDERING_COMPARE_OPS = (ast.Lt, ast.LtE, ast.Gt, ast.GtE)
def _fs01_compare_handles_none(node: ast.AST, parent: ast.Compare) -> bool:
    for index, op in enumerate(parent.ops):
        left = parent.left if index == 0 else parent.comparators[index - 1]
        right = parent.comparators[index]
        if node is not left and node is not right:
            continue
        if isinstance(op, _FS01_ORDERING_COMPARE_OPS):
            return False
        if isinstance(op, (ast.In, ast.NotIn)) and node is right:
            return False
    return True
def _fs01_or_default_consumes(node: ast.AST, parent: ast.BoolOp) -> bool:
    if not isinstance(parent.op, ast.Or):
        return False
    for index, value in enumerate(parent.values):
        if value is not node:
            continue
        later = parent.values[index + 1:]
        if not later:
            return False
        return (any(_fs01_truthy_constant(item) for item in later)
                or _fs01_definitely_not_none(later[-1]))
    return False
def _fs01_or_short_circuits(node: ast.AST, parent: ast.BoolOp) -> bool:
    if not isinstance(parent.op, ast.Or):
        return False
    for index, value in enumerate(parent.values):
        if value is not node:
            continue
        return any(_fs01_truthy_constant(prev)
                   for prev in parent.values[:index])
    return False
def _fs01_truthy_constant(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant) and node.value is not None
            and bool(node.value))
def _fs01_in_test_context(node: ast.Call, parent_map: dict) -> bool:
    cur: ast.AST = node
    while id(cur) in parent_map:
        parent = parent_map[id(cur)]
        if isinstance(parent, ast.BoolOp):
            if (_fs01_or_short_circuits(cur, parent)
                    or _fs01_or_default_consumes(cur, parent)):
                return True
            cur = parent
            continue
        if (isinstance(parent, ast.UnaryOp)
                and isinstance(parent.op, ast.Not)):
            return True
        if isinstance(parent, _FS01_TEST_CONTAINERS):
            return parent.test is cur
        if isinstance(parent, ast.Call) and parent.args and parent.args[0] is cur:
            name = expr_target_name(parent.func)
            if name == "bool":
                return True
        if isinstance(parent, ast.Compare):
            return _fs01_compare_handles_none(cur, parent)
        return False
    return False
def _fs01_scope_root(node: ast.AST, parent_map: dict) -> ast.AST | None:
    cur = node
    while id(cur) in parent_map:
        cur = parent_map[id(cur)]
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda, ast.ClassDef, ast.Module)):
            return cur
    return None
def _assignment_value_pairs(
        target: ast.AST, value: ast.AST) -> list[tuple[list[str], ast.AST]]:
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(item, ast.Starred) for item in target.elts)):
        pairs = []
        for target_item, value_item in zip(
                target.elts, value.elts, strict=True):
            pairs.extend(_assignment_value_pairs(target_item, value_item))
        return pairs
    return [(list(iter_unpack_target_names(target)), value)]
def _fs01_guard_names(node: ast.AST, parent_map: dict) -> list[str]:
    current = node
    parent = parent_map.get(id(current))
    while isinstance(parent, (ast.Tuple, ast.List)):
        current = parent
        parent = parent_map.get(id(current))
    if isinstance(parent, ast.Assign):
        names = []
        for target in parent.targets:
            for bound_names, bound_value in _assignment_value_pairs(
                    target, parent.value):
                if bound_value is node:
                    names.extend(bound_names)
        return names
    if isinstance(parent, ast.AnnAssign) and isinstance(parent.target, ast.Name):
        return [parent.target.id]
    if (isinstance(parent, ast.NamedExpr)
            and isinstance(parent.target, ast.Name)):
        return [parent.target.id]
    return []
def _fs01_guarded_name(test: ast.AST) -> str:
    if isinstance(test, ast.Name):
        return test.id
    if isinstance(test, ast.NamedExpr) and isinstance(test.target, ast.Name):
        return test.target.id
    return ""
def _fs01_atom_branch(test: ast.AST, name: str) -> str | None:
    if _fs01_guarded_name(test) == name:
        return _GUARD_BODY
    if (isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)
            and _fs01_guarded_name(test.operand) == name):
        return _GUARD_ORELSE
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1):
        return None
    left, right = test.left, test.comparators[0]
    if not ((_fs01_guarded_name(left) == name
             and isinstance(right, ast.Constant) and right.value is None)
            or (_fs01_guarded_name(right) == name
                and isinstance(left, ast.Constant) and left.value is None)):
        return None
    op = test.ops[0]
    if isinstance(op, (ast.Is, ast.Eq)):
        return _GUARD_ORELSE
    if isinstance(op, (ast.IsNot, ast.NotEq)):
        return _GUARD_BODY
    return None
def _fs01_path_defends(path: list, name: str) -> bool:
    defended = False
    for test, outcome in path:
        for rebind in _guard_walrus_rebinds(test, name):
            defended = _fs01_definitely_not_none(rebind.value)
        branch = _fs01_atom_branch(test, name)
        if branch == _GUARD_BODY:
            defended = outcome
        elif branch == _GUARD_ORELSE:
            defended = not outcome
    return defended
def _fs01_boolop_defends(use: ast.AST, name: str, parents: dict) -> bool:
    current = use
    while id(current) in parents:
        parent = parents[id(current)]
        if isinstance(parent, ast.BoolOp):
            index = next((i for i, value in enumerate(parent.values)
                          if value is current), -1)
            if index > 0:
                outcome = isinstance(parent.op, ast.And)
                paths = _sem_fixed_outcome_paths([
                    (value, outcome) for value in parent.values[:index]])
                if all(_fs01_path_defends(path, name) for path in paths):
                    return True
        current = parent
    return False
def _fs01_use_needs_guard(node: ast.Name, parents: dict) -> bool:
    if _fs01_boolop_defends(node, node.id, parents):
        return False
    holder = parents.get(id(node))
    if isinstance(holder, _FS01_TEST_CONTAINERS) and holder.test is node:
        return False
    if isinstance(holder, ast.BoolOp):
        return False
    if isinstance(holder, ast.UnaryOp):
        return not isinstance(holder.op, ast.Not)
    if isinstance(holder, ast.Compare):
        return not _fs01_compare_handles_none(node, holder)
    return True
def _statement_rebind_value(stmt: ast.stmt, name: str) -> ast.AST | None:
    if isinstance(stmt, ast.Assign):
        targets = stmt.targets
    elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
        targets = [stmt.target]
    else:
        return None
    if name not in {target.id for target in targets
                    if isinstance(target, ast.Name)}:
        return None
    return stmt.value
def _sem_rebind_statements(
        stmts: list[ast.stmt], name: str, states: frozenset[bool],
        value_ok: Callable[[ast.AST], bool]) -> frozenset[bool]:
    for stmt in _sem_reachable_prefix(stmts):
        value = _statement_rebind_value(stmt, name)
        if value is not None:
            states = frozenset({value_ok(value)})
            continue
        if isinstance(stmt, ast.If):
            outcomes = []
            if not _sem_block_terminates(stmt.body):
                outcomes.append(_sem_rebind_statements(
                    stmt.body, name, states, value_ok))
            if not _sem_block_terminates(stmt.orelse):
                outcomes.append(_sem_rebind_statements(
                    stmt.orelse, name, states, value_ok))
            states = (frozenset().union(*outcomes)
                      if outcomes else frozenset())
            continue
        if isinstance(stmt, ast.While):
            body = _sem_rebind_statements(
                stmt.body, name, states, value_ok)
            normal = (states | body
                      if _sem_loop_body_has_back_edge(stmt.body) else states)
            outcomes = _sem_rebind_statements(
                stmt.orelse, name, normal, value_ok)
            states = (outcomes | body
                      if loop_body_has_break(stmt.body) else outcomes)
            continue
        if isinstance(stmt, (ast.For, ast.AsyncFor)):
            body_states = (frozenset({False})
                           if name in iter_unpack_target_names(stmt.target)
                           else states)
            body = _sem_rebind_statements(
                stmt.body, name, body_states, value_ok)
            normal = (body_states | body
                      if _sem_loop_body_has_back_edge(stmt.body)
                      else body_states)
            outcomes = _sem_rebind_statements(
                stmt.orelse, name, normal, value_ok)
            states = (outcomes | body
                      if loop_body_has_break(stmt.body) else outcomes)
            continue
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            targets = {target for item in stmt.items
                       if item.optional_vars is not None
                       for target in iter_unpack_target_names(
                           item.optional_vars)}
            states = _sem_rebind_statements(
                stmt.body, name,
                frozenset({False}) if name in targets else states, value_ok)
            continue
        if isinstance(stmt, TRY_NODE_TYPES):
            body = _sem_rebind_statements(
                stmt.body, name, states, value_ok)
            body_terminated = _sem_block_terminates(stmt.body)
            if not body_terminated:
                body = _sem_rebind_statements(
                    stmt.orelse, name, body, value_ok)
            normal_terminated = (
                body_terminated or _sem_block_terminates(stmt.orelse))
            handler_entry, handler_reachable = _sem_try_handler_entry(
                stmt.body, states, copy_flow=lambda flow: flow,
                step_flow=lambda node, flow: _sem_rebind_statements(
                    [node], name, flow, value_ok),
                merge_flows=lambda flows: frozenset().union(*flows))
            outcomes = [] if normal_terminated else [body]
            outcomes.extend(_sem_rebind_statements(
                handler.body, name, handler_entry, value_ok)
                for handler in stmt.handlers
                if handler_reachable
                and not _sem_block_terminates(handler.body))
            states = _sem_rebind_statements(
                stmt.finalbody, name,
                frozenset().union(*outcomes), value_ok)
            continue
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            if stmt.name == name:
                states = frozenset({False})
            continue
        names = _plain_rebind_names(stmt)
        if names is not None and name in names:
            states = frozenset({False})
    return states
def _rebind_between_guard_and_use(
        guard: ast.AST, name: str, use: ast.AST, parents: dict,
        value_ok: Callable[[ast.AST], bool], *,
        initially_valid: bool = True) -> bool:
    segments: list[list[ast.stmt]] = []
    current = use
    while current is not guard and id(current) in parents:
        if isinstance(current, ast.stmt):
            block = _sem_statement_block(current, parents)
            if block is not None:
                previous = block[:block.index(current)]
                if guard in previous:
                    segments.append(previous[previous.index(guard) + 1:])
                    break
                segments.append(previous)
        current = parents[id(current)]
    states = frozenset({initially_valid})
    for segment in reversed(segments):
        states = _sem_rebind_statements(
            segment, name, states, value_ok)
    return False in states
def _fs01_later_loads(scope_nodes: list[ast.AST], names: list[str],
                       call_pos: tuple[int, int]) -> list[ast.Name]:
    return [sub for sub in scope_nodes
            if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
            and sub.id in names and (sub.lineno, sub.col_offset) > call_pos]
def _fs01_guard_candidate_uses(loads: list[ast.Name], binding: ast.AST,
                               parent_map: dict) -> list[ast.Name]:
    return [sub for sub in loads
            if _fs01_use_needs_guard(sub, parent_map)
            and _rebind_between_guard_and_use(
                binding, sub.id, sub, parent_map, _fs01_definitely_not_none,
                initially_valid=False)]
def _fs01_later_guards(scope_nodes: list[ast.AST],
                       call_pos: tuple[int, int]) -> list[ast.AST]:
    return [guard for guard in scope_nodes
            if isinstance(guard, _FS01_TEST_CONTAINERS)
            and (guard.lineno, guard.col_offset) > call_pos]
def _fs01_name_binds_to_scope(binding_scope: ast.AST, name: str,
                               use: ast.AST, parent_map: dict) -> bool:
    for scope in scope_chain(use, parent_map):
        if scope is binding_scope:
            declaration = _scope_name_declaration(scope, name)
            return (not declaration or
                    (declaration == "global" and isinstance(scope, ast.Module)))
        declaration = _scope_name_declaration(scope, name)
        if declaration == "global":
            return isinstance(binding_scope, ast.Module)
        if declaration == "nonlocal":
            continue
        if _scope_binds_name(scope, name):
            return False
    return False
def _fs01_guarded_after_bind(node: ast.AST, parent_map: dict) -> bool:
    names = _fs01_guard_names(node, parent_map)
    if not names:
        return False
    parent = parent_map.get(id(node))
    scope = _fs01_scope_root(parent, parent_map)
    if scope is None:
        return False
    call_pos = (node.lineno, node.col_offset)
    scope_nodes = list(iter_scope_nodes(scope))
    own_ids = {id(item) for item in scope_nodes}
    loads = _fs01_later_loads(scope_nodes, names, call_pos)
    loads.extend(
        sub for sub in walk_nodes(scope)
        if id(sub) not in own_ids
        and isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
        and sub.id in names and (sub.lineno, sub.col_offset) > call_pos
        and _fs01_name_binds_to_scope(scope, sub.id, sub, parent_map))
    uses = _fs01_guard_candidate_uses(loads, parent, parent_map)
    if not uses:
        return bool(loads)
    guards = _fs01_later_guards(scope_nodes, call_pos)
    guards.extend(
        guard for guard in walk_nodes(scope)
        if id(guard) not in own_ids
        and isinstance(guard, _FS01_TEST_CONTAINERS)
        and (guard.lineno, guard.col_offset) > call_pos)
    current = node
    while id(current) in parent_map:
        current = parent_map[id(current)]
        if (isinstance(current, _FS01_TEST_CONTAINERS)
                and in_subtree(node, current.test)):
            guards.append(current)
        elif (isinstance(current, ast.While)
              and any(in_subtree(node, stmt) for stmt in current.body)):
            # 调用在循环体内：循环出口意味着 test 为假，之后的使用由 test 守卫。
            guards.append(current)
    return all(
        any(_fs01_covers_use(guard, names, use, parent_map)
            for guard in guards)
        for use in uses)
def _fs01_covers_use(guard: ast.AST, names: list[str], use: ast.Name,
                     parent_map: dict) -> bool:
    safe_branch = partial(_fold_guard_branches, atom=_fs01_atom_branch)
    if not any(safe_branch(guard.test, name) is not None for name in names):
        return False
    return any(_guard_protects(
        guard, use, name, parent_map, safe_branch,
        repair_ok=_fs01_definitely_not_none)
        and not _rebind_between_guard_and_use(
            guard, name, use, parent_map, _fs01_definitely_not_none)
        for name in names if use.id == name)
def check_FS01(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    parent_map = build_parent_map(tree)
    resolver = _ModuleCallResolver(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        accessor = _fs01_env_accessor(node, resolver)
        if not accessor:
            continue
        if _fs01_in_test_context(node, parent_map):
            continue
        if _fs01_guarded_after_bind(node, parent_map):
            continue
        if not _fs01_getenv_risk(node):
            continue
        issues.append(DiagnoseFinding(
            id="FS-01", severity="P2", dimension="trap",
            file=filepath, line=node.lineno,
            description=(f"{accessor} 缺省默认值或默认值为 None，"
                          "环境变量缺失时返回 None"),
            suggestion=("根因: 环境变量缺失时 None 参与路径拼接抛 TypeError "
                        "或生成假路径。\n"
                        f"修复策略: {accessor}('X', default) 提供默认值；"
                        "关键路径缺失应显式报错而非静默\n"
                        "参考标准: Python os.getenv 文档 / 防御式编程"),
        ))
    return issues
_JS01_JSON_FACTORY = frozenset({"json.load", "json.loads"})
_JS01_DICT_METHODS = frozenset({
    "get", "items", "keys", "values", "pop", "popitem", "setdefault", "update",
})
_JS01_FIX = ("根因: json.loads/load 可合法解析出标量/列表（如 loads(\"123\") 返回 int），"
             "返回形态由输入决定而非由调用方假设决定；对非 dict 结果直接按 "
             "dict 使用会抛 TypeError/AttributeError，中断当前处理流程。\n"
             "修复策略: 解析后先 isinstance(payload, dict) 做形状校验，"
             "非 dict 走明确的降级/报错路径；列表预期形态用 "
             "isinstance(payload, list)\n"
             "参考标准: Python json 文档 / 防御式编程")
def _js01_json_flows(val: ast.AST, json_calls: _JS01Calls,
                      json_names: Container[str]) -> bool:
    stack = [val]
    while stack:
        cur = stack.pop()
        if id(cur) in json_calls:
            return True
        if isinstance(cur, ast.Name) and cur.id in json_names:
            return True
        if isinstance(cur, ast.IfExp):
            stack.extend((cur.body, cur.orelse))
        elif isinstance(cur, ast.BoolOp):
            stack.extend(cur.values)
        elif isinstance(cur, ast.NamedExpr):
            stack.append(cur.value)
    return False
def _js01_definitely_dict(node: ast.AST | None) -> bool:
    return isinstance(node, (ast.Dict, ast.DictComp))
def _js01_flow_copy(flow):
    origins, safe = flow
    return dict(origins), set(safe)
def _js01_flow_merge(flows):
    flows = list(flows)
    if not flows:
        return {}, set()
    origins: dict[str, frozenset[ast.AST]] = {}
    for flow_origins, _safe in flows:
        for name, nodes in flow_origins.items():
            origins[name] = origins.get(name, frozenset()) | nodes
    safe = set(flows[0][1])
    for _origins, flow_safe in flows[1:]:
        safe.intersection_update(flow_safe)
    return origins, safe
def _js01_value_flow(value: ast.AST, flow, json_calls: _JS01Calls):
    origins: set[ast.AST] = set()
    direct_json = False
    safe = True
    stack = [value]
    while stack:
        current = stack.pop()
        if id(current) in json_calls:
            direct_json = True
            safe = False
        elif isinstance(current, ast.Name):
            origins.update(flow[0].get(current.id, ()))
            safe = safe and current.id in flow[1]
        elif (isinstance(current, ast.IfExp)
              and getattr(json_calls, "resolver", None) is not None):
            for branch, outcome in ((current.body, True),
                                    (current.orelse, False)):
                branch_flow = _js01_test_outcome_flow(
                    current.test, flow, json_calls, outcome)
                branch_origins, branch_json, branch_safe = _js01_value_flow(
                    branch, branch_flow, json_calls)
                origins.update(branch_origins)
                direct_json = direct_json or branch_json
                safe = safe and branch_safe
        elif isinstance(current, ast.IfExp):
            stack.extend((current.body, current.orelse))
        elif isinstance(current, ast.BoolOp):
            stack.extend(current.values)
        elif isinstance(current, ast.NamedExpr):
            stack.append(current.value)
        elif _js01_definitely_dict(current):
            continue
        else:
            safe = False
    return origins, direct_json, safe
def _js01_assign_flow(flow, names: list[str], value: ast.AST,
                      node: ast.AST, json_calls: _JS01Calls) -> None:
    value_origins, direct_json, safe = _js01_value_flow(
        value, flow, json_calls)
    if direct_json:
        value_origins.add(node)
    for name in names:
        flow[1].discard(name)
        if value_origins:
            flow[0][name] = frozenset(value_origins)
        else:
            flow[0].pop(name, None)
        if safe:
            flow[1].add(name)
def _js01_unknown_rebind(flow, names) -> None:
    for name in names:
        flow[1].discard(name)
        flow[0].pop(name, None)
def _js01_apply_namedexprs(root: ast.AST | None, flow,
                           json_calls: _JS01Calls) -> None:
    if root is None:
        return
    found: list[ast.NamedExpr] = []
    stack = [root]
    while stack:
        current = stack.pop()
        if isinstance(current, FRAME_BOUNDARY_NODES):
            continue
        if isinstance(current, ast.NamedExpr) and isinstance(
                current.target, ast.Name):
            found.append(current)
        stack.extend(ast.iter_child_nodes(current))
    for node in sorted(found, key=lambda item: (item.lineno, item.col_offset)):
        _js01_assign_flow(
            flow, [node.target.id], node.value, node, json_calls)
def _js01_flow_block(stmts: list[ast.stmt], use: ast.AST | None,
                     flow, json_calls: _JS01Calls):
    for stmt in _sem_reachable_prefix(stmts):
        if use is not None and in_subtree(use, stmt):
            return _js01_flow_before_statement(
                stmt, use, flow, json_calls)
        flow = _js01_flow_statement(stmt, flow, json_calls)
    return flow
def _js01_try_handler_entry(stmt: ast.AST, flow,
                            json_calls: _JS01Calls):
    return _sem_try_handler_entry(
        stmt.body, flow, copy_flow=_js01_flow_copy,
        step_flow=lambda node, current: _js01_flow_statement(
            node, current, json_calls),
        merge_flows=_js01_flow_merge)
def _js01_try_outcome_flows(stmt: ast.AST, flow, json_calls: _JS01Calls,
                            *, include_terminated: bool = False):
    body = _js01_flow_block(
        stmt.body, None, _js01_flow_copy(flow), json_calls)
    normal = _js01_flow_block(stmt.orelse, None, body, json_calls)
    handler_entry, handler_reachable = _js01_try_handler_entry(
        stmt, flow, json_calls)
    normal_terminated = (_sem_block_terminates(stmt.body)
                         or _sem_block_terminates(stmt.orelse))
    outcomes = ([] if normal_terminated and not include_terminated
                else [normal])
    for handler in stmt.handlers if handler_reachable else ():
        handler_flow = _js01_flow_copy(handler_entry)
        if handler.name:
            _js01_unknown_rebind(handler_flow, [handler.name])
        handler_exit = _js01_flow_block(
            handler.body, None, handler_flow, json_calls)
        if include_terminated or not _sem_block_terminates(handler.body):
            outcomes.append(handler_exit)
    return outcomes
def _js01_match_case_entry_flow(case: ast.match_case, flow,
                                json_calls: _JS01Calls,
                                cutoff: ast.AST | None = None):
    case_flow = _js01_flow_copy(flow)
    _js01_unknown_rebind(
        case_flow, iter_pattern_capture_names(case.pattern))
    if (cutoff is not None and case.guard is not None
            and in_subtree(cutoff, case.guard)):
        return case_flow
    return _js01_test_outcome_flow(
        case.guard, case_flow, json_calls, True)
def _js01_match_pattern_always_matches(case: ast.match_case) -> bool:
    return (isinstance(case.pattern, ast.MatchAs)
            and case.pattern.pattern is None)
def _js01_match_case_follow_flow(case: ast.match_case, flow,
                                 json_calls: _JS01Calls):
    always_matches = _js01_match_pattern_always_matches(case)
    if case.guard is None:
        return None if always_matches else _js01_flow_copy(flow)
    case_flow = _js01_flow_copy(flow)
    _js01_unknown_rebind(
        case_flow, iter_pattern_capture_names(case.pattern))
    guard_false = _js01_test_outcome_flow(
        case.guard, case_flow, json_calls, False)
    if always_matches:
        return guard_false
    return _js01_flow_merge((flow, guard_false))
def _js01_refine_dict_guard(test: ast.AST, outcome: bool, flow,
                            json_calls: _JS01Calls) -> None:
    resolver = getattr(json_calls, "resolver", None)
    if resolver is None:
        return
    candidate = test
    positive = outcome
    if isinstance(candidate, ast.UnaryOp) and isinstance(candidate.op, ast.Not):
        candidate = candidate.operand
        positive = not positive
    if not positive:
        return
    name = _js01_dict_guard_name(candidate, resolver)
    if name:
        flow[1].add(name)
def _js01_test_outcome_flow(test: ast.AST, flow,
                            json_calls: _JS01Calls, outcome: bool):
    if not isinstance(test, ast.BoolOp):
        current = _js01_flow_copy(flow)
        _js01_apply_namedexprs(test, current, json_calls)
        _js01_refine_dict_guard(test, outcome, current, json_calls)
        return current
    flows = []
    for path in _sem_outcome_paths(test, outcome):
        current = _js01_flow_copy(flow)
        for atom, atom_outcome in path:
            _js01_apply_namedexprs(atom, current, json_calls)
            _js01_refine_dict_guard(
                atom, atom_outcome, current, json_calls)
        flows.append(current)
    return _js01_flow_merge(flows)
def _js01_while_exit_flow(stmt: ast.While, flow,
                          json_calls: _JS01Calls):
    body_entry = _js01_test_outcome_flow(
        stmt.test, flow, json_calls, True)
    body_exit = _js01_flow_block(
        stmt.body, None, body_entry, json_calls)
    flows = ((flow, body_exit)
             if _sem_loop_body_has_back_edge(stmt.body) else (flow,))
    before_exit_test = _js01_flow_merge(flows)
    return _js01_test_outcome_flow(
        stmt.test, before_exit_test, json_calls, False)
def _js01_for_exit_flow(stmt: ast.For | ast.AsyncFor, flow,
                        json_calls: _JS01Calls):
    body_flow = _js01_flow_copy(flow)
    _js01_unknown_rebind(
        body_flow, list(iter_unpack_target_names(stmt.target)))
    body_exit = _js01_flow_block(
        stmt.body, None, body_flow, json_calls)
    flows = ((flow, body_exit)
             if _sem_loop_body_has_back_edge(stmt.body) else (flow,))
    return _js01_flow_merge(flows)
def _js01_flow_statement(stmt: ast.stmt, flow,
                         json_calls: _JS01Calls):
    bound = _js01_value_binding(stmt)
    if bound is not None:
        names, value = bound
        _js01_apply_namedexprs(value, flow, json_calls)
        if isinstance(stmt, ast.Assign):
            for target in stmt.targets:
                for target_names, target_value in _assignment_value_pairs(
                        target, value):
                    _js01_assign_flow(
                        flow, target_names, target_value, stmt, json_calls)
        else:
            _js01_assign_flow(flow, names, value, stmt, json_calls)
        return flow
    if isinstance(stmt, ast.If):
        body_entry = _js01_test_outcome_flow(
            stmt.test, flow, json_calls, True)
        else_entry = _js01_test_outcome_flow(
            stmt.test, flow, json_calls, False)
        outcomes = []
        if not _sem_block_terminates(stmt.body):
            outcomes.append(_js01_flow_block(
                stmt.body, None, body_entry, json_calls))
        if not _sem_block_terminates(stmt.orelse):
            outcomes.append(_js01_flow_block(
                stmt.orelse, None, else_entry, json_calls))
        return _js01_flow_merge(outcomes)
    if isinstance(stmt, ast.While):
        exit_flow = _js01_while_exit_flow(stmt, flow, json_calls)
        return _js01_flow_block(
            stmt.orelse, None, exit_flow, json_calls)
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        _js01_apply_namedexprs(stmt.iter, flow, json_calls)
        exit_flow = _js01_for_exit_flow(stmt, flow, json_calls)
        return _js01_flow_block(
            stmt.orelse, None, exit_flow, json_calls)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        for item in stmt.items:
            _js01_apply_namedexprs(item.context_expr, flow, json_calls)
            if item.optional_vars is not None:
                _js01_unknown_rebind(
                    flow, list(iter_unpack_target_names(item.optional_vars)))
        return _js01_flow_block(stmt.body, None, flow, json_calls)
    if isinstance(stmt, TRY_NODE_TYPES):
        outcomes = _js01_try_outcome_flows(stmt, flow, json_calls)
        merged = _js01_flow_merge(outcomes)
        return _js01_flow_block(stmt.finalbody, None, merged, json_calls)
    if isinstance(stmt, ast.Match):
        _js01_apply_namedexprs(stmt.subject, flow, json_calls)
        outcomes = []
        remaining = _js01_flow_copy(flow)
        for case in stmt.cases:
            if not _sem_block_terminates(case.body):
                case_flow = _js01_match_case_entry_flow(
                    case, remaining, json_calls)
                outcomes.append(_js01_flow_block(
                    case.body, None, case_flow, json_calls))
            remaining = _js01_match_case_follow_flow(
                case, remaining, json_calls)
            if remaining is None:
                break
        if remaining is not None:
            outcomes.append(remaining)
        return _js01_flow_merge(outcomes)
    if isinstance(stmt, ast.AugAssign):
        for name in iter_unpack_target_names(stmt.target):
            flow[1].discard(name)
        return flow
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        _js01_unknown_rebind(flow, [stmt.name])
        return flow
    names = _plain_rebind_names(stmt)
    if names is not None:
        _js01_unknown_rebind(flow, names)
    if isinstance(stmt, ast.Expr):
        _js01_apply_namedexprs(stmt.value, flow, json_calls)
    return flow
def _js01_for_body_entry_flow(stmt: ast.For | ast.AsyncFor, flow,
                               json_calls: _JS01Calls):
    target_names = list(iter_unpack_target_names(stmt.target))
    first = _js01_flow_copy(flow)
    _js01_unknown_rebind(first, target_names)
    if not _sem_loop_body_has_back_edge(stmt.body):
        return first
    body_exit = _js01_flow_block(
        stmt.body, None, _js01_flow_copy(first), json_calls)
    merged = _js01_flow_merge((first, body_exit))
    _js01_unknown_rebind(merged, target_names)
    return merged
def _js01_while_body_entry_flow(stmt: ast.While, flow,
                                 json_calls: _JS01Calls):
    first_entry = _js01_test_outcome_flow(
        stmt.test, flow, json_calls, True)
    if not _sem_loop_body_has_back_edge(stmt.body):
        return first_entry
    body_exit = _js01_flow_block(
        stmt.body, None, _js01_flow_copy(first_entry), json_calls)
    next_entry = _js01_test_outcome_flow(
        stmt.test, body_exit, json_calls, True)
    return _js01_flow_merge((first_entry, next_entry))
def _js01_flow_before_statement(stmt: ast.stmt, use: ast.AST, flow,
                                json_calls: _JS01Calls):
    if isinstance(stmt, ast.If):
        if in_subtree(use, stmt.test):
            return flow
        in_body = any(in_subtree(use, node) for node in stmt.body)
        branch = stmt.body if in_body else stmt.orelse
        branch_entry = _js01_test_outcome_flow(
            stmt.test, flow, json_calls, in_body)
        return _js01_flow_block(branch, use, branch_entry, json_calls)
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        if in_subtree(use, stmt.iter):
            return flow
        _js01_apply_namedexprs(stmt.iter, flow, json_calls)
        if any(in_subtree(use, node) for node in stmt.body):
            body_entry = _js01_for_body_entry_flow(
                stmt, flow, json_calls)
            return _js01_flow_block(
                stmt.body, use, body_entry, json_calls)
        exit_flow = _js01_for_exit_flow(stmt, flow, json_calls)
        return _js01_flow_block(
            stmt.orelse, use, exit_flow, json_calls)
    if isinstance(stmt, ast.While):
        if in_subtree(use, stmt.test):
            return flow
        if any(in_subtree(use, node) for node in stmt.body):
            body_entry = _js01_while_body_entry_flow(
                stmt, flow, json_calls)
            return _js01_flow_block(
                stmt.body, use, body_entry, json_calls)
        exit_flow = _js01_while_exit_flow(stmt, flow, json_calls)
        return _js01_flow_block(
            stmt.orelse, use, exit_flow, json_calls)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        for item in stmt.items:
            if in_subtree(use, item.context_expr):
                return flow
            _js01_apply_namedexprs(item.context_expr, flow, json_calls)
            if item.optional_vars is not None:
                _js01_unknown_rebind(
                    flow, list(iter_unpack_target_names(item.optional_vars)))
        return _js01_flow_block(stmt.body, use, flow, json_calls)
    if isinstance(stmt, TRY_NODE_TYPES):
        if any(in_subtree(use, node) for node in stmt.body):
            return _js01_flow_block(stmt.body, use, flow, json_calls)
        body = _js01_flow_block(
            stmt.body, None, _js01_flow_copy(flow), json_calls)
        if any(in_subtree(use, node) for node in stmt.orelse):
            return _js01_flow_block(stmt.orelse, use, body, json_calls)
        handler_entry, handler_reachable = _js01_try_handler_entry(
            stmt, flow, json_calls)
        for handler in stmt.handlers:
            if any(in_subtree(use, node) for node in handler.body):
                handler_flow = _js01_flow_copy(handler_entry)
                if handler.name:
                    _js01_unknown_rebind(handler_flow, [handler.name])
                return _js01_flow_block(
                    handler.body, use, handler_flow, json_calls)
        if any(in_subtree(use, node) for node in stmt.finalbody):
            outcomes = _js01_try_outcome_flows(
                stmt, flow, json_calls, include_terminated=True)
            if not _sem_try_has_catch_all(stmt) and handler_reachable:
                outcomes.append(handler_entry)
            merged = _js01_flow_merge(outcomes)
            return _js01_flow_block(
                stmt.finalbody, use, merged, json_calls)
        return flow
    if isinstance(stmt, ast.Match):
        if in_subtree(use, stmt.subject):
            return flow
        _js01_apply_namedexprs(stmt.subject, flow, json_calls)
        remaining = flow
        for case in stmt.cases:
            case_flow = _js01_match_case_entry_flow(
                case, remaining, json_calls, use)
            if case.guard is not None and in_subtree(use, case.guard):
                return case_flow
            if any(in_subtree(use, node) for node in case.body):
                return _js01_flow_block(
                    case.body, use, case_flow, json_calls)
            remaining = _js01_match_case_follow_flow(
                case, remaining, json_calls)
            if remaining is None:
                break
    return flow
def _js01_apply_boolop_prefixes(root: ast.AST, use: ast.AST, flow,
                                json_calls: _JS01Calls) -> None:
    if root is use:
        return
    if isinstance(root, ast.BoolOp):
        for index, value in enumerate(root.values):
            if in_subtree(use, value):
                for previous in root.values[:index]:
                    _js01_apply_namedexprs(previous, flow, json_calls)
                break
    for child in ast.iter_child_nodes(root):
        if in_subtree(use, child):
            _js01_apply_boolop_prefixes(child, use, flow, json_calls)
            return
_JS01_LOOP_NODES = (ast.For, ast.AsyncFor, ast.While)
def _js01_branch_region(parent: ast.AST, node: ast.AST, parents: dict):
    child = _js01_child_toward(parent, node, parents)
    if child is None:
        return None
    if isinstance(parent, ast.If):
        if child in parent.body:
            return "body"
        if child in parent.orelse:
            return "orelse"
    elif isinstance(parent, ast.Match):
        if child in parent.cases:
            return ("case", parent.cases.index(child))
    elif isinstance(parent, TRY_NODE_TYPES):
        for field in ("body", "orelse", "finalbody", "handlers"):
            block = getattr(parent, field, ())
            if child in block:
                if field == "handlers":
                    return (field, block.index(child))
                return field
    return None
def _js01_break_can_reach(loop: ast.AST, cutoff: ast.AST | None,
                          scope: ast.AST, parents: dict) -> bool:
    if cutoff is None:
        return True
    if in_subtree(cutoff, loop):
        return False
    loop_end = (getattr(loop, "end_lineno", None) or loop.lineno,
                getattr(loop, "end_col_offset", None) or 0)
    cutoff_start = (cutoff.lineno, cutoff.col_offset)
    if loop_end > cutoff_start:
        return False
    loop_ancestors: dict[int, ast.AST] = {}
    current: ast.AST | None = loop
    while current is not None:
        loop_ancestors[id(current)] = current
        if current is scope:
            break
        current = parents.get(id(current))
    current = cutoff
    while current is not None and id(current) not in loop_ancestors:
        current = parents.get(id(current))
    if current is None:
        return False
    if isinstance(current, (ast.If, ast.Match, *TRY_NODE_TYPES)):
        return (_js01_branch_region(current, loop, parents)
                == _js01_branch_region(current, cutoff, parents))
    return True
def _js01_loop_breaks_before(scope: ast.AST, cutoff: ast.AST | None,
                             parents: dict) -> list[ast.Break]:
    result: list[ast.Break] = []
    for node in iter_scope_nodes(scope):
        if not isinstance(node, ast.Break):
            continue
        current: ast.AST = node
        loop = None
        while id(current) in parents:
            parent = parents[id(current)]
            if isinstance(parent, _JS01_LOOP_NODES):
                loop = parent
                break
            current = parent
        if (loop is None
                or not _js01_break_can_reach(loop, cutoff, scope, parents)):
            continue
        result.append(node)
    return result
def _js01_reaching_flow(scope: ast.AST, cutoff: ast.AST | None,
                        json_calls: _JS01Calls):
    body = getattr(scope, "body", [])
    if not isinstance(body, list):
        return {}, set()
    flow = _js01_flow_block(body, cutoff, ({}, set()), json_calls)
    if cutoff is not None:
        for stmt in body:
            if in_subtree(cutoff, stmt):
                _js01_apply_boolop_prefixes(stmt, cutoff, flow, json_calls)
                break
    return flow
def _js01_reaching_origins(scope: ast.AST, name: str, cutoff: ast.AST | None,
                           json_calls: _JS01Calls, *,
                           include_loop_breaks: bool = True
                           ) -> frozenset[ast.AST]:
    flow = _js01_reaching_flow(scope, cutoff, json_calls)
    origins = (frozenset() if name in flow[1]
               else flow[0].get(name, frozenset()))
    if not include_loop_breaks:
        return origins
    parents = build_parent_map(scope)
    for break_node in _js01_loop_breaks_before(scope, cutoff, parents):
        break_flow = _js01_reaching_flow(scope, break_node, json_calls)
        current: ast.AST = break_node
        while id(current) in parents:
            parent = parents[id(current)]
            if (isinstance(parent, TRY_NODE_TYPES) and parent.finalbody
                    and not any(in_subtree(break_node, stmt)
                                for stmt in parent.finalbody)):
                break_flow = _js01_flow_block(
                    parent.finalbody, None, break_flow, json_calls)
            if isinstance(parent, _JS01_LOOP_NODES):
                break
            current = parent
        if name not in break_flow[1]:
            origins = origins | break_flow[0].get(name, frozenset())
    return origins
def _js01_type_names(arg: ast.AST) -> set[str] | None:
    if isinstance(arg, ast.Name):
        return {arg.id}
    if isinstance(arg, ast.Tuple):
        names: set[str] = set()
        for elt in arg.elts:
            if not isinstance(elt, ast.Name):
                return None
            names.add(elt.id)
        return names
    return None
def _js01_dict_guard_name(node: ast.AST,
                          resolver: _ModuleCallResolver) -> str:
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "isinstance" and len(node.args) == 2
            and resolver.builtin_name(node, "isinstance")
            and resolver.builtin_name(node, "dict")
            and _js01_type_names(node.args[1]) == {"dict"}):
        return ""
    return _fs01_guarded_name(node.args[0])
def _js01_is_dict_guard(node: ast.AST, name: str,
                        resolver: _ModuleCallResolver) -> bool:
    return _js01_dict_guard_name(node, resolver) == name
def _js01_is_not_dict_guard(node: ast.AST, name: str,
                            resolver: _ModuleCallResolver) -> bool:
    return (isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not)
            and _js01_is_dict_guard(node.operand, name, resolver))
def _js01_atom_branch(test: ast.AST, name: str,
                      resolver: _ModuleCallResolver) -> str | None:
    if _js01_is_dict_guard(test, name, resolver):
        return _GUARD_BODY
    if _js01_is_not_dict_guard(test, name, resolver):
        return _GUARD_ORELSE
    return None
def _js01_path_defends(path: list, name: str,
                       resolver: _ModuleCallResolver) -> bool:
    defended = False
    for test, outcome in path:
        for rebind in _guard_walrus_rebinds(test, name):
            defended = _js01_definitely_dict(rebind.value)
        if _js01_is_dict_guard(test, name, resolver):
            defended = outcome
        elif _js01_is_not_dict_guard(test, name, resolver):
            defended = not outcome
    return defended
def _js01_outcome_defends(test: ast.AST, name: str,
                          resolver: _ModuleCallResolver,
                          outcome: bool) -> bool:
    return all(_js01_path_defends(path, name, resolver)
               for path in _sem_outcome_paths(test, outcome))
def _js01_boolop_defends(use: ast.AST, name: str, parents: dict,
                         resolver: _ModuleCallResolver) -> bool:
    cur = use
    while id(cur) in parents:
        parent = parents[id(cur)]
        if isinstance(parent, ast.BoolOp):
            index = next((i for i, value in enumerate(parent.values)
                          if value is cur), -1)
            if index > 0:
                outcome = isinstance(parent.op, ast.And)
                paths = _sem_fixed_outcome_paths([
                    (value, outcome) for value in parent.values[:index]])
                if all(_js01_path_defends(path, name, resolver)
                       for path in paths):
                    return True
        cur = parent
    return False
def _js01_guard_after_binding(
        guard: ast.AST, binding: ast.AST | None, name: str,
        resolver: _ModuleCallResolver) -> bool:
    if binding is None:
        return False
    test = getattr(guard, "test", None)
    if test is not None and in_subtree(binding, test):
        binding_pos = (binding.lineno, binding.col_offset)
        for node in walk_nodes(test):
            if not _js01_is_dict_guard(node, name, resolver):
                continue
            if in_subtree(binding, node.args[0]):
                return True
            if (node.lineno, node.col_offset) > binding_pos:
                return True
        return False
    safe_branch = (_fold_guard_branches(
        test, name, partial(_js01_atom_branch, resolver=resolver))
                   if test is not None else None)
    if safe_branch is not None:
        safe_nodes = _sem_branch_nodes(guard, safe_branch)
        if any(in_subtree(binding, stmt) for stmt in safe_nodes):
            return False
    if (isinstance(guard, ast.While)
            and any(in_subtree(binding, stmt) for stmt in guard.body)):
        return not loop_body_has_break(guard.body)
    return ((getattr(guard, "lineno", -1), getattr(guard, "col_offset", -1))
            > (getattr(binding, "lineno", -1),
               getattr(binding, "col_offset", -1)))
def _js01_guard_covers(
        guard: ast.AST, name: str, use: ast.AST, parents: dict,
        binding: ast.AST | None, resolver: _ModuleCallResolver) -> bool:
    safe_branch = partial(
        _fold_guard_branches,
        atom=partial(_js01_atom_branch, resolver=resolver))
    branch = _fold_guard_branches(guard.test, name, partial(
        _js01_atom_branch, resolver=resolver))
    return (_js01_guard_after_binding(
                guard, binding, name, resolver)
            and branch is not None
            and _js01_outcome_defends(
                guard.test, name, resolver, branch == _GUARD_BODY)
            and _guard_protects(
                guard, use, name, parents, safe_branch,
                repair_ok=_js01_definitely_dict)
            and not _rebind_between_guard_and_use(
                guard, name, use, parents, _js01_definitely_dict))
def _js01_use_defended(name: str, use: ast.AST, scope: ast.AST,
                       parents: dict, binding: ast.AST | None,
                       resolver: _ModuleCallResolver) -> bool:
    if _js01_boolop_defends(use, name, parents, resolver):
        return True
    return any(isinstance(guard, _FS01_TEST_CONTAINERS)
               and _js01_guard_covers(
                   guard, name, use, parents, binding, resolver)
               for guard in iter_scope_nodes(scope))
def _js01_child_toward(ancestor: ast.AST, node: ast.AST,
                       parents: dict) -> ast.AST | None:
    cur = node
    while cur is not None:
        parent = parents.get(id(cur))
        if parent is ancestor:
            return cur
        cur = parent
    return None
def _js01_scope_entry(scope: ast.AST, node: ast.AST,
                      parents: dict) -> ast.AST | None:
    chain = scope_chain(node, parents)
    for index, outer in enumerate(chain):
        if outer is scope:
            return chain[index - 1] if index else None
    return _js01_child_toward(scope, node, parents)
def _scope_name_declaration(scope: ast.AST, name: str) -> str:
    for candidate in iter_scope_nodes(scope):
        if isinstance(candidate, ast.Global) and name in candidate.names:
            return "global"
        if isinstance(candidate, ast.Nonlocal) and name in candidate.names:
            return "nonlocal"
    return ""
def _scope_binds_name(scope: ast.AST, name: str) -> bool:
    if name in collect_param_names(scope):
        return True
    for candidate in iter_scope_nodes(scope):
        if (isinstance(candidate, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.ClassDef))
                and candidate.name == name):
            return True
        if (isinstance(candidate, ast.Match)
                and any(name in iter_pattern_capture_names(case.pattern)
                        for case in candidate.cases)):
            return True
        if (isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.Lambda))
                and isinstance(candidate, ast.AnnAssign)
                and isinstance(candidate.target, ast.Name)
                and candidate.target.id == name):
            return True
        bound = _js01_value_binding(candidate)
        if bound is not None and name in bound[0]:
            return True
        names = _plain_rebind_names(candidate)
        if names is not None and name in names:
            return True
    return False
def _js01_outer_undefended_origins(
        name: str, node: ast.AST, scope: ast.AST, parents: dict,
        json_calls: _JS01Calls, resolver: _ModuleCallResolver,
        ) -> frozenset[ast.AST]:
    if (_scope_binds_name(scope, name)
            and not _in_definition_time_face(scope, node)):
        return frozenset()
    for binding_scope in scope_chain(node, parents)[1:]:
        if not _scope_binds_name(binding_scope, name):
            continue
        cutoff = _js01_scope_entry(binding_scope, node, parents)
        origins = _js01_reaching_origins(
            binding_scope, name, cutoff, json_calls)
        if cutoff is not None:
            origins = frozenset(origins) | _js01_reaching_origins(
                binding_scope, name, None, json_calls)
        return frozenset(origin for origin in origins
                         if not _js01_use_defended_in_chain(
                             name, node, binding_scope, parents,
                             origin, resolver))
    return frozenset()
def _js01_use_defended_in_chain(name: str, use: ast.AST, binding_scope: ast.AST,
                                parents: dict, binding: ast.AST | None,
                                resolver: _ModuleCallResolver) -> bool:
    if _js01_boolop_defends(use, name, parents, resolver):
        return True
    for scope in scope_chain(use, parents):
        if any(isinstance(guard, _FS01_TEST_CONTAINERS)
               and _js01_guard_covers(
                   guard, name, use, parents, binding, resolver)
               for guard in iter_scope_nodes(scope)):
            return True
        if scope is binding_scope:
            break
    return False
def _plain_rebind_names(node: ast.AST) -> list[str] | None:
    if isinstance(node, ast.Delete):
        return [name for target in node.targets
                for name in iter_unpack_target_names(target)]
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return list(iter_unpack_target_names(node.target))
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return _js01_with_target_names(node)
    if isinstance(node, ast.ExceptHandler):
        return [node.name] if node.name else []
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return _import_bound_names(node)
    if isinstance(node, ast.AugAssign):
        return list(iter_unpack_target_names(node.target))
    return None
def _js01_with_target_names(node: ast.AST) -> list[str]:
    return [name for item in node.items if item.optional_vars is not None
            for name in iter_unpack_target_names(item.optional_vars)]
def _import_bound_names(node: ast.AST) -> list[str]:
    return [alias.asname or alias.name.split(".")[0]
            for alias in node.names if alias.name != "*"]
def _js01_value_binding(node: ast.AST) -> tuple[list[str], ast.expr] | None:
    if isinstance(node, ast.Assign):
        return list(iter_unpack_target_names(node.targets)), node.value
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        names = [node.target.id] if isinstance(node.target, ast.Name) else []
        return names, node.value
    if isinstance(node, ast.NamedExpr):
        return [node.target.id], node.value
    return None
def _js01_name_use_finding(
        node: ast.AST, name: str, description: str, filepath: str,
        json_calls: _JS01Calls, scope: ast.AST, parents: dict,
        resolver: _ModuleCallResolver,
        reported: set[tuple[str, frozenset[ast.AST]]],
        ) -> DiagnoseFinding | None:
    origins = _js01_reaching_origins(scope, name, node, json_calls)
    if origins:
        undefended = frozenset(origin for origin in origins
                               if not _js01_use_defended(
                                   name, node, scope, parents,
                                   origin, resolver))
    elif (not _scope_binds_name(scope, name)
          or _in_definition_time_face(scope, node)):
        undefended = _js01_outer_undefended_origins(
            name, node, scope, parents, json_calls, resolver)
    else:
        undefended = frozenset()
    report_key = (name, undefended)
    if undefended and report_key not in reported:
        reported.add(report_key)
        return _js01_finding(node.lineno, filepath, description)
    return None
def _js01_finding(line: int, filepath: str,
                  description: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="JS-01", severity="P1", dimension="robust",
        file=filepath, line=line,
        description=description, suggestion=_JS01_FIX)
def _js01_direct_method_finding(
        node: ast.AST, filepath: str,
        json_calls: _JS01Calls) -> DiagnoseFinding | None:
    if (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _JS01_DICT_METHODS
            and _js01_json_flows(
                node.func.value, json_calls, frozenset())):
        return _js01_finding(
            node.lineno, filepath,
            "json.loads 结果未做形状防御直接调用 ."
            + node.func.attr + "()（标量/列表输入即崩）")
    return None
def _js01_subscript_finding(
        node: ast.AST, filepath: str, json_calls: _JS01Calls,
        scope: ast.AST, parents: dict, resolver: _ModuleCallResolver,
        reported: set[tuple[str, frozenset[ast.AST]]],
        ) -> DiagnoseFinding | None:
    if not isinstance(node, ast.Subscript):
        return None
    _key = _js01_string_key(node.slice)
    if _key is None:
        return None
    if _js01_json_flows(node.value, json_calls, frozenset()):
        return _js01_finding(
            node.lineno, filepath,
            "json.loads 结果直接下标访问"
            f"[{_key!r}] 未做形状防御"
            "（标量/列表输入即 TypeError）")
    v = node.value
    if not isinstance(v, ast.Name):
        return None
    return _js01_name_use_finding(
        node, v.id,
        f"json 解析结果 {v.id}[{_key!r}] 未做 dict 形状防御"
        "（病态输入即 TypeError）",
        filepath, json_calls, scope, parents, resolver, reported)
def _js01_string_key(slice_node: ast.AST) -> str | None:
    if (isinstance(slice_node, ast.Constant)
            and isinstance(slice_node.value, str)):
        return slice_node.value
    return None
def _js01_bound_method_finding(
        node: ast.AST, filepath: str, json_calls: _JS01Calls,
        scope: ast.AST, parents: dict, resolver: _ModuleCallResolver,
        reported: set[tuple[str, frozenset[ast.AST]]],
        ) -> DiagnoseFinding | None:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _JS01_DICT_METHODS
            and isinstance(node.func.value, ast.Name)):
        return None
    v = node.func.value
    return _js01_name_use_finding(
        node, v.id,
        (f"json 解析结果 {v.id}.{node.func.attr}() "
         "未做 dict 形状防御（标量输入即 AttributeError）"),
        filepath, json_calls, scope, parents, resolver, reported)
def check_JS01(tree: ast.AST, source_lines: list[str], filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseFinding]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    scopes = scope_roots(tree)
    parents = build_parent_map(tree)
    resolver = _ModuleCallResolver(tree)
    json_calls = _JS01FlowContext(
        frozenset(
            id(node) for node in walk_nodes(tree)
            if resolver.canonical_name(node, "json") in _JS01_JSON_FACTORY),
        resolver)
    for scope in scopes:
        reported: set[tuple[str, frozenset[ast.AST]]] = set()
        for node in iter_scope_nodes(scope):
            finding = _js01_direct_method_finding(
                node, filepath, json_calls)
            if finding is None:
                finding = _js01_subscript_finding(
                    node, filepath, json_calls, scope, parents,
                    resolver, reported)
            if finding is None:
                finding = _js01_bound_method_finding(
                    node, filepath, json_calls, scope, parents,
                    resolver, reported)
            if finding is not None:
                issues.append(finding)
    return issues
_GUARD_IN_TEST = "in_test"
_GUARD_OUTSIDE = "outside"
def _guard_is_not_param(test: Any, param_name: str) -> bool:
    return (isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not)
            and isinstance(test.operand, ast.Name)
            and test.operand.id == param_name)
def _frame_subtree_contains(root: Any, target: Any) -> bool:
    stack: list[ast.AST] = [root]
    while stack:
        n = stack.pop()
        if n is target:
            return True
        if isinstance(n, FRAME_BOUNDARY_NODES):
            continue
        stack.extend(ast.iter_child_nodes(n))
    return False
def _guard_tests_param(test: Any, param_name: str) -> bool:
    return any(isinstance(_sub, ast.Name) and _sub.id == param_name
               for _sub in walk_nodes(test))
def _guard_call_placement(stmt: Any, call_node: Any) -> str:
    if _frame_subtree_contains(stmt.test, call_node):
        return _GUARD_IN_TEST
    if any(_frame_subtree_contains(branch, call_node) for branch in stmt.body):
        return _GUARD_BODY
    if any(_frame_subtree_contains(branch, call_node)
           for branch in stmt.orelse):
        return _GUARD_ORELSE
    return _GUARD_OUTSIDE
_FACET_NONE = "none"
_FACET_BLANK = "blank"
_EMPTY_FACETS = frozenset({_FACET_NONE, _FACET_BLANK})
def _guard_statement_protects(stmt: ast.AST, call_node: Any,
                              param_name: str, parents: dict,
                              required: frozenset[str] = _EMPTY_FACETS) -> bool:
    protected = False
    if isinstance(stmt, (ast.If, ast.While)):
        if _guard_tests_param(stmt.test, param_name):
            placement = _guard_call_placement(stmt, call_node)
            protected = _guard_placement_protects(
                stmt, placement, call_node, param_name, parents, required)
    elif isinstance(stmt, ast.Assert):
        protected = _guard_assert_protects(
            stmt, call_node, param_name, parents, required)
    elif isinstance(stmt, ast.IfExp):
        protected = _guard_ifexp_protects(stmt, call_node, param_name, required)
    elif isinstance(stmt, ast.BoolOp):
        protected = _guard_boolop_protects(stmt, call_node, param_name, required)
    return protected and not _rebind_between_guard_and_use(
        stmt, param_name, call_node, parents, _js03_is_valid_json_text)
def _is_param_guarded(func_node: Any, param_name: str, call_node: Any,
                      all_funcs: list, parents: dict | None = None,
                      required: frozenset[str] = _EMPTY_FACETS) -> bool:
    if parents is None:
        parents = build_parent_map(func_node)
    for scope in _js03_containing_funcs(all_funcs, call_node):
        body = getattr(scope, 'body', None)
        roots = body if isinstance(body, list) else (
            [body] if isinstance(body, ast.AST) else [])
        if any(_guard_statement_protects(
                stmt, call_node, param_name, parents, required)
               for stmt in iter_frame_nodes(roots)):
            return True
        if scope is func_node:
            break
    return False
def _guard_ifexp_protects(expr: ast.IfExp, call_node: Any,
                          param_name: str,
                          required: frozenset[str] = _EMPTY_FACETS) -> bool:
    if not _guard_tests_param(expr.test, param_name):
        return False
    if _frame_subtree_contains(expr.body, call_node):
        in_orelse = False
    elif _frame_subtree_contains(expr.orelse, call_node):
        in_orelse = True
    else:
        return False
    return _guard_branch_protects_by_facet(
        expr.test, param_name, in_orelse, required)
def _guard_boolop_protects(expr: ast.BoolOp, call_node: Any,
                           param_name: str,
                           required: frozenset[str] = _EMPTY_FACETS) -> bool:
    _or_side = isinstance(expr.op, ast.Or)
    for _idx, _value in enumerate(expr.values):
        if _idx == 0 or not _frame_subtree_contains(_value, call_node):
            continue
        if _guard_short_circuit_protects(
                expr.values[:_idx], param_name, _or_side, required):
            return True
    return False
def _guard_path_exclusions(path: list, param_name: str) -> frozenset[str]:
    excluded: frozenset[str] = frozenset()
    for test, outcome in path:
        for rebind in _guard_walrus_rebinds(test, param_name):
            excluded = (_EMPTY_FACETS
                        if _js03_is_valid_json_text(rebind.value)
                        else frozenset())
        excluded_true, excluded_false = _guard_empty_facet_atom(
            test, param_name)
        excluded = excluded | (excluded_true if outcome else excluded_false)
    return excluded
def _guard_outcome_exclusions(test: Any, param_name: str,
                              outcome: bool) -> frozenset[str]:
    states = [_guard_path_exclusions(path, param_name)
              for path in _sem_outcome_paths(test, outcome)]
    return _facet_intersection(states)
def _guard_empty_facets(test: Any, param_name: str
                        ) -> tuple[frozenset[str], frozenset[str]]:
    return (_guard_outcome_exclusions(test, param_name, True),
            _guard_outcome_exclusions(test, param_name, False))
def _facet_intersection(sets: list[frozenset[str]]) -> frozenset[str]:
    if not sets:
        return frozenset()
    merged = sets[0]
    for item in sets[1:]:
        merged = merged & item
    return merged
def _guard_empty_facet_atom(test: Any, param_name: str
                            ) -> tuple[frozenset[str], frozenset[str]]:
    if isinstance(test, ast.Name) and test.id == param_name:
        return _EMPTY_FACETS, frozenset()
    if _guard_is_not_param(test, param_name):
        return frozenset(), _EMPTY_FACETS
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        left, right = test.left, test.comparators[0]
        if isinstance(left, ast.Name) and left.id == param_name:
            return _guard_compare_facets(test.ops[0], right)
        if isinstance(right, ast.Name) and right.id == param_name:
            return _guard_compare_facets(test.ops[0], left)
    return frozenset(), frozenset()
def _guard_compare_facets(op: Any, comparator: Any
                          ) -> tuple[frozenset[str], frozenset[str]]:
    if not isinstance(comparator, ast.Constant):
        return frozenset(), frozenset()
    if comparator.value is None:
        facet = _FACET_NONE
    elif isinstance(comparator.value, (str, bytes)) and not comparator.value:
        facet = _FACET_BLANK
    else:
        return frozenset(), frozenset()
    other = _EMPTY_FACETS - {facet}
    if isinstance(op, (ast.Is, ast.Eq)):
        return other, frozenset({facet})
    if isinstance(op, (ast.IsNot, ast.NotEq)):
        return frozenset({facet}), other
    return frozenset(), frozenset()
def _guard_branch_excluded_facets(
        test: Any, param_name: str,
        in_orelse: bool) -> frozenset[str]:
    excluded_true, excluded_false = _guard_empty_facets(test, param_name)
    return excluded_false if in_orelse else excluded_true
def _guard_branch_protects_by_facet(test: Any, param_name: str,
                                    in_orelse: bool,
                                    required: frozenset[str] = _EMPTY_FACETS,
                                    ) -> bool:
    excluded = _guard_branch_excluded_facets(test, param_name, in_orelse)
    return required <= excluded
def _guard_walrus_rebinds(test: ast.AST, param_name: str) -> list[ast.NamedExpr]:
    found: list[ast.NamedExpr] = []
    stack = [test]
    while stack:
        current = stack.pop()
        if isinstance(current, FRAME_BOUNDARY_NODES):
            continue
        if (isinstance(current, ast.NamedExpr)
                and isinstance(current.target, ast.Name)
                and current.target.id == param_name):
            found.append(current)
        stack.extend(ast.iter_child_nodes(current))
    return sorted(found, key=lambda node: (node.lineno, node.col_offset))
def _guard_short_circuit_protects(previous: list, param_name: str,
                                  or_side: bool,
                                  required: frozenset[str] = _EMPTY_FACETS,
                                  ) -> bool:
    paths = _sem_fixed_outcome_paths([
        (test, not or_side) for test in previous])
    return all(required <= _guard_path_exclusions(path, param_name)
               for path in paths)
def _guard_assert_protects(stmt: ast.Assert, call_node: Any,
                           param_name: str, parents: dict,
                           required: frozenset[str] = _EMPTY_FACETS) -> bool:
    if not _guard_tests_param(stmt.test, param_name):
        return False
    if _frame_subtree_contains(stmt.test, call_node):
        return False
    if not _guard_branch_protects_by_facet(
            stmt.test, param_name, False, required):
        return False
    return _sem_after_in_block(stmt, call_node, parents)
def _guard_outside_protects(stmt: Any, call_node: Any, param_name: str,
                            parents: dict,
                            required: frozenset[str] = _EMPTY_FACETS) -> bool:
    if isinstance(stmt, ast.While):
        if loop_body_has_break(stmt.body):
            return False
        _excluded_true, excluded_false = _guard_empty_facets(
            stmt.test, param_name)
        return (required <= excluded_false
                and _sem_after_in_block(stmt, call_node, parents))
    if not isinstance(stmt, ast.If):
        return False
    excluded_true, excluded_false = _guard_empty_facets(stmt.test, param_name)
    if required <= excluded_true:
        unsafe_nodes = stmt.orelse
    elif required <= excluded_false:
        unsafe_nodes = stmt.body
    else:
        return False
    return ((_sem_block_terminates(unsafe_nodes)
             or _branch_repairs_param(
                 unsafe_nodes, param_name, _js03_is_valid_json_text))
            and _sem_after_in_block(stmt, call_node, parents))
def _guard_placement_protects(stmt: Any, placement: str, call_node: Any,
                              param_name: str, parents: dict,
                              required: frozenset[str] = _EMPTY_FACETS) -> bool:
    if placement == _GUARD_IN_TEST:
        return False
    if placement == _GUARD_OUTSIDE:
        return _guard_outside_protects(
            stmt, call_node, param_name, parents, required)
    return _guard_branch_protects_by_facet(
        stmt.test, param_name, placement == _GUARD_ORELSE, required)
def _js03_collect_empty_params(tree: Any) -> tuple[list, list]:
    empty_params: list[tuple[str, Any, frozenset[str]]] = []
    all_funcs: list = []
    for _fn in walk_nodes(tree):
        if isinstance(_fn, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            all_funcs.append(_fn)
            empty_params.extend(
                (_name, _fn, _required)
                for _name, _required in _js03_empty_default_names(_fn.args))
    return empty_params, all_funcs
def _js03_empty_input_kind(node: Any) -> str | None:
    if not isinstance(node, ast.Constant):
        return None
    if node.value is None:
        return "none"
    if isinstance(node.value, (str, bytes)) and not node.value:
        return "empty"
    return None
def _js03_is_valid_json_text(node: Any) -> bool:
    if not (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and node.value):
        return False
    try:
        json.loads(node.value)
    except (json.JSONDecodeError, UnicodeDecodeError, RecursionError):  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return False
    return True
def _js03_required_facets(kind: str | None) -> frozenset[str]:
    """空值形态 → 该形参必须被守卫排除的空值面。"""
    if kind == "none":
        return frozenset({_FACET_NONE})
    if kind == "empty":
        return frozenset({_FACET_BLANK})
    return _EMPTY_FACETS
def _js03_empty_default_names(
        args: ast.arguments,
) -> list[tuple[str, frozenset[str]]]:
    """返回 ``(形参名, 必须被守卫排除的空值面)``。

    默认值为 ``None`` 时只需排除 ``none`` 面；默认值为空字符串/空字节串时
    只需排除 ``blank`` 面。守卫是否成立必须按该形参实际的空值面判定，
    不能一律要求两个面都被排除（那会把 ``if s is None: ...`` 这类
    正确守卫误判为未防护）。
    """
    _pos_args = list(args.posonlyargs) + list(args.args)
    _offset = len(_pos_args) - len(args.defaults)
    pairs: list[tuple[str, frozenset[str]]] = []
    for _i, _default in enumerate(args.defaults):
        _kind = _js03_empty_input_kind(_default)
        if _kind is not None:
            pairs.append((_pos_args[_offset + _i].arg,
                          _js03_required_facets(_kind)))
    for _arg, _default in zip(args.kwonlyargs, args.kw_defaults, strict=True):
        _kind = _js03_empty_input_kind(_default)
        if _kind is not None:
            pairs.append((_arg.arg, _js03_required_facets(_kind)))
    return pairs
def _node_span(node: ast.AST) -> tuple[tuple[int, int], tuple[int, int]]:
    return ((node.lineno, node.col_offset),
            (getattr(node, "end_lineno", None) or node.lineno,
             getattr(node, "end_col_offset", None) or 0))
def _span_contains(outer: ast.AST, inner: ast.AST) -> bool:
    outer_start, outer_end = _node_span(outer)
    inner_start, inner_end = _node_span(inner)
    return outer_start <= inner_start and inner_end <= outer_end
def _js03_containing_funcs(all_funcs: list, node: ast.Call) -> list:
    contained = []
    for candidate in all_funcs:
        if not _span_contains(candidate, node):
            continue
        start, end = _node_span(candidate)
        span = (end[0] - start[0], end[1] - start[1])
        contained.append((span, candidate))
    return [candidate for _span, candidate in sorted(
        contained, key=lambda item: item[0])]
def _js03_find_defining_func(all_funcs: list, node: ast.Call,
                             arg_id: str) -> Any:
    for candidate in _js03_containing_funcs(all_funcs, node):
        if _in_definition_time_face(candidate, node):
            continue
        declaration = _scope_name_declaration(candidate, arg_id)
        if declaration == "global":
            return None
        if declaration == "nonlocal":
            continue
        if _scope_binds_name(candidate, arg_id):
            return candidate
    return None
def _js03_loads_first_arg(node: ast.Call) -> ast.AST | None:
    if node.args:
        return node.args[0]
    _kw = next((k for k in node.keywords if k.arg == 's'), None)
    return _kw.value if _kw is not None else None
def _js03_is_unguarded_empty_param(node: ast.Call, arg_id: str,
                                  all_funcs: list,
                                  empty_params: list) -> bool:
    _defining = _js03_find_defining_func(all_funcs, node, arg_id)
    if _defining is None:
        return False
    for _pname, _fnode, _required in empty_params:
        if _pname != arg_id or _fnode is not _defining:
            continue
        parents = build_parent_map(_fnode)
        if not _rebind_between_guard_and_use(
                _fnode, _pname, node, parents, _js03_is_valid_json_text,
                initially_valid=False):
            # 入口到调用点的每条路径都已把形参改绑为合法非空 JSON 文本，
            # 默认值不再流入调用。
            return False
        return not _is_param_guarded(
            _fnode, _pname, node, all_funcs, parents, _required)
    return False
_JS03_RULE = {
    "rule_id": "JS-03", "severity": "P2", "dimension": "json_safety",
    "rule_ref": "json-empty-string"}
def _js03_report(issues: list[dict[str, Any]], node: ast.Call,
                 source_lines: list[str], filepath: str,
                 title: str, description: str) -> None:
    issues.append(build_ast_issue(
        _JS03_RULE, source_lines, filepath, node, title, description,
        "根因: json.loads 的入参可能为 None、空字符串或空字节串, "
        "None 会抛 TypeError，空字符串或空字节串会抛 JSONDecodeError。\n"
        "修复策略: 调用前加空值守卫 "
        "(if data: result = json.loads(data) else: result = {}), "
        "或把形参默认值改为合法 JSON 文本 '{}'.\n"
        "参考标准: PEP 8 / json 模块 / JSONDecodeError"))
def check_JS03(tree: ast.AST, source_lines: list[str],
               filepath: str = _DEFAULT_FILEPATH) -> list[dict[str, Any]]:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_JS03 执行")
    issues: list[dict[str, Any]] = []
    if tree is None:
        return issues
    _empty_params, _all_funcs = _js03_collect_empty_params(tree)
    resolver = _ModuleCallResolver(tree)
    json_loads_calls = frozenset(
        id(node) for node in walk_nodes(tree)
        if resolver.canonical_name(node, "json") == "json.loads")
    for node in walk_nodes(tree):
        violation = _js03_violation(
            node, _all_funcs, _empty_params, json_loads_calls)
        if violation is None:
            continue
        title, description = violation
        _js03_report(issues, node, source_lines, filepath, title, description)
    return issues
def _js03_violation(node: Any, all_funcs: list,
                    empty_params: list,
                    json_loads_calls: frozenset[int]) -> tuple[str, str] | None:
    if id(node) not in json_loads_calls:
        return None
    arg = _js03_loads_first_arg(node)
    if arg is None:
        return None
    empty_kind = _js03_empty_input_kind(arg)
    if empty_kind == "none":
        return ("json.loads(None) 会抛出异常",
                "None 不是合法 JSON 入参，json.loads(None) 会抛出 TypeError.")
    if empty_kind == "empty":
        literal = repr(arg.value)
        return (f"json.loads({literal}) 会抛出异常",
                (f"空字符串或空字节串不是合法 JSON 入参，"
                 f"json.loads({literal}) 会抛出 JSONDecodeError."))
    if (isinstance(arg, ast.Name)
            and _js03_is_unguarded_empty_param(
                node, arg.id, all_funcs, empty_params)):
        return (f"json.loads({arg.id}) 参数可能为 None/空字符串/空字节串",
                ("参数默认值为 None、空字符串或空字节串,未做空值守卫直接传入"
                 "json.loads,分别会抛出 TypeError/JSONDecodeError."))
    return None
def wiring_declarations() -> dict:
    return {"catalogs": {
        "aicoder_direct": {"JS-01": check_JS01},
        "traps_bindings": {
            "FS01": check_FS01, "TP07": check_TP07, "JS01": check_JS01,
        },
        "rule_bindings": {"JS03": check_JS03},
    }}

from __future__ import annotations

import ast
import logging
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    block_may_fall_through,
    dotted_name,
    is_subscript_of,
    iter_loop_frame_nodes,
    loop_body_has_break,
    module_postpones_annotations,
    node_position,
    recv_name,
    resolve_import_binding,
)
from jwsgj.diag_shared_ast_views import (
    call_scope_map,
    collect_lexical_scope_table,
    definition_time_expressions,
    parent_map,
    same_scope_bfs_nodes,
    scope_import_tables,
    scope_node_bound_names,
    scope_shadows_import,
    tree_nodes,
)
from jwsgj.diag_types_defs import (
    DiagnoseIssue,
)
from jwsgj.diag_types_vocab import (
    DiagnoseSeverity,
)
from jwsgj.prevention_scope_facts import walk_nodes

_log = logging.getLogger(__name__)
_DEFAULT_SOURCE_LINES: list[str] | None = None
_DEFAULT_FILEPATH = ''
__all__ = [
    'GATE_DETECTORS',
    'detect_b07_modify_iterable_during_loop',
    'detect_b09_string_concat_in_loop',
    'detect_b17_iterator_reuse',
    'detect_b29_range_len_antipattern',
    'detect_b32_dict_modify_during_iter',
    'detect_b37_lazy_iterator_subscript',
    'detect_b39_len_of_lazy_iterator',
    'detect_b66_next_invalid_iterator',
    'detect_b68_while_true_no_exit',
]
_log.info("diag_gate_loop B 系列循环语义域已加载: %d 项导出", len(__all__))
def _finish(check_id: str, detector: str, issues: list,
            filepath: str) -> list[DiagnoseIssue]:
    if issues:
        _log.debug("[%s] %s 命中 %d 处: %s", check_id, detector,
                   len(issues), filepath)
    return issues
def _error_issue(check_id: str, message: str, line: int, suggestion: str) -> DiagnoseIssue:
    return DiagnoseIssue(
        check_id=check_id, severity=DiagnoseSeverity.ERROR,
        message=message, line=line,
        suggestion=suggestion, auto_fixable=False,
    )
def _warn_issue(check_id: str, message: str, line: int, suggestion: str) -> DiagnoseIssue:
    return DiagnoseIssue(
        check_id=check_id, severity=DiagnoseSeverity.WARN, message=message,
        line=line, suggestion=suggestion, auto_fixable=False)
_ForNode = ast.For | ast.AsyncFor
_FOR_NODES = (ast.For, ast.AsyncFor)
_LOOP_NODES = (*_FOR_NODES, ast.While)
def _named_call(node: ast.AST, names: frozenset[str] | set[str]) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in names)
class _LoopBindings:
    def __init__(self, tree: ast.Module) -> None:
        self.table = collect_lexical_scope_table(tree)
        self.call_scopes = call_scope_map(self.table)
        self.imports = scope_import_tables(tree)
        self.parents = parent_map(tree)
    def is_builtin(self, node: ast.AST, names: frozenset[str]) -> bool:
        if not _named_call(node, names):
            return False
        name = node.func.id
        scope = self.call_scopes.get(id(node))
        return bool(
            scope is not None
            and not scope_shadows_import(self.table, scope, name)
            and resolve_import_binding(
                self.imports, self.parents, node, name) is None)
def _loop_builtin_call(node: ast.AST, names: frozenset[str],
                       bindings: _LoopBindings | None) -> bool:
    if not _named_call(node, names):
        return False
    return bindings is None or bindings.is_builtin(node, names)
_B07_BRANCH_BLOCK_NODES = (ast.ExceptHandler, ast.match_case)
_B07_SCOPE_BOUNDARY_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
)
_ITER_MODIFY_METHODS = frozenset({
    'append', 'remove', 'pop', 'insert', 'extend', 'clear', 'sort', 'reverse',
    'difference_update', 'intersection_update', 'symmetric_difference_update',
})
_B32_SIZE_MESSAGE_TEMPLATES = {
    'update': "遍历时更新容器: for 迭代 '{iter_name}' 时调用 .update() 会触发 RuntimeError（dict/set 大小改变）",
    'add': "遍历时修改集合: for 迭代 '{iter_name}' 时调用 .add() 会触发 RuntimeError（集合大小改变）",
    'discard': "遍历时修改集合: for 迭代 '{iter_name}' 时调用 .discard() 会触发 RuntimeError（集合大小改变）",
    'popitem': "遍历时删除元素: for 迭代 '{iter_name}' 时调用 .popitem() 会触发 RuntimeError（字典大小改变）",
    'setdefault': "遍历时插入键: for 迭代 '{iter_name}' 时调用 .setdefault() 新增键会触发 RuntimeError（字典大小改变）",
}
_B32_SIZE_METHODS = frozenset(_B32_SIZE_MESSAGE_TEMPLATES)
_B32_SIZE_NEUTRAL_METHODS = frozenset({'add', 'setdefault'})
_MUTATOR_METHODS = _ITER_MODIFY_METHODS | _B32_SIZE_METHODS
_ITER_VIEW_METHODS = frozenset({'items', 'keys', 'values'})
_ITER_COPY_CONSTRUCTORS = frozenset({'list', 'tuple', 'set', 'sorted'})
_ELEMENT_PRESERVING_FACTORIES = frozenset({'iter', 'reversed', 'filter'})
_OPAQUE_ITER_FACTORIES = frozenset({'zip', 'map'})
_LOOP_TRY_NODES = (ast.Try, ast.TryStar) if hasattr(ast, 'TryStar') else (ast.Try,)
_LOOP_EXIT_OR_CALL_NODES = (
    ast.Return, ast.Raise, ast.Yield, ast.YieldFrom, ast.Await, ast.Call,
)
def _module_annotations_evaluated(tree: ast.Module) -> bool:
    return not module_postpones_annotations(tree, require_absolute=True)
def _evaluated_definition_expressions(
        node: ast.AST, annotations_evaluated: bool = True) -> list[ast.AST]:
    lazy: set[int] = set()
    for type_param in getattr(node, 'type_params', None) or ():
        for attr in ('bound', 'default'):
            value = getattr(type_param, attr, None)
            if value is not None:
                lazy.add(id(value))
    return [expr for expr in definition_time_expressions(
        node, annotations_evaluated=annotations_evaluated)
            if id(expr) not in lazy]
def _immediate_execution_nodes(
        roots, *, enter_class_bodies: bool,
        annotations_evaluated: bool = True) -> list[ast.AST]:
    stack = list(reversed(list(roots)))
    out: list[ast.AST] = []
    while stack:
        node = stack.pop()
        out.append(node)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            children = _evaluated_definition_expressions(
                node, annotations_evaluated)
        elif isinstance(node, ast.ClassDef):
            children = _evaluated_definition_expressions(
                node, annotations_evaluated)
            if enter_class_bodies:
                children = [*children, *node.body]
        else:
            children = list(ast.iter_child_nodes(node))
        stack.extend(reversed(children))
    return out
def _execution_scope_nodes(
        scope: ast.AST, annotations_evaluated: bool = True) -> list[ast.AST]:
    body = getattr(scope, 'body', ())
    roots = body if isinstance(body, list) else (body,)
    return _immediate_execution_nodes(
        roots, enter_class_bodies=False,
        annotations_evaluated=annotations_evaluated)
def _iter_loop_groups(tree: ast.Module, bindings: _LoopBindings):
    annotations_evaluated = _module_annotations_evaluated(tree)
    for node in tree_nodes(tree):
        if not isinstance(node, _FOR_NODES):
            continue
        iter_names = _extract_iter_names(node.iter, bindings)
        if iter_names:
            yield node, iter_names, _immediate_execution_nodes(
                node.body, enter_class_bodies=True,
                annotations_evaluated=annotations_evaluated)
def _append_hit(issues: list[DiagnoseIssue], seen: set[tuple[str, int]],
                iter_name: str, sub: ast.AST,
                issue: DiagnoseIssue | None) -> None:
    if issue is None:
        return
    key = (iter_name, sub.lineno)
    if key not in seen:
        seen.add(key)
        issues.append(issue)
def _b07_is_materialized_iter(
        iter_node: ast.AST, bindings: _LoopBindings | None) -> bool:
    if isinstance(iter_node, ast.Subscript) and isinstance(iter_node.slice, ast.Slice):
        return True
    return _loop_builtin_call(
        iter_node, _ITER_COPY_CONSTRUCTORS | {'range', 'dict', 'frozenset'},
        bindings)
def _b07_is_mutation_node(node: ast.AST) -> bool:
    if isinstance(node, ast.Call):
        return True
    if isinstance(node, ast.AugAssign):
        return True
    return isinstance(node, ast.Subscript) and isinstance(node.ctx, ast.Store)
def _b07_mutation_ids_in(stmt: ast.AST) -> set[int]:
    return {
        id(node)
        for node in _immediate_execution_nodes(
            [stmt], enter_class_bodies=True)
        if _b07_is_mutation_node(node)
    }
def _b07_stmt_reaches_own_continue(stmt: ast.AST) -> bool:
    stack = [stmt]
    while stack:
        node = stack.pop()
        if isinstance(node, _LOOP_NODES):
            stack.extend(getattr(node, 'orelse', ()))
            continue
        if isinstance(node, ast.Continue):
            return True
        stack.extend(ast.iter_child_nodes(node))
    return False
def _break_exits_loop(break_stmt: ast.Break, loop_node: _ForNode,
                      parent_of: dict[ast.AST, ast.AST]) -> bool:
    child: ast.AST = break_stmt
    cur = parent_of.get(child)
    while cur is not None and cur is not loop_node:
        if isinstance(cur, _LOOP_NODES) and child not in cur.orelse:
            return False
        child = cur
        cur = parent_of.get(cur)
    return cur is loop_node
def _b07_finally_exits_loop(
        stmt: ast.AST, loop_node: _ForNode,
        parent_of: dict[ast.AST, ast.AST]) -> bool:
    if not isinstance(stmt, _LOOP_TRY_NODES):
        return False
    for final_stmt in getattr(stmt, "finalbody", ()) or ():
        if isinstance(final_stmt, (ast.Return, ast.Raise)):
            return True
        if (isinstance(final_stmt, ast.Break)
                and _break_exits_loop(final_stmt, loop_node, parent_of)):
            return True
        if _b07_stmt_reaches_own_continue(final_stmt):
            return False
    return False
def _loop_finally_continues(
        stmt: ast.AST, loop_node: _ForNode,
        parent_of: dict[ast.AST, ast.AST]) -> bool:
    current = stmt
    while current is not loop_node:
        parent = parent_of.get(current)
        if parent is None:
            break
        finalbody = (getattr(parent, "finalbody", ()) or ()
                     if isinstance(parent, _LOOP_TRY_NODES) else ())
        if (finalbody and current not in finalbody
                and any(_b07_stmt_reaches_own_continue(final_stmt)
                        for final_stmt in finalbody)):
            return True
        current = parent
    return False
def _b07_block_exit_guarantee(stmt: ast.AST, guaranteed: bool,
                              loop_node: _ForNode,
                              parent_of: dict[ast.AST, ast.AST]) -> bool:
    if _loop_finally_continues(stmt, loop_node, parent_of):
        return False
    if isinstance(stmt, (ast.Return, ast.Raise)):
        return True
    if isinstance(stmt, ast.Break):
        return _break_exits_loop(stmt, loop_node, parent_of)
    if _b07_finally_exits_loop(stmt, loop_node, parent_of):
        return True
    if isinstance(stmt, ast.Continue):
        return False
    if _b07_stmt_reaches_own_continue(stmt):
        return False
    return guaranteed
def _b07_exit_followed_mutation_ids(node: _ForNode,
                                    parent_of: dict[ast.AST, ast.AST]) -> set[int]:
    safe: set[int] = set()
    stack: list[ast.AST] = [node]
    while stack:
        current = stack.pop()
        if isinstance(current, _B07_SCOPE_BOUNDARY_NODES):
            continue
        if _b07_finally_exits_loop(current, node, parent_of):
            safe |= _b07_mutation_ids_in(current)
            continue
        for _field, value in ast.iter_fields(current):
            if not isinstance(value, list):
                continue
            branches = [item for item in value
                        if isinstance(item, _B07_BRANCH_BLOCK_NODES)]
            if branches:
                stack.extend(branches)
                continue
            block = [item for item in value if isinstance(item, ast.stmt)]
            if not block:
                continue
            guaranteed = False
            for stmt in reversed(block):
                if guaranteed and not _b07_stmt_reaches_own_continue(stmt):
                    safe |= _b07_mutation_ids_in(stmt)
                _stmt_exits = _b07_block_exit_guarantee(
                    stmt, guaranteed, node, parent_of)
                if _stmt_exits and not guaranteed:
                    safe |= _b07_mutation_ids_in(stmt)
                guaranteed = _stmt_exits
                stack.append(stmt)
    return safe
def detect_b07_modify_iterable_during_loop(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    seen: set[tuple[str, int]] = set()
    bindings = _LoopBindings(tree)
    parent_of = parent_map(tree)
    for node, iter_names, frame in _iter_loop_groups(tree, bindings):
        if _b07_is_materialized_iter(node.iter, bindings):
            continue
        safe_mutations = _b07_exit_followed_mutation_ids(node, parent_of)
        worklist_bfs = _b07_is_worklist_bfs(node)
        sequence_kinds = {
            name: _b07_literal_sequence_kind(node, name, parent_of)
            for name in iter_names}
        for sub in frame:
            if id(sub) in safe_mutations:
                continue
            for iter_name in iter_names:
                _append_hit(issues, seen, iter_name, sub,
                            _b07_check_node(
                                sub, iter_name, worklist_bfs,
                                sequence_kinds[iter_name]))
    return _finish('B07', 'modify_iterable_during_loop', issues, filepath)
def _loop_key_names(node: ast.For | ast.AsyncFor | ast.comprehension,
                    *, unknown_is_key: bool) -> set[str]:
    whole_element_names = _simple_target_names(node.target)
    iter_node = node.iter
    if isinstance(iter_node, ast.GeneratorExp):
        return (whole_element_names if _iter_elements_are_keys(
            iter_node, unknown_is_key) else set())
    if not isinstance(iter_node, ast.Call):
        return whole_element_names
    func = iter_node.func
    if isinstance(func, ast.Name):
        if func.id == 'enumerate':
            return _enumerate_value_names(node, iter_node, unknown_is_key)
        if func.id in _ELEMENT_PRESERVING_FACTORIES:
            return (whole_element_names if _iter_elements_are_keys(
                iter_node, unknown_is_key) else set())
        if func.id in _OPAQUE_ITER_FACTORIES:
            return set()
        return whole_element_names if unknown_is_key else set()
    if not (isinstance(func, ast.Attribute)
            and func.attr in _ITER_VIEW_METHODS):
        return whole_element_names if unknown_is_key else set()
    if func.attr == 'values':
        return set()
    target = node.target
    if func.attr == 'keys':
        return {target.id} if isinstance(target, ast.Name) else set()
    if isinstance(target, (ast.Tuple, ast.List)) and target.elts:
        first = target.elts[0]
        return {first.id} if isinstance(first, ast.Name) else set()
    return set()
def _enumerate_value_names(
        node: ast.For | ast.AsyncFor | ast.comprehension,
        iter_node: ast.Call, unknown_is_key: bool) -> set[str]:
    keywords = iter_node.keywords
    if (not 1 <= len(iter_node.args) <= 2
            or len(keywords) > 1
            or any(keyword.arg != 'start' for keyword in keywords)
            or (len(iter_node.args) == 2 and keywords)):
        return set()
    target = node.target
    if not (isinstance(target, (ast.Tuple, ast.List))
            and len(target.elts) >= 2):
        return set()
    names = _simple_target_names(target.elts[1])
    if not names:
        return set()
    return names if _iter_elements_are_keys(
        iter_node.args[0], unknown_is_key) else set()
def _simple_target_names(target: ast.AST) -> set[str]:
    if isinstance(target, ast.Name):
        return {target.id}
    if isinstance(target, ast.Starred):
        return _simple_target_names(target.value)
    return set()
def _contains_node(root: ast.AST | None, target: ast.AST) -> bool:
    return root is not None and any(node is target for node in walk_nodes(root))
def _binding_follows_mutation(node: ast.AST, mutation: ast.AST) -> bool:
    if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                         ast.NamedExpr)):
        roots = [node.value]
    elif isinstance(node, _FOR_NODES):
        roots = [node.iter]
    elif isinstance(node, ast.withitem):
        roots = [node.context_expr]
    elif isinstance(node, ast.ExceptHandler):
        roots = [node.type]
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        roots = _evaluated_definition_expressions(node)
    elif isinstance(node, ast.ClassDef):
        roots = [node]
    else:
        return False
    return any(_contains_node(root, mutation) for root in roots)
def _loop_key_rebindings(
        frame: list[ast.AST], names: set[str],
) -> dict[str, list[ast.AST]]:
    found: dict[str, list[ast.AST]] = {name: [] for name in names}
    for node in frame:
        if isinstance(node, ast.AnnAssign) and node.value is None:
            continue
        for name in names:
            if _b29_rebinds_name(node, name):
                found[name].append(node)
    return found
def _available_loop_key_names(
        names: set[str], rebindings: dict[str, list[ast.AST]],
        mutation: ast.AST,
) -> set[str]:
    mutation_pos = node_position(mutation)
    available: set[str] = set()
    for name in names:
        invalidated = any(
            _b17_binding_position(binding) < mutation_pos
            and not _binding_follows_mutation(binding, mutation)
            for binding in rebindings.get(name, ()))
        if not invalidated:
            available.add(name)
    return available
def _iter_elements_are_keys(inner: ast.AST, unknown_is_key: bool) -> bool:
    if isinstance(inner, ast.GeneratorExp):
        if not inner.generators or not isinstance(inner.elt, ast.Name):
            return False
        name = inner.elt.id
        key_names = _loop_key_names(
            inner.generators[0], unknown_is_key=unknown_is_key)
        return name in key_names and all(
            not _target_binds_name(generator.target, name)
            for generator in inner.generators[1:])
    if isinstance(inner, (ast.Name, ast.Attribute, ast.Subscript)):
        return True
    if not isinstance(inner, ast.Call):
        return unknown_is_key
    func = inner.func
    if isinstance(func, ast.Attribute) and func.attr in _ITER_VIEW_METHODS:
        return func.attr == 'keys'
    if isinstance(func, ast.Name):
        if func.id in _ELEMENT_PRESERVING_FACTORIES:
            source_index = 1 if func.id == 'filter' else 0
            expected_args = 2 if func.id == 'filter' else 1
            if len(inner.args) != expected_args or inner.keywords:
                return unknown_is_key
            return _iter_elements_are_keys(
                inner.args[source_index], unknown_is_key)
        if func.id in _OPAQUE_ITER_FACTORIES:
            return False
    return unknown_is_key
def _b07_literal_sequence_kind(
        loop: ast.AST, name: str, parents: dict) -> str | None:
    scope = loop
    while scope in parents:
        scope = parents[scope]
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda, ast.ClassDef, ast.Module)):
            break
    events: list[tuple[ast.AST, ast.AST | None]] = []
    loop_pos = node_position(loop)
    for node in _execution_scope_nodes(scope):
        if node_position(node) >= loop_pos or name not in scope_node_bound_names(node):
            continue
        values = dict(_binding_value_pairs(node))
        events.append((node, values.get(name)))
    guaranteed = [
        (node, value) for node, value in events
        if _b17_execution_guaranteed_before(node, loop, parents)]
    if not guaranteed:
        return None
    latest, value = max(guaranteed, key=lambda event: node_position(event[0]))
    latest_pos = node_position(latest)
    if any(latest_pos < node_position(node)
           and not _b17_execution_guaranteed_before(node, loop, parents)
           for node, _value in events):
        return None
    if isinstance(value, ast.List):
        return 'list'
    if isinstance(value, ast.Tuple):
        return 'tuple'
    return None

def _b07_check_node(sub: ast.AST, iter_name: str,
                    worklist_bfs: bool = False,
                    sequence_kind: str | None = None) -> DiagnoseIssue | None:
    if isinstance(sub, ast.Call):
        return _b07_check_call(sub, iter_name, worklist_bfs)
    if isinstance(sub, ast.AugAssign):
        return _b07_check_augassign(sub, iter_name, sequence_kind)
    if isinstance(sub, ast.Subscript) and isinstance(sub.ctx, ast.Store):
        return _b07_check_subscript(sub, iter_name)
    return None
def _b07_is_worklist_bfs(loop_node: ast.AST) -> bool:
    """BFS 工作队列模式：循环体内有 ``if key in seen: continue`` 且 ``seen``
    在循环内被 ``.add()`` 守卫。此时对**被迭代的队列**调用 ``.extend()`` 是
    逐层扩展工作集的故意写法（新入队元素需要被后续迭代处理），不是
    “边遍历边改”的缺陷。"""
    guard_names: set[str] = set()
    added_names: set[str] = set()
    for sub in iter_loop_frame_nodes(loop_node.body):
        if isinstance(sub, ast.If) and sub.body and isinstance(
                sub.body[-1], (ast.Continue, ast.Return)):
            test = sub.test
            if (isinstance(test, ast.Compare) and len(test.ops) == 1
                    and isinstance(test.ops[0], ast.In)
                    and len(test.comparators) == 1):
                guard = recv_name(test.comparators[0])
                if guard:
                    guard_names.add(guard)
        if (isinstance(sub, ast.Call)
                and isinstance(sub.func, ast.Attribute)
                and sub.func.attr in {'add', 'update'}):
            added = recv_name(sub.func.value)
            if added:
                added_names.add(added)
    return bool(guard_names & added_names)
def _b07_check_call(sub: ast.Call, iter_name: str,
                    worklist_bfs: bool = False) -> DiagnoseIssue | None:
    if (isinstance(sub.func, ast.Attribute) and sub.func.attr in _ITER_MODIFY_METHODS
            and recv_name(sub.func.value) == iter_name):
        if worklist_bfs and sub.func.attr == 'extend':
            return None
        return _error_issue(
            'B07',
            f"循环中修改迭代对象: for 迭代 '{iter_name}' 时调用 .{sub.func.attr}() 会跳过元素或死循环",
            sub.lineno,
            '迭代副本（for x in list(items)）或先收集再修改',
        )
    return None
def _b07_check_augassign(
        sub: ast.AugAssign, iter_name: str,
        sequence_kind: str | None = None) -> DiagnoseIssue | None:
    immutable_rebind = (
        sequence_kind == 'tuple' and isinstance(sub.op, ast.Add)
        and isinstance(sub.value, ast.Tuple))
    string_rebind = (
        sequence_kind != 'list' and _is_str_concat_augassign(sub))
    if (recv_name(sub.target) == iter_name
            and not immutable_rebind and not string_rebind):
        if _is_self_inplace_merge(sub, iter_name):
            return None
        return _error_issue(
            'B07',
            f"循环中修改迭代对象: 对 '{iter_name}' 使用 += 可能改变其长度",
            sub.lineno,
            '迭代副本或改用其他累加方式',
        )
    return None
def _is_self_inplace_merge(sub: ast.AugAssign, iter_name: str) -> bool:
    return (isinstance(sub.op, (ast.BitOr, ast.BitAnd))
            and recv_name(sub.value) == iter_name)
def _b07_check_subscript(sub: ast.Subscript,
                         iter_name: str) -> DiagnoseIssue | None:
    if recv_name(sub.value) != iter_name:
        return None
    # 下标赋值 ``seq[i] = value`` 只替换元素、不改变长度，迭代器不会错位或
    # 死循环（与 ``.append/.extend`` 有本质区别）。只有**切片**赋值
    # ``seq[i:j] = ...`` 能改变长度，才属于真正会破坏迭代的写法。
    if not isinstance(sub.slice, ast.Slice):
        return None
    step = sub.slice.step
    if (step is not None
            and not (isinstance(step, ast.Constant) and step.value is None)):
        # 扩展切片赋值要求等长替换，不能像普通切片一样改变列表长度。
        return None
    return _error_issue(
        'B07',
        f"循环中修改迭代对象: 对 '{iter_name}' 下标赋值会破坏迭代",
        sub.lineno,
        '迭代副本或先收集再修改',
    )
def _extract_iter_names(
        iter_node: ast.AST, bindings: _LoopBindings | None = None) -> set[str]:
    names: set[str] = set()
    _collect_iter_names(iter_node, names, bindings)
    return names
def _collect_iter_names(
        node: ast.AST, names: set[str],
        bindings: _LoopBindings | None) -> None:
    if isinstance(node, ast.GeneratorExp):
        if node.generators:
            _collect_iter_names(node.generators[0].iter, names, bindings)
        return
    if isinstance(node, ast.Name):
        names.add(node.id)
        return
    if isinstance(node, ast.Attribute):
        dn = dotted_name(node)
        if dn:
            names.add(dn)
        return
    if isinstance(node, ast.Call):
        _collect_call_iter_names(node, names, bindings)
def _collect_call_iter_names(
        node: ast.Call, names: set[str],
        bindings: _LoopBindings | None) -> None:
    fn = node.func
    if isinstance(fn, ast.Attribute):
        if fn.attr in _ITER_VIEW_METHODS:
            _collect_iter_names(fn.value, names, bindings)
        return
    if (isinstance(fn, ast.Name)
            and _loop_builtin_call(
                node, _LAZY_ITERATOR_FACTORIES | {'range', 'len'}, bindings)):
        _collect_call_args(fn.id, node, names, bindings)
_FACTORY_ARG_SPECS: dict[str, tuple[slice, slice]] = {
    'iter': (slice(None, 1), slice(None, 1)),
    'enumerate': (slice(None, 1), slice(None, 1)),
    'map': (slice(1, None), slice(1, None)),
    'filter': (slice(1, None), slice(1, 2)),
    'zip': (slice(None), slice(None)),
    'reversed': (slice(None), slice(None)),
}
_LAZY_ITERATOR_FACTORIES = frozenset(_FACTORY_ARG_SPECS)
def _collect_call_args(
        fn_id: str, node: ast.Call, names: set[str],
        bindings: _LoopBindings | None) -> None:
    if fn_id == 'range':
        for a in node.args:
            if _loop_builtin_call(a, {'len'}, bindings):
                _collect_iter_names(a, names, bindings)
        return
    if fn_id == 'len':
        for a in node.args:
            _collect_iter_names(a, names, bindings)
        return
    if fn_id == 'iter':
        if len(node.args) == 1 and not node.keywords:
            _collect_iter_names(node.args[0], names, bindings)
        return
    spec = _FACTORY_ARG_SPECS.get(fn_id)
    if spec is None:
        return
    for a in node.args[spec[0]]:
        _collect_iter_names(a, names, bindings)
def _is_str_concat_value(value: ast.AST) -> bool:
    return ((isinstance(value, ast.Constant) and isinstance(value.value, str))
            or isinstance(value, ast.JoinedStr))
def _is_str_concat_augassign(node: ast.AugAssign) -> bool:
    return isinstance(node.op, ast.Add) and _is_str_concat_value(node.value)
def detect_b32_dict_modify_during_iter(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    seen: set[tuple[str, int]] = set()
    bindings = _LoopBindings(tree)
    _pm = bindings.parents
    for node, iter_names, frame in _iter_loop_groups(tree, bindings):
        if _b07_is_materialized_iter(node.iter, bindings):
            continue
        loop_key_names = _loop_key_names(node, unknown_is_key=False)
        key_rebindings = _loop_key_rebindings(frame, loop_key_names)
        for sub in frame:
            active_key_names = _available_loop_key_names(
                loop_key_names, key_rebindings, sub)
            hit = _b32_issue_for_sub(
                sub, iter_names, node, _pm, active_key_names)
            if hit is not None:
                iter_name, issue = hit
                _append_hit(issues, seen, iter_name, sub, issue)
    return _finish('B32', 'dict_modify_during_iter', issues, filepath)
def _b32_issue_for_sub(sub: ast.AST, iter_names: set[str], for_node: _ForNode,
                       parent_of: dict[ast.AST, ast.AST],
                       loop_key_names: set[str]):
    for iter_name in sorted(iter_names):
        if isinstance(sub, ast.Delete):
            issue = _b32_check_delete(sub, iter_name, for_node, parent_of)
        elif (isinstance(sub, ast.Call) and isinstance(sub.func, ast.Attribute)
                and sub.func.attr in _B32_SIZE_METHODS):
            issue = _b32_check_size_call(
                sub, iter_name, loop_key_names, for_node, parent_of)
        else:
            issue = None
        if issue is not None:
            return iter_name, issue
    return None
def _b32_check_delete(sub: ast.Delete, iter_name: str, for_node: _ForNode,
                      parent_of: dict[ast.AST, ast.AST]) -> DiagnoseIssue | None:
    for t in sub.targets:
        if (is_subscript_of(t, iter_name)
                and not _b32_is_safe_terminating_mutation(
                    for_node, sub, parent_of)):
            return _error_issue(
                'B32',
                f"遍历时删除元素: for 迭代 '{iter_name}' 时 del {iter_name}[...] 会改变容器大小（字典触发 RuntimeError、列表跳元素）",
                sub.lineno,
                '先收集待删项，循环结束后统一删除，或遍历副本 for x in list(items)',
            )
    return None
def _b32_reuses_loop_key(sub: ast.Call, loop_key_names: set[str]) -> bool:
    first = sub.args[0] if sub.args else None
    return (isinstance(first, ast.Name) and first.id in loop_key_names)
def _b32_update_arg_reuses_loop_keys(
        arg: ast.AST, loop_key_names: set[str], iter_name: str) -> bool:
    if isinstance(arg, (ast.List, ast.Tuple, ast.Set)) and not arg.elts:
        return True
    if (isinstance(arg, ast.Constant)
            and isinstance(arg.value, (str, bytes)) and not arg.value):
        return True
    if isinstance(arg, ast.Dict):
        return all(
            isinstance(key, ast.Name) and key.id in loop_key_names
            for key in arg.keys)
    return bool(iter_name) and recv_name(arg) == iter_name
def _b32_update_reuses_loop_keys(
        sub: ast.Call, loop_key_names: set[str], iter_name: str) -> bool:
    if any(keyword.arg is not None for keyword in sub.keywords):
        return False
    args = [*sub.args, *(keyword.value for keyword in sub.keywords)]
    return all(
        _b32_update_arg_reuses_loop_keys(arg, loop_key_names, iter_name)
        for arg in args)
def _b32_check_size_call(
        sub: ast.Call, iter_name: str, loop_key_names: set[str],
        for_node: _ForNode,
        parent_of: dict[ast.AST, ast.AST]) -> DiagnoseIssue | None:
    if recv_name(sub.func.value) != iter_name:
        return None
    if sub.func.attr == 'update' and _b32_update_reuses_loop_keys(
            sub, loop_key_names, iter_name):
        return None
    if (sub.func.attr in _B32_SIZE_NEUTRAL_METHODS
            and _b32_reuses_loop_key(sub, loop_key_names)):
        return None
    if _b32_is_safe_terminating_mutation(for_node, sub, parent_of):
        return None
    _msg = _B32_SIZE_MESSAGE_TEMPLATES[sub.func.attr].format(
        iter_name=iter_name)
    return _error_issue(
        'B32', _msg, sub.lineno,
        '先收集待加/待删项，循环结束后统一修改，或遍历副本 for x in list(s)',
    )
def _b32_block_guarantees_loop_exit(
        body: list[ast.stmt], for_node: _ForNode,
        parent_of: dict[ast.AST, ast.AST]) -> bool:
    guaranteed = False
    for stmt in body:
        if _b07_stmt_reaches_own_continue(stmt):
            return False
        guaranteed = _b07_block_exit_guarantee(
            stmt, guaranteed, for_node, parent_of)
    return guaranteed
def _b32_catching_handler_continues(
        stmt: ast.stmt, for_node: _ForNode,
        parent_of: dict[ast.AST, ast.AST]) -> bool:
    current: ast.AST = stmt
    while current is not for_node:
        parent = parent_of.get(current)
        if parent is None:
            break
        if (isinstance(parent, _LOOP_TRY_NODES)
                and any(current is body_stmt for body_stmt in parent.body)
                and not (parent.finalbody and _b32_block_guarantees_loop_exit(
                    parent.finalbody, for_node, parent_of))
                and any(not _b32_block_guarantees_loop_exit(
                    handler.body, for_node, parent_of)
                        for handler in parent.handlers)):
            return True
        if parent is for_node:
            break
        current = parent
    return False
def _b32_is_safe_terminating_mutation(
        for_node: _ForNode, node: ast.AST,
        parent_of: dict[ast.AST, ast.AST]) -> bool:
    stmt = node
    while not isinstance(stmt, ast.stmt):
        parent = parent_of.get(stmt)
        if parent is None:
            return False
        stmt = parent
    if _b32_enclosing_block(stmt, parent_of) is None:
        return False
    if _b32_catching_handler_continues(stmt, for_node, parent_of):
        return False
    if (isinstance(stmt, (ast.Return, ast.Raise))
            and not _loop_finally_continues(stmt, for_node, parent_of)):
        return True
    return _b32_scan_after_mutation(
        _B32MutationSite(for_node, stmt, parent_of))
def _b32_enclosing_block(node: ast.AST, parent_of: dict[ast.AST, ast.AST]
                        ) -> tuple[list, ast.AST] | None:
    parent = parent_of.get(node)
    if parent is None:
        return None
    for attr in ('body', 'orelse', 'finalbody'):
        body = getattr(parent, attr, None)
        if isinstance(body, list) and node in body:
            return body, parent
    return None
def _b32_block_successors(
        node: ast.AST, parent_of: dict[ast.AST, ast.AST]) -> list:
    found = _b32_enclosing_block(node, parent_of)
    if found is None:
        return []
    body, _owner = found
    return body[body.index(node) + 1:]
def _b32_except_transition(
        node: ast.AST, parent: ast.ExceptHandler,
        parent_of: dict[ast.AST, ast.AST]) -> tuple[ast.AST | None, list]:
    if node not in parent.body:
        return None, []
    successors = parent.body[parent.body.index(node) + 1:]
    try_node = parent_of.get(parent)
    if not isinstance(try_node, _LOOP_TRY_NODES):
        return None, successors
    successors.extend(try_node.finalbody)
    return try_node, successors
def _b32_regular_transition(
        node: ast.AST, parent: ast.AST,
        parent_of: dict[ast.AST, ast.AST]) -> tuple[ast.AST | None, list]:
    found = _b32_enclosing_block(node, parent_of)
    if found is None:
        if isinstance(parent, ast.Match) and node in parent.cases:
            return parent, []
        return None, []
    body, _owner = found
    successors = body[body.index(node) + 1:]
    if isinstance(parent, _LOOP_NODES):
        return None, successors
    if isinstance(parent, _LOOP_TRY_NODES):
        if body is parent.body:
            successors.extend(parent.orelse)
        if body is not parent.finalbody:
            successors.extend(parent.finalbody)
    return parent, successors
def _b32_transition(
        node: ast.AST, parent: ast.AST, for_node: _ForNode,
        parent_of: dict[ast.AST, ast.AST]) -> tuple[ast.AST | None, list]:
    if parent is for_node:
        return None, _b32_block_successors(node, parent_of)
    if isinstance(parent, ast.ExceptHandler):
        return _b32_except_transition(node, parent, parent_of)
    if isinstance(parent, _LOOP_TRY_NODES) and node in parent.handlers:
        return parent, parent.finalbody
    return _b32_regular_transition(node, parent, parent_of)
def _b32_successor_stmts(stmt: ast.stmt, for_node: _ForNode,
                         parent_of: dict[ast.AST, ast.AST]) -> list:
    seq: list = []
    node: ast.AST = stmt
    for _ in range(64):
        parent = parent_of.get(node)
        if parent is None:
            break
        next_node, successors = _b32_transition(
            node, parent, for_node, parent_of)
        seq.extend(successors)
        if next_node is None:
            break
        node = next_node
    return seq
class _B32MutationSite(NamedTuple):
    for_node: _ForNode
    stmt: ast.stmt
    parent_of: dict[ast.AST, ast.AST]
def _b32_scan_after_mutation(site: _B32MutationSite) -> bool:
    for _later in _b32_successor_stmts(
            site.stmt, site.for_node, site.parent_of):
        if isinstance(_later, (ast.Return, ast.Raise)):
            return not _loop_finally_continues(
                _later, site.for_node, site.parent_of)
        if isinstance(_later, ast.Break):
            return (_break_exits_loop(_later, site.for_node, site.parent_of)
                    and not _loop_finally_continues(
                        _later, site.for_node, site.parent_of))
        if isinstance(_later, ast.Continue):
            return False
        if _b32_continue_reaches_iter(_later, site.for_node, site.parent_of):
            return False
    return False
def _b32_continue_reaches_iter(stmt: ast.AST, for_node: _ForNode,
                               parent_of: dict[ast.AST, ast.AST]) -> bool:
    for node in walk_nodes(stmt):
        if not isinstance(node, ast.Continue):
            continue
        child: ast.AST = node
        cur = parent_of.get(child)
        while cur is not None:
            if isinstance(cur, _LOOP_NODES) and child not in cur.orelse:
                if cur is for_node:
                    return True
                break
            child = cur
            cur = parent_of.get(cur)
    return False
def _static_unary_truth(test: ast.UnaryOp) -> bool | None:
    if isinstance(test.op, ast.Not):
        inner = _static_truth(test.operand)
        return None if inner is None else not inner
    operand = test.operand
    if not (isinstance(operand, ast.Constant)
            and isinstance(operand.value, (int, float, complex))
            and not isinstance(operand.value, bool)):
        return None
    if isinstance(test.op, ast.Invert):
        return (bool(~operand.value)
                if isinstance(operand.value, int) else None)
    if isinstance(test.op, (ast.USub, ast.UAdd)):
        return bool(operand.value)
    return None
def _static_container_truth(test: ast.AST) -> bool | None:
    if isinstance(test, (ast.Tuple, ast.List, ast.Set)):
        if not test.elts:
            return False
        if any(not isinstance(el, ast.Starred) for el in test.elts):
            return True
        return None
    if isinstance(test, ast.Dict):
        if not test.keys:
            return False
        if any(key is not None for key in test.keys):
            return True
    return None
def _static_truth(test: ast.AST) -> bool | None:
    if isinstance(test, ast.UnaryOp):
        return _static_unary_truth(test)
    if isinstance(test, ast.Constant):
        return bool(test.value)
    if isinstance(test, (ast.Tuple, ast.List, ast.Set, ast.Dict)):
        return _static_container_truth(test)
    return None
def _is_true_const_test(test: ast.AST) -> bool:
    return _static_truth(test) is True
def _loop_body_has_exit_or_call(body: list) -> bool:
    if any(isinstance(n, _LOOP_EXIT_OR_CALL_NODES)
           for n in iter_loop_frame_nodes(body)):
        return True
    return loop_body_has_break(body)
_OPAQUE_CONCRETE_ITERATOR_FACTORIES = frozenset({
    'enumerate', 'filter', 'map', 'zip',
})
_ITER_LITERAL_NODES = (
    ast.List, ast.Tuple, ast.Set, ast.Dict,
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
_REVERSED_LITERAL_NODES = (
    ast.List, ast.Tuple, ast.Dict, ast.ListComp, ast.DictComp,
)
def _valid_lazy_factory_call(
        factory_call: ast.Call, bindings: _LoopBindings) -> bool:
    fac = factory_call.func
    if (_FACTORY_ARG_SPECS.get(getattr(fac, 'id', None)) is None
            or not _loop_builtin_call(
                factory_call, _LAZY_ITERATOR_FACTORIES, bindings)):
        return False
    args = factory_call.args
    argc = len(args)
    keywords = factory_call.keywords
    keyword_names = [keyword.arg for keyword in keywords]
    keyword_set = set(keyword_names)
    if (None in keyword_set or len(keyword_set) != len(keyword_names)
            or (fac.id == 'enumerate' and keyword_set
                and (keyword_set != {'start'} or argc != 1))
            or (fac.id == 'zip' and not keyword_set <= {'strict'})
            or (fac.id not in {'enumerate', 'zip'} and keyword_set)):
        return False
    if ((fac.id == 'iter' and not 1 <= argc <= 2)
            or (fac.id == 'reversed' and argc != 1)
            or (fac.id == 'enumerate' and not 1 <= argc <= 2)
            or (fac.id == 'map' and argc < 2)
            or (fac.id == 'filter' and argc != 2)):
        return False
    if fac.id == 'enumerate' and (argc == 2 or keyword_set):
        start = (keywords[keyword_names.index('start')].value
                 if keyword_set else args[1])
        if ((isinstance(start, ast.Constant)
             and not isinstance(start.value, int))
                or isinstance(start, (ast.List, ast.Tuple, ast.Set, ast.Dict,
                                      ast.ListComp, ast.SetComp, ast.DictComp))):
            return False
    return True
def _guaranteed_opaque_iterator_call(
        node: ast.AST, bindings: _LoopBindings) -> bool:
    # 入参可为任意表达式（下标被取值对象 / len 实参 / iter 嵌套实参），
    # 非调用节点不可能是惰性迭代器工厂；_valid_lazy_factory_call 只接受 Call。
    if not isinstance(node, ast.Call):
        return False
    if not _valid_lazy_factory_call(node, bindings):
        return False
    factory = node.func.id
    if factory in _OPAQUE_CONCRETE_ITERATOR_FACTORIES:
        return True
    if node.keywords:
        return False
    if factory == 'iter' and len(node.args) == 2:
        return True
    if len(node.args) != 1:
        return False
    arg = node.args[0]
    if factory == 'iter':
        if isinstance(arg, _ITER_LITERAL_NODES):
            return True
        if (isinstance(arg, ast.Constant)
                and isinstance(arg.value, (str, bytes))):
            return True
        if _loop_builtin_call(arg, {'range'}, bindings):
            return True
        return _guaranteed_opaque_iterator_call(arg, bindings)
    if factory == 'reversed':
        return bool(
            isinstance(arg, _REVERSED_LITERAL_NODES)
            or (isinstance(arg, ast.Constant)
                and isinstance(arg.value, (str, bytes)))
            or _loop_builtin_call(arg, {'range'}, bindings))
    return False
def _b37_subscript_issue(
        node: ast.Subscript, bindings: _LoopBindings) -> DiagnoseIssue | None:
    v = node.value
    if isinstance(v, ast.GeneratorExp):
        return _error_issue(
            'B37',
            '生成器表达式是惰性迭代器（无 __getitem__），直接下标一执行即 TypeError: not subscriptable',
            node.lineno,
            '先物化：list(...)[i]，或改用 next()/推导式')
    if not _guaranteed_opaque_iterator_call(v, bindings):
        return None
    return _error_issue(
        'B37',
        (f'{v.func.id}() 返回惰性迭代器（无 __getitem__），直接下标'
         f'一执行即 TypeError: not subscriptable'),
        node.lineno,
        f'先物化：list({v.func.id}(...))[i]，或改用 next()/推导式')
def detect_b37_lazy_iterator_subscript(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    bindings = _LoopBindings(tree)
    issues: list[DiagnoseIssue] = []
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Subscript):
            continue
        issue = _b37_subscript_issue(node, bindings)
        if issue is not None:
            issues.append(issue)
    return _finish('B37', 'lazy_iterator_subscript', issues, filepath)
def _b39_lazy_hit(arg: ast.expr, bindings: _LoopBindings) -> str | None:
    if isinstance(arg, ast.GeneratorExp):
        return '生成器表达式'
    if _guaranteed_opaque_iterator_call(arg, bindings):
        return f'{arg.func.id}() 惰性迭代器'
    return None
def _b39_call_issue(
        node: ast.Call, bindings: _LoopBindings) -> DiagnoseIssue | None:
    if not (_loop_builtin_call(node, {'len'}, bindings)
            and len(node.args) == 1 and not node.keywords):
        return None
    hit = _b39_lazy_hit(node.args[0], bindings)
    if hit is None:
        return None
    return _error_issue('B39', f'len() 消费{hit}（无 __len__），一执行即 TypeError',
                        node.lineno,
                        '先物化：len(list(...))，或改用 sum(1 for _ in ...) 计数')
def detect_b39_len_of_lazy_iterator(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    bindings = _LoopBindings(tree)
    issues: list[DiagnoseIssue] = []
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        issue = _b39_call_issue(node, bindings)
        if issue is not None:
            issues.append(issue)
    return _finish('B39', 'len_of_lazy_iterator', issues, filepath)
def _b66_known_non_iterable(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant)
            and not isinstance(node.value, (str, bytes)))


def _b66_empty_input(node: ast.AST) -> bool:
    if isinstance(node, (ast.GeneratorExp, ast.ListComp,
                         ast.SetComp, ast.DictComp)):
        for generator in node.generators:
            if _b66_known_non_iterable(generator.iter):
                return False
            if _b66_empty_input(generator.iter):
                return True
            if any(_static_truth(test) is False for test in generator.ifs):
                return True
        return False
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and not node.value)
_B66_NON_ITERATOR_CTORS = frozenset({
    'list', 'tuple', 'set', 'dict', 'str', 'bytes', 'bytearray', 'frozenset',
})
def _b66_lazy_factory_inputs(
        factory_call: ast.Call, bindings: _LoopBindings) -> tuple | None:
    if not _valid_lazy_factory_call(factory_call, bindings):
        return None
    fac = factory_call.func
    if fac.id == 'iter' and len(factory_call.args) != 1:
        return None
    spec = _FACTORY_ARG_SPECS[fac.id]
    return factory_call.args[spec[1]]
def _b66_signature_issue(
        node: ast.Call, bindings: _LoopBindings) -> DiagnoseIssue | None:
    if not _loop_builtin_call(node, {'next'}, bindings):
        return None
    if 1 <= len(node.args) <= 2 and not node.keywords:
        return None
    return _error_issue(
        'B66',
        'next() 参数签名非法：应为 next(iterator[, default])，且不接受关键字参数',
        node.lineno, '传入迭代器，并只用第二个位置参数提供默认值')
def _b66_non_iterator_issue(
        node: ast.Call, bindings: _LoopBindings) -> DiagnoseIssue | None:
    arg0 = node.args[0]
    literal = isinstance(arg0, (ast.List, ast.Tuple, ast.Set, ast.Dict,
                                ast.ListComp, ast.SetComp, ast.DictComp,
                                ast.Constant))
    ctor_call = _loop_builtin_call(arg0, _B66_NON_ITERATOR_CTORS, bindings)
    range_call = _loop_builtin_call(arg0, {'range'}, bindings)
    if not (literal or ctor_call or range_call):
        return None
    detail = ('range() 返回可迭代对象而非迭代器' if range_call
              else '参数为非迭代器容器' if ctor_call
              else '参数为非迭代器字面量')
    return _error_issue(
        'B66', f'next() {detail}：必 TypeError（object is not an iterator）',
        node.lineno, '先 iter() 包装（next(iter(seq))），或确认参数是迭代器')
def _b66_empty_factory_issue(
        node: ast.Call, bindings: _LoopBindings) -> DiagnoseIssue | None:
    arg0 = node.args[0]
    if len(node.args) >= 2:
        return None
    if isinstance(arg0, ast.GeneratorExp):
        if not _b66_empty_input(arg0):
            return None
        return _error_issue(
            'B66',
            'next(生成器表达式) 输入为空字面量序列且无 default：必 StopIteration',
            node.lineno, '补 default 参数（next(it, default)）或先判空')
    if not isinstance(arg0, ast.Call):
        return None
    inputs = _b66_lazy_factory_inputs(arg0, bindings)
    if inputs is None:
        return None
    if any(_b66_known_non_iterable(arg) for arg in inputs):
        return None
    empty_zero_arg_zip = arg0.func.id == 'zip' and not arg0.args
    if not empty_zero_arg_zip and not any(_b66_empty_input(a) for a in inputs):
        return None
    return _error_issue(
        'B66',
        f'next({arg0.func.id}(...)) 输入为空字面量序列且无 default：必 StopIteration',
        node.lineno, '补 default 参数（next(it, default)）或先判空')
def _b66_next_call_issue(
        node: ast.Call, bindings: _LoopBindings) -> DiagnoseIssue | None:
    issue = _b66_signature_issue(node, bindings)
    if issue is not None:
        return issue
    if not _loop_builtin_call(node, {'next'}, bindings):
        return None
    issue = _b66_non_iterator_issue(node, bindings)
    if issue is not None:
        return issue
    return _b66_empty_factory_issue(node, bindings)
def detect_b66_next_invalid_iterator(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    bindings = _LoopBindings(tree)
    issues: list[DiagnoseIssue] = []
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        issue = _b66_next_call_issue(node, bindings)
        if issue is not None:
            issues.append(issue)
    return _finish('B66', 'next_invalid_iterator', issues, filepath)
def detect_b68_while_true_no_exit(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    for node in tree_nodes(tree):
        if not isinstance(node, ast.While) or not _is_true_const_test(node.test):
            continue
        if _loop_body_has_exit_or_call(node.body):
            continue
        issues.append(_error_issue(
            'B68',
            'while True 循环体无 break/return/raise/yield 且无调用：必死循环',
            node.lineno,
            '补退出条件（break/return）或改为有限循环（for/while 条件表达式）',
        ))
    return _finish('B68', 'while_true_no_exit', issues, filepath)
_EXHAUSTIVE_CONSUMERS = frozenset({
    'list', 'tuple', 'set', 'frozenset', 'dict', 'sum', 'max', 'min', 'sorted',
})
_PARTIAL_CONSUMERS = frozenset({'any', 'all'})
def _execution_scope_roots(tree: ast.Module) -> list[ast.AST]:
    scopes = [n for n in tree_nodes(tree)
              if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda, ast.ClassDef))]
    scopes.append(tree)
    return scopes
def _target_value_pairs(
        target: ast.AST, value: ast.AST) -> list[tuple[str, ast.AST]]:
    if isinstance(target, ast.Name):
        return [(target.id, value)]
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and all(not isinstance(elt, ast.Starred) for elt in target.elts)):
        return []
    return [pair for target_elt, value_elt in zip(target.elts, value.elts)
            for pair in _target_value_pairs(target_elt, value_elt)]
def _binding_value_pairs(node: ast.AST) -> list[tuple[str, ast.AST]]:
    if isinstance(node, ast.Assign):
        return [pair for target in node.targets
                for pair in _target_value_pairs(target, node.value)]
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return _target_value_pairs(node.target, node.value)
    if isinstance(node, ast.NamedExpr):
        return _target_value_pairs(node.target, node.value)
    return []
def detect_b09_string_concat_in_loop(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    seen: set[tuple[str, int]] = set()
    annotations_evaluated = _module_annotations_evaluated(tree)
    parents = parent_map(tree)
    for scope in _execution_scope_roots(tree):
        bindings = _b09_scope_bindings(scope, annotations_evaluated)
        if not bindings:
            continue
        issues.extend(_b09_loop_concat_issues(
            scope, bindings, seen, parents, annotations_evaluated))
    return _finish('B09', 'string_concat_in_loop', issues, filepath)
def _b09_scope_bindings(
        scope: ast.AST, annotations_evaluated: bool = True,
) -> dict[str, list[tuple[int, int, bool, ast.AST]]]:
    bindings: dict[str, list[tuple[int, int, bool, ast.AST]]] = {}
    for node in _execution_scope_nodes(scope, annotations_evaluated):
        for name, value in _binding_value_pairs(node):
            bindings.setdefault(name, []).append(
                (node.lineno, node.col_offset,
                 _is_str_concat_value(value), node))
    return bindings
def _b09_bound_may_be_str_at(
        history: list[tuple[int, int, bool, ast.AST]], target: ast.AST,
        parents: dict[ast.AST, ast.AST]) -> bool:
    target_pos = node_position(target)
    for line, col, is_str, event in history:
        if not is_str or (line, col) > target_pos:
            continue
        later_non_strings = [
            other for other_line, other_col, other_is_str, other in history
            if not other_is_str
            and (line, col) < (other_line, other_col) <= target_pos
        ]
        if not _b17_events_cover_before(later_non_strings, target, parents):
            return True
    return False
def _b09_rhs_may_be_string(value: ast.AST) -> bool:
    if _is_str_concat_value(value):
        return True
    if isinstance(value, ast.Constant):
        return False
    return not isinstance(value, (ast.List, ast.Tuple, ast.Set, ast.Dict))
def _b09_concat_target(
        sub: ast.AST, bindings: dict,
        parents: dict[ast.AST, ast.AST]) -> str | None:
    if not isinstance(sub, ast.AugAssign):
        return None
    if not isinstance(sub.op, ast.Add):
        return None
    if not isinstance(sub.target, ast.Name):
        return None
    if not _b09_rhs_may_be_string(sub.value):
        return None
    name = sub.target.id
    if name not in bindings:
        return None
    if not _b09_bound_may_be_str_at(bindings[name], sub, parents):
        return None
    return name
def _b09_loop_concat_issues(
        scope: ast.AST, bindings: dict, seen: set[tuple[str, int]],
        parents: dict[ast.AST, ast.AST],
        annotations_evaluated: bool = True) -> list[DiagnoseIssue]:
    found: list[DiagnoseIssue] = []
    for loop in _execution_scope_nodes(scope, annotations_evaluated):
        if not isinstance(loop, _LOOP_NODES):
            continue
        for sub in iter_loop_frame_nodes(loop.body):
            name = _b09_concat_target(sub, bindings, parents)
            if name is None:
                continue
            key = (name, sub.lineno)
            if key in seen:
                continue
            seen.add(key)
            found.append(_warn_issue(
                'B09',
                f"循环内字符串拼接: '{name} += ...' 反复创建新字符串，性能差",
                sub.lineno, "收集到列表后用 ''.join() 拼接"))
    return found
def detect_b17_iterator_reuse(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    bindings = _LoopBindings(tree)
    parents = parent_map(tree)
    annotations_evaluated = _module_annotations_evaluated(tree)
    for scope in _execution_scope_roots(tree):
        all_assigns, iter_assigns = _b17_scope_assigns(
            scope, bindings, annotations_evaluated)
        if not iter_assigns:
            continue
        consume_lines = _b17_scope_consumes(
            scope, set(iter_assigns), bindings, parents,
            annotations_evaluated)
        for var, iter_lines in iter_assigns.items():
            issues.extend(_b17_reuse_issues(
                var, iter_lines, consume_lines[var],
                all_assigns.get(var, []), parents))
    return _finish('B17', 'iterator_reuse', issues, filepath)
def _b17_binding_position(node: ast.AST) -> tuple[int, int]:
    value: ast.AST | None = None
    if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign,
                         ast.NamedExpr)):
        value = node.value
    elif isinstance(node, _FOR_NODES):
        value = node.iter
    if value is not None:
        # 绑定发生在 RHS/迭代表达式求值之后，不能屏蔽其中的旧迭代器消费。
        return (
            getattr(value, 'end_lineno', None) or value.lineno,
            getattr(value, 'end_col_offset', None) or value.col_offset,
        )
    anchor = node
    if isinstance(node, ast.withitem) and node.optional_vars is not None:
        anchor = node.optional_vars
    elif isinstance(node, ast.comprehension):
        anchor = node.target
    return node_position(anchor)
def _b17_scope_assigns(
        scope: ast.AST, bindings: _LoopBindings,
        annotations_evaluated: bool = True,
) -> tuple[dict[str, list[tuple[int, int]]],
           dict[str, list[tuple[int, int]]]]:
    all_assigns: dict[str, list[tuple[int, int]]] = {}
    iter_assigns: dict[str, list[tuple[int, int]]] = {}
    for node in _execution_scope_nodes(scope, annotations_evaluated):
        position = _b17_binding_position(node)
        for name in scope_node_bound_names(node):
            all_assigns.setdefault(name, []).append(position)
    for node in _execution_scope_nodes(scope, annotations_evaluated):
        line, col = _b17_binding_position(node)
        for name, value in _binding_value_pairs(node):
            if (isinstance(value, ast.GeneratorExp)
                    or _loop_builtin_call(
                        value, _LAZY_ITERATOR_FACTORIES, bindings)):
                iter_assigns.setdefault(name, []).append((line, col))
    return all_assigns, iter_assigns
def _consume_args(
        node: ast.AST, bindings: _LoopBindings) -> list[tuple[ast.Name, str]]:
    if not _loop_builtin_call(
            node, _EXHAUSTIVE_CONSUMERS | _PARTIAL_CONSUMERS, bindings):
        return []
    func = node.func
    if func.id in _EXHAUSTIVE_CONSUMERS:
        kind = 'exhaustive'
    else:
        kind = 'partial'
    return [(a, kind) for a in node.args if isinstance(a, ast.Name)]
def _b17_loop_consume(node: ast.AST, parents: dict) -> tuple[ast.Name, str] | None:
    if (not isinstance(node, _FOR_NODES)
            or not isinstance(node.iter, ast.Name)):
        return None
    early_exit = any(
        isinstance(sub, (ast.Return, ast.Raise))
        and not _loop_finally_continues(sub, node, parents)
        for sub in iter_loop_frame_nodes(node.body))
    kind = ('partial' if early_exit or loop_body_has_break(node.body)
            else 'exhaustive')
    return node.iter, kind
def _b17_scope_consumes(
        scope: ast.AST, iter_names: set, bindings: _LoopBindings,
        parents: dict, annotations_evaluated: bool = True,
) -> dict[str, list[tuple[int, int, str, ast.AST]]]:
    events: dict[str, list[tuple[int, int, str, ast.AST]]] = {
        v: [] for v in iter_names}
    for node in _execution_scope_nodes(scope, annotations_evaluated):
        consumes = _consume_args(node, bindings)
        loop_consume = _b17_loop_consume(node, parents)
        if loop_consume is not None:
            consumes.append(loop_consume)
        for arg, kind in consumes:
            if arg.id not in events:
                continue
            events[arg.id].append((node.lineno, node.col_offset, kind, node))
    return events
def _b17_reuse_issues(var: str, iter_lines: list[tuple[int, int]],
                      consumes: list[tuple[int, int, str, ast.AST]],
                      barriers: list[tuple[int, int]],
                      parents: dict) -> list[DiagnoseIssue]:
    reuse_sites = _b17_reuse_sites(
        consumes, barriers, set(iter_lines), parents)
    found: list[DiagnoseIssue] = []
    for positions in reuse_sites.values():
        reuse_ln, _reuse_col = min(positions)
        found.append(_warn_issue(
            'B17',
            f"迭代器复用: 迭代器 '{var}' 耗尽后仍被消费 {len(positions)} 次，后续读取恒为空",
            reuse_ln,
            '将迭代器一次性转为 list 再复用，或为每次消费重新创建迭代器'))
    return found
def _b17_execution_region(
        node: ast.AST, ancestor: ast.AST, parents: dict) -> tuple | None:
    current = node
    parent = parents.get(current)
    while parent is not None and parent is not ancestor:
        current, parent = parent, parents.get(parent)
    if parent is not ancestor:
        return None
    if isinstance(ancestor, (ast.If, ast.IfExp)):
        containers = ((ancestor.body, ancestor.orelse)
                      if isinstance(ancestor, ast.If)
                      else ((ancestor.body,), (ancestor.orelse,)))
        return next((('branch', index)
                     for index, body in enumerate(containers)
                     if any(stmt is current for stmt in body)), None)
    if isinstance(ancestor, ast.Match):
        return next((('case', index)
                     for index, case in enumerate(ancestor.cases)
                     if case is current), None)
    if isinstance(ancestor, _LOOP_NODES):
        if current in ancestor.body:
            return ('loop-body',)
        if current in ancestor.orelse:
            return ('loop-else',)
        return None
    if isinstance(ancestor, _LOOP_TRY_NODES):
        if current in ancestor.body:
            return ('try-body',)
        if current in ancestor.orelse:
            return ('try-else',)
        if current in ancestor.finalbody:
            return None
        return next((('handler', index)
                     for index, handler in enumerate(ancestor.handlers)
                     if handler is current), None)
    if isinstance(ancestor, ast.BoolOp):
        index = next((i for i, value in enumerate(ancestor.values)
                      if value is current), 0)
        return ('bool', index) if index else None
    if isinstance(ancestor, ast.Compare):
        index = next((i for i, value in enumerate(ancestor.comparators)
                      if value is current), -1)
        return ('compare', index) if index > 0 else None
    if isinstance(ancestor, ast.comprehension):
        return ('comprehension-child', id(current))
    if (isinstance(ancestor, (ast.ListComp, ast.SetComp, ast.DictComp,
                              ast.GeneratorExp))
            and (current is getattr(ancestor, 'elt', None) or any(
                current is value for value in (
                    getattr(ancestor, 'key', None),
                    getattr(ancestor, 'value', None))))):
        return ('comprehension-output',)
    return None
def _b17_region_dominates(source: tuple, target: tuple | None) -> bool:
    if source == target:
        return True
    if source == ('try-body',) and target == ('try-else',):
        return True
    if target is not None and source[0] == target[0] and source[0] in {
            'bool', 'compare'}:
        return source[1] < target[1]
    return False
def _b17_execution_guaranteed_before(
        first: ast.AST, second: ast.AST, parents: dict) -> bool:
    second_chain: set[ast.AST] = set()
    current: ast.AST | None = second
    while current is not None:
        second_chain.add(current)
        current = parents.get(current)
    current = first
    while current is not None:
        parent = parents.get(current)
        if parent is None:
            break
        source = _b17_execution_region(current, parent, parents)
        if source is not None:
            target = (_b17_execution_region(second, parent, parents)
                      if parent in second_chain else None)
            if not _b17_region_dominates(source, target):
                return False
        if parent in second_chain:
            break
        current = parent
    return True
def _b17_pattern_irrefutable(pattern: ast.AST) -> bool:
    if isinstance(pattern, ast.MatchAs):
        return (pattern.pattern is None
                or _b17_pattern_irrefutable(pattern.pattern))
    return (isinstance(pattern, ast.MatchOr)
            and any(_b17_pattern_irrefutable(item) for item in pattern.patterns))


def _b17_match_events_cover_before(
        events: list[ast.AST], match_node: ast.Match, parents: dict,
        seen: set[tuple]) -> bool:
    for index, case in enumerate(match_node.cases):
        if case.guard is not None:
            return False
        if block_may_fall_through(case.body):
            case_events = [
                event for event in events
                if _b17_execution_region(event, match_node, parents)
                == ('case', index)]
            if (not case.body or not _b17_events_cover_before(
                    case_events, case.body[-1], parents, seen)):
                return False
        if _b17_pattern_irrefutable(case.pattern):
            return True
    return False


def _b17_events_cover_before(
        events: list[ast.AST], target: ast.AST, parents: dict,
        seen: set[tuple] | None = None,
) -> bool:
    if any(_b17_execution_guaranteed_before(event, target, parents)
           for event in events):
        return True
    if not events:
        return False
    marker = (id(target), tuple(sorted(id(event) for event in events)))
    seen = set() if seen is None else seen
    if marker in seen:
        return False
    seen.add(marker)
    candidates: set[ast.If] = set()
    match_candidates: set[ast.Match] = set()
    for event in events:
        current: ast.AST | None = event
        while current is not None and current is not target:
            current = parents.get(current)
            if isinstance(current, ast.If):
                candidates.add(current)
            elif isinstance(current, ast.Match):
                match_candidates.add(current)
    for if_node in candidates:
        if not if_node.orelse or not _b17_execution_guaranteed_before(
                if_node, target, parents):
            continue
        covered = True
        for index, branch in enumerate((if_node.body, if_node.orelse)):
            if not block_may_fall_through(branch):
                continue
            branch_events = [
                event for event in events
                if _b17_execution_region(event, if_node, parents)
                == ('branch', index)]
            if not branch or not _b17_events_cover_before(
                    branch_events, branch[-1], parents, seen):
                covered = False
                break
        if covered:
            return True
    for match_node in match_candidates:
        if (_b17_execution_guaranteed_before(match_node, target, parents)
                and _b17_match_events_cover_before(
                    events, match_node, parents, seen)):
            return True
    return False
def _b17_event_inside_loop_body(
        loop_node: ast.AST, consume_node: ast.AST, parents: dict) -> bool:
    if not isinstance(loop_node, _FOR_NODES):
        return False
    current = consume_node
    parent = parents.get(current)
    while parent is not None and parent is not loop_node:
        current, parent = parent, parents.get(parent)
    return parent is loop_node and current in loop_node.body
_B17_INVERTED_EVALUATION_NODES = (
    ast.IfExp, ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
def _b17_inverted_evaluation_before(
        first: ast.AST, second: ast.AST, parents: dict) -> bool:
    second_chain: set[ast.AST] = set()
    current: ast.AST | None = second
    while current is not None:
        second_chain.add(current)
        current = parents.get(current)
    current = first
    while current is not None:
        parent = parents.get(current)
        if parent is None:
            break
        if parent in second_chain:
            return bool(
                isinstance(parent, _B17_INVERTED_EVALUATION_NODES)
                and _b17_execution_guaranteed_before(first, second, parents))
        current = parent
    return False
def _b17_reuse_sites(
        consumes: list[tuple[int, int, str, ast.AST]],
        barriers: list[tuple[int, int]], iter_lines: set[tuple[int, int]],
        parents: dict) -> dict[tuple[int, int], list[tuple[int, int]]]:
    reuse_sites: dict[tuple[int, int], list[tuple[int, int]]] = {}
    for c_ln, c_col, _kind, consume_node in consumes:
        consume_pos = (c_ln, c_col)
        seg_head = max((a for a in barriers if a <= consume_pos), default=None)
        if seg_head is None or seg_head not in iter_lines:
            continue
        prior_events: list[ast.AST] = []
        for other_ln, other_col, other_kind, other_node in consumes:
            other_pos = (other_ln, other_col)
            other_seg_head = max(
                (a for a in barriers if a <= other_pos), default=None)
            if (other_kind != 'exhaustive' or other_seg_head != seg_head
                    or _b17_event_inside_loop_body(
                        other_node, consume_node, parents)):
                continue
            if (other_pos >= consume_pos
                    and not _b17_inverted_evaluation_before(
                        other_node, consume_node, parents)):
                continue
            prior_events.append(other_node)
        exhausted_before = _b17_events_cover_before(
            prior_events, consume_node, parents)
        if not exhausted_before:
            continue
        reuse_sites.setdefault(seg_head, []).append(consume_pos)
    return reuse_sites
def detect_b29_range_len_antipattern(code: str, tree: ast.Module, source_lines: list[str] | None = _DEFAULT_SOURCE_LINES, filepath: str = _DEFAULT_FILEPATH) -> list[DiagnoseIssue]:
    issues: list[DiagnoseIssue] = []
    bindings = _LoopBindings(tree)
    annotations_evaluated = _module_annotations_evaluated(tree)
    for node in tree_nodes(tree):
        if not isinstance(node, ast.For):
            continue
        matched = _match_range_len(node, bindings)
        if matched is None:
            continue
        loop_var, seq_name = matched
        if _loop_only_reads_index(
                node, loop_var, seq_name, annotations_evaluated):
            issues.append(_warn_issue(
                'B29',
                f"range(len()) 反模式: for {loop_var} in range(len({seq_name})) 仅用 {loop_var} 读取 {seq_name}[{loop_var}]，应直接迭代",
                node.lineno,
                f"改为 for item in {seq_name}，或 for {loop_var}, item in enumerate({seq_name}) 同时需要索引与元素"))
    return _finish('B29', 'range_len_antipattern', issues, filepath)
def _len_call_name(
        arg: ast.expr, bindings: _LoopBindings | None = None) -> str | None:
    if not _loop_builtin_call(arg, {'len'}, bindings):
        return None
    if len(arg.args) != 1 or not isinstance(arg.args[0], ast.Name):
        return None
    return arg.args[0].id
def _match_range_len(
        for_node: ast.For,
        bindings: _LoopBindings | None = None) -> tuple[str, str] | None:
    it = for_node.iter
    if not _loop_builtin_call(it, {'range'}, bindings):
        return None
    if len(it.args) != 1:
        return None
    seq_name = _len_call_name(it.args[0], bindings)
    if seq_name is None:
        return None
    loop_target = for_node.target
    if not isinstance(loop_target, ast.Name):
        return None
    return (loop_target.id, seq_name)
def _iter_subscript_write_targets(targets: list) -> list:
    out: list[ast.Subscript] = []
    for t in targets:
        if isinstance(t, ast.Subscript):
            out.append(t)
        elif isinstance(t, ast.Starred):
            out.extend(_iter_subscript_write_targets([t.value]))
        elif isinstance(t, (ast.Tuple, ast.List)):
            out.extend(_iter_subscript_write_targets(t.elts))
    return out
def _loop_only_reads_index(
        for_node: ast.For, loop_var: str, seq_name: str,
        annotations_evaluated: bool = True) -> bool:
    body_nodes = _immediate_execution_nodes(
        for_node.body, enter_class_bodies=True,
        annotations_evaluated=annotations_evaluated)
    else_nodes = _immediate_execution_nodes(
        for_node.orelse, enter_class_bodies=True,
        annotations_evaluated=annotations_evaluated)
    scope_nodes = same_scope_bfs_nodes(for_node)
    if _b29_loop_writes_seq(
            [*body_nodes, *else_nodes, *scope_nodes], seq_name):
        return False
    all_else_nodes = [
        node for stmt in for_node.orelse for node in tree_nodes(stmt)]
    if _b29_index_has_other_use(all_else_nodes, loop_var, set()):
        return False
    legal_index = {
        sub.slice for sub in body_nodes
        if is_subscript_of(sub, seq_name)
        and isinstance(sub.slice, ast.Name)
        and sub.slice.id == loop_var
    }
    if not legal_index:
        return False
    all_body_nodes = [
        node for stmt in for_node.body for node in tree_nodes(stmt)]
    return not _b29_index_has_other_use(
        all_body_nodes, loop_var, legal_index)
def _b29_subscript_write(sub: ast.stmt) -> list[ast.Subscript]:
    if isinstance(sub, ast.Assign):
        return _iter_subscript_write_targets(sub.targets)
    if isinstance(sub, (ast.AnnAssign, ast.AugAssign)):
        return [sub.target] if isinstance(sub.target, ast.Subscript) else []
    if isinstance(sub, ast.Delete):
        return _iter_subscript_write_targets(sub.targets)
    return []
def _is_mutator_call(node, seq_name: str) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id == seq_name
            and node.func.attr in _MUTATOR_METHODS)
def _b29_loop_writes_seq(body_nodes, seq_name: str) -> bool:
    for sub in body_nodes:
        if _b29_rebinds_name(sub, seq_name):
            return True
        if any(is_subscript_of(t, seq_name) for t in _b29_subscript_write(sub)):
            return True
        if _is_mutator_call(sub, seq_name):
            return True
    return False
def _target_binds_name(target: ast.AST, name: str) -> bool:
    if isinstance(target, ast.Name):
        return target.id == name
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_target_binds_name(elt, name) for elt in target.elts)
    if isinstance(target, ast.Starred):
        return _target_binds_name(target.value, name)
    return False
def _b29_rebinds_name(sub: ast.AST, name: str) -> bool:
    if isinstance(sub, ast.Delete):
        return any(_target_binds_name(target, name) for target in sub.targets)
    if isinstance(sub, ast.AnnAssign) and sub.value is None:
        return _target_binds_name(sub.target, name)
    if isinstance(sub, ast.comprehension):
        return False
    return name in scope_node_bound_names(sub)
def _b29_index_has_other_use(body_nodes, loop_var: str,
                             legal_index: set[ast.AST]) -> bool:
    for n in body_nodes:
        if isinstance(n, ast.Name) and n.id == loop_var and n not in legal_index:
            return True
    return False
GATE_DETECTORS: dict[str, Any] = {
    "B07": detect_b07_modify_iterable_during_loop,
    "B09": detect_b09_string_concat_in_loop,
    "B17": detect_b17_iterator_reuse,
    "B29": detect_b29_range_len_antipattern,
    "B32": detect_b32_dict_modify_during_iter,
    "B37": detect_b37_lazy_iterator_subscript,
    "B39": detect_b39_len_of_lazy_iterator,
    "B66": detect_b66_next_invalid_iterator,
    "B68": detect_b68_while_true_no_exit,
}

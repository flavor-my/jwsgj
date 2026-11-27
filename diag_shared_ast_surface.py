from __future__ import annotations

import ast
import logging
import re
from collections.abc import Callable
from dataclasses import dataclass, field

from jwsgj.diag_shared_ast_bindings import (
    _STRING_SEQUENCE_TYPES,
    _TRY_STMT_TYPES,
    _string_elts,
    binding_names_of,
    import_stmt_binds,
)
from jwsgj.diag_shared_ast_nodes import (
    TYPE_ALIAS_NODES,
    assign_targets_value,
    definition_time_exprs,
    is_docstring_stmt,
    is_main_check,
    is_placeholder_stmt,
    is_static_method,
    is_type_checking_guard,
    iter_module_scope_funcdefs,
    iter_module_scope_nodes,
    iter_module_stmt_blocks,
    iter_pattern_capture_names,
    main_guard_branch,
    module_postpones_annotations,
    str_constant_value,
    typing_guard_aliases,
    typing_type_checking_names,
)
from jwsgj.diag_shared_source_core import parse_cached
from jwsgj.diag_types_vocab import PARSE_DEGRADE_EXC
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
_ALL_ROOTS = frozenset({"__all__"})
def is_all_target(target: ast.AST) -> bool:
    return isinstance(target, ast.Name) and target.id == "__all__"
def extract_all_strings(assign_node: ast.AST) -> list[str] | None:
    normalized = assign_targets_value(assign_node)
    if normalized is None:
        return None
    targets, value = normalized
    if not any(is_all_target(t) for t in targets):
        return None
    return _string_elts(value) if isinstance(value, _STRING_SEQUENCE_TYPES) \
        else None
def extract_all_augassign_strings(node: ast.AST) -> list[str] | None:
    if not (isinstance(node, ast.AugAssign)
            and is_all_target(node.target)
            and isinstance(node.op, (ast.Add, ast.BitOr))):
        return None
    accepted = (_STRING_SEQUENCE_TYPES + (ast.Set,)
                if isinstance(node.op, ast.BitOr) else _STRING_SEQUENCE_TYPES)
    return (_string_elts(node.value)
            if isinstance(node.value, accepted) else None)
def _is_export_declaration(node: ast.AST) -> bool:
    if not is_all_assignment(node):
        return False
    return not (isinstance(node, ast.AugAssign)
                and not isinstance(node.op, (ast.Add, ast.BitOr)))
def is_all_assignment(node: ast.AST) -> bool:
    if isinstance(node, ast.Assign):
        return any(is_all_target(t) for t in node.targets)
    if isinstance(node, ast.AugAssign):
        return is_all_target(node.target)
    if isinstance(node, ast.AnnAssign):
        return is_all_target(node.target) and node.value is not None
    return False
def extract_all_names(node: ast.AST) -> list[str] | None:
    if not isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
        return None
    if (isinstance(node, ast.AugAssign)
            and not isinstance(node.op, (ast.Add, ast.BitOr))):
        return None
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return None
    targets = list(node.targets) if isinstance(node, ast.Assign) \
        else [node.target]
    if not any(is_all_target(target) for target in targets):
        return None
    value = node.value
    if not isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return None
    names: list[str] = []
    for elt in value.elts:
        if isinstance(elt, ast.Constant) and isinstance(elt.value, str):
            names.append(elt.value)
        else:
            return None
    return names
def _dunder_all_elt_entries(value, depth: int = 0) -> list[tuple[str, int]]:
    if depth > 20:
        return []
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return [(elt.value, elt.lineno) for elt in value.elts
                if isinstance(elt, ast.Constant)
                and isinstance(elt.value, str)]
    if isinstance(value, ast.BinOp) and isinstance(value.op,
                                                  (ast.Add, ast.BitOr, ast.Mult)):
        return (_dunder_all_elt_entries(value.left, depth + 1)
                + _dunder_all_elt_entries(value.right, depth + 1))
    return []
def _all_declared_entries(node: ast.stmt,
                          roots) -> list[tuple[str, int]]:
    if (isinstance(node, ast.AugAssign)
            and _root_name(node.target, roots)):
        if isinstance(node.op, (ast.Add, ast.BitOr)):
            return _dunder_all_elt_entries(node.value)
        return []
    subscript = _all_subscript_target(node, roots)
    if subscript is not None and not isinstance(node, ast.AugAssign):
        name = (str_constant_value(node.value)
                if node.value is not None else None)
        if name is not None:
            return [(name, node.value.lineno)]
        return _dunder_all_elt_entries(node.value)
    value = _all_assignment_value(node)
    if value is not None:
        return _dunder_all_elt_entries(value)
    return _dunder_all_call_entries(node, roots)
def iter_all_export_entries(tree: ast.Module) -> list[tuple[str, int]]:
    entries: dict[str, int] = {}
    replay = replay_export_surface(tree, _entry_lines=entries)
    final_names = set(replay.names)
    return sorted(
        ((name, line) for name, line in entries.items() if name in final_names),
        key=lambda item: item[1])
def _dunder_all_assign_names(node) -> list:
    if not _is_export_declaration(node):
        return []
    return [name for name, _line in _dunder_all_elt_entries(node.value)]
def _is_dunder_all_extend_call(node, roots=_ALL_ROOTS) -> bool:
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return False
    call = node.value
    if not call.args:
        return False
    func = call.func
    return (isinstance(func, ast.Attribute) and _root_name(func.value, roots)
            and func.attr in ("extend", "append", "insert"))
def _dunder_all_call_entries(node, roots=_ALL_ROOTS) -> list[tuple[str, int]]:
    if not _is_dunder_all_extend_call(node, roots):
        return []
    call = node.value
    if call.func.attr == 'insert':
        if len(call.args) < 2:
            return []
        name = str_constant_value(call.args[1])
        return [(name, call.args[1].lineno)] if name is not None else []
    if call.func.attr == 'append':
        name = str_constant_value(call.args[0])
        return [(name, call.args[0].lineno)] if name is not None else []
    return _dunder_all_elt_entries(call.args[0])
def dunder_all_node_names(node) -> list:
    names = _dunder_all_assign_names(node)
    if names:
        return names
    return [name for name, _line in _dunder_all_call_entries(node)]
def collect_all_export_names(node: ast.AST) -> tuple[bool, list[str]]:
    if not _is_export_declaration(node):
        return False, []
    return True, [name for name, _line in _dunder_all_elt_entries(node.value)]
_EXPORT_REPEAT_LIMIT = 256
_STATIC_BINDING_MAX_DEPTH = 32
_EMPTY_EXPORT_SEEN = frozenset()
EXPORT_BRANCH_UNION = "union"
EXPORT_BRANCH_ASSUME = "assume"
_ALL_READONLY_METHODS = frozenset({"count", "index", "copy"})
_ALL_NON_MUTATING_CALLS = frozenset({
    "all", "any", "bool", "format", "frozenset", "getattr", "hasattr",
    "isinstance", "issubclass", "iter", "len", "list", "max", "min",
    "print", "repr", "reversed", "set", "sorted", "str", "sum",
    "tuple", "type",
})
def _root_name(target: ast.AST, roots: frozenset[str] | set[str]) -> bool:
    return isinstance(target, ast.Name) and target.id in roots
@dataclass(frozen=True)
class ExportReplay:
    names: list[str]
    exact: bool
    ordered: bool
    computed: bool
    augmented: bool
    empty_node: ast.stmt | None
    declared: bool
@dataclass
class _ExportState:
    names: set[str]
    seen: set[str]
    order: list[str]
    exact: bool = True
    kind: str | None = None
    ordered: bool = True
    roots: set[str] = field(default_factory=lambda: set(_ALL_ROOTS))
    uncertain_roots: set[str] = field(default_factory=set)
    bindings: dict[str, ast.AST] | None = None
    computed: bool = False
    augmented: bool = False
    empty_node: ast.stmt | None = None
    declared: bool = False
    annotations_evaluated: bool = True
    side_effect_calls: frozenset[int] = field(default_factory=frozenset)
def _state_replay(st: _ExportState) -> ExportReplay:
    names = list(st.order) if st.ordered and st.order else sorted(st.names)
    return ExportReplay(
        names=names,
        exact=st.exact,
        ordered=st.ordered,
        computed=st.computed,
        augmented=st.augmented,
        empty_node=st.empty_node,
        declared=st.declared,
    )
def _container_kind(value: ast.expr | None) -> str | None:
    stack: list[ast.expr | None] = [value]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.List):
            return "list"
        if isinstance(node, ast.Set):
            return "set"
        if isinstance(node, ast.Tuple):
            return "tuple"
        if isinstance(node, ast.BinOp) and isinstance(
                node.op, (ast.Add, ast.BitOr, ast.Mult)):
            stack.append(node.right)
            stack.append(node.left)
    return None
def _value_order_known(value: ast.expr | None, bindings=None,
                       depth: int = 0) -> bool:
    if value is None:
        return True
    if (bindings and isinstance(value, ast.Name) and value.id in bindings
            and depth <= _STATIC_BINDING_MAX_DEPTH):
        return _value_order_known(bindings[value.id], bindings, depth + 1)
    if isinstance(value, ast.Set):
        return False
    if isinstance(value, (ast.List, ast.Tuple)):
        return all(_value_order_known(elt.value if isinstance(elt, ast.Starred)
                                      else elt, bindings, depth + 1)
                   for elt in value.elts)
    if isinstance(value, ast.BinOp):
        if isinstance(value.op, ast.BitOr):
            return False
        if isinstance(value.op, ast.Add):
            return (_value_order_known(value.left, bindings, depth + 1)
                    and _value_order_known(value.right, bindings, depth + 1))
    return True
def _degrade_export_state(st: _ExportState) -> None:
    st.exact = False
    st.order = []
    st.ordered = False
    st.names = set(st.seen)
    st.computed = True
def _clear_export_state(st: _ExportState) -> None:
    st.names.clear()
    st.seen.clear()
    st.order.clear()
    st.exact = True
    st.ordered = st.kind != "set"
    st.computed = False
def _deref_binding(value, bindings, seen: frozenset[str], depth: int):
    while bindings and isinstance(value, ast.Name) and value.id in bindings:
        name = value.id
        if name in seen or depth > _STATIC_BINDING_MAX_DEPTH:
            return None, seen, depth
        binding = bindings[name]
        binding_pos = (getattr(binding, "lineno", 0),
                       getattr(binding, "col_offset", 0))
        value_pos = (getattr(value, "lineno", 0),
                     getattr(value, "col_offset", 0))
        if binding_pos > value_pos:
            return None, seen, depth
        value = binding
        seen = seen | {name}
        depth += 1
    return value, seen, depth
def _elt_export_elts(elts, bindings=None, seen: frozenset[str] = _EMPTY_EXPORT_SEEN,
                     depth: int = 0) -> tuple[list[str], bool]:
    names: list[str] = []
    exact = True
    for elt in elts:
        part = None
        if isinstance(elt, ast.Starred):
            part = resolve_export_elts(elt.value, bindings, seen, depth + 1)
        else:
            name = str_constant_value(elt)
            if name is not None:
                names.append(name)
                continue
        if part is None:
            exact = False
            continue
        names.extend(part[0])
        exact = exact and part[1]
    return names, exact
def resolve_export_elts(value, bindings=None,
                        seen: frozenset[str] = _EMPTY_EXPORT_SEEN,
                        depth: int = 0) -> tuple[list[str], bool] | None:
    if depth > _STATIC_BINDING_MAX_DEPTH:
        return None
    value, seen, depth = _deref_binding(value, bindings, seen, depth)
    if value is None:
        return None
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return _elt_export_elts(value.elts, bindings, seen, depth)
    if not isinstance(value, ast.BinOp):
        return None
    if isinstance(value.op, ast.Add):
        return _add_export_elts(value, bindings, seen, depth)
    if isinstance(value.op, ast.BitOr):
        return _union_export_elts(value, bindings, seen, depth)
    if isinstance(value.op, ast.Mult):
        return _repeat_export_elts(value, bindings, seen, depth)
    return None
def _add_export_elts(value: ast.BinOp, bindings=None,
                     seen: frozenset[str] = _EMPTY_EXPORT_SEEN,
                     depth: int = 0) -> tuple[list[str], bool]:
    stack: list[ast.expr] = [value]
    known: list[str] = []
    exact = True
    while stack:
        node = stack.pop()
        node, node_seen, node_depth = _deref_binding(node, bindings, seen, depth)
        if node is None:
            exact = False
            continue
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            stack.append(node.right)
            stack.append(node.left)
            continue
        part = resolve_export_elts(node, bindings, node_seen, node_depth)
        if part is None:
            exact = False
            continue
        known.extend(part[0])
        exact = exact and part[1]
    return known, exact
def _union_export_elts(value: ast.BinOp, bindings=None,
                       seen: frozenset[str] = _EMPTY_EXPORT_SEEN,
                       depth: int = 0) -> tuple[list[str], bool] | None:
    stack: list[ast.expr] = [value]
    known: list[str] = []
    deduped: set[str] = set()
    exact = True
    while stack:
        node = stack.pop()
        node, node_seen, node_depth = _deref_binding(node, bindings, seen, depth)
        if node is None:
            exact = False
            continue
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
            stack.append(node.right)
            stack.append(node.left)
            continue
        if isinstance(node, (ast.List, ast.Tuple, ast.Dict)):
            return None
        if isinstance(node, ast.Set):
            part_names, part_exact = _elt_export_elts(
                node.elts, bindings, node_seen, node_depth)
            known.extend(name for name in part_names
                         if name not in deduped and not deduped.add(name))
            exact = exact and part_exact
            continue
        exact = False
    return known, exact
def _repeat_export_elts(value: ast.BinOp, bindings=None,
                        seen: frozenset[str] = _EMPTY_EXPORT_SEEN,
                        depth: int = 0) -> tuple[list[str], bool] | None:
    left, left_seen, left_depth = _deref_binding(
        value.left, bindings, seen, depth)
    right, right_seen, right_depth = _deref_binding(
        value.right, bindings, seen, depth)
    seq_part = (resolve_export_elts(left, bindings, left_seen, left_depth)
                if left is not None else None)
    count = _literal_int(right) if right is not None else None
    if seq_part is None:
        seq_part = (resolve_export_elts(right, bindings, right_seen,
                                          right_depth)
                    if right is not None else None)
        count = _literal_int(left) if left is not None else None
    if seq_part is None:
        return None
    seq, seq_exact = seq_part
    if count is None:
        return list(seq), False
    if count <= 0:
        return [], True
    if count > _EXPORT_REPEAT_LIMIT:
        return list(seq), False
    return list(seq) * count, seq_exact
def _literal_export_elts(value: ast.expr,
                         bindings=None) -> tuple[list[str], bool]:
    resolved = resolve_export_elts(value, bindings)
    return resolved if resolved is not None else ([], False)
def _export_sequence_value(value: ast.expr | None,
                           bindings=None) -> list[str] | None:
    if value is None:
        return None
    resolved = resolve_export_elts(value, bindings)
    if resolved is None:
        return None
    names, exact = resolved
    return names if exact else None
def _is_all_clear_mutation(node: ast.stmt, roots) -> bool:
    if not isinstance(node, ast.Expr) or not isinstance(node.value, ast.Call):
        return False
    call = node.value
    func = call.func
    return (isinstance(func, ast.Attribute) and _root_name(func.value, roots)
            and func.attr == "clear" and not call.args and not call.keywords)
def _all_delete_binds_name(target: ast.AST, roots) -> bool:
    if isinstance(target, ast.Name):
        return target.id in roots
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_all_delete_binds_name(elt, roots) for elt in target.elts)
    return False
def _is_all_delete_name(node: ast.stmt, roots) -> bool:
    return isinstance(node, ast.Delete) and any(
        _all_delete_binds_name(target, roots) for target in node.targets)
def _literal_int(node: ast.expr) -> int | None:
    if (isinstance(node, ast.Constant)
            and isinstance(node.value, int)
            and not isinstance(node.value, bool)):
        return node.value
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        operand = node.operand
        if (isinstance(operand, ast.Constant)
                and isinstance(operand.value, int)
                and not isinstance(operand.value, bool)):
            return operand.value if isinstance(node.op, ast.UAdd) else -operand.value
    return None
def _apply_all_removal(
    node: ast.stmt, st: _ExportState,
) -> tuple[set[str], bool] | None:
    if isinstance(node, ast.Delete):
        return _apply_all_delete(node, st)
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return None
    call = node.value
    func = call.func
    if not (isinstance(func, ast.Attribute) and _root_name(func.value, st.roots)):
        return None
    if func.attr == "remove":
        return _apply_all_remove_call(call, st)
    if func.attr == "discard":
        return _apply_all_discard_call(call, st)
    if func.attr == "pop":
        return _apply_all_pop_call(call, st)
    return None
def _apply_all_remove_call(
    call: ast.Call, st: _ExportState,
) -> tuple[set[str], bool]:
    if (st.kind not in (None, "list", "set")
            or call.keywords or len(call.args) != 1):
        return set(), False
    if not st.exact or not (st.ordered or st.kind == "set"):
        return set(), False
    arg = call.args[0]
    if not (isinstance(arg, ast.Constant) and isinstance(arg.value, str)):
        return set(), False
    if st.ordered:
        try:
            st.order.remove(arg.value)
        except ValueError as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc,
                context='_apply_all_remove_call:ValueError')
    return {arg.value}, True
def _apply_all_discard_call(
    call: ast.Call, st: _ExportState,
) -> tuple[set[str], bool]:
    if st.kind != "set" or call.keywords or len(call.args) != 1 or not st.exact:
        return set(), False
    arg = call.args[0]
    if not (isinstance(arg, ast.Constant) and isinstance(arg.value, str)):
        return set(), False
    return {arg.value}, True
def _apply_all_pop_call(
    call: ast.Call, st: _ExportState,
) -> tuple[set[str], bool]:
    if st.kind != "list" or call.keywords or not st.exact or not st.ordered:
        return set(), False
    if not call.args:
        stored = st.order.pop() if st.order else None
        return ({stored}, True) if stored is not None else (set(), True)
    if len(call.args) != 1:
        return set(), False
    idx = _literal_int(call.args[0])
    if idx is None:
        return set(), False
    if -len(st.order) <= idx < len(st.order):
        return {st.order.pop(idx)}, True
    return set(), True
def _apply_all_delete(
    node: ast.Delete, st: _ExportState,
) -> tuple[set[str], bool] | None:
    removed: set[str] = set()
    known = True
    found = False
    for target in node.targets:
        if not (isinstance(target, ast.Subscript)
                and _root_name(target.value, st.roots)):
            continue
        found = True
        if not st.exact or not st.ordered:
            known = False
            continue
        slice_node = target.slice
        if (isinstance(slice_node, ast.Slice)
                and slice_node.lower is None
                and slice_node.upper is None
                and slice_node.step is None):
            removed.update(st.order)
            st.order.clear()
            continue
        idx = _literal_int(slice_node)
        if idx is not None:
            if -len(st.order) <= idx < len(st.order):
                removed.add(st.order.pop(idx))
            continue
        known = False
    return (removed, known) if found else None
def _all_insert_op(node: ast.stmt, roots):
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return None
    call = node.value
    func = call.func
    if not (isinstance(func, ast.Attribute) and func.attr == "insert"
            and _root_name(func.value, roots)):
        return None
    if len(call.args) != 2 or call.keywords:
        return False
    index = _literal_int(call.args[0])
    if index is None:
        return False
    arg = call.args[1]
    if isinstance(arg, ast.Constant):
        return (index, arg.value) if isinstance(arg.value, str) else "skip"
    return False
def _all_insert_name(node: ast.stmt) -> str | None:
    call = node.value
    if not isinstance(call, ast.Call):
        return None
    if len(call.args) != 2 or call.keywords:
        return None
    arg = call.args[1]
    if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
        return arg.value
    return None
def _apply_all_insert(node: ast.stmt, st: _ExportState) -> bool:
    if st.kind not in (None, "list"):
        return False
    op = _all_insert_op(node, st.roots)
    if op is None:
        return False
    if op is False:
        name = _all_insert_name(node)
        if name is not None:
            st.names.add(name)
            st.seen.add(name)
        _degrade_export_state(st)
        return True
    if op == "skip":
        _degrade_export_state(st)
        return True
    index, name = op
    pos = index if index >= 0 else len(st.order) + index
    pos = max(0, min(pos, len(st.order)))
    if st.ordered:
        st.order.insert(pos, name)
    st.names.add(name)
    st.seen.add(name)
    return True
def _all_mutation_elts(
        node: ast.stmt, st: _ExportState
) -> tuple[list[str], bool, bool] | None:
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return None
    call = node.value
    func = call.func
    if not isinstance(func, ast.Attribute) or not _root_name(func.value, st.roots):
        return None
    if st.kind not in (None, "list"):
        return None
    if func.attr not in ("append", "extend") or call.keywords:
        return None
    if len(call.args) != 1:
        return [], False, False
    value = call.args[0]
    if func.attr == "append":
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            return [value.value], True, True
        return [], False, False
    elts, literal = _literal_export_elts(value, st.bindings)
    return elts, literal, _value_order_known(value, st.bindings)
def _all_assignment_targets(node: ast.stmt) -> list[ast.expr] | None:
    if isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add):
        return [node.target]
    parts = assign_targets_value(node)
    return list(parts[0]) if parts is not None else None
def _all_assignment_value(node: ast.stmt) -> ast.expr | None:
    targets = _all_assignment_targets(node)
    if targets is None or not any(is_all_target(t) for t in targets):
        return None
    return node.value
def _target_contains(target: ast.AST, predicate: Callable[[ast.AST], bool]) -> bool:
    if predicate(target):
        return True
    if isinstance(target, (ast.Tuple, ast.List)):
        return any(_target_contains(elt, predicate) for elt in target.elts)
    if isinstance(target, ast.Starred):
        return _target_contains(target.value, predicate)
    return False
def _nested_all_write(node: ast.stmt,
                      predicate: Callable[[ast.AST], bool]) -> bool:
    targets = _all_assignment_targets(node) or []
    return any(isinstance(target, (ast.Tuple, ast.List, ast.Starred))
               and _target_contains(target, predicate) for target in targets)
def _nested_all_subscript_assignment(node: ast.stmt, roots) -> bool:
    return _nested_all_write(
        node, lambda target: isinstance(target, ast.Subscript)
        and _root_name(target.value, roots))
def _all_subscript_target(node: ast.stmt,
                          roots) -> ast.Subscript | None:
    if isinstance(node, (ast.AugAssign, ast.AnnAssign)):
        targets: list[ast.expr] = [node.target]
    elif isinstance(node, ast.Assign):
        targets = list(node.targets)
    else:
        return None
    if len(targets) != 1 or not isinstance(targets[0], ast.Subscript):
        return None
    target = targets[0]
    return target if _root_name(target.value, roots) else None
def _all_subscript_rebuilt(
    st: _ExportState, target: ast.Subscript, value: ast.expr | None,
) -> list[str] | None:
    if st.kind not in (None, "list"):
        return None
    order = list(st.order) if st.exact and st.ordered else None
    index = _literal_int(target.slice)
    if index is not None:
        name = str_constant_value(value) if value is not None else None
        if order is None or name is None or not -len(order) <= index < len(order):
            return None
        order[index] = name
        return order
    slice_node = target.slice
    if not isinstance(slice_node, ast.Slice):
        return None
    replacement = _export_sequence_value(value, st.bindings)
    if replacement is None:
        return None
    if (slice_node.lower is None and slice_node.upper is None
            and slice_node.step is None):
        st.kind = "list"
        return replacement
    if order is None:
        return None
    bounds: list[int | None] = []
    for raw_bound in (slice_node.lower, slice_node.upper, slice_node.step):
        resolved = (_literal_int(raw_bound)
                    if raw_bound is not None else None)
        if raw_bound is not None and resolved is None:
            return None
        bounds.append(resolved)
    if bounds[2] == 0:
        return None
    start, stop, step = slice(*bounds).indices(len(order))
    if step == 1:
        tail = order[stop:] if stop > start else order[start:]
        return [*order[:start], *replacement, *tail]
    positions = list(range(start, stop, step))
    if len(positions) != len(replacement):
        return None
    for position, name in zip(positions, replacement, strict=True):
        order[position] = name
    return order
def _apply_all_subscript_assign(node: ast.stmt, st: _ExportState) -> bool:
    target = _all_subscript_target(node, st.roots)
    if target is None:
        if _nested_all_subscript_assignment(node, st.roots):
            _degrade_export_state(st)
            return True
        return False
    if isinstance(node, ast.AugAssign):
        _degrade_export_state(st)
        return True
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return True
    rebuilt = _all_subscript_rebuilt(st, target, node.value)
    if rebuilt is None:
        _degrade_export_state(st)
        return True
    order_known = _value_order_known(node.value, st.bindings)
    st.order = rebuilt if order_known else []
    st.names = set(rebuilt)
    st.seen = set(rebuilt)
    st.exact = True
    st.ordered = order_known
    return True
def _apply_all_reverse(call: ast.Call, st: _ExportState) -> None:
    if st.kind not in (None, "list") or call.args or call.keywords:
        return
    if st.exact and st.ordered:
        st.order.reverse()
    else:
        st.order = []
        st.ordered = False
def _apply_all_sort(call: ast.Call, st: _ExportState) -> None:
    if st.kind not in (None, "list") or call.args:
        return
    reverse = False
    dynamic_key = False
    for keyword in call.keywords:
        if keyword.arg == "key":
            dynamic_key = not (isinstance(keyword.value, ast.Constant)
                               and keyword.value.value is None)
            continue
        if keyword.arg != "reverse" or not isinstance(
                keyword.value, ast.Constant):
            _degrade_export_state(st)
            return
        reverse = bool(keyword.value.value)
    if not (st.exact and st.ordered):
        st.order = []
        st.ordered = False
        return
    st.order = sorted(st.order, reverse=reverse)
    if dynamic_key:
        st.order = []
        st.ordered = False
def _apply_all_sort_reverse(node: ast.stmt, st: _ExportState) -> bool:
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return False
    call = node.value
    func = call.func
    if not (isinstance(func, ast.Attribute) and _root_name(func.value, st.roots)):
        return False
    if func.attr == "reverse":
        _apply_all_reverse(call, st)
        return True
    if func.attr == "sort":
        _apply_all_sort(call, st)
        return True
    return False
def _all_augassign_applies(op: ast.operator, kind: str | None) -> bool:
    if isinstance(op, ast.Add):
        return kind in ("list", "tuple", None)
    if isinstance(op, (ast.BitOr, ast.Sub, ast.BitAnd, ast.BitXor)):
        return kind in ("set", None)
    if isinstance(op, ast.Mult):
        return kind in ("list", "tuple", None)
    return False
def _apply_all_augassign_op(op: ast.operator, st: _ExportState,
                            elts: list[str]) -> None:
    if isinstance(op, (ast.Add, ast.BitOr)):
        st.names.update(elts)
        st.seen.update(elts)
        if st.exact:
            st.order.extend(elts)
    elif isinstance(op, ast.Sub):
        st.names.difference_update(elts)
        st.seen.difference_update(elts)
        if st.exact:
            st.order[:] = [name for name in st.order if name in st.names]
    elif isinstance(op, ast.BitAnd):
        st.names.intersection_update(elts)
        st.seen.intersection_update(elts)
        if st.exact:
            st.order[:] = [name for name in st.order if name in st.names]
    else:
        st.names.symmetric_difference_update(elts)
        st.seen.symmetric_difference_update(elts)
        st.order = []
        st.ordered = False
def _apply_all_repeat(st: _ExportState, factor: ast.expr) -> None:
    count = _literal_int(factor)
    if count is None:
        _degrade_export_state(st)
        return
    if count <= 0:
        st.names.clear()
        st.seen.clear()
        st.order.clear()
        st.exact = True
        st.ordered = True
        st.computed = False
        return
    if count > 1:
        if len(st.order) * count <= _EXPORT_REPEAT_LIMIT:
            st.order = st.order * count
        else:
            st.order = []
            st.ordered = False
def _apply_all_augassign(node: ast.AugAssign, st: _ExportState) -> None:
    if not _all_augassign_applies(node.op, st.kind):
        if st.kind is None:
            _degrade_export_state(st)
        return
    if isinstance(node.op, ast.Mult):
        _apply_all_repeat(st, node.value)
        return
    elts, literal = _literal_export_elts(node.value, st.bindings)
    if isinstance(node.op, ast.BitAnd) and not literal:
        _degrade_export_state(st)
        return
    _apply_all_augassign_op(node.op, st, elts)
    if not literal:
        _degrade_export_state(st)
    elif st.exact and not _value_order_known(node.value, st.bindings):
        st.order = []
        st.ordered = False
def _apply_all_assignment(node: ast.stmt, st: _ExportState) -> bool:
    if _nested_all_write(node, is_all_target):
        _degrade_export_state(st)
        return True
    if isinstance(node, ast.AugAssign) and _root_name(node.target, st.roots):
        _apply_all_augassign(node, st)
        st.augmented = True
        return True
    value = _all_assignment_value(node)
    if value is None:
        return False
    if (st.declared and isinstance(value, ast.Name)
            and value.id in st.roots and value.id not in st.uncertain_roots):
        return True
    elts, literal = _literal_export_elts(value, st.bindings)
    st.kind = _container_kind(value)
    st.ordered = _value_order_known(value, st.bindings)
    if literal:
        st.names = set(elts)
        st.order = list(elts)
        st.exact = True
        st.seen = set(elts)
        st.computed = False
        st.augmented = False
    else:
        references_previous = any(
            isinstance(sub, ast.Name) and sub.id in st.roots
            for sub in _iter_surface_runtime_nodes(value))
        if not references_previous:
            st.names.clear()
            st.seen.clear()
            st.order.clear()
            st.augmented = False
        st.names.update(elts)
        if st.exact:
            st.order.extend(elts)
        st.seen.update(elts)
        _degrade_export_state(st)
    return True
def _iter_surface_runtime_nodes(
    node: ast.AST, *, include_class_body: bool = True,
    annotations_evaluated: bool = True,
):
    stack: list[tuple[ast.AST, bool]] = [(node, False)]
    while stack:
        current, in_class_body = stack.pop()
        yield current
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if annotations_evaluated:
                children = [*current.decorator_list, current.args]
                if current.returns is not None:
                    children.append(current.returns)
            else:
                children = definition_time_exprs(current)
        elif TYPE_ALIAS_NODES and isinstance(current, TYPE_ALIAS_NODES):
            children = [current.name]
        elif isinstance(current, ast.AnnAssign) and not annotations_evaluated:
            children = [current.target]
            if current.value is not None:
                children.append(current.value)
        elif isinstance(current, ast.Lambda):
            children = [current.args]
        elif isinstance(current, ast.ClassDef):
            children = [*current.decorator_list, *current.bases,
                        *current.keywords]
            if include_class_body:
                stack.extend(
                    (stmt, True) for stmt in reversed(current.body))
        else:
            children = [
                child for child in ast.iter_child_nodes(current)
                if in_class_body or not isinstance(child, ast.stmt)]
        stack.extend((child, in_class_body) for child in reversed(children))
def _readonly_shielded_ref_ids(call: ast.Call) -> set[int]:
    """嵌套在只读内建调用（len/sorted/tuple…）实参内的节点 id。

    ``logger.info("…%d 项导出", len(__all__))`` 这类留痕语句只读取导出面，
    其内层 ``__all__`` 引用不是潜在变异；若按外层调用的实参子树整体判定，
    会把静态 ``__all__`` 误降级为"不精确"，进而让符号 grounding 对该模块的
    全部未知符号放行。
    """
    shielded: set[int] = set()
    for sub in walk_nodes(call):
        if (not isinstance(sub, ast.Call) or sub is call
                or not isinstance(sub.func, ast.Name)
                or sub.func.id not in _ALL_NON_MUTATING_CALLS):
            continue
        for value in (*sub.args, *(kw.value for kw in sub.keywords)):
            shielded.add(id(value))
            shielded.update(id(ref) for ref in walk_nodes(value))
    return shielded


def _surface_call_side_effect(
    node: ast.stmt, roots, annotations_evaluated: bool = True,
    side_effect_calls: frozenset[int] | None = None,
) -> bool:
    for call in _iter_surface_runtime_nodes(
            node, annotations_evaluated=annotations_evaluated):
        if not isinstance(call, ast.Call):
            continue
        if side_effect_calls is not None and id(call) in side_effect_calls:
            return True
        func = call.func
        if (isinstance(func, ast.Name) and func.id == "getattr"
                and call.args and _root_name(call.args[0], roots)):
            method_name = (str_constant_value(call.args[1])
                           if len(call.args) >= 2 else None)
            if method_name not in _ALL_READONLY_METHODS:
                return True
            continue
        if isinstance(func, ast.Attribute) and _root_name(func.value, roots):
            if func.attr in _ALL_READONLY_METHODS:
                continue
            return True
        if isinstance(func, ast.Name) and func.id in _ALL_NON_MUTATING_CALLS:
            continue
        shielded = _readonly_shielded_ref_ids(call)
        if any(_root_name(ref, roots) and id(ref) not in shielded
               for arg in call.args for ref in walk_nodes(arg)):
            return True
        if any(_root_name(ref, roots) and id(ref) not in shielded
               for kw in call.keywords for ref in walk_nodes(kw.value)):
            return True
    return False
class _ExportWalkContext:
    __slots__ = ("_aliases", "_names", "_tree")
    def __init__(self, tree: ast.Module) -> None:
        self._tree = tree
        self._aliases: set[str] | None = None
        self._names: set[str] | None = None
    @property
    def typing_aliases(self) -> set[str]:
        if self._aliases is None:
            self._aliases = typing_guard_aliases(self._tree)
        return self._aliases
    @property
    def type_checking_names(self) -> set[str] | None:
        if self._names is None:
            self._names = typing_type_checking_names(self._tree) or None
        return self._names
def import_time_branch_visibility(
    test: ast.expr,
    typing_aliases: set[str] | None = None,
    type_checking_names: set[str] | None = None,
) -> bool | None:
    if isinstance(test, ast.Constant):
        return bool(test.value)
    if (isinstance(test, ast.UnaryOp)
            and isinstance(test.op, ast.Not)):
        inner = import_time_branch_visibility(
            test.operand, typing_aliases, type_checking_names)
        return None if inner is None else not inner
    if is_main_check(test) or is_type_checking_guard(
            test, typing_aliases, type_checking_names):
        return False
    main_branch = main_guard_branch(test)
    if main_branch is not None:
        return not main_branch
    return None
_EXPORT_SCOPE_BARRIERS = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)
def _static_empty_iterable(node: ast.AST) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and not node.value)


def _import_time_loop_visibility(
    node: ast.stmt, typing_aliases: set[str] | None = None,
    type_checking_names: set[str] | None = None,
) -> tuple[bool | None, bool | None]:
    if isinstance(node, ast.While):
        body_visible = import_time_branch_visibility(
            node.test, typing_aliases, type_checking_names)
        else_visible = (None if body_visible is None else not body_visible)
        return body_visible, else_visible
    if isinstance(node, ast.For) and _static_empty_iterable(node.iter):
        return False, True
    return None, None


def _export_child_stmts(node: ast.stmt, nested: bool, invisible: bool,
                        ctx: _ExportWalkContext) -> tuple:
    if isinstance(node, _EXPORT_SCOPE_BARRIERS):
        return ()
    if isinstance(node, ast.If):
        body_visible = import_time_branch_visibility(
            node.test, ctx.typing_aliases, ctx.type_checking_names)
        child_nested = nested or body_visible is None
        body_invisible = invisible or body_visible is False
        orelse_invisible = invisible or body_visible is True
        return tuple(
            [(stmt, child_nested, body_invisible) for stmt in node.body]
            + [(stmt, child_nested, orelse_invisible) for stmt in node.orelse])
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        body_visible, else_visible = _import_time_loop_visibility(
            node, ctx.typing_aliases, ctx.type_checking_names)
        return tuple(
            [(stmt, nested or body_visible is None,
              invisible or body_visible is False) for stmt in node.body]
            + [(stmt, nested or else_visible is None,
                invisible or else_visible is False) for stmt in node.orelse])
    if isinstance(node, _TRY_STMT_TYPES):
        conditional_blocks = [node.body]
        conditional_blocks.extend(handler.body for handler in node.handlers)
        conditional_blocks.append(node.orelse)
        return tuple(
            [(stmt, True, invisible)
             for block in conditional_blocks for stmt in block]
            + [(stmt, nested, invisible) for stmt in node.finalbody])
    return tuple((stmt, True, invisible)
                 for block in iter_module_stmt_blocks(node) for stmt in block)
def _iter_export_scope_stmts(tree: ast.Module,
                             ctx: _ExportWalkContext | None = None):
    ctx = ctx or _ExportWalkContext(tree)
    stack: list[tuple[ast.stmt, bool, bool]] = [
        (stmt, False, False) for stmt in reversed(tree.body)]
    while stack:
        node, nested, invisible = stack.pop()
        yield node, nested, invisible
        stack.extend(reversed(_export_child_stmts(
            node, nested, invisible, ctx)))
def _rebind_roots(node: ast.Assign | ast.AnnAssign | ast.NamedExpr,
                  st: _ExportState) -> None:
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    bound = {name for target in targets for name in binding_names_of(target)}
    bare = {target.id for target in targets if isinstance(target, ast.Name)}
    nested = bound - bare
    st.roots.difference_update(nested - _ALL_ROOTS)
    st.uncertain_roots.difference_update(nested)
    if not bare:
        return
    value = node.value
    value_root = isinstance(value, ast.Name) and value.id in st.roots
    if "__all__" in bare:
        if value_root and value.id not in st.uncertain_roots:
            st.roots |= bare | set(_ALL_ROOTS)
            st.uncertain_roots.difference_update(bare)
        else:
            st.roots = bare | set(_ALL_ROOTS)
            st.uncertain_roots.clear()
    elif value_root:
        st.roots |= bare
        st.uncertain_roots.difference_update(bare)
    else:
        st.roots -= bare
        st.uncertain_roots.difference_update(bare)
def _module_walrus_assignments(node: ast.stmt, annotations_evaluated: bool):
    """语句中会在模块执行期求值的海象赋值（函数体/lambda 体不计）。"""
    return (
        sub for sub in _iter_surface_runtime_nodes(
            node, annotations_evaluated=annotations_evaluated)
        if isinstance(sub, ast.NamedExpr) and isinstance(sub.target, ast.Name))
def _apply_export_core(node: ast.stmt, st: _ExportState) -> bool:
    if _is_all_clear_mutation(node, st.roots):
        _clear_export_state(st)
        st.augmented = False
        return True
    if _is_all_delete_name(node, _ALL_ROOTS):
        _clear_export_state(st)
        st.kind = None
        st.ordered = True
        st.augmented = False
        return True
    removal = _apply_all_removal(node, st)
    if removal is not None:
        removed, known = removal
        if known:
            st.names = (set(st.order) if st.exact and st.ordered
                        else st.names - removed)
            st.seen.difference_update(removed - st.names)
        else:
            _degrade_export_state(st)
        return True
    if _apply_all_insert(node, st):
        st.augmented = True
        return True
    mutation = _all_mutation_elts(node, st)
    if mutation is not None:
        elts, literal, order_known = mutation
        st.names.update(elts)
        st.seen.update(elts)
        if st.exact and order_known:
            st.order.extend(elts)
        elif st.exact:
            st.order = []
            st.ordered = False
        st.augmented = True
        if not literal:
            _degrade_export_state(st)
        return True
    if _apply_all_subscript_assign(node, st):
        return True
    if _apply_all_sort_reverse(node, st):
        return True
    if _apply_all_assignment(node, st):
        return True
    if _surface_call_side_effect(
            node, st.roots, st.annotations_evaluated, st.side_effect_calls):
        _degrade_export_state(st)
        return True
    return False
def _apply_export_stmt(node: ast.stmt, st: _ExportState) -> bool:
    tuple_target = (
        node.target
        if isinstance(node, ast.AugAssign)
        and isinstance(node.target, ast.Name)
        and node.target.id in st.roots and st.kind == "tuple"
        else None
    )
    if tuple_target is not None and not is_all_target(tuple_target):
        st.roots.discard(tuple_target.id)
        st.uncertain_roots.discard(tuple_target.id)
        return False
    applied = _apply_export_core(node, st)
    if tuple_target is not None:
        st.roots = set(_ALL_ROOTS)
        st.uncertain_roots.clear()
    if isinstance(node, (ast.Assign, ast.AnnAssign)):
        _rebind_roots(node, st)
    for _walrus in _module_walrus_assignments(
            node, st.annotations_evaluated):
        # 海象赋值在模块执行期同样改写绑定：目标若就是导出根本身，导出面
        # 已被整体重绑（降级为未知）；否则按别名登记/注销，使后续经别名的
        # 变异可见、经已注销别名的调用不再误判。
        if _walrus.target.id == "__all__":
            _degrade_export_state(st)
        _rebind_roots(_walrus, st)
    if isinstance(node, ast.Delete):
        deleted = {name for target in node.targets
                   for name in binding_names_of(target)}
        st.roots.difference_update(deleted - _ALL_ROOTS)
        st.uncertain_roots.difference_update(deleted)
    if not applied:
        return False
    if _is_all_delete_name(node, _ALL_ROOTS):
        st.declared = False
        st.empty_node = None
        return True
    st.declared = True
    if st.exact and not st.names:
        st.empty_node = node
    elif st.names:
        st.empty_node = None
    return True
def _export_target_roots(target: ast.AST) -> set[str]:
    if isinstance(target, ast.Name):
        return {target.id}
    if isinstance(target, ast.Subscript):
        return _export_target_roots(target.value)
    if isinstance(target, (ast.Tuple, ast.List)):
        return {name for elt in target.elts
                for name in _export_target_roots(elt)}
    if isinstance(target, ast.Starred):
        return _export_target_roots(target.value)
    return set()
def _export_subscript_roots(target: ast.AST) -> set[str]:
    if isinstance(target, ast.Subscript):
        return _export_target_roots(target.value)
    if isinstance(target, (ast.Tuple, ast.List)):
        return {name for elt in target.elts
                for name in _export_subscript_roots(elt)}
    if isinstance(target, ast.Starred):
        return _export_subscript_roots(target.value)
    return set()
def _export_stmt_roots(
    node: ast.stmt, annotations_evaluated: bool = True,
) -> set[str]:
    roots: set[str] = set()
    if isinstance(node, (ast.AugAssign, ast.Delete)):
        targets = node.targets if isinstance(node, ast.Delete) else [node.target]
        for target in targets:
            roots.update(_export_target_roots(target))
    elif isinstance(node, (ast.Assign, ast.AnnAssign)):
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        for target in targets:
            roots.update(_export_subscript_roots(target))
    for sub in _iter_surface_runtime_nodes(
            node, annotations_evaluated=annotations_evaluated):
        if not isinstance(sub, ast.Call):
            continue
        func = sub.func
        if isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
            roots.add(func.value.id)
        roots.update(arg.id for arg in sub.args if isinstance(arg, ast.Name))
        roots.update(kw.value.id for kw in sub.keywords
                     if isinstance(kw.value, ast.Name))
    return roots
def _merge_conditional_names(
    st: _ExportState, prev_names: set[str], prev_seen: set[str],
    prev_kind: str | None, prev_declared: bool,
) -> None:
    st.declared = st.declared or prev_declared
    st.exact = False
    st.order = []
    st.ordered = False
    st.names = prev_names | st.names
    st.seen = prev_seen | st.names
    st.kind = prev_kind
    if st.names:
        st.empty_node = None
def replay_export_surface(
    tree: ast.Module, *,
    branches: str = EXPORT_BRANCH_UNION,
    bindings: dict[str, ast.AST] | None = None,
    _entry_lines: dict[str, int] | None = None,
    _side_effect_calls: frozenset[int] | None = None,
) -> ExportReplay:
    if branches not in (EXPORT_BRANCH_UNION, EXPORT_BRANCH_ASSUME):
        raise ValueError(f"unknown export branch mode: {branches!r}")
    ctx = _ExportWalkContext(tree)
    st = _ExportState(
        names=set(), seen=set(), order=[], bindings=bindings,
        annotations_evaluated=not module_postpones_annotations(
            tree, require_absolute=True),
        side_effect_calls=frozenset(_side_effect_calls or ()))
    union = branches == EXPORT_BRANCH_UNION
    for node, nested, invisible in _iter_export_scope_stmts(tree, ctx):
        if invisible:
            continue
        if _entry_lines is not None:
            for name, line in _all_declared_entries(node, st.roots):
                _entry_lines[name] = line
        prev_names, prev_seen = set(st.names), set(st.seen)
        prev_kind, prev_roots = st.kind, set(st.roots)
        prev_declared = st.declared
        prev_uncertain = set(st.uncertain_roots)
        conditional_alias = bool(
            union and _export_stmt_roots(
                node, st.annotations_evaluated) & st.uncertain_roots)
        applied = _apply_export_stmt(node, st)
        if nested and union:
            branch_roots = set(st.roots)
            st.uncertain_roots = (
                prev_uncertain | st.uncertain_roots
                | (prev_roots ^ branch_roots)) - set(_ALL_ROOTS)
            st.roots = prev_roots | branch_roots | set(_ALL_ROOTS)
        if not applied:
            continue
        if not union or not (nested or conditional_alias):
            continue
        _merge_conditional_names(
            st, prev_names, prev_seen, prev_kind, prev_declared)
    return _state_replay(st)
def _collect_module_export_state(
    tree: ast.Module,
) -> tuple[set[str], list[str], bool]:
    replay = replay_export_surface(tree)
    _names, order, exact = set(replay.names), replay.names, replay.exact
    return _names, (list(order) if replay.ordered else []), exact
def collect_module_exports_state(tree: ast.Module) -> tuple[set[str], bool]:
    names, _order, exact = _collect_module_export_state(tree)
    return names, exact
def collect_module_exports_ordered(tree: ast.Module) -> tuple[list[str], bool]:
    names, order, exact = _collect_module_export_state(tree)
    if order:
        return list(dict.fromkeys(order)), exact
    return sorted(names), exact
_DYNAMIC_EXPORT_MARKERS = (
    "importlib.import_module", "globals().update", "globals()[")
_MODULE_REGISTRY_ASSIGN_RE = re.compile(
    r'^([A-Za-z_][A-Za-z0-9_]*)\s*(?::[^=\n]+)?=\s*[\[{(]',
    re.MULTILINE)
_MODULE_REGISTRY_TOKENS = frozenset({
    "known", "registry", "lazy", "exports", "table", "index", "map"})
_MODULE_REGISTRY_BARE_NAMES = frozenset({
    "modules", "module_list", "module_names"})
def _is_module_registry_target(name: str) -> bool:
    lowered = name.lower()
    bare = lowered.strip('_')
    if bare in _MODULE_REGISTRY_BARE_NAMES:
        return True
    return ("module" in lowered
            and any(token in lowered for token in _MODULE_REGISTRY_TOKENS))
def _is_globals_call(node: ast.AST | None) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "globals"
            and not node.args and not node.keywords)
def _has_dynamic_export_code(tree: ast.AST) -> bool:
    for node in walk_nodes(tree):
        if isinstance(node, ast.Call):
            func = node.func
            if (isinstance(func, ast.Attribute)
                    and func.attr == "import_module"
                    and isinstance(func.value, ast.Name)
                    and func.value.id == "importlib"):
                return True
            if (isinstance(func, ast.Attribute) and func.attr == "update"
                    and _is_globals_call(func.value)):
                return True
        elif isinstance(node, ast.Subscript) and _is_globals_call(node.value):
            return True
    return False
def _has_module_registry_table(tree: ast.AST) -> bool:
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        if not isinstance(node.value, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
            continue
        targets = (node.targets if isinstance(node, ast.Assign)
                   else [node.target])
        if any(isinstance(t, ast.Name) and _is_module_registry_target(t.id)
               for t in targets):
            return True
    return False
def _has_library_init_text_signature(content: str) -> bool:
    if any(marker in content for marker in _DYNAMIC_EXPORT_MARKERS):
        return True
    if any(_is_module_registry_target(m.group(1))
           for m in _MODULE_REGISTRY_ASSIGN_RE.finditer(content)):
        return True
    all_match = re.search(
        r'__all__\s*(?::[^=\n]+)?=\s*[\[\(](.*?)[\]\)]', content,
        re.DOTALL)
    if all_match:
        _all_seg = all_match.group(1)
        exports = (re.findall(r'"([^"]+)"', _all_seg)
                   + re.findall(r"'([^']+)'", _all_seg))
        if len(exports) > 10:
            return True
    module_def_count = len(
        re.findall(r'^[\t ]*(?:async\s+)?def\s+([^\W\d]\w*)', content,
                   re.MULTILINE))
    return module_def_count > 30
def has_library_init_signature(content: str) -> bool:
    if not isinstance(content, str):
        return False
    content = content.removeprefix("\ufeff")
    try:
        tree = parse_cached(content)
    except PARSE_DEGRADE_EXC as _exc:
        log_swallowed(
            __name__, _exc,
            context=f'has_library_init_signature:{type(_exc).__name__}')
        return _has_library_init_text_signature(content)
    if _has_dynamic_export_code(tree):
        return True
    if _has_module_registry_table(tree):
        return True
    if len(module_export_names(tree)) > 10:
        return True
    return len(list(iter_module_scope_funcdefs(tree))) > 30
def module_export_names(tree: ast.AST) -> set[str]:
    if not isinstance(tree, ast.Module):
        return set()
    names, _order, _exact = _collect_module_export_state(tree)
    return names
def init_export_surface(tree: ast.Module) -> tuple[set[str], set[str], set[str]]:
    class_defs: set[str] = set()
    import_names: set[str] = set()
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        if isinstance(node, ast.ClassDef):
            class_defs.add(node.name)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            import_names.update(import_stmt_binds(node))
    return module_export_names(tree), class_defs, import_names
_ALL_WRITE_METHODS = frozenset({
    "extend", "append", "insert", "remove", "discard", "pop", "clear",
    "sort", "reverse",
})
def _is_all_mutation_stmt(node: ast.stmt) -> bool:
    if (is_all_assignment(node) or _is_all_delete_name(node, _ALL_ROOTS)
            or _nested_all_write(node, is_all_target)
            or _nested_all_subscript_assignment(node, _ALL_ROOTS)):
        return True
    if _all_subscript_target(node, _ALL_ROOTS) is not None:
        return True
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
        func = node.value.func
        return (isinstance(func, ast.Attribute)
                and func.attr in _ALL_WRITE_METHODS
                and is_all_target(func.value))
    return False
def _is_reexport_stmt(
    stmt: ast.AST, found: list, ctx: _ExportWalkContext,
) -> bool:
    if isinstance(stmt, (ast.Import, ast.ImportFrom)):
        found.append(stmt)
        return True
    if (_is_all_mutation_stmt(stmt) or is_docstring_stmt(stmt)
            or is_placeholder_stmt(stmt)):
        return True
    if isinstance(stmt, ast.If):
        if not is_type_checking_guard(
                stmt.test, ctx.typing_aliases, ctx.type_checking_names):
            return False
        return all(_is_reexport_stmt(s, found, ctx) for s in (*stmt.body, *stmt.orelse))
    if isinstance(stmt, _TRY_STMT_TYPES):
        blocks = [stmt.body, stmt.orelse, stmt.finalbody]
        blocks.extend(handler.body for handler in stmt.handlers)
        return all(_is_reexport_stmt(s, found, ctx) for block in blocks for s in block)
    return False
def is_reexport_surface(tree: ast.AST) -> bool:
    # 不能以 ``module_export_names`` 作为前置门槛：无 ``__all__`` 的纯转发
    # 模块（如 ``from .core import main``）导出面为空，但确实是 facade；
    # 漏判会让盲点报告把其导出误标为「内部死代码」。
    if not isinstance(tree, ast.Module) or not tree.body:
        return False
    found: list = []
    ctx = _ExportWalkContext(tree)
    if not all(_is_reexport_stmt(stmt, found, ctx) for stmt in tree.body):
        return False
    return bool(found)
def first_line(text: str) -> str:
    if not text:
        return ""
    return text.split("\n", maxsplit=1)[0].strip()
def _default_repr(dv) -> str:
    if isinstance(dv, ast.Constant):
        return repr(dv.value)
    if isinstance(dv, ast.Name):
        return dv.id
    if (isinstance(dv, ast.UnaryOp)
            and isinstance(dv.op, (ast.USub, ast.UAdd))
            and isinstance(dv.operand, ast.Constant)
            and isinstance(dv.operand.value, (int, float, complex))
            and not isinstance(dv.operand.value, bool)):
        try:
            return ast.unparse(dv)
        except Exception as e:  # noqa: BLE001 — 默认值展示降级，不阻断扫描
            logger.warning("_default_repr: 默认值反解析失败: %s", e)
            return "..."
    if isinstance(dv, ast.Attribute):
        return _annotation_to_str(dv)
    return "..."
def _arg_spec(arg: ast.arg, default_val, kind: str) -> dict:
    return {
        "name": arg.arg,
        "type": _annotation_to_str(arg.annotation) if arg.annotation else None,
        "default": default_val,
        "kind": kind,
    }
def _extract_param_specs(node) -> list:
    params = []
    args_list = list(node.args.posonlyargs) + list(node.args.args)
    posonly_count = len(node.args.posonlyargs)
    defaults = list(node.args.defaults)
    default_offset = len(args_list) - len(defaults)
    for idx, arg in enumerate(args_list):
        default_val = None
        if idx >= default_offset:
            default_val = _default_repr(defaults[idx - default_offset])
        param = _arg_spec(arg, default_val, "positional")
        if idx < posonly_count:
            param["posonly"] = True
        params.append(param)
    if node.args.vararg:
        params.append(_arg_spec(node.args.vararg, None, "vararg"))
    for idx, arg in enumerate(node.args.kwonlyargs):
        kd = node.args.kw_defaults[idx]
        default_val = _default_repr(kd) if kd is not None else None
        params.append(_arg_spec(arg, default_val, "keyword"))
    if node.args.kwarg:
        params.append(_arg_spec(node.args.kwarg, None, "kwarg"))
    return params
def _decorator_call_name(dec: ast.Call) -> str | None:
    if isinstance(dec.func, ast.Name):
        return dec.func.id
    if isinstance(dec.func, ast.Attribute):
        return _annotation_to_str(dec.func)
    return None
def _decorator_name(dec) -> str | None:
    if isinstance(dec, ast.Name):
        return dec.id
    if isinstance(dec, ast.Attribute):
        return _annotation_to_str(dec)
    if isinstance(dec, ast.Call):
        return _decorator_call_name(dec)
    return None
def _extract_decorator_names(node) -> list:
    decorators = []
    for dec in node.decorator_list:
        name = _decorator_name(dec)
        if name is not None:
            decorators.append(name)
    return decorators
def extract_function_info(node) -> dict:
    func_doc = (ast.get_docstring(node) or "").strip()
    returns = None
    if node.returns:
        returns = _annotation_to_str(node.returns)
    return {
        "name": node.name,
        "doc": first_line(func_doc),
        "full_doc": func_doc,
        "params": _extract_param_specs(node),
        "returns": returns,
        "line": node.lineno,
        "decorators": _extract_decorator_names(node),
        "is_async": isinstance(node, ast.AsyncFunctionDef),
    }
def _extract_base_names(node) -> list:
    bases = []
    for base in node.bases:
        name = _annotation_to_str(base)
        if name and name != "...":
            bases.append(name)
    return bases
def _iter_class_binding_stmts(stmts):
    for stmt in stmts:
        yield stmt
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(stmt, _TRY_STMT_TYPES):
            yield from _iter_class_binding_stmts(stmt.body)
            for handler in stmt.handlers:
                yield from _iter_class_binding_stmts(handler.body)
                yield handler
            yield from _iter_class_binding_stmts(stmt.orelse)
            yield from _iter_class_binding_stmts(stmt.finalbody)
            continue
        for block in iter_module_stmt_blocks(stmt):
            yield from _iter_class_binding_stmts(block)
def _effective_class_method_nodes(node) -> list:
    methods = {}
    for child in _iter_class_binding_stmts(node.body):
        for name in _target_binding_names(child):
            methods.pop(name, None)
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
            methods[child.name] = child
        elif isinstance(child, ast.ClassDef):
            methods.pop(child.name, None)
        elif isinstance(child, (ast.Import, ast.ImportFrom)):
            for name in import_stmt_binds(child):
                methods.pop(name, None)
        elif isinstance(child, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            for name in _assignment_binding_names(child):
                methods.pop(name, None)
        elif isinstance(child, ast.Delete):
            for target in child.targets:
                for name in binding_names_of(target):
                    methods.pop(name, None)
        elif isinstance(child, ast.ExceptHandler) and child.name:
            methods.pop(child.name, None)
    return list(methods.values())
def _extract_class_methods(node) -> tuple:
    public_methods = []
    all_methods = []
    for cn in _effective_class_method_nodes(node):
        all_methods.append(cn.name)
        if not cn.name.startswith("_"):
            mdoc = (ast.get_docstring(cn) or "").strip()
            public_methods.append({
                "name": cn.name,
                "doc": first_line(mdoc),
            })
    return public_methods, all_methods
def _extract_init_params(node) -> list:
    for child in reversed(_effective_class_method_nodes(node)):
        if child.name == "__init__":
            params = _extract_param_specs(child)
            if (not is_static_method(child)
                    and params and params[0].get("kind") == "positional"):
                return params[1:]
            return params
    return []
def extract_class_info(node) -> dict:
    cls_doc = (ast.get_docstring(node) or "").strip()
    bases = _extract_base_names(node)
    cls_public_methods, cls_all_methods = _extract_class_methods(node)
    return {
        "name": node.name,
        "doc": first_line(cls_doc),
        "full_doc": cls_doc,
        "line": node.lineno,
        "bases": bases,
        "public_methods": cls_public_methods,
        "all_methods": cls_all_methods,
        "init_params": _extract_init_params(node),
    }
def _collect_import_entries(node) -> tuple:
    if isinstance(node, ast.Import):
        return [alias.name for alias in node.names], []
    if isinstance(node, ast.ImportFrom):
        if not node.module:
            return [], [alias.name for alias in node.names
                        if alias.name != "*"]
        if node.level:
            return [], [node.module]
        return [node.module], []
    return [], []
def _replace_constants(module_constants: list, new_constants: list) -> None:
    index = {const["name"]: pos
             for pos, const in enumerate(module_constants)}
    for const in new_constants:
        pos = index.get(const["name"])
        if pos is None:
            index[const["name"]] = len(module_constants)
            module_constants.append(const)
        else:
            module_constants[pos] = const
def _root_prefixed_imports(module_names: list, import_root: str) -> list:
    if not isinstance(import_root, str) or not import_root:
        return []
    prefix = import_root + "."
    return [name for name in module_names
            if name == import_root or name.startswith(prefix)]
def _assignment_binding_names(node: ast.stmt) -> set[str]:
    if isinstance(node, ast.Assign):
        return {name for target in node.targets
                for name in binding_names_of(target)}
    if isinstance(node, ast.AnnAssign):
        return (binding_names_of(node.target)
                if node.value is not None else set())
    if isinstance(node, ast.AugAssign):
        return binding_names_of(node.target)
    return set()
def _target_binding_names(node: ast.stmt) -> set[str]:
    names: set[str] = set()
    if isinstance(node, (ast.For, ast.AsyncFor)):
        names |= binding_names_of(node.target)
    for item in getattr(node, "items", ()) or ():
        if item.optional_vars is not None:
            names |= binding_names_of(item.optional_vars)
    if isinstance(node, ast.Match):
        names.update(
            name for case in node.cases
            for name in iter_pattern_capture_names(case.pattern))
    names.update(
        sub.target.id
        for sub in _iter_surface_runtime_nodes(
            node, include_class_body=False)
        if isinstance(sub, ast.NamedExpr) and isinstance(sub.target, ast.Name))
    return names
def _drop_stale_constants(names: set[str], module_constants: list) -> None:
    module_constants[:] = [const for const in module_constants
                           if const.get("name") not in names]
def _drop_stale_bindings(names: set[str], symbols: dict,
                         module_constants: list) -> None:
    if not names:
        return
    for name in names:
        symbols.pop(name, None)
    _drop_stale_constants(names, module_constants)
def _module_constants_from_node(node) -> list[dict]:
    if isinstance(node, ast.AugAssign) or not isinstance(node.value, ast.Constant):
        return []
    val_str = repr(node.value.value)
    if len(val_str) > 80:
        val_str = val_str[:79] + "…"
    targets = node.targets if isinstance(node, ast.Assign) else [node.target]
    return [{"name": target.id, "value": val_str}
            for target in targets
            if isinstance(target, ast.Name) and target.id.isupper()
            and len(target.id) > 1 and not target.id.startswith("_")]
_MODULE_BINDING_STOP = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
                        ast.Lambda)
def _iter_module_bindings(tree: ast.Module):
    ctx = _ExportWalkContext(tree)
    stack = [(stmt, False, False) for stmt in reversed(tree.body)]
    while stack:
        node, _nested, invisible = stack.pop()
        if invisible:
            continue
        yield node
        if isinstance(node, (*_MODULE_BINDING_STOP, ast.ExceptHandler)):
            continue
        if isinstance(node, _TRY_STMT_TYPES):
            children = list(node.body)
            for handler in node.handlers:
                children.extend(handler.body)
                children.append(handler)
            children.extend(node.orelse)
            children.extend(node.finalbody)
            stack.extend((child, True, False) for child in reversed(children))
            continue
        stack.extend(reversed(_export_child_stmts(node, False, False, ctx)))
def collect_module_symbols(tree: ast.Module, import_root: str = "") -> tuple:
    symbols: dict[str, tuple[str, dict]] = {}
    top_level_imports = []
    internal_imports = []
    module_constants = []
    for node in _iter_module_bindings(tree):
        _drop_stale_bindings(
            _target_binding_names(node), symbols, module_constants)
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            _drop_stale_bindings(
                import_stmt_binds(node), symbols, module_constants)
            top_delta, internal_delta = _collect_import_entries(node)
            top_level_imports.extend(top_delta)
            internal_imports.extend(internal_delta)
            internal_imports.extend(
                _root_prefixed_imports(top_delta, import_root))
            continue
        if isinstance(node, ast.ExceptHandler):
            if node.name:
                _drop_stale_bindings({node.name}, symbols, module_constants)
            continue
        if isinstance(node, ast.Delete):
            _drop_stale_bindings(
                {name for target in node.targets
                 for name in binding_names_of(target)},
                symbols, module_constants)
            continue
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and not node.name.startswith("_")):
            _drop_stale_bindings({node.name}, symbols, module_constants)
            symbols[node.name] = ("function", extract_function_info(node))
            continue
        if isinstance(node, ast.ClassDef) and not node.name.startswith("_"):
            _drop_stale_bindings({node.name}, symbols, module_constants)
            symbols[node.name] = ("class", extract_class_info(node))
            continue
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            _drop_stale_bindings(
                _assignment_binding_names(node), symbols, module_constants)
            _replace_constants(
                module_constants, _module_constants_from_node(node))
            continue
        if isinstance(node, ast.AugAssign):
            _drop_stale_constants(
                _assignment_binding_names(node), module_constants)
    functions = [info for kind, info in symbols.values()
                 if kind == "function"]
    classes = [info for kind, info in symbols.values()
               if kind == "class"]
    exports, _exact = collect_module_exports_ordered(tree)
    return functions, classes, exports, top_level_imports, internal_imports, module_constants
def _annotation_to_str(node) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Constant):
        return ast.unparse(node)
    if isinstance(node, ast.Subscript):
        base = _annotation_to_str(node.value)
        try:
            sl = _annotation_to_str(node.slice)
            return f"{base}[{sl}]"
        except Exception as e:  # noqa: BLE001 — 切片转换失败降级，不阻断整体
            logger.warning("_annotation_to_str: 注解转字符串失败: %s", e)
            return base
    if isinstance(node, ast.Tuple):
        return ", ".join(_annotation_to_str(e) for e in node.elts)
    try:
        return ast.unparse(node)
    except Exception as e:  # noqa: BLE001 — unparse 失败降级返回占位符
        logger.warning("_annotation_to_str: ast.unparse失败: %s", e)
        return "..."
__all__ = [
    "ExportReplay",
    "collect_all_export_names",
    "collect_module_exports_ordered",
    "collect_module_exports_state",
    "collect_module_symbols",
    "dunder_all_node_names",
    "extract_all_augassign_strings",
    "extract_all_names",
    "extract_all_strings",
    "extract_class_info",
    "extract_function_info",
    "first_line",
    "has_library_init_signature",
    "init_export_surface",
    "is_all_assignment",
    "is_all_target",
    "is_reexport_surface",
    "iter_all_export_entries",
    "module_export_names",
    "replay_export_surface",
]
logger.info(
    "diag_shared_ast_surface L0 导出面回放·符号清单与定义信息已加载: %d 项导出",
    len(__all__))

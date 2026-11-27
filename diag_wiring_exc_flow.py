from __future__ import annotations

import ast
import builtins
import logging
import operator
from collections.abc import Iterator
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    MATCH_NODE_TYPES,
    TYPE_ALIAS_NODES,
    collect_param_names,
    import_alias_bound_names,
    is_class_shaped_exc_name,
    iter_arg_defaults,
    iter_own_nodes,
    iter_pattern_capture_names,
    iter_unpack_target_names,
    module_postpones_annotations,
    walk_stmts,
)
from jwsgj.diag_shared_ast_nodes import dotted_name as _dotted_name
from jwsgj.diag_shared_ast_views import parent_map
from jwsgj.diag_shared_source_core import (
    TRY_TYPES,
    extract_code_lines,
)
from jwsgj.diag_types_defs import (
    DiagnoseFinding,
    finding_scan_exempt,
)
from jwsgj.diag_types_vocab import (
    CAT_EXCEPTION_HANDLING,
)
from jwsgj.diag_wiring_exc import (
    _EMPTY_NAMES,
    _MATCH_CASE_TYPES,
    _collect_direct_frame_binds,
    _except_type_names,
    _iter_nodes_of_type,
    _iter_runtime_def_site_nodes,
    collect_frame_evidence,
    walk_handler_scope_frame_aware,
)
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    'check_EH04',
    'check_EH05',
    'check_EX04',
    'check_EX06',
    'check_EX07',
    'check_WC01',
    'enclosing_guaranteed_names',
]
_log = logging.getLogger(__name__)
_log.info(
    "diag_wiring_exc_flow 异常绑定流域已加载: %d 项导出",
    len(__all__))
_MATCH_AS_TYPES = ((ast.MatchAs,) if hasattr(ast, "MatchAs") else ())
_MATCH_OR_TYPES = ((ast.MatchOr,) if hasattr(ast, "MatchOr") else ())
_SCOPE_BARRIER_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
                        ast.Lambda)
_DEFAULT_ANNOTATIONS_EVALUATED = False
_DEFAULT_ANNOTATIONS_POSTPONED = False
_LITERAL_COMPARE_OPS = (
    (ast.Eq, operator.eq), (ast.NotEq, operator.ne),
    (ast.Lt, operator.lt), (ast.LtE, operator.le),
    (ast.Gt, operator.gt), (ast.GtE, operator.ge),
    (ast.In, lambda left, right: left in right),
    (ast.NotIn, lambda left, right: left not in right),
)
def _literal_compare_truth(left, op, right) -> bool | None:
    try:
        left_value = ast.literal_eval(left)
        right_value = ast.literal_eval(right)
    except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):
        return None
    for op_type, compare in _LITERAL_COMPARE_OPS:
        if not isinstance(op, op_type):
            continue
        try:
            return bool(compare(left_value, right_value))
        except (TypeError, ValueError, ArithmeticError, RecursionError):
            return None
    return None
def _guaranteed_compare_operands(node: ast.Compare) -> list:
    operands = [node.left]
    left = node.left
    for op, right in zip(node.ops, node.comparators, strict=True):
        operands.append(right)
        if _literal_compare_truth(left, op, right) is not True:
            break
        left = right
    return operands
def _child_stmt_containers(node) -> list:
    if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        return [node.body]
    if isinstance(node, (ast.If, ast.While, ast.For, ast.AsyncFor)):
        return [node.body, node.orelse]
    if isinstance(node, TRY_TYPES):
        return [node.body, node.orelse, node.finalbody,
                *(h.body for h in node.handlers)]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [node.body]
    if isinstance(node, MATCH_NODE_TYPES):
        return [c.body for c in node.cases]
    if isinstance(node, _MATCH_CASE_TYPES):
        return [node.body]
    if isinstance(node, ast.ExceptHandler):
        return [node.body]
    return []
def _const_truth(node):
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, ast.UnaryOp):
        return _const_unary_truth(node)
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        if any(isinstance(element, ast.Starred) for element in node.elts):
            return None
        return bool(node.elts)
    if isinstance(node, ast.Dict):
        if any(key is None for key in node.keys):
            return None
        return bool(node.keys)
    return None
def _const_unary_truth(node):
    if isinstance(node.op, ast.Not):
        inner = _const_truth(node.operand)
        return None if inner is None else not inner
    operand = node.operand
    if not (isinstance(operand, ast.Constant)
            and isinstance(operand.value, (int, float, complex))):
        return None
    if isinstance(node.op, ast.Invert):
        if not isinstance(operand.value, int) or isinstance(operand.value, bool):
            return None
        return bool(~operand.value)
    if isinstance(node.op, (ast.USub, ast.UAdd)):
        return bool(operand.value)
    return None
def _may_delete_names(stmts) -> frozenset:
    names: set = set()
    for sub in walk_stmts(stmts):
        if isinstance(sub, ast.Delete):
            for target in sub.targets:
                names.update(iter_unpack_target_names(target))
    return frozenset(names)
def _barrier_between(inner_seq) -> bool:
    return any(isinstance(node, _SCOPE_BARRIER_TYPES)
               for node in inner_seq)
def _nearest_scope_container(outer_chain):
    for anc in outer_chain:
        if isinstance(anc, ast.Module):
            return None
        if isinstance(anc, _SCOPE_BARRIER_TYPES):
            return anc
    return None
def _class_namespace_bind(outer_chain) -> bool:
    return isinstance(_nearest_scope_container(outer_chain), ast.ClassDef)
def _binds_reach_inner(outer: ast.AST, seq, idx: int) -> bool:
    if isinstance(outer, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        return True
    ancestors = seq[idx - 1::-1] if idx else ()
    if not (isinstance(outer, ast.ClassDef)
            or _class_namespace_bind(ancestors)):
        return True
    return not _barrier_between(seq[idx + 1:])
def _stmt_in(inner: ast.AST, stmts) -> bool:
    return any(stmt is inner for stmt in stmts)
def _range_literal_length(node) -> int | None:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "range"
            and not node.keywords
            and 1 <= len(node.args) <= 3):
        return None
    values: list[int] = []
    for arg in node.args:
        if not (isinstance(arg, ast.Constant)
                and isinstance(arg.value, int)
                and not isinstance(arg.value, bool)):
            return None
        values.append(arg.value)
    if len(values) == 1:
        start, stop, step = 0, values[0], 1
    elif len(values) == 2:
        start, stop, step = values[0], values[1], 1
    else:
        start, stop, step = values
    if step == 0:
        return None
    if step > 0:
        return max(0, (stop - start + step - 1) // step)
    return max(0, (start - stop - step - 1) // (-step))
def _definitely_empty_iter(node) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    length = _range_literal_length(node)
    if length is not None:
        return length == 0
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and not node.value)
def _definitely_nonempty_iter(node) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return bool(node.elts) and all(
            not isinstance(element, ast.Starred) for element in node.elts)
    if isinstance(node, ast.Dict):
        return bool(node.keys) and all(key is not None for key in node.keys)
    length = _range_literal_length(node)
    if length is not None:
        return length > 0
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and bool(node.value))
def _guaranteed_comprehension_walrus_names(node) -> frozenset:
    generators = getattr(node, 'generators', None) or ()
    if not generators:
        return frozenset()
    if isinstance(node, ast.GeneratorExp):
        return frozenset()
    names: set = set()
    for index, gen in enumerate(generators):
        if index:
            names |= _evaluated_walrus_names(gen.iter)
        if not _definitely_nonempty_iter(gen.iter):
            return frozenset(names)
        for cond in gen.ifs:
            names |= _evaluated_walrus_names(cond)
            if _const_truth(cond) is not True:
                return frozenset(names)
    if isinstance(node, ast.DictComp):
        names |= _evaluated_walrus_names(node.key)
        names |= _evaluated_walrus_names(node.value)
    else:
        names |= _evaluated_walrus_names(node.elt)
    return frozenset(names)
def _evaluated_walrus_names(node) -> frozenset:
    if node is None:
        return frozenset()
    if isinstance(node, ast.NamedExpr):
        inner = _evaluated_walrus_names(node.value)
        if isinstance(node.target, ast.Name):
            return frozenset((node.target.id,)) | inner
        return inner
    if isinstance(node, ast.BoolOp):
        return (_evaluated_walrus_names(node.values[0])
                if node.values else frozenset())
    if isinstance(node, ast.IfExp):
        return _evaluated_walrus_names(node.test)
    if isinstance(node, ast.Compare):
        names: set = set()
        for operand in _guaranteed_compare_operands(node):
            names |= _evaluated_walrus_names(operand)
        return frozenset(names)
    if isinstance(node, ast.Lambda):
        names: set = set()
        for default in iter_arg_defaults(node.args):
            names |= _evaluated_walrus_names(default)
        return frozenset(names)
    if isinstance(node, ast.GeneratorExp):
        return (_evaluated_walrus_names(node.generators[0].iter)
                if node.generators else frozenset())
    if isinstance(node, COMP_SCOPE_NODES):
        first_iter = (_evaluated_walrus_names(node.generators[0].iter)
                      if node.generators else frozenset())
        return first_iter | _guaranteed_comprehension_walrus_names(node)
    names = set()
    for sub in ast.iter_child_nodes(node):
        names |= _evaluated_walrus_names(sub)
    return frozenset(names)
def _path_intersection(paths) -> frozenset:
    merged: frozenset | None = None
    for path in paths:
        merged = path if merged is None else (merged & path)
    return merged or frozenset()
def _shortcut_branch_paths(branches, is_truthy: bool) -> list:
    anchor = 0 if is_truthy else 1
    paths: list = []
    prefix = frozenset()
    for pair in branches:
        paths.append(prefix | pair[anchor])
        prefix = prefix | pair[1 - anchor]
    return paths
def _branch_walrus_names(node) -> tuple[frozenset, frozenset]:
    if node is None:
        return frozenset(), frozenset()
    if isinstance(node, ast.NamedExpr):
        names = _evaluated_walrus_names(node)
        return names, names
    if isinstance(node, ast.BoolOp):
        branches = [_branch_walrus_names(value) for value in node.values]
        if not branches:
            return frozenset(), frozenset()
        if isinstance(node.op, ast.And):
            truthy = frozenset().union(*(names for names, _f in branches))
            return truthy, _path_intersection(
                _shortcut_branch_paths(branches, is_truthy=False))
        falsy = frozenset().union(*(names for _t, names in branches))
        return (_path_intersection(
            _shortcut_branch_paths(branches, is_truthy=True)), falsy)
    if isinstance(node, ast.Compare):
        falsy = _evaluated_walrus_names(node)
        truthy = set(falsy)
        for comparator in node.comparators[1:]:
            truthy |= _evaluated_walrus_names(comparator)
        return frozenset(truthy), falsy
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        truthy, falsy = _branch_walrus_names(node.operand)
        return falsy, truthy
    if isinstance(node, ast.IfExp):
        test_truthy, test_falsy = _branch_walrus_names(node.test)
        body_truthy, body_falsy = _branch_walrus_names(node.body)
        else_truthy, else_falsy = _branch_walrus_names(node.orelse)
        base = _evaluated_walrus_names(node.test)
        truthy = base | _path_intersection(
            [test_truthy | body_truthy, test_falsy | else_truthy])
        falsy = base | _path_intersection(
            [test_truthy | body_falsy, test_falsy | else_falsy])
        return truthy, falsy
    names = _evaluated_walrus_names(node)
    return names, names
def _match_case_header_binds(outer, inner) -> frozenset:
    for case in outer.cases:
        if case is inner or _stmt_in(inner, case.body):
            names = set(_evaluated_walrus_names(outer.subject))
            names.update(iter_pattern_capture_names(case.pattern))
            if case.guard is not None:
                names.update(_branch_walrus_names(case.guard)[0])
            return frozenset(names)
    return frozenset()
def _ancestor_header_binds(outer: ast.AST, inner: ast.AST) -> frozenset:
    if isinstance(outer, (ast.For, ast.AsyncFor)):
        if not _stmt_in(inner, outer.body):
            return frozenset()
        return (frozenset(list(iter_unpack_target_names(outer.target)))
                | _evaluated_walrus_names(outer.iter))
    if isinstance(outer, (ast.With, ast.AsyncWith)):
        if not _stmt_in(inner, outer.body):
            return frozenset()
        names: set = set()
        for item in outer.items:
            names |= _evaluated_walrus_names(item.context_expr)
            if item.optional_vars is not None:
                names.update(list(iter_unpack_target_names(item.optional_vars)))
        return frozenset(names)
    if isinstance(outer, (ast.If, ast.While)):
        if _stmt_in(inner, outer.body):
            return _branch_walrus_names(outer.test)[0]
        if _stmt_in(inner, outer.orelse):
            return _branch_walrus_names(outer.test)[1]
        return frozenset()
    if isinstance(outer, MATCH_NODE_TYPES):
        return _match_case_header_binds(outer, inner)
    return frozenset()
def _straightline_guaranteed_binds(chain) -> frozenset:
    binds: set = set()
    seq = list(reversed(chain))
    for _i in range(1, len(seq)):
        outer, inner = seq[_i - 1], seq[_i]
        if not _binds_reach_inner(outer, seq, _i - 1):
            continue
        binds |= _ancestor_header_binds(outer, inner)
        container = _container_holding(outer, inner)
        if container is None:
            continue
        flow = _HandlerFlow()
        for stmt in container:
            if stmt is inner:
                break
            _bound, _continues = flow._stmts([stmt], binds, None)
            binds = set(_bound)
            if not _continues:
                break
    return frozenset(binds)
def _container_holding(outer: ast.AST, inner: ast.AST) -> list | None:
    for cand in _child_stmt_containers(outer):
        if any(stmt is inner for stmt in cand):
            return cand
    return None
def _kills_name_del(sub: ast.AST, name: str, handler_line: int) -> bool:
    if not (isinstance(sub, ast.Delete) and sub.lineno < handler_line):
        return False
    return any(name in list(iter_unpack_target_names(t)) for t in sub.targets)
def _kills_name_rebind(sub: ast.AST, name: str, handler_line: int,
                        ancestor_ids: frozenset) -> bool:
    return (isinstance(sub, ast.ExceptHandler) and sub.name == name
            and sub.lineno < handler_line
            and id(sub) not in ancestor_ids)
def _enclosing_binding_killed(scope: ast.AST, name: str, handler_line: int,
                               ancestor_ids: frozenset) -> bool:
    for sub in iter_own_nodes(scope):
        if _kills_name_del(sub, name, handler_line):
            return True
        if _kills_name_rebind(sub, name, handler_line, ancestor_ids):
            return True
    return False
def _ancestor_chain(handler: ast.ExceptHandler,
                     parent_map: dict) -> list:
    chain = []
    cur = handler
    while True:
        cur = parent_map.get(cur)
        if cur is None:
            return chain
        chain.append(cur)
def _scope_candidate_names(scope: ast.AST) -> tuple:
    if isinstance(scope, ast.ExceptHandler):
        return (scope.name,) if scope.name else ()
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return tuple(collect_param_names(scope))
    return ()
def _candidate_bind_visible(scope: ast.AST, chain: list,
                            idx: int) -> bool:
    if not (isinstance(scope, ast.ExceptHandler)
            and _class_namespace_bind(chain[idx + 1:])):
        return True
    return not _barrier_between(chain[:idx])
def enclosing_guaranteed_names(handler: ast.ExceptHandler,
                                parent_map: dict) -> frozenset:
    chain = _ancestor_chain(handler, parent_map)
    ancestor_ids = frozenset(id(n) for n in chain)
    function_index = next(
        (index for index, node in enumerate(chain)
         if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))), None)
    function_locals = (
        _collect_direct_frame_binds(chain[function_index])
        if function_index is not None else frozenset())
    guaranteed: set = set()
    for _idx, scope in enumerate(chain):
        if not _candidate_bind_visible(scope, chain, _idx):
            continue
        candidates = _scope_candidate_names(scope)
        for name in candidates:
            if name in guaranteed:
                continue
            if (function_index is not None and _idx > function_index
                    and name in function_locals):
                continue
            if _enclosing_binding_killed(scope, name, handler.lineno,
                                         ancestor_ids):
                continue
            guaranteed.add(name)
    straightline = _straightline_guaranteed_binds(chain)
    if function_index is None:
        guaranteed |= straightline
    else:
        inner = _straightline_guaranteed_binds(
            chain[:function_index + 1])
        guaranteed |= inner
        guaranteed |= (straightline - inner) - function_locals
    return frozenset(guaranteed)
def _enclosing_global_names(handler: ast.ExceptHandler,
                            parent_map: dict) -> frozenset:
    chain = _ancestor_chain(handler, parent_map)
    module_index = next((idx for idx, node in enumerate(chain)
                         if isinstance(node, ast.Module)), None)
    if module_index is None:
        return frozenset()
    guaranteed = set(_straightline_guaranteed_binds(
        chain[max(module_index - 1, 0):]))
    ancestor_ids = frozenset(id(node) for node in chain)
    for index, scope in enumerate(chain[:module_index]):
        if not isinstance(scope, ast.ExceptHandler) or not scope.name:
            continue
        if any(isinstance(node, _SCOPE_BARRIER_TYPES)
               for node in chain[index + 1:module_index]):
            continue
        if not _enclosing_binding_killed(
                scope, scope.name, handler.lineno, ancestor_ids):
            guaranteed.add(scope.name)
    return frozenset(guaranteed)

def _enclosing_class_local_names(handler: ast.ExceptHandler,
                                 parent_map: dict) -> frozenset:
    scope = _nearest_scope_container(_ancestor_chain(handler, parent_map))
    return (_collect_direct_frame_binds(scope)
            if isinstance(scope, ast.ClassDef) else frozenset())

def _enclosing_function_local_names(handler: ast.ExceptHandler,
                                    parent_map: dict) -> frozenset:
    current = parent_map.get(handler)
    while current is not None:
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return _collect_direct_frame_binds(current)
        current = parent_map.get(current)
    return frozenset()
_EX_ERROR_NAME_CORES = frozenset(
    {"e", "err", "error", "ex", "exc", "exception"})
_EX_ERROR_NAME_FAMILY = _EX_ERROR_NAME_CORES | frozenset(
    "_" + _n for _n in _EX_ERROR_NAME_CORES)
def _is_irrefutable_pattern(pattern) -> bool:
    if isinstance(pattern, _MATCH_AS_TYPES):
        return (pattern.pattern is None
                or _is_irrefutable_pattern(pattern.pattern))
    if isinstance(pattern, _MATCH_OR_TYPES):
        return any(_is_irrefutable_pattern(sub) for sub in pattern.patterns)
    return False
def _merge_flow_paths(paths) -> tuple[set, bool]:
    live = [path for path in paths if path is not None]
    if not live:
        return set(), False
    merged = set(live[0])
    for path in live[1:]:
        merged &= path
    return merged, True
class _HandlerFlow:
    __slots__ = (
        '_annotations_postponed',
        '_annotations_stack',
        '_break_paths',
        '_class_bound',
        '_class_fallbacks',
        '_comp_depth',
        '_continue_paths',
        '_entry_bound',
        '_global_bound',
        '_unbound',
    )
    def __init__(self, *, annotations_evaluated: bool = _DEFAULT_ANNOTATIONS_EVALUATED,
                 annotations_postponed: bool = _DEFAULT_ANNOTATIONS_POSTPONED,
                 entry_bound: frozenset = _EMPTY_NAMES,
                 global_bound: frozenset = _EMPTY_NAMES,
                 class_bound: frozenset = _EMPTY_NAMES) -> None:
        self._annotations_stack = [annotations_evaluated]
        self._annotations_postponed = annotations_postponed
        self._entry_bound = entry_bound
        self._global_bound = global_bound
        self._class_bound = class_bound
        self._class_fallbacks: list = [None]
        self._comp_depth = 0
        self._break_paths: list[list[set]] = []
        self._continue_paths: list[list[set]] = []
        self._unbound: dict[str, list[int]] = {}
    def run(self, handler: ast.ExceptHandler) -> dict[str, list[int]]:
        initial = set(self._entry_bound)
        if handler.name:
            initial.add(handler.name)
        self._stmts(handler.body or (), initial, None)
        return {name: sorted(set(lines))
                for name, lines in self._unbound.items()}
    def _record(self, node: ast.Name, bound: set, outer) -> None:
        if node.id in bound:
            return
        if outer is not None and node.id in outer:
            return
        self._unbound.setdefault(node.id, []).append(node.lineno)
    def _eval(self, node, bound: set, outer) -> None:
        if node is None:
            return
        if isinstance(node, ast.Name):
            if isinstance(node.ctx, ast.Load):
                self._record(node, bound, outer)
            return
        if isinstance(node, ast.NamedExpr):
            self._eval(node.value, bound, outer)
            if isinstance(node.target, ast.Name):
                bound.add(node.target.id)
            return
        if isinstance(node, ast.Compare):
            self._eval_compare(node, bound, outer)
            return
        if isinstance(node, ast.BoolOp):
            self._eval_boolop(node, bound, outer)
            return
        if isinstance(node, ast.IfExp):
            self._eval_ifexp(node, bound, outer)
            return
        if self._eval_deferred(node, bound, outer):
            return
        if isinstance(node, ast.Dict):
            self._eval_dict(node, bound, outer)
            return
        for child in ast.iter_child_nodes(node):
            self._eval(child, bound, outer)
    def _eval_deferred(self, node, bound: set, outer) -> bool:
        if isinstance(node, ast.Lambda):
            for default in iter_arg_defaults(node.args):
                self._eval(default, bound, outer)
            return True
        if isinstance(node, ast.GeneratorExp):
            if node.generators:
                self._eval(node.generators[0].iter, bound, outer)
            return True
        if isinstance(node, COMP_SCOPE_NODES):
            self._eval_comprehension(node, bound, outer)
            return True
        return False
    def _eval_dict(self, node: ast.Dict, bound: set, outer) -> None:
        for key, value in zip(node.keys, node.values, strict=True):
            self._eval(key, bound, outer)
            self._eval(value, bound, outer)
    def _eval_compare(self, node: ast.Compare, bound: set, outer) -> None:
        guaranteed_count = len(_guaranteed_compare_operands(node))
        path = set(bound)
        self._eval(node.left, path, outer)
        guaranteed = set(path)
        left = node.left
        for index, (op, comparator) in enumerate(
                zip(node.ops, node.comparators, strict=True)):
            self._eval(comparator, path, outer)
            if index + 2 == guaranteed_count:
                guaranteed = set(path)
            if _literal_compare_truth(left, op, comparator) is False:
                break
            left = comparator
        bound.clear()
        bound.update(guaranteed)
    def _eval_boolop(self, node: ast.BoolOp, bound: set, outer) -> None:
        if not node.values:
            return
        is_and = isinstance(node.op, ast.And)
        reach = set(bound)
        result_paths: list[set] = []
        for index, sub in enumerate(node.values):
            before = set(reach)
            self._eval(sub, reach, outer)
            if index == len(node.values) - 1:
                result_paths.append(reach)
                break
            truthy, falsy = _branch_walrus_names(sub)
            short_circuit = falsy if is_and else truthy
            constant = _const_truth(sub)
            short_circuits = constant is not None and (
                (is_and and not constant) or (not is_and and constant))
            if constant is None or short_circuits:
                result_paths.append(before | short_circuit)
            if short_circuits:
                break
            reach = before | (truthy if is_and else falsy)
        merged = _path_intersection(result_paths)
        bound.clear()
        bound.update(merged)
    def _eval_ifexp(self, node: ast.IfExp, bound: set, outer) -> None:
        self._eval(node.test, bound, outer)
        constant = _const_truth(node.test)
        if constant is not None:
            branch = node.body if constant else node.orelse
            path_names = (_branch_walrus_names(node.test)[0] if constant
                          else _branch_walrus_names(node.test)[1])
            selected_bound = set(bound) | path_names
            self._eval(branch, selected_bound, outer)
            bound.clear()
            bound.update(selected_bound)
            return
        body_bound = set(bound) | _branch_walrus_names(node.test)[0]
        self._eval(node.body, body_bound, outer)
        else_bound = set(bound) | _branch_walrus_names(node.test)[1]
        self._eval(node.orelse, else_bound, outer)
        merged = body_bound & else_bound
        bound.clear()
        bound.update(merged)
    def _eval_comprehension(self, node, bound: set, outer) -> None:
        generators = node.generators
        if not generators:
            return
        self._eval(generators[0].iter, bound, outer)
        if _definitely_empty_iter(generators[0].iter):
            return
        local_names: set = set()
        for gen in generators:
            local_names.update(list(iter_unpack_target_names(gen.target)))
        if self._comp_depth:
            base = set(bound) | set(self._class_fallbacks[-1] or ())
        elif self._class_fallbacks[-1] is not None:
            base = set(self._class_fallbacks[-1])
        else:
            base = set(bound)
        frame_outer = base - local_names
        frame: set = set()
        self._comp_depth += 1
        try:
            for index, gen in enumerate(generators):
                if index:
                    self._eval(gen.iter, frame, frame_outer)
                    if _definitely_empty_iter(gen.iter):
                        return
                self._eval_target_loads(gen.target, frame, frame_outer)
                frame.update(list(iter_unpack_target_names(gen.target)))
                for condition in gen.ifs:
                    self._eval(condition, frame, frame_outer)
                    if _const_truth(condition) is False:
                        return
            if isinstance(node, ast.DictComp):
                self._eval(node.key, frame, frame_outer)
                self._eval(node.value, frame, frame_outer)
            else:
                self._eval(node.elt, frame, frame_outer)
        finally:
            self._comp_depth -= 1
            guaranteed = _guaranteed_comprehension_walrus_names(node)
            bound.update((frame - local_names) & guaranteed)
    def _stmts(self, stmts, bound: set, outer) -> tuple[set, bool]:
        current = set(bound)
        for stmt in stmts:
            current, continues = self._stmt(stmt, current, outer)
            if not continues:
                return current, False
        return current, True
    def _stmt(self, stmt, bound: set, outer) -> tuple[set, bool]:
        result = self._stmt_binding(stmt, bound, outer)
        if result is not None:
            return result
        result = self._stmt_control(stmt, bound, outer)
        if result is not None:
            return result
        return self._stmt_other(stmt, bound, outer)
    def _stmt_binding(self, stmt, bound: set, outer):
        result = self._stmt_assignment_binding(stmt, bound, outer)
        if result is not None:
            return result
        result = self._stmt_declaration_binding(stmt, bound, outer)
        if result is not None:
            return result
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            return self._with(stmt, bound, outer)
        return None
    def _stmt_assignment_binding(self, stmt, bound: set, outer):
        if isinstance(stmt, ast.Assign):
            self._eval(stmt.value, bound, outer)
            for target in stmt.targets:
                self._bind_target(target, bound, outer)
            return bound, True
        if isinstance(stmt, ast.AnnAssign):
            self._annassign(stmt, bound, outer)
            return bound, True
        if isinstance(stmt, ast.AugAssign):
            self._eval_aug_target(stmt.target, bound, outer)
            self._eval(stmt.value, bound, outer)
            if isinstance(stmt.target, ast.Name):
                bound.add(stmt.target.id)
            return bound, True
        if isinstance(stmt, ast.Delete):
            for target in stmt.targets:
                self._delete_target(target, bound, outer)
            return bound, True
        return None
    def _stmt_declaration_binding(self, stmt, bound: set, outer):
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            bound.update(import_alias_bound_names(stmt))
            return bound, True
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
            for site in _iter_runtime_def_site_nodes(
                    stmt, annotations_postponed=self._annotations_postponed):
                self._eval(site, bound, outer)
            bound.add(stmt.name)
            return bound, True
        if isinstance(stmt, ast.ClassDef):
            return bound, self._classdef(stmt, bound, outer)
        if TYPE_ALIAS_NODES and isinstance(stmt, TYPE_ALIAS_NODES):
            if isinstance(stmt.name, ast.Name):
                bound.add(stmt.name.id)
            return bound, True
        return None
    def _stmt_control(self, stmt, bound: set, outer):
        if isinstance(stmt, ast.If):
            return self._if(stmt, bound, outer)
        if isinstance(stmt, (ast.For, ast.AsyncFor)):
            return self._for(stmt, bound, outer)
        if isinstance(stmt, ast.While):
            return self._while(stmt, bound, outer)
        if isinstance(stmt, TRY_TYPES):
            return self._try(stmt, bound, outer)
        if MATCH_NODE_TYPES and isinstance(stmt, MATCH_NODE_TYPES):
            return self._match(stmt, bound, outer)
        return None
    def _stmt_other(self, stmt, bound: set, outer) -> tuple[set, bool]:
        if isinstance(stmt, ast.Return):
            self._eval(stmt.value, bound, outer)
            return bound, False
        if isinstance(stmt, ast.Raise):
            self._eval(stmt.exc, bound, outer)
            self._eval(stmt.cause, bound, outer)
            return bound, False
        if isinstance(stmt, ast.Break):
            if self._break_paths:
                self._break_paths[-1].append(set(bound))
            return bound, False
        if isinstance(stmt, ast.Continue):
            if self._continue_paths:
                self._continue_paths[-1].append(set(bound))
            return bound, False
        if isinstance(stmt, ast.Assert):
            self._eval(stmt.test, bound, outer)
            truth = _const_truth(stmt.test)
            if truth is not True:
                msg_bound = set(bound) | _branch_walrus_names(stmt.test)[1]
                self._eval(stmt.msg, msg_bound, outer)
            bound.update(_branch_walrus_names(stmt.test)[0])
            return bound, truth is not False
        if isinstance(stmt, ast.Expr):
            self._eval(stmt.value, bound, outer)
            return bound, True
        if isinstance(stmt, (ast.Global, ast.Nonlocal, ast.Pass)):
            return bound, True
        for child in ast.iter_child_nodes(stmt):
            self._eval(child, bound, outer)
        return bound, True
    def _eval_target_loads(self, target, bound: set, outer) -> None:
        if isinstance(target, ast.Name):
            return
        if isinstance(target, (ast.Tuple, ast.List)):
            for element in target.elts:
                self._eval_target_loads(element, bound, outer)
            return
        if isinstance(target, ast.Starred):
            self._eval_target_loads(target.value, bound, outer)
            return
        self._eval(target, bound, outer)
    def _bind_target(self, target, bound: set, outer) -> None:
        if isinstance(target, ast.Name):
            bound.add(target.id)
            return
        if isinstance(target, (ast.Tuple, ast.List)):
            for element in target.elts:
                self._bind_target(element, bound, outer)
            return
        if isinstance(target, ast.Starred):
            self._bind_target(target.value, bound, outer)
            return
        self._eval(target, bound, outer)
    def _delete_target(self, target, bound: set, outer) -> None:
        if isinstance(target, ast.Name):
            self._record(target, bound, outer)
            bound.discard(target.id)
            return
        if isinstance(target, (ast.Tuple, ast.List)):
            for element in target.elts:
                self._delete_target(element, bound, outer)
            return
        if isinstance(target, ast.Starred):
            self._delete_target(target.value, bound, outer)
            return
        self._eval(target, bound, outer)
    def _eval_aug_target(self, target, bound: set, outer) -> None:
        if isinstance(target, ast.Name):
            self._record(target, bound, outer)
            return
        self._eval(target, bound, outer)
    def _annassign(self, stmt: ast.AnnAssign, bound: set, outer) -> None:
        if stmt.value is not None:
            self._eval(stmt.value, bound, outer)
            if isinstance(stmt.target, ast.Name):
                bound.add(stmt.target.id)
            else:
                self._eval(stmt.target, bound, outer)
        else:
            self._eval_target_loads(stmt.target, bound, outer)
        if self._annotations_stack[-1]:
            self._eval(stmt.annotation, bound, outer)
    def _classdef(self, node: ast.ClassDef, bound: set, outer) -> bool:
        for decorator in node.decorator_list:
            self._eval(decorator, bound, outer)
        for base in node.bases:
            self._eval(base, bound, outer)
        for keyword in node.keywords:
            self._eval(keyword.value, bound, outer)
        fallback = (set(bound) if self._class_fallbacks[-1] is None
                    else set(self._class_fallbacks[-1]))
        fallback.difference_update(self._class_bound)
        local_names = _collect_direct_frame_binds(node)
        body_outer = (fallback - local_names) | self._global_bound
        self._class_fallbacks.append(body_outer)
        self._annotations_stack.append(not self._annotations_postponed)
        try:
            _body_bound, body_continues = self._stmts(
                node.body, set(), body_outer)
        finally:
            self._annotations_stack.pop()
            self._class_fallbacks.pop()
        if body_continues:
            bound.add(node.name)
        return body_continues
    def _with(self, stmt, bound: set, outer) -> tuple[set, bool]:
        for item in stmt.items:
            self._eval(item.context_expr, bound, outer)
            if item.optional_vars is not None:
                self._bind_target(item.optional_vars, bound, outer)
        body_bound, body_continues = self._stmts(stmt.body, bound, outer)
        return body_bound, body_continues
    def _if(self, stmt: ast.If, bound: set, outer) -> tuple[set, bool]:
        self._eval(stmt.test, bound, outer)
        truth = _const_truth(stmt.test)
        if truth is not None:
            if truth:
                taken = stmt.body
                names = _branch_walrus_names(stmt.test)[0]
            else:
                taken = stmt.orelse
                names = _branch_walrus_names(stmt.test)[1]
            return self._stmts(taken, set(bound) | names, outer)
        body_bound, body_continues = self._stmts(
            stmt.body, set(bound) | _branch_walrus_names(stmt.test)[0], outer)
        else_bound, else_continues = self._stmts(
            stmt.orelse, set(bound) | _branch_walrus_names(stmt.test)[1], outer)
        return _merge_flow_paths([
            body_bound if body_continues else None,
            else_bound if else_continues else None])
    def _for(self, stmt, bound: set, outer) -> tuple[set, bool]:
        self._eval(stmt.iter, bound, outer)
        if _definitely_empty_iter(stmt.iter):
            return self._stmts(stmt.orelse, set(bound), outer)
        self._eval_target_loads(stmt.target, bound, outer)
        body_entry = set(bound) | frozenset(iter_unpack_target_names(stmt.target))
        self._break_paths.append([])
        self._continue_paths.append([])
        try:
            body_bound, body_continues = self._stmts(
                stmt.body, body_entry, outer)
        finally:
            break_paths = self._break_paths.pop()
            continue_paths = self._continue_paths.pop()
        body_guaranteed = _definitely_nonempty_iter(stmt.iter)
        return self._loop_tail(
            stmt, bound, outer, body_bound, break_paths, continue_paths,
            body_continues, body_guaranteed=body_guaranteed)
    def _while(self, stmt: ast.While, bound: set, outer) -> tuple[set, bool]:
        self._eval(stmt.test, bound, outer)
        truth = _const_truth(stmt.test)
        if truth is False:
            return self._stmts(
                stmt.orelse, set(bound) | _branch_walrus_names(stmt.test)[1], outer)
        body_entry = set(bound) | _branch_walrus_names(stmt.test)[0]
        self._break_paths.append([])
        self._continue_paths.append([])
        try:
            body_bound, body_continues = self._stmts(
                stmt.body, body_entry, outer)
        finally:
            break_paths = self._break_paths.pop()
            continue_paths = self._continue_paths.pop()
        iteration_bound, has_iteration = _merge_flow_paths([
            body_bound if body_continues else None, *continue_paths])
        if has_iteration:
            self._eval(stmt.test, set(iteration_bound), outer)
        return self._loop_tail(
            stmt, bound, outer, body_bound, break_paths, continue_paths,
            body_continues, _branch_walrus_names(stmt.test)[1],
            body_guaranteed=(truth is True))
    def _loop_tail(self, stmt, bound: set, outer, body_bound: set,
                   break_paths: list[set], continue_paths: list[set],
                   body_continues: bool,
                   else_extra: frozenset = _EMPTY_NAMES, *,
                   body_guaranteed: bool = False) -> tuple[set, bool]:
        iteration_bound, _has_iteration = _merge_flow_paths([
            body_bound if body_continues else None, *continue_paths])
        deleted = _may_delete_names(stmt.body) - iteration_bound
        exhaustion_paths: list[set] = []
        if not body_guaranteed:
            exhaustion_paths.append(set(bound))
        if body_continues:
            exhaustion_paths.append(set(body_bound) - deleted)
        exhaustion_paths.extend(set(path) - deleted for path in continue_paths)
        if isinstance(stmt, ast.While) and _const_truth(stmt.test) is True:
            exhaustion_paths = []
        paths = list(break_paths)
        if exhaustion_paths:
            pre_else, _ = _merge_flow_paths(exhaustion_paths)
            else_bound, else_continues = self._stmts(
                stmt.orelse, pre_else | else_extra, outer)
            if else_continues:
                paths.append(else_bound)
        return _merge_flow_paths(paths)
    def _try_body(self, stmts, bound: set, outer) -> tuple[set, bool, set]:
        current = set(bound)
        continues = True
        exception_entries: set | None = None
        for stmt in stmts:
            if not _stmt_cannot_raise(stmt):
                refined = _compound_raise_entry(stmt, current)
                raise_entry = set(current) if refined is None else refined
                exception_entries = (
                    raise_entry if exception_entries is None
                    else exception_entries & raise_entry)
            current, continues = self._stmt(stmt, current, outer)
            if not continues:
                break
        if exception_entries is None:
            exception_entries = set(current)
        return current, continues, exception_entries
    def _try(self, stmt, bound: set, outer) -> tuple[set, bool]:
        entry = set(bound)
        break_marks = [len(paths) for paths in self._break_paths]
        continue_marks = [len(paths) for paths in self._continue_paths]
        body_may_raise = _try_body_may_raise(stmt)
        body_bound, body_continues, exception_entry = self._try_body(
            stmt.body, entry, outer)
        paths: list = []
        exit_paths: list = []
        for handler in (stmt.handlers if body_may_raise else ()):
            escape_marks = [
                (container, len(container))
                for container in (*self._break_paths, *self._continue_paths)
            ]
            handler_entry = set(exception_entry)
            self._eval(handler.type, handler_entry, outer)
            if handler.name:
                handler_entry.add(handler.name)
            handler_bound, handler_continues = self._stmts(
                handler.body, handler_entry, outer)
            if handler.name:
                handler_bound.discard(handler.name)
                for container, mark in escape_marks:
                    for path in container[mark:]:
                        path.discard(handler.name)
            exit_paths.append(handler_bound)
            if handler_continues:
                paths.append(handler_bound)
        normal = None
        if body_continues:
            if stmt.orelse:
                normal, normal_continues = self._stmts(
                    stmt.orelse, body_bound, outer)
                exit_paths.append(normal)
                if not normal_continues:
                    normal = None
            else:
                normal = body_bound
                exit_paths.append(body_bound)
        else:
            exit_paths.append(body_bound)
        if normal is not None:
            paths.append(normal)
        merged, has_path = _merge_flow_paths(paths)
        if not stmt.finalbody:
            if not has_path:
                return body_bound, False
            return merged, True
        pending_loop_paths = [
            (container, path)
            for containers, marks in (
                (self._break_paths, break_marks),
                (self._continue_paths, continue_marks),
            )
            for container, mark in zip(containers, marks, strict=True)
            for path in container[mark:]
        ]
        catches_all = not body_may_raise or any(
            handler.type is None
            or {"BaseException", "builtins.BaseException"}.intersection(
                _except_type_names(handler.type))
            for handler in stmt.handlers)
        if not catches_all:
            exit_paths.append(set(exception_entry))
        finally_entry, _has_exit = _merge_flow_paths(exit_paths)
        finally_bound, finally_continues = self._stmts(
            stmt.finalbody, finally_entry, outer)
        finally_deleted = _may_delete_names(stmt.finalbody)
        finally_added = ((finally_bound - finally_entry)
                         | (finally_bound & finally_deleted))
        for container, path in pending_loop_paths:
            if finally_continues:
                path.difference_update(finally_deleted)
                path.update(finally_added)
            else:
                container[:] = [
                    candidate for candidate in container
                    if candidate is not path
                ]
        if not has_path:
            return finally_bound, False
        continuing_bound = (merged - finally_deleted) | finally_added
        return continuing_bound, finally_continues
    def _match(self, stmt, bound: set, outer) -> tuple[set, bool]:
        self._eval(stmt.subject, bound, outer)
        paths: list = []
        fallthrough: list[set] = [set(bound)]
        for case in stmt.cases:
            if not fallthrough:
                break
            case_base = set(_path_intersection(fallthrough))
            self._eval(case.pattern, case_base, outer)
            case_entry = set(case_base) | frozenset(
                iter_pattern_capture_names(case.pattern))
            body_entry: set | None = case_entry
            guard_failure: set | None = None
            if case.guard is not None:
                self._eval(case.guard, case_entry, outer)
                truth = _const_truth(case.guard)
                truthy, falsy = _branch_walrus_names(case.guard)
                if truth is False:
                    body_entry = None
                    guard_failure = set(case_entry) | falsy
                else:
                    body_entry = set(case_entry) | truthy
                    if truth is None:
                        guard_failure = set(case_entry) | falsy
            if body_entry is not None:
                case_bound, case_continues = self._stmts(
                    case.body, body_entry, outer)
                if case_continues:
                    paths.append(case_bound)
            next_fallthrough: list[set] = []
            if not _is_irrefutable_pattern(case.pattern):
                next_fallthrough.append(case_base)
            if guard_failure is not None:
                next_fallthrough.append(guard_failure)
            fallthrough = next_fallthrough
        if fallthrough:
            paths.append(set(_path_intersection(fallthrough)))
        return _merge_flow_paths(paths)
def _handler_annotations_evaluated(handler: ast.ExceptHandler, tree: Any,
                                  parents_cache: list, *,
                                  annotations_postponed: bool = _DEFAULT_ANNOTATIONS_POSTPONED) -> bool:
    if annotations_postponed:
        return False
    if not any(isinstance(node, ast.AnnAssign)
               for node in walk_stmts(handler.body)):
        return False
    if parents_cache[0] is None:
        parents_cache[0] = parent_map(tree)
    parents = parents_cache[0]
    cur = parents.get(handler)
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            return False
        if isinstance(cur, (ast.Module, ast.ClassDef)):
            return True
        cur = parents.get(cur)
    return True
def _handler_in_module_scope(handler: ast.ExceptHandler, tree: Any,
                             parents_cache: list) -> bool:
    if parents_cache[0] is None:
        parents_cache[0] = parent_map(tree)
    cur = parents_cache[0].get(handler)
    while cur is not None:
        if isinstance(cur, ast.Module):
            return True
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda, ast.ClassDef)):
            return False
        cur = parents_cache[0].get(cur)
    return True
def _safe_hashable_literal_expr(node) -> bool:
    if isinstance(node, ast.Constant):
        try:
            hash(node.value)
        except TypeError:
            return False
        return True
    if isinstance(node, ast.Tuple):
        return all(not isinstance(element, ast.Starred)
                   and _safe_hashable_literal_expr(element)
                   for element in node.elts)
    if isinstance(node, ast.UnaryOp):
        return _safe_literal_expr(node)
    return False
def _safe_literal_expr(node) -> bool:
    if isinstance(node, ast.Constant):
        return True
    if isinstance(node, (ast.Tuple, ast.List)):
        return all(not isinstance(element, ast.Starred)
                   and _safe_literal_expr(element)
                   for element in node.elts)
    if isinstance(node, ast.Set):
        return all(not isinstance(element, ast.Starred)
                   and _safe_hashable_literal_expr(element)
                   for element in node.elts)
    if isinstance(node, ast.Dict):
        return all(key is not None
                   and _safe_hashable_literal_expr(key)
                   and _safe_literal_expr(value)
                   for key, value in zip(node.keys, node.values, strict=True))
    if isinstance(node, ast.UnaryOp):
        if isinstance(node.op, ast.Not):
            return _safe_literal_expr(node.operand)
        if isinstance(node.op, ast.Invert):
            return (isinstance(node.operand, ast.Constant)
                    and isinstance(node.operand.value, int)
                    and not isinstance(node.operand.value, bool))
        if isinstance(node.op, (ast.USub, ast.UAdd)):
            if isinstance(node.operand, ast.UnaryOp):
                return _safe_literal_expr(node.operand)
            return (isinstance(node.operand, ast.Constant)
                    and isinstance(node.operand.value, (int, float, complex)))
    return False
def _safe_assign_targets(targets, value) -> bool:
    if not targets:
        return False
    if all(isinstance(target, ast.Name) for target in targets):
        return _safe_literal_expr(value)
    if (len(targets) == 1
            and isinstance(targets[0], (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(targets[0].elts) == len(value.elts)
            and all(isinstance(element, ast.Name)
                    for element in targets[0].elts)):
        return all(_safe_literal_expr(element) for element in value.elts)
    return False
def _stmt_cannot_raise(stmt) -> bool:
    if isinstance(stmt, (ast.Pass, ast.Global, ast.Nonlocal,
                         ast.Break, ast.Continue)):
        return True
    if isinstance(stmt, ast.Assign):
        return _safe_assign_targets(stmt.targets, stmt.value)
    if isinstance(stmt, ast.Return):
        return stmt.value is None or _safe_literal_expr(stmt.value)
    if isinstance(stmt, ast.Expr):
        return _safe_literal_expr(stmt.value)
    if isinstance(stmt, ast.Assert):
        return (_safe_literal_expr(stmt.test)
                and _const_truth(stmt.test) is True)
    return False
def _try_body_may_raise(stmt: ast.AST) -> bool:
    return any(not _stmt_cannot_raise(child) for child in stmt.body)
def _pure_name_target(target) -> bool:
    if isinstance(target, ast.Name):
        return True
    if isinstance(target, (ast.Tuple, ast.List)):
        return all(_pure_name_target(element) for element in target.elts)
    return (isinstance(target, ast.Starred)
            and _pure_name_target(target.value))
def _expr_cannot_raise(node) -> bool:
    if _safe_literal_expr(node):
        return True
    return (isinstance(node, ast.NamedExpr)
            and _expr_cannot_raise(node.value))
def _compound_raise_entry(stmt, current: set) -> set | None:
    """复合语句内部 raise 点的确定绑定集；头部表达式可能抛出时无法精化，
    返回 None 由调用方退回语句执行前的绑定集。"""
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        if not (_expr_cannot_raise(stmt.iter)
                and _pure_name_target(stmt.target)):
            return None
        if _definitely_empty_iter(stmt.iter):
            return set(current)
        if not _definitely_nonempty_iter(stmt.iter):
            return None
        return set(current) | frozenset(
            iter_unpack_target_names(stmt.target))
    if isinstance(stmt, ast.If) and _expr_cannot_raise(stmt.test):
        truthy, falsy = _branch_walrus_names(stmt.test)
        body_entry = set(current) | truthy
        else_entry = set(current) | falsy
        if not stmt.orelse:
            return body_entry
        if not stmt.body:
            return else_entry
        return body_entry & else_entry
    return None
def _try_body_entry_bound(handler: ast.ExceptHandler,
                          parent_map: dict) -> frozenset:
    try_stmt = parent_map.get(handler)
    if not isinstance(try_stmt, TRY_TYPES):
        return frozenset()
    current = set(enclosing_guaranteed_names(handler, parent_map))
    flow = _HandlerFlow()
    _current, _continues, definite = flow._try_body(
        try_stmt.body, current, None)
    return frozenset(definite)
def _matched_unbound_names(
        node: ast.ExceptHandler, tree: Any, *,
        candidate_names: Any, parents_cache: list,
        annotations_evaluated: bool,
        annotations_postponed: bool) -> set:
    if parents_cache[0] is None:
        parents_cache[0] = parent_map(tree)
    try_stmt = parents_cache[0].get(node)
    if isinstance(try_stmt, TRY_TYPES) and not _try_body_may_raise(try_stmt):
        return set()
    global_bound = (_enclosing_global_names(node, parents_cache[0])
                    - _enclosing_function_local_names(
                        node, parents_cache[0]))
    class_bound = _enclosing_class_local_names(node, parents_cache[0])
    unbound_loads = _HandlerFlow(
        annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed,
        global_bound=global_bound,
        class_bound=class_bound).run(node)
    matched = set(unbound_loads) & set(candidate_names)
    if not matched:
        return set()
    entry_bound = (enclosing_guaranteed_names(node, parents_cache[0])
                   | _try_body_entry_bound(node, parents_cache[0]))
    if not (entry_bound & matched):
        return matched
    return set(_HandlerFlow(
        annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed,
        entry_bound=entry_bound,
        global_bound=global_bound,
        class_bound=class_bound).run(node)) & set(candidate_names)
def check_EX06(tree: Any, source: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_EX06 执行")
    issues = []
    if tree is None:
        return issues
    _parents_cache: list = [None]
    annotations_postponed = module_postpones_annotations(tree)
    for node in _iter_nodes_of_type(tree, ast.ExceptHandler):
        if node.name is not None:
            continue
        matched = _matched_unbound_names(
            node, tree, candidate_names=_EX_ERROR_NAME_FAMILY,
            parents_cache=_parents_cache,
            annotations_evaluated=_handler_annotations_evaluated(
                node, tree, _parents_cache,
                annotations_postponed=annotations_postponed),
            annotations_postponed=annotations_postponed)
        if not matched:
            continue
        issues.append(_make_ex06_issue(
            node, matched, source, filepath))
    return issues
def _make_ex06_issue(node: ast.ExceptHandler, matched: set,
                     source: Any, filepath: Any) -> dict:
    return {
        "rule_id": "EX-06", "severity": "P0", "dimension": CAT_EXCEPTION_HANDLING,
        "file": filepath, "line": node.lineno,
        "title": f"except 子句缺少 as 绑定但块内引用 '{min(matched)}'",
        "description": (
            f"except 子句未绑定异常名, 块内却引用了 {', '.join(sorted(matched))} 变量,"
            "运行时触发 NameError. 检测面覆盖任意具名异常类型"
            "(Name/Attribute/元组，含窄类型)，文案不限定捕获类型."
        ),
        "code_snippet": extract_code_lines(source, node.lineno),
        "suggestion": '根因: 代码使用了不规范或有风险的实现方式。该问题属于异常处理类别。\n修复策略: 为 except 子句补上 as 绑定(如 except <捕获类型> as e:) 并确保块内使用正确的变量名.\n参考标准: PEP 8 / pylint W07xx',
        "rule_ref": "sc0617",
    }
def _ex07_alias_names(bound_name: str) -> frozenset:
    core = bound_name.lstrip("_")
    if core in _EX_ERROR_NAME_CORES:
        return _EX_ERROR_NAME_FAMILY - {bound_name}
    if bound_name.startswith("_"):
        unadorned = bound_name[1:]
        return frozenset({unadorned}) if unadorned else frozenset()
    return frozenset({"_" + bound_name})
def _nested_rebind_selfkill_line(
        handler: ast.ExceptHandler, bound_name: str,
        load_lines: dict[str, list[int]], *,
        annotations_evaluated: bool = _DEFAULT_ANNOTATIONS_EVALUATED,
        annotations_postponed: bool = _DEFAULT_ANNOTATIONS_POSTPONED
        ) -> int | None:
    ref_lines = load_lines.get(bound_name, ())
    if not ref_lines:
        return None
    flow = _HandlerFlow(
        annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed)
    flow_unbound = frozenset(flow.run(handler).get(bound_name, ()))
    for sub in walk_stmts(handler.body):
        if not isinstance(sub, ast.ExceptHandler) or sub.name != bound_name:
            continue
        block_end = getattr(sub, 'end_lineno', sub.lineno)
        killed = min((ln for ln in ref_lines
                      if ln > block_end and ln in flow_unbound),
                     default=None)
        if killed is not None:
            return killed
    return None
def check_EX07(tree: Any, source: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_EX07 执行")
    issues = []
    if tree is None:
        return issues
    _parents_cache: list = [None]
    annotations_postponed = module_postpones_annotations(tree)
    for node in _iter_nodes_of_type(tree, ast.ExceptHandler):
        if node.name is None:
            continue
        issues.extend(_ex07_handler_issues(
            node, tree, _parents_cache, source, filepath,
            annotations_postponed=annotations_postponed))
    return issues
def _ex07_handler_issues(node: ast.ExceptHandler, tree: Any,
                         parents_cache: list, source: Any, filepath: Any, *,
                         annotations_postponed: bool = _DEFAULT_ANNOTATIONS_POSTPONED) -> list:
    bound_name = node.name
    annotations_evaluated = _handler_annotations_evaluated(
        node, tree, parents_cache,
        annotations_postponed=annotations_postponed)
    evidence = collect_frame_evidence(
        node, annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed,
        module_scope=_handler_in_module_scope(node, tree, parents_cache))
    suspicious = _matched_unbound_names(
        node, tree, candidate_names=_ex07_alias_names(bound_name),
        parents_cache=parents_cache,
        annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed)
    selfkill_line = _nested_rebind_selfkill_line(
        node, bound_name, evidence[1],
        annotations_evaluated=annotations_evaluated,
        annotations_postponed=annotations_postponed)
    out: list = []
    if suspicious:
        out.append(_make_ex07_alias_issue(
            node, bound_name, suspicious, source, filepath))
    if selfkill_line is not None:
        out.append(_make_ex07_selfkill_issue(
            bound_name, selfkill_line, source, filepath))
    return out
def _make_ex07_alias_issue(node: ast.ExceptHandler, bound_name: str,
                           suspicious: set, source: Any,
                           filepath: Any) -> dict:
    return {
        "rule_id": "EX-07", "severity": "P0", "dimension": CAT_EXCEPTION_HANDLING,
        "file": filepath, "line": node.lineno,
        "title": f"except 绑定 '{bound_name}' 但块内引用 '{min(suspicious)}' — 变量名不一致",
        "description": (
            f"except 子句绑定变量名为 '{bound_name}',"
            f"但块内引用了 '{', '.join(sorted(suspicious))}'."
            "这会导致 NameError,因为变量名不匹配."
        ),
        "code_snippet": extract_code_lines(source, node.lineno),
        "suggestion": f"根因: 代码实现不一致, 缺乏统一规范。该问题属于异常处理类别。\n修复策略: 统一变量名:将块内的引用改为 '{bound_name}', 或将 except 绑定改为匹配的变量名.\n参考标准: PEP 8 / pylint W07xx",
        "rule_ref": "sc0581",
    }
def _make_ex07_selfkill_issue(bound_name: str, selfkill_line: int,
                              source: Any, filepath: Any) -> dict:
    return {
        "rule_id": "EX-07", "severity": "P0", "dimension": CAT_EXCEPTION_HANDLING,
        "file": filepath, "line": selfkill_line,
        "title": (f"except 绑定 '{bound_name}' 被嵌套 except 同名"
                  f"重绑定覆盖, 块后引用 '{bound_name}'"),
        "description": (
            f"嵌套 except 子句以 as {bound_name} 重绑定并覆盖本帧"
            f"绑定, 其块结束时隐式删除该名字; 第 {selfkill_line} 行"
            "的引用在嵌套分支匹配执行时触发 NameError."
        ),
        "code_snippet": extract_code_lines(source, selfkill_line),
        "suggestion": (
            f"根因: 嵌套 except 同名 as 绑定的块结束隐式 del 击杀了"
            f"外层绑定, 块后引用无存活绑定。该问题属于异常处理类别。\n"
            f"修复策略: 嵌套 except 改用不同变量名(如 nested_{bound_name}),\n"
            "或在嵌套块后重新引用前显式重新赋值/改用日志记录原始异常。\n"
            "参考标准: PEP 8 / pylint W07xx"
        ),
        "rule_ref": "sc0581",
    }
def _handler_uses_bound_name(node: ast.ExceptHandler, *,
                             annotations_evaluated: bool = _DEFAULT_ANNOTATIONS_EVALUATED,
                             annotations_postponed: bool = _DEFAULT_ANNOTATIONS_POSTPONED,
                             module_scope: bool = False) -> bool:
    if not node.body:
        return False
    for child, _frame_kind in walk_handler_scope_frame_aware(
            node, annotations_evaluated=annotations_evaluated,
            annotations_postponed=annotations_postponed,
            module_scope=module_scope):
        if (isinstance(child, ast.Name)
                and isinstance(child.ctx, (ast.Load, ast.Del))
                and child.id == node.name):
            return True
    return False
def check_EH05(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_EH05 执行")
    issues = []
    if tree is None:
        return issues
    annotations_postponed = module_postpones_annotations(tree)
    _parents_cache: list = [None]
    for node in _iter_nodes_of_type(tree, ast.ExceptHandler):
        if not node.name:
            continue
        annotations_evaluated = _handler_annotations_evaluated(
            node, tree, _parents_cache,
            annotations_postponed=annotations_postponed)
        if _handler_uses_bound_name(
                node, annotations_evaluated=annotations_evaluated,
                annotations_postponed=annotations_postponed,
                module_scope=_handler_in_module_scope(
                    node, tree, _parents_cache)):
            continue
        if _matched_unbound_names(
                node, tree, candidate_names=_ex07_alias_names(node.name),
                parents_cache=_parents_cache,
                annotations_evaluated=annotations_evaluated,
                annotations_postponed=annotations_postponed):
            continue
        _bound = node.name
        issues.append(DiagnoseFinding(
            id="EH-05", severity="P2", dimension=CAT_EXCEPTION_HANDLING,
            file=filepath, title=f"except块中异常对象{_bound}未被使用",
            description=f"except X as {_bound}: 中{_bound}变量未被引用, 应简化为 except X:",
            line=getattr(node, 'lineno', 0),
            code_snippet=extract_code_lines(
                source_lines, getattr(node, 'lineno', 0)),
            suggestion=(f'根因: except X as {_bound}: 中{_bound}变量未被引用, 应简化为 except X:。该问题属于异常处理类别。\n'
                        f'修复策略: 移除未使用的as {_bound}子句: except ValueError: 代替 except ValueError as {_bound}:\n'
                        '参考标准: PEP 8 / pylint W07xx / CWE-396')
        ))
    return issues
def _raise_within_handler(node: ast.Raise,
                          parents: dict[ast.AST, ast.AST]) -> bool:
    cur = parents.get(node)
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            return False
        if isinstance(cur, ast.ExceptHandler):
            return True
        cur = parents.get(cur)
    return False
def _is_uncaused_new_raise(node: ast.AST) -> bool:
    if not (isinstance(node, ast.Raise) and node.exc is not None
            and node.cause is None):
        return False
    if isinstance(node.exc, ast.Call):
        return True
    return is_class_shaped_exc_name(_dotted_name(node.exc) or "")
def check_EH04(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_EH04 执行")
    issues = []
    if tree is None:
        return issues
    candidates = [node for node in walk_nodes(tree)
                  if _is_uncaused_new_raise(node)]
    if not candidates:
        return issues
    _parents = parent_map(tree)
    for node in candidates:
        if _raise_within_handler(node, _parents):
            issues.append(DiagnoseFinding(
                id="EH-04", severity="P1", dimension=CAT_EXCEPTION_HANDLING,
                file=filepath, line=node.lineno, col_offset=node.col_offset,
                title="raise新异常未使用from连接",
                code_snippet=extract_code_lines(source_lines, node.lineno),
                description="raise新异常未使用from连接原始异常链",
                suggestion='根因: raise新异常未使用from连接原始异常链。该问题属于异常处理类别。\n修复策略: 使用raise NewError(...) from e\n参考标准: PEP 8 / pylint W07xx / CWE-396'
            ))
    return issues
def check_EX04(tree: Any, source_lines: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_EX04 执行")
    issues = []
    if tree is None:
        return issues
    for node in _iter_nodes_of_type(tree, TRY_TYPES):
        issues.extend(_ex04_findings_for_try(node, source_lines, filepath))
    return issues
def _ex04_findings_for_try(node: Any, source_lines: Any,
                           filepath: Any) -> list:
    # 与 check_EX04 的遍历口径一致：except* (TryStar) 块同样按子句顺序匹配，
    # 重复类型的后续子句同样永远收不到异常。
    if not isinstance(node, TRY_TYPES):
        return []
    findings: list = []
    seen: set = set()
    for handler in node.handlers:
        if handler.type is None:
            continue
        for tname in dict.fromkeys(_except_type_names(handler.type)):
            if tname in seen:
                findings.append(DiagnoseFinding(
                    id="EX-04", severity="P2", dimension=CAT_EXCEPTION_HANDLING,
                    file=filepath, line=handler.lineno,
                    col_offset=handler.col_offset,
                    title=f"duplicate except type: {tname}",
                    description=f"异常类型 {tname} 在前面的 except 子句中已捕获, 此分支永远不会执行.",
                    code_snippet=extract_code_lines(source_lines, handler.lineno),
                    suggestion=(f'根因: 重复捕获异常类型 "{tname}", 后面的 except 永远不会执行。\n'
                                '修复策略: 合并重复的 except 分支\n'
                                '参考标准: Ruff B014 / Pylint W0705'),
                    rule_ref="Ruff B014 / Pylint W0705",
                ))
            else:
                seen.add(tname)
    return findings
def _unique_class_defs(tree: ast.AST) -> dict[str, ast.ClassDef]:
    definitions: dict[str, ast.ClassDef] = {}
    ambiguous: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        if node.name in definitions:
            ambiguous.add(node.name)
        else:
            definitions[node.name] = node
    for name in ambiguous:
        definitions.pop(name, None)
    return definitions

def _local_exception_subclass(raised_name: str, caught_name: str,
                              class_defs: dict[str, ast.ClassDef],
                              seen: set[str] | None = None) -> bool:
    definition = class_defs.get(raised_name)
    if definition is None:
        return False
    seen = set() if seen is None else seen
    if raised_name in seen:
        return False
    seen.add(raised_name)
    caught_cls = getattr(builtins, caught_name, None)
    for base in definition.bases:
        base_name = (_dotted_name(base) or '').removeprefix('builtins.')
        if base_name == caught_name:
            return True
        base_cls = getattr(builtins, base_name, None)
        if (isinstance(base_cls, type) and isinstance(caught_cls, type)
                and issubclass(base_cls, caught_cls)):
            return True
        if _local_exception_subclass(
                base_name, caught_name, class_defs, seen):
            return True
    return False

def _handler_has_direct_bare_reraise(
        handler: ast.ExceptHandler, raise_node: ast.Raise, class_defs) -> bool:
    def walk(nodes, handler_groups=()) -> bool:
        for node in nodes:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.Lambda, ast.ExceptHandler)):
                continue
            if isinstance(node, ast.If):
                truth = _const_truth(node.test)
                if truth is not None:
                    if walk(node.body if truth else node.orelse,
                            handler_groups):
                        return True
                    continue
            if isinstance(node, ast.While):
                truth = _const_truth(node.test)
                if truth is not None:
                    if walk(node.body if truth else node.orelse,
                            handler_groups):
                        return True
                    continue
            if isinstance(node, ast.For) and _definitely_empty_iter(node.iter):
                if walk(node.orelse, handler_groups):
                    return True
                continue
            if isinstance(node, TRY_TYPES):
                if walk(node.body, [node.handlers, *handler_groups]):
                    return True
                if walk(node.orelse, handler_groups):
                    return True
                if walk(node.finalbody, handler_groups):
                    return True
                continue
            if isinstance(node, ast.Raise):
                if (node.exc is None
                        and not _raise_caught_by_handlers(
                            raise_node, handler_groups, class_defs)):
                    return True
                continue
            if walk(ast.iter_child_nodes(node), handler_groups):
                return True
        return False
    return walk(handler.body)
def _raise_caught_by_handlers(node: ast.Raise, handler_groups,
                              class_defs=None) -> bool:
    class_defs = class_defs or {}
    expr = node.exc.func if isinstance(node.exc, ast.Call) else node.exc
    raised_name = (_dotted_name(expr) or '').removeprefix('builtins.')
    raised_cls = (None if raised_name in class_defs
                  else getattr(builtins, raised_name, None))
    if not (isinstance(raised_cls, type)
            and issubclass(raised_cls, BaseException)):
        raised_cls = None
    for handlers in handler_groups:
        for handler in handlers:
            names = (_except_type_names(handler.type)
                     if handler.type is not None else ())
            matched = handler.type is None or bool(
                raised_name and raised_name in names)
            if not matched and raised_cls is None:
                matched = any(
                    _local_exception_subclass(raised_name, name, class_defs)
                    for name in names)
            elif not matched:
                for name in names:
                    if name in class_defs:
                        continue
                    caught_cls = getattr(builtins, name, None)
                    if (isinstance(caught_cls, type)
                            and issubclass(caught_cls, BaseException)
                            and issubclass(raised_cls, caught_cls)):
                        matched = True
                        break
            if not matched:
                continue
            if _handler_has_direct_bare_reraise(
                    handler, node, class_defs):
                break
            return True
    return False
def _inherited_handler_groups(node: ast.AST, parents: dict) -> list:
    groups: list = []
    child = node
    parent = parents.get(child)
    while parent is not None:
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            break
        if isinstance(parent, TRY_TYPES) and _stmt_in(child, parent.body):
            groups.append(parent.handlers)
        child, parent = parent, parents.get(parent)
    return groups
def _iter_finally_direct_raises(finalbody, inherited_handler_groups=(),
                                class_defs=None) -> Iterator[ast.Raise]:
    def walk(nodes, handler_groups):
        for node in nodes:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            if isinstance(node, ast.If):
                truth = _const_truth(node.test)
                if truth is not None:
                    yield from walk(
                        node.body if truth else node.orelse, handler_groups)
                    continue
            if isinstance(node, ast.While):
                truth = _const_truth(node.test)
                if truth is not None:
                    yield from walk(
                        node.body if truth else node.orelse, handler_groups)
                    continue
            if isinstance(node, ast.For) and _definitely_empty_iter(node.iter):
                yield from walk(node.orelse, handler_groups)
                continue
            if isinstance(node, TRY_TYPES):
                yield from walk(node.body, [node.handlers, *handler_groups])
                yield from walk(node.orelse, handler_groups)
                for handler in node.handlers:
                    yield from walk(handler.body, handler_groups)
                continue
            if isinstance(node, ast.Raise):
                has_explicit_cause = node.cause is not None and not (
                    isinstance(node.cause, ast.Constant)
                    and node.cause.value is None)
                if (node.exc is not None and not has_explicit_cause
                        and not _raise_caught_by_handlers(
                            node, handler_groups, class_defs)):
                    yield node
                continue
            yield from walk(ast.iter_child_nodes(node), handler_groups)
    yield from walk(finalbody, list(inherited_handler_groups))
def check_WC01(tree: Any, source: Any, filepath: Any) -> Any:
    if finding_scan_exempt(filepath):
        return []
    _log.debug("规则入口 check_WC01 执行")
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    parents = parent_map(tree)
    class_defs = _unique_class_defs(tree)
    for node in _iter_nodes_of_type(tree, TRY_TYPES):
        if not node.finalbody:
            continue
        inherited = _inherited_handler_groups(node, parents)
        for sub in _iter_finally_direct_raises(
                node.finalbody, inherited, class_defs):
            issues.append(DiagnoseFinding(
                id="WC-01", severity="P2", dimension=CAT_EXCEPTION_HANDLING,
                file=filepath, line=sub.lineno, col_offset=sub.col_offset,
                title="finally块中raise会覆盖原始异常",
                code_snippet=extract_code_lines(source, sub.lineno),
                description="finally中的raise会替换try块中的原始异常,导致真实错误丢失.",
                suggestion="根因: finally块中的raise会掩盖try块中正在传播的原始异常。\n"
                           "修复策略: 避免在finally中raise; 若必须抛出,先用logging.exception记录原始异常,\n"
                           "或使用 raise NewError(...) from original 显式链式保留。\n"
                           "参考标准: PEP 8 / pylint W0133",
                rule_ref="WC-01",
            ))
    return issues
def wiring_declarations() -> dict:
    return {"catalogs": {
        "rule_bindings": {
            'EH04': check_EH04, 'EH05': check_EH05, 'EX04': check_EX04,
            'EX06': check_EX06, 'EX07': check_EX07, 'WC01': check_WC01,
        },
    }}

import ast
import builtins
import logging
from collections.abc import Callable, Iterator
from typing import NamedTuple

from jwsgj.diag_shared_ast_bindings import (
    collect_shadow_bindings,
    exec_scope_declarations,
)
from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    SHADOW_SCOPE_STOP,
    TRY_STAR,
    comp_element_roots,
    comp_target_names,
    in_subtree,
    is_none_literal,
    iter_def_site_nodes,
    iter_pattern_capture_names,
    iter_scope_nodes_with_shadow,
    iter_unpack_target_names,
    root_binding_shadow,
    scope_roots,
    split_identifier,
    type_last_name,
)
from jwsgj.diag_shared_ast_views import parent_map
from jwsgj.diag_types_defs import DiagnoseFinding, finding_scan_exempt
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    "check_BI01", "check_NM01",
]
logger = logging.getLogger(__name__)
logger.info("diag_rules_numeric_guard 已加载：%d 项导出", len(__all__))
_EMPTY_NAMES: frozenset[str] = frozenset()
_SCOPE_DEFINITION_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda,
)
def _statement_block(parent: ast.AST | None,
                     node: ast.AST) -> list | None:
    if parent is None:
        return None
    for field in ("body", "orelse", "finalbody"):
        block = getattr(parent, field, None)
        if isinstance(block, list) and node in block:
            return block
    return None
def _block_terminates(stmts: list[ast.stmt]) -> bool:
    if not stmts:
        return False
    last = stmts[-1]
    if isinstance(last, (ast.Return, ast.Raise, ast.Continue, ast.Break)):
        return True
    if isinstance(last, ast.If):
        return (_block_terminates(last.body)
                and _block_terminates(last.orelse))
    if isinstance(last, (ast.Try, TRY_STAR)):
        if _block_terminates(last.finalbody):
            return True
        normal_terminates = (_block_terminates(last.body)
                             or _block_terminates(last.orelse))
        return (normal_terminates
                and all(_block_terminates(handler.body)
                        for handler in last.handlers))
    return False
class _ScopeKeyTable(NamedTuple):
    keys: dict[int, str]
    class_keys: frozenset[str]
def _scope_keys(tree: ast.AST) -> _ScopeKeyTable:
    keys: dict[int, str] = {}
    class_keys: set[str] = set()
    occurrences: dict[str, int] = {}
    stack: list[tuple[ast.AST, str]] = [(tree, "")]
    while stack:
        node, key = stack.pop()
        keys[id(node)] = key
        if isinstance(node, ast.ClassDef):
            class_keys.add(key)
        for child in ast.iter_child_nodes(node):
            if isinstance(child, _SCOPE_DEFINITION_NODES):
                child_name = getattr(child, "name", "<lambda>")
                base_key = f"{key}.{child_name}" if key else child_name
                occurrences[base_key] = occurrences.get(base_key, 0) + 1
                occurrence = occurrences[base_key]
                child_key = (base_key if occurrence == 1
                             else f"{base_key}#{occurrence}")
                stack.append((child, child_key))
            else:
                stack.append((child, key))
    return _ScopeKeyTable(keys, frozenset(class_keys))
def _persistent_scope_bindings(scope: ast.AST, local: set[str]) -> set[str]:
    if not isinstance(scope, (ast.Module, ast.ClassDef)):
        return local
    sequential = _sequential_scope_bindings(scope, frozenset(local))
    persistent = set(local)
    for name, records in sequential.items():
        states = {name in persistent}
        for record in sorted(records, key=lambda item: item.end):
            if record.block is not None:
                continue
            if record.certain:
                states = {record.is_binding}
            else:
                states.add(record.is_binding)
        if True in states:
            persistent.add(name)
        else:
            persistent.discard(name)
    return persistent
def _scope_local_bindings(scopes: list[ast.AST],
                          scope_keys: dict[int, str]) -> dict[str, frozenset]:
    bindings: dict[str, frozenset] = {}
    for scope in scopes:
        if isinstance(scope, ast.Module):
            key = ""
        elif isinstance(scope, _SCOPE_DEFINITION_NODES):
            key = scope_keys.get(id(scope), "")
        else:
            continue
        local, global_names = exec_scope_declarations(scope)
        persistent = _persistent_scope_bindings(
            scope, set(local).difference(global_names))
        bindings[key] = frozenset(persistent)
    return bindings
def _iter_scope_chain(key: str) -> Iterator[str]:
    parts = key.split(".") if key else []
    for end in range(len(parts), -1, -1):
        yield ".".join(parts[:end])
def _nm01_finding(var: str, call: ast.Call,
                  filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="NM-01", severity="P2", dimension="numeric",
        file=filepath, line=call.lineno,
        description=(f"{var} 经 float 判定后 {call.func.id}({var}) "
                     "无 isfinite 防御（inf/nan 输入即 OverflowError/"
                     "ValueError 中断整批）"),
        suggestion=("根因: inf/nan 均能通过 isinstance(x, float)，"
                    "int(inf) 抛 OverflowError、int(nan) 抛 "
                    "ValueError；若转换位于循环内，一条非有限值会"
                    "中断整批处理。\n"
                    "修复策略: 转换前用 math.isfinite(x) 校验，"
                    "非有限值逐条跳过并计数，避免整体中断\n"
                    "参考标准: IEEE 754 浮点特殊值 / "
                    "Python math.isfinite 文档"),
    )
class _NM01Fact(NamedTuple):
    node: ast.AST
    shadow: frozenset[str]
    try_covered: bool
    failed: frozenset[str]
    frames: tuple[int, ...]
def _nm01_keep_earliest(
        positions: dict[str, tuple[int, int]], var: str,
        pos: tuple[int, int]) -> None:
    current = positions.get(var)
    if current is None or pos < current:
        positions[var] = pos
def _nm01_isinstance_check_args(
        node: ast.AST) -> tuple[str, ast.expr] | None:
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "isinstance" and len(node.args) == 2
            and isinstance(node.args[0], ast.Name)):
        return node.args[0].id, node.args[1]
    return None
def _nm01_bool_comparison(
        test: ast.AST) -> tuple[ast.expr, bool] | None:
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1
            and len(test.comparators) == 1):
        return None
    op = test.ops[0]
    if not isinstance(op, (ast.Eq, ast.NotEq, ast.Is, ast.IsNot)):
        return None
    left = test.left
    right = test.comparators[0]
    left_bool = (left.value if isinstance(left, ast.Constant)
                 and isinstance(left.value, bool) else None)
    right_bool = (right.value if isinstance(right, ast.Constant)
                  and isinstance(right.value, bool) else None)
    if (left_bool is None) == (right_bool is None):
        return None
    operand, literal = ((right, left_bool) if left_bool is not None
                        else (left, right_bool))
    if not isinstance(operand, ast.Call):
        return None
    if (_nm01_isinstance_check_args(operand) is None
            and type_last_name(operand.func) not in ("isfinite", "isnan", "isinf")
            and _nm01_isinteger_receiver(operand) is None):
        return None
    negated = not literal
    if isinstance(op, (ast.NotEq, ast.IsNot)):
        negated = not negated
    return operand, negated
def _nm01_bool_test_view(test: ast.expr) -> ast.expr:
    comparison = _nm01_bool_comparison(test)
    if comparison is not None:
        operand, negated = comparison
        operand = _nm01_bool_test_view(operand)
        return (ast.UnaryOp(op=ast.Not(), operand=operand)
                if negated else operand)
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        operand = _nm01_bool_test_view(test.operand)
        if operand is not test.operand:
            return ast.UnaryOp(op=ast.Not(), operand=operand)
    elif isinstance(test, ast.BoolOp):
        values = [_nm01_bool_test_view(value) for value in test.values]
        if any(value is not original
               for value, original in zip(values, test.values)):
            return ast.BoolOp(op=test.op, values=values)
    return test
_NM01_SHADOWABLE_BUILTINS = frozenset({"int", "round", "isinstance", "float"})
def _nm01_checked_vars(scope_nodes: list[_NM01Fact],
                        allowed: frozenset[str] | None = None,
                        shadowed_builtins: frozenset[str] = _EMPTY_NAMES
                        ) -> set[str]:
    checked: set[str] = set()
    if "isinstance" in shadowed_builtins:
        return checked
    for fact in scope_nodes:
        if fact.frames or "isinstance" in fact.shadow:
            continue
        args = _nm01_isinstance_check_args(fact.node)
        if args is None:
            continue
        name, ty = args
        if (name not in fact.shadow
                and "float" not in fact.shadow
                and "float" not in shadowed_builtins
                and (allowed is None or name in allowed)
                and _nm01_guard_includes_float(ty)):
            checked.add(name)
    return checked
def _nm01_type_names(ty: ast.AST) -> list[str]:
    if isinstance(ty, ast.Tuple):
        return [name for elt in ty.elts for name in _nm01_type_names(elt)]
    if isinstance(ty, ast.BinOp) and isinstance(ty.op, ast.BitOr):
        return _nm01_type_names(ty.left) + _nm01_type_names(ty.right)
    return [type_last_name(ty)]
def _nm01_builtin_exception_type(
        node: ast.AST) -> type[BaseException] | None:
    if isinstance(node, ast.Call):
        node = node.func
    if not isinstance(node, ast.Name):
        return None
    candidate = getattr(builtins, node.id, None)
    if (isinstance(candidate, type)
            and issubclass(candidate, BaseException)):
        return candidate
    return None

def _nm01_raise_certainly_caught(
        node: ast.Raise, handlers: list[ast.ExceptHandler]) -> bool | None:
    if node.exc is None:
        for handler in handlers:
            names = (set() if handler.type is None
                     else set(_nm01_type_names(handler.type)))
            if handler.type is None or names & {"Exception", "BaseException"}:
                return True
        return None
    raised = _nm01_builtin_exception_type(node.exc)
    if raised is None:
        return None
    unknown_handler = False
    for handler in handlers:
        if handler.type is None:
            return True
        for name in _nm01_type_names(handler.type):
            caught = getattr(builtins, name, None)
            if not (isinstance(caught, type)
                    and issubclass(caught, BaseException)):
                unknown_handler = True
                continue
            if issubclass(raised, caught):
                return True
    return None if unknown_handler else False

def _nm01_handler_reraises(handler: ast.ExceptHandler) -> bool:
    stack: list[tuple[ast.AST, list[ast.ExceptHandler] | None]] = [
        (node, None) for node in handler.body]
    while stack:
        node, local_handlers = stack.pop()
        if isinstance(node, ast.Raise):
            if local_handlers is None:
                return True
            caught = _nm01_raise_certainly_caught(node, local_handlers)
            if caught is False:
                return True
            continue
        if isinstance(node, SHADOW_SCOPE_STOP):
            continue
        if isinstance(node, _NM01_TRY_TYPES):
            # else、finally 与 handler 自身不被同一个 try 的 handlers 覆盖。
            stack.extend((child, local_handlers) for child in node.finalbody)
            stack.extend((child, local_handlers) for child in node.orelse)
            stack.extend((child, local_handlers)
                         for nested_handler in node.handlers
                         for child in nested_handler.body)
            body_handlers = node.handlers or local_handlers
            stack.extend((child, body_handlers) for child in node.body)
            continue
        stack.extend((child, local_handlers)
                     for child in ast.iter_child_nodes(node))
    return False
def _nm01_try_covers_int_errors(handlers: list[ast.ExceptHandler]) -> bool:
    required = {"OverflowError", "ValueError"}
    covered: set[str] = set()
    for handler in handlers:
        names = (set() if handler.type is None
                 else set(_nm01_type_names(handler.type)))
        if handler.type is None or names & {"Exception", "BaseException"}:
            matched = set(required)
        else:
            matched = set()
            if names & {"OverflowError", "ArithmeticError"}:
                matched.add("OverflowError")
            if "ValueError" in names:
                matched.add("ValueError")
        if matched - covered and _nm01_handler_reraises(handler):
            return False
        covered |= matched
    return covered == required
_NM01_FINITE_WORDS = frozenset({"finite", "valid", "real", "safe"})
_NM01_NUMBER_WORDS = frozenset({"number", "numeric", "float"})
def _nm01_is_finite_contract_name(name: str) -> bool:
    segments = set(split_identifier(name))
    return bool(segments & _NM01_FINITE_WORDS
                and segments & _NM01_NUMBER_WORDS)
def _nm01_finite_contract_bindings(
        scope_nodes: list[_NM01Fact]) -> dict[str, list[ast.AST]]:
    bound: dict[str, list[ast.AST]] = {}
    for fact in scope_nodes:
        node = fact.node
        if fact.frames or not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        value = getattr(node, "value", None)
        if not (isinstance(value, ast.Call)
                and _nm01_is_finite_contract_name(
                    type_last_name(value.func))):
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        for target in targets:
            if isinstance(target, ast.Name):
                bound.setdefault(target.id, []).append(node)
    return bound
def _nm01_finite_binding_dominates(
        binding: ast.AST, conversion: ast.AST,
        parents: dict[ast.AST, ast.AST]) -> bool:
    current = conversion
    while current is not None:
        parent = parents.get(current)
        if parent is None:
            return False
        block = _statement_block(parent, current)
        if block is not None:
            earlier = block[:block.index(current)]
            if any(stmt is binding for stmt in earlier):
                return True
            if (isinstance(parent, _NM01_TRY_TYPES)
                    and block is parent.orelse
                    and any(stmt is binding for stmt in parent.body)):
                return True
        current = parent
    return False

def _nm01_bound_to_finite_contract(
        var: str, conv_node: ast.AST, bound: dict[str, list[ast.AST]],
        parents: dict[ast.AST, ast.AST] | None) -> bool:
    if parents is None:
        return False
    conv_pos = (conv_node.lineno, conv_node.col_offset)
    for binding in bound.get(var, ()):
        end_pos = (binding.end_lineno, binding.end_col_offset)
        if end_pos > conv_pos:
            continue
        if not _nm01_finite_binding_dominates(binding, conv_node, parents):
            continue
        if not _rebound_between(var, binding, conv_node, parents):
            return True
    return False
_NM01_FLOAT_SUPERTYPES = frozenset({
    "float", "object", "Number", "Real", "Complex", "Any",
})
def _nm01_guard_excludes_float(ty: ast.expr) -> bool:
    names = _nm01_type_names(ty)
    return bool(names) and all(name and name not in _NM01_FLOAT_SUPERTYPES
                               for name in names)
def _nm01_guard_includes_float(ty: ast.expr) -> bool:
    return "float" in _nm01_type_names(ty)
def _nm01_collect_polarity_guards(
        test: ast.expr,
        true_out: set[str],
        false_out: set[str]) -> None:
    test = _nm01_bool_test_view(test)
    false_out |= _nm01_false_guard_vars(test)
    for t in _nm01_and_terms(test):
        if isinstance(t, ast.UnaryOp) and isinstance(t.op, ast.Not):
            nargs = _nm01_isinstance_check_args(t.operand)
            if nargs is not None and _nm01_guard_includes_float(nargs[1]):
                true_out.add(nargs[0])
            continue
        cargs = _nm01_isinstance_check_args(t)
        if cargs is not None and _nm01_guard_excludes_float(cargs[1]):
            true_out.add(cargs[0])
def _nm01_false_guard_vars(test: ast.expr) -> set[str]:
    test = _nm01_bool_test_view(test)
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.Or):
        names: set[str] = set()
        for value in test.values:
            names |= _nm01_false_guard_vars(value)
        return names
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
        parts = [_nm01_false_guard_vars(value) for value in test.values]
        safe = set(parts[0]) if parts else set()
        for part in parts[1:]:
            safe &= part
        return safe
    not_finite = _nm01_not_isfinite_names(test)
    if not_finite:
        return set(not_finite)
    root_args = _nm01_isinstance_check_args(test)
    if root_args is not None and _nm01_guard_includes_float(root_args[1]):
        return {root_args[0]}
    return set()
def _nm01_and_terms(test: ast.expr) -> list[ast.expr]:
    terms: list[ast.expr] = []
    stack: list[ast.expr] = [test]
    while stack:
        term = stack.pop()
        if isinstance(term, ast.BoolOp) and isinstance(term.op, ast.And):
            stack.extend(reversed(term.values))
            continue
        terms.append(term)
    return terms
def _nm01_not_func_call(
        t: ast.expr,
        funcs: tuple[str, ...]) -> tuple[str, str] | None:
    if (isinstance(t, ast.UnaryOp) and isinstance(t.op, ast.Not)
            and isinstance(t.operand, ast.Call)
            and type_last_name(t.operand.func) in funcs
            and t.operand.args
            and isinstance(t.operand.args[0], ast.Name)):
        return t.operand.args[0].id, type_last_name(t.operand.func)
    return None
def _nm01_not_isfinite_names(t: ast.expr) -> set[str]:
    info = _nm01_not_func_call(t, ("isfinite",))
    return {info[0]} if info is not None else set()
def _nm01_bare_isfinite_names(t: ast.expr) -> set[str]:
    if (isinstance(t, ast.Call)
            and type_last_name(t.func) == "isfinite"
            and t.args and isinstance(t.args[0], ast.Name)):
        return {t.args[0].id}
    return set()
def _nm01_and_chain_naninf_var(
        values: list[ast.expr]) -> set[str]:
    var: str | None = None
    names: set[str] = set()
    for t in values:
        info = _nm01_not_func_call(t, ("isnan", "isinf"))
        if info is None:
            return set()
        name, func_name = info
        if var is None:
            var = name
        elif var != name:
            return set()
        names.add(func_name)
    if var is not None and names == {"isnan", "isinf"}:
        return {var}
    return set()
def _boolop_values(node: ast.AST, op: type[ast.boolop]) -> list[ast.expr] | None:
    if isinstance(node, ast.BoolOp) and isinstance(node.op, op):
        return node.values
    return None
def _nm01_finiteness_failed_vars(test: ast.expr, on_true: bool) -> set[str]:
    test = _nm01_bool_test_view(test)
    if on_true:
        values = _boolop_values(test, ast.And) or [test]
        failed: set[str] = set()
        for value in values:
            failed |= _nm01_not_isfinite_names(value)
            failed |= _nm01_inverted_isinteger_names(value)
        failed -= _nm01_finiteness_passed_vars(test)
        return failed
    values = _boolop_values(test, ast.And)
    if values is not None:
        chained = _nm01_and_chain_naninf_var(values)
        if chained:
            return chained
        narrowed: set[str] = set()
        for value in values:
            narrowed |= _nm01_bare_isfinite_names(value)
            narrowed |= _nm01_positive_isinteger_names(value)
        return narrowed
    values = _boolop_values(test, ast.Or)
    if values is not None:
        failed = set()
        for value in values:
            failed |= _nm01_bare_isfinite_names(value)
            failed |= _nm01_positive_isinteger_names(value)
        return failed
    return (_nm01_bare_isfinite_names(test)
            | _nm01_positive_isinteger_names(test))
def _nm01_isinteger_receiver(
        node: ast.AST,
        shadowed: frozenset[str] = _EMPTY_NAMES) -> str | None:
    if (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "is_integer"
            and not node.args
            and isinstance(node.func.value, ast.Name)
            and node.func.value.id not in shadowed):
        return node.func.value.id
    return None
def _nm01_positive_isinteger_names(test: ast.expr) -> set[str]:
    name = _nm01_isinteger_receiver(test)
    return {name} if name is not None else set()
def _nm01_inverted_isinteger_names(test: ast.expr) -> set[str]:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _nm01_positive_isinteger_names(test.operand)
    return set()
def _nm01_finiteness_passed_vars(test: ast.expr) -> set[str]:
    test = _nm01_bool_test_view(test)
    if isinstance(test, ast.BoolOp):
        if isinstance(test.op, ast.Or):
            alternatives = [_nm01_finiteness_passed_vars(value)
                            for value in test.values]
            if not alternatives:
                return set()
            passed = set(alternatives[0])
            for alternative in alternatives[1:]:
                passed &= alternative
            return passed
        passed: set[str] = set()
        isnan: set[str] = set()
        isinf: set[str] = set()
        for term in test.values:
            passed |= _nm01_finiteness_passed_vars(term)
            info = _nm01_not_func_call(term, ("isnan", "isinf"))
            if info is None:
                continue
            if info[1] == "isnan":
                isnan.add(info[0])
            else:
                isinf.add(info[0])
        return passed | (isnan & isinf)
    return (_nm01_bare_isfinite_names(test)
            | _nm01_positive_isinteger_names(test))
def _nm01_terms_guard_names(terms: list[ast.expr]) -> frozenset[str]:
    guards: set[str] = set()
    inverted: set[str] = set()
    for term in terms:
        true_out: set[str] = set()
        _nm01_collect_polarity_guards(term, true_out, set())
        guards |= true_out
        inverted |= _nm01_finiteness_failed_vars(term, True)
    combined = (terms[0] if len(terms) == 1
                else ast.BoolOp(op=ast.And(), values=list(terms)))
    guards |= _nm01_finiteness_passed_vars(combined)
    return frozenset(guards - inverted)
_NM01_TRY_TYPES = (ast.Try, TRY_STAR)
def _nm01_branch_polarity(
        test: ast.expr) -> tuple[set[str], set[str], set[str], set[str]]:
    guards: set[str] = set()
    falsified: set[str] = set()
    _nm01_collect_polarity_guards(test, guards, falsified)
    return (guards, falsified,
            _nm01_finiteness_failed_vars(test, True),
            _nm01_finiteness_failed_vars(test, False))
class _NM01State(NamedTuple):
    shadow: frozenset[str]
    try_covered: bool
    failed: frozenset[str]
    frames: tuple[int, ...]
def _nm01_branch_frames(
        body_items: list[ast.AST], else_items: list[ast.AST],
        state: _NM01State,
        pol: tuple[set[str], set[str], set[str], set[str]],
        ) -> tuple[tuple, tuple]:
    ff_true, ff_false = pol[2:]
    body_frame = (iter(body_items), state._replace(
        failed=state.failed | frozenset(ff_true)))
    else_frame = (iter(else_items), state._replace(
        failed=state.failed | frozenset(ff_false)))
    return body_frame, else_frame
def _nm01_if_frames(
        child: ast.If, state: _NM01State,
        pol: tuple[set[str], set[str], set[str], set[str]],
        ) -> list[tuple]:
    body_frame, else_frame = _nm01_branch_frames(
        child.body, child.orelse, state, pol)
    return [
        else_frame,
        body_frame,
        (iter([child.test]), state),
    ]
def _nm01_ifexp_frames(
        child: ast.IfExp, state: _NM01State,
        pol: tuple[set[str], set[str], set[str], set[str]],
        ) -> list[tuple]:
    body_frame, else_frame = _nm01_branch_frames(
        [child.body], [child.orelse], state, pol)
    return [
        (iter([child.test]), state),
        else_frame,
        body_frame,
    ]
_NM01_FRAME = tuple[Iterator[ast.AST], _NM01State]
def _nm01_push_branch_frames(stack: list[_NM01_FRAME], child: ast.AST,
                             state: _NM01State) -> bool:
    if isinstance(child, ast.If):
        pol = _nm01_branch_polarity(child.test)
        if any(pol):
            stack.extend(_nm01_if_frames(child, state, pol))
            return True
        return False
    if isinstance(child, ast.IfExp):
        pol = _nm01_branch_polarity(child.test)
        if any(pol):
            stack.extend(_nm01_ifexp_frames(child, state, pol))
            return True
    return False
def _nm01_push_try_frames(stack: list[_NM01_FRAME], child: ast.AST,
                          state: _NM01State) -> None:
    body_try = state.try_covered or _nm01_try_covers_int_errors(child.handlers)
    stack.append((iter(child.finalbody), state))
    stack.append((iter(child.handlers), state))
    stack.append((iter(child.orelse), state))
    stack.append((iter(child.body), state._replace(try_covered=body_try)))
def _execution_scope_children(scope: ast.AST) -> Iterator[ast.AST]:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return iter(scope.body)
    if isinstance(scope, ast.Lambda):
        return iter((scope.body,))
    return ast.iter_child_nodes(scope)
def _nm01_comp_region_roots(comp: ast.AST) -> list[ast.AST]:
    generators = getattr(comp, "generators", ()) or ()
    roots: list[ast.AST] = []
    if generators:
        first = generators[0]
        roots.extend([first.target, *first.ifs])
        roots.extend(generators[1:])
    roots.extend(comp_element_roots(comp))
    return roots
def _nm01_comp_outer_iter_ids(comp: ast.AST) -> set[int]:
    generators = getattr(comp, "generators", ()) or ()
    if not generators:
        return set()
    return {id(node) for node in walk_nodes(generators[0].iter)}
def _nm01_iter_with_guards(scope: ast.AST,
                           shadowed: frozenset[str] = _EMPTY_NAMES,
                           init_try: bool = False,
                           init_failed: frozenset[str] = _EMPTY_NAMES,
                           ) -> Iterator[_NM01Fact]:
    stack: list[_NM01_FRAME] = [
        (_execution_scope_children(scope),
         _NM01State(frozenset(shadowed), bool(init_try),
                    frozenset(init_failed), ()))]
    while stack:
        try:
            child = next(stack[-1][0])
        except StopIteration:
            stack.pop()
            continue
        state = stack[-1][1]
        yield _NM01Fact(child, state.shadow,
                        state.try_covered, state.failed, state.frames)
        if isinstance(child, SHADOW_SCOPE_STOP):
            stack.append((iter(iter_def_site_nodes(child)), state))
            continue
        nxt = state._replace(shadow=root_binding_shadow(child, state.shadow))
        if isinstance(child, ast.Lambda):
            nxt = nxt._replace(frames=nxt.frames + (id(child),),
                               try_covered=False)
            stack.append((iter((child.body,)), nxt))
            stack.append((iter(iter_def_site_nodes(child)), state))
            continue
        if isinstance(child, COMP_SCOPE_NODES):
            stack.append((iter(_nm01_comp_region_roots(child)), nxt))
            if child.generators:
                stack.append((iter((child.generators[0].iter,)), state))
            continue
        if _nm01_push_branch_frames(stack, child, nxt):
            continue
        if isinstance(child, _NM01_TRY_TYPES):
            _nm01_push_try_frames(stack, child, nxt)
            continue
        stack.append((iter(ast.iter_child_nodes(child)), nxt))
def _nm01_isinteger_guarded_names(
        scope_nodes: list[_NM01Fact]) -> dict[str, tuple[int, int]]:
    guarded: dict[str, tuple[int, int]] = {}
    for fact in scope_nodes:
        node = fact.node
        var = _nm01_isinteger_receiver(node, fact.shadow)
        if var is not None:
            pos = (node.lineno, node.col_offset)
            _nm01_keep_earliest(guarded, var, pos)
    return guarded
def _nm01_guard_call_args(
        node: ast.AST,
        shadowed: frozenset[str]) -> tuple[str, str] | None:
    if not isinstance(node, ast.Call):
        return None
    args = node.args
    if not args or not isinstance(args[0], ast.Name) or args[0].id in shadowed:
        return None
    return args[0].id, type_last_name(node.func)
def _nm01_finiteness_guard_names(
        scope_nodes: list[_NM01Fact]) -> dict[str, tuple[int, int]]:
    isfinite_pos: dict[str, list[tuple[int, int]]] = {}
    isnan_pos: dict[str, list[tuple[int, int]]] = {}
    isinf_pos: dict[str, list[tuple[int, int]]] = {}
    for fact in scope_nodes:
        node = fact.node
        info = _nm01_guard_call_args(node, fact.shadow)
        if info is None:
            continue
        var, func_last = info
        pos = (node.lineno, node.col_offset)
        bucket = {"isfinite": isfinite_pos, "isnan": isnan_pos,
                  "isinf": isinf_pos}.get(func_last)
        if bucket is not None:
            bucket.setdefault(var, []).append(pos)
    guarded: dict[str, tuple[int, int]] = {}
    for var, positions in isfinite_pos.items():
        guarded[var] = min(positions)
    for var in set(isnan_pos) & set(isinf_pos):
        pair = max(min(isnan_pos[var]), min(isinf_pos[var]))
        _nm01_keep_earliest(guarded, var, pair)
    return guarded
def _nm01_is_conv_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in ("int", "round"))
def _nm01_round_keyword_operands(
        node: ast.Call, operand: ast.AST | None, ndigits: ast.AST | None
) -> tuple[ast.AST | None, ast.AST | None] | None:
    for keyword in node.keywords:
        if keyword.arg is None:
            return None
        if keyword.arg == "ndigits":
            ndigits = keyword.value
        elif keyword.arg == "number" and operand is None:
            operand = keyword.value
        elif keyword.arg not in ("number", "ndigits"):
            return None
    return operand, ndigits
def _nm01_round_int_operand(node: ast.Call) -> ast.AST | None:
    if len(node.args) > 2:
        return None
    operands = _nm01_round_keyword_operands(
        node,
        node.args[0] if node.args else None,
        node.args[1] if len(node.args) == 2 else None,
    )
    if operands is None:
        return None
    operand, ndigits = operands
    if ndigits is not None and not is_none_literal(ndigits):
        return None
    return operand
def _nm01_conv_call_var(node: ast.AST) -> str | None:
    if not _nm01_is_conv_call(node):
        return None
    if node.func.id == "int":
        if len(node.args) != 1 or node.keywords:
            return None
        operand: ast.AST | None = node.args[0]
    else:
        operand = _nm01_round_int_operand(node)
    if not isinstance(operand, ast.Name):
        return None
    return operand.id
def _nm01_guard_exempt(var: str, call_pos: tuple[int, int],
                       guard_pos: dict[str, tuple[int, int]] | None,
                       fin_failed: frozenset[str],
                       comp_presence: frozenset[str] | None = None) -> bool:
    if var in fin_failed:
        return False
    if guard_pos is not None:
        gp = guard_pos.get(var)
        if gp is not None and gp < call_pos:
            return True
    return comp_presence is not None and var in comp_presence
class _NM01GuardContext(NamedTuple):
    guard_pos: dict[tuple[int, ...], dict[str, tuple[int, int]]] | None = None
    guard_nodes: dict[tuple[int, ...], dict[str, list[ast.AST]]] | None = None
    parents: dict[ast.AST, ast.AST] | None = None
    ifexp_conv_pos: dict[int, tuple[int, int]] | None = None
    comp_presence: dict[int, frozenset[str]] | None = None
    owned_convs: dict[int, int] | None = None
    shadowed_builtins: frozenset[str] = _EMPTY_NAMES
class _NM01DominanceContext(NamedTuple):
    conversion: ast.AST
    parents: dict[ast.AST, ast.AST]
    var: str
def _nm01_conv_func_shadowed(node: ast.AST,
                             shadowed: frozenset[str]) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in shadowed)
def _nm01_frame_guard_view(
        guard_pos_frames: dict[tuple[int, ...], dict[str, tuple[int, int]]]
        | None,
        frames: tuple[int, ...],
) -> dict[str, tuple[int, int]] | None:
    if guard_pos_frames is None:
        return None
    merged: dict[str, tuple[int, int]] = {}
    for i in range(len(frames) + 1):
        part = guard_pos_frames.get(frames[:i])
        if not part:
            continue
        for var, pos in part.items():
            _nm01_keep_earliest(merged, var, pos)
    return merged
def _nm01_owned_conv(fact: _NM01Fact,
                     context: _NM01GuardContext) -> bool:
    owner = (context.owned_convs or {}).get(id(fact.node))
    return owner is not None and owner in fact.frames
def _nm01_fact_guard_exempt(var: str, fact: _NM01Fact,
                            context: _NM01GuardContext) -> bool:
    node = fact.node
    call_pos = ((context.ifexp_conv_pos or {}).get(
        id(node), (node.lineno, node.col_offset)))
    frame_guard_pos = _nm01_frame_guard_view(context.guard_pos, fact.frames)
    gp = (frame_guard_pos or {}).get(var)
    if gp is not None and gp < call_pos and context.parents is not None:
        guards = _nm01_frame_guard_nodes(context.guard_nodes, fact.frames, var)
        dominance = _NM01DominanceContext(node, context.parents, var)
        if guards and not (
                any(_nm01_guard_dominates(guard, dominance)
                    for guard in guards)
                or _nm01_naninf_guards_dominate(guards, dominance)):
            frame_guard_pos = dict(frame_guard_pos)
            frame_guard_pos.pop(var, None)
    return _nm01_guard_exempt(
        var, call_pos, frame_guard_pos, fact.failed,
        (context.comp_presence or {}).get(id(node)))
def _nm01_conversion_findings(
        scope_nodes: list[_NM01Fact],
        checked_vars: set[str],
        allowed: frozenset[str] | None,
        filepath: str,
        context: _NM01GuardContext) -> list[DiagnoseFinding]:
    findings: list[DiagnoseFinding] = []
    reported: set[str] = set()
    finite_bound = _nm01_finite_contract_bindings(scope_nodes)
    for fact in scope_nodes:
        shadowed = context.shadowed_builtins | (
            fact.shadow & _NM01_SHADOWABLE_BUILTINS)
        if _nm01_conv_func_shadowed(fact.node, shadowed):
            continue
        var = _nm01_conv_call_var(fact.node)
        if var is None or _nm01_owned_conv(fact, context):
            continue
        if not _nm01_reportable(
                var, fact.shadow, checked_vars, allowed, reported):
            continue
        if fact.try_covered:
            continue
        if _nm01_fact_guard_exempt(var, fact, context):
            continue
        if _nm01_bound_to_finite_contract(
                var, fact.node, finite_bound, context.parents):
            continue
        reported.add(var)
        findings.append(_nm01_finding(var, fact.node, filepath))
    return findings
def _nm01_reportable(var: str, shadowed: set[str], checked_vars: set[str],
                     allowed: frozenset[str] | None,
                     reported: set[str]) -> bool:
    if var in shadowed or var not in checked_vars:
        return False
    if allowed is not None and var not in allowed:
        return False
    return var not in reported
def _nm01_ifexp_body_conv_eval_pos(
        tree: ast.AST) -> dict[int, tuple[int, int]]:
    corrected: dict[int, tuple[int, int]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.IfExp):
            continue
        test_end = (node.test.end_lineno, node.test.end_col_offset)
        for conv in walk_nodes(node.body):
            if not _nm01_is_conv_call(conv):
                continue
            src_pos = (conv.lineno, conv.col_offset)
            pos = max(src_pos, test_end)
            if id(conv) not in corrected or pos > corrected[id(conv)]:
                corrected[id(conv)] = pos
    return corrected
def _nm01_type_guarded_names(
        scope_nodes: list[_NM01Fact]) -> dict[str, tuple[int, int]]:
    guarded: dict[str, tuple[int, int]] = {}
    for fact in scope_nodes:
        var = _nm01_type_guard_var(fact.node, fact.shadow)
        if var is not None:
            _nm01_keep_earliest(
                guarded, var, (fact.node.lineno, fact.node.col_offset))
    return guarded
def _nm01_guard_evidence(
        scope_nodes: list[_NM01Fact]
        ) -> tuple[dict[tuple[int, ...], dict[str, tuple[int, int]]],
                   dict[tuple[int, ...], dict[str, list[ast.AST]]]]:
    by_frame: dict[tuple[int, ...], list[_NM01Fact]] = {}
    for fact in scope_nodes:
        by_frame.setdefault(fact.frames, []).append(fact)
    positions: dict[tuple[int, ...], dict[str, tuple[int, int]]] = {}
    nodes: dict[tuple[int, ...], dict[str, list[ast.AST]]] = {}
    for frames, facts in by_frame.items():
        merged: dict[str, tuple[int, int]] = {}
        for source in (_nm01_isinteger_guarded_names(facts),
                       _nm01_finiteness_guard_names(facts),
                       _nm01_type_guarded_names(facts)):
            for var, pos in source.items():
                _nm01_keep_earliest(merged, var, pos)
        positions[frames] = merged
        for fact in facts:
            var = _nm01_guard_node_var(fact.node, fact.shadow)
            if var is not None:
                nodes.setdefault(frames, {}).setdefault(
                    var, []).append(fact.node)
    return positions, nodes
def _nm01_type_guard_var(
        node: ast.AST, shadowed: frozenset[str]) -> str | None:
    if "isinstance" in shadowed or "float" in shadowed:
        return None
    info = _nm01_isinstance_check_args(node)
    if info is None:
        return None
    var, ty = info
    if var in shadowed:
        return None
    if (_nm01_guard_includes_float(ty)
            or _nm01_guard_excludes_float(ty)):
        return var
    return None
def _nm01_guard_node_var(node: ast.AST,
                         shadowed: frozenset[str]) -> str | None:
    type_guard = _nm01_type_guard_var(node, shadowed)
    if type_guard is not None:
        return type_guard
    receiver = _nm01_isinteger_receiver(node, shadowed)
    if receiver is not None:
        return receiver
    info = _nm01_guard_call_args(node, shadowed)
    if info is not None and info[1] in ("isfinite", "isnan", "isinf"):
        return info[0]
    return None
def _nm01_frame_guard_nodes(
        guard_nodes: dict[tuple[int, ...], dict[str, list[ast.AST]]] | None,
        frames: tuple[int, ...], var: str) -> list[ast.AST]:
    nodes: list[ast.AST] = []
    for i in range(len(frames) + 1):
        part = (guard_nodes or {}).get(frames[:i]) or {}
        nodes.extend(part.get(var, ()))
    return nodes
def _nm01_ancestors(node: ast.AST,
                    parents: dict[ast.AST, ast.AST]) -> Iterator[ast.AST]:
    current: ast.AST | None = node
    while current is not None:
        yield current
        current = parents.get(current)
def _nm01_child_toward(ancestor: ast.AST, descendant: ast.AST,
                       parents: dict[ast.AST, ast.AST]) -> ast.AST | None:
    current = descendant
    while current is not ancestor:
        parent = parents.get(current)
        if parent is None:
            return None
        if parent is ancestor:
            return current
        current = parent
    return None
def _nm01_guard_safe_truth(guard: ast.AST, var: str) -> bool | None:
    if var in _nm01_positive_isinteger_names(guard):
        return True
    type_info = _nm01_isinstance_check_args(guard)
    if type_info is not None and type_info[0] == var:
        ty = type_info[1]
        if _nm01_guard_includes_float(ty):
            return False
        if _nm01_guard_excludes_float(ty):
            return True
    info = _nm01_guard_call_args(guard, frozenset())
    if info is None or info[0] != var:
        return None
    if info[1] == "isfinite":
        return True
    if info[1] in ("isnan", "isinf"):
        return False
    return None
def _nm01_required_guard_truth(root: ast.AST, guard: ast.AST,
                               required: bool,
                               parents: dict[ast.AST, ast.AST]) -> bool | None:
    current = root
    while current is not guard:
        comparison = _nm01_bool_comparison(current)
        if comparison is not None:
            operand, negated = comparison
            child = _nm01_child_toward(current, guard, parents)
            if child is not operand:
                return None
            if negated:
                required = not required
            current = child
            continue
        if isinstance(current, ast.UnaryOp) and isinstance(current.op, ast.Not):
            required = not required
            current = current.operand
            continue
        if isinstance(current, ast.BoolOp):
            child = _nm01_child_toward(current, guard, parents)
            if child is None:
                return None
            if not ((isinstance(current.op, ast.And) and required)
                    or (isinstance(current.op, ast.Or) and not required)):
                return None
            current = child
            continue
        return None
    return required
def _nm01_bool_guard_dominates(
        guard: ast.AST, common: ast.AST,
        context: _NM01DominanceContext) -> bool:
    if not isinstance(common, ast.BoolOp):
        return False
    guard_child = _nm01_child_toward(common, guard, context.parents)
    conversion_child = _nm01_child_toward(
        common, context.conversion, context.parents)
    if guard_child is None or conversion_child is None:
        return False
    guard_index = next((i for i, value in enumerate(common.values)
                        if value is guard_child), -1)
    conversion_index = next((i for i, value in enumerate(common.values)
                             if value is conversion_child), -1)
    if guard_index < 0 or conversion_index <= guard_index:
        return False
    required = isinstance(common.op, ast.And)
    required = _nm01_required_guard_truth(
        guard_child, guard, required, context.parents)
    safe = _nm01_guard_safe_truth(guard, context.var)
    return required is not None and safe is not None and required == safe
def _nm01_naninf_or_names(values: list[ast.expr]) -> set[str]:
    names: set[str] = set()
    funcs: set[str] = set()
    for value in values:
        if not (isinstance(value, ast.Call) and value.args
                and isinstance(value.args[0], ast.Name)):
            return set()
        func = type_last_name(value.func)
        if func not in ("isnan", "isinf"):
            return set()
        names.add(value.args[0].id)
        funcs.add(func)
    if funcs == {"isnan", "isinf"} and len(names) == 1:
        return names
    return set()
def _nm01_false_finiteness_guarantee(test: ast.expr, var: str) -> bool:
    test = _nm01_bool_test_view(test)
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return var in _nm01_finiteness_passed_vars(test.operand)
    if isinstance(test, ast.BoolOp):
        if (isinstance(test.op, ast.Or)
                and var in _nm01_naninf_or_names(list(test.values))):
            return True
        guarantees = (_nm01_false_finiteness_guarantee(value, var)
                      for value in test.values)
        return all(guarantees) if isinstance(test.op, ast.And) else any(guarantees)
    return False
def _nm01_later_in_block(
        statement: ast.stmt, context: _NM01DominanceContext) -> bool:
    parent = context.parents.get(statement)
    if parent is None:
        return False
    block = _statement_block(parent, statement)
    if block is None:
        return False
    later = block[block.index(statement) + 1:]
    return any(in_subtree(context.conversion, stmt) for stmt in later)
def _nm01_branch_guard_covers(
        test: ast.expr, var: str, on_true: bool) -> bool:
    if on_true:
        return var in _nm01_terms_guard_names(_nm01_and_terms(test))
    return (var in _nm01_false_guard_vars(test)
            or _nm01_false_finiteness_guarantee(test, var))
def _nm01_ifexp_guard_verdict(
        parent: ast.IfExp, context: _NM01DominanceContext) -> bool:
    if in_subtree(context.conversion, parent.body):
        return _nm01_branch_guard_covers(parent.test, context.var, True)
    if in_subtree(context.conversion, parent.orelse):
        return _nm01_branch_guard_covers(parent.test, context.var, False)
    return False
def _nm01_if_guard_verdict(
        parent: ast.If, context: _NM01DominanceContext) -> bool:
    true_safe = _nm01_branch_guard_covers(
        parent.test, context.var, True)
    false_safe = _nm01_branch_guard_covers(
        parent.test, context.var, False)
    if any(in_subtree(context.conversion, stmt) for stmt in parent.body):
        return true_safe
    if any(in_subtree(context.conversion, stmt) for stmt in parent.orelse):
        return false_safe
    if in_subtree(context.conversion, parent.test):
        return False
    if not _nm01_later_in_block(parent, context):
        return False
    body_falls = not _block_terminates(parent.body)
    else_falls = not _block_terminates(parent.orelse)
    return ((not body_falls or true_safe)
            and (not else_falls or false_safe))
def _nm01_assert_guard_verdict(
        parent: ast.Assert, context: _NM01DominanceContext) -> bool:
    if in_subtree(context.conversion, parent):
        return False
    return (_nm01_later_in_block(parent, context)
            and _nm01_branch_guard_covers(parent.test, context.var, True))
def _nm01_while_guard_verdict(
        parent: ast.While, context: _NM01DominanceContext) -> bool:
    return (any(in_subtree(context.conversion, stmt) for stmt in parent.body)
            and _nm01_branch_guard_covers(parent.test, context.var, True))
def _nm01_parent_guard_verdict(
        parent: ast.AST | None, current: ast.AST,
        context: _NM01DominanceContext) -> bool | None:
    if isinstance(parent, ast.IfExp) and parent.test is current:
        return _nm01_ifexp_guard_verdict(parent, context)
    if isinstance(parent, ast.If) and parent.test is current:
        return _nm01_if_guard_verdict(parent, context)
    if isinstance(parent, ast.Assert) and parent.test is current:
        return _nm01_assert_guard_verdict(parent, context)
    if isinstance(parent, ast.While) and parent.test is current:
        return _nm01_while_guard_verdict(parent, context)
    return None
def _nm01_statement_guard_dominates(
        guard: ast.AST, context: _NM01DominanceContext) -> bool:
    current = guard
    while current is not None:
        parent = context.parents.get(current)
        verdict = _nm01_parent_guard_verdict(parent, current, context)
        if verdict is not None:
            return verdict and not _rebound_between(
                context.var, guard, context.conversion, context.parents)
        current = parent
    return False
def _nm01_is_self_assignment(stmt: ast.AST, var: str) -> bool:
    if not (isinstance(stmt, (ast.Assign, ast.AnnAssign))
            and isinstance(stmt.value, ast.Name) and stmt.value.id == var):
        return False
    targets = stmt.targets if isinstance(stmt, ast.Assign) else [stmt.target]
    return any(isinstance(target, ast.Name) and target.id == var
               for target in targets)
def _nm01_entry_rebinding(
        var: str, parent: ast.AST, child: ast.AST,
        guard: ast.AST | None) -> bool:
    """parent 进入 child 所在区域之前是否已重新绑定 var。

    循环目标、with 的 as 目标、except 的 as 名称与 match 捕获名都在进入
    各自 body 之前完成绑定。guard 为 None 表示 guard 位于 parent 之外；
    否则 guard 位于 parent 之内，此时只有 for 的 iter 求值先于目标绑定，
    其余形态不做推断。
    """
    if guard is not None and not isinstance(parent, (ast.For, ast.AsyncFor)):
        return False
    if isinstance(parent, (ast.For, ast.AsyncFor)):
        if (child is parent.iter
                or var not in iter_unpack_target_names(parent.target)):
            return False
        return guard is None or in_subtree(guard, parent.iter)
    if isinstance(parent, (ast.With, ast.AsyncWith)):
        targets = [item.optional_vars for item in parent.items
                   if item.optional_vars is not None]
        if not targets or var not in iter_unpack_target_names(targets):
            return False
        if any(child is stmt for stmt in parent.body):
            return True
        for index, item in enumerate(parent.items):
            if child is item:
                earlier = [prev.optional_vars for prev in parent.items[:index]
                           if prev.optional_vars is not None]
                return (bool(earlier)
                        and var in iter_unpack_target_names(earlier))
        return False
    if isinstance(parent, ast.ExceptHandler):
        return (parent.name == var
                and any(child is stmt for stmt in parent.body))
    if isinstance(parent, ast.Match):
        return (isinstance(child, ast.match_case)
                and var in iter_pattern_capture_names(child.pattern))
    return False
def _nm01_binding_statements_between(
        var: str, guard: ast.AST, conversion: ast.AST,
        parents: dict[ast.AST, ast.AST]) -> list[ast.AST] | None:
    conversion_ancestors = {
        id(node) for node in _nm01_ancestors(conversion, parents)}
    common = next((node for node in _nm01_ancestors(guard, parents)
                   if id(node) in conversion_ancestors), None)
    if common is None:
        return None
    bindings: list[ast.AST] = []
    guard_start = (guard.lineno, guard.col_offset)
    current: ast.AST | None = conversion
    while current is not None and current is not common:
        parent = parents.get(current)
        if parent is None:
            return None
        block = _statement_block(parent, current)
        if block is not None:
            for stmt in block[:block.index(current)]:
                if stmt is guard and isinstance(guard, (ast.Assign, ast.AnnAssign)):
                    continue
                stmt_end = (getattr(stmt, "end_lineno", stmt.lineno),
                            getattr(stmt, "end_col_offset", stmt.col_offset))
                if stmt is not guard and stmt_end <= guard_start:
                    continue
                if (var in _nm01_statement_bindings(stmt)
                        and not _nm01_is_self_assignment(stmt, var)):
                    bindings.append(stmt)
        if _nm01_entry_rebinding(
                var, parent, current, guard if parent is common else None):
            bindings.append(parent)
        current = parent
    return sorted(
        bindings,
        key=lambda stmt: (
            getattr(stmt, "end_lineno", stmt.lineno),
            getattr(stmt, "end_col_offset", stmt.col_offset),
        ),
    )
def _nm01_namedexpr_rebinding_in(
        root: ast.AST, var: str, start: tuple[int, int],
        end: tuple[int, int] | None = None) -> bool:
    stack = [root]
    while stack:
        node = stack.pop()
        if (node is not root
                and isinstance(node, (*SHADOW_SCOPE_STOP, ast.Lambda))):
            continue
        if (isinstance(node, ast.NamedExpr)
                and isinstance(node.target, ast.Name)
                and node.target.id == var):
            pos = (node.lineno, node.col_offset)
            if start < pos and (end is None or pos < end):
                return True
        stack.extend(ast.iter_child_nodes(node))
    return False
def _nm01_boolop_expression_rebinding(
        var: str, guard: ast.AST, conversion: ast.AST,
        parents: dict[ast.AST, ast.AST]) -> bool:
    conversion_ancestors = {
        id(node) for node in _nm01_ancestors(conversion, parents)}
    common = next((node for node in _nm01_ancestors(guard, parents)
                   if id(node) in conversion_ancestors), None)
    if not isinstance(common, ast.BoolOp):
        return False
    guard_child = _nm01_child_toward(common, guard, parents)
    conversion_child = _nm01_child_toward(common, conversion, parents)
    if guard_child is None or conversion_child is None:
        return False
    guard_index = next((i for i, value in enumerate(common.values)
                        if value is guard_child), -1)
    conversion_index = next((i for i, value in enumerate(common.values)
                             if value is conversion_child), -1)
    if guard_index < 0 or conversion_index <= guard_index:
        return False
    start = (getattr(guard, "end_lineno", guard.lineno),
             getattr(guard, "end_col_offset", guard.col_offset))
    end = (conversion.lineno, conversion.col_offset)
    return any(
        _nm01_namedexpr_rebinding_in(root, var, start, end)
        for root in common.values[guard_index:conversion_index + 1])
def _nm01_branch_test_expression_rebinding(
        var: str, guard: ast.AST, conversion: ast.AST,
        parents: dict[ast.AST, ast.AST]) -> bool:
    for ancestor in _nm01_ancestors(guard, parents):
        if not isinstance(ancestor, (ast.If, ast.IfExp, ast.While, ast.Assert)):
            continue
        if not in_subtree(guard, ancestor.test):
            continue
        if in_subtree(conversion, ancestor.test):
            return False
        start = (getattr(guard, "end_lineno", guard.lineno),
                 getattr(guard, "end_col_offset", guard.col_offset))
        return _nm01_namedexpr_rebinding_in(ancestor.test, var, start)
    return False
def _rebound_between(
        var: str, guard: ast.AST, conversion: ast.AST,
        parents: dict[ast.AST, ast.AST]) -> bool:
    bindings = _nm01_binding_statements_between(
        var, guard, conversion, parents)
    if bindings is None or bindings:
        return True
    if _nm01_boolop_expression_rebinding(var, guard, conversion, parents):
        return True
    return _nm01_branch_test_expression_rebinding(
        var, guard, conversion, parents)
def _nm01_guard_dominates(
        guard: ast.AST, context: _NM01DominanceContext, *,
        allow_partial_naninf: bool = False) -> bool:
    conversion_ancestors = {
        id(node) for node in _nm01_ancestors(
            context.conversion, context.parents)}
    common = next((node for node in _nm01_ancestors(guard, context.parents)
                   if id(node) in conversion_ancestors), None)
    if common is guard:
        return False
    partial_naninf = False
    if isinstance(common, ast.BoolOp):
        info = _nm01_guard_call_args(guard, frozenset())
        partial_naninf = (info is not None and info[0] == context.var
                          and info[1] in ("isnan", "isinf"))
    if (common is not None and (allow_partial_naninf or not partial_naninf)
            and _nm01_bool_guard_dominates(guard, common, context)):
        dominated = True
    else:
        dominated = _nm01_statement_guard_dominates(guard, context)
    if not dominated:
        return False
    return not _rebound_between(
        context.var, guard, context.conversion, context.parents)
def _nm01_rejection_guard_dominates(
        guard: ast.AST, context: _NM01DominanceContext) -> bool:
    current = guard
    while current is not None:
        parent = context.parents.get(current)
        if isinstance(parent, ast.If) and in_subtree(guard, parent.test):
            if any(in_subtree(context.conversion, stmt)
                   for stmt in parent.body):
                required = True
            elif (any(in_subtree(context.conversion, stmt)
                      for stmt in parent.orelse)
                  or (_block_terminates(parent.body)
                      and _nm01_later_in_block(parent, context))):
                required = False
            else:
                return False
            required = _nm01_required_guard_truth(
                parent.test, guard, required, context.parents)
            safe = _nm01_guard_safe_truth(guard, context.var)
            return (required is not None and safe is not None
                    and required == safe and not _rebound_between(
                        context.var, guard, context.conversion,
                        context.parents))
        current = parent
    return False
def _nm01_naninf_guards_dominate(
        guards: list[ast.AST], context: _NM01DominanceContext) -> bool:
    rejected: set[str] = set()
    for guard in guards:
        info = _nm01_guard_call_args(guard, frozenset())
        if (info is None or info[0] != context.var
                or info[1] not in ("isnan", "isinf")):
            continue
        if (_nm01_rejection_guard_dominates(guard, context)
                or _nm01_guard_dominates(
                    guard, context, allow_partial_naninf=True)):
            rejected.add(info[1])
    return rejected == {"isnan", "isinf"}
def _nm01_comp_region_findings(
        comp: ast.AST, filepath: str,
        inherited_try: bool,
        inherited_failed: frozenset[str],
        shadowed_builtins: frozenset[str],
        ) -> list[DiagnoseFinding]:
    region_locals = frozenset(comp_target_names(comp))
    if not region_locals:
        return []
    outer_iter_ids = _nm01_comp_outer_iter_ids(comp)
    region_nodes = [fact for fact in _nm01_iter_with_guards(
        comp,
        init_try=inherited_try,
        init_failed=inherited_failed - region_locals)
        if id(fact.node) not in outer_iter_ids]
    region_shadow = shadowed_builtins | frozenset(
        region_locals & _NM01_SHADOWABLE_BUILTINS)
    checked_vars = _nm01_checked_vars(
        region_nodes, region_locals, region_shadow)
    if not checked_vars:
        return []
    guard_pos, guard_nodes = _nm01_guard_evidence(region_nodes)
    return _nm01_conversion_findings(
        region_nodes, checked_vars, region_locals, filepath,
        _NM01GuardContext(
            guard_pos=guard_pos,
            guard_nodes=guard_nodes,
            parents=parent_map(comp),
            ifexp_conv_pos=_nm01_ifexp_body_conv_eval_pos(comp),
            comp_presence=_nm01_comp_presence(comp),
            shadowed_builtins=region_shadow))
def _nm01_lambda_owner_conv_id(
        fact: _NM01Fact, checked: set[str],
        shadowed_builtins: frozenset[str]) -> int | None:
    shadowed = shadowed_builtins | (
        fact.shadow & _NM01_SHADOWABLE_BUILTINS)
    if _nm01_conv_func_shadowed(fact.node, shadowed):
        return None
    var = _nm01_conv_call_var(fact.node)
    return id(fact.node) if var is not None and var in checked else None
def _nm01_keep_smallest_lambda_owner(
        owners: dict[int, int], sizes: dict[int, int], conv_id: int,
        scope: ast.Lambda, size: int) -> None:
    current = owners.get(conv_id)
    if current is None or size < sizes[current]:
        owners[conv_id] = id(scope)
        sizes[id(scope)] = size
def _nm01_lambda_conversion_owners(
        tree: ast.AST,
        scope_cache: dict[int, list[_NM01Fact]],
        shadow_by_scope: dict[int, frozenset[str]],
        ) -> dict[int, int]:
    owners: dict[int, int] = {}
    sizes: dict[int, int] = {}
    for scope in scope_roots(tree):
        if not isinstance(scope, ast.Lambda):
            continue
        nodes = scope_cache.get(id(scope)) or []
        shadowed_builtins = shadow_by_scope.get(id(scope), frozenset())
        checked = _nm01_checked_vars(nodes, shadowed_builtins=shadowed_builtins)
        if not checked:
            continue
        for fact in nodes:
            conv_id = _nm01_lambda_owner_conv_id(
                fact, checked, shadowed_builtins)
            if conv_id is not None:
                _nm01_keep_smallest_lambda_owner(
                    owners, sizes, conv_id, scope, len(nodes))
    return owners
def _nm01_lambda_node_ids(roots: list[ast.AST]) -> set[int]:
    ids: set[int] = set()
    for root in roots:
        for node in walk_nodes(root):
            if isinstance(node, ast.Lambda):
                ids.update(id(n) for n in walk_nodes(node))
    return ids
def _nm01_mark_conv_presence(
        root: ast.AST, guards: frozenset[str],
        presence: dict[int, frozenset[str]],
        skip_ids: frozenset[int] = _EMPTY_NAMES) -> None:
    if not guards:
        return
    for node in walk_nodes(root):
        if id(node) in skip_ids:
            continue
        if _nm01_conv_call_var(node) is not None:
            presence[id(node)] = (presence.get(id(node), frozenset())
                                  | guards)
def _nm01_comp_presence(comp: ast.AST) -> dict[int, frozenset[str]]:
    presence: dict[int, frozenset[str]] = {}
    guards: frozenset[str] = _EMPTY_NAMES
    for gen in getattr(comp, "generators", ()) or ():
        _nm01_mark_conv_presence(gen.iter, guards, presence)
        guards = guards - frozenset(iter_unpack_target_names(gen.target))
        for cond in gen.ifs:
            terms = _nm01_and_terms(cond)
            for index, term in enumerate(terms):
                _nm01_mark_conv_presence(
                    term, guards | _nm01_terms_guard_names(terms[:index]),
                    presence, frozenset(_nm01_lambda_node_ids([term])))
            guards = guards | _nm01_terms_guard_names(terms)
    roots = comp_element_roots(comp)
    skip_ids = frozenset(_nm01_lambda_node_ids(roots))
    for root in roots:
        _nm01_mark_conv_presence(root, guards, presence, skip_ids)
    return presence
def _nm01_comp_elt_presence(
        tree: ast.AST) -> dict[int, frozenset[str]]:
    presence: dict[int, frozenset[str]] = {}
    for comp in walk_nodes(tree):
        if not isinstance(comp, COMP_SCOPE_NODES):
            continue
        for node_id, guards in _nm01_comp_presence(comp).items():
            presence[node_id] = presence.get(node_id, frozenset()) | guards
    return presence
def _scope_shadowed_builtins(
        key: str, local_bindings: dict[str, frozenset[str]],
        candidates: frozenset[str],
        class_keys: frozenset[str] = _EMPTY_NAMES,
        *, own_is_class: bool = False) -> frozenset[str]:
    names: set[str] = set()
    for scope in _iter_scope_chain(key):
        if scope in class_keys and not (own_is_class and scope == key):
            continue
        names |= local_bindings.get(scope, frozenset())
    return frozenset(names & candidates)
def _nm01_statement_bindings(stmt: ast.AST) -> frozenset[str]:
    module = ast.Module(body=[stmt], type_ignores=[])
    return collect_shadow_bindings(module)[0].get("", frozenset())
class _SequentialBinding(NamedTuple):
    end: tuple[int, int]
    block: tuple[ast.AST, ...] | None = None
    is_binding: bool = True
    certain: bool = True
_SequentialBindings = dict[str, list[_SequentialBinding]]
def _nm01_test_binding_names(
        test: ast.AST, on_true: bool,
        candidates: frozenset[str]) -> frozenset[str]:
    return frozenset(
        node.target.id for node in _test_namedexprs(test, on_true)
        if isinstance(node.target, ast.Name) and node.target.id in candidates)
def _nm01_unconditional_expression_bindings(
        expression: ast.AST, candidates: frozenset[str]) -> frozenset[str]:
    return (_nm01_test_binding_names(expression, True, candidates)
            & _nm01_test_binding_names(expression, False, candidates))
class _NM01BindingEffect(NamedTuple):
    bound: frozenset[str]
    unbound: frozenset[str]
    changed: frozenset[str]
    may_unbound: frozenset[str]
    may_bound: frozenset[str]
def _nm01_new_binding_effect(
        bound: frozenset[str] = _EMPTY_NAMES,
        unbound: frozenset[str] = _EMPTY_NAMES) -> _NM01BindingEffect:
    return _NM01BindingEffect(
        bound, unbound, bound | unbound, unbound, bound)
def _nm01_effect_then(
        first: _NM01BindingEffect,
        second: _NM01BindingEffect) -> _NM01BindingEffect:
    bound = ((first.bound - second.changed) | second.bound) - second.unbound
    unbound = ((first.unbound - second.changed) | second.unbound) - second.bound
    may_unbound = (first.may_unbound | second.may_unbound) - second.bound
    may_bound = (first.may_bound | second.may_bound) - second.unbound
    return _NM01BindingEffect(
        frozenset(bound), frozenset(unbound), first.changed | second.changed,
        frozenset(may_unbound), frozenset(may_bound))
def _nm01_merge_binding_effects(
        paths: list[tuple[bool, _NM01BindingEffect]],
        candidates: frozenset[str]) -> _NM01BindingEffect:
    continuing = [effect for terminated, effect in paths if not terminated]
    if not continuing:
        return _NM01BindingEffect(
            candidates, candidates, candidates, candidates, candidates)
    bound = set.intersection(*(set(effect.bound) for effect in continuing))
    unbound = set.intersection(*(set(effect.unbound) for effect in continuing))
    changed = set().union(*(set(effect.changed) for effect in continuing))
    may_unbound = set().union(
        *(set(effect.may_unbound) for effect in continuing))
    may_bound = set().union(
        *(set(effect.may_bound) for effect in continuing))
    return _NM01BindingEffect(
        frozenset(bound), frozenset(unbound), frozenset(changed),
        frozenset(may_unbound - bound), frozenset(may_bound - unbound))
def _nm01_block_binding_effects(
        stmts: list[ast.stmt],
        candidates: frozenset[str]) -> _NM01BindingEffect:
    effect = _nm01_new_binding_effect()
    for stmt in stmts:
        effect = _nm01_effect_then(
            effect, _nm01_statement_binding_effects(stmt, candidates))
    return effect
def _nm01_statement_binding_effects(
        stmt: ast.stmt, candidates: frozenset[str]) -> _NM01BindingEffect:
    if isinstance(stmt, ast.Delete):
        deleted = {
            name for target in stmt.targets
            for name in iter_unpack_target_names(target)}
        return _nm01_new_binding_effect(
            unbound=frozenset(deleted & candidates))
    if isinstance(stmt, ast.If):
        body = _nm01_effect_then(
            _nm01_new_binding_effect(
                _nm01_test_binding_names(stmt.test, True, candidates)),
            _nm01_block_binding_effects(stmt.body, candidates))
        orelse = _nm01_effect_then(
            _nm01_new_binding_effect(
                _nm01_test_binding_names(stmt.test, False, candidates)),
            _nm01_block_binding_effects(stmt.orelse, candidates))
        return _nm01_merge_binding_effects([
            (_block_terminates(stmt.body), body),
            (_block_terminates(stmt.orelse), orelse),
        ], candidates)
    if isinstance(stmt, _NM01_TRY_TYPES):
        normal = _nm01_effect_then(
            _nm01_block_binding_effects(stmt.body, candidates),
            _nm01_block_binding_effects(stmt.orelse, candidates))
        normal_block = stmt.orelse or stmt.body
        paths = [(_block_terminates(normal_block), normal)]
        paths.extend(
            (_block_terminates(handler.body),
             _nm01_block_binding_effects(handler.body, candidates))
            for handler in stmt.handlers)
        effect = _nm01_merge_binding_effects(paths, candidates)
        if _block_terminates(stmt.finalbody):
            return _NM01BindingEffect(
                candidates, candidates, candidates, candidates, candidates)
        return _nm01_effect_then(
            effect, _nm01_block_binding_effects(stmt.finalbody, candidates))
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        targets = {
            name for item in stmt.items if item.optional_vars is not None
            for name in iter_unpack_target_names(item.optional_vars)}
        bound = frozenset(targets & candidates)
        for item in stmt.items:
            bound |= _nm01_unconditional_expression_bindings(
                item.context_expr, candidates)
        return _nm01_new_binding_effect(bound)
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        effect = _nm01_new_binding_effect(
            _nm01_unconditional_expression_bindings(stmt.iter, candidates))
        targets = frozenset(
            iter_unpack_target_names(stmt.target)) & candidates
        # 循环体可能零次执行，目标不是确定绑定；但只要在任一路径绑定，
        # 后续名称解析就可能看到该绑定，不能按仍指向内建名处理。
        return effect._replace(
            changed=effect.changed | targets,
            may_bound=effect.may_bound | targets)
    if isinstance(stmt, ast.While):
        return _nm01_new_binding_effect(
            _nm01_unconditional_expression_bindings(stmt.test, candidates))
    if isinstance(stmt, ast.Match):
        return _nm01_new_binding_effect(
            _nm01_unconditional_expression_bindings(stmt.subject, candidates))
    if isinstance(stmt, ast.Assert):
        return _nm01_new_binding_effect(
            _nm01_test_binding_names(stmt.test, True, candidates))
    return _nm01_new_binding_effect(
        _nm01_statement_bindings(stmt) & candidates)
def _sequential_scope_bindings(
        scope: ast.AST, candidates: frozenset[str],
) -> _SequentialBindings:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        candidates &= exec_scope_declarations(scope)[1]
    elif not isinstance(scope, (ast.Module, ast.ClassDef)):
        return {}
    if not candidates:
        return {}
    positions: _SequentialBindings = {}
    def add(names, node: ast.AST,
            block: tuple[ast.AST, ...] | None,
            *, is_binding: bool = True, certain: bool = True) -> None:
        end = (getattr(node, "end_lineno", node.lineno),
               getattr(node, "end_col_offset", node.col_offset))
        for name in names:
            positions.setdefault(name, []).append(
                _SequentialBinding(end, block, is_binding, certain))
    def walk_block(stmts: list[ast.stmt],
                   block: tuple[ast.AST, ...] | None) -> None:
        for stmt in stmts:
            effect = _nm01_statement_binding_effects(stmt, candidates)
            add(effect.bound, stmt, block)
            add(effect.unbound, stmt, block, is_binding=False)
            add(effect.may_unbound - effect.unbound, stmt, block,
                is_binding=False, certain=False)
            add(effect.may_bound - effect.bound, stmt, block,
                certain=False)
            if isinstance(stmt, (ast.If, ast.While)):
                add(_nm01_test_binding_names(stmt.test, True, candidates),
                    stmt.test, tuple(stmt.body))
                add(_nm01_test_binding_names(stmt.test, False, candidates),
                    stmt.test, tuple(stmt.orelse))
            if isinstance(stmt, (ast.For, ast.AsyncFor)):
                add(_nm01_unconditional_expression_bindings(
                    stmt.iter, candidates), stmt.iter, (stmt,))
                add(frozenset(iter_unpack_target_names(stmt.target)) & candidates,
                    stmt.target, tuple(stmt.body))
            elif isinstance(stmt, (ast.With, ast.AsyncWith)):
                for item in stmt.items:
                    add(_nm01_unconditional_expression_bindings(
                        item.context_expr, candidates),
                        item.context_expr, (stmt,))
                    if item.optional_vars is not None:
                        add(frozenset(iter_unpack_target_names(item.optional_vars))
                            & candidates, item.optional_vars, (stmt,))
            elif isinstance(stmt, ast.Match):
                add(_nm01_unconditional_expression_bindings(
                    stmt.subject, candidates), stmt.subject, (stmt,))
            if isinstance(stmt, _SCOPE_DEFINITION_NODES):
                continue
            for field_name in ("body", "orelse", "finalbody"):
                child_block = getattr(stmt, field_name, None)
                if (isinstance(child_block, list) and child_block
                        and all(isinstance(child, ast.stmt)
                                for child in child_block)):
                    walk_block(child_block, tuple(child_block))
            for handler in getattr(stmt, "handlers", ()) or ():
                if handler.name in candidates:
                    anchor = handler.type or handler
                    add({handler.name}, anchor, tuple(handler.body))
                walk_block(handler.body, tuple(handler.body))
            for case in getattr(stmt, "cases", ()) or ():
                walk_block(case.body, tuple(case.body))
    walk_block(scope.body, None)
    return positions
def _sequential_visible_shadow(
        node: ast.AST, shadow: frozenset[str],
        bindings: _SequentialBindings | None,
) -> frozenset[str]:
    if not bindings:
        return shadow
    pos = (getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
    visible = set(shadow)
    for name, records in bindings.items():
        states = {name in visible}
        for record in sorted(records, key=lambda item: item.end):
            if record.end > pos:
                continue
            if (record.block is not None
                    and not any(in_subtree(node, stmt)
                                for stmt in record.block)):
                continue
            if record.certain:
                states = {record.is_binding}
            else:
                states.add(record.is_binding)
        if True in states:
            visible.add(name)
        else:
            visible.discard(name)
    return frozenset(visible)
def _nm01_apply_sequential_shadow(
        facts: list[_NM01Fact],
        bindings: _SequentialBindings,
) -> list[_NM01Fact]:
    if not bindings:
        return facts
    return [fact._replace(
        shadow=fact.shadow | _sequential_visible_shadow(
            fact.node, _EMPTY_NAMES, bindings))
        for fact in facts]
def check_NM01(tree: ast.AST | None, source_lines: list[str],
               filepath: str = "") -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    analyzed_comps: set[int] = set()
    scope_table = _scope_keys(tree)
    ifexp_conv_pos = _nm01_ifexp_body_conv_eval_pos(tree)
    scopes = scope_roots(tree)
    local_bindings = _scope_local_bindings(scopes, scope_table.keys)
    scope_cache = {id(scope): list(_nm01_iter_with_guards(scope))
                   for scope in scopes}
    scope_shadow: dict[int, frozenset[str]] = {}
    for scope in scopes:
        key = scope_table.keys.get(id(scope), "")
        shadowed = _scope_shadowed_builtins(
            key, local_bindings, _NM01_SHADOWABLE_BUILTINS,
            scope_table.class_keys,
            own_is_class=isinstance(scope, ast.ClassDef))
        if isinstance(scope, (ast.Module, ast.ClassDef)):
            shadowed = shadowed - local_bindings.get(key, _EMPTY_NAMES)
        scope_shadow[id(scope)] = shadowed
    owned_convs = _nm01_lambda_conversion_owners(
        tree, scope_cache, scope_shadow)
    comp_presence = _nm01_comp_elt_presence(tree)
    for scope in scopes:
        sequential = _sequential_scope_bindings(
            scope, _NM01_SHADOWABLE_BUILTINS)
        scope_nodes = _nm01_apply_sequential_shadow(
            scope_cache[id(scope)], sequential)
        issues.extend(_nm01_analyze_scope(
            filepath, scope, analyzed_comps, ifexp_conv_pos,
            scope_nodes, comp_presence, owned_convs,
            scope_shadow[id(scope)]))
    return issues
def _nm01_region_issues(scope_nodes: list[_NM01Fact], filepath: str,
                        analyzed_comps: set[int],
                        shadowed_builtins: frozenset[str],
                        ) -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    for fact in scope_nodes:
        if fact.frames:
            continue
        node = fact.node
        if isinstance(node, COMP_SCOPE_NODES) and id(node) not in analyzed_comps:
            analyzed_comps.add(id(node))
            issues.extend(_nm01_comp_region_findings(
                node, filepath,
                inherited_try=fact.try_covered, inherited_failed=fact.failed,
                shadowed_builtins=shadowed_builtins
                | (fact.shadow & _NM01_SHADOWABLE_BUILTINS)))
    return issues
def _nm01_analyze_scope(filepath: str, scope: ast.AST,
                        analyzed_comps: set[int],
                        ifexp_conv_pos: dict[int, tuple[int, int]],
                        scope_nodes: list[_NM01Fact],
                        comp_presence: dict[int, frozenset[str]],
                        owned_convs: dict[int, int],
                        shadowed_builtins: frozenset[str],
                        ) -> list[DiagnoseFinding]:
    issues = _nm01_region_issues(
        scope_nodes, filepath, analyzed_comps, shadowed_builtins)
    checked_vars = _nm01_checked_vars(
        scope_nodes, shadowed_builtins=shadowed_builtins)
    if not checked_vars:
        return issues
    guard_pos, guard_nodes = _nm01_guard_evidence(scope_nodes)
    issues.extend(_nm01_conversion_findings(
        scope_nodes, checked_vars, None, filepath,
        _NM01GuardContext(
            guard_pos=guard_pos,
            guard_nodes=guard_nodes,
            parents=parent_map(scope),
            ifexp_conv_pos=ifexp_conv_pos,
            comp_presence=comp_presence,
            owned_convs=owned_convs,
            shadowed_builtins=shadowed_builtins)))
    return issues
_BI01_ARITH_OPS = (ast.Add, ast.Sub, ast.Mult, ast.Div, ast.FloorDiv,
                   ast.Mod, ast.Pow, ast.MatMult)
_BI01_AGG_BUILTINS = frozenset({"sum", "max", "min", "round", "abs"})
_BI01_SHADOWABLE_BUILTINS = _BI01_AGG_BUILTINS | frozenset(
    {"isinstance", "int", "float", "bool"})
def _bi01_negated_isinstance_ids(test: ast.AST) -> frozenset[int]:
    negated: set[int] = set()
    stack: list[tuple[ast.AST, bool]] = [(test, False)]
    while stack:
        node, neg = stack.pop()
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            stack.append((node.operand, not neg))
            continue
        if neg and _nm01_isinstance_check_args(node) is not None:
            negated.add(id(node))
        for child in ast.iter_child_nodes(node):
            stack.append((child, neg))
    return frozenset(negated)
def _bi01_lambda_body_ids(root: ast.AST) -> frozenset[int]:
    ids: set[int] = set()
    for node in walk_nodes(root):
        if isinstance(node, ast.Lambda):
            ids.update(id(sub) for sub in walk_nodes(node.body))
    return frozenset(ids)
def _bi01_intfloat_names(
        test: ast.AST,
        shadowed: frozenset[str] = _EMPTY_NAMES) -> set[str]:
    test = _nm01_bool_test_view(test)
    names: set[str] = set()
    negated = _bi01_negated_isinstance_ids(test)
    lambda_ids = _bi01_lambda_body_ids(test)
    def _match(node: ast.AST, visible: frozenset[str]) -> None:
        if id(node) in lambda_ids:
            return
        name = _bi01_numeric_isinstance_name(node, visible, negated)
        if name is not None:
            names.add(name)
    _match(test, root_binding_shadow(test, shadowed))
    for node, visible in iter_scope_nodes_with_shadow(test, shadowed):
        _match(node, visible)
    return names
def _bi01_branch_names(test: ast.AST, on_true: bool,
                       leaf: Callable[[ast.AST], set[str]], *,
                       leaf_on_true: bool) -> set[str]:
    test = _nm01_bool_test_view(test)
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _bi01_branch_names(
            test.operand, not on_true, leaf, leaf_on_true=leaf_on_true)
    if isinstance(test, ast.BoolOp):
        parts = [_bi01_branch_names(value, on_true, leaf,
                                    leaf_on_true=leaf_on_true)
                 for value in test.values]
        if not parts:
            return set()
        all_required = ((on_true and isinstance(test.op, ast.And))
                        or (not on_true and isinstance(test.op, ast.Or)))
        if all_required:
            return set().union(*parts)
        narrowed = set(parts[0])
        for part in parts[1:]:
            narrowed &= part
        return narrowed
    if on_true != leaf_on_true:
        return set()
    return leaf(test)
def _bi01_branch_intfloat_names(
        test: ast.AST, on_true: bool,
        shadowed: frozenset[str] = _EMPTY_NAMES) -> set[str]:
    return _bi01_branch_names(
        test, on_true,
        lambda node: _bi01_intfloat_names(node, shadowed),
        leaf_on_true=True)
def _bi01_type_name_enabled(
        ty: ast.AST, name: str,
        shadowed: frozenset[str] = _EMPTY_NAMES) -> bool:
    return name in _nm01_type_names(ty) and name not in shadowed
def _bi01_numeric_isinstance_name(
    node: ast.AST, shadowed: frozenset[str],
    negated: frozenset[int],
) -> str | None:
    info = _nm01_isinstance_check_args(node)
    if info is None or id(node) in negated:
        return None
    name, ty = info
    if name in shadowed:
        return None
    if not (_bi01_type_name_enabled(ty, "int", shadowed)
            or _bi01_type_name_enabled(ty, "float", shadowed)):
        return None
    return name
def _bi01_bool_guard_name(
        test: ast.AST,
        shadowed: frozenset[str] = _EMPTY_NAMES) -> str | None:
    info = _nm01_isinstance_check_args(test)
    if (info is not None
            and _bi01_type_name_enabled(info[1], "bool", shadowed)):
        return info[0]
    return None
def _bi01_int_guard_name(
        test: ast.AST,
        shadowed: frozenset[str] = _EMPTY_NAMES) -> str | None:
    info = _nm01_isinstance_check_args(test)
    if (info is not None
            and _bi01_type_name_enabled(info[1], "int", shadowed)):
        return info[0]
    return None
def _bi01_float_only_guard_name(
        test: ast.AST, shadowed: frozenset[str]) -> str | None:
    info = _nm01_isinstance_check_args(test)
    if info is None:
        return None
    names = _nm01_type_names(info[1])
    if (names and all(name == "float" for name in names)
            and "float" not in shadowed):
        return info[0]
    return None
def _bi01_excluded_leaf(test: ast.AST,
                        shadowed: frozenset[str]) -> set[str]:
    names: set[str] = set()
    for name in (_bi01_bool_guard_name(test, shadowed),
                 _bi01_int_guard_name(test, shadowed)):
        if name is not None:
            names.add(name)
    return names
class _BI01BoolGuard(NamedTuple):
    name: str
    node: ast.AST
    safe_on_true: bool
def _bi01_scope_nodes(scope: ast.AST) -> Iterator[ast.AST]:
    stack = list(reversed(list(_execution_scope_children(scope))))
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, _SCOPE_DEFINITION_NODES):
            stack.extend(reversed(list(iter_def_site_nodes(node))))
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
def _bi01_bool_guards(
        scope: ast.AST,
        shadowed: frozenset[str] = _EMPTY_NAMES,
        sequential_bindings: _SequentialBindings | None = None,
        ) -> list[_BI01BoolGuard]:
    guards: list[_BI01BoolGuard] = []
    for node in _bi01_scope_nodes(scope):
        if not isinstance(node, (ast.If, ast.While, ast.Assert)):
            continue
        visible_shadow = _sequential_visible_shadow(
            node, shadowed, sequential_bindings)
        if "isinstance" in visible_shadow:
            continue
        for name in _bi01_bool_excluded_names(
                node.test, True, visible_shadow):
            guards.append(_BI01BoolGuard(name, node, True))
        if isinstance(node, ast.Assert):
            continue
        for name in _bi01_bool_excluded_names(
                node.test, False, visible_shadow):
            guards.append(_BI01BoolGuard(name, node, False))
    return guards
def _bi01_guard_dominates(
        guard: _BI01BoolGuard, node: ast.AST,
        parents: dict[ast.AST, ast.AST]) -> bool:
    if_node = guard.node
    if isinstance(if_node, ast.Assert):
        block = _statement_block(parents.get(if_node), if_node)
        if block is None:
            return False
        later = block[block.index(if_node) + 1:]
        return any(in_subtree(node, stmt) for stmt in later)
    continuing = if_node.body if guard.safe_on_true else if_node.orelse
    if any(in_subtree(node, stmt) for stmt in continuing):
        return True
    if not isinstance(if_node, ast.If):
        return False
    terminated = if_node.orelse if guard.safe_on_true else if_node.body
    if not _block_terminates(terminated):
        return False
    block = _statement_block(parents.get(if_node), if_node)
    if block is None:
        return False
    later = block[block.index(if_node) + 1:]
    return any(in_subtree(node, stmt) for stmt in later)
def _bi01_bool_excluded_names(
        test: ast.AST, on_true: bool = True,
        shadowed: frozenset[str] = _EMPTY_NAMES) -> set[str]:
    return _bi01_branch_names(
        test, on_true,
        lambda node: _bi01_excluded_leaf(node, shadowed),
        leaf_on_true=False)
def _bi01_float_excluded_names(
        test: ast.AST, on_true: bool,
        shadowed: frozenset[str] = _EMPTY_NAMES) -> set[str]:
    return _bi01_branch_names(
        test, on_true,
        lambda node: (
            {name} if (name := _bi01_float_only_guard_name(node, shadowed))
            is not None else set()),
        leaf_on_true=True)
def _bi01_narrowing_partition(
        test: ast.AST, on_true: bool,
        shadowed: frozenset[str] = _EMPTY_NAMES,
) -> tuple[set[str], set[str]]:
    narrowed = _bi01_branch_intfloat_names(test, on_true, shadowed)
    excluded = narrowed & (
        _bi01_bool_excluded_names(test, on_true, shadowed)
        | _bi01_float_excluded_names(test, on_true, shadowed))
    return narrowed - excluded, excluded
def _bi01_collect_names(hit_nodes: dict[str, ast.AST], live: set[str],
                        root: ast.AST, shadowed: frozenset[str],
                        anchor: ast.AST) -> None:
    if isinstance(root, ast.Name):
        if root.id in live and root.id not in shadowed:
            hit_nodes.setdefault(root.id, anchor)
        return
    for sub, sh in iter_scope_nodes_with_shadow(
            root, root_binding_shadow(root, shadowed)):
        if (isinstance(sub, ast.Name) and sub.id in live
                and sub.id not in sh):
            hit_nodes.setdefault(sub.id, anchor)
def _bi01_check_anchor(
        hit_nodes: dict[str, ast.AST], live: set[str],
        node: ast.AST, shadowed: frozenset[str],
        builtin_shadow: frozenset[str],
        sequential_bindings: _SequentialBindings | None = None,
) -> None:
    if isinstance(node, ast.BinOp) and isinstance(node.op, _BI01_ARITH_OPS):
        _bi01_collect_names(hit_nodes, live, node, shadowed, node)
    elif isinstance(node, ast.AugAssign) and isinstance(node.op, _BI01_ARITH_OPS):
        _bi01_augassign_hit(hit_nodes, live, node, shadowed)
    elif _bi01_agg_call(
            node, shadowed | builtin_shadow | _sequential_visible_shadow(
                node, _EMPTY_NAMES, sequential_bindings)):
        operands = list(node.args)
        if node.func.id == "round":
            operands.extend(
                kw.value for kw in node.keywords if kw.arg == "number")
        for arg in operands:
            _bi01_collect_names(hit_nodes, live, arg, shadowed, node)
def _bi01_augassign_hit(
    hit_nodes: dict[str, ast.AST], live: set[str],
    node: ast.AugAssign, shadowed: frozenset[str],
) -> None:
    if (isinstance(node.target, ast.Name)
            and node.target.id in live
            and node.target.id not in shadowed):
        hit_nodes.setdefault(node.target.id, node)
    _bi01_collect_names(hit_nodes, live, node.value, shadowed, node)
def _bi01_agg_call(node: ast.AST, shadowed: frozenset[str]) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in _BI01_AGG_BUILTINS
            and node.func.id not in shadowed)
def _bi01_collect_body_hits(
        stmts: list[ast.AST], live: set[str],
        builtin_shadow: frozenset[str],
        sequential_bindings: _SequentialBindings | None = None,
) -> dict[str, ast.AST]:
    hit_nodes: dict[str, ast.AST] = {}
    for stmt in stmts:
        roots = (iter_def_site_nodes(stmt)
                 if isinstance(stmt, SHADOW_SCOPE_STOP) else (stmt,))
        for root in roots:
            _bi01_check_anchor(
                hit_nodes, live, root, frozenset(), builtin_shadow,
                sequential_bindings)
            for node, shadowed in iter_scope_nodes_with_shadow(root):
                _bi01_check_anchor(
                    hit_nodes, live, node, shadowed, builtin_shadow,
                    sequential_bindings)
    return hit_nodes
def _bi01_post_branch_hits(
        if_node: ast.If, live_on_true: set[str], live_on_false: set[str],
        parents: dict[ast.AST, ast.AST], builtin_shadow: frozenset[str],
        sequential_bindings: _SequentialBindings | None = None,
) -> dict[str, ast.AST]:
    body_terminates = _block_terminates(if_node.body)
    else_terminates = _block_terminates(if_node.orelse)
    if body_terminates == else_terminates:
        return {}
    live = live_on_false if body_terminates else live_on_true
    if not live:
        return {}
    block = _statement_block(parents.get(if_node), if_node)
    if block is None:
        return {}
    later = block[block.index(if_node) + 1:]
    return _bi01_collect_body_hits(
        later, live, builtin_shadow, sequential_bindings)
def _bi01_merge_hits(
        target: dict[str, ast.AST], source: dict[str, ast.AST]) -> None:
    for name, anchor in source.items():
        target.setdefault(name, anchor)
def _bi01_short_circuit_test_hits(
        test: ast.AST, shadow: frozenset[str],
        builtin_shadow: frozenset[str],
        sequential_bindings: _SequentialBindings | None = None,
        inherited_live: frozenset[str] = _EMPTY_NAMES,
        include_excluded: bool = False,
) -> dict[str, ast.AST]:
    if not isinstance(test, ast.BoolOp):
        return {}
    hits: dict[str, ast.AST] = {}
    on_true = isinstance(test.op, ast.And)
    for index, value in enumerate(test.values):
        live = set(inherited_live)
        if index:
            previous_values = list(test.values[:index])
            previous = (previous_values[0] if len(previous_values) == 1
                        else ast.BoolOp(op=test.op, values=previous_values))
            narrowed, excluded = _bi01_narrowing_partition(
                previous, on_true, shadow)
            live |= excluded if include_excluded else narrowed
        _bi01_merge_hits(hits, _bi01_collect_body_hits(
            [value], live, builtin_shadow, sequential_bindings))
        _bi01_merge_hits(hits, _bi01_short_circuit_test_hits(
            value, shadow, builtin_shadow, sequential_bindings,
            frozenset(live), include_excluded))
    return hits
def check_BI01(tree: ast.AST | None, source_lines: list[str],
               filepath: str = "") -> list[DiagnoseFinding]:
    issues: list[DiagnoseFinding] = []
    if tree is None:
        return issues
    if finding_scan_exempt(filepath):
        return issues
    scope_table = _scope_keys(tree)
    scopes = scope_roots(tree)
    local_bindings = _scope_local_bindings(scopes, scope_table.keys)
    for scope in scopes:
        key = scope_table.keys.get(id(scope), "")
        shadowed = _scope_shadowed_builtins(
            key, local_bindings, _BI01_SHADOWABLE_BUILTINS,
            scope_table.class_keys,
            own_is_class=isinstance(scope, ast.ClassDef))
        sequential = _sequential_scope_bindings(
            scope, _BI01_SHADOWABLE_BUILTINS)
        if sequential:
            shadowed = shadowed - local_bindings.get(key, _EMPTY_NAMES)
        for var, line in _bi01_scope_hits(
                scope, shadowed & _BI01_AGG_BUILTINS, shadowed,
                sequential_bindings=sequential):
            issues.append(_bi01_finding(var, line, filepath))
    return issues
def _bi01_guarded_hit(
        var: str, anchor: ast.AST,
        guards: list[_BI01BoolGuard],
        parents: dict[ast.AST, ast.AST]) -> bool:
    return any(
        guard.name == var
        and _bi01_guard_dominates(guard, anchor, parents)
        and not _rebound_between(var, guard.node, anchor, parents)
        for guard in guards)
def _bi01_append_unseen_hit(hits: list[tuple[str, int]],
                            seen_pairs: set[tuple[str, int]],
                            var: str, line: int) -> None:
    if (var, line) not in seen_pairs:
        seen_pairs.add((var, line))
        hits.append((var, line))
def _bi01_assignment_target_values(
        target: ast.AST, value: ast.AST) -> list[tuple[str, ast.AST]]:
    if isinstance(target, ast.Name):
        return [(target.id, value)]
    if (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(elt, ast.Starred)
                        for elt in (*target.elts, *value.elts))):
        return [
            pair
            for target_elt, value_elt in zip(
                target.elts, value.elts, strict=True)
            for pair in _bi01_assignment_target_values(target_elt, value_elt)
        ]
    return []
def _bi01_direct_assignment_value(
        stmt: ast.stmt, var: str) -> tuple[bool, ast.AST | None]:
    if isinstance(stmt, ast.Assign):
        matches = [
            bound_value
            for target in stmt.targets
            for name, bound_value in _bi01_assignment_target_values(
                target, stmt.value)
            if name == var
        ]
        if matches:
            return True, matches[-1]
    if (isinstance(stmt, ast.AnnAssign)
            and isinstance(stmt.target, ast.Name) and stmt.target.id == var):
        return True, stmt.value
    if (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.NamedExpr)
            and isinstance(stmt.value.target, ast.Name)
            and stmt.value.target.id == var):
        return True, stmt.value.value
    if isinstance(stmt, (ast.If, ast.While, ast.Assert)):
        candidates = [
            node for node in _unconditional_test_namedexprs(stmt.test)
            if isinstance(node.target, ast.Name) and node.target.id == var]
        if len(candidates) == 1:
            return True, candidates[0].value
    return False, None
def _test_namedexprs(test: ast.AST,
                          on_true: bool) -> list[ast.NamedExpr]:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _test_namedexprs(test.operand, not on_true)
    if isinstance(test, ast.BoolOp):
        exhaustive = ((on_true and isinstance(test.op, ast.And))
                      or (not on_true and isinstance(test.op, ast.Or)))
        if not exhaustive:
            return []
        child_truth = isinstance(test.op, ast.And)
        return [
            node for value in test.values
            for node in _test_namedexprs(value, child_truth)]
    found: list[ast.NamedExpr] = []
    stack = [test]
    while stack:
        node = stack.pop()
        if isinstance(node, (*SHADOW_SCOPE_STOP, *COMP_SCOPE_NODES, ast.IfExp)):
            continue
        if isinstance(node, ast.NamedExpr):
            found.append(node)
        stack.extend(ast.iter_child_nodes(node))
    return sorted(found, key=lambda node: (node.lineno, node.col_offset))
def _unconditional_test_namedexprs(
        test: ast.AST) -> list[ast.NamedExpr]:
    on_true = _test_namedexprs(test, True)
    false_ids = {id(node) for node in _test_namedexprs(test, False)}
    return [node for node in on_true if id(node) in false_ids]
def _test_namedexprs_before(
        test: ast.AST, anchor: ast.AST,
        parents: dict[ast.AST, ast.AST]) -> list[ast.NamedExpr]:
    path: list[tuple[ast.AST, ast.AST]] = []
    current = anchor
    while current is not test:
        parent = parents.get(current)
        if parent is None:
            return []
        path.append((parent, current))
        current = parent
    found: list[ast.NamedExpr] = []
    for parent, child in reversed(path):
        if not isinstance(parent, ast.BoolOp):
            continue
        try:
            index = parent.values.index(child)
        except ValueError:
            continue
        for value in parent.values[:index]:
            found.extend(_unconditional_test_namedexprs(value))
    return sorted(found, key=lambda node: (node.lineno, node.col_offset))
def _bi01_branch_continuation_truth(
        branch: ast.AST, anchor: ast.AST) -> bool | None:
    if isinstance(branch, ast.Assert):
        return True
    body = (branch.body if isinstance(branch, (ast.If, ast.While))
            else [branch.body])
    orelse = (branch.orelse if isinstance(branch, (ast.If, ast.While))
              else [branch.orelse])
    if any(in_subtree(anchor, stmt) for stmt in body):
        return True
    if any(in_subtree(anchor, stmt) for stmt in orelse):
        return False
    if isinstance(branch, ast.If):
        body_terminates = _block_terminates(branch.body)
        else_terminates = _block_terminates(branch.orelse)
        if body_terminates != else_terminates:
            return not body_terminates
    return None
def _bi01_guaranteed_bool_rebinding(
        stmt: ast.AST, value: ast.AST | None,
        shadowed: frozenset[str],
        sequential_bindings: _SequentialBindings | None) -> bool:
    if isinstance(value, ast.Constant) and isinstance(value.value, bool):
        return True
    if not (isinstance(value, ast.Call)
            and isinstance(value.func, ast.Name)
            and value.func.id == "bool"):
        return False
    visible = _sequential_visible_shadow(
        stmt, shadowed, sequential_bindings)
    return "bool" not in visible
def _bi01_block_rebinding_states(
        stmts: list[ast.stmt], var: str, anchor: ast.AST,
        parents: dict[ast.AST, ast.AST], shadowed: frozenset[str],
        sequential_bindings: _SequentialBindings | None,
) -> set[str]:
    states = {"unchanged"}
    for stmt in stmts:
        if var not in _nm01_statement_bindings(stmt):
            continue
        direct, value = _bi01_direct_assignment_value(stmt, var)
        if direct:
            if isinstance(value, ast.Name) and value.id == var:
                effects = {"unchanged"}
            else:
                effects = {"bool" if _bi01_guaranteed_bool_rebinding(
                    stmt, value, shadowed, sequential_bindings) else "lost"}
        elif isinstance(stmt, ast.If):
            effects = _bi01_if_rebinding_states(
                stmt, var, anchor, parents, shadowed, sequential_bindings)
        else:
            effects = {"lost"}
        merged: set[str] = set()
        for effect in effects:
            if effect == "unchanged":
                merged |= states
            else:
                merged.add(effect)
        states = merged
    return states
def _bi01_if_rebinding_states(
        stmt: ast.If, var: str, anchor: ast.AST,
        parents: dict[ast.AST, ast.AST], shadowed: frozenset[str],
        sequential_bindings: _SequentialBindings | None,
) -> set[str]:
    if any(isinstance(node, ast.NamedExpr)
           and isinstance(node.target, ast.Name)
           and node.target.id == var for node in walk_nodes(stmt.test)):
        return {"lost"}
    continuation = _bi01_branch_continuation_truth(stmt, anchor)
    states: set[str] = set()
    for truth, block in ((True, stmt.body), (False, stmt.orelse)):
        if continuation is not None and continuation != truth:
            continue
        states |= _bi01_block_rebinding_states(
            block, var, anchor, parents, shadowed, sequential_bindings)
    return states
def _bi01_rebinding_state(
        var: str, branch: ast.AST, anchor: ast.AST,
        parents: dict[ast.AST, ast.AST],
        shadowed: frozenset[str],
        sequential_bindings: _SequentialBindings | None) -> str:
    bindings = _nm01_binding_statements_between(
        var, branch, anchor, parents)
    if bindings is None:
        return "lost"
    events: list[tuple[ast.AST, ast.AST | None, bool]] = []
    branch_test = (branch.test if isinstance(
        branch, (ast.If, ast.IfExp, ast.While, ast.Assert)) else branch)
    if in_subtree(anchor, branch_test):
        test_events = _test_namedexprs_before(
            branch_test, anchor, parents)
    else:
        continuation = _bi01_branch_continuation_truth(branch, anchor)
        test_events = (_test_namedexprs(branch_test, continuation)
                       if continuation is not None else [])
    events.extend(
        (node, node.value, True)
        for node in test_events
        if isinstance(node.target, ast.Name) and node.target.id == var)
    for stmt in bindings:
        direct, value = _bi01_direct_assignment_value(stmt, var)
        events.append((stmt, value, direct))
    for stmt, value, direct in reversed(events):
        if not direct:
            if isinstance(stmt, ast.If):
                conditional = _bi01_if_rebinding_states(
                    stmt, var, anchor, parents, shadowed,
                    sequential_bindings)
                if "bool" in conditional:
                    return "bool"
                if "unchanged" in conditional:
                    continue
            return "lost"
        if isinstance(value, ast.Name) and value.id == var:
            continue
        return ("bool" if _bi01_guaranteed_bool_rebinding(
            stmt, value, shadowed, sequential_bindings) else "lost")
    return "unchanged"
def _bi01_scope_hits(
        scope: ast.AST, builtin_shadow: frozenset[str],
        shadow: frozenset[str] = _EMPTY_NAMES,
        *, sequential_bindings: _SequentialBindings | None = None,
) -> list[tuple[str, int]]:
    seen_pairs: set[tuple[str, int]] = set()
    hits: list[tuple[str, int]] = []
    guards = _bi01_bool_guards(scope, shadow, sequential_bindings)
    parents = parent_map(scope)
    for if_node in [n for n in _bi01_scope_nodes(scope)
                    if isinstance(n, (ast.If, ast.IfExp, ast.While,
                                      ast.Assert, ast.BoolOp))]:
        visible_shadow = _sequential_visible_shadow(
            if_node, shadow, sequential_bindings)
        test = (if_node.test if isinstance(
            if_node, (ast.If, ast.IfExp, ast.While, ast.Assert))
            else if_node)
        if "isinstance" in visible_shadow:
            continue
        live, excluded = _bi01_narrowing_partition(
            test, True, visible_shadow)
        false_live, false_excluded = _bi01_narrowing_partition(
            test, False, visible_shadow)
        def record(candidates: dict[str, ast.AST], *,
                   was_excluded: bool = False,
                   branch: ast.AST = if_node,
                   visible: frozenset[str] = visible_shadow) -> None:
            for var, anchor in candidates.items():
                state = _bi01_rebinding_state(
                    var, branch, anchor, parents, visible,
                    sequential_bindings)
                if state == "lost" or (was_excluded and state != "bool"):
                    continue
                if _bi01_guarded_hit(var, anchor, guards, parents):
                    continue
                _bi01_append_unseen_hit(hits, seen_pairs, var, anchor.lineno)
        if isinstance(if_node, ast.If):
            record(_bi01_post_branch_hits(
                if_node, live, false_live, parents, builtin_shadow,
                sequential_bindings))
            record(_bi01_post_branch_hits(
                if_node, excluded, false_excluded, parents, builtin_shadow,
                sequential_bindings), was_excluded=True)
        elif isinstance(if_node, ast.Assert):
            block = _statement_block(parents.get(if_node), if_node)
            later = ([] if block is None
                     else block[block.index(if_node) + 1:])
            record(_bi01_collect_body_hits(
                later, live, builtin_shadow, sequential_bindings))
            record(_bi01_collect_body_hits(
                later, excluded, builtin_shadow, sequential_bindings),
                was_excluded=True)
        record(_bi01_short_circuit_test_hits(
            test, visible_shadow, builtin_shadow, sequential_bindings))
        record(_bi01_short_circuit_test_hits(
            test, visible_shadow, builtin_shadow, sequential_bindings,
            include_excluded=True), was_excluded=True)
        if isinstance(if_node, (ast.If, ast.While)):
            body = if_node.body
            orelse = if_node.orelse
        elif isinstance(if_node, ast.IfExp):
            body = [if_node.body]
            orelse = [if_node.orelse]
        else:
            body = []
            orelse = []
        record(_bi01_collect_body_hits(
            body, live, builtin_shadow, sequential_bindings))
        record(_bi01_collect_body_hits(
            body, excluded, builtin_shadow, sequential_bindings),
            was_excluded=True)
        record(_bi01_collect_body_hits(
            orelse, false_live, builtin_shadow, sequential_bindings))
        record(_bi01_collect_body_hits(
            orelse, false_excluded, builtin_shadow, sequential_bindings),
            was_excluded=True)
    return hits
def _bi01_finding(var: str, line: int, filepath: str) -> DiagnoseFinding:
    return DiagnoseFinding(
        id="BI-01", severity="P2", dimension="type",
        file=filepath, line=line,
        description=(f"{var} 经 isinstance(int/float) 判定后参与算术，"
                     "未排除 bool（True/False 按 1/0 混入统计）"),
        suggestion=("根因: bool 是 int 子类，isinstance(True, int) "
                    "为真，True/False 混入后统计/覆盖率/置信度被悄悄"
                    "污染（例如统计场景把布尔成功标记算成 1 次"
                    "有效样本）。\n"
                    "修复策略: isinstance(x, (int, float)) and "
                    "not isinstance(x, bool) 双判定后再参与算术\n"
                    "参考标准: Python 数据模型（bool 是 int 的子类）"),
    )
def wiring_declarations() -> dict:
    return {"catalogs": {
        "aicoder_direct": {
            'BI-01': check_BI01, 'NM-01': check_NM01,
        },
        "traps_bindings": {
            'BI01': check_BI01, 'NM01': check_NM01,
        },
    }}

from __future__ import annotations

import ast
import logging
import math
import os
import re
import sys
import threading
from collections.abc import Callable, Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any

try:
    import z3
except ImportError as _imp_err:
    logging.getLogger(__name__).debug(
        "[diag_taint_symbolic] z3 导入失败，符号求解降级启发式: %s",
        _imp_err)
    z3 = None
from jwsgj.diag_shared_ast_nodes import (
    iter_arg_nodes,
    parse_ast_safely,
    resolve_call_name,
)
from jwsgj.diag_shared_ast_views import (
    collect_lexical_scope_table,
    same_scope_bfs_nodes,
    scope_import_tables,
)
from jwsgj.diag_shared_source_core import read_source_cached
from jwsgj.diag_taint_model import (
    BUILTIN_SINKS,
    CONTAINER_STMTS,
    SINK_NAMES,
    container_header_exprs,
    container_sub_bodies,
)
from jwsgj.diag_types_defs import ExecutionPath
from jwsgj.diag_types_vocab import normalize_filepath
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    'DEFAULT_SINK_NAMES',
    'MAX_PATHS',
    'BranchPoint',
    'ConcolicInput',
    'SeedGenerator',
    'SymbolicExecutor',
    'concolic_file_score',
    'expr_to_constraint',
    'guided_concolic_explore',
    'negate_constraint',
]
logger = logging.getLogger(__name__)
Z3_LOCK = threading.Lock()
MAX_PATHS = 64
_SMT_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
_SMT_CMP_OPS: dict[type, str] = {
    ast.Eq: '=', ast.NotEq: 'distinct', ast.Is: '=', ast.IsNot: 'distinct',
    ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>=',
}
_ORDER_CMP_SYMS = frozenset(('<', '<=', '>', '>='))
_ExpressionGuards = tuple[tuple[ast.AST, bool], ...]
def _smt_term(node: ast.AST) -> tuple[str, dict[str, str]] | None:
    if isinstance(node, ast.Name):
        return _smt_name(node)
    if isinstance(node, ast.Constant):
        return _smt_constant(node)
    if isinstance(node, ast.UnaryOp):
        return _smt_unary_op(node)
    if isinstance(node, ast.BoolOp):
        return _smt_bool_op(node)
    if isinstance(node, ast.Compare):
        return _compare_term(node)
    return None
def _smt_symbol(name: str) -> str:
    if name in _SMT_TERM_KEYWORDS:
        return f"|py:{name}|"
    if _SMT_IDENT_RE.match(name):
        return name
    return f"|{name}|"
def _smt_name(node: ast.Name) -> tuple[str, dict[str, str]] | None:
    name = node.id
    if not isinstance(name, str) or not name.isidentifier():
        return None
    if "|" in name or "\\" in name:
        return None
    return _smt_symbol(name), {name: "Bool"}
def _real_literal(value: float) -> str | None:
    if not math.isfinite(value):
        return None
    numerator, denominator = value.as_integer_ratio()
    return f"(/ {numerator} {denominator})"
def _constant_truth(node: ast.Constant) -> str | None:
    value = node.value
    if isinstance(value, (bool, int, float, str, bytes, type(None))):
        return "true" if value else "false"
    return None
def _signed_literal_truth(expr: ast.AST) -> str | None:
    if not (isinstance(expr, ast.UnaryOp)
            and isinstance(expr.op, (ast.USub, ast.UAdd))
            and isinstance(expr.operand, ast.Constant)):
        return None
    value = expr.operand.value
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return "true" if value else "false"
def _condition_truth(expr: ast.AST) -> str | None:
    if isinstance(expr, ast.Constant):
        return _constant_truth(expr)
    if isinstance(expr, (ast.List, ast.Tuple, ast.Dict, ast.Set)):
        try:
            value = ast.literal_eval(expr)
        except (SyntaxError, ValueError, TypeError, MemoryError, RecursionError):
            return None
        return "true" if value else "false"
    return _signed_literal_truth(expr)
def _definition_time_children(node: ast.AST) -> list[ast.AST] | None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        returns = getattr(node, "returns", None)
        return [
            *getattr(node, "decorator_list", ()),
            *node.args.defaults,
            *(value for value in node.args.kw_defaults if value is not None),
            *(arg.annotation for arg in iter_arg_nodes(node.args)
              if arg.annotation is not None),
            *((returns,) if returns is not None else ()),
        ]
    if isinstance(node, ast.ClassDef):
        return [
            *node.decorator_list,
            *node.bases,
            *(keyword.value for keyword in node.keywords),
            *node.body,
        ]
    return None
def _iter_executable_calls_with_guards(
        expr: ast.AST) -> Iterator[tuple[ast.Call, _ExpressionGuards]]:
    stack: list[tuple[ast.AST, _ExpressionGuards]] = [(expr, ())]
    while stack:
        node, guards = stack.pop()
        definition_children = _definition_time_children(node)
        if definition_children is not None:
            stack.extend(reversed(
                [(child, guards) for child in definition_children]))
            continue
        if isinstance(node, ast.Call):
            yield node, guards
        children = [(child, guards) for child in ast.iter_child_nodes(node)]
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Lambda):
            children.append((node.func.body, guards))
        if isinstance(node, ast.BoolOp):
            children = []
            prior_guards: list[tuple[ast.AST, bool]] = []
            for value in node.values:
                children.append((value, guards + tuple(prior_guards)))
                truth = _condition_truth(value)
                if ((isinstance(node.op, ast.And) and truth == "false")
                        or (isinstance(node.op, ast.Or) and truth == "true")):
                    break
                if truth is None:
                    prior_guards.append((value, isinstance(node.op, ast.And)))
        elif isinstance(node, ast.Compare):
            children = [(node.left, guards)]
            prior_guards: list[tuple[ast.AST, bool]] = []
            left = node.left
            for op, comparator in zip(node.ops, node.comparators, strict=False):
                children.append((comparator, guards + tuple(prior_guards)))
                prior_guards.append((ast.Compare(
                    left=left, ops=[op], comparators=[comparator]), True))
                left = comparator
        elif isinstance(node, ast.IfExp):
            truth = _condition_truth(node.test)
            if truth == "true":
                children = [(node.test, guards), (node.body, guards)]
            elif truth == "false":
                children = [(node.test, guards), (node.orelse, guards)]
            else:
                children = [
                    (node.test, guards),
                    (node.body, guards + ((node.test, True),)),
                    (node.orelse, guards + ((node.test, False),)),
                ]
        elif isinstance(node, ast.If):
            children = [(node.test, guards)]
            children.extend(
                (child, guards + ((node.test, True),))
                for child in node.body)
            children.extend(
                (child, guards + ((node.test, False),))
                for child in node.orelse)
        stack.extend(reversed(children))
def _smt_constant(node: ast.Constant) -> tuple[str, dict[str, str]] | None:
    value = node.value
    if isinstance(value, bool):
        return ("true" if value else "false"), {}
    if isinstance(value, int):
        return str(value), {}
    if isinstance(value, float):
        literal = _real_literal(value)
        return (literal, {}) if literal is not None else None
    return None
def _smt_bool_op(node: ast.BoolOp) -> tuple[str, dict[str, str]] | None:
    op = "and" if isinstance(node.op, ast.And) else "or"
    parts: list[str] = []
    decls: dict[str, str] = {}
    for value in node.values:
        truth = _condition_truth(value)
        if truth is not None:
            parts.append(truth)
            continue
        term = _smt_term(value)
        if term is None:
            return None
        if not _merge_decls(decls, term[1]):
            return None
        parts.append(term[0])
    return f"({op} {' '.join(parts)})", decls
def _merge_decls(decls: dict[str, str], extra: dict[str, str]) -> bool:
    for name, sort in extra.items():
        known = decls.get(name)
        if known is not None and known != sort:
            if {known, sort} == {"Int", "Real"}:
                decls[name] = "Real"
                continue
            return False
        decls[name] = sort
    return True
def _smt_unary_op(node: ast.UnaryOp) -> tuple[str, dict[str, str]] | None:
    if isinstance(node.op, ast.Not):
        return _smt_not(node.operand)
    return _smt_signed_literal(node)
def _smt_not(operand: ast.AST) -> tuple[str, dict[str, str]] | None:
    truth = _condition_truth(operand)
    if truth is not None:
        return ("false" if truth == "true" else "true"), {}
    term = _smt_term(operand)
    if term is None:
        return None
    return f"(not {term[0]})", term[1]
def _smt_signed_literal(node: ast.UnaryOp) -> tuple[str, dict[str, str]] | None:
    if not isinstance(node.op, (ast.USub, ast.UAdd)):
        return None
    operand = node.operand
    if not isinstance(operand, ast.Constant):
        return None
    value = operand.value
    if isinstance(value, bool):
        return None
    if isinstance(value, int):
        return str(-value if isinstance(node.op, ast.USub) else value), {}
    if isinstance(value, float):
        literal = _real_literal(value)
        if literal is None:
            return None
        return (f"(- {literal})" if isinstance(node.op, ast.USub) else literal), {}
    return None
def _chain_var_types(syms: list[str],
                     terms: list[tuple[str, dict[str, str]]],
                     ) -> dict[str, str] | None:
    needs = {_comparison_type_need(sym, lhs[0], rhs[0])
             for sym, lhs, rhs in zip(syms, terms, terms[1:], strict=False)}
    needs.discard(None)
    if "Bool" in needs and len(needs) > 1:
        return None
    chain_type = ("Real" if "Real" in needs
                  else next(iter(needs), None))
    out: dict[str, str] = {}
    for _term, term_decls in terms:
        if not _merge_decls(out, term_decls):
            return None
    if chain_type is None:
        return out
    for name, sort in tuple(out.items()):
        if sort == "Bool" and chain_type != "Bool":
            out[name] = chain_type
        elif {sort, chain_type} == {"Int", "Real"}:
            out[name] = "Real"
    return out
def _is_real_term(term: str) -> bool:
    return term.startswith(("(/ ", "(- (/ "))
def _comparison_type_need(sym: str, lhs: str, rhs: str) -> str | None:
    real = _is_real_term(lhs) or _is_real_term(rhs)
    if sym in _ORDER_CMP_SYMS:
        return "Real" if real else "Int"
    if lhs in ("true", "false") or rhs in ("true", "false"):
        return "Bool"
    if real:
        return "Real"
    if lhs.lstrip("-").isdigit() or rhs.lstrip("-").isdigit():
        return "Int"
    return None
def _wrap_smt_assert(term: str, decls: dict[str, str]) -> str:
    decls_s = "".join(
        f"(declare-const {_smt_symbol(n)} {t})" for n, t in decls.items())
    return f"{decls_s}(assert {term})"
def expr_to_constraint(expr: ast.AST, expected: bool) -> str | None:
    truth = _condition_truth(expr)
    if truth is not None:
        if not expected:
            truth = "false" if truth == "true" else "true"
        return f"(assert {truth})"
    if isinstance(expr, ast.Compare):
        return _compare_constraint(expr, expected)
    term = _smt_term(expr)
    if term is None:
        return None
    term_text, decls = term
    if not expected:
        term_text = f"(not {term_text})"
    return _wrap_smt_assert(term_text, decls)
def _constraints_with_guards(
        constraints: list[str], guards: _ExpressionGuards) -> list[str]:
    out = list(constraints)
    for expr, expected in guards:
        constraint = expr_to_constraint(expr, expected)
        if constraint:
            out.append(constraint)
    return out
def _compare_segment(
        op: ast.cmpop, comparator: ast.AST,
) -> tuple[str, tuple[str, dict[str, str]]] | None:
    sym = _SMT_CMP_OPS.get(type(op))
    term = _smt_term(comparator)
    if sym is None or term is None:
        return None
    return sym, term
def _collect_compare_terms(
        expr: ast.Compare,
) -> tuple[list[str], list[tuple[str, dict[str, str]]]] | None:
    if not expr.ops or not expr.comparators:
        return None
    left_term = _smt_term(expr.left)
    if left_term is None:
        return None
    terms: list[tuple[str, dict[str, str]]] = [left_term]
    syms: list[str] = []
    for op, comparator in zip(expr.ops, expr.comparators, strict=False):
        segment = _compare_segment(op, comparator)
        if segment is None:
            return None
        sym, right_term = segment
        syms.append(sym)
        terms.append(right_term)
    return syms, terms
def _compare_term(
        expr: ast.Compare,
) -> tuple[str, dict[str, str]] | None:
    collected = _collect_compare_terms(expr)
    if collected is None:
        return None
    syms, terms = collected
    decls = _chain_var_types(syms, terms)
    if decls is None:
        return None
    parts = [f"({sym} {lhs[0]} {rhs[0]})"
             for sym, lhs, rhs in zip(syms, terms, terms[1:], strict=False)]
    term = parts[0] if len(parts) == 1 else f"(and {' '.join(parts)})"
    return term, decls
def _compare_constraint(expr: ast.Compare, expected: bool) -> str | None:
    term = _compare_term(expr)
    if term is None:
        return None
    term_text, decls = term
    if not expected:
        term_text = f"(not {term_text})"
    return _wrap_smt_assert(term_text, decls)
_SMT_SYMBOL_TOKEN_RE = re.compile(r"\|[^|]*\||[A-Za-z_][A-Za-z0-9_]*")
_SMT_DECLARATION_RE = re.compile(
    r"\(declare-const\s+(\|[^|]+\||[A-Za-z_][A-Za-z0-9_]*)"
    r"\s+(Bool|Int|Real)\)")
_SMT_TERM_KEYWORDS = frozenset({
    "true", "false", "and", "or", "not", "distinct", "let", "forall",
    "exists", "ite", "xor", "as", "par", "check-sat", "assert",
})
def _smt_term_has_free_symbol(term: str) -> bool:
    for token in _SMT_SYMBOL_TOKEN_RE.findall(term):
        if token.startswith("|") or token not in _SMT_TERM_KEYWORDS:
            return True
    return False
def negate_constraint(constraint: str) -> str | None:
    i = constraint.find("(assert ")
    if i < 0 or not constraint.endswith(")"):
        return None
    decls = constraint[:i]
    term = constraint[i + len("(assert "):-1]
    if not term:
        return None
    if not decls and _smt_term_has_free_symbol(term):
        return None
    return f"{decls}(assert (not {term}))"
def _rest_blocks(block: list[ast.AST], stmt_idx: int,
                 blocks: tuple[list[ast.AST], ...],
                 block_idx: int) -> tuple[list[ast.AST], ...]:
    return (block[stmt_idx:],) + blocks[block_idx + 1:]
def _shift_loop_exits(
        loop_exits: tuple[tuple[int, int], ...], block_idx: int,
        prefix_len: int) -> tuple[tuple[int, int], ...]:
    return tuple(
        (prefix_len + (break_idx - block_idx),
         prefix_len + (continue_idx - block_idx))
        for break_idx, continue_idx in loop_exits
        if break_idx > block_idx and continue_idx > block_idx)
# 无参调用即为空容器的内建构造器
_EMPTY_ITERABLE_CALLS: frozenset[str] = frozenset({
    'list', 'tuple', 'set', 'frozenset', 'dict', 'str', 'bytes',
})
def _static_int(expr: ast.AST) -> int | None:
    """带符号的整数字面量；bool 是 int 子类但语义上不是整数，不认。"""
    if (isinstance(expr, ast.UnaryOp)
            and isinstance(expr.op, (ast.USub, ast.UAdd))):
        value = _static_int(expr.operand)
        if value is None:
            return None
        return -value if isinstance(expr.op, ast.USub) else value
    if (isinstance(expr, ast.Constant) and isinstance(expr.value, int)
            and not isinstance(expr.value, bool)):
        return expr.value
    return None
def _is_static_empty_iterable(node: ast.AST) -> bool:
    """可迭代对象能否**静态证明为空**；证明不了一律 False（保留循环体路径）。

    ``for i in range(0):`` 的循环体在任何输入下都不可达。符号执行若仍把
    循环体当作可行路径，会凭空产出“可达 sink + 触发输入”的证据，最终变成
    SE-40 误报。只做句法判定（字面量、``range(整数字面量…)``、无参空容器
    构造器）；名字绑定、形参、属性调用等一律视为未知。
    """
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    if isinstance(node, ast.Constant):
        return isinstance(node.value, (str, bytes)) and not node.value
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and not node.keywords):
        return False
    name = node.func.id
    if name in _EMPTY_ITERABLE_CALLS:
        return not node.args
    if name != 'range' or not 1 <= len(node.args) <= 3:
        return False
    bounds = [_static_int(arg) for arg in node.args]
    if None in bounds:
        return False
    start, stop, step = ((0, bounds[0], 1) if len(bounds) == 1
                         else (bounds[0], bounds[1], 1) if len(bounds) == 2
                         else (bounds[0], bounds[1], bounds[2]))
    if step == 0:
        return False    # range(step=0) 运行时抛 ValueError，不判定
    return (stop - start) * step <= 0
_SYMBOLIC_P0_SINKS = frozenset(
    s.name for s in BUILTIN_SINKS if s.severity == "P0")
_SEXPR_SCALARS = {'true': True, 'false': False}
def _model_decl_name(decl) -> str:
    text = str(decl)
    if text.startswith("|py:") and text.endswith("|"):
        return text[4:-1]
    if text.startswith("py:"):
        return text[3:]
    if text.startswith("|") and text.endswith("|"):
        return text[1:-1]
    return text
def _unify_numeric_constraint_sorts(constraints: list[str]) -> list[str]:
    real_names = {
        _model_decl_name(token)
        for constraint in constraints
        for token, sort in _SMT_DECLARATION_RE.findall(constraint)
        if sort == "Real"
    }
    if not real_names:
        return constraints
    def promote_int(match: re.Match) -> str:
        token, sort = match.groups()
        if sort == "Int" and _model_decl_name(token) in real_names:
            return f"(declare-const {token} Real)"
        return match.group(0)
    return [_SMT_DECLARATION_RE.sub(promote_int, constraint)
            for constraint in constraints]
def _flush_streams_best_effort() -> None:
    for _s in (sys.stdout, sys.stderr):
        try:
            if _s is not None:
                _s.flush()
        except Exception as e:  # noqa: BLE001 - 尽力刷新：失败仅记录，不阻断恢复
            logger.debug("[SymbolicExecutor] 流刷新失败跳过: %s", e)
def _restore_saved_fd(saved: int, target: int) -> OSError | None:
    restore_error: OSError | None = None
    try:
        os.dup2(saved, target)
    except OSError as exc:  # jwsgj:silent-ok 恢复错误由调用方统一传播
        restore_error = exc
    close_error = _close_fd_quietly(saved)
    return restore_error or close_error
def _close_fd_quietly(fd: int) -> OSError | None:
    try:
        os.close(fd)
    except OSError as exc:  # jwsgj:silent-ok 关闭错误由上下文管理器统一传播
        return exc
    return None
def _restore_fds(saved_fds: tuple[tuple[int, int | None], ...]) -> OSError | None:
    errors = [_restore_saved_fd(saved, target)
              for target, saved in saved_fds if saved is not None]
    return next(filter(None, errors), None)
@contextmanager
def _managed_fd(fd: int) -> Any:
    close_error: OSError | None = None
    try:
        yield fd
    finally:
        close_error = _close_fd_quietly(fd)
        if close_error is not None and sys.exc_info()[0] is not None:
            logger.warning(
                "[SymbolicExecutor] 描述符关闭失败（在飞异常优先透传）: %s",
                close_error, exc_info=close_error)
    if close_error is not None:
        raise close_error
@contextmanager
def _silence_native_output() -> Any:
    with _managed_fd(os.open(os.devnull, os.O_WRONLY)) as _devnull:
        _saved1: int | None = None
        _saved2: int | None = None
        _restore_error: OSError | None = None
        try:
            _saved1 = os.dup(1)
            _saved2 = os.dup(2)
            _flush_streams_best_effort()
            os.dup2(_devnull, 1)
            os.dup2(_devnull, 2)
            try:
                yield
            finally:
                _flush_streams_best_effort()
        finally:
            _restore_error = _restore_fds(((2, _saved2), (1, _saved1)))
            if _restore_error is not None and sys.exc_info()[0] is not None:
                logger.warning(
                    "[SymbolicExecutor] 静默窗口恢复失败（在飞异常优先透传，"
                    "本次恢复错误降级留痕不覆盖）: %s", _restore_error,
                    exc_info=_restore_error)
        if _restore_error is not None:
            raise _restore_error
class SymbolicExecutor:
    def __init__(self) -> None:
        self.paths: list[ExecutionPath] = []
        self._path_id = 0
        self._lock = threading.Lock()
        self._sink_name_resolver = None
        self._z3 = z3
        self._z3_available = z3 is not None
        if not self._z3_available:
            logger.warning("[SymbolicExecutor] Z3 不可用,使用启发式约束求解")
    def execute(self, func_node: ast.FunctionDef | ast.AsyncFunctionDef,
                import_tree: ast.Module | None = None
                ) -> list[ExecutionPath]:
        with self._lock:
            self.paths = []
            self._path_id = 0
            self._sink_name_resolver = None
            if not isinstance(
                    func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                return []
            tree = (import_tree if isinstance(import_tree, ast.Module)
                    else ast.Module(body=[func_node], type_ignores=[]))
            self._sink_name_resolver = _make_sink_name_resolver(
                tree, _SYMBOLIC_P0_SINKS, func_node)
            if any(isinstance(node, _TRY_STMT_TYPES)
                   for node in same_scope_bfs_nodes(func_node)):
                self._execute_try_paths(func_node)
            else:
                self._explore_paths(func_node.body, [])
            return list(self.paths)
    def _execute_try_paths(self, func_node: ast.FunctionDef | ast.AsyncFunctionDef
                           ) -> None:
        sinks = _SinkCollector(
            _SYMBOLIC_P0_SINKS, self._sink_name_resolver).collect(func_node.body)
        for path in _PathEnumerator().enumerate(func_node.body):
            for sink_name, sink_line, local_constraints in _path_reached_sinks(
                    sinks, path):
                self._record_path(
                    path["constraints"] + local_constraints, reaches_sink=True,
                    sink_name=sink_name, sink_line=sink_line)
            self._record_path(path["constraints"])
    def _push_if_branches(self, stack: list, stmt: ast.If,
                          rest: tuple[list[ast.AST], ...],
                          frame_constraints: list[str],
                          loop_exits: tuple[tuple[int, int], ...],
                          block_idx: int) -> None:
        self._record_header_sinks(stmt, frame_constraints)
        _cst = expr_to_constraint(stmt.test, True)
        true_constraints = frame_constraints + ([_cst] if _cst else [])
        _neg = expr_to_constraint(stmt.test, False)
        false_constraints = frame_constraints + ([_neg] if _neg else [])
        _exits = _shift_loop_exits(loop_exits, block_idx, 1)
        stack.append(((stmt.orelse,) + rest, 0, 0, false_constraints, _exits))
        stack.append(((stmt.body,) + rest, 0, 0, true_constraints, _exits))
    def _push_container_frames(self, stack: list, stmt: ast.AST,
                                rest: tuple[list[ast.AST], ...],
                                frame_constraints: list[str],
                                loop_exits: tuple[tuple[int, int], ...],
                                block_idx: int) -> None:
        self._record_header_sinks(stmt, frame_constraints)
        if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            body_constraints = frame_constraints
            zero_constraints = frame_constraints
            if isinstance(stmt, ast.While):
                _cst = expr_to_constraint(stmt.test, True)
                _neg = expr_to_constraint(stmt.test, False)
                if _cst:
                    body_constraints = frame_constraints + [_cst]
                if _neg:
                    zero_constraints = frame_constraints + [_neg]
            has_else = bool(stmt.orelse)
            normal_rest = (((stmt.orelse,) if has_else else ()) + rest)
            else_blocks = 1 if has_else else 0
            stack.append((
                normal_rest, 0, 0, zero_constraints,
                _shift_loop_exits(loop_exits, block_idx, else_blocks)))
            if (isinstance(stmt, (ast.For, ast.AsyncFor))
                    and _is_static_empty_iterable(stmt.iter)):
                # 可迭代对象静态为空：循环体在任何输入下都不可达，
                # 只保留零次迭代路径（orelse + 后继语句）。
                return
            rest_idx = 1 + else_blocks
            inherited = _shift_loop_exits(loop_exits, block_idx, rest_idx)
            stack.append((
                (stmt.body,) + normal_rest, 0, 0, body_constraints,
                inherited + ((rest_idx, 1),)))
            return
        if isinstance(stmt, _ZERO_ENTRY_CONTAINERS):
            stack.append((rest, 0, 0, frame_constraints,
                          _shift_loop_exits(loop_exits, block_idx, 0)))
        subs = [sub for sub in container_sub_bodies(stmt) if sub]
        inherited = _shift_loop_exits(loop_exits, block_idx, 1)
        for _idx in range(len(subs) - 1, -1, -1):
            if isinstance(stmt, ast.Match):
                guard = stmt.cases[_idx].guard
                if guard is not None:
                    self._record_sinks(guard, frame_constraints)
            stack.append(((subs[_idx],) + rest, 0, 0,
                          frame_constraints, inherited))
    def _record_sinks(self, node: ast.AST,
                      constraints: list[str]) -> bool:
        sink_hit = False
        for call, expression_guards in _iter_executable_calls_with_guards(node):
            call_name = (self._sink_name_resolver(call)
                         if self._sink_name_resolver is not None
                         else resolve_call_name(call))
            if call_name in _SYMBOLIC_P0_SINKS:
                self._record_path(
                    _constraints_with_guards(constraints, expression_guards),
                    reaches_sink=True,
                    sink_name=call_name, sink_line=call.lineno)
                sink_hit = True
        return sink_hit
    def _explore_paths(self, body: list[ast.AST],
                       constraints: list[str]) -> None:
        stack: list[tuple[tuple[list[ast.AST], ...], int, int,
                          list[str], tuple[tuple[int, int], ...]]] = [
            ((body,), 0, 0, constraints, ())]
        while stack:
            if len(self.paths) >= MAX_PATHS:
                logger.warning(
                    "[SymbolicExecutor] 路径数达到上限 %d，剩余分支不再展开",
                    MAX_PATHS)
                return
            blocks, block_idx, stmt_idx, frame_constraints, loop_exits = (
                stack.pop())
            finished = True
            while block_idx < len(blocks):
                block = blocks[block_idx]
                while stmt_idx < len(block):
                    stmt = block[stmt_idx]
                    stmt_idx += 1
                    if isinstance(stmt, ast.If):
                        rest = _rest_blocks(block, stmt_idx, blocks, block_idx)
                        self._push_if_branches(
                            stack, stmt, rest, frame_constraints,
                            loop_exits, block_idx)
                        finished = False
                        break
                    if isinstance(stmt, CONTAINER_STMTS):
                        rest = _rest_blocks(block, stmt_idx, blocks, block_idx)
                        self._push_container_frames(
                            stack, stmt, rest, frame_constraints,
                            loop_exits, block_idx)
                        finished = False
                        break
                    sink_hit = self._record_sinks(
                        stmt, frame_constraints)
                    if isinstance(stmt, (ast.Return, ast.Raise)):
                        if not sink_hit:
                            self._record_path(frame_constraints)
                        finished = False
                        break
                    if isinstance(stmt, (ast.Break, ast.Continue)):
                        if loop_exits:
                            exit_slot = 0 if isinstance(stmt, ast.Break) else 1
                            target = loop_exits[-1][exit_slot]
                            stack.append((blocks, target, 0,
                                          frame_constraints,
                                          loop_exits[:-1]))
                        finished = False
                        break
                if not finished:
                    break
                block_idx += 1
                stmt_idx = 0
                loop_exits = tuple(
                    targets for targets in loop_exits
                    if block_idx < targets[1])
            if finished:
                self._record_path(frame_constraints)
    def _record_header_sinks(self, stmt: ast.stmt,
                             constraints: list[str]) -> None:
        exprs = ([stmt.subject] if isinstance(stmt, ast.Match)
                 else container_header_exprs(stmt))
        for expr in exprs:
            self._record_sinks(expr, constraints)
    def _record_path(self, constraints: list[str],
                     reaches_sink: bool = False,
                     sink_name: str = "",
                     sink_line: int = 0) -> None:
        if len(self.paths) >= MAX_PATHS:
            return
        self._path_id += 1
        solution = (self.solve_constraints(constraints)
                    if constraints else None)
        self.paths.append(ExecutionPath(
            path_id=self._path_id,
            constraints=constraints,
            is_feasible=solution is None or len(solution) > 0,
            reaches_sink=reaches_sink,
            sink_name=sink_name,
            sink_line=sink_line,
            trigger_input=(solution
                           if reaches_sink and solution is not None else {}),
        ))
    def reset_state(self) -> int:
        with self._lock:
            released = int(bool(self.paths)) + int(bool(self._path_id))
            self.paths = []
            self._path_id = 0
            self._sink_name_resolver = None
        return released
    def solve_constraints(self, constraints: list[str]) -> dict[str, Any] | None:
        if not self._z3_available or self._z3 is None:
            return None
        with Z3_LOCK:
            return self._solve_constraints_locked(constraints)
    def _solve_constraints_locked(self, constraints: list[str]
                                  ) -> dict[str, Any] | None:
        try:
            with _silence_native_output():
                solver = self._z3.Solver()
                solver.set("timeout", 5000)
                if not self._load_constraints(solver, constraints):
                    return None
                result = solver.check()
                if result == self._z3.sat:
                    return self._model_to_trigger(solver.model())
                if result == self._z3.unsat:
                    return {}
                return None
        except Exception as _z3e:  # noqa: BLE001 - 求解器异常降级启发式，不阻断检测链路
            logger.debug(
                "[SymbolicExecutor] Z3 求解异常，降级启发式可行判定: %s",
                _z3e)
            return None
    def _load_constraints(self, solver, constraints: list[str]) -> bool:
        parse_failures = 0
        for constraint in _unify_numeric_constraint_sorts(constraints):
            try:
                solver.add(self._z3.parse_smt2_string(constraint))
            except Exception as _z3e:  # noqa: BLE001 - 降级容错，不阻断诊断链路
                parse_failures += 1
                logger.debug("Failed to parse constraint: %s (%s)",
                           constraint, _z3e)
        return parse_failures == 0
    def _model_to_trigger(self, model) -> dict[str, Any] | None:
        decls = model.decls()
        if not decls:
            return None
        pairs = [(_model_decl_name(decl), decl) for decl in decls]
        names = [name for name, _decl in pairs]
        if len(names) != len(set(names)):
            logger.debug("[SymbolicExecutor] 模型含同名异类型影子"
                       "常量，跨约束合取语义断裂，降级启发式: %s", names)
            return None
        return {name: self._model_value_to_python(model[decl])
                for name, decl in pairs}
    @staticmethod
    def _model_value_to_python(value: Any) -> Any:
        failures: list[str] = []
        if value is None:
            return None
        for attr in ("as_long", "as_fraction", "as_string"):
            fn = getattr(value, attr, None)
            if not callable(fn):
                continue
            try:
                out = fn()
            except Exception as e:  # noqa: BLE001 - 单一访问器不适用属预期
                failures.append(f"{attr}: {e}")
                continue
            if attr != "as_fraction":
                return out
            try:
                return float(out)
            except (TypeError, ValueError, OverflowError):
                failures.append(f"as_fraction: {out!r} 不可归一为 float")
        if failures:
            logger.warning("[SymbolicExecutor] 模型值全部转换失败: %s", failures)
        try:
            sexpr = value.sexpr()
        except Exception as _e:  # noqa: BLE001 - 兜底降级不阻断  # jwsgj:silent-ok 模型值回退字符串
            logger.debug("[SymbolicExecutor] 模型值 sexpr 失败，回退字符串: %s", _e)
            return str(value)
        return _SEXPR_SCALARS.get(sexpr, sexpr) if sexpr else str(value)
DEFAULT_SINK_NAMES: frozenset[str] = SINK_NAMES
_BOUNDARY_VALUES: tuple[Any, ...] = (0, 1, -1, 100, "", "test", "A" * 50,
                                     True, False, None)
@dataclass
class ConcolicInput:
    values: dict[str, Any] = field(default_factory=dict)
    path_constraints: list[str] = field(default_factory=list)
    covered_blocks: set[int] = field(default_factory=set)
    reached_sink: bool = False
    sink_name: str = ""
    fitness: float = 0.0
    seed_source: str = "boundary"
    def to_dict(self) -> dict[str, Any]:
        return {
            "values": self.values,
            "path_constraints": list(self.path_constraints),
            "covered_blocks": sorted(self.covered_blocks),
            "reached_sink": self.reached_sink,
            "sink_name": self.sink_name,
            "fitness": self.fitness,
            "seed_source": self.seed_source,
        }
@dataclass(frozen=True)
class _WalkTail:
    on_terminal: tuple[list[ast.stmt], ...] = ()
    on_normal: list[ast.stmt] | None = None
    always_next: tuple[list[ast.stmt], ...] = ()
    normal_tail: _WalkTail | None = None
_EMPTY_TAIL = _WalkTail()
@dataclass(frozen=True)
class _LoopContinuation:
    control_ids: frozenset[int]
    rest: list[ast.stmt]
    tail: _WalkTail
    continue_rest: list[ast.stmt] | None = None
@dataclass
class _PathState:
    constraints: list[str]
    choices: dict[int, bool]
    covered: set[int]
    covered_ids: set[int]
    branches: list[BranchPoint]
    unmodeled_identity: bool = False
    loop_control: ast.Break | ast.Continue | None = None
    loop_exits: list[_LoopContinuation] = field(default_factory=list)
    def fork(self) -> _PathState:
        return _PathState(
            constraints=list(self.constraints),
            choices=dict(self.choices),
            covered=set(self.covered),
            covered_ids=set(self.covered_ids),
            branches=list(self.branches),
            unmodeled_identity=self.unmodeled_identity,
            loop_control=self.loop_control,
            loop_exits=list(self.loop_exits),
        )
    def cover(self, stmt: ast.stmt) -> None:
        self.covered.add(stmt.lineno)
        self.covered_ids.add(id(stmt))
@dataclass
class BranchPoint:
    line_number: int = 0
    constraint: str = ""
    negated_constraint: str = ""
    taken_branch: bool = False
    block_id: int = 0
    def to_dict(self) -> dict[str, Any]:
        return {
            "line_number": self.line_number,
            "constraint": self.constraint,
            "negated_constraint": self.negated_constraint,
            "taken_branch": self.taken_branch,
            "block_id": self.block_id,
        }
_DEFAULT_SEED_COUNT = 10
_DEFAULT_ALLOW_NEGATION = True
def _seed_count(raw, default: int = _DEFAULT_SEED_COUNT) -> int:
    if isinstance(raw, bool):
        return default
    if isinstance(raw, int):
        return max(0, raw)
    try:
        return max(0, int(raw))
    except (TypeError, ValueError, OverflowError):
        return default
def _constraint_list(raw) -> list[str]:
    if raw is None:
        return []
    if isinstance(raw, str):
        return [raw]
    if not isinstance(raw, (list, tuple)):
        return []
    return [item for item in raw if isinstance(item, str)]
class SeedGenerator:
    def __init__(self, solver: Callable[[list[str]], dict[str, Any] | None] | None = None) -> None:
        self._solver = solver
    @classmethod
    def from_symbolic_executor(cls, executor: Any) -> SeedGenerator:
        return cls(solver=_bind_solver(executor))
    def generate(self, func_node: Any, num_seeds: int = _DEFAULT_SEED_COUNT,
                 base_constraints: list[str] | None = None,
                 param_names: list[str] | None = None, *,
                 allow_negation: bool = _DEFAULT_ALLOW_NEGATION) -> list[dict[str, Any]]:
        return [seed for seed, _src in self.generate_with_source(
            func_node, num_seeds=num_seeds, base_constraints=base_constraints,
            param_names=param_names, allow_negation=allow_negation)]
    def generate_with_source(self, func_node: Any, num_seeds: int = _DEFAULT_SEED_COUNT,
                             base_constraints: list[str] | None = None,
                             param_names: list[str] | None = None, *,
                             allow_negation: bool = _DEFAULT_ALLOW_NEGATION
                             ) -> list[tuple[dict[str, Any], str]]:
        seeds: list[tuple[dict[str, Any], str]] = []
        seen_keys: set[tuple] = set()
        num_seeds = _seed_count(num_seeds)
        if num_seeds == 0:
            return []
        base_constraints = _constraint_list(base_constraints)
        if isinstance(param_names, str):
            names = [param_names]
        elif param_names is not None:
            names = [name for name in param_names
                     if isinstance(name, str)]
        else:
            names = self._extract_param_names(func_node)
        for seed, src in self._channel_candidates(
                base_constraints, names, num_seeds,
                allow_negation=allow_negation):
            self._push_seed(seeds, seen_keys, seed, src, num_seeds)
            if len(seeds) >= num_seeds:
                break
        return seeds
    def _channel_candidates(
            self, base_constraints: list[str], names: list[str],
            num_seeds: int, *, allow_negation: bool
            ) -> Iterator[tuple[dict[str, Any], str]]:
        yield from self._solve(base_constraints, "z3")
        if base_constraints and allow_negation:
            negated = negate_constraint(base_constraints[-1])
            if negated is not None:
                yield from self._solve(
                    list(base_constraints[:-1]) + [negated], "z3_negation")
        yield from self._boundary_seed_candidates(names, num_seeds)
    @staticmethod
    def _push_seed(seeds: list[tuple[dict[str, Any], str]],
                   seen_keys: set[tuple], seed: dict[str, Any] | None,
                   src: str, limit: int) -> None:
        if seed is None or len(seeds) >= limit:
            return
        key = tuple(sorted((k, repr(v)) for k, v in seed.items()))
        if key in seen_keys:
            return
        seen_keys.add(key)
        seeds.append((dict(seed), src))
    def _solve(self, constraints: list[str], source: str) -> list[tuple[dict[str, Any], str]]:
        if self._solver is None or not constraints:
            return []
        try:
            solution = self._solver(list(constraints))
            if not solution:
                return []
            return [(dict(solution), source)]
        except Exception as e:  # noqa: BLE001
            logger.debug("[SeedGenerator] %s 求解失败，降级: %s", source, e)
            return []
    def _boundary_seed_candidates(self, names: list[str], num_seeds: int) -> list[tuple[dict[str, Any], str]]:
        if not names:
            return [({}, "boundary")] if num_seeds > 0 else []
        candidates: list[tuple[dict[str, Any], str]] = []
        for i in range(min(num_seeds, len(_BOUNDARY_VALUES))):
            seed = {pname: self._boundary_value(i) for pname in names}
            if seed:
                candidates.append((seed, "boundary"))
        return candidates
    @staticmethod
    def _extract_param_names(func_node: Any) -> list[str]:
        if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return []
        return [arg.arg for arg in iter_arg_nodes(func_node.args)]
    @staticmethod
    def _boundary_value(index: int) -> Any:
        return _BOUNDARY_VALUES[index % len(_BOUNDARY_VALUES)]
def _sink_alias_tables(tree, func_node):
    local_modules: dict[str, set[str]] = {}
    from_members: dict[str, tuple[str, str]] = {}
    shadowed_names: set[str] = set()
    if tree is None:
        return local_modules, from_members, shadowed_names
    lexical = collect_lexical_scope_table(tree)
    imports = scope_import_tables(tree)
    visible_scopes = []
    scope = func_node
    while scope is not None:
        if not isinstance(scope, ast.ClassDef):
            visible_scopes.append(scope)
        scope = lexical.parent.get(scope)
    resolved_names: set[str] = set()
    for scope in visible_scopes:
        scope_imports = imports.get(scope, {})
        candidates = (set(lexical.bound.get(scope, ()))
                      | set(scope_imports))
        for name in candidates - resolved_names:
            if name in lexical.shadow_bound.get(scope, ()):
                shadowed_names.add(name)
                continue
            binding = scope_imports.get(name)
            if binding is None:
                shadowed_names.add(name)
                continue
            if binding[0] == 'import':
                local_modules.setdefault(name, set()).add(binding[1])
            elif binding[1]:
                from_members[name] = (binding[1], binding[2])
        resolved_names.update(candidates)
    return local_modules, from_members, shadowed_names
def _make_sink_name_resolver(tree, sink_names, func_node):
    local_modules, from_members, shadowed_names = _sink_alias_tables(
        tree, func_node)
    if not local_modules and not from_members and not shadowed_names:
        return None
    def resolve(call: ast.Call) -> str:
        func = getattr(call, 'func', None)
        attributes: list[str] = []
        base_node = func
        while isinstance(base_node, ast.Attribute):
            attributes.append(base_node.attr)
            base_node = base_node.value
        attributes.reverse()
        if not isinstance(base_node, ast.Name):
            return resolve_call_name(call)
        base = base_node.id
        if base in shadowed_names:
            return ""
        if attributes:
            suffix = ".".join(attributes)
            modules = local_modules.get(base, ())
            if modules:
                for module in sorted(modules):
                    candidate = f"{module}.{suffix}"
                    if candidate in sink_names:
                        return candidate
                if "builtins" in modules and suffix in sink_names:
                    return suffix
                return ""
            target = from_members.get(base)
            if target is not None:
                candidate = f"{target[0]}.{target[1]}.{suffix}"
                return candidate if candidate in sink_names else ""
        else:
            target = from_members.get(base)
            if target is not None:
                candidate = f"{target[0]}.{target[1]}"
                if candidate in sink_names:
                    return candidate
                if target[0] == "builtins" and target[1] in sink_names:
                    return target[1]
                return ""
            if base in local_modules:
                return ""
        return resolve_call_name(call)
    return resolve
_SinkSite = tuple[
    str, int, dict[int, bool], int, _ExpressionGuards]
class _SinkCollector:
    def __init__(self, sink_names: frozenset[str], resolver=None) -> None:
        self._sink_names = sink_names
        self._resolver = resolver
        self.sites: list[_SinkSite] = []
    def collect(self, body: list[ast.stmt]) -> list[_SinkSite]:
        self._visit(body, {})
        return list(self.sites)
    def _visit(self, body: list[ast.stmt], guards: dict[int, bool]) -> None:
        for stmt in body:
            self._visit_stmt(stmt, guards)
    def _visit_stmt(self, stmt: ast.stmt, guards: dict[int, bool]) -> None:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            self._record(stmt, guards, stmt)
            return
        if isinstance(stmt, ast.If):
            self._record(stmt.test, guards, stmt)
            self._visit(stmt.body, {**guards, stmt.lineno: True})
            self._visit(stmt.orelse, {**guards, stmt.lineno: False})
            return
        if isinstance(stmt, CONTAINER_STMTS):
            self._dispatch_container(stmt, guards)
            return
        self._record(stmt, guards, stmt)
    def _dispatch_container(self, stmt: ast.stmt, guards: dict[int, bool]) -> None:
        if isinstance(stmt, ast.Match):
            self._record(stmt.subject, guards, stmt)
            for case in stmt.cases:
                if case.guard is not None:
                    self._record(case.guard, guards, case)
                self._visit(case.body, guards)
            return
        if isinstance(stmt, _TRY_STMT_TYPES):
            for handler in stmt.handlers:
                if handler.type is not None and handler.body:
                    self._record(handler.type, guards, handler.body[0])
        for expr in container_header_exprs(stmt):
            self._record(expr, guards, stmt)
        for sub in container_sub_bodies(stmt):
            if sub:
                self._visit(sub, guards)
    def _record(self, node: ast.AST, guards: dict[int, bool], owner: ast.AST) -> None:
        for call, expression_guards in _iter_executable_calls_with_guards(node):
            name = (self._resolver(call) if self._resolver is not None
                    else resolve_call_name(call))
            if name in self._sink_names:
                self.sites.append(
                    (name, call.lineno, dict(guards), id(owner), expression_guards))
_TRY_STMT_TYPES = (ast.Try,) + ((ast.TryStar,)
                                  if hasattr(ast, "TryStar") else ())
_TERMINAL_STMTS: tuple[type, ...] = (
    ast.Return, ast.Raise, ast.Break, ast.Continue)
_ZERO_ENTRY_CONTAINERS: tuple[type, ...] = (
    (ast.For, ast.AsyncFor, ast.While)
    + ((ast.Match,) if hasattr(ast, "Match") else ()))
def _split_terminal(stmts: list[ast.stmt]) -> tuple[list[ast.stmt], bool]:
    for index, stmt in enumerate(stmts):
        if isinstance(stmt, _TERMINAL_STMTS):
            return stmts[:index + 1], True
    return stmts, False
def _has_unmodeled_identity(expr: ast.AST) -> bool:
    for node in walk_nodes(expr):
        if not isinstance(node, ast.Compare) or not any(
                isinstance(op, (ast.Is, ast.IsNot)) for op in node.ops):
            continue
        operands = (node.left, *node.comparators)
        if any(not isinstance(operand, ast.Constant) for operand in operands):
            return True
    return False
class _PathEnumerator:
    def __init__(self) -> None:
        self.paths: list[dict[str, Any]] = []
    def enumerate(self, body: list[ast.stmt]) -> list[dict[str, Any]]:
        self._walk(body, _PathState([], {}, set(), set(), []))
        if len(self.paths) >= MAX_PATHS:
            logger.warning(
                "[PathEnumerator] 路径数达到上限 %d，剩余分支不再展开", MAX_PATHS)
        return list(self.paths)
    @property
    def _at_cap(self) -> bool:
        return len(self.paths) >= MAX_PATHS
    def _walk(self, body: list[ast.stmt], state: _PathState,
              tail: _WalkTail = _EMPTY_TAIL) -> None:
        if self._at_cap:
            return
        body, terminated = _split_terminal(body)
        if terminated:
            terminal = body[-1]
            state.loop_control = (
                terminal if isinstance(terminal, (ast.Break, ast.Continue))
                else None)
        for i, stmt in enumerate(body):
            state.cover(stmt)
            if isinstance(stmt, ast.If):
                self._expand_if(stmt, body[i + 1:], state, tail)
                return
            if isinstance(stmt, CONTAINER_STMTS):
                self._expand_container(stmt, body[i + 1:], state, tail)
                if (not isinstance(stmt, _ZERO_ENTRY_CONTAINERS)
                        or isinstance(stmt, (ast.For, ast.AsyncFor, ast.While))):
                    return
        if self._at_cap:
            return
        if terminated:
            self._run_chain(tail.on_terminal, tail.always_next, state)
        elif tail.on_normal is not None:
            normal_tail = tail.normal_tail or _WalkTail(
                on_terminal=tail.on_terminal,
                always_next=tail.always_next)
            self._walk(tail.on_normal, state, normal_tail)
        elif tail.always_next:
            self._run_chain((), tail.always_next, state)
        else:
            self._append_path(state)
    def _run_chain(self, chain: tuple[list[ast.stmt], ...],
                   trailing: tuple[list[ast.stmt], ...],
                   state: _PathState) -> None:
        if not chain:
            if trailing:
                self._run_chain(trailing, (), state)
            else:
                self._append_path(state)
            return
        self._walk(chain[0], state, _WalkTail(
            always_next=tuple(chain[1:]) + tuple(trailing)))
    def _append_path(self, state: _PathState) -> None:
        control = state.loop_control
        if control is not None:
            for index in range(len(state.loop_exits) - 1, -1, -1):
                continuation = state.loop_exits[index]
                if id(control) not in continuation.control_ids:
                    continue
                state.loop_control = None
                del state.loop_exits[index:]
                rest = continuation.rest
                if (isinstance(control, ast.Continue)
                        and continuation.continue_rest is not None):
                    rest = continuation.continue_rest
                self._walk(rest, state, continuation.tail)
                return
        self.paths.append({
            "constraints": state.constraints,
            "choices": state.choices,
            "covered": state.covered,
            "covered_ids": state.covered_ids,
            "branch_points": state.branches,
            "unmodeled_identity": state.unmodeled_identity,
        })
    def _expand_if(self, stmt: ast.If, rest: list[ast.stmt],
                   state: _PathState, tail: _WalkTail) -> None:
        cst = expr_to_constraint(stmt.test, True) or ""
        neg = expr_to_constraint(stmt.test, False) or ""
        for body, path_constraint, taken in ((stmt.body, cst, True),
                                            (stmt.orelse, neg, False)):
            branch_state = state.fork()
            if _has_unmodeled_identity(stmt.test):
                branch_state.unmodeled_identity = True
            if path_constraint:
                branch_state.constraints.append(path_constraint)
            branch_state.choices[stmt.lineno] = taken
            branch_state.branches.append(BranchPoint(
                line_number=stmt.lineno,
                constraint=cst,
                negated_constraint=neg,
                taken_branch=taken,
                block_id=stmt.lineno,
            ))
            branch_body, branch_term = _split_terminal(body)
            self._walk(branch_body + ([] if branch_term else rest),
                       branch_state, tail)
    def _expand_container(self, stmt: ast.stmt, rest: list[ast.stmt],
                          state: _PathState, tail: _WalkTail) -> None:
        if isinstance(stmt, _TRY_STMT_TYPES):
            self._expand_try(stmt, rest, state, tail)
            return
        if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
            self._expand_loop(stmt, rest, state, tail)
            return
        if isinstance(stmt, ast.Match):
            for case in stmt.cases:
                case_state = state.fork()
                case_state.covered_ids.add(id(case))
                self._walk(list(case.body) + rest, case_state, tail)
            return
        for sub in container_sub_bodies(stmt):
            if sub:
                sub_body, sub_term = _split_terminal(sub)
                self._walk(sub_body + ([] if sub_term else rest),
                           state.fork(), tail)
    def _expand_loop(self, stmt: ast.For | ast.AsyncFor | ast.While,
                     rest: list[ast.stmt], state: _PathState,
                     tail: _WalkTail) -> None:
        normal_rest = list(stmt.orelse) + list(rest)
        body_state = state.fork()
        zero_state = state.fork()
        if isinstance(stmt, ast.While):
            cst = expr_to_constraint(stmt.test, True)
            neg = expr_to_constraint(stmt.test, False)
            for branch_state, path_constraint, taken in (
                    (body_state, cst, True), (zero_state, neg, False)):
                if path_constraint:
                    branch_state.constraints.append(path_constraint)
                branch_state.choices[stmt.lineno] = taken
                branch_state.branches.append(BranchPoint(
                    line_number=stmt.lineno,
                    constraint=cst,
                    negated_constraint=neg,
                    taken_branch=taken,
                    block_id=stmt.lineno,
                ))
        if (isinstance(stmt, (ast.For, ast.AsyncFor))
                and _is_static_empty_iterable(stmt.iter)):
            # 与 SymbolicExecutor._push_container_frames 同口径：可迭代对象
            # 静态为空时循环体不可达，只走零次迭代路径。
            self._walk(normal_rest, zero_state, tail)
            return
        continuation = _LoopContinuation(
            control_ids=frozenset(
                id(node) for body_stmt in stmt.body
                for node in walk_nodes(body_stmt)),
            rest=list(rest), tail=tail, continue_rest=normal_rest)
        body_state.loop_exits.append(continuation)
        self._walk(list(stmt.body) + normal_rest, body_state, tail)
        self._walk(normal_rest, zero_state, tail)
    def _expand_try(self, stmt: ast.stmt, rest: list[ast.stmt],
                    state: _PathState, tail: _WalkTail) -> None:
        finalbody = list(stmt.finalbody)
        normal_after = rest or tail.on_normal or None
        normal_after_tail = (_WalkTail(
            on_terminal=tail.on_terminal,
            on_normal=tail.on_normal,
            normal_tail=tail.normal_tail,
            always_next=tail.always_next,
        ) if rest else tail.normal_tail)
        after_final = _WalkTail(
            on_terminal=tail.on_terminal,
            on_normal=normal_after,
            normal_tail=normal_after_tail,
            always_next=tail.always_next)
        inner_terminal = (((finalbody,) if finalbody else ())
                          + tuple(tail.on_terminal))
        post_try_tail = _WalkTail(
            on_terminal=inner_terminal,
            on_normal=finalbody if finalbody else normal_after,
            normal_tail=after_final if finalbody else normal_after_tail,
            always_next=tail.always_next)
        body_tail = _WalkTail(
            on_terminal=inner_terminal,
            on_normal=stmt.orelse,
            normal_tail=post_try_tail,
            always_next=tail.always_next)
        self._walk(stmt.body, state.fork(), body_tail)
        for handler in stmt.handlers:
            if handler.body:
                self._walk(handler.body, state.fork(), post_try_tail)
def _path_reached_sinks(
        sinks: list[_SinkSite],
        path: dict[str, Any]) -> list[tuple[str, int, list[str]]]:
    return [
        (name, line, _constraints_with_guards([], expression_guards))
        for (name, line, guards, stmt_id, expression_guards) in sinks
        if stmt_id in path["covered_ids"]
        and all(path["choices"].get(ln) == want
                for ln, want in guards.items())
    ]
def _path_fitness(path: dict[str, Any], reached: bool) -> float:
    if reached:
        return 1.0
    covered = len(path["covered"])
    return round(0.5 * (covered / max(1, covered + len(path["branch_points"]))), 3)
class _GuidedConcolicExplorer:
    def __init__(self, max_iterations: int = 30,
                 solver: Callable[[list[str]], dict[str, Any] | None] | None = None
                 ) -> None:
        self._max_iterations = max_iterations
        self._solver = solver
        self._seeds = SeedGenerator(solver=solver)
    def execute(self, func_node: ast.FunctionDef,
                seed_inputs: list[dict[str, Any]] | None = None,
                sink_patterns: list[str] | None = None,
                import_tree: ast.AST | None = None,
                ) -> list[ConcolicInput]:
        if not isinstance(func_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return []
        if isinstance(sink_patterns, str):
            sink_patterns = [sink_patterns]
        if not isinstance(sink_patterns, (list, tuple, set, frozenset)):
            sink_patterns = None
        names = [p for p in (sink_patterns or [])
                 if isinstance(p, str) and p]
        sink_names = frozenset(names) if names else DEFAULT_SINK_NAMES
        resolver = (None if import_tree is None
                    else _make_sink_name_resolver(
                        import_tree, sink_names, func_node))
        sinks = _SinkCollector(sink_names, resolver).collect(func_node.body)
        user_seeds = [dict(s) for s in (seed_inputs or []) if isinstance(s, dict)]
        return self._execute_paths(func_node, sinks, user_seeds)
    def _execute_paths(self, func_node: ast.FunctionDef,
                       sinks: list[_SinkSite],
                       user_seeds: list[dict[str, Any]]) -> list[ConcolicInput]:
        results: list[ConcolicInput] = []
        paths = _PathEnumerator().enumerate(func_node.body)
        for seed_offset, seed_limit in ((0, 1), (1, None)):
            for path in paths:
                if len(results) >= self._max_iterations:
                    return results
                self._materialize_path_inputs(
                    results, path, sinks, user_seeds, func_node,
                    seed_offset=seed_offset, seed_limit=seed_limit)
        return results
    def _is_proven_infeasible(self, constraints: list[str]) -> bool:
        if self._solver is None or not constraints:
            return False
        try:
            return self._solver(list(constraints)) == {}
        except Exception as exc:  # noqa: BLE001 — 可行性证据缺失时保留静态路径
            logger.debug("[Concolic] 路径可行性求解失败，保留静态路径: %s", exc)
            return False
    def _seed_matches_path(self, seed: dict[str, Any], source: str,
                           constraints: list[str]) -> bool:
        if not constraints or self._solver is None:
            return True
        if source == "z3":
            return True
        declarations = [
            (token, sort)
            for constraint in constraints
            for token, sort in _SMT_DECLARATION_RE.findall(constraint)
        ]
        numeric_sorts: dict[str, str] = {}
        for token, sort in declarations:
            name = _model_decl_name(token)
            if name not in seed or sort == "Bool":
                continue
            if sort == "Real" or isinstance(seed[name], float):
                numeric_sorts[name] = "Real"
            else:
                numeric_sorts.setdefault(name, "Int")
        assignments: dict[str, str] = {}
        path_constraints: list[str] = []
        for constraint in constraints:
            transformed = constraint
            for token, sort in _SMT_DECLARATION_RE.findall(constraint):
                name = _model_decl_name(token)
                if name not in seed:
                    continue
                target_sort = ("Bool" if sort == "Bool"
                               else numeric_sorts[name])
                value = seed[name]
                if target_sort == "Bool":
                    try:
                        value = bool(value)
                    except (TypeError, ValueError):
                        return False
                elif isinstance(value, bool):
                    value = int(value)
                literal = _smt_constant(ast.Constant(value=value))
                if literal is None:
                    return False
                seeded_symbol = f"|jwsgj-seed:{name}:{target_sort}|"
                transformed = transformed.replace(
                    f"(declare-const {token} {sort})",
                    f"(declare-const {seeded_symbol} {target_sort})",
                )
                transformed = _SMT_SYMBOL_TOKEN_RE.sub(
                    lambda match, token=token, seeded=seeded_symbol: (
                        seeded if match.group(0) == token else match.group(0)),
                    transformed,
                )
                assignments[seeded_symbol] = (
                    f"(declare-const {seeded_symbol} {target_sort})"
                    f"(assert (= {seeded_symbol} {literal[0]}))"
                )
            path_constraints.append(transformed)
        if not assignments:
            return True
        path_constraints.extend(assignments.values())
        try:
            solution = self._solver(path_constraints)
        except Exception as exc:  # noqa: BLE001 — 候选验证失败时不伪造路径匹配证据
            logger.debug("[Concolic] 种子与路径合取求解失败，丢弃候选: %s", exc)
            return False
        return bool(solution)
    def _materialize_path_inputs(
            self, results: list[ConcolicInput], path: dict[str, Any],
            sinks: list[_SinkSite],
            user_seeds: list[dict[str, Any]],
            func_node: ast.FunctionDef, *, seed_offset: int = 0,
            seed_limit: int | None = None) -> None:
        path_sinks = _path_reached_sinks(sinks, path)
        if path_sinks and path["unmodeled_identity"]:
            logger.debug(
                "[Concolic] 对象身份比较缺少精确模型，不产出 sink 输入证据")
            return
        constraints = list(path["constraints"])
        if path_sinks:
            constraints.extend(path_sinks[0][2])
        if self._is_proven_infeasible(constraints):
            return
        fitness = _path_fitness(path, bool(path_sinks))
        seed_pairs = self._resolve_seed_pairs(user_seeds, func_node, constraints)
        seed_pairs = [
            (seed, src) for seed, src in seed_pairs
            if self._seed_matches_path(seed, src, constraints)
        ]
        seed_pairs = seed_pairs[seed_offset:]
        if seed_limit is not None:
            seed_pairs = seed_pairs[:seed_limit]
        for seed, src in seed_pairs:
            if len(results) >= self._max_iterations:
                break
            results.append(ConcolicInput(
                values=dict(seed),
                path_constraints=list(constraints),
                covered_blocks=set(path["covered"]),
                reached_sink=bool(path_sinks),
                sink_name=path_sinks[0][0] if path_sinks else "",
                fitness=fitness,
                seed_source=src,
            ))
    def _resolve_seed_pairs(self, user_seeds: list[dict[str, Any]],
                            func_node: ast.FunctionDef,
                            constraints: list[str]
                            ) -> list[tuple[dict[str, Any], str]]:
        if user_seeds:
            return [(s, "user") for s in user_seeds]
        return self._seeds.generate_with_source(
            func_node, base_constraints=constraints,
            allow_negation=False)
def _parse_source_tree(source_code: str) -> ast.Module | None:
    tree, err = parse_ast_safely(source_code)
    if err is None:
        return tree
    if isinstance(err, TypeError):
        logger.warning("[Concolic] 非字符串源码输入，跳过 Concolic 探索")
    else:
        logger.warning("[Concolic] 源码解析失败，跳过符号解析")
    return None
def _locate_function(tree: ast.AST, func_name: str | None) -> ast.AST | None:
    if isinstance(tree, ast.Module) and func_name is not None:
        top_level = [
            node for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            and node.name == func_name
        ]
        if top_level:
            return top_level[-1]
    for node in walk_nodes(tree):
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and (func_name is None or node.name == func_name)):
            return node
    return None
_CONCOLIC_BRANCH_NODES = (ast.If, *CONTAINER_STMTS)
def concolic_file_score(filepath: str, func_name: str | None = None) -> int:
    filepath = normalize_filepath(filepath)
    if not filepath:
        return 0
    try:
        source = read_source_cached(filepath)
    except (OSError, ValueError):  # jwsgj:silent-ok 文件不可读时探索度按 0 返回
        return 0
    tree, error = parse_ast_safely(source or "")
    if error is not None:
        return 0
    target = _locate_function(tree, func_name)
    if target is None:
        return 0
    return sum(1 for child in same_scope_bfs_nodes(target)
               if isinstance(child, _CONCOLIC_BRANCH_NODES))
def _bind_solver(symbolic_executor: Any) -> Callable[[list[str]], dict[str, Any] | None] | None:
    if symbolic_executor is None:
        return None
    bound = getattr(symbolic_executor, "solve_constraints", None)
    return bound if callable(bound) else None
def guided_concolic_explore(source_code: str,
                            func_name: str | None = None,
                            seed_inputs: list[dict[str, Any]] | None = None,
                            sink_patterns: list[str] | None = None,
                            symbolic_executor: Any = None
                            ) -> list[ConcolicInput]:
    tree = _parse_source_tree(source_code)
    target_func = None if tree is None else _locate_function(tree, func_name)
    if target_func is None:
        return []
    if symbolic_executor is None:
        symbolic_executor = SymbolicExecutor()
    solver = _bind_solver(symbolic_executor)
    explorer = _GuidedConcolicExplorer(solver=solver)
    try:
        return explorer.execute(target_func, seed_inputs, sink_patterns,
                                import_tree=tree)
    except RecursionError:
        logger.warning("[Concolic] 路径枚举递归溢出，跳过符号解析")
        return []

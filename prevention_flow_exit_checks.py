from __future__ import annotations

import ast
import builtins
import logging
import os
from collections import OrderedDict
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import dotted_name, iter_scope_statements
from jwsgj.diag_shared_source_core import parse_cached, read_source
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import (
    FUNC_SCOPE_NODES,
    TRY_NODES,
    assert_always_fails,
    assigned_names,
    binding_evaluation_position,
    bound_names,
    break_binding_loop,
    constant_truth,
    construct_shadows_name,
    is_constant_true_while,
    is_irrefutable_pattern,
    is_statically_unreachable,
    iter_binding_entries,
    loop_has_binding,
    make_issue,
    match_always_exits,
    nearest_scope,
    param_names,
    parent_map_of,
    preceding_statements,
    scan_body_no_funcs,
    scope_chain,
    scope_definition_names,
    scope_function_defs,
    scope_local_bindings,
    snippet_of,
    source_lines,
    statically_empty_iterable,
    subtree_contains,
    try_block_terminates,
    walk_ast_nodes,
)

__all__ = [
    'check_LV17',
    'check_LV18',
    'check_LV20',
    'check_LV21',
    'check_LV29',
    'check_LV32',
]
_log = logging.getLogger(__name__)
_log.info(
    "prevention_flow_exit_checks 函数出口与异常传播域"
    "（终止信号/异常重抛/handler 覆盖）已加载：%d 项导出", len(__all__))
_FINDING_DIMENSION = 'logic_correctness'
_LV17_CONTROL_FLOW_NODES = tuple(
    t for t in (
        ast.If, ast.For, ast.AsyncFor, ast.While, ast.Try, ast.IfExp,
        getattr(ast, 'Match', None), ast.BoolOp, ast.ExceptHandler,
        ast.Assert, getattr(ast, 'TryStar', None),
        ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
    ) if t is not None
)
_LV17_COMPREHENSION_NODES = (ast.ListComp, ast.SetComp,
                             ast.DictComp, ast.GeneratorExp)
_LV17_RECURSION_HANDLERS = frozenset({
    'RecursionError', 'RuntimeError', 'Exception', 'BaseException',
})
_LV29_NORETURN_ANNOTATIONS: frozenset[str] = frozenset({'NoReturn', 'Never'})
_LV29_MODULE_AST_CACHE: OrderedDict[
    str, tuple[tuple[int, int], ast.AST | None]
] = OrderedDict()
_LV29_MODULE_CACHE_MAX = 128
_LV29_MODULE_NORETURN_CACHE: OrderedDict[
    str, tuple[tuple[int, int], tuple[frozenset[str], frozenset[str]]]
] = OrderedDict()
_LV29_MODULE_NORETURN_CACHE_MAX = 2048
_LV29_DIR_ENTRIES_CACHE: OrderedDict[
    str, tuple[tuple[int, int] | None, frozenset[str]]
] = OrderedDict()
_LV29_DIR_ENTRIES_CACHE_MAX = 512
_LV29_REEXPORT_DEPTH = 8
_LV29_NONE_TYPE_NAMES: frozenset[str] = frozenset({'None', 'NoneType', 'Optional'})
_LV29_UNKNOWN_BINDING_ID = -1
_GENERIC_EXC_ROOT_NAMES = frozenset({'Exception', 'BaseException'})
_LV21_BASE_ONLY_NAMES = frozenset({
    'BaseException', 'SystemExit', 'KeyboardInterrupt',
    'GeneratorExit', 'BaseExceptionGroup',
})
_LV21_BUILTIN_EXCEPTION_NAMES = frozenset({
    'Exception',
    'ArithmeticError', 'FloatingPointError', 'OverflowError',
    'ZeroDivisionError', 'AssertionError', 'AttributeError',
    'BufferError', 'EOFError', 'ExceptionGroup', 'ImportError',
    'ModuleNotFoundError', 'LookupError', 'IndexError', 'KeyError',
    'MemoryError', 'NameError', 'UnboundLocalError', 'OSError',
    'BlockingIOError', 'ChildProcessError', 'ConnectionError',
    'BrokenPipeError', 'ConnectionAbortedError', 'ConnectionRefusedError',
    'ConnectionResetError', 'FileExistsError', 'FileNotFoundError',
    'InterruptedError', 'IsADirectoryError', 'NotADirectoryError',
    'PermissionError', 'ProcessLookupError', 'TimeoutError',
    'ReferenceError', 'RuntimeError', 'NotImplementedError',
    'RecursionError', 'StopAsyncIteration', 'StopIteration',
    'SyntaxError', 'IndentationError', 'TabError', 'SystemError',
    'TypeError', 'ValueError', 'UnicodeError', 'UnicodeDecodeError',
    'UnicodeEncodeError', 'UnicodeTranslateError', 'Warning',
    'BytesWarning', 'DeprecationWarning', 'EncodingWarning',
    'FutureWarning', 'ImportWarning', 'PendingDeprecationWarning',
    'ResourceWarning', 'RuntimeWarning', 'SyntaxWarning',
    'UnicodeWarning', 'UserWarning',
})
_LV21_KNOWN_BUILTIN_NAMES = (
    _LV21_BUILTIN_EXCEPTION_NAMES | _LV21_BASE_ONLY_NAMES
    | _GENERIC_EXC_ROOT_NAMES
)
_LV21_EXC_CLASSES: dict[str, type | None] = {}
def _lv17_exit_flow_context(
        stmts: list, parents: dict[int, ast.AST], filepath: Any,
) -> _LV29FlowCtx:
    scope = nearest_scope(parents, stmts[0]) if stmts else None
    root = scope
    while root is not None:
        parent = parents.get(id(root))
        if parent is None:
            break
        root = parent
    if root is None:
        sys_names = os_names = bare_exit = bare_abort = frozenset()
        imported_bare = imported_async_bare = frozenset()
        imported_attrs = imported_async_attrs = frozenset()
    else:
        sys_names, os_names, bare_exit, bare_abort = _lv29_exit_aliases(root)
        (imported_bare, imported_async_bare, imported_attrs,
         imported_async_attrs) = _lv29_imported_noreturn_names(root, filepath)
    ctx = _LV29FlowCtx(
        parents=parents,
        sys_aliases=sys_names,
        os_aliases=os_names,
        bare_exit_names=bare_exit | imported_bare,
        bare_abort_names=bare_abort,
        noreturn_names=frozenset(),
        async_noreturn_names=frozenset(),
        async_bare_exit_names=imported_async_bare,
        noreturn_module_attrs=imported_attrs,
        async_noreturn_module_attrs=imported_async_attrs,
        import_scope_ids=frozenset({id(root)}) if root is not None else frozenset(),
    )
    scope_imports: dict[int, _Lv29ScopeImports] = {}
    if root is not None:
        ctx = _lv29_hide_exit_shadows(ctx, _lv29_non_import_shadows(root))
        top_sync, top_async = _lv29_scope_noreturn_defs(
            root, ctx, filepath, scope_imports)
        ctx = ctx._replace(
            noreturn_names=ctx.noreturn_names | top_sync,
            async_noreturn_names=ctx.async_noreturn_names | top_async)
    if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return ctx
    for current_scope in reversed(_lv29_lexical_import_scopes(scope, parents)):
        delta = _lv29_scope_imports(current_scope, filepath, scope_imports)
        shadowed = set(delta.shadowed) | _lv29_non_import_shadows(current_scope)
        ctx = _lv29_hide_exit_shadows(ctx, shadowed)
        ctx = ctx._replace(
            sys_aliases=ctx.sys_aliases | delta.sys_aliases,
            os_aliases=ctx.os_aliases | delta.os_aliases,
            bare_exit_names=ctx.bare_exit_names | delta.bare_exit_names,
            bare_abort_names=ctx.bare_abort_names | delta.bare_abort_names,
            async_bare_exit_names=(
                ctx.async_bare_exit_names | delta.async_bare_exit_names),
            noreturn_module_attrs=(
                ctx.noreturn_module_attrs | delta.noreturn_module_attrs),
            async_noreturn_module_attrs=(
                ctx.async_noreturn_module_attrs
                | delta.async_noreturn_module_attrs),
            import_scope_ids=ctx.import_scope_ids | {id(current_scope)},
        )
        local_sync, local_async = _lv29_scope_noreturn_defs(
            current_scope, ctx, filepath, scope_imports)
        ctx = ctx._replace(
            noreturn_names=ctx.noreturn_names | local_sync,
            async_noreturn_names=ctx.async_noreturn_names | local_async)
    return ctx
def _has_exit_stmt(
        stmts: list, parents: dict[int, ast.AST], ctx: _LV29FlowCtx,
) -> bool:
    if any(isinstance(sub, ast.Return)
           for sub in scan_body_no_funcs(stmts)):
        return True
    for root_stmt in stmts:
        if _lv29_statement_has_exception_exit(
                root_stmt, ctx, root=root_stmt):
            return True
        if any(
                _lv29_exit_call_terminates(
                    sub, ctx, hard_exit_only=True)
                for sub in scan_body_no_funcs([root_stmt])):
            return True
    return False
def _body_has_yield(func: ast.AST) -> bool:
    return any(isinstance(n, (ast.Yield, ast.YieldFrom))
               for n in scan_body_no_funcs(getattr(func, 'body', [])))
def _lv17_in_class_scope(fn: ast.AST, parents: dict[int, ast.AST]) -> bool:
    cur = parents.get(id(fn))
    while cur is not None and not isinstance(cur, (
            ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
            ast.Module)):
        if isinstance(cur, ast.ClassDef):
            return True
        cur = parents.get(id(cur))
    return False
def _lv17_call_is_awaited(
        call_node: ast.Call, parents: dict[int, ast.AST]) -> bool:
    cur: ast.AST = call_node
    parent = parents.get(id(cur))
    while isinstance(parent, ast.IfExp):
        if subtree_contains(parent.test, cur):
            return False
        cur = parent
        parent = parents.get(id(cur))
    return isinstance(parent, ast.Await)
def _lv17_self_calls(
        fn: ast.AST, body_nodes: list[ast.AST],
        parents: dict[int, ast.AST]) -> list[ast.Call]:
    calls: list[ast.Call] = []
    for node in body_nodes:
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == fn.name):
            continue
        if (isinstance(fn, ast.AsyncFunctionDef)
                and not _lv17_call_is_awaited(node, parents)):
            continue
        if is_statically_unreachable(node, parents, fn):
            continue
        calls.append(node)
    return calls
def _lv17_handler_catches_recursion(
        handler: ast.ExceptHandler, ctx: _Lv21NameCtx) -> bool:
    if handler.type is None:
        return True
    names = _lv21_resolved_names(handler.type, ctx)
    return bool(names) and any(
        name in _LV17_RECURSION_HANDLERS for name in names)
def _lv17_try_guards_body(node: ast.AST, call_node: ast.Call,
                          parents: dict[int, ast.AST]) -> bool:
    in_body = any(
        subtree_contains(stmt, call_node) for stmt in node.body)
    ctx = _Lv21NameCtx(parents, {})
    return in_body and any(
        _lv17_handler_catches_recursion(handler, ctx)
        for handler in node.handlers
    )
def _lv17_block_contains(stmts: list, call_node: ast.Call) -> bool:
    return any(subtree_contains(stmt, call_node) for stmt in stmts)
def _lv17_other_branch_has_self_call(
        parent: ast.If | ast.IfExp, call_node: ast.Call,
        parents: dict[int, ast.AST], ctx: _LV29FlowCtx) -> bool:
    fn = nearest_scope(parents, call_node)
    if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False
    if isinstance(parent.body, list):
        in_body = _lv17_block_contains(parent.body, call_node)
    else:
        in_body = subtree_contains(parent.body, call_node)
    other = parent.orelse if in_body else parent.body
    other_nodes = other if isinstance(other, list) else [other]
    if in_body and not other_nodes:
        # 无 else 的 if：另一条路径是 if 之后的落穿续体，不是空分支
        other_nodes = _lv17_fallthrough_statements(parent, parents)
    other_calls = _lv17_self_calls(
        fn, scan_body_no_funcs(other_nodes), parents)
    # 「另一分支含自调用」不等于「另一分支无基例」：elif/嵌套条件
    # 表达式中的自调用可能自身受基例保护。只在另一分支存在未受
    # 保护的自调用时才维持原判定；boundary 防止再次借用当前分支。
    return any(
        not _lv17_has_control_flow(
            other_nodes, other_call, parents, ctx, boundary=parent)
        for other_call in other_calls)
def _lv17_fallthrough_statements(
        node: ast.AST, parents: dict[int, ast.AST]) -> list:
    """``node`` 所在语句块中位于其后的同块后继语句。"""
    container = parents.get(id(node))
    if container is None:
        return []
    for field in ('body', 'orelse', 'finalbody'):
        seq = getattr(container, field, None)
        if not isinstance(seq, list):
            continue
        for index, stmt in enumerate(seq):
            if stmt is node:
                return seq[index + 1:]
    return []
def _lv17_if_guards(parent: ast.If, call_node: ast.Call,
                    parents: dict[int, ast.AST], ctx: _LV29FlowCtx) -> bool:
    truth = constant_truth(parent.test)
    if truth is None:
        return not _lv17_other_branch_has_self_call(
            parent, call_node, parents, ctx)
    return truth != _lv17_block_contains(parent.body, call_node)
def _lv17_loop_exit_before_call(
        loop: ast.While | ast.For | ast.AsyncFor, call_node: ast.Call,
        parents: dict[int, ast.AST], ctx: _LV29FlowCtx) -> bool:
    call_pos = (call_node.lineno, call_node.col_offset)
    for node in scan_body_no_funcs(loop.body):
        if not isinstance(node, (
                ast.Break, ast.Return, ast.Raise, ast.Expr, ast.Assign,
                ast.AnnAssign, ast.AugAssign, ast.Assert)):
            continue
        if subtree_contains(node, call_node):
            continue
        if (node.lineno, node.col_offset) >= call_pos:
            continue
        if is_statically_unreachable(node, parents, loop):
            continue
        if isinstance(node, ast.Break):
            if break_binding_loop(parents, node) is loop:
                return True
            continue
        if isinstance(node, ast.Return):
            return True
        if _lv29_statement_has_exception_exit(node, ctx, root=loop):
            return True
        if _lv29_exit_call_terminates(node, ctx, hard_exit_only=True):
            return True
        if isinstance(node, (ast.Raise, ast.Assert)):
            expression = node.exc if isinstance(node, ast.Raise) else node.test
            if (expression is not None
                    and _lv29_expression_terminates(
                        expression, ctx, hard_exit_only=True)):
                return True
    return False
def _lv17_while_guards(parent: ast.While, call_node: ast.Call,
                       parents: dict[int, ast.AST], ctx: _LV29FlowCtx) -> bool:
    if _lv17_block_contains(parent.body, call_node):
        if not is_constant_true_while(parent):
            return True
        return _lv17_loop_exit_before_call(parent, call_node, parents, ctx)
    return _lv17_loop_exit_before_call(parent, call_node, parents, ctx)
def _lv17_match_case_has_self_call(case: ast.AST, fn_name: str) -> bool:
    nodes = list(scan_body_no_funcs(case.body))
    if case.guard is not None:
        nodes.extend(walk_ast_nodes(case.guard))
    return any(isinstance(node, ast.Call)
               and isinstance(node.func, ast.Name) and node.func.id == fn_name
               for node in nodes)
def _lv17_match_guards(parent: ast.Match, call_node: ast.Call) -> bool:
    prior_base = False
    fn_name = getattr(call_node.func, 'id', '')
    for case in parent.cases:
        irrefutable = is_irrefutable_pattern(case.pattern)
        guard_truth = constant_truth(case.guard)
        if (case.guard is not None
                and subtree_contains(case.guard, call_node)):
            return prior_base or not irrefutable
        in_case = _lv17_block_contains(case.body, call_node)
        if (irrefutable
                and (case.guard is None or guard_truth is True)):
            return prior_base or not in_case
        if (not in_case and guard_truth is not False
                and not _lv17_match_case_has_self_call(case, fn_name)):
            prior_base = True
    return True
def _lv17_statically_nonempty_iterable(node: ast.AST) -> bool:
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return bool(node.elts)
    if isinstance(node, ast.Dict):
        return bool(node.keys)
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and bool(node.value))
def _lv17_never_executes_body(node: ast.AST) -> bool:
    if isinstance(node, (ast.If, ast.While)):
        return constant_truth(getattr(node, 'test', None)) is False
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return statically_empty_iterable(node.iter)
    return False
def _lv17_boolop_guards(parent: ast.BoolOp, call_node: ast.Call) -> bool:
    short_circuit_on = not isinstance(parent.op, ast.And)
    for value in parent.values:
        if subtree_contains(value, call_node):
            return False
        truth = constant_truth(value)
        if truth is None or truth is short_circuit_on:
            return True
    return False
def _lv17_handler_has_base_path(
        handler: ast.ExceptHandler, parents: dict[int, ast.AST],
        ctx: _LV29FlowCtx) -> bool:
    try_node = parents.get(id(handler))
    if not isinstance(try_node, ast.Try):
        return True
    scope = nearest_scope(parents, try_node)
    body_nodes = list(scan_body_no_funcs(try_node.body))
    for node in body_nodes:
        if (scope is not None
                and is_statically_unreachable(node, parents, scope)):
            continue
        if isinstance(node, ast.Return):
            return True
        if _lv29_exit_call_terminates(
                node, ctx, hard_exit_only=True):
            return True
    if not _lv29_terminate(
            try_node.body, ctx, allow_return=True, exceptions_exit=True):
        return True
    reachable_handlers, has_uncaught = _lv29_try_exception_routes(
        try_node, ctx)
    if has_uncaught:
        return True
    return reachable_handlers != {try_node.handlers.index(handler)}

def _lv17_guard_position(call_node: ast.Call, parent: ast.AST,
                         parents: dict[int, ast.AST], ctx: _LV29FlowCtx) -> bool:
    if isinstance(parent, (ast.For, ast.AsyncFor)):
        if subtree_contains(parent.iter, call_node):
            return False
        if _lv17_block_contains(parent.body, call_node):
            if (isinstance(parent, ast.For)
                    and _lv17_statically_nonempty_iterable(parent.iter)):
                return _lv17_loop_exit_before_call(
                    parent, call_node, parents, ctx)
            return True
        return _lv17_loop_exit_before_call(parent, call_node, parents, ctx)
    if isinstance(parent, TRY_NODES):
        return _lv17_try_guards_body(parent, call_node, parents)
    if isinstance(parent, (ast.If, ast.While, ast.Assert, ast.Match)):
        test = getattr(parent, 'test', None)
        if test is None:
            test = getattr(parent, 'subject', None)
        if subtree_contains(test, call_node):
            return False
        if isinstance(parent, ast.If):
            return _lv17_if_guards(parent, call_node, parents, ctx)
        if isinstance(parent, ast.While):
            return _lv17_while_guards(parent, call_node, parents, ctx)
        if isinstance(parent, ast.Assert):
            return constant_truth(parent.test) is not False
        if isinstance(parent, ast.Match):
            return _lv17_match_guards(parent, call_node)
        return True
    if isinstance(parent, ast.IfExp):
        if subtree_contains(parent.test, call_node):
            return False
        truth = constant_truth(parent.test)
        if truth is None:
            return not _lv17_other_branch_has_self_call(
                parent, call_node, parents, ctx)
        return truth != subtree_contains(parent.body, call_node)
    if isinstance(parent, ast.BoolOp):
        return _lv17_boolop_guards(parent, call_node)
    if isinstance(parent, _LV17_COMPREHENSION_NODES):
        if isinstance(parent, ast.GeneratorExp):
            return not (
                parent.generators
                and subtree_contains(parent.generators[0].iter, call_node))
        for generator in parent.generators:
            if subtree_contains(generator.iter, call_node):
                return False
            if not _lv17_statically_nonempty_iterable(generator.iter):
                return True
            for condition in generator.ifs:
                if subtree_contains(condition, call_node):
                    return False
                if constant_truth(condition) is not True:
                    return True
        return False
    if isinstance(parent, ast.ExceptHandler):
        return _lv17_handler_has_base_path(parent, parents, ctx)
    return True
def _lv17_call_is_guarded(
        call_node: ast.Call, parents: dict[int, ast.AST], ctx: _LV29FlowCtx,
        boundary: ast.AST | None = None,
) -> bool:
    cur = parents.get(id(call_node))
    while cur is not None and cur is not boundary and not isinstance(
            cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.Module)):
        if (isinstance(cur, _LV17_CONTROL_FLOW_NODES)
                and _lv17_guard_position(call_node, cur, parents, ctx)):
            return True
        cur = parents.get(id(cur))
    return False
def _lv17_has_control_flow(body_nodes: list[ast.AST],
                           call_node: ast.Call,
                           parents: dict[int, ast.AST],
                           ctx: _LV29FlowCtx,
                           boundary: ast.AST | None = None) -> bool:
    call_pos = (call_node.lineno, call_node.col_offset)
    for node in body_nodes:
        direct_exit = (
            isinstance(node, (ast.Expr, ast.Assign, ast.AnnAssign,
                              ast.AugAssign))
            and isinstance(parents.get(id(node)), (
                ast.FunctionDef, ast.AsyncFunctionDef)))
        if not (direct_exit or isinstance(node, _LV17_CONTROL_FLOW_NODES)):
            continue
        if subtree_contains(node, call_node):
            continue
        if (node.lineno, node.col_offset) >= call_pos:
            continue
        if not isinstance(node, _LV17_CONTROL_FLOW_NODES):
            if direct_exit and _has_exit_stmt([node], parents, ctx):
                return True
            continue
        blocks_call = (is_constant_true_while(node)
                       and not loop_has_binding(parents, node, ast.Break))
        if not (_has_exit_stmt([node], parents, ctx) or blocks_call):
            continue
        if (_lv17_never_executes_body(node)
                and not _has_exit_stmt(
                    getattr(node, 'orelse', []), parents, ctx)):
            continue
        return True
    return _lv17_call_is_guarded(
        call_node, parents, ctx, boundary=boundary)
def _lv17_self_call_without_branch(
        fn: ast.AST, name_counts: dict[tuple[int, str], int],
        parents: dict[int, ast.AST], filepath: Any,
) -> ast.Call | None:
    scope = nearest_scope(parents, fn)
    scope_key = id(scope) if scope is not None else 0
    if (fn.decorator_list or _lv17_in_class_scope(fn, parents)
            or name_counts.get((scope_key, fn.name), 0) > 1):
        return None
    if fn.name in scope_local_bindings(fn):
        return None
    if _body_has_yield(fn):
        return None
    body_nodes = scan_body_no_funcs(fn.body)
    call_nodes = _lv17_self_calls(fn, body_nodes, parents)
    if not call_nodes:
        return None
    ctx = _lv17_exit_flow_context(fn.body, parents, filepath)
    for call_node in sorted(
            call_nodes, key=lambda n: (n.lineno, n.col_offset)):
        if not _lv17_has_control_flow(body_nodes, call_node, parents, ctx):
            return call_node
    return None
def _lv17_issue(filepath: Any, src_lines: list[str], call_node: ast.Call,
                fn_name: str) -> dict[str, Any]:
    return make_issue(
        'LV-17', 'P1', _FINDING_DIMENSION, filepath, call_node.lineno,
        f'函数 {fn_name}() 无条件分支却自调用：无基例、必无限递归',
        (
            f'``{fn_name}()`` 函数体内没有任何条件分支'
            f'（if/for/while/try/条件表达式/推导式），却存在对自身的'
            f'直接调用——递归路径无条件执行且无终止条件，'
            f'首次调用即 RecursionError（超过最大递归深度）。'
        ),
        snippet_of(src_lines, call_node.lineno),
        (
            '根因：迭代改进/遍历逻辑忘写终止条件（基例），'
            '「处理后再处理一步」的意图直译成了无条件自调用。\n'
            '修复策略：补基例 ``if <终止条件>: return <结果>``；'
            '或改用 while 循环迭代（终止条件显式可控）。\n'
            '参考标准：无基例递归缺陷模式'
            '（Python 语言参考 RecursionError 语义）'
        ),
        'recursion-no-base-case',
    )
def check_LV17(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    functions = [n for n in walk_ast_nodes(tree)
                 if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    if not functions:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    name_counts: dict[tuple[int, str], int] = {}
    for fn in functions:
        scope = nearest_scope(parents, fn)
        scope_key = id(scope) if scope is not None else 0
        key = (scope_key, fn.name)
        name_counts[key] = name_counts.get(key, 0) + 1
    for fn in functions:
        call_node = _lv17_self_call_without_branch(
            fn, name_counts, parents, filepath)
        if call_node is None:
            continue
        issues.append(_lv17_issue(filepath, src_lines, call_node, fn.name))
    return issues
def _lv29_register_module_alias(alias: ast.alias, sys_names: set[str],
                               os_names: set[str]) -> None:
    if alias.asname:
        if alias.name == 'sys':
            sys_names.add(alias.asname)
        elif alias.name == 'os':
            os_names.add(alias.asname)
        return
    root = alias.name.split('.')[0]
    if root == 'sys':
        sys_names.add(root)
    elif root == 'os':
        os_names.add(root)
def _lv29_exit_aliases(
        tree: ast.AST,
) -> tuple[frozenset[str], frozenset[str], frozenset[str], frozenset[str]]:
    sys_names: set[str] = set()
    os_names: set[str] = set()
    bare_names: set[str] = set()
    bare_abort_names: set[str] = set()
    for node, _in_handler in iter_scope_statements(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                _lv29_register_module_alias(alias, sys_names, os_names)
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        if node.module == 'sys':
            bare_names.update(alias.asname or alias.name
                              for alias in node.names
                              if alias.name == 'exit')
        elif node.module == 'os':
            bare_abort_names.update(alias.asname or alias.name
                                    for alias in node.names
                                    if alias.name == '_exit')
    return (frozenset(sys_names), frozenset(os_names),
            frozenset(bare_names), frozenset(bare_abort_names))
class _LV29FlowCtx(NamedTuple):
    parents: dict[int, ast.AST]
    sys_aliases: frozenset[str]
    os_aliases: frozenset[str]
    bare_exit_names: frozenset[str]
    bare_abort_names: frozenset[str]
    noreturn_names: frozenset[str]
    async_noreturn_names: frozenset[str]
    async_bare_exit_names: frozenset[str]
    noreturn_module_attrs: frozenset[str]
    async_noreturn_module_attrs: frozenset[str]
    import_scope_ids: frozenset[int]
def _lv29_parse_str_annotation(text: str) -> ast.AST | None:
    try:
        return ast.parse(text, mode='eval').body
    except (SyntaxError, ValueError) as _swallow_e:
        log_swallowed(
            __name__, _swallow_e,
            context='_lv29_parse_str_annotation:SyntaxError+')
        return None
def _lv29_is_noreturn_annotation(node: ast.AST | None) -> bool:
    if isinstance(node, ast.Name):
        return node.id in _LV29_NORETURN_ANNOTATIONS
    if isinstance(node, ast.Attribute):
        return node.attr in _LV29_NORETURN_ANNOTATIONS
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return _lv29_is_noreturn_annotation(
            _lv29_parse_str_annotation(node.value))
    return False
def _lv29_has_normal_return(fn: ast.AST, ctx: _LV29FlowCtx) -> bool:
    for node in scan_body_no_funcs(getattr(fn, 'body', [])):
        if not isinstance(node, ast.Return):
            continue
        if is_statically_unreachable(node, ctx.parents, fn):
            continue
        if (node.value is not None
                and _lv29_expression_terminates(node.value, ctx)):
            continue
        parent = ctx.parents.get(id(node))
        overridden = False
        while parent is not None and parent is not fn:
            if isinstance(parent, TRY_NODES) and parent.finalbody:
                in_finalbody = any(
                    subtree_contains(stmt, node) for stmt in parent.finalbody)
                if (not in_finalbody and _lv29_terminate(
                        parent.finalbody, ctx, allow_return=False)):
                    overridden = True
                    break
            parent = ctx.parents.get(id(parent))
        if not overridden:
            return True
    return False
def _lv29_merge_candidate_states(
        *states: dict[str, frozenset[int]],
) -> dict[str, frozenset[int]]:
    merged: dict[str, set[int]] = {}
    for state in states:
        for name, definition_ids in state.items():
            merged.setdefault(name, set()).update(definition_ids)
    return {name: frozenset(ids) for name, ids in merged.items()}
def _lv29_active_candidate_bindings(
        scope: ast.AST, candidates: list[ast.AST],
) -> dict[str, frozenset[int]]:
    candidate_ids = {id(node) for node in candidates}
    parents = parent_map_of(scope)
    def visit(
            stmts: list, initial: dict[str, frozenset[int]],
    ) -> dict[str, frozenset[int]]:
        state = dict(initial)
        for stmt in stmts:
            if (isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and id(stmt) in candidate_ids):
                state[stmt.name] = frozenset({id(stmt)})
                continue
            if isinstance(stmt, ast.If):
                truth = constant_truth(stmt.test)
                if truth is not None:
                    state = visit(stmt.body if truth else stmt.orelse, state)
                else:
                    state = _lv29_merge_candidate_states(
                        visit(stmt.body, state), visit(stmt.orelse, state))
                continue
            if isinstance(stmt, ast.Match):
                before = state
                routes = []
                exhaustive = False
                for case in stmt.cases:
                    guard_truth = constant_truth(case.guard)
                    if guard_truth is False:
                        continue
                    routes.append(visit(case.body, before))
                    if (is_irrefutable_pattern(case.pattern)
                            and (case.guard is None or guard_truth is True)):
                        exhaustive = True
                        break
                if not exhaustive:
                    routes.append(before)
                state = _lv29_merge_candidate_states(*routes)
                continue
            if isinstance(stmt, TRY_NODES):
                before = state
                body = visit(stmt.body, before)
                normal = visit(stmt.orelse, body) if stmt.orelse else body
                handler_base = _lv29_merge_candidate_states(before, body)
                routes = [normal]
                routes.extend(
                    visit(handler.body, handler_base)
                    for handler in stmt.handlers)
                state = visit(
                    stmt.finalbody, _lv29_merge_candidate_states(*routes))
                continue
            if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
                before = state
                if _lv17_never_executes_body(stmt):
                    state = visit(stmt.orelse, before)
                elif (isinstance(stmt, ast.For)
                      and _lv17_statically_nonempty_iterable(stmt.iter)
                      and not loop_has_binding(parents, stmt, ast.Break)
                      and not loop_has_binding(parents, stmt, ast.Continue)):
                    state = visit(
                        stmt.orelse, visit(stmt.body, before))
                else:
                    body = visit(stmt.body, before)
                    state = _lv29_merge_candidate_states(
                        body, visit(stmt.orelse, before),
                        visit(stmt.orelse, body))
                continue
            if isinstance(stmt, (ast.With, ast.AsyncWith)):
                state = _lv29_merge_candidate_states(
                    state, visit(stmt.body, state))
                continue
            for name in assigned_names([stmt]):
                state[name] = frozenset({_LV29_UNKNOWN_BINDING_ID})
            if isinstance(stmt, ast.ClassDef):
                state[stmt.name] = frozenset({_LV29_UNKNOWN_BINDING_ID})
        return state
    body = getattr(scope, 'body', [])
    return visit(body if isinstance(body, list) else [], {})
def _lv29_terminated_name_sets(
        candidates: list[ast.AST],
        active_bindings: dict[str, frozenset[int]],
        terminated: set[int],
) -> tuple[frozenset[str], frozenset[str]]:
    by_id = {id(node): node for node in candidates}
    sync_names: set[str] = set()
    async_names: set[str] = set()
    for name, definition_ids in active_bindings.items():
        if not definition_ids or not definition_ids <= terminated:
            continue
        definitions = [by_id[node_id] for node_id in definition_ids]
        if all(isinstance(node, ast.FunctionDef) for node in definitions):
            sync_names.add(name)
        elif all(isinstance(node, ast.AsyncFunctionDef) for node in definitions):
            async_names.add(name)
    return frozenset(sync_names), frozenset(async_names)
def _lv29_noreturn_fixpoint(
        candidates: list[ast.AST], ctx: _LV29FlowCtx,
        base_sync: frozenset[str], base_async: frozenset[str],
        *, all_candidates: list[ast.AST],
        active_bindings: dict[str, frozenset[int]],
        allow_return: bool, filepath: Any,
        cache: dict[int, _Lv29ScopeImports],
) -> tuple[frozenset[str], frozenset[str]]:
    sync_names: frozenset[str] = frozenset()
    async_names: frozenset[str] = frozenset()
    prepared: dict[int, tuple[_LV29FlowCtx, frozenset[str]]] = {}
    while True:
        current = ctx._replace(
            noreturn_names=base_sync | sync_names,
            async_noreturn_names=base_async | async_names)
        terminated: set[int] = set()
        for node in candidates:
            if node.decorator_list or _body_has_yield(node):
                continue
            entry = prepared.get(id(node))
            if entry is None:
                prepared_ctx, imported_shadows = _lv29_visible_import_context(
                    node, ctx, filepath, cache)
                entry = (prepared_ctx,
                         imported_shadows
                         | frozenset(_lv29_non_import_shadows(node)))
                prepared[id(node)] = entry
            prepared_ctx, shadows = entry
            candidate_ctx = _lv29_hide_exit_shadows(
                prepared_ctx._replace(
                    noreturn_names=current.noreturn_names,
                    async_noreturn_names=current.async_noreturn_names),
                set(shadows))
            if (not allow_return
                    and _lv29_has_normal_return(node, candidate_ctx)):
                continue
            if _lv29_terminate(
                    node.body, candidate_ctx, allow_return=allow_return):
                terminated.add(id(node))
        new_sync, new_async = _lv29_terminated_name_sets(
            all_candidates, active_bindings, terminated)
        grown_sync = sync_names | new_sync
        grown_async = async_names | new_async
        if grown_sync == sync_names and grown_async == async_names:
            return sync_names, async_names
        sync_names, async_names = grown_sync, grown_async
def _lv29_declared_noreturn(
        candidates: list[ast.AST]) -> list[ast.AST]:
    return [
        node for node in candidates
        if not node.decorator_list and not _body_has_yield(node)
        and _lv29_is_noreturn_annotation(getattr(node, 'returns', None))
        and not any(isinstance(inner, ast.Return)
                    for inner in scan_body_no_funcs(node.body))
    ]
def _lv29_stat_fingerprint(path: str) -> tuple[int, int] | None:
    try:
        stat_result = os.stat(path)
    except OSError as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context='_lv29_stat_fingerprint:OSError+')
        return None
    return stat_result.st_mtime_ns, stat_result.st_size
def _lv29_cache_store(cache: OrderedDict, path: str, entry,
                      max_entries: int) -> None:
    cache[path] = entry
    cache.move_to_end(path)
    while len(cache) > max_entries:
        cache.popitem(last=False)
def _lv29_dir_entries(directory: str) -> frozenset[str]:
    cacheable = True
    try:
        stat_result = os.stat(directory)
        fingerprint = (stat_result.st_mtime_ns, stat_result.st_size)
    except (FileNotFoundError, NotADirectoryError):
        fingerprint = None
    except OSError as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context='_lv29_dir_entries:stat:OSError+')
        fingerprint = None
        cacheable = False
    cached = _LV29_DIR_ENTRIES_CACHE.get(directory)
    if (cacheable and cached is not None
            and cached[0] == fingerprint):
        _LV29_DIR_ENTRIES_CACHE.move_to_end(directory)
        return cached[1]
    try:
        entries = frozenset(os.listdir(directory))
    except (FileNotFoundError, NotADirectoryError):
        entries = frozenset()
    except OSError as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context='_lv29_dir_entries:OSError+')
        return frozenset()
    if cacheable:
        _lv29_cache_store(_LV29_DIR_ENTRIES_CACHE, directory,
                          (fingerprint, entries), _LV29_DIR_ENTRIES_CACHE_MAX)
    return entries
def _lv29_module_candidate_paths(
        directory: str, parts: list[str]) -> tuple[str, str]:
    root = os.path.join(directory, *parts)
    return os.path.join(root, '__init__.py'), root + '.py'
def _lv29_module_file(module: str, level: int, filepath: Any) -> str | None:
    try:
        filepath_text = os.fsdecode(os.fspath(filepath))
    except (OSError, TypeError, ValueError):
        return None
    if not filepath_text:
        return None
    raw_dir = os.path.dirname(filepath_text)
    base = os.path.abspath(raw_dir or os.curdir)
    root = base
    for _ in range(max(int(level) - 1, 0)):
        parent = os.path.dirname(root)
        if not parent or parent == root:
            break
        root = parent
    parts = [part for part in str(module or '').split('.') if part]
    if not parts:
        return None
    if level:
        search_dirs = [root]
        if base and base != root:
            search_dirs.append(base)
    else:
        search_dirs = []
        current = base or os.path.abspath(os.curdir)
        while True:
            search_dirs.append(current)
            parent = os.path.dirname(current)
            if not parent or parent == current:
                break
            current = parent
    candidates = [
        candidate
        for directory in search_dirs
        for candidate in _lv29_module_candidate_paths(directory, parts)
    ]
    if len(parts) > 1:
        fallback_dirs = [root]
        if base and base != root:
            fallback_dirs.append(base)
        candidates.extend(
            candidate
            for directory in fallback_dirs
            for candidate in _lv29_module_candidate_paths(
                directory, [parts[-1]])
        )
    for candidate in candidates:
        directory, name = os.path.split(candidate)
        if name not in _lv29_dir_entries(directory):
            continue
        try:
            return os.path.realpath(candidate)
        except OSError as _swallow_e:
            log_swallowed(
                __name__, _swallow_e, context='_lv29_module_file:OSError+')
    return None
def _lv29_package_init_file(level: int, filepath: Any) -> str | None:
    """``from <dots> import X``（module 为空）指向的包 ``__init__`` 路径。

    X 可以是包 ``__init__`` 直接定义或再导出的 NoReturn 名字，不走
    子模块文件路径；不解析它会让这类导入在 LV-29 中静默失效。
    """
    try:
        filepath_text = os.fsdecode(os.fspath(filepath))
    except (OSError, TypeError, ValueError):
        return None
    if not filepath_text:
        return None
    root = os.path.abspath(os.path.dirname(filepath_text) or os.curdir)
    for _ in range(max(int(level) - 1, 0)):
        parent = os.path.dirname(root)
        if not parent or parent == root:
            return None
        root = parent
    if '__init__.py' not in _lv29_dir_entries(root):
        return None
    try:
        return os.path.realpath(os.path.join(root, '__init__.py'))
    except OSError as _swallow_e:
        log_swallowed(
            __name__, _swallow_e, context='_lv29_package_init_file:OSError+')
        return None
def _lv29_module_tree(path: str) -> ast.AST | None:
    fingerprint = _lv29_stat_fingerprint(path)
    if fingerprint is None:
        _LV29_MODULE_AST_CACHE.pop(path, None)
        return None
    cached = _LV29_MODULE_AST_CACHE.get(path)
    if cached is not None and cached[0] == fingerprint:
        _LV29_MODULE_AST_CACHE.move_to_end(path)
        return cached[1]
    tree: ast.AST | None = None
    try:
        _lv_src = read_source(path)
        if _lv_src is None:
            raise OSError(f"源码不可读: {path}")
        tree = parse_cached(_lv_src, path)
    except (OSError, SyntaxError, ValueError, TypeError,
            RecursionError, MemoryError) as _swallow_e:
        log_swallowed(__name__, _swallow_e,
                      context='_lv29_module_tree:OSError+')
    _lv29_cache_store(_LV29_MODULE_AST_CACHE, path, (fingerprint, tree),
                      _LV29_MODULE_CACHE_MAX)
    return tree
def _lv29_module_noreturn_names(
        path: str) -> tuple[frozenset[str], frozenset[str]]:
    fingerprint = _lv29_stat_fingerprint(path)
    if fingerprint is None:
        _LV29_MODULE_NORETURN_CACHE.pop(path, None)
        return frozenset(), frozenset()
    cached = _LV29_MODULE_NORETURN_CACHE.get(path)
    if cached is not None and cached[0] == fingerprint:
        _LV29_MODULE_NORETURN_CACHE.move_to_end(path)
        return cached[1]
    tree = _lv29_module_tree(path)
    if tree is None:
        return frozenset(), frozenset()
    candidates = scope_function_defs(tree)
    declared = _lv29_declared_noreturn(candidates)
    active_bindings = _lv29_active_candidate_bindings(tree, candidates)
    result = _lv29_terminated_name_sets(
        candidates, active_bindings, {id(node) for node in declared})
    _lv29_cache_store(_LV29_MODULE_NORETURN_CACHE, path,
                      (fingerprint, result), _LV29_MODULE_NORETURN_CACHE_MAX)
    return result
def _lv29_module_reexport_noreturn(
        path: str, name: str, *, depth: int = 0,
) -> tuple[frozenset[str], frozenset[str]]:
    if depth >= _LV29_REEXPORT_DEPTH:
        return frozenset(), frozenset()
    tree = _lv29_module_tree(path)
    if tree is None:
        return frozenset(), frozenset()
    for node, _in_handler in iter_scope_statements(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        for alias in node.names:
            if alias.name == '*' or (alias.asname or alias.name) != name:
                continue
            source = _lv29_module_file(
                node.module or '', node.level or 0, path)
            if source is None or source == path:
                continue
            sync_names, async_names = _lv29_module_noreturn_names(source)
            if alias.name in sync_names:
                return frozenset({name}), frozenset()
            if alias.name in async_names:
                return frozenset(), frozenset({name})
            sub_sync, sub_async = _lv29_module_reexport_noreturn(
                source, alias.name, depth=depth + 1)
            if alias.name in sub_sync:
                return frozenset({name}), frozenset()
            if alias.name in sub_async:
                return frozenset(), frozenset({name})
    return frozenset(), frozenset()
#: ``_lv29_imported_noreturn_names`` 的记忆化表。
#:
#: 该函数只依赖「当前文件的树 + 文件路径」：内部把每个 import 语句解析成
#: 模块路径、再查 ``_LV29_MODULE_NORETURN_CACHE``。实测同一文件被调用
#: 9 次（每个函数作用域各一次），每次都把全部 import 重跑一遍。
#: 值只存 ``frozenset[str]``，不引用树，无引用环风险。
_LV29_IMPORTED_NORETURN_CACHE: Any = None

def _lv29_imported_noreturn_names(
        tree: ast.AST, filepath: Any,
) -> tuple[frozenset[str], frozenset[str], frozenset[str], frozenset[str]]:
    global _LV29_IMPORTED_NORETURN_CACHE
    cache = _LV29_IMPORTED_NORETURN_CACHE
    if cache is None:
        from weakref import WeakKeyDictionary
        cache = _LV29_IMPORTED_NORETURN_CACHE = WeakKeyDictionary()
    try:
        per_path = cache.get(tree)
    except TypeError:
        per_path = None
        cache = None
    key = _lv29_file_key(filepath)
    if per_path is not None and key in per_path:
        return per_path[key]
    result = _lv29_imported_noreturn_names_uncached(tree, filepath)
    if cache is not None:
        try:
            per_path = cache.get(tree)
            if per_path is None:
                per_path = {}
                cache[tree] = per_path
            per_path[key] = result
        except TypeError:
            pass
    return result

def _lv29_file_key(filepath: Any) -> str:
    try:
        return os.fspath(filepath)
    except TypeError:
        return repr(filepath)

def _lv29_imported_noreturn_names_uncached(
        tree: ast.AST, filepath: Any,
) -> tuple[frozenset[str], frozenset[str], frozenset[str], frozenset[str]]:
    bare: set[str] = set()
    async_bare: set[str] = set()
    attrs: set[str] = set()
    async_attrs: set[str] = set()
    requested_attrs = {
        call_name
        for node in walk_ast_nodes(tree)
        if isinstance(node, ast.Call)
        and (call_name := dotted_name(node.func))
    }
    for node, _in_handler in iter_scope_statements(tree):
        if isinstance(node, ast.ImportFrom):
            path = _lv29_module_file(
                node.module or '', node.level or 0, filepath)
            if path is None and node.level and not node.module:
                path = _lv29_package_init_file(node.level, filepath)
            sync_names: frozenset[str] = frozenset()
            async_names: frozenset[str] = frozenset()
            if path is not None:
                sync_names, async_names = _lv29_module_noreturn_names(path)
            for alias in node.names:
                if alias.name == '*':
                    continue
                local = alias.asname or alias.name
                if alias.name in sync_names:
                    bare.add(local)
                    continue
                if alias.name in async_names:
                    async_bare.add(local)
                    continue
                if path is not None:
                    reexport_sync, reexport_async = (
                        _lv29_module_reexport_noreturn(path, alias.name))
                    if alias.name in reexport_sync:
                        bare.add(local)
                        continue
                    if alias.name in reexport_async:
                        async_bare.add(local)
                        continue
                submodule = (
                    f'{node.module}.{alias.name}' if node.module else alias.name)
                submodule_path = _lv29_module_file(
                    submodule, node.level or 0, filepath)
                if submodule_path is None:
                    continue
                sub_sync, sub_async = _lv29_module_noreturn_names(submodule_path)
                module_alias = alias.asname or alias.name
                attrs.update(f'{module_alias}.{name}' for name in sub_sync)
                async_attrs.update(f'{module_alias}.{name}' for name in sub_async)
            continue
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            path = _lv29_module_file(alias.name, 0, filepath)
            if path is None:
                continue
            sync_names, async_names = _lv29_module_noreturn_names(path)
            module_alias = alias.asname or alias.name
            attrs.update(f'{module_alias}.{name}' for name in sync_names)
            async_attrs.update(
                f'{module_alias}.{name}' for name in async_names)
            prefix = f'{module_alias}.'
            reexport_names = {
                call_name[len(prefix):]
                for call_name in requested_attrs
                if call_name.startswith(prefix)
                and '.' not in call_name[len(prefix):]
            }
            for name in reexport_names:
                re_sync, re_async = _lv29_module_reexport_noreturn(path, name)
                if name in re_sync:
                    attrs.add(prefix + name)
                elif name in re_async:
                    async_attrs.add(prefix + name)
    return (frozenset(bare), frozenset(async_bare),
            frozenset(attrs), frozenset(async_attrs))
def _lv29_import_binding_names(scope: ast.AST) -> set[str]:
    names: set[str] = set()
    for node, _in_handler in iter_scope_statements(scope):
        if isinstance(node, ast.Import):
            names.update(alias.asname or alias.name.split('.')[0]
                         for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            names.update(alias.asname or alias.name for alias in node.names
                         if alias.name != '*')
    return names
def _lv29_lexical_import_scopes(
        fn: ast.AST, parents: dict[int, ast.AST]) -> list[ast.AST]:
    scopes = [fn]
    cur = nearest_scope(parents, fn)
    while cur is not None and not isinstance(cur, ast.Module):
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            scopes.append(cur)
        cur = nearest_scope(parents, cur)
    return scopes
class _Lv29ScopeImports(NamedTuple):
    shadowed: frozenset[str]
    sys_aliases: frozenset[str]
    os_aliases: frozenset[str]
    bare_exit_names: frozenset[str]
    bare_abort_names: frozenset[str]
    async_bare_exit_names: frozenset[str]
    noreturn_module_attrs: frozenset[str]
    async_noreturn_module_attrs: frozenset[str]
def _lv29_scope_imports(
        scope: ast.AST, filepath: Any,
        cache: dict[int, _Lv29ScopeImports]) -> _Lv29ScopeImports:
    key = id(scope)
    cached = cache.get(key)
    if cached is not None:
        return cached
    sys_names, os_names, bare_exit, bare_abort = _lv29_exit_aliases(scope)
    (imported_bare, imported_async_bare, imported_attrs,
     imported_async_attrs) = _lv29_imported_noreturn_names(scope, filepath)
    delta = _Lv29ScopeImports(
        shadowed=frozenset(_lv29_import_binding_names(scope)),
        sys_aliases=sys_names,
        os_aliases=os_names,
        bare_exit_names=bare_exit | imported_bare,
        bare_abort_names=bare_abort,
        async_bare_exit_names=imported_async_bare,
        noreturn_module_attrs=imported_attrs,
        async_noreturn_module_attrs=imported_async_attrs,
    )
    cache[key] = delta
    return delta
def _lv29_visible_import_context(
        fn: ast.AST, ctx: _LV29FlowCtx, filepath: Any,
        cache: dict[int, _Lv29ScopeImports],
) -> tuple[_LV29FlowCtx, frozenset[str]]:
    hidden: set[str] = set()
    for scope in _lv29_lexical_import_scopes(fn, ctx.parents):
        scope_id = id(scope)
        if scope_id in ctx.import_scope_ids:
            continue
        delta = _lv29_scope_imports(scope, filepath, cache)
        hidden |= delta.shadowed
        scoped = _lv29_hide_exit_shadows(ctx, set(delta.shadowed))
        ctx = scoped._replace(
            sys_aliases=scoped.sys_aliases | delta.sys_aliases,
            os_aliases=scoped.os_aliases | delta.os_aliases,
            bare_exit_names=(scoped.bare_exit_names | delta.bare_exit_names),
            bare_abort_names=(
                scoped.bare_abort_names | delta.bare_abort_names),
            async_bare_exit_names=(
                scoped.async_bare_exit_names | delta.async_bare_exit_names),
            noreturn_module_attrs=(
                scoped.noreturn_module_attrs | delta.noreturn_module_attrs),
            async_noreturn_module_attrs=(
                scoped.async_noreturn_module_attrs
                | delta.async_noreturn_module_attrs),
            import_scope_ids=scoped.import_scope_ids | {scope_id},
        )
    return ctx, frozenset(hidden)
def _lv29_non_import_shadows(scope: ast.AST) -> set[str]:
    body = getattr(scope, 'body', [])
    if not isinstance(body, list):
        body = []
    names = (param_names(scope)
             if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))
             else set())
    names |= scope_definition_names(body)
    for node in scan_body_no_funcs(body):
        if isinstance(node, (ast.Import, ast.ImportFrom, ast.alias)):
            continue
        names |= bound_names(node)
    return names
def _lv29_hide_exit_shadows(ctx: _LV29FlowCtx,
                            shadowed: set[str]) -> _LV29FlowCtx:
    return ctx._replace(
        sys_aliases=ctx.sys_aliases - shadowed,
        os_aliases=ctx.os_aliases - shadowed,
        bare_exit_names=ctx.bare_exit_names - shadowed,
        bare_abort_names=ctx.bare_abort_names - shadowed,
        async_bare_exit_names=ctx.async_bare_exit_names - shadowed,
        noreturn_names=ctx.noreturn_names - shadowed,
        async_noreturn_names=ctx.async_noreturn_names - shadowed,
        noreturn_module_attrs=frozenset(
            item for item in ctx.noreturn_module_attrs
            if item.partition('.')[0] not in shadowed),
        async_noreturn_module_attrs=frozenset(
            item for item in ctx.async_noreturn_module_attrs
            if item.partition('.')[0] not in shadowed),
    )
def _lv29_is_process_exit_call(func: ast.AST, ctx: _LV29FlowCtx) -> bool:
    if not (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)):
        return False
    recv = func.value.id
    if func.attr == 'exit':
        return recv in ctx.sys_aliases
    return func.attr == '_exit' and recv in ctx.os_aliases
def _lv29_call_terminates(
        call: ast.Call, ctx: _LV29FlowCtx, *, awaited: bool,
        hard_exit_only: bool,
) -> bool:
    func = call.func
    if hard_exit_only:
        if isinstance(func, ast.Name):
            return func.id in ctx.bare_abort_names
        return (_lv29_is_process_exit_call(func, ctx)
                and isinstance(func, ast.Attribute)
                and func.attr == '_exit')
    if isinstance(func, ast.Name):
        if (func.id in ctx.noreturn_names
                or func.id in ctx.bare_exit_names
                or func.id in ctx.bare_abort_names):
            return True
        return awaited and (
            func.id in ctx.async_noreturn_names
            or func.id in ctx.async_bare_exit_names)
    if _lv29_is_process_exit_call(func, ctx):
        return True
    call_name = dotted_name(func)
    if call_name in ctx.noreturn_module_attrs:
        return True
    return awaited and call_name in ctx.async_noreturn_module_attrs
def _lv29_literal_compare_truth(
        left: ast.AST, op: ast.cmpop, right: ast.AST,
) -> bool | None:
    if not isinstance(left, ast.Constant) or not isinstance(right, ast.Constant):
        return None
    left_value, right_value = left.value, right.value
    if isinstance(op, ast.Eq):
        return left_value == right_value
    if isinstance(op, ast.NotEq):
        return left_value != right_value
    numeric = (isinstance(left_value, (int, float))
               and isinstance(right_value, (int, float)))
    same_text_type = (isinstance(left_value, type(right_value))
                      and isinstance(left_value, (str, bytes)))
    if not numeric and not same_text_type:
        return None
    if isinstance(op, ast.Lt):
        return left_value < right_value
    if isinstance(op, ast.LtE):
        return left_value <= right_value
    if isinstance(op, ast.Gt):
        return left_value > right_value
    if isinstance(op, ast.GtE):
        return left_value >= right_value
    return None

def _lv29_expression_terminates(
        expression: ast.AST, ctx: _LV29FlowCtx, *,
        hard_exit_only: bool = False, in_await: bool = False,
) -> bool:
    if isinstance(expression, ast.Await):
        in_await = True
        expression = expression.value
    if isinstance(expression, ast.Call):
        if _lv29_call_terminates(
                expression, ctx, awaited=in_await,
                hard_exit_only=hard_exit_only):
            return True
        if _lv29_expression_terminates(
                expression.func, ctx, hard_exit_only=hard_exit_only):
            return True
        operands = [*expression.args,
                    *(keyword.value for keyword in expression.keywords)]
        return any(
            _lv29_expression_terminates(
                operand, ctx, hard_exit_only=hard_exit_only)
            for operand in operands)
    if isinstance(expression, ast.BoolOp):
        continue_on = isinstance(expression.op, ast.And)
        for value in expression.values:
            if _lv29_expression_terminates(
                    value, ctx, hard_exit_only=hard_exit_only):
                return True
            truth = constant_truth(value)
            if truth is None or truth is not continue_on:
                return False
        return False
    if isinstance(expression, ast.IfExp):
        if _lv29_expression_terminates(
                expression.test, ctx, hard_exit_only=hard_exit_only):
            return True
        truth = constant_truth(expression.test)
        if truth is None:
            return (
                _lv29_expression_terminates(
                    expression.body, ctx, hard_exit_only=hard_exit_only,
                    in_await=in_await)
                and _lv29_expression_terminates(
                    expression.orelse, ctx, hard_exit_only=hard_exit_only,
                    in_await=in_await))
        branch = expression.body if truth else expression.orelse
        return _lv29_expression_terminates(
            branch, ctx, hard_exit_only=hard_exit_only, in_await=in_await)
    if isinstance(expression, _LV17_COMPREHENSION_NODES):
        return bool(expression.generators) and _lv29_expression_terminates(
            expression.generators[0].iter, ctx,
            hard_exit_only=hard_exit_only)
    if isinstance(expression, ast.Lambda):
        defaults = [*expression.args.defaults,
                    *(default for default in expression.args.kw_defaults
                      if default is not None)]
        return any(
            _lv29_expression_terminates(
                default, ctx, hard_exit_only=hard_exit_only)
            for default in defaults)
    if isinstance(expression, ast.Compare):
        left = expression.left
        if _lv29_expression_terminates(
                left, ctx, hard_exit_only=hard_exit_only):
            return True
        for op, right in zip(expression.ops, expression.comparators):
            if _lv29_expression_terminates(
                    right, ctx, hard_exit_only=hard_exit_only):
                return True
            if _lv29_literal_compare_truth(left, op, right) is not True:
                return False
            left = right
        return False
    return any(
        _lv29_expression_terminates(
            child, ctx, hard_exit_only=hard_exit_only)
        for child in ast.iter_child_nodes(expression)
        if isinstance(child, ast.expr)
    )
def _lv29_exit_call_terminates(
        stmt: ast.AST, ctx: _LV29FlowCtx, *, hard_exit_only: bool,
) -> bool:
    if isinstance(stmt, (ast.Expr, ast.Return, ast.Assign,
                         ast.AnnAssign, ast.AugAssign)):
        expression = stmt.value
    else:
        return False
    return expression is not None and _lv29_expression_terminates(
        expression, ctx, hard_exit_only=hard_exit_only)
def _lv29_loop_else_terminates(
        node: ast.For | ast.AsyncFor | ast.While,
        ctx: _LV29FlowCtx, *, allow_return: bool,
        exceptions_exit: bool) -> bool:
    if not node.orelse:
        return False
    if loop_has_binding(ctx.parents, node, ast.Break):
        return False
    return _lv29_terminate(
        node.orelse, ctx, allow_return=allow_return,
        exceptions_exit=exceptions_exit)
def _lv29_if_terminates(
        node: ast.If, ctx: _LV29FlowCtx, *, allow_return: bool,
        exceptions_exit: bool) -> bool:
    truth = constant_truth(node.test)
    if truth is not None:
        branch = node.body if truth else node.orelse
        return _lv29_terminate(
            branch, ctx, allow_return=allow_return,
            exceptions_exit=exceptions_exit)
    return (
        bool(node.orelse)
        and _lv29_terminate(
            node.body, ctx, allow_return=allow_return,
            exceptions_exit=exceptions_exit)
        and _lv29_terminate(
            node.orelse, ctx, allow_return=allow_return,
            exceptions_exit=exceptions_exit))
def _lv29_expression_exception_name(
        expression: ast.AST, ctx: _LV29FlowCtx) -> str:
    if isinstance(expression, ast.Await):
        expression = expression.value
    if not isinstance(expression, ast.Call):
        return ''
    func = expression.func
    if isinstance(func, ast.Name) and func.id in ctx.bare_exit_names:
        return 'SystemExit'
    if (_lv29_is_process_exit_call(func, ctx)
            and isinstance(func, ast.Attribute) and func.attr == 'exit'):
        return 'SystemExit'
    return ''
def _lv29_exception_covered_by_try(
        node: ast.AST, root: ast.AST, ctx: _LV29FlowCtx,
        exception_name: str) -> bool:
    name_ctx = _Lv21NameCtx(ctx.parents, {})
    cur = node
    while cur is not root:
        parent = ctx.parents.get(id(cur))
        if parent is None:
            break
        if (isinstance(parent, ast.Try)
                and any(stmt is cur for stmt in parent.body)):
            covered = tuple(
                name
                for handler in parent.handlers
                for name in _lv21_handler_names(handler, name_ctx))
            if exception_name:
                if _lv21_covered_by(exception_name, covered):
                    return True
            elif 'BaseException' in covered:
                return True
        cur = parent
    return False
def _lv29_statement_exception_name(
        stmt: ast.AST, ctx: _LV29FlowCtx) -> str | None:
    if isinstance(stmt, ast.Raise):
        if (stmt.exc is not None
                and _lv29_expression_terminates(stmt.exc, ctx)):
            if _lv29_expression_terminates(
                    stmt.exc, ctx, hard_exit_only=True):
                return None
            return _lv29_expression_exception_name(stmt.exc, ctx)
        if stmt.exc is None:
            return ''
        target = (stmt.exc.func if isinstance(stmt.exc, ast.Call)
                  else stmt.exc)
        return _lv21_type_name(
            target, _Lv21NameCtx(ctx.parents, {})) or ''
    if assert_always_fails(stmt):
        return 'AssertionError'
    if isinstance(stmt, ast.Assert) and _lv29_expression_terminates(
            stmt.test, ctx):
        if _lv29_expression_terminates(
                stmt.test, ctx, hard_exit_only=True):
            return None
        return _lv29_expression_exception_name(stmt.test, ctx)
    if _lv29_exit_call_terminates(stmt, ctx, hard_exit_only=True):
        return None
    if _lv29_exit_call_terminates(stmt, ctx, hard_exit_only=False):
        return _lv29_expression_exception_name(stmt.value, ctx)
    expressions: list[ast.AST] = []
    if isinstance(stmt, (ast.If, ast.While)):
        expressions.append(stmt.test)
    elif isinstance(stmt, (ast.For, ast.AsyncFor)):
        expressions.append(stmt.iter)
    elif isinstance(stmt, (ast.With, ast.AsyncWith)):
        expressions.extend(item.context_expr for item in stmt.items)
    elif isinstance(stmt, ast.Match):
        expressions.append(stmt.subject)
    for expression in expressions:
        if _lv29_expression_terminates(
                expression, ctx, hard_exit_only=True):
            return None
        if _lv29_expression_terminates(expression, ctx):
            return _lv29_expression_exception_name(expression, ctx)
    return None
def _lv29_statement_has_exception_exit(
        stmt: ast.AST, ctx: _LV29FlowCtx, *,
        root: ast.AST | None = None) -> bool:
    root = stmt if root is None else root
    for sub in scan_body_no_funcs([stmt]):
        exception_name = _lv29_statement_exception_name(sub, ctx)
        if (exception_name is not None
                and not _lv29_exception_covered_by_try(
                    sub, root, ctx, exception_name)):
            return True
    return False
def _lv29_call_has_unknown_exception(
        call: ast.Call, ctx: _LV29FlowCtx,
        name_ctx: _Lv21NameCtx) -> bool:
    if (_lv29_call_terminates(
            call, ctx, awaited=False, hard_exit_only=False)
            or _lv29_call_terminates(
                call, ctx, awaited=False, hard_exit_only=True)):
        return False
    func = call.func
    if isinstance(func, ast.Name):
        imported_name = _lv21_builtin_from_import_name(
            func, name_ctx, func.id)
        if _lv21_builtin_exception(imported_name) is not None:
            return False
        if (not _lv21_builtin_shadowed(func, name_ctx, func.id)
                and _lv21_builtin_exception(func.id) is not None):
            return False
    elif (isinstance(func, ast.Attribute)
          and isinstance(func.value, ast.Name)):
        receiver = func.value
        builtins_module = (
            (receiver.id == 'builtins'
             and not _lv21_builtin_shadowed(
                 receiver, name_ctx, 'builtins'))
            or _lv21_builtin_module_alias(
                receiver, name_ctx, receiver.id))
        if (builtins_module
                and _lv21_builtin_exception(func.attr) is not None):
            return False
    return True
def _lv29_statement_has_unknown_exception(
        stmt: ast.AST, ctx: _LV29FlowCtx,
        name_ctx: _Lv21NameCtx) -> bool:
    return any(
        isinstance(sub, ast.Call)
        and _lv29_call_has_unknown_exception(sub, ctx, name_ctx)
        for sub in scan_body_no_funcs([stmt]))
def _lv29_try_exception_routes(
        node: ast.Try, ctx: _LV29FlowCtx) -> tuple[set[int], bool]:
    name_ctx = _Lv21NameCtx(ctx.parents, {})
    handler_names = [
        _lv21_handler_names(handler, name_ctx) for handler in node.handlers
    ]
    reachable_handlers: set[int] = set()
    has_uncaught = False
    scope = nearest_scope(ctx.parents, node)
    for stmt in node.body:
        for sub in scan_body_no_funcs([stmt]):
            exception_name = _lv29_statement_exception_name(sub, ctx)
            if (exception_name is None and isinstance(sub, ast.stmt)
                    and _lv29_statement_has_unknown_exception(
                        sub, ctx, name_ctx)):
                exception_name = ''
            if exception_name is None:
                continue
            if (scope is not None
                    and is_statically_unreachable(sub, ctx.parents, scope)):
                continue
            if _lv29_exception_covered_by_try(
                    sub, stmt, ctx, exception_name):
                continue
            definitely_caught = False
            for index, covered in enumerate(handler_names):
                if _lv21_covered_by(exception_name, covered):
                    matched: bool | None = True
                elif (not exception_name
                      or _lv21_builtin_exception(exception_name) is None):
                    matched = None
                else:
                    matched = False
                if matched is False:
                    continue
                reachable_handlers.add(index)
                if matched is True:
                    definitely_caught = True
                    break
            if not definitely_caught:
                has_uncaught = True
    return reachable_handlers, has_uncaught
def _lv29_try_terminates(
        node: ast.Try, ctx: _LV29FlowCtx, *, allow_return: bool,
        exceptions_exit: bool) -> bool:
    if _lv29_terminate(
            node.finalbody, ctx, allow_return=allow_return,
            exceptions_exit=exceptions_exit):
        return True
    if (not exceptions_exit
            and any(_lv29_statement_has_exception_exit(stmt, ctx)
                    for stmt in node.finalbody)):
        return False
    reachable_handlers, has_uncaught = _lv29_try_exception_routes(node, ctx)
    body_complete = _lv29_terminate(
        node.body, ctx, allow_return=allow_return, exceptions_exit=True)
    normal = body_complete
    if not normal and node.orelse:
        normal = _lv29_terminate(
            node.orelse, ctx, allow_return=allow_return,
            exceptions_exit=exceptions_exit)
    if not normal or (has_uncaught and not exceptions_exit):
        return False
    return all(
        _lv29_terminate(
            node.handlers[index].body, ctx, allow_return=allow_return,
            exceptions_exit=exceptions_exit)
        for index in reachable_handlers)
def _lv29_compound_terminates(
        node: ast.AST, ctx: _LV29FlowCtx, *, allow_return: bool,
        exceptions_exit: bool) -> bool:
    if isinstance(node, ast.If):
        if _lv29_expression_terminates(
                node.test, ctx, hard_exit_only=True):
            return True
        if _lv29_expression_terminates(node.test, ctx):
            return exceptions_exit
        return _lv29_if_terminates(
            node, ctx, allow_return=allow_return,
            exceptions_exit=exceptions_exit)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        if any(_lv29_expression_terminates(
                item.context_expr, ctx, hard_exit_only=True)
               for item in node.items):
            return True
        if any(_lv29_expression_terminates(item.context_expr, ctx)
               for item in node.items):
            return exceptions_exit
        return _lv29_terminate(
            node.body, ctx, allow_return=allow_return,
            exceptions_exit=False)
    if isinstance(node, TRY_NODES):
        if isinstance(node, ast.Try):
            return _lv29_try_terminates(
                node, ctx, allow_return=allow_return,
                exceptions_exit=exceptions_exit)
        if exceptions_exit:
            return try_block_terminates(
                node, lambda stmts: _lv29_terminate(
                    stmts, ctx, allow_return=allow_return))
        if _lv29_terminate(
                node.finalbody, ctx, allow_return=allow_return,
                exceptions_exit=False):
            return True
        if any(_lv29_statement_has_exception_exit(stmt, ctx)
               for stmt in node.finalbody):
            return False
        body_has_uncaught_exception = any(
            _lv29_statement_has_exception_exit(stmt, ctx, root=node)
            for stmt in node.body)
        normal = (
            _lv29_terminate(
                node.body, ctx, allow_return=allow_return,
                exceptions_exit=not body_has_uncaught_exception)
            or (bool(node.orelse) and _lv29_terminate(
                node.orelse, ctx, allow_return=allow_return,
                exceptions_exit=False)))
        return normal and all(
            _lv29_terminate(
                handler.body, ctx, allow_return=allow_return,
                exceptions_exit=False)
            for handler in node.handlers)
    if isinstance(node, (ast.For, ast.AsyncFor)):
        if _lv29_expression_terminates(
                node.iter, ctx, hard_exit_only=True):
            return True
        if _lv29_expression_terminates(node.iter, ctx):
            return exceptions_exit
        if (isinstance(node, ast.For)
                and _lv17_statically_nonempty_iterable(node.iter)
                and not loop_has_binding(ctx.parents, node, ast.Break)
                and not loop_has_binding(ctx.parents, node, ast.Continue)
                and _lv29_terminate(
                    node.body, ctx, allow_return=allow_return,
                    exceptions_exit=exceptions_exit)):
            return True
        return _lv29_loop_else_terminates(
            node, ctx, allow_return=allow_return,
            exceptions_exit=exceptions_exit)
    if isinstance(node, ast.While):
        if _lv29_expression_terminates(
                node.test, ctx, hard_exit_only=True):
            return True
        if _lv29_expression_terminates(node.test, ctx):
            return exceptions_exit
        if (is_constant_true_while(node)
                and not loop_has_binding(ctx.parents, node, ast.Break)):
            if exceptions_exit:
                return True
            if not _lv29_statement_has_exception_exit(node, ctx):
                return True
            return _lv29_terminate(
                node.body, ctx, allow_return=allow_return,
                exceptions_exit=False)
        return _lv29_loop_else_terminates(
            node, ctx, allow_return=allow_return,
            exceptions_exit=exceptions_exit)
    if isinstance(node, ast.Match):
        if _lv29_expression_terminates(
                node.subject, ctx, hard_exit_only=True):
            return True
        if _lv29_expression_terminates(node.subject, ctx):
            return exceptions_exit
        return match_always_exits(
            node, lambda block: _lv29_terminate(
                block, ctx, allow_return=allow_return,
                exceptions_exit=exceptions_exit))
    return False
def _lv29_terminate(
        stmts: list, ctx: _LV29FlowCtx, *, allow_return: bool,
        exceptions_exit: bool = True) -> bool:
    for stmt in stmts:
        if isinstance(stmt, ast.Raise):
            return exceptions_exit
        if allow_return and isinstance(stmt, ast.Return):
            if (stmt.value is not None
                    and _lv29_expression_terminates(
                        stmt.value, ctx, hard_exit_only=True)):
                return True
            return (
                exceptions_exit or stmt.value is None
                or not _lv29_expression_terminates(stmt.value, ctx))
        if isinstance(stmt, ast.Assert):
            if _lv29_expression_terminates(
                    stmt.test, ctx, hard_exit_only=True):
                return True
            if _lv29_expression_terminates(stmt.test, ctx):
                return exceptions_exit
        if assert_always_fails(stmt):
            return exceptions_exit
        if _lv29_exit_call_terminates(
                stmt, ctx, hard_exit_only=True):
            return True
        if _lv29_exit_call_terminates(
                stmt, ctx, hard_exit_only=False):
            return exceptions_exit
        if _lv29_compound_terminates(
                stmt, ctx, allow_return=allow_return,
                exceptions_exit=exceptions_exit):
            return True
        if (not exceptions_exit
                and _lv29_statement_has_exception_exit(stmt, ctx)):
            return False
    return False
def _lv29_scope_noreturn_defs(
        scope: ast.AST, ctx: _LV29FlowCtx, filepath: Any,
        cache: dict[int, _Lv29ScopeImports],
) -> tuple[frozenset[str], frozenset[str]]:
    candidates = scope_function_defs(scope)
    active_bindings = _lv29_active_candidate_bindings(scope, candidates)
    declared = _lv29_declared_noreturn(candidates)
    sync_names, async_names = _lv29_noreturn_fixpoint(
        declared, ctx, ctx.noreturn_names, ctx.async_noreturn_names,
        all_candidates=candidates, active_bindings=active_bindings,
        allow_return=True, filepath=filepath, cache=cache)
    inferred_sync, inferred_async = _lv29_noreturn_fixpoint(
        candidates, ctx, ctx.noreturn_names | sync_names,
        ctx.async_noreturn_names | async_names,
        all_candidates=candidates, active_bindings=active_bindings,
        allow_return=False, filepath=filepath, cache=cache)
    return sync_names | inferred_sync, async_names | inferred_async
def _lv29_has_value_return(
        func: ast.AST, parents: dict[int, ast.AST]) -> bool:
    for sub in scan_body_no_funcs(func.body):
        if not isinstance(sub, ast.Return) or sub.value is None:
            continue
        if is_statically_unreachable(sub, parents, func):
            continue
        if isinstance(sub.value, ast.Constant) and sub.value.value is None:
            continue
        return True
    return False
def _lv29_constant_includes_none(node: ast.Constant) -> bool:
    if node.value is None:
        return True
    if not isinstance(node.value, str):
        return False
    return _lv29_annotation_includes_none(
        _lv29_parse_str_annotation(node.value))
def _lv29_subscript_includes_none(node: ast.Subscript) -> bool:
    base = node.value
    name = base.id if isinstance(base, ast.Name) else getattr(base, 'attr', '')
    if name == 'Optional':
        return True
    slice_node = node.slice
    elts = (slice_node.elts if isinstance(slice_node, ast.Tuple)
            else [slice_node])
    if name == 'Annotated':
        return bool(elts) and _lv29_annotation_includes_none(elts[0])
    if name == 'Literal':
        return any(isinstance(elt, ast.Constant) and elt.value is None
                   for elt in elts)
    if name != 'Union':
        return False
    return any(_lv29_annotation_includes_none(elt) for elt in elts)
def _lv29_annotation_includes_none(node: ast.AST | None) -> bool:
    if node is None:
        return False
    if isinstance(node, ast.Constant):
        return _lv29_constant_includes_none(node)
    if isinstance(node, (ast.Name, ast.Attribute)):
        name = node.id if isinstance(node, ast.Name) else node.attr
        return name in _LV29_NONE_TYPE_NAMES
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return (_lv29_annotation_includes_none(node.left)
                or _lv29_annotation_includes_none(node.right))
    if isinstance(node, ast.Subscript):
        return _lv29_subscript_includes_none(node)
    return False
def _lv29_needs_check(
        func: ast.AST, parents: dict[int, ast.AST]) -> bool:
    if _lv29_annotation_includes_none(getattr(func, 'returns', None)):
        return False
    if _body_has_yield(func):
        return False
    return _lv29_has_value_return(func, parents)
def _lv29_issue(filepath: Any, src_lines: list[str], node: ast.FunctionDef | ast.AsyncFunctionDef,
                func_name: str) -> dict[str, Any]:
    return make_issue(
        'LV-29', 'P2', _FINDING_DIMENSION, filepath, node.lineno,
        f"函数 '{func_name}' 部分分支返回值但存在隐式 None 落穿路径",
        (
            f'``{func_name}()`` 体内有返回值的分支，但存在未以 '
            f'return/raise 终止的落穿路径——该路径静默返回 None。'
            f'调用方拿到 None 继续运算（算术/下标/属性访问）时以 '
            f'TypeError/None 崩溃收场，且错误现场远离成因点，'
            f'定位成本高。值返回函数的所有路径都应显式 return。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：分支补全时遗漏了兜底路径的 return（早返回守卫'
            '写法只覆盖了部分条件）。\n'
            '修复策略：补齐所有落穿路径的显式 return——末尾加 '
            '``return None``（有意返回 None 时写明）或 ``raise '
            'ValueError(...)``（不应到达时显式失败）；if/elif '
            '链补 else 分支。\n'
            '参考标准：缺失 return 分支缺陷模式（mypy '
            '--warn-no-return 同口径）'
        ),
        'implicit-none-fallthrough',
    )
def check_LV29(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    nodes = walk_ast_nodes(tree)
    if not nodes:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    sys_aliases, os_aliases, bare_exit, bare_abort = _lv29_exit_aliases(tree)
    (imported_bare, imported_async_bare, imported_attrs,
     imported_async_attrs) = _lv29_imported_noreturn_names(tree, filepath)
    base_ctx = _LV29FlowCtx(
        parents=parents,
        sys_aliases=sys_aliases,
        os_aliases=os_aliases,
        bare_exit_names=bare_exit | imported_bare,
        bare_abort_names=bare_abort,
        noreturn_names=frozenset(),
        async_noreturn_names=frozenset(),
        async_bare_exit_names=imported_async_bare,
        noreturn_module_attrs=imported_attrs,
        async_noreturn_module_attrs=imported_async_attrs,
        import_scope_ids=frozenset({id(tree)}),
    )
    base_ctx = _lv29_hide_exit_shadows(
        base_ctx, _lv29_non_import_shadows(tree))
    scope_imports: dict[int, _Lv29ScopeImports] = {}
    top_sync, top_async = _lv29_scope_noreturn_defs(
        tree, base_ctx, filepath, scope_imports)
    scope_noreturn: dict[
        int, tuple[frozenset[str], frozenset[str]]
    ] = {id(tree): (top_sync, top_async)}
    for node in nodes:
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        lexical_scopes = _lv29_lexical_import_scopes(node, parents)
        enclosing = lexical_scopes[1] if len(lexical_scopes) > 1 else tree
        inherited_sync, inherited_async = scope_noreturn[id(enclosing)]
        scoped, _imported_shadows = _lv29_visible_import_context(
            node,
            base_ctx._replace(
                noreturn_names=inherited_sync,
                async_noreturn_names=inherited_async),
            filepath, scope_imports)
        scoped = _lv29_hide_exit_shadows(
            scoped, _lv29_non_import_shadows(node))
        local_sync, local_async = _lv29_scope_noreturn_defs(
            node, scoped, filepath, scope_imports)
        scope_noreturn[id(node)] = (
            inherited_sync | local_sync, inherited_async | local_async)
        ctx = scoped._replace(
            noreturn_names=scoped.noreturn_names | local_sync,
            async_noreturn_names=scoped.async_noreturn_names | local_async)
        if not _lv29_needs_check(node, parents):
            continue
        if _lv29_terminate(node.body, ctx, allow_return=True):
            continue
        issues.append(_lv29_issue(filepath, src_lines, node, node.name))
    return issues
def _lv18_rebinds_name(node: ast.AST, name: str,
                      parents: dict[int, ast.AST]) -> bool:
    cur = node
    parent = parents.get(id(cur))
    while parent is not None:
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            return False
        if name in assigned_names(preceding_statements(parent, cur)):
            return True
        if isinstance(parent, ast.ExceptHandler):
            if parent.name == name:
                return False
        elif construct_shadows_name(parent, name):
            return True
        cur, parent = parent, parents.get(id(parent))
    return False
def _lv18_rethrown_binding(node: ast.AST, parents: dict[int, ast.AST]) -> str:
    if not isinstance(node, ast.Raise):
        return ''
    exc = node.exc
    if not isinstance(exc, ast.Name):
        return ''
    if _lv18_rebinds_name(node, exc.id, parents):
        return ''
    cur = parents.get(id(node))
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                           ast.Lambda)):
            return ''
        if isinstance(cur, ast.ExceptHandler):
            return exc.id if cur.name == exc.id else ''
        if isinstance(cur, TRY_NODES) and any(
                stmt is node for stmt in cur.finalbody):
            return ''
        node = cur
        cur = parents.get(id(cur))
    return ''
def _lv18_issue(filepath: Any, src_lines: list[str], node: ast.Raise,
                bound_name: str) -> dict[str, Any]:
    return make_issue(
        'LV-18', 'P2', _FINDING_DIMENSION, filepath, node.lineno,
        f'except 块内 raise {bound_name} 应改裸 raise：保留完整原始栈',
        (
            f'``raise {bound_name}`` 在当前位置追加新栈帧，'
            f'traceback 起点错位为 raise 行且多一层冗余帧；'
            f'裸 ``raise`` 原样重抛当前异常，完整保留原始'
            f'调用栈与 ``__traceback__``，定位真正的异常'
            f'源头不漂移。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：其他语言「catch 后重新 throw 变量」的惯性'
            '直译；Python 中裸 raise 即为「重抛当前异常」。\n'
            '修复策略：except 块内重抛用裸 ``raise``；需要包装成'
            '新异常用 ``raise NewError(...) from e`` 保留异常链'
            '（包装形态的重抛表达式不是裸名字，本检测不参与）。\n'
            '参考标准：异常重抛语义缺陷模式'
            '（Python 语言参考 raise 语句语义）'
        ),
        'raise-bound-name-in-except',
    )
def check_LV18(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    nodes = walk_ast_nodes(tree)
    if not nodes:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    for node in nodes:
        bound_name = _lv18_rethrown_binding(node, parents)
        if not bound_name:
            continue
        issues.append(_lv18_issue(filepath, src_lines, node, bound_name))
    return issues
def _lv20_issue(filepath: Any, src_lines: list[str],
                lineno: int) -> dict[str, Any]:
    return make_issue(
        'LV-20', 'P1', _FINDING_DIMENSION, filepath, lineno,
        'finally 块内 return：吞掉 try 的异常与返回值',
        (
            'finally 中的 return 会静默吞掉 try 块 pending '
            '的一切——try 内抛出的异常被丢弃（调用方拿不到'
            '异常也拿不到 except 分支的处理结果），try/'
            'except 已计算的返回值被 finally 的返回值覆盖。'
            '异常凭空消失、排查方向被彻底误导，是控制流'
            '缺陷中最隐蔽的一类（Python 语言参考 finally 语义）。'
        ),
        snippet_of(src_lines, lineno),
        (
            '根因：把 finally 当作「收尾兜底出口」书写，'
            '误以为 finally 的 return 是降级兜底——实际它'
            '是无条件覆盖。\n'
            '修复策略：finally 只做清理（关闭资源/解锁/'
            '打点），return 全部放 try/except 分支；需要'
            '「无论成败都返回默认值」语义时，在 try/'
            'except 里显式写 return，finally 保持空返回。\n'
            '参考标准：Python 语言参考 finally 语义'
            '（return/break/continue 在 finally 中的'
            '异常丢弃行为）'
        ),
        'finally-return-swallows',
    )
def _lv20_return_lines_in_finally(root: ast.AST) -> list[int]:
    lines: list[int] = []
    stack: list[ast.AST] = [root]
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.Return):
            lines.append(cur.lineno)
            continue
        if isinstance(cur, FUNC_SCOPE_NODES):
            continue
        if isinstance(cur, TRY_NODES):
            stack.extend(cur.body)
            stack.extend(cur.orelse)
            for handler in cur.handlers:
                stack.extend(handler.body)
            continue
        stack.extend(ast.iter_child_nodes(cur))
    return sorted(lines)
def check_LV20(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    for node in walk_ast_nodes(tree):
        if not isinstance(node, TRY_NODES):
            continue
        for final_stmt in node.finalbody:
            issues.extend(
                _lv20_issue(filepath, src_lines, lineno)
                for lineno in _lv20_return_lines_in_finally(final_stmt)
            )
    return issues
def _lv21_source_position(node: ast.AST) -> tuple[int, int]:
    return (getattr(node, 'lineno', 0) or 0,
            getattr(node, 'col_offset', 0) or 0)
def _lv21_is_builtin_import(node: ast.AST, name: str) -> bool:
    if isinstance(node, ast.Import):
        return any((alias.asname or alias.name.split('.')[0]) == name
                   and alias.name == 'builtins' for alias in node.names)
    if isinstance(node, ast.ImportFrom):
        return any((alias.asname or alias.name) == name
                   and node.module == 'builtins'
                   and alias.name in _LV21_KNOWN_BUILTIN_NAMES
                   for alias in node.names)
    return False
def _lv21_scope_binding_events(
        scope: ast.AST,
) -> dict[str, tuple[tuple[tuple[int, int], bool], ...]]:
    events: dict[str, list[tuple[tuple[int, int], bool]]] = {}
    def add(node: ast.AST, name: str) -> None:
        events.setdefault(name, []).append((
            binding_evaluation_position(node),
            _lv21_is_builtin_import(node, name)))
    if isinstance(scope, FUNC_SCOPE_NODES):
        position = _lv21_source_position(scope)
        for name in param_names(scope):
            events.setdefault(name, []).append((position, False))
    for stmt, _in_handler in iter_scope_statements(scope, include_defs=True):
        is_definition = isinstance(
            stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        for binding_node, name, _value in iter_binding_entries([stmt]):
            if binding_node is stmt or is_definition:
                add(binding_node, name)
        if is_definition:
            add(stmt, stmt.name)
    return {name: tuple(items) for name, items in events.items()}
class _Lv21NameCtx(NamedTuple):
    parents: dict[int, ast.AST]
    shadow_cache: dict[
        int, dict[str, tuple[tuple[tuple[int, int], bool], ...]]]
def _lv21_latest_direct_builtin_import(
        scope: ast.AST, name: str,
        events: tuple[tuple[tuple[int, int], bool], ...],
        cutoff: tuple[int, int]) -> bool:
    before = [(pos, is_builtin) for pos, is_builtin in events
              if pos < cutoff]
    if not before:
        return False
    latest = max(pos for pos, _is_builtin in before)
    if not any(is_builtin and pos == latest for pos, is_builtin in before):
        return False
    return any(
        binding_evaluation_position(stmt) == latest
        and _lv21_is_builtin_import(stmt, name)
        for stmt in getattr(scope, 'body', []))
def _lv21_builtin_shadowed(
        node: ast.AST, ctx: _Lv21NameCtx, name: str) -> bool:
    cutoff = _lv21_source_position(node)
    for scope in scope_chain(ctx.parents, node):
        key = id(scope)
        if key not in ctx.shadow_cache:
            ctx.shadow_cache[key] = _lv21_scope_binding_events(scope)
        events = ctx.shadow_cache[key].get(name, ())
        before = [is_builtin for pos, is_builtin in events if pos < cutoff]
        if any(not is_builtin for is_builtin in before):
            return not _lv21_latest_direct_builtin_import(
                scope, name, events, cutoff)
        if before:
            continue
        if (events and isinstance(scope, (ast.FunctionDef,
                                         ast.AsyncFunctionDef, ast.Lambda))):
            return True
    return False
def _lv21_builtin_module_alias(
        node: ast.AST, ctx: _Lv21NameCtx, name: str) -> bool:
    if _lv21_builtin_shadowed(node, ctx, name):
        return False
    for scope in scope_chain(ctx.parents, node):
        for stmt, _in_handler in iter_scope_statements(scope):
            if (not isinstance(stmt, ast.Import)
                    or binding_evaluation_position(stmt)
                    >= _lv21_source_position(node)):
                continue
            for alias in stmt.names:
                local = alias.asname or alias.name.split('.')[0]
                if alias.name == 'builtins' and local == name:
                    return True
    return False
def _lv21_builtin_from_import_name(
        node: ast.AST, ctx: _Lv21NameCtx, name: str) -> str:
    if _lv21_builtin_shadowed(node, ctx, name):
        return ''
    for scope in scope_chain(ctx.parents, node):
        for stmt, _in_handler in iter_scope_statements(scope):
            if (not isinstance(stmt, ast.ImportFrom) or stmt.module != 'builtins'
                    or binding_evaluation_position(stmt)
                    >= _lv21_source_position(node)):
                continue
            for alias in stmt.names:
                if ((alias.asname or alias.name) == name
                        and alias.name in _LV21_KNOWN_BUILTIN_NAMES):
                    return alias.name
    return ''
def _lv21_type_name(
        exc_type: ast.AST | None, ctx: _Lv21NameCtx) -> str | None:
    if isinstance(exc_type, ast.Name):
        name = exc_type.id
        imported_name = _lv21_builtin_from_import_name(exc_type, ctx, name)
        if imported_name:
            return imported_name
        if (name in _LV21_KNOWN_BUILTIN_NAMES
                and _lv21_builtin_shadowed(exc_type, ctx, name)):
            return None
        return name
    if isinstance(exc_type, ast.Attribute):
        receiver = exc_type.value
        if isinstance(receiver, ast.Name) and receiver.id == 'builtins':
            if _lv21_builtin_shadowed(exc_type, ctx, 'builtins'):
                return None
            return exc_type.attr
        if (isinstance(receiver, ast.Name)
                and _lv21_builtin_module_alias(exc_type, ctx, receiver.id)):
            return exc_type.attr
    return None
def _lv21_type_names(
        exc_type: ast.AST | None, ctx: _Lv21NameCtx) -> tuple[str, ...]:
    if isinstance(exc_type, ast.Tuple):
        names: list[str] = []
        for elt in exc_type.elts:
            if isinstance(elt, ast.Tuple):
                continue
            names.extend(_lv21_type_names(elt, ctx))
        return tuple(names)
    name = _lv21_type_name(exc_type, ctx)
    return (name,) if name is not None else ()
def _lv21_resolved_names(
        exc_type: ast.AST | None,
        ctx: _Lv21NameCtx) -> tuple[str, ...] | None:
    if isinstance(exc_type, ast.Tuple):
        names: list[str] = []
        for elt in exc_type.elts:
            if isinstance(elt, ast.Tuple):
                return None
            sub = _lv21_resolved_names(elt, ctx)
            if sub is None:
                return None
            names.extend(sub)
        return tuple(names)
    name = _lv21_type_name(exc_type, ctx)
    return (name,) if name is not None else None
def _lv21_type_display(exc_type: ast.AST | None, ctx: _Lv21NameCtx) -> str:
    if exc_type is None:
        return 'bare except'
    try:
        return ast.unparse(exc_type)
    except (AttributeError, ValueError) as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_lv21_type_display:unparse')
        return ' / '.join(_lv21_type_names(exc_type, ctx)) or '?'
def _lv21_builtin_exception(name: str) -> type | None:
    if name not in _LV21_EXC_CLASSES:
        candidate = getattr(builtins, name, None)
        _LV21_EXC_CLASSES[name] = (
            candidate
            if isinstance(candidate, type)
            and issubclass(candidate, BaseException)
            else None)
    return _LV21_EXC_CLASSES[name]
def _lv21_handler_names(
        handler: ast.ExceptHandler, ctx: _Lv21NameCtx) -> tuple[str, ...]:
    if handler.type is None:
        return ('BaseException',)
    return _lv21_resolved_names(handler.type, ctx) or ()
def _lv21_covered_by(name: str, covered: tuple[str, ...]) -> bool:
    if name in covered:
        return True
    name_cls = _lv21_builtin_exception(name)
    for broad in covered:
        broad_cls = _lv21_builtin_exception(broad)
        if broad_cls is None:
            continue
        if name_cls is None:
            if broad_cls is BaseException:
                return True
            continue
        if issubclass(name_cls, broad_cls):
            return True
    return False
def _lv21_dead_branch(
        handlers: list[ast.ExceptHandler],
        ctx: _Lv21NameCtx,
) -> tuple[ast.ExceptHandler, str, str] | None:
    covered: list[str] = []
    for idx, handler in enumerate(handlers[:-1]):
        covered.extend(_lv21_handler_names(handler, ctx))
        if not covered:
            continue
        dead = [
            _lv21_type_display(later.type, ctx)
            for later in handlers[idx + 1:]
            if (later_names := _lv21_handler_names(later, ctx))
            and all(_lv21_covered_by(name, tuple(covered))
                    for name in later_names)
        ]
        if dead:
            label = ('BaseException (bare except)'
                     if handler.type is None
                     else _lv21_type_display(handler.type, ctx))
            return (handler, label, ' / '.join(dead))
    return None
def _lv21_issue(filepath: Any, src_lines: list[str],
                handler: ast.ExceptHandler, broad_name: str,
                dead_desc: str) -> dict[str, Any]:
    return make_issue(
        'LV-21', 'P2', _FINDING_DIMENSION, filepath, handler.lineno,
        f'宽捕获在前：except {broad_name} 之后的分支永不可达',
        (
            f'``except {broad_name}:`` 之后的 handler（{dead_desc}）'
            f'永不可达——宽分支按声明序先匹配，后续具体异常分支'
            f'成为死代码：其中的重试/'
            f'降级/默认值逻辑静默失效，处理意图与实际行为背离'
            f'且无任何告警。'
        ),
        snippet_of(src_lines, handler.lineno),
        (
            '根因：handler 书写顺序按「兜底在前」直觉排列，'
            '违背「具体在前、宽泛殿后」的匹配序。\n'
            '修复策略：把具体异常分支移到宽捕获之前'
            '（``except ValueError: ... except Exception: ...``）；'
            '宽捕获只作最后兜底并保持最小处理面（记录日志 + '
            '重抛或聚合），不吞异常；需要捕 SystemExit 等 Base '
            '级异常时显式写在 Base 级补充分支。\n'
            '参考标准：Python 语言参考 except 子句按序匹配'
            '语义'
        ),
        'broad-except-first-dead-branch',
    )
def check_LV21(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    parents = parent_map_of(tree) if isinstance(tree, ast.AST) else {}
    ctx = _Lv21NameCtx(parents, {})
    for node in walk_ast_nodes(tree):
        if not isinstance(node, ast.Try):
            continue
        found = _lv21_dead_branch(node.handlers, ctx)
        if found is None:
            continue
        handler, broad_name, dead_desc = found
        issues.append(
            _lv21_issue(filepath, src_lines, handler, broad_name, dead_desc))
    return issues
def _lv32_generic_raise_name(
        node: ast.AST, ctx: _Lv21NameCtx) -> str:
    if not isinstance(node, ast.Raise) or node.exc is None:
        return ''
    target = node.exc.func if isinstance(node.exc, ast.Call) else node.exc
    name = _lv21_type_name(target, ctx)
    return name if name in _GENERIC_EXC_ROOT_NAMES else ''
def _lv32_issue(filepath: Any, src_lines: list[str], node: ast.Raise,
                generic_name: str) -> dict[str, Any]:
    return make_issue(
        'LV-32', 'P2', _FINDING_DIMENSION, filepath, node.lineno,
        f'raise {generic_name} 泛化异常：调用方的具体异常分支永不可达',
        (
            f'``raise {generic_name}(...)`` 抛出泛化基类——调用方的 '
            f'``except ValueError:`` 等具体异常分支永不匹配，'
            f'按异常类型分流处理的防御逻辑整体旁路；BaseException '
            f'更会穿透 ``except Exception:`` 兜底直达进程顶层。'
            f'异常类型是调用方与被调方的隐式契约，泛化抛出等于'
            f'契约作废。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：按「报错即可」直觉抛最宽基类，异常类型未按'
            '失败成因建模。\n'
            '修复策略：按成因抛具体子类——值非法用 '
            '``ValueError``、状态错误用 ``RuntimeError``/自定义'
            '异常、参数缺失用 ``TypeError``/``KeyError``；需要'
            '调用方统一处理时定义领域异常基类（``class '
            'ConfigError(Exception)``）再抛其子类。\n'
            '参考标准：异常契约失效缺陷模式（Python 语言参考 '
            'except 子句按类型匹配语义）'
        ),
        'raise-generic-exception',
    )
def check_LV32(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    src_lines = source_lines(source)
    parents = parent_map_of(tree) if isinstance(tree, ast.AST) else {}
    ctx = _Lv21NameCtx(parents, {})
    for node in walk_ast_nodes(tree):
        generic_name = _lv32_generic_raise_name(node, ctx)
        if not generic_name:
            continue
        issues.append(_lv32_issue(filepath, src_lines, node, generic_name))
    return issues

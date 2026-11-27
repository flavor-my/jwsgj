from __future__ import annotations

import ast
import logging
from typing import Any
from weakref import WeakKeyDictionary

from jwsgj.diag_shared_ast_nodes import iter_def_site_nodes
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import (
    FUNC_SCOPE_NODES,
    TRY_NODES,
    binding_entries_index,
    capture_binding_names,
    definition_outer_node_ids,
    import_bound_names,
    int_literal,
    iter_nodes_outside,
    make_issue,
    nearest_scope,
    node_end_position,
    param_names,
    parent_map_of,
    shadowed_binding_at,
    snippet_of,
    source_lines,
    target_binding_names,
    walk_ast_nodes,
    walk_nodes,
)

__all__ = [
    'check_LV10',
    'check_LV39',
    'check_LV54',
    'check_LV56',
    'check_LV59',
]
_log = logging.getLogger(__name__)
_log.info("prevention_gen_checks 生成器与调用产物消费域已加载：%d 项导出", len(__all__))
_EMPTY_NAMES: frozenset[str] = frozenset()
_EMPTY_IDS: frozenset[int] = frozenset()
_LV10_CALL_SHADOWS: WeakKeyDictionary[ast.Call, bool] = WeakKeyDictionary()
class _LV10RefExclusions(set[int]):
    def __init__(self, truthy_names: frozenset[str] = _EMPTY_NAMES) -> None:
        super().__init__()
        self.truthy_names = truthy_names
_LV10_SCOPE_CONTAINERS = (ast.Module, *FUNC_SCOPE_NODES)
def check_LV10(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    roots = walk_ast_nodes(tree)
    if not roots:
        return []
    _lv10_prepare_builtin_call_shadows(roots, tree)
    src_lines = source_lines(source)
    issues: list[dict[str, Any]] = []
    for container in roots:
        if not isinstance(container, _LV10_SCOPE_CONTAINERS):
            continue
        try:
            reports = _lv10_container_reports(container)
        except RecursionError as _swallow_e:
            log_swallowed(
                __name__, _swallow_e,
                context='check_LV10:RecursionError')
            continue
        issues.extend(
            _lv10_issue(filepath, src_lines, *report)
            for report in reports
        )
    return issues
def _lv10_container_reports(
        container: ast.AST) -> list[tuple[str, int, int]]:
    tracker = _LV10GenGroupTracker()
    if isinstance(container, ast.Lambda):
        _lv10_record_expr_eval(
            tracker, container.body, container.lineno, ctx=_LV10_CTX_VALUE)
    else:
        for stmt in _lv10_reachable_stmts(container.body):
            _lv10_process_stmt(tracker, stmt)
    return tracker.reports()
def _lv10_issue(filepath: Any, src_lines: list[str], member: str,
                first_line: int, second_line: int) -> dict[str, Any]:
    return make_issue(
        'LV-10', 'P1', 'resource_lifetime', filepath, second_line,
        f'生成器 {member} 被二次消费：后一次迭代缺失元素',
        (
            f'``{member}`` 是生成器表达式（单次消费），行 '
            f'{first_line} 的首次消费已推进（或耗尽）它：行 '
            f'{second_line} 的再次迭代/统计只能拿到剩余序列——'
            '整体耗尽时恒为空序列，部分推进时（``next``/``send``）'
            '缺前段元素，计数与聚合结果静默失真，无任何异常信号。'
        ),
        snippet_of(src_lines, second_line),
        (
            '根因：生成器的单次消费语义与「多次统计」意图叠加。\n'
            f'修复策略：把 ``{member}`` 物化为列表（``{member} = [...]`` '
            f'列表推导式）再多次消费；或每段统计独立构建生成器；'
            '单遍聚合用 ``for`` 循环同时累计多个统计量。\n'
            '参考标准：Python 生成器迭代协议——生成器耗尽后'
            '不会自动重置'
        ),
        'generator-double-consumption',
    )
# async 生成器（async def + yield）的带值 return 同样落入
# StopAsyncIteration.value，async for 协议不读取该值，与同步生成器同源
_LV59_GENERATOR_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef)
def _lv59_own_scope_stmts(
        node: ast.FunctionDef | ast.AsyncFunctionDef) -> list[ast.AST]:
    return [
        cur
        for stmt in node.body
        for cur in iter_nodes_outside(stmt)
    ]
def _lv59_is_none_expr(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return node.value is None
    if isinstance(node, ast.NamedExpr):
        return _lv59_is_none_expr(node.value)
    if not isinstance(node, ast.IfExp):
        return False
    truth = _lv10_static_truth_value(node.test)
    if truth is True:
        return _lv59_is_none_expr(node.body)
    if truth is False:
        return _lv59_is_none_expr(node.orelse)
    return (_lv59_is_none_expr(node.body)
            and _lv59_is_none_expr(node.orelse))
def _lv59_is_valued_return(node: ast.AST) -> bool:
    return (isinstance(node, ast.Return) and node.value is not None
            and not _lv59_is_none_expr(node.value))
def _lv59_valued_returns(own: list[ast.AST]) -> list[ast.Return]:
    if not any(isinstance(x, (ast.Yield, ast.YieldFrom)) for x in own):
        return []
    return [x for x in own if _lv59_is_valued_return(x)]
def _lv59_reachable_return_ids(
        node: ast.FunctionDef | ast.AsyncFunctionDef) -> set[int]:
    reachable: set[int] = set()
    def visit_stmts(stmts: list[ast.stmt]) -> None:
        for stmt in _lv10_reachable_stmts(stmts):
            if isinstance(stmt, ast.Return):
                reachable.add(id(stmt))
            if isinstance(stmt, FUNC_SCOPE_NODES):
                continue
            if isinstance(stmt, ast.If):
                for branch in _lv10_if_branch_bodies(stmt):
                    visit_stmts(branch)
            elif isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
                if _lv10_loop_execution_kind(stmt) != _LV10_LOOP_NEVER:
                    visit_stmts(stmt.body)
                if _lv10_loop_else_reachable(stmt):
                    visit_stmts(stmt.orelse)
            elif isinstance(stmt, TRY_NODES):
                visit_stmts(stmt.body)
                if _lv10_try_else_reachable(stmt):
                    visit_stmts(stmt.orelse)
                for handler in stmt.handlers:
                    visit_stmts(handler.body)
                visit_stmts(stmt.finalbody)
            elif (_LV10_MATCH_TYPE is not None
                  and isinstance(stmt, _LV10_MATCH_TYPE)):
                for case in _lv10_match_reachable_cases(stmt):
                    visit_stmts(case.body)
            else:
                for field in ('body', 'orelse', 'finalbody'):
                    visit_stmts(getattr(stmt, field, ()))
                for handler in getattr(stmt, 'handlers', ()):
                    visit_stmts(handler.body)
                for case in getattr(stmt, 'cases', ()):
                    visit_stmts(case.body)
            if _lv10_stmt_exits(stmt):
                break
    visit_stmts(node.body)
    return reachable
def _lv59_issue(filepath: Any, src_lines: list[str],
                node: ast.FunctionDef | ast.AsyncFunctionDef,
                ret: ast.Return) -> dict[str, Any]:
    _is_async_gen = isinstance(node, ast.AsyncFunctionDef)
    _stop_exc = 'StopAsyncIteration' if _is_async_gen else 'StopIteration'
    _consumer = ('``async for x in gen()``'
                 if _is_async_gen else '``for x in gen()``/``list(gen())``')
    return make_issue(
        'LV-59', 'P2', 'logic_correctness', filepath, ret.lineno,
        f'{"async " if _is_async_gen else ""}生成器函数 ``{node.name}`` '
        f'带值 return：值经 {_stop_exc}.value 静默吞没',
        (
            f'``{node.name}`` 是{"async " if _is_async_gen else ""}生成器函数'
            '（含 yield）——带值'
            ' return 不走函数返回值通道，值装入 '
            f'{_stop_exc}.'
            f'value：{_consumer} 等常规'
            '消费方整体丢弃该值（仅 ``yield from`` 委托链才能'
            '捕获），调用方读到的是 None/空，且无异常信号。'
        ),
        snippet_of(src_lines, ret.lineno),
        (
            '根因：生成器的产出协议是 yield 序列；return 值\n'
            '是协议结尾信号（PEP 380），不是数据通道。\n'
            '修复策略：把 ``return value`` 改为 ``yield value``\n'
            '（并入产出序列）；确需链路传出累计值时改非生成\n'
            '器函数收集后 return。\n'
            '参考标准：PEP 380 StopIteration.value 语义——\n'
            '常规迭代协议不读该值'
        ),
        'generator-return-value-dropped',
    )
_LV59_PROTOCOL_VALUE_READERS = frozenset({'__await__'})
def _lv59_protocol_value_reader_ids(tree: ast.AST) -> set[int]:
    readers: set[int] = set()
    for cls in walk_nodes(tree):
        if not isinstance(cls, ast.ClassDef):
            continue
        for stmt in cls.body:
            for node in _lv10_scope_def_nodes(stmt):
                if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                        and node.name in _LV59_PROTOCOL_VALUE_READERS):
                    readers.add(id(node))
    return readers
def _lv59_finally_suppressed_return_ids(tree: ast.AST) -> set[int]:
    suppressed: set[int] = set()
    for node in walk_nodes(tree):
        if not (isinstance(node, TRY_NODES) and node.finalbody
                and _lv10_block_exits(node.finalbody)):
            continue
        regions = [node.body, node.orelse]
        regions.extend(handler.body for handler in node.handlers)
        for region in regions:
            for stmt in region:
                for sub in iter_nodes_outside(stmt):
                    if isinstance(sub, ast.Return):
                        suppressed.add(id(sub))
    return suppressed
def check_LV59(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    roots = walk_ast_nodes(tree)
    if not roots:
        return []
    src_lines = source_lines(source)
    issues: list[dict[str, Any]] = []
    protocol_readers = _lv59_protocol_value_reader_ids(tree)
    suppressed_returns = _lv59_finally_suppressed_return_ids(tree)
    for node in roots:
        if not isinstance(node, _LV59_GENERATOR_SCOPE_TYPES):
            continue
        if id(node) in protocol_readers:
            continue
        reachable = _lv59_reachable_return_ids(node)
        for ret in _lv59_valued_returns(_lv59_own_scope_stmts(node)):
            if id(ret) not in reachable or id(ret) in suppressed_returns:
                continue
            issues.append(_lv59_issue(filepath, src_lines, node, ret))
    return issues
_LV10_CTX_CONSUME = 0
_LV10_CTX_VALUE = 1
_LV10_CTX_TRUTHY = 2
_LV10_MATCH_TYPE = getattr(ast, 'Match', None)
_MATCH_VALUE_T = getattr(ast, 'MatchValue', None)
_MATCH_SEQ_T = getattr(ast, 'MatchSequence', None)
_MATCH_MAPPING_T = getattr(ast, 'MatchMapping', None)
_MATCH_CLASS_T = getattr(ast, 'MatchClass', None)
_MATCH_AS_T = getattr(ast, 'MatchAs', None)
_MATCH_OR_T = getattr(ast, 'MatchOr', None)
_TYPE_ALIAS_T = getattr(ast, 'TypeAlias', None)
_PATTERN_EVAL_ATTRS: tuple[tuple[type, str], ...] = tuple(
    (pattern_type, attr)
    for pattern_type, attr in (
        (_MATCH_VALUE_T, 'value'),
        (_MATCH_MAPPING_T, 'keys'),
        (_MATCH_CLASS_T, 'cls'),
    )
    if pattern_type is not None
)
_PATTERN_CHILD_ATTRS: tuple[tuple[type, tuple[str, ...]], ...] = tuple(
    (pattern_type, attrs)
    for pattern_type, attrs in (
        (_MATCH_MAPPING_T, ('patterns',)),
        (_MATCH_CLASS_T, ('patterns', 'kwd_patterns')),
        (_MATCH_SEQ_T, ('patterns',)),
        (_MATCH_AS_T, ('pattern',)),
        (_MATCH_OR_T, ('patterns',)),
    )
    if pattern_type is not None
)
def _pattern_attr_items(value: Any):
    if value is None:
        return ()
    if isinstance(value, list):
        return tuple(v for v in value if v is not None)
    return (value,)
def _pattern_eval_exprs(pattern: ast.AST):
    for pattern_type, attr in _PATTERN_EVAL_ATTRS:
        if isinstance(pattern, pattern_type):
            yield from _pattern_attr_items(getattr(pattern, attr))
            return
def _pattern_sub_patterns(pattern: ast.AST):
    for pattern_type, attrs in _PATTERN_CHILD_ATTRS:
        if not isinstance(pattern, pattern_type):
            continue
        for attr in attrs:
            yield from _pattern_attr_items(getattr(pattern, attr))
        return
def _lv10_pattern_capture_names(pattern: ast.AST | None) -> set[str]:
    names: set[str] = set()
    if pattern is None:
        return names
    names |= capture_binding_names(pattern)
    for sub in _pattern_sub_patterns(pattern):
        names |= _lv10_pattern_capture_names(sub)
    return names
def _lv10_iter_pattern_exprs(pattern: ast.AST | None):
    if pattern is None:
        return
    yield from _pattern_eval_exprs(pattern)
    for sub in _pattern_sub_patterns(pattern):
        yield from _lv10_iter_pattern_exprs(sub)
def _lv10_expression_truth(
        node: ast.AST, truthy_names: frozenset[str]) -> bool | None:
    if isinstance(node, ast.NamedExpr):
        return _lv10_expression_truth(node.value, truthy_names)
    if isinstance(node, ast.Name) and node.id in truthy_names:
        return True
    return _lv10_static_truth_value(node)
def _ectx_exclude_unreachable(node: ast.AST, excluded: set[int]) -> None:
    for sub in walk_nodes(node):
        excluded.add(id(sub))
def _ectx_boolflow(node: ast.AST, ctx: int, excluded: set[int]) -> bool:
    truthy_names = getattr(excluded, 'truthy_names', _EMPTY_NAMES)
    if isinstance(node, ast.BoolOp):
        unreachable = False
        last_index = len(node.values) - 1
        for index, value in enumerate(node.values):
            if unreachable:
                _ectx_exclude_unreachable(value, excluded)
                continue
            if index == last_index:
                _lv10_expr_ctx(value, ctx, excluded)
                continue
            truth = _lv10_expression_truth(value, truthy_names)
            stops = ((isinstance(node.op, ast.Or) and truth is True)
                     or (isinstance(node.op, ast.And) and truth is False))
            value_ctx = (_LV10_CTX_TRUTHY
                         if truth is not None and not stops else ctx)
            _lv10_expr_ctx(value, value_ctx, excluded)
            unreachable = stops
        return True
    if isinstance(node, ast.IfExp):
        _lv10_expr_ctx(node.test, _LV10_CTX_TRUTHY, excluded)
        truth = _lv10_expression_truth(node.test, truthy_names)
        if truth is None:
            _lv10_expr_ctx(node.body, ctx, excluded)
            _lv10_expr_ctx(node.orelse, ctx, excluded)
            return True
        selected = node.body if truth else node.orelse
        unreachable = node.orelse if truth else node.body
        _lv10_expr_ctx(selected, ctx, excluded)
        _ectx_exclude_unreachable(unreachable, excluded)
        return True
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        _lv10_expr_ctx(node.operand, _LV10_CTX_TRUTHY, excluded)
        return True
    return False
def _ectx_containers(node: ast.AST, excluded: set[int]) -> bool:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        for e in node.elts:
            if isinstance(e, ast.Starred):
                _lv10_expr_ctx(e.value, _LV10_CTX_CONSUME, excluded)
            else:
                _lv10_expr_ctx(e, _LV10_CTX_VALUE, excluded)
        return True
    if isinstance(node, ast.Dict):
        for k, v in zip(node.keys, node.values, strict=False):
            if k is None:
                _lv10_expr_ctx(v, _LV10_CTX_CONSUME, excluded)
            else:
                _lv10_expr_ctx(k, _LV10_CTX_VALUE, excluded)
                _lv10_expr_ctx(v, _LV10_CTX_VALUE, excluded)
        return True
    if isinstance(node, ast.Starred):
        _lv10_expr_ctx(node.value, _LV10_CTX_CONSUME, excluded)
        return True
    return False
def _ectx_defs(node: ast.AST, ctx: int, excluded: set[int]) -> bool:
    if isinstance(node, ast.NamedExpr):
        _lv10_expr_ctx(node.value, ctx, excluded)
        return True
    if isinstance(node, ast.YieldFrom):
        if node.value is not None:
            _lv10_expr_ctx(node.value, _LV10_CTX_CONSUME, excluded)
        return True
    if isinstance(node, ast.Yield):
        if node.value is not None:
            _lv10_expr_ctx(node.value, _LV10_CTX_VALUE, excluded)
        return True
    if isinstance(node, ast.Lambda):
        for sub in walk_nodes(node.body):
            excluded.add(id(sub))
        for expr in iter_def_site_nodes(node):
            _lv10_expr_ctx(expr, _LV10_CTX_VALUE, excluded)
        return True
    return False
def _lv10_exclude_comprehension_loads(
        node: ast.AST, names: set[str], excluded: set[int]) -> None:
    if not names:
        return
    for sub in walk_nodes(node):
        if (isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
                and sub.id in names):
            excluded.add(id(sub))
def _ectx_gen_comps(node: ast.AST, ctx: int, excluded: set[int]) -> bool:
    if isinstance(node, ast.GeneratorExp) and ctx != _LV10_CTX_CONSUME:
        outer_iter = node.generators[0].iter
        outer_excluded = _LV10RefExclusions(
            getattr(excluded, 'truthy_names', _EMPTY_NAMES))
        _lv10_expr_ctx(outer_iter, _LV10_CTX_VALUE, outer_excluded)
        for sub in walk_nodes(node):
            excluded.add(id(sub))
        for sub in walk_nodes(outer_iter):
            if (isinstance(sub, ast.Name)
                    and isinstance(sub.ctx, ast.Load)
                    and id(sub) not in outer_excluded):
                excluded.discard(id(sub))
        return True
    if isinstance(node, ast.DictComp):
        result_exprs = (node.key, node.value)
    elif isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
        result_exprs = (node.elt,)
    else:
        return False
    target_names = {
        name
        for comp in node.generators
        for name in target_binding_names(comp.target)
    }
    for expr in result_exprs:
        _lv10_exclude_comprehension_loads(expr, target_names, excluded)
        _lv10_expr_ctx(expr, _LV10_CTX_VALUE, excluded)
    bound_names: set[str] = set()
    for comp in node.generators:
        _lv10_exclude_comprehension_loads(comp.iter, bound_names, excluded)
        _lv10_expr_ctx(comp.iter, _LV10_CTX_CONSUME, excluded)
        bound_names.update(target_binding_names(comp.target))
        for cond in comp.ifs:
            _lv10_exclude_comprehension_loads(cond, bound_names, excluded)
            _lv10_expr_ctx(cond, _LV10_CTX_TRUTHY, excluded)
    return True
def _ectx_fmt_cmp(node: ast.AST, excluded: set[int]) -> bool:
    if isinstance(node, ast.FormattedValue):
        _lv10_expr_ctx(node.value, _LV10_CTX_VALUE, excluded)
        if node.format_spec is not None:
            _lv10_expr_ctx(node.format_spec, _LV10_CTX_CONSUME,
                           excluded)
        return True
    if isinstance(node, ast.Compare):
        _lv10_expr_ctx(node.left, _LV10_CTX_VALUE, excluded)
        for op, right in zip(node.ops, node.comparators, strict=False):
            if isinstance(op, (ast.In, ast.NotIn)):
                _lv10_expr_ctx(right, _LV10_CTX_CONSUME, excluded)
            else:
                _lv10_expr_ctx(right, _LV10_CTX_VALUE, excluded)
        return True
    return False
def _lv10_expr_ctx(node: ast.AST, ctx: int,
                   excluded: set[int]) -> None:
    if isinstance(node, ast.Name):
        if ctx != _LV10_CTX_CONSUME:
            excluded.add(id(node))
        return
    if _ectx_boolflow(node, ctx, excluded):
        return
    if _ectx_containers(node, excluded):
        return
    if _ectx_defs(node, ctx, excluded):
        return
    if _ectx_gen_comps(node, ctx, excluded):
        return
    if _ectx_fmt_cmp(node, excluded):
        return
    _expr_ctx_consume_children(node, excluded, ctx)
_LV10_OBSERVE_BUILTINS = frozenset({
    'print', 'len', 'bool', 'repr', 'str', 'id', 'type',
    'hash', 'isinstance', 'issubclass', 'callable', 'vars', 'dir',
    'format', 'ascii',
})
_LV10_LAZY_ITERATOR_BUILTINS = frozenset({
    'iter', 'map', 'filter', 'enumerate', 'zip',
})
_LV10_GEN_DRIVER_ATTRS = frozenset({'send', 'throw', 'close', '__next__'})
def _lv10_call_arg_ctx(func: ast.expr, ctx: int,
                       position: int | None, *, shadowed: bool = False) -> int:
    if isinstance(func, ast.Name) and shadowed:
        return _LV10_CTX_CONSUME
    if isinstance(func, ast.Name) and func.id == 'iter' and position != 0:
        return _LV10_CTX_VALUE
    if (isinstance(func, ast.Attribute)
            and func.attr in _LV10_GEN_DRIVER_ATTRS):
        return _LV10_CTX_VALUE
    if isinstance(func, ast.Name):
        if func.id == 'next':
            return (_LV10_CTX_CONSUME if position == 0
                    else _LV10_CTX_VALUE)
        if func.id in _LV10_OBSERVE_BUILTINS:
            return _LV10_CTX_VALUE
        if func.id in _LV10_LAZY_ITERATOR_BUILTINS:
            return (_LV10_CTX_CONSUME if ctx == _LV10_CTX_CONSUME
                    else _LV10_CTX_VALUE)
    return _LV10_CTX_CONSUME
def _expr_ctx_consume_children(node: ast.AST,
                               excluded: set[int], ctx: int) -> None:
    if isinstance(node, ast.Call):
        if (isinstance(node.func, ast.Attribute)
                and node.func.attr in _LV10_GEN_DRIVER_ATTRS):
            _lv10_expr_ctx(node.func.value, _LV10_CTX_CONSUME, excluded)
        else:
            _lv10_expr_ctx(node.func, _LV10_CTX_VALUE, excluded)
        for position, arg in enumerate(node.args):
            arg_ctx = _lv10_call_arg_ctx(
                node.func, ctx, position,
                shadowed=_lv10_call_is_shadowed(node))
            _lv10_expr_ctx(arg, arg_ctx, excluded)
        for keyword in node.keywords:
            if keyword.value is not None:
                arg_ctx = _lv10_call_arg_ctx(
                    node.func, ctx, None,
                    shadowed=_lv10_call_is_shadowed(node))
                _lv10_expr_ctx(keyword.value, arg_ctx, excluded)
        return
    for child in ast.iter_child_nodes(node):
        if isinstance(child, ast.expr):
            _lv10_expr_ctx(child, _LV10_CTX_VALUE, excluded)
        elif isinstance(child, ast.keyword) and child.value is not None:
            _lv10_expr_ctx(child.value, _LV10_CTX_VALUE, excluded)
def _sctx_type_param_exprs(node: ast.AST):
    for tp in getattr(node, 'type_params', ()) or ():
        for child in ast.iter_child_nodes(tp):
            if isinstance(child, ast.expr):
                yield child
def _sctx_def_site(node: ast.AST, excluded: set[int]) -> None:
    for expr in iter_def_site_nodes(node):
        _lv10_expr_ctx(expr, _LV10_CTX_VALUE, excluded)
    for tp_expr in _sctx_type_param_exprs(node):
        _lv10_expr_ctx(tp_expr, _LV10_CTX_VALUE, excluded)
def _sctx_funcdef(node: ast.AST, excluded: set[int]) -> bool:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return False
    _sctx_def_site(node, excluded)
    for st in node.body:
        for sub in walk_nodes(st):
            excluded.add(id(sub))
    return True
def _sctx_classdef(node: ast.AST, excluded: set[int]) -> bool:
    if not isinstance(node, ast.ClassDef):
        return False
    _sctx_def_site(node, excluded)
    for st in node.body:
        _lv10_stmt_ctx(st, excluded)
    return True
def _sctx_type_alias(node: ast.AST, excluded: set[int]) -> bool:
    if _TYPE_ALIAS_T is None or not isinstance(node, _TYPE_ALIAS_T):
        return False
    _sctx_def_site(node, excluded)
    _lv10_expr_ctx(node.value, _LV10_CTX_VALUE, excluded)
    return True
def _sctx_defs(node: ast.AST, excluded: set[int]) -> bool:
    if _sctx_funcdef(node, excluded):
        return True
    if _sctx_classdef(node, excluded):
        return True
    return _sctx_type_alias(node, excluded)
def _sctx_cond(node: ast.AST, excluded: set[int]) -> bool:
    if isinstance(node, (ast.If, ast.While)):
        _lv10_expr_ctx(node.test, _LV10_CTX_TRUTHY, excluded)
        for st in (*node.body, *node.orelse):
            _lv10_stmt_ctx(st, excluded)
        return True
    if isinstance(node, ast.Assert):
        _lv10_expr_ctx(node.test, _LV10_CTX_TRUTHY, excluded)
        if node.msg is not None:
            _lv10_expr_ctx(node.msg, _LV10_CTX_VALUE, excluded)
        return True
    return False
def _sctx_assigns(node: ast.AST, excluded: set[int]) -> bool:
    if isinstance(node, ast.Assign):
        for t in node.targets:
            _lv10_expr_ctx(t, _LV10_CTX_CONSUME, excluded)
        value_ctx = _LV10_CTX_VALUE
        if any(isinstance(t, (ast.Tuple, ast.List)) for t in node.targets):
            value_ctx = _LV10_CTX_CONSUME
        _lv10_expr_ctx(node.value, value_ctx, excluded)
        return True
    if isinstance(node, ast.AnnAssign):
        _lv10_expr_ctx(node.annotation, _LV10_CTX_VALUE, excluded)
        _lv10_expr_ctx(node.target, _LV10_CTX_CONSUME, excluded)
        if node.value is not None:
            _lv10_expr_ctx(node.value, _LV10_CTX_VALUE, excluded)
        return True
    if isinstance(node, ast.AugAssign):
        _lv10_expr_ctx(node.target, _LV10_CTX_CONSUME, excluded)
        _lv10_expr_ctx(node.value, _LV10_CTX_CONSUME, excluded)
        return True
    return False
def _sctx_loops(node: ast.AST, excluded: set[int]) -> bool:
    if not isinstance(node, (ast.For, ast.AsyncFor)):
        return False
    _lv10_expr_ctx(node.iter, _LV10_CTX_CONSUME, excluded)
    for st in (*node.body, *node.orelse):
        _lv10_stmt_ctx(st, excluded)
    return True
def _sctx_withs(node: ast.AST, excluded: set[int]) -> bool:
    if not isinstance(node, (ast.With, ast.AsyncWith)):
        return False
    for item in node.items:
        _lv10_expr_ctx(item.context_expr, _LV10_CTX_VALUE, excluded)
    for st in node.body:
        _lv10_stmt_ctx(st, excluded)
    return True
def _sctx_tries(node: ast.AST, excluded: set[int]) -> bool:
    if not isinstance(node, TRY_NODES):
        return False
    for st in (*node.body, *node.orelse, *node.finalbody):
        _lv10_stmt_ctx(st, excluded)
    for h in node.handlers:
        if h.type is not None:
            _lv10_expr_ctx(h.type, _LV10_CTX_VALUE, excluded)
        for st in h.body:
            _lv10_stmt_ctx(st, excluded)
    return True
def _sctx_matches(node: ast.AST, excluded: set[int]) -> bool:
    if _LV10_MATCH_TYPE is None or not isinstance(node, _LV10_MATCH_TYPE):
        return False
    _lv10_expr_ctx(node.subject, _LV10_CTX_VALUE, excluded)
    for case in node.cases:
        for pat_expr in _lv10_iter_pattern_exprs(case.pattern):
            _lv10_expr_ctx(pat_expr, _LV10_CTX_VALUE, excluded)
        if case.guard is not None:
            _lv10_expr_ctx(case.guard, _LV10_CTX_TRUTHY, excluded)
        for st in case.body:
            _lv10_stmt_ctx(st, excluded)
    return True
def _sctx_bodied(node: ast.AST, excluded: set[int]) -> bool:
    if _sctx_loops(node, excluded):
        return True
    if _sctx_withs(node, excluded):
        return True
    if _sctx_tries(node, excluded):
        return True
    return _sctx_matches(node, excluded)
def _sctx_simple(node: ast.AST, excluded: set[int]) -> bool:
    if isinstance(node, ast.Return):
        if node.value is not None:
            _lv10_expr_ctx(node.value, _LV10_CTX_VALUE, excluded)
        return True
    if isinstance(node, ast.Raise):
        for exc_expr in (node.exc, node.cause):
            if exc_expr is not None:
                _lv10_expr_ctx(exc_expr, _LV10_CTX_VALUE, excluded)
        return True
    if isinstance(node, ast.Expr):
        _lv10_expr_ctx(node.value, _LV10_CTX_VALUE, excluded)
        return True
    return False
def _lv10_stmt_ctx(node: ast.AST, excluded: set[int]) -> None:
    if _sctx_defs(node, excluded):
        return
    if _sctx_cond(node, excluded):
        return
    if _sctx_assigns(node, excluded):
        return
    if _sctx_bodied(node, excluded):
        return
    if _sctx_simple(node, excluded):
        return
    _stmt_ctx_consume_children(node, excluded)
def _stmt_ctx_consume_children(node: ast.AST,
                               excluded: set[int]) -> None:
    for child in ast.iter_child_nodes(node):
        if isinstance(child, ast.expr):
            _lv10_expr_ctx(child, _LV10_CTX_CONSUME, excluded)
        elif isinstance(child, (ast.stmt, ast.excepthandler)):
            _lv10_stmt_ctx(child, excluded)
        elif isinstance(child, ast.keyword) and child.value is not None:
            _lv10_expr_ctx(child.value, _LV10_CTX_CONSUME, excluded)
def _lv10_non_consuming_refs(
        stmt: ast.AST, ctx: int = _LV10_CTX_VALUE,
        truthy_names: frozenset[str] = _EMPTY_NAMES) -> set[int]:
    excluded = _LV10RefExclusions(truthy_names)
    if isinstance(stmt, ast.stmt):
        _lv10_stmt_ctx(stmt, excluded)
    elif isinstance(stmt, ast.expr):
        _lv10_expr_ctx(stmt, ctx, excluded)
    return excluded
def _lv10_consume_sites(node: ast.AST, var: str,
                        excluded: set[int]) -> int:
    if isinstance(node, ast.Name):
        if (node.id == var and isinstance(node.ctx, ast.Load)
                and id(node) not in excluded):
            return 1
        return 0
    if isinstance(node, ast.IfExp):
        return (_lv10_consume_sites(node.test, var, excluded)
                + max(_lv10_consume_sites(node.body, var, excluded),
                      _lv10_consume_sites(node.orelse, var, excluded)))
    return sum(_lv10_consume_sites(child, var, excluded)
               for child in ast.iter_child_nodes(node))
def _lv10_consume_count(
        stmt: ast.AST, var: str,
        blocked_ids: frozenset[int] = _EMPTY_IDS,
        ctx: int = _LV10_CTX_VALUE,
        truthy_names: frozenset[str] = _EMPTY_NAMES) -> int:
    excluded = _lv10_non_consuming_refs(stmt, ctx, truthy_names)
    excluded |= blocked_ids
    return _lv10_consume_sites(stmt, var, excluded)
def _lv10_iter_def_time_walruses(root: ast.AST):
    pending = [root]
    idx = 0
    while idx < len(pending):
        node = pending[idx]
        idx += 1
        if isinstance(node, (ast.IfExp, ast.BoolOp)):
            yield node
            continue
        if isinstance(node, ast.Lambda):
            pending.extend(iter_def_site_nodes(node))
            continue
        if isinstance(node, ast.GeneratorExp):
            pending.append(node.generators[0].iter)
            continue
        if isinstance(node, ast.NamedExpr):
            yield node
        pending.extend(ast.iter_child_nodes(node))
def _lv10_assign_targets(stmt: ast.AST) -> tuple[list[str], ast.AST] | None:
    if isinstance(stmt, ast.Assign):
        names: list[str] = []
        for t in stmt.targets:
            if not isinstance(t, ast.Name):
                return None
            names.append(t.id)
        return names, stmt.value
    if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name) \
            and stmt.value is not None:
        return [stmt.target.id], stmt.value
    return None
def _lv10_scope_def_nodes(stmt: ast.AST):
    stack: list[ast.AST] = [stmt]
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            yield node
            continue
        if isinstance(node, ast.Lambda):
            continue
        stack.extend(ast.iter_child_nodes(node))
def _lv10_bind_order(node: ast.AST) -> tuple[int, int]:
    return (getattr(node, 'lineno', -1), getattr(node, 'col_offset', -1))
class _LV10BlockBinds:
    def __init__(self) -> None:
        self.rebinds: set[str] = set()
        self.plain_bound: set[str] = set()
        self._gen_at: dict[str, tuple[tuple[int, int], int, int]] = {}
        self._plain_at: dict[str, tuple[int, int]] = {}
        self._walrus: list[ast.NamedExpr] = []
        self._alias_at: dict[str, tuple[tuple[int, int], str, bool]] = {}
        self.gen_bound: set[str] = set()
    def plain(self, names, node: ast.AST) -> None:
        order = _lv10_bind_order(node)
        for name in names:
            self.rebinds.add(name)
            self.plain_bound.add(name)
            if order > self._plain_at.get(name, (-1, -1)):
                self._plain_at[name] = order
    def store(self, target: ast.AST, node: ast.AST) -> None:
        self.plain(target_binding_names(target), node)
    def alias(self, target: ast.Name, value: ast.Name,
              node: ast.AST, *, simultaneous: bool = False) -> None:
        self.plain([target.id], node)
        self._alias_at[target.id] = (
            _lv10_bind_order(node), value.id, simultaneous)
    def new_gen(self, target: ast.AST, genexp: ast.GeneratorExp,
                node: ast.AST) -> None:
        if not isinstance(target, ast.Name):
            return
        order = _lv10_bind_order(node)
        self.rebinds.add(target.id)
        self.gen_bound.add(target.id)
        prev = self._gen_at.get(target.id)
        if prev is None or order >= prev[0]:
            self._gen_at[target.id] = (order, id(genexp), genexp.lineno)
    def walrus(self, node: ast.NamedExpr) -> None:
        self.rebinds.add(node.target.id)
        self._walrus.append(node)
        if isinstance(node.value, ast.GeneratorExp):
            self.new_gen(node.target, node.value, node)
    def _walrus_state(self) -> dict[str, tuple[tuple[int, int], str | None]]:
        state: dict[str, tuple[tuple[int, int], str | None]] = {}
        for node in self._walrus:
            order = _lv10_bind_order(node)
            prev = state.get(node.target.id)
            if prev is not None and order < prev[0]:
                continue
            src = node.value.id if isinstance(node.value, ast.Name) else None
            state[node.target.id] = (order, src)
        return state
    def resolve(self) -> tuple[
            set[str], dict[str, tuple[int, int]],
            list[tuple[str, str]], list[tuple[str, str]]]:
        walrus_state = self._walrus_state()
        new_gens: dict[str, tuple[int, int]] = {}
        for name, (order, gen_id, line) in self._gen_at.items():
            if order <= self._plain_at.get(name, (-1, -1)):
                continue
            last_walrus = walrus_state.get(name)
            if last_walrus is not None and last_walrus[0] > order:
                continue
            new_gens[name] = (gen_id, line)
        aliases = [
            (name, src) for name, (_order, src) in walrus_state.items()
            if src is not None and name not in self.plain_bound
            and name not in self.gen_bound and src not in self.rebinds
        ]
        simultaneous_aliases: list[tuple[str, str]] = []
        for name, (order, src, simultaneous) in self._alias_at.items():
            if (order < self._plain_at.get(name, (-1, -1))
                    or name in self.gen_bound):
                continue
            if simultaneous:
                simultaneous_aliases.append((name, src))
            elif src != name and src not in self.rebinds:
                aliases.append((name, src))
        return self.rebinds, new_gens, aliases, simultaneous_aliases
def _rb_chain_genexp(value: ast.AST | None) -> ast.GeneratorExp | None:
    if isinstance(value, ast.GeneratorExp):
        return value
    if isinstance(value, ast.NamedExpr) and isinstance(
            value.value, ast.GeneratorExp):
        return value.value
    return None
def _rb_chain_name(value: ast.AST | None) -> ast.Name | None:
    if isinstance(value, ast.Name):
        return value
    if isinstance(value, ast.NamedExpr) and isinstance(value.value, ast.Name):
        return value.value
    return None
def _rb_assignment_binds(targets: list | tuple, value: ast.AST,
                         binds: _LV10BlockBinds, node: ast.AST,
                         *, simultaneous: bool = False) -> None:
    if (isinstance(value, (ast.Tuple, ast.List)) and targets
            and all(isinstance(target, (ast.Tuple, ast.List))
                    and len(target.elts) == len(value.elts)
                    and not any(isinstance(elt, ast.Starred)
                                for elt in target.elts)
                    for target in targets)):
        for target in targets:
            for subtarget, subvalue in zip(
                    target.elts, value.elts, strict=True):
                _rb_assignment_binds(
                    (subtarget,), subvalue, binds, node, simultaneous=True)
        return
    chain_value = _rb_chain_genexp(value)
    chain_name = _rb_chain_name(value) if chain_value is None else None
    for target in targets:
        if chain_value is not None and isinstance(target, ast.Name):
            binds.new_gen(target, chain_value, node)
        elif chain_name is not None and isinstance(target, ast.Name):
            binds.alias(target, chain_name, node, simultaneous=simultaneous)
        else:
            binds.store(target, node)
def _rb_target_binds(n: ast.AST, binds: _LV10BlockBinds) -> bool:
    if isinstance(n, ast.Assign):
        _rb_assignment_binds(n.targets, n.value, binds, n)
        return True
    if isinstance(n, ast.AnnAssign):
        if n.value is None:
            return True
        _rb_assignment_binds((n.target,), n.value, binds, n)
        return True
    if isinstance(n, (ast.AugAssign, ast.For, ast.AsyncFor)):
        binds.store(n.target, n)
        return True
    if isinstance(n, (ast.With, ast.AsyncWith)):
        for item in n.items:
            if item.optional_vars is not None:
                binds.store(item.optional_vars, n)
        return True
    return False
def _rb_walrus_alias(n: ast.AST, binds: _LV10BlockBinds) -> bool:
    if not isinstance(n, ast.NamedExpr):
        return False
    binds.walrus(n)
    return True
def _rb_import_binds(n: ast.AST, binds: _LV10BlockBinds) -> bool:
    if not isinstance(n, (ast.Import, ast.ImportFrom)):
        return False
    names, _star_seen = import_bound_names(n)
    binds.plain(names, n)
    return True
def _rb_match_captures(n: ast.AST, binds: _LV10BlockBinds) -> bool:
    captured = capture_binding_names(n)
    if not captured:
        return False
    binds.plain(captured, n)
    return True
def _rb_statement_binds(n: ast.AST, binds: _LV10BlockBinds) -> bool:
    if isinstance(n, ast.ExceptHandler) and n.name:
        binds.plain([n.name], n)
        return True
    if _rb_import_binds(n, binds):
        return True
    if _TYPE_ALIAS_T is not None and isinstance(n, _TYPE_ALIAS_T):
        binds.plain([n.name.id], n)
        return True
    if isinstance(n, ast.Delete):
        binds.plain([t.id for t in n.targets if isinstance(t, ast.Name)], n)
        return True
    return _rb_match_captures(n, binds)
def _lv10_block_rebinds(
        stmt: ast.AST, *, include_walrus: bool = True,
) -> tuple[
        set[str], dict[str, tuple[int, int]],
        list[tuple[str, str]], list[tuple[str, str]]]:
    binds = _LV10BlockBinds()
    for n in iter_nodes_outside(stmt):
        if _rb_target_binds(n, binds):
            continue
        if not include_walrus and isinstance(n, ast.NamedExpr):
            continue
        if include_walrus and _rb_walrus_alias(n, binds):
            continue
        _rb_statement_binds(n, binds)
    for n in _lv10_scope_def_nodes(stmt):
        binds.plain([n.name], n)
    return binds.resolve()
class _LV10GenGroupTracker:
    def __init__(self) -> None:
        self._member_of: dict[str, set[int]] = {}
        self._members: dict[int, set[str]] = {}
        self._first: dict[int, int] = {}
        self._second: dict[int, tuple[int, str]] = {}
        self._last_member: dict[int, str] = {}
        self._reports: set[tuple[str, int, int]] = set()
        self._next_gid = 0
        self._exception_sinks: list[list[tuple]] = []
    def _note_consume(self, gid: int, lineno: int, member: str) -> None:
        self._last_member[gid] = member
        if gid not in self._first:
            self._first[gid] = lineno
            return
        if gid in self._second:
            return
        self._second[gid] = (lineno, member)
        self._reports.add((member, self._first[gid], lineno))
    def new_group(self, name: str) -> int:
        self.detach(name)
        self._next_gid += 1
        gid = self._next_gid
        self._member_of[name] = {gid}
        self._members[gid] = {name}
        return gid
    def alias_to(self, name: str, target: str) -> None:
        target_gids = self._member_of.get(target)
        if not target_gids or self._member_of.get(name) == target_gids:
            return
        self.detach(name)
        self._member_of[name] = set(target_gids)
        for gid in target_gids:
            self._members.setdefault(gid, set()).add(name)
    def alias_many(self, aliases: list[tuple[str, str]]) -> None:
        sources: dict[str, set[int]] = {}
        for name, src in aliases:
            sources.setdefault(name, set()).update(
                self._member_of.get(src, ()))
        for name, _src in aliases:
            self.detach(name)
        for name, gids in sources.items():
            if not gids:
                continue
            self._member_of[name] = gids
            for gid in gids:
                self._members.setdefault(gid, set()).add(name)
    def knows(self, name: str) -> bool:
        return bool(self._member_of.get(name))
    def detach(self, name: str) -> None:
        for gid in self._member_of.pop(name, ()):
            members = self._members.get(gid)
            if members is None:
                continue
            members.discard(name)
            if not members:
                self._members.pop(gid, None)
    def record_consumes(self, subtree: ast.AST, lineno: int,
                        ignore_names: frozenset[str] = _EMPTY_NAMES,
                        blocked_ids: frozenset[int] = _EMPTY_IDS,
                        ctx: int = _LV10_CTX_VALUE) -> None:
        truthy_names = frozenset(self._member_of)
        for member, gids in self._member_of.items():
            if member in ignore_names:
                continue
            count = _lv10_consume_count(
                subtree, member, blocked_ids, ctx, truthy_names)
            if count <= 0:
                continue
            for gid in gids:
                for _ in range(count):
                    self._note_consume(gid, lineno, member)
    def bound(self, gid: int) -> bool:
        return bool(self._members.get(gid))
    def record_repeat_consume(self, gid: int, lineno: int) -> None:
        member = self._last_member.get(gid)
        if member is None:
            members = self._members.get(gid)
            member = min(members) if members else '?'
        self._note_consume(gid, lineno, member)
    def reports(self) -> list[tuple[str, int, int]]:
        earliest: dict[tuple[str, int], int] = {}
        for member, first_line, second_line in self._reports:
            key = (member, second_line)
            earliest[key] = min(first_line, earliest.get(key, first_line))
        return [
            (member, first_line, second_line)
            for (member, second_line), first_line in sorted(
                earliest.items(), key=lambda item: (item[0][1], item[0][0]))
        ]
    def counts(self) -> dict[int, tuple[int | None, tuple[int, str] | None]]:
        gids = set(self._members) | set(self._first) | set(self._second)
        return {gid: (self._first.get(gid), self._second.get(gid))
                for gid in gids}
    def snapshot_state(self) -> tuple:
        return ({name: set(gids) for name, gids in self._member_of.items()},
                {gid: set(members) for gid, members in self._members.items()},
                dict(self._first), dict(self._second), self._next_gid)
    def restore_state(self, snap: tuple) -> None:
        (self._member_of, self._members,
         self._first, self._second, self._next_gid) = (
            {name: set(gids) for name, gids in snap[0].items()},
            {gid: set(members) for gid, members in snap[1].items()},
            dict(snap[2]), dict(snap[3]), snap[4])
    def merge_exclusive_states(self, base_state: tuple,
                               branch_states: list[tuple]) -> None:
        if not branch_states:
            self.restore_state(base_state)
            return
        base_members = base_state[1]
        used = [base_state[4], *(state[4] for state in branch_states),
                *base_members]
        for state in branch_states:
            used.extend((*state[1], *state[2], *state[3]))
        next_gid = max(used, default=0) + 1
        mappings: list[dict[int, int]] = []
        for state in branch_states:
            mapping: dict[int, int] = {}
            for gid in state[1]:
                if gid in base_members:
                    mapping[gid] = gid
                    continue
                mapping[gid] = next_gid
                next_gid += 1
            mappings.append(mapping)
        member_of: dict[str, set[int]] = {}
        members: dict[int, set[str]] = {}
        counts: dict[int, list[tuple[int | None, tuple[int, str] | None]]] = {}
        for state, mapping in zip(branch_states, mappings, strict=True):
            for name, gids in state[0].items():
                for old_gid in gids:
                    new_gid = mapping[old_gid]
                    member_of.setdefault(name, set()).add(new_gid)
                    members.setdefault(new_gid, set()).add(name)
            for old_gid, new_gid in mapping.items():
                counts.setdefault(new_gid, []).append(
                    (state[2].get(old_gid), state[3].get(old_gid)))
        first: dict[int, int] = {}
        second: dict[int, tuple[int, str]] = {}
        for gid, states in counts.items():
            firsts = [value for value, _second in states if value is not None]
            if firsts:
                first[gid] = min(firsts)
            seconds = [value for _first, value in states]
            if states and all(value is not None for value in seconds):
                second[gid] = min(seconds, key=lambda value: value[0])
        self._member_of = member_of
        self._members = members
        self._first = first
        self._second = second
        self._next_gid = next_gid - 1
def _lv10_class_body_consume(tracker: _LV10GenGroupTracker,
                              cls: ast.ClassDef,
                              outer_ignore: frozenset[str] = _EMPTY_NAMES
                              ) -> None:
    shadow: set[str] = set(outer_ignore)
    for st in cls.body:
        _lv10_record_stmt_consumes(
            tracker, st, ignore_names=frozenset(shadow))
        shadow |= _lv10_block_rebinds(st)[0]
def _block_stmt_types(try_nodes, match_type) -> tuple[type, ...]:
    return (
        ast.If, ast.While, ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
        *try_nodes, *((match_type,) if match_type is not None else ()),
    )
_LV10_BLOCK_STMT_TYPES: tuple[type, ...] = _block_stmt_types(
    TRY_NODES, _LV10_MATCH_TYPE)
_LV10_TERMINAL_STMTS = (ast.Break, ast.Continue, ast.Return, ast.Raise)
def _lv10_reachable_stmts(stmts: list) -> list:
    for idx, st in enumerate(stmts):
        if _lv10_stmt_exits(st):
            return list(stmts[:idx + 1])
    return stmts
def _lv10_consume_seq_stmts(tracker: _LV10GenGroupTracker,
                            stmts: list,
                            ignore_names: frozenset[str],
                            blocked: set,
                            identity: bool) -> None:
    stmts = _lv10_reachable_stmts(stmts)
    for st in stmts:
        if isinstance(st, ast.Raise) and tracker._exception_sinks:
            tracker._exception_sinks[-1].append(tracker.snapshot_state())
        if isinstance(st, _LV10_BLOCK_STMT_TYPES):
            _lv10_seq_consume(tracker, st, ignore_names, blocked, identity)
        elif identity:
            _lv10_process_stmt(tracker, st, ignore_names)
        else:
            tracker.record_consumes(st, st.lineno,
                                    ignore_names=ignore_names,
                                    blocked_ids=frozenset(blocked))
def _lv10_loop_no_fallthrough(stmt: ast.AST) -> bool:
    if _lv10_own_loop_contains(stmt.body, ast.Break):
        return False
    if isinstance(stmt, ast.While):
        return _lv10_static_truth_value(stmt.test) is True
    size = _lv10_static_iteration_size(stmt)
    if size == _LV10_LOOP_INVALID:
        return True
    if size is None:
        return False
    return size >= 1 and _lv10_block_no_fallthrough(stmt.body)
def _lv10_block_may_raise_exit(stmts: list) -> bool:
    return any(_lv10_stmt_may_raise_exit(stmt)
               for stmt in _lv10_reachable_stmts(stmts))
def _lv10_stmt_may_raise_exit(stmt: ast.AST) -> bool:
    if isinstance(stmt, ast.Raise):
        return True
    if isinstance(stmt, ast.If):
        return any(_lv10_block_may_raise_exit(branch)
                   for branch in _lv10_if_branch_bodies(stmt))
    if isinstance(stmt, (ast.While, ast.For, ast.AsyncFor)):
        regions = []
        if _lv10_loop_execution_kind(stmt) != _LV10_LOOP_NEVER:
            regions.append(stmt.body)
        if _lv10_loop_else_reachable(stmt):
            regions.append(stmt.orelse)
        return any(_lv10_block_may_raise_exit(region) for region in regions)
    if isinstance(stmt, TRY_NODES):
        regions = [stmt.orelse, stmt.finalbody]
        regions.extend(handler.body for handler in stmt.handlers)
        if not stmt.handlers:
            regions.append(stmt.body)
        return any(_lv10_block_may_raise_exit(region) for region in regions)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return _lv10_block_may_raise_exit(stmt.body)
    if _LV10_MATCH_TYPE is not None and isinstance(stmt, _LV10_MATCH_TYPE):
        return any(_lv10_block_may_raise_exit(case.body)
                   for case in stmt.cases)
    if isinstance(stmt, ast.ClassDef):
        return _lv10_block_may_raise_exit(stmt.body)
    return False
def _lv10_stmt_no_fallthrough(stmt: ast.AST) -> bool:
    if isinstance(stmt, (ast.Return, ast.Raise)):
        return True
    if isinstance(stmt, ast.If):
        return all(_lv10_block_no_fallthrough(branch)
                   for branch in _lv10_if_branch_bodies(stmt))
    if isinstance(stmt, (ast.While, ast.For, ast.AsyncFor)):
        return _lv10_loop_no_fallthrough(stmt)
    if isinstance(stmt, TRY_NODES):
        if stmt.finalbody and _lv10_block_exits(stmt.finalbody):
            return _lv10_block_no_fallthrough(stmt.finalbody)
        normal_path_exits = (
            _lv10_block_no_fallthrough(stmt.body)
            or _lv10_block_no_fallthrough(stmt.orelse))
        return (normal_path_exits
                and all(_lv10_block_no_fallthrough(handler.body)
                        for handler in stmt.handlers))
    if _LV10_MATCH_TYPE is not None and isinstance(stmt, _LV10_MATCH_TYPE):
        return _lv10_match_no_fallthrough(stmt)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return (_lv10_block_no_fallthrough(stmt.body)
                and not _lv10_block_may_raise_exit(stmt.body))
    return False
def _lv10_block_no_fallthrough(stmts: list) -> bool:
    return any(_lv10_stmt_no_fallthrough(stmt)
               for stmt in _lv10_reachable_stmts(stmts))
def _lv10_consume_exclusive_group(
        tracker: _LV10GenGroupTracker,
        branches: list,
        ignore_names: frozenset[str],
        blocked: set,
        identity: bool,
        *,
        branch_pre=None) -> None:
    base_state = tracker.snapshot_state()
    branch_states: list[tuple] = []
    for payload in branches:
        tracker.restore_state(base_state)
        stmts = branch_pre(payload) if branch_pre is not None else payload
        if stmts:
            _lv10_consume_seq_stmts(tracker, stmts, ignore_names,
                                    blocked, identity)
        if not _lv10_block_no_fallthrough(stmts):
            branch_states.append(tracker.snapshot_state())
    tracker.merge_exclusive_states(base_state, branch_states)
_LV10_LOOP_INVALID = -1
_LV10_LOOP_NEVER = 0
_LV10_LOOP_REPEATS = 2
_LV10_EMPTY_CONTAINER_CALLS = frozenset({
    'list', 'tuple', 'set', 'frozenset', 'dict', 'str', 'bytes',
})
def _lv10_static_truth_value(node: ast.AST) -> bool | None:
    if isinstance(node, ast.GeneratorExp):
        return True
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        truth = _lv10_static_truth_value(node.operand)
        return None if truth is None else not truth
    if (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in _LV10_EMPTY_CONTAINER_CALLS
            and not _lv10_call_is_shadowed(node)
            and not node.args and not node.keywords):
        return False
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        if any(isinstance(elt, ast.Starred) for elt in node.elts):
            return None
        return bool(node.elts)
    if isinstance(node, ast.Dict):
        if any(key is None for key in node.keys):
            return None
        return bool(node.keys)
    return None
def _lv10_if_branch_bodies(stmt: ast.If) -> tuple[list, ...]:
    truth = _lv10_static_truth_value(stmt.test)
    if truth is True:
        return (stmt.body,)
    if truth is False:
        return (stmt.orelse,)
    return (stmt.body, stmt.orelse)
def _lv10_static_range_size(iter_node: ast.AST) -> int | None:
    if not (isinstance(iter_node, ast.Call)
            and isinstance(iter_node.func, ast.Name)
            and iter_node.func.id == 'range'
            and not _lv10_call_is_shadowed(iter_node)
            and not iter_node.keywords):
        return None
    values = [int_literal(arg, allow_bool=True) for arg in iter_node.args]
    if (any(value is None for value in values)
            or not 1 <= len(values) <= 3):
        return None
    try:
        return len(range(*values))
    except ValueError:
        return _LV10_LOOP_INVALID
    except OverflowError:
        return _LV10_LOOP_REPEATS
def _lv10_static_iteration_size(stmt: ast.AST) -> int | None:
    iter_node = getattr(stmt, 'iter', None)
    if (isinstance(iter_node, ast.Call)
            and isinstance(iter_node.func, ast.Name)
            and iter_node.func.id in _LV10_EMPTY_CONTAINER_CALLS
            and not _lv10_call_is_shadowed(iter_node)
            and not iter_node.args and not iter_node.keywords):
        return 0
    if isinstance(iter_node, (ast.List, ast.Tuple)):
        if any(isinstance(elt, ast.Starred) for elt in iter_node.elts):
            return None
        return len(iter_node.elts)
    if isinstance(iter_node, (ast.Set, ast.Dict)):
        elements = (iter_node.elts if isinstance(iter_node, ast.Set)
                    else iter_node.keys)
        if any(elt is None or isinstance(elt, ast.Starred)
               for elt in elements):
            return None
        try:
            return len(ast.literal_eval(iter_node))
        except (ValueError, TypeError, SyntaxError):
            return len(elements)
    if isinstance(iter_node, ast.Constant) and isinstance(
            iter_node.value, (str, bytes)):
        return len(iter_node.value)
    return _lv10_static_range_size(iter_node)
def _lv10_loop_execution_kind(stmt: ast.AST) -> int:
    if isinstance(stmt, ast.While):
        return (_LV10_LOOP_NEVER
                if _lv10_static_truth_value(stmt.test) is False
                else _LV10_LOOP_REPEATS)
    size = _lv10_static_iteration_size(stmt)
    if size is None:
        return _LV10_LOOP_REPEATS
    return min(max(size, _LV10_LOOP_NEVER), _LV10_LOOP_REPEATS)
def _lv10_own_loop_contains(body: list, terminal: type) -> bool:
    stack: list[tuple[ast.AST, int]] = [(item, 0) for item in body]
    while stack:
        node, loop_depth = stack.pop()
        if isinstance(node, _LV10_SCOPE_CONTAINERS):
            continue
        if isinstance(node, terminal):
            if loop_depth == 0:
                return True
            continue
        if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            stack.extend((item, loop_depth + 1) for item in node.body)
            stack.extend((item, loop_depth) for item in node.orelse)
            continue
        stack.extend(
            (child, loop_depth) for child in ast.iter_child_nodes(node))
    return False
def _lv10_body_prevents_replay(body: list) -> bool:
    body = _lv10_reachable_stmts(body)
    if not body or _lv10_own_loop_contains(body, ast.Continue):
        return False
    return _lv10_stmt_exits(body[-1])
def _lv10_block_exits(stmts: list) -> bool:
    return any(_lv10_stmt_exits(stmt) for stmt in stmts)
def _lv10_stmt_exits(stmt: ast.AST) -> bool:
    if isinstance(stmt, _LV10_TERMINAL_STMTS):
        return True
    if isinstance(stmt, ast.If):
        branches = _lv10_if_branch_bodies(stmt)
        return all(_lv10_block_exits(branch) for branch in branches)
    if isinstance(stmt, (ast.While, ast.For, ast.AsyncFor)):
        return _lv10_loop_no_fallthrough(stmt)
    if isinstance(stmt, TRY_NODES):
        # finally 未退出时不会吞掉正常路径的 return/raise：只有 finally
        # 自身退出才无条件决定 try 的终态。
        if stmt.finalbody and _lv10_block_exits(stmt.finalbody):
            return True
        normal_path_exits = (_lv10_block_exits(stmt.body)
                             or _lv10_block_exits(stmt.orelse))
        return (normal_path_exits
                and all(_lv10_block_exits(handler.body)
                        for handler in stmt.handlers))
    if _LV10_MATCH_TYPE is not None and isinstance(stmt, _LV10_MATCH_TYPE):
        return _lv10_match_no_fallthrough(stmt)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return (_lv10_block_no_fallthrough(stmt.body)
                and not _lv10_block_may_raise_exit(stmt.body))
    return False
def _lv10_loop_may_be_empty(stmt: ast.AST) -> bool:
    if isinstance(stmt, ast.While):
        return _lv10_static_truth_value(stmt.test) is not True
    size = _lv10_static_iteration_size(stmt)
    return size != _LV10_LOOP_INVALID and (size is None or size == 0)
def _lv10_loop_else_reachable(stmt: ast.AST) -> bool:
    if (isinstance(stmt, ast.While)
            and _lv10_static_truth_value(stmt.test) is True):
        return False
    if (isinstance(stmt, (ast.For, ast.AsyncFor))
            and _lv10_static_iteration_size(stmt) == _LV10_LOOP_INVALID):
        return False
    if _lv10_loop_execution_kind(stmt) == _LV10_LOOP_NEVER:
        return True
    if _lv10_loop_may_be_empty(stmt):
        return True
    return not _lv10_body_prevents_replay(stmt.body)
def _lv10_replay_consumes(tracker: _LV10GenGroupTracker,
                          before: dict) -> None:
    for gid, (first, second) in tracker.counts().items():
        if gid not in before or second is not None:
            continue
        prev_first = before[gid][0]
        if first is None or first == prev_first or not tracker.bound(gid):
            continue
        tracker.record_repeat_consume(gid, first)
def _lv10_consume_repeating_body(tracker: _LV10GenGroupTracker,
                                 loop: ast.AST, body: list,
                                 ignore_names, blocked,
                                 identity: bool,
                                 zero_state: tuple | None = None) -> None:
    execution_kind = _lv10_loop_execution_kind(loop)
    if execution_kind == _LV10_LOOP_NEVER:
        return
    body = _lv10_reachable_stmts(body)
    body_entry_state = tracker.snapshot_state()
    before = tracker.counts()
    _lv10_consume_seq_stmts(tracker, body, ignore_names, blocked,
                            identity)
    if (execution_kind == _LV10_LOOP_REPEATS
            and not _lv10_body_prevents_replay(body)):
        _lv10_replay_consumes(tracker, before)
    empty_state = zero_state or body_entry_state
    if _lv10_block_no_fallthrough(body):
        tracker.restore_state(empty_state)
        return
    if _lv10_loop_may_be_empty(loop):
        tracker.merge_exclusive_states(
            empty_state, [empty_state, tracker.snapshot_state()])
def _seq_consume_for(tracker: _LV10GenGroupTracker,
                     stmt, ignore_names, blocked, _fs_blocked,
                     identity: bool) -> None:
    _lv10_record_expr_eval(
        tracker, stmt.iter, stmt.lineno, ignore_names=ignore_names,
        blocked_ids=_fs_blocked, ctx=_LV10_CTX_CONSUME, identity=identity)
    zero_state = tracker.snapshot_state()
    if identity and _lv10_loop_execution_kind(stmt) != _LV10_LOOP_NEVER:
        for vname in target_binding_names(stmt.target):
            tracker.detach(vname)
    _lv10_consume_repeating_body(
        tracker, stmt, stmt.body, ignore_names, blocked, identity,
        zero_state=zero_state)
    if _lv10_loop_else_reachable(stmt):
        _lv10_consume_seq_stmts(tracker, stmt.orelse, ignore_names,
                                blocked, identity)
def _lv10_try_else_reachable(stmt: ast.AST) -> bool:
    return not _lv10_block_exits(stmt.body)
def _seq_consume_try(tracker: _LV10GenGroupTracker,
                     stmt, ignore_names, blocked, _fs_blocked,
                     identity: bool) -> None:
    body_entry = tracker.snapshot_state()
    raise_states: list[tuple] = []
    tracker._exception_sinks.append(raise_states)
    try:
        _lv10_consume_seq_stmts(tracker, stmt.body, ignore_names,
                                blocked, identity)
    finally:
        tracker._exception_sinks.pop()
    if not stmt.handlers and raise_states and tracker._exception_sinks:
        tracker._exception_sinks[-1].extend(raise_states)
    normal_state = tracker.snapshot_state()
    def _try_branch_stmts(payload) -> list:
        if isinstance(payload, ast.ExceptHandler):
            if payload.type is not None:
                _lv10_record_expr_eval(
                    tracker, payload.type, payload.lineno,
                    ignore_names=ignore_names, blocked_ids=_fs_blocked,
                    ctx=_LV10_CTX_VALUE, identity=identity)
            if payload.name and identity:
                tracker.detach(payload.name)
            return list(payload.body)
        return list(payload)
    branch_states: list[tuple] = []
    if not stmt.handlers:
        branch_states.extend(raise_states)
    if type(stmt) is not ast.Try:
        for base_state in (body_entry, *raise_states):
            tracker.restore_state(base_state)
            may_fallthrough = False
            for handler in stmt.handlers:
                handler_body = _try_branch_stmts(handler)
                _lv10_consume_seq_stmts(
                    tracker, handler_body, ignore_names, blocked, identity)
                if not _lv10_block_no_fallthrough(handler_body):
                    may_fallthrough = True
            if may_fallthrough:
                branch_states.append(tracker.snapshot_state())
    else:
        for handler in stmt.handlers:
            for base_state in (body_entry, *raise_states):
                tracker.restore_state(base_state)
                handler_body = _try_branch_stmts(handler)
                _lv10_consume_seq_stmts(
                    tracker, handler_body, ignore_names, blocked, identity)
                if not _lv10_block_no_fallthrough(handler_body):
                    branch_states.append(tracker.snapshot_state())
    tracker.restore_state(normal_state)
    if _lv10_try_else_reachable(stmt):
        _lv10_consume_seq_stmts(tracker, stmt.orelse, ignore_names,
                                blocked, identity)
        if not _lv10_block_no_fallthrough(stmt.orelse):
            branch_states.append(tracker.snapshot_state())
    tracker.merge_exclusive_states(body_entry, branch_states)
    _lv10_consume_seq_stmts(tracker, stmt.finalbody, ignore_names,
                            blocked, identity)
def _seq_consume_with(tracker: _LV10GenGroupTracker,
                      stmt, ignore_names, blocked, _fs_blocked,
                      identity: bool) -> None:
    for item in stmt.items:
        _lv10_record_expr_eval(
            tracker, item.context_expr, stmt.lineno,
            ignore_names=ignore_names, blocked_ids=_fs_blocked,
            ctx=_LV10_CTX_VALUE, identity=identity)
        if item.optional_vars is not None and identity:
            for vname in target_binding_names(item.optional_vars):
                tracker.detach(vname)
    _lv10_consume_seq_stmts(tracker, stmt.body, ignore_names,
                            blocked, identity)
def _lv10_irrefutable_pattern(pattern: ast.AST) -> bool:
    if _MATCH_AS_T is not None and isinstance(pattern, _MATCH_AS_T):
        return (pattern.pattern is None
                or _lv10_irrefutable_pattern(pattern.pattern))
    if _MATCH_OR_T is not None and isinstance(pattern, _MATCH_OR_T):
        return any(_lv10_irrefutable_pattern(sub)
                   for sub in pattern.patterns)
    return False
def _lv10_case_can_match(case: ast.AST) -> bool:
    guard = getattr(case, "guard", None)
    return guard is None or _lv10_static_truth_value(guard) is not False
def _lv10_case_always_matches(case: ast.AST) -> bool:
    guard = getattr(case, "guard", None)
    return ((guard is None or _lv10_static_truth_value(guard) is True)
            and _lv10_irrefutable_pattern(case.pattern))
def _lv10_match_reachable_cases(stmt: ast.AST) -> list:
    """按顺序返回可达 case：静态假 guard 跳过，穷尽 case 之后截断。"""
    cases = []
    for case in stmt.cases:
        guard = getattr(case, "guard", None)
        if guard is not None and _lv10_static_truth_value(guard) is False:
            continue
        cases.append(case)
        if _lv10_case_always_matches(case):
            break
    return cases
def _lv10_match_may_skip_all_cases(stmt: ast.AST) -> bool:
    return not any(_lv10_case_always_matches(case) for case in stmt.cases)
def _lv10_match_no_fallthrough(stmt: ast.AST) -> bool:
    """match 是否保证不落入后续语句（首个穷尽 case 及其之前均退出）。"""
    for index, case in enumerate(stmt.cases):
        if not _lv10_case_always_matches(case):
            continue
        # 该 case 之前仍可能先命中：它们的 body 也必须退出，否则存在
        # 落入 match 之后的正常路径；静态假 guard 的 case 永不执行。
        return all(_lv10_block_exits(item.body)
                   for item in stmt.cases[:index + 1]
                   if _lv10_case_can_match(item))
    return False
def _lv10_direct_match_capture(pattern: ast.AST) -> str | None:
    if (_MATCH_AS_T is not None and isinstance(pattern, _MATCH_AS_T)
            and pattern.pattern is None):
        return pattern.name
    return None
def _seq_consume_match(tracker: _LV10GenGroupTracker,
                       stmt, ignore_names, blocked, _fs_blocked,
                       identity: bool) -> None:
    _lv10_record_expr_eval(
        tracker, stmt.subject, stmt.lineno, ignore_names=ignore_names,
        blocked_ids=_fs_blocked, ctx=_LV10_CTX_VALUE, identity=identity)
    def _case_stmts(case) -> list:
        if case is None:
            return []
        for pat_expr in _lv10_iter_pattern_exprs(case.pattern):
            tracker.record_consumes(pat_expr, stmt.lineno,
                                    ignore_names=ignore_names,
                                    blocked_ids=_fs_blocked)
        if identity:
            direct_capture = _lv10_direct_match_capture(case.pattern)
            subject_name = (stmt.subject.id
                            if isinstance(stmt.subject, ast.Name) else "")
            if direct_capture and subject_name:
                if direct_capture != subject_name:
                    tracker.detach(direct_capture)
                    tracker.alias_to(direct_capture, subject_name)
            else:
                for cap in _lv10_pattern_capture_names(case.pattern):
                    tracker.detach(cap)
        if case.guard is not None:
            _lv10_record_expr_eval(
                tracker, case.guard, stmt.lineno, ignore_names=ignore_names,
                blocked_ids=_fs_blocked, ctx=_LV10_CTX_TRUTHY,
                identity=identity)
            if _lv10_static_truth_value(case.guard) is False:
                return []
        return list(case.body)
    branches = _lv10_match_reachable_cases(stmt)
    if _lv10_match_may_skip_all_cases(stmt):
        branches.append(None)
    _lv10_consume_exclusive_group(
        tracker, branches, ignore_names, blocked,
        branch_pre=_case_stmts, identity=identity)
def _lv10_seq_consume(tracker: _LV10GenGroupTracker,
                      stmt: ast.AST,
                      ignore_names: frozenset[str],
                      blocked: set,
                      identity: bool = True) -> None:
    _fs_blocked = frozenset(blocked)
    if isinstance(stmt, ast.If):
        _lv10_record_expr_eval(
            tracker, stmt.test, stmt.lineno, ignore_names=ignore_names,
            blocked_ids=_fs_blocked, ctx=_LV10_CTX_TRUTHY, identity=identity)
        _lv10_consume_exclusive_group(
            tracker, list(_lv10_if_branch_bodies(stmt)),
            ignore_names, blocked, identity=identity)
        return
    if isinstance(stmt, ast.While):
        before_test = tracker.counts()
        _lv10_record_expr_eval(
            tracker, stmt.test, stmt.lineno, ignore_names=ignore_names,
            blocked_ids=_fs_blocked, ctx=_LV10_CTX_TRUTHY, identity=identity)
        if (_lv10_loop_execution_kind(stmt) == _LV10_LOOP_REPEATS
                and not _lv10_body_prevents_replay(stmt.body)):
            _lv10_replay_consumes(tracker, before_test)
        _lv10_consume_repeating_body(tracker, stmt, stmt.body,
                                     ignore_names, blocked, identity)
        if _lv10_loop_else_reachable(stmt):
            _lv10_consume_seq_stmts(tracker, stmt.orelse, ignore_names,
                                    blocked, identity)
        return
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        _seq_consume_for(tracker, stmt, ignore_names, blocked,
                         _fs_blocked, identity)
        return
    if isinstance(stmt, TRY_NODES):
        _seq_consume_try(tracker, stmt, ignore_names, blocked,
                         _fs_blocked, identity)
        return
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        _seq_consume_with(tracker, stmt, ignore_names, blocked,
                          _fs_blocked, identity)
        return
    if _LV10_MATCH_TYPE is not None and isinstance(stmt, _LV10_MATCH_TYPE):
        _seq_consume_match(tracker, stmt, ignore_names, blocked,
                           _fs_blocked, identity)
        return
    tracker.record_consumes(stmt, stmt.lineno,
                            ignore_names=ignore_names,
                            blocked_ids=_fs_blocked)
def _lv10_record_stmt_consumes(tracker: _LV10GenGroupTracker,
                               stmt: ast.AST,
                               ignore_names: frozenset[str]
                               ) -> None:
    blocked: set[int] = set()
    for cls in _lv10_scope_def_nodes(stmt):
        if not isinstance(cls, ast.ClassDef):
            continue
        for d in iter_def_site_nodes(cls):
            tracker.record_consumes(d, cls.lineno,
                                    ignore_names=ignore_names)
        _lv10_class_body_consume(tracker, cls, ignore_names)
        for sub in walk_nodes(cls):
            blocked.add(id(sub))
    if isinstance(stmt, _LV10_BLOCK_STMT_TYPES):
        _lv10_seq_consume(tracker, stmt, ignore_names, blocked,
                          identity=False)
        return
    tracker.record_consumes(stmt, stmt.lineno,
                            ignore_names=ignore_names,
                            blocked_ids=frozenset(blocked))
def _track_new_generator(tracker: _LV10GenGroupTracker, name: str,
                          genexp_id: int, genexp_line: int,
                          excluded: set[int]) -> None:
    gid = tracker.new_group(name)
    if genexp_id not in excluded:
        tracker._note_consume(gid, genexp_line, name)
def _lv10_apply_rebinds(tracker: _LV10GenGroupTracker,
                        stmt: ast.AST, *, include_walrus: bool = True) -> None:
    rebinds, new_gens, walrus_aliases, simultaneous_aliases = (
        _lv10_block_rebinds(stmt, include_walrus=include_walrus))
    _aliased = {name for name, _src in simultaneous_aliases}
    if simultaneous_aliases:
        tracker.alias_many(simultaneous_aliases)
    if new_gens:
        _excluded = _lv10_non_consuming_refs(stmt)
        group_of: dict[int, str] = {}
        for gname, (genexp_id, _gen_line) in new_gens.items():
            first = group_of.get(genexp_id)
            if first is not None:
                tracker.alias_to(gname, first)
                continue
            _track_new_generator(
                tracker, gname, genexp_id, _gen_line, _excluded)
            group_of[genexp_id] = gname
    for w, src in walrus_aliases:
        if tracker.knows(src):
            tracker.alias_to(w, src)
            _aliased.add(w)
    for rname in rebinds - set(new_gens) - _aliased:
        tracker.detach(rname)
def _apply_boolop_def_time_walruses(
        tracker: _LV10GenGroupTracker, stmt: ast.AST, node: ast.BoolOp,
        ctx: int) -> None:
    base_state = tracker.snapshot_state()
    branch_states: list[tuple] = []
    stopped = False
    for child in node.values:
        _apply_def_time_walruses(tracker, stmt, child, ctx=ctx)
        truth = _lv10_value_truth(tracker, child)
        stops = ((isinstance(node.op, ast.Or) and truth is True)
                 or (isinstance(node.op, ast.And) and truth is False))
        if truth is None or stops:
            branch_states.append(tracker.snapshot_state())
        if stops:
            stopped = True
            break
    if not stopped:
        branch_states.append(tracker.snapshot_state())
    tracker.merge_exclusive_states(base_state, branch_states)
def _apply_def_time_walruses(tracker: _LV10GenGroupTracker,
                             stmt: ast.AST, value: ast.AST,
                             *, ctx: int = _LV10_CTX_VALUE) -> None:
    if isinstance(value, ast.IfExp):
        _apply_def_time_walruses(tracker, stmt, value.test, ctx=ctx)
        truth = _lv10_value_truth(tracker, value.test)
        if truth is not None:
            branch = value.body if truth else value.orelse
            _apply_def_time_walruses(tracker, stmt, branch, ctx=ctx)
            return
        base_state = tracker.snapshot_state()
        _apply_def_time_walruses(tracker, stmt, value.body, ctx=ctx)
        body_state = tracker.snapshot_state()
        tracker.restore_state(base_state)
        _apply_def_time_walruses(tracker, stmt, value.orelse, ctx=ctx)
        else_state = tracker.snapshot_state()
        tracker.merge_exclusive_states(base_state, [body_state, else_state])
        return
    if isinstance(value, ast.BoolOp):
        _apply_boolop_def_time_walruses(tracker, stmt, value, ctx)
        return
    _excluded: set[int] | None = None
    for sub in _lv10_iter_def_time_walruses(value):
        if isinstance(sub, (ast.IfExp, ast.BoolOp)):
            _apply_def_time_walruses(tracker, stmt, sub, ctx=ctx)
            continue
        w = sub.target.id
        if isinstance(sub.value, ast.GeneratorExp):
            if _excluded is None:
                _excluded = _lv10_non_consuming_refs(stmt, ctx)
            _track_new_generator(
                tracker, w, id(sub.value), sub.value.lineno, _excluded)
        elif (isinstance(sub.value, ast.Name)
                and tracker.knows(sub.value.id)):
            tracker.alias_to(w, sub.value.id)
        elif not _lv10_alias_value_sources(tracker, [w], sub.value):
            tracker.detach(w)
def _apply_def_site_walruses(tracker: _LV10GenGroupTracker,
                              node: ast.AST) -> None:
    for expression in iter_def_site_nodes(node):
        _apply_def_time_walruses(tracker, expression, expression)
def _lv10_bind_eval_walrus(tracker: _LV10GenGroupTracker,
                            node: ast.NamedExpr, ctx: int) -> None:
    name = node.target.id
    value = node.value
    if isinstance(value, ast.GeneratorExp):
        excluded = _lv10_non_consuming_refs(node, ctx)
        _track_new_generator(tracker, name, id(value), value.lineno, excluded)
    elif isinstance(value, ast.Name) and tracker.knows(value.id):
        tracker.alias_to(name, value.id)
    elif not _lv10_alias_value_sources(tracker, [name], value):
        tracker.detach(name)
def _lv10_record_boolop_eval(
        tracker: _LV10GenGroupTracker, node: ast.BoolOp, lineno: int,
        ctx: int, ignore_names: frozenset[str],
        blocked_ids: frozenset[int], identity: bool) -> None:
    base_state = tracker.snapshot_state()
    branch_states: list[tuple] = []
    stopped = False
    last_index = len(node.values) - 1
    for index, child in enumerate(node.values):
        _lv10_record_expr_eval(
            tracker, child, lineno, ctx, ignore_names,
            blocked_ids, identity)
        truth = _lv10_value_truth(tracker, child)
        stops = ((isinstance(node.op, ast.Or) and truth is True)
                 or (isinstance(node.op, ast.And) and truth is False))
        if stops:
            branch_states.append(tracker.snapshot_state())
            stopped = True
            break
        if truth is None and index < last_index:
            branch_states.append(tracker.snapshot_state())
    if not stopped:
        branch_states.append(tracker.snapshot_state())
    tracker.merge_exclusive_states(base_state, branch_states)
def _lv10_record_expr_eval(tracker: _LV10GenGroupTracker,
                           node: ast.AST, lineno: int, ctx: int,
                           ignore_names: frozenset[str] = _EMPTY_NAMES,
                           blocked_ids: frozenset[int] = _EMPTY_IDS,
                           identity: bool = True) -> None:
    if isinstance(node, ast.NamedExpr):
        _lv10_record_expr_eval(
            tracker, node.value, lineno, ctx,
            ignore_names, blocked_ids, identity)
        if identity:
            _lv10_bind_eval_walrus(tracker, node, ctx)
        return
    if isinstance(node, ast.BoolOp):
        _lv10_record_boolop_eval(
            tracker, node, lineno, ctx,
            ignore_names, blocked_ids, identity)
        return
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        for element in node.elts:
            element_ctx = (_LV10_CTX_CONSUME if isinstance(element, ast.Starred)
                           else _LV10_CTX_VALUE)
            _lv10_record_expr_eval(
                tracker, element, lineno, element_ctx,
                ignore_names, blocked_ids, identity)
        return
    tracker.record_consumes(
        node, lineno, ignore_names=ignore_names,
        blocked_ids=blocked_ids, ctx=ctx)
    if identity:
        _apply_def_time_walruses(tracker, node, node)
def _apply_assign_target_bindings(tracker: _LV10GenGroupTracker,
                                  names: list[str],
                                  top_walrus: ast.NamedExpr | None) -> None:
    for name in names:
        if top_walrus is None:
            tracker.detach(name)
            continue
        w = top_walrus.target.id
        if name == w:
            continue
        top_val = top_walrus.value
        if isinstance(top_val, ast.GeneratorExp) or (
                isinstance(top_val, ast.Name)
                and tracker.knows(top_val.id)):
            tracker.alias_to(name, w)
        else:
            tracker.detach(name)
def _lv10_value_truth(tracker: _LV10GenGroupTracker,
                      value: ast.AST) -> bool | None:
    return _lv10_expression_truth(value, frozenset(tracker._member_of))
def _lv10_value_source_names(tracker: _LV10GenGroupTracker,
                              value: ast.AST) -> list[str]:
    if isinstance(value, ast.NamedExpr):
        return _lv10_value_source_names(tracker, value.value)
    if isinstance(value, ast.Name):
        return [value.id] if tracker.knows(value.id) else []
    if isinstance(value, ast.GeneratorExp):
        values = []
        for comp in value.generators:
            values.append(comp.iter)
            if _lv10_static_iteration_size(comp) == _LV10_LOOP_NEVER:
                break
        return list(dict.fromkeys(
            name for child in values
            for name in _lv10_value_source_names(tracker, child)
        ))
    if isinstance(value, ast.IfExp):
        truth = _lv10_value_truth(tracker, value.test)
        values = ((value.body,) if truth is True else
                  (value.orelse,) if truth is False else
                  (value.body, value.orelse))
    elif isinstance(value, ast.BoolOp):
        selected = []
        for child in value.values:
            truth = _lv10_value_truth(tracker, child)
            if isinstance(value.op, ast.Or):
                if truth is False:
                    continue
                selected.append(child)
                if truth is True:
                    break
            else:
                if truth is True:
                    continue
                selected.append(child)
                if truth is False:
                    break
        values = selected
    elif (isinstance(value, ast.Call)
          and isinstance(value.func, ast.Name)
          and value.func.id in _LV10_LAZY_ITERATOR_BUILTINS
          and not _lv10_call_is_shadowed(value)):
        if value.func.id == 'iter':
            values = value.args[:1]
        elif value.func.id in {'map', 'filter'}:
            values = value.args[1:]
        else:
            values = value.args
    else:
        return []
    return list(dict.fromkeys(
        name
        for child in values
        for name in _lv10_value_source_names(tracker, child)
    ))
def _lv10_alias_value_sources(tracker: _LV10GenGroupTracker,
                               names: list[str], value: ast.AST) -> bool:
    sources = _lv10_value_source_names(tracker, value)
    if not sources:
        return False
    tracker.alias_many([
        (name, source) for name in names for source in sources
    ])
    return True
def _process_assign_stmt(tracker: _LV10GenGroupTracker,
                          stmt: ast.AST, names: list[str],
                          value: ast.AST) -> None:
    if isinstance(value, ast.GeneratorExp):
        tracker.record_consumes(value, stmt.lineno)
        _apply_def_time_walruses(tracker, value, value)
        if _lv10_alias_value_sources(tracker, names, value):
            return
        tracker.new_group(names[0])
        for extra in names[1:]:
            tracker.alias_to(extra, names[0])
        return
    if isinstance(value, ast.Name) and tracker.knows(value.id):
        for name in names:
            tracker.alias_to(name, value.id)
        return
    _lv10_record_expr_eval(
        tracker, value, stmt.lineno, _LV10_CTX_VALUE)
    top_walrus = value if isinstance(value, ast.NamedExpr) else None
    if _lv10_alias_value_sources(tracker, names, value):
        return
    _apply_assign_target_bindings(tracker, names, top_walrus)
def _lv10_process_stmt(tracker: _LV10GenGroupTracker,
                       stmt: ast.AST,
                       ignore_names: frozenset[str] = _EMPTY_NAMES
                       ) -> None:
    if isinstance(stmt, ast.ClassDef):
        for d in iter_def_site_nodes(stmt):
            tracker.record_consumes(d, stmt.lineno)
        _apply_def_site_walruses(tracker, stmt)
        _lv10_class_body_consume(tracker, stmt)
        tracker.detach(stmt.name)
        return
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
        tracker.record_consumes(stmt, stmt.lineno)
        _apply_def_site_walruses(tracker, stmt)
        tracker.detach(stmt.name)
        return
    if isinstance(stmt, _LV10_BLOCK_STMT_TYPES):
        _lv10_seq_consume(tracker, stmt, ignore_names, set())
        return
    assigned = _lv10_assign_targets(stmt)
    if assigned is not None:
        names, value = assigned
        _process_assign_stmt(tracker, stmt, names, value)
        return
    if isinstance(stmt, ast.Expr):
        expressions = (stmt.value,)
    elif isinstance(stmt, ast.Return):
        expressions = () if stmt.value is None else (stmt.value,)
    elif isinstance(stmt, ast.Raise):
        expressions = tuple(
            expr for expr in (stmt.exc, stmt.cause) if expr is not None)
    elif isinstance(stmt, ast.Assert):
        expressions = ((stmt.test,) if stmt.msg is None
                       else (stmt.test, stmt.msg))
    else:
        expressions = ()
    if expressions or isinstance(stmt, (ast.Return, ast.Raise, ast.Assert)):
        for expression in expressions:
            _lv10_record_expr_eval(
                tracker, expression, stmt.lineno, _LV10_CTX_VALUE,
                ignore_names=ignore_names)
    else:
        tracker.record_consumes(
            stmt, stmt.lineno, ignore_names=ignore_names)
        _apply_def_time_walruses(tracker, stmt, stmt)
    _lv10_apply_rebinds(tracker, stmt, include_walrus=False)
_NESTED_DEF_INDEX_CACHE: dict[int, tuple] = {}
_NESTED_DEF_INDEX_MAX = 512


def _nested_def_bindings(body: list) -> dict[str, tuple]:
    """``body`` 内嵌套函数/类的名字分桶（按 ``id(body)`` 记忆化）。

    原实现为「同一个作用域 × 每个待查名字」重扫整棵语句树，属 O(语句数 ×
    节点数) 的平方级热点（实测 3000 行模块上单个检测器就要分钟级）。索引
    只依赖语句列表结构，且桶内保持语句先后顺序，与逐次扫描**逐项等价**。
    """
    key = id(body)
    hit = _NESTED_DEF_INDEX_CACHE.get(key)
    if hit is not None and hit[0] is body:
        return hit[1]
    buckets: dict[str, list] = {}
    for stmt in body:
        for node in _lv10_scope_def_nodes(stmt):
            buckets.setdefault(node.name, []).append((node, node))
    index = {name: tuple(items) for name, items in buckets.items()}
    _NESTED_DEF_INDEX_CACHE[key] = (body, index)
    while len(_NESTED_DEF_INDEX_CACHE) > _NESTED_DEF_INDEX_MAX:
        _NESTED_DEF_INDEX_CACHE.pop(next(iter(_NESTED_DEF_INDEX_CACHE)), None)
    return index


def _named_binding_entries(scope: ast.AST, name: str) -> list[tuple[ast.AST, Any]]:
    body = getattr(scope, 'body', None)
    if not isinstance(body, list):
        return []
    entries = list(binding_entries_index(body).get(name, ()))
    entries.extend(_nested_def_bindings(body).get(name, ()))
    return entries
def _latest_binding(
        entries: list[tuple[ast.AST, Any]],
) -> ast.AST:
    return max(
        enumerate(entries),
        key=lambda item: (
            getattr(item[1][0], 'lineno', -1),
            getattr(item[1][0], 'col_offset', -1),
            item[0],
        ),
    )[1][0]
def _binding_shadows_name(
        binding: ast.AST, exclude_ids: frozenset[int],
        include_imports: bool,
) -> bool:
    if id(binding) in exclude_ids:
        return False
    return include_imports or not isinstance(
        binding, (ast.Import, ast.ImportFrom))
def _ordered_binding_verdict(
        scope: ast.AST, name: str, position: tuple[int, int],
        exclude_ids: frozenset[int], include_imports: bool,
) -> bool | None:
    prior = [
        (node, value) for node, value in _named_binding_entries(scope, name)
        if (getattr(node, 'lineno', -1), getattr(node, 'col_offset', -1))
        <= position
        and (not isinstance(
            node, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.NamedExpr))
            or node_end_position(node) <= position)
    ]
    if not prior:
        return None
    latest = _latest_binding(prior)
    if isinstance(latest, ast.Delete):
        return False
    return _binding_shadows_name(latest, exclude_ids, include_imports)
def _call_name_shadowed(
        node: ast.AST, name: str, parents: dict[int, ast.AST],
        cache: dict[tuple, set[str]], *,
        module_exclude_ids: frozenset[int] = _EMPTY_IDS,
        include_imports: bool = True,
) -> bool:
    scope = nearest_scope(parents, node)
    while (scope is not None and not isinstance(scope, ast.Module)
           and id(node) in definition_outer_node_ids(scope)):
        scope = nearest_scope(parents, scope)
    if isinstance(scope, ast.Module):
        if shadowed_binding_at(
                node, name, parents, cache, include_module=False,
                module_exclude_ids=module_exclude_ids,
                include_imports=include_imports):
            return True
        verdict = _ordered_binding_verdict(
            scope, name, (node.lineno, node.col_offset),
            module_exclude_ids, include_imports)
        return bool(verdict)
    module = node
    while module is not None and not isinstance(module, ast.Module):
        module = parents.get(id(module))
    module_entries = (
        _named_binding_entries(module, name) if module is not None else [])
    latest_module = _latest_binding(module_entries) if module_entries else None
    return shadowed_binding_at(
        node, name, parents, cache,
        include_module=not isinstance(latest_module, ast.Delete),
        module_exclude_ids=module_exclude_ids,
        include_imports=include_imports)

def _lv10_prepare_builtin_call_shadows(roots: Any, tree: ast.AST) -> None:
    parents = parent_map_of(tree)
    cache: dict[tuple, set[str]] = {}
    builtin_names = frozenset(
        _LV10_LAZY_ITERATOR_BUILTINS | _LV10_EMPTY_CONTAINER_CALLS
        | _LV10_OBSERVE_BUILTINS | {'range', 'next'}
    )
    for node in roots:
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id in builtin_names):
            continue
        _LV10_CALL_SHADOWS[node] = _call_name_shadowed(
            node, node.func.id, parents, cache)

def _lv10_call_is_shadowed(node: ast.Call) -> bool:
    return _LV10_CALL_SHADOWS.get(node, False)

_LV39_BUILTIN_NAMES = frozenset({'sorted', 'reversed', 'map', 'filter'})
_LV39_RE_FUNCS = frozenset({'sub', 'subn', 'split', 'findall', 'finditer'})
def _lv39_re_binding_name(alias: ast.alias) -> str | None:
    if alias.name == 're':
        return alias.asname or 're'
    if alias.name.startswith('re.') and alias.asname is None:
        return 're'
    return None
def _lv39_re_import_sites(
        tree: ast.AST, parents: dict[int, ast.AST],
) -> dict[str, list[tuple[ast.Import, ast.AST]]]:
    sites: dict[str, list[tuple[ast.Import, ast.AST]]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Import):
            continue
        scope = nearest_scope(parents, node)
        if scope is None:
            continue
        for alias in node.names:
            name = _lv39_re_binding_name(alias)
            if name is not None:
                sites.setdefault(name, []).append((node, scope))
    return sites
def _lv39_re_from_import_sites(
        tree: ast.AST, parents: dict[int, ast.AST],
) -> dict[str, list[tuple[ast.ImportFrom, ast.AST, str]]]:
    sites: dict[str, list[tuple[ast.ImportFrom, ast.AST, str]]] = {}
    for node in walk_nodes(tree):
        if (not isinstance(node, ast.ImportFrom)
                or node.level != 0 or node.module != 're'):
            continue
        scope = nearest_scope(parents, node)
        if scope is None:
            continue
        for alias in node.names:
            if alias.name not in _LV39_RE_FUNCS:
                continue
            local = alias.asname or alias.name
            sites.setdefault(local, []).append(
                (node, scope, f're.{alias.name}'))
    return sites
def _lv39_import_visible(
        call: ast.Call, import_node: ast.Import | ast.ImportFrom,
        import_scope: ast.AST,
        parents: dict[int, ast.AST],
) -> bool:
    ancestor: ast.AST | None = call
    while ancestor is not None and ancestor is not import_scope:
        ancestor = parents.get(id(ancestor))
    if ancestor is None:
        return False
    call_scope = nearest_scope(parents, call)
    if call_scope is import_scope:
        call_pos = (call.lineno, call.col_offset)
        return call_pos >= node_end_position(import_node)
    if isinstance(import_scope, ast.ClassDef):
        return False
    cur: ast.AST | None = call
    while cur is not None and cur is not import_scope:
        if isinstance(cur, ast.ClassDef):
            class_pos = (cur.lineno, cur.col_offset)
            return class_pos >= node_end_position(import_node)
        if isinstance(cur, FUNC_SCOPE_NODES):
            return True
        cur = parents.get(id(cur))
    return False
def _lv39_pure_func_name(
        call: ast.Call, shadowed: set[str] | frozenset[str],
        re_aliases: dict[str, frozenset[int]],
        direct_re_imports: dict[str, list[tuple[ast.ImportFrom, ast.AST, str]]],
        parents: dict[int, ast.AST]) -> str | None:
    f = call.func
    if isinstance(f, ast.Name):
        visible = [
            (import_node, scope, canonical)
            for import_node, scope, canonical in direct_re_imports.get(f.id, ())
            if _lv39_import_visible(call, import_node, scope, parents)
        ]
        visible_import_ids = frozenset(id(item[0]) for item in visible)
        if visible and not _ordered_call_name_shadowed(
                call, f.id, parents, visible_import_ids):
            return max(
                visible, key=lambda item: node_end_position(item[0]))[2]
        if f.id in _LV39_BUILTIN_NAMES:
            return None if f.id in shadowed else f.id
        return None
    if not (isinstance(f, ast.Attribute) and f.attr in _LV39_RE_FUNCS
            and isinstance(f.value, ast.Name)):
        return None
    re_name = f.value.id
    if re_name not in re_aliases or _ordered_call_name_shadowed(
            call, re_name, parents, re_aliases[re_name]):
        return None
    return 're.' + f.attr
def check_LV39(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    shadow_cache: dict[tuple, set[str]] = {}
    re_imports = _lv39_re_import_sites(tree, parents)
    direct_re_imports = _lv39_re_from_import_sites(tree, parents)
    for node in roots:
        if not isinstance(node, ast.Expr):
            continue
        if not isinstance(node.value, ast.Call):
            continue
        shadowed = {
            name for name in _LV39_BUILTIN_NAMES
            if _call_name_shadowed(node.value, name, parents, shadow_cache)
        }
        re_aliases = {
            name: frozenset(
                id(import_node) for import_node, scope in sites
                if _lv39_import_visible(
                    node.value, import_node, scope, parents))
            for name, sites in re_imports.items()
        }
        re_aliases = {name: ids for name, ids in re_aliases.items() if ids}
        bad_name = _lv39_pure_func_name(
            node.value, shadowed, re_aliases, direct_re_imports, parents)
        if not bad_name:
            continue
        issues.append(make_issue(
            'LV-39', 'P2', 'logic_correctness', filepath, node.lineno,
            f'{bad_name}(...) 结果作独立语句丢弃：排序/变换静默失效',
            (
                f'``{bad_name}`` 是纯函数——返回新值、不修改原对象；'
                '作为独立语句调用时返回值直接丢弃，排序/替换/过滤'
                '整体未生效，后续消费逻辑建立在「已变更」的假象上，'
                '静默产生错误结果且无任何报错信号。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：``list.sort()``（原地、返回 None）与 '
                '``sorted()``（返回新列表）语义混用认知错位；\n'
                'str 方法（B22 域）与 re.sub 的返回值消费遗漏。\n'
                '修复策略：接收返回值——``items = sorted(items)`` /\n'
                '``s = re.sub(p, r, s)``；确需就地变更用原地方言\n'
                '``items.sort()`` / ``items.reverse()``。\n'
                '参考标准：CPython 内置 sorted/map/filter/reversed 与 '
                're.sub 返回值契约（纯函数，非原地）'
            ),
            'pure-call-result-discarded',
        ))
    return issues
def _lv54_binding_form(node: ast.AST) -> tuple[ast.expr | None, list[str], str] | None:
    if isinstance(node, ast.Assign):
        names = [t.id for t in node.targets if isinstance(t, ast.Name)]
        if not names:
            return None
        value = node.value
        while isinstance(value, ast.NamedExpr):
            value = value.value
        return value, names, '赋值'
    if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
        value = node.value
        while isinstance(value, ast.NamedExpr):
            value = value.value
        return value, [node.target.id], '赋值'
    if isinstance(node, ast.NamedExpr) and isinstance(node.target, ast.Name):
        value = node.value
        while isinstance(value, ast.NamedExpr):
            value = value.value
        return value, [node.target.id], '海象绑定'
    return None
def _lv54_issue(node: ast.AST, target_name: str, form: str,
                filepath: Any, src_lines: list[str]) -> dict[str, Any]:
    return make_issue(
        'LV-54', 'P1', 'logic_correctness', filepath, node.lineno,
        f'print() 返回值{form} ``{target_name}``：恒 None 落绑',
        (
            f'``{target_name} = print(...)`` ——print() 的返回契约'
            f'恒为 None，``{target_name}`` 从绑定起即 None；下游'
            '对它做拼接/算术即 TypeError 后移，做 ``if '
            f'{target_name}:`` 恒假形成静默守卫失效。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：print 的副作用契约是「输出到 stdout」，返回值固定\n'
            '为 None；混淆副作用与返回值两重语义。\n'
            f'修复策略：删除 {form}（保留 print 独立语句），或把\n'
            '意图改为「return/产出值」（改函数返回值而非 print）。\n'
            '参考标准：print() 签名契约（builtins.print → None）'
        ),
        'print-return-value-binding',
    )
def check_LV54(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    shadow_cache: dict[tuple[int, frozenset[int]], set[str]] = {}
    for node in roots:
        _bound = _lv54_binding_form(node)
        if _bound is None:
            continue
        value, target_names, form = _bound
        if not (isinstance(value, ast.Call)
                and isinstance(value.func, ast.Name)
                and value.func.id == 'print'):
            continue
        if _call_name_shadowed(value, 'print', parents, shadow_cache):
            continue
        issues.extend(
            _lv54_issue(node, target_name, form, filepath, src_lines)
            for target_name in target_names)
    return issues
def _lv56_async_definitions(
        tree: ast.AST, parents: dict[int, ast.AST],
) -> dict[str, list[tuple[ast.AsyncFunctionDef, ast.AST]]]:
    definitions: dict[str, list[tuple[ast.AsyncFunctionDef, ast.AST]]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.AsyncFunctionDef) or node.decorator_list:
            continue
        if any(isinstance(sub, (ast.Yield, ast.YieldFrom))
               for stmt in node.body for sub in iter_nodes_outside(stmt)):
            continue
        scope = nearest_scope(parents, node)
        if scope is None:
            continue
        definitions.setdefault(node.name, []).append((node, scope))
    return definitions
def _lv56_definition_visible(
        call: ast.Call, definition: ast.AsyncFunctionDef,
        definition_scope: ast.AST, parents: dict[int, ast.AST],
) -> bool:
    if isinstance(definition_scope, ast.ClassDef):
        if nearest_scope(parents, call) is not definition_scope:
            return False
        call_pos = (call.lineno, call.col_offset)
        return call_pos >= node_end_position(definition)
    cur: ast.AST | None = call
    visible = False
    while cur is not None:
        if cur is definition_scope:
            visible = True
            break
        cur = parents.get(id(cur))
    if not visible:
        return False
    if nearest_scope(parents, call) is definition_scope:
        call_pos = (call.lineno, call.col_offset)
        return call_pos >= node_end_position(definition)
    cur = call
    while cur is not None and cur is not definition_scope:
        if isinstance(cur, ast.ClassDef):
            class_pos = (cur.lineno, cur.col_offset)
            return class_pos >= node_end_position(definition)
        if isinstance(cur, FUNC_SCOPE_NODES):
            return True
        cur = parents.get(id(cur))
    return False
def _lv56_relevant_scopes(
        call: ast.Call, parents: dict[int, ast.AST],
):
    current_scope = nearest_scope(parents, call)
    cur = parents.get(id(call))
    in_function = False
    class_checked = False
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            in_function = True
            yield cur, cur is current_scope
        elif isinstance(cur, ast.ClassDef):
            if not in_function and not class_checked:
                yield cur, cur is current_scope
            class_checked = True
        elif isinstance(cur, ast.Module):
            yield cur, cur is current_scope
        cur = parents.get(id(cur))
def _ordered_call_name_shadowed(
        call: ast.Call, name: str, parents: dict[int, ast.AST],
        accepted_ids: frozenset[int],
) -> bool:
    position = (call.lineno, call.col_offset)
    for scope, is_current in _lv56_relevant_scopes(call, parents):
        entries = _named_binding_entries(scope, name)
        prior = [
            (node, value) for node, value in entries
            if (getattr(node, 'lineno', -1),
                getattr(node, 'col_offset', -1)) <= position
        ] if is_current else entries
        if prior:
            return _binding_shadows_name(
                _latest_binding(prior), accepted_ids, include_imports=True)
        if (is_current and entries and isinstance(
                scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))):
            return True
        if (isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
                and name in param_names(scope)):
            return True
    return False
def check_LV56(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    parents = parent_map_of(tree)
    definitions = _lv56_async_definitions(tree, parents)
    if not definitions:
        return issues
    async_ids = frozenset(
        id(node) for entries in definitions.values() for node, _scope in entries)
    src_lines = source_lines(source)
    for node in roots:
        if not isinstance(node, ast.Expr):
            continue
        call = node.value
        if not (isinstance(call, ast.Call)
                and isinstance(call.func, ast.Name)
                and call.func.id in definitions):
            continue
        fname = call.func.id
        if not any(_lv56_definition_visible(call, definition, scope, parents)
                   for definition, scope in definitions[fname]):
            continue
        if _ordered_call_name_shadowed(call, fname, parents, async_ids):
            continue
        issues.append(make_issue(
            'LV-56', 'P1', 'logic_correctness', filepath, node.lineno,
            f'async def ``{fname}`` 裸调用丢弃协程：函数体永不执行',
            (
                f'``{fname}`` 是调用点可见的 async def——该调用只创建'
                f'协程对象就把结果丢弃，``{fname}`` 的函数体一次都'
                '不会执行；运行时仅产生 RuntimeWarning，业务路径整体'
                '静默失效。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：async def 的调用语义=造协程，帧推进依赖\n'
                'await/事件循环接管；裸调用等价「点亮即扔」。\n'
                '修复策略：异步上下文 ``await ' + fname + '(...)``；\n'
                f'同步入口 ``asyncio.run({fname}(...))``；并发编排\n'
                f'``asyncio.create_task({fname}(...))``（持有 task）。\n'
                '参考标准：awaitable/coroutine 执行协议（PEP 492）'
            ),
            'bare-async-call-coroutine-discarded',
        ))
    return issues

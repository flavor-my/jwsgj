from __future__ import annotations

import ast
import logging
from collections.abc import Callable
from typing import Any, NamedTuple

from jwsgj.prevention_scope_facts import (
    aligned_unpack_pairs,
    binding_evaluation_position,
    bound_names,
    bound_names_of,
    child_inherited_shadow,
    child_scopes,
    definition_outer_node_ids,
    is_none_constant,
    iter_binding_entries,
    make_issue,
    nearest_scope,
    param_names,
    parent_map_of,
    rebound_binding_names,
    run_scope_scan,
    scan_context,
    scope_body_stmts,
    scope_local_bindings,
    scope_nodes_with_shadow,
    scoped_shadow_map,
    snippet_of,
    statically_empty_iterable,
    walk_nodes,
)

__all__ = [
    'check_LV01',
    'check_LV04',
    'check_LV33',
    'check_LV50',
    'check_LV52',
    'check_LV53',
    'check_LV58',
]
_log = logging.getLogger(__name__)
_log.info("prevention_literal_truth 条件真值与比较语义域检测器已加载：%d 项导出", len(__all__))
_EMPTY_SHADOW: frozenset[str] = frozenset()
def _ordered_binding_positions(scope: ast.AST) -> dict[str, tuple[int, int]]:
    positions: dict[str, tuple[int, int]] = {}
    for node, name, _value in iter_binding_entries(scope_body_stmts(scope)):
        position = binding_evaluation_position(node)
        positions[name] = min(position, positions.get(name, position))
    for child in child_scopes(scope):
        position = binding_evaluation_position(child)
        positions[child.name] = min(
            position, positions.get(child.name, position))
    return positions
def _global_binding_names(
        scope: ast.AST, positions: dict[str, tuple[int, int]],
) -> frozenset[str]:
    declared = {
        name
        for node, _shadow in scope_nodes_with_shadow(scope)
        if isinstance(node, ast.Global)
        for name in node.names
    }
    return frozenset(declared.intersection(positions))
def _evaluation_shadow_map(tree: ast.AST) -> dict[int, frozenset[str]]:
    shadows = scoped_shadow_map(tree)
    if not isinstance(tree, ast.AST):
        return shadows
    facts: dict[int, tuple[
        frozenset[str], dict[str, tuple[int, int]], frozenset[str],
    ]] = {}
    def scope_facts(scope: ast.AST):
        key = id(scope)
        if key not in facts:
            positions = _ordered_binding_positions(scope)
            global_names = _global_binding_names(scope, positions)
            facts[key] = (
                frozenset(scope_local_bindings(scope)) | global_names,
                positions,
                global_names,
            )
        return facts[key]
    def remove_future_bindings(
            scope: ast.AST, node: ast.AST,
            inherited: frozenset[str], local: frozenset[str]) -> None:
        if not hasattr(node, 'lineno'):
            return
        own, positions, global_names = scope_facts(scope)
        is_module_or_class = isinstance(scope, (ast.Module, ast.ClassDef))
        if not is_module_or_class and not global_names:
            return
        node_position = (node.lineno, node.col_offset)
        current = set(shadows.get(id(node), _EMPTY_SHADOW))
        names = own if is_module_or_class else global_names
        for name in names:
            if name in inherited or name in local:
                continue
            position = positions.get(name)
            if position is None:
                continue
            if position > node_position:
                current.discard(name)
            elif name in global_names:
                current.add(name)
        shadows[id(node)] = frozenset(current)
    def visit(
            scope: ast.AST, inherited: frozenset[str],
            outer_scope: ast.AST | None = None,
            outer_inherited: frozenset[str] = _EMPTY_SHADOW) -> None:
        own, _positions, _global_names = scope_facts(scope)
        visible = inherited | own
        outer_ids = definition_outer_node_ids(scope)
        for node, local in scope_nodes_with_shadow(scope):
            if id(node) in outer_ids:
                if outer_scope is not None:
                    remove_future_bindings(
                        outer_scope, node, outer_inherited, local)
            else:
                remove_future_bindings(scope, node, inherited, local)
        child_inherited = child_inherited_shadow(scope, visible, inherited)
        for child in child_scopes(scope):
            visit(child, child_inherited, scope, inherited)
    visit(tree, _EMPTY_SHADOW)
    return shadows
def _iter_compare_pairs(node: ast.Compare):
    prev: ast.AST = node.left
    for op, comp in zip(node.ops, node.comparators, strict=True):
        yield prev, op, comp
        prev = comp
def _child_inheritance(facts: _LV53ScopeFacts,
                       scope: ast.AST,
                       child: ast.AST) -> frozenset[str]:
    if isinstance(child, ast.ClassDef):
        return facts.input_at.get(id(child), facts.inherited)
    return (facts.inherited if isinstance(scope, ast.ClassDef)
            else facts.final_input)
_NUMERIC_LITERAL_TYPES = (bool, int, float, complex)
def _signed_numeric_operand(node: ast.AST) -> Any:
    if not (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.USub, ast.UAdd))
            and isinstance(node.operand, ast.Constant)):
        return None
    value = node.operand.value
    if not isinstance(value, _NUMERIC_LITERAL_TYPES):
        return None
    return -value if isinstance(node.op, ast.USub) else value
_LV01_VALUE_COMPARE_OPS = (ast.Eq, ast.NotEq, ast.Lt, ast.LtE,
                           ast.Gt, ast.GtE, ast.In, ast.NotIn)
_LV01_NOT_LITERAL = object()
class _LV01Literal(NamedTuple):
    text: str
    truth: bool
def _lv01_container_truth(node: ast.AST) -> bool | None:
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        if any(not isinstance(elt, ast.Starred) for elt in node.elts):
            return True
        return None if node.elts else False
    if isinstance(node, ast.Dict):
        if any(key is not None for key in node.keys):
            return True
        return None if node.keys else False
    return None
def _lv01_bare_literal_value(node: ast.AST) -> Any:
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        inner = _lv01_bare_literal_value(node.operand)
        if inner is _LV01_NOT_LITERAL:
            return inner
        return _LV01Literal(f'not {inner.text}', not inner.truth)
    if isinstance(node, ast.Constant):
        value = node.value
        if value is Ellipsis:
            return _LV01Literal('...', True)
        if value is None or isinstance(value, (bool, int, float, complex,
                                               str, bytes)):
            return _LV01Literal(repr(value), bool(value))
        return _LV01_NOT_LITERAL
    container_truth = _lv01_container_truth(node)
    if container_truth is not None:
        return _LV01Literal(ast.unparse(node), container_truth)
    signed = _signed_numeric_operand(node)
    return (_LV01_NOT_LITERAL if signed is None
            else _LV01Literal(repr(signed), bool(signed)))
def _lv01_chain_leaves(node: ast.AST):
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        if _lv01_bare_literal_value(node) is not _LV01_NOT_LITERAL:
            yield node
        else:
            yield from _lv01_chain_leaves(node.operand)
        return
    if isinstance(node, ast.BoolOp):
        for value in node.values:
            yield from _lv01_chain_leaves(value)
        return
    yield node
def _lv01_has_value_compare(node: ast.BoolOp) -> bool:
    return any(isinstance(core, ast.Compare)
               and any(isinstance(op, _LV01_VALUE_COMPARE_OPS)
                       for op in core.ops)
               for core in _lv01_chain_leaves(node))
def _lv01_bare_literals_desc(node: ast.BoolOp) -> str:
    values = (_lv01_bare_literal_value(v) for v in _lv01_chain_leaves(node))
    return ' / '.join(value.text for value in values
                      if value is not _LV01_NOT_LITERAL)
def _lv01_literal_truth(node: ast.AST) -> bool | None:
    value = _lv01_bare_literal_value(node)
    return None if value is _LV01_NOT_LITERAL else value.truth
def _lv01_expression_truth(node: ast.AST) -> bool | None:
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        inner = _lv01_expression_truth(node.operand)
        return None if inner is None else not inner
    if isinstance(node, ast.BoolOp):
        truths = [_lv01_expression_truth(value) for value in node.values]
        if isinstance(node.op, ast.Or):
            if any(truth is True for truth in truths):
                return True
            return False if all(truth is False for truth in truths) else None
        if any(truth is False for truth in truths):
            return False
        return True if all(truth is True for truth in truths) else None
    return _lv01_literal_truth(node)
_LV01_VERDICT_SEMANTICS = {
    '恒真': '裸字面量为真值——链实际语义是「比较结果 or True」，'
            '条件恒真，分支被无条件进入',
    '恒假': '裸字面量为假值——链实际语义是「比较结果 and False」，'
            '条件恒假，分支永不进入',
    '退化': '链真值退化为各比较结果的布尔组合——裸字面量不参与'
            '判定，书写意图的多值判断被静默丢弃',
}
def _lv01_chain_verdict(node: ast.BoolOp) -> str:
    truth = _lv01_expression_truth(node)
    if truth is True:
        return '恒真'
    return '恒假' if truth is False else '退化'
_LV01_NEGATED_VERDICTS = {'恒真': '恒假', '恒假': '恒真'}
def _lv01_enclosing_negated(node: ast.BoolOp,
                            parents: dict[int, ast.AST]) -> bool:
    negated = False
    outermost: ast.AST = node
    parent = parents.get(id(node))
    while isinstance(parent, ast.UnaryOp) and isinstance(parent.op, ast.Not):
        negated = not negated
        outermost = parent
        parent = parents.get(id(parent))
    is_full_condition = (
        isinstance(parent, (ast.If, ast.While, ast.IfExp, ast.Assert))
        and parent.test is outermost
    )
    return negated and is_full_condition
def _lv01_verdict_semantics(chain_verdict: str, negated: bool) -> str:
    if not negated or chain_verdict not in _LV01_NEGATED_VERDICTS:
        return _LV01_VERDICT_SEMANTICS[chain_verdict]
    verdict = _LV01_NEGATED_VERDICTS[chain_verdict]
    branch = ('分支永不进入' if verdict == '恒假'
              else '分支被无条件进入')
    return (f'原比较链{chain_verdict}，外层 ``not`` 使整体条件反转为'
            f'{verdict}，{branch}')
def _lv01_is_nested_chain(node: ast.BoolOp, parents: dict[int, ast.AST]) -> bool:
    parent = parents.get(id(node))
    while isinstance(parent, ast.UnaryOp) and isinstance(parent.op, ast.Not):
        parent = parents.get(id(parent))
    return isinstance(parent, ast.BoolOp)
def check_LV01(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    ctx = scan_context(tree, source)
    if ctx is None:
        return []
    issues, src_lines = ctx
    parents = parent_map_of(tree)
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.BoolOp) and _lv01_has_value_compare(node)):
            continue
        if _lv01_is_nested_chain(node, parents):
            continue
        bare_desc = _lv01_bare_literals_desc(node)
        if not bare_desc:
            continue
        op_name = 'or' if isinstance(node.op, ast.Or) else 'and'
        chain_verdict = _lv01_chain_verdict(node)
        negated = _lv01_enclosing_negated(node, parents)
        verdict = (_LV01_NEGATED_VERDICTS.get(chain_verdict, chain_verdict)
                   if negated else chain_verdict)
        label = {'恒真': '恒真比较链', '恒假': '恒假比较链',
                 '退化': '比较链真值退化'}[verdict]
        issues.append(make_issue(
            'LV-01', 'P1', 'logic_correctness', filepath, node.lineno,
            f'{label}：{op_name} 链中裸字面量 {bare_desc} 被静默求值为 truthiness',
            (
                f'``{op_name}`` 链中的裸字面量 {bare_desc} 按 truthiness '
                f'参与短路求值：{_lv01_verdict_semantics(chain_verdict, negated)}；'
                '与书写意图（多值成员判断）不符，分支走向永久错误'
                '且无任何异常信号。'
            ),
            snippet_of(src_lines, node.lineno),
            (
                '根因：自然语言「等于 1 或 2」直译成 ``== 1 or 2``，'
                '比较运算符优先级高于 or，裸操作数脱离了比较语境。\n'
                '修复策略：多值成员判断用 ``x in (1, 2)``；多条件独立'
                '判断确保每个操作数都是完整布尔表达式（``x == 1 or '
                'x == 2``）。\n'
                '参考标准：恒真比较链缺陷模式（Python 语言参考布尔运算 truthiness 语义）'
            ),
            'tautological-compare-chain',
        ))
    return issues
def _lv04_is_none_guard_compare(node: ast.AST) -> ast.Compare | None:
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return None
    if not isinstance(node.ops[0], (ast.Is, ast.IsNot)):
        return None
    return node if len(node.comparators) == 1 else None
def _lv04_guard_name(node: ast.AST) -> str | None:
    while isinstance(node, ast.Attribute):
        node = node.value
    return node.id if isinstance(node, ast.Name) else None
def _lv04_guard_expression(node: ast.AST) -> ast.AST:
    if isinstance(node, ast.NamedExpr):
        return ast.Name(id=node.target.id, ctx=ast.Load())
    return node
def _lv04_none_guard(node: ast.AST) -> _LV04Guard | None:
    compare = _lv04_is_none_guard_compare(node)
    if compare is None:
        return None
    protects = isinstance(compare.ops[0], ast.IsNot)
    left = _lv04_guard_expression(compare.left)
    right = _lv04_guard_expression(compare.comparators[0])
    if _lv04_guard_name(left) is not None and is_none_constant(right):
        return _LV04Guard(left, protects)
    if _lv04_guard_name(right) is not None and is_none_constant(left):
        return _LV04Guard(right, protects)
    return None
class _LV04Guard(NamedTuple):
    expression: ast.AST
    protects_access: bool
_LV04Leaf = tuple[ast.AST, tuple[_LV04Guard, ...]]
_LV04_EAGER_GENERATOR_CONSUMERS = frozenset({
    'all', 'any', 'dict', 'frozenset', 'list', 'max', 'min', 'set',
    'sorted', 'sum', 'tuple', 'next',
})
_LV04_EAGER_GENERATOR_ALLOWED_KEYWORDS = {
    'max': frozenset({'default', 'key'}),
    'min': frozenset({'default', 'key'}),
    'sorted': frozenset({'key', 'reverse'}),
}
def _lv04_chain_leaves(values: list[ast.AST], guards: list[_LV04Guard],
                       leaves: list[_LV04Leaf]) -> list[_LV04Guard]:
    current = list(guards)
    for value in values:
        if isinstance(value, ast.BoolOp) and isinstance(value.op, ast.And):
            current = _lv04_chain_leaves(value.values, current, leaves)
            continue
        leaves.append((value, tuple(current)))
        guard = _lv04_none_guard(value)
        if guard is not None:
            current.append(guard)
    return current
def _lv04_locally_guarded_access_ids(
        value: ast.AST, guarded: ast.AST, guard_name: str) -> set[int]:
    expected = ast.dump(guarded)
    protected: set[int] = set()
    for node in walk_nodes(value):
        if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And)):
            continue
        leaves: list[_LV04Leaf] = []
        _lv04_chain_leaves(node.values, [], leaves)
        for leaf, guards in leaves:
            if not any(guard.protects_access
                       and ast.dump(guard.expression) == expected
                       for guard in guards):
                continue
            for sub, shadow in scope_nodes_with_shadow(leaf):
                if (guard_name not in shadow
                        and isinstance(sub, ast.Attribute)
                        and not isinstance(sub.ctx, ast.Store)
                        and ast.dump(sub.value) == expected):
                    protected.add(id(sub))
    return protected
def _lv04_deferred_expression_ids(
        value: ast.AST,
        shadows: dict[int, frozenset[str]] | None = None,
) -> set[int]:
    parents = parent_map_of(value)
    local_shadows = {id(node): shadow
                     for node, shadow in scope_nodes_with_shadow(value)}
    deferred: set[int] = set()
    def mark(root: ast.AST) -> None:
        deferred.update(id(sub) for sub in walk_nodes(root))
    for node in walk_nodes(value):
        if isinstance(node, ast.Lambda):
            parent = parents.get(id(node))
            immediately_called = (
                isinstance(parent, ast.Call) and parent.func is node)
            if not immediately_called:
                mark(node.body)
            continue
        if not isinstance(node, ast.GeneratorExp):
            continue
        parent = parents.get(id(node))
        consumer_name = (parent.func.id
                         if isinstance(parent, ast.Call)
                         and isinstance(parent.func, ast.Name) else '')
        keyword_names = ({kw.arg for kw in parent.keywords}
                         if isinstance(parent, ast.Call) else set())
        keywords_supported = (
            all(kw.arg is not None for kw in parent.keywords)
            and (consumer_name == 'dict' or keyword_names <= (
                _LV04_EAGER_GENERATOR_ALLOWED_KEYWORDS.get(
                    consumer_name, _EMPTY_SHADOW)))
        ) if isinstance(parent, ast.Call) else False
        eagerly_consumed = (
            isinstance(parent, ast.Call)
            and 1 <= len(parent.args) <= (
                2 if consumer_name == 'next' else 1)
            and parent.args[0] is node
            and keywords_supported
            and consumer_name in _LV04_EAGER_GENERATOR_CONSUMERS
            and consumer_name not in (
                shadows if shadows is not None else local_shadows
            ).get(id(parent), local_shadows.get(id(parent), _EMPTY_SHADOW)))
        if eagerly_consumed:
            continue
        for index, generator in enumerate(node.generators):
            if index:
                mark(generator.iter)
            mark(generator.target)
            for condition in generator.ifs:
                mark(condition)
        mark(node.elt)
    return deferred
def _lv04_unguarded_access_line(
        value: ast.AST, guarded: ast.AST, guard_name: str,
        already_guarded: bool,
        shadows: dict[int, frozenset[str]] | None = None,
) -> int | None:
    if already_guarded:
        return None
    expected = ast.dump(guarded)
    protected = _lv04_locally_guarded_access_ids(value, guarded, guard_name)
    deferred = _lv04_deferred_expression_ids(value, shadows)
    for sub, shadow in scope_nodes_with_shadow(value):
        if (guard_name in shadow or id(sub) in protected
                or id(sub) in deferred):
            continue
        if (isinstance(sub, ast.Attribute)
                and not isinstance(sub.ctx, ast.Store)
                and ast.dump(sub.value) == expected):
            return sub.lineno
    return None
def _lv04_make_inversion_issue(filepath: Any, src_lines: list[str],
                               guarded: str, access_line: int) -> dict[str, Any]:
    return make_issue(
        'LV-04', 'P1', 'null_safety', filepath, access_line,
        f'守卫顺序颠倒：{guarded} 的属性访问早于 ``{guarded} is [not] None`` 判断',
        (
            f'and 链中 ``{guarded}.<attr>`` 访问（行 {access_line}）'
            f'出现在 ``{guarded} is [not] None`` 守卫之前——{guarded}'
            f'为 None 时前段属性访问直接 AttributeError，守卫'
            f'排在后面永远保护不到，是死守卫。'
        ),
        snippet_of(src_lines, access_line),
        (
            '根因：复合守卫条件按业务语序书写，None 守卫被排到'
            '属性访问之后。\n'
            f'修复策略：把 ``{guarded} is not None`` 移到 and 链'
            '最前（守卫前置，短路保护后续访问）。\n'
            '参考标准：守卫顺序颠倒缺陷模式（Python 语言参考 and 短路求值语义）'
        ),
        'guard-order-inversion',
    )
def check_LV04(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    ctx = scan_context(tree, source)
    if ctx is None:
        return []
    issues, src_lines = ctx
    seen: set[tuple[int, str]] = set()
    parents = parent_map_of(tree)
    shadows = _evaluation_shadow_map(tree)
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And)):
            continue
        parent = parents.get(id(node))
        if isinstance(parent, ast.BoolOp) and isinstance(parent.op, ast.And):
            continue
        for guarded, access_line in _lv04_inversion_hits(
                node.values, shadows):
            name = ast.unparse(guarded)
            key = (access_line, name)
            if key in seen:
                continue
            seen.add(key)
            issues.append(_lv04_make_inversion_issue(
                filepath, src_lines, name, access_line))
    return issues
def _lv04_guard_active_before(
        leaves: list[_LV04Leaf], index: int, expected: str,
        guard_name: str) -> bool:
    active = False
    for value, _guards in leaves[:index]:
        if any(isinstance(sub, ast.NamedExpr)
               and sub.target.id == guard_name for sub in walk_nodes(value)):
            active = False
        guard = _lv04_none_guard(value)
        if (guard is not None and guard.protects_access
                and ast.dump(guard.expression) == expected):
            active = True
    return active
def _lv04_inversion_hits(
        values: list[ast.AST],
        shadows: dict[int, frozenset[str]] | None = None,
):
    leaves: list[_LV04Leaf] = []
    _lv04_chain_leaves(values, [], leaves)
    for index, (value, _guards_before) in enumerate(leaves):
        guard = _lv04_none_guard(value)
        if guard is None:
            continue
        guarded = guard.expression
        guard_name = _lv04_guard_name(guarded)
        if guard_name is None:
            continue
        expected_guard = ast.dump(guarded)
        for earlier_index, (earlier, _earlier_guards) in enumerate(
                leaves[:index]):
            already_guarded = _lv04_guard_active_before(
                leaves, earlier_index, expected_guard, guard_name)
            access_line = _lv04_unguarded_access_line(
                earlier, guarded, guard_name, already_guarded, shadows)
            if access_line is not None:
                yield guarded, access_line
def _lv33_starred_iterable_truth(node: ast.AST) -> bool | None:
    if isinstance(node, ast.Constant):
        return (bool(node.value)
                if isinstance(node.value, (str, bytes)) else None)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
        return _lv01_container_truth(node)
    return None
def _lv33_always_true_tuple(node: ast.AST) -> ast.Tuple | None:
    if not isinstance(node, ast.Assert):
        return None
    test = node.test
    if not isinstance(test, ast.Tuple) or not test.elts:
        return None
    if any(not isinstance(element, ast.Starred) for element in test.elts):
        return test
    for element in test.elts:
        if _lv33_starred_iterable_truth(element.value) is True:
            return test
    return None
def check_LV33(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    ctx = scan_context(tree, source)
    if ctx is None:
        return []
    issues, src_lines = ctx
    for node in walk_nodes(tree):
        test = _lv33_always_true_tuple(node)
        if test is None:
            continue
        second_msg = (len(test.elts) > 1
                      and isinstance(test.elts[1], ast.Constant)
                      and isinstance(test.elts[1].value, str))
        title = 'assert 元组恒真断言失效：元组非空恒真，校验永不触发'
        if len(test.elts) == 1:
            title = 'assert 单元素元组恒真断言失效：多写逗号，校验永不触发'
            desc = (
                '``assert (x,)`` 形态——单元素元组非空恒真，断言永不'
                '触发；意图是 ``assert x``，末尾多写的逗号把测试表达式'
                '变成了元组字面量。'
            )
        elif second_msg:
            desc = (
                '``assert (cond, msg)`` 笔误形态——元组整体非空恒真，'
                '断言分支不可达，参数校验/不变量检查整体失效且无任何'
                '报错信号；意图是 ``assert cond, msg``（msg 作为第二'
                '位置元素）。'
            )
        else:
            desc = (
                'assert 的测试表达式是非空元组字面量——元组恒真，'
                '断言永不触发；若意图是校验各元素真值，须拆为独立'
                '条件（``assert a and b``）。'
            )
        issues.append(make_issue(
            'LV-33', 'P1', 'logic_correctness', filepath, node.lineno,
            title, desc,
            snippet_of(src_lines, node.lineno),
            (
                '根因：msg 位置参数与 test 表达式同被括进括号（或误\n'
                '以元组为复合断言），test 成为元组字面量。\n'
                '修复策略：拆出元组——``assert cond, "msg"``；复合条件\n'
                '用 ``and``/``or`` 显式连接；校验类逻辑建议改显式\n'
                '``raise ValueError``（-O 优化模式下 assert 整体剥离，\n'
                'B31 同口径）。\n'
                '参考标准：CPython assert 语句两元素契约（test + 可选\n'
                'msg），元组真值语义（非空恒真）'
            ),
            'assert-tuple-always-true',
        ))
    return issues
_LV50_BUILTIN_PREDICATES = frozenset({
    'any', 'all', 'len', 'bool', 'callable', 'isinstance', 'issubclass',
    'hasattr',
})
def _lv50_operand_predicates(
        expr: ast.AST, shadow: set[str]) -> list[tuple[str, bool]]:
    if isinstance(expr, ast.UnaryOp) and isinstance(expr.op, ast.Not):
        return [(name, not negated)
                for name, negated in
                _lv50_operand_predicates(expr.operand, shadow)]
    if isinstance(expr, ast.BoolOp):
        hits: list[tuple[str, bool]] = []
        for value in expr.values:
            hits.extend(_lv50_operand_predicates(value, shadow))
        return hits
    if (isinstance(expr, ast.Name) and expr.id in _LV50_BUILTIN_PREDICATES
            and expr.id not in shadow):
        return [(expr.id, False)]
    return []
def _lv50_truth(expr: ast.AST, shadow: set[str]) -> bool | None:
    if isinstance(expr, ast.UnaryOp) and isinstance(expr.op, ast.Not):
        inner = _lv50_truth(expr.operand, shadow)
        return None if inner is None else not inner
    if isinstance(expr, ast.BoolOp):
        truths = [_lv50_truth(value, shadow) for value in expr.values]
        if isinstance(expr.op, ast.Or):
            if any(t is True for t in truths):
                return True
            return False if all(t is False for t in truths) else None
        if any(t is False for t in truths):
            return False
        return True if all(t is True for t in truths) else None
    if (isinstance(expr, ast.Name) and expr.id in _LV50_BUILTIN_PREDICATES
            and expr.id not in shadow):
        return True
    return None
def _lv50_verdict_text(verdict: bool | None, fname: str,
                       negated: bool) -> tuple[str, str]:
    if verdict is True and not negated:
        return (
            f'裸内建谓词函数对象作条件：{fname} 恒真，守卫失效',
            (
                f'``{fname}`` 是内建函数对象，非空容器语义的恒真值——'
                f'条件等价 ``if True``，分支恒走（while 形态则不可终止）。'
                f'意图是 ``{fname}(...)`` 调用判定结果，漏写调用括号'
                '使守卫静默失效。'
            ),
        )
    if verdict is False and negated:
        return (
            f'裸内建谓词取反作条件：not {fname} 恒假，守卫失效',
            (
                f'``not {fname}`` 是「非恒真值」——恒为 False，'
                '条件等价 ``if False``，分支永不进入，参数校验/'
                '不变量守卫整体失效且无任何报错信号。意图是 '
                f'``not {fname}(...)`` 判空/判无匹配。'
            ),
        )
    if negated:
        return (
            f'裸内建谓词取反作链操作数：not {fname} 恒假被静默丢弃',
            (
                f'``not {fname}`` 是「非恒真值」——恒为 False，作为 '
                '``and``/``or`` 链的操作数时该位置等价 ``and False`` / '
                '``or False``：and 链整体恒假（分支永不进入）、or 链'
                '退化为其余操作数，条件判定被静默丢弃且无异常信号。'
            ),
        )
    return (
        f'裸内建谓词函数对象作链操作数：{fname} 恒真被静默丢弃',
        (
            f'``{fname}`` 作为 ``and``/``or`` 链的操作数恒为真值，'
            '短路求值下该操作数不参与判定：误写形态使复合守卫退化'
            '为其余操作数，条件判定被静默丢弃且无异常信号。'
        ),
    )
def _lv50_issue(filepath: Any, src_lines: list[str], lineno: int,
                fname: str, verdict: bool | None,
                negated: bool) -> dict[str, Any]:
    title, description = _lv50_verdict_text(verdict, fname, negated)
    return make_issue(
        'LV-50', 'P1', 'logic_correctness', filepath, lineno,
        title, description,
        snippet_of(src_lines, lineno),
        (
            '根因：guard 表达式改写时丢调用括号（函数对象引用≠\n'
            '调用结果；Python 一等函数语义下对象本身合法作真值）。\n'
            f'修复策略：``{fname}(items)`` 补调用括号与实参；\n'
            '若意图判空容器用 ``if items:``（非空即真）；\n'
            f'取反判定用 ``not {fname}(items)``。\n'
            '参考标准：CPython 真值协议（函数对象非 __bool__ 定义，\n'
            '缺省恒真）'
        ),
        'bare-builtin-predicate-as-condition',
    )
def _lv50_scan_scope(
        scope: ast.AST, src_lines: list[str], filepath: Any,
        shadows: dict[int, frozenset[str]] | None = None,
        ) -> list[dict[str, Any]]:
    if shadows is None:
        shadows = _evaluation_shadow_map(scope)
    issues: list[dict[str, Any]] = []
    for node, local_shadow in scope_nodes_with_shadow(scope):
        test = _lv50_condition_test(node)
        if test is None:
            continue
        shadow = shadows.get(id(node), local_shadow)
        hits = _lv50_operand_predicates(test, shadow)
        if not hits:
            continue
        fname, negated = hits[0]
        verdict = _lv50_truth(test, shadow)
        issues.append(_lv50_issue(
            filepath, src_lines, node.lineno, fname, verdict, negated))
    for child in child_scopes(scope):
        issues.extend(_lv50_scan_scope(
            child, src_lines, filepath, shadows))
    return issues
def check_LV50(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    return run_scope_scan(tree, source, filepath, _lv50_scan_scope)
def _lv50_condition_test(node: ast.AST) -> ast.expr | None:
    if isinstance(node, (ast.If, ast.While, ast.IfExp, ast.Assert)):
        return node.test
    return None
_LV52_SINGLETON_LITERALS = frozenset({
    None, True, False, Ellipsis,
})
_LV52_FRESH_CONTAINER_CTORS = frozenset({'list', 'dict', 'set'})
def check_LV52(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    ctx = scan_context(tree, source)
    if ctx is None:
        return []
    issues, src_lines = ctx
    seen: set[tuple[int, str]] = set()
    shadows = _evaluation_shadow_map(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Compare):
            continue
        for kind in _lv52_hit_kinds(
                node, shadows.get(id(node), _EMPTY_SHADOW)):
            key = (node.lineno, kind)
            if key in seen:
                continue
            seen.add(key)
            issues.append(_lv52_make_issue(
                filepath, src_lines, node.lineno, kind))
    return issues
def _lv52_make_issue(filepath: Any, src_lines: list[str], lineno: int,
                     kind: str) -> dict[str, Any]:
    return make_issue(
        'LV-52', 'P2', 'logic_correctness', filepath, lineno,
        f'is 比较非单例字面量（{kind}）：identity 语义误用',
        (
            f'``is`` 判 identity（同一对象），``{kind}`` 字面量'
            '的值比较须 ``==``。小整数缓存/字符串驻留/常量折叠'
            '可让 ``x is <literal>`` 在当前解释器「碰巧成立」'
            '——运行时构造的等值对象即判假，属实现细节依赖的'
            '潜伏缺陷（ruff F632 同源）。'
        ),
        snippet_of(src_lines, lineno),
        (
            '根因：identity 与相等语义混淆（is 比对象地址，==\n'
            '走 __eq__ 协议）。\n'
            '修复策略：值比较改 ``==`` / ``!=``；is 仅用于单例\n'
            '判定（``x is None``/``is True``）与 sentinel 惯用法。\n'
            '参考标准：CPython 对象模型（id() 相等即 is，字面量\n'
            '折叠是实现级优化非语言契约）'
        ),
        'is-compare-non-singleton-literal',
    )
def _lv52_hit_kinds(node: ast.Compare, shadow: frozenset[str]):
    for prev, op, comp in _iter_compare_pairs(node):
        if not isinstance(op, (ast.Is, ast.IsNot)):
            continue
        for operand in (prev, comp):
            kind = _lv52_literal_kind(operand, shadow)
            if kind is not None:
                yield kind
                break
def _lv52_literal_kind(comp: ast.AST, shadow: frozenset[str]) -> str | None:
    if isinstance(comp, ast.Constant):
        if any(comp.value is lit for lit in _LV52_SINGLETON_LITERALS):
            return None
        return repr(comp.value)
    signed = _signed_numeric_operand(comp)
    if signed is not None:
        return repr(signed)
    if isinstance(comp, (ast.List, ast.Tuple, ast.Dict, ast.Set)):
        return type(comp).__name__ + ' 字面量'
    if (isinstance(comp, ast.Call) and isinstance(comp.func, ast.Name)
            and comp.func.id in _LV52_FRESH_CONTAINER_CTORS
            and comp.func.id not in shadow
            and not comp.args and not comp.keywords):
        return comp.func.id + '()'
    return None
_LV53_NUMERIC_TYPES = _NUMERIC_LITERAL_TYPES
_LV53_ORDERED_OPS = (ast.Lt, ast.LtE, ast.Gt, ast.GtE)
_LV53_OP_SYMBOLS = {ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>='}
def _lv53_numeric_literal_value(node: ast.AST) -> Any:
    value = (node.value if isinstance(node, ast.Constant)
             else _signed_numeric_operand(node))
    return value if isinstance(value, _LV53_NUMERIC_TYPES) else None
def _lv53_is_numeric_lit(node: ast.AST) -> bool:
    return _lv53_numeric_literal_value(node) is not None
def _lv53_literal_type_name(node: ast.AST) -> str:
    value = _lv53_numeric_literal_value(node)
    if isinstance(value, bool):
        return 'bool'
    if isinstance(value, int):
        return 'int'
    if isinstance(value, float):
        return 'float'
    if isinstance(value, complex):
        return 'complex'
    return 'int'
def _lv53_is_input_call(node: ast.AST,
                        shadow: frozenset = _EMPTY_SHADOW) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'input' and 'input' not in shadow)
def _lv53_input_call_at(
        node: ast.AST, shadow: frozenset, input_builtin: bool,
        input_binding_position: tuple[int, int] | None) -> bool:
    return (
        input_builtin
        and (input_binding_position is None
             or (node.lineno, node.col_offset) < input_binding_position)
        and _lv53_is_input_call(node, shadow)
    )
def _lv53_contains_input(
        node: ast.AST, known_input: frozenset[str],
        input_predicate: Callable[[ast.AST], bool] | None,
) -> bool:
    for sub in walk_nodes(node):
        if isinstance(sub, ast.Name) and sub.id in known_input:
            return True
        if (_lv53_is_input_call(sub)
                and (input_predicate is None or input_predicate(sub))):
            return True
    return False
def _lv53_string_expression_facts(
        node: ast.AST, known_input: frozenset[str],
        input_predicate: Callable[[ast.AST], bool] | None,
) -> tuple[bool, bool]:
    if (_lv53_is_input_call(node)
            and (input_predicate is None or input_predicate(node))):
        return True, True
    if isinstance(node, ast.Name) and node.id in known_input:
        return True, True
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return True, False
    if isinstance(node, ast.JoinedStr):
        return True, _lv53_contains_input(node, known_input, input_predicate)
    if not isinstance(node, ast.BinOp):
        return False, False
    left_is_string, left_from_input = _lv53_string_expression_facts(
        node.left, known_input, input_predicate)
    right_is_string, right_from_input = _lv53_string_expression_facts(
        node.right, known_input, input_predicate)
    if isinstance(node.op, ast.Add):
        if left_is_string and right_is_string:
            return True, left_from_input or right_from_input
        return False, False
    if isinstance(node.op, ast.Mult):
        if (left_is_string
                and isinstance(_lv53_numeric_literal_value(node.right), int)):
            return True, left_from_input
        if (right_is_string
                and isinstance(_lv53_numeric_literal_value(node.left), int)):
            return True, right_from_input
    return False, False
def _lv53_string_iteration_target(
        target: ast.AST, iterable: ast.AST, known_input: frozenset[str],
        input_predicate: Callable[[ast.AST], bool],
) -> str:
    if not isinstance(target, ast.Name):
        return ''
    is_string, from_input = _lv53_string_expression_facts(
        iterable, known_input, input_predicate)
    return target.id if is_string and from_input else ''
def _lv53_target_input_names(
        target: ast.AST, value: ast.AST,
        input_predicate: Callable[[ast.AST], bool] | None = None,
        *, known_input: frozenset[str] | None = None) -> set[str]:
    if isinstance(value, ast.IfExp):
        literal_truth = _lv53_condition_literal_truth(value.test)
        if literal_truth is True:
            return _lv53_target_input_names(
                target, value.body, input_predicate, known_input=known_input)
        if literal_truth is False:
            return _lv53_target_input_names(
                target, value.orelse, input_predicate, known_input=known_input)
        body_names = _lv53_target_input_names(
            target, value.body, input_predicate, known_input=known_input)
        other_names = _lv53_target_input_names(
            target, value.orelse, input_predicate, known_input=known_input)
        return body_names & other_names
    if isinstance(target, ast.Name):
        is_input = (_lv53_is_input_call(value)
                    and (input_predicate is None or input_predicate(value)))
        if not is_input and known_input is not None:
            is_string, from_input = _lv53_string_expression_facts(
                value, known_input, input_predicate)
            is_input = is_string and from_input
        return {target.id} if is_input else set()
    pairs = aligned_unpack_pairs(target, value)
    if pairs is None:
        return set()
    names: set[str] = set()
    for sub_target, sub_value in pairs:
        names |= _lv53_target_input_names(
            sub_target, sub_value, input_predicate, known_input=known_input)
    return names
def _lv53_input_binding_names(
        node: ast.AST,
        input_predicate: Callable[[ast.AST], bool] | None = None,
        *, known_input: frozenset[str] | None = None) -> set[str]:
    if isinstance(node, ast.Assign):
        names: set[str] = set()
        for target in node.targets:
            names |= _lv53_target_input_names(
                target, node.value, input_predicate, known_input=known_input)
        return names
    if (isinstance(node, (ast.AnnAssign, ast.NamedExpr))
            and node.value is not None):
        return _lv53_target_input_names(
            node.target, node.value, input_predicate, known_input=known_input)
    return set()
class _LV53ScopeFacts(NamedTuple):
    input_at: dict[int, frozenset[str]]
    inherited: frozenset[str]
    final_input: frozenset[str]
    input_builtin: bool
    unevaluated_ids: frozenset[int]
    input_binding_position: tuple[int, int] | None = None
def _lv53_statement_bindings(node: ast.AST) -> set[str]:
    if isinstance(node, ast.Delete):
        return rebound_binding_names(node)
    if isinstance(node, ast.Assign):
        return {name for target in node.targets
                for name in bound_names(target, include_params=False)}
    if isinstance(node, ast.AnnAssign):
        if node.value is None:
            return set()
        return bound_names(node.target, include_params=False)
    if isinstance(node, ast.AugAssign):
        if isinstance(node.op, (ast.Add, ast.Mult)):
            return set()
        return bound_names(node.target, include_params=False)
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return bound_names(node, include_params=False)
    return bound_names_of(node, include_params=False)
class _LV53Outcome(NamedTuple):
    state: frozenset[str]
    on_true: frozenset[str]
    on_false: frozenset[str]
def _lv53_merge_inputs(*states: frozenset[str]) -> frozenset[str]:
    if not states:
        return _EMPTY_SHADOW
    return frozenset(set.intersection(*(set(state) for state in states)))
def _lv53_condition_literal_truth(node: ast.AST) -> bool | None:
    value = node.value if isinstance(node, ast.NamedExpr) else node
    return _lv01_expression_truth(value)
def _lv53_parameter_annotations(node: ast.AST) -> list[ast.AST]:
    args = node.args
    parameters = [*args.posonlyargs, *args.args]
    if args.vararg is not None:
        parameters.append(args.vararg)
    parameters.extend(args.kwonlyargs)
    if args.kwarg is not None:
        parameters.append(args.kwarg)
    return [arg.annotation for arg in parameters
            if arg.annotation is not None]
def _lv53_statements_may_fallthrough(nodes: list[ast.stmt]) -> bool:
    for node in nodes:
        if isinstance(node, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
            return False
        if (isinstance(node, ast.If) and node.orelse
                and not _lv53_statements_may_fallthrough(node.body)
                and not _lv53_statements_may_fallthrough(node.orelse)):
            return False
    return True
def _lv53_straight_line_final_break(nodes: list[ast.stmt]) -> bool:
    if not nodes or not isinstance(nodes[-1], ast.Break):
        return False
    simple_prefix = (
        ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Expr, ast.Delete, ast.Pass,
    )
    return all(isinstance(node, simple_prefix) for node in nodes[:-1])
class _LV53Flow:
    def __init__(self, input_builtin: bool, *,
                 annotations_deferred: bool = False,
                 evaluate_variable_annotations: bool = True,
                 input_binding_position: tuple[int, int] | None = None,
                 class_bindings: frozenset[str] = _EMPTY_SHADOW) -> None:
        self.input_builtin = input_builtin
        self.input_binding_position = input_binding_position
        self.class_bindings = class_bindings
        self.annotations_deferred = annotations_deferred
        self.evaluate_variable_annotations = (
            evaluate_variable_annotations and not annotations_deferred)
        self.input_at: dict[int, frozenset[str]] = {}
        self.unevaluated_ids: set[int] = set()
    def _mark_unevaluated(self, node: ast.AST | list[ast.stmt]) -> None:
        nodes = node if isinstance(node, list) else [node]
        for item in nodes:
            self.unevaluated_ids.update(id(sub) for sub in walk_nodes(item))
    def _evaluate(self, node: ast.AST, inputs: frozenset[str],
                  record: bool = True) -> _LV53Outcome:
        shadows = {id(sub): shadow
                   for sub, shadow in scope_nodes_with_shadow(node)}
        return self._eval_node(node, inputs, shadows, record)
    @staticmethod
    def _same_outcome(state: frozenset[str]) -> _LV53Outcome:
        return _LV53Outcome(state, state, state)
    def _eval_node(
            self, node: ast.AST, inputs: frozenset[str],
            shadows: dict[int, frozenset[str]], record: bool,
    ) -> _LV53Outcome:
        if record:
            self.input_at[id(node)] = inputs
        shadow = shadows.get(id(node), _EMPTY_SHADOW)
        if isinstance(node, ast.AnnAssign) and not self.evaluate_variable_annotations:
            self.unevaluated_ids.update(id(sub) for sub in walk_nodes(node.annotation))
            current = inputs
            for child in ast.iter_child_nodes(node):
                if child is node.annotation:
                    continue
                current = self._eval_node(child, current, shadows, record).state
            return self._same_outcome(current)
        if isinstance(node, ast.NamedExpr):
            value = self._eval_node(node.value, inputs, shadows, record)
            current = set(value.state)
            name = node.target.id
            if name not in shadow:
                input_names = _lv53_input_binding_names(
                    node,
                    lambda value: _lv53_input_call_at(
                        value, shadow, self.input_builtin,
                        self.input_binding_position),
                    known_input=frozenset(current))
                if name in input_names:
                    current.add(name)
                else:
                    current.discard(name)
            state = frozenset(current)
            if record:
                self.input_at[id(node.target)] = state
            return self._same_outcome(state)
        if isinstance(node, ast.BoolOp):
            prefix_states: list[frozenset[str]] = []
            current = inputs
            result = self._same_outcome(inputs)
            reachable = True
            for value in node.values:
                value_result = self._eval_node(value, current, shadows, record)
                if not reachable:
                    if record:
                        self.unevaluated_ids.update(
                            id(sub) for sub in walk_nodes(value))
                    continue
                result = value_result
                literal_truth = _lv53_condition_literal_truth(value)
                if not ((isinstance(node.op, ast.And) and literal_truth is True)
                        or (isinstance(node.op, ast.Or)
                            and literal_truth is False)):
                    prefix_states.append(
                        result.on_false if isinstance(node.op, ast.And)
                        else result.on_true)
                current = (result.on_true if isinstance(node.op, ast.And)
                           else result.on_false)
                if ((isinstance(node.op, ast.And) and literal_truth is False)
                        or (isinstance(node.op, ast.Or) and literal_truth is True)):
                    reachable = False
            if isinstance(node.op, ast.And):
                on_true = result.on_true
                on_false = _lv53_merge_inputs(*prefix_states)
            else:
                on_true = _lv53_merge_inputs(*prefix_states)
                on_false = result.on_false
            chain_truth = _lv53_condition_literal_truth(node)
            if chain_truth is True:
                state = on_true
            elif chain_truth is False:
                state = on_false
            else:
                state = _lv53_merge_inputs(on_true, on_false)
            return _LV53Outcome(state, on_true, on_false)
        if isinstance(node, ast.Compare):
            current = self._eval_node(
                node.left, inputs, shadows, record).state
            prefix_states = []
            for comparator in node.comparators:
                current = self._eval_node(
                    comparator, current, shadows, record).state
                prefix_states.append(current)
            on_false = _lv53_merge_inputs(*prefix_states)
            return _LV53Outcome(
                _lv53_merge_inputs(current, on_false), current, on_false)
        if isinstance(node, ast.IfExp):
            test = self._eval_node(node.test, inputs, shadows, record)
            body = self._eval_node(
                node.body, test.on_true, shadows, record)
            other = self._eval_node(
                node.orelse, test.on_false, shadows, record)
            literal_truth = _lv53_condition_literal_truth(node.test)
            if literal_truth is True:
                self._mark_unevaluated(node.orelse)
                return body
            if literal_truth is False:
                self._mark_unevaluated(node.body)
                return other
            return _LV53Outcome(
                _lv53_merge_inputs(body.state, other.state),
                _lv53_merge_inputs(body.on_true, other.on_true),
                _lv53_merge_inputs(body.on_false, other.on_false))
        if isinstance(node, ast.Lambda):
            current = inputs
            for expression in (*node.args.defaults, *node.args.kw_defaults):
                if expression is not None:
                    current = self._eval_node(
                        expression, current, shadows, record).state
            body_inputs = frozenset(
                set(current) - self.class_bindings - param_names(node))
            self._eval_node(node.body, body_inputs, shadows, record)
            return self._same_outcome(current)
        if isinstance(node, (ast.ListComp, ast.SetComp,
                             ast.DictComp, ast.GeneratorExp)):
            current = inputs
            entry_state = inputs
            local_names: set[str] = set()
            for index, generator in enumerate(node.generators):
                current = self._eval_node(
                    generator.iter, current, shadows, record).state
                if index == 0:
                    entry_state = current
                iter_state = current
                target_names = bound_names(
                    generator.target, include_params=False)
                local_names.update(target_names)
                current = frozenset(
                    set(current) - self.class_bindings - target_names)
                if not generator.is_async:
                    target_name = _lv53_string_iteration_target(
                        generator.target, generator.iter, iter_state,
                        lambda value: _lv53_input_call_at(
                            value, shadows.get(id(value), _EMPTY_SHADOW),
                            self.input_builtin, self.input_binding_position))
                    if target_name:
                        current = current | frozenset({target_name})
                for condition in generator.ifs:
                    current = self._eval_node(
                        condition, current, shadows, record).on_true
            elements = ((node.key, node.value) if isinstance(node, ast.DictComp)
                        else (node.elt,))
            for element in elements:
                current = self._eval_node(
                    element, current, shadows, record).state
            outer_current = frozenset(
                (set(current) - local_names)
                | (set(entry_state) & (local_names | self.class_bindings)))
            state = (entry_state if isinstance(node, ast.GeneratorExp)
                     else _lv53_merge_inputs(entry_state, outer_current))
            return self._same_outcome(state)
        if isinstance(node, ast.Dict):
            current = inputs
            for key, value in zip(node.keys, node.values, strict=True):
                if key is not None:
                    current = self._eval_node(
                        key, current, shadows, record).state
                current = self._eval_node(
                    value, current, shadows, record).state
            return self._same_outcome(current)
        if isinstance(node, ast.Assign):
            current = self._eval_node(
                node.value, inputs, shadows, record).state
            for target in node.targets:
                current = self._eval_node(
                    target, current, shadows, record).state
            return self._same_outcome(current)
        current = inputs
        for child in ast.iter_child_nodes(node):
            current = self._eval_node(
                child, current, shadows, record).state
        return self._same_outcome(current)
    def evaluate(self, node: ast.AST,
                 inputs: frozenset[str]) -> frozenset[str]:
        return self._evaluate(node, inputs).state
    def _simple(self, node: ast.AST,
                inputs: frozenset[str]) -> frozenset[str]:
        evaluated = self.evaluate(node, inputs)
        current = set(evaluated)
        bindings = _lv53_statement_bindings(node)
        input_concat = False
        if (isinstance(node, ast.AugAssign)
                and isinstance(node.op, ast.Add)
                and isinstance(node.target, ast.Name)):
            value = (node.value.value if isinstance(node.value, ast.NamedExpr)
                     else node.value)
            is_string, from_input = _lv53_string_expression_facts(
                value, frozenset(evaluated),
                lambda value: _lv53_input_call_at(
                    value, _EMPTY_SHADOW, self.input_builtin,
                    self.input_binding_position))
            input_concat = is_string and from_input
        if input_concat:
            bindings = set()
            current.add(node.target.id)
        current.difference_update(bindings)
        current |= _lv53_input_binding_names(
            node,
            lambda value: _lv53_input_call_at(
                value, _EMPTY_SHADOW, self.input_builtin,
                self.input_binding_position),
            known_input=frozenset(evaluated))
        return frozenset(current)
    def _definition(self, node: ast.AST,
                    inputs: frozenset[str]) -> frozenset[str]:
        current = inputs
        is_function = isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        evaluated = ([
            *node.decorator_list, *node.args.defaults, *node.args.kw_defaults,
        ] if is_function else [
            *node.decorator_list, *node.bases,
            *(kw.value for kw in node.keywords),
        ])
        annotations = ([*_lv53_parameter_annotations(node), node.returns]
                       if is_function else [])
        if self.annotations_deferred:
            for expression in annotations:
                if expression is not None:
                    self.unevaluated_ids.update(
                        id(sub) for sub in walk_nodes(expression))
        else:
            evaluated.extend(annotations)
        for expression in evaluated:
            if expression is not None:
                current = self.evaluate(expression, current)
        self.input_at[id(node)] = frozenset(current)
        result = set(current)
        result.discard(node.name)
        return frozenset(result)
    def _if(self, node: ast.If, inputs: frozenset[str]) -> frozenset[str]:
        test = self._evaluate(node.test, inputs)
        body = self.statements(node.body, test.on_true)
        other = (self.statements(node.orelse, test.on_false)
                 if node.orelse else test.on_false)
        literal_truth = _lv53_condition_literal_truth(node.test)
        if literal_truth is True:
            self._mark_unevaluated(node.orelse)
            return body
        if literal_truth is False:
            self._mark_unevaluated(node.body)
            return other
        body_may_fallthrough = _lv53_statements_may_fallthrough(node.body)
        other_may_fallthrough = (
            _lv53_statements_may_fallthrough(node.orelse)
            if node.orelse else True)
        if not body_may_fallthrough and other_may_fallthrough:
            return other
        if body_may_fallthrough and not other_may_fallthrough:
            return body
        return body & other
    def _for(self, node: ast.For | ast.AsyncFor,
             inputs: frozenset[str]) -> frozenset[str]:
        base = self.evaluate(node.iter, inputs)
        body_names = set(base) - bound_names(
            node.target, include_params=False)
        if isinstance(node, ast.For):
            target_name = _lv53_string_iteration_target(
                node.target, node.iter, inputs,
                lambda value: _lv53_input_call_at(
                    value, _EMPTY_SHADOW, self.input_builtin,
                    self.input_binding_position))
            if target_name:
                body_names.add(target_name)
        body_start = frozenset(body_names)
        body = self.statements(node.body, body_start)
        if statically_empty_iterable(node.iter):
            self._mark_unevaluated(node.body)
            return self.statements(node.orelse, base)
        merged = base & body
        return self.statements(node.orelse, merged)
    def _while(self, node: ast.While,
               inputs: frozenset[str]) -> frozenset[str]:
        test = self._evaluate(node.test, inputs)
        body = self.statements(node.body, test.on_true)
        literal_truth = _lv53_condition_literal_truth(node.test)
        if literal_truth is False:
            self._mark_unevaluated(node.body)
            return self.statements(node.orelse, test.on_false)
        if literal_truth is True:
            self._mark_unevaluated(node.orelse)
            if _lv53_straight_line_final_break(node.body):
                return body
            exited = self._evaluate(
                node.test, test.state & body, record=False)
            return exited.on_false
        exited = self._evaluate(
            node.test, test.state & body, record=False)
        return self.statements(node.orelse, exited.on_false)
    def _with(self, node: ast.With | ast.AsyncWith,
              inputs: frozenset[str]) -> frozenset[str]:
        current = inputs
        for item in node.items:
            current = self.evaluate(item.context_expr, current)
            if item.optional_vars is not None:
                current = frozenset(set(current) - bound_names(
                    item.optional_vars, include_params=False))
        return self.statements(node.body, current)
    def _try(self, node: ast.Try | ast.TryStar,
             inputs: frozenset[str]) -> frozenset[str]:
        body = self.statements(node.body, inputs)
        normal = self.statements(node.orelse, body)
        handler_start = inputs & body
        outcomes = [normal]
        for handler in node.handlers:
            start = frozenset(set(handler_start) - ({handler.name}
                                                    if handler.name else set()))
            outcomes.append(self.statements(handler.body, start))
        merged = frozenset(set.intersection(*(set(item)
                                              for item in outcomes)))
        return self.statements(node.finalbody, merged)
    def _match(self, node: ast.Match,
               inputs: frozenset[str]) -> frozenset[str]:
        base = self.evaluate(node.subject, inputs)
        outcomes = [base]
        for case in node.cases:
            start = frozenset(set(base) - bound_names(
                case.pattern, include_params=False))
            if case.guard is not None:
                start = self._evaluate(case.guard, start).on_true
            outcomes.append(self.statements(case.body, start))
        return frozenset(set.intersection(*(set(item) for item in outcomes)))
    def statement(self, node: ast.AST,
                  inputs: frozenset[str]) -> frozenset[str]:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            return self._definition(node, inputs)
        if isinstance(node, ast.If):
            return self._if(node, inputs)
        if isinstance(node, (ast.For, ast.AsyncFor)):
            return self._for(node, inputs)
        if isinstance(node, ast.While):
            return self._while(node, inputs)
        if isinstance(node, (ast.With, ast.AsyncWith)):
            return self._with(node, inputs)
        if isinstance(node, (ast.Try, ast.TryStar)):
            return self._try(node, inputs)
        if isinstance(node, ast.Match):
            return self._match(node, inputs)
        return self._simple(node, inputs)
    def statements(self, nodes: list[ast.stmt],
                   inputs: frozenset[str]) -> frozenset[str]:
        current = inputs
        for index, node in enumerate(nodes):
            current = self.statement(node, current)
            if not _lv53_statements_may_fallthrough([node]):
                for remaining in nodes[index + 1:]:
                    self._mark_unevaluated(remaining)
                break
        return current
def _lv53_module_defers_annotations(scope: ast.AST) -> bool:
    return (isinstance(scope, ast.Module) and any(
        isinstance(stmt, ast.ImportFrom) and stmt.module == '__future__'
        and any(alias.name == 'annotations' for alias in stmt.names)
        for stmt in scope.body))
def _lv53_collect_facts(scope: ast.AST,
                        inherited: frozenset,
                        input_builtin: bool,
                        parent_scope: ast.AST | None = None,
                        annotations_deferred: bool = False,
                        input_binding_position: tuple[int, int] | None = None,
                        ) -> _LV53ScopeFacts:
    own_bindings = frozenset(scope_local_bindings(scope))
    class_global_fallback = (
        isinstance(scope, ast.ClassDef)
        and not isinstance(parent_scope, (ast.FunctionDef,
                                         ast.AsyncFunctionDef, ast.Lambda)))
    visible = (inherited if class_global_fallback
               else inherited.difference(own_bindings))
    flow = _LV53Flow(
        input_builtin,
        annotations_deferred=annotations_deferred,
        evaluate_variable_annotations=isinstance(
            scope, (ast.Module, ast.ClassDef)),
        input_binding_position=input_binding_position,
        class_bindings=(own_bindings if isinstance(scope, ast.ClassDef)
                        else _EMPTY_SHADOW),
    )
    final_input = flow.statements(scope_body_stmts(scope), visible)
    return _LV53ScopeFacts(
        flow.input_at, visible, final_input, input_builtin,
        frozenset(flow.unevaluated_ids), input_binding_position)
def _lv53_binding_is_input(name: str, facts: _LV53ScopeFacts,
                           shadow: frozenset, node: ast.AST) -> bool:
    recorded = facts.input_at.get(id(node))
    if recorded is not None:
        return name in recorded
    return name not in shadow and name in facts.inherited
def _lv53_name_binding_hit(node: ast.AST, other: ast.AST,
                           facts: _LV53ScopeFacts,
                           shadow: frozenset) -> str:
    if (isinstance(node, ast.Name)
            and _lv53_binding_is_input(node.id, facts, shadow, node)
            and _lv53_is_numeric_lit(other)):
        return node.id
    return ''
def _lv53_direct_call_hit(node: ast.AST, other: ast.AST,
                          facts: _LV53ScopeFacts,
                          shadow: frozenset) -> str:
    if (_lv53_input_call_at(
            node, shadow, facts.input_builtin, facts.input_binding_position)
            and _lv53_is_numeric_lit(other)):
        return 'input()'
    return ''
def _lv53_walrus_hit(node: ast.AST, other: ast.AST,
                     facts: _LV53ScopeFacts, shadow: frozenset) -> str:
    if (isinstance(node, ast.NamedExpr)
            and node.target.id in _lv53_input_binding_names(
                node,
                lambda value: _lv53_input_call_at(
                    value, shadow, facts.input_builtin,
                    facts.input_binding_position))
            and _lv53_is_numeric_lit(other)):
        return f'({node.target.id} := input())'
    return ''
def _lv53_string_expression_hit(
        node: ast.AST, other: ast.AST,
        facts: _LV53ScopeFacts, shadow: frozenset,
) -> str:
    if not _lv53_is_numeric_lit(other):
        return ''
    expression = node.value if isinstance(node, ast.NamedExpr) else node
    if not isinstance(expression, (ast.BinOp, ast.JoinedStr)):
        return ''
    known_input = facts.input_at.get(id(node), facts.inherited)
    is_string, from_input = _lv53_string_expression_facts(
        expression, known_input,
        lambda value: _lv53_input_call_at(
            value, shadow, facts.input_builtin,
            facts.input_binding_position))
    return ast.unparse(node) if is_string and from_input else ''
def _lv53_compare_hit(
        left: ast.AST, right: ast.AST,
        facts: _LV53ScopeFacts,
        shadow: frozenset) -> tuple[str, bool, str]:
    for swapped, (a, b) in enumerate(((left, right), (right, left))):
        hit = (_lv53_name_binding_hit(a, b, facts, shadow)
               or _lv53_direct_call_hit(a, b, facts, shadow)
               or _lv53_walrus_hit(a, b, facts, shadow)
               or _lv53_string_expression_hit(a, b, facts, shadow))
        if hit:
            return hit, not swapped, _lv53_literal_type_name(b)
    return '', True, ''
class _LV53Verdict(NamedTuple):
    severity: str
    verdict: str
    detail: str
    title: str
def _lv53_verdict(op: ast.cmpop, name_hit: str, literal_right: bool,
                  literal_type: str) -> _LV53Verdict | None:
    if isinstance(op, _LV53_ORDERED_OPS):
        quoted_types = (f"'str' and '{literal_type}'" if literal_right
                        else f"'{literal_type}' and 'str'")
        return _LV53Verdict(
            'P1', '必抛 TypeError',
            (
                f'``{name_hit}`` 承载的是 ``input()`` 产出——类型恒 '
                'str，与数字字面量做有序比较必抛 ``TypeError: '
                f"{_LV53_OP_SYMBOLS[type(op)]!r} not supported "
                f'between instances of {quoted_types}``，交互'
                '读数后判定分支一执行即崩。'
            ),
            f'{name_hit} 与数字字面量有序比较：str/{literal_type} TypeError',
        )
    if isinstance(op, ast.Eq):
        return _LV53Verdict(
            'P2', '恒假',
            (
                f'``{name_hit}`` 承载的是 ``input()`` 产出——类型恒 '
                f'str，与数字字面量做 ``==`` 比较恒为 False（str 与'
                f' {literal_type} 永不相等），守卫分支永不进入且无异常信号。'
            ),
            f'{name_hit} 与数字字面量 == 比较恒假：str 永不相等 {literal_type}',
        )
    if isinstance(op, ast.NotEq):
        return _LV53Verdict(
            'P2', '恒真',
            (
                f'``{name_hit}`` 承载的是 ``input()`` 产出——类型恒 '
                f'str，与数字字面量做 ``!=`` 比较恒为 True（str 与'
                f' {literal_type} 永不相等），守卫恒放行且无异常信号。'
            ),
            f'{name_hit} 与数字字面量 != 比较恒真：str 永不相等 {literal_type}',
        )
    return None
def _lv53_compare_issue(node: ast.Compare, facts: _LV53ScopeFacts,
                        shadow: frozenset, filepath: Any,
                        src_lines: list[str]) -> dict[str, Any] | None:
    for left, op, right in _iter_compare_pairs(node):
        name_hit, literal_right, literal_type = _lv53_compare_hit(
            left, right, facts, shadow)
        if not name_hit:
            continue
        verdict = _lv53_verdict(op, name_hit, literal_right, literal_type)
        if verdict is None:
            continue
        return _lv53_make_issue(filepath, src_lines, node, name_hit, verdict)
    return None
def _lv53_scan_scope(scope: ast.AST,
                     src_lines: list[str],
                     filepath: Any,
                     inherited: frozenset = _EMPTY_SHADOW,
                     input_shadowed: bool = False,
                     definition_facts: _LV53ScopeFacts | None = None,
                     parent_scope: ast.AST | None = None,
                     annotations_deferred: bool = False,
                     ) -> list[dict[str, Any]]:
    outer_inherited = inherited
    annotations_deferred = (
        annotations_deferred or _lv53_module_defers_annotations(scope))
    own_bindings = scope_local_bindings(scope)
    function_scope = isinstance(
        scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
    input_binding_position = _ordered_binding_positions(scope).get('input')
    input_builtin = not (
        input_shadowed or (function_scope and 'input' in own_bindings))
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        inherited = inherited.difference(param_names(scope))
    scoped = scope_nodes_with_shadow(scope)
    facts = _lv53_collect_facts(
        scope, inherited, input_builtin, parent_scope, annotations_deferred,
        input_binding_position)
    outer_facts = definition_facts or _LV53ScopeFacts(
        {}, outer_inherited, outer_inherited, not input_shadowed, frozenset())
    outer_ids = definition_outer_node_ids(scope)
    issues: list[dict[str, Any]] = []
    for node, shadow in scoped:
        if not isinstance(node, ast.Compare):
            continue
        node_facts = outer_facts if id(node) in outer_ids else facts
        if id(node) in node_facts.unevaluated_ids:
            continue
        issue = _lv53_compare_issue(
            node, node_facts, shadow, filepath, src_lines)
        if issue is not None:
            issues.append(issue)
    if isinstance(scope, ast.ClassDef):
        child_shadowed = input_shadowed
    elif isinstance(scope, ast.Module):
        child_shadowed = input_shadowed or 'input' in own_bindings
    else:
        child_shadowed = not input_builtin
    for child in child_scopes(scope):
        child_inherited = _child_inheritance(facts, scope, child)
        issues.extend(_lv53_scan_scope(
            child, src_lines, filepath, child_inherited, child_shadowed,
            facts, parent_scope=scope,
            annotations_deferred=annotations_deferred))
    return issues
def _lv53_make_issue(filepath: Any, src_lines: list[str], node: ast.Compare,
                     name_hit: str, verdict: _LV53Verdict) -> dict[str, Any]:
    return make_issue(
        'LV-53', verdict.severity, 'logic_correctness', filepath,
        node.lineno, verdict.title,
        verdict.detail,
        snippet_of(src_lines, node.lineno),
        (
            f'根因：``input()`` 返回契约是 str（{verdict.verdict}），\n'
            '数值语义必须先显式转换。\n'
            f'修复策略：``{name_hit}`` 先 ``int(...)``/``float(...)``\n'
            '转换（配合 try 容错非法输入），再参与数值比较；\n'
            '若比较的是字符串则两侧都按 str 处理。\n'
            '参考标准：Python3 input() 返回 str 契约与跨类型\n'
            '有序比较 TypeError 语义（PEP 原生比较协议）'
        ),
        'input-result-numeric-compare',
    )
def check_LV53(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    return run_scope_scan(tree, source, filepath, _lv53_scan_scope)
_LV58_VIEW_METHODS = frozenset({'keys', 'values', 'items'})
_LV58_SEQUENCE_CTORS = frozenset({'list', 'tuple'})
def _lv58_is_sequence_literal(
        node: ast.AST, shadow: frozenset[str]) -> bool:
    if isinstance(node, (ast.List, ast.Tuple)):
        return True
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in _LV58_SEQUENCE_CTORS
            and node.func.id not in shadow
            and not node.args and not node.keywords)
def _lv58_is_dict_constructor(
        node: ast.AST, shadow: frozenset[str]) -> bool:
    if isinstance(node, ast.Dict):
        return True
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'dict' and 'dict' not in shadow)
def _lv58_name_is_dict(
        name: str, compare: ast.Compare, scope: ast.AST,
        parents: dict[int, ast.AST],
        shadows: dict[int, frozenset[str]],
) -> bool:
    compare_position = (compare.lineno, compare.col_offset)
    bindings = []
    for node, bound_name, value in iter_binding_entries(scope_body_stmts(scope)):
        if bound_name != name:
            continue
        if isinstance(node, ast.AnnAssign) and node.value is None:
            continue
        if binding_evaluation_position(node) > compare_position:
            continue
        bindings.append((binding_evaluation_position(node), node, value))
    if not bindings:
        return False
    _position, binding, value = max(
        bindings, key=lambda item: item[0])
    if parents.get(id(binding)) is not scope:
        return False
    if not isinstance(binding, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
        return False
    return (value is not None and _lv58_is_dict_constructor(
        value, shadows.get(id(binding), _EMPTY_SHADOW)))
def _lv58_is_view_call(
        node: ast.AST, compare: ast.Compare, scope: ast.AST,
        parents: dict[int, ast.AST],
        shadows: dict[int, frozenset[str]],
) -> bool:
    if not (isinstance(node, ast.Call) and not node.args
            and not node.keywords and isinstance(node.func, ast.Attribute)
            and node.func.attr in _LV58_VIEW_METHODS):
        return False
    receiver = node.func.value
    if isinstance(receiver, ast.Name):
        return _lv58_name_is_dict(
            receiver.id, compare, scope, parents, shadows)
    return _lv58_is_dict_constructor(
        receiver, shadows.get(id(receiver), _EMPTY_SHADOW))
def _lv58_view_lit_method(
        prev: ast.AST, comp: ast.AST, op: ast.cmpop,
        shadow: frozenset[str], compare: ast.Compare, scope: ast.AST,
        parents: dict[int, ast.AST],
        shadows: dict[int, frozenset[str]]) -> str:
    if not isinstance(op, (ast.Eq, ast.NotEq)):
        return ''
    if (_lv58_is_view_call(prev, compare, scope, parents, shadows)
            and _lv58_is_sequence_literal(comp, shadow)):
        return prev.func.attr
    if (_lv58_is_view_call(comp, compare, scope, parents, shadows)
            and _lv58_is_sequence_literal(prev, shadow)):
        return comp.func.attr
    return ''
def _lv58_first_hit(
        node: ast.Compare, shadow: frozenset[str],
        parents: dict[int, ast.AST],
        shadows: dict[int, frozenset[str]]) -> tuple[str, bool] | None:
    scope = nearest_scope(parents, node)
    if scope is None:
        return None
    for prev, op, comp in _iter_compare_pairs(node):
        method = _lv58_view_lit_method(
            prev, comp, op, shadow, node, scope, parents, shadows)
        if method:
            return method, isinstance(op, ast.Eq)
    return None
def _lv58_make_issue(filepath: Any, src_lines: list[str], lineno: int,
                     method: str, is_eq: bool) -> dict[str, Any]:
    if is_eq:
        title = f'dict.{method}() 视图与字面量序列 == 恒假：守卫失效'
        description = (
            f'``dict.{method}()`` 返回视图对象——没有与 '
            'list/tuple 逐元素比较的相等语义（keys/items 按'
            '集合语义、values 按 identity），与序列比较恒为 '
            'False（与字典内容无关），守卫分支永不进入且无'
            '异常信号。'
        )
        suggestion = (
            f'根因：视图对象≠序列（``{method}()`` 是动态视图，\n'
            '与 list/tuple 不逐元素比较）。\n'
            f'修复策略：序列断言用 ``list(d.{method}()) == '
            '[...]``（或 list(d) 比较键序）；集合语义\n'
            '仅 keys/items 可用 ``d.<view>() == {...}``。\n'
            '参考标准：CPython dict view objects 比较协议\n'
            '（keys/items 集合语义、values 按 identity）'
        )
    else:
        title = f'dict.{method}() 视图与字面量序列 != 恒真：守卫失效'
        description = (
            f'``dict.{method}()`` 返回视图对象——与 '
            'list/tuple 字面量比较恒为 True（任何内容都'
            '满足 !=），守卫恒放行且无异常信号。'
        )
        suggestion = (
            f'根因：视图对象≠序列（``{method}()`` 是动态视图，\n'
            '与 list/tuple 不逐元素比较）。\n'
            f'修复策略：按序列比较先 ``list(d.{method}())``；\n'
            '集合语义仅 keys/items 可用集合字面量 ``{...}``。\n'
            '参考标准：CPython dict view objects 比较协议'
        )
    return make_issue(
        'LV-58', 'P2', 'logic_correctness', filepath, lineno,
        title, description, snippet_of(src_lines, lineno), suggestion,
        'dict-view-seq-literal-compare',
    )
def check_LV58(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    ctx = scan_context(tree, source)
    if ctx is None:
        return []
    issues, src_lines = ctx
    shadows = _evaluation_shadow_map(tree)
    parents = parent_map_of(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Compare):
            continue
        hit = _lv58_first_hit(
            node, shadows.get(id(node), _EMPTY_SHADOW), parents, shadows)
        if hit:
            issues.append(_lv58_make_issue(
                filepath, src_lines, node.lineno, *hit))
    return issues

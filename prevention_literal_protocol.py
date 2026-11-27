from __future__ import annotations

import ast
import logging
import re
from typing import Any, NamedTuple

from jwsgj.prevention_scope_facts import (
    _EMPTY_SHADOW,
    _with_item_binding_position,
    aligned_unpack_pairs,
    binding_body_start,
    binding_evaluation_position,
    bound_names,
    bound_names_of,
    capture_binding_names,
    child_inherited_shadow,
    child_scopes,
    definition_outer_node_ids,
    import_bound_names,
    is_dataclass_decorator,
    is_none_constant,
    make_issue,
    node_end_position,
    parent_map_of,
    rebound_binding_names,
    run_scope_scan,
    scan_context,
    scope_body_stmts,
    scope_local_bindings,
    scope_nodes_with_shadow,
    shadowed_binding_at,
    signed_numeric_literal,
    snippet_of,
    source_lines,
    target_binding_names,
    target_store_names,
    walk_nodes,
)

__all__ = [
    'check_LV13',
    'check_LV24',
    'check_LV36',
    'check_LV37',
    'check_LV38',
    'check_LV44',
]
_log = logging.getLogger(__name__)
_log.info("prevention_literal_protocol 取值构造与协议契约域检测器已加载：%d 项导出", len(__all__))
_LV13_TRY_TYPES = (ast.Try,) + (
    (ast.TryStar,) if hasattr(ast, 'TryStar') else ())
def _lv13_guaranteed_class_names(stmts: list[ast.stmt]) -> set[str]:
    names: set[str] = set()
    for node in stmts:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            names.add(node.name)
        elif isinstance(node, (ast.Assign, ast.AnnAssign)):
            names.update(_lv13_assigned_targets(node))
        elif isinstance(node, ast.If):
            if isinstance(node.test, ast.Constant):
                branch = node.body if bool(node.test.value) else node.orelse
                names.update(_lv13_guaranteed_class_names(branch))
            else:
                # 动态条件只有所有出口都定义的名称才保证存在。
                names.update(
                    _lv13_guaranteed_class_names(node.body)
                    & _lv13_guaranteed_class_names(node.orelse))
        elif isinstance(node, _LV13_TRY_TYPES):
            # 成功创建类时 finally 必执行；try/handler 中的定义不作保证。
            names.update(_lv13_guaranteed_class_names(node.finalbody))
    return names
def _lv13_scan_class_body(cls: ast.ClassDef) -> tuple[list, set[str]]:
    eq_nodes: list[ast.AST] = []
    assigned: dict[str, ast.AST] = {}
    stack: list[ast.AST] = list(cls.body)
    while stack:
        n = stack.pop()
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if n.name == '__eq__':
                eq_nodes.append(n)
            continue
        if isinstance(n, ast.ClassDef):
            continue
        assigned.update(_lv13_assigned_targets(n))
        stack.extend(ast.iter_child_nodes(n))
    if '__eq__' in assigned:
        eq_nodes.append(assigned['__eq__'])
    return eq_nodes, _lv13_guaranteed_class_names(cls.body)
def _lv13_assigned_targets(n: ast.AST) -> dict[str, ast.AST]:
    targets: list[ast.AST] = []
    if isinstance(n, ast.Assign):
        targets.extend(n.targets)
    elif isinstance(n, ast.AnnAssign) and n.value is not None:
        targets.append(n.target)
    return {name: n for target in targets
            for name, _lineno in target_store_names(target, 0)}
def _lv13_issue_texts(cls: ast.ClassDef) -> tuple[str, str, str]:
    return (
        f"类 {cls.name} 定义 __eq__ 但未定义 __hash__：实例不可哈希",
        (
            f'Python 语义联动：类定义 ``__eq__`` 且自身未定义 '
            f'``__hash__`` 时，``__hash__`` 被隐式置为 None——'
            f'{cls.name} 实例放入 set / dict 键 / lru_cache 时 '
            f'TypeError: unhashable type，报错点远离类定义，'
            f'排查成本高。'
        ),
        (
            '根因：值语义对象通常同时需要相等性与哈希一致性'
            '（equal 对象须有相同哈希），只写 __eq__ 会让类'
            '静默失去可哈希性。\n'
            '修复策略：按值字段实现 ``__hash__``（如 '
            '``def __hash__(self): return hash((self.x, self.y))``）；'
            '或确认业务确实不需要哈希时显式写 '
            '``__hash__ = None`` 声明意图（本检测放行该形态）。\n'
            '参考标准：协议联动缺失缺陷模式'
            '（Python 语言参考 __hash__ 隐式置 None 语义）'
        ),
    )
def _lv13_dataclass_manages_hash(dec: ast.AST) -> bool:
    if not is_dataclass_decorator(dec):
        return False
    if not isinstance(dec, ast.Call):
        return False
    eq = True
    frozen = False
    for kw in dec.keywords:
        if kw.arg is None:
            return True
        if kw.arg == 'unsafe_hash':
            if (not isinstance(kw.value, ast.Constant)
                    or bool(kw.value.value)):
                return True
        elif kw.arg in ('eq', 'frozen'):
            if not isinstance(kw.value, ast.Constant):
                return True
            if kw.arg == 'eq':
                eq = bool(kw.value.value)
            else:
                frozen = bool(kw.value.value)
    return frozen and eq
def _lv13_eq_without_hash(cls: ast.AST) -> ast.AST | None:
    if not isinstance(cls, ast.ClassDef):
        return None
    if any(_lv13_dataclass_manages_hash(d) for d in cls.decorator_list):
        return None
    eq_nodes, guaranteed_names = _lv13_scan_class_body(cls)
    if not eq_nodes or '__hash__' in guaranteed_names:
        return None
    return min(eq_nodes, key=lambda x: (x.lineno, x.col_offset))
def check_LV13(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    ctx = scan_context(tree, source)
    if ctx is None:
        return []
    issues, src_lines = ctx
    for cls in walk_nodes(tree):
        eq_node = _lv13_eq_without_hash(cls)
        if eq_node is None:
            continue
        title, desc, fix = _lv13_issue_texts(cls)
        issues.append(make_issue(
            'LV-13', 'P2', 'logic_correctness', filepath, eq_node.lineno,
            title, desc, snippet_of(src_lines, eq_node.lineno),
            fix, 'eq-without-hash',
        ))
    return issues
_LV24_LOG_NAMES = frozenset({
    'print', 'info', 'warning', 'warn', 'error', 'debug', 'exception',
    'critical', 'log', 'fatal', 'notice',
})
_LV24_LAZY_LOG_NAMES = _LV24_LOG_NAMES - {'print'}
_LV24_DOCSTRING_OWNERS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
def _lv24_docstring_node(owner: ast.AST) -> ast.Constant | None:
    body = scope_body_stmts(owner)
    if not body:
        return None
    first = body[0]
    if (isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant)
            and isinstance(first.value.value, str)):
        return first.value
    return None
def _lv24_docstring_ids(tree: ast.AST) -> set[int]:
    owners = [tree]
    owners.extend(node for node in walk_nodes(tree)
                  if isinstance(node, _LV24_DOCSTRING_OWNERS))
    return {id(doc) for doc in map(_lv24_docstring_node, owners)
            if doc is not None}
def _lv24_is_format_template(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in ('format', 'format_map')
            and isinstance(node.func.value, ast.Constant))
def _lv24_excluded_constant_ids(tree: ast.AST) -> set[int]:
    ids: set[int] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.JoinedStr):
            ids.update(id(part) for part in node.values
                       if isinstance(part, ast.Constant))
        elif _lv24_is_format_template(node):
            ids.add(id(node.func.value))
    return ids
def _lv24_lazy_kwargs_by_constant(
        tree: ast.AST) -> dict[int, frozenset[str]]:
    mapping: dict[int, frozenset[str]] = {}
    for node in walk_nodes(tree):
        if (not isinstance(node, ast.Call)
                or _lv24_log_call_name(node) not in _LV24_LAZY_LOG_NAMES):
            continue
        kw_names = frozenset(kw.arg for kw in node.keywords if kw.arg)
        if not kw_names:
            continue
        args: list[ast.AST] = list(node.args)
        args.extend(kw.value for kw in node.keywords)
        constant_ids: set[int] = set()
        _lv24_add_str_constants(constant_ids, args)
        for constant_id in constant_ids:
            mapping[constant_id] = mapping.get(
                constant_id, _EMPTY_SHADOW) | kw_names
    return mapping
def _lv24_log_call_name(node: ast.AST) -> str:
    if not isinstance(node, ast.Call):
        return ''
    func = node.func
    if isinstance(func, ast.Name):
        return func.id
    return func.attr if isinstance(func, ast.Attribute) else ''
def _lv24_is_log_call(node: ast.AST) -> bool:
    return _lv24_log_call_name(node) in _LV24_LOG_NAMES
def _lv24_add_str_constants(target: set[int], args: Any) -> None:
    for arg in args:
        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
            target.add(id(arg))
        elif isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Add):
            _lv24_add_str_constants(target, [arg.left, arg.right])
def _lv24_output_context_ids(tree: ast.AST) -> set[int]:
    ids: set[int] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Return):
            _lv24_add_str_constants(ids, [node.value])
            continue
        if isinstance(node, ast.Raise) and isinstance(node.exc, ast.Call):
            _lv24_add_str_constants(ids, node.exc.args)
            continue
        if _lv24_is_log_call(node):
            _lv24_add_str_constants(ids, node.args)
            if _lv24_log_call_name(node) != 'print':
                _lv24_add_str_constants(
                    ids, [kw.value for kw in node.keywords
                          if kw.arg == 'msg'])
    return ids
class _LV24Context(NamedTuple):
    bound: set[str]
    lazy_kwargs: dict[int, frozenset[str]]
    excluded: set[int]
    output_ctx: set[int]
def _lv24_context(tree: ast.AST) -> _LV24Context:
    return _LV24Context(
        bound=bound_names(tree),
        lazy_kwargs=_lv24_lazy_kwargs_by_constant(tree),
        excluded=(_lv24_excluded_constant_ids(tree)
                  | _lv24_docstring_ids(tree)),
        output_ctx=_lv24_output_context_ids(tree),
    )
def _lv24_is_candidate(node: ast.AST, ctx: _LV24Context) -> bool:
    if not (isinstance(node, ast.Constant) and isinstance(node.value, str)):
        return False
    return id(node) not in ctx.excluded and id(node) in ctx.output_ctx
_LV24_PLACEHOLDER_BASE = re.compile(r'(?:[^\W\d]|_)\w*')
def _lv24_placeholder_names(text: str) -> list[str]:
    names: list[str] = []
    i = 0
    end = len(text)
    while i < end:
        if text[i] == '{':
            if text.startswith('{{', i):
                i += 2
                continue
            close = text.find('}', i + 1)
            if close < 0:
                break
            body = re.split(r'[!:]', text[i + 1:close], maxsplit=1)[0]
            match = _LV24_PLACEHOLDER_BASE.match(body.strip())
            if match and match.group().isidentifier():
                names.append(match.group())
            i = close + 1
            continue
        i += 2 if text.startswith('}}', i) else 1
    return names
def _lv24_hit_names(
        text: str, ctx: _LV24Context, node: ast.AST,
        parents: dict[int, ast.AST], cache: dict[tuple, set[str]]) -> list[str]:
    lazy = ctx.lazy_kwargs.get(id(node), _EMPTY_SHADOW)
    return list(dict.fromkeys(
        name for name in _lv24_placeholder_names(text)
        if name in ctx.bound and name not in lazy
        and shadowed_binding_at(node, name, parents, cache)))
def _lv24_placeholder_hit(
        node: ast.AST, ctx: _LV24Context, parents: dict[int, ast.AST],
        cache: dict[tuple, set[str]]) -> str | None:
    if not _lv24_is_candidate(node, ctx):
        return None
    hits = _lv24_hit_names(node.value, ctx, node, parents, cache)
    return ' / '.join(hits) if hits else None
def _lv24_issue(filepath: Any, src_lines: list[str], node: ast.Constant,
                uniq: str) -> dict[str, Any]:
    return make_issue(
        'LV-24', 'P1', 'logic_correctness', filepath, node.lineno,
        f'str 字面量含 {{标识符}} 占位但无 f 前缀：{uniq} 插值静默失活',
        (
            f'字面量 ``"...{{...}}..."`` 无 f 前缀，花括号占位'
            f'（{uniq}）按字面文本原样输出——文案/日志/异常消息中'
            f'的变量值永远不出现，静态渲染错误且无任何异常信号。'
            f'f-string 内部段、``.format`` 模板与惰性格式化 keyword'
            f'三类合法语境已排除，命中即为忘 f 前缀。'
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：插值字符串书写时遗漏 f 前缀，``{x}`` 从插值'
            '表达式退化为普通文本。\n'
            '修复策略：字面量前加 f（``f"...{x}..."``）；模板场景'
            '保持 ``str.format`` / keyword 惰性格式化并确保占位名'
            '与实参一致。\n'
            '参考标准：Python f-string 与 str.format 插值语义（PEP 498 / PEP 3101）'
        ),
        'missing-f-prefix-placeholder',
    )
def check_LV24(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    ctx = scan_context(tree, source)
    if ctx is None:
        return []
    issues, src_lines = ctx
    lit_ctx = _lv24_context(tree)
    if not lit_ctx.bound or not lit_ctx.output_ctx:
        return issues
    parents = parent_map_of(tree)
    shadow_cache: dict[tuple, set[str]] = {}
    for node in walk_nodes(tree):
        uniq = _lv24_placeholder_hit(node, lit_ctx, parents, shadow_cache)
        if uniq is None:
            continue
        issues.append(
            _lv24_issue(filepath, src_lines, node, uniq))
    return issues
_LV36_UNBOUND_OWNERS = frozenset({'str', 'bytes', 'bytearray'})
_LV36_BYTES_OWNERS = frozenset({'bytes', 'bytearray'})
_LV36_EMPTY_LITERALS = {'str': '""', 'bytes': 'b""'}
_LV36_KIND_UNKNOWN = 'unknown'
_LV36_BUILTIN_KINDS = frozenset(
    f'builtin_{name}' for name in _LV36_UNBOUND_OWNERS)
def _lv36_is_compile_ref(
        node: ast.AST, module_names: frozenset[str],
        factory_names: frozenset[str]) -> bool:
    if isinstance(node, ast.Name):
        return node.id in factory_names
    return (isinstance(node, ast.Attribute)
            and node.attr == 'compile'
            and isinstance(node.value, ast.Name)
            and node.value.id in module_names)
def _lv36_is_compile_call(
        node: ast.AST | None, module_names: frozenset[str],
        factory_names: frozenset[str]) -> bool:
    node = _lv36_unwrap_receiver(node) if node is not None else None
    return (isinstance(node, ast.Call)
            and _lv36_is_compile_ref(
                node.func, module_names, factory_names))
def _lv36_compile_import_names(node: ast.AST) -> set[str]:
    if not isinstance(node, ast.ImportFrom) or node.module != 're':
        return set()
    return {alias.asname or alias.name for alias in node.names
            if alias.name == 'compile'}
def _lv36_unwrap_receiver(node: ast.AST) -> ast.AST:
    while isinstance(node, (ast.NamedExpr, ast.Await)):
        node = node.value
    return node
def _lv36_alias_target_kinds(
        value: ast.AST, target: ast.AST,
        module_names: frozenset[str],
        factory_names: frozenset[str]) -> tuple[set[str], set[str]]:
    if isinstance(value, ast.Name) and value.id in module_names:
        return set(target_binding_names(target)), set()
    if _lv36_is_compile_ref(value, module_names, factory_names):
        return set(), set(target_binding_names(target))
    pairs = aligned_unpack_pairs(target, value)
    if pairs is None:
        return set(), set()
    modules: set[str] = set()
    factories: set[str] = set()
    for sub_target, sub_value in pairs:
        sub_modules, sub_factories = _lv36_alias_target_kinds(
            sub_value, sub_target, module_names, factory_names)
        modules |= sub_modules
        factories |= sub_factories
    return modules, factories
def _lv36_alias_bindings(
        node: ast.AST, module_names: frozenset[str],
        factory_names: frozenset[str]) -> tuple[set[str], set[str]]:
    if isinstance(node, ast.Assign):
        value, targets = node.value, node.targets
    elif (isinstance(node, (ast.AnnAssign, ast.NamedExpr))
          and node.value is not None):
        value, targets = node.value, [node.target]
    else:
        return set(), set()
    modules: set[str] = set()
    factories: set[str] = set()
    for target in targets:
        sub_modules, sub_factories = _lv36_alias_target_kinds(
            value, target, module_names, factory_names)
        modules |= sub_modules
        factories |= sub_factories
    return modules, factories
def _lv36_pattern_names(
        value: ast.AST, target: ast.AST,
        module_names: frozenset[str],
        factory_names: frozenset[str],
        known_patterns: frozenset[str] = _EMPTY_SHADOW) -> set[str]:
    if isinstance(value, ast.Name) and value.id in known_patterns:
        return set(target_binding_names(target))
    if _lv36_is_compile_call(value, module_names, factory_names):
        return set(target_binding_names(target))
    pairs = aligned_unpack_pairs(target, value)
    if pairs is None:
        return set()
    names: set[str] = set()
    for sub_target, sub_value in pairs:
        names |= _lv36_pattern_names(
            sub_value, sub_target, module_names, factory_names,
            known_patterns)
    return names
def _lv36_iter_pattern_names(
        node: ast.For | ast.AsyncFor,
        module_names: frozenset[str],
        factory_names: frozenset[str],
        known_patterns: frozenset[str] = _EMPTY_SHADOW) -> set[str]:
    iterable = node.iter
    if isinstance(iterable, (ast.Tuple, ast.List, ast.Set)):
        if not iterable.elts:
            return set()
        common: set[str] | None = None
        for elt in iterable.elts:
            names = _lv36_pattern_names(
                elt, node.target, module_names, factory_names,
                known_patterns)
            common = names if common is None else common & names
            if not common:
                return set()
        return common or set()
    if isinstance(iterable, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
        return _lv36_pattern_names(
            iterable.elt, node.target, module_names, factory_names,
            known_patterns)
    return set()
def _lv36_is_literal_value(node: ast.AST) -> bool:
    return (isinstance(node, ast.Constant)
            or type(node) in (ast.List, ast.Tuple, ast.Dict, ast.Set,
                              ast.JoinedStr))
def _lv36_pattern_bindings(
        node: ast.AST, module_names: frozenset[str],
        factory_names: frozenset[str],
        known_patterns: frozenset[str] = _EMPTY_SHADOW,
        ) -> list[tuple[tuple[int, int], str]]:
    if isinstance(node, ast.Assign):
        value, targets = node.value, node.targets
    elif isinstance(node, ast.AnnAssign) and node.value is None:
        if (isinstance(node.target, ast.Name)
                and _lv36_is_pattern_annotation(node.annotation)):
            return [(node_end_position(node.annotation), node.target.id)]
        return []
    elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
        value, targets = node.value, [node.target]
    elif isinstance(node, ast.withitem):
        if node.optional_vars is None:
            return []
        position = _with_item_binding_position(node)
        names = _lv36_pattern_names(
            node.context_expr, node.optional_vars,
            module_names, factory_names, known_patterns)
        return [(position, name) for name in sorted(names)]
    elif isinstance(node, (ast.For, ast.AsyncFor)):
        position = binding_body_start(node)
        return [(position, name) for name in sorted(
            _lv36_iter_pattern_names(
                node, module_names, factory_names, known_patterns))]
    else:
        return []
    position = node_end_position(value)
    names: set[str] = set()
    for target in targets:
        names |= _lv36_pattern_names(
            value, target, module_names, factory_names, known_patterns)
    if (isinstance(node, ast.AnnAssign)
            and isinstance(node.target, ast.Name)
            and _lv36_is_pattern_annotation(node.annotation)
            and not _lv36_is_literal_value(value)):
        names.add(node.target.id)
    return [(position, name) for name in sorted(names)]
def _lv36_bound_names(node: ast.AST) -> set[str]:
    if isinstance(node, ast.Assign):
        return {name for target in node.targets
                for name in bound_names(target, include_params=False)}
    if isinstance(node, ast.AnnAssign):
        return (bound_names(node.target, include_params=False)
                if node.value is not None else set())
    if isinstance(node, (ast.AugAssign, ast.NamedExpr)):
        return bound_names(node.target, include_params=False)
    if isinstance(node, ast.withitem):
        return (set(target_binding_names(node.optional_vars))
                if node.optional_vars is not None else set())
    return rebound_binding_names(node) | bound_names_of(
        node, include_params=False)
def _lv36_binding_events(
        scoped: list[tuple[ast.AST, frozenset]],
        ) -> list[tuple[tuple[int, int], ast.AST, frozenset[str]]]:
    events: list[tuple[tuple[int, int], ast.AST, frozenset[str]]] = []
    pattern_owners = (ast.Assign, ast.AnnAssign, ast.NamedExpr,
                      ast.withitem, ast.For, ast.AsyncFor)
    for node, shadow in scoped:
        if isinstance(node, (ast.Name, ast.alias, ast.With, ast.AsyncWith)):
            continue
        names = _lv36_bound_names(node)
        if not names and not isinstance(node, pattern_owners):
            continue
        position = (_with_item_binding_position(node)
                    if isinstance(node, ast.withitem)
                    else binding_evaluation_position(node))
        events.append((position, node, shadow))
    return sorted(events, key=lambda item: item[0])
def _ordered_local_binding_states(
        scope: ast.AST,
        scoped: list[tuple[ast.AST, frozenset[str]]],
        children: list[ast.AST],
        ) -> tuple[
            dict[int, frozenset[str]], dict[int, frozenset[str]]]:
    own = frozenset(scope_local_bindings(scope))
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return ({id(node): own for node, _shadow in scoped
                 if isinstance(node, ast.Call)},
                {id(child): own for child in children})
    events = _lv36_binding_events(scoped)
    events.extend(
        (binding_evaluation_position(child), child, _EMPTY_SHADOW)
        for child in children)
    events.sort(key=lambda item: item[0])
    milestones = [
        ((node.lineno, node.col_offset), node, False)
        for node, _shadow in scoped if isinstance(node, ast.Call)]
    milestones.extend(
        (binding_evaluation_position(child), child, True)
        for child in children)
    milestones.sort(key=lambda item: item[0])
    active: set[str] = set()
    call_states: dict[int, frozenset[str]] = {}
    definition_states: dict[int, frozenset[str]] = {}
    index = 0
    for position, node, is_definition in milestones:
        while index < len(events) and events[index][0] < position:
            _event_pos, event_node, event_shadow = events[index]
            active.update(_lv36_bound_names(event_node) - event_shadow)
            index += 1
        if is_definition:
            definition_states[id(node)] = frozenset(active)
        else:
            call_states[id(node)] = frozenset(active)
    return call_states, definition_states
def _lv36_replay(
        events: list[tuple[tuple[int, int], ast.AST, frozenset[str]]],
        index: int, cutoff: tuple[int, int] | None,
        active_modules: set[str], active_patterns: set[str],
        active_factories: set[str], seen_bindings: set[str]) -> int:
    while index < len(events) and (
            cutoff is None or events[index][0] < cutoff):
        _pos, node, event_shadow = events[index]
        pattern_names = {
            name for _pattern_pos, name in _lv36_pattern_bindings(
                node, frozenset(active_modules), frozenset(active_factories),
                frozenset(active_patterns))
            if name not in event_shadow
        }
        aliased_modules, aliased_factories = _lv36_alias_bindings(
            node, frozenset(active_modules), frozenset(active_factories))
        bound = _lv36_bound_names(node) - event_shadow
        if isinstance(node, ast.AnnAssign) and node.value is None:
            pattern_names -= seen_bindings
        imported = isinstance(node, (ast.Import, ast.ImportFrom))
        factory_imports = _lv36_compile_import_names(node)
        for name in bound:
            active_patterns.discard(name)
            if imported and name in factory_imports:
                active_modules.discard(name)
                active_factories.add(name)
            elif imported:
                active_modules.add(name)
                active_factories.discard(name)
            else:
                active_modules.discard(name)
                active_factories.discard(name)
        seen_bindings.update(bound)
        for name in aliased_modules - event_shadow:
            active_patterns.discard(name)
            active_factories.discard(name)
            active_modules.add(name)
        for name in aliased_factories - event_shadow:
            active_patterns.discard(name)
            active_modules.discard(name)
            active_factories.add(name)
        for name in pattern_names:
            active_patterns.add(name)
            active_modules.discard(name)
            active_factories.discard(name)
        index += 1
    return index
def _lv36_binding_states(
        scoped: list[tuple[ast.AST, frozenset]],
        inherited_modules: frozenset[str],
        inherited_patterns: frozenset[str],
        inherited_factories: frozenset[str],
        static_shadow: frozenset[str],
        declared_patterns: frozenset[str] = _EMPTY_SHADOW,
        initial_bindings: frozenset[str] = _EMPTY_SHADOW,
        ) -> tuple[
            dict[int, tuple[
                frozenset[str], frozenset[str], frozenset[str]]],
            frozenset[str], frozenset[str], frozenset[str]]:
    events = _lv36_binding_events(scoped)
    calls = sorted(
        (((node.lineno, node.col_offset), node, shadow)
         for node, shadow in scoped if isinstance(node, ast.Call)),
        key=lambda item: item[0])
    active_modules = set(inherited_modules - static_shadow)
    active_factories = set(inherited_factories - static_shadow)
    active_patterns = set(
        (inherited_patterns - static_shadow) | declared_patterns)
    states: dict[int, tuple[
        frozenset[str], frozenset[str], frozenset[str]]] = {}
    seen_bindings = set(initial_bindings)
    index = 0
    for position, node, shadow in calls:
        index = _lv36_replay(
            events, index, position, active_modules, active_patterns,
            active_factories, seen_bindings)
        states[id(node)] = (frozenset(active_modules - shadow),
                            frozenset(active_patterns - shadow),
                            frozenset(active_factories - shadow))
    _lv36_replay(events, index, None, active_modules, active_patterns,
                 active_factories, seen_bindings)
    return (states, frozenset(active_modules), frozenset(active_patterns),
            frozenset(active_factories))
def _lv36_sep_offset(func: ast.Attribute,
                     module_names: frozenset,
                     pattern_names: frozenset,
                     factory_names: frozenset,
                     shadow: frozenset,
                     receiver_kinds: dict[str, str]) -> int | None:
    value = _lv36_unwrap_receiver(func.value)
    if isinstance(value, ast.Name) and value.id in pattern_names:
        return None
    if _lv36_is_compile_call(value, module_names, factory_names):
        return None
    if isinstance(value, ast.Attribute):
        root = value
        while isinstance(root, ast.Attribute):
            root = root.value
        if isinstance(root, ast.Name) and root.id in module_names:
            return None
        return 0
    if isinstance(value, ast.Name):
        if receiver_kinds.get(value.id) in _LV36_BUILTIN_KINDS:
            return 1
        if value.id in module_names:
            return None
        if value.id in _LV36_UNBOUND_OWNERS and value.id not in shadow:
            return 1
    return 0
def _lv36_empty_literal_kind(node: ast.AST) -> str | None:
    if not isinstance(node, ast.Constant):
        return None
    value = node.value
    if isinstance(value, str) and not value:
        return 'str'
    if isinstance(value, (bytes, bytearray)) and len(value) == 0:
        return 'bytes'
    return None
def _lv36_separator_kind(
        func: ast.Attribute, shadow: frozenset[str],
        receiver_kinds: dict[str, str]) -> str:
    value = _lv36_unwrap_receiver(func.value)
    if isinstance(value, ast.JoinedStr):
        return 'str'
    if isinstance(value, ast.Constant):
        if isinstance(value.value, (bytes, bytearray)):
            return 'bytes'
        if isinstance(value.value, str):
            return 'str'
    if isinstance(value, ast.Name):
        known_kind = receiver_kinds.get(value.id)
        if known_kind in _LV36_BUILTIN_KINDS:
            known_kind = known_kind.removeprefix('builtin_')
        if known_kind in _LV36_UNBOUND_OWNERS:
            return 'bytes' if known_kind == 'bytearray' else known_kind
        if value.id in shadow:
            return _LV36_KIND_UNKNOWN
        if value.id in _LV36_BYTES_OWNERS:
            return 'bytes'
        if value.id == 'str':
            return 'str'
    if isinstance(value, ast.Call) and isinstance(value.func, ast.Name):
        if value.func.id in shadow:
            return _LV36_KIND_UNKNOWN
        if value.func.id in _LV36_BYTES_OWNERS:
            return 'bytes'
        if value.func.id == 'str':
            return 'str'
    return _LV36_KIND_UNKNOWN
def _lv36_empty_separator_arg(
        node: ast.Call, offset: int, kind: str) -> str | None:
    positional = node.args[offset] if len(node.args) > offset else None
    candidates = [positional] if positional is not None else []
    candidates.extend(kw.value for kw in node.keywords if kw.arg == 'sep')
    for candidate in candidates:
        literal_kind = _lv36_empty_literal_kind(candidate)
        if (literal_kind is not None
                and kind in (_LV36_KIND_UNKNOWN, literal_kind)):
            return literal_kind
    return None
def _lv36_empty_separator(
        node: ast.AST,
        module_names: frozenset,
        pattern_names: frozenset,
        factory_names: frozenset,
        shadow: frozenset,
        receiver_kinds: dict[str, str]) -> tuple[str, str, str] | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if not (isinstance(func, ast.Attribute)
            and func.attr in ('split', 'rsplit')):
        return None
    receiver_kind = _lv36_separator_kind(
        func, shadow, receiver_kinds)
    if receiver_kind == _LV36_KIND_UNKNOWN:
        return None
    offset = _lv36_sep_offset(
        func, module_names, pattern_names, factory_names, shadow,
        receiver_kinds)
    if offset is None or (offset == 1 and not node.args):
        return None
    empty_kind = _lv36_empty_separator_arg(node, offset, receiver_kind)
    if empty_kind is None:
        return None
    return func.attr, empty_kind, receiver_kind
def _lv36_issue(filepath: Any, src_lines: list[str], node: ast.Call,
                method: str, kind: str,
                receiver_kind: str) -> dict[str, Any]:
    empty = _LV36_EMPTY_LITERALS[kind]
    owner = 'bytes' if kind == 'bytes' else 'str'
    if receiver_kind == owner:
        title = (f'{owner}.{method}({empty}) 空分隔符：必抛 ValueError'
                 '（empty separator）')
        description = (
            f'``{owner}.{method}({empty})`` 形态——分隔符为空时 '
            f'{owner}.{method} 必抛 ValueError: empty separator；'
            '按字符/字节切分的正确写法是 ``list(s)``（或生成'
            '器 ``(c for c in s)``），空分隔符调用一执行即崩。'
        )
    elif kind == 'bytes':
        title = (f'{method}({empty}) 空分隔符：bytes 接收者抛 ValueError，'
                 'str 接收者抛 TypeError')
        description = (
            f'``.{method}({empty})`` 传入空 bytes 分隔符——两种接收者'
            '契约的结果不同：bytes 接收者抛 ``ValueError: empty '
            'separator``，str 接收者抛 ``TypeError: must be str or '
            'None, not bytes``；按字符/字节切分的正确写法是 '
            '``list(s)``，空分隔符调用一执行即崩。'
        )
    else:
        title = (f'{method}({empty}) 空分隔符：str 接收者抛 ValueError，'
                 'bytes 接收者抛 TypeError')
        description = (
            f'``.{method}({empty})`` 传入空分隔符——接收者类型未知，'
            '两种契约都拒绝空分隔符：str 抛 ``ValueError: empty '
            'separator``，bytes 抛 ``TypeError: a bytes-like object '
            'is required``；按字符/字节切分的正确写法是 ``list(s)``，'
            '空分隔符调用一执行即崩。'
        )
    return make_issue(
        'LV-36', 'P1', 'logic_correctness', filepath, node.lineno,
        title, description, snippet_of(src_lines, node.lineno),
        (
            '根因：把 str.split 当字符级分割接口（空分隔符在\n'
            'shell/awk 里是合法语义，Python 契约相反）。\n'
            '修复策略：按字符分割用 ``list(s)``；按固定分隔符\n'
            '用真实分隔符 ``s.split(",")``；按正则用 ``re.split``。\n'
            '参考标准：CPython str/bytes.split 契约（sep 非空才允许，\n'
            'None 表示按空白切分）'
        ),
        'str-split-empty-separator',
    )
def _lv36_is_pattern_annotation(node: ast.AST | None) -> bool:
    if node is None:
        return False
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        text = node.value.strip().rsplit('.', 1)[-1]
        return text.split('[', 1)[0].strip('\'"') == 'Pattern'
    if isinstance(node, ast.Subscript):
        node = node.value
    if isinstance(node, ast.Attribute):
        return node.attr == 'Pattern'
    return isinstance(node, ast.Name) and node.id == 'Pattern'
def _lv36_parameter_facts(
        scope: ast.AST) -> tuple[frozenset[str], frozenset[str]]:
    args = getattr(scope, 'args', None)
    if not isinstance(args, ast.arguments):
        return _EMPTY_SHADOW, _EMPTY_SHADOW
    params = [*args.posonlyargs, *args.args, *args.kwonlyargs]
    params.extend(arg for arg in (args.vararg, args.kwarg)
                  if arg is not None)
    names = frozenset(arg.arg for arg in params)
    patterns = frozenset(
        arg.arg for arg in params
        if _lv36_is_pattern_annotation(arg.annotation))
    return patterns, names
def _lv36_receiver_kind_map(kinds: dict[str, str]) -> dict[str, str]:
    return {name: kind for name, kind in kinds.items()
            if kind in _LV36_UNBOUND_OWNERS | _LV36_BUILTIN_KINDS}
def _lv36_promote_builtin_imports(evidence: Any, scoped: list) -> None:
    for node, _shadow in scoped:
        if not isinstance(node, ast.ImportFrom) or node.module != 'builtins':
            continue
        position = binding_evaluation_position(node)
        for alias in node.names:
            kind = f'builtin_{alias.name}'
            if kind in _LV36_BUILTIN_KINDS:
                evidence._append(
                    alias.asname or alias.name, position, kind)
def _lv36_scan_scope(
        scope: ast.AST, src_lines: list[str], filepath: Any,
        inherited_modules: frozenset[str] = _EMPTY_SHADOW,
        inherited_patterns: frozenset[str] = _EMPTY_SHADOW,
        inherited_factories: frozenset[str] = _EMPTY_SHADOW,
        inherited_shadow: frozenset[str] = _EMPTY_SHADOW,
        definition_state: tuple[
            frozenset[str], frozenset[str], frozenset[str],
            frozenset[str]] | None = None,
        inherited_kinds: dict[str, str] | None = None,
        definition_kinds: dict[str, str] | None = None,
        ) -> list[dict[str, Any]]:
    scoped = scope_nodes_with_shadow(scope)
    own_bindings = frozenset(scope_local_bindings(scope))
    visible = inherited_shadow | own_bindings
    static_shadow = (own_bindings
                     if isinstance(scope, (ast.FunctionDef,
                                           ast.AsyncFunctionDef))
                     else _EMPTY_SHADOW)
    declared_patterns, parameter_names = _lv36_parameter_facts(scope)
    states, child_modules, child_patterns, child_factories = (
        _lv36_binding_states(
            scoped, inherited_modules, inherited_patterns,
            inherited_factories, static_shadow, declared_patterns,
            parameter_names | inherited_shadow)
    )
    children = child_scopes(scope)
    call_bindings, definition_bindings = _ordered_local_binding_states(
        scope, scoped, children)
    type_evidence = _LV44ScopeScanner(src_lines, filepath).collect_scope(
        scope_body_stmts(scope), is_class=isinstance(scope, ast.ClassDef))[0]
    _lv36_promote_builtin_imports(type_evidence, scoped)
    base_kinds = dict(inherited_kinds or {})
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        base_kinds = {name: kind for name, kind in base_kinds.items()
                      if name not in own_bindings}
        base_kinds.update(_lv44_param_kinds(scope))
    base_kinds = _lv36_receiver_kind_map(base_kinds)
    kind_states = {
        id(node): _lv36_receiver_kind_map(type_evidence.resolve(
            base_kinds, (node.lineno, node.col_offset)))
        for node, _shadow in scoped if isinstance(node, ast.Call)
    }
    final_kinds = _lv36_receiver_kind_map(type_evidence.resolve(base_kinds))
    outer_kinds = definition_kinds if definition_kinds is not None else base_kinds
    issues: list[dict[str, Any]] = []
    empty_state = (_EMPTY_SHADOW, _EMPTY_SHADOW, _EMPTY_SHADOW)
    outer_modules, outer_patterns, outer_factories, outer_shadow = (
        definition_state
        or (inherited_modules, inherited_patterns, inherited_factories,
            inherited_shadow)
    )
    outer_ids = definition_outer_node_ids(scope)
    for node, shadow in scoped:
        is_outer = id(node) in outer_ids
        state = ((outer_modules, outer_patterns, outer_factories)
                 if is_outer else states.get(id(node), empty_state))
        if is_outer:
            base_shadow = outer_shadow
        elif isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            base_shadow = visible
        else:
            base_shadow = inherited_shadow | call_bindings.get(
                id(node), _EMPTY_SHADOW)
        node_kinds = outer_kinds if is_outer else kind_states.get(id(node), {})
        hit = _lv36_empty_separator(
            node, *state, shadow | base_shadow, node_kinds)
        if hit is None:
            continue
        issues.append(_lv36_issue(
            filepath, src_lines, node, *hit))
    child_inherited = child_inherited_shadow(
        scope, child_modules, inherited_modules)
    child_inherited_patterns = child_inherited_shadow(
        scope, child_patterns, inherited_patterns)
    child_inherited_factories = child_inherited_shadow(
        scope, child_factories, inherited_factories)
    child_visible = child_inherited_shadow(scope, visible, inherited_shadow)
    visible_kind_names = child_inherited_shadow(
        scope, frozenset(final_kinds), frozenset(base_kinds))
    child_kinds = {name: kind for name, kind in final_kinds.items()
                   if name in visible_kind_names}
    for child in children:
        definition_visible = (
            visible if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))
            else inherited_shadow | definition_bindings.get(
                id(child), _EMPTY_SHADOW))
        child_definition = (
            child_modules, child_patterns, child_factories,
            definition_visible)
        child_definition_kinds = _lv36_receiver_kind_map(
            type_evidence.resolve(
                base_kinds, (child.lineno, child.col_offset)))
        issues.extend(_lv36_scan_scope(
            child, src_lines, filepath,
            child_inherited, child_inherited_patterns,
            child_inherited_factories, child_visible, child_definition,
            child_kinds, child_definition_kinds))
    return issues
def check_LV36(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    return run_scope_scan(tree, source, filepath, _lv36_scan_scope)
_CONTAINER_LITERAL_NODES = (
    ast.List, ast.ListComp, ast.Dict, ast.DictComp, ast.Set, ast.SetComp)
_MUTABLE_CONTAINER_CTOR_NAMES = frozenset(
    {'list', 'dict', 'set', 'bytearray'})
_LV37_MUTABLE_LITERALS = _CONTAINER_LITERAL_NODES
def _lv37_fromkeys_call(
        node: ast.AST,
        shadow: set[str] | frozenset[str]) -> ast.Call | None:
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if not (isinstance(func, ast.Attribute) and func.attr == 'fromkeys'):
        return None
    owner = func.value
    if (isinstance(owner, ast.Name) and owner.id == 'dict'
            and owner.id not in shadow):
        return node
    if isinstance(owner, (ast.Dict, ast.DictComp)):
        return node
    return None
_LV37_DEFAULT_ARG_INDEX = 1
_LV37_MUTABLE_CTOR_NAMES = _MUTABLE_CONTAINER_CTOR_NAMES
def _lv37_mutable_ctor(node: ast.AST, shadow: set[str]) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in _LV37_MUTABLE_CTOR_NAMES
            and node.func.id not in shadow)
def _lv37_keyword_arg(call: ast.Call) -> bool:
    return any(keyword.arg is not None for keyword in call.keywords)
def _lv37_mutable_default(
        call: ast.Call,
        shadow: set[str] | frozenset[str]) -> bool:
    if len(call.args) <= _LV37_DEFAULT_ARG_INDEX:
        return False
    default_arg = call.args[_LV37_DEFAULT_ARG_INDEX]
    if isinstance(default_arg, ast.Starred):
        return False
    return (isinstance(default_arg, _LV37_MUTABLE_LITERALS)
            or _lv37_mutable_ctor(default_arg, shadow))
def _lv37_scan_scope(
        scope: ast.AST, src_lines: list[str], filepath: Any,
        inherited: frozenset[str] = _EMPTY_SHADOW,
        definition_inherited: frozenset[str] | None = None,
        ) -> list[dict[str, Any]]:
    own = frozenset(scope_local_bindings(scope))
    visible = inherited | own
    outer = inherited if definition_inherited is None else definition_inherited
    outer_ids = definition_outer_node_ids(scope)
    scoped = scope_nodes_with_shadow(scope)
    children = child_scopes(scope)
    call_bindings, definition_bindings = (
        _ordered_local_binding_states(scope, scoped, children))
    issues: list[dict[str, Any]] = []
    for node, local_shadow in scoped:
        if id(node) in outer_ids:
            base = outer
        elif isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            base = visible
        else:
            base = inherited | call_bindings.get(id(node), _EMPTY_SHADOW)
        shadow = base | local_shadow
        call = _lv37_fromkeys_call(node, shadow)
        if call is None:
            continue
        if _lv37_keyword_arg(call):
            issues.append(make_issue(
                'LV-37', 'P1', 'logic_correctness', filepath, call.lineno,
                'dict.fromkeys 传入关键字实参：必抛 TypeError',
                (
                    '``dict.fromkeys(keys, value=[])`` 形态——fromkeys '
                    '是位置专用签名（``dict.fromkeys() takes no keyword '
                    'arguments``），关键字形态一执行即 TypeError；'
                    '按「共享可变默认值」理解会掩盖真实报错点。'
                ),
                snippet_of(src_lines, call.lineno),
                (
                    '根因：把位置专用内建方法当普通 Python 函数传关键字。\n'
                    '修复策略：默认值改用位置实参 ``dict.fromkeys(keys, [])\n'
                    '（并注意 LV-37 的跨键共享语义）或直接用推导式\n'
                    '``{k: [] for k in keys}``。\n'
                    '参考标准：CPython dict.fromkeys 位置专用签名'
                ),
                'dict-fromkeys-keyword-argument',
            ))
            continue
        if not _lv37_mutable_default(call, shadow):
            continue
        issues.append(make_issue(
            'LV-37', 'P2', 'logic_correctness', filepath, call.lineno,
            'dict.fromkeys 可变默认值：全部键共享同一可变对象',
            (
                '``dict.fromkeys(keys, [])`` 形态——fromkeys 把默认值'
                '对象本身挂到**每个**键上（引用共享，非复制），任一'
                '键下 append/update 会被所有键同时读到，跨键数据串'
                '扰且无报错信号，静默污染下游消费逻辑。'
            ),
            snippet_of(src_lines, call.lineno),
            (
                '根因：fromkeys 的默认值按引用共享（与 ``[[]] * n``\n'
                '乘法复制同根因家族），意图「每键独立容器」与实际\n'
                '「全键单容器」错位。\n'
                '修复策略：每键独立容器用推导式\n'
                '``{k: [] for k in keys}``；确需共享默认值时在文档\n'
                '注明引用共享语义。\n'
                '参考标准：CPython dict.fromkeys 契约（value 按引用\n'
                '共享，不复制）'
            ),
            'dict-fromkeys-mutable-default',
        ))
    child_inherited = child_inherited_shadow(scope, visible, inherited)
    for child in children:
        definition_visible = (
            visible if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))
            else inherited | definition_bindings.get(id(child), _EMPTY_SHADOW))
        issues.extend(_lv37_scan_scope(
            child, src_lines, filepath, child_inherited, definition_visible))
    return issues
def check_LV37(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    return run_scope_scan(tree, source, filepath, _lv37_scan_scope)
_LV38_NONCALLABLE_LITERALS = (
    *_CONTAINER_LITERAL_NODES, ast.Tuple, ast.GeneratorExp, ast.JoinedStr)
_LV38_NONCALLABLE_CTORS = _MUTABLE_CONTAINER_CTOR_NAMES | frozenset({
    'frozenset', 'tuple', 'bytes', 'str', 'int', 'float', 'complex',
    'bool', 'object', 'range',
})
def _lv38_noncallable_literal(
        node: ast.AST, shadow: frozenset[str]) -> bool:
    if isinstance(node, _LV38_NONCALLABLE_LITERALS):
        return True
    if isinstance(node, ast.Constant):
        return node.value is not None
    if signed_numeric_literal(node) is not None:
        return True
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id in _LV38_NONCALLABLE_CTORS
            and node.func.id not in shadow)
def _lv38_defaultdict_ref(
        func: ast.AST, factory_names: frozenset[str],
        module_names: frozenset[str]) -> bool:
    if isinstance(func, ast.Name):
        return func.id in factory_names
    return (isinstance(func, ast.Attribute) and func.attr == 'defaultdict'
            and isinstance(func.value, ast.Name)
            and func.value.id in module_names)
def _lv38_bad_factory_call(
        node: ast.AST, factory_names: frozenset[str],
        module_names: frozenset[str], shadow: frozenset[str]) -> str:
    if not isinstance(node, ast.Call):
        return ''
    if not _lv38_defaultdict_ref(node.func, factory_names, module_names):
        return ''
    if (node.args and not isinstance(node.args[0], ast.Starred)
            and _lv38_noncallable_literal(node.args[0], shadow)):
        return 'noncallable'
    if (any(kw.arg == 'default_factory' for kw in node.keywords)
            and (not node.args
                 or (not isinstance(node.args[0], ast.Starred)
                     and is_none_constant(node.args[0])))):
        return 'keyword'
    return ''
def _lv38_collections_aliases(
        node: ast.AST, factories: set[str], modules: set[str]) -> None:
    if isinstance(node, ast.Import):
        for alias in node.names:
            if alias.name == 'collections':
                modules.add(alias.asname or 'collections')
            elif (alias.name.startswith('collections.')
                  and alias.asname is None):
                modules.add('collections')
        return
    if isinstance(node, ast.ImportFrom) and node.module == 'collections':
        factories.update(alias.asname or alias.name
                         for alias in node.names
                         if alias.name == 'defaultdict')
def _lv38_alias_target_kinds(
        value: ast.AST, target: ast.AST,
        factory_names: frozenset[str],
        module_names: frozenset[str]) -> tuple[set[str], set[str]]:
    if _lv38_defaultdict_ref(value, factory_names, module_names):
        return set(target_binding_names(target)), set()
    if isinstance(value, ast.Name) and value.id in module_names:
        return set(), set(target_binding_names(target))
    pairs = aligned_unpack_pairs(target, value)
    if pairs is None:
        return set(), set()
    factories: set[str] = set()
    modules: set[str] = set()
    for sub_target, sub_value in pairs:
        sub_factories, sub_modules = _lv38_alias_target_kinds(
            sub_value, sub_target, factory_names, module_names)
        factories |= sub_factories
        modules |= sub_modules
    return factories, modules
def _lv38_alias_bindings(
        node: ast.AST, factory_names: frozenset[str],
        module_names: frozenset[str]) -> tuple[set[str], set[str]]:
    if isinstance(node, ast.Assign):
        value, targets = node.value, node.targets
    elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
        if node.value is None:
            return set(), set()
        value, targets = node.value, [node.target]
    else:
        return set(), set()
    factories: set[str] = set()
    modules: set[str] = set()
    for target in targets:
        sub_factories, sub_modules = _lv38_alias_target_kinds(
            value, target, factory_names, module_names)
        factories |= sub_factories
        modules |= sub_modules
    return factories, modules
def _lv38_alias_replay(
        events: list[tuple[tuple[int, int], ast.AST, frozenset[str]]],
        index: int, cutoff: tuple[int, int] | None,
        active_factories: set[str], active_modules: set[str]) -> int:
    while index < len(events) and (
            cutoff is None or events[index][0] < cutoff):
        _pos, node, event_shadow = events[index]
        imported_factories: set[str] = set()
        imported_modules: set[str] = set()
        _lv38_collections_aliases(
            node, imported_factories, imported_modules)
        aliased_factories, aliased_modules = _lv38_alias_bindings(
            node, frozenset(active_factories), frozenset(active_modules))
        imported_factories |= aliased_factories
        imported_modules |= aliased_modules
        for name in _lv36_bound_names(node) - event_shadow:
            active_factories.discard(name)
            active_modules.discard(name)
        for name in imported_factories - event_shadow:
            active_modules.discard(name)
            active_factories.add(name)
        for name in imported_modules - event_shadow:
            active_factories.discard(name)
            active_modules.add(name)
        index += 1
    return index
def _lv38_binding_states(
        scoped: list[tuple[ast.AST, frozenset[str]]],
        children: list[ast.AST],
        inherited_factories: frozenset[str],
        inherited_modules: frozenset[str],
        static_shadow: frozenset[str],
        ) -> tuple[
            dict[int, tuple[frozenset[str], frozenset[str]]],
            dict[int, tuple[frozenset[str], frozenset[str]]],
            frozenset[str], frozenset[str]]:
    events = _lv36_binding_events(scoped)
    events.extend(
        (binding_evaluation_position(child), child, _EMPTY_SHADOW)
        for child in children)
    events.sort(key=lambda item: item[0])
    milestones = [
        ((node.lineno, node.col_offset), node, shadow, False)
        for node, shadow in scoped if isinstance(node, ast.Call)]
    milestones.extend(
        (binding_evaluation_position(child), child, _EMPTY_SHADOW, True)
        for child in children)
    milestones.sort(key=lambda item: item[0])
    active_factories = set(inherited_factories - static_shadow)
    active_modules = set(inherited_modules - static_shadow)
    states: dict[int, tuple[frozenset[str], frozenset[str]]] = {}
    definition_states: dict[int, tuple[
        frozenset[str], frozenset[str]]] = {}
    index = 0
    for position, node, _shadow, is_definition in milestones:
        index = _lv38_alias_replay(
            events, index, position, active_factories, active_modules)
        factories = frozenset(active_factories)
        modules = frozenset(active_modules)
        if is_definition:
            definition_states[id(node)] = (factories, modules)
        else:
            states[id(node)] = (factories, modules)
    _lv38_alias_replay(
        events, index, None, active_factories, active_modules)
    return (states, definition_states, frozenset(active_factories),
            frozenset(active_modules))
def _lv38_scan_scope(
        scope: ast.AST, src_lines: list[str], filepath: Any,
        inherited_factories: frozenset[str] = _EMPTY_SHADOW,
        inherited_modules: frozenset[str] = _EMPTY_SHADOW,
        inherited_shadow: frozenset[str] = _EMPTY_SHADOW,
        definition_bindings: tuple[
            frozenset[str], frozenset[str], frozenset[str]] | None = None,
        ) -> list[dict[str, Any]]:
    scoped_nodes = scope_nodes_with_shadow(scope)
    outer_ids = definition_outer_node_ids(scope)
    local_scoped = [
        (node, shadow) for node, shadow in scoped_nodes
        if id(node) not in outer_ids]
    children = child_scopes(scope)
    own_bindings = frozenset(scope_local_bindings(scope))
    static_shadow = (
        own_bindings
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))
        else _EMPTY_SHADOW)
    call_states, child_definitions, final_factories, final_modules = (
        _lv38_binding_states(
            local_scoped, children, inherited_factories, inherited_modules,
            static_shadow)
    )
    call_bindings, definition_local_bindings = (
        _ordered_local_binding_states(scope, local_scoped, children))
    outer_factories, outer_modules, outer_shadow = (
        definition_bindings
        or (inherited_factories, inherited_modules, inherited_shadow)
    )
    empty_state = (_EMPTY_SHADOW, _EMPTY_SHADOW)
    issues: list[dict[str, Any]] = []
    for node, local_shadow in scoped_nodes:
        is_outer = id(node) in outer_ids
        if is_outer:
            call_factories, call_modules = outer_factories, outer_modules
        else:
            call_factories, call_modules = call_states.get(
                id(node), empty_state)
        if is_outer:
            shadow = outer_shadow | local_shadow
        else:
            local_bindings = (
                own_bindings
                if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))
                else call_bindings.get(id(node), _EMPTY_SHADOW))
            shadow = inherited_shadow | local_bindings | local_shadow
        defect = _lv38_bad_factory_call(
            node, call_factories - local_shadow, call_modules - local_shadow,
            shadow)
        if not defect:
            continue
        if defect == 'keyword':
            title = 'default_factory 关键字被当作初始条目：默认工厂未设置'
            description = (
                '``defaultdict(default_factory=list)`` 并不会设置默认工厂：'
                'CPython 的首个工厂参数是位置专用参数，该关键字会进入初始'
                '字典，而 ``default_factory`` 仍为 None；访问缺失键时抛 '
                'KeyError，预期的自动初始化静默失效。'
            )
            treatment = (
                '根因：把位置专用的首个工厂参数误写成关键字参数。\n'
                '修复策略：改用 ``defaultdict(list)`` 的位置实参形态；\n'
                '若确实需要名为 default_factory 的初始键，应显式构造字典，\n'
                '避免与工厂配置意图混淆。'
            )
        else:
            title = 'defaultdict 默认工厂传非 callable 字面量：必抛 TypeError'
            description = (
                '``defaultdict([])`` 形态——默认工厂实参须为 callable'
                '（类对象/函数），容器字面量/标量常量在构造时即抛 '
                'TypeError: first argument must be callable or None；'
                '意图「每键自动空列表」的正确写法是传 ``list`` 类'
                '对象本身。'
            )
            treatment = (
                '根因：把「每键空容器」的意图直接写成容器字面量，\n'
                '混淆「工厂（callable）」与「工厂产物（值）」。\n'
                '修复策略：``defaultdict(list)`` / ``defaultdict(dict)``\n'
                '传类型对象；动态构造用 ``defaultdict(lambda: [])``；\n'
                '显式初始化用 ``dict.fromkeys`` 或推导式（注意 LV-37\n'
                '可变默认共享域）。'
            )
        issues.append(make_issue(
            'LV-38', 'P1', 'logic_correctness', filepath, node.lineno,
            title, description, snippet_of(src_lines, node.lineno),
            treatment + '\n参考标准：CPython collections.defaultdict 契约',
            'defaultdict-noncallable-default',
        ))
    child_factories, child_modules = child_inherited_shadow(
        scope, final_factories, inherited_factories), child_inherited_shadow(
        scope, final_modules, inherited_modules)
    visible_shadow = inherited_shadow | own_bindings
    child_shadow = child_inherited_shadow(
        scope, visible_shadow, inherited_shadow)
    for child in children:
        definition_shadow = (
            visible_shadow
            if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))
            else inherited_shadow | definition_local_bindings.get(
                id(child), _EMPTY_SHADOW))
        child_factories_at_def, child_modules_at_def = child_definitions[id(child)]
        issues.extend(_lv38_scan_scope(
            child, src_lines, filepath, child_factories, child_modules,
            child_shadow,
            (child_factories_at_def, child_modules_at_def, definition_shadow)))
    return issues
def check_LV38(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    return run_scope_scan(tree, source, filepath, _lv38_scan_scope)
_LV44_NODE_KINDS: dict[type, str] = {
    ast.JoinedStr: 'str',
    ast.List: 'list',
    ast.ListComp: 'list',
    ast.Tuple: 'tuple',
    ast.Dict: 'dict',
    ast.DictComp: 'dict',
    ast.Set: 'set',
    ast.SetComp: 'set',
    ast.GeneratorExp: 'generator',
}
_LV44_NONE_KIND = 'none'
_LV44_FUNCTION_KIND = 'function'
_LV44_ADD_COMPATIBLE = frozenset({
    ('str', 'str'), ('bytes', 'bytes'), ('num', 'num'),
    ('list', 'list'), ('tuple', 'tuple'),
})
def _lv44_constant_kind(value: Any) -> str | None:
    if value is None or value is Ellipsis:
        return _LV44_NONE_KIND
    if isinstance(value, (bool, int, float, complex)):
        return 'num'
    if isinstance(value, str):
        return 'str'
    if isinstance(value, (bytes, bytearray)):
        return 'bytes'
    return None
def _lv44_literal_kind(node: ast.expr) -> str | None:
    if isinstance(node, ast.NamedExpr):
        return _lv44_literal_kind(node.value)
    if signed_numeric_literal(node) is not None:
        return 'num'
    if isinstance(node, ast.IfExp):
        body = _lv44_literal_kind(node.body)
        orelse = _lv44_literal_kind(node.orelse)
        return body if body is not None and body == orelse else None
    if isinstance(node, ast.BinOp):
        return _lv44_add_chain_kind(node)
    if isinstance(node, ast.Constant):
        return _lv44_constant_kind(node.value)
    return _LV44_NODE_KINDS.get(type(node))
def _lv44_add_chain_kind(node: ast.BinOp) -> str | None:
    if not isinstance(node.op, ast.Add):
        return None
    left = _lv44_literal_kind(node.left)
    right = _lv44_literal_kind(node.right)
    if left is None or right is None:
        return None
    return left if (left, right) in _LV44_ADD_COMPATIBLE else None
_LV44_AUGADD_COMPATIBLE = frozenset({
    ('num', 'num'), ('str', 'str'), ('bytes', 'bytes'), ('tuple', 'tuple'),
})
_LV44_IADD_LIST_RIGHT_OK = frozenset({
    'list', 'tuple', 'str', 'bytes', 'set', 'dict', 'generator',
})
_LV44_ANNOTATION_KINDS: dict[str, str] = {
    'int': 'num', 'float': 'num', 'complex': 'num', 'bool': 'num',
    'str': 'str', 'bytes': 'bytes', 'bytearray': 'bytes',
    'list': 'list', 'tuple': 'tuple', 'dict': 'dict', 'set': 'set',
    'frozenset': 'set',
}
def _lv44_annotation_kind(node: ast.expr | None) -> str | None:
    if node is None:
        return None
    if isinstance(node, ast.Constant):
        return None
    if isinstance(node, ast.Subscript):
        node = node.value
    if isinstance(node, ast.Attribute):
        return _LV44_ANNOTATION_KINDS.get(node.attr)
    if isinstance(node, ast.Name):
        return _LV44_ANNOTATION_KINDS.get(node.id)
    return None
def _lv44_scope_walk(stmts: Any) -> Any:
    stack = list(reversed(stmts))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda,
                             ast.ListComp, ast.SetComp,
                             ast.DictComp, ast.GeneratorExp)):
            yield node, True
            continue
        yield node, False
        stack.extend(reversed(list(ast.iter_child_nodes(node))))
def _lv44_nonruntime_annotation_ids(tree: ast.AST) -> frozenset[int]:
    postponed = isinstance(tree, ast.Module) and any(
        isinstance(node, ast.ImportFrom) and node.module == '__future__'
        and any(alias.name == 'annotations' for alias in node.names)
        for node in tree.body
    )
    excluded: set[int] = set()
    def exclude(annotation: ast.AST | None) -> None:
        if annotation is not None:
            excluded.update(id(node) for node in walk_nodes(annotation))
    if postponed:
        for node in walk_nodes(tree):
            if isinstance(node, ast.AnnAssign):
                exclude(node.annotation)
            elif isinstance(node, ast.arg):
                exclude(node.annotation)
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                exclude(node.returns)
        return frozenset(excluded)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for sub, boundary in _lv44_scope_walk(node.body):
            if not boundary and isinstance(sub, ast.AnnAssign):
                exclude(sub.annotation)
    return frozenset(excluded)
def _lv44_target_kind_pairs(
        target: ast.AST,
        value: ast.AST) -> list[tuple[str, str | None]]:
    if isinstance(target, ast.Name):
        return [(target.id, _lv44_literal_kind(value))]
    aligned = aligned_unpack_pairs(target, value)
    if aligned is None:
        return [(name, None) for name in target_binding_names(target)]
    pairs: list[tuple[str, str | None]] = []
    for sub_target, sub_value in aligned:
        pairs.extend(_lv44_target_kind_pairs(sub_target, sub_value))
    return pairs
def _lv44_assign_bindings(node: ast.Assign) -> list[tuple[str, str | None]]:
    bindings: list[tuple[str, str | None]] = []
    for target in node.targets:
        bindings.extend(_lv44_target_kind_pairs(target, node.value))
    return bindings
def _lv44_target_owner_bindings(node: ast.AST) -> list[tuple[str, str | None]]:
    if isinstance(node, ast.NamedExpr):
        kind = _lv44_literal_kind(node.value)
        return [(name, kind) for name in target_binding_names(node.target)]
    if isinstance(node, (ast.For, ast.AsyncFor)):
        targets: list[ast.AST] = [node.target]
        return [(name, None) for target in targets
                for name in target_binding_names(target)]
    # 未登记的节点类型不得落到未绑定变量（注册表之外的调用方也会走到这里）。
    return []
def _lv44_asname_bindings(node: ast.AST) -> list[tuple[str, str | None]]:
    return [(name, None) for name in capture_binding_names(node)]
def _lv44_delete_bindings(node: ast.Delete) -> list[tuple[str, str | None]]:
    names: list[str] = []
    stack = list(node.targets)
    while stack:
        target = stack.pop()
        if isinstance(target, ast.Name):
            names.append(target.id)
        elif isinstance(target, (ast.Tuple, ast.List)):
            stack.extend(target.elts)
        elif isinstance(target, ast.Starred):
            stack.append(target.value)
    return [(name, None) for name in names]
def _lv44_import_bindings(node: ast.AST) -> list[tuple[str, str | None]]:
    names, _star_seen = import_bound_names(node)
    return [(name, None) for name in names]
def _lv44_definition_bindings(node: ast.AST) -> list[tuple[str, str | None]]:
    kind = (_LV44_FUNCTION_KIND
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            else None)
    return [(node.name, kind)]
_LV44_BINDING_EXTRACTORS: dict[type, Any] = {
    ast.Assign: _lv44_assign_bindings,
    ast.For: _lv44_target_owner_bindings,
    ast.AsyncFor: _lv44_target_owner_bindings,
    ast.NamedExpr: _lv44_target_owner_bindings,
    ast.Delete: _lv44_delete_bindings,
    ast.ExceptHandler: _lv44_asname_bindings,
    ast.MatchAs: _lv44_asname_bindings,
    ast.MatchStar: _lv44_asname_bindings,
    ast.MatchMapping: _lv44_asname_bindings,
    ast.Import: _lv44_import_bindings,
    ast.ImportFrom: _lv44_import_bindings,
    ast.FunctionDef: _lv44_definition_bindings,
    ast.AsyncFunctionDef: _lv44_definition_bindings,
    ast.ClassDef: _lv44_definition_bindings,
}
def _lv44_rebinding(node: ast.AST) -> list[tuple[str, str | None]]:
    extractor = _LV44_BINDING_EXTRACTORS.get(type(node))
    return extractor(node) if extractor is not None else []
def _lv44_named_params(args: ast.arguments) -> list[Any]:
    return (list(getattr(args, 'posonlyargs', []) or [])
            + list(args.args or [])
            + list(args.kwonlyargs or []))
def _lv44_all_params(args: ast.arguments) -> list[Any]:
    params = _lv44_named_params(args)
    params += [a for a in (args.vararg, args.kwarg) if a is not None]
    return params
_LV44_VARARG_CONTAINERS: tuple[tuple[str, str], ...] = (
    ('vararg', 'tuple'), ('kwarg', 'dict'))
def _lv44_param_kinds(func: Any) -> dict[str, str]:
    kinds: dict[str, str] = {}
    args = func.args
    for a in _lv44_named_params(args):
        kind = _lv44_annotation_kind(a.annotation)
        if kind is not None:
            kinds[a.arg] = kind
    for attr, container in _LV44_VARARG_CONTAINERS:
        a = getattr(args, attr, None)
        if a is not None:
            kinds[a.arg] = container
    return kinds
class _LV44Evidence:
    def __init__(self) -> None:
        self.annotation_kinds: dict[str, str] = {}
        self.events: dict[
            str, list[tuple[tuple[int, int], str | None, bool]]] = {}
        self.conflicts: set[str] = set()
    def record_annotation(self, name: str, kind: str | None,
                          node: ast.AST | None, *,
                          has_value: bool,
                          preserve_outer: bool = False) -> None:
        if kind is None:
            return
        position = node_end_position(node)
        if not has_value:
            latest: tuple[tuple[int, int], str | None, bool] | None = None
            for event in self.events.get(name, []):
                if event[0] < position and (
                        latest is None or event[0] >= latest[0]):
                    latest = event
            if latest is not None and latest[2] and latest[1] is not None:
                return
            if latest is None and preserve_outer:
                return
        if name in self.conflicts:
            self._append(name, position, None, runtime=has_value)
            return
        prev = self.annotation_kinds.get(name)
        if prev is not None and prev != kind:
            self.conflicts.add(name)
            self._append(name, position, None, runtime=has_value)
            return
        self.annotation_kinds[name] = kind
        self._append(name, position, kind, runtime=has_value)
    def record_binding(self, node: ast.AST) -> None:
        if isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                if item.optional_vars is None:
                    continue
                pos = _with_item_binding_position(item)
                for name in target_binding_names(item.optional_vars):
                    self._append(name, pos, None)
            return
        bindings = _lv44_rebinding(node)
        if not bindings:
            return
        pos = binding_evaluation_position(node)
        for name, kind in bindings:
            self._append(name, pos, kind)
    def _append(self, name: str, pos: tuple[int, int],
                kind: str | None, *, runtime: bool = True) -> None:
        self.events.setdefault(name, []).append((pos, kind, runtime))
    def resolve(self, visible: dict[str, str],
                pos: tuple[int, int] | None = None) -> dict[str, str]:
        scoped = dict(visible)
        for name, events in self.events.items():
            found = False
            best_pos: tuple[int, int] | None = None
            kind: str | None = None
            runtime = False
            for ev_pos, ev_kind, ev_runtime in events:
                if pos is not None and ev_pos >= pos:
                    continue
                if best_pos is None or ev_pos >= best_pos:
                    best_pos, kind, found = ev_pos, ev_kind, True
                    runtime = ev_runtime
            if not found:
                continue
            if not runtime or kind is None:
                scoped.pop(name, None)
            else:
                scoped[name] = kind
        return scoped
class _LV44ScopeScanner:
    def __init__(self, src_lines: list[str], filepath: Any,
                 nonruntime_annotations: frozenset[int] = frozenset()) -> None:
        self.issues: list[dict[str, Any]] = []
        self.src_lines = src_lines
        self.filepath = filepath
        self.nonruntime_annotations = nonruntime_annotations
    def collect_scope(self, stmts: Any, *, is_class: bool = False
                      ) -> tuple[_LV44Evidence, list, list, list]:
        evidence = _LV44Evidence()
        nested: list[ast.AST] = []
        binops: list[ast.BinOp] = []
        augassigns: list[ast.AugAssign] = []
        for sub, boundary in _lv44_scope_walk(stmts):
            if id(sub) in self.nonruntime_annotations:
                continue
            if boundary:
                nested.append(sub)
                evidence.record_binding(sub)
            elif (isinstance(sub, ast.AnnAssign)
                  and isinstance(sub.target, ast.Name)):
                annotation_kind = _lv44_annotation_kind(sub.annotation)
                evidence.record_annotation(
                    sub.target.id, annotation_kind, sub.annotation,
                    has_value=sub.value is not None,
                    preserve_outer=is_class)
                literal_kind = (
                    _lv44_literal_kind(sub.value)
                    if sub.value is not None else None)
                if sub.value is not None:
                    evidence._append(
                        sub.target.id, node_end_position(sub.value),
                        literal_kind)
            elif (isinstance(sub, ast.BinOp)
                  and isinstance(sub.op, ast.Add)):
                binops.append(sub)
            elif (isinstance(sub, ast.AugAssign)
                  and isinstance(sub.op, ast.Add)):
                augassigns.append(sub)
            else:
                evidence.record_binding(sub)
        return evidence, nested, binops, augassigns
    def judge_concat(self, node: ast.AST, scoped: dict[str, str],
                     left: ast.expr, right: ast.expr, *,
                     op: str, compatible: frozenset) -> None:
        left_kind = _lv44_literal_kind(left)
        right_kind = _lv44_literal_kind(right)
        if left_kind is None and isinstance(left, ast.Name):
            left_kind = scoped.get(left.id)
        if right_kind is None and isinstance(right, ast.Name):
            right_kind = scoped.get(right.id)
        if not left_kind or not right_kind:
            return
        if (op == '+=' and left_kind == 'list'
                and right_kind in _LV44_IADD_LIST_RIGHT_OK):
            return
        if (left_kind, right_kind) in compatible:
            return
        same_family = left_kind == right_kind
        if left_kind == _LV44_NONE_KIND or right_kind == _LV44_NONE_KIND:
            title = f'None/Ellipsis 参与 {op} 拼接：一执行即 TypeError'
            detail = (
                f'``{op}`` 有一侧是 None/Ellipsis——NoneType 与 '
                'Ellipsis 均未实现 ``__add__``，也没有可接受的右操作数 '
                f'协议，一执行即抛 ``TypeError: unsupported operand '
                f"type(s) for {op}``。"
            )
        elif same_family:
            title = f'{left_kind} 不支持 {op} 运算：一执行即 TypeError'
            detail = (
                f'``{op}`` 两侧同为 {left_kind}：{left_kind} 未实现 '
                f'``{op}``，dict/set 合并须用 ``|`` 或 ``update()``——一执行即抛 '
                f'``TypeError: unsupported operand type(s) for {op}``。'
            )
        else:
            title = (f'异族二元拼接 {left_kind} {op} {right_kind}'
                     '：一执行即 TypeError')
            detail = (
                f'``{op}`` 两侧类型族不兼容（{left_kind} 与 {right_kind}）'
                f'——Python ``{op}`` 不做跨族隐式转换，一执行即抛 '
                '``TypeError: can only concatenate`` / '
                f'``unsupported operand type(s) for {op}``。str 拼接须两侧'
                '同为 str；序列拼接仅限同族（list+list / tuple+tuple）；'
                f'dict/set 不支持 ``{op}``（合并用 ``|`` 或 update）。'
            )
        self.issues.append(make_issue(
            'LV-44', 'P1', 'logic_correctness', self.filepath, node.lineno,
            title, detail,
            snippet_of(self.src_lines, node.lineno),
            (
                '根因：弱类型语言隐式转换直觉误用于 Python 强类型\n'
                '二元运算（str+num 无隐式 str()，与 JS/PHP 行为相反）。\n'
                '修复策略：文案拼接用 f-string（``f"count: {n}"``）或\n'
                '``"count: " + str(n)``；序列合并归同族或用 ``[*a, *b]``；\n'
                'dict/set 合并用 ``|`` / ``update()``；bytes 与 str 之间\n'
                '显式 encode/decode。\n'
                '参考标准：CPython 二元运算协议（PyNumber_Add 按类型'
                '分发，无跨族 coercion）'
            ),
            'literal-cross-type-concat',
        ))
    def scan(self, stmts: Any, visible: dict[str, str],
             is_class: bool = False,
             closure_base: dict[str, str] | None = None) -> None:
        evidence, nested, binops, augassigns = self.collect_scope(
            stmts, is_class=is_class)
        for node in binops:
            use_pos = (node.lineno, node.col_offset)
            self.judge_concat(
                node, evidence.resolve(visible, use_pos),
                node.left, node.right, op='+',
                compatible=_LV44_ADD_COMPATIBLE)
        for node in augassigns:
            use_pos = (node.lineno, node.col_offset)
            self.judge_concat(
                node, evidence.resolve(visible, use_pos),
                node.target, node.value, op='+=',
                compatible=_LV44_AUGADD_COMPATIBLE)
        nested_base = visible if is_class else evidence.resolve(visible)
        function_base = (
            closure_base
            if is_class and closure_base is not None else nested_base)
        definition_bases = {
            id(sub): evidence.resolve(visible, (sub.lineno, sub.col_offset))
            for sub in nested
        }
        self._dispatch_nested(
            nested, nested_base, definition_bases, function_base,
            is_class=is_class)
    def _dispatch_function(
            self, sub: ast.FunctionDef | ast.AsyncFunctionDef,
            nested_base: dict[str, str],
            definition_base: dict[str, str]) -> None:
        outer_exprs = [*sub.decorator_list, *sub.args.defaults]
        outer_exprs.extend(
            value for value in sub.args.kw_defaults
            if value is not None)
        outer_exprs.extend(
            arg.annotation for arg in _lv44_all_params(sub.args)
            if arg.annotation is not None)
        if sub.returns is not None:
            outer_exprs.append(sub.returns)
        self.scan(outer_exprs, definition_base)
        shadowed_params = {a.arg for a in _lv44_all_params(sub.args)}
        local_base = {k: v for k, v in nested_base.items()
                      if k not in shadowed_params}
        self.scan(sub.body,
                  {**local_base, **_lv44_param_kinds(sub)})
    def _dispatch_nested(
            self, nested: list, nested_base: dict[str, str],
            definition_bases: dict[int, dict[str, str]],
            function_base: dict[str, str], *, is_class: bool = False) -> None:
        for sub in nested:
            definition_base = definition_bases.get(id(sub), nested_base)
            if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self._dispatch_function(
                    sub, function_base, definition_base)
            elif isinstance(sub, ast.ClassDef):
                outer_exprs = [*sub.decorator_list, *sub.bases]
                outer_exprs.extend(kw.value for kw in sub.keywords)
                self.scan(outer_exprs, definition_base)
                self.scan(
                    sub.body, definition_base, is_class=True,
                    closure_base=function_base)
            elif isinstance(sub, ast.Lambda):
                outer_exprs = list(sub.args.defaults)
                outer_exprs.extend(
                    value for value in sub.args.kw_defaults
                    if value is not None)
                self.scan(outer_exprs, definition_base)
                shadowed = {a.arg for a in _lv44_all_params(sub.args)}
                lambda_base = {k: v for k, v in function_base.items()
                               if k not in shadowed}
                self.scan([sub.body],
                          {**lambda_base, **_lv44_param_kinds(sub)})
            else:
                self._dispatch_comprehension(
                    sub, nested_base, definition_base,
                    closure_base=function_base, is_class=is_class)
    def _dispatch_comprehension(
            self, sub: ast.expr, nested_base: dict[str, str],
            definition_base: dict[str, str], *,
            closure_base: dict[str, str], is_class: bool = False) -> None:
        eager = not isinstance(sub, ast.GeneratorExp)
        if is_class:
            body_base = nested_base if eager else closure_base
        else:
            body_base = definition_base if eager else nested_base
        visible = dict(definition_base)
        for index, gen in enumerate(sub.generators):
            if index == 0:
                self.scan([gen.iter], definition_base)
                visible = dict(body_base)
            else:
                self.scan([gen.iter], visible)
            shadowed = set(target_binding_names(gen.target))
            visible = {k: v for k, v in visible.items() if k not in shadowed}
            self.scan(list(gen.ifs), visible)
        if isinstance(sub, ast.DictComp):
            self.scan([sub.key, sub.value], visible)
        else:
            self.scan([sub.elt], visible)
def check_LV44(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    if not isinstance(tree, ast.AST):
        return []
    if isinstance(tree, ast.Module):
        stmts: list[Any] = tree.body
    elif isinstance(tree, ast.Expression):
        stmts = [tree.body]
    else:
        stmts = [tree]
    src_lines = source_lines(source)
    scanner = _LV44ScopeScanner(
        src_lines, filepath, _lv44_nonruntime_annotation_ids(tree))
    scanner.scan(stmts, {})
    return scanner.issues

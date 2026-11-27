from __future__ import annotations

import ast
import logging
import os
import threading
from collections import deque
from collections.abc import Callable, Iterator
from typing import Any, NamedTuple
from weakref import WeakKeyDictionary

__all__ = [
    'BINDING_FORM_HANDLERS',
    'COMP_NODES',
    'FUNC_SCOPE_NODES',
    'INPLACE_MUTATOR_METHODS',
    'MATCH_MAPPING_TYPE',
    'PATTERN_BIND_NODES',
    'READS_SELF_FORMS',
    'SCOPE_CONTAINERS',
    'TRY_NODES',
    'FlowVarResolver',
    'aligned_unpack_pairs',
    'assert_always_fails',
    'assigned_names',
    'bare_single_arg_call',
    'binding_body_start',
    'binding_entries_index',
    'binding_evaluation_position',
    'block_exits',
    'block_never_falls_through',
    'bound_names',
    'bound_names_of',
    'branch_truth',
    'break_binding_loop',
    'capture_binding_names',
    'child_inherited_shadow',
    'child_scopes',
    'comprehension_elt_nodes',
    'comprehension_shadows_name',
    'constant_truth',
    'construct_shadows_name',
    'definition_evaluated_children',
    'definition_outer_children',
    'definition_outer_node_ids',
    'deref_root_name',
    'flow_var_resolver',
    'func_name_of_call',
    'has_starred_arg',
    'import_bound_names',
    'imported_module_aliases',
    'int_literal',
    'is_constant_true_while',
    'is_dataclass_decorator',
    'is_irrefutable_pattern',
    'is_none_constant',
    'is_statically_unreachable',
    'iter_binding_entries',
    'iter_nodes_outside',
    'loop_has_binding',
    'make_issue',
    'match_always_exits',
    'nearest_scope',
    'node_end_position',
    'param_names',
    'parent_map_of',
    'preceding_statements',
    'prior_statements',
    'range_len_source',
    'rebound_binding_names',
    'run_scope_scan',
    'same_expr',
    'scan_body_no_funcs',
    'scan_context',
    'scope_bindings_cached',
    'scope_body_stmts',
    'scope_chain',
    'scope_definition_names',
    'scope_function_defs',
    'scope_local_bindings',
    'scope_nodes_with_shadow',
    'scoped_shadow_map',
    'shadowed_binding_at',
    'signed_numeric_literal',
    'snippet_of',
    'source_lines',
    'statically_empty_iterable',
    'stmt_siblings',
    'subtree_contains',
    'target_binding_names',
    'target_store_name_set',
    'target_store_names',
    'try_block_terminates',
    'walk_ast_nodes',
    'walk_nodes',
    'walk_scope_expr',
]
_log = logging.getLogger(__name__)
_log.info(
    "prevention_scope_facts 作用域/绑定/终止性事实域"
    "（含类成员绑定契约与跨轮绑定生命周期）已加载：%d 项导出", len(__all__))
_EMPTY_IDS: frozenset[int] = frozenset()
_EMPTY_SHADOW: frozenset[str] = frozenset()
_DEFAULT_INCLUDE_PARAMS = True
_DEFAULT_INCLUDE_IMPORTS = True
def source_lines(source: Any) -> list[str]:
    if isinstance(source, (list, tuple)):
        return list(source)
    return str(source).split('\n') if source else []
def snippet_of(src_lines: list[str], lineno: int) -> str:
    idx = lineno - 1
    return src_lines[idx].strip() if 0 <= idx < len(src_lines) else ''
def scan_context(tree, source) -> tuple[list[dict[str, Any]], list[str]] | None:
    if not isinstance(tree, ast.AST):
        return None
    return [], source_lines(source)
def run_scope_scan(tree: Any, source: Any, filepath: Any,
                    scan: Callable[..., list[dict[str, Any]]]) -> list[dict[str, Any]]:
    ctx = scan_context(tree, source)
    if ctx is None or not isinstance(tree, SCOPE_CONTAINERS):
        return []
    return scan(tree, ctx[1], filepath)
def branch_truth(parent: ast.AST, cur: ast.AST) -> bool | None:
    if isinstance(parent, (ast.If, ast.While)):
        if any(stmt is cur for stmt in getattr(parent, 'body', ())):
            return True
        if any(stmt is cur for stmt in getattr(parent, 'orelse', ())):
            return False
    elif isinstance(parent, ast.IfExp):
        if parent.body is cur:
            return True
        if parent.orelse is cur:
            return False
    return None
def make_issue(rule_id: str, severity: str, dimension: str,
                filepath: str, lineno: int, title: str,
                description: str, snippet: str, suggestion: str,
                rule_ref: str) -> dict[str, Any]:
    return {
        'rule_id': rule_id, 'severity': severity, 'dimension': dimension,
        'file': filepath, 'line': lineno, 'title': title,
        'description': description, 'code_snippet': snippet,
        'suggestion': suggestion, 'rule_ref': rule_ref,
    }
FUNC_SCOPE_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)
SCOPE_CONTAINERS = (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                    ast.ClassDef)
NESTED_SCOPES = FUNC_SCOPE_NODES
TRY_NODES = tuple(
    t for t in (ast.Try, getattr(ast, 'TryStar', None)) if t is not None
)
PATTERN_BIND_NODES = tuple(
    t for t in (getattr(ast, 'MatchAs', None), getattr(ast, 'MatchStar', None))
    if t is not None
)
MATCH_MAPPING_TYPE = getattr(ast, 'MatchMapping', None)
_TYPE_ALIAS_NODE = getattr(ast, 'TypeAlias', None)
def iter_nodes_outside(root: ast.AST,
                        stop_nodes: tuple[type, ...] = FUNC_SCOPE_NODES):
    if isinstance(root, stop_nodes):
        return
    stack = [root]
    while stack:
        node = stack.pop()
        yield node
        for child in _field_children(node):
            if not isinstance(child, stop_nodes):
                stack.append(child)
_WALK_NODES_CACHE: WeakKeyDictionary[Any, tuple[ast.AST, ...]] = WeakKeyDictionary()
_WALK_NODES_MISS = object()
# 两个缓存的构建成本相差一个数量级：walk_nodes 命中时只是取回列表，而
# parent_map 每次未命中都要重新遍历整棵子树。共用一个上限时，walk_nodes 的
# 大量小根（Name/Constant 等）会把按文件建立的父映射挤出缓存，导致每个作用域
# 都重算一次 O(节点数) 的父映射——即 O(作用域 x 深度) 退化。故分开设限，
# 并让父映射容量远大于并发文件数，使其在扫描期间一直命中。
_AST_CACHE_MAX = 1024
_PARENT_MAP_CACHE_MAX = 256
def _field_value_nodes(value: Any):
    if isinstance(value, ast.AST):
        yield value
        return
    if isinstance(value, list):
        yield from (item for item in value if isinstance(item, ast.AST))
def _field_children(node: ast.AST):
    for field in node._fields:
        value = getattr(node, field, _WALK_NODES_MISS)
        if value is not _WALK_NODES_MISS:
            yield from _field_value_nodes(value)
#: ``binding_entries_index`` 的语句列表级缓存。
#:
#: 实测 ``iter_binding_entries`` 单文件被调用 **140,812 次**（累计 20.8 s），
#: 每次都要把整个语句列表遍历一遍，而调用方几乎都只是「按绑定名过滤」——
#: 同一份遍历结果被反复重算。改为按语句列表 memo 化的「绑定名 → 项」倒排表后，
#: 按名过滤是 O(桶长)，不再是 O(子树节点数)。
#:
#: 键用 ``id(stmts)``、值里再存一份 ``stmts`` 强引用：缓存持有强引用，
#: 因此 id 在这期间不可能被回收复用，身份校验只是形式上的双保险。
_BINDING_INDEX_CACHE: dict[int, tuple[list, dict]] = {}
_BINDING_INDEX_LOCK = threading.Lock()
_BINDING_INDEX_MAX = 256


def binding_entries_index(stmts: list) -> dict[str, tuple]:
    """把 ``iter_binding_entries(stmts)`` 的结果按绑定名分桶（语句列表级 memo）。

    返回 ``{绑定名: ((node, value), ...)}``，每个桶内保持原生成的先后顺序，
    因此::

        [(n, v) for n, bound, v in iter_binding_entries(stmts) if bound == name]

    与 ``list(index.get(name, ()))`` **逐项等价（含顺序）**。调用方只读，
    不得修改返回的元组。
    """
    key = id(stmts)
    with _BINDING_INDEX_LOCK:
        hit = _BINDING_INDEX_CACHE.get(key)
    if hit is not None and hit[0] is stmts:
        return hit[1]
    buckets: dict[str, list] = {}
    for node, name, value in iter_binding_entries(stmts):
        buckets.setdefault(name, []).append((node, value))
    index = {name: tuple(items) for name, items in buckets.items()}
    with _BINDING_INDEX_LOCK:
        _BINDING_INDEX_CACHE[key] = (stmts, index)
        while len(_BINDING_INDEX_CACHE) > _BINDING_INDEX_MAX:
            _BINDING_INDEX_CACHE.pop(next(iter(_BINDING_INDEX_CACHE)), None)
    return index


def _evict_excess(cache, max_size: int) -> None:
    """把弱键缓存逐出到 ``max_size`` 以内。

    历史缺陷：``del cache[next(iter(cache))]`` 在 ``WeakKeyDictionary`` 上会在
    取键与删除之间被 GC 抢先回收弱引用，抛 ``KeyError``（实测中断诊断，日志
    留下 ``KeyError: <weakref ... to 'Return'>``）。逐出本身是尽力而为的
    内存收敛，单条已被回收即视为已逐出，跳过后继续。
    """
    while len(cache) > max_size:
        try:
            victim = next(iter(cache))
        except StopIteration:
            return
        try:
            del cache[victim]
        except KeyError:
            continue
def _cached_tree_value(cache, root: Any, builder, label: str,
                       *, max_size: int = _AST_CACHE_MAX):
    try:
        cached = cache.get(root)
    except TypeError as _e:
        _log.debug('静默降级[%s:TypeError]: %s: %s', label,
                   type(_e).__name__, _e)
        return builder(root)
    if cached is None:
        cached = builder(root)
        try:
            cache[root] = cached
        except TypeError as _e:
            _log.debug('静默降级[%s:TypeError]: %s: %s', label,
                       type(_e).__name__, _e)
        else:
            _evict_excess(cache, max_size)
    return cached
#: ``walk_nodes`` 专用容量。实测单文件有 **14,608 个不同 root**（每个 AST 节点
#: 都可能被当作子树根），而通用上限 1024 远小于它——每次写入都在逐出，
#: 命中率归零并退化成「每次都重建子树」。
#:
#: 内存代价可控：14,608 个子树共 1,343,205 个节点引用 ≈ 11 MB；
#: 而且缓存键是弱引用（``WeakKeyDictionary``），AST 回收时条目自动消失。
#: ``walk_nodes`` 专用容量。实测单文件有 **14,608 个不同 root**（每个 AST 节点
#: 都可能被当作子树根），而通用上限 1024 远小于它——每次写入都在逐出，
#: 命中率归零并退化成「每次都重建子树」。
#:
#: 内存代价可控：14,608 个子树共 1,343,205 个节点引用 ≈ 11 MB；
#: 而且缓存键是弱引用（``WeakKeyDictionary``），AST 回收时条目自动消失。
_WALK_NODES_CACHE_MAX = 16384

#: ``JWSGJ_WALK_VERIFY=1`` 时，每次命中都重新 ``ast.walk`` 并逐项做 ``is`` 比对。
#:
#: 缓存的是**节点身份序列**而不是计算结果，因此 ``lineno`` / ``col_offset`` 等
#: 属性变异不影响正确性，只有「增删子节点」这类**结构性变异**才需要失效。
#: 已逐一核对全部结构性变异点（``diag_structure_arch``、``diag_testing_source``、
#: ``diag_wiring_symbol_scan``、``skill_scan_kernels``、``code_level_feedback_l2``、
#: ``build_import_time_guard``、``diag_shared_ast_nodes`` 的 ``clone.*`` 系列），
#: 均为 ``copy.deepcopy`` 后再改，不触碰共享树。本开关把这条不变量变成可执行的回归检查。
_WALK_VERIFY = os.environ.get('JWSGJ_WALK_VERIFY') == '1'

def _verify_against_fresh_walk(root: ast.AST,
                               cached: tuple[ast.AST, ...]) -> None:
    """自检：确认缓存序列与现场 ``ast.walk`` 逐项同一（仅诊断模式）。"""
    fresh = tuple(ast.walk(root))
    if len(fresh) != len(cached):
        raise AssertionError(
            f'walk_nodes 缓存已过期：{len(cached)} != {len(fresh)} 个节点，'
            f'root={type(root).__name__}——检测过程中发生了结构性变异')
    for index, (old, new) in enumerate(zip(fresh, cached)):
        if old is not new:
            raise AssertionError(
                f'walk_nodes 缓存已过期：第 {index} 项 {type(old).__name__} '
                f'!= {type(new).__name__}，root={type(root).__name__}')

def walk_nodes(root: Any) -> tuple[ast.AST, ...]:
    """返回 ``root`` 的 BFS 节点序列，与 ``tuple(ast.walk(root))`` 逐项等价。

    这是全包唯一的 AST 遍历原语：156 个模块共享同一份序列，同一棵树只真实
    遍历一次。实测单文件（134 KB / 25,718 个节点）被独立遍历 **358 次**，
    累计产出 9,196,199 个节点，对应 ``ast.iter_child_nodes`` 31,967,415 次、
    ``ast.iter_fields`` 40,728,687 次——合并后整树真实遍历降到 213 次（-86.4%）。

    **只读契约**：返回元组而非列表。``ast.walk`` 本身返回生成器，它的合法
    用法只有迭代 / ``list()`` / ``next()`` / 解包，元组在这些用法上完全等价；
    而元组能保证调用方无法污染共享缓存（列表一旦被某个调用方 ``.append`` /
    ``.sort`` / ``.remove``，所有后续调用方都会拿到脏数据）。

    缓存键是 AST 对象本身（``WeakKeyDictionary``），AST 回收时条目自动消失，
    因此不存在 ``id`` 复用导致的错命中。

    Args:
        root: 任意 AST 节点。

    Returns:
        只读元组，元素与 ``ast.walk`` 同序同身份。

    Raises:
        与 ``ast.walk(root)`` 完全相同的异常（非 AST 入参时），不静默返回空序列。
    """
    try:
        cached = _WALK_NODES_CACHE.get(root)
    except TypeError as _e:
        _log.debug('静默降级[walk_nodes:TypeError]: %s: %s',
                   type(_e).__name__, _e)
        return tuple(ast.walk(root))
    if cached is not None:
        if _WALK_VERIFY:
            _verify_against_fresh_walk(root, cached)
        return cached
    nodes = tuple(ast.walk(root))
    try:
        _WALK_NODES_CACHE[root] = nodes
    except TypeError as _e:
        _log.debug('静默降级[walk_nodes:TypeError]: %s: %s',
                   type(_e).__name__, _e)
        return nodes
    _evict_excess(_WALK_NODES_CACHE, _WALK_NODES_CACHE_MAX)
    return nodes

def walk_ast_nodes(root: Any) -> tuple[ast.AST, ...]:
    """``walk_nodes`` 的空值安全变体：非 AST 入参返回空元组。"""
    return walk_nodes(root) if isinstance(root, ast.AST) else ()

def scope_body_stmts(scope: ast.AST) -> list[ast.AST]:
    body = getattr(scope, 'body', None)
    if isinstance(body, list):
        return body
    return [body] if isinstance(body, ast.AST) else []
def scan_body_no_funcs(stmts: list) -> list[ast.AST]:
    nodes: list[ast.AST] = []
    for stmt in stmts:
        if isinstance(stmt, FUNC_SCOPE_NODES):
            continue
        nodes.extend(iter_nodes_outside(stmt))
    return nodes
def target_store_names(target: ast.AST, lineno: int):
    for n in walk_nodes(target):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
            yield n.id, lineno
def _assign_form_binds(node: ast.Assign):
    for t in node.targets:
        for name, _lineno in target_store_names(t, node.lineno):
            yield name, node.value
def _augassign_form_binds(node: ast.AugAssign):
    for name, _lineno in target_store_names(node.target, node.lineno):
        yield name, None
def _annassign_form_binds(node: ast.AnnAssign):
    if node.value is None:
        return
    for name, _lineno in target_store_names(node.target, node.lineno):
        yield name, node.value
def _iter_form_binds(node: ast.For | ast.AsyncFor):
    for name, _lineno in target_store_names(node.target, node.lineno):
        yield name, node.iter
def _with_form_binds(node: ast.With | ast.AsyncWith):
    for item in node.items:
        if item.optional_vars is not None:
            for name, _lineno in target_store_names(
                    item.optional_vars, node.lineno):
                yield name, item.context_expr
def _namedexpr_form_binds(node: ast.NamedExpr):
    yield node.target.id, node.value
def _import_form_binds(node: ast.Import):
    for alias in node.names:
        yield alias.asname or alias.name.split(".")[0], None
def _importfrom_form_binds(node: ast.ImportFrom):
    for alias in node.names:
        if alias.name != "*":
            yield alias.asname or alias.name, None
def _pattern_form_binds(node: ast.AST):
    name = getattr(node, 'name', None)
    if name:
        yield name, None
def _mapping_form_binds(node: ast.AST):
    if node.rest:
        yield node.rest, None
def _type_alias_form_binds(node: ast.AST):
    name = getattr(node, 'name', None)
    if isinstance(name, ast.Name):
        yield name.id, None
def _except_form_binds(node: ast.ExceptHandler):
    if node.name:
        yield node.name, None
def _delete_form_binds(node: ast.Delete):
    for target in node.targets:
        for name in _del_names(target):
            yield name, None
BINDING_FORM_HANDLERS: dict[type, Any] = {  # jwsgj:suppress E1-MUTABLE-GLOBAL TP-07 — 审计认可：AST 节点类型分发表，仅导入期一次性填充（含版本门控分支），非共享状态缺陷
    ast.Assign: _assign_form_binds,
    ast.AugAssign: _augassign_form_binds,
    ast.AnnAssign: _annassign_form_binds,
    ast.For: _iter_form_binds,
    ast.AsyncFor: _iter_form_binds,
    ast.With: _with_form_binds,
    ast.AsyncWith: _with_form_binds,
    ast.NamedExpr: _namedexpr_form_binds,
    ast.Import: _import_form_binds,
    ast.ImportFrom: _importfrom_form_binds,
    ast.ExceptHandler: _except_form_binds,
    ast.Delete: _delete_form_binds,
}
BINDING_FORM_HANDLERS.update(
    dict.fromkeys(PATTERN_BIND_NODES, _pattern_form_binds))
if MATCH_MAPPING_TYPE is not None:
    BINDING_FORM_HANDLERS[MATCH_MAPPING_TYPE] = _mapping_form_binds
if _TYPE_ALIAS_NODE is not None:
    BINDING_FORM_HANDLERS[_TYPE_ALIAS_NODE] = _type_alias_form_binds
READS_SELF_FORMS: frozenset[type] = frozenset({ast.AugAssign})
def definition_outer_children(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, ast.Lambda):
        return [node.args]
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        children: list[ast.AST] = [
            *node.decorator_list,
            *getattr(node, 'type_params', ()),
            node.args,
        ]
        if node.returns is not None:
            children.append(node.returns)
        return children
    if isinstance(node, ast.ClassDef):
        return [
            *node.decorator_list,
            *getattr(node, 'type_params', ()),
            *node.bases,
            *(kw.value for kw in node.keywords),
        ]
    return []
def definition_outer_node_ids(scope: ast.AST) -> set[int]:
    return {
        id(node)
        for root in definition_outer_children(scope)
        for node in walk_nodes(root)
    }
def iter_binding_entries(stmts: list):
    for stmt in stmts:
        stack = [stmt]
        while stack:
            node = stack.pop()
            if isinstance(node, FUNC_SCOPE_NODES):
                stack.extend(definition_outer_children(node))
                continue
            handler = BINDING_FORM_HANDLERS.get(type(node))
            if handler is not None:
                for name, value in handler(node):
                    yield node, name, value
            stack.extend(_field_children(node))
def import_bound_names(node: ast.AST) -> tuple[frozenset[str], bool]:
    if not isinstance(node, (ast.Import, ast.ImportFrom)):
        return frozenset(), False
    star_seen = (isinstance(node, ast.ImportFrom)
                 and any(alias.name == '*' for alias in node.names))
    handler = BINDING_FORM_HANDLERS[type(node)]
    return frozenset(name for name, _value in handler(node)), star_seen
def assigned_names(stmts: list) -> dict[str, int]:
    names: dict[str, int] = {}
    for node, name, _value in iter_binding_entries(stmts):
        lineno = node.lineno
        prev = names.get(name)
        if prev is None or lineno < prev:
            names[name] = lineno
    return names
def scope_definition_names(stmts: list) -> set[str]:
    names: set[str] = set()
    stack: list[ast.AST] = list(stmts)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            names.add(node.name)
            continue
        if (_TYPE_ALIAS_NODE is not None
                and isinstance(node, _TYPE_ALIAS_NODE)):
            alias = getattr(node, 'name', None)
            if isinstance(alias, ast.Name):
                names.add(alias.id)
            continue
        if isinstance(node, ast.Lambda):
            continue
        stack.extend(_field_children(node))
    return names
def _store_or_alias_name(node: ast.AST) -> str | None:
    if isinstance(node, ast.Name):
        return node.id if isinstance(node.ctx, ast.Store) else None
    if isinstance(node, ast.alias):
        if node.name == '*':
            return None
        return node.asname or node.name.split('.')[0]
    return None
def _definition_name(node: ast.AST, include_params: bool) -> str | None:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return node.name
    if include_params and isinstance(node, ast.arg):
        return node.arg
    return None
def _bound_name_of(node: ast.AST, include_params: bool) -> str | None:
    return (_store_or_alias_name(node)
            or _definition_name(node, include_params))
_CAPTURE_NAME_ATTRS: dict[type, str] = {ast.ExceptHandler: 'name'}
_CAPTURE_NAME_ATTRS.update(dict.fromkeys(PATTERN_BIND_NODES, 'name'))
if MATCH_MAPPING_TYPE is not None:
    _CAPTURE_NAME_ATTRS[MATCH_MAPPING_TYPE] = 'rest'
def capture_binding_names(node: ast.AST) -> set[str]:
    attr = _CAPTURE_NAME_ATTRS.get(type(node))
    if attr is None:
        return set()
    captured = getattr(node, attr, None)
    return {captured} if captured else set()
def _pattern_capture_names(pattern: ast.AST) -> set[str]:
    return {name for node in walk_nodes(pattern)
            for name in capture_binding_names(node)}
def is_irrefutable_pattern(pattern: ast.AST) -> bool:
    if isinstance(pattern, ast.MatchAs) and pattern.pattern is None:
        return True
    return (isinstance(pattern, ast.MatchOr)
            and any(is_irrefutable_pattern(item) for item in pattern.patterns))
def rebound_binding_names(node: ast.AST) -> set[str]:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return set(target_binding_names(node.target))
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return {name for item in node.items
                if item.optional_vars is not None
                for name in target_binding_names(item.optional_vars)}
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return set(import_bound_names(node)[0])
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        return {node.name}
    if isinstance(node, ast.ExceptHandler):
        return {node.name} if node.name else set()
    if isinstance(node, ast.Delete):
        return {name for tgt in node.targets for name in _del_names(tgt)}
    if isinstance(node, (ast.Global, ast.Nonlocal)):
        return set()
    if _TYPE_ALIAS_NODE is not None and isinstance(node, _TYPE_ALIAS_NODE):
        alias = getattr(node, 'name', None)
        return {alias.id} if isinstance(alias, ast.Name) else set()
    return capture_binding_names(node)
def bound_names_of(node: ast.AST, *,
                    include_params: bool = _DEFAULT_INCLUDE_PARAMS) -> set[str]:
    name = _bound_name_of(node, include_params)
    return {name} if name is not None else capture_binding_names(node)
def bound_names(
        tree: Any, *, include_params: bool = _DEFAULT_INCLUDE_PARAMS,
) -> set[str]:
    names: set[str] = set()
    for node in walk_nodes(tree):
        names |= bound_names_of(node, include_params=include_params)
    return names
def imported_module_aliases(tree: Any, module_name: str) -> set[str]:
    aliases: set[str] = set()
    if not isinstance(tree, ast.AST) or not module_name:
        return aliases
    root = module_name.split('.')[0]
    prefix = module_name + '.'
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            if alias.name == module_name:
                aliases.add(alias.asname or alias.name.split('.')[0])
            elif alias.name.startswith(prefix) and alias.asname is None:
                aliases.add(root)
    return aliases
def param_names(fn: ast.AST) -> set[str]:
    a = getattr(fn, 'args', None)
    if not isinstance(a, ast.arguments):
        return set()
    names = {arg.arg for arg in (a.posonlyargs + a.args + a.kwonlyargs)}
    if a.vararg:
        names.add(a.vararg.arg)
    if a.kwarg:
        names.add(a.kwarg.arg)
    return names
def scope_nodes_with_shadow(scope: ast.AST) -> list[tuple[ast.AST, frozenset]]:
    out: list[tuple[ast.AST, frozenset]] = []
    stack: list[tuple[ast.AST, frozenset]] = [(scope, _EMPTY_SHADOW)]
    while stack:
        node, shadow = stack.pop()
        out.append((node, shadow))
        if isinstance(node, ast.Lambda):
            for default in (*node.args.defaults, *node.args.kw_defaults):
                if default is not None:
                    stack.append((default, shadow))
            stack.append((node.body, shadow | frozenset(param_names(node))))
            continue
        if isinstance(node, (ast.ListComp, ast.SetComp,
                             ast.DictComp, ast.GeneratorExp)):
            current = shadow
            for generator in node.generators:
                stack.append((generator.iter, current))
                current = current | frozenset(
                    name for name, _lineno in target_store_names(
                        generator.target, 0))
                for condition in generator.ifs:
                    stack.append((condition, current))
            if isinstance(node, ast.DictComp):
                stack.append((node.key, current))
                stack.append((node.value, current))
            else:
                stack.append((node.elt, current))
            continue
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)):
                continue
            stack.append((child, shadow))
    return out
def scoped_shadow_map(tree: ast.AST) -> dict[int, frozenset[str]]:
    shadows: dict[int, frozenset[str]] = {}
    if not isinstance(tree, ast.AST):
        return shadows
    parents = parent_map_of(tree)
    def visit(scope: ast.AST, inherited: frozenset[str],
              definition_inherited: frozenset[str]) -> None:
        own = frozenset(scope_local_bindings(scope))
        visible = inherited | own
        outer_ids = definition_outer_node_ids(scope)
        for node, local in scope_nodes_with_shadow(scope):
            if id(node) in outer_ids:
                base = definition_inherited
            elif (isinstance(scope, ast.ClassDef)
                  and not _class_namespace_visible(node, scope, parents)):
                base = inherited
            else:
                base = visible
            shadows[id(node)] = frozenset(base | local)
        child_inherited = (
            inherited if isinstance(scope, ast.ClassDef) else visible)
        for child in child_scopes(scope):
            visit(child, child_inherited, visible)
    visit(tree, _EMPTY_SHADOW, _EMPTY_SHADOW)
    return shadows
_LOCAL_BINDINGS_CACHE: WeakKeyDictionary[Any, frozenset[str]] = WeakKeyDictionary()
_LOCAL_BINDINGS_MAX = 4096


def _is_default_scope_args(exclude_ids, include_params,
                          include_imports) -> bool:
    return (not exclude_ids
            and include_params is _DEFAULT_INCLUDE_PARAMS
            and include_imports is _DEFAULT_INCLUDE_IMPORTS)


def scope_local_bindings(
        scope: ast.AST, *,
        exclude_ids: frozenset[int] = _EMPTY_IDS,
        include_params: bool = _DEFAULT_INCLUDE_PARAMS,
        include_imports: bool = _DEFAULT_INCLUDE_IMPORTS) -> set[str]:
    """返回作用域内局部绑定名（默认参数下按作用域记忆化）。

    原实现对每次调用都完整遍历作用域子树；调用方（如 LV25 可见绑定 owner）
    按节点循环调用时复杂度退化为 O(节点数 × 作用域大小)，单文件可达数秒。
    默认参数下结果只与作用域本身相关，故缓存并返回副本，语义不变。
    """
    if _is_default_scope_args(exclude_ids, include_params, include_imports):
        try:
            cached = _LOCAL_BINDINGS_CACHE.get(scope)
        except TypeError as _e:
            _log.debug('静默降级[scope_local_bindings:TypeError]: %s: %s',
                       type(_e).__name__, _e)
            cached = None
        if cached is not None:
            return set(cached)
        names = _scope_local_bindings_uncached(
            scope, exclude_ids=exclude_ids, include_params=include_params,
            include_imports=include_imports)
        try:
            _LOCAL_BINDINGS_CACHE[scope] = frozenset(names)
            _evict_excess(_LOCAL_BINDINGS_CACHE, _LOCAL_BINDINGS_MAX)
        except TypeError as _e:
            _log.debug('静默降级[scope_local_bindings:TypeError]: %s: %s',
                       type(_e).__name__, _e)
        return set(names)
    return _scope_local_bindings_uncached(
        scope, exclude_ids=exclude_ids, include_params=include_params,
        include_imports=include_imports)


def _scope_local_bindings_uncached(
        scope: ast.AST, *,
        exclude_ids: frozenset[int] = _EMPTY_IDS,
        include_params: bool = _DEFAULT_INCLUDE_PARAMS,
        include_imports: bool = _DEFAULT_INCLUDE_IMPORTS) -> set[str]:
    names: set[str] = set()
    redirected_names: set[str] = set()
    if include_params and isinstance(
            scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        names |= param_names(scope)
    body = getattr(scope, 'body', None)
    stack: list[ast.AST] = list(body) if isinstance(body, list) else (
        [body] if body is not None else [])
    while stack:
        node = stack.pop()
        if (not isinstance(scope, ast.Module)
                and isinstance(node, (ast.Global, ast.Nonlocal))):
            redirected_names.update(node.names)
            continue
        if isinstance(node, FUNC_SCOPE_NODES):
            if (not isinstance(node, ast.Lambda)
                    and id(node) not in exclude_ids):
                names.add(node.name)
            stack.extend(definition_outer_children(node))
            continue
        if isinstance(node, ast.comprehension):
            stack.append(node.iter)
            stack.extend(node.ifs or [])
            continue
        if not include_imports and isinstance(
                node, (ast.Import, ast.ImportFrom)):
            continue
        if isinstance(node, ast.Delete):
            names.update(_del_names(node))
        names |= bound_names_of(node, include_params=False)
        stack.extend(ast.iter_child_nodes(node))
    return names - redirected_names
def _build_parent_map(tree: ast.AST) -> dict[int, ast.AST]:
    parents: dict[int, ast.AST] = {}
    for parent in walk_nodes(tree):
        for child in ast.iter_child_nodes(parent):
            parents[id(child)] = parent
    return parents
_PARENT_MAP_CACHE: WeakKeyDictionary[Any, dict[int, ast.AST]] = WeakKeyDictionary()
def parent_map_of(tree: Any) -> dict[int, ast.AST]:
    return _cached_tree_value(
        _PARENT_MAP_CACHE, tree, _build_parent_map, 'parent_map_of',
        max_size=_PARENT_MAP_CACHE_MAX)
def nearest_scope(parents: dict[int, ast.AST], node: ast.AST) -> ast.AST | None:
    cur = parents.get(id(node))
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef, ast.Lambda, ast.Module)):
            return cur
        cur = parents.get(id(cur))
    return None
def child_scopes(scope: ast.AST) -> list[ast.AST]:
    out: list[ast.AST] = []
    stack = list(ast.iter_child_nodes(scope))
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            out.append(node)
            continue
        stack.extend(ast.iter_child_nodes(node))
    return out
def child_inherited_shadow(scope: ast.AST, visible: frozenset[str],
                            inherited: frozenset[str]) -> frozenset[str]:
    return inherited if isinstance(scope, ast.ClassDef) else visible
def scope_bindings_cached(
        scope: ast.AST, cache: dict[tuple, set[str]],
        exclude_ids: frozenset[int] = _EMPTY_IDS,
        include_imports: bool = _DEFAULT_INCLUDE_IMPORTS) -> set[str]:
    key = ((id(scope), exclude_ids) if include_imports
           else (id(scope), exclude_ids, False))
    if key not in cache:
        cache[key] = scope_local_bindings(
            scope, exclude_ids=exclude_ids, include_imports=include_imports)
    return cache[key]
def _definition_binding_precedes(
        scope: ast.AST, name: str, cutoff: tuple[int, int],
        exclude_ids: frozenset[int]) -> bool:
    stack: list[ast.AST] = list(getattr(scope, 'body', []))
    while stack:
        node = stack.pop()
        if isinstance(node, FUNC_SCOPE_NODES):
            if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef))
                    and node.name == name and id(node) not in exclude_ids
                    and binding_evaluation_position(node) <= cutoff):
                return True
            continue
        stack.extend(_field_children(node))
    return False

def _execution_binding_precedes(
        scope: ast.AST, name: str, node: ast.AST,
        exclude_ids: frozenset[int], include_imports: bool,
) -> bool:
    cutoff = (getattr(node, 'lineno', 0) or 0,
              getattr(node, 'col_offset', 0) or 0)
    body = getattr(scope, 'body', [])
    for bound_node, bound_name, _value in iter_binding_entries(body):
        if bound_name != name:
            continue
        if (not include_imports
                and isinstance(bound_node, (ast.Import, ast.ImportFrom))):
            continue
        if (isinstance(bound_node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.ClassDef))
                and id(bound_node) in exclude_ids):
            continue
        if isinstance(bound_node, (ast.With, ast.AsyncWith)):
            if any(item.optional_vars is not None
                   and name in target_binding_names(item.optional_vars)
                   and _with_item_binding_position(item) <= cutoff
                   for item in bound_node.items):
                return True
            continue
        if binding_evaluation_position(bound_node) <= cutoff:
            return True
    return _definition_binding_precedes(
        scope, name, cutoff, exclude_ids)
def shadowed_binding_at(
        node: ast.AST, name: str, parent: dict[int, ast.AST],
        cache: dict[tuple, set[str]], *,
        include_module: bool = True,
        module_exclude_ids: frozenset[int] = _EMPTY_IDS,
        include_imports: bool = _DEFAULT_INCLUDE_IMPORTS) -> bool:
    cur = parent.get(id(node))
    in_function = False
    deferred_execution = False
    class_checked = False
    while cur is not None:
        if isinstance(cur, COMP_NODES):
            if comprehension_shadows_name(cur, name, node):
                return True
            if id(node) not in _comprehension_outer_node_ids(cur):
                in_function = True
                if isinstance(cur, ast.GeneratorExp):
                    deferred_execution = True
        if (isinstance(cur, FUNC_SCOPE_NODES)
                and id(node) in definition_outer_node_ids(cur)):
            cur = parent.get(id(cur))
            continue
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.Lambda)):
            in_function = True
            deferred_execution = True
            if name in scope_bindings_cached(
                    cur, cache, module_exclude_ids, include_imports):
                return True
        elif isinstance(cur, ast.ClassDef):
            if (not in_function and not class_checked
                    and name in scope_bindings_cached(
                        cur, cache, module_exclude_ids, include_imports)
                    and (deferred_execution or _execution_binding_precedes(
                        cur, name, node, module_exclude_ids, include_imports))):
                return True
            class_checked = True
        elif isinstance(cur, ast.Module):
            if not include_module or name not in scope_bindings_cached(
                    cur, cache, module_exclude_ids, include_imports):
                return False
            return (deferred_execution or _execution_binding_precedes(
                cur, name, node, module_exclude_ids, include_imports))
        cur = parent.get(id(cur))
    return False
def _block_leaves_on(
        stmts: list[ast.stmt], exit_nodes: tuple[type, ...]) -> bool:
    for stmt in stmts:
        if isinstance(stmt, exit_nodes):
            return True
        if (isinstance(stmt, ast.If)
                and _block_leaves_on(stmt.body, exit_nodes)
                and _block_leaves_on(stmt.orelse, exit_nodes)):
            return True
    return False
def block_exits(stmts: list[ast.stmt]) -> bool:
    return _block_leaves_on(
        stmts, (ast.Return, ast.Raise, ast.Break, ast.Continue))
def break_binding_loop(parents: dict[int, ast.AST],
                        brk: ast.Break) -> ast.AST | None:
    child: ast.AST = brk
    anc = parents.get(id(brk))
    while anc is not None:
        if (isinstance(anc, (ast.For, ast.AsyncFor, ast.While))
                and any(s is child for s in getattr(anc, 'body', ()))):
            return anc
        child = anc
        anc = parents.get(id(anc))
    return None
def is_dataclass_decorator(dec: ast.AST) -> bool:
    if isinstance(dec, ast.Name):
        return dec.id == 'dataclass'
    if isinstance(dec, ast.Attribute):
        return dec.attr == 'dataclass'
    if isinstance(dec, ast.Call):
        return is_dataclass_decorator(dec.func)
    return False
def func_name_of_call(call: ast.Call) -> str | None:
    f = call.func
    if isinstance(f, ast.Name):
        return f.id
    if isinstance(f, ast.Attribute):
        return f.attr
    return None
def is_none_constant(node: ast.AST) -> bool:
    return isinstance(node, ast.Constant) and node.value is None
def has_starred_arg(node: ast.Call) -> bool:
    return any(isinstance(a, ast.Starred) for a in node.args)
def bare_single_arg_call(node: ast.AST | None, func_name: str) -> ast.AST | None:
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == func_name and len(node.args) == 1):
        return None
    arg = node.args[0]
    return None if isinstance(arg, ast.Starred) else arg
def range_len_source(node: ast.AST) -> str | None:
    inner = bare_single_arg_call(node, 'range')
    arg = bare_single_arg_call(inner, 'len')
    return arg.id if isinstance(arg, ast.Name) else None
def deref_root_name(node: ast.AST | None) -> str | None:
    cur: ast.AST | None = node
    if isinstance(cur, ast.Call):
        sourced = range_len_source(cur)
        if sourced is not None:
            return sourced
    while isinstance(cur, (ast.Call, ast.Attribute)):
        cur = cur.func if isinstance(cur, ast.Call) else cur.value
    return cur.id if isinstance(cur, ast.Name) else None
def same_expr(a: ast.AST, b: ast.AST) -> bool:
    return ast.dump(a) == ast.dump(b)
def stmt_siblings(owner: ast.AST, child: ast.AST) -> list | None:
    for _field, value in ast.iter_fields(owner):
        if isinstance(value, list) and any(stmt is child for stmt in value):
            return value
    return None
def int_literal(node: ast.AST, *, allow_bool: bool = False) -> int | None:
    sign = 1
    while isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        if isinstance(node.op, ast.USub):
            sign = -sign
        node = node.operand
    if not isinstance(node, ast.Constant):
        return None
    v = node.value
    if not isinstance(v, int) or (isinstance(v, bool) and not allow_bool):
        return None
    return sign * v
def signed_numeric_literal(node: ast.AST) -> int | float | complex | None:
    if not (isinstance(node, ast.UnaryOp)
            and isinstance(node.op, (ast.USub, ast.UAdd))):
        return None
    sign = 1
    while (isinstance(node, ast.UnaryOp)
           and isinstance(node.op, (ast.USub, ast.UAdd))):
        if isinstance(node.op, ast.USub):
            sign = -sign
        node = node.operand
    if not isinstance(node, ast.Constant):
        return None
    value = node.value
    if isinstance(value, bool) or not isinstance(value, (int, float, complex)):
        return None
    return sign * value
COMP_NODES = (ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)
def _comprehension_outer_node_ids(node: ast.AST) -> set[int] | frozenset[int]:
    generators = getattr(node, 'generators', ())
    if not generators:
        return _EMPTY_IDS
    return {id(sub) for sub in walk_nodes(generators[0].iter)}
def _class_namespace_visible(
        node: ast.AST, class_scope: ast.ClassDef,
        parents: dict[int, ast.AST]) -> bool:
    cur = parents.get(id(node))
    while cur is not None and cur is not class_scope:
        if (isinstance(cur, ast.Lambda)
                and id(node) not in definition_outer_node_ids(cur)):
            return False
        if (isinstance(cur, COMP_NODES)
                and id(node) not in _comprehension_outer_node_ids(cur)):
            return False
        cur = parents.get(id(cur))
    return True
def target_store_name_set(targets: Any) -> set[str]:
    return {nm for target in targets
            for nm, _lineno in target_store_names(target, 0)}
def target_binding_names(target: ast.AST) -> frozenset[str]:
    return frozenset(target_store_name_set([target]))
def aligned_unpack_pairs(
        target: ast.AST,
        value: ast.AST) -> list[tuple[ast.AST, ast.AST]] | None:
    if not (isinstance(target, (ast.Tuple, ast.List))
            and isinstance(value, (ast.Tuple, ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(elt, ast.Starred)
                        for elt in (*target.elts, *value.elts))):
        return None
    return list(zip(target.elts, value.elts, strict=True))
def comprehension_elt_nodes(node: ast.AST) -> tuple[ast.AST, ...]:
    if isinstance(node, ast.DictComp):
        return (node.key, node.value)
    return (node.elt,)
def _queue_comprehension_children(
        node: ast.AST, shadow: frozenset[str],
        todo: deque[tuple[ast.AST, frozenset[str]]]) -> None:
    current = shadow
    for gen in node.generators:
        todo.append((gen.iter, current))
        current = current | target_binding_names(gen.target)
        todo.extend((cond, current) for cond in gen.ifs)
    todo.extend((elt, current) for elt in comprehension_elt_nodes(node))
def definition_evaluated_children(node: ast.AST) -> list[ast.AST]:
    children = definition_outer_children(node)
    return [*children, *node.body] if isinstance(node, ast.ClassDef) else children
def walk_scope_expr(body: list[ast.AST],
                    visit: Callable[[ast.AST, frozenset[str]], None]) -> None:
    todo: deque[tuple[ast.AST, frozenset[str]]] = deque(
        [(node, frozenset()) for node in body])
    while todo:
        sub, shadow = todo.popleft()
        if isinstance(sub, NESTED_SCOPES):
            todo.extend((child, shadow)
                        for child in definition_evaluated_children(sub))
            continue
        visit(sub, shadow)
        if isinstance(sub, COMP_NODES):
            _queue_comprehension_children(sub, shadow, todo)
            continue
        todo.extend((child, shadow) for child in ast.iter_child_nodes(sub))
class _VarBindingEvent(NamedTuple):
    pos: tuple[int, int]
    name: str | None
    target: tuple[str, int] | None
    conditional: bool = False
_FLOW_DEFINITE = 0
_FLOW_CONDITIONAL = 1
_FLOW_UNREACHABLE = 2
class FlowVarResolver:
    __slots__ = ('_known_fns', '_model', '_nodes', '_pair_fname', '_preset')
    def __init__(self, nodes: list[ast.AST],
                 known_fns: dict[str, set[tuple[str, ...]]] | set[str],
                 pair_fname: Callable[[ast.AST | None], str | None],
                 preset: dict[str, tuple[str, int]] | None = None) -> None:
        self._nodes = list(nodes)
        self._known_fns = known_fns
        self._pair_fname = pair_fname
        self._preset = dict(preset) if preset else {}
        self._model = _flow_model(self._nodes)
    def _state_at(
            self, cutoff: tuple[int, int] | None,
    ) -> dict[str, tuple[str, int]]:
        roots, children, groups = self._model
        if not roots:
            state = _flow_apply(
                dict(self._preset), self._nodes, self._known_fns,
                self._pair_fname, cutoff)
        else:
            state = _flow_eval_sequence(
                roots, dict(self._preset), children, groups,
                self._known_fns, self._pair_fname, cutoff, True, False)
        return {name: target for name, target in state.items()
                if isinstance(target, tuple)}
    def resolve(self, name: str, lineno: int,
                col_offset: int = 0) -> tuple[str, int] | None:
        return self._state_at((lineno, col_offset)).get(name)
def node_end_position(node: ast.AST) -> tuple[int, int]:
    lineno = getattr(node, 'end_lineno', None) or getattr(
        node, 'lineno', 0) or 0
    col = getattr(node, 'end_col_offset', None)
    if col is None:
        col = getattr(node, 'col_offset', 0) or 0
    return (lineno, col)
def binding_evaluation_position(node: ast.AST) -> tuple[int, int]:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return node_end_position(node.iter)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        vars_ = [item.optional_vars for item in node.items
                 if item.optional_vars is not None]
        if vars_:
            return max(node_end_position(v) for v in vars_)
        return max((node_end_position(item.context_expr)
                    for item in node.items),
                   default=node_end_position(node))
    if isinstance(node, ast.Assign):
        return node_end_position(node.value)
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return node_end_position(node.value)
    if isinstance(node, ast.ExceptHandler):
        return (node_end_position(node.type) if node.type is not None
                else (node.lineno, node.col_offset))
    return node_end_position(node)
def _with_item_binding_position(item: ast.withitem) -> tuple[int, int]:
    return node_end_position(item.context_expr)
def binding_body_start(node: ast.AST) -> tuple[int, int]:
    body = getattr(node, 'body', None)
    if isinstance(body, list) and body:
        first = body[0]
        return (getattr(first, 'lineno', 0) or 0,
                getattr(first, 'col_offset', 0) or 0)
    return node_end_position(node)
def _del_names(target: ast.AST) -> Iterator[str]:
    for sub in walk_nodes(target):
        if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Del):
            yield sub.id
def _make_pair_fname(name_only: bool) -> Callable[[ast.AST | None], str | None]:
    def _pair_fname(value: ast.AST | None) -> str | None:
        if isinstance(value, ast.Await):
            value = value.value
        if not isinstance(value, ast.Call):
            return None
        if name_only:
            return value.func.id if isinstance(value.func, ast.Name) else None
        return func_name_of_call(value)
    return _pair_fname
def _bound_call_target(
        value: ast.AST | None, lineno: int,
        known_fns: dict[str, set[tuple[str, ...]]] | set[str],
        pair_fname: Callable[[ast.AST | None], str | None],
) -> tuple[str, int] | None:
    fname = pair_fname(value)
    return (fname, lineno) if fname in known_fns else None
def _assign_binding_events(
        target: ast.AST, value: ast.AST | None,
        pos: tuple[int, int], lineno: int,
        known_fns: dict[str, set[tuple[str, ...]]] | set[str],
        pair_fname: Callable[[ast.AST | None], str | None],
) -> list[_VarBindingEvent]:
    if isinstance(target, (ast.Tuple, ast.List)):
        pairs = aligned_unpack_pairs(target, value)
        if pairs is None:
            return [_VarBindingEvent(pos, name, None)
                    for name in sorted(target_binding_names(target))]
        return [event
                for sub_target, sub_value in pairs
                for event in _assign_binding_events(
                    sub_target, sub_value, pos, lineno,
                    known_fns, pair_fname)]
    if isinstance(target, ast.Name):
        return [_VarBindingEvent(
            pos, target.id,
            _bound_call_target(value, lineno, known_fns, pair_fname))]
    return [_VarBindingEvent(pos, name, None)
            for name in sorted(target_binding_names(target))]
def _value_binding_events(
        node: ast.AST, pos: tuple[int, int],
        known_fns: dict[str, set[tuple[str, ...]]] | set[str],
        pair_fname: Callable[[ast.AST | None], str | None],
) -> list[_VarBindingEvent] | None:
    if isinstance(node, ast.Assign):
        return [event
                for target in node.targets
                for event in _assign_binding_events(
                    target, node.value, pos, node.lineno,
                    known_fns, pair_fname)]
    if isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
        if (isinstance(node.target, ast.Name)
                and node.value is not None):
            return [_VarBindingEvent(
                pos, node.target.id,
                _bound_call_target(node.value, node.lineno,
                                   known_fns, pair_fname))]
        return []
    if isinstance(node, ast.AugAssign):
        return ([_VarBindingEvent(pos, node.target.id, None)]
                if isinstance(node.target, ast.Name) else [])
    return None
def _binding_event_position(node: ast.AST) -> tuple[int, int]:
    if isinstance(node, ast.match_case):
        return node_end_position(node.pattern)
    return node_end_position(node)
#: ``_binding_events_of`` 的语句列表级缓存。
#:
#: 实测该函数单文件被调 **76,063 次**、只对应 **2,725 个不同的 ``nodes`` 列表**
#: （复用度 27.9×），是 Top-5 检测器（EF01/WM01/LV17）共同的热点。
#:
#: 可缓存性（逐字等价）：当 ``execution`` 为空时，函数体内只剩
#: ``(execution or {}).get(id(node), _FLOW_DEFINITE)`` 恒返回 ``_FLOW_DEFINITE``，
#: 因此结果**只由 (nodes, known_fns, pair_fname) 决定**。身份校验防止 id 复用，
#: ``known_fns`` 另把当前键集合快照入键，避免同一 resolver 解析间原地增删键后
#: 错用旧事件；字典值不参与成员判断，不需要纳入快照。
#:
#: ``execution`` 非空时（子树含 ``ast.NamedExpr``）直接走原路径，不缓存。
#: 返回值只读，调用方不得原地修改。
_BINDING_EVENTS_CACHE: dict[tuple, tuple] = {}
_BINDING_EVENTS_LOCK = threading.Lock()
#: 实测单文件不同 ``nodes`` 列表 2,725 个；上界取 8192 留 3× 余量，
#: 避免「装满即逐出」造成二次重建（4,096 时实测多出 2,440 次重建）。
_BINDING_EVENTS_MAX = 8192


def _binding_events_of(
        nodes: list[ast.AST],
        known_fns: dict[str, set[tuple[str, ...]]] | set[str],
        pair_fname: Callable[[ast.AST | None], str | None],
        execution: dict[int, int] | None = None,
) -> list[_VarBindingEvent]:
    """``_binding_events_of_uncached`` 的缓存包装（``execution`` 为空时生效）。"""
    if execution:
        return _binding_events_of_uncached(
            nodes, known_fns, pair_fname, execution)
    key = (id(nodes), id(known_fns), id(pair_fname), frozenset(known_fns))
    with _BINDING_EVENTS_LOCK:
        hit = _BINDING_EVENTS_CACHE.get(key)
    if (hit is not None and hit[0] is nodes and hit[1] is known_fns
            and hit[2] is pair_fname):
        # 返回副本：缓存值可能被调用方误改（已实测原地 append 会污染），
        # 浅拷贝 O(n) 远小于重算的 O(子树)，仍保留 19× 收益。
        return list(hit[3])
    events = _binding_events_of_uncached(nodes, known_fns, pair_fname, None)
    with _BINDING_EVENTS_LOCK:
        _BINDING_EVENTS_CACHE[key] = (nodes, known_fns, pair_fname, events)
        while len(_BINDING_EVENTS_CACHE) > _BINDING_EVENTS_MAX:
            _BINDING_EVENTS_CACHE.pop(next(iter(_BINDING_EVENTS_CACHE)), None)
    return list(events)


def _binding_events_of_uncached(
        nodes: list[ast.AST],
        known_fns: dict[str, set[tuple[str, ...]]] | set[str],
        pair_fname: Callable[[ast.AST | None], str | None],
        execution: dict[int, int] | None = None,
) -> list[_VarBindingEvent]:
    events: list[_VarBindingEvent] = []
    for node in nodes:
        node_execution = (execution or {}).get(id(node), _FLOW_DEFINITE)
        if node_execution == _FLOW_UNREACHABLE:
            continue
        pos = _binding_event_position(node)
        value_events = _value_binding_events(
            node, pos, known_fns, pair_fname)
        if value_events is not None:
            if node_execution == _FLOW_CONDITIONAL:
                value_events = [event._replace(conditional=True)
                                for event in value_events]
            events.extend(value_events)
            continue
        if isinstance(node, (ast.For, ast.AsyncFor)):
            body_pos = binding_body_start(node)
            events.extend(_VarBindingEvent(body_pos, name, None)
                          for name in sorted(target_binding_names(node.target)))
            continue
        if isinstance(node, (ast.With, ast.AsyncWith)):
            for item in node.items:
                if item.optional_vars is not None:
                    bound_at = _with_item_binding_position(item)
                    events.extend(
                        _VarBindingEvent(bound_at, name, None)
                        for name in sorted(
                            target_binding_names(item.optional_vars)))
            continue
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            names, star_seen = import_bound_names(node)
            if star_seen:
                events.append(_VarBindingEvent(pos, None, None))
            events.extend(_VarBindingEvent(pos, name, None)
                          for name in names)
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            events.append(_VarBindingEvent(pos, node.name, None))
            continue
        if _TYPE_ALIAS_NODE is not None and isinstance(node, _TYPE_ALIAS_NODE):
            alias = getattr(node, 'name', None)
            if isinstance(alias, ast.Name):
                events.append(_VarBindingEvent(pos, alias.id, None))
            continue
        if isinstance(node, ast.Delete):
            events.extend(_VarBindingEvent(pos, name, None)
                          for tgt in node.targets
                          for name in _del_names(tgt))
            continue
        if isinstance(node, ast.ExceptHandler):
            if node.name:
                events.append(_VarBindingEvent(
                    binding_body_start(node), node.name, None))
            continue
        events.extend(_VarBindingEvent(pos, name, None)
                      for name in capture_binding_names(node))
    # 统一按位置排序后返回：调用方（_flow_apply）本就逐次 sorted()，
    # 在这里排一次即可，缓存命中时连排序也省掉。
    events.sort(key=lambda item: item.pos)
    return events
_FLOW_OWNER_NODES = (ast.stmt, ast.ExceptHandler, ast.match_case)
_FLOW_UNBOUND = object()
_FLOW_AMBIGUOUS = object()
def _flow_position(node: ast.AST) -> tuple[int, int]:
    if isinstance(node, ast.match_case):
        node = node.pattern
    return (getattr(node, 'lineno', 0) or 0,
            getattr(node, 'col_offset', 0) or 0)
def _flow_evaluated_children(node: ast.AST) -> list[ast.AST]:
    if isinstance(node, FUNC_SCOPE_NODES):
        return definition_outer_children(node)
    if isinstance(node, ast.GeneratorExp):
        return ([node.generators[0].iter]
                if node.generators else [])
    return list(_field_children(node))
def _flow_origin_dominates(
        origin: tuple[ast.AST, ast.AST] | None,
        cutoff: tuple[int, int] | None,
) -> bool:
    if origin is None or cutoff is None:
        return False
    boundary, branch = origin
    if not (_flow_position(boundary) <= cutoff <= node_end_position(boundary)):
        return False
    if isinstance(boundary, ast.BoolOp):
        return True
    return _flow_position(branch) <= cutoff <= node_end_position(branch)
#: ``_flow_namedexpr_execution`` 的「该节点列表的子树里存在 NamedExpr 吗」缓存。
#:
#: 该函数每被调用一次，都要把 ``nodes`` 的整棵子树递归走一遍；而实测单文件被
#: 调用 **76,063 次**、只对应 **980 个不同的 ``nodes`` 列表**（平均复用 77.6 次），
#: 且被测文件的子树里 **一个 ``NamedExpr`` 都没有**——即这 76,063 次全量遍历
#: 全部消耗在「确认没有海象运算符」上，占整文件检测耗时的 16%。
#:
#: 短路依据（逐字等价）：``visit`` 只在 ``isinstance(node, ast.NamedExpr)`` 分支
#: 写入 ``states``，因此子树内无 ``NamedExpr`` ⇒ ``states`` 必为 ``{}``。
#: 探测遍历用 ``_field_children``，它是 ``visit`` 各分支（BoolOp/IfExp/推导式）
#: 所走子集的**超集**，故「探测不到」一定能推出「``visit`` 也写不出状态」。
#:
#: 键为 ``id(nodes)``，值里持有 ``nodes`` 强引用：只要条目在缓存中，``nodes``
#: 就不会被回收，``id`` 也就不可能被复用——这是本缓存唯一的安全前提。
_NAMEDEXPR_PRESENCE: dict[int, tuple[list, bool]] = {}
_NAMEDEXPR_PRESENCE_LOCK = threading.Lock()
_NAMEDEXPR_PRESENCE_MAX = 2048


def release_scope_fact_caches() -> dict[str, int]:
    """清空本模块全部「按 AST 对象身份作键」的派生缓存。

    这些缓存跨文件永远不可能命中（键是上一文件的 AST 对象），保留只是
    钉住整棵文件 AST，见 ``diag_shared_ast_nodes.release_ast_identity_caches``。
    """
    out: dict[str, int] = {}
    for name, cache, lock in (
            ("binding_index", _BINDING_INDEX_CACHE, _BINDING_INDEX_LOCK),
            ("namedexpr_presence", _NAMEDEXPR_PRESENCE,
             _NAMEDEXPR_PRESENCE_LOCK),
            ("binding_events", _BINDING_EVENTS_CACHE, _BINDING_EVENTS_LOCK)):
        try:
            with lock:
                out[name] = len(cache)
                cache.clear()
        except Exception:
            out[name] = -1
    for name, cache in (("parent_map", _PARENT_MAP_CACHE),
                        ("local_bindings", _LOCAL_BINDINGS_CACHE),
                        ("walk_nodes", _WALK_NODES_CACHE)):
        try:
            out[name] = len(cache)
            cache.clear()
        except Exception:
            out[name] = -1
    return out


def _subtree_has_namedexpr(nodes: list[ast.AST]) -> bool:
    """``nodes`` 的后代里是否存在 ``ast.NamedExpr``（结果按列表身份缓存）。"""
    key = id(nodes)
    with _NAMEDEXPR_PRESENCE_LOCK:
        hit = _NAMEDEXPR_PRESENCE.get(key)
    if hit is not None and hit[0] is nodes:
        return hit[1]
    found = False
    stack = list(nodes)
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.NamedExpr):
            found = True
            break
        stack.extend(_field_children(cur))
    with _NAMEDEXPR_PRESENCE_LOCK:
        _NAMEDEXPR_PRESENCE[key] = (nodes, found)
        while len(_NAMEDEXPR_PRESENCE) > _NAMEDEXPR_PRESENCE_MAX:
            _NAMEDEXPR_PRESENCE.pop(next(iter(_NAMEDEXPR_PRESENCE)), None)
    return found


def _flow_namedexpr_execution(
        nodes: list[ast.AST], cutoff: tuple[int, int] | None = None,
) -> dict[int, int]:
    if not _subtree_has_namedexpr(nodes):
        # 子树内无 NamedExpr ⇒ visit 不可能写入任何状态，直接返回空字典。
        return {}
    states: dict[int, int] = {}
    def visit(node: ast.AST, status: int,
              origin: tuple[ast.AST, ast.AST] | None = None) -> None:
        if isinstance(node, ast.NamedExpr):
            effective = status
            if (status == _FLOW_CONDITIONAL and cutoff is not None
                    and node_end_position(node) <= cutoff
                    and _flow_origin_dominates(origin, cutoff)):
                effective = _FLOW_DEFINITE
            states[id(node)] = max(
                states.get(id(node), _FLOW_DEFINITE), effective)
        if isinstance(node, ast.BoolOp):
            current = status
            current_origin = origin
            for value in node.values:
                visit(value, current, current_origin)
                truth = constant_truth(value)
                stops = ((isinstance(node.op, ast.And) and truth is False)
                         or (isinstance(node.op, ast.Or) and truth is True))
                if stops:
                    current = _FLOW_UNREACHABLE
                    current_origin = (node, value)
                elif truth is None and current != _FLOW_UNREACHABLE:
                    current = max(current, _FLOW_CONDITIONAL)
                    current_origin = (node, value)
            return
        if isinstance(node, ast.IfExp):
            visit(node.test, status, origin)
            truth = constant_truth(node.test)
            body_status = (status if truth is True else
                           _FLOW_UNREACHABLE if truth is False else
                           max(status, _FLOW_CONDITIONAL))
            else_status = (status if truth is False else
                           _FLOW_UNREACHABLE if truth is True else
                           max(status, _FLOW_CONDITIONAL))
            visit(node.body, body_status,
                  (node, node.body) if truth is None else origin)
            visit(node.orelse, else_status,
                  (node, node.orelse) if truth is None else origin)
            return
        if isinstance(node, COMP_NODES):
            conditional = max(status, _FLOW_CONDITIONAL)
            for index, generator in enumerate(node.generators):
                if index == 0:
                    visit(generator.iter, status, origin)
                else:
                    visit(generator.iter, conditional, (node, generator.iter))
                for condition in generator.ifs:
                    visit(condition, conditional, (node, condition))
            for elt in comprehension_elt_nodes(node):
                visit(elt, conditional, (node, elt))
            return
        for child in _field_children(node):
            visit(child, status, origin)
    for root in nodes:
        visit(root, _FLOW_DEFINITE)
    return states
def _flow_deferred_ids(nodes: list[ast.AST]) -> set[int]:
    deferred: set[int] = set()
    visited: dict[int, bool] = {}
    stack = [(node, False) for node in reversed(nodes)]
    while stack:
        node, is_deferred = stack.pop()
        previous = visited.get(id(node))
        if previous is not None and (previous or not is_deferred):
            continue
        visited[id(node)] = is_deferred
        if is_deferred:
            deferred.add(id(node))
        evaluated = (set() if is_deferred else {
            id(child) for child in _flow_evaluated_children(node)})
        for child in _field_children(node):
            stack.append((
                child, is_deferred or id(child) not in evaluated))
    return deferred
def _flow_members(nodes: list[ast.AST]) -> list[ast.AST]:
    deferred = _flow_deferred_ids(nodes)
    members: list[ast.AST] = []
    seen: set[int] = set()
    stack = list(reversed(nodes))
    while stack:
        node = stack.pop()
        if id(node) in seen or id(node) in deferred:
            continue
        seen.add(id(node))
        members.append(node)
        stack.extend(reversed(_flow_evaluated_children(node)))
    return members
def _flow_model(nodes: list[ast.AST]):
    members = _flow_members(nodes)
    parents: dict[int, ast.AST] = {}
    fields: dict[int, str] = {}
    for parent in members:
        for field, value in ast.iter_fields(parent):
            for child in _field_value_nodes(value):
                parents[id(child)] = parent
                fields[id(child)] = field
    def owner_of(node: ast.AST) -> ast.AST | None:
        cur: ast.AST | None = node
        while cur is not None:
            if isinstance(cur, _FLOW_OWNER_NODES):
                return cur
            cur = parents.get(id(cur))
        return None
    groups: dict[int, list[ast.AST]] = {}
    owners: dict[int, ast.AST] = {}
    for node in members:
        owner = owner_of(node)
        if owner is not None:
            owners[id(owner)] = owner
            groups.setdefault(id(owner), []).append(node)
    children: dict[tuple[int, str], list[ast.AST]] = {}
    roots: list[ast.AST] = []
    for owner_id, owner in owners.items():
        cur = parents.get(owner_id)
        parent_owner = owner_of(cur) if cur is not None else None
        if parent_owner is None:
            roots.append(owner)
            continue
        children.setdefault(
            (id(parent_owner), fields[owner_id]), []).append(owner)
    for group in groups.values():
        group.sort(key=_flow_position)
    for group in children.values():
        group.sort(key=_flow_position)
    roots.sort(key=_flow_position)
    return roots, children, groups
def _flow_merge_entry(values: list[Any]) -> Any:
    targets = [value for value in values
               if value is not _FLOW_UNBOUND and value is not _FLOW_AMBIGUOUS]
    if not targets:
        return (_FLOW_AMBIGUOUS if _FLOW_AMBIGUOUS in values
                else _FLOW_UNBOUND)
    if (len({target[0] for target in targets}) == 1
            and _FLOW_AMBIGUOUS not in values
            and all(value is not _FLOW_UNBOUND for value in values)):
        return (targets[0][0], min(target[1] for target in targets))
    return _FLOW_AMBIGUOUS
def _flow_merge(*states: dict[str, Any]) -> dict[str, Any]:
    merged: dict[str, Any] = {}
    names = set().union(*(set(state) for state in states)) if states else set()
    for name in names:
        value = _flow_merge_entry(
            [state.get(name, _FLOW_UNBOUND) for state in states])
        if value is not _FLOW_UNBOUND:
            merged[name] = value
    return merged
def _flow_apply(
        state: dict[str, Any], nodes: list[ast.AST],
        known_fns: dict[str, set[tuple[str, ...]]] | set[str],
        pair_fname: Callable[[ast.AST | None], str | None],
        cutoff: tuple[int, int] | None,
) -> dict[str, Any]:
    result = dict(state)
    events = _binding_events_of(
        nodes, known_fns, pair_fname, _flow_namedexpr_execution(nodes, cutoff))
    for event in events:  # _binding_events_of 已按 pos 排好序
        if cutoff is not None and event.pos > cutoff:
            continue
        if event.name is None:
            result.clear()
        elif event.conditional:
            previous = result.get(event.name, _FLOW_UNBOUND)
            if (event.target is not None and isinstance(previous, tuple)
                    and previous[0] == event.target[0]):
                result[event.name] = (
                    previous[0], min(previous[1], event.target[1]))
            else:
                result[event.name] = _FLOW_AMBIGUOUS
        elif event.target is None:
            result.pop(event.name, None)
        else:
            result[event.name] = event.target
    return result
def _flow_eval_sequence(
        owners: list[ast.AST], state: dict[str, Any],
        children: dict[tuple[int, str], list[ast.AST]],
        groups: dict[int, list[ast.AST]],
        known_fns: dict[str, set[tuple[str, ...]]] | set[str],
        pair_fname: Callable[[ast.AST | None], str | None],
        cutoff: tuple[int, int] | None,
        prune_exits: bool,
        prune_loop_exits: bool,
) -> dict[str, Any]:
    for owner in owners:
        state = _flow_eval_owner(
            owner, state, children, groups, known_fns, pair_fname, cutoff,
            prune_exits, prune_loop_exits)
        if isinstance(owner, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
            break
    return state
def _flow_branch(
        owner: ast.AST, field: str, state: dict[str, Any],
        children: dict[tuple[int, str], list[ast.AST]],
        groups: dict[int, list[ast.AST]],
        known_fns: dict[str, set[tuple[str, ...]]] | set[str],
        pair_fname: Callable[[ast.AST | None], str | None],
        cutoff: tuple[int, int] | None,
        prune_exits: bool,
        prune_loop_exits: bool,
) -> dict[str, Any]:
    return _flow_eval_sequence(
        children.get((id(owner), field), []), dict(state), children,
        groups, known_fns, pair_fname, cutoff, prune_exits,
        prune_loop_exits)
def _flow_entered(
        owner: ast.AST, field: str,
        children: dict[tuple[int, str], list[ast.AST]],
        cutoff: tuple[int, int] | None,
) -> bool:
    if cutoff is None:
        return True
    branch = children.get((id(owner), field))
    start = _flow_position(branch[0]) if branch else node_end_position(owner)
    return cutoff >= start
def _flow_inside(
        owner: ast.AST, field: str,
        children: dict[tuple[int, str], list[ast.AST]],
        cutoff: tuple[int, int] | None,
) -> bool:
    if cutoff is None:
        return False
    branch = children.get((id(owner), field))
    if not branch:
        return False
    return _flow_position(branch[0]) <= cutoff <= node_end_position(branch[-1])
def _flow_block_terminates(
        stmts: list[ast.stmt], prune_loop_exits: bool) -> bool:
    exit_nodes = ((ast.Return, ast.Raise, ast.Break, ast.Continue)
                  if prune_loop_exits else (ast.Return, ast.Raise))
    return _block_leaves_on(stmts, exit_nodes)
def _flow_eval_owner(
        owner: ast.AST, state: dict[str, Any],
        children: dict[tuple[int, str], list[ast.AST]],
        groups: dict[int, list[ast.AST]],
        known_fns: dict[str, set[tuple[str, ...]]] | set[str],
        pair_fname: Callable[[ast.AST | None], str | None],
        cutoff: tuple[int, int] | None,
        prune_exits: bool,
        prune_loop_exits: bool,
) -> dict[str, Any]:
    if cutoff is not None and _flow_position(owner) > cutoff:
        return state
    group = groups.get(id(owner), [owner])
    if isinstance(owner, ast.If):
        base = _flow_apply(state, group, known_fns, pair_fname, cutoff)
        body = _flow_branch(
            owner, 'body', base, children, groups, known_fns,
            pair_fname, cutoff, prune_exits, prune_loop_exits)
        truth = constant_truth(owner.test)
        if truth is True:
            return body
        if truth is False:
            return _flow_branch(
                owner, 'orelse', base, children, groups, known_fns,
                pair_fname, cutoff, prune_exits, prune_loop_exits)
        if not _flow_entered(owner, 'orelse', children, cutoff):
            return body
        other = _flow_branch(
            owner, 'orelse', base, children, groups, known_fns,
            pair_fname, cutoff, prune_exits, prune_loop_exits)
        if _flow_inside(owner, 'orelse', children, cutoff):
            return other
        if prune_exits:
            body_terminates = _flow_block_terminates(
                owner.body, prune_loop_exits)
            other_terminates = (
                bool(owner.orelse) and _flow_block_terminates(
                    owner.orelse, prune_loop_exits))
            if body_terminates != other_terminates:
                return other if body_terminates else body
        return _flow_merge(body, other)
    if isinstance(owner, (ast.For, ast.AsyncFor, ast.While)):
        expression_nodes = [node for node in group if node is not owner]
        base = _flow_apply(
            state, expression_nodes, known_fns, pair_fname, cutoff)
        zero_trip = (
            (isinstance(owner, ast.While)
             and constant_truth(owner.test) is False)
            or (isinstance(owner, (ast.For, ast.AsyncFor))
                and statically_empty_iterable(owner.iter)))
        if zero_trip:
            return _flow_branch(
                owner, 'orelse', base, children, groups, known_fns,
                pair_fname, cutoff, prune_exits, prune_loop_exits)
        if not _flow_entered(owner, 'body', children, cutoff):
            return base
        body_base = _flow_apply(
            base, [owner], known_fns, pair_fname, cutoff)
        body = _flow_branch(
            owner, 'body', body_base, children, groups, known_fns,
            pair_fname, cutoff, prune_exits,
            _flow_inside(owner, 'body', children, cutoff))
        if not _flow_entered(owner, 'orelse', children, cutoff):
            return body
        if (isinstance(owner, ast.While)
                and constant_truth(owner.test) is True):
            return body
        loop_entry = _flow_merge(base, body)
        completed = _flow_branch(
            owner, 'orelse', loop_entry, children, groups,
            known_fns, pair_fname, cutoff, prune_exits, prune_loop_exits)
        if _flow_inside(owner, 'orelse', children, cutoff):
            return completed
        return _flow_merge(body, completed)
    if isinstance(owner, (ast.With, ast.AsyncWith)):
        base = _flow_apply(
            state, group, known_fns, pair_fname, cutoff)
        if not _flow_entered(owner, 'body', children, cutoff):
            return base
        return _flow_branch(
            owner, 'body', base, children, groups, known_fns,
            pair_fname, cutoff, prune_exits, prune_loop_exits)
    if isinstance(owner, TRY_NODES):
        base = _flow_apply(state, group, known_fns, pair_fname, cutoff)
        body = _flow_branch(
            owner, 'body', base, children, groups, known_fns,
            pair_fname, cutoff, prune_exits, prune_loop_exits)
        handlers = children.get((id(owner), 'handlers'), [])
        if handlers and not _flow_entered(handlers[0], 'body', children, cutoff):
            return body
        exception_body = (
            _flow_branch(
                owner, 'body', base, children, groups, known_fns,
                pair_fname, cutoff, False, prune_loop_exits)
            if prune_exits and handlers else body)
        result = body
        if _flow_entered(owner, 'orelse', children, cutoff):
            result = _flow_branch(
                owner, 'orelse', body, children, groups, known_fns,
                pair_fname, cutoff, prune_exits, prune_loop_exits)
            if _flow_inside(owner, 'orelse', children, cutoff):
                return result
        for handler in handlers:
            if not _flow_entered(handler, 'body', children, cutoff):
                continue
            handler_base = _flow_apply(
                _flow_merge(base, exception_body),
                groups.get(id(handler), [handler]),
                known_fns, pair_fname, cutoff)
            handled = _flow_branch(
                handler, 'body', handler_base, children, groups, known_fns,
                pair_fname, cutoff, prune_exits, prune_loop_exits)
            if _flow_inside(handler, 'body', children, cutoff):
                return handled
            if (prune_exits and _flow_block_terminates(
                    handler.body, prune_loop_exits)):
                continue
            if handler.name:
                handled.pop(handler.name, None)
            result = _flow_merge(result, handled)
        if not _flow_entered(owner, 'finalbody', children, cutoff):
            return result
        return _flow_branch(
            owner, 'finalbody', result, children, groups, known_fns,
            pair_fname, cutoff, prune_exits, prune_loop_exits)
    if isinstance(owner, ast.Match):
        base = _flow_apply(state, group, known_fns, pair_fname, cutoff)
        cases = children.get((id(owner), 'cases'), [])
        current = _flow_current_case(cases, children, cutoff)
        if current is not None:
            case_base = _flow_apply(
                base, groups.get(id(current), [current]),
                known_fns, pair_fname, cutoff)
            return _flow_branch(
                current, 'body', case_base, children, groups, known_fns,
                pair_fname, cutoff, prune_exits, prune_loop_exits)
        states = [base]
        for case in cases:
            if constant_truth(getattr(case, 'guard', None)) is False:
                continue
            case_base = _flow_apply(
                base, groups.get(id(case), [case]), known_fns, pair_fname, cutoff)
            case_state = _flow_branch(
                case, 'body', case_base, children, groups, known_fns,
                pair_fname, cutoff, prune_exits, prune_loop_exits)
            if (not prune_exits
                    or not _flow_block_terminates(
                        case.body, prune_loop_exits)):
                states.append(case_state)
            if _match_has_irrefutable_case(case):
                states.pop(0)
                break
        return _flow_merge(*states)
    return _flow_apply(state, group, known_fns, pair_fname, cutoff)
def _flow_current_case(
        cases: list[ast.AST],
        children: dict[tuple[int, str], list[ast.AST]],
        cutoff: tuple[int, int] | None,
) -> ast.AST | None:
    for case in cases:
        if _flow_inside(case, 'body', children, cutoff):
            return case
    return None
def _match_has_irrefutable_case(case: ast.AST) -> bool:
    guard = getattr(case, 'guard', None)
    return (is_irrefutable_pattern(case.pattern)
            and (guard is None or constant_truth(guard) is True))
def flow_var_resolver(
        nodes: list[ast.AST],
        known_fns: dict[str, set[tuple[str, ...]]] | set[str],
        preset: dict[str, tuple[str, int]] | None = None,
        *, name_only: bool = False,
) -> FlowVarResolver:
    pair_fname = _make_pair_fname(name_only)
    return FlowVarResolver(nodes, known_fns, pair_fname, preset)
INPLACE_MUTATOR_METHODS = frozenset({
    'sort', 'reverse', 'append', 'extend', 'insert', 'remove', 'clear',
    'update', 'add', 'discard', 'intersection_update', 'difference_update',
    'symmetric_difference_update',
})
def constant_truth(test: ast.AST | None) -> bool | None:
    return bool(test.value) if isinstance(test, ast.Constant) else None
def statically_empty_iterable(node: ast.AST) -> bool:
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    return (isinstance(node, ast.Constant)
            and isinstance(node.value, (str, bytes)) and not node.value)
def is_statically_unreachable(
        node: ast.AST, parents: dict[int, ast.AST],
        stop: ast.AST) -> bool:
    cur = node
    parent = parents.get(id(cur))
    while parent is not None:
        if _block_never_falls_through_impl(
                preceding_statements(parent, cur), parents,
                _loop_exits=True):
            return True
        if parent is stop:
            break
        if isinstance(parent, ast.If):
            truth = constant_truth(parent.test)
            if ((truth is True and any(cur is stmt for stmt in parent.orelse))
                    or (truth is False
                        and any(cur is stmt for stmt in parent.body))):
                return True
        elif isinstance(parent, ast.While):
            truth = constant_truth(parent.test)
            if ((truth is False and any(cur is stmt for stmt in parent.body))
                    or (truth is True
                        and any(cur is stmt for stmt in parent.orelse))):
                return True
        elif ((isinstance(parent, (ast.For, ast.AsyncFor))
               and statically_empty_iterable(parent.iter)
               and any(cur is stmt for stmt in parent.body))
              or (isinstance(parent, ast.match_case)
                  and constant_truth(parent.guard) is False
                  and any(cur is stmt for stmt in parent.body))):
            return True
        elif isinstance(parent, ast.Match) and isinstance(cur, ast.match_case):
            for case in parent.cases:
                if case is cur:
                    break
                guard_truth = constant_truth(case.guard)
                if (is_irrefutable_pattern(case.pattern)
                        and (case.guard is None or guard_truth is True)):
                    return True
        cur, parent = parent, parents.get(id(parent))
    return False
def try_block_terminates(
        node: ast.AST, terminates: Callable[[list], bool],
        _exceptions_exit: bool = True) -> bool:
    if terminates(node.finalbody):
        return True
    body_terminates = terminates(node.body)
    normal = (body_terminates
              or (bool(node.orelse) and terminates(node.orelse)))
    if (not _exceptions_exit and not body_terminates
            and not any(handler.type is None for handler in node.handlers)):
        # with.__exit__ 可抑制未匹配异常，else/类型化 handler 不能覆盖该路径。
        return False
    return normal and all(terminates(handler.body)
                          for handler in node.handlers)
def match_always_exits(node: ast.Match,
                       terminates: Callable[[list], bool]) -> bool:
    for case in node.cases:
        guard_truth = constant_truth(case.guard)
        if guard_truth is False:
            continue
        if not terminates(case.body):
            return False
        if (is_irrefutable_pattern(case.pattern)
                and (case.guard is None or guard_truth is True)):
            return True
    return False
def assert_always_fails(stmt: ast.AST) -> bool:
    if not isinstance(stmt, ast.Assert):
        return False
    if isinstance(stmt.test, ast.Constant):
        return not stmt.test.value
    return statically_empty_iterable(stmt.test)
def block_never_falls_through(
        stmts: list[ast.stmt],
        parents: dict[int, ast.AST] | None = None,
        _exceptions_exit: bool = True) -> bool:
    return _block_never_falls_through_impl(
        stmts, parents, _exceptions_exit)
def _block_never_falls_through_impl(
        stmts: list[ast.stmt],
        parents: dict[int, ast.AST] | None = None,
        _exceptions_exit: bool = True,
        _loop_exits: bool = False) -> bool:
    for stmt in stmts:
        if (isinstance(stmt, ast.Return)
                or (_loop_exits
                    and isinstance(stmt, (ast.Break, ast.Continue)))
                or (_exceptions_exit and isinstance(stmt, ast.Raise))):
            return True
        if _exceptions_exit and assert_always_fails(stmt):
            return True
        if isinstance(stmt, ast.Match) and match_always_exits(
                stmt, lambda block: _block_never_falls_through_impl(
                    block, parents, _exceptions_exit, _loop_exits)):
            return True
        if isinstance(stmt, ast.If):
            truth = constant_truth(stmt.test)
            if truth is not None:
                branch = stmt.body if truth else stmt.orelse
                if _block_never_falls_through_impl(
                        branch, parents, _exceptions_exit, _loop_exits):
                    return True
            elif (_block_never_falls_through_impl(
                    stmt.body, parents, _exceptions_exit, _loop_exits)
                    and _block_never_falls_through_impl(
                        stmt.orelse, parents, _exceptions_exit, _loop_exits)):
                return True
            continue
        if (isinstance(stmt, (ast.With, ast.AsyncWith))
                and _block_never_falls_through_impl(
                    stmt.body, parents, False, _loop_exits)):
            return True
        if isinstance(stmt, TRY_NODES) and try_block_terminates(
                stmt, lambda block: _block_never_falls_through_impl(
                    block, parents, _exceptions_exit, _loop_exits),
                _exceptions_exit):
            return True
        if parents is None:
            continue
        if (isinstance(stmt, (ast.For, ast.AsyncFor, ast.While))
                and not loop_has_binding(parents, stmt, ast.Break)):
            if is_constant_true_while(stmt):
                return True
            if (stmt.orelse
                    and _block_never_falls_through_impl(
                        stmt.orelse, parents, _exceptions_exit, _loop_exits)):
                return True
    return False
def loop_has_binding(
        parents: dict[int, ast.AST],
        loop: ast.While | ast.For | ast.AsyncFor,
        node_type: type) -> bool:
    if ((isinstance(loop, ast.While)
         and constant_truth(loop.test) is False)
            or (isinstance(loop, (ast.For, ast.AsyncFor))
                and statically_empty_iterable(loop.iter))):
        return False
    return any(
        break_binding_loop(parents, sub) is loop
        for sub in scan_body_no_funcs(loop.body)
        if isinstance(sub, node_type)
        and not is_statically_unreachable(sub, parents, loop))
def is_constant_true_while(stmt: ast.AST) -> bool:
    return (isinstance(stmt, ast.While)
            and isinstance(stmt.test, ast.Constant)
            and bool(stmt.test.value))
def scope_chain(parents: dict[int, ast.AST], node: ast.AST) -> list[ast.AST]:
    chain: list[ast.AST] = []
    cur = nearest_scope(parents, node)
    while cur is not None:
        if (isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.Module))
                or (isinstance(cur, ast.ClassDef) and not chain)):
            chain.append(cur)
        cur = nearest_scope(parents, cur)
    return chain
def scope_function_defs(
        scope: ast.AST) -> list[ast.FunctionDef | ast.AsyncFunctionDef]:
    out: list[ast.FunctionDef | ast.AsyncFunctionDef] = []
    stack: list[ast.AST] = list(reversed(
        list(getattr(scope, 'body', []))))
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            out.append(cur)
            continue
        if isinstance(cur, (ast.ClassDef, ast.Lambda)):
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))
    return out
def preceding_statements(parent: ast.AST, cur: ast.AST) -> list:
    for field in ('body', 'orelse', 'finalbody'):
        seq = getattr(parent, field, None)
        if isinstance(seq, list) and any(stmt is cur for stmt in seq):
            return prior_statements(seq, cur)
    return []
def prior_statements(stmts: list, cur: ast.AST) -> list:
    for idx, stmt in enumerate(stmts):
        if stmt is cur:
            return stmts[:idx]
    return []
def subtree_contains(root: ast.AST | None, target: ast.AST) -> bool:
    return root is not None and any(sub is target for sub in walk_nodes(root))
def construct_shadows_name(scope_node: ast.AST, name: str,
                           name_node: ast.AST | None = None) -> bool:
    if isinstance(scope_node, ast.Lambda):
        if (name_node is not None
                and id(name_node) in definition_outer_node_ids(scope_node)):
            return False
        return name in param_names(scope_node)
    if isinstance(scope_node, (ast.For, ast.AsyncFor)):
        return (name in target_binding_names(scope_node.target)
                and not (name_node is not None
                         and subtree_contains(scope_node.iter, name_node)))
    if isinstance(scope_node, (ast.With, ast.AsyncWith)):
        if name_node is not None:
            for index, item in enumerate(scope_node.items):
                if subtree_contains(item.context_expr, name_node):
                    return any(
                        previous.optional_vars is not None
                        and name in target_binding_names(
                            previous.optional_vars)
                        for previous in scope_node.items[:index]
                    )
        return any(
            item.optional_vars is not None
            and name in target_binding_names(item.optional_vars)
            for item in scope_node.items)
    if isinstance(scope_node, ast.ExceptHandler):
        return (scope_node.name == name
                and not (name_node is not None
                         and subtree_contains(scope_node.type, name_node)))
    if isinstance(scope_node, ast.match_case):
        return (scope_node.pattern is not None
                and name in _pattern_capture_names(scope_node.pattern))
    if isinstance(scope_node, (ast.ListComp, ast.SetComp, ast.DictComp,
                               ast.GeneratorExp)):
        return comprehension_shadows_name(scope_node, name, name_node)
    return False
def comprehension_shadows_name(
        scope_node: ast.ListComp | ast.SetComp | ast.DictComp | ast.GeneratorExp,
        name: str, name_node: ast.AST | None,
) -> bool:
    generators = scope_node.generators
    if name_node is not None:
        for index, generator in enumerate(generators):
            if subtree_contains(generator.iter, name_node):
                return any(
                    name in target_binding_names(previous.target)
                    for previous in generators[:index]
                )
            if any(subtree_contains(condition, name_node)
                   for condition in generator.ifs):
                return any(
                    name in target_binding_names(previous.target)
                    for previous in generators[:index + 1]
                )
    return any(name in target_binding_names(generator.target)
               for generator in generators)

from __future__ import annotations

import ast
import logging
from collections.abc import Iterable, Iterator
from typing import Any, NamedTuple

from jwsgj.prevention_scope_facts import (
    BINDING_FORM_HANDLERS,
    COMP_NODES,
    FUNC_SCOPE_NODES,
    READS_SELF_FORMS,
    TRY_NODES,
    assigned_names,
    binding_body_start,
    block_exits,
    bound_names_of,
    break_binding_loop,
    capture_binding_names,
    comprehension_elt_nodes,
    definition_evaluated_children,
    definition_outer_children,
    import_bound_names,
    is_irrefutable_pattern,
    iter_binding_entries,
    iter_nodes_outside,
    make_issue,
    nearest_scope,
    node_end_position,
    param_names,
    parent_map_of,
    scan_body_no_funcs,
    scope_body_stmts,
    scope_definition_names,
    scope_local_bindings,
    snippet_of,
    source_lines,
    target_binding_names,
    target_store_name_set,
    walk_ast_nodes,
    walk_nodes,
)

__all__ = [
    'check_LV03',
    'check_LV12',
    'check_LV43',
    'check_LV46',
    'check_LV47',
    'check_LV55',
    'check_LV61',
]
_log = logging.getLogger(__name__)
_log.info(
    "prevention_scope_checks 作用域与绑定生命周期规则族已加载：%d 项导出", len(__all__))
_DECL_KIND_NODES = {'global': ast.Global, 'nonlocal': ast.Nonlocal}
_DECL_NODE_TYPES = tuple(_DECL_KIND_NODES.values())
def _declared_names(fn: ast.AST, kind: str) -> set[str]:
    want = _DECL_KIND_NODES.get(kind)
    if want is None:
        return set()
    declared: set[str] = set()
    body = scope_body_stmts(fn)
    if not body:
        return declared
    for node in scan_body_no_funcs(body):
        if isinstance(node, want):
            declared.update(node.names)
    return declared
def _check_inputs(tree: Any, source: Any) -> tuple[bool, list[str]]:
    return (isinstance(tree, ast.AST), source_lines(source))
def _lv12_handler_bind_ranges(
    stmts: list,
) -> dict[str, list[tuple[int, int]]]:
    handler_binds: dict[str, list[tuple[int, int]]] = {}
    for node in scan_body_no_funcs(stmts):
        if isinstance(node, ast.ExceptHandler) and node.name:
            ln = getattr(node, 'lineno', 0) or 0
            end = getattr(node, 'end_lineno', None) or ln
            handler_binds.setdefault(node.name, []).append((ln, end))
    return handler_binds
def _name_reads_self(name: str, value: ast.AST) -> bool:
    return next(
        _load_positions(value, name, frozenset()), None) is not None
def _load_positions_many(
        children: Iterable[ast.AST], name: str, shadow: frozenset[str],
        include_deferred_generators: bool,
) -> Iterator[tuple[int, int]]:
    for child in children:
        yield from _load_positions(
            child, name, shadow,
            include_deferred_generators=include_deferred_generators)
def _load_definition_positions(
        node: ast.AST, name: str, shadow: frozenset[str],
        include_deferred_generators: bool,
) -> Iterator[tuple[int, int]]:
    if isinstance(node, ast.Lambda):
        children = (node.args,)
    elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        children = (*node.decorator_list,
                    *getattr(node, 'type_params', ()), node.args)
        if node.returns is not None:
            children += (node.returns,)
    else:
        children = (*node.body, *node.decorator_list,
                    *getattr(node, 'type_params', ()), *node.bases,
                    *(kw.value for kw in node.keywords))
    yield from _load_positions_many(
        children, name, shadow, include_deferred_generators)
def _load_generator_positions(
        node: ast.GeneratorExp, name: str, shadow: frozenset[str],
        include_deferred_generators: bool,
) -> Iterator[tuple[int, int]]:
    current = shadow
    for index, gen in enumerate(node.generators):
        if index == 0 or include_deferred_generators:
            yield from _load_positions(
                gen.iter, name, current,
                include_deferred_generators=include_deferred_generators)
        current = current | target_binding_names(gen.target)
        if include_deferred_generators:
            yield from _load_positions_many(
                gen.ifs, name, current, include_deferred_generators=True)
    if include_deferred_generators:
        yield from _load_positions_many(
            comprehension_elt_nodes(node), name, current,
            include_deferred_generators=True)
def _load_comprehension_positions(
        node: ast.AST, name: str, shadow: frozenset[str],
        include_deferred_generators: bool,
) -> Iterator[tuple[int, int]]:
    current = shadow
    for gen in node.generators:
        yield from _load_positions(
            gen.iter, name, current,
            include_deferred_generators=include_deferred_generators)
        current = current | target_binding_names(gen.target)
        yield from _load_positions_many(
            gen.ifs, name, current, include_deferred_generators)
    yield from _load_positions_many(
        comprehension_elt_nodes(node), name, current,
        include_deferred_generators)
def _load_positions(
        node: ast.AST, name: str, shadow: frozenset[str],
        *, include_deferred_generators: bool = False,
) -> Iterator[tuple[int, int]]:
    if isinstance(node, ast.Name):
        if (node.id == name and isinstance(node.ctx, ast.Load)
                and name not in shadow):
            yield (node.lineno, node.col_offset)
        return
    if isinstance(node, (ast.Lambda, ast.FunctionDef,
                         ast.AsyncFunctionDef, ast.ClassDef)):
        yield from _load_definition_positions(
            node, name, shadow, include_deferred_generators)
        return
    if isinstance(node, ast.GeneratorExp):
        yield from _load_generator_positions(
            node, name, shadow, include_deferred_generators)
        return
    if isinstance(node, COMP_NODES):
        yield from _load_comprehension_positions(
            node, name, shadow, include_deferred_generators)
        return
    yield from _load_positions_many(
        ast.iter_child_nodes(node), name, shadow,
        include_deferred_generators)
def _lv12_in_handler_range(
        name: str, node: ast.AST,
        handler_binds: dict[str, list[tuple[int, int]]],
) -> bool:
    if isinstance(node, ast.ExceptHandler) and node.name == name:
        return False
    lineno = getattr(node, 'lineno', 0) or 0
    return any(start <= lineno <= end
               for start, end in handler_binds.get(name, ()))
def _lv12_record_binding(
    name: str, node: ast.AST, reads_self: bool,
    candidates: dict[str, tuple[int, bool]],
    windows: dict[str, tuple[int, int]],
    handler_binds: dict[str, list[tuple[int, int]]],
) -> None:
    lineno = getattr(node, 'lineno', 0) or 0
    if _lv12_in_handler_range(name, node, handler_binds):
        return
    if name not in candidates or lineno < candidates[name][0]:
        candidates[name] = (lineno, reads_self)
    if isinstance(node, ast.ExceptHandler):
        return
    effective = _lv12_binding_position(node)
    previous = windows.get(name)
    if previous is None or effective < previous:
        windows[name] = effective
def _lv12_first_bindings(
    stmts: list,
) -> tuple[dict[str, tuple[int, bool]], dict[str, tuple[int, int]],
           dict[str, list[tuple[int, int]]]]:
    candidates: dict[str, tuple[int, bool]] = {}
    windows: dict[str, tuple[int, int]] = {}
    handler_binds = _lv12_handler_bind_ranges(stmts)
    for node, name, value in iter_binding_entries(stmts):
        reads_self = (type(node) in READS_SELF_FORMS
                      or (value is not None
                          and _name_reads_self(name, value)))
        _lv12_record_binding(
            name, node, reads_self, candidates, windows, handler_binds)
    for node in _lv12_own_statements(stmts):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            _lv12_record_binding(
                node.name, node, False, candidates, windows, handler_binds)
            continue
        if (isinstance(node, ast.AnnAssign) and node.value is None
                and isinstance(node.target, ast.Name)):
            name = node.target.id
            lineno = getattr(node, 'lineno', 0) or 0
            if name not in candidates or lineno < candidates[name][0]:
                candidates[name] = (lineno, False)
    return candidates, windows, handler_binds
def _lv12_own_statements(stmts: list) -> Iterator[ast.stmt]:
    stack: list[ast.AST] = list(stmts)
    while stack:
        node = stack.pop()
        if isinstance(node, ast.stmt):
            yield node
        if isinstance(node, FUNC_SCOPE_NODES):
            continue
        stack.extend(ast.iter_child_nodes(node))
def _lv12_binding_position(node: ast.AST) -> tuple[int, int]:
    if isinstance(node, (ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
                         ast.ExceptHandler)):
        return binding_body_start(node)
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return node_end_position(node)
    return node_end_position(node)
def _delete_hits(sn: ast.AST, name: str) -> bool:
    if not isinstance(sn, ast.Delete):
        return False
    return any(
        isinstance(n, ast.Name) and n.id == name
        and isinstance(n.ctx, ast.Del)
        for target in sn.targets for n in walk_nodes(target))
def _lv12_persistent_binding_nodes(
        body: list, name: str, handler_ranges: list[tuple[int, int]],
) -> list[tuple[tuple[int, int], ast.AST]]:
    bindings: list[tuple[tuple[int, int], ast.AST]] = []
    for node, bound, _value in iter_binding_entries(body):
        if bound != name or isinstance(node, ast.Delete):
            continue
        bindings.append((_lv12_binding_position(node), node))
    for node in _lv12_own_statements(body):
        if not (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef)) and node.name == name):
            continue
        bindings.append((_lv12_binding_position(node), node))
    return bindings
def _lv12_control_path(
        node: ast.AST, parents: dict[int, ast.AST],
) -> dict[int, str]:
    path: dict[int, str] = {}
    current = node
    while current is not None:
        parent = parents.get(id(current))
        if parent is None:
            break
        branch: str | None = None
        if isinstance(parent, (ast.If, ast.For, ast.AsyncFor, ast.While)):
            if current in parent.body:
                branch = 'body'
            elif current in parent.orelse:
                branch = 'else'
        elif (isinstance(parent, ast.Match)
              and isinstance(current, ast.match_case)):
            branch = str(id(current))
        elif isinstance(parent, TRY_NODES):
            if current in parent.body or current in parent.orelse:
                branch = 'body'
            elif current in parent.handlers:
                branch = f'handler:{id(current)}'
            elif current in parent.finalbody:
                # finally 在 try 体未正常完成（绑定前抛出）时同样执行，
                # 读取点不能与 try 体内的条件绑定视为同一路径。
                branch = 'finally'
        if branch is not None:
            path[id(parent)] = branch
        current = parent
    return path
def _direct_child_under(
        anc: ast.AST, node: ast.AST,
        parents: dict[int, ast.AST]) -> ast.AST | None:
    cur: ast.AST | None = node
    while cur is not None:
        parent = parents.get(id(cur))
        if parent is anc:
            return cur
        cur = parent
    return None


def _lv12_conditional_origins(
        binding: ast.AST, read: ast.AST,
        parents: dict[int, ast.AST],
) -> frozenset[tuple[int, str]]:
    """返回绑定相对读取点所跨越的可选执行区域。"""
    origins: set[tuple[int, str]] = set()
    if isinstance(binding, (ast.For, ast.AsyncFor, ast.While)):
        read_child = _direct_child_under(binding, read, parents)
        if read_child not in binding.body:
            origins.add((id(binding), 'body'))
    current: ast.AST | None = binding
    while current is not None:
        ancestor = parents.get(id(current))
        if ancestor is None:
            break
        binding_child = _direct_child_under(ancestor, binding, parents)
        read_child = _direct_child_under(ancestor, read, parents)
        if isinstance(ancestor, ast.If):
            for label, branch in (('body', ancestor.body),
                                  ('else', ancestor.orelse)):
                if binding_child in branch and read_child not in branch:
                    origins.add((id(ancestor), label))
        elif isinstance(ancestor, (ast.For, ast.AsyncFor, ast.While)):
            for label, branch in (('body', ancestor.body),
                                  ('else', ancestor.orelse)):
                in_branch = (binding is ancestor and label == 'body'
                             or binding_child in branch)
                if in_branch and read_child not in branch:
                    origins.add((id(ancestor), label))
        elif isinstance(ancestor, ast.Match):
            if (isinstance(binding_child, ast.match_case)
                    and read_child is not binding_child):
                sole_irrefutable = (
                    len(ancestor.cases) == 1
                    and binding_child.guard is None
                    and is_irrefutable_pattern(binding_child.pattern))
                if not sole_irrefutable:
                    origins.add((id(ancestor), str(id(binding_child))))
        elif isinstance(ancestor, TRY_NODES):
            in_normal_path = (binding_child in ancestor.body
                              or binding_child in ancestor.orelse)
            read_in_normal_path = (
                read_child in ancestor.body or read_child in ancestor.orelse)
            handlers_fall_through = any(
                not block_exits(handler.body) for handler in ancestor.handlers)
            read_in_finally = read_child in ancestor.finalbody
            if (in_normal_path and not read_in_normal_path
                    and (handlers_fall_through or read_in_finally)):
                origins.add((id(ancestor), 'body'))
            if (binding_child in ancestor.handlers
                    and read_child is not binding_child):
                origins.add((
                    id(ancestor), f'handler:{id(binding_child)}'))
        current = ancestor
    return frozenset(origins)


_BODY_MODULE_CACHE: dict[int, tuple[list, ast.Module]] = {}
_BODY_MODULE_CACHE_MAX = 512
_BODY_READ_NODES_CACHE: dict[int, tuple[list, dict]] = {}
_BODY_READ_NODES_CACHE_MAX = 256
def _body_read_nodes(body: list) -> dict[tuple[int, int], ast.AST]:
    """收集 body 内全部 ``Name`` 读取节点的位置索引。

    结果与具体名字无关，但原实现放在 ``_lv12_first_unbound_read`` 里，
    于是每个待查名字都要把整段 body 重新走一遍并重建一份字典——单个
    作用域有 M 个名字时就退化为 O(M x 节点数)。这里按 body 列表身份
    缓存，同一段 body 只构建一次。
    """
    key = id(body)
    hit = _BODY_READ_NODES_CACHE.get(key)
    if hit is not None and hit[0] is body:
        return hit[1]
    nodes = {
        (node.lineno, node.col_offset): node
        for stmt in body for node in walk_nodes(stmt)
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
    }
    if len(_BODY_READ_NODES_CACHE) >= _BODY_READ_NODES_CACHE_MAX:
        _BODY_READ_NODES_CACHE.pop(next(iter(_BODY_READ_NODES_CACHE)))
    _BODY_READ_NODES_CACHE[key] = (body, nodes)
    return nodes
def _body_module(body: list) -> ast.Module:
    """按 body 列表身份复用包装用的 ``ast.Module``。

    原实现每次调用都新建 ``ast.Module(body=body)`` 再取父映射，于是
    ``parent_map_of`` 的按对象缓存永远命中不了——每个作用域都要重建一次
    O(节点数) 的父映射，整体退化为 O(作用域 x 深度)。这里让同一条 body
    列表始终对应同一个 Module 对象，命中率与 body 的生命周期一致。
    Module 只作为遍历根，不参与任何语义判断，行为与原实现等价。
    """
    key = id(body)
    hit = _BODY_MODULE_CACHE.get(key)
    if hit is not None and hit[0] is body:
        return hit[1]
    module = ast.Module(body=body, type_ignores=[])
    if len(_BODY_MODULE_CACHE) >= _BODY_MODULE_CACHE_MAX:
        _BODY_MODULE_CACHE.pop(next(iter(_BODY_MODULE_CACHE)))
    _BODY_MODULE_CACHE[key] = (body, module)
    return module
class _LV12Event(NamedTuple):
    position: tuple[int, int]
    origins: frozenset[tuple[int, str]]
    deleted: bool

def _lv12_branch_options(node: ast.AST) -> tuple[str, ...]:
    if isinstance(node, (ast.If, ast.For, ast.AsyncFor, ast.While)):
        return 'body', 'else'
    if isinstance(node, ast.Match):
        cases = tuple(str(id(case)) for case in node.cases)
        exhaustive = any(
            case.guard is None and is_irrefutable_pattern(case.pattern)
            for case in node.cases)
        return cases if exhaustive else (*cases, 'missing')
    if isinstance(node, TRY_NODES):
        return ('body', *(
            f'handler:{id(handler)}' for handler in node.handlers))
    return ()

def _lv12_origins_compatible(
        left: frozenset[tuple[int, str]],
        right: frozenset[tuple[int, str]],
) -> bool:
    left_by_id = dict(left)
    return all(
        control_id not in left_by_id or left_by_id[control_id] == branch
        for control_id, branch in right)

def _lv12_conditions_cover(
        events: list[_LV12Event], assumed: frozenset[tuple[int, str]],
        nodes_by_id: dict[int, ast.AST],
) -> bool:
    memo: dict[frozenset[tuple[int, str]], bool] = {}
    def visit(current: frozenset[tuple[int, str]]) -> bool:
        cached = memo.get(current)
        if cached is not None:
            return cached
        compatible = [
            event for event in events
            if _lv12_origins_compatible(event.origins, current)
        ]
        if any(event.origins <= current for event in compatible):
            memo[current] = True
            return True
        remaining = {
            control_id for event in compatible
            for control_id, _branch in event.origins - current
        }
        if not remaining:
            memo[current] = False
            return False
        control_id = min(remaining)
        options = _lv12_branch_options(nodes_by_id.get(control_id))
        covered = bool(options) and all(
            visit(frozenset((*current, (control_id, branch))))
            for branch in options)
        memo[current] = covered
        return covered
    return visit(assumed)

def _lv12_unbound_mode(
        events: list[_LV12Event], nodes_by_id: dict[int, ast.AST],
) -> str | None:
    events.sort(key=lambda event: event.position)
    surviving: list[_LV12Event] = []
    for index, event in enumerate(events):
        later = [candidate for candidate in events[index + 1:]
                 if candidate.position > event.position]
        if not _lv12_conditions_cover(later, event.origins, nodes_by_id):
            surviving.append(event)
    if any(event.deleted and event.position[0] >= 0 for event in surviving):
        return 'deleted'
    if any(event.deleted for event in surviving):
        return 'before'
    return None

def _lv12_handler_delete_reaches_read(
        handler: ast.ExceptHandler, read: ast.AST,
        parents: dict[int, ast.AST],
) -> bool:
    if not block_exits(handler.body):
        return True
    parent = parents.get(id(handler))
    return (isinstance(parent, TRY_NODES)
            and _direct_child_under(parent, read, parents) in parent.finalbody)

def _lv12_first_unbound_read(
        body: list, name: str, window: tuple[int, int] | None,
        handler_ranges: list[tuple[int, int]],
) -> tuple[tuple[int, int], str] | None:
    bindings = _lv12_persistent_binding_nodes(body, name, handler_ranges)
    delete_nodes = [
        node for node, bound, _value in iter_binding_entries(body)
        if bound == name and isinstance(node, ast.Delete)
    ]
    handlers = [
        node for node in scan_body_no_funcs(body)
        if isinstance(node, ast.ExceptHandler) and node.name == name
    ]
    parents = parent_map_of(_body_module(body))
    nodes_by_id = {id(node): node for node in parents.values()}
    read_nodes = _body_read_nodes(body)
    first: tuple[tuple[int, int], str] | None = None
    for stmt in body:
        for pos in _load_positions(stmt, name, frozenset()):
            read_node = read_nodes[pos]
            read_path = _lv12_control_path(read_node, parents)
            prior = [
                (position, node, False)
                for position, node in bindings if position < pos
            ]
            prior.extend(
                (node_end_position(node), node, True)
                for node in delete_nodes
                if node_end_position(node) < pos)
            prior.extend(
                (node_end_position(handler), handler, True)
                for handler in handlers
                if node_end_position(handler) < pos
                and _lv12_handler_delete_reaches_read(
                    handler, read_node, parents))
            events = [_LV12Event((-1, -1), frozenset(), True)]
            for position, node, deleted in prior:
                origins = _lv12_conditional_origins(node, read_node, parents)
                if any(read_path.get(control_id, branch) != branch
                       for control_id, branch in origins):
                    continue
                events.append(_LV12Event(position, origins, deleted))
            mode = _lv12_unbound_mode(events, nodes_by_id)
            if mode is not None and (first is None or pos < first[0]):
                first = (pos, mode)
    return first
def _lv12_lexical_scopes(
        inner: ast.AST, parents: dict[int, ast.AST],
) -> Iterator[ast.AST]:
    current = parents.get(id(inner))
    while current is not None:
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Module)):
            yield current
        current = parents.get(id(current))
def _lv12_outer_face(
        outer: ast.AST) -> tuple[set, str, str, str, set[str]]:
    locals_ = (set(assigned_names(outer.body))
               | scope_definition_names(outer.body))
    global_names = _declared_names(outer, 'global')
    if isinstance(outer, ast.Module):
        return (locals_, 'global', '函数', '模块级变量', global_names)
    return (locals_ | param_names(outer),
            'nonlocal', '嵌套函数', '外层函数的局部变量', global_names)
def _lv12_nested_hits(
        inner: ast.AST, outer_locals: set,
) -> dict[str, tuple[int, str]]:
    first_writes, windows, handler_binds = _lv12_first_bindings(inner.body)
    if not first_writes:
        return {}
    excluded = (_declared_names(inner, 'nonlocal')
                | _declared_names(inner, 'global') | param_names(inner))
    hits: dict[str, tuple[int, str]] = {}
    for name, (lineno, reads_self) in first_writes.items():
        if name not in outer_locals or name in excluded:
            continue
        if reads_self:
            hits[name] = (lineno, 'self')
            continue
        ranges = handler_binds.get(name, ())
        unbound = _lv12_first_unbound_read(
            inner.body, name, windows.get(name), ranges)
        if unbound is not None:
            (read_line, _read_col), read_mode = unbound
            released = any(end < read_line for _start, end in ranges)
            mode = ('deleted' if read_mode == 'deleted'
                    else 'released' if released else read_mode)
            hits[name] = (read_line, mode)
    return hits
def _lv12_issue(filepath: Any, src_lines: list[str], inner_name: str,
                name: str, lineno: int, face: tuple,
                mode: str) -> dict[str, Any]:
    decl, inner_desc, var_desc = face
    if mode == 'before':
        title = (f'{inner_desc} {inner_name}() 在有效绑定前读取{var_desc} '
                 f'{name} 但缺 {decl}：调用即 UnboundLocalError')
        description = (
            f'{var_desc} ``{name}``，{inner_desc} '
            f'``{inner_name}()`` 体内的读取点位于首次绑定之前，或仅有'
            f'不保证执行的条件分支/循环/异常路径绑定，且无 {decl} 声明'
            f'——后续绑定使 ``{name}`` 成为{inner_desc}的局部名，'
            f'读取发生时本层尚无有效绑定，{inner_desc}的可达路径即 '
            'UnboundLocalError。'
        )
    elif mode == 'released':
        title = (f'{inner_desc} {inner_name}() 在 except 处理器退出后'
                 f'读取{var_desc} {name} 但缺 {decl}：'
                 '处理器退出即解绑，调用即 UnboundLocalError')
        description = (
            f'{var_desc} ``{name}`` 仅由 ``except ... as {name}`` '
            f'绑定——CPython 在处理器退出时隐式 ``del {name}`` 回收'
            f'异常对象，所以处理器之后的读取点仍然没有值，且无 {decl} '
            f'声明（该名字已成为{inner_desc}的局部名），'
            f'{inner_desc}被调用即 UnboundLocalError。'
        )
    elif mode == 'deleted':
        title = (f'{inner_desc} {inner_name}() 在 del 后读取{var_desc} '
                 f'{name} 但缺 {decl}：调用即 UnboundLocalError')
        description = (
            f'{var_desc} ``{name}`` 在{inner_desc} ``{inner_name}()`` 内'
            f'先被 ``del {name}`` 解绑，后续读取前没有新的有效绑定，且无 '
            f'{decl} 声明——读取发生时本层名字无值，'
            f'{inner_desc}被调用即 UnboundLocalError。'
        )
    else:
        title = (f'{inner_desc} {inner_name}() 先读后写{var_desc} '
                 f'{name} 但缺 {decl}：调用即 UnboundLocalError')
        description = (
            f'{var_desc} ``{name}``，{inner_desc} '
            f'``{inner_name}()`` 体内首次写即先读后写'
            f'（``{name} += 1`` / ``{name} = {name} + 1`` /'
            f' ``{name}: T = {name} + 1`` /'
            f' ``({name} := {name} + 1)`` 形态，'
            f'无 {decl} 声明）——该赋值语句使 ``{name}`` '
            f'成为{inner_desc}的局部名，右侧读取点在本层无'
            f'绑定，{inner_desc}被调用即 UnboundLocalError。'
        )
    return make_issue(
        'LV-12', 'P1', 'logic_correctness', filepath, lineno,
        title,
        description,
        snippet_of(src_lines, lineno),
        (
            f'根因：闭包「读取」外层变量合法，但「赋值」'
            f'会在函数内创建新的局部绑定，除非声明 '
            f'{decl}——读取点先于本层绑定，必崩。\n'
            f'修复策略：函数体内声明 '
            f'``{decl} {name}`` 后再赋值；或把可变容器'
            f'（list/dict）作为载体，函数内改容器内容'
            f'（读取成员不需要声明）。\n'
            '参考标准：作用域断裂缺陷模式'
            '（LEGB 绑定规则）'
        ),
        f'missing-{decl}',
    )
def check_LV12(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    valid, src_lines = _check_inputs(tree, source)
    if not valid:
        return issues
    parents = parent_map_of(tree)
    seen_hits: set[tuple[int, str]] = set()
    for inner in walk_nodes(tree):
        if not isinstance(inner, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for outer in _lv12_lexical_scopes(inner, parents):
            outer_locals, decl, inner_desc, var_desc, global_names = (
                _lv12_outer_face(outer))
            if not outer_locals:
                continue
            hits = _lv12_nested_hits(inner, outer_locals)
            for name in sorted(hits):
                key = (id(inner), name)
                if key in seen_hits:
                    continue
                seen_hits.add(key)
                lineno, mode = hits[name]
                face = (('global', inner_desc, '模块级变量')
                        if name in global_names or isinstance(outer, ast.Module)
                        else (decl, inner_desc, var_desc))
                issues.append(_lv12_issue(
                    filepath, src_lines, inner.name, name, lineno,
                    face, mode=mode))
    return issues
def _lv43_literal_dict_key(key: ast.AST | None) -> bool:
    if isinstance(key, ast.Constant):
        return True
    return (isinstance(key, ast.Tuple)
            and all(_lv43_literal_dict_key(elt) for elt in key.elts))
def _lv43_is_unpack_unsafe_dict_binding(value: ast.AST) -> bool:
    if not isinstance(value, ast.Dict):
        return False
    keys = value.keys
    if not keys:
        return False
    return all(_lv43_literal_dict_key(key) for key in keys)
def _lv43_store_hits(root: ast.AST, name: str) -> bool:
    return any(isinstance(n, ast.Name) and n.id == name
               and isinstance(n.ctx, ast.Store) for n in walk_nodes(root))
def _lv43_dict_anchor(sn: ast.stmt, target: ast.AST,
                      value: ast.AST) -> ast.stmt | None:
    if not isinstance(target, ast.Name):
        return None
    if not _lv43_is_unpack_unsafe_dict_binding(value):
        return None
    return sn
def _lv43_assign_face(
    sn: ast.AST, name: str,
) -> tuple[ast.stmt | None, bool]:
    if isinstance(sn, ast.Assign):
        if not any(_lv43_store_hits(t, name) for t in sn.targets):
            return None, False
        direct_target = next(
            (target for target in sn.targets
             if isinstance(target, ast.Name) and target.id == name), None)
        if direct_target is not None:
            anchor = _lv43_dict_anchor(sn, direct_target, sn.value)
            if anchor is not None:
                return anchor, False
        return None, True
    if (isinstance(sn, ast.AnnAssign) and sn.value is not None
            and isinstance(sn.target, ast.Name) and sn.target.id == name):
        anchor = _lv43_dict_anchor(sn, sn.target, sn.value)
        return (anchor, False) if anchor is not None else (None, True)
    return None, False
def _lv43_other_bind_face(sn: ast.AST, name: str) -> bool:
    if _delete_hits(sn, name):
        return True
    if import_bound_names(sn)[1]:
        return True
    handler = BINDING_FORM_HANDLERS.get(type(sn))
    if handler is None:
        return False
    return any(bound == name for bound, _value in handler(sn))
def _lv43_scope_binding_face(
        body: list, name: str, limit: tuple[int, int],
        conditional_lines: set[int] | frozenset[int],
) -> tuple[ast.stmt | None, bool]:
    entries: list[tuple[tuple[int, int], ast.stmt | None, bool]] = []
    for sn in scan_body_no_funcs(body):
        pos = (getattr(sn, 'lineno', 0) or 0,
               getattr(sn, 'col_offset', 0) or 0)
        if pos >= limit:
            continue
        if isinstance(sn, (ast.Assign, ast.AnnAssign)):
            face, other = _lv43_assign_face(sn, name)
        else:
            face, other = None, _lv43_other_bind_face(sn, name)
        entries.append((pos, face, other))
    entries.sort(key=lambda item: item[0])
    dict_bind: ast.stmt | None = None
    other_bind = False
    for pos, face, other in entries:
        if face is not None:
            if pos[0] not in conditional_lines:
                dict_bind = face
                other_bind = False
            elif not other_bind:
                dict_bind = face
        if other:
            other_bind = True
    return dict_bind, other_bind
def _lv43_is_kv_unpack_dict_iter(node: ast.For) -> bool:
    target = node.target
    if not (isinstance(target, (ast.Tuple, ast.List)) and len(target.elts) >= 2):
        return False
    if any(isinstance(e, ast.Starred) for e in target.elts):
        return False
    if not all(isinstance(e, ast.Name) for e in target.elts):
        return False
    if isinstance(node.iter, ast.Name):
        return True
    return _lv43_is_unpack_unsafe_dict_binding(node.iter)
def _lv43_key_outcome(key: ast.AST | None, arity: int) -> str:
    if isinstance(key, ast.Tuple):
        length = len(key.elts)
        if length == arity:
            return 'tuple'
        return f'short:{length}' if length < arity else 'long'
    if not isinstance(key, ast.Constant):
        return 'value'
    value = key.value
    if isinstance(value, (str, bytes)):
        if len(value) == arity:
            return 'char' if isinstance(value, str) else 'byte'
        return f'short:{len(value)}' if len(value) < arity else 'long'
    return 'type'
def _lv43_unpack_targets(node: ast.For) -> str:
    return ', '.join(
        elt.id for elt in node.target.elts if isinstance(elt, ast.Name))
def _lv43_issue_title(outcome: str, arity: int) -> str:
    if outcome == 'tuple':
        return (f'for 键值解包直接迭代 dict：键为 {arity} 元 tuple，'
                '按元素静默拆包（无异常、值全错）')
    if outcome == 'char':
        return (f'for 键值解包直接迭代 dict：键为 {arity} 字符 str，'
                '按字符静默拆包（无异常、值全错）')
    if outcome == 'byte':
        return (f'for 键值解包直接迭代 dict：键为 {arity} 字节 bytes，'
                '按字节拆成 int 静默拆包（无异常、值全错）')
    if outcome == 'type':
        return 'for 键值解包直接迭代 dict：键不可迭代，解包即 TypeError（漏 .items()）'
    return (f'for 键值解包直接迭代 dict：迭代产出键，{arity} 元解包必 '
            'ValueError（漏 .items()）')
def _lv43_issue_detail(
        target: str, iter_name: str, outcome: str, arity: int) -> str:
    head = (f'``for {target} in {iter_name}:`` 形态——直接迭代 dict 只'
            '产出键（单个键对象），')
    if outcome == 'tuple':
        return (head + f'字面量首个键是长度恰为 {arity} 的 tuple，解包'
                '**不报错**而是把键的元素逐个拆给目标名：无异常、无告警，'
                '静默丢弃对应的字典值；意图键值成对遍历须 ``.items()``。')
    if outcome == 'char':
        return (head + f'字面量首个键是长度恰为 {arity} 的 str，解包'
                '**不报错**而是把键按字符逐个拆给目标名，各名字拿到'
                '单个字符：无异常、无告警，静默产出错误数据；意图键值成对'
                '遍历须 ``.items()``。')
    if outcome == 'byte':
        return (head + f'字面量首个键是长度恰为 {arity} 的 bytes，解包'
                '**不报错**而是把键按字节拆给目标名，各名字拿到该字节的'
                'int 码值：无异常、无告警，静默产出错误数据；意图键值成对'
                '遍历须 ``.items()``。')
    if outcome == 'type':
        return (head + '字面量首个键是解包无法消费的标量常量（int/float/'
                'bool/None 不可迭代），首个键上即抛 ``TypeError: cannot '
                'unpack non-iterable ... object``；意图键值成对遍历须 '
                '``.items()``。')
    if outcome.startswith('short:'):
        got = outcome.split(':', 1)[1]
        return (head + f'字面量首个键的序列长度小于 {arity}，解包在首个键上'
                f'即抛 ``ValueError: not enough values to unpack '
                f'(expected {arity}, got {got})``；意图键值成对遍历须 ``.items()``。')
    if outcome == 'long':
        return (head + f'字面量首个键的序列长度大于 {arity}，解包在首个键上'
                f'即抛 ``ValueError: too many values to unpack '
                f'(expected {arity})``；意图键值成对遍历须 ``.items()``。')
    return (head + '字面量首个键无法按目标元数解包，迭代即抛 '
            '``ValueError``；意图键值成对遍历须 ``.items()``。')
def _lv43_issue(node: ast.For, iter_name: str, filepath: Any,
                src_lines: list[str], outcome: str) -> dict[str, Any]:
    arity = len(node.target.elts)
    target = _lv43_unpack_targets(node)
    return make_issue(
        'LV-43', 'P1', 'logic_correctness', filepath, node.lineno,
        _lv43_issue_title(outcome, arity),
        _lv43_issue_detail(target, iter_name, outcome, arity),
        snippet_of(src_lines, node.lineno),
        (
            '根因：dict 迭代协议默认 yield 键，与 zip/enumerate\n'
            '「逐元素解包」直觉错位，漏写 ``.items()``。\n'
            '修复策略：``for k, v in d.items():`` 成对遍历；仅需\n'
            '键用 ``for k in d:``；仅需值用 ``d.values()``。\n'
            '参考标准：CPython dict 迭代协议（for 产出键；\n'
            'items()/keys()/values() 三视图）'
        ),
        'for-unpack-iterates-dict-keys',
    )
def _lv43_visible_dict_binding(
        node: ast.AST, name: str, parents: dict[int, ast.AST],
) -> ast.stmt | None:
    scope = nearest_scope(parents, node)
    first = scope
    limit = (node.lineno, node.col_offset)
    while scope is not None:
        if scope is first or not isinstance(scope, ast.ClassDef):
            body = scope_body_stmts(scope)
            if body:
                binding_limits = [limit]
                if scope is not first:
                    inner_name = getattr(first, 'name', '')
                    call_positions = [
                        (call.lineno, call.col_offset)
                        for call in scan_body_no_funcs(body)
                        if (isinstance(call, ast.Call)
                            and isinstance(call.func, ast.Name)
                            and call.func.id == inner_name)]
                    if call_positions:
                        binding_limits = sorted(call_positions)
                conditional_lines = _lv61_conditional_lines(
                    _lv61_own_nodes(scope))
                for call_limit in binding_limits:
                    dict_bind, other_bind = _lv43_scope_binding_face(
                        body, name, call_limit, conditional_lines)
                    if dict_bind is not None and not other_bind:
                        return dict_bind
            if name in scope_local_bindings(scope):
                return None
        scope = nearest_scope(parents, scope)
    return None
def _lv43_hit(
    node: ast.AST, parents: dict[int, ast.AST], filepath: Any,
    src_lines: list[str],
) -> dict[str, Any] | None:
    if not (isinstance(node, ast.For) and _lv43_is_kv_unpack_dict_iter(node)):
        return None
    if isinstance(node.iter, ast.Dict):
        arity = len(node.target.elts)
        outcome = _lv43_key_outcome(node.iter.keys[0], arity)
        if outcome == 'tuple' and all(
                _lv43_key_outcome(key, arity) == 'tuple'
                for key in node.iter.keys):
            return None
        return _lv43_issue(
            node, ast.unparse(node.iter), filepath, src_lines, outcome)
    iter_name = node.iter.id
    dict_bind = _lv43_visible_dict_binding(node, iter_name, parents)
    if dict_bind is None:
        return None
    value = getattr(dict_bind, 'value', None)
    first_key = (value.keys[0]
                 if isinstance(value, ast.Dict) and value.keys else None)
    arity = len(node.target.elts)
    outcome = _lv43_key_outcome(first_key, arity)
    if outcome == 'tuple' and isinstance(value, ast.Dict) and all(
            _lv43_key_outcome(key, arity) == 'tuple' for key in value.keys):
        return None
    return _lv43_issue(node, iter_name, filepath, src_lines, outcome)
def check_LV43(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    valid, src_lines = _check_inputs(tree, source)
    if not valid:
        return issues
    parents = parent_map_of(tree)
    for node in walk_nodes(tree):
        hit = _lv43_hit(node, parents, filepath, src_lines)
        if hit is not None:
            issues.append(hit)
    return issues
_LV61_CALLABLE_BUILTINS: frozenset[str] = frozenset({
    'list', 'dict', 'set', 'tuple', 'frozenset', 'str', 'bytes',
    'bytearray', 'int', 'float', 'complex', 'bool', 'len', 'sum',
    'min', 'max', 'abs', 'round', 'divmod', 'pow', 'sorted',
    'reversed', 'any', 'all', 'id', 'type', 'input', 'open', 'print',
    'map', 'filter', 'zip', 'range', 'next', 'iter', 'enumerate',
    'repr', 'ord', 'chr', 'format', 'isinstance', 'issubclass',
    'getattr', 'setattr', 'hasattr', 'vars', 'dir', 'callable',
    'hash', 'hex', 'oct', 'bin',
})
_LV61_NONCALLABLE_VALUES = (
    ast.Constant, ast.JoinedStr, ast.List, ast.Tuple, ast.Set, ast.Dict,
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
def _lv61_is_noncallable_value(node: ast.AST) -> bool:
    if isinstance(node, _LV61_NONCALLABLE_VALUES):
        return True
    if isinstance(node, ast.UnaryOp):
        if isinstance(node.op, ast.Not):
            return True
        if not isinstance(node.operand, ast.Constant):
            return False
        value = node.operand.value
        if not isinstance(value, (int, float, complex)):
            return False
        if isinstance(node.op, (ast.UAdd, ast.USub)):
            return True
        return isinstance(node.op, ast.Invert) and isinstance(value, int)
    if isinstance(node, ast.IfExp):
        return (_lv61_is_noncallable_value(node.body)
                and _lv61_is_noncallable_value(node.orelse))
    return False
_LV61_TYPE_LABEL = {
    'list': 'list', 'dict': 'dict', 'set': 'set', 'tuple': 'tuple',
    'frozenset': 'frozenset', 'str': 'str', 'bytes': 'bytes',
    'bytearray': 'bytearray', 'int': 'int', 'float': 'float',
    'complex': 'complex', 'bool': 'bool',
}
def _lv61_own_nodes(scope: ast.AST) -> list[ast.AST]:
    if isinstance(scope, COMP_NODES):
        stack: list[ast.AST] = [
            *(gen.iter for gen in scope.generators[1:]),
            *(cond for gen in scope.generators for cond in gen.ifs),
            *comprehension_elt_nodes(scope),
        ]
    else:
        stack = list(scope_body_stmts(scope))
    out: list[ast.AST] = []
    while stack:
        cur = stack.pop()
        if isinstance(cur, FUNC_SCOPE_NODES):
            out.append(cur)
            stack.extend(definition_outer_children(cur))
            continue
        if isinstance(cur, COMP_NODES):
            if cur.generators:
                stack.append(cur.generators[0].iter)
            continue
        out.append(cur)
        stack.extend(ast.iter_child_nodes(cur))
    return out
def _lv61_assign_faces(
        ch: ast.AST,
) -> list[tuple[str, bool | None, int]]:
    if isinstance(ch, ast.Assign):
        is_literal = _lv61_is_noncallable_value(ch.value)
        value_name = ch.value.id if isinstance(ch.value, ast.Name) else None
        return [
            (target.id,
             None if target.id == value_name else is_literal,
             id(target))
            for target in ch.targets
            if (isinstance(target, ast.Name)
                and target.id in _LV61_CALLABLE_BUILTINS)
        ]
    if (isinstance(ch, ast.AnnAssign) and ch.value is not None
            and isinstance(ch.target, ast.Name)
            and ch.target.id in _LV61_CALLABLE_BUILTINS):
        value_name = ch.value.id if isinstance(ch.value, ast.Name) else None
        return [(ch.target.id,
                 None if ch.target.id == value_name
                 else _lv61_is_noncallable_value(ch.value),
                 id(ch.target))]
    if (isinstance(ch, ast.NamedExpr)
            and ch.target.id in _LV61_CALLABLE_BUILTINS):
        value_name = ch.value.id if isinstance(ch.value, ast.Name) else None
        return [(ch.target.id,
                 None if ch.target.id == value_name
                 else _lv61_is_noncallable_value(ch.value),
                 id(ch.target))]
    if (isinstance(ch, ast.AugAssign)
            and isinstance(ch.target, ast.Name)
            and ch.target.id in _LV61_CALLABLE_BUILTINS):
        is_literal = _lv61_is_noncallable_value(ch.value)
        return [(ch.target.id, None if is_literal else False, id(ch.target))]
    return []
def _lv61_module_import_face(ch: ast.AST) -> set[str]:
    if not isinstance(ch, ast.Import):
        return set()
    names = {
        alias.asname or alias.name.split('.')[0]
        for alias in ch.names
    }
    return names & _LV61_CALLABLE_BUILTINS
def _lv61_import_face(ch: ast.AST) -> tuple[set[str], bool]:
    if not isinstance(ch, ast.ImportFrom):
        return set(), False
    bound, star_import_seen = import_bound_names(ch)
    return set(bound) & _LV61_CALLABLE_BUILTINS, star_import_seen
def _lv61_pattern_face(ch: ast.AST) -> set[str]:
    return capture_binding_names(ch) & _LV61_CALLABLE_BUILTINS
def _lv61_definition_face(ch: ast.AST) -> set[str]:
    if isinstance(ch, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {ch.name} & _LV61_CALLABLE_BUILTINS
    return set()
def _lv61_handler_face(ch: ast.AST) -> set[str]:
    if isinstance(ch, ast.ExceptHandler) and ch.name:
        return {ch.name} & _LV61_CALLABLE_BUILTINS
    return set()
def _lv61_del_builtin_names(ch: ast.AST) -> set[str]:
    if not isinstance(ch, ast.Delete):
        return set()
    return {
        sub.id for tgt in ch.targets for sub in walk_nodes(tgt)
        if (isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Del)
            and sub.id in _LV61_CALLABLE_BUILTINS)
    }
_LV61Positions = dict[str, list[tuple[int, int]]]
_LV61LiteralValues = dict[str, list[tuple[tuple[int, int], ast.AST]]]
def _lv61_augassign_preserves_value(value: ast.AST, op: ast.operator) -> bool:
    if isinstance(value, ast.IfExp):
        return (_lv61_augassign_preserves_value(value.body, op)
                and _lv61_augassign_preserves_value(value.orelse, op))
    if isinstance(value, (ast.List, ast.ListComp,
                          ast.Tuple, ast.JoinedStr)):
        return isinstance(op, ast.Add)
    if isinstance(value, ast.Constant):
        return (isinstance(value.value, (str, bytes))
                and isinstance(op, ast.Add))
    if isinstance(value, (ast.Dict, ast.DictComp)):
        return isinstance(op, ast.BitOr)
    if isinstance(value, (ast.Set, ast.SetComp)):
        return isinstance(op, (ast.BitOr, ast.BitAnd,
                               ast.BitXor, ast.Sub))
    return False
def _lv61_stable_augassign(
        node: ast.AST, literal_positions: _LV61Positions,
        literal_values: _LV61LiteralValues,
        uncertain: _LV61Positions, deleted: _LV61Positions,
) -> bool:
    if not isinstance(node, ast.AugAssign):
        return False
    name = node.target.id
    position = (node.lineno, node.col_offset)
    literal = max((pos for pos in literal_positions.get(name, ())
                   if pos < position), default=None)
    values = [(pos, value) for pos, value in literal_values.get(name, ())
              if pos < position]
    if literal is None or not values:
        return False
    value_position, value = max(values, key=lambda item: item[0])
    if value_position != literal:
        return False
    if any(literal < pos < position
           for events in (uncertain, deleted)
           for pos in events.get(name, ())):
        return False
    return _lv61_augassign_preserves_value(value, node.op)
def _lv61_binding_position(node: ast.AST) -> tuple[int, int]:
    if (isinstance(node, (ast.Assign, ast.AnnAssign))
            and node.value is not None):
        return node_end_position(node.value)
    if isinstance(node, (ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
                         ast.ExceptHandler)):
        return binding_body_start(node)
    return node_end_position(node)
def _lv61_record_position(
        events: _LV61Positions, name: str, node: ast.AST,
        position: tuple[int, int] | None = None) -> None:
    events.setdefault(name, []).append(
        _lv61_binding_position(node) if position is None else position)
def _lv61_pass1_faces(
    own: list[ast.AST],
    conditional_lines: set[int] | frozenset[int],
) -> tuple[_LV61Positions, _LV61Positions, _LV61Positions, set[int]]:
    literal_positions: _LV61Positions = {}
    uncertain: _LV61Positions = {}
    deleted: _LV61Positions = {}
    literal_values: _LV61LiteralValues = {}
    known_target_node_ids: set[int] = set()
    ordered = sorted(own, key=lambda node: (
        getattr(node, 'lineno', 0) or 0,
        getattr(node, 'col_offset', 0) or 0))
    for ch in ordered:
        faces = _lv61_assign_faces(ch)
        if faces:
            stable_augassign = _lv61_stable_augassign(
                ch, literal_positions, literal_values, uncertain, deleted)
            for name, is_literal, tgt_id in faces:
                known_target_node_ids.add(tgt_id)
                if is_literal is None or stable_augassign:
                    continue
                events = literal_positions if is_literal else uncertain
                _lv61_record_position(events, name, ch)
                if (is_literal and isinstance(
                        ch, (ast.Assign, ast.AnnAssign, ast.NamedExpr))):
                    literal_values.setdefault(name, []).append(
                        (events[name][-1], ch.value))
            continue
        if deleted_names := _lv61_del_builtin_names(ch):
            deleted_positions = (
                uncertain if getattr(ch, 'lineno', 0) in conditional_lines
                else deleted)
            for name in deleted_names:
                _lv61_record_position(deleted_positions, name, ch)
            continue
        module_imports = _lv61_module_import_face(ch)
        if module_imports:
            for name in module_imports:
                _lv61_record_position(literal_positions, name, ch)
            continue
        import_uncertain, star = _lv61_import_face(ch)
        for name in (import_uncertain | _lv61_pattern_face(ch)
                     | _lv61_definition_face(ch) | _lv61_handler_face(ch)):
            _lv61_record_position(uncertain, name, ch)
        if star:
            for name in literal_positions:
                _lv61_record_position(uncertain, name, ch)
    return literal_positions, uncertain, deleted, known_target_node_ids
def _lv61_store_binding_position(
        node: ast.AST, parents: dict[int, ast.AST],
) -> tuple[int, int] | None:
    cur: ast.AST | None = node
    while cur is not None:
        if isinstance(cur, ast.comprehension):
            return node_end_position(cur.iter)
        if isinstance(cur, ast.AnnAssign) and cur.value is None:
            return None
        if type(cur) in BINDING_FORM_HANDLERS:
            return _lv61_binding_position(cur)
        cur = parents.get(id(cur))
    return node_end_position(node)
def _lv61_store_scan_uncertain(
    own: list[ast.AST], known_target_node_ids: set[int],
    uncertain: _LV61Positions,
) -> None:
    parents = {
        id(child): cur for cur in own
        for child in ast.iter_child_nodes(cur)
    }
    for ch in own:
        if (isinstance(ch, ast.Name) and isinstance(ch.ctx, ast.Store)
                and ch.id in _LV61_CALLABLE_BUILTINS
                and id(ch) not in known_target_node_ids):
            position = _lv61_store_binding_position(ch, parents)
            if position is not None:
                _lv61_record_position(uncertain, ch.id, ch, position)
def _lv61_binding_faces(
    own: list[ast.AST],
    conditional_lines: set[int] | frozenset[int],
) -> tuple[_LV61Positions, _LV61Positions, _LV61Positions]:
    literal_positions, uncertain, deleted, known_target_node_ids = (
        _lv61_pass1_faces(own, conditional_lines))
    _lv61_store_scan_uncertain(own, known_target_node_ids, uncertain)
    return literal_positions, uncertain, deleted

_LV61_ENTRY_STATE = 'entry'
_LV61_RESET_STATES = frozenset({'uncertain', 'deleted'})


def _lv61_statement_event_kind(
        stmt: ast.stmt, name: str, literal_positions: _LV61Positions,
        uncertain: _LV61Positions, deleted: _LV61Positions,
) -> str | None:
    if isinstance(stmt, (ast.For, ast.AsyncFor, ast.AugAssign)):
        return None
    if not (type(stmt) in BINDING_FORM_HANDLERS
            or isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef))):
        return None
    position = _lv61_binding_position(stmt)
    for kind, events in (('literal', literal_positions),
                         ('uncertain', uncertain), ('deleted', deleted)):
        if position in events.get(name, ()):
            return kind
    return None


def _lv61_nested_event_kinds(
        stmt: ast.stmt, name: str, literal_positions: _LV61Positions,
        uncertain: _LV61Positions, deleted: _LV61Positions,
) -> set[str]:
    start = (getattr(stmt, 'lineno', 0) or 0,
             getattr(stmt, 'col_offset', 0) or 0)
    end = node_end_position(stmt)
    kinds: set[str] = set()
    for kind, events in (('literal', literal_positions),
                         ('uncertain', uncertain), ('deleted', deleted)):
        if any(start <= pos <= end for pos in events.get(name, ())):
            kinds.add(kind)
    return kinds


def _lv61_block_terminal_states(
        block: list[ast.stmt], name: str,
        literal_positions: _LV61Positions, uncertain: _LV61Positions,
        deleted: _LV61Positions,
) -> set[str]:
    states = {_LV61_ENTRY_STATE}
    for stmt in block:
        direct = _lv61_statement_event_kind(
            stmt, name, literal_positions, uncertain, deleted)
        if direct is not None:
            states = {direct}
            continue
        if isinstance(stmt, ast.If):
            outcomes: set[str] = set()
            for branch in (stmt.body, stmt.orelse):
                branch_states = _lv61_block_terminal_states(
                    branch, name, literal_positions, uncertain, deleted)
                outcomes.update(branch_states - {_LV61_ENTRY_STATE})
                if _LV61_ENTRY_STATE in branch_states:
                    outcomes.update(states)
            states = outcomes
            continue
        nested = _lv61_nested_event_kinds(
            stmt, name, literal_positions, uncertain, deleted)
        if nested:
            states.update(nested)
    return states


def _lv61_guaranteed_resets(
        own: list[ast.AST], literal_positions: _LV61Positions,
        uncertain: _LV61Positions, deleted: _LV61Positions,
        conditional_lines: set[int] | frozenset[int],
) -> _LV61Positions:
    guaranteed: _LV61Positions = {}
    names = set(uncertain) | set(deleted)
    for ch in own:
        if (not isinstance(ch, ast.If) or not ch.orelse
                or ch.lineno in conditional_lines):
            continue
        start = (ch.lineno, ch.col_offset)
        end = node_end_position(ch)
        candidates = {
            name for name in names
            if any(start <= pos <= end
                   for events in (uncertain, deleted)
                   for pos in events.get(name, ()))
        }
        for name in candidates:
            body_states = _lv61_block_terminal_states(
                ch.body, name, literal_positions, uncertain, deleted)
            else_states = _lv61_block_terminal_states(
                ch.orelse, name, literal_positions, uncertain, deleted)
            if (body_states <= _LV61_RESET_STATES
                    and else_states <= _LV61_RESET_STATES):
                guaranteed.setdefault(name, []).append(node_end_position(ch))
    return guaranteed

_MATCH_CASE_TYPE = getattr(ast, "match_case", None)
_LV61_INHERITED_SHADOW = (0, 0)
_LV61_PARAMETER_DEFAULT = (0, 1)
_LV61_CONDITIONAL_INHERITED_SHADOW = (0, 2)
def _lv61_try_body_unconditional(ch: ast.AST) -> bool:
    handlers = getattr(ch, "handlers", ()) or ()
    return not handlers or all(
        block_exits(h.body) for h in handlers)
def _lv61_conditional_bodies(ch: ast.AST) -> list[ast.stmt]:
    if isinstance(ch, (ast.If, ast.For, ast.AsyncFor, ast.While)):
        return ch.body + ch.orelse
    if isinstance(ch, ast.ExceptHandler) or (
            _MATCH_CASE_TYPE is not None
            and isinstance(ch, _MATCH_CASE_TYPE)):
        return ch.body
    if isinstance(ch, TRY_NODES):
        if not _lv61_try_body_unconditional(ch):
            return list(ch.body) + list(ch.orelse)
        return []
    return []
def _lv61_body_lines(body: list[ast.stmt]) -> set[int]:
    lines: set[int] = set()
    for sub in body:
        for x in walk_nodes(sub):
            ln = getattr(x, 'lineno', None)
            if ln is not None:
                lines.add(ln)
    return lines
def _lv61_conditional_lines(own: list[ast.AST]) -> set[int]:
    conditional_lines: set[int] = set()
    for ch in own:
        conditional_lines |= _lv61_body_lines(_lv61_conditional_bodies(ch))
    return conditional_lines
def _lv61_latest_prior(
        events: _LV61Positions, name: str,
        position: tuple[int, int]) -> tuple[int, int] | None:
    return max((pos for pos in events.get(name, ()) if pos < position),
               default=None)
def _lv61_tracked_call(
    ch: ast.AST, literal_positions: _LV61Positions,
    uncertain: _LV61Positions, deleted: _LV61Positions,
    conditional_lines: set[int] | frozenset[int],
    guaranteed_resets: _LV61Positions | None = None,
) -> tuple[str, tuple[int, int] | None, bool] | None:
    if not isinstance(ch, ast.Call) or not isinstance(ch.func, ast.Name):
        return None
    fname = ch.func.id
    if fname not in literal_positions:
        return None
    position = (ch.lineno, ch.col_offset)
    literal = _lv61_latest_prior(literal_positions, fname, position)
    if literal is None:
        return None
    resets = [
        pos for events in (uncertain, deleted)
        for pos in events.get(fname, ()) if pos < position
    ]
    reset_candidates = [
        pos for pos in resets if pos[0] not in conditional_lines]
    if guaranteed_resets is not None:
        reset_candidates.extend(
            pos for pos in guaranteed_resets.get(fname, ()) if pos < position)
    reset = max(reset_candidates, default=None)
    if reset is not None and reset > literal:
        return None
    conditional_reset = any(
        pos > literal and pos[0] in conditional_lines for pos in resets)
    return fname, reset, conditional_reset
class _LV61ScopeFacts(NamedTuple):
    own: list[ast.AST]
    local_bindings: set[str]
    global_declared: set[str]
    nonlocal_declared: set[str]
    conditional_lines: set[int]
    literal_positions: _LV61Positions
    uncertain: _LV61Positions
    deleted: _LV61Positions
    guaranteed_resets: _LV61Positions
    persistent: _LV61Positions
_LV61_LEXICAL_SCOPES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.Module,
    *COMP_NODES,
)
def _lv61_parameter_default_positions(scope: ast.AST) -> _LV61Positions:
    if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
        return {}
    args = scope.args
    positional = [*args.posonlyargs, *args.args]
    defaulted = list(zip(
        positional[len(positional) - len(args.defaults):], args.defaults))
    defaulted.extend(
        (arg, default) for arg, default in zip(
            args.kwonlyargs, args.kw_defaults) if default is not None)
    positions: _LV61Positions = {}
    for arg, default in defaulted:
        if (arg.arg in _LV61_CALLABLE_BUILTINS
                and _lv61_is_noncallable_value(default)):
            positions[arg.arg] = [_LV61_PARAMETER_DEFAULT]
    return positions
def _lv61_build_scope_facts(scope: ast.AST) -> _LV61ScopeFacts:
    own = _lv61_own_nodes(scope)
    conditional_lines = _lv61_conditional_lines(own)
    literal_positions, uncertain, deleted = _lv61_binding_faces(
        own, conditional_lines)
    for name, positions in _lv61_parameter_default_positions(scope).items():
        literal_positions.setdefault(name, []).extend(positions)
    if isinstance(scope, COMP_NODES):
        local_bindings = target_store_name_set(
            [gen.target for gen in scope.generators])
    else:
        local_bindings = scope_local_bindings(scope)
    guaranteed_resets = _lv61_guaranteed_resets(
        own, literal_positions, uncertain, deleted, conditional_lines)
    persistent = _lv61_persistent_literal_shadows(
        literal_positions, uncertain, deleted, conditional_lines,
        guaranteed_resets)
    return _LV61ScopeFacts(
        own, local_bindings, _declared_names(scope, 'global'),
        _declared_names(scope, 'nonlocal'), conditional_lines,
        literal_positions, uncertain, deleted, guaranteed_resets, persistent,
    )
def _lv61_inherited_shadows(
        scope: ast.AST, parents: dict[int, ast.AST],
        facts_by_id: dict[int, _LV61ScopeFacts],
) -> _LV61Positions:
    inherited: _LV61Positions = {}
    blocked: set[str] = set()
    requested_globals = facts_by_id[id(scope)].global_declared
    current = parents.get(id(scope))
    while current is not None:
        if isinstance(current, _LV61_LEXICAL_SCOPES):
            outer = facts_by_id.get(id(current))
            if outer is not None:
                declarations = (set() if isinstance(current, ast.Module)
                                else outer.global_declared
                                | outer.nonlocal_declared)
                candidates = outer.local_bindings - declarations
                for name in candidates - blocked:
                    if (not isinstance(current, ast.Module)
                            and name in requested_globals):
                        continue
                    if name in outer.persistent:
                        inherited.setdefault(
                            name, list(outer.persistent[name]))
                    blocked.add(name)
            if isinstance(current, ast.Module):
                break
        current = parents.get(id(current))
    return inherited
def _lv61_call_events(
    own: list[ast.AST], literal_positions: _LV61Positions,
    uncertain: _LV61Positions, deleted: _LV61Positions,
    conditional_lines: set[int],
    guaranteed_resets: _LV61Positions | None = None,
) -> list[tuple[ast.Call, str, bool, str]]:
    events: list[tuple[ast.Call, str, bool, str]] = []
    for ch in own:
        match = _lv61_tracked_call(
            ch, literal_positions, uncertain, deleted, conditional_lines,
            guaranteed_resets)
        if match is None:
            continue
        fname, reset, conditional_reset = match
        call_position = (ch.lineno, ch.col_offset)
        prior = [pos for pos in literal_positions[fname]
                 if pos < call_position and (reset is None or pos > reset)]
        if not prior:
            continue
        latest = max(prior)
        hard = (latest not in {
                    _LV61_CONDITIONAL_INHERITED_SHADOW,
                    _LV61_PARAMETER_DEFAULT,
                }
                and latest[0] not in conditional_lines
                and not conditional_reset)
        scoped = [pos[0] for pos in prior if pos[0] > 0]
        if scoped:
            where = f'L{max(scoped)}'
        elif _LV61_PARAMETER_DEFAULT in prior:
            where = '参数默认值'
        else:
            where = '外层作用域'
        events.append((ch, fname, hard, where))
    return events
def _lv61_issue(filepath: Any, src_lines: list[str], ch: ast.Call,
                fname: str, hard: bool, where: str) -> dict[str, Any]:
    severity = 'P1' if hard else 'P2'
    certainty = ('赋值为线性路径，调用必 TypeError' if hard else
                 '条件路径仍保留不可调用绑定，走该路径即 TypeError')
    label = _LV61_TYPE_LABEL.get(fname, f'{fname}/object')
    return make_issue(
        'LV-61', severity, 'logic_correctness', filepath, ch.lineno,
        f'内建名 ``{fname}`` 被遮蔽后调用：{certainty}',
        (
            f'作用域内 ``{fname} = ...``（{where}）把内建 '
            f'``{fname}`` 遮蔽为不可调用对象；L{ch.lineno} 的 '
            f'``{fname}(...)`` 按内建语义发起调用即 '
            f'``TypeError: \'{label}\' object is not callable``。'
        ),
        snippet_of(src_lines, ch.lineno),
        (
            f'根因：变量命名撞内建名（``{fname}`` 为高频撞名\n'
            '之一）——赋值与调用共享同一名字空间，后读到的\n'
            '是遮蔽值而非内建。\n'
            '修复策略：变量改名用语义名（``items``/``values``/\n'
            f'``{fname}_list`` 等）；确需同语义调用时经\n'
            '``import builtins`` 显式取回内建\n'
            f'（``builtins.{fname}(...)``）。\n'
            '参考标准：LEGB 名字解析序——局部绑定优先于\n'
            'builtins，遮蔽即生效'
        ),
        'shadow-builtin-then-call',
    )
def _lv61_persistent_literal_shadows(
        literal_positions: _LV61Positions, uncertain: _LV61Positions,
        deleted: _LV61Positions,
        conditional_lines: set[int] | frozenset[int],
        guaranteed_resets: _LV61Positions | None = None,
) -> _LV61Positions:
    shadows: _LV61Positions = {}
    for name, positions in literal_positions.items():
        resets = [
            *uncertain.get(name, ()), *deleted.get(name, ())]
        unconditional_resets = [
            pos for pos in resets if pos[0] not in conditional_lines]
        if guaranteed_resets is not None:
            unconditional_resets.extend(guaranteed_resets.get(name, ()))
        last_reset = max(unconditional_resets, default=None)
        relevant = [
            pos for pos in positions if last_reset is None or pos > last_reset]
        if not relevant:
            continue
        unconditional = [
            pos for pos in relevant if pos[0] not in conditional_lines]
        conditional = bool(unconditional) and any(
            pos > max(unconditional) and pos[0] in conditional_lines
            for pos in resets)
        parameter_only = (
            bool(unconditional)
            and all(pos == _LV61_PARAMETER_DEFAULT for pos in unconditional))
        shadows[name] = [(
            _LV61_PARAMETER_DEFAULT if parameter_only else
            _LV61_CONDITIONAL_INHERITED_SHADOW
            if conditional or not unconditional else _LV61_INHERITED_SHADOW)]
    return shadows
def check_LV61(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    valid, src_lines = _check_inputs(tree, source)
    if not valid:
        return issues
    scope_types = (ast.Module, *FUNC_SCOPE_NODES, *COMP_NODES)
    scopes = [node for node in walk_nodes(tree)
              if isinstance(node, scope_types)]
    facts_by_id = {id(scope): _lv61_build_scope_facts(scope)
                   for scope in scopes}
    parents = parent_map_of(tree)
    for scope in scopes:
        facts = facts_by_id[id(scope)]
        literal_positions = {
            name: list(positions)
            for name, positions in facts.literal_positions.items()
        }
        inherited = _lv61_inherited_shadows(scope, parents, facts_by_id)
        if not isinstance(scope, ast.ClassDef):
            declarations = facts.global_declared | facts.nonlocal_declared
            local_barrier = facts.local_bindings - declarations
        else:
            local_barrier = set()
        for name, positions in inherited.items():
            if name not in local_barrier:
                literal_positions.setdefault(name, list(positions))
        if not literal_positions:
            continue
        for ch, fname, hard, where in _lv61_call_events(
                facts.own, literal_positions, facts.uncertain,
                facts.deleted, facts.conditional_lines, facts.guaranteed_resets):
            issues.append(_lv61_issue(
                filepath, src_lines, ch, fname, hard, where))
    return issues
_LV46_IMPLICIT_PARAM_NAMES = frozenset({'self', 'cls'})
_LV46_EXEMPT_DECORATORS = frozenset({'staticmethod'})
def _lv46_decorator_name(dec: ast.AST) -> str | None:
    if isinstance(dec, ast.Name):
        return dec.id
    if isinstance(dec, ast.Attribute):
        return dec.attr
    if isinstance(dec, ast.Call):
        return _lv46_decorator_name(dec.func)
    return None
def _lv46_has_exempt_decorator(fn: ast.FunctionDef) -> bool:
    return any(
        _lv46_decorator_name(dec) in _LV46_EXEMPT_DECORATORS
        for dec in fn.decorator_list
    )
def _lv46_scope_nodes(stmt: ast.AST) -> Iterator[ast.AST]:
    if isinstance(stmt, FUNC_SCOPE_NODES):
        yield stmt
        for child in definition_outer_children(stmt):
            yield from iter_nodes_outside(child)
        return
    yield from iter_nodes_outside(stmt)
def _lv46_non_positional_receivers(
        node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> set[str]:
    args = node.args
    names = {arg.arg for arg in args.kwonlyargs}
    if args.vararg is not None:
        names.add(args.vararg.arg)
    if args.kwarg is not None:
        names.add(args.kwarg.arg)
    return names & _LV46_IMPLICIT_PARAM_NAMES

def _lv46_implicit_refs(
        node: ast.FunctionDef | ast.AsyncFunctionDef) -> tuple[set[str], set[str]]:
    referenced: set[str] = set()
    local_binds: set[str] = set()
    for stmt in node.body:
        for sub in _lv46_scope_nodes(stmt):
            if isinstance(sub, ast.Name):
                if sub.id not in _LV46_IMPLICIT_PARAM_NAMES:
                    continue
                if isinstance(sub.ctx, ast.Load):
                    referenced.add(sub.id)
                elif isinstance(sub.ctx, ast.Store):
                    local_binds.add(sub.id)
                continue
            local_binds |= (bound_names_of(sub, include_params=False)
                            & _LV46_IMPLICIT_PARAM_NAMES)
    local_binds |= (
        scope_definition_names(node.body) & _LV46_IMPLICIT_PARAM_NAMES)
    local_binds |= (_declared_names(node, 'global')
                    | _declared_names(node, 'nonlocal'))
    referenced |= _lv46_nested_free_refs(
        node, _lv46_non_positional_receivers(node))
    return referenced, local_binds
def _lv46_deferred_children(scope: ast.AST) -> Iterator[ast.AST]:
    stack = list(scope_body_stmts(scope))
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.Lambda)):
            yield current
            stack.extend(definition_outer_children(current))
            continue
        stack.extend(ast.iter_child_nodes(current))
def _lv46_nested_free_refs(
        scope: ast.AST, ignored_local: frozenset[str] | set[str],
) -> set[str]:
    local = scope_local_bindings(scope) - ignored_local
    global_names = _declared_names(scope, 'global')
    referenced: set[str] = set()
    for name in _LV46_IMPLICIT_PARAM_NAMES - local - global_names:
        if any(position
               for stmt in scope_body_stmts(scope)
               for position in _load_positions(stmt, name, frozenset())):
            referenced.add(name)
    for child in _lv46_deferred_children(scope):
        referenced |= _lv46_nested_free_refs(child, frozenset())
    return referenced - local - global_names
def _lv46_first_failure(node: ast.FunctionDef | ast.AsyncFunctionDef) -> str:
    positional = len(node.args.posonlyargs) + len(node.args.args)
    if node.args.vararg is not None or positional > 0:
        return 'unbound'
    return 'arity'
def _lv46_vararg_receivers(
        node: ast.FunctionDef | ast.AsyncFunctionDef,
        missing: set[str],
) -> set[str]:
    if node.args.vararg is None:
        return set()
    return {node.args.vararg.arg} & missing

def _lv46_kwonly_receivers(
        node: ast.FunctionDef | ast.AsyncFunctionDef,
        missing: set[str],
) -> set[str]:
    return {arg.arg for arg in node.args.kwonlyargs} & missing

def _lv46_kwarg_receivers(
        node: ast.FunctionDef | ast.AsyncFunctionDef,
        missing: set[str],
) -> set[str]:
    if node.args.kwarg is None:
        return set()
    return {node.args.kwarg.arg} & missing
def _lv46_issue_head(
        node: ast.FunctionDef | ast.AsyncFunctionDef,
        missing: set[str], local_unbound: set[str]) -> str:
    names = '、'.join(sorted(missing))
    vararg_receivers = _lv46_vararg_receivers(node, missing)
    if vararg_receivers:
        vararg_names = '、'.join(sorted(vararg_receivers))
        return (f'类方法 {node.name} 将 {vararg_names} 用作 *args：'
                '值为位置实参 tuple，而非实例/类接收者')
    kwonly_receivers = _lv46_kwonly_receivers(node, missing)
    if kwonly_receivers:
        kwonly_names = '、'.join(sorted(kwonly_receivers))
        return (f'类方法 {node.name} 将 {kwonly_names} 声明为关键字专用参数：'
                '无法接收描述符按位置传入的实例/类')
    kwarg_receivers = _lv46_kwarg_receivers(node, missing)
    if kwarg_receivers:
        kwarg_names = '、'.join(sorted(kwarg_receivers))
        if _lv46_first_failure(node) == 'arity':
            return (f'类方法 {node.name} 仅将 {kwarg_names} 用作 **kwargs '
                    '且没有位置接收形参（实例调用即 TypeError）')
        return (f'类方法 {node.name} 将 {kwarg_names} 用作 **kwargs：'
                '值为关键字实参 dict，而非实例/类接收者')
    if _lv46_first_failure(node) == 'arity':
        return (f'类方法 {node.name} 引用 {names} 但参数表未声明'
                '（实例调用即 TypeError）')
    if local_unbound:
        outcome = ('体内名字解析或局部绑定失败'
                   if missing - local_unbound else
                   '体内局部名未绑定：UnboundLocalError')
        return (f'类方法 {node.name} 引用 {names} 但参数表未声明'
                f'（{outcome}）')
    return (f'类方法 {node.name} 引用 {names} 但参数表未声明'
            '（体内自由名 NameError）')
def _lv46_issue_detail(
        node: ast.FunctionDef | ast.AsyncFunctionDef,
        missing: set[str], local_unbound: set[str]) -> str:
    vararg_receivers = _lv46_vararg_receivers(node, missing)
    if vararg_receivers:
        vararg_names = '、'.join(sorted(vararg_receivers))
        detail = (
            f'``def {node.name}(...)`` 把 ``{vararg_names}`` 声明为变长位置'
            '参数。描述符传入的实例/类只会成为该 tuple 的一个元素，不会把'
            f'``{vararg_names}`` 本身绑定为接收者；访问接收者属性将触发 '
            'AttributeError，直接返回或传递该名字则会静默传递 tuple。'
        )
        remaining = missing - vararg_receivers
        if remaining:
            detail += ('\n此外，' + _lv46_issue_detail(
                node, remaining, local_unbound & remaining))
        return detail
    kwonly_receivers = _lv46_kwonly_receivers(node, missing)
    if kwonly_receivers:
        kwonly_names = '、'.join(sorted(kwonly_receivers))
        detail = (
            f'``def {node.name}(...)`` 把 ``{kwonly_names}`` 放在 ``*`` 之后。'
            '描述符传入的实例/类是位置实参，不会绑定到关键字专用形参。'
            '没有其他位置形参或 ``*args`` 时，额外的位置实参直接触发 '
            'TypeError；否则，必需关键字形参缺失会触发 TypeError，'
            '有默认值的名字则读到默认值而非接收者，后续属性访问可能 '
            'AttributeError，直接返回或传递会静默使用错误对象。'
        )
        remaining = missing - kwonly_receivers
        if remaining:
            detail += ('\n此外，' + _lv46_issue_detail(
                node, remaining, local_unbound & remaining))
        return detail
    kwarg_receivers = _lv46_kwarg_receivers(node, missing)
    if kwarg_receivers:
        kwarg_names = '、'.join(sorted(kwarg_receivers))
        if _lv46_first_failure(node) == 'arity':
            detail = (
                f'``def {node.name}(...)`` 仅通过 ``**{kwarg_names}`` '
                '接收关键字实参，没有可接收实例/类的位置形参；描述符额外'
                '传入的位置实参会在进入函数体前触发 TypeError。无实例的'
                '类访问调用虽不触发该参数个数错误，但此名字仍是关键字'
                '实参 dict，而不是实例/类接收者。'
            )
        else:
            detail = (
                f'``def {node.name}(...)`` 把 ``{kwarg_names}`` 声明为 '
                '变长关键字参数。实例/类由其他位置形参或 ``*args`` 吸收，'
                f'``{kwarg_names}`` 自身绑定为关键字实参 dict；访问接收者'
                '属性将触发 AttributeError，直接返回或传递该名字则会静默'
                '传递 dict。'
            )
        remaining = missing - kwarg_receivers
        if remaining:
            detail += ('\n此外，' + _lv46_issue_detail(
                node, remaining, local_unbound & remaining))
        return detail
    names = '、'.join(sorted(missing))
    head = (f'``def {node.name}(...)`` 类体内方法漏写隐式首参——函数体'
            f'引用 ``{names}``，但参数名集合不含该名；实例方法首参须 '
            '``self``、类方法首参须 ``cls``（配合 @classmethod 装饰）。')
    if _lv46_first_failure(node) == 'arity':
        return (head + '实例调用先把实例当作额外位置实参传入，参数个数'
                f'检查先失败：``TypeError: {node.name}() takes 0 '
                'positional arguments but 1 was given``（只有按未绑定方式'
                f'``Cls.{node.name}()`` 调用才走到体内 '
                f'``NameError: name {names} is not defined``）。')
    if not local_unbound:
        if node.args.vararg is not None:
            return (head + '实例被 ``*args`` 吸收，不触发参数个数检查；体内 '
                    f'``{names}`` 既非形参也无局部绑定，按全局名解析失败：'
                    f'``NameError: name {names} is not defined``。')
        return (head + '实例被填进首个位置形参，体内 '
                f'``{names}`` 既非形参也无局部绑定，按全局名解析失败：'
                f'``NameError: name {names} is not defined``。')
    receiver = ('实例被 ``*args`` 吸收，不触发参数个数检查；'
                if node.args.vararg is not None else
                '实例被填进首个位置形参；')
    local_names = '、'.join(sorted(local_unbound))
    failures = [
        (f'局部名 ``{local_names}`` 在有效绑定前、``del`` 后或 '
         '``except`` 变量释放后被读取，触发 ``UnboundLocalError``')
    ]
    free_names = missing - local_unbound
    if free_names:
        names_text = '、'.join(sorted(free_names))
        failures.append(
            f'自由名 ``{names_text}`` 无局部绑定，按全局名解析失败：'
            f'``NameError: name {names_text} is not defined``')
    return head + receiver + '；'.join(failures) + '。'
def _lv46_issue_texts(
        node: ast.FunctionDef | ast.AsyncFunctionDef,
        missing: set[str], local_unbound: set[str],
) -> tuple[str, str, str]:
    return (
        _lv46_issue_head(node, missing, local_unbound),
        _lv46_issue_detail(node, missing, local_unbound),
        (
            '根因：类方法隐式首参契约缺失（Python 实例方法不自\n'
            '动绑定 self，首参显式声明是绑定前提）。\n'
            f'修复策略：``def {node.name}(self, ...)`` 补隐式首参；\n'
            '若确为静态语义（不访问实例态）改用 ``@staticmethod``\n'
            '并移除体内 self 引用。\n'
            '参考标准：CPython 描述符协议（函数经类访问产生绑\n'
            '定方法，self 经显式首参传入）'
        ),
    )
def _lv46_missing_names(
        node: ast.AST, parents: dict,
) -> tuple[set[str], set[str]]:
    if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return set(), set()
    if not isinstance(nearest_scope(parents, node), ast.ClassDef):
        return set(), set()
    if _lv46_has_exempt_decorator(node):
        return set(), set()
    referenced, local_binds = _lv46_implicit_refs(node)
    args = node.args
    positional = (*args.posonlyargs, *args.args)
    explicit_params = {arg.arg for arg in positional}
    first_writes, windows, handler_binds = _lv12_first_bindings(node.body)
    self_reads = {
        name for name, (_lineno, reads_self) in first_writes.items()
        if reads_self
    }
    declared = (_declared_names(node, 'global')
                | _declared_names(node, 'nonlocal'))
    candidates = (((referenced | self_reads) & local_binds)
                  - explicit_params - declared)
    local_unbound: set[str] = set()
    for name in candidates:
        if first_writes.get(name, (0, False))[1]:
            local_unbound.add(name)
            continue
        unbound = _lv12_first_unbound_read(
            node.body, name, windows.get(name), handler_binds.get(name, ()))
        if unbound is not None:
            local_unbound.add(name)
    missing = (referenced - explicit_params - local_binds) | local_unbound
    return missing, local_unbound
def check_LV46(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    nodes = walk_ast_nodes(tree)
    if not nodes:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    for node in nodes:
        missing, local_unbound = _lv46_missing_names(node, parents)
        if not missing:
            continue
        title, desc, fix = _lv46_issue_texts(node, missing, local_unbound)
        issues.append(make_issue(
            'LV-46', 'P1', 'logic_correctness', filepath, node.lineno,
            title, desc, snippet_of(src_lines, node.lineno),
            fix, 'class-method-missing-self-param',
        ))
    return issues
def _lv47_body_returns(fn: ast.FunctionDef) -> list[ast.Return]:
    return [sub for stmt in fn.body
            for sub in iter_nodes_outside(stmt)
            if isinstance(sub, ast.Return)]
def _lv47_none_expr(value: ast.AST | None) -> bool:
    if value is None:
        return True
    if isinstance(value, ast.Constant) and value.value is None:
        return True
    if isinstance(value, ast.IfExp):
        return _lv47_none_expr(value.body) and _lv47_none_expr(value.orelse)
    return False
def _lv47_issue_texts() -> tuple[str, str, str]:
    return (
        '__init__ 存在带值 return：实例化即 TypeError',
        (
            '``__init__`` 的返回契约恒为 None——带值 return 在'
            '实例化完成时由类型机制抛 ``TypeError: __init__() '
            'should return None``。构造器向调用方暴露实例经 '
            '``cls(...)`` 返回值（``__new__``/``__init__`` 分工'
            '：__new__ 造对象、__init__ 只初始化不返回）。'
        ),
        (
            '根因：普通函数「出口必带值」直觉误用于构造器\n'
            '（__init__ 返回值由 CPython 固定消费，带值即崩）。\n'
            '修复策略：删除该 return 或改 ``return None``；需\n'
            '构造即校验失败时抛异常（``raise ValueError``）而\n'
            '非返回错误码。\n'
            '参考标准：CPython object.__init__ 返回契约（非\n'
            'None 返回值触发 TypeError）'
        ),
    )
def _lv47_is_generator(
        fn: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    return any(
        isinstance(sub, (ast.Yield, ast.YieldFrom))
        for stmt in fn.body for sub in iter_nodes_outside(stmt))
def _lv47_violating_returns(node: ast.AST, parents: dict) -> list[ast.Return]:
    if not isinstance(node, ast.FunctionDef) or node.name != '__init__':
        return []
    if not isinstance(nearest_scope(parents, node), ast.ClassDef):
        return []
    return [ret for ret in _lv47_body_returns(node)
            if not _lv47_none_expr(ret.value)]
def check_LV47(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    nodes = walk_ast_nodes(tree)
    if not nodes:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    title, desc, fix = _lv47_issue_texts()
    for node in nodes:
        if (isinstance(node, ast.AsyncFunctionDef) and node.name == '__init__'
                and isinstance(nearest_scope(parents, node), ast.ClassDef)):
            is_generator = _lv47_is_generator(node)
            object_kind = '异步生成器' if is_generator else '协程'
            object_type = 'async_generator' if is_generator else 'coroutine'
            issues.append(make_issue(
                'LV-47', 'P1', 'logic_correctness', filepath, node.lineno,
                f'async __init__ 返回{object_kind}：实例化即 TypeError',
                (
                    f'异步构造器被调用时创建并返回{object_kind}对象，而类型机制要求 '
                    '``__init__`` 返回 None；即使体内没有显式 return，'
                    '实例化仍抛 ``TypeError: __init__() should return '
                    f'None, not {object_type}``。'
                ),
                snippet_of(src_lines, node.lineno),
                (
                    f'根因：当前 async def 的调用结果恒为{object_kind}，与 '
                    '__init__ 的 None 返回契约不可兼容。\n修复策略：改为同步 '
                    '__init__，把异步初始化移到独立 async 工厂或异步初始化方法；'
                    'yield 逻辑应迁到独立的异步生成器。'
                    if is_generator else
                    '根因：async def 的调用结果恒为协程，与 __init__ 的 None '
                    '返回契约不可兼容。\n修复策略：改为同步 __init__，'
                    '把异步初始化移到独立 async 工厂或异步初始化方法。'
                ),
                ('async-generator-init-returns-async-generator'
                 if is_generator else 'async-init-returns-coroutine'),
            ))
            continue
        if (isinstance(node, ast.FunctionDef) and node.name == '__init__'
                and isinstance(nearest_scope(parents, node), ast.ClassDef)
                and _lv47_is_generator(node)):
            issues.append(make_issue(
                'LV-47', 'P1', 'logic_correctness', filepath, node.lineno,
                '__init__ 是生成器函数：实例化即 TypeError',
                (
                    '生成器函数被调用时创建并返回生成器对象，而类型机制要求 '
                    '``__init__`` 返回 None；即使体内没有带值 return，'
                    '实例化仍抛 ``TypeError: __init__() should return '
                    "None, not 'generator'``。"
                ),
                snippet_of(src_lines, node.lineno),
                (
                    '根因：函数体内出现 yield 使整个函数成为生成器——'
                    '调用结果是生成器对象，与 __init__ 的 None 返回契约'
                    '不可兼容。\n修复策略：把 yield/迭代逻辑移到独立方法或'
                    '生成器函数，__init__ 只做同步初始化。'
                ),
                'generator-init-returns-generator',
            ))
            continue
        for ret in _lv47_violating_returns(node, parents):
            issues.append(make_issue(
                'LV-47', 'P1', 'logic_correctness', filepath, ret.lineno,
                title, desc, snippet_of(src_lines, ret.lineno),
                fix, 'init-returns-value',
            ))
    return issues
_LV03_ACCUM_METHODS = frozenset({'append', 'extend', 'insert', 'add', 'update'})
def _lv03_constant_is_empty(value: Any) -> bool:
    if isinstance(value, bool) or value is None:
        return False
    if isinstance(value, (int, float, complex)):
        return value == 0
    return value in ('', b'')
_LV03_EMPTY_CONTAINER_CALLS = frozenset({
    'set', 'frozenset', 'list', 'dict', 'tuple',
})
def _lv03_is_empty_container_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in _LV03_EMPTY_CONTAINER_CALLS
            and not node.args and not node.keywords)
def _lv03_empty_literal(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return _lv03_constant_is_empty(node.value)
    if isinstance(node, (ast.List, ast.Tuple)):
        return not node.elts
    if isinstance(node, ast.Dict):
        return not node.keys
    return _lv03_is_empty_container_call(node)
def _lv03_assign_reset_names(stmt: ast.Assign) -> list[str]:
    if not stmt.targets:
        return []
    if len(stmt.targets) == 1:
        target = stmt.targets[0]
        if isinstance(target, ast.Name):
            return [target.id] if _lv03_empty_literal(stmt.value) else []
        if not isinstance(target, (ast.Tuple, ast.List)):
            return []
        if not (isinstance(stmt.value, (ast.Tuple, ast.List))
                and len(stmt.value.elts) == len(target.elts)):
            return []
        reset: list[str] = []
        for subtarget, value in zip(target.elts, stmt.value.elts):
            if (isinstance(subtarget, ast.Name)
                    and _lv03_empty_literal(value)):
                reset.append(subtarget.id)
        return reset
    if not all(isinstance(target, ast.Name) for target in stmt.targets):
        return []
    return ([target.id for target in stmt.targets]
            if _lv03_empty_literal(stmt.value) else [])
def _lv03_reset_targets(stmt: ast.AST) -> list[str]:
    if isinstance(stmt, ast.Assign):
        return _lv03_assign_reset_names(stmt)
    if isinstance(stmt, ast.AnnAssign):
        if (isinstance(stmt.target, ast.Name)
                and stmt.value is not None
                and _lv03_empty_literal(stmt.value)):
            return [stmt.target.id]
        return []
    if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
        call = stmt.value
        if (isinstance(call.func, ast.Attribute)
                and call.func.attr == 'clear'
                and isinstance(call.func.value, ast.Name)
                and not call.args and not call.keywords):
            return [call.func.value.id]
    return []
def _lv03_augassign_target(n: ast.AugAssign) -> str | None:
    if isinstance(n.target, ast.Name):
        return n.target.id
    if (isinstance(n.target, ast.Subscript)
            and isinstance(n.target.value, ast.Name)):
        return n.target.value.id
    return None
def _lv03_subassign_target(n: ast.Assign) -> str | None:
    if (n.targets and isinstance(n.targets[0], ast.Subscript)
            and isinstance(n.targets[0].value, ast.Name)):
        return n.targets[0].value.id
    return None
def _lv03_accum_call_target(n: ast.Call) -> str | None:
    if (isinstance(n.func, ast.Attribute)
            and n.func.attr in _LV03_ACCUM_METHODS
            and isinstance(n.func.value, ast.Name)):
        return n.func.value.id
    return None
def _lv03_self_rebind_target(n: ast.Assign) -> str | None:
    if len(n.targets) != 1 or not isinstance(n.targets[0], ast.Name):
        return None
    name = n.targets[0].id
    return name if _name_reads_self(name, n.value) else None
def _lv03_accum_var(n: ast.AST) -> str | None:
    if isinstance(n, ast.AugAssign):
        return _lv03_augassign_target(n)
    if isinstance(n, ast.Assign):
        return _lv03_subassign_target(n) or _lv03_self_rebind_target(n)
    if isinstance(n, ast.Call):
        return _lv03_accum_call_target(n)
    return None
def _lv03_accum_points(body: list) -> dict[str, list[tuple[int, int]]]:
    accums: dict[str, list[tuple[int, int]]] = {}
    for sub in body:
        if _lv03_reset_targets(sub):
            continue
        deferred = _lv03_deferred_body_ids(sub)
        for n in walk_nodes(sub):
            if id(n) in deferred:
                continue
            _var = _lv03_accum_var(n)
            if _var is not None:
                accums.setdefault(_var, []).append((n.lineno, n.col_offset))
    return accums
def _lv03_deferred_body_ids(stmt: ast.AST) -> set[int]:
    excluded: set[int] = set()
    stack: list[ast.AST] = [stmt]
    while stack:
        cur = stack.pop()
        face = _lv03_definition_face(cur)
        if face is None:
            stack.extend(ast.iter_child_nodes(cur))
            continue
        deferred_roots, evaluated_children = face
        for root in deferred_roots:
            excluded.update(id(x) for x in walk_nodes(root))
        stack.extend(evaluated_children)
    return excluded
def _lv03_definition_face(
        cur: ast.AST,
) -> tuple[list[ast.AST], list[ast.AST]] | None:
    if isinstance(cur, ast.GeneratorExp):
        deferred: list[ast.AST] = [
            *comprehension_elt_nodes(cur),
            *(gen.target for gen in cur.generators),
            *(gen.iter for gen in cur.generators[1:]),
            *(cond for gen in cur.generators for cond in gen.ifs),
        ]
        return deferred, ([cur.generators[0].iter] if cur.generators else [])
    if isinstance(cur, FUNC_SCOPE_NODES):
        if isinstance(cur, ast.ClassDef):
            deferred: list[ast.AST] = []
        elif isinstance(cur, ast.Lambda):
            deferred = [cur.body]
        else:
            deferred = list(cur.body)
        return deferred, definition_evaluated_children(cur)
    return None
def _lv03_container_rebinds(var: str, anc: ast.AST, seq: list) -> bool:
    if seq is not getattr(anc, 'body', None):
        return False
    if isinstance(anc, (ast.For, ast.AsyncFor)):
        return var in target_store_name_set([anc.target])
    if isinstance(anc, (ast.With, ast.AsyncWith)):
        return any(it.optional_vars is not None
                   and var in target_store_name_set([it.optional_vars])
                   for it in anc.items)
    return isinstance(anc, ast.ExceptHandler) and anc.name == var
class _Lv03ScanCtx(NamedTuple):
    parents: dict
    body_seq: list
    body_idx: int
    loop: ast.AST
def _lv03_rebind_kills_load(
        var: str, load_node: ast.AST, ctx: _Lv03ScanCtx) -> bool:
    cur = load_node
    while True:
        anc = ctx.parents.get(id(cur))
        if anc is None:
            return False
        hit = _lv03_enclosing_seq_index(anc, cur)
        if hit is not None:
            seq, idx = hit
            if _lv03_container_rebinds(var, anc, seq):
                return True
            if any(_lv03_rebind_after_loop(var, prev, ctx)
                   for prev in seq[:idx]):
                return True
        cur = anc
def _lv03_enclosing_seq_index(
        anc: ast.AST | None, cur: ast.AST,
) -> tuple[list, int] | None:
    if anc is None:
        return None
    for attr in ("body", "orelse", "finalbody"):
        seq = getattr(anc, attr, None)
        if not isinstance(seq, list):
            continue
        idx = next((i for i, s in enumerate(seq) if s is cur), None)
        if idx is not None:
            return seq, idx
    return None
def _lv03_rebind_after_loop(
        var: str, stmt: ast.AST, ctx: _Lv03ScanCtx) -> bool:
    loop_pos = (ctx.loop.lineno, ctx.loop.col_offset)
    loop_else = getattr(ctx.loop, 'orelse', ())
    for node, name, _value in iter_binding_entries([stmt]):
        if name != var or node is ctx.loop:
            continue
        position = (getattr(node, 'lineno', 0) or 0,
                    getattr(node, 'col_offset', 0) or 0)
        if position <= loop_pos:
            continue
        if isinstance(node, (ast.For, ast.AsyncFor, ast.ExceptHandler)):
            continue
        direct_stmt_binding = (
            node is stmt
            or (isinstance(stmt, ast.Expr) and node is stmt.value))
        direct_else_binding = any(
            node is else_stmt
            or (isinstance(else_stmt, ast.Expr)
                and node is else_stmt.value)
            for else_stmt in loop_else)
        loop_child = _direct_child_under(
            ctx.loop, node, ctx.parents)
        if loop_child is not None:
            if loop_child not in loop_else or not direct_else_binding:
                continue
        elif not direct_stmt_binding:
            continue
        return True
    return False
def _lv03_stmt_reads_after(
        var: str, stmt: ast.AST, ctx: _Lv03ScanCtx) -> bool:
    excluded = _lv03_deferred_body_ids(stmt)
    for n in walk_nodes(stmt):
        direct_load = (
            isinstance(n, ast.Name) and n.id == var
            and isinstance(n.ctx, ast.Load))
        augmented_read = (
            isinstance(n, ast.AugAssign)
            and _lv03_augassign_target(n) == var)
        if ((direct_load or augmented_read) and id(n) not in excluded):
            if _lv03_rebind_kills_load(var, n, ctx):
                continue
            return True
    return False
def _lv03_loop_else_read(
        var: str, node: ast.For | ast.AsyncFor | ast.While,
        body_seq: list, seq_idx: int, parents: dict) -> bool:
    ctx = _Lv03ScanCtx(parents, body_seq, seq_idx, node)
    return any(
        _lv03_stmt_reads_after(var, stmt, ctx) for stmt in node.orelse)
def _lv03_read_following(var: str, node: ast.AST, body_seq: list, seq_idx: int,
                         parents: dict) -> bool:
    cur: ast.AST = node
    first = True
    while True:
        parent = parents.get(id(cur))
        if parent is None:
            return False
        hit = _lv03_enclosing_seq_index(parent, cur)
        if hit is not None:
            seq, idx = hit
            lo = (seq_idx + 1) if first else idx + 1
            ctx = _Lv03ScanCtx(parents, body_seq, seq_idx, node)
            for stmt in seq[lo:]:
                if _lv03_stmt_reads_after(var, stmt, ctx):
                    return True
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.Lambda, ast.ClassDef, ast.Module)):
            return False
        first = False
        cur = parent
def _lv03_issue(var: str, lineno: int, filepath: Any,
                src_lines: list) -> dict[str, Any]:
    return make_issue(
        'LV-03', 'P1', 'logic_correctness', filepath, lineno,
        f'循环体内重置累加器：{var} 每轮被清零/清空，跨轮累积失效',
        (
            f'``{var} = <空值>`` 位于循环体内且其后有 ``{var}`` 的'
            f'累积操作（+= / ``{var} = {var} + ...`` 自引用重绑 /'
            ' append / 下标赋值），循环结束后 '
            f'``{var}`` 又被读取——意图是跨轮累积/收集，但每轮'
            f'开头的重置使最终值只保留最后一轮数据，静默产出'
            f'错误结果（无异常抛出）。'
        ),
        snippet_of(src_lines, lineno),
        (
            '根因：累加器/收集器初始化语句被误置于循环体内'
            '（重构移动语句时的典型错位）。\n'
            f'修复策略：把 ``{var} = <空值>`` 移到循环之前；'
            '若确实需要每轮独立统计，则消费也应留在循环体内'
            '（循环外不读）。\n'
            '参考标准：累加器重置缺陷模式（行为级阳性对照实验）'
        ),
        'accumulator-reset-in-loop',
    )
def _lv03_block_stops_iteration(
        stmts: list[ast.stmt], node: ast.For | ast.AsyncFor | ast.While,
        parents: dict[int, ast.AST]) -> bool:
    for stmt in stmts:
        if isinstance(stmt, (ast.Return, ast.Raise)):
            return True
        if (isinstance(stmt, ast.Break)
                and break_binding_loop(parents, stmt) is node):
            return True
        if isinstance(stmt, ast.Continue):
            return False
        if (isinstance(stmt, ast.If) and stmt.orelse
                and _lv03_block_stops_iteration(stmt.body, node, parents)
                and _lv03_block_stops_iteration(stmt.orelse, node, parents)):
            return True
    return False
def _lv03_loop_hits(node: ast.For | ast.AsyncFor | ast.While,
                    parents: dict[int, ast.AST],
                    body_seq: list, seq_idx: int) -> list[tuple[str, int]]:
    accums = _lv03_accum_points(node.body)
    if not accums:
        return []
    single_iteration = _lv03_block_stops_iteration(
        node.body, node, parents)
    hits: list[tuple[str, int]] = []
    for sub in node.body:
        position = (sub.lineno, sub.col_offset)
        for var in _lv03_reset_targets(sub):
            if not any(pos > position for pos in accums.get(var, ())):
                continue
            else_read = _lv03_loop_else_read(
                var, node, body_seq, seq_idx, parents)
            following_read = _lv03_read_following(
                var, node, body_seq, seq_idx, parents)
            if not single_iteration and (else_read or following_read):
                hits.append((var, sub.lineno))
    return hits
def check_LV03(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    for node in roots:
        if not isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            continue
        sibling = _lv03_enclosing_seq_index(parents.get(id(node)), node)
        if sibling is None:
            continue
        body_seq, seq_idx = sibling
        for var, lineno in _lv03_loop_hits(node, parents,
                                           body_seq, seq_idx):
            issues.append(_lv03_issue(var, lineno, filepath, src_lines))
    return issues
def _lv55_lambda_late_refs(lam: ast.Lambda, loop_vars: set[str]) -> set[str]:
    candidates = loop_vars - param_names(lam)
    return {
        name for name in candidates
        if any(_load_positions(
            lam.body, name, frozenset(),
            include_deferred_generators=True))
    }
_LV55_ACCUM_METHODS = frozenset({
    'append', 'add', 'insert', 'extend', 'setdefault', 'update',
})
_LV55_CONTAINER_NODES = (ast.List, ast.Tuple, ast.Set, ast.Dict)
def _lv55_escaped_lambdas(
        owner: ast.AST, roots: Iterable[ast.AST]) -> list[ast.Lambda]:
    immediate = _lv55_immediate_lambda_ids(owner)
    return [node for root in roots for node in walk_nodes(root)
            if isinstance(node, ast.Lambda) and id(node) not in immediate]
def _lv55_accum_lambdas(sub: ast.AST) -> list[ast.Lambda]:
    if (isinstance(sub, ast.Call) and isinstance(sub.func, ast.Attribute)
            and sub.func.attr in _LV55_ACCUM_METHODS):
        return _lv55_escaped_lambdas(
            sub, [*sub.args, *(kw.value for kw in sub.keywords)])
    if isinstance(sub, (ast.List, ast.Tuple, ast.Set)):
        return _lv55_escaped_lambdas(sub, sub.elts)
    if isinstance(sub, ast.Dict):
        return _lv55_escaped_lambdas(sub, [
            *(key for key in sub.keys if key is not None), *sub.values])
    if isinstance(sub, (ast.Assign, ast.AnnAssign)):
        targets = (sub.targets if isinstance(sub, ast.Assign)
                   else [sub.target])
        if sub.value is None or not any(
                isinstance(tgt, ast.Subscript) for tgt in targets):
            return []
        return _lv55_escaped_lambdas(sub, [sub.value])
    return []
_LV55_EAGER_KEY_CALLS = frozenset({'sorted', 'min', 'max'})
def _lv55_immediate_lambda_ids(root: ast.AST) -> set[int]:
    immediate: set[int] = set()
    def visit_defaults(lam: ast.Lambda) -> None:
        defaults = (
            *lam.args.defaults,
            *(item for item in lam.args.kw_defaults if item is not None),
        )
        for default in defaults:
            visit(default)
    def visit_eager_key(node: ast.AST) -> None:
        if isinstance(node, ast.Lambda):
            immediate.add(id(node))
            visit_defaults(node)
            visit(node.body)
            return
        for child in ast.iter_child_nodes(node):
            visit_eager_key(child)
    def visit(node: ast.AST) -> None:
        if isinstance(node, ast.Lambda):
            visit_defaults(node)
            return
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Lambda):
                immediate.add(id(node.func))
                visit(node.func.body)
            eager_key_call = (
                (isinstance(node.func, ast.Name)
                 and node.func.id in _LV55_EAGER_KEY_CALLS)
                or (isinstance(node.func, ast.Attribute)
                    and node.func.attr == 'sort'))
            if eager_key_call:
                for keyword in node.keywords:
                    if keyword.arg == 'key':
                        visit_eager_key(keyword.value)
        for child in ast.iter_child_nodes(node):
            visit(child)
    visit(root)
    return immediate
def _lv55_shadowed_between(
    lam: ast.Lambda, ref: str, boundary: ast.AST,
    parents: dict[int, ast.AST],
) -> bool:
    current = parents.get(id(lam))
    while current is not None and current is not boundary:
        if isinstance(current, (ast.Lambda, ast.FunctionDef,
                                ast.AsyncFunctionDef)):
            declared = (_declared_names(current, 'global')
                        | _declared_names(current, 'nonlocal'))
            if ref in scope_local_bindings(current) - declared:
                return True
        if (isinstance(current, COMP_NODES)
                and ref in target_store_name_set(
                    [gen.target for gen in current.generators])):
            return True
        current = parents.get(id(current))
    return False
def _lv55_comp_hits(
    node: ast.AST, parents: dict[int, ast.AST],
) -> Iterator[tuple[ast.Lambda, str, str]]:
    comp_vars = target_store_name_set(
        [gen.target for gen in getattr(node, 'generators', [])])
    if not comp_vars:
        return
    elts = ([node.key, node.value] if isinstance(node, ast.DictComp)
            else [node.elt])
    for elt in elts:
        immediate = _lv55_immediate_lambda_ids(elt)
        for lam in walk_nodes(elt):
            if not isinstance(lam, ast.Lambda):
                continue
            if id(lam) in immediate:
                continue
            for ref in sorted(_lv55_lambda_late_refs(lam, comp_vars)):
                if _lv55_shadowed_between(lam, ref, node, parents):
                    continue
                yield lam, ref, '推导式'
def _lv55_unread_overwrite_literal_ids(node: ast.AST) -> set[int]:
    reads = {
        sub.id for stmt in node.body for sub in walk_nodes(stmt)
        if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
    }
    excluded: set[int] = set()
    for stmt in scan_body_no_funcs(node.body):
        if (isinstance(stmt, ast.Assign) and stmt.targets
                and all(isinstance(target, ast.Name)
                        for target in stmt.targets)):
            names = {target.id for target in stmt.targets}
            value = stmt.value
        elif (isinstance(stmt, ast.AnnAssign)
                and isinstance(stmt.target, ast.Name)
                and stmt.value is not None):
            names = {stmt.target.id}
            value = stmt.value
        else:
            continue
        if names & reads or not isinstance(value, _LV55_CONTAINER_NODES):
            continue
        excluded.update(
            id(item) for item in walk_nodes(value)
            if isinstance(item, _LV55_CONTAINER_NODES))
    return excluded
def _lv55_loop_vars(node: ast.AST) -> set[str]:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return target_store_name_set([node.target])
    deferred = _lv03_deferred_body_ids(node.test)
    test_reads = {
        sub.id for sub in walk_nodes(node.test)
        if (isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
            and id(sub) not in deferred)
    }
    test_bindings = {
        sub.target.id for sub in walk_nodes(node.test)
        if isinstance(sub, ast.NamedExpr) and id(sub) not in deferred
    }
    return ((set(assigned_names(node.body)) & test_reads) | test_bindings)
def _lv55_loop_hits(
    node: ast.AST, parents: dict[int, ast.AST],
) -> Iterator[tuple[ast.Lambda, str, str]]:
    loop_vars = _lv55_loop_vars(node)
    if not loop_vars:
        return
    seen: set[tuple[int, str]] = set()
    overwritten_ids = _lv55_unread_overwrite_literal_ids(node)
    for stmt in node.body:
        discarded_ids: set[int] = set(overwritten_ids)
        if (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, _LV55_CONTAINER_NODES)):
            discarded_ids.update(
                id(item) for item in walk_nodes(stmt.value)
                if isinstance(item, _LV55_CONTAINER_NODES))
        for sub in walk_nodes(stmt):
            if id(sub) in discarded_ids:
                continue
            for lam in _lv55_accum_lambdas(sub):
                for ref in sorted(_lv55_lambda_late_refs(lam, loop_vars)):
                    if _lv55_shadowed_between(lam, ref, node, parents):
                        continue
                    key = (id(lam), ref)
                    if key in seen:
                        continue
                    seen.add(key)
                    where = ('while 循环体' if isinstance(node, ast.While)
                             else 'for 循环体')
                    yield lam, ref, where
def _lv55_issue(lam: ast.Lambda, ref: str, where: str, filepath: Any,
                src_lines: list[str]) -> dict[str, Any]:
    return make_issue(
        'LV-55', 'P2', 'logic_correctness', filepath, lam.lineno,
        f'lambda 迟绑定循环变量 ``{ref}``（{where}）：全部回调读到终值',
        (
            f'lambda 体内引用循环变量 ``{ref}`` 未用默认参数固定'
            '——闭包按名字捕获：循环结束后所有 lambda 读取同一'
            f'变量晚绑定值，第 1..N-1 轮的 ``{ref}`` 全部静默变'
            '成最后一轮值（回调/映射表/参数包整体错位，无异常）。'
        ),
        snippet_of(src_lines, lam.lineno),
        (
            '根因：Python 闭包是名字绑定（late binding），def 时\n'
            '不求值；循环变量不在 lambda 自身作用域创建新快照。\n'
            f'修复策略：默认参数固定 ``lambda {ref}={ref}: ...``；\n'
            '或用 functools.partial 绑定当轮值、或具名函数工厂。\n'
            '参考标准：PEP 289/PEP 227 闭包绑定语义（faq:why-\n'
            'do-lambdas-defined-in-a-loop-all-return-the-same）'
        ),
        'lambda-late-binding-loop-var',
    )
def check_LV55(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    issues: list[dict[str, Any]] = []
    roots = walk_ast_nodes(tree)
    if not roots:
        return issues
    src_lines = source_lines(source)
    parents = parent_map_of(tree)
    seen_hits: set[tuple[int, str]] = set()
    for node in roots:
        if isinstance(node, COMP_NODES):
            hits = _lv55_comp_hits(node, parents)
        elif isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
            hits = _lv55_loop_hits(node, parents)
        else:
            continue
        for lam, ref, where in hits:
            key = (id(lam), ref)
            if key in seen_hits:
                continue
            seen_hits.add(key)
            issues.append(_lv55_issue(
                lam, ref, where, filepath, src_lines))
    return issues

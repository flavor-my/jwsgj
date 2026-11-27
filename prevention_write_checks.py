from __future__ import annotations

import ast
import logging
import os
from collections import deque
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_nodes import (
    attr_chain_key,
    build_parent_map,
    decorator_name,
    handler_exc_names,
    is_broad_except,
    str_constant_value,
)
from jwsgj.diag_shared_ast_nodes import (
    subscript_base_name as _shared_subscript_base_name,
)
from jwsgj.diag_shared_ast_views import tree_nodes
from jwsgj.diag_types_defs import finding_scan_exempt
from jwsgj.prevention_scope_facts import (
    FUNC_SCOPE_NODES,
    SCOPE_CONTAINERS,
    binding_body_start,
    block_exits,
    branch_truth,
    flow_var_resolver,
    func_name_of_call,
    import_bound_names,
    is_none_constant,
    iter_nodes_outside,
    make_issue,
    nearest_scope,
    node_end_position,
    rebound_binding_names,
    scope_body_stmts,
    scope_local_bindings,
    shadowed_binding_at,
    snippet_of,
    source_lines,
    stmt_siblings,
    target_binding_names,
    walk_nodes,
    walk_scope_expr,
)

__all__ = [
    'WRITE_DIRECT_CHECKS',
    'check_DC05',
    'check_EF01',
    'check_NL01',
    'check_WM01',
]
_log = logging.getLogger(__name__)
_log.info("prevention_write_checks 编写时检查器已加载: %d 项导出", len(__all__))
def _log_detector_findings(rule_id: str, summary: str,
                           issues: list[dict[str, Any]],
                           filepath: Any) -> None:
    if not issues:
        return
    lines = [i.get('line') for i in issues[:10]]
    _log.info("%s 检出 %d 项%s: %s", rule_id, len(issues), summary,
              ", ".join(str(n) for n in lines),
              extra={
                  "event": "detector_findings",
                  "payload": {
                      "rule_id": rule_id,
                      "count": len(issues),
                      "file": filepath,
                      "lines": lines,
                  },
              })
def _unwrap_await(expr: ast.AST) -> ast.AST:
    while isinstance(expr, ast.Await):
        expr = expr.value
    return expr
_DATACLASS_DECORATORS = frozenset({
    'dataclass', 'define', 'frozen', 'mutable', 'attrs',
    'attr.s', 'attr.attributes', 'attr.attrs',
    'attrs.define', 'attrs.frozen', 'attrs.mutable',
})
_DATACLASS_IMPORT_MODULES = frozenset({
    'dataclasses', 'attr', 'attrs', 'pydantic.dataclasses',
})
_DATACLASS_IMPORT_NAMES = frozenset({
    'dataclass', 's', 'attributes', 'attrs', 'define', 'frozen', 'mutable',
})
def _decorator_target(dec: ast.expr) -> ast.expr:
    return dec.func if isinstance(dec, ast.Call) else dec
def _decorator_names(decorators: list[ast.expr]) -> set[str]:
    names: set[str] = set()
    for dec in decorators:
        target = _decorator_target(dec)
        last = decorator_name(dec) or None
        if last:
            names.add(last)
        chain = attr_chain_key(target)
        if chain is not None:
            names.add(chain)
    return names
def _is_classvar_annotation(ann: ast.expr) -> bool:
    return (isinstance(ann, ast.Name) and ann.id == 'ClassVar') or (
        isinstance(ann, ast.Attribute) and ann.attr == 'ClassVar')
def _init_field_count_of(item: ast.stmt) -> int:
    if not isinstance(item, ast.AnnAssign):
        return 0
    ann = item.annotation
    if isinstance(ann, ast.Subscript):
        ann = ann.value
    return 0 if _is_classvar_annotation(ann) else 1
def _declares_constructor(item: ast.stmt) -> bool:
    return (isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))
            and item.name in ('__init__', '__new__'))
def _count_init_fields(body: list[ast.stmt]) -> tuple[int, bool]:
    return (sum(_init_field_count_of(item) for item in body),
            any(_declares_constructor(item) for item in body))
def _is_parametrized_name_call(node: ast.AST) -> bool:
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and bool(node.args or node.keywords))
def _dc05_collect_name_evidence(tree: ast.AST) -> list[ast.Call]:
    return [node for node in walk_nodes(tree)
            if _is_parametrized_name_call(node)]
def _definition_rebinding_names(node: ast.AST) -> set[str]:
    if isinstance(node, (ast.Global, ast.Nonlocal)):
        return set()
    names = set(rebound_binding_names(node))
    for target, _value in iter_write_targets(node):
        names |= target_binding_names(target)
    if isinstance(node, ast.AugAssign):
        names |= target_binding_names(node.target)
    return names
def _definition_binding_position(node: ast.AST) -> tuple[int, int]:
    if isinstance(node, (ast.For, ast.AsyncFor, ast.With, ast.AsyncWith)):
        return binding_body_start(node)
    if isinstance(node, ast.ExceptHandler):
        return (node.lineno, node.col_offset)
    return node_end_position(node)
def _definition_rebinding_positions(
        scope: ast.AST,
        class_node: ast.ClassDef | ast.FunctionDef | ast.AsyncFunctionDef,
) -> list[tuple[int, int]]:
    positions: list[tuple[int, int]] = []
    stack = list(scope_body_stmts(scope))
    while stack:
        node = stack.pop()
        if node is class_node:
            continue
        if class_node.name in _definition_rebinding_names(node):
            positions.append(_definition_binding_position(node))
        if not isinstance(node, FUNC_SCOPE_NODES):
            stack.extend(ast.iter_child_nodes(node))
    return positions
def _definition_inner_scope_shadows(
        call: ast.Call,
        class_node: ast.ClassDef | ast.FunctionDef | ast.AsyncFunctionDef,
        class_scope: ast.AST,
        parents: dict[int, ast.AST]) -> bool:
    cur = parents.get(id(call))
    in_function = False
    while cur is not None and cur is not class_scope:
        if cur is class_node and not in_function:
            return True
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            in_function = True
            if class_node.name in scope_local_bindings(cur):
                return True
        elif isinstance(cur, ast.ClassDef):
            if not in_function and class_node.name in scope_local_bindings(cur):
                return True
        cur = parents.get(id(cur))
    return cur is not class_scope
def _call_resolves_to_definition(
        call: ast.Call,
        class_node: ast.ClassDef | ast.FunctionDef | ast.AsyncFunctionDef,
        parents: dict[int, ast.AST]) -> bool:
    class_scope = nearest_scope(parents, class_node)
    if class_scope is None or _definition_inner_scope_shadows(
            call, class_node, class_scope, parents):
        return False
    class_pos = node_end_position(class_node)
    call_pos = (call.lineno, call.col_offset)
    same_scope = nearest_scope(parents, call) is class_scope
    if same_scope and call_pos < class_pos:
        return False
    for rebound_pos in _definition_rebinding_positions(class_scope, class_node):
        if rebound_pos <= class_pos:
            continue
        if not same_scope or rebound_pos <= call_pos:
            return False
    return True
def _dc05_dataclass_names(tree: ast.AST) -> frozenset[str]:
    names = set(_DATACLASS_DECORATORS)
    for node in walk_nodes(tree):
        if isinstance(node, ast.ImportFrom):
            module = node.module or ''
            if (module not in _DATACLASS_IMPORT_MODULES
                    and not module.endswith('.dataclasses')):
                continue
            for alias in node.names:
                if alias.name in _DATACLASS_IMPORT_NAMES:
                    names.add(alias.asname or alias.name)
            continue
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            local = alias.asname or alias.name
            if alias.name == 'attr':
                names.update((local + '.s', local + '.attributes',
                              local + '.attrs'))
            elif alias.name == 'attrs':
                names.update((local + '.define', local + '.frozen',
                              local + '.mutable'))
            elif (alias.name in _DATACLASS_IMPORT_MODULES
                    or alias.name.endswith('.dataclasses')):
                names.add(local + '.dataclass')
    return frozenset(names)
def _dc05_uninitialized_field_count(node: ast.ClassDef,
                                    dataclass_names: frozenset[str]
                                    ) -> int | None:
    bases = [b for b in node.bases
             if not (isinstance(b, ast.Name) and b.id == 'object')]
    if bases:
        return None
    if _decorator_names(node.decorator_list) & dataclass_names:
        return None
    ann_count, has_init = _count_init_fields(node.body)
    if ann_count == 0 or has_init:
        return None
    return ann_count
def check_DC05(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[dict[str, Any]] = []
    if not isinstance(tree, ast.AST):
        return issues
    src_lines = source_lines(source)
    calls = _dc05_collect_name_evidence(tree)
    dataclass_names = _dc05_dataclass_names(tree)
    parents = build_parent_map(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        ann_count = _dc05_uninitialized_field_count(node, dataclass_names)
        if ann_count is None:
            continue
        if not any(call.func.id == node.name and _call_resolves_to_definition(
                call, node, parents) for call in calls):
            continue
        issues.append(_dc05_finding(node, ann_count, filepath, src_lines))
    _log_detector_findings("DC-05", "数据类缺 @dataclass", issues, filepath)
    return issues
def _dc05_finding(node: ast.ClassDef, ann_count: int, filepath: Any,
                  src_lines: Any) -> dict[str, Any]:
    return make_issue(
        'DC-05', 'P1', 'type_safety', filepath, node.lineno,
        f"类 '{node.name}' 含 {ann_count} 个注解字段但未加 @dataclass",
        (
            f"类 '{node.name}' 定义了类型注解字段且无 __init__，但缺少 "
            f"@dataclass 装饰器——字段注解不会生成构造器，"
            f"{node.name}(...) 实例化直接 TypeError: __init__() takes "
            f"1 positional argument。AI 手写数据类时高频遗漏。"
        ),
        snippet_of(src_lines, node.lineno),
        (
            '根因：数据类缺少 @dataclass 装饰器，注解字段不生成构造器。\n'
            f'修复策略：from dataclasses import dataclass 后在 class '
            f'{node.name} 上加 @dataclass；若类是 Enum/TypedDict/Protocol/'
            'pydantic BaseModel 则应显式继承对应基类而非裸类。\n'
            '参考标准: PEP 557 dataclass / pylint R0905 变体'
        ),
        'dataclass-missing',
    )
_WRITE_SCOPE_CONTAINERS = (*SCOPE_CONTAINERS, ast.Lambda)
_NEWLINE_UNSET = '\x00'
_NEWLINE_UNKNOWN = object()
_OPEN_FILE_FIRST_MODULES = frozenset({
    'builtins', 'io', 'gzip', 'bz2', 'lzma',
})
_COMPRESSED_OPEN_MODULES = frozenset({'gzip', 'bz2', 'lzma'})
_OPEN_MODE_INDEX = 1
_OPEN_NEWLINE_INDEX = 5
_PATH_OPEN_MODE_INDEX = 0
_PATH_OPEN_NEWLINE_INDEX = 4
_OPEN_MODE_CHARS = frozenset('rwaxbt+')
def _looks_like_open_mode(value: str | None) -> bool:
    return bool(value) and all(ch in _OPEN_MODE_CHARS for ch in value)
def _open_call_layout(call: ast.Call) -> tuple[int, int] | None:
    func = call.func
    if isinstance(func, ast.Name):
        if func.id != 'open':
            return None
        return _OPEN_MODE_INDEX, _OPEN_NEWLINE_INDEX
    if not (isinstance(func, ast.Attribute) and func.attr == 'open'):
        return None
    receiver = func.value
    if (isinstance(receiver, ast.Name)
            and receiver.id in _OPEN_FILE_FIRST_MODULES):
        return _OPEN_MODE_INDEX, _OPEN_NEWLINE_INDEX
    positional_mode = str_constant_value(call.args[0]) if call.args else None
    if _looks_like_open_mode(positional_mode):
        return _PATH_OPEN_MODE_INDEX, _PATH_OPEN_NEWLINE_INDEX
    return _OPEN_MODE_INDEX, _OPEN_NEWLINE_INDEX
def _positional_open_mode(args: list[ast.expr], index: int
                          ) -> tuple[str | None, bool]:
    if any(isinstance(arg, ast.Starred) for arg in args):
        return None, True
    if len(args) > index:
        return str_constant_value(args[index]), True
    return 'r', False
def _open_mode(call: ast.Call, layout: tuple[int, int]) -> str | None:
    mode, positional_decided = _positional_open_mode(call.args, layout[0])
    if not positional_decided and any(kw.arg is None for kw in call.keywords):
        mode = None
    for kw in call.keywords:
        if kw.arg == 'mode':
            mode = str_constant_value(kw.value)
    func = call.func
    receiver = (func.value.id
                if isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Name) else None)
    if (receiver in _COMPRESSED_OPEN_MODULES and mode
            and _looks_like_open_mode(mode) and 't' not in mode):
        mode = mode if 'b' in mode else mode + 'b'
    return mode
def _positional_newline(args: list, index: int) -> str | object:
    if any(isinstance(a, ast.Starred) for a in args):
        return _NEWLINE_UNKNOWN
    if len(args) <= index:
        return _NEWLINE_UNSET
    arg = args[index]
    if isinstance(arg, ast.Constant) and arg.value is None:
        return _NEWLINE_UNSET
    positional = str_constant_value(arg)
    return positional if positional is not None else _NEWLINE_UNKNOWN
def _open_newline(call: ast.Call, layout: tuple[int, int]) -> str | object:
    newline = (_NEWLINE_UNKNOWN
               if any(kw.arg is None for kw in call.keywords)
               else _positional_newline(call.args, layout[1]))
    for kw in call.keywords:
        if kw.arg != 'newline':
            continue
        value = str_constant_value(kw.value)
        if value is not None:
            newline = value
        elif (isinstance(kw.value, ast.Constant)
                and kw.value.value is None):
            newline = _NEWLINE_UNSET
        else:
            newline = _NEWLINE_UNKNOWN
    return newline
def _is_write_mode(mode: str) -> bool:
    return any(flag in mode for flag in ('w', 'a', 'x', '+'))
def _newline_translates(newline: str) -> bool:
    if newline == _NEWLINE_UNSET:
        return os.linesep != '\n'
    return newline not in ('', '\n')
def _read_keeps_newline(mode: str, newline: str) -> bool:
    return ('r' in mode or '+' in mode) and newline == ''
def _nl01_call_evidence(
    node: ast.Call, layout: tuple[int, int],
) -> tuple[bool, tuple[int, int] | None]:
    mode = _open_mode(node, layout)
    if mode is None or 'b' in mode:
        return False, None
    newline = _open_newline(node, layout)
    if newline is _NEWLINE_UNKNOWN:
        return False, None
    read_evidence = _read_keeps_newline(mode, newline)
    write_position = None
    if _is_write_mode(mode) and _newline_translates(newline):
        write_position = (node.lineno, node.col_offset)
    return read_evidence, write_position
_NL01_READ_METHODS = frozenset({'read', 'readline', 'readlines'})
_NL01_WRITE_METHODS = frozenset({'write', 'writelines'})
_NL01_ITER_FUNCTIONS = frozenset({
    'list', 'tuple', 'set', 'frozenset', 'sorted',
})
_NL01_ITER_METHODS = frozenset({'join'})
_NL01_MUTATING_METHODS = frozenset({
    'append', 'extend', 'insert', 'add', 'update',
})
_NL01_COMP_NODES = (ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)
def _nl01_removes_carriage_returns(expr: ast.AST) -> bool:
    if not (isinstance(expr, ast.Call)
            and isinstance(expr.func, ast.Attribute)
            and expr.func.attr == 'replace'
            and len(expr.args) == 2 and not expr.keywords):
        return False
    old = str_constant_value(expr.args[0])
    new = str_constant_value(expr.args[1])
    return old == '\r' and new is not None and '\r' not in new

def _nl01_depends_on_read(expr: ast.AST, flow: _Nl01Flow) -> bool:
    for sub in walk_nodes(expr):
        if id(sub) in flow.source_ids:
            return True
        if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load):
            if any(evidence[1] for evidence in _nl01_open_evidence_at(
                    flow, sub.id, sub)):
                return True
            if _nl01_name_state_at(
                    flow.taint_events.get(sub.id, ()), expr, flow.parents):
                return True
        if (isinstance(sub, ast.Call)
                and isinstance(sub.func, ast.Attribute)
                and sub.func.attr in _NL01_READ_METHODS
                and isinstance(sub.func.value, ast.Name)
                and any(evidence[1] for evidence in _nl01_open_evidence_at(
                        flow, sub.func.value.id, sub))):
            return True
    return False
_Nl01OpenEvidence = tuple[ast.Call, bool, tuple[int, int] | None]
_Nl01OpenCalls = dict[int, _Nl01OpenEvidence]
_Nl01OpenEvents = dict[str, list[tuple[ast.AST, _Nl01OpenEvidence | None]]]
@dataclass
class _Nl01Flow:
    open_calls: _Nl01OpenCalls
    source_ids: set[int]
    open_events: _Nl01OpenEvents = field(default_factory=dict)
    taint_events: dict[str, list[tuple[ast.AST, bool]]] = field(
        default_factory=dict)
    cr_present_events: dict[str, list[tuple[ast.AST, bool]]] = field(
        default_factory=dict)
    parents: dict[int, ast.AST] = field(default_factory=dict)
    write_translate: set[tuple[int, int]] = field(default_factory=set)
def _nl01_name_state_at(
        events: list[tuple[ast.AST, bool]] | tuple,
        node: ast.AST, parents: dict[int, ast.AST]) -> bool:
    clears = [event for event, state in events if not state]
    for source, state in events:
        if not state or not _wm01_write_may_precede(source, node, parents):
            continue
        later_clears = [
            clear for clear in clears
            if (node_end_position(source) < node_end_position(clear)
                and _wm01_write_may_precede(clear, node, parents))
        ]
        if any(_wm01_write_dominates(
                clear, node, parents, later_clears)
               for clear in later_clears):
            continue
        return True
    return False

def _nl01_open_evidence_at(
        flow: _Nl01Flow, name: str, node: ast.AST,
) -> list[_Nl01OpenEvidence]:
    events = flow.open_events.get(name, ())
    active: list[_Nl01OpenEvidence] = []
    for event, evidence in events:
        if not _wm01_write_may_precede(event, node, flow.parents):
            continue
        later_events = [
            later for later, _evidence in events
            if (node_end_position(event) < node_end_position(later)
                and _wm01_write_may_precede(later, node, flow.parents))
        ]
        if any(_wm01_write_dominates(
                later, node, flow.parents, later_events)
               for later in later_events):
            continue
        if evidence is not None:
            active.append(evidence)
    return active

def _nl01_cr_free(expr: ast.AST, flow: _Nl01Flow) -> bool:
    if _nl01_removes_carriage_returns(expr):
        return True
    if not isinstance(expr, ast.Name):
        return False
    events = flow.cr_present_events.get(expr.id, ())
    return bool(events) and not _nl01_name_state_at(
        events, expr, flow.parents)
def _nl01_open_facts(
        nodes: list[ast.AST], parents: dict[int, ast.AST],
        shadow_cache: dict[tuple[int, frozenset[int]], set[str]],
) -> tuple[_Nl01OpenCalls, tuple[int, int] | None]:
    open_calls: _Nl01OpenCalls = {}
    read_positions: list[tuple[int, int]] = []
    for node in nodes:
        if not isinstance(node, ast.Call):
            continue
        layout = _open_call_layout(node)
        if layout is None:
            continue
        if (isinstance(node.func, ast.Name) and node.func.id == 'open'
                and shadowed_binding_at(node, 'open', parents, shadow_cache)):
            continue
        read_evidence, write_position = _nl01_call_evidence(node, layout)
        if not read_evidence and write_position is None:
            continue
        open_calls[id(node)] = (node, read_evidence, write_position)
        if read_evidence:
            read_positions.append((node.lineno, node.col_offset))
    return open_calls, min(read_positions, default=None)
def _nl01_is_read_open(expr: ast.AST, open_calls: _Nl01OpenCalls) -> bool:
    evidence = open_calls.get(id(expr))
    return evidence is not None and evidence[1]
def _nl01_direct_iter_source(
        node: ast.AST, open_calls: _Nl01OpenCalls,
) -> ast.AST | None:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return node.iter if _nl01_is_read_open(node.iter, open_calls) else None
    if not isinstance(node, ast.Call) or not node.args:
        return None
    func = node.func
    consumes_iter = (
        isinstance(func, ast.Name) and func.id in _NL01_ITER_FUNCTIONS
    ) or (
        isinstance(func, ast.Attribute) and func.attr in _NL01_ITER_METHODS
    )
    if consumes_iter and any(
            _nl01_is_read_open(arg, open_calls) for arg in node.args):
        return node
    return None
def _nl01_read_sources(
        nodes: list[ast.AST], open_calls: _Nl01OpenCalls) -> set[int]:
    source_ids: set[int] = set()
    for node in nodes:
        direct_source = _nl01_direct_iter_source(node, open_calls)
        if direct_source is not None:
            source_ids.add(id(direct_source))
        if (isinstance(node, _NL01_COMP_NODES)
                and any(id(sub) in open_calls and open_calls[id(sub)][1]
                        for gen in node.generators
                        for sub in walk_nodes(gen.iter))):
            source_ids.add(id(node))
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr in _NL01_READ_METHODS):
            continue
        if any(id(sub) in open_calls and open_calls[id(sub)][1]
               for sub in walk_nodes(node.func.value)):
            source_ids.add(id(node))
    return source_ids
def _nl01_bind_name(
        flow: _Nl01Flow, event: ast.AST, name: str, depends: bool,
        direct_opens: list[_Nl01OpenEvidence] | None = None,
        *, cr_free: bool = False,
) -> None:
    flow.taint_events.setdefault(name, []).append((event, depends))
    flow.cr_present_events.setdefault(name, []).append((event, not cr_free))
    events = flow.open_events.setdefault(name, [])
    if direct_opens:
        events.extend((event, evidence) for evidence in direct_opens)
    else:
        events.append((event, None))
def _nl01_value_open_evidences(
        flow: _Nl01Flow, value: ast.AST,
) -> list[_Nl01OpenEvidence]:
    direct_open = flow.open_calls.get(id(value))
    if direct_open is not None:
        return [direct_open]
    if isinstance(value, ast.Name):
        return _nl01_open_evidence_at(flow, value.id, value)
    return []
def _nl01_unpacks_whole(targets: list[ast.AST], value: ast.AST) -> bool:
    if len(targets) != 1:
        return False
    target = targets[0]
    if not isinstance(target, (ast.Tuple, ast.List)):
        return False
    if not isinstance(value, (ast.Tuple, ast.List)):
        return True
    if len(value.elts) != len(target.elts):
        return True
    return any(isinstance(elt, ast.Starred)
               for elt in (*target.elts, *value.elts))
def _nl01_apply_binding(node: ast.AST, flow: _Nl01Flow) -> None:
    if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
        name = node.target.id
        depends = (_nl01_name_state_at(
                       flow.taint_events.get(name, ()), node.target,
                       flow.parents)
                   or _nl01_depends_on_read(node.value, flow))
        _nl01_bind_name(flow, node.target, name, depends)
        return
    targets: list[ast.AST] | None = None
    value: ast.AST | None = None
    if isinstance(node, ast.Assign):
        targets, value = list(node.targets), node.value
    elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)):
        targets, value = [node.target], node.value
    if targets is not None:
        if value is not None:
            if _nl01_unpacks_whole(targets, value):
                depends = _nl01_depends_on_read(value, flow)
                cr_free = _nl01_cr_free(value, flow)
                direct_opens = _nl01_value_open_evidences(flow, value)
                for target in targets:
                    for name in target_binding_names(target):
                        _nl01_bind_name(
                            flow, target, name, depends, direct_opens,
                            cr_free=cr_free)
            else:
                for target, sub_value in iter_write_targets(node):
                    depends = (sub_value is not None
                               and _nl01_depends_on_read(sub_value, flow))
                    cr_free = (sub_value is not None
                               and _nl01_cr_free(sub_value, flow))
                    direct_opens = (
                        _nl01_value_open_evidences(flow, sub_value)
                        if sub_value is not None else [])
                    for name in target_binding_names(target):
                        _nl01_bind_name(
                            flow, target, name, depends, direct_opens,
                            cr_free=cr_free)
        return
    if isinstance(node, (ast.For, ast.AsyncFor)):
        depends = _nl01_depends_on_read(node.iter, flow)
        for name in target_binding_names(node.target):
            _nl01_bind_name(flow, node.target, name, depends)
        return
    if isinstance(node, (ast.With, ast.AsyncWith)):
        for item in node.items:
            target = item.optional_vars
            if target is None:
                continue
            direct_opens = _nl01_value_open_evidences(
                flow, item.context_expr)
            for name in target_binding_names(target):
                _nl01_bind_name(flow, target, name, False, direct_opens)
        return
    for name in rebound_binding_names(node):
        _nl01_bind_name(flow, node, name, False)
def _nl01_apply_container_mutation(node: ast.AST, flow: _Nl01Flow) -> None:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and isinstance(node.func.value, ast.Name)):
        return
    name = node.func.value.id
    if node.func.attr == 'clear':
        flow.taint_events.setdefault(name, []).append((node, False))
        return
    if node.func.attr not in _NL01_MUTATING_METHODS:
        return
    values = [*node.args, *(kw.value for kw in node.keywords)]
    if any(_nl01_depends_on_read(value, flow) for value in values):
        flow.taint_events.setdefault(name, []).append((node, True))
def _nl01_collect_write(
        node: ast.AST, first_read: tuple[int, int], flow: _Nl01Flow) -> None:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _NL01_WRITE_METHODS and node.args):
        return
    receiver = node.func.value
    if isinstance(receiver, ast.Name):
        evidences = _nl01_open_evidence_at(flow, receiver.id, node)
    elif isinstance(receiver, ast.Call):
        evidence = flow.open_calls.get(id(receiver))
        evidences = [evidence] if evidence is not None else []
    else:
        return
    write_op_position = (node.lineno, node.col_offset)
    argument = node.args[0]
    depends = not _nl01_cr_free(argument, flow) and (
        _nl01_depends_on_read(argument, flow)
        or any(_nl01_is_read_open(arg, flow.open_calls)
               for arg in node.args)
    )
    read_in_args = any(
        id(sub) in flow.open_calls and flow.open_calls[id(sub)][1]
        for arg in node.args
        for sub in walk_nodes(arg))
    for _open_call, _read_evidence, write_position in evidences:
        if (write_position is not None
                and (write_op_position > first_read or read_in_args) and depends):
            flow.write_translate.add(write_position)
def _nl01_flow_position(node: ast.AST) -> tuple[int, int]:
    if isinstance(node, (ast.With, ast.AsyncWith, ast.For, ast.AsyncFor)):
        return binding_body_start(node)
    return node_end_position(node)
def _nl01_scan_scope(
    container: ast.AST,
    parents: dict[int, ast.AST],
    shadow_cache: dict[tuple[int, frozenset[int]], set[str]],
) -> tuple[tuple[int, int] | None, list[tuple[int, int]]]:
    nodes = iter_direct_scope(container)
    open_calls, first_read = _nl01_open_facts(nodes, parents, shadow_cache)
    if first_read is None:
        return None, []
    flow = _Nl01Flow(
        open_calls=open_calls,
        source_ids=_nl01_read_sources(nodes, open_calls),
        parents=parents)
    for node in sorted(nodes, key=_nl01_flow_position):
        _nl01_apply_binding(node, flow)
        _nl01_apply_container_mutation(node, flow)
        _nl01_collect_write(node, first_read, flow)
    return first_read, sorted(flow.write_translate)
def _nl01_issue(wline: int, filepath: Any, src_lines: list[str]) -> dict[str, Any]:
    return make_issue(
        'NL-01', 'P1', 'io_safety', filepath, wline,
        "open 读写 newline 语义不匹配：写侧非空 newline 将对已保留的 \\r\\n 二次转换",
        (
            "同作用域内读侧 newline=''（保留原换行 \\r\\n）与写侧 "
            "newline='\\r\\n'（写入时对每个 \\n 转换）并存——读入内容"
            "已含 \\r\\n，写出时被再次转换成 \\r\\r\\n，整文件换行"
            "破坏，py_compile 报超出行数 SyntaxError。"
        ),
        snippet_of(src_lines, wline),
        (
            '根因：读写两侧 newline 参数语义不一致导致双重转换。\n'
            "修复策略：读写统一 newline=''（原样保留），或两侧都"
            '不传（universal newline 统一转换）；需要精确控制时用'
            "二进制模式 rb/wb。切勿读 newline='' 而写 '\\r\\n'。\n"
            '参考标准: Python open() newline 参数文档'
        ),
        'newline-mismatch',
    )
def check_NL01(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[dict[str, Any]] = []
    if not isinstance(tree, ast.AST):
        return issues
    src_lines = source_lines(source)
    parents = build_parent_map(tree)
    shadow_cache: dict[tuple[int, frozenset[int]], set[str]] = {}
    for container in walk_nodes(tree):
        if not isinstance(container, _WRITE_SCOPE_CONTAINERS):
            continue
        read_position, write_translate = _nl01_scan_scope(
            container, parents, shadow_cache)
        if read_position is None or not write_translate:
            continue
        issues.extend(
            _nl01_issue(wpos[0], filepath, src_lines)
            for wpos in write_translate)
    _log_detector_findings("NL-01", " open() newline 双转换", issues, filepath)
    return issues
def _ef01_return_branches(value: ast.AST | None) -> tuple[bool, bool]:
    has_value = False
    has_none = False
    stack: list[ast.AST | None] = [value]
    while stack:
        cur = stack.pop()
        if cur is None or (isinstance(cur, ast.Constant)
                           and cur.value is None):
            has_none = True
        elif isinstance(cur, ast.IfExp):
            stack.append(cur.body)
            stack.append(cur.orelse)
        else:
            has_value = True
    return has_value, has_none
def _ef01_is_generator(scope: ast.AST) -> bool:
    return any(
        isinstance(sub, (ast.Yield, ast.YieldFrom))
        for stmt in scope_body_stmts(scope)
        for sub in iter_nodes_outside(stmt))
def _ef01_scope_returns_both(scope: ast.AST) -> bool:
    has_value = False
    has_none = False
    for sub in _contract_return_nodes(
            iter_direct_scope(scope), include_none=True):
        branch_value, branch_none = _ef01_return_branches(sub.value)
        has_value = has_value or branch_value
        has_none = has_none or branch_none
    return has_value and has_none
def _ef01_collect_optional_fns(
        tree: ast.AST,
) -> dict[str, list[ast.FunctionDef | ast.AsyncFunctionDef]]:
    optional_fns: dict[
        str, list[ast.FunctionDef | ast.AsyncFunctionDef]] = {}
    ambiguous: set[str] = set()
    method_scopes = _method_scope_names(tree)
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        fname = node.name
        if id(node) in method_scopes:
            continue
        if _ef01_is_generator(node):
            ambiguous.add(fname)
            continue
        if _ef01_scope_returns_both(node):
            optional_fns.setdefault(fname, []).append(node)
        else:
            ambiguous.add(fname)
    return {fname: defs for fname, defs in optional_fns.items()
            if fname not in ambiguous}
def _ef01_is_broad_handler(handler: ast.ExceptHandler) -> bool:
    if is_broad_except(handler):
        return True
    return 'AttributeError' in handler_exc_names(handler)
def _ef01_handler_raises(handler: ast.ExceptHandler) -> bool:
    return any(
        isinstance(sub, ast.Raise)
        for stmt in handler.body
        for sub in iter_nodes_outside(stmt))
def _ef01_handles_attribute_error(node: ast.AST) -> bool:
    for handler in node.handlers:
        if _ef01_is_broad_handler(handler):
            return not _ef01_handler_raises(handler)
    return False
def _ef01_guarded_ranges(nodes: list[ast.AST]) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    for node in nodes:
        if not isinstance(node, (ast.Try, getattr(ast, "TryStar", ast.Try))):
            continue
        if _ef01_handles_attribute_error(node):
            ranges.append(_ef01_try_span(node))
    return ranges
def _ef01_try_span(node: ast.AST) -> tuple[int, int]:
    body = getattr(node, 'body', None) or ()
    if not body:
        return (node.lineno, node.lineno)
    return (body[0].lineno,
            getattr(body[-1], 'end_lineno', body[-1].lineno) or body[-1].lineno)
def _ef01_guard_name(expr: ast.AST) -> str | None:
    if isinstance(expr, ast.NamedExpr):
        expr = expr.target
    return expr.id if isinstance(expr, ast.Name) else None
_EF01_TRUTHY_PREDICATES = frozenset({
    'isinstance', 'issubclass', 'callable', 'hasattr', 'bool',
})
def _ef01_classinfo_allows_none(node: ast.AST) -> bool:
    if is_none_constant(node):
        return True
    if isinstance(node, ast.Tuple):
        return any(_ef01_classinfo_allows_none(elt) for elt in node.elts)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return (_ef01_classinfo_allows_none(node.left)
                or _ef01_classinfo_allows_none(node.right))
    if isinstance(node, ast.Subscript):
        head = node.value
        name = (head.id if isinstance(head, ast.Name)
                else head.attr if isinstance(head, ast.Attribute) else None)
        if name == 'Optional':
            return True
        if name == 'Union':
            return _ef01_classinfo_allows_none(node.slice)
    if isinstance(node, ast.Name):
        return node.id == 'NoneType'
    if isinstance(node, ast.Attribute):
        return node.attr == 'NoneType'
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name) and node.func.id == 'type'
            and len(node.args) == 1 and not node.keywords
            and is_none_constant(node.args[0]))
def _ef01_narrow_call(test: ast.Call, truth: bool) -> set[str]:
    if not truth:
        return set()
    if not (isinstance(test.func, ast.Name)
            and test.func.id in _EF01_TRUTHY_PREDICATES and test.args):
        return set()
    if test.func.id == 'hasattr':
        attr_name = (str_constant_value(test.args[1])
                     if len(test.args) == 2 and not test.keywords else None)
        if attr_name is None or hasattr(None, attr_name):
            return set()
    if (test.func.id == 'isinstance' and len(test.args) >= 2
            and _ef01_classinfo_allows_none(test.args[1])):
        return set()
    return _ef01_narrow_names(test.args[0], True)
def _ef01_narrow_boolop(test: ast.BoolOp, truth: bool) -> set[str]:
    if isinstance(test.op, ast.And) and truth:
        names: set[str] = set()
        for value in test.values:
            names |= _ef01_narrow_names(value, True)
        return names
    if isinstance(test.op, ast.Or) and not truth:
        names = set()
        for value in test.values:
            names |= _ef01_narrow_names(value, False)
        return names
    return set()
def _ef01_narrow_compare(test: ast.Compare, truth: bool) -> set[str]:
    left, right = test.left, test.comparators[0]
    left_name = _ef01_guard_name(left)
    right_name = _ef01_guard_name(right)
    if left_name and is_none_constant(right):
        name, op = left_name, test.ops[0]
    elif right_name and is_none_constant(left):
        name, op = right_name, test.ops[0]
    else:
        return set()
    if isinstance(op, (ast.IsNot, ast.NotEq)):
        return {name} if truth else set()
    if isinstance(op, (ast.Is, ast.Eq)):
        return set() if truth else {name}
    return set()
def _ef01_narrow_names(test: ast.AST, truth: bool) -> set[str]:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _ef01_narrow_names(test.operand, not truth)
    if isinstance(test, ast.NamedExpr):
        return _ef01_narrow_names(test.target, truth)
    if isinstance(test, ast.Call):
        return _ef01_narrow_call(test, truth)
    if isinstance(test, ast.BoolOp):
        return _ef01_narrow_boolop(test, truth)
    if isinstance(test, ast.Compare):
        return (_ef01_narrow_compare(test, truth)
                if len(test.ops) == 1 else set())
    return {test.id} if isinstance(test, ast.Name) and truth else set()
def _ef01_checked_vars(nodes: list[ast.AST]) -> dict[str, list[ast.AST]]:
    checked: dict[str, list[ast.AST]] = {}
    for node in nodes:
        if isinstance(node, ast.Assert):
            names = _ef01_narrow_names(node.test, True)
            guard = node
        elif isinstance(node, ast.If):
            if block_exits(node.body):
                names = _ef01_narrow_names(node.test, False)
            elif block_exits(node.orelse):
                names = _ef01_narrow_names(node.test, True)
            else:
                continue
            guard = node
        else:
            continue
        for name in names:
            checked.setdefault(name, []).append(guard)
    return checked
@dataclass(frozen=True)
class _Ef01Scan:
    optional_fns: set[str]
    guarded: list[tuple[int, int]]
    checked_vars: dict[str, list[ast.AST]]
    issues: list[dict[str, Any]]
    filepath: Any
    src_lines: list[str]
    parents: dict[int, ast.AST]
    seen: set[int]
    shadowed_fns: frozenset[str] = frozenset()
class _Ef01Resolver:
    def __init__(
            self, nodes: list[ast.AST],
            optional_fn_defs: dict[
                str, list[ast.FunctionDef | ast.AsyncFunctionDef]],
            parents: dict[int, ast.AST]) -> None:
        self._optional_fn_defs = optional_fn_defs
        self._parents = parents
        self._flow = flow_var_resolver(
            nodes, set(optional_fn_defs), name_only=True)
        self._binding_calls: dict[tuple[str, int], list[ast.Call]] = {}
        for node in nodes:
            if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
                continue
            for _target, value in iter_write_targets(node):
                if value is None:
                    continue
                value = _unwrap_await(value)
                if not (isinstance(value, ast.Call)
                        and isinstance(value.func, ast.Name)
                        and value.func.id in optional_fn_defs):
                    continue
                self._binding_calls.setdefault(
                    (value.func.id, node.lineno), []).append(value)
    def is_optional_call(self, call: ast.Call) -> bool:
        if not isinstance(call.func, ast.Name):
            return False
        return any(
            _call_resolves_to_definition(call, definition, self._parents)
            for definition in self._optional_fn_defs.get(call.func.id, ()))
    def resolve(self, name: str, lineno: int,
                col_offset: int = 0) -> tuple[str, int] | None:
        hit = self._flow.resolve(name, lineno, col_offset)
        if hit is None:
            return None
        calls = self._binding_calls.get(hit, ())
        return hit if any(self.is_optional_call(call) for call in calls) else None
_EF01_BRANCH_GUARD_NODES = (ast.If, ast.While, ast.IfExp, ast.Assert)
def _ef01_short_circuit_guarded(sub: ast.AST, base_id: str,
                                parents: dict[int, ast.AST]) -> bool:
    cur = sub
    while id(cur) in parents:
        parent = parents[id(cur)]
        if isinstance(parent, ast.BoolOp):
            idx = next((i for i, v in enumerate(parent.values) if v is cur), None)
            if idx is not None:
                if isinstance(parent.op, ast.And):
                    prior = any(base_id in _ef01_narrow_names(prev, True)
                                for prev in parent.values[:idx])
                else:
                    prior = any(base_id in _ef01_narrow_names(prev, False)
                                for prev in parent.values[:idx])
                if prior:
                    return True
            cur = parent
            continue
        if isinstance(parent, _EF01_BRANCH_GUARD_NODES):
            truth = branch_truth(parent, cur)
            if (truth is not None
                    and base_id in _ef01_narrow_names(parent.test, truth)):
                return True
            cur = parent
            continue
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.ClassDef, ast.Module, ast.Lambda)):
            return False
        cur = parent
    return False
def _ef01_report(fname: str, how: str, lineno: int, site: ast.AST,
                 scan: _Ef01Scan) -> None:
    site_id = id(site)
    if site_id in scan.seen:
        return
    scan.seen.add(site_id)
    scan.issues.append(make_issue(
        'EF-01', 'P1', 'robustness', scan.filepath, lineno,
        f"Optional 函数 {fname}() 的 None 分支将被属性访问击穿",
        (
            f'{fname}() 同时存在值返回与 None 返回（空壳降级模式），但调用方'
            f'（{how}）未做 None 判断——降级分支触发 AttributeError 崩溃。'
            f'可选依赖 fallback 返回 None 而非有效结果对象是 P0 级实例化'
            f'崩溃的高频形态。'
        ),
        snippet_of(scan.src_lines, lineno),
        (
            '根因：降级路径返回 None 但消费端无判空。\n'
            '修复策略：①fallback 返回有效空对象（Null Object 模式）而非'
            'None；②调用方加 if result is None 分支处理；③函数签名标 '
            'Optional[T] 并在消费点强制 narrow。\n'
            '参考标准: Optional 返回值未经收窄即消费的缺陷模式'
        ),
        'empty-shell-fallback',
    ))
def _ef01_in_guard(guarded: list[tuple[int, int]], lineno: int) -> bool:
    return any(lo <= lineno <= hi for lo, hi in guarded)
def _ef01_within(node: ast.AST, ancestor: ast.AST,
                 parents: dict[int, ast.AST]) -> bool:
    cur: ast.AST | None = node
    while cur is not None:
        if cur is ancestor:
            return True
        cur = parents.get(id(cur))
    return False
def _ef01_guard_precedes(guard: ast.AST, node: ast.AST,
                         parents: dict[int, ast.AST]) -> bool:
    cur: ast.AST = node
    while True:
        parent = parents.get(id(cur))
        if parent is None:
            return False
        siblings = stmt_siblings(parent, cur)
        if siblings is not None:
            guard_idx = cur_idx = -1
            for idx, stmt in enumerate(siblings):
                if stmt is guard:
                    guard_idx = idx
                if stmt is cur:
                    cur_idx = idx
            if guard_idx >= 0:
                return 0 <= guard_idx < cur_idx
        cur = parent
def _ef01_guard_allows(guard: ast.AST, node: ast.AST,
                       parents: dict[int, ast.AST]) -> bool:
    if not _ef01_within(node, guard, parents):
        return _ef01_guard_precedes(guard, node, parents)
    if not isinstance(guard, ast.If):
        return False
    in_body = any(_ef01_within(node, stmt, parents) for stmt in guard.body)
    in_orelse = any(_ef01_within(node, stmt, parents) for stmt in guard.orelse)
    if block_exits(guard.body):
        return in_orelse
    return in_body
def _ef01_null_checked(checked_vars: dict[str, list[ast.AST]], var: str,
                       node: ast.AST, bind_line: int,
                       parents: dict[int, ast.AST]) -> bool:
    return any(bind_line <= getattr(guard, 'lineno', 0) <= node.lineno
               and _ef01_guard_allows(guard, node, parents)
               for guard in checked_vars.get(var, ()))
def _ef01_call_consumption(
        sub: ast.Attribute, call: ast.Call, fname: str | None,
        shadow: frozenset[str], resolver: _Ef01Resolver,
        scan: _Ef01Scan) -> None:
    if fname not in scan.optional_fns or fname in scan.shadowed_fns:
        return
    if shadow and fname in shadow:
        return
    if not resolver.is_optional_call(call):
        return
    if _ef01_in_guard(scan.guarded, sub.lineno):
        return
    _ef01_report(fname, f'{fname}(...) 返回值直接链式 .{sub.attr}',
                 sub.lineno, sub, scan)
def _ef01_var_consumption(sub: ast.Attribute, base_id: str,
                          hit: tuple[str, int] | None,
                          scan: _Ef01Scan) -> None:
    if hit is None or hit[0] in scan.shadowed_fns:
        return
    if sub.lineno < hit[1]:
        return
    if _ef01_null_checked(scan.checked_vars, base_id, sub, hit[1],
                          scan.parents):
        return
    if _ef01_short_circuit_guarded(sub, base_id, scan.parents):
        return
    if _ef01_in_guard(scan.guarded, sub.lineno):
        return
    _ef01_report(hit[0],
                 f'变量 {base_id}（{hit[0]}() 返回值）未判空'
                 f'直接 .{sub.attr}',
                 sub.lineno, sub, scan)
def _ef01_consume_attribute(sub: ast.Attribute, shadow: frozenset[str],
                            resolver: Any, scan: _Ef01Scan) -> None:
    base = _unwrap_await(sub.value)
    if isinstance(base, ast.Call):
        fname = base.func.id if isinstance(base.func, ast.Name) else None
        _ef01_call_consumption(
            sub, base, fname, shadow, resolver, scan)
        return
    if isinstance(base, ast.Name) and base.id not in shadow:
        hit = resolver.resolve(base.id, sub.lineno, sub.col_offset)
        _ef01_var_consumption(sub, base.id, hit, scan)
def _ef01_shadowed_fns(container: ast.AST,
                       optional_fns: set[str]) -> frozenset[str]:
    if not isinstance(container, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef, ast.Lambda)):
        return frozenset()
    own = getattr(container, 'name', None)
    return frozenset((scope_local_bindings(container) & optional_fns) - {own})
def _ef01_consume(body: list[ast.AST], resolver: Any,
                  scan: _Ef01Scan) -> None:
    def _visit(sub: ast.AST, shadow: frozenset[str]) -> None:
        if isinstance(sub, ast.Attribute):
            _ef01_consume_attribute(sub, shadow, resolver, scan)
    walk_scope_expr(body, _visit)
def check_EF01(tree: ast.AST | None, source: Any,
               filepath: str) -> list[dict[str, Any]]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[dict[str, Any]] = []
    if not isinstance(tree, ast.AST):
        return issues
    src_lines = source_lines(source)
    optional_fn_defs = _ef01_collect_optional_fns(tree)
    optional_fns = set(optional_fn_defs)
    if not optional_fns:
        return issues
    parents = build_parent_map(tree)
    seen: set[int] = set()
    for container in tree_nodes(tree):
        if not isinstance(container, _WRITE_SCOPE_CONTAINERS):
            continue
        nodes = iter_direct_scope(container)
        resolver = _Ef01Resolver(nodes, optional_fn_defs, parents)
        scan = _Ef01Scan(
            optional_fns=optional_fns,
            guarded=_ef01_guarded_ranges(nodes),
            checked_vars=_ef01_checked_vars(nodes),
            issues=issues, filepath=filepath, src_lines=src_lines,
            parents=parents, seen=seen,
            shadowed_fns=_ef01_shadowed_fns(container, optional_fns),
        )
        _ef01_consume(scope_body_stmts(container), resolver, scan)
    _log_detector_findings("EF-01", " Optional None 分支击穿", issues, filepath)
    return issues
def _scope_children_of(node: ast.AST) -> list[ast.AST]:
    children: list[ast.AST] = []
    for child in ast.iter_child_nodes(node):
        if isinstance(child, FUNC_SCOPE_NODES):
            continue
        if isinstance(child, ast.comprehension):
            children.append(child.iter)
            children.extend(child.ifs or [])
            continue
        children.append(child)
    return children
def iter_direct_scope(container: ast.AST) -> list[ast.AST]:
    out: list[ast.AST] = []
    queue: deque[ast.AST] = deque(scope_body_stmts(container))
    while queue:
        node = queue.popleft()
        out.append(node)
        if isinstance(node, FUNC_SCOPE_NODES):
            continue
        queue.extend(_scope_children_of(node))
    out.sort(key=lambda n: (getattr(n, 'lineno', 0), getattr(n, 'col_offset', 0)))
    return out
def _is_none_return(value: ast.AST | None) -> bool:
    return value is None or is_none_constant(value)
def _literal_dict_str_key(key: ast.AST | None) -> str | None:
    if isinstance(key, ast.Constant) and isinstance(key.value, str):
        return key.value
    return None
def _is_leaf_value(value: ast.AST | None) -> bool:
    return isinstance(value, (ast.Constant, ast.List, ast.Set, ast.Tuple,
                              ast.JoinedStr, ast.ListComp, ast.SetComp,
                              ast.GeneratorExp))
class _LiteralDictPaths(NamedTuple):
    keys: set[tuple[str, ...]]
    opaque: set[tuple[str, ...]]
def _merge_literal_dict_child(
        key: str, value: ast.AST,
        keys: set[tuple[str, ...]],
        opaque: set[tuple[str, ...]]) -> bool:
    if not isinstance(value, ast.Dict):
        if not _is_leaf_value(value):
            opaque.add((key,))
        return True
    sub = _literal_dict_paths(value)
    if sub is None:
        return False
    keys.update((key,) + sp for sp in sub.keys)
    opaque.update((key,) + sp for sp in sub.opaque)
    return True
def _literal_dict_paths(node: ast.AST) -> _LiteralDictPaths | None:
    if not isinstance(node, ast.Dict):
        return None
    keys: set[tuple[str, ...]] = set()
    opaque: set[tuple[str, ...]] = set()
    for k, v in zip(node.keys, node.values, strict=True):
        key = _literal_dict_str_key(k)
        if key is None:
            return None
        keys.difference_update(
            path for path in tuple(keys) if path[:1] == (key,))
        opaque.difference_update(
            path for path in tuple(opaque) if path[:1] == (key,))
        keys.add((key,))
        if not _merge_literal_dict_child(key, v, keys, opaque):
            return None
    return _LiteralDictPaths(keys, opaque)
def augmented_key_paths_and_opaque(
        value: ast.AST,
        var_literals: dict[str, set[tuple[str, ...]]],
        var_assigned: dict[str, int],
        var_opaque: dict[str, set[tuple[str, ...]]],
) -> _LiteralDictPaths | None:
    got = _literal_dict_paths(value)
    if got is not None:
        return got
    if (isinstance(value, ast.Name)
            and var_assigned.get(value.id, 0) > 0
            and value.id in var_literals):
        return _LiteralDictPaths(
            set(var_literals[value.id]),
            set(var_opaque.get(value.id, ())))
    return None
def _is_get_key_call(expr: ast.AST) -> bool:
    return (isinstance(expr, ast.Call)
            and isinstance(expr.func, ast.Attribute)
            and expr.func.attr == 'get'
            and bool(expr.args)
            and isinstance(expr.args[0], ast.Constant)
            and isinstance(expr.args[0].value, str))
def _is_subscript_key(expr: ast.AST) -> bool:
    return (isinstance(expr, ast.Subscript)
            and isinstance(expr.slice, ast.Constant)
            and isinstance(expr.slice.value, str))
def key_path_of(expr: ast.AST) -> tuple[ast.AST, tuple[str, ...]] | None:
    path: list[str] = []
    cur = expr
    while True:
        if _is_get_key_call(cur):
            path.append(cur.args[0].value)
            cur = cur.func.value
            continue
        if isinstance(cur, ast.Attribute):
            path.append(cur.attr)
            cur = cur.value
            continue
        if _is_subscript_key(cur):
            path.append(cur.slice.value)
            cur = cur.value
            continue
        break
    if not path:
        return None
    return cur, tuple(reversed(path))
def subscript_target_chain(target: ast.AST) -> tuple[str, tuple[str, ...]] | None:
    if not isinstance(target, ast.Subscript):
        return None
    keys: list[str] = []
    cur: ast.AST = target
    while isinstance(cur, ast.Subscript):
        sl = cur.slice
        if not (isinstance(sl, ast.Constant) and isinstance(sl.value, str)):
            return None
        keys.append(sl.value)
        cur = cur.value
    if not isinstance(cur, ast.Name):
        return None
    return cur.id, tuple(reversed(keys))
def iter_write_targets(
        node: ast.AST,
) -> list[tuple[ast.AST, ast.AST | None]]:
    if isinstance(node, ast.Assign):
        out: list[tuple[ast.AST, ast.AST | None]] = []
        for t in node.targets:
            out.extend(_expand_write_target(t, node.value))
        return out
    if isinstance(node, ast.AnnAssign) and node.value is not None:
        return [(node.target, node.value)]
    if isinstance(node, ast.NamedExpr):
        return [(node.target, node.value)]
    return []
def _expand_write_target(
        target: ast.AST,
        value: ast.AST | None,
) -> list[tuple[ast.AST, ast.AST | None]]:
    if isinstance(target, (ast.Tuple, ast.List)):
        _vals: tuple[ast.AST, ...] = ()
        if (isinstance(value, (ast.Tuple, ast.List))
                and len(value.elts) == len(target.elts)
                and not any(isinstance(e, ast.Starred)
                            for e in (*value.elts, *target.elts))):
            _vals = tuple(value.elts)
        out: list[tuple[ast.AST, ast.AST | None]] = []
        for i, el in enumerate(target.elts):
            out.extend(_expand_write_target(
                el, _vals[i] if i < len(_vals) else None))
        return out
    return [(target, value)]
def _poison_literal_var(
        var: str, var_assigned: dict[str, int],
        var_literals: dict[str, set[tuple[str, ...]]],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> None:
    var_assigned[var] = -1
    var_literals.pop(var, None)
    var_opaque.pop(var, None)
def _record_literal_assignment(
        var: str, val: ast.AST | None, count: int,
        var_assigned: dict[str, int],
        var_literals: dict[str, set[tuple[str, ...]]],
        var_opaque: dict[str, set[tuple[str, ...]]], *,
        replace: bool = False) -> None:
    got = _literal_dict_paths(val)
    if got is None:
        _poison_literal_var(var, var_assigned, var_literals, var_opaque)
        return
    var_assigned[var] = count + 1
    if replace:
        var_literals[var] = set(got.keys)
        var_opaque[var] = set(got.opaque)
        return
    var_literals.setdefault(var, set()).update(got.keys)
    var_opaque.setdefault(var, set()).update(got.opaque)
def _poison_rebound_names(
        nodes: list[ast.AST],
        var_assigned: dict[str, int],
        var_literals: dict[str, set[tuple[str, ...]]],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> None:
    seen: set[int] = set()
    pending = list(nodes)
    while pending:
        node = pending.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        names = rebound_binding_names(node)
        if (isinstance(node, (ast.Import, ast.ImportFrom))
                and import_bound_names(node)[1]):
            names |= set(var_assigned)
        for name in names:
            _poison_literal_var(name, var_assigned, var_literals, var_opaque)
        if isinstance(node, FUNC_SCOPE_NODES):
            continue
        pending.extend(_scope_children_of(node))
def local_literal_tables(
        nodes: list[ast.AST],
) -> tuple[dict[str, int], dict[str, set[tuple[str, ...]]],
           dict[str, set[tuple[str, ...]]]]:
    var_assigned: dict[str, int] = {}
    var_literals: dict[str, set[tuple[str, ...]]] = {}
    var_opaque: dict[str, set[tuple[str, ...]]] = {}
    nested_nodes = {
        id(child) for node in nodes for child in ast.iter_child_nodes(node)}
    for node in nodes:
        replace = (isinstance(node, (ast.Assign, ast.AnnAssign))
                   and id(node) not in nested_nodes)
        for tgt, val in iter_write_targets(node):
            if not isinstance(tgt, ast.Name):
                continue
            count = var_assigned.get(tgt.id, 0)
            if count < 0:
                continue
            _record_literal_assignment(
                tgt.id, val, count, var_assigned, var_literals, var_opaque,
                replace=replace)
    _poison_rebound_names(nodes, var_assigned, var_literals, var_opaque)
    return var_assigned, var_literals, var_opaque
def _poison_dynamic_key_target(
        target: ast.Subscript,
        var_literals: dict[str, set[tuple[str, ...]]],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> None:
    base = _shared_subscript_base_name(target)
    if base is not None:
        var_literals.pop(base, None)
        var_opaque.pop(base, None)
def _resolve_subscript_chain(
        target: ast.AST,
        var_literals: dict[str, set[tuple[str, ...]]],
        var_opaque: dict[str, set[tuple[str, ...]]],
) -> tuple[str, tuple[str, ...]] | None:
    chain = subscript_target_chain(target)
    if chain is None:
        if isinstance(target, ast.Subscript):
            _poison_dynamic_key_target(target, var_literals, var_opaque)
        return None
    return chain if chain[0] in var_literals else None
def _invalidate_literal_path_prefix(
        base: str, prefix: tuple[str, ...],
        var_literals: dict[str, set[tuple[str, ...]]],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> None:
    for table in (var_literals, var_opaque):
        paths = table.get(base)
        if paths is None:
            continue
        paths.difference_update(
            path for path in tuple(paths)
            if path[:len(prefix)] == prefix)


def _apply_subscript_writes(
        sub: ast.AST,
        var_literals: dict[str, set[tuple[str, ...]]],
        var_assigned: dict[str, int],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> None:
    for tgt, val in iter_write_targets(sub):
        chain = _resolve_subscript_chain(tgt, var_literals, var_opaque)
        if chain is None:
            continue
        base, keys = chain
        _invalidate_literal_path_prefix(
            base, keys, var_literals, var_opaque)
        var_literals[base].update(
            keys[:i + 1] for i in range(len(keys)))
        nested = augmented_key_paths_and_opaque(
            val, var_literals, var_assigned, var_opaque)
        if nested is not None:
            var_literals[base].update(keys + sp for sp in nested.keys)
            var_opaque.setdefault(base, set()).update(
                keys + sp for sp in nested.opaque)
        elif not _is_leaf_value(val):
            var_opaque.setdefault(base, set()).add(keys)
def _apply_augassign(
        sub: ast.AST,
        var_literals: dict[str, set[tuple[str, ...]]],
        var_assigned: dict[str, int],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> None:
    if not (isinstance(sub, ast.AugAssign) and isinstance(sub.op, ast.BitOr)):
        return
    if isinstance(sub.target, ast.Name):
        if sub.target.id not in var_literals:
            return
        base, keys = sub.target.id, ()
    else:
        chain = _resolve_subscript_chain(
            sub.target, var_literals, var_opaque)
        if chain is None:
            return
        base, keys = chain
    got = augmented_key_paths_and_opaque(
        sub.value, var_literals, var_assigned, var_opaque)
    if got is None:
        _invalidate_literal_path_prefix(
            base, keys, var_literals, var_opaque)
    else:
        for path in got.keys:
            if len(path) == 1:
                _invalidate_literal_path_prefix(
                    base, keys + path, var_literals, var_opaque)
    if keys:
        var_literals[base].add(keys)
    if got is None:
        var_opaque.setdefault(base, set()).add(keys)
        return
    var_literals[base].update(keys + sp for sp in got.keys)
    var_opaque.setdefault(base, set()).update(
        keys + sp for sp in got.opaque)
def _apply_setdefault(
        call: ast.Call, var: str,
        var_literals: dict[str, set[tuple[str, ...]]],
        var_assigned: dict[str, int],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> None:
    first = call.args[0] if call.args else None
    if not (isinstance(first, ast.Constant) and isinstance(first.value, str)):
        var_literals.pop(var, None)
        var_opaque.pop(var, None)
        return
    key = (first.value,)
    if any(path[:1] == key for path in var_literals[var]):
        return
    if len(call.args) >= 2:
        _setdefault_default(
            call, key, var, var_literals, var_assigned, var_opaque)
        return
    var_literals[var].add(key)
def _setdefault_default(
        call: ast.Call, key: tuple[str, ...], var: str,
        var_literals: dict[str, set[tuple[str, ...]]],
        var_assigned: dict[str, int],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> None:
    nested = augmented_key_paths_and_opaque(
        call.args[1], var_literals, var_assigned, var_opaque)
    if nested is None and not _is_leaf_value(call.args[1]):
        var_literals[var].add(key)
        var_opaque.setdefault(var, set()).add(key)
        return
    var_literals[var].add(key)
    if nested is not None:
        var_literals[var].update(key + sp for sp in nested.keys)
        var_opaque.setdefault(var, set()).update(
            key + sp for sp in nested.opaque)
def update_call_form(node: ast.AST) -> tuple[str, str] | None:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in ('update', 'setdefault')
            and isinstance(node.func.value, ast.Name)):
        return None
    return node.func.attr, node.func.value.id
def update_key_increments(
        call: ast.Call,
        var_literals: dict[str, set[tuple[str, ...]]],
        var_assigned: dict[str, int],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> tuple[
            set[tuple[str, ...]], set[tuple[str, ...]], bool]:
    added: set[tuple[str, ...]] = set()
    opaque: set[tuple[str, ...]] = set()
    open_keys = False
    for kw in call.keywords:
        if kw.arg is None:
            open_keys = True
            continue
        added.add((kw.arg,))
        value_paths = augmented_key_paths_and_opaque(
            kw.value, var_literals, var_assigned, var_opaque)
        if value_paths is None:
            if not _is_leaf_value(kw.value):
                opaque.add((kw.arg,))
        else:
            added |= {(kw.arg,) + sp for sp in value_paths.keys}
            opaque |= {(kw.arg,) + sp for sp in value_paths.opaque}
    for arg in call.args:
        got = augmented_key_paths_and_opaque(
            arg, var_literals, var_assigned, var_opaque)
        if got is None:
            open_keys = True
        else:
            added |= got.keys
            opaque |= got.opaque
    return added, opaque, open_keys
def _merge_update_keys_into_literals(
        call: ast.Call, var: str,
        var_literals: dict[str, set[tuple[str, ...]]],
        var_assigned: dict[str, int],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> bool:
    added, opaque, open_keys = update_key_increments(
        call, var_literals, var_assigned, var_opaque)
    for path in added:
        if len(path) == 1:
            _invalidate_literal_path_prefix(
                var, path, var_literals, var_opaque)
    var_literals[var] |= added
    var_opaque.setdefault(var, set()).update(opaque)
    return open_keys
def _apply_update_or_setdefault(
        sub: ast.AST,
        var_literals: dict[str, set[tuple[str, ...]]],
        var_assigned: dict[str, int],
        var_opaque: dict[str, set[tuple[str, ...]]]) -> None:
    form = update_call_form(sub)
    if form is None:
        return
    attr, var = form
    if var not in var_literals:
        return
    if attr == 'setdefault':
        _apply_setdefault(
            sub, var, var_literals, var_assigned, var_opaque)
        return
    if _merge_update_keys_into_literals(
            sub, var, var_literals, var_assigned, var_opaque):
        var_literals.pop(var, None)
        var_opaque.pop(var, None)
def _function_block_exits(stmts: list[ast.stmt]) -> bool:
    for stmt in stmts:
        if isinstance(stmt, (ast.Return, ast.Raise)):
            return True
        if (isinstance(stmt, ast.If)
                and _function_block_exits(stmt.body)
                and _function_block_exits(stmt.orelse)):
            return True
    return False
def _contract_return_nodes(
        scope_nodes: list[ast.AST], *, include_none: bool = False,
) -> list[ast.Return]:
    overridden: set[int] = set()
    try_nodes = (ast.Try, getattr(ast, 'TryStar', ast.Try))
    for node in scope_nodes:
        if not isinstance(node, try_nodes) or not _function_block_exits(
                node.finalbody):
            continue
        regions = [node.body, node.orelse,
                   *(handler.body for handler in node.handlers)]
        for region in regions:
            for stmt in region:
                for sub in iter_nodes_outside(stmt):
                    if isinstance(sub, ast.Return):
                        overridden.add(id(sub))
    return [node for node in scope_nodes
            if isinstance(node, ast.Return)
            and (include_none or not _is_none_return(node.value))
            and id(node) not in overridden]
def _return_value_paths(
        val: ast.AST,
        var_assigned: dict[str, int],
        var_literals: dict[str, set[tuple[str, ...]]],
        var_opaque: dict[str, set[tuple[str, ...]]],
) -> tuple[set[tuple[str, ...]], set[tuple[str, ...]]] | None:
    if isinstance(val, ast.Name):
        if var_assigned.get(val.id, 0) != 1 or val.id not in var_literals:
            return None
        return var_literals[val.id], var_opaque.get(val.id, set())
    got = _literal_dict_paths(val)
    if got is None:
        return None
    return got.keys, got.opaque
def _collect_return_paths(
        scope_nodes: list[ast.AST],
        var_assigned: dict[str, int],
        var_literals: dict[str, set[tuple[str, ...]]],
        var_opaque: dict[str, set[tuple[str, ...]]],
) -> tuple[set[tuple[str, ...]], set[tuple[str, ...]]] | None:
    paths: set[tuple[str, ...]] | None = None
    opaque: set[tuple[str, ...]] | None = None
    for sub in _contract_return_nodes(scope_nodes):
        got = _return_value_paths(
            sub.value, var_assigned, var_literals, var_opaque)
        if got is None:
            return None
        if paths is None:
            paths = set(got[0])
            opaque = set(got[1])
        else:
            paths.intersection_update(got[0])
            opaque.intersection_update(got[1])
    if paths is None or opaque is None:
        return None
    return paths, opaque
def _collect_return_union(
        scope_nodes: list[ast.AST],
        var_assigned: dict[str, int],
        var_literals: dict[str, set[tuple[str, ...]]],
        var_opaque: dict[str, set[tuple[str, ...]]],
) -> set[tuple[str, ...]] | None:
    union: set[tuple[str, ...]] = set()
    for sub in _contract_return_nodes(scope_nodes):
        got = _return_value_paths(
            sub.value, var_assigned, var_literals, var_opaque)
        if got is None:
            return None
        union |= got[0]
    return union
def _merge_fn_paths(
        fname: str,
        paths_opaque: tuple[set[tuple[str, ...]], set[tuple[str, ...]]],
        fn_key_paths: dict[str, set[tuple[str, ...]]],
        fn_opaque: dict[str, set[tuple[str, ...]]]) -> None:
    paths, opaque = paths_opaque
    if fname in fn_key_paths:
        fn_key_paths[fname] |= paths
        fn_opaque[fname] |= opaque
        return
    fn_key_paths[fname] = paths
    fn_opaque[fname] = opaque
def _merge_union_paths(
        fname: str,
        union: set[tuple[str, ...]] | None,
        fn_union_paths: dict[str, set[tuple[str, ...]] | None]) -> None:
    unknown = fname in fn_union_paths and fn_union_paths[fname] is None
    if union is None or unknown:
        fn_union_paths[fname] = None
        return
    known = fn_union_paths.get(fname)
    if known is None:
        fn_union_paths[fname] = set(union)
    else:
        known.update(union)
def collect_fn_key_paths(
        tree: ast.AST,
) -> tuple[dict[str, set[tuple[str, ...]]],
           dict[str, set[tuple[str, ...]]],
           dict[str, set[tuple[str, ...]] | None]]:
    fn_key_paths: dict[str, set[tuple[str, ...]]] = {}
    fn_opaque: dict[str, set[tuple[str, ...]]] = {}
    fn_union_paths: dict[str, set[tuple[str, ...]] | None] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, SCOPE_CONTAINERS) or isinstance(node, ast.Module):
            continue
        _scope_key_paths(node, fn_key_paths, fn_opaque, fn_union_paths)
    return fn_key_paths, fn_opaque, fn_union_paths
_FnContract = tuple[set[tuple[str, ...]], set[tuple[str, ...]]]
def collect_fn_key_paths_per_def(
        tree: ast.AST,
) -> dict[str, list[tuple[bool, _FnContract | None]]]:
    per_def: dict[str, list[tuple[bool, _FnContract | None]]] = {}
    method_names = _method_scope_names(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, SCOPE_CONTAINERS) or isinstance(node, ast.Module):
            continue
        fname = getattr(node, 'name', None)
        if not fname:
            continue
        tmp_paths: dict[str, set[tuple[str, ...]]] = {}
        tmp_opaque: dict[str, set[tuple[str, ...]]] = {}
        tmp_union: dict[str, set[tuple[str, ...]] | None] = {}
        _scope_key_paths(node, tmp_paths, tmp_opaque, tmp_union)
        paths = tmp_paths.get(fname)
        contract = (None if paths is None else
                    (paths, tmp_opaque.get(fname, set())))
        per_def.setdefault(fname, []).append(
            (id(node) in method_names, contract))
    return per_def
def _free_fn_definitions(
        tree: ast.AST,
) -> dict[str, list[ast.FunctionDef | ast.AsyncFunctionDef]]:
    method_scopes = _method_scope_names(tree)
    definitions: dict[
        str, list[ast.FunctionDef | ast.AsyncFunctionDef]] = {}
    for node in walk_nodes(tree):
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and id(node) not in method_scopes):
            definitions.setdefault(node.name, []).append(node)
    return definitions
def _method_scope_names(tree: ast.AST) -> set[int]:
    out: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        stack: list[ast.AST] = list(node.body)
        while stack:
            sub = stack.pop()
            if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef)):
                out.add(id(sub))
                continue
            stack.extend(ast.iter_child_nodes(sub))
    return out
def _scope_key_paths(
        node: ast.AST,
        fn_key_paths: dict[str, set[tuple[str, ...]]],
        fn_opaque: dict[str, set[tuple[str, ...]]],
        fn_union_paths: dict[str, set[tuple[str, ...]] | None]) -> None:
    fname = getattr(node, 'name', None)
    if not fname:
        return
    scope_nodes = iter_direct_scope(node)
    var_assigned, var_literals, var_opaque = local_literal_tables(
        scope_nodes)
    for sub in scope_nodes:
        _apply_subscript_writes(
            sub, var_literals, var_assigned, var_opaque)
        _apply_augassign(sub, var_literals, var_assigned, var_opaque)
        _apply_update_or_setdefault(
            sub, var_literals, var_assigned, var_opaque)
    _merge_union_paths(fname, _collect_return_union(
        scope_nodes, var_assigned, var_literals, var_opaque), fn_union_paths)
    paths_opaque = _collect_return_paths(
        scope_nodes, var_assigned, var_literals, var_opaque)
    if paths_opaque is None:
        return
    _merge_fn_paths(fname, paths_opaque, fn_key_paths, fn_opaque)
_Wm01WriteMap = dict[tuple[str, tuple[str, ...]], list[ast.AST]]
@dataclass(frozen=True)
class _Wm01Scan:
    fn_key_paths: dict[str, set[tuple[str, ...]]]
    fn_opaque: dict[str, set[tuple[str, ...]]]
    exempt: frozenset[int]
    local_keys: dict[str, set[tuple[str, ...]]]
    issues: list[dict[str, Any]]
    filepath: Any
    src_lines: list[str]
    seen: set[tuple[str, tuple[str, ...], int]]
    fn_defs: dict[str, list[ast.FunctionDef | ast.AsyncFunctionDef]]
    local_writes: _Wm01WriteMap
    local_opaque: dict[str, set[tuple[str, ...]]] = field(default_factory=dict)
    resolver: Any = None
    poison_writes: dict[str, list[ast.AST]] = field(default_factory=dict)
    parents: dict[int, ast.AST] = field(default_factory=dict)
    post_guards: tuple[
        tuple[ast.AST, frozenset[tuple[str, str]]], ...] = ()
    fn_union_paths: dict[str, set[tuple[str, ...]] | None] = field(
        default_factory=dict)
    shadowed_fns: frozenset[str] = frozenset()
@dataclass
class _LocalKeyCtx:
    local: dict[str, set[tuple[str, ...]]]
    var_literals: dict[str, set[tuple[str, ...]]]
    var_assigned: dict[str, int]
    writes: _Wm01WriteMap
    fn_key_paths: dict[str, set[tuple[str, ...]]]
    fn_union_paths: dict[str, set[tuple[str, ...]] | None]
    opaque: dict[str, set[tuple[str, ...]]] = field(default_factory=dict)
    var_opaque: dict[str, set[tuple[str, ...]]] = field(default_factory=dict)
    resolver: Any = None
    poison_writes: dict[str, list[ast.AST]] = field(default_factory=dict)
    parents: dict[int, ast.AST] = field(default_factory=dict)
    shadow_cache: dict[tuple[int, frozenset[int]], set[str]] = field(
        default_factory=dict)
_RECEIVER_PARAM_NAMES = frozenset({'self', 'cls'})
def _wm01_callable_ref_name(func: ast.AST) -> str | None:
    if isinstance(func, ast.Name):
        return func.id
    if (isinstance(func, ast.Attribute)
            and isinstance(func.value, ast.Name)
            and func.value.id in _RECEIVER_PARAM_NAMES):
        return func.attr
    return None
def _wm01_bound_value(node: ast.Call, callee: str,
                      param_names: dict[str, str]) -> ast.AST | None:
    if node.args and not isinstance(node.args[0], ast.Starred):
        return node.args[0]
    param = param_names.get(callee)
    if param is None or node.args or any(kw.arg is None for kw in node.keywords):
        return None
    matched = [kw.value for kw in node.keywords if kw.arg == param]
    return matched[0] if len(matched) == 1 else None
def _wm01_data_params(
        scope: ast.AST, *, is_method: bool) -> list[ast.arg]:
    args = getattr(scope, 'args', None)
    if args is None:
        return []
    params = [*getattr(args, 'posonlyargs', ()), *getattr(args, 'args', [])]
    if is_method and params and params[0].arg in _RECEIVER_PARAM_NAMES:
        params = params[1:]
    return [*params, *getattr(args, 'kwonlyargs', ())]
def _wm01_first_param_names(tree: ast.AST) -> dict[str, str]:
    names: dict[str, str] = {}
    conflicts: set[str] = set()
    method_scopes = _method_scope_names(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        params = _wm01_data_params(node, is_method=id(node) in method_scopes)
        if not params:
            continue
        first = params[0].arg
        prev = names.get(node.name)
        if prev is None:
            names[node.name] = first
        elif prev != first:
            conflicts.add(node.name)
    for name in conflicts:
        names.pop(name, None)
    return names
def _wm01_compatible_inner_call(
        node: ast.AST,
        fn_key_paths: dict[str, set[tuple[str, ...]]],
        param_names: dict[str, str],
) -> str | None:
    if not isinstance(node, ast.Call):
        return None
    callee = func_name_of_call(node)
    if callee is None:
        return None
    inner = _wm01_bound_value(node, callee, param_names)
    if not isinstance(inner, ast.Call):
        return None
    inner_name = _wm01_callable_ref_name(inner.func)
    if inner_name is None or inner_name not in fn_key_paths:
        return None
    return inner_name
def _wm01_group_call_sites(
        tree: ast.AST,
        fn_key_paths: dict[str, set[tuple[str, ...]]],
        param_names: dict[str, str],
) -> tuple[dict[str, list[str]], set[str]]:
    grouped: dict[str, list[str]] = {}
    foreign: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        callee = _wm01_callable_ref_name(node.func)
        if callee is None:
            continue
        inner = _wm01_compatible_inner_call(node, fn_key_paths, param_names)
        if inner is None:
            foreign.add(callee)
            continue
        bound = grouped.setdefault(callee, [])
        if inner not in bound:
            bound.append(inner)
    return grouped, foreign
def _wm01_param_bindings(
        tree: ast.AST,
        fn_key_paths: dict[str, set[tuple[str, ...]]],
        fn_opaque: dict[str, set[tuple[str, ...]]],
) -> dict[str, str]:
    grouped, foreign = _wm01_group_call_sites(
        tree, fn_key_paths, _wm01_first_param_names(tree))
    bindings: dict[str, str] = {}
    for callee, fns in grouped.items():
        if callee in foreign:
            continue
        if len(fns) == 1:
            bindings[callee] = fns[0]
            continue
        display = ' | '.join(fns)
        fn_key_paths[display] = set.intersection(
            *(fn_key_paths[f] for f in fns))
        fn_opaque[display] = set.intersection(
            *(fn_opaque.get(f, set()) for f in fns))
        bindings[callee] = display
    return bindings
def _augment_local(local: dict[str, set[tuple[str, ...]]], var: str,
                   paths: set[tuple[str, ...]] | None) -> None:
    if paths:
        local.setdefault(var, set()).update(paths)
def _wm01_record_key_writes(ctx: _LocalKeyCtx, var: str,
                           paths: set[tuple[str, ...]],
                           write: ast.AST) -> None:
    for path in paths:
        ctx.writes.setdefault((var, path), []).append(write)
def _wm01_child_under(
        ancestor: ast.AST, node: ast.AST,
        parents: dict[int, ast.AST]) -> ast.AST | None:
    cur = node
    while id(cur) in parents:
        parent = parents[id(cur)]
        if parent is ancestor:
            return cur
        cur = parent
    return None
def _wm01_region_write_dominates(
        region: list[ast.stmt], node: ast.AST, writes: list[ast.AST],
        parents: dict[int, ast.AST], stop: ast.AST,
        presence: tuple[str, str] | None) -> bool:
    return any(
        any(_ef01_within(write, stmt, parents) for stmt in region)
        and _wm01_write_dominates(
            write, node, parents, writes, stop=stop, presence=presence)
        for write in writes)

def _wm01_if_write_covered(
        owner: ast.If, node: ast.AST, writes: list[ast.AST],
        parents: dict[int, ast.AST],
        presence: tuple[str, str] | None = None) -> bool:
    for branch, truth in ((owner.body, True), (owner.orelse, False)):
        if block_exits(branch):
            continue
        if _wm01_region_write_dominates(
                branch, node, writes, parents, owner, presence):
            continue
        if (presence is not None
                and presence in _wm01_present_on_truth(owner.test, truth)):
            continue
        return False
    return True
def _wm01_try_write_covered(
        owner: ast.AST, node: ast.AST, writes: list[ast.AST],
        parents: dict[int, ast.AST],
        presence: tuple[str, str] | None = None) -> bool:
    def covered(region: list[ast.stmt]) -> bool:
        return _wm01_region_write_dominates(
            region, node, writes, parents, owner, presence)

    if covered(owner.finalbody):
        return True
    normal_covered = (
        block_exits(owner.body) or covered(owner.body) or covered(owner.orelse))
    return normal_covered and all(
        block_exits(handler.body) or covered(handler.body)
        for handler in owner.handlers)

def _wm01_write_dominates(
        write: ast.AST, node: ast.AST, parents: dict[int, ast.AST],
        writes: list[ast.AST], stop: ast.AST | None = None,
        presence: tuple[str, str] | None = None) -> bool:
    if node_end_position(write) > (node.lineno, node.col_offset):
        return False
    cur = write
    while cur is not stop:
        owner = parents.get(id(cur))
        if owner is None:
            return False
        if owner is stop:
            return True
        if isinstance(owner, SCOPE_CONTAINERS):
            return True
        if isinstance(owner, ast.If):
            if _ef01_within(cur, owner.test, parents):
                cur = owner
                continue
            truth = branch_truth(owner, cur)
            if truth is None:
                return False
            child = _wm01_child_under(owner, node, parents)
            if child is None:
                if not _wm01_if_write_covered(
                        owner, node, writes, parents, presence):
                    return False
            elif branch_truth(owner, child) != truth:
                return False
        elif isinstance(owner, (ast.For, ast.AsyncFor, ast.While)):
            evaluated = owner.iter if isinstance(
                owner, (ast.For, ast.AsyncFor)) else owner.test
            if _ef01_within(cur, evaluated, parents):
                cur = owner
                continue
            child = _wm01_child_under(owner, node, parents)
            if (child is None
                    or not any(child is stmt for stmt in owner.body)):
                return False
        elif isinstance(owner, (ast.With, ast.AsyncWith)):
            if any(_ef01_within(cur, item.context_expr, parents)
                   for item in owner.items):
                cur = owner
                continue
            child = _wm01_child_under(owner, node, parents)
            if (child is None
                    or not any(child is stmt for stmt in owner.body)):
                # 读点在 with 之后：体正常退出即已写入，与 try 体写入
                # 对 try 之后读点的支配同理，按体区域判定而非一票否决。
                if (child is None
                        and _wm01_region_write_dominates(
                            owner.body, node, writes, parents, owner, presence)):
                    cur = owner
                    continue
                return False
        elif isinstance(owner, (ast.Try, getattr(ast, 'TryStar', ast.Try))):
            child = _wm01_child_under(owner, node, parents)
            if child is None:
                if not _wm01_try_write_covered(
                        owner, node, writes, parents, presence):
                    return False
                cur = owner
                continue
            in_final = any(cur is stmt for stmt in owner.finalbody)
            if in_final:
                if not any(child is stmt for stmt in owner.finalbody):
                    return False
            else:
                same_region = any(
                    any(cur is stmt for stmt in region)
                    and any(child is stmt for stmt in region)
                    for region in (owner.body, owner.orelse, owner.finalbody))
                normal_transition = (
                    any(cur is stmt for stmt in owner.body)
                    and any(child is stmt for stmt in owner.orelse))
                same_handler = cur is child and isinstance(
                    cur, ast.ExceptHandler)
                if not (same_region or normal_transition or same_handler):
                    return False
        elif isinstance(owner, (ast.ExceptHandler, ast.match_case)):
            child = _wm01_child_under(owner, node, parents)
            bounded_region = (
                isinstance(owner, ast.ExceptHandler) and stop is not None
                and _ef01_within(owner, stop, parents))
            if child is None and not bounded_region:
                return False
        elif isinstance(owner, ast.Match):
            if _ef01_within(cur, owner.subject, parents):
                cur = owner
                continue
            # write 与读点必须落在同一 match_case 内才算支配；
            # 跨 case 的写不能保证读点执行，但同 case 内不能一票否决。
            child = _wm01_child_under(owner, node, parents)
            if child is None or child is not cur:
                return False
            cur = owner
            continue
        cur = owner
    return True
def _wm01_writes_guarantee(
        write_map: _Wm01WriteMap, var: str, path: tuple[str, ...],
        node: ast.AST, parents: dict[int, ast.AST]) -> bool:
    writes = write_map.get((var, path), ())
    presence = (path[0], var) if len(path) == 1 else None
    return any(_wm01_write_dominates(
        write, node, parents, list(writes), presence=presence)
               for write in writes)
def _wm01_poisoned_at(scan: Any, name: str, node: ast.AST) -> bool:
    writes = scan.poison_writes.get(name, ())
    return any(_wm01_write_dominates(
        write, node, scan.parents, list(writes)) for write in writes)
def _wm01_mark_poison(ctx: _LocalKeyCtx, name: str, node: ast.AST) -> None:
    ctx.poison_writes.setdefault(name, []).append(node)
def _wm01_poison_dynamic_base(target: ast.AST, ctx: _LocalKeyCtx,
                              node: ast.AST) -> None:
    base = _shared_subscript_base_name(target)
    if base is not None:
        _wm01_mark_poison(ctx, base, node)
def _wm01_local_subscript_keys(node: ast.AST, ctx: _LocalKeyCtx) -> None:
    for tgt, val in iter_write_targets(node):
        chain = subscript_target_chain(tgt)
        if not chain:
            if isinstance(tgt, ast.Subscript):
                _wm01_poison_dynamic_base(tgt, ctx, node)
            continue
        base, keys = chain
        ctx.local.setdefault(base, set()).add(keys)
        nested = augmented_key_paths_and_opaque(
            val, ctx.var_literals, ctx.var_assigned, ctx.var_opaque)
        if nested is not None:
            ctx.local[base].update(keys + sp for sp in nested.keys)
            ctx.opaque.setdefault(base, set()).update(
                keys + sp for sp in nested.opaque)
        elif not _is_leaf_value(val):
            ctx.opaque.setdefault(base, set()).add(keys)
        _wm01_record_key_writes(
            ctx, base,
            {keys} | ({keys + sp for sp in nested.keys}
                      if nested is not None else set()),
            node)
def _wm01_local_augassign_keys(node: ast.AST, ctx: _LocalKeyCtx) -> None:
    if not (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.BitOr)):
        return
    if isinstance(node.target, ast.Name):
        got = augmented_key_paths_and_opaque(
            node.value, ctx.var_literals, ctx.var_assigned, ctx.var_opaque)
        _augment_local(ctx.local, node.target.id,
                       got.keys if got is not None else None)
        if got is None:
            ctx.opaque.setdefault(node.target.id, set()).add(())
            _wm01_record_key_writes(ctx, node.target.id, {()}, node)
        elif got.opaque:
            ctx.opaque.setdefault(node.target.id, set()).update(got.opaque)
        _wm01_record_key_writes(
            ctx, node.target.id,
            set(got.keys) if got is not None else set(), node)
        return
    chain = subscript_target_chain(node.target)
    if not chain:
        if isinstance(node.target, ast.Subscript):
            _wm01_poison_dynamic_base(node.target, ctx, node)
        return
    base, keys = chain
    got = augmented_key_paths_and_opaque(
        node.value, ctx.var_literals, ctx.var_assigned, ctx.var_opaque)
    ctx.local.setdefault(base, set()).add(keys)
    if got is not None:
        ctx.local[base].update(keys + sp for sp in got.keys)
        if got.opaque:
            ctx.opaque.setdefault(base, set()).update(
                keys + sp for sp in got.opaque)
    else:
        ctx.opaque.setdefault(base, set()).add(keys)
    _wm01_record_key_writes(
        ctx, base,
        {keys} | ({keys + sp for sp in got.keys}
                  if got is not None else set()),
        node)
def _wm01_setdefault_key_exists(
        call: ast.Call, var: str, key: tuple[str, ...],
        ctx: _LocalKeyCtx) -> bool:
    for path in ctx.local.get(var, ()):
        if (_path_hit_or_prefix(key, {path})
                and _wm01_writes_guarantee(
                    ctx.writes, var, path, call, ctx.parents)):
            return True
    hit = ctx.resolver.resolve(var, call.lineno, call.col_offset)
    if not hit or call.lineno < hit[1]:
        return False
    return _path_hit_or_prefix(key, ctx.fn_key_paths.get(hit[0], set()))
def _wm01_write_may_precede(
        write: ast.AST, node: ast.AST,
        parents: dict[int, ast.AST]) -> bool:
    if node_end_position(write) > (node.lineno, node.col_offset):
        return False
    cur = write
    while id(cur) in parents:
        owner = parents[id(cur)]
        child = _wm01_child_under(owner, node, parents)
        if isinstance(owner, ast.If) and not _ef01_within(
                cur, owner.test, parents):
            write_branch = branch_truth(owner, cur)
            if write_branch is not None and child is not None:
                node_branch = branch_truth(owner, child)
                if node_branch is not None and node_branch != write_branch:
                    return False
        elif isinstance(owner, ast.Match):
            if (isinstance(cur, ast.match_case)
                    and isinstance(child, ast.match_case)
                    and cur is not child):
                return False
        elif (isinstance(owner, (ast.Try, getattr(ast, 'TryStar', ast.Try)))
              and isinstance(cur, ast.ExceptHandler)
              and isinstance(child, ast.ExceptHandler)
              and cur is not child):
            return False
        cur = owner
    return True
def _wm01_setdefault_key_may_exist(
        call: ast.Call, var: str, key: tuple[str, ...],
        ctx: _LocalKeyCtx) -> bool:
    for path in ctx.local.get(var, ()):
        if not _path_hit_or_prefix(key, {path}):
            continue
        if any(_wm01_write_may_precede(write, call, ctx.parents)
               for write in ctx.writes.get((var, path), ())):
            return True
    hit = ctx.resolver.resolve(var, call.lineno, call.col_offset)
    if not hit or call.lineno < hit[1]:
        return False
    union = ctx.fn_union_paths.get(hit[0])
    return union is None or _path_hit_or_prefix(key, union)
def _wm01_local_setdefault_keys(
        call: ast.Call, var: str, ctx: _LocalKeyCtx) -> None:
    if not (call.args
            and isinstance(call.args[0], ast.Constant)
            and isinstance(call.args[0].value, str)):
        _wm01_mark_poison(ctx, var, call)
        return
    _key = (call.args[0].value,)
    if _wm01_setdefault_key_exists(call, var, _key, ctx):
        return
    _may_exist = _wm01_setdefault_key_may_exist(call, var, _key, ctx)
    _got = None
    if len(call.args) >= 2:
        _got = augmented_key_paths_and_opaque(
            call.args[1], ctx.var_literals, ctx.var_assigned, ctx.var_opaque)
    ctx.local.setdefault(var, set()).add(_key)
    _default_paths = (_got.keys if _got is not None and not _may_exist
                      else set())
    ctx.local[var].update(_key + sp for sp in _default_paths)
    if _got is not None and _got.opaque and not _may_exist:
        ctx.opaque.setdefault(var, set()).update(
            _key + sp for sp in _got.opaque)
    elif _got is None and len(call.args) >= 2 and not _is_leaf_value(call.args[1]):
        ctx.opaque.setdefault(var, set()).add(_key)
    _wm01_record_key_writes(
        ctx, var, {_key} | {_key + sp for sp in _default_paths}, call)
def _wm01_update_keys_of_call(
        call: ast.Call, var: str, ctx: _LocalKeyCtx) -> bool:
    added, opaque, open_keys = update_key_increments(
        call, ctx.var_literals, ctx.var_assigned, ctx.var_opaque)
    _augment_local(ctx.local, var, added)
    if opaque:
        ctx.opaque.setdefault(var, set()).update(opaque)
    _wm01_record_key_writes(ctx, var, set(added or ()), call)
    return open_keys
def _wm01_local_call_keys(node: ast.AST, ctx: _LocalKeyCtx) -> None:
    form = update_call_form(node)
    if form is None:
        return
    attr, var = form
    if attr == 'setdefault':
        _wm01_local_setdefault_keys(node, var, ctx)
        return
    if _wm01_update_keys_of_call(node, var, ctx):
        _wm01_mark_poison(ctx, var, node)
def _wm01_local_escapes(node: ast.AST, ctx: _LocalKeyCtx) -> None:
    if not isinstance(node, ast.Call):
        return
    if (isinstance(node.func, ast.Name) and node.func.id == 'len'
            and len(node.args) == 1 and not node.keywords
            and not shadowed_binding_at(
                node, 'len', ctx.parents, ctx.shadow_cache)):
        return
    for arg in [*node.args, *(kw.value for kw in node.keywords)]:
        if isinstance(arg, ast.Name):
            _wm01_mark_poison(ctx, arg.id, node)
def _wm01_reset_name_bindings(node: ast.AST, ctx: _LocalKeyCtx) -> None:
    names = set(rebound_binding_names(node))
    for target, _value in iter_write_targets(node):
        names |= target_binding_names(target)
    for var in names:
        ctx.local.pop(var, None)
        ctx.opaque.pop(var, None)
        ctx.poison_writes.pop(var, None)
        for key in [key for key in ctx.writes if key[0] == var]:
            del ctx.writes[key]
def _wm01_local_augmented_keys(
        nodes: list[ast.AST],
        fn_key_paths: dict[str, set[tuple[str, ...]]],
        fn_union_paths: dict[str, set[tuple[str, ...]] | None],
        resolver: Any,
        parents: dict[int, ast.AST],
) -> tuple[dict[str, set[tuple[str, ...]]],
           dict[str, set[tuple[str, ...]]],
           dict[str, list[ast.AST]], _Wm01WriteMap]:
    var_assigned, var_literals, var_opaque = local_literal_tables(nodes)
    ctx = _LocalKeyCtx(local={}, writes={},
                       var_literals=var_literals, var_assigned=var_assigned,
                       var_opaque=var_opaque, parents=parents,
                       fn_key_paths=fn_key_paths,
                       fn_union_paths=fn_union_paths, resolver=resolver)
    for node in nodes:
        _wm01_local_subscript_keys(node, ctx)
        _wm01_local_augassign_keys(node, ctx)
        _wm01_local_call_keys(node, ctx)
        _wm01_local_escapes(node, ctx)
        _wm01_reset_name_bindings(node, ctx)
    return ctx.local, ctx.opaque, ctx.poison_writes, ctx.writes
def _wm01_presence_check_nodes(test: ast.AST) -> list[ast.AST]:
    found: list[ast.AST] = []
    for sub in walk_nodes(test):
        membership = _wm01_string_membership(sub, (ast.NotIn,))
        if membership is not None:
            found.append(sub)
            continue
        if isinstance(sub, ast.UnaryOp) and isinstance(sub.op, ast.Not):
            inner = _wm01_string_membership(sub.operand, (ast.In,))
            if inner is not None:
                found.append(sub.operand)
    return found
def _wm01_presence_exempt(nodes: list[ast.AST]) -> frozenset[int]:
    exempt: set[int] = set()
    for node in nodes:
        if isinstance(node, (ast.If, ast.While, ast.Assert, ast.IfExp)):
            exempt.update(id(sub)
                          for sub in _wm01_presence_check_nodes(node.test))
    return frozenset(exempt)
def _wm01_string_membership(
        sub: ast.AST, operators: tuple[type[ast.AST], ...],
) -> tuple[str, str, int] | None:
    if not (isinstance(sub, ast.Compare) and len(sub.ops) == 1
            and isinstance(sub.ops[0], operators)):
        return None
    if not (isinstance(sub.left, ast.Constant)
            and isinstance(sub.left.value, str)
            and isinstance(sub.comparators[0], ast.Name)):
        return None
    return sub.left.value, sub.comparators[0].id, sub.lineno
def _wm01_present_on_truth(test: ast.AST, truth: bool) -> set[tuple[str, str]]:
    if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
        return _wm01_present_on_truth(test.operand, not truth)
    if isinstance(test, ast.NamedExpr):
        return _wm01_present_on_truth(test.value, truth)
    if isinstance(test, ast.BoolOp):
        all_same = ((isinstance(test.op, ast.And) and truth)
                    or (isinstance(test.op, ast.Or) and not truth))
        if not all_same:
            return set()
        present: set[tuple[str, str]] = set()
        for value in test.values:
            present |= _wm01_present_on_truth(value, truth)
        return present
    membership = _wm01_string_membership(test, (ast.In, ast.NotIn))
    if membership is None:
        return set()
    key, var, _lineno = membership
    is_in = isinstance(test.ops[0], ast.In)
    return {(key, var)} if truth == is_in else set()
def _wm01_post_guards(
        nodes: list[ast.AST],
) -> tuple[tuple[ast.AST, frozenset[tuple[str, str]]], ...]:
    guards: list[tuple[ast.AST, frozenset[tuple[str, str]]]] = []
    for node in nodes:
        if isinstance(node, ast.Assert):
            present = frozenset(_wm01_present_on_truth(node.test, True))
            if present:
                guards.append((node, present))
            continue
        if not isinstance(node, ast.If):
            continue
        if block_exits(node.body):
            present = frozenset(_wm01_present_on_truth(node.test, False))
            if present:
                guards.append((node, present))
        if block_exits(node.orelse):
            present = frozenset(_wm01_present_on_truth(node.test, True))
            if present:
                guards.append((node, present))
    return tuple(guards)
def _wm01_membership_exempt(
        sub: ast.AST, var: str, scan: _Wm01Scan) -> bool:
    for lp in scan.local_keys.get(var, ()):
        if not (lp and lp[0] == sub.left.value):
            continue
        if any(_wm01_write_may_precede(write, sub, scan.parents)
               for write in scan.local_writes.get((var, lp), ())):
            return True
    return id(sub) in scan.exempt
def _wm01_post_guarded(
        scan: _Wm01Scan, var: str, key: str, node: ast.AST,
        bind_line: int) -> bool:
    pair = (key, var)
    return any(
        bind_line <= getattr(guard, 'lineno', 0)
        and pair in present
        and _ef01_guard_precedes(guard, node, scan.parents)
        for guard, present in scan.post_guards
    )
def _wm01_presence_guarded(
        scan: _Wm01Scan, var: str, key: str, node: ast.AST,
        bind_line: int) -> bool:
    pair = (key, var)
    if _wm01_post_guarded(scan, var, key, node, bind_line):
        return True
    cur = node
    while id(cur) in scan.parents:
        parent = scan.parents[id(cur)]
        if isinstance(parent, ast.BoolOp):
            idx = next(
                (i for i, value in enumerate(parent.values) if value is cur),
                None)
            if idx is not None:
                truth = isinstance(parent.op, ast.And)
                if any(bind_line <= getattr(prev, 'lineno', 0)
                       and pair in _wm01_present_on_truth(prev, truth)
                       for prev in parent.values[:idx]):
                    return True
            cur = parent
            continue
        if isinstance(parent, (ast.If, ast.While, ast.IfExp)):
            truth = branch_truth(parent, cur)
            if (truth is not None
                    and bind_line <= getattr(parent.test, 'lineno', 0)
                    and pair in _wm01_present_on_truth(parent.test, truth)):
                return True
            cur = parent
            continue
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.ClassDef, ast.Module, ast.Lambda)):
            return False
        cur = parent
    return False
def _wm01_direct_call_membership(
        sub: ast.AST, scan: _Wm01Scan, shadow: frozenset[str]) -> None:
    if not (isinstance(sub, ast.Compare) and len(sub.ops) == 1
            and isinstance(sub.ops[0], (ast.In, ast.NotIn))
            and isinstance(sub.left, ast.Constant)
            and isinstance(sub.left.value, str)):
        return
    base = _unwrap_await(sub.comparators[0])
    if not isinstance(base, ast.Call) or id(sub) in scan.exempt:
        return
    fname = _wm01_callable_ref_name(base.func)
    if (fname not in scan.fn_key_paths
            or (shadow and fname in shadow)
            or fname in scan.shadowed_fns):
        return
    if isinstance(base.func, ast.Name):
        definitions = scan.fn_defs.get(fname, ())
        if not any(_call_resolves_to_definition(base, definition, scan.parents)
                   for definition in definitions):
            return
    _wm01_report(
        scan, fname, (sub.left.value,),
        how=f'membership 判断 "in {fname}()"',
        lineno=sub.lineno, membership=True)
def _wm01_membership(sub: ast.AST, scan: _Wm01Scan,
                     shadow: frozenset[str]) -> None:
    membership = _wm01_string_membership(sub, (ast.In, ast.NotIn))
    if membership is None:
        _wm01_direct_call_membership(sub, scan, shadow)
        return
    key, var, lineno = membership
    if shadow and var in shadow:
        return
    if _wm01_poisoned_at(scan, var, sub):
        return
    if _wm01_membership_exempt(sub, var, scan):
        return
    hit = scan.resolver.resolve(var, sub.lineno, sub.col_offset)
    if not hit or lineno < hit[1] or hit[0] in scan.shadowed_fns:
        return
    if _wm01_post_guarded(scan, var, key, sub, hit[1]):
        return
    _wm01_report(scan, hit[0], (key,),
                 how=f'membership 判断 "in {var}"', lineno=lineno,
                 membership=True)
def _wm01_local_prefix_exempt(
        var: str, path: tuple[str, ...],
        local_keys: dict[str, set[tuple[str, ...]]] | None,
        local_writes: _Wm01WriteMap,
        node: ast.AST, parents: dict[int, ast.AST]) -> bool:
    if not (local_keys and path):
        return False
    for lp in local_keys.get(var, ()):
        if not (lp == path or lp[:len(path)] == path):
            continue
        if _wm01_writes_guarantee(local_writes, var, lp, node, parents):
            return True
    return False
def _wm01_check_name_base(base: ast.Name, path: tuple[str, ...],
                          site: ast.AST, scan: _Wm01Scan,
                          shadow: frozenset[str]) -> None:
    lineno = site.lineno
    if shadow and base.id in shadow:
        return
    if _wm01_poisoned_at(scan, base.id, site):
        return
    if _wm01_local_prefix_exempt(
            base.id, path, scan.local_keys, scan.local_writes,
            site, scan.parents):
        return
    guaranteed_opaque = {
        opaque_path
        for opaque_path in scan.local_opaque.get(base.id, ())
        if _wm01_writes_guarantee(
            scan.local_writes, base.id, opaque_path, site, scan.parents)
    }
    if _path_below_opaque(path, guaranteed_opaque):
        return
    hit = scan.resolver.resolve(
        base.id, base.lineno, base.col_offset)
    if not hit or lineno < hit[1] or hit[0] in scan.shadowed_fns:
        return
    paths = scan.fn_key_paths.get(hit[0], set())
    if (path and not _path_hit_or_prefix(path[:1], paths)
            and _wm01_presence_guarded(
                scan, base.id, path[0], site, hit[1])):
        return
    _wm01_report(scan, hit[0], path,
                 how=f'变量 {base.id} 的键访问', lineno=lineno)
def _wm01_has_longer_key_path(
        node: ast.AST,
        base: ast.AST,
        path: tuple[str, ...],
        parents: dict[int, ast.AST],
) -> bool:
    cur = node
    while True:
        parent = parents.get(id(cur))
        if parent is None:
            return False
        if isinstance(parent, ast.Attribute) and parent.value is cur:
            call = parents.get(id(parent))
            cur = (call if isinstance(call, ast.Call) and call.func is parent
                   else parent)
        elif isinstance(parent, ast.Subscript) and parent.value is cur:
            cur = parent
        elif (isinstance(parent, ast.Call) and parent.func is cur
              and _is_get_key_call(parent)):
            cur = parent
        else:
            return False
        outer = key_path_of(cur)
        if (outer is not None and outer[0] is base
                and len(outer[1]) > len(path)
                and outer[1][:len(path)] == path):
            return True
def _wm01_key_access(sub: ast.AST, scan: _Wm01Scan,
                     shadow: frozenset[str]) -> None:
    if isinstance(sub, (ast.Subscript, ast.Attribute)) and isinstance(
            sub.ctx, (ast.Store, ast.Del)):
        return
    if isinstance(sub, ast.Attribute):
        parent = scan.parents.get(id(sub))
        if isinstance(parent, ast.Call) and parent.func is sub:
            return
    kp = key_path_of(sub)
    if kp is None:
        return
    base, path = kp
    if _wm01_has_longer_key_path(sub, base, path, scan.parents):
        return
    base = _unwrap_await(base)
    if isinstance(base, ast.Name):
        _wm01_check_name_base(base, path, sub, scan, shadow)
    elif isinstance(base, ast.Call):
        _wm01_check_call_base(base, path, sub.lineno, scan, shadow)
def _wm01_check_call_base(base: ast.Call, path: tuple[str, ...],
                          lineno: int, scan: _Wm01Scan,
                          shadow: frozenset[str]) -> None:
    fname = _wm01_callable_ref_name(base.func)
    if fname not in scan.fn_key_paths:
        return
    if (shadow and fname in shadow) or fname in scan.shadowed_fns:
        return
    if isinstance(base.func, ast.Name):
        definitions = scan.fn_defs.get(fname, ())
        if not any(_call_resolves_to_definition(base, definition, scan.parents)
                   for definition in definitions):
            return
    _wm01_report(scan, fname, path,
                 how=f'{fname}(...) 返回值键访问', lineno=lineno)
def _wm01_scan_expr(node: ast.AST, scan: _Wm01Scan) -> None:
    def _visit(sub: ast.AST, shadow: frozenset[str]) -> None:
        _wm01_membership(sub, scan, shadow)
        if isinstance(sub, (ast.Attribute, ast.Subscript, ast.Call)):
            _wm01_key_access(sub, scan, shadow)
    walk_scope_expr([node], _visit)
def _path_hit_or_prefix(path: tuple[str, ...],
                        paths: set[tuple[str, ...]]) -> bool:
    return path in paths or any(
        len(rp) >= len(path) and rp[:len(path)] == path for rp in paths)
def _path_below_opaque(path: tuple[str, ...],
                       opaque_paths: set[tuple[str, ...]] | tuple) -> bool:
    return any(len(path) > len(op) and path[:len(op)] == op
               for op in opaque_paths)
def _wm01_is_contract_breach(scan: _Wm01Scan, fname: str,
                             path: tuple[str, ...]) -> bool:
    paths = scan.fn_key_paths.get(fname)
    if paths is None:
        return False
    if _path_hit_or_prefix(path, paths):
        return False
    return not _path_below_opaque(path, scan.fn_opaque.get(fname, ()))
def _wm01_is_membership_breach(scan: _Wm01Scan, fname: str,
                               path: tuple[str, ...]) -> bool:
    if fname not in scan.fn_key_paths:
        return False
    if fname not in scan.fn_union_paths:
        return False
    union = scan.fn_union_paths[fname]
    if union is None:
        return False
    if _path_hit_or_prefix(path, union):
        return False
    return not _path_below_opaque(path, scan.fn_opaque.get(fname, ()))
def _wm01_report(scan: _Wm01Scan, fname: str,
                 path: tuple[str, ...],
                 how: str, lineno: int, *,
                 membership: bool = False) -> None:
    is_breach = (_wm01_is_membership_breach if membership
                 else _wm01_is_contract_breach)
    if not is_breach(scan, fname, path):
        return
    dedup_key = (fname, path, lineno)
    if dedup_key in scan.seen:
        return
    scan.seen.add(dedup_key)
    paths = scan.fn_key_paths[fname]
    scan.issues.append(make_issue(
        'WM-01', 'P1', 'contract_safety', scan.filepath, lineno,
        f'键名契约断裂：{how} 路径 {".".join(path)} 不在 {fname}() 返回键集中',
        (
            f'{fname}() 的全部字面量返回键路径为 '
            f'{sorted(".".join(p) for p in paths)}，但调用方访问了 '
            f'{".".join(path)}——该键不存在，.get() 恒返回默认值、[] 触发 '
            f'KeyError、in 判断恒 False，下游功能静默失效。多阶段管道中'
            f'这是最高频的静默 BUG 形态（上游嵌套 {{"report": {{...}}}} 下游'
            f'顶层 .get("findings")）。'
        ),
        snippet_of(scan.src_lines, lineno),
        (
            '根因：阶段间数据契约（键名/嵌套层级）未对齐。\n'
            '修复策略：①以上游 return 字面量为契约 SSOT，调用方键路径'
            '逐一核对（含嵌套层级）；②契约面收敛到独立常量/TypedDict；'
            '③管道编排器在 run 循环内回写 stage 结果到 context 共享层。\n'
            '参考标准：生产与消费端数据结构键名契约不一致的缺陷模式'
        ),
        'write-key-contract',
    ))
def _wm01_is_method(node: ast.AST, parents: dict[int, ast.AST]) -> bool:
    cur = parents.get(id(node))
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            return False
        if isinstance(cur, ast.ClassDef):
            return True
        cur = parents.get(id(cur))
    return False
def _wm01_param_preset(
        container: ast.AST, bound_fn: str,
        *, is_method: bool) -> dict[str, tuple[str, int]] | None:
    if not bound_fn or not hasattr(container, 'args'):
        return None
    params = _wm01_data_params(container, is_method=is_method)
    if not params:
        return None
    return {params[0].arg: (bound_fn, 0)}
def _wm01_drop_ambiguous(
        fn_key_paths: dict[str, set[tuple[str, ...]]],
        fn_opaque: dict[str, set[tuple[str, ...]]],
        per_def: dict[str, list[tuple[bool, _FnContract | None]]],
) -> None:
    ambiguous = set()
    for name, defs in per_def.items():
        if name not in fn_key_paths or len(defs) < 2:
            continue
        if not all(is_method for is_method, _contract in defs):
            ambiguous.add(name)
            continue
        contracts = [contract for _is_method, contract in defs]
        if any(contract is None for contract in contracts):
            ambiguous.add(name)
            continue
        if len({(frozenset(contract[0]), frozenset(contract[1]))
                for contract in contracts if contract is not None}) > 1:
            ambiguous.add(name)
    for name in ambiguous:
        fn_key_paths.pop(name, None)
        fn_opaque.pop(name, None)
def _wm01_literal_base_write(
        nodes: list[ast.AST], var: str,
) -> tuple[ast.AST | None, _LiteralDictPaths]:
    for node in nodes:
        for target, value in iter_write_targets(node):
            if not isinstance(target, ast.Name) or target.id != var:
                continue
            got = _literal_dict_paths(value)
            if got is not None:
                return target, got
    return None, _LiteralDictPaths(set(), set())
def _scope_param_names(scope: ast.AST) -> frozenset[str]:
    args = getattr(scope, 'args', None)
    if args is None:
        return frozenset()
    params = [*args.posonlyargs, *args.args, *args.kwonlyargs,
              args.vararg, args.kwarg]
    return frozenset(p.arg for p in params if p is not None)
def _wm01_refined_scope_contract(
        scope: ast.AST,
        fn_key_paths: dict[str, set[tuple[str, ...]]],
        fn_union_paths: dict[str, set[tuple[str, ...]] | None],
        parents: dict[int, ast.AST],
) -> _FnContract | None:
    scope_nodes = iter_direct_scope(scope)
    var_assigned, var_literals, var_opaque = local_literal_tables(scope_nodes)
    for sub in scope_nodes:
        _apply_subscript_writes(sub, var_literals, var_assigned, var_opaque)
        _apply_augassign(sub, var_literals, var_assigned, var_opaque)
        _apply_update_or_setdefault(sub, var_literals, var_assigned, var_opaque)
    param_names = _scope_param_names(scope)
    resolver = flow_var_resolver(scope_nodes, fn_key_paths)
    _local_keys, _local_opaque, _poison, local_writes = (
        _wm01_local_augmented_keys(
            scope_nodes, fn_key_paths, fn_union_paths, resolver, parents))
    paths: set[tuple[str, ...]] | None = None
    opaque: set[tuple[str, ...]] | None = None
    for sub in _contract_return_nodes(scope_nodes):
        got = _return_value_paths(
            sub.value, var_assigned, var_literals, var_opaque)
        if got is None:
            return None
        if isinstance(sub.value, ast.Name):
            var = sub.value.id
            base_write, base = _wm01_literal_base_write(scope_nodes, var)
            if (var in param_names and not _wm01_write_dominates(
                    base_write, sub, parents, [base_write])):
                # 形参实参可能原样返回：键集取决于调用方，契约未知。
                return None
            # 该名在本作用域仅有这一次字面量绑定，return 能带值返回，
            # 基赋值就必然已执行、基键恒成立；循环/if/with 体内的
            # 基赋值不因支配判定保守否决而塌缩成空契约。
            guaranteed: set[tuple[str, ...]] = set(base.keys & got[0])
            guaranteed_opaque: set[tuple[str, ...]] = set(
                base.opaque & got[1])
            guaranteed.update(
                path for path in got[0]
                if _wm01_writes_guarantee(
                    local_writes, var, path, sub, parents))
            guaranteed_opaque.update(
                path for path in got[1]
                if _wm01_writes_guarantee(
                    local_writes, var, path, sub, parents))
            got = guaranteed, guaranteed_opaque
        if paths is None:
            paths = set(got[0])
            opaque = set(got[1])
        else:
            paths.intersection_update(got[0])
            opaque.intersection_update(got[1])
    if paths is None or opaque is None:
        return None
    return paths, opaque
def _wm01_refine_fn_contracts(
        tree: ast.AST,
        fn_key_paths: dict[str, set[tuple[str, ...]]],
        fn_opaque: dict[str, set[tuple[str, ...]]],
        fn_union_paths: dict[str, set[tuple[str, ...]] | None],
        per_def: dict[str, list[tuple[bool, _FnContract | None]]],
) -> None:
    parents = build_parent_map(tree)
    refined_paths: dict[str, set[tuple[str, ...]]] = {}
    refined_opaque: dict[str, set[tuple[str, ...]]] = {}
    indexes: dict[str, int] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, SCOPE_CONTAINERS) or isinstance(node, ast.Module):
            continue
        fname = getattr(node, 'name', None)
        if not fname:
            continue
        contract = _wm01_refined_scope_contract(
            node, fn_key_paths, fn_union_paths, parents)
        index = indexes.get(fname, 0)
        is_method, _old_contract = per_def[fname][index]
        per_def[fname][index] = is_method, contract
        indexes[fname] = index + 1
        if contract is not None:
            _merge_fn_paths(
                fname, contract, refined_paths, refined_opaque)
    fn_key_paths.clear()
    fn_key_paths.update(refined_paths)
    fn_opaque.clear()
    fn_opaque.update(refined_opaque)
@dataclass(frozen=True)
class _Wm01Run:
    fn_key_paths: dict[str, set[tuple[str, ...]]]
    fn_opaque: dict[str, set[tuple[str, ...]]]
    param_bindings: dict[str, str]
    issues: list[dict[str, Any]]
    filepath: Any
    src_lines: list[str]
    seen: set[tuple[str, tuple[str, ...], int]]
    fn_defs: dict[str, list[ast.FunctionDef | ast.AsyncFunctionDef]]
    parents: dict[int, ast.AST] = field(default_factory=dict)
    fn_union_paths: dict[str, set[tuple[str, ...]] | None] = field(
        default_factory=dict)
def check_WM01(tree: Any, source: Any, filepath: Any) -> list[dict[str, Any]]:
    if finding_scan_exempt(filepath):
        return []
    issues: list[dict[str, Any]] = []
    if not isinstance(tree, ast.AST):
        return issues
    fn_key_paths, fn_opaque, fn_union_paths = collect_fn_key_paths(tree)
    if not fn_key_paths:
        return issues
    per_def = collect_fn_key_paths_per_def(tree)
    _wm01_refine_fn_contracts(
        tree, fn_key_paths, fn_opaque, fn_union_paths, per_def)
    _wm01_drop_ambiguous(fn_key_paths, fn_opaque, per_def)
    for _ambiguous in (
            name for name in list(fn_union_paths)
            if name not in fn_key_paths):
        del fn_union_paths[_ambiguous]
    run = _Wm01Run(
        fn_key_paths=fn_key_paths,
        fn_opaque=fn_opaque,
        param_bindings=_wm01_param_bindings(tree, fn_key_paths, fn_opaque),
        issues=issues,
        filepath=filepath,
        src_lines=source_lines(source),
        seen=set(),
        fn_defs=_free_fn_definitions(tree),
        parents=build_parent_map(tree),
        fn_union_paths=fn_union_paths,
    )
    for container in walk_nodes(tree):
        if isinstance(container, _WRITE_SCOPE_CONTAINERS):
            _wm01_scan_container(container, run)
    _log_detector_findings("WM-01", "键名契约断裂", issues, filepath)
    return issues
def _wm01_shadowed_fns(container: ast.AST,
                       contract_names: set[str]) -> frozenset[str]:
    if not isinstance(container, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef, ast.Lambda)):
        return frozenset()
    own = getattr(container, 'name', None)
    return frozenset(
        (scope_local_bindings(container) & contract_names) - {own})
def _wm01_scan_container(container: ast.AST, run: _Wm01Run) -> None:
    nodes = iter_direct_scope(container)
    cname = getattr(container, 'name', None)
    bound_fn = run.param_bindings.get(cname or '', '')
    resolver = flow_var_resolver(
        nodes, run.fn_key_paths,
        preset=_wm01_param_preset(
            container, bound_fn,
            is_method=_wm01_is_method(container, run.parents)))
    (local_keys, local_opaque, poison_writes, local_writes) = (
        _wm01_local_augmented_keys(
            nodes, run.fn_key_paths, run.fn_union_paths,
            resolver, run.parents))
    scan = _Wm01Scan(
        fn_key_paths=run.fn_key_paths,
        fn_opaque=run.fn_opaque,
        exempt=_wm01_presence_exempt(nodes),
        post_guards=_wm01_post_guards(nodes),
        parents=run.parents,
        local_keys=local_keys,
        local_opaque=local_opaque,
        local_writes=local_writes,
        poison_writes=poison_writes,
        resolver=resolver,
        issues=run.issues,
        filepath=run.filepath,
        src_lines=run.src_lines,
        seen=run.seen,
        fn_defs=run.fn_defs,
        fn_union_paths=run.fn_union_paths,
        shadowed_fns=_wm01_shadowed_fns(container, set(run.fn_key_paths)),
    )
    for node in scope_body_stmts(container):
        _wm01_scan_expr(node, scan)
WRITE_DIRECT_CHECKS: dict[str, Callable[..., Any]] = {
    'WM-01': check_WM01,
    'DC-05': check_DC05,
    'NL-01': check_NL01,
    'EF-01': check_EF01,
}
def wiring_declarations() -> dict:
    return {"registry": {
        rule_id.replace("-", ""): check_fn
        for rule_id, check_fn in WRITE_DIRECT_CHECKS.items()
    }}

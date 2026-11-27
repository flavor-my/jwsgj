from __future__ import annotations

import ast
import logging
import re
import weakref
from collections.abc import Callable, Iterator
from dataclasses import dataclass
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_bindings import (
    build_scope_index,
    collect_binding_names,
    collect_shadow_bindings,
    exec_scope_declarations,
    module_fallback_shadowed,
    owner_scope,
)
from jwsgj.diag_shared_ast_nodes import (
    MATCH_CAPTURE_NODES,
    MATCH_REST_NODES,
    build_parent_map,
    flatten_unpack_targets,
    import_alias_bound_name,
    is_main_check,
    iter_def_site_nodes,
    iter_unpack_target_names,
    resolve_call_name,
)
from jwsgj.diag_shared_ast_views import cached_tree_view, tree_nodes
from jwsgj.diag_taint_model import (
    _TRY_NODE_TYPES,
    ASSIGN_NODES,
    TaintNameResolution,
    _element_binding_pairs,
    _iter_value_channel_nodes,
    _taint_attr_chain,
    assignment_form,
    taint_root_name,
    taint_source_of,
)
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    'ORIGIN_CALLS',
    'SCALAR_SANITIZER_CALLS',
    'TAINT_SOURCE_ATTRS',
    'TAINT_SOURCE_CALLS',
    'PreciseTaintAnalyzer',
    'ScopeFacts',
    'collect_regex_guards',
    'collect_sanitized_keys',
    'collect_scalar_sanitized_vars',
    'collect_scope_facts',
    'collect_source_taints',
    'is_sanitized',
    'iter_expr_origins',
    'lookup_name_assignment',
    'propagate_taints',
    'resolve_taint_source',
    'scope_visible_taints',
]
logger = logging.getLogger(__name__)
logger.info("diag_taint_dataflow 已加载: %d 项导出", len(__all__))
_DEFAULT_SCOPE = ""
_BINDING_FORM_NODES = ASSIGN_NODES + (
    ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
    ast.Match, ast.comprehension,
)
def _node_pos(node: ast.AST) -> tuple[int, int]:
    return getattr(node, "lineno", 0) or 0, getattr(node, "col_offset", 0) or 0
def _node_end_pos(node: ast.AST) -> tuple[int, int]:
    end_col = getattr(node, "end_col_offset", None)
    if end_col is None:
        end_col = getattr(node, "col_offset", 0) or 0
    return (getattr(node, "end_lineno", None) or getattr(node, "lineno", 0) or 0,
            end_col)
def _call_name_matches(node: ast.Call, names: set,
                       call_name_candidates=None) -> bool:
    if call_name_candidates is None:
        return resolve_call_name(node) in names
    return any(name in names for name in call_name_candidates(node) or ())
def _is_purifying_call(node: ast.Call, names, call_name_candidates=None,
                       tree: ast.AST | None = None) -> bool:
    custom_names = frozenset(names) - SCALAR_SANITIZER_CALLS
    return (_is_scalar_sanitizer_call(node, tree)
            or _call_name_matches(node, custom_names, call_name_candidates))
@dataclass(frozen=True)
class _FlowRegion:
    start: tuple[int, int]
    end: tuple[int, int]
    join_end: tuple[int, int]
    scope: str
    tail_spans: tuple[tuple[tuple[int, int], tuple[int, int]], ...] = ()
    loop_body: bool = False
    header_binding: bool = False
def _scope_within(scope: str, ancestor: str) -> bool:
    return not ancestor or scope == ancestor or scope.startswith(ancestor + ".")
def _entry_region(entry):
    return entry[3] if len(entry) > 3 else None
def _entry_writer_scope(entry) -> str:
    if len(entry) > 4:
        return entry[4]
    _region = _entry_region(entry)
    return _region.scope if _region is not None else _DEFAULT_SCOPE
def _pos_in_span(pos: tuple[int, int], span: tuple[tuple[int, int],
                                                 tuple[int, int]]) -> bool:
    return span[0] <= pos <= span[1]
_FUNCTION_CALL_CACHE: weakref.WeakKeyDictionary[ast.AST, tuple] = (
    weakref.WeakKeyDictionary())
def _own_function_has_yield(node: ast.AST) -> bool:
    stack = ([node.body] if isinstance(node, ast.Lambda)
             else list(node.body))
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(current, (ast.Yield, ast.YieldFrom)):
            return True
        stack.extend(ast.iter_child_nodes(current))
    return False
def _expression_runs_when_statement_runs(
        node: ast.AST, parents: dict[int, ast.AST]) -> bool:
    current = node
    while True:
        parent = parents.get(id(current))
        if parent is None or isinstance(parent, ast.stmt):
            return True
        if isinstance(parent, ast.BoolOp):
            if any(value is current for value in parent.values[1:]):
                return False
        elif isinstance(parent, ast.IfExp):
            if current is not parent.test:
                return False
        elif isinstance(parent, ast.Compare):
            if current is not parent.left and current is not parent.comparators[0]:
                return False
        elif isinstance(parent, (ast.ListComp, ast.SetComp,
                                 ast.GeneratorExp, ast.DictComp)):
            if current is not parent.generators[0].iter:
                return False
        elif isinstance(parent, ast.Lambda) and current is parent.body:
            return True
        current = parent
def _enclosing_lambda_body(
        node: ast.AST, parents: dict[int, ast.AST]) -> ast.Lambda | None:
    current = node
    while True:
        parent = parents.get(id(current))
        if parent is None:
            return None
        if isinstance(parent, ast.Lambda):
            if current is parent.body:
                return parent
        elif (isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef))
              and current in parent.body):
            return None
        current = parent
def _lambda_call_view(tree: ast.AST, scope_idx: dict[int, str],
                      parents: dict[int, ast.AST], shadow: tuple) -> tuple:
    local, global_names, class_scopes = shadow
    def _scope_of(node: ast.AST) -> str:
        registered = scope_idx.get(id(node))
        if registered is not None:
            return registered
        current = node
        while True:
            parent = parents.get(id(current))
            if parent is None:
                return ""
            if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.ClassDef)):
                enclosing = scope_idx.get(id(parent), "")
                return (f"{enclosing}.{parent.name}"
                        if enclosing else parent.name)
            current = parent
    def _writer(scope: str, name: str) -> str:
        owner = owner_scope(scope, name, local, global_names, class_scopes)
        return f"{owner}.{name}" if owner else name
    writers: dict[int, tuple[str, ...]] = {}
    bindings: dict[str, ast.Lambda] = {}
    scope_bindings: dict[int, tuple] = {}
    immediate_calls: list[tuple[str, tuple[int, int], str]] = []
    deferred: set[str] = set()
    for node in tree_nodes(tree):
        if not isinstance(node, ast.Lambda):
            continue
        parent = parents.get(id(node))
        scope = _scope_of(node)
        targets: list[ast.AST] = []
        if isinstance(parent, ast.Assign) and parent.value is node:
            targets = list(parent.targets)
        elif isinstance(parent, ast.AnnAssign) and parent.value is node:
            targets = [parent.target]
        names: list[str] = []
        for target in targets:
            if isinstance(target, ast.Name):
                writer = _writer(scope, target.id)
                if writer not in names:
                    names.append(writer)
        if not names:
            names.append(f"<lambda@{node.lineno}:{node.col_offset}>")
        else:
            for writer in names:
                bindings[writer] = node
        writers[id(node)] = tuple(names)
        scope_bindings[id(node)] = exec_scope_declarations(node)
        if _own_function_has_yield(node):
            deferred.update(names)
        if (isinstance(parent, ast.Call) and parent.func is node
                and _flow_region_for(parent, parents, scope_idx) is None
                and _expression_runs_when_statement_runs(parent, parents)):
            immediate_calls.append((names[0], _node_pos(parent), scope))
    alias_nodes = sorted(
        (node for node in tree_nodes(tree)
         if isinstance(node, (ast.Assign, ast.AnnAssign))
         and isinstance(node.value, ast.Name)),
        key=_node_pos)
    for node in alias_nodes:
        scope = _scope_of(node)
        lambda_node = bindings.get(_writer(scope, node.value.id))
        if lambda_node is None:
            continue
        targets = node.targets if isinstance(node, ast.Assign) else [node.target]
        for target in targets:
            if not isinstance(target, ast.Name):
                continue
            writer = _writer(scope, target.id)
            bindings[writer] = lambda_node
            if writer not in writers[id(lambda_node)]:
                writers[id(lambda_node)] = (*writers[id(lambda_node)], writer)
                if _own_function_has_yield(lambda_node):
                    deferred.add(writer)
    return (writers, tuple(immediate_calls), frozenset(deferred),
            scope_bindings)
def _build_function_call_view(tree: ast.AST) -> tuple:
    scope_idx = build_scope_index(tree)
    shadow = _shadow_of(tree)
    local, global_names, class_scopes = shadow
    parents = build_parent_map(tree)
    deferred_scopes: set[str] = set()
    for node in tree_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if (isinstance(node, ast.FunctionDef)
                and not _own_function_has_yield(node)):
            continue
        enclosing = scope_idx.get(id(node), "")
        deferred_scopes.add(
            f"{enclosing}.{node.name}" if enclosing else node.name)
    (lambda_writers, immediate_calls, lambda_deferred,
     lambda_scope_bindings) = _lambda_call_view(
        tree, scope_idx, parents, shadow)
    deferred_scopes.update(lambda_deferred)
    calls: dict[str, list[tuple[tuple[int, int], str]]] = {}
    for writer, pos, scope in immediate_calls:
        calls.setdefault(writer, []).append((pos, scope))
    for node in tree_nodes(tree):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)):
            continue
        if (_flow_region_for(node, parents, scope_idx) is not None
                or not _expression_runs_when_statement_runs(node, parents)):
            continue
        scope = scope_idx.get(id(node), "")
        owner = owner_scope(
            scope, node.func.id, local, global_names, class_scopes)
        writer = f"{owner}.{node.func.id}" if owner else node.func.id
        lambda_node = _enclosing_lambda_body(node, parents)
        if lambda_node is not None:
            lambda_local, lambda_global = lambda_scope_bindings[id(lambda_node)]
            if node.func.id in lambda_local and node.func.id not in lambda_global:
                continue
            callers = lambda_writers[id(lambda_node)]
        else:
            callers = (scope,)
        for caller in callers:
            calls.setdefault(writer, []).append((_node_pos(node), caller))
    call_map = {writer: tuple(sorted(positions, key=lambda item: item[0]))
                for writer, positions in calls.items()}
    return call_map, frozenset(deferred_scopes)
def _external_clean_executed(entry, writer: str, pos: tuple[int, int],
                             scope: str) -> bool:
    tree = entry[5] if len(entry) > 5 else None
    if tree is None:
        return False
    class_scopes = _shadow_of(tree)[2]
    if writer in class_scopes:
        return True
    calls, deferred_scopes = cached_tree_view(
        _FUNCTION_CALL_CACHE, tree, _build_function_call_view)
    def _executed(target: str, visiting: frozenset[str]) -> bool:
        if target in visiting or target in deferred_scopes:
            return False
        next_visiting = visiting | {target}
        for call_pos, caller in calls.get(target, ()):
            if call_pos > pos:
                continue
            if (not caller or caller in class_scopes
                    or _scope_within(scope, caller)):
                return True
            if _executed(caller, next_visiting):
                return True
        return False
    return _executed(writer, frozenset())
def _timeline_entry_applies(entry, pos: tuple[int, int], scope: str) -> bool:
    region = _entry_region(entry)
    if region is None:
        if not entry[2]:
            return True
        writer = _entry_writer_scope(entry)
        return (not writer or _scope_within(scope, writer)
                or _external_clean_executed(entry, writer, pos, scope))
    in_region = region.start <= pos <= region.end
    if entry[2]:
        return in_region and scope == region.scope
    return (_scope_within(scope, region.scope)
            and (in_region or pos > region.join_end
                 or scope != region.scope
                 or any(_pos_in_span(pos, _span)
                        for _span in region.tail_spans)))
def _entry_reaches_forward(entry, pos: tuple[int, int], scope: str) -> bool:
    _region = _entry_region(entry)
    if entry[2]:
        return bool(
            _region is not None and _region.header_binding
            and _region.start <= pos <= _region.end)
    if _region is not None and _region.loop_body:
        return _region.start <= pos <= _region.end
    _writer = _entry_writer_scope(entry)
    return scope != _writer and _scope_within(scope, _writer)
def _sanitized_before(sanitized_keys: dict, key: tuple[str, str],
                      pos: tuple[int, int], scope: str = _DEFAULT_SCOPE) -> bool:
    _timeline = sanitized_keys.get(key)
    if not _timeline:
        return False
    _latest = None
    for _entry in _timeline:
        _entry_pos = (_entry[0], _entry[1])
        if (_entry_pos >= pos
                and not _entry_reaches_forward(_entry, pos, scope)):
            continue
        if not _timeline_entry_applies(_entry, pos, scope):
            continue
        if _latest is None or _entry_pos >= (_latest[0], _latest[1]):
            _latest = _entry
    return bool(_latest and _latest[2])
@dataclass(frozen=True)
class _RoundState:
    key_resolver: object
    tainted_vars: dict
    taint_hops: dict
    taint_origins: dict | None
    shadow: tuple
    new_tainted: dict
@dataclass(frozen=True)
class _SourceCtx:
    tree: ast.AST
    report: object
    source_names: set
    shadow: tuple
    tainted_vars: dict
    taint_hops: dict
    taint_origins: dict | None
    call_name_candidates: object = None
def _pattern_capture_name(target: ast.AST) -> str | None:
    if isinstance(target, MATCH_CAPTURE_NODES):
        return target.name
    if isinstance(target, MATCH_REST_NODES):
        return target.rest
    return None

def _iter_binding_target_names(targets) -> Iterator[str]:
    for target in flatten_unpack_targets(targets):
        if isinstance(target, ast.Name):
            yield target.id
            continue
        name = _pattern_capture_name(target)
        if name:
            yield name

def _iter_owner_keys(targets, scope: str, shadow):
    for target in flatten_unpack_targets(targets):
        root_name = _pattern_capture_name(target) or taint_root_name(target)
        if root_name is not None:
            yield TaintNameResolution.owner_key(scope, root_name, shadow)
def _register_source_targets(targets, scope: str, lineno: int, hop: int,
                              origin_name: str, ctx: _SourceCtx) -> None:
    for key in _iter_owner_keys(targets, scope, ctx.shadow):
        ctx.tainted_vars[key] = lineno
        ctx.taint_hops[key] = hop
        if ctx.taint_origins is not None:
            ctx.taint_origins[key] = origin_name
def _sequence_values(patterns: list, value: ast.AST) -> list[tuple]:
    if not isinstance(value, (ast.Tuple, ast.List)):
        return [(sub, value) for sub in patterns]
    elements = list(value.elts)
    starred = [index for index, sub in enumerate(patterns)
               if isinstance(sub, (ast.MatchStar, ast.Starred))]
    if not starred:
        if len(patterns) != len(elements):
            return [(sub, value) for sub in patterns]
        return list(zip(patterns, elements, strict=True))
    if len(starred) != 1 or len(elements) < len(patterns) - 1:
        return [(sub, value) for sub in patterns]
    index = starred[0]
    trailing = len(patterns) - index - 1
    middle_end = len(elements) - trailing
    middle = ast.copy_location(ast.Tuple(
        elts=elements[index:middle_end], ctx=ast.Load()), value)
    aligned = [*elements[:index], middle, *elements[middle_end:]]
    return list(zip(patterns, aligned, strict=True))

_UNKNOWN_MATCH_KEY = object()

def _match_literal_key(node: ast.AST):
    try:
        return ast.literal_eval(node)
    except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):
        return _UNKNOWN_MATCH_KEY

def _match_mapping_values(pattern: ast.AST, value: ast.AST) -> tuple[list, ast.AST]:
    pairs = list(zip(pattern.keys, pattern.patterns, strict=True))
    known_items = None
    if isinstance(value, ast.Dict) and all(key is not None for key in value.keys):
        candidate = [(_match_literal_key(key), key, item)
                     for key, item in zip(value.keys, value.values, strict=True)]
        if all(key is not _UNKNOWN_MATCH_KEY for key, _key_node, _item in candidate):
            # Dict literals retain the last value for a duplicate key. Collapse
            # duplicates before projecting captures and the ``**rest`` mapping.
            known_items = []
            for item in candidate:
                existing = next(
                    (index for index, known_item in enumerate(known_items)
                     if known_item[0] == item[0]), None)
                if existing is None:
                    known_items.append(item)
                else:
                    known_items[existing] = item
    if known_items is None:
        return [(sub, value) for _key, sub in pairs], value
    projected = []
    matched_keys = []
    for key_node, sub in pairs:
        key = _match_literal_key(key_node)
        item = next((item for known_key, _key_node, item in known_items
                     if known_key == key), None)
        if item is not None:
            matched_keys.append(key)
        projected.append((sub, value if item is None else item))
    remaining = [(key_node, item) for key, key_node, item in known_items
                 if key not in matched_keys]
    rest = ast.copy_location(ast.Dict(
        keys=[key_node for key_node, _item in remaining],
        values=[item for _key_node, item in remaining]), value)
    return projected, rest

def _match_binding_forms(pattern: ast.AST, value: ast.AST) -> list[tuple]:
    if isinstance(pattern, ast.MatchAs):
        forms = [([pattern], value)] if pattern.name else []
        if pattern.pattern is not None:
            forms.extend(_match_binding_forms(pattern.pattern, value))
        return forms
    if isinstance(pattern, ast.MatchStar):
        return [([pattern], value)] if pattern.name else []
    if isinstance(pattern, ast.MatchSequence):
        return [form for sub, sub_value in _sequence_values(
                    list(pattern.patterns), value)
                for form in _match_binding_forms(sub, sub_value)]
    if isinstance(pattern, ast.MatchMapping):
        pairs, rest = _match_mapping_values(pattern, value)
        forms = [form for sub, sub_value in pairs
                 for form in _match_binding_forms(sub, sub_value)]
        if pattern.rest:
            forms.append(([pattern], rest))
        return forms
    if isinstance(pattern, ast.MatchOr):
        captures = {}
        for sub in pattern.patterns:
            for targets, sub_value in _match_binding_forms(sub, value):
                target = targets[0]
                name = _pattern_capture_name(target)
                _target, values = captures.setdefault(name, (target, []))
                values.append(sub_value)
        return [([target], values[0] if len(values) == 1 else
                 ast.copy_location(ast.Tuple(elts=values, ctx=ast.Load()), value))
                for target, values in captures.values()]
    if isinstance(pattern, ast.MatchClass):
        return [form for sub in (*pattern.patterns, *pattern.kwd_patterns)
                for form in _match_binding_forms(sub, value)]
    return []

def _target_binding_forms(target: ast.AST, value: ast.AST) -> list[tuple]:
    if isinstance(target, ast.Starred):
        return _target_binding_forms(target.value, value)
    if not isinstance(target, (ast.Tuple, ast.List)):
        return [(target, value)]
    return [form for sub, sub_value in _sequence_values(list(target.elts), value)
            for form in _target_binding_forms(sub, sub_value)]

def _loop_binding_forms(target: ast.AST, iterable: ast.AST) -> list[tuple]:
    rows = (list(iterable.elts)
            if isinstance(iterable, (ast.Tuple, ast.List)) else [iterable])
    columns: dict[ast.AST, list[ast.AST]] = {}
    for row in rows:
        for sub, sub_value in _target_binding_forms(target, row):
            columns.setdefault(sub, []).append(sub_value)
    return [([sub], ast.copy_location(ast.Tuple(
        elts=values, ctx=ast.Load()), iterable))
            for sub, values in columns.items()]

def _binding_forms(node: ast.AST):
    if isinstance(node, (ast.For, ast.AsyncFor, ast.comprehension)):
        return _loop_binding_forms(node.target, node.iter)
    pair = assignment_form(node)
    if pair is not None:
        return [pair]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [([item.optional_vars], item.context_expr)
                for item in node.items if item.optional_vars is not None]
    if isinstance(node, ast.Match):
        return [form for case in node.cases
                for form in _match_binding_forms(case.pattern, node.subject)]
    return []
def _scope_binding_forms(node: ast.AST, scope: str, shadow: tuple) -> list[tuple]:
    """会绑定到 ``scope``（节点所在外层作用域）的绑定形态。

    ``_binding_forms`` 把 ``ast.comprehension`` 也当作合法绑定形态，但推导式
    目标是推导式自身的局部变量（Python 3 为独立作用域），对外层同名变量不赋值；
    且该节点未注册进 ``build_scope_index``，登记时作用域与位置均回落到模块
    ``""``。若照单全收，``x = "safe"; y = [x for x in [input()]]`` 会把模块
    ``x`` 的污点/净化状态改写成 ``input``，使后面的 ``os.system(x)`` 误报。
    这里对 comprehension 只保留外层任一作用域都没有（非推导式）绑定的名字
    （纯推导式局部名，如 ``[c for c in [input()]]``，用于检出推导式内部的
    汇点）；推导式结果的值通道由 ``_iter_value_channel_nodes`` 经 ``elt`` 与各
    ``generator.iter`` 覆盖，不依赖这里的登记。
    """
    forms = _binding_forms(node)
    if not isinstance(node, ast.comprehension) or not forms:
        return forms
    local_bindings, global_names, _class_scopes = shadow
    kept: list[tuple] = []
    for targets, value in forms:
        _shadowed = any(
            owner_scope(scope, _name, local_bindings, global_names,
                        _class_scopes) != ""
            or _name in local_bindings.get("", frozenset())
            or _name in global_names.get("", frozenset())
            for _name in _iter_binding_target_names(targets))
        if not _shadowed:
            kept.append((targets, value))
    return kept
def _register_element_source(targets, value, scope: str, lineno: int,
                             ctx: _SourceCtx) -> bool:
    direct_name = taint_source_of(
        value, ctx.source_names,
        call_name_candidates=ctx.call_name_candidates)
    if direct_name is not None:
        _register_source_targets(
            targets, scope, lineno, 1, direct_name, ctx)
        return True
    for sub in _iter_value_channel_nodes(
            value,
            prune=lambda _c: _is_scalar_sanitizer_call(_c, ctx.tree)):
        sub_name = taint_source_of(
            sub, ctx.source_names,
            call_name_candidates=ctx.call_name_candidates)
        if sub_name is not None:
            _register_source_targets(
                targets, scope, lineno, 2, sub_name, ctx)
            return True
    return False
def collect_source_taints(tree, source_names, report,
                           taint_origins: dict | None = None, *,
                           scope_idx: dict[int, str],
                           shadow: tuple[dict, dict, frozenset] | None = None,
                           call_name_candidates=None):
    _shadow = _shadow_for(tree, shadow)
    tainted_vars: dict[tuple[str, str], int] = {}
    taint_hops: dict[tuple[str, str], int] = {}
    ctx = _SourceCtx(tree=tree, report=report, source_names=source_names,
                     shadow=_shadow, tainted_vars=tainted_vars,
                     taint_hops=taint_hops, taint_origins=taint_origins,
                     call_name_candidates=call_name_candidates)
    for node in walk_nodes(tree):
        _scope = scope_idx.get(id(node), "")
        _pairs = _scope_binding_forms(node, _scope, _shadow)
        if not _pairs:
            continue
        for _targets, _value in _pairs:
            _source_hits = 0
            for _bound_targets, _bound_value in _element_binding_pairs(
                    _targets, _value):
                _source_hits += int(_register_element_source(
                    _bound_targets, _bound_value, _scope,
                    _node_pos(node)[0], ctx))
            ctx.report.total_sources += (
                min(_source_hits, 1) if len(_targets) > 1 else _source_hits)
    return tainted_vars, taint_hops
def _next_hop(state: _RoundState, rhs_hits: set) -> int:
    return min(state.taint_hops.get(k, 1) for k in rhs_hits) + 1
def _pick_hit_origin(state: _RoundState, rhs_hits: set) -> str:
    candidates = sorted(
        (state.taint_hops.get(_k, 1), state.taint_origins[_k])
        for _k in rhs_hits if _k in state.taint_origins)
    return candidates[0][1] if candidates else ''
def _mark_new_taint(var_key: tuple[str, str], lineno: int, hop: int,
                     rhs_hits: set, state: _RoundState,
                     origin: str | None = None) -> None:
    state.new_tainted[var_key] = lineno
    state.taint_hops.setdefault(var_key, hop)
    if state.taint_origins is not None:
        state.taint_origins.setdefault(
            var_key,
            origin if origin is not None else _pick_hit_origin(
                state, rhs_hits))
def propagate_taints(tree, tainted_vars: dict, taint_hops: dict,
                      source_names: set, taint_origins: dict | None = None, *,
                      scope_idx: dict[int, str],
                      shadow: tuple[dict, dict, frozenset],
                      sanitized_keys: dict,
                      sanitizer_names: set,
                      call_name_candidates=None):
    _san_names = _purifying_call_names(sanitizer_names)
    def _taint_key_unsanitized(scope: str, name: str,
                               pos: tuple[int, int]):
        _k = TaintNameResolution.resolve_taint_key(
            scope, name, tainted_vars, shadow)
        if _k is None:
            return None
        if _sanitized_before(sanitized_keys, _k, pos, scope):
            return None
        return _k
    _plain_assigns, _aug_assigns, _mutations = (
        _collect_propagation_candidates(
            tree, scope_idx, source_names, _san_names,
            call_name_candidates=call_name_candidates, shadow=shadow))
    while True:
        state = _RoundState(
            key_resolver=_taint_key_unsanitized, tainted_vars=tainted_vars,
            taint_hops=taint_hops, taint_origins=taint_origins,
            shadow=shadow, new_tainted={})
        _propagate_plain_assigns_round(_plain_assigns, state)
        _propagate_aug_assigns_round(_aug_assigns, state)
        _propagate_mutations_round(_mutations, state)
        if not state.new_tainted:
            break
        tainted_vars.update(state.new_tainted)
def _propagate_to_targets(targets, scope: str, lineno: int,
                          hop: int, rhs_hits: set, state: _RoundState):
    for _tkey in _iter_owner_keys(targets, scope, state.shadow):
        if _tkey not in state.tainted_vars:
            _mark_new_taint(_tkey, lineno, hop, rhs_hits, state)
def _value_channel_names(value: ast.AST, sanitizer_names=(),
                         call_name_candidates=None,
                         tree: ast.AST | None = None) -> tuple:
    _names = frozenset(sanitizer_names)
    _prune = (None if not _names else
              lambda _c: _is_purifying_call(
                  _c, _names, call_name_candidates, tree))
    return tuple(_n.id for _n in _iter_value_channel_nodes(value, prune=_prune)
                 if isinstance(_n, ast.Name))
_PLAIN_FORM_NODES = tuple(
    _n for _n in _BINDING_FORM_NODES if _n is not ast.AugAssign)
_TAINING_MUTATION_METHODS = frozenset({
    'append', 'extend', 'insert', 'add', 'update', 'setdefault',
    'appendleft', 'extendleft',
})
def _collect_propagation_candidates(tree, scopes, source_names,
                                    san_names, call_name_candidates=None, *,
                                    shadow: tuple | None = None):
    _shadow = _shadow_for(tree, shadow)
    _plain_assigns: list[tuple] = []
    _aug_assigns: list[tuple[ast.AugAssign, str, tuple]] = []
    _mutations: list[tuple[str, tuple[int, int], list[tuple], str, str]] = []
    for _node in walk_nodes(tree):
        _n_scope = scopes.get(id(_node), "")
        if isinstance(_node, _PLAIN_FORM_NODES):
            _pos = _node_pos(_node)
            for _targets, _value in _scope_binding_forms(
                    _node, _n_scope, _shadow):
                _bindings = _element_binding_pairs(_targets, _value)
                for _bound_targets, _bound_value in _bindings:
                    if (isinstance(_bound_value, ast.Call)
                            and _call_name_matches(
                                _bound_value, source_names,
                                call_name_candidates)):
                        continue
                    _plain_assigns.append(
                        (_pos[0], _pos[1], _bound_targets, _n_scope,
                         _value_channel_names(
                             _bound_value, san_names, call_name_candidates,
                             tree=tree)))
            continue
        if isinstance(_node, ast.AugAssign):
            _aug_assigns.append(
                (_node, _n_scope, _value_channel_names(
                    _node.value, san_names, call_name_candidates, tree=tree)))
            continue
        if not (isinstance(_node, ast.Expr)
                and isinstance(_node.value, ast.Call)):
            continue
        _call = _node.value
        if (isinstance(_call.func, ast.Attribute)
                and _call.func.attr in _TAINING_MUTATION_METHODS):
            _collect_mutation_candidate(
                _node, _call, scopes, source_names, san_names, _mutations,
                call_name_candidates=call_name_candidates, tree=tree)
    return _plain_assigns, _aug_assigns, _mutations
def _first_direct_source(values, source_names, san_names,
                         call_name_candidates=None,
                         tree: ast.AST | None = None, *,
                         source_name_candidates=None,
                         resolve_imports: bool = False) -> str:
    source_candidates = (call_name_candidates if source_name_candidates is None
                         else source_name_candidates)
    for _arg in values:
        for _sub in _iter_value_channel_nodes(
                _arg,
                prune=lambda _c: _is_purifying_call(
                    _c, san_names, call_name_candidates, tree)):
            _src = taint_source_of(
                _sub, source_names,
                call_name_candidates=source_candidates)
            if not _src and resolve_imports:
                _src = resolve_taint_source(_sub, source_names, tree)
            if _src:
                return _src
    return ''
def _collect_mutation_candidate(_node, _call, scopes,
                                source_names, san_names, mutations,
                                call_name_candidates=None,
                                tree: ast.AST | None = None):
    _cont_root = taint_root_name(_call.func.value)
    if _cont_root is None:
        return
    _mut_vals = (*_call.args,
                 *(kw.value for kw in _call.keywords))
    _arg_names = [
        _value_channel_names(
            _arg, san_names, call_name_candidates=call_name_candidates,
            tree=tree)
        for _arg in _mut_vals]
    _direct_src = _first_direct_source(
        _mut_vals, source_names, san_names,
        call_name_candidates=call_name_candidates, tree=tree)
    _m_scope = scopes.get(id(_call), "")
    mutations.append(
        (_cont_root, (_node.lineno, _node.col_offset),
         _arg_names, _m_scope, _direct_src))
def _collect_rhs_hits(names, scope: str, pos: tuple[int, int],
                      key_resolver) -> set:
    hits: set = set()
    for name in names:
        key = key_resolver(scope, name, pos)
        if key is not None:
            hits.add(key)
    return hits
def _propagate_plain_assigns_round(_plain_assigns, state: _RoundState):
    for (_a_lineno, _a_col, _a_targets, _a_scope,
         _rhs_all) in _plain_assigns:
        rhs_hits = _collect_rhs_hits(
            _rhs_all, _a_scope, (_a_lineno, _a_col), state.key_resolver)
        if rhs_hits:
            _propagate_to_targets(
                _a_targets, _a_scope, _a_lineno, _next_hop(state, rhs_hits),
                rhs_hits, state)
def _propagate_aug_assigns_round(_aug_assigns, state: _RoundState):
    for aug_node, _g_scope, _rhs_all in _aug_assigns:
        rhs_hits = _collect_rhs_hits(
            _rhs_all, _g_scope,
            (aug_node.lineno, aug_node.col_offset), state.key_resolver)
        if not rhs_hits:
            continue
        _tname = (aug_node.target.id
                  if isinstance(aug_node.target, ast.Name)
                  else taint_root_name(aug_node.target))
        if _tname is None:
            continue
        _tkey = TaintNameResolution.owner_key(_g_scope, _tname, state.shadow)
        if _tkey in state.tainted_vars:
            continue
        _mark_new_taint(
            _tkey, aug_node.lineno, _next_hop(state, rhs_hits),
            rhs_hits, state)
def _propagate_mutations_round(_mutations, state: _RoundState):
    for _cont_root, _expr_pos, _arg_names_list, _m_scope, _direct_src in _mutations:
        _cont_key = TaintNameResolution.owner_key(_m_scope, _cont_root, state.shadow)
        if _cont_key in state.tainted_vars:
            continue
        if _direct_src:
            _mark_new_taint(_cont_key, _expr_pos[0], 1, (), state,
                             origin=_direct_src)
            continue
        _mut_hits: set = set()
        for _names in _arg_names_list:
            _mut_hits |= _collect_rhs_hits(
                _names, _m_scope, _expr_pos, state.key_resolver)
        if _mut_hits:
            _mark_new_taint(_cont_key, _expr_pos[0],
                            _next_hop(state, _mut_hits), _mut_hits, state)
def _purifying_call_names(sanitizer_names) -> frozenset[str]:
    return SCALAR_SANITIZER_CALLS | frozenset(sanitizer_names)
def _is_purifying_element(value: ast.AST, sanitizer_names: set,
                          call_name_candidates=None,
                          tree: ast.AST | None = None) -> bool:
    if _is_literal_value(value):
        return True
    return (isinstance(value, ast.Call)
            and _is_purifying_call(
                value, sanitizer_names, call_name_candidates, tree))
def _is_purifying_value(value: ast.AST, sanitizer_names: set,
                        call_name_candidates=None,
                        tree: ast.AST | None = None) -> bool:
    if isinstance(value, ast.Call):
        return _is_purifying_call(
            value, sanitizer_names, call_name_candidates, tree)
    if isinstance(value, (ast.Tuple, ast.List, ast.Set)):
        return bool(value.elts) and all(
            _is_purifying_element(
                e, sanitizer_names, call_name_candidates, tree)
            for e in value.elts)
    if isinstance(value, ast.Dict):
        pairs = [k for k in value.keys if k is not None]
        pairs.extend(value.values)
        return bool(pairs) and all(
            _is_purifying_element(
                e, sanitizer_names, call_name_candidates, tree)
            for e in pairs)
    return False
def _is_literal_value(value: ast.AST) -> bool:
    try:
        ast.literal_eval(value)
    except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):  # jwsgj:silent-ok literal_eval 判字面量，非字面量即预期分支
        return False
    return True
def _is_clean_mutation(call: ast.Call, sanitizer_names: set,
                       call_name_candidates=None,
                       tree: ast.AST | None = None) -> bool:
    values = (*call.args, *(kw.value for kw in call.keywords))
    return all(
        _is_literal_value(value)
        or _is_purifying_value(
            value, sanitizer_names, call_name_candidates, tree)
        for value in values)
def _body_span(body: list[ast.stmt]) -> tuple[tuple[int, int],
                                            tuple[int, int]] | None:
    if not body:
        return None
    return _node_pos(body[0]), _node_end_pos(body[-1])
def _body_spans(bodies) -> tuple[tuple[tuple[int, int],
                                      tuple[int, int]], ...]:
    _span = _body_span(bodies)
    return (_span,) if _span is not None else ()
def _handler_spans(node: ast.AST) -> tuple[tuple[tuple[int, int],
                                               tuple[int, int]], ...]:
    spans: list[tuple[tuple[int, int], tuple[int, int]]] = []
    for _handler in getattr(node, "handlers", ()):
        spans.extend(_body_spans(_handler.body))
    return tuple(spans)
def _region_for_body(
        body: list[ast.stmt], scope: str, join_end: tuple[int, int], *,
        tail_spans: tuple[tuple[tuple[int, int], tuple[int, int]], ...] = (),
        loop_body: bool = False,
) -> _FlowRegion | None:
    _span = _body_span(body)
    if _span is None:
        return None
    return _FlowRegion(
        _span[0], _span[1], join_end, scope, tail_spans, loop_body)
def _flow_region_for(node: ast.AST, parents: dict[int, ast.AST],
                     scope_idx: dict[int, str]) -> _FlowRegion | None:
    node_scope = scope_idx.get(id(node), "")
    if isinstance(node, ast.comprehension):
        parent = parents.get(id(node))
        if isinstance(parent, (ast.ListComp, ast.SetComp,
                               ast.GeneratorExp, ast.DictComp)):
            end = _node_end_pos(parent)
            return _FlowRegion(
                _node_pos(parent), end, end, node_scope,
                loop_body=True, header_binding=True)
    current = node
    while True:
        parent = parents.get(id(current))
        if parent is None:
            return None
        if (isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef))
                and current in parent.body):
            return None
        if isinstance(parent, ast.Lambda) and current is parent.body:
            return None
        join_end = _node_end_pos(parent)
        scope = scope_idx.get(id(parent), node_scope)
        body = None
        tail_spans: tuple[tuple[tuple[int, int], tuple[int, int]], ...] = ()
        loop_body = False
        if isinstance(parent, (ast.If, ast.With, ast.AsyncWith)):
            if current in parent.body:
                body = parent.body
            elif current in getattr(parent, "orelse", ()):
                body = parent.orelse
        elif isinstance(parent, (ast.For, ast.AsyncFor, ast.While)):
            if current in parent.body:
                body = parent.body
                loop_body = True
                tail_spans = _body_spans(parent.orelse)
            elif current in parent.orelse:
                body = parent.orelse
        elif isinstance(parent, _TRY_NODE_TYPES):
            if current in parent.body:
                body = parent.body
                tail_spans = (*_handler_spans(parent),
                              *_body_spans(parent.orelse),
                              *_body_spans(parent.finalbody))
            elif current in parent.orelse:
                body = parent.orelse
                tail_spans = _body_spans(parent.finalbody)
            elif current in parent.finalbody:
                body = parent.finalbody
            else:
                handler = next((item for item in parent.handlers
                                if current is item), None)
                if handler is not None:
                    body = handler.body
                    tail_spans = _body_spans(parent.finalbody)
        elif isinstance(parent, ast.Match):
            case = next((item for item in parent.cases
                         if current is item), None)
            if case is not None:
                body = case.body
        if body is not None:
            return _region_for_body(
                body, scope, join_end,
                tail_spans=tail_spans, loop_body=loop_body)
        current = parent
def _walrus_clean_region(node: ast.NamedExpr, parents: dict[int, ast.AST],
                         scope_idx: dict[int, str],
                         default_region: _FlowRegion | None,
                         ) -> tuple[_FlowRegion | None, bool]:
    on_true = True
    on_false = True
    saw_bool = False
    current: ast.AST = node
    while True:
        parent = parents.get(id(current))
        if parent is None:
            return default_region, on_true and on_false
        if isinstance(parent, ast.BoolOp):
            saw_bool = True
            index = next((i for i, value in enumerate(parent.values)
                          if value is current), 0)
            if index:
                if isinstance(parent.op, ast.And):
                    on_false = False
                else:
                    on_true = False
        elif isinstance(parent, ast.UnaryOp) and isinstance(parent.op, ast.Not):
            on_true, on_false = on_false, on_true
        elif (isinstance(parent, (ast.If, ast.While))
              and current is parent.test):
            if on_true and on_false:
                return default_region, True
            scope = scope_idx.get(id(parent), scope_idx.get(id(node), ""))
            if on_true:
                return _region_for_body(
                    parent.body, scope, _node_end_pos(parent),
                    loop_body=isinstance(parent, ast.While)), True
            if isinstance(parent, ast.If) and parent.orelse:
                return _region_for_body(
                    parent.orelse, scope, _node_end_pos(parent)), True
            return default_region, False
        elif isinstance(parent, (ast.ListComp, ast.SetComp,
                                 ast.GeneratorExp, ast.DictComp)):
            return default_region, False
        elif isinstance(parent, (ast.stmt, ast.Lambda, ast.ClassDef,
                                 ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.Module)):
            return default_region, on_true and on_false
        elif saw_bool:
            return default_region, False
        current = parent
def _update_target_timeline(scope: str, targets, pos: tuple[int, int],
                              is_san: bool,
                              sanitized_keys: dict[tuple[str, str], list],
                              shadow: tuple[dict, dict, frozenset] | None,
                              region: _FlowRegion | None = None,
                              tree: ast.AST | None = None) -> None:
    for _k in _iter_owner_keys(targets, scope, shadow):
        sanitized_keys.setdefault(_k, []).append(
            (pos[0], pos[1], is_san, region, scope, tree))
def _binds_whole_value(target) -> bool:
    if isinstance(target, ast.Name) or _pattern_capture_name(target):
        return True
    if isinstance(target, ast.Starred):
        return _binds_whole_value(target.value)
    if isinstance(target, (ast.Tuple, ast.List)):
        return all(_binds_whole_value(elt) for elt in target.elts)
    return False
def _normalize_timeline(entries: list) -> list:
    entries.sort(key=lambda _e: (_e[0], _e[1]))
    timeline: list = []
    for _e in entries:
        if timeline and (timeline[-1][0], timeline[-1][1]) == (_e[0], _e[1]):
            if not _e[2]:
                timeline[-1] = _e
            continue
        timeline.append(_e)
    return timeline
def _collect_mutation_timeline(node: ast.Expr, scope_idx: dict[int, str],
                               pur_names: frozenset[str],
                               sanitized_keys: dict, shadow,
                               call_name_candidates=None,
                               region: _FlowRegion | None = None,
                               tree: ast.AST | None = None) -> None:
    _call = node.value
    if not (isinstance(_call.func, ast.Attribute)
            and _call.func.attr in _TAINING_MUTATION_METHODS
            and not _is_clean_mutation(
                _call, pur_names, call_name_candidates, tree)):
        return
    _update_target_timeline(
        scope_idx.get(id(_call), ""), [_call.func.value],
        _node_pos(node), False, sanitized_keys, shadow, region, tree=tree)
def _is_clean_binding_value(value: ast.AST, scope: str,
                            pos: tuple[int, int], pur_names: frozenset[str],
                            sanitized_keys: dict, shadow,
                            call_name_candidates=None,
                            tree: ast.AST | None = None) -> bool:
    if isinstance(value, ast.NamedExpr):
        return _is_clean_binding_value(
            value.value, scope, pos, pur_names, sanitized_keys, shadow,
            call_name_candidates, tree)
    if isinstance(value, ast.Name):
        key = TaintNameResolution.resolve_taint_key(
            scope, value.id, sanitized_keys, shadow)
        return (key is not None and _sanitized_before(
            sanitized_keys, key, pos, scope))
    return (_is_purifying_value(
                value, pur_names, call_name_candidates, tree)
            or _is_literal_value(value))
def _augmented_targets_are_clean(targets, scope: str,
                                 pos: tuple[int, int], sanitized_keys: dict,
                                 shadow) -> bool:
    keys = tuple(_iter_owner_keys(targets, scope, shadow))
    return bool(keys) and all(
        _sanitized_before(sanitized_keys, key, pos, scope) for key in keys)
def _collect_binding_timeline(node: ast.AST, scope: str,
                              pur_names: frozenset[str],
                              sanitized_keys: dict, shadow,
                              call_name_candidates=None,
                              region: _FlowRegion | None = None,
                              tree: ast.AST | None = None,
                              allow_clean: bool = True,
                              forms: list[tuple] | None = None) -> None:
    for _targets, _value in (
            _scope_binding_forms(node, scope, shadow) if forms is None
            else forms):
        _eval_pos = _node_pos(_value)
        _activation_pos = _node_end_pos(_value)
        _bindings = _element_binding_pairs(_targets, _value)
        for _bound_targets, _bound_value in _bindings:
            _clean = _is_clean_binding_value(
                _bound_value, scope, _eval_pos, pur_names,
                sanitized_keys, shadow, call_name_candidates, tree)
            if _clean and isinstance(node, ast.AugAssign):
                _clean = _augmented_targets_are_clean(
                    _bound_targets, scope, _eval_pos, sanitized_keys, shadow)
            if _clean and not allow_clean:
                continue
            if not all(_binds_whole_value(target)
                       for target in _bound_targets):
                if not _clean:
                    _update_target_timeline(
                        scope, _bound_targets, _activation_pos, False,
                        sanitized_keys, shadow, region, tree=tree)
                continue
            _update_target_timeline(
                scope, _bound_targets, _activation_pos, _clean,
                sanitized_keys, shadow, region, tree=tree)
def collect_sanitized_keys(tree: ast.AST, sanitizer_names: set,
                            scope_idx: dict[int, str],
                            shadow: tuple[dict, dict, frozenset] | None = None,
                            call_name_candidates=None,
                            ) -> dict[tuple[str, str], list]:
    sanitized_keys: dict[tuple[str, str], list] = {}
    _shadow = _shadow_for(tree, shadow)
    _pur_names = _purifying_call_names(sanitizer_names)
    _parents = build_parent_map(tree)
    for sn_node in walk_nodes(tree):
        _is_mutation = (isinstance(sn_node, ast.Expr)
                        and isinstance(sn_node.value, ast.Call))
        if not _is_mutation and not isinstance(sn_node, _BINDING_FORM_NODES):
            continue
        _region = _flow_region_for(sn_node, _parents, scope_idx)
        if _is_mutation:
            _collect_mutation_timeline(
                sn_node, scope_idx, _pur_names, sanitized_keys, _shadow,
                call_name_candidates=call_name_candidates, region=_region,
                tree=tree)
            continue
        if isinstance(sn_node, ast.Match):
            for case in sn_node.cases:
                _collect_binding_timeline(
                    sn_node, scope_idx.get(id(sn_node), ""), _pur_names,
                    sanitized_keys, _shadow,
                    call_name_candidates=call_name_candidates,
                    region=_flow_region_for(case.pattern, _parents, scope_idx),
                    tree=tree,
                    forms=_match_binding_forms(case.pattern, sn_node.subject))
            continue
        _allow_clean = True
        if isinstance(sn_node, ast.NamedExpr):
            _region, _allow_clean = _walrus_clean_region(
                sn_node, _parents, scope_idx, _region)
        _collect_binding_timeline(
            sn_node, scope_idx.get(id(sn_node), ""), _pur_names,
            sanitized_keys, _shadow,
            call_name_candidates=call_name_candidates, region=_region,
            tree=tree, allow_clean=_allow_clean)
    for _k, _entries in sanitized_keys.items():
        sanitized_keys[_k] = _normalize_timeline(_entries)
    return sanitized_keys
def _record_names(expr, sanitizer_names: set,
                  inline_cover: dict[str, list[bool]],
                  call_name_candidates=None,
                  tree: ast.AST | None = None) -> list[str]:
    if expr is None:
        return []
    if isinstance(expr, ast.Name):
        if not isinstance(expr.ctx, ast.Load):
            return []
        inline_cover.setdefault(expr.id, []).append(False)
        return [expr.id]
    _names: list[str] = []
    _stk: list[tuple[ast.AST, bool]] = [(expr, False)]
    while _stk:
        n, inside = _stk.pop()
        if isinstance(n, ast.Call):
            _push_call_children(
                n, inside, sanitizer_names, _stk, call_name_candidates, tree)
        elif isinstance(n, ast.Name):
            if not isinstance(n.ctx, ast.Load):
                continue
            inline_cover.setdefault(n.id, []).append(inside)
            _names.append(n.id)
        else:
            _stk.extend((c, inside) for c in ast.iter_child_nodes(n))
    return _names
def _push_call_children(node: ast.Call, inside: bool, sanitizer_names: set,
                        stack: list[tuple[ast.AST, bool]],
                        call_name_candidates=None,
                        tree: ast.AST | None = None) -> None:
    _sub = inside or _is_purifying_call(
        node, sanitizer_names, call_name_candidates, tree)
    if isinstance(node.func, ast.Attribute):
        stack.append((node.func.value, inside))
    elif isinstance(node.func, (ast.Call, ast.Subscript)):
        stack.append((node.func, inside))
    for kw in reversed(node.keywords):
        if kw.value is not None:
            stack.append((kw.value, _sub))
    for arg in reversed(node.args):
        stack.append((arg, _sub))
def _target_is_tainted(name: str, scope: str, tainted_vars: dict | None,
                       shadow) -> bool:
    if tainted_vars is None:
        return True
    return TaintNameResolution.resolve_taint_key(scope, name, tainted_vars, shadow) is not None
def _target_is_sanitized(name: str, scope: str, sink_node: ast.Call,
                         sanitized_keys: dict, shadow,
                         inline_cover: dict) -> bool:
    _k = TaintNameResolution.resolve_taint_key(scope, name, sanitized_keys, shadow)
    if _k is not None and _sanitized_before(
            sanitized_keys, _k,
            (sink_node.lineno, sink_node.col_offset), scope):
        return True
    _occ = inline_cover.get(name)
    return bool(_occ) and all(_occ)
def _collect_target_names(node: ast.Call, sanitizer_names: set,
                          inline_cover: dict, scope: str,
                          tainted_vars: dict | None, shadow,
                          call_name_candidates=None,
                          argument_nodes=None,
                          tree: ast.AST | None = None) -> list[str]:
    targets: list[str] = []
    arguments = ((*node.args, *(kw.value for kw in node.keywords))
                 if argument_nodes is None else argument_nodes)
    for arg in arguments:
        targets.extend(n for n in _record_names(
            arg, sanitizer_names, inline_cover, call_name_candidates, tree)
            if _target_is_tainted(n, scope, tainted_vars, shadow))
    return targets
def is_sanitized(node: ast.Call, tree=None, scope: str = _DEFAULT_SCOPE,
                  sanitized_keys: dict | None = None, shadow=None,
                  tainted_vars: dict | None = None,
                  *, sanitizer_names: set,
                  call_name_candidates=None,
                  argument_nodes=None, source_names=None,
                  source_name_candidates=None,
                  check_inline_sources: bool = True) -> bool:
    if shadow is None and tree is not None:
        shadow = _shadow_for(tree, shadow)
    if sanitized_keys is None:
        if tree is None:
            return False
        sanitized_keys = collect_sanitized_keys(
            tree, sanitizer_names, build_scope_index(tree), shadow,
            call_name_candidates=call_name_candidates)
    arguments = ((*node.args, *(kw.value for kw in node.keywords))
                 if argument_nodes is None else argument_nodes)
    sources = (TAINT_SOURCE_CALLS | TAINT_SOURCE_ATTRS
               if source_names is None else source_names)
    if check_inline_sources and _first_direct_source(
            arguments, sources, _purifying_call_names(sanitizer_names),
            call_name_candidates=call_name_candidates, tree=tree,
            source_name_candidates=source_name_candidates,
            resolve_imports=source_name_candidates is None):
        return False
    _inline_cover: dict[str, list[bool]] = {}
    targets = _collect_target_names(
        node, _purifying_call_names(sanitizer_names), _inline_cover,
        scope, tainted_vars, shadow, call_name_candidates,
        argument_nodes=arguments, tree=tree)
    if not targets:
        return False
    return all(_target_is_sanitized(
        name, scope, node, sanitized_keys, shadow, _inline_cover)
        for name in targets)
SCALAR_SANITIZER_CALLS: frozenset[str] = frozenset({
    'int', 'float', 'bool', 'complex', 'len', 'abs', 'round',
    'hash', 'ord', 'hex', 'oct', 'bin', 'id',
})
TAINT_SOURCE_ATTRS: frozenset[str] = frozenset({
    'sys.argv', 'sys.stdin', 'os.environ',
    'request.args', 'request.form', 'request.files',
    'request.values', 'request.json', 'request.data',
    'request.cookies', 'request.headers',
    'request.GET', 'request.POST', 'request.body',
    'request.COOKIES', 'request.META',
    'flask.request.args', 'flask.request.form', 'flask.request.files',
    'flask.request.values', 'flask.request.json', 'flask.request.data',
    'flask.request.cookies', 'flask.request.headers',
})
TAINT_SOURCE_CALLS: frozenset[str] = frozenset({
    'input', 'raw_input', 'os.getenv', 'os.environ.get',
    'sys.stdin.read',
    'request.get', 'request.post', 'request.data',
    'request.get_json', 'flask.request.get_json',
    'file.read', 'socket.recv',
})
ORIGIN_CALLS: frozenset[str] = frozenset({
    'input', 'raw_input', 'os.getenv', 'os.environ.get',
    'request.get_json', 'flask.request.get_json',
})
_IMPORT_BINDING_CACHE: weakref.WeakKeyDictionary[ast.AST, tuple] = (
    weakref.WeakKeyDictionary())
def _binding_activation_pos(node: ast.AST) -> tuple[int, int]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)):
        return max(
            (_node_end_pos(site) for site in iter_def_site_nodes(node)),
            default=_node_pos(node))
    if isinstance(node, ast.ExceptHandler) and node.type is not None:
        return _node_end_pos(node.type)
    return _node_pos(node)
def _build_import_binding_view(tree: ast.AST) -> tuple:
    module_aliases: dict[str, set[str]] = {}
    from_bindings: list[tuple[str, str, str]] = []
    provenance: dict[tuple[str, str], str | None] = {}
    module_events: dict[str, list[tuple[tuple[int, int], str | None]]] = {}
    scoped_events: dict[
        tuple[str, str], list[tuple[tuple[int, int], str | None]]] = {}
    event_regions: dict[
        tuple[str, str, tuple[int, int]], _FlowRegion | None] = {}
    scope_idx = build_scope_index(tree)
    parents = build_parent_map(tree)
    local, global_names, class_scopes = _shadow_of(tree)
    def _scope_of(node: ast.AST) -> str:
        registered = scope_idx.get(id(node))
        if registered is not None:
            return registered
        current = node
        while True:
            parent = parents.get(id(current))
            if parent is None:
                return ""
            if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.ClassDef)):
                enclosing = scope_idx.get(id(parent), "")
                return (f"{enclosing}.{parent.name}"
                        if enclosing else parent.name)
            current = parent
    def _event(scope: str, bound: str, origin: str | None,
               activation: tuple[int, int], node: ast.AST) -> None:
        scope = owner_scope(
            scope, bound, local, global_names, class_scopes)
        scoped_events.setdefault((scope, bound), []).append((activation, origin))
        event_regions[(scope, bound, activation)] = _flow_region_for(
            node, parents, scope_idx)
        if not scope:
            module_events.setdefault(bound, []).append((activation, origin))
    def _remember(scope: str, bound: str, origin: str | None) -> None:
        scope = owner_scope(
            scope, bound, local, global_names, class_scopes)
        key = (scope, bound)
        previous = provenance.get(key, origin)
        provenance[key] = previous if previous == origin else None
    for node in tree_nodes(tree):
        scope = _scope_of(node)
        if isinstance(node, ast.Import):
            for alias in node.names:
                bound = import_alias_bound_name(alias, from_import=False)
                if bound is None:
                    continue
                module = (alias.name if alias.asname
                          else alias.name.split('.', maxsplit=1)[0])
                module_aliases.setdefault(module, set()).add(bound)
                _remember(scope, bound, module)
                _event(scope, bound, module, _node_end_pos(node), node)
            continue
        if isinstance(node, ast.ImportFrom):
            module = node.module or ""
            for alias in node.names:
                bound = import_alias_bound_name(alias, from_import=True)
                if alias.name == '*' or bound is None:
                    continue
                origin = (f"{module}.{alias.name}" if module else alias.name)
                actual_origin = origin if node.level == 0 else None
                _remember(scope, bound, actual_origin)
                _event(scope, bound, actual_origin, _node_end_pos(node), node)
                if node.level == 0:
                    from_bindings.append((module, alias.name, bound))
            continue
        names: set[str] = set()
        collect_binding_names(node, names)
        for name in names:
            _remember(scope, name, None)
        pairs = _scope_binding_forms(
            node, scope, (local, global_names, class_scopes))
        if pairs:
            for targets, value in pairs:
                activation = _node_end_pos(value)
                for name in _iter_binding_target_names(targets):
                    _event(scope, name, None, activation, node)
        else:
            activation = _binding_activation_pos(node)
            for name in names:
                _event(scope, name, None, activation, node)
    events = {name: tuple(sorted(items, key=lambda item: item[0]))
              for name, items in module_events.items()}
    local_events = {key: tuple(sorted(items, key=lambda item: item[0]))
                    for key, items in scoped_events.items()}
    return (module_aliases, tuple(from_bindings), provenance, events,
            local_events, event_regions)
def _import_binding_view(tree: ast.AST) -> tuple:
    return cached_tree_view(
        _IMPORT_BINDING_CACHE, tree, _build_import_binding_view)
def _binding_event_options(view: tuple, scope: str, name: str,
                           pos: tuple[int, int], use_scope: str) -> tuple:
    events = (view[3].get(name, ()) if not scope
              else view[4].get((scope, name), ()))
    prior = [event for event in events if event[0] <= pos]
    if not prior:
        return False, ()
    regions = view[5]
    def _dominates(event) -> bool:
        region = regions.get((scope, name, event[0]))
        return (region is None
                or (region.scope == use_scope
                    and region.start <= pos <= region.end))
    dominating = [index for index, event in enumerate(prior)
                  if _dominates(event)]
    if not dominating:
        return False, tuple(prior)
    baseline = dominating[-1]
    return True, tuple(prior[baseline:])
def _single_binding_origin(present: bool, events: tuple) -> tuple:
    if not present or not events:
        return False, None
    origins = {event[1] for event in events}
    return (True, next(iter(origins))) if len(origins) == 1 else (True, None)
def _module_binding_state(pos: tuple[int, int], name: str,
                          tree: ast.AST) -> tuple[bool, str | None] | None:
    view = _import_binding_view(tree)
    if not view[3].get(name):
        return None
    _baseline, events = _binding_event_options(view, "", name, pos, "")
    return _single_binding_origin(bool(events), events)
def _class_enclosing_import_binding(
        node: ast.AST, name: str, tree: ast.AST, scope: str, view: tuple,
        local: dict, global_names: dict, class_scopes: frozenset,
) -> tuple[bool, str | None]:
    pos = _node_pos(node)
    parts = scope.split('.')
    for index in range(len(parts) - 1, 0, -1):
        outer = '.'.join(parts[:index])
        if outer in class_scopes:
            continue
        if name in global_names.get(outer, ()):
            break
        _baseline, events = _binding_event_options(
            view, outer, name, pos, scope)
        if events:
            return _single_binding_origin(True, events)
        if name in local.get(outer, ()):
            return True, None
    return _module_binding_state(pos, name, tree) or (False, None)
def _visible_import_possibilities(node: ast.AST, name: str,
                                  tree: ast.AST) -> tuple:
    scope = build_scope_index(tree).get(id(node), "")
    local, global_names, class_scopes = _shadow_of(tree)
    owner = owner_scope(scope, name, local, global_names, class_scopes)
    key = (owner, name)
    view = _import_binding_view(tree)
    pos = _node_pos(node)
    if not scope and not owner and view[3].get(name):
        baseline, events = _binding_event_options(view, "", name, pos, scope)
        if not events:
            return False, frozenset(), True
        return (True, frozenset(event[1] for event in events), not baseline)
    if scope and owner == scope:
        events = view[4].get(key, ())
        if events:
            baseline, options = _binding_event_options(
                view, scope, name, pos, scope)
            if options:
                origins = {event[1] for event in options}
                fallback = not baseline and scope in class_scopes
                if fallback:
                    present, outer_origin = _class_enclosing_import_binding(
                        node, name, tree, scope, view, local, global_names,
                        class_scopes)
                    if present:
                        origins.add(outer_origin)
                    fallback = not present
                return True, frozenset(origins), fallback
            if scope in class_scopes:
                present, origin = _class_enclosing_import_binding(
                    node, name, tree, scope, view, local, global_names,
                    class_scopes)
                return (present, frozenset({origin}) if present else frozenset(),
                        not present)
            return True, frozenset({None}), False
    owner_events = (view[3].get(name, ()) if not owner
                    else view[4].get(key, ()))
    if scope and owner_events:
        baseline, events = _binding_event_options(
            view, owner, name, pos, scope)
        if events:
            return (True, frozenset(event[1] for event in events),
                    not baseline and not owner)
    provenance = view[2]
    if key in provenance:
        return True, frozenset({provenance[key]}), False
    if name in local.get(owner, ()):
        return True, frozenset({None}), False
    return False, frozenset(), True
def _visible_import_binding(node: ast.AST, name: str,
                            tree: ast.AST) -> tuple[bool, str | None]:
    present, origins, _fallback = _visible_import_possibilities(
        node, name, tree)
    if not present:
        return False, None
    return (True, next(iter(origins))) if len(origins) == 1 else (True, None)
def _imported_name_candidates(name: str, tree: ast.AST | None,
                              node: ast.AST | None = None, *,
                              possible: bool = False) -> tuple:
    if not name or tree is None:
        return (name,)
    module_aliases, from_bindings, _provenance, _events, _local_events = (
        _import_binding_view(tree)[:5])
    head, _sep, rest = name.partition('.')
    if node is not None:
        scope = build_scope_index(tree).get(id(node), "")
        if (not scope and _module_binding_state(
                _node_pos(node), head, tree) == (False, None)):
            return (name,)
        if possible:
            present, origins, fallback = _visible_import_possibilities(
                node, head, tree)
            if present or fallback:
                candidates = [name] if fallback else []
                for origin in sorted(
                        origins, key=lambda value: '' if value is None else value):
                    if origin is None:
                        continue
                    candidate = f"{origin}.{rest}" if rest else origin
                    if candidate not in candidates:
                        candidates.append(candidate)
                return tuple(candidates)
        present, origin = _visible_import_binding(node, head, tree)
        if (not present and scope in _shadow_of(tree)[2]
                and head in _shadow_of(tree)[0].get(scope, ())):
            return (name,)
        if present and origin is not None:
            return (f"{origin}.{rest}" if rest else origin,)
        if present and (head in module_aliases
                        or any(bound == head
                               for _module, _origin, bound in from_bindings)):
            return ()
    candidates = [name]
    for module, aliases in module_aliases.items():
        if head == module or head in aliases:
            candidate = f"{module}.{rest}" if rest else module
            if candidate not in candidates:
                candidates.append(candidate)
    for module, origin, bound in from_bindings:
        if head != bound:
            continue
        candidate = f"{module}.{origin}" if module else origin
        if rest:
            candidate = f"{candidate}.{rest}"
        if candidate not in candidates:
            candidates.append(candidate)
    return tuple(candidates)
def _without_builtin_prefix(name: str) -> str:
    return name.removeprefix('builtins.')
def _source_name_match(name: str, exact_calls: frozenset[str],
                       allow_calls: bool) -> str | None:
    name = _without_builtin_prefix(name)
    if name in TAINT_SOURCE_ATTRS:
        return name
    if not allow_calls:
        return None
    if name in exact_calls:
        return name
    base = name.rsplit('.', 1)[0] if '.' in name else ''
    return base if base in TAINT_SOURCE_ATTRS else None
def _resolved_source_name(name: str, exact_calls: frozenset[str],
                          tree: ast.AST | None, allow_calls: bool,
                          node: ast.AST | None = None) -> str | None:
    return next((_match for _candidate in _imported_name_candidates(
                     name, tree, node, possible=True)
                 if (_match := _source_name_match(
                     _candidate, exact_calls, allow_calls)) is not None), None)
def resolve_taint_source(node: ast.AST, exact_calls: frozenset[str],
                         tree: ast.AST | None = None) -> str | None:
    if isinstance(node, ast.Call):
        cn = resolve_call_name(node)
        source = _resolved_source_name(cn, exact_calls, tree, True, node)
        if source is not None:
            return source
        if isinstance(node.func, (ast.Attribute, ast.Subscript)):
            return resolve_taint_source(node.func, exact_calls, tree)
        return None
    if isinstance(node, (ast.Attribute, ast.Subscript)):
        target = node if isinstance(node, ast.Attribute) else node.value
        full = _taint_attr_chain(target)
        if full is not None:
            source = _resolved_source_name(
                full, exact_calls, tree, False, node)
            if source is not None:
                return source
        return resolve_taint_source(node.value, exact_calls, tree)
    if isinstance(node, ast.Name) and tree is not None:
        return _resolved_source_name(
            node.id, exact_calls, tree, False, node)
    return None
def iter_expr_origins(expr: ast.AST,
                      resolve_name: Callable[[str], str | None], *,
                      tree: ast.AST | None = None) -> Iterator[str]:
    for sub in _iter_value_channel_nodes(
            expr, prune=lambda _c: _is_scalar_sanitizer_call(_c, tree)):
        if isinstance(sub, ast.Name):
            origin = resolve_name(sub.id)
            if origin is None and tree is not None:
                origin = resolve_taint_source(sub, ORIGIN_CALLS, tree)
        else:
            origin = resolve_taint_source(sub, ORIGIN_CALLS, tree)
        if origin is not None:
            yield origin
def _bare_builtin_is_shadowed(node: ast.Call, name: str,
                              tree: ast.AST) -> bool:
    scope_idx = build_scope_index(tree)
    scope = scope_idx.get(id(node), "")
    local, global_names, class_scopes = _shadow_of(tree)
    owner = owner_scope(
        scope, name, local, global_names, class_scopes)
    if not owner and name not in local.get("", ()):
        return False
    present, origin = _visible_import_binding(node, name, tree)
    if not present:
        return False
    if origin is not None:
        return origin != f"builtins.{name}"
    return True
def _builtin_call_name(node: ast.Call, tree: ast.AST | None = None) -> str:
    raw = resolve_call_name(node)
    if (tree is not None and isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and (raw in SCALAR_SANITIZER_CALLS or raw == 'str')
            and _bare_builtin_is_shadowed(node, raw, tree)):
        return ''
    candidates = _imported_name_candidates(raw, tree, node)
    if not candidates:
        return ''
    for candidate in candidates:
        name = _without_builtin_prefix(candidate)
        if name in SCALAR_SANITIZER_CALLS or name == 'str':
            return name
    return _without_builtin_prefix(raw)
def _is_scalar_sanitizer_call(node: ast.Call,
                              tree: ast.AST | None = None) -> bool:
    return _builtin_call_name(node, tree) in SCALAR_SANITIZER_CALLS
def _agg_seq_children(sub: ast.AST) -> list:
    return list(sub.elts)
def _agg_dict_children(sub: ast.Dict) -> list:
    children = [_k for _k in sub.keys if _k is not None]
    children.extend(sub.values)
    return children
def _agg_binop_children(sub: ast.AST) -> list:
    return [sub.left, sub.right]
def _agg_unary_children(sub: ast.AST) -> list:
    return [sub.operand]
def _agg_values_children(sub: ast.AST) -> list:
    return list(sub.values)
def _agg_formatted_children(sub: ast.AST) -> list:
    children = [sub.value]
    if sub.format_spec is not None:
        children.append(sub.format_spec)
    return children
def _agg_ifexp_children(sub: ast.AST) -> list:
    return [sub.body, sub.orelse]
def _agg_call_children(sub: ast.AST) -> list:
    return list(sub.args) + [kw.value for kw in sub.keywords
                             if kw.value is not None]
_AGG_CHILD_EXTRACTORS: tuple[tuple[type, Any], ...] = (
    ((ast.Tuple, ast.List, ast.Set), _agg_seq_children),
    (ast.Dict, _agg_dict_children),
    (ast.BinOp, _agg_binop_children),
    (ast.UnaryOp, _agg_unary_children),
    (ast.BoolOp, _agg_values_children),
    (ast.JoinedStr, _agg_values_children),
    (ast.FormattedValue, _agg_formatted_children),
    (ast.IfExp, _agg_ifexp_children),
    (ast.Call, _agg_call_children),
)
def _sanitized_agg_children(sub: ast.AST) -> list:
    for node_types, extractor in _AGG_CHILD_EXTRACTORS:
        if isinstance(sub, node_types):
            return extractor(sub)
    return []
_AGG_NODE_TYPES: tuple[type, ...] = tuple(
    _t
    for _types, _extractor in _AGG_CHILD_EXTRACTORS
    for _t in (_types if isinstance(_types, tuple) else (_types,))
    if _t is not ast.Call)
@dataclass(frozen=True)
class _SanitizedViewCtx:
    view: dict[str, set[str]] | None
    origins: dict | None
    scope: str
    shadow: tuple[dict, dict, frozenset] | None
    tree: ast.AST | None
def _sanitized_fold(_sub: ast.AST,
                   _results: dict[int, tuple[bool, bool]]) -> None:
    _pure, _has = True, False
    for _k in _sanitized_agg_children(_sub):
        _kp, _kh = _results[id(_k)]
        _pure = _pure and _kp
        _has = _has or _kh
    _results[id(_sub)] = (_pure, _has)
def _sanitized_visit_state(
        sub: ast.AST, ctx: _SanitizedViewCtx
        ) -> tuple[tuple[bool, bool] | None, bool]:
    leaf = _sanitized_leaf_state(sub, ctx)
    if leaf is not None:
        return leaf, False
    if not isinstance(sub, ast.Call):
        return None, isinstance(sub, _AGG_NODE_TYPES)
    call_state = _sanitized_call_state(sub, ctx)
    return call_state, call_state is None
def _sanitized_expr_state(expr: ast.AST, ctx: _SanitizedViewCtx
                          ) -> tuple[bool, bool]:
    _results: dict[int, tuple[bool, bool]] = {}
    _stack: list[tuple[ast.AST, bool]] = [(expr, False)]
    while _stack:
        _sub, _aggregating = _stack.pop()
        if _aggregating:
            _sanitized_fold(_sub, _results)
            continue
        _state, _aggregate = _sanitized_visit_state(_sub, ctx)
        if _state is not None:
            _results[id(_sub)] = _state
            continue
        if _aggregate:
            _stack.append((_sub, True))
            for _k in _sanitized_agg_children(_sub):
                _stack.append((_k, False))
            continue
        _results[id(_sub)] = (False, False)
    return _results[id(expr)]
def _sanitized_lookup_scope(scope: str, name: str, shadow) -> str:
    if shadow is None:
        return scope
    owner = owner_scope(scope, name, shadow[0], shadow[1], shadow[2])
    if (owner == ""
            and name not in shadow[0].get("", ())
            and name not in shadow[1].get(scope, ())):
        return scope
    return owner
def _sanitized_name_state(sub: ast.Name, ctx: _SanitizedViewCtx
                          ) -> tuple[bool, bool]:
    _lookup_scope = _sanitized_lookup_scope(ctx.scope, sub.id, ctx.shadow)
    _in_san = (ctx.view is not None
               and sub.id in ctx.view.get(_lookup_scope, ()))
    _tainted = False
    if _in_san and ctx.origins is not None:
        if ctx.shadow is not None:
            _tainted = TaintNameResolution.resolve_taint_key(
                ctx.scope, sub.id, ctx.origins, ctx.shadow) is not None
        else:
            _tainted = (ctx.scope, sub.id) in ctx.origins
    return (True, True) if _in_san and not _tainted else (False, False)
def _sanitized_call_state(
        sub: ast.Call, ctx: _SanitizedViewCtx) -> tuple[bool, bool] | None:
    _cn = _builtin_call_name(sub, ctx.tree)
    if _cn in SCALAR_SANITIZER_CALLS:
        return (True, True)
    if _cn == 'str':
        return None
    return (False, False)
def _sanitized_leaf_state(sub: ast.AST, ctx: _SanitizedViewCtx
                          ) -> tuple[bool, bool] | None:
    if isinstance(sub, ast.Constant):
        return (True, False)
    if isinstance(sub, ast.Name):
        return _sanitized_name_state(sub, ctx)
    return None
def _register_sanitized_targets(_targets: list, _sc: str, out: dict[str, set[str]],
                               shadow: tuple[dict, dict, frozenset],
                               pos: tuple[int, int],
                               latest: dict[tuple[str, str], tuple[int, int]],
                               conditional: frozenset[tuple[str, str]],
                               ) -> bool:
    _new = False
    for _name in _iter_binding_target_names(_targets):
        _bsc = owner_scope(_sc, _name,
                           shadow[0], shadow[1], shadow[2])
        if ((_bsc, _name) in conditional
                or latest.get((_bsc, _name)) != pos):
            continue
        if _name not in out.get(_bsc, ()):
            out.setdefault(_bsc, set()).add(_name)
            _new = True
    return _new
def _latest_binding_positions(
        assigns: list[tuple[str, list, ast.AST, tuple[int, int]]],
        shadow: tuple[dict, dict, frozenset]
        ) -> dict[tuple[str, str], tuple[int, int]]:
    latest: dict[tuple[str, str], tuple[int, int]] = {}
    for _sc, _targets, _value, _pos in assigns:
        for _name in _iter_binding_target_names(_targets):
            _bsc = owner_scope(
                _sc, _name, shadow[0], shadow[1], shadow[2])
            _key = (_bsc, _name)
            if _key not in latest or _pos > latest[_key]:
                latest[_key] = _pos
    return latest
_CONDITIONAL_BINDING_CONTAINERS = (
    (ast.If, ast.For, ast.AsyncFor, ast.While, ast.Match,
     ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)
    + _TRY_NODE_TYPES
)
def _binding_is_conditional(node: ast.AST,
                            parents: dict[int, ast.AST]) -> bool:
    current = node
    while True:
        parent = parents.get(id(current))
        if parent is None:
            return False
        if isinstance(parent, _CONDITIONAL_BINDING_CONTAINERS):
            return True
        if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                               ast.ClassDef, ast.Lambda)):
            body = parent.body
            if ((isinstance(body, ast.AST) and current is body)
                    or (isinstance(body, list) and current in body)):
                return False
        current = parent
def _conditional_binding_keys(assigns, tree: ast.Module,
                              shadow) -> frozenset[tuple[str, str]]:
    parents = build_parent_map(tree)
    keys: set[tuple[str, str]] = set()
    for scope, targets, _value, _pos in assigns:
        if not _binding_is_conditional(targets[0] if targets else _value,
                                       parents):
            continue
        for name in _iter_binding_target_names(targets):
            owner = owner_scope(
                scope, name, shadow[0], shadow[1], shadow[2])
            keys.add((owner, name))
    return frozenset(keys)
def collect_scalar_sanitized_vars(
        tree: ast.Module,
        scope_idx: dict | None = None,
        taint_origins: dict | None = None,
        shadow: tuple[dict, dict, frozenset] | None = None) -> dict[str, set[str]]:
    if scope_idx is None:
        scope_idx = build_scope_index(tree)
    if shadow is None:
        shadow = _shadow_of(tree)
    _assigns = _materialize_sanitized_assigns(tree, scope_idx)
    _latest = _latest_binding_positions(_assigns, shadow)
    _conditional = _conditional_binding_keys(_assigns, tree, shadow)
    out: dict[str, set[str]] = {}
    changed = True
    while changed:
        changed = False
        for _sc, _targets, _value, _pos in _assigns:
            _pure, _has_san = _sanitized_expr_state(
                _value, _SanitizedViewCtx(
                    out, taint_origins, _sc, shadow, tree))
            if (_pure and _has_san
                    and _register_sanitized_targets(
                        _targets, _sc, out, shadow, _pos, _latest,
                        _conditional)):
                changed = True
    return out
def _materialize_sanitized_assigns(
        tree: ast.Module,
        scope_idx: dict) -> list[tuple[str, list, ast.AST, tuple[int, int]]]:
    assigns: list[tuple[str, list, ast.AST, tuple[int, int]]] = []
    _shadow = _shadow_of(tree)
    for node in walk_nodes(tree):
        if isinstance(node, ast.AugAssign):
            continue
        _scope = scope_idx.get(id(node), "")
        for _targets, _value in _scope_binding_forms(node, _scope, _shadow):
            _bindings = _element_binding_pairs(_targets, _value)
            for _bound_targets, _bound_value in _bindings:
                assigns.append((_scope, _bound_targets, _bound_value,
                                _node_pos(node)))
    return assigns
def _first_rebind_line_in_scope(stmts, var_name):
    first = None
    stack = list(stmts)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef, ast.Lambda)):
            first = _earlier_line(
                first, _def_site_rebind_line(node, var_name))
            if not isinstance(node, ast.Lambda) and node.name == var_name:
                first = _earlier_line(first, getattr(node, 'lineno', None))
            continue
        first = _earlier_line(first, _node_rebind_line(node, var_name))
        stack.extend(ast.iter_child_nodes(node))
    return first
def _def_site_rebind_line(node, var_name):
    first = None
    for site in iter_def_site_nodes(node):
        first = _earlier_line(
            first, _expr_rebind_line(site, var_name))
    return first
def _expr_rebind_line(expr, var_name):
    first = None
    stack = [expr]
    while stack:
        node = stack.pop()
        first = _earlier_line(first, _node_rebind_line(node, var_name))
        if isinstance(node, ast.Lambda):
            stack.extend(iter_def_site_nodes(node))
            continue
        stack.extend(ast.iter_child_nodes(node))
    return first
_SINGLE_NAME_REBIND_FORMS: tuple[tuple[type | tuple[type, ...], str], ...] = (
    (MATCH_CAPTURE_NODES, 'name'),
    (MATCH_REST_NODES, 'rest'),
    (ast.ExceptHandler, 'name'),
)
def _single_name_rebind(node) -> tuple[str | None, bool]:
    for node_types, attr in _SINGLE_NAME_REBIND_FORMS:
        if isinstance(node, node_types):
            return getattr(node, attr, None), True
    return None, False
def _import_binds(node, var_name: str) -> bool:
    from_import = isinstance(node, ast.ImportFrom)
    return any(
        import_alias_bound_name(alias, from_import=from_import) == var_name
        for alias in node.names)
def _node_rebind_line(node, var_name):
    _name, _single = _single_name_rebind(node)
    if _single:
        return getattr(node, 'lineno', None) if _name == var_name else None
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return getattr(node, 'lineno', None) if _import_binds(node, var_name) else None
    if any(var_name in iter_unpack_target_names([target])
           for target in _rebind_binding_targets(node)):
        return getattr(node, 'lineno', None)
    return None
def _earlier_line(current, line) -> int | None:
    if line is None:
        return current
    if current is None or line < current:
        return line
    return current
def _rebind_binding_targets(node) -> list:
    if isinstance(node, ast.Assign):
        return node.targets
    if isinstance(node, ast.AnnAssign):
        return [node.target] if node.value is not None else []
    if isinstance(node, (ast.AugAssign, ast.For, ast.AsyncFor)):
        return [node.target]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return [item.optional_vars for item in node.items
                if item.optional_vars is not None]
    if isinstance(node, ast.NamedExpr):
        return [node.target]
    return []
def _guard_body_interval(node: ast.If, target_name: str) -> tuple[int, int]:
    _if_ln = getattr(node, 'lineno', 0)
    start = min((getattr(s, 'lineno', 0) or _if_ln) for s in node.body)
    end = max((getattr(s, 'end_lineno', 0) or start) for s in node.body)
    rebind = _first_rebind_line_in_scope(node.body, target_name)
    if rebind is not None:
        end = min(end, rebind - 1)
    return start, end
def _deferred_execution_line_spans(node: ast.If) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    stack = list(node.body)
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if current.body:
                spans.append((
                    current.body[0].lineno,
                    getattr(current.body[-1], "end_lineno",
                            current.body[-1].lineno)))
            stack.extend(iter_def_site_nodes(current))
            continue
        if isinstance(current, ast.Lambda):
            spans.append((current.body.lineno,
                          getattr(current.body, "end_lineno",
                                  current.body.lineno)))
            stack.extend(iter_def_site_nodes(current))
            continue
        stack.extend(ast.iter_child_nodes(current))
    return spans
def _subtract_line_span(intervals: list[tuple[int, int]],
                        span: tuple[int, int]) -> list[tuple[int, int]]:
    start, end = span
    result: list[tuple[int, int]] = []
    for low, high in intervals:
        if end < low or start > high:
            result.append((low, high))
            continue
        if low < start:
            result.append((low, start - 1))
        if end < high:
            result.append((end + 1, high))
    return result
def _guard_body_intervals(node: ast.If,
                          target_name: str) -> list[tuple[int, int]]:
    intervals = [_guard_body_interval(node, target_name)]
    for span in _deferred_execution_line_spans(node):
        intervals = _subtract_line_span(intervals, span)
    return [(low, high) for low, high in intervals if low <= high]
def _guard_test_rebinds_after(test: ast.AST, target_name: str,
                               guard_call: ast.Call) -> bool:
    guard_end = (getattr(guard_call, 'end_lineno', guard_call.lineno),
                 getattr(guard_call, 'end_col_offset', guard_call.col_offset))
    stack = [test]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Lambda):
            stack.extend(iter_def_site_nodes(node))
            continue
        if (isinstance(node, ast.NamedExpr)
                and isinstance(node.target, ast.Name)
                and node.target.id == target_name
                and _node_pos(node) > guard_end):
            return True
        stack.extend(ast.iter_child_nodes(node))
    return False
def collect_regex_guards(tree: ast.Module) -> dict:
    guards: dict = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.If) or not node.body:
            continue
        for guard_call in _regex_guard_calls(node.test):
            pair = _fullmatch_guard_pair(guard_call, tree)
            if pair is None:
                continue
            target_name, _ = pair
            if _guard_test_rebinds_after(
                    node.test, target_name, guard_call):
                continue
            guards.setdefault(target_name, []).extend(
                _guard_body_intervals(node, target_name))
    return guards
def _regex_guard_calls(test) -> list:
    if isinstance(test, ast.NamedExpr):
        test = test.value
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
        calls = []
        for conjunct in test.values:
            candidate = (conjunct.value
                         if isinstance(conjunct, ast.NamedExpr) else conjunct)
            if isinstance(candidate, ast.Call):
                calls.append(candidate)
        return calls
    return [test] if isinstance(test, ast.Call) else []
_GUARD_MATCH_KINDS = ('fullmatch', 'match')
_GUARD_START_ANCHORS = ('^', r'\A')
_END_ANCHORS = ('$', r'\Z')
def _regex_guard_kind(call: ast.Call, tree: ast.Module) -> str | None:
    head, _sep, rest = resolve_call_name(call).partition('.')
    _present, origin = _visible_import_binding(call, head, tree)
    if rest:
        return rest if origin == 're' and rest in _GUARD_MATCH_KINDS else None
    if origin is None:
        return None
    resolved = origin.removeprefix('re.')
    return (resolved if origin.startswith('re.')
            and resolved in _GUARD_MATCH_KINDS else None)
def _guard_pattern_body(pattern: str) -> str:
    body = pattern
    for anchor in _GUARD_START_ANCHORS:
        if body.startswith(anchor):
            body = body[len(anchor):]
            break
    for anchor in _END_ANCHORS:
        if body.endswith(anchor):
            body = body[:-len(anchor)]
            break
    return body
def _static_regex_flag_value(node: ast.AST) -> int | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return node.value
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        left = _static_regex_flag_value(node.left)
        right = _static_regex_flag_value(node.right)
        if left is not None and right is not None:
            return left | right
        return None
    name = _taint_attr_chain(node)
    values = {
        're.ASCII': re.ASCII, 're.A': re.ASCII,
        're.IGNORECASE': re.IGNORECASE, 're.I': re.IGNORECASE,
        're.LOCALE': re.LOCALE, 're.L': re.LOCALE,
        're.DOTALL': re.DOTALL, 're.S': re.DOTALL,
        're.VERBOSE': re.VERBOSE, 're.X': re.VERBOSE,
        're.MULTILINE': re.MULTILINE, 're.M': re.MULTILINE,
    }
    return values.get(name)
def _regex_guard_has_unsafe_flags(call: ast.Call, kind: str) -> bool:
    flags = ([call.args[2]] if len(call.args) > 2 else [])
    flags.extend(kw.value for kw in call.keywords if kw.arg == 'flags')
    for flag in flags:
        value = _static_regex_flag_value(flag)
        if value is None:
            return True
        if value & re.IGNORECASE and not value & re.ASCII:
            return True
        if kind == 'match' and value & re.MULTILINE:
            return True
    return False
def _fullmatch_guard_pair(call, tree: ast.Module
                          ) -> tuple[str, str] | None:
    kind = _regex_guard_kind(call, tree)
    if kind is None or len(call.args) < 2:
        return None
    pat, target = call.args[0], call.args[1]
    if not isinstance(target, ast.Name) or not _is_whitelist_pattern(pat):
        return None
    if _regex_guard_has_unsafe_flags(call, kind):
        return None
    if kind == 'match' and not pat.value.rstrip().endswith(r'\Z'):
        return None
    return target.id, pat.value
_SAFE_GUARD_CHARS = frozenset(
    'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_')
_SAFE_GUARD_CLASS_TOKEN_RE = re.compile(r'.-.|.', re.DOTALL)
_SAFE_GUARD_QUANTIFIER_RE = re.compile(r'\{[0-9]+(?:,[0-9]*)?\}')
def _safe_guard_class(body: str) -> bool:
    if not body or body.startswith('^') or '\\' in body:
        return False
    for match in _SAFE_GUARD_CLASS_TOKEN_RE.finditer(body):
        token = match[0]
        start, end = token[0], token[-1]
        if (start > end
                or not {start, end}.issubset(_SAFE_GUARD_CHARS)):
            return False
        if any(chr(cp) not in _SAFE_GUARD_CHARS
               for cp in range(ord(start), ord(end) + 1)):
            return False
    return True
def _guard_quantifier_end(pattern: str, pos: int) -> int:
    if pos >= len(pattern):
        return pos
    if pattern[pos] in '+*?':
        return pos + 1
    if pattern[pos] != '{':
        return pos
    match = _SAFE_GUARD_QUANTIFIER_RE.match(pattern, pos)
    return match.end() if match is not None else -1
def _is_safe_guard_pattern(pattern: str) -> bool:
    body = _guard_pattern_body(pattern)
    if not body:
        return False
    pos = 0
    while pos < len(body):
        if body[pos] in _SAFE_GUARD_CHARS:
            pos += 1
        elif body[pos] == '[':
            close = body.find(']', pos + 1)
            if close < 0 or not _safe_guard_class(body[pos + 1:close]):
                return False
            pos = close + 1
        else:
            return False
        pos = _guard_quantifier_end(body, pos)
        if pos < 0:
            return False
    return True
def _is_whitelist_pattern(pat: ast.AST) -> bool:
    return (isinstance(pat, ast.Constant) and isinstance(pat.value, str)
            and _is_safe_guard_pattern(pat.value))
def _propagate_value_origin(sc, value, targets, origins, resolve,
                            composite_origin, bind_key):
    if isinstance(value, ast.Name):
        _src_key = resolve(sc, value.id)
        if _src_key is None:
            return False
        _hit_origin = origins[_src_key]
    else:
        _hit_origin = composite_origin(sc, value)
        if _hit_origin is None:
            return False
    _changed = False
    for _name in _iter_binding_target_names(targets):
        _tkey = bind_key(sc, _name)
        if _tkey not in origins:
            origins[_tkey] = _hit_origin
            _changed = True
    return _changed
def _composite_taint_origin(sc: str, value: ast.AST, origins: dict,
                            _resolve, tree: ast.AST | None = None) -> str | None:
    def _origin_of(name: str) -> str | None:
        _k = _resolve(sc, name)
        return None if _k is None else origins[_k]
    return next(iter_expr_origins(value, _origin_of, tree=tree), None)
class _TaintOriginsSnapshot(NamedTuple):
    tree: ast.Module
    origins: dict
    scope_idx: dict
class _ScopeBindingSnapshot(NamedTuple):
    tree: ast.Module
    local_bindings: dict
    global_names: dict
    class_scopes: frozenset
class _MainGuardSnapshot(NamedTuple):
    tree: ast.Module
    lines: set[int]
class PreciseTaintAnalyzer:
    def __init__(self) -> None:
        self._taint_origins_cache: _TaintOriginsSnapshot | None = None
        self._scope_bindings_cache: _ScopeBindingSnapshot | None = None
        self._main_guard_cache: _MainGuardSnapshot | None = None
    def collect_scope_bindings(self, tree: ast.Module) -> tuple[dict, dict]:
        self._ensure_scope_bindings(tree)
        cached = self._scope_bindings_cache
        return cached.local_bindings, cached.global_names
    def collect_class_scopes(self, tree: ast.Module) -> frozenset:
        self._ensure_scope_bindings(tree)
        return self._scope_bindings_cache.class_scopes
    def _ensure_scope_bindings(self, tree: ast.Module) -> None:
        cached = self._scope_bindings_cache
        if cached is not None and cached.tree is tree:
            return
        local, global_names, class_scopes = collect_shadow_bindings(tree)
        self._scope_bindings_cache = _ScopeBindingSnapshot(
            tree, local, global_names, class_scopes)
    def collect_taint_sources(self, tree: ast.Module) -> set:
        _origins, _ = self.collect_taint_origins(tree)
        return {_var for _sc, _var in _origins}
    def collect_taint_origins(self, tree: ast.Module) -> tuple[dict, dict]:
        _cached = self._taint_origins_cache
        if _cached is not None and _cached.tree is tree:
            return dict(_cached.origins), _cached.scope_idx
        _scope_idx = build_scope_index(tree)
        origins: dict = {}
        _local_bindings, _global_names = self.collect_scope_bindings(tree)
        _class_scopes = self.collect_class_scopes(tree)
        _shadow = (_local_bindings, _global_names, _class_scopes)
        def _bind_key(sc: str, name: str):
            return TaintNameResolution.owner_key(sc, name, _shadow)
        self._register_direct_origins(
            tree, _scope_idx, origins, _bind_key, _shadow)
        def _resolve(scope: str, name: str):
            return TaintNameResolution.resolve_taint_key(scope, name, origins, _shadow)
        self._taint_fixpoint(
            tree, _scope_idx, origins, _resolve, _bind_key, _shadow)
        self._taint_origins_cache = _TaintOriginsSnapshot(
            tree, dict(origins), _scope_idx)
        return dict(origins), _scope_idx
    def _taint_fixpoint(self, tree: ast.Module, _scope_idx: dict,
                        origins: dict, _resolve, _bind_key, shadow) -> None:
        def _composite(sc, value):
            return _composite_taint_origin(
                sc, value, origins, _resolve, tree)
        changed = True
        while changed:
            changed = self._propagate_round(
                tree, _scope_idx, origins, _resolve, _composite, _bind_key,
                shadow)
    @staticmethod
    def _propagate_round(tree: ast.Module, scope_idx: dict, origins: dict,
                         resolve, composite, bind_key, shadow) -> bool:
        changed = False
        for node in tree_nodes(tree):
            _sc = scope_idx.get(id(node), "")
            for _targets, _value in _scope_binding_forms(node, _sc, shadow):
                for _bound_targets, _bound_value in _element_binding_pairs(
                        _targets, _value):
                    changed = _propagate_value_origin(
                        _sc, _bound_value, _bound_targets, origins,
                        resolve, composite, bind_key) or changed
            if not (isinstance(node, ast.Expr)
                    and isinstance(node.value, ast.Call)):
                continue
            call = node.value
            if not (isinstance(call.func, ast.Attribute)
                    and call.func.attr in _TAINING_MUTATION_METHODS):
                continue
            root = taint_root_name(call.func.value)
            if root is None:
                continue
            values = (*call.args, *(kw.value for kw in call.keywords))
            origin = next((_origin for _value in values
                           if (_origin := composite(_sc, _value)) is not None),
                          None)
            key = bind_key(_sc, root)
            if origin is not None and key not in origins:
                origins[key] = origin
                changed = True
        return changed
    @staticmethod
    def _register_direct_origins(
            tree: ast.Module, scope_idx: dict, origins: dict,
            bind_key, shadow) -> None:
        for node in tree_nodes(tree):
            _sc = scope_idx.get(id(node), "")
            for _targets, _value in _scope_binding_forms(node, _sc, shadow):
                _origin = resolve_taint_source(_value, ORIGIN_CALLS, tree)
                if not _origin:
                    continue
                for _name in _iter_binding_target_names(_targets):
                    origins[bind_key(_sc, _name)] = _origin
    def main_guard_lines_cached(self, tree: ast.Module) -> set[int]:
        cached = self._main_guard_cache
        if cached is not None and cached.tree is tree:
            return cached.lines
        lines = self.main_guard_lines(tree)
        self._main_guard_cache = _MainGuardSnapshot(tree, lines)
        return lines
    @staticmethod
    def main_guard_lines(tree: ast.Module) -> set[int]:
        lines: set[int] = set()
        for node in tree_nodes(tree):
            if (isinstance(node, ast.If)
                    and is_main_check(node.test)):
                for sub in walk_nodes(node):
                    ln = getattr(sub, 'lineno', None)
                    if isinstance(ln, int):
                        lines.add(ln)
        return lines
def _project_visible_taints(origins: dict, scope: str, names: set[str],
                            local_bindings: dict, global_names: dict,
                            class_scopes: frozenset) -> None:
    chain = _scope_chain(scope)
    for origin_scope, var in origins:
        if origin_scope not in chain or var in names:
            continue
        if origin_scope:
            visible = owner_scope(
                scope, var, local_bindings, global_names,
                class_scopes) == origin_scope
        else:
            visible = not module_fallback_shadowed(
                scope, var, local_bindings, global_names, class_scopes)
        if visible:
            names.add(var)
def scope_visible_taints(origins: dict, scope: str,
                         local_bindings: dict, global_names: dict,
                         class_scopes: frozenset,
                         cache: dict | None = None) -> frozenset:
    if cache is not None:
        hit = cache.get(scope)
        if hit is not None:
            return hit
    names = {var for (_sc, var) in origins if _sc == scope}
    _project_visible_taints(origins, scope, names, local_bindings,
                            global_names, class_scopes)
    frozen = frozenset(names)
    if cache is not None:
        cache[scope] = frozen
    return frozen
class ScopeFacts(NamedTuple):
    origins: dict
    scope_idx: dict
    local_bindings: dict
    global_names: dict
    class_scopes: frozenset
    def module_visible(self, scope: str, name: str) -> bool:
        return not module_fallback_shadowed(
            scope, name, self.local_bindings, self.global_names,
            self.class_scopes)
    def scoped_value(self, scope: str, name: str, mapping: dict,
                     default=None):
        local_key = (scope, name)
        if local_key in mapping:
            return mapping[local_key]
        owner = owner_scope(
            scope, name, self.local_bindings, self.global_names,
            self.class_scopes)
        if owner == scope:
            return default
        owner_key = (owner, name)
        if owner_key in mapping:
            return mapping[owner_key]
        return default
def collect_scope_facts(analyzer: PreciseTaintAnalyzer,
                        tree: ast.Module) -> ScopeFacts:
    origins, scope_idx = analyzer.collect_taint_origins(tree)
    local_bindings, global_names = analyzer.collect_scope_bindings(tree)
    return ScopeFacts(
        origins, scope_idx, local_bindings, global_names,
        analyzer.collect_class_scopes(tree))
def _scope_chain(scope: str) -> frozenset:
    if not scope:
        return frozenset({""})
    _parts = scope.split(".")
    return frozenset(
        ".".join(_parts[:_i]) for _i in range(len(_parts), 0, -1)
    ) | {""}
def _binding_site_pos(node: ast.AST) -> tuple[int, int]:
    """绑定点的源码位置。

    ``_binding_forms`` 把 ``ast.comprehension`` 当作合法绑定形态，但该节点
    自身没有 ``lineno``/``col_offset``（位置在 ``target`` 上）。直接取属性
    会让整个文件的安全扫描抛 ``AttributeError`` 并被上层按「不可读文件」跳过，
    造成 6 个文件的检测结果静默缺失。
    """
    anchor = node.target if isinstance(node, ast.comprehension) else node
    return (getattr(anchor, "lineno", 0) or 0,
            getattr(anchor, "col_offset", 0) or 0)


def _before_use(node: ast.AST, name: str, use_lineno: int,
                use_col: int | None) -> bool:
    if use_col is None:
        return _binding_site_pos(node)[0] <= use_lineno
    assigned = _assigned_value_for_name(node, name)
    return _node_end_pos(assigned) < (use_lineno, use_col)
_SHADOW_CACHE: weakref.WeakKeyDictionary[ast.AST, tuple] = (
    weakref.WeakKeyDictionary())
_ASSIGN_INDEX_CACHE: weakref.WeakKeyDictionary[ast.AST, tuple] = (
    weakref.WeakKeyDictionary())
def _shadow_for(tree: ast.AST,
                shadow: tuple[dict, dict, frozenset] | None) -> tuple:
    return _shadow_of(tree) if shadow is None else shadow
def _shadow_of(tree: ast.AST) -> tuple:
    return cached_tree_view(_SHADOW_CACHE, tree, collect_shadow_bindings)
def _build_assign_index(tree: ast.AST) -> tuple:
    local_bindings, global_names, class_scopes = _shadow_of(tree)
    _shadow = (local_bindings, global_names, class_scopes)
    scope_idx = build_scope_index(tree)
    entries: list[tuple[ast.AST, dict[str, str]]] = []
    for node in tree_nodes(tree):
        _sc = scope_idx.get(id(node), "")
        owners: dict[str, str] = {}
        for _targets, _value in _scope_binding_forms(node, _sc, _shadow):
            for _name in _iter_binding_target_names(_targets):
                owners.setdefault(_name, owner_scope(
                    _sc, _name, local_bindings, global_names, class_scopes))
        if owners:
            entries.append((node, owners))
    return tuple(entries)
def _assign_index_of(tree: ast.AST) -> tuple:
    return cached_tree_view(_ASSIGN_INDEX_CACHE, tree, _build_assign_index)
def _lookup_scope_chain(tree: ast.Module, name: str, scope: str,
                        scope_idx: dict | None) -> frozenset | None:
    if scope_idx is None:
        return None
    local_bindings, global_names, class_scopes = _shadow_of(tree)
    if scope in class_scopes:
        return frozenset(
            candidate for candidate in _scope_chain(scope)
            if candidate == scope or candidate not in class_scopes)
    owner = owner_scope(
        scope, name, local_bindings, global_names, class_scopes)
    return frozenset({owner})
def _latest_assign_stmt(tree: ast.Module, name: str, use_lineno: int,
                        scope: str,
                        scope_idx: dict | None,
                        use_col: int | None = None,
                        visible_scopes: frozenset | None = None) -> ast.AST | None:
    chain = (visible_scopes if visible_scopes is not None
             else _lookup_scope_chain(tree, name, scope, scope_idx))
    candidates = (
        node for node, owners in _assign_index_of(tree)
        if name in owners
        and (chain is None or owners[name] in chain)
        and _before_use(node, name, use_lineno, use_col)
    )
    return max(
        candidates,
        key=lambda node: (
            _node_end_pos(_assigned_value_for_name(node, name)),
            -_binding_site_pos(node)[0],
            -_binding_site_pos(node)[1],
        ),
        default=None)
_AUGASSIGN_UNROLL_LIMIT = 16
def _assigned_value_for_name(node, name):
    _fallback = None
    for targets, value in _binding_forms(node):
        if _fallback is None:
            _fallback = value
        for bound_targets, bound_value in _element_binding_pairs(targets, value):
            if name in _iter_binding_target_names(bound_targets):
                return bound_value
    return _fallback if _fallback is not None else node
def lookup_name_assignment(tree: ast.Module, name: str,
                           use_lineno: int, scope: str = _DEFAULT_SCOPE,
                           scope_idx: dict | None = None,
                           use_col: int | None = None) -> ast.AST | None:
    if scope_idx is None:
        scope_idx = build_scope_index(tree)
    visible_scopes = _lookup_scope_chain(tree, name, scope, scope_idx)
    chain: list[ast.AugAssign] = []
    cursor = use_lineno
    cursor_col = use_col
    base: ast.AST | None = None
    while True:
        best = _latest_assign_stmt(tree, name, cursor, scope, scope_idx,
                                   cursor_col, visible_scopes)
        if best is None:
            break
        if not isinstance(best, ast.AugAssign):
            base = _assigned_value_for_name(best, name)
            break
        chain.append(best)
        if len(chain) > _AUGASSIGN_UNROLL_LIMIT:
            base = best.target
            break
        cursor, cursor_col = _binding_site_pos(best)
    if not chain:
        return base
    if base is None:
        base = chain[-1].target
    for stmt in reversed(chain):
        base = ast.BinOp(left=base, op=stmt.op, right=stmt.value)
    return base

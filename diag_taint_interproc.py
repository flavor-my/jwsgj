from __future__ import annotations

import ast
import hashlib
import logging
import os
import threading
from collections import OrderedDict
from contextlib import contextmanager
from dataclasses import (
    dataclass,
    field,
    replace,
)
from typing import Any

from jwsgj.diag_shared_ast_bindings import (
    build_scope_index,
    clear_scope_index_memo,
    collect_binding_names,
    collect_shadow_bindings,
    owner_scope,
)
from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    attr_chain_key,
    build_parent_map,
    call_arg_values,
    iter_own_scope,
    iter_unpack_target_names,
    resolve_call_name,
)
from jwsgj.diag_shared_ast_views import (
    register_cache_release,
    tree_nodes,
)
from jwsgj.diag_shared_source_core import (
    decode_source,
    parse_guard_cached,
)
from jwsgj.diag_taint_dataflow import (
    _sanitized_before,
    collect_sanitized_keys,
    is_sanitized,
)
from jwsgj.diag_taint_model import (
    BUILTIN_SANITIZERS,
    BUILTIN_SOURCES,
    CONTAINER_STMTS,
    SINK_NAMES,
    SOURCE_NAMES,
    TaintNameResolution,
    container_sub_bodies,
    first_taint_source,
    iter_calls_pruned,
)
from jwsgj.diag_taint_tracker import (
    _SINK_BY_NAME,
    _SINK_RESOLVER_MEMO,
    _SINK_RESOLVER_MEMO_LOCK,
    TaintReport,
    _bfs_visit,
    _block_dominates,
    _builtin_sanitizer_names_for_sink,
    _call_root_binding,
    _event_position,
    _flow_events,
    _FlowContext,
    _FlowEvent,
    _iter_binding_events,
    _iter_binding_pairs,
    _payload_mentions,
    _positional_param_names,
    _sanitized_keys_at_use,
    _sanitizer_prune,
    _sink_name_resolver,
    _sink_payload_args,
    _SinkNameResolver,
    _statement_for_node,
    _taint_state,
    _universal_sanitizer_names,
    analyze_taint,
    expr_end,
    from_import_receiver,
    iter_free_load_names,
)
from jwsgj.diag_types_defs import TaintTrace
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    TAINT_SOURCE_CATEGORY_BY_NAME,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    'CrossModuleTaintTracker',
    'check_vulnerability',
    'clear_taint_scope_memos',
    'cross_module_vulnerabilities',
    'shared_ast_bridge',
]
logger = logging.getLogger(__name__)
_DEFAULT_FILEPATH = ""
def _swallow(function_name: str, exc: BaseException) -> None:
    log_swallowed(__name__, exc,
                  context=f"{function_name}:{type(exc).__name__}")
def _load_tree(filepath: str, code: str | None) -> ast.Module | None:
    if code is not None:
        try:
            return ast.parse(code, filename=filepath or "<string>")
        except PARSE_DEGRADE_EXC as e:
            logger.warning("[CrossModuleTaint] 解析失败: %s (%s)", filepath, e)
            return None
    tree = parse_guard_cached(filepath)
    if tree is None:
        logger.warning("[CrossModuleTaint] 源文件不可读或解析失败，降级空: %s",
                       filepath)
    return tree
def _sanitized_at_use(scope: str, name: str, pos: tuple[int, int],
                      sanitized_keys: dict, shadow) -> bool:
    key = TaintNameResolution.resolve_taint_key(
        scope, name, sanitized_keys, shadow)
    return (key is not None and _sanitized_before(
        sanitized_keys, key, pos, scope))
def _sink_taint_state(cache: dict, tree: ast.Module, source_names,
                      names: _SinkNameResolver, sink_name: str) -> tuple:
    sanitizer_names = _builtin_sanitizer_names_for_sink(sink_name)
    cache_key = frozenset(sanitizer_names)
    state = cache.get(cache_key)
    if state is None:
        state = (*_taint_state(
            tree, TaintReport(file_path=""), source_names,
            sanitizer_names, names), sanitizer_names)
        cache[cache_key] = state
    return state
def _state_tainted_key(scope: str, name: str, pos: tuple[int, int],
                       state: tuple, shadow) -> tuple[str, str] | None:
    tainted_vars, _hops, _origins, sanitized_keys, _names = state
    key = TaintNameResolution.resolve_taint_key(
        scope, name, tainted_vars, shadow)
    if key is None or _sanitized_at_use(
            scope, name, pos, sanitized_keys, shadow):
        return None
    return key
def _state_expr_source(scope: str, expr: ast.AST, state: tuple,
                       shadow, names: _SinkNameResolver,
                       sink_node: ast.Call, expression_bindings: dict,
                       parents: dict[int, ast.AST],
                       only_name: str | None = None) -> str | None:
    _tainted_vars, _hops, origins, sanitized_keys, sanitizer_names = state
    for child in iter_free_load_names(expr):
        if only_name is not None and child.id != only_name:
            continue
        owner = expression_bindings.get(id(child), {}).get(child.id)
        if isinstance(owner, ast.Lambda):
            continue
        if isinstance(owner, COMP_SCOPE_NODES) and not (
                _state_comprehension_reaches(
                    child, only_name or child.id, scope, state, shadow,
                    names, sink_node, expression_bindings, parents)):
            continue
        child_scope = names.scope_index.get(id(child), scope)
        pos = (getattr(child, "lineno", 0) or 0,
               getattr(child, "col_offset", 0) or 0)
        key = _state_tainted_key(child_scope, child.id, pos, state, shadow)
        if key is None:
            continue
        if is_sanitized(
                sink_node, scope=child_scope, sanitized_keys=sanitized_keys,
                shadow=shadow, tainted_vars={key: 1},
                sanitizer_names=sanitizer_names,
                call_name_candidates=names.candidates,
                argument_nodes=[expr], check_inline_sources=False):
            continue
        return origins.get(key) or child.id
    if only_name is not None:
        return None
    return first_taint_source(
        expr, SOURCE_NAMES,
        prune=_sanitizer_prune(names, sanitizer_names),
        call_name_candidates=names.source_candidates)
def _state_comprehension_reaches(
        name_node: ast.Name, var_name: str, scope: str, state: tuple,
        shadow, names: _SinkNameResolver, sink_node: ast.Call,
        expression_bindings: dict, parents: dict[int, ast.AST]) -> bool:
    chain = _comprehension_chain(name_node, parents)
    reaching: dict[str, bool] = {}
    for comp in reversed(chain):
        for generator in comp.generators:
            iter_scope = names.scope_index.get(id(generator.iter), scope)
            iter_reaches = _state_expr_source(
                iter_scope, generator.iter, state, shadow, names, sink_node,
                expression_bindings, parents, only_name=var_name) is not None
            for target_name in iter_unpack_target_names(generator.target):
                reaching[target_name] = iter_reaches
    return reaching.get(name_node.id, False)
@dataclass(frozen=True)
class _PropagationCtx:
    var_name: str
    filepath: str
    tree: ast.Module
    def_keys: dict
    scope_state: tuple
    names: Any
    source_end: tuple[int, int]
    sanitized_keys: dict
    sanitizer_names: set
    parents: dict[int, ast.AST]
    expression_bindings: dict
    sink_states: dict = field(default_factory=dict)
class CrossModuleTaintTracker:
    def __init__(self) -> None:
        self.traces: list[TaintTrace] = []
        self._source_names: frozenset = SOURCE_NAMES
        self._sink_names: frozenset = SINK_NAMES
        self._cross_ctx_memo: dict[tuple, tuple[Any, _CrossCallCtx]] = {}
        # 推导式匹配的递归环守卫：``[x for x in x]`` 这类自引用会让
        # ``_comprehension_matched_uses`` 与 ``_matched_uses`` 互相递归
        # 到 RecursionError，整文件的安全发现被静默丢弃。
        self._comprehension_visiting: set[int] = set()
    def track_file(self, filepath: str, code: str | None = None,
                   tree: ast.Module | None = None) -> list[TaintTrace]:
        filepath = os.fspath(filepath)
        traces: list[TaintTrace] = []
        self.traces = traces
        if tree is None:
            tree = _load_tree(filepath, code)
            if tree is None:
                return []
        try:
            self._track_taint(tree, filepath, traces)
        finally:
            self._cross_ctx_memo.clear()
        self.traces = traces
        return list(traces)
    def _track_taint(self, tree: ast.Module, filepath: str,
                     traces: list[TaintTrace]) -> None:
        _names = _sink_name_resolver(tree)
        _scope_state = (_names.scope_index, _names.shadow)
        sanitizer_names = _universal_sanitizer_names(BUILTIN_SANITIZERS)
        sanitized_keys = collect_sanitized_keys(
            tree, sanitizer_names, _names.scope_index, _names.shadow,
            call_name_candidates=_names.candidates)
        propagation = _PropagationCtx(
            var_name="", filepath=filepath, tree=tree, def_keys={},
            scope_state=_scope_state, names=_names, source_end=(0, 0),
            sanitized_keys=sanitized_keys, sanitizer_names=sanitizer_names,
            # 复用解析器已缓存的父图，避免对同一棵树重复整树遍历
            # （``_names._parents`` 与 ``build_parent_map(tree)`` 同值）。
            parents=_names._parents,
            expression_bindings=_names.expression_bindings)
        for node in tree_nodes(tree):
            self._record_direct_pass(
                node, filepath, _names, traces, tree)
            for _name, _value, _strong in _iter_binding_events(node):
                source = first_taint_source(
                    _value, self._source_names,
                    prune=_sanitizer_prune(_names, sanitizer_names),
                    call_name_candidates=_names.source_candidates)
                if source is None:
                    continue
                self._record_source_target(
                    node, _name, source,
                    replace(propagation, source_end=expr_end(_value)), traces)
    def _record_direct_pass(self, node: ast.AST, filepath: str,
                            names: _SinkNameResolver,
                            traces: list[TaintTrace],
                            tree: ast.Module) -> None:
        if not isinstance(node, ast.Call):
            return
        _sink = names.sink_name(node, self._sink_names)
        if _sink is None:
            self._record_inline_cross_module_sink(
                node, filepath, tree, names, traces)
            return
        call_name = resolve_call_name(node)
        sanitizer_names = _builtin_sanitizer_names_for_sink(_sink)
        prune = _sanitizer_prune(names, sanitizer_names)
        for arg in _sink_payload_args(
                node, _SINK_BY_NAME.get(_sink)):
            src = first_taint_source(
                arg, self._source_names, prune=prune,
                call_name_candidates=names.source_candidates)
            if not src:
                continue
            trace = TaintTrace(
                variable=src,
                source_file=filepath,
                source_line=arg.lineno,
                source_expr=src,
                sink_file=filepath,
                sink_line=node.lineno,
                sink_expr=_sink,
            )
            trace.propagation_chain.append({
                "type": "direct_pass",
                "from_func": src,
                "to_func": call_name,
                "line": node.lineno,
                "file": filepath,
            })
            traces.append(trace)
    def _record_inline_cross_module_sink(self, node: ast.Call, filepath: str,
                                         tree: ast.Module,
                                         names: _SinkNameResolver,
                                         traces: list[TaintTrace]) -> None:
        cross = self._cross_ctx(filepath, tree)
        if cross is None:
            return
        _scope = cross.scopes.get(id(node), "")
        for module, func, src, _line, _sink, _pval in _iter_cross_sink_hits(
                node, _scope, cross, self._sink_names,
                lambda pval, sink_name: first_taint_source(
                    pval, self._source_names,
                    prune=_sanitizer_prune(
                        names, _builtin_sanitizer_names_for_sink(sink_name)),
                    call_name_candidates=names.source_candidates)):
            trace = TaintTrace(
                variable=src,
                source_file=filepath,
                source_line=getattr(_pval, "lineno", 0),
                source_expr=src,
            )
            self._apply_cross_sink(trace, module, filepath, _line, _sink)
            trace.propagation_chain.append({
                "type": "direct_pass",
                "from_func": src,
                "to_func": func,
                "line": node.lineno,
                "file": filepath,
            })
            traces.append(trace)
    @staticmethod
    def _apply_cross_sink(trace: TaintTrace, module: str, filepath: str,
                          sink_line: int, sink_name: str) -> None:
        trace.sink_file = (_sibling_candidate_path(module, filepath)
                           or filepath)
        trace.sink_line = sink_line
        trace.sink_expr = sink_name
        if module not in trace.crossed_modules:
            trace.crossed_modules.append(module)
    def _record_source_target(self, node: ast.AST, name: str, source: str,
                              ctx: _PropagationCtx,
                              traces: list[TaintTrace]) -> None:
        scopes, shadow = ctx.scope_state
        _sc = scopes.get(id(node), "")
        trace = TaintTrace(
            variable=name,
            source_file=ctx.filepath,
            source_line=node.lineno,
            source_expr=source,
        )
        target_ctx = replace(
            ctx, var_name=name,
            def_keys={TaintNameResolution.owner_key(_sc, name, shadow): True})
        self._trace_propagation(trace, target_ctx)
        traces.append(trace)
    def _trace_propagation(self, trace: TaintTrace, ctx: _PropagationCtx,
                           _visited: set | None = None) -> None:
        visited = _visited if _visited is not None else set()
        _calls = _call_nodes_of(ctx.tree)
        _arg_hits = {
            id(node): self._matched_uses(node, ctx, call_arg_values(node))
            for node in _calls
        }
        _recv_hits = {id(node): self._matched_receiver_uses(node, ctx)
                      for node in _calls}
        for node in _calls:
            self._record_arg_pass(
                node, ctx, trace, _arg_hits[id(node)],
                _recv_hits[id(node)])
            if trace.sink_line:
                break
        if trace.sink_line:
            return
        if len(visited) >= _MAX_PROPAGATION_DEPTH:
            return
        for node in _all_nodes_of(ctx.tree):
            chain_base_len = len(trace.propagation_chain)
            crossed_base = list(trace.crossed_functions)
            branches = self._record_return_assign(
                node, ctx, trace, _arg_hits, _recv_hits)
            branch_steps = trace.propagation_chain[chain_base_len:]
            chain_base = trace.propagation_chain[:chain_base_len]
            for index, (_name, _scope, _end) in enumerate(branches):
                _key = (_scope, _name)
                if _key in visited:
                    continue
                branch_visited = visited | {_key}
                trace.propagation_chain = chain_base + [branch_steps[index]]
                trace.crossed_functions = list(crossed_base)
                self._trace_propagation(
                    trace,
                    replace(
                        ctx, var_name=_name,
                        def_keys={TaintNameResolution.owner_key(
                            _scope, _name, ctx.scope_state[1]): True},
                        source_end=_end),
                    branch_visited)
                if trace.sink_line:
                    return
            trace.propagation_chain = chain_base
            trace.crossed_functions = crossed_base
    def _matched_receiver_uses(self, node: ast.Call,
                               ctx: _PropagationCtx) -> int:
        _func = node.func
        if not isinstance(_func, ast.Attribute):
            return 0
        return self._matched_uses(node, ctx, [_func.value])
    def _matched_uses(self, node: ast.AST, ctx: _PropagationCtx,
                      exprs) -> int:
        scopes, shadow = ctx.scope_state
        _n = 0
        for _expr in exprs:
            for _name_node in iter_free_load_names(_expr):
                if _name_node.id != ctx.var_name:
                    continue
                owner = ctx.expression_bindings.get(
                    id(_name_node), {}).get(_name_node.id)
                if isinstance(owner, ast.Lambda):
                    continue
                if isinstance(owner, COMP_SCOPE_NODES) and not (
                        self._comprehension_matched_uses(_name_node, ctx)):
                    continue
                _pos = (getattr(_name_node, 'lineno', 0),
                        getattr(_name_node, 'col_offset', 0))
                if _pos <= ctx.source_end:
                    continue
                _use_scope = scopes.get(
                    id(_name_node), scopes.get(id(node), ""))
                if TaintNameResolution.resolve_taint_key(
                        _use_scope, _name_node.id, ctx.def_keys,
                        shadow) is None:
                    continue
                if _sanitized_at_use(_use_scope, _name_node.id, _pos,
                                      ctx.sanitized_keys, shadow):
                    continue
                _n += 1
        return _n
    def _comprehension_matched_uses(self, name_node: ast.Name,
                                    ctx: _PropagationCtx) -> bool:
        key = id(name_node)
        if key in self._comprehension_visiting:
            # 已在计算同名节点的可达性：环上再绕一圈不会带来新信息，
            # 直接按「未被外层可迭代对象求值」处理。
            return False
        self._comprehension_visiting.add(key)
        try:
            chain = _comprehension_chain(name_node, ctx.parents)
            reaching: dict[str, bool] = {}
            for comp in reversed(chain):
                for generator in comp.generators:
                    iter_reaches = bool(self._matched_uses(
                        generator.iter, ctx, [generator.iter]))
                    for target_name in iter_unpack_target_names(
                            generator.target):
                        reaching[target_name] = iter_reaches
            return reaching.get(name_node.id, False)
        finally:
            self._comprehension_visiting.discard(key)
    def _record_arg_pass(self, node: ast.Call, ctx: _PropagationCtx,
                         trace: TaintTrace, hits: int,
                         receiver_hits: int) -> None:
        if trace.sink_line:
            return
        if not hits and not receiver_hits:
            return
        call_name = resolve_call_name(node)
        if not call_name:
            return
        for _ in range(hits):
            trace.propagation_chain.append({
                "type": "arg_pass",
                "from_var": ctx.var_name,
                "to_func": call_name,
                "line": node.lineno,
                "file": ctx.filepath,
            })
            trace.crossed_functions.append(call_name)
        for _ in range(receiver_hits):
            trace.propagation_chain.append({
                "type": "receiver_pass",
                "from_var": ctx.var_name,
                "to_func": call_name,
                "line": node.lineno,
                "file": ctx.filepath,
            })
            if call_name not in trace.crossed_functions:
                trace.crossed_functions.append(call_name)
        _sink = ctx.names.sink_name(node, self._sink_names)
        if _sink is not None:
            if not _payload_mentions(
                    node, ctx.var_name, _SINK_BY_NAME.get(_sink)):
                return
            scopes, shadow = ctx.scope_state
            scope = scopes.get(id(node), '')
            state = _sink_taint_state(
                ctx.sink_states, ctx.tree, self._source_names,
                ctx.names, _sink)
            key = _state_tainted_key(
                scope, ctx.var_name,
                (node.lineno, node.col_offset), state, shadow)
            if key is None:
                return
            if is_sanitized(
                    node, scope=scope, sanitized_keys=state[3], shadow=shadow,
                    tainted_vars={key: 1}, sanitizer_names=state[4],
                    call_name_candidates=ctx.names.candidates,
                    argument_nodes=_sink_payload_args(
                        node, _SINK_BY_NAME.get(_sink)),
                    check_inline_sources=False):
                return
            trace.sink_file = ctx.filepath
            trace.sink_line = node.lineno
            trace.sink_expr = _sink
            return
        self._record_cross_module_sink(node, ctx, trace)
    def _record_cross_module_sink(self, node: ast.Call,
                                  ctx: _PropagationCtx,
                                  trace: TaintTrace) -> None:
        if trace.sink_line:
            return
        scopes, shadow = ctx.scope_state
        cross = self._cross_ctx(ctx.filepath, ctx.tree)
        if cross is None:
            return
        _scope = scopes.get(id(node), "")
        def _carries(pval, sink_name):
            state = _sink_taint_state(
                cross.sink_states, ctx.tree, self._source_names,
                ctx.names, sink_name)
            return _state_expr_source(
                _scope, pval, state, shadow, ctx.names, node,
                cross.expression_bindings, cross.parents,
                only_name=ctx.var_name)
        for module, _func, _src, _line, _sink, _pval in _iter_cross_sink_hits(
                node, _scope, cross, self._sink_names, _carries):
            self._apply_cross_sink(
                trace, module, ctx.filepath, _line, _sink)
            return
    def _cross_ctx(self, filepath: str, tree: ast.Module
                   ) -> _CrossCallCtx | None:
        if not filepath:
            return None
        key = (os.path.abspath(filepath), id(tree))
        cached = self._cross_ctx_memo.get(key)
        if cached is not None and cached[0] is tree:
            return cached[1]
        cross = _CrossCallCtx.build(filepath, tree)
        self._cross_ctx_memo[key] = (tree, cross)
        return cross
    def _record_return_assign(self, node: ast.AST, ctx: _PropagationCtx,
                              trace: TaintTrace,
                              arg_hits: dict[int, int],
                              receiver_hits: dict[int, int]
                              ) -> list[tuple[str, str, tuple[int, int]]]:
        if trace.sink_line:
            return []
        if ((getattr(node, 'lineno', 0), getattr(node, 'col_offset', 0))
                <= ctx.source_end):
            return []
        _scope = ctx.scope_state[0].get(id(node), "")
        _new: list[tuple[str, str, tuple[int, int]]] = []
        for _tgt, _rhs, _strong in _iter_binding_pairs(node):
            _end = expr_end(_rhs)
            _calls = [_call for _call in iter_calls_pruned(_rhs)
                      if arg_hits.get(id(_call))
                      or receiver_hits.get(id(_call))]
            for _call in _calls:
                called_name = resolve_call_name(_call)
                if not called_name:
                    continue
                _name = self._append_binding_step(
                    trace, _tgt, node, ctx, 'return_assign',
                    called_name=called_name)
                if _name is not None:
                    _new.append((_name, _scope, _end))
            if _calls or not self._matched_uses(node, ctx, [_rhs]):
                continue
            _name = self._append_binding_step(
                trace, _tgt, node, ctx, 'assign')
            if _name is not None:
                _new.append((_name, _scope, _end))
        return _new
    @staticmethod
    def _append_binding_step(trace: TaintTrace, target: ast.AST,
                             node: ast.AST, ctx: _PropagationCtx,
                             step_type: str, *,
                             called_name: str = "") -> str | None:
        if isinstance(target, ast.Starred):
            target = target.value
        if not isinstance(target, ast.Name):
            return None
        trace.propagation_chain.append({
            "type": step_type,
            "from_func": called_name,
            "from_var": ctx.var_name,
            "to_var": target.id,
            "line": node.lineno,
            "file": ctx.filepath,
        })
        return target.id
_CROSS_MOD_TREE_MEMO: dict[tuple, ast.Module | None] = {}
_CROSS_MOD_TREE_MEMO_LOCK = threading.Lock()
_CROSS_MOD_TREE_MEMO_MAX = 128
_MAX_PROPAGATION_DEPTH = 16
_AST_BRIDGE_STATE = threading.local()
#: 传播递归中「本树的 Call 节点列表」备忘。
#:
#: ``_trace_propagation`` 是递归的（深度上限 ``_MAX_PROPAGATION_DEPTH``），
#: 且每个源变量都会从根重新走一遍；每层都要把整棵树的节点枚举一遍再按
#: ``isinstance(ast.Call)`` 过滤。同一棵树在单个文件内被枚举几十次，
#: 结果却完全相同。此处按树身份备忘（真 LRU，容量很小）。
_CALL_NODES_MEMO: 'OrderedDict[int, tuple]' = OrderedDict()
_CALL_NODES_MEMO_LOCK = threading.Lock()
_CALL_NODES_MEMO_CAP = 8

def _call_nodes_of(tree: ast.Module) -> list:
    """返回 ``[n for n in walk_nodes(tree) if isinstance(n, ast.Call)]``。"""
    _key = id(tree)
    with _CALL_NODES_MEMO_LOCK:
        _hit = _CALL_NODES_MEMO.get(_key)
        if _hit is not None and _hit[0] is tree:
            _CALL_NODES_MEMO.move_to_end(_key)
            return _hit[1]
    calls = [node for node in walk_nodes(tree)
             if isinstance(node, ast.Call)]
    with _CALL_NODES_MEMO_LOCK:
        _CALL_NODES_MEMO[_key] = (tree, calls)
        _CALL_NODES_MEMO.move_to_end(_key)
        while len(_CALL_NODES_MEMO) > _CALL_NODES_MEMO_CAP:
            _CALL_NODES_MEMO.popitem(last=False)
    return calls

def _all_nodes_of(tree: ast.Module) -> tuple:
    """``walk_nodes`` 的别名（语义相同，仅表达「全节点」意图）。"""
    return walk_nodes(tree)
_SIBLING_WARMED_STATE = threading.local()
@contextmanager
def shared_ast_bridge(cache: Any | None):
    _prev = getattr(_AST_BRIDGE_STATE, 'cache', None)
    if cache is not None:
        _AST_BRIDGE_STATE.cache = cache
    try:
        yield
    finally:
        _AST_BRIDGE_STATE.cache = _prev
def _warmed_sibling_set(bridge: Any) -> frozenset[str]:
    warmed = getattr(_SIBLING_WARMED_STATE, 'value', (None, frozenset()))
    if warmed[0] is not bridge:
        try:
            _set = frozenset(os.path.abspath(p) for p in bridge.py_files)
        except Exception as _e:  # noqa: BLE001 — bridge API 兼容任意异常，失败降级空集
            _swallow('_warmed_sibling_set', _e)
            _set = frozenset()
        warmed = (bridge, _set)
        _SIBLING_WARMED_STATE.value = warmed
    return warmed[1]
def clear_taint_scope_memos() -> int:
    n = clear_scope_index_memo()
    with _CROSS_MOD_TREE_MEMO_LOCK:
        n += len(_CROSS_MOD_TREE_MEMO)
        _CROSS_MOD_TREE_MEMO.clear()
    with _SINK_RESOLVER_MEMO_LOCK:
        n += len(_SINK_RESOLVER_MEMO)
        _SINK_RESOLVER_MEMO.clear()
    warmed = getattr(_SIBLING_WARMED_STATE, 'value', (None, frozenset()))
    if warmed[0] is not None:
        n += 1
        _SIBLING_WARMED_STATE.value = (None, frozenset())
    return n
def _sibling_candidate_paths(module: str, filepath: str) -> list[str]:
    caller = os.path.abspath(filepath)
    base = os.path.dirname(caller)
    level = len(module) - len(module.lstrip('.'))
    candidates: list[str] = []
    if level:
        for _ in range(level - 1):
            parent = os.path.dirname(base)
            if parent == base:
                return []
            base = parent
        tail = module[level:]
        if tail:
            parts = tail.split('.')
            candidates.append(os.path.join(base, *parts, "__init__.py"))
            candidates.append(os.path.join(base, *parts) + ".py")
        else:
            candidates.append(os.path.join(base, "__init__.py"))
    else:
        parts = [part for part in module.split('.') if part]
        if not parts:
            return []
        candidates.append(os.path.join(base, *parts, "__init__.py"))
        candidates.append(os.path.join(base, *parts) + ".py")
        cur = base
        while True:
            if (os.path.isdir(os.path.join(cur, parts[0]))
                    or os.path.isfile(os.path.join(cur, parts[0]) + ".py")):
                candidates.append(
                    os.path.join(cur, *parts, "__init__.py"))
                candidates.append(os.path.join(cur, *parts) + ".py")
                break
            parent = os.path.dirname(cur)
            if parent == cur:
                break
            cur = parent
    unique: list[str] = []
    seen: set[str] = set()
    for cand in candidates:
        key = os.path.normcase(cand)
        if key == os.path.normcase(caller) or key in seen:
            continue
        seen.add(key)
        unique.append(cand)
    return unique
def _sibling_candidate_path(module: str, filepath: str) -> str | None:
    candidates = _sibling_candidate_paths(module, filepath)
    for cand in candidates:
        if os.path.isfile(cand):
            return cand
    return candidates[0] if candidates else None
def _load_via_bridge(cand: str, filepath: str) -> ast.Module | None:
    bridge = getattr(_AST_BRIDGE_STATE, 'cache', None)
    try:
        _warm = _warmed_sibling_set(bridge)
        if _warm:
            _caller = os.path.abspath(filepath)
            if _caller in _warm and os.path.abspath(cand) not in _warm:
                return None
        return bridge.get_ast(cand)
    except Exception as _e:  # noqa: BLE001 — 预热 bridge 任意异常降级 None（保守跳过不误报）
        _swallow('_load_via_bridge', _e)
        return None
def _read_sibling_bytes(cand: str) -> bytes | None:
    try:
        with open(cand, "rb") as fh:
            return fh.read()
    except FileNotFoundError as _swallowed_exc:
        logger.debug("_read_sibling_bytes: 兄弟模块不存在: %s",
                     _swallowed_exc, exc_info=True)
        return None
    except OSError as _e:
        _swallow('_read_sibling_bytes', _e)
        return None
def _parse_sibling_source(cand: str, content: bytes | None = None
                          ) -> ast.Module | None:
    if content is None:
        content = _read_sibling_bytes(cand)
    if content is None:
        return None
    source = decode_source(content)
    if source is None:
        return None
    try:
        return ast.parse(source, filename=cand)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e,
                      context=f'_parse_sibling_source:{type(_e).__name__}')
        return None
def _load_via_local_memo(cand: str) -> ast.Module | None:
    content = _read_sibling_bytes(cand)
    if content is None:
        return None
    key = (cand, hashlib.sha256(content).digest())
    with _CROSS_MOD_TREE_MEMO_LOCK:
        if key in _CROSS_MOD_TREE_MEMO:
            return _CROSS_MOD_TREE_MEMO[key]
    _tree = _parse_sibling_source(cand, content)
    with _CROSS_MOD_TREE_MEMO_LOCK:
        if key not in _CROSS_MOD_TREE_MEMO:
            while len(_CROSS_MOD_TREE_MEMO) >= _CROSS_MOD_TREE_MEMO_MAX:
                _CROSS_MOD_TREE_MEMO.pop(next(iter(_CROSS_MOD_TREE_MEMO)))
            _CROSS_MOD_TREE_MEMO[key] = _tree
        return _CROSS_MOD_TREE_MEMO[key]
def _load_sibling_module_tree(module: str, filepath: str) -> ast.Module | None:
    cand = _sibling_candidate_path(module, filepath)
    if cand is None:
        return None
    return (_load_via_bridge(cand, filepath)
            if getattr(_AST_BRIDGE_STATE, 'cache', None) is not None
            else _load_via_local_memo(cand))
register_cache_release(
    "taint_scope_memos", clear_taint_scope_memos, "污点域作用域 memo", order=50)
def _vulnerability_report(report, vulnerabilities: list,
                          exploit_paths: list) -> dict:
    return {
        "total_vulnerabilities": len(vulnerabilities),
        "vulnerabilities": vulnerabilities,
        "exploit_paths": exploit_paths,
        "tainted_variables": list(report.tainted_variables) if report else [],
        "total_sources": report.total_sources if report else 0,
        "total_sinks": report.total_sinks if report else 0,
        "sanitizers_used": report.sanitizers_used if report else 0,
    }
def _entry_sink_meta(sink) -> dict:
    return {
        "sink": getattr(sink, "name", "") if sink else "",
        "rule_id": f"TAINT-{sink.category}" if sink else "TAINT",
        "severity": sink.severity if sink else "P0",
        "category": sink.category if sink else "",
        "cwe_id": sink.cwe_id if sink else "",
    }
def _entry_source_meta(source) -> dict:
    return {
        "source_name": getattr(source, "name", "") if source else "",
        "source_category": getattr(source, "category", "") if source else "",
    }
def _flow_to_entry(flow) -> tuple[dict, str]:
    sink = getattr(flow, "sink", None)
    source = getattr(flow, "source", None)
    description = getattr(flow, "description", None)
    entry = {
        **_entry_sink_meta(sink),
        **_entry_source_meta(source),
        "message": description or "污点传播到危险 sink",
        "risk_level": getattr(flow, "risk_level", "P0"),
        "line": getattr(flow, "line", 0),
        "exploitability": getattr(flow, "exploitability", "unknown"),
    }
    return entry, description or ""
def _append_cross_module_entries(vulnerabilities: list, exploit_paths: list,
                                 source_code: Any, tree: ast.AST | None,
                                 filepath: str) -> None:
    if not filepath:
        return
    try:
        _xm_tree = tree if tree is not None else ast.parse(
            source_code, filename=filepath)
        for xv in cross_module_vulnerabilities(filepath, _xm_tree):
            vulnerabilities.append(xv)
            exploit_paths.append(xv.get("message", ""))
    except Exception:
        logger.warning("[TaintCrossModule] 跨模块汇点解析失败", exc_info=True)
def check_vulnerability(source_code: Any, tree: ast.AST | None = None,
                        filepath: str = _DEFAULT_FILEPATH) -> Any:
    filepath = os.fspath(filepath) if filepath else ""
    report = analyze_taint(source_code, tree=tree)
    if report is None:
        return _vulnerability_report(None, [], [])
    vulnerabilities: list = []
    exploit_paths: list = []
    for flow in report.flows:
        if not getattr(flow, "is_exploitable", False):
            continue
        entry, path_text = _flow_to_entry(flow)
        vulnerabilities.append(entry)
        exploit_paths.append(path_text)
    _append_cross_module_entries(
        vulnerabilities, exploit_paths, source_code, tree, filepath)
    return _vulnerability_report(report, vulnerabilities, exploit_paths)
def cross_module_vulnerabilities(filepath: str,
                                  tree: ast.Module | None) -> list[dict]:
    if tree is None:
        return []
    ctx = _CrossCallCtx.build(filepath, tree)
    out: list[dict] = []
    seen: set[tuple] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        c_scope = ctx.scopes.get(id(node), "")
        for module, func, source, sink_line, sink_name, _pval in (
                _iter_cross_sink_hits(
                    node, c_scope, ctx, SINK_NAMES,
                    lambda pval, sink_name, _scope=c_scope, _node=node:
                    _cross_binding_source(
                        ctx, _scope, pval, sink_name, _node))):
            call_line = getattr(node, "lineno", 0)
            call_col = getattr(node, "col_offset", 0)
            key = (module, func, sink_line, sink_name, source,
                   call_line, call_col)
            if key in seen:
                continue
            seen.add(key)
            entry = _cross_entry(
                module, func, sink_line, sink_name, source, ctx.filepath)
            entry.update({
                "call_file": ctx.filepath,
                "call_line": call_line,
                "call_col": call_col,
            })
            out.append(entry)
    return out
_MODULE_BLOCK_STMTS = (ast.If, *CONTAINER_STMTS)
def _iter_module_level_defs(tree: ast.Module):
    stack: list[ast.stmt] = list(reversed(getattr(tree, "body", ())))
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield cur
            continue
        if isinstance(cur, _MODULE_BLOCK_STMTS):
            for _body in reversed(container_sub_bodies(cur)):
                stack.extend(reversed(_body))
def _iter_callee_func_defs(callee_tree: ast.Module, func: str):
    defs = [n for n in _iter_module_level_defs(callee_tree)
            if n.name == func]
    for index in range(len(defs) - 1, -1, -1):
        if any(defs[index] is stmt for stmt in callee_tree.body):
            return defs[index:]
    return defs
def _iter_cross_sink_hits(node: ast.Call, scope: str, cross: _CrossCallCtx,
                          sink_names: frozenset, carries):
    module, func = _cross_resolve_target(node, scope, cross)
    if not module:
        return
    callee_tree = _load_sibling_module_tree(module, cross.filepath)
    if callee_tree is None:
        return
    names = _sink_name_resolver(callee_tree)
    for fd in _iter_callee_func_defs(callee_tree, func):
        for _pname, _pval in _iter_cross_bindings(node, fd):
            for hit in _param_sink_hits(fd, _pname, sink_names, names):
                source = carries(_pval, hit[1])
                if source is None:
                    continue
                yield module, func, source, hit[0], hit[1], _pval
@dataclass(frozen=True)
class _CrossCallCtx:
    filepath: str
    tree: ast.Module
    names: _SinkNameResolver
    mod_alias: dict
    from_import: dict
    module_nonimport: frozenset
    scopes: dict
    shadow: tuple
    parents: dict[int, ast.AST]
    expression_bindings: dict
    sink_states: dict = field(default_factory=dict)
    @classmethod
    def build(cls, filepath: str, tree: ast.Module) -> _CrossCallCtx:
        names = _sink_name_resolver(tree)
        return cls(
            filepath=filepath, tree=tree, names=names,
            mod_alias=_collect_module_aliases(tree),
            from_import=_collect_from_import_bindings(tree),
            module_nonimport=_module_nonimport_binds(tree),
            scopes=names.scope_index, shadow=names.shadow,
            # 同上：与 ``build_parent_map(tree)`` 同值，直接复用免得再走一遍。
            parents=names._parents,
            expression_bindings=names.expression_bindings)
def _collect_module_aliases(tree: ast.Module) -> dict[str, str]:
    mod_alias: dict[str, str] = {}
    for node in tree.body:
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            if alias.asname:
                mod_alias[alias.asname] = alias.name
                continue
            _head = alias.name.split('.')[0]
            mod_alias[_head] = _head
    return mod_alias
def _collect_from_import_bindings(tree: ast.Module) -> dict[str, tuple[str, str]]:
    from_import: dict[str, tuple[str, str]] = {}
    for node in tree.body:
        if not isinstance(node, ast.ImportFrom):
            continue
        _prefix = "." * node.level + (node.module or "")
        from_import.update({
            alias.asname or alias.name: (_prefix, alias.name)
            for alias in node.names})
    return from_import
def _relative_module(module: str, filepath: str) -> str | None:
    if not module:
        return None
    if module.startswith('.'):
        return module
    _head, _sep, _tail = module.partition('.')
    caller_package = os.path.basename(os.path.dirname(os.path.abspath(filepath)))
    if _head == caller_package:
        return _tail or "."
    return module
def _receiver_module(_dotted: str, ctx: _CrossCallCtx) -> str | None:
    _alias = ctx.mod_alias.get(_dotted)
    if _alias is not None:
        return _relative_module(_alias, ctx.filepath)
    _top, _sep, _rest = _dotted.partition('.')
    _top_mod = ctx.mod_alias.get(_top)
    if _top_mod is not None and _rest:
        return _relative_module(f"{_top_mod}.{_rest}", ctx.filepath)
    _origin = ctx.from_import.get(_dotted)
    if not _origin:
        return None
    _receiver = from_import_receiver(_origin)
    return (_relative_module(_receiver, ctx.filepath)
            if _receiver is not None else None)
def _call_target_parts(node: ast.Call, ctx: _CrossCallCtx
                       ) -> tuple[str | None, str, str] | None:
    if isinstance(node.func, ast.Attribute):
        _dotted = attr_chain_key(node.func.value)
        if not _dotted:
            return None
        return (_receiver_module(_dotted, ctx), node.func.attr,
                _dotted.split('.')[0])
    if isinstance(node.func, ast.Name):
        module, func = ctx.from_import.get(node.func.id,
                                           (None, node.func.id))
        return _relative_module(module, ctx.filepath), func, node.func.id
    return None
def _cross_resolve_target(node: ast.Call, c_scope: str,
                          ctx: _CrossCallCtx):
    if _call_root_binding(node, ctx.expression_bindings) is not None:
        return None, None
    canonical = ctx.names.imported_call_name(node)
    if canonical is None and isinstance(node.func, ast.Attribute):
        prefix = ctx.names._receiver_prefix(
            c_scope, node.func.value, node)
        if prefix:
            canonical = f"{prefix}.{node.func.attr}"
    scoped_import = bool(canonical and "." in canonical)
    origin = ctx.names.imported_from_origin(node)
    from_package = bool(
        origin and set(origin[0]) == {'.'}
        and canonical == from_import_receiver(origin))
    if from_package:
        module, func = origin
        call_owner = node.func.id
    elif scoped_import:
        module, _sep, func = canonical.rpartition(".")
        module = _relative_module(module, ctx.filepath)
        if isinstance(node.func, ast.Name):
            call_owner = node.func.id
        else:
            owner_chain = attr_chain_key(node.func.value)
            call_owner = owner_chain.split('.')[0] if owner_chain else ""
    else:
        parts = _call_target_parts(node, ctx)
        if parts is None:
            return None, None
        module, func, call_owner = parts
    if module is None:
        return None, None
    if ((not scoped_import and call_owner in ctx.module_nonimport)
            or (not scoped_import and owner_scope(
                c_scope, call_owner, ctx.shadow[0], ctx.shadow[1],
                ctx.shadow[2]) != "")):
        return None, None
    return module, func
def _expand_literal_starred_args(args) -> list:
    expanded = []
    for arg in args:
        if (isinstance(arg, ast.Starred)
                and isinstance(arg.value, (ast.List, ast.Tuple))):
            expanded.extend(arg.value.elts)
        else:
            expanded.append(arg)
    return expanded
def _positional_bindings(args, params: list[str]):
    bindings = []
    next_param = 0
    unknown_starred = False
    for arg in args:
        if isinstance(arg, ast.Starred):
            unknown_starred = True
            bindings.extend((name, arg.value) for name in params[next_param:])
            continue
        if not unknown_starred:
            if next_param < len(params):
                bindings.append((params[next_param], arg))
                next_param += 1
            continue
        bindings.extend((name, arg) for name in params[next_param:])
    unique = []
    seen = set()
    for name, value in bindings:
        key = (name, id(value))
        if key not in seen:
            seen.add(key)
            unique.append((name, value))
    return unique
def _literal_dict_keyword_items(value) -> list[tuple[str, ast.AST]] | None:
    if not isinstance(value, ast.Dict):
        return None
    items: dict[str, ast.AST] = {}
    for key, item_value in zip(value.keys, value.values):
        if (not isinstance(key, ast.Constant)
                or not isinstance(key.value, str)):
            return None
        items[key.value] = item_value
    return list(items.items())
def _cross_keyword_items(keywords) -> list:
    items = []
    for keyword in keywords:
        if keyword.arg is not None:
            items.append((keyword.arg, keyword.value))
            continue
        literal_items = _literal_dict_keyword_items(keyword.value)
        if literal_items is None:
            items.append((None, keyword.value))
        else:
            items.extend(literal_items)
    return items
def _keyword_bindings(keyword_items, bindable: set[str],
                      positional_bound: set[str]):
    bindings = []
    explicit_names = {name for name, _value in keyword_items if name is not None}
    available = bindable - positional_bound
    for name, value in keyword_items:
        if value is None:
            continue
        if name is not None:
            if name in available:
                bindings.append((name, value))
            continue
        bindings.extend((candidate, value)
                        for candidate in sorted(available - explicit_names))
    return bindings
def _iter_cross_bindings(node: ast.Call, fd):
    params = _positional_param_names(fd)
    bindable = {a.arg for a in fd.args.args if a.arg in params}
    bindable |= {a.arg for a in fd.args.kwonlyargs}
    positional_args = _expand_literal_starred_args(node.args)
    keyword_items = _cross_keyword_items(node.keywords)
    positional_bindings = _positional_bindings(positional_args, params)
    if any(isinstance(arg, ast.Starred) for arg in positional_args):
        explicit_names = {name for name, _value in keyword_items
                          if name is not None}
        positional_bindings = [
            (name, value) for name, value in positional_bindings
            if name not in explicit_names]
    positional_bound = {name for name, _value in positional_bindings}
    bindings = positional_bindings + _keyword_bindings(
        keyword_items, bindable, positional_bound)
    vararg = fd.args.vararg
    if vararg is not None:
        unknown_index = next((index for index, arg in enumerate(positional_args)
                              if isinstance(arg, ast.Starred)), None)
        extra_args = (positional_args[len(params):] if unknown_index is None
                      else positional_args[unknown_index:])
        bindings.extend(
            (vararg.arg, arg.value if isinstance(arg, ast.Starred) else arg)
            for arg in extra_args)
    kwarg = fd.args.kwarg
    if kwarg is not None:
        bindings.extend(
            (kwarg.arg, value) for name, value in keyword_items
            if value is not None and (name is None or name not in bindable))
    return bindings
def _cross_source_category(src_name: str) -> str:
    src = next((s for s in BUILTIN_SOURCES if s.name == src_name), None)
    if src is not None:
        return src.category
    return TAINT_SOURCE_CATEGORY_BY_NAME.get(src_name, "")
def _cross_entry(module: str, func: str, sink_line: int,
                 sink_name: str, src_name: str, filepath: str = _DEFAULT_FILEPATH) -> dict:
    sink = _SINK_BY_NAME[sink_name]
    display_target = (f"{module}{func}" if module and set(module) == {'.'}
                      else f"{module}.{func}")
    relpath = module.lstrip('.').replace('.', '/') + ".py"
    candidate = (_sibling_candidate_path(module, filepath)
                 if filepath else None)
    if candidate is not None:
        try:
            relpath = os.path.relpath(
                candidate, os.path.dirname(os.path.abspath(filepath))).replace(
                    os.sep, '/')
        except ValueError as _rel_err:
            logger.debug("[TaintCrossModule] 跨盘符相对路径降级: %s", _rel_err)
    return {
        "rule_id": f"TAINT-{sink.category}",
        "source_name": src_name,
        "source_category": _cross_source_category(src_name),
        "severity": sink.severity,
        "category": sink.category,
        "cwe_id": sink.cwe_id,
        "message": (f"跨文件污点流: {src_name} → {display_target}()"
                    f" → {sink_name}（{relpath}:{sink_line}）"),
        "risk_level": sink.severity,
        "line": sink_line,
        "file": relpath,
        "sink": sink_name,
        "exploitability": "medium",
        "cross_module": True,
    }
def _cross_binding_source(ctx: _CrossCallCtx, c_scope: str,
                          pval: ast.AST, sink_name: str,
                          node: ast.Call) -> str | None:
    state = _sink_taint_state(
        ctx.sink_states, ctx.tree, SOURCE_NAMES, ctx.names, sink_name)
    return _state_expr_source(
        c_scope, pval, state, ctx.shadow, ctx.names, node,
        ctx.expression_bindings, ctx.parents)
def _module_nonimport_binds(tree: ast.Module) -> frozenset[str]:
    names: set[str] = set()
    _walk_block(tree, names)
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _global_write_binds(node, names)
    return frozenset(names)
def _global_write_binds(
        func_def: ast.FunctionDef | ast.AsyncFunctionDef, names: set) -> None:
    _declared: set[str] = set()
    _bound: set[str] = set()
    for sub in iter_own_scope(func_def, skip_lambda=True):
        if isinstance(sub, ast.Global):
            _declared.update(sub.names)
            continue
        collect_binding_names(sub, _bound, include_imports=False)
    names.update(_declared & _bound)
def _walk_block(n: ast.AST, names: set) -> None:
    stack = [n]
    while stack:
        cur = stack.pop()
        for child in ast.iter_child_nodes(cur):
            if collect_binding_names(child, names, include_imports=False):
                continue
            stack.append(child)
def _bound_in_inner_scope(scope: str, name: str,
                          shadow: tuple | None) -> bool:
    if shadow is None or not scope:
        return False
    return owner_scope(scope, name, shadow[0], shadow[1], shadow[2]) != ""
def _reaches_param(events: list[_FlowEvent], context: _FlowContext,
                   name_node: ast.Name, param: str) -> bool:
    position = (getattr(name_node, "lineno", 0),
                getattr(name_node, "col_offset", 0))
    statement = _statement_for_node(name_node, context.parents)
    def _upstream(state):
        var, pos, use_statement = state
        upstream = set()
        for event in context.active(
                events, var, position=pos, use_statement=use_statement):
            event_pos = _event_position(event)
            upstream.update(
                (_name.id, event_pos, event.node)
                for _name in iter_free_load_names(event.value))
        return upstream
    for var, pos, use_statement in _bfs_visit(
            (name_node.id, position, statement), _upstream):
        if var != param:
            continue
        reaching = context.active(
            events, var, position=pos, use_statement=use_statement)
        overwritten = any(
            event.strong and _block_dominates(
                context.tree, context.parents, event.block, use_statement)
            for event in reaching)
        if not overwritten:
            return True
    return False
def _comprehension_chain(
        name_node: ast.Name, parents: dict[int, ast.AST]) -> list[ast.AST]:
    chain: list[ast.AST] = []
    current = parents.get(id(name_node))
    while current is not None:
        if isinstance(current, COMP_SCOPE_NODES):
            chain.append(current)
        if isinstance(current, (ast.FunctionDef, ast.AsyncFunctionDef)):
            break
        current = parents.get(id(current))
    return chain
def _comprehension_reaches_param(
        name_node: ast.Name, param: str, events: list[_FlowEvent],
        context: _FlowContext, parents: dict[int, ast.AST]) -> bool:
    chain = _comprehension_chain(name_node, parents)
    reaching: dict[str, bool] = {}
    for comp in reversed(chain):
        for generator in comp.generators:
            iter_reaches = False
            for source in iter_free_load_names(generator.iter):
                source_reaches = reaching.get(source.id)
                if source_reaches is None:
                    source_reaches = _reaches_param(
                        events, context, source, param)
                if source_reaches:
                    iter_reaches = True
                    break
            for target_name in iter_unpack_target_names(generator.target):
                reaching[target_name] = iter_reaches
    return reaching.get(name_node.id, False)
def _param_sink_hits(func_def: ast.FunctionDef | ast.AsyncFunctionDef,
                     param: str, sink_names: frozenset,
                     names: _SinkNameResolver
                     ) -> list[tuple[int, str]]:
    parents = build_parent_map(func_def)
    events = [
        event for event in _flow_events(func_def, parents)
        if event.scope == id(func_def)
    ]
    scopes = build_scope_index(func_def)
    shadow = collect_shadow_bindings(func_def)
    sanitized_by_sink: dict[str, dict] = {}
    expression_bindings = names.expression_bindings
    own_positions = set()
    for own_node in iter_own_scope(func_def, skip_lambda=True):
        own_positions.add((getattr(own_node, "lineno", 0),
                           getattr(own_node, "col_offset", 0)))
        own_positions.add((getattr(own_node, "end_lineno", 0),
                           getattr(own_node, "end_col_offset", 0)))
    contexts: dict[int, _FlowContext] = {}
    hits: list[tuple[int, str]] = []
    for node in iter_own_scope(func_def, skip_lambda=True):
        if not isinstance(node, ast.Call):
            continue
        sink = names.sink_name(node, sink_names)
        if sink is None:
            continue
        sanitizer_names = _builtin_sanitizer_names_for_sink(sink)
        sanitized_keys = sanitized_by_sink.get(sink)
        if sanitized_keys is None:
            sanitized_keys = collect_sanitized_keys(
                func_def, sanitizer_names, scopes, shadow,
                call_name_candidates=names.candidates)
            sanitized_keys = {
                key: [
                    entry for entry in timeline
                    if (entry[0], entry[1]) in own_positions
                ]
                for key, timeline in sanitized_keys.items()
            }
            sanitized_by_sink[sink] = sanitized_keys
        scope = scopes.get(id(node), "")
        context = contexts.get(node.lineno)
        if context is None:
            context = _FlowContext(func_def, node.lineno, parents)
            contexts[node.lineno] = context
        sanitized_at_use = _sanitized_keys_at_use(
            sanitized_keys, events, _statement_for_node(
                node, context.parents))
        for arg in _sink_payload_args(
                node, _SINK_BY_NAME.get(sink)):
            reached = False
            for _name_node in iter_free_load_names(arg):
                inner_owner = expression_bindings.get(
                    id(_name_node), {}).get(_name_node.id)
                if isinstance(inner_owner, ast.Lambda):
                    continue
                inner_shadowed = _bound_in_inner_scope(
                    scope, _name_node.id, shadow)
                if isinstance(inner_owner, COMP_SCOPE_NODES) or inner_shadowed:
                    if not _comprehension_reaches_param(
                            _name_node, param, events, context, parents):
                        continue
                elif not _reaches_param(
                        events, context, _name_node, param):
                    continue
                key = TaintNameResolution.owner_key(
                    scope, _name_node.id, shadow)
                if is_sanitized(
                        node, scope=scope,
                        sanitized_keys=sanitized_at_use, shadow=shadow,
                        tainted_vars={key: 1},
                        sanitizer_names=sanitizer_names,
                        call_name_candidates=names.candidates,
                        argument_nodes=_sink_payload_args(
                            node, _SINK_BY_NAME.get(sink)),
                        check_inline_sources=False):
                    continue
                hits.append((node.lineno, sink))
                reached = True
                break
            if reached:
                break
    return hits

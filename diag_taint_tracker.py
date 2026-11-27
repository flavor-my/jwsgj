from __future__ import annotations

import ast
import builtins
import logging
import os
import re
import threading
from collections import deque
from collections.abc import Iterator
from dataclasses import (
    dataclass,
    field,
    replace,
)
from itertools import chain
from typing import (
    Any,
    ClassVar,
)

from jwsgj.diag_shared_ast_bindings import (
    build_scope_index,
    collect_binding_names,
    collect_shadow_bindings,
)
from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    build_parent_map,
    collect_param_names,
    dotted_name,
    iter_own_scope,
    iter_unpack_target_names,
    resolve_call_name,
)
from jwsgj.diag_shared_ast_views import tree_nodes
from jwsgj.diag_shared_source_core import (
    parse_guard_cached,
    read_py_source_with_error,
)
from jwsgj.diag_taint_dataflow import (
    SCALAR_SANITIZER_CALLS,
    _binding_activation_pos,
    _binding_forms,
    collect_sanitized_keys,
    collect_source_taints,
    is_sanitized,
    lookup_name_assignment,
    propagate_taints,
)
from jwsgj.diag_taint_model import (
    BUILTIN_SANITIZERS,
    BUILTIN_SINKS,
    BUILTIN_SOURCES,
    SINK_NAMES,
    SOURCE_NAMES,
    TaintNameResolution,
    TaintSanitizer,
    TaintSink,
    TaintSource,
    _iter_value_channel_nodes,
    assignment_form,
    first_taint_source,
    taint_source_of,
)
from jwsgj.diag_types_normalize import (
    coerce_line,
    finding_file_path,
    safe_int,
)
from jwsgj.diag_types_vocab import (
    MSG_SYNTAX_ERROR_SKIP,
    PARSE_DEGRADE_EXC,
    TAINT_LOCAL_TRUSTED_CATEGORIES,
)
from jwsgj.prevention_scope_facts import walk_nodes

__all__ = [
    'BackwardTaintEngine',
    'BidirectionalResult',
    'BidirectionalTaintFlow',
    'ForwardTaintProxy',
    'TaintFlow',
    'TaintPath',
    'TaintReport',
    'TaintTracker',
    'analyze_taint',
    'validate_security_findings',
]
logger = logging.getLogger(__name__)
_HOP_TIERS: tuple[tuple[int, str], ...] = (
    (2, "high"),
    (4, "medium"),
    (6, "low"),
)
def walk_segments(nodes, bound: frozenset[str]):
    items = tuple(nodes)
    return list(zip(items, (bound,) * len(items), strict=True))
def lambda_walk_segments(
        node: ast.Lambda, bound: frozenset[str]
        ) -> list[tuple[ast.AST, frozenset[str]]]:
    params = bound | frozenset(collect_param_names(node))
    defaults = [*node.args.defaults, *filter(None, node.args.kw_defaults)]
    return walk_segments(defaults, bound) + [(node.body, params)]
def comprehension_walk_segments(
        node: ast.ListComp | ast.SetComp | ast.GeneratorExp | ast.DictComp,
        bound: frozenset[str]) -> list[tuple[ast.AST, frozenset[str]]]:
    segments: list[tuple[ast.AST, frozenset[str]]] = []
    inner = bound
    for generator in node.generators:
        segments.append((generator.iter, inner))
        inner = inner | frozenset(iter_unpack_target_names(generator.target))
        for condition in generator.ifs:
            segments.append((condition, inner))
    values = ((node.key, node.value) if isinstance(node, ast.DictComp)
              else (node.elt,))
    segments.extend(walk_segments(values, inner))
    return segments
def _walrus_bindings(expr: ast.AST):
    bindings: dict[int, list[tuple[str, tuple[int, int], tuple]]] = {}
    parents: dict[int, int] = {}
    paths: dict[int, tuple] = {}
    stack: list[tuple[ast.AST, ast.AST, tuple]] = [(expr, expr, ())]
    while stack:
        cur, owner, path = stack.pop()
        paths[id(cur)] = path
        if isinstance(cur, ast.NamedExpr):
            end = expr_end(cur)
            for name in iter_unpack_target_names(cur.target):
                bindings.setdefault(id(owner), []).append((name, end, path))
        if isinstance(cur, ast.Lambda):
            if cur is not owner:
                parents[id(cur)] = id(owner)
            defaults = [*cur.args.defaults,
                        *filter(None, cur.args.kw_defaults)]
            segments = [(child, owner, path) for child in defaults]
            segments.append((cur.body, cur, ()))
        elif isinstance(cur, COMP_SCOPE_NODES):
            if cur is not owner:
                parents[id(cur)] = id(owner)
            children = []
            for generator in cur.generators:
                children.extend([generator.iter, generator.target,
                                 *generator.ifs])
            children.extend((cur.key, cur.value) if isinstance(cur, ast.DictComp)
                            else (cur.elt,))
            segments = [(child, cur, ()) for child in children]
        elif isinstance(cur, ast.IfExp):
            segments = [
                (cur.test, owner, path),
                (cur.body, owner, (*path, (cur, 0))),
                (cur.orelse, owner, (*path, (cur, 1))),
            ]
        elif isinstance(cur, ast.BoolOp):
            segments = [
                (child, owner,
                 path if index == 0 else (*path, (cur, index)))
                for index, child in enumerate(cur.values)
            ]
        else:
            segments = [(child, owner, path)
                        for child in ast.iter_child_nodes(cur)]
        stack.extend(segments)
    return bindings, parents, paths
def _conditional_path_covers(binding_path: tuple, name_path: tuple) -> bool:
    for root, binding_branch in binding_path:
        name_branch = next((branch for node, branch in name_path
                            if node is root), None)
        if isinstance(root, ast.IfExp):
            if name_branch != binding_branch:
                return False
        elif name_branch is None or name_branch < binding_branch:
            return False
    return True
def _walrus_covers(name_node: ast.Name, owner: ast.AST,
                   bindings: dict, parents: dict[int, int],
                   paths: dict[int, tuple]) -> bool:
    pos = (getattr(name_node, 'lineno', 0),
           getattr(name_node, 'col_offset', 0))
    name_path = paths.get(id(name_node), ())
    owner_id: int | None = id(owner)
    while owner_id is not None:
        for name, end, binding_path in bindings.get(owner_id, ()):
            if (name == name_node.id and end <= pos
                    and _conditional_path_covers(binding_path, name_path)):
                return True
        owner_id = parents.get(owner_id)
    return False
def _walk_free_load_names(node: ast.AST, bound: frozenset[str],
                          bindings: dict, parents: dict[int, int],
                          paths: dict[int, tuple], owner: ast.AST):
    stack: list[tuple[ast.AST, frozenset[str], ast.AST]] = [(node, bound, owner)]
    while stack:
        cur, cur_bound, cur_owner = stack.pop()
        if isinstance(cur, ast.Name):
            if (isinstance(cur.ctx, ast.Load) and cur.id not in cur_bound
                    and not _walrus_covers(
                        cur, cur_owner, bindings, parents, paths)):
                yield cur
            continue
        if isinstance(cur, ast.Lambda):
            segments = [
                (child, child_bound, cur if child is cur.body else cur_owner)
                for child, child_bound in lambda_walk_segments(cur, cur_bound)]
        elif isinstance(cur, COMP_SCOPE_NODES):
            segments = [
                (child, child_bound, cur)
                for child, child_bound in comprehension_walk_segments(
                    cur, cur_bound)]
        else:
            segments = [(child, cur_bound, cur_owner)
                        for child in ast.iter_child_nodes(cur)]
        stack.extend(reversed(segments))
def iter_free_load_names(expr: ast.AST):
    bindings, parents, paths = _walrus_bindings(expr)
    yield from _walk_free_load_names(
        expr, frozenset(), bindings, parents, paths, expr)
def from_import_receiver(origin: tuple[str, str]) -> str | None:
    _module, _name = origin
    if _module.startswith('.'):
        separator = "" if set(_module) == {'.'} else "."
        return f"{_module}{separator}{_name}"
    return f"{_module}.{_name}" if _module else _name
def _with_builtin_name_aliases(names) -> list[str]:
    out = list(dict.fromkeys(name for name in names if name))
    out.extend(name.removeprefix('builtins.') for name in tuple(out)
               if name.startswith('builtins.'))
    return list(dict.fromkeys(out))
def _call_root_binding(node: ast.AST, expression_bindings: dict):
    if not isinstance(node, ast.Call):
        return None
    root = dotted_name(node.func)
    if not root:
        return None
    return expression_bindings.get(id(node), {}).get(root.split('.')[0])
def _inner_binding_owners(root: ast.AST) -> dict[int, dict[str, ast.AST]]:
    owners: dict[int, dict[str, ast.AST]] = {}
    stack: list[tuple[ast.AST, dict[str, ast.AST]]] = [(root, {})]
    while stack:
        cur, bound = stack.pop()
        owners[id(cur)] = bound
        if isinstance(cur, ast.Lambda):
            defaults = [*cur.args.defaults,
                        *filter(None, cur.args.kw_defaults)]
            segments = [(child, bound) for child in defaults]
            body_bound = {**bound, **{
                name: cur for name in collect_param_names(cur)}}
            segments.append((cur.body, body_bound))
        elif isinstance(cur, COMP_SCOPE_NODES):
            segments = []
            inner = bound
            for generator in cur.generators:
                segments.append((generator.iter, inner))
                inner = {**inner, **{
                    name: cur for name in iter_unpack_target_names(
                        generator.target)}}
                segments.extend((condition, inner)
                                for condition in generator.ifs)
            values = ((cur.key, cur.value) if isinstance(cur, ast.DictComp)
                      else (cur.elt,))
            segments.extend((value, inner) for value in values)
        else:
            segments = [(child, bound)
                        for child in ast.iter_child_nodes(cur)]
        stack.extend(reversed(segments))
    return owners
def expr_end(node: ast.AST) -> tuple[int, int]:
    _line = getattr(node, "end_lineno", None)
    _col = getattr(node, "end_col_offset", None)
    if _line is None or _col is None:
        return (getattr(node, "lineno", 0) or 0,
                getattr(node, "col_offset", 0) or 0)
    return _line, _col
_SINK_METADATA_KEYWORDS = frozenset({
    "env", "cwd", "timeout", "capture_output", "text", "encoding", "errors",
    "check", "shell", "stdin", "stdout", "stderr", "input", "newline", "mode",
    "buffering", "closefd", "opener", "dir_fd", "follow_symlinks", "exist_ok",
    "start", "stop", "creationflags", "startupinfo", "preexec_fn", "pass_fds",
    "user", "group", "extra_groups", "umask", "restore_signals", "close_fds",
    "process_group", "bufsize", "universal_newlines", "limit", "bytes",
    "params", "parameters",
})
def _payload_mentions(node: ast.Call, var_name: str,
                      sink: TaintSink | None = None) -> bool:
    return any(_n.id == var_name
               for _arg in _sink_payload_args(node, sink)
               for _n in iter_free_load_names(_arg))
_VARIADIC_PAYLOAD_SINKS = frozenset({"os.path.join"})
def _sink_payload_args(node: ast.Call,
                       sink: TaintSink | None = None) -> list[ast.expr]:
    return [
        *(_arg for _index, _arg in enumerate(node.args)
          if sink is None or not sink.dangerous_params
          or _index in sink.dangerous_params
          or (sink.name in _VARIADIC_PAYLOAD_SINKS
              and _index >= min(sink.dangerous_params))
          or isinstance(_arg, ast.Starred)),
        *(kw.value for kw in node.keywords
          if kw.value is not None
          and (kw.arg is None or kw.arg not in _SINK_METADATA_KEYWORDS)),
    ]
@dataclass
class TaintFlow:
    source: TaintSource | None = None
    sink: TaintSink | None = None
    is_exploitable: bool = True
    risk_level: str = "P0"
    description: str = ""
    exploitability: str = "unknown"
    line: int = 0
@dataclass
class TaintReport:
    file_path: str = ""
    flows: list[TaintFlow] = field(default_factory=list)
    tainted_variables: list[str] = field(default_factory=list)
    total_sources: int = 0
    total_sinks: int = 0
    sanitizers_used: int = 0
@dataclass
class _SinkScanCtx:
    tree: ast.AST
    tainted_vars: dict
    taint_hops: dict
    sink_names: set
    source_names: set
    taint_origins: dict | None
    scope_idx: dict[int, str]
    sanitized_keys: dict
    shadow: tuple[dict, dict, frozenset]
    sanitizer_names: set
    names: _SinkNameResolver
    parents: dict[int, ast.AST]
    flow_events: list[_FlowEvent] = field(default_factory=list)
    sink_states: dict[frozenset, tuple] = field(default_factory=dict)
    counted_inline_source_nodes: set[int] = field(default_factory=set)
def _registry_names(entries) -> set:
    return {entry.name for entry in entries}
_UNIVERSAL_SANITIZER_CATEGORIES = frozenset({'type_cast', 'hash_sanitize'})
_SANITIZER_SINK_CATEGORIES = {
    'xss_prevention': frozenset({'xss'}),
    'cmd_injection_prevention': frozenset({'command_injection'}),
    'path_sanitize': frozenset({'path_traversal'}),
}
def _universal_sanitizer_names(sanitizers) -> set[str]:
    return set(SCALAR_SANITIZER_CALLS) | {
        item.name for item in sanitizers
        if item.category in _UNIVERSAL_SANITIZER_CATEGORIES
    }
def _sanitizer_names_for_sink(sanitizers, sink: TaintSink | None) -> set[str]:
    sink_category = sink.category if sink is not None else ''
    names = _universal_sanitizer_names(sanitizers)
    for item in sanitizers:
        allowed = _SANITIZER_SINK_CATEGORIES.get(item.category)
        if ((allowed is not None and sink_category in allowed)
                or (allowed is None and sink_category
                    and item.category == sink_category)):
            names.add(item.name)
    return names
_SINK_BY_NAME: dict[str, Any] = {item.name: item for item in BUILTIN_SINKS}
def _builtin_sanitizer_names_for_sink(sink_name: str) -> set[str]:
    return _sanitizer_names_for_sink(
        BUILTIN_SANITIZERS, _SINK_BY_NAME.get(sink_name))
def _star_import_kind(kind, name: str):
    if kind is None or kind[0] != 'from' or kind[2] != '*':
        return None
    return 'from', kind[1], name
def _comp_iter_hit(expr: ast.AST, env: dict, scope: str,
                   ctx: _SinkScanCtx):
    for _n in iter_free_load_names(expr):
        owner = ctx.names.expression_bindings.get(
            id(_n), {}).get(_n.id)
        if isinstance(owner, ast.Lambda):
            continue
        if isinstance(owner, COMP_SCOPE_NODES):
            _hit = env.get(_n.id)
            if _hit is not None:
                return _hit
            continue
        _hit = env.get(_n.id)
        if _hit is not None:
            return _hit
    for _n in iter_free_load_names(expr):
        owner = ctx.names.expression_bindings.get(
            id(_n), {}).get(_n.id)
        if (isinstance(owner, (ast.Lambda, *COMP_SCOPE_NODES))
                or _n.id in env):
            continue
        _key = TaintNameResolution.resolve_taint_key(
            scope, _n.id, ctx.tainted_vars, ctx.shadow)
        if _key is not None:
            return (ctx.taint_origins.get(_key, ""),
                    ctx.taint_hops.get(_key, 1))
    _src = TaintTracker._inline_source_name(expr, ctx)
    return (_src, 1) if _src else None
def _comprehension_env(node: ast.AST, scope: str,
                       ctx: _SinkScanCtx) -> dict:
    env: dict[str, tuple[str, int] | None] = {}
    for _gen in _comprehension_visible_generators(node, ctx.parents):
        _hit = _comp_iter_hit(_gen.iter, env, scope, ctx)
        for _name in iter_unpack_target_names(_gen.target):
            env[_name] = _hit
    return env
_CONSTRUCTOR_SINK_TAILS: frozenset[str] = frozenset(
    name.rsplit('.', 1)[1] for name in SINK_NAMES
    if '.' in name and name.split('.', 1)[0][:1].isupper())
def _import_scope(node: ast.AST, parents: dict[int, ast.AST]) -> str:
    parts: list[str] = []
    cur = parents.get(id(node))
    while cur is not None and not isinstance(cur, ast.Module):
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef)):
            parts.append(cur.name)
        elif isinstance(cur, ast.Lambda):
            parts.append(f"<lambda>@{cur.lineno}")
        cur = parents.get(id(cur))
    return '.'.join(reversed(parts))
def _collect_binding_kinds(tree: ast.Module, scopes: dict[int, str],
                           parents: dict | None = None
                           ) -> dict[tuple[str, str], list[tuple]]:
    kinds: dict[tuple[str, str], list[tuple]] = {}
    nodes = sorted(
        tree_nodes(tree),
        key=lambda _n: (getattr(_n, 'lineno', 0),
                        getattr(_n, 'col_offset', 0)))
    if parents is None:
        parents = build_parent_map(tree)
    for node in nodes:
        scope = scopes.get(id(node))
        if scope is None and isinstance(node, (ast.Import, ast.ImportFrom)):
            scope = _import_scope(node, parents)
        scope = scope or ""
        block = _flow_event_block(node, parents)
        if isinstance(node, ast.Import):
            position = expr_end(node)
            for alias in node.names:
                name = alias.asname or alias.name.split('.')[0]
                receiver = (alias.name if alias.asname
                            else alias.name.split('.')[0])
                kinds.setdefault((scope, name), []).append(
                    (*position, ('import', receiver), block))
            continue
        if isinstance(node, ast.ImportFrom):
            position = expr_end(node)
            prefix = '.' * node.level + (node.module or "")
            for alias in node.names:
                name = alias.asname or alias.name
                kinds.setdefault((scope, name), []).append(
                    (*position, ('from', prefix, alias.name), block))
            continue
        names: set[str] = set()
        collect_binding_names(node, names, include_imports=False)
        bound_names: set[str] = set()
        for targets, value in _binding_forms(node):
            activation = expr_end(value)
            for target in targets:
                for name in iter_unpack_target_names(target):
                    bound_names.add(name)
                    kinds.setdefault((scope, name), []).append(
                        (*activation, None, block))
        activation = _binding_activation_pos(node)
        for name in names - bound_names:
            kinds.setdefault((scope, name), []).append(
                (*activation, None, block))
    return kinds
def _sink_name_resolver(tree: ast.Module) -> _SinkNameResolver:
    """按树对象身份取（或构建）汇点名字解析器。

    容量控制采用**真 LRU**（命中移队尾、满则逐出最久未用的一项），而不是
    「满即 ``clear()``」。原因（实测）：该 memo 的条目数随扫描文件数线性增长
    （12 个文件 66 条，≈5.5 条/文件），307 个文件必然撞上上限；一旦整体清空，
    所有 sibling 模块的解析器全部作废并逐个重建（单个 0.586 s），形成周期性
    重建雪崩。

    每个条目是一个完整模块 AST 的 5 份派生字典（``scope_index``/``shadow``/
    ``expression_bindings``/``_parents``/``_bindings``，实测约 2 MB），因此
    容量上界直接决定了内存上界：512 条 ≈ 1 GB，128 条 ≈ 256 MB。
    """
    with _SINK_RESOLVER_MEMO_LOCK:
        _hit = _SINK_RESOLVER_MEMO.pop(id(tree), None)
        if _hit is not None and _hit[0] is tree:
            # 命中：移回队尾，避免热条目被先逐出。
            _SINK_RESOLVER_MEMO[id(tree)] = _hit
            return _hit[1]
    _resolver = _SinkNameResolver(tree)
    with _SINK_RESOLVER_MEMO_LOCK:
        _SINK_RESOLVER_MEMO[id(tree)] = (tree, _resolver)
        while len(_SINK_RESOLVER_MEMO) > _SINK_RESOLVER_MEMO_CAP:
            _SINK_RESOLVER_MEMO.pop(next(iter(_SINK_RESOLVER_MEMO)), None)
    return _resolver
_BIND_IMPORT = 'import'
_IMPORT_BINDING_KINDS = frozenset({_BIND_IMPORT, 'from'})
_BIND_REBIND = 'rebind'
_BIND_PARAM = 'param'
_BIND_NONE = 'none'
_RESOLVER_UNSET = object()
class _SinkNameResolver:
    """按 AST 树提供汇点名字解析的派生索引集合。

    五个索引（``scope_index`` / ``shadow`` / ``expression_bindings`` /
    ``_parents`` / ``_bindings``）各自是一次整树遍历，且存在依赖顺序
    （``_bindings`` 依赖前两者）。构建耗时实测 0.48 s/模块，而大多数调用点
    只用其中一两个（例如 ``_iter_cross_sink_hits`` 只查汇点名）。

    因此改为**按需惰性构建**：取到哪个属性才算哪个。语义与一次性全建完全
    等价（纯函数、结果相同），只省略了没被用到的遍历。
    """
    def __init__(self, tree: ast.Module) -> None:
        self._tree = tree
        self._scope_index: Any = _RESOLVER_UNSET
        self._shadow: Any = _RESOLVER_UNSET
        self._expression_bindings: Any = _RESOLVER_UNSET
        self._parents_cache: Any = _RESOLVER_UNSET
        self._bindings_cache: Any = _RESOLVER_UNSET
    @property
    def scope_index(self) -> dict:
        if self._scope_index is _RESOLVER_UNSET:
            self._scope_index = build_scope_index(self._tree)
        return self._scope_index
    @property
    def shadow(self):
        if self._shadow is _RESOLVER_UNSET:
            self._shadow = collect_shadow_bindings(self._tree)
        return self._shadow
    @property
    def expression_bindings(self) -> dict:
        if self._expression_bindings is _RESOLVER_UNSET:
            self._expression_bindings = _inner_binding_owners(self._tree)
        return self._expression_bindings
    @property
    def _parents(self) -> dict:
        if self._parents_cache is _RESOLVER_UNSET:
            self._parents_cache = build_parent_map(self._tree)
        return self._parents_cache
    @property
    def _bindings(self) -> dict:
        if self._bindings_cache is _RESOLVER_UNSET:
            self._bindings_cache = _collect_binding_kinds(
                self._tree, self.scope_index, self._parents)
        return self._bindings_cache
    def _is_delayed_module_use(self, node: ast.AST) -> bool:
        cur = self._parents.get(id(node))
        while cur is not None and not isinstance(cur, ast.Module):
            if isinstance(cur, _DEFINITION_NODES):
                return True
            cur = self._parents.get(id(cur))
        return False
    def _prior_bindings(self, entries, call_pos: tuple,
                        scope: str, current: str, node: ast.AST) -> list:
        if (not current and scope
                and self._is_delayed_module_use(node)):
            return list(entries or ())
        return [entry for entry in entries or ()
                if (entry[0], entry[1]) <= call_pos]
    def _binding_state(self, scope: str, name: str,
                       node: ast.AST) -> tuple[tuple | None, str]:
        call_line = getattr(node, 'lineno', None)
        call_pos = (call_line if call_line is not None else float('inf'),
                    getattr(node, 'col_offset', 0) or 0)
        first = True
        cur = scope
        while True:
            if name in self.shadow[1].get(cur, ()):
                if not cur:
                    return None, _BIND_NONE
                cur = ''
                first = False
                continue
            if first or cur not in self.shadow[2]:
                entries = self._bindings.get((cur, name))
                if entries:
                    prior = self._prior_bindings(
                        entries, call_pos, scope, cur, node)
                    if prior:
                        dominating = [
                            entry for entry in prior
                            if _block_dominates(
                                self._tree, self._parents, entry[3], node)]
                        if not dominating and not cur and hasattr(
                                builtins, name):
                            return None, _BIND_NONE
                        selected = dominating[-1] if dominating else prior[-1]
                        kind = selected[2]
                        return ((kind, _BIND_IMPORT) if kind is not None
                                else (None, _BIND_REBIND))
                if cur and cur not in self.shadow[2]:
                    if name in self.shadow[0].get(cur, ()):
                        return None, _BIND_PARAM
                    if entries:
                        return None, _BIND_REBIND
            if not cur:
                return None, _BIND_NONE
            cur = cur.rsplit('.', 1)[0] if '.' in cur else ''
            first = False
    def _possible_import_entries(self, scope: str, name: str) -> list:
        entries = list(self._bindings.get((scope, name)) or ())
        for entry in self._bindings.get((scope, '*')) or ():
            kind = _star_import_kind(entry[2], name)
            if kind is not None:
                entries.append((entry[0], entry[1], kind, entry[3]))
        return sorted(entries, key=lambda entry: (entry[0], entry[1]))
    def _possible_import_bindings(self, scope: str, name: str,
                                  node: ast.AST) -> list[tuple]:
        call_line = getattr(node, "lineno", None)
        call_pos = (call_line if call_line is not None else float("inf"),
                    getattr(node, "col_offset", 0) or 0)
        out: list[tuple] = []
        first = True
        cur = scope
        while True:
            if name in self.shadow[1].get(cur, ()):
                if not cur:
                    break
                cur = ""
                first = False
                continue
            if first or cur not in self.shadow[2]:
                entries = self._possible_import_entries(cur, name)
                prior = self._prior_bindings(
                    entries, call_pos, scope, cur, node)
                dominating = [
                    entry for entry in prior
                    if _block_dominates(
                        self._tree, self._parents, entry[3], node)]
                cutoff = max(
                    ((entry[0], entry[1]) for entry in dominating),
                    default=None)
                for entry in prior:
                    kind = entry[2]
                    if (kind is not None
                            and kind[0] in _IMPORT_BINDING_KINDS
                            and (cutoff is None
                                 or (entry[0], entry[1]) >= cutoff)):
                        out.append(kind)
                if (cur and cur not in self.shadow[2]
                        and (name in self.shadow[0].get(cur, ()) or entries)):
                    break
            if not cur:
                break
            cur = cur.rsplit(".", 1)[0] if "." in cur else ""
            first = False
        return list(dict.fromkeys(out))
    def _possible_receiver_prefixes(self, scope: str, value: ast.AST,
                                    node: ast.AST) -> list[str]:
        if isinstance(value, ast.Name):
            return [
                kind[1] if kind[0] == "import"
                else from_import_receiver((kind[1], kind[2]))
                for kind in self._possible_import_bindings(
                    scope, value.id, node)
            ]
        if isinstance(value, ast.Attribute):
            return [f"{prefix}.{value.attr}"
                    for prefix in self._possible_receiver_prefixes(
                        scope, value.value, node)]
        return []
    def is_namespace_binding(self, scope: str, name: str,
                             node: ast.Call) -> bool:
        if self.expression_bindings.get(id(node), {}).get(name) is not None:
            return False
        kind = self._binding_state(scope, name, node)[0]
        return kind is not None and kind[0] in _IMPORT_BINDING_KINDS
    def _module_root_shadowed(self, scope: str, name: str,
                              node: ast.AST) -> bool:
        if not name:
            return False
        kind, state = self._binding_state(scope, name, node)
        if state in (_BIND_PARAM, _BIND_REBIND):
            return True
        if kind is None:
            return False
        if kind[0] == 'from':
            return True
        return kind[1] != name
    def _binding_prefix(self, scope: str, name: str,
                        node: ast.AST) -> str | None:
        kind = self._binding_state(scope, name, node)[0]
        if kind is None:
            return None
        if kind[0] == 'import':
            return kind[1]
        return from_import_receiver((kind[1], kind[2]))
    def _receiver_prefix(self, scope: str, value: ast.AST,
                         node: ast.AST) -> str | None:
        root = dotted_name(value)
        if (root and self.expression_bindings.get(id(node), {}).get(
                root.split('.')[0]) is not None):
            return None
        if isinstance(value, ast.Name):
            return self._binding_prefix(scope, value.id, node)
        if isinstance(value, ast.Attribute):
            prefix = self._receiver_prefix(scope, value.value, node)
            return f"{prefix}.{value.attr}" if prefix else None
        return None
    def source_candidates(self, node: ast.AST) -> list[str]:
        if isinstance(node, ast.Call):
            return self.candidates(node)
        scope = self.scope_index.get(id(node), "")
        if isinstance(node, ast.Name):
            if self.expression_bindings.get(id(node), {}).get(node.id) is not None:
                return []
            kind, _state = self._binding_state(scope, node.id, node)
            out = ([from_import_receiver((kind[1], kind[2]))]
                   if kind is not None and kind[0] == "from" else [])
            out.extend(
                from_import_receiver((possible[1], possible[2]))
                for possible in self._possible_import_bindings(
                    scope, node.id, node) if possible[0] == "from")
            return _with_builtin_name_aliases(out)
        if not isinstance(node, ast.Attribute):
            return []
        root = dotted_name(node)
        if (root and self.expression_bindings.get(id(node), {}).get(
                root.split('.')[0]) is not None):
            return []
        out: list[str] = []
        wrote = dotted_name(node, constant_base=True)
        if wrote and not self._module_root_shadowed(
                scope, wrote.split('.', 1)[0], node):
            out.append(wrote)
        imported = self._receiver_prefix(scope, node, node)
        if imported:
            out.append(imported)
        out.extend(self._possible_receiver_prefixes(scope, node, node))
        return _with_builtin_name_aliases(out)
    def candidates(self, node: ast.Call) -> list[str]:
        if _call_root_binding(node, self.expression_bindings) is not None:
            return []
        _out: list[str] = []
        _scope = self.scope_index.get(id(node), "")
        _wrote = resolve_call_name(node)
        if _wrote and not self._module_root_shadowed(
                _scope, _wrote.split('.', 1)[0], node):
            _out.append(_wrote)
        _func = node.func
        if isinstance(_func, ast.Name):
            _kind = self._binding_state(_scope, _func.id, node)[0]
            if _kind is not None and _kind[0] == 'from':
                _out.append(self._binding_prefix(_scope, _func.id, node))
            _out.extend(
                from_import_receiver((possible[1], possible[2]))
                for possible in self._possible_import_bindings(
                    _scope, _func.id, node) if possible[0] == "from")
        elif isinstance(_func, ast.Attribute):
            _prefix = self._receiver_prefix(_scope, _func.value, node)
            if _prefix is not None:
                _out.append(f"{_prefix}.{_func.attr}")
            _out.extend(
                f"{_prefix}.{_func.attr}"
                for _prefix in self._possible_receiver_prefixes(
                    _scope, _func.value, node))
        return _with_builtin_name_aliases(_out)
    def imported_call_name(self, node: ast.Call) -> str | None:
        if _call_root_binding(node, self.expression_bindings) is not None:
            return None
        scope = self.scope_index.get(id(node), "")
        func = node.func
        if isinstance(func, ast.Name):
            return self._binding_prefix(scope, func.id, node)
        if (isinstance(func, ast.Attribute)
                and isinstance(func.value, ast.Name)):
            prefix = self._receiver_prefix(scope, func.value, node)
            return f"{prefix}.{func.attr}" if prefix else None
        return None
    def imported_from_origin(self, node: ast.Call) -> tuple[str, str] | None:
        if _call_root_binding(node, self.expression_bindings) is not None:
            return None
        if not isinstance(node.func, ast.Name):
            return None
        scope = self.scope_index.get(id(node), "")
        kind = self._binding_state(scope, node.func.id, node)[0]
        if kind is None or kind[0] != 'from':
            return None
        return kind[1], kind[2]
    def constructor_candidates(self, node: ast.Call,
                               sink_names) -> list[str]:
        _func = node.func
        if not (isinstance(_func, ast.Attribute)
                and isinstance(_func.value, ast.Name)):
            return []
        if _func.attr not in _CONSTRUCTOR_SINK_TAILS:
            return []
        _binding = lookup_name_assignment(
            self._tree, _func.value.id, node.lineno,
            self.scope_index.get(id(node), ""), self.scope_index,
            use_col=node.col_offset)
        if not isinstance(_binding, ast.Call):
            return []
        _tails = {_n.rsplit('.', 1)[-1] for _n in self.candidates(_binding)}
        return [f"{_tail}.{_func.attr}" for _tail in sorted(_tails)
                if f"{_tail}.{_func.attr}" in sink_names]
    def _imported_sink_name(self, node: ast.Call,
                            sink_names) -> str | None:
        _func = node.func
        if not isinstance(_func, ast.Name):
            return None
        _scope = self.scope_index.get(id(node), "")
        _kind = self._binding_state(_scope, _func.id, node)[0]
        _kinds = ([_kind] if _kind is not None and _kind[0] == "from" else [])
        _kinds.extend(
            possible for possible in self._possible_import_bindings(
                _scope, _func.id, node) if possible[0] == "from")
        for _kind in dict.fromkeys(_kinds):
            _imported = _kind[2]
            if (not _imported
                    or (hasattr(builtins, _imported)
                        and _kind[1] != "builtins")):
                continue
            if _imported in sink_names:
                return _imported
        return None
    def sink_name(self, node: ast.Call, sink_names) -> str | None:
        if _call_root_binding(node, self.expression_bindings) is not None:
            return None
        for _name in self.candidates(node):
            if _name in sink_names:
                return _name
        _imported = self._imported_sink_name(node, sink_names)
        if _imported is not None:
            return _imported
        _ctor = self.constructor_candidates(node, sink_names)
        return _ctor[0] if _ctor else None
def _sanitizer_prune(names: _SinkNameResolver | None,
                     sanitizer_names: set):
    def _prune(call: ast.Call) -> bool:
        candidates = (names.candidates(call) if names is not None
                      else [resolve_call_name(call)])
        return any(name in sanitizer_names for name in candidates)
    return _prune
def _taint_state(tree: ast.AST, report: TaintReport,
                 source_names: set, sanitizer_names: set,
                 names: _SinkNameResolver):
    taint_origins: dict[tuple[str, str], str] = {}
    sanitized_keys = collect_sanitized_keys(
        tree, sanitizer_names, names.scope_index, names.shadow,
        call_name_candidates=names.candidates)
    tainted_vars, taint_hops = collect_source_taints(
        tree, source_names, report, taint_origins,
        scope_idx=names.scope_index, shadow=names.shadow,
        call_name_candidates=names.source_candidates)
    propagate_taints(
        tree, tainted_vars, taint_hops, source_names, taint_origins,
        scope_idx=names.scope_index, shadow=names.shadow,
        sanitized_keys=sanitized_keys, sanitizer_names=sanitizer_names,
        call_name_candidates=names.source_candidates)
    return tainted_vars, taint_hops, taint_origins, sanitized_keys
class TaintTracker:
    def __init__(self) -> None:
        self.sources = list(BUILTIN_SOURCES)
        self.sinks = list(BUILTIN_SINKS)
        self.sanitizers = list(BUILTIN_SANITIZERS)
        self._sync_registry_maps()
    def _sync_registry_maps(self) -> None:
        self._source_by_name = {s.name: s for s in self.sources}
        self._sink_by_name = {s.name: s for s in self.sinks}
    def register_source(self, source: TaintSource) -> None:
        self.sources.append(source)
        self._source_by_name[source.name] = source
    def register_sink(self, sink: TaintSink) -> None:
        self.sinks.append(sink)
        self._sink_by_name[sink.name] = sink
    def register_sanitizer(self, sanitizer: TaintSanitizer) -> None:
        self.sanitizers.append(sanitizer)
    def analyze(self, code: Any, tree: ast.AST | None = None) -> TaintReport:
        if tree is None:
            if not isinstance(code, (str, bytes, bytearray)):
                logger.warning("[Taint] 源码载荷类型无效，降级空报告: %r",
                               type(code).__name__)
                return TaintReport(file_path="<string>")
            try:
                tree = ast.parse(code)
            except PARSE_DEGRADE_EXC:
                logger.warning(MSG_SYNTAX_ERROR_SKIP)
                return TaintReport(file_path="<string>")
        return self._analyze_tree(tree, "<string>")
    def analyze_file(self, filepath: str) -> TaintReport:
        filepath = os.fspath(filepath)
        tree = parse_guard_cached(filepath)
        if tree is None:
            logger.warning("[Taint] 源文件读取或解析失败，降级空报告: %s", filepath)
            return TaintReport(file_path=filepath)
        return self._analyze_tree(tree, filepath)
    def _analyze_tree(self, tree: ast.AST, filepath: str) -> TaintReport:
        self._sync_registry_maps()
        report = TaintReport(file_path=filepath)
        source_names = _registry_names(self.sources)
        sink_names = _registry_names(self.sinks)
        sanitizer_names = _registry_names(self.sanitizers)
        _names = _sink_name_resolver(tree)
        scope_idx = _names.scope_index
        _shadow = _names.shadow
        tainted_vars, taint_hops, taint_origins, sanitized_keys = _taint_state(
            tree, report, source_names,
            _universal_sanitizer_names(self.sanitizers), _names)
        report.tainted_variables = list(dict.fromkeys(
            var for _scope, var in tainted_vars))
        parents = build_parent_map(tree)
        self._detect_sinks(report, _SinkScanCtx(
            tree=tree, tainted_vars=tainted_vars, taint_hops=taint_hops,
            sink_names=sink_names, source_names=source_names,
            taint_origins=taint_origins,
            scope_idx=scope_idx, sanitized_keys=sanitized_keys,
            shadow=_shadow, sanitizer_names=sanitizer_names, names=_names,
            parents=parents, flow_events=_flow_events(tree, parents)))
        return report
    @staticmethod
    def _inline_source_hit(arg: ast.AST, ctx: _SinkScanCtx):
        if not ctx.source_names:
            return None, None
        prune = _sanitizer_prune(ctx.names, ctx.sanitizer_names)
        source = taint_source_of(
            arg, ctx.source_names,
            call_name_candidates=ctx.names.source_candidates)
        if source is not None:
            return source, arg
        for sub in _iter_value_channel_nodes(arg, prune=prune):
            source = taint_source_of(
                sub, ctx.source_names,
                call_name_candidates=ctx.names.source_candidates)
            if source is not None:
                return source, sub
        return None, None
    @staticmethod
    def _inline_source_name(arg: ast.AST, ctx: _SinkScanCtx) -> str | None:
        return TaintTracker._inline_source_hit(arg, ctx)[0]
    def _has_tainted_arg(self, ctx: _SinkScanCtx,
                         scope: str,
                         comp_env: dict | None,
                         payload_args: list[ast.expr]) -> bool:
        def _hit(name_node: ast.Name) -> bool:
            owner = ctx.names.expression_bindings.get(
                id(name_node), {}).get(name_node.id)
            if isinstance(owner, ast.Lambda):
                return False
            if isinstance(owner, COMP_SCOPE_NODES):
                return bool(comp_env and comp_env.get(name_node.id) is not None)
            if comp_env and name_node.id in comp_env:
                return comp_env[name_node.id] is not None
            return TaintNameResolution.resolve_taint_key(
                scope, name_node.id, ctx.tainted_vars, ctx.shadow) is not None
        for arg in payload_args:
            if any(_hit(_n) for _n in iter_free_load_names(arg)):
                return True
            if self._inline_source_name(arg, ctx) is not None:
                return True
        return False
    def _detect_sinks(self, report, ctx: _SinkScanCtx) -> TaintReport:
        for node in walk_nodes(ctx.tree):
            if not isinstance(node, ast.Call):
                continue
            func_name = ctx.names.sink_name(node, ctx.sink_names)
            if func_name is None:
                continue
            self._record_sink(node, func_name, report, ctx)
        return report
    def _inline_sources(self,
                        ctx: _SinkScanCtx,
                        payload_args: list[ast.expr]) -> list[str]:
        names: list[str] = []
        for arg in payload_args:
            name, source_node = self._inline_source_hit(arg, ctx)
            if name is None or source_node is None:
                continue
            node_key = id(source_node)
            if node_key in ctx.counted_inline_source_nodes:
                continue
            ctx.counted_inline_source_nodes.add(node_key)
            names.append(name)
        return names
    def _sink_taint_context(self, ctx: _SinkScanCtx,
                            sink: TaintSink | None) -> _SinkScanCtx:
        allowed = _sanitizer_names_for_sink(self.sanitizers, sink)
        cache_key = frozenset(allowed)
        state = ctx.sink_states.get(cache_key)
        if state is None:
            state = _taint_state(
                ctx.tree, TaintReport(file_path=""), ctx.source_names,
                allowed, ctx.names)
            ctx.sink_states[cache_key] = state
        tainted_vars, taint_hops, taint_origins, sanitized_keys = state
        return replace(
            ctx, tainted_vars=tainted_vars, taint_hops=taint_hops,
            taint_origins=taint_origins, sanitized_keys=sanitized_keys,
            sanitizer_names=allowed)
    def _record_sink(self, node: ast.Call, func_name: str, report,
                     ctx: _SinkScanCtx) -> None:
        report.total_sinks += 1
        snk = self._sink_by_name.get(func_name)
        ctx = self._sink_taint_context(ctx, snk)
        _scope = ctx.scope_idx.get(id(node), "")
        comp_env = _comprehension_env(node, _scope, ctx)
        payload_args = _sink_payload_args(node, snk)
        has_tainted_arg = self._has_tainted_arg(
            ctx, _scope, comp_env, payload_args)
        report.total_sources += len(self._inline_sources(ctx, payload_args))
        sanitized = self._sanitized_at_sink(
            node, _scope, has_tainted_arg, ctx, comp_env, payload_args)
        exploitability = (self._sink_exploitability(
            _scope, ctx, comp_env, payload_args)
            if has_tainted_arg else "unknown")
        _origin_src = self._trace_sink_arg_origins(
            _scope, ctx, comp_env, payload_args)
        report.flows.append(TaintFlow(
            source=_origin_src,
            sink=snk,
            description=f"{func_name}() at line {node.lineno}",
            risk_level=snk.severity if snk else "P0",
            is_exploitable=has_tainted_arg and not sanitized,
            exploitability=exploitability if not sanitized else "mitigated",
            line=node.lineno,
        ))
        if sanitized:
            report.sanitizers_used += 1
    def _sanitized_at_sink(self, node: ast.Call, scope: str,
                           has_tainted_arg: bool, ctx: _SinkScanCtx,
                           comp_env: dict | None,
                           payload_args: list[ast.expr]) -> bool:
        if not has_tainted_arg:
            return False
        tainted_vars = ctx.tainted_vars
        sanitized_keys = ctx.sanitized_keys
        if comp_env:
            tainted_vars = dict(tainted_vars)
            sanitized_keys = dict(sanitized_keys)
            for _name, _hit in comp_env.items():
                _key = TaintNameResolution.owner_key(
                    scope, _name, ctx.shadow)
                tainted_vars.pop(_key, None)
                sanitized_keys.pop(_key, None)
                if _hit is not None:
                    tainted_vars[_key] = 1
        sanitized_keys = _sanitized_keys_at_use(
            sanitized_keys, ctx.flow_events,
            _statement_for_node(node, ctx.parents))
        return is_sanitized(
            node, ctx.tree, scope, sanitized_keys, ctx.shadow,
            tainted_vars=tainted_vars,
            sanitizer_names=ctx.sanitizer_names,
            call_name_candidates=ctx.names.candidates,
            argument_nodes=payload_args, source_names=ctx.source_names,
            source_name_candidates=ctx.names.source_candidates)
    def _sink_exploitability(self, scope: str,
                             ctx: _SinkScanCtx,
                             comp_env: dict | None,
                             payload_args: list[ast.expr]) -> str:
        min_hop = min(
            self._arg_hops(scope, ctx, comp_env, payload_args), default=1)
        return next((label for limit, label in _HOP_TIERS
                     if min_hop <= limit), "theoretical")
    def _arg_hops(self, scope: str,
                  ctx: _SinkScanCtx,
                  comp_env: dict | None,
                  payload_args: list[ast.expr]) -> list:
        hops: list = []
        for _arg in payload_args:
            for _child in iter_free_load_names(_arg):
                owner = ctx.names.expression_bindings.get(
                    id(_child), {}).get(_child.id)
                if isinstance(owner, ast.Lambda):
                    continue
                if isinstance(owner, COMP_SCOPE_NODES):
                    _hit = comp_env.get(_child.id) if comp_env else None
                    if _hit is not None:
                        hops.append(_hit[1])
                    continue
                _hit = comp_env.get(_child.id) if comp_env else None
                if _hit is not None:
                    hops.append(_hit[1])
                if comp_env and _child.id in comp_env:
                    continue
                _key = TaintNameResolution.resolve_taint_key(
                    scope, _child.id, ctx.tainted_vars, ctx.shadow)
                if _key is not None:
                    hops.append(ctx.taint_hops.get(_key, 1))
            if self._inline_source_name(_arg, ctx) is not None:
                hops.append(1)
        return hops
    def _trace_sink_arg_origins(self, _scope: str,
                                ctx: _SinkScanCtx,
                                comp_env: dict | None,
                                payload_args: list[ast.expr]):
        _cands: dict = {}
        for _arg in payload_args:
            _inline = self._inline_source_name(_arg, ctx)
            if _inline is not None:
                _src = self._source_by_name.get(_inline)
                if _src is not None:
                    _cands.setdefault(_src.name, _src)
            if comp_env:
                for _n in iter_free_load_names(_arg):
                    owner = ctx.names.expression_bindings.get(
                        id(_n), {}).get(_n.id)
                    if not isinstance(owner, COMP_SCOPE_NODES):
                        continue
                    _hit = comp_env.get(_n.id)
                    _src = (self._source_by_name.get(_hit[0])
                            if _hit and _hit[0] else None)
                    if _src is not None:
                        _cands.setdefault(_src.name, _src)
            if ctx.taint_origins:
                for _src in self._expr_origin_sources(
                        _arg, _scope, ctx.taint_origins, ctx.shadow,
                        excluded_names=comp_env or {},
                        expression_bindings=ctx.names.expression_bindings):
                    _cands.setdefault(_src.name, _src)
        if not _cands:
            return None
        _ordered = list(_cands.values())
        return next((s for s in _ordered
                     if s.category not in TAINT_LOCAL_TRUSTED_CATEGORIES),
                    _ordered[0])
    def _expr_origin_sources(self, expr: ast.expr, scope: str,
                             taint_origins: dict,
                             shadow: tuple[dict, dict, frozenset],
                             excluded_names=(),
                             expression_bindings=None) -> list:
        _sources: dict = {}
        bindings = expression_bindings or {}
        for _n in iter_free_load_names(expr):
            owner = bindings.get(id(_n), {}).get(_n.id)
            if owner is not None or _n.id in excluded_names:
                continue
            _src = self._origin_source(_n.id, scope, taint_origins, shadow)
            if _src is not None:
                _sources.setdefault(_src.name, _src)
        return list(_sources.values())
    def _origin_source(self, name: str, scope: str, taint_origins: dict,
                       shadow: tuple[dict, dict, frozenset]):
        _key = TaintNameResolution.resolve_taint_key(scope, name, taint_origins, shadow)
        _origin_name = taint_origins.get(_key) if _key is not None else None
        return self._source_by_name.get(_origin_name) if _origin_name else None
def analyze_taint(code_or_path: Any, is_file: bool = False,
                  tree: ast.AST | None = None) -> Any:
    tracker = TaintTracker()
    if is_file:
        return tracker.analyze_file(code_or_path)
    return tracker.analyze(code_or_path, tree=tree)
_SINK_RESOLVER_MEMO: dict[int, tuple[ast.Module, Any]] = {}
_SINK_RESOLVER_MEMO_LOCK = threading.Lock()
#: 汇点名字解析器缓存容量。每条目约 2 MB（5 份整树派生字典），
#: 128 条 ≈ 256 MB；实测单文件热工作集仅 7–13 个 sibling 模块，
#: 128 条可覆盖约 20 个文件的 sibling 集合，逐出频率极低。
_SINK_RESOLVER_MEMO_CAP = 128
def _iter_binding_pairs(node: ast.AST):
    form = assignment_form(node)
    if form is not None:
        targets, value = form
        strong = not isinstance(node, ast.AugAssign)
        for _target in targets:
            for _tgt, _rhs in _iter_aligned_target_rhs(_target, value):
                yield _tgt, _rhs, strong and isinstance(_tgt, ast.Name)
        return
    if isinstance(node, (ast.With, ast.AsyncWith)):
        for item in node.items:
            if item.optional_vars is None:
                continue
            for _tgt, _rhs in _iter_aligned_target_rhs(
                    item.optional_vars, item.context_expr):
                yield _tgt, _rhs, isinstance(_tgt, ast.Name)
        return
    container = _container_mutation_target(node)
    if container is not None:
        call = node.value
        for value in (*call.args,
                      *(kw.value for kw in call.keywords
                        if kw.value is not None)):
            yield container, value, False
def _iter_binding_events(node: ast.AST):
    for _tgt, _rhs, _strong in _iter_binding_pairs(node):
        for _name in _iter_target_root_names(_tgt):
            yield _name, _rhs, _strong
def _iter_aligned_target_rhs(target: ast.AST, value: ast.AST):
    if isinstance(target, ast.Starred):
        yield from _iter_aligned_target_rhs(target.value, value)
        return
    if isinstance(target, (ast.Tuple, ast.List)):
        if isinstance(value, (ast.Tuple, ast.List)):
            starred = [index for index, element in enumerate(target.elts)
                       if isinstance(element, ast.Starred)]
            if not starred and len(target.elts) == len(value.elts):
                for _t, _v in zip(target.elts, value.elts, strict=True):
                    yield from _iter_aligned_target_rhs(_t, _v)
                return
            if len(starred) == 1 and len(value.elts) >= len(target.elts) - 1:
                index = starred[0]
                trailing = len(target.elts) - index - 1
                middle_end = len(value.elts) - trailing
                middle = ast.copy_location(ast.Tuple(
                    elts=list(value.elts[index:middle_end]), ctx=ast.Load()),
                    value)
                aligned = [*value.elts[:index], middle,
                           *value.elts[middle_end:]]
                for _t, _v in zip(target.elts, aligned, strict=True):
                    yield from _iter_aligned_target_rhs(_t, _v)
                return
        for _t in target.elts:
            yield from _iter_aligned_target_rhs(_t, value)
        return
    yield target, value
_DEFINITION_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_CONTAINER_MUTATION_METHODS = (
    "append", "extend", "insert", "add", "update",
    "__setitem__", "setdefault",
)
_TRANSPARENT_FUNC_NAMES = frozenset({
    "str", "int", "float", "bool", "list", "dict", "tuple", "set",
    "repr", "format", "strip", "lower", "upper", "replace", "join",
    "split",
})
_DEFAULT_MAX_SINKS = 20
def _names_from_call(node: ast.Call) -> set:
    names = set()
    if isinstance(node.func, ast.Name):
        names.add(node.func.id)
    elif (isinstance(node.func, ast.Attribute)
            and node.func.attr in _TRANSPARENT_FUNC_NAMES):
        names.update(_extract_names(node.func.value))
    for arg in chain(node.args, (kw.value for kw in node.keywords)):
        names.update(_extract_names(arg))
    return names
def _composite_child_nodes(node) -> tuple:
    if isinstance(node, ast.BinOp):
        return node.left, node.right
    if isinstance(node, ast.UnaryOp):
        return (node.operand,)
    if isinstance(node, ast.FormattedValue):
        return (node.value,)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return tuple(node.elts)
    if isinstance(node, ast.Dict):
        return tuple(filter(None, chain.from_iterable(
            zip(node.keys or [], node.values, strict=True))))
    if isinstance(node, ast.IfExp):
        return node.test, node.body, node.orelse
    if isinstance(node, (ast.BoolOp, ast.JoinedStr)):
        return tuple(node.values)
    if isinstance(node, COMP_SCOPE_NODES):
        return tuple(iter_free_load_names(node))
    if isinstance(node, ast.Lambda):
        return tuple(iter_free_load_names(node))
    if isinstance(node, (ast.Await, ast.Yield, ast.YieldFrom)):
        return (node.value,)
    return ()
def _extract_names(node) -> set:
    if isinstance(node, ast.Name):
        return {node.id}
    if isinstance(node, ast.Call):
        return _names_from_call(node)
    if isinstance(node, (ast.Subscript, ast.Attribute)):
        return _extract_names(node.value)
    if isinstance(node, ast.Starred):
        return _extract_names(node.value)
    if isinstance(node, ast.FormattedValue):
        return _extract_names(node.value)
    if isinstance(node, ast.NamedExpr):
        return _extract_names(node.value)
    return {name for child in _composite_child_nodes(node)
            for name in _extract_names(child)}
def _positional_param_names(func_node) -> list:
    return [a.arg for a in func_node.args.posonlyargs + func_node.args.args]
def _returned_param_names(func_node, param_set) -> set:
    names = set()
    for child in iter_own_scope(func_node, skip_lambda=True):
        if isinstance(child, ast.Return) and child.value:
            names |= _extract_names(child.value) & param_set
    return names
def _function_transfer_signature(func_node) -> tuple[set, list, list]:
    spec = func_node.args
    pos_params = _positional_param_names(func_node)
    all_params = pos_params + [arg.arg for arg in spec.kwonlyargs]
    all_params += [name for name in _star_param_names(func_node) if name]
    returned = _returned_param_names(func_node, set(all_params))
    return returned, pos_params, all_params
def _star_param_names(func_node) -> tuple[str, str]:
    spec = func_node.args
    return tuple(arg.arg if isinstance(arg, ast.arg) else ""
                 for arg in (spec.vararg, spec.kwarg))
@dataclass(frozen=True)
class _TransferSignature:
    returned: set
    pos_params: list
    all_params: list
    kw_params: list
    star_names: tuple
    is_method: bool
    binds_receiver: bool
def _method_binding_modes(tree) -> dict[int, bool]:
    modes: dict[int, bool] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        for child in node.body:
            if not isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            is_static = any(
                (isinstance(dec, ast.Name) and dec.id == "staticmethod")
                or (isinstance(dec, ast.Attribute) and dec.attr == "staticmethod")
                for dec in child.decorator_list)
            modes[id(child)] = not is_static
    return modes
def _call_short_name(node: ast.Call) -> str:
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    return ""
def _collect_func_transfers(tree) -> dict[str, list[_TransferSignature]]:
    transfers: dict[str, list[_TransferSignature]] = {}
    method_modes = _method_binding_modes(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        returned, pos_params, all_params = _function_transfer_signature(node)
        transfers.setdefault(node.name, []).append(
            _TransferSignature(
                returned=returned,
                pos_params=pos_params,
                all_params=all_params,
                kw_params=[arg.arg for arg in (
                    *node.args.args, *node.args.kwonlyargs)],
                star_names=_star_param_names(node),
                is_method=id(node) in method_modes,
                binds_receiver=method_modes.get(id(node), False),
            ))
    # Keep empty-return signatures: they are the only evidence that a same-name
    # method is clean even when a module-level function propagates its argument.
    return transfers
def _transfer_signature_for_call(node, func_transfers):
    if not isinstance(node, ast.Call):
        return None
    signatures = func_transfers.get(_call_short_name(node))
    if not signatures:
        return None
    return _select_transfer_signature(
        signatures, attribute_call=isinstance(node.func, ast.Attribute))
def _select_transfer_signature(signatures, *, attribute_call: bool):
    matching = [s for s in signatures if s.is_method is attribute_call]
    candidates = matching or signatures
    return next((s for s in candidates if s.returned), candidates[-1])
def _transfer_param_args(param, call_args, kw_args, pos_params,
                         star_names: tuple[str, str], bound_method: bool,
                         kw_spread, kw_params) -> list:
    vararg, kwarg = star_names
    if vararg and param == vararg:
        consumed = len(pos_params) - int(bound_method and bool(pos_params))
        return list(call_args[consumed:])
    if kwarg and param == kwarg:
        consumed_names = set(kw_params)
        return [value for name, value in kw_args.items()
                if name not in consumed_names] + list(kw_spread)
    arg_node = _resolve_arg_for_param(param, call_args, kw_args, pos_params,
                                      bound_method=bound_method)
    if arg_node is None:
        return list(kw_spread) if param in kw_params else []
    return [arg_node]
def _resolve_arg_for_param(param, call_args, kw_args, pos_params,
                           bound_method: bool):
    arg_node = kw_args.get(param)
    if arg_node is not None or param not in pos_params:
        return arg_node
    p_idx = pos_params.index(param)
    if bound_method and p_idx > 0:
        p_idx -= 1
    return call_args[p_idx] if p_idx < len(call_args) else None
def _transfer_value_nodes(node: ast.Call, transfer) -> list:
    kw_args = {kw.arg: kw.value for kw in node.keywords if kw.arg}
    kw_spread = [kw.value for kw in node.keywords if kw.arg is None]
    bound_method = (isinstance(node.func, ast.Attribute)
                    and transfer.binds_receiver)
    nodes: list = []
    for param in transfer.returned:
        if param not in transfer.all_params:
            continue
        if (bound_method and transfer.pos_params
                and param == transfer.pos_params[0]):
            nodes.append(node.func.value)
            continue
        nodes.extend(_transfer_param_args(
            param, node.args, kw_args, transfer.pos_params,
            transfer.star_names, bound_method=bound_method,
            kw_spread=kw_spread, kw_params=transfer.kw_params))
    return nodes
def _bfs_visit(start: str, expand) -> Iterator[str]:
    queue = deque([start])
    visited = {start}
    while queue:
        node = queue.popleft()
        yield node
        for nxt in expand(node):
            if nxt not in visited:
                visited.add(nxt)
                queue.append(nxt)
def _container_mutation_target(node: ast.AST) -> ast.Name | None:
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return None
    call = node.value
    if not isinstance(call.func, ast.Attribute):
        return None
    if call.func.attr not in _CONTAINER_MUTATION_METHODS:
        return None
    if not isinstance(call.func.value, ast.Name):
        return None
    return call.func.value
def _iter_target_root_names(target) -> Iterator[str]:
    if isinstance(target, (ast.Tuple, ast.List)):
        for element in target.elts:
            yield from _iter_target_root_names(element)
        return
    if isinstance(target, ast.Name):
        yield target.id
        return
    if isinstance(target, ast.Subscript):
        yield from _iter_target_root_names(target.value)
        return
    if isinstance(target, ast.Attribute):
        yield from _iter_target_root_names(target.value)
def _event_position(event: _FlowEvent) -> tuple[int, int]:
    return event.node.lineno, event.node.col_offset
def _event_activation(event: _FlowEvent) -> tuple[int, int]:
    if _container_mutation_target(event.node) is not None:
        return expr_end(event.node.value)
    return expr_end(event.value)
@dataclass(frozen=True)
class _FlowEvent:
    target: str
    value: ast.AST
    node: ast.AST
    strong: bool
    scope: int
    block: tuple
def _loop_target_guaranteed_at_use(
        loop: ast.For | ast.AsyncFor, statement: ast.AST) -> bool:
    if any(statement is body_stmt
           or any(node is statement for node in walk_nodes(body_stmt))
           for body_stmt in loop.body):
        return True
    iterable = loop.iter
    if isinstance(iterable, (ast.List, ast.Tuple, ast.Set)):
        return any(not isinstance(item, ast.Starred)
                   for item in iterable.elts)
    if isinstance(iterable, ast.Dict):
        return any(key is not None for key in iterable.keys)
    return (isinstance(iterable, ast.Constant)
            and isinstance(iterable.value, (str, bytes))
            and bool(iterable.value))
def _sanitized_keys_at_use(sanitized_keys: dict, events: list[_FlowEvent],
                           statement: ast.AST | None) -> dict:
    if statement is None:
        return sanitized_keys
    conditional_positions = {
        position
        for event in events
        if isinstance(event.node, (ast.For, ast.AsyncFor))
        and not _loop_target_guaranteed_at_use(event.node, statement)
        for position in (_event_position(event), expr_end(event.value))
    }
    if not conditional_positions:
        return sanitized_keys
    return {
        key: [entry for entry in timeline
              if (entry[0], entry[1]) not in conditional_positions]
        for key, timeline in sanitized_keys.items()
    }
def _flow_scope(node, parents):
    cur = parents.get(id(node))
    while cur is not None and not isinstance(
            cur, (ast.Module, *_DEFINITION_NODES, ast.ClassDef)):
        cur = parents.get(id(cur))
    return cur
def _flow_block(node, parents) -> tuple:
    parent = parents.get(id(node))
    for field_name in ("body", "orelse", "finalbody"):
        block = getattr(parent, field_name, None)
        if isinstance(block, list) and node in block:
            return id(parent), field_name
    return id(parent), ""
def _block_dominates(tree: ast.AST, parents: dict,
                     definition_block: tuple,
                     use_statement: ast.AST | None) -> bool:
    if use_statement is None:
        return False
    if definition_block[1] == "loop_body":
        loop = next(
            (node for node in chain((tree,), parents.values())
             if id(node) == definition_block[0]), None)
        return (loop is not None
                and _loop_target_guaranteed_at_use(loop, use_statement))
    final_container = None
    definition_end = None
    if definition_block[1] == "finalbody":
        definition_node = next(
            (node for node in chain((tree,), parents.values())
             if id(node) == definition_block[0]), None)
        if getattr(definition_node, "finalbody", None):
            final_container = _flow_block(definition_node, parents)
            definition_end = expr_end(definition_node)
    cur: ast.AST | None = use_statement
    while cur is not None:
        cur_block = _flow_block(cur, parents)
        if cur_block == definition_block:
            return True
        if (final_container is not None and cur_block == final_container
                and definition_end <= (
                    getattr(cur, "lineno", 0) or 0,
                    getattr(cur, "col_offset", 0) or 0)):
            return True
        cur = parents.get(id(cur))
    return False
def _flow_event_block(node: ast.AST, parents: dict) -> tuple:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return id(node), "loop_body"
    if not isinstance(node, ast.NamedExpr):
        return _flow_block(node, parents)
    cur = node
    while True:
        parent = parents.get(id(cur))
        if parent is None:
            return _flow_block(node, parents)
        if isinstance(parent, ast.stmt):
            if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef,
                                   ast.ClassDef)):
                return _flow_block(node, parents)
            return _flow_block(parent, parents)
        if ((isinstance(parent, ast.BoolOp) and cur is not parent.values[0])
                or (isinstance(parent, ast.IfExp) and cur is not parent.test)
                or isinstance(parent, (*COMP_SCOPE_NODES, ast.Lambda,
                                       getattr(ast, "match_case", ())))):
            return _flow_block(node, parents)
        cur = parent
def _flow_events(tree, parents) -> list[_FlowEvent]:
    events: list[_FlowEvent] = []
    for node in walk_nodes(tree):
        pairs = list(_iter_binding_events(node))
        if not pairs:
            continue
        scope = _flow_scope(node, parents)
        block = _flow_event_block(node, parents)
        for name, value, strong in pairs:
            events.append(_FlowEvent(
                name, value, node, strong, id(scope), block))
    return events
def _statement_for_node(node: ast.AST, parents: dict) -> ast.stmt | None:
    cur = node
    while cur is not None and not isinstance(cur, ast.stmt):
        cur = parents.get(id(cur))
    return cur
class _FlowContext:
    def __init__(self, tree, line: int, parents: dict) -> None:
        self.tree = tree
        self.line = line
        self.parents = parents
        self.scopes = self._sink_scopes()
        self.globals: dict[int, set[str]] = {}
        self.nonlocals: dict[int, set[str]] = {}
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.Global, ast.Nonlocal)):
                continue
            scope = _flow_scope(node, parents)
            channel = self.globals if isinstance(node, ast.Global) else self.nonlocals
            channel.setdefault(id(scope), set()).update(node.names)
    def _sink_scopes(self) -> set[int] | None:
        max_line = max((getattr(node, "end_lineno", 0) or 0
                        for node in walk_nodes(self.tree)), default=0)
        if not 1 <= self.line <= max_line:
            return None
        candidates = [node for node in walk_nodes(self.tree)
                      if isinstance(node, (*_DEFINITION_NODES, ast.ClassDef))
                      and node.lineno <= self.line <= (
                          getattr(node, "end_lineno", None) or node.lineno)]
        scope = (min(candidates,
                     key=lambda node: ((getattr(node, "end_lineno", None)
                                       or node.lineno) - node.lineno))
                 if candidates else self.tree)
        scopes: set[int] = set()
        cur = scope
        function_seen = False
        while cur is not None:
            if isinstance(cur, _DEFINITION_NODES):
                function_seen = True
                scopes.add(id(cur))
            elif not isinstance(cur, ast.ClassDef) or not function_seen:
                scopes.add(id(cur))
            cur = self.parents.get(id(cur))
        return scopes
    def _shares_nonlocal_scope(self, event_scope: int) -> bool:
        cur = self.parents.get(event_scope)
        while cur is not None:
            if (isinstance(cur, _DEFINITION_NODES)
                    and id(cur) in self.scopes):
                return True
            cur = self.parents.get(id(cur))
        return False
    def _visible(self, event: _FlowEvent) -> bool:
        if self.scopes is None or event.scope in self.scopes:
            return True
        if event.target in self.globals.get(event.scope, set()):
            return id(self.tree) in self.scopes
        if event.target in self.nonlocals.get(event.scope, set()):
            return self._shares_nonlocal_scope(event.scope)
        return False
    def parameter_scope(self, target: str,
                        use_statement: ast.AST | None) -> ast.AST | None:
        cur = use_statement
        while cur is not None:
            if isinstance(cur, _DEFINITION_NODES):
                if target in self.globals.get(id(cur), set()):
                    return None
                if target in collect_param_names(cur):
                    return cur
            cur = self.parents.get(id(cur))
        if self.scopes is not None:
            definitions = [
                node for node in walk_nodes(self.tree)
                if id(node) in self.scopes
                and isinstance(node, _DEFINITION_NODES)]
            if any(target in self.globals.get(id(node), set())
                   for node in definitions):
                return None
            candidates = [
                node for node in definitions
                if target in collect_param_names(node)]
            if candidates:
                return min(
                    candidates,
                    key=lambda node: ((getattr(node, "end_lineno", None)
                                       or node.lineno) - node.lineno))
        return None
    def history(self, events: list[_FlowEvent],
                position: tuple[int, int] | None = None) -> list[_FlowEvent]:
        limit = ((self.line, float("inf")) if position is None else position)
        return sorted(
            (event for event in events
             if self._visible(event) and _event_activation(event) < limit),
            key=_event_position)
    def active(self, events: list[_FlowEvent], target: str | None = None,
               position: tuple[int, int] | None = None,
               use_statement: ast.AST | None = None,
               respect_parameters: bool = True) -> list[_FlowEvent]:
        if respect_parameters and target is not None:
            parameter_scope = self.parameter_scope(target, use_statement)
            if parameter_scope is not None:
                events = [
                    event for event in events
                    if event.scope == id(parameter_scope)
                    or event.target in self.nonlocals.get(event.scope, set())]
        groups: dict[tuple, list[_FlowEvent]] = {}
        for event in self.history(events, position):
            if target is not None and event.target != target:
                continue
            groups.setdefault((event.target, event.block), []).append(event)
        selected: list[_FlowEvent] = []
        for group in groups.values():
            strong = [event for event in group if event.strong]
            if not strong:
                selected.extend(group)
                continue
            latest = max(strong, key=_event_position)
            selected.append(latest)
            selected.extend(event for event in group
                            if not event.strong
                            and _event_position(event) > _event_position(latest))
        selected = sorted(selected, key=_event_position)
        if use_statement is not None:
            dominating = [
                event for event in selected
                if event.strong and _block_dominates(
                    self.tree, self.parents, event.block, use_statement)]
            if dominating:
                cutoff = max(_event_position(event) for event in dominating)
                selected = [event for event in selected
                            if _event_position(event) >= cutoff]
        return selected
def _flow_sanitizer_names(tree: ast.AST, sink_line: int,
                          names: _SinkNameResolver) -> set[str]:
    by_sink = [
        _builtin_sanitizer_names_for_sink(sink_name)
        for _call, sink_name in _iter_line_sink_calls(tree, sink_line, names)
    ]
    if not by_sink:
        return _universal_sanitizer_names(BUILTIN_SANITIZERS)
    common = set(by_sink[0])
    common.intersection_update(*by_sink[1:])
    return common
def _flow_source_name(value: ast.AST, source_names: frozenset,
                      names: _SinkNameResolver,
                      sanitizer_names: set[str]) -> str | None:
    return first_taint_source(
        value, source_names,
        prune=_sanitizer_prune(names, sanitizer_names),
        call_name_candidates=names.source_candidates)
def _source_name_with_transfers(value: ast.AST, source_names: frozenset,
                                names: _SinkNameResolver,
                                sanitizer_names: set[str],
                                func_transfers: dict) -> str | None:
    transfer = _transfer_signature_for_call(value, func_transfers)
    if transfer is None:
        return _flow_source_name(
            value, source_names, names, sanitizer_names)
    for selected in _transfer_value_nodes(value, transfer):
        source = _flow_source_name(
            selected, source_names, names, sanitizer_names)
        if source is not None:
            return source
    return None
def _comprehension_visible_generators(node: ast.AST, parents: dict) -> list:
    chains: list[list[ast.comprehension]] = []
    cur: ast.AST | None = node
    child: ast.AST | None = None
    while cur is not None and not isinstance(
            cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        if isinstance(cur, COMP_SCOPE_NODES):
            generators = list(cur.generators)
            if isinstance(child, ast.comprehension):
                index = next(
                    i for i, gen in enumerate(generators) if gen is child)
                segment: ast.AST | None = node
                in_iter = False
                while segment is not None and segment is not child:
                    if segment is child.iter:
                        in_iter = True
                        break
                    segment = parents.get(id(segment))
                visible = generators[:index] if in_iter else generators[:index + 1]
            else:
                visible = generators
            chains.append(visible)
        child = cur
        cur = parents.get(id(cur))
    return [
        generator
        for generators in reversed(chains)
        for generator in generators
    ]
def _comprehension_visible_bindings(node: ast.AST, parents: dict) -> dict:
    bindings: dict[str, ast.comprehension] = {}
    for generator in _comprehension_visible_generators(node, parents):
        for name in iter_unpack_target_names(generator.target):
            bindings[name] = generator
    return bindings
def _sink_comprehension_binding(tree: ast.AST, sink_var: str, sink_line: int,
                                names: _SinkNameResolver):
    for call, sink_name in _iter_line_sink_calls(tree, sink_line, names):
        for arg in _sink_payload_args(call, _SINK_BY_NAME.get(sink_name)):
            for name_node in iter_free_load_names(arg):
                if name_node.id != sink_var:
                    continue
                binding = _comprehension_visible_bindings(
                    name_node, names._parents).get(sink_var)
                if binding is not None:
                    return binding
    return None
def _comprehension_external_dependencies(generator: ast.comprehension,
                                         parents: dict, resolve,
                                         seen: frozenset = frozenset()) -> set:
    if id(generator) in seen:
        return set()
    seen = seen | {id(generator)}
    bindings = _comprehension_visible_bindings(generator.iter, parents)
    dependencies: set[tuple[str, ast.comprehension]] = set()
    for name in resolve(generator.iter):
        upstream = bindings.get(name)
        if upstream is None:
            dependencies.add((name, generator))
        else:
            dependencies |= _comprehension_external_dependencies(
                upstream, parents, resolve, seen)
    return dependencies
class BackwardTaintEngine:
    TRANSPARENT_FUNCS: ClassVar[frozenset] = _TRANSPARENT_FUNC_NAMES
    def __init__(self, source_tree, file_path: str,
                 source_names: frozenset | None = None):
        self.tree = source_tree
        self.file_path = file_path
        self._parents = build_parent_map(source_tree)
        self._events = _flow_events(source_tree, self._parents)
        self._source_names = (source_names if source_names is not None
                              else SOURCE_NAMES)
        self._names = _sink_name_resolver(source_tree)
        self._func_transfers = _collect_func_transfers(source_tree)
    def trace_backward(self, sink_var: str, _sink_line: int) -> set:
        context = _FlowContext(self.tree, _sink_line, self._parents)
        sanitizer_names = _flow_sanitizer_names(
            self.tree, _sink_line, self._names)
        sources = set()
        sink_position, sink_statement = self._sink_anchor(
            sink_var, _sink_line, context)
        start = (sink_var, sink_position, sink_statement)
        comp_binding = _sink_comprehension_binding(
            self.tree, sink_var, _sink_line, self._names)
        comp_dependencies = (
            _comprehension_external_dependencies(
                comp_binding, self._parents, self._resolve_definition)
            if comp_binding is not None else None)
        def _expand(state):
            if state == start and comp_dependencies is not None:
                return {
                    (name,
                     (getattr(gen.iter, "lineno", 0),
                      getattr(gen.iter, "col_offset", 0)),
                     _statement_for_node(gen.iter, context.parents))
                    for name, gen in comp_dependencies
                }
            return self._definition_upstream(state, context)
        for state in _bfs_visit(start, _expand):
            if state == start and comp_dependencies is not None:
                continue
            var, position, use_statement = state
            reaching = context.active(
                self._events, var, position=position,
                use_statement=use_statement)
            if reaching:
                if any(self._is_source_event(event, sanitizer_names)
                       for event in reaching):
                    sources.add(var)
                    continue
                if self._is_import_namespace(var, use_statement):
                    continue
                if not any(event.strong and _block_dominates(
                        self.tree, self._parents, event.block, use_statement)
                        for event in reaching):
                    sources.add(var)
                continue
            if self._is_import_namespace(var, use_statement):
                continue
            if self._outer_parameter_source(
                    var, position, use_statement, context, sanitizer_names):
                continue
            sources.add(var)
        return sources
    def _outer_parameter_source(
            self, var: str, position: tuple, use_statement: ast.AST | None,
            context: _FlowContext, sanitizer_names: set[str]) -> bool:
        parameter_scope = context.parameter_scope(var, use_statement)
        if parameter_scope is None:
            return False
        reaching = context.active(
            self._events, var, position=position,
            use_statement=use_statement, respect_parameters=False)
        return any(
            event.scope != id(parameter_scope)
            and self._is_source_event(event, sanitizer_names)
            for event in reaching)
    def _is_import_namespace(self, var: str,
                             use_statement: ast.AST | None) -> bool:
        if use_statement is None:
            return False
        scope = next(
            (self._names.scope_index[id(candidate)]
             for candidate in walk_nodes(use_statement)
             if id(candidate) in self._names.scope_index), "")
        kind, _state = self._names._binding_state(
            scope, var, use_statement)
        return kind is not None and kind[0] in _IMPORT_BINDING_KINDS
    def _sink_anchor(self, sink_var: str, sink_line: int,
                     context: _FlowContext) -> tuple[tuple[int, int], ast.stmt | None]:
        for call, _sink_name in _iter_line_sink_calls(
                self.tree, sink_line, self._names):
            if _payload_mentions(
                    call, sink_var, _SINK_BY_NAME.get(_sink_name)):
                return expr_end(call), _statement_for_node(call, context.parents)
        return (sink_line, float("inf")), None
    def _is_source_event(self, event: _FlowEvent,
                         sanitizer_names: set[str]) -> bool:
        return _source_name_with_transfers(
            event.value, self._source_names, self._names,
            sanitizer_names, self._func_transfers) is not None
    def _definition_upstream(self, state: tuple, context: _FlowContext) -> set:
        var, position, use_statement = state
        upstream: set = set()
        for event in context.active(
                self._events, var, position=position,
                use_statement=use_statement):
            event_position = _event_position(event)
            for name in self._resolve_definition(event.value):
                upstream.add((name, event_position, event.node))
        return upstream
    def _resolve_definition(self, node, _depth: int = 0) -> set:
        if _depth > 100:
            return set()
        if isinstance(node, ast.Name):
            return {node.id}
        if isinstance(node, ast.Call):
            return self._resolve_call_definition(node, _depth)
        if isinstance(node, (ast.Subscript, ast.Attribute)):
            if isinstance(node.value, ast.Name):
                return {node.value.id}
            return self._resolve_definition(node.value, _depth + 1)
        if isinstance(node, ast.Starred):
            return self._resolve_definition(node.value, _depth + 1)
        if isinstance(node, ast.NamedExpr):
            return self._resolve_definition(node.value, _depth + 1)
        return self._resolve_nodes(_composite_child_nodes(node), _depth)
    def _resolve_nodes(self, nodes, _depth: int) -> set:
        upstream: set = set()
        for child in nodes or ():
            upstream |= self._resolve_definition(child, _depth + 1)
        return upstream
    def _resolve_call_definition(self, node: ast.Call, _depth: int) -> set:
        func_name = _call_short_name(node)
        if func_name in self.TRANSPARENT_FUNCS:
            return self._transparent_call_upstream(node, _depth)
        signatures = self._func_transfers.get(func_name)
        if not signatures:
            return set()
        signature = _select_transfer_signature(
            signatures, attribute_call=isinstance(node.func, ast.Attribute))
        return self._resolve_nodes(
            _transfer_value_nodes(node, signature), _depth)
    def _transparent_call_upstream(self, node: ast.Call, _depth: int) -> set:
        nodes: list = [kw.value for kw in node.keywords]
        nodes.extend(node.args)
        if isinstance(node.func, ast.Attribute):
            nodes.append(node.func.value)
        return self._resolve_nodes(nodes, _depth)
class ForwardTaintProxy:
    def __init__(self, sink_var: str, sink_line: int):
        self.sink_var = sink_var
        self.sink_line = sink_line
    def trace_forward(self, tree, source_candidates=None) -> set:
        if not source_candidates:
            return set()
        source_candidates = ({source_candidates}
                             if isinstance(source_candidates, str)
                             else frozenset(source_candidates))
        names = _sink_name_resolver(tree)
        func_transfers = _collect_func_transfers(tree)
        sanitizer_names = _flow_sanitizer_names(tree, self.sink_line, names)
        parents = build_parent_map(tree)
        events = _flow_events(tree, parents)
        context = _FlowContext(tree, self.sink_line, parents)
        sink_position = _sink_position(
            tree, self.sink_var, self.sink_line, names)
        sink_statement = next((
            _statement_for_node(call, context.parents)
            for call, _sink_name in _iter_line_sink_calls(
                tree, self.sink_line, names)
            if _payload_mentions(
                call, self.sink_var, _SINK_BY_NAME.get(_sink_name))), None)
        comp_binding = _sink_comprehension_binding(
            tree, self.sink_var, self.sink_line, names)
        comp_dependencies = (
            _comprehension_external_dependencies(
                comp_binding, parents, _extract_names)
            if comp_binding is not None else None)
        forward_edges = {}
        events_by_target: dict[str, list[_FlowEvent]] = {}
        for event in events:
            events_by_target.setdefault(event.target, []).append(event)
        def _add_edge(src, dst):
            forward_edges.setdefault(src, set()).add(dst)
        parameter_scope = context.parameter_scope(
            self.sink_var, sink_statement)
        history = context.history(events, position=sink_position)
        if parameter_scope is not None:
            history = [
                event for event in history
                if event.target != self.sink_var
                or event.scope == id(parameter_scope)]
        source_event_ids = {
            id(event) for event in history
            if event.target in source_candidates
            and _source_name_with_transfers(
                event.value, SOURCE_NAMES, names, sanitizer_names,
                func_transfers) is not None
        }
        source_defined_candidates = {
            event.target for event in history if id(event) in source_event_ids
        }
        first_candidate_definitions: set[str] = set()
        for event in history:
            if event.target not in source_candidates:
                continue
            is_source_event = id(event) in source_event_ids
            if (not is_source_event
                    and _transfer_signature_for_call(
                        event.value, func_transfers) is not None):
                first_candidate_definitions.add(event.target)
                continue
            if (not is_source_event
                    and (event.target in source_defined_candidates
                         or event.target in first_candidate_definitions)):
                continue
            first_candidate_definitions.add(event.target)
            _add_edge((event.target, (0, 0)),
                      (event.target, _event_position(event)))
        for event in history:
            event_position = _event_position(event)
            destination = (event.target, event_position)
            for src in _extract_names(event.value):
                upstream = context.active(
                    events_by_target.get(src, []), target=src,
                    position=event_position, use_statement=event.node)
                if upstream:
                    for previous in upstream:
                        _add_edge(
                            (src, _event_position(previous)),
                            destination)
                elif (src in source_candidates
                      and src not in first_candidate_definitions):
                    _add_edge((src, (0, 0)), destination)
        if comp_dependencies is not None:
            terminal = {(self.sink_var, sink_position)}
            for src, generator in comp_dependencies:
                position = (getattr(generator.iter, "lineno", 0),
                            getattr(generator.iter, "col_offset", 0))
                statement = _statement_for_node(
                    generator.iter, context.parents)
                upstream = context.active(
                    events_by_target.get(src, []), target=src,
                    position=position, use_statement=statement)
                if upstream:
                    for previous in upstream:
                        _add_edge((src, _event_position(previous)),
                                  (self.sink_var, sink_position))
                elif src in source_candidates:
                    _add_edge((src, (0, 0)), (self.sink_var, sink_position))
        else:
            terminal = {
                (self.sink_var, _event_position(event))
                for event in context.active(
                    events, target=self.sink_var, position=sink_position,
                    use_statement=sink_statement)
            }
        if (comp_dependencies is None and not terminal
                and parameter_scope is None and self._used_at_sink(tree, names)):
            terminal.add((self.sink_var, (0, 0)))
        return {candidate for candidate in source_candidates
                if self._reaches_sink(
                    forward_edges, (candidate, (0, 0)), terminal)}
    def _used_at_sink(self, tree, names: _SinkNameResolver) -> bool:
        return any(
            _payload_mentions(
                node, self.sink_var, _SINK_BY_NAME.get(_sink_name))
            for node, _sink_name in _iter_line_sink_calls(
                tree, self.sink_line, names))
    def _reaches_sink(self, forward_edges: dict, start: tuple,
                      terminal: set[tuple]) -> bool:
        return any(node in terminal
                   for node in _bfs_visit(
                       start, lambda var: forward_edges.get(var, ())))
@dataclass
class TaintPath:
    source: str
    sink: str
    path: list[str] = field(default_factory=list)
    file: str = ""
    line: int = 0
@dataclass
class BidirectionalResult:
    sink: str = ""
    confirmed_paths: list[TaintPath] = field(default_factory=list)
    forward_only_paths: list[TaintPath] = field(default_factory=list)
    backward_only_paths: list[TaintPath] = field(default_factory=list)
    def summary(self) -> dict:
        return {
            "sink": self.sink,
            "confirmed": len(self.confirmed_paths),
            "forward_only": len(self.forward_only_paths),
            "backward_only": len(self.backward_only_paths),
        }
def _sink_identity(sink_info) -> tuple[str, str, int] | None:
    if not isinstance(sink_info, dict):
        return None
    sink_var = sink_info.get("var", "")
    sink_file = finding_file_path(sink_info)
    sink_line = coerce_line(sink_info.get("line", 0))
    if (not isinstance(sink_var, str) or not sink_var
            or not sink_file or sink_line <= 0):
        return None
    return sink_var, sink_file, sink_line
class BidirectionalTaintFlow:
    def __init__(self, skill_dir: str):
        self.skill_dir = skill_dir
        self._source_files = {}
        self._sanitized_memo: dict[tuple, tuple[Any, dict]] = {}
    def validate_all(self, sinks, source_candidates=None) -> dict:
        results = {}
        for sink_info in sinks or ():
            identity = _sink_identity(sink_info)
            if identity is None:
                continue
            sink_var, sink_file, sink_line = identity
            results[f"{sink_file}:{sink_line}:{sink_var}"] = self.validate_sink(
                sink_var, sink_file, sink_line, source_candidates)
        return results
    def validate_sink(self, sink_var: str, sink_file: str, sink_line: int,
                      source_candidates=None) -> BidirectionalResult:
        sink_file = os.fspath(sink_file)
        result = BidirectionalResult(sink=sink_var)
        tree = self._load_ast(sink_file)
        if tree is None:
            return result
        backward_engine = BackwardTaintEngine(tree, sink_file)
        backward_sources = backward_engine.trace_backward(sink_var, sink_line)
        candidates = (source_candidates if source_candidates is not None
                      else backward_sources)
        forward_engine = ForwardTaintProxy(sink_var, sink_line)
        forward_sources = forward_engine.trace_forward(tree, candidates)
        confirmed_sources = self._confirmed_sources(
            tree, sink_var, sink_line, forward_sources & backward_sources)
        for src in sorted(forward_sources - backward_sources):
            result.forward_only_paths.append(TaintPath(
                source=src, sink=sink_var, path=[src, sink_var],
                file=sink_file, line=sink_line,
            ))
        for src in sorted(backward_sources - forward_sources):
            result.backward_only_paths.append(TaintPath(
                source=src, sink=sink_var, path=[sink_var, src],
                file=sink_file, line=sink_line,
            ))
        for src in sorted(confirmed_sources):
            result.confirmed_paths.append(TaintPath(
                source=src, sink=sink_var, path=[src, sink_var],
                file=sink_file, line=sink_line,
            ))
        return result
    def _confirmed_sources(self, tree, sink_var: str, sink_line: int,
                           sources: set) -> set:
        if not sources:
            return set()
        names = _sink_name_resolver(tree)
        scopes = names.scope_index
        shadow = names.shadow
        if self._sanitized_at_sink(
                tree, sink_var, sink_line, names, scopes, shadow):
            return set()
        return set(sources)
    def _sanitized_at_sink(self, tree, sink_var: str, sink_line: int,
                           names: _SinkNameResolver, scopes: dict,
                           shadow: tuple) -> bool:
        comp_binding = _sink_comprehension_binding(
            tree, sink_var, sink_line, names)
        matched = False
        events = _flow_events(tree, names._parents)
        for node, sink_name in _iter_line_sink_calls(tree, sink_line, names):
            if not _payload_mentions(
                    node, sink_var, _SINK_BY_NAME.get(sink_name)):
                continue
            matched = True
            sanitizer_names = _builtin_sanitizer_names_for_sink(sink_name)
            sanitized = self._sanitized_keys(
                tree, names, sanitizer_names)
            scope = scopes.get(id(node), "")
            key = TaintNameResolution.owner_key(scope, sink_var, shadow)
            if comp_binding is not None:
                sanitized = dict(sanitized)
                sanitized.pop(key, None)
            sanitized = _sanitized_keys_at_use(
                sanitized, events, _statement_for_node(node, names._parents))
            if not is_sanitized(
                    node, scope=scope, sanitized_keys=sanitized,
                    shadow=shadow, tainted_vars={key: 1},
                    sanitizer_names=sanitizer_names,
                    call_name_candidates=names.candidates,
                    argument_nodes=_sink_payload_args(
                        node, _SINK_BY_NAME.get(sink_name)),
                    check_inline_sources=False):
                return False
        return matched
    def _sanitized_keys(self, tree, names: _SinkNameResolver,
                        sanitizer_names: set) -> dict:
        key = (id(tree), frozenset(sanitizer_names))
        cached = self._sanitized_memo.get(key)
        if cached is not None and cached[0] is tree:
            return cached[1]
        sanitized = collect_sanitized_keys(
            tree, sanitizer_names, names.scope_index, names.shadow,
            call_name_candidates=names.candidates)
        self._sanitized_memo[key] = (tree, sanitized)
        return sanitized
    def _load_ast(self, file_path):
        if file_path in self._source_files:
            return self._source_files[file_path]
        abs_path = file_path if os.path.isabs(file_path) else \
            os.path.join(self.skill_dir, file_path)
        tree = None
        if os.path.isfile(abs_path):
            source, read_error = read_py_source_with_error(abs_path)
            if source is None:
                logger.warning("BidirectionalTaintFlow 读取失败 %s: %s",
                               file_path, read_error)
            else:
                try:
                    tree = ast.parse(source, filename=abs_path)
                except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
                    logger.warning("BidirectionalTaintFlow 解析失败 %s: %s",
                                   file_path, e)
                    tree = None
        self._source_files[file_path] = tree
        return tree
_SECURITY_FAMILY_KEYWORDS = (
    "sql_injection", "command_injection", "path_traversal", "deserialization",
    "secret", "credential", "insecure", "security", "taint", "ssti",
    "render_template", "xss", "ssrf", "danger_pattern", "vulnerability",
    "exploit", "attack", "unsafe",
)
_SECURITY_IDENTITY_KEYS = ("rule_family", "dimension", "category",
                           "check_family", "rule_type")
_SECURITY_RULE_ID_RE = re.compile(
    r"^(?:"
    r"(?:SE|SEC|TAINT|VULN|SSTI)(?:[-_ ]?\d+[A-Za-z]?|[-_ ].+)"
    r"|(?:CWE|CVE|PYSEC|GHSA|OWASP)[-_ ]?[A-Za-z0-9][A-Za-z0-9._-]*"
    r"|B\d{3}"
    r")$", re.IGNORECASE)
def _security_identity_text(finding: dict) -> str:
    return " ".join(
        str(finding.get(key) or "") for key in _SECURITY_IDENTITY_KEYS
    ).lower()
def _looks_security_finding(finding: dict) -> bool:
    if not isinstance(finding, dict):
        return False
    if any(k in _security_identity_text(finding)
           for k in _SECURITY_FAMILY_KEYWORDS):
        return True
    rule_id = str(
        finding.get("rule_id") or finding.get("type")
        or finding.get("check_id") or "").strip()
    return bool(rule_id) and bool(_SECURITY_RULE_ID_RE.match(rule_id))
def _normalize_max_sinks(value) -> int:
    budget = safe_int(value, default=_DEFAULT_MAX_SINKS)
    return budget if budget >= 0 else _DEFAULT_MAX_SINKS
def _security_findings(findings) -> list:
    if findings is None or not hasattr(findings, "__iter__"):
        return []
    return [f for f in findings
            if isinstance(f, dict) and _looks_security_finding(f)]
_TRANSPARENT_RECEIVER_METHODS: frozenset[str] = frozenset({
    *_TRANSPARENT_FUNC_NAMES,
    "get", "pop", "setdefault", "encode", "decode",
    "read", "readline", "readlines",
})
_SELF_RECEIVER_NAMES: frozenset[str] = frozenset({"self", "cls"})
def _is_namespace_object(call: ast.Call, receiver: ast.Name,
                         names_resolver: _SinkNameResolver) -> bool:
    return names_resolver.is_namespace_binding(
        names_resolver.scope_index.get(id(call), ""), receiver.id, call)
def _call_covers_line(call: ast.Call, line: int) -> bool:
    start = getattr(call, "lineno", 0) or 0
    end = getattr(call, "end_lineno", None) or start
    return start <= line <= end
def _iter_line_sink_calls(tree, line: int,
                          names_resolver: _SinkNameResolver | None = None):
    resolver = names_resolver or _sink_name_resolver(tree)
    seen: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call) or id(node) in seen:
            continue
        if not _call_covers_line(node, line):
            continue
        sink_name = resolver.sink_name(node, SINK_NAMES)
        if sink_name is None:
            continue
        seen.add(id(node))
        yield node, sink_name
def _sink_position(tree, sink_var: str, sink_line: int,
                   names_resolver: _SinkNameResolver | None = None
                   ) -> tuple[int, int]:
    for call, _sink_name in _iter_line_sink_calls(
            tree, sink_line, names_resolver):
        if _payload_mentions(
                call, sink_var, _SINK_BY_NAME.get(_sink_name)):
            return expr_end(call)
    return (sink_line, float("inf"))
def _collect_sink_names(node, names: list,
                        names_resolver: _SinkNameResolver,
                        _receiver_only: bool = False) -> None:
    if isinstance(node, ast.Name):
        if not (_receiver_only and node.id in _SELF_RECEIVER_NAMES):
            names.append(node.id)
        return
    if isinstance(node, ast.Call):
        sink_name = names_resolver.sink_name(node, SINK_NAMES)
        args = (_sink_payload_args(
            node, _SINK_BY_NAME.get(sink_name)) if sink_name is not None
                else [*node.args,
                      *(kw.value for kw in node.keywords
                        if kw.value is not None)])
        for arg in args:
            _collect_sink_names(arg, names, names_resolver, _receiver_only)
        _func = node.func
        if isinstance(_func, ast.Attribute):
            _recv = _func.value
            if isinstance(_recv, ast.Name):
                if (_func.attr in _TRANSPARENT_RECEIVER_METHODS
                        and _recv.id not in _SELF_RECEIVER_NAMES
                        and not _is_namespace_object(
                            node, _recv, names_resolver)):
                    names.append(_recv.id)
            elif isinstance(_recv, (ast.Attribute, ast.Call, ast.Subscript)):
                _collect_sink_names(_recv, names, names_resolver, True)
        elif isinstance(_func, (ast.Call, ast.Subscript)):
            _collect_sink_names(_func, names, names_resolver, True)
        return
    if isinstance(node, ast.Dict):
        _collect_dict_names(node, names, names_resolver, _receiver_only)
        return
    if isinstance(node, (ast.Yield, ast.YieldFrom)):
        _collect_sink_names(node.value, names, names_resolver, _receiver_only)
        return
    if isinstance(node, ast.expr):
        # 作为 Call.func 的 Name（如 ``"run " + str(safe)`` 里的 ``str``）是被
        # 调用的函数而非流入汇点的数据变量；若当作汇点变量，
        # ``_payload_mentions`` 会因其字面出现在 payload 中而判定“已使用”，
        # 把 ``int()`` 净化后的安全样本确认为 confirmed。
        _callee_ids = {id(_c.func) for _c in ast.walk(node)
                       if isinstance(_c, ast.Call)}
        names.extend(_n.id for _n in iter_free_load_names(node)
                     if id(_n) not in _callee_ids
                     and not (_receiver_only
                              and _n.id in _SELF_RECEIVER_NAMES))
def _collect_dict_names(node: ast.Dict, names: list,
                        names_resolver: _SinkNameResolver,
                        _receiver_only: bool = False) -> None:
    for key, value in zip(node.keys or [], node.values, strict=False):
        if key is not None:
            _collect_sink_names(key, names, names_resolver, _receiver_only)
        _collect_sink_names(value, names, names_resolver, _receiver_only)
def _extract_sink_names(tree, line: int) -> list:
    names: list = []
    names_resolver = _sink_name_resolver(tree)
    for call, _sink_name in _iter_line_sink_calls(tree, line, names_resolver):
        for arg in _sink_payload_args(
                call, _SINK_BY_NAME.get(_sink_name)):
            _collect_sink_names(arg, names, names_resolver)
    seen: set = set()
    ordered: list = []
    for name in names:
        if name in seen:
            continue
        seen.add(name)
        ordered.append(name)
    return ordered
def _direct_source_name(tree, line: int) -> str | None:
    names_resolver = _sink_name_resolver(tree)
    for call, sink_name in _iter_line_sink_calls(tree, line, names_resolver):
        prune = _sanitizer_prune(
            names_resolver, _builtin_sanitizer_names_for_sink(sink_name))
        for _arg in _sink_payload_args(
                call, _SINK_BY_NAME.get(sink_name)):
            _src = first_taint_source(
                _arg, SOURCE_NAMES, prune=prune,
                call_name_candidates=names_resolver.source_candidates)
            if _src:
                return _src
    return None
def _normalize_finding_entry(f: dict) -> tuple[str, int, str] | None:
    fpath = finding_file_path(f)
    line = coerce_line(f.get("line", 0))
    if not line:
        line = coerce_line(f.get("line_number", 0))
    if not fpath or line <= 0:
        return None
    return fpath, line, _finding_locator(f, fpath, line)
def _finding_locator(finding: dict, fpath: str, line: int) -> str:
    locator = finding.get("locator")
    if isinstance(locator, str) and locator:
        return locator
    return f"{fpath}:{line}"
def _verify_finding_line(flow: BidirectionalTaintFlow, fpath: str, line: int,
                         sink_names: list, max_sinks: int,
                         verified: int) -> tuple[dict | None, int]:
    best: dict | None = None
    best_score = (-1, -1)
    for sink_var in sink_names:
        if verified >= max_sinks:
            break
        result = flow.validate_sink(sink_var, fpath, line)
        s = result.summary()
        verified += 1
        score = (s["confirmed"], s["forward_only"] + s["backward_only"])
        if score > best_score:
            best_score = score
            best = {"confirmed": s["confirmed"] > 0,
                    "sink": sink_var,
                    "forward_only": s["forward_only"],
                    "backward_only": s["backward_only"]}
    return best, verified
def validate_security_findings(skill_dir: str, findings: list | None,
                            max_sinks: int = _DEFAULT_MAX_SINKS) -> dict:
    max_sinks = _normalize_max_sinks(max_sinks)
    security_findings = _security_findings(findings)
    if not security_findings:
        return {"summary": {"confirmed": 0, "forward_only": 0,
                            "backward_only": 0, "sinks": 0},
                "per_finding": {}, "sinks_verified": 0}
    flow = BidirectionalTaintFlow(skill_dir)
    per_finding = {}
    summary = {"confirmed": 0, "forward_only": 0,
               "backward_only": 0, "sinks": 0}
    verified = 0
    line_cache: dict[tuple[str, int], dict | None] = {}
    for f in security_findings:
        entry = _normalize_finding_entry(f)
        if entry is None:
            continue
        fpath, line, locator = entry
        cache_key = (fpath, line)
        if cache_key in line_cache:
            best = line_cache[cache_key]
        else:
            best, verified = _verify_line_cached(
                flow, fpath, line, max_sinks, verified)
            line_cache[cache_key] = best
        if best is None:
            continue
        _accumulate_finding_result(per_finding, summary, locator, best)
    return {"summary": summary, "per_finding": per_finding,
            "sinks_verified": verified}
def _verify_line_cached(flow: BidirectionalTaintFlow, fpath: str, line: int,
                        max_sinks: int, verified: int) -> tuple[dict | None, int]:
    if verified >= max_sinks:
        return None, verified
    tree = flow._load_ast(fpath)
    if tree is None:
        return None, verified
    sink_names = _extract_sink_names(tree, line)
    best = None
    if sink_names:
        best, verified = _verify_finding_line(
            flow, fpath, line, sink_names, max_sinks, verified)
    if best is not None and best["confirmed"]:
        return best, verified
    _direct = _direct_source_name(tree, line)
    if _direct is None:
        return best, verified
    if not sink_names:
        verified += 1
    return {"confirmed": True, "sink": _direct, "forward_only": 0,
            "backward_only": 0, "direct_source": True}, verified
def _accumulate_finding_result(per_finding: dict, summary: dict,
                               locator: str, best: dict) -> None:
    per_finding[locator] = dict(best)
    summary["sinks"] += 1
    if best["confirmed"]:
        summary["confirmed"] += 1
        return
    summary["forward_only"] += best.get("forward_only", 0)
    summary["backward_only"] += best.get("backward_only", 0)

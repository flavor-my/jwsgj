from __future__ import annotations

import ast
import logging
import os
import threading
from collections.abc import Iterable
from dataclasses import dataclass, field
from functools import partial
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    dotted_name,
    iter_own_nodes,
    iter_params,
    iter_pattern_capture_names,
    iter_unpack_target_names,
    module_postpones_annotations,
)
from jwsgj.diag_shared_ast_views import parent_map, tree_nodes
from jwsgj.diag_shared_source_core import (
    parse_py_file,
    read_source,
)
from jwsgj.diag_shared_source_scan import (
    line_has_applicable_nosec,
    line_has_taint_suppression,
)
from jwsgj.diag_testing_test_index import iter_collectable_test_functions
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    is_generic_archive_or_cache_path,
    is_scan_py_name,
    is_test_source_basename,
    prune_scan_dirnames,
    scan_prune_dirs,
)

_log = logging.getLogger("jwsgj.engine_d2_flow")
__all__ = [
    "ALIAS_SINK_ROUTES",
    "MUTATING_ATTRS",
    "POWERSHELL_PROGRAMS",
    "SINK_BARE_NAMES",
    "CrossFileTaintEngine",
    "alias_resolve_map",
    "calls_by_lineno_cached",
    "clear_call_scan_memos",
    "clear_flow_memos",
    "collect_d2_taint_source_cached",
    "d2_expr_taint_source",
    "expr_reaches_param",
    "fn_def_site_exprs",
    "function_param_names",
    "has_nosec_marker",
    "interpreter_option_consumes_value",
    "iter_calls_with_scope_cached",
    "iter_module_scope_stmts",
    "load_sink_tree",
    "match_capture_names",
    "match_sink",
    "memo_clear",
    "memo_hit",
    "memo_store",
    "parse_module_aliases_cached",
    "shell_interpretation_open",
    "sink_first_arg",
]
def load_sink_tree(skill_dir: str, rel_file, cache=None) -> tuple[Any, Any]:
    if not skill_dir or not rel_file:
        return None, None
    try:
        root = os.path.realpath(skill_dir)
        path = os.path.realpath(os.path.join(root, rel_file))
        if os.path.normcase(os.path.commonpath((root, path))) != os.path.normcase(root):
            _log.debug("[D2] sink 路径越出扫描根（忽略）: %r",
                       (skill_dir, rel_file))
            return None, None
    except (OSError, TypeError, ValueError) as _e:
        _log.debug("[D2] sink 路径解析失败（忽略）: %r (%s)",
                   (skill_dir, rel_file), _e)
        return None, None
    if not os.path.isfile(path):
        return None, None
    tree = _parse_file_tree(path, cache, "sink 文件", quiet=True)
    if tree is None:
        return None, None
    return tree, path
_D2_SINK_NOSEC_RULES = {
    "eval": frozenset({"B307"}),
    "exec": frozenset({"B102"}),
}
_SUBPROCESS_EXEC_FUNCS = frozenset({
    "run", "call", "Popen", "check_call", "check_output",
    "getoutput", "getstatusoutput",
})
_SUBPROCESS_EXEC_TARGETS = frozenset(
    f"@subprocess.{name}" for name in _SUBPROCESS_EXEC_FUNCS)
def _read_nosec_source(path: str, cache) -> str | None:
    getter = getattr(cache, "get_source", None) if cache is not None else None
    if callable(getter):
        try:
            cached = getter(path)
        except (OSError, ValueError) as _e:
            _log.debug("[D2] nosec 缓存读取失败，回退文件通道: %s (%s)",
                       path, _e)
            cached = None
        if cached is not None:
            return cached
    try:
        return read_source(path)
    except (OSError, ValueError) as _e:
        _log.debug("[D2] nosec 判定源码读取失败: %s (%s)", path, _e)
        return None
def has_nosec_marker(skill_dir, rel_file, line, sink="", cache=None) -> bool:
    try:
        _tree, path = load_sink_tree(skill_dir, rel_file, cache)
        if not path:
            return False
        source = _read_nosec_source(path, cache)
        if source is None:
            return False
        if line_has_taint_suppression(source, line, sink):
            return True
        _category = ("command_injection"
                     if sink in {"system", "popen", "subprocess"} else "")
        return line_has_applicable_nosec(
            source, line, _category,
            _D2_SINK_NOSEC_RULES.get(sink, frozenset()))
    except Exception as _e:  
        _log.debug("nosec 判定异常，保守不判 audited 交 CV 仲裁: %s", _e,
                   exc_info=True)
        return False
def _collect_import_aliases(node: ast.AST, aliases: dict[str, str], *,
                            sink_relevant_only: bool,
                            visible_names: Iterable[str]) -> None:
    shadow_names = frozenset(visible_names).union(
        aliases, _MODULE_SHADOW_RELEVANT)
    if isinstance(node, ast.Import):
        _collect_import_stmt_aliases(
            node, aliases, sink_relevant_only=sink_relevant_only,
            shadow_names=shadow_names)
    elif isinstance(node, ast.ImportFrom):
        _collect_from_import_aliases(
            node, aliases, shadow_names=shadow_names)
def _collect_import_stmt_aliases(node: ast.Import, aliases: dict[str, str], *,
                                 sink_relevant_only: bool,
                                 shadow_names: frozenset[str]) -> None:
    for a in node.names:
        _root = a.name.split(".", 1)[0]
        _bound = a.asname or _root
        if a.asname is None and _root in _SINK_IMPORT_ROOTS:
            aliases[_root] = _root
            continue
        if (a.asname is not None
                and (_root in _SINK_IMPORT_ROOTS or not sink_relevant_only)):
            aliases[_bound] = a.name
            continue
        if _bound in shadow_names:
            aliases[_bound] = ""
def _collect_from_import_aliases(node: ast.ImportFrom,
                                 aliases: dict[str, str], *,
                                 shadow_names: frozenset[str]) -> None:
    _star = _STAR_SINK_NAMES.get(node.module or "") if not node.level else None
    for a in node.names:
        if a.name == "*":
            if _star:
                aliases.update(_star)
            continue
        _bound = a.asname or a.name
        _target = (None if node.level else
                   _from_import_target(node.module or "", a.name))
        if _target is not None:
            aliases[_bound] = _target
        elif _bound in shadow_names:
            aliases[_bound] = ""
def _from_import_target(module: str, name: str) -> str | None:
    if name == "*" or "." in name:
        return None
    if module == "os" and name in {"system", "popen"}:
        return f"@os.{name}"
    if module == "subprocess" and name in _SUBPROCESS_EXEC_FUNCS:
        return f"@subprocess.{name}"
    if module == "builtins" and name in _BUILTINS_ATTR_SINKS:
        return f"@builtins.{name}"
    return None
def _parse_module_aliases(tree: ast.Module) -> dict[str, str]:
    aliases: dict[str, str] = {}
    for node in iter_module_scope_stmts(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            _collect_import_aliases(
                node, aliases, sink_relevant_only=False,
                visible_names=aliases)
    return aliases
MUTATING_ATTRS = frozenset({"extend", "append", "insert", "add", "update"})
SINK_BARE_NAMES = frozenset({"eval", "exec", "system", "popen", "open"})
_SINK_MODULE_ROOTS = frozenset({"os", "subprocess"})
_SINK_IMPORT_ROOTS = frozenset(_SINK_MODULE_ROOTS | {"builtins"})
_BUILTINS_ATTR_SINKS = frozenset({"eval", "exec", "open"})
_STAR_SINK_NAMES: dict[str, dict[str, str]] = {
    "os": {"system": "@os.system", "popen": "@os.popen"},
    "subprocess": {
        name: f"@subprocess.{name}" for name in _SUBPROCESS_EXEC_FUNCS},
}
ALIAS_SINK_ROUTES = {
    "@os.system": "system", "@os.popen": "popen",
    "@builtins.eval": "eval", "@builtins.exec": "exec",
    "@builtins.open": "open",
    **{name: name for name in SINK_BARE_NAMES},
}
_MODULE_SHADOW_RELEVANT = frozenset(SINK_BARE_NAMES | _SINK_MODULE_ROOTS
                                   | {"builtins"})
_TRY_BLOCK_TYPES = (ast.Try, getattr(ast, "TryStar", ast.Try))
_MATCH_TYPE = getattr(ast, "Match", None)
_MATCH_CASE_TYPE = getattr(ast, "match_case", None)
def _is_match_node(node: ast.AST) -> bool:
    return _MATCH_TYPE is not None and isinstance(node, _MATCH_TYPE)
_COMP_CONTAINER_TYPES = (ast.ListComp, ast.SetComp, ast.GeneratorExp,
                          ast.DictComp)
def _children_in_eval_order(node: ast.AST) -> list:
    if isinstance(node, ast.DictComp):
        return [*node.generators, node.key, node.value]
    if isinstance(node, _COMP_CONTAINER_TYPES):
        return [*node.generators, node.elt]
    if isinstance(node, ast.Dict):
        return _dict_children_in_eval_order(node)
    return list(ast.iter_child_nodes(node))
def _dict_children_in_eval_order(node: ast.Dict) -> list:
    _children: list = []
    for _key, _value in zip(node.keys, node.values, strict=True):
        if _key is not None:
            _children.append(_key)
        _children.append(_value)
    return _children
def match_capture_names(node: ast.AST) -> list[str]:
    if not _is_match_node(node):
        return []
    names: list[str] = []
    for case in node.cases:
        names.extend(iter_pattern_capture_names(case.pattern))
    return names
def _assign_roots(value: ast.AST) -> list[str]:
    roots: list[str] = []
    stack: list[tuple[ast.AST, frozenset[str]]] = [(value, frozenset())]
    while stack:
        node, bound = stack.pop()
        if isinstance(node, ast.Name):
            if isinstance(node.ctx, ast.Load) and node.id not in bound:
                roots.append(node.id)
            continue
        if isinstance(node, ast.Lambda):
            args = node.args
            children = [(_d, bound) for _d in (
                *args.defaults, *(_d for _d in args.kw_defaults if _d is not None))]
            children.append((node.body, bound | frozenset(function_param_names(node))))
        elif isinstance(node, _COMP_CONTAINER_TYPES):
            generators = node.generators
            local = bound
            children = []
            for generator in generators:
                children.append((generator.iter, local))
                local = local | frozenset(
                    iter_unpack_target_names(generator.target))
                children.extend((test, local) for test in generator.ifs)
            values = (node.key, node.value) if isinstance(node, ast.DictComp) else (node.elt,)
            children.extend((item, local) for item in values)
        else:
            children = [(child, bound) for child in ast.iter_child_nodes(node)]
        stack.extend(reversed(children))
    return roots
def _def_site_frame_seq(node) -> list:
    _body = node.body if isinstance(node.body, list) else [node.body]
    _seq = [*fn_def_site_exprs(node)]
    if not isinstance(node, ast.Lambda):
        _seq.append(("bind_definition", node))
    return [*_seq, ("push", function_param_names(node)),
            *_body, ("pop", None)]
@dataclass
class _IfBranchState:
    entry: tuple
    conditional_depth: int
    body: tuple | None = None
@dataclass
class _TraversalState:
    aliases: dict[str, str]
    deferred_annotations: frozenset[int] = field(default_factory=frozenset)
    module_import_events: tuple = ()
    module_shadow_events: tuple = ()
    module_scoped_shadows: tuple = ()
    module_alias_seed: dict[str, str] = field(default_factory=dict)
    module_alias_cache: dict[int, dict[str, str]] = field(default_factory=dict)
    param_stack: list[list[str]] = field(default_factory=list)
    assign_stack: list[dict[str, list[str]]] = field(
        default_factory=list)
    alias_stack: list[dict[str, str]] = field(default_factory=list)
    clean_binding_stack: list[tuple[str, object, object]] = field(
        default_factory=list)
    scope_kinds: list[str] = field(default_factory=list)
    conditional_depth: int = 0
    conditional_depth_stack: list[int] = field(default_factory=list)
    if_stack: list[_IfBranchState] = field(default_factory=list)
    result: list[tuple[ast.Call, list[str] | None,
                      dict[str, list[str]] | None,
                      dict[str, str] | None]] = field(
        default_factory=list)
def _copy_assign_frames(frames: list) -> list:
    return [{name: list(roots) for name, roots in frame.items()}
            for frame in frames]
def _copy_alias_frames(frames: list) -> list:
    return [dict(frame) for frame in frames]
def _capture_if_frames(state: _TraversalState) -> tuple:
    return (_copy_assign_frames(state.assign_stack),
            _copy_alias_frames(state.alias_stack))
def _restore_if_frames(state: _TraversalState, snapshot: tuple) -> None:
    state.assign_stack = _copy_assign_frames(snapshot[0])
    state.alias_stack = _copy_alias_frames(snapshot[1])
_MISSING_BINDING = object()
def _alias_options(value) -> tuple[str, ...]:
    if isinstance(value, frozenset):
        return tuple(sorted(_v for _v in value if isinstance(_v, str)))
    return (value,) if isinstance(value, str) else ()
def _combined_alias_value(values) -> str | frozenset[str]:
    options = sorted({_option for _value in values
                      for _option in _alias_options(_value) if _option})
    if not options:
        return ""
    return options[0] if len(options) == 1 else frozenset(options)
def _merge_if_frames(state: _TraversalState, entry: tuple,
                     left: tuple, right: tuple) -> tuple:
    merged_assigns: list = []
    visible_params = _scope_frame_indexes(
        len(state.param_stack), state.scope_kinds)
    for index, entry_frame in enumerate(entry[0]):
        left_frame = left[0][index]
        right_frame = right[0][index]
        names = set(entry_frame) | set(left_frame) | set(right_frame)
        merged: dict[str, list[str]] = {}
        for name in sorted(names):
            fallback = entry_frame.get(name, _MISSING_BINDING)
            if (fallback is _MISSING_BINDING
                    and any(name in state.param_stack[i]
                            for i in visible_params)):
                fallback = [_param_root(name)]
            values = (left_frame.get(name, fallback),
                      right_frame.get(name, fallback))
            if all(value is _MISSING_BINDING for value in values):
                continue
            roots: list[str] = []
            for value in values:
                if value is _MISSING_BINDING:
                    continue
                roots.extend(root for root in value if root not in roots)
            merged[name] = roots
        merged_assigns.append(merged)
    merged_aliases: list = []
    entry_visible = dict(state.aliases)
    for _i in _alias_scope_frame_indexes(len(entry[1]), state.scope_kinds):
        entry_visible.update(entry[1][_i])
    for index, entry_frame in enumerate(entry[1]):
        left_frame = left[1][index]
        right_frame = right[1][index]
        names = set(entry_frame) | set(left_frame) | set(right_frame)
        merged = {}
        for name in sorted(names):
            fallback = entry_frame.get(
                name, entry_visible.get(name, _MISSING_BINDING))
            values = (left_frame.get(name, fallback),
                      right_frame.get(name, fallback))
            if all(value is _MISSING_BINDING for value in values):
                continue
            if values[0] == values[1] and values[0] is not _MISSING_BINDING:
                merged[name] = values[0]
            else:
                merged[name] = _combined_alias_value(values)
        merged_aliases.append(merged)
    return merged_assigns, merged_aliases
def _enter_if_branch(state: _TraversalState) -> None:
    state.if_stack.append(_IfBranchState(
        _capture_if_frames(state), state.conditional_depth))
    state.conditional_depth = 0
def _swap_if_branch(state: _TraversalState) -> None:
    if not state.if_stack:
        _log.warning("[D2] if 分支标记 swap 与 enter 不配对（忽略）")
        return
    branch = state.if_stack[-1]
    branch.body = _capture_if_frames(state)
    _restore_if_frames(state, branch.entry)
    state.conditional_depth = 0
def _exit_if_branch(state: _TraversalState) -> None:
    if not state.if_stack:
        _log.warning("[D2] if 分支标记 exit 与 enter 不配对（忽略）")
        return
    branch = state.if_stack.pop()
    right = _capture_if_frames(state)
    left = branch.body if branch.body is not None else branch.entry
    merged = _merge_if_frames(state, branch.entry, left, right)
    _restore_if_frames(state, merged)
    state.conditional_depth = branch.conditional_depth
def _mutating_receiver_root(rv: ast.expr) -> str:
    if isinstance(rv, ast.Subscript) and isinstance(rv.value, ast.Name):
        return rv.value.id
    if isinstance(rv, ast.Name):
        return rv.id
    return ""
def _extend_mutating_arg_roots(node: ast.Call, recv: str,
                               frame: dict,
                               param_stack: list | None = None,
                               scope_kinds: list | None = None) -> None:
    _roots = frame.get(recv)
    if _roots is None:
        _roots = []
        _frames = list(param_stack or ())
        if any(recv in _frames[_i] for _i in
               _scope_frame_indexes(len(_frames), scope_kinds)):
            _roots.append(_param_root(recv))
        frame[recv] = _roots
    for _arg in (*node.args, *(kw.value for kw in node.keywords)):
        for _rn in _assign_roots(_arg):
            _roots.append(_rn)
def _register_mutating_call(node: ast.Call, assign_stack: list,
                            param_stack: list | None = None,
                            scope_kinds: list | None = None) -> None:
    if (assign_stack and isinstance(node.func, ast.Attribute)
            and node.func.attr in MUTATING_ATTRS):
        _recv = _mutating_receiver_root(node.func.value)
        if _recv:
            _extend_mutating_arg_roots(node, _recv, assign_stack[-1],
                                       param_stack, scope_kinds)
def _visible_frame_indexes(scope_kinds: list) -> list[int]:
    if not scope_kinds:
        return []
    _last = len(scope_kinds) - 1
    _in_function = 'function' in scope_kinds
    return [i for i, kind in enumerate(scope_kinds)
            if (kind != 'class' or i == _last)
            and (kind != 'module' or not _in_function)]
def _scope_frame_indexes(frame_count: int,
                         scope_kinds: list | None) -> list[int] | range:
    if scope_kinds is None or len(scope_kinds) != frame_count:
        return range(frame_count)
    return _visible_frame_indexes(scope_kinds)
def _alias_scope_frame_indexes(frame_count: int,
                               scope_kinds: list | None) -> list[int]:
    indexes = set(_scope_frame_indexes(frame_count, scope_kinds))
    if (scope_kinds is not None and len(scope_kinds) == frame_count
            and 'function' in scope_kinds):
        indexes.update(i for i, kind in enumerate(scope_kinds)
                       if kind == 'module')
    return sorted(indexes)
def _merged_scope_aliases(aliases: dict[str, str],
                          alias_stack: list,
                          scope_kinds: list | None = None) -> dict[str, str]:
    scope_aliases = dict(aliases)
    for _i in _alias_scope_frame_indexes(len(alias_stack), scope_kinds):
        scope_aliases.update(alias_stack[_i])
    return scope_aliases
_ALIAS_SINK_VALUES = (_SINK_IMPORT_ROOTS | frozenset(ALIAS_SINK_ROUTES)
                     | _SUBPROCESS_EXEC_TARGETS)
def _alias_for_roots(roots: list[str],
                     visible: dict[str, str] | None = None,
                     ) -> str | frozenset[str]:
    if len(roots) != 1:
        return ""
    root = roots[0]
    if visible is not None:
        root = visible.get(root, root)
    if isinstance(root, frozenset):
        return _combined_alias_value(root.intersection(_ALIAS_SINK_VALUES))
    return root if root in _ALIAS_SINK_VALUES else ""
def _project_local_aliases(state: _TraversalState, names: Iterable[str],
                           frame: dict) -> None:
    if not state.alias_stack:
        return
    visible = _merged_scope_aliases(
        state.aliases, state.alias_stack, state.scope_kinds)
    _apply_param_shadows(state, visible)
    for name in names:
        alias = _alias_for_roots(frame.get(name, []), visible)
        state.alias_stack[-1][name] = alias
        visible[name] = alias
def _apply_param_shadows(state: _TraversalState,
                        scope_aliases: dict[str, str]) -> None:
    for _i in _visible_frame_indexes(state.scope_kinds):
        local_aliases = (state.alias_stack[_i]
                         if _i < len(state.alias_stack) else {})
        if _i < len(state.param_stack):
            for _name in state.param_stack[_i]:
                if _name not in local_aliases:
                    scope_aliases[_name] = ''
def _apply_shadow_bindings(state: _TraversalState,
                           scope_aliases: dict[str, str]) -> None:
    _apply_param_shadows(state, scope_aliases)
    for _i in _visible_frame_indexes(state.scope_kinds):
        local_aliases = (state.alias_stack[_i]
                         if _i < len(state.alias_stack) else {})
        if _i >= len(state.assign_stack):
            continue
        for _name, _roots in state.assign_stack[_i].items():
            if _name in local_aliases:
                continue
            alias = _alias_for_roots(_roots, scope_aliases)
            if alias or _name not in scope_aliases:
                scope_aliases[_name] = alias
def _is_module_root(node: ast.expr, scope_aliases: dict[str, str]) -> bool:
    if not isinstance(node, ast.Name):
        return False
    return any(_alias in _SINK_MODULE_ROOTS for _alias in
               _alias_options(scope_aliases.get(node.id, node.id)))
def _is_builtins_root(node: ast.expr, scope_aliases: dict[str, str]) -> bool:
    if not isinstance(node, ast.Name):
        return False
    return "builtins" in _alias_options(scope_aliases.get(node.id, node.id))
def _is_sink_candidate(_f: ast.expr, scope_aliases: dict[str, str]) -> bool:
    if isinstance(_f, ast.Name):
        return _f.id in SINK_BARE_NAMES or _f.id in scope_aliases
    if isinstance(_f, ast.Attribute):
        return (_f.attr == "open"
                or (_f.attr in _BUILTINS_ATTR_SINKS
                    and _is_builtins_root(_f.value, scope_aliases))
                or _is_module_root(_f.value, scope_aliases))
    return False
def _module_aliases_at_call(state: _TraversalState,
                            at: tuple[int, int]) -> dict[str, str]:
    if (not state.module_import_events and not state.module_shadow_events
            and not state.module_scoped_shadows):
        return state.aliases
    hit = state.module_alias_cache.get(at)
    if hit is not None:
        return hit
    aliases = _module_alias_timeline(
        state.module_alias_seed, state.module_import_events,
        state.module_shadow_events, at)
    for start, end, name in state.module_scoped_shadows:
        if start <= at <= end:
            aliases[name] = ""
    state.module_alias_cache[at] = aliases
    return aliases
def _handle_call_node(node: ast.Call, state: _TraversalState) -> None:
    base_aliases = (state.aliases if "function" in state.scope_kinds
                    else _module_aliases_at_call(
                        state, (node.lineno, node.col_offset)))
    scope_aliases = _merged_scope_aliases(
        base_aliases, state.alias_stack, state.scope_kinds)
    _apply_shadow_bindings(state, scope_aliases)
    if not _is_sink_candidate(node.func, scope_aliases):
        state.result.append((node, None, None, None))
        return
    params = [p for ps in state.param_stack for p in ps]
    state.result.append((node, params,
                         _merged_assign_snapshot(
                             state.assign_stack, state.scope_kinds),
                         dict(scope_aliases)))
def _merged_assign_snapshot(assign_stack: list,
                            scope_kinds: list | None = None) -> dict[str, list[str]]:
    merged: dict[str, list[str]] = {}
    _indexes = list(_scope_frame_indexes(len(assign_stack), scope_kinds))
    for _i in reversed(_indexes):
        for key, roots in assign_stack[_i].items():
            merged.setdefault(key, list(roots))
    return merged
def _register_function_import(node: ast.AST, state: _TraversalState) -> None:
    if state.assign_stack:
        _visible = _merged_scope_aliases(
            state.aliases, state.alias_stack, state.scope_kinds)
        _collect_import_aliases(
            node, state.alias_stack[-1], sink_relevant_only=True,
            visible_names=_visible)
_PARAM_ROOT_PREFIX = '@param:'
def _param_root(name: str) -> str:
    return f'{_PARAM_ROOT_PREFIX}{name}'
def _old_binding_roots(name: str, frame: dict, params: set[str]):
    if name in frame:
        return list(frame[name])
    if name in params:
        return [_param_root(name)]
    return None
def _binding_roots(roots: list[str], targets: set[str], frame: dict,
                   old: dict) -> list[str]:
    _resolved: list[str] = []
    for _root in roots:
        if _root in targets:
            _resolved.extend(old.get(_root) or ())
        elif _root in frame and not frame[_root]:
            continue
        else:
            _resolved.append(_root)
    return _resolved
def _freeze_rebound_aliases(frame: dict, targets: set[str], old: dict) -> None:
    for _name, _roots in list(frame.items()):
        if _name in targets:
            continue
        _frozen: list[str] = []
        for _root in _roots:
            if _root in targets:
                _frozen.extend(old.get(_root) or ())
            else:
                _frozen.append(_root)
        frame[_name] = list(dict.fromkeys(_frozen))
def _bind_deps(target: ast.AST, roots: Iterable[str], frame: dict,
               state: _TraversalState,
               replace: bool | None = None,
               root_plan: dict[str, list[str]] | None = None) -> None:
    _names = list(iter_unpack_target_names(target))
    _targets = set(_names)
    _roots = list(roots)
    _params = {p for ps in state.param_stack for p in ps}
    _old = {name: _old_binding_roots(name, frame, _params)
            for name in _names}
    _visible_aliases = _merged_scope_aliases(
        state.aliases, state.alias_stack, state.scope_kinds)
    for _name in _names:
        if (not _old[_name] and _name not in _params
                and _alias_options(_visible_aliases.get(_name, ""))):
            _old[_name] = [_name]
    if root_plan is None:
        shared = list(dict.fromkeys(
            _binding_roots(_roots, _targets, frame, _old)))
        resolved_by_name = {name: shared for name in _names}
    else:
        resolved_by_name = {
            name: list(dict.fromkeys(_binding_roots(
                root_plan.get(name, []), _targets, frame, _old)))
            for name in _names
        }
    if replace is None:
        replace = state.conditional_depth == 0
    _replace = replace
    if _replace:
        _freeze_rebound_aliases(frame, _targets, _old)
    for _tn in _names:
        resolved = resolved_by_name[_tn]
        if _replace:
            frame[_tn] = list(resolved)
        else:
            frame[_tn] = list(dict.fromkeys(
                [*(_old.get(_tn) or ()), *resolved]))
    _project_local_aliases(state, _names, frame)
def _direct_unpack_root_plan(target: ast.AST, value: ast.AST,
                             ) -> dict[str, list[str]] | None:
    if isinstance(target, ast.Name):
        return {target.id: _assign_roots(value)}
    if not isinstance(target, (ast.Tuple, ast.List)):
        return None
    if not isinstance(value, (ast.Tuple, ast.List)):
        return None
    if len(target.elts) != len(value.elts):
        return None
    plan: dict[str, list[str]] = {}
    for target_item, value_item in zip(target.elts, value.elts, strict=True):
        item_plan = _direct_unpack_root_plan(target_item, value_item)
        if item_plan is None:
            return None
        plan.update(item_plan)
    return plan
def _value_target_pairs(target: ast.AST,
                        value: ast.AST) -> list[tuple[str, ast.AST]]:
    if isinstance(target, ast.Name):
        return [(target.id, value)]
    if not isinstance(target, (ast.Tuple, ast.List)):
        return []
    if not isinstance(value, (ast.Tuple, ast.List)):
        return []
    if len(target.elts) != len(value.elts):
        return []
    pairs: list[tuple[str, ast.AST]] = []
    for target_item, value_item in zip(target.elts, value.elts, strict=True):
        pairs.extend(_value_target_pairs(target_item, value_item))
    return pairs
def _attribute_sink_alias(value: ast.AST,
                          visible: dict[str, str]) -> str:
    if (not isinstance(value, ast.Attribute)
            or not isinstance(value.value, ast.Name)):
        return ""
    for _base in _alias_options(visible.get(value.value.id, value.value.id)):
        _target = _from_import_target(_base, value.attr)
        if _target is not None:
            return _target
    return ""
def _apply_value_sink_aliases(target: ast.AST, value: ast.AST,
                              state: _TraversalState) -> None:
    if (not state.alias_stack or not state.assign_stack
            or not isinstance(value, ast.Attribute)
            or not isinstance(value.value, ast.Name)):
        return
    _pairs = _value_target_pairs(target, value)
    if not _pairs:
        return
    base_aliases = (state.aliases if "function" in state.scope_kinds
                    else _module_aliases_at_call(
                        state, _end_position(value)))
    visible = _merged_scope_aliases(
        base_aliases, state.alias_stack, state.scope_kinds)
    _apply_param_shadows(state, visible)
    for _name, _value in _pairs:
        _alias = _attribute_sink_alias(_value, visible)
        if not _alias:
            continue
        state.alias_stack[-1][_name] = _alias
        visible[_name] = _alias
def _assign_deps_assign(node: ast.Assign, state: _TraversalState) -> None:
    roots = _assign_roots(node.value)
    for t in node.targets:
        _bind_deps(
            t, roots, state.assign_stack[-1], state,
            root_plan=_direct_unpack_root_plan(t, node.value),
        )
        _apply_value_sink_aliases(t, node.value, state)
def _assign_deps_for_loop(node, state: _TraversalState) -> None:
    _bind_deps(node.target, _assign_roots(node.iter), state.assign_stack[-1],
               state, replace=True)
def _assign_deps_with_item(item: ast.withitem,
                          state: _TraversalState) -> None:
    if item.optional_vars is not None:
        _bind_deps(item.optional_vars, _assign_roots(item.context_expr),
                   state.assign_stack[-1], state)
def _assign_deps_with(node, state: _TraversalState) -> None:
    for _item in node.items:
        _assign_deps_with_item(_item, state)
def _assign_deps_comprehension(node: ast.comprehension,
                               state: _TraversalState) -> None:
    _bind_deps(node.target, _assign_roots(node.iter), state.assign_stack[-1],
               state, replace=True)
def _assign_deps_aug(node: ast.AugAssign, state: _TraversalState) -> None:
    if isinstance(node.target, ast.Name):
        _bind_deps(node.target, _assign_roots(node.value), state.assign_stack[-1],
                   state, replace=False)
def _assign_deps_ann(node: ast.AnnAssign, state: _TraversalState) -> None:
    if node.value is not None and isinstance(node.target, ast.Name):
        _bind_deps(node.target, _assign_roots(node.value), state.assign_stack[-1],
                   state)
        _apply_value_sink_aliases(node.target, node.value, state)
def _resolved_comprehension_roots(roots: list[str],
                                  state: _TraversalState) -> list[str]:
    _snapshot = _merged_assign_snapshot(state.assign_stack, state.scope_kinds)
    _resolved: list[str] = []
    for _root in roots:
        if _root in _snapshot:
            _resolved.extend(_snapshot[_root])
        else:
            _resolved.append(_root)
    return _resolved
def _assign_deps_walrus(node: ast.NamedExpr, state: _TraversalState) -> None:
    _in_comprehension = bool(
        state.scope_kinds and state.scope_kinds[-1] == 'comprehension')
    _roots = _assign_roots(node.value)
    if _in_comprehension:
        _roots = _resolved_comprehension_roots(_roots, state)
    for _i in range(len(state.assign_stack) - 1, -1, -1):
        if state.scope_kinds[_i] != 'comprehension':
            _bind_deps(node.target, _roots, state.assign_stack[_i], state,
                       replace=(not _in_comprehension
                                and state.conditional_depth == 0))
            return
def _assign_deps_match_case(node, case,
                            state: _TraversalState) -> None:
    _frame = state.assign_stack[-1]
    _names = list(iter_pattern_capture_names(case.pattern))
    _roots = _assign_roots(node.subject)
    for _name in _names:
        _frame[_name] = list(_roots)
    _project_local_aliases(state, _names, _frame)
_ASSIGN_DEPS_HANDLERS: dict = {
    ast.Assign: _assign_deps_assign,
    ast.For: _assign_deps_for_loop,
    ast.AsyncFor: _assign_deps_for_loop,
    ast.With: _assign_deps_with,
    ast.AsyncWith: _assign_deps_with,
    ast.AugAssign: _assign_deps_aug,
    ast.AnnAssign: _assign_deps_ann,
    ast.NamedExpr: _assign_deps_walrus,
}
def _assignment_frame_seq(node: ast.AST) -> list:
    if isinstance(node, ast.Assign):
        return [node.value, *node.targets, ("bind_deps", node)]
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return [node.iter, ("enter_if", None), ("bind_deps", node),
                *node.body, ("swap_if", None), ("exit_if", None),
                *_conditional_statements(node.orelse)]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        _seq: list = []
        for _item in node.items:
            _seq.extend((_item.context_expr, ("bind_with_item", _item)))
        return [*_seq, *node.body]
    if isinstance(node, ast.NamedExpr):
        return [node.value, ("bind_deps", node)]
    if isinstance(node, ast.AugAssign):
        return [node.target, node.value, ("bind_deps", node)]
    if _is_match_node(node):
        return _match_frame_seq(node)
    return [*_statement_children_in_eval_order(node), ("bind_deps", node)]
_IMPORT_NODE_TYPES = frozenset({ast.Import, ast.ImportFrom})
_DEF_SITE_NODE_TYPES = frozenset({
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda})
def _class_def_site_exprs(node: ast.ClassDef) -> list:
    _exprs: list = [*node.decorator_list, *node.bases]
    _exprs.extend(_kw.value for _kw in node.keywords)
    _exprs.extend(getattr(node, 'type_params', ()) or ())
    return _exprs
def _class_def_site_seq(node: ast.ClassDef) -> list:
    return [*_class_def_site_exprs(node),
            ("push_class", []), *node.body, ("pop", None),
            ("bind_definition", node)]
def _conditional_statements(statements: list) -> list:
    if not statements:
        return []
    return [('enter_conditional', None), *statements,
            ('exit_conditional', None)]
def _if_branch_seq(test: ast.AST, body: list, orelse: list) -> list:
    return [test, ('enter_if', None), *body, ('swap_if', None),
            *orelse, ('exit_if', None)]
def _match_cases_frame_seq(node, cases: list) -> list:
    if not cases:
        return []
    _case = cases[0]
    _body = [('bind_match_case', (node, _case))]
    if _case.guard is not None:
        _body.append(_case.guard)
    _body.extend(_case.body)
    return [('enter_if', None), *_body, ('swap_if', None),
            *_match_cases_frame_seq(node, cases[1:]), ('exit_if', None)]
def _match_frame_seq(node) -> list:
    return [node.subject, *_match_cases_frame_seq(node, list(node.cases))]
def _handler_frame_seq(handler) -> list:
    _seq: list = []
    if handler.type is not None:
        _seq.append(handler.type)
    if handler.name:
        _seq.append(('bind_clean', handler.name))
    _seq.extend(handler.body)
    if handler.name:
        _seq.append(('restore_clean', handler.name))
    return _seq
def _statement_children_in_eval_order(node: ast.AST) -> list:
    if isinstance(node, ast.If):
        return _if_branch_seq(node.test, node.body, node.orelse)
    if isinstance(node, ast.IfExp):
        return _if_branch_seq(node.test, [node.body], [node.orelse])
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return [node.iter, *_conditional_statements(node.body),
                *_conditional_statements(node.orelse)]
    if isinstance(node, ast.While):
        return [node.test, *_conditional_statements(node.body),
                *_conditional_statements(node.orelse)]
    if isinstance(node, _TRY_BLOCK_TYPES):
        _seq: list = [*_conditional_statements(node.body)]
        for _handler in node.handlers:
            _seq.extend(_conditional_statements(_handler_frame_seq(_handler)))
        _seq.extend(_conditional_statements(node.orelse))
        _seq.extend(_conditional_statements(node.finalbody))
        return _seq
    if _is_match_node(node):
        return _match_frame_seq(node)
    return _children_in_eval_order(node)
def _comprehension_frame_seq(node: ast.AST) -> list:
    _generators = node.generators
    _seq: list = [_generators[0].iter, ('push_comprehension', [])]
    for _index, _generator in enumerate(_generators):
        if _index:
            _seq.append(_generator.iter)
        _seq.append(('bind_comprehension', _generator))
        _seq.extend(_generator.ifs)
    if isinstance(node, ast.DictComp):
        _seq.extend((node.key, node.value))
    else:
        _seq.append(node.elt)
    _seq.append(('pop', None))
    return _seq
def _bind_local_scope_name(node: ast.AST, state: _TraversalState) -> None:
    _name = getattr(node, 'name', '')
    if not (_name and state.assign_stack):
        return
    _frame = state.assign_stack[-1]
    if state.conditional_depth:
        _params = {p for ps in state.param_stack for p in ps}
        _old = _old_binding_roots(_name, _frame, _params)
        _frame[_name] = list(_old) if _old is not None else []
    else:
        _frame[_name] = []
    _project_local_aliases(state, [_name], _frame)
def _handle_node(node: ast.AST, state: _TraversalState) -> list:
    if id(node) in state.deferred_annotations:
        return []
    _t = node.__class__
    if _t is ast.Call:
        _handle_call_node(node, state)
        return [*_children_in_eval_order(node), ("register_mutation", node)]
    if _t is ast.ClassDef:
        return _class_def_site_seq(node)
    if _t in _COMP_CONTAINER_TYPES:
        return _comprehension_frame_seq(node)
    if _t in _ASSIGN_DEPS_HANDLERS:
        return _assignment_frame_seq(node)
    if _t in _IMPORT_NODE_TYPES:
        _register_function_import(node, state)
        return _children_in_eval_order(node)
    if _t in _DEF_SITE_NODE_TYPES:
        return _def_site_frame_seq(node)
    return _statement_children_in_eval_order(node)
def _deferred_annotation_ids(tree: ast.Module) -> frozenset[int]:
    postponed = module_postpones_annotations(tree, require_absolute=True)
    annotations: list[ast.AST] = []
    stack: list[tuple[ast.AST, bool]] = [(tree, False)]
    while stack:
        node, in_function = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            in_function = True
            if postponed:
                annotations.extend(_arg_annotation_exprs(node.args))
                if not isinstance(node, ast.Lambda) and node.returns is not None:
                    annotations.append(node.returns)
        elif isinstance(node, ast.ClassDef):
            in_function = False
        elif isinstance(node, ast.AnnAssign) and (postponed or in_function):
            annotations.append(node.annotation)
        stack.extend(
            (child, in_function) for child in ast.iter_child_nodes(node))
    return frozenset(id(node) for node in annotations)
def _iter_calls_with_scope(tree: ast.Module, aliases: dict[str, str] | None = None,
                           *, _return_state: bool = False):
    if aliases is None:
        aliases = _parse_module_aliases(tree)
    events = tuple(node for node in iter_module_scope_stmts(tree)
                   if node.__class__ in _IMPORT_NODE_TYPES)
    shadows, conditional_shadows = _module_shadow_events(tree)
    event_aliases: dict[str, str] = {}
    for event in events:
        _collect_import_aliases(
            event, event_aliases, sink_relevant_only=False,
            visible_names=event_aliases)
    seed = {name: value for name, value in aliases.items()
            if name not in event_aliases}
    state = _TraversalState(
        aliases=_module_alias_timeline(seed, events, shadows, None),
        deferred_annotations=_deferred_annotation_ids(tree),
        module_import_events=events, module_shadow_events=shadows,
        module_scoped_shadows=_module_scoped_shadows(
            tree, conditional_shadows),
        module_alias_seed=seed,
        param_stack=[[]], assign_stack=[{}], alias_stack=[{}],
        scope_kinds=['module'])
    _stack: list = [tree]
    while _stack:
        _item = _stack.pop()
        if isinstance(_item, tuple):
            _apply_frame_marker(_item, state)
            continue
        _stack.extend(reversed(_handle_node(_item, state)))
    return state if _return_state else state.result
def _bind_clean_scope_name(name: str, state: _TraversalState) -> None:
    if not state.assign_stack:
        return
    _frame = state.assign_stack[-1]
    _alias_frame = state.alias_stack[-1] if state.alias_stack else {}
    _old_roots = _frame.get(name, _MISSING_BINDING)
    state.clean_binding_stack.append((
        name,
        list(_old_roots) if _old_roots is not _MISSING_BINDING else _MISSING_BINDING,
        _alias_frame.get(name, _MISSING_BINDING),
    ))
    _frame[name] = []
    _project_local_aliases(state, [name], _frame)
def _restore_clean_scope_name(name: str, state: _TraversalState) -> None:
    if not state.assign_stack:
        return
    if not state.clean_binding_stack:
        _log.warning("[D2] except 绑定 restore 与 bind 不配对（忽略）: %s", name)
        return
    _bound_name, _roots, _alias = state.clean_binding_stack.pop()
    if _bound_name != name:
        _log.warning("[D2] except 绑定恢复顺序异常（忽略）: %r != %r",
                     _bound_name, name)
        return
    _frame = state.assign_stack[-1]
    if _roots is _MISSING_BINDING:
        _frame.pop(name, None)
    else:
        _frame[name] = list(_roots)
    if state.alias_stack:
        _alias_frame = state.alias_stack[-1]
        if _alias is _MISSING_BINDING:
            _alias_frame.pop(name, None)
        else:
            _alias_frame[name] = _alias
def _apply_frame_marker(marker: tuple, state: _TraversalState) -> None:
    _kind = marker[0]
    if _kind == 'enter_if':
        _enter_if_branch(state)
        return
    if _kind == 'swap_if':
        _swap_if_branch(state)
        return
    if _kind == 'exit_if':
        _exit_if_branch(state)
        return
    if _kind == 'register_mutation':
        _register_mutating_call(marker[1], state.assign_stack,
                                state.param_stack, state.scope_kinds)
        return
    if _kind == 'bind_comprehension':
        _assign_deps_comprehension(marker[1], state)
        return
    if _kind == 'bind_definition':
        _bind_local_scope_name(marker[1], state)
        return
    if _kind == 'bind_deps':
        if state.assign_stack:
            _handler = _ASSIGN_DEPS_HANDLERS[marker[1].__class__]
            _handler(marker[1], state)
        return
    if _kind == 'bind_with_item':
        if state.assign_stack:
            _assign_deps_with_item(marker[1], state)
        return
    if _kind == 'bind_match_case':
        if state.assign_stack:
            _node, _case = marker[1]
            _assign_deps_match_case(_node, _case, state)
        return
    if _kind == 'bind_clean':
        _bind_clean_scope_name(marker[1], state)
        return
    if _kind == 'restore_clean':
        _restore_clean_scope_name(marker[1], state)
        return
    if _kind == 'enter_conditional':
        state.conditional_depth += 1
        return
    if _kind == 'exit_conditional':
        state.conditional_depth -= 1
        return
    if _kind in ("push", "push_class", "push_comprehension"):
        state.conditional_depth_stack.append(state.conditional_depth)
        state.conditional_depth = 0
        state.param_stack.append(marker[1])
        state.assign_stack.append({})
        state.alias_stack.append({})
        state.scope_kinds.append({
            "push": "function",
            "push_class": "class",
            "push_comprehension": "comprehension",
        }[_kind])
        return
    if _kind != 'pop':
        _log.warning("[D2] 未知帧标记（忽略）: %r", marker)
        return
    if not state.assign_stack:
        _log.warning("[D2] 帧标记 pop 与 push 不配对（忽略）")
        return
    state.param_stack.pop()
    state.assign_stack.pop()
    state.alias_stack.pop()
    state.scope_kinds.pop()
    state.conditional_depth = state.conditional_depth_stack.pop()
_CALLS_SCOPE_MEMO_LOCK = threading.Lock()
_CALLS_SCOPE_MEMO_CAP = 512
_SCOPE_FRAMES_MEMO: dict[int, tuple[ast.Module, tuple]] = {}
def memo_hit(memo: dict, key, tree):
    with _CALLS_SCOPE_MEMO_LOCK:
        hit = memo.get(key)
        if hit is not None and hit[0] is tree:
            return hit[1]
    return None
def memo_store(memo: dict, key, tree, value):
    with _CALLS_SCOPE_MEMO_LOCK:
        hit = memo.get(key)
        if hit is not None and hit[0] is tree:
            return hit[1]
        if len(memo) >= _CALLS_SCOPE_MEMO_CAP:
            memo.clear()
        memo[key] = (tree, value)
        return value
def memo_clear(*memos: dict) -> int:
    with _CALLS_SCOPE_MEMO_LOCK:
        total = sum(len(memo) for memo in memos)
        for memo in memos:
            memo.clear()
    return total
def _memoized_tree_value(memo: dict, path: str, tree: ast.Module, compute,
                         *, context: str = ""):
    key = (os.path.abspath(path), context)
    hit = memo_hit(memo, key, tree)
    if hit is not None:
        return hit
    value = compute()
    memo_store(memo, key, tree, value)
    return value
def _copy_call_entry(entry: tuple) -> tuple:
    node, params, assigns, aliases = entry
    return (
        node,
        list(params) if params is not None else None,
        ({name: list(roots) for name, roots in assigns.items()}
         if assigns is not None else None),
        dict(aliases) if aliases is not None else None,
    )
def _copy_call_entries(entries: list) -> list:
    return [_copy_call_entry(entry) for entry in entries]
_ALIASES_MEMO: dict[str, tuple[ast.Module, dict[str, str]]] = {}
def parse_module_aliases_cached(path: str, tree: ast.Module) -> dict[str, str]:
    if not isinstance(tree, ast.Module):
        return {}
    return dict(_memoized_tree_value(
        _ALIASES_MEMO, path, tree, lambda: _parse_module_aliases(tree)))
_CALLS_SCOPE_MEMO: dict[str, tuple[ast.Module, list]] = {}
def iter_calls_with_scope_cached(path: str, tree: ast.Module) -> list:
    if not isinstance(tree, ast.Module):
        return []
    return _copy_call_entries(_memoized_tree_value(
        _CALLS_SCOPE_MEMO, path, tree,
        lambda: _iter_calls_with_scope(
            tree, aliases=parse_module_aliases_cached(path, tree))))
_CALLS_BY_LINENO_MEMO: dict[str, tuple[ast.Module, dict[int, list]]] = {}
def calls_by_lineno_cached(path: str, tree: ast.Module) -> dict[int, list]:
    if not isinstance(tree, ast.Module):
        return {}
    def _index_by_line() -> dict[int, list]:
        by_line: dict[int, list] = {}
        for entry in iter_calls_with_scope_cached(path, tree):
            by_line.setdefault(getattr(entry[0], "lineno", -1), []).append(entry)
        return by_line
    return {line: _copy_call_entries(entries) for line, entries in
            _memoized_tree_value(
                _CALLS_BY_LINENO_MEMO, path, tree, _index_by_line).items()}
_MODULE_ASSIGNS_MEMO: dict[str, tuple[ast.Module, dict]] = {}
def _module_assigns_for_link_cached(path: str, tree: ast.Module) -> dict:
    if not isinstance(tree, ast.Module):
        return {}
    def _compute_module_assigns() -> dict:
        state = _iter_calls_with_scope(
            tree, aliases=parse_module_aliases_cached(path, tree),
            _return_state=True)
        return {name: list(roots)
                for name, roots in state.assign_stack[0].items()}
    return {name: list(roots) for name, roots in _memoized_tree_value(
        _MODULE_ASSIGNS_MEMO, path, tree, _compute_module_assigns).items()}
def iter_module_scope_stmts(tree: ast.Module):
    _stack = list(reversed(tree.body))
    while _stack:
        node = _stack.pop()
        yield node
        _stack.extend(reversed(_module_scope_children(node)))
_BLOCK_BODY_FIELDS: dict[type, tuple[str, ...]] = {
    ast.If: ("body", "orelse"),
    ast.For: ("body", "orelse"),
    ast.AsyncFor: ("body", "orelse"),
    ast.While: ("body", "orelse"),
    ast.With: ("body",),
    ast.AsyncWith: ("body",),
}
def _module_scope_children(node: ast.AST) -> list:
    if isinstance(node, _TRY_BLOCK_TYPES):
        return _try_scope_children(node)
    if _is_match_node(node):
        return [stmt for _case in node.cases for stmt in _case.body]
    fields = _BLOCK_BODY_FIELDS.get(node.__class__)
    if fields is None:
        return []
    _children: list = []
    for field_name in fields:
        _children.extend(getattr(node, field_name))
    return _children
def _end_position(node: ast.AST) -> tuple[int, int]:
    _line = getattr(node, "end_lineno", None)
    _col = getattr(node, "end_col_offset", None)
    return (_line if _line is not None else node.lineno,
            _col if _col is not None else node.col_offset)
def _module_shadow_events_for_stmt(stmt: ast.AST) -> list[tuple]:
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef)):
        return [(*_end_position(stmt), (stmt.name,))]
    if isinstance(stmt, ast.AnnAssign):
        if stmt.value is None:
            return []
        _names = tuple(iter_unpack_target_names(stmt.target))
        return [(*_end_position(stmt), _names)] if _names else []
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        _names = tuple(iter_unpack_target_names(stmt.target))
        return [(*_end_position(stmt.iter), _names)] if _names else []
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        _events: list[tuple] = []
        for _item in stmt.items:
            if _item.optional_vars is None:
                continue
            _names = tuple(iter_unpack_target_names(_item.optional_vars))
            if _names:
                _events.append((*_end_position(_item.context_expr), _names))
        return _events
    if isinstance(stmt, (ast.Assign, ast.AugAssign)):
        _names = tuple(_name for _target in _assign_targets(stmt)
                       for _name in iter_unpack_target_names(_target))
        return [(*_end_position(stmt), _names)] if _names else []
    return []
def _iter_module_walrus_nodes(tree: ast.Module):
    stack: list[ast.AST] = [tree]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.NamedExpr):
            yield node
        if node.__class__ in _DEF_SITE_NODE_TYPES:
            children = fn_def_site_exprs(node)
        elif isinstance(node, ast.ClassDef):
            children = _class_def_site_exprs(node)
        else:
            children = list(ast.iter_child_nodes(node))
        stack.extend(reversed(children))
def _block_end_position(statements: list) -> tuple[int, int] | None:
    return _end_position(statements[-1]) if statements else None
def _conditional_binding_end(node: ast.AST, parents: dict) -> tuple | None:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return _block_end_position(node.body)
    current = node
    while True:
        parent = parents.get(current)
        if parent is None or isinstance(
                parent, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef,
                         ast.ClassDef, ast.Lambda)):
            return None
        if isinstance(parent, ast.If):
            if current in parent.body:
                return _block_end_position(parent.body)
            if current in parent.orelse:
                return _block_end_position(parent.orelse)
        if isinstance(parent, ast.IfExp):
            if current is parent.body:
                return _end_position(parent.body)
            if current is parent.orelse:
                return _end_position(parent.orelse)
        if isinstance(parent, (ast.For, ast.AsyncFor, ast.While)):
            if current in parent.body:
                return _block_end_position(parent.body)
            if current in parent.orelse:
                return _block_end_position(parent.orelse)
        if isinstance(parent, _TRY_BLOCK_TYPES):
            for field_name in ('body', 'orelse', 'finalbody'):
                statements = getattr(parent, field_name)
                if current in statements:
                    return _block_end_position(statements)
        if isinstance(parent, ast.ExceptHandler) and current in parent.body:
            return _block_end_position(parent.body)
        if (_MATCH_CASE_TYPE is not None
                and isinstance(parent, _MATCH_CASE_TYPE)
                and current in parent.body):
            return _block_end_position(parent.body)
        current = parent
def _module_shadow_events(tree: ast.Module) -> tuple:
    _out: list = []
    _scoped: list = []
    parents = parent_map(tree)
    def _record(node: ast.AST, events: list) -> None:
        conditional_end = _conditional_binding_end(node, parents)
        if conditional_end is None:
            _out.extend(events)
            return
        for line, col, names in events:
            start = (line, col)
            if start <= conditional_end:
                _scoped.extend((start, conditional_end, name)
                               for name in names)
    for node in iter_module_scope_stmts(tree):
        if node.__class__ not in _IMPORT_NODE_TYPES:
            _record(node, _module_shadow_events_for_stmt(node))
    deferred = _deferred_annotation_ids(tree)
    for node in _iter_module_walrus_nodes(tree):
        if id(node) not in deferred:
            _record(node, [(*_end_position(node.value), (node.target.id,))])
    _out.sort(key=lambda event: event[:2])
    _scoped.sort()
    return tuple(_out), tuple(_scoped)
def _except_binding_position(handler) -> tuple[int, int]:
    if handler.type is not None:
        return _end_position(handler.type)
    return handler.lineno, handler.col_offset
def _module_scoped_shadows(tree: ast.Module, conditional: tuple) -> tuple:
    events: list = list(conditional)
    for node in iter_module_scope_stmts(tree):
        if isinstance(node, _TRY_BLOCK_TYPES):
            for handler in node.handlers:
                if handler.name:
                    start = _except_binding_position(handler)
                    events.append((start, _end_position(handler), handler.name))
        elif _is_match_node(node):
            for case in node.cases:
                tail = (case.body[-1] if case.body
                        else case.guard or case.pattern)
                start = (case.pattern.lineno, case.pattern.col_offset)
                end = _end_position(tail)
                events.extend((start, end, name) for name in
                              iter_pattern_capture_names(case.pattern))
    return tuple(sorted(events))
def _module_alias_timeline(seed: dict, events: tuple, shadows: tuple,
                           at: tuple[int, int] | None) -> dict:
    aliases = dict(seed)
    _i = _j = 0
    while _i < len(events) or _j < len(shadows):
        _import_key = ((events[_i].lineno, events[_i].col_offset)
                       if _i < len(events) else None)
        _shadow_key = ((shadows[_j][0], shadows[_j][1])
                       if _j < len(shadows) else None)
        if _shadow_key is not None and (_import_key is None
                                        or _shadow_key <= _import_key):
            if at is not None and _shadow_key > at:
                return aliases
            for _name in shadows[_j][2]:
                if _name in aliases or _name in _MODULE_SHADOW_RELEVANT:
                    aliases[_name] = ""
            _j += 1
            continue
        if at is not None and _import_key > at:
            return aliases
        _collect_import_aliases(
            events[_i], aliases, sink_relevant_only=False,
            visible_names=aliases)
        _i += 1
    return aliases
def _try_scope_children(node) -> list:
    _children = [*node.body]
    for _handler in node.handlers:
        _children.extend(_handler.body)
    _children.extend(node.orelse)
    _children.extend(node.finalbody)
    return _children
def _arg_annotation_exprs(args) -> list:
    _exprs = [p.annotation for p in iter_params(args)
              if p.annotation is not None]
    for _var in (args.vararg, args.kwarg):
        if _var is not None and _var.annotation is not None:
            _exprs.append(_var.annotation)
    return _exprs
def fn_def_site_exprs(fn_def) -> list:
    if not isinstance(fn_def, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
        return []
    _a = fn_def.args
    _defaults = [*_a.defaults,
                 *(_d for _d in _a.kw_defaults if _d is not None)]
    if isinstance(fn_def, ast.Lambda):
        return _defaults
    _exprs: list = [*fn_def.decorator_list, *_defaults]
    _exprs.extend(_arg_annotation_exprs(_a))
    if fn_def.returns is not None:
        _exprs.append(fn_def.returns)
    _exprs.extend(getattr(fn_def, "type_params", ()) or ())
    return _exprs
def function_param_names(fn: ast.AST) -> list[str]:
    a = getattr(fn, "args", None)
    if a is None:
        return []
    names = [x.arg for x in list(a.posonlyargs) + list(a.args)]
    if a.vararg:
        names.append(a.vararg.arg)
    names.extend(x.arg for x in a.kwonlyargs)
    if a.kwarg:
        names.append(a.kwarg.arg)
    return names
def clear_call_scan_memos() -> int:
    return memo_clear(_CALLS_SCOPE_MEMO, _ALIASES_MEMO, _CALLS_BY_LINENO_MEMO,
                      _SCOPE_FRAMES_MEMO, _MODULE_ASSIGNS_MEMO)
@dataclass
class CrossFileTaintReport:
    flows: list = field(default_factory=list)
    summary: dict[str, Any] = field(default_factory=dict)
def _tree_has_pytest_collector(tree: ast.Module) -> bool:
    return next(iter_collectable_test_functions(tree), None) is not None
def _is_pytest_test_file(fpath: str, cache=None) -> bool:
    tree = _parse_file_tree(fpath, cache, "test 文件判定", quiet=True)
    if tree is None:
        return False
    return _tree_has_pytest_collector(tree)
def _parse_file_text(fpath: str, context: str,
                     quiet: bool) -> ast.Module | None:
    _source, tree = parse_py_file(fpath, quiet=quiet)
    if tree is None:
        log = _log.debug if quiet else _log.warning
        log("[CrossFileTaint] %s失败，跳过 %s（共享解析通道已降级）",
            context, fpath)
    return tree
def _cached_probe_tree(fpath: str, cache,
                       context: str) -> ast.Module | None:
    if cache is None:
        return None
    try:
        return cache.get_ast(fpath)
    except Exception as _e:  
        _log.debug("[D2] cache.get_ast 异常，%s降级文件解析: %s (%s)",
                   context, fpath, _e)
        return None
_D2_TAINT_SOURCE_CALLS = frozenset({
    "input", "raw_input", "builtins.input", "builtins.raw_input",
    "os.getenv", "os.environ.get"})
_D2_TAINT_SOURCE_ATTRS = frozenset({
    "sys.argv", "sys.stdin", "os.environ",
    "request.args", "request.form", "request.files",
    "request.values", "request.json", "request.data",
    "flask.request.args", "flask.request.form", "flask.request.files",
})
def _d2_resolve_head(name: str, import_fims: dict | None) -> str:
    if import_fims is not None and name:
        _head = name.split(".", 1)[0]
        if _head in import_fims:
            _mapped = import_fims[_head]
            return _mapped + name[len(_head):] if _mapped else ""
    return name
def _d2_taint_call_hit(name: str, known_funcs: dict):
    if not name:
        return None
    if name in known_funcs:
        return known_funcs[name]
    if name in _D2_TAINT_SOURCE_CALLS:
        return name
    _base = name.rsplit(".", 1)[0] if "." in name else ""
    if _base in _D2_TAINT_SOURCE_ATTRS:
        return _base
    return None
def _d2_call_expr_source(sub: ast.Call, known_funcs: dict,
                         import_fims: dict | None):
    _raw = dotted_name(sub.func)
    _resolved = _d2_resolve_head(_raw, import_fims)
    return _d2_taint_call_hit(_resolved, known_funcs)
def _d2_attr_base_source(node: ast.AST, import_fims: dict | None) -> str:
    _resolved = _d2_resolve_head(dotted_name(node), import_fims)
    return _resolved if _resolved in _D2_TAINT_SOURCE_ATTRS else ""
_LOCAL_TAINT_FALLBACK = "local_taint"
def _local_taint_origin(local_taint, name: str) -> str:
    if isinstance(local_taint, dict):
        origin = local_taint.get(name)
        return origin if isinstance(origin, str) else ""
    return _LOCAL_TAINT_FALLBACK if name in local_taint else ""
def _node_taint_source(sub: ast.AST, local_taint,
                       known_funcs: dict, import_fims: dict | None) -> str:
    if isinstance(sub, ast.Call):
        return _d2_call_expr_source(sub, known_funcs, import_fims) or ""
    if isinstance(sub, ast.Attribute):
        return _d2_attr_base_source(sub, import_fims)
    if isinstance(sub, ast.Subscript):
        return _d2_attr_base_source(sub.value, import_fims)
    if isinstance(sub, ast.Name):
        return _local_taint_origin(local_taint, sub.id)
    return ""
def _iter_value_taint_nodes(expr: ast.AST):
    stack = [(expr, frozenset())]
    while stack:
        node, bound = stack.pop()
        if isinstance(node, ast.Lambda):
            continue
        if (isinstance(node, ast.Name)
                and (not isinstance(node.ctx, ast.Load) or node.id in bound)):
            continue
        yield node
        if isinstance(node, _COMP_CONTAINER_TYPES):
            local = bound
            children = []
            for generator in node.generators:
                children.append((generator.iter, local))
                local = local | frozenset(
                    iter_unpack_target_names(generator.target))
                children.extend((test, local) for test in generator.ifs)
            values = ((node.key, node.value)
                      if isinstance(node, ast.DictComp) else (node.elt,))
            children.extend((item, local) for item in values)
        else:
            children = [(child, bound)
                        for child in ast.iter_child_nodes(node)]
        stack.extend(reversed(children))
def d2_expr_taint_source(expr: ast.AST, local_taint,
                          known_funcs: dict, import_fims: dict | None = None) -> str:
    for sub in _iter_value_taint_nodes(expr):
        _hit = _node_taint_source(sub, local_taint, known_funcs, import_fims)
        if _hit:
            return _hit
    return ""
_ASSIGN_FORM_TYPES = (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.NamedExpr)
def _is_taint_assign_stmt(stmt) -> bool:
    if not isinstance(stmt, _ASSIGN_FORM_TYPES):
        return False
    return not (isinstance(stmt, ast.AnnAssign) and stmt.value is None)
def _is_taint_return_stmt(stmt) -> bool:
    return isinstance(stmt, ast.Return) and stmt.value is not None
def _fn_taint_statements(fn_node: ast.AST) -> tuple:
    _assign_stmts: list = []
    _return_stmts: list = []
    for stmt in iter_own_nodes(fn_node):
        if _is_taint_assign_stmt(stmt):
            _assign_stmts.append(stmt)
        elif _is_taint_return_stmt(stmt):
            _return_stmts.append(stmt)
    return _assign_stmts, _return_stmts
def _assign_targets(stmt) -> list:
    return stmt.targets if isinstance(stmt, ast.Assign) else [stmt.target]
def _direct_taint_source_plan(target: ast.AST, value: ast.AST,
                              local_taint: dict, known: dict,
                              fims: dict) -> dict[str, str] | None:
    if isinstance(target, (ast.Tuple, ast.List)):
        if (not isinstance(value, (ast.Tuple, ast.List))
                or len(target.elts) != len(value.elts)):
            return None
        plan: dict[str, str] = {}
        for target_item, value_item in zip(
                target.elts, value.elts, strict=True):
            item_plan = _direct_taint_source_plan(
                target_item, value_item, local_taint, known, fims)
            if item_plan is None:
                return None
            plan.update(item_plan)
        return plan
    source = d2_expr_taint_source(value, local_taint, known, fims)
    return {name: source for name in iter_unpack_target_names(target)}
def _assignment_taint_sources(stmt, local_taint: dict, known: dict,
                              fims: dict) -> dict[str, str]:
    sources: dict[str, str] = {}
    for target in _assign_targets(stmt):
        plan = _direct_taint_source_plan(
            target, stmt.value, local_taint, known, fims)
        if plan is None:
            source = d2_expr_taint_source(
                stmt.value, local_taint, known, fims)
            plan = {name: source
                    for name in iter_unpack_target_names(target)}
        sources.update(plan)
    return sources
def _merge_taint_source_map(sources: dict[str, str], local_taint: dict, *,
                            overwrite: bool) -> bool:
    added = False
    for name, source in sources.items():
        if not source or (not overwrite and name in local_taint):
            continue
        if local_taint.get(name) != source:
            local_taint[name] = source
            added = True
    return added
def _propagate_local_taint(assign_stmts: list, known: dict, fims: dict) -> dict:
    local_taint: dict = {}
    _propagated = True
    while _propagated:
        _propagated = False
        for stmt in assign_stmts:
            if _propagate_stmt(stmt, local_taint, known, fims):
                _propagated = True
    return local_taint
def _propagate_stmt(stmt, local_taint: dict, known: dict, fims: dict) -> bool:
    sources = _assignment_taint_sources(stmt, local_taint, known, fims)
    return _merge_taint_source_map(sources, local_taint, overwrite=False)
def _return_taint_source(return_stmts: list, local_taint,
                         known: dict, fims: dict) -> str:
    for stmt in return_stmts:
        ret_source = d2_expr_taint_source(
            stmt.value, local_taint, known, fims)
        if ret_source:
            return ret_source
    return ""
def _is_straight_line_taint_fn(node) -> bool:
    for stmt in node.body:
        if isinstance(stmt, (*_ASSIGN_FORM_TYPES, ast.Return, ast.Pass)):
            continue
        if isinstance(stmt, ast.Expr) and not any(
                isinstance(child, ast.NamedExpr)
                for child in walk_nodes(stmt.value)):
            continue
        return False
    return True
def _clear_assign_targets(stmt, local_taint: dict) -> None:
    for target in _assign_targets(stmt):
        for name in iter_unpack_target_names(target):
            local_taint.pop(name, None)
def _sequential_fn_taint_source(node, known: dict, fims: dict) -> str:
    local_taint: dict = {}
    for stmt in node.body:
        if isinstance(stmt, ast.Return):
            if stmt.value is None:
                return ""
            return d2_expr_taint_source(
                stmt.value, local_taint, known, fims)
        if not _is_taint_assign_stmt(stmt):
            continue
        sources = _assignment_taint_sources(stmt, local_taint, known, fims)
        if not isinstance(stmt, ast.AugAssign):
            _clear_assign_targets(stmt, local_taint)
        _merge_taint_source_map(sources, local_taint, overwrite=True)
    return ""
def _fn_taint_round(node, known: dict, fims: dict) -> str:
    if _is_straight_line_taint_fn(node):
        return _sequential_fn_taint_source(node, known, fims)
    _assign_stmts, _return_stmts = _fn_taint_statements(node)
    local_taint = _propagate_local_taint(_assign_stmts, known, fims)
    return _return_taint_source(_return_stmts, local_taint, known, fims)
def _function_import_maps(tree: ast.Module,
                          file_name: str | None = None) -> dict[int, dict]:
    mods, fims = _parse_module_imports(tree, file_name)
    frames, parents = _scope_frames_cached(tree, file_name)
    memo: dict = {}
    import_maps = {}
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        scoped_mods, scoped_fims = _merged_import_maps(
            id(node), mods, fims, frames, parents, memo)
        import_maps[id(node)] = {**scoped_mods, **scoped_fims}
    return import_maps
def _record_scope_binding(bindings: dict, scope, name: str,
                          position: tuple[int, int], definition) -> None:
    if not name:
        return
    table = bindings.setdefault(scope, {})
    previous = table.get(name)
    if previous is None or position >= previous[0]:
        table[name] = position, definition
def _record_stmt_shadow_bindings(node: ast.AST, scope,
                                 bindings: dict) -> None:
    if isinstance(node, (ast.Assign, ast.AugAssign)):
        events = [(_end_position(node), tuple(
            name for target in _assign_targets(node)
            for name in iter_unpack_target_names(target)))]
    elif isinstance(node, ast.AnnAssign):
        events = ([] if node.value is None else
                  [(_end_position(node),
                    tuple(iter_unpack_target_names(node.target)))])
    elif isinstance(node, (ast.For, ast.AsyncFor)):
        events = [(_end_position(node.iter),
                   tuple(iter_unpack_target_names(node.target)))]
    elif isinstance(node, (ast.With, ast.AsyncWith)):
        events = [(_end_position(item.context_expr),
                   tuple(iter_unpack_target_names(item.optional_vars)))
                  for item in node.items if item.optional_vars is not None]
    elif isinstance(node, ast.NamedExpr):
        events = [(_end_position(node.value), (node.target.id,))]
    elif _is_match_node(node):
        events = [(_end_position(node.subject), tuple(match_capture_names(node)))]
    elif isinstance(node, ast.Import):
        events = [(_end_position(node), tuple(
            alias.asname or alias.name.split(".", 1)[0]
            for alias in node.names))]
    elif isinstance(node, ast.ImportFrom):
        events = [(_end_position(node), tuple(
            alias.asname or alias.name for alias in node.names
            if alias.name != "*"))]
    elif isinstance(node, ast.ExceptHandler) and node.name:
        events = [(_except_binding_position(node), (node.name,))]
    else:
        return
    for position, names in events:
        for name in names:
            _record_scope_binding(bindings, scope, name, position, node)
def _scope_binding_children(node: ast.AST, scope) -> list:
    if isinstance(node, ast.Lambda):
        return ([(child, scope) for child in fn_def_site_exprs(node)]
                + [(node.body, id(node))])
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return ([(child, scope) for child in fn_def_site_exprs(node)]
                + [(stmt, id(node)) for stmt in node.body])
    if isinstance(node, ast.ClassDef):
        return ([(child, scope) for child in _class_def_site_exprs(node)]
                + [(stmt, id(node)) for stmt in node.body])
    return [(child, scope) for child in ast.iter_child_nodes(node)]
def _function_scope_index(tree: ast.Module) -> tuple:
    parents: dict[int, int | None] = {}
    bindings: dict[int | None, dict] = {}
    class_scopes: set[int] = set()
    stack = [(tree, None)]
    while stack:
        node, scope = stack.pop()
        next_scope = scope
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            parents[id(node)] = scope
            _record_scope_binding(
                bindings, scope, node.name, _end_position(node), node)
            next_scope = id(node)
            for name in function_param_names(node):
                _record_scope_binding(
                    bindings, next_scope, name,
                    (node.lineno, node.col_offset), None)
        elif isinstance(node, ast.ClassDef):
            parents[id(node)] = scope
            class_scopes.add(id(node))
            _record_scope_binding(
                bindings, scope, node.name, _end_position(node), None)
            next_scope = id(node)
        elif isinstance(node, ast.Lambda):
            parents[id(node)] = scope
            next_scope = id(node)
            for name in function_param_names(node):
                _record_scope_binding(
                    bindings, next_scope, name,
                    (node.lineno, node.col_offset), None)
        else:
            _record_stmt_shadow_bindings(node, scope, bindings)
        stack.extend(reversed(_scope_binding_children(node, next_scope)))
    return parents, bindings, class_scopes
def _visible_function_bindings(node: ast.AST, scope_index: tuple) -> dict:
    parents, bindings, class_scopes = scope_index
    visible: dict[str, ast.AST | None] = {}
    scope = id(node)
    while scope is not None:
        if scope not in class_scopes:
            for name, (_position, definition) in bindings.get(scope, {}).items():
                visible.setdefault(name, definition)
        scope = parents.get(scope)
    for name, (_position, definition) in bindings.get(None, {}).items():
        visible.setdefault(name, definition)
    return visible
def _taint_assignment_alias(node: ast.AST, imports: dict,
                            visible: dict) -> str:
    if not isinstance(node, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
        return ""
    raw = dotted_name(node.value)
    head = raw.split(".", 1)[0] if raw else ""
    if head in imports:
        return _d2_resolve_head(raw, imports)
    if raw in {"input", "raw_input"} and raw not in visible:
        return raw
    return ""
def _effective_taint_import_map(visible: dict, base: dict) -> dict:
    imports = dict(base)
    assignments: list[tuple[str, ast.AST]] = []
    for name, definition in visible.items():
        if isinstance(definition, (ast.FunctionDef, ast.AsyncFunctionDef)):
            imports.pop(name, None)
        elif not isinstance(definition, (ast.Import, ast.ImportFrom)):
            imports[name] = ""
        if isinstance(definition, (ast.Assign, ast.AnnAssign, ast.NamedExpr)):
            assignments.append((name, definition))
    for _round in range(len(assignments)):
        changed = False
        for name, definition in assignments:
            if imports.get(name):
                continue
            resolved = _taint_assignment_alias(definition, imports, visible)
            if resolved:
                imports[name] = resolved
                changed = True
        if not changed:
            break
    return imports
def _collect_taint_round(functions: list, funcs: dict,
                         import_maps: dict[int, dict],
                         scope_index: tuple) -> bool:
    changed = False
    for node in functions:
        if id(node) in funcs:
            continue
        visible = _visible_function_bindings(node, scope_index)
        known = {
            name: (funcs[id(definition)][0]
                   if definition is not None and id(definition) in funcs
                   else "")
            for name, definition in visible.items()
        }
        ret_source = _fn_taint_round(
            node, known, _effective_taint_import_map(
                visible, import_maps.get(id(node), {})))
        if ret_source:
            funcs[id(node)] = (ret_source, node.lineno)
            changed = True
    return changed
def _collect_d2_taint_source_funcs(tree: ast.Module,
                                   file_name: str | None = None) -> dict:
    funcs: dict = {}
    functions = [node for node in walk_nodes(tree)
                 if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))]
    scope_index = _function_scope_index(tree)
    import_maps = _function_import_maps(tree, file_name)
    for _round in range(len(functions) + 1):
        if not _collect_taint_round(
                functions, funcs, import_maps, scope_index):
            break
    result: dict = {}
    for name, (_position, node) in scope_index[1].get(None, {}).items():
        if node is None:
            continue
        summary = funcs.get(id(node))
        if summary is not None:
            result[name] = summary
    return result
_TAINT_SOURCE_FUNCS_MEMO: dict[str, tuple[ast.Module, dict]] = {}
def clear_flow_memos() -> int:
    return memo_clear(_TAINT_SOURCE_FUNCS_MEMO)
def collect_d2_taint_source_cached(path: str, tree: ast.Module) -> dict:
    if not isinstance(tree, ast.Module):
        return {}
    return dict(_memoized_tree_value(
        _TAINT_SOURCE_FUNCS_MEMO, path, tree,
        lambda: _collect_d2_taint_source_funcs(tree)))
def _note_import_aliases(node: ast.Import, mods: dict) -> None:
    for a in node.names:
        if a.asname:
            mods[a.asname] = a.name
            continue
        _root = a.name.split(".", 1)[0]
        mods[_root] = _root
def _resolved_import_module(node: ast.ImportFrom,
                            file_name: str | None) -> str | None:
    if not node.level:
        return node.module
    if not file_name:
        return None
    package = os.path.dirname(os.path.normpath(file_name))
    parts = [] if package in {"", "."} else package.split(os.sep)
    ascend = node.level - 1
    if ascend > len(parts):
        return None
    if ascend:
        parts = parts[:-ascend]
    if node.module:
        parts.extend(node.module.split("."))
    return ".".join(parts) or None


def _note_from_import_aliases(node: ast.ImportFrom, fims: dict,
                              file_name: str | None = None) -> None:
    module = _resolved_import_module(node, file_name)
    if not module:
        return
    for a in node.names:
        if a.name == "*":
            continue
        fims[a.asname or a.name] = f"{module}.{a.name}"
def _note_import_into(node: ast.AST, mods: dict, fims: dict,
                      file_name: str | None = None) -> None:
    if isinstance(node, ast.Import):
        _note_import_aliases(node, mods)
        for alias in node.names:
            bound = alias.asname or alias.name.split(".", 1)[0]
            fims.pop(bound, None)
    elif isinstance(node, ast.ImportFrom):
        _note_from_import_aliases(node, fims, file_name)
        for alias in node.names:
            if alias.name != "*":
                mods.pop(alias.asname or alias.name, None)
def _parse_module_imports(tree: ast.Module,
                          file_name: str | None = None) -> tuple:
    mods: dict = {}
    fims: dict = {}
    for node in iter_module_scope_stmts(tree):
        _note_import_into(node, mods, fims, file_name)
    return mods, fims
def _parse_general_imports(tree: ast.Module) -> tuple:
    mods: dict = {}
    fims: dict = {}
    for node in walk_nodes(tree):
        _note_import_into(node, mods, fims)
    return mods, fims
def alias_resolve_map(tree: ast.Module) -> dict:
    if not isinstance(tree, ast.Module):
        return {}
    _mods, _fims = _parse_general_imports(tree)
    return {**_mods, **_fims}
def _dotted_module_name(node: ast.AST, mods: dict, fims: dict) -> str:
    if isinstance(node, ast.Name):
        return fims.get(node.id) or mods.get(node.id, "")
    if isinstance(node, ast.Attribute):
        _head = _dotted_module_name(node.value, mods, fims)
        return f"{_head}.{node.attr}" if _head else ""
    return ""
def _call_assign_target_func(func, mods: dict, fims: dict) -> tuple:
    if isinstance(func, ast.Attribute):
        return _dotted_module_name(func.value, mods, fims), func.attr
    if isinstance(func, ast.Name):
        _mapped = fims.get(func.id, "")
        if "." in _mapped:
            return tuple(_mapped.rsplit(".", 1))
    return ("", "")
def _register_call_assign(node, fn_id, mods: dict, fims: dict,
                          out: dict) -> None:
    if not isinstance(node, _ASSIGN_FORM_TYPES):
        return
    _value = node.value
    while isinstance(_value, ast.Await):
        _value = _value.value
    if not isinstance(_value, ast.Call):
        return
    _targets = _assign_targets(node)
    module, fname = _call_assign_target_func(_value.func, mods, fims)
    if module and fname:
        for t in _targets:
            if isinstance(t, ast.Name):
                out.setdefault(t.id, []).append(
                    (module, fname, node.lineno, fn_id))
def _maybe_register_call_assign(node: ast.AST, fn_id, mods: dict,
                                fims: dict, out: dict) -> None:
    if isinstance(node, _ASSIGN_FORM_TYPES):
        _register_call_assign(node, fn_id, mods, fims, out)
def _fn_scope_succs(_node, _fid, _succ: list) -> None:
    for _ext in fn_def_site_exprs(_node):
        _succ.append((_ext, _fid))
    for _stmt in _node.body:
        _succ.append((_stmt, id(_node)))
def _class_body_succs(_cls: ast.ClassDef, _succ: list) -> list:
    _nested: list = []
    for _stmt in _cls.body:
        if isinstance(_stmt, (ast.FunctionDef,
                              ast.AsyncFunctionDef)):
            for _m in _stmt.body:
                _succ.append((_m, id(_stmt)))
        elif isinstance(_stmt, ast.ClassDef):
            _nested.append(_stmt)
    return _nested
def _class_scope_succs(_node, _fid, _succ: list) -> None:
    _cb_stack = [_node]
    while _cb_stack:
        _cls = _cb_stack.pop()
        for _ext in (*_cls.decorator_list, *_cls.bases,
                     *_cls.keywords):
            _succ.append((_ext, _fid))
        _cb_stack.extend(_class_body_succs(_cls, _succ))
def _lambda_scope_succs(_node, _fid, _succ: list) -> None:
    for _ext in fn_def_site_exprs(_node):
        _succ.append((_ext, _fid))
    _succ.append((_node.body, id(_node)))
def _call_assign_succs(node, fid) -> list:
    _succ: list = []
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        _fn_scope_succs(node, fid, _succ)
    elif isinstance(node, ast.ClassDef):
        _class_scope_succs(node, fid, _succ)
    elif isinstance(node, ast.Lambda):
        _lambda_scope_succs(node, fid, _succ)
    else:
        _succ.extend((child, fid) for child in ast.iter_child_nodes(node))
    return _succ
def _own_import_frame(scope: ast.AST,
                      file_name: str | None = None) -> tuple:
    mods: dict = {}
    fims: dict = {}
    for node in iter_own_nodes(scope):
        _note_import_into(node, mods, fims, file_name)
    return mods, fims
def _scope_frames_cached(tree: ast.Module,
                         file_name: str | None = None) -> tuple:
    key = (id(tree), os.path.normcase(os.path.normpath(file_name or "")))
    hit = memo_hit(_SCOPE_FRAMES_MEMO, key, tree)
    if hit is not None:
        return hit
    return memo_store(
        _SCOPE_FRAMES_MEMO, key, tree,
        _scope_import_frames(tree, file_name))
def _scope_import_frames(tree: ast.Module,
                         file_name: str | None = None) -> tuple:
    _frames: dict = {}
    _parents: dict = {}
    _stack: list = [(tree, None)]
    while _stack:
        node, fid = _stack.pop()
        _fid = fid
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            if fid is not None:
                _parents[id(node)] = fid
            _frames[id(node)] = _own_import_frame(node, file_name)
            _fid = id(node)
        for _child in ast.iter_child_nodes(node):
            _stack.append((_child, _fid))
    return _frames, _parents
def _merged_import_maps(fid, mods: dict, fims: dict, frames: dict,
                        parents: dict, memo: dict) -> tuple:
    if fid is None:
        return mods, fims
    hit = memo.get(fid)
    if hit is not None:
        return hit
    chain: list = []
    cur = fid
    while cur is not None:
        frame = frames.get(cur)
        if frame is not None:
            chain.append(frame)
        cur = parents.get(cur)
    merged_mods = dict(mods)
    merged_fims = dict(fims)
    for frame_mods, frame_fims in reversed(chain):
        for name in frame_mods:
            merged_fims.pop(name, None)
        for name in frame_fims:
            merged_mods.pop(name, None)
        merged_mods.update(frame_mods)
        merged_fims.update(frame_fims)
    merged = (merged_mods, merged_fims)
    memo[fid] = merged
    return merged
def _collect_call_assigns(tree: ast.Module, mods: dict, fims: dict,
                          file_name: str | None = None) -> dict:
    out: dict = {}
    deferred_annotations = _deferred_annotation_ids(tree)
    _frames, _parents = _scope_frames_cached(tree, file_name)
    _memo: dict = {}
    _work: list = [(tree, None)]
    while _work:
        _node, _fid = _work.pop()
        if id(_node) in deferred_annotations:
            continue
        _scoped_mods, _scoped_fims = _merged_import_maps(
            _fid, mods, fims, _frames, _parents, _memo)
        _maybe_register_call_assign(_node, _fid, _scoped_mods, _scoped_fims, out)
        _work.extend(reversed(_call_assign_succs(_node, _fid)))
    return out
POWERSHELL_PROGRAMS = frozenset({
    'powershell', 'powershell.exe', 'pwsh', 'pwsh.exe',
})
_INTERPRETER_VALUE_OPTION_FAMILIES = (
    (frozenset({'python', 'python.exe', 'python3', 'python3.exe', 'py', 'py.exe'}),
     frozenset({'-X', '-w', '--check-hash-based-pycs'})),
    (frozenset({'sh', 'bash', 'zsh', 'dash', 'ash', 'ksh', 'csh', 'tcsh',
                'sh.exe', 'bash.exe', 'zsh.exe', 'dash.exe', 'ksh.exe'}),
     frozenset({'-o', '--init-file', '--rcfile'})),
    (POWERSHELL_PROGRAMS,
     frozenset({'-executionpolicy', '-ep', '-inputformat', '-outputformat',
                '-configurationname', '-workingdirectory', '-windowstyle',
                '-psconsolefile', '-settingsfile', '-custompipename'})),
    (frozenset({'node', 'node.exe', 'nodejs', 'nodejs.exe'}),
     frozenset({'-r', '--require', '--import', '--loader',
                '--experimental-loader', '--input-type'})),
    (frozenset({'ruby', 'ruby.exe'}),
     frozenset({'-r', '--require', '-I', '--include'})),
    (frozenset({'perl', 'perl.exe'}),
     frozenset({'-I', '-m'})),
    (frozenset({'php', 'php.exe'}),
     frozenset({'-d'})),
)
def interpreter_option_consumes_value(program: str, token: str) -> bool:
    normalized = token.strip()
    folded = normalized.lower()
    return any(
        program in programs
        and (normalized in options or folded in options)
        for programs, options in _INTERPRETER_VALUE_OPTION_FAMILIES)
def _shell_value_open(value: ast.AST) -> bool:
    return not isinstance(value, ast.Constant) or bool(value.value)
def shell_interpretation_open(node: ast.Call) -> bool:
    if not isinstance(node, ast.Call):
        return False
    if any(isinstance(arg, ast.Starred) for arg in node.args[:9]):
        return True
    if len(node.args) > 8 and _shell_value_open(node.args[8]):
        return True
    for k in node.keywords:
        if k.arg is None:
            return True
        if k.arg == "shell" and _shell_value_open(k.value):
            return True
    return False
def sink_first_arg(node: ast.Call) -> ast.AST | None:
    if not isinstance(node, ast.Call):
        return None
    if node.args:
        return node.args[0]
    for _k in node.keywords:
        if _k.arg in {"args", "cmd"}:
            return _k.value
    return None
def _subprocess_sink(node: ast.Call, params: list[str] | None,
                     assigns: dict[str, list[str]] | None,
                     allow_untainted: bool) -> str:
    if (allow_untainted or shell_interpretation_open(node)
            or expr_reaches_param(sink_first_arg(node), params, assigns)):
        return "subprocess"
    return ""
def _sink_from_name_call(func: ast.Name, node: ast.Call,
                         params: list[str] | None,
                         assigns: dict[str, list[str]] | None,
                         aliases: dict[str, str] | None,
                         allow_untainted_subprocess: bool) -> str:
    _bound = aliases if aliases is not None else {}
    if func.id in SINK_BARE_NAMES and func.id not in _bound:
        return func.id
    for _fa in _alias_options(_bound.get(func.id, "")):
        _route = ALIAS_SINK_ROUTES.get(_fa)
        if _route is not None:
            return _route
        if _fa in _SUBPROCESS_EXEC_TARGETS:
            return _subprocess_sink(
                node, params, assigns, allow_untainted_subprocess)
    return ""
def _sink_from_attr_call(func: ast.Attribute, node: ast.Call,
                         params: list[str] | None,
                         assigns: dict[str, list[str]] | None,
                         aliases: dict[str, str] | None,
                         allow_untainted_subprocess: bool) -> str:
    for _mod in _alias_options(_call_base_root(func, aliases)):
        if _mod == "os" and func.attr in {"system", "popen"}:
            return func.attr
        if _mod == "builtins" and func.attr in _BUILTINS_ATTR_SINKS:
            return func.attr
        if _mod == "subprocess" and func.attr in _SUBPROCESS_EXEC_FUNCS:
            return _subprocess_sink(
                node, params, assigns, allow_untainted_subprocess)
    return "open" if func.attr == "open" else ""
def _call_base_root(func: ast.Attribute,
                    aliases: dict | None) -> str | frozenset[str]:
    base = func.value
    if not isinstance(base, ast.Name):
        return ""
    bound = aliases if aliases is not None else {}
    return bound.get(base.id, base.id)
def match_sink(node: ast.Call, params: list[str] | None = None,
               assigns: dict[str, list[str]] | None = None,
               aliases: dict[str, str] | None = None, *,
               allow_untainted_subprocess: bool = False) -> str:
    if not isinstance(node, ast.Call):
        return ""
    func = node.func
    if isinstance(func, ast.Name):
        return _sink_from_name_call(
            func, node, params, assigns, aliases, allow_untainted_subprocess)
    if isinstance(func, ast.Attribute):
        return _sink_from_attr_call(
            func, node, params, assigns, aliases, allow_untainted_subprocess)
    return ""
def expr_reaches_param(
    expr: ast.AST | None, params: list[str] | None,
    assigns: dict[str, list[str]] | None,
) -> bool:
    params_set = set(params or ())
    assigns = assigns or {}
    if expr is None or isinstance(expr, ast.Constant):
        return False
    pending = _assign_roots(expr)
    seen: set[str] = set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        if name.startswith(_PARAM_ROOT_PREFIX):
            if name[len(_PARAM_ROOT_PREFIX):] in params_set:
                return True
            continue
        dependencies = assigns.get(name)
        if dependencies is None:
            if name in params_set:
                return True
        else:
            pending.extend(dependencies)
    return False
def _parse_file_tree(fpath: str, cache, context: str,
                     quiet: bool) -> ast.Module | None:
    tree = _cached_probe_tree(fpath, cache, context)
    if tree is not None:
        return tree
    return _parse_file_text(fpath, context, quiet=quiet)
def _aggregate_global_taint_funcs(file_entries: list) -> dict:
    _global_taint_funcs: dict = {}
    for (_gfn, _gfp, _gtree, _gca) in file_entries:
        _source_funcs = _memoized_tree_value(
            _TAINT_SOURCE_FUNCS_MEMO, _gfp, _gtree,
            partial(_collect_d2_taint_source_funcs, _gtree, _gfn),
            context=os.path.normcase(os.path.normpath(_gfn)))
        for _fname2, (_gsrc, _gline) in _source_funcs.items():
            _global_taint_funcs.setdefault(_fname2, []).append(
                (_gfn, _gsrc, _gline))
    return _global_taint_funcs
def _fn_span_index(tree: ast.Module) -> list:
    return [
        (n.lineno, getattr(n, "end_lineno", n.lineno) or n.lineno, id(n))
        for n in tree_nodes(tree)
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda))
    ]
@dataclass(frozen=True)
class _FileScanCtx:
    fname: str
    fpath: str
    tree: ast.Module
    call_assigns: dict
    fn_spans: list
    global_taint_funcs: dict
    root_dir: str
def _file_matches_module(module: str, file_name: str) -> bool:
    if not module or not file_name:
        return False
    module_path = module.replace(".", os.sep)
    candidates = (f"{module_path}.py", os.path.join(module_path, "__init__.py"))
    actual = os.path.normcase(os.path.normpath(file_name))
    return any(actual == os.path.normcase(os.path.normpath(candidate))
               for candidate in candidates)
def _taint_func_flow_steps(_cf: str, lctx: _FileScanCtx, sink_var: str,
                           sink_line: int, module: str) -> tuple | None:
    for (_sf, _ssrc, _sline) in lctx.global_taint_funcs.get(_cf, ()):
        _callee_path = os.path.join(lctx.root_dir, _sf)
        _callee_norm = os.path.normcase(os.path.abspath(_callee_path))
        if _callee_norm == os.path.normcase(os.path.abspath(lctx.fpath)):
            continue
        if not _file_matches_module(module, _sf):
            continue
        return (
            {"file_path": _callee_path, "line": _sline,
             "variable": _cf, "constraint": f"taint_source={_ssrc}"},
            {"file_path": lctx.fpath, "line": sink_line,
             "variable": sink_var, "constraint": ""},
            _ssrc,
        )
    return None
def _sink_fn_chain(node: ast.Call, fn_spans: list) -> set:
    return {_fid for (_lo, _hi, _fid) in fn_spans
            if _lo <= node.lineno <= _hi}
def _visible_call_targets(_v: str, assigns, params, _sink_chain: set,
                          call_assigns: dict) -> list:
    _bound = _v in (params or ()) or (
        assigns is not None and _v in assigns)
    _out = []
    for (_cm, _cf, _cl, _cfn) in call_assigns.get(_v, ()):
        if _cfn is None:
            if _bound and _sink_chain:
                continue
        elif _cfn not in _sink_chain:
            continue
        _out.append((_cm, _cf, _cl, _cfn))
    return _out
def _link_cross_file_steps(_flow: dict, _first, node: ast.Call, assigns,
                           params, lctx: _FileScanCtx) -> bool:
    if not lctx.call_assigns or _first is None:
        return False
    _sink_chain = _sink_fn_chain(node, lctx.fn_spans)
    def _reachable_roots(module_assigns: dict | None) -> set[str]:
        _pending = _assign_roots(_first)
        _seen: set[str] = set()
        while _pending:
            _name = _pending.pop()
            if _name in _seen:
                continue
            _seen.add(_name)
            if assigns is not None and _name in assigns:
                _dependencies = assigns[_name]
            elif _name in (params or ()):
                _dependencies = ()
            elif module_assigns is not None:
                _dependencies = module_assigns.get(_name, ())
            else:
                _dependencies = ()
            _pending.extend(_dependencies)
        return _seen
    def _attempt_link(module_assigns: dict | None) -> bool:
        for _v in sorted(_reachable_roots(module_assigns)):
            for (_cm, _cf, _cl, _cfn) in _visible_call_targets(
                    _v, assigns, params, _sink_chain, lctx.call_assigns):
                _steps = _taint_func_flow_steps(
                    _cf, lctx, _v, node.lineno, _cm)
                if _steps is not None:
                    _flow.update(_cross_file_flow_fields(_steps))
                    return True
        return False
    if _attempt_link(None):
        return True
    if not _sink_chain:
        return False
    _module_assigns = _module_assigns_for_link_cached(lctx.fpath, lctx.tree)
    return bool(_module_assigns) and _attempt_link(_module_assigns)
def _cross_file_flow_fields(steps: tuple) -> dict:
    _src_step, _sink_step, _ssrc = steps
    return {"steps": [_src_step, _sink_step],
            "source_name": _ssrc,
            "reaches_param": True}
def _is_scan_candidate(fname: str, fpath: str, cache,
                       restrict: set[str] | None) -> bool:
    if not is_scan_py_name(os.path.basename(fname)):
        return False
    if os.path.isdir(fpath):
        return False
    if (is_test_source_basename(os.path.basename(fname))
            and _is_pytest_test_file(fpath, cache)):
        return False
    return (restrict is None
            or os.path.normcase(os.path.abspath(fpath)) in restrict)
def _collect_file_entries(root_dir: str, dir_listing: list, cache,
                          _restrict) -> tuple:
    _file_entries: list = []
    _files_scanned = 0
    _files_failed = 0
    for fname in dir_listing:
        fpath = os.path.join(root_dir, fname)
        if not _is_scan_candidate(fname, fpath, cache, _restrict):
            continue
        tree = _parse_file_tree(fpath, cache, "扫描项目文件", quiet=False)
        if tree is None:
            _files_failed += 1
            continue
        _files_scanned += 1
        _mods, _fims = _parse_module_imports(tree, file_name=fname)
        _call_assigns = _collect_call_assigns(
            tree, _mods, _fims, file_name=fname)
        _file_entries.append((fname, fpath, tree, _call_assigns))
    return _file_entries, _files_scanned, _files_failed
def _sink_flow_record(lctx: _FileScanCtx, node: ast.Call, sink: str,
                      reaches: bool) -> dict:
    return {
        "source_file": lctx.fpath,
        "sink": sink,
        "line": node.lineno,
        "severity": "P1",
        "rule_id": "SYMBOLIC-SINK",
        "rule_family": "danger_pattern",
        "flow_id": f"{lctx.fname}:{node.lineno}:{node.col_offset}:{sink}",
        "reaches_param": reaches,
    }
def _iter_scan_relpaths(root_dir: str) -> tuple[list, list[str]]:
    rels: list = []
    errors: list[str] = []
    def _record(err: OSError) -> None:
        errors.append(str(err))
        _log.warning("[CrossFileTaint] 子目录不可读，跳过并继续: %s", err)
    _skip = scan_prune_dirs(root_dir)
    for dirpath, dirnames, filenames in os.walk(root_dir, onerror=_record):
        prune_scan_dirnames(dirnames, _skip)
        dirnames.sort()
        for name in sorted(filenames):
            if not is_scan_py_name(name):
                continue
            _abs = os.path.join(dirpath, name)
            _rel = os.path.relpath(_abs, root_dir)
            if is_generic_archive_or_cache_path(_rel):
                continue
            rels.append(_rel)
    return rels, errors
def _list_scan_root(root_dir: str | None, report) -> list | None:
    if not root_dir:
        report.summary["files_scanned"] = 0
        report.summary["files_failed"] = 0
        report.summary["scan_error"] = "扫描根未提供，跨文件污点扫描未执行"
        return None
    if not os.path.isdir(root_dir):
        report.summary["files_scanned"] = 0
        report.summary["files_failed"] = 0
        report.summary["scan_error"] = f"扫描根不存在或不是目录: {root_dir}"
        return None
    try:
        rels, errors = _iter_scan_relpaths(root_dir)
    except OSError as e:
        _log.warning("[CrossFileTaint] 扫描根不可读，整目录跳过 %s: %s",
                     root_dir, e)
        report.summary["files_scanned"] = 0
        report.summary["files_failed"] = 0
        report.summary["scan_error"] = f"扫描根不可读: {e}"
        return None
    if errors:
        report.summary["walk_error_count"] = len(errors)
    return rels
class CrossFileTaintEngine:
    def _scan_file_sinks(self, lctx: _FileScanCtx, report) -> None:
        for node, params, assigns, scope_aliases in iter_calls_with_scope_cached(lctx.fpath, lctx.tree):
            if params is None:
                continue
            sink = match_sink(node, params, assigns, scope_aliases)
            cross_file_only = False
            if not sink:
                sink = match_sink(
                    node, params, assigns, scope_aliases,
                    allow_untainted_subprocess=True)
                cross_file_only = bool(sink)
            if not sink or sink == "open":
                continue
            _first = sink_first_arg(node)
            _reaches = expr_reaches_param(_first, params, assigns)
            _flow = _sink_flow_record(lctx, node, sink, _reaches)
            linked = _link_cross_file_steps(
                _flow, _first, node, assigns, params, lctx)
            if cross_file_only and not linked:
                continue
            report.flows.append(_flow)
    def analyze_project(
        self, root_dir: str | None = None, cache=None,
        restrict_files: list[str] | None = None,
    ) -> CrossFileTaintReport:
        report = CrossFileTaintReport()
        _root = os.path.abspath(root_dir) if root_dir else root_dir
        _dir_listing = _list_scan_root(_root, report)
        if _dir_listing is None:
            return report
        _restrict: set[str] | None = (
            {os.path.normcase(os.path.abspath(os.path.join(_root, f)))
             for f in restrict_files}
            if restrict_files is not None else None
        )
        _file_entries, _files_scanned, _files_failed = _collect_file_entries(
            _root, _dir_listing, cache, _restrict)
        _global_taint_funcs = _aggregate_global_taint_funcs(_file_entries)
        for _entry in _file_entries:
            self._scan_entry(_entry, _global_taint_funcs, _root, report)
        report.summary["files_scanned"] = _files_scanned
        report.summary["files_failed"] = _files_failed
        return report
    def _scan_entry(self, entry, global_taint_funcs: dict,
                    root_dir: str, report) -> None:
        fname, fpath, tree, _call_assigns = entry
        _lctx = _FileScanCtx(
            fname=fname, fpath=fpath, tree=tree,
            call_assigns=_call_assigns,
            fn_spans=_fn_span_index(tree),
            global_taint_funcs=global_taint_funcs,
            root_dir=root_dir)
        self._scan_file_sinks(_lctx, report)

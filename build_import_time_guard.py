from __future__ import annotations

__all__ = [
    "guard_atexit_register",
    "guard_import_side_effect",
    "guard_imports",
]
import ast as _ast
import copy
import logging
import os
import sys
from collections.abc import Iterable, Iterator
from dataclasses import dataclass
from importlib import machinery, util
from typing import NamedTuple

from jwsgj.build_import_reference import (
    _FUNCTION_CONTAINER_TYPES,
    _IMPORT_GUARD_OPS,
    _MODULE_FILE_SUFFIXES,
    _TRY_STMT_TYPES,
    _guard_outcome,
    _importfrom_candidate_dirs_by_parts,
    _iter_block_parts,
    _iter_guard_py_sources,
    _outermost_package_root,
    _passed,
    _path_identity,
    _prune_non_import_time_branches,
    _resolve_relative_module,
    _submodule_file_exists,
)
from jwsgj.diag_shared_ast_bindings import (
    collect_shadow_bindings,
    exec_scope_declarations,
)
from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    _non_import_time_branch,
    _type_checking_guard_node_polarities,
    build_parent_map,
    collect_param_names,
    comp_target_names,
    definition_time_exprs,
    import_alias_bound_names,
    in_subtree,
    is_main_check,
    is_star_import,
    iter_def_site_nodes,
    iter_evaluation_scope_chain,
    iter_module_level_stmts,
    iter_scope_nodes,
    iter_unpack_target_names,
    module_postpones_annotations,
    pattern_capture_name,
)
from jwsgj.diag_shared_source_core import read_source
from jwsgj.diag_types_defs import (
    GuardResult,
    OperationContext,
    code_to_write_str,
    issues_guard_result,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    GuardLevel,
    OperationType,
)
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
def _parse_code(code: str) -> _ast.Module | None:
    try:
        return _ast.parse(code)
    except PARSE_DEGRADE_EXC as exc:
        logger.warning("[Guard] 待写入代码无法解析,跳过: %s", exc)
        return None
def _parse_guarded_code(ctx: OperationContext, guard_name: str,
                        op_skip_msg: str) -> tuple:
    if ctx.operation not in (OperationType.MODIFY_CODE,
                                 OperationType.REFACTOR,
                                 OperationType.WRITE_FILE):
        return None, _passed(guard_name, op_skip_msg)
    code = code_to_write_str(ctx)
    if not code:
        return None, _passed(guard_name, "无待写入代码,跳过")
    tree = _parse_code(code)
    if tree is None:
        return None, _passed(guard_name, "代码无法解析,跳过")
    return tree, None
_IO_SCAN_STMT_TYPES = (_ast.Assign, _ast.AnnAssign, _ast.AugAssign, _ast.Expr,
                       _ast.Assert, _ast.Raise, _ast.Delete,
                       _ast.Import, _ast.ImportFrom)
_IO_FUNCS = {"open", "makedirs", "mkdir", "remove", "rmdir", "rmtree",
             "listdir", "walk", "scandir", "stat", "exists", "isfile",
             "isdir", "rename", "replace", "unlink",
             "copy", "copy2", "copyfile", "copytree", "move",
             "run", "call", "check_call", "check_output",
             "Popen", "system", "popen", "getoutput", "getstatusoutput"}
_IO_MODULES = {"os", "shutil", "subprocess", "pathlib", "io",
              "builtins"}
_PATHLIB_IO_FUNCS = {"read_text", "read_bytes", "write_text", "write_bytes",
                     "open", "unlink", "mkdir", "rmdir", "stat", "exists",
                     "is_file", "is_dir", "readlink", "lstat",
                     "touch", "rename", "replace", "iterdir", "glob", "rglob"}
_PATHLIB_PATH_FACTORY_FUNCS = frozenset({"cwd", "home"})
_PATHLIB_PATH_DERIVING_FUNCS = frozenset({
    "joinpath", "resolve", "absolute", "expanduser", "relative_to",
    "readlink", "with_name", "with_stem", "with_suffix", "with_segments",
})
_IO_SUBMODULES = {"os.path"}
_STAR_IMPORT_IO_MEMBERS: dict[str, frozenset] = {
    "builtins": frozenset({"open"}),
    "io": frozenset({"open"}),
    "os": frozenset({"open", "makedirs", "mkdir", "remove", "rmdir",
                     "listdir", "walk", "scandir", "stat", "rename",
                     "replace", "unlink", "system", "popen", "path"}),
    "os.path": frozenset({"exists", "isfile", "isdir"}),
    "shutil": frozenset({"rmtree", "copy", "copy2", "copyfile",
                          "copytree", "move"}),
    "subprocess": frozenset({"run", "call", "check_call", "check_output",
                             "Popen", "getoutput", "getstatusoutput"}),
    "pathlib": frozenset({"Path"}),
}
def _iter_def_class_units(node, annotations_evaluated: bool):
    if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
        yield from _yield_def_exec_units(node, annotations_evaluated)
    elif isinstance(node, _ast.ClassDef):
        yield from _iter_class_exec_units(node, annotations_evaluated)
def _iter_class_exec_units(node: _ast.ClassDef, annotations_evaluated: bool):
    yield from iter_def_site_nodes(node)
    yield from _iter_module_stmt_units(node.body, annotations_evaluated)
def _iter_nested_units(node, annotations_evaluated: bool):
    if isinstance(node, _TRY_STMT_TYPES):
        for handler in node.handlers:
            if handler.type is not None:
                yield handler.type
    for part in _iter_block_parts(node):
        if isinstance(part, list):
            yield from _iter_module_stmt_units(part, annotations_evaluated)
        else:
            yield part
def _iter_module_stmt_units(body, annotations_evaluated: bool):
    for node in body:
        if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef,
                              _ast.ClassDef)):
            yield from _iter_def_class_units(node, annotations_evaluated)
            continue
        if isinstance(node, _IO_SCAN_STMT_TYPES):
            yield node
        if isinstance(node, _ast.If) and is_main_check(node.test):
            yield from _iter_module_stmt_units(node.orelse,
                                               annotations_evaluated)
            continue
        yield from _iter_nested_units(node, annotations_evaluated)
def _yield_def_exec_units(node, annotations_evaluated: bool):
    if annotations_evaluated:
        yield from iter_def_site_nodes(node)
    else:
        yield from definition_time_exprs(node)
def _walk_io_call_nodes(root):
    stack: list[tuple[_ast.AST, bool]] = [(root, False)]
    while stack:
        node, executes_lambda_body = stack.pop()
        yield node
        if isinstance(node, _ast.Lambda):
            stack.extend((child, False)
                         for child in _ast.iter_child_nodes(node)
                         if child is not node.body)
            if executes_lambda_body:
                stack.append((node.body, False))
        elif isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef,
                               _ast.ClassDef)):
            stack.extend((child, False)
                         for child in _ast.iter_child_nodes(node)
                         if child not in node.body)
        else:
            stack.extend(
                (child, isinstance(node, _ast.Call) and child is node.func)
                for child in _ast.iter_child_nodes(node))
def _non_import_scope_bindings(tree: _ast.AST) -> dict:
    probe = _prune_non_import_time_branches(tree, drop_imports=True)
    local, _globals, _classes = collect_shadow_bindings(probe)
    return local
class _IoBindings(NamedTuple):
    module_aliases: dict[str, str]
    io_func_aliases: dict[str, str]
    pathlib_path_aliases: set[str]
    pathlib_path_instances: set[str]
    shadowed_names: set[str]
class _BindingEvent(NamedTuple):
    position: tuple[int, int]
    local: str
    module: str | None
    member: str
    control: tuple[tuple[int, str], ...] = ()
    definition: int | None = None
    deleted: bool = False
    initializer: _ast.AST | None = None
    from_iterable: bool = False
class _ScopeBindingIndex(NamedTuple):
    events: tuple[_BindingEvent, ...]
    local_names: frozenset[str]
    function_scope: bool
    def _resolve_events(self, name: str, use_position: tuple[int, int],
                        star_members: dict[str, frozenset],
                        skip_definitions: frozenset[int] = frozenset(),
                        use_control: tuple[tuple[int, str], ...] = ()):
        eligible: list[tuple[_BindingEvent, tuple[str | None, str]]] = []
        for event in self.events:
            if (event.position > use_position
                    or event.definition in skip_definitions):
                continue
            binding: tuple[str | None, str] | None = None
            if event.local == name:
                binding = (event.module, event.member)
            elif event.local == '*':
                members = star_members.get(event.module or '')
                if members is None:
                    binding = ('', '*')
                elif name in members:
                    binding = (event.module or '', name)
            if binding is not None:
                eligible.append((event, binding))
        if eligible:
            latest_event, latest_binding = eligible[-1]
            control_depth = len(latest_event.control)
            if (not latest_event.control
                    or (control_depth <= len(use_control)
                        and use_control[:control_depth]
                        == latest_event.control)):
                return [(latest_event, latest_binding)]
            possible = [(latest_event, latest_binding)]
            for index in range(len(eligible) - 2, -1, -1):
                event, binding = eligible[index]
                if not event.module:
                    continue
                later = eligible[index + 1:]
                definite_shadow = any(
                    not candidate.control and not candidate.module
                    for candidate, _binding in later)
                if definite_shadow or self._conditional_shadow_covers(
                        later, event.control):
                    continue
                if binding not in [candidate_binding
                                   for _candidate, candidate_binding in possible]:
                    possible.append((event, binding))
            return possible
        if self.function_scope and name in self.local_names:
            return None
        return _BINDING_MISSING
    def resolve(self, name: str, use_position: tuple[int, int],
                star_members: dict[str, frozenset],
                skip_definitions: frozenset[int] = frozenset(),
                use_control: tuple[tuple[int, str], ...] = ()):
        resolved = self._resolve_events(
            name, use_position, star_members, skip_definitions, use_control)
        if resolved is _BINDING_MISSING:
            return resolved
        if resolved is None:
            return None, ''
        return [binding for _event, binding in resolved]
    @staticmethod
    def _conditional_shadow_covers(
            later: list[tuple[_BindingEvent, tuple[str | None, str]]],
            prefix: tuple[tuple[int, str], ...]) -> bool:
        depth = len(prefix)
        branch_events: dict[int, list[_BindingEvent]] = {}
        for event, _binding in later:
            if (len(event.control) > depth
                    and event.control[:depth] == prefix
                    and event.control[depth][1] in {'body', 'else'}):
                branch_events.setdefault(
                    event.control[depth][0], []).append(event)
        for if_id in branch_events:
            covered = True
            for branch in ('body', 'else'):
                branch_prefix = (*prefix, (if_id, branch))
                direct = [
                    (event, binding) for event, binding in later
                    if event.control == branch_prefix]
                if not direct:
                    if _ScopeBindingIndex._conditional_shadow_covers(
                            later, branch_prefix):
                        continue
                    covered = False
                    break
                if direct[-1][0].module:
                    covered = False
                    break
                shadow_position = direct[-1][0].position
                if any(event.control[:depth + 1] == branch_prefix
                       and event.position > shadow_position and event.module
                       for event, _binding in later):
                    covered = False
                    break
            if covered:
                return True
        return False
_BINDING_MISSING = object()
def _node_position(node: _ast.AST) -> tuple[int, int]:
    return (getattr(node, 'lineno', -1), getattr(node, 'col_offset', -1))
def _node_end_position(node: _ast.AST) -> tuple[int, int]:
    return (getattr(node, 'end_lineno', None) or getattr(node, 'lineno', -1),
            getattr(node, 'end_col_offset', None)
            if getattr(node, 'end_col_offset', None) is not None
            else getattr(node, 'col_offset', -1))
def _body_start_position(node: _ast.AST) -> tuple[int, int]:
    body = getattr(node, 'body', ())
    return _node_position(body[0]) if body else _node_end_position(node)
def _binding_control_path(
        node: _ast.AST, scope: _ast.AST,
        parent_map: dict[int, _ast.AST]) -> tuple[tuple[int, str], ...]:
    path: list[tuple[int, str]] = []
    child = node
    current = parent_map.get(id(node))
    while current is not None and current is not scope:
        branch: str | None = None
        if isinstance(current, _ast.If):
            if child in current.body:
                branch = 'body'
            elif child in current.orelse:
                branch = 'else'
        elif isinstance(current, (_ast.For, _ast.AsyncFor, _ast.While)):
            if child in current.body:
                branch = 'loop-body'
            elif child in current.orelse:
                branch = 'loop-else'
        elif isinstance(current, _TRY_STMT_TYPES):
            if child in current.body:
                branch = 'try-body'
            elif child in current.orelse:
                branch = 'try-else'
            elif child in current.handlers:
                branch = f'handler-{current.handlers.index(child)}'
        elif isinstance(current, _ast.Match) and child in current.cases:
            branch = f'case-{current.cases.index(child)}'
        if branch is not None:
            path.append((id(current), branch))
        child = current
        current = parent_map.get(id(current))
    path.reverse()
    return tuple(path)
def _target_name_nodes(target: _ast.AST):
    return (node for node in walk_nodes(target)
            if isinstance(node, _ast.Name))
def _iter_assignment_initializers(
        target: _ast.AST, value: _ast.AST | None):
    if (isinstance(target, (_ast.Tuple, _ast.List))
            and isinstance(value, (_ast.Tuple, _ast.List))
            and len(target.elts) == len(value.elts)
            and not any(isinstance(item, _ast.Starred)
                        for item in target.elts)):
        for target_item, value_item in zip(target.elts, value.elts):
            yield from _iter_assignment_initializers(target_item, value_item)
        return
    initializer = value if isinstance(target, _ast.Name) else None
    for name in iter_unpack_target_names(target):
        yield name, initializer
def _scope_binding_index(
        scope: _ast.AST,
        parent_map: dict[int, _ast.AST]) -> _ScopeBindingIndex:
    local, _globals, _classes = collect_shadow_bindings(scope)
    params = collect_param_names(scope)
    binding_names = frozenset(set(local.get('', ())) | params)
    if isinstance(scope, COMP_SCOPE_NODES):
        binding_names = binding_names | comp_target_names(scope)
    nodes = list(iter_scope_nodes(scope))
    outer_names = {name for node in nodes
                   if isinstance(node, (_ast.Global, _ast.Nonlocal))
                   for name in node.names}
    local_names = binding_names - outer_names
    deferred_target_ids: set[int] = set()
    comprehension_target_owners: dict[int, _ast.AST] = {}
    comprehensions = [node for node in nodes
                      if isinstance(node, COMP_SCOPE_NODES)]
    if isinstance(scope, COMP_SCOPE_NODES):
        comprehensions.append(scope)
    for node in comprehensions:
        for generator in node.generators:
            for target_name in _target_name_nodes(generator.target):
                comprehension_target_owners[id(target_name)] = node
    for node in nodes:
        if isinstance(node, _ast.Assign):
            targets = node.targets
        elif isinstance(node, (_ast.AnnAssign, _ast.AugAssign,
                               _ast.For, _ast.AsyncFor, _ast.NamedExpr)):
            targets = (node.target,)
        else:
            continue
        for target in targets:
            deferred_target_ids.update(
                id(target_name) for target_name in _target_name_nodes(target))
    def make_event(node: _ast.AST, local_name: str,
                   module: str | None, member: str = '', *,
                   position: tuple[int, int] | None = None,
                   extra_control: tuple[tuple[int, str], ...] = (),
                   definition: int | None = None,
                   deleted: bool = False,
                   initializer: _ast.AST | None = None,
                   from_iterable: bool = False) -> _BindingEvent:
        return _BindingEvent(
            position if position is not None else _node_position(node),
            local_name, module, member,
            (*_binding_control_path(node, scope, parent_map), *extra_control),
            definition, deleted, initializer, from_iterable)
    events: list[_BindingEvent] = []
    function_scope = isinstance(scope, _FUNCTION_CONTAINER_TYPES)
    if function_scope:
        events.extend(_BindingEvent((-1, -1), name, None, '')
                      for name in sorted(params))
    for node in nodes:
        if isinstance(node, _ast.Import):
            for alias in node.names:
                name = alias.asname or alias.name.split('.')[0]
                if name in binding_names:
                    target = (alias.name if alias.asname
                              else alias.name.split('.')[0])
                    events.append(make_event(node, name, target))
            continue
        if isinstance(node, _ast.ImportFrom):
            module = '' if node.level else (node.module or '')
            for alias in node.names:
                name = alias.asname or alias.name
                if alias.name == '*':
                    events.append(make_event(node, '*', module, '*'))
                elif name in binding_names:
                    events.append(make_event(
                        node, name, module, alias.name))
            continue
        if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            if node.name in binding_names:
                events.append(make_event(
                    node, node.name, None,
                    position=_body_start_position(node)))
            continue
        if isinstance(node, _ast.ClassDef):
            if node.name in binding_names:
                events.append(make_event(
                    node, node.name, None, definition=id(node)))
            continue
        if isinstance(node, _ast.NamedExpr):
            for name in iter_unpack_target_names(node.target):
                if name in binding_names:
                    events.append(make_event(
                        node, name, None,
                        position=_node_end_position(node),
                        deleted=False,
                        initializer=node.value))
            continue
        if isinstance(node, (_ast.Assign, _ast.AnnAssign, _ast.AugAssign)):
            if not (isinstance(node, _ast.AnnAssign) and node.value is None):
                targets = node.targets if isinstance(node, _ast.Assign) else (
                    node.target,)
                for target in targets:
                    value = (None if isinstance(node, _ast.AugAssign)
                             else node.value)
                    for name, initializer in _iter_assignment_initializers(
                            target, value):
                        if name in binding_names:
                            events.append(make_event(
                                node, name, None,
                                position=_node_end_position(node),
                                initializer=initializer))
            continue
        if isinstance(node, (_ast.For, _ast.AsyncFor)):
            initializer = (
                node.iter
                if isinstance(node.target, _ast.Name)
                and isinstance(node.iter, (_ast.List, _ast.Tuple)) else None)
            for name in iter_unpack_target_names(node.target):
                if name in binding_names:
                    events.append(make_event(
                        node, name, None,
                        position=_body_start_position(node),
                        extra_control=((id(node), 'loop-body'),),
                        initializer=initializer,
                        from_iterable=initializer is not None))
            continue
        capture = pattern_capture_name(node)
        if capture and capture in binding_names:
            if isinstance(node, _ast.ExceptHandler):
                events.append(make_event(
                    node, capture, None,
                    position=(_node_end_position(node.type)
                              if node.type is not None
                              else _node_position(node)),
                    definition=id(node)))
                events.append(make_event(
                    node, capture, None,
                    position=_node_end_position(node),
                    definition=id(node), deleted=True))
            else:
                events.append(make_event(node, capture, None))
        if (isinstance(node, _ast.Name)
                and isinstance(node.ctx, (_ast.Store, _ast.Del))
                and id(node) not in deferred_target_ids
                and id(node) not in comprehension_target_owners
                and node.id in binding_names):
            events.append(make_event(
                node, node.id, None,
                deleted=isinstance(node.ctx, _ast.Del)))
    events.sort(key=lambda event: event.position)
    return _ScopeBindingIndex(tuple(events), local_names, function_scope)
def _collect_execution_binding_indices(
        tree: _ast.Module, scope_types,
        parent_map: dict[int, _ast.AST]) -> dict[int, _ScopeBindingIndex]:
    scopes = [tree, *(node for node in walk_nodes(tree)
                      if isinstance(node, scope_types))]
    return {id(scope): _scope_binding_index(scope, parent_map)
            for scope in scopes}
def _call_query_names(call: _ast.AST) -> frozenset[str]:
    root = call.func if isinstance(call, _ast.Call) else call
    return frozenset(node.id for node in walk_nodes(root)
                     if isinstance(node, _ast.Name))
def _import_evaluation_scopes(
        call: _ast.Call, parent_map: dict[int, _ast.AST]) -> list[_ast.AST]:
    lexical = iter_evaluation_scope_chain(call, parent_map)
    comprehensions: list[_ast.AST] = []
    current = parent_map.get(id(call))
    child: _ast.AST = call
    below: _ast.AST | None = None
    while current is not None:
        if isinstance(current, COMP_SCOPE_NODES):
            first_generator = current.generators[0]
            outermost_iter = (child is first_generator
                              and below is first_generator.iter)
            if not outermost_iter:
                comprehensions.append(current)
        below = child
        child = current
        current = parent_map.get(id(current))
    def distance(scope: _ast.AST) -> int:
        node: _ast.AST | None = call
        steps = 0
        while node is not None and node is not scope:
            node = parent_map.get(id(node))
            steps += 1
        return steps
    return sorted([*lexical, *comprehensions], key=distance)
def _comprehension_target_is_visible(
        scope: _ast.AST, name: str, call: _ast.Call) -> bool:
    generators = scope.generators
    visible_count = len(generators)
    for index, generator in enumerate(generators):
        if in_subtree(call, generator.iter):
            visible_count = index
            break
        if any(in_subtree(call, condition) for condition in generator.ifs):
            visible_count = index + 1
            break
    return any(
        name in set(iter_unpack_target_names(generator.target))
        for generator in generators[:visible_count]
    )
def _class_definitions_evaluating_call(
        call: _ast.Call, parent_map: dict[int, _ast.AST]) -> frozenset[int]:
    definitions: set[int] = set()
    deferred = False
    child: _ast.AST = call
    current = parent_map.get(id(call))
    while current is not None:
        if ((isinstance(current, _ast.Lambda) and child is current.body)
                or (isinstance(current,
                               (_ast.FunctionDef, _ast.AsyncFunctionDef))
                    and child in current.body)):
            deferred = True
        elif isinstance(current, _ast.ClassDef) and not deferred:
            definitions.add(id(current))
        child = current
        current = parent_map.get(id(current))
    return frozenset(definitions)
def _innermost_deferred_scope(
        call: _ast.Call, parent_map: dict[int, _ast.AST]) -> _ast.AST | None:
    child: _ast.AST = call
    current = parent_map.get(id(call))
    while current is not None:
        if (isinstance(current, (_ast.FunctionDef, _ast.AsyncFunctionDef))
                and child in current.body):
            return current
        if isinstance(current, _ast.Lambda) and child is current.body:
            parent = parent_map.get(id(current))
            immediately_invoked = (
                isinstance(parent, _ast.Call) and parent.func is current)
            if not immediately_invoked:
                return current
        child = current
        current = parent_map.get(id(current))
    return None

def _merge_binding_event_possibilities(current, future):
    if current is _BINDING_MISSING:
        return future
    if future is _BINDING_MISSING:
        return current
    current_records = ([(None, (None, ''))] if current is None
                       else list(current))
    future_records = ([(None, (None, ''))] if future is None
                      else list(future))
    merged = []
    seen = set()
    for event, binding in [*current_records, *future_records]:
        key = (id(event) if event is not None else None, binding)
        if key not in seen:
            seen.add(key)
            merged.append((event, binding))
    return merged

_LATEST_BINDING_POSITION = (sys.maxsize, sys.maxsize)

def _binding_event_records_at(
        call: _ast.Call, parent_map: dict[int, _ast.AST],
        scope_bindings: dict[int, _ScopeBindingIndex],
        star_members: dict[str, frozenset],
        defer_outer: bool = False,
) -> dict[str, list[tuple[_BindingEvent | None, tuple[str | None, str]]]]:
    scopes = _import_evaluation_scopes(call, parent_map)
    names = _call_query_names(call)
    use_position = (getattr(call, 'lineno', -1),
                    getattr(call, 'col_offset', -1))
    records: dict[
        str, list[tuple[_BindingEvent | None, tuple[str | None, str]]]] = {}
    evaluating_classes = _class_definitions_evaluating_call(call, parent_map)
    deferred_scope = (_innermost_deferred_scope(call, parent_map)
                      if defer_outer else None)
    for name in names:
        for scope in scopes:
            if (isinstance(scope, COMP_SCOPE_NODES)
                    and _comprehension_target_is_visible(scope, name, call)):
                records[name] = [(None, (None, ''))]
                break
            index = scope_bindings.get(id(scope))
            if index is None:
                continue
            use_control = _binding_control_path(call, scope, parent_map)
            events = index._resolve_events(
                name, use_position, star_members, evaluating_classes,
                use_control)
            if (deferred_scope is not None and scope is not deferred_scope
                    and not in_subtree(scope, deferred_scope)):
                future_events = index._resolve_events(
                    name, _LATEST_BINDING_POSITION, star_members,
                    evaluating_classes, use_control)
                events = _merge_binding_event_possibilities(
                    events, future_events)
            if events is _BINDING_MISSING:
                continue
            records[name] = [(None, (None, ''))] if events is None else events
            break
    return records
def _io_bindings_at(call: _ast.Call, parent_map: dict[int, _ast.AST],
                    scope_bindings: dict[int, _ScopeBindingIndex]) -> _IoBindings:
    event_records = _binding_event_records_at(
        call, parent_map, scope_bindings, dict(_STAR_IMPORT_IO_MEMBERS))
    module_aliases: dict[str, str] = {}
    io_func_aliases: dict[str, str] = {}
    pathlib_path_aliases: set[str] = set()
    pathlib_path_instances: set[str] = set()
    shadowed_names: set[str] = set()
    for local, candidate_events in event_records.items():
        has_io_binding = False
        for event, (module, member) in candidate_events:
            if module and module.split('.')[0] in _IO_MODULES:
                if not member:
                    module_aliases[local] = module
                    has_io_binding = True
                elif module == 'pathlib' and member == 'Path':
                    pathlib_path_aliases.add(local)
                    has_io_binding = True
                elif member in _IO_FUNCS:
                    io_func_aliases[local] = f'{module}.{member}'
                    has_io_binding = True
                elif f'{module}.{member}' in _IO_SUBMODULES:
                    module_aliases[local] = f'{module}.{member}'
                    has_io_binding = True
            initializer = event.initializer if event is not None else None
            if initializer is not None:
                initializer_values = (
                    initializer.elts
                    if event.from_iterable
                    and isinstance(initializer, (_ast.List, _ast.Tuple))
                    else (initializer,))
                for initializer_value in initializer_values:
                    initializer_bindings = _io_bindings_at(
                        initializer_value, parent_map, scope_bindings)
                    if _initializer_is_pathlib_path(
                            initializer_value, initializer_bindings):
                        pathlib_path_instances.add(local)
                        has_io_binding = True
                        break
        if not has_io_binding:
            shadowed_names.add(local)
    return _IoBindings(module_aliases, io_func_aliases,
                       pathlib_path_aliases, pathlib_path_instances,
                       shadowed_names)
def _io_scan_units(node, annotations_lazy: bool) -> Iterator[_ast.AST]:
    if annotations_lazy and isinstance(node, _ast.AnnAssign):
        yield node.target
        if node.value is not None:
            yield node.value
        return
    yield node
def _scan_module_io_issues(tree: _ast.Module) -> list[str]:
    tree = _prune_non_import_time_branches(tree)
    parent_map = build_parent_map(tree)
    scope_bindings = _collect_execution_binding_indices(
        tree, (_ast.ClassDef, _ast.Lambda, *COMP_SCOPE_NODES), parent_map)
    annotations_lazy = module_postpones_annotations(
        tree, require_absolute=True)
    issues: list[str] = []
    for unit in _iter_module_stmt_units(
            tree.body, annotations_evaluated=not annotations_lazy):
        for node in _io_scan_units(unit, annotations_lazy):
            for call in _walk_io_call_nodes(node):
                if not isinstance(call, _ast.Call):
                    continue
                bindings = _io_bindings_at(
                    call, parent_map, scope_bindings)
                _msg = _classify_io_call(call, bindings)
                if _msg is not None:
                    issues.append(_msg)
    return issues
def guard_import_side_effect(ctx: OperationContext) -> GuardResult:
    tree, skip = _parse_guarded_code(ctx, "G28", "非代码修改,跳过")
    if skip is not None:
        return skip
    return issues_guard_result(
        "G28", "import 副作用检查", "模块级 I/O", _scan_module_io_issues(tree),
        "将 I/O 操作移入函数中延迟执行，或用环境变量在测试/CI 环境跳过",
        "import 副作用检查通过", level=GuardLevel.WARN)
def _is_os_path_twolevel_io(func: _ast.Attribute,
                            bindings: _IoBindings) -> bool:
    return (isinstance(func, _ast.Attribute)
            and isinstance(func.value, _ast.Attribute)
            and isinstance(func.value.value, _ast.Name)
            and func.attr in _IO_FUNCS
            and func.value.attr == "path"
            and func.value.value.id not in bindings.shadowed_names
            and (func.value.value.id == "os"
                 or bindings.module_aliases.get(func.value.value.id) == "os"))
def _ctor_is_pathlib_path(ctor: _ast.AST, bindings: _IoBindings) -> bool:
    if isinstance(ctor, _ast.Name):
        return ctor.id in bindings.pathlib_path_aliases
    if (isinstance(ctor, _ast.Attribute)
            and ctor.attr in _PATHLIB_PATH_FACTORY_FUNCS):
        return _ctor_is_pathlib_path(ctor.value, bindings)
    return (isinstance(ctor, _ast.Attribute)
            and isinstance(ctor.value, _ast.Name)
            and ctor.value.id not in bindings.shadowed_names
            and ctor.attr == "Path"
            and (ctor.value.id == "pathlib"
                 or bindings.module_aliases.get(ctor.value.id) == "pathlib"))
def _initializer_is_pathlib_path(
        expr: _ast.AST, bindings: _IoBindings) -> bool:
    if isinstance(expr, _ast.Name):
        return expr.id in bindings.pathlib_path_instances
    if isinstance(expr, _ast.Attribute):
        return (expr.attr == "parent"
                and _initializer_is_pathlib_path(expr.value, bindings))
    if isinstance(expr, _ast.Subscript):
        return (isinstance(expr.value, _ast.Attribute)
                and expr.value.attr == "parents"
                and _initializer_is_pathlib_path(expr.value.value, bindings))
    if isinstance(expr, _ast.BinOp):
        return (isinstance(expr.op, _ast.Div)
                and (_initializer_is_pathlib_path(expr.left, bindings)
                     or _initializer_is_pathlib_path(expr.right, bindings)))
    if not isinstance(expr, _ast.Call):
        return False
    if _ctor_is_pathlib_path(expr.func, bindings):
        return True
    return (isinstance(expr.func, _ast.Attribute)
            and expr.func.attr in _PATHLIB_PATH_DERIVING_FUNCS
            and _initializer_is_pathlib_path(expr.func.value, bindings))
def _single_attr_chain_io_msg(func: _ast.Attribute, base: str,
                              bindings: _IoBindings,
                              lineno) -> str | None:
    if func.attr not in _IO_FUNCS or base in bindings.shadowed_names:
        return None
    module = (base if base in _IO_MODULES
              else bindings.module_aliases.get(base))
    if module != "os.path" and module not in _IO_MODULES:
        return None
    return f"行 {lineno}: 模块级 I/O 调用 {module}.{func.attr}()"
def _pathlib_chain_has_ctor(expr: _ast.AST,
                            bindings: _IoBindings) -> bool:
    node = expr
    while True:
        if isinstance(node, _ast.Call):
            if _ctor_is_pathlib_path(node.func, bindings):
                return True
            node = node.func
            continue
        if isinstance(node, (_ast.Attribute, _ast.Subscript)):
            node = node.value
            continue
        if isinstance(node, _ast.BinOp):
            return (_pathlib_chain_has_ctor(node.left, bindings)
                    or _pathlib_chain_has_ctor(node.right, bindings))
        return (isinstance(node, _ast.Name)
                and node.id in bindings.pathlib_path_instances)
def _pathlib_io_msg(func: _ast.AST, bindings: _IoBindings,
                    lineno) -> str | None:
    if not (isinstance(func, _ast.Attribute)
            and func.attr in _PATHLIB_IO_FUNCS):
        return None
    if (_ctor_is_pathlib_path(func.value, bindings)
            or _pathlib_chain_has_ctor(func.value, bindings)):
        return f"行 {lineno}: 模块级 I/O 调用 Path(...).{func.attr}()"
    return None
def _bare_name_io_msg(func: _ast.AST, bindings: _IoBindings,
                      lineno) -> str | None:
    if not isinstance(func, _ast.Name) or func.id in bindings.shadowed_names:
        return None
    if func.id == "open":
        return f"行 {lineno}: 模块级 open() 调用"
    if func.id in bindings.io_func_aliases:
        return (f"行 {lineno}: 模块级 I/O 调用 "
                f"{bindings.io_func_aliases[func.id]}()")
    return None
def _classify_io_call(call: _ast.Call,
                      bindings: _IoBindings) -> str | None:
    func = call.func
    _lineno = getattr(call, 'lineno', '?')
    if isinstance(func, _ast.Attribute) and isinstance(func.value, _ast.Name):
        _msg = _single_attr_chain_io_msg(
            func, func.value.id, bindings, _lineno)
        if _msg is not None:
            return _msg
    if _is_os_path_twolevel_io(func, bindings):
        return f"行 {_lineno}: 模块级 I/O 调用 os.path.{func.attr}()"
    _msg = _pathlib_io_msg(func, bindings, _lineno)
    if _msg is not None:
        return _msg
    return _bare_name_io_msg(func, bindings, _lineno)
def _scan_atexit_issues(tree: _ast.Module) -> list[str]:
    tree = _prune_non_import_time_branches(tree)
    issues: list[str] = []
    _index = _AtexitIndex.of(tree)
    bindings = _collect_execution_binding_indices(
        tree, _ATEXIT_SCOPE_TYPES, _index.parent_map)
    for node in walk_nodes(tree):
        if not isinstance(node, _ast.Call):
            continue
        if _is_protected_register(node, _index):
            continue
        register_names, module_aliases, shadowed_names = _atexit_call_names(
            node, _index, bindings)
        _msg = _classify_atexit_call(
            node, register_names, module_aliases, shadowed_names)
        if _msg is not None:
            issues.append(_msg)
    return issues
def guard_atexit_register(ctx: OperationContext) -> GuardResult:
    tree, skip = _parse_guarded_code(ctx, "G29", "非代码修改,跳过")
    if skip is not None:
        return skip
    return issues_guard_result(
        "G29", "atexit 注册检查", "无防重入注册", _scan_atexit_issues(tree),
        "用模块级 _REGISTERED 标志包裹 atexit.register，避免重复导入时重复注册",
        "atexit 注册检查通过", level=GuardLevel.WARN)
def _registered_flag_name(node: _ast.AST) -> str | None:
    if isinstance(node, _ast.Name):
        return node.id
    if isinstance(node, _ast.Attribute):
        return node.attr
    return None
def _flag_constant_bool(node: _ast.AST) -> bool | None:
    if not isinstance(node, _ast.Constant):
        return None
    value = node.value
    if isinstance(value, bool):
        return value
    if isinstance(value, int) and value in (0, 1):
        return bool(value)
    if value is None:
        return False
    return None
def _is_registered_flag(node: _ast.AST) -> bool:
    name = _registered_flag_name(node)
    return bool(name) and ("REGISTERED" in name or "_registered" in name)
def _registered_flag_polarity(test: _ast.AST) -> bool | None:
    if _is_registered_flag(test):
        return True
    if isinstance(test, _ast.UnaryOp) and isinstance(test.op, _ast.Not):
        inner = _registered_flag_polarity(test.operand)
        return None if inner is None else not inner
    if isinstance(test, _ast.BoolOp) and isinstance(test.op, _ast.And):
        polarities = [_registered_flag_polarity(v) for v in test.values]
        return False if any(p is False for p in polarities) else None
    return _compare_flag_polarity(test)
def _compare_flag_polarity(test: _ast.AST) -> bool | None:
    if not (isinstance(test, _ast.Compare) and len(test.ops) == 1
            and len(test.comparators) == 1):
        return None
    left, right = test.left, test.comparators[0]
    op = test.ops[0]
    if _is_registered_flag(left):
        value = _flag_constant_bool(right)
    elif _is_registered_flag(right):
        value = _flag_constant_bool(left)
    else:
        return None
    if value is None:
        return None
    if isinstance(op, (_ast.Eq, _ast.Is)):
        return value
    if isinstance(op, (_ast.NotEq, _ast.IsNot)):
        return not value
    return None
def _guard_flag_names(test: _ast.AST) -> tuple[str, ...]:
    if _is_registered_flag(test):
        name = _registered_flag_name(test)
        return (name,) if name else ()
    if isinstance(test, _ast.UnaryOp) and isinstance(test.op, _ast.Not):
        return _guard_flag_names(test.operand)
    if isinstance(test, _ast.BoolOp) and isinstance(test.op, _ast.And):
        names = [name for value in test.values
                 if _registered_flag_polarity(value) is False
                 for name in _guard_flag_names(value)]
        return tuple(dict.fromkeys(names))
    if (isinstance(test, _ast.Compare) and len(test.ops) == 1
            and len(test.comparators) == 1):
        left, right = test.left, test.comparators[0]
        if _is_registered_flag(left):
            name = _registered_flag_name(left)
            return (name,) if name else ()
        if _is_registered_flag(right):
            name = _registered_flag_name(right)
            return (name,) if name else ()
    return ()
def _collect_guard_ifs(
        tree: _ast.Module,
) -> tuple[dict[int, bool], list, dict[int, tuple[str, ...]]]:
    guard_polarity: dict[int, bool] = {}
    guard_clause_ifs: list = []
    guard_flag_names: dict[int, tuple[str, ...]] = {}
    for check_node in walk_nodes(tree):
        if not isinstance(check_node, _ast.If):
            continue
        polarity = _registered_flag_polarity(check_node.test)
        if polarity is None:
            continue
        guard_polarity[id(check_node)] = polarity
        guard_flag_names[id(check_node)] = _guard_flag_names(check_node.test)
        if (polarity
                and any(isinstance(s, (_ast.Return, _ast.Raise,
                                       _ast.Break, _ast.Continue))
                        for s in check_node.body)):
            guard_clause_ifs.append(check_node)
    return guard_polarity, guard_clause_ifs, guard_flag_names
def _collect_flag_scopes(
        tree: _ast.Module) -> tuple[dict[int, frozenset], dict[int, frozenset]]:
    local_scopes: dict[int, frozenset] = {}
    global_scopes: dict[int, frozenset] = {}
    scope_types = (*_FUNCTION_CONTAINER_TYPES, _ast.ClassDef)
    for node in walk_nodes(tree):
        if not isinstance(node, scope_types):
            continue
        local_names, global_names = exec_scope_declarations(node)
        local_scopes[id(node)] = local_names
        global_scopes[id(node)] = global_names
    return local_scopes, global_scopes
def _build_stmt_positions(tree: _ast.Module) -> dict[int, tuple[int, str, int]]:
    stmt_positions: dict[int, tuple[int, str, int]] = {}
    for _owner in walk_nodes(tree):
        for _attr in ("body", "orelse", "finalbody"):
            _register_stmt_list(getattr(_owner, _attr, None),
                                id(_owner), _attr, stmt_positions)
        for _h in getattr(_owner, "handlers", None) or []:
            _register_stmt_list(_h.body, id(_h), "body", stmt_positions)
        for _case in getattr(_owner, "cases", None) or []:
            _register_stmt_list(_case.body, id(_case), "body", stmt_positions)
    return stmt_positions
def _register_stmt_list(stmts, owner_id: int, attr: str,
                        stmt_positions: dict) -> None:
    if not isinstance(stmts, list):
        return
    for _idx, _s in enumerate(stmts):
        if isinstance(_s, _ast.stmt):
            stmt_positions[id(_s)] = (owner_id, attr, _idx)
_ATEXIT_SCOPE_TYPES = (
    *_FUNCTION_CONTAINER_TYPES, _ast.ClassDef, *COMP_SCOPE_NODES)
_ATEXIT_STAR_IMPORT_MEMBERS = {"atexit": frozenset({"register"})}
def _atexit_call_names(
        call: _ast.Call, index: _AtexitIndex,
        bindings: dict[int, _ScopeBindingIndex]) -> tuple[set, set, set]:
    event_records = _binding_event_records_at(
        call, index.parent_map, bindings, _ATEXIT_STAR_IMPORT_MEMBERS,
        defer_outer=True)
    records = {name: [binding for _event, binding in events]
               for name, events in event_records.items()}
    register_names: set[str] = set()
    module_aliases: set[str] = set()
    shadowed_names: set[str] = set()
    for local, candidate_bindings in records.items():
        has_atexit_binding = False
        for module, member in candidate_bindings:
            if module == 'atexit' and not member:
                module_aliases.add(local)
                has_atexit_binding = True
            elif module == 'atexit' and member == 'register':
                register_names.add(local)
                has_atexit_binding = True
        if not has_atexit_binding:
            shadowed_names.add(local)
    return register_names, module_aliases, shadowed_names
@dataclass(frozen=True)
class _AtexitIndex:
    parent_map: dict[int, _ast.AST]
    stmt_positions: dict[int, tuple[int, str, int]]
    guard_if_polarity: dict[int, bool]
    guard_clause_ifs: list
    guard_flag_names: dict[int, tuple[str, ...]]
    flag_local_scopes: dict[int, frozenset]
    flag_global_scopes: dict[int, frozenset]
    @classmethod
    def of(cls, tree: _ast.Module) -> _AtexitIndex:
        guard_polarity, guard_clause_ifs, guard_flag_names = _collect_guard_ifs(
            tree)
        local_scopes, global_scopes = _collect_flag_scopes(tree)
        return cls(
            parent_map=build_parent_map(tree),
            stmt_positions=_build_stmt_positions(tree),
            guard_if_polarity=guard_polarity,
            guard_clause_ifs=guard_clause_ifs,
            guard_flag_names=guard_flag_names,
            flag_local_scopes=local_scopes,
            flag_global_scopes=global_scopes,
        )
def _owning_stmt(node: _ast.AST, index: _AtexitIndex) -> _ast.AST | None:
    _cur: _ast.AST | None = node
    while _cur is not None and id(_cur) not in index.stmt_positions:
        _cur = index.parent_map.get(id(_cur))
    return _cur
def _flag_binding_credible(call_node: _ast.AST,
                           flag_names: tuple[str, ...],
                           index: _AtexitIndex) -> bool:
    if not flag_names:
        return True
    for flag_name in flag_names:
        _child: _ast.AST = call_node
        _cur: _ast.AST | None = index.parent_map.get(id(call_node))
        deferred = False
        while _cur is not None and not isinstance(_cur, _ast.Module):
            is_function = isinstance(_cur, _FUNCTION_CONTAINER_TYPES)
            in_deferred_body = (
                (isinstance(_cur, _ast.Lambda) and _child is _cur.body)
                or (isinstance(_cur,
                               (_ast.FunctionDef, _ast.AsyncFunctionDef))
                    and _child in _cur.body))
            if is_function and not in_deferred_body:
                _child = _cur
                _cur = index.parent_map.get(id(_cur))
                continue
            deferred = deferred or in_deferred_body
            local_names = index.flag_local_scopes.get(id(_cur))
            class_binding_visible = not isinstance(_cur, _ast.ClassDef) or not deferred
            if (class_binding_visible and local_names is not None
                    and flag_name in local_names
                    and flag_name not in index.flag_global_scopes.get(
                        id(_cur), frozenset())):
                break
            _child = _cur
            _cur = index.parent_map.get(id(_cur))
        else:
            return True
    return False
def _protected_by_enclosing_guard(call_node: _ast.AST,
                                  index: _AtexitIndex) -> bool:
    _child: _ast.AST | None = call_node
    _cur: _ast.AST | None = index.parent_map.get(id(call_node))
    while _cur is not None:
        polarity = index.guard_if_polarity.get(id(_cur))
        if polarity is not None:
            body = getattr(_cur, "body", ())
            orelse = getattr(_cur, "orelse", ())
            protected_branch = (
                (polarity is False and any(_child is s for s in body))
                or (polarity is True and any(_child is s for s in orelse)))
            if (protected_branch and _executes_with_owning_stmt(
                    call_node, _child, index)
                    and _flag_binding_credible(
                        call_node,
                        index.guard_flag_names.get(id(_cur), ()), index)):
                return True
        _child = _cur
        _cur = index.parent_map.get(id(_cur))
    return False
def _executes_with_owning_stmt(call_node: _ast.AST, stmt: _ast.AST,
                               index: _AtexitIndex) -> bool:
    _child: _ast.AST | None = call_node
    _cur: _ast.AST | None = index.parent_map.get(id(call_node))
    while _cur is not None:
        if isinstance(_cur, _ast.Lambda) and _child is _cur.body:
            return False
        if (isinstance(_cur, (_ast.FunctionDef, _ast.AsyncFunctionDef))
                and any(_child is _s for _s in _cur.body)):
            return False
        if _cur is stmt:
            break
        _child = _cur
        _cur = index.parent_map.get(id(_cur))
    return True
def _guard_clause_precedes(call_node: _ast.AST,
                           index: _AtexitIndex) -> bool:
    _child: _ast.AST | None = call_node
    _cur: _ast.AST | None = index.parent_map.get(id(call_node))
    while _cur is not None:
        _pos = index.stmt_positions.get(id(_child))
        if (_pos is not None and _executes_with_owning_stmt(
                call_node, _child, index)):
            for _gc in index.guard_clause_ifs:
                _gpos = index.stmt_positions.get(id(_gc))
                if (_gpos is not None and _gpos[0] == _pos[0]
                        and _gpos[1] == _pos[1] and _pos[2] > _gpos[2]
                        and _flag_binding_credible(
                            call_node,
                            index.guard_flag_names.get(id(_gc), ()),
                            index)):
                    return True
        _child = _cur
        _cur = index.parent_map.get(id(_cur))
    return False
def _protected_by_guard_clause(call_node: _ast.AST,
                               index: _AtexitIndex) -> bool:
    _stmt = _owning_stmt(call_node, index)
    if _stmt is None:
        return False
    if not _executes_with_owning_stmt(call_node, _stmt, index):
        return False
    return _guard_clause_precedes(call_node, index)
def _is_protected_register(call_node: _ast.Call,
                           index: _AtexitIndex) -> bool:
    return (_protected_by_enclosing_guard(call_node, index)
            or _protected_by_guard_clause(call_node, index))
def _classify_atexit_call(node: _ast.Call,
                          register_names: set, module_aliases: set,
                          shadowed_names: set) -> str | None:
    _fn = node.func
    _lineno = getattr(node, 'lineno', '?')
    if (isinstance(_fn, _ast.Attribute) and _fn.attr == "register"
            and isinstance(_fn.value, _ast.Name)
            and (_fn.value.id in module_aliases
                 or (_fn.value.id == "atexit"
                     and _fn.value.id not in shadowed_names))):
        return (f"行 {_lineno}: {_fn.value.id}.register() 无防重入标志保护")
    if isinstance(_fn, _ast.Name) and _fn.id in register_names:
        return (f"行 {_lineno}: register()（from atexit import register）"
                f" 无防重入标志保护")
    return None
_EXTERNAL_MODULES_ENV = "PY_IMPORT_GUARD_EXTERNAL_MODULES"
_EXTERNAL_MODULES_ENV_LEGACY = "SAFE_OPS_EXTERNAL_MODULES"
def _configured_external_tops() -> frozenset[str]:
    raw = ",".join(filter(None, (os.environ.get(_EXTERNAL_MODULES_ENV, ""),
                                 os.environ.get(_EXTERNAL_MODULES_ENV_LEGACY, ""))))
    return frozenset(part.strip().split('.', maxsplit=1)[0]
                     for part in raw.split(',')
                     if part.strip())
def _plain_search_locations(spec) -> list[str] | None:
    locations = getattr(spec, 'submodule_search_locations', None)
    if locations is None:
        return None
    origin = getattr(spec, 'origin', None)
    if isinstance(origin, str) and origin:
        return [os.path.dirname(origin)]
    try:
        return [os.fspath(path) for path in locations]
    except KeyError:
        return [os.fspath(path)
                for path in getattr(locations, '_path', ())]
def _descend_submodule_roots(
        roots: Iterable[str], segments: list[str],
        prefix: Iterable[str] = ()) -> tuple[str, list[str]]:
    dirs = list(roots)
    resolved_parts = list(prefix)
    for _idx, _seg in enumerate(segments):
        resolved_parts.append(_seg)
        try:
            spec = machinery.PathFinder.find_spec(
                '.'.join(resolved_parts), dirs)
        except KeyError:
            # 命名空间包分段：importlib 构造 _NamespacePath 时按父包名取
            # sys.modules[父包].__path__，只读定位流程不导入父包，父包未加载
            # 即抛 KeyError；改走下方目录级解析（__init__/模块文件/命名空间目录）
            spec = None
        if spec is not None:
            locations = _plain_search_locations(spec)
            if _idx == len(segments) - 1:
                if spec.submodule_search_locations is not None:
                    return "", list(locations or ())
                origin = getattr(spec, 'origin', None)
                return (origin if isinstance(origin, str) and origin else ""), []
            if spec.submodule_search_locations is None:
                return "", []
            dirs = list(locations or ())
            if not dirs:
                return "", []
            continue
        namespace_dirs: list[str] = []
        package_dir = ""
        for base in dirs:
            sub_dir = os.path.join(base, _seg)
            if os.path.isfile(os.path.join(sub_dir, "__init__.py")):
                package_dir = sub_dir
                break
            module_file = _module_file_in(base, _seg)
            if module_file:
                return ((module_file, []) if _idx == len(segments) - 1
                        else ("", []))
            if os.path.isdir(sub_dir):
                namespace_dirs.append(sub_dir)
        if package_dir:
            dirs = [package_dir]
        elif namespace_dirs:
            dirs = namespace_dirs
        else:
            return "", []
    return "", dirs
def _fs_submodule_ok(module_path: str, top_spec) -> bool:
    parts = [part for part in module_path.split('.') if part]
    if len(parts) == 1:
        return True
    if getattr(top_spec, "submodule_search_locations", None) is None:
        return False
    locations = _plain_search_locations(top_spec) or []
    module_file, package_dirs = _descend_submodule_roots(
        locations, parts[1:], parts[:1])
    return bool(module_file or package_dirs)
def _fallback_roots_check(module_path: str,
                          fallback_roots: list[str]) -> bool | None:
    if not fallback_roots:
        return None
    top = module_path.split('.', maxsplit=1)[0]
    try:
        top_spec = machinery.PathFinder.find_spec(top, fallback_roots)
    except (ImportError, ValueError) as exc:
        logger.debug("[Guard] fallback 根下顶级名解析失败: %s (%s)",
                     module_path, exc)
        return None
    if top_spec is None:
        return None
    return _fs_submodule_ok(module_path, top_spec)
def _check_import(module_path: str,
                  fallback_roots: list[str] | None = None,
                  fallback_verdict: bool | None = None
                  ) -> tuple[bool, str | None]:
    try:
        if fallback_roots and fallback_verdict is None:
            fallback_verdict = _fallback_roots_check(
                module_path, fallback_roots)
        if fallback_verdict is not None:
            return ((True, None) if fallback_verdict
                    else (False, f"模块 {module_path} 不存在"))
        module_file, package_dirs = _locate_module(module_path)
        if not module_file and not package_dirs:
            return False, f"模块 {module_path} 不存在"
        return True, None
    except ValueError as e:
        logger.warning("[Guard] find_spec 值错误: %s", e)
        return False, f"导入 {module_path} 失败: {e}"
    except (ImportError, OSError, AttributeError) as e:
        logger.warning("[Guard] 检查 %s 时出错: %s", module_path, e)
        return False, f"检查 {module_path} 时出错: {e}"
def _module_file_in(base_dir: str, segment: str) -> str:
    for suffix in _MODULE_FILE_SUFFIXES:
        candidate = os.path.join(base_dir, segment + suffix)
        if os.path.isfile(candidate):
            return candidate
    return ""
def _locate_module(module_path: str) -> tuple[str, list[str]]:
    parts = [part for part in module_path.split('.') if part]
    if not parts:
        return "", []
    top = parts[0]
    loaded_modules = {name for name in sys.modules
                      if name == top or name.startswith(top + '.')}
    try:
        is_stdlib = top in sys.stdlib_module_names
        spec = util.find_spec(module_path if is_stdlib else top)
        if spec is None:
            return "", []
        dirs = _plain_search_locations(spec)
        if len(parts) == 1 or is_stdlib:
            origin = getattr(spec, 'origin', None)
            module_file = (origin if isinstance(origin, str) and origin
                           else "")
            return module_file, list(dirs or ())
        return _descend_submodule_roots(dirs or (), parts[1:], parts[:1])
    except (ModuleNotFoundError, KeyError, ValueError) as exc:
        logger.debug("[Guard] 模块定位失败，按不存在处理: %s (%s)",
                     module_path, exc)
        return "", []
    finally:
        for _name in [n for n in sys.modules
                      if (n == top or n.startswith(top + '.'))
                      and n not in loaded_modules]:
            sys.modules.pop(_name, None)
def _unique_roots(candidates: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    roots: list[str] = []
    for candidate in candidates:
        real = os.path.abspath(candidate)
        key = os.path.normcase(real)
        if key not in seen:
            seen.add(key)
            roots.append(real)
    return roots
def _derive_fallback_roots(fpath: str, target_path: str = "") -> list[str]:
    fdir = os.path.dirname(os.path.abspath(fpath))
    candidates: list[str] = []
    pkg_root = _outermost_package_root(os.path.dirname(os.path.abspath(fpath)))
    if pkg_root:
        candidates.append(pkg_root)
    candidates.append(fdir)
    if target_path:
        target = os.path.abspath(target_path)
        candidates.append(target if os.path.isdir(target)
                           else os.path.dirname(target))
    return _unique_roots(candidates)
def _should_skip_import(module_path: str) -> bool:
    if not module_path:
        return True
    top = module_path.split('.', maxsplit=1)[0]
    return top in _configured_external_tops()
def _contains_active_raise(node: _ast.AST) -> bool:
    stack: list[_ast.AST] = [node]
    while stack:
        current = stack.pop()
        if isinstance(current, _ast.Raise):
            return True
        if isinstance(current, _FUNCTION_CONTAINER_TYPES):
            continue
        stack.extend(_ast.iter_child_nodes(current))
    return False
_IMPORT_ERROR_EXCEPTION_NAMES = frozenset({
    'ImportError', 'ModuleNotFoundError', 'Exception', 'BaseException'})
def _is_builtin_import_exception(
        candidate: _ast.AST,
        parent_map: dict[int, _ast.AST] | None = None,
        scope_bindings: dict[int, _ScopeBindingIndex] | None = None) -> bool:
    if isinstance(candidate, _ast.BinOp) and isinstance(candidate.op, _ast.BitOr):
        return (_is_builtin_import_exception(
                    candidate.left, parent_map, scope_bindings)
                or _is_builtin_import_exception(
                    candidate.right, parent_map, scope_bindings))
    if isinstance(candidate, _ast.Name):
        if parent_map is None or scope_bindings is None:
            return candidate.id in _IMPORT_ERROR_EXCEPTION_NAMES
        records = _binding_event_records_at(
            candidate, parent_map, scope_bindings,
            {'builtins': _IMPORT_ERROR_EXCEPTION_NAMES})
        events = records.get(candidate.id)
        if events is None:
            return candidate.id in _IMPORT_ERROR_EXCEPTION_NAMES
        return any(module == 'builtins'
                   and member in _IMPORT_ERROR_EXCEPTION_NAMES
                   for _event, (module, member) in events)
    if not (isinstance(candidate, _ast.Attribute)
            and isinstance(candidate.value, _ast.Name)
            and candidate.attr in _IMPORT_ERROR_EXCEPTION_NAMES):
        return False
    root_name = candidate.value.id
    if parent_map is None or scope_bindings is None:
        return root_name == 'builtins'
    records = _binding_event_records_at(
        candidate, parent_map, scope_bindings,
        {'builtins': _IMPORT_ERROR_EXCEPTION_NAMES})
    events = records.get(root_name)
    return bool(events) and any(
        module == 'builtins' and not member
        for _event, (module, member) in events)
def _try_suppresses_import_errors(
        node: _ast.AST,
        parent_map: dict[int, _ast.AST] | None = None,
        scope_bindings: dict[int, _ScopeBindingIndex] | None = None) -> bool:
    for handler in node.handlers:
        exc = handler.type
        candidates = exc.elts if isinstance(exc, _ast.Tuple) else (
            [exc] if exc is not None else [])
        if exc is None or any(
                _is_builtin_import_exception(
                    candidate, parent_map, scope_bindings)
                for candidate in candidates):
            return not _contains_active_raise(handler)
    return False
def _iter_required_import_nodes(
        tree: _ast.Module) -> Iterator[tuple[_ast.AST, tuple[_ast.AST, ...]]]:
    # 与 _prune_non_import_time_branches 同源：从根节点解析 typing 别名
    # （`from typing import TYPE_CHECKING as TC`、`import typing as t`），
    # 否则 _non_import_time_branch 的无极性回退只认裸名 TYPE_CHECKING。
    # 产出 (导入节点, 保护它的 try 节点链)：仅当导入位于抑制了体导入失败的
    # try/except ImportError 的 else 分支时链非空（嵌套 else 逐层累积）——
    # else 仅在体无异常时执行，其导入是否必需取决于各层体导入的检查结果。
    tc_polarities = _type_checking_guard_node_polarities(tree)
    stack: list[tuple[_ast.AST, bool, bool, tuple[_ast.AST, ...]]] = [
        (tree, False, False, ())]
    parent_map: dict[int, _ast.AST] | None = None
    scope_bindings: dict[int, _ScopeBindingIndex] | None = None
    while stack:
        node, optional, in_function, guard = stack.pop()
        if isinstance(node, (_ast.Import, _ast.ImportFrom)):
            if not optional:
                yield node, guard
            continue
        if isinstance(node, _ast.Lambda):
            continue
        if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            for child in reversed(node.body):
                stack.append((child, False, True, ()))
            continue
        if isinstance(node, (_ast.If, _ast.While, _ast.For,
                             _ast.AsyncFor)):
            # 分支可达性统一走 _non_import_time_branch（与 G12/G28 同源）：
            # 常量 test/空可迭代、TYPE_CHECKING、__main__ 守卫均由其判定，
            # 避免 G4 内联实现与共享剪枝漂移（例如 __name__ != '__main__'
            # 的 else 分支被误当必需导入）。函数体内的 __main__ 守卫例外：
            # 函数可能由入口直接调用，两个分支都保守提取。
            if (isinstance(node, _ast.If) and in_function
                    and is_main_check(node.test)):
                branches = [node.body, node.orelse]
            else:
                _branch = _non_import_time_branch(node, tc_polarities)
                if _branch == 'body':
                    branches = [node.orelse]
                elif _branch == 'orelse':
                    branches = [node.body]
                else:
                    branches = [node.body, node.orelse]
            for branch in reversed(branches):
                for child in reversed(branch):
                    stack.append((child, optional, in_function, guard))
            continue
        if isinstance(node, _TRY_STMT_TYPES):
            if parent_map is None:
                parent_map = build_parent_map(tree)
                scope_bindings = _collect_execution_binding_indices(
                    tree, _ATEXIT_SCOPE_TYPES, parent_map)
            body_optional = optional or _try_suppresses_import_errors(
                node, parent_map, scope_bindings)
            # else 分支仅在体无异常时执行：体导入失败被抑制时，else 中的
            # 导入交给该 try 节点保护（由 _try_body_imports_broken 按体导入
            # 实际检查结果决定是否报告）；handlers/finally 总执行，不受保护。
            # 嵌套 else 累积保护链：外层体断裂时内层整段不执行。
            parts = ((node.body, body_optional, guard),
                     (node.handlers, optional, guard),
                     (node.orelse, optional,
                      guard + (node,) if body_optional else guard),
                     (node.finalbody, optional, guard))
            for children, child_optional, child_guard in reversed(parts):
                for child in reversed(children):
                    stack.append((child, child_optional, in_function, child_guard))
            continue
        for child in reversed(list(_ast.iter_child_nodes(node))):
            stack.append((child, optional, in_function, guard))
def _try_body_imports_broken(fpath: str, target: str,
                             guards: tuple[_ast.AST, ...], roots: list[str],
                             fallback_verdicts: dict[str, bool | None]) -> bool:
    # 保护链上任一 try 体中导入期可达的导入已断裂，else 分支必然不执行。
    # 体导入本身是可选导入（不进必需集），故此处独立判定而非复用
    # broken_modules；函数/lambda 体内的导入不在导入期执行，跳过。
    for guard in guards:
        body = getattr(guard, 'body', None)
        if not isinstance(body, list):
            continue
        stack: list[_ast.AST] = list(body)
        while stack:
            node = stack.pop()
            if isinstance(node, (_ast.Import, _ast.ImportFrom)):
                pairs = ([(alias.name, 0) for alias in node.names]
                         if isinstance(node, _ast.Import)
                         else [(node.module or '', node.level or 0)])
                for module_path, level in pairs:
                    resolved, rel_error = _absolute_import_name(
                        fpath, module_path, level, target)
                    if rel_error is not None:
                        continue
                    if resolved is None or _should_skip_import(resolved):
                        continue
                    if resolved not in fallback_verdicts:
                        fallback_verdicts[resolved] = (
                            _fallback_roots_check(resolved, roots)
                            if roots else None)
                    ok, _err = _check_import(
                        resolved, roots, fallback_verdicts[resolved])
                    if not ok:
                        return True
                continue
            if isinstance(node, _FUNCTION_CONTAINER_TYPES):
                continue
            stack.extend(_ast.iter_child_nodes(node))
    return False
def _extract_imports(
        source: str,
) -> list[tuple[_ast.AST, str, int, tuple[str, ...],
                   tuple[_ast.AST, ...]]]:
    try:
        tree = _ast.parse(source)
    except PARSE_DEGRADE_EXC as exc:
        logger.warning("[Guard] 源码语法错误或解析爆栈,跳过导入提取: %s", exc)
        return []
    result: list[tuple[_ast.AST, str, int, tuple[str, ...],
                       tuple[_ast.AST, ...]]] = []
    for node, guard in _iter_required_import_nodes(tree):
        if isinstance(node, _ast.Import):
            result.extend((node, alias.name, 0, (), guard)
                          for alias in node.names)
        elif isinstance(node, _ast.ImportFrom):
            result.append((node, node.module or '', node.level or 0,
                           tuple(alias.name for alias in node.names), guard))
    return result
def _namespace_package_root(fpath: str, target_path: str) -> str:
    if not target_path:
        return ''
    file_dir = os.path.dirname(os.path.abspath(fpath))
    target = os.path.abspath(target_path)
    target_dir = target if os.path.isdir(target) else os.path.dirname(target)
    try:
        rel = os.path.relpath(file_dir, target_dir)
    except ValueError:
        return ''
    if rel != os.curdir and rel != os.pardir and not rel.startswith(
            os.pardir + os.sep):
        return target_dir
    current = file_dir
    while True:
        if os.path.isfile(os.path.join(current, '__init__.py')):
            regular_root = _outermost_package_root(current)
            if regular_root:
                return regular_root
        parent = os.path.dirname(current)
        if parent == current:
            break
        current = parent
    if rel == os.curdir:
        return os.path.dirname(file_dir)
    return ''
def _absolute_import_name(
    fpath: str, module_path: str, level: int, target_path: str = '',
) -> tuple[str | None, str | None]:
    if level <= 0:
        return module_path, None
    pkg_root = _outermost_package_root(os.path.dirname(os.path.abspath(fpath)))
    if not pkg_root:
        pkg_root = _namespace_package_root(fpath, target_path)
    if not pkg_root:
        return None, None
    fp_rel = os.path.relpath(os.path.abspath(fpath), pkg_root).replace('\\', '/')
    if fp_rel.startswith('../'):  # jwsgj:suppress SS-02 — 路径守卫判定，非路径访问
        return None, None
    depth = len([p for p in os.path.dirname(fp_rel).split('/') if p])
    if level - 1 >= depth:
        dotted = '.' * level + (module_path or '')
        return None, f"相对导入 {dotted} 超出顶层包范围"
    return _resolve_relative_module(fp_rel, level, module_path or None), None
def _check_source_imports(fpath: str, source: str, target: str,
                          roots_memo: dict[str, list[str]]) -> list[str]:
    roots = roots_memo.get(fpath)
    if roots is None:
        roots = _derive_fallback_roots(fpath, target)
        roots_memo[fpath] = roots
    imports = _extract_imports(source)
    if (any(level > 0 for _node, _module, level, _aliases, _guard in imports)
            and not _outermost_package_root(
                os.path.dirname(os.path.abspath(fpath)))):
        namespace_root = _namespace_package_root(fpath, target)
        if namespace_root:
            roots = _unique_roots([namespace_root, *roots])
            roots_memo[fpath] = roots
    errors: list[str] = []
    checked_modules: set[str] = set()
    checked_aliases: set[tuple[str, str]] = set()
    broken_modules: set[str] = set()
    fallback_verdicts: dict[str, bool | None] = {}
    for node, module_path, level, aliases, guards in imports:
        resolved, rel_error = _absolute_import_name(
            fpath, module_path, level, target)
        if rel_error is not None:
            errors.append(f"{fpath}: {rel_error}")
            continue
        if resolved is None or _should_skip_import(resolved):
            continue
        if (guards
                and _try_body_imports_broken(
                    fpath, target, guards, roots, fallback_verdicts)):
            continue
        if resolved not in fallback_verdicts:
            fallback_verdicts[resolved] = (
                _fallback_roots_check(resolved, roots) if roots else None)
        verdict = fallback_verdicts[resolved]
        if resolved not in checked_modules:
            checked_modules.add(resolved)
            ok, err = _check_import(resolved, roots, verdict)
            if not ok:
                broken_modules.add(resolved)
                errors.append(f"{fpath}: {err}")
        if resolved in broken_modules:
            continue
        errors.extend(_check_importfrom_aliases(
            fpath, resolved, module_path, level, aliases, roots, verdict,
            checked_aliases, node, source))
    return errors
def guard_imports(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _IMPORT_GUARD_OPS:
        return _passed("G4", "非导入相关操作,跳过导入检查")
    _target = ctx.target_path
    _roots_memo: dict[str, list[str]] = {}
    errors: list[str] = []
    for fpath, source in _iter_guard_py_sources(ctx):
        errors.extend(_check_source_imports(fpath, source, _target, _roots_memo))
    return _guard_outcome(
        "G4", "导入链", "导入链完整性检查通过", errors,
        "修复断裂的导入链.对于已删除的模块,更新导入语句.")
_SURFACE_CACHE: dict[
    str,
    tuple[tuple[int, int], tuple[set[str], bool, set[str]] | None],
] = {}
_SURFACE_CACHE_CAP = 128
def _module_alias_surface(
        surface_path: str,
        source: str | None = None) -> tuple[set[str], bool, set[str]] | None:
    if source is not None:
        return _read_alias_surface(surface_path, source)
    try:
        stat = os.stat(surface_path)
    except OSError as exc:
        logger.debug("[Guard] 导入面不可读: %s (%s)", surface_path, exc)
        return None
    cache_key = os.path.normcase(os.path.abspath(surface_path))
    signature = (stat.st_mtime_ns, stat.st_size)
    cached = _SURFACE_CACHE.get(cache_key)
    if cached is not None and cached[0] == signature:
        return cached[1]
    surface = _read_alias_surface(surface_path)
    if len(_SURFACE_CACHE) >= _SURFACE_CACHE_CAP:
        _SURFACE_CACHE.clear()
    _SURFACE_CACHE[cache_key] = (signature, surface)
    return surface
def _surface_module_name(surface_path: str) -> str | None:
    absolute = os.path.abspath(surface_path)
    pkg_root = _outermost_package_root(os.path.dirname(absolute))
    if not pkg_root:
        basename = os.path.basename(absolute)
        return (basename.removesuffix('.py')
                if basename.endswith('.py') and basename != '__init__.py'
                else None)
    rel = os.path.relpath(absolute, pkg_root).replace('\\', '/')
    if rel.endswith('/__init__.py'):
        rel = rel[:-len('/__init__.py')]
    else:
        rel = rel.removesuffix('.py')
    return '.'.join(part for part in rel.split('/') if part) or None
class _SelfImportStripper(_ast.NodeTransformer):
    def __init__(self, surface_path: str):
        self.surface_path = surface_path
        self.module_name = _surface_module_name(surface_path)
        self.self_bound: set[str] = set()
    def visit_ImportFrom(self, node):
        if self.module_name:
            resolved, rel_error = _absolute_import_name(
                self.surface_path, node.module or '', node.level)
            if rel_error is None and resolved == self.module_name:
                self.self_bound.update(
                    alias.asname or alias.name for alias in node.names
                    if alias.name != '*')
                return None
        return self.generic_visit(node)
def _binding_covered_by_later_deletes(
        events: list[_BindingEvent], event_index: int) -> bool:
    event = events[event_index]
    later_events = events[event_index + 1:]
    for later in later_events:
        if (later.deleted and len(later.control) <= len(event.control)
                and event.control[:len(later.control)] == later.control):
            return True
    shadow_events = [
        (later._replace(module=None if later.deleted else 'bound'), (None, ''))
        for later in later_events]
    return _ScopeBindingIndex._conditional_shadow_covers(
        shadow_events, event.control)
def _retain_final_alias_bindings(
        tree: _ast.Module, names: set[str],
        before: tuple[int, int] | None = None) -> set[str]:
    index = _scope_binding_index(tree, build_parent_map(tree))
    for name in tuple(names):
        events = [event for event in index.events
                  if event.local == name
                  and (before is None or event.position < before)]
        if before is None:
            ephemeral_definitions = {
                event.definition for event in events
                if event.deleted and event.definition is not None}
            if ephemeral_definitions:
                events = [event for event in events
                          if event.definition not in ephemeral_definitions]
                if not events:
                    names.discard(name)
                    continue
        binding_indices = [
            index for index, event in enumerate(events) if not event.deleted]
        if events and not binding_indices:
            names.discard(name)
            continue
        if binding_indices and all(
                _binding_covered_by_later_deletes(events, index)
                for index in binding_indices):
            names.discard(name)
    return names
def _alias_binding_evidence(
        tree: _ast.Module, surface_path: str,
        before: tuple[int, int] | None = None) -> tuple[set[str], set[str]]:
    stripper = _SelfImportStripper(surface_path)
    probe = stripper.visit(copy.deepcopy(tree))
    local, _globals, _classes = collect_shadow_bindings(probe)
    independent = set(local.get('', frozenset()))
    if before is not None:
        index = _scope_binding_index(probe, build_parent_map(probe))
        independent = {
            name for name in independent
            if any(event.local == name and not event.deleted
                   and event.position < before for event in index.events)
        }
    independent = _retain_final_alias_bindings(probe, independent, before)
    return independent, stripper.self_bound
def _self_import_prebindings(
        surface_path: str, import_node: _ast.AST,
        source: str | None = None) -> set[str] | None:
    if source is None:
        source = read_source(surface_path)
    if source is None:
        return None
    try:
        tree = _ast.parse(source, filename=surface_path)
    except PARSE_DEGRADE_EXC as exc:
        logger.debug("[Guard] 自导入面不可解析: %s (%s)", surface_path, exc)
        return None
    tree = _prune_non_import_time_branches(tree)
    independent, _self_bound = _alias_binding_evidence(
        tree, surface_path, _node_position(import_node))
    return independent
def _read_alias_surface(
        surface_path: str,
        source: str | None = None) -> tuple[set[str], bool, set[str]] | None:
    if source is None:
        source = read_source(surface_path)
    if source is None:
        return None
    try:
        tree = _ast.parse(source, filename=surface_path)
        tree = _prune_non_import_time_branches(tree)
        local, _globals, _classes = collect_shadow_bindings(tree)
        independent, self_bound = _alias_binding_evidence(tree, surface_path)
    except PARSE_DEGRADE_EXC as e:
        logger.debug("[Guard] 导入面不可解析,别名面按动态处理: %s (%s)",
                     surface_path, e)
        return None
    names = _retain_final_alias_bindings(
        tree, set(local.get('', frozenset())))
    names = (names - self_bound) | independent
    dynamic = '__getattr__' in names or any(
        is_star_import(stmt) for stmt in iter_module_level_stmts(tree))
    return names, dynamic, independent
def _fallback_surface_paths(
        module_path: str, level: int, fpath: str,
        fallback_roots: list[str]) -> list[tuple[str | None, str | None]]:
    namespace_surfaces: list[tuple[None, str]] = []
    seen_namespaces: set[str] = set()
    for root in fallback_roots:
        for cand in _importfrom_candidate_dirs_by_parts(
                module_path, level, root, fpath):
            real = os.path.abspath(cand)
            init_path = os.path.join(real, '__init__.py')
            if os.path.isfile(init_path):
                return [(init_path, real)]
            if os.path.isfile(real + '.py'):
                return [(real + '.py', None)]
            if os.path.isdir(real):
                key = _path_identity(real)
                if key not in seen_namespaces:
                    seen_namespaces.add(key)
                    namespace_surfaces.append((None, real))
    return namespace_surfaces
def _module_surface_paths(
        resolved: str, module_path: str, level: int, fpath: str,
        fallback_roots: list[str],
        fallback_verdict: bool | None) -> list[tuple[str | None, str | None]]:
    if level or fallback_verdict is not None:
        return _fallback_surface_paths(
            module_path, level, fpath, fallback_roots)
    module_file, package_dirs = _locate_module(resolved)
    package_surfaces = [
        (os.path.join(loc, '__init__.py'), loc)
        for loc in package_dirs
        if os.path.isfile(os.path.join(loc, '__init__.py'))]
    if package_surfaces:
        return package_surfaces
    namespace_surfaces = [
        (None, loc) for loc in package_dirs if os.path.isdir(loc)]
    if namespace_surfaces:
        return namespace_surfaces
    if module_file and module_file.lower().endswith(".py"):
        return [(module_file, None)]
    return _fallback_surface_paths(module_path, level, fpath, fallback_roots)
def _check_importfrom_aliases(
        fpath: str, resolved: str, module_path: str, level: int,
        aliases: tuple[str, ...], fallback_roots: list[str],
        fallback_verdict: bool | None,
        checked: set[tuple[str, str]],
        import_node: _ast.AST,
        current_source: str | None = None) -> list[str]:
    names = [alias for alias in aliases if alias != '*']
    if not names:
        return []
    surfaces = _module_surface_paths(
        resolved, module_path, level, fpath, fallback_roots,
        fallback_verdict)
    if not surfaces:
        return []
    confirmed: set[str] = set()
    uncertain = False
    self_key = _path_identity(fpath)
    self_bound = frozenset(import_alias_bound_names(import_node))
    for surface_path, pkg_dir in surfaces:
        if surface_path is None:
            bound, dynamic, independent = set(), False, set()
        else:
            is_self_surface = _path_identity(surface_path) == self_key
            surface = _module_alias_surface(
                surface_path, current_source if is_self_surface else None)
            if surface is None:
                uncertain = True
                continue
            bound, dynamic, independent = surface
        if dynamic:
            uncertain = True
            continue
        if (surface_path is not None
                and _path_identity(surface_path) == self_key):
            independent = _self_import_prebindings(
                surface_path, import_node, current_source)
            if independent is None:
                uncertain = True
                continue
            bound = (bound - self_bound) | independent
        confirmed.update(
            alias for alias in names
            if alias in bound
            or (pkg_dir is not None
                and _submodule_file_exists(pkg_dir, alias)))
    if uncertain:
        return []
    errors: list[str] = []
    for alias in names:
        key = (resolved, alias)
        if alias in confirmed or key in checked:
            continue
        checked.add(key)
        errors.append(f"{fpath}: 模块 {resolved}.{alias} 不存在")
    return errors

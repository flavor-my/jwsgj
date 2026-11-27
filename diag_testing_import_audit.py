from __future__ import annotations

import ast
import logging
import os
import sys
from collections import defaultdict, deque
from dataclasses import dataclass

from jwsgj.diag_shared_ast_nodes import (
    collect_param_names,
    dotted_name,
    first_segment,
    import_binds_of,
    iter_arg_nodes,
    iter_def_site_nodes,
    main_guard_node_ids,
    module_postpones_annotations,
)
from jwsgj.diag_testing_source import (
    TRY_STAR_T,
    FileCache,
    _entry_scan_root,
    _runtime_import_module_names,
    collect_module_assign_names,
    collect_scope_binding_names,
    collect_typing_tc_bindings,
    container_names_of_stmt,
    entry_import_node_dotted,
    entry_module_dotted,
    entry_nodes,
    entry_rel_path,
    is_main_entry_guard,
    iter_direct_scope_nodes,
    iter_module_binding_nodes,
    iter_module_level_stmts,
    module_entry_indexes,
    module_level_bound_names,
    nodes_where,
    record_module_import,
    reuse_or_build_import_graph,
    scope_direct_bindings,
    static_if_branch,
    type_checking_static_body,
)
from jwsgj.diag_types_defs import TestMethodResult
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import detect_cycles, is_test_file_path
from jwsgj.skill_profile import detect_layout

logger = logging.getLogger(__name__)
__all__ = [
    'ImportTopology',
    'analyze_import_topology',
    'annotate_structure_metrics',
    'broken_cross_call_findings',
    'collect_cross_module_calls',
    'collect_import_side_effects',
    'package_identity',
    'package_module_dotted',
    'resolve_broken_cross_calls',
    'root_init_entry',
    'scan_entry_import_findings',
]
_STDLIB_MODULE_NAMES = getattr(sys, "stdlib_module_names", frozenset())
def _lazy_import_target_is_stdlib(child: ast.AST) -> bool:
    if isinstance(child, ast.ImportFrom):
        if child.level:
            return False
        _root = (child.module or '').split('.')[0]
        return bool(_root) and _root in _STDLIB_MODULE_NAMES
    if isinstance(child, ast.Import):
        return all(a.name.split('.')[0] in _STDLIB_MODULE_NAMES
                   for a in child.names)
    return False
def _module_target_is_intra_package(module: str, internal_mods: set,
                                    pkg_name: str) -> bool:
    if not module:
        return False
    if pkg_name and (module == pkg_name
                     or module.startswith(pkg_name + '.')):
        return True
    return module in internal_mods
def _lazy_target_is_intra_package(child, internal_mods: set,
                                  pkg_name: str) -> bool:
    if isinstance(child, ast.ImportFrom):
        if child.level >= 1:
            return True
        _mod = child.module or ''
        if _module_target_is_intra_package(_mod, internal_mods, pkg_name):
            return True
        return any(
            _module_target_is_intra_package(
                f'{_mod}.{alias.name}' if _mod else alias.name,
                internal_mods, pkg_name)
            for alias in child.names if alias.name != '*')
    if isinstance(child, ast.Import):
        return all(_module_target_is_intra_package(
            alias.name, internal_mods, pkg_name) for alias in child.names)
    return False
def _assign_target_is_import_hook(target: ast.expr) -> bool:
    if isinstance(target, ast.Attribute):
        return target.attr == '__import__'
    if isinstance(target, ast.Subscript):
        return (isinstance(target.slice, ast.Constant)
                and target.slice.value == '__import__')
    return False
def _hook_install_target_name(assign) -> str | None:
    if not isinstance(assign.value, ast.Name):
        return None
    if not any(_assign_target_is_import_hook(t) for t in assign.targets):
        return None
    return assign.value.id
def _entry_hook_exempt_import_ids(entry) -> set:
    _import_hook_fn_names = {
        _name for _hn in nodes_where(entry, (ast.Assign,))
        if (_name := _hook_install_target_name(_hn)) is not None
    }
    _hook_exempt_import_ids = set()
    for _fn in nodes_where(entry, (ast.FunctionDef, ast.AsyncFunctionDef)):
        if _fn.name not in _import_hook_fn_names:
            continue
        for _c in walk_nodes(_fn):
            if isinstance(_c, (ast.Import, ast.ImportFrom)):
                _hook_exempt_import_ids.add(id(_c))
    return _hook_exempt_import_ids
@dataclass(frozen=True)
class _LazyScanContext:
    in_tests: bool
    try_import_ids: set
    hook_exempt_ids: set
    internal_mods: set
    pkg_name: str
def _lazy_import_is_exempt(child, ctx: _LazyScanContext,
                           reported_ids: set) -> bool:
    if id(child) in reported_ids:
        return True
    if id(child) in ctx.hook_exempt_ids:
        return True
    if isinstance(child, ast.Import):
        if all(_module_target_is_intra_package(
                alias.name, ctx.internal_mods, ctx.pkg_name)
               or alias.name.split('.')[0] in _STDLIB_MODULE_NAMES
               for alias in child.names):
            return True
    elif (_lazy_target_is_intra_package(
            child, ctx.internal_mods, ctx.pkg_name)
          or _lazy_import_target_is_stdlib(child)):
        return True
    if id(child) in ctx.try_import_ids:
        return True
    return ctx.in_tests
def _scan_entry_lazy_imports(entry, ctx: _LazyScanContext) -> list:
    out = []
    _rel_path = entry_rel_path(entry)
    _reported_import_ids: set[int] = set()
    for node in entry_nodes(entry):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        for child in iter_direct_scope_nodes(node, include_class_body=True):
            if not isinstance(child, (ast.Import, ast.ImportFrom)):
                continue
            if _lazy_import_is_exempt(child, ctx, _reported_import_ids):
                continue
            out.append({
                'file': _rel_path, 'line': child.lineno,
                'function': node.name,
                'type': 'lazy_import', 'severity': 'low',
                'message': f"函数内导入: {node.name}() 第 {child.lineno} 行",
            })
            _reported_import_ids.add(id(child))
    return out
def _index_try_body_imports(try_node, scoped: dict) -> None:
    stack = list(try_node.body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            scoped[id(node)] = (node, try_node)
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        stack.extend(ast.iter_child_nodes(node))
def _entry_try_body_imports(entry) -> dict:
    scoped: dict = {}
    for _tn in nodes_where(entry, (ast.Try, TRY_STAR_T)):
        if not _tn.handlers:
            continue
        _index_try_body_imports(_tn, scoped)
    return scoped
_FALLBACK_CATCH_TYPES = frozenset({"ImportError", "ModuleNotFoundError",
                                   "Exception"})
_FALLBACK_LOG_ATTRS = frozenset({"debug", "info", "warning", "warn", "error",
                                 "exception", "critical", "fatal", "log",
                                 "getLogger", "log_swallowed", "print"})
def _exception_type_catches_import_failure(node: ast.AST) -> bool:
    if isinstance(node, ast.Name):
        return node.id in _FALLBACK_CATCH_TYPES
    if (isinstance(node, ast.Attribute)
            and isinstance(node.value, ast.Name)
            and node.value.id == 'builtins'):
        return node.attr in _FALLBACK_CATCH_TYPES
    if isinstance(node, ast.Tuple):
        return any(_exception_type_catches_import_failure(elt)
                   for elt in node.elts)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.BitOr):
        return (_exception_type_catches_import_failure(node.left)
                or _exception_type_catches_import_failure(node.right))
    return False
def _handler_catches_import_failure(handler) -> bool:
    if handler.type is None:
        return True
    return _exception_type_catches_import_failure(handler.type)
def _is_fallback_statement(stmt) -> bool:
    if isinstance(stmt, (ast.Import, ast.ImportFrom, ast.Assign,
                         ast.AnnAssign, ast.Pass, ast.Return)):
        return True
    if not (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)):
        return False
    _func = stmt.value.func
    _attr = (_func.attr if isinstance(_func, ast.Attribute)
             else (_func.id if isinstance(_func, ast.Name) else None))
    return _attr in _FALLBACK_LOG_ATTRS
def _is_optional_dep_fallback(try_node) -> bool:
    handlers = getattr(try_node, 'handlers', None)
    if not handlers:
        return False
    import_handlers = [handler for handler in handlers
                       if _handler_catches_import_failure(handler)]
    return bool(import_handlers) and all(
        all(_is_fallback_statement(stmt) for stmt in handler.body)
        for handler in import_handlers)
def _scan_entry_conditional_imports(entry, try_imports: dict) -> list:
    out = []
    for child, try_node in sorted(try_imports.values(),
                                  key=lambda item: item[0].lineno):
        if (_lazy_import_target_is_stdlib(child)
                or _is_optional_dep_fallback(try_node)):
            continue
        out.append({
            'file': entry_rel_path(entry), 'line': child.lineno,
            'type': 'conditional_import', 'severity': 'low',
            'message': "条件导入 (try/except): 可能影响静态分析",
        })
    return out
def scan_entry_import_findings(cache, internal_mods) -> tuple:
    lazy_imports = []
    conditional_imports = []
    _pkg_name = package_identity(getattr(cache, 'skill_dir', '') or '')[1]
    _internal_names = set(internal_mods or ())
    _internal_names.update(
        dotted for entry in cache.valid_entries
        if (dotted := entry_module_dotted(entry)))
    for entry in cache.valid_entries:
        if entry.mod_stem == '__init__':
            continue
        _in_tests = is_test_file_path(entry_rel_path(entry))
        _try_imports = _entry_try_body_imports(entry)
        _lazy_ctx = _LazyScanContext(
            in_tests=_in_tests,
            try_import_ids=set(_try_imports),
            hook_exempt_ids=_entry_hook_exempt_import_ids(entry),
            internal_mods=_internal_names,
            pkg_name=_pkg_name,
        )
        lazy_imports.extend(_scan_entry_lazy_imports(entry, _lazy_ctx))
        if _in_tests:
            continue
        conditional_imports.extend(_scan_entry_conditional_imports(
            entry, _try_imports))
    return lazy_imports, conditional_imports
def _import_alias_to_module(entry) -> dict:
    _alias_to_mod: dict[str, str] = {}
    for imp in entry.imports:
        _a = imp.get('alias')
        if _a and imp.get('name'):
            _alias_to_mod[_a] = imp['name'].split('.')[-1]
    return _alias_to_mod
def _internal_module_target(dotted: str, internal_mods: set,
                            pkg_name: str) -> str | None:
    if dotted in internal_mods:
        return dotted
    leaf = dotted.rsplit('.', 1)[-1]
    if leaf not in internal_mods:
        return None
    if dotted == leaf:
        return leaf
    return leaf if pkg_name and dotted.startswith(pkg_name + '.') else None
def _logical_import_node_targets(node, entry, internal_mods: set,
                                 pkg_name: str) -> tuple:
    module_targets: dict[str, str | None] = {}
    symbol_targets: dict[str, tuple[str | None, str]] = {}
    if isinstance(node, ast.Import):
        for alias in node.names:
            ref = alias.asname or alias.name
            module_targets[ref] = _internal_module_target(
                alias.name, internal_mods, pkg_name)
        return module_targets, symbol_targets
    if not isinstance(node, ast.ImportFrom):
        return module_targets, symbol_targets
    base = entry_import_node_dotted(node, entry)
    if base is None:
        return module_targets, symbol_targets
    base_target = _internal_module_target(base, internal_mods, pkg_name)
    if base_target is None:
        base_target = _own_package_module_target(base, entry, internal_mods)
    base_in_own_package = base in _entry_ancestor_packages(entry)
    for alias in node.names:
        if alias.name == '*':
            continue
        ref = alias.asname or alias.name
        if base_target is not None:
            symbol_targets[ref] = (base_target, alias.name)
            continue
        if base_in_own_package and alias.name in internal_mods:
            # 基模块落在条目自身的包链内（含技能根包）：别名是包内子模块名
            # 即为模块目标，不能再要求点分名带包名前缀（点分名是技能根相对路径）。
            module_targets[ref] = alias.name
            continue
        submodule = _internal_module_target(
            '.'.join(part for part in (base, alias.name) if part),
            internal_mods, pkg_name)
        if submodule is not None:
            module_targets[ref] = submodule
        else:
            symbol_targets[ref] = (None, alias.name)
    return module_targets, symbol_targets
def _entry_ancestor_packages(entry) -> frozenset[str]:
    parts = [part for part in entry_rel_path(entry).replace('\\', '/').split('/')[:-1]
             if part and part != '.']
    return frozenset(
        '.'.join(parts[:end]) for end in range(len(parts) + 1))
def _own_package_module_target(dotted: str, entry,
                                 internal_mods: set) -> str | None:
    head, dot, leaf = dotted.rpartition('.')
    if dot and head in _entry_ancestor_packages(entry) and leaf in internal_mods:
        return leaf
    return None
def _logical_cross_call_context(entry, internal_mods: set) -> dict:
    _skill_dir = _entry_scan_root(entry)
    _pkg_name = package_identity(_skill_dir)[1] if _skill_dir else ''
    ctx = {
        'package_name': _pkg_name,
        'imported_names': _collect_imported_names(entry),
        'local_assign_names': collect_module_assign_names(entry.tree),
        'alias_to_mod': _import_alias_to_module(entry),
        'binding_ranges': None,
        'module_import_names': _module_level_import_names(entry.tree),
        'local_import_ranges': None,
        'module_binding_events': None,
        'import_target_events': None,
    }
    ctx['import_target_events'] = _runtime_import_target_events(
        entry, ctx,
        target_resolver=lambda node: _logical_import_node_targets(
            node, entry, internal_mods, _pkg_name))
    return ctx
def collect_cross_module_calls(entry, internal_mods: set) -> set:
    called: set = set()
    ctx = _logical_cross_call_context(entry, internal_mods)
    imported_refs = ctx['imported_names']
    for node in entry_nodes(entry):
        if not isinstance(node, ast.Call):
            continue
        line = getattr(node, 'lineno', 0) or 0
        column = getattr(node, 'col_offset', None)
        if isinstance(node.func, ast.Name):
            ref = node.func.id
            found, target_mod, symbol = _call_import_target_event(
                entry, ctx, ref, line, column, 'symbol')
            if not found or target_mod not in internal_mods:
                continue
            if not _call_has_visible_import(
                    entry, ctx, ref, line, column):
                continue
            if _call_is_shadowed_locally(
                    entry, ctx, ref, line, column):
                continue
            called.add(symbol)
            continue
        if not isinstance(node.func, ast.Attribute):
            continue
        path = dotted_name(node.func)
        module = path.rpartition('.')[0]
        if not module:
            continue
        found, target_mod, _symbol = _call_import_target_event(
            entry, ctx, module, line, column, 'module')
        if not found:
            if (module in ctx['import_target_events']['module']
                    or module in ctx['import_target_events']['symbol']):
                continue
            target_mod = (module if module in internal_mods
                          else ctx['alias_to_mod'].get(module))
            if target_mod is None and (
                    module in imported_refs
                    or module.split('.')[0] in imported_refs):
                target_mod = _internal_module_target(
                    module, internal_mods, ctx['package_name'])
        if target_mod not in internal_mods:
            continue
        if not _call_has_visible_import(
                entry, ctx, module, line, column):
            continue
        if _call_is_shadowed_locally(
                entry, ctx, module, line, column):
            continue
        called.add(node.func.attr)
    return called
_COMPREHENSION_NODE_TYPES = (ast.ListComp, ast.SetComp, ast.DictComp,
                             ast.GeneratorExp)
_SCOPE_NODE_TYPES = ((ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
                      ast.ClassDef) + _COMPREHENSION_NODE_TYPES)
_SourcePosition = tuple[int, int]
_SourceRange = tuple[_SourcePosition, _SourcePosition]
def _collect_imported_names(entry) -> set:
    names: set[str] = set()
    for node in entry_nodes(entry):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            names |= import_binds_of(node)
    return names
def _scope_parents(tree: ast.AST) -> dict[ast.AST, ast.AST | None]:
    parents: dict[ast.AST, ast.AST | None] = {}
    stack: list[tuple[ast.AST, ast.AST | None]] = [(tree, None)]
    while stack:
        node, parent = stack.pop()
        if isinstance(node, _SCOPE_NODE_TYPES):
            parents[node] = parent
            parent = node
        stack.extend((child, parent) for child in ast.iter_child_nodes(node))
    return parents
def _direct_global_names(scope: ast.AST) -> set[str]:
    return {name for node in iter_direct_scope_nodes(scope)
            if isinstance(node, ast.Global) for name in node.names}
def _direct_nonlocal_names(scope: ast.AST) -> set[str]:
    return {name for node in iter_direct_scope_nodes(scope)
            if isinstance(node, ast.Nonlocal) for name in node.names}
def _node_start(node: ast.AST) -> _SourcePosition:
    return (getattr(node, 'lineno', 0) or 0,
            getattr(node, 'col_offset', 0) or 0)
def _node_end(node: ast.AST) -> _SourcePosition:
    start = _node_start(node)
    end_col = getattr(node, 'end_col_offset', None)
    return (getattr(node, 'end_lineno', None) or start[0],
            start[1] if end_col is None else end_col)
def _node_range(node: ast.AST) -> _SourceRange:
    return _node_start(node), _node_end(node)
def _scope_execution_range(scope: ast.AST) -> _SourceRange | None:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        body = scope.body
        return (_node_start(body[0]), _node_end(scope)) if body else None
    if isinstance(scope, ast.Lambda):
        return _node_range(scope.body)
    if isinstance(scope, _COMPREHENSION_NODE_TYPES):
        return _node_range(scope)
    return None
def _binding_event_position(stmt) -> _SourcePosition:
    line = getattr(stmt, 'lineno', None)
    if line is None:
        line = getattr(getattr(stmt, 'context_expr', None), 'lineno', 0)
    column = getattr(stmt, 'col_offset', 0) or 0
    binding_site = None
    if isinstance(stmt, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
        binding_site = stmt
    elif isinstance(stmt, ast.NamedExpr):
        binding_site = stmt.value
    elif isinstance(stmt, (ast.For, ast.AsyncFor)):
        binding_site = stmt.iter
    elif isinstance(stmt, ast.withitem):
        binding_site = stmt.context_expr
    if binding_site is not None:
        line = getattr(binding_site, 'end_lineno', None) or line
        column = getattr(binding_site, 'end_col_offset', None) or column
    return line, column
def _declared_outer_binding_ranges(scope: ast.AST) -> dict:
    declared = _direct_global_names(scope) | _direct_nonlocal_names(scope)
    own_range = _scope_execution_range(scope)
    if not declared or own_range is None:
        return {}
    end = own_range[1]
    ranges: dict[str, list[_SourceRange]] = {name: [] for name in declared}
    for stmt in iter_direct_scope_nodes(scope):
        bound_names: set[str] = set()
        declared_outer: set[str] = set()
        collect_scope_binding_names(stmt, bound_names, declared_outer)
        for name in bound_names & declared:
            start = _binding_event_position(stmt)
            if start < end:
                ranges[name].append((start, end))
    return ranges
def _subtract_source_ranges(ranges: list[_SourceRange],
                            excluded: _SourceRange) -> list[_SourceRange]:
    excluded_start, excluded_end = excluded
    if excluded_start >= excluded_end:
        return ranges
    remaining: list[_SourceRange] = []
    for start, end in ranges:
        if excluded_end <= start or excluded_start >= end:
            remaining.append((start, end))
            continue
        if start < excluded_start:
            remaining.append((start, min(end, excluded_start)))
        right_start = max(start, excluded_end)
        if right_start < end:
            remaining.append((right_start, end))
    return remaining
def _ordered_import_binding_ranges(
        scope: ast.AST, active_ranges: list[_SourceRange],
) -> dict[str, list[_SourceRange]]:
    if not isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)):
        return {}
    declared = _direct_global_names(scope) | _direct_nonlocal_names(scope)
    events: dict[str, list[tuple[_SourcePosition, str]]] = defaultdict(list)
    for stmt in iter_direct_scope_nodes(scope):
        position = _binding_event_position(stmt)
        bound_names: set[str] = set()
        declared_outer: set[str] = set()
        collect_scope_binding_names(stmt, bound_names, declared_outer)
        for name in bound_names - declared:
            events[name].append((position, 'assign'))
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            for name in import_binds_of(stmt) - declared:
                events[name].append((position, 'import'))
    is_function = isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef))
    result: dict[str, list[_SourceRange]] = {}
    for name, name_events in events.items():
        if not any(kind == 'import' for _position, kind in name_events):
            continue
        ordered = sorted(name_events, key=lambda event: event[0])
        intervals: list[_SourceRange] = []
        for range_start, end in active_ranges:
            cursor = range_start
            state = 'assign' if is_function else None
            for start, kind in ordered:
                if start <= range_start:
                    state = kind
                    continue
                if start >= end:
                    break
                if state == 'assign' and cursor < start:
                    intervals.append((cursor, start))
                cursor = start
                state = kind
            if state == 'assign' and cursor < end:
                intervals.append((cursor, end))
        result[name] = intervals
    return result


def _nonlocal_import_unshadow_ranges(scope: ast.AST) -> dict:
    declared = _direct_nonlocal_names(scope)
    own_range = _scope_execution_range(scope)
    if not declared or own_range is None:
        return {}
    events: dict[str, list[tuple[_SourcePosition, str]]] = defaultdict(list)
    for stmt in iter_direct_scope_nodes(scope):
        position = _binding_event_position(stmt)
        bound_names: set[str] = set()
        declared_outer: set[str] = set()
        collect_scope_binding_names(stmt, bound_names, declared_outer)
        for name in bound_names & declared:
            events[name].append((position, 'assign'))
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            for name in import_binds_of(stmt) & declared:
                events[name].append((position, 'import'))
    result: dict[str, list[_SourceRange]] = {}
    for name, name_events in events.items():
        ordered = sorted(name_events, key=lambda event: event[0])
        for index, (start, kind) in enumerate(ordered):
            if kind != 'import':
                continue
            end = (ordered[index + 1][0]
                   if index + 1 < len(ordered) else own_range[1])
            if start < end:
                result.setdefault(name, []).append((start, end))
    return result


def _collect_scope_binding_ranges(tree: ast.AST) -> dict:
    parents = _scope_parents(tree)
    execution_ranges: dict[ast.AST, list[_SourceRange]] = {}
    for scope in parents:
        own_range = _scope_execution_range(scope)
        ranges = [own_range] if own_range is not None else []
        if isinstance(scope, _COMPREHENSION_NODE_TYPES) and scope.generators:
            ranges = _subtract_source_ranges(
                ranges, _node_range(scope.generators[0].iter))
        execution_ranges[scope] = ranges
    binding_ranges = dict(execution_ranges)
    for scope in parents:
        if not isinstance(scope, ast.ClassDef):
            continue
        ranges = list(execution_ranges[scope])
        for nested in parents:
            if nested is scope:
                continue
            ancestor = parents[nested]
            while ancestor is not None and ancestor is not scope:
                ancestor = parents[ancestor]
            if ancestor is not scope:
                continue
            for excluded in execution_ranges[nested]:
                ranges = _subtract_source_ranges(ranges, excluded)
        binding_ranges[scope] = ranges
    ranges_by_scope: dict[ast.AST, dict[str, list[_SourceRange]]] = {}
    import_ranges_by_scope: dict[
        ast.AST, dict[str, list[_SourceRange]]] = {}
    for scope in parents:
        bound_names = scope_direct_bindings(scope)
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            bound_names |= collect_param_names(scope)
        ranges_by_scope[scope] = {
            name: list(binding_ranges[scope]) for name in bound_names}
        if isinstance(scope, ast.ClassDef):
            binding_starts: dict[str, _SourcePosition] = {}
            for stmt in iter_direct_scope_nodes(scope):
                stmt_names: set[str] = set()
                declared_outer: set[str] = set()
                collect_scope_binding_names(
                    stmt, stmt_names, declared_outer)
                for name in stmt_names & bound_names:
                    start = _binding_event_position(stmt)
                    binding_starts[name] = min(
                        start, binding_starts.get(name, start))
            for name, start in binding_starts.items():
                intervals: list[_SourceRange] = []
                for range_start, end in binding_ranges[scope]:
                    visible_start = max(start, range_start)
                    if visible_start < end:
                        intervals.append((visible_start, end))
                ranges_by_scope[scope][name] = intervals
        if isinstance(scope, _COMPREHENSION_NODE_TYPES):
            previous_targets: set[str] = set()
            for generator in scope.generators:
                target_names: set[str] = set()
                declared_outer: set[str] = set()
                collect_scope_binding_names(
                    generator, target_names, declared_outer)
                for name in target_names - previous_targets:
                    intervals = ranges_by_scope[scope].get(name)
                    if intervals is not None:
                        ranges_by_scope[scope][name] = _subtract_source_ranges(
                            intervals, _node_range(generator.iter))
                previous_targets |= target_names
        import_ranges = _ordered_import_binding_ranges(
            scope, binding_ranges[scope])
        import_ranges_by_scope[scope] = import_ranges
        ranges_by_scope[scope].update(import_ranges)
        for name, intervals in _declared_outer_binding_ranges(scope).items():
            ranges_by_scope[scope][name] = intervals
    for scope, import_ranges in import_ranges_by_scope.items():
        for name in import_ranges:
            ancestor = parents[scope]
            while ancestor is not None:
                ancestor_ranges = ranges_by_scope[ancestor].get(name)
                if ancestor_ranges is not None:
                    for excluded in binding_ranges[scope]:
                        ancestor_ranges = _subtract_source_ranges(
                            ancestor_ranges, excluded)
                    ranges_by_scope[ancestor][name] = ancestor_ranges
                ancestor = parents[ancestor]
    for scope in parents:
        unshadow_ranges = _nonlocal_import_unshadow_ranges(scope)
        for name, excluded_ranges in unshadow_ranges.items():
            current = scope
            while current is not None:
                current_ranges = ranges_by_scope[current].get(name)
                if current_ranges is not None:
                    for excluded in excluded_ranges:
                        current_ranges = _subtract_source_ranges(
                            current_ranges, excluded)
                    ranges_by_scope[current][name] = current_ranges
                current = parents[current]
    for scope in parents:
        global_names = _direct_global_names(scope)
        if not global_names:
            continue
        ancestor = parents[scope]
        while ancestor is not None:
            ancestor_ranges = ranges_by_scope[ancestor]
            for name in global_names:
                for excluded in binding_ranges[scope]:
                    if name in ancestor_ranges:
                        ancestor_ranges[name] = _subtract_source_ranges(
                            ancestor_ranges[name], excluded)
            ancestor = parents[ancestor]
    ranges: dict[str, list[_SourceRange]] = {}
    for scope_ranges in ranges_by_scope.values():
        for name, intervals in scope_ranges.items():
            ranges.setdefault(name, []).extend(intervals)
    return ranges
def _call_in_bound_scope(binding_ranges: dict, name: str, line,
                         column=None) -> bool:
    if not name:
        return False
    ranges = binding_ranges.get(name, ())
    if not isinstance(column, int) or isinstance(column, bool):
        return any(start[0] <= line <= end[0] for start, end in ranges)
    position = (line, column)
    return any(start <= position < end for start, end in ranges)
def _module_level_import_names(tree: ast.AST) -> frozenset[str]:
    names: set[str] = set()
    for stmt in iter_module_level_stmts(getattr(tree, 'body', ()) or ()):
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            names |= import_binds_of(stmt)
    return frozenset(names)
def _local_import_binding_ranges(tree: ast.AST) -> dict[str, list[_SourceRange]]:
    parents = _scope_parents(tree)
    ranges: dict[str, list[_SourceRange]] = {}
    for scope in parents:
        own_range = _scope_execution_range(scope)
        if own_range is None:
            continue
        active_ranges = [own_range]
        if isinstance(scope, ast.ClassDef):
            for nested, parent in parents.items():
                ancestor = parent
                while ancestor is not None and ancestor is not scope:
                    ancestor = parents[ancestor]
                if ancestor is not scope:
                    continue
                excluded = _scope_execution_range(nested)
                if excluded is not None:
                    active_ranges = _subtract_source_ranges(
                        active_ranges, excluded)
        for stmt in iter_direct_scope_nodes(scope):
            if not isinstance(stmt, (ast.Import, ast.ImportFrom)):
                continue
            start = _binding_event_position(stmt)
            for range_start, end in active_ranges:
                visible_start = max(start, range_start)
                if visible_start >= end:
                    continue
                for name in import_binds_of(stmt):
                    ranges.setdefault(name, []).append((visible_start, end))
    return ranges
def _call_has_visible_import(entry, ctx: dict, ref: str, line: int,
                             column) -> bool:
    root = first_segment(ref)
    if root in ctx['module_import_names']:
        return True
    if ctx['local_import_ranges'] is None:
        ctx['local_import_ranges'] = _local_import_binding_ranges(entry.tree)
    return _call_in_bound_scope(
        ctx['local_import_ranges'], root, line, column)
def package_identity(skill_dir: str) -> tuple[str, str]:
    layout = detect_layout(skill_dir)
    return (layout.package_root or skill_dir,
            layout.package_name or os.path.basename(os.path.normpath(skill_dir)))
def _module_relative_parts(entry_path: str,
                           package_root: str) -> list[str] | None:
    try:
        rel_path = os.path.relpath(entry_path, package_root)
    except ValueError:
        return None
    if os.path.isabs(rel_path):
        return None
    parts = rel_path.replace('\\', '/').split('/')[:-1]
    return None if '..' in parts else parts
def package_module_dotted(entry, package_root: str) -> str | None:
    parts = _module_relative_parts(entry.path, package_root)
    if parts is None:
        return None
    if not entry.is_init:
        parts = [*parts, os.path.splitext(os.path.basename(entry.path))[0]]
    return '.'.join(parts)
def _runtime_module_indexes(cache, package_root: str) -> tuple[dict, dict]:
    by_path, by_stem = module_entry_indexes(cache)
    by_path = dict(by_path)
    for entry in cache.valid_entries:
        dotted = package_module_dotted(entry, package_root)
        if dotted is not None:
            by_path[dotted] = entry
    return by_path, by_stem
def root_init_entry(cache, package_root: str):
    if not package_root:
        return cache.init_entry
    for entry in cache.valid_entries:
        if (entry.is_init
                and package_module_dotted(entry, package_root) == ''):
            return entry
    return None
def _module_report_name(entry, package_root: str) -> str:
    dotted = package_module_dotted(entry, package_root)
    if dotted is not None:
        return dotted or '__init__'
    return entry_module_dotted(entry) or entry.mod_stem
def _module_path_has_suffix(entry, dotted: str) -> bool:
    entry_dotted = entry_module_dotted(entry)
    if not entry_dotted:
        return False
    return entry_dotted == dotted or entry_dotted.endswith('.' + dotted)
def _module_entry_for(dotted: str, module_indexes, package_name: str,
                      internal_mods: set | None):
    by_path, by_stem = module_indexes
    if not dotted:
        return by_path.get('')
    target = by_path.get(dotted)
    if target is not None:
        # 技能根相对点分名（如 src/pkg 布局的 src.pkg.c）本身就是条目路径键，
        # 精确命中即内部模块，不受首段内部名门禁限制。
        return target
    _first = dotted.split('.', 1)[0]
    if package_name and (dotted == package_name
                         or dotted.startswith(package_name + '.')):
        dotted = dotted[len(package_name):].lstrip('.')
        if not dotted:
            return by_path.get('')
    elif not ((internal_mods and _first in internal_mods)
              or _first in by_path):
        return None
    target = by_path.get(dotted)
    if target is not None:
        return target
    candidates = [entry for entry in by_stem.get(dotted.rsplit('.', 1)[-1], ())
                  if _module_path_has_suffix(entry, dotted)]
    return candidates[0] if len(candidates) == 1 else None
def _import_node_targets(node, entry, module_indexes, package_name: str,
                         internal_mods: set | None) -> tuple[dict, dict]:
    module_targets: dict[str, object] = {}
    symbol_targets: dict[str, tuple[object, str]] = {}
    if isinstance(node, ast.Import):
        for alias in node.names:
            target = _module_entry_for(
                alias.name, module_indexes, package_name, internal_mods)
            ref = alias.asname or alias.name
            if target is not None and ref:
                module_targets[ref] = target
        return module_targets, symbol_targets
    if not isinstance(node, ast.ImportFrom):
        return module_targets, symbol_targets
    base = entry_import_node_dotted(node, entry)
    if base is None:
        return module_targets, symbol_targets
    for alias in node.names:
        if alias.name == '*':
            continue
        ref = alias.asname or alias.name
        submodule = _module_entry_for(
            '.'.join(part for part in (base, alias.name) if part),
            module_indexes, package_name, internal_mods)
        if submodule is not None:
            module_targets[ref] = submodule
            continue
        target = _module_entry_for(
            base, module_indexes, package_name, internal_mods)
        if target is not None and ref:
            symbol_targets[ref] = (target, alias.name)
    return module_targets, symbol_targets
def _entry_import_targets(entry, module_indexes, package_name: str,
                          internal_mods: set | None) -> tuple[dict, dict]:
    module_targets: dict[str, object] = {}
    symbol_targets: dict[str, tuple[object, str]] = {}
    for node in entry_nodes(entry):
        node_modules, node_symbols = _import_node_targets(
            node, entry, module_indexes, package_name, internal_mods)
        for ref, target in node_modules.items():
            module_targets.setdefault(ref, target)
        for ref, target in node_symbols.items():
            symbol_targets.setdefault(ref, target)
    return module_targets, symbol_targets
def _resolve_import_target(ref: str, ctx: dict):
    import_targets = ctx.get('import_targets', {})
    target = import_targets.get(ref)
    if target is not None or not ref:
        return target
    module_indexes = ctx.get('module_indexes')
    if module_indexes is None:
        return None
    by_path, _by_stem = module_indexes
    for prefix in sorted(import_targets, key=len, reverse=True):
        if not ref.startswith(prefix + '.'):
            continue
        base = import_targets[prefix]
        base_dotted = entry_module_dotted(base)
        suffix = ref[len(prefix):].strip('.')
        dotted = '.'.join(part for part in (base_dotted, suffix) if part)
        target = by_path.get(dotted)
        if target is not None:
            return target
    if any(name.startswith(ref + '.') for name in import_targets):
        return _module_entry_for(
            ref, module_indexes, ctx.get('package_name', ''),
            ctx.get('internal_mods'))
    return None
def _entry_cross_call_context(entry, module_indexes, package_name: str,
                              internal_mods: set | None,
                              package_root: str) -> dict:
    import_targets, symbol_targets = _entry_import_targets(
        entry, module_indexes, package_name, internal_mods)
    return {
        'imported_names': _collect_imported_names(entry),
        'local_assign_names': collect_module_assign_names(entry.tree),
        'alias_to_mod': _import_alias_to_module(entry),
        'binding_ranges': None,
        'module_import_names': _module_level_import_names(entry.tree),
        'local_import_ranges': None,
        'import_targets': import_targets,
        'symbol_targets': symbol_targets,
        'module_indexes': module_indexes,
        'package_name': package_name,
        'internal_mods': internal_mods,
        'package_root': package_root,
        'module_binding_events': None,
        'import_target_events': None,
    }
def _runtime_import_target_events(entry, ctx, target_resolver=None) -> dict:
    events = {'module': defaultdict(list), 'symbol': defaultdict(list)}
    tree = getattr(entry, 'tree', None)
    if tree is None:
        return events
    if target_resolver is None:
        def target_resolver(node):
            return _import_node_targets(
                node, entry, ctx['module_indexes'], ctx['package_name'],
                ctx['internal_mods'])
    target_cache = {}

    def record(node, ranges, *, deferred: bool = False) -> None:
        if id(node) not in target_cache:
            target_cache[id(node)] = target_resolver(node)
        module_targets, symbol_targets = target_cache[id(node)]
        refs = []
        if isinstance(node, ast.Import):
            refs = [(alias.asname or alias.name, 'module', '')
                    for alias in node.names]
        elif isinstance(node, ast.ImportFrom):
            for alias in node.names:
                if alias.name == '*':
                    continue
                ref = alias.asname or alias.name
                kind = 'module' if ref in module_targets else 'symbol'
                refs.append((ref, kind, alias.name))
        start = _binding_event_position(node)
        for range_start, end in ranges:
            visible_start = (range_start if deferred
                             else max(start, range_start))
            if end is not None and visible_start >= end:
                continue
            for ref, kind, original_symbol in refs:
                if kind == 'module':
                    target, symbol = module_targets.get(ref), ''
                else:
                    target, symbol = symbol_targets.get(
                        ref, (None, original_symbol))
                events[kind][ref].append(
                    (visible_start, end, target, symbol))
    module_imports = [
        stmt for stmt in iter_module_level_stmts(
            getattr(tree, 'body', ()) or ())
        if isinstance(stmt, (ast.Import, ast.ImportFrom))]
    for stmt in module_imports:
        record(stmt, [((0, 0), None)])
    parents = _scope_parents(tree)
    for scope in parents:
        own_range = _scope_execution_range(scope)
        if own_range is None:
            continue
        active_ranges = [own_range]
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.Lambda)):
            for stmt in module_imports:
                record(stmt, [own_range], deferred=True)
        if isinstance(scope, ast.ClassDef):
            for nested, parent in parents.items():
                ancestor = parent
                while ancestor is not None and ancestor is not scope:
                    ancestor = parents[ancestor]
                if ancestor is not scope:
                    continue
                excluded = _scope_execution_range(nested)
                if excluded is not None:
                    active_ranges = _subtract_source_ranges(
                        active_ranges, excluded)
        for stmt in iter_direct_scope_nodes(scope):
            if isinstance(stmt, (ast.Import, ast.ImportFrom)):
                record(stmt, [(start, end) for start, end in active_ranges])
    return events
def _call_import_target_event(entry, ctx, ref: str, line: int,
                              column, kind: str):
    if ctx['import_target_events'] is None:
        ctx['import_target_events'] = _runtime_import_target_events(entry, ctx)
    candidates = []
    for event in ctx['import_target_events'][kind].get(ref, ()):
        start, end, _target, _symbol = event
        if isinstance(column, int) and not isinstance(column, bool):
            position = (line, column)
            visible = start <= position and (end is None or position < end)
        else:
            visible = start[0] <= line and (end is None or line <= end[0])
        if visible:
            candidates.append(event)
    if not candidates:
        return False, None, ''
    _start, _end, target, symbol = max(
        candidates, key=lambda event: event[0])
    return True, target, symbol
def _module_binding_events(entry) -> dict:
    events: dict[str, list[tuple[int, int, str]]] = defaultdict(list)
    tree = getattr(entry, 'tree', None)
    if tree is None:
        return events
    for stmt in iter_module_level_stmts(getattr(tree, 'body', ()) or ()):
        line, column = _binding_event_position(stmt)
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            for name in import_binds_of(stmt):
                events[name].append((line, column, 'import'))
            continue
        bound_names: set[str] = set()
        declared_outer: set[str] = set()
        collect_scope_binding_names(stmt, bound_names, declared_outer)
        for name in bound_names - declared_outer:
            events[name].append((line, column, 'assign'))
    return events
def _call_is_shadowed_locally(entry, ctx, orig_ref, call_line,
                              call_column) -> bool:
    root_ref = first_segment(orig_ref)
    if root_ref in ctx['local_assign_names']:
        if ctx['module_binding_events'] is None:
            ctx['module_binding_events'] = _module_binding_events(entry)
        events = ctx['module_binding_events'].get(root_ref, ())
        column = (call_column
                  if isinstance(call_column, int)
                  and not isinstance(call_column, bool) else float('inf'))
        prior = [event for event in events
                 if (event[0], event[1]) <= (call_line, column)]
        if prior:
            if max(prior)[2] != 'import':
                return True
        elif not events:
            return True
    if ctx['binding_ranges'] is None:
        ctx['binding_ranges'] = _collect_scope_binding_ranges(entry.tree)
    return _call_in_bound_scope(
        ctx['binding_ranges'], root_ref, call_line, call_column)
@dataclass(frozen=True)
class _ModuleSurface:
    names: frozenset
    open_attribute_surface: bool
    def defines(self, name: str) -> bool:
        return self.open_attribute_surface or name in self.names
def _module_attribute_surface_is_open(tree: ast.AST | None) -> bool:
    if tree is None:
        return False
    for node in iter_module_level_stmts(getattr(tree, 'body', [])):
        if isinstance(node, ast.ImportFrom) and any(
                alias.name == '*' for alias in node.names):
            return True
        if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and node.name == '__getattr__'):
            return True
    return False
def _module_surface(entry) -> _ModuleSurface:
    tree = getattr(entry, 'tree', None)
    if tree is None:
        names = {f.get('name') for f in getattr(entry, 'functions', ()) or ()}
        names |= {c.get('name') for c in getattr(entry, 'classes', ()) or ()}
        names.discard(None)
        return _ModuleSurface(frozenset(names), False)
    return _ModuleSurface(
        frozenset(module_level_bound_names(tree, include_imports=True)),
        _module_attribute_surface_is_open(tree))
def _detect_broken_call_finding(entry, call, ctx, internal_mods,
                                entries_by_stem, surfaces):
    callee = call.get('name', '')
    _call_line = call.get('line', 0) or 0
    _call_column = call.get('column')
    _orig_ref = call.get('module', '') or ''
    if not _orig_ref:
        return _detect_symbol_call_finding(
            entry, callee, _call_line, _call_column, ctx, surfaces)
    target_found, target_entry, _symbol = _call_import_target_event(
        entry, ctx, _orig_ref, _call_line, _call_column, 'module')
    if not target_found and (
            _orig_ref in ctx['import_target_events']['module']
            or _orig_ref in ctx['import_target_events']['symbol']):
        return None
    if not target_found:
        target_entry = _resolve_import_target(_orig_ref, ctx)
    if target_found and target_entry is None:
        return None
    if target_entry is not None:
        mod_ref = _module_report_name(target_entry, ctx['package_root'])
    else:
        mod_ref = (_orig_ref if _orig_ref in internal_mods
                   else ctx['alias_to_mod'].get(_orig_ref))
        if not (mod_ref and mod_ref in internal_mods):
            return None
        if mod_ref not in ctx['imported_names']:
            return None
        target_entry = entries_by_stem.get(mod_ref)
        if not target_entry:
            return None
    if not _call_has_visible_import(
            entry, ctx, _orig_ref, _call_line, _call_column):
        return None
    if _call_is_shadowed_locally(
            entry, ctx, _orig_ref, _call_line, _call_column):
        return None
    if surfaces[id(target_entry)].defines(callee):
        return None
    return _broken_call_record(entry, _call_line, mod_ref, callee)
def _detect_symbol_call_finding(entry, callee: str, call_line: int,
                                call_column, ctx: dict, surfaces) -> dict | None:
    target_found, target_entry, symbol = _call_import_target_event(
        entry, ctx, callee, call_line, call_column, 'symbol')
    if not target_found and (
            callee in ctx['import_target_events']['symbol']):
        return None
    if not target_found:
        symbol_target = ctx.get('symbol_targets', {}).get(callee)
        if symbol_target is None:
            return None
        target_entry, symbol = symbol_target
    elif target_entry is None:
        return None
    if not _call_has_visible_import(
            entry, ctx, callee, call_line, call_column):
        return None
    if _call_is_shadowed_locally(
            entry, ctx, callee, call_line, call_column):
        return None
    if surfaces[id(target_entry)].defines(symbol):
        return None
    mod_ref = _module_report_name(target_entry, ctx['package_root'])
    return _broken_call_record(entry, call_line, mod_ref, symbol)
def _broken_call_record(entry, call_line: int, mod_ref: str,
                        symbol: str) -> dict:
    return {
        'file': entry_rel_path(entry), 'line': call_line,
        'type': 'broken_cross_call', 'severity': 'high',
        'symbol': f'{mod_ref}.{symbol}',
        'message': f'跨模块调用断裂: {mod_ref}.{symbol}() 目标不存在',
    }
def broken_cross_call_findings(cache, internal_mods=None) -> list:
    if internal_mods is None:
        internal_mods = getattr(cache, "internal_mods", None) or set()
    _package_root, _package_name = package_identity(
        getattr(cache, 'skill_dir', '') or '')
    module_indexes = _runtime_module_indexes(cache, _package_root)
    _entries_by_stem: dict = {}
    for e in cache.valid_entries:
        _entries_by_stem.setdefault(e.mod_stem, e)
    _surfaces = {id(e): _module_surface(e) for e in cache.valid_entries}
    findings: list = []
    for entry in cache.valid_entries:
        if is_test_file_path(entry_rel_path(entry)):
            continue
        _ctx = _entry_cross_call_context(
            entry, module_indexes, _package_name, internal_mods, _package_root)
        for call in entry.calls:
            _finding = _detect_broken_call_finding(
                entry, call, _ctx, internal_mods, _entries_by_stem, _surfaces)
            if _finding is not None:
                findings.append(_finding)
    return findings
def resolve_broken_cross_calls(cache: FileCache, result: TestMethodResult,
                               internal_mods: set[str] | None = None) -> int:
    findings = broken_cross_call_findings(cache, internal_mods)
    result.findings.extend(findings)
    return len(findings)
def _iter_runtime_module_nodes(tree: ast.AST):
    typing_refs, tc_binds = collect_typing_tc_bindings(
        iter_module_binding_nodes(tree))
    stack: list[tuple[ast.AST, int, int]] = [(tree, 0, 0)]
    while stack:
        node, _fd, _td = stack.pop()
        yield node, _fd, _td
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            stack.extend((c, _fd + 1, _td)
                         for c in ast.iter_child_nodes(node))
        elif is_main_entry_guard(node):
            stack.append((node.test, _fd, _td))
            stack.extend((c, _fd, _td) for c in node.orelse)
        elif _td == 0 and (static_body := type_checking_static_body(
                node, typing_refs, tc_binds)) is not None:
            stack.append((node.test, _fd, _td))
            stack.extend((c, _fd, _td + (static_body is node.body))
                         for c in node.body)
            stack.extend((c, _fd, _td + (static_body is node.orelse))
                         for c in node.orelse)
        elif (isinstance(node, ast.If)
              and (static_branch := static_if_branch(node.test)) is not None):
            stack.append((node.test, _fd, _td))
            live_body = node.body if static_branch else node.orelse
            stack.extend((c, _fd, _td) for c in live_body)
        elif (isinstance(node, ast.While)
              and static_if_branch(node.test) is False):
            stack.append((node.test, _fd, _td))
            stack.extend((c, _fd, _td) for c in node.orelse)
        else:
            stack.extend((c, _fd, _td) for c in ast.iter_child_nodes(node))
def _init_module_level_import_deps(init_entry, internal_mods: set, *,
                                   internal_dotted=None) -> set[str]:
    if init_entry is None or init_entry.tree is None:
        return set()
    _graph: defaultdict[str, set[str]] = defaultdict(set)
    for node, _fd, _td in _iter_runtime_module_nodes(init_entry.tree):
        if _fd or _td:
            continue
        record_module_import(
            node, internal_mods, '__init__', _graph,
            internal_dotted=internal_dotted)
    return _graph.get('__init__', set())
def _runtime_dep_graph(cache, internal_mods):
    dep_graph = dict(reuse_or_build_import_graph(cache, internal_mods))
    _package_root = package_identity(
        getattr(cache, 'skill_dir', '') or '')[0]
    _init_entry = root_init_entry(cache, _package_root)
    if _init_entry is not None and _init_entry.tree is not None:
        _init_deps = _init_module_level_import_deps(
            _init_entry, internal_mods,
            internal_dotted=_runtime_import_module_names(cache.entries))
        if _init_deps:
            dep_graph['__init__'] = _init_deps
    return dep_graph
def _topo_sort_and_detect_cycles(dep_graph):
    topo_order: list[str] = []
    all_nodes = set(dep_graph.keys())
    for deps in dep_graph.values():
        all_nodes.update(deps)
    remaining = {node: len(dep_graph.get(node, ())) for node in all_nodes}
    importers_of: defaultdict[str, list[str]] = defaultdict(list)
    for node, deps in dep_graph.items():
        for dep in deps:
            importers_of[dep].append(node)
    queue = deque(sorted(filter(lambda n: remaining[n] == 0, all_nodes)))
    while queue:
        node = queue.popleft()
        topo_order.append(node)
        for importer in sorted(importers_of.get(node, ())):
            remaining[importer] -= 1
            if remaining[importer] == 0:
                queue.append(importer)
    topo_valid = len(topo_order) == len(all_nodes)
    cycles = detect_cycles(dep_graph)
    return topo_order, topo_valid, cycles
@dataclass(frozen=True)
class ImportTopology:
    dep_graph: dict
    topo_order: list
    topo_valid: bool
    cycles: list
def analyze_import_topology(cache, internal_mods) -> ImportTopology:
    dep_graph = _runtime_dep_graph(cache, internal_mods)
    topo_order, topo_valid, cycles = _topo_sort_and_detect_cycles(dep_graph)
    return ImportTopology(
        dep_graph=dep_graph, topo_order=topo_order,
        topo_valid=topo_valid, cycles=cycles)
_LOGGER_CONFIG_ATTRS = frozenset({
    "addHandler", "removeHandler", "setLevel", "addFilter",
    "removeFilter", "setFormatter",
})
_LOGGER_RECORD_ATTRS = frozenset({
    "debug", "info", "warning", "warn", "error", "exception",
    "critical", "fatal", "log",
})
_LOGGER_FACTORY_CALLS = frozenset({"getLogger", "get_module_logger"})
_LOGGER_NAME_HINTS = frozenset({"log", "logger", "_log", "_logger"})
def _logger_receiver(value: ast.AST, logger_names) -> bool:
    if isinstance(value, ast.Name):
        return (value.id in logger_names
                or value.id.lower() in _LOGGER_NAME_HINTS)
    if isinstance(value, ast.Attribute):
        return (value.attr in logger_names
                or value.attr.lower() in _LOGGER_NAME_HINTS)
    return isinstance(value, ast.Call) and _is_logger_factory_call(value)
def _is_logger_record_receiver(value: ast.AST, logger_names) -> bool:
    if isinstance(value, ast.Name):
        return value.id in logger_names
    return isinstance(value, ast.Call) and _is_logger_factory_call(value)
_PURE_MODULE_CALL_NAMES = frozenset({
    'dataclass', 'field', 'object', 'TypeVar', 'NewType',
    'total_ordering', 'unique', 'runtime_checkable', 'overload',
    'staticmethod', 'classmethod', 'property', 'lru_cache', 'cache',
})
_PURE_MODULE_LITERAL_CALL_NAMES = frozenset({
    'namedtuple', 'frozenset', 'tuple', 'set', 'list', 'dict',
    'str', 'int', 'float', 'getattr', 'len', 'isinstance', 'issubclass',
    'enumerate', 'zip',
})
_PURE_MODULE_CALL_DOTTED = frozenset({
    're.compile', 're.escape',
    'os.path.dirname', 'os.path.abspath', 'os.path.join',
    'os.path.normpath', 'os.path.normcase', 'os.path.basename',
    'os.path.splitext', 'os.path.realpath', 'os.path.expanduser',
})
def _is_literal_expr(node: ast.AST) -> bool:
    if isinstance(node, ast.Constant):
        return True
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return all(_is_literal_expr(elt) for elt in node.elts)
    if isinstance(node, ast.Dict):
        return (all(_is_literal_expr(k) for k in node.keys if k is not None)
                and all(_is_literal_expr(v) for v in node.values if v is not None))
    return False
_CTOR_HOOK_NAMES = frozenset({'__init__', '__new__', '__post_init__'})
def _pure_ctor_class_names(tree) -> set[str]:
    class_nodes = [node for node in getattr(tree, 'body', ()) or ()
                   if isinstance(node, ast.ClassDef)]
    pure_hooks: dict[str, bool] = {}
    for node in class_nodes:
        hooks = [sub for sub in node.body
                 if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef))
                 and sub.name in _CTOR_HOOK_NAMES]
        pure_hooks[node.name] = not any(
            isinstance(sub, (ast.Call, ast.Global, ast.Nonlocal,
                             ast.Import, ast.ImportFrom))
            for hook in hooks for sub in walk_nodes(hook))
    names: set[str] = set()
    changed = True
    while changed:
        changed = False
        for node in class_nodes:
            if node.name in names or not pure_hooks[node.name] or node.keywords:
                continue
            if all(isinstance(base, ast.Name)
                   and (base.id == 'object' or base.id in names)
                   for base in node.bases):
                names.add(node.name)
                changed = True
    return names
def _call_arguments_pure(call: ast.Call, pure_ctors) -> bool:
    for arg in [*call.args, *(kw.value for kw in call.keywords)]:
        for expr in _iter_scope_evaluated_calls(arg):
            if not _is_call_pure(expr, pure_ctors):
                return False
    return True
def _is_call_pure(call: ast.Call, pure_ctors) -> bool:
    func = call.func
    if isinstance(func, ast.Name):
        if func.id in _PURE_MODULE_CALL_NAMES:
            return _call_arguments_pure(call, pure_ctors)
        if func.id in _PURE_MODULE_LITERAL_CALL_NAMES:
            return all(_is_literal_expr(arg) for arg in (
                *call.args, *(kw.value for kw in call.keywords)))
        return func.id in pure_ctors and _call_arguments_pure(call, pure_ctors)
    if isinstance(func, ast.Attribute) and _is_literal_expr(func.value):
        return _call_arguments_pure(call, pure_ctors)
    return False
def _logger_receiver_arguments_pure(receiver: ast.AST,
                                      pure_ctors) -> bool:
    if not isinstance(receiver, ast.Call):
        return True
    return _call_arguments_pure(receiver, pure_ctors)
def _is_benign_module_call(call: ast.Call, logger_names,
                           pure_ctors) -> bool:
    func = call.func
    if isinstance(func, ast.Name):
        if func.id.startswith(("register_", "unregister_")):
            return _call_arguments_pure(call, pure_ctors)
        return bool(_is_call_pure(call, pure_ctors))
    if not isinstance(func, ast.Attribute):
        return False
    if func.attr in _LOGGER_CONFIG_ATTRS:
        return (_logger_receiver(func.value, logger_names)
                and _logger_receiver_arguments_pure(func.value, pure_ctors)
                and _call_arguments_pure(call, pure_ctors))
    if (func.attr in _LOGGER_RECORD_ATTRS
            and _is_logger_record_receiver(func.value, logger_names)):
        return (_logger_receiver_arguments_pure(func.value, pure_ctors)
                and _call_arguments_pure(call, pure_ctors))
    if _is_call_pure(call, pure_ctors):
        return True
    return (dotted_name(func) in _PURE_MODULE_CALL_DOTTED
            and _call_arguments_pure(call, pure_ctors))
def _own_module_level_names(entry) -> tuple[set, set]:
    binding_nodes = tuple(iter_module_binding_nodes(entry.tree))
    own_func_names = {n.name for n in binding_nodes
                      if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}
    own_container_names: set = set()
    for _an in binding_nodes:
        own_container_names |= container_names_of_stmt(_an)
    return own_func_names, own_container_names
def _single_name_assign_target(stmt) -> tuple:
    if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 \
            and isinstance(stmt.targets[0], ast.Name):
        return stmt.targets[0], stmt.value
    if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
        return stmt.target, stmt.value
    return None, None
def _is_logger_factory_call(value: ast.AST) -> bool:
    return isinstance(value, ast.Call) and (
        (isinstance(value.func, ast.Attribute)
         and value.func.attr in _LOGGER_FACTORY_CALLS
         and isinstance(value.func.value, ast.Name))
        or (isinstance(value.func, ast.Name)
            and value.func.id in _LOGGER_FACTORY_CALLS))
def _module_logger_bind_names(entry) -> set:
    logger_names = set()
    for _an in iter_module_binding_nodes(entry.tree):
        _tgt, _lc = _single_name_assign_target(_an)
        if _tgt is not None and _is_logger_factory_call(_lc):
            logger_names.add(_tgt.id)
    return logger_names
def _is_self_init_call(call: ast.Call, own_func_names: set,
                       own_container_names: set) -> bool:
    if isinstance(call.func, ast.Name):
        return call.func.id in own_func_names
    return (isinstance(call.func, ast.Attribute)
            and isinstance(call.func.value, ast.Name)
            and call.func.value.id in own_container_names
            and call.func.attr in ('update', 'extend', 'append'))
def _iter_scope_evaluated_calls(expr: ast.AST):
    stack: list[ast.AST] = [expr]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Call):
            yield node
            continue
        if isinstance(node, ast.BoolOp):
            evaluated = []
            for value in node.values:
                evaluated.append(value)
                truth = static_if_branch(value)
                if ((isinstance(node.op, ast.And) and truth is False)
                        or (isinstance(node.op, ast.Or) and truth is True)):
                    break
            stack.extend(evaluated)
            continue
        if isinstance(node, ast.IfExp):
            stack.append(node.test)
            truth = static_if_branch(node.test)
            if truth is None:
                stack.extend((node.body, node.orelse))
            else:
                stack.append(node.body if truth else node.orelse)
            continue
        if isinstance(node, ast.Lambda):
            stack.extend(node.args.defaults)
            stack.extend(d for d in node.args.kw_defaults if d is not None)
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            stack.extend(node.decorator_list)
            stack.extend(node.args.defaults)
            stack.extend(d for d in node.args.kw_defaults if d is not None)
            continue
        if isinstance(node, ast.ClassDef):
            stack.extend(node.decorator_list)
            stack.extend(node.bases)
            stack.extend(kw.value for kw in node.keywords)
            continue
        stack.extend(ast.iter_child_nodes(node))
def _module_level_call_exprs(node, *,
                             annotations_postponed: bool = False) -> list[ast.AST]:
    if isinstance(node, ast.Expr):
        return [node.value]
    if isinstance(node, ast.Assign):
        return [*node.targets, node.value]
    if isinstance(node, ast.AnnAssign):
        exprs: list[ast.AST] = [node.target]
        if not annotations_postponed:
            exprs.append(node.annotation)
        if node.value is not None:
            exprs.append(node.value)
        return exprs
    if isinstance(node, ast.AugAssign):
        return [node.target, node.value]
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        sites = list(iter_def_site_nodes(node))
        if not annotations_postponed:
            return sites
        annotations = [
            param.annotation for param in iter_arg_nodes(node.args)
            if param.annotation is not None]
        if node.returns is not None:
            annotations.append(node.returns)
        annotation_ids = {id(annotation) for annotation in annotations}
        return [site for site in sites if id(site) not in annotation_ids]
    if isinstance(node, ast.ClassDef):
        return list(iter_def_site_nodes(node))
    if isinstance(node, ast.If):
        return [node.test]
    if isinstance(node, ast.While):
        return [node.test]
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return [node.target, node.iter]
    if isinstance(node, (ast.With, ast.AsyncWith)):
        exprs = []
        for item in node.items:
            exprs.append(item.context_expr)
            if item.optional_vars is not None:
                exprs.append(item.optional_vars)
        return exprs
    if isinstance(node, ast.ExceptHandler):
        return [node.type] if node.type is not None else []
    if isinstance(node, ast.Assert):
        return [node.test, *([node.msg] if node.msg is not None else [])]
    if isinstance(node, ast.Match):
        return [node.subject]
    if isinstance(node, ast.match_case):
        return [node.guard] if node.guard is not None else []
    if isinstance(node, ast.Raise):
        return [expr for expr in (node.exc, node.cause) if expr is not None]
    if isinstance(node, ast.Delete):
        return list(node.targets)
    return []
def _scan_module_level_side_effects(entry, logger_names: set,
                                    own_func_names: set,
                                    own_container_names: set) -> list:
    out = []
    pure_ctors = _pure_ctor_class_names(entry.tree)
    annotations_postponed = module_postpones_annotations(
        entry.tree, require_absolute=True)
    _rel_path = entry_rel_path(entry)
    # 守卫体是进程入口而不是 import 副作用：其中的 sys.exit()/main() 只在
    # 直接执行脚本时发生，import 本模块不会触发，不属于模块级隐式行为。
    guard_ids = main_guard_node_ids(entry.tree)
    for node, func_depth, tc_depth in _iter_runtime_module_nodes(entry.tree):
        if func_depth or tc_depth or id(node) in guard_ids:
            continue
        definition_eval = isinstance(
            node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
        calls = [
            call for expr in _module_level_call_exprs(
                node, annotations_postponed=annotations_postponed)
            for call in _iter_scope_evaluated_calls(expr)]
        for call in calls:
            if id(call) in guard_ids:
                # 进程入口守卫内的调用不属于 import 副作用。
                continue
            if (_is_benign_module_call(call, logger_names, pure_ctors)
                    or (not definition_eval and _is_self_init_call(
                        call, own_func_names, own_container_names)
                        and _call_arguments_pure(call, pure_ctors))
                    or (_is_logger_factory_call(call)
                        and _call_arguments_pure(call, pure_ctors))):
                continue
            out.append({
                "file": _rel_path, "line": call.lineno,
                "type": "module_level_call",
                "severity": "low",
                "message": (
                    f"模块级函数调用: {ast.unparse(call.func)[:60]}()"),
            })
    return out
def collect_import_side_effects(entries) -> list:
    out = []
    for entry in entries:
        own_func_names, own_container_names = _own_module_level_names(entry)
        logger_names = _module_logger_bind_names(entry)
        out.extend(_scan_module_level_side_effects(
            entry, logger_names, own_func_names, own_container_names))
    return out
def _cycle_affected_modules(cycles, dep_graph) -> set:
    affected = {mod for cycle in cycles for mod in cycle}
    stack = list(affected)
    while stack:
        current = stack.pop()
        for importer, deps in dep_graph.items():
            if current in deps and importer not in affected:
                affected.add(importer)
                stack.append(importer)
    return affected
def annotate_structure_metrics(result, topology: ImportTopology) -> None:
    _affected = 0
    if topology.cycles:
        _affected = len(_cycle_affected_modules(
            topology.cycles, topology.dep_graph))
    result.metrics['cycle_affected_modules'] = _affected
    if topology.cycles:
        result.findings.append({
            'type': 'cycle_impact', 'severity': 'high',
            'affected': _affected,
            'message': f'循环依赖影响 {_affected} 个模块',
        })
    init_position = -1
    if topology.topo_order and '__init__' in topology.topo_order:
        init_position = topology.topo_order.index('__init__')
    result.metrics['init_load_position'] = init_position
    if init_position > 0:
        result.findings.append({
            'type': 'init_order', 'severity': 'medium',
            'position': init_position,
            'message': f'__init__ 在真加载序中位于第 {init_position + 1} 位：'
                       f'其模块级导入的包内模块先于它就位'
                       f'（init 加载膨胀信号，建议延迟导入）',
        })

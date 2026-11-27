from __future__ import annotations

import ast
import logging
import os
from collections.abc import Iterator
from typing import NamedTuple

from jwsgj.diag_blindspot_file import (
    collect_py_files,
    find_package_init,
    module_stem_index,
    rel_to_dotted_module,
    tests_domain_files,
)
from jwsgj.diag_shared_ast_bindings import (
    build_scope_index,
    collect_binding_names,
    collect_shadow_bindings,
    exec_scope_declarations,
    module_fallback_shadowed,
)
from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    assign_targets_value,
    collect_param_names,
    iter_evaluation_scope_chain,
    iter_module_scope_funcdefs,
    iter_module_scope_nodes,
    iter_own_nodes,
    iter_unpack_target_names,
)
from jwsgj.diag_shared_ast_surface import (
    has_library_init_signature,
    init_export_surface,
    is_reexport_surface,
    module_export_names,
    replay_export_surface,
)
from jwsgj.diag_shared_source_core import (
    load_module,
    parse_cached,
    read_source,
)
from jwsgj.diag_shared_source_scan import (
    is_suppressed,
    parse_suppressions,
)
from jwsgj.prevention_scope_facts import walk_nodes

logger = logging.getLogger(__name__)
__all__ = [
    "attr_read_consumed_refs",
    "collect_test_consumed_refs",
    "is_exported_from_init",
    "is_facade_module",
    "is_library_project",
    "iter_bound_attr_reads",
    "parse_module",
    "reset_package_shape_caches",
    "resolve_symbol_ref",
    "scan_dynamic_patterns",
    "suppressed_declaration",
    "suppressions_for",
]
_library_skill_cache: dict = {}
_library_init_content_cache: dict = {}
_init_exports_cache: dict = {}
_init_source_cache: dict = {}
def reset_package_shape_caches() -> None:
    _library_skill_cache.clear()
    _library_init_content_cache.clear()
    _init_exports_cache.clear()
    _init_source_cache.clear()
def _init_cache_key(init_path: str) -> str:
    return os.path.normcase(os.path.abspath(init_path))
def _read_init_source(init_path: str) -> str | None:
    key = _init_cache_key(init_path)
    source = read_source(init_path)
    if source is None:
        logger.debug("读取 __init__.py 失败或不可解码: %s", init_path)
    if key not in _init_source_cache or _init_source_cache[key] != source:
        _init_source_cache[key] = source
        _init_exports_cache.pop(key, None)
    return source
def is_library_project(project_root: str) -> bool:
    found = find_package_init(project_root)
    init_path = (found[0] if found
                 else os.path.join(project_root, "__init__.py"))
    _key = _init_cache_key(init_path)
    content = _read_init_source(init_path)
    if (_key in _library_skill_cache
            and _library_init_content_cache.get(_key) == content):
        return _library_skill_cache[_key]
    is_lib = content is not None and has_library_init_signature(content)
    _library_init_content_cache[_key] = content
    _library_skill_cache[_key] = is_lib
    return is_lib
def _parse_init_exports(init_path: str):
    _key = _init_cache_key(init_path)
    source = _read_init_source(init_path)
    if source is None:
        _init_exports_cache[_key] = None
        return None
    if _key in _init_exports_cache:
        return _init_exports_cache[_key]
    try:
        tree = parse_cached(source, init_path)
    except SyntaxError as exc:
        logger.debug("解析 __init__.py 失败: %s", exc)
        _init_exports_cache[_key] = None
        return None
    all_names, class_defs, import_names = init_export_surface(tree)
    if any(isinstance(node, ast.ImportFrom)
           and any(alias.name == '*' for alias in node.names)
           for node in iter_module_scope_nodes(tree, descend_classes=False)):
        import_names = {*import_names, '*'}
    result = (all_names, class_defs, import_names)
    _init_exports_cache[_key] = result
    return result
def _module_path_matches_class(import_path: str, class_module: str) -> bool:
    return bool(import_path and class_module) and (
        import_path == class_module
        or import_path.endswith('.' + class_module)
        or class_module.endswith('.' + import_path))


def _overwrites_export_binding(node, class_name: str) -> bool:
    normalized = assign_targets_value(node)
    if normalized is not None:
        targets, value = normalized
        bound_names = {name for target in targets
                       for name in iter_unpack_target_names(target)}
        if class_name not in bound_names:
            return False
        return not (isinstance(value, ast.Name) and value.id == class_name)
    if isinstance(node, ast.AugAssign):
        return isinstance(node.target, ast.Name) and node.target.id == class_name
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return node.name == class_name
    if isinstance(node, ast.Import):
        return any((alias.asname or alias.name.split('.', 1)[0]) == class_name
                   for alias in node.names)
    if isinstance(node, ast.ImportFrom):
        return any((alias.asname or alias.name) == class_name
                   for alias in node.names)
    if isinstance(node, ast.Delete):
        return any(isinstance(target, ast.Name) and target.id == class_name
                   for target in node.targets)
    return False

def _iter_init_binding_nodes(tree: ast.Module):
    """模块作用域源码序遍历：不进入类体与函数体，但产出函数/类定义节点本身。

    iter_module_scope_nodes 会整体跳过 FunctionDef 节点，而 __init__.py 的
    导出面判定必须看到顶层 def（同名函数会遮蔽导出类，__getattr__ 构成
    PEP 562 动态导出），故此处单独遍历。
    """
    stack = list(ast.iter_child_nodes(tree))
    stack.reverse()
    while stack:
        cur = stack.pop()
        if isinstance(cur, ast.Lambda):
            continue
        yield cur
        if isinstance(cur, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        stack.extend(reversed(list(ast.iter_child_nodes(cur))))

def _init_import_targets_class(tree, project_root: str, init_path: str,
                               class_name: str, class_filepath: str,
                               *, allow_star: bool) -> bool:
    rel = _rel_to_root(project_root, class_filepath)
    if rel is None:
        return False
    class_module = _dotted_module_name(rel)
    source_package = _source_package_name(project_root, init_path)
    same_file = bool(class_filepath) and (
        os.path.normcase(os.path.abspath(class_filepath))
        == os.path.normcase(os.path.abspath(init_path)))
    top_level_ids = {id(node) for node in tree.body}
    exported = False
    for node in _iter_init_binding_nodes(tree):
        is_top_level = id(node) in top_level_ids
        if is_top_level and _overwrites_export_binding(node, class_name):
            exported = False
        if isinstance(node, ast.ClassDef) and node.name == class_name:
            if same_file:
                exported = True
            continue
        if (allow_star and isinstance(
                node, (ast.FunctionDef, ast.AsyncFunctionDef))
                and node.name == '__getattr__'):
            exported = True
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        import_path = _import_from_path(node, source_package)
        if not _module_path_matches_class(import_path or '', class_module):
            continue
        for alias in node.names:
            bound_name = alias.asname or alias.name
            if ((alias.name == class_name and bound_name == class_name)
                    or (allow_star and alias.name == '*')):
                exported = True
    return exported


def _star_export_targets_class(init_path: str, project_root: str,
                               class_name: str, class_filepath: str) -> bool:
    """裸 ``from .mod import *`` 的导出判定：星号导入本身不登记任何名字，
    需回到类所在模块按 ``__all__``（无 ``__all__`` 时按公开名）核对。"""
    tree = parse_module(init_path)
    if (tree is None or not _init_import_targets_class(
            tree, project_root, init_path, class_name, class_filepath,
            allow_star=True)):
        return False
    source_tree = parse_module(class_filepath) if class_filepath else None
    if source_tree is None:
        return not class_name.startswith('_')
    all_names, class_defs, import_names = init_export_surface(source_tree)
    if class_name not in (class_defs | import_names | all_names):
        return False
    replay = replay_export_surface(source_tree)
    if replay.declared and not replay.computed:
        return class_name in set(replay.names)
    return not class_name.startswith('_')


def is_exported_from_init(project_root: str, class_name: str,
                           class_filepath: str) -> bool:
    try:
        _fp = os.fsdecode(os.fspath(class_filepath))
    except (TypeError, ValueError):
        _fp = ""
    if _fp and not os.path.isabs(_fp):
        _fp = os.path.join(project_root, _fp)
    if _fp:
        current = os.path.dirname(os.path.abspath(_fp))
    else:
        found = find_package_init(project_root)
        current = os.path.dirname(found[0]) if found else project_root
    root = os.path.normcase(os.path.abspath(project_root))
    while True:
        current_key = os.path.normcase(os.path.abspath(current))
        try:
            if os.path.commonpath([root, current_key]) != root:
                return False
        except ValueError:  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
            return False
        init_path = os.path.join(current, "__init__.py")
        exports = _parse_init_exports(init_path)
        if exports is not None:
            all_names, class_defs, import_names = exports
            explicit_binding = (
                class_name in class_defs or class_name in import_names
                or (class_name in all_names and '*' in import_names))
            if explicit_binding:
                tree = parse_module(init_path)
                return bool(tree is not None and _init_import_targets_class(
                    tree, project_root, init_path, class_name, _fp,
                    allow_star=class_name in all_names))
            if class_name in all_names:
                return True
            if ('*' in import_names and _star_export_targets_class(
                    init_path, project_root, class_name, _fp)):
                return True
        if current_key == root:
            return False
        parent = os.path.dirname(current)
        if parent == current:
            return False
        current = parent
def is_facade_module(project_root: str, filepath: str) -> bool:
    _fp = filepath if filepath and os.path.isabs(filepath) else (
        os.path.join(project_root, filepath) if filepath else "")
    tree = parse_module(_fp) if _fp else None
    return tree is not None and is_reexport_surface(tree)
def parse_module(filepath, ctx=None):
    loaded = load_module(filepath, ctx)
    return loaded[1] if loaded else None
def _package_name_from_rel(rel: str) -> str:
    parent = os.path.dirname(rel)
    if parent in ('', '.'):
        return ''
    return parent.replace('\\', '/').replace('/', '.')
def _rel_to_root(project_root: str, filepath: str) -> str | None:
    try:
        rel = os.path.relpath(filepath, project_root)
    except (TypeError, ValueError) as exc:
        logger.debug('[BlindSpot] 源路径无法归一,跳过: %s (%s)', filepath, exc)
        return None
    return rel.replace('\\', '/')
def _source_package_name(project_root: str, filepath: str) -> str | None:
    rel = _rel_to_root(project_root, filepath)
    if rel is None:
        return None
    return _package_name_from_rel(rel)
def _relative_import_path(level: int, module: str,
                          source_package: str) -> str | None:
    parts = source_package.split('.') if source_package else []
    ascend = level - 1
    if ascend and ascend >= len(parts):
        return None
    if ascend:
        parts = parts[:-ascend]
    if module:
        parts.extend(module.split('.'))
    return '.'.join(parts)


def _import_from_path(node: ast.ImportFrom,
                      source_package: str | None) -> str | None:
    if not node.level or source_package is None:
        return node.module
    return _relative_import_path(
        node.level, node.module or '', source_package)


def _dynamic_import_module_path(node: ast.Call, module_path: str,
                                source_package: str | None) -> str | None:
    if not module_path.startswith('.'):
        return module_path
    package_node = (node.args[1] if len(node.args) > 1 else next(
        (kw.value for kw in node.keywords if kw.arg == 'package'), None))
    if isinstance(package_node, ast.Constant) and isinstance(
            package_node.value, str):
        package_name = package_node.value
    elif (isinstance(package_node, ast.Name)
          and package_node.id == '__package__'):
        package_name = source_package
    else:
        return None
    if package_name is None:
        return None
    level = len(module_path) - len(module_path.lstrip('.'))
    return _relative_import_path(
        level, module_path[level:], package_name)
def _node_binding_pairs(node, source_package: str | None) -> list[tuple[str, str]]:
    if isinstance(node, ast.Import):
        return _import_stmt_binding_pairs(node)
    if isinstance(node, ast.ImportFrom):
        return _import_from_binding_pairs(node, source_package)
    return []
def _import_stmt_binding_pairs(node: ast.Import) -> list[tuple[str, str]]:
    pairs: list[tuple[str, str]] = []
    for alias in node.names:
        if alias.asname:
            pairs.append((alias.asname, alias.name))
        else:
            top_level = alias.name.split('.', 1)[0]
            pairs.append((top_level, top_level))
    return pairs
def _import_from_binding_pairs(node: ast.ImportFrom,
                               source_package: str | None) -> list[tuple[str, str]]:
    import_path = _import_from_path(node, source_package)
    if import_path is None and source_package is not None:
        return []
    base = import_path + "." if import_path else ""
    return [(_al.asname or _al.name, base + _al.name) for _al in node.names]
def _collect_import_bindings(stmts, source_package=None) -> dict[str, str]:
    return {bind_name: dotted for node in stmts
            for bind_name, dotted in _node_binding_pairs(node, source_package)}
_IMPORT_SCOPE_NODES = (
    ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
)
_FUNCTION_SCOPE_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
class _ImportBindingEvent(NamedTuple):
    dotted: str
    position: tuple[int, int]
    suite_path: tuple
class _BindingBarrier(NamedTuple):
    position: tuple[int, int]
    suite_path: tuple
    container: ast.stmt | None = None
class _ImportBindingIndex(NamedTuple):
    parents: dict
    bindings: dict[int, dict[str, str]]
    local_bindings: dict[int, frozenset[str]]
    global_names: dict[int, frozenset[str]]
    nonlocal_names: dict[int, frozenset[str]]
    module: ast.Module
    names: frozenset[str]
    comprehension_shadowed: frozenset[int]
    binding_events: dict[int, dict[str, tuple[_ImportBindingEvent, ...]]]
    statement_suites: dict[int, tuple]
    binding_barriers: dict[int, dict[str, tuple[_BindingBarrier, ...]]]
    definite_rebinds: dict[int, frozenset[str]]
def _scope_import_declarations(scope) -> tuple[frozenset[str], frozenset[str]]:
    global_names: set[str] = set()
    nonlocal_names: set[str] = set()
    for node in iter_own_nodes(scope):
        if isinstance(node, ast.Global):
            global_names.update(node.names)
        elif isinstance(node, ast.Nonlocal):
            nonlocal_names.update(node.names)
    return frozenset(global_names), frozenset(nonlocal_names)
def _enclosing_import_scope(node, parents):
    current = parents.get(id(node))
    while current is not None and not isinstance(current, _IMPORT_SCOPE_NODES):
        current = parents.get(id(current))
    return current
def _nonlocal_import_scope(scope, parents):
    current = parents.get(id(scope))
    while current is not None:
        if isinstance(current, _FUNCTION_SCOPE_NODES):
            return current
        current = parents.get(id(current))
    return scope
def _statement_suite_index(tree) -> dict[int, tuple]:
    suites: dict[int, tuple] = {}
    for parent in walk_nodes(tree):
        for field, value in ast.iter_fields(parent):
            if not isinstance(value, list):
                continue
            for item in value:
                if isinstance(item, ast.stmt):
                    suites[id(item)] = (id(parent), field, parent)
    return suites
def _suite_path(node, scope, parents, statement_suites) -> tuple:
    path = []
    current = node
    while current is not None and current is not scope:
        suite = statement_suites.get(id(current))
        if suite is not None:
            path.append(suite)
        current = parents.get(id(current))
    return tuple(reversed(path))
def _binding_position(node) -> tuple[int, int]:
    return (getattr(node, 'lineno', 0), getattr(node, 'col_offset', 0))
def _binding_end_position(node) -> tuple[int, int]:
    start_line = getattr(node, 'lineno', 0)
    return (getattr(node, 'end_lineno', None) or start_line,
            getattr(node, 'end_col_offset', None) or 0)
def _rebinding_position(node) -> tuple[int, int]:
    if (isinstance(node, (ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
                          ast.ExceptHandler)) and node.body):
        return _binding_position(node.body[0])
    return _binding_end_position(node)
def _direct_rebinding_names(node) -> set[str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name}
    if isinstance(node, ast.Lambda):
        return set()
    if isinstance(node, ast.ExceptHandler):
        return {node.name} if node.name else set()
    names: set[str] = set()
    collect_binding_names(node, names, include_imports=False)
    return names
def _build_import_binding_index(tree, source_package) -> _ImportBindingIndex:
    parents = {id(child): parent for parent in walk_nodes(tree)
               for child in ast.iter_child_nodes(parent)}
    statement_suites = _statement_suite_index(tree)
    scopes = [tree] + [node for node in walk_nodes(tree)
                       if node is not tree and isinstance(node, _IMPORT_SCOPE_NODES)]
    bindings: dict[int, dict[str, str]] = {}
    binding_events: dict[int, dict[str, list[_ImportBindingEvent]]] = {}
    binding_barriers: dict[int, dict[str, list[_BindingBarrier]]] = {}
    local_bindings: dict[int, frozenset[str]] = {}
    global_names: dict[int, frozenset[str]] = {}
    nonlocal_names: dict[int, frozenset[str]] = {}
    for scope in scopes:
        bindings[id(scope)] = {}
        binding_events[id(scope)] = {}
        binding_barriers[id(scope)] = {}
        local_bindings[id(scope)] = exec_scope_declarations(scope)[0]
        global_names[id(scope)], nonlocal_names[id(scope)] = (
            _scope_import_declarations(scope))
    for node in walk_nodes(tree):
        pairs = _node_binding_pairs(node, source_package)
        if not pairs:
            continue
        scope = _enclosing_import_scope(node, parents)
        if scope is None:
            continue
        for bind_name, dotted in pairs:
            target = scope
            if bind_name in global_names[id(scope)]:
                target = tree
            elif bind_name in nonlocal_names[id(scope)]:
                target = _nonlocal_import_scope(scope, parents)
            event = _ImportBindingEvent(
                dotted, _binding_position(node),
                _suite_path(node, target, parents, statement_suites))
            binding_events[id(target)].setdefault(bind_name, []).append(event)
    for node in walk_nodes(tree):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        bound_names = _direct_rebinding_names(node)
        if not bound_names:
            continue
        scope = _enclosing_import_scope(node, parents)
        if scope is None:
            continue
        for bind_name in bound_names:
            target = scope
            if bind_name in global_names[id(scope)]:
                target = tree
            elif bind_name in nonlocal_names[id(scope)]:
                target = _nonlocal_import_scope(scope, parents)
            barrier = _BindingBarrier(
                _rebinding_position(node),
                _suite_path(node, target, parents, statement_suites),
                _rebinding_container(node, target, parents))
            binding_barriers[id(target)].setdefault(bind_name, []).append(barrier)
    ordered_events: dict[int, dict[str, tuple[_ImportBindingEvent, ...]]] = {}
    for scope_id, scoped_events in binding_events.items():
        ordered_events[scope_id] = {}
        for name, events in scoped_events.items():
            ordered = tuple(sorted(events, key=lambda event: event.position))
            ordered_events[scope_id][name] = ordered
            bindings[scope_id][name] = ordered[-1].dotted
    ordered_barriers: dict[int, dict[str, tuple[_BindingBarrier, ...]]] = {}
    for scope_id, scoped_events in binding_barriers.items():
        ordered_barriers[scope_id] = {
            name: tuple(sorted(events, key=lambda event: event.position))
            for name, events in scoped_events.items()
        }
    definite_rebinds: dict[int, set[str]] = {}
    checked: set[tuple[int, str]] = set()
    for scoped_barriers in binding_barriers.values():
        for bind_name, barriers in scoped_barriers.items():
            for barrier in barriers:
                container = barrier.container
                if container is None:
                    continue
                key = (id(container), bind_name)
                if key in checked:
                    continue
                checked.add(key)
                if _stmt_definitely_rebinds(container, bind_name):
                    definite_rebinds.setdefault(id(container), set()).add(
                        bind_name)
    names = frozenset(name for scoped in bindings.values() for name in scoped)
    return _ImportBindingIndex(
        parents, bindings, local_bindings, global_names, nonlocal_names,
        tree, names, frozenset(_comprehension_shadow_name_ids(tree)),
        ordered_events, statement_suites, ordered_barriers,
        {cid: frozenset(values) for cid, values in definite_rebinds.items()})
def _exclusive_branch_paths(left, right) -> bool:
    for left_suite, right_suite in zip(left, right):
        if left_suite == right_suite:
            continue
        return (left_suite[0] == right_suite[0]
                and isinstance(left_suite[2], ast.If)
                and left_suite[1] != right_suite[1])
    return False
def _stmt_definitely_rebinds(node, name: str) -> bool:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return node.name == name
    if isinstance(node, ast.If):
        return bool(node.orelse) and (
            _suite_definitely_rebinds(node.body, name)
            and _suite_definitely_rebinds(node.orelse, name))
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return _suite_definitely_rebinds(node.body, name)
    if isinstance(node, (ast.Try, getattr(ast, 'TryStar', ast.Try))):
        if node.finalbody and _suite_definitely_rebinds(node.finalbody, name):
            return True
        if not _suite_definitely_rebinds(node.body, name):
            return False
        return all(_suite_definitely_rebinds(handler.body, name)
                   for handler in node.handlers)
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        return False
    return name in _direct_rebinding_names(node)
def _suite_definitely_rebinds(stmts, name: str) -> bool:
    for stmt in stmts:
        if _stmt_definitely_rebinds(stmt, name):
            return True
        if isinstance(stmt, (ast.Return, ast.Raise, ast.Break, ast.Continue)):
            return False
    return False
def _rebinding_container(node, target, parents):
    current = node
    while current is not None:
        if parents.get(id(current)) is target:
            return current if isinstance(current, ast.stmt) else None
        current = parents.get(id(current))
    return None
def _barrier_blocks_read(barrier, name: str, position, read_path,
                         index: _ImportBindingIndex) -> bool:
    if barrier.position > position:
        return False
    if read_path[:len(barrier.suite_path)] == barrier.suite_path:
        return True
    container = barrier.container
    if container is None or not read_path:
        return False
    if barrier.suite_path[:1] != read_path[:1]:
        return False
    if _binding_end_position(container) > position:
        return False
    return name in index.definite_rebinds.get(id(container), ())
def _local_import_binding_candidates(
        name: str, node, scope, index: _ImportBindingIndex) -> tuple[str, ...]:
    events = index.binding_events.get(id(scope), {}).get(name, ())
    if not events:
        return ()
    position = _binding_position(node)
    read_path = _suite_path(
        node, scope, index.parents, index.statement_suites)
    eligible = [event for event in events
                if event.position <= position
                and not _exclusive_branch_paths(read_path, event.suite_path)]
    prefix_depths = [len(event.suite_path) for event in eligible
                     if read_path[:len(event.suite_path)] == event.suite_path]
    if prefix_depths:
        deepest = max(prefix_depths)
        anchor = max(index for index, event in enumerate(eligible)
                     if len(event.suite_path) == deepest
                     and read_path[:deepest] == event.suite_path)
        eligible = eligible[anchor:]
    barriers = index.binding_barriers.get(id(scope), {}).get(name, ())
    cutoffs = [barrier.position for barrier in barriers
               if _barrier_blocks_read(barrier, name, position, read_path, index)]
    if cutoffs:
        cutoff = max(cutoffs)
        eligible = [event for event in eligible if event.position >= cutoff]
    return tuple(dict.fromkeys(event.dotted for event in eligible))
def _deferred_import_binding_candidates(
        name: str, scope, index: _ImportBindingIndex) -> tuple[str, ...]:
    events = index.binding_events.get(id(scope), {}).get(name, ())
    return tuple(dict.fromkeys(event.dotted for event in events))

def _scoped_import_binding_candidates(
        name: str, node, index: _ImportBindingIndex) -> tuple[str, ...]:
    nonlocal_lookup = False
    for scope_position, scope in enumerate(
            iter_evaluation_scope_chain(node, index.parents)):
        scope_id = id(scope)
        if scope_id not in index.bindings:
            continue
        if not nonlocal_lookup and name in index.global_names[scope_id]:
            target = index.module
            if isinstance(scope, (ast.Module, ast.ClassDef)):
                return _local_import_binding_candidates(
                    name, node, target, index)
            return _deferred_import_binding_candidates(name, target, index)
        if not nonlocal_lookup and name in index.nonlocal_names[scope_id]:
            nonlocal_lookup = True
            continue
        scoped = index.bindings[scope_id]
        if nonlocal_lookup:
            if isinstance(scope, _FUNCTION_SCOPE_NODES):
                if name in scoped:
                    return _deferred_import_binding_candidates(
                        name, scope, index)
                if name in index.local_bindings.get(scope_id, ()):
                    return ()
            if isinstance(scope, ast.Module):
                return ()
            continue
        if name in scoped:
            if scope_position == 0:
                return _local_import_binding_candidates(
                    name, node, scope, index)
            return (scoped[name],)
        if (isinstance(scope, _FUNCTION_SCOPE_NODES)
                and name in index.local_bindings.get(scope_id, ())):
            return ()
    return ()
def _scoped_import_binding(name: str, node,
                           index: _ImportBindingIndex) -> str | None:
    candidates = _scoped_import_binding_candidates(name, node, index)
    return candidates[-1] if candidates else None
def _bound_expr_parts(node) -> tuple[ast.AST, list[str]]:
    value = node
    segments: list[str] = []
    while isinstance(value, ast.Attribute):
        segments.append(value.attr)
        value = value.value
    if isinstance(value, ast.Call):
        value = value.func
        while isinstance(value, ast.Attribute):
            segments.append(value.attr)
            value = value.value
    return value, segments
def _bound_root_name(node) -> ast.Name | None:
    value, _segments = _bound_expr_parts(node)
    return value if isinstance(value, ast.Name) else None
def _visible_import_bindings(node,
                             index: _ImportBindingIndex) -> dict[str, str]:
    visible: dict[str, str] = {}
    root = _bound_root_name(node)
    shadowed_name = (
        root.id if root is not None
        and id(root) in index.comprehension_shadowed else None)
    for name in index.names:
        if name == shadowed_name:
            continue
        dotted = _scoped_import_binding(name, node, index)
        if dotted:
            visible[name] = dotted
    return visible
def _visible_import_binding_options(
        node, index: _ImportBindingIndex) -> tuple[dict[str, str], ...]:
    visible = _visible_import_bindings(node, index)
    root = _bound_root_name(node)
    if root is None or id(root) in index.comprehension_shadowed:
        return (visible,)
    candidates = _scoped_import_binding_candidates(root.id, node, index)
    if not candidates:
        return (visible,)
    return tuple({**visible, root.id: dotted} for dotted in candidates)
def iter_bound_attr_reads(
        tree: ast.AST, bindings,
        source_package: str | None = None) -> Iterator[tuple[str, str]]:
    if not bindings:
        return
    scoped = isinstance(bindings, _ImportBindingIndex)
    nodes = list(walk_nodes(tree))
    if (scoped and not bindings.names
            and not any(_is_dynamic_import_call(node) for node in nodes)):
        return
    chained = {id(node.value) for node in nodes
               if isinstance(node, ast.Attribute)
               and isinstance(node.value, ast.Attribute)}
    for node in nodes:
        if id(node) in chained or not isinstance(node, ast.Attribute):
            continue
        options = (_visible_import_binding_options(node, bindings)
                   if scoped else (bindings,))
        for active in options:
            pair = _bound_attr_pair(
                node, active, source_package=source_package)
            if pair is not None:
                yield pair
def _is_dynamic_import_call(node) -> bool:
    if not isinstance(node, ast.Call):
        return False
    func = node.func
    return ((isinstance(func, ast.Name) and func.id == '__import__')
            or (isinstance(func, ast.Attribute)
                and func.attr == 'import_module'))

def _bound_attr_pair(node, bindings,
                     source_package: str | None = None) -> tuple[str, str] | None:
    if not (isinstance(node, ast.Attribute)
            and isinstance(node.ctx, ast.Load) and node.attr):
        return None
    if isinstance(node.value, ast.Call):
        dotted = _bound_dotted_expr(
            node.value, bindings, source_package=source_package)
        if dotted:
            return dotted, node.attr
    value, segments = _bound_expr_parts(node.value)
    if not isinstance(value, ast.Name) or value.id not in bindings:
        return None
    dotted = bindings[value.id]
    if not dotted:
        return None
    if segments:
        dotted += '.' + '.'.join(reversed(segments))
    return dotted, node.attr
def _symbol_module_match(import_path: str, module_name: str,
                         exact: bool) -> tuple[int, int, str] | None:
    def match_prefix(prefix: str, candidate: str) -> str | None:
        if candidate == prefix:
            return ''
        if candidate.startswith(prefix + '.'):
            return candidate[len(prefix):]
        return None
    suffix = match_prefix(module_name, import_path)
    if suffix is not None:
        return len(module_name), 3, suffix
    if exact:
        return None
    parts = module_name.split('.')
    for index in range(1, len(parts)):
        prefix = '.'.join(parts[index:])
        suffix = match_prefix(prefix, import_path)
        if suffix is not None:
            return len(prefix), 2, suffix
    import_parts = import_path.split('.')
    for index in range(1, len(import_parts)):
        candidate = '.'.join(import_parts[index:])
        suffix = match_prefix(module_name, candidate)
        if suffix is not None:
            return len(module_name), 1, suffix
    return None
def resolve_symbol_ref(import_path: str, symbol: str, stem_index,
                       *, exact: bool = False) -> set[str]:
    candidates = {
        name
        for part in import_path.split('.') if part
        for name in stem_index.get(part, ())
    }
    matches = []
    for name in candidates:
        match = _symbol_module_match(import_path, name, exact)
        if match is None:
            continue
        specificity, rank, suffix = match
        matches.append((specificity, rank, len(name), name, suffix))
    if not matches:
        return set()
    best_specificity, best_rank = max(
        (specificity, rank)
        for specificity, rank, _length, _name, _suffix in matches)
    return {
        f'{name}{suffix}.{symbol}'
        for specificity, rank, _length, name, suffix in matches
        if (specificity, rank) == (best_specificity, best_rank)
    }
def _bound_dotted_expr(node, bindings,
                       source_package: str | None = None) -> str | None:
    if isinstance(node, ast.Name):
        return bindings.get(node.id)
    if isinstance(node, ast.Attribute):
        pair = _bound_attr_pair(
            node, bindings, source_package=source_package)
        if pair is not None:
            dotted, attr = pair
            return f'{dotted}.{attr}' if dotted else attr
        return None
    if isinstance(node, ast.Call):
        if not _is_dynamic_import_call(node):
            return None
        func = node.func
        module_arg = (node.args[0] if node.args else next(
            (kw.value for kw in node.keywords if kw.arg == 'name'), None))
        if (isinstance(module_arg, ast.Constant)
                and isinstance(module_arg.value, str) and module_arg.value):
            module_path = module_arg.value
            if not (isinstance(func, ast.Name) and func.id == '__import__'):
                return _dynamic_import_module_path(
                    node, module_path, source_package)
            fromlist = (node.args[3] if len(node.args) >= 4 else next(
                (kw.value for kw in node.keywords if kw.arg == 'fromlist'),
                None))
            if fromlist is None:
                return module_path.split('.', 1)[0]
            if isinstance(fromlist, ast.Constant):
                has_fromlist = bool(fromlist.value)
            elif isinstance(fromlist, (ast.List, ast.Tuple, ast.Set)):
                has_fromlist = bool(fromlist.elts)
            elif isinstance(fromlist, ast.Dict):
                has_fromlist = bool(fromlist.keys)
            else:
                has_fromlist = True
            return (module_path if has_fromlist
                    else module_path.split('.', 1)[0])
    return None
def _getattr_symbol_name(node, string_bindings,
                         module_name_load_ids=None) -> str | None:
    name_arg = node.args[1]
    if (isinstance(name_arg, ast.Constant)
            and isinstance(name_arg.value, str) and name_arg.value):
        return name_arg.value
    if isinstance(name_arg, ast.Name):
        if not _module_name_load_allowed(name_arg, module_name_load_ids):
            return None
        return string_bindings.get(name_arg.id)
    return None
def _resolve_getattr_symbol(node, bindings, stem_index,
                            string_bindings, module_name_load_ids=None,
                            source_package=None) -> set[str]:
    if not (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name) and node.func.id == 'getattr'
            and len(node.args) >= 2):
        return set()
    module_path = _bound_dotted_expr(
        node.args[0], bindings, source_package=source_package)
    symbol_name = _getattr_symbol_name(
        node, string_bindings, module_name_load_ids)
    if not module_path or not symbol_name:
        return set()
    return resolve_symbol_ref(module_path, symbol_name, stem_index)
def _from_import_consumed_refs(tree, stem_index,
                               source_package: str | None) -> set[str]:
    refs: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        import_path = _import_from_path(node, source_package)
        if not import_path:
            continue
        exact = bool(node.level) and source_package is not None
        for _al in node.names:
            if _al.name != '*':
                refs |= resolve_symbol_ref(
                    import_path, _al.name, stem_index, exact=exact)
    return refs
def attr_read_consumed_refs(tree, stem_index, source_package=None) -> set[str]:
    stmts = list(walk_nodes(tree))
    binding_index = _build_import_binding_index(tree, source_package)
    relative_paths = {
        dotted
        for node in stmts
        if source_package is not None
        and isinstance(node, ast.ImportFrom) and node.level
        for _bind_name, dotted in _node_binding_pairs(node, source_package)
    }
    refs: set[str] = set()
    for dotted, attr in iter_bound_attr_reads(
            tree, binding_index, source_package=source_package):
        refs |= resolve_symbol_ref(
            dotted, attr, stem_index, exact=dotted in relative_paths)
    string_bindings = _module_string_constant_bindings(tree)
    module_name_load_ids = _module_scope_name_load_ids(tree)
    for node in stmts:
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == 'getattr' and len(node.args) >= 2):
            continue
        for bindings in _visible_import_binding_options(
                node.args[0], binding_index):
            refs |= _resolve_getattr_symbol(
                node, bindings, stem_index,
                string_bindings, module_name_load_ids,
                source_package=source_package)
    return refs
def collect_test_consumed_refs(project_root: str, files, ctx=None,
                               stem_index=None) -> set[str]:
    if stem_index is None:
        stem_index = module_stem_index(project_root, files)
    if not stem_index:
        return set()
    refs: set[str] = set()
    for tf in tests_domain_files(project_root):
        tree = parse_module(tf, ctx)
        if tree is None:
            continue
        source_package = _source_package_name(project_root, tf)
        refs |= (_from_import_consumed_refs(tree, stem_index, source_package)
                 | attr_read_consumed_refs(tree, stem_index, source_package))
    return refs
def _is_symbol_name_text(text: str) -> bool:
    return bool(text) and len(text) <= 80 and (
        text[0].isalpha() or text[0] == '_') and all(
        ch.isalnum() or ch == '_' for ch in text)
def _simple_name(full_name: str) -> str:
    return full_name.rsplit('.', 1)[-1]
def _qualify(prefix: str, name: str) -> str:
    return f'{prefix}.{name}' if prefix else name
def _registration_value(node) -> ast.expr | None:
    if isinstance(node, ast.Assign):
        targets = node.targets
    elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
        targets = [node.target]
    else:
        return None
    if node.value is None:
        return None
    if any(isinstance(t, ast.Name) and t.id == '__all__' for t in targets):
        return None
    return node.value
def _namespace_string_constants(value_node) -> set[str]:
    if not isinstance(value_node, (ast.Dict, ast.List, ast.Tuple, ast.Set)):
        return set()
    found: set[str] = set()
    stack = [value_node]
    while stack:
        node = stack.pop()
        if isinstance(node, ast.Dict):
            stack.extend(v for v in node.values if v is not None)
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            continue
        if isinstance(node, ast.Constant):
            if isinstance(node.value, str) and _is_symbol_name_text(node.value):
                found.add(node.value)
            continue
        stack.extend(ast.iter_child_nodes(node))
    return found
def _container_func_refs(value_node) -> tuple[set[str], set[str]]:
    bare_names: set[str] = set()
    attr_names: set[str] = set()
    if isinstance(value_node, ast.Dict):
        candidates = list(value_node.values)
    elif isinstance(value_node, (ast.List, ast.Tuple, ast.Set)):
        candidates = list(value_node.elts)
    else:
        return bare_names, attr_names
    for cand in candidates:
        if isinstance(cand, ast.Attribute):
            attr_names.add(cand.attr)
        elif isinstance(cand, ast.Name):
            bare_names.add(cand.id)
    return bare_names, attr_names
def _decorator_ref_node_ids(tree) -> set[int]:
    decorated: set[int] = set()
    for sub in walk_nodes(tree):
        if isinstance(sub, (ast.FunctionDef, ast.AsyncFunctionDef,
                            ast.ClassDef)):
            for dec in sub.decorator_list:
                decorated.add(id(dec))
    return decorated
def _class_attr_read_names(class_node: ast.ClassDef) -> set[str]:
    names: set[str] = set()
    stack: list[ast.AST] = list(class_node.body)
    while stack:
        node = stack.pop()
        if isinstance(node, ast.ClassDef):
            continue
        if (isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Load)
                and isinstance(node.value, ast.Name)
                and node.value.id in ('self', 'cls')):
            names.add(node.attr)
        stack.extend(ast.iter_child_nodes(node))
    return names
def _class_attr_names(item: ast.stmt) -> list[str]:
    if isinstance(item, (ast.Assign, ast.AnnAssign)):
        names: set[str] = set()
        collect_binding_names(item, names, include_imports=False)
        return list(names)
    if isinstance(item, ast.ClassDef):
        return [item.name]
    return []
def _collect_class_attrs(class_node: ast.ClassDef) -> list[str]:
    attrs: list[str] = []
    for item in class_node.body:
        attrs.extend(_class_attr_names(item))
    return attrs
def _lambda_binding_names(node) -> frozenset[str]:
    names = set(collect_param_names(node))
    stack = [node.body]
    while stack:
        current = stack.pop()
        if collect_binding_names(current, names):
            continue
        stack.extend(ast.iter_child_nodes(current))
    return frozenset(names)
def _named_scope_key(scope_node, definition_scopes) -> str:
    if isinstance(scope_node, ast.Module):
        return ''
    return _qualify(definition_scopes.get(id(scope_node), ''), scope_node.name)
def _comprehension_shadow_name_ids(tree) -> set[int]:
    shadowed: set[int] = set()
    stack = [(tree, frozenset())]
    while stack:
        node, visible_names = stack.pop()
        if isinstance(node, COMP_SCOPE_NODES):
            bound_before = set(visible_names)
            generators = []
            for generator in node.generators:
                iter_visible = frozenset(bound_before)
                bound_before.update(iter_unpack_target_names(generator.target))
                generators.append((
                    generator, iter_visible, frozenset(bound_before)))
            for generator, iter_visible, condition_visible in generators:
                stack.append((generator.iter, iter_visible))
                stack.extend((condition, condition_visible)
                             for condition in generator.ifs)
            roots = ((node.key, node.value) if isinstance(node, ast.DictComp)
                     else (node.elt,))
            stack.extend((root, frozenset(bound_before)) for root in roots)
            continue
        if (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
                and node.id in visible_names):
            shadowed.add(id(node))
        stack.extend((child, visible_names)
                     for child in ast.iter_child_nodes(node))
    return shadowed
def _module_scope_name_load_ids(tree) -> set[int]:
    parents = {id(child): parent for parent in walk_nodes(tree)
               for child in ast.iter_child_nodes(parent)}
    definition_scopes = build_scope_index(tree)
    local_bindings, global_names, class_scopes = collect_shadow_bindings(tree)
    lambda_bindings = {
        id(node): _lambda_binding_names(node)
        for node in walk_nodes(tree) if isinstance(node, ast.Lambda)
    }
    comprehension_shadowed = _comprehension_shadow_name_ids(tree)
    visible: set[int] = set()
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)):
            continue
        if id(node) in comprehension_shadowed:
            continue
        named_scope = ''
        shadowed = False
        for scope in iter_evaluation_scope_chain(node, parents):
            if isinstance(scope, ast.Lambda):
                if node.id in lambda_bindings.get(id(scope), ()):
                    shadowed = True
                    break
                continue
            if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef,
                                  ast.ClassDef, ast.Module)):
                named_scope = _named_scope_key(scope, definition_scopes)
                break
        if shadowed:
            continue
        if not module_fallback_shadowed(
                named_scope, node.id, local_bindings, global_names, class_scopes):
            visible.add(id(node))
    return visible
def _module_name_load_allowed(node, module_name_load_ids) -> bool:
    return module_name_load_ids is None or id(node) in module_name_load_ids
def _collect_bare_value_refs(node, bare_slot, call_targets, decorator_ids,
                             module_name_load_ids=None) -> None:
    decorated = decorator_ids or ()
    for sub in walk_nodes(node):
        if (isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
                and id(sub) not in call_targets and id(sub) not in decorated
                and _module_name_load_allowed(sub, module_name_load_ids)):
            bare_slot.add(sub.id)
def _collect_value_ref_names(node, call_targets, bare_slot, attr_slot=None,
                             decorator_ids=None, module_name_load_ids=None,
                             module_slot=None) -> None:
    if not isinstance(node, ast.ClassDef):
        _collect_bare_value_refs(
            node, bare_slot, call_targets, decorator_ids, module_name_load_ids)
        return
    class_bound: set[str] = set()
    for stmt in node.body:
        if not isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef)):
            statement_refs: set[str] = set()
            _collect_bare_value_refs(
                stmt, statement_refs, call_targets, decorator_ids,
                module_name_load_ids)
            bare_slot.update(name for name in statement_refs
                             if name in class_bound)
            if module_slot is not None:
                module_slot.update(name for name in statement_refs
                                   if name not in class_bound)
        collect_binding_names(stmt, class_bound)
    if attr_slot is not None:
        attr_slot.update(_class_attr_read_names(node))
def _collect_class_qualified_refs(tree, module_name, call_targets, class_attr_refs) -> None:
    local_classes = {node.name
                     for node in iter_module_scope_nodes(
                         tree, descend_classes=False)
                     if isinstance(node, ast.ClassDef)}
    if not local_classes:
        return
    module_name_load_ids = _module_scope_name_load_ids(tree)
    for sub in walk_nodes(tree):
        if not isinstance(sub, ast.Attribute):
            continue
        if not isinstance(sub.ctx, ast.Load) or id(sub) in call_targets:
            continue
        base = sub.value
        if (isinstance(base, ast.Name) and base.id in local_classes
                and _module_name_load_allowed(base, module_name_load_ids)):
            class_attr_refs.setdefault(
                (module_name, base.id), set()).add(sub.attr)
class _DecoratorRef(NamedTuple):
    name: str | None
    owner: str | None
    is_attribute: bool
    is_call: bool
def _decorator_ref(dec: ast.expr) -> _DecoratorRef:
    is_call = isinstance(dec, ast.Call)
    func = dec.func if is_call else dec
    if isinstance(func, ast.Name):
        return _DecoratorRef(func.id, None, False, is_call)
    if isinstance(func, ast.Attribute):
        owner = func.value.id if isinstance(func.value, ast.Name) else None
        return _DecoratorRef(func.attr, owner, True, is_call)
    return _DecoratorRef(None, None, False, is_call)
_WEB_HOOK_DECORATORS: frozenset[str] = frozenset({
    'before_request', 'after_request', 'teardown_request',
    'before_serving', 'after_serving', 'middleware', 'on_event',
    'add_event_handler', 'exception_handler', 'add_exception_handler',
})
_REGISTRAR_DECORATORS: frozenset[str] = frozenset({
    'register_rule', 'register', 'subscribe',
    'on', 'listen', 'add_handler', 'add_listener',
    'register_checker', 'register_hook',
})
def _module_vars_call_ids(tree) -> set[int]:
    return {
        id(node) for node in iter_module_scope_nodes(tree, descend_classes=False)
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'vars' and not node.args)
    }
class _DynamicRefCollector:
    __slots__ = ('call_graph', 'dynamic', 'files', 'gi_mods',
                 'import_binding_index', 'module_name_load_ids',
                 'module_string_constants', 'scanner', 'stem_index')
    def __init__(self, scanner, files, call_graph, stem_index) -> None:
        self.scanner = scanner
        self.files = files
        self.call_graph = call_graph
        self.stem_index = stem_index
        self.dynamic: set[str] = set()
        self.gi_mods: set[str] = set()
        self.module_name_load_ids: set[int] | None = None
        self.import_binding_index: _ImportBindingIndex | None = None
        self.module_string_constants: dict[str, dict[str, str]] = {}
    def collect(self) -> tuple[set[str], set[str]]:
        for filepath in self.files:
            self._scan_file(filepath)
        self.dynamic |= collect_test_consumed_refs(
            self.scanner.project_root, self.files, ctx=self.scanner._ctx,
            stem_index=self.stem_index)
        return self.dynamic, self.gi_mods
    def _scan_file(self, filepath) -> None:
        parsed = _parse_scan_target(self.scanner, filepath)
        if parsed is None:
            return
        rel, tree = parsed
        self.module_name_load_ids = _module_scope_name_load_ids(tree)
        mod_name = _dotted_module_name(rel)
        local_func_names = _collect_local_func_names(tree)
        module_vars_calls = _module_vars_call_ids(tree)
        self.module_string_constants[mod_name] = (
            _module_string_constant_bindings(tree))
        source_package = _package_name_from_rel(rel)
        self.import_binding_index = _build_import_binding_index(
            tree, source_package)
        self.dynamic |= attr_read_consumed_refs(
            tree, self.stem_index, source_package=source_package)
        class_scope_assigns = _class_scope_assign_ids(tree)
        for node in walk_nodes(tree):
            if isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                if id(node) not in class_scope_assigns:
                    self._check_assign_patterns(node, mod_name)
                continue
            if isinstance(node, ast.Call):
                self._dispatch_call_node(
                    node, mod_name, local_func_names, module_vars_calls)
                continue
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef)):
                self._check_funcdef_patterns(node, mod_name)
                continue
            if isinstance(node, (ast.For, ast.AsyncFor)):
                self._check_for_patterns(node, mod_name)
        self._check_ns_introspection_patterns(tree, source_package)
        self._register_callgraph_imports(rel)
    def _add_dynamic_ref(self, mod_name, name) -> None:
        self.dynamic.add(_qualify(mod_name, name))
        self.dynamic.add(name)
        if isinstance(mod_name, str) and '.' in mod_name:
            self.dynamic.add(_qualify(mod_name.split('.', 1)[-1], name))
    @staticmethod
    def _self_or_name_ref(arg, module_name_load_ids) -> str | None:
        if isinstance(arg, ast.Attribute):
            if isinstance(arg.value, ast.Name) and arg.value.id == 'self':
                return arg.attr
            return None
        if isinstance(arg, ast.Name):
            return (arg.id if _module_name_load_allowed(
                arg, module_name_load_ids) else None)
        return None
    @staticmethod
    def _is_name_call(node, name: str) -> bool:
        return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == name)
    @staticmethod
    def _is_method_call(node, owner: str,
                        attrs: str | tuple[str, ...]) -> bool:
        if isinstance(attrs, str):
            attrs = (attrs,)
        return (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name)
                and node.func.value.id == owner
                and node.func.attr in attrs)
    @staticmethod
    def _is_attr_call(node, attr: str) -> bool:
        return (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == attr)
    def _register_callback_args(self, args, mod_name) -> None:
        for arg in args:
            ref = self._self_or_name_ref(arg, self.module_name_load_ids)
            if ref:
                self._add_dynamic_ref(mod_name, ref)
    def _check_registration_patterns(self, node, mod_name) -> None:
        if self._is_method_call(node, 'atexit', 'register'):
            self._register_callback_args(node.args, mod_name)
        if self._is_name_call(node, 'patch'):
            self._register_callback_args(node.args[1:], mod_name)
        if self._is_method_call(node, 'sys', 'settrace'):
            self._register_callback_args(node.args, mod_name)
        if (self._is_method_call(node, 'signal', 'signal')
                and len(node.args) >= 2):
            ref = self._self_or_name_ref(node.args[1], self.module_name_load_ids)
            if ref:
                self._add_dynamic_ref(mod_name, ref)
    def _register_thread_target(self, node, mod_name) -> None:
        targets = ([node.args[1]] if len(node.args) >= 2 else []) + [
            kw.value for kw in node.keywords if kw.arg == 'target']
        for target in targets:
            ref = self._self_or_name_ref(target, self.module_name_load_ids)
            if ref:
                self._add_dynamic_ref(mod_name, ref)
    def _register_create_task(self, node, mod_name) -> None:
        for arg in node.args:
            if (isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name)
                    and _module_name_load_allowed(
                        arg.func, self.module_name_load_ids)):
                self._add_dynamic_ref(mod_name, arg.func.id)
            elif (isinstance(arg, ast.Name)
                    and _module_name_load_allowed(
                        arg, self.module_name_load_ids)):
                self._add_dynamic_ref(mod_name, arg.id)
    def _register_pool_submit(self, node, mod_name) -> None:
        if node.args:
            ref = self._self_or_name_ref(node.args[0], self.module_name_load_ids)
            if ref:
                self._add_dynamic_ref(mod_name, ref)
    def _register_weakref_callback(self, node, mod_name) -> None:
        if len(node.args) >= 2:
            ref = self._self_or_name_ref(node.args[1], self.module_name_load_ids)
            if ref:
                self._add_dynamic_ref(mod_name, ref)
    def _check_concurrency_patterns(self, node, mod_name) -> None:
        if self._is_method_call(node, 'threading', 'Thread'):
            self._register_thread_target(node, mod_name)
        if self._is_method_call(node, 'asyncio', 'create_task'):
            self._register_create_task(node, mod_name)
        if self._is_attr_call(node, 'submit'):
            self._register_pool_submit(node, mod_name)
        if self._is_method_call(node, 'weakref', ('ref', 'proxy')):
            self._register_weakref_callback(node, mod_name)
    def _register_getattr_fstring(self, name_arg, mod_name) -> None:
        first = name_arg.values[0] if name_arg.values else None
        if (isinstance(first, ast.Constant) and isinstance(first.value, str)
                and first.value.startswith('_')):
            self.dynamic.add(_qualify(mod_name, f'{first.value}*'))
    def _check_getattr_patterns(self, node, mod_name) -> None:
        binding_options = (_visible_import_binding_options(
            node.args[0], self.import_binding_index)
            if self.import_binding_index is not None else ({},))
        resolved: set[str] = set()
        for bindings in binding_options:
            resolved |= _resolve_getattr_symbol(
                node, bindings, self.stem_index,
                self.module_string_constants.get(mod_name, {}),
                self.module_name_load_ids)
        if resolved:
            self.dynamic |= resolved
            return
        if any(_bound_dotted_expr(node.args[0], bindings)
               for bindings in binding_options):
            return
        name_arg = node.args[1]
        is_constant_name = (isinstance(name_arg, ast.Constant)
                            and isinstance(name_arg.value, str)
                            and bool(name_arg.value))
        if is_constant_name:
            self._add_dynamic_ref(mod_name, name_arg.value)
        elif (isinstance(name_arg, ast.Name)
              and _module_name_load_allowed(
                  name_arg, self.module_name_load_ids)):
            constant_name = self.module_string_constants.get(
                mod_name, {}).get(name_arg.id)
            if constant_name:
                self.dynamic.add(f"attr:{constant_name}")
        elif isinstance(name_arg, ast.JoinedStr):
            self._register_getattr_fstring(name_arg, mod_name)
    @staticmethod
    def _str_list_elements(value) -> list[str]:
        if not isinstance(value, (ast.List, ast.Tuple, ast.Set)):
            return []
        return [e.value for e in value.elts
                if isinstance(e, ast.Constant) and isinstance(e.value, str)]
    @staticmethod
    def _import_fromlist(node) -> list[str]:
        fromlist = node.args[3] if len(node.args) >= 4 else None
        if fromlist is None:
            fromlist = next(
                (kw.value for kw in node.keywords
                 if kw.arg == 'fromlist'), None)
        return _DynamicRefCollector._str_list_elements(fromlist)
    def _check_import_patterns(self, node) -> None:
        module_path = None
        if node.args and isinstance(node.args[0], ast.Constant):
            value = node.args[0].value
            if isinstance(value, str) and value:
                module_path = value
        for name in self._import_fromlist(node):
            if not name:
                continue
            resolved = (resolve_symbol_ref(module_path, name, self.stem_index)
                        if module_path else set())
            if resolved:
                self.dynamic |= resolved
            else:
                self.dynamic.add(name)
    def _check_dynamic_access_patterns(self, node, mod_name) -> None:
        if self._is_name_call(node, 'getattr') and len(node.args) >= 2:
            self._check_getattr_patterns(node, mod_name)
        if self._is_name_call(node, '__import__'):
            self._check_import_patterns(node)
    def _collect_seq_func_refs(self, elt, mod_name, depth, loop_called) -> None:
        if (isinstance(elt, ast.Name)
                and _module_name_load_allowed(
                    elt, self.module_name_load_ids)):
            if loop_called:
                self._add_dynamic_ref(mod_name, elt.id)
        elif depth < 1 and isinstance(elt, ast.Tuple):
            for sub in elt.elts:
                self._collect_seq_func_refs(sub, mod_name, depth + 1, True)
    def _collect_dict_dispatch_refs(self, value: ast.Dict, mod_name) -> None:
        for _key, val in zip(value.keys, value.values, strict=True):
            if _key is None:
                continue
            if (isinstance(val, ast.Name)
                    and _module_name_load_allowed(
                        val, self.module_name_load_ids)):
                self._add_dynamic_ref(mod_name, val.id)
            elif (isinstance(val, ast.Constant) and isinstance(val.value, str)
                    and val.value.startswith('_')):
                self._add_dynamic_ref(mod_name, val.value)
    def _check_assign_patterns(self, node, mod_name) -> None:
        normalized = assign_targets_value(node)
        if normalized is None and isinstance(node, ast.AugAssign):
            normalized = ([node.target], node.value)
        if normalized is None:
            return
        targets, value = normalized
        self._collect_assign_value_refs(
            value, mod_name,
            has_name_target=any(isinstance(t, ast.Name) for t in targets))
        self._register_sys_excepthook(targets, value, mod_name)
    def _collect_assign_value_refs(self, value, mod_name,
                                   has_name_target) -> None:
        if isinstance(value, ast.Name):
            if _module_name_load_allowed(value, self.module_name_load_ids):
                self._add_dynamic_ref(mod_name, value.id)
            return
        if not has_name_target:
            return
        if isinstance(value, ast.Dict):
            self._collect_dict_dispatch_refs(value, mod_name)
        elif isinstance(value, (ast.Tuple, ast.Set)):
            for elt in value.elts:
                self._collect_seq_func_refs(elt, mod_name, 0, True)
        elif isinstance(value, ast.List):
            for elt in value.elts:
                self._collect_seq_func_refs(elt, mod_name, 0, False)
    def _register_sys_excepthook(self, targets, value, mod_name) -> None:
        for target in targets:
            if not (isinstance(target, ast.Attribute)
                    and isinstance(target.value, ast.Name)
                    and target.value.id == 'sys'
                    and target.attr == 'excepthook'):
                continue
            ref = self._self_or_name_ref(value, self.module_name_load_ids)
            if ref:
                self._add_dynamic_ref(mod_name, ref)
    def _check_call_patterns(self, node, mod_name) -> None:
        self._check_registration_patterns(node, mod_name)
        self._check_concurrency_patterns(node, mod_name)
        self._check_dynamic_access_patterns(node, mod_name)
    @staticmethod
    def _is_local_private_func_ref(expr, local_func_names,
                                   module_name_load_ids=None) -> bool:
        return (isinstance(expr, ast.Name) and expr.id.startswith('_')
                and expr.id in local_func_names
                and _module_name_load_allowed(expr, module_name_load_ids))
    def _check_arg_value_refs(self, node, mod_name, local_func_names) -> None:
        for arg in node.args:
            if self._is_local_private_func_ref(
                    arg, local_func_names, self.module_name_load_ids):
                self._add_dynamic_ref(mod_name, arg.id)
        for kw in node.keywords:
            if (kw.arg is not None
                    and self._is_local_private_func_ref(
                        kw.value, local_func_names, self.module_name_load_ids)):
                self._add_dynamic_ref(mod_name, kw.value.id)
    def _register_decorator_refs(self, node, mod_name) -> None:
        for dec in node.decorator_list:
            info = _decorator_ref(dec)
            if info.name is None:
                continue
            if not info.is_attribute:
                self.dynamic.add(info.name)
                self.dynamic.add(_qualify(mod_name, info.name))
                continue
            func = dec.func if isinstance(dec, ast.Call) else dec
            bindings = (
                _visible_import_bindings(func, self.import_binding_index)
                if self.import_binding_index is not None else {})
            if _bound_attr_pair(func, bindings) is not None:
                continue
            if info.owner is not None:
                self.dynamic.add(_qualify(
                    mod_name, f'{info.owner}.{info.name}'))
    def _check_funcdef_patterns(self, node, mod_name) -> None:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            self._check_hook_registrar_decorators(node, mod_name)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.ClassDef)):
            self._register_decorator_refs(node, mod_name)
    def _check_hook_registrar_decorators(self, node, mod_name) -> None:
        for dec in node.decorator_list:
            dec_name = _decorator_ref(dec).name
            if (dec_name in _WEB_HOOK_DECORATORS
                    or dec_name in _REGISTRAR_DECORATORS):
                self._add_dynamic_ref(mod_name, node.name)
    def _collect_iter_literal_refs(self, node, mod_name, loop_called) -> None:
        if not isinstance(node.iter, (ast.List, ast.Tuple, ast.Set)):
            return
        for elt in node.iter.elts:
            if isinstance(elt, ast.Tuple):
                self._collect_seq_func_refs(elt, mod_name, 0, True)
            elif (isinstance(elt, ast.Name) and loop_called
                    and _module_name_load_allowed(
                        elt, self.module_name_load_ids)):
                self._add_dynamic_ref(mod_name, elt.id)
    @staticmethod
    def _loop_var_is_called(node, loop_var_name: str) -> bool:
        parents = {id(child): parent for parent in walk_nodes(node)
                   for child in ast.iter_child_nodes(parent)}
        comprehension_shadowed = _comprehension_shadow_name_ids(node)
        for child in walk_nodes(node):
            if not (isinstance(child, ast.Call)
                    and isinstance(child.func, ast.Name)
                    and child.func.id == loop_var_name
                    and id(child.func) not in comprehension_shadowed):
                continue
            scopes = iter_evaluation_scope_chain(child, parents)
            if any(loop_var_name in exec_scope_declarations(scope)[0]
                   for scope in scopes):
                continue
            return True
        return False
    def _check_for_patterns(self, node, mod_name) -> None:
        if not isinstance(node, (ast.For, ast.AsyncFor)):
            return
        loop_var = node.target
        loop_called = (isinstance(loop_var, ast.Name)
                       and self._loop_var_is_called(node, loop_var.id))
        self._collect_iter_literal_refs(node, mod_name, loop_called)
    def _register_globals_introspection(
            self, node, mod_name, module_vars_calls) -> None:
        if not isinstance(node.func, ast.Name) or node.args:
            return
        if (node.func.id == 'globals'
                or (node.func.id == 'vars' and id(node) in module_vars_calls)):
            self.gi_mods.add(mod_name)
    def _dispatch_call_node(
            self, node, mod_name, local_func_names, module_vars_calls) -> None:
        self._check_call_patterns(node, mod_name)
        self._check_arg_value_refs(node, mod_name, local_func_names)
        self._register_globals_introspection(
            node, mod_name, module_vars_calls)
    def _register_callgraph_imports(self, rel) -> None:
        if self.call_graph is None or not hasattr(self.call_graph, 'imports'):
            return
        for local_name in self.call_graph.imports.get(rel, {}):
            self.dynamic.add(local_name)
    def _check_ns_introspection_patterns(self, tree, source_package) -> None:
        import_module_seen, ns_enum_seen, prefixes = _collect_ns_evidence(tree)
        import_bindings = _collect_import_bindings(
            iter_module_scope_nodes(tree, descend_classes=False), source_package)
        if not ((import_module_seen or import_bindings)
                and ns_enum_seen and prefixes):
            return
        stem_map, ambiguous = _stem_disambiguated_map(self.files)
        module_map = _module_disambiguated_map(
            self.scanner.project_root, self.files)
        unambiguous_stems = {key: path for key, path in stem_map.items()
                             if key not in ambiguous}
        resolution_map = {**unambiguous_stems, **module_map}
        module_paths = _ns_module_paths(
            tree, import_module_seen, import_bindings,
            stem_map=resolution_map, ctx=self.scanner._ctx)
        if not module_paths:
            return
        self._expand_module_paths(
            module_paths, resolution_map, ambiguous, prefixes)
    def _expand_module_paths(self, module_paths, stem_map, ambiguous,
                             prefixes) -> None:
        for mod_path in module_paths:
            stem = (mod_path.rsplit('.', 1)[-1]
                    if '.' in mod_path else mod_path)
            target_file = stem_map.get(mod_path)
            if not target_file:
                if stem in ambiguous:
                    continue
                target_file = stem_map.get(stem)
            if target_file and os.path.isfile(target_file):
                self._expand_prefix_fns(target_file, mod_path, prefixes)
    def _expand_prefix_fns(self, target_file, target_mod, prefixes) -> None:
        tree = parse_module(target_file, self.scanner._ctx)
        if tree is None:
            return
        prefix_tuple = tuple(sorted(prefixes))
        for top in iter_module_scope_funcdefs(tree):
            if top.name.startswith(prefix_tuple):
                self._add_dynamic_ref(target_mod, top.name)
def _class_method_names(cls_node) -> set[str]:
    return {item.name for item in cls_node.body
            if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef))}
def _collect_local_func_names(tree) -> set[str]:
    names = {node.name for node in iter_module_scope_funcdefs(tree)}
    for node in iter_module_scope_nodes(tree, descend_classes=False):
        if isinstance(node, ast.ClassDef):
            names.update(_class_method_names(node))
    return names
def _dotted_module_name(rel: str) -> str:
    parts = rel_to_dotted_module(rel).split('.')
    if parts[-1] == '__init__':
        parts = parts[:-1]
    return '.'.join(parts)
def _parse_scan_target(scanner, filepath):
    tree = parse_module(filepath, scanner._ctx)
    if tree is None:
        return None
    rel = _rel_to_root(scanner.project_root, filepath)
    if rel is None:
        return None
    return rel.replace('\\', '/'), tree
def _class_scope_assign_ids(tree) -> set[int]:
    ids: set[int] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        for sub in iter_own_nodes(node):
            if isinstance(sub, (ast.Assign, ast.AnnAssign)):
                ids.add(id(sub))
    return ids
def _ns_is_import_module(node) -> bool:
    func = node.func
    return isinstance(func, ast.Attribute) and func.attr == 'import_module'
def _ns_is_enumeration(node) -> bool:
    func = node.func
    if isinstance(func, ast.Name):
        return func.id == 'dir' and bool(node.args)
    if not isinstance(func, ast.Attribute):
        return False
    return (func.attr == 'getmembers'
            or (func.attr == 'items' and isinstance(func.value, ast.Call)
                and isinstance(func.value.func, ast.Name)
                and func.value.func.id == 'vars'))
def _ns_prefix_literal(node) -> str | None:
    func = node.func
    if not (isinstance(func, ast.Attribute) and func.attr == 'startswith'
            and node.args):
        return None
    arg0 = node.args[0]
    if (isinstance(arg0, ast.Constant) and isinstance(arg0.value, str)
            and arg0.value.startswith('_')):
        return arg0.value
    return None
def _collect_ns_evidence(tree) -> tuple[bool, bool, set[str]]:
    import_module_seen = False
    ns_enum_seen = False
    prefixes: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        if _ns_is_import_module(node):
            import_module_seen = True
        if _ns_is_enumeration(node):
            ns_enum_seen = True
        prefix = _ns_prefix_literal(node)
        if prefix is not None:
            prefixes.add(prefix)
    return import_module_seen, ns_enum_seen, prefixes
def _seq_element_path(elt, import_module_seen, import_bindings) -> str | None:
    if (import_module_seen and isinstance(elt, ast.Constant)
            and isinstance(elt.value, str) and elt.value):
        return elt.value
    if (import_bindings and isinstance(elt, ast.Name)
            and elt.id in import_bindings):
        return import_bindings[elt.id]
    return None
def _seq_module_names(value, import_module_seen, import_bindings) -> list[str]:
    names: list[str] = []
    for elt in value.elts:
        path = _seq_element_path(elt, import_module_seen, import_bindings)
        if path is not None:
            names.append(path)
    return names
def _module_string_constant_bindings(tree) -> dict[str, str]:
    bindings: dict[str, str] = {}
    for top in iter_module_scope_nodes(tree, descend_classes=False):
        normalized = assign_targets_value(top)
        if normalized is None:
            continue
        targets, value = normalized
        if not (isinstance(value, ast.Constant)
                and isinstance(value.value, str) and value.value):
            continue
        for target in targets:
            if isinstance(target, ast.Name):
                bindings[target.id] = value.value
    return bindings
def _module_string_sequence_bindings(tree) -> dict[str, list[str]]:
    bindings: dict[str, list[str]] = {}
    for top in iter_module_scope_nodes(tree, descend_classes=False):
        normalized = assign_targets_value(top)
        if normalized is None:
            continue
        targets, value = normalized
        if not isinstance(value, (ast.List, ast.Tuple, ast.Set)):
            continue
        items = [elt.value for elt in value.elts
                 if isinstance(elt, ast.Constant)
                 and isinstance(elt.value, str) and elt.value]
        if not items:
            continue
        for target in targets:
            if isinstance(target, ast.Name):
                bindings[target.id] = list(items)
    return bindings
def _imported_sequence_values(import_bindings, name, stem_map,
                              ctx) -> list[str]:
    dotted = import_bindings.get(name)
    if not dotted or '.' not in dotted:
        return []
    module_path, const_name = dotted.rsplit('.', 1)
    stem = module_path.rsplit('.', 1)[-1]
    target = stem_map.get(module_path) or stem_map.get(stem)
    if not target or not os.path.isfile(target):
        return []
    target_tree = parse_module(target, ctx)
    if target_tree is None:
        return []
    return _module_string_sequence_bindings(target_tree).get(const_name, [])
def _ns_module_paths(tree, import_module_seen, import_bindings,
                     *, stem_map=None, ctx=None) -> list[str]:
    module_paths: list[str] = []
    sequence_bindings = _module_string_sequence_bindings(tree)
    for top in iter_module_scope_nodes(tree, descend_classes=False):
        normalized = assign_targets_value(top)
        if normalized is None:
            continue
        _targets, _value = normalized
        if not any(isinstance(t, ast.Name) for t in _targets):
            continue
        if isinstance(_value, (ast.List, ast.Tuple, ast.Set)):
            module_paths.extend(
                _seq_module_names(_value, import_module_seen, import_bindings))
            continue
        for sub in walk_nodes(_value):
            if not isinstance(sub, ast.Name):
                continue
            if sub.id in sequence_bindings:
                module_paths.extend(sequence_bindings[sub.id])
            elif stem_map is not None:
                module_paths.extend(_imported_sequence_values(
                    import_bindings, sub.id, stem_map, ctx))
    return module_paths
def _stem_disambiguated_map(files) -> tuple[dict[str, str], set[str]]:
    stem_map: dict[str, str] = {}
    ambiguous: set[str] = set()
    for f in files:
        stem = os.path.splitext(os.path.basename(f))[0]
        if stem in stem_map:
            ambiguous.add(stem)
        else:
            stem_map[stem] = f
    return stem_map, ambiguous
def _module_disambiguated_map(project_root, files) -> dict[str, str]:
    module_map: dict[str, str] = {}
    ambiguous: set[str] = set()
    for filepath in files:
        rel = _rel_to_root(project_root, filepath)
        if rel is None:
            continue
        module_name = _dotted_module_name(rel)
        if not module_name:
            continue
        if module_name in module_map:
            ambiguous.add(module_name)
        else:
            module_map[module_name] = filepath
    for module_name in ambiguous:
        module_map.pop(module_name, None)
    return module_map
def scan_dynamic_patterns(scanner, source_paths: list[str] | None, call_graph,
                          files: list[str] | None = None) -> tuple[set[str], set[str]]:
    if files is None:
        files = collect_py_files(
            scanner.project_root, source_paths, ctx=scanner._ctx)
    collector = _DynamicRefCollector(
        scanner, files, call_graph,
        module_stem_index(scanner.project_root, files))
    return collector.collect()
def _collect_module_all_exports(tree, module_name, exports_cache) -> None:
    exports = exports_cache.setdefault(module_name, set())
    for _name in module_export_names(tree):
        exports.add(_qualify(module_name, _name))
        exports.add(_name)
def suppressions_for(filepath: str, ctx=None) -> dict:
    if not filepath:
        return {}
    source = read_source(filepath, ctx)
    if source is None:
        logger.debug('抑制注解读取失败，按无抑制处理: %s', filepath)
        return {}
    return parse_suppressions(source)
def suppressed_declaration(suppressions, func_info: dict, rule_ids) -> bool:
    if not suppressions:
        return False
    start_line = func_info.get('start_line')
    if not (isinstance(start_line, int) and not isinstance(start_line, bool)
            and start_line > 0):
        return False
    first_line = func_info.get('decl_first_line')
    if not (isinstance(first_line, int) and not isinstance(first_line, bool)
            and 0 < first_line <= start_line):
        first_line = start_line
    for probe in range(first_line - 1, start_line + 1):
        if probe <= 0:
            continue
        if any(is_suppressed(suppressions, probe, rid) for rid in rule_ids):
            return True
    return False

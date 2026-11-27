from __future__ import annotations

__all__ = [
    "guard_blast_radius",
    "guard_circular",
    "guard_delete",
]
import ast as _ast
import io
import logging
import os
import re as _re
import tokenize
from collections.abc import Callable, Iterable, Iterator
from importlib import machinery
from typing import NamedTuple, TypedDict

from jwsgj.diag_shared_ast_nodes import (
    FUNC_NODE_TYPES,
    _non_import_time_branch,
    _type_checking_guard_node_polarities,
    extract_all_declarations,
    import_alias_bound_names,
    iter_module_level_stmts,
    module_level_binding_names,
)
from jwsgj.diag_shared_ast_nodes import (
    _prune_non_import_time_branches as _prune_non_import_time_branches,
)
from jwsgj.diag_shared_source_core import read_source
from jwsgj.diag_types_defs import (
    GuardResult,
    OperationContext,
    code_to_write_str,
)
from jwsgj.diag_types_normalize import normalize_files_list
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    PROJECT_ROOT_MARKERS,
    GuardLevel,
    OperationType,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    is_backup_snapshot_dir,
    is_scan_py_name,
    is_temp_artifact_dir,
    is_test_dir_name,
    is_under_root,
    resolve_search_root,
    scan_exclude_dirs,
)

logger = logging.getLogger(__name__)
_SCAN_EXTRA_IGNORE_DIRS_LOWER = frozenset({"$recycle.bin"})
_MAX_ROOT_WALK = 12
_SCAN_ROOT_FANOUT_LIMIT = 256
_FUNCTION_CONTAINER_TYPES = (*FUNC_NODE_TYPES, _ast.Lambda)
def _is_py_source(path: str) -> bool:
    return isinstance(path, str) and is_scan_py_name(os.path.basename(path))
def _iter_module_level_imports(tree: _ast.Module):
    stack: list[_ast.AST] = [tree]
    tc_polarities = _type_checking_guard_node_polarities(tree)
    while stack:
        node = stack.pop()
        if isinstance(node, _FUNCTION_CONTAINER_TYPES):
            continue
        if isinstance(node, _ast.If):
            _branch = _non_import_time_branch(node, tc_polarities)
            if _branch == 'body':
                stack.extend(node.orelse)
                continue
            if _branch == 'orelse':
                stack.extend(node.body)
                continue
        if isinstance(node, (_ast.Import, _ast.ImportFrom)):
            yield node
        stack.extend(_ast.iter_child_nodes(node))
def _from_import_submodule_names(node: _ast.ImportFrom, search_dir: str,
                                 fpath: str, overrides=None) -> set[str]:
    names: set[str] = set()
    for cand in _importfrom_candidate_dirs_by_parts(
            node.module or '', node.level or 0, search_dir, fpath):
        for alias in node.names:
            nm = alias.name
            if _submodule_file_exists(cand, nm, overrides):
                names.add(nm)
    return names
def _scan_excluded_dirs(root_dir: str, *,
                        include_tests: bool) -> frozenset[str]:
    excluded = {name for name in scan_exclude_dirs(root_dir)
                if not (include_tests and is_test_dir_name(name))}
    return frozenset(excluded) | _SCAN_EXTRA_IGNORE_DIRS_LOWER
def _should_scan_dir(name: str, *, excluded: frozenset[str]) -> bool:
    lower = name.lower()
    return (not name.startswith('.')
            and lower not in excluded
            and not is_backup_snapshot_dir(name)
            and not is_temp_artifact_dir(name))
def _module_entry(fpath: str, search_dir: str,
                  root_name: str) -> tuple[str, str, str, bool]:
    rel = os.path.relpath(fpath, search_dir).replace('\\', '/')
    parts = rel[:-3].split('/')
    is_package = _is_init_stem(parts[-1])
    if is_package:
        parts = parts[:-1]
    qual = '.'.join(parts) or root_name
    return fpath, qual, qual.rsplit('.', 1)[-1], is_package
def _shadowed_module_stems(cur: str, dirs: Iterable[str]) -> set[str]:
    return {os.path.normcase(name) for name in dirs
            if os.path.isfile(os.path.join(cur, name, '__init__.py'))}
def _iter_py_modules(search_dir: str):
    root_name = os.path.basename(os.path.abspath(search_dir))
    excluded = _scan_excluded_dirs(search_dir, include_tests=False)
    for cur, dirs, files in os.walk(search_dir):
        dirs[:] = [d for d in dirs
                   if _should_scan_dir(d, excluded=excluded)]
        shadowed = _shadowed_module_stems(cur, dirs)
        for fname in files:
            if not is_scan_py_name(fname):
                continue
            stem = fname[:-3]
            if not _is_init_stem(stem) and os.path.normcase(stem) in shadowed:
                logger.debug("[Guard] 模块被同名包遮蔽,跳过建图: %s",
                             os.path.join(cur, fname))
                continue
            yield _module_entry(os.path.join(cur, fname), search_dir,
                                root_name)
class _ModuleIndex:
    def __init__(self, entries: list[tuple[str, str, str, bool]],
                 package_prefixes: Iterable[str] = ()) -> None:
        self._id_of_qual: dict[str, str] = {}
        self._qual_of_id: dict[str, str] = {}
        self._package_of_id: dict[str, str] = {}
        self._short_counts: dict[str, int] = {}
        self._package_prefixes = tuple(package_prefixes)
        for _fpath, _qual, short, _is_pkg in entries:
            self._short_counts[short] = self._short_counts.get(short, 0) + 1
        for _fpath, qual, short, is_pkg in entries:
            node_id = short if self._short_counts[short] == 1 else qual
            self._id_of_qual[qual] = node_id
            self._qual_of_id[node_id] = qual
            self._package_of_id[node_id] = (qual if is_pkg
                                            else qual.rpartition('.')[0])
    def id_of_qual(self, qual: str) -> str | None:
        return self._id_of_qual.get(qual)
    def root_package_ids(self) -> tuple[str, ...]:
        return tuple(sorted(
            node_id for node_id, qual in self._qual_of_id.items()
            if '.' not in qual and self._package_of_id.get(node_id) == qual))
    def _base_package(self, importer_id: str, level: int) -> str | None:
        base = self._package_of_id.get(importer_id)
        if base is None:
            return None
        for _ in range(max(0, level - 1)):
            base = base.rpartition('.')[0]
            if not base:
                return None
        return base
    def _resolve_qualified(self, target: str) -> str | None:
        exact = self._id_of_qual.get(target)
        if exact is not None:
            return exact
        for prefix in self._package_prefixes:
            if target == prefix:
                root_id = self._id_of_qual.get(prefix.rsplit('.', 1)[-1])
                if root_id is not None:
                    return root_id
            if target.startswith(prefix + '.'):
                return self._id_of_qual.get(target[len(prefix) + 1:])
        return None
    def resolve(self, target: str, importer_id: str, level: int = 0) -> str | None:
        if level:
            base = self._base_package(importer_id, level)
            if base is None:
                return None
            target = f"{base}.{target}" if base else target
        return self._resolve_qualified(target) if target else None
def _load_module_tree(fpath: str, cache, overrides):
    override = (overrides or {}).get(os.path.realpath(fpath))
    try:
        source = None
        tree = None
        if override is None and cache is not None:
            try:
                source = cache.get_source(fpath)
                tree = cache.get_ast(fpath)
            except Exception:
                logger.debug("[Guard] 共享缓存读取异常回退直读: %s", fpath,
                             exc_info=True)
                source = None
        if source is None:
            source = override if override is not None else read_source(fpath)
        if source is None:
            logger.warning("[Guard] 建图读文件失败,跳过该文件: %s", fpath)
            return None
        if tree is None:
            tree = _ast.parse(source, filename=fpath)
        return _prune_non_import_time_branches(tree)
    except (OSError, *PARSE_DEGRADE_EXC) as exc:
        logger.warning("[Guard] 建图读文件/解析失败,跳过该文件: %s (%s)",
                       fpath, exc)
        return None
def _package_init_targets(module: str, level: int, search_dir: str,
                          fpath: str) -> Iterator[tuple[str, int]]:
    """导入语句隐含触发的「中间包 __init__ 执行」目标。

    只产出 ``a.b.c`` 的**中间**包（``a``、``a.b``），不再产出相对导入的
    自身包（``from .sub import X`` 里的 ``base``）。后者是结构性事实——包内
    任何模块都依赖自己的 ``__init__``——而包的 ``__init__`` 又几乎总会再导出
    子模块，于是 ``pkg/__init__ → pkg.sub → pkg`` 会被判成循环依赖。
    这不是缺陷而是门面（facade）模式，G12 会把每一个带再导出的包都报出来。
    真实循环仍由子模块之间的边捕获（``from . import sub`` 走
    ``_from_import_submodule_names``，绝对导入走模块名）。
    """
    parts = [part for part in module.split('.') if part]
    if level:
        base = _relative_base_package(fpath, search_dir, level)
        if not base:
            return
        for size in range(1, len(parts)):
            yield f"{base}.{'.'.join(parts[:size])}", 0
        return
    for size in range(1, len(parts)):
        yield '.'.join(parts[:size]), 0
def _importfrom_targets(node: _ast.ImportFrom, search_dir: str,
                        fpath: str, overrides=None):
    level = int(node.level or 0)
    yield from _package_init_targets(
        node.module or '', level, search_dir, fpath)
    if not node.module:
        submodules = _from_import_submodule_names(
            node, search_dir, fpath, overrides)
        for sub in sorted(submodules):
            yield sub, level
        return
    yield node.module, level
    for sub in _from_import_submodule_names(
            node, search_dir, fpath, overrides):
        yield f"{node.module}.{sub}", level
def _import_targets_for(node, search_dir: str, fpath: str, overrides=None):
    if isinstance(node, _ast.Import):
        for alias in node.names:
            yield from _package_init_targets(
                alias.name, 0, search_dir, fpath)
            yield alias.name, 0
    elif isinstance(node, _ast.ImportFrom):
        yield from _importfrom_targets(node, search_dir, fpath, overrides)
def _override_entries(entries: list, search_dir: str,
                      overrides) -> list[tuple[str, str, str, bool]]:
    if not overrides:
        return []
    known = {os.path.realpath(entry[0]) for entry in entries}
    root_name = os.path.basename(os.path.abspath(search_dir))
    extra: list[tuple[str, str, str, bool]] = []
    for fpath in overrides:
        if (os.path.realpath(fpath) in known
                or not _is_py_source(fpath)
                or not is_under_root(fpath, search_dir)):
            continue
        extra.append(_module_entry(fpath, search_dir, root_name))
    return extra
def _indexed_graph(search_dir: str, cache,
                   overrides) -> tuple[dict[str, set[str]], _ModuleIndex]:
    entries = list(_iter_py_modules(search_dir))
    entries.extend(_override_entries(entries, search_dir, overrides))
    index = _ModuleIndex(entries, _search_package_prefixes(search_dir))
    return _graph_for_entries(
        search_dir, entries, index, cache, overrides), index
def _edge_targets(index: _ModuleIndex, node_id: str, node,
                  search_dir: str, fpath: str, overrides=None) -> Iterator[str]:
    for target, level in _import_targets_for(
            node, search_dir, fpath, overrides):
        yield index.resolve(target, node_id, level) or target
def _graph_for_entries(search_dir: str, entries: list, index: _ModuleIndex,
                       cache, overrides) -> dict[str, set[str]]:
    graph: dict[str, set[str]] = {}
    for fpath, qual, _short, _is_pkg in entries:
        node_id = index.id_of_qual(qual)
        tree = _load_module_tree(fpath, cache, overrides)
        if tree is None or node_id is None:
            continue
        edges = graph.setdefault(node_id, set())
        for node in _iter_module_level_imports(tree):
            for target in _edge_targets(index, node_id, node, search_dir,
                                        fpath, overrides):
                if target and target != node_id:
                    edges.add(target)
    return graph
def _build_internal_adjacency(graph: dict[str, set[str]]) -> dict[str, set[str]]:
    adj: dict[str, set[str]] = {}
    all_nodes = set(graph.keys())
    for src, targets in graph.items():
        for tgt in targets:
            if tgt in all_nodes:
                adj.setdefault(src, set()).add(tgt)
    return adj
def _drop_facade_node(adj: dict[str, set[str]],
                      facade: str | Iterable[str] | None) -> dict[str, set[str]]:
    """剔除**包门面节点**（``__init__``）在环检测中的出边。

    ``jwsgj/__init__.py`` 是全量再导出门面：子模块里的
    ``from jwsgj.x import y`` 会被解析成经过包节点的边，于是任意两个
    「A 导入 jwsgj.x、jwsgj.x 导入 B、B 导入 jwsgj.a」的模块都构成环。
    但包初始化永远先于子模块，运行时不会出现部分初始化——这类经过门面的
    环是**再导出门面模式的固有形态**，不是循环导入缺陷（实测 719/719 条
    环全部经过包节点）。子模块之间的真实环不经过门面，仍然照常检出。
    """
    facades = {facade} if isinstance(facade, str) else set(facade or ())
    if not facades or facades.isdisjoint(adj):
        return adj
    return {src: targets for src, targets in adj.items() if src not in facades}
def _find_cycles(graph: dict[str, set[str]],
                 facade_node: str | Iterable[str] | None = None) -> list[list[str]]:
    adj = _drop_facade_node(_build_internal_adjacency(graph), facade_node)
    cycles = []
    color: dict[str, int] = {}
    path: list[str] = []
    for node in sorted(graph):
        if color.get(node, 0) != 0:
            continue
        color[node] = 1
        path.append(node)
        stack = [iter(sorted(adj.get(node, ())))]
        while stack:
            neighbor = next(stack[-1], None)
            if neighbor is None:
                stack.pop()
                color[path.pop()] = 2
                continue
            state = color.get(neighbor, 0)
            if state == 0:
                color[neighbor] = 1
                path.append(neighbor)
                stack.append(iter(sorted(adj.get(neighbor, ()))))
            elif state == 1:
                cycle_start = path.index(neighbor)
                cycles.append([*path[cycle_start:], neighbor])
    return cycles
def _cyclic_graph_nodes(graph: dict[str, set[str]],
                        facade_node: str | Iterable[str] | None = None) -> set[str]:
    adj = _drop_facade_node(_build_internal_adjacency(graph), facade_node)
    finish_order: list[str] = []
    visited: set[str] = set()
    for root in sorted(graph):
        if root in visited:
            continue
        visited.add(root)
        stack = [(root, iter(sorted(adj.get(root, ()))))]
        while stack:
            node, neighbors = stack[-1]
            neighbor = next(neighbors, None)
            if neighbor is None:
                finish_order.append(node)
                stack.pop()
            elif neighbor not in visited:
                visited.add(neighbor)
                stack.append((neighbor, iter(sorted(adj.get(neighbor, ())))))
    reverse = {node: set() for node in graph}
    for src, targets in adj.items():
        for target in targets:
            reverse[target].add(src)
    visited.clear()
    cyclic: set[str] = set()
    for root in reversed(finish_order):
        if root in visited:
            continue
        component: list[str] = []
        stack = [root]
        visited.add(root)
        while stack:
            node = stack.pop()
            component.append(node)
            for neighbor in sorted(reverse[node], reverse=True):
                if neighbor not in visited:
                    visited.add(neighbor)
                    stack.append(neighbor)
        if len(component) > 1 or root in adj.get(root, ()):
            cyclic.update(component)
    return cyclic
class _CycleScope(NamedTuple):
    cycle_modules: frozenset[str]
    package_prefixes: tuple[str, ...]
    index: _ModuleIndex | None
    importer_id: str | None
def _importer_node_id(index: _ModuleIndex | None, fpath: str,
                      search_dir: str) -> str | None:
    if index is None or not fpath or not search_dir:
        return None
    dotted, _base = _rel_module_of(fpath, search_dir)
    if (not dotted and _is_init_file(fpath)
            and _path_identity(os.path.dirname(fpath))
            == _path_identity(search_dir)):
        dotted = os.path.basename(os.path.abspath(search_dir))
    return index.id_of_qual(dotted) if dotted else None
def _cycle_issue(filename: str, import_repr: str, lineno: int) -> str:
    return (f"{filename}: 顶层 `{import_repr}` "
            f"（第 {lineno} 行）参与循环导入环，"
            f"建议下沉共享依赖到独立模块或经包入口注入，"
            f"保持模块顶部 import")
def _module_ref_hits(name: str, cycle_modules: frozenset | set,
                     package_prefixes: Iterable[str] = (),
                     allow_short: bool = False) -> bool:
    if not name:
        return False
    if name in cycle_modules:
        return True
    for prefix in package_prefixes:
        if (prefix and name.startswith(prefix + '.')
                and name[len(prefix) + 1:] in cycle_modules):
            return True
    return allow_short and '.' in name and name.rsplit('.', 1)[-1] in cycle_modules
def _cycle_hit(scope: _CycleScope, target: str,
               allow_short: bool = False) -> bool:
    if scope.index is not None and scope.importer_id and target:
        node_id = scope.index.resolve(target, scope.importer_id)
        if node_id is not None:
            return node_id in scope.cycle_modules
    return _module_ref_hits(target, scope.cycle_modules,
                            scope.package_prefixes, allow_short)
def _importfrom_module_target(node: _ast.ImportFrom, search_dir: str,
                              fpath: str) -> str:
    module = node.module or ''
    if not node.level or not (search_dir and fpath):
        return module
    fp_rel = os.path.relpath(os.path.abspath(fpath), search_dir).replace('\\', '/')
    if fp_rel.startswith('../'):  # jwsgj:suppress SS-02 — 路径守卫判定，非路径访问
        return module
    resolved = _resolve_relative_module(
        fp_rel, node.level, module or None, _pkg_prefix_for(search_dir))
    return resolved if resolved is not None else ""
def _mark_confirmed_submodule_aliases(node: _ast.ImportFrom, filename: str,
                                      scope: _CycleScope,
                                      search_dir: str, fpath: str) -> list[str]:
    issues: list[str] = []
    _subs = _from_import_submodule_names(node, search_dir, fpath)
    if not _subs:
        return issues
    _rel_prefix = '.' * node.level
    _base = _importfrom_module_target(node, search_dir, fpath)
    for _alias in node.names:
        _target = f"{_base}.{_alias.name}" if _base else _alias.name
        if _alias.name in _subs and _cycle_hit(scope, _target,
                                               allow_short=True):
            issues.append(_cycle_issue(
                filename,
                f"from {_rel_prefix}{node.module} import {_alias.name}",
                node.lineno))
    return issues
def _mark_bare_importfrom_cycle(node: _ast.ImportFrom, filename: str,
                                scope: _CycleScope,
                                search_dir: str, fpath: str) -> list[str]:
    prefix = '.' * node.level
    has_paths = bool(fpath and search_dir)
    if has_paths:
        pkg = _relative_base_package(fpath, search_dir, node.level)
        if pkg is None:
            return []
    else:
        pkg = ''
    submodules = (_from_import_submodule_names(node, search_dir, fpath)
                  if has_paths else set())
    issues: list[str] = []
    for alias in node.names:
        _target = pkg if alias.name == '*' else (
            f"{pkg}.{alias.name}" if pkg else alias.name)
        resolved = (scope.index.resolve(_target, scope.importer_id)
                    if scope.index is not None and scope.importer_id
                    else None)
        is_submodule = (not has_paths or alias.name in submodules
                        or resolved is not None)
        target = _target if alias.name == '*' or is_submodule else pkg
        if _cycle_hit(scope, target, allow_short=True):
            issues.append(_cycle_issue(
                filename, f"from {prefix} import {alias.name}", node.lineno))
    return issues
def _mark_importfrom_cycle(node: _ast.ImportFrom, filename: str,
                           scope: _CycleScope,
                           search_dir: str, fpath: str) -> list[str]:
    if not node.module:
        return _mark_bare_importfrom_cycle(
            node, filename, scope, search_dir, fpath)
    prefix = '.' * node.level
    _target = _importfrom_module_target(node, search_dir, fpath)
    if _cycle_hit(scope, _target):
        return [_cycle_issue(filename,
                             f"from {prefix}{node.module} import ...",
                             node.lineno)]
    if search_dir and fpath:
        return _mark_confirmed_submodule_aliases(
            node, filename, scope, search_dir, fpath)
    return []
def _mark_import_cycle_aliases(node: _ast.Import, filename: str,
                               scope: _CycleScope) -> list[str]:
    issues: list[str] = []
    for alias in node.names:
        if _cycle_hit(scope, alias.name):
            issues.append(_cycle_issue(
                filename, f"import {alias.name}", node.lineno))
    return issues
def _check_top_level_imports(source: str, filename: str,
                             cycle_modules: frozenset[str] | set[str] | None,
                             search_dir: str, fpath: str,
                             index: _ModuleIndex | None = None) -> list[str]:
    issues = []
    if not cycle_modules:
        return issues
    importer_id = _importer_node_id(index, fpath, search_dir)
    if index is not None and importer_id not in cycle_modules:
        return issues
    try:
        tree = _ast.parse(source)
    except PARSE_DEGRADE_EXC as exc:
        logger.warning("[Guard] 源码语法错误或解析爆栈,跳过环内导入标记: %s (%s)",
                       filename, exc)
        return issues
    tree = _prune_non_import_time_branches(tree)
    scope = _CycleScope(
        frozenset(cycle_modules),
        tuple(_search_package_prefixes(search_dir)) if search_dir else (),
        index, importer_id)
    for node in _iter_module_level_imports(tree):
        if isinstance(node, _ast.ImportFrom):
            issues.extend(_mark_importfrom_cycle(
                node, filename, scope, search_dir, fpath))
        elif isinstance(node, _ast.Import):
            issues.extend(_mark_import_cycle_aliases(node, filename, scope))
    return issues
def _is_scan_container_root(path: str) -> bool:
    try:
        dir_count = 0
        with os.scandir(path) as entries:
            for entry in entries:
                if not entry.is_dir(follow_symlinks=False):
                    continue
                dir_count += 1
                if dir_count > _SCAN_ROOT_FANOUT_LIMIT:
                    return True
    except OSError as exc:
        logger.debug("[Guard] 目录不可枚举，按非容器处理: %s (%s)", path, exc)
        return False
    return False
def _find_project_root(start_dir: str) -> str:
    cur = os.path.abspath(start_dir)
    for _ in range(_MAX_ROOT_WALK):
        if (any(os.path.exists(os.path.join(cur, marker))
                for marker in PROJECT_ROOT_MARKERS)
                and not _is_scan_container_root(cur)):
            return cur
        parent = os.path.dirname(cur)
        if parent == cur:
            break
        cur = parent
    return ""
def _clamp_to_project_root(candidate: str, project_root: str) -> str:
    if not candidate or not project_root:
        return candidate
    if is_under_root(candidate, project_root):
        return candidate
    logger.debug(
        "[Guard] 搜索根 %s 超出项目根 %s，已钳制到项目根",
        candidate, project_root)
    return project_root
def _nearest_package_root(start_dir: str) -> str:
    cur = start_dir
    for _ in range(_MAX_ROOT_WALK):
        if not cur or os.path.exists(os.path.join(cur, '__init__.py')):
            return cur
        parent = os.path.dirname(cur)
        if parent == cur:
            return ""
        cur = parent
    return ""
def _resolve_g12_search_dir(search_dir: str, target: str) -> str:
    if (search_dir and os.path.isdir(search_dir)
            and (not target or is_under_root(target, search_dir))):
        return search_dir
    if not target:
        return ""
    start_dir = (os.path.abspath(target) if os.path.isdir(target)
                 else os.path.dirname(os.path.abspath(target)))
    project_root = _find_project_root(start_dir)
    pkg_root = _outermost_package_root(start_dir)
    if pkg_root:
        pkg_root = _clamp_to_project_root(pkg_root, project_root)
        if os.path.dirname(pkg_root) == pkg_root:
            logger.debug("[Guard] 包根位于盘根,跳过全盘建图: %s", target)
            return ""
        return pkg_root
    nearest = _nearest_package_root(start_dir)
    if not nearest:
        fallback = resolve_search_root(start_dir)
        fallback = _clamp_to_project_root(fallback, project_root) or fallback
        if _is_scan_container_root(fallback):
            logger.debug("[Guard] 回落根是容器目录,改用目标目录: %s", fallback)
            return start_dir
        return fallback
    nearest = _clamp_to_project_root(nearest, project_root)
    outer = _outermost_package_root(nearest)
    if outer and os.path.dirname(outer) != outer:
        return _clamp_to_project_root(outer, project_root)
    return nearest
def _detect_import_cycles(
        search_dir: str, cache, overrides,
) -> tuple[list[list[str]], set[str], _ModuleIndex | None]:
    if not search_dir or not os.path.isdir(search_dir):
        return [], set(), None
    graph, index = _indexed_graph(search_dir, cache, overrides)
    facades = (index.root_package_ids()
               or (os.path.basename(os.path.normpath(search_dir)),))
    cycles = _find_cycles(graph, facade_node=facades)
    if not cycles:
        return [], set(), index
    cycle_ids = (_cyclic_graph_nodes(graph, facade_node=facades)
                 .difference(facades))
    return cycles, cycle_ids, index
def guard_circular(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _IMPORT_GUARD_OPS:
        return _passed("G12", "非导入相关操作,跳过循环导入检查")
    issues = []
    _meta_search_dir = ctx.metadata.get("search_dir")
    search_dir = (_meta_search_dir if isinstance(_meta_search_dir, str) else "")
    target = ctx.target_path
    search_dir = _resolve_g12_search_dir(search_dir, target)
    if not search_dir:
        logger.debug("[Guard] G12 未确定扫描根,跳过循环导入检查")
        return _passed("G12", "未确定扫描根,跳过循环导入检查")
    pending = _pending_write_source(ctx, target)
    overrides = ({os.path.realpath(pending[0]): pending[1]}
                 if pending else None)
    cycles, cycle_modules, index = _detect_import_cycles(
        search_dir, ctx.metadata.get('shared_cache'), overrides)
    for cycle in cycles:
        cycle_str = " → ".join(cycle)
        issues.append(f"检测到循环导入: {cycle_str}")
    for fpath, source in _iter_guard_py_sources(ctx):
        top_issues = _check_top_level_imports(
            source, os.path.basename(fpath), cycle_modules, search_dir, fpath,
            index)
        issues.extend(top_issues)
    return _guard_outcome(
        "G12", "循环导入", "循环导入检查通过", issues,
        "重构模块结构消除循环依赖:将共享接口提取到"
        "独立的 base/core 模块,或将循环双方的公共依赖"
        "下沉至上游模块.")
def _extract_public_symbols_from_ast(
        tree: _ast.Module, *, include_imports: bool) -> set[str]:
    pruned = _prune_non_import_time_branches(tree)
    symbols = {name for name in module_level_binding_names(pruned)
               if name and not name.startswith('_')}
    if include_imports:
        symbols.update(
            name for node in iter_module_level_stmts(pruned)
            if isinstance(node, (_ast.Import, _ast.ImportFrom))
            for name in import_alias_bound_names(node)
            if name and not name.startswith('_'))
    symbols |= {name for name in extract_all_declarations(pruned) if name}
    return symbols
def _load_ast(filepath: str, tag: str) -> _ast.Module | None:
    source = read_source(filepath)
    if source is None:
        logger.warning("[%s] 读取 %s 失败,跳过", tag, filepath)
        return None
    try:
        return _ast.parse(source)
    except PARSE_DEGRADE_EXC as e:
        logger.warning("[%s] %s 源码不可解析,跳过: %s", tag, filepath, e)
        return None
def _iter_py_files(root: str) -> Iterator[str]:
    excluded = _scan_excluded_dirs(root, include_tests=True)
    for dirpath, dirs, filenames in os.walk(root):
        dirs[:] = [d for d in dirs
                   if _should_scan_dir(d, excluded=excluded)]
        for fn in filenames:
            if is_scan_py_name(fn):
                yield os.path.join(dirpath, fn)
def _pkg_init_chain(target_path: str, mod_name: str,
                    target_is_pkg_init: bool) -> list[tuple[str, str]]:
    levels: list[tuple[str, str]] = []
    cur = (os.path.dirname(os.path.dirname(target_path))
           if target_is_pkg_init else os.path.dirname(target_path))
    suffix = mod_name
    while os.path.isfile(os.path.join(cur, '__init__.py')):
        levels.append((cur, suffix))
        parent = os.path.dirname(cur)
        if parent == cur:
            break
        suffix = f"{os.path.basename(cur)}.{suffix}"
        cur = parent
    return levels
class _ExportProbe(NamedTuple):
    suffix: str
    full_dotted: str
    parent_abs: str | None
    parent_rel: str
    mod_name: str
    symbols: frozenset[str]
def _iter_export_bearing_stmts(
        body, *, tc_polarities=None) -> Iterator[_ast.stmt]:
    for node in body:
        if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef,
                              _ast.ClassDef, _ast.Lambda)):
            continue
        if isinstance(node, _ast.ImportFrom):
            yield node
            continue
        if isinstance(node, _ast.If):
            _branch = _non_import_time_branch(node, tc_polarities)
            if _branch == 'body':
                yield from _iter_export_bearing_stmts(
                    node.orelse, tc_polarities=tc_polarities)
                continue
            if _branch == 'orelse':
                yield from _iter_export_bearing_stmts(
                    node.body, tc_polarities=tc_polarities)
                continue
            yield from _iter_export_bearing_stmts(
                node.body, tc_polarities=tc_polarities)
            yield from _iter_export_bearing_stmts(
                node.orelse, tc_polarities=tc_polarities)
            continue
        for part in _iter_block_parts(node):
            if isinstance(part, list):
                yield from _iter_export_bearing_stmts(
                    part, tc_polarities=tc_polarities)
def _init_export_evidence(init_tree: _ast.Module, init_path: str,
                          probe: _ExportProbe) -> list[str]:
    msgs: list[str] = []
    tc_polarities = _type_checking_guard_node_polarities(init_tree)
    for node in _iter_export_bearing_stmts(
            init_tree.body, tc_polarities=tc_polarities):
        if isinstance(node, _ast.ImportFrom):
            msgs.extend(_importfrom_export_msgs(
                node, init_path, probe))
    return msgs
def _imports_name(aliases: list[_ast.alias], wanted: str) -> bool:
    return any(alias.name == wanted for alias in aliases)
def _direct_import_export_msgs(node: _ast.ImportFrom, init_path: str,
                               mod_name: str,
                               symbols: frozenset[str]) -> list[str]:
    msgs: list[str] = []
    for alias in node.names:
        if alias.name == '*':
            msgs.append(f"{init_path} star 导出 {mod_name} 全部公开符号")
        elif alias.name in symbols:
            msgs.append(f"{init_path} 导出了 {alias.name}")
    return msgs
def _matched_parent_path(node: _ast.ImportFrom, module: str,
                         probe: _ExportProbe) -> str | None:
    if node.level > 1 or probe.mod_name == '__init__':
        return None
    candidates = ((probe.parent_abs, probe.parent_rel) if node.level == 0
                  else (probe.parent_rel,))
    return module if module and module in candidates else None
def _parent_reexport_msgs(node: _ast.ImportFrom, init_path: str, *,
                         parent_path: str | None,
                         mod_name: str) -> list[str]:
    if parent_path is None or not _imports_name(node.names, mod_name):
        return []
    return [f"{init_path} re-export 模块 {mod_name}"]
def _importfrom_export_msgs(node: _ast.ImportFrom, init_path: str,
                            probe: _ExportProbe) -> list[str]:
    if node.level > 1:
        return []
    module = node.module or ''
    if module == probe.suffix or module == probe.full_dotted:
        return _direct_import_export_msgs(
            node, init_path, probe.mod_name, probe.symbols)
    if (node.module is None and node.level == 1
            and probe.suffix == probe.mod_name
            and _imports_name(node.names, probe.mod_name)):
        return [f"{init_path} re-export 模块 {probe.mod_name}"]
    return _parent_reexport_msgs(
        node, init_path,
        parent_path=_matched_parent_path(node, module, probe),
        mod_name=probe.mod_name)
class _ExporterScan(NamedTuple):
    symbols: frozenset
    levels: list
    mod_name: str
    full_dotted: str
    parent_abs: str | None
def _build_exporter_scan(target_path: str, mod_name: str,
                         target_is_pkg_init: bool) -> _ExporterScan | None:
    tree = _load_ast(target_path, "G5")
    if tree is None:
        return None
    symbols = _extract_public_symbols_from_ast(tree, include_imports=True)
    levels = _pkg_init_chain(target_path, mod_name, target_is_pkg_init)
    if not levels:
        return None
    pkg_parts = [os.path.basename(d) for d, _s in levels]
    abs_prefix = '.'.join(reversed(pkg_parts))
    full_dotted = f"{abs_prefix}.{mod_name}" if abs_prefix else mod_name
    parent_abs = full_dotted.rsplit('.', 1)[0] if '.' in full_dotted else None
    return _ExporterScan(frozenset(symbols), levels, mod_name,
                         full_dotted, parent_abs)
def _is_init_stem(stem: str) -> bool:
    return os.path.normcase(stem) == os.path.normcase("__init__")
def _is_init_file(name_or_path: str) -> bool:
    stem = os.path.splitext(os.path.basename(name_or_path))[0]
    return _is_init_stem(stem)
def _find_exporters(target_path: str) -> list[str]:
    exporters: list[str] = []
    if not os.path.isfile(target_path):
        return exporters
    mod_name = os.path.splitext(os.path.basename(target_path))[0]
    target_is_pkg_init = _is_init_stem(mod_name)
    if target_is_pkg_init:
        mod_name = os.path.basename(os.path.dirname(target_path))
    scan = _build_exporter_scan(target_path, mod_name, target_is_pkg_init)
    if scan is None:
        return exporters
    messages = [msg for init_dir, suffix in scan.levels
                for msg in _level_export_messages(init_dir, suffix, scan)]
    return list(dict.fromkeys(messages))
def _level_export_messages(init_dir: str, suffix: str,
                           scan: _ExporterScan) -> list[str]:
    init_path = os.path.join(init_dir, '__init__.py')
    init_tree = _load_ast(init_path, "G5")
    if init_tree is None:
        return []
    init_tree = _prune_non_import_time_branches(init_tree)
    probe = _ExportProbe(
        suffix=suffix, full_dotted=scan.full_dotted, parent_abs=scan.parent_abs,
        parent_rel=(suffix.rsplit('.', 1)[0] if '.' in suffix else ''),
        mod_name=scan.mod_name, symbols=scan.symbols)
    return _init_export_evidence(init_tree, init_path, probe)
def _module_path_parts(rel_posix: str) -> list[str]:
    parts = [p for p in rel_posix.split('/') if p and p != '.']
    return [] if '..' in parts else parts
def _rel_to_module(rel_posix: str) -> tuple[str, str]:
    stem = os.path.splitext(rel_posix)[0]
    parts = _module_path_parts(stem)
    if not parts:
        return '', ''
    if _is_init_stem(parts[-1]):
        if len(parts) == 1:
            return '', ''
        return '.'.join(parts[:-1]), parts[-2]
    return '.'.join(parts), parts[-1]
def _rel_module_of(fpath: str, search_dir: str) -> tuple[str, str]:
    rel = os.path.relpath(fpath, search_dir).replace('\\', '/')
    return _rel_to_module(rel)
def _relative_base_package(fpath: str, search_dir: str,
                           level: int) -> str | None:
    dotted, _base = _rel_module_of(fpath, search_dir)
    is_pkg = _is_init_file(fpath)
    parts = [p for p in (dotted if is_pkg
                         else dotted.rpartition('.')[0]).split('.') if p]
    prefix_parts = [p for p in _pkg_prefix_for(search_dir).split('.') if p]
    chain = prefix_parts + parts
    up = max(0, level - 1)
    if up >= len(chain):
        return None
    return '.'.join(chain[:len(chain) - up]) or None
def _resolve_relative_module(fp_rel: str, level: int,
                             module: str | None,
                             package_prefix: str = "") -> str | None:
    stem = fp_rel.removesuffix('.py')
    parts = [p for p in stem.split('/') if p and p != '.']
    if '..' in parts:
        return None
    pkg_parts = parts[:-1]
    prefix_parts = [p for p in package_prefix.split('.') if p]
    chain = prefix_parts + pkg_parts
    up = level - 1
    if up < 0 or up >= len(chain):
        return None
    base = chain[:len(chain) - up]
    if module:
        base.extend(part for part in module.split('.') if part)
    if not base:
        return None
    return '.'.join(base)
def _refs_of_import_node(node: _ast.Import,
                         match: Callable[[str], bool]) -> list[str]:
    return [f"import {alias.name}" for alias in node.names
            if match(alias.name)]
def _refs_of_importfrom_node(node: _ast.ImportFrom,
                             scan: _RefScanContext) -> list[str]:
    refs: list[str] = []
    if node.level == 0:
        module = node.module or ''
        if scan.match(module):
            refs.append(f"from {module} import ...")
        elif (_is_parent_module(module, scan.parent_pkg, scan.full_parent,
                                scan.full_parents)
              and _imports_name(node.names, scan.base_name)):
            refs.append(f"from {module} import {scan.base_name}")
        return refs
    return _refs_of_relative_importfrom(node, scan)
def _refs_of_relative_importfrom(
        node: _ast.ImportFrom, scan: _RefScanContext) -> list[str]:
    rel_dots = '.' * node.level
    head = f"from {rel_dots}{node.module or ''}"
    resolved = _resolve_relative_module(
        scan.fp_rel, node.level, node.module, scan.pkg_prefix)
    if resolved in scan.exact:
        return [f"{head} import ..."]
    if (resolved is not None
            and _is_parent_module(resolved, scan.parent_pkg, scan.full_parent,
                                  scan.full_parents)
            and _imports_name(node.names, scan.base_name)):
        return [f"{head} import {scan.base_name}"]
    if node.module is None:
        return _from_dot_import_ref_evidence(node, scan, rel_dots)
    return []
def _from_dot_import_ref_evidence(
        node: _ast.ImportFrom, scan: _RefScanContext,
        rel_dots: str) -> list[str]:
    refs: list[str] = []
    for alias in node.names:
        resolved_alias = _resolve_relative_module(
            scan.fp_rel, node.level, alias.name, scan.pkg_prefix)
        if resolved_alias is not None and resolved_alias in scan.exact:
            refs.append(f"from {rel_dots} import {alias.name}")
            break
    return refs
def _resolve_packaged_relative_name(name: str, package: str) -> str:
    level = len(name) - len(name.lstrip('.'))
    if not level or not package:
        return name
    parts = [part for part in package.split('.') if part]
    up = level - 1
    if up >= len(parts):
        return name
    resolved = parts[:len(parts) - up]
    suffix = name[level:]
    if suffix:
        resolved.append(suffix)
    return '.'.join(resolved)
def _refs_of_call_node(node: _ast.Call,
                       scan: _RefScanContext) -> list[str]:
    func = node.func
    fname = func.attr if isinstance(func, _ast.Attribute) else (
        func.id if isinstance(func, _ast.Name) else '')
    if fname not in ('import_module', '__import__'):
        return []
    name_node = (node.args[0] if node.args else next(
        (kw.value for kw in node.keywords if kw.arg == 'name'), None))
    if not (isinstance(name_node, _ast.Constant)
            and isinstance(name_node.value, str)):
        return []
    name = name_node.value
    if fname == '__import__' and name and not name.startswith('.'):
        level_node = (node.args[4] if len(node.args) > 4 else next(
            (kw.value for kw in node.keywords if kw.arg == 'level'), None))
        if (isinstance(level_node, _ast.Constant)
                and isinstance(level_node.value, int)
                and level_node.value > 0):
            resolved = _resolve_relative_module(
                scan.fp_rel, level_node.value, name, scan.pkg_prefix)
            if resolved is not None:
                name = resolved
    if fname == 'import_module' and name.startswith('.'):
        package_node = (node.args[1] if len(node.args) > 1 else next(
            (kw.value for kw in node.keywords if kw.arg == 'package'), None))
        if (isinstance(package_node, _ast.Constant)
                and isinstance(package_node.value, str)):
            name = _resolve_packaged_relative_name(name, package_node.value)
        elif isinstance(package_node, _ast.Name) and package_node.id == '__package__':
            level = len(name) - len(name.lstrip('.'))
            resolved = _resolve_relative_module(
                scan.fp_rel, level, name[level:] or None, scan.pkg_prefix)
            if resolved is not None:
                name = resolved
    return [f"动态导入 {name}"] if scan.match(name) else []
def _build_ref_matcher(exact: set[str],
                       prefix_roots: Iterable[str] = ()) -> Callable[[str], bool]:
    roots = tuple(root for root in prefix_roots if root)
    def _match(mod: str) -> bool:
        return (mod in exact
                or any(mod.startswith(root + '.') for root in roots))
    return _match
def _refs_of_string_literals(tree: _ast.AST,
                             str_targets: set[str]) -> list[str]:
    if not str_targets:
        return []
    for node in walk_nodes(tree):
        if (isinstance(node, _ast.Constant)
                and isinstance(node.value, str)
                and node.value in str_targets):
            return [f"字符串引用 {node.value}"]
    return []
class _RefScanContext(NamedTuple):
    fp_rel: str
    pkg_prefix: str
    parent_pkg: str | None
    full_parent: str | None
    base_name: str
    exact: frozenset[str]
    match: Callable[[str], bool]
    str_targets: frozenset[str]
    full_parents: frozenset[str] = frozenset()
def _nonempty(values) -> frozenset[str]:
    return frozenset(value for value in values if value)
def _build_ref_scan_context(fp_rel: str, pkg_dotted: str,
                            base_name: str, pkg_prefix: str,
                            pkg_prefixes: Iterable[str] = ()) -> _RefScanContext:
    prefixes = tuple(dict.fromkeys(
        prefix for prefix in (pkg_prefix, *pkg_prefixes) if prefix))
    full_names = frozenset(
        f"{prefix}.{pkg_dotted}" if pkg_dotted else prefix
        for prefix in prefixes)
    full = (f"{pkg_prefix}.{pkg_dotted}" if pkg_dotted else pkg_prefix) \
        if pkg_prefix else ''
    exact = ({pkg_dotted} if pkg_dotted else set()) | set(full_names)
    return _RefScanContext(
        fp_rel=fp_rel,
        pkg_prefix=pkg_prefix,
        parent_pkg=pkg_dotted.rsplit('.', 1)[0] if '.' in pkg_dotted else None,
        full_parent=full.rsplit('.', 1)[0] if full and '.' in full else None,
        base_name=base_name,
        exact=frozenset(exact),
        match=_build_ref_matcher(exact, exact),
        str_targets=_nonempty(t for t in exact if '.' in t),
        full_parents=frozenset(
            name.rsplit('.', 1)[0] for name in full_names if '.' in name),
    )
def _is_parent_module(module: str, parent_pkg: str | None,
                      full_parent: str | None,
                      full_parents: Iterable[str] = ()) -> bool:
    return bool((parent_pkg and module == parent_pkg)
                or (full_parent and module == full_parent)
                or module in full_parents)
def _refs_of_ast_node(node: _ast.AST, scan: _RefScanContext) -> list[str]:
    if isinstance(node, _ast.Import):
        return _refs_of_import_node(node, scan.match)
    if isinstance(node, _ast.ImportFrom):
        return _refs_of_importfrom_node(node, scan)
    if isinstance(node, _ast.Call):
        return _refs_of_call_node(node, scan)
    return []
def _ast_references_module(tree: _ast.AST, fp_rel: str, pkg_dotted: str,
                           base_name: str, pkg_prefix: str,
                           pkg_prefixes: Iterable[str] = ()) -> list[str]:
    scan = _build_ref_scan_context(
        fp_rel, pkg_dotted, base_name, pkg_prefix, pkg_prefixes)
    refs: list[str] = []
    for node in walk_nodes(tree):
        refs.extend(_refs_of_ast_node(node, scan))
    refs.extend(_refs_of_string_literals(tree, set(scan.str_targets)))
    return refs
_TEXT_TOKEN_IGNORE = frozenset({
    tokenize.ENCODING, tokenize.NL, tokenize.COMMENT, tokenize.INDENT,
    tokenize.DEDENT, tokenize.ENDMARKER,
})
def _iter_text_tokens(
        content: str) -> Iterator[tokenize.TokenInfo | None]:
    lines = content.splitlines(keepends=True)
    offset = 0
    while offset < len(lines):
        segment = ''.join(lines[offset:])
        try:
            for token in tokenize.generate_tokens(io.StringIO(segment).readline):
                if offset:
                    token = token._replace(
                        start=(token.start[0] + offset, token.start[1]),
                        end=(token.end[0] + offset, token.end[1]))
                yield token
            return
        except (tokenize.TokenError, IndentationError, SyntaxError) as exc:
            logger.debug("[G5] 文本词法扫描跳过错误物理行并继续: %s", exc)
            yield None
            lineno = getattr(exc, 'lineno', None)
            if lineno is None and isinstance(exc, tokenize.TokenError):
                position = exc.args[1] if len(exc.args) > 1 else None
                if isinstance(position, tuple) and position:
                    lineno = position[0]
            if not isinstance(lineno, int) or lineno < 1:
                return
            next_offset = offset + lineno
            if next_offset >= len(lines):
                return
            offset = next_offset
def _iter_text_import_tokens(content: str) -> Iterator[list[tokenize.TokenInfo]]:
    statement: list[tokenize.TokenInfo] = []
    for token in _iter_text_tokens(content):
        if token is None:
            if statement:
                yield statement
                statement = []
            continue
        if not statement:
            if (token.type == tokenize.NAME
                    and token.string in ('import', 'from')):
                statement = [token]
            continue
        if token.type == tokenize.NEWLINE or token.string == ';':
            yield statement
            statement = []
        elif token.type not in _TEXT_TOKEN_IGNORE:
            statement.append(token)
    if statement:
        yield statement
def _valid_absolute_module(module: str) -> bool:
    return bool(_re.fullmatch(r'\w+(?:\.\w+)*', module))
def _split_import_parts(parts: list[str]) -> list[list[str]]:
    segments: list[list[str]] = []
    current: list[str] = []
    for part in parts:
        if part == ',':
            if current:
                segments.append(current)
                current = []
            continue
        current.append(part)
    if current:
        segments.append(current)
    return segments
def _plain_import_aliases(parts: list[str]) -> list[_ast.alias]:
    aliases: list[_ast.alias] = []
    for segment in _split_import_parts(parts):
        module_parts: list[str] = []
        for part in segment:
            if part == 'as':
                break
            module_parts.append(part)
        module = ''.join(module_parts)
        if _valid_absolute_module(module):
            aliases.append(_ast.alias(name=module))
    return aliases
def _from_import_aliases(parts: list[str]) -> list[_ast.alias]:
    aliases: list[_ast.alias] = []
    expect_name = True
    for part in parts:
        if part in ('(', ')'):
            continue
        if part == ',':
            expect_name = True
            continue
        if not expect_name:
            continue
        if _re.fullmatch(r'\w+|\*', part):
            aliases.append(_ast.alias(name=part))
        expect_name = False
    return aliases
def _text_import_node(
        statement: list[tokenize.TokenInfo],
) -> _ast.Import | _ast.ImportFrom | None:
    parts = [token.string for token in statement]
    if not parts:
        return None
    lineno = statement[0].start[0]
    if parts[0] == 'import':
        aliases = _plain_import_aliases(parts[1:])
        return _ast.Import(names=aliases, lineno=lineno) if aliases else None
    if parts[0] != 'from':
        return None
    try:
        import_at = parts.index('import', 1)
    except ValueError:
        return None
    dotted = ''.join(parts[1:import_at])
    if not dotted or not _re.fullmatch(r'[.\w]+', dotted):
        return None
    level = len(dotted) - len(dotted.lstrip('.'))
    module = dotted[level:] or None
    if module and not _valid_absolute_module(module):
        return None
    aliases = _from_import_aliases(parts[import_at + 1:])
    if not aliases:
        return None
    return _ast.ImportFrom(
        module=module, names=aliases, level=level, lineno=lineno)
def _text_string_refs(content: str, str_targets: set[str]) -> list[str]:
    if not str_targets:
        return []
    for token in _iter_text_tokens(content):
        if token is None or token.type != tokenize.STRING:
            continue
        try:
            value = _ast.literal_eval(token.string)
        except (SyntaxError, ValueError):
            continue
        if isinstance(value, str) and value in str_targets:
            return [f"字符串引用 {value}"]
    return []
def _text_module_refs(content: str, fp_rel: str, pkg_dotted: str,
                      base_name: str, pkg_prefix: str,
                      pkg_prefixes: Iterable[str] = ()) -> list[str]:
    scan = _build_ref_scan_context(
        fp_rel, pkg_dotted, base_name, pkg_prefix, pkg_prefixes)
    refs: list[str] = []
    for statement in _iter_text_import_tokens(content):
        node = _text_import_node(statement)
        if node is not None:
            refs.extend(_refs_of_ast_node(node, scan))
    refs.extend(_text_string_refs(content, set(scan.str_targets)))
    return refs
class _ImporterScanState(NamedTuple):
    module_specs: dict
    pkg_prefix: str
    base_names: set
    exclude: set
    target_abs_set: set
    results: dict
    pkg_prefixes: tuple[str, ...] = ()
def _pkg_prefix_for(search_dir: str) -> str:
    prefixes = _search_package_prefixes(search_dir) if search_dir else ()
    return prefixes[0] if prefixes else ""
def _scan_importers_once(module_specs: dict, search_dir: str,
                         exclude_paths=None) -> dict:
    results: dict[str, list[str]] = {dotted: [] for dotted in module_specs}
    exclude = {os.path.abspath(p) for p in (exclude_paths or ())}
    base_names = {spec[0] for spec in module_specs.values() if spec[0]}
    target_abs_set = {spec[1] for spec in module_specs.values()}
    pkg_prefixes = _search_package_prefixes(search_dir) if search_dir else ()
    state = _ImporterScanState(
        module_specs=module_specs,
        pkg_prefix=pkg_prefixes[0] if pkg_prefixes else "",
        base_names=base_names, exclude=exclude,
        target_abs_set=target_abs_set, results=results,
        pkg_prefixes=pkg_prefixes)
    for fp in _iter_py_files(search_dir):
        _ingest_importer_file(fp, search_dir, state)
    return results
def _ingest_importer_file(fp: str, search_dir: str,
                          state: _ImporterScanState) -> None:
    fp_abs = os.path.abspath(fp)
    if fp_abs in state.exclude or fp_abs in state.target_abs_set:
        return
    content = read_source(fp)
    if content is None:
        logger.warning("[G5] _scan_importers_once: 读取 %s 失败,跳过", fp)
        return
    has_base_name = any(b in content for b in state.base_names)
    has_relative_dynamic_import = (
        "__package__" in content and "import_module" in content)
    if not has_base_name and not has_relative_dynamic_import:
        return
    tree, fp_rel = _parse_importer(content, fp, search_dir)
    _assign_spec_refs(content, tree, fp_rel, fp, state)
def _parse_importer(content: str, fp: str,
                   search_dir: str) -> tuple[_ast.Module | None, str]:
    fp_rel = os.path.relpath(fp, search_dir).replace('\\', '/')
    try:
        tree = _ast.parse(content)
    except PARSE_DEGRADE_EXC as e:
        logger.debug("[G5] _scan_importers_once: %s 解析失败降级文本匹配: %s",
                     fp, e)
        return None, fp_rel
    return tree, fp_rel
def _assign_spec_refs(content: str, tree: _ast.Module | None, fp_rel: str,
                      fp: str, state: _ImporterScanState) -> None:
    for dotted, (base_name, _t) in state.module_specs.items():
        refs = (_ast_references_module(
                    tree, fp_rel, dotted, base_name, state.pkg_prefix,
                    state.pkg_prefixes)
                if tree is not None
                else _text_module_refs(
                    content, fp_rel, dotted, base_name, state.pkg_prefix,
                    state.pkg_prefixes))
        if refs:
            state.results[dotted].append(fp)
def _relative_attr_importers(init_abs: str, search_dir: str,
                             pkg_dotted: str,
                             symbols: frozenset[str]) -> list[str]:
    if not symbols:
        return []
    hits: list[str] = []
    for fp in _iter_py_files(os.path.dirname(init_abs)):
        if os.path.abspath(fp) == init_abs:
            continue
        tree = _load_ast(fp, "G5")
        if tree is None:
            continue
        for node in walk_nodes(tree):
            if (isinstance(node, _ast.ImportFrom) and not node.module
                    and node.level
                    and _relative_base_package(fp, search_dir, node.level)
                    == pkg_dotted
                    and any(a.name == '*' or a.name in symbols
                            for a in node.names)):
                hits.append(fp)
                break
    return hits
def _find_importers(pkg_path: str, search_dir: str) -> list[str]:
    raw_pkg_path = pkg_path.replace('\\', '/')
    target_abs = os.path.abspath(os.path.join(search_dir, raw_pkg_path))
    pkg_dotted, base_name = _rel_to_module(raw_pkg_path)
    is_init = _is_init_file(target_abs)
    is_root_init = is_init and not pkg_dotted
    if is_root_init:
        base_name = os.path.basename(os.path.abspath(search_dir))
        if not _search_package_prefixes(search_dir):
            pkg_dotted = base_name
    if not pkg_dotted and not is_root_init:
        return []
    found = _scan_importers_once(
        {pkg_dotted: (base_name, target_abs)}, search_dir)[pkg_dotted]
    if not is_init:
        return found
    pkg_prefix = _pkg_prefix_for(search_dir)
    if is_root_init:
        relative_pkg = pkg_prefix or base_name
    else:
        relative_pkg = (f"{pkg_prefix}.{pkg_dotted}"
                        if pkg_prefix else pkg_dotted)
    extra = _relative_attr_importers(
        target_abs, search_dir, relative_pkg,
        frozenset(_extract_public_symbols(target_abs)))
    return list(dict.fromkeys([*found, *extra]))
def _dir_delete_specs(py_files: list[str], search_dir: str,
                      target: str) -> tuple[dict[str, tuple[str, str]], str]:
    specs: dict[str, tuple[str, str]] = {}
    for fpath in py_files:
        dotted, base = _rel_module_of(fpath, search_dir)
        if dotted:
            specs[dotted] = (base, os.path.abspath(fpath))
    dir_rel = os.path.relpath(target, search_dir).replace('\\', '/')
    dir_parts = _module_path_parts(dir_rel)
    dir_dotted = '.'.join(dir_parts)
    if dir_parts:
        specs.setdefault(dir_dotted,
                         (dir_parts[-1], os.path.abspath(target)))
    return specs, dir_dotted
def _dir_import_issue_messages(py_files: list[str], scan: dict,
                               search_dir: str, dir_dotted: str = "") -> list[str]:
    issues: list[str] = []
    for fpath in py_files:
        dotted, _base = _rel_module_of(fpath, search_dir)
        if dir_dotted and dotted == dir_dotted and _is_init_file(fpath):
            continue
        importers = scan.get(dotted, []) if dotted else []
        if importers:
            issues.append(f"{os.path.basename(fpath)} 被 {len(importers)} 个文件导入")
    return issues
def _collect_dir_delete_issues(target: str, search_dir: str) -> list[str]:
    py_files = list(_iter_py_files(target))
    inner_abs = {os.path.abspath(fpath) for fpath in py_files}
    specs, dir_dotted = _dir_delete_specs(py_files, search_dir, target)
    scan = _scan_importers_once(specs, search_dir, exclude_paths=inner_abs)
    issues = _dir_import_issue_messages(
        py_files, scan, search_dir, dir_dotted)
    if dir_dotted and scan.get(dir_dotted):
        dir_importers = scan[dir_dotted]
        issues.append(f"包目录被 {len(dir_importers)} 个文件导入: "
                      f"{', '.join(os.path.basename(i) for i in dir_importers[:5])}")
    return issues
def _file_delete_issues(target: str, search_dir: str) -> list[str]:
    if not _is_py_source(target):
        return []
    issues: list[str] = []
    pkg_path = os.path.relpath(target, search_dir).replace('\\', '/')
    importers = _find_importers(pkg_path, search_dir)
    if importers:
        issues.append(f"文件被 {len(importers)} 个文件导入: "
                      f"{', '.join(os.path.basename(i) for i in importers[:5])}")
    issues.extend(_find_exporters(target))
    return issues
def _delete_target_issues(target: str, search_dir: str) -> list[str]:
    if os.name == 'nt':
        target = os.path.realpath(target)
        search_dir = os.path.realpath(search_dir)
    if os.path.isfile(target):
        return _file_delete_issues(target, search_dir)
    if os.path.isdir(target):
        return _collect_dir_delete_issues(target, search_dir)
    return []
def _guard_search_dir(ctx: OperationContext, target: str) -> str:
    meta_search_dir = ctx.metadata.get("search_dir")
    if (isinstance(meta_search_dir, str) and meta_search_dir.strip()
            and os.path.isdir(meta_search_dir)
            and is_under_root(target, meta_search_dir)):
        return os.path.abspath(meta_search_dir)
    start_dir = os.path.dirname(os.path.abspath(target))
    project_root = _find_project_root(start_dir)
    if project_root:
        return project_root
    pkg_root = _outermost_package_root(start_dir)
    if pkg_root:
        return pkg_root
    fallback = resolve_search_root(start_dir)
    if _is_scan_container_root(fallback):
        logger.debug("[Guard] 回落根是容器目录,改用目标目录: %s", fallback)
        return start_dir
    return fallback
def _passed(guard_name: str, message: str) -> GuardResult:
    return GuardResult(guard_name=guard_name, passed=True, message=message)
def guard_delete(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in (OperationType.DELETE_FILE,
                                 OperationType.DELETE_DIR,
                                 OperationType.CLEANUP):
        return _passed("G5", "非删除操作,跳过依赖分析")
    if ctx.dry_run:
        return _passed("G5", "dry_run 模式,跳过依赖分析")
    target = ctx.target_path
    if not os.path.exists(target):
        return _passed("G5", "目标不存在,无需分析")
    if os.path.isfile(target) and not _is_py_source(target):
        return _passed("G5", "非 Python 文件,跳过导入依赖分析")
    issues = _delete_target_issues(target, _guard_search_dir(ctx, target))
    if issues:
        return GuardResult(
            guard_name="G5", passed=False, level=GuardLevel.BLOCK,
            message=f"删除操作影响 {len(issues)} 处依赖", details=issues[:15],
            fix_suggestion="先更新所有导入方,或确认这些依赖可以安全断开.")
    return _passed("G5", "依赖分析通过,无外部引用")
def _extract_public_symbols(filepath: str, *,
                            include_imports: bool = True) -> set[str]:
    tree = _load_ast(filepath, "G20")
    if tree is None:
        return set()
    return _extract_public_symbols_from_ast(tree,
                                            include_imports=include_imports)
def _scan_symbol_reference_surface(target_path: str, search_dir: str,
                                   symbols: set[str]) -> tuple[int, list[str]]:
    if not symbols:
        return 0, []
    total_refs = 0
    affected_files: set[str] = set()
    ordered = sorted(symbols, key=lambda sym: (-len(sym), sym))
    pattern = _re.compile(
        r'\b(?:' + '|'.join(_re.escape(sym) for sym in ordered) + r')\b')
    target_key = _path_identity(target_path)
    for fp in _iter_py_files(search_dir):
        refs_in_file = _count_symbol_refs_in_file(
            fp, target_key, pattern)
        if refs_in_file:
            total_refs += refs_in_file
            affected_files.add(os.path.abspath(fp))
    return total_refs, sorted(affected_files)
def _count_symbol_refs_in_file(fp: str, target_key: str,
                                pattern: _re.Pattern) -> int:
    if _path_identity(fp) == target_key:
        return 0
    content = read_source(fp)
    if content is None:
        logger.warning("[G20] _estimate_blast_radius: 读取 %s 失败,跳过", fp)
        return 0
    return sum(1 for _match in pattern.finditer(content))
class _BlastRadius(TypedDict):
    target: str
    symbols: list[str]
    total_references: int
    affected_files: list[str]
    severity: str
_SEVERITY_BANDS = ((10, "critical"), (5, "high"), (2, "medium"))
def _severity_for(count: int) -> str:
    for threshold, level in _SEVERITY_BANDS:
        if count >= threshold:
            return level
    return "low"
def _estimate_blast_radius(target_path: str, search_dir: str) -> _BlastRadius:
    radius: _BlastRadius = {
        "target": target_path,
        "symbols": [],
        "total_references": 0,
        "affected_files": [],
        "severity": "low",
    }
    if not os.path.isfile(target_path):
        return radius
    symbols = _extract_public_symbols(target_path, include_imports=False)
    radius["symbols"] = sorted(symbols)
    if not symbols:
        return radius
    total_refs, affected_files = _scan_symbol_reference_surface(
        target_path, search_dir, symbols)
    radius["total_references"] = total_refs
    radius["affected_files"] = affected_files
    radius["severity"] = _severity_for(len(affected_files))
    return radius
def _path_identity(path: str) -> str:
    try:
        return os.path.normcase(os.path.realpath(os.path.abspath(path)))
    except (OSError, ValueError):
        return os.path.normcase(os.path.abspath(path))
def _declared_scope_paths(declared_files, base_dir: str) -> set[str]:
    base = os.path.abspath(base_dir or os.getcwd())
    scope: set[str] = set()
    for declared in normalize_files_list(declared_files):
        if not isinstance(declared, str) or not declared:
            continue
        try:
            scope.add(
                os.path.abspath(declared) if os.path.isabs(declared)
                else os.path.abspath(os.path.join(base, declared)))
        except (OSError, ValueError) as exc:
            logger.warning(
                "[G20] affected_files 路径非法,按未声明处理: %r (%s)",
                declared, exc)
    return scope
def _blast_radius_issues(radius: _BlastRadius,
                         declared_files, base_dir: str) -> list[str]:
    declared = {_path_identity(path)
                for path in _declared_scope_paths(declared_files, base_dir)}
    undeclared = [path for path in radius["affected_files"]
                  if _path_identity(path) not in declared]
    issues: list[str] = []
    if undeclared:
        issues.append(
            f"影响范围超出预期: {len(undeclared)} 个文件未在 affected_files 中声明: "
            f"{', '.join(os.path.basename(f) for f in sorted(undeclared)[:5])}"
        )
    if radius["severity"] in ("critical", "high"):
        issues.append(
            f"影响范围严重程度: {radius['severity']}."
            f"共 {radius['total_references']} 处引用,"
            f"影响 {len(radius['affected_files'])} 个文件."
        )
    return issues
def guard_blast_radius(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in (OperationType.DELETE_FILE,
                                 OperationType.MODIFY_CODE,
                                 OperationType.REFACTOR, OperationType.RENAME,
                                 OperationType.MOVE):
        return _passed("G20", "非代码修改操作,跳过影响范围预估")
    target = ctx.target_path
    if not os.path.isfile(target):
        return _passed("G20", "目标不是文件,跳过影响范围预估")
    search_dir = _guard_search_dir(ctx, target)
    radius = _estimate_blast_radius(target, search_dir)
    issues = _blast_radius_issues(radius, list(ctx.affected_files or ()),
                                  base_dir=search_dir)
    if issues:
        return GuardResult(
            guard_name="G20", passed=False, level=GuardLevel.WARN,
            message=f"影响范围预估发现 {len(issues)} 个问题", details=issues,
            fix_suggestion="在 affected_files 中声明所有受影响文件,"
                           "或确认未声明的文件可以安全忽略.")
    return _passed("G20", f"影响范围: {radius['severity']}, "
                          f"{radius['total_references']} 处引用, "
                          f"{len(radius['affected_files'])} 个文件")
_MODULE_FILE_SUFFIXES = tuple(dict.fromkeys((
    *machinery.SOURCE_SUFFIXES,
    *machinery.BYTECODE_SUFFIXES,
    *machinery.EXTENSION_SUFFIXES,
)))
def _outermost_package_root(start_dir: str) -> str:
    cur = os.path.abspath(start_dir)
    pkg_root = ""
    while os.path.isfile(os.path.join(cur, "__init__.py")):
        parent = os.path.dirname(cur)
        pkg_root = parent
        if parent == cur:
            break
        cur = parent
    return pkg_root
def _iter_guard_py_sources(ctx: OperationContext) -> Iterator[tuple[str, str]]:
    seen: set[str] = set()
    target = ctx.target_path
    pending = _pending_write_source(ctx, target)
    pending_key = os.path.realpath(pending[0]) if pending else ""
    emitted_pending = False
    candidates = list(ctx.affected_files or ())
    if _is_py_source(target) and os.path.isfile(target):
        candidates.insert(0, target)
    for fpath, source in _iter_affected_py_sources(candidates):
        key = os.path.realpath(fpath)
        if key in seen:
            continue
        seen.add(key)
        if pending_key and key == pending_key:
            source = pending[1]
            emitted_pending = True
        yield fpath, source
    if pending and not emitted_pending:
        yield pending[0], pending[1]
def _iter_affected_py_sources(affected_files) -> Iterator[tuple[str, str]]:
    for fpath in affected_files:
        if not _is_py_source(fpath) or not os.path.exists(fpath):
            continue
        source = read_source(fpath)
        if source is None:
            logger.warning("[G4] 读取影响文件失败,跳过: %s", fpath)
            continue
        yield fpath, source
_IMPORT_GUARD_OPS = (OperationType.ADD_IMPORT, OperationType.MODIFY_CODE,
                     OperationType.REFACTOR, OperationType.WRITE_FILE)
def _guard_outcome(guard_name: str, label: str, pass_message: str,
                   issues: list[str], fix_suggestion: str) -> GuardResult:
    if not issues:
        return GuardResult(guard_name=guard_name, passed=True,
                           message=pass_message)
    return GuardResult(
        guard_name=guard_name, passed=False, level=GuardLevel.WARN,
        message=f"{label}检查发现 {len(issues)} 个问题",
        details=issues[:10],
        fix_suggestion=fix_suggestion,
    )
def _pending_write_source(ctx: OperationContext,
                          target: str) -> tuple[str, str] | None:
    if not _is_py_source(target):
        return None
    metadata = ctx.metadata if isinstance(ctx.metadata, dict) else {}
    if "code_to_write" not in metadata:
        return None
    raw_code = metadata["code_to_write"]
    code = code_to_write_str(ctx)
    if code:
        return target, code
    if isinstance(raw_code, str):
        return target, code
    if isinstance(raw_code, (bytes, bytearray)):
        try:
            bytes(raw_code).decode("utf-8")
        except UnicodeDecodeError:
            return None
        return target, code
    if (isinstance(raw_code, (list, tuple))
            and all(isinstance(line, str) for line in raw_code)):
        return target, code
    return None
def _importfrom_candidate_dirs_by_parts(mod: str, level: int, search_dir: str,
                                        fpath: str) -> list[str]:
    if level:
        file_dir = os.path.dirname(os.path.abspath(fpath))
        pkg_root = _outermost_package_root(file_dir)
        if not pkg_root:
            pkg_root = os.path.abspath(search_dir)
            if not is_under_root(file_dir, pkg_root):
                return []
        rel = os.path.relpath(file_dir, pkg_root).replace('\\', '/')
        top_pkg = (pkg_root if rel == '.'
                   else os.path.join(pkg_root, rel.split('/')[0]))
        base = file_dir
        for _ in range(level - 1):
            base = os.path.dirname(base)
            if not is_under_root(base, top_pkg):
                return []
        return [os.path.join(base, *mod.split('.'))] if mod else [base]
    if not mod:
        return []
    parts = mod.split('.')
    candidates = [os.path.join(search_dir, *parts)]
    root_name = os.path.basename(os.path.normpath(search_dir))
    if parts[0] == root_name:
        candidates.append(os.path.join(search_dir, *parts[1:]))
    prefixes = _search_package_prefixes(search_dir)
    for prefix in prefixes:
        prefix_parts = prefix.split('.')
        if parts[:len(prefix_parts)] == prefix_parts:
            candidates.append(os.path.join(
                search_dir, *parts[len(prefix_parts):]))
    if prefixes:
        full_parts = prefixes[0].split('.')
        for prefix_len in range(1, len(full_parts)):
            if parts[:prefix_len] != full_parts[:prefix_len]:
                continue
            base = search_dir
            for _ in range(len(full_parts) - prefix_len):
                base = os.path.dirname(base)
            candidates.append(os.path.join(base, *parts[prefix_len:]))
    return list(dict.fromkeys(candidates))
def _submodule_file_exists(pkg_dir: str, alias: str, overrides=None) -> bool:
    module_path = os.path.join(pkg_dir, alias)
    if os.path.isdir(module_path):
        return True
    if any(os.path.isfile(os.path.join(pkg_dir, alias + ext))
           for ext in _MODULE_FILE_SUFFIXES):
        return True
    if not overrides:
        return False
    pending_paths = {
        _path_identity(module_path + '.py'),
        _path_identity(os.path.join(module_path, '__init__.py')),
    }
    return any(_path_identity(path) in pending_paths
               for path in overrides if _is_py_source(path))
def _search_package_prefixes(search_dir: str) -> tuple[str, ...]:
    names: list[str] = []
    cur = os.path.abspath(search_dir)
    while os.path.isfile(os.path.join(cur, '__init__.py')):
        names.insert(0, os.path.basename(cur))
        parent = os.path.dirname(cur)
        if parent == cur:
            break
        cur = parent
    return tuple(sorted({'.'.join(names[idx:])
                         for idx in range(len(names))}, key=len, reverse=True))
_MATCH_STMT_TYPE = getattr(_ast, "Match", None)
_TRY_STMT_TYPES = tuple(t for t in (_ast.Try, getattr(_ast, "TryStar", None))
                        if t is not None)
def _iter_try_parts(node: _ast.AST):
    yield node.body
    yield node.orelse
    yield node.finalbody
    for handler in node.handlers:
        yield handler.body
def _iter_match_parts(node: _ast.AST):
    yield node.subject
    for case in node.cases:
        if case.guard is not None:
            yield case.guard
        yield case.body
def _iter_with_parts(node):
    for item in node.items:
        yield item.context_expr
    yield node.body
def _iter_loop_parts(node, head):
    yield head
    yield node.body
    yield node.orelse
def _iter_block_parts(node: _ast.AST):
    if isinstance(node, _TRY_STMT_TYPES):
        yield from _iter_try_parts(node)
        return
    if isinstance(node, _ast.If):
        yield node.test
        yield node.body
        yield node.orelse
        return
    if isinstance(node, (_ast.With, _ast.AsyncWith)):
        yield from _iter_with_parts(node)
        return
    if isinstance(node, (_ast.For, _ast.AsyncFor)):
        yield from _iter_loop_parts(node, node.iter)
        return
    if isinstance(node, _ast.While):
        yield from _iter_loop_parts(node, node.test)
        return
    if _MATCH_STMT_TYPE is not None and isinstance(node, _MATCH_STMT_TYPE):
        yield from _iter_match_parts(node)

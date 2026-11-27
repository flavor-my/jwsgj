from __future__ import annotations

import ast
import logging
import os
import time
import tokenize
from collections import Counter, defaultdict, deque
from dataclasses import dataclass, field
from pathlib import Path

from jwsgj.build_module_topology import (
    export_assignment_targets,
    export_table_pairs,
    normalize_module_name,
)
from jwsgj.diag_dependency_core import (
    FAN_CRITICAL_RATIO,
    resolve_layer_fan_thresholds,
    resolve_outlier_limit,
)
from jwsgj.diag_module_surface import (
    dynamic_module_binding_names,
    is_main_guard_if,
    iter_module_level_nodes_tc,
    iter_target_py_files,
    project_package_root,
    relative_import_base,
)
from jwsgj.diag_module_topology import (
    target_infra_modules,
    target_layer_map,
)
from jwsgj.diag_testing_source import (
    FileCache,
    build_import_graph_excluding_lazy,
    collect_scope_binding_names,
    entry_module_dotted,
    entry_nodes,
    entry_rel_path,
    entry_used_names,
    import_binding_names,
    import_node_dotted,
    is_transient_io_error,
    iter_module_binding_nodes,
    module_entry_indexes,
    nodes_where,
    skill_has_nested_sources,
    static_if_branch,
)
from jwsgj.diag_types_defs import (
    TestMethodResult,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    TEST_DIR_CANDIDATES_LOWER,
    detect_cycles,
    is_pruned_scan_dir,
)


class _ProjectFileCache(FileCache):
    _CACHE_FILENAME = '.filecache_project.pkl'
    def _load_paths(self):
        return [str(path) for path in
                iter_target_py_files(self.skill_dir, include_tests=False)
                if not _pruned_scan_path(path, self.skill_dir)]
__all__ = [
    'run_architecture_tests',
    'run_smoke_tests',
]
_log = logging.getLogger(__name__)
def _module_scope_binding_names(node) -> set[str]:
    names: set[str] = set()
    declared_outer: set[str] = set()
    collect_scope_binding_names(node, names, declared_outer)
    return names - declared_outer
def _iter_import_time_binding_nodes(tree):
    excluded: set[int] = set()
    static_loops: set[int] = set()
    for node, under_tc in iter_module_level_nodes_tc(
            tree, include_class_body=False):
        if under_tc:
            excluded.update(id(child) for child in walk_nodes(node))
        elif is_main_guard_if(node):
            for statement in node.body:
                excluded.update(id(child) for child in walk_nodes(statement))
        elif isinstance(node, ast.While):
            static = static_if_branch(node.test)
            if static is not None:
                static_loops.add(id(node))
                unreachable = node.orelse if static else node.body
                for statement in unreachable:
                    excluded.update(id(child) for child in walk_nodes(statement))
    for node in iter_module_binding_nodes(tree):
        if id(node) in excluded or id(node) in static_loops:
            continue
        yield node
def _collect_init_bindings(init_tree) -> tuple[set[str], set[str], set[str], bool]:
    all_names: set[str] = set()
    imported: set[str] = set()
    defined: set[str] = set()
    star_import_seen = False
    for node in _iter_import_time_binding_nodes(init_tree):
        defined.update(dynamic_module_binding_names(node))
        for table_name, names in export_table_pairs(node):
            if table_name == "__all__":
                all_names.update(names)
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            names, has_star = import_binding_names(node)
            star_import_seen = star_import_seen or has_star
            imported |= names
            continue
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            defined.add(node.name)
            continue
        names = _module_scope_binding_names(node)
        defined.update(names)
    return all_names, imported, defined, star_import_seen
_TOP_LEVEL_PACKAGE_SKIP = (GENERIC_SCAN_IGNORE_DIRS_LOWER
                           | TEST_DIR_CANDIDATES_LOWER)
def _pruned_scan_path(path, root) -> bool:
    try:
        rel = os.path.relpath(os.fspath(path), os.fspath(root))
    except (TypeError, ValueError, OSError):
        return False
    parts = Path(rel).parts
    return any(is_pruned_scan_dir(part, _TOP_LEVEL_PACKAGE_SKIP)
               for part in parts[:-1])
def _entry_pruned(entry) -> bool:
    parts = Path(str(getattr(entry, "rel_path", ""))).parts
    return any(is_pruned_scan_dir(part, _TOP_LEVEL_PACKAGE_SKIP)
               for part in parts[:-1])
def _gate_entries(cache) -> list:
    if cache is None:
        return []
    return [entry for entry in cache.valid_entries
            if not _entry_pruned(entry)]
def _gate_file_entries(cache) -> list:
    if cache is None:
        return []
    return [entry for entry in cache.entries if not _entry_pruned(entry)]
def _sole_top_level_package(skill_dir: str) -> str:
    try:
        entries = sorted(os.listdir(skill_dir))
    except OSError:  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
        return ""
    packages = [
        name for name in entries
        if not is_pruned_scan_dir(name, _TOP_LEVEL_PACKAGE_SKIP)
        and os.path.isfile(os.path.join(skill_dir, name, "__init__.py"))
    ]
    return packages[0] if len(packages) == 1 else ""
def _package_prefix(skill_dir: str) -> str:
    if not isinstance(skill_dir, str) or not os.path.isdir(skill_dir):
        return ""
    try:
        base = os.path.realpath(skill_dir)
        package_root = os.path.realpath(project_package_root(skill_dir))
        prefix = os.path.relpath(package_root, base)
    except (OSError, ValueError) as exc:
        _log.debug("_package_prefix: 包根解析降级: %s", exc)
        return ""
    if prefix in ("", os.curdir):
        if os.path.isfile(os.path.join(base, "__init__.py")):
            return ""
        prefix = _sole_top_level_package(skill_dir)
    if not prefix or prefix == os.curdir:
        return ""
    if os.pardir in prefix.replace("\\", "/").split("/"):
        return ""
    return prefix.replace(os.sep, "/")
def _facade_delegates_nested(init_entry) -> bool:
    tree = getattr(init_entry, "tree", None)
    if tree is None:
        return False
    return _init_is_pure_marker(tree) or not _init_public_api_face(tree)
def _subpackage_facade(cache, prefix: str):
    if not prefix:
        return None
    getter = getattr(cache, "get", None)
    if not callable(getter):
        return None
    return getter(os.path.join(*prefix.split("/"), "__init__.py"))
def _facade_entry(cache) -> tuple[object | None, str]:
    skill_dir = getattr(cache, "skill_dir", "") or ""
    prefix = _package_prefix(skill_dir)
    init_entry = getattr(cache, "init_entry", None)
    if init_entry is not None and not _facade_delegates_nested(init_entry):
        return init_entry, prefix
    nested = _subpackage_facade(cache, prefix)
    if nested is not None:
        return nested, prefix
    if init_entry is not None:
        return init_entry, prefix
    return None, ""
def _root_export_module_names(cache) -> set[str]:
    if cache is None:
        return set()
    _facade, prefix = _facade_entry(cache)
    base = tuple(part for part in prefix.split("/") if part)
    names: set[str] = set()
    for e in _gate_entries(cache):
        parts = Path(entry_rel_path(e)).parts
        if base:
            if parts[:len(base)] != base:
                continue
            parts = parts[len(base):]
        if not parts:
            continue
        name = parts[0] if len(parts) > 1 else normalize_module_name(parts[0])
        if name:
            names.add(name)
    return names
def _unreachable_all_exports(init_tree, cache) -> set[str]:
    if init_tree is None:
        return set()
    all_names, imported, defined, star_import_seen = _collect_init_bindings(
        init_tree)
    has_dynamic_getattr = any(
        _node_binds_module_getattr(node)
        for node in _iter_import_time_binding_nodes(init_tree))
    if star_import_seen or has_dynamic_getattr:
        return set()
    return all_names - (imported | defined) - _root_export_module_names(cache)
def _check_all_consistency(cache) -> list:
    violations = []
    init_entry, _prefix = _facade_entry(cache)
    if not (init_entry and getattr(init_entry, "tree", None)):
        return violations
    missing = _unreachable_all_exports(init_entry.tree, cache)
    if missing:
        violations.append({
            "type": "all_inconsistency", "severity": "medium",
            "missing": sorted(missing)[:10],
            "message": (f"__all__ 导出了 {len(missing)} 个无法从门面"
                        f"到达的名称"),
        })
    return violations
def _module_level_definition_names(entry) -> set[str]:
    names = {func['name'] for func in entry.functions if not func.get('scope')}
    names.update(cls['name'] for cls in entry.classes if not cls.get('scope'))
    return names
def _arch_module_keys(cache) -> dict[int, str]:
    stem_counts = Counter(
        entry.mod_stem for entry in _gate_entries(cache)
        if getattr(entry, "mod_stem", "") and entry.mod_stem != "__init__"
    )
    qualified = any(count > 1 for count in stem_counts.values())
    keys: dict[int, str] = {}
    for entry in _gate_entries(cache):
        stem = getattr(entry, "mod_stem", "")
        if not stem:
            continue
        key = stem
        if qualified and not getattr(entry, "is_init", False):
            key = entry_module_dotted(entry).removeprefix("src.") or stem
        keys[id(entry)] = key
    return keys
def _gate_business_entries(cache) -> list:
    return [entry for entry in _gate_entries(cache) if not entry.is_init]
def _add_root_package_qualified_edges(cache, entries, module_keys,
                                      graph) -> None:
    package_name = _root_package_alias(getattr(cache, "skill_dir", "") or "")
    if not package_name:
        return
    internal_keys = {
        module_keys.get(id(entry), entry.mod_stem) for entry in entries
    }
    for entry in entries:
        source = module_keys.get(id(entry), entry.mod_stem)
        for node in _iter_import_time_binding_nodes(entry.tree):
            if isinstance(node, ast.Import):
                raw_names = [alias.name for alias in node.names]
            elif isinstance(node, ast.ImportFrom) and not node.level:
                base = node.module or ""
                raw_names = [base] if base else []
                raw_names.extend(
                    f"{base}.{alias.name}" if base else alias.name
                    for alias in node.names)
            else:
                continue
            for raw_name in raw_names:
                _add_internal_import_edge(
                    graph, source, raw_name, internal_keys,
                    {package_name: ""})


def _root_package_alias(root: str) -> str:
    """技能根本身是包时的绝对导入前缀（即根目录名），否则为空串。"""
    if not root or not os.path.isfile(os.path.join(root, "__init__.py")):
        return ""
    return os.path.basename(os.path.abspath(root))


def _strip_root_package_alias(name: str, alias: str) -> str:
    """把 ``<alias>.pkg.mod`` 归一为相对技能根的 ``pkg.mod``。"""
    if alias and (name == alias or name.startswith(alias + ".")):
        return name[len(alias):].lstrip(".")
    return name


def _import_dotted_name(entry, node: ast.ImportFrom, root: str) -> str | None:
    """相对/绝对导入的点名（相对技能根）。

    ``import_node_dotted`` 按脚本目录语义计算相对层级：技能根本身是包
    （根目录带 ``__init__.py``）时，一级子包内的 ``..x`` 回到根包是合法形态，
    此时按 ``relative_import_base`` 的包边界兜底，避免真实依赖边丢失。
    """
    dotted = import_node_dotted(node, entry.rel_path)
    if (dotted is not None or not node.level or not root
            or not os.path.isfile(os.path.join(root, "__init__.py"))):
        return dotted
    base = relative_import_base(entry.path, node.level, root)
    if base is None:
        return None
    try:
        parts = list(Path(base).relative_to(Path(root)).parts)
    except ValueError:
        return None
    if node.module:
        parts.extend(node.module.split("."))
    return ".".join(parts)


def _import_time_dotted_names(entry, root: str) -> set[str]:
    """模块级（非延迟）导入语句触达的点名集合（相对技能根，含逐级前缀）。

    技能根本身是包时，绝对导入（``from <root>.pkg import x``）带有根包前缀，
    与 ``entry_module_dotted`` 的相对技能根口径不一致；统一剥掉根包前缀，
    经子包门面的绝对导入才能与 ``inits`` 对上并展开为对包内模块的依赖边。
    """
    names: set[str] = set()
    root_alias = _root_package_alias(root)
    for node in _iter_import_time_binding_nodes(entry.tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                parts = alias.name.split(".")
                names.update(
                    ".".join(parts[:index])
                    for index in range(1, len(parts) + 1))
        elif isinstance(node, ast.ImportFrom):
            base = _import_dotted_name(entry, node, root)
            if base is None:
                continue
            if node.module:
                names.add(base)
            names.update(
                f"{base}.{alias.name}" if base else alias.name
                for alias in node.names)
    return {
        _strip_root_package_alias(name, root_alias).removeprefix("src.")
        for name in names
    } - {""}


def _expand_package_import_edges(cache, entries, module_keys, graph) -> None:
    """把经包门面的导入（``from .pkg import x`` / ``import pkg``）展开为对包内模块的依赖边。

    导入一个子包会执行其 ``__init__.py``，后者再导入包内模块；只记模块文件间的
    直接边会漏掉这条真实依赖，经门面回指的循环依赖在导入图上不可见。
    """
    root = getattr(cache, "skill_dir", "") or ""
    inits = {
        entry_module_dotted(entry).removeprefix("src."): entry
        for entry in _gate_entries(cache)
        if getattr(entry, "is_init", False) and entry_module_dotted(entry)
    }
    if not inits:
        return
    dotted_keys = {
        entry_module_dotted(entry).removeprefix("src."):
        module_keys.get(id(entry), entry.mod_stem)
        for entry in entries if entry_module_dotted(entry)
    }
    reached: dict[str, set[str]] = {}

    def _package_targets(name: str) -> set[str]:
        # 闭包必须在本地 visited 上一次走完：递归时以「祖先链 seen」为守卫
        # 算出的只是部分闭包，若写入 reached 会被后续调用当作完整结果复用，
        # 使包环中后访问的包漏掉经另一侧包到达的模块（循环依赖随之漏报）。
        if name in reached:
            return reached[name]
        targets: set[str] = set()
        visited: set[str] = set()
        pending = [name]
        while pending:
            current = pending.pop()
            if current in visited:
                continue
            visited.add(current)
            init = inits.get(current)
            if init is None or getattr(init, "tree", None) is None:
                continue
            for imported in _import_time_dotted_names(init, root):
                if imported in inits:
                    pending.append(imported)
                elif imported in dotted_keys:
                    targets.add(dotted_keys[imported])
        reached[name] = targets
        return targets

    for entry in entries:
        if getattr(entry, "tree", None) is None:
            continue
        source = module_keys.get(id(entry), entry.mod_stem)
        for name in _import_time_dotted_names(entry, root):
            if name not in inits:
                continue
            for target in _package_targets(name):
                if target != source:
                    graph[source].add(target)


def _add_root_relative_import_edges(cache, entries, module_keys,
                                   graph) -> None:
    """补齐共享导入图跳过的根包 ``..`` 相对导入边。

    ``build_import_graph_excluding_lazy`` 对 ``import_node_dotted`` 返回 None 的
    相对导入直接跳过；技能根自身是包时，子包内回到根包的 ``..`` 是合法形态，
    这里按 ``_import_dotted_name`` 的包边界解析补边，避免真实依赖（含循环）丢失。
    """
    root = getattr(cache, "skill_dir", "") or ""
    if not root or not os.path.isfile(os.path.join(root, "__init__.py")):
        return
    internal_keys = {
        module_keys.get(id(entry), entry.mod_stem) for entry in entries
    }
    for entry in entries:
        if getattr(entry, "tree", None) is None:
            continue
        source = module_keys.get(id(entry), entry.mod_stem)
        for node in _iter_import_time_binding_nodes(entry.tree):
            if not (isinstance(node, ast.ImportFrom) and node.level
                    and import_node_dotted(node, entry.rel_path) is None):
                continue
            dotted = _import_dotted_name(entry, node, root)
            if dotted is None:
                continue
            if node.module:
                _add_internal_import_edge(
                    graph, source, dotted, internal_keys, {})
            for alias in node.names:
                raw_name = f"{dotted}.{alias.name}" if dotted else alias.name
                _add_internal_import_edge(
                    graph, source, raw_name, internal_keys, {})


def _gate_import_graph(cache) -> dict[str, set[str]]:
    entries = _gate_business_entries(cache)
    internal_mods = {
        entry.mod_stem for entry in entries
        if getattr(entry, "mod_stem", "")
    }
    graph = build_import_graph_excluding_lazy(entries, internal_mods)
    module_keys = _arch_module_keys(cache)
    qualified = any(
        module_keys.get(id(entry), entry.mod_stem) != entry.mod_stem
        for entry in entries)
    if qualified:
        _add_root_package_qualified_edges(
            cache, entries, module_keys, graph)
    _add_root_relative_import_edges(cache, entries, module_keys, graph)
    _expand_package_import_edges(cache, entries, module_keys, graph)
    return graph
def _build_arch_graph(
    cache: FileCache,
) -> tuple[dict[str, set[str]], dict[str, set[str]]]:
    import_graph = _gate_import_graph(cache)
    module_keys = _arch_module_keys(cache)
    module_functions: dict[str, set[str]] = defaultdict(set)
    for entry in _gate_business_entries(cache):
        module_functions[module_keys.get(id(entry), entry.mod_stem)].update(
            _module_level_definition_names(entry))
    return import_graph, module_functions
def _public_defined_names(entry) -> set[str]:
    return {name for name in _module_level_definition_names(entry)
            if not name.startswith('_')}
def _compute_dead_code_metrics(
    cache: FileCache
) -> tuple[set, float]:
    per_entry: list[tuple[str, set[str], set[str]]] = []
    external_used: set[str] = set()
    total_public = 0
    module_keys = _arch_module_keys(cache)
    for entry in _gate_entries(cache):
        raw_stem = getattr(entry, "mod_stem", "") or ""
        if _is_entry_module(raw_stem):
            continue
        stem = module_keys.get(id(entry), raw_stem)
        public_defined = _public_defined_names(entry)
        all_defined = _module_level_definition_names(entry)
        used_in_module = entry_used_names(entry)
        total_public += len(public_defined)
        per_entry.append((stem, public_defined,
                          public_defined & used_in_module))
        external_used |= {name for name in used_in_module
                          if name not in all_defined}
    unused_public = {
        f"{stem}.{name}" if stem else name
        for stem, public_defined, self_used in per_entry
        for name in public_defined
        if name not in self_used and name not in external_used
    }
    dead_code_pct = len(unused_public) / max(total_public, 1) * 100
    return unused_public, dead_code_pct
_ARCH_METHOD_NAME = "架构测试"
_ARCH_METHOD_ID = "architecture"
_SMOKE_METHOD_NAME = "冒烟测试"
_SMOKE_METHOD_ID = "smoke_test"
_MISSING_DIR_REASON = "目录不存在"
_NO_SOURCE_REASON = "无可用源码"
_ENTRY_MODULE_STEMS = frozenset({'__init__', '__main__'})
_INFRA_MODULES = frozenset({'utils'})
_INFRA_NAME_TOKENS = frozenset({
    'config', 'settings', 'constants', 'types', 'log', 'logging',
    'paths', 'runtime', 'guard', 'errors', 'exceptions', 'db',
})
def _module_leaf_name(name: str) -> str:
    return name.replace("\\", "/").rsplit("/", 1)[-1].rsplit(".", 1)[-1]
def _module_tokens(name: str) -> tuple[str, ...]:
    leaf = _module_leaf_name(name).lower().strip('_')
    return tuple(t for t in leaf.split('_') if t)
def _is_entry_module(name: str) -> bool:
    return _module_leaf_name(name) in _ENTRY_MODULE_STEMS
def _is_infra_module(name: str, infra_modules) -> bool:
    return (name in infra_modules
            or name.lstrip('_') in _INFRA_MODULES
            or bool(_INFRA_NAME_TOKENS.intersection(_module_tokens(name))))
_TRANSITIVE_DEP_LIMIT = 15
_UNSTABLE_RATIO_LIMIT = 0.7
_SRP_RESPONSIBILITY_LIMIT = 5
# 定义数绝对下限：小技能（模块总数少、每模块十几个定义）不因分布紧凑而失去判别力。
_GOD_MODULE_FUNCTION_FLOOR = 100
_CORE_NAME_TOKENS = frozenset({'core', 'engine', 'main', 'pipeline'})
_UTILS_NAME_TOKENS = frozenset({'util', 'utils', 'helper', 'helpers', 'common'})
_ABSTRACT_NAME_TOKENS = frozenset({'abstract', 'base', 'interface', 'abc'})
def _collect_core_modules(all_modules: set) -> set:
    return {m for m in all_modules
            if not _is_entry_module(m)
            and _CORE_NAME_TOKENS.intersection(_module_tokens(m))}
def _collect_utils_modules(all_modules: set, infra_modules) -> set:
    utils_modules = set()
    for m in all_modules:
        if _is_entry_module(m):
            continue
        tokens = _module_tokens(m)
        if (_is_infra_module(m, infra_modules)
                or _CORE_NAME_TOKENS.intersection(tokens)):
            continue
        if _UTILS_NAME_TOKENS.intersection(tokens):
            utils_modules.add(m)
    return utils_modules
def _check_layer_violations(import_graph: dict, utils_modules: set,
                           violations: list, infra_modules) -> None:
    for utils_mod in utils_modules:
        for dep in import_graph.get(utils_mod, set()):
            if _is_entry_module(dep) or _is_infra_module(dep, infra_modules):
                continue
            if dep not in utils_modules:
                violations.append({
                    "type": "layer_violation", "severity": "medium",
                    "from": utils_mod, "to": dep,
                    "message": f"工具模块 {utils_mod} 不应依赖业务模块 {dep}",
                })
def _check_dep_direction(import_graph: dict, core_modules: set,
                         utils_modules: set, violations: list) -> None:
    for core_mod in core_modules:
        for dep in import_graph.get(core_mod, set()):
            if _is_entry_module(dep):
                continue
            if dep in utils_modules:
                violations.append({
                    "type": "dependency_direction", "severity": "medium",
                    "from": core_mod, "to": dep,
                    "message": f"核心模块 {core_mod} 不应依赖工具模块 {dep}（方向反转）",
                })
def _check_dep_inversion(import_graph: dict, core_modules: set,
                         violations: list) -> None:
    for mod in core_modules:
        for dep in import_graph.get(mod, set()):
            if (not _is_entry_module(dep) and dep not in core_modules
                    and not dep.startswith('_')
                    and {'impl', 'concrete'}.intersection(_module_tokens(dep))):
                violations.append({
                    "type": "dependency_inversion", "severity": "low",
                    "from": mod, "to": dep,
                    "message": f"模块 {mod} 依赖具体实现 {dep}，考虑通过抽象接口",
                })
def _check_declared_layer_direction(import_graph: dict,
                                    layer_map: dict[str, int]) -> list:
    violations = []
    for source, targets in import_graph.items():
        source_layer = layer_map.get(source)
        if source_layer is None:
            continue
        for target in targets:
            target_layer = layer_map.get(target)
            if target_layer is None or source_layer >= target_layer:
                continue
            violations.append({
                "type": "layer_violation", "severity": "medium",
                "from": source, "to": target,
                "source_layer": source_layer, "target_layer": target_layer,
                "message": (f"分层违规: {source}(L{source_layer}) 不应依赖 "
                            f"{target}(L{target_layer})"),
            })
    return violations
def _check_layer_direction_solid(import_graph: dict, all_modules: set, *,
                                 infra_modules,
                                 layer_map: dict[str, int] | None = None) -> list:
    if layer_map:
        return _check_declared_layer_direction(import_graph, layer_map)
    violations = []
    utils_modules = _collect_utils_modules(all_modules, infra_modules)
    core_modules = _collect_core_modules(all_modules)
    _check_layer_violations(
        import_graph, utils_modules, violations, infra_modules)
    _check_dep_direction(import_graph, core_modules, utils_modules, violations)
    _check_dep_inversion(import_graph, core_modules, violations)
    return violations
def _check_transitive_coupling(import_graph: dict, all_modules: set,
                               violations: list) -> dict:
    transitive_deps = {}
    for mod in all_modules:
        if _is_entry_module(mod):
            continue
        visited = set()
        queue = deque([mod])
        while queue:
            current = queue.popleft()
            for dep in import_graph.get(current, set()):
                if dep == mod or _is_entry_module(dep):
                    continue
                if dep not in visited:
                    visited.add(dep)
                    queue.append(dep)
        visited.discard(mod)
        transitive_deps[mod] = visited
    for mod, deps in transitive_deps.items():
        if len(deps) > _TRANSITIVE_DEP_LIMIT:
            violations.append({
                "type": "transitive_coupling", "severity": "low",
                "module": mod, "transitive_deps": len(deps),
                "message": (f"模块 {mod} 传递依赖 {len(deps)} 个模块"
                            f"（建议 ≤ {_TRANSITIVE_DEP_LIMIT}）"),
            })
    return transitive_deps
def _in_degrees(import_graph: dict) -> Counter:
    return Counter(dep for deps in import_graph.values() for dep in deps)
def _check_module_instability(import_graph: dict, all_modules: set,
                              violations: list, in_degrees: Counter) -> dict:
    module_instability = {}
    raw_instability: dict[str, float] = {}
    for mod in all_modules:
        if _is_entry_module(mod):
            continue
        ca = in_degrees.get(mod, 0)
        ce = len(import_graph.get(mod, set()))
        total_coupling = ca + ce
        value = ce / total_coupling if total_coupling > 0 else 0.0
        raw_instability[mod] = value
        module_instability[mod] = round(value, 2)
    for mod, instability in module_instability.items():
        # 叶子模块 Ca=0 时 I 恒等于 1.0，这是定义式而非风险信号：
        # 只有同时存在入度与出度，"高出度低入度"才是可改进的耦合方向。
        if in_degrees.get(mod, 0) <= 0:
            continue
        if raw_instability[mod] > _UNSTABLE_RATIO_LIMIT:
            violations.append({
                "type": "unstable_dependency", "severity": "low",
                "module": mod, "instability": instability,
                "message": (f"模块 {mod} 不稳定度 {instability:.0%}"
                            f"（I = Ce/(Ca+Ce)，高出度低入度）"),
            })
    return module_instability
_NAMING_CLUSTER_SIZE_LIMIT = 5
_NAMING_CLUSTER_SMALL_PROJECT = 30
def _is_naming_cluster(mods: set, total_modules: int, has_cycles: bool) -> bool:
    if len(mods) <= _NAMING_CLUSTER_SIZE_LIMIT:
        return False
    return total_modules > _NAMING_CLUSTER_SMALL_PROJECT or has_cycles
def _check_naming_clusters(all_modules: set, violations: list,
                           has_cycles: bool) -> dict:
    naming_prefixes = defaultdict(set)
    for mod in all_modules:
        if _is_entry_module(mod):
            continue
        _prefix = mod.split('_')[0]
        if not _prefix:
            continue
        naming_prefixes[_prefix].add(mod)
    total_modules = len(all_modules)
    for prefix, mods in naming_prefixes.items():
        if _is_naming_cluster(mods, total_modules, has_cycles):
            violations.append({
                "type": "naming_cluster", "severity": "low",
                "prefix": prefix, "count": len(mods),
                "message": f"前缀 '{prefix}' 下有 {len(mods)} 个模块，可能需要子包组织",
            })
    return naming_prefixes
_FAT_INTERFACE_EXPORT_LIMIT = 30
def _is_fat_interface(entry) -> bool:
    return (bool(entry.has_all) and not getattr(entry, "is_init", False)
            and not _is_entry_module(getattr(entry, "mod_stem", ""))
            and len(entry.all_names) > _FAT_INTERFACE_EXPORT_LIMIT)
def _check_fat_interfaces(cache, violations: list) -> None:
    module_keys = _arch_module_keys(cache)
    for entry in _gate_entries(cache):
        if _is_fat_interface(entry):
            violations.append({
                "type": "fat_interface", "severity": "low",
                "module": module_keys.get(id(entry), entry.mod_stem),
                "exports": len(entry.all_names),
                "message": (f"模块 {entry.mod_stem} 导出 {len(entry.all_names)} 个名称"
                            f"（阈值 {_FAT_INTERFACE_EXPORT_LIMIT}），违反接口隔离"),
            })
_SRP_GENERIC_PREFIXES = frozenset(
    {'get', 'set', 'is', 'has', 'run', 'do', 'check', 'test'})
def _responsibility_token(func_name: str) -> str | None:
    parts = func_name.split('_')
    if not parts[0]:
        return None
    if parts[0] not in _SRP_GENERIC_PREFIXES:
        token = parts[0] if len(parts) > 1 else parts[0][:4]
    elif len(parts) > 1:
        token = parts[1][:4]
    else:
        return None
    return token or None
def _check_srp_violations(cache, violations: list) -> dict:
    """计算各模块的「职责词表」，仅作度量，不产生 finding。

    函数名的动词前缀种类数只是「对外 API 面宽度」的代理，与「变更原因
    多样性」没有稳定对应关系：共享工具库（ast 节点处理、类型归一化）
    与 COM 桥接层天然聚齐十几个动词，却都各自服务单一领域。实测该判据
    在本项目 307 个模块上命中 215 个（70%），任何阈值都无法压到可操作
    水平，因此不再上报违规——真正的 SRP 信号由 god_module（定义数离群）、
    low_cohesion（LCOM4）、excessive_coupling（扇出）与
    transitive_coupling（传递依赖）覆盖，这四条都有可操作的判定阈值。
    """
    module_responsibilities = defaultdict(set)
    module_keys = _arch_module_keys(cache)
    for entry in _gate_entries(cache):
        if _is_entry_module(entry.mod_stem):
            continue
        # 私有辅助模块（_shared/_utils 等）承担多种职责是刻意为之：
        # 它们的定位就是汇聚跨模块公用实现，SRP 在此反向约束会误伤。
        if _module_leaf_name(entry.mod_stem).startswith('_'):
            continue
        module_key = module_keys.get(id(entry), entry.mod_stem)
        for func in entry.functions:
            if func.get('scope'):
                continue
            token = _responsibility_token(func['name'])
            if token is not None:
                module_responsibilities[module_key].add(token)
    return module_responsibilities

def _check_advanced_metrics(import_graph: dict, all_modules: set, cache,
                            violations: list, has_cycles: bool,
                            in_degrees: Counter):
    transitive_deps = _check_transitive_coupling(import_graph, all_modules, violations)
    module_instability = _check_module_instability(
        import_graph, all_modules, violations, in_degrees)
    naming_prefixes = _check_naming_clusters(all_modules, violations, has_cycles)
    _check_fat_interfaces(cache, violations)
    module_responsibilities = _check_srp_violations(cache, violations)
    return (transitive_deps, module_instability, naming_prefixes,
            module_responsibilities)
def _check_excessive_coupling(import_graph: dict, violations: list,
                              layer_map: dict | None = None) -> None:
    degrees = {mod: len(deps) for mod, deps in import_graph.items()
               if not _is_entry_module(mod)}
    # 扇出阈值按层解析：编排层天然需要聚合大量下层模块，与叶子层用同一常量
    # 会把正常的分层设计判成耦合过宽。
    thresholds = resolve_layer_fan_thresholds(degrees, layer_map or {}, kind="out")
    fallback = max(thresholds.values(), default=0.0)
    for mod, degree in degrees.items():
        threshold = thresholds.get((layer_map or {}).get(mod, -1), fallback)
        if degree <= threshold:
            continue
        violations.append({
            "type": "excessive_coupling",
            "severity": ("high" if degree >= threshold * FAN_CRITICAL_RATIO
                         else "medium"),
            "module": mod, "fan_out": degree,
            "threshold": round(threshold, 1),
            "message": (f"模块 {mod} 扇出 {degree} "
                        f"(阈值 {threshold:.1f})，职责可能过于宽泛"),
        })
def _check_god_modules(module_functions: dict, violations: list,
                       infra_modules: tuple = ()) -> None:
    counts = {mod: len(funcs) for mod, funcs in module_functions.items()
              if not _is_entry_module(mod)}
    # 定义数阈值按项目自身分布派生：基础设施/共享层模块的单一职责本身就是
    # 汇聚全库公用定义，不参与离群判定。
    limit = resolve_outlier_limit(
        counts.values(), floor=float(_GOD_MODULE_FUNCTION_FLOOR))
    for mod, count in counts.items():
        if mod in infra_modules:
            continue
        if count <= limit:
            continue
        violations.append({
            "type": "god_module", "severity": "medium",
            "module": mod, "function_count": count,
            "message": (f"模块 {mod} 包含 {count} 个定义"
                        f" (阈值 {limit:.0f})，违反单一职责"),
        })
def _assemble_all_modules(import_graph: dict, cache) -> set:
    all_modules = set(import_graph.keys())
    for deps in import_graph.values():
        all_modules.update(deps)
    module_keys = _arch_module_keys(cache)
    for entry in _gate_entries(cache):
        stem = module_keys.get(id(entry), getattr(entry, "mod_stem", ""))
        if stem and not getattr(entry, "is_init", False):
            all_modules.add(stem)
    return all_modules
def _cli_entry_module_keys(cache) -> set[str]:
    """有 ``if __name__ == "__main__":`` 守卫的模块 key 集合。

    这类模块是**进程入口**（``python scripts/xxx.py``），由 shell 或技能
    文档直接调用，不参与 import 图。把它们当「孤立模块」会误伤所有双模式
    CLI 技能——每个脚本一个入口正是它们的标准布局，而不是没人用的死模块。
    """
    keys: set[str] = set()
    module_keys = _arch_module_keys(cache)
    for entry in _gate_entries(cache):
        tree = getattr(entry, "tree", None)
        if tree is None:
            continue
        if any(is_main_guard_if(node) for node in getattr(tree, "body", ())):
            keys.add(module_keys.get(id(entry), entry.mod_stem))
    return keys


def _deferred_import_module_keys(cache) -> set[str]:
    """被**任意位置**（含函数体内）import 到的模块 key 集合。

    import 图只记模块级语句：双模式 CLI 技能把 ``from docx_lint import ...``
    写在命令处理函数里（顶层依赖缺失时只影响该子命令，不拖垮整包），于是
    这些模块在图上入度为 0，被判成「孤儿」。但「有人 import 它」本身就是
    消费证据——孤儿判据是「无人引用」，不是「无模块级引用」。
    """
    keys: set[str] = set()
    entries = _gate_entries(cache)
    module_keys = _arch_module_keys(cache)
    by_dotted = {
        dotted: module_keys.get(id(entry), entry.mod_stem)
        for entry in entries
        if getattr(entry, "mod_stem", "")
        and (dotted := entry_module_dotted(entry).removeprefix("src."))
    }
    root = getattr(cache, "skill_dir", "") or ""
    package_alias = _root_package_alias(root)
    for entry in entries:
        tree = getattr(entry, "tree", None)
        if tree is None:
            continue
        for node in walk_nodes(tree):
            if isinstance(node, ast.ImportFrom):
                base = _import_dotted_name(entry, node, root)
                if base is None:
                    continue
                names = [base] if node.module else []
                names.extend(
                    f"{base}.{alias.name}" if base else alias.name
                    for alias in node.names)
            elif isinstance(node, ast.Import):
                names = [alias.name for alias in node.names]
            else:
                continue
            for name in names:
                candidates = {name.removeprefix("src.").strip(".")}
                if package_alias and name.startswith(package_alias + "."):
                    candidates.add(name[len(package_alias) + 1:])
                for candidate in candidates:
                    key = by_dotted.get(candidate)
                    if key is not None:
                        keys.add(key)
    return keys


def _check_orphan_modules(import_graph: dict, all_modules: set,
                          violations: list, in_degrees: Counter,
                          cli_entry_modules: set | None = None,
                          deferred_modules: set | None = None) -> None:
    _cli = cli_entry_modules or set()
    _deferred = deferred_modules or set()
    for mod in all_modules:
        if (not in_degrees.get(mod) and not import_graph.get(mod)
                and not _is_entry_module(mod) and mod not in _cli
                and mod not in _deferred):
            violations.append({
                "type": "orphan_module", "severity": "low",
                "module": mod,
                "message": f"模块 {mod} 无任何依赖关系（孤立模块）",
            })
def _scan_basic_structure_violations(import_graph: dict,
                                      module_functions: dict,
                                      cache, violations: list,
                                      in_degrees: Counter,
                                      layer_map: dict | None = None,
                                      infra_modules: tuple = ()) -> set:
    _check_excessive_coupling(import_graph, violations, layer_map=layer_map)
    _check_god_modules(module_functions, violations, infra_modules=infra_modules)
    all_modules = _assemble_all_modules(import_graph, cache)
    _check_orphan_modules(import_graph, all_modules, violations, in_degrees,
                          _cli_entry_module_keys(cache),
                          _deferred_import_module_keys(cache))
    return all_modules
_OCP_NESTED_SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef)
def _count_isinstance_dispatch(func_node) -> int:
    count = 0
    stack = list(ast.iter_child_nodes(func_node))
    while stack:
        child = stack.pop()
        if isinstance(child, _OCP_NESTED_SCOPE_TYPES):
            continue
        if (isinstance(child, ast.If)
                and isinstance(child.test, ast.Call)
                and isinstance(child.test.func, ast.Name)
                and child.test.func.id == 'isinstance'):
            count += 1
        stack.extend(ast.iter_child_nodes(child))
    return count
@dataclass
class _ArchIntermediate:
    all_modules: set
    import_graph: dict
    cycles: list
    abstract_modules: set
    concrete_modules: set
    abstraction_ratio: float
    transitive_deps: dict
    module_instability: dict
    naming_prefixes: dict
    module_responsibilities: dict
def _count_ocp_dispatch(cache, violations: list) -> None:
    for entry in _gate_entries(cache):
        if _is_entry_module(getattr(entry, "mod_stem", "")):
            continue
        for node in entry_nodes(entry):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                type_dispatch_count = _count_isinstance_dispatch(node)
                if type_dispatch_count >= 3:
                    violations.append({
                        "type": "ocp_violation", "severity": "low",
                        "file": entry.rel_path, "function": node.name,
                        "dispatch_count": type_dispatch_count,
                        "message": f"函数 {node.name} 有 {type_dispatch_count} 个 isinstance 分支，可能违反开闭原则（考虑多态）",
                    })
def _coupling_metrics(arch: _ArchIntermediate) -> dict:
    instability_values = list(arch.module_instability.values())
    return {
        "total_modules": len(arch.all_modules),
        "total_edges": sum(len(deps) for deps in arch.import_graph.values()),
        "cycles": len(arch.cycles),
        "max_transitive_deps": max(
            (len(d) for d in arch.transitive_deps.values()), default=0),
        "avg_instability": round(
            sum(instability_values) / max(len(instability_values), 1), 2),
    }
def _surface_metrics(cache, violations: list, arch: _ArchIntermediate,
                     unused_public: set, dead_code_pct: float) -> dict:
    responsibility_sizes = [len(r) for r in arch.module_responsibilities.values()]
    total_modules = len(arch.all_modules)
    has_cycles = bool(arch.cycles)
    violation_types = Counter(v["type"] for v in violations)
    return {
        "violations": len(violations),
        "violation_types": dict(violation_types),
        "abstract_modules": len(arch.abstract_modules),
        "concrete_modules": len(arch.concrete_modules),
        "abstraction_ratio": round(arch.abstraction_ratio, 2),
        "naming_clusters": sum(
            1 for mods in arch.naming_prefixes.values()
            if _is_naming_cluster(mods, total_modules, has_cycles)),
        "fat_interfaces": sum(1 for e in _gate_entries(cache)
                               if _is_fat_interface(e)),
        "srp_violations": violation_types["srp_violation"],
        "ocp_violations": violation_types["ocp_violation"],
        "dead_code_pct": round(dead_code_pct, 1),
        "unused_public_count": len(unused_public),
        "avg_responsibilities": round(
            sum(responsibility_sizes) / max(len(responsibility_sizes), 1), 1),
    }
def _finalize_architecture_results(result, cache, violations, arch, start):
    _count_ocp_dispatch(cache, violations)
    unused_public, dead_code_pct = _compute_dead_code_metrics(cache)
    result.metrics = {
        **_coupling_metrics(arch),
        **_surface_metrics(cache, violations, arch, unused_public, dead_code_pct),
    }
    result.findings = violations
    critical = sum(1 for v in violations if v.get("severity") == "high")
    if critical == 0 and len(violations) <= 3:
        result.status = "pass"
        result.score = 100 if not violations else 80
        result.summary = (f"架构: {len(arch.all_modules)} 模块, {len(violations)} 违规, "
                          f"抽象率 {arch.abstraction_ratio:.0%}")
    elif critical <= 1:
        result.status = "warn"
        result.score = 60
        result.summary = f"架构: {critical} 严重违规 ({len(violations)} 总计)"
    else:
        result.status = "fail"
        result.score = 25
        result.summary = f"架构: {critical} 严重违规需修复"
    result.finish(start)
    _log.info("架构测试完成: 状态=%s 分数=%s 违规=%d 模块=%d",
                result.status, result.score, len(violations), len(arch.all_modules))
    return result
def _compute_abstraction(
        all_modules: set, *, infra_modules) -> tuple[set, set, float]:
    modules = {m for m in all_modules if not _is_entry_module(m)}
    abstract_modules = {m for m in modules
                        if _ABSTRACT_NAME_TOKENS.intersection(_module_tokens(m))}
    utils_modules = _collect_utils_modules(modules, infra_modules)
    concrete_modules = modules - abstract_modules - utils_modules
    abstraction_ratio = len(abstract_modules) / max(len(modules), 1)
    return abstract_modules, concrete_modules, abstraction_ratio
def _abort_invalid_dir(skill_dir, start, *,
                       method_name: str,
                       method_id: str,
                       reason: str = _MISSING_DIR_REASON) -> TestMethodResult:
    _log.warning("%s分析目录无效（%s），按 error 终止: %r",
                 method_name, reason, skill_dir)
    result = TestMethodResult.invalid_input(
        skill_dir, method_name, method_id, "分析", start)
    if reason != _MISSING_DIR_REASON:
        result.error = f"{reason}: {skill_dir!r}"
        result.summary = f"分析目录不可用（{reason}）: {skill_dir!r}"
    return result
def _resolve_effective_dir(skill_dir, cache) -> str:
    try:
        resolved = os.fsdecode(os.fspath(skill_dir))
    except (TypeError, ValueError) as exc:
        _log.debug("_resolve_effective_dir: 目录参数不可解析: %s", exc)
        return ""
    if not resolved.strip():
        return ""
    resolved = os.path.abspath(resolved)
    if not os.path.isdir(resolved):
        return resolved
    if cache is not None:
        cached_dir = getattr(cache, "skill_dir", "")
        if isinstance(cached_dir, str) and cached_dir.strip():
            cached_dir = os.path.abspath(cached_dir)
            if os.path.normcase(cached_dir) != os.path.normcase(resolved):
                _log.warning("共享缓存目录与入参不一致，按缓存目录分析: %r -> %r",
                             resolved, cached_dir)
            resolved = cached_dir
    return resolved
def _prepare_cache(skill_dir: str, kwargs: dict) -> tuple:
    cache: FileCache = kwargs.get('_cache')
    resolved = _resolve_effective_dir(skill_dir, cache)
    if not resolved or not os.path.isdir(resolved):
        return None, ""
    if cache is None:
        _log.debug("架构测试无共享缓存，现场构建: %s", resolved)
        cache = _ProjectFileCache(resolved)
        cache.load()
    elif not cache.entries:
        return None, resolved
    return cache, resolved
def _append_cycle_violations(cycles: list, violations: list) -> None:
    for cycle in cycles:
        violations.append({
            "type": "circular_dependency", "severity": "high",
            "modules": cycle,
            "message": f"循环依赖: {' → '.join(cycle)} → {cycle[0]}",
        })
def run_architecture_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name=_ARCH_METHOD_NAME,
        method_id=_ARCH_METHOD_ID,
    )
    cache, effective_dir = _prepare_cache(skill_dir, kwargs)
    if cache is None or not cache.entries:
        return _abort_invalid_dir(
            skill_dir, start,
            method_name=_ARCH_METHOD_NAME, method_id=_ARCH_METHOD_ID,
            reason=_MISSING_DIR_REASON if not effective_dir else _NO_SOURCE_REASON)
    if not _gate_entries(cache):
        return _abort_invalid_dir(
            skill_dir, start, method_name=_ARCH_METHOD_NAME,
            method_id=_ARCH_METHOD_ID, reason="无可解析源码")
    violations = []
    import_graph, module_functions = _build_arch_graph(cache)
    cycles = detect_cycles(import_graph)
    _append_cycle_violations(cycles, violations)
    in_degrees = _in_degrees(import_graph)
    layer_map = target_layer_map(effective_dir)
    infra_modules = target_infra_modules(effective_dir, dict(in_degrees))
    all_modules = _scan_basic_structure_violations(
        import_graph, module_functions, cache, violations, in_degrees,
        layer_map=layer_map, infra_modules=infra_modules)
    violations.extend(_check_layer_direction_solid(
        import_graph, all_modules,
        layer_map=layer_map, infra_modules=infra_modules))
    violations.extend(_check_all_consistency(cache))
    abstract_modules, concrete_modules, abstraction_ratio = _compute_abstraction(
        all_modules, infra_modules=infra_modules)
    (transitive_deps, module_instability, naming_prefixes,
     module_responsibilities) = _check_advanced_metrics(
        import_graph, all_modules, cache, violations, has_cycles=bool(cycles),
        in_degrees=in_degrees,
    )
    arch = _ArchIntermediate(
        all_modules=all_modules, import_graph=import_graph, cycles=cycles,
        abstract_modules=abstract_modules, concrete_modules=concrete_modules,
        abstraction_ratio=abstraction_ratio, transitive_deps=transitive_deps,
        module_instability=module_instability, naming_prefixes=naming_prefixes,
        module_responsibilities=module_responsibilities,
    )
    return _finalize_architecture_results(result, cache, violations, arch, start)
@dataclass
class _SmokeTally:
    passed: int = 0
    failed: int = 0
    blocking: int = 0
    failures: list = field(default_factory=list)
    syntax_ok: int = 0
    syntax_fail: int = 0
    unreadable: int = 0
    circular: int = 0
    def absorb(self, passed: int, failed: int, failures) -> None:
        self.passed += passed
        self.failed += failed
        self.failures.extend(failures)
    def absorb_failure(self, failure) -> None:
        if failure is None:
            self.passed += 1
        else:
            self.failed += 1
            self.failures.append(failure)
def _init_is_pure_marker(init_tree) -> bool:
    return all(
        (isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
         and (isinstance(node.value.value, str) or node.value.value is Ellipsis))
        or isinstance(node, ast.Pass)
        or (isinstance(node, ast.ImportFrom) and node.module == '__future__')
        for node in init_tree.body)
def _smoke_check_init_surface(init_tree) -> tuple[int, int, list]:
    if not init_tree:
        return 0, 0, []
    if _init_is_pure_marker(init_tree):
        return 0, 0, []
    _passed = 0
    _failed = 0
    _failures: list = []
    if _init_public_api_face(init_tree):
        _passed += 1
    else:
        _failed += 1
        _failures.append({"check": "public_api", "message": "__init__.py 无公开函数/类"})
    if isinstance(ast.get_docstring(init_tree), str):
        _passed += 1
    else:
        _failed += 1
        _failures.append({"check": "module_docstring", "message": "__init__.py 缺少模块文档字符串"})
    sig_p, sig_f, sig_failures = _init_entry_signature_failures(init_tree)
    _passed += sig_p
    _failed += sig_f
    _failures.extend(sig_failures)
    return _passed, _failed, _failures
def _init_public_api_face(init_tree) -> bool:
    for node in _iter_import_time_binding_nodes(init_tree):
        if _node_is_public_api_evidence(node):
            return True
    return False
_PUBLIC_DEF_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
def _node_binds_module_getattr(node) -> bool:
    if '__getattr__' in dynamic_module_binding_names(node):
        return True
    if isinstance(node, _PUBLIC_DEF_TYPES):
        return node.name == '__getattr__'
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        names, _has_star = import_binding_names(node)
        return '__getattr__' in names
    if (isinstance(node, (ast.Assign, ast.AnnAssign))
            and isinstance(node.value,
                           (ast.Constant, ast.List, ast.Tuple, ast.Set, ast.Dict))):
        return False
    return '__getattr__' in _module_scope_binding_names(node)
def _node_is_public_api_evidence(node) -> bool:
    if _node_binds_module_getattr(node):
        return True
    if any(not name.startswith('_')
           for name in dynamic_module_binding_names(node)):
        return True
    if isinstance(node, _PUBLIC_DEF_TYPES):
        return not node.name.startswith('_')
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        names, has_star = import_binding_names(node)
        return has_star or any(not name.startswith('_') for name in names)
    if not _assign_defines_name(node, "__all__", allow_aug=True):
        return False
    value = getattr(node, "value", None)
    return not (isinstance(value, (ast.List, ast.Tuple, ast.Set))
                and not value.elts)
def _assign_defines_name(node, name: str, allow_aug: bool = False) -> bool:
    if isinstance(node, ast.AnnAssign) and node.value is None:
        return False
    if isinstance(node, ast.AugAssign) and not allow_aug:
        return False
    return any(t.id == name for t in export_assignment_targets(node))
_ENTRY_PARAM_LIMIT = 10
def _init_entry_signature_failures(init_tree) -> tuple[int, int, list]:
    _passed = 0
    _failed = 0
    _failures: list = []
    for node in _iter_import_time_binding_nodes(init_tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) \
                and not node.name.startswith('_'):
            param_count = (len(node.args.posonlyargs) + len(node.args.args)
                           + len(node.args.kwonlyargs)
                           + (node.args.vararg is not None)
                           + (node.args.kwarg is not None))
            if param_count > _ENTRY_PARAM_LIMIT:
                _failed += 1
                _failures.append({"check": "entry_signature", "message": (f"入口函数 {node.name} 参数过多 "
                                                                              f"({param_count}, 阈值 {_ENTRY_PARAM_LIMIT})")})
            else:
                _passed += 1
            if node.returns is None:
                _failed += 1
                _failures.append({"check": "entry_return_annotation", "message": f"入口函数 {node.name} 缺少返回类型注解"})
            else:
                _passed += 1
    return _passed, _failed, _failures
_MD_VERSION_KEYS = frozenset({"version", "版本号", "版本"})
_MD_OPTIONAL_SECTION_CHECKS = (
    ("md_changelog", ("## 变更", "### 变更", "变更记录", "更新日志",
                      "changelog", "版本历史")),
)
_MD_MIN_LENGTH = 200
_SMOKE_FINDING_LIMIT = 30
def _smoke_check_skill_md_content(skill_dir) -> tuple[int, int, list]:
    skill_md_path = os.path.join(skill_dir, "SKILL.md")
    if not os.path.isfile(skill_md_path):
        return 0, 0, []
    try:
        with open(skill_md_path, encoding='utf-8') as f:
            md_content = f.read()
    except (OSError, UnicodeDecodeError) as e:
        _log.warning("_smoke_check_skill_md_content: SKILL.md 不可读: %s", e)
        return 0, 1, [{"check": "md_unreadable",
                       "message": f"SKILL.md 不可读: {type(e).__name__}"}]
    return _skill_md_content_verdict(md_content)
def _skill_md_content_verdict(md_content: str) -> tuple[int, int, list]:
    md_lower = md_content.lower()
    lines = md_content.splitlines()
    frontmatter_lines: list[str] = []
    if lines and lines[0].strip() == "---":
        for index, line in enumerate(lines[1:], start=1):
            if line.strip() in {"---", "..."}:
                frontmatter_lines = lines[1:index]
                break
    has_version = False
    for line in frontmatter_lines:
        if not line or line[0].isspace() or line.lstrip().startswith("#"):
            continue
        key, separator, value = line.partition(":")
        if not separator:
            key, separator, value = line.partition("：")
        if not separator or key.strip() not in _MD_VERSION_KEYS:
            continue
        value = value.split("#", 1)[0].strip().strip("'\"").strip()
        has_version = bool(value) and value.lower() not in {"null", "~"}
        if has_version:
            break
    _md_checks = 0
    _md_fail = 0
    _md_failures: list = []
    if has_version:
        _md_checks += 1
    else:
        _md_fail += 1
        _md_failures.append({"check": "md_version",
                             "message": "SKILL.md 缺少版本号"})
    for check, tokens in _MD_OPTIONAL_SECTION_CHECKS:
        if any(token in md_lower for token in tokens):
            _md_checks += 1
    if len(md_content) >= _MD_MIN_LENGTH:
        _md_checks += 1
    else:
        _md_fail += 1
        _md_failures.append({
            "check": "md_too_short",
            "message": f"SKILL.md 内容过短 (<{_MD_MIN_LENGTH}字符)",
        })
    return _md_checks, _md_fail, _md_failures
def _finalize_smoke_verdict(result, tally: _SmokeTally, start):
    total_checks = tally.passed + tally.failed
    result.metrics = {
        "total_checks": total_checks,
        "passed": tally.passed,
        "failed": tally.failed,
        "blocking_failures": tally.blocking,
        "syntax_ok_files": tally.syntax_ok,
        "syntax_fail_files": tally.syntax_fail,
        "unreadable_files": tally.unreadable,
        "circular_imports": tally.circular,
        "findings_truncated": len(tally.failures) > _SMOKE_FINDING_LIMIT,
        "check_coverage": round(tally.passed / total_checks * 100, 1) if total_checks > 0 else 0,
    }
    result.findings = tally.failures[:_SMOKE_FINDING_LIMIT]
    if tally.blocking:
        result.status = "fail"
        result.score = 25
        result.summary = (f"冒烟测试阻断: {tally.blocking} 项致命失败"
                          f" ({tally.passed}/{total_checks} 通过)")
    elif tally.failed == 0:
        result.status = "pass"
        result.score = 100
        result.summary = f"冒烟测试全部通过 ({tally.passed}/{total_checks})"
    elif tally.failed <= 1:
        result.status = "warn"
        result.score = 70
        result.summary = f"冒烟测试 {tally.passed}/{total_checks} 通过"
    else:
        result.status = "warn"
        result.score = 30
        result.summary = f"冒烟测试 {tally.passed}/{total_checks} 通过, {tally.failed} 项失败"
    return result.finish(start)
def _smoke_graph_key(entry) -> str:
    return (entry_module_dotted(entry).removeprefix("src.")
            or getattr(entry, "mod_stem", ""))
def _add_internal_import_edge(
        graph, source: str, raw_name: str,
        internal_keys: set[str], aliases: dict[str, str],
        *, skip: frozenset[str] | set[str] = frozenset()) -> bool:
    raw_name = raw_name.removeprefix("src.").strip(".")
    if not raw_name:
        return False
    candidates = {raw_name}
    for alias, alias_target in aliases.items():
        if raw_name == alias and alias_target:
            candidates.add(alias_target)
        elif raw_name.startswith(alias + "."):
            relative_name = raw_name[len(alias) + 1:]
            if relative_name:
                candidates.add(relative_name)
    matches: set[str] = set()
    for candidate in candidates:
        candidate_matches = {key for key in internal_keys if key == candidate}
        if not candidate_matches:
            candidate_matches = {
                key for key in internal_keys
                if key.endswith("." + candidate)
            }
        matches.update(candidate_matches)
    for target in matches:
        if target != source and target not in skip:
            graph[source].add(target)
    return bool(matches)
def _smoke_import_graph(cache) -> dict[str, set[str]]:
    entries = _gate_entries(cache)
    keys_by_entry = {id(entry): _smoke_graph_key(entry) for entry in entries}
    keys_by_rel = {
        entry_rel_path(entry).replace("\\", "/"): keys_by_entry[id(entry)]
        for entry in entries
    }
    internal_keys = set(keys_by_entry.values())
    aliases: dict[str, str] = {}
    root = getattr(cache, "skill_dir", "") or ""
    root_alias = _root_package_alias(root)
    root_key = keys_by_rel.get("__init__.py", "")
    if root and root_key:
        aliases[os.path.basename(os.path.abspath(root))] = root_key

    def _ancestor_init_keys(entry) -> set[str]:
        # 模块导入时会先执行其祖先包入口；包入口再导入子模块是常规布局，
        # 子模块对**自身**祖先入口的回指恒成立（``import pkg.util`` 先执行
        # ``pkg/__init__``）。把它计入冒烟循环图，任何“门面导入子模块 +
        # 子模块绝对导入同包子模块”的合法技能都会被判成致命循环导入；
        # 这与架构图对祖先入口回指的口径保持一致，只跳过自身祖先，
        # 兄弟包/祖孙包之间的真实环仍会保留。
        parts = entry_rel_path(entry).replace("\\", "/").split("/")
        keys: set[str] = set()
        for index in range(len(parts) - 1, 0, -1):
            key = keys_by_rel.get("/".join(parts[:index]) + "/__init__.py")
            if key:
                keys.add(key)
        if root_key and parts != ["__init__.py"]:
            keys.add(root_key)
        return keys

    graph: dict[str, set[str]] = {
        source: set() for source in internal_keys if source}
    for entry in entries:
        source = keys_by_entry[id(entry)]
        if not source or entry.tree is None:
            continue
        skip = _ancestor_init_keys(entry)
        for node in _iter_import_time_binding_nodes(entry.tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    # ``import a.b.c`` 依次执行 a、a.b 的 __init__ 与 c：只记完整
                    # 点名会漏掉对包门面的依赖，经门面回指的循环随之漏报。
                    parts = alias.name.split(".")
                    for index in range(1, len(parts) + 1):
                        prefix = ".".join(parts[:index])
                        if index < len(parts) and prefix == root_alias:
                            # 根包 __init__ 是包内每个模块的导入发起者，
                            # ``import <root>.sibling`` 对它的回指对扁平包恒成立，
                            # 计入只会把全部绝对兄弟导入判成环；真正依赖根命名空间
                            # 的 ``from <root> import x`` 仍由下方别名解析记边。
                            continue
                        _add_internal_import_edge(
                            graph, source, prefix, internal_keys, aliases,
                            skip=skip)
                continue
            if not isinstance(node, ast.ImportFrom):
                continue
            base = _import_dotted_name(entry, node, root)
            if base is None:
                continue
            if node.module:
                _add_internal_import_edge(
                    graph, source, base, internal_keys, aliases, skip=skip)
            for alias in node.names:
                raw_name = (f"{base}.{alias.name}" if base else alias.name)
                matched = _add_internal_import_edge(
                    graph, source, raw_name, internal_keys, aliases,
                    skip=skip)
                if not matched and node.level and not node.module:
                    _add_internal_import_edge(
                        graph, source, base or "__init__",
                        internal_keys, aliases, skip=skip)
    return graph
def _smoke_check_circular_imports(cache) -> tuple:
    mod_level_graph = _smoke_import_graph(cache)
    real_cycles = detect_cycles(mod_level_graph) if mod_level_graph else []
    real_count = len(real_cycles)
    if real_count == 0:
        return (0, None)
    file_path, line = _cycle_import_location(cache, real_cycles[0])
    cycle_text = "; ".join(
        " -> ".join([*(str(stem) for stem in cycle), str(cycle[0])])
        for cycle in real_cycles[:3] if cycle)
    message = f"检测到 {real_count} 个循环导入"
    if cycle_text:
        message = f"{message}: {cycle_text}"
    return (real_count, {
        "check": "circular_import",
        "rule_id": "circular_import",
        "message": message,
        "file": file_path,
        "line": line,
        "cycles": real_cycles,
    })
def _cycle_import_location(cache, cycle: list) -> tuple[str, int]:
    by_path, by_stem = module_entry_indexes(cache)
    root = getattr(cache, "skill_dir", "") or ""
    for stem in cycle:
        normalized_stem = stem.removeprefix("src.")
        entry = by_path.get(stem)
        if entry is None:
            entry = by_path.get(normalized_stem)
        if entry is None:
            entry = by_path.get(f"src.{normalized_stem}")
        if entry is not None and _entry_pruned(entry):
            entry = None
        if entry is None:
            candidates = [candidate for candidate in by_stem.get(stem, [])
                          if not _entry_pruned(candidate)]
            entry = candidates[0] if len(candidates) == 1 else None
        if entry is None or entry.tree is None:
            continue
        targets = {target.removeprefix("src.")
                   for target in cycle if target != stem}
        for node in _iter_import_time_binding_nodes(entry.tree):
            if not isinstance(node, (ast.Import, ast.ImportFrom)):
                continue
            if isinstance(node, ast.Import):
                names = [alias.name for alias in node.names]
            else:
                base = _import_dotted_name(entry, node, root)
                if base is None:
                    continue
                names = [base] if node.module else []
                names.extend(
                    f"{base}.{alias.name}" if base else alias.name
                    for alias in node.names)
            for name in names:
                normalized_name = name.removeprefix("src.")
                if any(normalized_name == target
                       or normalized_name.endswith("." + target)
                       or target.endswith("." + normalized_name)
                       for target in targets):
                    return entry.rel_path.replace('\\', '/'), node.lineno
    return "", 0
def _smoke_check_entry_reachability(
        init_tree, cache, tally: _SmokeTally) -> None:
    unreachable_exports = _unreachable_all_exports(init_tree, cache)
    if not unreachable_exports:
        tally.absorb_failure(None)
        return
    tally.absorb_failure({
        "check": "entry_reachable",
        "message": (f"__all__ 中 {len(unreachable_exports)} 个名称无法"
                    f"从 __init__ 到达: "
                    f"{', '.join(sorted(unreachable_exports)[:5])}"),
    })
def _smoke_check_relative_imports(cache) -> tuple[dict | None, bool]:
    root = getattr(cache, "skill_dir", "") or ""
    if not root:
        _log.debug("relative_import check skipped: cache has no skill_dir")
        return (None, False)
    bad_relative_imports = sum(
        1 for entry in _gate_entries(cache)
        for node in nodes_where(entry, (ast.ImportFrom,))
        if _relative_import_is_broken(entry.path, node, root)
    )
    if bad_relative_imports == 0:
        return (None, True)
    return ({
        "check": "relative_import",
        "message": f"{bad_relative_imports} 个相对导入目标模块或符号不存在",
    }, True)
def _package_import_names(init_path: str) -> set[str] | None:
    if not os.path.isfile(init_path):
        return set()
    try:
        with tokenize.open(init_path) as source_file:
            tree = ast.parse(source_file.read(), filename=init_path)
    except (OSError, SyntaxError, UnicodeError, ValueError,
            RecursionError, MemoryError) as exc:
        _log.debug("package init parse degraded: %s", exc)
        return None
    names: set[str] = set()
    for node in _iter_import_time_binding_nodes(tree):
        if _node_binds_module_getattr(node):
            return None
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            bound, has_star = import_binding_names(node)
            if has_star:
                return None
            names |= bound
            continue
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == 'globals'):
            return None
        names |= _module_scope_binding_names(node)
    return names
def _relative_module_exists(base: str | os.PathLike, dotted_name: str) -> bool:
    target = os.path.join(base, *dotted_name.split('.'))
    return os.path.isfile(target + '.py') or os.path.isdir(target)
def _relative_import_is_broken(entry_path: str, node, root: str) -> bool:
    if not node.level:
        return False
    base = relative_import_base(entry_path, node.level, root)
    if base is None:
        return True
    import_base = base
    if node.module:
        target = os.path.join(base, *node.module.split('.'))
        if not os.path.isdir(target):
            module_path = target + '.py'
            if not os.path.isfile(module_path):
                return True
            if any(alias.name == '*' for alias in node.names):
                return False
            module_names = _package_import_names(module_path)
            if module_names is None:
                return False
            return any(alias.name not in module_names for alias in node.names)
        import_base = target
    package_names = _package_import_names(os.path.join(import_base, '__init__.py'))
    for alias in node.names:
        if alias.name == '*':
            continue
        if _relative_module_exists(import_base, alias.name):
            continue
        if package_names is None or alias.name in package_names:
            continue
        return True
    return False
def run_smoke_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name=_SMOKE_METHOD_NAME,
        method_id=_SMOKE_METHOD_ID,
    )
    cache: FileCache = kwargs.get('_cache')
    resolved_dir = _resolve_effective_dir(skill_dir, cache)
    if not resolved_dir or not os.path.isdir(resolved_dir):
        return _abort_invalid_dir(
            skill_dir, start,
            method_name=_SMOKE_METHOD_NAME, method_id=_SMOKE_METHOD_ID)
    skill_dir = resolved_dir
    if cache is None:
        cache = _ProjectFileCache(skill_dir)
        cache.load()
    if not cache.entries:
        return _abort_invalid_dir(
            skill_dir, start,
            method_name=_SMOKE_METHOD_NAME, method_id=_SMOKE_METHOD_ID,
            reason=_NO_SOURCE_REASON)
    if not _gate_file_entries(cache):
        return _abort_invalid_dir(
            skill_dir, start, method_name=_SMOKE_METHOD_NAME,
            method_id=_SMOKE_METHOD_ID, reason="无可扫描源码")
    tally = _SmokeTally()
    nested_layout = skill_has_nested_sources(skill_dir)
    has_skill_manifest = os.path.isfile(os.path.join(skill_dir, "SKILL.md"))
    init_tree, init_p, init_f, init_failures, init_blocking = \
        _smoke_check_init_parse(cache, allow_missing=nested_layout)
    tally.absorb(init_p, init_f, init_failures)
    tally.blocking += init_blocking
    if has_skill_manifest:
        tally.passed += 1
    syntax = _smoke_check_syntax(cache)
    tally.syntax_ok, tally.syntax_fail = syntax[0], syntax[1]
    tally.unreadable = syntax[2]
    tally.absorb(syntax[3], syntax[4], syntax[5])
    if tally.syntax_fail:
        tally.blocking += 1
    tally.absorb(*_smoke_check_version(
        init_tree, has_skill_manifest=has_skill_manifest,
        importable_package=_package_name_importable(skill_dir)))
    tally.circular = _smoke_run_semantic_checks(
        init_tree, cache, tally, skip_reachability=init_tree is None)
    if tally.circular:
        tally.blocking += 1
    for passed, failed, failures in (_smoke_check_init_surface(init_tree),
                                     _smoke_check_skill_md_content(skill_dir)):
        tally.absorb(passed, failed, failures)
    return _finalize_smoke_verdict(result, tally, start)
def _smoke_run_semantic_checks(init_tree, cache, tally: _SmokeTally, *,
                               skip_reachability: bool = False) -> int:
    circular_count, circ_failure = _smoke_check_circular_imports(cache)
    tally.absorb_failure(circ_failure)
    if not skip_reachability:
        _smoke_check_entry_reachability(init_tree, cache, tally)
    rel_failure, rel_executed = _smoke_check_relative_imports(cache)
    if rel_executed:
        tally.absorb_failure(rel_failure)
    return circular_count
def _smoke_check_init_parse(cache, *, allow_missing: bool) -> tuple:
    _passed = 0
    _failed = 0
    _blocking = 0
    _failures: list = []
    init_tree = None
    init_entry, _prefix = _facade_entry(cache)
    if init_entry is None:
        if not allow_missing:
            _failed += 1
            _blocking += 1
            _failures.append({"check": "init_exists", "message": "缺少 __init__.py"})
        return init_tree, _passed, _failed, _failures, _blocking
    if init_entry.tree is not None:
        _passed += 1
        init_tree = init_entry.tree
    else:
        _failed += 1
        parse_error = getattr(init_entry, "parse_error", None)
        if is_transient_io_error(parse_error):
            _failures.append({"check": "init_unreadable",
                              "message": parse_error or "__init__.py 不可读"})
        else:
            _blocking += 1
            _failures.append({"check": "init_parse",
                              "message": "__init__.py 语法错误"})
    return init_tree, _passed, _failed, _failures, _blocking
def _smoke_check_syntax(cache) -> tuple:
    _ok = 0
    _syntax_fail = 0
    _unreadable = 0
    _failures: list = []
    for e in _gate_file_entries(cache):
        if e.tree is not None:
            _ok += 1
            continue
        parse_error = getattr(e, "parse_error", None)
        if is_transient_io_error(parse_error):
            _unreadable += 1
            _failures.append({"check": "unreadable", "file": e.rel_path,
                              "message": parse_error or "文件不可读"})
            continue
        _syntax_fail += 1
        _failures.append({"check": "syntax", "file": e.rel_path,
                          "message": parse_error or "语法错误"})
    if _syntax_fail or _unreadable:
        return _ok, _syntax_fail, _unreadable, 0, 1, _failures
    return _ok, 0, 0, 1, 0, []
def _package_name_importable(skill_dir: str) -> bool:
    """技能目录名能否作为 Python 包名 import。

    目录名含连字符（如 ``antu-cad``）时无法 ``import``，其 ``__init__.py``
    只是脚本目录的命名空间占位，版本唯一事实源是 SKILL.md frontmatter。
    """
    return os.path.basename(os.path.normpath(skill_dir)).isidentifier()


def _smoke_check_version(init_tree, *, has_skill_manifest: bool,
                         importable_package: bool = True) -> tuple:
    if not importable_package:
        return 0, 0, []
    if not has_skill_manifest or not init_tree:
        return 0, 0, []
    for node in _iter_import_time_binding_nodes(init_tree):
        if _version_binding_node(node):
            return 1, 0, []
    return 0, 1, [{"check": "version", "message": "__init__.py 缺少 __version__"}]
def _version_binding_node(node) -> bool:
    if isinstance(node, ast.ImportFrom):
        return any((alias.asname or alias.name) == "__version__"
                   for alias in node.names)
    return (_assign_defines_name(node, "__version__")
            or "__version__" in dynamic_module_binding_names(node))

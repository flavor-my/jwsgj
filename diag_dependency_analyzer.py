from __future__ import annotations  # noqa: I001
import argparse
import ast
import json
import logging
import math
import os
import sys
from collections import Counter, defaultdict
from collections.abc import Callable
from typing import Any, NamedTuple
import jwsgj.diag_module_topology as _layer_registry
from jwsgj.diag_dependency_core import (
    Finding,
    PackageRootResolver,
    _ParsedSourceCache,
    fan_severity,
    import_chain_findings,
    import_target_exists,
    resolve_global_fan_threshold,
    resolve_layer_fan_thresholds,
)
from jwsgj.diag_module_surface import (
    dynamic_module_binding_names,
    extract_all_surface,
    is_main_guard_if,
    iter_match_capture_names,
    iter_module_level_imports_tc,
    iter_module_level_nodes_tc,
    iter_static_edge_nodes,
    iter_walrus_expr_bindings,
    layout_of,
    relative_import_base,
)
from jwsgj.diag_module_topology import (
    apply_layer_suggestions,
    has_layer_registry_surface,
    import_in_degrees,
    is_registry_host,
    target_infra_modules,
    target_layer_map,
)
from jwsgj.diag_shared_ast_nodes import (
    iter_unpack_target_names,
    resolve_import_binding,
)
from jwsgj.diag_shared_ast_views import (
    collect_lexical_scope_table,
    parent_map,
    scope_import_tables,
    scope_node_bound_names,
    scope_shadows_import,
)
from jwsgj.diag_shared_source_core import (
    count_lines,
    read_source,
    read_source_auto,
)
from jwsgj.diag_types_normalize import mean_std
from jwsgj.diag_types_vocab import MAX_FILE_LINES, PARSE_DEGRADE_EXC
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_scope import (
    DependencyGraph,
    cycle_member_groups,
    import_key,
    iter_prod_py_files,
    safe_relpath,
    tarjan_scc,
)
from jwsgj.prevention_scope_facts import walk_nodes
logger = logging.getLogger(__name__)
_HEALTH_DEDUCTIONS: dict[str, int] = {
    "D9-CYCLE": 15,
    "D9-LAYER": 5,
    "D9-LAYER-IMPLICIT": 5,
    "D9-ORPHAN-FULL": 3,
    "D9-ORPHAN-SEMI": 1,
    "D9-HIGH-FANIN": 2,
    "D9-HIGH-FANOUT": 2,
    "D9-SELF-IMPORT": 2,
    "D9-HUB": 3,
}
_BROKEN_IMPORT_RULES = frozenset({"D9-BROKEN-IMPORT", "D9-BROKEN-SYMBOL"})
_FAN_RULES = frozenset({"D9-HIGH-FANIN", "D9-HIGH-FANOUT"})
_HUB_STABLE_MAX_FANOUT = 0
_MODULE_IMPORT_SYMBOL = "<module>"
_LOAD_ERRORS = (OSError, *PARSE_DEGRADE_EXC)
_TYPE_ALIAS_TYPES = (ast.TypeAlias,) if hasattr(ast, "TypeAlias") else ()
GENERIC_SCRIPT_MODULES: frozenset[str] = frozenset({
    "setup", "conftest", "noxfile", "fabfile", "manage",
    "wsgi", "asgi", "__main__", "__init__",
})
def _package_entry_identity(skill_dir: str, fpath: str) -> str:
    root = os.path.abspath(skill_dir)
    pkg_dir = os.path.dirname(os.path.abspath(fpath))
    try:
        rel = os.path.relpath(pkg_dir, root)
    except ValueError:  # jwsgj:silent-ok
        return ''
    if os.path.isabs(rel) or rel == os.pardir or rel.startswith(os.pardir + os.sep):
        return ''
    source_root, root_package = _package_scan_root(root)
    layout = layout_of(root)
    package_root = (os.path.abspath(layout.package_root)
                    if layout.is_package else '')
    return _scan_module_name(
        os.path.abspath(fpath), root, source_root, root_package, package_root)
def _has_main_guard(tree: ast.AST) -> bool:
    return any(is_main_guard_if(node) for node in getattr(tree, 'body', ()))
def _package_init_key(path: str) -> str:
    return os.path.normcase(os.path.abspath(path))
def _deleted_from_stmt(node: ast.stmt) -> set[str]:
    if not isinstance(node, ast.Delete):
        return set()
    return {name for target in node.targets
            for name in iter_unpack_target_names(target)}
def _collect_defined_and_bound(tree: ast.Module) -> tuple[set[str], set[str]]:
    defined: set[str] = set()
    bound: set[str] = set()
    last_binding: dict[str, tuple[int, int]] = {}
    last_deletion: dict[str, tuple[int, int]] = {}
    for node, under_tc in iter_module_level_nodes_tc(
            tree, include_class_body=False):
        if under_tc:
            continue
        node_defined = _defined_from_stmt(node)
        node_defined.update(iter_walrus_expr_bindings(node))
        # ``globals()['x'] = v`` / ``globals().update({...})`` 同样定义模块属性。
        node_defined.update(dynamic_module_binding_names(node))
        node_bound = _bound_from_import(node)
        defined |= node_defined
        bound |= node_bound
        position = (getattr(node, 'lineno', 0),
                    getattr(node, 'col_offset', 0))
        for name in node_defined | node_bound:
            if position > last_binding.get(name, (-1, -1)):
                last_binding[name] = position
        for name in _deleted_from_stmt(node):
            if position > last_deletion.get(name, (-1, -1)):
                last_deletion[name] = position
    for name, position in last_deletion.items():
        if last_binding.get(name, (-1, -1)) < position:
            defined.discard(name)
            bound.discard(name)
    return defined, bound | defined
def _defined_from_stmt(node: ast.stmt) -> set[str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name}
    if isinstance(node, _TYPE_ALIAS_TYPES):
        return {node.name.id} if isinstance(node.name, ast.Name) else set()
    if isinstance(node, ast.Assign):
        return _assign_bound_names(node.targets)
    if isinstance(node, ast.AnnAssign):
        return _annassign_name(node)
    if isinstance(node, (ast.For, ast.AsyncFor, ast.With, ast.AsyncWith)):
        return _defined_from_targets(node)
    if isinstance(node, ast.Match):
        return _match_capture_names(node)
    return set()
def _assign_bound_names(targets: list[ast.expr]) -> set[str]:
    return {name for target in targets
            for name in iter_unpack_target_names(target)}
def _match_capture_names(node: ast.Match) -> set[str]:
    return {name for case in node.cases
            for name in iter_match_capture_names(case.pattern)}
def _annassign_name(node: ast.AnnAssign) -> set[str]:
    if isinstance(node.target, ast.Name) and node.value is not None:
        return {node.target.id}
    return set()
def _defined_from_targets(node: ast.stmt) -> set[str]:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return set(iter_unpack_target_names(node.target))
    return {name for item in node.items if item.optional_vars is not None
            for name in iter_unpack_target_names(item.optional_vars)}
def _bound_from_import(node: ast.stmt) -> set[str]:
    if isinstance(node, ast.ImportFrom):
        return {alias.asname or alias.name for alias in node.names}
    if isinstance(node, ast.Import):
        return {alias.asname or alias.name.split(".")[0]
                for alias in node.names}
    return set()
def _ctx_value(ctx: Any, getter: str, fpath: str,
               expected_type: type, tag: str) -> Any:
    if ctx is None:
        return None
    try:
        value = getattr(ctx, getter)(fpath)
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e, context=f'{tag}:{type(_e).__name__}')
        return None
    return value if isinstance(value, expected_type) else None
def _has_dynamic_export_channel(tree: ast.Module, bound: set[str]) -> bool:
    if "__getattr__" in bound:
        return True
    for node, under_tc in iter_module_level_nodes_tc(
            tree, include_class_body=False):
        if under_tc:
            continue
        if (isinstance(node, ast.ImportFrom)
                and any(alias.name == "*" for alias in node.names)):
            return True
    return False
class ApiContractAuditor:
    def __init__(self, skill_dir: str, py_files: list[str],
                 ctx: Any | None = None):
        self.skill_dir = skill_dir
        self.py_files = py_files
        self.ctx = ctx
    def _load_source(self, fp: str) -> str:
        source = _ctx_value(
            self.ctx, 'get_source', fp, str,
            'ApiContractAuditor._load_source')
        return source if source is not None else read_source_auto(fp)
    def _load_tree(self, fp: str, source: str) -> ast.Module:
        tree = _ctx_value(
            self.ctx, 'get_ast', fp, ast.Module,
            'ApiContractAuditor._load_tree')
        if tree is not None:
            return tree
        return compile(source, fp, "exec", ast.PyCF_ONLY_AST)
    def _load_module_tree(self, fp: str) -> ast.Module | None:
        try:
            source = self._load_source(fp)
            return self._load_tree(fp, source)
        except _LOAD_ERRORS as e:
            logger.info("[ApiContractAuditor] API 契约分析跳过不可读/不可解析文件: %s: %s", fp, e)
            return None
    @staticmethod
    def _ghost_export_text(name: str) -> str:
        return f"__all__ 导出 '{name}' 但未在文件中定义或导入"
    def _find_ghost_exports(self, fp: str, all_names: list[str],
                            bound: set[str]) -> Finding | None:
        ghost_names = [name for name in all_names if name not in bound]
        if not ghost_names:
            return None
        if len(ghost_names) == 1:
            _msg = self._ghost_export_text(ghost_names[0])
        else:
            _msg = (f"__all__ 幽灵导出({len(ghost_names)}个): "
                    + ", ".join(f"'{n}'" for n in ghost_names))
        return Finding(
            rule_id="API-01",
            severity="P1",
            message=_msg,
            file=safe_relpath(fp, self.skill_dir),
            confidence=0.95,
            detail=("\n".join(
                self._ghost_export_text(n)
                for n in ghost_names)
                if len(ghost_names) > 1 else ""),
        )
    def _find_unexported_publics(self, fp: str, fname: str,
                                 defined: set[str],
                                 all_names: list[str]) -> list[Finding]:
        if fname.lower() != "__init__.py":
            return []
        return [Finding(
            rule_id="API-02",
            severity="P3",
            message=f"公开名称 '{name}' 未在 __all__ 中导出",
            file=safe_relpath(fp, self.skill_dir),
            confidence=0.5,
        ) for name in sorted(defined)
            if not name.startswith("_") and name not in all_names]
    def api_contract_analysis(self) -> dict:
        findings: list[Finding] = []
        for fp in sorted(self.py_files):
            fname = os.path.basename(fp)
            tree = self._load_module_tree(fp)
            if tree is None:
                continue
            surface = extract_all_surface(tree)
            if surface is None:
                continue
            defined, bound = _collect_defined_and_bound(tree)
            ghost = (None if (_has_dynamic_export_channel(tree, bound)
                              or not surface.complete)
                     else self._find_ghost_exports(fp, surface.names, bound))
            if ghost is not None:
                findings.append(ghost)
            if surface.complete:
                findings.extend(self._find_unexported_publics(
                    fp, fname, defined, surface.names))
        return {"findings": findings}
def _health_deduction(finding: Finding) -> int:
    if finding.rule_id in _BROKEN_IMPORT_RULES:
        return 2 if finding.severity == "P3" else 10
    base = _HEALTH_DEDUCTIONS.get(finding.rule_id, 0)
    if finding.rule_id in _FAN_RULES and finding.severity == "P1":
        return base * 2
    return base
def _degree_order(item: tuple[str, int]) -> tuple[int, str]:
    return (-item[1], item[0])
__all__ = [
    'GENERIC_SCRIPT_MODULES',
    'OVERSIZED_THRESHOLD',
    'ApiContractAuditor',
    'ArchitectureRuleAnalyzer',
    'DependencyAnalyzer',
    'auto_suggest_layer_map',
    'build_closures',
    'classify_file_sizes',
    'compare_with_baseline',
    'compute_impact',
    'format_report',
    'layer_map_stats',
    'log_layer_map_result',
    'main',
    'module_name_of',
    'package_name_of',
    'scan_graph',
    'scan_module_fanout',
    'summarize',
]
class DependencyAnalyzer:
    _DYNAMIC_IMPORT_CALLS = frozenset({
        "__import__", "importlib.import_module",
        "importlib.spec_from_loader", "importlib.util.spec_from_loader",
    })
    ENTRY_MODULES = frozenset({"__init__", "__main__"})
    def __init__(self, skill_dir: str,
                 layer_map: dict[str, int] | None = None):
        self.skill_dir = skill_dir
        self._roots = PackageRootResolver(skill_dir)
        self._pkg_roots: set[str] = set()
        self.py_files: list[str] = []
        self.ctx = None
        self._parsed_sources: dict[str, tuple[ast.AST, str]] = {}
        self._graph_built_once = False
        self._integrity_scanned_once = False
        self._prod_files_snapshot: frozenset[str] = frozenset()
        self._lib_exists: dict[tuple[str, str], bool] = {}
        self._scan_py_files()
        self._refresh_module_identities()
        self._pkg_roots = self._roots.resolve(
            [*self._package_init_files, *self.py_files],
            parsed=self._parsed_sources)
        self._main_guard_modules: set[str] = set()
        self._facade_cache: frozenset[str] | None = None
        self._facade_targets_by_init: dict[str, frozenset[str]] = {}
        self._facade_init_paths: dict[str, str] = {}
        self._package_init_consumers: dict[str, set[tuple[str, bool]]] = {}
        self._facade_closures: dict[str, frozenset[str]] = {}
        self.layer_map = (dict(layer_map) if layer_map is not None
                          else target_layer_map(skill_dir))
    def _scan_py_files(self) -> None:
        if not os.path.isdir(self.skill_dir):
            if os.path.exists(self.skill_dir):
                raise NotADirectoryError(
                    f"DependencyAnalyzer 目标路径非目录: {self.skill_dir!r}")
            raise FileNotFoundError(
                f"DependencyAnalyzer 目标目录不存在: {self.skill_dir!r}")
        prod_files = iter_prod_py_files(self.skill_dir)
        self._prod_files_snapshot = frozenset(prod_files)
        self._package_init_files = self._init_files_of(prod_files)
        self.py_files = self._module_files_of(prod_files)
    @staticmethod
    def _init_files_of(prod_files: list[str]) -> list[str]:
        return [fpath for fpath in prod_files
                if os.path.basename(fpath).lower() == '__init__.py']
    def _refresh_module_identities(self) -> None:
        self.py_files = list(dict.fromkeys(self.py_files))
        stems = Counter(os.path.splitext(os.path.basename(p))[0]
                        for p in self.py_files)
        self._module_name_by_path: dict[str, str] = {}
        self._module_targets: dict[str, list[str]] = {}
        for fpath in self.py_files:
            stem = os.path.splitext(os.path.basename(fpath))[0]
            if stems[stem] == 1:
                module_name = stem
            else:
                rel = os.path.relpath(fpath, self.skill_dir)
                module_name = os.path.splitext(rel)[0].replace(os.sep, ".")
            self._module_name_by_path[fpath] = module_name
            self._module_targets.setdefault(stem, []).append(module_name)
        self._module_name_by_normpath: dict[str, str] = {
            os.path.normcase(os.path.abspath(path)): name
            for path, name in self._module_name_by_path.items()
        }
        self._module_names = frozenset(self._module_name_by_path.values())
        self._package_entry_names = frozenset(
            name for name in (
                _package_entry_identity(self.skill_dir, fpath)
                for fpath in self._package_init_files)
            if name)
        self._script_name_entries = frozenset(
            self._module_name_by_path[fpath] for fpath in self.py_files
            if os.path.splitext(os.path.basename(fpath))[0]
            in GENERIC_SCRIPT_MODULES)
    def known_module_surface(self) -> frozenset[str]:
        return self._module_names | self._package_entry_names
    @staticmethod
    def _is_module_file(fname: str, fpath: str) -> bool:
        lower = fname.lower()
        return (lower.endswith(".py") and lower != "__init__.py"
                and os.path.isfile(fpath))
    def _lib_module_exists(self, name: str, base_dir: str | None = None) -> bool:
        root = base_dir if base_dir is not None else self.skill_dir
        key = (root, name)
        cached = self._lib_exists.get(key)
        if cached is None:
            cached = import_target_exists(os.path.join(root, name))
            self._lib_exists[key] = cached
        return cached
    def _top_level_module_path(self, name: str) -> str | None:
        candidates = [
            os.path.join(self.skill_dir, name, '__init__.py'),
            os.path.join(self.skill_dir, name + '.py'),
        ]
        layout = layout_of(self.skill_dir)
        if layout.is_package:
            package_root = os.path.abspath(layout.package_root)
            if os.path.normcase(package_root) == os.path.normcase(
                    os.path.abspath(self.skill_dir)):
                return None
            source_root = os.path.dirname(package_root)
            candidates.extend((
                os.path.join(source_root, name, '__init__.py'),
                os.path.join(source_root, name + '.py'),
            ))
        for path in dict.fromkeys(candidates):
            if not os.path.isfile(path):
                continue
            key = os.path.normcase(os.path.abspath(path))
            if (key in self._module_name_by_normpath
                    or os.path.basename(path).lower() == '__init__.py'):
                return path
        return None
    def _abs_edge_target_ok(self, parts: list[str]) -> bool:
        if not parts or not self._roots.is_importable(parts[0]):
            return False
        if len(parts) < 2:
            return True
        return self._lib_module_exists(
            os.path.join(*parts[1:]), base_dir=self._roots.probe_dir(parts[0]))
    def _resolve_edge_target(self, target: str,
                             target_path: str | None) -> str | None:
        if target_path:
            return self._module_name_by_normpath.get(
                os.path.normcase(os.path.abspath(target_path)))
        if target in self._module_names:
            return target
        candidates = self._module_targets.get(target, ())
        return candidates[0] if len(candidates) == 1 else None
    @staticmethod
    def _init_is_ancestor_of(init_path: str, fpath: str | None) -> bool:
        """包入口是否为导入方的祖先包入口。

        祖先包入口是包内模块的导入发起者，包内模块导入任意目标时对它的回指恒成立
        （根包入口更是所有模块的祖先），计入只会把包内全部多段导入判成对入口触达
        模块的依赖；只有包外模块导入该包入口才是真实的执行期依赖。
        """
        if not fpath:
            return False
        package_dir = os.path.normcase(os.path.dirname(os.path.abspath(init_path)))
        return os.path.normcase(os.path.abspath(fpath)).startswith(
            package_dir + os.sep)
    def _add_package_entry_edges(self, graph: DependencyGraph,
                                 module_name: str, first_dir: str,
                                 parts: list[str], *, fpath: str | None,
                                 implicit: bool = False) -> None:
        """``a.b.c`` 的导入依次执行 a、a.b 的包入口。

        中间包入口登记为门面消费方，由 ``_link_package_facades`` 展开为对入口
        导入期触达模块的依赖边；只记叶子模块会让仅经门面消费的模块入度为 0
        （误报孤儿），经门面回指的循环也不可见。``first_dir`` 是 ``parts[0]``
        对应的目录。
        """
        for index in range(1, len(parts)):
            entry = self._module_file_path(first_dir, parts[1:index])
            if (os.path.basename(entry) != '__init__.py'
                    or self._init_is_ancestor_of(entry, fpath)):
                continue
            self._add_project_edge(
                graph, module_name, parts[index - 1],
                implicit=implicit, target_path=entry)
    def _add_project_edge(self, graph: DependencyGraph, source: str,
                          target: str, *, implicit: bool = False,
                          target_path: str | None = None) -> None:
        resolved = self._resolve_edge_target(target, target_path)
        if target_path and resolved is None:
            if os.path.basename(target_path).lower() == '__init__.py':
                init_key = _package_init_key(target_path)
                self._facade_init_paths.setdefault(init_key, target_path)
                self._package_init_consumers.setdefault(
                    source, set()).add((init_key, implicit))
            return
        linked = target if resolved is None else resolved
        register = resolved is not None
        if implicit:
            graph.add_implicit_edge(source, linked, register_target=register)
        else:
            graph.add_edge(source, linked, register_target=register)
    @staticmethod
    def _module_file_path(base_dir: str, parts: list[str]) -> str:
        module_path = os.path.join(base_dir, *parts)
        package_init = os.path.join(module_path, '__init__.py')
        return package_init if os.path.isfile(package_init) else module_path + '.py'
    @staticmethod
    def _project_edges(graph: DependencyGraph, module: str) -> set[str]:
        return {
            target
            for target in (*graph.edges.get(module, ()),
                           *graph.implicit_edges.get(module, ()))
            if target in graph.nodes
        }
    @classmethod
    def _project_edge_map(
            cls, graph: DependencyGraph) -> dict[str, set[str]]:
        return {module: cls._project_edges(graph, module)
                for module in graph.nodes}
    @classmethod
    def _fan_in_degrees(cls, graph: DependencyGraph) -> dict[str, int]:
        dependents: dict[str, set[str]] = defaultdict(set)
        for source in (*graph.edges, *graph.implicit_edges):
            for target in cls._project_edges(graph, source):
                dependents[target].add(source)
        return {target: len(sources)
                for target, sources in dependents.items()}
    @classmethod
    def _fan_out_degrees(cls, graph: DependencyGraph) -> dict[str, int]:
        fan_out: dict[str, int] = {}
        for module in graph.nodes:
            degree = len(cls._project_edges(graph, module))
            if degree:
                fan_out[module] = degree
        return fan_out
    def _module_files_of(self, prod_files: list[str]) -> list[str]:
        return [fpath for fpath in prod_files
                if self._is_module_file(os.path.basename(fpath), fpath)]
    def _refresh_if_stale(self) -> None:
        if not os.path.isdir(self.skill_dir):
            return
        prod_files = iter_prod_py_files(self.skill_dir)
        if frozenset(prod_files) == self._prod_files_snapshot:
            return
        current = self._module_files_of(prod_files)
        self.py_files = current
        self._package_init_files = self._init_files_of(prod_files)
        self._refresh_module_identities()
        self._parsed_sources.clear()
        self._pkg_roots = self._roots.resolve(
            [*self._package_init_files, *self.py_files],
            parsed=self._parsed_sources)
        self._prod_files_snapshot = frozenset(prod_files)
        self._main_guard_modules = set()
        self._reset_facade_caches()
        self._lib_exists.clear()
    def _entry_exempt_modules(self) -> frozenset[str]:
        return frozenset(self.ENTRY_MODULES
                         | self._script_name_entries
                         | self._main_guard_modules)
    def _reset_facade_caches(self) -> None:
        self._facade_cache = None
        self._facade_targets_by_init.clear()
        self._facade_init_paths.clear()
        self._package_init_consumers.clear()
        self._facade_closures.clear()
    def _facade_imported_modules(self) -> frozenset[str]:
        if self._facade_cache is None:
            self._facade_cache = self._collect_facade_imports()
        return self._facade_cache
    def _collect_facade_imports(self) -> frozenset[str]:
        targets: set[str] = set()
        for fpath in self._package_init_files:
            targets |= self._facade_closure(_package_init_key(fpath), fpath)
        return frozenset(targets)
    def _package_facade_targets(self, init_path: str) -> frozenset[str]:
        """包入口在导入期直接触达的项目模块（嵌套包只记录关系，不在此展开）。"""
        key = _package_init_key(init_path)
        cached = self._facade_targets_by_init.get(key)
        if cached is not None:
            return cached
        self._facade_init_paths[key] = init_path
        evidence = DependencyGraph()
        loaded = self._load_file_tree(init_path)
        if loaded is not None:
            self._add_static_edges(loaded[0], init_path, key, evidence)
            self._detect_implicit_deps(loaded[0], init_path, key, evidence)
        targets = frozenset(
            target
            for edge_map in (evidence.edges, evidence.implicit_edges)
            for edge_targets in edge_map.values()
            for target in edge_targets if target in self._module_names)
        self._facade_targets_by_init[key] = targets
        return targets
    def _facade_closure(self, init_key: str,
                        init_path: str | None = None) -> frozenset[str]:
        """经包入口导入闭包触达的项目模块：本地 visited 一次走完，结果与调用顺序无关。"""
        cached = self._facade_closures.get(init_key)
        if cached is not None:
            return cached
        if init_path is not None:
            self._facade_init_paths.setdefault(init_key, init_path)
        targets: set[str] = set()
        visited: set[str] = set()
        pending = [init_key]
        while pending:
            current = pending.pop()
            if current in visited:
                continue
            visited.add(current)
            targets |= self._package_facade_targets(
                self._facade_init_paths.get(current, current))
            pending.extend(
                nested_key for nested_key, _implicit in
                self._package_init_consumers.get(current, ()))
        result = frozenset(targets)
        self._facade_closures[init_key] = result
        return result
    def _link_package_facades(self, graph: DependencyGraph) -> None:
        """把「导入包入口」解析为对入口导入期触达模块的依赖边。

        ``from pkg import x`` / ``from . import pkg`` 会先执行 ``pkg/__init__.py``，
        后者再导入包内模块；只记模块文件间的直接边会让仅经门面消费的模块
        入度/出度皆为 0（误报完全孤儿），经门面回指的循环也不可见。
        """
        for source, init_keys in list(self._package_init_consumers.items()):
            if source in self._facade_targets_by_init:
                continue
            for init_key, implicit in init_keys:
                for target in self._facade_closure(init_key):
                    if target == source:
                        continue
                    if implicit:
                        graph.add_implicit_edge(source, target)
                    else:
                        graph.add_edge(source, target)
    def build_graph(self) -> DependencyGraph:
        graph = DependencyGraph()
        if self._graph_built_once:
            self._parsed_sources.clear()
            self._pkg_roots = self._roots.resolve(
                [*self._package_init_files, *self.py_files],
                parsed=self._parsed_sources)
        self._graph_built_once = True
        self._refresh_if_stale()
        self._main_guard_modules = set()
        self._reset_facade_caches()
        for fpath in self._package_init_files:
            self._load_file_tree(fpath)
        for fpath in self.py_files:
            module_name = self._module_name_by_path[fpath]
            graph.nodes.add(module_name)
            loaded = self._load_file_tree(fpath)
            if loaded is None:
                continue
            tree = loaded[0]
            if _has_main_guard(tree):
                self._main_guard_modules.add(module_name)
            self._add_static_edges(tree, fpath, module_name, graph)
            self._detect_implicit_deps(tree, fpath, module_name, graph)
        self._link_package_facades(graph)
        self._integrity_scanned_once = False
        return graph
    def _load_file_tree(self, fpath: str) -> tuple[ast.AST, str | None] | None:
        cached = self._parsed_sources.get(fpath)
        if cached is not None:
            return cached
        tree = _ctx_value(self.ctx, 'get_ast', fpath, ast.AST, 'build_graph')
        content = _ctx_value(
            self.ctx, 'get_source', fpath, str, 'build_graph')
        if tree is not None:
            return tree, content
        try:
            content = read_source_auto(fpath)
            tree = compile(content, fpath, "exec", ast.PyCF_ONLY_AST)
        except _LOAD_ERRORS as e:
            logger.warning("[build_graph] 读取/解析 %s 失败，跳过该文件: %s", fpath, e)
            return None
        if content is not None:
            self._parsed_sources[fpath] = (tree, content)
        return tree, content
    def _add_static_edges(self, tree: ast.AST, fpath: str,
                          module_name: str, graph: DependencyGraph) -> None:
        for node in iter_static_edge_nodes(tree):
            self._add_stmt_edges(node, fpath, module_name, graph)
    def _add_stmt_edges(self, node: ast.AST, fpath: str, module_name: str,
                        graph: DependencyGraph) -> None:
        if isinstance(node, ast.Import):
            self._add_import_edges(node, fpath, module_name, graph)
            return
        if not isinstance(node, ast.ImportFrom):
            return
        if node.level > 0:
            self._add_from_relative_edges(fpath, node, module_name, graph)
        elif node.module:
            self._add_from_absolute_edges(node, fpath, module_name, graph)
    def _add_import_edges(self, node: ast.Import, fpath: str,
                          module_name: str, graph: DependencyGraph) -> None:
        for alias in node.names:
            parts = alias.name.split(".")
            if len(parts) == 1:
                if (parts[0] in self._module_targets
                        or self._roots.is_importable(parts[0])):
                    target_path = self._top_level_module_path(parts[0])
                    if target_path is not None:
                        self._add_project_edge(
                            graph, module_name, parts[0], target_path=target_path)
                continue
            if (self._roots.is_importable(parts[0])
                    and self._abs_edge_target_ok(parts)):
                probe_dir = self._roots.probe_dir(parts[0])
                self._add_project_edge(
                    graph, module_name, parts[-1],
                    target_path=self._module_file_path(probe_dir, parts[1:]))
                self._add_package_entry_edges(
                    graph, module_name, probe_dir, parts, fpath=fpath)
    def _add_from_relative_edges(self, fpath: str, node: ast.ImportFrom,
                                 module_name: str,
                                 graph: DependencyGraph) -> None:
        base_path = relative_import_base(fpath, node.level, self.skill_dir)
        if base_path is None:
            return
        base_dir = str(base_path)
        if not node.module:
            self._add_alias_edges(module_name, node.names, base_dir, graph)
            return
        parts = node.module.split(".")
        module_rel = os.path.join(*parts)
        if self._lib_module_exists(module_rel, base_dir=base_dir):
            self._add_project_edge(
                graph, module_name, parts[-1],
                target_path=self._module_file_path(base_dir, parts))
            self._add_package_entry_edges(
                graph, module_name, os.path.join(base_dir, parts[0]), parts,
                fpath=fpath)
            self._add_alias_edges(
                module_name, node.names,
                os.path.join(base_dir, module_rel), graph)
    def _add_from_absolute_edges(self, node: ast.ImportFrom, fpath: str,
                                 module_name: str,
                                 graph: DependencyGraph) -> None:
        parts = node.module.split(".")
        if len(parts) == 1 and parts[0] in self._module_targets:
            target_path = self._top_level_module_path(parts[0])
            if target_path is not None:
                self._add_project_edge(
                    graph, module_name, parts[0], target_path=target_path)
            return
        if not self._roots.is_importable(parts[0]):
            return
        if len(parts) == 1:
            # ``from pkg import x`` 先执行 ``pkg/__init__.py``：目标路径解析为包入口，
            # 由 _link_package_facades 展开为入口导入期触达的模块边。
            package_path = self._top_level_module_path(parts[0])
            if package_path is not None:
                self._add_project_edge(
                    graph, module_name, parts[0], target_path=package_path)
        if len(parts) >= 2:
            if self._abs_edge_target_ok(parts):
                probe_dir = self._roots.probe_dir(parts[0])
                self._add_project_edge(
                    graph, module_name, parts[-1],
                    target_path=self._module_file_path(probe_dir, parts[1:]))
                self._add_package_entry_edges(
                    graph, module_name, probe_dir, parts, fpath=fpath)
                module_rel = os.path.join(*parts[1:])
                self._add_alias_edges(
                    module_name, node.names,
                    os.path.join(probe_dir, module_rel), graph)
            return
        probe_dir = self._roots.probe_dir(parts[0])
        self._add_alias_edges(module_name, node.names, probe_dir, graph)
    def _add_alias_edges(self, module_name: str, aliases: list[ast.alias],
                         base_dir: str, graph: DependencyGraph) -> None:
        for alias in aliases:
            if (alias.name != "*"
                    and self._lib_module_exists(alias.name, base_dir=base_dir)):
                self._add_project_edge(
                    graph, module_name, alias.name,
                    target_path=self._module_file_path(
                        base_dir, alias.name.split(".")))
    @staticmethod
    def _dotted_expression_name(node: ast.AST) -> str:
        parts: list[str] = []
        while isinstance(node, ast.Attribute):
            parts.append(node.attr)
            node = node.value
        if not isinstance(node, ast.Name):
            return ''
        parts.append(node.id)
        return '.'.join(reversed(parts))
    @staticmethod
    def _runtime_name(expression: ast.AST, query: ast.AST,
                      imports: dict, parents: dict) -> tuple[str, str, bool]:
        name = DependencyAnalyzer._dotted_expression_name(expression)
        if not name:
            return '', '', False
        root, *suffix = name.split('.')
        record = resolve_import_binding(imports, parents, query, root)
        if record is None:
            return ((name, root, False) if name == '__import__'
                    else ('', root, True))
        if record[0] == 'import':
            base = record[1]
        elif record[0] == 'from' and record[1]:
            base = f'{record[1]}.{record[2]}'
        else:
            return '', root, True
        canonical = '.'.join([base, *suffix])
        return canonical, root, canonical != name
    @staticmethod
    def _direct_child_under(node: ast.AST, ancestor: ast.AST,
                            parents: dict) -> ast.AST | None:
        child = node
        parent = parents.get(child)
        while parent is not None and parent is not ancestor:
            child = parent
            parent = parents.get(child)
        return child if parent is ancestor else None
    @classmethod
    def _if_branch_at(cls, node: ast.AST, ancestor: ast.If,
                      parents: dict) -> str | None:
        child = cls._direct_child_under(node, ancestor, parents)
        if child is None:
            return None
        if any(child is statement for statement in ancestor.body):
            return 'body'
        if any(child is statement for statement in ancestor.orelse):
            return 'else'
        return None
    @classmethod
    def _binding_cannot_affect_query(cls, node: ast.AST, query: ast.AST,
                                     parents: dict, root: str) -> bool:
        def in_expression(expression: ast.AST) -> bool:
            return (query is expression
                    or cls._direct_child_under(
                        query, expression, parents) is not None)

        if (isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign))
                and node.value is not None and in_expression(node.value)):
            return True
        if (isinstance(node, (ast.For, ast.AsyncFor))
                and in_expression(node.iter)):
            return True
        if (isinstance(node, ast.withitem)
                and in_expression(node.context_expr)):
            return True
        if isinstance(node, (ast.With, ast.AsyncWith)):
            for index, item in enumerate(node.items):
                if not in_expression(item.context_expr):
                    continue
                earlier_binding = any(
                    root in iter_unpack_target_names(earlier.optional_vars)
                    for earlier in node.items[:index]
                    if earlier.optional_vars is not None)
                if not earlier_binding:
                    return True
        ancestor = parents.get(node)
        while ancestor is not None:
            if isinstance(ancestor, ast.If):
                binding_branch = cls._if_branch_at(node, ancestor, parents)
                if binding_branch is not None:
                    if isinstance(ancestor.test, ast.Constant):
                        live_branch = 'body' if bool(ancestor.test.value) else 'else'
                        if binding_branch != live_branch:
                            return True
                    query_branch = cls._if_branch_at(query, ancestor, parents)
                    if (query_branch is not None
                            and query_branch != binding_branch):
                        return True
            ancestor = parents.get(ancestor)
        return False
    @staticmethod
    def _runtime_binding_events(scope: ast.AST, root: str,
                                parents: dict, lexical: Any,
                                query: ast.AST | None = None
                                ) -> list[tuple[tuple[int, int], bool]] | None:
        events: list[tuple[tuple[int, int], bool]] = []
        annotation_events: list[tuple[tuple[int, int], bool]] = []
        for node in walk_nodes(scope):
            if node is scope:
                continue
            owner: ast.AST | None = node
            while owner is not None and owner not in lexical.bound:
                owner = parents.get(owner)
            if owner is not scope:
                continue
            if isinstance(node, (ast.Global, ast.Nonlocal)):
                if root in node.names:
                    return None
                continue
            if isinstance(node, ast.Delete):
                names = {name for target in node.targets
                         for name in iter_unpack_target_names(target)}
            else:
                names = scope_node_bound_names(node)
            pure_annotation = (
                isinstance(node, ast.AnnAssign) and node.value is None
                and isinstance(scope, (ast.FunctionDef,
                                       ast.AsyncFunctionDef))
                and isinstance(node.target, ast.Name))
            if pure_annotation:
                names = {node.target.id}
            if root not in names:
                continue
            if isinstance(node, ast.NamedExpr):
                return None
            if (query is not None
                    and DependencyAnalyzer._binding_cannot_affect_query(
                        node, query, parents, root)):
                continue
            positioned: ast.AST | None = node
            while positioned is not None and not hasattr(positioned, 'lineno'):
                positioned = parents.get(positioned)
            position = (getattr(positioned, 'lineno', 0),
                        getattr(positioned, 'col_offset', 0))
            is_import = isinstance(node, (ast.Import, ast.ImportFrom))
            target_events = annotation_events if pure_annotation else events
            target_events.append((position, is_import))
        return events or annotation_events
    @staticmethod
    def _runtime_root_shadowed(query: ast.AST, root: str,
                               parents: dict, lexical: Any,
                               imports: dict) -> bool:
        scope: ast.AST | None = query
        while scope is not None and scope not in lexical.bound:
            scope = parents.get(scope)
        if scope is None:
            return False
        ordered_scopes = (ast.Module, ast.ClassDef, ast.FunctionDef,
                          ast.AsyncFunctionDef, ast.Lambda)
        if not isinstance(scope, ordered_scopes):
            return scope_shadows_import(lexical, scope, root)
        events = DependencyAnalyzer._runtime_binding_events(
            scope, root, parents, lexical, query)
        if not events:
            return scope_shadows_import(lexical, scope, root)
        position = (getattr(query, 'lineno', 0),
                    getattr(query, 'col_offset', 0))
        prior = [event for event in events if event[0] <= position]
        if prior:
            return not max(prior)[1]
        if isinstance(scope, ast.Module):
            return root != '__import__'
        if isinstance(scope, ast.ClassDef):
            outer = lexical.parent.get(scope)
            if (outer is not None
                    and scope_shadows_import(lexical, outer, root)):
                return True
            outer_import = resolve_import_binding(
                imports, parents, scope, root)
            return outer_import is None and root != '__import__'
        return True
    @staticmethod
    def _static_string(node: ast.AST) -> str | None:
        return (node.value if isinstance(node, ast.Constant)
                and isinstance(node.value, str) else None)
    @classmethod
    def _dynamic_call_literal(cls, node: ast.Call) -> str | None:
        for keyword in node.keywords:
            if keyword.arg == 'name':
                return cls._static_string(keyword.value)
        if not node.args or isinstance(node.args[0], ast.Starred):
            return None
        return cls._static_string(node.args[0])
    @staticmethod
    def _importlib_uses_current_package(node: ast.Call) -> bool:
        anchor = node.args[1] if len(node.args) > 1 else None
        if anchor is None:
            anchor = next((keyword.value for keyword in node.keywords
                           if keyword.arg == 'package'), None)
        return isinstance(anchor, ast.Name) and anchor.id == '__package__'
    @staticmethod
    def _dunder_import_level(node: ast.Call) -> int | None:
        level_node = node.args[4] if len(node.args) > 4 else next(
            (keyword.value for keyword in node.keywords
             if keyword.arg == 'level'), None)
        if level_node is None:
            return 0
        if (not isinstance(level_node, ast.Constant)
                or type(level_node.value) is not int
                or level_node.value < 0):
            return None
        return level_node.value
    @classmethod
    def _dynamic_relative_level(cls, node: ast.Call, call_name: str,
                                literal: str) -> int | None:
        if call_name == 'importlib.import_module':
            level = len(literal) - len(literal.lstrip('.'))
            if level and not cls._importlib_uses_current_package(node):
                return None
            return level
        if call_name == '__import__':
            if literal.startswith('.'):
                return None
            return cls._dunder_import_level(node)
        return None if literal.startswith('.') else 0
    def _detect_implicit_deps(self, tree: ast.AST, fpath: str,
                              module_name: str,
                              graph: DependencyGraph) -> None:
        imports = scope_import_tables(tree)
        parents = parent_map(tree)
        lexical = None
        for node in iter_static_edge_nodes(tree):
            if isinstance(node, ast.Call):
                call_name, root, _ = self._runtime_name(
                    node.func, node, imports, parents)
                if call_name not in self._DYNAMIC_IMPORT_CALLS:
                    continue
                if lexical is None:
                    lexical = collect_lexical_scope_table(tree)
                if self._runtime_root_shadowed(
                        node, root, parents, lexical, imports):
                    continue
                literal = self._dynamic_call_literal(node)
                if literal is None:
                    continue
                relative_level = self._dynamic_relative_level(
                    node, call_name, literal)
                if relative_level is None:
                    continue
                self._add_implicit_edge_from_literal(
                    module_name, graph, literal, fpath=fpath,
                    relative_level=relative_level)
            elif isinstance(node, ast.Subscript):
                container, root, _ = self._runtime_name(
                    node.value, node, imports, parents)
                if container != 'sys.modules':
                    continue
                if lexical is None:
                    lexical = collect_lexical_scope_table(tree)
                if self._runtime_root_shadowed(
                        node, root, parents, lexical, imports):
                    continue
                literal = self._static_string(node.slice)
                if literal is not None:
                    self._add_implicit_edge_from_literal(
                        module_name, graph, literal, fpath=fpath)
    def _add_relative_implicit_edge(
            self, fpath: str, module_name: str, graph: DependencyGraph,
            literal: str, relative_level: int) -> None:
        q_parts = literal.lstrip('.').split('.')
        if not all(p.isidentifier() for p in q_parts):
            return
        base_path = relative_import_base(fpath, relative_level, self.skill_dir)
        if base_path is None:
            return
        base_dir = str(base_path)
        module_rel = os.path.join(*q_parts)
        if self._lib_module_exists(module_rel, base_dir=base_dir):
            self._add_project_edge(
                graph, module_name, q_parts[-1], implicit=True,
                target_path=self._module_file_path(base_dir, q_parts))
            self._add_package_entry_edges(
                graph, module_name, os.path.join(base_dir, q_parts[0]),
                q_parts, fpath=fpath, implicit=True)
    def _add_implicit_edge_from_literal(
            self, module_name: str, graph: DependencyGraph,
            literal: str, *, fpath: str | None = None,
            relative_level: int = 0) -> None:
        if relative_level:
            if fpath is not None:
                self._add_relative_implicit_edge(
                    fpath, module_name, graph, literal, relative_level)
            return
        q_parts = literal.split(".")
        if not all(p.isidentifier() for p in q_parts):
            return
        if (len(q_parts) >= 2 and self._roots.is_importable(q_parts[0])
                and self._abs_edge_target_ok(q_parts)):
            probe_dir = self._roots.probe_dir(q_parts[0])
            self._add_project_edge(
                graph, module_name, q_parts[-1], implicit=True,
                target_path=self._module_file_path(probe_dir, q_parts[1:]))
            self._add_package_entry_edges(
                graph, module_name, probe_dir, q_parts, fpath=fpath,
                implicit=True)
        elif q_parts[0] in self._module_targets:
            target_path = self._top_level_module_path(q_parts[0])
            if target_path is not None:
                self._add_project_edge(
                    graph, module_name, q_parts[0], implicit=True,
                    target_path=target_path)
    @staticmethod
    def _layer_label(layer: int) -> str:
        return f"L{layer}" if layer >= 0 else "未登记层"
    @staticmethod
    def _fan_in_finding(module: str, degree: int, threshold: float,
                        severity: str) -> Finding:
        return Finding(
            rule_id="D9-HIGH-FANIN",
            severity=severity,
            message=(f"高扇入模块: {module} (入度={degree}, "
                     f"分层阈值={threshold:.1f})"),
            detail=(f"被 {degree} 个模块依赖，超过本层告警线 {threshold:.1f}；"
                    "治理优先级：先确认是否属稳定底座契约，"
                    "再按 converge_dependency 收敛消费方或提取稳定接口"),
        )
    @staticmethod
    def _fan_out_finding(module: str, degree: int, threshold: float,
                         severity: str) -> Finding:
        return Finding(
            rule_id="D9-HIGH-FANOUT",
            severity=severity,
            message=(f"高扇出模块: {module} (出度={degree}, "
                     f"分层阈值={threshold:.1f})"),
            detail=(f"依赖 {degree} 个模块，超过本层告警线 {threshold:.1f}；"
                    "治理优先级：先收敛向上依赖（职责下沉到既有底座），"
                    "再经包统一出入口消费，最后才评估迁移"),
        )
    @staticmethod
    def _fan_severity(degree: int, threshold: float, upward: int) -> str:
        return "P1" if upward else fan_severity(degree, threshold)
    def _high_degree_findings(
            self, degrees: dict[str, int],
            thresholds: dict[int, float],
            finding_factory: Callable[[str, int, float, str], Finding],
            skip_modules: frozenset[str] = frozenset(),
            breakdown: dict[str, dict] | None = None) -> list[Finding]:
        findings: list[Finding] = []
        for module, degree in sorted(degrees.items(), key=_degree_order):
            if module in skip_modules:
                continue
            threshold = thresholds.get(self.layer_map.get(module, -1))
            if threshold is None or degree <= threshold:
                continue
            info = (breakdown or {}).get(module) or {}
            severity = self._fan_severity(
                degree, threshold, info.get("upward", 0))
            findings.append(finding_factory(module, degree, threshold, severity))
        return findings
    def _fan_out_breakdown(self, fan_out: dict[str, int],
                            thresholds: dict[int, float],
                            graph: DependencyGraph) -> dict[str, dict]:
        breakdown: dict[str, dict] = {}
        for module, degree in sorted(fan_out.items(), key=_degree_order):
            own_layer = self.layer_map.get(module, -1)
            threshold = thresholds.get(own_layer)
            if own_layer < 0 or threshold is None or degree <= threshold:
                continue
            by_layer: Counter[int] = Counter(
                self.layer_map.get(dep, -1)
                for dep in self._project_edges(graph, module))
            upward = sum(v for k, v in by_layer.items() if k > own_layer)
            breakdown[module] = {
                "degree": degree,
                "threshold": round(threshold, 1),
                "severity": self._fan_severity(degree, threshold, upward),
                "own_layer": own_layer,
                "by_layer": {self._layer_label(k): v
                             for k, v in sorted(by_layer.items())},
                "upward": upward,
                "same_layer": by_layer.get(own_layer, 0),
                "downward": sum(v for k, v in by_layer.items()
                                if 0 <= k < own_layer),
                "unregistered": by_layer.get(-1, 0),
                "governance_method": "converge_dependency",
            }
        return breakdown
    def fan_analysis(self, graph: DependencyGraph) -> tuple[list[Finding], dict]:
        fan_in = self._fan_in_degrees(graph)
        fan_out = self._fan_out_degrees(graph)
        in_thresholds = resolve_layer_fan_thresholds(
            fan_in, self.layer_map, kind="in")
        out_thresholds = resolve_layer_fan_thresholds(
            fan_out, self.layer_map)
        out_breakdown = self._fan_out_breakdown(fan_out, out_thresholds, graph)
        findings = self._high_degree_findings(
            fan_in, in_thresholds, self._fan_in_finding)
        findings.extend(self._high_degree_findings(
            fan_out, out_thresholds, self._fan_out_finding,
            skip_modules=self._entry_exempt_modules(),
            breakdown=out_breakdown))
        fi_mean, fi_std = mean_std(list(fan_in.values()))
        fo_mean, fo_std = mean_std(list(fan_out.values()))
        raw = {
            "fan_in": dict(sorted(fan_in.items(), key=_degree_order)[:20]),
            "fan_out": dict(sorted(fan_out.items(), key=_degree_order)[:20]),
            "fi_mean": round(fi_mean, 1),
            "fi_std": round(fi_std, 1),
            "fi_threshold": round(resolve_global_fan_threshold(
                fan_in, kind="in"), 1),
            "fi_thresholds": {str(k): round(v, 1)
                              for k, v in sorted(in_thresholds.items())},
            "fo_mean": round(fo_mean, 1),
            "fo_std": round(fo_std, 1),
            "fo_threshold": round(resolve_global_fan_threshold(fan_out), 1),
            "fo_thresholds": {str(k): round(v, 1)
                              for k, v in sorted(out_thresholds.items())},
            "fan_out_breakdown": out_breakdown,
        }
        return findings, raw
    def _collect_layer_violations(self, edge_map: dict, rule_id: str,
                                  msg_prefix: str, verb: str,
                                  detail: str) -> list[Finding]:
        findings: list[Finding] = []
        for source, targets in edge_map.items():
            src_layer = self.layer_map.get(source)
            if src_layer is None:
                continue
            for target in sorted(targets):
                tgt_layer = self.layer_map.get(target)
                if tgt_layer is None:
                    continue
                if src_layer < tgt_layer:
                    findings.append(Finding(
                        rule_id=rule_id,
                        severity="P1",
                        message=f"{msg_prefix}: {source}(L{src_layer}) "
                                f"{verb}依赖 {target}(L{tgt_layer})",
                        detail=detail,
                    ))
        return findings
    def layer_violations(self, graph: DependencyGraph) -> list[Finding]:
        findings = self._collect_layer_violations(
            graph.edges, "D9-LAYER", "分层违规", "",
            "下层模块不应依赖上层模块")
        findings.extend(self._collect_layer_violations(
            graph.implicit_edges, "D9-LAYER-IMPLICIT",
            "隐式分层违规", "隐式", "下层模块通过隐式机制依赖上层模块"))
        return findings
    def _hub_is_reasonable(self, module: str, layer: int,
                           module_fan_out: dict[str, int]) -> bool:
        if self.layer_map:
            return layer in (0, 1)
        return module_fan_out.get(module, 0) <= _HUB_STABLE_MAX_FANOUT
    def hub_detection(self, graph: DependencyGraph) -> tuple[list[Finding], list[dict]]:
        findings: list[Finding] = []
        hubs: list[dict] = []
        fan_in = self._fan_in_degrees(graph)
        fan_out = self._fan_out_degrees(graph)
        fi_mean, fi_std = mean_std(list(fan_in.values()))
        hub_threshold = fi_mean + 2 * fi_std
        for module, degree in sorted(fan_in.items(), key=_degree_order):
            if degree > max(20, hub_threshold):
                layer = self.layer_map.get(module, -1)
                is_reasonable = self._hub_is_reasonable(
                    module, layer, fan_out)
                hubs.append({
                    "name": module,
                    "fan_in": degree,
                    "layer": layer,
                    "is_reasonable": is_reasonable,
                })
                if not is_reasonable:
                    findings.append(Finding(
                        rule_id="D9-HUB",
                        severity="P2",
                        message=(f"不合理 Hub 模块: {module}"
                                 f"({self._layer_label(layer)}, 入度={degree})"),
                        detail=("非底座模块（L2+）被大量其他模块依赖：改为经包统一出入口消费、"
                                "或把职责下沉到既有底座模块（结构调整须先过变更论证）"
                                if layer >= 0 else
                                f"模块未登记分层：自身依赖 {fan_out.get(module, 0)} "
                                "个项目内模块，属耦合枢纽而非稳定底座；先收敛消费方、"
                                "把职责下沉到既有底座，或显式为项目声明权威分层表"),
                    ))
        return findings, hubs
    def orphan_detection(self, graph: DependencyGraph) -> tuple[list[Finding], list[dict]]:
        findings: list[Finding] = []
        orphans: list[dict] = []
        fan_in = self._fan_in_degrees(graph)
        fan_out = self._fan_out_degrees(graph)
        exempt = self._entry_exempt_modules() | self._facade_imported_modules()
        for module in sorted(graph.nodes):
            if module in exempt:
                continue
            record, finding = self._orphan_record(
                module, fan_in.get(module, 0), fan_out.get(module, 0))
            if record is not None:
                orphans.append(record)
                findings.append(finding)
        return findings, orphans
    def _orphan_record(self, module: str, fan_in_degree: int, fan_out_degree: int
                       ) -> tuple[dict | None, Finding | None]:
        layer = self.layer_map.get(module, -1)
        if fan_in_degree == 0 and fan_out_degree == 0:
            return (
                {"name": module, "type": "full_orphan", "layer": layer},
                Finding(
                    rule_id="D9-ORPHAN-FULL",
                    severity="P2",
                    message=(f"完全孤儿模块: {module}"
                             f"({self._layer_label(layer)})"),
                    detail="模块不被任何模块依赖，也不依赖任何模块，可能已废弃",
                ),
            )
        if fan_in_degree == 0 and fan_out_degree > 0:
            return (
                {"name": module, "type": "semi_orphan", "layer": layer,
                 "fan_out": fan_out_degree},
                Finding(
                    rule_id="D9-ORPHAN-SEMI",
                    severity="P3",
                    message=(f"半孤儿模块: {module}"
                             f"({self._layer_label(layer)}, "
                             f"出度={fan_out_degree})"),
                    detail=(f"模块不被任何其他模块依赖，但自身依赖 "
                            f"{fan_out_degree} 个模块"),
                ),
            )
        return None, None
    def critical_path(self, graph: DependencyGraph) -> dict:
        length, chain = longest_chain(self._project_edge_map(graph))
        return {
            "nodes": chain,
            "length": length,
            "description": " → ".join(chain),
        }
    def cycle_detection(self, graph: DependencyGraph) -> tuple[list[Finding], list[dict]]:
        findings: list[Finding] = []
        cycles: list[dict] = []
        for modules in cycle_member_groups(
                self._project_edge_map(graph), set(graph.nodes)):
            cycles.append({"modules": modules, "size": len(modules)})
            if len(modules) > 1:
                findings.append(Finding(
                    rule_id="D9-CYCLE",
                    severity="P1",
                    message=f"循环依赖: {len(modules)} 个模块成环",
                    detail=f"环内模块: {', '.join(modules)}",
                ))
                continue
            module = modules[0]
            findings.append(Finding(
                rule_id="D9-CYCLE",
                severity="P1",
                message="循环依赖: 1 个模块自环",
                detail=f"环内模块: {module}（模块导入自身，应删除自引用导入）",
            ))
        return findings, cycles
    def health_score(self, findings: list[Finding]) -> int:
        score = 100
        for finding in findings:
            score -= _health_deduction(finding)
        return max(0, min(100, score))
    def import_integrity_findings(self) -> list[Finding]:
        if self._integrity_scanned_once:
            self._parsed_sources.clear()
        self._refresh_if_stale()
        if self._integrity_scanned_once:
            self._pkg_roots = self._roots.resolve(
                [*self._package_init_files, *self.py_files],
                parsed=self._parsed_sources)
        self._integrity_scanned_once = True
        self._graph_built_once = True
        cache = (self.ctx if self.ctx is not None
                 else _ParsedSourceCache(self._parsed_sources))
        return import_chain_findings(
            self.skill_dir, self.py_files, self._pkg_roots, cache,
            parsed=self._parsed_sources)
    def _collect_d9_findings(self, graph: DependencyGraph) -> tuple[list[Finding], dict]:
        all_findings: list[Finding] = []
        fan_findings, fan_raw = self.fan_analysis(graph)
        all_findings.extend(fan_findings)
        layer_findings = self.layer_violations(graph)
        all_findings.extend(layer_findings)
        hub_findings, hubs = self.hub_detection(graph)
        all_findings.extend(hub_findings)
        orphan_findings, orphans = self.orphan_detection(graph)
        all_findings.extend(orphan_findings)
        cpath = self.critical_path(graph)
        cycle_findings, cycles = self.cycle_detection(graph)
        all_findings.extend(cycle_findings)
        import_findings = self.import_integrity_findings()
        all_findings.extend(import_findings)
        ctx = {
            "fan_raw": fan_raw,
            "hubs": hubs,
            "orphans": orphans,
            "cpath": cpath,
            "cycles": cycles,
            "layer_findings_count": len(layer_findings),
        }
        return all_findings, ctx
    def full_analysis(self, graph: DependencyGraph | None = None) -> dict:
        if graph is None:
            graph = self.build_graph()
        all_findings, d9 = self._collect_d9_findings(graph)
        score = self.health_score(all_findings)
        result = self._build_result(graph, all_findings, d9, score)
        self._log_result(result, all_findings)
        return result
    def _build_result(self, graph: DependencyGraph, all_findings: list[Finding],
                      d9: dict, score: int) -> dict:
        severity_counts = Counter(f.severity for f in all_findings)
        rule_counts = Counter(f.rule_id for f in all_findings)
        result = {
            "status": "warn" if all_findings else "pass",
            "findings_count": len(all_findings),
            "findings": [f.to_dict() for f in all_findings],
            "summary": (
                f"模块依赖分析: {len(graph.nodes)}模块, {graph.total_edges}依赖边, "
                f"{len(d9['cycles'])}环, 健康度{score}/100"
            ),
            "payload": {
                "graph": graph.summary(),
                "fan_analysis": d9["fan_raw"],
                "hubs": d9["hubs"],
                "orphans": d9["orphans"],
                "critical_path": d9["cpath"],
                "cycles": d9["cycles"],
                "layer_violations_count": d9["layer_findings_count"],
                "health_score": score,
                "severity_summary": dict(severity_counts),
                "rule_summary": dict(rule_counts),
            },
        }
        result["ai_execution"] = self._execution_guidance()
        return result
    def _execution_guidance(self) -> dict:
        return {
            "next_action": "review_and_fix_dependency_findings",
            "instruction": (
                "逐项审核 findings（循环依赖/分层违规/断链导入/孤儿模块/高扇出）；"
                "审核通过后按 detail 建议收敛依赖方向（职责下沉到既有底座模块/"
                "改为经包统一出入口消费/消除重复边）；结构性调整（拆分/合并）"
                "由项目自身策略决定，须先过变更论证——本分析器只提供依赖方向证据，"
                "不向目标项目强加拆分禁令，"
                "随后调用 "
                f"{type(self).__module__}.{type(self).__name__}"
                f"({self.skill_dir!r})"
                ".full_analysis() 复扫，直至 findings_count 归零或降级至可接受"
            ),
            "fan_governance_order": [
                "P0 分层倒置扇出：下层依赖上层（D9-LAYER/D9-LAYER-IMPLICIT），先修正方向",
                "P1 严重超限：degree >= 分层阈值 × 1.5，按 fan_out_breakdown.upward 优先收敛",
                "P2 高扇出/高扇入：degree >= 分层阈值，用 converge_dependency 收敛到既有底座",
                "P3 观察项：仅记录基线，不产治疗项",
            ],
            "governance_method": "converge_dependency",
        }
    @staticmethod
    def _log_result(result: dict, all_findings: list[Finding]) -> None:
        if not all_findings:
            logger.info("[DependencyAnalyzer] full_analysis 零检出: %s",
                        result["summary"])
            return
        logger.warning(
            "[DependencyAnalyzer] full_analysis 检出 %d 项: sev=%s rules=%s | %s",
            len(all_findings), result["payload"]["severity_summary"],
            result["payload"]["rule_summary"], result["summary"],
        )
def layer_map_stats(graph, current_map: dict,
                     suggestions: list[dict]) -> dict:
    mapped = sum(1 for m in graph.nodes if m in current_map)
    actions = [s["action"] for s in suggestions]
    return {
        "total_modules": len(graph.nodes),
        "mapped": mapped,
        "unmapped": len(graph.nodes) - mapped,
        "suggestions": {
            "add": actions.count("add"),
            "update": actions.count("update"),
            "remove": actions.count("remove"),
        },
    }
def log_layer_map_result(result: dict, skill_dir: str,
                          dry_run: bool) -> None:
    actions = result["stats"]["suggestions"]
    if dry_run:
        phase = "dry_run 分析"
    elif result["applied"]:
        phase = "建议已写回生效"
    elif not result.get("writeback_surface", True):
        phase = "目标无权威层表，仅产建议"
    else:
        phase = "建议写回失败"
    logger.info(
        "[auto_suggest_layer_map] %s: add=%d update=%d remove=%d | %s",
        phase, actions["add"], actions["update"], actions["remove"], skill_dir)
def auto_suggest_layer_map(skill_dir: str, dry_run: bool = True) -> dict:
    analyzer = DependencyAnalyzer(skill_dir)
    graph = analyzer.build_graph()
    current_map = dict(analyzer.layer_map)
    registry_host = is_registry_host(skill_dir)
    writeback_surface = has_layer_registry_surface(skill_dir)
    excluded_modules = (_layer_registry.UNREGISTERED_BY_DESIGN
                        if registry_host else frozenset())
    inferred, alt_layers = _layer_registry.infer_layer_map(
        graph, current_map, excluded_modules)
    suggestions = _layer_registry.build_layer_suggestions(
        graph, current_map, inferred, alt_layers,
        registry_host or writeback_surface, excluded_modules,
        known_modules=analyzer.known_module_surface())
    result = {
        "suggestions": suggestions,
        "stats": layer_map_stats(graph, current_map, suggestions),
        "applied": apply_layer_suggestions(suggestions, skill_dir, dry_run),
        "writeback_surface": writeback_surface,
    }
    log_layer_map_result(result, skill_dir, dry_run)
    return result
_RATIO_TOLERANCE = 0.03
_COUNT_TOLERANCE = 0.05
def _package_scan_root(skill_dir: str) -> tuple[str, str]:
    project_root = os.path.abspath(skill_dir)
    layout = layout_of(project_root)
    if not layout.is_package:
        return project_root, import_key(os.path.basename(project_root))
    package_root = os.path.abspath(layout.package_root)
    source_root = (project_root if os.path.dirname(package_root) == project_root
                   else package_root)
    return source_root, import_key(layout.package_name)
def _relative_scan_path(path: str, skill_dir: str, source_root: str) -> str:
    for root in (source_root, skill_dir):
        try:
            rel = os.path.relpath(path, root)
        except ValueError:
            continue
        if (os.path.isabs(rel) or rel == os.pardir
                or rel.startswith(os.pardir + os.sep)):
            continue
        return rel
    return path
def _module_name_from_rel(rel: str, root_package: str) -> str:
    parts = rel.split(os.sep)
    if parts[-1].lower() == '__init__.py':
        return root_package if len(parts) == 1 else '.'.join(parts[:-1])
    if not parts[-1].lower().endswith('.py'):
        return ''
    return os.path.splitext(rel)[0].replace(os.sep, '.')
def _path_within_root(path: str, root: str) -> bool:
    if not root:
        return False
    real_root = os.path.realpath(root)
    try:
        common = os.path.commonpath(
            (os.path.realpath(os.path.abspath(path)), real_root))
    except (OSError, ValueError):
        return False
    return os.path.normcase(common) == os.path.normcase(real_root)
def _scan_module_name(path: str, skill_dir: str, source_root: str,
                      root_package: str, package_root: str) -> str:
    rel = _relative_scan_path(path, skill_dir, source_root)
    name = _module_name_from_rel(rel, root_package)
    if (not name or name == root_package
            or name.startswith(root_package + '.')
            or not _path_within_root(path, package_root)):
        return name
    external_base = os.path.join(skill_dir, *name.split('.'))
    current = os.path.normcase(os.path.abspath(path))
    for candidate in (external_base + '.py',
                      os.path.join(external_base, '__init__.py')):
        if (os.path.normcase(os.path.abspath(candidate)) != current
                and os.path.isfile(candidate)):
            return f'{root_package}.{name}'
    return name
def package_name_of(skill_dir: str) -> str:
    if not skill_dir:
        return ''
    return _package_scan_root(os.path.abspath(skill_dir))[1]
def module_name_of(file_path: Any, skill_dir: str = '') -> str:
    if not skill_dir:
        return ''
    try:
        text = os.fspath(file_path or '')
    except TypeError:  # jwsgj:silent-ok
        return ''
    if not isinstance(text, str) or not text.strip():
        return ''
    skill_root = os.path.abspath(skill_dir)
    source_root, root_package = _package_scan_root(skill_root)
    path = text.strip()
    if not os.path.isabs(path):
        path = os.path.join(skill_root, path)
    rel = _relative_scan_path(path, skill_root, source_root)
    if (os.path.isabs(rel) or rel == os.pardir
            or rel.startswith(os.pardir + os.sep)):
        return ''
    layout = layout_of(skill_root)
    package_root = (os.path.abspath(layout.package_root)
                    if layout.is_package else '')
    return _scan_module_name(
        path, skill_root, source_root, root_package, package_root)
def _scan_module_paths(skill_dir: str, roots: tuple[str, str] | None = None,
                       ) -> dict[str, str]:
    os.listdir(skill_dir)
    module_paths: dict[str, str] = {}
    source_root, root_package = roots or _package_scan_root(skill_dir)
    layout = layout_of(skill_dir)
    package_root = (os.path.abspath(layout.package_root)
                    if layout.is_package else '')
    for path in sorted(iter_prod_py_files(skill_dir)):
        rel = _relative_scan_path(path, skill_dir, source_root)
        parts = rel.split(os.sep)
        is_pkg_entry = parts[-1].lower() == '__init__.py'
        name = _scan_module_name(
            path, skill_dir, source_root, root_package, package_root)
        if is_pkg_entry or name not in module_paths:
            module_paths[name] = path
    return module_paths
def _package_initializer_dependencies(
        module_paths: dict[str, str]) -> dict[str, tuple[str, ...]]:
    init_names = {
        os.path.normcase(os.path.abspath(path)): name
        for name, path in module_paths.items()
        if os.path.basename(path).lower() == '__init__.py'
    }
    dependencies: dict[str, tuple[str, ...]] = {}
    for name, path in module_paths.items():
        current = os.path.dirname(os.path.abspath(path))
        parents: list[str] = []
        while True:
            init_path = os.path.normcase(
                os.path.join(current, '__init__.py'))
            parent_name = init_names.get(init_path)
            if parent_name is not None and parent_name != name:
                parents.append(parent_name)
            parent = os.path.dirname(current)
            if parent == current:
                break
            current = parent
        dependencies[name] = tuple(dict.fromkeys(parents))
    return dependencies
def _strip_scan_root_package(module: str, root_package: str) -> str:
    if module == root_package:
        return ''
    prefix = root_package + '.'
    return module.removeprefix(prefix)
def _emit_absolute_import(node: ast.Import, root_package: str,
                          script_prefix: str,
                          add: Callable[[str], bool],
                          add_package: Callable[[str], bool]) -> None:
    for alias in node.names:
        absolute = alias.name
        stripped = _strip_scan_root_package(absolute, root_package)
        if absolute == root_package or absolute.startswith(root_package + '.'):
            if not add_package(absolute) and stripped != absolute:
                add_package(stripped)
        else:
            add(absolute)
        if '.' not in absolute and script_prefix:
            add(f'{script_prefix}.{absolute}')
def _emit_relative_import(node: ast.ImportFrom, pkg_segs: list[str],
                          root_package: str,
                          add: Callable[[str], bool]) -> None:
    keep = len(pkg_segs) - (node.level - 1)
    if (keep < 0 or (keep == 0 and pkg_segs
                     and pkg_segs[0] == root_package)):
        return
    def add_relative(candidate: str) -> bool:
        if not candidate:
            return add(root_package)
        qualified = (candidate if candidate == root_package
                     or candidate.startswith(root_package + '.')
                     else f'{root_package}.{candidate}')
        return add(qualified) or (qualified != candidate and add(candidate))
    base = pkg_segs[:keep]
    if node.module:
        module = '.'.join([*base, node.module])
        add_relative(module)
        for alias in node.names:
            if alias.name != '*':
                add_relative(f'{module}.{alias.name}' if module else alias.name)
        return
    for alias in node.names:
        if alias.name != '*':
            add_relative('.'.join([*base, alias.name]))
    if any(alias.name == '*' for alias in node.names):
        add_relative('.'.join(base))
def _emit_from_import(node: ast.ImportFrom, root_package: str,
                      script_prefix: str,
                      add: Callable[[str], bool],
                      add_package: Callable[[str], bool]) -> None:
    absolute_module = node.module or ''
    stripped_module = _strip_scan_root_package(
        absolute_module, root_package)
    def add_absolute(absolute: str, stripped: str) -> None:
        if absolute == root_package or absolute.startswith(root_package + '.'):
            if absolute and add_package(absolute):
                return
            if stripped and stripped != absolute:
                add_package(stripped)
        elif absolute:
            add(absolute)
    add_absolute(absolute_module, stripped_module)
    for alias in node.names:
        if alias.name == '*':
            continue
        absolute = (f'{absolute_module}.{alias.name}'
                    if absolute_module else alias.name)
        stripped = (f'{stripped_module}.{alias.name}'
                    if stripped_module else alias.name)
        add_absolute(absolute, stripped)
    if stripped_module and '.' not in stripped_module and script_prefix:
        add(f'{script_prefix}.{stripped_module}')
def _scan_import_targets(node: ast.AST, pkg_segs: list[str],
                         known: set[str], root_package: str,
                         script_prefix: str,
                         package_aliases: set[str]) -> list[str]:
    targets: list[str] = []
    seen: set[str] = set()
    def add(candidate: str) -> bool:
        if candidate not in known:
            return False
        if candidate not in seen:
            seen.add(candidate)
            targets.append(candidate)
        return True
    def add_external(candidate: str) -> bool:
        if candidate in package_aliases:
            return False
        return add(candidate)
    if isinstance(node, ast.Import):
        _emit_absolute_import(
            node, root_package, script_prefix, add_external, add)
    elif node.level:
        _emit_relative_import(node, pkg_segs, root_package, add)
    else:
        _emit_from_import(
            node, root_package, script_prefix, add_external, add)
    return targets
def _module_level_import_ids(tree: ast.Module) -> set[int]:
    return {id(node) for node in iter_module_level_imports_tc(tree)}
def _scan_module_scope(path: str, skill_dir: str, source_root: str,
                       ) -> tuple[list[str], str]:
    rel_dir = os.path.dirname(_relative_scan_path(path, skill_dir, source_root))
    pkg_segs = rel_dir.split(os.sep) if rel_dir else []
    if not pkg_segs:
        return pkg_segs, ''
    if os.path.isfile(os.path.join(os.path.dirname(path), '__init__.py')):
        return pkg_segs, ''
    return pkg_segs, '.'.join(pkg_segs)
def _record_scan_edge(graph: dict[str, set[str]],
                      edges: dict[tuple[str, str], dict[str, Any]],
                      name: str, target: str, symbols: set[str],
                      lazy: bool) -> None:
    if target == name:
        return
    graph[name].add(target)
    entry = edges.setdefault((name, target),
                             {'symbols': set(), 'lazy': 0, 'total': 0})
    entry['symbols'].update(symbols)
    entry['total'] += 1
    if lazy:
        entry['lazy'] += 1
def _collect_module_edges(
        name: str, path: str, skill_dir: str, source_root: str,
        known: set[str], root_package: str,
        package_dependencies: dict[str, tuple[str, ...]],
        package_aliases: set[str],
        graph: dict[str, set[str]],
        edges: dict[tuple[str, str], dict[str, Any]]) -> None:
    pkg_segs, script_prefix = _scan_module_scope(
        path, skill_dir, source_root)
    try:
        tree = ast.parse(read_source_auto(path))
    except _LOAD_ERRORS as exc:
        log_swallowed(__name__, exc, context='scan_graph:读源/解析')
        return
    import_time = _module_level_import_ids(tree)
    # 导入方自身所在的祖先包入口（含根包）是其导入发起者，对它们的回指恒成立：
    # 计入会让包内每个模块都依赖根包，正常包被统计成环、扇出与闭包统一偏大。
    own_packages = frozenset(package_dependencies.get(name, ()))
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        lazy = id(node) not in import_time
        statement_symbols: dict[str, set[str]] = {}
        if isinstance(node, ast.ImportFrom):
            imports = [
                (ast.copy_location(ast.ImportFrom(
                    module=node.module, names=[alias], level=node.level), node),
                 set() if alias.name == '*' else {alias.name})
                for alias in node.names
            ]
        else:
            imports = [(node, {_MODULE_IMPORT_SYMBOL})]
        for import_node, symbols in imports:
            targets = _scan_import_targets(
                import_node, pkg_segs, known, root_package, script_prefix,
                package_aliases)
            for target in targets:
                dependencies = (target, *package_dependencies.get(target, ()))
                for dependency in dependencies:
                    if dependency in own_packages:
                        continue
                    statement_symbols.setdefault(
                        dependency, set()).update(symbols)
        for target, symbols in statement_symbols.items():
            _record_scan_edge(
                graph, edges, name, target, symbols, lazy)
OVERSIZED_THRESHOLD = MAX_FILE_LINES
def _strip_pkg_to_rel(dotted: str, pkg: str) -> str:
    return dotted[len(pkg) + 1:].replace(".", "/")
def _resolve_abs_target(module: str, pkg_name: str, rel_set: set[str],
                        prefer_qualified: bool = False) -> list[str]:
    qualified_init = pkg_name + "/__init__"
    if module == pkg_name:
        if prefer_qualified and qualified_init in rel_set:
            return [qualified_init]
        return ["__init__"] if "__init__" in rel_set else []
    prefix = pkg_name + "."
    if not module.startswith(prefix):
        return []
    parts = module[len(prefix):].split(".")
    cand = "/".join(parts)
    candidates = []
    if prefer_qualified:
        qualified = pkg_name + "/" + cand
        candidates.extend((qualified + "/__init__", qualified))
    candidates.extend((cand + "/__init__", cand))
    for candidate in candidates:
        if candidate in rel_set:
            return [candidate]
    for i in range(len(parts) - 1, 0, -1):
        init_cand = "/".join(parts[:i]) + "/__init__"
        if prefer_qualified:
            qualified_init = pkg_name + "/" + init_cand
            if qualified_init in rel_set:
                return [qualified_init]
        if init_cand in rel_set:
            return [init_cand]
    return []
def _self_import_finding(rel: str, message: str, line: int,
                         detail: str = "") -> Finding:
    return Finding(
        rule_id="ARCH-001",
        severity="P2",
        message=message,
        file=rel + ".py",
        line=line,
        confidence=0.8,
        detail=detail,
    )
def _cycle_finding(cycle_nodes: list[str], dep: str) -> Finding:
    return Finding(
        rule_id="ARCH-002",
        severity="P1",
        message=f"循环依赖: {' -> '.join(cycle_nodes)} -> {dep}",
        file=dep + ".py",
        confidence=0.8,
    )
def _god_file_finding(rel: str, line_count: int) -> Finding:
    return Finding(
        rule_id="ARCH-003",
        severity="P1",
        message=f"上帝文件: {line_count}行 (>{OVERSIZED_THRESHOLD} 行约束)",
        file=rel + ".py",
        confidence=0.8,
    )


def _is_ancestor_init(init_rel: str, rel: str,
                     package_members: set[str]) -> bool:
    """包入口是否为 ``rel`` 的祖先包入口。

    根 ``__init__`` 是全部包成员的祖先（以 ``package_members`` 判定成员身份，
    src 布局的 setup.py 等包外文件不算）；子包入口以路径前缀判定。
    """
    if init_rel == '__init__':
        return rel in package_members
    package_dir = init_rel[:-len('/__init__')]
    return rel == init_rel or rel.startswith(package_dir + '/')


def _add_edges(import_graph: dict, rel: str, targets,
               all_rels: set[str], package_members: set[str]) -> None:
    for target in targets:
        dependencies = [target]
        parts = target.split('/')[:-1]
        while parts:
            candidate = '/'.join(parts) + '/__init__'
            if candidate in all_rels and candidate != target:
                dependencies.append(candidate)
            parts.pop()
        if '__init__' in all_rels and target != '__init__':
            dependencies.append('__init__')
        for dependency in dependencies:
            if dependency == rel:
                continue
            if ((dependency.endswith('/__init__') or dependency == '__init__')
                    and _is_ancestor_init(dependency, rel, package_members)):
                # 导入 a/b/c 会依次执行 a、a/b 的包入口；但包入口是包内每个模块的
                # 导入发起者，包内模块对祖先入口的回指恒成立（根 __init__ 更是
                # 所有模块的祖先），计入只会把包内全部导入判成环。只有包外模块
                # （如 src 布局的 setup.py）导入包入口才是真实依赖边。
                continue
            import_graph[rel].add(dependency)
def _record_cycle(cycle_nodes: list[str], dep: str, findings: list,
                  reported: set[tuple]) -> None:
    cyc = tuple(sorted(cycle_nodes))
    if cyc in reported:
        return
    reported.add(cyc)
    if len(cyc) >= 2:
        findings.append(_cycle_finding(cycle_nodes, dep))
def _record_grey_cycle(dep: str, path: list[str], findings: list,
                       reported: set[tuple]) -> None:
    if dep in path:
        _record_cycle(path[path.index(dep):], dep, findings, reported)
def _visit_cycle(start: str, import_graph: dict, state: dict[str, int],
                 reported: set[tuple], findings: list) -> None:
    state[start] = 1
    work: list[list] = [
        [start, iter(sorted(import_graph.get(start, set()))), [start]]]
    while work:
        node, neighbours, path = work[-1]
        advanced = False
        for dep in neighbours:
            mark = state.get(dep, 0)
            if mark == 1:
                _record_grey_cycle(dep, path, findings, reported)
            elif mark == 0:
                state[dep] = 1
                work.append([dep, iter(sorted(import_graph.get(dep, set()))),
                             [*path, dep]])
                advanced = True
                break
        if advanced:
            continue
        work.pop()
        state[node] = 2
class _ArchFile(NamedTuple):
    line_count: int
    tree: ast.Module | None
class _ArchScanData(NamedTuple):
    pkg: str
    all_rels: set[str]
    line_counts: dict
    parsed_trees: dict
    findings: list
    display_paths: dict[str, str]
class ArchitectureRuleAnalyzer:
    def __init__(self, skill_dir: str, py_files: list[str]):
        self.skill_dir = skill_dir
        scan_root, self.pkg = _package_scan_root(skill_dir)
        layout = layout_of(skill_dir)
        self._is_package = layout.is_package
        self._package_nodes_qualified = False
        self._package_alias_rels: set[str] = set()
        self._package_member_rels: set[str] = set()
        self.package_root = (os.path.abspath(layout.package_root)
                             if layout.is_package else scan_root)
        self.py_files = py_files
    def _is_package_member(self, fpath: str) -> bool:
        if not self._is_package:
            return False
        try:
            # SkillLayout.package_root 经 realpath 归一（符号链接技能根会解析到
            # 真实目录），文件路径须同样归一，否则经符号链接访问技能根时全部成员
            # 都被判为包外文件，包身份/限定节点逻辑整体失效。
            common = os.path.commonpath(
                (os.path.realpath(os.path.abspath(fpath)),
                 os.path.realpath(self.package_root)))
        except (OSError, ValueError):
            return False
        return os.path.normcase(common) == os.path.normcase(
            os.path.realpath(self.package_root))
    def _ns_dir(self, mod_rel: str) -> str | None:
        if not mod_rel:
            return None
        roots = dict.fromkeys((
            self.package_root, os.path.abspath(self.skill_dir)))
        for root in roots:
            ns_dir = os.path.join(root, mod_rel)
            if (os.path.isdir(ns_dir)
                    and not os.path.isfile(
                        os.path.join(ns_dir, "__init__.py"))):
                return ns_dir
        return None
    def _ns_member_targets(self, mod_rel: str, names: list[str]) -> list[str]:
        ns_dir = self._ns_dir(mod_rel)
        if ns_dir is None:
            return []
        targets: list[str] = []
        for name in names:
            if name == "*":
                targets.append(mod_rel)
                continue
            if self._facade_member_exists(ns_dir, name):
                targets.append(mod_rel + "/" + name)
        return targets
    def _logical_rel(self, rel: str) -> str:
        prefix = self.pkg + "/"
        if self._package_nodes_qualified and rel.startswith(prefix):
            return rel[len(prefix):]
        return rel
    def _relative_base_parts(self, rel: str,
                             node: ast.ImportFrom) -> list[str] | None:
        rel = self._logical_rel(rel)
        pkg_parts = rel.split("/")[:-1]
        up = node.level - 1
        if up > len(pkg_parts):
            return None
        return pkg_parts[:len(pkg_parts) - up]
    @staticmethod
    def _is_self_target(parts: list[str], rel: str) -> bool:
        target = "/".join(parts)
        package_init = f"{target}/__init__" if target else "__init__"
        return target == rel or package_init == rel
    def _check_rel_self_import(self, rel: str, base: str,
                               node: ast.ImportFrom,
                               findings: list) -> None:
        target_rel = self._logical_rel(rel)
        base_parts = self._relative_base_parts(rel, node)
        if base_parts is None:
            return
        if node.module:
            module_parts = [*base_parts, *node.module.split('.')]
            if self._is_self_target(module_parts, target_rel):
                findings.append(_self_import_finding(
                    rel, f"模块 {base} 自导入自身（相对导入形态）",
                    node.lineno))
                return
            for alias in node.names:
                if (alias.name != "*"
                        and self._is_self_target(
                            [*module_parts, *alias.name.split('.')],
                            target_rel)):
                    findings.append(_self_import_finding(
                        rel, f"模块 {base} 自导入自身（相对父包门面形态）",
                        node.lineno))
                    break
            return
        if (any(alias.name == "*" for alias in node.names)
                and self._is_self_target(base_parts, target_rel)):
            findings.append(_self_import_finding(
                rel, f"模块 {base} 自导入自身（纯相对星号导入形态）",
                node.lineno,
                detail="从当前包星号导入会在包初始化期间重新导入自身"))
            return
        for alias in node.names:
            if (alias.name != "*"
                    and self._is_self_target(
                        [*base_parts, *alias.name.split('.')], target_rel)):
                findings.append(_self_import_finding(
                    rel, f"模块 {base} 自导入自身（纯相对导入形态）",
                    node.lineno))
                break
    def _file_is_shadowed_by_package(self, rel: str) -> bool:
        logical_rel = self._logical_rel(rel)
        if logical_rel.endswith("/__init__"):
            return False
        parts = logical_rel.split("/")
        roots = dict.fromkeys((self.package_root, os.path.abspath(self.skill_dir)))
        return any(os.path.isfile(os.path.join(root, *parts, "__init__.py"))
                   for root in roots)
    def _is_external_package_member_import(self, rel: str, pkg: str,
                                           module: str) -> bool:
        return (rel in self._package_member_rels
                and module != pkg and not module.startswith(pkg + '.'))
    def _is_abs_self_target(self, rel: str, pkg: str, module: str) -> bool:
        if self._is_external_package_member_import(rel, pkg, module):
            return False
        if _resolve_abs_target(
                module, pkg, {rel}, self._package_nodes_qualified) == [rel]:
            return True
        if rel in self._package_member_rels or "." not in module:
            return False
        logical_rel = self._logical_rel(rel)
        if self._file_is_shadowed_by_package(logical_rel):
            return False
        return self._direct_module_target(
            module.replace(".", "/"), {logical_rel}) == [logical_rel]
    def _check_abs_from_self_import(self, rel: str, base: str, pkg: str,
                                    node: ast.ImportFrom, findings: list,
                                    in_package: bool) -> None:
        if self._root_name_is_self_module(
                rel, base, node.module, in_package):
            findings.append(_self_import_finding(
                rel, f"模块 {base} 自导入自身", node.lineno))
            return
        if self._is_external_package_member_import(rel, pkg, node.module):
            return
        if self._is_abs_self_target(rel, pkg, node.module):
            self._check_abs_module_self_import(rel, pkg, node, findings)
            return
        self._check_facade_self_import(rel, pkg, node, findings)
    def _root_name_is_self_module(self, rel: str, base: str,
                                  module: str, in_package: bool) -> bool:
        if in_package or "/" in rel or module.split(".")[0] != base:
            return False
        pkg_init = os.path.join(self.package_root, base, "__init__.py")
        return not os.path.isfile(pkg_init)
    def _check_abs_module_self_import(self, rel: str, pkg: str,
                                      node: ast.ImportFrom,
                                      findings: list) -> None:
        if any(alias.name == "*" for alias in node.names):
            findings.append(_self_import_finding(
                rel, f"模块 {rel} 自导入自身（绝对导入形态）", node.lineno,
                detail="星号导入会重新导入当前模块的全部公开名，导入期形成自引用"))
            return
        mod_dir = self._absolute_module_dir(pkg, node.module)
        illegal = [
            a.name for a in node.names
            if not self._facade_member_exists(mod_dir, a.name)
        ]
        if not illegal:
            return
        findings.append(_self_import_finding(
            rel, f"模块 {rel} 自导入自身（绝对导入形态）", node.lineno,
            detail=f"符号不可解析: {', '.join(illegal)}"))
    def _absolute_module_dir(self, pkg: str, module: str) -> str:
        if module == pkg:
            return self.package_root
        if module.startswith(pkg + "."):
            return os.path.join(
                self.package_root, *module[len(pkg) + 1:].split("."))
        return os.path.join(
            os.path.abspath(self.skill_dir), *module.split("."))
    @staticmethod
    def _facade_member_exists(mod_dir: str, name: str) -> bool:
        member = os.path.join(mod_dir, name)
        return (os.path.isfile(member + ".py")
                or os.path.isfile(os.path.join(member, "__init__.py"))
                or os.path.isdir(member))
    def _check_facade_self_import(self, rel: str, pkg: str,
                                  node: ast.ImportFrom,
                                  findings: list) -> None:
        if node.module == pkg:
            prefix = ""
        elif node.module.startswith(pkg + "."):
            prefix = node.module[len(pkg) + 1:] + "."
        else:
            prefix = node.module + "."
        logical_rel = self._logical_rel(rel)
        for alias in node.names:
            target = prefix + alias.name
            if (alias.name != "*"
                    and self._is_self_target(target.split("."), logical_rel)):
                findings.append(_self_import_finding(
                    rel, f"模块 {rel} 自导入自身（经父包门面形态）",
                    node.lineno))
                break
    def _import_stmt_self_message(self, alias_name: str, rel: str, base: str,
                                  pkg: str, in_package: bool) -> str:
        if self._root_name_is_self_module(
                rel, base, alias_name, in_package):
            return f"模块 {base} 自导入自身（import 语句形态）"
        if self._is_abs_self_target(rel, pkg, alias_name):
            return f"模块 {rel} 自导入自身（import 语句形态）"
        return ""
    def _check_import_stmt_self_import(self, rel: str, base: str,
                                       pkg: str, node: ast.Import,
                                       findings: list, in_package: bool) -> None:
        for alias in node.names:
            message = self._import_stmt_self_message(
                alias.name, rel, base, pkg, in_package)
            if message:
                findings.append(_self_import_finding(
                    rel, message, node.lineno))
                break
    def _load_arch_file(self, fp: str) -> _ArchFile | None:
        try:
            content = read_source_auto(fp)
        except OSError as e:
            logger.warning("[ArchitectureRuleAnalyzer] 架构分析读盘失败（T15 跳过该文件）: %s: %s", fp, e)
            return None
        line_count = count_lines(content)
        try:
            tree = compile(content, fp, "exec", ast.PyCF_ONLY_AST)
        except PARSE_DEGRADE_EXC as e:
            logger.warning("[ArchitectureRuleAnalyzer] 架构分析解析失败（依赖图排除该文件）: %s: %s", fp, e)
            return _ArchFile(line_count=line_count, tree=None)
        return _ArchFile(line_count=line_count, tree=tree)
    def _collect_self_imports(self, rel: str, base: str, pkg: str,
                              tree: ast.Module, findings: list,
                              in_package: bool) -> None:
        if self._file_is_shadowed_by_package(rel):
            return
        for node in walk_nodes(tree):
            if isinstance(node, ast.ImportFrom):
                self._dispatch_import_from(
                    rel, base, pkg, node, findings, in_package)
            elif isinstance(node, ast.Import):
                self._check_import_stmt_self_import(
                    rel, base, pkg, node, findings, in_package)
    def _dispatch_import_from(self, rel: str, base: str, pkg: str,
                               node: ast.ImportFrom, findings: list,
                               in_package: bool) -> None:
        if node.level > 0:
            self._check_rel_self_import(rel, base, node, findings)
        elif node.module:
            self._check_abs_from_self_import(
                rel, base, pkg, node, findings, in_package)
    def _scan_files_structure(self) -> _ArchScanData:
        self._package_alias_rels = set()
        self._package_member_rels = set()
        findings: list[Finding] = []
        pkg = self.pkg
        all_rels: set[str] = set()
        line_counts: dict[str, int] = {}
        parsed_trees: dict[str, ast.Module] = {}
        display_paths: dict[str, str] = {}
        records = []
        for fp in self.py_files:
            rel = _relative_scan_path(
                fp, self.skill_dir, self.package_root).replace("\\", "/")[:-3]
            display_rel = os.path.relpath(
                fp, self.skill_dir).replace("\\", "/")[:-3]
            in_package = self._is_package_member(fp)
            records.append((fp, rel, display_rel, in_package))
        rel_counts = Counter(record[1] for record in records)
        self._package_nodes_qualified = any(
            rel_counts[rel] > 1
            and any(record[1] == rel and record[3] for record in records)
            and any(record[1] == rel and not record[3] for record in records)
            for rel in rel_counts)
        for fp, rel, display_rel, in_package in records:
            if in_package and self._package_nodes_qualified:
                rel = pkg + "/" + rel
            if in_package:
                self._package_member_rels.add(rel)
                if not rel.startswith(pkg + "/"):
                    self._package_alias_rels.add(rel)
            display_paths[rel] = display_rel
            base = os.path.basename(fp)[:-3]
            all_rels.add(rel)
            loaded = self._load_arch_file(fp)
            if loaded is None:
                continue
            line_counts[rel] = loaded.line_count
            if loaded.tree is None:
                continue
            parsed_trees[rel] = loaded.tree
            first_new = len(findings)
            self._collect_self_imports(
                rel, base, pkg, loaded.tree, findings,
                self._is_package_member(fp))
            for finding in findings[first_new:]:
                finding.file = display_rel + ".py"
        return _ArchScanData(
            pkg=pkg, all_rels=all_rels,
            line_counts=line_counts, parsed_trees=parsed_trees,
            findings=findings, display_paths=display_paths)
    def _module_symbol_candidates(self, pkg: str, dotted: str,
                                  names: list[str],
                                  all_rels: set) -> list[str]:
        cands = list(_resolve_abs_target(
            dotted, pkg, all_rels, self._package_nodes_qualified))
        if dotted != pkg and not dotted.startswith(pkg + "."):
            return self._direct_dotted_candidates(dotted, names, all_rels)
        members = [
            target
            for name in names if name != "*"
            for target in _resolve_abs_target(
                f"{dotted}.{name}", pkg, all_rels,
                self._package_nodes_qualified)
        ]
        if members:
            return list(dict.fromkeys([*cands, *members]))
        if cands:
            return cands
        return self._ns_member_targets(
            _strip_pkg_to_rel(dotted, pkg), names)
    def _package_dir_candidates(self, pkg: str, dotted: str,
                                all_rels: set) -> list[str]:
        cands = list(_resolve_abs_target(
            dotted, pkg, all_rels, self._package_nodes_qualified))
        if cands:
            return cands
        if not dotted.startswith(pkg + "."):
            return self._direct_dotted_candidates(dotted, [], all_rels)
        mod_rel = _strip_pkg_to_rel(dotted, pkg)
        return [mod_rel] if self._ns_dir(mod_rel) is not None else []
    def _direct_module_target(self, rel: str, all_rels: set) -> list[str]:
        if not rel:
            return []
        init_rel = f"{rel}/__init__"
        if init_rel in all_rels:
            return [init_rel]
        if rel in all_rels:
            return [rel]
        return [rel] if self._ns_dir(rel) is not None else []
    def _direct_dotted_candidates(self, dotted: str, names: list[str],
                                  all_rels: set) -> list[str]:
        rel = dotted.replace(".", "/")
        cands = self._direct_module_target(rel, all_rels)
        for name in names:
            if name == "*":
                continue
            member = (f"{rel}/{name.replace('.', '/')}"
                      if rel else name.replace(".", "/"))
            cands.extend(self._direct_module_target(member, all_rels))
        return list(dict.fromkeys(
            cand for cand in cands if cand not in self._package_alias_rels))
    def _root_facade_members(self, rel: str,
                             node: ast.ImportFrom) -> list[str]:
        logical_rel = self._logical_rel(rel)
        members: list[str] = []
        for alias in node.names:
            if (alias.name != "*" and alias.name != logical_rel
                    and self._facade_member_exists(
                        self.package_root, alias.name)):
                members.append(alias.name)
        return members
    def _graph_edges_from_relative(self, rel: str, pkg: str,
                                   node: ast.ImportFrom, all_rels: set,
                                   import_graph: dict) -> None:
        base_parts = self._relative_base_parts(rel, node)
        if base_parts is None:
            return
        if node.module:
            abs_mod = ".".join(
                [pkg, *base_parts, *node.module.split(".")])
            _add_edges(import_graph, rel, self._module_symbol_candidates(
                pkg, abs_mod, [a.name for a in node.names], all_rels),
                all_rels, self._package_member_rels)
            return
        if any(alias.name == "*" for alias in node.names):
            _add_edges(import_graph, rel, self._package_dir_candidates(
                pkg, ".".join([pkg, *base_parts]), all_rels),
                all_rels, self._package_member_rels)
        for alias in node.names:
            if alias.name == "*":
                continue
            abs_mod = ".".join(
                [pkg, *base_parts, *alias.name.split(".")])
            _add_edges(import_graph, rel,
                       self._package_dir_candidates(pkg, abs_mod, all_rels),
                       all_rels, self._package_member_rels)
    def _graph_edges_from_abs_from(self, rel: str, pkg: str,
                                   node: ast.ImportFrom,
                                   all_rels: set, import_graph: dict) -> None:
        cands = self._module_symbol_candidates(
            pkg, node.module, [a.name for a in node.names], all_rels)
        _add_edges(import_graph, rel, cands, all_rels,
                   self._package_member_rels)
        if not cands and node.module == pkg:
            _add_edges(import_graph, rel,
                       self._root_facade_members(rel, node), all_rels,
                       self._package_member_rels)
    def _graph_edges_from_import_stmt(self, rel: str, pkg: str,
                                      node: ast.Import, all_rels: set,
                                      import_graph: dict) -> None:
        for alias in node.names:
            _add_edges(import_graph, rel,
                       self._package_dir_candidates(pkg, alias.name, all_rels),
                       all_rels, self._package_member_rels)
    def _add_import_edges(self, rel: str, pkg: str, tree: ast.Module,
                          all_rels: set, import_graph: dict) -> None:
        # 只统计**导入期执行**的 import：函数体内的延迟导入是官方推荐的断环手法
        # （见各模块 "lazy-by-design — 硬环断路器" 注释），不会在加载期形成环，
        # 计入会把刻意的延迟导入判成 P1 循环依赖。
        for node in iter_module_level_imports_tc(tree):
            if isinstance(node, ast.ImportFrom):
                if node.level > 0:
                    self._graph_edges_from_relative(
                        rel, pkg, node, all_rels, import_graph)
                elif node.module:
                    self._graph_edges_from_abs_from(
                        rel, pkg, node, all_rels, import_graph)
            elif isinstance(node, ast.Import):
                self._graph_edges_from_import_stmt(
                    rel, pkg, node, all_rels, import_graph)
    def _build_import_graph(self, pkg: str, all_rels: set[str],
                            parsed_trees: dict) -> dict:
        import_graph: dict[str, set[str]] = defaultdict(set)
        for rel, tree in parsed_trees.items():
            self._add_import_edges(
                rel, pkg, tree, all_rels, import_graph)
        return import_graph
    def _detect_import_cycles(self, import_graph: dict,
                              findings: list) -> None:
        state: dict[str, int] = {}
        reported: set[tuple] = set()
        for node in sorted(import_graph):
            if state.get(node, 0) == 0:
                _visit_cycle(node, import_graph, state, reported, findings)
    def _detect_god_files(self, line_counts: dict, findings: list) -> None:
        for rel, line_count in line_counts.items():
            if line_count > OVERSIZED_THRESHOLD:
                findings.append(_god_file_finding(rel, line_count))
    def architecture_analysis(self) -> dict:
        scan = self._scan_files_structure()
        import_graph = self._build_import_graph(
            scan.pkg, scan.all_rels, scan.parsed_trees)
        findings = scan.findings
        scan_finding_count = len(findings)
        self._detect_import_cycles(import_graph, findings)
        self._detect_god_files(scan.line_counts, findings)
        for finding in findings[scan_finding_count:]:
            module_rel = finding.file[:-3]
            display = scan.display_paths.get(module_rel)
            if display is not None:
                finding.file = display + ".py"
        return {
            "findings": findings,
            "module_count": len(self.py_files),
        }
def classify_file_sizes(py_files: list[str], skill_dir: str,
                         ctx: Any) -> dict:
    stats: dict = {
        "small": 0,
        "medium": 0,
        "large": 0,
        "total_lines": 0,
        "readable": 0,
        "small_names": [],
    }
    for fname in py_files:
        src = read_source(os.path.join(skill_dir, fname), ctx)
        if src is None:
            continue
        stats["readable"] += 1
        lines = count_lines(src)
        stats["total_lines"] += lines
        if lines < 100:
            stats["small"] += 1
            stats["small_names"].append(fname)
        elif lines < 500:
            stats["medium"] += 1
        else:
            stats["large"] += 1
    return stats
def scan_graph(skill_dir: str) -> tuple[dict[str, set[str]],
                                        dict[tuple[str, str], dict[str, Any]]]:
    roots = _package_scan_root(skill_dir)
    module_paths = _scan_module_paths(skill_dir, roots)
    known = set(module_paths)
    source_root, root_package = roots
    layout = layout_of(skill_dir)
    package_root = (os.path.abspath(layout.package_root)
                    if layout.is_package else '')
    package_aliases = {
        name for name, path in module_paths.items()
        if name != root_package and not name.startswith(root_package + '.')
        and _path_within_root(path, package_root)
    }
    graph: dict[str, set[str]] = {name: set() for name in known}
    edges: dict[tuple[str, str], dict[str, Any]] = {}
    package_dependencies = _package_initializer_dependencies(module_paths)
    for name, path in module_paths.items():
        _collect_module_edges(
            name, path, skill_dir, source_root, known, root_package,
            package_dependencies, package_aliases, graph, edges)
    return graph, edges
def scan_module_fanout(skill_dir: str) -> dict[str, int]:
    try:
        graph, _edges = scan_graph(skill_dir)
    except Exception as exc:  # noqa: BLE001
        log_swallowed(__name__, exc, context="scan_module_fanout")
        return {}
    return {name: len(deps) for name, deps in graph.items()}
def build_closures(graph: dict[str, set[str]]) -> dict[str, set[str]]:
    closures: dict[str, set[str]] = {}
    for start, start_deps in graph.items():
        seen: set[str] = set()
        stack = list(start_deps)
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node)
            stack.extend(graph.get(node, ()))
        closures[start] = seen
    return closures
def compute_impact(closures: dict[str, set[str]]) -> dict[str, int]:
    impact = {name: 0 for name in closures}
    for name, deps in closures.items():
        for dep in deps:
            if dep in impact and dep != name:
                impact[dep] += 1
    return impact
def _topo_order(deps_of: dict[str, set[str]]) -> list[str]:
    indegree = {node: 0 for node in deps_of}
    for deps in deps_of.values():
        for dep in deps:
            if dep in indegree:
                indegree[dep] += 1
    order = [node for node, degree in indegree.items() if degree == 0]
    index = 0
    while index < len(order):
        node = order[index]
        index += 1
        for dep in deps_of[node]:
            if dep not in indegree:
                continue
            indegree[dep] -= 1
            if indegree[dep] == 0:
                order.append(dep)
    return order if len(order) == len(deps_of) else []
def _longest_path_dp(deps_of: dict[str, set[str]],
                     order: list[str]) -> tuple[dict[str, int], dict[str, str]]:
    depth: dict[str, int] = {}
    nxt: dict[str, str] = {}
    for node in reversed(order):
        best_dep = None
        best_value = -1
        for dep in sorted(deps_of[node]):
            value = depth.get(dep, 0)
            if value > best_value:
                best_value = value
                best_dep = dep
        depth[node] = best_value + 1 if best_dep is not None else 0
        if best_dep is not None:
            nxt[node] = best_dep
    return depth, nxt
def _walk_chain(head: str, nxt: dict[str, str]) -> list[str]:
    chain = [head]
    while chain[-1] in nxt:
        chain.append(nxt[chain[-1]])
    return chain
def _condensation_chain(deps_of: dict[str, set[str]]) -> tuple[int, list[str]]:
    components = tarjan_scc({node: set(deps)
                             for node, deps in deps_of.items()})
    members: dict[int, list[str]] = {}
    comp_of: dict[str, int] = {}
    for index, component in enumerate(components):
        members[index] = sorted(component)
        for node in component:
            comp_of[node] = index
    edges: dict[int, set[int]] = {index: set() for index in members}
    for node, deps in deps_of.items():
        source = comp_of[node]
        for dep in deps:
            target = comp_of[dep]
            if target != source:
                edges[source].add(target)
    order = _topo_order(edges)
    if not order:
        return 0, []
    weight = {index: len(group) for index, group in members.items()}
    depth: dict[int, int] = {}
    nxt: dict[int, int] = {}
    for index in reversed(order):
        best_index: int | None = None
        best_depth = -1
        for dep in sorted(edges[index]):
            value = depth.get(dep, 0)
            if value > best_depth:
                best_depth, best_index = value, dep
        depth[index] = (best_depth if best_index is not None else 0) \
            + weight[index]
        if best_index is not None:
            nxt[index] = best_index
    head = min(depth, key=lambda index: (-depth[index], members[index][0]))
    chain: list[str] = []
    current = head
    while current in nxt:
        chain.extend(members[current])
        current = nxt[current]
    chain.extend(members[current])
    return len(chain), chain
def longest_chain(graph: dict[str, set[str]]) -> tuple[int, list[str]]:
    deps_of = {node: {dep for dep in graph.get(node, ()) if dep in graph}
               for node in graph}
    if not deps_of:
        return 0, []
    order = _topo_order(deps_of)
    if not order:
        return _condensation_chain(deps_of)
    depth, nxt = _longest_path_dp(deps_of, order)
    head = max(depth, key=lambda name: (depth[name], name))
    chain = _walk_chain(head, nxt)
    return len(chain), chain
def _percentile(values: list[int], ratio: float) -> int:
    if not values:
        return 0
    position = min(len(values) - 1, int(len(values) * ratio))
    return values[position]
def _median(values: list[int]) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return float(ordered[middle])
    return (ordered[middle - 1] + ordered[middle]) / 2.0
def summarize(skill_dir: str) -> dict[str, Any]:
    if not os.path.isdir(skill_dir):
        raise FileNotFoundError(f"依赖测绘目标目录不存在: {skill_dir!r}")
    graph, edges = scan_graph(skill_dir)
    infra_modules = target_infra_modules(
        skill_dir, import_in_degrees(graph))
    closures = build_closures(graph)
    impact = compute_impact(closures)
    sizes = sorted(len(value) for value in closures.values())
    cycles = sorted(cycle_member_groups(graph, set(graph)))
    length, chain = longest_chain(graph)
    single = sum(
        1 for entry in edges.values()
        if len(entry['symbols']) == 1
        and _MODULE_IMPORT_SYMBOL not in entry['symbols']
    )
    fan_in_counts = Counter(dst for _src, dst in edges)
    infra_set = frozenset(infra_modules)
    infra_edges = sum(count for name, count in fan_in_counts.items()
                      if name in infra_set)
    lazy_edges = sum(1 for entry in edges.values() if entry['total'] and entry['total'] == entry['lazy'])
    largest = max(closures, key=lambda name: len(closures[name])) if closures else None
    top_impact = sorted(((count, name) for name, count in impact.items()), reverse=True)[:20]
    return {
        'skill_dir': skill_dir,
        'modules': len(graph),
        'edges': len(edges),
        'cycle_count': len(cycles),
        'cycles': cycles[:3],
        'closure': {
            'min': sizes[0] if sizes else 0,
            'p25': _percentile(sizes, 0.25),
            'median': _median(sizes),
            'p90': _percentile(sizes, 0.9),
            'max': sizes[-1] if sizes else 0,
            'max_module': largest,
        },
        'longest_chain': length,
        'longest_chain_modules': chain,
        'infra_share': round(infra_edges / len(edges), 4) if edges else 0.0,
        'infra_fan_in': {name: fan_in_counts.get(name, 0)
                         for name in infra_modules},
        'single_symbol_edge_ratio': round(single / len(edges), 4) if edges else 0.0,
        'fully_lazy_edges': lazy_edges,
        'impact': impact,
        'impact_top': top_impact,
    }
def format_report(report: dict[str, Any]) -> str:
    closure = report['closure']
    lines = [
        f"modules={report['modules']} edges={report['edges']} cycles={report['cycle_count']}",
        (
            f"closure: min={closure.get('min', 0)} p25={closure.get('p25', 0)} "
            f"median={closure['median']} p90={closure.get('p90', 0)} "
            f"max={closure.get('max', 0)}({closure.get('max_module')})"
        ),
        (
            f"longest_chain={report['longest_chain']} "
            f"infra_share={report['infra_share']:.1%} "
            f"single_symbol_ratio={report['single_symbol_edge_ratio']:.1%} "
            f"fully_lazy_edges={report['fully_lazy_edges']}"
        ),
    ]
    if report['longest_chain_modules']:
        lines.append('chain: ' + ' -> '.join(report['longest_chain_modules']))
    cycles = report.get('cycles') or []
    if cycles:
        lines.append(f"cycle_nodes={cycles}")
    return '\n'.join(lines)
def _baseline_number(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        number = float(value)
    except (OverflowError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_baseline_number:float')
        return None
    return number if math.isfinite(number) and number >= 0 else None
def _baseline_validation_problems(
        baseline: dict[str, Any]) -> list[str]:
    problems: list[str] = []
    for field in ('edges', 'infra_share', 'cycle_count', 'longest_chain'):
        if field in baseline and _baseline_number(baseline[field]) is None:
            problems.append(f"基线字段 {field} 非法：应为有限非负数值")
    if 'closure' not in baseline:
        return problems
    closure = baseline['closure']
    if not isinstance(closure, dict):
        problems.append("基线字段 closure 非法：应为 JSON 对象")
    elif ('median' in closure
          and _baseline_number(closure['median']) is None):
        problems.append("基线字段 closure.median 非法：应为有限非负数值")
    return problems

def _edge_drift_problems(report: dict[str, Any],
                         baseline: dict[str, Any]) -> list[str]:
    base_edges = _baseline_number(baseline.get('edges'))
    if base_edges is None:
        return []
    if base_edges == 0:
        return ([f"边数漂移 0 -> {report['edges']} (基线为零，新增边即漂移)"]
                if report['edges'] > 0 else [])
    drift = abs(report['edges'] - base_edges) / base_edges
    if drift <= _COUNT_TOLERANCE:
        return []
    return [f"边数漂移 {base_edges:g} -> {report['edges']} ({drift:.1%})"]
def _closure_drift_problems(report: dict[str, Any],
                            baseline: dict[str, Any]) -> list[str]:
    closure = baseline.get('closure')
    base_median = _baseline_number(
        closure.get('median') if isinstance(closure, dict) else None)
    if base_median is None:
        return []
    current_median = report['closure']['median']
    if base_median == 0:
        return ([f"闭包中位漂移 0 -> {current_median} (基线为零，新增闭包即漂移)"]
                if current_median > 0 else [])
    drift = abs(current_median - base_median) / base_median
    if drift <= 0.2:
        return []
    return [f"闭包中位漂移 {base_median:g} -> {current_median}"]
def _share_drift_problems(report: dict[str, Any],
                          baseline: dict[str, Any]) -> list[str]:
    base_share = _baseline_number(baseline.get('infra_share'))
    if (base_share is None
            or abs(report['infra_share'] - base_share) <= _RATIO_TOLERANCE):
        return []
    return [f"基础设施占比漂移 {base_share:.1%} -> {report['infra_share']:.1%}"]
def _cycle_problems(report: dict[str, Any],
                    baseline: dict[str, Any]) -> list[str]:
    base_cycles = _baseline_number(baseline.get('cycle_count'))
    if base_cycles is None or report['cycle_count'] <= base_cycles:
        return []
    new_cycles = report['cycle_count'] - base_cycles
    return [(f"新增循环依赖 {new_cycles:g} 处"
             f"（{base_cycles:g} -> {report['cycle_count']}）")]
def _chain_problems(report: dict[str, Any],
                    baseline: dict[str, Any]) -> list[str]:
    base_chain = _baseline_number(baseline.get('longest_chain'))
    if base_chain is None or report['longest_chain'] <= base_chain + 2:
        return []
    return [f"最长链变长 {base_chain:g} -> {report['longest_chain']}"]
def compare_with_baseline(report: dict[str, Any],
                          baseline: dict[str, Any]) -> list[str]:
    problems = _baseline_validation_problems(baseline)
    for collect in (_edge_drift_problems, _closure_drift_problems,
                    _share_drift_problems, _cycle_problems, _chain_problems):
        problems.extend(collect(report, baseline))
    return problems
def _load_baseline(path: str) -> dict[str, Any] | None:
    try:
        with open(path, encoding='utf-8') as handle:
            data = json.load(handle)
    except _LOAD_ERRORS as exc:
        log_swallowed(__name__, exc, context='_load_baseline:JSON 解析')
        return None
    return data if isinstance(data, dict) else None
def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description='Python 项目包内消费关系测绘')
    parser.add_argument('--root', default='.', help='项目根目录')
    parser.add_argument('--json', dest='json_out', help='输出指标 JSON 路径')
    parser.add_argument('--baseline', help='基线 JSON 路径，给出时执行对比')
    parser.add_argument('--impact', action='store_true', help='打印影响面 Top 模块')
    args = parser.parse_args(argv)
    try:
        report = summarize(args.root)
    except OSError as exc:
        print(f'ERROR: {exc}', file=sys.stderr)
        return 2
    print(format_report(report))
    if args.impact:
        for count, name in report['impact_top']:
            print(f'  impact={count:4d}  {name}')
    if args.json_out:
        try:
            with open(args.json_out, 'w', encoding='utf-8') as handle:
                json.dump(report, handle, ensure_ascii=False, indent=1)
        except OSError as exc:
            print(f'ERROR: {exc}', file=sys.stderr)
            return 2
    failures = 0
    if args.baseline:
        baseline = _load_baseline(args.baseline)
        if baseline is None:
            print(f'ERROR: 基线不可读或非 JSON 对象: {args.baseline}',
                  file=sys.stderr)
            return 2
        problems = compare_with_baseline(report, baseline)
        for problem in problems:
            print('BASELINE DRIFT: ' + problem, file=sys.stderr)
        failures = len(problems)
    return 1 if failures else 0
if __name__ == '__main__':
    sys.exit(main())

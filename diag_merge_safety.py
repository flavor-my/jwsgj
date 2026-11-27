from __future__ import annotations

import ast
import io
import itertools
import logging
import os
import re
import sys
import time
import tokenize
from collections import defaultdict, deque
from collections.abc import Callable, Hashable, Iterator, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from jwsgj.diag_detectors_registry import get_registry
from jwsgj.diag_shared_ast_nodes import (
    is_type_checking_guard,
    parse_ast_safely,
    relative_import_targets,
    typing_guard_aliases,
    typing_type_checking_names,
)
from jwsgj.diag_shared_source_core import (
    ASTUtils,
    count_lines,
    decode_source,
    iter_unquoted,
    leading_quote_states,
    parse_py_file,
    read_cached,
    read_source_cached,
    read_source_with_fingerprint,
    stat_fingerprint,
)
from jwsgj.diag_shared_source_scan import (
    is_masked_offset,
    scan_masked_spans,
)
from jwsgj.diag_types_normalize import coerce_path_str
from jwsgj.diag_types_vocab import LINE_LIMIT
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    CACHE_TEMP_DIR_NAMES,
    DIAG_OUT_OF_SCOPE_DIRS,
    SCAN_IGNORE_DIRS_LOWER,
    TEST_DIR_CANDIDATES_LOWER,
    is_pruned_scan_dir,
    is_scan_py_name,
    is_test_source_basename,
    iter_scan_py_files,
    relative_module_base,
    resolve_internal_dependency,
    resolve_search_root,
)
from jwsgj.skill_profile import detect_layout

__all__ = [
    "CYCLE_PRIORITY_EXTRACT_SHARED",
    "CYCLE_PRIORITY_LAZY_IMPORT",
    "CYCLE_PRIORITY_ORDER",
    "CYCLE_PRIORITY_RESTRUCTURE",
    "CYCLE_PRIORITY_TYPE_CHECKING",
    "IMPORT_SCAN_SKIP_DIRS",
    "UNSAFE_UNICODE_CHARS",
    "FragmentConsolidator",
    "MergePreflightChecker",
    "analyze_dependencies_before_split",
    "build_normalized_import_graph",
    "check_merge_self_protection",
    "check_unicode_safety",
    "choose_cycle_fix_priority",
    "detect_all_new",
    "detect_circular_imports",
    "detect_circular_imports_stratified",
    "enumerate_all_cycles",
    "find_graph_cycles",
    "is_protective_split",
    "module_name_for_path",
    "normalize_import_graph",
    "tarjan_scc",
]
logger = logging.getLogger(__name__)
logger.addHandler(logging.NullHandler())
_SCAN_PRUNE_DIRNAMES = frozenset(SCAN_IGNORE_DIRS_LOWER | CACHE_TEMP_DIR_NAMES)
_GRAPH_EXCLUDE_DIRNAMES = frozenset(
    _SCAN_PRUNE_DIRNAMES | DIAG_OUT_OF_SCOPE_DIRS | {"backup"}
)
_CONTAINER_TYPES = (list, tuple, set, frozenset)
_GRAPH_DEFAULT_OPTIONS: dict[str, bool] = {
    "include_tests": False,
    "allow_bare": False,
    "intra_package_only": False,
}
def _graph_edges(value: Any) -> tuple:
    if isinstance(value, _CONTAINER_TYPES):
        return tuple(value)
    logger.warning("[Cycles] 邻接表依赖非清单形状,按空邻接处理: %r",
                   type(value).__name__)
    return ()
def find_graph_cycles(graph: dict) -> list[list[str]]:
    if not isinstance(graph, Mapping):
        logger.warning("[Cycles] find_graph_cycles 非映射载荷,按空图处理: %r",
                       type(graph).__name__)
        return []
    adjacency = {node: _hashable_edges(node, deps)
                 for node, deps in graph.items()}
    return _find_cycles_in_graph(adjacency, set(adjacency))
def _hashable_edges(node: str, deps: Any) -> set[Any]:
    edges: set[Any] = set()
    for dep in _graph_edges(deps):
        if not isinstance(dep, Hashable):
            logger.warning(
                "[Cycles] 邻接项不可哈希,跳过该项: %r: %r", node, dep)
            continue
        edges.add(dep)
    return edges
def _sorted_neighbors(node: Any, deps: Any) -> list[Any]:
    return sorted(_hashable_edges(node, deps), key=str)
def enumerate_all_cycles(graph: dict) -> list[list[str]]:
    if not isinstance(graph, Mapping):
        logger.warning("[Cycles] enumerate_all_cycles 非映射载荷,按空图处理: %r",
                       type(graph).__name__)
        return []
    nodes = sorted(graph.keys(), key=str)
    order = {n: i for i, n in enumerate(nodes)}
    cycles: list[list[str]] = []
    for i, start in enumerate(nodes):
        cycles.extend(_enumerate_cycles_from(start, i, graph, order))
    return cycles
def _cycle_frame(node: str, graph: dict, order: dict[str, int],
                 min_index: int) -> tuple[str, Iterator[str]]:
    return node, iter(
        n for n in _sorted_neighbors(node, graph.get(node, ()))
        if order.get(n, -1) >= min_index)
def _unwind_cycle_frame(stack: list[tuple[str, Iterator[str]]],
                        path: list[str], on_path: set[str], start: str) -> None:
    node, _neighbors = stack.pop()
    if node != start:
        path.pop()
        on_path.discard(node)
def _enumerate_cycles_from(start: str, min_index: int, graph: dict,
                           order: dict[str, int]) -> list[list[str]]:
    path: list[str] = [start]
    on_path: set[str] = {start}
    found: list[list[str]] = []
    stack: list[tuple[str, Iterator[str]]] = [
        _cycle_frame(start, graph, order, min_index)]
    while stack:
        _node, neighbors = stack[-1]
        descended = False
        for neighbor in neighbors:
            if neighbor in on_path:
                if neighbor == start:
                    found.append(path + [start])
                continue
            on_path.add(neighbor)
            path.append(neighbor)
            stack.append(_cycle_frame(neighbor, graph, order, min_index))
            descended = True
            break
        if not descended:
            _unwind_cycle_frame(stack, path, on_path, start)
    return found
def _log_walk_error(exc: OSError) -> None:
    logger.warning("[Cycles] 目录枚举失败,已跳过: %s", exc)
def _walk_python_files(
    root_dir: str, keep_dir: Callable[[str], bool],
    keep_file: Callable[[str], bool] | None = None,
    on_error: Callable[[OSError], None] | None = None,
) -> Iterator[str]:
    for dirpath, dirnames, filenames in os.walk(
            root_dir, onerror=on_error or _log_walk_error):
        dirnames[:] = sorted(d for d in dirnames if keep_dir(d))
        for fname in sorted(filenames):
            if not is_scan_py_name(fname):
                continue
            fpath = os.path.join(dirpath, fname)
            if keep_file is not None and not keep_file(fpath):
                continue
            yield fpath
def _is_graph_scan_file(fpath: str, include_tests: bool) -> bool:
    return include_tests or not is_test_source_basename(
        os.path.basename(fpath))
def _module_relpath(fpath: str, root_dir: str, package_root: str) -> str:
    if (package_root
            and os.path.normcase(os.path.abspath(package_root))
            != os.path.normcase(os.path.abspath(root_dir))
            and _relpath_within(fpath, package_root) is not None):
        return os.path.relpath(fpath, os.path.dirname(package_root))
    return os.path.relpath(fpath, root_dir)
def _iter_project_modules(
        root_dir: str,
        include_tests: bool = _GRAPH_DEFAULT_OPTIONS["include_tests"],
        *,
        on_error: Callable[[OSError], None] | None = None,
) -> Iterator[tuple[str, str, list[str]]]:
    excluded_dirs = (_GRAPH_EXCLUDE_DIRNAMES if not include_tests
                     else _GRAPH_EXCLUDE_DIRNAMES
                     - TEST_DIR_CANDIDATES_LOWER)
    package_root = detect_layout(root_dir).package_root
    for fpath in _walk_python_files(
            root_dir,
            lambda d: _is_scan_dirname(
                d, excluded_dirs, include_tests=include_tests),
            lambda f: _is_graph_scan_file(f, include_tests),
            on_error=on_error):
        rel = _module_relpath(fpath, root_dir, package_root)
        module, pkg_segs = _resolve_module_identity(
            os.path.basename(fpath), rel)
        yield fpath, module, pkg_segs
def _is_scan_dirname(dirname: str, excluded_dirs: frozenset[str],
                     *, include_tests: bool) -> bool:
    lowered = dirname.lower()
    return (not is_pruned_scan_dir(dirname, excluded_dirs)
            and (include_tests or not lowered.startswith('test_')))
def _resolve_module_identity(fname: str, rel: str) -> tuple[str, list[str]]:
    module, _base_name = _split_module_identity(rel)
    if fname == "__init__.py":
        return (module or "__init__"), (module.split(".") if module else [])
    return module, (module.split(".")[:-1] if module else [])
def module_name_for_path(path: str, root_dir: str) -> str:
    path = coerce_path_str(path)
    root_dir = coerce_path_str(root_dir)
    if not path or not root_dir:
        return ""
    package_root = detect_layout(root_dir).package_root
    inside_root = _relpath_within(path, root_dir) is not None
    inside_package = (bool(package_root)
                      and _relpath_within(path, package_root) is not None)
    if not inside_root and not inside_package:
        logger.warning(
            "[Cycles] module_name_for_path: 路径不在根目录内, 返回空模块名 "
            "path=%s root=%s", path, root_dir)
        return ""
    rel = _module_relpath(path, root_dir, package_root)
    module, _pkg_segs = _resolve_module_identity(os.path.basename(path), rel)
    return module
def _record_from_symbols(symbol_map: dict[str, list[str]], target: str,
                         node: ast.ImportFrom) -> None:
    syms = symbol_map.setdefault(target, [])
    for alias in node.names:
        if alias.name == "*":
            continue
        sym = alias.name if alias.asname is None else f"{alias.name} as {alias.asname}"
        if sym not in syms:
            syms.append(sym)
def _record_importfrom_edges(
    node: ast.ImportFrom, pkg_segs: list[str], targets: set,
    symbol_map: dict, source_module: str,
) -> None:
    if node.level > 0:
        rel_targets = relative_import_targets(pkg_segs, node)
        if not rel_targets:
            return
        if node.module:
            base_target = rel_targets[0]
            targets.add(base_target)
            targets.update(f"{base_target}.{a.name}"
                           for a in node.names if a.name != "*")
            _record_from_symbols(symbol_map, base_target, node)
        else:
            base_target = ".".join(
                pkg_segs[:len(pkg_segs) - (node.level - 1)])
            if base_target and base_target != source_module:
                targets.add(base_target)
                _record_from_symbols(symbol_map, base_target, node)
            for target in rel_targets:
                target = target.removesuffix(".*")
                if not target:
                    continue
                targets.add(target)
                symbol_map.setdefault(target, [])
    elif node.module:
        targets.add(node.module)
        targets.update(f"{node.module}.{a.name}"
                       for a in node.names if a.name != "*")
        _record_from_symbols(symbol_map, node.module, node)
def _collect_module_imports(
    fpath: str, pkg_segs: list[str], source_module: str,
) -> tuple[set[str], dict[str, list[str]]] | tuple[None, None]:
    content, tree = parse_py_file(fpath)
    if content is None or tree is None:
        return None, None
    targets: set[str] = set()
    symbol_map: dict[str, list[str]] = {}
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                targets.add(alias.name)
        elif isinstance(node, ast.ImportFrom):
            _record_importfrom_edges(
                node, pkg_segs, targets, symbol_map, source_module)
    return targets, symbol_map
def _build_suffix_index(nodes: set) -> dict[str, list[str]]:
    suffix_index: dict[str, list[str]] = {}
    for n in nodes:
        suffix_index.setdefault(n.rsplit(".", 1)[-1], []).append(n)
    return suffix_index
def _resolve_import_node(
    imp: str, nodes: set, suffix_index: dict[str, list[str]],
    allow_bare: bool = _GRAPH_DEFAULT_OPTIONS["allow_bare"],
) -> str | None:
    if imp in nodes:
        return imp
    candidates = [c for c in suffix_index.get(imp.rsplit(".", 1)[-1], [])
                  if "." in imp and c.endswith("." + imp)]
    if candidates:
        best = max(candidates, key=lambda c: c.count("."))
        depth = best.count(".")
        if sum(1 for c in candidates if c.count(".") == depth) != 1:
            return None
        return best
    if allow_bare:
        return _resolve_bare_import(imp, suffix_index)
    return None
def _resolve_bare_import(imp: str, suffix_index: dict[str, list[str]]) -> str | None:
    if "." in imp:
        return None
    bare = [c for c in suffix_index.get(imp, []) if c.endswith("." + imp)]
    if not bare:
        return None
    best = min(bare, key=lambda c: c.count("."))
    if sum(1 for c in bare if c.count(".") == best.count(".")) != 1:
        return None
    return best
def _package_ancestor_segments(root_dir: str) -> list[str]:
    path = os.path.abspath(root_dir)
    segments = [os.path.basename(path)]
    anchored = os.path.isfile(os.path.join(path, "__init__.py"))
    parent = os.path.dirname(path)
    while parent != path and os.path.isfile(os.path.join(parent, "__init__.py")):
        segments.insert(0, os.path.basename(parent))
        anchored = True
        path, parent = parent, os.path.dirname(parent)
    return segments if anchored else []
def _project_import_prefixes(root_dir: str) -> list[str]:
    segments = _package_ancestor_segments(root_dir)
    return [".".join(segments[end:]) for end in range(len(segments))]
def _flat_package_name(root_dir: str) -> str:
    layout = detect_layout(root_dir)
    if (layout.package_name and layout.package_root
            and os.path.normcase(os.path.abspath(layout.package_root))
            == os.path.normcase(os.path.abspath(root_dir))):
        return layout.package_name
    return ""
def _build_project_alias_index(nodes: set,
                               prefixes: list[str]) -> dict[str, str]:
    alias_index: dict[str, str] = {}
    for prefix in prefixes:
        if not prefix:
            continue
        for node in nodes:
            alias_index.setdefault(f"{prefix}.{node}", node)
    return alias_index
def _resolve_project_import(imp: str, nodes: set,
                            alias_index: dict[str, str],
                            package_prefixes: tuple[str, ...] | list[str] = ()
                            ) -> str | None:
    if imp in nodes:
        return imp
    mapped = alias_index.get(imp)
    if mapped is not None:
        return mapped
    if imp in package_prefixes and "__init__" in nodes:
        return "__init__"
    return None
def _is_package_self_target(
        mapped: str, module: str, *, flat_package: str) -> bool:
    # 自身父包（含扁平包根 "__init__"）在模块运行时已处于初始化链上。
    if mapped == module:
        return False
    if module.startswith(mapped + "."):
        return True
    return bool(flat_package) and mapped == "__init__"
def _package_self_import_binds_only_submodules(
        raw_target: str, module: str, symbols: Mapping[str, list[str]],
        resolve: Callable[[str, str], str | None],
) -> bool:
    # `from . import x` 只有在 x 落到已知子模块时才是恒真边；若 x 可能是父包
    # __init__ 中定义的名字（部分初始化属性访问），或为星号导入，则依赖真实存在。
    names = symbols.get(raw_target)
    if names is None:
        return True
    if not names:
        return False
    for name in names:
        leaf = name.split(" as ", 1)[0].strip()
        if not leaf or leaf == "*":
            return False
        if resolve(f"{raw_target}.{leaf}", module) is None:
            return False
    return True
def normalize_import_graph(
        import_graph: dict,
        allow_bare: bool = _GRAPH_DEFAULT_OPTIONS["allow_bare"],
) -> dict:
    if not isinstance(import_graph, Mapping):
        logger.warning("[Cycles] normalize_import_graph 非映射载荷,按空图处理: %r",
                       type(import_graph).__name__)
        return {}
    nodes = {node for node in import_graph if isinstance(node, str)}
    if len(nodes) != len(import_graph):
        logger.warning(
            "[Cycles] normalize_import_graph 含非 str 模块键, 已跳过 %d 个",
            len(import_graph) - len(nodes))
    suffix_index = _build_suffix_index(nodes)
    normalized_graph: dict[str, set[str]] = {}
    for module, imports in import_graph.items():
        if not isinstance(module, str):
            continue
        normalized: set[str] = set()
        for imp in _iter_str_entries(imports, label="imports", owner=module):
            mapped = _resolve_import_node(imp, nodes, suffix_index,
                                          allow_bare=allow_bare)
            if mapped is not None:
                normalized.add(mapped)
        normalized_graph[module] = normalized
    return normalized_graph
def build_normalized_import_graph(
        root_dir: str,
        include_tests: bool = _GRAPH_DEFAULT_OPTIONS["include_tests"],
        allow_bare: bool = _GRAPH_DEFAULT_OPTIONS["allow_bare"],
        *,
        _incomplete_files: list[str] | None = None,
        _walk_error: Callable[[OSError], None] | None = None,
) -> tuple[dict, dict]:
    raw_root = root_dir
    root_dir = coerce_path_str(root_dir)
    if not root_dir.strip():
        logger.warning(
            "[Cycles] build_normalized_import_graph: root_dir 应为非空路径字符串,"
            " 收到 %r, 按空图降级", raw_root)
        return {}, {}
    if not os.path.isdir(root_dir):
        logger.warning(
            "[Cycles] build_normalized_import_graph: root_dir 不是目录,"
            " 按空图降级: %s", root_dir)
        return {}, {}
    import_graph: dict[str, set[str]] = defaultdict(set)
    symbol_import_map: dict[str, dict[str, list[str]]] = {}
    direct_script_prefixes: dict[str, str] = {}
    flat_package = _flat_package_name(root_dir)
    for fpath, module, pkg_segs in _iter_project_modules(
            root_dir, include_tests=include_tests, on_error=_walk_error):
        import_graph[module]
        if (pkg_segs and not os.path.isfile(
                os.path.join(os.path.dirname(fpath), '__init__.py'))):
            direct_script_prefixes[module] = '.'.join(pkg_segs)
        scan_pkg_segs = pkg_segs
        scan_module = module
        if flat_package:
            scan_pkg_segs = [flat_package, *pkg_segs]
            scan_module = (flat_package if module == "__init__"
                           else f"{flat_package}.{module}")
        targets, syms = _collect_module_imports(
            fpath, scan_pkg_segs, scan_module)
        if targets is None:
            if _incomplete_files is not None:
                _incomplete_files.append(fpath)
            continue
        import_graph[module] |= targets
        if syms:
            symbol_import_map[module] = syms
    nodes = set(import_graph.keys())
    suffix_index = _build_suffix_index(nodes)
    package_prefixes = _project_import_prefixes(root_dir)
    alias_index = _build_project_alias_index(nodes, package_prefixes)
    def _resolve(imp: str, source_module: str) -> str | None:
        mapped = _resolve_project_import(
            imp, nodes, alias_index, package_prefixes)
        if mapped is None and '.' not in imp:
            prefix = direct_script_prefixes.get(source_module)
            sibling = f'{prefix}.{imp}' if prefix else ''
            if sibling in nodes:
                mapped = sibling
        if mapped is None and allow_bare:
            return _resolve_bare_import(imp, suffix_index)
        return mapped
    normalized_graph: dict[str, set[str]] = {}
    for module, deps in import_graph.items():
        normalized: set[str] = set()
        symbols = symbol_import_map.get(module, {})
        for dep in deps:
            mapped = _resolve(dep, module)
            if mapped is None:
                continue
            # `from . import x` / `import pkg` 指向自身父包的边恒真：包内模块运行时
            # 父包已在初始化链上；仅当导入符号无法落到已知子模块（可能是 __init__
            # 中定义的名字）时才保留对 __init__ 的依赖。
            if (_is_package_self_target(mapped, module, flat_package=flat_package)
                    and _package_self_import_binds_only_submodules(
                        dep, module, symbols, _resolve)):
                continue
            normalized.add(mapped)
            if mapped == module:
                continue
            # 父包 __init__ 边仅对包外导入方成立：包内模块运行时父包已初始化，
            # 再补父包边会把 "__init__ 再导出子模块 + 子模块导入兄弟" 误判成环。
            normalized.update(
                ancestor for ancestor in _module_name_and_ancestors(mapped)
                if ancestor != module and ancestor in nodes
                and not module.startswith(ancestor + "."))
        normalized_graph[module] = normalized
    normalized_symbol_map = _normalize_symbol_import_map(
        symbol_import_map, _resolve)
    return normalized_graph, normalized_symbol_map
def _normalize_symbol_import_map(
        symbol_import_map: dict,
        resolver: Callable[[str, str], str | None]) -> dict:
    normalized: dict = {}
    for mod, deps in symbol_import_map.items():
        inner: dict[str, list[str]] = {}
        for imp, syms in deps.items():
            mapped = resolver(imp, mod)
            if mapped is None:
                continue
            merged = inner.setdefault(mapped, [])
            for sym in syms:
                if sym not in merged:
                    merged.append(sym)
        normalized[mod] = inner
    return normalized
class MergePreflightChecker:
    def __init__(self, root_dir: str) -> None:
        self.root_dir = coerce_path_str(root_dir)
        self.import_graph: dict[str, set[str]] = defaultdict(set)
        self._incomplete_files: list[str] = []
    def build_graph(self) -> None:
        self._incomplete_files = []
        evidence_root = os.path.abspath(self.root_dir)
        if not os.path.isdir(evidence_root):
            self.import_graph = {}
            return
        evidence = _ScanEvidence()
        graph, _symbols = build_normalized_import_graph(
            self.root_dir,
            _incomplete_files=self._incomplete_files,
            _walk_error=evidence.walk_error)
        if not evidence.complete:
            self._incomplete_files.append(
                f"{evidence_root} (directory enumeration failed)")
        self.import_graph = graph
    def _expand_package_members(self, files_to_merge: list[str]) -> list[str]:
        expanded = list(files_to_merge)
        seen = set(files_to_merge)
        for module in files_to_merge:
            prefix = f"{module}."
            for node in self.import_graph:
                if node.startswith(prefix) and node not in seen:
                    seen.add(node)
                    expanded.append(node)
        return expanded
    def _simulate_merge(self, files_to_merge: list[str], merged_name: str) -> list[list[str]]:
        merged_set = set(files_to_merge)
        internal = merged_set | {merged_name}
        new_graph: dict[str, set[str]] = {}
        for module, imports in self.import_graph.items():
            if module in internal:
                continue
            new_graph[module] = {
                (merged_name if imp in merged_set else imp) for imp in imports
            }
        all_imports: set[str] = set()
        for module in internal:
            all_imports |= self.import_graph.get(module, set())
        new_graph[merged_name] = all_imports - internal
        return enumerate_all_cycles(new_graph)
    def check_merge_safety(self, files_to_merge: list[str], merged_name: str) -> dict:
        degraded = _reject_invalid_merge_safety_params(files_to_merge, merged_name)
        if degraded is not None:
            return degraded
        files_to_merge = [
            m.strip().removesuffix('.__init__')
            for m in _filter_nonblank_strs(
                files_to_merge, owner="check_merge_safety",
                label="files_to_merge 模块名")
        ]
        files_to_merge = [m for m in files_to_merge if m]
        if not files_to_merge:
            logger.warning(
                "[Antipattern] check_merge_safety: 过滤后无有效待合并模块,"
                " 保守降级不放行")
            return _merge_safety_result(
                False, [], "invalid parameters: files_to_merge empty")
        if not self.import_graph:
            self.build_graph()
        merged_name = merged_name.strip().removesuffix('.__init__')
        if (not merged_name or merged_name in {".", ".."}
                or any(ch.isspace() for ch in merged_name)
                or "/" in merged_name or "\\" in merged_name
                or any(not seg for seg in merged_name.split("."))):
            logger.warning(
                "[Antipattern] check_merge_safety: merged_name 非法(%r),"
                " 保守降级不放行", merged_name)
            return _merge_safety_result(
                False, [], "invalid parameters: merged_name invalid")
        missing = sorted(m for m in files_to_merge
                         if m not in self.import_graph)
        if missing:
            logger.warning(
                "[Antipattern] check_merge_safety: 待合并模块不在导入图中"
                " %s, 无法验证合并安全性, 保守降级不放行",
                ", ".join(missing))
            return _merge_safety_result(
                False, [], f"unknown modules: {', '.join(missing)}")
        if self._incomplete_files:
            logger.warning(
                "[Antipattern] 导入图含 %d 个不可读或不可解析文件，"
                "无法验证合并安全性，保守降级不放行: %s",
                len(self._incomplete_files), ", ".join(self._incomplete_files))
            return _merge_safety_result(
                False, [], "incomplete import graph: source files unreadable or unparsable")
        current_cycles = enumerate_all_cycles(self.import_graph)
        merge_set = self._expand_package_members(files_to_merge)
        simulated_cycles = self._simulate_merge(merge_set, merged_name)
        new_cycles = _filter_new_cycles(
            simulated_cycles, current_cycles, merged_name, set(merge_set))
        return _merge_safety_result(not new_cycles, new_cycles)
def _merge_safety_result(safe: bool, cycles: list[list[str]],
                         error: str | None = None) -> dict:
    result: dict = {
        "safe": safe,
        "new_cycles": cycles,
        "total_new_cycles": len(cycles),
    }
    if error is not None:
        result["error"] = error
    return result
def _reject_invalid_merge_safety_params(files_to_merge: Any,
                                        merged_name: Any) -> dict | None:
    if not isinstance(files_to_merge, list):
        logger.warning(
            "[Antipattern] check_merge_safety: files_to_merge 应为模块名"
            "列表, 收到 %s, 保守降级不放行", type(files_to_merge).__name__)
        return _merge_safety_result(
            False, [], "invalid parameters: files_to_merge not a list")
    if not isinstance(merged_name, str):
        logger.warning(
            "[Antipattern] check_merge_safety: merged_name 应为模块名"
            "字符串, 收到 %s, 保守降级不放行", type(merged_name).__name__)
        return _merge_safety_result(
            False, [], "invalid parameters: merged_name not a str")
    if not merged_name.strip():
        logger.warning(
            "[Antipattern] check_merge_safety: merged_name 为空白模块名,"
            " 保守降级不放行")
        return _merge_safety_result(
            False, [], "invalid parameters: merged_name blank")
    return None
def _filter_nonblank_strs(items: list, *, owner: str, label: str) -> list[str]:
    kept: list[str] = []
    for item in items:
        if isinstance(item, str):
            if item.strip():
                kept.append(item)
                continue
            logger.warning(
                "[Antipattern] %s: %s 内含空白项 %r, 已剔除",
                owner, label, item)
            continue
        logger.warning(
            "[Antipattern] %s: %s 内含非字符串元素 %r(%s), 已剔除",
            owner, label, item, type(item).__name__)
    return kept
def _cycle_edge_signature(
        cycle: list[str], unit_nodes: frozenset[str],
        unit_label: str,
) -> frozenset[tuple[str, str]]:
    edges: set[tuple[str, str]] = set()
    for src, dst in itertools.pairwise(cycle):
        src_external = src not in unit_nodes
        dst_external = dst not in unit_nodes
        if not (src_external or dst_external):
            continue
        edges.add(
            (src if src_external else unit_label,
             dst if dst_external else unit_label)
        )
    return frozenset(edges)
def _filter_new_cycles(simulated_cycles: list[list[str]],
                       current_cycles: list[list[str]],
                       merged_name: str,
                       merge_set: set[str]) -> list[list[str]]:
    merge_unit = frozenset(merge_set | {merged_name})
    current_edges = [
        _cycle_edge_signature(oc, merge_unit, merged_name)
        for oc in current_cycles
    ]
    simulated_unit = merge_unit | {merged_name}
    new_cycles: list[list[str]] = []
    for sim_cycle in simulated_cycles:
        if merged_name not in sim_cycle:
            continue
        sim_edges = _cycle_edge_signature(
            sim_cycle, simulated_unit, merged_name)
        if sim_edges not in current_edges:
            new_cycles.append(sim_cycle)
    return new_cycles
UNSAFE_UNICODE_CHARS = {
    '\u3002': ('\u3002', '句号', '.'),
    '\uff0c': ('\uff0c', '逗号', ','),
    '\uff1a': ('\uff1a', '冒号', ':'),
    '\uff1b': ('\uff1b', '分号', ';'),
    '\uff08': ('（', '左括号', '('),
    '\uff09': ('）', '右括号', ')'),
    '\u2192': ('→', '箭头', '->'),
    '\u2190': ('←', '左箭头', '<-'),
    '\u201c': ('\u201c', '左双引号', '"'),
    '\u201d': ('\u201d', '右双引号', '"'),
    '\u3001': ('、', '顿号', ','),
    '\u2014': ('—', '破折号', '--'),
    '\u2026': ('…', '省略号', '...'),
    '\uff0e': ('．', '全角句点', '.'),
    '\u00a0': ('\xa0', '非断空格', ' '),
}
_UNICODE_SKIP_TOKEN_TYPES = frozenset({
    tokenize.STRING,
    tokenize.COMMENT,
    tokenize.NL,
    tokenize.NEWLINE,
    tokenize.INDENT,
    tokenize.DEDENT,
    tokenize.ENCODING,
    tokenize.ENDMARKER,
    getattr(tokenize, 'FSTRING_MIDDLE', -1),
    getattr(tokenize, 'FSTRING_START', -1),
    getattr(tokenize, 'FSTRING_END', -1),
})
def check_unicode_safety(filepath: str | os.PathLike) -> list:
    filepath = coerce_path_str(filepath)
    if not filepath:
        return []
    issues = []
    content, _ = read_source_with_fingerprint(filepath)
    if content is None:
        return issues
    try:
        _scan_unicode_tokens(content, filepath, issues)
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as _exc:
        log_swallowed(__name__, _exc, context='check_unicode_safety:tokenize')
        reported = {(iss['char'], iss['line'], iss['column']) for iss in issues}
        issues.extend(_scan_unicode_lines(content, filepath, reported))
    issues.sort(key=lambda iss: (iss['line'], iss['column']))
    return issues
def _unicode_issue(filepath: str, line: int, column: int, ch: str,
                   in_token: bool) -> dict:
    display, name, replacement = UNSAFE_UNICODE_CHARS[ch]
    message = (
        f"代码token含全角标点 '{display}' ({name}), 建议替换为 '{replacement}'"
        if in_token else
        f"全角标点 '{display}' ({name}), 建议替换为 '{replacement}'")
    suggestion = (
        f"根因: 代码标识符/运算符中使用了全角字符，可能导致SyntaxError"
        f"或可移植性问题。\n修复策略: 将 '{display}' 替换为 '{replacement}'\n"
        f"参考标准: PEP 8 / pylint / SonarQube"
        if in_token else "")
    return {
        "detector_id": "MS01",
        "pattern_name": "Unicode安全",
        "severity": "WARN",
        "filepath": filepath,
        "file": filepath,
        "line": line,
        "column": column,
        "char": display,
        "char_name": name,
        "suggested_replacement": replacement,
        "message": message,
        "suggestion": suggestion,
    }
def _scan_unicode_tokens(content: str, filepath: str, issues: list) -> None:
    for tok in tokenize.generate_tokens(io.StringIO(content).readline):
        if tok.type in _UNICODE_SKIP_TOKEN_TYPES:
            continue
        for pos, ch in enumerate(tok.string):
            if ch not in UNSAFE_UNICODE_CHARS:
                continue
            issues.append(_unicode_issue(
                filepath, tok.start[0], tok.start[1] + pos, ch,
                in_token=True))
def _code_offsets(line: str) -> Iterator[int]:
    for pos, ch in iter_unquoted(line):
        if ch == "#":
            return
        yield pos
def _scan_unicode_lines(content: str, filepath: str,
                        reported: set[tuple[str, int, int]]) -> list[dict]:
    lines = content.split('\n')
    states = leading_quote_states(lines)
    fallback: list[dict] = []
    for lineno, line in enumerate(lines, 1):
        if states[lineno - 1]:
            continue
        for pos in _code_offsets(line):
            char = line[pos]
            if char not in UNSAFE_UNICODE_CHARS:
                continue
            display = UNSAFE_UNICODE_CHARS[char][0]
            if (display, lineno, pos) in reported:
                continue
            fallback.append(
                _unicode_issue(filepath, lineno, pos, char, in_token=False))
    return fallback
def check_merge_self_protection(
    merge_files: list[str] | None = None,
    output_file: str | None = None,
    delete_list: list[str] | None = None,
) -> list[dict]:
    merge_paths, merge_param_issues = _normalize_path_list_param(
        merge_files, "merge_files")
    delete_paths, delete_param_issues = _normalize_path_list_param(
        delete_list, "delete_list")
    output_file, output_param_issues = _normalize_output_file_param(output_file)
    issues: list[dict] = [
        *merge_param_issues, *delete_param_issues, *output_param_issues,
    ]
    if output_file is not None and not _is_blank_path(output_file):
        issues.extend(_check_output_in_delete_list(output_file, delete_paths))
        issues.extend(_check_merge_source_distinct(merge_paths, output_file))
    issues.extend(_check_merge_files_exist(merge_paths))
    return issues
def _normalize_path_list_param(
    value: Any, name: str,
) -> tuple[list[str], list[dict]]:
    if value is None:
        return [], []
    if not isinstance(value, list):
        logger.warning(
            "[Antipattern] check_merge_self_protection: %s 应为路径列表, "
            "收到 %s, 按空清单降级并报告校验不完整", name, type(value).__name__)
        return [], [_ms02_issue(
            "ERROR",
            f"{name} 应为路径列表，收到 {type(value).__name__}，"
            "无法完成合并自保护校验",
            f"根因: {name} 参数形态非法，部分安全检查未执行。\n"
            f"修复策略: 将 {name} 改为路径列表",
        )]
    coerced = [
        coerce_path_str(item)
        if isinstance(item, (os.PathLike, bytes)) else item
        for item in value
    ]
    paths = _filter_nonblank_strs(
        coerced, owner="check_merge_self_protection", label=f"{name} 路径")
    if len(paths) == len(coerced):
        return paths, []
    return paths, [_ms02_issue(
        "ERROR",
        f"{name} 含空白或非字符串路径项，无法完成合并自保护校验",
        f"根因: {name} 中部分路径无法归一化，相关安全比对未执行。\n"
        f"修复策略: 移除 {name} 中的无效路径项",
    )]
def _normalize_output_file_param(
    value: Any,
) -> tuple[str | None, list[dict]]:
    if value is None:
        return None, []
    if isinstance(value, (str, bytes, os.PathLike)):
        path = coerce_path_str(value)
        if not _is_blank_path(path):
            return path, []
        logger.warning(
            "[Antipattern] check_merge_self_protection: output_file 为空白"
            "路径, 跳过身份比对并报告校验不完整")
        return path, [_ms02_issue(
            "ERROR",
            "output_file 为空白路径，无法完成输出身份隔离校验",
            "根因: 输出路径为空，无法与删除列表和合并源比对。\n"
            "修复策略: 提供非空白 output_file 路径",
        )]
    logger.warning(
        "[Antipattern] check_merge_self_protection: output_file 应为路径, "
        "收到 %s, 按未提供处理并报告校验不完整", type(value).__name__)
    return None, [_ms02_issue(
        "ERROR",
        f"output_file 应为路径，收到 {type(value).__name__}，"
        "无法完成输出身份隔离校验",
        "根因: output_file 参数形态非法，输出身份比对未执行。\n"
        "修复策略: 将 output_file 改为有效路径",
    )]
def _is_blank_path(value: Any) -> bool:
    return isinstance(value, str) and not value.strip()
def _norm_merge_path(p: str) -> str:
    if _is_blank_path(p):
        return ""
    return os.path.normcase(os.path.abspath(os.path.normpath(p)))
def _ms02_issue(severity: str, message: str, suggestion: str,
                filepath: str = "", line: int = 0) -> dict:
    return {
        "detector_id": "MS02",
        "pattern_name": "合并自保护",
        "severity": severity,
        "filepath": filepath,
        "file": filepath,
        "line": line,
        "message": message,
        "suggestion": suggestion,
    }
def _same_merge_file(first: str, second: str) -> bool:
    if _norm_merge_path(first) == _norm_merge_path(second):
        return True
    try:
        return os.path.samefile(first, second)
    except (OSError, ValueError):
        return False
def _check_output_in_delete_list(
        output_file: str, delete_paths: list[str]) -> list[dict]:
    if any(_same_merge_file(output_file, path) for path in delete_paths):
        return [_ms02_issue(
            "CRITICAL",
            f"输出文件 '{output_file}' 也在删除列表中! 合并后会立即丢失.",
            f"根因: 输出文件同处删除列表, 产物会被立即删除。\n"
            f"修复策略: 从 delete_list 移除 '{output_file}'",
            output_file,
        )]
    return []
def _check_merge_source_distinct(
        merge_paths: list[str], output_file: str) -> list[dict]:
    issues: list[dict] = []
    for f in merge_paths:
        if not _same_merge_file(f, output_file):
            continue
        issues.append(_ms02_issue(
            "CRITICAL",
            f"合并源文件 '{f}' 与输出文件相同, 会导致自引用循环",
            '根因: 合并源与输出路径相同, 合并会形成自引用。\n'
            '修复策略: 指定不同的输出名',
            f,
        ))
    return issues
def _check_merge_files_exist(merge_paths: list[str]) -> list[dict]:
    issues: list[dict] = []
    for f in merge_paths:
        if not os.path.exists(f):
            issues.append(_ms02_issue(
                "ERROR",
                f"待合并文件 '{f}' 不存在",
                '根因: 待合并文件不存在, 合并将失败。\n修复策略: 核对 merge_files 路径',
                f,
            ))
        elif not os.path.isfile(f):
            issues.append(_ms02_issue(
                "ERROR",
                f"待合并路径 '{f}' 不是文件",
                '根因: 合并源必须是可读取文件, 目录等路径不能参与合并。\n'
                '修复策略: 核对 merge_files 文件路径',
                f,
            ))
    return issues
def detect_all_new(root_dir: str, include_file=None, skip_keys=None) -> dict:
    results = {
        "D20_merge_preflight": [],
        "D21_unicode_safety": [],
    }
    raw_root = root_dir
    root_dir = coerce_path_str(root_dir)
    if not root_dir.strip():
        logger.warning("[Antipattern] detect_all_new: root_dir 应为非空路径字符串,"
                       " 收到 %r, 按零检出降级", raw_root)
        return results
    if not os.path.isdir(root_dir):
        logger.warning("[Antipattern] detect_all_new: root_dir 不是目录,"
                       " 按零检出降级: %s", root_dir)
        return results
    _skip = _normalize_skip_keys(skip_keys)
    include_file = _normalize_include_file(include_file)
    if "D20_merge_preflight" not in _skip:
        results["D20_merge_preflight"] = _detect_merge_preflight_issues(root_dir)
    if "D21_unicode_safety" not in _skip:
        for fpath in _walk_python_files(
                root_dir,
                lambda d: _is_scan_dirname(
                    d, _SCAN_PRUNE_DIRNAMES, include_tests=True),
                include_file):
            results["D21_unicode_safety"].extend(check_unicode_safety(fpath))
    _d20_n = len(results["D20_merge_preflight"])
    _d21_n = len(results["D21_unicode_safety"])
    if _d20_n or _d21_n:
        logger.warning("[Antipattern] detect_all_new 检出: root=%s D20=%d D21=%d",
                     root_dir, _d20_n, _d21_n)
    else:
        logger.info("[Antipattern] detect_all_new 零检出: root=%s", root_dir)
    return results
def _normalize_skip_keys(skip_keys) -> set:
    if skip_keys is None:
        return set()
    if isinstance(skip_keys, (set, frozenset, list, tuple)):
        kept = {k for k in skip_keys if isinstance(k, str)}
        dropped = sum(1 for k in skip_keys if not isinstance(k, str))
        if dropped:
            logger.warning(
                "[Antipattern] detect_all_new: skip_keys 内含非 str 键"
                " %d 个，已剔除", dropped)
        return kept
    logger.warning(
        "[Antipattern] detect_all_new: skip_keys 应为键集合"
        "（set/frozenset/list/tuple），收到 %s，按 None 降级",
        type(skip_keys).__name__)
    return set()
def _normalize_include_file(include_file) -> Callable[[str], bool] | None:
    if include_file is not None and not callable(include_file):
        logger.warning(
            "[Antipattern] detect_all_new: include_file 应为可调用"
            "谓词，收到 %s，按 None 降级", type(include_file).__name__)
        return None
    return include_file
_D20_MAX_REPORTED_CYCLES = 20
def _detect_merge_preflight_issues(root_dir: str) -> list[dict]:
    checker = MergePreflightChecker(root_dir)
    checker.build_graph()
    cycles = find_graph_cycles(checker.import_graph)
    if len(cycles) > _D20_MAX_REPORTED_CYCLES:
        logger.warning(
            "[Antipattern] D20 循环依赖超出上报上限: 实测 %d 个环,"
            " 仅上报前 %d 个, 截断 %d 个",
            len(cycles), _D20_MAX_REPORTED_CYCLES,
            len(cycles) - _D20_MAX_REPORTED_CYCLES)
    d20_issues = []
    for cycle in cycles[:_D20_MAX_REPORTED_CYCLES]:
        _head = cycle[0] if cycle else ""
        d20_issues.append({
            "detector_id": "D20",
            "pattern_name": "合并前循环依赖",
            "severity": "P2",
            "filepath": _head,
            "file": _head,
            "line": 0,
            "message": f"导入图循环依赖环({len(cycle) - 1}节点): {' -> '.join(cycle)}",
            "suggestion": "根因: 模块间存在循环导入。该问题属于架构质量类别。\n修复策略: 通过依赖下沉/接口提取消除环\n参考标准: PEP 8",
        })
    return d20_issues
IMPORT_SCAN_SKIP_DIRS = _SCAN_PRUNE_DIRNAMES
_IMPORT_SCAN_MAX_FILES = 4000
_IMPORT_STMT_FROM_RE = re.compile(r"(?:^|[\n;:])\s*from\s+([\.\w]+?)\s*import\b")
_IMPORT_STMT_PLAIN_RE = re.compile(r"(?:^|[\n;:])\s*import\s+([^\n#;]+)")
_PACKAGE_IMPORT_INDEX: dict[
    str, tuple[float, tuple, dict[str, list[str]], bool, bool]] = {}
_PACKAGE_INDEX_TTL = 120.0
_PACKAGE_INDEX_MAX_ENTRIES = 32
@dataclass
class _ScanEvidence:
    complete: bool = True
    def walk_error(self, exc: OSError) -> None:
        self.complete = False
        _log_walk_error(exc)
def _package_import_snapshot(
    package_dir: str, evidence: _ScanEvidence,
) -> tuple:
    limit = max(0, _IMPORT_SCAN_MAX_FILES)
    snapshot = []
    for fp in _iter_scannable_py(package_dir, evidence.walk_error):
        snapshot.append((fp, stat_fingerprint(
            fp, 'package_import_snapshot:OSError')))
        if len(snapshot) > limit:
            break
    return tuple(snapshot)
def _build_package_import_index(
        package_dir: str) -> tuple[dict[str, list[str]], bool, bool]:
    now = time.time()
    evidence = _ScanEvidence()
    cache_key = os.path.normcase(os.path.abspath(package_dir))
    snapshot = _package_import_snapshot(package_dir, evidence)
    hit = _PACKAGE_IMPORT_INDEX.get(cache_key)
    if (hit is not None and now - hit[0] < _PACKAGE_INDEX_TTL
            and hit[1] == snapshot):
        return hit[2], hit[3], hit[4] and evidence.complete
    limit = max(0, _IMPORT_SCAN_MAX_FILES)
    index: dict[str, set[str]] = {}
    scanned = 0
    truncated = len(snapshot) > limit
    for fp, _fingerprint in snapshot[:limit]:
        scanned += 1
        content = read_cached(fp)
        if content is None:
            evidence.complete = False
            logger.warning("[SplitDep] 包导入索引读取失败，证据不完整: %s", fp)
            continue
        _index_file_imports(
            index, fp, content, import_root=os.path.dirname(package_dir),
            evidence=evidence)
    result = {k: sorted(v) for k, v in index.items()}
    if (cache_key not in _PACKAGE_IMPORT_INDEX
            and len(_PACKAGE_IMPORT_INDEX) >= _PACKAGE_INDEX_MAX_ENTRIES):
        _PACKAGE_IMPORT_INDEX.pop(next(iter(_PACKAGE_IMPORT_INDEX)))
    _PACKAGE_IMPORT_INDEX[cache_key] = (
        now, snapshot, result, truncated, evidence.complete)
    logger.debug("[SplitDep] 包导入索引构建: %s 模块键=%d 扫描文件=%d%s",
                 package_dir, len(result), scanned,
                 " (截断)" if truncated else "")
    return result, truncated, evidence.complete
def _iter_scan_targets(
    scan_dirs: list[str], exclude_norm: str | None,
    on_error: Callable[[OSError], None],
):
    seen: set[str] = set()
    for scan_dir in scan_dirs:
        if not scan_dir or not os.path.isdir(scan_dir):
            continue
        yield from _iter_unique_scan_files(
            scan_dir, seen, exclude_norm, on_error)
def _iter_unique_scan_files(
    scan_dir: str, seen: set[str], exclude_norm: str | None,
    on_error: Callable[[OSError], None],
):
    for fp in _iter_scannable_py(scan_dir, on_error):
        fp_norm = os.path.normcase(fp)
        if fp_norm in seen or fp_norm == exclude_norm:
            continue
        seen.add(fp_norm)
        yield fp
def _scan_importers_bounded(
    module_candidates: set[str], scan_dirs: list[str], exclude_path: str,
    max_files: int | None = None, import_root: str | None = None,
) -> tuple[list[str], bool, bool]:
    limit = max(0, _IMPORT_SCAN_MAX_FILES if max_files is None else max_files)
    norm_candidates = {c.lstrip(".") for c in module_candidates}
    norm_candidates.discard("")
    if not norm_candidates:
        return [], False, True
    exclude_norm = (os.path.normcase(os.path.abspath(exclude_path))
                    if exclude_path else None)
    evidence = _ScanEvidence()
    importers: list[str] = []
    scanned = 0
    for fp in _iter_scan_targets(
            scan_dirs, exclude_norm, evidence.walk_error):
        scanned += 1
        if scanned > limit:
            return importers, True, evidence.complete
        content = read_cached(fp)
        if content is None:
            evidence.complete = False
            logger.warning("[SplitDep] 导入方读取失败，证据不完整: %s", fp)
            continue
        if _content_imports_any(
                content, norm_candidates, importer_path=fp,
                import_root=import_root, evidence=evidence):
            importers.append(fp)
    return importers, False, evidence.complete
def _iter_scannable_py(
    root: str, on_error: Callable[[OSError], None],
):
    for fp in _walk_python_files(
            root, lambda d: _is_scan_dirname(
                d, IMPORT_SCAN_SKIP_DIRS, include_tests=True),
            on_error=on_error):
        yield os.path.abspath(fp)
def _iter_unmasked_import_matches(pattern: re.Pattern[str], content: str):
    masked_spans = scan_masked_spans(content, True)
    for match in pattern.finditer(content):
        if not is_masked_offset(masked_spans, match.start(1)):
            yield match
def _ast_import_records(
    content: str,
) -> tuple[list[str], list[tuple[str, list[str]]]] | None:
    try:
        tree = ast.parse(content)
    except (SyntaxError, ValueError, RecursionError, MemoryError):
        return None
    plain: list[str] = []
    from_imports: list[tuple[str, list[str]]] = []
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            plain.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            module = "." * node.level + (node.module or "")
            from_imports.append(
                (module, [alias.name for alias in node.names]))
    return plain, from_imports
def _regex_import_records(
    content: str,
) -> tuple[list[str], list[tuple[str, list[str]]]]:
    from_imports = [
        (m.group(1), _iter_from_symbol_names(content, m))
        for m in _iter_unmasked_import_matches(_IMPORT_STMT_FROM_RE, content)
    ]
    plain = [
        name
        for m in _iter_unmasked_import_matches(_IMPORT_STMT_PLAIN_RE, content)
        for name in _iter_plain_import_names(content, m)
    ]
    return plain, from_imports
def _import_records(
    content: str, evidence: _ScanEvidence | None = None,
) -> tuple[list[str], list[tuple[str, list[str]]]]:
    records = _ast_import_records(content)
    if records is not None:
        return records
    if evidence is not None:
        evidence.complete = False
    return _regex_import_records(content)
def _module_name_and_ancestors(name: str) -> Iterator[str]:
    parts = name.split(".")
    for end in range(len(parts), 0, -1):
        yield ".".join(parts[:end])
def _file_package_name(fpath: str, import_root: str | None = None) -> str:
    package_dir = os.path.dirname(fpath)
    package_root = _resolve_package_root(package_dir)
    anchored = os.path.isfile(os.path.join(package_root, "__init__.py"))
    base_dir = (os.path.dirname(package_root) if anchored or not import_root
                else import_root)
    rel = os.path.relpath(package_dir, base_dir)
    return ".".join(
        part for part in rel.replace("\\", "/").split("/")
        if part and part != ".")
def _relative_import_candidate_names(
    module: str, symbols: list[str], importer_path: str,
    import_root: str | None = None,
) -> Iterator[str]:
    level = len(module) - len(module.lstrip("."))
    mod_key = module[level:]
    package_parts = [
        p for p in _file_package_name(importer_path, import_root).split(".") if p]
    ascend = level - 1
    if not package_parts or ascend >= len(package_parts):
        return
    base_parts = (package_parts[:-ascend] if ascend else package_parts)
    if mod_key:
        base_parts = [*base_parts, *mod_key.split(".")]
    base = ".".join(base_parts)
    if not base:
        return
    yield from _module_name_and_ancestors(base)
    for symbol in symbols:
        if symbol and symbol != "*":
            yield f"{base}.{symbol}"
def _iter_import_candidate_names(
    plain: list[str], from_imports: list[tuple[str, list[str]]],
    importer_path: str | None = None, import_root: str | None = None,
) -> Iterator[str]:
    for name in plain:
        if name:
            yield from _module_name_and_ancestors(name)
    for module, symbols in from_imports:
        relative = module.startswith(".")
        if relative and importer_path:
            yield from _relative_import_candidate_names(
                module, symbols, importer_path, import_root)
            continue
        mod_key = module.lstrip(".")
        if mod_key:
            if relative:
                yield mod_key
            else:
                yield from _module_name_and_ancestors(mod_key)
        for symbol in symbols:
            if not symbol or symbol == "*":
                continue
            if mod_key:
                yield f"{mod_key}.{symbol}"
            elif relative:
                yield symbol
def _index_file_imports(
        index: dict[str, set[str]], fp: str, content: str,
        import_root: str | None = None,
        evidence: _ScanEvidence | None = None) -> None:
    plain, from_imports = _import_records(content, evidence=evidence)
    for name in _iter_import_candidate_names(
            plain, from_imports, importer_path=fp, import_root=import_root):
        index.setdefault(name, set()).add(fp)
def _tail_code_line(content: str, pos: int) -> tuple[str, int]:
    nl = content.find("\n", pos)
    if nl == -1:
        return content[pos:].split("#", 1)[0], -1
    return content[pos:nl].split("#", 1)[0], nl + 1
def _collect_import_head(content: str, head: str, pos: int) -> str:
    parenthesized = "(" in head and ")" not in head
    continued = head.rstrip().endswith("\\")
    if not parenthesized and not continued:
        return head
    collected = [head]
    while pos != -1:
        line, pos = _tail_code_line(content, pos)
        collected.append(line)
        if parenthesized and ")" in line:
            break
        if not parenthesized and not line.rstrip().endswith("\\"):
            break
    else:
        return head
    return re.sub(r"\\[ \t]*(?:\r\n|\r|\n)", " ", "\n".join(collected))
def _iter_from_symbol_names(content: str, m) -> list[str]:
    code_line, pos = _tail_code_line(content, m.end())
    head = _collect_import_head(content, code_line, pos).split(";", 1)[0]
    names: list[str] = []
    skip_next = False
    for tok in re.split(r"[,\s()]+", head):
        if not tok or tok == "*":
            continue
        if tok == "as":
            skip_next = True
            continue
        if skip_next:
            skip_next = False
            continue
        names.append(tok)
    return names
def _iter_plain_import_names(content: str, m) -> list[str]:
    next_line = m.end() + (content.startswith("\n", m.end()))
    head = _collect_import_head(
        content, m.group(1), next_line).split(";", 1)[0]
    names: list[str] = []
    for part in head.split(","):
        toks = part.strip().strip("()").split()
        if toks:
            names.append(toks[0])
    return names
def _content_imports_any(
    content: str, norm_candidates: set[str], importer_path: str | None = None,
    import_root: str | None = None,
    evidence: _ScanEvidence | None = None,
) -> bool:
    plain, from_imports = _import_records(content, evidence=evidence)
    return any(
        name in norm_candidates
        for name in _iter_import_candidate_names(
            plain, from_imports, importer_path=importer_path,
            import_root=import_root)
    )
def _resolve_package_root(start_dir: str) -> str:
    d = start_dir
    while os.path.isfile(os.path.join(d, "__init__.py")):
        parent = os.path.dirname(d)
        if parent == d or not os.path.isfile(os.path.join(parent, "__init__.py")):
            break
        d = parent
    if os.path.isfile(os.path.join(d, "__init__.py")):
        return d
    parent = os.path.dirname(start_dir)
    probe = start_dir
    while parent and parent != probe:
        if os.path.isfile(os.path.join(parent, "__init__.py")):
            root = parent
            while True:
                upper = os.path.dirname(root)
                if (upper == root
                        or not os.path.isfile(os.path.join(upper, "__init__.py"))):
                    break
                root = upper
            return root
        probe, parent = parent, os.path.dirname(parent)
    return d
def _relpath_within(path: str, root: str) -> str | None:
    try:
        rel = os.path.relpath(path, root)
    except ValueError as _e:
        log_swallowed(__name__, _e, context='_relpath_within:ValueError')
        return None
    if rel == ".." or rel.startswith(".." + os.sep):
        return None
    return rel
def _derive_default_search_root(fpath: str) -> str:
    d = os.path.dirname(fpath)
    pkg_root = _resolve_package_root(d)
    if os.path.isfile(os.path.join(pkg_root, "__init__.py")):
        import_root = os.path.dirname(pkg_root)
        project_candidate = os.path.dirname(import_root)
        detected_package = detect_layout(project_candidate).package_root
        if (detected_package
                and os.path.normcase(os.path.abspath(detected_package))
                == os.path.normcase(os.path.abspath(pkg_root))):
            return project_candidate
        return import_root if import_root != pkg_root else pkg_root
    return resolve_search_root(d)
def _load_target_tree(fpath: str) -> tuple[ast.Module | None, dict | None]:
    if not os.path.isfile(fpath):
        return None, {"safe_to_split": False, "error": "file not found"}
    try:
        with open(fpath, "rb") as f:
            source = decode_source(f.read())
    except OSError as e:
        logger.warning("[SplitDep] 读取 %s 失败: %s", fpath, e)
        return None, {"safe_to_split": False, "error": f"read failed: {e}"}
    if source is None:
        logger.warning("[SplitDep] %s 编码声明非法或不可解码", fpath)
        return None, {"safe_to_split": False,
                      "error": "read failed: 非法编码声明或不可解码"}
    tree, exc = parse_ast_safely(source)
    if exc is not None:
        logger.warning("[SplitDep] %s 语法错误,跳过: %s", fpath, exc)
        return None, {"safe_to_split": False, "error": "syntax error"}
    return tree, None
def _covers_search_root(root: str, paths: tuple[str, ...]) -> bool:
    return all(_relpath_within(path, root) is not None for path in paths)
def _resolve_search_root(fpath: str, package_dir: str,
                         project_root: Any) -> str:
    explicit = coerce_path_str(project_root)
    if project_root is not None and not explicit:
        logger.warning(
            "[SplitDep] project_root 应为路径, 收到 %s, 按未提供处理",
            type(project_root).__name__)
    if not explicit:
        return _derive_default_search_root(fpath)
    explicit = os.path.abspath(explicit)
    if os.path.isdir(explicit) and _covers_search_root(
            explicit, (fpath, package_dir)):
        return explicit
    search_root = resolve_search_root(explicit)
    if _covers_search_root(search_root, (fpath, package_dir)):
        return search_root
    logger.warning(
        "[SplitDep] project_root=%s 解析的 search_root=%s 未同时覆盖"
        "目标文件 %s 与其包根 %s，降级默认推断",
        project_root, search_root, fpath, package_dir)
    return _derive_default_search_root(fpath)
def _collect_import_lists(tree: ast.Module) -> list[str]:
    imports: list[str] = []
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            imports.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imports.append(node.module)
    return imports
def _split_module_identity(rel_path: str) -> tuple[str, str]:
    stem = os.path.splitext(rel_path)[0]
    parts = [p for p in stem.replace("\\", "/").split("/") if p]
    if parts and parts[-1] == "__init__":
        parts = parts[:-1]
    if not parts:
        return "", ""
    return ".".join(parts), parts[-1]
def _importer_candidates(package_dir: str, rel_dotted: str,
                         base_name: str, dotted_full: str | None = None
                         ) -> set[str]:
    pkg_prefix = os.path.basename(package_dir)
    candidates = {base_name, rel_dotted}
    if rel_dotted:
        candidates.add(f"{pkg_prefix}.{rel_dotted}")
    if dotted_full is not None:
        candidates.add(dotted_full)
    candidates.discard("")
    return candidates
def _relativize_imported_by(paths: Any, root: str) -> list[str]:
    return sorted({os.path.relpath(p, root).replace("\\", "/")
                   for p in paths})
def _collect_importers_intra(
    fpath: str, package_dir: str, rel_dotted: str, base_name: str,
) -> tuple[str, str, list[str], bool, bool]:
    search_root = package_dir
    pkg_path = os.path.relpath(fpath, search_root).replace("\\", "/")
    candidates = _importer_candidates(package_dir, rel_dotted, base_name)
    index, truncated, evidence_complete = _build_package_import_index(package_dir)
    importer_set: set[str] = set()
    for cand in candidates:
        importer_set.update(index.get(cand, []))
    fpath_norm = os.path.normcase(fpath)
    importer_set = {p for p in importer_set
                    if os.path.normcase(p) != fpath_norm}
    imported_by = _relativize_imported_by(importer_set, package_dir)
    return search_root, pkg_path, imported_by, truncated, evidence_complete
def _collect_importers_textscan(
    fpath: str, package_dir: str, search_root: str, rel_dotted: str,
    base_name: str,
) -> tuple[str, str, list[str], bool, bool]:
    pkg_path = os.path.relpath(fpath, search_root).replace("\\", "/")
    dotted_full, _ = _split_module_identity(pkg_path)
    candidates = _importer_candidates(package_dir, rel_dotted, base_name,
                                     dotted_full)
    scan_dirs = [package_dir]
    if os.path.abspath(search_root) != os.path.abspath(package_dir):
        scan_dirs.append(search_root)
    imported_by_abs, truncated, evidence_complete = _scan_importers_bounded(
        candidates, scan_dirs, exclude_path=fpath, import_root=search_root)
    imported_by = _relativize_imported_by(imported_by_abs, search_root)
    return search_root, pkg_path, imported_by, truncated, evidence_complete
def _collect_importers(
    fpath: str, package_dir: str, search_root: str, intra_package_only: bool,
) -> tuple[str, str, list[str], bool, bool]:
    rel_posix = os.path.relpath(fpath, package_dir).replace("\\", "/")
    rel_dotted, base_name = _split_module_identity(rel_posix)
    if not rel_dotted:
        rel_dotted = base_name = os.path.basename(os.path.normpath(package_dir))
    if intra_package_only:
        return _collect_importers_intra(fpath, package_dir, rel_dotted,
                                        base_name)
    return _collect_importers_textscan(fpath, package_dir, search_root,
                                       rel_dotted, base_name)
_STDLIB_MODULE_NAMES = frozenset(getattr(sys, "stdlib_module_names", ()))
def _module_candidates(base_dir: str | Path, module: str) -> tuple[str, ...]:
    if not module:
        return ()
    rel = module.replace(".", os.sep)
    base = Path(base_dir)
    return (str(base / f"{rel}.py"), str(base / rel / "__init__.py"))
def _module_file_path(directory: str, dotted: str) -> str | None:
    for candidate in _module_candidates(directory, dotted):
        if os.path.isfile(candidate):
            return _norm_merge_path(candidate)
    return None
def _import_target_path(module: str, level: int,
                        dirpath: str) -> tuple[str | None, bool]:
    if level:
        base = dirpath
        for _ in range(level - 1):
            base = os.path.dirname(base)
            if not base:
                return None, False
        return _module_file_path(base, module), bool(module)
    top = module.split('.')[0] if module else ''
    if not top:
        return None, False
    directory = dirpath
    while True:
        if _module_target_exists(directory, top):
            return _module_file_path(directory, module), True
        parent = os.path.dirname(directory)
        if parent == directory:
            return None, False
        directory = parent
def _target_import_edges(tree: ast.Module,
                         dirpath: str) -> tuple[dict[str, str], bool]:
    edges: dict[str, str] = {}
    complete = True
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                path, internal = _import_target_path(alias.name, 0, dirpath)
                if path is None:
                    complete = complete and not internal
                    continue
                edges.setdefault(path, alias.name)
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        if node.level and not node.module:
            aliases = [alias for alias in node.names if alias.name != "*"]
            binds_only_submodules = (
                len(aliases) == len(node.names)
                and all(_import_target_path(
                    alias.name, node.level, dirpath)[0] is not None
                    for alias in aliases))
            # 同 _record_import_node：仅当符号可能来自父包 __init__ 时保留该边。
            if not binds_only_submodules:
                package_init, _internal = _import_target_path(
                    "__init__", node.level, dirpath)
                if package_init is not None:
                    edges.setdefault(package_init, "__init__")
        required: tuple[str, ...] = (
            (node.module,) if node.module else ())
        optional = tuple(
            f"{node.module}.{alias.name}"
            if node.module else alias.name
            for alias in node.names
            if alias.name != "*")
        for name in required:
            path, internal = _import_target_path(name, node.level, dirpath)
            if path is None:
                complete = complete and not internal
                continue
            edges.setdefault(path, name)
        for name in optional:
            path, _internal = _import_target_path(name, node.level, dirpath)
            if path is not None:
                edges.setdefault(path, name)
    return edges, complete
_SPLIT_RISKY_DEPENDENTS = 10
_SPLIT_CAUTION_DEPENDENTS = 5
def _escalate_split_risk(recommendation: str, warning: str,
                         reason: str) -> tuple[str, str]:
    if recommendation == "safe":
        return "caution", reason
    return recommendation, f"{warning}；{reason}" if warning else reason
def _build_split_impact(imported_by: list[str], imports: list[str],
                        circular_risk: list[str], truncated: bool,
                        evidence_complete: bool) -> tuple[dict, str]:
    if len(imported_by) > _SPLIT_RISKY_DEPENDENTS:
        recommendation, warning = "risky", (
            f"文件被 {len(imported_by)} 个外部文件导入,"
            "拆分后需更新所有导入路径"
        )
    elif len(imported_by) > _SPLIT_CAUTION_DEPENDENTS:
        recommendation, warning = "caution", (
            f"文件被 {len(imported_by)} 个外部文件导入,拆分需同步更新导入方"
        )
    else:
        recommendation, warning = "safe", ""
    if circular_risk:
        recommendation, warning = _escalate_split_risk(
            recommendation, warning,
            f"检测到 {len(circular_risk)} 组双向导入环，拆分前需先断环")
    if truncated:
        recommendation, warning = _escalate_split_risk(
            recommendation, warning,
            "扫描已截断，依赖证据不完整，无法确认拆分安全")
    if not evidence_complete:
        recommendation, warning = _escalate_split_risk(
            recommendation, warning,
            "部分导入方无法读取或解析，循环依赖证据不完整")
    split_impact = {
        "imported_by_count": len(imported_by),
        "import_count": len(imports),
        "external_dependents": imported_by[:_SPLIT_RISKY_DEPENDENTS],
        "recommendation": recommendation,
    }
    if warning:
        split_impact["warning"] = warning
    if circular_risk:
        split_impact["circular_count"] = len(circular_risk)
    if truncated:
        split_impact["scan_truncated"] = True
    if not evidence_complete:
        split_impact["analysis_incomplete"] = True
    return split_impact, recommendation
@dataclass(frozen=True)
class _SplitFacts:
    pkg_path: str
    imports: list[str]
    imported_by: list[str]
    split_impact: dict
    circular_risk: list[str]
    recommendation: str
    truncated: bool
    evidence_complete: bool
    safe_to_split: bool
def _collect_circular_risks(imported_by: list[str], search_root: str,
                            tree: ast.Module, dirpath: str,
                            pkg_path: str) -> tuple[list[str], bool]:
    edges, evidence_complete = _target_import_edges(tree, dirpath)
    risks: list[str] = []
    for importer in imported_by:
        evidence = edges.get(_norm_merge_path(
            os.path.join(search_root, importer)))
        if evidence is None:
            continue
        risks.append(f"{importer} <-> {pkg_path} (via {evidence})")
    return risks, evidence_complete
def _log_split_facts(facts: _SplitFacts) -> None:
    logger.info("[SplitDep] 拆分依赖分析完成: %s — 导入方=%d 导入=%d "
                "环风险=%d 建议=%s safe_to_split=%s%s%s",
                facts.pkg_path, len(facts.imported_by), len(facts.imports),
                len(facts.circular_risk), facts.recommendation,
                facts.safe_to_split,
                " (扫描截断)" if facts.truncated else "",
                "" if facts.evidence_complete else " (证据不完整)")
def _split_facts_payload(facts: _SplitFacts) -> dict:
    return {
        "filepath": facts.pkg_path,
        "imports": facts.imports,
        "imported_by": facts.imported_by,
        "split_impact": facts.split_impact,
        "circular_risk": facts.circular_risk,
        "safe_to_split": facts.safe_to_split,
    }
def analyze_dependencies_before_split(
        filepath: str, project_root: str | os.PathLike | None = None,
        intra_package_only: bool = _GRAPH_DEFAULT_OPTIONS[
            "intra_package_only"],
) -> dict:
    raw_path = coerce_path_str(filepath)
    if not raw_path.strip():
        logger.warning("[SplitDep] filepath 应为非空路径, 收到 %r",
                       type(filepath).__name__)
        return {"safe_to_split": False,
                "error": "invalid parameters: filepath not a path str"}
    fpath = os.path.abspath(raw_path)
    tree, err = _load_target_tree(fpath)
    if err is not None:
        return err
    package_dir = _resolve_package_root(os.path.dirname(fpath))
    search_root = _resolve_search_root(fpath, package_dir, project_root)
    imports = _collect_import_lists(tree)
    search_root, pkg_path, imported_by, truncated, scan_complete = (
        _collect_importers(
            fpath, package_dir, search_root, intra_package_only))
    circular_risk, target_complete = _collect_circular_risks(
        imported_by, search_root, tree, os.path.dirname(fpath), pkg_path)
    evidence_complete = scan_complete and target_complete
    split_impact, recommendation = _build_split_impact(
        imported_by, imports, circular_risk, truncated, evidence_complete)
    facts = _SplitFacts(
        pkg_path=pkg_path, imports=imports, imported_by=imported_by,
        split_impact=split_impact, circular_risk=circular_risk,
        recommendation=recommendation, truncated=truncated,
        evidence_complete=evidence_complete,
        safe_to_split=(recommendation == "safe" and not truncated
                       and evidence_complete))
    _log_split_facts(facts)
    return _split_facts_payload(facts)
def _module_target_exists(base_dir: str, top: str) -> bool:
    return any(os.path.isfile(path)
               for path in _module_candidates(base_dir, top))
def _is_project_internal_top(top: str, dirpath: str) -> bool:
    d = dirpath
    while True:
        if _module_target_exists(d, top):
            return True
        parent = os.path.dirname(d)
        if parent == d:
            return False
        d = parent
def _relative_import_target_verdict(dirpath: str, level: int,
                                    imported_top: str) -> bool | None:
    _base = dirpath
    for _ in range(level - 1):
        _base = os.path.dirname(_base)
        if not _base:
            return None
    if not _module_target_exists(_base, imported_top):
        return None
    _target = os.path.join(_base, imported_top)
    package_root = _resolve_package_root(dirpath)
    return _relpath_within(_target, package_root) is not None
def _count_cross_pkg_imports(tree: ast.Module, dirpath: str,
                              pkg_parts: set) -> int:
    total = 0
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            total += sum(
                _count_cross_pkg_target(
                    alias.name.split('.')[0], 0, dirpath, pkg_parts)
                for alias in node.names)
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        if node.module:
            total += _count_cross_pkg_target(
                node.module.split('.')[0], node.level, dirpath, pkg_parts)
        elif node.level >= 2:
            total += sum(
                _count_cross_pkg_target(
                    alias.name.split('.')[0], node.level, dirpath, pkg_parts)
                for alias in node.names)
    return total
def _count_cross_pkg_target(imported_top: str, level: int, dirpath: str,
                            pkg_parts: set) -> int:
    if level == 1 and (
            os.path.isdir(os.path.join(dirpath, imported_top))
            or os.path.isfile(os.path.join(dirpath, imported_top + '.py'))):
        return 0
    if level >= 2:
        verdict = _relative_import_target_verdict(
            dirpath, level, imported_top)
        if verdict is not None:
            return 0 if verdict else 1
    return 1 if _is_cross_pkg_top(imported_top, dirpath, pkg_parts) else 0
def _is_cross_pkg_top(imported_top: str, dirpath: str, pkg_parts: set) -> bool:
    if imported_top in pkg_parts:
        return False
    return _is_project_internal_top(imported_top, dirpath)
_PROTECTIVE_SPLIT_MAX_LINES = 80
_PROTECTIVE_SPLIT_MIN_CROSS_IMPORTS = 2
def is_protective_split(filepath: str | os.PathLike) -> bool:
    filepath = coerce_path_str(filepath)
    if not filepath:
        return False
    result = ASTUtils.parse_file(filepath)
    if result is None:
        return False
    tree, content = result
    lines = count_lines(content)
    if lines > _PROTECTIVE_SPLIT_MAX_LINES:
        return False
    dirpath = os.path.dirname(os.path.abspath(filepath))
    package_root = _resolve_package_root(dirpath)
    pkg_parts = {os.path.basename(os.path.normpath(package_root))}
    return (_count_cross_pkg_imports(tree, dirpath, pkg_parts)
            >= _PROTECTIVE_SPLIT_MIN_CROSS_IMPORTS)
_CONSOLIDATED_BASENAME = "_consolidated.py"
def _valid_fragment_file_entry(entry: Any) -> bool:
    if not isinstance(entry, dict):
        return False
    path = entry.get("path")
    lines = entry.get("lines")
    return (isinstance(path, str) and bool(path.strip())
            and isinstance(lines, int)
            and not isinstance(lines, bool)
            and lines >= 0)
def _merge_target_existing_lines(target: str) -> int | None:
    if os.path.lexists(target) and not os.path.isfile(target):
        logger.warning(
            "[Antipattern] 合并目标已存在但不是文件, 无法安全写入: %s", target)
        return None
    if not os.path.isfile(target):
        return 0
    content = read_source_cached(target)
    if content is None:
        logger.warning(
            "[Antipattern] 合并目标不可读, 无法确认合并后行数: %s", target)
        return None
    return count_lines(content)
class FragmentConsolidator:
    SMALL_FILE_THRESHOLD = 50
    FRAGMENTATION_THRESHOLD = 0.5
    EXEMPT_PATTERNS = frozenset({
        '__init__.py', '__main__.py', 'setup.py',
        'version.py', '_version.py',
    })
    def detect(self, root_dir: str) -> dict:
        logger.info("[Antipattern] 碎片统计开始 root=%s", root_dir)
        py_files, small_files, total_lines = self._accumulate_fragment_stats(root_dir)
        fragmentation_rate = len(small_files) / max(len(py_files), 1)
        needs = (fragmentation_rate > self.FRAGMENTATION_THRESHOLD
                 and self._has_mergeable_group(small_files))
        logger.info(
            "[Antipattern] 碎片统计完成 root=%s files=%d small=%d "
            "rate=%.4f needs_consolidation=%s",
            root_dir, len(py_files), len(small_files), fragmentation_rate,
            needs)
        return {
            "needs_consolidation": needs,
            "small_file_list": small_files,
            "fragmentation_rate": round(fragmentation_rate, 4),
            "total_files": len(py_files),
            "total_lines": total_lines,
            "small_file_count": len(small_files),
        }
    def _accumulate_fragment_stats(self, root_dir: str) -> tuple[list, list, int]:
        py_files: list = []
        small_files: list = []
        total_lines = 0
        root_dir = coerce_path_str(root_dir)
        if not root_dir.strip() or not os.path.isdir(root_dir):
            logger.warning(
                "[Antipattern] 碎片统计: root 不是目录, 按零统计降级: %s",
                root_dir)
            return py_files, small_files, total_lines
        for fpath in iter_scan_py_files(root_dir):
            py_files.append(fpath)
            _src = read_source_cached(fpath)
            if _src is None:
                logger.warning("[Antipattern] 碎片统计跳过 %s", fpath)
                continue
            n_lines = count_lines(_src)
            total_lines += n_lines
            _entry = self._small_file_entry(fpath, n_lines)
            if _entry is not None:
                small_files.append(_entry)
        return py_files, small_files, total_lines
    def _small_file_entry(self, fpath: str, n_lines: int) -> dict | None:
        if n_lines > self.SMALL_FILE_THRESHOLD:
            return None
        if os.path.basename(fpath).lower() in self.EXEMPT_PATTERNS:
            return None
        try:
            if is_protective_split(fpath):
                return None
        except Exception as _pe:
            logger.warning("[Antipattern] 保护性拆分判断失败，按保护处理并跳过 %s: %s",
                           fpath, _pe, exc_info=True)
            return None
        return {"path": fpath, "lines": n_lines}
    @staticmethod
    def _has_mergeable_group(small_files: list) -> bool:
        groups: dict[str, int] = defaultdict(int)
        for entry in small_files:
            if os.path.basename(entry["path"]) == _CONSOLIDATED_BASENAME:
                continue
            groups[os.path.dirname(entry["path"])] += 1
        return any(count >= 2 for count in groups.values())
    @staticmethod
    def _coerce_fragment_stats(stats: Any) -> dict | None:
        if not isinstance(stats, dict):
            return None
        if not isinstance(stats.get("needs_consolidation"), bool):
            return None
        _sfl = stats.get("small_file_list")
        if not isinstance(_sfl, list):
            return None
        if not all(_valid_fragment_file_entry(entry) for entry in _sfl):
            return None
        return stats
    def generate_merge_plan(self, root_dir: str, stats: dict | None = None) -> list[dict]:
        resolved = self._coerce_fragment_stats(stats)
        if resolved is None:
            if stats is not None:
                logger.warning("[Antipattern] stats 非 detect() 同构形态，回退现场扫描: %r",
                             type(stats).__name__)
            resolved = self.detect(root_dir)
        if not resolved["needs_consolidation"]:
            return []
        plans = self._assemble_dir_group_plans(resolved)
        self._annotate_cycle_safety(plans, root_dir)
        logger.info("[Antipattern] 合并计划产出 root=%s plans=%d cycle_safe=%d",
                  root_dir, len(plans),
                  sum(1 for p in plans if p.get("cycle_safe")))
        return plans
    @staticmethod
    def _assemble_dir_group_plans(stats: dict) -> list[dict]:
        dir_groups: dict[str, list[dict]] = defaultdict(list)
        for f in stats["small_file_list"]:
            dir_groups[os.path.dirname(f["path"])].append(f)
        plans = []
        for d, files in dir_groups.items():
            target = os.path.join(d, _CONSOLIDATED_BASENAME)
            target_id = _norm_merge_path(target)
            sources = [
                f for f in files
                if _norm_merge_path(f["path"]) != target_id
            ]
            if len(sources) < 2:
                continue
            existing = _merge_target_existing_lines(target)
            if existing is None:
                logger.warning(
                    "[Antipattern] 跳过合并计划 %s: 合并目标不可读,"
                    " 无法确认合并后行数是否超限", d)
                continue
            total = sum(f["lines"] for f in sources) + existing
            if total > LINE_LIMIT:
                logger.warning(
                    "[Antipattern] 跳过合并计划 %s: 合并后约 %d 行超过"
                    "单文件上限 %d", d, total, LINE_LIMIT)
                continue
            plans.append({
                "target": target,
                "sources": [f["path"] for f in sources],
                "file_count": len(sources),
                "total_lines": total,
                "strategy": "directory_merge",
            })
        return plans
    def _annotate_cycle_safety(self, plans: list[dict], root_dir: str) -> None:
        if not plans:
            return
        for plan in plans:
            plan.setdefault("cycle_safe", False)
            plan.setdefault("new_cycle_count", 0)
            plan.setdefault("new_cycles", [])
        try:
            checker = MergePreflightChecker(root_dir)
            checker.build_graph()
            for plan in plans:
                merged_mod = module_name_for_path(plan["target"], root_dir)
                src_mods = [module_name_for_path(s, root_dir)
                            for s in plan["sources"]]
                safety = checker.check_merge_safety(src_mods, merged_mod)
                plan["cycle_safe"] = safety.get("safe", False)
                plan["new_cycle_count"] = safety.get("total_new_cycles", 0)
                plan["new_cycles"] = safety.get("new_cycles", [])[:5]
        except Exception as e:  # noqa: BLE001
            logger.warning("[Antipattern] 合并计划循环安全校验失败: %s", e)
CYCLE_PRIORITY_RESTRUCTURE = "restructure"
CYCLE_PRIORITY_TYPE_CHECKING = "type_checking"
CYCLE_PRIORITY_EXTRACT_SHARED = "extract_shared"
CYCLE_PRIORITY_LAZY_IMPORT = "lazy_import"
CYCLE_PRIORITY_ORDER: list[str] = [
    CYCLE_PRIORITY_RESTRUCTURE,
    CYCLE_PRIORITY_TYPE_CHECKING,
    CYCLE_PRIORITY_EXTRACT_SHARED,
    CYCLE_PRIORITY_LAZY_IMPORT,
]
def choose_cycle_fix_priority(
    is_type_only: bool = False,
    restructure_feasible: bool = True,
    extract_feasible: bool = True,
) -> str:
    if restructure_feasible:
        return CYCLE_PRIORITY_RESTRUCTURE
    if is_type_only:
        return CYCLE_PRIORITY_TYPE_CHECKING
    if extract_feasible:
        return CYCLE_PRIORITY_EXTRACT_SHARED
    return CYCLE_PRIORITY_LAZY_IMPORT
def _path_key_index(file_analyses: Mapping[str, Any]) -> dict[str, str]:
    return {_norm_merge_path(path): path
            for path in _str_domain_keys(file_analyses, warn=False)}
def _package_parent_initializers(
    src: str, target: str, path_index: Mapping[str, str],
) -> Iterator[str]:
    source_id = _norm_merge_path(src)
    target_id = _norm_merge_path(target)
    if source_id == target_id:
        return
    parent = os.path.dirname(target_id)
    while True:
        initializer_id = _norm_merge_path(
            os.path.join(parent, "__init__.py"))
        if initializer_id not in {source_id, target_id}:
            initializer = path_index.get(initializer_id)
            # 导入方位于该父包内时父包 __init__ 已在初始化链上，不构成依赖边。
            if (initializer is not None
                    and _relpath_within(source_id, parent) is None):
                yield initializer
        next_parent = os.path.dirname(parent)
        if next_parent == parent:
            break
        parent = next_parent
@dataclass
class _ImportEdgeGraph:
    file_analyses: dict[str, Any]
    full: dict[str, set[str]] = field(
        default_factory=lambda: defaultdict(set))
    module_level: dict[str, set[str]] = field(
        default_factory=lambda: defaultdict(set))
    path_index: dict[str, str] = field(init=False, repr=False)
    def __post_init__(self) -> None:
        self.path_index = _path_key_index(self.file_analyses)
    def record(
        self, src: str, dep_path: str | None, *, module_level: bool,
    ) -> None:
        if not isinstance(dep_path, str) or not dep_path:
            return
        target = self.path_index.get(_norm_merge_path(dep_path))
        if target is None or target == src:
            return
        targets = (
            target,
            *_package_parent_initializers(src, target, self.path_index),
        )
        for dependency in targets:
            self.full[src].add(dependency)
            if module_level:
                self.module_level[src].add(dependency)
    def sink(self, src: str, *, module_level: bool) -> _CycleGraphSink:
        return _CycleGraphSink(self, src, module_level=module_level)
@dataclass(frozen=True)
class _CycleGraphSink:
    graph: _ImportEdgeGraph
    src: str
    module_level: bool
    def add_edge(self, dep_path: str | None) -> None:
        self.graph.record(self.src, dep_path, module_level=self.module_level)
def detect_circular_imports(file_analyses: dict[str, Any]) -> list[list[str]]:
    if not isinstance(file_analyses, Mapping):
        logger.warning(
            "[Cycles] file_analyses 非映射载荷,跳过环检测: %r",
            type(file_analyses).__name__)
        return []
    graph: dict[str, set[str]] = defaultdict(set)
    all_nodes: set[str] = set()
    path_index = _path_key_index(file_analyses)
    for fpath in _str_domain_keys(file_analyses):
        analysis = file_analyses[fpath]
        all_nodes.add(fpath)
        imports = getattr(analysis, "imports_in", None)
        if imports is None:
            logger.warning(
                "[Cycles] 载荷缺 imports_in 属性,跳过其内部依赖边: %s", fpath)
            continue
        for imp_in in _iter_str_entries(imports, label="imports_in", owner=fpath):
            importer = path_index.get(_norm_merge_path(imp_in))
            if importer is not None:
                targets = (
                    fpath,
                    *_package_parent_initializers(importer, fpath, path_index),
                )
                graph[importer].update(targets)
                all_nodes.update(targets)
    return _find_cycles_in_graph(graph, all_nodes)
def _iter_str_entries(
    items: Any, *, label: str, owner: str,
) -> Iterator[str]:
    if isinstance(items, str) or not isinstance(items, _CONTAINER_TYPES):
        logger.warning(
            "[Cycles] %s 非清单形状,跳过整段: %s: %r",
            label, owner, type(items).__name__)
        return
    for item in items:
        if isinstance(item, str):
            yield item
        else:
            logger.warning(
                "[Cycles] %s 含非 str 项,跳过该项: %s: %r",
                label, owner, item)
def _coerce_str_cache(value: Any, label: str) -> dict[str, Any]:
    if value is None:
        return {}
    if isinstance(value, dict):
        return value
    logger.warning("[Cycles] %s 应为 dict, 收到 %s, 按空缓存降级",
                   label, type(value).__name__)
    return {}
def _coerce_import_edges(value: Any) -> Mapping | None:
    if value is None:
        return None
    if not isinstance(value, Mapping):
        logger.warning("[Cycles] import_edges 应为文件→通道映射, 收到 %s, "
                       "改为 AST 遍历", type(value).__name__)
        return None
    invalid_entries = sum(
        not isinstance(edges, Mapping) for edges in value.values())
    if invalid_entries:
        logger.warning(
            "[Cycles] import_edges 含 %d 个非映射文件条目, "
            "证据形状不完整, 改为 AST 遍历", invalid_entries)
        return None
    return value
def detect_circular_imports_stratified(
    file_analyses: dict[str, Any],
    source_cache: dict[str, str] | None = None,
    ast_cache: dict[str, Any] | None = None,
    import_edges: dict[str, dict[str, list[str]]] | None = None,
) -> dict[str, list[list[str]]]:
    if not isinstance(file_analyses, Mapping):
        logger.warning(
            "[Cycles] file_analyses 非映射载荷,跳过分层环检测: %r",
            type(file_analyses).__name__)
        return _cycle_report([], [])
    source_cache = _coerce_str_cache(source_cache, "source_cache")
    ast_cache = _coerce_str_cache(ast_cache, "ast_cache")
    import_edges = _coerce_import_edges(import_edges)
    graph = _ImportEdgeGraph(file_analyses)
    if import_edges is not None:
        _PreCollectedEdgeIngestor(import_edges, graph).ingest()
    else:
        _traverse_ast_import_edges(graph, source_cache, ast_cache)
    return _stratify_cycle_report(
        graph, set(_str_domain_keys(graph.file_analyses)))
def _traverse_ast_import_edges(
    graph: _ImportEdgeGraph,
    source_cache: dict[str, str],
    ast_cache: dict[str, Any] | None,
) -> None:
    common_root = _derive_common_root(graph.file_analyses)
    import_roots = _absolute_import_roots(common_root)
    for fpath_str in _str_domain_keys(graph.file_analyses, warn=False):
        tree = _parse_tree_cached(fpath_str, source_cache, ast_cache)
        if tree is None:
            continue
        skill_dir = Path(fpath_str).parent
        typing_aliases = typing_guard_aliases(tree)
        type_checking_names = typing_type_checking_names(tree)
        stack: list[tuple[ast.AST, bool]] = [
            (child, False) for child in ast.iter_child_nodes(tree)
        ]
        while stack:
            node, lazy = stack.pop()
            if isinstance(node, _LAZY_SCOPE_NODES):
                _push_child_nodes(stack, node, lazy=True)
            elif (isinstance(node, ast.If)
                  and is_type_checking_guard(
                      node.test, typing_aliases, type_checking_names)):
                stack.extend((child, True) for child in node.body)
                stack.extend((child, lazy) for child in node.orelse)
            elif isinstance(node, (ast.ImportFrom, ast.Import)):
                _record_import_node(
                    node, graph.sink(fpath_str, module_level=not lazy),
                    skill_dir, common_root, import_roots)
            else:
                _push_child_nodes(stack, node, lazy=lazy)
def _record_import_node(
    node: ast.Import | ast.ImportFrom,
    sink: _CycleGraphSink,
    skill_dir: Path,
    common_root: Path | None,
    import_roots: tuple[Path, ...],
) -> None:
    if isinstance(node, ast.Import):
        _add_absolute_module_edges(
            [alias.name for alias in node.names],
            sink, common_root, import_roots)
        return
    if not node.level:
        if not node.module:
            _add_absolute_module_edges(
                [a.name for a in node.names], sink, common_root, import_roots)
            return
        # 绝对形式导入自身包 `from pkg import x`：仅当 x 不是已知子模块（可能是
        # pkg/__init__ 定义的名字）或为星号导入时，才保留对自身包 __init__ 的边。
        aliases = [a.name for a in node.names if a.name != "*"]
        keep_own_init = (
            len(aliases) != len(node.names)
            or any(not _binds_non_init_submodule(
                f"{node.module}.{alias}", sink, common_root, import_roots)
                for alias in aliases))
        names = ([node.module]
                 + [f"{node.module}.{a.name}" for a in node.names]
                 if node.module else
                 [a.name for a in node.names])
        _add_absolute_module_edges(
            names, sink, common_root, import_roots,
            keep_own_package_init=keep_own_init)
        return
    base_dir = skill_dir
    for _ in range(node.level - 1):
        base_dir = base_dir.parent
    if not node.module:
        aliases = [alias for alias in node.names if alias.name != "*"]
        deps = [
            resolve_internal_dependency(alias.name, base_dir)
            for alias in aliases]
        # `from . import x` 对父包 __init__ 的边恒真（父包已在初始化链上）；
        # 仅当存在星号导入或某个符号不是子模块（可能是 __init__ 定义的名字）时
        # 显式保留该边（_add_import_edges 会过滤自身包 __init__）。
        if len(aliases) != len(node.names) or any(dep is None for dep in deps):
            sink.add_edge(_dep_path_if_internal(
                "__init__", base_dir, sink.graph.path_index, sink.src))
        _add_import_edges(deps, base_dir, sink)
        return
    _add_import_edges([relative_module_base(node.module)], base_dir, sink)
    alias_base = base_dir.joinpath(*node.module.split("."))
    _add_import_edges(
        [resolve_internal_dependency(alias.name, alias_base)
         for alias in node.names], alias_base, sink)
_LAZY_SCOPE_NODES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
def _push_child_nodes(
    stack: list[tuple[ast.AST, bool]], node: ast.AST, *, lazy: bool
) -> None:
    stack.extend((child, lazy) for child in ast.iter_child_nodes(node))
def _parse_tree_cached(
    fpath_str: str,
    source_cache: dict[str, str],
    ast_cache: dict[str, Any] | None,
) -> ast.Module | None:
    cache: dict[str, Any] = {} if ast_cache is None else ast_cache
    if fpath_str in cache:
        cached = cache[fpath_str]
        if cached is None or isinstance(cached, ast.AST):
            return cached
        logger.warning(
            "[Cycles] ast_cache 预填非 AST 脏值,回退重新解析: %s: %r",
            fpath_str, type(cached).__name__)
    source = _source_from_cache(fpath_str, source_cache)
    if source is None:
        cache[fpath_str] = None
        return None
    try:
        tree = ast.parse(source, filename=fpath_str)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
        logger.warning("[Cycles] 解析源码失败,跳过 %s: %s", fpath_str, e)
        cache[fpath_str] = None
        return None
    cache[fpath_str] = tree
    return tree
def _add_absolute_module_edges(
    names: list[str],
    sink: _CycleGraphSink,
    common_root: Path | None,
    import_roots: tuple[Path, ...],
    *,
    keep_own_package_init: bool = False,
) -> None:
    for name in names:
        path = _resolve_absolute_name_to_file(
            name, common_root, sink.graph.path_index, import_roots)
        if path is None:
            continue
        if (not keep_own_package_init
                and _is_own_package_initializer(path, sink.src)):
            continue
        sink.add_edge(path)
def _is_own_package_initializer(path: str, src: str) -> bool:
    # 模块对包含自身的包（含祖先包）__init__ 的导入边恒真：执行到该模块时父包
    # 已处于初始化链上，`import pkg` / `import pkg.sub` 均为 no-op。
    if os.path.basename(path) != "__init__.py":
        return False
    package_dir = os.path.normcase(os.path.abspath(os.path.dirname(path)))
    current = os.path.normcase(os.path.abspath(os.path.dirname(src)))
    while True:
        if current == package_dir:
            return True
        parent = os.path.dirname(current)
        if parent == current:
            return False
        current = parent
def _binds_non_init_submodule(
        name: str, sink: _CycleGraphSink, common_root: Path | None,
        import_roots: tuple[Path, ...],
) -> bool:
    path = _resolve_absolute_name_to_file(
        name, common_root, sink.graph.path_index, import_roots)
    return path is not None and not _is_own_package_initializer(path, sink.src)
@dataclass(frozen=True)
class _PreCollectedEdgeIngestor:
    import_edges: dict[str, dict[str, list[str]]]
    graph: _ImportEdgeGraph
    def ingest(self) -> None:
        edge_path_index = _path_key_index(self.import_edges)
        for fpath_str in _str_domain_keys(self.graph.file_analyses, warn=False):
            edge_key = edge_path_index.get(_norm_merge_path(fpath_str))
            edges = self.import_edges.get(edge_key) if edge_key is not None else None
            if not isinstance(edges, Mapping):
                if edges:
                    logger.warning(
                        "[Cycles] import_edges 条目非映射形状,跳过该文件: %s: %r",
                        fpath_str, type(edges).__name__)
                continue
            self._ingest_bare(edges.get("all", ()), fpath_str, module_level=False)
            self._ingest_bare(edges.get("module", ()), fpath_str, module_level=True)
            self._ingest_resolved(
                edges.get("resolved", ()), fpath_str, module_level=False)
            self._ingest_resolved(
                edges.get("resolved_module", ()), fpath_str, module_level=True)
    def _ingest_bare(
        self, deps: Any, fpath_str: str, *, module_level: bool,
    ) -> None:
        base_dir = Path(fpath_str).parent
        for dep in _iter_str_entries(
                deps, label="import_edges 裸名通道", owner=fpath_str):
            self.graph.record(
                fpath_str,
                _dep_path_if_internal(
                    dep, base_dir, self.graph.path_index, fpath_str),
                module_level=module_level)
    def _ingest_resolved(
        self, dep_paths: Any, fpath_str: str, *, module_level: bool,
    ) -> None:
        for dep_path in _iter_str_entries(
                dep_paths, label="import_edges resolved 通道", owner=fpath_str):
            self.graph.record(
                fpath_str, dep_path, module_level=module_level)
def _source_from_cache(
    fpath_str: str,
    source_cache: dict[str, str],
) -> str | None:
    if fpath_str in source_cache:
        cached = source_cache[fpath_str]
        if isinstance(cached, str):
            return cached
        logger.warning(
            "[Cycles] source_cache 预填非 str 脏值,回退读盘覆盖: %s: %r",
            fpath_str, type(cached).__name__)
    source = read_cached(fpath_str)
    if source is None:
        logger.warning("[Cycles] 读取/解码源码失败,跳过 %s（解释器同口径）",
                     fpath_str)
        return None
    source_cache[fpath_str] = source
    return source
def _known_module_path(
    module: str,
    base_dir: Path,
    path_index: Mapping[str, str],
) -> str | None:
    for candidate in _module_candidates(base_dir, module):
        key = path_index.get(_norm_merge_path(candidate))
        if key is not None:
            return key
    return None
def _dep_path_if_internal(
    dep: str | None,
    base_dir: Path,
    path_index: Mapping[str, str],
    self_path: str,
) -> str | None:
    if not dep:
        return None
    path = _known_module_path(dep, base_dir, path_index)
    return None if path == self_path else path
def _str_domain_keys(
    file_analyses: Mapping[str, Any], *, warn: bool = True,
) -> Iterator[str]:
    for key in file_analyses:
        if isinstance(key, str):
            yield key
        elif warn:
            logger.warning(
                "[Cycles] file_analyses 含非 str 键,跳过该文件: %r", key)
def _derive_common_root(
    file_analyses: Mapping[str, Any],
) -> Path | None:
    common: Path | None = None
    for fpath_str in _str_domain_keys(file_analyses, warn=False):
        d = Path(fpath_str).parent
        if common is None:
            common = d
            continue
        while common != d and common not in d.parents:
            parent = common.parent
            if parent == common:
                return None
            common = parent
    return common
def _absolute_import_roots(common_root: Path | None) -> tuple[Path, ...]:
    if common_root is None:
        return ()
    package_root = detect_layout(str(common_root)).package_root
    if (not package_root
            or os.path.normcase(os.path.abspath(package_root))
            == os.path.normcase(os.path.abspath(common_root))):
        roots = (common_root,)
    else:
        src_import_root = Path(package_root).parent
        roots = (src_import_root, common_root)
    anchored_root = Path(_resolve_package_root(str(common_root)))
    if (anchored_root != common_root
            and (anchored_root / "__init__.py").is_file()):
        roots += (anchored_root,)
    return roots
def _resolve_absolute_name_to_file(
    name: str | None,
    common_root: Path | None,
    path_index: Mapping[str, str],
    import_roots: tuple[Path, ...] | None = None,
) -> str | None:
    if not name or common_root is None:
        return None
    roots = (import_roots if import_roots is not None
             else _absolute_import_roots(common_root))
    for root in roots:
        parts = name.split('.')
        head = parts[0]
        if head == root.name:
            parts = parts[1:]
            if not parts:
                init = _known_module_path("__init__", root, path_index)
                if init:
                    return init
        if parts:
            found = _known_module_path(
                '/'.join(parts), root, path_index)
            if found:
                return found
        if head != root.name and head in _STDLIB_MODULE_NAMES:
            continue
        dep = resolve_internal_dependency(name, root)
        found = (_known_module_path(dep, root, path_index)
                 if dep else None)
        if found:
            return found
    return None
def _add_import_edges(
    deps: list[str | None],
    base_dir: Path,
    sink: _CycleGraphSink,
) -> None:
    for dep in deps:
        path = _dep_path_if_internal(
            dep, base_dir, sink.graph.path_index, sink.src)
        if path is None or _is_own_package_initializer(path, sink.src):
            continue
        sink.add_edge(path)
def _scc_cycle_path(
    scc_nodes: frozenset[str],
    graph: dict[str, set[str]],
) -> list[str]:
    start = min(scc_nodes, key=str)
    if len(scc_nodes) == 1 and start in graph.get(start, set()):
        return [start, start]
    parent: dict[str, str] = {}
    queue: deque[str] = deque([start])
    while queue:
        current = queue.popleft()
        for nxt in _sorted_neighbors(current, graph.get(current, set())):
            if nxt not in scc_nodes:
                continue
            if nxt == start:
                if current == start and len(scc_nodes) > 1:
                    continue
                return _cycle_chain_to_start(current, start, parent)
            if nxt not in parent:
                parent[nxt] = current
                queue.append(nxt)
    return [start, start]
def _cycle_chain_to_start(
    current: str, start: str, parent: dict[str, str],
) -> list[str]:
    chain = [current]
    cursor = current
    while cursor != start:
        cursor = parent[cursor]
        chain.append(cursor)
    chain.reverse()
    return chain + [start]
def _canonical_cycle_path(path: list[str]) -> list[str]:
    body = path[:-1]
    start = min(range(len(body)), key=lambda i: str(body[i]))
    rotated = body[start:] + body[:start]
    return rotated + [rotated[0]]
def _cycle_path_through_edge(
    start: str, neighbor: str, scc_nodes: frozenset[str],
    graph: dict[str, set[str]],
) -> list[str] | None:
    parent: dict[str, str] = {neighbor: neighbor}
    queue: deque[str] = deque([neighbor])
    while queue:
        current = queue.popleft()
        for nxt in _sorted_neighbors(current, graph.get(current, set())):
            if nxt not in scc_nodes or nxt in parent:
                continue
            parent[nxt] = current
            if nxt != start:
                queue.append(nxt)
                continue
            chain = [start]
            cursor = start
            while cursor != neighbor:
                cursor = parent[cursor]
                chain.append(cursor)
            chain.reverse()
            return _canonical_cycle_path([start, *chain])
    return None
def _lazy_scc_cycle_path(
    scc_nodes: frozenset[str], full: dict[str, set[str]],
    module_level: dict[str, set[str]],
) -> list[str]:
    for src in sorted(scc_nodes, key=str):
        for dst in _sorted_neighbors(src, full.get(src, set())):
            if dst not in scc_nodes or dst in module_level.get(src, set()):
                continue
            path = _cycle_path_through_edge(src, dst, scc_nodes, full)
            if path is not None:
                return path
    return _scc_cycle_path(scc_nodes, full)
def _cycle_sccs(
    graph: dict[str, set[str]],
    all_nodes: set[str],
) -> list[tuple[frozenset[str], list[str]]]:
    domain = set(all_nodes)
    limited: dict[str, set[str]] = {}
    for node in sorted(domain, key=str):
        limited[node] = {
            dst for dst in graph.get(node, set()) if dst in domain
        }
    result: list[tuple[frozenset[str], list[str]]] = []
    for scc in tarjan_scc(limited):
        scc_set = frozenset(scc)
        if len(scc) > 1 or scc[0] in limited.get(scc[0], set()):
            result.append((scc_set, _scc_cycle_path(scc_set, limited)))
    return result
def _find_cycles_in_graph(
    graph: dict[str, set[str]], all_nodes: set[str],
) -> list[list[str]]:
    return [path for _scc, path in _cycle_sccs(graph, all_nodes)]
_CYCLE_REPORT_KEYS = ("module_level_cycles", "lazy_only_cycles")
def _cycle_report(
    module_cycles: list[list[str]],
    lazy_cycles: list[list[str]],
) -> dict[str, list[list[str]]]:
    return dict(zip(_CYCLE_REPORT_KEYS, (module_cycles, lazy_cycles),
                    strict=True))
def _stratify_cycle_report(
    graph: _ImportEdgeGraph,
    all_nodes: set[str],
) -> dict[str, list[list[str]]]:
    module_sccs = _cycle_sccs(graph.module_level, all_nodes)
    module_cycle_sets = {scc for scc, _path in module_sccs}
    full_sccs = _cycle_sccs(graph.full, all_nodes)
    lazy_only_cycles = [
        _lazy_scc_cycle_path(scc, graph.full, graph.module_level)
        for scc, _path in full_sccs
        if scc not in module_cycle_sets
    ]
    return _cycle_report(
        [path for _scc, path in module_sccs], lazy_only_cycles)
@dataclass
class _TarjanState:
    lowlink: dict[str, int] = field(default_factory=dict)
    index: dict[str, int] = field(default_factory=dict)
    on_stack: dict[str, bool] = field(default_factory=dict)
    stack: list[str] = field(default_factory=list)
    result: list[list[str]] = field(default_factory=list)
    counter: int = 0
    def enter(self, node: str) -> None:
        self.index[node] = self.counter
        self.lowlink[node] = self.counter
        self.counter += 1
        self.stack.append(node)
        self.on_stack[node] = True
    def back_edge(self, node: str, neighbor: str) -> None:
        self.lowlink[node] = min(self.lowlink[node], self.index[neighbor])
    def finish(self, node: str, work: list) -> None:
        work.pop()
        if work:
            parent = work[-1][0]
            self.lowlink[parent] = min(
                self.lowlink[parent], self.lowlink[node])
        if self.lowlink[node] == self.index[node]:
            self.result.append(_pop_scc(self.stack, self.on_stack, node))
def _pop_scc(stack: list[str], on_stack: dict[str, bool], root: str) -> list[str]:
    scc: list[str] = []
    while True:
        w = stack.pop()
        on_stack[w] = False
        scc.append(w)
        if w == root:
            break
    return scc
def tarjan_scc(graph: dict[str, set[str]]) -> list[list[str]]:
    if not isinstance(graph, Mapping):
        logger.warning("[Cycles] tarjan_scc 非映射载荷,按空图处理: %r",
                       type(graph).__name__)
        return []
    state = _TarjanState()
    for start in graph:
        if start in state.index:
            continue
        state.enter(start)
        work: list[tuple[str, Any]] = [
            (start, iter(_sorted_neighbors(start, graph.get(start, ()))))]
        while work:
            node, neighbors = work[-1]
            try:
                neighbor = next(neighbors)
            except StopIteration:
                state.finish(node, work)
                continue
            if neighbor not in state.index:
                state.enter(neighbor)
                work.append(
                    (neighbor,
                     iter(_sorted_neighbors(neighbor, graph.get(neighbor, ())))))
            elif state.on_stack.get(neighbor, False):
                state.back_edge(node, neighbor)
    return state.result
def _register_merge_safety_rules() -> None:
    get_registry().register_batch({
        "MS01": check_unicode_safety,
        "MS02": check_merge_self_protection,
    })

from __future__ import annotations

__all__ = [
    'ModuleStructureAnalyzer',
    'analyze_export_consistency',
    'analyze_facade_reachability',
    'analyze_fragmentation',
    'analyze_module_coupling',
    'analyze_structural_health',
    'warn_duplicate_module_stems',
]
import ast
import copy
import fnmatch
import io
import logging
import os
import re
import tokenize
from collections import Counter, deque
from pathlib import Path
from typing import Any

from jwsgj.diag_dependency_analyzer import (
    GENERIC_SCRIPT_MODULES,
    OVERSIZED_THRESHOLD,
    ApiContractAuditor,
    ArchitectureRuleAnalyzer,
    DependencyAnalyzer,
    classify_file_sizes,
)
from jwsgj.diag_dependency_core import (
    Finding,
)
from jwsgj.diag_module_surface import (
    extract_all_surface,
    iter_module_level_imports_tc,
    iter_module_level_nodes_tc,
    relative_import_base,
)
from jwsgj.diag_shared_ast_nodes import (
    _type_checking_guard_node_polarities,
    is_main_check,
    iter_module_level_stmts,
    parse_import_name_list,
    parse_source_tree,
    type_checking_body_node_ids,
)
from jwsgj.diag_shared_source_core import (
    count_lines,
    iter_file_trees,
    read_source,
    read_source_auto,
)
from jwsgj.diag_structure_rules import (
    _SCAN_PRUNE_DIRS,
    FragmentReport,
    _groups_with_fragments,
    _is_exempt_basename,
    detect_fragments,
    format_report,
)
from jwsgj.diag_types_defs import (
    make_a2_finding,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    TEST_DIR_CANDIDATES_LOWER,
    DependencyGraph,
    collect_py_files,
    cycle_member_groups,
    import_key,
    is_runtime_temp_path,
    is_test_file_path,
    prune_scan_dirnames,
    safe_relpath,
)

logger = logging.getLogger(__name__)
_SA_DECL_PAT = re.compile(
    r"独立卫星工具|可独立运行|可脱离技能环境|独立部署"
    r"|\bstandalone\s+(?:tool|script|utility|module|cli)\b"
    r"|\brun\s+independently\b"
    r"|\bindependent(?:ly)?\s+deploy(?:able|ment)?\b",
    re.IGNORECASE)
_LAZY_REGISTRY_MODULE_GLOB = "*lazy*.py"
_LAZY_REGISTRY_NAME_HINTS = (
    "lazy", "table", "registry", "export", "surface", "anchor")
_PACKAGE_ROOT_SKIP_DIRS = frozenset(
    GENERIC_SCAN_IGNORE_DIRS_LOWER | TEST_DIR_CANDIDATES_LOWER)
class _UnknownAllNames:
    __slots__ = ()
_UNKNOWN_ALL_NAMES = _UnknownAllNames()
def _require_structure_root(skill_dir: str) -> str:
    raw = os.fsdecode(os.fspath(skill_dir))
    if not raw.strip():
        raise ValueError("结构分析目标目录不能为空")
    if os.path.isdir(raw):
        return raw
    if os.path.exists(raw):
        raise NotADirectoryError(f"结构分析目标路径非目录: {raw!r}")
    raise FileNotFoundError(f"结构分析目标目录不存在: {raw!r}")
def warn_duplicate_module_stems(
        py_files: list[str], graph_label: str = "D9 依赖图") -> None:
    stem_seen: Counter[str] = Counter(
        os.path.splitext(os.path.basename(fp))[0].lower() for fp in py_files)
    dupes = sorted(s for s, c in stem_seen.items() if c > 1)
    if dupes:
        logger.warning(
            "[ModuleStructureAnalyzer] 递归扫描发现 %d 组同名模块，"
            "%s 按 basename 建节点将合并同名文件（扇入扇出与孤立"
            "模块统计受污染，相关结论不可信）: %s",
            len(dupes), graph_label, ", ".join(dupes[:10]))
def _pkg_import_targets_from_node(
    node: ast.AST, skill_name, source_path: str | None = None,
    skill_dir: str | None = None,
    module_stems: dict[str, str] | None = None,
) -> set[str]:
    path_aware = bool(source_path and skill_dir)
    if isinstance(node, ast.ImportFrom):
        return _pkg_importfrom_targets(
            node, skill_name, source_path, skill_dir, module_stems)
    if isinstance(node, ast.Import):
        return _pkg_plain_import_targets(
            node, skill_name, allow_local=path_aware)
    return set()
def _import_alias_names(node: ast.ImportFrom) -> set[str]:
    return {alias.name for alias in node.names}
def _pkg_importfrom_targets(
    node: ast.ImportFrom, skill_name,
    source_path: str | None, skill_dir: str | None,
    module_stems: dict[str, str] | None,
) -> set[str]:
    module_leaf = (node.module or "").rsplit(".", 1)[-1].lower()
    collect_names = (
        not node.module or module_stems is None or module_leaf not in module_stems)
    if node.level > 0:
        if source_path and skill_dir:
            if relative_import_base(source_path, node.level, skill_dir) is None:
                return set()
            targets = _import_alias_names(node) if collect_names else set()
            if node.module:
                targets.add(node.module.rsplit(".", 1)[-1])
            return targets
        if node.level != 1:
            return set()
        if not node.module:
            return _import_alias_names(node)
    if not node.module:
        return set()
    parts = node.module.split(".")
    same_package = _is_project_package(parts[0], skill_name)
    local_absolute = bool(source_path and skill_dir and len(parts) == 1)
    if not same_package and node.level == 0 and not local_absolute:
        return set()
    targets = (_import_alias_names(node)
               if collect_names and same_package else set())
    if len(parts) > 1 or not same_package:
        targets.add(parts[-1])
    return targets
def _pkg_plain_import_targets(node: ast.Import, skill_name,
                              allow_local: bool) -> set[str]:
    targets: set[str] = set()
    for alias in node.names:
        parts = alias.name.split(".")
        if _is_project_package(parts[0], skill_name) and len(parts) > 1:
            targets.add(parts[-1])
        elif allow_local and len(parts) == 1:
            targets.add(parts[0])
    return targets
def _collect_coupling_py_files(skill_dir: str, ctx=None) -> list[str]:
    return [f for f in collect_py_files(skill_dir, ctx)
            if os.path.basename(f).lower() != "__init__.py"]
def _graph_add_edge(target: str, mod_name: str, bucket: dict[str, set[str]],
                    module_stems: dict[str, str]) -> None:
    _canonical = module_stems.get(target.lower())
    if _canonical is not None and _canonical != mod_name:
        bucket.setdefault(mod_name, set()).add(_canonical)
def _non_runtime_branch_node_ids(tree: ast.Module) -> set[int]:
    excluded = type_checking_body_node_ids(tree)
    guard_polarities = _type_checking_guard_node_polarities(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.If):
            continue
        if isinstance(node.test, ast.Constant):
            body_visible = bool(node.test.value)
        else:
            negated = guard_polarities.get(id(node))
            if negated is None:
                continue
            body_visible = negated
        inactive = node.body if not body_visible else node.orelse
        for stmt in inactive:
            excluded.update(id(child) for child in walk_nodes(stmt))
    return excluded
def _graph_collect_lazy_edges(tree, mod_name: str, skill_name: str,
                              lazy_out: dict[str, set[str]],
                              module_stems: dict[str, str], skill_dir: str,
                              source_path: str,
                              non_runtime_ids: set[int] | None = None) -> None:
    if non_runtime_ids is None:
        non_runtime_ids = _non_runtime_branch_node_ids(tree)
    _stack: list[tuple[ast.AST, bool]] = [(tree, False)]
    while _stack:
        _node, _lazy = _stack.pop()
        if id(_node) in non_runtime_ids:
            continue
        if _lazy:
            for target in _pkg_import_targets_from_node(
                    _node, skill_name, source_path, skill_dir, module_stems):
                _graph_add_edge(target, mod_name, lazy_out, module_stems)
        _child_lazy = _lazy or isinstance(
            _node, (ast.FunctionDef, ast.AsyncFunctionDef))
        for _child in ast.iter_child_nodes(_node):
            _stack.append((_child, _child_lazy))
def _graph_scan_file(fpath: str, ctx, skill_name: str,
                     module_stems: dict[str, str],
                     imports: dict[str, set[str]],
                     lazy_out: dict[str, set[str]] | None,
                     skill_dir: str) -> None:
    mod_name = os.path.splitext(os.path.basename(fpath))[0]
    for _, tree in iter_file_trees([fpath], ctx):
        non_runtime_ids = _non_runtime_branch_node_ids(tree)
        for node, non_runtime in iter_module_level_nodes_tc(tree):
            if non_runtime:
                non_runtime_ids.update(
                    id(child) for child in walk_nodes(node))
                continue
            if not isinstance(node, (ast.Import, ast.ImportFrom)):
                continue
            if id(node) in non_runtime_ids:
                continue
            for target in _pkg_import_targets_from_node(
                    node, skill_name, fpath, skill_dir, module_stems):
                _graph_add_edge(target, mod_name, imports, module_stems)
        if lazy_out is not None:
            _graph_collect_lazy_edges(
                tree, mod_name, skill_name, lazy_out, module_stems,
                skill_dir, fpath, non_runtime_ids)
def _project_package_names(skill_dir: str) -> frozenset[str]:
    names = {os.path.basename(os.path.abspath(skill_dir))}
    module_root, pkg_name = _resolve_module_root(skill_dir)
    names.update({pkg_name, os.path.basename(module_root)})
    names.update(_importable_subpackage_names(skill_dir))
    names = {import_key(n) for n in names if n}
    return frozenset(n for n in names if n.isidentifier())
def _importable_subpackage_names(skill_dir: str) -> set[str]:
    names: set[str] = set()
    for base_dir in (skill_dir, os.path.join(skill_dir, "src")):
        if not os.path.isdir(base_dir):
            continue
        try:
            entries = os.listdir(base_dir)
        except OSError as _e:
            log_swallowed(
                __name__, _e,
                context='_importable_subpackage_names:OSError')
            continue
        for name in entries:
            if name.startswith(".") or name.lower() in _PACKAGE_ROOT_SKIP_DIRS:
                continue
            if _is_package_root_candidate(os.path.join(base_dir, name)):
                names.add(name)
    return names
def _is_project_package(head: str, package_names) -> bool:
    if isinstance(package_names, (set, frozenset)):
        return head in package_names
    return head == package_names
def _build_import_graph(
    skill_dir: str, py_files: list[str], ctx=None, lazy_out: dict[str, set[str]] | None = None
) -> dict[str, set[str]]:
    imports: dict[str, set[str]] = {}
    skill_name = _project_package_names(skill_dir)
    module_stems = {
        os.path.splitext(os.path.basename(f))[0].lower():
        os.path.splitext(os.path.basename(f))[0]
        for f in py_files
    }
    for fname in py_files:
        _graph_scan_file(os.path.join(skill_dir, fname), ctx, skill_name,
                     module_stems, imports, lazy_out, skill_dir)
    return imports
def _cycle_groups(graph: dict[str, set[str]]) -> list[list[str]]:
    return sorted(cycle_member_groups(graph, set(graph)))
def _has_module_main_guard(src: str, fpath: str) -> bool:
    tree = parse_source_tree(src, fpath)
    if tree is None:
        return False
    return any(isinstance(node, ast.If) and is_main_check(node.test)
               for node in iter_module_level_stmts(tree))
def _scan_script_markers(py_files: list[str], skill_dir: str,
                         ctx) -> tuple[set[str], set[str], set[str]]:
    shebang_scripts: set[str] = set()
    sa_declared: set[str] = set()
    main_guard_scripts: set[str] = set()
    for fname in py_files:
        fpath = os.path.join(skill_dir, fname)
        src = read_source(fpath, ctx)
        mn = os.path.splitext(os.path.basename(fname))[0]
        if src is not None and src.split("\n", 1)[0].startswith("#!"):
            shebang_scripts.add(mn)
        if src is not None and _SA_DECL_PAT.search(src):
            sa_declared.add(mn)
        if src is not None and _has_module_main_guard(src, fpath):
            main_guard_scripts.add(mn)
    return shebang_scripts, sa_declared, main_guard_scripts
def _add_import_parts(raw: str, star_connected: set[str]) -> None:
    for part in parse_import_name_list(raw):
        star_connected.add(part)
def _reconnect_by_regex(src: str, star_connected: set[str]) -> None:
    src = _drop_comments_and_string_statements(src)
    for m in re.finditer(r"from\s+\.(?!\.)(?:[\w.]*\.)?(\w+)\s+import\s+", src):
        star_connected.add(m.group(1))
    for m in re.finditer(r"from\s+\.\s+import\s+([\w, \t]+)", src):
        _add_import_parts(m.group(1), star_connected)
    for m in re.finditer(r"from\s+\.\s+import\s*\(([^)]*)\)", src, re.DOTALL):
        _add_import_parts(m.group(1), star_connected)
def _init_files(skill_dir: str, ctx=None) -> list[str]:
    return [
        os.path.join(skill_dir, relpath)
        for relpath in collect_py_files(skill_dir, ctx)
        if os.path.basename(relpath).lower() == "__init__.py"
    ]
def _init_star_connections(skill_dir: str, skill_name: str,
                           ctx) -> set[str]:
    star_connected: set[str] = set()
    module_stems = {
        os.path.splitext(os.path.basename(path))[0].lower():
        os.path.splitext(os.path.basename(path))[0]
        for path in collect_py_files(skill_dir, ctx)
        if os.path.basename(path).lower() != "__init__.py"
    }
    for init_path in _init_files(skill_dir, ctx):
        init_src = read_source(init_path, ctx) or ""
        if not init_src:
            continue
        init_tree = parse_source_tree(init_src, init_path)
        if init_tree is None:
            _reconnect_by_regex(init_src, star_connected)
            continue
        for node in iter_module_level_imports_tc(init_tree):
            star_connected.update(_pkg_import_targets_from_node(
                node, skill_name, init_path, skill_dir, module_stems))
    return star_connected
def _find_isolated_modules(
    py_files: list[str], imports: dict[str, set[str]], skill_dir: str, ctx=None
) -> tuple[list[str], list[str]]:
    all_imported = set().union(*imports.values()) if imports else set()
    shebang_scripts, sa_declared, main_guard_scripts = _scan_script_markers(
        py_files, skill_dir, ctx)
    star_connected = _init_star_connections(
        skill_dir, _project_package_names(skill_dir), ctx)
    entry_points = (shebang_scripts | star_connected | sa_declared
                    | main_guard_scripts | set(GENERIC_SCRIPT_MODULES))
    def _isolated_names(exempt: set[str]) -> list[str]:
        return [
            mn for fname in py_files
            if (mn := os.path.splitext(os.path.basename(fname))[0])
            not in exempt
            and not imports.get(mn) and mn not in all_imported
        ]
    isolated = _isolated_names(entry_points)
    sa_exempted = sorted(
        mn for mn in _isolated_names(entry_points - sa_declared)
        if mn in sa_declared)
    return isolated, sa_exempted
def _compute_fan_metrics(imports: dict[str, set[str]]) -> tuple[dict[str, int], dict[str, int]]:
    fan_in: dict[str, int] = {}
    for deps in imports.values():
        for d in sorted(deps):
            fan_in[d] = fan_in.get(d, 0) + 1
    fan_out = {m: len(deps) for m, deps in imports.items()}
    return fan_in, fan_out
def _top_modules(degrees: dict[str, int], limit: int = 10) -> dict[str, int]:
    ranked = sorted(degrees.items(), key=lambda item: (-item[1], item[0]))
    return dict(ranked[:limit])
def _combined_graph(imports: dict[str, set[str]],
                    lazy_edges: dict[str, set[str]]) -> dict[str, set[str]]:
    combined: dict[str, set[str]] = {m: set(d) for m, d in imports.items()}
    for m, deps in lazy_edges.items():
        combined.setdefault(m, set()).update(deps)
    return combined
def _soft_cycles_only(soft_all: list[list[str]],
                      cycles: list[list[str]]) -> list[list[str]]:
    _hard_keys = {tuple(sorted(c)) for c in cycles}
    return [c for c in soft_all if tuple(sorted(c)) not in _hard_keys]
def analyze_module_coupling(skill_dir: str, ctx: Any = None) -> dict:
    skill_dir = _require_structure_root(skill_dir)
    py_files = _collect_coupling_py_files(skill_dir, ctx)
    py_files = [f for f in py_files if not is_test_file_path(f)]
    warn_duplicate_module_stems(py_files, "模块耦合图")
    lazy_edges: dict[str, set[str]] = {}
    imports = _build_import_graph(skill_dir, py_files, ctx, lazy_out=lazy_edges)
    total_modules = len(py_files)
    cycles = _cycle_groups(imports)
    combined = _combined_graph(imports, lazy_edges)
    soft_cycles = _soft_cycles_only(_cycle_groups(combined), cycles)
    import_edges = sum(len(deps) for deps in combined.values())
    isolated, sa_exempted = _find_isolated_modules(py_files, combined, skill_dir, ctx)
    fan_in, fan_out = _compute_fan_metrics(combined)
    return {
        "total_modules": total_modules,
        "import_edges": import_edges,
        "cycles": len(cycles),
        "cycle_details": cycles,
        "soft_cycles": len(soft_cycles),
        "soft_cycle_details": soft_cycles,
        "isolated_modules": len(isolated),
        "isolated_names": isolated,
        "isolated_sa_exempted": sa_exempted,
        "max_fan_in": max(fan_in.values()) if fan_in else 0,
        "max_fan_out": max(fan_out.values()) if fan_out else 0,
        "fan_in": _top_modules(fan_in),
        "fan_out": _top_modules(fan_out),
    }
def analyze_facade_reachability(skill_dir: str, ctx: Any = None,
                                *, min_modules: int = 6) -> dict:
    module_root, skill_pkg_name = _resolve_module_root(skill_dir)
    all_py = _scannable_module_names(module_root)
    total_mods = len(all_py)
    if total_mods < min_modules:
        return {"total_modules": total_mods, "reachable_modules": 0,
                "unreachable_modules": 0, "unreachable_ratio": 0.0,
                "unreachable_names": []}
    all_mod_names = {f[:-3] for f in all_py}
    import_graph = _facade_import_graph(
        all_py, module_root, skill_pkg_name, all_mod_names, ctx)
    entry_mods, lazy_registered = _reachability_seeds(
        module_root, all_mod_names, ctx)
    seeds = {e for e in entry_mods if e in all_mod_names or e in {"__init__", "__main__"}}
    seeds |= lazy_registered
    visited = _bfs_reachable(import_graph, seeds)
    unreachable_mods = all_mod_names - visited
    return {
        "total_modules": total_mods,
        "reachable_modules": len(visited & all_mod_names),
        "unreachable_modules": len(unreachable_mods),
        "unreachable_ratio": len(unreachable_mods) / max(total_mods, 1),
        "unreachable_names": sorted(unreachable_mods)[:20],
    }
def analyze_export_consistency(skill_dir: str, ctx: Any = None) -> dict:
    module_root, skill_pkg_name = _resolve_module_root(skill_dir)
    init_fp = os.path.join(module_root, "__init__.py")
    if not os.path.isfile(init_fp):
        return {}
    init_src = read_source(init_fp, ctx) or ""
    if not init_src:
        return {}
    _init_tree = _source_tree(init_src, init_fp, ctx)
    package_names = frozenset(
        {skill_pkg_name}
        | {name[:-3] for name in _scannable_module_names(module_root)})
    imported_names = _init_imported_names(
        init_src, package_names, _init_tree, skill_pkg_name)
    all_names = _init_all_names(init_src, _init_tree)
    total_exported = len(imported_names)
    if all_names is _UNKNOWN_ALL_NAMES:
        return {
            "total_exported": total_exported,
            "in_all": None,
            "mismatch_ratio": None,
        }
    in_all = (total_exported if all_names is None
              else len(imported_names & all_names))
    mismatch_ratio = (1 - (in_all / max(total_exported, 1))
                      if total_exported > 0 else 0)
    return {
        "total_exported": total_exported,
        "in_all": in_all,
        "mismatch_ratio": mismatch_ratio,
    }
def _source_tree(src: str, fp: str, ctx: Any = None) -> Any:
    if ctx is not None and hasattr(ctx, "get_ast"):
        try:
            tree = ctx.get_ast(fp)
        except Exception as _ctx_e:  # noqa: BLE001
            log_swallowed(__name__, _ctx_e, context='_source_tree:ctx')
        else:
            if isinstance(tree, ast.Module):
                return tree
    return parse_source_tree(src, fp)
def _pkg_import_targets_from_source(src: str, fp: str, skill_pkg_name: str,
                        all_mod_names: set[str], mod_name: str,
                        ctx: Any = None) -> set[str]:
    tree = _source_tree(src, fp, ctx)
    if tree is not None:
        return _pkg_import_targets_from_source_ast(tree, skill_pkg_name, all_mod_names, mod_name)
    return _pkg_import_targets_from_source_regex(src, skill_pkg_name, all_mod_names, mod_name)
def _importfrom_edge_spec(node: ast.ImportFrom, skill_pkg_name: str,
                          all_mod_names: set[str]) -> tuple[list[str], bool]:
    _first = (node.module or "").split(".")[0]
    if node.level == 1:
        return (node.module.split(".") if node.module else []), True
    if node.level == 0 and _first == skill_pkg_name:
        return (node.module or "").split(".")[1:], True
    if node.level == 0 and node.module in all_mod_names:
        return [node.module], False
    return [], False
def _importfrom_node_targets(node: ast.ImportFrom, skill_pkg_name: str,
                             all_mod_names: set[str], mod_name: str) -> set[str]:
    _mods, _collect_names = _importfrom_edge_spec(
        node, skill_pkg_name, all_mod_names)
    _candidates = set(_mods) if len(_mods) <= 1 else set()
    if _collect_names and not _mods:
        _candidates |= {_a.name for _a in node.names}
    return {_m for _m in _candidates if _m in all_mod_names and _m != mod_name}
def _pkg_import_targets_from_source_ast(tree, skill_pkg_name: str, all_mod_names: set[str],
                            mod_name: str) -> set[str]:
    targets: set[str] = set()
    if mod_name == "__main__":
        tree = copy.deepcopy(tree)
        for node in walk_nodes(tree):
            if isinstance(node, ast.If) and is_main_check(node.test):
                node.test = ast.Constant(value=True)
    non_runtime_ids = _non_runtime_branch_node_ids(tree)
    for node, under_tc in iter_module_level_nodes_tc(tree):
        if under_tc:
            non_runtime_ids.update(id(child) for child in walk_nodes(node))
    for node in walk_nodes(tree):
        if id(node) in non_runtime_ids:
            continue
        if isinstance(node, ast.ImportFrom):
            targets |= _importfrom_node_targets(
                node, skill_pkg_name, all_mod_names, mod_name)
        elif isinstance(node, ast.Import):
            targets |= _ast_import_stmt_targets(
                node, skill_pkg_name, all_mod_names, mod_name)
    return targets
def _ast_import_stmt_targets(node: ast.Import, skill_pkg_name: str,
                             all_mod_names: set[str], mod_name: str) -> set[str]:
    targets: set[str] = set()
    for _a in node.names:
        _parts = _a.name.split(".")
        if len(_parts) == 1:
            _edge_parts = _parts
        elif len(_parts) == 2 and _parts[0] == skill_pkg_name:
            _edge_parts = _parts[1:]
        else:
            _edge_parts = []
        for _m in _edge_parts:
            if _m in all_mod_names and _m != mod_name:
                targets.add(_m)
    return targets
def _is_pkg_edge(candidate: str, all_mod_names: set[str], mod_name: str) -> bool:
    return candidate in all_mod_names and candidate != mod_name
_FROM_IMPORT_RE = re.compile(
    r"^[ \t]*from\s+(?P<mod>\.*[\w.]*)\s+import\s*"
    r"(?P<names>\([^)]*\)|[^\n#;]*)", re.MULTILINE)
_BARE_IMPORT_RE = re.compile(r"^[ \t]*import\s+(?P<names>[^\n#;]+)", re.MULTILINE)
def _import_spec_parts(raw: str, skill_pkg_name: str,
                       all_mod_names: set[str]) -> tuple[list[str], bool]:
    dotted = (raw or "").strip()
    level = len(dotted) - len(dotted.lstrip("."))
    parts = [part for part in dotted.lstrip(".").split(".") if part]
    if level == 1:
        return parts, True
    if level == 0 and parts and parts[0] == skill_pkg_name:
        return parts[1:], True
    if level == 0 and len(parts) == 1 and parts[0] in all_mod_names:
        return parts, False
    return [], False
def _unaliased_import_name(raw: str) -> str:
    return re.split(r"\s+as\s+", raw.strip(), maxsplit=1)[0].strip()
def _imported_symbol_names(raw: str) -> set[str]:
    normalized = (raw or "").replace("(", " ").replace(")", " ")
    return {name for name in parse_import_name_list(normalized)
            if name.isidentifier()}
def _importfrom_source_targets(src: str, skill_pkg_name: str,
                               all_mod_names: set[str], mod_name: str) -> set[str]:
    targets: set[str] = set()
    for match in _FROM_IMPORT_RE.finditer(src):
        mods, collect_names = _import_spec_parts(
            match.group("mod"), skill_pkg_name, all_mod_names)
        candidates = set(mods) if len(mods) <= 1 else set()
        if collect_names and not mods:
            candidates |= _imported_symbol_names(match.group("names"))
        targets |= {candidate for candidate in candidates
                    if _is_pkg_edge(candidate, all_mod_names, mod_name)}
    return targets
def _regex_bare_import_targets(src: str, skill_pkg_name: str,
                              all_mod_names: set[str], mod_name: str) -> set[str]:
    targets: set[str] = set()
    for match in _BARE_IMPORT_RE.finditer(src):
        for piece in match.group("names").split(","):
            parts = _unaliased_import_name(piece).split(".")
            if len(parts) == 1:
                edge_parts = parts
            elif len(parts) == 2 and parts[0] == skill_pkg_name:
                edge_parts = parts[1:]
            else:
                edge_parts = []
            targets |= {part for part in edge_parts
                        if _is_pkg_edge(part, all_mod_names, mod_name)}
    return targets
def _pkg_import_targets_from_source_regex(src: str, skill_pkg_name: str,
                              all_mod_names: set[str], mod_name: str) -> set[str]:
    src = _drop_non_import_time_blocks(
        _drop_comments_and_string_statements(src),
        preserve_deferred=True,
        preserve_main=mod_name == "__main__")
    return (_importfrom_source_targets(src, skill_pkg_name, all_mod_names, mod_name)
            | _regex_bare_import_targets(src, skill_pkg_name, all_mod_names, mod_name))
def _facade_import_graph(all_py: list[str], skill_dir: str, skill_pkg_name: str,
                         all_mod_names: set[str], ctx=None) -> dict[str, set[str]]:
    import_graph: dict[str, set[str]] = {}
    shadowed_modules = {
        name for name in all_mod_names
        if os.path.isfile(os.path.join(skill_dir, name, "__init__.py"))
    }
    graph_sources = [(pf[:-3], pf) for pf in all_py]
    for entry_name, entry_file in (("__init__", "__init__.py"),
                                   ("__main__", "__main__.py")):
        if os.path.isfile(os.path.join(skill_dir, entry_file)):
            graph_sources.append((entry_name, entry_file))
    for mod_name, file_name in graph_sources:
        import_graph.setdefault(mod_name, set())
        _fp = os.path.join(skill_dir, file_name)
        src = read_source(_fp, ctx) or ""
        if src:
            targets = _pkg_import_targets_from_source(
                src, _fp, skill_pkg_name, all_mod_names, mod_name, ctx)
            import_graph[mod_name] |= targets - shadowed_modules
    return import_graph
def _reachability_seeds(skill_dir: str, all_mod_names: set[str],
                        ctx=None) -> tuple[set[str], set[str]]:
    entry_mods: set[str] = set()
    if os.path.isfile(os.path.join(skill_dir, "__init__.py")):
        entry_mods.add("__init__")
    if os.path.isfile(os.path.join(skill_dir, "__main__.py")):
        entry_mods.add("__main__")
    if os.path.isfile(os.path.join(skill_dir, "facade.py")):
        entry_mods.add("facade")
    elif not entry_mods:
        entry_mods |= all_mod_names
    lazy_registered = _lazy_registered_modules(skill_dir, all_mod_names, ctx)
    return entry_mods, lazy_registered
def _lazy_dict_module_names(node: ast.Dict, all_mod_names: set[str]) -> set[str]:
    names: set[str] = set()
    for part in list(node.keys) + list(node.values):
        if isinstance(part, ast.Constant) and part.value in all_mod_names:
            names.add(part.value)
    return names
def _lazy_registry_files(skill_dir: str) -> list[str]:
    candidates = ["__init__.py"]
    try:
        entries = sorted(os.listdir(skill_dir))
    except OSError as _e:
        log_swallowed(__name__, _e, context='_lazy_registry_files:OSError')
        entries = []
    candidates.extend(
        name for name in entries
        if fnmatch.fnmatch(name.lower(), _LAZY_REGISTRY_MODULE_GLOB)
        and os.path.isfile(os.path.join(skill_dir, name)))
    return candidates
def _lazy_registered_modules(skill_dir: str, all_mod_names: set[str],
                             ctx=None) -> set[str]:
    registered: set[str] = set()
    for file_name in _lazy_registry_files(skill_dir):
        lazy_registry_path = os.path.join(skill_dir, file_name)
        if not os.path.isfile(lazy_registry_path):
            continue
        tree = parse_source_tree(read_source(lazy_registry_path, ctx) or "",
                                 lazy_registry_path)
        if tree is None:
            continue
        for node, under_tc in iter_module_level_nodes_tc(
                tree, include_class_body=False):
            if under_tc:
                continue
            if isinstance(node, ast.Assign):
                targets = node.targets
            elif isinstance(node, ast.AnnAssign) and node.value is not None:
                targets = [node.target]
            else:
                continue
            if not isinstance(node.value, ast.Dict):
                continue
            if file_name == "__init__.py" and not any(
                    isinstance(target, ast.Name)
                    and any(hint in target.id.lower()
                            for hint in _LAZY_REGISTRY_NAME_HINTS)
                    for target in targets):
                continue
            registered |= _lazy_dict_module_names(node.value, all_mod_names)
    return registered
def _is_entry_module(filename: str) -> bool:
    return filename.lower() in ("__init__.py", "__main__.py")
def _scannable_module_names(base_dir: str) -> list[str]:
    try:
        names = os.listdir(base_dir)
    except OSError as _e:
        log_swallowed(__name__, _e, context='_scannable_module_names:OSError')
        return []
    return [
            f
            for f in names
            if f.lower().endswith(".py")
            and not _is_entry_module(f)
            and not is_test_file_path(f)
            and os.path.isfile(os.path.join(base_dir, f))
        ]
def _is_package_root_candidate(path: str) -> bool:
    return os.path.isdir(path) and (
        os.path.isfile(os.path.join(path, "__init__.py"))
        or bool(_scannable_module_names(path)))
def _resolve_module_root(skill_dir: str) -> tuple[str, str]:
    root = os.path.abspath(_require_structure_root(skill_dir))
    root_dir_name = os.path.basename(root)
    pkg_name = import_key(root_dir_name)
    root_modules = _scannable_module_names(root)
    if os.path.isfile(os.path.join(root, "__init__.py")):
        return root, pkg_name
    preferred = (os.path.join(root, root_dir_name),
                 os.path.join(root, "src", root_dir_name))
    for cand in preferred:
        if _is_package_root_candidate(cand):
            return cand, import_key(os.path.basename(cand))
    search_roots = [os.path.join(root, "src")]
    has_packaging_marker = any(
        os.path.isfile(os.path.join(root, marker))
        for marker in ("pyproject.toml", "setup.py", "setup.cfg"))
    if not root_modules or has_packaging_marker:
        search_roots.append(root)
    for base_dir in search_roots:
        if not os.path.isdir(base_dir):
            continue
        try:
            entries = os.listdir(base_dir)
        except OSError as _e:
            log_swallowed(__name__, _e, context='_resolve_module_root:OSError')
            continue
        candidates = [
            name for name in entries
            if name.lower() not in _PACKAGE_ROOT_SKIP_DIRS
            and not name.startswith(".")
            and _is_package_root_candidate(os.path.join(base_dir, name))
        ]
        if len(candidates) == 1:
            return (os.path.join(base_dir, candidates[0]),
                    import_key(candidates[0]))
    return root, pkg_name
def _bfs_reachable(import_graph: dict[str, set[str]], seeds: set[str]) -> set[str]:
    visited = set(seeds)
    queue = deque(seeds)
    while queue:
        cur = queue.popleft()
        for neighbor in import_graph.get(cur, ()):
            if neighbor not in visited:
                visited.add(neighbor)
                queue.append(neighbor)
    return visited
def _is_public_export_binding(name: str) -> bool:
    if not name.isidentifier():
        return False
    if name.startswith('__') and name.endswith('__'):
        return True
    return not name.startswith('_')
_TYPE_CHECKING_GUARD_RE = re.compile(
    r"^(?P<indent>[ \t]*)if\s+(?:[\w.]+\.)?TYPE_CHECKING\s*:")
_MAIN_GUARD_RE = re.compile(
    r"^(?P<indent>[ \t]*)if\s+(?:"
    r"__name__\s*==\s*['\"]__main__['\"]|"
    r"['\"]__main__['\"]\s*==\s*__name__)\s*:")
_ELSE_CLAUSE_RE = re.compile(
    r"^(?P<indent>[ \t]*)else\s*:\s*(?:#.*)?$")
_DEFERRED_SCOPE_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?:async[ \t]+def|def|class)\b")
_CONSTANT_BRANCH_GUARD_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?:if|while)\s+(?P<test>.+?)\s*:\s*(?:#.*)?$")
_FOR_LOOP_GUARD_RE = re.compile(
    r"^(?P<indent>[ \t]*)for\s+.+?\s+in\s+(?P<iterable>.+?)\s*:\s*(?:#.*)?$")
def _regex_type_checking_names(src: str) -> set[str]:
    names = {'TYPE_CHECKING'}
    for match in _FROM_IMPORT_RE.finditer(src):
        if match.group('mod') not in {'typing', 'typing_extensions'}:
            continue
        raw = match.group('names')
        imported_names = parse_import_name_list(raw)
        bound_names = parse_import_name_list(raw, bound_names=True)
        for imported, bound in zip(imported_names, bound_names, strict=True):
            if imported == 'TYPE_CHECKING':
                names.add(bound)
    return names
def _type_checking_guard_re(src: str, *, negated: bool = False):
    aliases = sorted(_regex_type_checking_names(src) - {'TYPE_CHECKING'})
    if not aliases and not negated:
        return _TYPE_CHECKING_GUARD_RE
    names = [r"(?:[\w.]+\.)?TYPE_CHECKING"]
    names.extend(re.escape(name) for name in aliases)
    prefix = r"if\s+not\s+" if negated else r"if\s+"
    return re.compile(
        r"^(?P<indent>[ \t]*)" + prefix
        + r"(?:" + "|".join(names) + r")\s*:")
def _blank_source_token(lines: list[str], start: tuple[int, int],
                        end: tuple[int, int]) -> None:
    for row in range(start[0], end[0] + 1):
        line = lines[row - 1]
        left = start[1] if row == start[0] else 0
        right = end[1] if row == end[0] else len(line)
        lines[row - 1] = line[:left] + " " * (right - left) + line[right:]
def _drop_comments_and_string_statements(src: str) -> str:
    lines = src.splitlines()
    previous_kind: int | None = None
    string_statement = False
    try:
        tokens = tokenize.generate_tokens(io.StringIO(src).readline)
        for item in tokens:
            kind = item.type
            if kind == tokenize.COMMENT:
                _blank_source_token(lines, item.start, item.end)
                continue
            if (kind == tokenize.STRING
                    and (string_statement or previous_kind is None
                         or previous_kind in {
                             tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT})):
                _blank_source_token(lines, item.start, item.end)
                string_statement = True
            elif kind == tokenize.NEWLINE:
                string_statement = False
            if kind != tokenize.NL:
                previous_kind = kind
    except (tokenize.TokenError, SyntaxError):
        pass
    return "\n".join(lines)
def _constant_nonruntime_guard(line: str):
    match = _CONSTANT_BRANCH_GUARD_RE.match(line)
    if match is not None:
        try:
            test = ast.parse(match.group("test"), mode="eval").body
        except SyntaxError:
            return None
        return (match if isinstance(test, ast.Constant) and not test.value
                else None)
    match = _FOR_LOOP_GUARD_RE.match(line)
    if match is None:
        return None
    try:
        iterable = ast.literal_eval(match.group("iterable"))
    except (ValueError, SyntaxError):
        return None
    return (match if isinstance(iterable, (list, tuple, dict, set, str, bytes))
            and not iterable else None)
def _drop_non_import_time_blocks(
        src: str, *, preserve_deferred: bool = False,
        preserve_main: bool = False) -> str:
    kept: list[str] = []
    skip_indent: int | None = None
    type_checking_guard = _type_checking_guard_re(src)
    negated_type_checking_guard = _type_checking_guard_re(src, negated=True)
    negated_body_indents: list[int] = []
    for line in src.splitlines():
        if skip_indent is not None:
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            indent = len(line) - len(line.lstrip())
            if indent > skip_indent:
                continue
            skip_indent = None
        if line.strip() and not line.lstrip().startswith("#"):
            indent = len(line) - len(line.lstrip())
            else_clause = _ELSE_CLAUSE_RE.match(line)
            while negated_body_indents and indent <= negated_body_indents[-1]:
                if (else_clause is not None
                        and indent == negated_body_indents[-1]):
                    break
                negated_body_indents.pop()
            if (else_clause is not None and negated_body_indents
                    and indent == negated_body_indents[-1]):
                negated_body_indents.pop()
                skip_indent = indent
                continue
        guard = (type_checking_guard.match(line)
                 or _constant_nonruntime_guard(line))
        if not preserve_main:
            guard = guard or _MAIN_GUARD_RE.match(line)
        if not preserve_deferred:
            guard = guard or _DEFERRED_SCOPE_RE.match(line)
        if guard is not None:
            skip_indent = len(guard.group("indent"))
            continue
        negated_guard = negated_type_checking_guard.match(line)
        if negated_guard is not None:
            negated_body_indents.append(len(negated_guard.group("indent")))
        kept.append(line)
    return "\n".join(kept)
def _init_imported_names(init_src: str, skill_pkg_name,
                         init_tree, root_pkg_name: str) -> set[str]:
    if init_tree is None:
        return _init_imported_names_regex(
            _drop_comments_and_string_statements(init_src), skill_pkg_name,
            root_pkg_name)
    imported_names: set[str] = set()
    for _node, under_tc in iter_module_level_nodes_tc(
            init_tree, include_class_body=False):
        if under_tc:
            continue
        if isinstance(_node, ast.ImportFrom):
            imported_names |= _init_bound_names_from_importfrom(
                _node, skill_pkg_name)
        elif isinstance(_node, ast.Import):
            imported_names |= _init_bound_names_from_import(
                _node, skill_pkg_name, root_pkg_name)
    return imported_names
def _init_bound_names_from_importfrom(node: ast.ImportFrom,
                                      skill_pkg_name) -> set[str]:
    _first = (node.module or "").split(".")[0]
    if not (node.level >= 1 or _is_project_package(_first, skill_pkg_name)):
        return set()
    _bound = {(_a.asname or _a.name) for _a in node.names if _a.name != "*"}
    return {b for b in _bound if _is_public_export_binding(b)}
def _init_bound_names_from_import(node: ast.Import,
                                  skill_pkg_name,
                                  root_pkg_name: str) -> set[str]:
    bound: set[str] = set()
    for alias in node.names:
        parts = alias.name.split(".")
        if not _is_project_package(parts[0], skill_pkg_name):
            continue
        if alias.asname:
            bound.add(alias.asname)
        elif len(parts) > 1 and parts[0] == root_pkg_name:
            bound.add(parts[1])
        else:
            bound.add(parts[0])
    return {name for name in bound if _is_public_export_binding(name)}
def _init_imported_names_regex(init_src: str, skill_pkg_name,
                               root_pkg_name: str) -> set[str]:
    imported_names: set[str] = set()
    package_names = ({skill_pkg_name} if isinstance(skill_pkg_name, str)
                     else set(skill_pkg_name))
    package_pattern = "|".join(
        re.escape(name) for name in sorted(package_names) if name) or r"(?!)"
    _prefix = (r"^[ \t]*from\s+(?:\.+(?:\w+(?:\.\w+)*)?|(?:"
               + package_pattern + r")(?:\.\w+)*)\s+import\s+")
    _src = _drop_non_import_time_blocks(init_src)
    def _add(raw: str) -> None:
        for name in parse_import_name_list(raw, bound_names=True):
            if _is_public_export_binding(name):
                imported_names.add(name)
    for m in re.finditer(
            _prefix + r"\(([^)]+)\)", _src, re.DOTALL | re.MULTILINE):
        _add(m.group(1))
    for m in re.finditer(
        _prefix
        + r"([A-Za-z_]\w*(?:\s+as\s+[A-Za-z_]\w*)?"
        + r"(?:\s*,\s*[A-Za-z_]\w*(?:\s+as\s+[A-Za-z_]\w*)?)*\s*,?)",
        _src,
        re.MULTILINE,
    ):
        _add(m.group(1))
    for match in _BARE_IMPORT_RE.finditer(_src):
        raw = match.group("names")
        original_names = parse_import_name_list(raw)
        bound_names = parse_import_name_list(raw, bound_names=True)
        for original, bound in zip(
                original_names, bound_names, strict=True):
            parts = original.split(".")
            if not _is_project_package(parts[0], skill_pkg_name):
                continue
            if bound != original:
                public_name = bound
            elif len(parts) > 1 and parts[0] == root_pkg_name:
                public_name = parts[1]
            else:
                public_name = parts[0]
            if _is_public_export_binding(public_name):
                imported_names.add(public_name)
    return imported_names
def _init_all_names(
        init_src: str, init_tree) -> set[str] | None | _UnknownAllNames:
    all_names: set[str] = set()
    if init_tree is not None:
        surface = extract_all_surface(init_tree)
        if surface is None:
            return None
        if not surface.complete:
            return _UNKNOWN_ALL_NAMES
        all_names.update(surface.names)
    else:
        init_src = _drop_non_import_time_blocks(
            _drop_comments_and_string_statements(init_src))
        if not re.search(r"__all__", init_src):
            return None
        all_match = re.search(
            r"^[ \t]*__all__\s*=\s*[\(\[]([^)\]]*)[\)\]]",
            init_src, re.DOTALL | re.MULTILINE)
        if all_match is None:
            return _UNKNOWN_ALL_NAMES
        trailing = init_src[all_match.end():].split("\n", 1)[0].lstrip()
        if trailing and not trailing.startswith(("#", ";")):
            return _UNKNOWN_ALL_NAMES
        other_source = init_src[:all_match.start()] + init_src[all_match.end():]
        other_source = "\n".join(
            line.split("#", 1)[0] for line in other_source.splitlines())
        if re.search(
                r"\b__all__\s*(?:\+?=|\.\s*(?:append|extend|insert|remove|pop|clear)\b)",
                other_source):
            return _UNKNOWN_ALL_NAMES
        literal = all_match.group(0).split("=", 1)[1].strip()
        try:
            value = ast.literal_eval(literal)
        except (ValueError, SyntaxError):
            return _UNKNOWN_ALL_NAMES
        if (not isinstance(value, (list, tuple))
                or not all(isinstance(name, str) for name in value)):
            return _UNKNOWN_ALL_NAMES
        all_names.update(value)
    return all_names
_MAX_FRAGMENT_ITEMS = 50
_STRUCTURE_FACT_FAMILY: dict[str, str] = {
    "A10-OVERSIZED": "oversized",
    "ARCH-003": "oversized",
    "A10-EMPTY": "empty",
    "D12-FRAGMENT": "fragment",
    "D12-REBOUND": "rebound",
    "ARCH-001": "self_import",
    "ARCH-002": "import_cycle",
    "API-01": "ghost_export",
    "API-02": "unexported_public",
}
_STRUCTURE_SEVERITY_PENALTY: dict[str, int] = {
    "P0": 15, "P1": 8, "P2": 3, "P3": 1,
}
def _structure_penalty(findings: list[Finding]) -> int:
    penalties: dict[tuple[str, str], int] = {}
    for finding in findings:
        family = _STRUCTURE_FACT_FAMILY.get(finding.rule_id)
        if family is None:
            continue
        key = (family, finding.file or "")
        penalty = _STRUCTURE_SEVERITY_PENALTY.get(finding.severity, 1)
        penalties[key] = max(penalties.get(key, 0), penalty)
    return sum(penalties.values())
def _is_collectable_py_name(filename: str) -> bool:
    return (filename.lower().endswith(".py")
            and not filename.startswith("."))
class ModuleStructureAnalyzer(DependencyAnalyzer):
    def __init__(self, skill_dir: str, ctx: Any | None = None):
        super().__init__(skill_dir)
        self.ctx = ctx
        self.audit_py_files = self._scan_audit_py_files()
        warn_duplicate_module_stems(self.py_files)
    def _scan_audit_py_files(self) -> list[str]:
        audit_files = []
        for root, dirs, filenames in os.walk(self.skill_dir):
            prune_scan_dirnames(dirs, _SCAN_PRUNE_DIRS)
            for fn in sorted(filenames):
                if not _is_collectable_py_name(fn):
                    continue
                fp = os.path.join(root, fn)
                if is_test_file_path(fp):
                    continue
                if not is_runtime_temp_path(fp):
                    audit_files.append(fp)
        return audit_files
    def baseline_analysis(self) -> dict:
        findings: list[Finding] = []
        dir_stats: dict[str, dict] = {}
        oversized_files: list[dict] = []
        empty_files: list[str] = []
        unreadable_files: list[str] = []
        file_count = 0
        total_lines = 0
        for fp in self.audit_py_files:
            line_count = self._count_file_lines(fp)
            rel = safe_relpath(fp, self.skill_dir)
            rel_dir = os.path.dirname(rel) or "."
            if line_count is None:
                unreadable_files.append(rel)
            file_count += 1
            total_lines += line_count or 0
            self._accumulate_dir_stats(dir_stats, rel_dir, line_count)
            if line_count is not None and line_count > OVERSIZED_THRESHOLD:
                findings.append(self._oversized_finding(rel, line_count))
                oversized_files.append({"file": rel, "lines": line_count})
            if line_count == 0 and not _is_exempt_basename(rel):
                findings.append(self._empty_finding(rel))
                empty_files.append(rel)
        return {
            "file_count": file_count,
            "total_lines": total_lines,
            "dir_distribution": dir_stats,
            "oversized_files": oversized_files,
            "empty_files": empty_files,
            "findings": findings,
            "degraded": bool(unreadable_files),
            "error": ("行数统计失败: " + ", ".join(unreadable_files)
                      if unreadable_files else ""),
        }
    @staticmethod
    def _accumulate_dir_stats(dir_stats: dict[str, dict], rel_dir: str,
                              line_count: int | None) -> None:
        bucket = dir_stats.setdefault(rel_dir, {"file_count": 0, "total_lines": 0})
        bucket["file_count"] += 1
        if line_count is not None:
            bucket["total_lines"] += line_count
    @staticmethod
    def _oversized_finding(rel: str, line_count: int) -> Finding:
        return Finding(
            rule_id="A10-OVERSIZED",
            severity="P1",
            message=f"超大文件: {line_count}行 (约束: <={OVERSIZED_THRESHOLD}行)",
            file=rel,
            confidence=0.90,
        )
    @staticmethod
    def _empty_finding(rel: str) -> Finding:
        return Finding(
            rule_id="A10-EMPTY",
            severity="P2",
            message="空文件 (0行)",
            file=rel,
            confidence=0.85,
        )
    @staticmethod
    def _count_file_lines(fp: str) -> int | None:
        try:
            return count_lines(read_source_auto(fp))
        except (OSError, ValueError) as e:
            logger.warning("[ModuleStructureAnalyzer] 行数统计失败（A10 判定跳过该文件）: %s: %s", fp, e)
            return None
    @staticmethod
    def _fragment_findings(report: FragmentReport) -> list[Finding]:
        fragment_rate = report.fragment_ratio
        severity = "P2" if fragment_rate > report.warn_ratio else "P3"
        findings: list[Finding] = []
        for ff in report.fragment_files[:_MAX_FRAGMENT_ITEMS]:
            findings.append(Finding(
                rule_id="D12-FRAGMENT",
                severity=severity,
                message=f"碎片文件（{ff.path}，{ff.lines} 行）",
                file=ff.path,
                detail=f"公共前缀: {ff.prefix}" if ff.prefix else "",
                confidence=0.8,
            ))
        zone_lo, zone_hi = report.rebound_zone
        for rb in report.rebound_files[:_MAX_FRAGMENT_ITEMS]:
            findings.append(Finding(
                rule_id="D12-REBOUND",
                severity="P3",
                message=(f"反弹风险: {rb.path}（{rb.rebound_risk}），"
                         "A10-OVERSIZED 修复（删行/拆分）后回落将触发 D09 碎片化"),
                file=rb.path,
                detail=(f"行数处于反弹风险区 [{zone_lo},{zone_hi}]，"
                        "拆分/删行时保留行数缓冲或合并入邻近模块"),
                confidence=0.7,
            ))
        return findings
    @staticmethod
    def _group_merge_suggestions(report: FragmentReport) -> list:
        suggestions = []
        for g in _groups_with_fragments(report):
            if not g.is_worth_merging:
                continue
            group_dir = Path(g.files[0].path).parent.as_posix()
            suggested_name = (f"{g.prefix}.py" if group_dir == "."
                              else f"{group_dir}/{g.prefix}.py")
            suggestions.append({
                "type": "group",
                "action": "merge",
                "base": g.prefix,
                "files": [ff.path for ff in g.files],
                "suggested_name": suggested_name,
                "file_count": g.file_count,
                "total_lines": g.total_lines,
                "ref_counts": dict(g.ref_counts),
                "total_refs": g.total_refs,
                "risk_level": g.risk_level,
                "message": (f"合并同前缀碎片组 {g.prefix}（{g.file_count} 个文件，"
                            f"共 {g.total_lines} 行，引用 {g.total_refs}, "
                            f"风险 {g.risk_level}）到 {suggested_name}"),
            })
        return suggestions
    @staticmethod
    def _dir_merge_suggestions(report: FragmentReport) -> list:
        return [{
            "type": "dir",
            "action": "review",
            "path": d.path,
            "fragment_ratio": d.fragment_ratio,
            "level": d.level,
            "message": f"目录 {d.path} 碎片率 {d.fragment_ratio:.0%}（{d.level}），建议合并小型文件",
        } for d in report.dir_reports if d.level in ("warn", "block")]
    @staticmethod
    def _fragment_merge_suggestions(report: FragmentReport) -> list:
        merge_suggestions: list = []
        merge_suggestions.extend(
            ModuleStructureAnalyzer._group_merge_suggestions(report))
        merge_suggestions.extend(
            ModuleStructureAnalyzer._dir_merge_suggestions(report))
        if report.blocked:
            merge_suggestions.append({
                "type": "global",
                "action": "block",
                "message": "存在超过阈值的可合并碎片组，触发全局阻断建议：优先执行合并重构",
            })
        if report.rebound_files:
            rebound_lo, rebound_hi = report.rebound_zone
            merge_suggestions.append({
                "type": "rebound",
                "action": "watch",
                "files": [rb.path for rb in report.rebound_files[:_MAX_FRAGMENT_ITEMS]],
                "message": (f"反弹风险文件 {len(report.rebound_files)} 个：行数处于"
                            f" [{rebound_lo},{rebound_hi}] 区间，"
                            f"A10-OVERSIZED 修复（删行）会使其回落 <{report.min_lines} 行"
                            "触发 D09，拆分时保留行数缓冲或合并入邻近模块"),
            })
        return merge_suggestions
    def fragment_analysis(self) -> dict:
        findings: list[Finding] = []
        fragment_rate = 0.0
        merge_suggestions: list = []
        report: FragmentReport | None = None
        error = ""
        degraded = False
        try:
            report = detect_fragments(self.skill_dir)
            fragment_rate = report.fragment_ratio
            findings = self._fragment_findings(report)
            merge_suggestions = self._fragment_merge_suggestions(report)
        except Exception as e:
            degraded = True
            error = str(e) or type(e).__name__
            logger.warning("[ModuleStructureAnalyzer] 碎片化检测异常: %s", e, exc_info=True)
        text_report = ""
        try:
            if isinstance(report, FragmentReport):
                text_report = format_report(report)
        except Exception as e:  # noqa: BLE001
            logger.debug("[ModuleStructureAnalyzer] text_report 渲染降级: %s", e)
        return {
            "findings": findings,
            "fragment_rate": fragment_rate,
            "merge_suggestions": merge_suggestions,
            "text_report": text_report,
            "degraded": degraded,
            "error": error,
        }
    def health_score(self, findings: list[Finding]) -> int:
        base = super().health_score(findings)
        return max(0, base - _structure_penalty(findings))
    def full_analysis(self, graph: DependencyGraph | None = None) -> dict:
        if graph is None:
            graph = self.build_graph()
        checks = self._run_structure_checks(graph)
        score = self.health_score(checks["all_findings"])
        result = self._assemble_result(graph, checks, score)
        self._log_analysis(result, checks["severity_counts"],
                          checks["rule_counts"])
        return result
    def _safe_arch_analysis(self) -> dict:
        try:
            return ArchitectureRuleAnalyzer(
                self.skill_dir, self.audit_py_files).architecture_analysis()
        except Exception as e:
            logger.warning("[ModuleStructureAnalyzer] 架构分析异常: %s", e,
                           exc_info=True)
            return {"findings": [], "module_count": 0,
                    "degraded": True, "error": str(e)}
    def _safe_api_analysis(self) -> dict:
        try:
            return ApiContractAuditor(
                self.skill_dir, self.audit_py_files,
                self.ctx).api_contract_analysis()
        except Exception as e:
            logger.warning("[ModuleStructureAnalyzer] API 契约分析异常: %s", e,
                           exc_info=True)
            return {"findings": [], "degraded": True, "error": str(e)}
    def _run_structure_checks(self, graph: DependencyGraph) -> dict:
        all_findings, d9 = self._collect_d9_findings(graph)
        baseline = self.baseline_analysis()
        all_findings.extend(baseline["findings"])
        fragment = self.fragment_analysis()
        all_findings.extend(fragment["findings"])
        arch = self._safe_arch_analysis()
        all_findings.extend(arch["findings"])
        api = self._safe_api_analysis()
        all_findings.extend(api["findings"])
        return {
            "all_findings": all_findings,
            "d9": d9,
            "baseline": baseline,
            "fragment": fragment,
            "arch": arch,
            "api": api,
            "severity_counts": Counter(f.severity for f in all_findings),
            "rule_counts": Counter(f.rule_id for f in all_findings),
            "source_counts": dict(Counter(
                finding.rule_id.split("-", 1)[0]
                for finding in all_findings)),
        }
    def _assemble_result(self, graph: DependencyGraph, checks: dict,
                         score: int) -> dict:
        all_findings = checks["all_findings"]
        baseline, fragment = checks["baseline"], checks["fragment"]
        degraded = any((
            baseline.get("degraded"),
            fragment.get("degraded"),
            checks["arch"].get("degraded"),
            checks["api"].get("degraded"),
        ))
        result = {
            "status": "warn" if all_findings or degraded else "pass",
            "findings_count": len(all_findings),
            "findings": [f.to_dict() for f in all_findings],
            "summary": (
                f"模块结构分析: {baseline['file_count']}文件, {baseline['total_lines']}行, "
                f"{len(graph.nodes)}模块, {graph.total_edges}依赖边, "
                f"{len(checks['d9']['cycles'])}环, 健康度{score}/100, "
                f"碎片率{fragment.get('fragment_rate', 0)*100:.1f}%"
                f"{'（检测降级）' if degraded else ''}, "
                f"共{len(all_findings)}项发现"
            ),
            "payload": self._full_analysis_payload(graph, checks, score),
        }
        result["ai_execution"] = {
            "next_action": "review_and_fix_module_structure_findings",
            "instruction": (
                "逐项审核 findings（上帝文件/自导入/循环依赖/碎片合并/API 契约）；"
                "审核通过后按 detail 建议执行结构治理（收敛职责到既有模块/"
                "改为经包统一出入口消费/合并碎片组；禁止拆分文件或子模块，"
                "合并须先过 merge 论证），随后调用 "
                f"{type(self).__module__}.{type(self).__name__}"
                f"({self.skill_dir!r}).full_analysis() 复扫验证"
            ),
        }
        return result
    @staticmethod
    def _log_analysis(result: dict, severity_counts: Counter,
                      rule_counts: Counter) -> None:
        if result["findings_count"]:
            logger.warning(
                "[ModuleStructureAnalyzer] full_analysis 检出 %d 项: "
                "sev=%s rules=%s | %s",
                result["findings_count"], dict(severity_counts),
                dict(rule_counts), result["summary"])
        else:
            logger.info("[ModuleStructureAnalyzer] full_analysis 零检出: %s",
                        result["summary"])
    @staticmethod
    def _full_analysis_payload(graph: DependencyGraph, checks: dict,
                              score: int) -> dict:
        d9 = checks["d9"]
        rule_counts = checks["rule_counts"]
        return {
            "graph": graph.summary(),
            "fan_analysis": d9["fan_raw"],
            "hubs": d9["hubs"],
            "orphans": d9["orphans"],
            "critical_path": d9["cpath"],
            "cycles": d9["cycles"],
            "layer_violations_count": d9["layer_findings_count"],
            "health_score": score,
            "baseline": ModuleStructureAnalyzer._baseline_payload(
                checks["baseline"]),
            "fragment": ModuleStructureAnalyzer._fragment_payload(
                checks["fragment"]),
            "architecture": ModuleStructureAnalyzer._arch_payload(
                checks["arch"], rule_counts),
            "api_contract": ModuleStructureAnalyzer._api_payload(
                rule_counts, checks["api"]),
            "severity_summary": dict(checks["severity_counts"]),
            "rule_summary": dict(rule_counts),
            "source_summary": checks["source_counts"],
        }
    @staticmethod
    def _baseline_payload(baseline: dict) -> dict:
        return {
            "file_count": baseline["file_count"],
            "total_lines": baseline["total_lines"],
            "oversized_count": len(baseline["oversized_files"]),
            "empty_count": len(baseline["empty_files"]),
            "degraded": bool(baseline.get("degraded")),
            "error": baseline.get("error", ""),
        }
    @staticmethod
    def _fragment_payload(fragment: dict) -> dict:
        return {
            "rate": fragment.get("fragment_rate", 0),
            "merge_suggestions": fragment.get("merge_suggestions", []),
            "text_report": fragment.get("text_report", ""),
            "degraded": bool(fragment.get("degraded")),
            "error": fragment.get("error", ""),
        }
    @staticmethod
    def _arch_payload(arch: dict, rule_counts: Counter) -> dict:
        return {
            "module_count": arch.get("module_count", 0),
            "self_imports": rule_counts["ARCH-001"],
            "cycles": rule_counts["ARCH-002"],
            "god_files": rule_counts["ARCH-003"],
            "degraded": bool(arch.get("degraded")),
            "error": arch.get("error", ""),
        }
    @staticmethod
    def _api_payload(rule_counts: Counter, api: dict | None = None) -> dict:
        api = api or {}
        return {
            "api_01_count": rule_counts["API-01"],
            "api_02_count": rule_counts["API-02"],
            "degraded": bool(api.get("degraded")),
            "error": api.get("error", ""),
        }
def analyze_fragmentation(skill_dir: str, ctx: Any = None) -> dict:
    skill_dir = _require_structure_root(skill_dir)
    py_files = [f for f in collect_py_files(skill_dir, ctx)
                if not is_test_file_path(f)
                and os.path.basename(f).lower() != "__init__.py"]
    total_files = len(py_files)
    sizes = classify_file_sizes(py_files, skill_dir, ctx)
    small_files = sizes["small"]
    medium_files = sizes["medium"]
    large_files = sizes["large"]
    total_lines = sizes["total_lines"]
    readable_files = sizes["readable"]
    small_names = sizes["small_names"]
    avg_lines = total_lines / max(readable_files, 1)
    _count_pressure = min(1.0, max(0.0, (total_files - 100) / 400.0))
    _small_ratio = small_files / max(readable_files, 1)
    fragmentation_score = min(1.0, _small_ratio * (0.7 + 0.3 * _count_pressure))
    return {
        "total_files": total_files,
        "small_files": small_files,
        "medium_files": medium_files,
        "large_files": large_files,
        "total_lines": total_lines,
        "avg_lines": round(avg_lines, 1),
        "readable_files": readable_files,
        "small_file_names": small_names,
        "fragmentation_score": round(fragmentation_score, 3),
    }
def _isolated_within_tolerance(isolated: int, total_modules: int,
                               orphan_tolerance: str) -> bool:
    return (orphan_tolerance == "high"
            and isolated <= max(2, int(total_modules * 0.15)))
def _struct_finding(findings: list, skill_dir: str, rule_id: str,
                    severity: str, message: str) -> None:
    findings.append(make_a2_finding(
        rule_id, severity, str(skill_dir), 0, message))
def _emit_cycle_findings(findings: list, skill_dir: str, mc: dict,
                         cycles: int) -> None:
    if cycles > 0:
        _struct_finding(
            findings, skill_dir, "MODULE-CYCLE", "P1",
            f"模块循环依赖(加载期硬环): {cycles} 个环"
            f"，详情: {(mc.get('cycle_details') or [])[:3]}")
def _emit_isolated_findings(findings: list, skill_dir: str, st: dict,
                            mc: dict, isolated: int) -> None:
    if isolated > 0 and not _isolated_within_tolerance(
            isolated, mc.get("total_modules") or 1,
            st.get("orphan_tolerance") or "normal"):
        _struct_finding(
            findings, skill_dir, "MODULE-ISOLATED", "P2",
            f"孤立模块: {isolated} 个（技能类型={st.get('type')}）"
            f"，详情: {(mc.get('isolated_names') or [])[:5]}")
def _emit_frag_findings(findings: list, skill_dir: str, fr: dict,
                        frag_score: float) -> None:
    if frag_score <= 0.3:
        return
    detail = f"，详情: {(fr.get('small_file_names') or [])[:5]}"
    if frag_score > 0.5:
        severity = "P2"
        message = (f"文件碎片化: 小文件占比 {fr.get('small_files') or 0}"
                  f"/{fr.get('readable_files') or fr.get('total_files') or 0}"
                  f" (score={frag_score})")
    else:
        severity = "P3"
        message = f"轻度文件碎片化 (score={frag_score})"
    _struct_finding(findings, skill_dir, "FILE-FRAG", severity, message + detail)
def analyze_structural_health(skill_dir: str, findings: list, payload_parts: dict,
                              skill_type: dict, ctx=None) -> None:
    mc = analyze_module_coupling(skill_dir, ctx)
    fr = analyze_fragmentation(skill_dir, ctx)
    cycles = mc.get("cycles") or 0
    _emit_cycle_findings(findings, skill_dir, mc, cycles)
    isolated = mc.get("isolated_modules") or 0
    _emit_isolated_findings(findings, skill_dir, skill_type, mc, isolated)
    frag_score = fr.get("fragmentation_score") or 0.0
    _emit_frag_findings(findings, skill_dir, fr, frag_score)
    payload_parts["structural"] = {
        "skill_type": skill_type.get("type"),
        "orphan_tolerance": skill_type.get("orphan_tolerance"),
        "cycles": cycles,
        "soft_cycles": mc.get("soft_cycles") or 0,
        "isolated_modules": isolated,
        "total_modules": mc.get("total_modules") or 0,
        "fragmentation_score": frag_score,
        "small_files": fr.get("small_files") or 0,
    }
    _a2_dep_integrity(skill_dir, findings, payload_parts, ctx)
def _emit_dep_degraded(findings: list, skill_dir: str, channel: str,
                       error: BaseException) -> None:
    _struct_finding(
        findings, skill_dir, "STRUCT-DEGRADED", "P3",
        f"结构取证通道降级({channel}): {type(error).__name__}: {error}"
        "（该段发现可能缺失，建议复跑确认）")
def _a2_dep_integrity(skill_dir: str, findings: list, payload_parts: dict, ctx=None) -> None:
    try:
        msa = ModuleStructureAnalyzer(skill_dir, ctx=ctx)
        import_integrity = msa.import_integrity_findings()
    except Exception as e:
        logger.warning("[A2] 导入完整性取证异常（降级）: %s", e, exc_info=True)
        payload_parts["structural"]["dep_analysis"] = _dep_analysis_payload(
            [], {"degraded": True, "error": str(e)}, 0)
        _emit_dep_degraded(findings, skill_dir, "导入完整性", e)
        return
    try:
        api_contract = ApiContractAuditor(
            msa.skill_dir, msa.audit_py_files, msa.ctx).api_contract_analysis()
    except Exception as e:
        logger.warning("[A2] API 契约取证异常（降级）: %s", e, exc_info=True)
        api_contract = {"findings": [], "degraded": True, "error": str(e)}
        _emit_dep_degraded(findings, skill_dir, "API 契约", e)
    _append_domain_findings(findings, import_integrity)
    _append_domain_findings(findings, api_contract.get("findings", []))
    payload_parts["structural"]["dep_analysis"] = _dep_analysis_payload(
        import_integrity, api_contract, len(msa.py_files))
def _append_domain_findings(findings: list, items) -> None:
    for item in items:
        _fd = item.to_dict()
        _fd["source"] = "A2"
        findings.append(_fd)
def _dep_analysis_payload(import_integrity: list, api_contract: dict,
                          module_count: int) -> dict:
    counts = {"D9-BROKEN-IMPORT": 0, "D9-BROKEN-SYMBOL": 0,
              "D9-SELF-IMPORT": 0}
    for finding in import_integrity:
        if finding.rule_id in counts:
            counts[finding.rule_id] += 1
    return {
        "broken_imports": counts["D9-BROKEN-IMPORT"],
        "broken_symbols": counts["D9-BROKEN-SYMBOL"],
        "self_imports": counts["D9-SELF-IMPORT"],
        "api_contract_issues": len(api_contract.get("findings", [])),
        "module_count": module_count,
        "degraded": bool(api_contract.get("degraded")),
        "error": api_contract.get("error", ""),
    }

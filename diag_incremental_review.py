# ruff: noqa: I001
from __future__ import annotations
import argparse
import ast
import logging
import os
import re
import shutil
import subprocess
import time
from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field
from typing import Any, ClassVar
from jwsgj.build_contract import (
    DEFAULT_PROJECT_ROOT,
    cli_boundary,
    dump_json_report_checked,
    fail_cli,
    json_text,
    promote_single_dir,
    run_cli_action,
)
from jwsgj.build_skill_merge import (
    compute_current_snapshot,
    default_snapshot_dir,
    load_hash_snapshot,
    save_hash_snapshot,
    scan_py_files,
)
from jwsgj.diag_shared_ast_nodes import (
    block_may_fall_through,
    build_parent_map,
    calc_nesting,
    collect_param_names,
    dotted_name,
    is_safe_yaml_loader,
    iter_evaluation_scope_chain,
    iter_own_scope,
    iter_pattern_capture_names,
    iter_scope_nodes_with_shadow,
    iter_unpack_target_names,
    module_level_binding_names,
    resolve_call_name,
)
from jwsgj.diag_shared_source_core import read_source_with_fingerprint
from jwsgj.diag_traps_guard import (
    _sem_reachable_prefix,
    _sem_statement_may_raise,
)
from jwsgj.log_config import log_swallowed, trace_module_run
from jwsgj.runtime_scope import import_key
from jwsgj.shared_cache import get_warmed_cache
from jwsgj.prevention_scope_facts import walk_nodes
__all__ = [
    "INCREMENTAL_REVIEW_COMMANDS",
    "ImpactAnalysis",
    "IncrementalContext",
    "IncrementalGuard",
    "IncrementalGuardResult",
    "analyze_changed_files",
    "build_dependency_graph",
    "cmd_incremental_review",
    "detect_changed_py_files",
    "format_incremental_review",
    "register_incremental_review",
]
logger = logging.getLogger(__name__)
_MAX_FILES_FOR_FULL_GRAPH = 500
_MAX_DEPENDENCY_DEPTH = 3
_DEFAULT_ENABLE_IMPACT_ANALYSIS = True
def _root_text(project_root: Any) -> str:
    if project_root is None:
        return ""
    if isinstance(project_root, (bytes, bytearray)):
        return os.fsdecode(project_root)
    if isinstance(project_root, os.PathLike):
        return os.fsdecode(os.fspath(project_root))
    if isinstance(project_root, str):
        return project_root
    raise TypeError(
        "project_root 必须是 str、PathLike 或 None，"
        f"实际为 {type(project_root).__name__}")
def _validated_project_root(project_root: Any) -> str:
    if project_root is None:
        text = DEFAULT_PROJECT_ROOT
    else:
        text = _root_text(project_root)
        if not text.strip():
            raise ValueError("project_root 不得为空或纯空白；空路径不得回落到进程 cwd")
    root = os.path.abspath(text)
    if not os.path.isdir(root):
        raise NotADirectoryError(f"项目根目录不存在: {root}")
    return root
def _warm_shared_cache_tolerant(project_root: str) -> None:
    try:
        get_warmed_cache(project_root)
    except Exception as exc:  # noqa: BLE001 — 预热失败只影响下游缓存，不阻断审查
        logger.warning(
            "[Incremental] 共享缓存预热未完成（本次审查继续）: %s", exc)
@dataclass
class IncrementalContext:
    mode: str = "full"
    changed_files: list[str] = field(default_factory=list)
    deleted_files: list[str] = field(default_factory=list)
    affected_files: list[str] = field(default_factory=list)
    unchanged_files: list[str] = field(default_factory=list)
    reusable_methods: list[str] = field(default_factory=list)
    total_files: int = 0
    incremental_ratio: float = 1.0
    hash_snapshot: dict[str, str] = field(default_factory=dict)
    prev_snapshot: dict[str, str] = field(default_factory=dict)
    dependency_graph_built: bool = False
    dependency_graph: dict[str, set[str]] = field(
        default_factory=dict, repr=False)
    @property
    def is_incremental(self) -> bool:
        return self.mode == "incremental"
    @property
    def change_count(self) -> int:
        return len(self.changed_files) + len(self.deleted_files)
    def to_dict(self) -> dict:
        return {
            "mode": self.mode,
            "changed_files_count": len(self.changed_files),
            "deleted_files_count": len(self.deleted_files),
            "affected_files_count": len(self.affected_files),
            "unchanged_files_count": len(self.unchanged_files),
            "total_files": self.total_files,
            "incremental_ratio": round(self.incremental_ratio, 3),
            "reusable_methods": self.reusable_methods,
            "dependency_graph_built": self.dependency_graph_built,
        }
_SURROGATE_RE = re.compile('[\ud800-\udfff]')
def _display_text(text: str) -> str:
    if _SURROGATE_RE.search(text):
        return text.encode('utf-8', 'backslashreplace').decode('utf-8')
    return text
def _extract_imports(filepath: str, skill_dir: str,
                     allow_missing: set[str] | None = None, *,
                     strict: bool = False) -> set[str]:
    deps: set[str] = set()
    content, _fingerprint = read_source_with_fingerprint(filepath)
    if content is None:
        logger.warning("[Incremental] 源文件不可读: %s",
                       _display_text(filepath))
        if strict:
            raise OSError(f"源文件不可读: {filepath}")
        return deps
    try:
        tree = ast.parse(content, filename=filepath)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
        logger.warning("[Incremental] 源文件解析失败: %s (%s)",
                       _display_text(filepath), e)
        if strict:
            raise ValueError(f"源文件解析失败: {filepath}: {e}") from e
        return deps
    _add_root_init_edge(skill_dir, deps, allow_missing)
    own_rel = os.path.relpath(filepath, skill_dir)
    _add_pkg_init_edges(own_rel, skill_dir, deps, allow_missing)
    file_dir = os.path.dirname(filepath)
    for node in walk_nodes(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                _resolve_import(alias.name, skill_dir, deps, allow_missing)
        elif isinstance(node, ast.ImportFrom):
            deps |= _resolve_import_from(node, skill_dir, file_dir, allow_missing)
    self_rel = os.path.relpath(filepath, skill_dir).replace("\\", "/")
    deps.discard(self_rel)
    return deps
def _import_from_prefix(node: ast.ImportFrom, file_dir: str,
                        skill_dir: str) -> str | None:
    if node.level <= 0:
        return node.module or ""
    base = file_dir
    for _ in range(node.level - 1):
        base = os.path.dirname(base)
    base_rel = os.path.relpath(base, skill_dir)
    if base_rel.startswith(".."):
        return None
    if base_rel == ".":
        return node.module or ""
    pkg = base_rel.replace(os.sep, ".")
    return f"{pkg}.{node.module}" if node.module else pkg
def _add_root_init_edge(skill_dir: str, deps: set[str],
                        allow_missing: set[str] | None = None) -> None:
    rel_init = "__init__.py"
    if (os.path.isfile(os.path.join(skill_dir, rel_init))
            or (allow_missing and rel_init in allow_missing)):
        deps.add(rel_init)
def _resolve_import_from(node: ast.ImportFrom, skill_dir: str,
                         file_dir: str,
                         allow_missing: set[str] | None = None) -> set[str]:
    deps: set[str] = set()
    prefix = _import_from_prefix(node, file_dir, skill_dir)
    if prefix is None:
        return deps
    if node.level > 0:
        _add_root_init_edge(skill_dir, deps, allow_missing)
    if prefix:
        _resolve_import(prefix, skill_dir, deps, allow_missing)
        for alias in node.names:
            _resolve_import(f"{prefix}.{alias.name}", skill_dir, deps,
                            allow_missing)
    else:
        for alias in node.names:
            _resolve_import(alias.name, skill_dir, deps, allow_missing)
    return deps
def _add_pkg_init_edges(parts_os: str, skill_dir: str, deps: set[str],
                        allow_missing: set[str] | None = None) -> None:
    segments = parts_os.split(os.sep)[:-1]
    acc: list[str] = []
    for seg in segments:
        acc.append(seg)
        pkg_dir = os.sep.join(acc)
        pkg_init = os.path.join(skill_dir, pkg_dir, "__init__.py")
        if os.path.isfile(pkg_init):
            deps.add(os.path.relpath(pkg_init, skill_dir).replace("\\", "/"))
            continue
        rel_init = pkg_dir.replace(os.sep, "/") + "/__init__.py"
        if allow_missing and rel_init in allow_missing:
            deps.add(rel_init)
def _resolve_import(module_name: str, skill_dir: str, deps: set[str],
                    allow_missing: set[str] | None = None) -> None:
    candidates = [module_name]
    _root_pkg = import_key(os.path.basename(os.path.normpath(skill_dir)))
    _head, _dot, _rest = module_name.partition(".")
    _root_qualified = bool(_root_pkg and _head == _root_pkg)
    if _root_qualified:
        candidates.append(_rest or "__init__")
    for _mod in candidates:
        if _resolve_import_candidate(_mod, skill_dir, deps, allow_missing):
            if _root_qualified and _rest:
                _add_root_init_edge(skill_dir, deps, allow_missing)
            return
def _resolve_import_candidate(_mod: str, skill_dir: str, deps: set[str],
                              allow_missing: set[str] | None) -> bool:
    parts = _mod.replace(".", os.sep)
    source_roots = [skill_dir]
    src_root = os.path.join(skill_dir, "src")
    has_missing_src = any(
        os.fsdecode(rel).replace("\\", "/").lower().startswith("src/")
        for rel in (allow_missing or ())
    )
    if os.path.isdir(src_root) or has_missing_src:
        source_roots.append(src_root)
    for source_root in source_roots:
        source_prefix = os.path.relpath(source_root, skill_dir)
        prefix = "" if source_prefix == "." else source_prefix + os.sep
        project_parts = prefix + parts
        rel_base = project_parts.replace(os.sep, "/")
        probes = (
            (os.path.join(source_root, parts, "__init__.py"),
             rel_base + "/__init__.py"),
            (os.path.join(source_root, parts + ".py"), rel_base + ".py"),
        )
        for fs_path, rel_missing in probes:
            if os.path.isfile(fs_path):
                rel = os.path.relpath(fs_path, skill_dir).replace("\\", "/")
            elif allow_missing and rel_missing in allow_missing:
                rel = rel_missing
            else:
                continue
            deps.add(rel)
            _add_pkg_init_edges(
                project_parts, skill_dir, deps, allow_missing)
            return True
    return False
def build_dependency_graph(skill_dir: str,
                          allow_missing: set[str] | None = None, *,
                          strict: bool = False) -> dict[str, set[str]]:
    py_files = scan_py_files(skill_dir, strict=strict)
    graph: dict[str, set[str]] = {}
    for fp in py_files:
        rel = os.path.relpath(fp, skill_dir).replace("\\", "/")
        imports = _extract_imports(
            fp, skill_dir, allow_missing, strict=strict)
        graph[rel] = imports
    logger.info("[Incremental] 依赖图构建完成: %d 个文件, %d 条边",
                len(graph), sum(len(v) for v in graph.values()))
    return graph
def _dependency_items(deps: Any) -> tuple[str, ...]:
    if deps is None:
        return ()
    if isinstance(deps, (str, bytes, os.PathLike)):
        candidates = (deps,)
    elif isinstance(deps, Iterable):
        try:
            candidates = tuple(deps)
        except Exception as exc:  # noqa: BLE001 — 任意可迭代载体可能自定义异常
            logger.warning("[Incremental] 依赖集合物化失败，按单条处理: %s", exc)
            candidates = (deps,)
    else:
        candidates = (deps,)
    paths: list[str] = []
    dirty = 0
    for candidate in candidates:
        try:
            paths.append(os.fsdecode(candidate))
        except TypeError:
            dirty += 1
    if dirty:
        logger.warning("[Incremental] 跳过 %d 个非路径依赖条目", dirty)
    return tuple(paths)
def build_reverse_graph(graph: Mapping[str, Any] | None) -> dict[str, set[str]]:
    reverse: dict[str, set[str]] = {}
    if not isinstance(graph, Mapping):
        return reverse
    for src, deps in graph.items():
        try:
            source = os.fsdecode(src).replace("\\", "/")
        except TypeError:
            logger.warning("[Incremental] 跳过非路径依赖图源节点: %r", src)
            continue
        for dep in _dependency_items(deps):
            reverse.setdefault(_graph_key(dep), set()).add(source)
    return reverse
def _changed_file_items(changed_files: Any) -> list[str]:
    if changed_files is None:
        return []
    if isinstance(changed_files, (str, bytes, os.PathLike)):
        changed_files = [changed_files]
    if not isinstance(changed_files, Iterable):
        changed_files = [changed_files]
    return [
        path.replace("\\", "/")
        for path in _decode_changed_paths(changed_files)
    ]
def compute_affected_files(
    changed_files: Any,
    dependency_graph: Mapping[str, Any] | None,
    max_depth: int = _MAX_DEPENDENCY_DEPTH,
) -> set[str]:
    reverse_graph = build_reverse_graph(dependency_graph)
    affected = set(_changed_file_items(changed_files))
    frontier = set(affected)
    visited = {_graph_key(path) for path in affected}
    for _depth in range(max_depth):
        next_frontier = {
            dependent
            for current in frontier
            for dependent in reverse_graph.get(_graph_key(current), ())
            if _graph_key(dependent) not in visited
        }
        if not next_frontier:
            break
        affected.update(next_frontier)
        visited.update(_graph_key(path) for path in next_frontier)
        frontier = next_frontier
    return affected
def _diff_snapshots(current_snapshot: dict[str, str],
                   prev_snapshot: dict[str, str]) -> tuple[set[str], set[str]]:
    changed_rels: set[str] = set()
    for rel, h in current_snapshot.items():
        if prev_snapshot.get(rel) != h:
            changed_rels.add(rel)
    deleted_rels = set(prev_snapshot.keys()) - set(current_snapshot.keys())
    if deleted_rels:
        logger.info("[Incremental] 检测到 %d 个已删除文件", len(deleted_rels))
    new_rels = set(current_snapshot.keys()) - set(prev_snapshot.keys())
    if new_rels:
        logger.info("[Incremental] 检测到 %d 个新增文件", len(new_rels))
        changed_rels.update(new_rels)
    return changed_rels, deleted_rels
def _resolve_affected_files(skill_dir: str, changed_rels: set[str],
                            deleted_rels: set[str], total_files: int
                            ) -> tuple[list[str], bool, dict[str, set[str]] | None]:
    try:
        if total_files <= _MAX_FILES_FOR_FULL_GRAPH:
            dep_graph = build_dependency_graph(
                skill_dir, allow_missing=deleted_rels, strict=True)
        else:
            logger.info("[Incremental] 项目较大 (%d 文件)，使用局部依赖图", total_files)
            dep_graph = _build_local_dependency_graph(skill_dir, changed_rels,
                                                       deleted_rels=deleted_rels)
        affected_rels = compute_affected_files(
            list(changed_rels | deleted_rels), dep_graph)
        affected_abs = [
            os.path.join(skill_dir, rel) for rel in sorted(affected_rels)
            if os.path.isfile(os.path.join(skill_dir, rel))
        ]
        return affected_abs, True, dep_graph
    except Exception as e:  # noqa: BLE001 — 任意建图失败均须回退全量，避免漏审
        logger.warning("[Incremental] 依赖图构建失败，回退全部当前 Python 文件: %s", e)
        return scan_py_files(skill_dir, strict=True), False, None
def compute_incremental_scope(
    skill_dir: str,
    report_dir: str,
    force_full: bool = False,
    *,
    enable_impact_analysis: bool = _DEFAULT_ENABLE_IMPACT_ANALYSIS,
) -> IncrementalContext:
    ctx = IncrementalContext()
    current_snapshot = compute_current_snapshot(skill_dir)
    ctx.hash_snapshot = current_snapshot
    ctx.total_files = len(current_snapshot)
    if force_full:
        return _ctx_full_mode(ctx, skill_dir, "强制全量模式")
    prev_snapshot = load_hash_snapshot(report_dir)
    if prev_snapshot is None:
        return _ctx_full_mode(ctx, skill_dir, "无历史快照")
    ctx.prev_snapshot = prev_snapshot
    changed_rels, deleted_rels = _diff_snapshots(current_snapshot, prev_snapshot)
    if not changed_rels and not deleted_rels:
        logger.info("[Incremental] 无文件变更，但仍执行诊断（方法可能需刷新）")
        ctx.mode = "incremental"
        ctx.changed_files = []
        ctx.affected_files = []
        ctx.unchanged_files = [os.path.join(skill_dir, rel)
                               for rel in sorted(current_snapshot)]
        ctx.incremental_ratio = 0.0
        ctx.reusable_methods = []
        return ctx
    return _ctx_changed_mode(
        ctx, skill_dir, current_snapshot, changed_rels, deleted_rels,
        enable_impact_analysis=enable_impact_analysis)
def _ctx_full_mode(ctx: IncrementalContext, skill_dir: str,
                   reason: str) -> IncrementalContext:
    ctx.mode = "full"
    ctx.affected_files = sorted(
        os.path.join(skill_dir, rel) for rel in ctx.hash_snapshot)
    logger.info("[Incremental] %s，执行全量模式（%d 文件）",
                reason, len(ctx.affected_files))
    return ctx
def _ctx_changed_mode(ctx: IncrementalContext, skill_dir: str,
                      current_snapshot: dict[str, str],
                      changed_rels: set[str],
                      deleted_rels: set[str], *,
                      enable_impact_analysis: bool = _DEFAULT_ENABLE_IMPACT_ANALYSIS) -> IncrementalContext:
    changed_abs = [os.path.join(skill_dir, rel) for rel in sorted(changed_rels)
                   if os.path.isfile(os.path.join(skill_dir, rel))]
    ctx.changed_files = changed_abs
    ctx.deleted_files = [os.path.join(skill_dir, rel)
                         for rel in sorted(deleted_rels)]
    if enable_impact_analysis:
        (ctx.affected_files, ctx.dependency_graph_built,
         reusable_graph) = _resolve_affected_files(
            skill_dir, changed_rels, deleted_rels, ctx.total_files)
        if reusable_graph is not None:
            ctx.dependency_graph = reusable_graph
    else:
        ctx.affected_files = list(changed_abs)
        ctx.dependency_graph_built = False
        logger.info("[Incremental] 影响分析已关闭，仅审查变更文件")
    affected_rel_set = {
        os.path.relpath(fp, skill_dir).replace("\\", "/")
        for fp in ctx.affected_files
    }
    ctx.unchanged_files = [
        os.path.join(skill_dir, rel)
        for rel in sorted(current_snapshot)
        if rel not in affected_rel_set
    ]
    ctx.incremental_ratio = len(ctx.affected_files) / max(ctx.total_files, 1)
    ctx.mode = "incremental"
    logger.info(
        "[Incremental] 增量分析: %d 变更 -> %d 受影响 / %d 总计 (比例 %.1f%%, 依赖图=%s)",
        len(changed_rels),
        len(ctx.affected_files),
        ctx.total_files,
        ctx.incremental_ratio * 100,
        "已构建" if ctx.dependency_graph_built else "未构建",
    )
    return ctx
def _package_probe_names(path: str, skill_dir: str) -> set[str]:
    parent = os.path.basename(os.path.dirname(path))
    if parent:
        return {parent}
    root_pkg = import_key(os.path.basename(os.path.normpath(skill_dir)))
    return {root_pkg} if root_pkg else set()
def _module_probe_names(targets: set[str], skill_dir: str) -> set[str]:
    names: set[str] = set()
    for t in targets:
        _stem = os.path.splitext(os.path.basename(t))[0]
        names.add(_stem)
        if _stem == "__init__":
            names |= _package_probe_names(t, skill_dir)
    return names
def _package_init_probe_dirs(targets: set[str]) -> set[str]:
    package_dirs: set[str] = set()
    suffix = "/__init__.py"
    for target in targets:
        rel = target.replace("\\", "/").strip("/")
        if rel == "__init__.py":
            package_dirs.add("")
        elif rel.endswith(suffix):
            package_dirs.add(rel[:-len(suffix)])
    return package_dirs
def _inside_any_package(rel: str, package_dirs: set[str]) -> bool:
    return any(
        not package_dir or rel.startswith(package_dir + "/")
        for package_dir in package_dirs)
@dataclass
class _LocalGraphState:
    skill_dir: str
    deleted_rels: set[str] | None = None
    resolved: set[str] = field(default_factory=set)
    graph: dict[str, set[str]] = field(default_factory=dict)
    _py_files: list[str] = field(default_factory=list, init=False, repr=False)
    _source: dict[str, str] = field(
        default_factory=dict, init=False, repr=False)
    def _source_of(self, fp: str) -> str:
        if fp not in self._source:
            source, _fingerprint = read_source_with_fingerprint(fp)
            if source is None:
                logger.warning(
                    "[Incremental] 局部图源文件读取失败，终止局部建图: %s", fp)
                raise OSError(f"局部图源文件不可读: {fp}")
            self._source[fp] = source
        return self._source[fp]
    def _project_files(self) -> list[str]:
        if not self._py_files:
            self._py_files = scan_py_files(self.skill_dir, strict=True)
        return self._py_files
    def scan_round(self, targets: set[str], module_names: set[str],
                   package_dirs: set[str]) -> set[str]:
        new_resolved: set[str] = set()
        probe_names = {os.path.normcase(name) for name in module_names}
        for fp in self._project_files():
            rel = os.path.relpath(fp, self.skill_dir).replace("\\", "/")
            if rel in self.resolved:
                continue
            content = os.path.normcase(self._source_of(fp))
            if (rel in targets
                    or _inside_any_package(rel, package_dirs)
                    or any(name in content for name in probe_names)):
                self.graph[rel] = _extract_imports(
                    fp, self.skill_dir, self.deleted_rels, strict=True)
                new_resolved.add(rel)
        return new_resolved
def _build_local_dependency_graph(
    skill_dir: str,
    changed_rels: set[str],
    deleted_rels: set[str] | None = None,
) -> dict[str, set[str]]:
    state = _LocalGraphState(skill_dir, deleted_rels)
    _start = set(changed_rels) | set(deleted_rels or ())
    seen_targets = set(_start)
    targets = set(_start)
    while targets:
        module_names = _module_probe_names(targets, skill_dir)
        package_dirs = _package_init_probe_dirs(targets)
        new_resolved = state.scan_round(targets, module_names, package_dirs)
        if not new_resolved:
            break
        state.resolved |= new_resolved
        affected = compute_affected_files(list(_start), state.graph)
        targets = {a for a in affected if a not in seen_targets}
        seen_targets |= targets
    return state.graph
@dataclass
class ImpactAnalysis:
    file: str = ""
    hot_path: bool = False
    affected_modules: list[str] = field(default_factory=list)
    affected_modules_total: int = 0
    risk_level: str = "low"
@dataclass
class IncrementalGuardResult:
    total_issues: int = 0
    critical_issues: int = 0
    regression_risk_score: float = 0.0
    impact_analyses: list[ImpactAnalysis] = field(default_factory=list)
    issues: list[dict[str, Any]] = field(default_factory=list)
    def to_dict(self) -> dict[str, Any]:
        return {
            "total_issues": self.total_issues,
            "critical_issues": self.critical_issues,
            "regression_risk_score": self.regression_risk_score,
            "impact_analyses": [
                {
                    "file": ia.file,
                    "hot_path": ia.hot_path,
                    "affected_modules": list(ia.affected_modules),
                    "affected_modules_total": ia.affected_modules_total,
                    "risk_level": ia.risk_level,
                }
                for ia in self.impact_analyses
            ],
            "issues": [dict(issue) for issue in self.issues],
        }
def _issue(filepath: str, rule_id: str, severity: str,
           message: str, line: int = 0) -> dict[str, Any]:
    return {"file": filepath, "rule_id": rule_id, "severity": severity,
            "message": message, "line": line}
_YAML_LOADER_AWARE_CALLS = frozenset({"yaml.load", "yaml.load_all"})
_SNAPSHOT_RETRY_RULES = frozenset({
    "INC-02", "INC-03", "INC-SEC-04", "INC-CMPX-03",
})
def _graph_key(value: str) -> str:
    return os.path.normcase(value.replace("\\", "/")).replace("\\", "/")
_LEXICAL_LOCAL_SCOPES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
def _node_position(node: ast.AST) -> tuple[int, int]:
    return getattr(node, "lineno", -1), getattr(node, "col_offset", -1)
def _node_end_position(node: ast.AST) -> tuple[int, int]:
    return (getattr(node, "end_lineno", None) or getattr(node, "lineno", -1),
            getattr(node, "end_col_offset", None)
            if getattr(node, "end_col_offset", None) is not None
            else getattr(node, "col_offset", -1))
def _node_contains(outer: ast.AST, inner: ast.AST) -> bool:
    return (_node_position(outer) <= _node_position(inner)
            and _node_position(inner) <= _node_end_position(outer))
def _binding_event_names(node: ast.AST) -> set[str]:
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return {node.name}
    if isinstance(node, ast.Assign):
        return {name for target in node.targets
                for name in iter_unpack_target_names(target)}
    if isinstance(node, ast.AnnAssign):
        return (set(iter_unpack_target_names(node.target))
                if node.value is not None else set())
    if isinstance(node, ast.AugAssign):
        return set(iter_unpack_target_names(node.target))
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return set(iter_unpack_target_names(node.target))
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return ({name for item in node.items if item.optional_vars is not None
                 for name in iter_unpack_target_names(item.optional_vars)}
                | {name for item in node.items
                   for name in _expr_binding_names(item.context_expr)})
    if isinstance(node, ast.ExceptHandler):
        return {node.name} if node.name else set()
    if isinstance(node, ast.Match):
        return {name for case in node.cases
                for name in iter_pattern_capture_names(case.pattern)}
    if isinstance(node, ast.NamedExpr):
        return set(iter_unpack_target_names(node.target))
    if isinstance(node, ast.Delete):
        return {name for target in node.targets
                for name in iter_unpack_target_names(target)}
    if isinstance(node, ast.comprehension):
        return set(iter_unpack_target_names(node.target))
    return set()
def _binding_events(tree: ast.AST) -> list[ast.AST]:
    events = []
    for node in iter_own_scope(tree):
        if isinstance(node, ast.comprehension):
            continue
        if (isinstance(node, (ast.Import, ast.ImportFrom))
                or _binding_event_names(node)):
            events.append(node)
    return sorted(events, key=_node_position)
def _inside_blocks(call: ast.AST, blocks: Iterable[Iterable[ast.AST]]) -> bool:
    return any(_node_contains(statement, call)
               for block in blocks for statement in block)
def _binding_event_names_at_call(node: ast.AST, call: ast.AST) -> set[str]:
    if isinstance(node, ast.Match):
        for case in node.cases:
            in_guard = (case.guard is not None
                        and _node_contains(case.guard, call))
            if in_guard or _inside_blocks(call, (case.body,)):
                return set(iter_pattern_capture_names(case.pattern))
    elif isinstance(node, (ast.With, ast.AsyncWith)):
        for index, item in enumerate(node.items):
            if _node_contains(item.context_expr, call):
                names = {
                    name
                    for previous in node.items[:index]
                    if previous.optional_vars is not None
                    for name in iter_unpack_target_names(previous.optional_vars)
                }
                for previous in node.items[:index]:
                    names |= _expr_binding_names(previous.context_expr)
                names |= _expr_binding_names(item.context_expr, before=call)
                return names
    return _binding_event_names(node)
def _safe_binding_options(names: Iterable[str]) -> dict[str, frozenset[Any]]:
    return {name: frozenset({("", "")}) for name in names}
def _expr_binding_names(expr: ast.AST | None,
                        before: ast.AST | None = None) -> set[str]:
    """条件/上下文/简单语句中赋值表达式（:=）在所在作用域绑定的名字。

    PEP 572：赋值表达式绑定到所在作用域，lambda/def/class 体内除外，推导式内
    的赋值表达式同样绑定外层。``before`` 给定时只计入在其之前已完成求值的
    赋值表达式（右侧表达式求值完成后绑定才生效）。
    """
    if expr is None:
        return set()
    names: set[str] = set()
    stack: list[ast.AST] = [expr]
    while stack:
        current = stack.pop()
        if isinstance(current, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef,
                                ast.ClassDef)):
            continue
        if (isinstance(current, ast.NamedExpr)
                and (before is None
                     or _node_end_position(current.value) <= _node_position(before))):
            names |= set(iter_unpack_target_names(current.target))
        stack.extend(ast.iter_child_nodes(current))
    return names
def _expr_binding_options(expr: ast.AST | None,
                          before: ast.AST | None = None,
                          ) -> dict[str, frozenset[Any]]:
    return _safe_binding_options(_expr_binding_names(expr, before))
def _loop_test_expr(node: ast.stmt) -> ast.expr | None:
    return node.test if isinstance(node, ast.While) else getattr(node, "iter", None)
def _with_expr_bindings(
    bound: dict[str, frozenset[Any]], expr: ast.AST | None,
    before: ast.AST | None = None,
) -> dict[str, frozenset[Any]]:
    result = dict(bound)
    result.update(_expr_binding_options(expr, before))
    return result
def _import_binding_options(node: ast.AST) -> dict[str, frozenset[Any]]:
    if isinstance(node, ast.Import):
        result: dict[str, frozenset[Any]] = {}
        for alias in node.names:
            top = alias.name.split(".")[0]
            local = alias.asname or top
            canonical = alias.name if alias.asname else top
            module = (canonical if canonical in IncrementalGuard._WATCHED_MEMBERS
                      else "")
            result[local] = frozenset({(module, "")})
        return result
    if isinstance(node, ast.ImportFrom):
        result = {}
        watched = (frozenset() if node.level else
                   IncrementalGuard._WATCHED_MEMBERS.get(
                       node.module or "", frozenset()))
        for alias in node.names:
            if alias.name == "*":
                for member in watched:
                    result[member] = frozenset({
                        ("", f"{node.module}.{member}")})
                continue
            local = alias.asname or alias.name
            member = (f"{node.module}.{alias.name}"
                      if alias.name in watched else "")
            result[local] = frozenset({("", member)})
        return result
    return {}
def _event_binding_options(
    node: ast.AST, before: ast.Call | None = None,
) -> dict[str, frozenset[Any]]:
    imported = _import_binding_options(node)
    if imported or isinstance(node, (ast.Import, ast.ImportFrom)):
        return imported
    names = (_binding_event_names_at_call(node, before)
             if before is not None else _binding_event_names(node))
    return _safe_binding_options(names)
def _assign_binding_options(
    state: dict[str, frozenset[Any]], node: ast.AST,
    before: ast.Call | None = None,
) -> dict[str, frozenset[Any]]:
    result = dict(state)
    result.update(_event_binding_options(node, before))
    return result
def _merge_possible_bindings(
    paths: Iterable[dict[str, frozenset[Any]]],
) -> dict[str, frozenset[Any]]:
    materialized = list(paths)
    if not materialized:
        return {}
    merged: dict[str, frozenset[Any]] = {}
    for name in set().union(*(path.keys() for path in materialized)):
        options: set[Any] = set()
        for path in materialized:
            options.update(path.get(name, frozenset({None})))
        merged[name] = frozenset(options)
    return merged
def _possible_after_block(
    statements: Iterable[ast.stmt], bound: dict[str, frozenset[Any]],
) -> dict[str, frozenset[Any]]:
    result = dict(bound)
    for statement in statements:
        result = _possible_after_statement(statement, result)
    return result
def _possible_exception_entry(
    statements: Iterable[ast.stmt], bound: dict[str, frozenset[Any]],
) -> dict[str, frozenset[Any]]:
    current = dict(bound)
    exceptional: list[dict[str, frozenset[Any]]] = []
    # 简单语句异常发生在绑定生效前；复合语句还需保留其部分执行状态。
    simple_stmts = (ast.Assign, ast.AnnAssign, ast.AugAssign,
                    ast.Expr, ast.Delete, ast.Import, ast.ImportFrom)
    for statement in _sem_reachable_prefix(list(statements)):
        before = dict(current)
        current = _possible_after_statement(statement, current)
        if _sem_statement_may_raise(statement):
            exceptional.append(before)
            if not isinstance(statement, simple_stmts):
                exceptional.append(dict(current))
        if not block_may_fall_through([statement]):
            # return/break/continue 与 raise 同样会进入 finally。
            exceptional.append(current)
    return _merge_possible_bindings(exceptional or [current])
def _possible_after_try(
    node: ast.stmt, bound: dict[str, frozenset[Any]], *,
    include_final: bool = True,
) -> dict[str, frozenset[Any]]:
    normal = _possible_after_block(node.body, bound)
    normal = _possible_after_block(node.orelse, normal)
    paths = [normal]
    after_paths = ([normal] if block_may_fall_through(node.body)
                   and block_may_fall_through(node.orelse) else [])
    exception_entry = (_possible_exception_entry(node.body, bound)
                       if node.handlers or not include_final else {})
    if node.handlers:
        for handler in node.handlers:
            handler_bound = _assign_binding_options(exception_entry, handler)
            handler_result = _possible_after_block(handler.body, handler_bound)
            if handler.name:
                handler_result.pop(handler.name, None)
            paths.append(handler_result)
            if block_may_fall_through(handler.body):
                after_paths.append(handler_result)
    if not include_final:
        # finally 也会经过无处理器或类型处理器未覆盖的异常出口。
        if (not node.handlers
                or any(handler.type is not None for handler in node.handlers)):
            paths.append(exception_entry)
        return _merge_possible_bindings(paths)
    if not after_paths or not block_may_fall_through(node.finalbody):
        return {}
    merged = _merge_possible_bindings(after_paths)
    return _possible_after_block(node.finalbody, merged)
def _possible_after_statement(
    node: ast.stmt, bound: dict[str, frozenset[Any]],
) -> dict[str, frozenset[Any]]:
    if isinstance(node, ast.If):
        test_bound = dict(bound)
        test_bound.update(_expr_binding_options(node.test))
        paths = [
            _possible_after_block(block, test_bound)
            for block in (node.body, node.orelse)
            if block_may_fall_through(block)
        ]
        return _merge_possible_bindings(paths)
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        test_bound = dict(bound)
        test_bound.update(_expr_binding_options(_loop_test_expr(node)))
        loop_bound = _assign_binding_options(test_bound, node)
        body = _possible_after_block(node.body, loop_bound)
        resume = _merge_possible_bindings((test_bound, body))
        if node.orelse:
            after_else = _possible_after_block(node.orelse, resume)
            return _merge_possible_bindings((body, after_else))
        return resume
    if isinstance(node, (ast.With, ast.AsyncWith)):
        with_bound = _assign_binding_options(bound, node)
        body = _possible_after_block(node.body, with_bound)
        return _merge_possible_bindings((with_bound, body))
    if isinstance(node, ast.Try) or type(node).__name__ == "TryStar":
        return _possible_after_try(node, bound)
    if isinstance(node, ast.Match):
        paths = []
        exhaustive = False
        subject_bound = dict(bound)
        subject_bound.update(_expr_binding_options(node.subject))
        for case in node.cases:
            case_bound = dict(subject_bound)
            case_bound.update(_safe_binding_options(
                iter_pattern_capture_names(case.pattern)))
            if block_may_fall_through(case.body):
                paths.append(_possible_after_block(case.body, case_bound))
            if (case.guard is None and isinstance(case.pattern, ast.MatchAs)
                    and case.pattern.pattern is None):
                exhaustive = True
        if not exhaustive:
            paths.append(dict(subject_bound))
        return _merge_possible_bindings(paths)
    result = _assign_binding_options(bound, node)
    names = _expr_binding_names(node)
    if names:
        result.update(_safe_binding_options(names))
    return result
def _possible_before_block(
    statements: Iterable[ast.stmt], bound: dict[str, frozenset[Any]],
    call: ast.Call,
) -> dict[str, frozenset[Any]]:
    result = dict(bound)
    for statement in statements:
        if _node_contains(statement, call):
            return _possible_before_statement(statement, result, call)
        result = _possible_after_statement(statement, result)
    return result
def _possible_before_statement(
    node: ast.stmt, bound: dict[str, frozenset[Any]], call: ast.Call,
) -> dict[str, frozenset[Any]]:
    if isinstance(node, ast.If):
        if _node_contains(node.test, call):
            return _with_expr_bindings(bound, node.test, call)
        test_bound = _with_expr_bindings(bound, node.test)
        for block in (node.body, node.orelse):
            if _inside_blocks(call, (block,)):
                return _possible_before_block(block, test_bound, call)
        return dict(bound)
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        test_expr = _loop_test_expr(node)
        test_bound = _with_expr_bindings(bound, test_expr)
        loop_bound = _assign_binding_options(test_bound, node)
        if _node_contains(test_expr, call):
            before_call = _with_expr_bindings(bound, test_expr, call)
            if not isinstance(node, ast.While):
                return before_call
            later_iteration = _possible_after_block(node.body, loop_bound)
            later_iteration.update(_expr_binding_options(test_expr, before=call))
            return _merge_possible_bindings((before_call, later_iteration))
        if _inside_blocks(call, (node.body,)):
            later_iteration = _possible_after_block(node.body, loop_bound)
            iteration_entry = _merge_possible_bindings((
                loop_bound, later_iteration))
            return _possible_before_block(node.body, iteration_entry, call)
        if _inside_blocks(call, (node.orelse,)):
            body = _possible_after_block(node.body, loop_bound)
            resume = _merge_possible_bindings((test_bound, body))
            return _possible_before_block(node.orelse, resume, call)
        return dict(bound)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        for item in node.items:
            if _node_contains(item.context_expr, call):
                previous = _binding_event_names_at_call(node, call)
                bound = dict(bound)
                bound.update(_safe_binding_options(previous))
                return bound
        if _inside_blocks(call, (node.body,)):
            with_bound = _assign_binding_options(bound, node)
            return _possible_before_block(node.body, with_bound, call)
        return dict(bound)
    if isinstance(node, ast.Try) or type(node).__name__ == "TryStar":
        if _inside_blocks(call, (node.body,)):
            return _possible_before_block(node.body, bound, call)
        for handler in node.handlers:
            if _inside_blocks(call, (handler.body,)):
                exception_entry = _possible_exception_entry(node.body, bound)
                handler_bound = _assign_binding_options(exception_entry, handler)
                return _possible_before_block(handler.body, handler_bound, call)
        if _inside_blocks(call, (node.orelse,)):
            normal = _possible_after_block(node.body, bound)
            return _possible_before_block(node.orelse, normal, call)
        if _inside_blocks(call, (node.finalbody,)):
            before_final = _possible_after_try(node, bound, include_final=False)
            return _possible_before_block(node.finalbody, before_final, call)
        return dict(bound)
    if isinstance(node, ast.Match):
        if _node_contains(node.subject, call):
            return _with_expr_bindings(bound, node.subject, call)
        subject_bound = _with_expr_bindings(bound, node.subject)
        for case in node.cases:
            case_bound = dict(subject_bound)
            case_bound.update(_safe_binding_options(
                iter_pattern_capture_names(case.pattern)))
            if case.guard is not None and _node_contains(case.guard, call):
                return case_bound
            if _inside_blocks(call, (case.body,)):
                return _possible_before_block(case.body, case_bound, call)
        return dict(bound)
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return dict(bound)
    return _with_expr_bindings(bound, node, call)
def _possible_bindings(
    tree: ast.AST, before: ast.Call | None,
) -> dict[str, frozenset[Any]]:
    body = getattr(tree, "body", None)
    if not isinstance(body, list):
        return {}
    if before is None:
        return _possible_after_block(body, {})
    return _possible_before_block(body, {}, before)
def _merge_scope_aliases(
    target: dict[str, frozenset[str | None]], local: str,
    incoming: frozenset[str | None],
) -> None:
    existing = target.get(local)
    if existing is None:
        target[local] = incoming
        return
    if None not in existing:
        return
    concrete = (existing - {None}) | (incoming - {None})
    if None in incoming:
        concrete.add(None)
    target[local] = frozenset(concrete)
class IncrementalGuard:
    MAX_FUNC_LINES: ClassVar[int] = 150
    MAX_NESTING: ClassVar[int] = 4
    _DANGER_CALLS: ClassVar[set[str]] = {
        "eval", "exec", "builtins.eval", "builtins.exec",
        "os.system", "os.popen",
        "subprocess.getoutput", "subprocess.getstatusoutput",
    }
    _UNSAFE_LOADS: ClassVar[set[str]] = {
        "pickle.load", "pickle.loads", "marshal.load", "marshal.loads",
        "yaml.load", "yaml.load_all", "yaml.full_load",
        "yaml.full_load_all", "yaml.unsafe_load", "yaml.unsafe_load_all",
    }
    _SUBPROCESS_FUNCS: ClassVar[frozenset[str]] = frozenset({
        "run", "call", "check_call", "check_output", "Popen",
        "getoutput", "getstatusoutput",
    })
    _WATCHED_MEMBERS: ClassVar[dict[str, frozenset[str]]] = {
        "builtins": frozenset({"eval", "exec"}),
        "os": frozenset({"system", "popen"}),
        "pickle": frozenset({"load", "loads"}),
        "marshal": frozenset({"load", "loads"}),
        "yaml": frozenset({
            "load", "load_all", "full_load", "full_load_all",
            "unsafe_load", "unsafe_load_all", "Loader", "FullLoader",
            "UnsafeLoader", "SafeLoader", "CSafeLoader", "BaseLoader",
            "CBaseLoader",
        }),
        "subprocess": _SUBPROCESS_FUNCS,
    }
    def __init__(self, project_root: str = DEFAULT_PROJECT_ROOT,
                 dependency_graph: Mapping[str, Any] | None = None) -> None:
        self.project_root = _validated_project_root(project_root)
        graph = (dependency_graph
                 if isinstance(dependency_graph, Mapping)
                 else build_dependency_graph(self.project_root))
        self._reverse_graph: dict[str, set[str]] = build_reverse_graph(graph)
        logger.info("[IncrementalGuard] 初始化: project_root=%s", self.project_root)
    def _find_importers(self, filepath: str) -> list[str]:
        try:
            rel = os.path.relpath(filepath, self.project_root).replace("\\", "/")
        except ValueError as _e:
            log_swallowed(__name__, _e, context='IncrementalGuard._find_importers:ValueError')
            return []
        return sorted(self._reverse_graph.get(_graph_key(rel), ()))
    def analyze_changes(self, changed_files: list[str] | None = None,
                        enable_impact_analysis: bool = _DEFAULT_ENABLE_IMPACT_ANALYSIS) -> IncrementalGuardResult:
        changed_files = _normalize_changed_files_input(
            changed_files or [], self.project_root)
        analyzed_files = [
            fpath for fpath in changed_files
            if fpath.lower().endswith(".py")]
        result = IncrementalGuardResult()
        for fpath in analyzed_files:
            file_issues, risk_level, hot_path, affected_modules = self._analyze_file(
                fpath, enable_impact_analysis)
            result.critical_issues += sum(
                1 for i in file_issues if i["severity"] == "critical")
            result.impact_analyses.append(ImpactAnalysis(
                file=fpath, hot_path=hot_path,
                affected_modules=affected_modules[:10],
                affected_modules_total=len(affected_modules),
                risk_level=risk_level,
            ))
            result.issues.extend(file_issues)
            result.total_issues += len(file_issues)
        hot_count = sum(1 for ia in result.impact_analyses if ia.hot_path)
        total_files = max(len(analyzed_files), 1)
        hot_ratio = hot_count / total_files
        weighted_severity = sum(
            self._SEVERITY_SCORE_WEIGHTS.get(issue["severity"], 0.0)
            for issue in result.issues
        )
        severity_ratio = weighted_severity / total_files
        result.regression_risk_score = round(
            min(1.0, severity_ratio * 0.6 + hot_ratio * 0.4), 2
        )
        logger.info(
            "[IncrementalGuard] 增量审查完成: %d Python 文件（输入 %d）, "
            "%d 问题 (%d critical), 风险=%.2f",
            len(analyzed_files), len(changed_files), result.total_issues,
            result.critical_issues, result.regression_risk_score)
        return result
    def _analyze_file(self, fpath: str,
                      enable_impact_analysis: bool
                      ) -> tuple[list[dict[str, Any]], str, bool, list[str]]:
        if not fpath.lower().endswith(".py"):
            return [], "low", False, []
        affected_modules = (
            self._find_importers(fpath) if enable_impact_analysis else [])
        if not os.path.isfile(fpath):
            return self._apply_impact(
                [_issue(fpath, "INC-01", "warn", f"文件不存在: {fpath}")],
                "low", affected_modules)
        syntax_ok, tree, file_issues, risk_level = self._syntax_check(fpath)
        if syntax_ok:
            sec_issues, cmpx_issues = self._scan_ok_file(tree, fpath)
            file_issues.extend(sec_issues)
            file_issues.extend(cmpx_issues)
            risk_level = self._escalate_risk(
                risk_level, sec_issues + cmpx_issues)
        return self._apply_impact(file_issues, risk_level, affected_modules)
    def _syntax_check(self, fpath: str
                      ) -> tuple[bool, ast.Module | None, list[dict[str, Any]], str]:
        source, _fingerprint = read_source_with_fingerprint(fpath)
        if source is None:
            return False, None, [
                _issue(fpath, "INC-03", "warn", "源码读取失败: 文件不可读或已删除")
            ], "low"
        try:
            tree = ast.parse(source, filename=fpath)
        except SyntaxError as e:
            log_swallowed(__name__, e, context='IncrementalGuard._syntax_check:SyntaxError')
            return False, None, [
                _issue(fpath, "INC-02", "critical",
                       f"语法错误: {e.msg} (line {e.lineno or 0})", e.lineno or 0)
            ], "critical"
        except (ValueError, RecursionError, MemoryError) as e:
            log_swallowed(__name__, e, context='IncrementalGuard._syntax_check:parse')
            return False, None, [
                _issue(fpath, "INC-03", "warn",
                       f"源码读取/解析失败: {type(e).__name__}: {e}")
            ], "low"
        return True, tree, [], "low"
    def _scan_ok_file(self, tree: ast.Module, fpath: str
                      ) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
        try:
            sec_issues = self._scan_security(tree, fpath)
        except Exception as scan_err:  # noqa: BLE001 — 扫描器故障须转为可见发现
            logger.warning("[IncrementalGuard] 安全扫描失败 %s: %s", fpath, scan_err)
            sec_issues = [_issue(
                fpath, "INC-SEC-04", "high",
                f"安全扫描失败: {type(scan_err).__name__}: {scan_err}",
            )]
        try:
            cmpx_issues = self._check_complexity(tree, fpath)
        except Exception as cmpx_err:  # noqa: BLE001 — 评估故障须转为可见发现
            logger.warning("[IncrementalGuard] 复杂度评估失败 %s: %s", fpath, cmpx_err)
            cmpx_issues = [_issue(
                fpath, "INC-CMPX-03", "medium",
                f"复杂度评估失败: {type(cmpx_err).__name__}: {cmpx_err}",
            )]
        return sec_issues, cmpx_issues
    _RISK_RANK: ClassVar[dict[str, int]] = {"low": 0, "medium": 1, "high": 2, "critical": 3}
    _RISK_NAMES: ClassVar[dict[int, str]] = {r: n for n, r in _RISK_RANK.items()}
    _SEVERITY_SCORE_WEIGHTS: ClassVar[dict[str, float]] = {
        "medium": 0.2, "high": 0.5, "critical": 1.0,
    }
    @staticmethod
    def _escalate_risk(risk_level: str,
                       issues: list[dict[str, Any]]) -> str:
        rank = IncrementalGuard._RISK_RANK.get(risk_level)
        if rank is None:
            return risk_level
        for issue in issues:
            sev_rank = IncrementalGuard._RISK_RANK.get(issue.get("severity", ""), 0)
            rank = max(rank, sev_rank)
        return IncrementalGuard._RISK_NAMES.get(rank, risk_level)
    @staticmethod
    def _apply_impact(file_issues: list[dict[str, Any]], risk_level: str,
                      affected_modules: list[str]
                      ) -> tuple[list[dict[str, Any]], str, bool, list[str]]:
        hot_path = len(affected_modules) > 5
        if hot_path and risk_level in ("low", "medium"):
            risk_level = "high"
        elif len(affected_modules) > 2 and risk_level == "low":
            risk_level = "medium"
        return file_issues, risk_level, hot_path, affected_modules
    def _scan_security(self, tree: ast.AST, filepath: str) -> list[dict[str, Any]]:
        issues: list[dict[str, Any]] = []
        parents = build_parent_map(tree)
        bindings_cache: dict[
            tuple[int, int], tuple[dict[str, frozenset[str | None]],
                                  dict[str, frozenset[str | None]], frozenset[str]]] = {}
        evaluation_shadows = {
            id(scope_node): shadowed
            for scope_node, shadowed in iter_scope_nodes_with_shadow(tree)
            if isinstance(scope_node, ast.Call) and shadowed
        }
        for node in walk_nodes(tree):
            if not isinstance(node, ast.Call):
                continue
            module_aliases: dict[str, frozenset[str | None]] = {}
            member_aliases: dict[str, frozenset[str | None]] = {}
            shadowed_names: set[str] = set()
            scope_chain = iter_evaluation_scope_chain(node, parents)
            for index, scope in enumerate(scope_chain):
                if index == 0:
                    scope_modules, scope_members, scope_bound = (
                        self._call_bindings(scope, before=node))
                else:
                    nested_scope = scope_chain[index - 1]
                    scope_key = (id(scope), id(nested_scope))
                    if scope_key not in bindings_cache:
                        bindings_cache[scope_key] = self._outer_call_bindings(
                            scope, nested_scope)
                    scope_modules, scope_members, scope_bound = (
                        bindings_cache[scope_key])
                for local, canonical in scope_modules.items():
                    if local not in shadowed_names:
                        _merge_scope_aliases(module_aliases, local, canonical)
                for local, canonical in scope_members.items():
                    if local not in shadowed_names:
                        _merge_scope_aliases(member_aliases, local, canonical)
                for local in scope_bound:
                    module_aliases.setdefault(local, frozenset({""}))
                    member_aliases.setdefault(local, frozenset({""}))
                shadowed_names.update(scope_bound)
            for local in evaluation_shadows.get(id(node), ()):
                module_aliases[local] = frozenset({""})
                member_aliases[local] = frozenset({""})
            call_names = self._canonical_call_names(
                resolve_call_name(node), module_aliases, member_aliases)
            danger_calls = sorted(call_names & self._DANGER_CALLS)
            if danger_calls:
                issues.append(_issue(
                    filepath, "INC-SEC-01", "critical",
                    f"{danger_calls[0]}() 高危调用 (line {node.lineno})", node.lineno))
            else:
                unsafe_calls = sorted(call_names & self._UNSAFE_LOADS)
                for call_name in unsafe_calls:
                    if (call_name in _YAML_LOADER_AWARE_CALLS
                            and self._yaml_load_is_safe(
                                node, module_aliases, member_aliases)):
                        continue
                    issues.append(_issue(
                        filepath, "INC-SEC-02", "high",
                        f"{call_name}() 不安全加载 (line {node.lineno})", node.lineno))
                    break
            for call_name in sorted(call_names):
                shell_issues = self._shell_true_issues(node, filepath, call_name)
                if shell_issues:
                    issues.extend(shell_issues)
                    break
        return issues
    @staticmethod
    def _direct_nested_calls(
            scope: ast.AST, nested_scope: ast.AST) -> tuple[ast.Call, ...]:
        if not isinstance(nested_scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return ()
        name = nested_scope.name
        return tuple(
            node for node in iter_own_scope(scope)
            if isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == name
        )
    def _outer_call_bindings(
            self, scope: ast.AST, nested_scope: ast.AST
    ) -> tuple[dict[str, frozenset[str | None]],
               dict[str, frozenset[str | None]], frozenset[str]]:
        """合并外层终态与嵌套函数直接调用点可见的词法绑定。"""
        snapshots = [self._call_bindings(scope)]
        snapshots.extend(
            self._call_bindings(scope, before=call)
            for call in self._direct_nested_calls(scope, nested_scope)
        )
        modules: dict[str, frozenset[str | None]] = {}
        members: dict[str, frozenset[str | None]] = {}
        for snapshot in snapshots:
            for local, canonical in snapshot[0].items():
                modules[local] = modules.get(local, frozenset()) | canonical
            for local, canonical in snapshot[1].items():
                members[local] = members.get(local, frozenset()) | canonical
        return modules, members, snapshots[0][2]
    @staticmethod
    def _call_bindings(
            tree: ast.AST, *, before: ast.Call | None = None,
    ) -> tuple[dict[str, frozenset[str | None]],
               dict[str, frozenset[str | None]], frozenset[str]]:
        modules: dict[str, frozenset[str | None]] = {}
        members: dict[str, frozenset[str | None]] = {}
        events = _binding_events(tree)
        possible = _possible_bindings(tree, before)
        bound_names = set(collect_param_names(tree))
        if isinstance(getattr(tree, "body", None), list):
            bound_names |= module_level_binding_names(tree)
        for node in events:
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                for alias in node.names:
                    bound_names.add(alias.asname or alias.name)
            else:
                bound_names |= _binding_event_names(node)
        lexical_locals = isinstance(tree, _LEXICAL_LOCAL_SCOPES)
        redirected = {
            name for node in iter_own_scope(tree)
            if isinstance(node, (ast.Global, ast.Nonlocal))
            for name in node.names
        }
        shadowed = set(bound_names) if lexical_locals else set()
        for name, options in possible.items():
            if lexical_locals and name not in redirected:
                options = {option for option in options if option is not None}
            modules[name] = frozenset(
                None if option is None else option[0] for option in options)
            members[name] = frozenset(
                None if option is None else option[1] for option in options)
            if not lexical_locals and None not in options:
                shadowed.add(name)
        if lexical_locals:
            shadowed |= bound_names
        shadowed -= redirected
        return modules, members, frozenset(shadowed)
    @staticmethod
    def _canonical_call_names(
            call_name: str, module_aliases: dict[str, Any],
            member_aliases: dict[str, Any]) -> frozenset[str]:
        if not call_name:
            return frozenset()
        head, _, tail = call_name.rpartition(".")
        aliases = module_aliases if head else member_aliases
        local = head or call_name
        if local not in aliases:
            return frozenset({call_name})
        values = aliases[local]
        if isinstance(values, str):
            values = frozenset({values})
        names: set[str] = set()
        for value in values:
            if value is None:
                names.add(call_name)
                continue
            names.add(f"{value}.{tail}" if head and value else
                      "" if head else value)
        return frozenset(names)
    @staticmethod
    def _yaml_load_is_safe(
            node: ast.Call, module_aliases: dict[str, Any],
            member_aliases: dict[str, Any]) -> bool:
        loader = (node.args[1] if len(node.args) > 1 else next(
            (kw.value for kw in node.keywords if kw.arg == "Loader"), None))
        if loader is None:
            return False
        raw_name = dotted_name(loader)
        if isinstance(loader, ast.Name):
            if loader.id not in member_aliases:
                return False
        elif raw_name.partition(".")[0] not in module_aliases:
            return False
        canonical_names = IncrementalGuard._canonical_call_names(
            raw_name, module_aliases, member_aliases)
        if not canonical_names or "" in canonical_names:
            return False
        for canonical in canonical_names:
            try:
                loader_expr = ast.parse(canonical, mode="eval").body
            except (SyntaxError, ValueError, RecursionError):  # jwsgj:silent-ok 源码片段不可解析，按非安全 yaml 加载器返回 False
                return False
            if not is_safe_yaml_loader(loader_expr):
                return False
        return True
    @staticmethod
    def _shell_true_issues(node: ast.Call, filepath: str,
                           call_name: str) -> list[dict[str, Any]]:
        head, _, tail = call_name.rpartition(".")
        if head != "subprocess" or tail not in IncrementalGuard._SUBPROCESS_FUNCS:
            return []
        shell_value = next(
            (kw.value for kw in node.keywords if kw.arg == "shell"), None)
        if (shell_value is None
                and tail not in {"getoutput", "getstatusoutput"}
                and len(node.args) > 8
                and not any(isinstance(arg, ast.Starred) for arg in node.args[:9])):
            shell_value = node.args[8]
        if isinstance(shell_value, ast.Constant) and shell_value.value:
            return [_issue(
                filepath, "INC-SEC-03", "critical",
                f"shell=True 命令注入风险 (line {node.lineno})", node.lineno)]
        return []
    def _check_complexity(self, tree: ast.AST, filepath: str) -> list[dict[str, Any]]:
        issues: list[dict[str, Any]] = []
        for node in walk_nodes(tree):
            if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                continue
            end_line = getattr(node, "end_lineno", node.lineno)
            func_lines = end_line - node.lineno + 1
            if func_lines > IncrementalGuard.MAX_FUNC_LINES:
                issues.append(_issue(
                    filepath, "INC-CMPX-01", "high",
                    f"函数 '{node.name}' {func_lines} 行超过限制 "
                    f"{IncrementalGuard.MAX_FUNC_LINES}",
                    node.lineno))
            nesting = calc_nesting(node)
            if nesting > IncrementalGuard.MAX_NESTING:
                issues.append(_issue(
                    filepath, "INC-CMPX-02", "medium",
                    f"函数 '{node.name}' 嵌套深度 {nesting} 超过限制 "
                    f"{IncrementalGuard.MAX_NESTING}",
                    node.lineno))
        return issues
def _save_snapshot_tolerant(snapshot: dict[str, str], snapshot_dir: str) -> None:
    try:
        save_hash_snapshot(snapshot, snapshot_dir)
    except Exception as e:  # noqa: BLE001 — 快照落盘失败不得吞掉审查结果
        logger.warning("[Incremental] 哈希快照保存失败（本次结果不受影响）: %s", e)
def _decode_changed_paths(changed_files) -> list[str]:
    _dirty: list[Any] = []
    paths: list[str] = []
    for f in changed_files:
        try:
            paths.append(os.fsdecode(f))
        except TypeError as exc:
            log_swallowed(__name__, exc,
                          context="_decode_changed_paths:TypeError")
            _dirty.append(f)
    if _dirty:
        logger.warning(
            "[Incremental] 过滤 %d 个非 str 变更文件元素: %s",
            len(_dirty), [type(f).__name__ for f in _dirty])
    return paths
def _dedupe_absolute_paths(paths: list[str], project_root: str) -> list[str]:
    normalized: list[str] = []
    seen: set[str] = set()
    blank_count = 0
    duplicate_count = 0
    for f in paths:
        if not f.strip():
            blank_count += 1
            continue
        path = f if os.path.isabs(f) else os.path.join(project_root, f)
        path = os.path.normpath(path)
        key = os.path.normcase(path)
        if key in seen:
            duplicate_count += 1
            continue
        seen.add(key)
        normalized.append(path)
    if blank_count:
        logger.warning("[Incremental] 过滤 %d 个空白变更文件元素", blank_count)
    if duplicate_count:
        logger.warning("[Incremental] 去重 %d 个重复变更文件元素", duplicate_count)
    return normalized
def _normalize_changed_files_input(
        changed_files: list[str] | str | bytes | os.PathLike,
        project_root: str) -> list[str]:
    if (isinstance(changed_files, (str, bytes, os.PathLike, Mapping))
            or not isinstance(changed_files, Iterable)):
        changed_files = [changed_files]
    return _dedupe_absolute_paths(
        _decode_changed_paths(changed_files), project_root)
def _missing_project_rels(
        project_root: str, changed_files: Iterable[str]) -> set[str]:
    missing: set[str] = set()
    for path in changed_files:
        if os.path.isfile(path):
            continue
        try:
            rel = os.path.relpath(path, project_root).replace("\\", "/")
        except ValueError:
            continue
        if rel == ".." or rel.startswith("../") or os.path.isabs(rel):
            continue
        missing.add(rel)
    return missing
def _snapshot_detected_changes(
        project_root: str, snapshot_dir: str, *,
        enable_impact_analysis: bool = _DEFAULT_ENABLE_IMPACT_ANALYSIS,
) -> tuple[IncrementalContext, list[str], bool]:
    ctx = compute_incremental_scope(
        project_root, snapshot_dir,
        enable_impact_analysis=enable_impact_analysis)
    if ctx.mode == "incremental":
        return ctx, ctx.affected_files or ctx.changed_files, True
    if ctx.mode == "full":
        return ctx, _absolute_scope(project_root, ctx.affected_files), True
    return ctx, [], False
def _absolute_scope(project_root: str, rels: Iterable[str]) -> list[str]:
    scope: list[str] = []
    for rel in rels:
        path = rel if os.path.isabs(rel) else os.path.join(project_root, rel)
        path = os.path.normpath(path)
        if os.path.isfile(path):
            scope.append(path)
    return scope
def _resolve_review_scope(
    project_root: str,
    changed_files: list[str],
    snapshot_dir: str,
    explicit_input: bool,
    *,
    enable_impact_analysis: bool = _DEFAULT_ENABLE_IMPACT_ANALYSIS,
) -> tuple[IncrementalContext | None, list[str], bool]:
    if snapshot_dir and not explicit_input:
        return _snapshot_detected_changes(
            project_root, snapshot_dir,
            enable_impact_analysis=enable_impact_analysis)
    if not explicit_input:
        return None, detect_changed_py_files(project_root), False
    return None, changed_files, False
def _refresh_snapshot_baseline(
        ctx: IncrementalContext | None,
        refresh: bool,
        snapshot_dir: str,
        result: IncrementalGuardResult | None = None,
) -> None:
    if not refresh or ctx is None:
        return
    retry_rules = sorted({
        issue.get("rule_id") for issue in (result.issues if result else [])
        if issue.get("rule_id") in _SNAPSHOT_RETRY_RULES
    })
    if retry_rules:
        logger.warning(
            "[Incremental] 本轮存在可重试扫描故障 %s，保留旧快照以下轮复核",
            ", ".join(retry_rules))
        return
    _save_snapshot_tolerant(ctx.hash_snapshot, snapshot_dir)
def _empty_review_response(ctx: IncrementalContext | None,
                          refresh: bool,
                          snapshot_dir: str) -> dict[str, Any]:
    _refresh_snapshot_baseline(ctx, refresh, snapshot_dir)
    changed_files = (
        list(ctx.changed_files) + list(ctx.deleted_files)
        if ctx is not None else [])
    deleted_files = list(ctx.deleted_files) if ctx is not None else []
    change_count = ctx.change_count if ctx is not None else 0
    response = _review_response(
        IncrementalGuardResult(), change_count, len(deleted_files),
        changed_files, deleted_files)
    response["message"] = (
        "增量审查完成: 0 文件, 无变更" if not change_count else
        f"增量审查完成: 0 文件, {change_count} 项变更无需复核")
    return response
def _review_response(result: IncrementalGuardResult,
                     changed_count: int, deleted_count: int,
                     changed_files: list[str],
                     deleted_files: list[str]) -> dict[str, Any]:
    data = result.to_dict()
    data["changed_files_count"] = changed_count
    data["analyzed_files_count"] = len(result.impact_analyses)
    data["changed_files"] = list(changed_files)
    data["deleted_files"] = list(deleted_files)
    data["deleted_files_count"] = deleted_count
    return {
        "status": "ok",
        "data": data,
        "message": (
            f"增量审查完成: {len(result.impact_analyses)} 文件, "
            f"{result.total_issues} 问题 ({result.critical_issues} critical), "
            f"回归风险={result.regression_risk_score}"
        ),
    }
def _porcelain_paths(stdout: str, repo_root: str) -> list[str]:
    changed: list[str] = []
    fields = stdout.split("\0")
    index = 0
    while index < len(fields):
        entry = fields[index]
        index += 1
        if len(entry) < 4:
            continue
        status = entry[:2]
        rename_source = ""
        if "R" in status or "C" in status:
            source = fields[index] if index < len(fields) else ""
            index += 1
            if "R" in status and source.lower().endswith(".py"):
                rename_source = os.path.normpath(os.path.join(repo_root, source))
        part = entry[3:]
        if part.lower().endswith(".py"):
            changed.append(os.path.normpath(os.path.join(repo_root, part)))
        if rename_source:
            changed.append(rename_source)
    return changed
def detect_changed_py_files(project_root: str) -> list[str]:
    changed: list[str] = []
    git_exe = shutil.which("git")
    if git_exe is None:
        logger.warning("git 不在 PATH，变更检测不可用，回退全项目 Python 复核")
        return scan_py_files(project_root)
    try:
        top = subprocess.run(  # jwsgj:suppress SYM-TAINT — 审计认可：git 固定子命令，project_root 仅作 -C 目录参数，无 shell 拼接
            [git_exe, "-C", project_root, "rev-parse", "--show-toplevel"],
            check=False, capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=10,
        )
        repo_root = top.stdout.strip() if top.returncode == 0 else ""
        if (not repo_root or len(repo_root.splitlines()) != 1
                or not os.path.isdir(repo_root)):
            repo_root = os.path.abspath(project_root)
        out = subprocess.run(  # jwsgj:suppress SYM-TAINT — 审计认可：git 固定子命令，project_root 仅作 -C 目录参数，无 shell 拼接
            [git_exe, "-C", project_root, "status", "--porcelain", "-z",
             "--untracked-files=all", "--", "."],
            check=False, capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=10,
        )
        if out.returncode != 0:
            logger.warning("git status 执行失败（rc=%s），回退全项目 Python 复核",
                           out.returncode)
            return scan_py_files(project_root)
        if out.stdout.strip():
            changed = _porcelain_paths(out.stdout, repo_root)
    except Exception as exc:  # noqa: BLE001 — Git/路径故障均回退全量，避免漏审
        logger.warning("git 变更检测执行失败，回退全项目 Python 复核: %s", exc)
        return scan_py_files(project_root)
    return changed
def analyze_changed_files(
        project_root: str = DEFAULT_PROJECT_ROOT,
        changed_files: (list[str] | str | bytes | os.PathLike | None) = None,
        enable_impact_analysis: bool = _DEFAULT_ENABLE_IMPACT_ANALYSIS,
        snapshot_dir: str = "") -> dict[str, Any]:
    project_root = _validated_project_root(project_root)
    _warm_shared_cache_tolerant(project_root)
    _explicit_input = changed_files is not None
    if _explicit_input:
        changed_files = _normalize_changed_files_input(changed_files, project_root)
    ctx, changed_files, refresh_baseline = _resolve_review_scope(
        project_root, changed_files, snapshot_dir, _explicit_input,
        enable_impact_analysis=enable_impact_analysis)
    if not changed_files:
        return _empty_review_response(ctx, refresh_baseline, snapshot_dir)
    if enable_impact_analysis:
        if ctx is None:
            reusable_graph = build_dependency_graph(
                project_root,
                allow_missing=_missing_project_rels(project_root, changed_files),
            )
        else:
            reusable_graph = (
                ctx.dependency_graph if ctx.mode == "incremental" else None)
    else:
        reusable_graph = {}
    result = IncrementalGuard(
        project_root=project_root, dependency_graph=reusable_graph
    ).analyze_changes(
        changed_files=changed_files,
        enable_impact_analysis=enable_impact_analysis,
    )
    _refresh_snapshot_baseline(
        ctx, refresh_baseline, snapshot_dir, result)
    detected_deleted = (
        [path for path in changed_files if not os.path.isfile(path)]
        if ctx is None else []
    )
    changed_count = (ctx.change_count if ctx is not None
                     else len(changed_files))
    deleted_count = (len(ctx.deleted_files) if ctx is not None
                     else len(detected_deleted))
    reported_changes = (
        list(ctx.changed_files) + list(ctx.deleted_files)
        if ctx is not None else list(changed_files)
    )
    reported_deleted = (
        list(ctx.deleted_files) if ctx is not None else detected_deleted
    )
    return _review_response(
        result, changed_count, deleted_count, reported_changes, reported_deleted)
def _field(container: Any, key: str, default: Any) -> Any:
    if not isinstance(container, Mapping):
        return default
    value = container.get(key)
    return default if value is None else value
def _mapping_items(payload: Any, label: str) -> list[Mapping[str, Any]]:
    if payload is None:
        return []
    if isinstance(payload, (Mapping, str, bytes)):
        logger.warning("[Incremental] %s 载体非序列（降级空）: %s",
                       label, type(payload).__name__)
        return []
    if not isinstance(payload, Iterable):
        logger.warning("[Incremental] %s 载体不可迭代（降级空）: %s",
                       label, type(payload).__name__)
        return []
    raw = list(payload)
    items = [item for item in raw if isinstance(item, Mapping)]
    if len(items) != len(raw):
        logger.warning("[Incremental] %s 跳过 %d 个非映射条目",
                       label, len(raw) - len(items))
    return items
def _item_count(value: Any) -> int:
    if isinstance(value, (str, bytes, Mapping)) or not isinstance(value, Iterable):
        return 0
    return len(list(value))
def format_incremental_review(project_root: str, data: dict,
                              changed: list) -> str:
    lines = [
        f"项目根目录: {os.path.abspath(project_root)}",
        f"变更文件数: {_field(data, 'changed_files_count', len(changed))}",
        f"分析文件数: {_field(data, 'analyzed_files_count', 0)}",
        (f"问题总数: {_field(data, 'total_issues', 0)} "
         f"(critical: {_field(data, 'critical_issues', 0)})"),
        f"回归风险评分: {_field(data, 'regression_risk_score', 0.0)}",
    ]
    for issue in _mapping_items(_field(data, "issues", []), "issues"):
        lines.append(
            f"  [{_field(issue, 'severity', '?')}] {_field(issue, 'rule_id', '')} "
            f"{_field(issue, 'file', '')}: {_field(issue, 'message', '')}")
    for ia in _mapping_items(_field(data, "impact_analyses", []),
                             "impact_analyses"):
        hot = " [热路径]" if ia.get("hot_path") else ""
        total_modules = _field(
            ia, 'affected_modules_total',
            _item_count(_field(ia, 'affected_modules', [])))
        lines.append(
            f"  影响: {_field(ia, 'file', '')} "
            f"风险={_field(ia, 'risk_level', 'low')}{hot} "
            f"导入者={total_modules}")
    return "\n".join(lines)
def _validated_explicit_files(project_root: str,
                             explicit: list | None) -> list | None:
    if not explicit:
        return None
    invalid = []
    for raw in explicit:
        path = raw if os.path.isabs(raw) else os.path.join(project_root, raw)
        if os.path.isfile(path):
            continue
        deleted_py = str(raw).lower().endswith(".py") and not os.path.exists(path)
        try:
            rel = os.path.relpath(path, project_root).replace("\\", "/")
        except ValueError:
            rel = ".."
        inside = rel != ".." and not rel.startswith("../") and not os.path.isabs(rel)
        if deleted_py and inside:
            continue
        invalid.append(raw)
    if invalid:
        fail_cli(
            "incremental-review",
            "变更文件不存在: " + ", ".join(invalid[:5])
            + "（目录请单独传入，或用 -p/--project 指定项目根）", code=1)
    return list(explicit)
@cli_boundary("incremental-review", "增量审查命令失败")
def cmd_incremental_review(args: argparse.Namespace) -> None:
    _t0 = time.monotonic()
    project_root = getattr(args, "project", None)
    if project_root is None:
        project_root = DEFAULT_PROJECT_ROOT
    files = list(getattr(args, "files", None) or [])
    project_root, files = promote_single_dir(project_root, files)
    if not os.path.isdir(project_root):
        fail_cli("incremental-review", f"目录不存在: {project_root}", code=1)
    explicit = _validated_explicit_files(project_root, files or None)
    result = run_cli_action(
        "incremental-review", "增量审查执行异常", analyze_changed_files,
        project_root=project_root,
        changed_files=explicit,
        enable_impact_analysis=not getattr(args, "no_impact", False),
        snapshot_dir=default_snapshot_dir(project_root),
        code=2,
    )
    data = result.get("data") or {}
    display_changed = data.get("changed_files")
    if not isinstance(display_changed, list):
        display_changed = explicit or []
    print(format_incremental_review(project_root, data, display_changed))
    print(f"\n{result.get('message') or ''}")
    _emit_incremental_output(args, project_root, display_changed, data)
    changed_count = data.get("changed_files_count")
    if changed_count is None:
        changed_count = len(display_changed)
    trace_module_run(
        "__main__", "cmd_incremental_review", _t0, outcome="ok",
        changed_files=changed_count,
        total_issues=data.get("total_issues"),
        critical_issues=data.get("critical_issues"),
        regression_risk_score=data.get("regression_risk_score"),
    )
def _emit_incremental_output(args: argparse.Namespace, project_root: str,
                              changed: list, data: dict) -> None:
    reported_changes = data.get("changed_files")
    if not isinstance(reported_changes, list):
        reported_changes = changed
    payload = {
        "project_root": project_root, **data, "changed_files": reported_changes,
    }
    if getattr(args, "output", None):
        dump_json_report_checked(args.output, payload, "incremental-review")
    elif getattr(args, "json", False):
        print("\n" + json_text(payload))
def register_incremental_review(sub) -> None:
    p_inc = sub.add_parser(
        "incremental-review",
        help="增量代码审查（变更文件四步审查+回归风险评分）")
    p_inc.add_argument("-p", "--project", default=DEFAULT_PROJECT_ROOT,
                       help="项目根目录（默认当前目录）")
    p_inc.add_argument("files", nargs="*",
                       help="变更文件列表（省略时按增量快照检测；无快照时全量基线复核）")
    p_inc.add_argument("--no-impact", action="store_true",
                       help="关闭影响分析（跳过依赖图构建）")
    p_inc.add_argument("--json", action="store_true", help="输出 JSON 报告")
    p_inc.add_argument("-o", "--output", help="JSON 报告输出路径")
INCREMENTAL_REVIEW_COMMANDS = {
    "incremental-review": cmd_incremental_review,
}

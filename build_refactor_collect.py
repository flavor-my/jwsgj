from __future__ import annotations

import ast
import logging
import ntpath
import os
import posixpath
import re
import symtable
import sys
from collections import defaultdict, deque
from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass, field
from enum import Enum
from itertools import combinations
from pathlib import Path
from typing import Any, Self

from jwsgj.build_module_topology import (
    CollectionResult,
    ModuleReferenceCollector,
    collect_test_symbol_consumers,
    extract_module_state_names,
    iter_module_assigns,
)
from jwsgj.build_refactor_plan import (
    MergeEvidence,
    MigrationEvidence,
    compute_optimal_boundaries,
    find_merge_candidates,
    find_migrate_candidates,
    find_rewrite_candidates,
    find_split_candidates,
    infer_responsibility_domains,
    resolve_boundary_conflicts,
)
from jwsgj.build_refactor_policy import (
    BoundaryAnalysisResult,
    FileAnalysis,
    is_excluded_file,
    require_deep_analysis,
)
from jwsgj.diag_shared_ast_nodes import (
    classify_import_usage,
    collect_import_usage,
    extract_all_declarations,
    is_broad_except,
    is_package_init_path,
    is_static_method,
    iter_class_scope_methods,
    iter_module_level_stmts,
    iter_module_scope_entities,
    iter_module_stmt_blocks,
    iter_unpack_target_names,
    own_scope_line_span,
)
from jwsgj.diag_shared_source_core import (
    count_lines,
    parse_py_file,
    parse_py_source,
    read_py_source_with_error,
    read_source_with_fingerprint,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import iter_prod_py_files
from jwsgj.skill_profile import detect_layout

__all__ = [
    'FileMapping',
    'MappingReport',
    'MappingStatus',
    'ModuleBoundaryAnalyzer',
    'PreRefactoringMapper',
    'assign_value_key',
    'check_reexport_dependencies',
    'detect_cross_file_duplicates',
    'detect_dead_code',
    'detect_logic_issues',
    'detect_quality_issues',
    'detect_top_def_overflow',
    'detect_unused_imports',
    'quick_map',
]
_log = logging.getLogger(__name__)
_log.info("build_refactor_collect 已加载: %d 项导出", len(__all__))
class MappingStatus(str, Enum):
    RESOLVED = "resolved"
    ORPHAN = "orphan"
    CONFLICT = "conflict"
    SKIPPED = "skipped"
@dataclass
class FileMapping:
    source_path: str = ""
    target_path: str = ""
    source_size: int = 0
    is_empty_stub: bool = False
    status: MappingStatus = MappingStatus.ORPHAN
    notes: str = ""
    source_lines: int = 0
    def to_dict(self) -> dict[str, Any]:
        return {
            "source_path": self.source_path,
            "target_path": self.target_path,
            "source_size": self.source_size,
            "is_empty_stub": self.is_empty_stub,
            "status": self.status.value,
            "notes": self.notes,
            "source_lines": self.source_lines,
        }
@dataclass
class MappingReport:
    source_root: str = ""
    target_root: str = ""
    source_available: bool = True
    total_source_files: int = 0
    total_empty_stubs: int = 0
    mapped_files: int = 0
    orphan_files: list[FileMapping] = field(default_factory=list)
    conflict_files: list[FileMapping] = field(default_factory=list)
    all_mappings: list[FileMapping] = field(default_factory=list)
    def coverage_pct(self) -> float:
        if self.total_source_files == 0:
            return 0.0
        return round(self.mapped_files / self.total_source_files * 100, 1)
    def is_clean(self) -> bool:
        return (self.source_available
                and not self.orphan_files
                and not self.conflict_files)
    def summary(self) -> str:
        if not self.source_available:
            return f"源目录不存在，未执行映射: {self.source_root}"
        return (
            f"映射 {self.total_source_files} 个文件: "
            f"已映射 {self.mapped_files}, "
            f"孤儿 {len(self.orphan_files)}, "
            f"冲突 {len(self.conflict_files)}, "
            f"覆盖率 {self.coverage_pct()}%"
        )
    def to_dict(self) -> dict[str, Any]:
        return {
            "source_root": self.source_root,
            "target_root": self.target_root,
            "source_available": self.source_available,
            "total_source_files": self.total_source_files,
            "total_empty_stubs": self.total_empty_stubs,
            "mapped_files": self.mapped_files,
            "coverage_pct": self.coverage_pct(),
            "is_clean": self.is_clean(),
            "orphan_files": [m.to_dict() for m in self.orphan_files],
            "conflict_files": [m.to_dict() for m in self.conflict_files],
            "all_mappings": [m.to_dict() for m in self.all_mappings],
        }
def _normalize_exclude_patterns(exclude_patterns: object) -> list[str]:
    if exclude_patterns is None:
        return []
    if isinstance(exclude_patterns, str):
        _log.warning("[mapper] exclude_patterns 收到单个字符串，按单一模式处理: %r",
                     exclude_patterns)
        return [exclude_patterns] if exclude_patterns else []
    if not isinstance(exclude_patterns, Iterable):
        _log.warning("[mapper] exclude_patterns 非可迭代形状 %s，按无自定义模式处理",
                     type(exclude_patterns).__name__)
        return []
    return [pattern for pattern in exclude_patterns
            if isinstance(pattern, str) and pattern]
def _coerce_path_param(value: object) -> str | None:
    try:
        path = os.fspath(value)  # type: ignore[arg-type]
    except TypeError:
        return None
    return path if isinstance(path, str) and path.strip() else None
def _matches_exclude_pattern(path: str, basename: str,
                              pattern: str) -> bool:
    if pattern.endswith("/"):
        seg = pattern.strip("/")
        if not seg:
            return False
        return (path == seg or path.startswith(seg + "/")
                or path.endswith("/" + seg) or f"/{seg}/" in path)
    if '/' in pattern:
        candidate = path.strip('/')
        wanted = pattern.strip('/')
        if not wanted:
            return False
        return (candidate == wanted or candidate.startswith(wanted + '/')
                or candidate.endswith('/' + wanted)
                or f'/{wanted}/' in candidate)
    return basename == pattern or basename.startswith(pattern)
@dataclass
class _ScanTally:
    all_mappings: list[FileMapping] = field(default_factory=list)
    orphans: list[FileMapping] = field(default_factory=list)
    conflicts: list[FileMapping] = field(default_factory=list)
    total_files: int = 0
    empty_stubs: int = 0
    def add(self, mapping: FileMapping) -> None:
        self.total_files += 1
        self.empty_stubs += int(mapping.is_empty_stub)
        if mapping.status == MappingStatus.ORPHAN:
            self.orphans.append(mapping)
        elif mapping.status == MappingStatus.CONFLICT:
            self.conflicts.append(mapping)
        self.all_mappings.append(mapping)
    def mapped(self) -> int:
        return sum(1 for m in self.all_mappings
                   if m.status == MappingStatus.RESOLVED)
def _build_mapping_report(source_root: str, target_root: str,
                          scan: _ScanTally) -> MappingReport:
    report = MappingReport(
        source_root=source_root,
        target_root=target_root,
        total_source_files=scan.total_files,
        total_empty_stubs=scan.empty_stubs,
        mapped_files=scan.mapped(),
        orphan_files=scan.orphans,
        conflict_files=scan.conflicts,
        all_mappings=scan.all_mappings,
    )
    if not report.is_clean():
        _log.error(
            "[mapper] INCOMPLETE MAPPING: %d orphans, %d conflicts.",
            len(scan.orphans), len(scan.conflicts)
        )
    return report
_DEFAULT_EXCLUDE_PATTERNS = ('__pycache__/', '.git/', 'tests/', 'test_')
def _is_empty_stub_tree(tree: ast.Module) -> bool:
    for statement in tree.body:
        if isinstance(statement, ast.Pass):
            continue
        if (isinstance(statement, ast.Expr)
                and isinstance(statement.value, ast.Constant)
                and (isinstance(statement.value.value, str)
                     or statement.value.value is Ellipsis)):
            continue
        return False
    return True
def _mapping_source_evidence(fpath: str) -> tuple[int, bool, str]:
    source, error = read_py_source_with_error(fpath)
    if error is None and source is not None:
        source_lines = count_lines(source)
        tree, parse_error = parse_py_source(source)
        if tree is not None:
            return source_lines, _is_empty_stub_tree(tree), ""
        if parse_error is None:
            parse_error = SyntaxError("源码解析返回空 AST")
        return source_lines, False, f"stub_check_failed:{type(parse_error).__name__}"
    if error is None:
        error = UnicodeDecodeError(
            "utf-8", b"", 0, 1, "源码读取返回空文本")
    log_swallowed(
        __name__, error,
        context='_mapping_source_evidence:read')
    return 0, False, 'line_count_failed:' + type(error).__name__
class PreRefactoringMapper:
    def __init__(self, exclude_patterns: Iterable[str] | None = None) -> None:
        self._exclude_patterns: set[str] = set(_DEFAULT_EXCLUDE_PATTERNS)
        patterns = _normalize_exclude_patterns(exclude_patterns)
        self._exclude_patterns.update(patterns)
    def _process_file(self, fpath: str, source_root: str,
                      target_seen: dict[str, str],
                      rules: dict[str, str]) -> FileMapping:
        rel = os.path.relpath(fpath, source_root).replace('\\', '/')
        size = os.path.getsize(fpath)
        source_lines, is_stub, evidence_note = _mapping_source_evidence(fpath)
        def build_mapping(target_path: str, status: MappingStatus,
                          notes: str = "") -> FileMapping:
            return FileMapping(
                source_path=rel, target_path=target_path, source_size=size,
                is_empty_stub=is_stub, status=status,
                notes="; ".join(
                    part for part in (notes, evidence_note) if part),
                source_lines=source_lines)
        target_rel = _apply_rules(rel, rules)
        if target_rel is None:
            return build_mapping(
                "", MappingStatus.ORPHAN, "No mapping rule matched")
        target_rel = _normalize_target_path(target_rel)
        if target_rel is None:
            return build_mapping(
                "", MappingStatus.ORPHAN,
                "Mapping rule produced target outside target root")
        if target_rel in ("", "."):
            return build_mapping(
                "", MappingStatus.ORPHAN,
                "Mapping rule produced empty target")
        if is_stub:
            return build_mapping(target_rel, MappingStatus.SKIPPED)
        target_key = os.path.normcase(target_rel)
        if target_key in target_seen:
            return build_mapping(
                target_rel, MappingStatus.CONFLICT,
                f"Target already mapped from: {target_seen[target_key]}")
        target_seen[target_key] = rel
        return build_mapping(target_rel, MappingStatus.RESOLVED)
    def _iter_source_files(self, source_root: str) -> Iterator[str]:
        def _on_walk_error(err: OSError) -> None:
            _log.warning(
                "[mapper] 目录遍历失败，子树未纳入映射: %s (%s)",
                getattr(err, "filename", source_root), err)
        for root, dirs, files in os.walk(
                source_root, onerror=_on_walk_error):
            dirs[:] = sorted(
                d for d in dirs
                if not self._is_excluded(os.path.relpath(
                    os.path.join(root, d), source_root)))
            for filename in sorted(files):
                fpath = os.path.join(root, filename)
                relative_path = os.path.relpath(fpath, source_root)
                if self._is_candidate_file(relative_path):
                    yield fpath
    def _scan_directory(self, source_root: str,
                        rules: dict[str, str]) -> _ScanTally:
        scan = _ScanTally()
        target_seen: dict[str, str] = {}
        for fpath in self._iter_source_files(source_root):
            try:
                mapping = self._process_file(
                    fpath, source_root, target_seen, rules)
            except OSError as e:
                _log.warning(
                    "[mapper] 文件处理失败(可能已被并发删除),登记孤儿: %s (%s)",
                    fpath, e)
                rel = os.path.relpath(fpath, source_root).replace('\\', '/')
                mapping = FileMapping(
                    source_path=rel, status=MappingStatus.ORPHAN,
                    notes=f"processing_failed:{type(e).__name__}: {e}")
            scan.add(mapping)
        return scan
    def _is_candidate_file(self, fpath: str) -> bool:
        if not fpath.lower().endswith('.py'):
            return False
        return (os.path.basename(fpath).lower() != '__init__.py'
                and not self._is_excluded(fpath))
    def map_directory(
        self,
        source_root: str,
        target_root: str,
        layer_rules: dict[str, str] | None = None,
    ) -> MappingReport:
        effective_rules = _normalize_rules(layer_rules)
        source_path = _coerce_path_param(source_root)
        if source_path is None:
            _log.warning("[mapper] source_root 应为非空路径，收到 %r，返回空映射报告",
                         type(source_root).__name__)
            return MappingReport(
                source_root="" if source_root is None else str(source_root),
                target_root="" if target_root is None else str(target_root),
                source_available=False,
            )
        source_root = os.path.abspath(source_path)
        target_norm = _coerce_path_param(target_root)
        target_root = os.path.abspath(target_norm) if target_norm else ""
        if not os.path.isdir(source_root):
            _log.warning("[mapper] 源目录不存在，返回空映射报告: %s", source_root)
            return MappingReport(
                source_root=source_root,
                target_root=target_root,
                source_available=False,
            )
        scan = self._scan_directory(source_root, effective_rules)
        return _build_mapping_report(source_root, target_root, scan)
    def _is_excluded(self, path: str) -> bool:
        p = path.replace('\\', '/')
        basename = p.rsplit('/', 1)[-1]
        return any(_matches_exclude_pattern(p, basename, pattern)
                   for pattern in self._exclude_patterns)
def _segment_boundary_hit(src_prefix: str, rest: str) -> bool:
    return not (src_prefix and not src_prefix.endswith('/')
                and rest and not rest.startswith('/'))
def _join_target(tgt_prefix: str, suffix: str) -> str:
    base = tgt_prefix.rstrip('/')
    return base + '/' + suffix if base else suffix
def _normalize_target_path(target_rel: str) -> str | None:
    normalized = posixpath.normpath(target_rel.replace('\\', '/'))
    if (normalized.startswith(('/', '../'))
            or ntpath.splitdrive(normalized)[0] or normalized == '..'):
        return None
    return normalized
def _normalize_rules(rules: object) -> dict[str, str]:
    if rules is None:
        return {}
    if not isinstance(rules, dict):
        _log.warning("[mapper] layer_rules 非映射形态 %s，按无规则处理",
                     type(rules).__name__)
        return {}
    out: dict[str, str] = {}
    for src_prefix, tgt_prefix in rules.items():
        if isinstance(src_prefix, str) and isinstance(tgt_prefix, str):
            out[src_prefix] = tgt_prefix
        else:
            _log.warning("[mapper] 映射规则条目非法 %r -> %r，已跳过",
                         src_prefix, tgt_prefix)
    return out
def _apply_rules(source_rel: str,
                 rules: dict[str, str]) -> str | None:
    for src_prefix, tgt_prefix in sorted(rules.items(), key=lambda x: -len(x[0])):
        if not source_rel.startswith(src_prefix):
            continue
        rest = source_rel[len(src_prefix):]
        if not _segment_boundary_hit(src_prefix, rest):
            continue
        suffix = rest.lstrip('/')
        if not suffix:
            return tgt_prefix.rstrip('/')
        return _join_target(tgt_prefix, suffix)
    return None
def quick_map(source_root: str, target_root: str,
              rules: dict[str, str] | None = None) -> dict[str, Any]:
    mapper = PreRefactoringMapper()
    report = mapper.map_directory(source_root, target_root, rules)
    return report.to_dict()
_MAX_SCORE = 10.0
_COUPLING_SCALE = 3.0
_COHESION_SCALE = 5.0
_LOW_COHESION_SCORE = 2.0
_MIXED_RESPONSIBILITY_MIN = 2
def _cached_py_files(cache: Any) -> list[Path]:
    if cache is None:
        return []
    try:
        cached_files = list(cache.py_files or [])
    except Exception as e:  # noqa: BLE001
        _log.warning("SharedCache.py_files 读取失败，退化全库扫描: %s", e)
        return []
    files: list[Path] = []
    for entry in cached_files:
        path = os.fspath(entry) if isinstance(entry, os.PathLike) else entry
        if isinstance(path, str) and path and path.lower().endswith(".py"):
            files.append(Path(path))
            continue
        _log.warning("[Boundary] 缓存 py_files 含非路径元素，已剔除: %r", entry)
    return files
def _read_source(filepath: Path) -> str | None:
    source, _fingerprint = read_source_with_fingerprint(str(filepath))
    if source is None:
        _log.warning("[Boundary] 跳过无法读取的文件 %s", filepath)
    return source
def _parse_tree(source: str, fp_s: str) -> ast.AST | None:
    try:
        return ast.parse(source, filename=fp_s)
    except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
        _log.warning("[Boundary] 跳过无法解析的文件 %s: %s", fp_s, e)
        return None
def _relative_path(filepath: Path, skill_dir: Path) -> str | None:
    try:
        return str(filepath.relative_to(skill_dir))
    except ValueError:
        _log.warning("[Boundary] 跳过技能目录外文件 %s", filepath)
        return None
def _source_size(filepath: Path, source: str) -> int:
    try:
        return filepath.stat().st_size
    except OSError as e:
        _log.debug("stat 失败，降级内存字节长度: %s: %s", filepath, e)
        return len(source.encode("utf-8"))
def _shared_tree(cache: Any, fp_s: str) -> ast.AST | None:
    if cache is None:
        return None
    try:
        return cache.get_ast(fp_s)
    except Exception as e:  # noqa: BLE001
        _log.debug("缓存 AST 读取失败，回退源码解析: %s", e, exc_info=True)
        return None
def _cached_source_tree(
    cache: Any, fp_s: str,
) -> tuple[str | None, ast.AST | None]:
    if cache is None:
        return None, None
    try:
        get_snapshot = getattr(cache, "get_source_and_ast", None)
        if callable(get_snapshot):
            source, shared_tree = get_snapshot(fp_s)
        else:
            source = cache.get_source(fp_s)
            shared_tree = (
                _shared_tree(cache, fp_s) if source is not None else None)
    except Exception as e:  # noqa: BLE001
        _log.debug("SharedCache 源码/AST 读取失败，磁盘兜底: %s: %s", fp_s, e)
        return None, None
    if source is None:
        return None, None
    return source, shared_tree
def _ast_for(ast_cache: dict[str, ast.AST | None], fp_s: str, source: str,
             shared_tree: ast.AST | None) -> ast.AST | None:
    if fp_s in ast_cache:
        return ast_cache[fp_s]
    tree = shared_tree if shared_tree is not None else _parse_tree(source, fp_s)
    ast_cache[fp_s] = tree
    return tree
def _load_source_and_tree(
    filepath: Path, skill_dir: Path, cache: Any,
    source_cache: dict[str, str], ast_cache: dict[str, ast.AST | None],
) -> tuple[str, str, ast.AST, int] | None:
    rel_path = _relative_path(filepath, skill_dir)
    if rel_path is None:
        return None
    fp_s = str(filepath)
    source, shared_tree = _cached_source_tree(cache, fp_s)
    if source is None:
        source = _read_source(filepath)
        if source is None:
            return None
    tree = _ast_for(ast_cache, fp_s, source, shared_tree)
    if tree is None:
        return None
    source_cache[fp_s] = source
    return rel_path, source, tree, _source_size(filepath, source)
@dataclass
class _GraphViews:
    out: dict[str, set[str]] = field(default_factory=lambda: defaultdict(set))
    weighted: dict[str, dict[str, float]] = field(
        default_factory=lambda: defaultdict(dict))
    reverse: dict[str, set[str]] = field(default_factory=lambda: defaultdict(set))
    reverse_only: dict[str, set[str]] = field(
        default_factory=lambda: defaultdict(set))
    def clear(self: Self) -> None:
        self.out.clear()
        self.weighted.clear()
        self.reverse.clear()
        self.reverse_only.clear()
    def link(self: Self, src: str, tgt: str, *, import_only: bool = False) -> None:
        self.out[src].add(tgt)
        self.reverse[tgt].add(src)
        if import_only:
            self.reverse_only[tgt].add(src)
    def add_weight(self: Self, src: str, tgt: str, weight: float) -> None:
        self.weighted[src][tgt] = self.weighted[src].get(tgt, 0) + weight
def _chain_seed_graph(
    views: _GraphViews,
) -> dict[str, dict[str, float]]:
    threshold = ModuleBoundaryAnalyzer.WEIGHT_THRESHOLD
    undirected: dict[str, dict[str, float]] = defaultdict(dict)
    for src, targets in views.weighted.items():
        for tgt, weight in targets.items():
            if weight >= threshold:
                undirected[src][tgt] = max(
                    undirected[src].get(tgt, 0.0), weight)
                undirected[tgt][src] = max(
                    undirected[tgt].get(src, 0.0), weight)
    for src, targets in views.out.items():
        for tgt in targets:
            undirected.setdefault(src, {})
            undirected.setdefault(tgt, {})
    return undirected
def _collect_chain_members(
    start: str, undirected: dict[str, dict[str, float]],
) -> list[str]:
    threshold = ModuleBoundaryAnalyzer.WEIGHT_THRESHOLD
    queue = deque([start])
    visited: set[str] = set()
    chain_members: list[str] = []
    while queue:
        current = queue.popleft()
        if current in visited:
            continue
        visited.add(current)
        chain_members.append(current)
        for neighbor, weight in undirected[current].items():
            if neighbor not in visited and weight >= threshold:
                queue.append(neighbor)
    return chain_members
def _assign_orphan_chains(
    chains: dict[str, list[str]], chain_id: int,
    file_analyses: dict[str, FileAnalysis],
) -> int:
    for fpath, analysis in file_analyses.items():
        if analysis.execution_chain_id:
            continue
        chain_id += 1
        chain_key = f"chain_{chain_id}"
        chains[chain_key] = [fpath]
        analysis.execution_chain_id = chain_key
    return chain_id
def _strong_pair_weight(
    views: _GraphViews, fpath: str, members: list[str],
) -> tuple[float, bool]:
    threshold = ModuleBoundaryAnalyzer.WEIGHT_THRESHOLD
    total_weight = 0.0
    has_strong = False
    for member in members:
        if member == fpath:
            continue
        for src, tgt in ((fpath, member), (member, fpath)):
            weight = views.weighted.get(src, {}).get(tgt, 0)
            if weight >= threshold:
                total_weight += weight
                has_strong = True
    return total_weight, has_strong
def _cohesion_score(
    views: _GraphViews, fpath: str, chain_id: str,
    chains: dict[str, list[str]], weight_call: float,
) -> float:
    if not chain_id or chain_id not in chains:
        return 0.0
    members = chains[chain_id]
    n_others = len(members) - 1
    if n_others <= 0:
        return _MAX_SCORE
    total_weight, has_strong = _strong_pair_weight(views, fpath, members)
    if not has_strong:
        return _LOW_COHESION_SCORE
    return min(_MAX_SCORE,
               total_weight / n_others / weight_call * _COHESION_SCALE)
def _derive_responsibility(analysis: FileAnalysis) -> None:
    members = (*analysis.classes, *analysis.functions)
    non_empty = infer_responsibility_domains(members)
    analysis.has_mixed_responsibilities = (
        len(non_empty) >= _MIXED_RESPONSIBILITY_MIN)
    analysis.module_responsibility = ", ".join(sorted(non_empty)) or "unknown"
def _top_def_spans(tree: ast.AST) -> dict[str, tuple[int, int]]:
    spans: dict[str, tuple[int, int]] = {}
    for node in iter_module_scope_entities(tree):
        start, end = _definition_span(node)
        prev = spans.get(node.name)
        if prev is None or start < prev[0]:
            spans[node.name] = (start, end)
    return spans
class ModuleBoundaryAnalyzer:
    WEIGHT_FROM_IMPORT = 1.5
    WEIGHT_IMPORT = 1.0
    WEIGHT_THRESHOLD = 2.0
    def __init__(self: Self, skill_dir: str, cache=None) -> None:
        skill_dir_text = _coerce_path_param(skill_dir)
        if skill_dir_text is None:
            raise ValueError("skill_dir 必须是非空路径")
        self.skill_dir = Path(os.path.abspath(skill_dir_text))
        self._cache = cache
        self._collector = ModuleReferenceCollector(self.skill_dir)
        self._import_graph: dict[str, set[str]] = defaultdict(set)
        self._weighted_graph: dict[str, dict[str, float]] = defaultdict(dict)
        self._reverse_import_graph: dict[str, set[str]] = defaultdict(set)
        self._reverse_import_only_graph: dict[str, set[str]] = defaultdict(set)
        self._file_analyses: dict[str, FileAnalysis] = {}
        self._ast_cache: dict[str, ast.AST | None] = {}
        self._source_cache: dict[str, str] = {}
        self._deep_analyzed = False
    def _graph_views(self: Self) -> _GraphViews:
        return _GraphViews(
            out=self._import_graph,
            weighted=self._weighted_graph,
            reverse=self._reverse_import_graph,
            reverse_only=self._reverse_import_only_graph,
        )
    def deep_analyze(self: Self) -> None:
        self._deep_analyzed = False
        self._deep_analyze_all_files()
        check_reexport_dependencies(
            self._file_analyses, self.skill_dir, self._collector.import_index,
            symbol_consumers=self._collector.symbol_consumers)
        detect_dead_code(
            self._file_analyses, self._source_cache,
            self._ast_cache, self._collector.name_index,
            self._collector.import_index)
        detect_cross_file_duplicates(
            self._file_analyses, self._source_cache, self._ast_cache)
        self._deep_analyzed = True
    def analyze_boundaries(self: Self) -> BoundaryAnalysisResult:
        require_deep_analysis(self._deep_analyzed)
        self._build_import_graph()
        execution_chains = self._detect_execution_chains()
        self._analyze_module_responsibilities()
        result = BoundaryAnalysisResult(analysis_complete=True)
        result.execution_chains = execution_chains
        result.split_candidates = find_split_candidates(
            self._file_analyses, self._get_tree)
        result.merge_candidates = find_merge_candidates(
            execution_chains, self._file_analyses,
            MergeEvidence(
                weighted_graph=self._weighted_graph,
                reverse_import_graph=self._reverse_import_graph,
                reverse_import_only_graph=self._reverse_import_only_graph,
                weight_threshold=self.WEIGHT_THRESHOLD,
            ))
        result.migrate_candidates = find_migrate_candidates(
            self._file_analyses,
            MigrationEvidence(
                top_level_refs=self._collector.top_level_refs,
                module_level_refs=self._collector.module_level_refs,
                all_declarations=self._collector.all_declarations,
                module_state_names=self._collector.module_state_names,
                import_index=self._collector.import_index,
                test_symbol_consumers=collect_test_symbol_consumers(
                    self.skill_dir),
            ))
        result.rewrite_candidates = find_rewrite_candidates(
            self._file_analyses)
        result.boundaries = compute_optimal_boundaries(
            execution_chains, self._file_analyses)
        return resolve_boundary_conflicts(result, self._file_analyses)
    def _deep_analyze_all_files(self: Self) -> None:
        self._file_analyses = {}
        self._source_cache = {}
        self._ast_cache = {}
        self._collector = ModuleReferenceCollector(self.skill_dir)
        for fp in self._iter_py_files():
            self._analyze_single_file(fp)
    def _iter_py_files(self: Self) -> list[Path]:
        candidates = _cached_py_files(self._cache)
        if not candidates:
            candidates = [Path(fp) for fp in
                          iter_prod_py_files(str(self.skill_dir))]
        return [Path(os.path.abspath(str(fp))) for fp in candidates
                if not is_excluded_file(fp)]
    def _analyze_single_file(self: Self, filepath: Path) -> None:
        loaded = _load_source_and_tree(
            filepath, self.skill_dir, self._cache,
            self._source_cache, self._ast_cache)
        if loaded is None:
            return
        rel_path, source, tree, size_bytes = loaded
        collected = self._collector.collect_file(filepath, tree)
        self._file_analyses[str(filepath)] = FileAnalysis(
            filepath=str(filepath),
            relative_path=rel_path,
            size_bytes=size_bytes,
            line_count=count_lines(source),
            classes=collected.classes,
            functions=collected.functions,
            imports_out=collected.imports_out,
            call_references=collected.call_refs,
            from_import_entries=collected.from_import_entries,
            **self._detect_file_issues(filepath, tree, collected),
        )
    def _detect_file_issues(self, filepath: Path, tree: ast.AST,
                            collected: CollectionResult) -> dict[str, Any]:
        quality_issues = detect_quality_issues(tree, nodes=collected.nodes)
        quality_issues.extend(detect_top_def_overflow(collected.top_defs))
        unused_imports, reexport_bridges = detect_unused_imports(
            tree, str(filepath), nodes=collected.nodes)
        _spans = _top_def_spans(tree)
        _comp = _full_graph_labels(collected.top_defs)
        return {
            "unrelated_code_blocks": _unrelated_block_pairs(
                collected.top_defs, _comp),
            "substantial_unrelated_blocks": _unrelated_block_pairs(
                collected.top_defs, _comp, spans=_spans),
            "quality_issues": quality_issues,
            "logic_issues": detect_logic_issues(tree, nodes=collected.nodes),
            "unused_imports": unused_imports,
            "reexport_bridges": reexport_bridges,
        }
    def _get_tree(self: Self, fpath: str) -> ast.AST | None:
        if fpath in self._ast_cache:
            return self._ast_cache[fpath]
        shared_tree = _shared_tree(self._cache, fpath)
        source = self._source_cache.get(fpath)
        if shared_tree is None and source is None:
            return None
        return _ast_for(self._ast_cache, fpath, source or "", shared_tree)
    def get_shared_caches(self: Self) -> tuple[dict[str, str], dict[str, Any]]:
        return self._source_cache, self._ast_cache
    def get_import_indexes(
        self: Self,
    ) -> tuple[dict[str, dict[str, list[str]]], dict[str, list[tuple]]]:
        return self._collector.import_edges, self._collector.import_nodes
    def _build_import_graph(self: Self) -> None:
        views = self._graph_views()
        views.clear()
        for analysis in self._file_analyses.values():
            analysis.imports_in = []
        for fpath, analysis in self._file_analyses.items():
            total_import_weight = self._link_import_edges(
                fpath, analysis, views)
            self._register_call_edges(fpath, analysis, views)
            analysis.coupling_score = min(
                _MAX_SCORE, total_import_weight / _COUPLING_SCALE)
        for fpath, analysis in self._file_analyses.items():
            analysis.shared_base_consumers = len(
                self._reverse_import_only_graph.get(fpath, ()))
    def _link_import_edges(self: Self, fpath: str, analysis: FileAnalysis,
                           views: _GraphViews) -> float:
        pair_import_weight: dict[str, float] = {}
        for imp in analysis.imports_out:
            resolved = self._resolved_import_weight(analysis, imp)
            if resolved is None:
                continue
            target_file, weight = resolved
            views.link(fpath, target_file, import_only=True)
            target_analysis = self._file_analyses[target_file]
            if fpath not in target_analysis.imports_in:
                target_analysis.imports_in.append(fpath)
            pair_import_weight[target_file] = max(
                weight, pair_import_weight.get(target_file, 0.0))
        for target_file, weight in pair_import_weight.items():
            views.add_weight(fpath, target_file, weight)
        return sum(pair_import_weight.values())
    def _resolved_import_weight(self: Self, analysis: FileAnalysis,
                                imp: str) -> tuple[str, float] | None:
        target_file = self._collector.module_to_file(imp)
        if not target_file or target_file not in self._file_analyses:
            return None
        weight = (self.WEIGHT_FROM_IMPORT
                  if imp in analysis.from_import_entries
                  else self.WEIGHT_IMPORT)
        return target_file, weight
    def _register_call_edges(self: Self, fpath: str,
                             analysis: FileAnalysis, views: _GraphViews) -> None:
        for target_fp, call_weight in analysis.call_references.items():
            if target_fp not in self._file_analyses:
                continue
            views.link(fpath, target_fp)
            views.add_weight(fpath, target_fp, call_weight)
    def _detect_execution_chains(self: Self) -> dict[str, list[str]]:
        for analysis in self._file_analyses.values():
            analysis.execution_chain_id = ""
        undirected = _chain_seed_graph(self._graph_views())
        visited: set[str] = set()
        chains: dict[str, list[str]] = {}
        chain_id = 0
        for node in undirected:
            if node in visited:
                continue
            chain_id += 1
            chain_key = f"chain_{chain_id}"
            chain_members = _collect_chain_members(node, undirected)
            visited.update(chain_members)
            chains[chain_key] = chain_members
            self._bind_chain_id(chain_members, chain_key)
        chain_id = _assign_orphan_chains(
            chains, chain_id, self._file_analyses)
        self._calculate_cohesion_scores(chains)
        return chains
    def _bind_chain_id(self: Self, members: list[str], chain_key: str) -> None:
        for member in members:
            if member in self._file_analyses:
                self._file_analyses[member].execution_chain_id = chain_key
    def _calculate_cohesion_scores(self: Self, chains: dict[str, list[str]]) -> None:
        weight_call = self._collector.WEIGHT_CALL
        views = self._graph_views()
        for fpath, analysis in self._file_analyses.items():
            analysis.cohesion_score = _cohesion_score(
                views, fpath, analysis.execution_chain_id, chains,
                weight_call)
    def _analyze_module_responsibilities(self: Self) -> None:
        for analysis in self._file_analyses.values():
            _derive_responsibility(analysis)
    @property
    def file_analyses(self: Self) -> dict[str, FileAnalysis]:
        return dict(self._file_analyses)
_TOP_DEF_LIMIT = 30
_TOP_DEF_SCAN_LIMIT = 400
_SUBSTANTIAL_BLOCK_MIN_SHARE = 0.10
_SUBSTANTIAL_BLOCK_MIN_DEFS = 2
_MAX_FUNCTION_LINES = 80
_MAX_FUNCTION_PARAMS = 7
_MAX_CLASS_METHODS = 20
_MAX_MODULE_STATE_VARS = 30
_PAIRWISE_SHARED_REF_MIN = 3
_MIN_PAIRWISE_DEFS = 2
_MIN_FILES_FOR_CROSS_DEFINITION = 2
def assign_value_key(value_node: ast.expr) -> tuple[str, bool]:
    try:
        return ast.unparse(value_node), True
    except Exception as e:  # noqa: BLE001
        _log.warning("[Boundary] 赋值 RHS unparse 异常（该定义退出值判等）: %s",
                     e, exc_info=True)
        return "", False
def _pairwise_adjacency(
    scan_defs: list[tuple[str, set[str]]],
) -> list[set[int]]:
    n = len(scan_defs)
    adj: list[set[int]] = [set() for _ in range(n)]
    for i, j in combinations(range(n), 2):
        name_a, refs_a = scan_defs[i]
        name_b, refs_b = scan_defs[j]
        if (name_b in refs_a or name_a in refs_b
                or len(refs_a & refs_b) >= _PAIRWISE_SHARED_REF_MIN):
            adj[i].add(j)
            adj[j].add(i)
    return adj
def _label_component(adj: list[set[int]], start: int,
                     comp: list[int]) -> None:
    cid = comp[start]
    stack = [start]
    while stack:
        cur = stack.pop()
        for nxt in adj[cur]:
            if comp[nxt] != -1:
                continue
            comp[nxt] = cid
            stack.append(nxt)
def _component_labels(adj: list[set[int]]) -> list[int]:
    n = len(adj)
    comp = [-1] * n
    for start in range(n):
        if comp[start] != -1:
            continue
        comp[start] = start
        _label_component(adj, start, comp)
    return comp
def detect_top_def_overflow(
    top_defs: list[tuple[str, set[str]]],
) -> list[str]:
    if len(top_defs) > _TOP_DEF_LIMIT:
        return [f"文件有 {len(top_defs)} 个顶层定义，结构过于复杂"]
    return []
def _full_graph_labels(
    top_defs: list[tuple[str, set[str]]],
) -> list[int]:
    n = len(top_defs)
    if n <= _TOP_DEF_SCAN_LIMIT:
        return _component_labels(_pairwise_adjacency(top_defs))
    _log.warning(
        "顶层定义 %d 项超过全量连通分析上限 %d，退化为前段分析",
        n, _TOP_DEF_SCAN_LIMIT)
    return _component_labels(_pairwise_adjacency(top_defs[:_TOP_DEF_SCAN_LIMIT]))
def _unrelated_block_pairs(
    top_defs: list[tuple[str, set[str]]],
    comp: list[int],
    spans: dict[str, tuple[int, int]] | None = None,
) -> list[str]:
    scan_defs = top_defs[:_TOP_DEF_LIMIT]
    n = len(scan_defs)
    if n < _MIN_PAIRWISE_DEFS:
        return []
    keep = None
    if spans:
        keep = _substantial_labels(top_defs, comp, spans)
        if keep is None or len(keep) < 2:
            return []
    labels = comp[:n]
    return [
        f"{scan_defs[i][0]} ↔ {scan_defs[j][0]}"
        for i in range(n) for j in range(i + 1, n)
        if labels[i] != labels[j]
        and (keep is None or (labels[i] in keep and labels[j] in keep))
    ]
def _substantial_labels(
    top_defs: list[tuple[str, set[str]]],
    comp: list[int],
    spans: dict[str, tuple[int, int]],
) -> set[int] | None:
    lines: dict[int, int] = {}
    counts: dict[int, int] = {}
    total = 0
    for (name, _refs), label in zip(top_defs, comp, strict=False):
        span = spans.get(name)
        if span is None:
            continue
        size = max(0, span[1] - span[0] + 1)
        total += size
        lines[label] = lines.get(label, 0) + size
        counts[label] = counts.get(label, 0) + 1
    if not total:
        return None
    return {
        label for label, size in lines.items()
        if counts.get(label, 0) >= _SUBSTANTIAL_BLOCK_MIN_DEFS
        and size / total >= _SUBSTANTIAL_BLOCK_MIN_SHARE
    }
def _function_quality_issues(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
    *,
    is_method: bool = False,
) -> list[str]:
    issues: list[str] = []
    func_lines = own_scope_line_span(node)
    if func_lines > _MAX_FUNCTION_LINES:
        issues.append(f"超长函数 {node.name} ({func_lines} 行)")
    params = (list(node.args.posonlyargs) + list(node.args.args)
              + list(node.args.kwonlyargs))
    if is_method and params and params[0].arg in ("self", "cls"):
        params = params[1:]
    params.extend(
        arg for arg in (node.args.vararg, node.args.kwarg) if arg is not None)
    param_count = len(params)
    if param_count > _MAX_FUNCTION_PARAMS:
        issues.append(f"参数过多 {node.name} ({param_count} 个参数)")
    for default in node.args.defaults + node.args.kw_defaults:
        if isinstance(default, (ast.List, ast.Dict, ast.Set)):
            issues.append(f"可变默认参数 {node.name}")
            break
    return issues
def _is_noop_stmt(stmt: ast.stmt) -> bool:
    if isinstance(stmt, ast.Pass):
        return True
    return (isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Constant)
            and (stmt.value.value is Ellipsis
                 or isinstance(stmt.value.value, str)))
def _except_quality_issues(node: ast.ExceptHandler) -> list[str]:
    issues: list[str] = []
    if node.type is None:
        issues.append(f"bare except 无异常类型 (行 {node.lineno})")
    if (is_broad_except(node)
            and all(_is_noop_stmt(b) for b in node.body)):
        issues.append(f"静默异常 (行 {node.lineno})")
    return issues
def _import_quality_issues(node: ast.ImportFrom) -> list[str]:
    if any(a.name == "*" for a in node.names):
        module_disp = node.module or ("." * node.level)
        return [f"通配符导入 from {module_disp} import * (行 {node.lineno})"]
    return []
def _call_quality_issues(node: ast.Call) -> list[str]:
    func = node.func
    if isinstance(func, ast.Name) and func.id == "__import__":
        return [f"__import__() 反模式 (行 {node.lineno})"]
    return []
def _class_quality_issues(node: ast.ClassDef) -> list[str]:
    method_count = sum(1 for _ in iter_class_scope_methods(node))
    if method_count > _MAX_CLASS_METHODS:
        return [f"上帝类 {node.name} ({method_count} 个方法)"]
    return []
def _module_scope_quality_issues(tree: ast.AST) -> list[str]:
    issues: list[str] = []
    module_vars = len(extract_module_state_names(tree))
    if module_vars > _MAX_MODULE_STATE_VARS:
        issues.append(
            f"模块级变量过多 ({module_vars} 个，阈值 {_MAX_MODULE_STATE_VARS})")
    return issues
_QUALITY_RULE_FAMILIES: tuple[
    tuple[type | tuple[type, ...], Callable[[ast.AST], list[str]]], ...] = (
    (ast.ExceptHandler, _except_quality_issues),
    (ast.ImportFrom, _import_quality_issues),
    (ast.Call, _call_quality_issues),
    (ast.ClassDef, _class_quality_issues),
)
def _direct_method_ids(tree: ast.AST) -> set[int]:
    return {
        id(method)
        for cls in walk_nodes(tree) if isinstance(cls, ast.ClassDef)
        for method in iter_class_scope_methods(cls)
        if not is_static_method(method)
    }
def detect_quality_issues(tree: ast.AST,
                          nodes: list[ast.AST] | None = None) -> list[str]:
    issues: list[str] = []
    method_ids = _direct_method_ids(tree)
    for node in (nodes if nodes is not None else walk_nodes(tree)):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            issues.extend(_function_quality_issues(
                node, is_method=id(node) in method_ids))
            continue
        for node_types, rule in _QUALITY_RULE_FAMILIES:
            if isinstance(node, node_types):
                issues.extend(rule(node))
                break
    issues.extend(_module_scope_quality_issues(tree))
    return issues
def _walk_loop_scope(loop_node: ast.AST) -> Iterator[ast.AST]:
    orelse_ids = {id(stmt) for stmt in getattr(loop_node, "orelse", ())}
    stack = [
        child for child in ast.iter_child_nodes(loop_node)
        if id(child) not in orelse_ids
    ]
    while stack:
        cur = stack.pop()
        yield cur
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        stack.extend(ast.iter_child_nodes(cur))
def _own_scope_stmt_blocks(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> Iterator[list]:
    pending: list[list] = [list(getattr(node, "body", ()) or ())]
    while pending:
        block = pending.pop()
        if not block:
            continue
        yield block
        for stmt in block:
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef, ast.Lambda)):
                continue
            pending.extend(iter_module_stmt_blocks(stmt))
def _unreachable_after_flow_end(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> str | None:
    for block in _own_scope_stmt_blocks(node):
        last = len(block) - 1
        for i, stmt in enumerate(block):
            terminator: str | None = None
            if isinstance(stmt, ast.Return):
                terminator = "return"
            elif isinstance(stmt, ast.Raise):
                terminator = "raise"
            elif isinstance(stmt, ast.Break):
                terminator = "break"
            elif isinstance(stmt, ast.Continue):
                terminator = "continue"
            if terminator and i < last:
                return f"不可达代码 {node.name} ({terminator} 后)"
    return None
def _is_string_concat_augassign(child: ast.AugAssign) -> bool:
    val = child.value
    return (
        (isinstance(val, ast.Constant) and isinstance(val.value, str))
        or isinstance(val, ast.JoinedStr)
        or (isinstance(val, ast.Call)
            and isinstance(val.func, ast.Name)
            and val.func.id == "str")
    )
def _is_unseen_loop_import(node: ast.AST, seen_lines: set[int]) -> bool:
    return (isinstance(node, (ast.Import, ast.ImportFrom))
            and node.lineno not in seen_lines)
def _is_unseen_loop_concat(node: ast.AST, seen_lines: set[int]) -> bool:
    return (isinstance(node, ast.AugAssign)
            and isinstance(node.op, ast.Add)
            and isinstance(node.target, ast.Name)
            and node.lineno not in seen_lines
            and _is_string_concat_augassign(node))
def _loop_scope_issues(
    loop_node: ast.AST,
    seen_import_lines: set[int],
    seen_concat_lines: set[int],
) -> list[str]:
    issues: list[str] = []
    for child in _walk_loop_scope(loop_node):
        if _is_unseen_loop_import(child, seen_import_lines):
            seen_import_lines.add(child.lineno)
            issues.append(f"循环内导入 (行 {child.lineno})")
        elif _is_unseen_loop_concat(child, seen_concat_lines):
            seen_concat_lines.add(child.lineno)
            issues.append(f"循环内字符串拼接 (行 {child.lineno})")
    return issues
def _detect_fn_loop_issues(nodes: Iterable[ast.AST]) -> list[str]:
    issues: list[str] = []
    seen_loop_import_lines: set[int] = set()
    seen_loop_concat_lines: set[int] = set()
    for node in nodes:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            unreachable = _unreachable_after_flow_end(node)
            if unreachable:
                issues.append(unreachable)
        elif isinstance(node, (ast.For, ast.While, ast.AsyncFor)):
            issues.extend(_loop_scope_issues(
                node, seen_loop_import_lines, seen_loop_concat_lines))
    return issues
def _duplicate_assign_issue(
    var_name: str, defs: list[tuple[int, str, bool]],
) -> str:
    comparable_vals = {v for _, v, cmp_ok in defs if cmp_ok}
    if len(comparable_vals) > 1:
        return (f"重复变量定义值冲突 {var_name} "
                f"({_defs_display(defs, with_value=True)})")
    lines_str = _defs_display(defs, with_value=False)
    if all(cmp_ok for _, _, cmp_ok in defs):
        return f"重复变量定义 {var_name} (行 {lines_str}, 值相同)"
    return f"重复变量定义 {var_name} (行 {lines_str}, 值不可比较)"
def _defs_display(defs: list[tuple[int, str, bool]], *,
                  with_value: bool) -> str:
    if not with_value:
        return ", ".join(f"L{ln}" for ln, _v, _c in defs)
    return ", ".join(
        f"L{ln}={v[:60]}" if cmp_ok else f"L{ln}=?"
        for ln, v, cmp_ok in defs)
_TRY_STAR_NODES = tuple(
    node_type for node_type in (getattr(ast, "TryStar", None),)
    if node_type is not None)
_BranchPath = tuple[tuple[int, int], ...]
_ModuleAssignDef = tuple[int, str, bool, _BranchPath]
def _module_branch_paths(tree: ast.AST) -> dict[int, _BranchPath]:
    paths: dict[int, _BranchPath] = {}
    def visit_block(stmts: Iterable[ast.AST], path: _BranchPath) -> None:
        for stmt in stmts:
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.Lambda, ast.ClassDef)):
                continue
            if isinstance(stmt, (ast.Assign, ast.AnnAssign)):
                paths[stmt.lineno] = path
            if isinstance(stmt, ast.If):
                visit_block(stmt.body, path + ((id(stmt), 0),))
                visit_block(stmt.orelse, path + ((id(stmt), 1),))
                continue
            if isinstance(stmt, ast.Match):
                for index, case in enumerate(stmt.cases):
                    visit_block(case.body, path + ((id(stmt), index),))
                continue
            if isinstance(stmt, ast.Try):
                # 普通 try 的不同 handler 互斥；try 体与 handler、finally 与
                # 各分支仍可能连续执行。
                # try-else 仅在未进入任何 handler 时执行，故与全部 handler
                # 互斥，使用独立分支标记（下标取 len(handlers) 不与 handler
                # 下标冲突），否则 except/else 两处赋值会被误报为重复定义。
                visit_block(stmt.body, path)
                for index, handler in enumerate(stmt.handlers):
                    visit_block(
                        handler.body, path + ((id(stmt), index),))
                visit_block(
                    stmt.orelse, path + ((id(stmt), len(stmt.handlers)),))
                visit_block(stmt.finalbody, path)
                continue
            if isinstance(stmt, _TRY_STAR_NODES):
                # except* 的多个 handler 可以分别处理同一异常组中的不同异常，
                # 彼此不互斥，共用下标 0；但 try-else 仅在 try 体未抛出时
                # 执行，与全部 handler 互斥（下标 1）。若不单列分支，
                # handler/else 两处赋值会落入通用块路径被误报为重复定义。
                visit_block(stmt.body, path)
                for handler in stmt.handlers:
                    visit_block(handler.body, path + ((id(stmt), 0),))
                visit_block(stmt.orelse, path + ((id(stmt), 1),))
                visit_block(stmt.finalbody, path)
                continue
            for block in iter_module_stmt_blocks(stmt):
                visit_block(block, path)
    visit_block(getattr(tree, "body", ()), ())
    return paths
def _branch_paths_exclusive(left: _BranchPath, right: _BranchPath) -> bool:
    left_choices = dict(left)
    return any(
        node_id in left_choices and left_choices[node_id] != branch
        for node_id, branch in right
    )
def _nonexclusive_assign_components(
    defs: list[_ModuleAssignDef],
) -> list[list[tuple[int, str, bool]]]:
    adjacency: list[set[int]] = [set() for _ in defs]
    for left, right in combinations(range(len(defs)), 2):
        if _branch_paths_exclusive(defs[left][3], defs[right][3]):
            continue
        adjacency[left].add(right)
        adjacency[right].add(left)
    labels = _component_labels(adjacency)
    grouped: dict[int, list[tuple[int, str, bool]]] = defaultdict(list)
    for definition, label in zip(defs, labels, strict=True):
        grouped[label].append(definition[:3])
    return [component for component in grouped.values() if len(component) > 1]
def _classify_duplicate_assigns(
    module_assigns: Mapping[str, list[_ModuleAssignDef]],
) -> list[str]:
    return [
        _duplicate_assign_issue(var_name, component)
        for var_name, defs in module_assigns.items() if len(defs) > 1
        for component in _nonexclusive_assign_components(defs)
    ]
def _detect_module_duplicate_assigns(tree: ast.AST) -> list[str]:
    module_assigns: dict[str, list[_ModuleAssignDef]] = defaultdict(list)
    branch_paths = _module_branch_paths(tree)
    for name, lineno, _end, value in iter_module_assigns(tree):
        val_key, comparable = assign_value_key(value)
        module_assigns[name].append(
            (lineno, val_key, comparable, branch_paths.get(lineno, ())))
    return _classify_duplicate_assigns(module_assigns)
def detect_logic_issues(tree: ast.AST,
                        nodes: list[ast.AST] | None = None) -> list[str]:
    return _detect_fn_loop_issues(
        nodes if nodes is not None else walk_nodes(tree)
    ) + _detect_module_duplicate_assigns(tree)
def _is_exported_or_dunder(name: str, exported_names: set[str]) -> bool:
    return name.startswith("__") or name in exported_names
def detect_unused_imports(tree: ast.AST, filepath: str = "",
                          nodes: list[ast.AST] | None = None) -> tuple[list[str], list[str]]:
    if is_package_init_path(filepath):
        return [], []
    import_entries, used_names, exported_names = collect_import_usage(tree, nodes)
    unused: list[str] = []
    reexport: list[str] = []
    for name, line, desc in import_entries:
        unused_item, reexport_item = classify_import_usage(
            name, line, desc, used_names, exported_names)
        if unused_item is not None:
            unused.append(unused_item)
        if reexport_item is not None:
            reexport.append(reexport_item)
    return unused, reexport
def _iter_parsed_files(
    file_analyses: Mapping[str, FileAnalysis],
    source_cache: Mapping[str, str],
    ast_cache: Mapping[str, ast.AST | None],
) -> Iterator[tuple[str, FileAnalysis, str, ast.AST]]:
    for fpath_str, analysis in file_analyses.items():
        source = source_cache.get(fpath_str, "")
        if not source:
            continue
        tree = ast_cache.get(fpath_str)
        if tree is None:
            _log.warning("[Boundary] 深度分析时 AST 解析失败(语法错误)，此处跳过: %s", fpath_str)
            continue
        yield fpath_str, analysis, source, tree
def _line_set(ranges: Iterable[tuple[int, int]]) -> set[int]:
    return {ln for s, e in ranges for ln in range(s, e + 1)}
def _relative_module_name(path: Path, root: Path) -> str:
    try:
        rel = Path(os.path.abspath(str(path))).relative_to(
            Path(os.path.abspath(str(root))))
    except (OSError, ValueError):
        return path.stem
    return ".".join(rel.with_suffix("").parts)
def _relative_package_prefix(path: Path, root: Path) -> str:
    try:
        rel = Path(os.path.abspath(str(path))).relative_to(
            Path(os.path.abspath(str(root))))
    except (OSError, ValueError):
        return ""
    return ".".join(rel.parts)
def _strip_package_prefix(
    module: str, package_name: str, package_root_prefix: str,
) -> str:
    if package_name and module == package_name:
        return package_root_prefix
    if package_name and module.startswith(package_name + "."):
        suffix = module[len(package_name) + 1:]
        return ".".join(
            part for part in (package_root_prefix, suffix) if part)
    return module
def _import_base_module(
    node: ast.ImportFrom, package_prefix: str, package_name: str,
    package_root_prefix: str,
) -> str:
    if node.level <= 0:
        return _strip_package_prefix(
            node.module or "", package_name, package_root_prefix)
    parts = package_prefix.split(".") if package_prefix else []
    drop = node.level - 1
    if drop > 0:
        parts = parts[:max(0, len(parts) - drop)]
    base = ".".join(parts)
    if node.module:
        base = f"{base}.{node.module}" if base else node.module
    return base
def _init_import_bindings(
    init_tree: ast.AST, package_prefix: str, package_name: str,
    package_root_prefix: str,
) -> tuple[dict[str, set[str]], set[str]]:
    init_imports: dict[str, set[str]] = defaultdict(set)
    star_modules: set[str] = set()
    for node in iter_module_level_stmts(init_tree):
        if not isinstance(node, ast.ImportFrom):
            continue
        base = _import_base_module(
            node, package_prefix, package_name, package_root_prefix)
        for alias in node.names:
            if alias.name == "*":
                if base:
                    star_modules.add(base)
                continue
            if node.module:
                init_imports[base].add(alias.name)
    return init_imports, star_modules
@dataclass(frozen=True)
class _ReferenceIndex:
    module_occurrences: Mapping[str, frozenset[tuple[int, int]]]
    own_assignment_occurrences: Mapping[str, frozenset[tuple[int, int]]]
    scoped_references: tuple[tuple[int, int, frozenset[str]], ...]
    function_globals: Mapping[tuple[str, int], frozenset[str]]
    def occurrences(self, name: str) -> set[int]:
        lines = {
            line for line, _column in self.module_occurrences.get(name, ())}
        lines.update(
            start for start, _end, names in self.scoped_references
            if name in names
        )
        return lines
    def referenced_outside(
        self, name: str, exclude_ranges: Iterable[tuple[int, int]],
    ) -> bool:
        excluded = _line_set(exclude_ranges)
        own_occurrences = self.own_assignment_occurrences.get(name, ())
        if any((line, column) not in own_occurrences and line not in excluded
               for line, column in self.module_occurrences.get(name, ())):
            return True
        return any(
            name in names
            and any(line not in excluded for line in range(start, end + 1))
            for start, end, names in self.scoped_references
        )
def _nested_global_references(table: symtable.SymbolTable) -> set[str]:
    references: set[str] = set()
    pending = [table]
    while pending:
        current = pending.pop()
        references.update(
            symbol.get_name()
            for symbol in current.get_symbols()
            if symbol.is_global() and symbol.is_referenced()
        )
        pending.extend(current.get_children())
    return references
_AST_TYPE_ALIAS = getattr(ast, "TypeAlias", None)
_COMPREHENSION_NODE_TYPES = (
    ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp,
)
_AST_SCOPE_NODE_TYPES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
) + _COMPREHENSION_NODE_TYPES + (
    (_AST_TYPE_ALIAS,) if _AST_TYPE_ALIAS is not None else ())
def _ast_scope_key(node: ast.AST) -> tuple[str, str, int]:
    if _AST_TYPE_ALIAS is not None and isinstance(node, _AST_TYPE_ALIAS):
        return "type alias", node.name.id, node.lineno
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return "function", node.name, node.lineno
    if isinstance(node, ast.Lambda):
        return "function", "lambda", node.lineno
    if isinstance(node, ast.ClassDef):
        return "class", node.name, node.lineno
    for node_type, name in (
            (ast.ListComp, "listcomp"), (ast.SetComp, "setcomp"),
            (ast.DictComp, "dictcomp"), (ast.GeneratorExp, "genexpr")):
        if isinstance(node, node_type):
            return "function", name, node.lineno
    raise TypeError(f"非词法作用域节点: {type(node).__name__}")
def _outer_scope_expressions(node: ast.AST) -> Iterator[ast.AST]:
    if isinstance(node, _COMPREHENSION_NODE_TYPES):
        if node.generators:
            yield node.generators[0].iter
        return
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        yield from node.decorator_list if not isinstance(node, ast.Lambda) else ()
        args = node.args
        yield from args.defaults
        yield from (default for default in args.kw_defaults if default is not None)
        if getattr(node, "type_params", ()):
            return
        arguments = (*args.posonlyargs, *args.args, *args.kwonlyargs)
        for argument in (*arguments, args.vararg, args.kwarg):
            if argument is not None and argument.annotation is not None:
                yield argument.annotation
        if not isinstance(node, ast.Lambda) and node.returns is not None:
            yield node.returns
        return
    if isinstance(node, ast.ClassDef):
        yield from node.decorator_list
        if getattr(node, "type_params", ()):
            return
        yield from node.bases
        yield from (keyword.value for keyword in node.keywords)
def _outer_scope_global_refs(node: ast.AST) -> frozenset[str]:
    """收集定义期在外层作用域求值的全局名引用（注解/默认值/装饰器）。

    symtable 把函数注解与默认值的符号归入外层作用域而非函数子表，只看
    ``_nested_global_references`` 会漏掉这些引用：仅被死函数注解/默认值
    引用的常量既不算 DC-01 零引用死常量，也进不了 DC-03 级联候选。
    """
    return frozenset(
        sub.id
        for expression in _outer_scope_expressions(node)
        for sub in walk_nodes(expression)
        if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
    )
def _iter_direct_scope_nodes(tree: ast.AST) -> Iterator[ast.AST]:
    pending = deque(ast.iter_child_nodes(tree))
    while pending:
        node = pending.popleft()
        if isinstance(node, _COMPREHENSION_NODE_TYPES):
            yield node
            pending.extend(ast.iter_child_nodes(node))
            continue
        if isinstance(node, _AST_SCOPE_NODE_TYPES):
            yield node
            pending.extend(_outer_scope_expressions(node))
            continue
        pending.extend(ast.iter_child_nodes(node))
def _inlined_comprehension_local_load_ids(
    tree: ast.AST, inlined_scope_ids: set[int], matched_scope_ids: set[int],
) -> set[int]:
    local_load_ids: set[int] = set()
    def visit(node: ast.AST, bound: frozenset[str]) -> None:
        if id(node) in matched_scope_ids:
            for expression in _outer_scope_expressions(node):
                visit(expression, bound)
            return
        if id(node) in inlined_scope_ids:
            generators = node.generators
            visit(generators[0].iter, bound)
            inner = bound
            for index, generator in enumerate(generators):
                if index:
                    visit(generator.iter, inner)
                visit(generator.target, inner)
                inner = inner | frozenset(
                    iter_unpack_target_names(generator.target))
                for condition in generator.ifs:
                    visit(condition, inner)
            if isinstance(node, ast.DictComp):
                visit(node.key, inner)
                visit(node.value, inner)
            else:
                visit(node.elt, inner)
            return
        if (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
                and node.id in bound):
            local_load_ids.add(id(node))
        for child in ast.iter_child_nodes(node):
            visit(child, bound)
    visit(tree, frozenset())
    return local_load_ids
def _module_occurrences(
    tree: ast.AST, matched_scope_ids: set[int],
    inlined_scope_ids: set[int],
) -> dict[str, frozenset[tuple[int, int]]]:
    occurrences: dict[str, set[tuple[int, int]]] = defaultdict(set)
    local_load_ids = _inlined_comprehension_local_load_ids(
        tree, inlined_scope_ids, matched_scope_ids)
    pending = deque(ast.iter_child_nodes(tree))
    while pending:
        node = pending.popleft()
        if id(node) in matched_scope_ids:
            pending.extend(_outer_scope_expressions(node))
            continue
        if (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
                and id(node) not in local_load_ids):
            occurrences[node.id].add((node.lineno, node.col_offset))
        pending.extend(ast.iter_child_nodes(node))
    return {name: frozenset(positions) for name, positions in occurrences.items()}
def _own_assignment_occurrences(
    tree: ast.AST,
) -> dict[str, frozenset[tuple[int, int]]]:
    occurrences: dict[str, set[tuple[int, int]]] = defaultdict(set)
    for node in iter_module_level_stmts(tree):
        if isinstance(node, ast.Assign):
            assigned_names = set(iter_unpack_target_names(node.targets))
        elif (isinstance(node, ast.AnnAssign) and node.value is not None
              and isinstance(node.target, ast.Name)):
            assigned_names = {node.target.id}
        else:
            continue
        for name in assigned_names:
            occurrences[name].update(
                (reference.lineno, reference.col_offset)
                for reference in walk_nodes(node)
                if isinstance(reference, ast.Name)
                and isinstance(reference.ctx, ast.Load)
                and reference.id == name
            )
    return {name: frozenset(positions) for name, positions in occurrences.items()}
def _build_reference_index(
    tree: ast.AST, source: str, filename: str,
) -> _ReferenceIndex:
    module_table = symtable.symtable(source, filename, "exec")
    nodes_by_key: dict[tuple[str, str, int], deque[ast.AST]] = defaultdict(deque)
    for node in _iter_direct_scope_nodes(tree):
        nodes_by_key[_ast_scope_key(node)].append(node)
    matched_scope_ids: set[int] = set()
    scoped_references: list[tuple[int, int, frozenset[str]]] = []
    function_globals: dict[tuple[str, int], frozenset[str]] = {}
    for child in module_table.get_children():
        key = child.get_type(), child.get_name(), child.get_lineno()
        candidates = nodes_by_key.get(key)
        if not candidates and child.get_type() == "type parameter":
            for scope_type in ("class", "function", "type alias"):
                fallback_key = scope_type, child.get_name(), child.get_lineno()
                candidates = nodes_by_key.get(fallback_key)
                if candidates:
                    break
        if not candidates:
            raise ValueError(f"符号表作用域无法映射到 AST: {key}")
        node = candidates.popleft()
        matched_scope_ids.add(id(node))
        references = frozenset(_nested_global_references(child))
        start, end = _definition_span(node)
        scoped_references.append((start, end, references))
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            function_globals[(node.name, node.lineno)] = (
                references | _outer_scope_global_refs(node))
    parents = {
        id(child): parent
        for parent in walk_nodes(tree) for child in ast.iter_child_nodes(parent)}
    inlined_scope_ids: set[int] = set()
    for remaining in nodes_by_key.values():
        for node in remaining:
            ancestor = parents.get(id(node))
            while (ancestor is not None
                   and id(ancestor) not in matched_scope_ids):
                ancestor = parents.get(id(ancestor))
            if (ancestor is not None
                    and isinstance(ancestor, _COMPREHENSION_NODE_TYPES)):
                continue
            if isinstance(node, _COMPREHENSION_NODE_TYPES):
                inlined_scope_ids.add(id(node))
                continue
            raise ValueError(
                f"AST 作用域无法映射到符号表: {_ast_scope_key(node)}")
    return _ReferenceIndex(
        module_occurrences=_module_occurrences(
            tree, matched_scope_ids, inlined_scope_ids),
        own_assignment_occurrences=_own_assignment_occurrences(tree),
        scoped_references=tuple(scoped_references),
        function_globals=function_globals,
    )
@dataclass(frozen=True)
class _FileScanEvidence:
    exported_names: set[str]
    module_assign_ranges: dict[str, list[tuple[int, int]]]
    references: _ReferenceIndex
def _scan_evidence(
    tree: ast.AST, source: str, filename: str,
) -> _FileScanEvidence:
    return _FileScanEvidence(
        exported_names=extract_all_declarations(tree),
        module_assign_ranges=_module_assign_ranges(tree),
        references=_build_reference_index(tree, source, filename),
    )
@dataclass(frozen=True)
class _BridgeEvidence:
    module_name: str
    init_imported_names: set[str]
    star_modules: set[str]
    fpath: str
    import_index: Mapping[str, set[str]] | None
    symbol_consumers: Mapping[tuple[str, str], set[str]] | None = None
def _classify_bridges(
    analysis: FileAnalysis,
    evidence: _BridgeEvidence,
) -> None:
    confirmed_reexport: list[str] = []
    confirmed_unused: list[str] = []
    for bridge in analysis.reexport_bridges:
        match = re.search(r'import\s+([\w.]+)(?:\s+as\s+(\w+))?', bridge)
        if not match:
            confirmed_reexport.append(bridge)
            continue
        imported_name = match.group(2) or match.group(1).split(".")[0]
        reason = _bridge_confirmation(imported_name, evidence)
        if reason:
            confirmed_reexport.append(f"{bridge} → 确认重导出: {reason}")
        else:
            confirmed_unused.append(f"{bridge} → 确认未使用: __init__.py 未引用")
    analysis.reexport_bridges = confirmed_reexport
    analysis.unused_imports.extend(confirmed_unused)
def _bridge_confirmation(imported_name: str,
                         evidence: _BridgeEvidence) -> str:
    if ("*" in evidence.init_imported_names
            or imported_name in evidence.init_imported_names):
        return f"__init__.py 通过 {evidence.module_name} 引用"
    if evidence.module_name in evidence.star_modules:
        return f"__init__.py 星号转发 {evidence.module_name} 的 __all__"
    if (evidence.symbol_consumers is not None
            and _symbol_imported_elsewhere(
                imported_name, evidence.fpath, evidence.symbol_consumers)):
        return "外部模块直接 import 消费"
    if _imported_elsewhere(
            imported_name, evidence.fpath, evidence.import_index):
        return "外部模块直接 import 消费"
    return ""
def _symbol_imported_elsewhere(
    symbol: str,
    fpath_str: str,
    symbol_consumers: Mapping[tuple[str, str], set[str]],
) -> bool:
    consumers = symbol_consumers.get((fpath_str, symbol), set())
    return any(consumer != fpath_str for consumer in consumers)
def _load_init_bindings(
    init_path: Path, package_prefix: str, package_name: str,
    package_root_prefix: str,
) -> tuple[dict[str, set[str]], set[str], bool]:
    _init_source, init_tree = parse_py_file(str(init_path), quiet=True)
    if init_tree is None:
        _log.debug(
            "[Boundary] __init__.py 解析失败(编码/语法)，跳过该包的重导出确认: %s",
            init_path)
        return {}, set(), False
    init_imports, star_modules = _init_import_bindings(
        init_tree, package_prefix, package_name, package_root_prefix)
    return init_imports, star_modules, True
def _package_entry_dirs(fpath_path: Path, root: Path) -> list[Path]:
    root_abs = Path(os.path.abspath(root))
    current = Path(os.path.abspath(fpath_path.parent))
    if current != root_abs and root_abs not in current.parents:
        return list(dict.fromkeys((fpath_path.parent, root)))
    dirs: list[Path] = []
    while True:
        dirs.append(current)
        if current == root_abs:
            return dirs
        current = current.parent
def check_reexport_dependencies(
    file_analyses: Mapping[str, FileAnalysis], skill_dir: Path,
    import_index: Mapping[str, set[str]] | None = None,
    symbol_consumers: Mapping[tuple[str, str], set[str]] | None = None,
) -> None:
    root = Path(os.path.abspath(skill_dir))
    layout = detect_layout(str(root))
    package_name = layout.package_name if layout.is_package else root.name
    package_root_prefix = (
        _relative_package_prefix(Path(layout.package_root), root)
        if layout.is_package else ""
    )
    binding_cache: dict[
        str, tuple[dict[str, set[str]], set[str], bool]] = {}
    def _bindings_for(
        pkg_dir: Path,
    ) -> tuple[dict[str, set[str]], set[str], bool]:
        key = str(pkg_dir)
        if key not in binding_cache:
            init_path = pkg_dir / "__init__.py"
            binding_cache[key] = (
                _load_init_bindings(
                    init_path, _relative_package_prefix(pkg_dir, root),
                    package_name, package_root_prefix) if init_path.exists()
                else ({}, set(), True))
        return binding_cache[key]
    for fpath, analysis in file_analyses.items():
        if not analysis.reexport_bridges:
            continue
        fpath_path = Path(fpath)
        if not fpath_path.is_absolute():
            fpath_path = root / fpath_path
        pkg_dirs = _package_entry_dirs(fpath_path, root)
        if not any((d / "__init__.py").exists() for d in pkg_dirs):
            continue
        init_imports: dict[str, set[str]] = defaultdict(set)
        star_modules: set[str] = set()
        parsed_all = True
        for pkg_dir in pkg_dirs:
            pkg_imports, pkg_stars, parse_ok = _bindings_for(pkg_dir)
            parsed_all = parsed_all and parse_ok
            for mod_name, names in pkg_imports.items():
                init_imports[mod_name].update(names)
            star_modules.update(pkg_stars)
        if not parsed_all:
            continue
        module_name = _relative_module_name(fpath_path, root)
        _classify_bridges(
            analysis,
            _BridgeEvidence(
                module_name=module_name,
                init_imported_names=init_imports.get(module_name, set()),
                star_modules=star_modules,
                fpath=fpath,
                import_index=import_index,
                symbol_consumers=symbol_consumers,
            ))
def _imported_elsewhere(
    symbol: str,
    fpath_str: str,
    import_index: Mapping[str, set[str]] | None,
) -> bool:
    if import_index is None:
        return False
    return any(f != fpath_str for f in import_index.get(symbol, ()))
def _external_refs_exist(
    symbol: str,
    fpath_str: str,
    name_index: Mapping[str, list[str]],
    import_index: Mapping[str, set[str]] | None,
) -> bool:
    if any(f != fpath_str for f in name_index.get(symbol, [])):
        return True
    return _imported_elsewhere(symbol, fpath_str, import_index)
def _module_assign_ranges(tree: ast.AST) -> dict[str, list[tuple[int, int]]]:
    ranges: dict[str, list[tuple[int, int]]] = defaultdict(list)
    for name, start, end, _value in iter_module_assigns(tree):
        ranges[name].append((start, end))
    return ranges
def _scan_dead_constants(
    analysis: FileAnalysis,
    evidence: _FileScanEvidence,
    fpath_str: str,
    name_index: Mapping[str, list[str]],
    import_index: Mapping[str, set[str]] | None,
) -> None:
    for nm, ranges in evidence.module_assign_ranges.items():
        if not _is_dead_constant(
                nm, evidence, fpath_str, name_index, import_index):
            continue
        ranges_str = ", ".join(f"L{s}-{e}" for s, e in ranges)
        analysis.dead_constants.append(
            f"DC-01: {nm} ({ranges_str}, 零引用死常量)",
        )
def detect_dead_code(
    file_analyses: Mapping[str, FileAnalysis],
    source_cache: Mapping[str, str],
    ast_cache: Mapping[str, ast.AST | None],
    name_index: Mapping[str, list[str]],
    import_index: Mapping[str, set[str]] | None = None,
    *,
    scan_constants: bool = True,
    scan_cascade: bool = True,
) -> None:
    for analysis in file_analyses.values():
        if scan_constants:
            analysis.dead_constants.clear()
        if scan_cascade:
            analysis.cascade_dead_candidates.clear()
    for fpath_str, analysis, source, tree in _iter_parsed_files(
            file_analyses, source_cache, ast_cache):
        try:
            evidence = _scan_evidence(tree, source, fpath_str)
        except (SyntaxError, ValueError, RecursionError, MemoryError) as exc:
            _log.warning(
                "[Boundary] 引用索引构建失败，跳过死代码扫描: %s: %s",
                fpath_str, exc)
            continue
        if scan_constants:
            _scan_dead_constants(
                analysis, evidence, fpath_str, name_index, import_index)
        if scan_cascade:
            _scan_cascade_dead_code(
                analysis, evidence, tree, name_index, import_index)
def _is_dead_constant(name: str, evidence: _FileScanEvidence,
                      fpath_str: str, name_index: Mapping[str, list[str]],
                      import_index: Mapping[str, set[str]] | None) -> bool:
    if _is_exported_or_dunder(name, evidence.exported_names):
        return False
    if _external_refs_exist(name, fpath_str, name_index, import_index):
        return False
    return not evidence.references.referenced_outside(name, ())
def _resolve_dead_funcs(
    candidates: dict[str, tuple[int, int, set[str]]],
    references: _ReferenceIndex,
) -> dict[str, tuple[int, int, set[str]]]:
    if not candidates:
        return {}
    occurrence = {name: references.occurrences(name) for name in candidates}
    dead_names = set(candidates)
    while True:
        dead_line_nos = _line_set(
            candidates[name][:2] for name in dead_names)
        resurrected = {
            nm for nm in dead_names
            if not occurrence[nm] <= dead_line_nos
        }
        if not resurrected:
            return {nm: span for nm, span in candidates.items()
                    if nm in dead_names}
        dead_names -= resurrected
def _definition_span(node: ast.AST) -> tuple[int, int]:
    start = min(
        (d.lineno for d in getattr(node, "decorator_list", ())),
        default=node.lineno,
    )
    return start, getattr(node, "end_lineno", node.lineno)
def _dead_func_candidates(
    tree: ast.AST,
    exported_names: set[str],
    fpath_str: str,
    name_index: Mapping[str, list[str]],
    import_index: Mapping[str, set[str]] | None,
    global_refs_by_function: Mapping[tuple[str, int], frozenset[str]],
) -> dict[str, tuple[int, int, set[str]]]:
    candidates: dict[str, tuple[int, int, set[str]]] = {}
    for node in iter_module_scope_entities(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if node.decorator_list:
            continue
        name = node.name
        if not name.startswith("_") or _is_exported_or_dunder(
                name, exported_names):
            continue
        if _external_refs_exist(name, fpath_str, name_index, import_index):
            continue
        global_refs = global_refs_by_function.get((name, node.lineno))
        if global_refs is None:
            _log.warning(
                "[Boundary] 函数符号表缺失，跳过级联候选: %s:%s",
                fpath_str, name)
            continue
        candidates[name] = (*_definition_span(node), global_refs)
    return candidates
def _is_cascade_candidate(
    ref_name: str,
    module_assign_ranges: Mapping[str, list[tuple[int, int]]],
    exported_names: set[str],
    reported_cascade: set[str],
) -> bool:
    if ref_name in reported_cascade:
        return False
    if _is_exported_or_dunder(ref_name, exported_names):
        return False
    return ref_name in module_assign_ranges
def _scan_cascade_dead_code(
    analysis: FileAnalysis,
    evidence: _FileScanEvidence,
    tree: ast.AST,
    name_index: Mapping[str, list[str]],
    import_index: Mapping[str, set[str]] | None,
) -> None:
    fpath_str = analysis.filepath
    candidates = _dead_func_candidates(
        tree, evidence.exported_names, fpath_str, name_index, import_index,
        evidence.references.function_globals)
    dead_funcs = _resolve_dead_funcs(candidates, evidence.references)
    ctx = _CascadeScanContext(
        evidence=evidence,
        dead_ranges=[(s, e) for s, e, _ in dead_funcs.values()],
        fpath=fpath_str,
        name_index=name_index,
        import_index=import_index,
    )
    reported_cascade: set[str] = set()
    for func_name, (f_start, f_end, referenced) in dead_funcs.items():
        for ref_name in sorted(
                referenced,
                key=lambda name: _cascade_ref_order(
                    name, ctx.evidence.module_assign_ranges)):
            if not _is_cascade_death(ref_name, ctx, reported_cascade):
                continue
            reported_cascade.add(ref_name)
            analysis.cascade_dead_candidates.append(
                f"DC-03: {ref_name} (级联死亡: 死函数 {func_name} 的引用变量, "
                f"L{f_start}-{f_end})",
            )
@dataclass(frozen=True)
class _CascadeScanContext:
    evidence: _FileScanEvidence
    dead_ranges: list[tuple[int, int]]
    fpath: str
    name_index: Mapping[str, list[str]]
    import_index: Mapping[str, set[str]] | None
def _cascade_ref_order(
    ref_name: str,
    module_assign_ranges: Mapping[str, list[tuple[int, int]]],
) -> tuple[int, str]:
    spans = module_assign_ranges.get(ref_name)
    return (spans[0][0] if spans else sys.maxsize, ref_name)
def _is_cascade_death(ref_name: str, ctx: _CascadeScanContext,
                      reported: set[str]) -> bool:
    if not _is_cascade_candidate(
            ref_name, ctx.evidence.module_assign_ranges,
            ctx.evidence.exported_names, reported):
        return False
    if ctx.evidence.references.referenced_outside(
            ref_name, ctx.dead_ranges):
        return False
    return not _external_refs_exist(
        ref_name, ctx.fpath, ctx.name_index, ctx.import_index)
def _conflicting_declaration_values(
    defs: list[tuple[str, str, bool, int]],
) -> bool:
    return len({v for _, v, cmp_ok, _ in defs if cmp_ok}) > 1
def _format_independent_defs(
    defs: list[tuple[str, str, bool, int]],
) -> str:
    return ", ".join(
        f"{Path(fp).name}:L{ln}={v[:30]}" if cmp_ok
        else f"{Path(fp).name}:L{ln}=?"
        for fp, v, cmp_ok, ln in defs
    )
def _report_independent_defs(
    name: str,
    defs: list[tuple[str, str, bool, int]],
    file_analyses: Mapping[str, FileAnalysis],
) -> None:
    if not _conflicting_declaration_values(defs):
        return
    files_str = _format_independent_defs(defs)
    for fp in dict.fromkeys(f for f, _, _, _ in defs):
        analysis_ref = file_analyses.get(fp)
        if analysis_ref:
            analysis_ref.cross_file_duplicates.append(
                f"DC-04: {name} (同名独立定义: {files_str})",
            )
def detect_cross_file_duplicates(
    file_analyses: Mapping[str, FileAnalysis],
    source_cache: Mapping[str, str],
    ast_cache: Mapping[str, ast.AST | None],
) -> None:
    for analysis in file_analyses.values():
        analysis.cross_file_duplicates.clear()
    all_assigns: dict[str, list[tuple[str, str, bool, int]]] = defaultdict(list)
    for fpath_str, _analysis, _source, tree in _iter_parsed_files(
            file_analyses, source_cache, ast_cache):
        for nm, lineno, _end, value in iter_module_assigns(tree):
            val_key, comparable = assign_value_key(value)
            all_assigns[nm].append((fpath_str, val_key, comparable, lineno))
    for name, defs in all_assigns.items():
        if name.startswith("__"):
            continue
        if len({fp for fp, _, _, _ in defs}) < _MIN_FILES_FOR_CROSS_DEFINITION:
            continue
        _report_independent_defs(name, defs, file_analyses)

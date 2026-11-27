from __future__ import annotations

import ast
import hashlib
import importlib
import logging
import math
import os
import time
from collections import defaultdict
from collections.abc import Callable, Iterable, Iterator, Mapping, Sequence
from dataclasses import dataclass, field
from enum import Enum
from functools import partial
from typing import Any, NamedTuple, Self

from jwsgj.diag_antipattern import (
    default_param_sites,
    parse_tree,
    tally_shape_node,
)
from jwsgj.diag_detector_assembly import (
    AUDIT_DETECTOR_IDS,
    detect_all,
    detect_all_audit_patterns,
    detect_all_new_patterns,
    load_source_and_tree,
    registry_sec_family_ids,
)
from jwsgj.diag_detector_findings import (
    RETIRED_RULE_IDS,
    finding_file,
    normalize_severity,
    retired_registry_excludes,
    split_malformed_issues,
)
from jwsgj.diag_detector_findings import (
    build_issue_envelope as _issue_envelope,
)
from jwsgj.diag_detector_findings import (
    coerce_issue_line as _norm_issue_line,
)
from jwsgj.diag_detector_findings import (
    coerce_issue_text as _norm_issue_str,
)
from jwsgj.diag_detectors_registry import get_registry as _get_registry
from jwsgj.diag_merge_safety import (
    detect_all_new,
)
from jwsgj.diag_wiring_import_scan import (
    build_import_scan_context,
)
from jwsgj.log_config import (
    log_swallowed,
    write_module_run,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    detect_layout,
    is_diagnosis_out_of_scope,
    is_scan_excluded,
    is_scan_py_name,
    iter_scan_py_files,
    prune_scan_dirnames,
    scan_exclude_dirs,
    scan_prune_dirs,
)

__all__ = [
    'CrossSkillDetector',
    'DefaultParamDuplicationDetector',
    'DetectedSignal',
    'DuplicateCodeDetector',
    'SignalDetector',
    'SignalType',
    'collect_scope_filtered_findings',
    'collect_top_scan_files',
    'run_density_post_processor',
    'run_extended_detectors',
    'run_file_detectors',
]
logger = logging.getLogger(__name__)
logger.info(
    "diag_antipattern_flow_detect 已加载: %d 项导出（检测通道与结果归一）",
    len(__all__))
def _coerce_root_arg(value: Any) -> str | None:
    if isinstance(value, str):
        text = value.strip()
        return text or None
    if isinstance(value, os.PathLike):
        text = _text_or_fspath(value).strip()
        return text or None
    return None
def _text_or_fspath(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, os.PathLike):
        try:
            return os.fsdecode(value)
        except TypeError:
            return ""
    return ""
def _path_identity(value: Any) -> str:
    text = _text_or_fspath(value)
    if not text:
        return ""
    try:
        return os.path.normcase(os.path.abspath(text))
    except (OSError, ValueError, TypeError) as exc:
        logger.debug("[Antipattern] 路径归一失败，保留文本比较键 %r: %s",
                     value, exc)
        return os.path.normcase(text)
def _coerce_py_files(value: Any) -> list[str]:
    if value is None:
        return []
    _unordered = isinstance(value, (set, frozenset))
    if isinstance(value, (str, os.PathLike)):
        items: list[Any] = [value]
    elif (isinstance(value, Iterable)
          and not isinstance(value, (bytes, Mapping))):
        try:
            items = list(value)
        except TypeError:
            logger.debug("[Antipattern] 文件清单不可迭代: %r",
                         type(value).__name__)
            return []
    else:
        logger.debug("[Antipattern] 文件清单形态非法，按空清单处理: %r",
                     type(value).__name__)
        return []
    files: list[str] = []
    seen: set[str] = set()
    for item in items:
        if not isinstance(item, (str, os.PathLike)):
            logger.debug("[Antipattern] 跳过非路径文件项: %r", item)
            continue
        path = _text_or_fspath(item).strip()
        if not path:
            continue
        key = _path_identity(path)
        if key in seen:
            continue
        seen.add(key)
        files.append(path)
    if _unordered:
        files.sort(key=lambda item: _path_identity(item))
    return files
def _coerce_str_seq(value: Any) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        items: list[Any] = [value]
    elif isinstance(value, Iterable) and not isinstance(value, (bytes, Mapping)):
        try:
            items = list(value)
        except TypeError:
            return []
    else:
        return []
    result: list[str] = []
    seen: set[str] = set()
    for item in items:
        if not isinstance(item, str):
            logger.debug("[Antipattern] 跳过非字符串清单项: %r", item)
            continue
        text = item.strip()
        if not text or text in seen:
            continue
        seen.add(text)
        result.append(text)
    return result
def _coerce_bool(value: Any, default: bool) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, str):
        text = value.strip().lower()
        if text in {"1", "true", "yes", "on"}:
            return True
        if text in {"0", "false", "no", "off", ""}:
            return False
        return default
    if isinstance(value, (int, float)):
        return bool(value)
    return default
def _coerce_categories(value: Any) -> frozenset[str] | None:
    if value is None:
        return None
    if isinstance(value, str):
        return frozenset({value.strip()}) if value.strip() else None
    if isinstance(value, Mapping):
        items: list[Any] = list(value.keys())
    elif isinstance(value, Iterable) and not isinstance(value, bytes):
        try:
            items = list(value)
        except TypeError:
            logger.debug("[Antipattern] categories 不可迭代，按全量处理: %r",
                         type(value).__name__)
            return None
    else:
        logger.debug("[Antipattern] categories 形态非法，按全量处理: %r",
                     type(value).__name__)
        return None
    return frozenset(
        item.strip() for item in items
        if isinstance(item, str) and item.strip())
def _confidence_or_none(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        number = float(value)
    except OverflowError:
        return None
    if not math.isfinite(number):
        return None
    return min(1.0, max(0.0, number))
def _nonneg_float_or_none(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    try:
        number = float(value)
    except OverflowError:
        return None
    if not math.isfinite(number) or number < 0:
        return None
    return number
def _slot_needs_attention(items: Mapping) -> bool:
    if _coerce_bool(items.get("disabled"), False):
        return False
    return not _coerce_bool(items.get("ok"), True)
def _normalize_cache_params(
    ast_cache: Any, import_nodes: Any,
) -> tuple[Any, Any]:
    if ast_cache is not None and not isinstance(ast_cache, dict):
        logger.debug("[Antipattern] ast_cache 非 dict 形态，按无缓存处理: %r",
                   type(ast_cache).__name__)
        ast_cache = None
    if import_nodes is not None and not isinstance(import_nodes, Mapping):
        logger.debug("[Antipattern] import_nodes 非 Mapping 形态，按无预收集索引处理: %r",
                   type(import_nodes).__name__)
        import_nodes = None
    return ast_cache, import_nodes
def _lookup_precollected_entries(
    import_nodes: Mapping | None, fpath: str,
) -> list | tuple | None:
    if import_nodes is None:
        return None
    _entries = import_nodes.get(fpath)
    if isinstance(_entries, (list, tuple)):
        return _entries
    if _entries is not None:
        logger.debug("[Antipattern] 预收集导入条目非 list/tuple 容器，回退 AST 路径 %s: %r",
                   fpath, type(_entries).__name__)
    return None
class _CrossSkillScan(NamedTuple):
    fpath: str
    skill_name: str
    skill_names: set[str]
    violations: list[dict]
def _record_violation(scan: _CrossSkillScan, lineno: int,
                      imported: str, to_skill: str) -> None:
    scan.violations.append({
        "file": scan.fpath,
        "line": lineno,
        "imports": imported,
        "from_skill": scan.skill_name,
        "to_skill": to_skill,
    })
def _cross_skill_top(name: str, scan: _CrossSkillScan) -> str | None:
    top = name.split('.', 1)[0]
    if top != scan.skill_name and top in scan.skill_names:
        return top
    return None
def _judge_import_kind_entry(
    lineno: int, names: Any, scan: _CrossSkillScan,
) -> None:
    if not isinstance(names, (list, tuple)):
        if names is not None:
            logger.debug("[Antipattern] 跳过畸形 import 条目 names 容器 %s: %r",
                       scan.fpath, names)
        return
    for _alias_name in names:
        if not isinstance(_alias_name, str):
            logger.debug("[Antipattern] 跳过畸形别名项 %s: %r",
                       scan.fpath, _alias_name)
            continue
        _top = _cross_skill_top(_alias_name, scan)
        if _top is not None:
            _record_violation(scan, lineno, _alias_name, _top)
def _judge_from_kind_entry(
    lineno: int, module: Any, level: Any, scan: _CrossSkillScan,
) -> None:
    if not isinstance(level, int) or isinstance(level, bool):
        level = 0
    if level > 0:
        return
    if not isinstance(module, str):
        if module is not None:
            logger.debug("[Antipattern] 跳过畸形 from 条目 module %s: %r",
                       scan.fpath, module)
        return
    _top = _cross_skill_top(module, scan) if module else None
    if _top is not None:
        _record_violation(scan, lineno, module, _top)
def _judge_import_entries(entries: list, scan: _CrossSkillScan) -> None:
    for _entry in entries:
        if not (isinstance(_entry, (list, tuple)) and len(_entry) == 5):
            logger.debug("[Antipattern] 跳过畸形预收集导入条目 %s: %r",
                       scan.fpath, _entry)
            continue
        _lineno, _kind, _names, _module, _level = _entry
        if _kind == "import":
            _judge_import_kind_entry(_lineno, _names, scan)
        elif _kind == "from":
            _judge_from_kind_entry(_lineno, _module, _level, scan)
        else:
            logger.debug("[Antipattern] 跳过未知 kind 预收集导入条目 %s: %r",
                       scan.fpath, _kind)
class CrossSkillDetector:
    def detect(self, skill_dir: str, all_skills_dir: str | None = None,
               ast_cache: dict[str, Any] | None = None,
               import_nodes: dict[str, list[tuple]] | None = None) -> list[dict]:
        root = _coerce_root_arg(skill_dir)
        if not root:
            logger.warning(
                "[Antipattern] 跨技能导入检测跳过：技能根缺失/非法 %r",
                skill_dir)
            return []
        if all_skills_dir is None:
            skills_root = os.path.dirname(os.path.abspath(root))
        else:
            skills_root = _coerce_root_arg(all_skills_dir)
            if skills_root is None:
                logger.warning(
                    "[Antipattern] skills 根缺失/非法，按同级目录回退: %r",
                    all_skills_dir)
                skills_root = os.path.dirname(os.path.abspath(root))
        logger.info("[Antipattern] 跨技能导入检测开始 skill=%s skills_root=%s",
                  root, skills_root)
        violations = []
        skill_name = os.path.basename(os.path.normpath(root))
        if not self._is_skill_root(root):
            logger.info(
                "[Antipattern] 跨技能导入检测不适用（目标非技能根） skill=%s",
                root)
            return violations
        own_identities = self._skill_identities(root)
        skill_names = self._get_skill_names(skills_root)
        skill_names.difference_update(own_identities)
        if not skill_names:
            logger.info("[Antipattern] 跨技能导入检测完成 skill=%s violations=0 "
                      "(skills 根无目录)", skill_dir)
            return violations
        ast_cache, import_nodes = _normalize_cache_params(ast_cache, import_nodes)
        for fpath in iter_scan_py_files(root):
            self._detect_file_violations(
                fpath, ast_cache, import_nodes,
                _CrossSkillScan(fpath, skill_name, skill_names, violations))
        logger.info("[Antipattern] 跨技能导入检测完成 skill=%s violations=%d",
                  skill_dir, len(violations))
        return violations
    def _detect_file_violations(self, fpath: str, ast_cache,
                                import_nodes, scan: _CrossSkillScan) -> None:
        _entries = _lookup_precollected_entries(import_nodes, fpath)
        if _entries is not None:
            _judge_import_entries(_entries, scan)
            return
        tree = self._resolve_tree(fpath, ast_cache)
        if tree is None:
            return
        _local_entries: list[tuple] = []
        for node in walk_nodes(tree):
            if isinstance(node, ast.Import):
                _local_entries.append((node.lineno, "import",
                                       [a.name for a in node.names],
                                       None, 0))
            elif isinstance(node, ast.ImportFrom):
                _local_entries.append((node.lineno, "from",
                                       None, node.module, node.level))
        _judge_import_entries(_local_entries, scan)
    @staticmethod
    def _resolve_tree(fpath: str, ast_cache) -> ast.AST | None:
        if ast_cache is not None and fpath in ast_cache:
            _cached = ast_cache[fpath]
            if _cached is None or isinstance(_cached, ast.AST):
                return _cached
            logger.debug(
                "[Antipattern] ast_cache 值非 AST 树/None 哨兵，"
                "回退现场解析 %s: %r",
                fpath, type(_cached).__name__)
        tree = parse_tree(fpath)
        if tree is None:
            if ast_cache is not None:
                ast_cache[fpath] = None
            return None
        if ast_cache is not None:
            ast_cache[fpath] = tree
        return tree
    @staticmethod
    def _is_skill_root(skill_dir: str) -> bool:
        return os.path.isfile(os.path.join(skill_dir, "SKILL.md"))
    @staticmethod
    def _skill_identities(skill_dir: str) -> set[str]:
        identities = {os.path.basename(os.path.normpath(skill_dir))}
        package_name = detect_layout(skill_dir).package_name
        if package_name:
            identities.add(package_name.split(".", 1)[0])
        return identities
    @staticmethod
    def _get_skill_names(skills_dir: str) -> set[str]:
        if not os.path.isdir(skills_dir):
            return set()
        names: set[str] = set()
        try:
            entries = os.listdir(skills_dir)
        except OSError as e:
            logger.warning("[Antipattern] 技能根枚举失败: %s: %s",
                           skills_dir, e)
            return names
        for dirname in entries:
            skill_dir = os.path.join(skills_dir, dirname)
            if (os.path.isdir(skill_dir) and not dirname.startswith(".")
                    and not dirname.startswith("__")
                    and CrossSkillDetector._is_skill_root(skill_dir)):
                names.update(CrossSkillDetector._skill_identities(skill_dir))
        return names
_DEFAULT_INCLUDE_ANNOTATIONS = True
class DuplicateCodeDetector:
    def detect_duplicate_functions(self, root_dir: str) -> list[dict]:
        root = _coerce_root_arg(root_dir)
        if not root:
            logger.warning("[Antipattern] 重复函数检测跳过：根目录缺失/非法")
            return []
        logger.info("[Antipattern] 重复函数检测开始 root=%s", root)
        func_signatures = self._collect_func_signatures(root)
        duplicates = []
        for sig, entries in func_signatures.items():
            duplicates.extend(self._duplicates_in_group(sig, entries))
        logger.info("[Antipattern] 重复函数检测完成 root=%s groups=%d",
                  root_dir, len(duplicates))
        return duplicates
    def _collect_func_signatures(self, root_dir: str) -> dict:
        func_signatures: dict[str, list[tuple[dict, frozenset[str]]]] = defaultdict(list)
        for fpath in iter_scan_py_files(root_dir):
            tree = parse_tree(fpath)
            if tree is None:
                continue
            _include_annotations = not _future_annotations(tree)
            for node in walk_nodes(tree):
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    sig = self._function_signature(
                        node, _include_annotations)
                    func_signatures[sig].append((
                        {
                            "file": fpath,
                            "name": node.name,
                            "line": node.lineno,
                            "lines": node.end_lineno - node.lineno + 1,
                        },
                        frozenset(
                            n.id for n in _iter_shape_nodes(
                                node, _include_annotations)
                            if isinstance(n, ast.Name)
                        ),
                    ))
        return func_signatures
    @staticmethod
    def _duplicates_in_group(sig: str, entries: list) -> list[dict]:
        groups: list[dict] = []
        for cluster in DuplicateCodeDetector._similarity_clusters(entries):
            metas = [meta for meta, _ids in cluster]
            names = [m["name"] for m in metas]
            max_sim = DuplicateCodeDetector._max_name_jaccard(
                [ids for _meta, ids in cluster])
            groups.append({
                "signature_hash": sig,
                "functions": metas,
                "name_similarity": round(max_sim, 3),
                "suggestion": f"合并 {names} 为单一实现",
            })
        return groups
    @staticmethod
    def _similarity_clusters(entries: list) -> list[list]:
        total = len(entries)
        parent = list(range(total))
        def _find(index: int) -> int:
            while parent[index] != index:
                parent[index] = parent[parent[index]]
                index = parent[index]
            return index
        for i in range(total):
            for j in range(i + 1, total):
                left, right = entries[i][1], entries[j][1]
                union = left | right
                if not union:
                    continue
                if len(left & right) / len(union) < 0.7:
                    continue
                root_i, root_j = _find(i), _find(j)
                if root_i != root_j:
                    parent[root_j] = root_i
        buckets: dict[int, list[int]] = {}
        for index in range(total):
            buckets.setdefault(_find(index), []).append(index)
        ordered = sorted(buckets.values(), key=lambda idxs: idxs[0])
        return [
            [entries[index] for index in idxs]
            for idxs in ordered if len(idxs) >= 2
        ]
    @staticmethod
    def _max_name_jaccard(name_sets: list) -> float:
        max_sim = 0.0
        for i in range(len(name_sets)):
            for j in range(i + 1, len(name_sets)):
                union = name_sets[i] | name_sets[j]
                if union:
                    sim = len(name_sets[i] & name_sets[j]) / len(union)
                    max_sim = max(max_sim, sim)
        return max_sim
    def _function_signature(
            self, func_node: ast.AST,
            include_annotations: bool = _DEFAULT_INCLUDE_ANNOTATIONS) -> str:
        _a = func_node.args
        params = (len(_a.posonlyargs) + len(_a.args) + len(_a.kwonlyargs)
                  + (1 if _a.vararg else 0) + (1 if _a.kwarg else 0))
        shape = (f"{len(_a.posonlyargs)}_{len(_a.args)}_{len(_a.kwonlyargs)}"
                 f"_{1 if _a.vararg else 0}_{1 if _a.kwarg else 0}")
        returns, branches, loops, calls, assign_targets = (
            self._walk_shape_stats(func_node, include_annotations))
        call_hash = hashlib.md5('|'.join(sorted(calls)[:8]).encode(), usedforsecurity=False).hexdigest()[:8]
        assign_hash = hashlib.md5('|'.join(sorted(assign_targets)[:8]).encode(), usedforsecurity=False).hexdigest()[:8]
        execution_kind = (
            "async" if isinstance(func_node, ast.AsyncFunctionDef) else "sync")
        return (f"k{execution_kind}_p{params}_s{shape}_r{returns}_b{branches}"
                f"_l{loops}_ch{call_hash}_ah{assign_hash}")
    @staticmethod
    def _walk_shape_stats(
            func_node: ast.AST,
            include_annotations: bool = _DEFAULT_INCLUDE_ANNOTATIONS) -> tuple:
        counts = dict.fromkeys(("returns", "branches", "loops"), 0)
        calls: set[str] = set()
        assign_targets: set[str] = set()
        for node in _iter_shape_nodes(func_node, include_annotations):
            tally_shape_node(node, counts, calls, assign_targets)
        return (counts["returns"], counts["branches"], counts["loops"],
                calls, assign_targets)
def _future_annotations(tree: ast.AST) -> bool:
    for node in getattr(tree, "body", ()):
        if (isinstance(node, ast.ImportFrom)
                and node.module == "__future__"
                and any(alias.name == "annotations" for alias in node.names)):
            return True
    return False
def _definition_time_children(
        node: ast.AST,
        include_annotations: bool = _DEFAULT_INCLUDE_ANNOTATIONS) -> list[ast.AST]:
    children: list[ast.AST] = []
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        children.extend(node.decorator_list)
        if include_annotations:
            if node.returns is not None:
                children.append(node.returns)
            for arg in (*node.args.posonlyargs, *node.args.args,
                        *node.args.kwonlyargs):
                if arg.annotation is not None:
                    children.append(arg.annotation)
            for arg in (node.args.vararg, node.args.kwarg):
                if arg is not None and arg.annotation is not None:
                    children.append(arg.annotation)
        children.extend(getattr(node, "type_params", ()) or ())
    children.extend(node.args.defaults)
    children.extend(d for d in node.args.kw_defaults if d is not None)
    return children
def _iter_shape_nodes(
        scope_node: ast.AST,
        include_annotations: bool = _DEFAULT_INCLUDE_ANNOTATIONS) -> Iterator[ast.AST]:
    if isinstance(scope_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
        stack = [*scope_node.body,
                 *_definition_time_children(scope_node, include_annotations)]
    elif isinstance(scope_node, ast.Lambda):
        stack = [scope_node.body,
                 *_definition_time_children(scope_node, include_annotations)]
    else:
        stack = list(ast.iter_child_nodes(scope_node))
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda)):
            stack.extend(_definition_time_children(node, include_annotations))
            continue
        stack.extend(ast.iter_child_nodes(node))
DEFAULT_DUP_MIN_OCCURRENCES = 3
DEFAULT_DUP_MIN_FILES = 2
DEFAULT_DUP_MIN_SINGLE_FILE_OCCURRENCES = 5
DEFAULT_DUP_MAX_SITES = 20
def _site_preview(sites: list[dict], root_dir: str, limit: int = 3) -> str:
    parts: list[str] = []
    for site in sites[:limit]:
        try:
            rel = os.path.relpath(site["file"], root_dir)
        except (OSError, ValueError) as _swallowed_exc:
            log_swallowed(
                __name__, _swallowed_exc,
                context=f"_site_preview:{type(_swallowed_exc).__name__}")
            rel = str(site["file"])
        parts.append(f"{rel}:{site['line']}({site['function']})")
    if len(sites) > limit:
        parts.append(f"等 {len(sites)} 处")
    return "、".join(parts)
class DefaultParamDuplicationDetector:
    MIN_OCCURRENCES = DEFAULT_DUP_MIN_OCCURRENCES
    MIN_FILES = DEFAULT_DUP_MIN_FILES
    MIN_SINGLE_FILE_OCCURRENCES = DEFAULT_DUP_MIN_SINGLE_FILE_OCCURRENCES
    def detect(self, root_dir: str) -> list[dict]:
        root = _coerce_root_arg(root_dir)
        if not root:
            logger.warning(
                "[Antipattern] 重复默认参数检测跳过：根目录缺失/非法")
            return []
        groups: dict[tuple, list[dict]] = defaultdict(list)
        for fpath in iter_scan_py_files(root):
            tree = parse_tree(fpath)
            if tree is None:
                continue
            for key, site in default_param_sites(tree, fpath):
                groups[key].append(site)
        findings = self._build_findings(groups, root)
        findings.sort(key=lambda f: (_path_identity(f["file"]),
                                     f["line"], f["param"]))
        if findings:
            logger.info("[Antipattern] 重复默认参数检测完成 groups=%d",
                        len(findings))
        return findings
    def _build_findings(self, groups: dict[tuple, list[dict]],
                        root_dir: str) -> list[dict]:
        findings: list[dict] = []
        for (param, _kind, value), sites in groups.items():
            file_count = self._reportable_file_count(sites)
            if file_count is None:
                continue
            findings.append(
                self._finding(param, value, sites, file_count, root_dir))
        return findings
    def _reportable_file_count(self, sites: list[dict]) -> int | None:
        if len(sites) < self.MIN_OCCURRENCES:
            return None
        file_count = len({_path_identity(s["file"]) for s in sites})
        if file_count == 1:
            return (file_count if len(sites) >= self.MIN_SINGLE_FILE_OCCURRENCES
                    else None)
        return file_count if file_count >= self.MIN_FILES else None
    @staticmethod
    def _finding(param: str, value, sites: list[dict], file_count: int,
                 root_dir: str) -> dict:
        sites.sort(key=lambda s: (_path_identity(s["file"]),
                                  s["line"], s["function"]))
        first = sites[0]
        detail = (
            f"重复默认参数 {param}={value!r}：{len(sites)} 处 / "
            f"{file_count} 个文件（{_site_preview(sites, root_dir)}），"
            "修改默认值需同步多处"
        )
        finding = {
            "file": first["file"],
            "line": first["line"],
            "function": first["function"],
            "param": param,
            "default": repr(value),
            "occurrences": len(sites),
            "file_count": file_count,
            "sites": sites[:DEFAULT_DUP_MAX_SITES],
            "detail": detail,
            "message": detail,
            "suggestion": (
                "抽取为共享常量或配置项（如模块级 DEFAULT_* / Settings），"
                "各函数引用同一来源，避免默认值漂移"
            ),
        }
        if len(sites) > DEFAULT_DUP_MAX_SITES:
            finding["overflow_sites"] = sites[DEFAULT_DUP_MAX_SITES:]
        return finding
_ENGINE_CATEGORY_SEVERITY: dict[str, str] = {
    "C1_facade": "low",
    "C2_lazy_import": "low",
    "C4_regression": "low",
    "C6_circular": "low",
    "C8_dead_code": "low",
    "C10_fragments": "medium",
    "C11_duplicates": "low",
    "C16_stubs": "low",
    "C17_dynamic_import": "low",
    "C18_default_duplication": "low",
    "C19_passthrough_layer": "low",
}
def _abspath_at_root(path: Any, root: Any) -> str:
    text = _text_or_fspath(path)
    root_text = _coerce_root_arg(root)
    if not text or not root_text:
        return ""
    if not os.path.isabs(text):
        text = os.path.join(root_text, text)
    return os.path.abspath(text)
def _path_in_tree(path: str, root: str) -> bool:
    root_text = _coerce_root_arg(root)
    if not _text_or_fspath(path) or not root_text:
        return False
    try:
        _ap = os.path.normcase(_abspath_at_root(path, root_text))
        _rp = os.path.normcase(os.path.abspath(root_text))
        return os.path.commonpath([_ap, _rp]) == _rp
    except (ValueError, OSError, TypeError) as _e:
        logger.debug(
            "_path_in_tree 异常，保守视为越界: path=%s root=%s: %s",
            path, root, _e)
        return False
def _group_files_by_parent_dir(files: list) -> dict[str, set[str]]:
    drive_groups: dict[str, dict[str, set[str]]] = {}
    for fpath in files:
        if not fpath.lower().endswith(".py"):
            continue
        absolute = os.path.abspath(fpath)
        drive = os.path.normcase(os.path.splitdrive(absolute)[0])
        parent = os.path.dirname(absolute)
        drive_groups.setdefault(drive, {}).setdefault(parent, set()).add(
            _path_identity(fpath))
    grouped: dict[str, set[str]] = {}
    for dir_files_map in drive_groups.values():
        common_root = os.path.commonpath(list(dir_files_map))
        grouped[common_root] = set().union(*dir_files_map.values())
    return {key: grouped[key] for key in sorted(grouped, key=os.path.normcase)}
def _category_issue(category: str, file_path: Any, line: Any,
                    detail: Any) -> dict:
    return {
        "type": category,
        "file": _text_or_fspath(file_path),
        "line": _norm_issue_line(line),
        "severity": _ENGINE_CATEGORY_SEVERITY.get(category, "low"),
        "detail": _norm_issue_str(detail),
    }
def _dict_category_detail(findings: dict, category: str) -> str:
    detail = _norm_issue_str(
        findings.get("detail"), findings.get("description"))
    if not detail and isinstance(findings.get("fragmentation_rate"), (int, float)):
        detail = (
            f"目录碎片化: 碎片率 {findings.get('fragmentation_rate')}"
            f"（{findings.get('small_file_count', '?')}/"
            f"{findings.get('total_files', '?')} 个文件为微型文件），"
            f"阈值 {findings.get('small_file_threshold_hint', '?')}"
        )
    if detail:
        return detail
    keys = sorted(
        str(key) for key in findings
        if key not in {"disabled", "ok", "needs_consolidation",
                       "small_file_list"})
    suffix = f"（{', '.join(keys[:5])}）" if keys else ""
    return f"{category or '反模式'} 检查未通过{suffix}"
def _antipattern_detail(finding: dict, category: str) -> str:
    for key in ("message", "detail", "description", "suggestion",
                "pattern", "value"):
        text = _norm_issue_str(finding.get(key))
        if text:
            return text
    # 检测器自身的失败原因（如源码不可解析）必须优先于数值型兜底文案：
    # 否则 facade_count=0 的解析失败会被写成「门面数量 0 超过上限」的假违规。
    error = _norm_issue_str(finding.get("error"))
    if error:
        return f"{category} 检查未通过: {error}"
    cycle = finding.get("cycle")
    if isinstance(cycle, (list, tuple)) and cycle:
        return "循环依赖链: " + " -> ".join(str(module) for module in cycle)
    if "facade_count" in finding:
        return (f"__init__.py 门面数量 {finding.get('facade_count', '?')} "
                f"超过上限 {finding.get('max_facade', '?')}")
    kind = _norm_issue_str(finding.get("type"))
    name = _norm_issue_str(finding.get("name"), finding.get("function"))
    if kind and name:
        return f"{kind}: {name}"
    return kind or name or f"{category} 反模式"
def _duplicate_group_issues(category: str, finding: dict, funcs: list,
                            file_set: set) -> list[dict]:
    group_names = [str(fn.get("name", "?")) for fn in funcs if isinstance(fn, dict)]
    suggestion = str(finding.get("suggestion", "") or "")
    issues: list[dict] = []
    for fn in funcs:
        if not isinstance(fn, dict) or not fn.get("file"):
            continue
        if _path_identity(fn["file"]) not in file_set:
            continue
        detail = (f"重复函数 {fn.get('name', '?')!s} "
                  f"(相似组: {', '.join(group_names)})")
        if suggestion:
            detail += f"; 建议: {suggestion}"
        issues.append(_category_issue(category, fn["file"], fn.get("line", 0), detail))
    return issues
def _sites_in_file_set(finding: dict, file_set: set) -> list[dict]:
    sites = finding.get("sites")
    overflow_sites = finding.get("overflow_sites", [])
    if not isinstance(sites, list):
        return []
    if not isinstance(overflow_sites, list):
        overflow_sites = []
    matched: list[dict] = []
    for site in [*sites, *overflow_sites]:
        if not isinstance(site, dict):
            continue
        fpath = str(site.get("file") or "")
        if fpath and _path_identity(fpath) in file_set:
            matched.append(site)
    return matched
def _cycle_issue(category: str, cycle: list, parent_dir: str) -> list[dict]:
    return [_category_issue(
        category, parent_dir, 0,
        "循环依赖链: " + " -> ".join(str(m) for m in cycle))]
def _finding_issues(category: str, finding: dict, parent_dir: str,
                    file_set: set) -> list[dict]:
    fpath = finding_file(finding)
    if fpath and _path_identity(fpath) in file_set:
        return [_category_issue(
            category, fpath, finding.get("line", 0),
            _antipattern_detail(finding, category))]
    sites = _sites_in_file_set(finding, file_set)
    if sites:
        anchor = sites[0]
        return [_category_issue(
            category, anchor.get("file", ""), anchor.get("line", 0),
            _antipattern_detail(finding, category))]
    funcs = finding.get("functions")
    if isinstance(funcs, list) and funcs:
        return _duplicate_group_issues(category, finding, funcs, file_set)
    cycle = finding.get("cycle")
    if isinstance(cycle, list) and cycle:
        return _cycle_issue(category, cycle, parent_dir)
    return []
class SignalType(Enum):
    PERFORMANCE_DROP = "performance_drop"
    ANOMALY = "anomaly"
@dataclass
class DetectedSignal:
    signal_type: SignalType
    strength: float
    source: str
    description: str
    detected_at: float
    metadata: dict[str, Any] = field(default_factory=dict)
    triggered: bool = False
class SignalDetector:
    DEFAULT_MAX_HISTORY = 1000
    WEAK_SIGNAL_THRESHOLD = 0.3
    TIMING_HISTORY_LIMIT = 20
    PERFORMANCE_DROP_RATIO = 1.5
    def __init__(self: Self, max_history: int | None = None) -> None:
        self.max_history = max_history
        self._signals: list[DetectedSignal] = []
        self._timings: dict[str, list[float]] = {}
    @property
    def max_history(self: Self) -> int:
        return self._max_history
    @max_history.setter
    def max_history(self: Self, value: Any) -> None:
        self._max_history = self._normalize_history(value)
    @classmethod
    def _normalize_history(cls, value: Any) -> int:
        if value is None or isinstance(value, bool):
            return cls.DEFAULT_MAX_HISTORY
        try:
            parsed = int(value)
        except (TypeError, ValueError, OverflowError):
            logger.debug(
                "[Antipattern] max_history 非法，回退默认上限: %r", value)
            return cls.DEFAULT_MAX_HISTORY
        return max(0, parsed)
    def _add_signal(self: Self, signal: DetectedSignal) -> None:
        self._signals.append(signal)
        if self.max_history <= 0:
            self._signals = []
        elif len(self._signals) > self.max_history:
            self._signals = self._signals[-self.max_history:]
    def _get_baseline(self: Self, operation: str) -> float | None:
        timings = self._timings.get(operation)
        if timings:
            valid = [value for value in timings
                     if _nonneg_float_or_none(value) is not None]
            if valid:
                return sum(valid) / len(valid)
        return None
    def _record_timing(self: Self, operation: str, elapsed_ms: float) -> None:
        timings = self._timings.setdefault(operation, [])
        timings.append(elapsed_ms)
        if len(timings) > self.TIMING_HISTORY_LIMIT:
            del timings[:len(timings) - self.TIMING_HISTORY_LIMIT]
    def detect_signal(
        self: Self, signal_type: SignalType, source: str,
        strength: float, description: str = "",
        metadata: dict[str, Any] | None = None,
    ) -> DetectedSignal:
        _strength = _confidence_or_none(strength)
        if _strength is None:
            logger.debug("[Antipattern] strength 非法，按 0.0 处理: %r",
                         strength)
            _strength = 0.0
        _source = _norm_issue_str(source) or "<unknown>"
        _label = (signal_type.value
                  if isinstance(signal_type, SignalType) else str(signal_type))
        _meta = dict(metadata) if isinstance(metadata, Mapping) else {}
        signal = DetectedSignal(
            signal_type=signal_type,
            strength=_strength,
            source=_source,
            description=_norm_issue_str(description) or f"{_label} from {_source}",
            detected_at=time.time(),
            metadata=_meta,
            triggered=_strength >= self.WEAK_SIGNAL_THRESHOLD,
        )
        self._add_signal(signal)
        return signal
    def check_performance(self: Self, operation: str, current_ms: float) -> DetectedSignal | None:
        _operation = _norm_issue_str(operation) or "<unknown>"
        _current = _nonneg_float_or_none(current_ms)
        if _current is None:
            logger.debug("[Antipattern] 耗时非法，跳过性能采样: %r",
                         current_ms)
            return None
        baseline = self._get_baseline(_operation)
        self._record_timing(_operation, _current)
        if baseline is None or baseline <= 0:
            return None
        if _current > baseline * self.PERFORMANCE_DROP_RATIO:
            strength = min(1.0, (_current - baseline) / baseline)
            return self.detect_signal(
                signal_type=SignalType.PERFORMANCE_DROP,
                source=_operation,
                strength=strength,
                description=f"性能下降: {_current:.1f}ms vs baseline {baseline:.1f}ms",
                metadata={"baseline_ms": baseline, "current_ms": _current},
            )
        return None
    @property
    def signals(self: Self) -> list[DetectedSignal]:
        return list(self._signals)
    def drain_triggered(self: Self) -> list[DetectedSignal]:
        triggered = [s for s in self._signals if s.triggered]
        if triggered:
            self._signals = [s for s in self._signals if not s.triggered]
        return triggered
    def clear(self: Self) -> None:
        self._signals.clear()
        self._timings.clear()
_SCAN_TOP_N_MIN = 1
def _scan_is_core_py(fname: str, fpath: str, root: str = "") -> bool:
    if not is_scan_py_name(fname):
        return False
    return not is_scan_excluded(
        str(fpath).replace("\\", "/"), fname, root_dir=root or None)
def _scan_file_size(fpath: str) -> int:
    try:
        return os.path.getsize(fpath)
    except OSError:
        logger.debug("getsize 失败按 0 参与排序: %s", fpath, exc_info=True)
        return 0
def _scan_norm_top_n(top_files) -> int:
    try:
        return max(_SCAN_TOP_N_MIN, int(top_files))
    except (TypeError, ValueError, OverflowError):
        logger.debug("top_files 非法，按 %d 回退: %r", _SCAN_TOP_N_MIN, top_files)
        return _SCAN_TOP_N_MIN
def _walk_denied(err: OSError) -> None:
    logger.warning("目录遍历降级（跳过不可读目录）: %s", err)
def _scan_collect_size_paths(skill_dir: str) -> list[tuple[int, str]]:
    collected: list[tuple[int, str]] = []
    _skip_dirs = scan_prune_dirs(skill_dir)
    for root, dirs, files in os.walk(skill_dir, onerror=_walk_denied):
        prune_scan_dirnames(dirs, _skip_dirs)
        for fname in files:
            fpath = os.path.join(root, fname)
            if not _scan_is_core_py(fname, fpath, skill_dir):
                continue
            collected.append((_scan_file_size(fpath), fpath))
    return collected
def collect_top_scan_files(skill_dir: str, top_files: int) -> list[str]:
    root = _coerce_root_arg(skill_dir)
    if not root:
        logger.warning("[Antipattern] 顶层扫描选择跳过：技能根缺失/非法")
        return []
    collected = _scan_collect_size_paths(root)
    collected.sort(key=lambda item: (-item[0], os.path.normcase(item[1])))
    picked = [p for _, p in collected[:_scan_norm_top_n(top_files)]]
    init_path = os.path.join(root, "__init__.py")
    if (os.path.isfile(init_path) and init_path not in picked
            and _scan_is_core_py(
                os.path.basename(init_path), init_path, root)):
        picked.append(init_path)
    return picked
_SEVERITY_CONFIDENCE = {"P0": 0.90, "P1": 0.75, "P2": 0.55, "P3": 0.40}
_PHASE_DIRECT_OVERLAP_IDS = frozenset({
    "SN01", "SN02", "SN03", "SN04", "SN05",
    "AI02", "AI03",
    "SL06",
})
def _scan_file_and_registry(fp: str, cache, exclude, reg_exclude) -> list:
    try:
        src, _tree = load_source_and_tree(fp, cache)
        if not src:
            return []
        issues = detect_all(src, fp, tree=_tree, exclude_rules=exclude)
        if not isinstance(issues, (list, tuple)):
            issues = []
        for iss in issues:
            if isinstance(iss, dict):
                iss["file"] = fp
        return list(issues) + _registry_channel_issues(
            src, fp, _tree, reg_exclude)
    except (OSError, UnicodeDecodeError, ValueError, KeyError, TypeError,
            RecursionError, MemoryError) as e:
        logger.warning("[UnifiedAstEngine] A1 file error: %s: %s", fp, e)
    return []
def _registry_channel_issues(src: str, fp: str, _tree,
                             reg_exclude) -> list:
    reg_issues: list = []
    try:
        raw = _get_registry().run_file_detectors(
            src, fp, tree=_tree, exclude_ids=reg_exclude)
        if raw is None:
            return []
        if not isinstance(raw, (list, tuple)):
            logger.warning(
                "[UnifiedAstEngine] A1 registered detectors 返回异形容器: %r",
                type(raw).__name__)
            return []
        reg_issues = list(raw)
        for _ri in reg_issues:
            if isinstance(_ri, dict):
                _ri["file"] = fp
    except Exception as _e:
        logger.warning("[UnifiedAstEngine] A1 registered detectors failed: %s", _e)
    return reg_issues
def _normalize_issue_severities(all_issues: list) -> None:
    for iss in all_issues:
        if not isinstance(iss, dict):
            continue
        sev = iss.get("severity", "")
        if not isinstance(sev, str) or sev not in _SEVERITY_CONFIDENCE:
            sev = normalize_severity(sev)
            iss["severity"] = sev
        _conf = _confidence_or_none(iss.get("confidence"))
        iss["confidence"] = (
            _SEVERITY_CONFIDENCE.get(sev, 0.50) if _conf is None else _conf)
def _release_file_scope_caches() -> None:
    """释放全部「按 AST 对象身份作键」的派生缓存（文件边界调用）。

    文件内的复用（实测最高 77.6×）在本次扫描结束前已全部发生，因此释放
    **不损失任何命中**，只把驻留内存从「全部文件」压回「当前文件」。
    """
    try:
        from jwsgj.diag_shared_ast_nodes import release_ast_identity_caches
        release_ast_identity_caches()
    except Exception:  # 释放失败不阻断诊断
        logger.debug("[UnifiedAstEngine] AST 身份缓存释放失败", exc_info=True)
    for _mod, _fn in (("jwsgj.prevention_scope_facts", "release_scope_fact_caches"),
                      ("jwsgj.diag_shared_ast_bindings", "release_binding_caches"),
                      ("jwsgj.diag_guard_sql_statement", "release_rd30_caches")):
        try:
            getattr(importlib.import_module(_mod), _fn)()
        except Exception:  # 模块未加载/未提供钩子，跳过
            logger.debug("[UnifiedAstEngine] %s.%s 跳过", _mod, _fn)


def run_file_detectors(py_files: list[str], cache: Any = None) -> list[dict]:
    _t0 = time.monotonic()
    all_issues: list[dict] = []
    _exclude = RETIRED_RULE_IDS if RETIRED_RULE_IDS else None
    _reg_exclude = (retired_registry_excludes() | registry_sec_family_ids()
                    | _PHASE_DIRECT_OVERLAP_IDS)
    _scan_files = _coerce_py_files(py_files)
    logger.info("[UnifiedAstEngine] A1 扫描文件: %d", len(_scan_files))
    _total = len(_scan_files)
    for _done, fp in enumerate(_scan_files, start=1):
        if _done % 50 == 0 or _done == _total:
            logger.info("[UnifiedAstEngine] A1 扫描进度: %d/%d", _done, _total)
        try:
            all_issues.extend(
                _scan_file_and_registry(fp, cache, _exclude, _reg_exclude))
        except Exception as e:
            logger.warning("[UnifiedAstEngine] A1 扫描异常: %s: %s", fp, e)
        finally:
            # 文件边界释放「按 AST 对象身份作键」的派生缓存。
            # 这些缓存跨文件永远不可能命中（键是上一文件的 AST 对象），
            # 保留只会钉住整棵文件 AST：实测 4 个文件后 RSS 139 MB → 1757 MB。
            _release_file_scope_caches()
    _normalize_issue_severities(all_issues)
    write_module_run(
        "diag_antipattern_flow_detect", "run_file_detectors",
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        files=len(_scan_files), issues=len(all_issues))
    return all_issues
def _in_scope_file(fp: str, skill_dir: str) -> bool:
    root = _coerce_root_arg(skill_dir)
    if not root:
        logger.debug("[Antipattern] 作用域判定跳过：技能根缺失/非法 %r",
                     skill_dir)
        return False
    try:
        probe = _abspath_at_root(fp, root).replace("\\", "/")
        if not probe:
            return False
        rel_dir = os.path.dirname(
            os.path.relpath(probe, os.path.abspath(root)))
    except (OSError, TypeError, ValueError):
        return False
    if is_scan_excluded(probe, os.path.basename(probe), root_dir=root):
        return False
    rel_segs = [seg for seg in rel_dir.replace("\\", "/").split("/") if seg]
    if ".." in rel_segs:
        return False
    excluded = scan_exclude_dirs(root)
    return not any(seg.lower() in excluded for seg in rel_segs)
def _pattern_finding_to_issue(f, default_rule_id: str, category: str,
                             confidence: float,
                             detail_fallback: bool = False) -> dict:
    _msg = (_norm_issue_str(getattr(f, "message", "")) or
            (_norm_issue_str(getattr(f, "detail", ""))
             if detail_fallback else ""))
    _pattern = _norm_issue_str(getattr(f, "pattern_name", ""))
    _message = ": ".join(_part for _part in (_pattern, _msg) if _part)
    return _issue_envelope(
        _norm_issue_str(getattr(f, "detector_id", ""), default_rule_id),
        getattr(f, "severity", ""),
        getattr(f, "line", 0),
        _norm_issue_str(getattr(f, "filepath", None),
                        getattr(f, "file", None)),
        _message,
        category, confidence)
_MERGE_SAFETY_CATEGORIES = {
    "D20_merge_preflight": "merge_cycle_preflight",
    "D21_unicode_safety": "unicode_safety",
}
def _collect_merge_safety_issues(result: Any, all_issues: list) -> None:
    if not isinstance(result, dict):
        return
    for d_key, d_items in result.items():
        if not isinstance(d_items, list):
            continue
        for item in d_items:
            if not isinstance(item, dict):
                continue
            all_issues.append(_issue_envelope(
                d_key, item.get("severity", "P2"), item.get("line"),
                (_text_or_fspath(item.get("file"))
                 or _text_or_fspath(item.get("filepath"))),
                (_norm_issue_str(item.get("message"))
                 or f"{d_key} 检查未通过"),
                _MERGE_SAFETY_CATEGORIES.get(d_key, "unknown"), 0.65))
def _import_safety_issue(finding: Any, target: str, rule_id: str,
                         default_sev: str, skill_dir: str) -> dict | None:
    if not isinstance(finding, dict):
        return None
    filepath = str(finding.get("file") or target)
    if not _path_in_tree(filepath, skill_dir):
        return None
    return _issue_envelope(
        _norm_issue_str(finding.get("rule_id"), rule_id),
        finding.get("severity") or default_sev,
        finding.get("line"), filepath,
        (_norm_issue_str(finding.get("message"))
         or f"{rule_id} 导入安全检查未通过"),
        _norm_issue_str(finding.get("category"), "import_safety"),
        0.80 if default_sev == "P0" else 0.70)
_IMPORT_SAFETY_CHANNELS = (("GF16", "P0"), ("GF18", "P1"))
def _run_import_safety_channel(py_files: list, skill_dir: str,
                               all_issues: list) -> None:
    _reg = _get_registry()
    _targets = sorted(
        (resolved for f in py_files
         if (resolved := _abspath_at_root(f, skill_dir))
         and _in_scope_file(resolved, skill_dir)),
        key=lambda path: _path_identity(path))
    if not _targets:
        logger.info(
            "[UnifiedAstEngine] A5 import_safety 通道前置跳过 "
            "(无范围内文件, py_files=%d)", len(py_files))
        return
    logger.info("[UnifiedAstEngine] A5 import_safety 覆盖文件: %d",
                len(_targets))
    _context = build_import_scan_context(skill_dir)
    _seen: set[tuple] = set()
    for _cid, _sev_default in _IMPORT_SAFETY_CHANNELS:
        for _target in _targets:
            for _f in (_reg.run(
                    _cid, filepath=_target, context=_context) or []):
                _issue = _import_safety_issue(
                    _f, _target, _cid, _sev_default, skill_dir)
                if _issue is None:
                    continue
                _key = (_issue["rule_id"], _issue["file"],
                        _issue["line"], _issue["message"])
                if _key in _seen:
                    continue
                _seen.add(_key)
                all_issues.append(_issue)
_SQLITE_SUFFIXES = (".db", ".sqlite", ".sqlite3")
def _discover_xt01_context(skill_dir: str) -> tuple[list[str], str | None]:
    _db_paths: list[str] = []
    _skip_dirs = scan_prune_dirs(skill_dir)
    for _root, _dirs, _fns in os.walk(skill_dir, onerror=_walk_denied):
        prune_scan_dirnames(_dirs, _skip_dirs)
        _db_paths.extend(
            os.path.join(_root, _fn) for _fn in _fns
            if _fn.lower().endswith(_SQLITE_SUFFIXES))
    _skill_md = os.path.join(skill_dir, "SKILL.md")
    return (sorted(_db_paths, key=os.path.normcase),
            _skill_md if os.path.isfile(_skill_md) else None)
def _xt01_issue(finding: Any, skill_dir: str) -> dict | None:
    if not isinstance(finding, dict):
        return None
    _pattern = _norm_issue_str(finding.get("pattern"), "unknown")
    _message = _norm_issue_str(finding.get("message")) or "未提供详情"
    return _issue_envelope(
        "XT01", finding.get("severity") or "WARNING",
        finding.get("lineno") or finding.get("line"),
        (_text_or_fspath(finding.get("filepath"))
         or _text_or_fspath(skill_dir)),
        f"XT01 {_pattern}: {_message}",
        "sql_structure", 0.65,
        suggestion=_norm_issue_str(finding.get("suggestion")))
def _run_xt01_channel(skill_dir: str, all_issues: list) -> None:
    _db_paths, _skill_md = _discover_xt01_context(skill_dir)
    if not (_db_paths or _skill_md):
        logger.info("[UnifiedAstEngine] A5 XT01 通道前置跳过 (无 db 文件且无 SKILL.md)")
        return
    for _f in (_get_registry().run(
            "XT01", root_dir=skill_dir, db_paths=_db_paths,
            skill_md_path=_skill_md) or []):
        _issue = _xt01_issue(_f, skill_dir)
        if _issue is not None:
            all_issues.append(_issue)
def _run_channel_guarded(label: str, fn, *args) -> int:
    try:
        fn(*args)
        return 0
    except Exception as e:
        logger.warning("[UnifiedAstEngine] %s failed: %s", label, e)
        return 1
def _run_new_patterns_channel(skill_dir: str, all_issues: list) -> None:
    findings = detect_all_new_patterns(
        skill_dir, include_file=partial(_in_scope_file, skill_dir=skill_dir))
    for f in findings:
        all_issues.append(_pattern_finding_to_issue(
            f, "D34", "new_pattern_detector", 0.70,
            detail_fallback=True))
_AUDIT_RETIRED_IDS = frozenset(AUDIT_DETECTOR_IDS) & RETIRED_RULE_IDS
def _run_audit_patterns_channel(skill_dir: str, all_issues: list) -> None:
    _audit_exclude = _AUDIT_RETIRED_IDS
    if AUDIT_DETECTOR_IDS and _audit_exclude >= frozenset(AUDIT_DETECTOR_IDS):
        logger.info(
            "[UnifiedAstEngine] A5 audit_patterns 通道前置跳过 "
            "(exclude 覆盖全部 %d 个运行检测器)", len(AUDIT_DETECTOR_IDS))
        return
    audit_findings = detect_all_audit_patterns(
        skill_dir,
        exclude_detectors=set(_audit_exclude),
        include_file=partial(_in_scope_file, skill_dir=skill_dir),
    )
    for f in audit_findings:
        all_issues.append(_pattern_finding_to_issue(
            f, "D41", "audit_pattern_detector", 0.75))
def _run_detect_all_new_channel(skill_dir: str, all_issues: list) -> None:
    result = detect_all_new(
        skill_dir, include_file=partial(_in_scope_file, skill_dir=skill_dir),
        skip_keys={"D20_merge_preflight"} & RETIRED_RULE_IDS,
    )
    _collect_merge_safety_issues(result, all_issues)
def run_extended_detectors(skill_dir: str,
                           py_files: list[str]) -> tuple[list[dict], int]:
    _t0 = time.monotonic()
    root = _coerce_root_arg(skill_dir)
    _files = _coerce_py_files(py_files)
    if not root:
        logger.warning("[UnifiedAstEngine] extended 跳过：技能根缺失/非法")
        write_module_run(
            "diag_antipattern_flow_detect", "run_extended_detectors",
            outcome="degraded",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            issues=0, failures=1, files=len(_files))
        return [], 1
    all_issues: list[dict] = []
    failures = 0
    failures += _run_channel_guarded(
        "A5 new_patterns", _run_new_patterns_channel, root, all_issues)
    failures += _run_channel_guarded(
        "A5 audit_patterns", _run_audit_patterns_channel, root, all_issues)
    failures += _run_channel_guarded(
        "A5 detect_all_new", _run_detect_all_new_channel, root, all_issues)
    failures += _run_channel_guarded(
        "A5 import_safety", _run_import_safety_channel, _files, root,
        all_issues)
    failures += _run_channel_guarded(
        "A5 XT01", _run_xt01_channel, root, all_issues)
    write_module_run(
        "diag_antipattern_flow_detect", "run_extended_detectors",
        outcome="ok" if not failures else "degraded",
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        issues=len(all_issues), failures=failures, files=len(_files))
    return all_issues, failures
_AP_CATEGORY_MAP = {
    "C1_facade": ("AP-C1", "P3", "Facade 反模式(信息级提示)"),
    "C2_lazy_import": ("AP-C2", "P3", "延迟导入反模式(信息级提示)"),
    "C4_regression": ("AP-C4", "P3", "退化代码反模式(信息级提示)"),
    "C6_circular": ("AP-C6", "P3", "循环依赖反模式(信息级提示)"),
    "C8_dead_code": ("AP-C8", "P3", "死代码反模式(信息级提示)"),
    "C11_duplicates": ("AP-C11", "P3", "重复代码反模式(信息级提示)"),
    "C16_stubs": ("AP-C16", "P3", "桩函数反模式(信息级提示)"),
    "C17_dynamic_import": ("AP-C17", "P3", "动态导入反模式(信息级提示)"),
    "C18_default_duplication": ("AP-C18", "P3", "重复默认参数反模式(信息级提示)"),
    "C19_passthrough_layer": ("AP-C19", "P3", "纯转发层反模式(信息级提示)"),
    "C10_fragments": ("AP-C10", "P2", "目录碎片化反模式(需合并)"),
}
_AP_RULE_INDEX = {
    _rule_id: (_rule_id, _severity, _desc)
    for _rule_id, _severity, _desc in _AP_CATEGORY_MAP.values()
}
def _ap_category_mapping(raw_rule: str) -> tuple:
    raw = _norm_issue_str(raw_rule)
    if not raw:
        return "AP-unknown", "P3", "未知反模式"
    mapped = _AP_CATEGORY_MAP.get(raw)
    if mapped is not None:
        return mapped
    already = _AP_RULE_INDEX.get(raw)
    if already is not None:
        return already
    if raw[:3].upper() == "AP-":
        return raw, "P3", raw
    return "AP-" + raw, "P3", raw
def _normalize_density_fields(f: dict) -> tuple:
    filepath = finding_file(f)
    _line = _norm_issue_line(f.get("line"), f.get("lineno"))
    _message = _norm_issue_str(
        f.get("message"), f.get("detail"), f.get("description"))
    return filepath, _line, _message
def _density_issue_of(f: dict) -> tuple[dict, str]:
    raw_rule = _norm_issue_str(f.get("rule_id"), f.get("type"))
    rule_id, severity, desc = _ap_category_mapping(raw_rule)
    filepath, _line, _msg = _normalize_density_fields(f)
    return _issue_envelope(
        rule_id, severity, _line, filepath,
        _msg if isinstance(_msg, str) and _msg else desc,
        "antipattern", 0.60), filepath
def run_density_post_processor(antipattern_findings: list[dict]) -> dict:
    issues: list[dict] = []
    counts_by_identity: dict[str, int] = {}
    display_paths: dict[str, str] = {}
    if isinstance(antipattern_findings, (list, tuple)):
        _items = antipattern_findings
    elif (isinstance(antipattern_findings, Iterable)
          and not isinstance(antipattern_findings, (str, bytes, Mapping))):
        try:
            _items = list(antipattern_findings)
        except TypeError:
            _items = ()
    else:
        if antipattern_findings is not None:
            logger.debug("[Antipattern] 密度后处理输入形态非法: %r",
                         type(antipattern_findings).__name__)
        _items = ()
    for f in _items:
        if not isinstance(f, dict):
            continue
        issue, filepath = _density_issue_of(f)
        issues.append(issue)
        if filepath:
            identity = _path_identity(filepath)
            display_paths.setdefault(identity, filepath)
            counts_by_identity[identity] = counts_by_identity.get(identity, 0) + 1
    file_violation_count = {
        display_paths[identity]: count
        for identity, count in counts_by_identity.items()
    }
    density_hotspots = _density_hotspots(file_violation_count)
    return {
        "issues": issues,
        "density_hotspots": density_hotspots,
        "total_violations": len(issues),
        "file_violation_count": file_violation_count,
    }
_DENSITY_HOTSPOT_MIN = 3
def _density_hotspots(counts: dict) -> list[dict]:
    return [{"file": _fp, "violation_count": _cnt, "density": "high"}
            for _fp, _cnt in sorted(counts.items(), key=lambda x: (-x[1], x[0]))
            if _cnt >= _DENSITY_HOTSPOT_MIN]
def _filter_dim_issues(issues,
                       is_out_of_scope) -> tuple[list, int, int]:
    malformed, candidates = split_malformed_issues(issues)
    kept, out_of_scope = _split_out_of_scope(candidates, is_out_of_scope)
    return kept, out_of_scope, malformed
def _split_out_of_scope(dicts: list, is_out_of_scope) -> tuple[list, int]:
    kept = [f for f in dicts
            if not is_out_of_scope(finding_file(f))]
    return kept, len(dicts) - len(kept)
def collect_scope_filtered_findings(
    results: dict, dim_order: Sequence[str],
    is_out_of_scope: Callable[[str], bool] = is_diagnosis_out_of_scope,
) -> tuple[list[dict], dict[str, int], int, int]:
    if not isinstance(results, dict):
        logger.warning("[Antipattern] 域过滤跳过：results 非 dict %r",
                       type(results).__name__)
        return [], {}, 0, 0
    if not callable(is_out_of_scope):
        logger.warning("[Antipattern] is_out_of_scope 非可调用，回退默认判定")
        is_out_of_scope = is_diagnosis_out_of_scope
    all_findings: list[dict] = []
    dim_counts: dict[str, int] = {}
    dropped_scope = 0
    dropped_malformed = 0
    for dim in _coerce_str_seq(dim_order):
        kept, _ds, _dm = _filter_dim_issues(
            results.get(dim, []), is_out_of_scope)
        dropped_scope += _ds
        dropped_malformed += _dm
        results[dim] = kept
        all_findings.extend(kept)
        dim_counts[dim] = len(kept)
    return all_findings, dim_counts, dropped_scope, dropped_malformed

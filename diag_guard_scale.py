from __future__ import annotations

import ast as _ast
import importlib.util
import json
import logging
import os
import subprocess
import sys
import types
from dataclasses import asdict, dataclass, field
from typing import Any, NamedTuple, Protocol

from jwsgj.diag_shared_ast_nodes import (
    FUNC_NODE_TYPES,
    definition_start_line,
    iter_class_scope_methods,
    iter_module_level_stmts,
    type_checking_body_node_ids,
)
from jwsgj.diag_shared_source_core import (
    count_lines,
    parse_py_file,
    read_source_interpreter_encoding,
    read_source_with_fingerprint,
)
from jwsgj.diag_types_normalize import (
    as_count,
    as_dict,
    is_real_number,
    strict_iterable_list,
    strip_bom,
)
from jwsgj.diag_types_vocab import (
    FIELD_TOTAL_FUNCTIONS,
    PARSE_DEGRADE_EXC,
    ROOT_SUBSYSTEM,
    GateThresholds,
)
from jwsgj.log_config import (
    log_swallowed,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import subprocess_noartifact_env
from jwsgj.runtime_scope import (
    collect_baseline_py_files,
    prune_walk_dirs,
)

logger = logging.getLogger(__name__)
__all__ = [
    'STUB_BODY_LINES_THRESHOLD',
    'ArchitectureCapacityValidator',
    'BatchQualityTrendMonitor',
    'CapacityVerdict',
    'FunctionMappingGenerator',
    'FunctionSignature',
    'GateImportVerifier',
    'GateProjectScanner',
    'collect_function_nodes',
    'count_stubs_in_nodes',
    'enhance_verify_fix_semantic',
    'is_stub_function',
    'verify_with_compile',
]
def collect_function_nodes(tree: _ast.AST) -> list:
    if not isinstance(tree, _ast.AST):
        return []
    return [node for node in walk_nodes(tree)
            if isinstance(node, FUNC_NODE_TYPES)]
def _path_arg(value):
    if isinstance(value, (str, bytes)):
        return os.fsdecode(value)
    if isinstance(value, os.PathLike):
        return os.fsdecode(os.fspath(value))
    return value
def _coerce_scan_path(value, entry: str) -> str:
    if isinstance(value, (str, bytes, os.PathLike)):
        path = os.fsdecode(os.fspath(value))
        if path:
            return path
    raise ValueError(
        f"{entry}: project_path 须为非空 str/PathLike，实际为 {value!r}")
_STUB_EXEMPT_DECORATORS = frozenset((
    "property", "abstractmethod", "overload",
))
def _stub_exempt_decorator(decorator) -> bool:
    if isinstance(decorator, _ast.Name):
        return decorator.id in _STUB_EXEMPT_DECORATORS
    if isinstance(decorator, _ast.Attribute):
        return decorator.attr in _STUB_EXEMPT_DECORATORS
    return False
def _is_stub_return_value(v) -> bool:
    if v is None or v is Ellipsis:
        return True
    if isinstance(v, bool):
        return not v
    if isinstance(v, (int, float)):
        return v == 0
    if isinstance(v, (str, bytes)):
        return len(v) == 0
    return False
def _is_not_implemented_error(stmt) -> bool:
    if not isinstance(stmt, _ast.Raise) or stmt.exc is None:
        return False
    exc = stmt.exc.func if isinstance(stmt.exc, _ast.Call) else stmt.exc
    if isinstance(exc, _ast.Name):
        return exc.id == "NotImplementedError"
    return (isinstance(exc, _ast.Attribute)
            and exc.attr == "NotImplementedError")
def _is_stub_single_stmt(stmt) -> bool:
    if isinstance(stmt, _ast.Pass):
        return True
    if isinstance(stmt, _ast.Raise):
        return _is_not_implemented_error(stmt)
    if not isinstance(stmt, _ast.Return):
        return False
    if stmt.value is None:
        return True
    return (isinstance(stmt.value, _ast.Constant)
            and _is_stub_return_value(stmt.value.value))
def is_stub_function(func_node) -> bool:
    if not isinstance(func_node, (_ast.FunctionDef, _ast.AsyncFunctionDef,
                                 _ast.ClassDef)):
        return False
    if any(_stub_exempt_decorator(d) for d in func_node.decorator_list):
        return False
    body = [s for s in func_node.body
            if not (isinstance(s, _ast.Expr) and isinstance(s.value, _ast.Constant))]
    if not body:
        return True
    return len(body) == 1 and _is_stub_single_stmt(body[0])
def count_stubs_in_nodes(nodes) -> tuple[int, int]:
    funcs = [n for n in strict_iterable_list(nodes)
             if isinstance(n, FUNC_NODE_TYPES)]
    return sum(1 for n in funcs if is_stub_function(n)), len(funcs)
class GateProjectScanner:
    def __init__(self, project_path: str, shared_cache=None):
        self.project_path = _path_arg(project_path)
        self.shared_cache = shared_cache
        self._scan_inventory_memo: list | None = None
        self._size_data_memo: dict | None = None
    def reset(self) -> None:
        self._scan_inventory_memo = None
        self._size_data_memo = None
    def _cache_channel(self, name: str):
        cache = self.shared_cache
        return getattr(cache, name, None) if cache is not None else None
    def read_source_and_tree(self, filepath: str) -> tuple[str | None, _ast.AST | None]:
        filepath = _path_arg(filepath)
        cached = self._cached_source_tree(filepath)
        if cached is not None:
            return cached
        source, _fingerprint = read_source_with_fingerprint(filepath)
        if source is None:
            logger.warning("[ConsolGate] 读取失败 %s", filepath)
            return None, None
        return source, self._parse_source_tree(source, filepath)
    def _cached_source_tree(
            self, filepath: str) -> tuple[str | None, _ast.AST | None] | None:
        getter = self._cache_channel("get_source_and_ast")
        if getter is None:
            return None
        try:
            cached = getter(filepath)
        except Exception:
            logger.warning("[ConsolGate] 共享缓存读取异常，回退直接读盘", exc_info=True)
            return None
        if isinstance(cached, (tuple, list)) and len(cached) == 2:
            source, tree = cached[0], cached[1]
            if ((source is None or isinstance(source, str))
                    and (tree is None or isinstance(tree, _ast.AST))):
                return source, tree
            logger.warning(
                "[ConsolGate] 共享缓存返回元素形态违约（期望 "
                "(str|None, AST|None)，实际 (%s, %s)），回退直接读盘",
                type(source).__name__, type(tree).__name__)
            return None
        logger.warning(
            "[ConsolGate] 共享缓存返回形态违约（期望 (source, tree) "
            "二元组，实际 %s），回退直接读盘", type(cached).__name__)
        return None
    @staticmethod
    def _parse_source_tree(source: str, filepath: str) -> _ast.AST | None:
        try:
            return _ast.parse(source, filename=filepath)
        except PARSE_DEGRADE_EXC as e:
            logger.debug("[ConsolGate] 语法解析失败 %s: %s", filepath, e)
            return None
    def _cached_function_nodes(self, tree: _ast.AST) -> list | None:
        getter = self._cache_channel("get_function_nodes")
        if getter is None:
            return None
        try:
            nodes = getter(tree)
        except Exception:
            logger.warning("[ConsolGate] 函数节点索引读取异常，回退本地枚举", exc_info=True)
            return None
        if isinstance(nodes, list):
            offender = next(
                (node for node in nodes
                 if not isinstance(node, FUNC_NODE_TYPES)), None)
            if offender is None:
                return nodes
            logger.warning(
                "[ConsolGate] 函数节点索引元素形态违约（期望函数定义节点，"
                "实际 %s），回退本地枚举", type(offender).__name__)
            return None
        if nodes is not None:
            logger.warning(
                "[ConsolGate] 函数节点索引返回形态违约（期望 list[AST]，"
                "实际 %s），回退本地枚举", type(nodes).__name__)
        return None
    def _store_function_nodes(self, tree: _ast.AST, nodes: list) -> None:
        setter = self._cache_channel("set_function_nodes")
        if setter is None:
            return
        try:
            setter(tree, nodes)
        except Exception:
            logger.warning("[ConsolGate] 函数节点索引回填失败", exc_info=True)
    def function_nodes_shared(self, tree: _ast.AST | None) -> list:
        if tree is None:
            return []
        nodes = self._cached_function_nodes(tree)
        if nodes is not None:
            return nodes
        nodes = collect_function_nodes(tree)
        self._store_function_nodes(tree, nodes)
        return nodes
    def _inventory(self) -> list:
        memo = self._scan_inventory_memo
        if memo is not None:
            return memo
        project_path = _coerce_scan_path(
            self.project_path, "GateProjectScanner")
        inventory = [self._inventory_entry(filepath)
                     for filepath in collect_baseline_py_files(project_path)]
        self._scan_inventory_memo = inventory
        return inventory
    def scan_inventory(self) -> list:
        return [(filepath, source, list(nodes))
                for filepath, source, nodes, _public_count in self._inventory()]
    def _inventory_entry(self, filepath: str) -> tuple:
        source, tree = self.read_source_and_tree(filepath)
        nodes = self.function_nodes_shared(tree)
        return (filepath, source, nodes, _public_api_function_count(tree, nodes))
    def count_project_files(self) -> int:
        return len(self._inventory())
    def count_project_lines(self) -> int:
        return self.collect_size_data()["total_lines"]
    def count_project_functions(self) -> int:
        return sum(public_count
                   for _fp, _src, _nodes, public_count in self._inventory())
    def scan_stubs(self):
        stub_count = 0
        total_count = 0
        for _fp, _src, nodes, _public_count in self._inventory():
            _s, _t = count_stubs_in_nodes(nodes)
            stub_count += _s
            total_count += _t
        return stub_count, total_count
    def collect_size_data(self) -> dict:
        result = self._size_data_memo
        if result is None:
            file_sizes = {}
            func_lines = []
            for filepath, source, nodes, _public_count in self._inventory():
                if source is None:
                    continue
                line_count = count_lines(source)
                file_sizes[filepath] = line_count
                for node in nodes:
                    end = getattr(node, 'end_lineno', None) or node.lineno
                    func_lines.append(end - definition_start_line(node) + 1)
            result = {
                "file_sizes": file_sizes,
                "func_lines": func_lines,
                "total_files": len(file_sizes),
                "total_lines": sum(file_sizes.values()),
            }
            self._size_data_memo = result
        return {
            "file_sizes": dict(result["file_sizes"]),
            "func_lines": list(result["func_lines"]),
            "total_files": result["total_files"],
            "total_lines": result["total_lines"],
        }
def _nonnegative_integral_count(value: Any) -> int | None:
    if not is_real_number(value) or value < 0:
        return None
    count = as_count(value)
    return count if count == value else None
def _safe_int_ratio(numerator: int, denominator: int) -> float:
    try:
        return numerator / denominator
    except OverflowError as _e:
        log_swallowed(__name__, _e, context='_safe_int_ratio:OverflowError')
        return sys.float_info.max
    except ZeroDivisionError as _e:
        log_swallowed(__name__, _e, context='_safe_int_ratio:ZeroDivisionError')
        return 0.0
@dataclass
class CapacityVerdict:
    passed: bool
    data: dict = field(default_factory=dict)
    errors: list = field(default_factory=list)
    warnings: list = field(default_factory=list)
    def to_dict(self) -> dict:
        return {
            "passed": self.passed,
            "data": dict(self.data),
            "errors": list(self.errors),
            "warnings": list(self.warnings),
        }
    def __repr__(self) -> str:
        status = "PASS" if self.passed else "FAIL"
        return (f"CapacityVerdict({status}, errors={len(self.errors)}, "
                f"warnings={len(self.warnings)})")
class ArchitectureCapacityValidator:
    MAX_FUNCS_PER_FILE = 30
    WARN_FUNCS_PER_FILE = 20
    @classmethod
    def _normalize_architecture_inputs(cls, old_architecture, new_architecture) -> tuple:
        old_architecture = as_dict(old_architecture)
        new_architecture = as_dict(new_architecture)
        old_raw = old_architecture.get(FIELD_TOTAL_FUNCTIONS)
        new_raw = new_architecture.get("total_files")
        old_count = _nonnegative_integral_count(old_raw)
        new_count = _nonnegative_integral_count(new_raw)
        old_total_funcs = old_count if old_count is not None else 0
        new_total_files = new_count if new_count is not None else 0
        old_measured = old_count is not None
        new_measured = new_count is not None
        old_subsystems = as_dict(old_architecture.get("subsystems"))
        new_subsystem_files = as_dict(
            new_architecture.get("target_files_by_subsystem"))
        return (old_total_funcs, new_total_files, old_subsystems,
                new_subsystem_files, old_measured, new_measured)
    @classmethod
    def _min_files_for(cls, func_count: int) -> int:
        return ((func_count + cls.MAX_FUNCS_PER_FILE - 1)
                // cls.MAX_FUNCS_PER_FILE)
    @classmethod
    def _check_global_capacity(cls, old_total_funcs: int, new_total_files: int,
                               errors: list, warnings: list, data: dict) -> None:
        capacity = new_total_files * cls.MAX_FUNCS_PER_FILE
        data["capacity"] = capacity
        data["required_capacity"] = old_total_funcs
        data["capacity_ratio"] = round(
            _safe_int_ratio(capacity, max(old_total_funcs, 1)), 2)
        if capacity < old_total_funcs:
            min_files = cls._min_files_for(old_total_funcs)
            errors.append(
                f"架构容量不足: {new_total_files}文件 x {cls.MAX_FUNCS_PER_FILE}函数/文件 = {capacity}容量 "
                f"< {old_total_funcs}个原有函数.建议最少 {min_files} 个文件.")
        elif capacity * 5 < old_total_funcs * 6:
            warnings.append(f"架构容量偏紧: {capacity}/{old_total_funcs} ({data['capacity_ratio']}x).")
    @classmethod
    def _check_subsystem_capacities(cls, old_subsystems: dict, new_subsystem_files: dict,
                                    errors: list) -> None:
        if (not new_subsystem_files
                and any(name != ROOT_SUBSYSTEM for name in old_subsystems)):
            errors.append(
                "容量校验未度量: new_architecture 缺少有效 "
                "target_files_by_subsystem")
            return
        for sub_name, sub_info in old_subsystems.items():
            if sub_name == ROOT_SUBSYSTEM:
                continue
            raw_funcs = sub_info.get("functions", 0) if isinstance(sub_info, dict) else sub_info
            sub_funcs = _nonnegative_integral_count(raw_funcs)
            if sub_funcs is None:
                errors.append(
                    f"子系统 [{sub_name}] 函数计数无效（须为非负整数，"
                    f"实际 {raw_funcs!r}）.")
                continue
            matched_names = [
                name for name in new_subsystem_files
                if name == sub_name or (
                    isinstance(name, str) and isinstance(sub_name, str)
                    and name.startswith(sub_name + "/"))
            ]
            if not matched_names:
                if sub_funcs:
                    errors.append(
                        f"子系统 [{sub_name}] 在新架构中消失（{sub_funcs}个函数无对应位置）.")
                continue
            file_counts = [
                (name, new_subsystem_files[name],
                 _nonnegative_integral_count(new_subsystem_files[name]))
                for name in matched_names
            ]
            invalid_counts = [item for item in file_counts if item[2] is None]
            if invalid_counts:
                for name, raw_files, _count in invalid_counts:
                    errors.append(
                        f"子系统 [{name}] 文件计数无效（须为非负整数，"
                        f"实际 {raw_files!r}）.")
                continue
            sub_files_new = sum(
                count for _name, _raw, count in file_counts
                if count is not None)
            if sub_files_new == 0:
                if sub_funcs:
                    errors.append(
                        f"子系统 [{sub_name}] 在新架构中无可用文件"
                        f"（{sub_funcs}个函数无对应位置，请检查文件数量/可读性）.")
                continue
            sub_capacity = sub_files_new * cls.MAX_FUNCS_PER_FILE
            if sub_capacity < sub_funcs:
                min_sub_files = cls._min_files_for(sub_funcs)
                errors.append(
                    f"子系统 [{sub_name}] 容量不足: {sub_files_new}文件 x {cls.MAX_FUNCS_PER_FILE} "
                    f"= {sub_capacity} < {sub_funcs}个函数.建议最少 {min_sub_files} 个文件.")
    @classmethod
    def validate(cls, old_architecture: dict, new_architecture: dict) -> CapacityVerdict:
        errors: list[str] = []
        warnings: list[str] = []
        data: dict = {}
        (old_total_funcs, new_total_files, old_subsystems,
         new_subsystem_files, old_measured, new_measured) = (
            cls._normalize_architecture_inputs(old_architecture, new_architecture))
        if not old_measured:
            errors.append(
                "容量校验未度量: old_architecture 缺少有效 total_functions")
        if not new_measured:
            errors.append(
                "容量校验未度量: new_architecture 缺少有效 total_files")
        data["old_measured"] = old_measured
        data["new_measured"] = new_measured
        if old_measured and new_measured:
            cls._check_global_capacity(
                old_total_funcs, new_total_files, errors, warnings, data)
            file_count = max(new_total_files, 1)
            density = _safe_int_ratio(old_total_funcs, file_count)
            data["func_density"] = round(density, 1)
            if density > cls.WARN_FUNCS_PER_FILE:
                warnings.append(
                    f"平均函数密度过高: {density:.1f}函数/文件 "
                    f"> {cls.WARN_FUNCS_PER_FILE}.")
        cls._check_subsystem_capacities(
            old_subsystems, new_subsystem_files, errors)
        return CapacityVerdict(not errors, data=data, errors=errors, warnings=warnings)
    @classmethod
    def quick_scan(cls, project_path: str) -> dict:
        project_path = cls._require_scan_path(project_path)
        total_files, total_functions, total_lines, subsystems = cls._scan_tree(
            project_path)
        return {
            "total_files": total_files,
            FIELD_TOTAL_FUNCTIONS: total_functions,
            "total_lines": total_lines,
            "subsystems": subsystems,
            "avg_functions_per_file": (
                round(_safe_int_ratio(total_functions, total_files), 2)
                if total_files else 0),
            "avg_lines_per_file": (
                round(_safe_int_ratio(total_lines, total_files), 2)
                if total_files else 0),
        }
    @classmethod
    def _scan_tree(cls, project_path: str) -> tuple[int, int, int, dict]:
        total_files = 0
        total_functions = 0
        total_lines = 0
        subsystems: dict[str, dict] = {}
        for root, file_paths in cls._group_by_dir(
                collect_baseline_py_files(project_path)).items():
            sub_name, sub_read, sub_funcs, sub_lines = cls._scan_subdir_stats(
                root, file_paths, project_path)
            total_files += sub_read
            total_functions += sub_funcs
            total_lines += sub_lines
            cls._merge_subsystem_stats(
                subsystems, sub_name, sub_read, sub_funcs, sub_lines)
        return total_files, total_functions, total_lines, subsystems
    @staticmethod
    def _group_by_dir(file_paths: list) -> dict[str, list[str]]:
        grouped: dict[str, list[str]] = {}
        for fp in file_paths:
            grouped.setdefault(os.path.dirname(fp), []).append(fp)
        return grouped
    @staticmethod
    def _merge_subsystem_stats(subsystems: dict, name: str, files: int,
                               functions: int, lines: int) -> None:
        bucket = subsystems.get(name)
        if bucket is None:
            subsystems[name] = {
                "files": files, "functions": functions, "lines": lines}
            return
        bucket["files"] += files
        bucket["functions"] += functions
        bucket["lines"] += lines
    @staticmethod
    def _require_scan_path(project_path: str) -> str:
        path = _coerce_scan_path(
            project_path, "ArchitectureCapacityValidator.quick_scan")
        if not os.path.isdir(path):
            raise ValueError(
                f"ArchitectureCapacityValidator.quick_scan: project_path "
                f"目录不存在: {path!r}")
        return path
    @classmethod
    def _scan_subdir_stats(cls, root: str, file_paths: list,
                           project_path: str) -> tuple[str, int, int, int]:
        rel_dir = os.path.relpath(root, project_path)
        sub_name = ROOT_SUBSYSTEM if rel_dir == "." else rel_dir.replace(os.sep, "/")
        sub_funcs = 0
        sub_lines = 0
        sub_read = 0
        for fp in file_paths:
            metrics = cls._py_file_metrics(fp)
            if metrics is None:
                continue
            file_lines, file_funcs = metrics
            sub_funcs += file_funcs
            sub_lines += file_lines
            sub_read += 1
        return sub_name, sub_read, sub_funcs, sub_lines
    @classmethod
    def _py_file_metrics(cls, fp: str) -> tuple[int, int] | None:
        content, tree = parse_py_file(fp, quiet=True)
        if content is None:
            logger.debug("跳过不可读或不可解码文件: %s", fp)
            return None
        if tree is None:
            logger.debug("跳过不可解析文件（口径同 extract_functions）: %s", fp)
            return None
        lines = count_lines(content)
        funcs = sum(
            1 for node in walk_nodes(tree)
            if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef,
                                 _ast.ClassDef)))
        return lines, funcs
STUB_BODY_LINES_THRESHOLD = 2
def _file_key_or_none(value: Any) -> str | None:
    return value if isinstance(value, str) and value else None
def _mapping_file_key(func, default: str | None) -> str | None:
    if isinstance(func, dict):
        return (_file_key_or_none(func.get("file_path"))
                or _file_key_or_none(func.get("file")) or default)
    fp = (_file_key_or_none(getattr(func, "file_path", None))
          or _file_key_or_none(getattr(func, "file", None)))
    return fp or default
def _coerce_body_lines(value: Any) -> float | None:
    if not is_real_number(value) or value < 0:
        return None
    return value
def _iter_valid_entries(functions: list):
    for raw in strict_iterable_list(functions):
        entry = _func_entry(raw)
        if entry is None:
            continue
        yield raw, *entry
class _FunctionScan(NamedTuple):
    index: dict[str, list]
    name_counts: dict[str, int]
    stubs: list[dict]
    valid_count: int
    stub_eligible_count: int
def _scan_functions(functions: list) -> _FunctionScan:
    index: dict[str, list] = {}
    name_counts: dict[str, int] = {}
    stubs: list[dict] = []
    valid_count = 0
    stub_eligible_count = 0
    for raw, kind, name, body, explicit_stub in _iter_valid_entries(functions):
        valid_count += 1
        index.setdefault(name, []).append(raw)
        name_counts[name] = name_counts.get(name, 0) + 1
        if kind == "class":
            continue
        stub_eligible_count += 1
        is_stub = (explicit_stub if explicit_stub is not None else
                   body is not None and body <= STUB_BODY_LINES_THRESHOLD)
        if is_stub:
            stubs.append({"name": name,
                          "file": _mapping_file_key(raw, default=None),
                          "body_lines": body})
    return _FunctionScan(index, name_counts, stubs, valid_count,
                         stub_eligible_count)
def _func_entry(func: Any) -> tuple[str, str, float | None, bool | None] | None:
    if isinstance(func, dict):
        name = func.get("name", "")
        body = func.get("body_lines")
        explicit_stub = func.get("is_stub")
        kind = func.get("kind", "function")
    elif hasattr(func, "name"):
        name = func.name
        body = getattr(func, "body_lines", None)
        explicit_stub = getattr(func, "is_stub", None)
        kind = getattr(func, "kind", "function")
    else:
        return None
    if not isinstance(name, str):
        return None
    name = name.strip()
    if not name:
        return None
    if not isinstance(explicit_stub, bool):
        explicit_stub = None
    if not isinstance(kind, str) or not kind:
        kind = "function"
    return kind, name, _coerce_body_lines(body), explicit_stub
def _node_body_lines(node) -> int:
    return node.end_lineno - node.lineno + 1 if node.end_lineno else 0
def _is_public_name(name: str) -> bool:
    return not name.startswith("_")
def _definition_scope_is_public(node: _ast.AST, parents: dict) -> bool:
    parent = parents.get(node)
    while parent is not None:
        if isinstance(parent, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
            return False
        if (isinstance(parent, _ast.ClassDef)
                and not _is_public_name(parent.name)):
            return False
        parent = parents.get(parent)
    return True
def _public_api_function_count(tree: _ast.AST | None, nodes: list) -> int:
    if tree is None:
        return 0
    parents = {
        child: parent
        for parent in walk_nodes(tree)
        for child in _ast.iter_child_nodes(parent)
    }
    count = 0
    for node in nodes:
        if not _definition_scope_is_public(node, parents):
            continue
        if _is_public_name(node.name):
            count += 1
            continue
        parent = parents.get(node)
        while parent is not None and not isinstance(
                parent, (_ast.FunctionDef, _ast.AsyncFunctionDef, _ast.ClassDef)):
            parent = parents.get(parent)
        if node.name == "__init__" and isinstance(parent, _ast.ClassDef):
            count += 1
    return count
def _collect_arg_names(args: _ast.arguments) -> list[str]:
    names = [a.arg for a in getattr(args, "posonlyargs", [])]
    names += [a.arg for a in args.args]
    if args.vararg:
        names.append(args.vararg.arg)
    names += [a.arg for a in args.kwonlyargs]
    if args.kwarg:
        names.append(args.kwarg.arg)
    return names
@dataclass
class FunctionSignature:
    name: str
    file_path: str
    line: int
    kind: str = "function"
    is_public: bool = False
    parameters: list = field(default_factory=list)
    body_lines: int = 0
    subsystem: str = ""
    is_stub: bool | None = None
    def to_dict(self) -> dict:
        return asdict(self)
def _match_old_new(old_index: dict[str, list],
                   new_index: dict[str, list]) -> tuple[list, list]:
    matched, missing = [], []
    for name, old_list in old_index.items():
        new_list = new_index.get(name, [])
        if new_list:
            matched.append({"old": name, "new": name,
                            "old_count": len(old_list), "new_count": len(new_list)})
        if len(new_list) < len(old_list):
            files = {fp for fp in (_mapping_file_key(f, default=None)
                                   for f in old_list) if fp}
            missing.append({"name": name,
                            "count": len(old_list) - len(new_list),
                            "files": sorted(files)})
    return matched, missing
def _mapping_coverage(old_index: dict[str, list],
                      new_index: dict[str, list]) -> float:
    if not old_index:
        return 1.0
    old_total = sum(len(entries) for entries in old_index.values())
    matched_total = sum(
        min(len(entries), len(new_index.get(name, [])))
        for name, entries in old_index.items()
    )
    return matched_total / old_total
class FunctionMappingGenerator:
    def __init__(self, project_path: str) -> None:
        path = _coerce_scan_path(project_path, "FunctionMappingGenerator")
        self.project_path = os.path.abspath(path)
        self.functions: list[FunctionSignature] = []
        self.file_line_counts: dict[str, int] = {}
    def extract_functions(self, include_private: bool = True) -> list[dict]:
        self.functions = []
        self.file_line_counts = {}
        for fp in collect_baseline_py_files(self.project_path):
            rel = os.path.relpath(fp, self.project_path)
            _source, tree = parse_py_file(fp, quiet=True)
            if tree is None:
                logger.warning("源文件读取或解析失败，跳过函数提取: %s", rel)
                continue
            self.file_line_counts[rel] = count_lines(_source)
            self._extract_from_tree(tree, rel)
        self._assign_subsystems()
        if not include_private:
            self.functions = [f for f in self.functions if f.is_public]
        return [f.to_dict() for f in self.functions]
    def _assign_subsystems(self) -> None:
        for f in self.functions:
            parts = f.file_path.replace("\\", "/").split("/")
            f.subsystem = "/".join(parts[:-1]) if len(parts) > 1 else ROOT_SUBSYSTEM
    def _extract_from_tree(self, tree: _ast.Module, rel_path: str) -> None:
        handled_method_ids: set[int] = set()
        parents = {
            child: parent
            for parent in walk_nodes(tree)
            for child in _ast.iter_child_nodes(parent)
        }
        for node in walk_nodes(tree):
            if isinstance(node, (_ast.FunctionDef, _ast.AsyncFunctionDef)):
                if id(node) in handled_method_ids:
                    continue
                self._emit_function_node(
                    node, rel_path, _definition_scope_is_public(node, parents))
            elif isinstance(node, _ast.ClassDef):
                self._emit_class_node(
                    node, rel_path, handled_method_ids,
                    _definition_scope_is_public(node, parents))
    def _emit_function_node(self, node, rel_path: str,
                            scope_public: bool) -> None:
        self.functions.append(FunctionSignature(
            name=node.name, file_path=rel_path, line=node.lineno,
            kind="function",
            is_public=scope_public and _is_public_name(node.name),
            parameters=_collect_arg_names(node.args),
            body_lines=_node_body_lines(node),
            is_stub=is_stub_function(node)))
    def _emit_class_node(self, node: _ast.ClassDef, rel_path: str,
                         handled_method_ids: set[int],
                         scope_public: bool) -> None:
        class_public = scope_public and _is_public_name(node.name)
        self.functions.append(FunctionSignature(
            name=node.name, file_path=rel_path, line=node.lineno,
            kind="class", is_public=class_public,
            body_lines=_node_body_lines(node),
            is_stub=is_stub_function(node)))
        for item in iter_class_scope_methods(node):
            handled_method_ids.add(id(item))
            self.functions.append(FunctionSignature(
                name=f"{node.name}.{item.name}", file_path=rel_path,
                line=item.lineno, kind="method",
                is_public=(class_public
                           and (_is_public_name(item.name)
                                or item.name == "__init__")),
                parameters=_collect_arg_names(item.args),
                body_lines=_node_body_lines(item),
                is_stub=is_stub_function(item)))
    def generate_mapping(self, old_functions: list, new_functions: list | None = None) -> dict:
        new_funcs = (self.extract_functions() if new_functions is None
                     else new_functions)
        new_scan = _scan_functions(new_funcs)
        old_scan = _scan_functions(old_functions)
        matched, missing = _match_old_new(old_scan.index, new_scan.index)
        stubs = new_scan.stubs
        stub_denominator = new_scan.stub_eligible_count
        coverage = _mapping_coverage(old_scan.index, new_scan.index)
        matched_count = sum(
            min(item["old_count"], item["new_count"]) for item in matched)
        missing_count = sum(item["count"] for item in missing)
        return {
            "coverage_rate": coverage,
            "total_old": old_scan.valid_count,
            "total_new": new_scan.valid_count,
            "matched_count": matched_count,
            "missing_count": missing_count,
            "stub_count": len(stubs),
            "stub_rate": (len(stubs) / stub_denominator
                          if stub_denominator else 0.0),
            "matched_functions": matched,
            "missing_functions": missing,
            "stub_functions": stubs,
        }
    def print_missing_report(self, mapping: dict, max_show: int = 30) -> str:
        lines = [
            f"\n{'='*60}",
            f"  函数映射报告: {mapping['coverage_rate']*100:.1f}% 覆盖",
            f"  旧:{mapping['total_old']} | 新:{mapping['total_new']} | 匹配:{mapping['matched_count']} | 缺失:{mapping['missing_count']}",
            f"  空桩率: {mapping['stub_rate']*100:.1f}% ({mapping['stub_count']}个)",
        ]
        if mapping["missing_count"] > 0:
            lines.append(f"\n  缺失函数 (前{max_show}个):")
            for m in mapping["missing_functions"][:max_show]:
                lines.append(f"    - {m['name']} ({', '.join(m['files'][:2])})")
        lines.append(f"{'='*60}")
        return "\n".join(lines)
class BatchQualityTrendMonitor:
    def analyze(self, old_functions: list, new_functions: list) -> dict:
        new_scan = _scan_functions(new_functions)
        old_scan = _scan_functions(old_functions)
        new_counts = new_scan.name_counts
        stub_count = len(new_scan.stubs)
        stub_denominator = new_scan.stub_eligible_count
        stub_rate = (stub_count / stub_denominator
                     if stub_denominator else 0.0)
        old_counts = old_scan.name_counts
        lost = [name for name, count in old_counts.items()
                if new_counts.get(name, 0) < count]
        lost_count = sum(
            max(0, count - new_counts.get(name, 0))
            for name, count in old_counts.items()
        )
        if old_counts:
            quality_score = max(0.0, 1.0 - stub_rate - lost_count * 0.01)
        elif new_counts:
            quality_score = 1.0 - stub_rate
        else:
            quality_score = 0.0
        return {
            "stub_rate": stub_rate,
            "subsystem_loss": sorted(lost)[:20],
            "quality_score": round(quality_score, 3),
        }
def _verification_memo_key(project_path: str, targets: list) -> tuple:
    return (os.path.abspath(project_path), tuple(targets))
def _evict_target_module_family(mod_name: str) -> None:
    root_name = mod_name.partition(".")[0]
    if not root_name:
        return
    for name in tuple(sys.modules):
        if name == root_name or name.startswith(root_name + "."):
            sys.modules.pop(name, None)
def _coerce_verification_targets(targets):
    if targets is None:
        return None
    if isinstance(targets, (str, bytes, bytearray, dict)):
        raise ValueError(
            "targets 须为 (module_name, source_file) 二元组的可迭代对象，"
            f"实际为 {type(targets).__name__}")
    try:
        return list(targets)
    except TypeError as exc:
        raise ValueError(
            "targets 须为 (module_name, source_file) 二元组的可迭代对象，"
            f"实际为 {type(targets).__name__}") from exc
def _qualified_module_name(pkg_name: str, mod_path: str) -> str:
    if not pkg_name:
        return mod_path
    if mod_path == pkg_name or mod_path.startswith(pkg_name + "."):
        return mod_path
    return f"{pkg_name}.{mod_path}"
def _runtime_module_map_imports(
        parent_mod: types.ModuleType, parent: str,
        map_names: tuple[str, ...]) -> list[str]:
    imports: list[str] = []
    parent_attrs = vars(parent_mod)
    for map_name in map_names:
        if map_name not in parent_attrs:
            continue
        module_map = parent_attrs[map_name]
        if not isinstance(module_map, dict) or any(
                not isinstance(export_name, str) or not isinstance(mod_path, str)
                for export_name, mod_path in module_map.items()):
            raise TypeError(f"{map_name} 须为 dict[str, str]")
        imports.extend(_qualified_module_name(parent, mod_path)
                       for mod_path in module_map.values())
    return imports
class _SourceTreeReader(Protocol):
    def read_source_and_tree(self, filepath: str) -> tuple[str | None, _ast.AST | None]:
        ...
def _apply_all_insert(names: list, call: _ast.Call) -> list:
    name = _method_str_arg(call, 1)
    index = _method_int_arg(call, 0)
    if name is None or index is None:
        return names
    pos = index if index >= 0 else len(names) + index
    pos = max(0, min(pos, len(names)))
    return names[:pos] + [name] + names[pos:]
def _apply_all_remove(names: list, call: _ast.Call) -> list:
    name = _method_str_arg(call, 0)
    if name is None:
        return names
    for pos, existing in enumerate(names):
        if existing == name:
            return names[:pos] + names[pos + 1:]
    return names
def _apply_all_pop(names: list, call: _ast.Call) -> list:
    if not names:
        return names
    index = _method_int_arg(call, 0) if call.args else -1
    if index is None:
        return names
    pos = index if index >= 0 else len(names) + index
    if not 0 <= pos < len(names):
        return names
    return names[:pos] + names[pos + 1:]
def _apply_all_method(names: list, attr: str, call: _ast.Call) -> list:
    if attr == "append":
        name = _method_str_arg(call, 0)
        return names + [name] if name is not None else names
    if attr == "extend":
        added = (_eval_export_names(call.args[0])
                 if call.args else None)
        return names + added[1] if added is not None else names
    if attr == "insert":
        return _apply_all_insert(names, call)
    if attr == "remove":
        return _apply_all_remove(names, call)
    if attr == "pop":
        return _apply_all_pop(names, call)
    if attr == "clear" and not call.args:
        return []
    if attr in ("sort", "reverse"):
        return names
    return names
def _method_str_arg(call: _ast.Call, index: int) -> str | None:
    if len(call.args) <= index:
        return None
    arg = call.args[index]
    if isinstance(arg, _ast.Constant):
        if isinstance(arg.value, str):
            return arg.value
        raise ValueError(
            f"__all__ 第 {arg.lineno} 行使用了非字符串导出名: {arg.value!r}")
    return None
def _method_int_arg(call: _ast.Call, index: int) -> int | None:
    if len(call.args) <= index:
        return None
    arg = call.args[index]
    if (isinstance(arg, _ast.Constant)
            and isinstance(arg.value, int)
            and not isinstance(arg.value, bool)):
        return arg.value
    if (isinstance(arg, _ast.UnaryOp)
            and isinstance(arg.op, (_ast.USub, _ast.UAdd))):
        operand = arg.operand
        if (isinstance(operand, _ast.Constant)
                and isinstance(operand.value, int)
                and not isinstance(operand.value, bool)):
            return (-operand.value if isinstance(arg.op, _ast.USub)
                    else operand.value)
    return None
def _eval_export_names(value: _ast.AST, depth: int = 0):
    if depth > 20:
        return None
    container = _eval_export_container(value)
    if container is not None:
        return container
    if isinstance(value, _ast.BinOp) and isinstance(value.op, _ast.Add):
        left = _eval_export_names(value.left, depth + 1)
        right = _eval_export_names(value.right, depth + 1)
        if (left is not None and right is not None
                and left[0] == right[0]):
            return left[0], left[1] + right[1]
    return None
def _eval_export_container(value: _ast.AST):
    if not isinstance(value, (_ast.List, _ast.Tuple)):
        return None
    if any(not isinstance(elt, _ast.Constant) for elt in value.elts):
        return None
    invalid = next(
        (elt for elt in value.elts if not isinstance(elt.value, str)), None)
    if invalid is not None:
        raise ValueError(
            f"__all__ 第 {invalid.lineno} 行包含非字符串导出名: "
            f"{invalid.value!r}")
    kind = "list" if isinstance(value, _ast.List) else "tuple"
    return kind, [elt.value for elt in value.elts]
def _identifier_tokens(name: str) -> list[str]:
    tokens: list[str] = []
    current: list[str] = []
    for char in str(name).lower():
        if "a" <= char <= "z" or "0" <= char <= "9":
            current.append(char)
        elif current:
            tokens.append("".join(current))
            current = []
    if current:
        tokens.append("".join(current))
    return tokens
class GateImportVerifier:
    @staticmethod
    def _parse_subproc_failed(stdout: str | None) -> list | None:
        text = (stdout or "").strip()
        if not text:
            return None
        parsed = None
        try:
            parsed = json.loads(text)
        except ValueError as _e:
            log_swallowed(__name__, _e, context='GateImportVerifier._parse_subproc_failed:ValueError')
            lines = [ln for ln in text.splitlines() if ln.strip()]
            if lines:
                parsed = json.loads(lines[-1])
        if not isinstance(parsed, list):
            raise ValueError(
                f"子进程验证输出不是合法的失败名单 JSON 数组: {text!r:.120}")
        return parsed
    _SUBPROC_VERIFIER_SRC = (
        "import sys, json, importlib\n"
        "failed = []\n"
        "known_modules = dict(sys.modules)\n"
        "path_snapshot = list(sys.path)\n"
        "targets = json.load(sys.stdin)\n"
        "proj_roots = {t[0].split('.')[0] for t in targets}\n"
        "for target in targets:\n"
        "    mod, force_import = target[:2]\n"
        "    preferred_root = target[2] if len(target) > 2 else ''\n"
        "    runtime_export_only = target[3] if len(target) > 3 else False\n"
        "    runtime_module_map = target[4] if len(target) > 4 else None\n"
        "    runtime_export_names = target[5] if len(target) > 5 else None\n"
        "    for name in set(sys.modules) - set(known_modules):\n"
        "        if name.split('.')[0] in proj_roots:\n"
        "            sys.modules.pop(name, None)\n"
        "    for name, module in known_modules.items():\n"
        "        if sys.modules.get(name) is not module:\n"
        "            sys.modules[name] = module\n"
        "    sys.path[:] = path_snapshot\n"
        "    if preferred_root:\n"
        "        sys.path.insert(0, preferred_root)\n"
        "    root_name = mod.partition('.')[0]\n"
        "    for name in tuple(sys.modules):\n"
        "        if name == root_name or name.startswith(root_name + '.'):\n"
        "            sys.modules.pop(name, None)\n"
        "    importlib.invalidate_caches()\n"
        "    try:\n"
        "        parts = mod.rsplit('.', 1)\n"
        "        if len(parts) == 2 and not force_import:\n"
        "            parent, child = parts\n"
        "            parent_mod = importlib.import_module(parent)\n"
        "            if not hasattr(parent_mod, child):\n"
        "                importlib.import_module(mod)\n"
        "        else:\n"
        "            importlib.import_module(mod)\n"
        "        if runtime_export_only:\n"
        "            parent = (runtime_export_only if isinstance(runtime_export_only, str)\n"
        "                      else (mod.rsplit('.', 1)[0] if '.' in mod else mod))\n"
        "            parent_mod = importlib.import_module(parent)\n"
        "            export_names = getattr(parent_mod, '__all__', ())\n"
        "            if runtime_export_names:\n"
        "                export_names = [n for n in export_names\n"
        "                                if n in runtime_export_names]\n"
        "            for export_name in export_names:\n"
        "                if not hasattr(parent_mod, export_name):\n"
        "                    mod = f'{parent}.{export_name}'\n"
        "                    importlib.import_module(mod)\n"
        "        if runtime_module_map:\n"
        "            parent, map_names = runtime_module_map\n"
        "            parent_mod = importlib.import_module(parent)\n"
        "            parent_attrs = vars(parent_mod)\n"
        "            for map_name in map_names:\n"
        "                if map_name not in parent_attrs:\n"
        "                    continue\n"
        "                module_map = parent_attrs[map_name]\n"
        "                if not isinstance(module_map, dict):\n"
        "                    raise TypeError(f'{map_name} 须为 dict[str, str]')\n"
        "                for export_name, mod_path in module_map.items():\n"
        "                    if not isinstance(export_name, str) or not isinstance(mod_path, str):\n"
        "                        raise TypeError(f'{map_name} 须为 dict[str, str]')\n"
        "                    mod = (mod_path if (not parent or mod_path == parent or\n"
        "                                      mod_path.startswith(parent + '.')) else\n"
        "                           f'{parent}.{mod_path}')\n"
        "                    importlib.import_module(mod)\n"
        "    except (Exception, SystemExit) as e:\n"
        "        failed.append(f'{mod} ({type(e).__name__}: {e})')\n"
        "json.dump(failed, sys.stdout)\n"
    )
    def __init__(self, project_path: str, thresholds, scanner: _SourceTreeReader):
        self.project_path = _path_arg(project_path)
        self.thresholds = thresholds
        self._scanner = scanner
        self._import_targets_memo: tuple[str, list] | None = None
        self._import_verify_memo: tuple | None = None
        self._subproc_verify_memo: tuple | None = None
        self._runtime_export_targets: dict[tuple[str, str], str] = {}
        # 每个 target 只对自身负责的导出名做 __all__ 回退校验；缺省（根
        # target）校验全部导出名，避免每个 target 重复认领兄弟导出的失败。
        self._runtime_export_names: dict[tuple[str, str], tuple[str, ...]] = {}
        self._runtime_module_map_targets: dict[
            tuple[str, str], tuple[str, tuple[str, ...]]] = {}
    def reset(self) -> None:
        self._import_targets_memo = None
        self._import_verify_memo = None
        self._subproc_verify_memo = None
        self._runtime_export_targets.clear()
        self._runtime_export_names.clear()
        self._runtime_module_map_targets.clear()
    @staticmethod
    def _package_root_candidates(project_path: str) -> list[str]:
        proj = os.path.abspath(project_path)
        candidates: list[str] = []
        for cur, dirs, files in os.walk(proj):
            rel = os.path.relpath(cur, proj)
            depth = 0 if rel == "." else len(rel.split(os.sep))
            if depth > 2:
                dirs[:] = []
                continue
            if cur != proj and "__init__.py" in files:
                candidates.append(cur)
            prune_walk_dirs(dirs, root_dir=proj)
        return candidates
    def detect_import_layout(
            self, project_path: str) -> tuple[str, str, str, str]:
        project_path = _coerce_scan_path(project_path, "GateImportVerifier")
        proj = os.path.abspath(project_path)
        init_at_root = os.path.join(proj, "__init__.py")
        if os.path.isfile(init_at_root):
            import_root, package_name, _in_package = _module_load_plan(
                init_at_root)
            return proj, import_root, package_name, init_at_root
        candidates = self._package_root_candidates(proj)
        if candidates:
            outer = self._outer_package_roots(candidates)
            parents = {os.path.dirname(path) for path in outer}
            if len(outer) > 1 and len(parents) == 1:
                import_root = parents.pop()
                return import_root, import_root, "", ""
            best = self._select_package_root(candidates)
            return (best, os.path.dirname(best), os.path.basename(best),
                    os.path.join(best, "__init__.py"))
        return proj, proj, "", ""
    @staticmethod
    def _outer_package_roots(candidates: list[str]) -> list[str]:
        return [
            path for path in candidates
            if not any(
                path != other
                and os.path.commonpath((path, other)) == other
                for other in candidates)
        ]
    def _detect_import_layouts(
            self, project_path: str) -> list[tuple[str, str, str, str]]:
        project_path = _coerce_scan_path(project_path, "GateImportVerifier")
        proj = os.path.abspath(project_path)
        if os.path.isfile(os.path.join(proj, "__init__.py")):
            return [self.detect_import_layout(proj)]
        candidates = self._package_root_candidates(proj)
        outer = self._outer_package_roots(candidates)
        if len(outer) > 1:
            return [
                (path, os.path.dirname(path), os.path.basename(path),
                 os.path.join(path, "__init__.py"))
                for path in sorted(outer)
            ]
        return [self.detect_import_layout(proj)]
    def _select_package_root(self, candidates: list[str]) -> str:
        return min(candidates, key=lambda path: (
            -len(collect_baseline_py_files(path)), path.count(os.sep), path))
    def _resolve_init_path(self, project_path: str,
                           init_path: str | None) -> str:
        if init_path:
            return init_path
        detected = self.detect_import_layout(project_path)[3]
        return detected or os.path.join(project_path, "__init__.py")
    def _read_init_tree(self, project_path: str,
                        init_path: str | None) -> _ast.AST | None:
        init_path = self._resolve_init_path(project_path, init_path)
        if not os.path.exists(init_path):
            return None
        _source, tree = self._scanner.read_source_and_tree(init_path)
        return tree
    def parse_init_all_names(self, project_path: str,
                             init_path: str | None = None,
                             *, _with_runtime_state: bool = False
                             ) -> list | tuple[list, bool]:
        tree = self._read_init_tree(project_path, init_path)
        if tree is None:
            return ([], False) if _with_runtime_state else []
        names: list = []
        runtime_required = False
        for kind, payload in self._iter_all_events(tree):
            if kind == "runtime":
                runtime_required = True
                continue
            if kind == "method":
                runtime_required = True
                names = _apply_all_method(names, *payload)
                continue
            value, is_aug = payload
            evaluated = _eval_export_names(value)
            if evaluated is None:
                runtime_required = True
                logger.warning(
                    "[ConsolGate] __all__ 赋值右侧不可静态求值（%s），"
                    "静态名单跳过该语句，改由运行时导出验证",
                    type(value).__name__)
                if not is_aug:
                    names = []
                continue
            names = names + evaluated[1] if is_aug else evaluated[1]
        return ((names, runtime_required) if _with_runtime_state
                else names)
    @classmethod
    def _iter_all_events(cls, tree: _ast.AST):
        events: list[tuple[int, int, str, tuple]] = []
        non_runtime = type_checking_body_node_ids(tree)
        module_body_ids = {id(stmt) for stmt in tree.body}
        for node in iter_module_level_stmts(tree):
            if id(node) in non_runtime:
                continue
            parts = cls._assignment_parts(node)
            if (parts is not None
                    and any(isinstance(t, _ast.Name) and t.id == "__all__"
                            for t in parts[0])):
                events.append((node.lineno, node.col_offset, "assign",
                               (parts[1], parts[2])))
                if id(node) not in module_body_ids:
                    events.append((node.lineno, node.col_offset,
                                   "runtime", ()))
                continue
            method = cls._all_method_call(node)
            if method is not None:
                events.append((node.lineno, node.col_offset, "method", method))
                if id(node) not in module_body_ids:
                    events.append((node.lineno, node.col_offset,
                                   "runtime", ()))
        events.sort(key=lambda item: (item[0], item[1]))
        return [(kind, payload) for _ln, _col, kind, payload in events]
    @staticmethod
    def _all_method_call(node: _ast.AST):
        if not isinstance(node, _ast.Expr) or not isinstance(node.value, _ast.Call):
            return None
        call = node.value
        func = call.func
        if not (isinstance(func, _ast.Attribute)
                and isinstance(func.value, _ast.Name)
                and func.value.id == "__all__"):
            return None
        return func.attr, call
    def parse_init_module_map(
            self, project_path: str, init_path: str | None = None, *,
            _with_runtime_state: bool = False) -> dict | tuple[dict, list[str]]:
        tree = self._read_init_tree(project_path, init_path)
        if tree is None:
            return ({}, []) if _with_runtime_state else {}
        events = list(self._iter_var_assignments(
            tree, self._is_lazy_module_map_var))
        # 下标赋值/方法调用等原地突变不是整体赋值，_iter_var_assignments
        # 看不到；若仍按静态映射信任，会漏验新增或被覆盖的导出。
        runtime_names = self._module_level_mutated_names(
            tree, self._is_lazy_module_map_var)
        runtime_names.update(
            name
            for value, _is_aug, names, nested in events
            if nested or self._static_str_dict_entries(value) is None
            for name in names
        )
        module_map: dict = {}
        for value, is_aug, names, _nested in events:
            if any(name in runtime_names for name in names):
                continue
            entries = self._static_str_dict_entries(value)
            if entries is None:
                if not is_aug:
                    module_map = {}
                continue
            module_map = {**module_map, **entries} if is_aug else entries
        return ((module_map, sorted(runtime_names))
                if _with_runtime_state else module_map)
    @staticmethod
    def _is_lazy_module_map_var(var_name: str) -> bool:
        tokens = set(_identifier_tokens(var_name))
        if "lazy" in tokens:
            return True
        if not var_name.isupper():
            return False
        return bool(tokens & {"module", "import"}) and "map" in tokens
    @staticmethod
    def _static_str_dict_entries(value: _ast.AST) -> dict | None:
        if not isinstance(value, _ast.Dict):
            return None
        entries = {}
        for key, val in zip(value.keys, value.values, strict=False):
            if not (isinstance(key, _ast.Constant) and isinstance(key.value, str)
                    and isinstance(val, _ast.Constant)
                    and isinstance(val.value, str)):
                return None
            entries[key.value] = val.value
        return entries
    @staticmethod
    def _iter_var_assignments(tree: _ast.AST, var_name):
        matcher = (var_name if callable(var_name)
                   else lambda name: name == var_name)
        found: list[tuple] = []
        non_runtime = type_checking_body_node_ids(tree)
        module_body_ids = {id(stmt) for stmt in tree.body}
        for node in iter_module_level_stmts(tree):
            if id(node) in non_runtime:
                continue
            parts = GateImportVerifier._assignment_parts(node)
            if parts is None:
                continue
            targets, value, is_aug = parts
            names = tuple(t.id for t in targets
                          if isinstance(t, _ast.Name) and matcher(t.id))
            if names:
                found.append((node.lineno, node.col_offset, value, is_aug,
                              names, id(node) not in module_body_ids))
        found.sort(key=lambda item: (item[0], item[1]))
        for _ln, _col, value, is_aug, names, nested in found:
            yield value, is_aug, names, nested
    @staticmethod
    def _module_level_mutated_names(tree: _ast.AST, var_name) -> set[str]:
        """返回模块层级被原地突变的映射变量名。

        ``_MAP["k"] = "mod"``、``del _MAP["k"]``、``_MAP.update({...})``
        改变映射内容却不是整体赋值。与 ``__all__`` 的 ``_all_method_call``
        口径一致：任何方法调用都按运行时处理（宁可多验，不可漏验）。
        遍历范围与 ``_iter_var_assignments`` 相同：模块层级语句、
        跳过 TYPE_CHECKING 守卫下的非运行时分支。
        """
        matcher = (var_name if callable(var_name)
                   else lambda name: name == var_name)
        non_runtime = type_checking_body_node_ids(tree)
        mutated: set[str] = set()
        for node in iter_module_level_stmts(tree):
            if id(node) in non_runtime:
                continue
            targets: tuple = ()
            if isinstance(node, _ast.Assign):
                targets = tuple(node.targets)
            elif isinstance(node, (_ast.AnnAssign, _ast.AugAssign)):
                targets = (node.target,)
            elif isinstance(node, _ast.Delete):
                targets = tuple(node.targets)
            for target in targets:
                if (isinstance(target, _ast.Subscript)
                        and isinstance(target.value, _ast.Name)
                        and matcher(target.value.id)):
                    mutated.add(target.value.id)
            value = getattr(node, "value", None)
            if (isinstance(node, _ast.Expr) and isinstance(value, _ast.Call)
                    and isinstance(value.func, _ast.Attribute)
                    and isinstance(value.func.value, _ast.Name)
                    and matcher(value.func.value.id)):
                mutated.add(value.func.value.id)
        return mutated
    @staticmethod
    def _assignment_parts(node: _ast.AST):
        if isinstance(node, _ast.Assign):
            return node.targets, node.value, False
        if isinstance(node, _ast.AnnAssign) and node.value is not None:
            return [node.target], node.value, False
        if isinstance(node, _ast.AugAssign):
            return [node.target], node.value, True
        return None
    def fallback_scan_modules(self, project_path: str) -> dict:
        module_map = {}
        _seen_short: set = set()
        for fp in collect_baseline_py_files(project_path):
            f = os.path.basename(fp)
            rel_path = os.path.relpath(fp, project_path)
            if f == '__init__.py':
                if rel_path == '__init__.py':
                    continue
                dotted = os.path.dirname(rel_path).replace(os.sep, '.')
                previous = module_map.get(dotted)
                if previous is not None and previous != dotted:
                    module_map[previous] = previous
                module_map[dotted] = dotted
                continue
            mod_name = f[:-3]
            dotted = rel_path[:-3].replace(os.sep, '.')
            if mod_name in _seen_short:
                previous = module_map.pop(mod_name, None)
                if previous is not None:
                    module_map[previous] = previous
                module_map[dotted] = dotted
            else:
                _seen_short.add(mod_name)
                previous = module_map.get(mod_name)
                if previous is None:
                    module_map[mod_name] = dotted
                else:
                    module_map[dotted] = dotted
        return module_map
    def collect_import_targets(self, project_path: str) -> list:
        memo_key = os.path.abspath(project_path)
        memo = self._import_targets_memo
        if memo is not None and memo[0] == memo_key:
            return list(memo[1])
        targets: list = []
        covered: set[tuple[str, str]] = set()
        for module_base, _path_root, prefix, init_path in (
                self._detect_import_layouts(project_path)):
            all_names, runtime_all = (
                self.parse_init_all_names(
                    project_path, init_path, _with_runtime_state=True)
                if prefix else ([], False))
            declared, runtime_map_names = (
                self.parse_init_module_map(
                    project_path, init_path, _with_runtime_state=True)
                if prefix else ({}, []))
            fallback = self.fallback_scan_modules(module_base)
            target_map = {**fallback, **declared}
            layout_targets = self._build_import_targets(
                module_base, prefix, init_path,
                [] if runtime_all else all_names, target_map)
            # value = (父包名, 本 target 负责的导出名)；导出名为空表示
            # 校验全部 __all__（仅 __all__ 不可静态解析的根 target）。
            runtime_export_candidates: dict[
                tuple[str, str], tuple[str, list[str]]] = {}
            if runtime_all:
                root_target = (prefix, init_path)
                if root_target not in layout_targets:
                    layout_targets.append(root_target)
                runtime_export_candidates[root_target] = (prefix, [])
            else:
                for name in all_names:
                    mod_path = target_map.get(name, name)
                    full_mod = _qualified_module_name(prefix, mod_path)
                    source_file = (
                        init_path if name not in target_map else
                        self._module_source_file(module_base, prefix, full_mod))
                    runtime_export_candidates.setdefault(
                        (full_mod, source_file), (prefix, []))[1].append(name)
            runtime_module_map_candidates = {}
            if runtime_map_names:
                root_target = (prefix, init_path)
                if root_target not in layout_targets:
                    layout_targets.append(root_target)
                runtime_module_map_candidates[root_target] = (
                    prefix, tuple(runtime_map_names))
            if not layout_targets and prefix:
                layout_targets = [(prefix, init_path)]
            for target in layout_targets:
                if target in runtime_export_candidates:
                    _parent, _export_names = runtime_export_candidates[target]
                    self._runtime_export_targets[target] = _parent
                    if _export_names:
                        self._runtime_export_names[target] = tuple(
                            _export_names)
                if target in runtime_module_map_candidates:
                    self._runtime_module_map_targets[target] = (
                        runtime_module_map_candidates[target])
                if target not in covered:
                    targets.append(target)
                    covered.add(target)
            for mod_path in fallback.values():
                full_mod = _qualified_module_name(prefix, mod_path)
                target = (
                    full_mod,
                    self._module_source_file(module_base, prefix, full_mod))
                if target in covered:
                    continue
                targets.append(target)
                covered.add(target)
        self._import_targets_memo = (memo_key, targets)
        return list(targets)
    @classmethod
    def _build_import_targets(cls, module_base: str, pkg_name: str,
                              init_path: str, all_names: list,
                              target_map: dict) -> list:
        targets: dict[str, str] = {}
        for name in all_names:
            mod_path = target_map.get(name)
            if mod_path is None:
                targets.setdefault(
                    _qualified_module_name(pkg_name, name), init_path)
                continue
            full_mod = _qualified_module_name(pkg_name, mod_path)
            targets.setdefault(
                full_mod,
                cls._module_source_file(module_base, pkg_name, full_mod))
        for mod_path in target_map.values():
            full_mod = _qualified_module_name(pkg_name, mod_path)
            targets.setdefault(
                full_mod,
                cls._module_source_file(module_base, pkg_name, full_mod))
        return list(targets.items())
    @staticmethod
    def _module_relative_name(prefix: str, mod_name: str) -> str | None:
        if not prefix:
            return mod_name
        if mod_name == prefix:
            return ""
        if mod_name.startswith(prefix + "."):
            return mod_name[len(prefix) + 1:]
        return None
    @classmethod
    def _module_source_file(cls, module_base: str, prefix: str,
                            mod_name: str) -> str:
        rel = cls._module_relative_name(prefix, mod_name)
        if rel is None:
            return ""
        rel_path = rel.replace(".", os.sep)
        if not rel_path:
            return os.path.join(module_base, "__init__.py")
        module_file = os.path.join(module_base, rel_path + ".py")
        if os.path.isfile(module_file):
            return module_file
        package_init = os.path.join(module_base, rel_path, "__init__.py")
        if os.path.isfile(package_init):
            return package_init
        return module_file
    @classmethod
    def _target_is_real_module(cls, module_base: str, prefix: str,
                               mod_name: str) -> bool:
        rel = cls._module_relative_name(prefix, mod_name)
        if rel is None:
            return False
        if not rel:
            return os.path.isdir(module_base)
        rel_path = rel.replace(".", os.sep)
        return (os.path.isfile(os.path.join(module_base, rel_path + ".py"))
                or os.path.isdir(os.path.join(module_base, rel_path)))
    @staticmethod
    def _target_layout(layouts: list, mod_name: str,
                       source_file: str) -> tuple:
        matches = [
            layout for layout in layouts
            if layout[2] and (mod_name == layout[2]
                              or mod_name.startswith(layout[2] + "."))
        ]
        if len(matches) > 1 and source_file:
            source = _path_arg(source_file)
            if isinstance(source, str):
                source = os.path.abspath(source)
                source_matches = []
                for layout in matches:
                    try:
                        if os.path.commonpath(
                                (source, layout[0])) == layout[0]:
                            source_matches.append(layout)
                    except ValueError:
                        continue
                matches = source_matches or matches
        return matches[0] if matches else layouts[0]
    def _target_verification_mode(
            self, layout: tuple, mod_name: str, source_file: str) -> tuple:
        force_import = self._target_is_real_module(
            layout[0], layout[2], mod_name)
        runtime_export_only = self._runtime_export_targets.get(
            (mod_name, source_file), False)
        runtime_module_map = self._runtime_module_map_targets.get(
            (mod_name, source_file))
        runtime_export_names = self._runtime_export_names.get(
            (mod_name, source_file))
        return (force_import, runtime_export_only, runtime_module_map,
                runtime_export_names)
    @staticmethod
    def _verify_single_target(
            mod_name: str, force_import: bool = False,
            runtime_export_only: bool | str = False,
            runtime_module_map: tuple[str, tuple[str, ...]] | None = None,
            runtime_export_names: tuple[str, ...] | None = None,
            ) -> str | None:
        try:
            parts = mod_name.rsplit(".", 1)
            if len(parts) == 2 and not force_import:
                parent, child = parts
                parent_mod = importlib.import_module(parent)
                if not hasattr(parent_mod, child):
                    importlib.import_module(mod_name)
            else:
                importlib.import_module(mod_name)
            if runtime_export_only:
                parent = (
                    runtime_export_only if isinstance(runtime_export_only, str)
                    else (mod_name.rsplit(".", 1)[0]
                          if "." in mod_name else mod_name))
                parent_mod = importlib.import_module(parent)
                export_names = getattr(parent_mod, "__all__", ())
                if runtime_export_names:
                    wanted = set(runtime_export_names)
                    export_names = tuple(
                        name for name in export_names if name in wanted)
                for export_name in export_names:
                    if not hasattr(parent_mod, export_name):
                        mod_name = f"{parent}.{export_name}"
                        importlib.import_module(mod_name)
            if runtime_module_map:
                parent, map_names = runtime_module_map
                parent_mod = importlib.import_module(parent)
                for full_mod in _runtime_module_map_imports(
                        parent_mod, parent, map_names):
                    mod_name = full_mod
                    importlib.import_module(mod_name)
        except SystemExit as e:
            logger.debug("[ConsolGate] verify_import_chain 导入中断: %s", e, exc_info=True)
            return f"{mod_name} (SystemExit: {e})"
        except (ImportError, SyntaxError) as e:
            logger.debug("[ConsolGate] verify_import_chain 导入失败: %s", e, exc_info=True)
            return f"{mod_name} ({e})"
        except Exception as e:
            logger.debug("[ConsolGate] verify_import_chain 意外异常: %s", e, exc_info=True)
            return f"{mod_name} (unexpected: {e})"
        return None
    def verify_import_chain(self, project_path: str, targets: list | None = None):
        if targets is None:
            targets = self.collect_import_targets(project_path)
        else:
            targets = _coerce_verification_targets(targets)
        if not targets:
            return 100.0, []
        memo_key = _verification_memo_key(project_path, targets)
        _memo = self._import_verify_memo
        if _memo is not None and _memo[0] == memo_key:
            _pct, _broken = _memo[1]
            return _pct, list(_broken)
        layouts = self._detect_import_layouts(project_path)
        base_path_roots = list(dict.fromkeys(layout[1] for layout in layouts))
        path_snapshot = list(sys.path)
        known_modules = dict(sys.modules)
        package_attrs = _package_module_attr_snapshot()
        _prev_dwb = sys.dont_write_bytecode
        sys.dont_write_bytecode = True
        try:
            broken = []
            for mod_name, source_file in targets:
                _restore_verification_imports(known_modules, package_attrs)
                layout = self._target_layout(layouts, mod_name, source_file)
                path_roots = [layout[1]] + [
                    root for root in base_path_roots if root != layout[1]]
                sys.path[:] = [
                    root for root in path_snapshot if root not in base_path_roots]
                for path_root in reversed(path_roots):
                    sys.path.insert(0, path_root)
                _evict_target_module_family(mod_name)
                importlib.invalidate_caches()
                (force_import, runtime_export_only, runtime_module_map,
                 runtime_export_names) = self._target_verification_mode(
                    layout, mod_name, source_file)
                issue = self._verify_single_target(
                    mod_name, force_import, runtime_export_only,
                    runtime_module_map, runtime_export_names)
                if issue is not None:
                    broken.append(issue)
        finally:
            sys.dont_write_bytecode = _prev_dwb
            _restore_verification_imports(known_modules, package_attrs)
            sys.path[:] = path_snapshot
        total = len(targets)
        ok = total - len(broken)
        integrity_pct = (ok / total * 100) if total > 0 else 100.0
        self._import_verify_memo = (memo_key, (integrity_pct, list(broken)))
        return integrity_pct, broken
    def _subprocess_timeout(self) -> float:
        value = getattr(self.thresholds, "IMPORT_SUBPROCESS_TIMEOUT_S", None)
        if is_real_number(value) and value > 0:
            return float(value)
        return float(GateThresholds.IMPORT_SUBPROCESS_TIMEOUT_S)
    def _subproc_verify_env(self, project_path: str) -> dict[str, str]:
        env = subprocess_noartifact_env()
        layouts = self._detect_import_layouts(project_path)
        target_paths = {
            os.path.normcase(os.path.abspath(path))
            for layout in layouts for path in layout[:2]
        }
        existing = []
        for entry in env.get("PYTHONPATH", "").split(os.pathsep):
            if not entry:
                continue
            normalized = os.path.normcase(os.path.abspath(entry))
            if normalized not in target_paths:
                existing.append(entry)
        if existing:
            env["PYTHONPATH"] = os.pathsep.join(existing)
        else:
            env.pop("PYTHONPATH", None)
        return env
    def _run_subproc_verifier(self, env: dict[str, str],
                              module_targets: list) -> list | None:
        try:
            proc = subprocess.run(
                [sys.executable, "-c", self._SUBPROC_VERIFIER_SRC],
                input=json.dumps(module_targets),
                capture_output=True, text=True, encoding="utf-8",
                errors="replace", env=env,
                timeout=self._subprocess_timeout(),
                check=False,
            )
            if proc.returncode == 0:
                failed = self._parse_subproc_failed(proc.stdout)
                if failed is not None:
                    return failed
                logger.warning(
                    "[GATE-03/07] 子进程验证输出为空，按无证据处理并降级进程内验证")
                return None
            logger.warning(
                "[GATE-03/07] 子进程验证异常退出 rc=%s，按目标验证失败处理: %s",
                proc.returncode, (proc.stderr or "")[:300])
            return [
                f"{target[0]} (SubprocessError: rc={proc.returncode})"
                for target in module_targets
            ]
        except subprocess.TimeoutExpired as e:
            logger.warning(
                "[GATE-03/07] 子进程验证超时，按目标验证失败处理且不降级进程内: %s", e)
            return [
                f"{target[0]} (TimeoutExpired: {e})" for target in module_targets
            ]
        except (OSError, ValueError) as e:
            logger.warning("[GATE-03/07] 子进程验证不可用，降级进程内验证: %s", e)
        return None
    def verify_import_chain_subprocess(self, project_path: str,
                                       targets: list | None = None
                                       ) -> tuple[float, list, str]:
        if targets is None:
            targets = self.collect_import_targets(project_path)
        else:
            targets = _coerce_verification_targets(targets)
        if not targets:
            return 100.0, [], "subprocess"
        memo_key = _verification_memo_key(project_path, targets)
        _memo = self._subproc_verify_memo
        if _memo is not None and _memo[0] == memo_key:
            _p, _f, _mode = _memo[1]
            return _p, list(_f), _mode
        env = self._subproc_verify_env(project_path)
        layouts = self._detect_import_layouts(project_path)
        module_targets = []
        for mod_name, source_file in targets:
            layout = self._target_layout(layouts, mod_name, source_file)
            (force_import, runtime_export_only, runtime_module_map,
             runtime_export_names) = self._target_verification_mode(
                layout, mod_name, source_file)
            module_targets.append([
                mod_name, force_import, layout[1], runtime_export_only,
                runtime_module_map, runtime_export_names,
            ])
        failed = self._run_subproc_verifier(env, module_targets)
        if failed is not None:
            passed = len(targets) - len(failed)
            pct = passed / len(targets) * 100
            failed_names = [str(f) for f in failed]
            self._subproc_verify_memo = (
                memo_key, (pct, list(failed_names), "subprocess"))
            return pct, failed_names, "subprocess"
        pct, broken = self.verify_import_chain(project_path, targets)
        self._subproc_verify_memo = (
            memo_key, (pct, list(broken), "inprocess"))
        return pct, broken, "inprocess"
def _read_source_text(file_path: str,
                      purpose: str) -> tuple[str | None, Exception | None]:
    file_path = _path_arg(file_path)
    if not isinstance(file_path, str) or not file_path:
        error = ValueError(f"源码路径畸形: {file_path!r}")
        logger.warning("%s 读取源码失败: %s", purpose, error)
        return None, error
    try:
        return read_source_interpreter_encoding(file_path), None
    except (OSError, UnicodeDecodeError, SyntaxError) as e:
        logger.warning("%s 读取源码失败: %s: %s", purpose, file_path, e)
        return None, e
def verify_with_compile(source_code: str, file_path: str = "") -> dict[str, Any]:
    if isinstance(file_path, (bytes, os.PathLike)):
        file_path = os.fsdecode(os.fspath(file_path))
    if not isinstance(file_path, str):
        file_path = ""
    if not isinstance(source_code, (str, bytes, bytearray)):
        return {
            "status": "error",
            "errors": [{
                "msg": f"source_code 须为 str/bytes，实际 {type(source_code).__name__}",
                "lineno": None,
                "offset": None,
                "text": None,
            }],
        }
    try:
        compile(strip_bom(source_code), file_path or "<verify>", "exec")
        return {"status": "ok", "errors": []}
    except PARSE_DEGRADE_EXC as e:
        logger.warning("verify_with_compile 语法验证失败: %s", e, exc_info=True)
        return {
            "status": "error",
            "errors": [{
                "msg": getattr(e, "msg", None) or str(e),
                "lineno": getattr(e, "lineno", None),
                "offset": getattr(e, "offset", None),
                "text": getattr(e, "text", None),
            }],
        }
def _verify_callable_layer(result: dict[str, Any], mod: Any,
                           func_name: str) -> None:
    if not func_name:
        return
    try:
        fn = getattr(mod, func_name)
    except AttributeError:
        result["errors"].append(f"{func_name} 在模块中不存在")
        return
    except (Exception, SystemExit) as e:
        logger.warning("语义验证的属性查询异常: %s", e, exc_info=True)
        result["errors"].append(
            f"{func_name} 属性查询失败 ({type(e).__name__}: {e})")
        return
    if callable(fn):
        result["callable_ok"] = True
    else:
        result["errors"].append(
            f"{func_name} 存在但不可调用 (type={type(fn).__name__})")
def enhance_verify_fix_semantic(file_path: str, func_name: str = "") -> dict[str, Any]:
    result: dict[str, Any] = {
        "syntax_ok": False, "import_ok": False, "callable_ok": False, "errors": []}
    file_path = _path_arg(file_path)
    if not isinstance(file_path, str) or not file_path:
        result["errors"].append(f"读取文件失败: 路径畸形 {file_path!r}")
        return result
    if not isinstance(func_name, str):
        func_name = ""
    if not _verify_syntax_layer(file_path, result):
        return result
    _verify_import_layer(file_path, func_name, result)
    return result
def _verify_syntax_layer(file_path: str, result: dict[str, Any]) -> bool:
    src, read_err = _read_source_text(file_path, "enhance_verify_fix_semantic")
    if src is None:
        result["errors"].append(f"读取文件失败: {read_err}")
        return False
    try:
        compile_result = verify_with_compile(src, file_path)
    except Exception as e:
        logger.warning("enhance_verify_fix_semantic compile 验证异常: %s", e, exc_info=True)
        result["errors"].append(f"compile失败: {e}")
        return False
    if compile_result["status"] != "ok":
        err = compile_result["errors"][0] if compile_result["errors"] else {}
        result["errors"].append(f"语法错误 L{err.get('lineno')}: {err.get('msg')}")
        return False
    result["syntax_ok"] = True
    return True
def _module_load_plan(file_path: str) -> tuple[str, str, bool]:
    abs_path = os.path.abspath(file_path)
    stem = os.path.splitext(os.path.basename(abs_path))[0]
    directory = os.path.dirname(abs_path)
    parts = [] if stem == "__init__" else [stem]
    in_package = False
    while os.path.isfile(os.path.join(directory, "__init__.py")):
        parts.insert(0, os.path.basename(directory))
        in_package = True
        parent = os.path.dirname(directory)
        if parent == directory:
            break
        directory = parent
    if not in_package:
        return directory, stem, False
    return directory, ".".join(parts), True
_ABSENT = object()
def _package_module_attr_snapshot() -> dict[int, tuple[Any, dict[str, Any]]]:
    snapshot: dict[int, tuple[Any, dict[str, Any]]] = {}
    for pkg_mod in list(sys.modules.values()):
        if pkg_mod is None or getattr(pkg_mod, "__path__", None) is None:
            continue
        try:
            attrs = vars(pkg_mod)
        except TypeError:
            logger.debug("包模块属性不可枚举，跳过快照: %r", pkg_mod, exc_info=True)
            continue
        snapshot[id(pkg_mod)] = (pkg_mod, dict(attrs))
    return snapshot
def _restore_package_module_attrs(
        snapshot: dict[int, tuple[Any, dict[str, Any]]]) -> None:
    for pkg_mod, saved in snapshot.values():
        try:
            current_attrs = dict(vars(pkg_mod))
        except TypeError:
            logger.debug("包模块属性不可枚举，跳过还原: %r", pkg_mod, exc_info=True)
            continue
        for attr in sorted(set(saved) | set(current_attrs)):
            saved_value = saved.get(attr, _ABSENT)
            value = current_attrs.get(attr, _ABSENT)
            if (not isinstance(saved_value, types.ModuleType)
                    and not isinstance(value, types.ModuleType)):
                continue
            if saved_value is value:
                continue
            try:
                if saved_value is _ABSENT:
                    delattr(pkg_mod, attr)
                else:
                    setattr(pkg_mod, attr, saved_value)
            except (AttributeError, TypeError):
                logger.debug("恢复父包属性失败(非阻断): %s", attr,
                             exc_info=True)
def _restore_verification_imports(known: dict[str, Any],
                                  package_attrs: dict) -> None:
    _restore_package_module_attrs(package_attrs)
    for _name in set(sys.modules) - set(known):
        sys.modules.pop(_name, None)
    for _name, _mod in known.items():
        if sys.modules.get(_name, _ABSENT) is not _mod:
            sys.modules[_name] = _mod
def _exec_module_in_context(spec, mod, import_root: str, module_name: str) -> None:
    known = dict(sys.modules)
    package_attrs = _package_module_attr_snapshot()
    path_snapshot = list(sys.path)
    dwb_snapshot = sys.dont_write_bytecode
    prior = sys.modules.get(module_name, _ABSENT)
    sys.path[:] = [import_root] + [
        path for path in sys.path if path != import_root]
    _evict_target_module_family(module_name)
    sys.modules[module_name] = mod
    sys.dont_write_bytecode = True
    try:
        spec.loader.exec_module(mod)
    finally:
        sys.dont_write_bytecode = dwb_snapshot
        _restore_verification_imports(known, package_attrs)
        if prior is _ABSENT:
            sys.modules.pop(module_name, None)
        else:
            sys.modules[module_name] = prior
        sys.path[:] = path_snapshot
def _verify_import_layer(file_path: str, func_name: str,
                         result: dict[str, Any]) -> None:
    try:
        import_root, module_name, _in_package = _module_load_plan(file_path)
        spec = importlib.util.spec_from_file_location(module_name, file_path)
        if spec and spec.loader:
            mod = importlib.util.module_from_spec(spec)
            _exec_module_in_context(spec, mod, import_root, module_name)
            result["import_ok"] = True
            _verify_callable_layer(result, mod, func_name)
        else:
            result["errors"].append("无法创建模块spec")
    except (Exception, SystemExit) as e:
        logger.warning("enhance_verify_fix_semantic 导入验证异常: %s", e, exc_info=True)
        result["errors"].append(f"导入失败: {type(e).__name__}: {e}")
